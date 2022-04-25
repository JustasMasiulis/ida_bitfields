#include <hexsuite.hpp>

struct access_info
{
	cexpr_t* underlying_expr = nullptr;
	uint64_t mask;
	ea_t     ea;
	uint8_t  shift_value;

	explicit operator bool() const { return underlying_expr != nullptr; }
};

// makes sure that the immediate / cot_num is on the right hand side
inline std::pair<cexpr_t*, cexpr_t*> normalize_binop( cexpr_t* expr )
{
	const auto num = expr->find_num_op();
	return { expr->theother( num ), num ? num : expr->y };
}

inline void replace_or_delete( cexpr_t* expr, cexpr_t* replacement, bool success )
{
	if ( !replacement )
		return;

	if ( success )
		expr->replace_by( replacement );
	else
		delete replacement;
}

inline void merge_accesses( cexpr_t*& original, cexpr_t* access, ctype_t op, ea_t ea, tinfo_t type )
{
	if ( !access )
		return;

	if ( !original )
		original = access;
	else
	{
		original = new cexpr_t( op, original, access );
		original->type = std::move( type );
		original->exflags = 0;
		original->ea = ea;
	}
}

// used for the allocation of helper names
inline char* alloc_cstr( const char* str )
{
	const auto len = strlen( str ) + 1;
	auto alloc = hexrays_alloc( len );
	if ( alloc )
		memcpy( alloc, str, len );
	return ( char* ) alloc;
}

// selects (adds memref expr) for the first member that is a struct inside of an union
inline void select_first_union_field( cexpr_t*& expr )
{
	if ( !expr->type.is_union() )
		return;

	udt_member_t member;
	for ( int i = 0; ; ++i )
	{
		member.offset = i;
		if ( expr->type.find_udt_member( &member, STRMEM_INDEX ) == -1 )
			break;

		if ( !member.type.is_struct() )
			continue;

		expr = new cexpr_t( cot_memref, expr );
		expr->type = member.type;
		expr->m = i;
		expr->exflags = 0;
		expr->ea = expr->x->ea;
		return;
	}
}

inline cexpr_t* create_bitfield_access( access_info& info, udt_member_t& member, ea_t original_ea, tinfo_t& common_type )
{
	func_type_data_t data;
	data.flags = FTI_PURE;
	data.rettype = member.size == 1 ? tinfo_t{ BTF_BOOL } : common_type;
	data.cc = CM_CC_UNKNOWN;
	data.push_back( funcarg_t{ .type = info.underlying_expr->type } );
	data.push_back( funcarg_t{ .type = common_type } );

	tinfo_t functype;
	if ( !functype.create_func( data ) )
	{
		msg( "[bitfields] failed to create a bitfield access function type.\n" );
		return nullptr;
	}

	// construct the callable
	auto call_fn = new cexpr_t();
	call_fn->op = cot_helper;
	call_fn->type = functype;
	call_fn->exflags = 0;
	call_fn->helper = alloc_cstr( "b" );

	// construct the call args
	auto call_args = new carglist_t( std::move( functype ) );

	call_args->push_back( carg_t{} );
	auto& arg0 = ( *call_args )[ 0 ];
	static_cast< cexpr_t& >( arg0 ) = *info.underlying_expr;
	arg0.ea = info.ea;

	call_args->push_back( carg_t{} );
	auto& arg1 = ( *call_args )[ 1 ];
	arg1.op = cot_helper;
	arg1.type = common_type;
	arg1.exflags = EXFL_ALONE;
	arg1.helper = alloc_cstr( member.name.c_str() );

	// construct the call / access itself
	auto access = new cexpr_t( cot_call, call_fn );
	access->type = member.size == 1 ? tinfo_t{ BTF_BOOL } : common_type;
	access->exflags = 0;
	access->a = call_args;
	access->ea = original_ea;

	return access;
}

inline uint64_t bitfield_access_mask( udt_member_t& member )
{
	uint64_t mask = 0;
	for ( int i = member.offset; i < member.offset + member.size; ++i )
		mask |= ( 1ull << i );
	return mask;
}

// executes callback for each member in `type` where its offset coincides with `and_mask`.
// `cmp_mask` is used to calculate enabled bits in the bitfield.
template<class Callback> bool for_each_bitfield( Callback cb, tinfo_t type, uint64_t and_mask )
{
	udt_member_t member;
	for ( size_t i = 0; i < 64; ++i )
	{
		if ( !( and_mask & ( 1ull << i ) ) )
			continue;

		member.offset = i;
		if ( type.find_udt_member( &member, STRMEM_OFFSET ) == -1 )
			continue;

		if ( !member.is_bitfield() )
			continue;

		if ( member.offset != i )
			continue;

		uint64_t mask = bitfield_access_mask( member );
		if ( member.size != 1 && ( and_mask & mask ) != and_mask )
		{
			msg( "[bitfields] bad offset (%ull) and size (%ull) combo of a field for given mask (%ull)\n", member.offset, member.size, and_mask );
			return false;
		}

		cb( member );
	}
	return true;
}

// handles various cases of potential bitfield access.
// * (*(type*)&x >> imm1) & imm2
// * *(type*)&x & imm
// * HIDWORD(*(type*)&x)
inline access_info unwrap_access( cexpr_t* expr )
{
	access_info res;
	if ( expr->op == cot_band )
	{
		auto num = expr->find_num_op();
		if ( !num )
			return res;

		res.mask = num->n->_value;
		res.shift_value = 0;
		expr = expr->theother( num );
	}
	else if ( expr->op == cot_call )
	{
		if ( expr->x->op != cot_helper || expr->a->size() != 1 )
			return res;

		constexpr static std::tuple<std::string_view, uint64_t, uint8_t> functions[] = {
			{"LOBYTE",  0x00'00'00'00'00'00'00'FF, 0 * 8},
			{"LOWORD",  0x00'00'00'00'00'00'FF'FF, 0 * 8},
			{"LODWORD", 0x00'00'00'00'FF'FF'FF'FF, 0 * 8},
			{"HIBYTE",  0xFF'00'00'00'00'00'00'00, 7 * 8},
			{"HIWORD",  0xFF'FF'00'00'00'00'00'00, 6 * 8},
			{"HIDWORD", 0xFF'FF'FF'FF'00'00'00'00, 4 * 8},
			{"BYTE1",   0x00'00'00'00'00'00'FF'00, 1 * 8},
			{"BYTE2",   0x00'00'00'00'00'FF'00'00, 2 * 8},
			{"BYTE3",   0x00'00'00'00'FF'00'00'00, 3 * 8},
			{"BYTE4",   0x00'00'00'FF'00'00'00'00, 4 * 8},
			{"BYTE5",   0x00'00'FF'00'00'00'00'00, 5 * 8},
			{"BYTE6",   0x00'FF'00'00'00'00'00'00, 6 * 8},
			{"WORD1",   0x00'00'00'00'FF'FF'00'00, 2 * 8},
			{"WORD2",   0x00'00'FF'FF'00'00'00'00, 4 * 8},
		};

		// check if it's one of the functions we care for
		auto it = std::ranges::find( functions, expr->x->helper, [ ] ( auto&& func ) { return std::get<0>( func ); } );
		if ( it == std::end( functions ) )
			return res;

		expr = &( *expr->a )[ 0 ];
		res.mask = std::get<1>( *it );
		res.shift_value = std::get<2>( *it );
	}
	else
		return res;

	if ( expr->op == cot_ushr )
	{
		auto shiftnum = expr->find_num_op();
		if ( !shiftnum )
			return res;

		expr = expr->theother( shiftnum );
		if ( res.shift_value == 0 )
			res.mask <<= shiftnum->n->_value;

		res.shift_value += ( uint8_t ) shiftnum->n->_value;
	}

	if ( expr->op != cot_ptr || expr->x->op != cot_cast || expr->x->x->op != cot_ref )
		return res;

	res.underlying_expr = expr->x->x->x;

	// extract the ea from one of the expression parts for union selection to work
	// thanks to @RolfRolles for help with making it work
	ea_t use_ea = expr->x->x->ea;
	use_ea = use_ea != BADADDR ? use_ea : expr->x->ea;
	use_ea = use_ea != BADADDR ? use_ea : expr->ea;
	if ( use_ea == BADADDR )
		msg( "[bitfields] can't find parent ea - won't be able to save union selection\n" );

	res.ea = use_ea;

	return res;
}

inline void handle_comparison( cexpr_t* expr )
{
	auto [eq, eq_num] = normalize_binop( expr );
	if ( eq_num->op != cot_num )
		return;

	auto info = unwrap_access( eq );
	if ( !info )
		return;

	cexpr_t* replacement = nullptr;
	auto success = for_each_bitfield(
		[ &, eq_num = eq_num ] ( udt_member_t& member )
		{
			// construct the call / access itself
			auto access = create_bitfield_access( info, member, expr->ea, eq_num->type );
			if ( !access )
				return;

			const auto mask = bitfield_access_mask( member );
			const auto value = ( ( eq_num->n->_value << info.shift_value ) & mask ) >> member.offset;

			// if the flag is multi byte, reconstruct the comparison
			if ( member.size > 1 )
			{
				auto num = new cnumber_t();
				num->assign( value, access->type.get_size(), member.type.is_signed() ? type_signed : type_unsigned );

				auto num_expr = new cexpr_t();
				num_expr->op = cot_num;
				num_expr->type = access->type;
				num_expr->n = num;
				num_expr->exflags = 0;

				access = new cexpr_t( expr->op, access, num_expr );
				access->type = tinfo_t{ BTF_BOOL };
				access->exflags = 0;
				access->ea = expr->ea;
			}
			// otherwise the flag is single bit; if the flag is disabled, add logical not
			else if ( value ^ ( expr->op == cot_eq ) )
			{
				access = new cexpr_t( cot_lnot, access );
				access->type = tinfo_t{ BTF_BOOL };
				access->exflags = 0;
				access->ea = expr->ea;
			}

			merge_accesses( replacement, access, expr->op == cot_eq ? cot_land : cot_lor, expr->ea, tinfo_t{ BTF_BOOL } );
		}, info.underlying_expr->type, info.mask );

	replace_or_delete( expr, replacement, success );
}

inline void handle_assignment( cexpr_t* expr )
{
	auto rhs = expr->y;
	auto info = unwrap_access( rhs );
	if ( !info )
		return;

	cexpr_t* replacement = nullptr;
	auto success = for_each_bitfield(
		[ & ] ( udt_member_t& member )
		{
			// TODO: for assignment where more than 1 field is being accessed create a new bitfield type for the result
			// that would contain the correctly masked and shifted fields
			const auto access = create_bitfield_access( info, member, expr->y->ea, expr->x->type );
			merge_accesses( replacement, access, cot_bor, rhs->ea, expr->x->type );
		}, info.underlying_expr->type, info.mask );

	replace_or_delete( expr->y, replacement, success );
}

// match special bit functions
inline void handle_call( cexpr_t* expr )
{
	constexpr static size_t num_bitmask_funcs = 8;
	constexpr static std::string_view functions[] = {
		// bit mask functions
		"_InterlockedOr8",
		"_InterlockedOr16",
		"_InterlockedOr",
		"_InterlockedOr64",
		"_InterlockedAnd8",
		"_InterlockedAnd16",
		"_InterlockedAnd",
		"_InterlockedAnd64",
		// bit index functions
		"_bittest",
		"_bittest64",
		"_bittestandreset",
		"_bittestandreset64",
		"_bittestandset",
		"_bittestandset64",
		"_interlockedbittestandset",
		"_interlockedbittestandset64"
	};

	// we expect a helper whose name is one of special functions
	if ( expr->x->op != cot_helper )
		return;

	// 2 args
	if ( expr->a->size() != 2 )
		return;

	// (type*)& is expected for first arg
	cexpr_t* arg0 = &( *expr->a )[ 0 ];
	if ( arg0->op != cot_cast || arg0->x->op != cot_ref )
		return;

	// second arg has to be a number
	auto& arg1 = ( *expr->a )[ 1 ];
	if ( arg1.op != cot_num )
		return;

	// these functions will reference the union directly, so select a field for a start
	select_first_union_field( arg0->x->x );
	arg0 = arg0->x->x;

	// check if it's one of the functions we care for
	auto it = std::ranges::find( functions, expr->x->helper );
	if ( it == std::end( functions ) )
		return;

	auto mask = arg1.n->_value;

	// if it's a bitmask function make the mask 1 << n
	if ( std::distance( functions, it ) >= num_bitmask_funcs )
		mask = ( 1ull << mask );

	cexpr_t* replacement = nullptr;
	bool success = for_each_bitfield(
		[ & ] ( udt_member_t& member )
		{
			auto helper = new cexpr_t();
			helper->op = cot_helper;
			helper->type = arg1.type;
			helper->ea = arg1.ea;
			helper->exflags = EXFL_ALONE;
			helper->helper = alloc_cstr( member.name.c_str() );

			merge_accesses( replacement, helper, cot_bor, arg1.ea, arg1.type );
		}, arg0->type, mask );

	replace_or_delete( &arg1, replacement, success );
}

inline auto bitfields_optimizer = hex::hexrays_callback_for<hxe_maturity>(
	[ ] ( cfunc_t* cfunc, ctree_maturity_t maturity )->ssize_t
	{
		if ( maturity != CMAT_FINAL )
			return 0;

		struct visitor : ctree_visitor_t
		{
			visitor() : ctree_visitor_t( CV_FAST ) {}

			int idaapi visit_expr( cexpr_t* expr ) override
			{
				if ( expr->op == cot_eq || expr->op == cot_ne )
					handle_comparison( expr );
				else if ( expr->op == cot_call )
					handle_call( expr );
				else if ( expr->op == cot_asg )
					handle_assignment( expr );

				return 0;
			}
		};

		visitor{}.apply_to( &cfunc->body, nullptr );

		return 0;
	} );

struct bitfields : plugmod_t
{
	netnode nn = { "$ bitfields", 0, true };

	void set_state( bool s )
	{
		bitfields_optimizer.set_state( s );
	}
	bitfields()
	{
		set_state( nn.altval( 0 ) == 0 );
	}
	~bitfields()
	{
		bitfields_optimizer.uninstall();
	}

	bool run( size_t ) override
	{
		constexpr const char* format = R"(
AUTOHIDE NONE
bitfields plugin for Hex-Rays decompiler.
State: %s)";
		int code = ask_buttons( "~E~nable", "~D~isable", "~C~lose", -1, format + 1, nn.altval( 0 ) == 0 ? "Enabled" : "Disabled" );
		if ( code < 0 )
			return true;
		nn.altset( 0, code ? 0 : 1 );
		set_state( code );
		return true;
	}
};
plugin_t PLUGIN = { IDP_INTERFACE_VERSION, PLUGIN_MULTI, hex::init_hexray<bitfields>, nullptr, nullptr, "bitfields", nullptr, "bitfields", nullptr, };