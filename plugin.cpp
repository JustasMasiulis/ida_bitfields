#include <hexsuite.hpp>

// makes sure that the immediate / cot_num is on the right hand side
std::pair<cexpr_t*, cexpr_t*> normalize_binop( cexpr_t* expr )
{
	const auto num = expr->find_num_op();
	return { expr->theother( num ), num ? num : expr->y };
}

// used for the allocation of helper names
char* alloc_cstr( const char* str )
{
	const auto len = strlen( str ) + 1;
	auto alloc = hexrays_alloc( len );
	if ( alloc )
		memcpy( alloc, str, len );
	return ( char* ) alloc;
}

// selects (adds memref expr) for the first member that is a struct inside of an union
void select_first_union_field( cexpr_t*& expr )
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

// creates a function type of signature `type(bitfield_type, number_type)`
// if creation fails, returns "unknown" type
tinfo_t create_bitfunc( tinfo_t bitfield_type, tinfo_t number_type, tinfo_t type )
{
	func_type_data_t data;
	data.flags = FTI_PURE;
	data.rettype = type;
	data.push_back( funcarg_t{ .type = bitfield_type } );
	data.push_back( funcarg_t{ .type = number_type } );

	tinfo_t t;
	if ( t.create_func( data ) )
		return t;

	return tinfo_t{};
}

// executes callback for each member in `type` where its offset coincides with `and_mask`.
// `cmp_mask` is used to calculate whether the bitfield is enabled or not and passed as second arg to the callback.
// If the bitfield is multi-bit, the cmp_mask and boolean passed to the callback has no meaning.
template<class Callback> bool for_each_bitfield( Callback cb, tinfo_t type, uint64_t and_mask, uint64_t cmp_mask )
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

		if ( member.size != 1 )
		{
			uint64_t mask = 0;
			for ( int i = member.offset; i < member.offset + member.size; ++i )
				mask |= ( 1ull << i );

			if ( ( and_mask & mask ) != mask )
			{
				msg( "[bitfields] bad offset (%ull) and size (%ull) combo of a field for given mask (%ull)\n", member.offset, member.size, and_mask );
				return false;
			}
		}

		cb( member, ( cmp_mask & ( 1ull << i ) ) != 0 );
	}
	return true;
}

void handle_comparison( cexpr_t* expr )
{
	// (x & imm) == imm
	auto [eq, eq_num] = normalize_binop( expr );
	if ( eq->op != cot_band || eq_num->op != cot_num )
		return;

	auto [band, band_num] = normalize_binop( eq );

	// unwrap shifts that compiler might generate
	// ((x >> imm) & imm) == imm
	uint64_t mask_shift_right = 0;
	if ( band->op == cot_ushr )
	{
		auto shiftnum = band->find_num_op();
		if ( !shiftnum )
			return;

		mask_shift_right = shiftnum->n->_value;
		band = band->theother( shiftnum );
	}

	if ( band->op != cot_ptr || band_num->op != cot_num
		  || band->x->op != cot_cast
		  || band->x->x->op != cot_ref )
		return;

	// original member ref without the `*(type*)&` part
	auto orig = band->x->x->x;
	auto type = orig->type;

	// extract the ea from one of the expression parts for union selection to work
	// thanks to @RolfRolles for help with making it work
	ea_t use_ea = band->x->x->ea;
	use_ea = use_ea != BADADDR ? use_ea : band->x->ea;
	use_ea = use_ea != BADADDR ? use_ea : band->ea;
	if ( use_ea == BADADDR )
		msg( "[bitfields] can't find parent ea - won't be able to save union selection\n" );


	// invert comparison mask if it's a not equal check
	const auto cmp_mask = expr->op == cot_eq ? eq_num->n->_value : ~eq_num->n->_value;

	cexpr_t* replacement = nullptr;
	auto success = for_each_bitfield(
		[ &, eq_num = eq_num, band_num = band_num ] ( udt_member_t& member, bool enabled )
		{
			const auto fret = member.size > 1 ? eq_num->type : tinfo_t{ BTF_BOOL };
			auto ftype = create_bitfunc( orig->type, band_num->type, fret );
			if ( ftype.is_unknown() )
			{
				msg( "[bitfields] Failed to create bitflag function prototype\n" );
				return;
			}

			// construct the callable
			auto call_fn = new cexpr_t();
			call_fn->op = cot_helper;
			call_fn->type = ftype;
			call_fn->exflags = 0;
			call_fn->helper = alloc_cstr( "b" );

			// construct the call args
			auto call_args = new carglist_t( ftype );

			call_args->push_back( carg_t{} );
			auto& arg0 = ( *call_args )[ 0 ];
			static_cast< cexpr_t& >( arg0 ) = *orig;
			arg0.ea = use_ea;

			call_args->push_back( carg_t{} );
			auto& arg1 = ( *call_args )[ 1 ];
			arg1.op = cot_helper;
			arg1.type = tinfo_t{ ( type_t ) ( band_num->type.get_size() > 4 ? BTF_UINT64 : BTF_UINT32 ) };
			arg1.exflags = EXFL_ALONE;
			arg1.helper = alloc_cstr( member.name.c_str() );

			// construct the call / access itself
			auto access = new cexpr_t( cot_call, call_fn );
			access->type = fret;
			access->exflags = 0;
			access->a = call_args;
			access->ea = expr->ea;

			// if the flag is multi byte, reconstruct the comparison
			if ( member.size > 1 )
			{
				access = new cexpr_t( expr->op, access, new cexpr_t( *eq_num ) );
				access->type = tinfo_t{ BTF_BOOL };
				access->exflags = 0;
				access->ea = expr->ea;
			}
			// otherwise the flag is single bit; if the flag is disabled, add logical not
			else if ( !enabled )
			{
				access = new cexpr_t( cot_lnot, access );
				access->type = tinfo_t{ BTF_BOOL };
				access->exflags = 0;
				access->ea = expr->ea;
			}

			if ( !replacement )
				replacement = access;
			else
			{
				replacement = new cexpr_t( cot_land, replacement, access );
				replacement->type = tinfo_t{ BTF_BOOL };
				replacement->exflags = 0;
			}
		}, type, band_num->n->_value << mask_shift_right, cmp_mask << mask_shift_right );

	if ( replacement )
	{
		if ( success )
			expr->replace_by( replacement );
		else
			delete expr;
	}
}

// match special bit functions
void handle_call( cexpr_t* expr )
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

	// 2 args
	if ( expr->a->size() != 2 )
		return;

	// second arg has to be a number
	auto& arg1 = ( *expr->a )[ 1 ];
	if ( arg1.op != cot_num )
		return;

	// we expect a helper whose name is one of those functions
	if ( expr->x->op != cot_helper )
		return;

	// (type*)& is expected for first arg
	cexpr_t* arg0 = &( *expr->a )[ 0 ];
	if ( arg0->op != cot_cast || arg0->x->op != cot_ref )
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
	if ( std::distance( std::begin( functions ), it ) >= num_bitmask_funcs )
		mask = ( 1ull << mask );

	cexpr_t* replacement = nullptr;
	bool success = for_each_bitfield(
		[ & ] ( udt_member_t& member, bool )
		{
			auto helper = new cexpr_t();
			helper->op = cot_helper;
			helper->type = arg1.type;
			helper->ea = arg1.ea;
			helper->exflags = EXFL_ALONE;
			helper->helper = alloc_cstr( member.name.c_str() );

			if ( !replacement )
				replacement = helper;
			else
			{
				replacement = new cexpr_t( cot_bor, replacement, helper );
				replacement->type = arg1.type;
				replacement->ea = arg1.ea;
				replacement->exflags = 0;
			}
		}, arg0->type, mask, ( uint64_t ) -1 );

	if ( replacement )
	{
		if ( success )
			arg1.replace_by( replacement );
		else
			delete replacement;
	}
}

auto bitfields_optimizer = hex::hexrays_callback_for<hxe_maturity>(
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