# ida bitfields

A simple IDA Pro plugin to make bitfields and bitflags in them easier to reason about.

It hasn't yet been tested very much and will have some rough edges, but it works well enough for me. Feel free to open an issue if something is wrong.

## Example

### Before

![terminate](https://bugcheck.me/assets/images/terminate.png)

### After

![terminate](https://bugcheck.me/assets/images/terminate_bitfields.png)

## Usage

Plugin will either automatically convert the code or you will need to switch which union field is selected to the one that contains the bitfields.

To do that right click on the union member and and perform `select union field` (`alt + y`).

## Installation

Copy the DLLs to the plugins folder in your IDA installation directory.

## Acknowledgements

Huge thanks to [@RolfRolles](https://github.com/rolfrolles) for help and feedback, and [@can1357](http://github.com/can1357) for his HexSuite/NtRays projects which essentially gave me the motivation to write this plugin.
