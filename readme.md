# ida bitfields

A simple IDA Pro plugin to make bitfields and bitflags in them easier to reason about.


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

## Acknowledgments

Huge thanks to @RolfRolles for help and feedback, and @can1357 for his HexSuite/NtRays projects which essentially gave me the motivation to write this plugin.
