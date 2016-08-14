# mm-scala
This is intended to be a lightweight version of [mmj2](https://github.com/digama0/mmj2/) which is optimized for rapid development. (In other words, the errors are probably not so great but the code is relatively short.) I don't think this is likely to become a full-featured proof assistant, but it does more complete parsing than any other verifier except [metamath.exe](http://us.metamath.org/index.html#mmprog). In particular, it will read `$t` and `$j` comments, and checks that typecodes have been defined before they are used.

This is a 100% grammatical verifier - it parses all formulas, and does not use strings during verification. Verification of non-grammatical databases is not planned.

Future additions include maintenance utilities such as proof replacement.
