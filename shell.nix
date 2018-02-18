with import <nixpkgs> {};
let
bool2cnf = (import ./bool2cnf.nix);
in
stdenv.mkDerivation {
    name = "leapcats";
    buildInputs = [ bool2cnf minisat ];
}
