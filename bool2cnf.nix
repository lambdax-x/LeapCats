with import <nixpkgs> {};
stdenv.mkDerivation {
  name = "bool2cnf";
  src = fetchFromGitHub {
    owner = "tkren";
    repo = "bool2cnf";
    rev = "c6556ce690cfbb492d11dae16491cb0c3be20876";
    sha256 = "1sc4rd9cwq885gi6flx6dr664d3jwszy7s3kpcyjskxcl5nl1g3a";
  };
  buildInputs = [ flex bison ];
  installPhase = ''
    mkdir -p $out/bin
    mv bool2cnf $out/bin
  '';
}
