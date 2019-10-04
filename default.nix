let
  compilerVersion = "ghc864";
  sources = import ./nix/sources.nix;
  pkgs = import sources.nixpkgs {};
in

with pkgs;

let
  hpkgs = haskell.packages."${compilerVersion}";
  btools = [
    hpkgs.cabal-install
    hpkgs.ghcid
    hpkgs.hoogle
    hpkgs.stylish-cabal
  ];
  modifier = drv: haskell.lib.addBuildTools drv btools;
in

hpkgs.developPackage { root = ./.; inherit modifier; returnShellEnv = false; }
