{ nixpkgs ? import <nixpkgs> {}, compiler ? "default"}:
let
  haskellPackages = (if   compiler == "default"
                     then nixpkgs.pkgs.haskellPackages
                     else nixpkgs.pkgs.haskell.packages.${compiler}).override {
    overrides = self: super: {
    };
  };
  developPackage = haskellPackages.developPackage { root = ./.; };
  hoogle         = haskellPackages.ghcWithHoogle (hs: with hs;
                     [ ]);
in
  developPackage.overrideAttrs (oldAttrs: with nixpkgs; {
    buildInputs = oldAttrs.buildInputs ++ [
      pkgs.hlint
      haskellPackages.cabal-install
    ];
    shellHook = ''
    '';
  })
