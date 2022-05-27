{ nixpkgs  ? import <nixpkgs> {} , compiler ? "default" }:
with nixpkgs;
let
  haskellPackages = (if   compiler == "default"
                     then pkgs.haskellPackages
                     else pkgs.haskell.packages.${compiler}).override {
    overrides = self: super: {
      # TODO linear-base's Setup.hs depends on cabal-doctest
      # linear-base = pkgs.haskell.lib.addSetupDepend self.cabal-doctest
      #                 (pkgs.haskell.lib.dontCheck super.linear-base);
      linear-base = (pkgs.haskell.lib.dontCheck super.linear-base).overrideDerivation
        (old: {
          prePatch = ''
            echo import Distribution.Simple >  Setup.hs
            echo main = defaultMain         >> Setup.hs
          '';
        });
    };
  };
  developPackage = haskellPackages.developPackage { root = ./.; withHoogle = false; };
  hoogle         = haskellPackages.ghcWithHoogle (hs: with hs; []);
in
  developPackage.overrideAttrs (oldAttrs: {
    buildInputs = oldAttrs.buildInputs ++ [
    ];
  })
