{
  description = "";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  inputs.agda-stdlib = { url = "github:agda/agda-stdlib"; flake = false; };
  inputs.agda-unimath = { url = "github:UniMath/agda-unimath"; flake = false; };
  inputs.denotational-hardware = { url = "github:conal/denotational-hardware"; flake = false; };

  outputs = { self, nixpkgs, agda-stdlib, agda-unimath, denotational-hardware }:
    let
      definedSystems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" ];
      forAllSystems = nixpkgs.lib.genAttrs definedSystems;
      nixpkgsFor = forAllSystems (system: nixpkgs.legacyPackages.${system});
      agdaEnv = (system : (nixpkgsFor.${system}.agda.withPackages (ps: [
              (ps.standard-library.overrideAttrs (oldAttrs:
                { src = agda-stdlib; }))
              ps.agda-categories
              (ps.mkDerivation {
                pname = "agda-unimath";
                version = "1.0.0";
                src = agda-unimath;
                meta = {};
                preBuild = "make src/everything.lagda.md";
                everythingFile = "./src/everything.lagda.md";
                libraryFile = "agda-unimath.agda-lib";
              })
              (ps.mkDerivation {
                pname = "hardware";
                version = "1.0.0";
                src = denotational-hardware;
                meta = {};
                libraryFile = "hardware.agda-lib";
                buildInputs = [
                  ps.standard-library
                ];
              })
      ])));
    in
    {
      devShells = forAllSystems (system: {
        agdaEnv = agdaEnv system;
        devShell = nixpkgsFor.${system}.mkShell {
          packages = [ (agdaEnv system) ];
        };
      });
      packages = forAllSystems (system: let ps = (agdaEnv system);
      # ps' = ps.agda.withPackages agdaPackages;
      in {

        defaultPackage.${system} = nixpkgsFor.${system}.agdaPackages.mkDerivation {
                pname = "agi";
                version = "1.0.0";
                src = ./.;
                meta = {};
                libraryFile = "agi.agda-lib";
                everythingFile = "agi.agda";
                buildInputs = [
                  (agdaEnv system)
                ];
              };
      });
    };
}
