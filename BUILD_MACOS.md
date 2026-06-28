# Building `tctl_sat` on macOS (Apple Silicon)

`tctl_sat` builds and runs natively on macOS (arm64). The dependency that used
to be "Linux-only" — UDBM — is from the UPPAAL team and is cross-platform; the
top `CMakeLists.txt` already has the `darwin` branches. Three small things were
needed to make it go through on a current macOS + CMake 4 toolchain.

## Prerequisites

```bash
brew install z3 cmake        # z3 is also a RUNTIME dependency (libz3 dylib)
```
(`shasum` and a C++ compiler ship with macOS / Xcode CLT.)

## Steps

```bash
cd Implementation/UDBM
# Build UDBM + UUtils for darwin (deps: xxHash, boost, doctest, UUtils).
# CMAKE_POLICY_VERSION_MINIMUM=3.5 is the CMake-4 escape hatch for the
# dependencies that still declare cmake_minimum_required(VERSION <3.5).
CMAKE_POLICY_VERSION_MINIMUM=3.5 bash ./compile.sh darwin-libs-release
# -> build-darwin-release/src/libUDBM.a  and  local/darwin/lib/lib{base,hash}.a

cd ..
cmake -S . -B build-macos -DCMAKE_BUILD_TYPE=Release -DUDBM_DIR="$PWD/UDBM"
cmake --build build-macos -j4
# -> build-macos/tctl_sat   (Mach-O arm64)
```

## The three fixes (already applied / noted)

1. **`UDBM/getlibs.sh` checksum** — the doctest/UUtils archives were verified
   with `sha256sum --check`, which the macOS/Anaconda `sha256sum` doesn't
   support. Patched to use native `shasum -a256 --check -` (like the xxHash and
   boost entries already did). *Committed in `getlibs.sh`.*
2. **CMake 4 policy** — CMake ≥ 4 removed compatibility with
   `cmake_minimum_required(VERSION < 3.5)`, which some dependencies still
   declare. Export `CMAKE_POLICY_VERSION_MINIMUM=3.5` for the UDBM build (shown
   above). *Pass at build time; no source change.*
3. **`UDBM_DIR`** — the top `CMakeLists.txt` defaults `UDBM_DIR` to
   `${CMAKE_SOURCE_DIR}/../UDBM`, but the UDBM source in this tree is at
   `Implementation/UDBM`. Pass `-DUDBM_DIR="$PWD/UDBM"` (shown above) so it uses
   the one you just built rather than cloning a fresh copy beside `Implementation`.

## Verify

```bash
echo 'AG[0,2] p' | ./build-macos/tctl_sat /dev/stdin           # SATISFIABLE
echo 'EF ((gclk > 4) & (gclk < 5))' > /tmp/r.txt
./build-macos/tctl_sat               /tmp/r.txt   # UNSATISFIABLE (int)
./build-macos/tctl_sat --real-vars gclk /tmp/r.txt # SATISFIABLE   (real, clocks)
```

## Runtime note

The binary links Homebrew's `libz3` dynamically
(`/opt/homebrew/opt/z3/lib/libz3.*.dylib`), so a Mac running it needs
`brew install z3`. (To ship without that dependency, static-link z3 or bundle the
dylib and adjust the install name with `install_name_tool`.)
