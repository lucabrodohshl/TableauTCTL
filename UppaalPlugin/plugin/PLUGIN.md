# TCTL "Check Satisfiability" — UPPAAL plugin

A UPPAAL GUI plugin that adds a **Satisfiability** tab: select queries, click
**Check Satisfiability**, get a per-query SAT/UNSAT verdict, and **save a UPPAAL
`.xml` witness** for satisfiable ones. It follows the UrPal plugin pattern.

```
plugin/
  build.gradle              UrPal-style build (flatDir $UPPAAL_ROOT/libs, Java 8)
  settings.gradle
  src/main/java/tctl/uppaal/
    SatPlugin.java           implements com.uppaal.plugin.Plugin (entry point)
    SatWorkspace.java        the "Satisfiability" tab + results UI
    SatRunner.java           shells out to the bundled engine
  src/main/resources/engine/ (you add these — bundled into the jar)
    uppaal2tctl.py           the translator   (../../translator/uppaal2tctl.py)
    checksat.py              the driver       (../../translator/checksat.py)
    tctl_sat                 native solver built for the host OS
```

## How it works

1. The tab lists the open document's queries (checkboxes, all on by default).
2. **Check Satisfiability** saves the current model to a temp `.xml`, writes the
   selected queries to a temp `.q`, and runs the bundled engine:
   `python3 checksat.py --model M.xml --queries Q.q --binary tctl_sat
   --witness-dir DIR --porcelain`.
3. `checksat.py` → `uppaal2tctl.py` translates each query (operators, predicates,
   per-instance location invariants, clocks→real, deadlock/SMC rejected) and runs
   `tctl_sat`; on SAT with `--model` it emits a UPPAAL `.xml` witness.
4. The results window shows each verdict; **SAT** rows offer **Save witness…**
   (a file chooser writing the `.xml`); **UNSAT**/**REJECTED** rows show the
   reason. (See `../DESIGN.md` for the exact translation semantics.)

The heavy lifting lives in the **tested** Python engine; the Java is a thin
UI + subprocess layer.

## Build & install

```bash
# dir containing lib/model.jar and uppaal.jar. On macOS (UPPAAL 5.0.0):
export UPPAAL_ROOT="/Applications/UPPAAL-5.0.0.app/Contents/Resources/uppaal"
# add the engine files:
cp ../translator/uppaal2tctl.py ../translator/checksat.py src/main/resources/engine/
cp /path/to/tctl_sat                        src/main/resources/engine/   # host-OS build
./gradlew deployLocal                        # build + copy jar to $UPPAAL_ROOT/plugins
# or: ./gradlew runUppaal                    # build + deploy + launch UPPAAL
```

Requirements: **Java 8**, **Gradle**, **UPPAAL ≥ 4.1.22**, **python3** on the
machine, and a `tctl_sat` binary for the host OS (with Z3). The jar manifest
declares `Uppaal-Plugin: tctl.uppaal.SatPlugin`, which the loader reads.

**macOS:** an arm64 `tctl_sat` is already staged in
`src/main/resources/engine/tctl_sat` (built per `../../Implementation/BUILD_MACOS.md`);
it needs `brew install z3` at runtime (it links Homebrew's `libz3`). On Linux,
replace it with a Linux build of `tctl_sat`.

## Two integration points to wire (UPPAAL-version specific)

`SatWorkspace.java` isolates the only two calls that depend on UPPAAL's
`model.jar` API; everything else is version-independent. Fill them in against
`model-javadoc.jar` (package `com.uppaal.model.*`) / `demo/ModelDemo.java`, using
UrPal's `UppaalUtil` as a reference:

- `currentQueries()` → the open document's query formulas
  (Registry → current `Document` → query list).
- `saveCurrentModelToXml()` → write the open `Document` to a temp `.xml`
  (`com.uppaal.model.io2` XML writer / `Document.save`).

Also confirm `PluginWorkspace`'s exact method names (`getName` / `getComponent`)
match your UPPAAL build — they are the tab title and the hosted Swing component.

## Status

- Engine (translator + driver + solver `--real-vars`): **implemented and tested**
  end-to-end (see `../translator/`), verdicts and witnesses verified.
- Java plugin: **written to the documented API**; not compiled here (no UPPAAL
  install on the dev machine). Build it in your UPPAAL environment and wire the
  two hooks above.
