package tctl.uppaal;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.ArrayList;
import java.util.List;

/**
 * Shells out to the tested Python engine (uppaal2tctl.py + checksat.py) which
 * translates each UPPAAL query and runs the native {@code tctl_sat} solver.
 *
 * The engine (two .py files + the {@code tctl_sat} binary) is bundled in the
 * plugin jar under {@code /engine/}; on first use it is extracted to a temp dir.
 * Communicates via {@code --porcelain}: one TSV line per query
 * {@code verdict<TAB>query<TAB>witnessPath<TAB>reason}.
 */
final class SatRunner {

    static final class Result {
        final String query, verdict, reason;
        final File witness;       // non-null only for SAT with a saved witness
        Result(String verdict, String query, File witness, String reason) {
            this.verdict = verdict; this.query = query;
            this.witness = witness; this.reason = reason;
        }
    }

    private static Path engineDir;   // cached extraction

    /**
     * Resolve a python3 interpreter by absolute path. A GUI app launched via
     * Finder/`open` inherits a minimal PATH, so a bare "python3" may not resolve;
     * probe the usual locations first, then fall back to PATH.
     */
    static String python3() {
        String[] cands = {
            "/opt/homebrew/bin/python3", "/usr/local/bin/python3",
            "/opt/anaconda3/bin/python3", "/usr/bin/python3",
        };
        for (String c : cands) if (new File(c).canExecute()) return c;
        return "python3";
    }

    static synchronized Path engine() throws IOException {
        if (engineDir != null) return engineDir;
        Path dir = Files.createTempDirectory("tctl_engine_");
        for (String res : new String[]{"uppaal2tctl.py", "checksat.py", "tctl_sat"}) {
            try (InputStream in = SatRunner.class.getResourceAsStream("/engine/" + res)) {
                if (in == null) throw new IOException("bundled resource missing: /engine/" + res);
                Path out = dir.resolve(res);
                Files.copy(in, out, StandardCopyOption.REPLACE_EXISTING);
                out.toFile().setExecutable(true);
            }
        }
        engineDir = dir;
        return dir;
    }

    static List<Result> check(File modelXml, List<String> queries) throws IOException, InterruptedException {
        Path eng = engine();
        Path qfile = Files.createTempFile("queries_", ".q");
        Files.write(qfile, queries, StandardCharsets.UTF_8);
        Path wdir = Files.createTempDirectory("witnesses_");

        List<String> cmd = new ArrayList<>();
        cmd.add(python3());
        cmd.add(eng.resolve("checksat.py").toString());
        if (modelXml != null) {   // null -> engine runs model-free (pure logic)
            cmd.add("--model");  cmd.add(modelXml.getAbsolutePath());
        }
        cmd.add("--queries");    cmd.add(qfile.toString());
        cmd.add("--binary");     cmd.add(eng.resolve("tctl_sat").toString());
        cmd.add("--witness-dir"); cmd.add(wdir.toString());
        cmd.add("--porcelain");

        ProcessBuilder pb = new ProcessBuilder(cmd);
        pb.environment().put("PYTHONPATH", eng.toString());   // import uppaal2tctl
        pb.redirectErrorStream(false);
        Process p = pb.start();

        List<Result> results = new ArrayList<>();
        try (BufferedReader r = new BufferedReader(
                new InputStreamReader(p.getInputStream(), StandardCharsets.UTF_8))) {
            String line;
            while ((line = r.readLine()) != null) {
                String[] f = line.split("\t", -1);
                if (f.length < 2) continue;
                String verdict = f[0];
                String query = f[1];
                File witness = (f.length > 2 && !f[2].isEmpty()) ? new File(f[2]) : null;
                String reason = (f.length > 3 && !f[3].isEmpty()) ? f[3] : null;
                results.add(new Result(verdict, query, witness, reason));
            }
        }
        p.waitFor();
        return results;
    }

    private SatRunner() {}
}
