package tctl.uppaal;

import com.uppaal.plugin.PluginWorkspace;
import com.uppaal.plugin.Registry;
import com.uppaal.plugin.Repository;
import com.uppaal.model.core2.Document;
import com.uppaal.model.core2.Query;
import com.uppaal.model.core2.QueryList;
import com.uppaal.model.io2.XMLWriter;

import javax.swing.*;
import java.awt.*;
import java.io.File;
import java.io.FileOutputStream;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.List;

/**
 * The "Satisfiability" tab.
 *
 * UX (as specified):
 *   - lists the model's queries, each with a checkbox (all selected by default);
 *   - a "Check Satisfiability" button runs the engine on the selected queries;
 *   - when finished, a results window pops up: each query shows its verdict;
 *     an UNSAT row is just a label; a SAT row additionally offers "Save witness…"
 *     which opens a save dialog writing the UPPAAL .xml witness; rejected queries
 *     (e.g. those using {@code deadlock}, or statistical/strategy queries) are
 *     shown with the reason.
 *
 * The two UPPAAL-version-specific hooks — reading the current queries and saving
 * the current model to a temp .xml — are isolated in {@link #currentQueries()} and
 * {@link #saveCurrentModelToXml()}; wire them to your UPPAAL {@code model.jar}
 * (see model-javadoc.jar / UrPal's UppaalUtil for the exact calls).
 */
public class SatWorkspace implements PluginWorkspace {

    private final Registry registry;
    private final JPanel root = new JPanel(new BorderLayout(8, 8));
    private final JPanel queryList = new JPanel();
    private final List<JCheckBox> boxes = new ArrayList<>();

    public SatWorkspace(Registry registry) {
        this.registry = registry;
        build();
    }

    // ---- PluginWorkspace contract (UPPAAL 5.0.0, com.uppaal.plugin) -----------

    @Override public String getTitle() { return "Satisfiability"; }
    @Override public Icon getIcon() { return null; }
    @Override public String getTitleToolTip() { return "Check TCTL query satisfiability"; }
    @Override public Component getComponent() { return root; }
    /** Ordering hint among workspaces; a large value places this plugin tab last. */
    @Override public int getDevelopmentIndex() { return 100; }

    // This tab does not zoom.
    @Override public boolean getCanZoom() { return false; }
    @Override public boolean getCanZoomToFit() { return false; }
    @Override public double getZoom() { return 1.0; }
    @Override public void setZoom(double z) { }
    @Override public void zoomToFit() { }
    @Override public void zoomIn() { }
    @Override public void zoomOut() { }

    /** Called when the tab becomes active/inactive; refresh the query list on show. */
    @Override public void setActive(boolean active) { if (active) reloadQueries(); }

    // ---- UI -----------------------------------------------------------------

    private void build() {
        queryList.setLayout(new BoxLayout(queryList, BoxLayout.Y_AXIS));
        reloadQueries();

        JButton refresh = new JButton("Reload queries");
        refresh.addActionListener(e -> reloadQueries());

        JButton check = new JButton("Check Satisfiability");
        check.addActionListener(e -> onCheck());

        JPanel top = new JPanel(new FlowLayout(FlowLayout.LEFT));
        top.add(new JLabel("Select queries to check (all selected by default):"));
        top.add(refresh);

        JPanel bottom = new JPanel(new FlowLayout(FlowLayout.LEFT));
        bottom.add(check);

        root.add(top, BorderLayout.NORTH);
        root.add(new JScrollPane(queryList), BorderLayout.CENTER);
        root.add(bottom, BorderLayout.SOUTH);
    }

    private void reloadQueries() {
        queryList.removeAll();
        boxes.clear();
        for (String q : currentQueries()) {
            JCheckBox cb = new JCheckBox(q, true);   // selected by default
            boxes.add(cb);
            queryList.add(cb);
        }
        queryList.revalidate();
        queryList.repaint();
    }

    private void onCheck() {
        List<String> selected = new ArrayList<>();
        for (JCheckBox cb : boxes) if (cb.isSelected()) selected.add(cb.getText());
        if (selected.isEmpty()) {
            JOptionPane.showMessageDialog(root, "No queries selected.");
            return;
        }
        File modelXml;
        try {
            modelXml = saveCurrentModelToXml();
        } catch (Exception ex) {
            JOptionPane.showMessageDialog(root, "Could not read the current model:\n" + ex,
                    "Error", JOptionPane.ERROR_MESSAGE);
            return;
        }

        // Run off the EDT; show a small progress dialog.
        final JDialog busy = new JDialog((Frame) null, "Checking…", true);
        busy.add(new JLabel("  Running the satisfiability engine…  "));
        busy.pack();
        busy.setLocationRelativeTo(root);

        SwingWorker<List<SatRunner.Result>, Void> worker = new SwingWorker<>() {
            @Override protected List<SatRunner.Result> doInBackground() throws Exception {
                return SatRunner.check(modelXml, selected);
            }
            @Override protected void done() {
                busy.dispose();
                try {
                    showResults(get());
                } catch (Exception ex) {
                    JOptionPane.showMessageDialog(root, "Engine error:\n" + ex,
                            "Error", JOptionPane.ERROR_MESSAGE);
                }
            }
        };
        worker.execute();
        busy.setVisible(true);   // blocks until worker calls dispose()
    }

    /** The results pop-up: a row per query; SAT rows offer "Save witness…". */
    private void showResults(List<SatRunner.Result> results) {
        JPanel panel = new JPanel(new GridBagLayout());
        GridBagConstraints c = new GridBagConstraints();
        c.insets = new Insets(3, 6, 3, 6);
        c.anchor = GridBagConstraints.WEST;
        int row = 0;
        for (SatRunner.Result r : results) {
            c.gridx = 0; c.gridy = row; c.weightx = 0;
            JLabel verdict = new JLabel(r.verdict);
            verdict.setForeground("SAT".equals(r.verdict) ? new Color(0, 128, 0)
                    : "UNSAT".equals(r.verdict) ? new Color(178, 24, 43) : Color.DARK_GRAY);
            verdict.setFont(verdict.getFont().deriveFont(Font.BOLD));
            panel.add(verdict, c);

            c.gridx = 1; c.weightx = 1;
            String text = r.query + (r.reason != null ? "   (" + r.reason + ")" : "");
            panel.add(new JLabel(text), c);

            c.gridx = 2; c.weightx = 0;
            if ("SAT".equals(r.verdict) && r.witness != null) {
                JButton save = new JButton("Save witness…");
                save.addActionListener(e -> saveWitness(r));
                panel.add(save, c);
            } else {
                panel.add(new JLabel(""), c);
            }
            row++;
        }
        JScrollPane sp = new JScrollPane(panel);
        sp.setPreferredSize(new Dimension(720, Math.min(80 + 28 * results.size(), 480)));
        JOptionPane.showMessageDialog(root, sp, "Satisfiability results",
                JOptionPane.PLAIN_MESSAGE);
    }

    private void saveWitness(SatRunner.Result r) {
        JFileChooser fc = new JFileChooser();
        fc.setSelectedFile(new File("witness.xml"));
        if (fc.showSaveDialog(root) == JFileChooser.APPROVE_OPTION) {
            try {
                Files.copy(r.witness.toPath(), fc.getSelectedFile().toPath(),
                        java.nio.file.StandardCopyOption.REPLACE_EXISTING);
                JOptionPane.showMessageDialog(root, "Witness saved to\n"
                        + fc.getSelectedFile().getAbsolutePath());
            } catch (Exception ex) {
                JOptionPane.showMessageDialog(root, "Could not save witness:\n" + ex,
                        "Error", JOptionPane.ERROR_MESSAGE);
            }
        }
    }

    // ---- UPPAAL model access (com.uppaal.model.*, UPPAAL 5.0.0) ---------------

    /**
     * Find the open {@link Document} by scanning the Registry's repositories for
     * one whose content is a Document. This avoids hard-coding the (undocumented)
     * repository name and is robust across UPPAAL builds.
     */
    private Document findDocument() {
        if (registry == null) return null;
        try {
            for (Object nameObj : registry.getRepositoryNames()) {
                Repository repo = registry.getRepository(String.valueOf(nameObj));
                if (repo == null) continue;
                Object held = repo.get();
                if (held instanceof Document) return (Document) held;
            }
        } catch (Exception ignored) { }
        return null;
    }

    /** Query formulas of the open document (empty if none / no document). */
    private List<String> currentQueries() {
        List<String> qs = new ArrayList<>();
        Document doc = findDocument();
        if (doc == null) return qs;
        QueryList ql = doc.getQueryList();
        if (ql != null) {
            for (Query q : ql) {
                String f = q.getFormula();
                if (f != null && !f.trim().isEmpty()) qs.add(f.trim());
            }
        }
        return qs;
    }

    /**
     * Save the open model to a temporary UPPAAL .xml and return the file.
     * Returns {@code null} if no document is open (the engine then runs in
     * model-free / pure-logic mode).
     */
    private File saveCurrentModelToXml() throws Exception {
        Document doc = findDocument();
        if (doc == null) return null;
        File tmp = File.createTempFile("uppaal_model_", ".xml");
        try (FileOutputStream os = new FileOutputStream(tmp)) {
            new XMLWriter(os).visitDocument(doc);
        }
        return tmp;
    }
}
