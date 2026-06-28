package tctl.uppaal;

import com.uppaal.plugin.Plugin;
import com.uppaal.plugin.PluginWorkspace;
import com.uppaal.plugin.Registry;

/**
 * Entry point of the TCTL "Check Satisfiability" UPPAAL plugin.
 *
 * The UPPAAL GUI discovers this class via the jar manifest attribute
 * {@code Uppaal-Plugin: tctl.uppaal.SatPlugin} and calls {@link #getWorkspaces()}
 * when the GUI is built; each returned {@link PluginWorkspace} becomes a tab.
 *
 * The {@code Registry} constructor is the documented way to integrate with the
 * UPPAAL framework (access to the open document/model and the query list); a
 * no-arg fallback is provided for older loaders.
 */
public class SatPlugin implements Plugin {

    private final Registry registry;

    public SatPlugin(Registry registry) {
        this.registry = registry;
    }

    public SatPlugin() {
        this(null);
    }

    @Override
    public PluginWorkspace[] getWorkspaces() {
        return new PluginWorkspace[] { new SatWorkspace(registry) };
    }
}
