// ============================================================================
// main.cpp — Entry point for the ctl_sat tool
// ============================================================================

#include "tctl/cli.hpp"

#include <iostream>
#include <stdexcept>

int main(int argc, char* argv[]) {
    try {
        tctl::Options opts = tctl::parse_args(argc, argv);

        if (opts.help) {
            tctl::print_usage(argv[0]);
            return 0;
        }

        return tctl::run(opts);

    } catch (const std::exception& e) {
        std::cerr << "ERROR: " << e.what() << "\n";
        tctl::print_usage(argv[0]);
        return 1;
    }
}
