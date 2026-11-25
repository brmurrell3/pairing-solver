#include <exception>
#include <iostream>
#include <string>

#include "check.hpp"

// Each suite returns the number of fixture cases or test groups it ran.
int run_unit_tests();
int run_fixture_file(const std::string& path);
int run_solver_tests();
int run_exhaustive(int per_policy);

int main(int argc, char** argv) {
    std::string suite = argc > 1 ? argv[1] : "";
    try {
        int ran = 0;
        if (suite == "unit" && argc == 2) {
            ran = run_unit_tests();
        } else if (suite == "fixture" && argc == 3) {
            ran = run_fixture_file(argv[2]);
        } else if (suite == "solver" && argc == 2) {
            ran = run_solver_tests();
        } else if (suite == "exhaustive" && argc == 3) {
            ran = run_exhaustive(std::stoi(argv[2]));
        } else {
            std::cerr << "usage: pairing_tests unit | solver | fixture <file.toml> | exhaustive <portfolios per policy>\n";
            return 2;
        }
        const auto& c = check::counter();
        std::cout << suite << (argc == 3 ? std::string(" ") + argv[2] : "") << ": " << ran << " cases, " << c.checks
                  << " checks, " << c.failures << " failed\n";
        return c.failures == 0 ? 0 : 1;
    } catch (const std::exception& e) {
        std::cerr << "error";
        if (!check::context().empty()) std::cerr << " [" << check::context() << "]";
        std::cerr << ": " << e.what() << "\n";
        return 1;
    }
}
