#pragma once

// A minimal check harness: no test framework is installed, and the tests need only
// equality checks with readable failure messages.

#include <iostream>
#include <string>
#include <type_traits>

#include "pairing/money.hpp"

namespace check {

struct Counter {
    int checks = 0;
    int failures = 0;
};

inline Counter& counter() {
    static Counter c;
    return c;
}

// Printed with each failure, e.g. the fixture case id.
inline std::string& context() {
    static std::string s;
    return s;
}

inline std::string text(const pairing::Money& m) { return m.str(); }
inline std::string text(const pairing::Rate& r) { return std::to_string(r.ppm) + " ppm"; }
inline std::string text(bool b) { return b ? "true" : "false"; }
inline std::string text(const std::string& s) { return s; }
template <class T>
    requires std::is_arithmetic_v<T>
std::string text(T v) {
    return std::to_string(v);
}

inline void report(const std::string& message, const char* file, int line) {
    ++counter().failures;
    std::cerr << file << ":" << line << ": ";
    if (!context().empty()) std::cerr << "[" << context() << "] ";
    std::cerr << message << "\n";
}

template <class A, class B>
void equal(const A& actual, const B& expected, const char* expr, const char* file, int line) {
    ++counter().checks;
    if (!(actual == expected)) report(std::string(expr) + ": got " + text(actual) + ", expected " + text(expected), file, line);
}

inline void truth(bool ok, const char* expr, const char* file, int line) {
    ++counter().checks;
    if (!ok) report(std::string("failed: ") + expr, file, line);
}

template <class F>
void throws(F&& f, const char* expr, const char* file, int line) {
    ++counter().checks;
    try {
        f();
    } catch (const std::exception&) {
        return;
    }
    report(std::string("did not throw: ") + expr, file, line);
}

}  // namespace check

#define CHECK(cond) ::check::truth((cond), #cond, __FILE__, __LINE__)
#define CHECK_EQ(actual, expected) ::check::equal((actual), (expected), #actual, __FILE__, __LINE__)
#define CHECK_THROWS(expr) ::check::throws([&] { (void)(expr); }, #expr, __FILE__, __LINE__)
