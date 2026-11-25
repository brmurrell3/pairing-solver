#include "pairing/money.hpp"

#include <cmath>
#include <cstdlib>
#include <limits>
#include <stdexcept>

namespace pairing {

namespace {

__extension__ typedef __int128 int128;

std::int64_t narrow(int128 v) {
    if (v > std::numeric_limits<std::int64_t>::max() || v < std::numeric_limits<std::int64_t>::min())
        throw std::overflow_error("money overflow");
    return static_cast<std::int64_t>(v);
}

// n / d rounded half away from zero; d > 0.
int128 divide_rounded(int128 n, int128 d) {
    int128 q = n / d;
    int128 r = n % d;
    if (r < 0) r = -r;
    if (2 * r >= d) q += (n < 0) ? -1 : 1;
    return q;
}

}  // namespace

Money Money::dollars(double d) {
    double scaled = std::round(d * static_cast<double>(per_dollar));
    if (!(std::fabs(scaled) < 9.2e18)) throw std::overflow_error("money overflow");
    return from_micros(static_cast<std::int64_t>(scaled));
}

std::string Money::str() const {
    std::int64_t m = m_;
    bool negative = m < 0;
    // Work in unsigned to cover the most negative value.
    std::uint64_t a = negative ? 0 - static_cast<std::uint64_t>(m) : static_cast<std::uint64_t>(m);
    std::uint64_t whole = a / per_dollar;
    std::uint64_t frac = a % per_dollar;
    std::string digits = std::to_string(frac + per_dollar).substr(1);  // six digits
    while (digits.size() > 2 && digits.back() == '0') digits.pop_back();
    return (negative ? "-" : "") + std::to_string(whole) + "." + digits;
}

Money& Money::operator+=(Money o) {
    if (__builtin_add_overflow(m_, o.m_, &m_)) throw std::overflow_error("money overflow");
    return *this;
}

Money& Money::operator-=(Money o) {
    if (__builtin_sub_overflow(m_, o.m_, &m_)) throw std::overflow_error("money overflow");
    return *this;
}

Rate Rate::from_double(double fraction) {
    return Rate{static_cast<std::int64_t>(std::llround(fraction * 1e6))};
}

Money operator*(Money price, std::int64_t units) {
    return Money::from_micros(narrow(static_cast<int128>(price.micros()) * units));
}

Money operator*(Rate r, Money m) {
    return Money::from_micros(narrow(divide_rounded(static_cast<int128>(m.micros()) * r.ppm, 1'000'000)));
}

Rate operator*(Rate a, Rate b) {
    return Rate{narrow(divide_rounded(static_cast<int128>(a.ppm) * b.ppm, 1'000'000))};
}

}  // namespace pairing
