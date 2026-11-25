#pragma once

#include <compare>
#include <cstdint>
#include <string>

namespace pairing {

// Dollar amounts and per-unit prices, as integer millionths of a dollar.
//
// Integer arithmetic makes every requirement exact and deterministic (spec §5.4).
// Prices quoted to the cent times whole share counts times percentages with at most
// four decimals are exact at this scale, so the manual's figures are reproduced
// without tolerance. Products go through 128-bit intermediates and overflow throws.
class Money {
public:
    static constexpr std::int64_t per_dollar = 1'000'000;

    constexpr Money() = default;
    static constexpr Money from_micros(std::int64_t m) {
        Money x;
        x.m_ = m;
        return x;
    }
    // Rounds to the nearest micro-dollar, so decimal inputs with up to six places are exact.
    static Money dollars(double d);

    constexpr std::int64_t micros() const { return m_; }
    // Two decimals, more only when the value has sub-cent digits.
    std::string str() const;

    constexpr auto operator<=>(const Money&) const = default;
    constexpr Money operator-() const { return from_micros(-m_); }
    Money& operator+=(Money o);
    Money& operator-=(Money o);
    friend Money operator+(Money a, Money b) { return a += b; }
    friend Money operator-(Money a, Money b) { return a -= b; }

private:
    std::int64_t m_ = 0;
};

// A fraction as integer parts per million: 20% is Rate{200'000}.
struct Rate {
    std::int64_t ppm = 0;

    static Rate from_double(double fraction);
    constexpr auto operator<=>(const Rate&) const = default;
};

constexpr Rate percent(std::int64_t whole) { return Rate{whole * 10'000}; }

// Price per unit times a count of units. Exact.
Money operator*(Money price, std::int64_t units);
inline Money operator*(std::int64_t units, Money price) { return price * units; }
// Rounded half away from zero to the micro-dollar.
Money operator*(Rate r, Money m);
Rate operator*(Rate a, Rate b);

}  // namespace pairing
