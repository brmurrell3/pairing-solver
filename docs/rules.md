# Margin rules encoded by the first application

Paraphrased from FINRA Rule 4210 as published on finra.org on 2026-11-25, and from
the Cboe Margin Manual dated November 30, 2021 (local copies in `refs/`). Paragraph
citations are to Rule 4210 unless marked otherwise. Confirm against the live rule text
before relying on any number.

## Units

- **U1 (series).** A series is a class, an expiration date, an exercise price and a unit of trading ((f)(2)(A)(xxx)). An option adjusted after a corporate action is therefore its own series.
- **U2 (equivalent units).** For stock, the underlying component is the equivalent number of shares; for index options, it is the index value times the multiplier ((f)(2)(A)(xxxv)). Aggregate exercise price is the strike times the shares the contract covers ((f)(2)(A)(ii)).
- **U3 (balance unit).** Spread balance is measured in aggregate underlying contract value, not contract counts ((f)(2)(A)(xxxii)d). The solver therefore balances in share-equivalents (`w_i × contracts`).

## Spreads

- **R1. What counts as a spread** ((f)(2)(A)(xxxii); Cboe manual p. 9). A set of long and short positions in different call series, put series, or both, with limited risk and reward. All of these must hold:
  - a. same underlying;
  - b. all American-style or all European-style;
  - c. all listed or all OTC;
  - d. within calls and within puts, long and short aggregate underlying value are equal;
  - e. shorts expire on or before the longs.
- **R2. Spread requirement** ((f)(2)(H)(i); Cboe manual pp. 36–39):
  - The requirement on the shorts is the lesser of their uncovered requirement (R3) and the spread's maximum potential loss.
  - The maximum potential loss comes from the intrinsic values of every leg at an underlying price equal to each exercise price in the spread. Net them at each price; the largest net loss is the figure, or zero if there is none.
  - Longs are paid in full, and short sale proceeds may be applied.
  - Cboe's worked examples total this as maximum loss plus long premiums.
- **R2a. Mixed expirations** (Cboe manual pp. 37–39). The maximum-loss method applies to several two-legged spreads grouped into one complex spread. A worked example passes condition e pair by pair:
  - long April 45 call against short March 55 call;
  - long June 60 call against short May 55 call.

  The manual adds that FINRA or brokers may require one expiration, or every short expiring at or before the nearest long. These are the `expiry_rule` policies.
- **R2b. Box spread definitions** ((f)(2)(A)(vi)). Long and short boxes need the same contract size, underlying, expiration and aggregate underlying value. A European-style long box needs 50% of the aggregate strike difference and may be valued at up to 100% of it ((H)(v)e).

## Single options

- **R3. Uncovered short option** ((f)(2)(E)(i)):
  - **Base:** 100% of the option's current market value, plus a percentage of the underlying component value, less any out-of-the-money amount.
  - **Floor:** 100% of market value plus a minimum percentage. For calls, the minimum percentage is of the underlying value; for puts, of the aggregate exercise price.

  | Underlying | Percentage | Minimum |
  |---|---|---|
  | Stock, industry (narrow) index | 20% | 10% |
  | Broad index | 15% | 10% |
- **R4. Long options** ((f)(2)(D)):
  - **Nine months or less to expiration:** 100% of the purchase price.
  - **Listed, more than nine months:** at least 75% of current market value; the remaining 25% is loan value.
- **R5. Separate margining** ((F)(i)). Each option is margined on its own unless an offset in R2, R6, R7 or R8 applies.

## Offsets

- **R6. Short straddle or combination** ((G)(i); Cboe manual p. 8). A short put and short call on the same underlying component need the greater of the two uncovered requirements, plus the market value of the other option.
- **R7. Covered positions** ((F)(ii), (I)(i), (I)(iii)):
  - A covered option needs no margin.
  - A short call against a net long position in the underlying needs no margin on the call, if the long position is margined. The long position is valued at no more than the call's strike.
  - A short put against a net short underlying position needs no margin on the put.
- **R8. Hedged underlying minimums** ((H)(v)), as maintenance on the underlying position:
  - a. Long put with long underlying (or long call with short underlying): 10% of the aggregate exercise price plus the out-of-the-money amount, capped at the standard maintenance requirement.
  - b. Conversion: 10% of the aggregate exercise price.
  - c. Reverse conversion: 10% of the aggregate exercise price, plus any amount by which the put strike exceeds the market price.
  - d. Collar: the lesser of (10% of the put's aggregate exercise price plus its out-of-the-money amount) and (25% of the call's aggregate exercise price).
- **R9. Stock maintenance** ((c)):
  - Long: 25% of market value.
  - Short under $5: the greater of $2.50 per share and 100% of market value.
  - Short at $5 or above: the greater of $5.00 per share and 30% of market value.
  - Initial requirements come from Regulation T and Cboe Rule 10.3 (to be confirmed; see Q6).

## Choosing the pairing

- **R10. The pairing is the holder's choice.** The Cboe manual lets positions be margined separately to get the lowest requirement (Initial and Maintenance Requirements, opening paragraph). FINRA (f)(2)(M) lets a customer designate which held position stands in for margin on an option. No text found prescribes a pairing method.

## Open questions

- **Q1. Fractional contracts.** No text in Rule 4210, its spread definitions, the Cboe manual, or Reg T 220.12 (as read through a mirror) allows or forbids pairing part of a contract.
  - *What the rules imply:* balance is measured in underlying value (U3), so adjusted series pair at non-integer contract ratios. For example, two 150-share contracts balance three 100-share contracts. A deliverable with cash or a second security would need value-based ratios that are rarely whole.
  - *My inference, not rule text:* this may be the source of the recollection that partial contracts to two decimals are allowed.
  - *To resolve:* find where that recollection comes from. Until then, the grid is a policy (`grid`), not a fixed rule.
- **Q2. Expiration ordering.** Condition e does not say whether it applies pair by pair or across the whole group. The Cboe examples (R2a) support pair by pair. Default `expiry_rule = pairwise`; offer the stricter readings as policies.
- **Q3. Long options beyond nine months inside a spread. Answered 2026-11-25.** The long gives up its loan value and is paid in full.
  - *Evidence:* the Cboe manual's reduced-value put spread charges the 18-month long at $200, not 75% ($150). The XSP/SPX call spread charges $1,350, not $1,012.50. The engine does this.
  - *Not evidence:* the manual's "Long Box Spread – Loan Value Utilized" example concerns the European long box treatment (R2b, (H)(v)e), not R4.
- **Q4. Cboe Rule 10.3 current text.** The manual is dated 2021-11-30. Check 10.3 for changes since then.
- **Q5. "Covered".** Covered is defined by FINRA Rule 2360(a), which has not been read.
- **Q6. Regulation T.** 12 CFR 220.12 was read only through a mirror; the eCFR page redirected. Confirm the initial percentages for stock and the deference to exchange rules for options in 220.12(f).
- **Q7. Recent amendments.** The rule history lists amendments effective 2026-06-04 and 2026-10-22. The local copy postdates both, so it should be current; record which paragraphs changed.
- **Q8. Valuing short stock in hedged positions.** The manual's worked numbers carry short stock at 100% of the call's exercise price: $5,900 for long call/short stock, and $12,100 and $8,560 for the two reverse conversions. Reading FINRA (H)(v) with market value gives $5,500, $12,600 and $8,250. Policy `hedged_short_value` selects either; the default reproduces the manual.
- **Q9. Reverse conversion, initial requirement.** The manual's table allows short sale proceeds plus 10% of the exercise price when the strike is below the sale price. Its worked example instead uses the 150% short-sale requirement ($17,900). The engine follows the example. Find which one Cboe 10.3 supports.
- **Q10. OTC long option beyond nine months, maintenance.** The manual gives 75% of intrinsic value. FINRA (f)(2)(D) states one formula for both initial and maintenance. The engine follows FINRA; only the initial figure has a fixture.
- **Q11. Exercise style for hedged-underlying offsets.** The manual requires American-style options for the R8 structures; FINRA (H)(v) does not say so. The engine requires American style.
- **Q12. Leveraged ETF factors.** The engine scales the R3 percentages and minimums by the ETF's leverage factor (1.5x, 2x, 3x), as the manual's samples do, citing Cboe Regulatory Circular RG09-97. Not yet sourced beyond the manual.
