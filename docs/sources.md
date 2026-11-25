# Sources

Accessed 2026-11-25 unless noted.

## Rule texts

| Source | Status | What it settled |
|---|---|---|
| [FINRA Rule 4210](https://www.finra.org/rules-guidance/rulebooks/finra-rules/4210) | Read verbatim; local copy `refs/finra-4210-2026-11-25.*` | Spread definition, maximum potential loss method, uncovered rates, straddles, covered positions, hedged-underlying minimums, stock maintenance. Basis for rules.md. |
| [Cboe Margin Manual, 2021-11-30](https://cdn.cboe.com/resources/membership/Margin_Manual.pdf) | Read through pdftotext; local copy `refs/cboe-margin-manual-2021-11-30.*`; the license forbids redistribution | Same spread conditions as FINRA, worked maximum-loss examples with mixed expirations, complex-spread examples. Source of the fixtures. |
| [Cboe strategy-based margin page](https://www.cboe.com/en/markets/us/options/margin/strategy-based-margin/) | Read | Uncovered rates and the straddle rule agree with the manual; cites Cboe Rule 10.3. |
| [FINRA Interpretations of Rule 4210, from 2026-06-04](https://www.finra.org/rules-guidance/guidance/interps-4210-202606) | Partly read (about the first 40k of 365k characters) | No fractional-contract text in the part read. The rest is still to read. |
| [Regulation T, 12 CFR 220](https://www.ecfr.gov/current/title-12/chapter-II/subchapter-A/part-220) | eCFR redirected; [LII mirror of 220.12](https://www.law.cornell.edu/cfr/text/12/220.12) read | 220.12(f) defers option requirements to exchange rules. No fractional-contract text. |
| [FINRA Notice to Members 06-26](https://www.finra.org/rules-guidance/notices/06-26) | Search summary only | Describes condors and iron spreads as combinations of butterflies and boxes. |
| [FINRA Regulatory Notice 12-44](https://www.finra.org/rules-guidance/notices/12-44) | Not read | Likely the amendment that adopted the general spread definition and maximum-loss rule. Read it to date the change. |

## Papers

| Source | Status | Relevance |
|---|---|---|
| Rudd and Schroeder, "The Calculation of Minimum Margin," *Management Science* 28(12):1368–1379, 1982. [doi:10.1287/mnsc.28.12.1368](https://pubsonline.informs.org/doi/pdf/10.1287/mnsc.28.12.1368), [RePEc](https://ideas.repec.org/a/inm/ormnsc/v28y1982i12p1368-1379.html) | Not read (paywalled) | Transportation-problem formulation for two-legged spreads, solved exactly and compared with heuristics. |
| Matsypura and Timkovsky, "Margining Option Portfolios by Network Flows," *Networks*, 2012. [doi:10.1002/net.20465](https://zendy.io/title/10.1002/net.20465); working paper [BAWP 05/2010](https://ses.library.usyd.edu.au/handle/2123/8173) | Blocked to automated fetch (403); download by hand | Heuristic network-flow algorithm for three- and four-leg spreads, using minimum-cost and maximum flow. |
| Matsypura and Timkovsky, "Combinatorics of Option Spreads: The Margining Aspect," [BAWP 04/2010](https://ses.library.usyd.edu.au/handle/2123/8172) | Blocked (403); download by hand | Models spreads with up to 134 legs. Notes the SEC approved complex spreads of 5 to 12 legs in December 2005. Argues margining under maximum-loss rules is polynomial by network flows, without identifying individual spreads. |
| Matsypura and Timkovsky, "Combinations of Option Spreads," ICORES 2012, pp. 321–331. [doi:10.5220/0003798003210331](https://www.scitepress.org/Papers/2012/37980/) | Not read | Builds multi-leg spreads from two-, three- and four-leg ones. |

**Before claiming anything new:** spec §3.1 formulates spreads as one flexible maximum-loss group per class. It may be what Matsypura and Timkovsky already do in the 04/2010 paper. Read it before describing the formulation as original.

## Industry

| Source | Status | Relevance |
|---|---|---|
| [ION, "Optimizing Cboe strategy allocations with linear programming"](https://iongroup.com/blog/markets/cboe-strategy-based-margin-optimization-and-options-margin-requirements/), 2026-04-17 | Read through a subagent's summary | Enumerates candidate strategies, prices one unit of each, solves an LP/ILP. On 38 real portfolios it was never worse than greedy. Worked example: three calls margined at $33,600 as naked, $9,000 as two spreads and $7,300 as a butterfly. The post gives no prices, so the example cannot be reproduced. No solve times. Evidence that greedy pairing is still common in production. |
