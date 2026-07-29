# Agricultural Costing & Break-Even Tool

> A self-service Excel decision tool that lets a farmer and a business advisor work out **what each crop actually earns, what it must sell to break even, and which crop deserves the land** — in a single sitting, with no Excel knowledge required.

Built and donated as a **volunteer project** for **MATI Northern Galilee (מט"י צפון הגליל)**, a nonprofit Small Business Development Center serving small businesses and farmers in the Galilee Panhandle.

**Language:** the tool, its guide and its glossary are in Hebrew — that's who uses it.

---

## The problem

Many small farmers price produce by habit. They plan around the Grade A market price and never account for the Grade B share, the waste, the produce lost in the field and in sorting, or the fixed costs that get paid whether or not anything grows. The result is a farmer working a full season on a crop that is quietly losing money.

MATI's advisors needed a tool they could fill in *with* a farmer during a meeting — not a model that requires an analyst to operate.

## Structure

Seven sheets, each feeding the next. Data is entered once and flows through the whole model. Supports up to **7 crops** side by side.

| # | Sheet | Purpose |
|---|---|---|
| 1 | `מדריך` — Guide | Order of work, colour legend, plain-language glossary, FAQ |
| 2 | `דשבורד` — Dashboard | KPIs, charts, alerts, and Net Revenue Management analysis |
| 3 | `נק' איזון` — Break-Even | Fixed costs, variable costs, contribution margin, break-even in units and shekels |
| 4 | `תנובה_והפסדים` — Yield & Losses | Dunams, yield per dunam, field and sorting loss → net sellable yield |
| 5 | `תמחיר_לפי_דרגה` — Pricing by Grade | Quality mix and prices → weighted average price per kg |
| 6 | `ניתוח_רגישות` — Sensitivity | ±30% stress test on both price and cost, per crop |
| 7 | `רווח_לדונם` — Profit per Dunam | The planning metric: profit per unit of land, by crop |

## The model

**Net yield** — not every kilogram grown is a kilogram sold:

```
Net yield = dunams × yield/dunam × (1 − field loss %) × (1 − sorting loss %)
```

**Weighted average price** — the core correction the tool exists to make. Waste is derived automatically as `1 − %Grade A − %Grade B` and earns nothing:

```
Weighted price = (%Grade A × Price A) + (%Grade B × Price B)
```

**Break-even, per crop and for the whole farm.** Per crop it's the straightforward fixed-costs-over-contribution calculation, rounded up to a whole unit. For the farm as a whole the tool uses the **weighted-average contribution margin method**, which handles a multi-crop business correctly rather than treating each crop as if it carried the fixed costs alone:

```
Break-even units   = ROUNDUP(total fixed costs ÷ contribution per unit)
Break-even revenue = total fixed costs ÷ Σ(contribution ratio × share of sales)
```

**Profit per dunam** — land is the scarcest resource, so crops compete on return per dunam after fixed costs are allocated across the farm's total area.

**Sensitivity analysis** — each crop is re-run across a ±30% range in 10-point steps, separately for selling price and for variable cost. Every row returns a new contribution, a new profit or loss, a recalculated break-even quantity, and a plain ✅ / ❌ verdict on whether the crop still works at that price.

**Net Revenue Management** — for each crop the dashboard compares a 10% price increase against a 10% variable-cost reduction, at both per-kg and total-profit level, and names the stronger lever. It answers the question farmers actually ask: *should I push for a better price, or cut my costs?*

## Design decisions worth noting

**Fixed costs include what farmers usually leave out.** The fixed-cost sheet has 14 categories, and among rent, insurance, depreciation and interest it also lists **unpaid family labour** and **family living expenses**. On a family farm these are real economic costs; excluding them is exactly how a farm appears profitable while the family gets poorer.

**A cost-per-kg calculator for people who don't think in per-kg terms.** Farmers know what they paid the fuel supplier, not what fuel costs per kilogram of peppers. A side calculator takes the amount paid and the crop, looks up that crop's net yield with `INDEX`/`MATCH` against an array constant, and returns ₪/kg ready to drop into the cost table.

**Built for non-technical users.** Colour-coded inputs (yellow = type here, calculated cells left alone), a 💡 explanation line on every sheet stating the formula in words, a Hebrew guide with the correct order of work and a glossary, and verdict columns that return ✅/❌ rather than a number the user has to interpret.

**It ships empty.** This is a template, not a case study. Every input cell is zero until a farmer fills it in — there is no client data in this repository.

## Excel techniques used

- Multi-sheet model with a single entry point — crop names and quantities propagate by reference, so nothing is typed twice
- Weighted-average contribution margin break-even for a multi-product business
- `SUMPRODUCT` for revenue and total variable cost across all crops
- `INDEX` + `MATCH` against an array constant for the cost-per-kg lookup
- `IFERROR` throughout so an unfilled template shows zeros rather than `#DIV/0!`
- `NA()` in chart helper columns to suppress empty crops from pie charts
- Dynamic KPI text built with `TEXT()` and concatenation (e.g. `₪12,400 לדונם`)
- Conditional verdict logic driving the sensitivity and NRM outputs

## Repository contents

| Path | Description |
|---|---|
| `קובץ_תמחיר_חקלאי.xlsx` | The tool — 7 sheets, ready to fill in |
| `docs/workbook-preview.pdf` | Full PDF export of every sheet, so you can view the tool without Excel |
| `LICENSE` | MIT |

## How to use it

1. Download `קובץ_תמחיר_חקלאי.xlsx` (or browse `docs/workbook-preview.pdf` first).
2. Open the **מדריך** (Guide) sheet and follow the stated order of work.
3. Fill in the yellow cells only. Everything else calculates itself.
4. Read the **דשבורד** (Dashboard) sheet for KPIs, alerts and the NRM recommendation.

## About

Built by **Ilan Metrikin** — economics & data analyst.
📧 [imetrikin@gmail.com](mailto:imetrikin@gmail.com) · [LinkedIn](https://www.linkedin.com/in/ilan-metrikin-36a652218/)
