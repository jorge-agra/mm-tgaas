# `tgaas.mm` — exterior angle and AAS

`tgaas.mm` is a self-contained extension of `set.mm`: it imports the database
and proves the exterior-angle theorem and the AAS triangle congruence
criterion. Every one of its 46 `$p` statements is a dependency of `tgaas`.

## GeoCoq

[GeoCoq](https://github.com/GeoCoq/GeoCoq) is a Coq formalization of geometry
following Schwabhäuser, Szmielew and Tarski, and it already has both results
proved: `l11_41` (the exterior angle theorem) and `l11_50_2` (AAS).

Nothing was ported from it. No Coq term was translated and no `set.mm` proof
here is a transcription; GeoCoq was used as a **route map** — its lemma
decomposition told us which intermediate facts are worth naming, and which
`set.mm` gaps had to be filled before the main line could be attempted. The
lemmas it supplied, cited in the theorem comments, are `l11_41` and
`l11_41_aux` for the exterior angle, `l11_21_a` / `l11_21_b` for degenerate
angle congruence, `bet_in_angle_bet` for flat sub-angles, `l11_30` for angle
order under congruence, `l11_13` for vertical angles, and `l4_6` for
transferring a point across a triangle congruence.

The route diverges from GeoCoq in four places, each noted at the theorem
concerned: strictness is carried as `leA /\ -. cgrA` rather than a defined
`ltA`; `tgextancgra` closes through `acopyeu` (angle-construction uniqueness)
instead of `conga_cop__or_out_ts`; `cgrgptxfr` uses `cgrg3col4` plus
`tgbtwnxfr` where GeoCoq composes `l4_6` with `cong2_conga_cong`; and the
`l11_29_a` direction of angle order is avoided entirely, which GeoCoq relies on
but this file does not need. One branch, `inagcgrasubhl`, has no GeoCoq
counterpart at all — GeoCoq's corresponding case only locates a witness its
universally quantified statement already supplies.

## Comparison with the "Triangle Congruences" blueprint

https://github.com/tirix/metamath-blueprints

| Blueprint entry | Schwabhäuser | State there | Here |
|---|---|---|---|
| `df-leag`, `isleag` | 11.27 | `Formalized` (in `set.mm`) | used as-is (`isleag`, `isleagd`) |
| `tgexta` | 11.41 | `ReadyForStmt` | **proved**, under the name `tgexta2` |
| `tgaas` | 11.50 | `StmtFormalized` | **proved** (`tgaas`, via `tgaas1`) |
| `isleag2` | 11.29 | `ReadyForProof` | not present — see below |
| `tgtrcgras` | 11.44(1) | `ReadyForStmt` | absent |
| `tgtrltad` | 11.44(2) | `ReadyForStmt` | absent; its dependency `tgexta` is now available |
| `tgass` | 11.52 | `ReadyForStmt` | absent |

So two blueprint states are made stale by this file — `tgexta` and `tgaas` both
become `Formalized`. `isleag2` does not: it was staged here as a placeholder,
never proved, and was removed rather than shipped incomplete.

### Discrepancies worth reconciling

- **Naming.** The blueprint calls the exterior-angle theorem `tgexta`; the
  label here is `tgexta2`, with `tgextale`, `tgextancgra`, `tgextalt1`,
  `tgextalt2`, `tgextaoa` and `tgexta2n` as its route. 

- **`tgexta`'s dependency list is inaccurate.** It reads
  `["oacgr", "miriso", "axpasch", "df-leag", "acopy"]`. What the proof actually
  uses: `axtgpasch` (the `set.mm` spelling — there is no `axpasch`), `acopyeu`
  as well as `acopy` (the *uniqueness* form is what yields strictness),
  `miriso`, `mirln`, `mirln2`, `mirmir`, and both `oacgr` (in
  `tgexta2lem1_inag`) and `sacgr` (in `tgextaoa`, which notes that `oacgr`
  would also close it from two supplements).

- **There is no `ltA`.** Both 11.41 and 11.44(2) are strict-inequality
  statements, but `set.mm` has `leA` and no strict counterpart. `tgexta2`
  therefore carries strictness inline as `leA` together with `-. cgrA`, and
  `tgexta2n` is the ex-falso form that makes the pair usable in a
  contradiction branch — a bare `leA` conclusion is satisfied by a congruence
  and so contradicts nothing. This convention binds `tgexta`, `tgtrltad` and
  `tgass` alike;

- **Route divergence on 11.29.** The blueprint plans `isleag2` as the transport
  tool. This file gets what `tgaas` needs from `leacgrsrc`, `leacgrtrg` and
  `leacgrtr` (an `l11_30` analogue) instead, which avoids the unproved
  `l11_29_a` direction entirely. Note that `leacgrtrg` must **not** be proved
  through `isleag2`: the reverse direction of `isleag2` depends on
  `leacgrtrg`, so that route is circular.

### Lemmas here with no blueprint entry

Several of these are `set.mm` gaps in their own right rather than AAS
scaffolding:

- `cgrahlb` — two null angles are congruent; GeoCoq `l11_21_b`, the converse of
  `cgrahl`.
- `cgrabtwnb` — two flat angles are congruent; the converse of `cgrabtwn`.
- `inagbtwn` — a flat sub-angle forces the containing angle flat; GeoCoq
  `bet_in_angle_bet`.
- `cgranorm` — ray normalization, the forward direction of `iscgra` (11.3).
- `cgrgptxfr` — transfer a segment point across a triangle congruence; 11.28
  plus `l4_6`.
- `hlorbtwn` — trichotomy bookkeeping for three collinear points.
- `inagcgratrg` — in-angle transport across an angle congruence.
- `leacgrsrc`, `leacgrtrg`, `leacgrtr` — angle order under congruence of the
  smaller, the larger, and both angles (11.30).

### Not derived anywhere in this file

The third angle congruence is never inferred from the other two: that is the
angle-sum theorem, which is false in absolute geometry. The AAS proof instead
rules out `( B .- C ) =/= ( E .- F )` with the exterior-angle theorem.

## Conforming to the blueprint

### Simple

- **Rename `tgexta2` to `tgexta`**, along with `tgexta2n` and
  `tgexta2lem1_inag`. This file is self-contained and no file outside it cites
  these labels, so it is a rename plus one `verify` run.
- **Correct `tgexta`'s `dependencies` array** in the blueprint. The accurate
  list is recorded above.
- **Use `oacgr` instead of `sacgr` in `tgextaoa`**, if the blueprint's list is
  to be read literally: one theorem, roughly ten to twenty extra rows to go
  through two supplements. There is no benefit — `oacgr` is already used in
  `tgexta2lem1_inag`, so the dependency is satisfied either way.

### Expensive, and as specified not usable here

Routing angle order through `isleag2` (11.29), as the blueprint's dependency
graph implies:

- `isleag2b` is already proved (a 53-row worksheet), so half of 11.29 exists.
- `isleag2a` (GeoCoq `l11_29_a`) is not, and it is a real construction:
  extend the *source* angle at its own vertex through `acopy` / `hlcgrex`,
  with `y` bound in the conclusion, so its `$d` conditions are mandatory and
  propagate to every caller. It shares no interface with `inagcgratrg` —
  different vertex, opposite direction of transport — so nothing already proved
  gets reused. The comparable constructions in this file ran 84 to 103
  worksheet rows each (`inagcgrasubbtwn`, `inagcgratrgmain`, `tgextahp`,
  `cgrahlb`); `isleag2a` should be scoped the same way. 
- **The payoff for this proof is zero.** `tgaas` reaches `tgexta2` through
  `leacgrtr`, and `leacgrtr` cannot be re-derived from `isleag2` — `isleag2b`
  depends on `leacgrtrg`, so that route is circular. Proving `isleag2` adds a
  parallel result; it does not shorten, simplify or replace anything here.

### Moderate work, but the decision is a community one

Honoring "strictly less" with an actual `ltA`: a `df-ltag` definition, two or
three bridge lemmas (`ltA` against `leA /\ -. cgrA`, plus the ex-falso form
that would replace `tgexta2n`), then restating `tgextalt1`, `tgextalt2`,
`tgexta2` and their consumers. Adding a definition to `set.mm` is the part that
takes discussion, and `tgtrltad` and `tgass` will want the same answer.

