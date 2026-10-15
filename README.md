# Wolstenholme's theorem and Zolotarev's lemma in Lean 4

[![CI](https://github.com/fahad-96/wolstenholme-zolotarev/actions/workflows/ci.yml/badge.svg)](https://github.com/fahad-96/wolstenholme-zolotarev/actions/workflows/ci.yml)
![Lean](https://img.shields.io/badge/Lean-v4.35.0-blue)
![Mathlib](https://img.shields.io/badge/Mathlib-v4.35.0-blue)

This repository formalizes two classical results of elementary number theory in Lean 4,
on top of Mathlib. Neither result is in Mathlib yet.

Every proof is complete. There is no `sorry`, `admit` or `native_decide`, no new axiom, and no
`set_option`. The build has zero warnings with Mathlib's standard style linters turned on.

## The results

### Wolstenholme's theorem

For every prime $p \ge 5$,

$$\binom{2p-1}{p-1} \equiv 1 \pmod{p^3}.$$

Two congruences for harmonic sums come with it. For every prime $p \ge 5$,

$$1 + \frac{1}{2} + \frac{1}{3} + \cdots + \frac{1}{p-1} \equiv 0 \pmod{p^2}
\qquad\text{and}\qquad
1 + \frac{1}{2^2} + \frac{1}{3^2} + \cdots + \frac{1}{(p-1)^2} \equiv 0 \pmod{p}.$$

As rational numbers, this says that $p^2$ divides the numerator of the harmonic number
$H_{p-1}$, and that $p$ divides the numerator of the second sum. The binomial congruence needs
the second one, in the form $\sum_{k=1}^{p-1} \frac{1}{k(p-k)} \equiv 0 \pmod p$.

On the way we also get Babbage's theorem. For every odd prime $p$,
$\binom{2p-1}{p-1} \equiv 1 \pmod{p^2}$.

The bounds on $p$ are sharp. The repository proves this for the binomial congruences and for
the harmonic number. For $p = 3$ we have $\binom{5}{2} = 10 \not\equiv 1 \pmod{27}$ and
$H_2 = 3/2$. For $p = 2$ we have $\binom{3}{1} = 3 \not\equiv 1 \pmod 4$.

### Zolotarev's lemma

Let $p$ be a prime and let $a$ be an integer with $p \nmid a$. Then the Legendre symbol
$\left(\frac{a}{p}\right)$ is the sign of the permutation $x \mapsto ax$ of $\mathbb{Z}/p\mathbb{Z}$.

As a corollary, for an odd prime $p$ the sign of $x \mapsto -x$ is $(-1)^{(p-1)/2}$.

## The Lean statements

These are the headline theorems of [`Wolstenholme/Main.lean`](Wolstenholme/Main.lean) and
[`Zolotarev/Main.lean`](Zolotarev/Main.lean). Here they are written with full names, and with the
section variables spelled out in each signature.

```lean
theorem Wolstenholme.wolstenholmes_theorem {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]

theorem Wolstenholme.choose_two_mul_modEq_two {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    (2 * p).choose p ≡ 2 [MOD p ^ 3]

theorem Wolstenholme.babbages_theorem {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 2]

theorem Wolstenholme.sq_dvd_harmonic_num {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    (p : ℤ) ^ 2 ∣ (harmonic (p - 1)).num

theorem Wolstenholme.two_le_padicValRat_harmonic {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    2 ≤ padicValRat p (harmonic (p - 1))

theorem Wolstenholme.dvd_sum_inv_sq_num {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    (p : ℤ) ∣ (∑ k ∈ Finset.Ioo 0 p, ((k : ℚ) ^ 2)⁻¹).num

theorem Zolotarev.zolotarevs_lemma {p : ℕ} [Fact p.Prime] {a : ℤ} (ha : (a : ZMod p) ≠ 0) :
    (Equiv.Perm.sign (Equiv.mulLeft₀ (a : ZMod p) ha) : ℤ) = legendreSym p a

theorem Zolotarev.sign_neg_eq_χ₄ {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (Equiv.Perm.sign (Equiv.neg (ZMod p)) : ℤ) = ZMod.χ₄ p
```

The congruences are stated with `Nat.ModEq`, so no conclusion subtracts `1` from a binomial
coefficient. The only subtractions left are `2 * p - 1` and `p - 1`, which are exact because
`p ≥ 1`.

## Why this is not already in Mathlib

I checked the Mathlib source at the pinned tag `v4.35.0` (commit `56a0058`, 13 October 2026)
and on `master`.

* A search of `Mathlib`, `Archive` and `Counterexamples` for `wolstenholme`, `zolotarev` and
  `babbage` (any case) finds nothing.
  GitHub code search on master:
  [Wolstenholme](https://github.com/search?q=repo%3Aleanprover-community%2Fmathlib4+wolstenholme&type=code),
  [Zolotarev](https://github.com/search?q=repo%3Aleanprover-community%2Fmathlib4+zolotarev&type=code).
  The only hit for Wolstenholme is the list of 1000 theorems.
* That list,
  [`docs/1000.yaml`](https://github.com/leanprover-community/mathlib4/blob/v4.35.0/docs/1000.yaml#L1847-L1848),
  has an entry for Wolstenholme's theorem with only a `title`, and no `decl`, `decls` or
  `statement` field. In that file this means Mathlib has no formal proof yet.
* The harmonic number files only treat the prime 2:
  [`Harmonic/Int.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.35.0/Mathlib/NumberTheory/Harmonic/Int.lean)
  proves `padicValRat_two_harmonic` and `harmonic_not_int`.
* For the Legendre symbol, Mathlib has Gauss's lemma and Eisenstein's lemma
  ([`GaussEisensteinLemmas.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.35.0/Mathlib/NumberTheory/LegendreSymbol/GaussEisensteinLemmas.lean)),
  but nothing that relates it to the sign of a permutation.
* I also considered Korselt's criterion for Carmichael numbers. It is already in Mathlib as
  `Nat.isCarmichael_iff_korselt`
  ([search](https://github.com/search?q=repo%3Aleanprover-community%2Fmathlib4+korselt&type=code)),
  so I left it out.

## Proof outline

### Wolstenholme's theorem

Work in `ZMod (p ^ n)`. For `0 < k < p`, the residue of `k` is a unit.

1. **Pairing.** Since `k + (p - k) = p`, we get `1/k + 1/(p - k) = p / (k (p - k))`.
2. **The key sum mod p.** Let `W = ∑ 1/(k (p - k))`. Modulo `p` each term is `-1/k²`. The map
   `x ↦ 1/x` permutes `ZMod p`, so `∑ 1/k² = ∑ k²`. That power sum vanishes when `2 < p - 1`,
   by Mathlib's `FiniteField.sum_pow_lt_card_sub_one`. So `W ≡ 0 (mod p)` for `p ≥ 5`.
3. **The harmonic sum.** Summing step 1 over `k` gives `2 H = p W`. Since `W ≡ 0 (mod p)`, the
   right side vanishes mod `p²`. As `p` is odd, `H ≡ 0 (mod p²)`.
4. **The binomial as a product.** `C(2p - 1, p - 1) * (p - 1)! = ∏ (p + k)`, so in
   `ZMod (p ^ n)` the binomial coefficient equals `P = ∏ (1 + p/k)`.
5. **Babbage, mod p².** Here `p² = 0`, so `P = 1 + p H`. Step 3's identity gives
   `2 p H = p² W = 0`, hence `p H = 0` and `P = 1`. This needs only that `p` is odd.
6. **Wolstenholme, mod p³.** Pair the factor for `k` with the factor for `p - k`. By step 1,
   `(1 + p/k)(1 + p/(p - k)) = 1 + 2p² / (k (p - k))`. So `P² = 1 + 2p² W`, because `p⁴ = 0`.
   By step 2, `p² W = 0`, so `P² = 1`. Finally `P = 1 + y` with `y` a multiple of `p`, so
   `y³ = 0`. From `(1 + y)² = 1` and the fact that `2` is a unit, `y = 0`.
7. **Back to rational numbers.** Multiplying by `(p - 1)! ^ m` clears the denominators of
   `∑ 1/k^m`. Since `(p - 1)!` is coprime to `p`, a congruence in `ZMod (p ^ j)` moves to the
   numerator of the rational sum. This gives the statements about `harmonic (p - 1)` and about
   `∑ 1/k²`.

### Zolotarev's lemma

1. The map `u ↦ sign (x ↦ u x)` is a group homomorphism from `(ZMod p)ˣ` to `{±1}`.
2. A square `u = r²` has sign `sign(r)² = 1`.
3. Take a generator `g` of the cyclic group `(ZMod p)ˣ`, with `p` odd. Then `x ↦ g x` fixes
   `0` and moves the `p - 1` nonzero residues around one cycle. Its sign is
   `-(-1)^(p - 1) = -1`.
4. A non-square is an odd power of `g`, so its sign is `-1`.
5. The quadratic character is `1` on nonzero squares and `-1` on non-squares, so the two agree.
   For `p = 2` every unit is a square, so no oddness assumption is needed.

## File map

| File | Contents |
| --- | --- |
| [`Wolstenholme/Basic.lean`](Wolstenholme/Basic.lean) | Inverses of `0 < k < p` in `ZMod (p ^ n)`, the pairing identity, reduction mod `p`, the reflection `k ↦ p - k`, and two lemmas about numerators and denominators of rationals. |
| [`Wolstenholme/PowerSums.lean`](Wolstenholme/PowerSums.lean) | Power sums and inverse power sums over `0 < k < p` vanish in `ZMod p`. The key sum `∑ 1/(k (p - k))` vanishes for `p ≥ 5`. |
| [`Wolstenholme/Harmonic.lean`](Wolstenholme/Harmonic.lean) | The harmonic congruence in `ZMod (p ^ 2)`, and the transfer from `ZMod M` to numerators of rational sums. |
| [`Wolstenholme/Binomial.lean`](Wolstenholme/Binomial.lean) | The product formula for `C(2p - 1, p - 1)`, Babbage's theorem in `ZMod (p ^ 2)` and Wolstenholme's theorem in `ZMod (p ^ 3)`. |
| [`Wolstenholme/Main.lean`](Wolstenholme/Main.lean) | The headline statements with `Nat.ModEq`, numerators and `padicValRat`, plus the counterexamples for `p = 2` and `p = 3`. |
| [`Zolotarev/SignHom.lean`](Zolotarev/SignHom.lean) | The sign homomorphism on `(ZMod p)ˣ`, its value on squares, generators and non-squares. |
| [`Zolotarev/Main.lean`](Zolotarev/Main.lean) | Zolotarev's lemma and the corollary for `x ↦ -x`. |
| [`Checks.lean`](Checks.lean) | Restates each headline theorem and prints its axioms. |
| [`docs/WALKTHROUGH.md`](docs/WALKTHROUGH.md) | Every lemma explained in a few sentences. |
| [`docs/REVIEW_NOTES.md`](docs/REVIEW_NOTES.md) | Mistakes I hit or avoided while formalizing, and how I fixed them. |

## Building

You need [elan](https://github.com/leanprover/elan). The toolchain is pinned in
`lean-toolchain` (`leanprover/lean4:v4.35.0`), and Mathlib is pinned to the `v4.35.0` tag in
`lake-manifest.json`.

```bash
lake exe cache get
```

```bash
lake build
```

```bash
lake env lean Checks.lean
```

The first command downloads the compiled Mathlib cache. The second builds both libraries.
The third prints the axioms of every headline theorem.

## Axioms

Output of `lake env lean Checks.lean`:

```text
'Wolstenholme.wolstenholmes_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
'Wolstenholme.choose_two_mul_modEq_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'Wolstenholme.babbages_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
'Wolstenholme.sq_dvd_harmonic_num' depends on axioms: [propext, Classical.choice, Quot.sound]
'Wolstenholme.two_le_padicValRat_harmonic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Wolstenholme.dvd_sum_inv_sq_num' depends on axioms: [propext, Classical.choice, Quot.sound]
'Wolstenholme.natCast_choose_eq_one_zmod_cube' depends on axioms: [propext, Classical.choice, Quot.sound]
'Wolstenholme.sum_Ioo_inv_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Wolstenholme.not_choose_modEq_one_three' depends on axioms: [propext]
'Wolstenholme.not_sq_dvd_harmonic_num_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'Wolstenholme.not_choose_modEq_one_two' depends on axioms: [propext]
'Zolotarev.zolotarevs_lemma' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zolotarev.sign_mulLeft₀_eq_quadraticChar' depends on axioms: [propext, Classical.choice, Quot.sound]
'Zolotarev.sign_neg_eq_χ₄' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the three standard axioms of Lean and Mathlib. The two binomial counterexamples,
`not_choose_modEq_one_three` and `not_choose_modEq_one_two`, are proved by `decide` alone, so
they need only `propext`.

## What CI checks

The [workflow](.github/workflows/ci.yml) runs on every push to `main`, on every pull request
and on manual runs. It uses
[`leanprover/lean-action`](https://github.com/leanprover/lean-action) to:

* build with `lake build --wfail`, so any warning fails the build, including the Mathlib style
  linters that `lakefile.toml` turns on;
* run `lake lint`, which applies the Batteries environment linters (missing docstrings, unused
  arguments, simp normal forms and more);
* replay every declaration of both libraries through the kernel with `leanchecker`.

Then it runs `Checks.lean` and fails if any theorem uses an axiom other than `propext`,
`Classical.choice` and `Quot.sound`. Finally it greps the sources for `sorry`, `admit`,
`native_decide`, `axiom`, `set_option` and `unsafe`.

The only Lean options live in `lakefile.toml`. They are the ones from Mathlib's project
template, plus `autoImplicit = false`, and they only make the build stricter or match Mathlib's
own settings.

## Documentation

* [`docs/WALKTHROUGH.md`](docs/WALKTHROUGH.md) explains every lemma: what it says, how the proof
  works and which lemmas from Mathlib and Lean core it uses.
* [`docs/REVIEW_NOTES.md`](docs/REVIEW_NOTES.md) lists the traps I ran into, such as statements
  that fail for `p = 3`, natural number subtraction and junk values of `ZMod` inverses.

## License

Apache 2.0, the same license as Mathlib. See [`LICENSE`](LICENSE).
