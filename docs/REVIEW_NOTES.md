# Review notes

These are the problems I ran into, or had to steer around, while formalizing this project. Each
entry gives the problem and the fix. I think they are the kind of thing a reviewer of Lean
proofs should look for.

## 1. The statement is false for p = 3

**Problem.** Wolstenholme's theorem is often quoted as "for every odd prime". That is wrong.
For `p = 3`, `C(5, 2) = 10`, and `10` is not `1` modulo `27`. The harmonic statement also fails:
`H_2 = 3/2`, and `9` does not divide `3`. The root cause sits in one place. The proof needs
`∑ 1/k² ≡ 0 (mod p)`, which comes from a power sum `∑ k^m` with `m = 2`. Mathlib's
`FiniteField.sum_pow_lt_card_sub_one` needs `m < p - 1`, and for `p = 3` we have `m = p - 1`.
Indeed `1 + 1/4 ≡ 2 (mod 3)`.

**Fix.** The hypothesis is `5 ≤ p`. It is turned into `2 < p - 1` in exactly two places,
`sum_Ioo_inv_mul_inv_sub_eq_zero` and `dvd_sum_inv_sq_num`, each time to apply
`sum_Ioo_inv_pow_eq_zero` with `m = 2`. To show that the bound is sharp, `Main.lean` has the
counterexamples `not_choose_modEq_one_three` and `not_sq_dvd_harmonic_num_three`. I also checked
the statements numerically for all primes below 40 before writing any proof.

## 2. Different results need different hypotheses

**Problem.** It is tempting to put `5 ≤ p` on everything. But Babbage's theorem
(`C(2p - 1, p - 1) ≡ 1` modulo `p²`) is true for `p = 3`, since `10 ≡ 1 (mod 9)`. It only fails
for `p = 2`, where `C(3, 1) = 3` and `3` is not `1` modulo `4`. A hypothesis that is stronger than
needed is a real defect, because it makes the theorem weaker than the mathematics.

**Fix.** `babbages_theorem` assumes only `p.Prime` and `p ≠ 2`, and its proof avoids power sums
entirely. `not_choose_modEq_one_two` shows that `p ≠ 2` is needed. Zolotarev's lemma has no
oddness assumption at all, because for `p = 2` every unit is a square and both sides are `1`. A
review pass also removed unneeded hypotheses from helper lemmas.
`pow_mul_eq_zero_of_castHom_eq_zero` first assumed `p.Prime` and now has no hypothesis on `p`.
`support_toPerm_of_ne_one` now asks for `g ≠ 1` instead of "g generates and p is odd".

## 3. Natural number subtraction

**Problem.** The headline statements use `2 * p - 1` and `p - 1`, and the lemmas use `p - k`.
All of these are truncated subtraction on `ℕ`. The reflection `k ↦ p - k` is an involution only
on `k ≤ p`, because `p - (p - k) = k` needs `k ≤ p`. In `ZMod p`, rewriting the cast of `p - k`
as `-k` uses `Nat.cast_sub`, which needs `k ≤ p` too. A congruence written as `p ^ 3 ∣ C - 1`
would also hide a truncated subtraction in the conclusion.

**Fix.** The conclusions use `Nat.ModEq`, so they never subtract `1` from a binomial
coefficient. The only subtractions left there are `2 * p - 1` and `p - 1`, which are exact
because `p ≥ 1`. The two reindexings that involve subtraction, `k ↦ p - k` and `i ↦ i + 1` with
inverse `k ↦ k - 1`, go through `Finset.prod_nbij'` with explicit membership goals, and `omega`
closes them. I checked the edge cases `p = 0` and `p = 1` for the general lemmas. For example, at
`p = 0` both sides of `choose_mul_factorial_eq_prod` are `1`.

## 4. A type ascription that is not a cast

**Problem.** While testing statements I wrote `∑ k ∈ Ioo 0 7, (k : ZMod 49)⁻¹`, meaning "cast
the natural number `k` into `ZMod 49`". Lean read it differently. The type of `k` was still
unknown, so the ascription made `k` itself an element of `ZMod 49`. Here Lean then failed,
because Mathlib puts no order on `ZMod 49`, so `Ioo 0 7` cannot be formed there. The same thing
happened in a test inside `Multiset.map fun u => ...`. Both times the error was loud, but the
mechanism is dangerous. When the needed instances do exist, the index silently gets a different
type.

**Fix.** In the library, every sum over natural numbers runs over `Ioo 0 p` or `Ioo 0 (n + 1)`
with `p n : ℕ`, which fixes `k : ℕ`. I confirmed this with `#check`, which prints the casts as
`↑k`. In test code I write `Ioo (0 : ℕ) 7` and give binder types explicitly.

## 5. ZMod inverses outside the units are junk

**Problem.** In Mathlib, `x⁻¹` is defined for every `x : ZMod n`. When `x` is not a unit, the
value is junk. For example `(4 : ZMod 36)⁻¹ = 1`, while `(4 : ZMod 6)⁻¹ = 5`. So reducing an
inverse from `ZMod 36` to `ZMod 6` does not give the inverse. A lemma like
"the reduction of `k⁻¹` is `k⁻¹`" is false unless `k` is coprime to the modulus.

**Fix.** Inverses of naturals only appear for `0 < k < p`. Those are units modulo `p ^ n`, and
modulo any `M` coprime to `(p - 1)!`. The only other inverse is `0⁻¹ = 0`. It comes up in the sum
over all of `ZMod p` in `sum_Ioo_inv_pow_eq_zero`, and in the `k = 0` case of
`castHom_inv_natCast`. I never cast an inverse directly. `castHom_inv_natCast` is proved from
`k * k⁻¹ = 1` and uniqueness of inverses, so its hypotheses are exactly the ones the argument
needs.

## 6. Mathlib is built with the module system

**Problem.** My first skeleton used plain `import Mathlib...` lines. With Mathlib `v4.35.0`,
Lake then prints a warning for every such import, saying the file should use the module system.
That would fail CI, which builds with `--wfail`.

**Fix.** Every library file starts with `module`, uses `public import` for what the statements
need, and wraps its declarations in `public section`. The one definition, `mulSign`, is marked
`@[expose]` so that other modules can unfold it. Imports that only proofs need are plain
`import`, so they are not passed on to the files that import this one. That covers the tactic
`linear_combination` and a few lemma files. I also dropped a heavy import (`Harmonic.Bounds`, which
pulls in integration) and reproved the one lemma I needed from it. This cut the build from about
2950 jobs to about 2320.

## 7. What `decide` can and cannot do

**Problem.** I do not use `native_decide`, because it trusts compiled code, and CI rejects it.
Plain `decide` has limits. It got stuck on `¬ 9 ∣ (3/2 : ℚ).num`, because rational arithmetic
does not reduce in the kernel. In another spot it refused to run, because a local
`Fact p.Prime` instance appeared in the goal as a free variable. Also, `congr 1` once closed a
goal `Icc 1 (p - 1) = Ioo 0 p` by unfolding both sides to the same list. That proof would break
silently if Mathlib changed how intervals are implemented.

**Fix.** For the rational number I proved `(3/2 : ℚ).num = 3` with `Rat.num_div_eq_of_coprime`.
After that, `decide` only checks two small facts: that `3` and `2` are coprime, and that `9` does
not divide `3`. For `ZMod 2` I used `fin_cases`. For the interval I replaced the accidental
definitional proof with an explicit `ext` and `omega`. The only proofs that are `decide` alone
are `not_choose_modEq_one_three` and `not_choose_modEq_one_two`. They only touch `Nat.choose` and
`Nat.ModEq` on small numbers.

## 8. Names must not collide with Mathlib

**Problem.** No declaration here should reuse a Mathlib name. Being inside
`namespace Wolstenholme` is not enough. If a name like `sum_Ioo_reflect` also existed as
`Finset.sum_Ioo_reflect`, then `open Finset` would make every use ambiguous. `@[to_additive]`
also creates a second name (`sum_Ioo_reflect` from `prod_Ioo_reflect`) that is easy to forget.

**Fix.** I checked all 49 names twice: the 48 declarations in the source, plus the
`sum_Ioo_reflect` that `@[to_additive]` creates. A small Lean program compared the last name
component of each one with all 370,714 constants in the loaded environment. A text search over
the 12,488 `.lean` files of Lean core and of all nine packages in `.lake/packages` looked for
declarations with the same name. Neither found a clash. My first version of the Lean check had a
bug: it skipped every name starting with `eq_`, to ignore generated equation lemmas such as
`eq_1`, and so it missed `eq_zero_of_one_add_sq_eq_one`. A review pass also renamed several
lemmas to match Mathlib conventions. For example, `natCast_mul_inv_self` became
`natCast_mul_inv_cancel`, because Mathlib no longer uses `mul_inv_self`. And
`choose_eq_one_of_sq` became `natCast_choose_eq_one_zmod_sq`, because `_of_` in a Mathlib name
introduces a hypothesis.
