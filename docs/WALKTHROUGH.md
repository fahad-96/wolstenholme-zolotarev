# Walkthrough

This file explains every declaration in the project, file by file, in the order of the imports.
For each one it says what the statement means, how the proof goes, and which library lemmas
it uses. Most come from Mathlib, and a few basic facts about `ℕ` come from Lean core. You only need to know Lean basics: `rw`, `simp`, `exact`, `have`, `obtain` and
`omega`.

Notation used below. `p` is a natural number, usually a prime. `Ioo 0 p` is the finset of
naturals `k` with `0 < k < p`. In `ZMod n`, `x⁻¹` is Mathlib's inverse on `ZMod n`. It is
defined for every element, and it is a true inverse exactly when `x` is coprime to `n`.

## A note on the overall design

All congruences are proved as equations in `ZMod (p ^ n)`. This is easier than working with
`Int.ModEq` and division, because `ring` and `linear_combination` work in any commutative
ring. The main statements only invert `k` with `0 < k < p`, which is a real inverse because
`k` is coprime to the modulus. Two helpers also meet `0⁻¹ = 0`: `castHom_inv_natCast` allows
`k = 0`, and `sum_Ioo_inv_pow_eq_zero` reindexes by `x ↦ x⁻¹` on all of `ZMod p`.

`Basic.lean` and `Harmonic.lean` prove the lemmas that move a congruence in `ZMod M` to the
numerator of a rational number. `Main.lean` applies them, and translates the results to
`Nat.ModEq`, to `harmonic (p - 1)` and to `padicValRat`.

Every library file is a Lean `module`. Imports that the statements need are `public import`.
Imports that only proofs need are plain `import`: the tactic `linear_combination`, and a few
lemma files such as `Mathlib.Data.Nat.Prime.Factorial`.

## `Wolstenholme/Basic.lean`

### `prod_Ioo_reflect` and `sum_Ioo_reflect`

These say that `∏ k ∈ Ioo 0 p, f (p - k) = ∏ k ∈ Ioo 0 p, f k`, and the same for sums. The map
`k ↦ p - k` is its own inverse on `Ioo 0 p`, so the proof is `Finset.prod_nbij'` with that map
in both directions. Four side goals say that both maps send `Ioo 0 p` into itself and undo
each other. They are facts about natural number subtraction, which `omega` closes. The fifth
says the factors match, and it is `rfl`. The sum version comes for free from `@[to_additive]`.

### `coprime_pow_of_pos_of_lt`

For a prime `p` and `0 < k < p`, `k` is coprime to `p ^ n`. Mathlib's
`Nat.coprime_of_lt_prime` gives `p.Coprime k`. Then `Nat.Coprime.symm` and
`Nat.Coprime.pow_right` finish it.

### `coprime_factorial_sub_one`

The prime `p` is coprime to `(p - 1)!`. This is Mathlib's `Nat.Prime.coprime_factorial_of_lt`
with `n = p - 1`. The bound `p - 1 < p` comes from `Nat.sub_lt`.

### `natCast_mul_inv_cancel`

For `0 < k < p`, `k * k⁻¹ = 1` in `ZMod (p ^ n)`. This is Mathlib's `ZMod.coe_mul_inv_eq_one`,
which needs `k` to be coprime to the modulus. The coprimality is
`coprime_pow_of_pos_of_lt`. `inv_add_inv_sub`, `castHom_inv_natCast` and
`natCast_choose_eq_prod_one_add` use it to cancel `k * k⁻¹`.

### `inv_add_inv_sub`

The pairing identity: `k⁻¹ + (p - k)⁻¹ = p * (k⁻¹ * (p - k)⁻¹)` in `ZMod (p ^ n)`. Write
`a = k` and `b = p - k`, so `a + b = p` by `Nat.add_sub_cancel'`. The identity is then a
linear combination of `a * a⁻¹ = 1`, `b * b⁻¹ = 1` and `a + b = p`, and `linear_combination`
checks it with `ring`. In `ZMod (p ^ n)`, `ring` treats `a⁻¹` and `b⁻¹` as plain atoms, which
is exactly what we want.

### `castHom_inv_natCast`

Reducing `k⁻¹` from `ZMod (p ^ n)` to `ZMod p` gives `k⁻¹` in `ZMod p`, for `k < p`. The case
`k = 0` is trivial because `0⁻¹ = 0` (`ZMod.inv_zero`). Otherwise apply the ring hom
`ZMod.castHom` to `k * k⁻¹ = 1` and use `map_mul`, `map_natCast` and `map_one`. So the image
`y` of `k⁻¹` satisfies `k * y = 1`. Since also `k * k⁻¹ = 1` in `ZMod p`, inverses are unique,
and a one-line `linear_combination` shows `y = k⁻¹`.

### `pow_mul_eq_zero_of_castHom_eq_zero`

If `x : ZMod (p ^ (n + 1))` reduces to `0` in `ZMod p`, then `p ^ n * x = 0`. Lift `x` to an
integer `y` with `ZMod.intCast_surjective`. The hypothesis becomes `(p : ℤ) ∣ y` by
`map_intCast` and `ZMod.intCast_zmod_eq_zero_iff_dvd`, so `y = p * c`. Then
`p ^ n * (p * c) = p ^ (n + 1) * c`, and `p ^ (n + 1) = 0` in `ZMod (p ^ (n + 1))` by
`ZMod.natCast_self`. This lemma turns "a sum is divisible by `p`" into
"`p ^ n` times the sum vanishes".

### `dvd_num_of_intCast_eq_mul`

Let `q` be rational and let `N = D * q` be an integer, with `D` coprime to `M`. If `M` divides
`N`, then `M` divides `q.num`. Multiply `N = D * q` by `q.den` and use `Rat.mul_den_eq_num` to
get `N * q.den = D * q.num` in `ℤ`. Then `M` divides `D * q.num`. Since `M` and `D` are coprime
(`Nat.isCoprime_iff_coprime`), `IsCoprime.dvd_of_dvd_mul_left` gives `M ∣ q.num`.

### `den_dvd_of_intCast_eq_mul`

If `N = D * q` is an integer, then `q.den` divides `D`. The same identity
`N * q.den = D * q.num` shows that `q.den` divides `D * q.num`. The numerator and denominator
of `q` are coprime (`Rat.reduced`, turned into `IsCoprime` with `Int.isCoprime_iff_gcd_eq_one`),
so `IsCoprime.dvd_of_dvd_mul_right` gives `q.den ∣ D`.

## `Wolstenholme/PowerSums.lean`

### `sum_Ioo_eq_sum_zmod`

If `f : ZMod p → M` has `f 0 = 0`, then `∑ k ∈ Ioo 0 p, f k = ∑ x : ZMod p, f x`. First
`Finset.sum_erase` drops the zero term from the right side. Then `Finset.sum_nbij'` matches
`Ioo 0 p` with `univ.erase 0` using the cast `k ↦ (k : ZMod p)` and its inverse `ZMod.val`. The
side goals use `ZMod.natCast_eq_zero_iff`, `ZMod.val_pos`, `ZMod.val_lt`,
`ZMod.val_cast_of_lt` and `ZMod.natCast_zmod_val`. Only `[NeZero p]` is needed, not primality.

### `sum_Ioo_pow_eq_zero`

For a prime `p` and `0 < m < p - 1`, `∑ k ∈ Ioo 0 p, k ^ m = 0` in `ZMod p`. The previous lemma
turns it into a sum over all of `ZMod p` (the term at `0` vanishes because `m ≠ 0`). That sum is
`0` by Mathlib's `FiniteField.sum_pow_lt_card_sub_one`, using `ZMod.card` for the size of the
field. Both bounds on `m` are needed: for `m = 0` and for `m = p - 1` the sum is
`p - 1 = -1`, not `0`.

### `sum_Ioo_inv_pow_eq_zero`

The same statement for `k⁻¹ ^ m`. After moving to a sum over `ZMod p`, reindex by `x ↦ x⁻¹`,
which is a bijection because it is its own inverse (`inv_involutive`, used with
`Fintype.sum_bijective`). This gives the power sum `∑ x ^ m` again.

### `sum_Ioo_inv_mul_inv_sub_eq_zero`

For `p ≥ 5`, `∑ k ∈ Ioo 0 p, k⁻¹ * (p - k)⁻¹ = 0` in `ZMod p`. Each term equals `-(k⁻¹ ^ 2)`,
because `p - k = -k` in `ZMod p` (`Nat.cast_sub`, `ZMod.natCast_self`) and `(-k)⁻¹ = -k⁻¹`
(`inv_neg`). So the sum is `-∑ k⁻¹ ^ 2`, which vanishes by the previous lemma with `m = 2`. This
is where `p ≥ 5` comes from: we need `2 < p - 1`. This sum is the heart of the whole proof.

## `Wolstenholme/Harmonic.lean`

### `two_mul_sum_Ioo_inv`

In `ZMod (p ^ n)`, `2 * ∑ k⁻¹ = p * ∑ k⁻¹ * (p - k)⁻¹`. Write `2 * S` as `S + S` and reindex the
second copy with `sum_Ioo_reflect`, so it becomes `∑ (p - k)⁻¹`. Combine the two sums with
`Finset.sum_add_distrib`, pull `p` inside with `Finset.mul_sum`, and finish term by term with
`inv_add_inv_sub`.

### `pow_mul_sum_Ioo_inv_mul_inv_sub_eq_zero`

For `p ≥ 5`, `p ^ n * W = 0` in `ZMod (p ^ (n + 1))`, where `W = ∑ k⁻¹ * (p - k)⁻¹`. By
`pow_mul_eq_zero_of_castHom_eq_zero` it is enough that `W` reduces to `0` in `ZMod p`. The
reduction is a ring hom, so it commutes with the sum and products (`map_sum`, `map_mul`). By
`castHom_inv_natCast` it sends each inverse to the inverse in `ZMod p`. The result is the sum
from `sum_Ioo_inv_mul_inv_sub_eq_zero`.

### `sum_Ioo_inv_eq_zero`

Wolstenholme's harmonic congruence: for `p ≥ 5`, `∑ k ∈ Ioo 0 p, k⁻¹ = 0` in `ZMod (p ^ 2)`.
Take `two_mul_sum_Ioo_inv` with `n = 2`. Its right side is `p * W`, which is `0` by the previous
lemma with `n = 1`. So `S + S = 0`. Since `p ^ 2` is odd, `ZMod.add_self_eq_zero_iff_eq_zero`
gives `S = 0`.

### `harmonic_sub_one_eq_sum_Ioo`

`harmonic (p - 1) = ∑ k ∈ Ioo 0 p, (k : ℚ)⁻¹`. Mathlib defines `harmonic n` as a sum over
`range n` of `(i + 1)⁻¹`. Unfold it, write `range` as `Ico 0 (p - 1)` (`Finset.range_eq_Ico`)
and shift the index by one with `Finset.sum_Ico_add'`. What remains is
`Ico 1 (p - 1 + 1) = Ioo 0 p`, which `omega` checks pointwise, including the case `p = 0`.

### `natCast_sum_factorial_div_pow`

Clearing denominators over `ℚ`:
`∑ ((p - 1)! / k) ^ m = (p - 1)! ^ m * ∑ 1 / k ^ m`, where the left side is a natural number.
Each `k` divides `(p - 1)!` (`Nat.dvd_factorial`), so `Nat.cast_div` turns the natural division
into a rational one. Then `div_pow` and `div_eq_mul_inv` finish each term.

### `natCast_sum_factorial_div_pow_zmod`

The same natural number, now in `ZMod M` with `M` coprime to `(p - 1)!`:
`∑ ((p - 1)! / k) ^ m = (p - 1)! ^ m * ∑ k⁻¹ ^ m`. From `((p - 1)! / k) * k = (p - 1)!`
(`Nat.div_mul_cancel`) and `k * k⁻¹ = 1`, a `linear_combination` gives
`(p - 1)! / k = (p - 1)! * k⁻¹` in `ZMod M`. The coprimality of `k` and `M` comes from
`Nat.Coprime.coprime_dvd_left`, since `k` divides `(p - 1)!`.

### `dvd_sum_inv_pow_num`

The transfer to rational numbers. If `M` is coprime to `(p - 1)!` and `∑ k⁻¹ ^ m = 0` in
`ZMod M`, then `M` divides the numerator of `∑ 1 / k ^ m`. Apply `dvd_num_of_intCast_eq_mul`
with `N = ∑ ((p - 1)! / k) ^ m` and `D = (p - 1)! ^ m`. The two lemmas above give `N = D * q`
over `ℚ` and `N = 0` in `ZMod M`, which is `M ∣ N` by `ZMod.natCast_eq_zero_iff`.

### `harmonic_den_dvd_factorial`

The denominator of `harmonic n` divides `n !`. Take `natCast_sum_factorial_div_pow` with `p` set
to `n + 1` and `m = 1`, and identify the sum with `harmonic n` by
`harmonic_sub_one_eq_sum_Ioo (n + 1)`. This shows that `n ! * harmonic n` is a natural number.
Then `den_dvd_of_intCast_eq_mul` gives the result.

## `Wolstenholme/Binomial.lean`

### `exists_prod_one_add_mul`

In a commutative semiring, `∏ (1 + c * f i) = 1 + c * b` for some `b`. The property
"has the form `1 + c * b`" holds for `1` and for every factor. It is closed under
multiplication, because `(1 + c b)(1 + c b') = 1 + c (b + b' + c b b')`.
`Finset.prod_induction` combines these facts, and `ring` checks the identity.

### `prod_one_add_mul_of_sq_eq_zero`

If `c ^ 2 = 0`, then `∏ (1 + c * f i) = 1 + c * ∑ f i`. The proof is induction on the finset
with `Finset.cons_induction`. In the step, expanding the product gives an extra term
`c ^ 2 * (f a * S)`, and it vanishes because `c ^ 2 = 0`. The `calc` block does the expansion
with `ring` and then rewrites with the hypothesis.

### `eq_zero_of_one_add_sq_eq_one`

In a commutative ring where `2` is a unit, if `y ^ 3 = 0` and `(1 + y) ^ 2 = 1`, then `y = 0`.
The hypothesis says `2 y + y ^ 2 = 0`. Multiplying by `y` and using `y ^ 3 = 0` gives
`2 y ^ 2 = 0`, so `y ^ 2 = 0` because `2` is a unit (`IsUnit.mul_right_eq_zero`). Then
`2 y = 0`, so `y = 0`. Both steps are `linear_combination`.

### `choose_mul_factorial_eq_prod`

`C(2p - 1, p - 1) * (p - 1)! = ∏ k ∈ Ioo 0 p, (p + k)` in `ℕ`. The case `p = 0` is `simp`.
Otherwise rewrite `2p - 1` as `p + (p - 1)` and use `Nat.ascFactorial_eq_factorial_mul_choose`.
It says that `(p + 1)(p + 2) ... (p + (p - 1))` equals `(p - 1)! * C(2p - 1, p - 1)`. Then
`Nat.ascFactorial_eq_prod_range` writes the rising factorial as a product over `range (p - 1)`,
and `Finset.prod_nbij'` with `i ↦ i + 1` matches it with the product over `Ioo 0 p`.

### `natCast_choose_eq_prod_one_add`

In `ZMod (p ^ n)`, `C(2p - 1, p - 1) = ∏ k ∈ Ioo 0 p, (1 + p * k⁻¹)`. Cast the previous lemma
into `ZMod (p ^ n)`. Each factor `p + k` equals `k * (1 + p * k⁻¹)` because `k * k⁻¹ = 1`. So
the product is `(∏ k) * ∏ (1 + p * k⁻¹)`, and `∏ k = (p - 1)!` (`Finset.prod_Ico_id_eq_factorial`).
Finally `(p - 1)!` is a unit in `ZMod (p ^ n)` (`ZMod.unitOfCoprime`), so we can cancel it with
`IsUnit.mul_left_cancel`.

### `natCast_choose_eq_one_zmod_sq`

Babbage's theorem: for an odd prime `p`, `C(2p - 1, p - 1) = 1` in `ZMod (p ^ 2)`. Here
`p ^ 2 = 0`, so `prod_one_add_mul_of_sq_eq_zero` turns the product into `1 + p * S` with
`S = ∑ k⁻¹`. Multiplying `two_mul_sum_Ioo_inv` by `p` gives `2 p S = p ^ 2 W = 0`. Since `p ^ 2`
is odd, `ZMod.add_self_eq_zero_iff_eq_zero` gives `p S = 0`. This needs no power sum facts,
which is why it holds already for `p = 3`.

### `natCast_choose_eq_one_zmod_cube`

Wolstenholme's theorem in `ZMod (p ^ 3)` for `p ≥ 5`. Let `P = ∏ (1 + p k⁻¹)`.

1. Reindexing with `prod_Ioo_reflect` shows `P = ∏ (1 + p (p - k)⁻¹)`.
2. So `P ^ 2 = ∏ (1 + p k⁻¹)(1 + p (p - k)⁻¹)` by `Finset.prod_mul_distrib`. By
   `inv_add_inv_sub`, each factor is `1 + p ^ 2 * (2 k⁻¹ (p - k)⁻¹)`.
3. Since `(p ^ 2) ^ 2 = p ^ 4 = 0` (`pow_eq_zero_of_le`), `prod_one_add_mul_of_sq_eq_zero` gives
   `P ^ 2 = 1 + 2 p ^ 2 W`. Here `p ^ 2 W = 0` by
   `pow_mul_sum_Ioo_inv_mul_inv_sub_eq_zero` with `n = 2`, so `P ^ 2 = 1`.
4. By `exists_prod_one_add_mul`, `P = 1 + p b`. With `y = p b`, `y ^ 3 = p ^ 3 b ^ 3 = 0`. Also `2` is a
   unit, by `ZMod.isUnit_iff_coprime` and `Nat.coprime_two_left`, since `p ^ 3` is odd. So
   `eq_zero_of_one_add_sq_eq_one` gives `y = 0` and `P = 1`.

## `Wolstenholme/Main.lean`

### `wolstenholmes_theorem`

For a prime `p ≥ 5`, `C(2p - 1, p - 1) ≡ 1 [MOD p ^ 3]`. `ZMod.natCast_eq_natCast_iff` turns a
`Nat.ModEq` into an equation in `ZMod (p ^ 3)`, and that equation is
`natCast_choose_eq_one_zmod_cube`.

### `choose_two_mul_modEq_two`

For a prime `p ≥ 5`, `C(2p, p) ≡ 2 [MOD p ^ 3]`. First, `C(2p, p) = 2 * C(2p - 1, p - 1)`. The
identity `Nat.add_one_mul_choose_eq` gives `2p * C(2p - 1, p - 1) = C(2p, p) * p`, and we cancel
`p > 0` with `Nat.eq_of_mul_eq_mul_right`. Then multiply Wolstenholme's congruence by `2` with
`Nat.ModEq.mul_left`.

### `babbages_theorem`

For an odd prime `p`, `C(2p - 1, p - 1) ≡ 1 [MOD p ^ 2]`. Same translation as above, using
`natCast_choose_eq_one_zmod_sq`.

### `sq_dvd_harmonic_num`

For a prime `p ≥ 5`, `(p : ℤ) ^ 2` divides `(harmonic (p - 1)).num`. Apply
`dvd_sum_inv_pow_num` with `M = p ^ 2` and `m = 1`. The coprimality of `p ^ 2` and `(p - 1)!`
is `coprime_factorial_sub_one` with `Nat.Coprime.pow_left`. The congruence in `ZMod (p ^ 2)` is
`sum_Ioo_inv_eq_zero`. Finally `harmonic_sub_one_eq_sum_Ioo` rewrites the harmonic number as
the sum.

### `two_le_padicValRat_harmonic`

For a prime `p ≥ 5`, the `p`-adic valuation of `harmonic (p - 1)` is at least `2`. Mathlib
defines `padicValRat p q` as `padicValInt p q.num - padicValNat p q.den` (`padicValRat_def`).
The denominator divides `(p - 1)!` by `harmonic_den_dvd_factorial`, so `p` does not divide it,
and its valuation is `0` (`padicValNat.eq_zero_of_not_dvd`). The numerator is nonzero because
the harmonic number is positive (`harmonic_pos`, `Rat.num_ne_zero`). `padicValInt_dvd_iff` then
turns `p ^ 2 ∣ num` into `2 ≤ padicValInt p num`.

### `dvd_sum_inv_sq_num`

For a prime `p ≥ 5`, `p` divides the numerator of `∑ 1 / k ^ 2`. This is `dvd_sum_inv_pow_num`
with `M = p` and `m = 2`, together with `sum_Ioo_inv_pow_eq_zero`.

### `not_choose_modEq_one_three`

`C(5, 2) = 10` is not `1` modulo `27`, so Wolstenholme's congruence fails at `p = 3`.
`Nat.ModEq` has a `Decidable` instance and `Nat.choose` is computable, so for these small numbers
`decide` proves it by evaluation in the kernel.

### `not_sq_dvd_harmonic_num_three`

`harmonic 2 = 3 / 2`, and `9` does not divide `3`, so the harmonic statement fails at `p = 3`.
`harmonic_succ` and `norm_num` compute `harmonic 2`. `decide` cannot compute with rationals, so
`Rat.num_div_eq_of_coprime` gives `(3 / 2 : ℚ).num = 3`, and `decide` handles the final
integer fact.

### `not_choose_modEq_one_two`

`C(3, 1) = 3` is not `1` modulo `4`, so Babbage's congruence fails at `p = 2`. Proved by
`decide`.

## `Zolotarev/SignHom.lean`

### `mulSign`

The definition. For a prime `p`, the units of `ZMod p` act on `ZMod p` by multiplication.
`MulAction.toPermHom` turns this action into a group hom `(ZMod p)ˣ →* Perm (ZMod p)`, and
composing with `Equiv.Perm.sign` gives `mulSign p : (ZMod p)ˣ →* ℤˣ`. Because it is a
composition of homs, multiplicativity is free. The definition is marked `@[expose]` so that
other modules can unfold it.

### `mulSign_apply`

`mulSign p u` is the sign of `Equiv.mulLeft₀ u`, the permutation `x ↦ u * x`. Unfold the
composition with `MonoidHom.comp_apply`. The two permutations agree pointwise. `Units.smul_def`
says that a unit acts through its value, and `simp` turns that action into multiplication with
`smul_eq_mul`.

### `mulSign_of_isSquare`

If `u` is a square in `ZMod p`, then `mulSign p u = 1`. Write `u = r * r`. Then `r ≠ 0`, so `u`
is the unit `Units.mk0 r _` squared, by `Units.ext`. The sign is multiplicative (`map_mul`), and
every unit `s` of `ℤ` satisfies `s * s = 1` (`Int.units_mul_self`).

### `ne_one_of_forall_mem_zpowers`

For an odd prime `p`, a generator of `(ZMod p)ˣ` is not `1`. If it were, every unit would be
`1`, because `Subgroup.zpowers 1 = ⊥` (`Subgroup.zpowers_one_eq_bot`, `Subgroup.mem_bot`). In
particular `-1 = 1`, which is false in `ZMod p` when `p > 2` (`ZMod.neg_one_ne_one`).

### `isCycle_toPerm_of_forall_mem_zpowers`

For an odd prime `p`, the permutation `x ↦ g * x` for a generator `g` is a cycle. Mathlib's
`IsCycle` asks for one moved point (we take `1`, which goes to `g ≠ 1`) such that every moved
point lies in its cycle. A moved point `y` is nonzero, so `y = g ^ k` for some integer `k`
(`Subgroup.mem_zpowers_iff`). The `k`-th power of the permutation is the permutation of `g ^ k`
(`map_zpow` for the hom `MulAction.toPermHom`), and it sends `1` to `y`.

### `support_toPerm_of_ne_one`

For a unit `g ≠ 1`, the permutation `x ↦ g * x` moves exactly the nonzero residues. If `x = 0`,
then `g * 0 = 0`. If `x ≠ 0`, then `g * x = x` would force `g = 1` by `mul_eq_right₀`. The proof
unfolds the support with `Equiv.Perm.mem_support` and `Finset.mem_erase`.

### `mulSign_of_forall_mem_zpowers`

For an odd prime `p`, a generator `g` has sign `-1`. Mathlib's `Equiv.Perm.IsCycle.sign` says
that a cycle has sign `-(-1) ^ (size of support)`. The support is `univ.erase 0`, with `p - 1`
elements (`Finset.card_erase_of_mem`, `Finset.card_univ`, `ZMod.card`). Since `p - 1` is even
(`Nat.Odd.sub_odd`), the sign is `-1` (`Even.neg_one_pow`).

### `mulSign_of_not_isSquare`

A unit that is not a square has sign `-1`. If `p = 2`, every element of `ZMod 2` equals its own
square (checked by `fin_cases`), so there is nothing to prove. Otherwise take a generator `g`
(`IsCyclic.exists_generator`) and write `u = g ^ k`. If `k` were even, `u` would be a square,
so `k` is odd (`Int.even_or_odd`). The sign is then `(-1) ^ k = -1` by `map_zpow`, the previous
lemma and `Odd.neg_one_zpow`.

## `Zolotarev/Main.lean`

### `sign_mulLeft₀_eq_quadraticChar`

For `a ≠ 0` in `ZMod p`, the sign of `x ↦ a * x` equals `quadraticChar (ZMod p) a`. First
`mulSign_apply` rewrites the sign as `mulSign p` of the unit `a`. Then split on whether `a` is a
square. If it is, both sides are `1` (`mulSign_of_isSquare`,
`quadraticChar_one_iff_isSquare`). If not, both sides are `-1` (`mulSign_of_not_isSquare`,
`quadraticChar_neg_one_iff_not_isSquare`). The casts from `ℤˣ` to `ℤ` are `Units.val_one` and
`Units.val_neg`.

### `zolotarevs_lemma`

Zolotarev's lemma: for an integer `a` with `p ∤ a`, the sign of `x ↦ a * x` on `ZMod p` is
`legendreSym p a`. Mathlib defines `legendreSym p a` as `quadraticChar (ZMod p) a`, so this is
the previous lemma applied to the residue of `a`.

### `sign_neg_eq_χ₄`

For an odd prime `p`, the sign of `x ↦ -x` on `ZMod p` is `χ₄ p`, which is `(-1) ^ ((p - 1) / 2)`.
Negation is multiplication by `-1` (checked pointwise by `simp`). Zolotarev's lemma turns the
sign into `legendreSym p (-1)`, and Mathlib's `legendreSym.at_neg_one` evaluates it.
