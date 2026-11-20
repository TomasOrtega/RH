import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalEmbeddingRangeEqField
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniformizerGaloisAction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormSubLeOfNear
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

/- English proof (translation)
Express the relevant statement in the definitionally equal form `IsUnit (show BDeRhamPlus (GroundTheory.PAdicHodge.normInteger ℂ_[l]) l from u)`. Assume the negation of the conclusion as `hy`. Establish `h2` using `(IsLocalRing.mem_maximalIdeal _).2 hy`. Rewrite `h2` using `[GroundTheory.PAdicHodge.IsPerfectoidField.maximalIdeal_bDeRhamPlus, RingHom.mem_ker]`. Conclude with `h h2`.
-/
theorem isUnit_BdRp_of_thB {l : ℕ} [Fact l.Prime] {u : Formalism.Per6.BdRp l} (h : thB l u ≠ 0) :
    IsUnit u := by
  change IsUnit (show BDeRhamPlus (GroundTheory.PAdicHodge.normInteger ℂ_[l]) l from u)
  by_contra hy
  have h2 := (IsLocalRing.mem_maximalIdeal _).2 hy
  rw [GroundTheory.PAdicHodge.IsPerfectoidField.maximalIdeal_bDeRhamPlus, RingHom.mem_ker] at h2
  exact h h2

/- English proof (translation)
Use `set S : Formalism.Per6.BdRp l := ∑ i ∈ Finset.range q, a ^ i * b ^ (q - 1 - i) with hS`. Establish `hkey : (a - b) * (S - 1) = 0`. Establish `h1 : (a - b) * S = a ^ q - b ^ q` using `(Commute.all a b).mul_geom_sum₂ q`. Rewrite using `[mul_sub, h1, ha, hb, mul_one, sub_self]`. Establish `hθS : thB l S = (q : ℂ_[l]) * thB l a ^ (q - 1)`.

Rewrite using `[hS, map_sum, Finset.sum_congr rfl (g := fun _ => thB l a ^ (q - 1))]`. Simplify using the standard rewrite rules. Introduce `i hi`. Establish `hi' : i ≤ q - 1` using `Nat.le_sub_one_of_lt (Finset.mem_range.1 hi)`. Rewrite using `[map_mul, map_pow, map_pow, ← hab, ← pow_add, Nat.add_sub_cancel' hi']`.

Establish `hζ : thB l a ^ q = thB l a` using `by rw [← map_pow, ha]`. Establish `hne : thB l (S - 1) ≠ 0`. Rewrite using `[map_sub, map_one, hθS]`. Distinguish the cases in `h0 : thB l a = 0`. Rewrite using `[h0, zero_pow (by omega)]`.

Simplify using the standard rewrite rules. Establish `h1 : thB l a ^ (q - 1) = 1`. Establish `e : thB l a ^ (q - 1) * thB l a = 1 * thB l a`. Rewrite using `[← pow_succ, Nat.sub_add_cancel (by omega), hζ, one_mul]`. Conclude with `mul_right_cancel₀ h0 e`.

Rewrite using `[h1, mul_one, sub_ne_zero]`. Conclude with `(by omega : q ≠ 1)` after adjusting the coercions. Establish `hu` using `isUnit_BdRp_of_thB hne`. Conclude with `sub_eq_zero.1 ((hu.mul_left_eq_zero).1 hkey)`.
-/
theorem eq_of_pow_eq_self_of_thB_eq {l : ℕ} [Fact l.Prime] {q : ℕ} (hq : 2 ≤ q)
    {a b : Formalism.Per6.BdRp l} (ha : a ^ q = a) (hb : b ^ q = b) (hab : thB l a = thB l b) :
    a = b := by
  set S : Formalism.Per6.BdRp l := ∑ i ∈ Finset.range q, a ^ i * b ^ (q - 1 - i) with hS
  have hkey : (a - b) * (S - 1) = 0 := by
    have h1 : (a - b) * S = a ^ q - b ^ q := (Commute.all a b).mul_geom_sum₂ q
    rw [mul_sub, h1, ha, hb, mul_one, sub_self]
  have hθS : thB l S = (q : ℂ_[l]) * thB l a ^ (q - 1) := by
    rw [hS, map_sum, Finset.sum_congr rfl (g := fun _ => thB l a ^ (q - 1))]
    · simp
    · intro i hi
      have hi' : i ≤ q - 1 := Nat.le_sub_one_of_lt (Finset.mem_range.1 hi)
      rw [map_mul, map_pow, map_pow, ← hab, ← pow_add, Nat.add_sub_cancel' hi']
  have hζ : thB l a ^ q = thB l a := by rw [← map_pow, ha]
  have hne : thB l (S - 1) ≠ 0 := by
    rw [map_sub, map_one, hθS]
    by_cases h0 : thB l a = 0
    · rw [h0, zero_pow (by omega)]
      simp
    · have h1 : thB l a ^ (q - 1) = 1 := by
        have e : thB l a ^ (q - 1) * thB l a = 1 * thB l a := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega), hζ, one_mul]
        exact mul_right_cancel₀ h0 e
      rw [h1, mul_one, sub_ne_zero]
      exact_mod_cast (by omega : q ≠ 1)
  have hu := isUnit_BdRp_of_thB hne
  exact sub_eq_zero.1 ((hu.mul_left_eq_zero).1 hkey)

/- English proof (translation)
Introduce `l _ q hq _ x y hx hy hxy`. Use `eq_of_pow_eq_self_of_thB_eq hq ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[← tch_pow, hx]`. Rewrite using `[← map_pow, hy]`. Rewrite using `[thB_tch, thB_rB, hxy, omC_apply]`.
-/
theorem tch_eq_rB_of_sh_eq : ∀ {l : ℕ} [Fact l.Prime] (q : ℕ), 2 ≤ q → l ∣ q → ∀ (x : Tl l) (y : Om l),
    x ^ q = x → y ^ q = y → sh x = omC y → tch l x = rB l y := by
  intro l _ q hq _ x y hx hy hxy
  refine eq_of_pow_eq_self_of_thB_eq hq ?_ ?_ ?_
  · rw [← tch_pow, hx]
  · rw [← map_pow, hy]
  · rw [thB_tch, thB_rB, hxy, omC_apply]

end GlobalTheory.CompanionTheory.LTPer.Tilt
