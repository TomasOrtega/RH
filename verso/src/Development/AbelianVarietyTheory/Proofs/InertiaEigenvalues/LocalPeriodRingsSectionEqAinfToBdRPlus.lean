import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIntegersTensorEqLetterwiseProductAinf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.SeedSec

/- English proof (translation)
Use `set S := ∑ i ∈ Finset.range n, u ^ i * v ^ (n - 1 - i) with hS`. Establish `h1 : S * (u - v) = u - v` using `by rw [hS, geom_sum₂_mul, hu, hv]`. Establish `hc : θ u ^ n = θ u` using `by rw [← map_pow, hu]`. Establish `e : θ S = n * θ u ^ (n - 1)`. Rewrite using `[hS, map_sum, Finset.sum_congr rfl (g := fun _ => θ u ^ (n - 1)) (fun i hi => by`.

Use `Finset.mem_range.1 hi` as an intermediate fact. Rewrite using `[map_mul, map_pow, map_pow, ← h, ← pow_add]`. Use `congr 1`. Use the proof step `omega)]`. Simplify using the standard rewrite rules.

Establish `h2 : θ (S - 1) ≠ 0`. Rewrite using `[map_sub, map_one, e]`. Distinguish the cases in `h0 : θ u = 0`. Rewrite using `[h0, zero_pow (by omega)]`. Simplify using the standard rewrite rules.

Establish `h3 : θ u ^ (n - 1) = 1`. Use `mul_right_cancel₀ h0 ?_` and prove the remaining obligations. Rewrite using `[← pow_succ, Nat.sub_add_cancel (by omega), one_mul, hc]`. Rewrite using `[h3, mul_one, sub_ne_zero]`. Conclude with `(show n ≠ 1 by omega)` after adjusting the coercions.

Establish `h4 : (S - 1) * (u - v) = 0` using `by rw [sub_mul, h1, one_mul, sub_self]`. Conclude with `sub_eq_zero.1 ((hθ _ h2).mul_right_eq_zero.1 h4)`.
-/
theorem eq_of_pow_eq_self {R K : Type} [CommRing R] [Field K] [CharZero K] (θ : R →+* K)
    (hθ : ∀ y, θ y ≠ 0 → IsUnit y) {n : ℕ} (hn : 2 ≤ n) {u v : R} (hu : u ^ n = u) (hv : v ^ n = v)
    (h : θ u = θ v) : u = v := by
  set S := ∑ i ∈ Finset.range n, u ^ i * v ^ (n - 1 - i) with hS
  have h1 : S * (u - v) = u - v := by rw [hS, geom_sum₂_mul, hu, hv]
  have hc : θ u ^ n = θ u := by rw [← map_pow, hu]
  have e : θ S = n * θ u ^ (n - 1) := by
    rw [hS, map_sum, Finset.sum_congr rfl (g := fun _ => θ u ^ (n - 1)) (fun i hi => by
      have := Finset.mem_range.1 hi
      rw [map_mul, map_pow, map_pow, ← h, ← pow_add]
      congr 1
      omega)]
    simp
  have h2 : θ (S - 1) ≠ 0 := by
    rw [map_sub, map_one, e]
    by_cases h0 : θ u = 0
    · rw [h0, zero_pow (by omega)]
      simp
    · have h3 : θ u ^ (n - 1) = 1 := by
        refine mul_right_cancel₀ h0 ?_
        rw [← pow_succ, Nat.sub_add_cancel (by omega), one_mul, hc]
      rw [h3, mul_one, sub_ne_zero]
      exact_mod_cast (show n ≠ 1 by omega)
  have h4 : (S - 1) * (u - v) = 0 := by rw [sub_mul, h1, one_mul, sub_self]
  exact sub_eq_zero.1 ((hθ _ h2).mul_right_eq_zero.1 h4)

/- English proof (translation)
Establish `hs : (Polynomial.X ^ n - Polynomial.X : Polynomial (Om l)).Splits` using `IsAlgClosed.splits _`. Establish `h0 : (Polynomial.X ^ n - Polynomial.X : Polynomial (Om l)) ≠ 0` using `fun h => by`. Use `congrArg (Polynomial.coeff · 1) h` as an intermediate fact. Simplify using `[Polynomial.coeff_X_pow, show (1 : ℕ) ≠ n by omega] at this`. Take `⟨x, hx⟩` from `hs.mem_range_of_isRoot h0 (i := algebraMap (Om l) ℂ_[l]) (x := c) (by simp [hc])`.

Conclude with `⟨x, hx⟩`.
-/
theorem exists_om_of_pow_eq_self (l : ℕ) [Fact l.Prime] {n : ℕ} (hn : 2 ≤ n) (c : ℂ_[l]) (hc : c ^ n = c) :
    ∃ x : Om l, algebraMap (Om l) ℂ_[l] x = c := by
  have hs : (Polynomial.X ^ n - Polynomial.X : Polynomial (Om l)).Splits := IsAlgClosed.splits _
  have h0 : (Polynomial.X ^ n - Polynomial.X : Polynomial (Om l)) ≠ 0 := fun h => by
    have := congrArg (Polynomial.coeff · 1) h
    simp [Polynomial.coeff_X_pow, show (1 : ℕ) ≠ n by omega] at this
  obtain ⟨x, hx⟩ := hs.mem_range_of_isRoot h0 (i := algebraMap (Om l) ℂ_[l]) (x := c) (by simp [hc])
  exact ⟨x, hx⟩

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Use `IsHausdorff.haus hR _ fun n => ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n z)`. Rewrite using `[SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']`. Use `⟨f c - g c, ?_⟩` and prove the remaining obligations.

Establish `hf` using `congrArg f hc`. Establish `hg` using `congrArg g hc`. Simplify using `only [map_mul, map_pow, map_natCast, map_sub] at hf hg`. Take the linear combination `hf - hg`.
-/
private theorem padicInt_hom_apply_eq {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R]
    (hR : IsHausdorff (Ideal.span {(l : R)}) R) (f g : ℤ_[l] →+* R) (z : ℤ_[l]) : f z = g z := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus hR _ fun n => ?_
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n z)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  refine ⟨f c - g c, ?_⟩
  have hf := congrArg f hc
  have hg := congrArg g hc
  simp only [map_mul, map_pow, map_natCast, map_sub] at hf hg
  linear_combination hf - hg

/- English proof (translation)
Establish `hspan : w ∈ Submodule.span ℤ_[l] (Set.range (WittVector.teichmuller l : Fq l a → Wq l a))`. Rewrite using `[span_teich]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hspan using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨z, rfl⟩` from `hy`. Establish `hq : 2 ≤ l ^ a` using `one_lt_pow_l l a`. Establish `hw : (WittVector.teichmuller l z) ^ (l ^ a) = WittVector.teichmuller l z`. Rewrite using `[← map_pow, Fq.pow_card]`. Use `set A := wA l a (WittVector.teichmuller l z) with hAdef`.

Establish `hA : A ^ (l ^ a) = A` using `by rw [hAdef, ← map_pow, hw]`. Establish `hc : ((Per.θ l A : OC l) : ℂ_[l]) ^ (l ^ a) = ((Per.θ l A : OC l) : ℂ_[l])`. Rewrite using `[← SubmonoidClass.coe_pow, ← map_pow, hA]`. Take `⟨x, hx⟩` from `exists_om_of_pow_eq_self l hq _ hc`. Establish `hxq : x ^ (l ^ a) = x` using `(algebraMap (Om l) ℂ_[l]).injective (by rw [map_pow, hx, hc])`.

Use `⟨x, hx.symm, eq_of_pow_eq_self (Per.θD l) (thetaD_props l).2.2.1 hq (by rw [← map_pow, hxq]) (by rw [← map_pow, hA]) ?_⟩` and prove the remaining obligations. Rewrite using `[C.o_sec.th, (thetaD_props l).2.2.2.1]`. Conclude with `hx`. Consider the case `zero => exact ⟨0, by simp, by simp⟩`. Consider the case `add y y' _ _ hy hy'`.

Take `⟨x, hx1, hx2⟩` from `hy`. Take `⟨x', hx1', hx2'⟩` from `hy'`. Use `⟨x + x', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_add, map_add, Subring.coe_add, hx1, hx1']`. Rewrite using `[map_add, map_add, map_add, hx2, hx2']`.

Consider the case `smul r y _ hy`. Take `⟨x, hx1, hx2⟩` from `hy`. Establish `e : wA l a (r • y) = algebraMap ℤ_[l] (Ainf l) r * wA l a y`. Rewrite using `[map_smul, Algebra.smul_def]`. Use `⟨algebraMap ℚ_[l] (Om l) (r : ℚ_[l]) * x, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[e, map_mul, Subring.coe_mul, hx1, map_mul]`. Use `congr 1`. Conclude with `GlobalTheory.UnramIdem.ringHom_eq ((Per.θ l).comp (algebraMap ℤ_[l] (Ainf l))) r`. Rewrite using `[e, map_mul, map_mul, hx2, C.o_sec.z r]`. Establish `hA : IsAdicComplete (Ideal.span {(l : Ainf l)}) (Ainf l)` using `inferInstance`.

Rewrite using `[padicInt_hom_apply_eq hA.toIsHausdorff (Per.zA l) (algebraMap ℤ_[l] (Ainf l)) r]`.
-/
theorem exists_sec (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (C : Core l) (w : Wq l a) :
    ∃ x : Om l, ((Per.θ l (wA l a w) : OC l) : ℂ_[l]) = algebraMap (Om l) ℂ_[l] x ∧
      C.o x = aDp l (wA l a w) := by
  have hspan : w ∈ Submodule.span ℤ_[l] (Set.range (WittVector.teichmuller l : Fq l a → Wq l a)) := by
    rw [span_teich]; trivial
  induction hspan using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, rfl⟩ := hy
    have hq : 2 ≤ l ^ a := one_lt_pow_l l a
    have hw : (WittVector.teichmuller l z) ^ (l ^ a) = WittVector.teichmuller l z := by
      rw [← map_pow, Fq.pow_card]
    set A := wA l a (WittVector.teichmuller l z) with hAdef
    have hA : A ^ (l ^ a) = A := by rw [hAdef, ← map_pow, hw]
    have hc : ((Per.θ l A : OC l) : ℂ_[l]) ^ (l ^ a) = ((Per.θ l A : OC l) : ℂ_[l]) := by
      rw [← SubmonoidClass.coe_pow, ← map_pow, hA]
    obtain ⟨x, hx⟩ := exists_om_of_pow_eq_self l hq _ hc
    have hxq : x ^ (l ^ a) = x := (algebraMap (Om l) ℂ_[l]).injective (by rw [map_pow, hx, hc])
    refine ⟨x, hx.symm, eq_of_pow_eq_self (Per.θD l) (thetaD_props l).2.2.1 hq
      (by rw [← map_pow, hxq]) (by rw [← map_pow, hA]) ?_⟩
    rw [C.o_sec.th, (thetaD_props l).2.2.2.1]
    exact hx
  | zero => exact ⟨0, by simp, by simp⟩
  | add y y' _ _ hy hy' =>
    obtain ⟨x, hx1, hx2⟩ := hy
    obtain ⟨x', hx1', hx2'⟩ := hy'
    refine ⟨x + x', ?_, ?_⟩
    · rw [map_add, map_add, map_add, Subring.coe_add, hx1, hx1']
    · rw [map_add, map_add, map_add, hx2, hx2']
  | smul r y _ hy =>
    obtain ⟨x, hx1, hx2⟩ := hy
    have e : wA l a (r • y) = algebraMap ℤ_[l] (Ainf l) r * wA l a y := by
      rw [map_smul, Algebra.smul_def]
    refine ⟨algebraMap ℚ_[l] (Om l) (r : ℚ_[l]) * x, ?_, ?_⟩
    · rw [e, map_mul, Subring.coe_mul, hx1, map_mul]
      congr 1
      exact GlobalTheory.UnramIdem.ringHom_eq ((Per.θ l).comp (algebraMap ℤ_[l] (Ainf l))) r
    · rw [e, map_mul, map_mul, hx2, C.o_sec.z r]
      have hA : IsAdicComplete (Ideal.span {(l : Ainf l)}) (Ainf l) := inferInstance
      rw [padicInt_hom_apply_eq hA.toIsHausdorff (Per.zA l) (algebraMap ℤ_[l] (Ainf l)) r]

/- English proof (translation)
Introduce `l _ a _ C w x hx`. Take `⟨y, hy1, hy2⟩` from `exists_sec l a C w`. Establish `hxy : x = y` using `(algebraMap (Om l) ℂ_[l]).injective (hx.symm.trans hy1)`. Rewrite using `[hxy, hy2]`.
-/
theorem o_eq_aDp_wA : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (C : Core l) (w : Wq l a) (x : Om l),
    ((Per.θ l (wA l a w) : OC l) : ℂ_[l]) = (x : ℂ_[l]) → C.o x = aDp l (wA l a w) := by
  intro l _ a _ C w x hx
  obtain ⟨y, hy1, hy2⟩ := exists_sec l a C w
  have hxy : x = y := (algebraMap (Om l) ℂ_[l]).injective (hx.symm.trans hy1)
  rw [hxy, hy2]

end GlobalTheory.SeedSec
