import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.LocalTwistContinuousInvolutionIntegralProperties
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.EllipticCharpolySelfReciprocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMonicUnitRootsBoundedDenominatorNumberFielStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonIntegerDenominatorOfValuationBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyCoeffDetInvValuationBoundedOfIsCompactGLStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemSectionConjStatement

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FinPolySupp

/- English proof (translation)
Introduce `E _ _ _ n w y hy`. Take `⟨M, rfl⟩` from `hy`. Establish `hint : ∀ z : Ov E w, Valued.v (z : w.adicCompletion E) ≤ 1` using `fun z => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 z.2`. Use `⟨fun k => ?_, ?_⟩` and prove the remaining obligations. Establish `: (bc (Ov E w).subtype M).val = (M.val).map (Ov E w).subtype` using `rfl`.

Rewrite using `[this, Matrix.charpoly_map, coeff_map]`. Conclude with `hint _`. Rewrite using `[← map_inv]`. Establish `: (bc (Ov E w).subtype M⁻¹).val = ((M⁻¹).val).map (Ov E w).subtype` using `rfl`. Rewrite using `[this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`.

Conclude with `hint _`.
-/
theorem int_pts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (y : GLw n w), y ∈ GlobalTheory.LFun.KGL w n → (∀ k, Valued.v (y.val.charpoly.coeff k) ≤ 1) ∧ Valued.v (y⁻¹ : GLw n w).val.det ≤ 1 := by
  intro E _ _ _ n w y hy
  obtain ⟨M, rfl⟩ := hy
  have hint : ∀ z : Ov E w, Valued.v (z : w.adicCompletion E) ≤ 1 := fun z =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 z.2
  refine ⟨fun k => ?_, ?_⟩
  · have : (bc (Ov E w).subtype M).val = (M.val).map (Ov E w).subtype := rfl
    rw [this, Matrix.charpoly_map, coeff_map]; exact hint _
  · rw [← map_inv]
    have : (bc (Ov E w).subtype M⁻¹).val = ((M⁻¹).val).map (Ov E w).subtype := rfl
    rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hint _
end GlobalTheory.FinPolySupp

namespace GlobalTheory.FinPolySupp

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
The claim follows from `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x`.
-/
theorem val_alg (w : Pl E) (x : E) : Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x

/- English proof (translation)
Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Use extensionality with `a`. Rewrite using `[← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), h]`.
-/
theorem pl_ext {u u' : Pl E} (h : ∀ x : E, u.valuation E x = u'.valuation E x) : u = u' := by
  apply HeightOneSpectrum.ext
  ext a
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), h]

/- English proof (translation)
Establish `hc : ∀ k, algebraMap E (w.adicCompletion E) (P.coeff k) = y.val.charpoly.coeff k`. Introduce `k`. Rewrite using `[hP, atPl, coeff_map]`. Use `⟨fun k => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← val_alg, hc]`.

Conclude with `h1 k`. Rewrite using `[← val_alg, map_inv₀, hc]`. Establish `hdet : y.val.det = (-1) ^ Fintype.card (Fin n) * y.val.charpoly.coeff 0` using `Matrix.det_eq_sign_charpoly_coeff _`. Establish `hmul : (y⁻¹ : GLw n w).val.det * y.val.det = 1`. Rewrite using `[← Matrix.det_mul, Units.inv_mul, Matrix.det_one]`.

Establish `hinv : (y⁻¹ : GLw n w).val.det = (y.val.det)⁻¹` using `eq_inv_of_mul_eq_one_left hmul`. Establish `hv : Valued.v y.val.det = Valued.v (y.val.charpoly.coeff 0)`. Rewrite using `[hdet, map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul]`. Rewrite `h2` using `[hinv, map_inv₀, hv]`. Rewrite using `[map_inv₀]`.

Conclude with `h2`.
-/
theorem transfer {n : ℕ} (w : Pl E) (y : GLw n w) (P : E[X]) (hP : y.val.charpoly = atPl w P)
    (γ : WithZero (Multiplicative ℤ))
    (h1 : ∀ k, Valued.v (y.val.charpoly.coeff k) ≤ γ) (h2 : Valued.v (y⁻¹ : GLw n w).val.det ≤ γ) :
    (∀ k, w.valuation E (P.coeff k) ≤ γ) ∧ w.valuation E (P.coeff 0)⁻¹ ≤ γ := by
  have hc : ∀ k, algebraMap E (w.adicCompletion E) (P.coeff k) = y.val.charpoly.coeff k := by
    intro k; rw [hP, atPl, coeff_map]
  refine ⟨fun k => ?_, ?_⟩
  · rw [← val_alg, hc]; exact h1 k
  · rw [← val_alg, map_inv₀, hc]
    have hdet : y.val.det = (-1) ^ Fintype.card (Fin n) * y.val.charpoly.coeff 0 :=
      Matrix.det_eq_sign_charpoly_coeff _
    have hmul : (y⁻¹ : GLw n w).val.det * y.val.det = 1 := by
      rw [← Matrix.det_mul, Units.inv_mul, Matrix.det_one]
    have hinv : (y⁻¹ : GLw n w).val.det = (y.val.det)⁻¹ := eq_inv_of_mul_eq_one_left hmul
    have hv : Valued.v y.val.det = Valued.v (y.val.charpoly.coeff 0) := by
      rw [hdet, map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul]
    rw [hinv, map_inv₀, hv] at h2
    rw [map_inv₀]; exact h2

/- English proof (translation)
Distinguish the cases in `hind : f = (KL n w : Set (UL n w)).indicator 1`. Use `⟨1, fun _ => rfl, ?_⟩` and prove the remaining obligations. Introduce and unpack `P ⟨y, hy, hP⟩`. Establish `hyK : y ∈ KL n w`. Assume the negation of the conclusion as `hn`.

Apply `hy` to reduce the goal to its premises. Rewrite using `[hind]`. Conclude with `Set.indicator_of_notMem hn _`. Establish `hy1 : y.1 ∈ GlobalTheory.LFun.KGL w n` using `(Subgroup.mem_subgroupOf).1 hyK`. Take `⟨h1, h2⟩` from `int_pts E n w y.1 hy1`.

Conclude with `transfer w y.1 P hP 1 h1 h2`. Take `⟨γ, hγ⟩` from `GlobalTheory.T.charpoly_coeff_det_inv_valuation_bounded_of_isCompact_GL E n w (Subtype.val '' tsupport f) (hf.image continuous_subtype_val)`. Use `⟨γ, fun h => absurd h hind, ?_⟩` and prove the remaining obligations. Introduce and unpack `P ⟨y, hy, hP⟩`. Take `⟨h1, h2⟩` from `hγ y.1 ⟨y, subset_tsupport f hy, rfl⟩`.

Conclude with `transfer w y.1 P hP γ h1 h2`.
-/
theorem bound_at (n : ℕ) (w : Pl E) (f : UL n w → ℂ) (hf : HasCompactSupport f) :
    ∃ γ : WithZero (Multiplicative ℤ), (f = (KL n w : Set (UL n w)).indicator 1 → γ = 1) ∧
      ∀ P : E[X], (∃ y : UL n w, f y ≠ 0 ∧ y.1.val.charpoly = atPl w P) →
        (∀ k, w.valuation E (P.coeff k) ≤ γ) ∧ w.valuation E (P.coeff 0)⁻¹ ≤ γ := by
  by_cases hind : f = (KL n w : Set (UL n w)).indicator 1
  · refine ⟨1, fun _ => rfl, ?_⟩
    rintro P ⟨y, hy, hP⟩
    have hyK : y ∈ KL n w := by
      by_contra hn
      apply hy
      rw [hind]
      exact Set.indicator_of_notMem hn _
    have hy1 : y.1 ∈ GlobalTheory.LFun.KGL w n := (Subgroup.mem_subgroupOf).1 hyK
    obtain ⟨h1, h2⟩ := int_pts E n w y.1 hy1
    exact transfer w y.1 P hP 1 h1 h2
  · obtain ⟨γ, hγ⟩ := GlobalTheory.T.charpoly_coeff_det_inv_valuation_bounded_of_isCompact_GL E n w (Subtype.val '' tsupport f) (hf.image continuous_subtype_val)
    refine ⟨γ, fun h => absurd h hind, ?_⟩
    rintro P ⟨y, hy, hP⟩
    obtain ⟨h1, h2⟩ := hγ y.1 ⟨y, subset_tsupport f hy, rfl⟩
    exact transfer w y.1 P hP γ h1 h2

/- English proof (translation)
Take `⟨h0, hcsr⟩` from `GlobalTheory.T.elliptic_charpoly_self_reciprocal E n P hP`. Establish `hdeg : (P.map (IsCMField.complexConj E).toRingEquiv.toRingHom).natDegree = n`. Rewrite using `[natDegree_map_eq_of_injective (RingHom.injective _)]`. Conclude with `hP.2.1`. Establish `key : ∀ j ≤ n, IsCMField.complexConj E (P.coeff 0) * P.coeff j = IsCMField.complexConj E (P.coeff (n - j))`.

Introduce `j hj`. Use `congrArg (fun Q => Q.coeff j) hcsr` as an intermediate fact. Simplify using `only [coeff_C_mul, coeff_reverse, hdeg, coeff_map] at this`. Rewrite `this` using `[revAt_le hj]`. Conclude with `this`.

Establish `hc0 : IsCMField.complexConj E (P.coeff 0) = (P.coeff 0)⁻¹`. Use `key 0 (Nat.zero_le _)` as an intermediate fact. Establish `hn : P.coeff n = 1` using `by rw [← hP.2.1]; exact hP.1`. Rewrite `this` using `[Nat.sub_zero, hn, map_one]`. Conclude with `eq_inv_of_mul_eq_one_left this`.

Use `split_ifs with hk`. Use `key (n - k) (Nat.sub_le n k)` as an intermediate fact. Rewrite `this` using `[Nat.sub_sub_self hk, hc0]`. Rewrite using `[← this]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[coeff_eq_zero_of_natDegree_lt (by rw [hP.2.1]; omega), map_zero]`.
-/
theorem conj_coeff (n : ℕ) (P : E[X]) (hP : P ∈ Ell E n) (k : ℕ) :
    IsCMField.complexConj E (P.coeff k) = if k ≤ n then P.coeff (n - k) * (P.coeff 0)⁻¹ else 0 := by
  obtain ⟨h0, hcsr⟩ := GlobalTheory.T.elliptic_charpoly_self_reciprocal E n P hP
  have hdeg : (P.map (IsCMField.complexConj E).toRingEquiv.toRingHom).natDegree = n := by
    rw [natDegree_map_eq_of_injective (RingHom.injective _)]; exact hP.2.1
  have key : ∀ j ≤ n, IsCMField.complexConj E (P.coeff 0) * P.coeff j =
      IsCMField.complexConj E (P.coeff (n - j)) := by
    intro j hj
    have := congrArg (fun Q => Q.coeff j) hcsr
    simp only [coeff_C_mul, coeff_reverse, hdeg, coeff_map] at this
    rw [revAt_le hj] at this
    exact this
  have hc0 : IsCMField.complexConj E (P.coeff 0) = (P.coeff 0)⁻¹ := by
    have := key 0 (Nat.zero_le _)
    have hn : P.coeff n = 1 := by rw [← hP.2.1]; exact hP.1
    rw [Nat.sub_zero, hn, map_one] at this
    exact eq_inv_of_mul_eq_one_left this
  split_ifs with hk
  · have := key (n - k) (Nat.sub_le n k)
    rw [Nat.sub_sub_self hk, hc0] at this
    rw [← this]; field_simp
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [hP.2.1]; omega), map_zero]

/- English proof (translation)
Introduce `E _ _ _ _ n S hS f hcpt hev`. Use `choose γ hγ1 hγ using fun w => bound_at n w (f w) (hcpt w)`. Establish `hpart` using `GlobalTheory.T.exists_mem_section_valuation_eq_conj E S hS`. Set `p : Pl E → Pl E` to `fun u => if h : u ∈ S then u else (hpart u h).choose`. Establish `hpS : ∀ u, u ∉ S → p u ∈ S ∧ ∀ x : E, u.valuation E x = (p u).valuation E (IsCMField.complexConj E x)`.

Introduce `u hu`. Simplify using `only [p, dif_neg hu]`. Conclude with `(hpart u hu).choose_spec`. Set `Γ : Pl E → WithZero (Multiplicative ℤ)` to `fun u => if u ∈ S then γ u else γ (p u) * γ (p u)`. Establish `hB : {w | ¬ f w = (KL n w : Set (UL n w)).indicator 1}.Finite` using `Filter.eventually_cofinite.1 hev`.

Establish `hΓ : ∀ᶠ u in cofinite, Γ u ≤ 1`. Rewrite using `[Filter.eventually_cofinite]`. Establish `hsub : {u | ¬ Γ u ≤ 1} ⊆ {w | ¬ f w = (KL n w : Set (UL n w)).indicator 1} ∪ {u | u ∉ S ∧ p u ∈ {w | ¬ f w = (KL n w : Set (UL n w)).indicator 1}}`. Introduce `u hu`. Distinguish the cases in `huS : u ∈ S`.

Use `left`. Introduce `hf`. Apply `hu` to reduce the goal to its premises. Simplify using `[Γ, huS, hγ1 u hf]`. Use `right`.

Use `⟨huS, fun hf => hu ?_⟩` and prove the remaining obligations. Simplify using `[Γ, huS, hγ1 _ hf]`. Use `(hB.union ?_).subset hsub` and prove the remaining obligations. Use `Set.Finite.of_finite_image (f := p) (hB.subset ?_) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨u, hu, rfl⟩`.

Conclude with `hu.2`. Introduce `u hu u' hu' he`. Apply `pl_ext` to reduce the goal to its premises. Introduce `x`. Rewrite using `[(hpS u hu.1).2, (hpS u' hu'.1).2, he]`.

Take `⟨d, hd0, hd⟩` from `GlobalTheory.T.exists_common_integer_denominator_of_valuation_bounds E Γ hΓ`. Use `(GlobalTheory.T.finite_monic_unitRoots_bounded_denominator_numberField E n d hd0).subset ?_` and prove the remaining obligations. Introduce and unpack `P ⟨hP, hPS⟩`. Use `⟨hP.1, hP.2.1, hP.2.2.2, fun k => hd _ fun u => ?_⟩` and prove the remaining obligations. Distinguish the cases in `huS : u ∈ S`.

Simplify using `only [Γ, if_pos huS]`. Conclude with `(hγ u P (hPS u huS)).1 k`. Simplify using `only [Γ, if_neg huS]`. Take `⟨hpu, hv⟩` from `hpS u huS`. Take `⟨hb1, hb2⟩` from `hγ (p u) P (hPS _ hpu)`.

Rewrite using `[hv, conj_coeff n P hP k]`. Use `split_ifs`. Rewrite using `[map_mul]`. Conclude with `mul_le_mul' (hb1 _) hb2`. Rewrite using `[map_zero]`.

Conclude with `zero_le'`.
-/
theorem finpoly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ f : ∀ w : Pl E, UL n w → ℂ, (∀ w, HasCompactSupport (f w)) → (∀ᶠ w in (cofinite : Filter (Pl E)), f w = (KL n w : Set (UL n w)).indicator 1) → {P : E[X] | P ∈ Ell E n ∧ ∀ w ∈ S, ∃ y : UL n w, f w y ≠ 0 ∧ y.1.val.charpoly = atPl w P}.Finite := by
  intro E _ _ _ _ n S hS f hcpt hev
  choose γ hγ1 hγ using fun w => bound_at n w (f w) (hcpt w)
  have hpart := GlobalTheory.T.exists_mem_section_valuation_eq_conj E S hS
  let p : Pl E → Pl E := fun u => if h : u ∈ S then u else (hpart u h).choose
  have hpS : ∀ u, u ∉ S → p u ∈ S ∧ ∀ x : E, u.valuation E x = (p u).valuation E (IsCMField.complexConj E x) := by
    intro u hu; simp only [p, dif_neg hu]; exact (hpart u hu).choose_spec
  let Γ : Pl E → WithZero (Multiplicative ℤ) := fun u => if u ∈ S then γ u else γ (p u) * γ (p u)
  have hB : {w | ¬ f w = (KL n w : Set (UL n w)).indicator 1}.Finite := Filter.eventually_cofinite.1 hev
  have hΓ : ∀ᶠ u in cofinite, Γ u ≤ 1 := by
    rw [Filter.eventually_cofinite]
    have hsub : {u | ¬ Γ u ≤ 1} ⊆ {w | ¬ f w = (KL n w : Set (UL n w)).indicator 1} ∪
        {u | u ∉ S ∧ p u ∈ {w | ¬ f w = (KL n w : Set (UL n w)).indicator 1}} := by
      intro u hu
      by_cases huS : u ∈ S
      · left; intro hf; apply hu; simp [Γ, huS, hγ1 u hf]
      · right; refine ⟨huS, fun hf => hu ?_⟩; simp [Γ, huS, hγ1 _ hf]
    refine (hB.union ?_).subset hsub
    refine Set.Finite.of_finite_image (f := p) (hB.subset ?_) ?_
    · rintro _ ⟨u, hu, rfl⟩; exact hu.2
    · intro u hu u' hu' he
      apply pl_ext; intro x
      rw [(hpS u hu.1).2, (hpS u' hu'.1).2, he]
  obtain ⟨d, hd0, hd⟩ := GlobalTheory.T.exists_common_integer_denominator_of_valuation_bounds E Γ hΓ
  refine (GlobalTheory.T.finite_monic_unitRoots_bounded_denominator_numberField E n d hd0).subset ?_
  rintro P ⟨hP, hPS⟩
  refine ⟨hP.1, hP.2.1, hP.2.2.2, fun k => hd _ fun u => ?_⟩
  by_cases huS : u ∈ S
  · simp only [Γ, if_pos huS]; exact (hγ u P (hPS u huS)).1 k
  · simp only [Γ, if_neg huS]
    obtain ⟨hpu, hv⟩ := hpS u huS
    obtain ⟨hb1, hb2⟩ := hγ (p u) P (hPS _ hpu)
    rw [hv, conj_coeff n P hP k]
    split_ifs
    · rw [map_mul]; exact mul_le_mul' (hb1 _) hb2
    · rw [map_zero]; exact zero_le'

end GlobalTheory.FinPolySupp
