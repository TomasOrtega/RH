import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

noncomputable section

namespace GlobalTheory.FrobRestrict

open scoped Pointwise

open NumberField IsDedekindDomain in
open scoped Pointwise in
/- English proof (translation)
Establish `hdec : φ ∈ ValuationSubring.decompositionSubgroup F A` using `hφ.1`. Proceed by induction on `n with`. Consider the case `zero => exact ⟨one_mem _, fun x _ => by simp⟩`. Consider the case `succ n ih`. Use `⟨Subgroup.pow_mem _ hdec _, fun x hx => ?_⟩` and prove the remaining obligations.

Establish `hxq : A.valuation (x ^ q) ≤ 1` using `by rw [map_pow]; exact pow_le_one' hx q`. Establish `e : (φ ^ (n + 1)) x - x ^ q ^ (n + 1) = ((φ ^ n) (x ^ q) - (x ^ q) ^ q ^ n) + (φ ^ n) (φ x - x ^ q)`. Rewrite using `[pow_succ, AlgEquiv.mul_apply, map_sub, pow_succ', pow_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Use `Valuation.map_add_lt _ (ih.2 _ hxq) ?_` and prove the remaining obligations. Rewrite using `[_root_.ReciprocityTheory.Gal.valuation_apply_lt_one_iff (Subgroup.pow_mem _ hdec n)]`. Conclude with `hφ.2 x hx`.
-/
theorem _root_.GlobalTheory.FrobRestrict.isFrob_pow {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {A : ValuationSubring Ω} {q : ℕ} {φ : _root_.Formalism.ConjugateSelfDual.G F Ω} (hφ : _root_.Formalism.ConjugateSelfDual.IsFrob A q φ) (n : ℕ) :
    _root_.Formalism.ConjugateSelfDual.IsFrob A (q ^ n) (φ ^ n) := by
  have hdec : φ ∈ ValuationSubring.decompositionSubgroup F A := hφ.1
  induction n with
  | zero => exact ⟨one_mem _, fun x _ => by simp⟩
  | succ n ih =>
    refine ⟨Subgroup.pow_mem _ hdec _, fun x hx => ?_⟩
    have hxq : A.valuation (x ^ q) ≤ 1 := by rw [map_pow]; exact pow_le_one' hx q
    have e : (φ ^ (n + 1)) x - x ^ q ^ (n + 1)
        = ((φ ^ n) (x ^ q) - (x ^ q) ^ q ^ n) + (φ ^ n) (φ x - x ^ q) := by
      rw [pow_succ, AlgEquiv.mul_apply, map_sub, pow_succ', pow_mul]
      ring
    rw [e]
    refine Valuation.map_add_lt _ (ih.2 _ hxq) ?_
    rw [_root_.ReciprocityTheory.Gal.valuation_apply_lt_one_iff (Subgroup.pow_mem _ hdec n)]
    exact hφ.2 x hx

open NumberField IsDedekindDomain in
open scoped Pointwise in
/- English proof (translation)
Simplify using `only [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff] at h ⊢`. Conclude with `h`.
-/
private lemma restrictScalars_mem_decompositionSubgroup {E Ω : Type} [Field E] [Field Ω]
    [Algebra E Ω] {K : IntermediateField E Ω} {A : ValuationSubring Ω} {ι : _root_.Formalism.ConjugateSelfDual.G K Ω}
    (h : ι ∈ ValuationSubring.decompositionSubgroup K A) :
    ι.restrictScalars E ∈ ValuationSubring.decompositionSubgroup E A := by
  simp only [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff] at h ⊢
  exact h

open NumberField IsDedekindDomain in
open scoped Pointwise in
/- English proof (translation)
Introduce `E Ω _ _ _ _ K _ _ v w h A hw`. Establish `hnorm : _root_.Formalism.ConjugateSelfDual.normV w = _root_.Formalism.ConjugateSelfDual.normV v ^ w.asIdeal.inertiaDeg (𝓞 E)` using `by haveI : w.asIdeal.LiesOver v.asIdeal := ⟨h.symm⟩ haveI := v.isMaximal haveI := w.isMaximal`. Rewrite using `[Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal w.asIdeal]`. Unfold `_root_.Formalism.ConjugateSelfDual.normV`. Use `letI := Ideal.Quotient.field v.asIdeal`.

Conclude with `Module.natCard_eq_pow_finrank (K := 𝓞 E ⧸ v.asIdeal) (V := 𝓞 K ⧸ w.asIdeal)`. Use `⟨fun x => ?_, hnorm, fun ι hι => ?_, fun σ φ hσ hφ => ?_⟩` and prove the remaining obligations. Establish `e : (algebraMap K Ω) ((algebraMap (𝓞 E) (𝓞 K) x : 𝓞 K) : K) = algebraMap E Ω (x : E)`. Rewrite using `[IsScalarTower.algebraMap_apply E K Ω]`. Both sides reduce to the same expression.

Rewrite using `[← e, hw, ← h, Ideal.mem_comap]`. Rewrite `hι`, the goal using `[_root_.ReciprocityTheory.Gal.mem_Ine]`. Conclude with `⟨restrictScalars_mem_decompositionSubgroup hι.1, hι.2⟩`. Establish `hσ' : _root_.Formalism.ConjugateSelfDual.IsFrob A (_root_.Formalism.ConjugateSelfDual.normV v ^ w.asIdeal.inertiaDeg (𝓞 E)) (σ.restrictScalars E)`. Rewrite using `[← hnorm]`.

Conclude with `⟨restrictScalars_mem_decompositionSubgroup hσ.1, hσ.2⟩`. Establish `hφf` using `_root_.GlobalTheory.FrobRestrict.isFrob_pow hφ (w.asIdeal.inertiaDeg (𝓞 E))`. Establish `h1` using `_root_.ReciprocityTheory.Gal.inv_mul_mem_Ine_of_isFrob hφf hσ'`. Establish `h2` using `_root_.ReciprocityTheory.Gal.conj_mem_Ine (g := φ ^ w.asIdeal.inertiaDeg (𝓞 E)) hφf.1 h1`. Rewrite `h2` using `[mul_inv_cancel_left]`. Then use the resulting hypothesis.
-/
theorem _root_.GlobalTheory.FrobRestrict.frob_restrict : ∀ (E Ω : Type) [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] (K : IntermediateField E Ω) [FiniteDimensional E K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 K)),
    w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → ∀ A : ValuationSubring Ω,
    _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w → _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v ∧ _root_.Formalism.ConjugateSelfDual.normV w = _root_.Formalism.ConjugateSelfDual.normV v ^ w.asIdeal.inertiaDeg (𝓞 E) ∧
    (∀ ι ∈ _root_.ReciprocityTheory.Gal.Ine (F := K) A, ι.restrictScalars E ∈ _root_.ReciprocityTheory.Gal.Ine (F := E) A) ∧
    ∀ (σ : _root_.Formalism.ConjugateSelfDual.G K Ω) (φ : _root_.Formalism.ConjugateSelfDual.G E Ω), _root_.Formalism.ConjugateSelfDual.IsFrob A (_root_.Formalism.ConjugateSelfDual.normV w) σ → _root_.Formalism.ConjugateSelfDual.IsFrob A (_root_.Formalism.ConjugateSelfDual.normV v) φ →
    σ.restrictScalars E * (φ ^ w.asIdeal.inertiaDeg (𝓞 E))⁻¹ ∈ _root_.ReciprocityTheory.Gal.Ine (F := E) A := by
  intro E Ω _ _ _ _ K _ _ v w h A hw
  have hnorm : _root_.Formalism.ConjugateSelfDual.normV w = _root_.Formalism.ConjugateSelfDual.normV v ^ w.asIdeal.inertiaDeg (𝓞 E) := by
    haveI : w.asIdeal.LiesOver v.asIdeal := ⟨h.symm⟩
    haveI := v.isMaximal
    haveI := w.isMaximal
    rw [Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal w.asIdeal]
    unfold _root_.Formalism.ConjugateSelfDual.normV
    letI := Ideal.Quotient.field v.asIdeal
    exact Module.natCard_eq_pow_finrank (K := 𝓞 E ⧸ v.asIdeal) (V := 𝓞 K ⧸ w.asIdeal)
  refine ⟨fun x => ?_, hnorm, fun ι hι => ?_, fun σ φ hσ hφ => ?_⟩
  · have e : (algebraMap K Ω) ((algebraMap (𝓞 E) (𝓞 K) x : 𝓞 K) : K)
        = algebraMap E Ω (x : E) := by
      rw [IsScalarTower.algebraMap_apply E K Ω]
      rfl
    rw [← e, hw, ← h, Ideal.mem_comap]
  · rw [_root_.ReciprocityTheory.Gal.mem_Ine] at hι ⊢
    exact ⟨restrictScalars_mem_decompositionSubgroup hι.1, hι.2⟩
  · have hσ' : _root_.Formalism.ConjugateSelfDual.IsFrob A (_root_.Formalism.ConjugateSelfDual.normV v ^ w.asIdeal.inertiaDeg (𝓞 E)) (σ.restrictScalars E) := by
      rw [← hnorm]
      exact ⟨restrictScalars_mem_decompositionSubgroup hσ.1, hσ.2⟩
    have hφf := _root_.GlobalTheory.FrobRestrict.isFrob_pow hφ (w.asIdeal.inertiaDeg (𝓞 E))
    have h1 := _root_.ReciprocityTheory.Gal.inv_mul_mem_Ine_of_isFrob hφf hσ'
    have h2 := _root_.ReciprocityTheory.Gal.conj_mem_Ine (g := φ ^ w.asIdeal.inertiaDeg (𝓞 E)) hφf.1 h1
    rwa [mul_inv_cancel_left] at h2

end GlobalTheory.FrobRestrict
