import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJacobianSectionIsUnitGermOfLocalIso

set_option autoImplicit false

noncomputable section

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.CotIndep

open IsLocalRing TensorProduct

/- English proof (translation)
Establish `hker : RingHom.ker (algebraMap P (ResidueField P)) = maximalIdeal P` using `ker_residue`. Establish `hx' : x ∈ RingHom.ker (algebraMap P (ResidueField P))`. Rewrite using `[hker]`. Conclude with `Ideal.pow_le_self two_ne_zero hx`. Establish `h0 : (RingHom.ker (algebraMap P (ResidueField P))).toCotangent ⟨x, hx'⟩ = 0`.

Rewrite using `[Ideal.toCotangent_eq_zero]`. Express the relevant statement in the definitionally equal form `x ∈ _ ^ 2`. Rewrite using `[hker]`. Conclude with `hx`. Use `congrArg (KaehlerDifferential.kerCotangentToTensor k P (ResidueField P)) h0` as an intermediate fact.

Rewrite `this` using `[KaehlerDifferential.kerCotangentToTensor_toCotangent, map_zero]`. Then use the resulting hypothesis.
-/
theorem tmul_D_eq_zero_of_mem_sq (k P : Type*) [CommRing k] [CommRing P] [IsLocalRing P]
    [Algebra k P] {x : P} (hx : x ∈ maximalIdeal P ^ 2) :
    (1 : ResidueField P) ⊗ₜ[P] KaehlerDifferential.D k P x = 0 := by
  have hker : RingHom.ker (algebraMap P (ResidueField P)) = maximalIdeal P := ker_residue
  have hx' : x ∈ RingHom.ker (algebraMap P (ResidueField P)) := by
    rw [hker]; exact Ideal.pow_le_self two_ne_zero hx
  have h0 : (RingHom.ker (algebraMap P (ResidueField P))).toCotangent ⟨x, hx'⟩ = 0 := by
    rw [Ideal.toCotangent_eq_zero]
    change x ∈ _ ^ 2
    rw [hker]; exact hx
  have := congrArg (KaehlerDifferential.kerCotangentToTensor k P (ResidueField P)) h0
  rwa [KaehlerDifferential.kerCotangentToTensor_toCotangent, map_zero] at this

/- English proof (translation)
Establish `h1 : IsFreeGen P (dForm (ρ.comp α) fun i => ρ (z i))`. Use `MorJac.isFreeGen_formMap (D := n) hρ rfl hω` as an intermediate fact. Rewrite `this` using `[formMap_dForm]`. Then use the resulting hypothesis. Use `letI := (ρ.comp α).toAlgebra`. Use `set κ := ResidueField P`.

Set `φ : Omega (ρ.comp α) →ₗ[P] κ ⊗[P] Omega (ρ.comp α)` to `TensorProduct.mk P κ _ 1`. Establish `h2` using `h1.of_isBaseChange (isBaseChange_exteriorPower (TensorProduct.isBaseChange P (Omega (ρ.comp α)) κ) n)`. Rewrite `h2` using `[dForm_eq, exteriorPowerMapOver_ιMulti]`. Establish `h3 : exteriorPower.ιMulti κ n (fun i => φ (dFun (ρ.comp α) (ρ (z i)))) ≠ 0`. Introduce `h0`.

Rewrite `h2` using `[h0]`. Conclude with `one_ne_zero (h2.1 (a₁ := (1 : κ)) (a₂ := 0) (by simp))`. Establish `h4 : LinearIndependent κ (fun i => φ (dFun (ρ.comp α) (ρ (z i))))`. Assume the negation of the conclusion as `h`. Conclude with `h3 (AlternatingMap.map_linearDependent _ _ h)`.

Establish `h5` using `h4.comp (Subtype.val : J → Fin n) Subtype.val_injective`. Rewrite `h5`, the goal using `[Fintype.linearIndependent_iff]`. Introduce `g hg i`. Use `choose b hb using fun j => residue_surjective (R := P) (g j)`. Establish `hsq : ∑ j : J, b j * ρ (z j) ∈ maximalIdeal P ^ 2`.

Establish `e : ∑ j : J, g j • ((maximalIdeal P).toCotangent ⟨ρ (z j), hz j⟩ : CotangentSpace P) = (maximalIdeal P).toCotangent (∑ j : J, b j • (⟨ρ (z j), hz j⟩ : maximalIdeal P))`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, ← hb j, ← ResidueField.algebraMap_eq, algebraMap_smul]`. Rewrite `hg` using `[e, Ideal.toCotangent_eq_zero]`.

Simplify `hg` using `[Submodule.coe_sum]`. Establish `h0` using `tmul_D_eq_zero_of_mem_sq k P hsq`. Establish `htk : ∀ j : J, algebraMap P κ (ρ (z j)) = 0` using `fun j => by`. Rewrite using `[ResidueField.algebraMap_eq]`. Conclude with `(residue_eq_zero_iff _).2 (hz j)`.

Use `h5 g ?_ i` and prove the remaining obligations. Rewrite using `[← h0, map_sum, tmul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Derivation.leibniz, tmul_add, ← smul_tmul, ← smul_tmul, Algebra.smul_def, mul_one, Algebra.smul_def, mul_one, htk, zero_tmul, add_zero, ← hb j, ← ResidueField.algebraMap_eq]`. Express the relevant statement in the definitionally equal form `(algebraMap P κ (b j)) • ((1 : κ) ⊗ₜ[P] KaehlerDifferential.D k P (ρ (z j))) = _`.

Rewrite using `[smul_tmul', smul_eq_mul, mul_one]`.
-/
theorem linearIndependent_toCotangent {k A P : Type*} [CommRing k] [CommRing A] [CommRing P]
    [IsLocalRing P] (α : k →+* A) (ρ : A →+* P)
    (hρ : letI := ρ.toAlgebra; Algebra.FormallyEtale A P) {n : ℕ} (z : Fin n → A)
    (hω : IsFreeGen A (dForm α z)) (J : Finset (Fin n))
    (hz : ∀ j : J, ρ (z j) ∈ maximalIdeal P) :
    LinearIndependent (ResidueField P)
      (fun j : J => ((maximalIdeal P).toCotangent ⟨ρ (z j), hz j⟩ : CotangentSpace P)) := by
  classical
  have h1 : IsFreeGen P (dForm (ρ.comp α) fun i => ρ (z i)) := by
    have := MorJac.isFreeGen_formMap (D := n) hρ rfl hω
    rwa [formMap_dForm] at this
  letI := (ρ.comp α).toAlgebra
  set κ := ResidueField P
  let φ : Omega (ρ.comp α) →ₗ[P] κ ⊗[P] Omega (ρ.comp α) := TensorProduct.mk P κ _ 1
  have h2 := h1.of_isBaseChange
    (isBaseChange_exteriorPower (TensorProduct.isBaseChange P (Omega (ρ.comp α)) κ) n)
  rw [dForm_eq, exteriorPowerMapOver_ιMulti] at h2
  have h3 : exteriorPower.ιMulti κ n (fun i => φ (dFun (ρ.comp α) (ρ (z i)))) ≠ 0 := by
    intro h0
    rw [h0] at h2
    exact one_ne_zero (h2.1 (a₁ := (1 : κ)) (a₂ := 0) (by simp))
  have h4 : LinearIndependent κ (fun i => φ (dFun (ρ.comp α) (ρ (z i)))) := by
    by_contra h
    exact h3 (AlternatingMap.map_linearDependent _ _ h)
  have h5 := h4.comp (Subtype.val : J → Fin n) Subtype.val_injective
  rw [Fintype.linearIndependent_iff] at h5 ⊢
  intro g hg i
  choose b hb using fun j => residue_surjective (R := P) (g j)
  have hsq : ∑ j : J, b j * ρ (z j) ∈ maximalIdeal P ^ 2 := by
    have e : ∑ j : J, g j • ((maximalIdeal P).toCotangent ⟨ρ (z j), hz j⟩ : CotangentSpace P) =
        (maximalIdeal P).toCotangent (∑ j : J, b j • (⟨ρ (z j), hz j⟩ : maximalIdeal P)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, ← hb j, ← ResidueField.algebraMap_eq, algebraMap_smul]
    rw [e, Ideal.toCotangent_eq_zero] at hg
    simpa [Submodule.coe_sum] using hg
  have h0 := tmul_D_eq_zero_of_mem_sq k P hsq
  have htk : ∀ j : J, algebraMap P κ (ρ (z j)) = 0 := fun j => by
    rw [ResidueField.algebraMap_eq]; exact (residue_eq_zero_iff _).2 (hz j)
  refine h5 g ?_ i
  rw [← h0, map_sum, tmul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Derivation.leibniz, tmul_add, ← smul_tmul, ← smul_tmul, Algebra.smul_def, mul_one,
    Algebra.smul_def, mul_one, htk, zero_tmul, add_zero, ← hb j, ← ResidueField.algebraMap_eq]
  change (algebraMap P κ (b j)) • ((1 : κ) ⊗ₜ[P] KaehlerDifferential.D k P (ρ (z j))) = _
  rw [smul_tmul', smul_eq_mul, mul_one]

end GlobalTheory.CotIndep

namespace GlobalTheory.CotIndep

/- English proof (translation)
Introduce `Y _ _ q n _ U z hf y hy J hz`. Conclude with `linearIndependent_toCotangent (algX q U) (Y.presheaf.germ U y hy).hom (MorJac.formallyEtale_germ hf.affine y hy) z hf.gen J hz`.
-/
theorem linearIndependent_cotangent_of_isFrame : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], ∀ (U : Y.Opens) (z : Fin n → Γ(Y, U)), IsFrame (dOn q z) → ∀ (y : Y) (hy : y ∈ U) (J : Finset (Fin n)) (hz : ∀ j : J, Y.presheaf.germ U y hy (z j) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)), LinearIndependent (IsLocalRing.ResidueField (Y.presheaf.stalk y)) (fun j : J => ((IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).toCotangent ⟨(fun j : J => Y.presheaf.germ U y hy (z j)) j, hz j⟩ : IsLocalRing.CotangentSpace (Y.presheaf.stalk y))) := by
  intro Y _ _ q n _ U z hf y hy J hz
  exact linearIndependent_toCotangent (algX q U) (Y.presheaf.germ U y hy).hom
    (MorJac.formallyEtale_germ hf.affine y hy) z hf.gen J hz

end GlobalTheory.CotIndep
