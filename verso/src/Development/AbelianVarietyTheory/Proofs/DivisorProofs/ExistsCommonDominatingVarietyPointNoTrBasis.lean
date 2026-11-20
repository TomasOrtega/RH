import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDomainTensorComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResidueToComplexOfRationalResidueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalModelAtComplexPointStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CommonPoint

/- English proof (translation)
The claim follows from `IsFractionRing.of_field R K fun f => by obtain ⟨a, ha, b, hb, hb0, e⟩ := h.frac f exact ⟨⟨a, ha⟩, ⟨b, hb⟩, (eq_div_iff hb0).2 e⟩`.
-/
theorem isFractionRing_of_isLocModel {K : Type} [Field K] [Algebra ℂ K] {R : Subring K}
    (h : IsLocModel (algebraMap ℂ K) R) : IsFractionRing R K :=
  IsFractionRing.of_field R K fun f => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := h.frac f
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, (eq_div_iff hb0).2 e⟩

/- English proof (translation)
Use `letI : Algebra ℂ R := ((algebraMap ℂ K).codRestrict R h.const_mem).toAlgebra`. Take `⟨ε, h1, h2⟩` from `GlobalTheory.T.exists_residue_to_complex_of_rationalResidue R h h'`. Conclude with `⟨⟨ε, h1⟩, h2⟩`.
-/
theorem exists_residue {K : Type} [Field K] [Algebra ℂ K] (R : Subring K)
    (h : IsLocModel (algebraMap ℂ K) R) (h' : RatRes (algebraMap ℂ K) R) :
    letI : Algebra ℂ R := ((algebraMap ℂ K).codRestrict R h.const_mem).toAlgebra
    ∃ ε : R →ₐ[ℂ] ℂ, ∀ r : R, ε r = 0 ↔ NonUnit R (r : K) := by
  letI : Algebra ℂ R := ((algebraMap ℂ K).codRestrict R h.const_mem).toAlgebra
  obtain ⟨ε, h1, h2⟩ := GlobalTheory.T.exists_residue_to_complex_of_rationalResidue R h h'
  exact ⟨⟨ε, h1⟩, h2⟩

/- English proof (translation)
Introduce `K L _ _ _ _ R S hR hR' hS hS'`. Use `letI : Algebra ℂ R := ((algebraMap ℂ K).codRestrict R hR.const_mem).toAlgebra`. Use `letI : Algebra ℂ S := ((algebraMap ℂ L).codRestrict S hS.const_mem).toAlgebra`. Use `haveI : IsScalarTower ℂ R K := IsScalarTower.of_algebraMap_eq' rfl`. Use `haveI : IsScalarTower ℂ S L := IsScalarTower.of_algebraMap_eq' rfl`.

Use `haveI : Algebra.EssFiniteType ℂ R := hR.essFiniteType`. Use `haveI : Algebra.EssFiniteType ℂ S := hS.essFiniteType`. Use `haveI := isFractionRing_of_isLocModel hR`. Use `haveI := isFractionRing_of_isLocModel hS`. Take `⟨εR, hεR⟩` from `exists_residue R hR hR'`.

Take `⟨εS, hεS⟩` from `exists_residue S hS hS'`. Set `iR : R →ₐ[ℂ] K` to `IsScalarTower.toAlgHom ℂ R K`. Set `iS : S →ₐ[ℂ] L` to `IsScalarTower.toAlgHom ℂ S L`. Establish `hinj : Function.Injective (Algebra.TensorProduct.map iR iS)`. Establish `e : (Algebra.TensorProduct.map iR iS).toLinearMap = (iR.toLinearMap.rTensor L).comp (iS.toLinearMap.lTensor R)`.

Use extensionality with `x y`. Simplify using the standard rewrite rules. Establish `h1 : Function.Injective (iS.toLinearMap.lTensor R)` using `Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective`. Establish `h2 : Function.Injective (iR.toLinearMap.rTensor L)` using `Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective`. Introduce `x y hxy`.

Establish `ex` using `LinearMap.congr_fun e x`. Establish `ey` using `LinearMap.congr_fun e y`. Conclude with `h1 (h2 (ex.symm.trans (hxy.trans ey)))`. Use `haveI : IsDomain (K ⊗[ℂ] L) := GlobalTheory.TensorFields.isDomain_tensor_complex K L`. Use `haveI : IsDomain (R ⊗[ℂ] S) := hinj.isDomain _`.

Use `haveI : Algebra.EssFiniteType S (S ⊗[ℂ] R) := Algebra.EssFiniteType.baseChange ℂ R S`. Use `haveI : Algebra.EssFiniteType ℂ (S ⊗[ℂ] R) := Algebra.EssFiniteType.comp ℂ S (S ⊗[ℂ] R)`. Use `haveI : Algebra.EssFiniteType ℂ (R ⊗[ℂ] S) := Algebra.EssFiniteType.of_surjective (Algebra.TensorProduct.comm ℂ S R).toAlgHom (Algebra.TensorProduct.comm ℂ S R).surjective`. Set `ε : R ⊗[ℂ] S →ₐ[ℂ] ℂ` to `Algebra.TensorProduct.lift εR εS fun _ _ => Commute.all _ _`. Take `⟨T, hT, hT', hTa⟩` from `GlobalTheory.T.exists_localModel_at_complexPoint (R ⊗[ℂ] S) ε`.

Set `M` to `FractionRing (R ⊗[ℂ] S)`. Set `j : R ⊗[ℂ] S →ₐ[ℂ] M` to `IsScalarTower.toAlgHom ℂ _ M`. Establish `hj : Function.Injective j` using `IsFractionRing.injective (R ⊗[ℂ] S) M`. Establish `hl : Function.Injective (j.comp Algebra.TensorProduct.includeLeft)`. Rewrite using `[AlgHom.coe_comp]`.

Conclude with `hj.comp (Algebra.TensorProduct.includeLeft_injective (S := ℂ) (algebraMap ℂ S).injective)`. Establish `hr : Function.Injective (j.comp Algebra.TensorProduct.includeRight)`. Rewrite using `[AlgHom.coe_comp]`. Conclude with `hj.comp (Algebra.TensorProduct.includeRight_injective (algebraMap ℂ R).injective)`. Take `⟨ρ, hρ⟩ : ∃ ρ : K →ₐ[ℂ] M, ∀ r : R, ρ (r : K) = j (r ⊗ₜ 1)` from `⟨IsFractionRing.liftAlgHom hl, fun r => (IsFractionRing.liftAlgHom_apply hl _).trans (IsFractionRing.lift_algebraMap hl r)⟩`.

Take `⟨σ, hσ⟩ : ∃ σ : L →ₐ[ℂ] M, ∀ s : S, σ (s : L) = j (1 ⊗ₜ s)` from `⟨IsFractionRing.liftAlgHom hr, fun s => (IsFractionRing.liftAlgHom_apply hr _).trans (IsFractionRing.lift_algebraMap hr s)⟩`. Use `⟨M, inferInstance, inferInstance, ρ, σ, T, hT, hT', fun f hf => ?_, fun f hf => ?_⟩` and prove the remaining obligations. Establish `e : ρ.toRingHom f = algebraMap _ M ((⟨f, hf⟩ : R) ⊗ₜ[ℂ] (1 : S))` using `hρ ⟨f, hf⟩`. Rewrite using `[e]`. Use `⟨(hTa _).1, fun hn => (hTa _).2 ?_⟩` and prove the remaining obligations.

Establish `h0 : εR ⟨f, hf⟩ = 0` using `(hεR ⟨f, hf⟩).2 hn`. Simplify using `[ε, h0]`. Establish `e : σ.toRingHom f = algebraMap _ M ((1 : R) ⊗ₜ[ℂ] (⟨f, hf⟩ : S))` using `hσ ⟨f, hf⟩`. Rewrite using `[e]`. Use `⟨(hTa _).1, fun hn => (hTa _).2 ?_⟩` and prove the remaining obligations.

Establish `h0 : εS ⟨f, hf⟩ = 0` using `(hεS ⟨f, hf⟩).2 hn`. Simplify using `[ε, h0]`.
-/
theorem pair_step : ∀ {K L : Type} [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] (R : Subring K) (S : Subring L),
  IsLocModel (algebraMap ℂ K) R → RatRes (algebraMap ℂ K) R →
  IsLocModel (algebraMap ℂ L) S → RatRes (algebraMap ℂ L) S →
  ∃ (M : Type) (_ : Field M) (_ : Algebra ℂ M) (ρ : K →ₐ[ℂ] M) (σ : L →ₐ[ℂ] M) (T : Subring M),
    IsLocModel (algebraMap ℂ M) T ∧ RatRes (algebraMap ℂ M) T ∧
    Dominates ρ.toRingHom T R ∧ Dominates σ.toRingHom T S := by
  intro K L _ _ _ _ R S hR hR' hS hS'
  letI : Algebra ℂ R := ((algebraMap ℂ K).codRestrict R hR.const_mem).toAlgebra
  letI : Algebra ℂ S := ((algebraMap ℂ L).codRestrict S hS.const_mem).toAlgebra
  haveI : IsScalarTower ℂ R K := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower ℂ S L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.EssFiniteType ℂ R := hR.essFiniteType
  haveI : Algebra.EssFiniteType ℂ S := hS.essFiniteType
  haveI := isFractionRing_of_isLocModel hR
  haveI := isFractionRing_of_isLocModel hS
  obtain ⟨εR, hεR⟩ := exists_residue R hR hR'
  obtain ⟨εS, hεS⟩ := exists_residue S hS hS'
  let iR : R →ₐ[ℂ] K := IsScalarTower.toAlgHom ℂ R K
  let iS : S →ₐ[ℂ] L := IsScalarTower.toAlgHom ℂ S L
  have hinj : Function.Injective (Algebra.TensorProduct.map iR iS) := by
    have e : (Algebra.TensorProduct.map iR iS).toLinearMap =
        (iR.toLinearMap.rTensor L).comp (iS.toLinearMap.lTensor R) := by
      ext x y; simp
    have h1 : Function.Injective (iS.toLinearMap.lTensor R) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
    have h2 : Function.Injective (iR.toLinearMap.rTensor L) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
    intro x y hxy
    have ex := LinearMap.congr_fun e x
    have ey := LinearMap.congr_fun e y
    exact h1 (h2 (ex.symm.trans (hxy.trans ey)))
  haveI : IsDomain (K ⊗[ℂ] L) := GlobalTheory.TensorFields.isDomain_tensor_complex K L
  haveI : IsDomain (R ⊗[ℂ] S) := hinj.isDomain _
  haveI : Algebra.EssFiniteType S (S ⊗[ℂ] R) := Algebra.EssFiniteType.baseChange ℂ R S
  haveI : Algebra.EssFiniteType ℂ (S ⊗[ℂ] R) := Algebra.EssFiniteType.comp ℂ S (S ⊗[ℂ] R)
  haveI : Algebra.EssFiniteType ℂ (R ⊗[ℂ] S) :=
    Algebra.EssFiniteType.of_surjective (Algebra.TensorProduct.comm ℂ S R).toAlgHom
      (Algebra.TensorProduct.comm ℂ S R).surjective
  let ε : R ⊗[ℂ] S →ₐ[ℂ] ℂ := Algebra.TensorProduct.lift εR εS fun _ _ => Commute.all _ _
  obtain ⟨T, hT, hT', hTa⟩ := GlobalTheory.T.exists_localModel_at_complexPoint (R ⊗[ℂ] S) ε
  let M := FractionRing (R ⊗[ℂ] S)
  let j : R ⊗[ℂ] S →ₐ[ℂ] M := IsScalarTower.toAlgHom ℂ _ M
  have hj : Function.Injective j := IsFractionRing.injective (R ⊗[ℂ] S) M
  have hl : Function.Injective (j.comp Algebra.TensorProduct.includeLeft) := by
    rw [AlgHom.coe_comp]
    exact hj.comp (Algebra.TensorProduct.includeLeft_injective (S := ℂ) (algebraMap ℂ S).injective)
  have hr : Function.Injective (j.comp Algebra.TensorProduct.includeRight) := by
    rw [AlgHom.coe_comp]
    exact hj.comp (Algebra.TensorProduct.includeRight_injective (algebraMap ℂ R).injective)
  obtain ⟨ρ, hρ⟩ : ∃ ρ : K →ₐ[ℂ] M, ∀ r : R, ρ (r : K) = j (r ⊗ₜ 1) :=
    ⟨IsFractionRing.liftAlgHom hl, fun r => (IsFractionRing.liftAlgHom_apply hl _).trans
      (IsFractionRing.lift_algebraMap hl r)⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : L →ₐ[ℂ] M, ∀ s : S, σ (s : L) = j (1 ⊗ₜ s) :=
    ⟨IsFractionRing.liftAlgHom hr, fun s => (IsFractionRing.liftAlgHom_apply hr _).trans
      (IsFractionRing.lift_algebraMap hr s)⟩
  refine ⟨M, inferInstance, inferInstance, ρ, σ, T, hT, hT', fun f hf => ?_, fun f hf => ?_⟩
  · have e : ρ.toRingHom f = algebraMap _ M ((⟨f, hf⟩ : R) ⊗ₜ[ℂ] (1 : S)) := hρ ⟨f, hf⟩
    rw [e]
    refine ⟨(hTa _).1, fun hn => (hTa _).2 ?_⟩
    have h0 : εR ⟨f, hf⟩ = 0 := (hεR ⟨f, hf⟩).2 hn
    simp [ε, h0]
  · have e : σ.toRingHom f = algebraMap _ M ((1 : R) ⊗ₜ[ℂ] (⟨f, hf⟩ : S)) := hσ ⟨f, hf⟩
    rw [e]
    refine ⟨(hTa _).1, fun hn => (hTa _).2 ?_⟩
    have h0 : εS ⟨f, hf⟩ = 0 := (hεS ⟨f, hf⟩).2 hn
    simp [ε, h0]

/- English proof (translation)
Use `letI : Algebra ℂ O := ((algebraMap ℂ κ).codRestrict O h.const_mem).toAlgebra`. Use `haveI : Algebra.EssFiniteType ℂ O := h.essFiniteType`. Use `haveI : IsScalarTower ℂ O κ := IsScalarTower.of_algebraMap_eq' rfl`. Use `haveI : IsFractionRing O κ := IsFractionRing.of_field O κ (fun f => by`. Take `⟨a, ha, b, hb, hb0, e⟩` from `h.frac f`.

Conclude with `⟨⟨a, ha⟩, ⟨b, hb⟩, (eq_div_iff hb0).2 e⟩)`. Use `haveI : Algebra.EssFiniteType O κ := Algebra.EssFiniteType.of_isLocalization κ (nonZeroDivisors O)`. Use `haveI : Algebra.EssFiniteType ℂ κ := Algebra.EssFiniteType.comp ℂ O κ`. Take `⟨s, hs⟩` from `exists_finset_isTranscendenceBasis ℂ κ`. Use `⟨s.card, fun i => (s.equivFin.symm i : κ), ?_⟩` and prove the remaining obligations.

Establish `e : (algebraMap ℂ κ).toAlgebra = (inferInstance : Algebra ℂ κ)` using `Algebra.algebra_ext _ _ fun _ => rfl`. Unfold `TrBasis`. Rewrite using `[e]`. Conclude with `hs.comp_equiv s.equivFin.symm`.
-/
theorem trBasis_of_isLocModel {κ : Type} [Field κ] [Algebra ℂ κ] {O : Subring κ}
    (h : IsLocModel (algebraMap ℂ κ) O) : ∃ (k : ℕ) (z : Fin k → κ), TrBasis (algebraMap ℂ κ) z := by
  letI : Algebra ℂ O := ((algebraMap ℂ κ).codRestrict O h.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ O := h.essFiniteType
  haveI : IsScalarTower ℂ O κ := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsFractionRing O κ := IsFractionRing.of_field O κ (fun f => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := h.frac f
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, (eq_div_iff hb0).2 e⟩)
  haveI : Algebra.EssFiniteType O κ := Algebra.EssFiniteType.of_isLocalization κ (nonZeroDivisors O)
  haveI : Algebra.EssFiniteType ℂ κ := Algebra.EssFiniteType.comp ℂ O κ
  obtain ⟨s, hs⟩ := exists_finset_isTranscendenceBasis ℂ κ
  refine ⟨s.card, fun i => (s.equivFin.symm i : κ), ?_⟩
  have e : (algebraMap ℂ κ).toAlgebra = (inferInstance : Algebra ℂ κ) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  unfold TrBasis
  rw [e]
  exact hs.comp_equiv s.equivFin.symm

/- English proof (translation)
Proceed by induction on `c with`. Consider the case `zero`. Introduce `O _`. Conclude with `⟨ℂ, inferInstance, inferInstance, Fin.elim0, ⊤, isLocModel_self, ratRes_self, fun i => i.elim0⟩`. Consider the case `succ c ih`.

Introduce `O hO`. Take `⟨κ'', _, _, ρ'', O'', h1, h2, h3⟩` from `ih (fun i => O (Fin.castSucc i)) (fun i => hO _)`. Take `⟨M, _, _, ρ', σ, T, g1, g2, g3, g4⟩` from `pair_step O'' (O (Fin.last c)) h1 h2 (hO _).1 (hO _).2`. Use `⟨M, inferInstance, inferInstance, Fin.lastCases σ (fun j => ρ'.comp (ρ'' j)), T, g1, g2, fun i => ?_⟩` and prove the remaining obligations. Proceed by induction on `i using Fin.lastCases with`.

Consider the case `last => simpa only [Fin.lastCases_last] using g4`. Consider the case `cast j`. Simplify using `only [Fin.lastCases_castSucc]`. Conclude with `(h3 j).trans g3`.
-/
theorem exists_common_dominating_varietyPoint_noTrBasis {κ : Type} [Field κ] [Algebra ℂ κ] (c : ℕ) : ∀ (O : Fin c → Subring κ),
    (∀ i, IsLocModel (algebraMap ℂ κ) (O i) ∧ RatRes (algebraMap ℂ κ) (O i)) →
    ∃ (κ' : Type) (_ : Field κ') (_ : Algebra ℂ κ') (ρ : Fin c → (κ →ₐ[ℂ] κ')) (O' : Subring κ'),
      IsLocModel (algebraMap ℂ κ') O' ∧ RatRes (algebraMap ℂ κ') O' ∧
      ∀ i, Dominates (ρ i).toRingHom O' (O i) := by
  induction c with
  | zero =>
    intro O _
    exact ⟨ℂ, inferInstance, inferInstance, Fin.elim0, ⊤, isLocModel_self, ratRes_self,
      fun i => i.elim0⟩
  | succ c ih =>
    intro O hO
    obtain ⟨κ'', _, _, ρ'', O'', h1, h2, h3⟩ := ih (fun i => O (Fin.castSucc i)) (fun i => hO _)
    obtain ⟨M, _, _, ρ', σ, T, g1, g2, g3, g4⟩ :=
      pair_step O'' (O (Fin.last c)) h1 h2 (hO _).1 (hO _).2
    refine ⟨M, inferInstance, inferInstance, Fin.lastCases σ (fun j => ρ'.comp (ρ'' j)), T, g1, g2,
      fun i => ?_⟩
    induction i using Fin.lastCases with
    | last => simpa only [Fin.lastCases_last] using g4
    | cast j =>
      simp only [Fin.lastCases_castSucc]
      exact (h3 j).trans g3

/- English proof (translation)
Introduce `κ _ _ c O hO _`. Take `⟨κ', _, _, ρ, O', h1, h2, h3⟩` from `exists_common_dominating_varietyPoint_noTrBasis c O hO`. Conclude with `⟨κ', inferInstance, inferInstance, ρ, O', h1, h2, h3, trBasis_of_isLocModel h1⟩`.
-/
theorem exists_common_field : ∀ {κ : Type} [Field κ] [Algebra ℂ κ] (c : ℕ) (O : Fin c → Subring κ),
  (∀ i, IsLocModel (algebraMap ℂ κ) (O i) ∧ RatRes (algebraMap ℂ κ) (O i)) → (∃ (k : ℕ) (z : Fin k → κ), TrBasis (algebraMap ℂ κ) z) →
  ∃ (κ' : Type) (_ : Field κ') (_ : Algebra ℂ κ') (ρ : Fin c → (κ →ₐ[ℂ] κ')) (O' : Subring κ'),
    IsLocModel (algebraMap ℂ κ') O' ∧ RatRes (algebraMap ℂ κ') O' ∧ (∀ i, Dominates (ρ i).toRingHom O' (O i)) ∧
    ∃ (k' : ℕ) (z' : Fin k' → κ'), TrBasis (algebraMap ℂ κ') z' := by
  intro κ _ _ c O hO _
  obtain ⟨κ', _, _, ρ, O', h1, h2, h3⟩ := exists_common_dominating_varietyPoint_noTrBasis c O hO
  exact ⟨κ', inferInstance, inferInstance, ρ, O', h1, h2, h3, trBasis_of_isLocModel h1⟩

end GlobalTheory.CommonPoint
