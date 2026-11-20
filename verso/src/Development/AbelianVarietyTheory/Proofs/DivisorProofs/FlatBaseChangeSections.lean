import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ThreeTermComplexOfProjectiveCechModel
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SecFlatBC

/- English proof (translation)
Use `LB.sec_ext fun j => ?_` and prove the remaining obligations. Rewrite using `[AbLaw.SecOn.coord_pullLE, LB.coord_ofSec, LB.coord_ofSec]`. Simplify using `only [Cartier.secPull, resG, Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]`.
-/
theorem pullLE_ofSec {X X' : Scheme.{0}} {L : LB X} (τ : L.Sec) (π : X' ⟶ X) (V : X.Opens) (V' : X'.Opens)
    (e : V' ≤ π ⁻¹ᵁ V) :
    AbLaw.SecOn.pullLE L π V V' e (LB.ofSec τ V) = LB.ofSec (Cartier.secPull τ π) V' := by
  refine LB.sec_ext fun j => ?_
  rw [AbLaw.SecOn.coord_pullLE, LB.coord_ofSec, LB.coord_ofSec]
  simp only [Cartier.secPull, resG, Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

/- English proof (translation)
Set `F : M.Sec →+ Γ(X', M.U i)` to `⟨⟨fun s => s.f i, rfl⟩, fun _ _ => rfl⟩`. Express the relevant statement in the definitionally equal form `F _ = _`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `resG X' le_top (AbLaw.cst f' ⊤ (c a)) * (τ a).f i = _`.

Rewrite using `[show resG X' (le_top : M.U i ≤ ⊤) = AbLaw.rs X' le_top from rfl, AbLaw.rs_cst]`. Both sides reduce to the same expression.
-/
theorem sum_smul_f {X' : Scheme.{0}} {R' : Type} [CommRing R'] (f' : X' ⟶ Sp R') {M : LB X'} {n : ℕ}
    (c : Fin n → R') (τ : Fin n → M.Sec) (i : M.ι) :
    (∑ a, AbLaw.cst f' ⊤ (c a) • τ a).f i = ∑ a, cstOn f' _ (c a) * (τ a).f i := by
  let F : M.Sec →+ Γ(X', M.U i) := ⟨⟨fun s => s.f i, rfl⟩, fun _ _ => rfl⟩
  change F _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  change resG X' le_top (AbLaw.cst f' ⊤ (c a)) * (τ a).f i = _
  rw [show resG X' (le_top : M.U i ≤ ⊤) = AbLaw.rs X' le_top from rfl, AbLaw.rs_cst]
  rfl

/- English proof (translation)
Introduce `R R' _ _ φ X X' f f' π _ _ L hφ H hL σ`. Use `letI := φ.toAlgebra`. Use `haveI : Module.Flat R R' := hφ`. Establish `H' : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap R R')))` using `H`. Establish `: CompactSpace X` using `QuasiCompact.compactSpace_of_compactSpace f`.

Use `GlobalTheory.isAffineHom_diagonal_of_isSeparated f` as an intermediate fact. Take `⟨m, D, hD, hc⟩` from `GlobalTheory.exists_fin_affine_cover (X := X) (V := ⊤) isCompact_univ`. Establish `hD' : ∀ s : Finset (Fin m), s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i)` using `GlobalTheory.isAffineOpen_finset_biInf hD`. Establish `hc'` using `AbLaw.PerfOfModel.iSup_preimage π hc`. Set `E` to `AbLaw.CechOne.secKerEquiv (L.pull π) f' hc'`.

Set `E₀` to `AbLaw.CechOne.secKerEquiv L f hc`. Set `d` to `((AbLaw.cechLB f L D).d 0 1).hom`. Take `⟨x, hx, hxy⟩` from `(AbLaw.PerfOfModel.termMap_bijOn hL H' hD').2.2 (E σ).2`. Establish `hker : LinearMap.ker (d.baseChange R') = LinearMap.range ((LinearMap.ker d).subtype.baseChange R')` using `Module.Flat.ker_lTensor_eq (R := R) R' R' d`. Rewrite `hx` using `[hker]`.

Take `⟨z, rfl⟩` from `hx`. Take `⟨S, rfl⟩` from `TensorProduct.exists_finset z`. Set `e` to `S.equivFin`. Use `⟨S.card, fun a => (e.symm a).1.1, fun a => E₀.symm (e.symm a).1.2, ?_⟩` and prove the remaining obligations. Establish `key : σ = ∑ a, AbLaw.cst f' ⊤ ((e.symm a).1.1) • Cartier.secPull (E₀.symm (e.symm a).1.2) π`.

Apply `E.injective` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hxy, map_sum, map_sum, map_sum, AddSubmonoid.coe_finset_sum, ← Finset.sum_coe_sort S, ← e.symm.sum_comp]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[AbLaw.CechOne.secKerEquiv_smul, LinearMap.baseChange_tmul]`.

Use function extensionality and compare the values at `s`. Establish `hk : (((e.symm a).1.2).1 : (AbLaw.cechLB f L D).X 0) s = AbLaw.SecOnR.of f L _ (LB.ofSec (E₀.symm (e.symm a).1.2) (⨅ i ∈ s.1, D i))`. Rewrite using `[← AbLaw.CechOne.secKerEquiv_val L f hc]`. Conclude with `congrArg (fun y => (y.1 : (AbLaw.cechLB f L D).X 0) s) (E₀.apply_symm_apply _).symm`. Express the relevant statement in the definitionally equal form `(e.symm a).1.1 • AbLaw.secCubePull L D H'.w s.1 ((((e.symm a).1.2).1 : (AbLaw.cechLB f L D).X 0) s) = (e.symm a).1.1 • ((E (Cartier.secPull (E₀.symm (e.symm a).1.2) π)).1 : (AbLaw.cechLB f' (L.pull π) fun i ↦ π ⁻¹ᵁ D i).X 0) s`.

Rewrite using `[hk, AbLaw.CechOne.secKerEquiv_val]`. Express the relevant statement in the definitionally equal form `_ • AbLaw.SecOnR.pull L H'.w _ _ _ _ = _`. Rewrite using `[AbLaw.SecOnR.pull_of, pullLE_ofSec]`. Both sides reduce to the same expression. Introduce `i`.

Rewrite using `[key, sum_smul_f]`.
-/
theorem exists_sum_secPull : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) [QuasiCompact f] [IsSeparated f] (L : LB X), φ.Flat → IsPullback π f' f (spMap φ) → L.IsLB → ∀ σ : (L.pull π).Sec, ∃ (n : ℕ) (c : Fin n → R') (τ : Fin n → L.Sec), ∀ i, σ.f i = ∑ a, cstOn f' _ (c a) * (Cartier.secPull (τ a) π).f i := by
  intro R R' _ _ φ X X' f f' π _ _ L hφ H hL σ
  letI := φ.toAlgebra
  haveI : Module.Flat R R' := hφ
  have H' : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := H
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have := GlobalTheory.isAffineHom_diagonal_of_isSeparated f
  obtain ⟨m, D, hD, hc⟩ := GlobalTheory.exists_fin_affine_cover (X := X) (V := ⊤) isCompact_univ
  have hD' : ∀ s : Finset (Fin m), s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i) :=
    GlobalTheory.isAffineOpen_finset_biInf hD
  have hc' := AbLaw.PerfOfModel.iSup_preimage π hc
  let E := AbLaw.CechOne.secKerEquiv (L.pull π) f' hc'
  let E₀ := AbLaw.CechOne.secKerEquiv L f hc
  let d := ((AbLaw.cechLB f L D).d 0 1).hom
  obtain ⟨x, hx, hxy⟩ := (AbLaw.PerfOfModel.termMap_bijOn hL H' hD').2.2 (E σ).2
  have hker : LinearMap.ker (d.baseChange R') = LinearMap.range ((LinearMap.ker d).subtype.baseChange R') :=
    Module.Flat.ker_lTensor_eq (R := R) R' R' d
  rw [hker] at hx
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset z
  let e := S.equivFin
  refine ⟨S.card, fun a => (e.symm a).1.1, fun a => E₀.symm (e.symm a).1.2, ?_⟩

  have key : σ = ∑ a, AbLaw.cst f' ⊤ ((e.symm a).1.1) • Cartier.secPull (E₀.symm (e.symm a).1.2) π := by
    apply E.injective
    apply Subtype.ext
    rw [← hxy, map_sum, map_sum, map_sum, AddSubmonoid.coe_finset_sum,
      ← Finset.sum_coe_sort S, ← e.symm.sum_comp]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [AbLaw.CechOne.secKerEquiv_smul, LinearMap.baseChange_tmul]
    funext s
    have hk : (((e.symm a).1.2).1 : (AbLaw.cechLB f L D).X 0) s =
        AbLaw.SecOnR.of f L _ (LB.ofSec (E₀.symm (e.symm a).1.2) (⨅ i ∈ s.1, D i)) := by
      rw [← AbLaw.CechOne.secKerEquiv_val L f hc]
      exact congrArg (fun y => (y.1 : (AbLaw.cechLB f L D).X 0) s) (E₀.apply_symm_apply _).symm
    change (e.symm a).1.1 • AbLaw.secCubePull L D H'.w s.1 ((((e.symm a).1.2).1 : (AbLaw.cechLB f L D).X 0) s) =
      (e.symm a).1.1 • ((E (Cartier.secPull (E₀.symm (e.symm a).1.2) π)).1 : (AbLaw.cechLB f' (L.pull π) fun i ↦ π ⁻¹ᵁ D i).X 0) s
    rw [hk, AbLaw.CechOne.secKerEquiv_val]
    change _ • AbLaw.SecOnR.pull L H'.w _ _ _ _ = _
    rw [AbLaw.SecOnR.pull_of, pullLE_ofSec]
    rfl
  intro i
  rw [key, sum_smul_f]

end GlobalTheory.SecFlatBC
