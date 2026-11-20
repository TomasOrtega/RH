import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CrystallineSubrepresentation

noncomputable section

namespace GlobalTheory.Survey.CrystallineCyclotomic

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) (LL : Type) [Field LL] [Algebra Qp LL]

include PD in

/- English proof (translation)
Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_nontrivial_iff_subsingleton]`. Apply `PD.not_mem_filtration_two` to reduce the goal to its premises. Rewrite using `[Subsingleton.elim PD.t 0, map_zero]`. Conclude with `zero_mem _`.
-/
theorem nontrivial_B : Nontrivial B := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply PD.not_mem_filtration_two
  rw [Subsingleton.elim PD.t 0, map_zero]
  exact zero_mem _

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[mem_Dcris]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Set `e` to `Module.finBasis Qp LL`.

Set `c : Fin (finrank Qp LL) → LL ⊗[Qp] B →ₗ[Qp] B` to `fun i => (TensorProduct.lid Qp B).toLinearMap ∘ₗ (LinearMap.rTensor B (e.coord i))`. Establish `hsum : ∀ y : LL ⊗[Qp] B, y = ∑ i, e i ⊗ₜ[Qp] c i y`. Introduce `y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul v b => conv_lhs => rw [← e.sum_repr v, TensorProduct.sum_tmul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[c, TensorProduct.smul_tmul]`. Consider the case `add a b ha hb`. Simplify using `only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, ← ha, ← hb]`.

Establish `hc : ∀ i g y, c i (actVB PD (Representation.trivial LL G LL) g y) = PD.actB g (c i y)`. Introduce `i g y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b`.

Use `((PD.actB g).toAlgHom.toLinearMap.restrictScalars Qp).map_smul (e.coord i v) b` as an intermediate fact. Establish `h2 : PD.actB g (e.coord i v • b) = e.coord i v • PD.actB g b` using `this`. Simplify using `only [c, actVB, LinearMap.comp_apply, AlgebraTensorModule.map_tmul, LinearMap.rTensor_tmul, LinearEquiv.coe_coe, TensorProduct.lid_tmul, h2]`. Simplify using the standard rewrite rules. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.

Rewrite using `[hsum x]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Take `⟨k, hk⟩` from `PD.invB (c i x) fun g => by rw [← hc, hx]`. Conclude with `⟨e i ⊗ₜ k, by simp [hk]⟩`. Introduce and unpack `⟨y, rfl⟩ g`.

Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => simp [actVB]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.
-/
theorem dcris_trivial [FiniteDimensional Qp LL] :
    Dcris PD (Representation.trivial LL G LL) =
      LinearMap.range (AlgebraTensorModule.map (LinearMap.id : LL →ₗ[LL] LL)
        (IsScalarTower.toAlgHom Qp K₀ B).toLinearMap) := by
  ext x
  rw [mem_Dcris]
  constructor
  · intro hx
    let e := Module.finBasis Qp LL
    let c : Fin (finrank Qp LL) → LL ⊗[Qp] B →ₗ[Qp] B := fun i =>
      (TensorProduct.lid Qp B).toLinearMap ∘ₗ (LinearMap.rTensor B (e.coord i))
    have hsum : ∀ y : LL ⊗[Qp] B, y = ∑ i, e i ⊗ₜ[Qp] c i y := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v b =>
        conv_lhs => rw [← e.sum_repr v, TensorProduct.sum_tmul]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [c, TensorProduct.smul_tmul]
      | add a b ha hb =>
        simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, ← ha, ← hb]
    have hc : ∀ i g y, c i (actVB PD (Representation.trivial LL G LL) g y) = PD.actB g (c i y) := by
      intro i g y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v b =>
        have := ((PD.actB g).toAlgHom.toLinearMap.restrictScalars Qp).map_smul (e.coord i v) b
        have h2 : PD.actB g (e.coord i v • b) = e.coord i v • PD.actB g b := this
        simp only [c, actVB, LinearMap.comp_apply, AlgebraTensorModule.map_tmul,
          LinearMap.rTensor_tmul, LinearEquiv.coe_coe, TensorProduct.lid_tmul, h2]
        simp
      | add a b ha hb => simp only [map_add, ha, hb]
    rw [hsum x]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨k, hk⟩ := PD.invB (c i x) fun g => by rw [← hc, hx]
    exact ⟨e i ⊗ₜ k, by simp [hk]⟩
  · rintro ⟨y, rfl⟩ g
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVB]
    | add a b ha hb => simp only [map_add, ha, hb]

/- English proof (translation)
Use `haveI := nontrivial_B PD`. Use `haveI := PD.finK₀`. Unfold `IsCrys`. Rewrite using `[dcris_trivial, LinearMap.finrank_range_of_inj]`. Simplify using the standard rewrite rules.

Conclude with `Module.Flat.lTensor_preserves_injective_linearMap (M := LL) (IsScalarTower.toAlgHom Qp K₀ B).toLinearMap (algebraMap K₀ B).injective`.
-/
theorem isCrys_trivial [FiniteDimensional Qp LL] : IsCrys PD (Representation.trivial LL G LL) := by
  haveI := nontrivial_B PD
  haveI := PD.finK₀
  unfold IsCrys
  rw [dcris_trivial, LinearMap.finrank_range_of_inj]
  · simp
  · exact Module.Flat.lTensor_preserves_injective_linearMap (M := LL)
      (IsScalarTower.toAlgHom Qp K₀ B).toLinearMap (algebraMap K₀ B).injective

def cyc : G →* LLˣ := (Units.map (algebraMap Qp LL).toMonoidHom).comp PD.χ

/- English proof (translation)
Take `⟨u, hu⟩` from `PD.t_unit`. Set `m : LL ⊗[Qp] B ≃ₗ[LL] LL ⊗[Qp] B` to `AlgebraTensorModule.congr (LinearEquiv.refl LL LL) (u.mulLeftLinearEquiv Qp B)`. Establish `hm : ∀ g y, actVB PD (Representation.trivial LL G LL) g (m y) = m (actVB PD (charRep (cyc PD LL)) g y)`. Introduce `g y`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul v b`. Establish `hmq : ∀ (q : Qp) (z : LL ⊗[Qp] B), m (q • z) = q • m z` using `fun q z => (m : LL ⊗[Qp] B →ₗ[LL] LL ⊗[Qp] B).map_smul_of_tower q z`. Simplify using `[actVB, charRep, cyc, ← Algebra.smul_def, TensorProduct.smul_tmul, hmq]`. Simplify using `[m, hu, PD.t_act]`.

Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Establish `h : (Dcris PD (charRep (cyc PD LL))).map (m : LL ⊗[Qp] B →ₗ[LL] LL ⊗[Qp] B) = Dcris PD (Representation.trivial LL G LL)`. Use extensionality with `x`. Take `⟨y, rfl⟩` from `m.surjective x`. Simplify using `only [Submodule.mem_map, LinearEquiv.coe_coe, m.injective.eq_iff, exists_eq_right, mem_Dcris, hm]`.

Establish `h1` using `isCrys_trivial PD LL`. Unfold `IsCrys at h1 ⊢`. Rewrite using `[← h1, ← h, LinearEquiv.finrank_map_eq]`.
-/
theorem isCrys_cyc [FiniteDimensional Qp LL] : IsCrys PD (charRep (cyc PD LL)) := by
  obtain ⟨u, hu⟩ := PD.t_unit
  let m : LL ⊗[Qp] B ≃ₗ[LL] LL ⊗[Qp] B :=
    AlgebraTensorModule.congr (LinearEquiv.refl LL LL) (u.mulLeftLinearEquiv Qp B)
  have hm : ∀ g y, actVB PD (Representation.trivial LL G LL) g (m y) =
      m (actVB PD (charRep (cyc PD LL)) g y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      have hmq : ∀ (q : Qp) (z : LL ⊗[Qp] B), m (q • z) = q • m z := fun q z =>
        (m : LL ⊗[Qp] B →ₗ[LL] LL ⊗[Qp] B).map_smul_of_tower q z
      simp [actVB, charRep, cyc, ← Algebra.smul_def, TensorProduct.smul_tmul, hmq]
      simp [m, hu, PD.t_act]
    | add a b ha hb => simp only [map_add, ha, hb]
  have h : (Dcris PD (charRep (cyc PD LL))).map (m : LL ⊗[Qp] B →ₗ[LL] LL ⊗[Qp] B) =
      Dcris PD (Representation.trivial LL G LL) := by
    ext x
    obtain ⟨y, rfl⟩ := m.surjective x
    simp only [Submodule.mem_map, LinearEquiv.coe_coe, m.injective.eq_iff, exists_eq_right,
      mem_Dcris, hm]
  have h1 := isCrys_trivial PD LL
  unfold IsCrys at h1 ⊢
  rw [← h1, ← h, LinearEquiv.finrank_map_eq]

/- English proof (translation)
The claim follows from `haveI := LL.2 isCrys_trivial (P.PD K) ↥LL.1`.
-/
theorem exists_crys (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) :
    IsCrys (P.PD K) (Representation.trivial ↥LL.1 ↥(GK K) ↥LL.1) :=
  haveI := LL.2
  isCrys_trivial (P.PD K) ↥LL.1

end GlobalTheory.Survey.CrystallineCyclotomic
