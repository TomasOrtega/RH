import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.BijOnKerAndExactOfQuasiIsoBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianProjectiveBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CyclicIdeal

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.MumfordLocal

section Matrices

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']

def vec {P : Type} [AddCommGroup P] [Module R P] {a : ℕ} (b : Module.Basis (Fin a) R P) :
    (Fin a → R') ≃ₗ[R'] R' ⊗[R] P :=
  (Algebra.TensorProduct.basis R' b).equivFun.symm

/- English proof (translation)
Simplify using `[vec, TensorProduct.smul_tmul']`.
-/
theorem vec_apply {P : Type} [AddCommGroup P] [Module R P] {a : ℕ} (b : Module.Basis (Fin a) R P)
    (v : Fin a → R') : vec b v = ∑ k, v k ⊗ₜ[R] b k := by
  simp [vec, TensorProduct.smul_tmul']

/- English proof (translation)
Rewrite using `[vec, LinearEquiv.symm_apply_eq, ← LinearMap.toMatrix_baseChange, Module.Basis.equivFun_apply, ← LinearMap.toMatrix_mulVec_repr (Algebra.TensorProduct.basis R' b)]`. Use `congr 1`. Conclude with `((Algebra.TensorProduct.basis R' b).equivFun.apply_symm_apply v).symm`.
-/
theorem vec_mulVec {P Q : Type} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] {a c : ℕ}
    (b : Module.Basis (Fin a) R P) (b' : Module.Basis (Fin c) R Q) (d : P →ₗ[R] Q) (v : Fin a → R') :
    vec b' (((LinearMap.toMatrix b b' d).map (algebraMap R R')).mulVec v) =
      d.baseChange R' (vec b v) := by
  rw [vec, LinearEquiv.symm_apply_eq, ← LinearMap.toMatrix_baseChange, Module.Basis.equivFun_apply,
    ← LinearMap.toMatrix_mulVec_repr (Algebra.TensorProduct.basis R' b)]
  congr 1
  exact ((Algebra.TensorProduct.basis R' b).equivFun.apply_symm_apply v).symm

/- English proof (translation)
Establish `h : ∀ ψ, b.dualBasis.equivFun (d.dualMap ψ) = (LinearMap.toMatrix b b' d).transpose.mulVecLin (b'.dualBasis.equivFun ψ)` using `fun ψ => by`. Rewrite using `[← LinearMap.toMatrix_transpose, Matrix.mulVecLin_apply]`. Conclude with `(LinearMap.toMatrix_mulVec_repr b'.dualBasis b.dualBasis _ ψ).symm`. Use `⟨Submodule.Quotient.equiv _ _ b.dualBasis.equivFun ?_⟩` and prove the remaining obligations. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨ψ, rfl⟩, rfl⟩`. Conclude with `⟨_, (h ψ).symm⟩`. Introduce and unpack `⟨y, rfl⟩`. Take `⟨ψ, rfl⟩` from `b'.dualBasis.equivFun.surjective y`.

Conclude with `⟨_, ⟨ψ, rfl⟩, h ψ⟩`.
-/
theorem coker_dualMap_equiv {P Q : Type} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    {a c : ℕ} (b : Module.Basis (Fin a) R P) (b' : Module.Basis (Fin c) R Q) (d : P →ₗ[R] Q) :
    Nonempty ((Module.Dual R P ⧸ LinearMap.range d.dualMap) ≃ₗ[R]
      ((Fin a → R) ⧸ LinearMap.range (LinearMap.toMatrix b b' d).transpose.mulVecLin)) := by
  have h : ∀ ψ, b.dualBasis.equivFun (d.dualMap ψ) =
      (LinearMap.toMatrix b b' d).transpose.mulVecLin (b'.dualBasis.equivFun ψ) := fun ψ => by
    rw [← LinearMap.toMatrix_transpose, Matrix.mulVecLin_apply]
    exact (LinearMap.toMatrix_mulVec_repr b'.dualBasis b.dualBasis _ ψ).symm
  refine ⟨Submodule.Quotient.equiv _ _ b.dualBasis.equivFun ?_⟩
  ext x
  constructor
  · rintro ⟨_, ⟨ψ, rfl⟩, rfl⟩
    exact ⟨_, (h ψ).symm⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨ψ, rfl⟩ := b'.dualBasis.equivFun.surjective y
    exact ⟨_, ⟨ψ, rfl⟩, h ψ⟩

end Matrices

section Complex

variable {R : Type} [CommRing R] {Y : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of R)} {M : LB Y}
  {κ : Type} [LinearOrder κ] [Fintype κ] {D : κ → Y.Opens}
  {C : CochainComplex (ModuleCat.{0} R) ℕ} (φ : C ⟶ cechLB f M D)

def loc (x : C.X 0) (p : κ × M.ι) : Γ(Y, (⨅ l ∈ ({p.1} : Finset κ), D l) ⊓ M.U p.2) :=
  SecOnR.coord (f := f) (M := M) ((φ.f 0).hom x ⟨{p.1}, Finset.card_singleton _⟩) p.2

variable {R' : Type} [CommRing R'] [Algebra R R'] {Y' : Scheme.{0}} {π : Y' ⟶ Y}
  {f' : Y' ⟶ Spec (CommRingCat.of R')}

omit [Fintype κ] in

/- English proof (translation)
The claim follows from `congrArg ModuleCat.Hom.hom (cechLB_d f M D p)`.
-/
theorem cech_d (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) (D : κ → Y.Opens) (p : ℕ) :
    ((cechLB f M D).d p (p + 1)).hom = Cube.d (secCube f M D) (p + 1) :=
  congrArg ModuleCat.Hom.hom (cechLB_d f M D p)

/- English proof (translation)
Establish `hb` using `(bijOn_ker_and_exact_of_quasiIso_baseChange R R' C _ φ hφ).1`. Establish `hc' : ⨆ i, π ⁻¹ᵁ D i = ⊤` using `by rw [← Scheme.Hom.preimage_iSup, hc]; rfl`. Establish `h₁` using `secTermBaseChange_bijective hM H 1 fun s hs => hD s (Finset.card_pos.1 (by omega))`. Establish `h₂` using `secTermBaseChange_bijective hM H 2 fun s hs => hD s (Finset.card_pos.1 (by omega))`. Rewrite `hb` using `[cech_d f M D 0]`.

Establish `hk : ∀ y, secTermBaseChange M D H.w 1 y ∈ LinearMap.ker ((cechLB f' (M.pull π) fun i => π ⁻¹ᵁ D i).d 0 1).hom ↔ y ∈ LinearMap.ker ((Cube.d (secCube f M D) 1).baseChange R')` using `fun y => by`. Rewrite using `[cech_d f' _ _ 0]`. Express the relevant statement in the definitionally equal form `Cube.d _ 1 _ = 0 ↔ _`. Rewrite using `[d_secTermBaseChange]`. Conclude with `map_eq_zero_iff _ h₂.1`.

Set `F : LinearMap.ker ((C.d 0 1).hom.baseChange R') → LinearMap.ker ((cechLB f' (M.pull π) fun i => π ⁻¹ᵁ D i).d 0 1).hom` to `fun x => ⟨secTermBaseChange M D H.w 1 ((φ.f 0).hom.baseChange R' x.1), (hk _).2 (hb.1 x.2)⟩`. Establish `hF : Function.Bijective F`. Use `⟨fun x y h => Subtype.ext (hb.2.1 x.2 y.2 (h₁.1 (congrArg Subtype.val h))), fun z => ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `h₁.2 z.1`. Take `⟨x, hx, rfl⟩` from `hb.2.2 ((hk y).1 (hy ▸ z.2))`.

Conclude with `⟨⟨x, hx⟩, Subtype.ext hy⟩`. Use `⟨(Equiv.ofBijective F hF).trans (CechOne.secKerEquiv (M.pull π) f' hc').toEquiv.symm, fun x s => ?_⟩` and prove the remaining obligations. Use `(CechOne.secKerEquiv_val (M.pull π) f' hc' _ s).symm.trans ?_` and prove the remaining obligations. Conclude with `congrFun (congrArg Subtype.val ((CechOne.secKerEquiv (M.pull π) f' hc').apply_symm_apply (F x))) s`.
-/
theorem exists_equiv_sec (hM : M.IsLB) (hc : ⨆ i, D i = ⊤)
    (hD : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i))
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (hφ : QuasiIso
      (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R R')).mapHomologicalComplex _).map φ)) :
    ∃ E : LinearMap.ker ((C.d 0 1).hom.baseChange R') ≃ LB.Sec (M.pull π), ∀ x s,
      SecOnR.of f' _ _ (GlobalTheory.LB.ofSec (E x) (⨅ i ∈ s.1, π ⁻¹ᵁ D i)) =
        secTermBaseChange M D H.w 1 ((φ.f 0).hom.baseChange R' x.1) s := by
  have hb := (bijOn_ker_and_exact_of_quasiIso_baseChange R R' C _ φ hφ).1
  have hc' : ⨆ i, π ⁻¹ᵁ D i = ⊤ := by rw [← Scheme.Hom.preimage_iSup, hc]; rfl
  have h₁ := secTermBaseChange_bijective hM H 1 fun s hs => hD s (Finset.card_pos.1 (by omega))
  have h₂ := secTermBaseChange_bijective hM H 2 fun s hs => hD s (Finset.card_pos.1 (by omega))
  rw [cech_d f M D 0] at hb
  have hk : ∀ y, secTermBaseChange M D H.w 1 y ∈
      LinearMap.ker ((cechLB f' (M.pull π) fun i => π ⁻¹ᵁ D i).d 0 1).hom ↔
      y ∈ LinearMap.ker ((Cube.d (secCube f M D) 1).baseChange R') := fun y => by
    rw [cech_d f' _ _ 0]
    change Cube.d _ 1 _ = 0 ↔ _
    rw [d_secTermBaseChange]
    exact map_eq_zero_iff _ h₂.1
  let F : LinearMap.ker ((C.d 0 1).hom.baseChange R') →
      LinearMap.ker ((cechLB f' (M.pull π) fun i => π ⁻¹ᵁ D i).d 0 1).hom := fun x =>
    ⟨secTermBaseChange M D H.w 1 ((φ.f 0).hom.baseChange R' x.1), (hk _).2 (hb.1 x.2)⟩
  have hF : Function.Bijective F := by
    refine ⟨fun x y h => Subtype.ext (hb.2.1 x.2 y.2 (h₁.1 (congrArg Subtype.val h))), fun z => ?_⟩
    obtain ⟨y, hy⟩ := h₁.2 z.1
    obtain ⟨x, hx, rfl⟩ := hb.2.2 ((hk y).1 (hy ▸ z.2))
    exact ⟨⟨x, hx⟩, Subtype.ext hy⟩
  refine ⟨(Equiv.ofBijective F hF).trans (CechOne.secKerEquiv (M.pull π) f' hc').toEquiv.symm,
    fun x s => ?_⟩
  refine (CechOne.secKerEquiv_val (M.pull π) f' hc' _ s).symm.trans ?_
  exact congrFun (congrArg Subtype.val
    ((CechOne.secKerEquiv (M.pull π) f' hc').apply_symm_apply (F x))) s

/- English proof (translation)
Use `(bijOn_ker_and_exact_of_quasiIso_baseChange R R' C _ φ hφ).2 ?_` and prove the remaining obligations. Establish `hc' : ⨆ i, π ⁻¹ᵁ D i = ⊤` using `by rw [← Scheme.Hom.preimage_iSup, hc]; rfl`. Establish `h₁` using `secTermBaseChange_bijective hM H 1 fun s hs => hD s (Finset.card_pos.1 (by omega))`. Establish `h₂` using `secTermBaseChange_bijective hM H 2 fun s hs => hD s (Finset.card_pos.1 (by omega))`. Establish `h₃` using `secTermBaseChange_bijective hM H 3 fun s hs => hD s (Finset.card_pos.1 (by omega))`.

Establish `he` using `(cechComplex_exactAt_succ_iff _ 0).1 (CechOne.exactAt_one_of_h1Zero f' (LB.isLB_pull hM π) hc' h)`. Rewrite using `[cech_d f M D 0, cech_d f M D 1]`. Introduce `y`. Establish `e` using `he (secTermBaseChange M D H.w 2 y)`. Use `erw [d_secTermBaseChange, map_eq_zero_iff _ h₃.1] at e`.

Use `e.trans ⟨fun ⟨z, hz⟩ => ?_, fun ⟨x, hx⟩ => ⟨secTermBaseChange M D H.w 1 x, ?_⟩⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `h₁.2 z`. Conclude with `⟨x, h₂.1 ((d_secTermBaseChange M D H.w 1 x).symm.trans hz)⟩`. Conclude with `(d_secTermBaseChange M D H.w 1 x).trans (congrArg _ hx)`.
-/
theorem exact_of_h1Zero (hM : M.IsLB) (hc : ⨆ i, D i = ⊤)
    (hD : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i))
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (hφ : QuasiIso
      (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R R')).mapHomologicalComplex _).map φ))
    (h : FirstCohomologyVanishes (M.pull π)) :
    Function.Exact ((C.d 0 1).hom.baseChange R') ((C.d 1 2).hom.baseChange R') := by
  refine (bijOn_ker_and_exact_of_quasiIso_baseChange R R' C _ φ hφ).2 ?_
  have hc' : ⨆ i, π ⁻¹ᵁ D i = ⊤ := by rw [← Scheme.Hom.preimage_iSup, hc]; rfl
  have h₁ := secTermBaseChange_bijective hM H 1 fun s hs => hD s (Finset.card_pos.1 (by omega))
  have h₂ := secTermBaseChange_bijective hM H 2 fun s hs => hD s (Finset.card_pos.1 (by omega))
  have h₃ := secTermBaseChange_bijective hM H 3 fun s hs => hD s (Finset.card_pos.1 (by omega))
  have he := (cechComplex_exactAt_succ_iff _ 0).1
    (CechOne.exactAt_one_of_h1Zero f' (LB.isLB_pull hM π) hc' h)
  rw [cech_d f M D 0, cech_d f M D 1]
  intro y
  have e := he (secTermBaseChange M D H.w 2 y)
  erw [d_secTermBaseChange, map_eq_zero_iff _ h₃.1] at e
  refine e.trans ⟨fun ⟨z, hz⟩ => ?_, fun ⟨x, hx⟩ => ⟨secTermBaseChange M D H.w 1 x, ?_⟩⟩
  · obtain ⟨x, rfl⟩ := h₁.2 z
    exact ⟨x, h₂.1 ((d_secTermBaseChange M D H.w 1 x).symm.trans hz)⟩
  · exact (d_secTermBaseChange M D H.w 1 x).trans (congrArg _ hx)

omit [Fintype κ] in

/- English proof (translation)
Set `G : R' ⊗[R] C.X 0 →+ Γ(Y', π ⁻¹ᵁ ((⨅ l ∈ ({p.1} : Finset κ), D l) ⊓ M.U p.2))` to `AddMonoidHom.mk' (fun z => rs Y' h (SecOnR.coord (f := f') (M := M.pull π) (secTermBaseChange M D w 1 ((φ.f 0).hom.baseChange R' z) ⟨{p.1}, Finset.card_singleton _⟩) fun _ => p.2)) fun z z' => by erw [map_add, map_add]`. Conclude with `map_add (rs Y' h) _ _`. Use `(map_sum G _ _).trans (Finset.sum_congr rfl fun k _ => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `rs Y' h (SecOnR.coord (f := f') (M := M.pull π) (v k • secCubePull M D w {p.1} ((φ.f 0).hom (x k) ⟨{p.1}, Finset.card_singleton _⟩)) fun _ => p.2) = _`. Use `erw [SecOnR.coord_base_smul]`.

Rewrite using `[map_mul, rs_cst]`. Use `congr 1`. Use `(congrArg (rs Y' h) (SecOn.coord_pullLE π (preimage_biInf D π _).ge _ _)).trans ?_` and prove the remaining obligations. Use `(GlobalTheory.LB.resG_appLE π _ _ _).trans ?_` and prove the remaining obligations. Conclude with `congrArg (fun q => q.hom (loc φ (x k) p)) (Scheme.Hom.app_eq_appLE π).symm`.
-/
theorem coord_secTermBaseChange (w : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
    {a : ℕ} (v : Fin a → R') (x : Fin a → C.X 0) (p : κ × M.ι)
    (h : π ⁻¹ᵁ ((⨅ l ∈ ({p.1} : Finset κ), D l) ⊓ M.U p.2) ≤
      (⨅ l ∈ ({p.1} : Finset κ), π ⁻¹ᵁ D l) ⊓ (M.pull π).U fun _ => p.2) :
    rs Y' h (SecOnR.coord (f := f') (M := M.pull π) (secTermBaseChange M D w 1
      ((φ.f 0).hom.baseChange R' (∑ k, v k ⊗ₜ[R] x k)) ⟨{p.1}, Finset.card_singleton _⟩) fun _ => p.2) =
      ∑ k, cst f' _ (v k) * (π.app _).hom (loc φ (x k) p) := by
  let G : R' ⊗[R] C.X 0 →+ Γ(Y', π ⁻¹ᵁ ((⨅ l ∈ ({p.1} : Finset κ), D l) ⊓ M.U p.2)) :=
    AddMonoidHom.mk' (fun z => rs Y' h (SecOnR.coord (f := f') (M := M.pull π) (secTermBaseChange M D w 1
      ((φ.f 0).hom.baseChange R' z) ⟨{p.1}, Finset.card_singleton _⟩) fun _ => p.2))
      fun z z' => by
        erw [map_add, map_add]
        exact map_add (rs Y' h) _ _
  refine (map_sum G _ _).trans (Finset.sum_congr rfl fun k _ => ?_)
  change rs Y' h (SecOnR.coord (f := f') (M := M.pull π) (v k • secCubePull M D w {p.1}
    ((φ.f 0).hom (x k) ⟨{p.1}, Finset.card_singleton _⟩)) fun _ => p.2) = _
  erw [SecOnR.coord_base_smul]
  rw [map_mul, rs_cst]
  congr 1
  refine (congrArg (rs Y' h) (SecOn.coord_pullLE π (preimage_biInf D π _).ge _ _)).trans ?_
  refine (GlobalTheory.LB.resG_appLE π _ _ _).trans ?_
  exact congrArg (fun q => q.hom (loc φ (x k) p)) (Scheme.Hom.app_eq_appLE π).symm

def perfOfBases (hM : M.IsLB) (hc : ⨆ i, D i = ⊤)
    (hD : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i))
    (hφ : ∀ (R' : Type) [CommRing R'] [Algebra R R'], QuasiIso
      (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R R')).mapHomologicalComplex _).map φ))
    {a b c : ℕ} (b₀ : Module.Basis (Fin a) R (C.X 0)) (b₁ : Module.Basis (Fin b) R (C.X 1))
    (b₂ : Module.Basis (Fin c) R (C.X 2)) : Perf f M where
  a := a
  b := b
  c := c
  D₀ := LinearMap.toMatrix b₀ b₁ (C.d 0 1).hom
  D₁ := LinearMap.toMatrix b₁ b₂ (C.d 1 2).hom
  comp := by
    rw [← LinearMap.toMatrix_comp, ← ModuleCat.hom_comp, C.d_comp_d, ModuleCat.hom_zero, map_zero]
  I := κ × M.ι
  W p := (⨅ l ∈ ({p.1} : Finset κ), D l) ⊓ M.U p.2
  ch p := p.2
  le _ := inf_le_right
  cover := by
    refine top_unique fun y _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc.ge (Set.mem_univ y))
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hM.cover.ge (Set.mem_univ y))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), CechOne.le_single D le_rfl hi, hj⟩
  u k := loc φ (b₀ k)
  sec R' _ g Y' π f' H := by
    letI := g.toAlgebra
    obtain ⟨E, hE⟩ := exists_equiv_sec φ hM hc hD H (hφ R')
    refine ⟨((vec b₀).toEquiv.subtypeEquiv fun v => ?_).trans E, fun v p => ?_⟩
    · rw [← (vec b₁).map_eq_zero_iff]
      exact (congrArg (· = 0) (vec_mulVec b₀ b₁ _ v)).to_iff
    · have h : π ⁻¹ᵁ ((⨅ l ∈ ({p.1} : Finset κ), D l) ⊓ M.U p.2) ≤
          (⨅ l ∈ ({p.1} : Finset κ), π ⁻¹ᵁ D l) ⊓ (M.pull π).U fun _ => p.2 :=
        le_inf ((π.preimage_mono inf_le_left).trans (preimage_biInf D π _).le)
          (le_pull M π inf_le_right)
      refine Eq.trans ?_ (coord_secTermBaseChange φ H.w v.1 b₀ p h)
      rw [← vec_apply]
      exact (rs_rs _ h _).symm.trans (congrArg (fun z => rs Y' h (SecOnR.coord (f := f') (M := M.pull π) z fun _ => p.2))
        (hE _ ⟨{p.1}, Finset.card_singleton _⟩))
  exact R' _ g Y' π f' H h w hw := by
    letI := g.toAlgebra
    obtain ⟨x, hx⟩ := (exact_of_h1Zero φ hM hc hD H (hφ R') h (vec b₁ w)).1
      ((vec_mulVec b₁ b₂ _ w).symm.trans ((congrArg (vec b₂) hw).trans (map_zero _)))
    obtain ⟨v, rfl⟩ := (vec b₀).surjective x
    exact ⟨v, (vec b₁).injective ((vec_mulVec b₀ b₁ _ v).trans hx)⟩

end Complex

section Geometry

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left)

/- English proof (translation)
Use `(KerPow.pull_iff _ _ q).2 (KerPow.hasGen_of_trivial hL fun U _ g => ?_)` and prove the remaining obligations. Set `q' : Over.mk (q ≫ (A ⊗ A).hom) ⟶ A ⊗ A` to `Over.homMk q rfl`. Establish `hs : s = q ≫ (A ⊗ A).hom`. Establish `h₁ : η[A].left ≫ A.hom = 𝟙 S` using `Over.w η[A]`. Rewrite using `[← Over.w (fst A A), reassoc_of% h, h₁]`.

Conclude with `(Category.comp_id _).symm`. Establish `h₁ : q' ≫ fst A A = 1`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `h.trans ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `s ≫ η[A].left = (toUnit (Over.mk (q ≫ (A ⊗ A).hom))).left ≫ η[A].left`.

Rewrite using `[hs, Over.toUnit_left]`. Both sides reduce to the same expression. Establish `h₂ : q ≫ (lift (fst A A ≫ 𝟙 A) (snd A A) ≫ μ[A]).left = q ≫ (snd A A).left`. Express the relevant statement in the definitionally equal form `(q' ≫ lift (fst A A ≫ 𝟙 A) (snd A A) ≫ μ[A]).left = (q' ≫ snd A A).left`. Rewrite using `[comp_lift_assoc, Category.comp_id, h₁, ← Hom.mul_def, _root_.one_mul]`.

Rewrite using `[Fin.prod_univ_two]`. Express the relevant statement in the definitionally equal form `g (q ≫ (lift (fst A A ≫ 𝟙 A) (snd A A) ≫ μ[A]).left) ^ (1 : ℤ) * g (q ≫ (snd A A).left) ^ (-1 : ℤ) = 1`. Rewrite using `[h₂, ← zpow_add]`. Simplify using the standard rewrite rules.
-/
theorem triv_of_origin (hL : L.IsLB) {X : Scheme.{0}} (q : X ⟶ (A ⊗ A).left) (s : X ⟶ S)
    (h : q ≫ (fst A A).left = s ≫ η[A].left) : Triv ((translDiff A L (𝟙 A)).pull q) := by
  refine (KerPow.pull_iff _ _ q).2 (KerPow.hasGen_of_trivial hL fun U _ g => ?_)
  let q' : Over.mk (q ≫ (A ⊗ A).hom) ⟶ A ⊗ A := Over.homMk q rfl
  have hs : s = q ≫ (A ⊗ A).hom := by
    have h₁ : η[A].left ≫ A.hom = 𝟙 S := Over.w η[A]
    rw [← Over.w (fst A A), reassoc_of% h, h₁]
    exact (Category.comp_id _).symm
  have h₁ : q' ≫ fst A A = 1 := by
    apply Over.OverMorphism.ext
    refine h.trans ?_
    change s ≫ η[A].left = (toUnit (Over.mk (q ≫ (A ⊗ A).hom))).left ≫ η[A].left
    rw [hs, Over.toUnit_left]
    rfl
  have h₂ : q ≫ (lift (fst A A ≫ 𝟙 A) (snd A A) ≫ μ[A]).left = q ≫ (snd A A).left := by
    change (q' ≫ lift (fst A A ≫ 𝟙 A) (snd A A) ≫ μ[A]).left = (q' ≫ snd A A).left
    rw [comp_lift_assoc, Category.comp_id, h₁, ← Hom.mul_def, _root_.one_mul]
  rw [Fin.prod_univ_two]
  change g (q ≫ (lift (fst A A ≫ 𝟙 A) (snd A A) ≫ μ[A]).left) ^ (1 : ℤ) *
    g (q ≫ (snd A A).left) ^ (-1 : ℤ) = 1
  rw [h₂, ← zpow_add]
  simp

/- English proof (translation)
Establish `h₀ : IsPullback (snd A A).left (fst A A).left A.hom A.hom` using `(IsPullback.of_hasPullback A.hom A.hom).flip`. Establish `h₁ : IsPullback (snd T A).left (fst T A).left A.hom T.hom` using `(IsPullback.of_hasPullback T.hom A.hom).flip`. Use `IsPullback.of_right ?_ ?_ h₀` and prove the remaining obligations. Rewrite using `[← Over.comp_left, whiskerRight_snd, Over.w]`. Conclude with `h₁`.

Rewrite using `[← Over.comp_left, whiskerRight_fst, Over.comp_left]`.
-/
theorem isPullback_whiskerRight {T : Over S} (x : T ⟶ A) :
    IsPullback (x ▷ A).left (fst T A).left (fst A A).left x.left := by
  have h₀ : IsPullback (snd A A).left (fst A A).left A.hom A.hom :=
    (IsPullback.of_hasPullback A.hom A.hom).flip
  have h₁ : IsPullback (snd T A).left (fst T A).left A.hom T.hom :=
    (IsPullback.of_hasPullback T.hom A.hom).flip
  refine IsPullback.of_right ?_ ?_ h₀
  · rw [← Over.comp_left, whiskerRight_snd, Over.w]
    exact h₁
  · rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]

/- English proof (translation)
Establish `h₁` using `(KerPow.pull_iff _ _ _).1 h`. Establish `h₂` using `hK R t x fun p => ⟨⊤, trivial, (KerPow.pull_iff _ _ _).2 (h₁.pull ((fst (Over.mk t) A).left ⁻¹ᵁ ⊤).ι fun k => ?_)⟩`. Rewrite using `[h₂, Over.comp_left, Over.toUnit_left]`. Both sides reduce to the same expression. Use `congr 1 fin_cases k`.

Express the relevant statement in the definitionally equal form `(x ▷ A ≫ lift (fst A A ≫ 𝟙 A) (snd A A) ≫ μ[A]).left = (lift (fst _ A ≫ x) (snd _ A) ≫ μ[A]).left`. Rewrite using `[comp_lift_assoc, Category.comp_id, whiskerRight_fst, whiskerRight_snd]`. Express the relevant statement in the definitionally equal form `(x ▷ A ≫ snd A A).left = (snd _ A).left`. Rewrite using `[whiskerRight_snd]`.
-/
theorem eq_origin_of_triv (hK : KTriv A L) {R : Type} [CommRing R] {t : Spec (CommRingCat.of R) ⟶ S}
    (x : Over.mk t ⟶ A) (h : Triv ((translDiff A L (𝟙 A)).pull (x ▷ A).left)) :
    x.left = t ≫ η[A].left := by
  have h₁ := (KerPow.pull_iff _ _ _).1 h
  have h₂ := hK R t x fun p => ⟨⊤, trivial, (KerPow.pull_iff _ _ _).2
    (h₁.pull ((fst (Over.mk t) A).left ⁻¹ᵁ ⊤).ι fun k => ?_)⟩
  · rw [h₂, Over.comp_left, Over.toUnit_left]
    rfl
  · congr 1
    fin_cases k
    · change (x ▷ A ≫ lift (fst A A ≫ 𝟙 A) (snd A A) ≫ μ[A]).left =
        (lift (fst _ A ≫ x) (snd _ A) ≫ μ[A]).left
      rw [comp_lift_assoc, Category.comp_id, whiskerRight_fst, whiskerRight_snd]
    · change (x ▷ A ≫ snd A A).left = (snd _ A).left
      rw [whiskerRight_snd]

end Geometry

/- English proof (translation)
Introduce `K _ _ P R _ t₀ χ₀ O _ _ _ _ _ t Y π f H ht₀ hχ ht κ _ _ D C φ hD hc hC hφ`. Take `⟨-, hsep, -, hcl, hsurj, HA⟩` from `(AbProj.abelian_projective_baseChange K P).2 O t Y π f H`. Establish `hM : ((translDiff P.A P.L (𝟙 P.A)).pull π).IsLB` using `LB.isLB_pull (LB.isLB_linComb P.isLB _ _) π`. Use `haveI : Y.IsSeparated := ⟨by`. Rewrite using `[← terminal.comp_from f]`.

Use the proof step `infer_instance⟩`. Establish `hD' : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i)` using `fun s hs => by`. Proceed by induction on `hs using Finset.Nonempty.cons_induction with`. Consider the case `singleton i => simpa using hD i`. Consider the case `cons i s hi _ ih`.

Rewrite using `[Finset.cons_eq_insert, Finset.iInf_insert]`. Conclude with `(hD i).inf ih`. Use `haveI := fun p => (hC p).1`. Use `haveI := fun p => (hC p).2`. Set `χ : O →+* K` to `IsLocalization.lift (M := (RingHom.ker χ₀).primeCompl) (g := χ₀) fun y => Ne.isUnit y.2`.

Establish `hχ₀ : χ.comp (algebraMap R O) = χ₀` using `IsLocalization.lift_comp _`. Establish `hm` using `IsLocalization.AtPrime.map_eq_maximalIdeal (RingHom.ker χ₀) O`. Establish `hker : IsLocalRing.maximalIdeal O ≤ RingHom.ker χ`. Rewrite using `[← hm, Ideal.map_le_iff_le_comap, RingHom.comap_ker, hχ₀]`. Establish `hloc : IsLocalHom χ` using `⟨fun a ha => by`.

Assume the negation of the conclusion as `h`. Conclude with `ha.ne_zero (hker h)⟩`. Establish `horig : Spec.map (CommRingCat.ofHom χ) ≫ t = η[P.A].left`. Rewrite using `[ht, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hχ₀, hχ]`. Establish `H₀` using `IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom χ))`.

Establish `htriv : Triv (((translDiff P.A P.L (𝟙 P.A)).pull π).pull (pullback.fst f (Spec.map (CommRingCat.ofHom χ))))` using `CubeOpen.triv_pull_pull _ _ (triv_of_origin P.A P.L P.isLB _ (pullback.snd _ _) (by`. Rewrite using `[Category.assoc, H.w, H₀.w_assoc, horig]))`. Take `⟨I, ⟨e⟩, hI⟩` from `UU.SecCyclic.cyclic_ideal O Y f _ hM (perfOfBases φ hM hc hD' hφ (Module.finBasis O _) (Module.finBasis O _) (Module.finBasis O _)) hcl hsurj K χ hloc _ _ _ H₀ (CubeOpen.bijective_appTop globalFns_holds P.A P.isAb (H₀.paste_horiz HA)) htriv`. Establish `h₁ : I ≤ IsLocalRing.maximalIdeal O` using `((hI K χ _ _ _ H₀).1 htriv).trans (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top χ))`. Establish `h₂ : IsLocalRing.maximalIdeal O ≤ I`.

Set `x : Over.mk ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ t) ≫ P.A.hom) ⟶ P.A` to `Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ t) rfl`. Establish `Hx` using `isPullback_whiskerRight P.A x`. Set `π'` to `H.lift (x ▷ P.A).left ((fst _ P.A).left ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) (Hx.w.trans (Category.assoc _ _ _).symm)`. Establish `hπ : π' ≫ π = (x ▷ P.A).left` using `H.lift_fst _ _ _`. Establish `H' : IsPullback π' (fst _ P.A).left f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))` using `IsPullback.of_right (by rw [hπ]; exact Hx) (H.lift_snd _ _ _) H`.

Establish `h₃` using `(KerPow.pull_iff _ _ _).1 ((hI _ _ _ _ _ H').2 (Ideal.mk_ker (I := I)).ge)`. Establish `h₄` using `eq_origin_of_triv P.A P.L P.ktriv x (h₃.pull (𝟙 _) fun _ => by`. Rewrite using `[Category.id_comp, hπ])`. Take `⟨ψ, hψ⟩` from `Spec.map_surjective ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ t) ≫ P.A.hom)`. Establish `h₅ : Spec.map (CommRingCat.ofHom (algebraMap R O) ≫ CommRingCat.ofHom (Ideal.Quotient.mk I)) = Spec.map (CommRingCat.ofHom χ₀ ≫ ψ)`.

Rewrite using `[← cancel_mono t₀, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, ← ht, hχ, hψ]`. Conclude with `h₄`. Rewrite using `[← hm, Ideal.map_le_iff_le_comap]`. Introduce `r hr`. Establish `h₆ : Ideal.Quotient.mk I (algebraMap R O r) = ψ.hom (χ₀ r)` using `congrArg (fun q => q.hom r) (Spec.map_injective h₅)`.

Rewrite `h₆` using `[show χ₀ r = 0 from hr, map_zero]`. Conclude with `(Ideal.Quotient.eq_zero_iff_mem (I := I)).1 h₆`. Take `⟨e'⟩` from `coker_dualMap_equiv (Module.finBasis O (C.X 0)) (Module.finBasis O (C.X 1)) (C.d 0 1).hom`. Conclude with `⟨(e'.trans e).trans (Submodule.quotEquivOfEq _ _ (le_antisymm h₁ h₂))⟩`.
-/
theorem coker_dualMap_equiv_residueField_of_origin : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (R : Type) [CommRing R] (t₀ : Spec (CommRingCat.of R) ⟶ P.A.left) (χ₀ : R →+* K) (O : Type) [CommRing O] [IsLocalRing O] [Algebra R O] [(RingHom.ker χ₀).IsPrime] [IsLocalization.AtPrime O (RingHom.ker χ₀)] (t : Spec (CommRingCat.of O) ⟶ P.A.left) (Y : Scheme.{0}) (π : Y ⟶ (P.A ⊗ P.A).left) (f : Y ⟶ Spec (CommRingCat.of O)), IsPullback π f (fst P.A P.A).left t → IsOpenImmersion t₀ → Spec.map (CommRingCat.ofHom χ₀) ≫ t₀ = η[P.A].left → t = Spec.map (CommRingCat.ofHom (algebraMap R O)) ≫ t₀ → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens) (C : CochainComplex (ModuleCat.{0} O) ℕ) (φ : C ⟶ cechLB f ((translDiff P.A P.L (𝟙 P.A)).pull π) D), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (∀ p, Module.Free O (C.X p) ∧ Module.Finite O (C.X p)) → (∀ (R' : Type) [CommRing R'] [Algebra O R'], QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap O R')).mapHomologicalComplex _).map φ)) → Nonempty ((Module.Dual O (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[O] IsLocalRing.ResidueField O) := by
  intro K _ _ P R _ t₀ χ₀ O _ _ _ _ _ t Y π f H ht₀ hχ ht κ _ _ D C φ hD hc hC hφ
  obtain ⟨-, hsep, -, hcl, hsurj, HA⟩ := (AbProj.abelian_projective_baseChange K P).2 O t Y π f H
  have hM : ((translDiff P.A P.L (𝟙 P.A)).pull π).IsLB := LB.isLB_pull (LB.isLB_linComb P.isLB _ _) π
  haveI : Y.IsSeparated := ⟨by
    rw [← terminal.comp_from f]
    infer_instance⟩
  have hD' : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i) := fun s hs => by
    induction hs using Finset.Nonempty.cons_induction with
    | singleton i => simpa using hD i
    | cons i s hi _ ih =>
      rw [Finset.cons_eq_insert, Finset.iInf_insert]
      exact (hD i).inf ih
  haveI := fun p => (hC p).1
  haveI := fun p => (hC p).2
  let χ : O →+* K := IsLocalization.lift (M := (RingHom.ker χ₀).primeCompl) (g := χ₀)
    fun y => Ne.isUnit y.2
  have hχ₀ : χ.comp (algebraMap R O) = χ₀ := IsLocalization.lift_comp _
  have hm := IsLocalization.AtPrime.map_eq_maximalIdeal (RingHom.ker χ₀) O
  have hker : IsLocalRing.maximalIdeal O ≤ RingHom.ker χ := by
    rw [← hm, Ideal.map_le_iff_le_comap, RingHom.comap_ker, hχ₀]
  have hloc : IsLocalHom χ := ⟨fun a ha => by
    by_contra h
    exact ha.ne_zero (hker h)⟩
  have horig : Spec.map (CommRingCat.ofHom χ) ≫ t = η[P.A].left := by
    rw [ht, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hχ₀, hχ]
  have H₀ := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom χ))
  have htriv : Triv (((translDiff P.A P.L (𝟙 P.A)).pull π).pull
      (pullback.fst f (Spec.map (CommRingCat.ofHom χ)))) :=
    CubeOpen.triv_pull_pull _ _ (triv_of_origin P.A P.L P.isLB _ (pullback.snd _ _) (by
      rw [Category.assoc, H.w, H₀.w_assoc, horig]))
  obtain ⟨I, ⟨e⟩, hI⟩ := UU.SecCyclic.cyclic_ideal O Y f _ hM
    (perfOfBases φ hM hc hD' hφ (Module.finBasis O _) (Module.finBasis O _) (Module.finBasis O _))
    hcl hsurj K χ hloc _ _ _ H₀
    (CubeOpen.bijective_appTop globalFns_holds P.A P.isAb (H₀.paste_horiz HA)) htriv
  have h₁ : I ≤ IsLocalRing.maximalIdeal O := ((hI K χ _ _ _ H₀).1 htriv).trans
    (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top χ))
  have h₂ : IsLocalRing.maximalIdeal O ≤ I := by
    let x : Over.mk ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ t) ≫ P.A.hom) ⟶ P.A :=
      Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ t) rfl
    have Hx := isPullback_whiskerRight P.A x
    let π' := H.lift (x ▷ P.A).left
      ((fst _ P.A).left ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      (Hx.w.trans (Category.assoc _ _ _).symm)
    have hπ : π' ≫ π = (x ▷ P.A).left := H.lift_fst _ _ _
    have H' : IsPullback π' (fst _ P.A).left f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
      IsPullback.of_right (by rw [hπ]; exact Hx) (H.lift_snd _ _ _) H
    have h₃ := (KerPow.pull_iff _ _ _).1 ((hI _ _ _ _ _ H').2 (Ideal.mk_ker (I := I)).ge)
    have h₄ := eq_origin_of_triv P.A P.L P.ktriv x (h₃.pull (𝟙 _) fun _ => by
      rw [Category.id_comp, hπ])
    obtain ⟨ψ, hψ⟩ := Spec.map_surjective
      ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ t) ≫ P.A.hom)
    have h₅ : Spec.map (CommRingCat.ofHom (algebraMap R O) ≫ CommRingCat.ofHom (Ideal.Quotient.mk I)) =
        Spec.map (CommRingCat.ofHom χ₀ ≫ ψ) := by
      rw [← cancel_mono t₀, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, ← ht, hχ, hψ]
      exact h₄
    rw [← hm, Ideal.map_le_iff_le_comap]
    intro r hr
    have h₆ : Ideal.Quotient.mk I (algebraMap R O r) = ψ.hom (χ₀ r) :=
      congrArg (fun q => q.hom r) (Spec.map_injective h₅)
    rw [show χ₀ r = 0 from hr, map_zero] at h₆
    exact (Ideal.Quotient.eq_zero_iff_mem (I := I)).1 h₆
  obtain ⟨e'⟩ := coker_dualMap_equiv (Module.finBasis O (C.X 0)) (Module.finBasis O (C.X 1))
    (C.d 0 1).hom
  exact ⟨(e'.trans e).trans (Submodule.quotEquivOfEq _ _ (le_antisymm h₁ h₂))⟩

end GlobalTheory.MumfordLocal
