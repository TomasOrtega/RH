import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationPullbackCompatibleIso
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionNonzeroClosedFibreGeneratesExpansionZeroStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisationGenericFibreCartesianToModelBundleStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormalisedThetaConstantsPrimitiveIntegralOneUnitStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Ex.OnModel

/- English proof (translation)
Take `rfl : (fun k => h ≫ φ k) = φ'` from `funext e`. Take `⟨j, hj⟩` from `TopologicalSpace.Opens.mem_iSup.1 hy`. Use `TopologicalSpace.Opens.mem_iSup.2 ⟨j, ?_⟩` and prove the remaining obligations. Establish `hle` using `VVRank.wchart_le_of_eq (L := L) h e j`. Establish `q` using `Y'.basicOpen_res ((h.app _).hom (s.f j)) (homOfLE hle).op`.

Use `q.ge ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 (Y.basicOpen_le _ hj) k, ?_⟩` and prove the remaining obligations. Conclude with `(Scheme.preimage_basicOpen h (s.f j)).le hj`.
-/
theorem mem_nonzeroLocus_pullTo {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K → (Y' ⟶ X)} (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (e : ∀ k, h ≫ φ k = φ' k) {y : Y'}
    (hy : h y ∈ nonzeroLocus s) : y ∈ nonzeroLocus (VVRank.pullTo s h e) := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨j, ?_⟩
  have hle := VVRank.wchart_le_of_eq (L := L) h e j
  have q := Y'.basicOpen_res ((h.app _).hom (s.f j)) (homOfLE hle).op
  refine q.ge ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 (Y.basicOpen_le _ hj) k, ?_⟩
  exact (Scheme.preimage_basicOpen h (s.f j)).le hj

section Base
variable {S : Scheme.{0}} (G : Over S)

def toBase : G.left ⟶ (Over.mk (𝟙 S) ⊗ G).left :=
  (lift (Over.homMk G.hom (Category.comp_id _) : G ⟶ Over.mk (𝟙 S)) (𝟙 G)).left

/- English proof (translation)
Rewrite using `[toBase, ← Over.comp_left, lift_snd, Over.id_left]`.
-/
theorem toBase_snd : toBase G ≫ (snd (Over.mk (𝟙 S)) G).left = 𝟙 _ := by
  rw [toBase, ← Over.comp_left, lift_snd, Over.id_left]

/- English proof (translation)
The claim follows from `(pullback.condition (f := 𝟙 S) (g := G.hom)).symm.trans (Category.comp_id _)`.
-/
theorem snd_hom : (snd (Over.mk (𝟙 S)) G).left ≫ G.hom = (fst (Over.mk (𝟙 S)) G).left :=
  (pullback.condition (f := 𝟙 S) (g := G.hom)).symm.trans (Category.comp_id _)

/- English proof (translation)
Establish `a : toBase G ≫ (fst (Over.mk (𝟙 S)) G).left = G.hom`. Rewrite using `[toBase, ← Over.comp_left, lift_fst]`. Both sides reduce to the same expression. Use `psi_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, a, Category.assoc]`.

Conclude with `congrArg (r ≫ ·) (snd_hom G)`. Rewrite using `[Category.assoc, toBase_snd, Category.comp_id]`.
-/
theorem comp_toBase {Z : Scheme.{0}} (r : Z ⟶ (Over.mk (𝟙 S) ⊗ G).left) :
    (r ≫ (snd (Over.mk (𝟙 S)) G).left) ≫ toBase G = r := by
  have a : toBase G ≫ (fst (Over.mk (𝟙 S)) G).left = G.hom := by
    rw [toBase, ← Over.comp_left, lift_fst]; rfl
  refine psi_ext ?_ ?_
  · rw [Category.assoc, a, Category.assoc]
    exact congrArg (r ≫ ·) (snd_hom G)
  · rw [Category.assoc, toBase_snd, Category.comp_id]

variable [GrpObj G] {L : LB G.left} {k : ℕ}

def down (σ : LB.Sec (LPow G L (k : ℤ) (Over.mk (𝟙 S)))) : H0 L k :=
  VVRank.pullTo (φ := fun _ : Fin 1 => (snd (Over.mk (𝟙 S)) G).left) (ε := fun _ => (k : ℤ)) σ (toBase G)
    fun _ => toBase_snd G

/- English proof (translation)
Use `(VVRank.sval_pullTo _ _ _ _ z hJ).trans ?_` and prove the remaining obligations. Rewrite using `[comp_toBase]`.
-/
theorem sval_down (σ : LB.Sec (LPow G L (k : ℤ) (Over.mk (𝟙 S)))) {Z : Scheme.{0}} (r : Z ⟶ (Over.mk (𝟙 S) ⊗ G).left)
    (z : Z) {J} (hJ : Good L z J) :
    sval (down G σ) (r ≫ (snd (Over.mk (𝟙 S)) G).left) z J = VVRank.sv G σ r z J := by
  refine (VVRank.sval_pullTo _ _ _ _ z hJ).trans ?_
  rw [comp_toBase]

/- English proof (translation)
Use `mem_nonzeroLocus_pullTo _ _ _ ?_` and prove the remaining obligations. Establish `e` using `comp_toBase G (𝟙 _)`. Rewrite `e` using `[Category.id_comp]`. Rewrite using `[← Scheme.Hom.comp_apply, e]`. Conclude with `hg`.
-/
theorem mem_nonzeroLocus_down (σ : LB.Sec (LPow G L (k : ℤ) (Over.mk (𝟙 S)))) {g : (Over.mk (𝟙 S) ⊗ G).left}
    (hg : g ∈ nonzeroLocus σ) : (snd (Over.mk (𝟙 S)) G).left g ∈ nonzeroLocus (down G σ) := by
  refine mem_nonzeroLocus_pullTo _ _ _ ?_
  have e := comp_toBase G (𝟙 _)
  rw [Category.id_comp] at e
  rw [← Scheme.Hom.comp_apply, e]
  exact hg

end Base

/- English proof (translation)
Introduce `s`. Take `⟨b, hb⟩` from `h (down G s)`. Set `c : Γ((Over.mk (𝟙 (Sp V))).left, ⊤)` to `(Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom b`. Establish `key : SecM.ofSec G s = c • SecM.ofSec G σ` using `ThetaAct.sv_ext hL fun y J hJ => by`. Use `Eq.trans ?_ (ThetaAct.sv_smul _ _ _ _ hJ).symm` and prove the remaining obligations.

Use `(sval_down G s (𝟙 _) y hJ).symm.trans (Eq.trans ?_ (congrArg (_ * ·) (sval_down G σ (𝟙 _) y hJ)))` and prove the remaining obligations. Establish `hz` using `hJ.mem (fun _ : Fin 1 => 𝟙 G.left) (𝟙 _ ≫ (snd (Over.mk (𝟙 (Sp V))) G).left)`. Use `(congrArg (gs _ y _) (hb _)).trans ((gs_mul _ y _ hz _ _).trans (congrArg (· * _) ?_))` and prove the remaining obligations. Use `(gs_res _ y le_top hz _).trans ((gs_pull _ G.hom y ⊤ trivial _).trans ?_)` and prove the remaining obligations. Rewrite using `[Category.assoc, snd_hom]`.

Conclude with `⟨c, fun j => congrArg (fun q => q.1 j) key⟩`.
-/
theorem isGenSec_of_down {V : Type} [CommRing V] (G : Over (Sp V)) [GrpObj G] {L : LB G.left} (hL : L.IsLB) {k : ℕ}
    (σ : LB.Sec (LPow G L (k : ℤ) (Over.mk (𝟙 (Sp V))))) (h : ∀ s : H0 L k, ∃ b : V, SecIsMul G.hom b s (down G σ)) :
    IsGenSec G L (k : ℤ) σ := by
  intro s
  obtain ⟨b, hb⟩ := h (down G s)
  let c : Γ((Over.mk (𝟙 (Sp V))).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom b
  have key : SecM.ofSec G s = c • SecM.ofSec G σ := ThetaAct.sv_ext hL fun y J hJ => by
    refine Eq.trans ?_ (ThetaAct.sv_smul _ _ _ _ hJ).symm
    refine (sval_down G s (𝟙 _) y hJ).symm.trans (Eq.trans ?_ (congrArg (_ * ·) (sval_down G σ (𝟙 _) y hJ)))
    have hz := hJ.mem (fun _ : Fin 1 => 𝟙 G.left) (𝟙 _ ≫ (snd (Over.mk (𝟙 (Sp V))) G).left)
    refine (congrArg (gs _ y _) (hb _)).trans ((gs_mul _ y _ hz _ _).trans (congrArg (· * _) ?_))
    refine (gs_res _ y le_top hz _).trans ((gs_pull _ G.hom y ⊤ trivial _).trans ?_)
    rw [Category.assoc, snd_hom]
  exact ⟨c, fun j => congrArg (fun q => q.1 j) key⟩

/- English proof (translation)
Introduce `hHV V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U σ hσ`. Establish `hL` using `U.LG.isLB`. Use `A.isAb.comm` as an intermediate fact. Take `⟨g, hg, hg'⟩` from `hσ`. Take `⟨hgen, hexp⟩` from `GlobalTheory.T.section_nonzero_closedFibre_generates_expansion_zero hHV.1 V hc ϖ hϖ D Q hQ F v hv A G hG U (down G σ) ⟨_, by rw [← Scheme.Hom.comp_apply, snd_hom]; exact hg, mem_nonzeroLocus_down G σ hg'⟩`.

Use `⟨isGenSec_of_down G hL σ hgen, fun m h₁ h₂ h₃ ξ => ?_⟩` and prove the remaining obligations. Take `⟨w₀, ρ, w, hp, hN, hw, hr, H⟩` from `GlobalTheory.T.uniformisation_generic_fibre_cartesian_to_model_bundleIso V _ D A G U.toUnifPre`. Establish `hτ : 𝟙 (Sp F) ≫ (Over.mk (jFK (R` using `V) F ≫ jK V)).hom = (TFK (R := V) F).hom ≫ jK V := Category.id_comp _`. Take `⟨th, hth⟩` from `exists_secRel hp (T := TFK (R := V) F) (T₀ := Over.mk (jFK (R := V) F ≫ jK V)) (𝟙 (Sp F)) hτ hw hL A.isLB (VVRank.pullS G _ ξ σ)`. Take `⟨σ', hσ', hE⟩` from `H F 1 (down G σ) th fun Z r z J J' hJ hJ' => by`.

Use `Eq.trans ?_ (hth Z r z J J' hJ hJ')` and prove the remaining obligations. Use `Eq.trans ?_ ((sval_down G σ _ z hJ).trans (VVRank.sv_pullS G _ ξ σ _ z hJ).symm)` and prove the remaining obligations. Rewrite using `[Category.assoc, VVRank.whisker_snd_left, Category.assoc, psi_snd']`. Take `⟨ϑ, hϑ, hP⟩` from `hexp σ' hσ'`. Take `⟨k₁, x, c, k₂, k₃⟩` from `GlobalTheory.T.normalisedThetaConstants_primitive_integral_one_unit hHV V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN th ϑ (hE ϑ hϑ) hP m h₁ h₂ h₃`.

Establish `hx : ∀ x : TFK (R` using `V) F ⟶ A.A, 𝟙 (Sp F) ≫ (pushHom hp (TFK (R := V) F) x).left = x.left ≫ _ := fun x => Category.id_comp _`. Use `⟨fun x₀ c hc => ?_, pushHom hp (TFK (R := V) F) x, c, ?_, k₃⟩` and prove the remaining obligations. Set `y : TFK (R` to `V) F ⟶ A.A := Over.homMk (hp.1.lift x₀.left (jFK (R := V) F) (Over.w x₀)) (hp.1.lift_snd _ _ _)`. Establish `hy : 𝟙 (Sp F) ≫ x₀.left = y.left ≫ _` using `(Category.id_comp _).trans (hp.1.lift_fst _ _ _).symm`. Establish `hn : y ^ (m ^ 2) = 1`.

Use `Over.OverMorphism.ext (hp.1.hom_ext ?_ (by rw [Over.w, Over.w]))` and prove the remaining obligations. Use `(over_pow hp (T₀ := Over.mk (jFK (R := V) F ≫ jK V)) _ hτ hy _).symm.trans ?_` and prove the remaining obligations. Rewrite using `[hc.1]`. Conclude with `over_one hp _ hτ`. Conclude with `k₁ y c (ThG.move hp _ hτ hw hL A.isLB hr hy hn hth hc)`.

Establish `: IsIso (X` using `(TFK (R := V) F).left) (Y := (Over.mk (jFK (R := V) F ≫ jK V)).left) (𝟙 (Sp F)) := IsIso.id _`. Establish `q` using `ThG.up hp _ hτ hw hL A.isLB hr (hx x) (by rw [← map_pow, k₂.1, map_one]) hth k₂`. Establish `e : inv (X` using `(TFK (R := V) F).left) (Y := (Over.mk (jFK (R := V) F ≫ jK V)).left) (𝟙 (Sp F)) = 𝟙 (Sp F) := IsIso.inv_eq_of_hom_inv_id (Category.id_comp _)`. Rewrite `q` using `[e]`. Conclude with `q`.
-/
theorem theta_on_model : HV → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ σ : LB.Sec (LPow G U.LG.L ((1 : ℕ) : ℤ) (Over.mk (𝟙 (Sp V)))), NZ G U.LG.L (𝟙 (Sp V)) σ → IsGenSec G U.LG.L ((1 : ℕ) : ℤ) σ ∧ ∀ m : ℕ, Odd m → IsUnit (m : V) → 3 ≤ m → ∀ (ξ : Over.mk (jFK (R := V) F ≫ jK V) ⟶ Over.mk (𝟙 (Sp V))), (∀ x (c : F), ThG G U.LG.L U.LG.rig m (VVRank.pullS G _ ξ σ) x (fnOf c) → 0 ≤ v c) ∧ ∃ x, ∃ c : F, ThG G U.LG.L U.LG.rig m (VVRank.pullS G _ ξ σ) x (fnOf c) ∧ v c = 0 := by
  intro hHV V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U σ hσ
  have hL := U.LG.isLB
  have := A.isAb.comm
  obtain ⟨g, hg, hg'⟩ := hσ
  obtain ⟨hgen, hexp⟩ := GlobalTheory.T.section_nonzero_closedFibre_generates_expansion_zero hHV.1 V hc ϖ hϖ D Q hQ F v hv A G hG U (down G σ)
    ⟨_, by rw [← Scheme.Hom.comp_apply, snd_hom]; exact hg, mem_nonzeroLocus_down G σ hg'⟩
  refine ⟨isGenSec_of_down G hL σ hgen, fun m h₁ h₂ h₃ ξ => ?_⟩
  obtain ⟨w₀, ρ, w, hp, hN, hw, hr, H⟩ := GlobalTheory.T.uniformisation_generic_fibre_cartesian_to_model_bundleIso V _ D A G U.toUnifPre
  have hτ : 𝟙 (Sp F) ≫ (Over.mk (jFK (R := V) F ≫ jK V)).hom = (TFK (R := V) F).hom ≫ jK V := Category.id_comp _
  obtain ⟨th, hth⟩ := exists_secRel hp (T := TFK (R := V) F) (T₀ := Over.mk (jFK (R := V) F ≫ jK V)) (𝟙 (Sp F)) hτ hw hL
    A.isLB (VVRank.pullS G _ ξ σ)
  obtain ⟨σ', hσ', hE⟩ := H F 1 (down G σ) th fun Z r z J J' hJ hJ' => by
    refine Eq.trans ?_ (hth Z r z J J' hJ hJ')
    refine Eq.trans ?_ ((sval_down G σ _ z hJ).trans (VVRank.sv_pullS G _ ξ σ _ z hJ).symm)
    rw [Category.assoc, VVRank.whisker_snd_left, Category.assoc, psi_snd']
  obtain ⟨ϑ, hϑ, hP⟩ := hexp σ' hσ'
  obtain ⟨k₁, x, c, k₂, k₃⟩ := GlobalTheory.T.normalisedThetaConstants_primitive_integral_one_unit hHV V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN th ϑ (hE ϑ hϑ) hP m h₁ h₂ h₃
  have hx : ∀ x : TFK (R := V) F ⟶ A.A, 𝟙 (Sp F) ≫ (pushHom hp (TFK (R := V) F) x).left = x.left ≫ _ :=
    fun x => Category.id_comp _
  refine ⟨fun x₀ c hc => ?_, pushHom hp (TFK (R := V) F) x, c, ?_, k₃⟩
  · let y : TFK (R := V) F ⟶ A.A := Over.homMk (hp.1.lift x₀.left (jFK (R := V) F) (Over.w x₀)) (hp.1.lift_snd _ _ _)
    have hy : 𝟙 (Sp F) ≫ x₀.left = y.left ≫ _ := (Category.id_comp _).trans (hp.1.lift_fst _ _ _).symm
    have hn : y ^ (m ^ 2) = 1 := by
      refine Over.OverMorphism.ext (hp.1.hom_ext ?_ (by rw [Over.w, Over.w]))
      refine (over_pow hp (T₀ := Over.mk (jFK (R := V) F ≫ jK V)) _ hτ hy _).symm.trans ?_
      rw [hc.1]
      exact over_one hp _ hτ
    exact k₁ y c (ThG.move hp _ hτ hw hL A.isLB hr hy hn hth hc)
  · have : IsIso (X := (TFK (R := V) F).left) (Y := (Over.mk (jFK (R := V) F ≫ jK V)).left) (𝟙 (Sp F)) := IsIso.id _
    have q := ThG.up hp _ hτ hw hL A.isLB hr (hx x) (by rw [← map_pow, k₂.1, map_one]) hth k₂
    have e : inv (X := (TFK (R := V) F).left) (Y := (Over.mk (jFK (R := V) F ≫ jK V)).left) (𝟙 (Sp F)) = 𝟙 (Sp F) :=
      IsIso.inv_eq_of_hom_inv_id (Category.id_comp _)
    rw [e] at q
    exact q

end GlobalTheory.Ex.OnModel
end
