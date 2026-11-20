import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModificationClosureOfGraphStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianSchemeAway
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open Classical

namespace GlobalTheory.MumGen

/- English proof (translation)
Introduce `R₁ _ _ o Ω _ _ _ _ S ρS M U₀ EE hO Z e M' h hh A₁ φ hcart hlb`. Establish `hr : Set.range M.pt ⊆ (U₀ : Set M.Z)` using `(GlobalTheory.ZH.top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hO.ne)`. Set `x : Sp Ω ⟶ U₀.toScheme` to `IsOpenImmersion.lift U₀.ι M.pt (by rw [Scheme.Opens.range_ι]; exact hr)`. Establish `hx : x ≫ U₀.ι = M.pt` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hy₀ : (spMap e ≫ x) ≫ Z.u₀ = spMap (e.comp S.R.val.toRingHom)`.

Rewrite using `[Category.assoc, Z.u₀_gen x hx, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]`. Establish `w₁ : φ ≫ ρS.P.A.hom = (A₁.A.hom ≫ (spMap e ≫ x)) ≫ Z.u₀`. Rewrite using `[hcart.1.w, Category.assoc, hy₀]`. Set `lam : A₁.A.left ⟶ pullback ρS.P.A.hom Z.u₀` to `pullback.lift φ (A₁.A.hom ≫ (spMap e ≫ x)) w₁`. Establish `hlam : IsGrpPullback A₁.A ((Over.pullback Z.u₀).obj ρS.P.A) (spMap e ≫ x) lam` using `IsGrpPullback.cancel (isGrpPullback_pullback ρS.P.A Z.u₀) (hcart.congr hy₀.symm (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)`.

Establish `hcomp : IsGrpPullback A₁.A Z.G ((spMap e ≫ x) ≫ U₀.ι) (lam ≫ Z.φ)` using `IsGrpPullback.comp hlam Z.cart`. Establish `hyy : (spMap e ≫ x) ≫ U₀.ι = M'.gp ≫ h` using `by rw [Category.assoc, hx, hh]`. Establish `w₂ : (lam ≫ Z.φ) ≫ Z.G.hom = (A₁.A.hom ≫ M'.gp) ≫ h`. Rewrite using `[hcomp.1.w, hyy, Category.assoc]`. Set `α : A₁.A.left ⟶ pullback Z.G.hom h` to `pullback.lift (lam ≫ Z.φ) (A₁.A.hom ≫ M'.gp) w₂`.

Establish `hα : IsGrpPullback A₁.A ((Over.pullback h).obj Z.G) M'.gp α` using `IsGrpPullback.cancel (isGrpPullback_pullback Z.G h) (hcomp.congr hyy (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)`. Use `⟨α, hα, ?_⟩` and prove the remaining obligations. Establish `hP` using `ρS.P.isLB`. Establish `hZ` using `Z.L.isLB`. Establish `i₁ : LBIso (ρS.P.L.pull φ) ((ρS.P.L.pull (pullback.fst ρS.P.A.hom Z.u₀)).pull lam)` using `GlobalTheory.GenSpread.lbIso_pull_pull hP lam (pullback.lift_fst _ _ _).symm`.

Establish `i₂ : LBIso ((ρS.P.L.pull (pullback.fst ρS.P.A.hom Z.u₀)).pull lam) ((Z.L.L.pull Z.φ).pull lam)` using `GlobalTheory.GenSpread.lbIso_pullback (LBIso.symm ⟨Z.w, Z.w_gen⟩) lam`. Establish `i₃ : LBIso ((Z.L.L.pull Z.φ).pull lam) (Z.L.L.pull (lam ≫ Z.φ))` using `LBIso.symm (GlobalTheory.GenSpread.lbIso_pull_pull hZ lam rfl)`. Establish `i₄ : LBIso (Z.L.L.pull (lam ≫ Z.φ)) ((Z.L.L.pull (pullback.fst Z.G.hom h)).pull α)` using `GlobalTheory.GenSpread.lbIso_pull_pull hZ α (pullback.lift_fst _ _ _).symm`. Establish `j₁` using `LBIso.trans A₁.isLB (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) hlb i₁`. Establish `j₂` using `LBIso.trans A₁.isLB (pull_isLB (pull_isLB hP _) _) (pull_isLB (pull_isLB hZ _) _) j₁ i₂`.

Establish `j₃` using `LBIso.trans A₁.isLB (pull_isLB (pull_isLB hZ _) _) (pull_isLB hZ _) j₂ i₃`. Conclude with `LBIso.trans A₁.isLB (pull_isLB hZ _) (pull_isLB (pull_isLB hZ _) _) j₃ i₄`.
-/
theorem genFibre_pullback : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → ∀ (Z : GlobalTheory.ZH.ZHOut ρS M U₀ EE) (e : Ω →+* FractionRing R₁) (M' : Modif R₁) (h : M'.S ⟶ M.Z), M'.gp ≫ h = spMap e ≫ M.pt → ∀ (A₁ : PolAV (Sp (FractionRing R₁))) (φ : A₁.A.left ⟶ ρS.P.A.left), IsGrpPullback A₁.A ρS.P.A (spMap (e.comp S.R.val.toRingHom)) φ → LBIso A₁.L (ρS.P.L.pull φ) → ∃ α : A₁.A.left ⟶ ((Over.pullback h).obj Z.G).left, IsGrpPullback A₁.A ((Over.pullback h).obj Z.G) M'.gp α ∧ LBIso A₁.L ((Z.L.L.pull (pullback.fst Z.G.hom h)).pull α) := by
  intro R₁ _ _ o Ω _ _ _ _ S ρS M U₀ EE hO Z e M' h hh A₁ φ hcart hlb
  have hr : Set.range M.pt ⊆ (U₀ : Set M.Z) := (GlobalTheory.ZH.top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hO.ne)
  let x : Sp Ω ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι M.pt (by rw [Scheme.Opens.range_ι]; exact hr)
  have hx : x ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have hy₀ : (spMap e ≫ x) ≫ Z.u₀ = spMap (e.comp S.R.val.toRingHom) := by
    rw [Category.assoc, Z.u₀_gen x hx, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]
  have w₁ : φ ≫ ρS.P.A.hom = (A₁.A.hom ≫ (spMap e ≫ x)) ≫ Z.u₀ := by
    rw [hcart.1.w, Category.assoc, hy₀]
  let lam : A₁.A.left ⟶ pullback ρS.P.A.hom Z.u₀ := pullback.lift φ (A₁.A.hom ≫ (spMap e ≫ x)) w₁
  have hlam : IsGrpPullback A₁.A ((Over.pullback Z.u₀).obj ρS.P.A) (spMap e ≫ x) lam :=
    IsGrpPullback.cancel (isGrpPullback_pullback ρS.P.A Z.u₀)
      (hcart.congr hy₀.symm (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)
  have hcomp : IsGrpPullback A₁.A Z.G ((spMap e ≫ x) ≫ U₀.ι) (lam ≫ Z.φ) := IsGrpPullback.comp hlam Z.cart
  have hyy : (spMap e ≫ x) ≫ U₀.ι = M'.gp ≫ h := by rw [Category.assoc, hx, hh]
  have w₂ : (lam ≫ Z.φ) ≫ Z.G.hom = (A₁.A.hom ≫ M'.gp) ≫ h := by
    rw [hcomp.1.w, hyy, Category.assoc]
  let α : A₁.A.left ⟶ pullback Z.G.hom h := pullback.lift (lam ≫ Z.φ) (A₁.A.hom ≫ M'.gp) w₂
  have hα : IsGrpPullback A₁.A ((Over.pullback h).obj Z.G) M'.gp α :=
    IsGrpPullback.cancel (isGrpPullback_pullback Z.G h)
      (hcomp.congr hyy (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)
  refine ⟨α, hα, ?_⟩
  have hP := ρS.P.isLB
  have hZ := Z.L.isLB
  have i₁ : LBIso (ρS.P.L.pull φ) ((ρS.P.L.pull (pullback.fst ρS.P.A.hom Z.u₀)).pull lam) :=
    GlobalTheory.GenSpread.lbIso_pull_pull hP lam (pullback.lift_fst _ _ _).symm
  have i₂ : LBIso ((ρS.P.L.pull (pullback.fst ρS.P.A.hom Z.u₀)).pull lam) ((Z.L.L.pull Z.φ).pull lam) :=
    GlobalTheory.GenSpread.lbIso_pullback (LBIso.symm ⟨Z.w, Z.w_gen⟩) lam
  have i₃ : LBIso ((Z.L.L.pull Z.φ).pull lam) (Z.L.L.pull (lam ≫ Z.φ)) :=
    LBIso.symm (GlobalTheory.GenSpread.lbIso_pull_pull hZ lam rfl)
  have i₄ : LBIso (Z.L.L.pull (lam ≫ Z.φ)) ((Z.L.L.pull (pullback.fst Z.G.hom h)).pull α) :=
    GlobalTheory.GenSpread.lbIso_pull_pull hZ α (pullback.lift_fst _ _ _).symm
  have j₁ := LBIso.trans A₁.isLB (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) hlb i₁
  have j₂ := LBIso.trans A₁.isLB (pull_isLB (pull_isLB hP _) _) (pull_isLB (pull_isLB hZ _) _) j₁ i₂
  have j₃ := LBIso.trans A₁.isLB (pull_isLB (pull_isLB hZ _) _) (pull_isLB hZ _) j₂ i₃
  exact LBIso.trans A₁.isLB (pull_isLB hZ _) (pull_isLB (pull_isLB hZ _) _) j₃ i₄

end GlobalTheory.MumGen
