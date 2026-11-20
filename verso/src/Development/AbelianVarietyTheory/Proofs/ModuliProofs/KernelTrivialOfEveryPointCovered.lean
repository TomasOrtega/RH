import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaGroupKernelTrivialOfOpenCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBasicOpenKTrivOfFibreStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.KTrivGlob

/- English proof (translation)
Substitute `hab` using the available equality. Establish `h1 : u = u'` using `Over.OverMorphism.ext hu`. Establish `h2 : v = v'` using `Over.OverMorphism.ext hv`. Substitute `h1 h2` using the available equality. Both sides reduce to the same expression.
-/
private theorem mul_left_congr_of_base_eq {S T : Scheme.{0}} {G : Over S} [GrpObj G] {a b : T ⟶ S} (hab : a = b)
    (u v : Over.mk a ⟶ G) (u' v' : Over.mk b ⟶ G) (hu : u.left = u'.left) (hv : v.left = v'.left) :
    (u * v).left = (u' * v').left := by
  subst hab
  have h1 : u = u' := Over.OverMorphism.ext hu
  have h2 : v = v' := Over.OverMorphism.ext hv
  subst h1 h2
  rfl

/- English proof (translation)
Take `⟨hp₁, hm₁⟩` from `h₁`. Take `⟨hp₂, hm₂⟩` from `h₂`. Establish `hw : φ₂ ≫ G.hom = (G₂.hom ≫ g) ≫ f₁` using `by rw [hp₂.w]; simp`. Use `⟨hp₁.lift φ₂ (G₂.hom ≫ g) hw, hp₁.lift_fst _ _ _, ?_, ?_⟩` and prove the remaining obligations. Use `IsPullback.of_right ?_ (hp₁.lift_snd _ _ _) hp₁` and prove the remaining obligations.

Rewrite using `[hp₁.lift_fst]`. Conclude with `hp₂`. Introduce `T x y x₀ y₀ hx hy`. Apply `hp₁.hom_ext` to reduce the goal to its premises. Establish `ex : (x₀.left ≫ φ₁) ≫ G.hom = (T.hom ≫ g) ≫ f₁`.

Rewrite using `[Category.assoc, hp₁.w, ← Category.assoc, Over.w x₀]`. Both sides reduce to the same expression. Establish `ey : (y₀.left ≫ φ₁) ≫ G.hom = (T.hom ≫ g) ≫ f₁`. Rewrite using `[Category.assoc, hp₁.w, ← Category.assoc, Over.w y₀]`. Both sides reduce to the same expression.

Establish `fx : (x.left ≫ φ₂) ≫ G.hom = T.hom ≫ g ≫ f₁`. Rewrite using `[Category.assoc, hp₂.w, ← Category.assoc, Over.w x]`. Establish `fy : (y.left ≫ φ₂) ≫ G.hom = T.hom ≫ g ≫ f₁`. Rewrite using `[Category.assoc, hp₂.w, ← Category.assoc, Over.w y]`. Establish `A` using `hm₁ (Over.mk (T.hom ≫ g)) x₀ y₀ (Over.homMk (x₀.left ≫ φ₁) ex) (Over.homMk (y₀.left ≫ φ₁) ey) rfl rfl`.

Establish `B` using `hm₂ T x y (Over.homMk (x.left ≫ φ₂) fx) (Over.homMk (y.left ≫ φ₂) fy) rfl rfl`. Establish `C` using `mul_left_congr_of_base_eq (Category.assoc T.hom g f₁) (Over.homMk (x₀.left ≫ φ₁) ex) (Over.homMk (y₀.left ≫ φ₁) ey) (Over.homMk (x.left ≫ φ₂) fx) (Over.homMk (y.left ≫ φ₂) fy) (by simp [hx, hp₁.lift_fst]) (by simp [hy, hp₁.lift_fst])`. Rewrite using `[← A, C, B, Category.assoc, hp₁.lift_fst]`. Rewrite using `[Over.w (x₀ * y₀), Category.assoc, hp₁.lift_snd, ← Category.assoc, Over.w (x * y)]`. Both sides reduce to the same expression.
-/
private theorem exists_isGrpPullback_factor {S S₁ S₂ : Scheme.{0}} {G : Over S} {G₁ : Over S₁} {G₂ : Over S₂}
    [GrpObj G] [GrpObj G₁] [GrpObj G₂] {f₁ : S₁ ⟶ S} {g : S₂ ⟶ S₁} {φ₁ : G₁.left ⟶ G.left}
    {φ₂ : G₂.left ⟶ G.left} (h₁ : IsGrpPullback G₁ G f₁ φ₁) (h₂ : IsGrpPullback G₂ G (g ≫ f₁) φ₂) :
    ∃ ψ : G₂.left ⟶ G₁.left, ψ ≫ φ₁ = φ₂ ∧ IsGrpPullback G₂ G₁ g ψ := by
  obtain ⟨hp₁, hm₁⟩ := h₁
  obtain ⟨hp₂, hm₂⟩ := h₂
  have hw : φ₂ ≫ G.hom = (G₂.hom ≫ g) ≫ f₁ := by rw [hp₂.w]; simp
  refine ⟨hp₁.lift φ₂ (G₂.hom ≫ g) hw, hp₁.lift_fst _ _ _, ?_, ?_⟩
  · refine IsPullback.of_right ?_ (hp₁.lift_snd _ _ _) hp₁
    rw [hp₁.lift_fst]
    exact hp₂
  · intro T x y x₀ y₀ hx hy
    apply hp₁.hom_ext
    · have ex : (x₀.left ≫ φ₁) ≫ G.hom = (T.hom ≫ g) ≫ f₁ := by
        rw [Category.assoc, hp₁.w, ← Category.assoc, Over.w x₀]; rfl
      have ey : (y₀.left ≫ φ₁) ≫ G.hom = (T.hom ≫ g) ≫ f₁ := by
        rw [Category.assoc, hp₁.w, ← Category.assoc, Over.w y₀]; rfl
      have fx : (x.left ≫ φ₂) ≫ G.hom = T.hom ≫ g ≫ f₁ := by
        rw [Category.assoc, hp₂.w, ← Category.assoc, Over.w x]
      have fy : (y.left ≫ φ₂) ≫ G.hom = T.hom ≫ g ≫ f₁ := by
        rw [Category.assoc, hp₂.w, ← Category.assoc, Over.w y]
      have A := hm₁ (Over.mk (T.hom ≫ g)) x₀ y₀ (Over.homMk (x₀.left ≫ φ₁) ex) (Over.homMk (y₀.left ≫ φ₁) ey) rfl rfl
      have B := hm₂ T x y (Over.homMk (x.left ≫ φ₂) fx) (Over.homMk (y.left ≫ φ₂) fy) rfl rfl
      have C := mul_left_congr_of_base_eq (Category.assoc T.hom g f₁) (Over.homMk (x₀.left ≫ φ₁) ex)
        (Over.homMk (y₀.left ≫ φ₁) ey) (Over.homMk (x.left ≫ φ₂) fx) (Over.homMk (y.left ≫ φ₂) fy)
        (by simp [hx, hp₁.lift_fst]) (by simp [hy, hp₁.lift_fst])
      rw [← A, C, B, Category.assoc, hp₁.lift_fst]
    · rw [Over.w (x₀ * y₀), Category.assoc, hp₁.lift_snd, ← Category.assoc, Over.w (x * y)]
      rfl

/- English proof (translation)
Take `⟨hp₁, hm₁⟩` from `h₁`. Take `⟨hp₂, hm₂⟩` from `h₂`. Use `⟨hp₂.paste_horiz hp₁, ?_⟩` and prove the remaining obligations. Introduce `T x y x₀ y₀ hx hy`. Establish `ex : (x.left ≫ ψ) ≫ G₁.hom = T.hom ≫ g`.

Rewrite using `[Category.assoc, hp₂.w, ← Category.assoc, Over.w x]`. Establish `ey : (y.left ≫ ψ) ≫ G₁.hom = T.hom ≫ g`. Rewrite using `[Category.assoc, hp₂.w, ← Category.assoc, Over.w y]`. Establish `ex' : ((x.left ≫ ψ) ≫ φ) ≫ G.hom = (T.hom ≫ g) ≫ f`. Rewrite using `[Category.assoc, hp₁.w, ← Category.assoc, ex]`.

Establish `ey' : ((y.left ≫ ψ) ≫ φ) ≫ G.hom = (T.hom ≫ g) ≫ f`. Rewrite using `[Category.assoc, hp₁.w, ← Category.assoc, ey]`. Establish `A` using `hm₂ T x y (Over.homMk (x.left ≫ ψ) ex) (Over.homMk (y.left ≫ ψ) ey) rfl rfl`. Establish `B` using `hm₁ (Over.mk (T.hom ≫ g)) (Over.homMk (x.left ≫ ψ) ex) (Over.homMk (y.left ≫ ψ) ey) (Over.homMk ((x.left ≫ ψ) ≫ φ) ex') (Over.homMk ((y.left ≫ ψ) ≫ φ) ey') rfl rfl`. Establish `C` using `mul_left_congr_of_base_eq (Category.assoc T.hom g f).symm x₀ y₀ (Over.homMk ((x.left ≫ ψ) ≫ φ) ex') (Over.homMk ((y.left ≫ ψ) ≫ φ) ey') (by simp [hx]) (by simp [hy])`.

Rewrite using `[C, B, A, Category.assoc]`.
-/
private theorem isGrpPullback_comp' {S S₁ S₂ : Scheme.{0}} {G : Over S} {G₁ : Over S₁} {G₂ : Over S₂}
    [GrpObj G] [GrpObj G₁] [GrpObj G₂] {f : S₁ ⟶ S} {g : S₂ ⟶ S₁} {φ : G₁.left ⟶ G.left}
    {ψ : G₂.left ⟶ G₁.left} (h₂ : IsGrpPullback G₂ G₁ g ψ) (h₁ : IsGrpPullback G₁ G f φ) :
    IsGrpPullback G₂ G (g ≫ f) (ψ ≫ φ) := by
  obtain ⟨hp₁, hm₁⟩ := h₁
  obtain ⟨hp₂, hm₂⟩ := h₂
  refine ⟨hp₂.paste_horiz hp₁, ?_⟩
  intro T x y x₀ y₀ hx hy
  have ex : (x.left ≫ ψ) ≫ G₁.hom = T.hom ≫ g := by
    rw [Category.assoc, hp₂.w, ← Category.assoc, Over.w x]
  have ey : (y.left ≫ ψ) ≫ G₁.hom = T.hom ≫ g := by
    rw [Category.assoc, hp₂.w, ← Category.assoc, Over.w y]
  have ex' : ((x.left ≫ ψ) ≫ φ) ≫ G.hom = (T.hom ≫ g) ≫ f := by
    rw [Category.assoc, hp₁.w, ← Category.assoc, ex]
  have ey' : ((y.left ≫ ψ) ≫ φ) ≫ G.hom = (T.hom ≫ g) ≫ f := by
    rw [Category.assoc, hp₁.w, ← Category.assoc, ey]
  have A := hm₂ T x y (Over.homMk (x.left ≫ ψ) ex) (Over.homMk (y.left ≫ ψ) ey) rfl rfl
  have B := hm₁ (Over.mk (T.hom ≫ g)) (Over.homMk (x.left ≫ ψ) ex) (Over.homMk (y.left ≫ ψ) ey)
    (Over.homMk ((x.left ≫ ψ) ≫ φ) ex') (Over.homMk ((y.left ≫ ψ) ≫ φ) ey') rfl rfl
  have C := mul_left_congr_of_base_eq (Category.assoc T.hom g f).symm x₀ y₀ (Over.homMk ((x.left ≫ ψ) ≫ φ) ex')
    (Over.homMk ((y.left ≫ ψ) ≫ φ) ey') (by simp [hx]) (by simp [hy])
  rw [C, B, A, Category.assoc]

/- English proof (translation)
Take `⟨ψ, hψ, hG⟩` from `exists_isGrpPullback_factor h₁ h₂`. Establish `e₃ : LBIso (L₁.pull ψ) (L.pull φ₂)` using `GlobalTheory.GenSpread.lbIso_pull_of_lbIso e₁ ψ hψ.symm`. Establish `hψL : (L₁.pull ψ).IsLB` using `pull_isLB hL₁ ψ`. Establish `e₄ : LBIso L₂ (L₁.pull ψ)` using `LBIso.trans hL₂ (pull_isLB hL φ₂) hψL e₂ (LBIso.symm e₃)`. Take `⟨w, hw⟩` from `e₄`.

Conclude with `kTriv_pull hG hL₁ hL₂ ((isGen_iff w).1 hw) hK`.
-/
theorem kTriv_transfer {S S₁ S₂ : Scheme.{0}} {G : Over S} {G₁ : Over S₁} {G₂ : Over S₂} [GrpObj G] [GrpObj G₁]
    [GrpObj G₂] {f₁ : S₁ ⟶ S} {g : S₂ ⟶ S₁} {φ₁ : G₁.left ⟶ G.left} {φ₂ : G₂.left ⟶ G.left} {L : LB G.left}
    {L₁ : LB G₁.left} {L₂ : LB G₂.left} (hL : L.IsLB) (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB)
    (h₁ : IsGrpPullback G₁ G f₁ φ₁) (h₂ : IsGrpPullback G₂ G (g ≫ f₁) φ₂)
    (e₁ : LBIso L₁ (L.pull φ₁)) (e₂ : LBIso L₂ (L.pull φ₂)) (hK : Out.KTriv G₁ L₁) : Out.KTriv G₂ L₂ := by
  obtain ⟨ψ, hψ, hG⟩ := exists_isGrpPullback_factor h₁ h₂
  have e₃ : LBIso (L₁.pull ψ) (L.pull φ₂) := GlobalTheory.GenSpread.lbIso_pull_of_lbIso e₁ ψ hψ.symm
  have hψL : (L₁.pull ψ).IsLB := pull_isLB hL₁ ψ
  have e₄ : LBIso L₂ (L₁.pull ψ) := LBIso.trans hL₂ (pull_isLB hL φ₂) hψL e₂ (LBIso.symm e₃)
  obtain ⟨w, hw⟩ := e₄
  exact kTriv_pull hG hL₁ hL₂ ((isGen_iff w).1 hw) hK

set_option maxHeartbeats 400000 in
/- English proof (translation)
Take `⟨_, ⟨V, hV, rfl⟩, hfqV, -⟩` from `S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f q)) isOpen_univ`. Use `replace hV : IsAffineOpen V := hV`. Use `haveI : IsNoetherianRing Γ(S, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩`. Establish `hAp : IsGrpPullback ((Over.pullback hV.fromSpec).obj G) G hV.fromSpec (pullback.fst G.hom hV.fromSpec)` using `isGrpPullback_pullback G hV.fromSpec`. Establish `hLA : (L.pull (pullback.fst G.hom hV.fromSpec)).IsLB` using `pull_isLB hL _`.

Take `⟨hAb, hAamp, -⟩` from `GlobalTheory.pol_pull S _ G ((Over.pullback hV.fromSpec).obj G) hV.fromSpec _ L _ hL hLA hG hAp (PolBaseChange.lbIso_refl hLA)`. Establish `hrange : Set.range (S'.fromSpecResidueField q ≫ f) ⊆ Set.range hV.fromSpec`. Introduce and unpack `_ ⟨z, rfl⟩`. Rewrite using `[hV.range_fromSpec]`. Simplify using `using hfqV`.

Take `⟨m, hm⟩ : ∃ m : Spec (S'.residueField q) ⟶ Spec Γ(S, V), m ≫ hV.fromSpec = S'.fromSpecResidueField q ≫ f` from `⟨_, IsOpenImmersion.lift_fac _ _ hrange⟩`. Establish `hx : spMap (Spec.preimage m).hom = m` using `Spec.map_preimage m`. Establish `hpt : spMap (Spec.preimage m).hom ≫ hV.fromSpec = S'.fromSpecResidueField q ≫ f` using `by rw [hx, hm]`. Establish `h₂` using `IsGrpPullback.congr (isGrpPullback_comp' (isGrpPullback_pullback ((Over.pullback hV.fromSpec).obj G) (spMap (Spec.preimage m).hom)) hAp) hpt rfl`. Establish `hK₀` using `kTriv_transfer hL hL' (pull_isLB hLA _) h h₂ e (LBIso.symm (GlobalTheory.GenSpread.lbIso_pull_pull hL _ rfl)) hK`.

Take `⟨r, hr, hsp⟩` from `GlobalTheory.T.exists_basicOpen_kTriv_of_fibre Γ(S, V) ((Over.pullback hV.fromSpec).obj G) (L.pull (pullback.fst G.hom hV.fromSpec)) (S'.residueField q) (Spec.preimage m).hom ((Over.pullback (spMap (Spec.preimage m).hom)).obj ((Over.pullback hV.fromSpec).obj G)) (pullback.fst ((O …`. Establish `hmem : f q ∈ S.basicOpen r`. Set `z : Spec (S'.residueField q)` to `IsLocalRing.closedPoint (S'.residueField q)`. Establish `e1 : (m ≫ hV.fromSpec) z = (S'.fromSpecResidueField q ≫ f) z` using `by rw [hm]`. Simplify using `only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] at e1`.

Rewrite using `[← e1]`. Use `show m z ∈ hV.fromSpec ⁻¹ᵁ S.basicOpen r`. Rewrite using `[hV.fromSpec_preimage_basicOpen]`. Establish `hmz : m z = PrimeSpectrum.comap (Spec.preimage m).hom z` using `(congrArg (fun k : Spec (S'.residueField q) ⟶ Spec Γ(S, V) => k z) (Spec.map_preimage m)).symm`. Rewrite using `[hmz]`.

Use `show r ∉ (PrimeSpectrum.comap (Spec.preimage m).hom z).asIdeal`. Rewrite using `[PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]`. Introduce `hin`. Apply `hr` to reduce the goal to its premises. Establish `: ¬ IsUnit ((Spec.preimage m).hom r)` using `(IsLocalRing.mem_maximalIdeal _).1 hin`.

Simplify using `using this`. Establish `hU` using `hV.basicOpen r`. Use `⟨S.basicOpen r, hmem, ?_⟩` and prove the remaining obligations. Establish `hunit : IsUnit ((S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom r)` using `S.toRingedSpace.isUnit_res_basicOpen r`. Establish `hK'` using `hsp Γ(S, S.basicOpen r) (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom ((Over.pullback (spMap (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom)).obj ((Over.pullback hV.fromSpec).obj G)) (pullback.fst ((Over.pullback hV.fromSpec).obj G).hom (spMap (S.presheaf.map (homOfL …`.

Establish `h₁'` using `isGrpPullback_comp' (isGrpPullback_pullback ((Over.pullback hV.fromSpec).obj G) (spMap (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom)) hAp`. Establish `hιeq : (S.basicOpen r).ι = hU.isoSpec.hom ≫ (spMap (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom ≫ hV.fromSpec)`. Rewrite using `[show spMap (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom ≫ hV.fromSpec = hU.fromSpec from hV.map_fromSpec hU (homOfLE (S.basicOpen_le r)).op, hU.isoSpec_hom_fromSpec]`. Establish `h₂'` using `IsGrpPullback.congr (isGrpPullback_pullback G (S.basicOpen r).ι) hιeq rfl`. Conclude with `kTriv_transfer hL (pull_isLB hLA _) (pull_isLB hL _) h₁' h₂' (LBIso.symm (GlobalTheory.GenSpread.lbIso_pull_pull hL _ rfl)) (PolBaseChange.lbIso_refl (pull_isLB hL _)) hK'`.
-/
private theorem exists_open_kTriv_restrict_of_kTriv_fibre {S S' : Scheme.{0}} [IsLocallyNoetherian S] {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (hG : IsAbelianScheme G) (hA : Out.RelAmple G L) (h : IsGrpPullback G' G f φ) (e : LBIso L' (L.pull φ))
    (hK : Out.KTriv G' L') (q : S') :
    ∃ U : S.Opens, f q ∈ U ∧ Out.KTriv ((Over.pullback U.ι).obj G) (L.pull (pullback.fst G.hom U.ι)) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hfqV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f q)) isOpen_univ
  replace hV : IsAffineOpen V := hV
  haveI : IsNoetherianRing Γ(S, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hAp : IsGrpPullback ((Over.pullback hV.fromSpec).obj G) G hV.fromSpec (pullback.fst G.hom hV.fromSpec) :=
    isGrpPullback_pullback G hV.fromSpec
  have hLA : (L.pull (pullback.fst G.hom hV.fromSpec)).IsLB := pull_isLB hL _
  obtain ⟨hAb, hAamp, -⟩ := GlobalTheory.pol_pull S _ G ((Over.pullback hV.fromSpec).obj G) hV.fromSpec _ L _ hL hLA hG hAp
    (PolBaseChange.lbIso_refl hLA)
  have hrange : Set.range (S'.fromSpecResidueField q ≫ f) ⊆ Set.range hV.fromSpec := by
    rintro _ ⟨z, rfl⟩
    rw [hV.range_fromSpec]
    simpa using hfqV
  obtain ⟨m, hm⟩ : ∃ m : Spec (S'.residueField q) ⟶ Spec Γ(S, V),
      m ≫ hV.fromSpec = S'.fromSpecResidueField q ≫ f :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hrange⟩
  have hx : spMap (Spec.preimage m).hom = m := Spec.map_preimage m
  have hpt : spMap (Spec.preimage m).hom ≫ hV.fromSpec = S'.fromSpecResidueField q ≫ f := by rw [hx, hm]
  have h₂ := IsGrpPullback.congr (isGrpPullback_comp'
    (isGrpPullback_pullback ((Over.pullback hV.fromSpec).obj G) (spMap (Spec.preimage m).hom)) hAp) hpt rfl
  have hK₀ := kTriv_transfer hL hL' (pull_isLB hLA _) h h₂ e
    (LBIso.symm (GlobalTheory.GenSpread.lbIso_pull_pull hL _ rfl)) hK
  obtain ⟨r, hr, hsp⟩ := GlobalTheory.T.exists_basicOpen_kTriv_of_fibre Γ(S, V) ((Over.pullback hV.fromSpec).obj G)
    (L.pull (pullback.fst G.hom hV.fromSpec)) (S'.residueField q) (Spec.preimage m).hom
    ((Over.pullback (spMap (Spec.preimage m).hom)).obj ((Over.pullback hV.fromSpec).obj G))
    (pullback.fst ((Over.pullback hV.fromSpec).obj G).hom (spMap (Spec.preimage m).hom)) hAb hLA (hAamp hA)
    (isGrpPullback_pullback ((Over.pullback hV.fromSpec).obj G) (spMap (Spec.preimage m).hom)) hK₀
  have hmem : f q ∈ S.basicOpen r := by
    let z : Spec (S'.residueField q) := IsLocalRing.closedPoint (S'.residueField q)
    have e1 : (m ≫ hV.fromSpec) z = (S'.fromSpecResidueField q ≫ f) z := by rw [hm]
    simp only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] at e1
    rw [← e1]
    show m z ∈ hV.fromSpec ⁻¹ᵁ S.basicOpen r
    rw [hV.fromSpec_preimage_basicOpen]
    have hmz : m z = PrimeSpectrum.comap (Spec.preimage m).hom z :=
      (congrArg (fun k : Spec (S'.residueField q) ⟶ Spec Γ(S, V) => k z) (Spec.map_preimage m)).symm
    rw [hmz]
    show r ∉ (PrimeSpectrum.comap (Spec.preimage m).hom z).asIdeal
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    intro hin
    apply hr
    have : ¬ IsUnit ((Spec.preimage m).hom r) := (IsLocalRing.mem_maximalIdeal _).1 hin
    simpa using this
  have hU := hV.basicOpen r
  refine ⟨S.basicOpen r, hmem, ?_⟩
  have hunit : IsUnit ((S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom r) :=
    S.toRingedSpace.isUnit_res_basicOpen r
  have hK' := hsp Γ(S, S.basicOpen r) (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom
    ((Over.pullback (spMap (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom)).obj
      ((Over.pullback hV.fromSpec).obj G))
    (pullback.fst ((Over.pullback hV.fromSpec).obj G).hom (spMap (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom))
    hunit (isGrpPullback_pullback ((Over.pullback hV.fromSpec).obj G) (spMap (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom))
  have h₁' := isGrpPullback_comp' (isGrpPullback_pullback ((Over.pullback hV.fromSpec).obj G)
    (spMap (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom)) hAp
  have hιeq : (S.basicOpen r).ι = hU.isoSpec.hom ≫
      (spMap (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom ≫ hV.fromSpec) := by
    rw [show spMap (S.presheaf.map (homOfLE (S.basicOpen_le r)).op).hom ≫ hV.fromSpec = hU.fromSpec from
      hV.map_fromSpec hU (homOfLE (S.basicOpen_le r)).op, hU.isoSpec_hom_fromSpec]
  have h₂' := IsGrpPullback.congr (isGrpPullback_pullback G (S.basicOpen r).ι) hιeq rfl
  exact kTriv_transfer hL (pull_isLB hLA _) (pull_isLB hL _) h₁' h₂'
    (LBIso.symm (GlobalTheory.GenSpread.lbIso_pull_pull hL _ rfl)) (PolBaseChange.lbIso_refl (pull_isLB hL _)) hK'

/- English proof (translation)
The claim follows from `exists_open_kTriv_restrict_of_kTriv_fibre hL hL' hG hA h e hK q`.
-/
theorem exists_open {S S' : Scheme.{0}} [IsLocallyNoetherian S] {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (hG : IsAbelianScheme G) (hA : Out.RelAmple G L) (h : IsGrpPullback G' G f φ) (e : LBIso L' (L.pull φ))
    (hK : Out.KTriv G' L') (q : S') :
    ∃ U : S.Opens, f q ∈ U ∧ Out.KTriv ((Over.pullback U.ι).obj G) (L.pull (pullback.fst G.hom U.ι)) := exists_open_kTriv_restrict_of_kTriv_fibre hL hL' hG hA h e hK q

/- English proof (translation)
Introduce `hLaws E _ _ _ H S _ t hP hA h`. Use `haveI : IsProper t.G.hom := hP`. Establish `hAb : IsAbelianScheme t.G` using `AbelianSchemeGerms.isAbelianScheme_of_proper t.G t.semi`. Establish `hL : t.PP.L.IsLB` using `t.PP.isLB`. Establish `hU : ∀ p : S, ∃ U : S.Opens, p ∈ U ∧ Out.KTriv ((Over.pullback U.ι).obj t.G) (t.PP.L.pull (pullback.fst t.G.hom U.ι))`.

Introduce `p`. Take `⟨S', f, t', ⟨cm, cart, -, -, lin⟩, ⟨q, rfl⟩, hk⟩` from `h p`. Take `⟨w, hw, -⟩` from `lin`. Conclude with `exists_open hL t'.PP.isLB hAb hA cart ⟨w, hw⟩ hk q`. Use `choose U hpU hKU using hU`.

Conclude with `GlobalTheory.CoverGlue.kTriv_of_cover S S U t.G (fun p => (Over.pullback (U p).ι).obj t.G) (fun p => pullback.fst t.G.hom (U p).ι) (eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hpU x⟩) (fun p => isGrpPullback_pullback t.G (U p).ι) t.PP.L (fun p => t.PP.L.pull (pu …`.
-/
theorem kTriv_of_forall_point : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → (∀ p : S, ∃ (S' : Scheme.{0}) (f : S' ⟶ S) (t' : SAB H S') (_ : SABMap t' t f), p ∈ Set.range f ∧ Out.KTriv t'.G t'.PP.L) → Out.KTriv t.G t.PP.L := by
  intro hLaws E _ _ _ H S _ t hP hA h
  haveI : IsProper t.G.hom := hP
  have hAb : IsAbelianScheme t.G := AbelianSchemeGerms.isAbelianScheme_of_proper t.G t.semi
  have hL : t.PP.L.IsLB := t.PP.isLB
  have hU : ∀ p : S, ∃ U : S.Opens, p ∈ U ∧
      Out.KTriv ((Over.pullback U.ι).obj t.G) (t.PP.L.pull (pullback.fst t.G.hom U.ι)) := by
    intro p
    obtain ⟨S', f, t', ⟨cm, cart, -, -, lin⟩, ⟨q, rfl⟩, hk⟩ := h p
    obtain ⟨w, hw, -⟩ := lin
    exact exists_open hL t'.PP.isLB hAb hA cart ⟨w, hw⟩ hk q
  choose U hpU hKU using hU
  exact GlobalTheory.CoverGlue.kTriv_of_cover S S U t.G (fun p => (Over.pullback (U p).ι).obj t.G)
    (fun p => pullback.fst t.G.hom (U p).ι)
    (eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hpU x⟩)
    (fun p => isGrpPullback_pullback t.G (U p).ι) t.PP.L (fun p => t.PP.L.pull (pullback.fst t.G.hom (U p).ι))
    hL (fun p => pull_isLB hL _) (fun p => PolBaseChange.lbIso_refl (pull_isLB hL _)) hAb
    (fun p => (GlobalTheory.pol_pull S (U p).toScheme t.G _ (U p).ι _ t.PP.L _ hL (pull_isLB hL _) hAb
      (isGrpPullback_pullback t.G (U p).ι) (PolBaseChange.lbIso_refl (pull_isLB hL _))).1) hKU

end GlobalTheory.KTrivGlob
