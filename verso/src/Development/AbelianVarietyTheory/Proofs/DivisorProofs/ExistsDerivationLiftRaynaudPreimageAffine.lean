import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothRayQuotient
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDerivationExtendOfFormallySmooth
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LiftDer

/- English proof (translation)
Set `g : R →+* Γ(X, U)` to `(f.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom`. Establish `hg : g.Smooth`. Use `RingHom.Smooth.comp (RingHom.Smooth.of_bijective ?_) ?_` and prove the remaining obligations. Conclude with `((Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm).bijective`. Conclude with `HasRingHomProperty.appLE @Smooth f inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _`.

Use `letI : Algebra R Γ(X, U) := g.toAlgebra`. Use `haveI : Algebra.FormallySmooth R Γ(X, U) := hg.formallySmooth`. Take `⟨d, hadd, hmul, hc⟩` from `GlobalTheory.KS.exists_derivation_extend_of_formallySmooth R Γ(X, U) Γ(X, U) (RingHom.id _) (fun r => g (D r)) (fun a b => by simp) (fun a b => by`. Simplify using `only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, RingHom.id_apply]`. Rewrite using `[RingHom.algebraMap_toAlgebra])`.

Conclude with `⟨d, hadd, hmul, fun r => hc r⟩`.
-/
theorem exists_lift_of_smooth (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) [Smooth f]
    (U : X.Opens) (hU : IsAffineOpen U) (D : Derivation ℤ R R) :
    ∃ δ : Γ(X, U) → Γ(X, U), (∀ a b, δ (a + b) = δ a + δ b) ∧ (∀ a b, δ (a * b) = a * δ b + b * δ a) ∧
      ∀ r, δ (constFn f U r) = constFn f U (D r) := by
  let g : R →+* Γ(X, U) :=
    (f.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have hg : g.Smooth := by
    refine RingHom.Smooth.comp (RingHom.Smooth.of_bijective ?_) ?_
    · exact ((Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm).bijective
    · exact HasRingHomProperty.appLE @Smooth f inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
  letI : Algebra R Γ(X, U) := g.toAlgebra
  haveI : Algebra.FormallySmooth R Γ(X, U) := hg.formallySmooth
  obtain ⟨d, hadd, hmul, hc⟩ := GlobalTheory.KS.exists_derivation_extend_of_formallySmooth R Γ(X, U) Γ(X, U)
    (RingHom.id _) (fun r => g (D r)) (fun a b => by simp) (fun a b => by
      simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, RingHom.id_apply]
      rw [RingHom.algebraMap_toAlgebra])
  exact ⟨d, hadd, hmul, fun r => hc r⟩

/- English proof (translation)
Take `⟨c⟩` from `GlobalTheory.TorusModel.nonempty_gtCoord GlobalTheory.allSixLaws.1.globalFns Y.isGt ⊥ 0`. Establish `hc : IsAffineHom c.q.left` using `c.q_affine`. Set `F` to `fstG (⊥ : Ideal R) 0 Y.H`. Set `j` to `inv F.left`. Establish `hF : F.left ≫ Y.H.hom = (thickObj R ⊥ 0 Y.H).hom ≫ thick R ⊥ 0` using `Over.w F`.

Set `ξ` to `Y.Φ Y.H (𝟙 _)`. Take `⟨x, hx⟩` from `GlobalTheory.TorusCoord.exists_point c (T := Y.H) (Y.H.hom ≫ inv (thick R ⊥ 0)) (by simp) ξ`. Take `⟨ξ', hξ'⟩` from `GlobalTheory.TorusCoord.exists_isPointOf c (T := Y.H) j (by`. Rewrite using `[← hF]`. Conclude with `IsIso.inv_hom_id_assoc _ _)`.

Set `b : Y.H ⟶ Y.H` to `(Y.Φ Y.H).symm ξ'`. Establish `hb : Y.Φ Y.H b = ξ'` using `Equiv.apply_symm_apply _ _`. Set `a` to `x ≫ F.left`. Establish `ha : a ≫ Y.H.hom = Y.H.hom`. Rewrite using `[Category.assoc, hF]`.

Conclude with `GlobalTheory.TorusCoord.IsPointOf.comp_hom c hx`. Set `a' : Y.H ⟶ Y.H` to `Over.homMk a ha`. Establish `haj : a ≫ j = x` using `by simp [a, j]`. Establish `e1 : b.left ≫ x = j`. Establish `h1 : GtPt.IsPull b.left ξ (Y.Φ Y.H (b ≫ 𝟙 _))` using `Y.rep.1 Y.H Y.H b (𝟙 _)`.

Rewrite `h1` using `[Category.comp_id, hb]`. Conclude with `(GlobalTheory.TorusCoord.IsPointOf.pull c hx h1).unique_left c hξ'`. Establish `e1' : b.left ≫ a = 𝟙 _`. Rewrite using `[← Category.assoc, e1]`. Simplify using `[j]`.

Establish `e2 : a' ≫ b = 𝟙 _`. Establish `h2 : GtPt.IsPull a (Y.Φ Y.H b) (Y.Φ Y.H (a' ≫ b))` using `Y.rep.1 Y.H Y.H a' b`. Rewrite `h2` using `[hb]`. Establish `h3` using `GlobalTheory.TorusCoord.IsPointOf.pull c hξ' h2`. Rewrite `h3` using `[haj]`.

Conclude with `(Y.Φ Y.H).injective (h3.unique_right c hx)`. Establish `e2' : a ≫ b.left = 𝟙 _` using `congrArg (·.left) e2`. Establish `: IsIso a` using `⟨⟨b.left, e2', e1'⟩⟩`. Establish `hq : Y.q.left = a ≫ j ≫ c.q.left ≫ pullback.fst Q.P.A.hom (thick R ⊥ 0)`. Rewrite using `[← Category.assoc a j, haj, ← GlobalTheory.TorusCoord.pG_left]`.

Conclude with `hx.1`. Rewrite using `[hq]`. Use `infer_instance`.
-/
theorem isAffineHom_q {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) : IsAffineHom Y.q.left := by
  obtain ⟨c⟩ := GlobalTheory.TorusModel.nonempty_gtCoord GlobalTheory.allSixLaws.1.globalFns Y.isGt ⊥ 0
  have hc : IsAffineHom c.q.left := c.q_affine
  let F := fstG (⊥ : Ideal R) 0 Y.H
  let j := inv F.left
  have hF : F.left ≫ Y.H.hom = (thickObj R ⊥ 0 Y.H).hom ≫ thick R ⊥ 0 := Over.w F
  let ξ := Y.Φ Y.H (𝟙 _)
  obtain ⟨x, hx⟩ := GlobalTheory.TorusCoord.exists_point c (T := Y.H) (Y.H.hom ≫ inv (thick R ⊥ 0)) (by simp) ξ
  obtain ⟨ξ', hξ'⟩ := GlobalTheory.TorusCoord.exists_isPointOf c (T := Y.H) j (by
    rw [← hF]; exact IsIso.inv_hom_id_assoc _ _)
  let b : Y.H ⟶ Y.H := (Y.Φ Y.H).symm ξ'
  have hb : Y.Φ Y.H b = ξ' := Equiv.apply_symm_apply _ _
  let a := x ≫ F.left
  have ha : a ≫ Y.H.hom = Y.H.hom := by
    rw [Category.assoc, hF]
    exact GlobalTheory.TorusCoord.IsPointOf.comp_hom c hx
  let a' : Y.H ⟶ Y.H := Over.homMk a ha
  have haj : a ≫ j = x := by simp [a, j]
  have e1 : b.left ≫ x = j := by
    have h1 : GtPt.IsPull b.left ξ (Y.Φ Y.H (b ≫ 𝟙 _)) := Y.rep.1 Y.H Y.H b (𝟙 _)
    rw [Category.comp_id, hb] at h1
    exact (GlobalTheory.TorusCoord.IsPointOf.pull c hx h1).unique_left c hξ'
  have e1' : b.left ≫ a = 𝟙 _ := by
    rw [← Category.assoc, e1]; simp [j]
  have e2 : a' ≫ b = 𝟙 _ := by
    have h2 : GtPt.IsPull a (Y.Φ Y.H b) (Y.Φ Y.H (a' ≫ b)) := Y.rep.1 Y.H Y.H a' b
    rw [hb] at h2
    have h3 := GlobalTheory.TorusCoord.IsPointOf.pull c hξ' h2
    rw [haj] at h3
    exact (Y.Φ Y.H).injective (h3.unique_right c hx)
  have e2' : a ≫ b.left = 𝟙 _ := congrArg (·.left) e2
  have : IsIso a := ⟨⟨b.left, e2', e1'⟩⟩
  have hq : Y.q.left = a ≫ j ≫ c.q.left ≫ pullback.fst Q.P.A.hom (thick R ⊥ 0) := by
    rw [← Category.assoc a j, haj, ← GlobalTheory.TorusCoord.pG_left]
    exact hx.1
  rw [hq]
  infer_instance

/- English proof (translation)
Establish `h1 : Smooth Y.q.left` using `Y.smooth_q`. Use `Q.P.smoothDim` as an intermediate fact. Establish `h2 : Smooth Q.P.A.hom` using `SmoothOfRelativeDimension.smooth Q.P.g _`. Rewrite using `[← Over.w Y.q]`. Use `infer_instance`.
-/
theorem smooth_H {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) : Smooth Y.H.hom := by
  have h1 : Smooth Y.q.left := Y.smooth_q
  have := Q.P.smoothDim
  have h2 : Smooth Q.P.A.hom := SmoothOfRelativeDimension.smooth Q.P.g _
  rw [← Over.w Y.q]
  infer_instance

/- English proof (translation)
Introduce `R _ _ Q O _ _ _ oa Y V D`. Use `isAffineHom_q Y` as an intermediate fact. Use `smooth_H Y` as an intermediate fact. Conclude with `exists_lift_of_smooth R Y.H.left Y.H.hom _ (V.2.preimage Y.q.left) D`.
-/
theorem exists_lift_preimage : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (D : Derivation ℤ R R), ∃ δ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1) → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1), (∀ a b, δ (a + b) = δ a + δ b) ∧ (∀ a b, δ (a * b) = a * δ b + b * δ a) ∧ ∀ r, δ (constFn Y.H.hom _ r) = constFn Y.H.hom _ (D r) := by
  intro R _ _ Q O _ _ _ oa Y V D
  have := isAffineHom_q Y
  have := smooth_H Y
  exact exists_lift_of_smooth R Y.H.left Y.H.hom _ (V.2.preimage Y.q.left) D

end GlobalTheory.LiftDer
