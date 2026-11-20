import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralOfTorsion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.CubeSymDescent

/- English proof (translation)
Introduce `S S' G G' _ _ _ _ f β h L c s hs i₃ c₃ hup T x y u z J hJ`. Set `φs : Fin 2 → (G.left ⟶ G.left)` to `![(ι[G]).left, 𝟙 G.left]`. Set `εs : Fin 2 → ℤ` to `![1, -1]`. Set `a` to `x3 G 0`. Set `b` to `x3 G 1`.

Set `d` to `x3 G 2`. Set `A` to `LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a⁻¹ (lift b⁻¹ d⁻¹)).left) (LB.pullGen L.L φs εs s (a * b).left)) (LB.pullGen L.L φs εs s (a * d).left)) (LB.pullGen L.L φs εs s (b * d).left)`. Establish `vA : ∀ (T : Over S) (V : T ⟶ G3 G) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J → val A V.left z J = cubV c z J (V ≫ a)⁻¹ (V ≫ b)⁻¹ (V ≫ d)⁻¹ * val s ((V ≫ a) * (V ≫ b)).left z J * val s ((V ≫ a) * (V ≫ d)).left z J * val s ((V ≫ b) * (V ≫ d)).left z J`. Introduce `T V z J hJ`. Establish `m1` using `val_mul hJ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a⁻¹ (lift b⁻¹ d⁻¹)).left) (LB.pullGen L.L φs εs s (a * b).left)) (LB.pullGen L.L φs εs s (a * d).left)) (LB.pullGen L.L φs εs s (b * d).left) V.left`.

Establish `m2` using `val_mul hJ (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a⁻¹ (lift b⁻¹ d⁻¹)).left) (LB.pullGen L.L φs εs s (a * b).left)) (LB.pullGen L.L φs εs s (a * d).left) V.left`. Establish `m3` using `val_mul hJ (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a⁻¹ (lift b⁻¹ d⁻¹)).left) (LB.pullGen L.L φs εs s (a * b).left) V.left`. Use `m1.trans ?_` and prove the remaining obligations. Rewrite using `[m2, m3, val_pull hJ, val_pull hJ, val_pull hJ, val_pull (φ := thφ G (x3 G)) (ε := thε) hJ c.t _ V.left]`. Simplify using `only [← Over.comp_left, comp_lift, GrpObj.comp_inv, MonObj.comp_mul]`.

Both sides reduce to the same expression. Set `B` to `LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift b d)).left) (LB.pullGen L.L φs εs s (a * b * d).left)) (LB.pullGen L.L φs εs s a.left)) (LB.pullGen L.L φs εs s b.left)) (LB.pullGen L.L …`. Establish `vB : ∀ (T : Over S) (V : T ⟶ G3 G) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J → val B V.left z J = cubV c z J (V ≫ a) (V ≫ b) (V ≫ d) * val s ((V ≫ a) * (V ≫ b) * (V ≫ d)).left z J * val s (V ≫ a).left z J * val s (V ≫ b).left z J * val s (V ≫ d).left z J`. Introduce `T V z J hJ`. Establish `m1` using `val_mul hJ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift b d)).left) (LB.pullGen L.L φs εs s (a * b * d).left)) (LB.pullGen L.L φs εs s a.left)) (LB.pullGen L.L φs εs s b.left)) (LB.pullGen L.L φs εs s d. …`.

Establish `m2` using `val_mul hJ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift b d)).left) (LB.pullGen L.L φs εs s (a * b * d).left)) (LB.pullGen L.L φs εs s a.left)) (LB.pullGen L.L φs εs s b.left) V.left`. Establish `m3` using `val_mul hJ (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift b d)).left) (LB.pullGen L.L φs εs s (a * b * d).left)) (LB.pullGen L.L φs εs s a.left) V.left`. Establish `m4` using `val_mul hJ (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift b d)).left) (LB.pullGen L.L φs εs s (a * b * d).left) V.left`. Use `m1.trans ?_` and prove the remaining obligations. Rewrite using `[m2, m3, m4, val_pull hJ, val_pull hJ, val_pull hJ, val_pull hJ, val_pull (φ := thφ G (x3 G)) (ε := thε) hJ c.t _ V.left]`.

Simplify using `only [← Over.comp_left, comp_lift, MonObj.comp_mul]`. Both sides reduce to the same expression. Establish `hcorr : LB.Gen.Corr L.L _ _ _ _ A B`. Use `GlobalTheory.GtTorsionPoints.corr_of_val_pull L.isLB (cubeMapOf h).F3 i₃ (fun a b e => c₃ a b e) fun z J hJ => ?_` and prove the remaining obligations. Set `P : Over.mk ((G3 G').hom ≫ f) ⟶ G3 G` to `lift (pushPt h.1.w (x3 G' 0)) (lift (pushPt h.1.w (x3 G' 1)) (pushPt h.1.w (x3 G' 2)))`.

Establish `hP : (cubeMapOf h).F3 = P.left` using `rfl`. Establish `ha : P ≫ a = pushHom h (G3 G') (x3 G' 0)` using `by simp [P, a, x3]; rfl`. Establish `hb : P ≫ b = pushHom h (G3 G') (x3 G' 1)` using `by simp [P, b, x3]; rfl`. Establish `hd : P ≫ d = pushHom h (G3 G') (x3 G' 2)` using `by simp [P, d, x3]; rfl`. Rewrite using `[hP, vA _ P z J hJ, vB _ P z J hJ, ha, hb, hd]`.

Establish `e` using `hup (G3 G') z J hJ (x3 G' 0) (x3 G' 1) (x3 G' 2)`. Simplify using `only [map_inv, map_mul] at e ⊢`. Conclude with `e`. Establish `e` using `val_corr hJ hcorr (lift x (lift y u)).left`. Establish `ha : lift x (lift y u) ≫ a = x` using `by simp [a, x3]`.

Establish `hb : lift x (lift y u) ≫ b = y` using `by simp [b, x3]`. Establish `hd : lift x (lift y u) ≫ d = u` using `by simp [d, x3]`. Rewrite `e` using `[vA _ _ z J hJ, vB _ _ z J hJ, ha, hb, hd]`. Conclude with `e`.
-/
theorem of_push : ∀ {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {β : G'.left ⟶ G.left} (h : IsGrpPullback G' G f β), ∀ (L : RigLB G) (c : CubicalStr G L) (s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])), s.IsGen → (∀ U, Function.Injective ((cubeMapOf h).F3.app U).hom) → (∀ {X : Scheme.{0}} (a b : (G3 G).left ⟶ X), (cubeMapOf h).F3 ≫ a = (cubeMapOf h).F3 ≫ b → a = b) → (∀ (T : Over S') (z : T.left) (I : (T.left ⟶ G.left) → L.L.ι), Good L.L z I → ∀ x y u : T ⟶ G', cubV c z I (pushHom h T x⁻¹) (pushHom h T y⁻¹) (pushHom h T u⁻¹) * val s (pushHom h T (x * y)).left z I * val s (pushHom h T (x * u)).left z I * val s (pushHom h T (y * u)).left z I = cubV c z I (pushHom h T x) (pushHom h T y) (pushHom h T u) * val s (pushHom h T (x * y * u)).left z I * val s (pushHom h T x).left z I * val s (pushHom h T y).left z I * val s (pushHom h T u).left z I) → ∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J → cubV c z J x⁻¹ y⁻¹ u⁻¹ * val s (x * y).left z J * val s (x * u).left z J * val s (y * u).left z J = cubV c z J x y u * val s (x * y * u).left z J * val s x.left z J * val s y.left z J * val s u.left z J := by
  intro S S' G G' _ _ _ _ f β h L c s hs i₃ c₃ hup T x y u z J hJ
  let φs : Fin 2 → (G.left ⟶ G.left) := ![(ι[G]).left, 𝟙 G.left]
  let εs : Fin 2 → ℤ := ![1, -1]
  let a := x3 G 0
  let b := x3 G 1
  let d := x3 G 2
  let A := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
    (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a⁻¹ (lift b⁻¹ d⁻¹)).left)
    (LB.pullGen L.L φs εs s (a * b).left)) (LB.pullGen L.L φs εs s (a * d).left))
    (LB.pullGen L.L φs εs s (b * d).left)
  have vA : ∀ (T : Over S) (V : T ⟶ G3 G) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J →
      val A V.left z J = cubV c z J (V ≫ a)⁻¹ (V ≫ b)⁻¹ (V ≫ d)⁻¹ * val s ((V ≫ a) * (V ≫ b)).left z J *
        val s ((V ≫ a) * (V ≫ d)).left z J * val s ((V ≫ b) * (V ≫ d)).left z J := by
    intro T V z J hJ
    have m1 := val_mul hJ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a⁻¹ (lift b⁻¹ d⁻¹)).left)
      (LB.pullGen L.L φs εs s (a * b).left)) (LB.pullGen L.L φs εs s (a * d).left))
      (LB.pullGen L.L φs εs s (b * d).left) V.left
    have m2 := val_mul hJ (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a⁻¹ (lift b⁻¹ d⁻¹)).left)
      (LB.pullGen L.L φs εs s (a * b).left)) (LB.pullGen L.L φs εs s (a * d).left) V.left
    have m3 := val_mul hJ (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a⁻¹ (lift b⁻¹ d⁻¹)).left)
      (LB.pullGen L.L φs εs s (a * b).left) V.left
    refine m1.trans ?_
    rw [m2, m3, val_pull hJ, val_pull hJ, val_pull hJ, val_pull (φ := thφ G (x3 G)) (ε := thε) hJ c.t _ V.left]
    simp only [← Over.comp_left, comp_lift, GrpObj.comp_inv, MonObj.comp_mul]
    rfl
  let B := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
    (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift b d)).left)
    (LB.pullGen L.L φs εs s (a * b * d).left)) (LB.pullGen L.L φs εs s a.left))
    (LB.pullGen L.L φs εs s b.left)) (LB.pullGen L.L φs εs s d.left)
  have vB : ∀ (T : Over S) (V : T ⟶ G3 G) (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J →
      val B V.left z J = cubV c z J (V ≫ a) (V ≫ b) (V ≫ d) * val s ((V ≫ a) * (V ≫ b) * (V ≫ d)).left z J *
        val s (V ≫ a).left z J * val s (V ≫ b).left z J * val s (V ≫ d).left z J := by
    intro T V z J hJ
    have m1 := val_mul hJ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift b d)).left)
      (LB.pullGen L.L φs εs s (a * b * d).left)) (LB.pullGen L.L φs εs s a.left))
      (LB.pullGen L.L φs εs s b.left)) (LB.pullGen L.L φs εs s d.left) V.left
    have m2 := val_mul hJ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift b d)).left)
      (LB.pullGen L.L φs εs s (a * b * d).left)) (LB.pullGen L.L φs εs s a.left))
      (LB.pullGen L.L φs εs s b.left) V.left
    have m3 := val_mul hJ (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift b d)).left)
      (LB.pullGen L.L φs εs s (a * b * d).left)) (LB.pullGen L.L φs εs s a.left) V.left
    have m4 := val_mul hJ (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift b d)).left)
      (LB.pullGen L.L φs εs s (a * b * d).left) V.left
    refine m1.trans ?_
    rw [m2, m3, m4, val_pull hJ, val_pull hJ, val_pull hJ, val_pull hJ,
      val_pull (φ := thφ G (x3 G)) (ε := thε) hJ c.t _ V.left]
    simp only [← Over.comp_left, comp_lift, MonObj.comp_mul]
    rfl
  have hcorr : LB.Gen.Corr L.L _ _ _ _ A B := by
    refine GlobalTheory.GtTorsionPoints.corr_of_val_pull L.isLB (cubeMapOf h).F3 i₃ (fun a b e => c₃ a b e) fun z J hJ => ?_
    let P : Over.mk ((G3 G').hom ≫ f) ⟶ G3 G :=
      lift (pushPt h.1.w (x3 G' 0)) (lift (pushPt h.1.w (x3 G' 1)) (pushPt h.1.w (x3 G' 2)))
    have hP : (cubeMapOf h).F3 = P.left := rfl
    have ha : P ≫ a = pushHom h (G3 G') (x3 G' 0) := by simp [P, a, x3]; rfl
    have hb : P ≫ b = pushHom h (G3 G') (x3 G' 1) := by simp [P, b, x3]; rfl
    have hd : P ≫ d = pushHom h (G3 G') (x3 G' 2) := by simp [P, d, x3]; rfl
    rw [hP, vA _ P z J hJ, vB _ P z J hJ, ha, hb, hd]
    have e := hup (G3 G') z J hJ (x3 G' 0) (x3 G' 1) (x3 G' 2)
    simp only [map_inv, map_mul] at e ⊢
    exact e
  have e := val_corr hJ hcorr (lift x (lift y u)).left
  have ha : lift x (lift y u) ≫ a = x := by simp [a, x3]
  have hb : lift x (lift y u) ≫ b = y := by simp [b, x3]
  have hd : lift x (lift y u) ≫ d = u := by simp [d, x3]
  rw [vA _ _ z J hJ, vB _ _ z J hJ, ha, hb, hd] at e
  exact e

end GlobalTheory.CubeSymDescent
