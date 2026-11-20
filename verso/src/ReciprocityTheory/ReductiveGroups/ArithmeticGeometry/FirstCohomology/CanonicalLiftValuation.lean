import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1.CanonicalLiftValuation

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

/- English proof (translation)
Establish `hC` using `isCub_cubV (c := D.toPre.cub) hJ`. Establish `h` using `(ros_add (c := D.toPre.cub) hG D.toPre.P.isAb f g r hr hr0 hJ 1 1 y).2`. Establish `h11 : (1 : T ⟶ D.toPre.P.A) * 1 = 1` using `mul_one _`. Establish `h1g : (1 : T ⟶ D.toPre.P.A) ≫ g = 1` using `by first`. Consider the case `exact MonObj.one_comp g`.

Consider the case `simp [MonObj.Hom.one_def]`. Consider the case `simp [Hom.one_def]`. Establish `c11 : ∀ a : T ⟶ D.toPre.P.A, cubV D.toPre.cub z J a 1 1 = 1` using `fun a => (hC.s01 a 1 1).trans (hC.face a 1)`. Rewrite `h` using `[h11, h1g, c11 y, c11 (y ≫ f), _root_.mul_one, _root_.one_mul]`. Establish `h' : val₂ r z J y 1 * val₂ r z J y 1 = val₂ r z J y 1 * 1`.

Rewrite using `[_root_.mul_one]`. Conclude with `h.symm`. Conclude with `mul_left_cancel h'`.
-/
theorem ros_snd_one (hG : GlobalFnsSt) (f g : D.toPre.P.A ⟶ D.toPre.P.A) [IsMonHom f] [IsMonHom g]
    (r : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A f g) rosatiε)) (hr : r.IsGen)
    (hr0 : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ r (zero2 D.toPre.P.A)) (LB.oneGen D.toPre.P.L))
    {T : Over (Spec (CommRingCat.of V))} {z : T.left} {J} (hJ : Good D.toPre.P.L z J) (y : T ⟶ D.toPre.P.A) :
    val₂ r z J y 1 = 1 := by
  have hC := isCub_cubV (c := D.toPre.cub) hJ
  have h := (ros_add (c := D.toPre.cub) hG D.toPre.P.isAb f g r hr hr0 hJ 1 1 y).2
  have h11 : (1 : T ⟶ D.toPre.P.A) * 1 = 1 := mul_one _
  have h1g : (1 : T ⟶ D.toPre.P.A) ≫ g = 1 := by
    first
    | exact MonObj.one_comp g
    | simp [MonObj.Hom.one_def]
    | simp [Hom.one_def]
  have c11 : ∀ a : T ⟶ D.toPre.P.A, cubV D.toPre.cub z J a 1 1 = 1 := fun a =>
    (hC.s01 a 1 1).trans (hC.face a 1)
  rw [h11, h1g, c11 y, c11 (y ≫ f), _root_.mul_one, _root_.one_mul] at h
  have h' : val₂ r z J y 1 * val₂ r z J y 1 = val₂ r z J y 1 * 1 := by
    rw [_root_.mul_one]; exact h.symm
  exact mul_left_cancel h'

/- English proof (translation)
Introduce `U _ h`. Use `haveI := oa.onB.hom a`. Use `haveI := oa.onB.hom (star a)`. Simplify using `only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, pullφ, pullε]`. Rewrite using `[prod_ros]`.

Simplify using `only [Fin.prod_univ_succ, Fin.prod_univ_zero, DegPre.famφ, DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_succ, smul_zero]`. Establish `E1 : (padd D.toPre.P.A (DegPre.prB D.toPre F) (toUnit _ ≫ D.toPre.c 0)).left = (DegPre.prB D.toPre F).left`. Use `congr 1`. Express the relevant statement in the definitionally equal form `DegPre.prB D.toPre F * cP D.toPre _ 0 = _`. Rewrite using `[cPoint_zero, _root_.mul_one]`.

Establish `E2 : (toUnit (DegPre.BF D.toPre F) ≫ D.toPre.c 0).left = (toUnit (DegPre.BF D.toPre F) ≫ η[D.toPre.P.A]).left`. Use `congr 1`. Conclude with `cPoint_zero (D := D.toPre) _`. Establish `E5 : (cP D.toPre _ χ ≫ oa.onB.act (star a)).left = (toUnit (DegPre.BF D.toPre F) ≫ D.toPre.c (star a • χ)).left`. Use `congr 1`.

Rewrite using `[oa.c_lin]`. Simplify using `[cP]`. Establish `E4 : ((cP D.toPre _ χ ≫ oa.onB.act (star a)) * DegPre.prB D.toPre F).left = (padd D.toPre.P.A (DegPre.prB D.toPre F) (toUnit _ ≫ D.toPre.c (star a • χ))).left`. Use `congr 1`. Express the relevant statement in the definitionally equal form `_ = DegPre.prB D.toPre F * (toUnit _ ≫ D.toPre.c (star a • χ))`.

Rewrite using `[mul_comm]`. Use `congr 1`. Rewrite using `[oa.c_lin]`. Simplify using `[cP]`. Establish `E6 : (cP D.toPre _ χ * (DegPre.prB D.toPre F ≫ oa.onB.act a)).left = (aF D F oa a).left ≫ (padd D.toPre.P.A (DegPre.prB D.toPre F) (toUnit _ ≫ D.toPre.c χ)).left`.

Rewrite using `[← Over.comp_left]`. Use `congr 1`. Express the relevant statement in the definitionally equal form `_ = aF D F oa a ≫ (DegPre.prB D.toPre F * (toUnit _ ≫ D.toPre.c χ))`. Rewrite using `[mul_comm]`. Use `first`.

Consider the case `rw [MonObj.comp_mul]`. Consider the case `rw [comp_mul]`. Consider the case `rw [Hom.comp_mul]`. Simplify using `[aF, cP]`. Establish `E7 : (cP D.toPre (DegPre.BF D.toPre F) χ).left = (aF D F oa a).left ≫ (toUnit _ ≫ D.toPre.c χ).left`.

Rewrite using `[← Over.comp_left]`. Use `congr 1`. Simplify using `[aF, cP]`. Establish `E8 : (DegPre.prB D.toPre F ≫ oa.onB.act a).left = (aF D F oa a).left ≫ (DegPre.prB D.toPre F).left`. Rewrite using `[← Over.comp_left]`.

Use `congr 1`. Simplify using `[aF]`. Establish `E9 : (aF D F oa a).left ≫ (toUnit (DegPre.BF D.toPre F) ≫ η[D.toPre.P.A]).left = (toUnit (DegPre.BF D.toPre F) ≫ η[D.toPre.P.A]).left`. Rewrite using `[← Over.comp_left]`. Use `congr 1`.

Simplify using the standard rewrite rules. Rewrite using `[E1, E2, E4, E5, E6, E7, E8, E9]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_zpow]`. Normalize the expressions using the abelian group laws.
-/
private theorem formEq_sumElim_pullφ_rosatiφ (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (χ : D.toPre.X) :
    FormEq (Sum.elim (pullφ D F oa a 0) (fun j => (lift (cP D.toPre _ χ) (DegPre.prB D.toPre F)).left ≫
        rosatiφ D.toPre.P.A (oa.onB.act (star a)) (oa.onB.act a) j))
      (Sum.elim (pullε k N) rosatiε) (pullφ D F oa a χ) (pullε k N) := by
  intro U _ h
  haveI := oa.onB.hom a
  haveI := oa.onB.hom (star a)
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, pullφ, pullε]
  rw [prod_ros]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, DegPre.famφ, DegPre.famε, Matrix.cons_val_zero,
    Matrix.cons_val_succ, smul_zero]
  have E1 : (padd D.toPre.P.A (DegPre.prB D.toPre F) (toUnit _ ≫ D.toPre.c 0)).left =
      (DegPre.prB D.toPre F).left := by
    congr 1
    change DegPre.prB D.toPre F * cP D.toPre _ 0 = _
    rw [cPoint_zero, _root_.mul_one]
  have E2 : (toUnit (DegPre.BF D.toPre F) ≫ D.toPre.c 0).left =
      (toUnit (DegPre.BF D.toPre F) ≫ η[D.toPre.P.A]).left := by
    congr 1
    exact cPoint_zero (D := D.toPre) _
  have E5 : (cP D.toPre _ χ ≫ oa.onB.act (star a)).left =
      (toUnit (DegPre.BF D.toPre F) ≫ D.toPre.c (star a • χ)).left := by
    congr 1
    rw [oa.c_lin]
    simp [cP]
  have E4 : ((cP D.toPre _ χ ≫ oa.onB.act (star a)) * DegPre.prB D.toPre F).left =
      (padd D.toPre.P.A (DegPre.prB D.toPre F) (toUnit _ ≫ D.toPre.c (star a • χ))).left := by
    congr 1
    change _ = DegPre.prB D.toPre F * (toUnit _ ≫ D.toPre.c (star a • χ))
    rw [mul_comm]
    congr 1
    rw [oa.c_lin]
    simp [cP]
  have E6 : (cP D.toPre _ χ * (DegPre.prB D.toPre F ≫ oa.onB.act a)).left =
      (aF D F oa a).left ≫ (padd D.toPre.P.A (DegPre.prB D.toPre F) (toUnit _ ≫ D.toPre.c χ)).left := by
    rw [← Over.comp_left]
    congr 1
    change _ = aF D F oa a ≫ (DegPre.prB D.toPre F * (toUnit _ ≫ D.toPre.c χ))
    rw [mul_comm]
    first
    | rw [MonObj.comp_mul]
    | rw [comp_mul]
    | rw [Hom.comp_mul]
    simp [aF, cP]
  have E7 : (cP D.toPre (DegPre.BF D.toPre F) χ).left =
      (aF D F oa a).left ≫ (toUnit _ ≫ D.toPre.c χ).left := by
    rw [← Over.comp_left]
    congr 1
    simp [aF, cP]
  have E8 : (DegPre.prB D.toPre F ≫ oa.onB.act a).left = (aF D F oa a).left ≫ (DegPre.prB D.toPre F).left := by
    rw [← Over.comp_left]
    congr 1
    simp [aF]
  have E9 : (aF D F oa a).left ≫ (toUnit (DegPre.BF D.toPre F) ≫ η[D.toPre.P.A]).left =
      (toUnit (DegPre.BF D.toPre F) ≫ η[D.toPre.P.A]).left := by
    rw [← Over.comp_left]
    congr 1
    simp
  rw [E1, E2, E4, E5, E6, E7, E8, E9]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  abel

/- English proof (translation)
Use `haveI := oa.onB.hom a`. Use `haveI := oa.onB.hom (star a)`. Use `(gen_unique' D.toPre.P.isLB (formEq_sumElim_pullφ_rosatiφ oa a k N χ) (fst (TF (R := V) F) D.toPre.P.A).left (DegPre.zF D.toPre F).left GC.zF_fst (surj_appTop (D := D.toPre) (F := F) hG) hu (mulGen_isGen _ _ _ _ _ _ _ hu0 (pullGen_isGen _ _ _ _ hr _)) ?_ Z ρ z J hJ).trans (val_mu …` and prove the remaining obligations. Introduce `y J' hJ'`. Rewrite using `[val_mul hJ']`.

Establish `e1 : val u (DegPre.zF D.toPre F).left y J' = val (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R` using `V) F)) (𝟙 _) y J' := by`. Rewrite using `[← Category.id_comp (DegPre.zF D.toPre F).left, ← val_pull hJ']`. Conclude with `val_corr hJ' hc _`. Establish `e2 : val u0 (DegPre.zF D.toPre F).left y J' = val (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R` using `V) F)) (𝟙 _) y J' := by`. Rewrite using `[← Category.id_comp (DegPre.zF D.toPre F).left, ← val_pull hJ']`.

Conclude with `val_corr hJ' hc0 _`. Establish `hz : DegPre.zF D.toPre F ≫ lift (cP D.toPre _ χ) (DegPre.prB D.toPre F) = lift (cP D.toPre (TF (R` using `V) F) χ) 1 := by`. Simplify using `[DegPre.zF, cP, Hom.one_def]`. Establish `e3 : val (LB.pullGen D.toPre.P.L _ _ r (lift (cP D.toPre _ χ) (DegPre.prB D.toPre F)).left) (DegPre.zF D.toPre F).left y J' = 1`. Rewrite using `[val_pull hJ', ← Over.comp_left, hz]`.

Conclude with `ros_snd_one hG _ _ r hr hr0 hJ' _`. Rewrite using `[e1, e2, e3]`. Conclude with `(_root_.mul_one _).symm`.
-/
theorem pull_val_chi (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (χ : D.toPre.X)
    (u : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε k N))) (hu : u.IsGen)
    (hc : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F)))
    (u0 : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a 0) (pullε k N))) (hu0 : u0.IsGen)
    (hc0 : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u0 (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F)))
    (r : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε))
    (hr : r.IsGen)
    (hr0 : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ r (zero2 D.toPre.P.A)) (LB.oneGen D.toPre.P.L))
    (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J) (hJ : Good D.toPre.P.L z J) :
    val u ρ z J = val u0 ρ z J *
      val (LB.pullGen D.toPre.P.L _ _ r (lift (cP D.toPre _ χ) (DegPre.prB D.toPre F)).left) ρ z J := by
  haveI := oa.onB.hom a
  haveI := oa.onB.hom (star a)
  refine (gen_unique' D.toPre.P.isLB (formEq_sumElim_pullφ_rosatiφ oa a k N χ) (fst (TF (R := V) F) D.toPre.P.A).left
    (DegPre.zF D.toPre F).left GC.zF_fst (surj_appTop (D := D.toPre) (F := F) hG) hu
    (mulGen_isGen _ _ _ _ _ _ _ hu0 (pullGen_isGen _ _ _ _ hr _)) ?_ Z ρ z J hJ).trans (val_mul hJ _ _ _)
  intro y J' hJ'
  rw [val_mul hJ']
  have e1 : val u (DegPre.zF D.toPre F).left y J' = val (LB.pullGen D.toPre.P.L _ _
      (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F)) (𝟙 _) y J' := by
    rw [← Category.id_comp (DegPre.zF D.toPre F).left, ← val_pull hJ']
    exact val_corr hJ' hc _
  have e2 : val u0 (DegPre.zF D.toPre F).left y J' = val (LB.pullGen D.toPre.P.L _ _
      (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F)) (𝟙 _) y J' := by
    rw [← Category.id_comp (DegPre.zF D.toPre F).left, ← val_pull hJ']
    exact val_corr hJ' hc0 _
  have hz : DegPre.zF D.toPre F ≫ lift (cP D.toPre _ χ) (DegPre.prB D.toPre F) =
      lift (cP D.toPre (TF (R := V) F) χ) 1 := by
    simp [DegPre.zF, cP, Hom.one_def]
  have e3 : val (LB.pullGen D.toPre.P.L _ _ r (lift (cP D.toPre _ χ) (DegPre.prB D.toPre F)).left)
      (DegPre.zF D.toPre F).left y J' = 1 := by
    rw [val_pull hJ', ← Over.comp_left, hz]
    exact ros_snd_one hG _ _ r hr hr0 hJ' _
  rw [e1, e2, e3]
  exact (_root_.mul_one _).symm
