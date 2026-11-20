import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubicalSymmetryTransport
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PulledComparisonEven

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ConstGrp
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

/- English proof (translation)
Take `⟨hp, hv⟩` from `(genRelR_iff w t t₀).1 h`. Establish `hc : ∀ k, pt k ≫ φ = 𝟙 _ ≫ pt₀ k` using `fun k => (hp k).trans (Category.id_comp _).symm`. Take `⟨a, ha, H⟩` from `CubTransport.exists_pmaps hw hM₀ hM (𝟙 _) hc t₀ ht₀`. Take `⟨ρ, hρ⟩` from `TLinPf.ratio_glue _ (TLinPf.linComb_cover M hM pt ε) a t ha ht`. Establish `hr : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp A) (z : Z) (q : K → M.ι), r z ∈ LB.wchart M pt q → gm r z (LB.wchart M pt q) (a.s q) = gm r z ⊤ ρ * gm r z (LB.wchart M pt q) (t.s q)` using `fun Z r z q hq => (congrArg (gm r z _) (hρ q)).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top hq ρ) rfl))`.

Establish `h1 : gm (𝟙 (Sp A)) (cpt A) ⊤ ρ = 1` using `by choose q hq using fun k => exists_chart hM (pt k (cpt A)) choose p hp' using fun k => exists_chart hM₀ (φ (pt k (cpt A)))`. Establish `e₁` using `H _ (𝟙 _) (cpt A) p q hp' hq`. Establish `e₂` using `Units.ext (hv q p hp' hq)`. Rewrite `e₁` using `[hr _ _ _ q (Set.mem_iInter.2 hq)]`. Simplify using `only [Category.id_comp] at e₁`.

Rewrite `e₁` using `[← e₂]`. Conclude with `(mul_eq_right.1 (mul_left_cancel e₁).symm)`. Establish `h2 : ρ = 1`. Establish `e₁` using `toStkA_valR (𝟙 (Sp A)) ⊤ (cpt A) le_rfl ρ`. Establish `e₂` using `toStkA_valR (𝟙 (Sp A)) ⊤ (cpt A) le_rfl 1`.

Rewrite `e₁` using `[h1]`. Rewrite `e₂` using `[map_one]`. Establish `e₃` using `toStkA_injective (e₁.trans e₂.symm)`. Use `unit_ext fun z _ => Units.ext ?_` and prove the remaining obligations. Rewrite using `[← toStkA_valR (𝟙 (Sp A)) ⊤ z le_rfl, ← toStkA_valR (𝟙 (Sp A)) ⊤ z le_rfl, e₃]`.

Introduce `Z r z p q hp hq`. Rewrite using `[H Z r z p q hp hq, hr Z r z q (Set.mem_iInter.2 hq), h2, map_one, _root_.one_mul]`.
-/
theorem pmaps_of_genRelR {A : Type} [CommRing A] [IsLocalRing A] {B B₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀}
    {φ : B ⟶ B₀} {w : LB.Iso M (M₀.pull φ)} (hw : PGen w) (hM : M.IsLB) (hM₀ : M₀.IsLB) {K : Type} [Fintype K]
    {ε : K → ℤ} {pt : K → (Sp A ⟶ B)} {pt₀ : K → (Sp A ⟶ B₀)} {t : LB.Gen (LB.LinComb M pt ε)}
    {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)} (ht : t.IsGen) (ht₀ : t₀.IsGen) (h : GenRelR w t t₀) :
    PMaps w pt pt₀ ε t t₀ (𝟙 _) := by
  obtain ⟨hp, hv⟩ := (genRelR_iff w t t₀).1 h
  have hc : ∀ k, pt k ≫ φ = 𝟙 _ ≫ pt₀ k := fun k => (hp k).trans (Category.id_comp _).symm
  obtain ⟨a, ha, H⟩ := CubTransport.exists_pmaps hw hM₀ hM (𝟙 _) hc t₀ ht₀
  obtain ⟨ρ, hρ⟩ := TLinPf.ratio_glue _ (TLinPf.linComb_cover M hM pt ε) a t ha ht
  have hr : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp A) (z : Z) (q : K → M.ι), r z ∈ LB.wchart M pt q →
      gm r z (LB.wchart M pt q) (a.s q) = gm r z ⊤ ρ * gm r z (LB.wchart M pt q) (t.s q) := fun Z r z q hq =>
    (congrArg (gm r z _) (hρ q)).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top hq ρ) rfl))
  have h1 : gm (𝟙 (Sp A)) (cpt A) ⊤ ρ = 1 := by
    choose q hq using fun k => exists_chart hM (pt k (cpt A))
    choose p hp' using fun k => exists_chart hM₀ (φ (pt k (cpt A)))
    have e₁ := H _ (𝟙 _) (cpt A) p q hp' hq
    have e₂ := Units.ext (hv q p hp' hq)
    rw [hr _ _ _ q (Set.mem_iInter.2 hq)] at e₁
    simp only [Category.id_comp] at e₁
    rw [← e₂] at e₁
    exact (mul_eq_right.1 (mul_left_cancel e₁).symm)
  have h2 : ρ = 1 := by
    have e₁ := toStkA_valR (𝟙 (Sp A)) ⊤ (cpt A) le_rfl ρ
    have e₂ := toStkA_valR (𝟙 (Sp A)) ⊤ (cpt A) le_rfl 1
    rw [h1] at e₁
    rw [map_one] at e₂
    have e₃ := toStkA_injective (e₁.trans e₂.symm)
    refine unit_ext fun z _ => Units.ext ?_
    rw [← toStkA_valR (𝟙 (Sp A)) ⊤ z le_rfl, ← toStkA_valR (𝟙 (Sp A)) ⊤ z le_rfl, e₃]
  intro Z r z p q hp hq
  rw [H Z r z p q hp hq, hr Z r z q (Set.mem_iInter.2 hq), h2, map_one, _root_.one_mul]

section Push

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {f : S' ⟶ S} {F : G'.left ⟶ G.left} (gp : IsGrpPullback G' G f F)

omit [IsCommMonObj G] [IsCommMonObj G'] in
/- English proof (translation)
The claim follows from `Over.OverMorphism.ext (Category.assoc _ _ _).symm`.
-/
theorem map_push {T T' : Over S'} (ρ : T' ⟶ T) (x : T ⟶ G') :
    (Over.map f).map ρ ≫ pushHom gp T x = pushHom gp T' (ρ ≫ x) :=
  Over.OverMorphism.ext (Category.assoc _ _ _).symm

omit [IsCommMonObj G] [IsCommMonObj G'] in
/- English proof (translation)
Introduce `x y h` and use `Over.OverMorphism.ext (gp.1.hom_ext (congrArg (fun q => q.left) h) ((Over.w x).trans (Over.w y).symm))`.
-/
theorem push_injective (T : Over S') : Function.Injective (pushHom gp T) := fun x y h =>
  Over.OverMorphism.ext (gp.1.hom_ext (congrArg (fun q => q.left) h) ((Over.w x).trans (Over.w y).symm))

/- English proof (translation)
Establish `hψ : ∀ I : thK, thφ G' (x3 G') I ≫ F = (cubeMapOf gp).F3 ≫ thφ G (x3 G) I` using `fun I => (cubeMapOf gp).psum_comm I.down`. Establish `q : ∀ {T : Over S'} (x x' y : T ⟶ G'), (lift x (lift x' y)).left ≫ (cubeMapOf gp).F3 = (lift (pushHom gp T x) (lift (pushHom gp T x') (pushHom gp T y))).left` using `fun {T} x x' y => by`. Establish `e : (Over.map f).map (lift x (lift x' y)) ≫ lift (pushHom gp _ (x3 G' 0)) (lift (pushHom gp _ (x3 G' 1)) (pushHom gp _ (x3 G' 2))) = lift (pushHom gp T x) (lift (pushHom gp T x') (pushHom gp T y))`. Rewrite using `[comp_lift, comp_lift, map_push, map_push, map_push]`. Simplify using `[x3]`.

Conclude with `congrArg (fun q => q.left) e`. Set `o : 𝟙_ (Over S') ⟶ G'` to `1`. Establish `H : PMaps w (thφ G' (x3 G')) (thφ G (x3 G)) thε c'.t c.t (cubeMapOf gp).F3` using `EvenPull.pmaps_of_section hw L.isLB L'.isLB _ hψ _ c'.isGen _ c.isGen ((snd G' (G' ⊗ G')).left ≫ (snd G' G').left ≫ G'.hom) (lift o (lift o o)).left (by rw [Over.w, Over.w]; exact Over.w _) (surj_comp (surj_snd hG hA _) (surj_comp (surj_snd hG hA _) (hG _ _ hA).2)) fun y J J' hJ …`. Rewrite using `[q]`. Establish `e₁ : cubV c (T` using `Over.mk ((𝟙_ (Over S')).hom ≫ f)) y J (pushHom gp _ o) (pushHom gp _ o) (pushHom gp _ o) = 1 := by`.

Rewrite using `[map_one]`. Conclude with `(isCub_cubV c (T := Over.mk ((𝟙_ (Over S')).hom ≫ f)) hJ).face _ _`. Establish `e₂` using `prod_cub o o o (fun q => gw w q y (J (q ≫ F)) (J' q))`. Establish `e₃ : cubV c' y J' o o o = 1` using `(isCub_cubV c' hJ').face _ _`. Use `e₁.trans (Eq.trans ?_ (congrArg₂ (· * ·) e₂ e₃).symm)` and prove the remaining obligations.

Simplify using `[o]`. Establish `e` using `CubTransport.val_pmaps hψ H (lift x (lift x' y)).left hJ hJ'`. Rewrite `e` using `[q]`. Take `rfl : h = _` from `funext hh`. Conclude with `e.trans (congrArg₂ (· * ·) (prod_cub x x' y (fun q => gw w q z (J (q ≫ F)) (J' q))) rfl)`.
-/
theorem cubV_push (hG : GlobalFnsSt) (hA : IsAbelianScheme G') {L : RigLB G} {L' : RigLB G'} (c : CubicalStr G L)
    (c' : CubicalStr G' L') {w : LB.Iso L'.L (L.L.pull F)} (hw : PGen w) {T : Over S'} (x x' y : T ⟶ G') {z : T.left}
    {J J'} (hJ : Good L.L z J) (hJ' : Good L'.L z J') (h : (T.left ⟶ G'.left) → (T.left.presheaf.stalk z)ˣ)
    (hh : ∀ q, h q = gw w q z (J (q ≫ F)) (J' q)) :
    cubV c (T := Over.mk (T.hom ≫ f)) z J (pushHom gp T x) (pushHom gp T x') (pushHom gp T y) =
      (h (x * x' * y).left * (h (x * x').left)⁻¹ * (h (x * y).left)⁻¹ * (h (x' * y).left)⁻¹ * h x.left * h x'.left *
        h y.left * (h (1 : T ⟶ G').left)⁻¹) * cubV c' z J' x x' y := by
  have hψ : ∀ I : thK, thφ G' (x3 G') I ≫ F = (cubeMapOf gp).F3 ≫ thφ G (x3 G) I :=
    fun I => (cubeMapOf gp).psum_comm I.down
  have q : ∀ {T : Over S'} (x x' y : T ⟶ G'), (lift x (lift x' y)).left ≫ (cubeMapOf gp).F3 =
      (lift (pushHom gp T x) (lift (pushHom gp T x') (pushHom gp T y))).left := fun {T} x x' y => by
    have e : (Over.map f).map (lift x (lift x' y)) ≫
        lift (pushHom gp _ (x3 G' 0)) (lift (pushHom gp _ (x3 G' 1)) (pushHom gp _ (x3 G' 2))) =
        lift (pushHom gp T x) (lift (pushHom gp T x') (pushHom gp T y)) := by
      rw [comp_lift, comp_lift, map_push, map_push, map_push]
      simp [x3]
    exact congrArg (fun q => q.left) e
  let o : 𝟙_ (Over S') ⟶ G' := 1
  have H : PMaps w (thφ G' (x3 G')) (thφ G (x3 G)) thε c'.t c.t (cubeMapOf gp).F3 :=
    EvenPull.pmaps_of_section hw L.isLB L'.isLB _ hψ _ c'.isGen _ c.isGen
      ((snd G' (G' ⊗ G')).left ≫ (snd G' G').left ≫ G'.hom) (lift o (lift o o)).left
      (by rw [Over.w, Over.w]; exact Over.w _)
      (surj_comp (surj_snd hG hA _) (surj_comp (surj_snd hG hA _) (hG _ _ hA).2)) fun y J J' hJ hJ' => by
        rw [q]
        have e₁ : cubV c (T := Over.mk ((𝟙_ (Over S')).hom ≫ f)) y J (pushHom gp _ o) (pushHom gp _ o)
            (pushHom gp _ o) = 1 := by
          rw [map_one]
          exact (isCub_cubV c (T := Over.mk ((𝟙_ (Over S')).hom ≫ f)) hJ).face _ _
        have e₂ := prod_cub o o o (fun q => gw w q y (J (q ≫ F)) (J' q))
        have e₃ : cubV c' y J' o o o = 1 := (isCub_cubV c' hJ').face _ _
        refine e₁.trans (Eq.trans ?_ (congrArg₂ (· * ·) e₂ e₃).symm)
        simp [o]
  have e := CubTransport.val_pmaps hψ H (lift x (lift x' y)).left hJ hJ'
  rw [q] at e
  obtain rfl : h = _ := funext hh
  exact e.trans (congrArg₂ (· * ·) (prod_cub x x' y (fun q => gw w q z (J (q ≫ F)) (J' q))) rfl)

omit [IsCommMonObj G] [IsCommMonObj G'] in
/- English proof (translation)
The claim follows from `Over.OverMorphism.ext (by show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _ rw [Category.assoc, ha, Category.assoc])`.
-/
theorem push_act {a : G ⟶ G} {a' : G' ⟶ G'} (ha : a'.left ≫ F = F ≫ a.left) {T : Over S'} (x : T ⟶ G') :
    pushHom gp T (x ≫ a') = pushHom gp T x ≫ a :=
  Over.OverMorphism.ext (by
    show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
    rw [Category.assoc, ha, Category.assoc])

/- English proof (translation)
Set `U` to `lift (pushHom gp _ (fst G' G')) (pushHom gp _ (snd G' G'))`. Establish `q : ∀ {T : Over S'} (x y : T ⟶ G'), (lift x y).left ≫ U.left = (lift (pushHom gp T x) (pushHom gp T y)).left` using `fun {T} x y => by`. Establish `e : (Over.map f).map (lift x y) ≫ U = lift (pushHom gp T x) (pushHom gp T y)`. Rewrite using `[comp_lift, map_push, map_push, lift_fst, lift_snd]`. Conclude with `congrArg (fun q => q.left) e`.

Establish `k : ∀ (p' : G' ⊗ G' ⟶ G') (p : G ⊗ G ⟶ G), pushHom gp _ p' = U ≫ p → p'.left ≫ F = U.left ≫ p.left` using `fun p' p e => congrArg (fun q => q.left) e`. Establish `u₁ : pushHom gp _ (fst G' G') = U ≫ fst G G` using `(lift_fst _ _).symm`. Establish `u₂ : pushHom gp _ (snd G' G') = U ≫ snd G G` using `(lift_snd _ _).symm`. Establish `u₃ : pushHom gp _ (fst G' G' ≫ a') = U ≫ fst G G ≫ a` using `by rw [push_act gp ha, u₁, Category.assoc]`. Establish `u₄ : pushHom gp _ (snd G' G' ≫ b') = U ≫ snd G G ≫ b` using `by rw [push_act gp hb, u₂, Category.assoc]`.

Establish `hψ : ∀ i, rosatiφ G' a' b' i ≫ F = U.left ≫ rosatiφ G a b i` using `fun i => by fin_cases i`. Conclude with `k _ _ ((map_mul _ _ _).trans ((congrArg₂ (· * ·) u₃ u₂).trans (MonObj.comp_mul _ _ _).symm))`. Conclude with `k _ _ u₃`. Conclude with `k _ _ u₂`. Conclude with `k _ _ ((map_mul _ _ _).trans ((congrArg₂ (· * ·) u₁ u₄).trans (MonObj.comp_mul _ _ _).symm))`.

Conclude with `k _ _ u₁`. Conclude with `k _ _ u₄`. Set `o : 𝟙_ (Over S') ⟶ G'` to `1`. Establish `H : PMaps w (rosatiφ G' a' b') (rosatiφ G a b) rosatiε u' u U.left` using `EvenPull.pmaps_of_section hw hL hL' _ hψ _ hu' _ hu ((snd G' G').left ≫ G'.hom) (lift o o).left (by rw [Over.w]; exact Over.w _) (surj_comp (surj_snd hG hA _) (hG _ _ hA).2) fun y J J' hJ hJ' => by`. Rewrite using `[q, map_one]`.

Establish `z₁ : (lift (1 : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G) 1).left = (toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ f))).left ≫ zero2 G`. Rewrite using `[← Over.comp_left, comp_lift]`. Both sides reduce to the same expression. Establish `z₂ : (lift o o).left = 𝟙 _ ≫ zero2 G'` using `by simp [o, Hom.one_def]`. Establish `e₁` using `(congrArg (fun q => val u q y J) z₁).trans ((val_pull hJ _ _ _).symm.trans ((val_corr hJ u₀ _).trans (val_one _)))`.

Establish `e₃ : val₂ u' (T` using `𝟙_ (Over S')) y J' o o = 1 := (congrArg (fun q => val u' q y J') z₂).trans ((val_pull hJ' _ _ _).symm.trans ((val_corr hJ' u₀' _).trans (val_one _)))`. Establish `e₂` using `prod_ros a' b' o o (fun q => gw w q y (J (q ≫ F)) (J' q))`. Use `e₁.trans (Eq.trans ?_ (congrArg₂ (· * ·) e₂ e₃).symm)` and prove the remaining obligations. Simplify using `[o, MonObj.one_comp]`. Establish `e` using `CubTransport.val_pmaps hψ H (lift x y).left hJ hJ'`.

Rewrite `e` using `[q]`. Take `rfl : h = _` from `funext hh`. Conclude with `e.trans (congrArg₂ (· * ·) (prod_ros a' b' x y (fun q => gw w q z (J (q ≫ F)) (J' q))) rfl)`.
-/
theorem ros_push (hG : GlobalFnsSt) (hA : IsAbelianScheme G') {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB)
    (hL' : L'.IsLB) {w : LB.Iso L' (L.pull F)} (hw : PGen w) {a b : G ⟶ G} {a' b' : G' ⟶ G'} [IsMonHom a'] [IsMonHom b']
    (ha : a'.left ≫ F = F ≫ a.left) (hb : b'.left ≫ F = F ≫ b.left)
    (u : LB.Gen (LB.LinComb L (rosatiφ G a b) rosatiε)) (hu : u.IsGen)
    (u₀ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 G)) (LB.oneGen L))
    (u' : LB.Gen (LB.LinComb L' (rosatiφ G' a' b') rosatiε)) (hu' : u'.IsGen)
    (u₀' : LB.Gen.Corr L' _ _ _ _ (LB.pullGen L' _ _ u' (zero2 G')) (LB.oneGen L'))
    {T : Over S'} (x y : T ⟶ G') {z : T.left}
    {J J'} (hJ : Good L z J) (hJ' : Good L' z J') (h : (T.left ⟶ G'.left) → (T.left.presheaf.stalk z)ˣ)
    (hh : ∀ q, h q = gw w q z (J (q ≫ F)) (J' q)) :
    val₂ u (T := Over.mk (T.hom ≫ f)) z J (pushHom gp T x) (pushHom gp T y) =
      (h ((x ≫ a') * y).left * (h (x ≫ a').left)⁻¹ * (h y.left)⁻¹ * (h (x * (y ≫ b')).left)⁻¹ * h x.left *
        h (y ≫ b').left) * val₂ u' z J' x y := by
  let U := lift (pushHom gp _ (fst G' G')) (pushHom gp _ (snd G' G'))
  have q : ∀ {T : Over S'} (x y : T ⟶ G'), (lift x y).left ≫ U.left =
      (lift (pushHom gp T x) (pushHom gp T y)).left := fun {T} x y => by
    have e : (Over.map f).map (lift x y) ≫ U = lift (pushHom gp T x) (pushHom gp T y) := by
      rw [comp_lift, map_push, map_push, lift_fst, lift_snd]
    exact congrArg (fun q => q.left) e
  have k : ∀ (p' : G' ⊗ G' ⟶ G') (p : G ⊗ G ⟶ G), pushHom gp _ p' = U ≫ p → p'.left ≫ F = U.left ≫ p.left :=
    fun p' p e => congrArg (fun q => q.left) e
  have u₁ : pushHom gp _ (fst G' G') = U ≫ fst G G := (lift_fst _ _).symm
  have u₂ : pushHom gp _ (snd G' G') = U ≫ snd G G := (lift_snd _ _).symm
  have u₃ : pushHom gp _ (fst G' G' ≫ a') = U ≫ fst G G ≫ a := by rw [push_act gp ha, u₁, Category.assoc]
  have u₄ : pushHom gp _ (snd G' G' ≫ b') = U ≫ snd G G ≫ b := by rw [push_act gp hb, u₂, Category.assoc]
  have hψ : ∀ i, rosatiφ G' a' b' i ≫ F = U.left ≫ rosatiφ G a b i := fun i => by
    fin_cases i
    · exact k _ _ ((map_mul _ _ _).trans ((congrArg₂ (· * ·) u₃ u₂).trans (MonObj.comp_mul _ _ _).symm))
    · exact k _ _ u₃
    · exact k _ _ u₂
    · exact k _ _ ((map_mul _ _ _).trans ((congrArg₂ (· * ·) u₁ u₄).trans (MonObj.comp_mul _ _ _).symm))
    · exact k _ _ u₁
    · exact k _ _ u₄
  let o : 𝟙_ (Over S') ⟶ G' := 1
  have H : PMaps w (rosatiφ G' a' b') (rosatiφ G a b) rosatiε u' u U.left :=
    EvenPull.pmaps_of_section hw hL hL' _ hψ _ hu' _ hu
      ((snd G' G').left ≫ G'.hom) (lift o o).left (by rw [Over.w]; exact Over.w _)
      (surj_comp (surj_snd hG hA _) (hG _ _ hA).2) fun y J J' hJ hJ' => by
        rw [q, map_one]
        have z₁ : (lift (1 : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G) 1).left =
            (toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ f))).left ≫ zero2 G := by
          rw [← Over.comp_left, comp_lift]; rfl
        have z₂ : (lift o o).left = 𝟙 _ ≫ zero2 G' := by simp [o, Hom.one_def]
        have e₁ := (congrArg (fun q => val u q y J) z₁).trans
          ((val_pull hJ _ _ _).symm.trans ((val_corr hJ u₀ _).trans (val_one _)))
        have e₃ : val₂ u' (T := 𝟙_ (Over S')) y J' o o = 1 := (congrArg (fun q => val u' q y J') z₂).trans
          ((val_pull hJ' _ _ _).symm.trans ((val_corr hJ' u₀' _).trans (val_one _)))
        have e₂ := prod_ros a' b' o o (fun q => gw w q y (J (q ≫ F)) (J' q))
        refine e₁.trans (Eq.trans ?_ (congrArg₂ (· * ·) e₂ e₃).symm)
        simp [o, MonObj.one_comp]
  have e := CubTransport.val_pmaps hψ H (lift x y).left hJ hJ'
  rw [q] at e
  obtain rfl : h = _ := funext hh
  exact e.trans (congrArg₂ (· * ·) (prod_ros a' b' x y (fun q => gw w q z (J (q ≫ F)) (J' q))) rfl)

end Push

section Data

variable {R R₀ : Type} [CommRing R] [IsDomain R] [CommRing R₀] [IsDomain R₀] {D : DegPre R} {D₀ : DegPre R₀}
  {f : Sp R ⟶ Sp R₀} {φ : D.P.A.left ⟶ D₀.P.A.left} (gp : IsGrpPullback D.P.A D₀.P.A f φ)
  (w : LB.Iso D.P.L (D₀.P.L.pull φ)) (e : D₀.X → D.X) {T : Over (Sp R)} {F : Type} [Field F]
  [Algebra (FractionRing R₀) F] (ρ : Over.mk (T.hom ≫ f) ⟶ TF (R := R₀) F)

def Rel (g : GtPt D T) (g₀ : GtPtF D₀ F) : Prop :=
  pushHom gp T g.b = ρ ≫ g₀.b ∧ ∀ x (z : T.left) J J', Good D₀.P.L z J → Good D.P.L z J' →
    ∀ h : (T.left ⟶ D.P.A.left) → (T.left.presheaf.stalk z)ˣ, (∀ q, h q = gw w q z (J (q ≫ φ)) (J' q)) →
      val (g₀.s x) ρ.left z J = ((h (cP D T (e x) * g.b).left)⁻¹ * h (cP D T (e x)).left * h g.b.left *
        (h (1 : T ⟶ D.P.A).left)⁻¹) * val (g.s (e x)) (𝟙 _) z J'

variable {gp w e ρ}

/- English proof (translation)
Use `⟨Over.OverMorphism.ext (hc 0 2), fun x z J J' hJ hJ' h hh => ?_⟩` and prove the remaining obligations. Take `rfl : h = _` from `funext hh`. Establish `v` using `CubTransport.val_pmaps (fun k => (hc x k).trans (Category.id_comp _).symm) (H x) (𝟙 _) hJ hJ'`. Rewrite `v` using `[val_pull hJ, Category.id_comp]`. Establish `p` using `FormalPoint.prod_gtφT (𝟙 T) g.b (e x) (fun q => gw w q z (J (q ≫ φ)) (J' q))`.

Rewrite `p` using `[Category.id_comp]`. Conclude with `(congrArg (fun q => val (g₀.s x) q z J) (Category.id_comp _).symm).trans (v.trans (congrArg₂ (· * ·) p rfl))`.
-/
theorem rel_of_pmaps {g : GtPt D T} {g₀ : GtPtF D₀ F}
    (hc : ∀ x k, DegPre.gtφT D T g.b (e x) k ≫ φ = ρ.left ≫ DegPre.gtφ D₀ F g₀.b x k)
    (H : ∀ x, PMaps w _ _ DegPre.gtε (g.s (e x)) (LB.pullGen _ _ _ (g₀.s x) ρ.left) (𝟙 _)) : Rel gp w e ρ g g₀ := by
  refine ⟨Over.OverMorphism.ext (hc 0 2), fun x z J J' hJ hJ' h hh => ?_⟩
  obtain rfl : h = _ := funext hh
  have v := CubTransport.val_pmaps (fun k => (hc x k).trans (Category.id_comp _).symm) (H x) (𝟙 _) hJ hJ'
  rw [val_pull hJ, Category.id_comp] at v
  have p := FormalPoint.prod_gtφT (𝟙 T) g.b (e x) (fun q => gw w q z (J (q ≫ φ)) (J' q))
  rw [Category.id_comp] at p
  exact (congrArg (fun q => val (g₀.s x) q z J) (Category.id_comp _).symm).trans (v.trans (congrArg₂ (· * ·) p rfl))

/- English proof (translation)
Establish `hb : g''.b = g.b * g'.b` using `push_injective gp T (by`. Rewrite using `[map_mul, r.1, r'.1, r''.1, h₀.1]`. Conclude with `MonObj.comp_mul _ _ _)`. Use `⟨hb, fun χ => corr_of_val D.P.isLB fun z J' hJ' => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `he χ`.

Take `⟨J, hJ⟩` from `TLinPf.idx_exists D₀.P.L D₀.P.isLB z`. Establish `a` using `((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D₀.cub ρ hJ _ _ _))).symm.trans ((val_corr hJ (h₀.2 x) ρ.left).trans (val_mul hJ _ _ _))`. Establish `c` using `cubV_push gp hG D.P.isAb D₀.cub D.cub hw (cP D T (e x)) g.b g'.b hJ hJ' _ (fun _ => rfl)`. Rewrite `c` using `[hc, r.1, r'.1]`. Establish `b` using `r.2 x z J J' hJ hJ' _ (fun _ => rfl)`.

Establish `b'` using `r'.2 x z J J' hJ hJ' _ (fun _ => rfl)`. Establish `b''` using `r''.2 x z J J' hJ hJ' _ (fun _ => rfl)`. Establish `a'` using `(congrArg₂ (· * ·) b'' c).symm.trans (a.trans (congrArg₂ (· * ·) b b'))`. Establish `v` using `val_cub D.cub (𝟙 T) hJ' (cP D T (e x)) g.b g'.b`. Rewrite `v` using `[Category.id_comp, Category.id_comp, Category.id_comp]`.

Use `((val_mul hJ' _ _ _).trans (congrArg₂ (· * ·) rfl v)).trans (Eq.trans ?_ (val_mul hJ' _ _ _).symm)` and prove the remaining obligations. Generalize the expression as in `val (g''.s (e x)) (𝟙 _) z J' = s'' at a' ⊢`. Rewrite `a'` using `[hb, ← _root_.mul_assoc (cP D T (e x))]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Establish `a''` using `congrArg Additive.ofMul a'`.

Simplify using `only [ofMul_mul, ofMul_inv] at a'' ⊢`. Take the linear combination `(norm := abel) a''`.
-/
theorem isAdd_of_rel (hG : GlobalFnsSt) (hw : PGen w)
    (hc : ∀ x, pushHom gp T (cP D T (e x)) = ρ ≫ cP D₀ _ x) (he : Function.Surjective e)
    {g g' g'' : GtPt D T} {g₀ g₀' g₀'' : GtPtF D₀ F} (r : Rel gp w e ρ g g₀) (r' : Rel gp w e ρ g' g₀')
    (r'' : Rel gp w e ρ g'' g₀'') (h₀ : g₀.IsAdd g₀' g₀'') : g.IsAdd g' g'' := by
  have hb : g''.b = g.b * g'.b := push_injective gp T (by
    rw [map_mul, r.1, r'.1, r''.1, h₀.1]; exact MonObj.comp_mul _ _ _)
  refine ⟨hb, fun χ => corr_of_val D.P.isLB fun z J' hJ' => ?_⟩
  obtain ⟨x, rfl⟩ := he χ
  obtain ⟨J, hJ⟩ := TLinPf.idx_exists D₀.P.L D₀.P.isLB z
  have a := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cub D₀.cub ρ hJ _ _ _))).symm.trans
    ((val_corr hJ (h₀.2 x) ρ.left).trans (val_mul hJ _ _ _))
  have c := cubV_push gp hG D.P.isAb D₀.cub D.cub hw (cP D T (e x)) g.b g'.b hJ hJ' _ (fun _ => rfl)
  rw [hc, r.1, r'.1] at c
  have b := r.2 x z J J' hJ hJ' _ (fun _ => rfl)
  have b' := r'.2 x z J J' hJ hJ' _ (fun _ => rfl)
  have b'' := r''.2 x z J J' hJ hJ' _ (fun _ => rfl)
  have a' := (congrArg₂ (· * ·) b'' c).symm.trans (a.trans (congrArg₂ (· * ·) b b'))
  have v := val_cub D.cub (𝟙 T) hJ' (cP D T (e x)) g.b g'.b
  rw [Category.id_comp, Category.id_comp, Category.id_comp] at v
  refine ((val_mul hJ' _ _ _).trans (congrArg₂ (· * ·) rfl v)).trans (Eq.trans ?_ (val_mul hJ' _ _ _).symm)
  generalize val (g''.s (e x)) (𝟙 _) z J' = s'' at a' ⊢
  rw [hb, ← _root_.mul_assoc (cP D T (e x))] at a'
  apply Additive.ofMul.injective
  have a'' := congrArg Additive.ofMul a'
  simp only [ofMul_mul, ofMul_inv] at a'' ⊢
  linear_combination (norm := abel) a''

/- English proof (translation)
Use `oa.onB.hom a` as an intermediate fact. Use `oa.onB.hom (star a)` as an intermediate fact. Use `oa₀.onB.hom a` as an intermediate fact. Use `oa₀.onB.hom (star a)` as an intermediate fact. Establish `hr` using `oa₀.onB.rosati (star a)`.

Rewrite `hr` using `[star_star]`. Take `⟨u₀, hu₀, n₀⟩` from `exists_ros hG D₀.P.isAb D₀.P.isLB _ _ hr`. Establish `hb : g'.b = g.b ≫ oa.onB.act a` using `push_injective gp T (by`. Rewrite using `[push_act gp (ho a), r.1, r'.1, h₀.1, Category.assoc])`. Use `⟨hb, fun u hu n χ => corr_of_val D.P.isLB fun z J' hJ' => ?_⟩` and prove the remaining obligations.

Take `⟨x, rfl⟩` from `he χ`. Take `⟨J, hJ⟩` from `TLinPf.idx_exists D₀.P.L D₀.P.isLB z`. Establish `v₀ : val (LB.pullGen D₀.P.L _ _ u₀ (lift (DegPre.cF D₀ F x) g₀.b).left) ρ.left z J = val₂ u₀ (T` using `Over.mk (T.hom ≫ f)) z J (ρ ≫ cP D₀ _ x) (ρ ≫ g₀.b) := by`. Use `(val_pull hJ _ _ _).trans ?_` and prove the remaining obligations. Rewrite using `[← Over.comp_left, comp_lift]`.

Both sides reduce to the same expression. Establish `k` using `((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl v₀)).symm.trans (val_corr hJ (h₀.2 u₀ hu₀ n₀ x) ρ.left)`. Establish `c` using `ros_push gp hG D.P.isAb D₀.P.isLB D.P.isLB hw (ho (star a)) (ho a) u₀ hu₀ n₀ u hu n (cP D T (e x)) g.b hJ hJ' _ (fun _ => rfl)`. Rewrite `c` using `[hc, r.1]`. Establish `b` using `r.2 (star a • x) z J J' hJ hJ' _ (fun _ => rfl)`.

Establish `b'` using `r'.2 x z J J' hJ hJ' _ (fun _ => rfl)`. Establish `k'` using `(congrArg₂ (· * ·) b c).symm.trans (k.trans b')`. Establish `cf : cP D T (star a • e x) = cP D T (e x) ≫ oa.onB.act (star a)`. Rewrite using `[cP, oa.c_lin, ← Category.assoc]`. Both sides reduce to the same expression.

Establish `v : val (LB.pullGen D.P.L _ _ u (lift (DegPre.cT D T (e x)) g.b).left) (𝟙 _) z J' = val₂ u z J' (cP D T (e x)) g.b`. Use `(val_pull hJ' _ _ _).trans ?_` and prove the remaining obligations. Rewrite using `[Category.id_comp]`. Both sides reduce to the same expression. Use `((val_mul hJ' _ _ _).trans (congrArg₂ (· * ·) rfl v)).trans ?_` and prove the remaining obligations.

Rewrite `k'` using `[hl]`. Generalize the expression as in `val (g'.s (e x)) (𝟙 _) z J' = s' at k' ⊢`. Generalize the expression as in `val (g.s (star a • e x)) (𝟙 _) z J' = s at k' ⊢`. Rewrite `k'` using `[hb, cf]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Establish `k''` using `congrArg Additive.ofMul k'`. Simplify using `only [ofMul_mul, ofMul_inv] at k'' ⊢`. Take the linear combination `(norm := abel) k''`.
-/
theorem isSmulPt_of_rel (hG : GlobalFnsSt) (hw : PGen w)
    (hc : ∀ x, pushHom gp T (cP D T (e x)) = ρ ≫ cP D₀ _ x) (he : Function.Surjective e)
    {O : Type} [CommRing O] [StarRing O] [Module O D.X] [Module O D₀.X] (oa : D.OAct O) (oa₀ : D₀.OAct O)
    (hl : ∀ (a : O) x, e (a • x) = a • e x) (ho : ∀ a, (oa.onB.act a).left ≫ φ = φ ≫ (oa₀.onB.act a).left) (a : O)
    {g g' : GtPt D T} {g₀ g₀' : GtPtF D₀ F} (r : Rel gp w e ρ g g₀) (r' : Rel gp w e ρ g' g₀')
    (h₀ : GtAct oa₀ a g₀ g₀') : FormalPoint.IsSmulPt oa a g g' := by
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  have := oa₀.onB.hom a
  have := oa₀.onB.hom (star a)
  have hr := oa₀.onB.rosati (star a)
  rw [star_star] at hr
  obtain ⟨u₀, hu₀, n₀⟩ := exists_ros hG D₀.P.isAb D₀.P.isLB _ _ hr
  have hb : g'.b = g.b ≫ oa.onB.act a := push_injective gp T (by
    rw [push_act gp (ho a), r.1, r'.1, h₀.1, Category.assoc])
  refine ⟨hb, fun u hu n χ => corr_of_val D.P.isLB fun z J' hJ' => ?_⟩
  obtain ⟨x, rfl⟩ := he χ
  obtain ⟨J, hJ⟩ := TLinPf.idx_exists D₀.P.L D₀.P.isLB z
  have v₀ : val (LB.pullGen D₀.P.L _ _ u₀ (lift (DegPre.cF D₀ F x) g₀.b).left) ρ.left z J =
      val₂ u₀ (T := Over.mk (T.hom ≫ f)) z J (ρ ≫ cP D₀ _ x) (ρ ≫ g₀.b) := by
    refine (val_pull hJ _ _ _).trans ?_
    rw [← Over.comp_left, comp_lift]; rfl
  have k := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl v₀)).symm.trans
    (val_corr hJ (h₀.2 u₀ hu₀ n₀ x) ρ.left)
  have c := ros_push gp hG D.P.isAb D₀.P.isLB D.P.isLB hw (ho (star a)) (ho a) u₀ hu₀ n₀ u hu n (cP D T (e x)) g.b
    hJ hJ' _ (fun _ => rfl)
  rw [hc, r.1] at c
  have b := r.2 (star a • x) z J J' hJ hJ' _ (fun _ => rfl)
  have b' := r'.2 x z J J' hJ hJ' _ (fun _ => rfl)
  have k' := (congrArg₂ (· * ·) b c).symm.trans (k.trans b')
  have cf : cP D T (star a • e x) = cP D T (e x) ≫ oa.onB.act (star a) := by
    rw [cP, oa.c_lin, ← Category.assoc]; rfl
  have v : val (LB.pullGen D.P.L _ _ u (lift (DegPre.cT D T (e x)) g.b).left) (𝟙 _) z J' =
      val₂ u z J' (cP D T (e x)) g.b := by
    refine (val_pull hJ' _ _ _).trans ?_
    rw [Category.id_comp]; rfl
  refine ((val_mul hJ' _ _ _).trans (congrArg₂ (· * ·) rfl v)).trans ?_
  rw [hl] at k'
  generalize val (g'.s (e x)) (𝟙 _) z J' = s' at k' ⊢
  generalize val (g.s (star a • e x)) (𝟙 _) z J' = s at k' ⊢
  rw [hb, cf] at k'
  apply Additive.ofMul.injective
  have k'' := congrArg Additive.ofMul k'
  simp only [ofMul_mul, ofMul_inv] at k'' ⊢
  linear_combination (norm := abel) k''

end Data

end GlobalTheory.ConstGrp
