import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalTau
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymTau
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {Lr : RigLB A} (c : CubicalStr A Lr)

/- English proof (translation)
Establish `he : zero2 A ≫ (A ⊗ A).hom = 𝟙 S` using `Over.w (lift η[A] η[A])`. Establish `hp : Function.Surjective (A ⊗ A).hom.appTop.hom`. Use `surj_comp (surj_snd hG hA A) ((hG _ _ hA).2)` as an intermediate fact. Rewrite `this` using `[Over.w (snd A A)]`. Then use the resulting hypothesis. Conclude with `gen_unique' Lr.isLB hF (A ⊗ A).hom (zero2 A) he hp hu hu' h0 T.left (lift x y).left z J hJ`.
-/
theorem gen_eq₂ (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → ((A ⊗ A).left ⟶ A.left)} {ε : K → ℤ} {φ' : K' → ((A ⊗ A).left ⟶ A.left)} {ε' : K' → ℤ}
    (hF : FormEq φ' ε' φ ε) {u : LB.Gen (LB.LinComb Lr.L φ ε)} {u' : LB.Gen (LB.LinComb Lr.L φ' ε')}
    (hu : u.IsGen) (hu' : u'.IsGen) (h0 : ∀ y J, Good Lr.L y J → val u (zero2 A) y J = val u' (zero2 A) y J)
    {T : Over S} {z : T.left} {J} (hJ : Good Lr.L z J) (x y : T ⟶ A) :
    val u (lift x y).left z J = val u' (lift x y).left z J := by
  have he : zero2 A ≫ (A ⊗ A).hom = 𝟙 S := Over.w (lift η[A] η[A])
  have hp : Function.Surjective (A ⊗ A).hom.appTop.hom := by
    have := surj_comp (surj_snd hG hA A) ((hG _ _ hA).2)
    rwa [Over.w (snd A A)] at this
  exact gen_unique' Lr.isLB hF (A ⊗ A).hom (zero2 A) he hp hu hu' h0 T.left (lift x y).left z J hJ

omit [IsCommMonObj A] in
/- English proof (translation)
Use `val_corr hJ h₀ (𝟙 _)` as an intermediate fact. Rewrite `this` using `[val_pull hJ, Category.id_comp, val_one]`. Then use the resulting hypothesis.
-/
theorem val_zero2 {f g : A ⟶ A} (u : LB.Gen (LB.LinComb Lr.L (rosatiφ A f g) rosatiε))
    (h₀ : LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (zero2 A)) (LB.oneGen Lr.L)) {y : (𝟙_ (Over S)).left} {J}
    (hJ : Good Lr.L y J) : val u (zero2 A) y J = 1 := by
  have := val_corr hJ h₀ (𝟙 _)
  rwa [val_pull hJ, Category.id_comp, val_one] at this

/- English proof (translation)
Establish `hv : ∀ {T' : Over S} {z : T'.left} {J}, Good Lr.L z J → ∀ x y : T' ⟶ A, val (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u' (lift (snd A A) (fst A A)).left) u) (lift x y).left z J = val₂ u' z J y x * val₂ u z J x y` using `fun hJ x y => by`. Use `(val_mul hJ _ _ _).trans ?_` and prove the remaining obligations. Rewrite using `[val_pull hJ, ← Over.comp_left, comp_lift, lift_snd, lift_fst]`. Both sides reduce to the same expression. Use `(hv hJ x y).symm.trans ((gen_eq₂ hG hA (u' := LB.oneGen Lr.L) (fun U _ h => ?_) (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu' _) hu) (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm) (fun y I hI …` and prove the remaining obligations.

Establish `p₁` using `prod_ros g f (snd A A) (fst A A) h`. Establish `p₂` using `prod_ros f g (fst A A) (snd A A) h`. Rewrite `p₂` using `[lift_fst_snd]`. Simplify using `only [Over.id_left, Category.id_comp] at p₂`. Use `(Fintype.prod_empty _).trans (Eq.trans ?_ (DVR.prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := U) _ p₁ p₂).symm)` and prove the remaining obligations.

Rewrite using `[mul_comm (snd A A ≫ g) (fst A A), mul_comm (snd A A) (fst A A ≫ f)]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_one]`. Normalize the expressions using the abelian group laws. Use `hv hI η[A] η[A]` as an intermediate fact.

Simplify using `only [val₂] at this`. Rewrite using `[this, val_zero2 u' h₀' hI, val_zero2 u h₀ hI, _root_.mul_one, val_one]`.
-/
theorem ros_swap (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (f g : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (u : LB.Gen (LB.LinComb Lr.L (rosatiφ A f g) rosatiε)) (hu : u.IsGen)
    (h₀ : LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (zero2 A)) (LB.oneGen Lr.L))
    (u' : LB.Gen (LB.LinComb Lr.L (rosatiφ A g f) rosatiε)) (hu' : u'.IsGen)
    (h₀' : LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u' (zero2 A)) (LB.oneGen Lr.L))
    {T : Over S} {z : T.left} {J} (hJ : Good Lr.L z J) (x y : T ⟶ A) :
    val₂ u' z J y x * val₂ u z J x y = 1 := by
  have hv : ∀ {T' : Over S} {z : T'.left} {J}, Good Lr.L z J → ∀ x y : T' ⟶ A,
      val (LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u' (lift (snd A A) (fst A A)).left) u) (lift x y).left z J =
        val₂ u' z J y x * val₂ u z J x y := fun hJ x y => by
    refine (val_mul hJ _ _ _).trans ?_
    rw [val_pull hJ, ← Over.comp_left, comp_lift, lift_snd, lift_fst]; rfl
  refine (hv hJ x y).symm.trans ((gen_eq₂ hG hA (u' := LB.oneGen Lr.L) (fun U _ h => ?_)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu' _) hu)
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
    (fun y I hI => ?_) hJ x y).trans (val_one _))
  · have p₁ := prod_ros g f (snd A A) (fst A A) h
    have p₂ := prod_ros f g (fst A A) (snd A A) h
    rw [lift_fst_snd] at p₂
    simp only [Over.id_left, Category.id_comp] at p₂
    refine (Fintype.prod_empty _).trans (Eq.trans ?_ (DVR.prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := U) _ p₁ p₂).symm)
    rw [mul_comm (snd A A ≫ g) (fst A A), mul_comm (snd A A) (fst A A ≫ f)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_one]
    abel
  · have := hv hI η[A] η[A]
    simp only [val₂] at this
    rw [this, val_zero2 u' h₀' hI, val_zero2 u h₀ hI, _root_.mul_one, val_one]

/- English proof (translation)
Set `t` to `LB.mulGen Lr.L _ _ _ _ (LB.pullGen Lr.L (thφ A (x3 A)) thε c.t (lift (snd A A ≫ g₁) (lift (snd A A ≫ g₂) (fst A A))).left) (LB.invGen Lr.L _ _ (LB.pullGen Lr.L (thφ A (x3 A)) thε c.t (lift (fst A A ≫ f₁) (lift (fst A A ≫ f₂) (snd A A))).left))`. Establish `hv : ∀ {T' : Over S} {z : T'.left} {J}, Good Lr.L z J → ∀ x y : T' ⟶ A, val t (lift x y).left z J = cubV c z J (y ≫ g₁) (y ≫ g₂) x * (cubV c z J (x ≫ f₁) (x ≫ f₂) y)⁻¹` using `fun hJ x y => by`. Use `(val_mul hJ _ _ _).trans ?_` and prove the remaining obligations. Use `congrArg₂ (· * ·) ((val_cub c _ hJ _ _ _).trans ?_) ((val_inv _ _).trans (congrArg _ ((val_cub c _ hJ _ _ _).trans ?_)))` and prove the remaining obligations. Simplify using `only [lift_snd_assoc, lift_fst]`.

Simplify using `only [lift_fst_assoc, lift_snd]`. Establish `hm : ∀ {T' : Over S} {z : T'.left} {J}, Good Lr.L z J → ∀ x y : T' ⟶ A, val (LB.mulGen Lr.L _ _ _ _ u₁ u₂) (lift x y).left z J = val₂ u₁ z J x y * val₂ u₂ z J x y` using `fun hJ x y => val_mul hJ _ _ _`. Use `(hm hJ y w).symm.trans ((gen_eq₂ hG hA (u' := t) (fun U _ h => ?_) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu₁ hu₂) (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ c.isGen _) (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ c.isGen _))) (fun y I hI => ?_) hJ y w).trans (hv …` and prove the remaining obligations. Establish `p₁` using `prod_ros f₁ g₁ (fst A A) (snd A A) h`. Establish `p₂` using `prod_ros f₂ g₂ (fst A A) (snd A A) h`.

Rewrite `p₁`, `p₂` using `[lift_fst_snd]`. Simplify using `only [Over.id_left, Category.id_comp] at p₁ p₂`. Use `(DVR.prod_sum₂ (K := thK) (K' := thK) (U := U) _ (prod_cub _ _ _ h) (DVR.prod_neg _ _ (prod_cub _ _ _ h))).trans (Eq.trans ?_ (DVR.prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := U) _ p₁ p₂).symm)` and prove the remaining obligations. Establish `e₁ : (snd A A ≫ g₁) * (snd A A ≫ g₂) = snd A A` using `by rw [← MonObj.comp_mul, hg, Category.comp_id]`. Establish `e₂ : (fst A A ≫ f₁) * (fst A A ≫ f₂) = fst A A` using `by rw [← MonObj.comp_mul, hf, Category.comp_id]`.

Rewrite using `[e₁, e₂, mul_comm (snd A A) (fst A A), mul_comm (snd A A ≫ g₁) (fst A A), mul_comm (snd A A ≫ g₂) (fst A A)]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`. Normalize the expressions using the abelian group laws. Use `hv hI η[A] η[A]` as an intermediate fact.

Rewrite using `[this]`. Use `(val_mul hI _ _ _).trans ?_` and prove the remaining obligations. Rewrite using `[val_zero2 u₁ h₁ hI, val_zero2 u₂ h₂ hI, _root_.mul_one]`. Establish `C` using `isCub_cubV c hI`. Establish `o : (η[A] : 𝟙_ (Over S) ⟶ A) = 1` using `by simp [Hom.one_def]`.

Simplify using `only [o, MonObj.one_comp, C.face, inv_one, _root_.mul_one]`.
-/
theorem ros_sum (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (f₁ g₁ f₂ g₂ : A ⟶ A) [IsMonHom f₁] [IsMonHom g₁]
    [IsMonHom f₂] [IsMonHom g₂] (hf : f₁ * f₂ = 𝟙 A) (hg : g₁ * g₂ = 𝟙 A)
    (u₁ : LB.Gen (LB.LinComb Lr.L (rosatiφ A f₁ g₁) rosatiε)) (hu₁ : u₁.IsGen)
    (h₁ : LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u₁ (zero2 A)) (LB.oneGen Lr.L))
    (u₂ : LB.Gen (LB.LinComb Lr.L (rosatiφ A f₂ g₂) rosatiε)) (hu₂ : u₂.IsGen)
    (h₂ : LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u₂ (zero2 A)) (LB.oneGen Lr.L))
    {T : Over S} {z : T.left} {J} (hJ : Good Lr.L z J) (y w : T ⟶ A) :
    val₂ u₁ z J y w * val₂ u₂ z J y w = cubV c z J (w ≫ g₁) (w ≫ g₂) y * (cubV c z J (y ≫ f₁) (y ≫ f₂) w)⁻¹ := by
  let t := LB.mulGen Lr.L _ _ _ _
    (LB.pullGen Lr.L (thφ A (x3 A)) thε c.t (lift (snd A A ≫ g₁) (lift (snd A A ≫ g₂) (fst A A))).left)
    (LB.invGen Lr.L _ _ (LB.pullGen Lr.L (thφ A (x3 A)) thε c.t (lift (fst A A ≫ f₁) (lift (fst A A ≫ f₂) (snd A A))).left))
  have hv : ∀ {T' : Over S} {z : T'.left} {J}, Good Lr.L z J → ∀ x y : T' ⟶ A,
      val t (lift x y).left z J = cubV c z J (y ≫ g₁) (y ≫ g₂) x * (cubV c z J (x ≫ f₁) (x ≫ f₂) y)⁻¹ := fun hJ x y => by
    refine (val_mul hJ _ _ _).trans ?_
    refine congrArg₂ (· * ·) ((val_cub c _ hJ _ _ _).trans ?_) ((val_inv _ _).trans (congrArg _ ((val_cub c _ hJ _ _ _).trans ?_)))
    · simp only [lift_snd_assoc, lift_fst]
    · simp only [lift_fst_assoc, lift_snd]
  have hm : ∀ {T' : Over S} {z : T'.left} {J}, Good Lr.L z J → ∀ x y : T' ⟶ A,
      val (LB.mulGen Lr.L _ _ _ _ u₁ u₂) (lift x y).left z J = val₂ u₁ z J x y * val₂ u₂ z J x y :=
    fun hJ x y => val_mul hJ _ _ _
  refine (hm hJ y w).symm.trans ((gen_eq₂ hG hA (u' := t) (fun U _ h => ?_)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hu₁ hu₂)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ c.isGen _)
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ c.isGen _)))
    (fun y I hI => ?_) hJ y w).trans (hv hJ y w))
  · have p₁ := prod_ros f₁ g₁ (fst A A) (snd A A) h
    have p₂ := prod_ros f₂ g₂ (fst A A) (snd A A) h
    rw [lift_fst_snd] at p₁ p₂
    simp only [Over.id_left, Category.id_comp] at p₁ p₂
    refine (DVR.prod_sum₂ (K := thK) (K' := thK) (U := U) _ (prod_cub _ _ _ h)
      (DVR.prod_neg _ _ (prod_cub _ _ _ h))).trans (Eq.trans ?_ (DVR.prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := U) _ p₁ p₂).symm)
    have e₁ : (snd A A ≫ g₁) * (snd A A ≫ g₂) = snd A A := by rw [← MonObj.comp_mul, hg, Category.comp_id]
    have e₂ : (fst A A ≫ f₁) * (fst A A ≫ f₂) = fst A A := by rw [← MonObj.comp_mul, hf, Category.comp_id]
    rw [e₁, e₂, mul_comm (snd A A) (fst A A), mul_comm (snd A A ≫ g₁) (fst A A), mul_comm (snd A A ≫ g₂) (fst A A)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have := hv hI η[A] η[A]
    rw [this]
    refine (val_mul hI _ _ _).trans ?_
    rw [val_zero2 u₁ h₁ hI, val_zero2 u₂ h₂ hI, _root_.mul_one]
    have C := isCub_cubV c hI
    have o : (η[A] : 𝟙_ (Over S) ⟶ A) = 1 := by simp [Hom.one_def]
    simp only [o, MonObj.one_comp, C.face, inv_one, _root_.mul_one]

/- English proof (translation)
Substitute `e` using the available equality. Take `⟨t, ht, hv⟩` from `exists_gen Lr.isLB (φ' := GlobalTheory.PolDeg.lamPts x (a * b)) (ε' := GlobalTheory.PolDeg.negε) (fun U _ h => by`. Use `(DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := thK) (U := U) _ (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ rfl rfl) (DVR.prod_neg _ _ (prod_cub a b x h))).trans ?_` and prove the remaining obligations. Simplify using `only [GlobalTheory.PolDeg.lamPts, GlobalTheory.PolDeg.negε, Fin.prod_univ_four, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]`. Rewrite using `[mul_comm x a, mul_comm x (a * b)]`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_zpow]`. Use the proof step `abel)`. Use the proof step `(LB.mulGen Lr.L _ _ _ _ (LB.mulGen Lr.L _ _ _ _ t₁ t₂) (LB.invGen Lr.L _ _ (LB.pullGen Lr.L (thφ A (x3 A)) thε c.t (lift a (lift b x)).left)))`. Use the proof step `(DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ ht₁ ht₂) (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ c.isGen _)))`.

Use `⟨t, ht, fun p J hJ => ?_⟩` and prove the remaining obligations. Establish `hc` using `val_cub c (𝟙 T) hJ a b x`. Simplify using `only [Over.id_left, Category.id_comp] at hc`. Use `(hv _ _ p J hJ).trans ((val_mul hJ _ _ _).trans ?_)` and prove the remaining obligations. Rewrite using `[val_mul hJ]`.

Conclude with `congrArg (_ * ·) ((val_inv (z := p) (J := J) _ _).trans (congrArg (·⁻¹) hc))`.
-/
theorem exists_tauSum {T : Over S} (x a b w : T ⟶ A) (e : a * b = w)
    (t₁ : LB.Gen (LB.LinComb Lr.L (GlobalTheory.PolDeg.lamPts x a) GlobalTheory.PolDeg.negε)) (ht₁ : t₁.IsGen)
    (t₂ : LB.Gen (LB.LinComb Lr.L (GlobalTheory.PolDeg.lamPts b x) GlobalTheory.PolDeg.negε)) (ht₂ : t₂.IsGen) :
    ∃ t : LB.Gen (LB.LinComb Lr.L (GlobalTheory.PolDeg.lamPts x w) GlobalTheory.PolDeg.negε), t.IsGen ∧
      ∀ p J, Good Lr.L p J → val t (𝟙 _) p J = val t₁ (𝟙 _) p J * val t₂ (𝟙 _) p J * (cubV c p J a b x)⁻¹ := by
  subst e
  obtain ⟨t, ht, hv⟩ := exists_gen Lr.isLB (φ' := GlobalTheory.PolDeg.lamPts x (a * b)) (ε' := GlobalTheory.PolDeg.negε)
    (fun U _ h => by
      refine (DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := thK) (U := U) _
        (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ rfl rfl) (DVR.prod_neg _ _ (prod_cub a b x h))).trans ?_
      simp only [GlobalTheory.PolDeg.lamPts, GlobalTheory.PolDeg.negε, Fin.prod_univ_four, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.tail_cons]
      rw [mul_comm x a, mul_comm x (a * b)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      abel)
    (LB.mulGen Lr.L _ _ _ _ (LB.mulGen Lr.L _ _ _ _ t₁ t₂)
      (LB.invGen Lr.L _ _ (LB.pullGen Lr.L (thφ A (x3 A)) thε c.t (lift a (lift b x)).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ ht₁ ht₂)
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ c.isGen _)))
  refine ⟨t, ht, fun p J hJ => ?_⟩
  have hc := val_cub c (𝟙 T) hJ a b x
  simp only [Over.id_left, Category.id_comp] at hc
  refine (hv _ _ p J hJ).trans ((val_mul hJ _ _ _).trans ?_)
  rw [val_mul hJ]
  exact congrArg (_ * ·) ((val_inv (z := p) (J := J) _ _).trans (congrArg (·⁻¹) hc))

end GlobalTheory.SymTau

namespace GlobalTheory.SymTau

section Alg
variable {G U : Type} [CommGroup G] [CommGroup U] {θ : G → G → G → U} (C : IsCub θ)
include C

/- English proof (translation)
Establish `k` using `C.compat Y Y' a b`. Establish `sA` using `(C.s12 a b (Y * Y')).trans (C.s01 _ _ _)`. Establish `sB` using `(C.s12 a b Y).trans (C.s01 _ _ _)`. Establish `sC` using `(C.s12 a b Y').trans (C.s01 _ _ _)`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Establish `a₁` using `congrArg Additive.ofMul h₁`. Establish `a₂` using `congrArg Additive.ofMul h₂`. Establish `ak` using `congrArg Additive.ofMul k`. Establish `aA` using `congrArg Additive.ofMul sA`. Establish `aB` using `congrArg Additive.ofMul sB`.

Establish `aC` using `congrArg Additive.ofMul sC`. Simplify using `only [ofMul_mul, ofMul_inv] at a₁ a₂ ak aA aB aC ⊢`. Take the linear combination `(norm := abel) a₁ + a₂ - ak - aA + aB + aC`.
-/
theorem alg_first (Y Y' a b : G) (v₁ v₂ x₁ x₂ y₁ y₂ : U) (h₁ : v₁ * θ Y Y' a = x₁ * x₂) (h₂ : v₂ * θ Y Y' b = y₁ * y₂) :
    v₁ * v₂ * (θ a b (Y * Y'))⁻¹ * θ Y Y' (a * b) = x₁ * y₁ * (θ a b Y)⁻¹ * (x₂ * y₂ * (θ a b Y')⁻¹) := by
  have k := C.compat Y Y' a b
  have sA := (C.s12 a b (Y * Y')).trans (C.s01 _ _ _)
  have sB := (C.s12 a b Y).trans (C.s01 _ _ _)
  have sC := (C.s12 a b Y').trans (C.s01 _ _ _)
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul h₁; have a₂ := congrArg Additive.ofMul h₂; have ak := congrArg Additive.ofMul k
  have aA := congrArg Additive.ofMul sA; have aB := congrArg Additive.ofMul sB; have aC := congrArg Additive.ofMul sC
  simp only [ofMul_mul, ofMul_inv] at a₁ a₂ ak aA aB aC ⊢
  linear_combination (norm := abel) a₁ + a₂ - ak - aA + aB + aC

/- English proof (translation)
Establish `k₁` using `C.coc (a * b) a' b' Y`. Establish `k₂` using `C.coc a b a' Y`. Establish `k₃` using `C.coc (a * a') b b' Y`. Establish `k₄` using `C.coc a a' b Y`. Rewrite `k₁` using `[mul_right_comm a b a']`.

Rewrite `k₂` using `[mul_comm b a']`. Establish `s` using `C.s01 b a' Y`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Establish `a₁` using `congrArg Additive.ofMul h₁`. Establish `a₂` using `congrArg Additive.ofMul h₂`.

Establish `b₁` using `congrArg Additive.ofMul k₁`. Establish `b₂` using `congrArg Additive.ofMul k₂`. Establish `b₃` using `congrArg Additive.ofMul k₃`. Establish `b₄` using `congrArg Additive.ofMul k₄`. Establish `bs` using `congrArg Additive.ofMul s`.

Simplify using `only [ofMul_mul, ofMul_inv] at a₁ a₂ b₁ b₂ b₃ b₄ bs ⊢`. Take the linear combination `(norm := abel) a₁ + a₂ - b₁ + b₂ + b₃ - b₄ + bs`.
-/
theorem alg_second (Y a a' b b' : G) (v₁ v₂ x₁ x₂ y₁ y₂ : U) (h₁ : v₁ * θ a a' Y = x₁ * x₂)
    (h₂ : v₂ * θ b b' Y = y₁ * y₂) :
    v₁ * v₂ * (θ (a * a') (b * b') Y)⁻¹ * θ (a * b) (a' * b') Y = x₁ * y₁ * (θ a b Y)⁻¹ * (x₂ * y₂ * (θ a' b' Y)⁻¹) := by
  have k₁ := C.coc (a * b) a' b' Y
  have k₂ := C.coc a b a' Y
  have k₃ := C.coc (a * a') b b' Y
  have k₄ := C.coc a a' b Y
  rw [mul_right_comm a b a'] at k₁
  rw [mul_comm b a'] at k₂
  have s := C.s01 b a' Y
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul h₁; have a₂ := congrArg Additive.ofMul h₂
  have b₁ := congrArg Additive.ofMul k₁; have b₂ := congrArg Additive.ofMul k₂
  have b₃ := congrArg Additive.ofMul k₃; have b₄ := congrArg Additive.ofMul k₄; have bs := congrArg Additive.ofMul s
  simp only [ofMul_mul, ofMul_inv] at a₁ a₂ b₁ b₂ b₃ b₄ bs ⊢
  linear_combination (norm := abel) a₁ + a₂ - b₁ + b₂ + b₃ - b₄ + bs

/- English proof (translation)
Establish `s₁` using `(C.s12 a b Ya).trans (C.s01 _ _ _)`. Establish `s₂` using `(C.s12 p q Y).trans (C.s01 _ _ _)`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Establish `a₁` using `congrArg Additive.ofMul e₁`. Establish `a₂` using `congrArg Additive.ofMul e₂`.

Establish `a₃` using `congrArg Additive.ofMul ra`. Establish `a₄` using `congrArg Additive.ofMul sw`. Establish `c₁` using `congrArg Additive.ofMul s₁`. Establish `c₂` using `congrArg Additive.ofMul s₂`. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_one] at a₁ a₂ a₃ a₄ c₁ c₂ ⊢`.

Take the linear combination `(norm := abel) a₁ - a₂ + a₃ + a₄ - c₁ + c₂`.
-/
theorem alg_bal (Y Ya a b p q : G) (v₁ v₂ w₁ w₂ uz ua ub ub' : U) (e₁ : v₁ * ua = w₁) (e₂ : w₂ * ub' = v₂)
    (ra : uz * θ Y p q = θ Ya a b * (ua * ub)) (sw : ub' * ub = 1) :
    v₁ * v₂ * (θ a b Ya)⁻¹ * uz = w₁ * w₂ * (θ p q Y)⁻¹ := by
  have s₁ := (C.s12 a b Ya).trans (C.s01 _ _ _)
  have s₂ := (C.s12 p q Y).trans (C.s01 _ _ _)
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul e₁; have a₂ := congrArg Additive.ofMul e₂; have a₃ := congrArg Additive.ofMul ra
  have a₄ := congrArg Additive.ofMul sw; have c₁ := congrArg Additive.ofMul s₁; have c₂ := congrArg Additive.ofMul s₂
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at a₁ a₂ a₃ a₄ c₁ c₂ ⊢
  linear_combination (norm := abel) a₁ - a₂ + a₃ + a₄ - c₁ + c₂

/- English proof (translation)
Establish `s` using `C.s01 b' a' Z`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Establish `a₁` using `congrArg Additive.ofMul e₁`. Establish `a₂` using `congrArg Additive.ofMul e₂`. Establish `a₃` using `congrArg Additive.ofMul sw`.

Establish `a₄` using `congrArg Additive.ofMul sm`. Establish `c₁` using `congrArg Additive.ofMul s`. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_one] at a₁ a₂ a₃ a₄ c₁ ⊢`. Take the linear combination `(norm := abel) -a₁ + a₂ - a₃ + a₄ - c₁`.
-/
theorem alg_symm (Y Z a b a' b' : G) (v₁ v₂ v₃ v₄ u₁ u₁' u₀ : U) (e₁ : v₄ * u₁ = v₁) (e₂ : v₂ * u₁' = v₃)
    (sw : u₁' * u₀ = 1) (sm : u₁ * u₀ = θ a b Y * (θ b' a' Z)⁻¹) :
    v₁ * v₂ * (θ a b Y)⁻¹ = v₃ * v₄ * (θ a' b' Z)⁻¹ := by
  have s := C.s01 b' a' Z
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul e₁; have a₂ := congrArg Additive.ofMul e₂; have a₃ := congrArg Additive.ofMul sw
  have a₄ := congrArg Additive.ofMul sm; have c₁ := congrArg Additive.ofMul s
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at a₁ a₂ a₃ a₄ c₁ ⊢
  linear_combination (norm := abel) -a₁ + a₂ - a₃ + a₄ - c₁

end Alg

end GlobalTheory.SymTau

namespace GlobalTheory.SymTau

/- English proof (translation)
Introduce `R _ _ B _ _ hA M cub O _ _ act hros X _ _ c cadd clin w0 hw τ hτ`. Take `⟨hgen, hadd1, hadd2, hbal⟩` from `hτ`. Establish `hG` using `GlobalTheory.globalFns_holds`. Establish `cw : ∀ z, c (w0 • z) * c (star w0 • z) = c z` using `fun z => by rw [← cadd, ← add_smul, hw, one_smul]`. Use `choose τ' hτ'g hτ'v using fun y z => exists_tauSum cub (c y) (c (w0 • z)) (c (star w0 • z)) (c z) (cw z) (τ y (w0 • z)) (hgen _ _) (τ (star w0 • z) y) (hgen _ _)`.

Use `⟨τ', ⟨hτ'g, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `y y' z p J hJ`. Establish `ey : cubV cub p J (c (w0 • z)) (c (star w0 • z)) (c (y + y')) = cubV cub p J (c (w0 • z)) (c (star w0 • z)) (c y * c y')` using `by rw [cadd]`. Establish `ez : cubV cub p J (c y) (c y') (c z) = cubV cub p J (c y) (c y') (c (w0 • z) * c (star w0 • z))`. Rewrite using `[cw z]`.

Rewrite using `[hτ'v _ _ p J hJ, hτ'v _ _ p J hJ, hτ'v _ _ p J hJ, ey, ez]`. Conclude with `alg_first (isCub_cubV cub hJ) _ _ _ _ _ _ _ _ _ _ (hadd1 y y' (w0 • z) p J hJ) (hadd2 (star w0 • z) y y' p J hJ)`. Introduce `y z z' p J hJ`. Establish `v₁ : val (τ y (w0 • (z + z'))) (𝟙 _) p J = val (τ y (w0 • z + w0 • z')) (𝟙 _) p J` using `by rw [smul_add]`. Establish `v₂ : val (τ (star w0 • (z + z')) y) (𝟙 _) p J = val (τ (star w0 • z + star w0 • z') y) (𝟙 _) p J`.

Rewrite using `[smul_add]`. Establish `ea : cubV cub p J (c (w0 • (z + z'))) (c (star w0 • (z + z'))) (c y) = cubV cub p J (c (w0 • z) * c (w0 • z')) (c (star w0 • z) * c (star w0 • z')) (c y)`. Rewrite using `[smul_add, smul_add, cadd, cadd]`. Establish `ez : cubV cub p J (c z) (c z') (c y) = cubV cub p J (c (w0 • z) * c (star w0 • z)) (c (w0 • z') * c (star w0 • z')) (c y)` using `by rw [cw z, cw z']`. Rewrite using `[hτ'v _ _ p J hJ, hτ'v _ _ p J hJ, hτ'v _ _ p J hJ, v₁, v₂, ea, ez]`.

Conclude with `alg_second (isCub_cubV cub hJ) _ _ _ _ _ _ _ _ _ _ _ (hadd2 y (w0 • z) (w0 • z') p J hJ) (hadd1 (star w0 • z) (star w0 • z') y p J hJ)`. Introduce `a u hu hu0 y z p J hJ haveI := act.hom a haveI := act.hom (star a)`. Take `⟨ub, hub, hub0⟩` from `exists_ros hG hA M.isLB (act.act (star a)) (act.act a) (by simpa only [star_star] using hros (star a))`. Establish `hb` using `hbal (star a)`. Rewrite `hb` using `[star_star]`.

Establish `q₁ : star a • w0 • z = w0 • star a • z` using `smul_comm _ _ _`. Establish `q₂ : star a • star w0 • z = star w0 • star a • z` using `smul_comm _ _ _`. Establish `e₁` using `hbal a u hu hu0 y (w0 • z) p J hJ`. Establish `e₂` using `hb ub hub hub0 (star w0 • z) y p J hJ`. Establish `ra` using `(ros_add cub hG hA (act.act a) (act.act (star a)) u hu hu0 hJ (c (w0 • z)) (c (star w0 • z)) (c y)).2`.

Establish `sw` using `ros_swap hG hA (act.act a) (act.act (star a)) u hu hu0 ub hub hub0 hJ (c y) (c (star w0 • z))`. Simplify using `only [val₂] at ra sw`. Rewrite `ra` using `[← clin, ← clin, ← clin, q₁, q₂, cw z]`. Rewrite `e₁` using `[q₁]`. Rewrite `e₂` using `[q₂]`.

Rewrite using `[hτ'v _ _ p J hJ, hτ'v _ _ p J hJ]`. Conclude with `alg_bal (isCub_cubV cub hJ) _ _ _ _ _ _ _ _ _ _ _ _ _ _ e₁ e₂ ra sw`. Introduce `y z p J hJ haveI := act.hom w0 haveI := act.hom (star w0)`. Take `⟨u₀, hu₀, hu₀0⟩` from `exists_ros hG hA M.isLB (act.act w0) (act.act (star w0)) (hros w0)`. Take `⟨u₁, hu₁, hu₁0⟩` from `exists_ros hG hA M.isLB (act.act (star w0)) (act.act w0) (by simpa only [star_star] using hros (star w0))`.

Establish `hb` using `hbal (star w0)`. Rewrite `hb` using `[star_star]`. Establish `e₁` using `hb u₁ hu₁ hu₁0 y z p J hJ`. Establish `e₂` using `hb u₁ hu₁ hu₁0 z y p J hJ`. Establish `sw` using `ros_swap hG hA (act.act w0) (act.act (star w0)) u₀ hu₀ hu₀0 u₁ hu₁ hu₁0 hJ (c y) (c z)`.

Establish `hf : act.act (star w0) * act.act w0 = 𝟙 B`. Rewrite using `[← act.map_one, ← hw, add_comm]`. Conclude with `(act.map_add _ _).symm`. Establish `hg : act.act w0 * act.act (star w0) = 𝟙 B`. Rewrite using `[← act.map_one, ← hw]`.

Conclude with `(act.map_add _ _).symm`. Establish `sm` using `ros_sum cub hG hA (act.act (star w0)) (act.act w0) (act.act w0) (act.act (star w0)) hf hg u₁ hu₁ hu₁0 u₀ hu₀ hu₀0 hJ (c y) (c z)`. Simplify using `only [val₂] at sw sm`. Rewrite `sm` using `[← clin, ← clin, ← clin, ← clin]`. Rewrite using `[hτ'v _ _ p J hJ, hτ'v _ _ p J hJ]`.

Conclude with `alg_symm (isCub_cubV cub hJ) _ _ _ _ _ _ _ _ _ _ _ _ _ e₁ e₂ sw sm`.
-/
theorem symm_of_bal : ∀ (R : Type) [CommRing R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B →
    ∀ (M : RigLB B) (cub : CubicalStr B M) (O : Type) [CommRing O] [StarRing O] (act : RingAct B O),
    (∀ a : O, RosatiAdj B M.L (act.act a) (act.act (star a))) →
    ∀ (X : Type) [AddCommGroup X] [Module O X] (c : X → (𝟙_ (Over (Sp R)) ⟶ B)), (∀ y y', c (y + y') = c y * c y') →
    (∀ (a : O) (y : X), c (a • y) = c y ≫ act.act a) → ∀ w0 : O, w0 + star w0 = 1 →
    ∀ τ : ∀ y z : X, LB.Gen (LB.LinComb M.L (GlobalTheory.PolDeg.lamPts (c y) (c z)) GlobalTheory.PolDeg.negε), GlobalTheory.UTau0.BalTau M cub act c τ →
    ∃ τ' : ∀ y z : X, LB.Gen (LB.LinComb M.L (GlobalTheory.PolDeg.lamPts (c y) (c z)) GlobalTheory.PolDeg.negε), GlobalTheory.UTau0.BalTau M cub act c τ' ∧
      ∀ y z p J, Good M.L p J → val (τ' y z) (𝟙 _) p J = val (τ' z y) (𝟙 _) p J := by
  intro R _ _ B _ _ hA M cub O _ _ act hros X _ _ c cadd clin w0 hw τ hτ
  obtain ⟨hgen, hadd1, hadd2, hbal⟩ := hτ
  have hG := GlobalTheory.globalFns_holds
  have cw : ∀ z, c (w0 • z) * c (star w0 • z) = c z := fun z => by rw [← cadd, ← add_smul, hw, one_smul]
  choose τ' hτ'g hτ'v using fun y z => exists_tauSum cub (c y) (c (w0 • z)) (c (star w0 • z)) (c z) (cw z)
    (τ y (w0 • z)) (hgen _ _) (τ (star w0 • z) y) (hgen _ _)
  refine ⟨τ', ⟨hτ'g, ?_, ?_, ?_⟩, ?_⟩
  · intro y y' z p J hJ
    have ey : cubV cub p J (c (w0 • z)) (c (star w0 • z)) (c (y + y')) =
        cubV cub p J (c (w0 • z)) (c (star w0 • z)) (c y * c y') := by rw [cadd]
    have ez : cubV cub p J (c y) (c y') (c z) = cubV cub p J (c y) (c y') (c (w0 • z) * c (star w0 • z)) := by
      rw [cw z]
    rw [hτ'v _ _ p J hJ, hτ'v _ _ p J hJ, hτ'v _ _ p J hJ, ey, ez]
    exact alg_first (isCub_cubV cub hJ) _ _ _ _ _ _ _ _ _ _ (hadd1 y y' (w0 • z) p J hJ)
      (hadd2 (star w0 • z) y y' p J hJ)
  · intro y z z' p J hJ
    have v₁ : val (τ y (w0 • (z + z'))) (𝟙 _) p J = val (τ y (w0 • z + w0 • z')) (𝟙 _) p J := by rw [smul_add]
    have v₂ : val (τ (star w0 • (z + z')) y) (𝟙 _) p J = val (τ (star w0 • z + star w0 • z') y) (𝟙 _) p J := by
      rw [smul_add]
    have ea : cubV cub p J (c (w0 • (z + z'))) (c (star w0 • (z + z'))) (c y) =
        cubV cub p J (c (w0 • z) * c (w0 • z')) (c (star w0 • z) * c (star w0 • z')) (c y) := by
      rw [smul_add, smul_add, cadd, cadd]
    have ez : cubV cub p J (c z) (c z') (c y) =
        cubV cub p J (c (w0 • z) * c (star w0 • z)) (c (w0 • z') * c (star w0 • z')) (c y) := by rw [cw z, cw z']
    rw [hτ'v _ _ p J hJ, hτ'v _ _ p J hJ, hτ'v _ _ p J hJ, v₁, v₂, ea, ez]
    exact alg_second (isCub_cubV cub hJ) _ _ _ _ _ _ _ _ _ _ _ (hadd2 y (w0 • z) (w0 • z') p J hJ)
      (hadd1 (star w0 • z) (star w0 • z') y p J hJ)
  · intro a u hu hu0 y z p J hJ
    haveI := act.hom a
    haveI := act.hom (star a)
    obtain ⟨ub, hub, hub0⟩ := exists_ros hG hA M.isLB (act.act (star a)) (act.act a)
      (by simpa only [star_star] using hros (star a))
    have hb := hbal (star a)
    rw [star_star] at hb
    have q₁ : star a • w0 • z = w0 • star a • z := smul_comm _ _ _
    have q₂ : star a • star w0 • z = star w0 • star a • z := smul_comm _ _ _
    have e₁ := hbal a u hu hu0 y (w0 • z) p J hJ
    have e₂ := hb ub hub hub0 (star w0 • z) y p J hJ
    have ra := (ros_add cub hG hA (act.act a) (act.act (star a)) u hu hu0 hJ (c (w0 • z)) (c (star w0 • z)) (c y)).2
    have sw := ros_swap hG hA (act.act a) (act.act (star a)) u hu hu0 ub hub hub0 hJ (c y) (c (star w0 • z))
    simp only [val₂] at ra sw
    rw [← clin, ← clin, ← clin, q₁, q₂, cw z] at ra
    rw [q₁] at e₁
    rw [q₂] at e₂
    rw [hτ'v _ _ p J hJ, hτ'v _ _ p J hJ]
    exact alg_bal (isCub_cubV cub hJ) _ _ _ _ _ _ _ _ _ _ _ _ _ _ e₁ e₂ ra sw
  · intro y z p J hJ
    haveI := act.hom w0
    haveI := act.hom (star w0)
    obtain ⟨u₀, hu₀, hu₀0⟩ := exists_ros hG hA M.isLB (act.act w0) (act.act (star w0)) (hros w0)
    obtain ⟨u₁, hu₁, hu₁0⟩ := exists_ros hG hA M.isLB (act.act (star w0)) (act.act w0)
      (by simpa only [star_star] using hros (star w0))
    have hb := hbal (star w0)
    rw [star_star] at hb
    have e₁ := hb u₁ hu₁ hu₁0 y z p J hJ
    have e₂ := hb u₁ hu₁ hu₁0 z y p J hJ
    have sw := ros_swap hG hA (act.act w0) (act.act (star w0)) u₀ hu₀ hu₀0 u₁ hu₁ hu₁0 hJ (c y) (c z)
    have hf : act.act (star w0) * act.act w0 = 𝟙 B := by
      rw [← act.map_one, ← hw, add_comm]; exact (act.map_add _ _).symm
    have hg : act.act w0 * act.act (star w0) = 𝟙 B := by
      rw [← act.map_one, ← hw]; exact (act.map_add _ _).symm
    have sm := ros_sum cub hG hA (act.act (star w0)) (act.act w0) (act.act w0) (act.act (star w0)) hf hg u₁ hu₁ hu₁0
      u₀ hu₀ hu₀0 hJ (c y) (c z)
    simp only [val₂] at sw sm
    rw [← clin, ← clin, ← clin, ← clin] at sm
    rw [hτ'v _ _ p J hJ, hτ'v _ _ p J hJ]
    exact alg_symm (isCub_cubV cub hJ) _ _ _ _ _ _ _ _ _ _ _ _ _ e₁ e₂ sw sm

end GlobalTheory.SymTau
