import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt

noncomputable section

namespace GlobalTheory.ArcCM.Split

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Alg

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}

def quo (θ : A → A → A → U) (k : ℕ) (x b : A) : U := cubN θ k 1 x b * (cubN θ k 1 b x)⁻¹

variable (h : IsCub θ)
include h

/- English proof (translation)
Establish `e₁` using `h.coc a b (c * d) x`. Establish `e₂` using `h.coc b c d x`. Establish `e₃` using `h.coc a c (b * d) x`. Establish `e₄` using `h.coc c b d x`. Rewrite `e₃` using `[mul_left_comm c b d]`.

Rewrite `e₄` using `[mul_comm c b, h.s01 c b]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Establish `E` using `fun {p q : U} (e : p = q) => congrArg Additive.ofMul e`. Establish `a₁` using `E e₁`. Establish `a₂` using `E e₂`.

Establish `a₃` using `E e₃`. Establish `a₄` using `E e₄`. Simplify using `only [ofMul_mul] at *`. Take the linear combination `(norm := abel) a₁ - a₂ - a₃ + a₄`.
-/
theorem coc_four (a b c d x : A) :
    θ (a * b) (c * d) x * θ a b x * θ c d x = θ (a * c) (b * d) x * θ a c x * θ b d x := by
  have e₁ := h.coc a b (c * d) x
  have e₂ := h.coc b c d x
  have e₃ := h.coc a c (b * d) x
  have e₄ := h.coc c b d x
  rw [mul_left_comm c b d] at e₃
  rw [mul_comm c b, h.s01 c b] at e₄
  apply Additive.ofMul.injective
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E e₁; have a₂ := E e₂; have a₃ := E e₃; have a₄ := E e₄
  simp only [ofMul_mul] at *
  linear_combination (norm := abel) a₁ - a₂ - a₃ + a₄

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp [cubN, h.face]`. Consider the case `succ k ih`. Establish `c` using `coc_four h (m ^ k) (m' ^ k) m m' x`. Simplify using `only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢`.

Rewrite using `[pow_succ m, pow_succ m', pow_succ (θ m m' x), mul_pow]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Establish `ih'` using `congrArg Additive.ofMul ih`. Establish `c'` using `congrArg Additive.ofMul c`. Simplify using `only [ofMul_mul] at ih' c' ⊢`.

Take the linear combination `(norm := abel) ih' + c'`.
-/
theorem cubN_mul_left (k : ℕ) (m m' x : A) :
    cubN θ k 1 (m * m') x * θ m m' x ^ k = θ (m ^ k) (m' ^ k) x * cubN θ k 1 m x * cubN θ k 1 m' x := by
  induction k with
  | zero => simp [cubN, h.face]
  | succ k ih =>
    have c := coc_four h (m ^ k) (m' ^ k) m m' x
    simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
    rw [pow_succ m, pow_succ m', pow_succ (θ m m' x), mul_pow]
    apply Additive.ofMul.injective
    have ih' := congrArg Additive.ofMul ih
    have c' := congrArg Additive.ofMul c
    simp only [ofMul_mul] at ih' c' ⊢
    linear_combination (norm := abel) ih' + c'

/- English proof (translation)
Rewrite using `[quo, h.N_one, inv_one, _root_.mul_one]`. Conclude with `Finset.prod_eq_one fun _ _ => h.face₂ _ _`.
-/
theorem quo_one (k : ℕ) (b : A) : quo θ k 1 b = 1 := by
  rw [quo, h.N_one, inv_one, _root_.mul_one]
  exact Finset.prod_eq_one fun _ _ => h.face₂ _ _

/- English proof (translation)
Establish `e₁` using `cubN_mul_left h k x x' b`. Establish `e₂` using `h.N_add k 1 b x x'`. Rewrite `e₁` using `[hx, h.face]`. Rewrite `e₂` using `[h.face, _root_.one_mul, h.s01 b, h.s12 x b, h.s01 (b ^ k), h.s12 x (b ^ k)]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Establish `a₁` using `congrArg Additive.ofMul e₁`. Establish `a₂` using `congrArg Additive.ofMul e₂`. Simplify using `only [quo, ofMul_mul, ofMul_inv, ofMul_one] at a₁ a₂ ⊢`. Take the linear combination `(norm := abel) a₁ - a₂`.
-/
theorem quo_mul_left {k : ℕ} {x x' : A} (hx : x ^ k = 1) (b : A) :
    quo θ k (x * x') b * θ x x' (b ^ k) = quo θ k x b * quo θ k x' b := by
  have e₁ := cubN_mul_left h k x x' b
  have e₂ := h.N_add k 1 b x x'
  rw [hx, h.face] at e₁
  rw [h.face, _root_.one_mul, h.s01 b, h.s12 x b, h.s01 (b ^ k), h.s12 x (b ^ k)] at e₂
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul e₁
  have a₂ := congrArg Additive.ofMul e₂
  simp only [quo, ofMul_mul, ofMul_inv, ofMul_one] at a₁ a₂ ⊢
  linear_combination (norm := abel) a₁ - a₂

/- English proof (translation)
Establish `e₁` using `cubN_mul_left h k b b' x`. Establish `e₂` using `h.N_add k 1 x b b'`. Rewrite `e₂` using `[hx, h.face, _root_.one_mul, h.face]`. Rewrite `e₁` using `[h.s12 b, h.s01 b, h.s12 (b ^ k), h.s01 (b ^ k)]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Establish `a₁` using `congrArg Additive.ofMul e₁`. Establish `a₂` using `congrArg Additive.ofMul e₂`. Simplify using `only [quo, ofMul_mul, ofMul_inv, ofMul_one] at a₁ a₂ ⊢`. Take the linear combination `(norm := abel) a₂ - a₁`.
-/
theorem quo_mul_right {k : ℕ} {x : A} (hx : x ^ k = 1) (b b' : A) :
    quo θ k x (b * b') * θ x (b ^ k) (b' ^ k) = quo θ k x b * quo θ k x b' := by
  have e₁ := cubN_mul_left h k b b' x
  have e₂ := h.N_add k 1 x b b'
  rw [hx, h.face, _root_.one_mul, h.face] at e₂
  rw [h.s12 b, h.s01 b, h.s12 (b ^ k), h.s01 (b ^ k)] at e₁
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul e₁
  have a₂ := congrArg Additive.ofMul e₂
  simp only [quo, ofMul_mul, ofMul_inv, ofMul_one] at a₁ a₂ ⊢
  linear_combination (norm := abel) a₂ - a₁

end Alg

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {n : ℕ}

/- English proof (translation)
Use `val_cub D.cub (𝟙 T) hJ x x' w` as an intermediate fact. Rewrite `this` using `[Category.id_comp, Category.id_comp, Category.id_comp]`. Then use the resulting hypothesis.
-/
theorem val_cubAtT {T : Over (Sp R)} {y : T.left} {J} (hJ : Good D.P.L y J) (x x' w : T ⟶ D.P.A) :
    val (DegPre.cubAtT D T x x' w) (𝟙 _) y J = th D y J x x' w := by
  have := val_cub D.cub (𝟙 T) hJ x x' w
  rwa [Category.id_comp, Category.id_comp, Category.id_comp] at this

/- English proof (translation)
Rewrite using `[Fin.prod_univ_four]`. Use `show h (cP D _ χ * b).left ^ (-1 : ℤ) * h (cP D _ χ).left ^ (1 : ℤ) * h b.left ^ (1 : ℤ) * h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) = _`. Simplify using `only [zpow_neg, zpow_one]`.
-/
theorem prod_gtT {T : Over (Sp R)} (b : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (DegPre.gtφT D T b χ i) ^ DegPre.gtε i =
      (h (cP D _ χ * b).left)⁻¹ * h (cP D _ χ).left * h b.left * (h (1 : T ⟶ D.P.A).left)⁻¹ := by
  rw [Fin.prod_univ_four]
  show h (cP D _ χ * b).left ^ (-1 : ℤ) * h (cP D _ χ).left ^ (1 : ℤ) * h b.left ^ (1 : ℤ) *
    h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) = _
  simp only [zpow_neg, zpow_one]

variable (hc : ∀ y, D.c y ^ n = 1)
include hc

/- English proof (translation)
The claim follows from `(cPoint_nsmul D T n χ).symm.trans (GlobalTheory.TauTwist.cPoint_nsmul_eq_one hc T χ)`.
-/
theorem cPoint_pow_eq_one (T : Over (Sp R)) (χ : D.X) : cP D T χ ^ n = 1 :=
  (cPoint_nsmul D T n χ).symm.trans (GlobalTheory.TauTwist.cPoint_nsmul_eq_one hc T χ)

/- English proof (translation)
Take `⟨t, ht, hv⟩` from `exists_cubN D.cub 1 (cP D T χ) b n`. Take `⟨u, hu, hw⟩` from `exists_cubN D.cub 1 b (cP D T χ) n`. Take `⟨t', ht', hv'⟩` from `exists_gen D.P.isLB (φ' := DegPre.gtφT D T (b ^ n) χ) (ε' := DegPre.gtε) (fun U _ h => by`. Rewrite using `[prod_gtT, cPoint_pow_eq_one hc, mul_comm (cP D T χ) (b ^ n), mul_comm b (cP D T χ)]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Simplify using `[Fintype.prod_sum_type, Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]`. Use the proof step `module) (LB.mulGen D.P.L _ _ _ _ t (LB.invGen D.P.L _ _ u))`. Use the proof step `(mulGen_isGen _ _ _ _ _ _ _ ht (invGen_isGen _ _ _ _ hu))`. Use `⟨t', ht', fun T' ρ z J hJ => (hv' _ _ z J hJ).trans ((val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) (hv T' ρ z J hJ) ((val_inv _ _).trans (congrArg (·⁻¹) (hw T' ρ z J hJ)))).trans ?_))⟩` and prove the remaining obligations. Rewrite using `[MonObj.comp_one, comp_cP]`.

Both sides reduce to the same expression.
-/
theorem exists_coord (T : Over (Sp R)) (b : T ⟶ D.P.A) (χ : D.X) :
    ∃ t : LB.Gen (LB.LinComb D.P.L (DegPre.gtφT D T (b ^ n) χ) DegPre.gtε), t.IsGen ∧
      ∀ (T' : Over (Sp R)) (ρ : T' ⟶ T) (z : T'.left) (J), Good D.P.L z J →
        val t ρ.left z J = quo (th D z J) n (cP D T' χ) (ρ ≫ b) := by
  obtain ⟨t, ht, hv⟩ := exists_cubN D.cub 1 (cP D T χ) b n
  obtain ⟨u, hu, hw⟩ := exists_cubN D.cub 1 b (cP D T χ) n
  obtain ⟨t', ht', hv'⟩ := exists_gen D.P.isLB (φ' := DegPre.gtφT D T (b ^ n) χ) (ε' := DegPre.gtε) (fun U _ h => by
      rw [prod_gtT, cPoint_pow_eq_one hc, mul_comm (cP D T χ) (b ^ n), mul_comm b (cP D T χ)]
      apply Additive.ofMul.injective
      simp [Fintype.prod_sum_type, Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module) (LB.mulGen D.P.L _ _ _ _ t (LB.invGen D.P.L _ _ u))
    (mulGen_isGen _ _ _ _ _ _ _ ht (invGen_isGen _ _ _ _ hu))
  refine ⟨t', ht', fun T' ρ z J hJ => (hv' _ _ z J hJ).trans ((val_mul hJ _ _ _).trans
    ((congrArg₂ (· * ·) (hv T' ρ z J hJ) ((val_inv _ _).trans (congrArg (·⁻¹) (hw T' ρ z J hJ)))).trans ?_))⟩
  rw [MonObj.comp_one, comp_cP]
  rfl

/- English proof (translation)
Use `(exists_coord hc T b χ).choose_spec.2 T (𝟙 T) z J hJ` as an intermediate fact. Rewrite `this` using `[Category.id_comp]`. Then use the resulting hypothesis.
-/
theorem val_coord (T : Over (Sp R)) (b : T ⟶ D.P.A) (χ : D.X) {z : T.left} {J} (hJ : Good D.P.L z J) :
    val (exists_coord hc T b χ).choose (𝟙 _) z J = quo (th D z J) n (cP D T χ) b := by
  have := (exists_coord hc T b χ).choose_spec.2 T (𝟙 T) z J hJ
  rwa [Category.id_comp] at this

def liftPt (T : Over (Sp R)) (b : T ⟶ D.P.A) : GtPt D T where
  b := b ^ n
  s χ := (exists_coord hc T b χ).choose
  isGen χ := (exists_coord hc T b χ).choose_spec.1
  s_zero := corr_of_val D.P.isLB fun y J hJ => (val_coord hc T b 0 hJ).trans (Eq.trans (by
    rw [cPoint_zero]; exact quo_one (isCub_cubV D.cub hJ) n b) (val_one _).symm)
  mult χ χ' := corr_of_val D.P.isLB fun y J hJ =>
    (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) (val_coord hc T b _ hJ) (val_cubAtT hJ _ _ _)).trans (Eq.trans (by
      rw [cPoint_add]; exact quo_mul_left (isCub_cubV D.cub hJ) (cPoint_pow_eq_one hc T χ) b)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_coord hc T b _ hJ) (val_coord hc T b _ hJ))).symm))

/- English proof (translation)
Use `⟨fun _ _ => rfl, fun T b b' => ⟨mul_pow b b' n, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩, fun T T' h b => ⟨?_, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩⟩` and prove the remaining obligations. Conclude with `(val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) (val_coord hc T _ _ hJ) (val_cubAtT hJ _ _ _)).trans ((quo_mul_right (isCub_cubV D.cub hJ) (cPoint_pow_eq_one hc T χ) b b').trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_coord hc T b _ hJ) (val_coord hc T b' _ hJ))).symm))`. Conclude with `congrArg (fun q : T' ⟶ D.P.A => q.left) (map_pow (preHom h) b n).symm`. Use `(val_coord hc T' _ _ hJ).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)` and prove the remaining obligations. Rewrite using `[Category.id_comp]`.

Conclude with `((exists_coord hc T b χ).choose_spec.2 T' h y J hJ).symm`.
-/
theorem isSplit_liftPt : IsSplit D n (liftPt hc) := by
  refine ⟨fun _ _ => rfl, fun T b b' => ⟨mul_pow b b' n, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩,
    fun T T' h b => ⟨?_, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩⟩
  · exact (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) (val_coord hc T _ _ hJ) (val_cubAtT hJ _ _ _)).trans
      ((quo_mul_right (isCub_cubV D.cub hJ) (cPoint_pow_eq_one hc T χ) b b').trans
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_coord hc T b _ hJ) (val_coord hc T b' _ hJ))).symm))
  · exact congrArg (fun q : T' ⟶ D.P.A => q.left) (map_pow (preHom h) b n).symm
  · refine (val_coord hc T' _ _ hJ).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    rw [Category.id_comp]
    exact ((exists_coord hc T b χ).choose_spec.2 T' h y J hJ).symm

end GlobalTheory.ArcCM.Split

namespace GlobalTheory.ArcCM

open AlgebraicGeometry CategoryTheory MonObj ReciprocityTheory.ChartRestriction.G

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ hc` and use `⟨_, Split.isSplit_liftPt hc⟩`.
-/
theorem exists_isSplit : Known → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D₀ : Out.DegPre R) (n : ℕ),
    0 < n → (∀ y, D₀.c y ^ n = 1) → ∃ sB, IsSplit D₀ n sB :=
  fun _ _ _ _ _ _ _ _ hc => ⟨_, Split.isSplit_liftPt hc⟩

end GlobalTheory.ArcCM
