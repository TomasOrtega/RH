import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HomDerivativeClosure

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.QuadraticAction

section Act

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

def comb (φ : G ⟶ G) (m n : ℤ) : G ⟶ G := (𝟙 G) ^ m * φ ^ n

omit [IsCommMonObj G] in
/- English proof (translation)
Simplify using `[comb]`.
-/
theorem comb_one_zero (φ : G ⟶ G) : comb φ 1 0 = 𝟙 G := by simp [comb]

/- English proof (translation)
Establish `h1 : IsMonHom (1 : G ⟶ G)` using `by rw [Hom.one_def]; infer_instance`. Establish `hm : ∀ f g : G ⟶ G, IsMonHom f → IsMonHom g → IsMonHom (f * g)` using `fun f g _ _ => by`. Rewrite using `[Hom.mul_def]`. Use `infer_instance`. Proceed by induction on `n using Int.induction_on with`.

Consider the case `zero => rwa [zpow_zero]`. Consider the case `succ n h => rw [zpow_add_one]`. Conclude with `hm _ _ h inferInstance`. Consider the case `pred n h => rw [zpow_sub_one]`. Conclude with `hm _ _ h inferInstance`.
-/
theorem isMonHom_zpow (f : G ⟶ G) [IsMonHom f] (n : ℤ) : IsMonHom (f ^ n) := by
  have h1 : IsMonHom (1 : G ⟶ G) := by rw [Hom.one_def]; infer_instance
  have hm : ∀ f g : G ⟶ G, IsMonHom f → IsMonHom g → IsMonHom (f * g) := fun f g _ _ => by
    rw [Hom.mul_def]; infer_instance
  induction n using Int.induction_on with
  | zero => rwa [zpow_zero]
  | succ n h => rw [zpow_add_one]; exact hm _ _ h inferInstance
  | pred n h => rw [zpow_sub_one]; exact hm _ _ h inferInstance

/- English proof (translation)
Use `isMonHom_zpow (𝟙 G) m` as an intermediate fact. Use `isMonHom_zpow φ n` as an intermediate fact. Rewrite using `[comb, Hom.mul_def]`. Use `infer_instance`.
-/
theorem isMonHom_comb (φ : G ⟶ G) [IsMonHom φ] (m n : ℤ) : IsMonHom (comb φ m n) := by
  have := isMonHom_zpow (𝟙 G) m
  have := isMonHom_zpow φ n
  rw [comb, Hom.mul_def]
  infer_instance

/- English proof (translation)
Simplify using `only [comb, zpow_add]`. Conclude with `mul_mul_mul_comm _ _ _ _`.
-/
theorem comb_add (φ : G ⟶ G) (m n m' n' : ℤ) :
    comb φ (m + m') (n + n') = comb φ m n * comb φ m' n' := by
  simp only [comb, zpow_add]
  exact mul_mul_mul_comm _ _ _ _

/- English proof (translation)
Simplify using `only [mul_zpow, ← zpow_mul, zpow_add]`. The two sides agree by associativity and commutativity.
-/
theorem zpow_identity {M : Type*} [CommGroup M] (x y : M) (a b m n m' n' : ℤ) :
    (x ^ m * y ^ n) ^ m' * (y ^ m * (x ^ a * y ^ b) ^ n) ^ n' =
      x ^ (m * m' + a * n * n') * y ^ (m * n' + n * m' + b * n * n') := by
  simp only [mul_zpow, ← zpow_mul, zpow_add]
  ac_rfl

/- English proof (translation)
Establish `e : comb φ m n ≫ φ = φ ^ m * comb φ a b ^ n`. Rewrite using `[comb, MonObj.mul_comp, GrpObj.zpow_comp, GrpObj.zpow_comp, Category.id_comp, h]`. Use `conv_lhs => rw [comb.eq_1 φ m' n', MonObj.comp_mul, GrpObj.comp_zpow, GrpObj.comp_zpow, Category.comp_id, e]`. Conclude with `zpow_identity (M := G ⟶ G) _ _ _ _ _ _ _ _`.
-/
theorem comb_comp (φ : G ⟶ G) [IsMonHom φ] {a b : ℤ} (h : φ ≫ φ = comb φ a b) (m n m' n' : ℤ) :
    comb φ m n ≫ comb φ m' n' =
      comb φ (m * m' + a * n * n') (m * n' + n * m' + b * n * n') := by
  have e : comb φ m n ≫ φ = φ ^ m * comb φ a b ^ n := by
    rw [comb, MonObj.mul_comp, GrpObj.zpow_comp, GrpObj.zpow_comp, Category.id_comp, h]
  conv_lhs => rw [comb.eq_1 φ m' n', MonObj.comp_mul, GrpObj.comp_zpow, GrpObj.comp_zpow,
    Category.comp_id, e]
  exact zpow_identity (M := G ⟶ G) _ _ _ _ _ _ _ _

def quadAct (φ : G ⟶ G) [IsMonHom φ] {a b : ℤ} (h : φ ≫ φ = comb φ a b) :
    OAct (QuadraticAlgebra ℤ a b) G where
  act z := comb φ z.re z.im
  hom _ := isMonHom_comb ..
  one := comb_one_zero φ
  mul z w := by rw [comb_comp φ h, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  add z w := comb_add ..

def zsqrtdAct (φ : G ⟶ G) [IsMonHom φ] {d : ℤ} (h : φ ≫ φ = comb φ d 0) :
    OAct (ℤ√d) G where
  act z := comb φ z.re z.im
  hom _ := isMonHom_comb ..
  one := comb_one_zero φ
  mul z w := by rw [comb_comp φ h, Zsqrtd.re_mul, Zsqrtd.im_mul]; simp
  add z w := comb_add ..

end Act

section Lie

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

end Lie

end GlobalTheory.QuadraticAction
