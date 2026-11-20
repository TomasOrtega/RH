import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLinearLiftOfAbelianEndomorphismStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.HermImNondeg

/- English proof (translation)
Simplify using `only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add]`.
-/
theorem hermForm_add_right' {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := by
  simp only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add]

/- English proof (translation)
Simplify using `only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]`.
-/
theorem hermForm_smul_right' {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm z (a • w) = star a * hermForm Hm z w := by
  simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Simplify using `only [hermForm, dotProduct, Matrix.mulVec, star_sum, star_mul', Pi.star_apply, star_star, h.apply, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem hermForm_self_star {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) (z : Fin g → ℂ) :
    star (hermForm Hm z z) = hermForm Hm z z := by
  simp only [hermForm, dotProduct, Matrix.mulVec, star_sum, star_mul', Pi.star_apply, star_star, h.apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Use `⟨fun x => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hc : ((EF x x : ℤ) : ℝ) = 0`. Rewrite using `[← hEF]`. Establish `h1` using `congrArg Complex.im (hermForm_self_star hH (P x))`. Establish `h2 : (star (hermForm Hm (P x) (P x))).im = -(hermForm Hm (P x) (P x)).im` using `Complex.conj_im _`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `hc` after adjusting the coercions. Use `set z := P x with hz`. Establish `key : ∀ w : Fin g → ℂ, (hermForm Hm z w).im = 0`. Introduce `w`.

Establish `hw : w ∈ Submodule.span ℝ (Set.range P)` using `hspan ▸ Submodule.mem_top`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem a ha`. Take `⟨y, rfl⟩` from `ha`. Rewrite using `[hEF, hx y]`.

Simplify using the standard rewrite rules. Consider the case `zero => simp [hermForm]`. Consider the case `add a b _ _ h1 h2 => rw [hermForm_add_right', Complex.add_im, h1, h2, add_zero]`. Consider the case `smul r a _ h1`. Rewrite using `[← Complex.coe_smul, hermForm_smul_right']`.

Simplify using `[h1]`. Establish `hI` using `key (Complex.I • z)`. Rewrite `hI` using `[hermForm_smul_right']`. Establish `hre : (hermForm Hm z z).re = 0`. Establish `: (star Complex.I * hermForm Hm z z).im = -(hermForm Hm z z).re`.

Simplify using `[Complex.mul_im]`. Combine the linear equalities and inequalities to obtain the conclusion. Assume the negation of the conclusion as `hne`. Establish `hz0 : z ≠ 0`. Introduce `h0`.

Apply `hne` to reduce the goal to its premises. Apply `hP` to reduce the goal to its premises. Rewrite using `[← hz, h0, map_zero]`. Use `hpos z hz0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem im_hermForm_alternating_nondegenerate (La : Type) [AddCommGroup La] (g : ℕ) (P : La →+ (Fin g → ℂ))
    (Hm : Matrix (Fin g) (Fin g) ℂ) (EF : LinearMap.BilinForm ℤ La) (hP : Function.Injective P)
    (hspan : Submodule.span ℝ (Set.range P) = ⊤) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hEF : ∀ x y, (hermForm Hm (P x) (P y)).im = EF x y) :
    (∀ x, EF x x = 0) ∧ ∀ x, (∀ y, EF x y = 0) → x = 0 := by
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · have hc : ((EF x x : ℤ) : ℝ) = 0 := by
      rw [← hEF]
      have h1 := congrArg Complex.im (hermForm_self_star hH (P x))
      have h2 : (star (hermForm Hm (P x) (P x))).im = -(hermForm Hm (P x) (P x)).im := Complex.conj_im _
      linarith
    exact_mod_cast hc
  · set z := P x with hz
    have key : ∀ w : Fin g → ℂ, (hermForm Hm z w).im = 0 := by
      intro w
      have hw : w ∈ Submodule.span ℝ (Set.range P) := hspan ▸ Submodule.mem_top
      induction hw using Submodule.span_induction with
      | mem a ha =>
        obtain ⟨y, rfl⟩ := ha
        rw [hEF, hx y]; simp
      | zero => simp [hermForm]
      | add a b _ _ h1 h2 => rw [hermForm_add_right', Complex.add_im, h1, h2, add_zero]
      | smul r a _ h1 =>
        rw [← Complex.coe_smul, hermForm_smul_right']
        simp [h1]
    have hI := key (Complex.I • z)
    rw [hermForm_smul_right'] at hI
    have hre : (hermForm Hm z z).re = 0 := by
      have : (star Complex.I * hermForm Hm z z).im = -(hermForm Hm z z).re := by
        simp [Complex.mul_im]
      linarith
    by_contra hne
    have hz0 : z ≠ 0 := by
      intro h0; apply hne; apply hP; rw [← hz, h0, map_zero]
    have := hpos z hz0
    linarith

end GlobalTheory.HermImNondeg

/- English proof (translation)
The claim follows from `GlobalTheory.HermImNondeg.im_hermForm_alternating_nondegenerate`.
-/
example : ∀ (La : Type) [AddCommGroup La] (g : ℕ) (P : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (EF : LinearMap.BilinForm ℤ La), Function.Injective P → Submodule.span ℝ (Set.range P) = ⊤ → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ x y, (hermForm Hm (P x) (P y)).im = EF x y) → (∀ x, EF x x = 0) ∧ ∀ x, (∀ y, EF x y = 0) → x = 0 := GlobalTheory.HermImNondeg.im_hermForm_alternating_nondegenerate
