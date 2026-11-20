import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.InversionStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory.RiemannForm

/- English proof (translation)
Establish `hA' : A * h = 1` using `mul_eq_one_comm.mp hA`. Establish `hB' : B = A * τ` using `by rw [← hB, ← Matrix.mul_assoc, hA', Matrix.one_mul]`. Use `set M := Aᵀ * Hm * A.map (starRingEnd ℂ) with hM`. Establish `hMB : Aᵀ * Hm * B.map (starRingEnd ℂ) = M * τ.map (starRingEnd ℂ)`. Rewrite using `[hB', Matrix.map_mul, hM]`.

Simplify using `only [Matrix.mul_assoc]`. Establish `hMY : M.map Complex.re * τ.map Complex.im = 1`. Use extensionality with `a b`. Use `h2 a b` as an intermediate fact. Rewrite `this` using `[hMB, Matrix.mul_apply, Complex.im_sum]`.

Rewrite using `[Matrix.mul_apply, ← neg_inj, ← this, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Simplify using `[h1 a c]`. Establish `hinv : (τ.map Complex.im)⁻¹ = M.map Complex.re` using `Matrix.inv_eq_left_inv hMY`. Establish `hMre : (M.map Complex.re).map (fun x : ℝ => (x : ℂ)) = M`.

Use extensionality with `a b`. Apply the tactic sequence `apply Complex.ext <;> simp [h1 a b]`. Establish `hH : Hm = hᵀ * M * h.map (starRingEnd ℂ)`. Establish `e1 : hᵀ * Aᵀ = 1` using `by rw [← Matrix.transpose_mul, hA', Matrix.transpose_one]`. Establish `e2 : A.map (starRingEnd ℂ) * h.map (starRingEnd ℂ) = 1`.

Rewrite using `[← Matrix.map_mul, hA']`. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e1, e2]`. Simplify using the standard rewrite rules.

Use `_ = _ := by rw [hM]; simp only [Matrix.mul_assoc]`. Use `⟨by rw [hinv, hMre]; exact hH, ?_⟩` and prove the remaining obligations. Establish `hd : M.det * (((τ.map Complex.im).det : ℝ) : ℂ) = 1`. Establish `e` using `congrArg Matrix.det hMY`. Rewrite `e` using `[Matrix.det_mul, Matrix.det_one]`.

Establish `e' : M.det = (((M.map Complex.re).det : ℝ) : ℂ)` using `by conv_lhs => rw [← hMre]`. Conclude with `(RingHom.map_det Complex.ofRealHom _).symm`. Rewrite using `[e']`. Conclude with `e` after adjusting the coercions. Establish `hc : (h.map (starRingEnd ℂ)).det = starRingEnd ℂ h.det` using `(RingHom.map_det (starRingEnd ℂ) h).symm`.

Rewrite using `[hH, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hc]`. Use `Complex.mul_conj' h.det` as an intermediate fact. Use `push_cast`. Take the linear combination `(h.det * starRingEnd ℂ h.det) * hd + this`.
-/
theorem eq_of_im {g : ℕ} (h τ Hm A B : Matrix (Fin g) (Fin g) ℂ) (hA : h * A = 1) (hB : h * B = τ)
    (h1 : ∀ a b, ((Aᵀ * Hm * A.map (starRingEnd ℂ)) a b).im = 0)
    (h2 : ∀ a b, ((Aᵀ * Hm * B.map (starRingEnd ℂ)) a b).im = -(1 : Matrix (Fin g) (Fin g) ℝ) a b) :
    Hm = hᵀ * ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) * h.map (starRingEnd ℂ) ∧
      Hm.det * (((τ.map Complex.im).det : ℝ) : ℂ) = ((‖h.det‖ ^ 2 : ℝ) : ℂ) := by
  have hA' : A * h = 1 := mul_eq_one_comm.mp hA
  have hB' : B = A * τ := by rw [← hB, ← Matrix.mul_assoc, hA', Matrix.one_mul]
  set M := Aᵀ * Hm * A.map (starRingEnd ℂ) with hM
  have hMB : Aᵀ * Hm * B.map (starRingEnd ℂ) = M * τ.map (starRingEnd ℂ) := by
    rw [hB', Matrix.map_mul, hM]; simp only [Matrix.mul_assoc]
  have hMY : M.map Complex.re * τ.map Complex.im = 1 := by
    ext a b
    have := h2 a b
    rw [hMB, Matrix.mul_apply, Complex.im_sum] at this
    rw [Matrix.mul_apply, ← neg_inj, ← this, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [h1 a c]
  have hinv : (τ.map Complex.im)⁻¹ = M.map Complex.re := Matrix.inv_eq_left_inv hMY
  have hMre : (M.map Complex.re).map (fun x : ℝ => (x : ℂ)) = M := by
    ext a b
    apply Complex.ext <;> simp [h1 a b]
  have hH : Hm = hᵀ * M * h.map (starRingEnd ℂ) := by
    have e1 : hᵀ * Aᵀ = 1 := by rw [← Matrix.transpose_mul, hA', Matrix.transpose_one]
    have e2 : A.map (starRingEnd ℂ) * h.map (starRingEnd ℂ) = 1 := by
      rw [← Matrix.map_mul, hA']; simp
    calc Hm = (hᵀ * Aᵀ) * Hm * (A.map (starRingEnd ℂ) * h.map (starRingEnd ℂ)) := by
          rw [e1, e2]; simp
      _ = _ := by rw [hM]; simp only [Matrix.mul_assoc]
  refine ⟨by rw [hinv, hMre]; exact hH, ?_⟩
  have hd : M.det * (((τ.map Complex.im).det : ℝ) : ℂ) = 1 := by
    have e := congrArg Matrix.det hMY
    rw [Matrix.det_mul, Matrix.det_one] at e
    have e' : M.det = (((M.map Complex.re).det : ℝ) : ℂ) := by
      conv_lhs => rw [← hMre]
      exact (RingHom.map_det Complex.ofRealHom _).symm
    rw [e']; exact_mod_cast e
  have hc : (h.map (starRingEnd ℂ)).det = starRingEnd ℂ h.det :=
    (RingHom.map_det (starRingEnd ℂ) h).symm
  rw [hH, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hc]
  have := Complex.mul_conj' h.det
  push_cast
  linear_combination (h.det * starRingEnd ℂ h.det) * hd + this

/- English proof (translation)
Rewrite using `[Matrix.mul_assoc]`. Both sides reduce to the same expression.
-/
theorem entry_eq {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (u v : Fin g → Fin g → ℂ) (a b : Fin g) :
    ((Matrix.of u)ᵀᵀ * Hm * ((Matrix.of v)ᵀ).map (starRingEnd ℂ)) a b = hermForm Hm (u a) (v b) := by
  rw [Matrix.mul_assoc]
  rfl

/- English proof (translation)
Introduce `E _ _ _ H D g ty bas P h τ Hm hE _ hn _ hH`. Use `eq_of_im h τ Hm (Matrix.of fun k => P (bas (Pi.single (Sum.inl k) 1)))ᵀ (Matrix.of fun k => P (bas (Pi.single (Sum.inr k) 1)))ᵀ ?_ ?_ ?_ ?_` and prove the remaining obligations. Use extensionality with `i k`. Use `congrFun (hn k).1 i` as an intermediate fact. Rewrite using `[Matrix.one_apply, ← Pi.single_apply k (1 : ℂ) i, ← this]`.

Both sides reduce to the same expression. Use extensionality with `i k`. Use `congrFun (hn k).2 i` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_single_one]`. Conclude with `this`.

Introduce `a b`. Rewrite using `[entry_eq, hH, hE]`. Simplify using `[omegaStd]`. Introduce `a b`. Rewrite using `[entry_eq, hH, hE]`.

Simplify using `[omegaStd, Pi.single_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp_all [eq_comm]`.
-/
theorem herm_eq_of_normalised : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (P : D.La →+ (Fin g → ℂ)) (h τ Hm : Matrix (Fin g) (Fin g) ℂ), (∀ a b, D.EF (bas a) (bas b) = -omegaStd a b) → IsPeriod D ty P → (∀ k, h *ᵥ P (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧ h *ᵥ P (bas (Pi.single (Sum.inr k) 1)) = τ *ᵥ Pi.single k 1) → τ ∈ SiegelH (Fin g) → (∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y) → Hm = hᵀ * ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) * h.map (starRingEnd ℂ) ∧ Hm.det * (((τ.map Complex.im).det : ℝ) : ℂ) = ((‖h.det‖ ^ 2 : ℝ) : ℂ) := by
  intro E _ _ _ H D g ty bas P h τ Hm hE _ hn _ hH
  refine eq_of_im h τ Hm (Matrix.of fun k => P (bas (Pi.single (Sum.inl k) 1)))ᵀ
    (Matrix.of fun k => P (bas (Pi.single (Sum.inr k) 1)))ᵀ ?_ ?_ ?_ ?_
  · ext i k
    have := congrFun (hn k).1 i
    rw [Matrix.one_apply, ← Pi.single_apply k (1 : ℂ) i, ← this]
    rfl
  · ext i k
    have := congrFun (hn k).2 i
    rw [Matrix.mulVec_single_one] at this
    exact this
  · intro a b
    rw [entry_eq, hH, hE]
    simp [omegaStd]
  · intro a b
    rw [entry_eq, hH, hE]
    simp [omegaStd, Pi.single_apply, Matrix.one_apply]
    split_ifs <;> simp_all [eq_comm]

end GlobalTheory.RiemannForm
