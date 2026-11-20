import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.FrameDer
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceActionDeterminant

noncomputable section

open Matrix Finset
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.HbBasis

open PositivityTheory.RgTw (Mat hb)
open PositivityTheory.RgBcC
open PositivityTheory.RgBcC.LfSt

variable {n : ℕ}

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.sum_apply]`. Simplify using `only [Matrix.single_apply]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[Matrix.one_apply_ne h]`. Use `Finset.sum_eq_zero fun x _ => if_neg fun hx => h (hx.1.symm.trans hx.2)` and prove the remaining obligations.
-/
theorem sum_single_one : ∑ a : Fin n, (Matrix.single a a (1 : ℂ) : Mat n) = 1 := by
  ext i j
  rw [Matrix.sum_apply]
  simp only [Matrix.single_apply]
  by_cases h : i = j
  · subst h
    simp
  · rw [Matrix.one_apply_ne h]
    refine Finset.sum_eq_zero fun x _ => if_neg fun hx => h (hx.1.symm.trans hx.2)

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.TopClass.sqrt_two_inv_sq`.
-/
theorem sqrt_two_inv_sq : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 :=
  GlobalTheory.CompanionTheory.TopClass.sqrt_two_inv_sq

/- English proof (translation)
Establish `hs` using `sqrt_two_inv_sq`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Establish `: (hb (a, a) : Mat n) = Matrix.single a a 1` using `by simp [hb]`. Rewrite using `[this, Matrix.single_mul_single_same, ← two_smul ℂ, smul_smul]`.

Evaluate the numerical expressions. Establish `hne : b ≠ a` using `fun e => h e.symm`. Distinguish the cases in `h' : a < b`. Establish `: (hb (a, b) : Mat n) = (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) • (Matrix.single a b 1 + Matrix.single b a 1)`. Simplify using `[hb, h, h']`.

Rewrite using `[this, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs]`. Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne _ _ _ _ hne, Matrix.single_mul_single_of_ne _ _ _ _ h]`. Simplify using `[add_comm]`. Establish `: (hb (a, b) : Mat n) = (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * Complex.I) • (Matrix.single a b 1 - Matrix.single b a 1)`. Simplify using `[hb, h, h']`.

Establish `hc : (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * Complex.I) * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * Complex.I) = -(1 / 2)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[this, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc]`. Simplify using `only [Matrix.sub_mul, Matrix.mul_sub, Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne _ _ _ _ hne, Matrix.single_mul_single_of_ne _ _ _ _ h]`. Simplify using `only [mul_one, sub_zero, zero_sub, neg_smul, smul_neg, smul_sub, smul_add]`.

Normalize the expressions using the abelian group laws.
-/
theorem hb_mul_self (a b : Fin n) :
    (hb (a, b) : Mat n) * hb (a, b) = (1 / 2 : ℂ) • (Matrix.single a a 1 + Matrix.single b b 1) := by
  have hs := sqrt_two_inv_sq
  by_cases h : a = b
  · subst h
    have : (hb (a, a) : Mat n) = Matrix.single a a 1 := by simp [hb]
    rw [this, Matrix.single_mul_single_same, ← two_smul ℂ, smul_smul]
    norm_num
  · have hne : b ≠ a := fun e => h e.symm
    by_cases h' : a < b
    · have : (hb (a, b) : Mat n) = (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) • (Matrix.single a b 1 + Matrix.single b a 1) := by
        simp [hb, h, h']
      rw [this, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.single_mul_single_same,
        Matrix.single_mul_single_of_ne _ _ _ _ hne, Matrix.single_mul_single_of_ne _ _ _ _ h]
      simp [add_comm]
    · have : (hb (a, b) : Mat n) =
          (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * Complex.I) • (Matrix.single a b 1 - Matrix.single b a 1) := by
        simp [hb, h, h']
      have hc : (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * Complex.I) * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * Complex.I) = -(1 / 2) := by
        calc _ = (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) * (Complex.I * Complex.I) := by ring
          _ = _ := by rw [hs, Complex.I_mul_I]; ring
      rw [this, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.single_mul_single_same,
        Matrix.single_mul_single_of_ne _ _ _ _ hne, Matrix.single_mul_single_of_ne _ _ _ _ h]
      simp only [mul_one, sub_zero, zero_sub, neg_smul, smul_neg, smul_sub, smul_add]
      abel

/- English proof (translation)
Rewrite using `[Fintype.sum_prod_type]`. Simplify using `only [hb_mul_self, ← Finset.smul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, sum_single_one]`. Rewrite using `[← Nat.cast_smul_eq_nsmul ℂ n (1 : Mat n), ← two_smul ℂ, smul_smul, smul_smul]`. Evaluate the numerical expressions.
-/
theorem sum_hb_mul_self : ∑ p, (hb p : Mat n) * hb p = (n : ℂ) • 1 := by
  rw [Fintype.sum_prod_type]
  simp only [hb_mul_self, ← Finset.smul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, sum_single_one]
  rw [← Nat.cast_smul_eq_nsmul ℂ n (1 : Mat n), ← two_smul ℂ, smul_smul, smul_smul]
  norm_num

/- English proof (translation)
Use `GlobalTheory.CompanionTheory.ConeLin.re_trace (1 : Mat n) (by simp) p` as an intermediate fact. Simplify `this` using `[coords]`.
-/
theorem coords_one (p : Fin n × Fin n) : ((coords (1 : Mat n) p : ℝ) : ℂ) = (hb p : Mat n).trace := by
  have := GlobalTheory.CompanionTheory.ConeLin.re_trace (1 : Mat n) (by simp) p
  simpa [coords] using this

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.ConeLin.hOf_re H hH`.
-/
theorem hOf_coords {H : Mat n} (hH : H.IsHermitian) : hOf (coords H) = H :=
  GlobalTheory.CompanionTheory.ConeLin.hOf_re H hH

/- English proof (translation)
Use function extensionality and compare the values at `q`. Establish `: (hOf v * hb q).trace = (v q : ℂ)` using `by classical`. Simplify using `[hOf, Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul, GlobalTheory.CompanionTheory.TopClass.trace_hb_mul_hb]`. Simplify using `[coords, this]`.
-/
theorem coords_hOf (v : Fin n × Fin n → ℝ) : coords (hOf v) = v := by
  funext q
  have : (hOf v * hb q).trace = (v q : ℂ) := by
    classical
    simp [hOf, Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul,
      GlobalTheory.CompanionTheory.TopClass.trace_hb_mul_hb]
  simp [coords, this]

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.ConeLin.hOf_herm v`.
-/
theorem hOf_isHermitian (v : Fin n × Fin n → ℝ) : (hOf v).IsHermitian :=
  GlobalTheory.CompanionTheory.ConeLin.hOf_herm v

/- English proof (translation)
Establish `h` using `hOf_coords (H := (1 : Mat n)) Matrix.isHermitian_one`. Simplify `h` using `only [hOf, coords_one]`.
-/
theorem sum_trace_smul_hb : ∑ p, (hb p : Mat n).trace • hb p = 1 := by
  have h := hOf_coords (H := (1 : Mat n)) Matrix.isHermitian_one
  simpa only [hOf, coords_one] using h

/- English proof (translation)
Use `show (hOf (coords (1 : Mat n))).PosDef`. Rewrite using `[hOf_coords Matrix.isHermitian_one]`. Conclude with `Matrix.PosDef.one`.
-/
theorem oPt_mem_cone : oPt n ∈ cone n := by
  show (hOf (coords (1 : Mat n))).PosDef
  rw [hOf_coords Matrix.isHermitian_one]
  exact Matrix.PosDef.one

/- English proof (translation)
Introduce `_` and use `⟨GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose, GlobalTheory.CompanionTheory.TopClass.trace_hb_mul_hb, fun _ hH => hOf_coords hH, coords_hOf, hOf_isHermitian, sum_hb_mul_self, sum_trace_smul_hb, oPt_mem_cone⟩`.
-/
theorem hbFacts : HbFacts := fun _ =>
  ⟨GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose, GlobalTheory.CompanionTheory.TopClass.trace_hb_mul_hb, fun _ hH => hOf_coords hH,
    coords_hOf, hOf_isHermitian, sum_hb_mul_self, sum_trace_smul_hb, oPt_mem_cone⟩

end GlobalTheory.CompanionTheory.HbBasis
