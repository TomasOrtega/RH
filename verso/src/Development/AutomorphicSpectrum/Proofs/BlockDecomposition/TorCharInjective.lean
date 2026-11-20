import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CPoly

noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount.Tope

variable {n : ℕ}

abbrev TorPt (n : ℕ) := {z : Fin n → ℂ // ∀ a, ‖z a‖ = 1}

def diagU (z : TorPt n) : Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨diagonal z.1, by
    rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
      ← diagonal_one]
    congr 1
    funext a
    rw [Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, z.2 a]
    simp⟩

def dualAct (E : KMod n) (k : Matrix.unitaryGroup (Fin n) ℂ) : Module.End ℂ (E.V →L[ℂ] ℂ) where
  toFun ξ := ξ ∘L E.ρ k⁻¹
  map_add' x y := ContinuousLinearMap.add_comp _ _ _
  map_smul' c x := ContinuousLinearMap.smul_comp _ _ _

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use `show diagonal z.1 * diagonal w.1 = diagonal w.1 * diagonal z.1`. Rewrite using `[diagonal_mul_diagonal, diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Conclude with `mul_comm _ _`.
-/
theorem diagU_comm (z w : TorPt n) : diagU z * diagU w = diagU w * diagU z := by
  apply Subtype.ext
  show diagonal z.1 * diagonal w.1 = diagonal w.1 * diagonal z.1
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext a
  exact mul_comm _ _

/- English proof (translation)
Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `ξ`. Use `show (ξ ∘L E.ρ (diagU w)⁻¹) ∘L E.ρ (diagU z)⁻¹ = (ξ ∘L E.ρ (diagU z)⁻¹) ∘L E.ρ (diagU w)⁻¹`. Rewrite using `[ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc]`. Use `congr 1`.

Rewrite using `[← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def, ← map_mul, ← map_mul, ← _root_.mul_inv_rev, ← _root_.mul_inv_rev, diagU_comm]`.
-/
theorem dualAct_comm (E : KMod n) (z w : TorPt n) : Commute (dualAct E (diagU z)) (dualAct E (diagU w)) := by
  apply LinearMap.ext
  intro ξ
  show (ξ ∘L E.ρ (diagU w)⁻¹) ∘L E.ρ (diagU z)⁻¹ = (ξ ∘L E.ρ (diagU z)⁻¹) ∘L E.ρ (diagU w)⁻¹
  rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc]
  congr 1
  rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def, ← map_mul, ← map_mul, ← _root_.mul_inv_rev,
    ← _root_.mul_inv_rev, diagU_comm]

def torChar (μ : Fin n → ℤ) (z : TorPt n) : ℂ := ∏ a, z.1 a ^ μ a

/- English proof (translation)
Introduce `μ ν h`. Assume the negation of the conclusion as `hne`. Take `⟨a, ha⟩ : ∃ a, μ a ≠ ν a` from `Function.ne_iff.1 hne`. Establish `hd : (μ a - ν a : ℤ) ≠ 0` using `sub_ne_zero.2 ha`. Use `set w : ℂ := Complex.exp (((Real.pi / ((μ a - ν a : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I) with hw`.

Establish `hw1 : ‖w‖ = 1` using `Complex.norm_exp_ofReal_mul_I _`. Establish `hw0 : w ≠ 0` using `Complex.exp_ne_zero _`. Apply the tactic sequence `let z : TorPt n := ⟨fun b => if b = a then w else 1, fun b => by by_cases hb : b = a <;> simp [hb, hw1]⟩`. Establish `hval : ∀ m : Fin n → ℤ, torChar m z = w ^ m a`. Introduce `m`.

Unfold `torChar`. Rewrite using `[Fintype.prod_eq_single a (fun b hb => by simp [z, hb])]`. Simplify using `[z]`. Establish `h1` using `congrFun h z`. Rewrite `h1` using `[hval, hval]`.

Establish `h2 : w ^ (μ a - ν a) = 1`. Rewrite using `[zpow_sub₀ hw0, h1, div_self (zpow_ne_zero _ hw0)]`. Establish `h3 : w ^ (μ a - ν a) = -1`. Rewrite using `[hw, ← Complex.exp_int_mul]`. Establish `hd' : ((μ a - ν a : ℤ) : ℂ) ≠ 0` using `Int.cast_ne_zero.2 hd`.

Establish `: (((μ a - ν a : ℤ)) : ℂ) * (((Real.pi / ((μ a - ν a : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I) = (Real.pi : ℂ) * Complex.I`. Move the coercions through the operations in `at hd' ⊢`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this, Complex.exp_pi_mul_I]`. Rewrite `h2` using `[h3]`.

Evaluate the numerical expressions using `at h2`.
-/
theorem torChar_injective : Function.Injective (torChar (n := n)) := by
  intro μ ν h
  by_contra hne
  obtain ⟨a, ha⟩ : ∃ a, μ a ≠ ν a := Function.ne_iff.1 hne
  have hd : (μ a - ν a : ℤ) ≠ 0 := sub_ne_zero.2 ha
  set w : ℂ := Complex.exp (((Real.pi / ((μ a - ν a : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I) with hw
  have hw1 : ‖w‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hw0 : w ≠ 0 := Complex.exp_ne_zero _
  let z : TorPt n := ⟨fun b => if b = a then w else 1, fun b => by by_cases hb : b = a <;> simp [hb, hw1]⟩
  have hval : ∀ m : Fin n → ℤ, torChar m z = w ^ m a := by
    intro m
    unfold torChar
    rw [Fintype.prod_eq_single a (fun b hb => by simp [z, hb])]
    simp [z]
  have h1 := congrFun h z
  rw [hval, hval] at h1
  have h2 : w ^ (μ a - ν a) = 1 := by
    rw [zpow_sub₀ hw0, h1, div_self (zpow_ne_zero _ hw0)]
  have h3 : w ^ (μ a - ν a) = -1 := by
    rw [hw, ← Complex.exp_int_mul]
    have hd' : ((μ a - ν a : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.2 hd
    have : (((μ a - ν a : ℤ)) : ℂ) * (((Real.pi / ((μ a - ν a : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I) =
        (Real.pi : ℂ) * Complex.I := by
      push_cast at hd' ⊢
      field_simp
    rw [this, Complex.exp_pi_mul_I]
  rw [h3] at h2
  norm_num at h2

/- English proof (translation)
Introduce `ξ hξ`. Use `(Submodule.mem_iInf _).2 fun z => ?_` and prove the remaining obligations. Apply `Module.End.eigenspace_le_maxGenEigenspace` to reduce the goal to its premises. Rewrite using `[Module.End.mem_eigenspace_iff]`. Conclude with `hξ (diagU z) z.1 rfl`.
-/
theorem wtDual_le_joint (E : KMod n) (μ : Fin n → ℤ) :
    wtDual E μ ≤ ⨅ z : TorPt n, (dualAct E (diagU z)).maxGenEigenspace (torChar μ z) := by
  intro ξ hξ
  refine (Submodule.mem_iInf _).2 fun z => ?_
  apply Module.End.eigenspace_le_maxGenEigenspace
  rw [Module.End.mem_eigenspace_iff]
  exact hξ (diagU z) z.1 rfl

/- English proof (translation)
Introduce `n E`. Establish `hind` using `Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun z : TorPt n => dualAct E (diagU z)) (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (dualAct_comm E j i) φ)`. Conclude with `(hind.comp torChar_injective).mono fun μ => wtDual_le_joint E μ`.
-/
theorem wtDual_iSupIndep : ∀ {n : ℕ} (E : KMod n), iSupIndep (wtDual E) := by
  intro n E
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
    (fun z : TorPt n => dualAct E (diagU z))
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (dualAct_comm E j i) φ)
  exact (hind.comp torChar_injective).mono fun μ => wtDual_le_joint E μ

end GlobalTheory.CompanionTheory.RealCount.Tope
