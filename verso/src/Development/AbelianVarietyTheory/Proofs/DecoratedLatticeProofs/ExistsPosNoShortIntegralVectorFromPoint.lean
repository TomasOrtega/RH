import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.HeightBoundSetup

noncomputable section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

namespace GlobalTheory.CuspGeo.FirstMinPos

/- English proof (translation)
Use `(pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_left (norm_le_pi_norm x j) (norm_nonneg _)`. Use `_ = (∑ j, ‖A i j‖) * ‖x‖ := by rw [Finset.sum_mul]`.

Use `_ ≤ (∑ i, ∑ j, ‖A i j‖) * ‖x‖ := by`. Use `mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun i => ∑ j, ‖A i j‖) (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i)`.
-/
theorem norm_mulVec_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    ‖A *ᵥ x‖ ≤ (∑ i, ∑ j, ‖A i j‖) * ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  calc ‖(A *ᵥ x) i‖ = ‖∑ j, A i j * x j‖ := rfl
    _ ≤ ∑ j, ‖A i j * x j‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖A i j‖ * ‖x‖ := Finset.sum_le_sum fun j _ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x j) (norm_nonneg _)
    _ = (∑ j, ‖A i j‖) * ‖x‖ := by rw [Finset.sum_mul]
    _ ≤ (∑ i, ∑ j, ‖A i j‖) * ‖x‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact Finset.single_le_sum (f := fun i => ∑ j, ‖A i j‖)
          (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i)

variable (I : AutInst)

/- English proof (translation)
Establish `hs : ∀ v (b : I.E), I.φ v (star b) = star (I.φ v b)` using `fun v b => I.cm.cmUnram.2.1 _ b`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `hfin` using `CompanionTheory.D.gk.RF.PE.finite_bdd I hs 1`. Establish `hmem : ∀ k : ℕ, a ^ k ∈ {x : I.E | IsIntegral ℤ x ∧ ∀ v, ‖I.φ v x‖ ≤ 1}` using `fun k => ⟨ha.pow k, fun v => by rw [map_pow, norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hc v).le⟩`.

Take `⟨m, k, hmk, he⟩` from `hfin.exists_lt_map_eq_of_forall_mem hmem`. Take `⟨v⟩` from `(inferInstance : Nonempty (InfinitePlace I.F))`. Establish `hpos : 0 < ‖I.φ v a‖` using `norm_pos_iff.2 ((map_ne_zero _).2 h0)`. Establish `h1` using `congrArg (fun b => ‖I.φ v b‖) he`. Simplify using `only [map_pow, norm_pow] at h1`.

Conclude with `absurd h1 (pow_lt_pow_right_of_lt_one₀ hpos (hc v) hmk).ne'`.
-/
theorem exists_one_le_norm {a : I.E} (ha : IsIntegral ℤ a) (h0 : a ≠ 0) : ∃ v, 1 ≤ ‖I.φ v a‖ := by
  have hs : ∀ v (b : I.E), I.φ v (star b) = star (I.φ v b) := fun v b => I.cm.cmUnram.2.1 _ b
  by_contra hc
  push_neg at hc
  have hfin := CompanionTheory.D.gk.RF.PE.finite_bdd I hs 1
  have hmem : ∀ k : ℕ, a ^ k ∈ {x : I.E | IsIntegral ℤ x ∧ ∀ v, ‖I.φ v x‖ ≤ 1} := fun k =>
    ⟨ha.pow k, fun v => by rw [map_pow, norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hc v).le⟩
  obtain ⟨m, k, hmk, he⟩ := hfin.exists_lt_map_eq_of_forall_mem hmem
  obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace I.F))
  have hpos : 0 < ‖I.φ v a‖ := norm_pos_iff.2 ((map_ne_zero _).2 h0)
  have h1 := congrArg (fun b => ‖I.φ v b‖) he
  simp only [map_pow, norm_pow] at h1
  exact absurd h1 (pow_lt_pow_right_of_lt_one₀ hpos (hc v) hmk).ne'

/- English proof (translation)
Establish `hP : I.P v * (I.P v)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))`. Establish `hy : uMat (y v) * uMat (y v)⁻¹ = 1` using `CompanionTheory.D.gk.RF.PE.uMat_mul_inv (y v)`. Simplify using `only [vec, mulVec_mulVec, Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (uMat (y v)), hy, Matrix.one_mul, hP, one_mulVec]`.
-/
theorem coords_eq (y : I.Ginf) (u : Fin I.n → I.E) (v : InfinitePlace I.F) :
    (fun i => I.φ v (u i)) = (I.P v * uMat (y v)) *ᵥ vec I y u v := by
  have hP : I.P v * (I.P v)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))
  have hy : uMat (y v) * uMat (y v)⁻¹ = 1 := CompanionTheory.D.gk.RF.PE.uMat_mul_inv (y v)
  simp only [vec, mulVec_mulVec, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (uMat (y v)), hy, Matrix.one_mul, hP, one_mulVec]

def cst (y : I.Ginf) (v : InfinitePlace I.F) : ℝ := ∑ i, ∑ j, ‖(I.P v * uMat (y v)) i j‖

/- English proof (translation)
The claim follows from `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _`.
-/
theorem cst_nonneg (y : I.Ginf) (v : InfinitePlace I.F) : 0 ≤ cst I y v :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

/- English proof (translation)
Establish `e` using `congrFun (coords_eq I y u v) i`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_phi_le (y : I.Ginf) (u : Fin I.n → I.E) (v : InfinitePlace I.F) (i : Fin I.n) :
    ‖I.φ v (u i)‖ ≤ cst I y v * ‖vec I y u‖ := by
  have e := congrFun (coords_eq I y u v) i
  calc ‖I.φ v (u i)‖ = ‖((I.P v * uMat (y v)) *ᵥ vec I y u v) i‖ := by rw [← e]
    _ ≤ ‖(I.P v * uMat (y v)) *ᵥ vec I y u v‖ := norm_le_pi_norm _ i
    _ ≤ cst I y v * ‖vec I y u v‖ := norm_mulVec_le _ _
    _ ≤ cst I y v * ‖vec I y u‖ := mul_le_mul_of_nonneg_left (norm_le_pi_norm _ v) (cst_nonneg I y v)

end GlobalTheory.CuspGeo.FirstMinPos

namespace GlobalTheory.CuspGeo

open FirstMinPos in

/- English proof (translation)
Introduce `I y`. Establish `hK0 : 0 < ∑ v, cst I y v + 1` using `add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun v _ => cst_nonneg I y v) one_pos`. Use `⟨1 / (∑ v, cst I y v + 1), by positivity, fun u hu h0 => ?_⟩` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, u i ≠ 0 := by`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Conclude with `h0 (funext hc)`. Take `⟨v, hv⟩` from `exists_one_le_norm I (hu i) hi`. Establish `h2 : cst I y v ≤ ∑ v, cst I y v + 1`. Use `Finset.single_le_sum (f := cst I y) (fun v _ => cst_nonneg I y v) (Finset.mem_univ v)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[div_le_iff₀ hK0]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem firstMin_pos : ∀ (I : AutInst) (y : I.Ginf), ∃ t : ℝ, 0 < t ∧ NoShort I y t := by
  intro I y
  have hK0 : 0 < ∑ v, cst I y v + 1 :=
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun v _ => cst_nonneg I y v) one_pos
  refine ⟨1 / (∑ v, cst I y v + 1), by positivity, fun u hu h0 => ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra hc; push_neg at hc; exact h0 (funext hc)
  obtain ⟨v, hv⟩ := exists_one_le_norm I (hu i) hi
  have h2 : cst I y v ≤ ∑ v, cst I y v + 1 := by
    have := Finset.single_le_sum (f := cst I y) (fun v _ => cst_nonneg I y v) (Finset.mem_univ v)
    linarith
  rw [div_le_iff₀ hK0]
  calc (1 : ℝ) ≤ cst I y v * ‖vec I y u‖ := hv.trans (norm_phi_le I y u v i)
    _ ≤ (∑ v, cst I y v + 1) * ‖vec I y u‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ = ‖vec I y u‖ * (∑ v, cst I y v + 1) := mul_comm _ _

end GlobalTheory.CuspGeo

end
