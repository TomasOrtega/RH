import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ZhatSectionExists
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped ENNReal

namespace GlobalTheory.CellRep

/- English proof (translation)
Establish `hb : u.BlockTriangular id` using `fun i j h => hu.1 i j h`. Rewrite using `[Matrix.det_of_upperTriangular hb]`. Simplify using `[hu.2]`.
-/
lemma det_upUni {m : ℕ} {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ Formalism.FourierDecayAlt.C2.UTset m) : u.det = 1 := by
  have hb : u.BlockTriangular id := fun i j h => hu.1 i j h
  rw [Matrix.det_of_upperTriangular hb]
  simp [hu.2]

/- English proof (translation)
Introduce `k r z z' γ p hz hz' hT hT' hγ ⟨L, U, hL, hU, hZ⟩`. Use `set d : Fin (r + 1) → ℂ := fun b => (-1 : ℂ) ^ (r - b.val) with hd`. Establish `hdd : ∀ b, d b * d b = 1` using `fun b => by`. Simplify using `only [hd]`. Rewrite using `[← mul_pow]`.

Simplify using the standard rewrite rules. Use `set D : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.diagonal d with hD`. Establish `hDD : D * D = 1`. Rewrite using `[hD, Matrix.diagonal_mul_diagonal]`. Simplify using `[hdd]`.

Establish `hO : ∀ g, ZhatO k r z z' g = Zhat k r z z' g * D` using `fun g => by`. Use extensionality with `a b`. Rewrite using `[hD, Matrix.mul_diagonal, mul_comm]`. Both sides reduce to the same expression. Establish `hLU : Lᴴ ∈ Formalism.FourierDecayAlt.C2.UTset (r + 1)` using `⟨fun i j h => by simp [Matrix.conjTranspose_apply, (hL j i).1 h], fun i => by simp [Matrix.conjTranspose_apply, (hL i i).2 rfl]⟩`.

Establish `hUU : U ∈ Formalism.FourierDecayAlt.C2.UTset (r + 1)` using `⟨fun i j h => (hU i j).1 h, fun i => (hU i i).2 rfl⟩`. Establish `hU' : D * U * D ∈ Formalism.FourierDecayAlt.C2.UTset (r + 1)` using `⟨fun i j h => by simp [hD, Matrix.mul_diagonal, Matrix.diagonal_mul, (hU i j).1 h], fun i => by simp [hD, Matrix.mul_diagonal, Matrix.diagonal_mul, (hU i i).2 rfl, hdd]⟩`. Take `⟨ha, -, hau⟩` from `Formalism.FourierDecayAlt.P.c2_tau_mem k r z ⟨hz, hT⟩ _ hLU`. Take `⟨hb, -, hbu⟩` from `Formalism.FourierDecayAlt.P.c2_tau_mem k r z' ⟨hz', hT'⟩ _ hU'`. Use `set a := Formalism.FourierDecayAlt.C2.tauM k r z Lᴴ`.

Use `set b := Formalism.FourierDecayAlt.C2.tauM k r z' (D * U * D)`. Establish `hS : ∀ (w : Fin (2 * r + k + 1) → ℂ) (n : MatKR k r), n ∈ Nset k r → n ∈ Sset k r w` using `fun w n hn => ⟨1, ⟨WeylGroupFacts.uh_one, fun _ => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩, n, hn, (Matrix.one_mul n).symm⟩`. Establish `hai` using `WeylGroupFacts.mem_n_inv ha`. Establish `hbi` using `WeylGroupFacts.mem_n_inv hb`. Establish `hau' : IsUnit a.det` using `WeylGroupFacts.isUnit_of_uh ha.1`.

Establish `hbu' : IsUnit b.det` using `WeylGroupFacts.isUnit_of_uh hb.1`. Establish `hg : a * γ * b⁻¹ ∈ UH (Hpk k r)` using `WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul ha.1 hγ) hbi.1`. Establish `he : γ = a⁻¹ * (a * γ * b⁻¹) * b`. Rewrite using `[Matrix.mul_assoc a, Matrix.nonsing_inv_mul_cancel_left _ _ hau', Matrix.nonsing_inv_mul_cancel_right _ _ hbu']`. Use `⟨a⁻¹, hai, b, hb, a * γ * b⁻¹, hg, he, ?_⟩` and prove the remaining obligations.

Establish `hE` using `Formalism.FourierDecayAlt.P.zhat_equivalence k r z z' ⟨hz, hT⟩ ⟨hz', hT'⟩ a (hS z a ha) b (hS z' b hb) (a * γ * b⁻¹)`. Rewrite `hE` using `[← he, hau, hbu, Matrix.conjTranspose_conjTranspose]`. Establish `h1 : L * ZhatO k r z z' (a * γ * b⁻¹) * U = L * ptMat p * U`. Rewrite using `[← hZ, hO, hO γ, hE]`. Simplify using `only [Matrix.mul_assoc, hDD, Matrix.mul_one]`.

Establish `hLu : IsUnit L.det`. Use `det_upUni hLU` as an intermediate fact. Rewrite `this` using `[Matrix.det_conjTranspose]`. Establish `h2 : L.det = 1` using `by simpa using congrArg star this`. Rewrite using `[h2]`.

Conclude with `isUnit_one`. Establish `hUu : IsUnit U.det` using `by rw [det_upUni hUU]; exact isUnit_one`. Establish `h2` using `congrArg (fun X => L⁻¹ * (X * U⁻¹)) h1`. Simplify `h2` using `only [Matrix.mul_nonsing_inv_cancel_right _ _ hUu, Matrix.nonsing_inv_mul_cancel_left _ _ hLu]`.
-/
theorem cell_rep : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : MatKR k r) (p : Point ℂ (r + 1)), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → γ ∈ UH (Hpk k r) → IsInCell (ZhatO k r z z' γ) p → ∃ n ∈ Nset k r, ∃ n' ∈ Nset k r, ∃ g₀ ∈ UH (Hpk k r), γ = n * g₀ * n' ∧ ZhatO k r z z' g₀ = ptMat p := by
  intro k r z z' γ p hz hz' hT hT' hγ ⟨L, U, hL, hU, hZ⟩
  set d : Fin (r + 1) → ℂ := fun b => (-1 : ℂ) ^ (r - b.val) with hd
  have hdd : ∀ b, d b * d b = 1 := fun b => by
    simp only [hd]; rw [← mul_pow]; simp
  set D : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.diagonal d with hD
  have hDD : D * D = 1 := by
    rw [hD, Matrix.diagonal_mul_diagonal]; simp [hdd]
  have hO : ∀ g, ZhatO k r z z' g = Zhat k r z z' g * D := fun g => by
    ext a b
    rw [hD, Matrix.mul_diagonal, mul_comm]; rfl
  have hLU : Lᴴ ∈ Formalism.FourierDecayAlt.C2.UTset (r + 1) :=
    ⟨fun i j h => by simp [Matrix.conjTranspose_apply, (hL j i).1 h],
     fun i => by simp [Matrix.conjTranspose_apply, (hL i i).2 rfl]⟩
  have hUU : U ∈ Formalism.FourierDecayAlt.C2.UTset (r + 1) := ⟨fun i j h => (hU i j).1 h, fun i => (hU i i).2 rfl⟩
  have hU' : D * U * D ∈ Formalism.FourierDecayAlt.C2.UTset (r + 1) :=
    ⟨fun i j h => by simp [hD, Matrix.mul_diagonal, Matrix.diagonal_mul, (hU i j).1 h],
     fun i => by simp [hD, Matrix.mul_diagonal, Matrix.diagonal_mul, (hU i i).2 rfl, hdd]⟩
  obtain ⟨ha, -, hau⟩ := Formalism.FourierDecayAlt.P.c2_tau_mem k r z ⟨hz, hT⟩ _ hLU
  obtain ⟨hb, -, hbu⟩ := Formalism.FourierDecayAlt.P.c2_tau_mem k r z' ⟨hz', hT'⟩ _ hU'
  set a := Formalism.FourierDecayAlt.C2.tauM k r z Lᴴ
  set b := Formalism.FourierDecayAlt.C2.tauM k r z' (D * U * D)
  have hS : ∀ (w : Fin (2 * r + k + 1) → ℂ) (n : MatKR k r), n ∈ Nset k r → n ∈ Sset k r w :=
    fun w n hn => ⟨1, ⟨WeylGroupFacts.uh_one, fun _ => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩,
      Matrix.one_mulVec _⟩, n, hn, (Matrix.one_mul n).symm⟩
  have hai := WeylGroupFacts.mem_n_inv ha
  have hbi := WeylGroupFacts.mem_n_inv hb
  have hau' : IsUnit a.det := WeylGroupFacts.isUnit_of_uh ha.1
  have hbu' : IsUnit b.det := WeylGroupFacts.isUnit_of_uh hb.1
  have hg : a * γ * b⁻¹ ∈ UH (Hpk k r) := WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul ha.1 hγ) hbi.1
  have he : γ = a⁻¹ * (a * γ * b⁻¹) * b := by
    rw [Matrix.mul_assoc a, Matrix.nonsing_inv_mul_cancel_left _ _ hau',
      Matrix.nonsing_inv_mul_cancel_right _ _ hbu']
  refine ⟨a⁻¹, hai, b, hb, a * γ * b⁻¹, hg, he, ?_⟩
  have hE := Formalism.FourierDecayAlt.P.zhat_equivalence k r z z' ⟨hz, hT⟩ ⟨hz', hT'⟩ a (hS z a ha) b (hS z' b hb)
    (a * γ * b⁻¹)
  rw [← he, hau, hbu, Matrix.conjTranspose_conjTranspose] at hE
  have h1 : L * ZhatO k r z z' (a * γ * b⁻¹) * U = L * ptMat p * U := by
    rw [← hZ, hO, hO γ, hE]
    simp only [Matrix.mul_assoc, hDD, Matrix.mul_one]
  have hLu : IsUnit L.det := by
    have := det_upUni hLU
    rw [Matrix.det_conjTranspose] at this
    have h2 : L.det = 1 := by simpa using congrArg star this
    rw [h2]; exact isUnit_one
  have hUu : IsUnit U.det := by rw [det_upUni hUU]; exact isUnit_one
  have h2 := congrArg (fun X => L⁻¹ * (X * U⁻¹)) h1
  simpa only [Matrix.mul_nonsing_inv_cancel_right _ _ hUu, Matrix.nonsing_inv_mul_cancel_left _ _ hLu] using h2

end GlobalTheory.CellRep
