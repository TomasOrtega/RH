import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmulMemMMOfEqLphiUAdd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowSmulPhiMemMM
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.BK

/- English proof (translation)
Introduce `O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D y₀ hη hy n`. Establish `key (w : Vec K a ι) (hw : w ∈ D.MM) : (l : K) ^ η • D.phi w ∈ D.MM` using `PhiMod.pow_smul_phi_mem_MM O K l e a ι D.toPhiMod η D.upper w hw`. Proceed by induction on `n with`. Consider the case `zero`. Establish `hE : E K l e ∈ S O K e` using `E_mem l e _`.

Establish `hNE : N K (E K l e) ∈ S O K e`. Rewrite using `[N_apply]`. Conclude with `mul_mem HasU.X_mem (derivative_mem_S hE)`. Establish `h0 : (l : K) ^ η • D.phi y₀ ∈ D.MM` using `D.l_pow_smul_phi_mem_MM (D.Mext_mono (A_le_S l e) hy)`. Establish `hA : (l : K) ^ (H + 2 * η + 1) • D.phi y₀ ∈ D.MM`.

Use `D.l_pow_smul_mem_MM (H + η + 1) h0` as an intermediate fact. Rewrite `this` using `[smul_smul, ← pow_add, show H + η + 1 + η = H + 2 * η + 1 by ring]`. Then use the resulting hypothesis. Establish `hk : E K l e ^ (H + η) • y₀ ∈ D.MM`. Rewrite using `[pow_add, mul_smul]`. Conclude with `D.ext_mono (A_le_S l e) (D.lower _ hy)`.

Establish `h1 : E K l e ^ (H + η + 1) • D.conn y₀ ∈ D.MM`. Establish `h2` using `sub_mem (D.smul_mem_MM hE (D.conn_mem_MM hk)) (D.smul_mem_MM (mul_mem (natCast_mem _ (H + η)) hNE) hk)`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[PhiMod.conn_smul, N_apply, derivative_pow]`. Generalize the expression as in `H + η = k`.

Use extensionality with `τ i : 2`. Simplify using `only [smul_eq_mul, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, N_apply]`. Consider the cases of `k with`. Consider the case `zero => simp`. Consider the case `succ k => simp only [Nat.add_sub_cancel]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h3` using `D.smul_mem_Mext (A_le_S l e) h1`. Rewrite `h3` using `[smul_smul, ← pow_add]`. Establish `hB` using `D.l_pow_smul_phi_mem_MM h3`. Rewrite `hB` using `[show η + (H + η + 1) = H + 2 * η + 1 by ring]`.

Use `⟨(e : K⟦X⟧) • ((l : K) ^ (H + 2 * η + 1) • D.phi y₀) + (l : K) ^ (H + 2 * η + 1) • D.phi (D.conn y₀), add_mem (D.smul_mem_MM (natCast_mem _ e) hA) hB, ?_⟩` and prove the remaining obligations. Establish `hc : D.conn ((X : K⟦X⟧) ^ e • y₀) = (X : K⟦X⟧) ^ e • ((e : K⟦X⟧) • y₀ + D.conn y₀)`. Rewrite using `[PhiMod.conn_smul, smul_add, smul_smul]`. Use `congr 2`. Use extensionality with `n`.

Rewrite using `[coeff_N, ← map_natCast (C : K →+* K⟦X⟧), coeff_mul_C, coeff_X_pow]`. Apply the tactic sequence `split_ifs with h <;> simp [h]`. Rewrite using `[zero_mul, add_zero, zero_add, pow_one, pow_one, hc, PhiMod.lphi_apply, PhiMod.phi_smul, map_add, PhiMod.phi_smul, map_pow, frob_X, ← pow_mul, map_natCast, mul_comm l e]`. Simplify using `only [smul_add, smul_smul, pow_succ]`. Apply the tactic sequence `congr 1 <;> exact smul_comm _ _ _`.

Consider the case `succ n ih`. Take `⟨w, hw, h⟩` from `ih`. Use `⟨_, key w hw, ?_⟩` and prove the remaining obligations. Rewrite using `[show H + 2 * η + (n + 1) * (η - 1) = (η - 1) + (H + 2 * η + n * (η - 1)) by ring, pow_add, mul_smul, pow_succ', Module.End.mul_apply, ← map_smul, h, PhiMod.lphi_apply, PhiMod.phi_smul, map_pow, frob_X, ← pow_mul, smul_smul, ← pow_succ, Nat.sub_add_cancel hη, smul_comm]`. Use `congr 2`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem lphi_pow_conn_X_pow_smul_mem : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ (y₀ : Vec K a ι), 1 ≤ η → E K l e ^ η • y₀ ∈ D.M → ∀ n : ℕ, ∃ w ∈ D.MM, (l : K) ^ (H + 2 * η + n * (η - 1)) • (D.lphi ^ (n + 1)) (D.conn ((X : K⟦X⟧) ^ e • y₀)) = (X : K⟦X⟧) ^ (e * l ^ (n + 1)) • w := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D y₀ hη hy n
  have key (w : Vec K a ι) (hw : w ∈ D.MM) : (l : K) ^ η • D.phi w ∈ D.MM :=
    PhiMod.pow_smul_phi_mem_MM O K l e a ι D.toPhiMod η D.upper w hw
  induction n with
  | zero =>
    have hE : E K l e ∈ S O K e := E_mem l e _
    have hNE : N K (E K l e) ∈ S O K e := by
      rw [N_apply]; exact mul_mem HasU.X_mem (derivative_mem_S hE)

    have h0 : (l : K) ^ η • D.phi y₀ ∈ D.MM :=
      D.l_pow_smul_phi_mem_MM (D.Mext_mono (A_le_S l e) hy)
    have hA : (l : K) ^ (H + 2 * η + 1) • D.phi y₀ ∈ D.MM := by
      have := D.l_pow_smul_mem_MM (H + η + 1) h0
      rwa [smul_smul, ← pow_add, show H + η + 1 + η = H + 2 * η + 1 by ring] at this

    have hk : E K l e ^ (H + η) • y₀ ∈ D.MM := by
      rw [pow_add, mul_smul]
      exact D.ext_mono (A_le_S l e) (D.lower _ hy)
    have h1 : E K l e ^ (H + η + 1) • D.conn y₀ ∈ D.MM := by
      have h2 := sub_mem (D.smul_mem_MM hE (D.conn_mem_MM hk))
        (D.smul_mem_MM (mul_mem (natCast_mem _ (H + η)) hNE) hk)
      convert h2 using 1
      rw [PhiMod.conn_smul, N_apply, derivative_pow]
      generalize H + η = k
      ext τ i : 2
      simp only [smul_eq_mul, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, N_apply]
      cases k with
      | zero => simp
      | succ k => simp only [Nat.add_sub_cancel]; ring
    have h3 := D.smul_mem_Mext (A_le_S l e) h1
    rw [smul_smul, ← pow_add] at h3
    have hB := D.l_pow_smul_phi_mem_MM h3
    rw [show η + (H + η + 1) = H + 2 * η + 1 by ring] at hB
    refine ⟨(e : K⟦X⟧) • ((l : K) ^ (H + 2 * η + 1) • D.phi y₀) +
      (l : K) ^ (H + 2 * η + 1) • D.phi (D.conn y₀),
      add_mem (D.smul_mem_MM (natCast_mem _ e) hA) hB, ?_⟩
    have hc : D.conn ((X : K⟦X⟧) ^ e • y₀) = (X : K⟦X⟧) ^ e • ((e : K⟦X⟧) • y₀ + D.conn y₀) := by
      rw [PhiMod.conn_smul, smul_add, smul_smul]
      congr 2
      ext n
      rw [coeff_N, ← map_natCast (C : K →+* K⟦X⟧), coeff_mul_C, coeff_X_pow]
      split_ifs with h <;> simp [h]
    rw [zero_mul, add_zero, zero_add, pow_one, pow_one, hc, PhiMod.lphi_apply, PhiMod.phi_smul, map_add,
      PhiMod.phi_smul, map_pow, frob_X, ← pow_mul, map_natCast, mul_comm l e]
    simp only [smul_add, smul_smul, pow_succ]
    congr 1 <;> exact smul_comm _ _ _
  | succ n ih =>
    obtain ⟨w, hw, h⟩ := ih
    refine ⟨_, key w hw, ?_⟩
    rw [show H + 2 * η + (n + 1) * (η - 1) = (η - 1) + (H + 2 * η + n * (η - 1)) by ring, pow_add,
      mul_smul, pow_succ', Module.End.mul_apply, ← map_smul, h, PhiMod.lphi_apply, PhiMod.phi_smul,
      map_pow, frob_X, ← pow_mul, smul_smul, ← pow_succ, Nat.sub_add_cancel hη, smul_comm]
    congr 2
    ring

end GlobalTheory.BK
