import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepArith

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

/- English proof (translation)
Rewrite using `[LinearMap.map_smul₂, LinearMap.map_smulₛₗ]`. Simplify using `only [smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rep_H_smul (L : PeriodPair) (m : Type) [Fintype m] [DecidableEq m] (ξ : ℂ) (z : m → ℂ) :
    stdH L m (ξ • z) (ξ • z) = ξ * conj ξ * stdH L m z z := by
  rw [LinearMap.map_smul₂, LinearMap.map_smulₛₗ]
  simp only [smul_eq_mul]
  ring

/- English proof (translation)
Take `⟨hac, -, hd8, -⟩` from `hOK`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k : ℤ, b = 2 * k + 1 := by`. Break down `Int.even_or_odd b with ⟨j, hj⟩ | ⟨j, hj⟩` into its components or cases. It suffices to derive a contradiction. Establish `h4 : (d : ℤ) = 4 * ((a : ℤ) * c - j * j)`.

Rewrite `hac` using `[hj]`. Take the linear combination `-hac`. Generalize the expression as in `(a : ℤ) * c - j * j = t at h4`. Use linear arithmetic over natural numbers and integers. Conclude with `⟨j, hj⟩`.

Establish `hadd` using `rep_theta_add_conj b d`. Establish `hmul` using `rep_theta_mul_conj a b c d hac`. Use `⟨cmTheta b d - (k : ℂ), a * c - k * b + k ^ 2, 1, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, map_intCast]`. Establish `hb : (b : ℂ) = 2 * k + 1`.

Rewrite using `[hk]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take the linear combination `hadd + hb`. Rewrite using `[map_sub, map_intCast]`.

Use `push_cast`. Rewrite using `[div_one]`. Take the linear combination `hmul - (k : ℂ) * hadd`. Introduce `h`. Establish `h1` using `Int.le_of_dvd one_pos h`.

Establish `h2` using `hl.one_lt`. Use linear arithmetic over natural numbers and integers. Introduce `v hv`. Unfold `SatMem at hv ⊢`. Take `⟨n, hn, hnv⟩` from `hv`.

Use `⟨n, hn, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_comm, sub_smul, Int.cast_smul_eq_zsmul]`. Conclude with `Λ.sub_mem (hθ _ hnv) (Λ.zsmul_mem hnv k)`.
-/
theorem rep_tau {m : Type} (a : ℕ) (b c : ℤ) (d : ℕ) (hOK : CmOK a b c d) (Λ : AddSubgroup (m → ℂ))
    (hθ : ∀ z ∈ Λ, cmTheta b d • z ∈ Λ) {l : ℕ} (hl : l.Prime) :
    ∃ τ : ℂ, ∃ r s : ℤ, τ + conj τ = 1 ∧ τ * conj τ = (r : ℂ) / s ∧ ¬ (l : ℤ) ∣ s ∧
      ∀ v : m → ℂ, SatMem l Λ v → SatMem l Λ (τ • v) := by
  obtain ⟨hac, -, hd8, -⟩ := hOK
  obtain ⟨k, hk⟩ : ∃ k : ℤ, b = 2 * k + 1 := by
    rcases Int.even_or_odd b with ⟨j, hj⟩ | ⟨j, hj⟩
    · exfalso
      have h4 : (d : ℤ) = 4 * ((a : ℤ) * c - j * j) := by
        rw [hj] at hac
        linear_combination -hac
      generalize (a : ℤ) * c - j * j = t at h4
      omega
    · exact ⟨j, hj⟩
  have hadd := rep_theta_add_conj b d
  have hmul := rep_theta_mul_conj a b c d hac
  refine ⟨cmTheta b d - (k : ℂ), a * c - k * b + k ^ 2, 1, ?_, ?_, ?_, ?_⟩
  · rw [map_sub, map_intCast]
    have hb : (b : ℂ) = 2 * k + 1 := by
      rw [hk]
      push_cast
      ring
    linear_combination hadd + hb
  · rw [map_sub, map_intCast]
    push_cast
    rw [div_one]
    linear_combination hmul - (k : ℂ) * hadd
  · intro h
    have h1 := Int.le_of_dvd one_pos h
    have h2 := hl.one_lt
    omega
  · intro v hv
    unfold SatMem at hv ⊢
    obtain ⟨n, hn, hnv⟩ := hv
    refine ⟨n, hn, ?_⟩
    rw [smul_comm, sub_smul, Int.cast_smul_eq_zsmul]
    exact Λ.sub_mem (hθ _ hnv) (Λ.zsmul_mem hnv k)

end PI.UnitaryGroupMassFormula.UnimodLocStd
