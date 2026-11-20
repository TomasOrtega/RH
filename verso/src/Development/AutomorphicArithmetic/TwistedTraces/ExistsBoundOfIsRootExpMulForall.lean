import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

/- English proof (translation)
Introduce `d p hp`. Establish `hfin : Set.Finite {z : ℂ | ∀ t : ℝ, (p t).IsRoot (Complex.exp (z * t))}`. Assume the negation of the conclusion as `hinf`. Take `⟨F, hF, hcard⟩` from `Set.Infinite.exists_subset_card_eq hinf (d + 1)`. Take `⟨R, hR⟩` from `(F.finite_toSet.isBounded).exists_norm_le`.

Use `set S : ℝ := |R| + 1 with hS`. Establish `hSpos : 0 < S` using `by positivity`. Establish `hRS : ∀ z ∈ F, ‖z‖ ≤ S` using `fun z hz => by`. Establish `h1` using `hR z (Finset.mem_coe.mpr hz)`. Establish `h2` using `le_abs_self R`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `set t : ℝ := S⁻¹ with ht`. Establish `htpos : 0 < t` using `inv_pos.mpr hSpos`. Establish `hn : ∀ z ∈ F, ‖z * (t : ℂ)‖ ≤ 1` using `fun z hz => by`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos, ht]`.

Rewrite using `[mul_inv_le_iff₀ hSpos, one_mul]`. Conclude with `hRS z hz`. Establish `hinj : Set.InjOn (fun z : ℂ => Complex.exp (z * (t : ℂ))) F`. Introduce `z hz w hw h`. Take `⟨n, hn'⟩` from `Complex.exp_eq_exp_iff_exists_int.mp h`.

Establish `h1` using `hn z hz`. Establish `h2` using `hn w hw`. Establish `h3 : ‖(n : ℂ) * (2 * Real.pi * Complex.I)‖ ≤ 2`. Establish `: (n : ℂ) * (2 * Real.pi * Complex.I) = z * t - w * t` using `by rw [hn']; ring`. Rewrite using `[this]`.

Use `norm_sub_le (z * (t : ℂ)) (w * t)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hn0 : n = 0`. Assume the negation of the conclusion as `hne`. Establish `h4 : (1 : ℝ) ≤ |(n : ℝ)|` using `by exact_mod_cast Int.one_le_abs hne`.

Establish `h5 : ‖(n : ℂ) * (2 * Real.pi * Complex.I)‖ = |(n : ℝ)| * (2 * Real.pi)`. Simplify using `[abs_of_pos Real.pi_pos]`. Establish `h6` using `Real.pi_gt_three`. Rewrite `h3` using `[h5]`. Use the polynomial consequences of the given equalities and inequalities.

Rewrite `hn'` using `[hn0]`. Establish `htne : (t : ℂ) ≠ 0` using `by exact_mod_cast htpos.ne'`. Establish `: z * (t : ℂ) = w * t` using `by simpa using hn'`. Conclude with `mul_right_cancel₀ htne this`. Establish `hsub : (F.image (fun z : ℂ => Complex.exp (z * (t : ℂ)))).val ⊆ (p t).roots`.

Introduce `x hx`. Take `⟨z, hz, rfl⟩` from `Finset.mem_image.mp (Finset.mem_val.mp hx)`. Conclude with `(Polynomial.mem_roots (hp t).1).mpr (hF (Finset.mem_coe.mpr hz) t)`. Establish `hle` using `Polynomial.card_le_degree_of_subset_roots hsub`. Rewrite `hle` using `[Finset.card_image_of_injOn hinj, hcard]`.

Use `(hp t).2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨M, hM⟩` from `hfin.isBounded.exists_norm_le`. Conclude with `⟨M, fun z hz => hM z hz⟩`.
-/
theorem UpperTheory.exists_bound_of_isRoot_exp_mul_forall :
    ∀ (d : ℕ) (p : ℝ → ℂ[X]), (∀ t, p t ≠ 0 ∧ (p t).natDegree ≤ d) → ∃ M : ℝ, ∀ z : ℂ, (∀ t : ℝ, (p t).IsRoot (Complex.exp (z * t))) → ‖z‖ ≤ M := by
  intro d p hp
  classical
  have hfin : Set.Finite {z : ℂ | ∀ t : ℝ, (p t).IsRoot (Complex.exp (z * t))} := by
    by_contra hinf
    obtain ⟨F, hF, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (d + 1)
    obtain ⟨R, hR⟩ := (F.finite_toSet.isBounded).exists_norm_le
    set S : ℝ := |R| + 1 with hS
    have hSpos : 0 < S := by positivity
    have hRS : ∀ z ∈ F, ‖z‖ ≤ S := fun z hz => by
      have h1 := hR z (Finset.mem_coe.mpr hz)
      have h2 := le_abs_self R
      linarith
    set t : ℝ := S⁻¹ with ht
    have htpos : 0 < t := inv_pos.mpr hSpos
    have hn : ∀ z ∈ F, ‖z * (t : ℂ)‖ ≤ 1 := fun z hz => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos, ht]
      rw [mul_inv_le_iff₀ hSpos, one_mul]
      exact hRS z hz
    have hinj : Set.InjOn (fun z : ℂ => Complex.exp (z * (t : ℂ))) F := by
      intro z hz w hw h
      obtain ⟨n, hn'⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
      have h1 := hn z hz
      have h2 := hn w hw
      have h3 : ‖(n : ℂ) * (2 * Real.pi * Complex.I)‖ ≤ 2 := by
        have : (n : ℂ) * (2 * Real.pi * Complex.I) = z * t - w * t := by rw [hn']; ring
        rw [this]
        have := norm_sub_le (z * (t : ℂ)) (w * t)
        linarith
      have hn0 : n = 0 := by
        by_contra hne
        have h4 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hne
        have h5 : ‖(n : ℂ) * (2 * Real.pi * Complex.I)‖ = |(n : ℝ)| * (2 * Real.pi) := by
          simp [abs_of_pos Real.pi_pos]
        have h6 := Real.pi_gt_three
        rw [h5] at h3
        nlinarith
      rw [hn0] at hn'
      have htne : (t : ℂ) ≠ 0 := by exact_mod_cast htpos.ne'
      have : z * (t : ℂ) = w * t := by simpa using hn'
      exact mul_right_cancel₀ htne this
    have hsub : (F.image (fun z : ℂ => Complex.exp (z * (t : ℂ)))).val ⊆ (p t).roots := by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp (Finset.mem_val.mp hx)
      exact (Polynomial.mem_roots (hp t).1).mpr (hF (Finset.mem_coe.mpr hz) t)
    have hle := Polynomial.card_le_degree_of_subset_roots hsub
    rw [Finset.card_image_of_injOn hinj, hcard] at hle
    have := (hp t).2
    omega
  obtain ⟨M, hM⟩ := hfin.isBounded.exists_norm_le
  exact ⟨M, fun z hz => hM z hz⟩
