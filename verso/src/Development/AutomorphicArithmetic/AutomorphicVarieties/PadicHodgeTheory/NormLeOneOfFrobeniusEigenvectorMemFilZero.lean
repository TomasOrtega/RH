import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsAlgebraicElementOfAlgebraicVectorSubspace
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

/- English proof (translation)
Introduce `l _ c δ hc hφ hF`. Assume the negation of the conclusion as `hδ`. Establish `hδ0 : δ ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hδ`.

Establish `hv : δ.valuation < 0`. Assume the negation of the conclusion as `h`. Conclude with `hδ ((Padic.norm_le_one_iff_val_nonneg δ).2 (not_lt.1 h))`. Take `⟨a, ha⟩ : ∃ a : ℕ, ((a + 1 : ℕ) : ℤ) = -δ.valuation` from `⟨(-δ.valuation - 1).toNat, by push_cast; omega⟩`. Establish `hl : (l : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero`.

Establish `hu : ‖δ * (l : ℚ_[l]) ^ (a + 1)‖ = 1`. Rewrite using `[norm_mul, Padic.norm_p_pow, Padic.norm_eq_zpow_neg_valuation hδ0, ← zpow_add₀ hl, ha]`. Simplify using the standard rewrite rules. Set `u : ℤ_[l]` to `⟨δ * (l : ℚ_[l]) ^ (a + 1), hu.le⟩`. Establish `huu : IsUnit u` using `PadicInt.isUnit_iff.2 hu`.

Take `⟨N, N', hNN, hN, hN', hφN, -⟩` from `UpperTheory.exists_algebraic_element_of_algebraicVectorSubspace (l := l) (n := 1) (Matrix.of fun _ _ => u) (by rw [Matrix.det_fin_one]; exact huu)`. Use `set P := PP l with hP`. Use `set D := P.PD (botExt l) with hD`. Establish `h1 : N 0 0 * N' 0 0 = 1`. Use `congrFun (congrFun hNN 0) 0` as an intermediate fact.

Simplify `this` using `[Matrix.mul_apply]`. Establish `h2 : P.φB (N 0 0) = algebraMap ℚ_[l] (Bcr l) (δ * (l : ℚ_[l]) ^ (a + 1)) * N 0 0`. Use `congrFun (congrFun hφN 0) 0` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, Fin.sum_univ_one]`. Conclude with `this`.

Use `set w := N 0 0`. Use `set w' := N' 0 0 with hw'`. Establish `h3 : algebraMap ℚ_[l] (Bcr l) (δ * (l : ℚ_[l]) ^ (a + 1)) * P.φB w' = w'`. Establish `h` using `congrArg P.φB h1`. Rewrite `h` using `[map_mul, map_one, h2]`.

Take the linear combination `w' * h - (algebraMap ℚ_[l] (Bcr l) (δ * (l : ℚ_[l]) ^ (a + 1)) * P.φB w') * h1`. Establish `ht : P.φB D.t = algebraMap ℚ_[l] (Bcr l) (l : ℚ_[l]) * D.t`. Use `D.t_φ` as an intermediate fact. Rewrite `this` using `[P.PD_φ, P.PD_p, Algebra.smul_def]`. Conclude with `this`.

Establish `hb : D.φ (c * D.t ^ (a + 1) * w') = c * D.t ^ (a + 1) * w'`. Rewrite using `[P.PD_φ, map_mul, map_mul, map_pow, hφ, ht, mul_pow]`. Rewrite `h3` using `[map_mul, map_pow]`. Take the linear combination `(c * D.t ^ (a + 1)) * h3`. Establish `ht0 : D.ι D.t ∈ D.Fil 0` using `D.Fil_anti 0 D.mem_filtration_one`.

Establish `htp : ∀ n : ℕ, D.ι (D.t ^ n) ∈ D.Fil 0`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, map_one]`. Conclude with `D.one_mem`.

Consider the case `succ n ih => rw [pow_succ, map_mul]`. Conclude with `D.Fil_mul 0 0 _ _ ih ht0`. Establish `hF1 : D.ι (c * D.t ^ (a + 1) * w') ∈ D.Fil 1`. Rewrite using `[map_mul, map_mul, pow_succ, map_mul]`. Establish `e1 : D.ι c ∈ D.Fil 0` using `by rw [P.PD_ι]; exact hF`.

Establish `e2 : D.ι w' ∈ D.Fil 0` using `by rw [P.PD_ι]; exact hN' 0 0`. Conclude with `D.Fil_mul 1 0 _ _ (D.Fil_mul 0 1 _ _ e1 (D.Fil_mul 0 1 _ _ (htp a) D.mem_filtration_one)) e2`. Take `⟨r, hr⟩` from `D.fund _ hb (D.Fil_anti 0 hF1)`. Establish `hr0 : r ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hr` using `[map_zero]`. Establish `hw : IsUnit w'` using `IsUnit.of_mul_eq_one w (by rw [mul_comm]; exact h1)`. Rewrite `hr` using `[eq_comm, hw.mul_left_eq_zero, (D.t_unit.pow _).mul_left_eq_zero]`. Conclude with `hc hr`. Establish `hone : (1 : P.R.BdR) ∈ D.Fil 1`.

Rewrite `hF1` using `[← hr, P.PD_ι, AlgHom.commutes]`. Use `(D.Fil 1).smul_mem (algebraMap ℚ_[l] ↥(botExt l).1 r⁻¹) hF1` as an intermediate fact. Rewrite `this` using `[algebraMap_smul, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hr0, map_one]`. Then use the resulting hypothesis. Use `D.Fil_mul 1 1 _ _ D.mem_filtration_one hone` as an intermediate fact. Rewrite `this` using `[mul_one]`.

Conclude with `D.not_mem_filtration_two this`.
-/
theorem UpperTheory.norm_le_one_of_frobenius_eigenvector_mem_fil_zero :
    ∀ {l : ℕ} [Fact l.Prime] (c : Bcr l) (δ : ℚ_[l]), c ≠ 0 → (PP l).φB c = algebraMap ℚ_[l] (Bcr l) δ * c → (PP l).ιB c ∈ ((PP l).PD (botExt l)).Fil 0 → ‖δ‖ ≤ 1 := by
  intro l _ c δ hc hφ hF
  by_contra hδ
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    simp at hδ
  have hv : δ.valuation < 0 := by
    by_contra h
    exact hδ ((Padic.norm_le_one_iff_val_nonneg δ).2 (not_lt.1 h))
  obtain ⟨a, ha⟩ : ∃ a : ℕ, ((a + 1 : ℕ) : ℤ) = -δ.valuation := ⟨(-δ.valuation - 1).toNat, by push_cast; omega⟩
  have hl : (l : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hu : ‖δ * (l : ℚ_[l]) ^ (a + 1)‖ = 1 := by
    rw [norm_mul, Padic.norm_p_pow, Padic.norm_eq_zpow_neg_valuation hδ0, ← zpow_add₀ hl, ha]
    simp
  let u : ℤ_[l] := ⟨δ * (l : ℚ_[l]) ^ (a + 1), hu.le⟩
  have huu : IsUnit u := PadicInt.isUnit_iff.2 hu
  obtain ⟨N, N', hNN, hN, hN', hφN, -⟩ := UpperTheory.exists_algebraic_element_of_algebraicVectorSubspace (l := l) (n := 1) (Matrix.of fun _ _ => u)
    (by rw [Matrix.det_fin_one]; exact huu)
  set P := PP l with hP
  set D := P.PD (botExt l) with hD
  have h1 : N 0 0 * N' 0 0 = 1 := by
    have := congrFun (congrFun hNN 0) 0
    simpa [Matrix.mul_apply] using this
  have h2 : P.φB (N 0 0) = algebraMap ℚ_[l] (Bcr l) (δ * (l : ℚ_[l]) ^ (a + 1)) * N 0 0 := by
    have := congrFun (congrFun hφN 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_one] at this
    exact this
  set w := N 0 0
  set w' := N' 0 0 with hw'
  have h3 : algebraMap ℚ_[l] (Bcr l) (δ * (l : ℚ_[l]) ^ (a + 1)) * P.φB w' = w' := by
    have h := congrArg P.φB h1
    rw [map_mul, map_one, h2] at h
    linear_combination w' * h - (algebraMap ℚ_[l] (Bcr l) (δ * (l : ℚ_[l]) ^ (a + 1)) * P.φB w') * h1
  have ht : P.φB D.t = algebraMap ℚ_[l] (Bcr l) (l : ℚ_[l]) * D.t := by
    have := D.t_φ
    rw [P.PD_φ, P.PD_p, Algebra.smul_def] at this
    exact this
  have hb : D.φ (c * D.t ^ (a + 1) * w') = c * D.t ^ (a + 1) * w' := by
    rw [P.PD_φ, map_mul, map_mul, map_pow, hφ, ht, mul_pow]
    rw [map_mul, map_pow] at h3
    linear_combination (c * D.t ^ (a + 1)) * h3
  have ht0 : D.ι D.t ∈ D.Fil 0 := D.Fil_anti 0 D.mem_filtration_one
  have htp : ∀ n : ℕ, D.ι (D.t ^ n) ∈ D.Fil 0 := by
    intro n
    induction n with
    | zero => rw [pow_zero, map_one]; exact D.one_mem
    | succ n ih => rw [pow_succ, map_mul]; exact D.Fil_mul 0 0 _ _ ih ht0
  have hF1 : D.ι (c * D.t ^ (a + 1) * w') ∈ D.Fil 1 := by
    rw [map_mul, map_mul, pow_succ, map_mul]
    have e1 : D.ι c ∈ D.Fil 0 := by rw [P.PD_ι]; exact hF
    have e2 : D.ι w' ∈ D.Fil 0 := by rw [P.PD_ι]; exact hN' 0 0
    exact D.Fil_mul 1 0 _ _ (D.Fil_mul 0 1 _ _ e1 (D.Fil_mul 0 1 _ _ (htp a) D.mem_filtration_one)) e2
  obtain ⟨r, hr⟩ := D.fund _ hb (D.Fil_anti 0 hF1)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [map_zero] at hr
    have hw : IsUnit w' := IsUnit.of_mul_eq_one w (by rw [mul_comm]; exact h1)
    rw [eq_comm, hw.mul_left_eq_zero, (D.t_unit.pow _).mul_left_eq_zero] at hr
    exact hc hr
  have hone : (1 : P.R.BdR) ∈ D.Fil 1 := by
    rw [← hr, P.PD_ι, AlgHom.commutes] at hF1
    have := (D.Fil 1).smul_mem (algebraMap ℚ_[l] ↥(botExt l).1 r⁻¹) hF1
    rwa [algebraMap_smul, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hr0, map_one] at this
  have := D.Fil_mul 1 1 _ _ D.mem_filtration_one hone
  rw [mul_one] at this
  exact D.not_mem_filtration_two this
