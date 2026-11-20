import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SqrtOneAdd

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Use `haveI : IsAdicComplete (maximalIdeal C) C := IsCO.complete (O := O)`. Take `⟨b, rfl⟩` from `IsLocalRing.residue_surjective z`. Use `set ζ₀ := algebraMap O C b`. Establish `hr : res O C ζ₀ = residue O b` using `(res O C).commutes b`. Establish `hu : IsUnit ζ₀`.

Assume the negation of the conclusion as `hc`. Conclude with `hz (hr ▸ (res_eq_zero_iff O C ζ₀).2 ((IsLocalRing.mem_maximalIdeal _).2 hc))`. Use `set u := hu.unit`. Establish `hinv : res O C (↑u⁻¹ : C) * residue O b = 1`. Rewrite using `[← hr, ← map_mul]`.

Establish `: (↑u⁻¹ : C) * ζ₀ = 1`. Use `u.inv_mul` as an intermediate fact. Simplify `this` using `[u]`. Rewrite using `[this, map_one]`. Take `⟨α, hα, hα1⟩` from `UpperTheory.V.AlgebraTools.sqrt_one_add (maximalIdeal C) (a * (↑u⁻¹ : C) ^ 2) h2 (by`.

Rewrite using `[← res_eq_zero_iff O, map_sub, map_mul, map_pow, ha, map_one]`. Take the linear combination `(residue O b * res O C (↑u⁻¹ : C) + 1) * hinv)`. Use `⟨ζ₀ * α, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : res O C (α : C) = 1`. Use `(res_eq_zero_iff O C _).2 hα1` as an intermediate fact.

Rewrite `this` using `[map_sub, map_one, sub_eq_zero]`. Conclude with `this`. Rewrite using `[map_mul, hr, h1, mul_one]`. Establish `hz0 : ζ₀ * (↑u⁻¹ : C) = 1`. Use `u.mul_inv` as an intermediate fact.

Simplify `this` using `[u]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem co_sqrt {O C : Type} [CommRing O] [IsLocalRing O] [CommRing C] [Algebra O C] [IsCO O C]
    (h2 : IsUnit (2 : C)) (a : C) (z : ResidueField O) (hz : z ≠ 0) (ha : res O C a = z ^ 2) :
    ∃ ζ : C, res O C ζ = z ∧ ζ ^ 2 = a := by
  haveI : IsAdicComplete (maximalIdeal C) C := IsCO.complete (O := O)
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective z
  set ζ₀ := algebraMap O C b
  have hr : res O C ζ₀ = residue O b := (res O C).commutes b
  have hu : IsUnit ζ₀ := by
    by_contra hc
    exact hz (hr ▸ (res_eq_zero_iff O C ζ₀).2 ((IsLocalRing.mem_maximalIdeal _).2 hc))
  set u := hu.unit
  have hinv : res O C (↑u⁻¹ : C) * residue O b = 1 := by
    rw [← hr, ← map_mul]
    have : (↑u⁻¹ : C) * ζ₀ = 1 := by
      have := u.inv_mul
      simpa [u] using this
    rw [this, map_one]
  obtain ⟨α, hα, hα1⟩ := UpperTheory.V.AlgebraTools.sqrt_one_add (maximalIdeal C) (a * (↑u⁻¹ : C) ^ 2) h2 (by
    rw [← res_eq_zero_iff O, map_sub, map_mul, map_pow, ha, map_one]
    linear_combination (residue O b * res O C (↑u⁻¹ : C) + 1) * hinv)
  refine ⟨ζ₀ * α, ?_, ?_⟩
  · have h1 : res O C (α : C) = 1 := by
      have := (res_eq_zero_iff O C _).2 hα1
      rw [map_sub, map_one, sub_eq_zero] at this
      exact this
    rw [map_mul, hr, h1, mul_one]
  · have hz0 : ζ₀ * (↑u⁻¹ : C) = 1 := by
      have := u.mul_inv
      simpa [u] using this
    calc (ζ₀ * α) ^ 2 = ζ₀ ^ 2 * (α : C) ^ 2 := by ring
      _ = ζ₀ ^ 2 * (a * (↑u⁻¹ : C) ^ 2) := by rw [hα]
      _ = a * (ζ₀ * (↑u⁻¹ : C)) ^ 2 := by ring
      _ = a := by rw [hz0, one_pow, mul_one]

/- English proof (translation)
Establish `hQ' : IsUnit Q.det` using `(Matrix.isUnit_iff_isUnit_det Q).1 hQ`. Establish `htr : D.trace = 0`. Establish `e : Dᵀ = -(Q * D) * Q⁻¹`. Rewrite using `[← hD, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQ', Matrix.mul_one]`. Establish `h : Dᵀ.trace = - D.trace`.

Rewrite using `[e, Matrix.neg_mul, Matrix.trace_neg, Matrix.trace_mul_cycle, Matrix.nonsing_inv_mul _ hQ', Matrix.one_mul]`. Rewrite `h` using `[Matrix.trace_transpose]`. Establish `: 2 * D.trace = 0` using `by linear_combination h`. Conclude with `(mul_eq_zero.1 this).resolve_left h2`. It suffices to establish `hdet : (((w n i : K) * ζ) • (1 : Matrix (Fin n) (Fin n) K) - D).det = 0 by`.

Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 hdet`. Use `⟨v, hv0, ?_⟩` and prove the remaining obligations. Rewrite `hv` using `[Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]`. Conclude with `hv.symm`. Break down `hn with rfl | rfl` into its components or cases.

Establish `hf : ∀ (M : Matrix (Fin 2) (Fin 2) K) (x : K), 2 * (x • (1 : Matrix (Fin 2) (Fin 2) K) - M).det = 2 * x ^ 2 - 2 * M.trace * x + M.trace ^ 2 - (M * M).trace`. Introduce `M x`. Simplify using `[Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]`. Expand and normalize the polynomial expressions, which then agree. Establish `h` using `hf D ((w 2 i : K) * ζ)`.

Rewrite `h` using `[htr, ht]`. Apply the tactic sequence `have hw : (w 2 i : K) ^ 2 = 1 := by fin_cases i <;> norm_num [UpperTheory.V.Fr.w]`. Establish `: 2 * (((w 2 i : K) * ζ) • (1 : Matrix (Fin 2) (Fin 2) K) - D).det = 0`. Rewrite using `[h]`. Take the linear combination `(2 * ζ ^ 2) * hw`.

Conclude with `(mul_eq_zero.1 this).resolve_left h2`. Establish `hf : ∀ (M : Matrix (Fin 3) (Fin 3) K) (x : K), 2 * (x • (1 : Matrix (Fin 3) (Fin 3) K) - M).det = 2 * x ^ 3 - 2 * M.trace * x ^ 2 + (M.trace ^ 2 - (M * M).trace) * x - 2 * M.det`. Introduce `M x`. Simplify using `[Matrix.det_fin_three, Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hdD : D.det = 0`. Establish `h` using `congrArg Matrix.det hD`. Rewrite `h` using `[Matrix.det_mul, Matrix.det_transpose, Matrix.det_neg, Matrix.det_mul]`. Simplify using `at h`. Establish `: 2 * (D.det * Q.det) = 0` using `by linear_combination h`.

Break down `mul_eq_zero.1 this with h' | h'` into its components or cases. Conclude with `absurd h' h2`. Conclude with `(mul_eq_zero.1 h').resolve_right hQ'.ne_zero`. Establish `h` using `hf D ((w 3 i : K) * ζ)`. Rewrite `h` using `[htr, ht, hdD]`.

Apply the tactic sequence `have hw : (w 3 i : K) ^ 3 = (w 3 i : K) := by fin_cases i <;> norm_num [UpperTheory.V.Fr.w]`. Establish `: 2 * (((w 3 i : K) * ζ) • (1 : Matrix (Fin 3) (Fin 3) K) - D).det = 0`. Rewrite using `[h]`. Take the linear combination `(2 * ζ ^ 3) * hw`. Conclude with `(mul_eq_zero.1 this).resolve_left h2`.
-/
private theorem skew_eig {K : Type} [Field K] {n : ℕ} (hn : n = 2 ∨ n = 3) (h2 : (2 : K) ≠ 0)
    (Q D : Matrix (Fin n) (Fin n) K) (ζ : K) (hQ : IsUnit Q) (hD : Dᵀ * Q = -(Q * D))
    (ht : (D * D).trace = 2 * ζ ^ 2) (i : Fin n) : ∃ v : Fin n → K, v ≠ 0 ∧ D *ᵥ v = ((w n i : K) * ζ) • v := by
  have hQ' : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ
  have htr : D.trace = 0 := by
    have e : Dᵀ = -(Q * D) * Q⁻¹ := by
      rw [← hD, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQ', Matrix.mul_one]
    have h : Dᵀ.trace = - D.trace := by
      rw [e, Matrix.neg_mul, Matrix.trace_neg, Matrix.trace_mul_cycle, Matrix.nonsing_inv_mul _ hQ', Matrix.one_mul]
    rw [Matrix.trace_transpose] at h
    have : 2 * D.trace = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_left h2
  suffices hdet : (((w n i : K) * ζ) • (1 : Matrix (Fin n) (Fin n) K) - D).det = 0 by
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    refine ⟨v, hv0, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
    exact hv.symm
  rcases hn with rfl | rfl
  · have hf : ∀ (M : Matrix (Fin 2) (Fin 2) K) (x : K),
        2 * (x • (1 : Matrix (Fin 2) (Fin 2) K) - M).det = 2 * x ^ 2 - 2 * M.trace * x + M.trace ^ 2 - (M * M).trace := by
      intro M x
      simp [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    have h := hf D ((w 2 i : K) * ζ)
    rw [htr, ht] at h
    have hw : (w 2 i : K) ^ 2 = 1 := by
      fin_cases i <;> norm_num [UpperTheory.V.Fr.w]
    have : 2 * (((w 2 i : K) * ζ) • (1 : Matrix (Fin 2) (Fin 2) K) - D).det = 0 := by
      rw [h]
      linear_combination (2 * ζ ^ 2) * hw
    exact (mul_eq_zero.1 this).resolve_left h2
  · have hf : ∀ (M : Matrix (Fin 3) (Fin 3) K) (x : K),
        2 * (x • (1 : Matrix (Fin 3) (Fin 3) K) - M).det = 2 * x ^ 3 - 2 * M.trace * x ^ 2 + (M.trace ^ 2 - (M * M).trace) * x - 2 * M.det := by
      intro M x
      simp [Matrix.det_fin_three, Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three]
      ring
    have hdD : D.det = 0 := by
      have h := congrArg Matrix.det hD
      rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_neg, Matrix.det_mul] at h
      simp at h
      have : 2 * (D.det * Q.det) = 0 := by linear_combination h
      rcases mul_eq_zero.1 this with h' | h'
      · exact absurd h' h2
      · exact (mul_eq_zero.1 h').resolve_right hQ'.ne_zero
    have h := hf D ((w 3 i : K) * ζ)
    rw [htr, ht, hdD] at h
    have hw : (w 3 i : K) ^ 3 = (w 3 i : K) := by
      fin_cases i <;> norm_num [UpperTheory.V.Fr.w]
    have : 2 * (((w 3 i : K) * ζ) • (1 : Matrix (Fin 3) (Fin 3) K) - D).det = 0 := by
      rw [h]
      linear_combination (2 * ζ ^ 3) * hw
    exact (mul_eq_zero.1 this).resolve_left h2

/- English proof (translation)
Establish `h2ζ : (2 : K) * ζ ≠ 0` using `mul_ne_zero h2 hζ`. Establish `hμinj : Function.Injective (fun i : Fin n => (w n i : K) * ζ)`. Introduce `i j h`. Simplify using `only at h`. Apply the tactic sequence `rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases j <;> simp [w] at h ⊢ <;> first`.

Consider the case `exact hζ h`. Consider the case `exact hζ h.symm`. Consider the case `exact h2ζ (by linear_combination h)`. Consider the case `exact h2ζ (by linear_combination -h)`. Establish `hμsum : ∀ i j : Fin n, (w n i : K) * ζ + (w n j : K) * ζ = 0 → j = i.rev`.

Introduce `i j h`. Apply the tactic sequence `rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases j <;> simp [w] at h ⊢ <;> first`. Consider the case `exact hζ h`. Consider the case `exact hζ h.symm`. Consider the case `exact h2ζ (by linear_combination h)`.

Consider the case `exact h2ζ (by linear_combination -h)`. Use `choose v hv0 hv using hv`. Use `set μ : Fin n → K := fun i => (w n i : K) * ζ with hμ`. Use `set V : Matrix (Fin n) (Fin n) K := Matrix.of fun a i => v i a with hVdef`. Establish `hV : IsUnit V`.

Rewrite using `[← Matrix.linearIndependent_cols_iff_isUnit]`. Establish `: V.col = v`. Use function extensionality and compare the values at `i a`. Both sides reduce to the same expression. Rewrite using `[this]`.

Use `Module.End.eigenvectors_linearIndependent' (Matrix.toLin' D) μ hμinj v fun i => ?_` and prove the remaining obligations. Use `⟨?_, hv0 i⟩` and prove the remaining obligations. Rewrite using `[Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]`. Conclude with `hv i`. Establish `hDV : D * V = V * Matrix.diagonal μ`.

Use extensionality with `a i`. Use `congrFun (hv i) a` as an intermediate fact. Simplify using `only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this`. Rewrite using `[Matrix.mul_diagonal, Matrix.mul_apply]`. Simplify using `only [hVdef, Matrix.of_apply]`.

Rewrite using `[this, hμ, mul_comm]`. Use `set M := Vᵀ * Q * V with hMdef`. Establish `hMsym : ∀ i j, M j i = M i j`. Introduce `i j`. Establish `: Mᵀ = M`.

Rewrite using `[hMdef, Matrix.transpose_mul, Matrix.transpose_mul, hs, Matrix.transpose_transpose, Matrix.mul_assoc]`. Rewrite using `[← Matrix.transpose_apply M i j, this]`. Establish `hMu : IsUnit M` using `((Matrix.isUnit_transpose V).2 hV |>.mul hQ).mul hV`. Establish `hcomm : Matrix.diagonal μ * M = -(M * Matrix.diagonal μ)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.transpose_mul, Matrix.diagonal_transpose, hMdef, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]`. Use `_ = Vᵀ * (Dᵀ * Q) * V := by`. Rewrite using `[← hDV, Matrix.transpose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = -(M * Matrix.diagonal μ) := by`.

Rewrite using `[hD, Matrix.mul_neg, Matrix.neg_mul, hMdef, Matrix.mul_assoc, Matrix.mul_assoc, hDV, Matrix.mul_assoc, Matrix.mul_assoc]`. Establish `hM0 : ∀ i j, j ≠ i.rev → M i j = 0`. Introduce `i j hij`. Use `congrFun (congrFun hcomm i) j` as an intermediate fact. Simplify using `only [Matrix.diagonal_mul, Matrix.neg_apply, Matrix.mul_diagonal] at this`.

Establish `h' : (μ i + μ j) * M i j = 0` using `by linear_combination this`. Break down `mul_eq_zero.1 h' with h | h` into its components or cases. Conclude with `absurd (hμsum i j h) hij`. Conclude with `h`. Establish `hMr : ∀ i, M i i.rev ≠ 0`.

Introduce `i h`. Establish `hdet : M.det = 0` using `Matrix.det_eq_zero_of_row_eq_zero i fun j => by`. Distinguish the cases in `hj : j = i.rev`. Rewrite using `[hj]`. Conclude with `h`.

Conclude with `hM0 i j hj`. Conclude with `((Matrix.isUnit_iff_isUnit_det M).1 hMu).ne_zero hdet`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc0, hc⟩ : ∃ c : Fin n → K, (∀ i, c i ≠ 0) ∧ ∀ i, c i * c i.rev * M i i.rev = 1 := by`. Break down `hn with rfl | rfl` into its components or cases. Establish `hm : M 0 1 ≠ 0` using `by simpa using hMr 0`.

Establish `hm' : M 1 0 = M 0 1` using `hMsym 0 1`. Use `⟨![1, (M 0 1)⁻¹], ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `intro i fin_cases i <;> simp [hm]`. Apply the tactic sequence `intro i fin_cases i <;> simp [hm'] <;> field_simp`. Establish `hm : M 0 2 ≠ 0` using `by simpa using hMr 0`.

Establish `hm' : M 2 0 = M 0 2` using `hMsym 0 2`. Establish `hq : M 1 1 ≠ 0` using `by simpa using hMr 1`. Take `⟨z, hz⟩` from `IsAlgClosed.exists_eq_mul_self (M 1 1)⁻¹`. Establish `hz0 : z ≠ 0`. Introduce and unpack `rfl`.

Simplify using `[hq] at hz`. Use `⟨![1, z, (M 0 2)⁻¹], ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `intro i fin_cases i <;> simp [hm, hz0]`. Apply the tactic sequence `intro i fin_cases i <;> simp [hm'] <;> field_simp`. Rewrite using `[sq, ← hz, inv_mul_cancel₀ hq]`.

Use `⟨V * Matrix.diagonal c, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `hV.mul ((Matrix.isUnit_diagonal).2 (Pi.isUnit_iff.2 fun i => (hc0 i).isUnit))`. Use extensionality with `i j`. Rewrite using `[Matrix.transpose_mul, Matrix.diagonal_transpose]`. Establish `e : Matrix.diagonal c * Vᵀ * Q * (V * Matrix.diagonal c) = Matrix.diagonal c * M * Matrix.diagonal c`.

Rewrite using `[hMdef]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[e, Matrix.mul_diagonal, Matrix.diagonal_mul, Jmat]`. Use `split_ifs with hj`. Substitute `hj` using the available equality.

Take the linear combination `hc i`. Rewrite using `[hM0 i j hj]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← Matrix.mul_assoc, hDV, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]`. Use `congr 2`.

Use function extensionality and compare the values at `i`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem skew_norm {K : Type} [Field K] [IsAlgClosed K] {n : ℕ} (hn : n = 2 ∨ n = 3) (h2 : (2 : K) ≠ 0)
    (Q D : Matrix (Fin n) (Fin n) K) (ζ : K) (hζ : ζ ≠ 0) (hQ : IsUnit Q) (hs : Qᵀ = Q) (hD : Dᵀ * Q = -(Q * D))
    (hv : ∀ i : Fin n, ∃ v : Fin n → K, v ≠ 0 ∧ D *ᵥ v = ((w n i : K) * ζ) • v) :
    ∃ P : Matrix (Fin n) (Fin n) K, IsUnit P ∧ Pᵀ * Q * P = Jmat K n ∧
      D * P = P * Matrix.diagonal fun i => (w n i : K) * ζ := by
  have h2ζ : (2 : K) * ζ ≠ 0 := mul_ne_zero h2 hζ
  have hμinj : Function.Injective (fun i : Fin n => (w n i : K) * ζ) := by
    intro i j h
    simp only at h
    rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases j <;> simp [w] at h ⊢ <;>
      first
      | exact hζ h
      | exact hζ h.symm
      | exact h2ζ (by linear_combination h)
      | exact h2ζ (by linear_combination -h)
  have hμsum : ∀ i j : Fin n, (w n i : K) * ζ + (w n j : K) * ζ = 0 → j = i.rev := by
    intro i j h
    rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases j <;> simp [w] at h ⊢ <;>
      first
      | exact hζ h
      | exact hζ h.symm
      | exact h2ζ (by linear_combination h)
      | exact h2ζ (by linear_combination -h)
  choose v hv0 hv using hv
  set μ : Fin n → K := fun i => (w n i : K) * ζ with hμ
  set V : Matrix (Fin n) (Fin n) K := Matrix.of fun a i => v i a with hVdef
  have hV : IsUnit V := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    have : V.col = v := by
      funext i a
      rfl
    rw [this]
    refine Module.End.eigenvectors_linearIndependent' (Matrix.toLin' D) μ hμinj v fun i => ?_
    refine ⟨?_, hv0 i⟩
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact hv i
  have hDV : D * V = V * Matrix.diagonal μ := by
    ext a i
    have := congrFun (hv i) a
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [hVdef, Matrix.of_apply]
    rw [this, hμ, mul_comm]
  set M := Vᵀ * Q * V with hMdef
  have hMsym : ∀ i j, M j i = M i j := by
    intro i j
    have : Mᵀ = M := by
      rw [hMdef, Matrix.transpose_mul, Matrix.transpose_mul, hs, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.transpose_apply M i j, this]
  have hMu : IsUnit M := ((Matrix.isUnit_transpose V).2 hV |>.mul hQ).mul hV
  have hcomm : Matrix.diagonal μ * M = -(M * Matrix.diagonal μ) := by
    calc Matrix.diagonal μ * M = (V * Matrix.diagonal μ)ᵀ * Q * V := by
          rw [Matrix.transpose_mul, Matrix.diagonal_transpose, hMdef, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = Vᵀ * (Dᵀ * Q) * V := by
          rw [← hDV, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = -(M * Matrix.diagonal μ) := by
          rw [hD, Matrix.mul_neg, Matrix.neg_mul, hMdef, Matrix.mul_assoc, Matrix.mul_assoc, hDV, Matrix.mul_assoc, Matrix.mul_assoc]
  have hM0 : ∀ i j, j ≠ i.rev → M i j = 0 := by
    intro i j hij
    have := congrFun (congrFun hcomm i) j
    simp only [Matrix.diagonal_mul, Matrix.neg_apply, Matrix.mul_diagonal] at this
    have h' : (μ i + μ j) * M i j = 0 := by linear_combination this
    rcases mul_eq_zero.1 h' with h | h
    · exact absurd (hμsum i j h) hij
    · exact h
  have hMr : ∀ i, M i i.rev ≠ 0 := by
    intro i h
    have hdet : M.det = 0 := Matrix.det_eq_zero_of_row_eq_zero i fun j => by
      by_cases hj : j = i.rev
      · rw [hj]
        exact h
      · exact hM0 i j hj
    exact ((Matrix.isUnit_iff_isUnit_det M).1 hMu).ne_zero hdet
  obtain ⟨c, hc0, hc⟩ : ∃ c : Fin n → K, (∀ i, c i ≠ 0) ∧ ∀ i, c i * c i.rev * M i i.rev = 1 := by
    rcases hn with rfl | rfl
    · have hm : M 0 1 ≠ 0 := by simpa using hMr 0
      have hm' : M 1 0 = M 0 1 := hMsym 0 1
      refine ⟨![1, (M 0 1)⁻¹], ?_, ?_⟩
      · intro i
        fin_cases i <;> simp [hm]
      · intro i
        fin_cases i <;> simp [hm'] <;> field_simp
    · have hm : M 0 2 ≠ 0 := by simpa using hMr 0
      have hm' : M 2 0 = M 0 2 := hMsym 0 2
      have hq : M 1 1 ≠ 0 := by simpa using hMr 1
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_eq_mul_self (M 1 1)⁻¹
      have hz0 : z ≠ 0 := by
        rintro rfl
        simp [hq] at hz
      refine ⟨![1, z, (M 0 2)⁻¹], ?_, ?_⟩
      · intro i
        fin_cases i <;> simp [hm, hz0]
      · intro i
        fin_cases i <;> simp [hm'] <;> field_simp
        rw [sq, ← hz, inv_mul_cancel₀ hq]
  refine ⟨V * Matrix.diagonal c, ?_, ?_, ?_⟩
  · exact hV.mul ((Matrix.isUnit_diagonal).2 (Pi.isUnit_iff.2 fun i => (hc0 i).isUnit))
  · ext i j
    rw [Matrix.transpose_mul, Matrix.diagonal_transpose]
    have e : Matrix.diagonal c * Vᵀ * Q * (V * Matrix.diagonal c) = Matrix.diagonal c * M * Matrix.diagonal c := by
      rw [hMdef]
      simp only [Matrix.mul_assoc]
    rw [e, Matrix.mul_diagonal, Matrix.diagonal_mul, Jmat]
    split_ifs with hj
    · subst hj
      linear_combination hc i
    · rw [hM0 i j hj]
      ring
  · rw [← Matrix.mul_assoc, hDV, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 2
    funext i
    ring

/- English proof (translation)
Use `set φ := MulSemiringAction.toRingHom _ (Matrix (Fin n) (Fin n) K) (ConjAct.toConjAct P)`. Establish `hs : ∀ (c : K), φ (c • (1 : Matrix (Fin n) (Fin n) K)) = c • 1`. Introduce `c`. Simplify using `only [φ, MulSemiringAction.toRingHom_apply, ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct, mul_smul_comm, smul_mul_assoc, mul_one, Units.mul_inv]`. Establish `: ordProd (fun s => φ (r s)) ψ g = φ (ordProd r ψ g)`.

Unfold `ordProd`. Rewrite using `[map_list_prod, List.map_ofFn]`. Use `congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))` and prove the remaining obligations. Simplify using `[Function.comp, map_sub, hs]`. Rewrite using `[this, h, map_zero]`.
-/
private theorem ordProd_conj {H K : Type} [CommRing K] {n : ℕ} (P : (Matrix (Fin n) (Fin n) K)ˣ)
    (r : H → Matrix (Fin n) (Fin n) K) (ψ : Fin n → H → K) (g : Fin n → H) (h : ordProd r ψ g = 0) :
    ordProd (fun s => (MulSemiringAction.toRingHom _ _ (ConjAct.toConjAct P)) (r s)) ψ g = 0 := by
  set φ := MulSemiringAction.toRingHom _ (Matrix (Fin n) (Fin n) K) (ConjAct.toConjAct P)
  have hs : ∀ (c : K), φ (c • (1 : Matrix (Fin n) (Fin n) K)) = c • 1 := by
    intro c
    simp only [φ, MulSemiringAction.toRingHom_apply, ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct,
      mul_smul_comm, smul_mul_assoc, mul_one, Units.mul_inv]
  have : ordProd (fun s => φ (r s)) ψ g = φ (ordProd r ψ g) := by
    unfold ordProd
    rw [map_list_prod, List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
    simp [Function.comp, map_sub, hs]
  rw [this, h, map_zero]

/- English proof (translation)
Introduce `l _ O _ _ _ _ F C₀ n hF hn C _ _ _ K _ _ _ hinj r Q t χ hQ hQs hform htr ht hpsi hord`. Establish `hQi : Q * Q⁻¹ = 1` using `Matrix.mul_nonsing_inv Q ((Matrix.isUnit_iff_isUnit_det Q).1 hQ)`. Establish `hiQ : Q⁻¹ * Q = 1` using `Matrix.nonsing_inv_mul Q ((Matrix.isUnit_iff_isUnit_det Q).1 hQ)`. Establish `hst : ∀ g : F.G0, Q * r (F.star g) = (r g)ᵀ * Q`. Introduce `g`.

Establish `h1` using `hform g⁻¹`. Establish `h2 : (r g)ᵀ * (r g⁻¹)ᵀ = 1`. Rewrite using `[← Matrix.transpose_mul, ← map_mul, inv_mul_cancel, map_one, Matrix.transpose_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]`.

Both sides reduce to the same expression. Use `_ = (r g)ᵀ * Q := by rw [h1]`. Establish `hS` using `UpperTheory.V.Fr.star hF`. Establish `htrs : ∀ g : F.G0, (r (F.star g)).trace = (r g).trace`. Introduce `g`.

Establish `: r (F.star g) = Q⁻¹ * ((r g)ᵀ * Q)`. Rewrite using `[← hst g, ← Matrix.mul_assoc, hiQ, Matrix.one_mul]`. Rewrite using `[this, Matrix.trace_mul_comm, Matrix.mul_assoc, hQi, Matrix.mul_one, Matrix.trace_transpose]`. Use `set A := r F.g0 with hA`. Use `set B := r (F.star F.g0) with hB`.

Use `set D := A - B with hDdef`. Establish `hBt : Bᵀ * Q = Q * A`. Use `hst (F.star F.g0)` as an intermediate fact. Rewrite `this` using `[hS.1]`. Conclude with `this.symm`.

Establish `hskew : Dᵀ * Q = -(Q * D)`. Rewrite using `[hDdef, Matrix.transpose_sub, Matrix.sub_mul, hBt, Matrix.mul_sub, ← hst F.g0]`. Normalize the expressions using the abelian group laws. Establish `hDD : (D * D).trace = 2 * ((r (F.g0 * F.g0)).trace - (r (F.g0 * F.star F.g0)).trace)`. Establish `e1 : (B * B).trace = (A * A).trace`.

Rewrite using `[hB, ← map_mul, ← hS.2.1, htrs, map_mul]`. Establish `e2 : (B * A).trace = (A * B).trace` using `Matrix.trace_mul_comm _ _`. Rewrite using `[map_mul, map_mul, ← hA, ← hB, hDdef]`. Simplify using `only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, e1, e2]`. Expand and normalize the polynomial expressions, which then agree.

Use `set a : (ResidueField O)ˣ := F.Ψ (F.g0 : F.Γ) with ha`. Use `set z : ResidueField O := (a : ResidueField O) - ((a⁻¹ : (ResidueField O)ˣ) : ResidueField O) with hz`. Establish `hab : (a : ResidueField O) * ((a⁻¹ : (ResidueField O)ˣ) : ResidueField O) = 1` using `Units.mul_inv a`. Establish `hz0 : z ≠ 0`. Introduce `h0`.

Apply `hF.baseSubgroup_spec` to reduce the goal to its premises. Rewrite using `[← ha, sq]`. Apply `Units.val_injective` to reduce the goal to its premises. Rewrite using `[Units.val_mul, Units.val_one]`. Establish `: (a : ResidueField O) = ((a⁻¹ : (ResidueField O)ˣ) : ResidueField O)` using `sub_eq_zero.1 h0`.

Use `nth_rewrite 2 [this]`. Conclude with `hab`. Establish `hP1 : F.Ψ ((F.g0 * F.g0 : F.G0) : F.Γ) = a * a`. Rewrite using `[Subgroup.coe_mul, map_mul]`. Establish `hP2 : F.Ψ ((F.g0 * F.star F.g0 : F.G0) : F.Γ) = 1`.

Rewrite using `[Subgroup.coe_mul, map_mul, hS.2.2.1, mul_inv_cancel]`. Use `set X : C := t (F.g0 * F.g0) - t (F.g0 * F.star F.g0) with hX`. Establish `hresX : res O C X = z ^ 2`. Establish `hb : (a : ResidueField O) ≠ 0` using `a.ne_zero`. Rewrite using `[hX, map_sub, htr.2, htr.2, hP1, hP2, hz, Units.val_inv_eq_inv_val]`.

Break down `hn with rfl | rfl` into its components or cases. Simplify using `[Fin.sum_univ_two, UpperTheory.V.Fr.w, Units.val_inv_eq_inv_val]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Simplify using `[Fin.sum_univ_three, UpperTheory.V.Fr.w, Units.val_inv_eq_inv_val]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hk2 : (2 : ResidueField O) ≠ 0` using `by haveI : CharP (ResidueField O) l := IsCoef.char`. Introduce `h0`. Establish `h2 : (l : ℕ) ∣ 2` using `(CharP.cast_eq_zero_iff (ResidueField O) l 2).1 (by exact_mod_cast h0)`.

Establish `hl : l.Prime` using `Fact.out`. Break down `(Nat.dvd_prime Nat.prime_two).1 h2 with h | h` into its components or cases. Conclude with `hl.one_lt.ne' h`. Conclude with `hF.l_odd h`. Establish `hC2 : IsUnit (2 : C)`.

Assume the negation of the conclusion as `hc`. Establish `hm : (2 : C) ∈ maximalIdeal C` using `(IsLocalRing.mem_maximalIdeal _).2 hc`. Rewrite `hm` using `[← res_eq_zero_iff O, map_ofNat]`. Conclude with `hk2 hm`. Take `⟨ζ, hζr, hζX⟩` from `co_sqrt hC2 X z hz0 hresX`.

Use `set ζK : K := algebraMap C K ζ with hζK`. Establish `hK2 : (2 : K) ≠ 0`. Use `hC2.map (algebraMap C K)` as an intermediate fact. Rewrite `this` using `[map_ofNat]`. Conclude with `this.ne_zero`.

Establish `hζ0 : ζK ≠ 0`. Introduce `h0`. Apply `hz0` to reduce the goal to its premises. Rewrite using `[← hζr, (map_eq_zero_iff _ hinj).1 h0, map_zero]`. Establish `htrK : (D * D).trace = 2 * ζK ^ 2`.

Rewrite using `[hDD, ← ht, ← ht, ← map_sub, ← hX, ← hζX, hζK, map_pow]`. Establish `hv` using `skew_eig hn hK2 Q D ζK hQ hskew htrK`. Take `⟨P, hPu, hPQ, hDP⟩` from `skew_norm hn hK2 Q D ζK hζ0 hQ hQs hskew hv`. Take `⟨U, hU⟩` from `hPu`. Establish `hPi : (U : Matrix (Fin n) (Fin n) K) * ((U⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K) = 1` using `U.mul_inv`.

Establish `hiP : ((U⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K) * (U : Matrix (Fin n) (Fin n) K) = 1` using `U.inv_mul`. Substitute `hU` using the available equality. Use `set Pm : Matrix (Fin n) (Fin n) K := (U : Matrix (Fin n) (Fin n) K) with hPm`. Use `set Pi : Matrix (Fin n) (Fin n) K := ((U⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K) with hPim`. Establish `hconj : ∀ M : Matrix (Fin n) (Fin n) K, (MulSemiringAction.toRingHom _ _ (ConjAct.toConjAct U⁻¹)) M = Pi * M * Pm`.

Introduce `M`. Simplify using `[MulSemiringAction.toRingHom_apply, ConjAct.units_smul_def, hPim, hPm]`. Establish `e1 : Q * Pm = Piᵀ * Jmat K n`. Rewrite using `[← hPQ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul, hPi, Matrix.transpose_one, Matrix.one_mul]`. Establish `e2 : Pmᵀ * Q = Jmat K n * Pi`.

Rewrite using `[← hPQ, Matrix.mul_assoc (Pmᵀ * Q), hPi, Matrix.mul_one]`. Set `ρr : F.G0 →* Matrix (Fin n) (Fin n) K` to `((MulSemiringAction.toRingHom _ _ (ConjAct.toConjAct U⁻¹) : Matrix (Fin n) (Fin n) K →+* Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K →* Matrix (Fin n) (Fin n) K).comp r`. Establish `hρ : ∀ g, ρr g = Pi * r g * Pm` using `fun g => hconj (r g)`. Establish `hpol : ∀ g, ρr (F.star g) = Jmat K n * (ρr g)ᵀ * Jmat K n`. Introduce `g`.

Rewrite using `[hρ, hρ, Matrix.transpose_mul, Matrix.transpose_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Jmat_mul_Jmat, Matrix.one_mul]`. Use `_ = Jmat K n * (Pmᵀ * Q) * r (F.star g) * Pm := by`. Rewrite using `[e2]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = Jmat K n * Pmᵀ * ((r g)ᵀ * Q) * Pm := by`. Rewrite using `[← hst]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Jmat K n * Pmᵀ * (r g)ᵀ * (Q * Pm) := by`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = Jmat K n * (Pmᵀ * ((r g)ᵀ * Piᵀ)) * Jmat K n := by`. Rewrite using `[e1]`. Simplify using `only [Matrix.mul_assoc]`. Establish `hdm : Pi * r F.g0 * Pm - Pi * r (F.star F.g0) * Pm = Matrix.diagonal fun i => (w n i : K) * ζK`.

Rewrite using `[← Matrix.sub_mul, ← Matrix.mul_sub, ← hA, ← hB, ← hDdef, Matrix.mul_assoc, hDP, ← Matrix.mul_assoc, hiP, Matrix.one_mul]`. Use `⟨⟨ρr, fun v i => (Units.map (algebraMap C K : C →* K)).comp (χ v i), hpol, ?_, ?_⟩, U⁻¹, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j hij`. Rewrite using `[hρ, hρ, hdm, Matrix.diagonal_apply_ne _ hij]`. Introduce `v g`.

Conclude with `ordProd_conj U⁻¹ (fun s => r (F.loc0 v s)) (fun i s => algebraMap C K (χ v i s)) g (hord v g)`. Introduce `g`. Rewrite using `[inv_inv]`. Conclude with `hρ g`. Introduce `v i g`.

Both sides reduce to the same expression. Use `⟨⟨t, htr, fun g => ?_⟩, ⟨fun v i g => (χ v i g : C), hpsi, fun v i g => rfl⟩, ⟨ζ, hζr, fun i => ?_⟩⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap C K (t g) = (ρr g).trace`. Rewrite using `[ht, hρ, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hPi, Matrix.one_mul]`. Express the relevant statement in the definitionally equal form `(ρr F.g0 - ρr (F.star F.g0)) i i = _`.

Rewrite using `[hρ, hρ, hdm, Matrix.diagonal_apply_eq]`.
-/
theorem UpperTheory.V.Fr.of_form :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (K : Type) [Field K] [IsAlgClosed K] [Algebra C K], Function.Injective (algebraMap C K) → ∀ (r : F.G0 →* Matrix (Fin n) (Fin n) K) (Q : Matrix (Fin n) (Fin n) K) (t : F.G0 → C) (χ : ∀ v, Fin n → F.Gv v →* Cˣ), IsUnit Q → Qᵀ = Q → (∀ g, (r g)ᵀ * Q * r (F.conj g) = Q) → IsTr O F n t → (∀ g, algebraMap C K (t g) = (r g).trace) → IsPsi O F n (fun v i g => (χ v i g : C)) → (∀ v g, ordProd (fun s => r (F.loc0 v s)) (fun i s => algebraMap C K (χ v i s)) g = 0) → ∃ (ρ : NRep F n K) (h : GL (Fin n) K), (∀ g, ρ.r g = h * r g * h⁻¹) ∧ (∀ v i g, (ρ.ψ v i g : K) = algebraMap C K (χ v i g)) ∧ Integral O C ρ := by
  intro l _ O _ _ _ _ F C₀ n hF hn C _ _ _ K _ _ _ hinj r Q t χ hQ hQs hform htr ht hpsi hord
  have hQi : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q ((Matrix.isUnit_iff_isUnit_det Q).1 hQ)
  have hiQ : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q ((Matrix.isUnit_iff_isUnit_det Q).1 hQ)
  have hst : ∀ g : F.G0, Q * r (F.star g) = (r g)ᵀ * Q := by
    intro g
    have h1 := hform g⁻¹
    have h2 : (r g)ᵀ * (r g⁻¹)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← map_mul, inv_mul_cancel, map_one, Matrix.transpose_one]
    calc Q * r (F.star g) = (r g)ᵀ * ((r g⁻¹)ᵀ * Q * r (F.conj g⁻¹)) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]; rfl
      _ = (r g)ᵀ * Q := by rw [h1]
  have hS := UpperTheory.V.Fr.star hF
  have htrs : ∀ g : F.G0, (r (F.star g)).trace = (r g).trace := by
    intro g
    have : r (F.star g) = Q⁻¹ * ((r g)ᵀ * Q) := by
      rw [← hst g, ← Matrix.mul_assoc, hiQ, Matrix.one_mul]
    rw [this, Matrix.trace_mul_comm, Matrix.mul_assoc, hQi, Matrix.mul_one, Matrix.trace_transpose]
  set A := r F.g0 with hA
  set B := r (F.star F.g0) with hB
  set D := A - B with hDdef
  have hBt : Bᵀ * Q = Q * A := by
    have := hst (F.star F.g0)
    rw [hS.1] at this
    exact this.symm
  have hskew : Dᵀ * Q = -(Q * D) := by
    rw [hDdef, Matrix.transpose_sub, Matrix.sub_mul, hBt, Matrix.mul_sub, ← hst F.g0]
    abel
  have hDD : (D * D).trace = 2 * ((r (F.g0 * F.g0)).trace - (r (F.g0 * F.star F.g0)).trace) := by
    have e1 : (B * B).trace = (A * A).trace := by
      rw [hB, ← map_mul, ← hS.2.1, htrs, map_mul]
    have e2 : (B * A).trace = (A * B).trace := Matrix.trace_mul_comm _ _
    rw [map_mul, map_mul, ← hA, ← hB, hDdef]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, e1, e2]
    ring
  set a : (ResidueField O)ˣ := F.Ψ (F.g0 : F.Γ) with ha
  set z : ResidueField O := (a : ResidueField O) - ((a⁻¹ : (ResidueField O)ˣ) : ResidueField O) with hz
  have hab : (a : ResidueField O) * ((a⁻¹ : (ResidueField O)ˣ) : ResidueField O) = 1 := Units.mul_inv a
  have hz0 : z ≠ 0 := by
    intro h0
    apply hF.baseSubgroup_spec
    rw [← ha, sq]
    apply Units.val_injective
    rw [Units.val_mul, Units.val_one]
    have : (a : ResidueField O) = ((a⁻¹ : (ResidueField O)ˣ) : ResidueField O) := sub_eq_zero.1 h0
    nth_rewrite 2 [this]
    exact hab
  have hP1 : F.Ψ ((F.g0 * F.g0 : F.G0) : F.Γ) = a * a := by
    rw [Subgroup.coe_mul, map_mul]
  have hP2 : F.Ψ ((F.g0 * F.star F.g0 : F.G0) : F.Γ) = 1 := by
    rw [Subgroup.coe_mul, map_mul, hS.2.2.1, mul_inv_cancel]
  set X : C := t (F.g0 * F.g0) - t (F.g0 * F.star F.g0) with hX
  have hresX : res O C X = z ^ 2 := by
    have hb : (a : ResidueField O) ≠ 0 := a.ne_zero
    rw [hX, map_sub, htr.2, htr.2, hP1, hP2, hz, Units.val_inv_eq_inv_val]
    rcases hn with rfl | rfl
    · simp [Fin.sum_univ_two, UpperTheory.V.Fr.w, Units.val_inv_eq_inv_val]
      field_simp
      ring
    · simp [Fin.sum_univ_three, UpperTheory.V.Fr.w, Units.val_inv_eq_inv_val]
      field_simp
      ring
  have hk2 : (2 : ResidueField O) ≠ 0 := by
    haveI : CharP (ResidueField O) l := IsCoef.char
    intro h0
    have h2 : (l : ℕ) ∣ 2 := (CharP.cast_eq_zero_iff (ResidueField O) l 2).1 (by exact_mod_cast h0)
    have hl : l.Prime := Fact.out
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · exact hl.one_lt.ne' h
    · exact hF.l_odd h
  have hC2 : IsUnit (2 : C) := by
    by_contra hc
    have hm : (2 : C) ∈ maximalIdeal C := (IsLocalRing.mem_maximalIdeal _).2 hc
    rw [← res_eq_zero_iff O, map_ofNat] at hm
    exact hk2 hm
  obtain ⟨ζ, hζr, hζX⟩ := co_sqrt hC2 X z hz0 hresX
  set ζK : K := algebraMap C K ζ with hζK
  have hK2 : (2 : K) ≠ 0 := by
    have := hC2.map (algebraMap C K)
    rw [map_ofNat] at this
    exact this.ne_zero
  have hζ0 : ζK ≠ 0 := by
    intro h0
    apply hz0
    rw [← hζr, (map_eq_zero_iff _ hinj).1 h0, map_zero]
  have htrK : (D * D).trace = 2 * ζK ^ 2 := by
    rw [hDD, ← ht, ← ht, ← map_sub, ← hX, ← hζX, hζK, map_pow]
  have hv := skew_eig hn hK2 Q D ζK hQ hskew htrK
  obtain ⟨P, hPu, hPQ, hDP⟩ := skew_norm hn hK2 Q D ζK hζ0 hQ hQs hskew hv
  obtain ⟨U, hU⟩ := hPu
  have hPi : (U : Matrix (Fin n) (Fin n) K) * ((U⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K) = 1 := U.mul_inv
  have hiP : ((U⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K) * (U : Matrix (Fin n) (Fin n) K) = 1 := U.inv_mul
  subst hU
  set Pm : Matrix (Fin n) (Fin n) K := (U : Matrix (Fin n) (Fin n) K) with hPm
  set Pi : Matrix (Fin n) (Fin n) K := ((U⁻¹ : (Matrix (Fin n) (Fin n) K)ˣ) : Matrix (Fin n) (Fin n) K) with hPim
  have hconj : ∀ M : Matrix (Fin n) (Fin n) K,
      (MulSemiringAction.toRingHom _ _ (ConjAct.toConjAct U⁻¹)) M = Pi * M * Pm := by
    intro M
    simp [MulSemiringAction.toRingHom_apply, ConjAct.units_smul_def, hPim, hPm]
  have e1 : Q * Pm = Piᵀ * Jmat K n := by
    rw [← hPQ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul, hPi, Matrix.transpose_one, Matrix.one_mul]
  have e2 : Pmᵀ * Q = Jmat K n * Pi := by
    rw [← hPQ, Matrix.mul_assoc (Pmᵀ * Q), hPi, Matrix.mul_one]
  let ρr : F.G0 →* Matrix (Fin n) (Fin n) K :=
    ((MulSemiringAction.toRingHom _ _ (ConjAct.toConjAct U⁻¹) : Matrix (Fin n) (Fin n) K →+* Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K →* Matrix (Fin n) (Fin n) K).comp r
  have hρ : ∀ g, ρr g = Pi * r g * Pm := fun g => hconj (r g)
  have hpol : ∀ g, ρr (F.star g) = Jmat K n * (ρr g)ᵀ * Jmat K n := by
    intro g
    rw [hρ, hρ, Matrix.transpose_mul, Matrix.transpose_mul]
    calc Pi * r (F.star g) * Pm = (Jmat K n * Jmat K n) * Pi * r (F.star g) * Pm := by
          rw [Jmat_mul_Jmat, Matrix.one_mul]
      _ = Jmat K n * (Pmᵀ * Q) * r (F.star g) * Pm := by
          rw [e2]; simp only [Matrix.mul_assoc]
      _ = Jmat K n * Pmᵀ * ((r g)ᵀ * Q) * Pm := by
          rw [← hst]; simp only [Matrix.mul_assoc]
      _ = Jmat K n * Pmᵀ * (r g)ᵀ * (Q * Pm) := by
          simp only [Matrix.mul_assoc]
      _ = Jmat K n * (Pmᵀ * ((r g)ᵀ * Piᵀ)) * Jmat K n := by
          rw [e1]; simp only [Matrix.mul_assoc]
  have hdm : Pi * r F.g0 * Pm - Pi * r (F.star F.g0) * Pm = Matrix.diagonal fun i => (w n i : K) * ζK := by
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, ← hA, ← hB, ← hDdef, Matrix.mul_assoc, hDP, ← Matrix.mul_assoc, hiP, Matrix.one_mul]
  refine ⟨⟨ρr, fun v i => (Units.map (algebraMap C K : C →* K)).comp (χ v i), hpol, ?_, ?_⟩, U⁻¹, ?_, ?_, ?_⟩
  · intro i j hij
    rw [hρ, hρ, hdm, Matrix.diagonal_apply_ne _ hij]
  · intro v g
    exact ordProd_conj U⁻¹ (fun s => r (F.loc0 v s)) (fun i s => algebraMap C K (χ v i s)) g (hord v g)
  · intro g
    rw [inv_inv]
    exact hρ g
  · intro v i g
    rfl
  · refine ⟨⟨t, htr, fun g => ?_⟩, ⟨fun v i g => (χ v i g : C), hpsi, fun v i g => rfl⟩, ⟨ζ, hζr, fun i => ?_⟩⟩
    · change algebraMap C K (t g) = (ρr g).trace
      rw [ht, hρ, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hPi, Matrix.one_mul]
    · change (ρr F.g0 - ρr (F.star F.g0)) i i = _
      rw [hρ, hρ, hdm, Matrix.diagonal_apply_eq]
