import Mathlib

open Matrix

/- English proof (translation)
Establish `h` using `Matrix.aeval_self_charpoly M`. Rewrite `h` using `[hM]`. Simplify using `only [map_mul, map_sub, map_add, map_one, map_pow, Polynomial.aeval_X, Polynomial.aeval_C] at h`. Rewrite `h` using `[Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, sq]`. Conclude with `h`.
-/
private lemma cayley_hamilton_rank_three_factored {K : Type} [Field K] (τ : K) (M : Matrix (Fin 3) (Fin 3) K)
    (hM : M.charpoly = (Polynomial.X - 1) * (Polynomial.X ^ 2 - Polynomial.C τ * Polynomial.X + 1)) :
    (M - 1) * (M * M - τ • M + 1) = 0 := by
  have h := Matrix.aeval_self_charpoly M
  rw [hM] at h
  simp only [map_mul, map_sub, map_add, map_one, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C] at h
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, sq] at h
  exact h

/- English proof (translation)
Establish `hp : ∀ t : K, (Matrix.scalar (Fin 3) t - M).det = (t - 1) * (t ^ 2 - τ * t + 1)`. Introduce `t`. Rewrite using `[← Matrix.eval_charpoly, hM]`. Simplify using the standard rewrite rules. Establish `e0` using `hp 0`.

Establish `e1` using `hp 1`. Establish `em` using `hp (-1)`. Simplify using `only [Matrix.det_fin_three, Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply] at e0 e1 em`. Simplify using `only [Fin.isValue, Fin.reduceEq, if_true, if_false, eq_self_iff_true] at e0 e1 em`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[Matrix.trace_fin_three]`. Take the linear combination `e0 - e1 / 2 - em / 2`. Rewrite using `[Matrix.trace_fin_three]`. Simplify using `only [Matrix.mul_apply, Fin.sum_univ_three]`. Take the linear combination `(M 0 0 + M 1 1 + M 2 2 + 1 + τ) * (e0 - e1 / 2 - em / 2) - (e1 - em)`.
-/
private lemma trace_inverseGram_conj_smul_eq {K : Type} [Field K] [CharZero K] (τ : K) (M : Matrix (Fin 3) (Fin 3) K)
    (hM : M.charpoly = (Polynomial.X - 1) * (Polynomial.X ^ 2 - Polynomial.C τ * Polynomial.X + 1)) :
    Matrix.trace M = 1 + τ ∧ Matrix.trace (M * M) = τ ^ 2 - 1 := by
  have hp : ∀ t : K, (Matrix.scalar (Fin 3) t - M).det = (t - 1) * (t ^ 2 - τ * t + 1) := by
    intro t
    rw [← Matrix.eval_charpoly, hM]
    simp
  have e0 := hp 0
  have e1 := hp 1
  have em := hp (-1)
  simp only [Matrix.det_fin_three, Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply] at e0 e1 em
  simp only [Fin.isValue, Fin.reduceEq, if_true, if_false, eq_self_iff_true] at e0 e1 em
  constructor
  · rw [Matrix.trace_fin_three]
    linear_combination e0 - e1 / 2 - em / 2
  · rw [Matrix.trace_fin_three]
    simp only [Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination (M 0 0 + M 1 1 + M 2 2 + 1 + τ) * (e0 - e1 / 2 - em / 2) - (e1 - em)

/- English proof (translation)
Introduce `K _ _ τ hτ M hM`. Establish `hPQ` using `cayley_hamilton_rank_three_factored τ M hM`. Take `⟨htr1, htr2⟩` from `trace_inverseGram_conj_smul_eq τ M hM`. Establish `hc : (2 - τ : K) ≠ 0`. Introduce `h0`.

Apply `hτ` to reduce the goal to its premises. Establish `h2 : τ = 2` using `by linear_combination -h0`. Rewrite using `[h2]`. Evaluate the numerical expressions. Take `⟨Q, hQdef⟩ : ∃ Q : Matrix (Fin 3) (Fin 3) K, Q = M * M - τ • M + 1` from `⟨_, rfl⟩`.

Rewrite `hPQ` using `[← hQdef]`. Establish `hMQ : M * Q = Q`. Rewrite `hPQ` using `[sub_mul, one_mul, sub_eq_zero]`. Conclude with `hPQ`. Establish `hQM : Q * M = Q`.

Establish `hc' : Q * M = M * Q`. Rewrite using `[hQdef]`. Simplify using `only [sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, mul_assoc]`. Rewrite using `[hc', hMQ]`. Establish `hQQ : Q * Q = (2 - τ) • Q`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_add, mul_sub, mul_one, mul_smul_comm, mul_assoc]`. Use `_ = (2 - τ) • Q := by`. Rewrite using `[hQM, hQM, sub_smul, two_smul]`. Normalize the expressions using the abelian group laws.

Take `⟨E, hE⟩ : ∃ E : Matrix (Fin 3) (Fin 3) K, E = (2 - τ)⁻¹ • Q` from `⟨_, rfl⟩`. Establish `hEE : E * E = E`. Rewrite using `[hE, smul_mul_smul_comm, hQQ, smul_smul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Establish `hME : M * E = E` using `by rw [hE, mul_smul_comm, hMQ]`. Establish `hEM : E * M = E` using `by rw [hE, smul_mul_assoc, hQM]`. Establish `htrQ : Matrix.trace Q = 2 - τ`. Rewrite using `[hQdef, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, htr1, htr2, Matrix.trace_one]`. Simplify using `only [Fintype.card_fin, smul_eq_mul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `htrE : Matrix.trace E = 1`. Rewrite using `[hE, Matrix.trace_smul, htrQ, smul_eq_mul, inv_mul_cancel₀ hc]`. Take `⟨F, hF⟩ : ∃ F : Matrix (Fin 3) (Fin 3) K, F = 1 - E` from `⟨_, rfl⟩`.

Establish `htrF : Matrix.trace F = 2`. Rewrite using `[hF, Matrix.trace_sub, Matrix.trace_one, htrE]`. Simplify using `only [Fintype.card_fin]`. Evaluate the numerical expressions. Establish `hQF : Q * F = 0`.

Rewrite using `[hF, mul_sub, mul_one, hE, mul_smul_comm, hQQ, smul_smul, inv_mul_cancel₀ hc, one_smul, sub_self]`. Establish `hEF : E * F = 0` using `by rw [hF, mul_sub, mul_one, hEE, sub_self]`. Establish `hMF : M * F = F * M` using `by rw [hF, mul_sub, sub_mul, mul_one, one_mul, hME, hEM]`. Establish `hQv : ∀ x : Fin 3 → K, Q *ᵥ x = M *ᵥ (M *ᵥ x) - τ • (M *ᵥ x) + x`. Introduce `x`.

Rewrite using `[hQdef, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]`. Establish `hdet : (Matrix.scalar (Fin 3) (1 : K) - M).det = 0`. Rewrite using `[← Matrix.eval_charpoly, hM]`. Simplify using the standard rewrite rules. Take `⟨e, he0, he⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hdet`.

Establish `hMe : M *ᵥ e = e`. Rewrite `he` using `[Matrix.sub_mulVec, sub_eq_zero]`. Simplify using `using he.symm`. Establish `hEe : E *ᵥ e = e`. Establish `h1 : Q *ᵥ e = (2 - τ) • e`.

Rewrite using `[hQv, hMe, hMe, sub_smul, two_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[hE, Matrix.smul_mulVec, h1, smul_smul, inv_mul_cancel₀ hc, one_smul]`. Set `W : Submodule K (Fin 3 → K)` to `LinearMap.range (Matrix.toLin' F)`. Establish `hW : ∀ x ∈ W, Matrix.toLin' M x ∈ W`.

Introduce and unpack `x ⟨y, rfl⟩`. Use `⟨M *ᵥ y, ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hMF]`. Set `g : W →ₗ[K] W` to `(Matrix.toLin' M).restrict hW`. Choose the witnesses or unpack the hypotheses as in `⟨v0, hv0⟩ : ∃ v : W, LinearIndependent K ![v, g v] := by`.

Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Take `⟨a, ha⟩` from `LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent hno`. Establish `hMFx : ∀ x : Fin 3 → K, M *ᵥ (F *ᵥ x) = a • (F *ᵥ x)`. Introduce `x`.

Establish `h` using `congrArg (fun h : W →ₗ[K] W => ((h ⟨F *ᵥ x, x, rfl⟩ : W) : Fin 3 → K)) ha`. Simplify `h` using `[g, LinearMap.restrict_apply, Matrix.toLin'_apply]`. Establish `hMFm : M * F = a • F`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `z`. Rewrite using `[map_smul, LinearMap.smul_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hMFx]`. Establish `htrM : Matrix.trace M = 1 + 2 * a`. Establish `hsplit : M = M * E + M * F` using `by rw [← mul_add, hF, add_sub_cancel, mul_one]`. Rewrite using `[hsplit, Matrix.trace_add, hME, hMFm, Matrix.trace_smul, htrE, htrF, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hF0 : ∃ x : Fin 3 → K, F *ᵥ x ≠ 0`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Establish `hF00 : F = 0`.

Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `z`. Rewrite using `[map_zero, LinearMap.zero_apply, Matrix.toLin'_apply, hall z]`. Rewrite `htrF` using `[hF00, Matrix.trace_zero]`.

Evaluate the numerical expressions using `at htrF`. Take `⟨x, hx⟩` from `hF0`. Establish `hq : (a ^ 2 - τ * a + 1) • (F *ᵥ x) = 0`. Establish `h` using `hQv (F *ᵥ x)`. Rewrite `h` using `[Matrix.mulVec_mulVec, hQF, Matrix.zero_mulVec, hMFx, Matrix.mulVec_smul, hMFx]`.

Rewrite using `[h]`. Use `module`. Establish `hq' : a ^ 2 - τ * a + 1 = 0`. Break down `smul_eq_zero.mp hq with h | h` into its components or cases. Conclude with `h`.

Conclude with `absurd h hx`. Apply `hτ` to reduce the goal to its premises. Establish `ht : τ = 2 * a` using `by linear_combination htr1.symm.trans htrM`. Take the linear combination `(τ - 2 * a) * ht - 4 * hq'`. Take `⟨y, hy⟩` from `v0.2`.

Use `set v : Fin 3 → K := (v0 : Fin 3 → K) with hvdef`. Establish `hvF : v = F *ᵥ y` using `by rw [← hy, Matrix.toLin'_apply]`. Establish `hv : LinearIndependent K ![v, M *ᵥ v]`. Establish `h` using `hv0.map' W.subtype (Submodule.ker_subtype W)`. Establish `hfun : (W.subtype ∘ ![v0, g v0]) = ![v, M *ᵥ v]`.

Use extensionality with `i : 1`. Apply the tactic sequence `fin_cases i <;> simp [g, LinearMap.restrict_apply, Matrix.toLin'_apply, hvdef]`. Rewrite `h` using `[hfun]`. Conclude with `h`. Establish `hQv0 : Q *ᵥ v = 0` using `by rw [hvF, Matrix.mulVec_mulVec, hQF, Matrix.zero_mulVec]`.

Use `⟨e, v, hMe, ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `hQv v`. Rewrite `h` using `[hQv0]`. Rewrite using `[eq_sub_iff_add_eq, ← sub_eq_zero, h]`. Normalize the expressions using the abelian group laws.

Establish `hEv : E *ᵥ v = 0` using `by rw [hvF, Matrix.mulVec_mulVec, hEF, Matrix.zero_mulVec]`. Establish `hEMv : E *ᵥ (M *ᵥ v) = 0` using `by rw [Matrix.mulVec_mulVec, hEM, hEv]`. Establish `hli : LinearIndependent K ![e, v, M *ᵥ v]`. Express the relevant statement in the definitionally equal form `LinearIndependent K (Fin.cons e ![v, M *ᵥ v])`. Rewrite using `[linearIndependent_fin_cons]`.

Use `⟨hv, fun hmem => ?_⟩` and prove the remaining obligations. Establish `hle : Submodule.span K (Set.range ![v, M *ᵥ v]) ≤ LinearMap.ker (Matrix.toLin' E)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Apply the tactic sequence `fin_cases i <;> simp [Matrix.toLin'_apply, hEv, hEMv]`.

Establish `h0` using `hle hmem`. Rewrite `h0` using `[LinearMap.mem_ker, Matrix.toLin'_apply, hEe]`. Conclude with `he0 h0`. Establish `hu : IsUnit (Matrix.of ![e, v, M *ᵥ v])` using `Matrix.linearIndependent_rows_iff_isUnit.mp hli`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero`.
-/
theorem UpperTheory.exists_fixed_rotation_basis_of_charpoly :
    ∀ (K : Type) [Field K] [CharZero K] (τ : K), τ ^ 2 - 4 ≠ 0 → ∀ M : Matrix (Fin 3) (Fin 3) K,
        M.charpoly = (Polynomial.X - 1) * (Polynomial.X ^ 2 - Polynomial.C τ * Polynomial.X + 1) →
        ∃ e v : Fin 3 → K, M *ᵥ e = e ∧ M *ᵥ (M *ᵥ v) = τ • (M *ᵥ v) - v ∧ (Matrix.of ![e, v, M *ᵥ v]).det ≠ 0 := by
  intro K _ _ τ hτ M hM
  have hPQ := cayley_hamilton_rank_three_factored τ M hM
  obtain ⟨htr1, htr2⟩ := trace_inverseGram_conj_smul_eq τ M hM
  have hc : (2 - τ : K) ≠ 0 := by
    intro h0
    apply hτ
    have h2 : τ = 2 := by linear_combination -h0
    rw [h2]
    norm_num
  obtain ⟨Q, hQdef⟩ : ∃ Q : Matrix (Fin 3) (Fin 3) K, Q = M * M - τ • M + 1 := ⟨_, rfl⟩
  rw [← hQdef] at hPQ
  have hMQ : M * Q = Q := by
    rw [sub_mul, one_mul, sub_eq_zero] at hPQ
    exact hPQ
  have hQM : Q * M = Q := by
    have hc' : Q * M = M * Q := by
      rw [hQdef]
      simp only [sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc,
        mul_smul_comm, mul_assoc]
    rw [hc', hMQ]
  have hQQ : Q * Q = (2 - τ) • Q := by
    calc Q * Q = Q * (M * M - τ • M + 1) := by rw [← hQdef]
      _ = Q * M * M - τ • (Q * M) + Q := by
        simp only [mul_add, mul_sub, mul_one, mul_smul_comm, mul_assoc]
      _ = (2 - τ) • Q := by
        rw [hQM, hQM, sub_smul, two_smul]
        abel
  obtain ⟨E, hE⟩ : ∃ E : Matrix (Fin 3) (Fin 3) K, E = (2 - τ)⁻¹ • Q := ⟨_, rfl⟩
  have hEE : E * E = E := by
    rw [hE, smul_mul_smul_comm, hQQ, smul_smul]
    congr 1
    field_simp
  have hME : M * E = E := by rw [hE, mul_smul_comm, hMQ]
  have hEM : E * M = E := by rw [hE, smul_mul_assoc, hQM]
  have htrQ : Matrix.trace Q = 2 - τ := by
    rw [hQdef, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, htr1, htr2, Matrix.trace_one]
    simp only [Fintype.card_fin, smul_eq_mul]
    push_cast
    ring
  have htrE : Matrix.trace E = 1 := by
    rw [hE, Matrix.trace_smul, htrQ, smul_eq_mul, inv_mul_cancel₀ hc]
  obtain ⟨F, hF⟩ : ∃ F : Matrix (Fin 3) (Fin 3) K, F = 1 - E := ⟨_, rfl⟩
  have htrF : Matrix.trace F = 2 := by
    rw [hF, Matrix.trace_sub, Matrix.trace_one, htrE]
    simp only [Fintype.card_fin]
    norm_num
  have hQF : Q * F = 0 := by
    rw [hF, mul_sub, mul_one, hE, mul_smul_comm, hQQ, smul_smul, inv_mul_cancel₀ hc, one_smul,
      sub_self]
  have hEF : E * F = 0 := by rw [hF, mul_sub, mul_one, hEE, sub_self]
  have hMF : M * F = F * M := by rw [hF, mul_sub, sub_mul, mul_one, one_mul, hME, hEM]
  have hQv : ∀ x : Fin 3 → K, Q *ᵥ x = M *ᵥ (M *ᵥ x) - τ • (M *ᵥ x) + x := by
    intro x
    rw [hQdef, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_mulVec]
  have hdet : (Matrix.scalar (Fin 3) (1 : K) - M).det = 0 := by
    rw [← Matrix.eval_charpoly, hM]
    simp
  obtain ⟨e, he0, he⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hMe : M *ᵥ e = e := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at he
    simpa using he.symm
  have hEe : E *ᵥ e = e := by
    have h1 : Q *ᵥ e = (2 - τ) • e := by
      rw [hQv, hMe, hMe, sub_smul, two_smul]
      abel
    rw [hE, Matrix.smul_mulVec, h1, smul_smul, inv_mul_cancel₀ hc, one_smul]
  let W : Submodule K (Fin 3 → K) := LinearMap.range (Matrix.toLin' F)
  have hW : ∀ x ∈ W, Matrix.toLin' M x ∈ W := by
    rintro x ⟨y, rfl⟩
    refine ⟨M *ᵥ y, ?_⟩
    simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hMF]
  let g : W →ₗ[K] W := (Matrix.toLin' M).restrict hW
  obtain ⟨v0, hv0⟩ : ∃ v : W, LinearIndependent K ![v, g v] := by
    by_contra hno
    push_neg at hno
    obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent hno
    have hMFx : ∀ x : Fin 3 → K, M *ᵥ (F *ᵥ x) = a • (F *ᵥ x) := by
      intro x
      have h := congrArg (fun h : W →ₗ[K] W => ((h ⟨F *ᵥ x, x, rfl⟩ : W) : Fin 3 → K)) ha
      simpa [g, LinearMap.restrict_apply, Matrix.toLin'_apply] using h
    have hMFm : M * F = a • F := by
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro z
      rw [map_smul, LinearMap.smul_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
        ← Matrix.mulVec_mulVec, hMFx]
    have htrM : Matrix.trace M = 1 + 2 * a := by
      have hsplit : M = M * E + M * F := by rw [← mul_add, hF, add_sub_cancel, mul_one]
      rw [hsplit, Matrix.trace_add, hME, hMFm, Matrix.trace_smul, htrE, htrF, smul_eq_mul]
      ring
    have hF0 : ∃ x : Fin 3 → K, F *ᵥ x ≠ 0 := by
      by_contra hall
      push_neg at hall
      have hF00 : F = 0 := by
        apply Matrix.toLin'.injective
        apply LinearMap.ext
        intro z
        rw [map_zero, LinearMap.zero_apply, Matrix.toLin'_apply, hall z]
      rw [hF00, Matrix.trace_zero] at htrF
      norm_num at htrF
    obtain ⟨x, hx⟩ := hF0
    have hq : (a ^ 2 - τ * a + 1) • (F *ᵥ x) = 0 := by
      have h := hQv (F *ᵥ x)
      rw [Matrix.mulVec_mulVec, hQF, Matrix.zero_mulVec, hMFx, Matrix.mulVec_smul, hMFx] at h
      rw [h]
      module
    have hq' : a ^ 2 - τ * a + 1 = 0 := by
      rcases smul_eq_zero.mp hq with h | h
      · exact h
      · exact absurd h hx
    apply hτ
    have ht : τ = 2 * a := by linear_combination htr1.symm.trans htrM
    linear_combination (τ - 2 * a) * ht - 4 * hq'
  obtain ⟨y, hy⟩ := v0.2
  set v : Fin 3 → K := (v0 : Fin 3 → K) with hvdef
  have hvF : v = F *ᵥ y := by rw [← hy, Matrix.toLin'_apply]
  have hv : LinearIndependent K ![v, M *ᵥ v] := by
    have h := hv0.map' W.subtype (Submodule.ker_subtype W)
    have hfun : (W.subtype ∘ ![v0, g v0]) = ![v, M *ᵥ v] := by
      ext i : 1
      fin_cases i <;> simp [g, LinearMap.restrict_apply, Matrix.toLin'_apply, hvdef]
    rw [hfun] at h
    exact h
  have hQv0 : Q *ᵥ v = 0 := by rw [hvF, Matrix.mulVec_mulVec, hQF, Matrix.zero_mulVec]
  refine ⟨e, v, hMe, ?_, ?_⟩
  · have h := hQv v
    rw [hQv0] at h
    rw [eq_sub_iff_add_eq, ← sub_eq_zero, h]
    abel
  · have hEv : E *ᵥ v = 0 := by rw [hvF, Matrix.mulVec_mulVec, hEF, Matrix.zero_mulVec]
    have hEMv : E *ᵥ (M *ᵥ v) = 0 := by rw [Matrix.mulVec_mulVec, hEM, hEv]
    have hli : LinearIndependent K ![e, v, M *ᵥ v] := by
      change LinearIndependent K (Fin.cons e ![v, M *ᵥ v])
      rw [linearIndependent_fin_cons]
      refine ⟨hv, fun hmem => ?_⟩
      have hle : Submodule.span K (Set.range ![v, M *ᵥ v]) ≤ LinearMap.ker (Matrix.toLin' E) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        fin_cases i <;> simp [Matrix.toLin'_apply, hEv, hEMv]
      have h0 := hle hmem
      rw [LinearMap.mem_ker, Matrix.toLin'_apply, hEe] at h0
      exact he0 h0
    have hu : IsUnit (Matrix.of ![e, v, M *ᵥ v]) := Matrix.linearIndependent_rows_iff_isUnit.mp hli
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
