import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

open MeasureTheory Set UpperHalfPlane
open scoped MatrixGroups ENNReal

/- English proof (translation)
Introduce `hN`. Unfold `UpperTheory.V.Af.Rs.FdNull at hN`. Unfold `UpperTheory.V.Af.Rs.FdCount`. Use `haveI : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))`. Use `haveI : Countable SL(2, ℤ) := inferInstanceAs (Countable {A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1})`.

Establish `hnull : ∀ γ : SL(2, ℤ), volume ((fun z : ℍ => γ • z) ⁻¹' (ModularGroup.fd \ ModularGroup.fdo)) = 0`. Introduce `γ`. Establish `: (fun z : ℍ => γ • z) = fun z : ℍ => ((γ : GL (Fin 2) ℝ)) • z` using `rfl`. Rewrite using `[this, measure_preimage_smul]`. Conclude with `hN`.

Establish `hB` using `measure_iUnion_null hnull`. Rewrite using `[ae_iff]`. Use `measure_mono_null ?_ hB` and prove the remaining obligations. Introduce `z hz`. Assume the negation of the conclusion as `hzB`.

Simplify using `only [mem_iUnion, mem_preimage, not_exists] at hzB`. Take `⟨g, hg⟩` from `ModularGroup.exists_smul_mem_fd z`. Establish `hgo : g • z ∈ ModularGroup.fdo`. Assume the negation of the conclusion as `h`. Conclude with `hzB g ⟨hg, h⟩`.

Establish `hne : g ≠ -g`. Introduce `h`. Establish `h1 : (1 : SL(2, ℤ)) = -1`. Use `congrArg (fun A => A * g⁻¹) h` as an intermediate fact. Simplify using `using this`.

Use `congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h1` as an intermediate fact. Simplify using `at this`. Apply `hz` to reduce the goal to its premises. Rewrite using `[tsum_eq_sum (s := {g, -g}) ?_]`. Rewrite using `[Finset.sum_pair hne]`.

Establish `hg' : (-g) • z ∈ ModularGroup.fd` using `by simpa using hg`. Rewrite using `[indicator_of_mem hg, indicator_of_mem hg', one_add_one_eq_two]`. Introduce `γ hγ`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton, not_or] at hγ`. Apply `indicator_of_notMem` to reduce the goal to its premises.

Introduce `hmem`. Establish `heq : γ • z = (γ * g⁻¹) • (g • z)`. Rewrite using `[smul_smul, inv_mul_cancel_right]`. Rewrite `hmem` using `[heq]`. Break down `ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd hgo hmem with h | h` into its components or cases.

Conclude with `hγ.1 (mul_inv_eq_one.mp h)`. Apply `hγ.2` to reduce the goal to its premises. Rewrite `h` using `[mul_inv_eq_iff_eq_mul]`. Rewrite using `[h]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.V.Af.Rs.fdCount :
    UpperTheory.V.Af.Rs.FdNull → UpperTheory.V.Af.Rs.FdCount := by
  intro hN
  unfold UpperTheory.V.Af.Rs.FdNull at hN
  unfold UpperTheory.V.Af.Rs.FdCount
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  haveI : Countable SL(2, ℤ) :=
    inferInstanceAs (Countable {A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1})
  have hnull : ∀ γ : SL(2, ℤ),
      volume ((fun z : ℍ => γ • z) ⁻¹' (ModularGroup.fd \ ModularGroup.fdo)) = 0 := by
    intro γ
    have : (fun z : ℍ => γ • z) = fun z : ℍ => ((γ : GL (Fin 2) ℝ)) • z := rfl
    rw [this, measure_preimage_smul]
    exact hN
  have hB := measure_iUnion_null hnull
  rw [ae_iff]
  refine measure_mono_null ?_ hB
  intro z hz
  by_contra hzB
  simp only [mem_iUnion, mem_preimage, not_exists] at hzB
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
  have hgo : g • z ∈ ModularGroup.fdo := by
    by_contra h
    exact hzB g ⟨hg, h⟩
  have hne : g ≠ -g := by
    intro h
    have h1 : (1 : SL(2, ℤ)) = -1 := by
      have := congrArg (fun A => A * g⁻¹) h
      simpa using this
    have := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h1
    simp at this
  apply hz
  rw [tsum_eq_sum (s := {g, -g}) ?_]
  · rw [Finset.sum_pair hne]
    have hg' : (-g) • z ∈ ModularGroup.fd := by simpa using hg
    rw [indicator_of_mem hg, indicator_of_mem hg', one_add_one_eq_two]
  · intro γ hγ
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hγ
    apply indicator_of_notMem
    intro hmem
    have heq : γ • z = (γ * g⁻¹) • (g • z) := by
      rw [smul_smul, inv_mul_cancel_right]
    rw [heq] at hmem
    rcases ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd hgo hmem with h | h
    · exact hγ.1 (mul_inv_eq_one.mp h)
    · apply hγ.2
      rw [mul_inv_eq_iff_eq_mul] at h
      rw [h]
      simp
