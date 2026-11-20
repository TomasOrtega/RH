import Mathlib

namespace GlobalTheory.JointEigenvectorsIndependentSatakeParameters

/- English proof (translation)
Rewrite using `[linearIndependent_iff']`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `g _ i hi`.

Simplify using `at hi`. Consider the case `insert a s ha ih`. Introduce `g hg`. Rewrite `hg` using `[Finset.sum_insert ha]`. Establish `e1 : ∑ i ∈ s, g i • v i = -(g a • v a)` using `eq_neg_of_add_eq_zero_right hg`.

Establish `hs : ∀ i ∈ s, g i = 0`. Introduce `i hi`. Establish `hne : (i : J → ℂ) ≠ a` using `fun h => ha (Subtype.ext h ▸ hi)`. Take `⟨j, hj⟩` from `Function.ne_iff.mp hne`. Establish `e2 : ∑ i ∈ s, (g i * (i : J → ℂ) j) • v i = -((g a * (a : J → ℂ) j) • v a)`.

Use `congrArg (T j) e1` as an intermediate fact. Simplify `this` using `[map_sum, map_smul, hT, smul_smul]`. Establish `e3 : ∑ i ∈ s, ((a : J → ℂ) j * g i) • v i = -(((a : J → ℂ) j * g a) • v a)`. Use `congrArg (fun x => (a : J → ℂ) j • x) e1` as an intermediate fact. Simplify `this` using `[Finset.smul_sum, smul_smul]`.

Establish `h2 : ∑ i ∈ s, (g i * ((i : J → ℂ) j - (a : J → ℂ) j)) • v i = 0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← sub_smul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `_ = 0 := by rw [e2, e3, mul_comm ((a : J → ℂ) j) (g a)]; exact sub_self _`. Use `ih (fun i => g i * ((i : J → ℂ) j - (a : J → ℂ) j)) h2 i hi` as an intermediate fact. Conclude with `(mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hj)`.

Establish `hsum : ∑ i ∈ s, g i • v i = 0` using `Finset.sum_eq_zero fun i hi => by rw [hs i hi, zero_smul]`. Introduce `i hi`. Break down `Finset.mem_insert.mp hi with rfl | hi` into its components or cases. Rewrite `hg` using `[hsum, add_zero]`. Conclude with `(smul_eq_zero.mp hg).resolve_right (hv _)`.

Conclude with `hs i hi`.
-/
theorem linearIndependent_jointEigenvectors {J V : Type} [AddCommGroup V] [Module ℂ V]
    (T : J → V →ₗ[ℂ] V) (S : Set (J → ℂ)) (v : S → V)
    (hv : ∀ χ : S, v χ ≠ 0)
    (hT : ∀ (χ : S) (j : J), T j (v χ) = (χ : J → ℂ) j • v χ) :
    LinearIndependent ℂ v := by
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro g _ i hi
    simp at hi
  | insert a s ha ih =>
    intro g hg
    rw [Finset.sum_insert ha] at hg
    have e1 : ∑ i ∈ s, g i • v i = -(g a • v a) := eq_neg_of_add_eq_zero_right hg
    have hs : ∀ i ∈ s, g i = 0 := by
      intro i hi
      have hne : (i : J → ℂ) ≠ a := fun h => ha (Subtype.ext h ▸ hi)
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
      have e2 : ∑ i ∈ s, (g i * (i : J → ℂ) j) • v i = -((g a * (a : J → ℂ) j) • v a) := by
        have := congrArg (T j) e1
        simpa [map_sum, map_smul, hT, smul_smul] using this
      have e3 : ∑ i ∈ s, ((a : J → ℂ) j * g i) • v i = -(((a : J → ℂ) j * g a) • v a) := by
        have := congrArg (fun x => (a : J → ℂ) j • x) e1
        simpa [Finset.smul_sum, smul_smul] using this
      have h2 : ∑ i ∈ s, (g i * ((i : J → ℂ) j - (a : J → ℂ) j)) • v i = 0 := by
        calc ∑ i ∈ s, (g i * ((i : J → ℂ) j - (a : J → ℂ) j)) • v i
            = ∑ i ∈ s, (g i * (i : J → ℂ) j) • v i - ∑ i ∈ s, ((a : J → ℂ) j * g i) • v i := by
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [← sub_smul]
              congr 1
              ring
          _ = 0 := by rw [e2, e3, mul_comm ((a : J → ℂ) j) (g a)]; exact sub_self _
      have := ih (fun i => g i * ((i : J → ℂ) j - (a : J → ℂ) j)) h2 i hi
      exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hj)
    have hsum : ∑ i ∈ s, g i • v i = 0 := Finset.sum_eq_zero fun i hi => by rw [hs i hi, zero_smul]
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · rw [hsum, add_zero] at hg
      exact (smul_eq_zero.mp hg).resolve_right (hv _)
    · exact hs i hi

end GlobalTheory.JointEigenvectorsIndependentSatakeParameters
