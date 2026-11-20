import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IndependenceCharacters

/- English proof (translation)
Introduce `V _ _ Ξ P T ev hinj v hv hT`. Rewrite using `[linearIndependent_iff']`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro g _ i hi`.

Simplify using `at hi`. Consider the case `insert a s ha ih`. Introduce `g hg`. Rewrite `hg` using `[Finset.sum_insert ha]`. Establish `hs : ∀ i ∈ s, g i = 0`.

Introduce `i hi`. Establish `hne : ev i ≠ ev a` using `fun h => ha (hinj h ▸ hi)`. Take `⟨p, hp⟩` from `Function.ne_iff.mp hne`. Establish `h1 : (g a * ev a p) • v a + ∑ j ∈ s, (g j * ev j p) • v j = 0`. Establish `h` using `congrArg (T p) hg`.

Simplify `h` using `only [map_add, map_sum, map_smul, map_zero, hT, smul_smul]`. Establish `h2 : (g a * ev a p) • v a + ∑ j ∈ s, (g j * ev a p) • v j = 0`. Establish `h` using `congrArg (fun x => ev a p • x) hg`. Simplify `h` using `only [smul_add, Finset.smul_sum, smul_zero, smul_smul, mul_comm]`. Establish `h3 : ∑ j ∈ s, (g j * (ev j p - ev a p)) • v j = 0`.

Simplify using `only [mul_sub, sub_smul, Finset.sum_sub_distrib]`. Rewrite using `[sub_eq_zero]`. Conclude with `add_left_cancel (h1.trans h2.symm)`. Establish `h4` using `ih (fun j => g j * (ev j p - ev a p)) h3 i hi`. Conclude with `(mul_eq_zero.mp h4).resolve_right (sub_ne_zero.mpr hp)`.

Establish `h0 : ∑ j ∈ s, g j • v j = 0` using `Finset.sum_eq_zero fun j hj => by rw [hs j hj, zero_smul]`. Rewrite `hg` using `[h0, add_zero]`. Introduce `i hi`. Break down `Finset.mem_insert.mp hi with rfl | hi` into its components or cases. Conclude with `(smul_eq_zero.mp hg).resolve_right (hv _)`.

Conclude with `hs i hi`.
-/
theorem UpperTheory.Reformulated.B.LinearIndependentEigenvectors.li_eig :
    ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] {Ξ P : Type}
    (T : P → V →ₗ[ℂ] V) (ev : Ξ → P → ℂ),
    Function.Injective ev →
      ∀ (v : Ξ → V),
        (∀ (ξ : Ξ), v ξ ≠ (0 : V)) → (∀ (ξ : Ξ) (p : P), (T p : V → V) (v ξ) = ev ξ p • v ξ) → LinearIndependent ℂ v := by
  intro V _ _ Ξ P T ev hinj v hv hT
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.induction_on with
  | empty => intro g _ i hi; simp at hi
  | insert a s ha ih =>
    intro g hg
    rw [Finset.sum_insert ha] at hg
    have hs : ∀ i ∈ s, g i = 0 := by
      intro i hi
      have hne : ev i ≠ ev a := fun h => ha (hinj h ▸ hi)
      obtain ⟨p, hp⟩ := Function.ne_iff.mp hne
      have h1 : (g a * ev a p) • v a + ∑ j ∈ s, (g j * ev j p) • v j = 0 := by
        have h := congrArg (T p) hg
        simpa only [map_add, map_sum, map_smul, map_zero, hT, smul_smul] using h
      have h2 : (g a * ev a p) • v a + ∑ j ∈ s, (g j * ev a p) • v j = 0 := by
        have h := congrArg (fun x => ev a p • x) hg
        simpa only [smul_add, Finset.smul_sum, smul_zero, smul_smul, mul_comm] using h
      have h3 : ∑ j ∈ s, (g j * (ev j p - ev a p)) • v j = 0 := by
        simp only [mul_sub, sub_smul, Finset.sum_sub_distrib]
        rw [sub_eq_zero]
        exact add_left_cancel (h1.trans h2.symm)
      have h4 := ih (fun j => g j * (ev j p - ev a p)) h3 i hi
      exact (mul_eq_zero.mp h4).resolve_right (sub_ne_zero.mpr hp)
    have h0 : ∑ j ∈ s, g j • v j = 0 :=
      Finset.sum_eq_zero fun j hj => by rw [hs j hj, zero_smul]
    rw [h0, add_zero] at hg
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact (smul_eq_zero.mp hg).resolve_right (hv _)
    · exact hs i hi
