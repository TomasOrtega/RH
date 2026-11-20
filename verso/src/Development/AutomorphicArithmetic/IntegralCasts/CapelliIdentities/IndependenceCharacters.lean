import Mathlib

/- English proof (translation)
Introduce `V I J _ _ T v lam hv hT hinj`. Rewrite using `[linearIndependent_iff']`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro g _ j hj`.

Simplify using `at hj`. Consider the case `insert a s ha ih`. Introduce `g hg`. Rewrite `hg` using `[Finset.sum_insert ha]`. Establish `hs : ∀ b ∈ s, g b = 0`.

Introduce `b hb`. Establish `hne : lam b ≠ lam a` using `fun h => ha (hinj h ▸ hb)`. Take `⟨i, hi⟩` from `Function.ne_iff.mp hne`. Establish `h1 : g a • lam a i • v a + ∑ j ∈ s, g j • lam j i • v j = 0`. Use `congrArg (T i) hg` as an intermediate fact.

Simplify `this` using `only [map_add, map_sum, map_smul, map_zero, hT]`. Establish `h2 : g a • lam a i • v a + ∑ j ∈ s, g j • lam a i • v j = 0`. Use `congrArg (fun x => lam a i • x) hg` as an intermediate fact. Simplify `this` using `only [smul_add, Finset.smul_sum, smul_zero, smul_comm (lam a i)]`. Establish `h3 : ∑ j ∈ s, (g j * (lam j i - lam a i)) • v j = 0`.

Establish `h4 : ∑ j ∈ s, g j • lam j i • v j = ∑ j ∈ s, g j • lam a i • v j` using `add_left_cancel (h1.trans h2.symm)`. Simplify using `only [mul_smul, sub_smul, smul_sub, Finset.sum_sub_distrib, h4, sub_self]`. Establish `h5` using `ih (fun j => g j * (lam j i - lam a i)) h3 b hb`. Conclude with `(mul_eq_zero.mp h5).resolve_right (sub_ne_zero.mpr hi)`. Establish `h0 : ∑ j ∈ s, g j • v j = 0` using `Finset.sum_eq_zero fun j hj => by rw [hs j hj, zero_smul]`.

Rewrite `hg` using `[h0, add_zero]`. Introduce `j hj`. Break down `Finset.mem_insert.mp hj with rfl | hj` into its components or cases. Conclude with `(smul_eq_zero.mp hg).resolve_right (hv _)`. Conclude with `hs j hj`.
-/
theorem UpperTheory.Reformulated.B.LinearIndependentOfDistinctEigensystems.indep :
    ∀ {V I J : Type} [inst : AddCommGroup V]
    [inst_1 : _root_.Module ℂ V] (T : I → Module.End ℂ V) (v : J → V) (lam : J → I → ℂ),
    (∀ (j : J), v j ≠ (0 : V)) →
      (∀ (j : J) (i : I), (T i : V → V) (v j) = lam j i • v j) → Function.Injective lam → LinearIndependent ℂ v := by
  intro V I J _ _ T v lam hv hT hinj
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.induction_on with
  | empty => intro g _ j hj; simp at hj
  | insert a s ha ih =>
    intro g hg
    rw [Finset.sum_insert ha] at hg
    have hs : ∀ b ∈ s, g b = 0 := by
      intro b hb
      have hne : lam b ≠ lam a := fun h => ha (hinj h ▸ hb)
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
      have h1 : g a • lam a i • v a + ∑ j ∈ s, g j • lam j i • v j = 0 := by
        have := congrArg (T i) hg
        simpa only [map_add, map_sum, map_smul, map_zero, hT] using this
      have h2 : g a • lam a i • v a + ∑ j ∈ s, g j • lam a i • v j = 0 := by
        have := congrArg (fun x => lam a i • x) hg
        simpa only [smul_add, Finset.smul_sum, smul_zero, smul_comm (lam a i)] using this
      have h3 : ∑ j ∈ s, (g j * (lam j i - lam a i)) • v j = 0 := by
        have h4 : ∑ j ∈ s, g j • lam j i • v j = ∑ j ∈ s, g j • lam a i • v j :=
          add_left_cancel (h1.trans h2.symm)
        simp only [mul_smul, sub_smul, smul_sub, Finset.sum_sub_distrib, h4, sub_self]
      have h5 := ih (fun j => g j * (lam j i - lam a i)) h3 b hb
      exact (mul_eq_zero.mp h5).resolve_right (sub_ne_zero.mpr hi)
    have h0 : ∑ j ∈ s, g j • v j = 0 :=
      Finset.sum_eq_zero fun j hj => by rw [hs j hj, zero_smul]
    rw [h0, add_zero] at hg
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (smul_eq_zero.mp hg).resolve_right (hv _)
    · exact hs j hj
