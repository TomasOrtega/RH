import Mathlib

namespace Bl.general_b_fact'''

/- English proof (translation)
Introduce `K V ι Γ _ _ _ T c w hw hT hc`. Rewrite using `[linearIndependent_iff']`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro g _ i hi`.

Simplify using `at hi`. Consider the case `insert a s ha ih`. Introduce `g hg`. Establish `key : ∀ i ∈ s, g i = 0`. Introduce `i hi`.

Establish `hia : i ≠ a` using `fun h => ha (h ▸ hi)`. Take `⟨γ, hγ⟩` from `hc i a hia`. Establish `e : ∀ j, (g j * (c j γ - c a γ)) • w j = T γ (g j • w j) - c a γ • (g j • w j)`. Introduce `j`. Rewrite using `[map_smul, hT, smul_smul, smul_smul, ← sub_smul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : ∑ j ∈ insert a s, (g j * (c j γ - c a γ)) • w j = 0`. Rewrite using `[Finset.sum_congr rfl (fun j _ => e j), Finset.sum_sub_distrib, ← map_sum, ← Finset.smul_sum, hg, map_zero, smul_zero, sub_zero]`. Rewrite `h2` using `[Finset.sum_insert ha, sub_self, mul_zero, zero_smul, zero_add]`.

Use `ih (fun j => g j * (c j γ - c a γ)) h2 i hi` as an intermediate fact. Conclude with `(mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hγ)`. Introduce `i hi`. Take `h | hi` from `Finset.mem_insert.mp hi`. Substitute `h` using the available equality.

Rewrite `hg` using `[Finset.sum_insert ha, Finset.sum_eq_zero (fun j hj => by rw [key j hj, zero_smul]), add_zero]`. Conclude with `(smul_eq_zero.mp hg).resolve_right (hw _)`. Conclude with `key i hi`.
-/
theorem goal1 :
  ∀ {K V ι Γ : Type} [inst : Field.{0} K] [inst_1 : AddCommGroup.{0} V] [inst_2 : Module.{0, 0} K V]
  (T : Γ → LinearMap.{0, 0, 0, 0} (RingHom.id.{0} K) V V) (c : ι → Γ → K) (w : ι → V),
  (∀ (i : ι), Ne.{1} (w i) 0) →
    (∀ (i : ι) (γ : Γ), Eq.{1} (DFunLike.coe.{1, 1, 1} (T γ) (w i)) (HSMul.hSMul.{0, 0, 0} (c i γ) (w i))) →
      (∀ (i j : ι), Ne.{1} i j → Exists.{1} fun (γ : Γ) ↦ Ne.{1} (c i γ) (c j γ)) → LinearIndependent.{0, 0, 0} K w := by
  intro K V ι Γ _ _ _ T c w hw hT hc
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.induction_on with
  | empty => intro g _ i hi; simp at hi
  | insert a s ha ih =>
    intro g hg
    have key : ∀ i ∈ s, g i = 0 := by
      intro i hi
      have hia : i ≠ a := fun h => ha (h ▸ hi)
      obtain ⟨γ, hγ⟩ := hc i a hia
      have e : ∀ j, (g j * (c j γ - c a γ)) • w j = T γ (g j • w j) - c a γ • (g j • w j) := by
        intro j
        rw [map_smul, hT, smul_smul, smul_smul, ← sub_smul]
        congr 1
        ring
      have h2 : ∑ j ∈ insert a s, (g j * (c j γ - c a γ)) • w j = 0 := by
        rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_sub_distrib, ← map_sum, ← Finset.smul_sum, hg,
          map_zero, smul_zero, sub_zero]
      rw [Finset.sum_insert ha, sub_self, mul_zero, zero_smul, zero_add] at h2
      have := ih (fun j => g j * (c j γ - c a γ)) h2 i hi
      exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hγ)
    intro i hi
    obtain h | hi := Finset.mem_insert.mp hi
    · subst h
      rw [Finset.sum_insert ha, Finset.sum_eq_zero (fun j hj => by rw [key j hj, zero_smul]), add_zero] at hg
      exact (smul_eq_zero.mp hg).resolve_right (hw _)
    · exact key i hi

end Bl.general_b_fact'''
