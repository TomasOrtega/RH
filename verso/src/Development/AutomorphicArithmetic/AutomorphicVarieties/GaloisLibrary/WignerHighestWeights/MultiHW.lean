import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

/- English proof (translation)
Introduce `ι V _ _ _ n F _ _ hM`. Take `⟨hF, hcomm⟩` from `hM`. Establish `hc : ∀ t k i j, F t k k * F t i j - F t i j * F t k k = ((if k = i then (1 : ℂ) else 0) - (if j = k then 1 else 0)) • F t i j`. Introduce `t k i j`. Rewrite using `[hF t]`.

Apply the tactic sequence `by_cases h1 : k = i <;> by_cases h2 : j = k <;> simp_all`. Set `G : ι → Module.End ℂ V` to `fun s => ∑ k : Fin n, ((k : ℕ) : ℂ) • F s k k`. Establish `hG : ∀ t i j, G t * F t i j - F t i j * G t = (((i : ℕ) : ℂ) - (j : ℕ)) • F t i j`. Introduce `t i j`. Rewrite using `[Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]`.

Simplify using `only [smul_mul_assoc, mul_smul_comm, ← smul_sub, hc, smul_smul, ← Finset.sum_smul]`. Simplify using `[mul_sub]`. Establish `hG' : ∀ s t, s ≠ t → ∀ i j, G s * F t i j - F t i j * G s = 0`. Introduce `s t hst i j`. Rewrite using `[Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]`.

Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, mul_smul_comm, hcomm s t hst, sub_self]`. Set `H : Module.End ℂ V` to `∑ s, G s`. Establish `hH : ∀ t i j, H * F t i j = F t i j * H + (((i : ℕ) : ℂ) - (j : ℕ)) • F t i j`. Introduce `t i j`.

Rewrite using `[← sub_eq_iff_eq_add', Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_eq_single t (fun s _ hs => hG' s t hs i j) (by simp), hG]`. Take `⟨l, hl, hmin⟩` from `Set.exists_min_image {c | H.HasEigenvalue c} Complex.re (Module.End.finite_hasEigenvalue H) (Module.End.exists_eigenvalue H)`. Take `⟨v, hv, hv0, ν, hν⟩` from `GlobalTheory.AlgInfChar.exists_joint_eigenvector (fun p : ι × Fin n => F p.1 p.2 p.2) (fun p q => by`. Take `⟨s, i⟩` from `p`. Take `⟨t, j⟩` from `q`.

Distinguish the cases in `hst : s = t`. Substitute `hst` using the available equality. Rewrite using `[← sub_eq_zero, hc]`. Apply the tactic sequence `by_cases h : i = j <;> simp [h, eq_comm]`. Conclude with `hcomm s t hst _ _ _ _) (H.eigenspace l) hl`.

Use the proof step `(fun k v hv => by`. Rewrite `hv`, the goal using `[Module.End.mem_eigenspace_iff]`. Rewrite using `[← Module.End.mul_apply, hH]`. Simplify using `[hv])`. Rewrite `hv` using `[Module.End.mem_eigenspace_iff]`.

Establish `hup : ∀ t i j, i < j → F t i j v = 0`. Introduce `t i j hij`. Assume the negation of the conclusion as `h0`. Establish `h1 : H (F t i j v) = (l + (((i : ℕ) : ℂ) - (j : ℕ))) • F t i j v`. Rewrite using `[← Module.End.mul_apply, hH]`.

Simplify using `[hv, add_smul]`. Establish `h2` using `hmin _ (Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 h1, h0⟩)`. Simplify using `at h2`. Conclude with `absurd hij (not_lt.2 h2)`. Establish `hν' : ∀ t k, F t k k v = ν (t, k) • v` using `fun t k => hν (t, k)`.

Use `⟨fun t k => ν (t, k), v, hv0, fun t => ⟨⟨hν' t, hup t⟩, fun i j hij => GlobalTheory.AlgInfChar.exists_nat_of_primitive (F t i j) (F t j i) (F t i i - F t j j) ?_ ?_ v _ hv0 (hup t i j hij) ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hF t]`. Simplify using the standard rewrite rules. Establish `h1` using `hc t i j i`. Establish `h2` using `hc t j j i`.

Simplify using `only [hij.ne, if_false, if_true] at h1 h2`. Rewrite using `[sub_mul, mul_sub]`. Take the linear combination `(norm := module) h1 - h2`. Simplify using `[hν', sub_smul]`.
-/
theorem UpperTheory.V.AlgRepEndIrreducible.multiHW :
    ∀ (ι V : Type) [Fintype ι] [AddCommGroup V] [Module ℂ V] (n : ℕ) (F : ι → Fin n → Fin n → Module.End ℂ V) [FiniteDimensional ℂ V] [Nontrivial V], IsMultiGl F →
      ∃ (ν : ι → Fin n → ℂ) (v : V), v ≠ 0 ∧ ∀ t, Formalism.REAL.IsHW (F t) (ν t) v ∧ Dom (ν t) := by
  intro ι V _ _ _ n F _ _ hM
  obtain ⟨hF, hcomm⟩ := hM
  classical
  have hc : ∀ t k i j, F t k k * F t i j - F t i j * F t k k =
      ((if k = i then (1 : ℂ) else 0) - (if j = k then 1 else 0)) • F t i j := by
    intro t k i j
    rw [hF t]
    by_cases h1 : k = i <;> by_cases h2 : j = k <;> simp_all
  let G : ι → Module.End ℂ V := fun s => ∑ k : Fin n, ((k : ℕ) : ℂ) • F s k k
  have hG : ∀ t i j, G t * F t i j - F t i j * G t = (((i : ℕ) : ℂ) - (j : ℕ)) • F t i j := by
    intro t i j
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    simp only [smul_mul_assoc, mul_smul_comm, ← smul_sub, hc, smul_smul, ← Finset.sum_smul]
    simp [mul_sub]
  have hG' : ∀ s t, s ≠ t → ∀ i j, G s * F t i j - F t i j * G s = 0 := by
    intro s t hst i j
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, hcomm s t hst, sub_self]
  let H : Module.End ℂ V := ∑ s, G s
  have hH : ∀ t i j, H * F t i j = F t i j * H + (((i : ℕ) : ℂ) - (j : ℕ)) • F t i j := by
    intro t i j
    rw [← sub_eq_iff_eq_add', Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
      Finset.sum_eq_single t (fun s _ hs => hG' s t hs i j) (by simp), hG]
  obtain ⟨l, hl, hmin⟩ := Set.exists_min_image {c | H.HasEigenvalue c} Complex.re (Module.End.finite_hasEigenvalue H)
    (Module.End.exists_eigenvalue H)
  obtain ⟨v, hv, hv0, ν, hν⟩ := GlobalTheory.AlgInfChar.exists_joint_eigenvector (fun p : ι × Fin n => F p.1 p.2 p.2)
    (fun p q => by
      obtain ⟨s, i⟩ := p
      obtain ⟨t, j⟩ := q
      by_cases hst : s = t
      · subst hst
        rw [← sub_eq_zero, hc]
        by_cases h : i = j <;> simp [h, eq_comm]
      · exact hcomm s t hst _ _ _ _) (H.eigenspace l) hl
    (fun k v hv => by
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      rw [← Module.End.mul_apply, hH]
      simp [hv])
  rw [Module.End.mem_eigenspace_iff] at hv
  have hup : ∀ t i j, i < j → F t i j v = 0 := by
    intro t i j hij
    by_contra h0
    have h1 : H (F t i j v) = (l + (((i : ℕ) : ℂ) - (j : ℕ))) • F t i j v := by
      rw [← Module.End.mul_apply, hH]
      simp [hv, add_smul]
    have h2 := hmin _ (Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 h1, h0⟩)
    simp at h2
    exact absurd hij (not_lt.2 h2)
  have hν' : ∀ t k, F t k k v = ν (t, k) • v := fun t k => hν (t, k)
  refine ⟨fun t k => ν (t, k), v, hv0, fun t => ⟨⟨hν' t, hup t⟩, fun i j hij =>
    GlobalTheory.AlgInfChar.exists_nat_of_primitive (F t i j) (F t j i) (F t i i - F t j j) ?_ ?_ v _ hv0
      (hup t i j hij) ?_⟩⟩
  · rw [hF t]; simp
  · have h1 := hc t i j i
    have h2 := hc t j j i
    simp only [hij.ne, if_false, if_true] at h1 h2
    rw [sub_mul, mul_sub]
    linear_combination (norm := module) h1 - h2
  · simp [hν', sub_smul]
