import Mathlib

open IsLocalRing

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Split into cases according to the possible forms of the given data. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Treat this case separately.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Th.AnnihilatorQuotientFinite.eigKill :
    ∀ {K V : Type} [Field K] [AddCommGroup V] [Module K V] (φ : Module.End K V) (k : ℕ) (F : V), F ∈ ⨆ μ : K, φ.eigenspace μ → (φ ^ k) F = 0 → φ F = 0 := by
  intro K V _ _ _ φ k F hF hk
  have hdisj := Module.End.eigenspaces_iSupIndep φ 0
  set S := ⨆ (μ : K) (_ : μ ≠ 0), φ.eigenspace μ with hS
  have hinv : ∀ z ∈ S, φ z ∈ S := by
    have hle : S ≤ S.comap φ := by
      refine iSup₂_le fun μ hμ => ?_
      intro v hv
      rw [Submodule.mem_comap, Module.End.mem_eigenspace_iff.1 hv]
      exact Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem hμ (Submodule.smul_mem _ _ hv))
    exact fun z hz => hle hz
  have hinj : ∀ z ∈ S, φ z = 0 → z = 0 := by
    intro z hz h0
    have hz0 : z ∈ φ.eigenspace 0 := by
      rw [Module.End.mem_eigenspace_iff, zero_smul]
      exact h0
    exact Submodule.disjoint_def.1 hdisj z hz0 hz
  have hpow : ∀ n : ℕ, ∀ z ∈ S, (φ ^ n) z = 0 → z = 0 := by
    intro n
    induction n with
    | zero =>
      intro z _ h
      simpa using h
    | succ n ih =>
      intro z hz h
      rw [pow_succ, Module.End.mul_apply] at h
      exact hinj z hz (ih _ (hinv z hz) h)
  rw [iSup_split_single _ (0 : K)] at hF
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hF
  have hy' : φ y = 0 := by
    rw [Module.End.mem_eigenspace_iff, zero_smul] at hy
    exact hy
  cases k with
  | zero =>
    have h0 : y + z = 0 := by simpa using hk
    rw [h0, map_zero]
  | succ k =>
    have hyk : (φ ^ (k + 1)) y = 0 := by
      rw [pow_succ, Module.End.mul_apply, hy', map_zero]
    rw [map_add, hyk, zero_add] at hk
    rw [map_add, hy', hpow _ z hz hk, map_zero, add_zero]
