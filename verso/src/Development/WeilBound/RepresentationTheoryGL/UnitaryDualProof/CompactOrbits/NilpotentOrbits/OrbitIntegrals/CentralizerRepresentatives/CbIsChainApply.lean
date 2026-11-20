import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.IsChain

noncomputable section

namespace PositivityTheory.RgUd.T.Nil.Orb.BReps

open Module Submodule

variable {E W : Type} [Field E] [AddCommGroup W] [Module E W]

def cbFam (N : W →ₗ[E] W) {ι : Type} (l : ι → ℕ) (y : ι → W) : (Σ a, Fin (l a)) → W :=
  fun p => (N ^ (p.2 : ℕ)) (y p.1)

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem cb_pow_succ (N : W →ₗ[E] W) (i : ℕ) (x : W) : N ((N ^ i) x) = (N ^ (i + 1)) x := by
  rw [pow_succ', Module.End.mul_apply]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem cb_pow_pow (N : W →ₗ[E] W) (m j : ℕ) (x : W) : (N ^ m) ((N ^ j) x) = (N ^ (m + j)) x := by
  rw [← Module.End.mul_apply, ← pow_add]

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.
-/
theorem cb_pow_zero_of_le (N : W →ₗ[E] W) {m j : ℕ} {x : W} (h : (N ^ m) x = 0) (hj : m ≤ j) :
    (N ^ j) x = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [show m + d = d + m from add_comm _ _, ← cb_pow_pow, h, map_zero]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem cb_isChain_of_fam (N : W →ₗ[E] W) {ι : Type} (l : ι → ℕ) (y : ι → W)
    (hy : ∀ a, (N ^ l a) (y a) = 0) (B : Module.Basis (Σ a, Fin (l a)) E W)
    (hB : ∀ p, B p = cbFam N l y p) : IsChain N l B := by
  intro a i
  rw [hB]
  simp only [cbFam]
  rw [cb_pow_succ]
  split_ifs with h
  · rw [hB]; rfl
  · have hi := i.isLt
    rw [show (i : ℕ) + 1 = l a by omega, hy]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities.
-/
theorem cb_isChain_apply (N : W →ₗ[E] W) {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (a : ι) (h0 : 0 < l a) (i : ℕ) (hi : i < l a) :
    B ⟨a, ⟨i, hi⟩⟩ = (N ^ i) (B ⟨a, ⟨0, h0⟩⟩) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h1 := hB a ⟨i, by omega⟩
    rw [dif_pos (show ((⟨i, by omega⟩ : Fin (l a)) : ℕ) + 1 < l a from hi)] at h1
    rw [← h1, ih (by omega), cb_pow_succ]

/- English proof (translation)
Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem cb_isChain_apply' (N : W →ₗ[E] W) {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (a : ι) (h0 : 0 < l a) (i : Fin (l a)) :
    B ⟨a, i⟩ = (N ^ (i : ℕ)) (B ⟨a, ⟨0, h0⟩⟩) := by
  obtain ⟨i, hi⟩ := i
  exact cb_isChain_apply N hB a h0 i hi

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem cb_isChain_len (N : W →ₗ[E] W) {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (a : ι) (h0 : 0 < l a) : (N ^ l a) (B ⟨a, ⟨0, h0⟩⟩) = 0 := by
  have h1 := hB a ⟨l a - 1, by omega⟩
  rw [dif_neg (show ¬ (((⟨l a - 1, by omega⟩ : Fin (l a)) : ℕ) + 1 < l a) by simp; omega)] at h1
  rw [cb_isChain_apply N hB a h0 (l a - 1) (by omega), cb_pow_succ] at h1
  rwa [show l a - 1 + 1 = l a by omega] at h1

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem cb_eq_top (N : W →ₗ[E] W) (hN : IsNilpotent N) (S : Submodule E W)
    (hS : ∀ x ∈ S, N x ∈ S) (h : S ⊔ LinearMap.range N = ⊤) : S = ⊤ := by
  have key : ∀ k : ℕ, S ⊔ LinearMap.range (N ^ k) = ⊤ := by
    intro k
    induction k with
    | zero => rw [pow_zero, Module.End.one_eq_id, LinearMap.range_id, sup_top_eq]
    | succ k ih =>
      rw [eq_top_iff]
      intro w _
      have hw : w ∈ S ⊔ LinearMap.range N := h ▸ Submodule.mem_top
      obtain ⟨x, hx, z, hz, rfl⟩ := Submodule.mem_sup.mp hw
      obtain ⟨z', rfl⟩ := hz
      have hz' : z' ∈ S ⊔ LinearMap.range (N ^ k) := ih ▸ Submodule.mem_top
      obtain ⟨x2, hx2, z2, hz2, rfl⟩ := Submodule.mem_sup.mp hz'
      obtain ⟨z3, rfl⟩ := hz2
      rw [map_add]
      apply Submodule.mem_sup.mpr
      refine ⟨x + N x2, S.add_mem hx (hS _ hx2), (N ^ (k + 1)) z3, ⟨z3, rfl⟩, ?_⟩
      rw [cb_pow_succ, add_assoc]
  obtain ⟨K, hK⟩ := hN
  have := key K
  rwa [hK, LinearMap.range_zero, sup_bot_eq] at this

end PositivityTheory.RgUd.T.Nil.Orb.BReps
