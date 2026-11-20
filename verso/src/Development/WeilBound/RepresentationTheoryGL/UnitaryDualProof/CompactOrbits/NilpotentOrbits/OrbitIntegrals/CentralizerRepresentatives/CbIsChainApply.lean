import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.IsChain

noncomputable section

namespace PositivityTheory.RgUd.T.Nil.Orb.BReps

open Module Submodule

variable {E W : Type} [Field E] [AddCommGroup W] [Module E W]

def cbFam (N : W →ₗ[E] W) {ι : Type} (l : ι → ℕ) (y : ι → W) : (Σ a, Fin (l a)) → W :=
  fun p => (N ^ (p.2 : ℕ)) (y p.1)

/- English proof (translation)
Rewrite using `[pow_succ', Module.End.mul_apply]`.
-/
theorem cb_pow_succ (N : W →ₗ[E] W) (i : ℕ) (x : W) : N ((N ^ i) x) = (N ^ (i + 1)) x := by
  rw [pow_succ', Module.End.mul_apply]

/- English proof (translation)
Rewrite using `[← Module.End.mul_apply, ← pow_add]`.
-/
theorem cb_pow_pow (N : W →ₗ[E] W) (m j : ℕ) (x : W) : (N ^ m) ((N ^ j) x) = (N ^ (m + j)) x := by
  rw [← Module.End.mul_apply, ← pow_add]

/- English proof (translation)
Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hj`. Rewrite using `[show m + d = d + m from add_comm _ _, ← cb_pow_pow, h, map_zero]`.
-/
theorem cb_pow_zero_of_le (N : W →ₗ[E] W) {m j : ℕ} {x : W} (h : (N ^ m) x = 0) (hj : m ≤ j) :
    (N ^ j) x = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [show m + d = d + m from add_comm _ _, ← cb_pow_pow, h, map_zero]

/- English proof (translation)
Introduce `a i`. Rewrite using `[hB]`. Simplify using `only [cbFam]`. Rewrite using `[cb_pow_succ]`. Use `split_ifs with h`.

Rewrite using `[hB]`. Both sides reduce to the same expression. Establish `hi` using `i.isLt`. Rewrite using `[show (i : ℕ) + 1 = l a by omega, hy]`.
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
Proceed by induction on `i with`. Consider the case `zero => simp`. Consider the case `succ i ih`. Establish `h1` using `hB a ⟨i, by omega⟩`. Rewrite `h1` using `[dif_pos (show ((⟨i, by omega⟩ : Fin (l a)) : ℕ) + 1 < l a from hi)]`.

Rewrite using `[← h1, ih (by omega), cb_pow_succ]`.
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
Take `⟨i, hi⟩` from `i`. Conclude with `cb_isChain_apply N hB a h0 i hi`.
-/
theorem cb_isChain_apply' (N : W →ₗ[E] W) {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (a : ι) (h0 : 0 < l a) (i : Fin (l a)) :
    B ⟨a, i⟩ = (N ^ (i : ℕ)) (B ⟨a, ⟨0, h0⟩⟩) := by
  obtain ⟨i, hi⟩ := i
  exact cb_isChain_apply N hB a h0 i hi

/- English proof (translation)
Establish `h1` using `hB a ⟨l a - 1, by omega⟩`. Rewrite `h1` using `[dif_neg (show ¬ (((⟨l a - 1, by omega⟩ : Fin (l a)) : ℕ) + 1 < l a) by simp; omega)]`. Rewrite `h1` using `[cb_isChain_apply N hB a h0 (l a - 1) (by omega), cb_pow_succ]`. Rewrite `h1` using `[show l a - 1 + 1 = l a by omega]`. Then use the resulting hypothesis.
-/
theorem cb_isChain_len (N : W →ₗ[E] W) {ι : Type} {l : ι → ℕ} {B : Module.Basis (Σ a, Fin (l a)) E W}
    (hB : IsChain N l B) (a : ι) (h0 : 0 < l a) : (N ^ l a) (B ⟨a, ⟨0, h0⟩⟩) = 0 := by
  have h1 := hB a ⟨l a - 1, by omega⟩
  rw [dif_neg (show ¬ (((⟨l a - 1, by omega⟩ : Fin (l a)) : ℕ) + 1 < l a) by simp; omega)] at h1
  rw [cb_isChain_apply N hB a h0 (l a - 1) (by omega), cb_pow_succ] at h1
  rwa [show l a - 1 + 1 = l a by omega] at h1

/- English proof (translation)
Establish `key : ∀ k : ℕ, S ⊔ LinearMap.range (N ^ k) = ⊤`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => rw [pow_zero, Module.End.one_eq_id, LinearMap.range_id, sup_top_eq]`. Consider the case `succ k ih`.

Rewrite using `[eq_top_iff]`. Introduce `w _`. Establish `hw : w ∈ S ⊔ LinearMap.range N` using `h ▸ Submodule.mem_top`. Take `⟨x, hx, z, hz, rfl⟩` from `Submodule.mem_sup.mp hw`. Take `⟨z', rfl⟩` from `hz`.

Establish `hz' : z' ∈ S ⊔ LinearMap.range (N ^ k)` using `ih ▸ Submodule.mem_top`. Take `⟨x2, hx2, z2, hz2, rfl⟩` from `Submodule.mem_sup.mp hz'`. Take `⟨z3, rfl⟩` from `hz2`. Rewrite using `[map_add]`. Apply `Submodule.mem_sup.mpr` to reduce the goal to its premises.

Use `⟨x + N x2, S.add_mem hx (hS _ hx2), (N ^ (k + 1)) z3, ⟨z3, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[cb_pow_succ, add_assoc]`. Take `⟨K, hK⟩` from `hN`. Use `key K` as an intermediate fact. Rewrite `this` using `[hK, LinearMap.range_zero, sup_bot_eq]`. Then use the resulting hypothesis.
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
