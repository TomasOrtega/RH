import Mathlib
open scoped PowerSeries Pointwise

namespace GlobalTheory

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem smul_pow_mem_span_pow_smul_top {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (l : O) (j n : ℕ) (x : M) (h : n ≤ j) :
    l ^ j • x ∈ (Ideal.span {l}) ^ n • (⊤ : Submodule O M) := by
  rw [Ideal.span_singleton_pow]
  have e : l ^ j • x = l ^ n • (l ^ (j - n) • x) := by
    rw [smul_smul, ← pow_add, Nat.add_sub_cancel' h]
  rw [e]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem map_mem_pow_smul_top {O M N : Type} [CommRing O] [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (I : Ideal O) (n : ℕ) (f : M →ₗ[O] N) {x : M}
    (hx : x ∈ I ^ n • (⊤ : Submodule O M)) : f x ∈ I ^ n • (⊤ : Submodule O N) := by
  have hle : I ^ n • (⊤ : Submodule O M) ≤ (I ^ n • (⊤ : Submodule O N)).comap f := by
    rw [Submodule.smul_le]
    intro r hr y _
    simp only [Submodule.mem_comap, map_smul]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  exact hle hx

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Simplify to obtain the desired conclusion from the available facts. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Extract witnesses or component facts from the available result.

Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Treat this case separately. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

A detailed English derivation is pending.
-/
theorem successive_approximation : ∀ {O Y Z : Type} [CommRing O] [AddCommGroup Y] [Module O Y]
    [AddCommGroup Z] [Module O Z] (l : O) [IsAdicComplete (Ideal.span {l}) Y]
    [IsHausdorff (Ideal.span {l}) Z] (Lc P : Y →ₗ[O] Z) (W : Submodule O Z) (c k : ℕ), c < k →
    (∀ y, Lc y ∈ W ∧ (Lc + l ^ k • P) y ∈ W) → (∀ z, l • z ∈ W → z ∈ W) →
    (∀ z ∈ W, l ^ c • z ∈ LinearMap.range Lc) → ∀ y₀ : Y, ∃ y, (Lc + l ^ k • P) y = Lc y₀ := by
  intro O Y Z _ _ _ _ _ l _ _ Lc P W c k hck hW hsat hrange y₀
  have hsatn : ∀ n z, l ^ n • z ∈ W → z ∈ W := by
    intro n
    induction n with
    | zero => intro z h; simpa using h
    | succ n ih =>
      intro z h
      apply ih
      apply hsat
      rwa [smul_smul, ← pow_succ']
  have hPW : ∀ y, P y ∈ W := by
    intro y
    apply hsatn k
    have h := W.sub_mem (hW y).2 (hW y).1
    simpa [LinearMap.add_apply, LinearMap.smul_apply] using h
  have hg : ∀ v, ∃ u, Lc u = l ^ c • P v := fun v => by
    obtain ⟨u, hu⟩ := hrange _ (hPW v)
    exact ⟨u, hu⟩
  choose g hg using hg
  obtain ⟨d, hd, hk⟩ : ∃ d, 1 ≤ d ∧ k = d + c := ⟨k - c, by omega, by omega⟩
  let L' : Y →ₗ[O] Z := Lc + l ^ k • P
  have hL' : ∀ y, L' y = Lc y + l ^ k • P y := fun y => rfl
  let s : ℕ → Y × Y := fun n =>
    Nat.rec (y₀, -y₀) (fun i p => (p.1 + l ^ ((i + 1) * d) • g p.2, -g p.2)) n
  have s_succ : ∀ n, s (n + 1) = ((s n).1 + l ^ ((n + 1) * d) • g (s n).2, -g (s n).2) :=
    fun n => rfl
  have s_zero : s 0 = (y₀, -y₀) := rfl
  have inv : ∀ n, Lc y₀ - L' (s n).1 = l ^ (n * d) • l ^ k • P (s n).2 := by
    intro n
    induction n with
    | zero =>
      rw [s_zero, hL']
      simp
    | succ n ih =>
      rw [s_succ]
      simp only
      rw [map_add, map_smul, ← sub_sub, ih, hL', hg, map_neg, smul_neg, smul_add, smul_smul,
        smul_smul, smul_smul, ← pow_add, ← pow_add, ← pow_add]
      have e : n * d + k = (n + 1) * d + c := by
        rw [hk, add_mul, one_mul, add_assoc]
      rw [e, sub_add_eq_sub_sub, sub_self, zero_sub, smul_neg, smul_smul, ← pow_add]
  have hcauchy : ∀ a b, a ≤ b → (s a).1 ≡ (s b).1 [SMOD (Ideal.span {l}) ^ a • (⊤ : Submodule O Y)] := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => rfl
    | succ b hab ih =>
      rw [SModEq.sub_mem] at ih ⊢
      rw [s_succ]
      simp only
      have h2 := smul_pow_mem_span_pow_smul_top l ((b + 1) * d) a (g (s b).2)
        (by nlinarith)
      have := Submodule.sub_mem _ ih h2
      rwa [sub_sub] at this
  obtain ⟨y, hy⟩ := IsPrecomplete.prec (IsAdicComplete.toIsPrecomplete) (fun {a b} h => hcauchy a b h)
  refine ⟨y, ?_⟩
  have key : Lc y₀ - L' y = 0 := by
    apply IsHausdorff.haus' (I := Ideal.span {l})
    intro n
    rw [SModEq.sub_mem, sub_zero]
    have h1 : Lc y₀ - L' y = (Lc y₀ - L' (s n).1) + L' ((s n).1 - y) := by
      rw [map_sub]; abel
    rw [h1, inv, smul_smul, ← pow_add]
    refine Submodule.add_mem _ (smul_pow_mem_span_pow_smul_top l _ n _ (by nlinarith)) ?_
    exact map_mem_pow_smul_top _ n L' ((SModEq.sub_mem).mp (hy n))
  exact (sub_eq_zero.mp key).symm

end GlobalTheory
