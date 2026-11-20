import Mathlib
open scoped PowerSeries Pointwise

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[Ideal.span_singleton_pow]`. Establish `e : l ^ j • x = l ^ n • (l ^ (j - n) • x)`. Rewrite using `[smul_smul, ← pow_add, Nat.add_sub_cancel' h]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top`.
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
Establish `hle : I ^ n • (⊤ : Submodule O M) ≤ (I ^ n • (⊤ : Submodule O N)).comap f`. Rewrite using `[Submodule.smul_le]`. Introduce `r hr y _`. Simplify using `only [Submodule.mem_comap, map_smul]`. Conclude with `Submodule.smul_mem_smul hr Submodule.mem_top`.

Conclude with `hle hx`.
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
Introduce `O Y Z _ _ _ _ _ l _ _ Lc P W c k hck hW hsat hrange y₀`. Establish `hsatn : ∀ n z, l ^ n • z ∈ W → z ∈ W`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro z h`.

Simplify using `using h`. Consider the case `succ n ih`. Introduce `z h`. Apply `ih` to reduce the goal to its premises. Apply `hsat` to reduce the goal to its premises.

Rewrite using `[smul_smul, ← pow_succ']` and apply the resulting hypothesis. Establish `hPW : ∀ y, P y ∈ W`. Introduce `y`. Apply `hsatn k` to reduce the goal to its premises. Establish `h` using `W.sub_mem (hW y).2 (hW y).1`.

Simplify `h` using `[LinearMap.add_apply, LinearMap.smul_apply]`. Establish `hg : ∀ v, ∃ u, Lc u = l ^ c • P v` using `fun v => by`. Take `⟨u, hu⟩` from `hrange _ (hPW v)`. Conclude with `⟨u, hu⟩`. Use `choose g hg using hg`.

Take `⟨d, hd, hk⟩ : ∃ d, 1 ≤ d ∧ k = d + c` from `⟨k - c, by omega, by omega⟩`. Set `L' : Y →ₗ[O] Z` to `Lc + l ^ k • P`. Establish `hL' : ∀ y, L' y = Lc y + l ^ k • P y` using `fun y => rfl`. Set `s : ℕ → Y × Y` to `fun n => Nat.rec (y₀, -y₀) (fun i p => (p.1 + l ^ ((i + 1) * d) • g p.2, -g p.2)) n`. Establish `s_succ : ∀ n, s (n + 1) = ((s n).1 + l ^ ((n + 1) * d) • g (s n).2, -g (s n).2)` using `fun n => rfl`.

Establish `s_zero : s 0 = (y₀, -y₀)` using `rfl`. Establish `inv : ∀ n, Lc y₀ - L' (s n).1 = l ^ (n * d) • l ^ k • P (s n).2`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`.

Rewrite using `[s_zero, hL']`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Rewrite using `[s_succ]`. Simplify using `only`.

Rewrite using `[map_add, map_smul, ← sub_sub, ih, hL', hg, map_neg, smul_neg, smul_add, smul_smul, smul_smul, smul_smul, ← pow_add, ← pow_add, ← pow_add]`. Establish `e : n * d + k = (n + 1) * d + c`. Rewrite using `[hk, add_mul, one_mul, add_assoc]`. Rewrite using `[e, sub_add_eq_sub_sub, sub_self, zero_sub, smul_neg, smul_smul, ← pow_add]`. Establish `hcauchy : ∀ a b, a ≤ b → (s a).1 ≡ (s b).1 [SMOD (Ideal.span {l}) ^ a • (⊤ : Submodule O Y)]`.

Introduce `a b hab`. Proceed by induction on `b, hab using Nat.le_induction with`. Consider the case `base => rfl`. Consider the case `succ b hab ih`. Rewrite `ih`, the goal using `[SModEq.sub_mem]`.

Rewrite using `[s_succ]`. Simplify using `only`. Establish `h2` using `smul_pow_mem_span_pow_smul_top l ((b + 1) * d) a (g (s b).2) (by nlinarith)`. Use `Submodule.sub_mem _ ih h2` as an intermediate fact. Rewrite `this` using `[sub_sub]`. Then use the resulting hypothesis.

Take `⟨y, hy⟩` from `IsPrecomplete.prec (IsAdicComplete.toIsPrecomplete) (fun {a b} h => hcauchy a b h)`. Use `⟨y, ?_⟩` and prove the remaining obligations. Establish `key : Lc y₀ - L' y = 0`. Apply `IsHausdorff.haus' (I := Ideal.span {l})` to reduce the goal to its premises. Introduce `n`.

Rewrite using `[SModEq.sub_mem, sub_zero]`. Establish `h1 : Lc y₀ - L' y = (Lc y₀ - L' (s n).1) + L' ((s n).1 - y)`. Rewrite using `[map_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[h1, inv, smul_smul, ← pow_add]`.

Use `Submodule.add_mem _ (smul_pow_mem_span_pow_smul_top l _ n _ (by nlinarith)) ?_` and prove the remaining obligations. Conclude with `map_mem_pow_smul_top _ n L' ((SModEq.sub_mem).mp (hy n))`. Conclude with `(sub_eq_zero.mp key).symm`.
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
