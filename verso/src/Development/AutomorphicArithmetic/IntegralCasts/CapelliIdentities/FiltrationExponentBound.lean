import Mathlib

/- English proof (translation)
Introduce `O A D _ _ _ _ _ _ _ N γ ϖ l E e lam hE he hEe hlam hlam0 hϖ hγ w hw`. Use `choose u hu using hlam`. Establish `hγ' : ∀ (r : ℕ) (x : N), ∃ x' : N, γ (ϖ ^ r • (x : D)) - ϖ ^ r • (x : D) = lam r • (ϖ ^ r • (x : D)) + ϖ ^ (r + 1) • (x' : D)`. Introduce `r x`. Take `⟨x', h1, h2⟩` from `hγ r x x.2`.

Conclude with `⟨⟨x', h1⟩, h2⟩`. Use `choose f hf using hγ'`. Establish `h0 : γ w - w = ϖ • (f 0 ⟨w, hw⟩ : D)`. Use `hf 0 ⟨w, hw⟩` as an intermediate fact. Simplify `this` using `[hlam0]`.

Set `s : ℕ → N` to `fun K => Nat.rec (l ^ E 0 • f 0 ⟨w, hw⟩) (fun k sk => - f (k + 1) (((u k)⁻¹ : Oˣ).val • sk)) K`. Establish `hs0 : s 0 = l ^ E 0 • f 0 ⟨w, hw⟩` using `rfl`. Establish `hsS : ∀ k, s (k + 1) = - f (k + 1) (((u k)⁻¹ : Oˣ).val • s k)` using `fun _ => rfl`. Set `c : ℕ → N` to `fun K => Nat.casesOn K 0 (fun k => ((u k)⁻¹ : Oˣ).val • s k)`. Establish `hc0 : c 0 = 0` using `rfl`.

Establish `hcS : ∀ k, c (k + 1) = ((u k)⁻¹ : Oˣ).val • s k` using `fun _ => rfl`. Use `clear_value c s`. Establish `key : ∀ K, l ^ E K • (γ w - w) - ∑ y ∈ Finset.range (K + 1), l ^ (E K - E y) • (γ (ϖ ^ y • (c y : D)) - ϖ ^ y • (c y : D)) = ϖ ^ (K + 1) • (s K : D)`. Introduce `K`. Proceed by induction on `K with`.

Consider the case `zero`. Simplify using `only [zero_add, Finset.sum_range_one, hc0, hs0, h0, ZeroMemClass.coe_zero, smul_zero, map_zero, sub_zero, pow_one, Submodule.coe_smul]`. Rewrite using `[smul_comm]`. Consider the case `succ K ih`. Establish `hK : E K ≤ E (K + 1)` using `hE (Nat.le_succ K)`.

Establish `hsum : ∑ y ∈ Finset.range (K + 1), l ^ (E (K + 1) - E y) • (γ (ϖ ^ y • (c y : D)) - ϖ ^ y • (c y : D)) = l ^ (E (K + 1) - E K) • ∑ y ∈ Finset.range (K + 1), l ^ (E K - E y) • (γ (ϖ ^ y • (c y : D)) - ϖ ^ y • (c y : D))`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun y hy => ?_` and prove the remaining obligations. Establish `hy' : E y ≤ E K` using `hE (Nat.lt_succ_iff.mp (Finset.mem_range.mp hy))`. Rewrite using `[smul_smul, ← pow_add]`.

Use `congr 2`. Use linear arithmetic over natural numbers and integers. Establish `hp : l ^ E (K + 1) = l ^ (E (K + 1) - E K) * l ^ E K`. Rewrite using `[← pow_add]`. Use `congr 1`.

Use linear arithmetic over natural numbers and integers. Establish `hl : lam (K + 1) • (ϖ ^ (K + 1) • (c (K + 1) : D)) = l ^ (E (K + 1) - E K) • (ϖ ^ (K + 1) • (s K : D))`. Rewrite using `[hcS, Submodule.coe_smul, smul_comm (ϖ ^ (K + 1)), smul_smul, hu]`. Use `congr 1`. Rewrite using `[mul_right_comm, Units.mul_inv, one_mul]`.

Rewrite using `[Finset.sum_range_succ _ (K + 1), hsum, hp, mul_smul, ← sub_sub, ← smul_sub, ih, hf, hl, hsS, ← hcS]`. Simplify using the standard rewrite rules. Use `⟨fun y => (c y : D), by simp [hc0], fun y => (c y).2, fun K => ?_⟩` and prove the remaining obligations. Consider the cases of `K with`. Consider the case `zero`.

Use `⟨l ^ e 0 • (ϖ • (f 0 ⟨w, hw⟩ : D)), N.smul_mem _ (hϖ _ (f 0 ⟨w, hw⟩).2), ?_⟩` and prove the remaining obligations. Simplify using `[h0]`. Consider the case `succ K`. Establish `hK : E K ≤ e (K + 1)` using `(hEe K).trans (he (Nat.le_succ K))`. Use `⟨l ^ (e (K + 1) - E K) • (s K : D), N.smul_mem _ (s K).2, ?_⟩` and prove the remaining obligations.

Establish `hp : l ^ e (K + 1) = l ^ (e (K + 1) - E K) * l ^ E K`. Rewrite using `[← pow_add]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Rewrite using `[smul_comm (ϖ ^ (K + 1)), ← key, smul_sub (l ^ (e (K + 1) - E K)), ← mul_smul, ← hp, Finset.smul_sum]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun y hy => ?_` and prove the remaining obligations. Establish `hyK : y ≤ K` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hy)`. Establish `h1 : E y ≤ E K` using `hE hyK`. Establish `h2 : e y ≤ e (K + 1)` using `he (hyK.trans (Nat.le_succ K))`.

Establish `h3` using `hEe y`. Rewrite using `[smul_comm (ϖ ^ y), map_smul, ← smul_sub, smul_smul, smul_smul, ← pow_add, ← pow_add]`. Use `congr 2`. Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.filtration_exponent_bound :
    ∀ {O A D : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup D] [Module O D] [Module A D]
        [IsScalarTower O A D] (N : Submodule O D) (γ : D →ₗ[O] D) (ϖ : A) (l : O) (E e : ℕ → ℕ) (lam : ℕ → O),
        Monotone E → Monotone e → (∀ y, E y ≤ e y) →
        (∀ r : ℕ, ∃ u : Oˣ, lam (r + 1) = (u : O) * l ^ (E (r + 1) - E r)) →
        lam 0 = 0 → (∀ x ∈ N, ϖ • x ∈ N) →
        (∀ (r : ℕ), ∀ x ∈ N, ∃ x' ∈ N,
          γ (ϖ ^ r • x) - ϖ ^ r • x = lam r • (ϖ ^ r • x) + ϖ ^ (r + 1) • x') →
        ∀ w ∈ N, ∃ c : ℕ → D, c 0 = 0 ∧ (∀ y, c y ∈ N) ∧ ∀ K : ℕ, ∃ t ∈ N,
          l ^ e K • (γ w - w) - ∑ y ∈ Finset.range K, l ^ (e K - e y) •
            (γ (ϖ ^ y • (l ^ (e y - E y) • c y)) - ϖ ^ y • (l ^ (e y - E y) • c y)) = ϖ ^ K • t := by
  intro O A D _ _ _ _ _ _ _ N γ ϖ l E e lam hE he hEe hlam hlam0 hϖ hγ w hw
  choose u hu using hlam
  have hγ' : ∀ (r : ℕ) (x : N), ∃ x' : N,
      γ (ϖ ^ r • (x : D)) - ϖ ^ r • (x : D) = lam r • (ϖ ^ r • (x : D)) + ϖ ^ (r + 1) • (x' : D) := by
    intro r x
    obtain ⟨x', h1, h2⟩ := hγ r x x.2
    exact ⟨⟨x', h1⟩, h2⟩
  choose f hf using hγ'
  have h0 : γ w - w = ϖ • (f 0 ⟨w, hw⟩ : D) := by
    have := hf 0 ⟨w, hw⟩
    simpa [hlam0] using this
  let s : ℕ → N := fun K => Nat.rec (l ^ E 0 • f 0 ⟨w, hw⟩)
    (fun k sk => - f (k + 1) (((u k)⁻¹ : Oˣ).val • sk)) K
  have hs0 : s 0 = l ^ E 0 • f 0 ⟨w, hw⟩ := rfl
  have hsS : ∀ k, s (k + 1) = - f (k + 1) (((u k)⁻¹ : Oˣ).val • s k) := fun _ => rfl
  let c : ℕ → N := fun K => Nat.casesOn K 0 (fun k => ((u k)⁻¹ : Oˣ).val • s k)
  have hc0 : c 0 = 0 := rfl
  have hcS : ∀ k, c (k + 1) = ((u k)⁻¹ : Oˣ).val • s k := fun _ => rfl
  clear_value c s
  have key : ∀ K, l ^ E K • (γ w - w) - ∑ y ∈ Finset.range (K + 1), l ^ (E K - E y) •
      (γ (ϖ ^ y • (c y : D)) - ϖ ^ y • (c y : D)) = ϖ ^ (K + 1) • (s K : D) := by
    intro K
    induction K with
    | zero =>
      simp only [zero_add, Finset.sum_range_one, hc0, hs0, h0, ZeroMemClass.coe_zero, smul_zero,
        map_zero, sub_zero, pow_one, Submodule.coe_smul]
      rw [smul_comm]
    | succ K ih =>
      have hK : E K ≤ E (K + 1) := hE (Nat.le_succ K)
      have hsum : ∑ y ∈ Finset.range (K + 1), l ^ (E (K + 1) - E y) •
          (γ (ϖ ^ y • (c y : D)) - ϖ ^ y • (c y : D)) =
          l ^ (E (K + 1) - E K) • ∑ y ∈ Finset.range (K + 1), l ^ (E K - E y) •
          (γ (ϖ ^ y • (c y : D)) - ϖ ^ y • (c y : D)) := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun y hy => ?_
        have hy' : E y ≤ E K := hE (Nat.lt_succ_iff.mp (Finset.mem_range.mp hy))
        rw [smul_smul, ← pow_add]
        congr 2
        omega
      have hp : l ^ E (K + 1) = l ^ (E (K + 1) - E K) * l ^ E K := by
        rw [← pow_add]
        congr 1
        omega
      have hl : lam (K + 1) • (ϖ ^ (K + 1) • (c (K + 1) : D)) =
          l ^ (E (K + 1) - E K) • (ϖ ^ (K + 1) • (s K : D)) := by
        rw [hcS, Submodule.coe_smul, smul_comm (ϖ ^ (K + 1)), smul_smul, hu]
        congr 1
        rw [mul_right_comm, Units.mul_inv, one_mul]
      rw [Finset.sum_range_succ _ (K + 1), hsum, hp, mul_smul, ← sub_sub, ← smul_sub, ih, hf, hl,
        hsS, ← hcS]
      simp
  refine ⟨fun y => (c y : D), by simp [hc0], fun y => (c y).2, fun K => ?_⟩
  cases K with
  | zero =>
    refine ⟨l ^ e 0 • (ϖ • (f 0 ⟨w, hw⟩ : D)), N.smul_mem _ (hϖ _ (f 0 ⟨w, hw⟩).2), ?_⟩
    simp [h0]
  | succ K =>
    have hK : E K ≤ e (K + 1) := (hEe K).trans (he (Nat.le_succ K))
    refine ⟨l ^ (e (K + 1) - E K) • (s K : D), N.smul_mem _ (s K).2, ?_⟩
    have hp : l ^ e (K + 1) = l ^ (e (K + 1) - E K) * l ^ E K := by
      rw [← pow_add]
      congr 1
      omega
    rw [smul_comm (ϖ ^ (K + 1)), ← key, smul_sub (l ^ (e (K + 1) - E K)), ← mul_smul, ← hp,
      Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun y hy => ?_
    have hyK : y ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hy)
    have h1 : E y ≤ E K := hE hyK
    have h2 : e y ≤ e (K + 1) := he (hyK.trans (Nat.le_succ K))
    have h3 := hEe y
    rw [smul_comm (ϖ ^ y), map_smul, ← smul_sub, smul_smul, smul_smul, ← pow_add, ← pow_add]
    congr 2
    omega
