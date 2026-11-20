import Mathlib

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `f hf`. Simplify using `using hf`. Consider the case `succ n ih`.

Introduce `f hf`. Rewrite using `[pow_succ, Module.End.mul_apply]`. Conclude with `ih _ (hT f hf)`.
-/
private theorem UpperTheory.pow_preserves_submodule {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (U : Submodule A M) (T : Module.End A M) (hT : ∀ f ∈ U, T f ∈ U) (n : ℕ) :
    ∀ f ∈ U, (T ^ n) f ∈ U := by
  induction n with
  | zero =>
    intro f hf
    simpa using hf
  | succ n ih =>
    intro f hf
    rw [pow_succ, Module.End.mul_apply]
    exact ih _ (hT f hf)

/- English proof (translation)
Take `⟨r, rfl⟩` from `Nat.exists_eq_add_of_le hm`. Establish `h'` using `UpperTheory.pow_preserves_submodule U T hT r _ h`. Establish `e : (T ^ r) ((T ^ (a + q)) f - (T ^ a) f) = (T ^ (a + r + q)) f - (T ^ (a + r)) f`. Rewrite using `[show a + r + q = r + (a + q) by ring, show a + r = r + a by ring, pow_add T r (a + q), pow_add T r a, Module.End.mul_apply, Module.End.mul_apply, map_sub]`. Rewrite `h'` using `[e]`.

Conclude with `h'`.
-/
private theorem UpperTheory.periodic_difference_shift {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (U : Submodule A M) (T : Module.End A M) (hT : ∀ f ∈ U, T f ∈ U) (f : M) (a q : ℕ)
    (h : (T ^ (a + q)) f - (T ^ a) f ∈ U) (m : ℕ) (hm : a ≤ m) :
    (T ^ (m + q)) f - (T ^ m) f ∈ U := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hm
  have h' := UpperTheory.pow_preserves_submodule U T hT r _ h
  have e : (T ^ r) ((T ^ (a + q)) f - (T ^ a) f) = (T ^ (a + r + q)) f - (T ^ (a + r)) f := by
    rw [show a + r + q = r + (a + q) by ring, show a + r = r + a by ring,
      pow_add T r (a + q), pow_add T r a, Module.End.mul_apply, Module.End.mul_apply, map_sub]
  rw [e] at h'
  exact h'

/- English proof (translation)
Proceed by induction on `c with`. Consider the case `zero => simp`. Consider the case `succ c ih`. Establish `h2` using `UpperTheory.periodic_difference_shift U T hT f a q h (m + q * c) (by omega)`. Establish `e : m + q * (c + 1) = m + q * c + q` using `by ring`.

Rewrite using `[e]`. Establish `hs` using `U.add_mem h2 ih`. Rewrite `hs` using `[sub_add_sub_cancel]`. Conclude with `hs`.
-/
private theorem UpperTheory.periodic_difference_mul_period {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (U : Submodule A M) (T : Module.End A M) (hT : ∀ f ∈ U, T f ∈ U) (f : M) (a q : ℕ)
    (h : (T ^ (a + q)) f - (T ^ a) f ∈ U) (m : ℕ) (hm : a ≤ m) (c : ℕ) :
    (T ^ (m + q * c)) f - (T ^ m) f ∈ U := by
  induction c with
  | zero => simp
  | succ c ih =>
    have h2 := UpperTheory.periodic_difference_shift U T hT f a q h (m + q * c) (by omega)
    have e : m + q * (c + 1) = m + q * c + q := by ring
    rw [e]
    have hs := U.add_mem h2 ih
    rw [sub_add_sub_cancel] at hs
    exact hs

/- English proof (translation)
Take `⟨N, hN⟩ : ∃ N, N = a * (p + 1)` from `⟨_, rfl⟩`. Establish `haN : a ≤ N`. Rewrite using `[hN]`. Conclude with `Nat.le_mul_of_pos_right a (Nat.succ_pos p)`. Establish `hbase : ∀ i, N + (p + 1) ≤ i → (T ^ i.factorial) f - (T ^ N) f ∈ U`.

Introduce `i hi`. Take `⟨k, hk⟩` from `Nat.dvd_factorial (Nat.succ_pos p) (show p + 1 ≤ i by omega)`. Establish `hi' : N ≤ i.factorial` using `le_trans (by omega) (Nat.self_le_factorial i)`. Establish `hak : a ≤ k`. Rewrite `hi'` using `[hk, hN, mul_comm]`.

Conclude with `Nat.le_of_mul_le_mul_left hi' (Nat.succ_pos p)`. Take `⟨c, rfl⟩` from `Nat.exists_eq_add_of_le hak`. Establish `e : i.factorial = N + (p + 1) * c`. Rewrite using `[hk, hN, Nat.succ_eq_add_one]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `UpperTheory.periodic_difference_mul_period U T hT f a (p + 1) h N haN c`. Use `⟨N + (p + 1), fun i j hi hj => ?_⟩` and prove the remaining obligations. Establish `hs` using `U.sub_mem (hbase i hi) (hbase j hj)`. Rewrite `hs` using `[sub_sub_sub_cancel_right]`. Then use the resulting hypothesis.
-/
private theorem UpperTheory.factorial_powers_cauchy {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (U : Submodule A M) (T : Module.End A M) (hT : ∀ f ∈ U, T f ∈ U) (f : M) (a p : ℕ)
    (h : (T ^ (a + (p + 1))) f - (T ^ a) f ∈ U) :
    ∃ J : ℕ, ∀ i j, J ≤ i → J ≤ j → (T ^ i.factorial) f - (T ^ j.factorial) f ∈ U := by
  obtain ⟨N, hN⟩ : ∃ N, N = a * (p + 1) := ⟨_, rfl⟩
  have haN : a ≤ N := by
    rw [hN]
    exact Nat.le_mul_of_pos_right a (Nat.succ_pos p)
  have hbase : ∀ i, N + (p + 1) ≤ i → (T ^ i.factorial) f - (T ^ N) f ∈ U := by
    intro i hi
    obtain ⟨k, hk⟩ := Nat.dvd_factorial (Nat.succ_pos p) (show p + 1 ≤ i by omega)
    have hi' : N ≤ i.factorial := le_trans (by omega) (Nat.self_le_factorial i)
    have hak : a ≤ k := by
      rw [hk, hN, mul_comm] at hi'
      exact Nat.le_of_mul_le_mul_left hi' (Nat.succ_pos p)
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hak
    have e : i.factorial = N + (p + 1) * c := by
      rw [hk, hN, Nat.succ_eq_add_one]
      ring
    rw [e]
    exact UpperTheory.periodic_difference_mul_period U T hT f a (p + 1) h N haN c
  refine ⟨N + (p + 1), fun i j hi hj => ?_⟩
  have hs := U.sub_mem (hbase i hi) (hbase j hj)
  rwa [sub_sub_sub_cancel_right] at hs

/- English proof (translation)
Introduce `A M _ _ _ V T hV hT hsep hcomp hper`. Establish `hJ : ∀ f k, ∃ J : ℕ, ∀ i j, J ≤ i → J ≤ j → (T ^ i.factorial) f - (T ^ j.factorial) f ∈ V k`. Introduce `f k`. Take `⟨a, p, h⟩` from `hper f k`. Conclude with `UpperTheory.factorial_powers_cauchy (V k) T (hT k) f a p h`.

Use `choose J hJ using hJ`. Set `Nm : M → ℕ → ℕ` to `fun f k => ∑ i ∈ Finset.range (k + 1), J f i`. Establish `hNmJ : ∀ f k, J f k ≤ Nm f k` using `fun f k => Finset.single_le_sum (f := J f) (fun _ _ => Nat.zero_le _) (Finset.self_mem_range_succ k)`. Establish `hNmmono : ∀ f k, Nm f k ≤ Nm f (k + 1)` using `fun f k => by`. Simplify using `only [Nm]`.

Rewrite using `[Finset.sum_range_succ _ (k + 1)]`. Use linear arithmetic over natural numbers and integers. Establish `hseq : ∀ f k, (T ^ (Nm f (k + 1)).factorial) f - (T ^ (Nm f k).factorial) f ∈ V k` using `fun f k => hJ f k _ _ (le_trans (hNmJ f k) (hNmmono f k)) (hNmJ f k)`. Establish `hlim : ∀ f, ∃ L, ∀ k, L - (T ^ (Nm f k).factorial) f ∈ V k` using `fun f => hcomp (fun k => (T ^ (Nm f k).factorial) f) (hseq f)`. Use `choose L hL using hlim`.

Set `P : M → M → Prop` to `fun f x => ∀ k, ∃ J : ℕ, ∀ j, J ≤ j → (T ^ j.factorial) f - x ∈ V k`. Establish `hPL : ∀ f, P f (L f)`. Introduce `f k`. Use `⟨Nm f k, fun j hj => ?_⟩` and prove the remaining obligations. Establish `h1` using `hJ f k j (Nm f k) (le_trans (hNmJ f k) hj) (hNmJ f k)`.

Establish `hs` using `(V k).sub_mem h1 (hL f k)`. Rewrite `hs` using `[sub_sub_sub_cancel_right]`. Then use the resulting hypothesis. Establish `huniq : ∀ f x y, P f x → P f y → x = y`. Introduce `f x y hx hy`. Establish `hxy : x - y = 0`.

Apply `hsep` to reduce the goal to its premises. Introduce `k`. Take `⟨J1, h1⟩` from `hx k`. Take `⟨J2, h2⟩` from `hy k`. Establish `hs` using `(V k).sub_mem (h2 (max J1 J2) (le_max_right _ _)) (h1 (max J1 J2) (le_max_left _ _))`.

Rewrite `hs` using `[sub_sub_sub_cancel_left]`. Then use the resulting hypothesis. Conclude with `sub_eq_zero.mp hxy`. Establish `hPadd : ∀ f g x y, P f x → P g y → P (f + g) (x + y)`. Introduce `f g x y hx hy k`. Take `⟨J1, h1⟩` from `hx k`.

Take `⟨J2, h2⟩` from `hy k`. Use `⟨max J1 J2, fun j hj => ?_⟩` and prove the remaining obligations. Establish `hs` using `(V k).add_mem (h1 j (le_trans (le_max_left _ _) hj)) (h2 j (le_trans (le_max_right _ _) hj))`. Rewrite using `[map_add]`. Use `hs using 1` and compare the differences between its conclusion and the goal.

Normalize the expressions using the abelian group laws. Establish `hPsmul : ∀ (c : A) f x, P f x → P (c • f) (c • x)`. Introduce `c f x hx k`. Take `⟨J1, h1⟩` from `hx k`. Use `⟨J1, fun j hj => ?_⟩` and prove the remaining obligations.

Establish `hs` using `(V k).smul_mem c (h1 j hj)`. Rewrite `hs` using `[smul_sub, ← map_smul]`. Then use the resulting hypothesis. Set `e : Module.End A M` to `{ toFun := L map_add' := fun f g => huniq (f + g) _ _ (hPL _) (hPadd f g _ _ (hPL f) (hPL g)) map_smul' := fun c f => huniq (c • f) _ _ (hPL _) (hPsmul c f _ (hPL f)) }`. Use `⟨e, fun f k => ⟨hPL f k, ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Take `⟨a, p, h⟩` from `hper f k`.

Take `⟨J1, h1⟩` from `hPL f k`. Use `⟨p, ?_⟩` and prove the remaining obligations. Use `show (T ^ (p + 1)) (L f) - L f ∈ V k`. Take `⟨j, hjdef⟩ : ∃ j, j = max J1 a` from `⟨_, rfl⟩`. Establish `hja : a ≤ j.factorial` using `le_trans (by omega) (Nat.self_le_factorial _)`.

Establish `hA` using `h1 j (by omega)`. Establish `hB` using `UpperTheory.periodic_difference_shift (V k) T (hT k) f a (p + 1) h j.factorial hja`. Establish `hC` using `UpperTheory.pow_preserves_submodule (V k) T (hT k) (p + 1) _ hA`. Establish `eq : (T ^ (p + 1)) ((T ^ j.factorial) f) = (T ^ (j.factorial + (p + 1))) f`. Rewrite using `[add_comm j.factorial (p + 1), pow_add T (p + 1) j.factorial, Module.End.mul_apply]`.

Establish `hsum` using `(V k).add_mem ((V k).add_mem ((V k).neg_mem hC) hB) hA`. Rewrite `hsum` using `[map_sub, eq]`. Use `hsum using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws. Introduce `hf`.

Take `⟨J1, h1⟩` from `hPL f k`. Establish `hA` using `h1 J1 le_rfl`. Establish `hB` using `UpperTheory.pow_preserves_submodule (V k) T (hT k) J1.factorial f hf`. Use `show L f ∈ V k`. Establish `hs` using `(V k).sub_mem hB hA`.

Rewrite `hs` using `[sub_sub_cancel]`. Then use the resulting hypothesis. Introduce and unpack `⟨n, hn⟩`. Establish `h0 : (T ^ (0 + (n + 1))) f - (T ^ 0) f ∈ V k` using `by simpa using hn`. Take `⟨J1, h1⟩` from `hPL f k`. Take `⟨N, hN⟩ : ∃ N, N = max J1 (n + 1)` from `⟨_, rfl⟩`.

Take `⟨c, hc⟩` from `Nat.dvd_factorial (Nat.succ_pos n) (show n + 1 ≤ N by omega)`. Establish `hB` using `UpperTheory.periodic_difference_mul_period (V k) T (hT k) f 0 (n + 1) h0 0 le_rfl c`. Rewrite `hB` using `[zero_add, pow_zero, ← hc]`. Establish `hA` using `h1 N (by omega)`. Use `show L f - f ∈ V k`.

Establish `hs` using `(V k).sub_mem hB hA`. Rewrite `hs` using `[sub_sub_sub_cancel_left]`. Simplify using `using hs`.
-/
theorem UpperTheory.exists_ordinaryProjector_of_eventually_periodic :
    ∀ (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (V : ℕ → Submodule A M) (T : Module.End A M), Antitone V → (∀ k, ∀ f ∈ V k, T f ∈ V k) → (∀ f, (∀ k, f ∈ V k) → f = 0) → (∀ a : ℕ → M, (∀ k, a (k + 1) - a k ∈ V k) → ∃ L, ∀ k, L - a k ∈ V k) → (∀ f k, ∃ a p : ℕ, (T ^ (a + (p + 1))) f - (T ^ a) f ∈ V k) → ∃ e : Module.End A M, ∀ f k, (∃ J : ℕ, ∀ j, J ≤ j → (T ^ j.factorial) f - e f ∈ V k) ∧ (∃ n : ℕ, (T ^ (n + 1)) (e f) - e f ∈ V k) ∧ (f ∈ V k → e f ∈ V k) ∧ ((∃ n : ℕ, (T ^ (n + 1)) f - f ∈ V k) → e f - f ∈ V k) := by
  intro A M _ _ _ V T hV hT hsep hcomp hper
  have hJ : ∀ f k, ∃ J : ℕ, ∀ i j, J ≤ i → J ≤ j →
      (T ^ i.factorial) f - (T ^ j.factorial) f ∈ V k := by
    intro f k
    obtain ⟨a, p, h⟩ := hper f k
    exact UpperTheory.factorial_powers_cauchy (V k) T (hT k) f a p h
  choose J hJ using hJ
  let Nm : M → ℕ → ℕ := fun f k => ∑ i ∈ Finset.range (k + 1), J f i
  have hNmJ : ∀ f k, J f k ≤ Nm f k := fun f k =>
    Finset.single_le_sum (f := J f) (fun _ _ => Nat.zero_le _) (Finset.self_mem_range_succ k)
  have hNmmono : ∀ f k, Nm f k ≤ Nm f (k + 1) := fun f k => by
    simp only [Nm]
    rw [Finset.sum_range_succ _ (k + 1)]
    omega
  have hseq : ∀ f k, (T ^ (Nm f (k + 1)).factorial) f - (T ^ (Nm f k).factorial) f ∈ V k :=
    fun f k => hJ f k _ _ (le_trans (hNmJ f k) (hNmmono f k)) (hNmJ f k)
  have hlim : ∀ f, ∃ L, ∀ k, L - (T ^ (Nm f k).factorial) f ∈ V k := fun f =>
    hcomp (fun k => (T ^ (Nm f k).factorial) f) (hseq f)
  choose L hL using hlim
  let P : M → M → Prop := fun f x => ∀ k, ∃ J : ℕ, ∀ j, J ≤ j → (T ^ j.factorial) f - x ∈ V k
  have hPL : ∀ f, P f (L f) := by
    intro f k
    refine ⟨Nm f k, fun j hj => ?_⟩
    have h1 := hJ f k j (Nm f k) (le_trans (hNmJ f k) hj) (hNmJ f k)
    have hs := (V k).sub_mem h1 (hL f k)
    rwa [sub_sub_sub_cancel_right] at hs
  have huniq : ∀ f x y, P f x → P f y → x = y := by
    intro f x y hx hy
    have hxy : x - y = 0 := by
      apply hsep
      intro k
      obtain ⟨J1, h1⟩ := hx k
      obtain ⟨J2, h2⟩ := hy k
      have hs := (V k).sub_mem (h2 (max J1 J2) (le_max_right _ _)) (h1 (max J1 J2) (le_max_left _ _))
      rwa [sub_sub_sub_cancel_left] at hs
    exact sub_eq_zero.mp hxy
  have hPadd : ∀ f g x y, P f x → P g y → P (f + g) (x + y) := by
    intro f g x y hx hy k
    obtain ⟨J1, h1⟩ := hx k
    obtain ⟨J2, h2⟩ := hy k
    refine ⟨max J1 J2, fun j hj => ?_⟩
    have hs := (V k).add_mem (h1 j (le_trans (le_max_left _ _) hj))
      (h2 j (le_trans (le_max_right _ _) hj))
    rw [map_add]
    convert hs using 1
    abel
  have hPsmul : ∀ (c : A) f x, P f x → P (c • f) (c • x) := by
    intro c f x hx k
    obtain ⟨J1, h1⟩ := hx k
    refine ⟨J1, fun j hj => ?_⟩
    have hs := (V k).smul_mem c (h1 j hj)
    rwa [smul_sub, ← map_smul] at hs
  let e : Module.End A M :=
    { toFun := L
      map_add' := fun f g => huniq (f + g) _ _ (hPL _) (hPadd f g _ _ (hPL f) (hPL g))
      map_smul' := fun c f => huniq (c • f) _ _ (hPL _) (hPsmul c f _ (hPL f)) }
  refine ⟨e, fun f k => ⟨hPL f k, ?_, ?_, ?_⟩⟩
  · obtain ⟨a, p, h⟩ := hper f k
    obtain ⟨J1, h1⟩ := hPL f k
    refine ⟨p, ?_⟩
    show (T ^ (p + 1)) (L f) - L f ∈ V k
    obtain ⟨j, hjdef⟩ : ∃ j, j = max J1 a := ⟨_, rfl⟩
    have hja : a ≤ j.factorial := le_trans (by omega) (Nat.self_le_factorial _)
    have hA := h1 j (by omega)
    have hB := UpperTheory.periodic_difference_shift (V k) T (hT k) f a (p + 1) h j.factorial hja
    have hC := UpperTheory.pow_preserves_submodule (V k) T (hT k) (p + 1) _ hA
    have eq : (T ^ (p + 1)) ((T ^ j.factorial) f) = (T ^ (j.factorial + (p + 1))) f := by
      rw [add_comm j.factorial (p + 1), pow_add T (p + 1) j.factorial, Module.End.mul_apply]
    have hsum := (V k).add_mem ((V k).add_mem ((V k).neg_mem hC) hB) hA
    rw [map_sub, eq] at hsum
    convert hsum using 1
    abel
  · intro hf
    obtain ⟨J1, h1⟩ := hPL f k
    have hA := h1 J1 le_rfl
    have hB := UpperTheory.pow_preserves_submodule (V k) T (hT k) J1.factorial f hf
    show L f ∈ V k
    have hs := (V k).sub_mem hB hA
    rwa [sub_sub_cancel] at hs
  · rintro ⟨n, hn⟩
    have h0 : (T ^ (0 + (n + 1))) f - (T ^ 0) f ∈ V k := by simpa using hn
    obtain ⟨J1, h1⟩ := hPL f k
    obtain ⟨N, hN⟩ : ∃ N, N = max J1 (n + 1) := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.succ_pos n) (show n + 1 ≤ N by omega)
    have hB := UpperTheory.periodic_difference_mul_period (V k) T (hT k) f 0 (n + 1) h0 0 le_rfl c
    rw [zero_add, pow_zero, ← hc] at hB
    have hA := h1 N (by omega)
    show L f - f ∈ V k
    have hs := (V k).sub_mem hB hA
    rw [sub_sub_sub_cancel_left] at hs
    simpa using hs
