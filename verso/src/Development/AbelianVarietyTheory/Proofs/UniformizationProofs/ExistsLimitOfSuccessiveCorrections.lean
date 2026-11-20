import Mathlib

namespace GlobalTheory.Unif

/- English proof (translation)
Introduce `e x hx`. Establish `hanti : Antitone K` using `antitone_nat_of_succ_le hK`. Establish `hmem : ∀ (n : ℕ) (z : M), z ∈ (Ideal.span {a} ^ n • ⊤ : Submodule R M) ↔ ∃ y : M, z = a ^ n • y`. Introduce `n z`. Rewrite using `[Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, -, h⟩`. Conclude with `⟨y, h.symm⟩`. Introduce and unpack `⟨y, h⟩`. Conclude with `⟨y, trivial, h.symm⟩`.

Use `choose y hy using hs`. Set `s : (n : ℕ) → K (e + n)` to `fun n => Nat.rec (motive := fun n => K (e + n)) ⟨x, hx⟩ (fun n z => ⟨z.1 - a ^ (e + n + 1) • y (e + n) z.1 z.2, hy _ _ _⟩) n`. Establish `hs0 : (s 0 : M) = x` using `rfl`. Establish `hsn : ∀ n, (s (n + 1) : M) = s n - a ^ (e + n + 1) • y (e + n) (s n).1 (s n).2` using `fun n => rfl`. Establish `hd : ∀ m n, m ≤ n → ∃ z : M, (s m : M) - s n = a ^ (e + m + 1) • z`.

Introduce `m n hmn`. Proceed by induction on `n, hmn using Nat.le_induction with`. Consider the case `base => exact ⟨0, by simp⟩`. Consider the case `succ n hmn ih`. Take `⟨z, hz⟩` from `ih`.

Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hmn`. Use `⟨z + a ^ k • y (e + (m + k)) (s (m + k)).1 (s (m + k)).2, ?_⟩` and prove the remaining obligations. Rewrite using `[hsn, smul_add, ← hz, smul_smul, ← pow_add, show e + m + 1 + k = e + (m + k) + 1 by ring]`. Normalize the expressions using the abelian group laws. Take `⟨L, hL⟩` from `IsPrecomplete.prec (I := Ideal.span {a}) (M := M) inferInstance (f := fun n => (s n : M)) (by`.

Introduce `m n hmn`. Take `⟨z, hz⟩` from `hd m n hmn`. Rewrite using `[SModEq.sub_mem, hmem]`. Use `⟨a ^ (e + 1) • z, ?_⟩` and prove the remaining obligations. Rewrite using `[hz, smul_smul, ← pow_add, show m + (e + 1) = e + m + 1 by ring])`.

Establish `hl : ∀ m, ∃ z : M, (s m : M) - L = a ^ (e + m + 1) • z`. Introduce `m`. Take `⟨z, hz⟩` from `hd m (e + m + 1) (by omega)`. Establish `h` using `hL (e + m + 1)`. Rewrite `h` using `[SModEq.sub_mem, hmem]`.

Take `⟨w, hw⟩` from `h`. Use `⟨z + w, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add, ← hz, ← hw]`. Normalize the expressions using the abelian group laws. Take `⟨z, hz⟩` from `hl 0`.

Use `⟨L, z, fun m => ?_, hz⟩` and prove the remaining obligations. Take `⟨w, hw⟩` from `hl m`. Establish `hLe : L = (s m : M) - a ^ (e + m + 1) • w` using `by rw [← hw]; abel`. Apply `hanti (show m ≤ e + m by omega)` to reduce the goal to its premises. Rewrite using `[hLe]`.

Conclude with `Submodule.sub_mem _ (s m).2 (ha _ _)`.
-/
theorem exists_limit_of_successive_corrections (R : Type) [CommRing R] (a : R) (M : Type)
    [AddCommGroup M] [Module R M] [IsPrecomplete (Ideal.span {a}) M] (K : ℕ → Submodule R M)
    (hK : ∀ e, K (e + 1) ≤ K e) (ha : ∀ (e : ℕ) (x : M), a ^ (e + 1) • x ∈ K e)
    (hs : ∀ e, ∀ x ∈ K e, ∃ y : M, x - a ^ (e + 1) • y ∈ K (e + 1)) :
    ∀ e, ∀ x ∈ K e, ∃ x' y : M, (∀ e', x' ∈ K e') ∧ x - x' = a ^ (e + 1) • y := by
  intro e x hx
  have hanti : Antitone K := antitone_nat_of_succ_le hK
  have hmem : ∀ (n : ℕ) (z : M), z ∈ (Ideal.span {a} ^ n • ⊤ : Submodule R M) ↔
      ∃ y : M, z = a ^ n • y := by
    intro n z
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, -, h⟩
      exact ⟨y, h.symm⟩
    · rintro ⟨y, h⟩
      exact ⟨y, trivial, h.symm⟩
  choose y hy using hs
  let s : (n : ℕ) → K (e + n) := fun n =>
    Nat.rec (motive := fun n => K (e + n)) ⟨x, hx⟩
      (fun n z => ⟨z.1 - a ^ (e + n + 1) • y (e + n) z.1 z.2, hy _ _ _⟩) n
  have hs0 : (s 0 : M) = x := rfl
  have hsn : ∀ n, (s (n + 1) : M) = s n - a ^ (e + n + 1) • y (e + n) (s n).1 (s n).2 :=
    fun n => rfl
  have hd : ∀ m n, m ≤ n → ∃ z : M, (s m : M) - s n = a ^ (e + m + 1) • z := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact ⟨0, by simp⟩
    | succ n hmn ih =>
      obtain ⟨z, hz⟩ := ih
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      refine ⟨z + a ^ k • y (e + (m + k)) (s (m + k)).1 (s (m + k)).2, ?_⟩
      rw [hsn, smul_add, ← hz, smul_smul, ← pow_add,
        show e + m + 1 + k = e + (m + k) + 1 by ring]
      abel
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {a}) (M := M) inferInstance
    (f := fun n => (s n : M)) (by
      intro m n hmn
      obtain ⟨z, hz⟩ := hd m n hmn
      rw [SModEq.sub_mem, hmem]
      refine ⟨a ^ (e + 1) • z, ?_⟩
      rw [hz, smul_smul, ← pow_add, show m + (e + 1) = e + m + 1 by ring])
  have hl : ∀ m, ∃ z : M, (s m : M) - L = a ^ (e + m + 1) • z := by
    intro m
    obtain ⟨z, hz⟩ := hd m (e + m + 1) (by omega)
    have h := hL (e + m + 1)
    rw [SModEq.sub_mem, hmem] at h
    obtain ⟨w, hw⟩ := h
    refine ⟨z + w, ?_⟩
    rw [smul_add, ← hz, ← hw]
    abel
  obtain ⟨z, hz⟩ := hl 0
  refine ⟨L, z, fun m => ?_, hz⟩
  obtain ⟨w, hw⟩ := hl m
  have hLe : L = (s m : M) - a ^ (e + m + 1) • w := by rw [← hw]; abel
  apply hanti (show m ≤ e + m by omega)
  rw [hLe]
  exact Submodule.sub_mem _ (s m).2 (ha _ _)

end GlobalTheory.Unif
