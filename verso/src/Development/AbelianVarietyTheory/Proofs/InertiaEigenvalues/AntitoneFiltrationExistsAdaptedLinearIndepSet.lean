import Mathlib

namespace GlobalTheory

open Submodule

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Use `⟨∅, fun _ => hi, linearIndepOn_empty L id, fun x hx => hx.elim, fun a ha => ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_empty_iff_false, false_and, Set.ofPred_false, Submodule.span_empty]`. Rewrite using `[eq_bot_iff, ← hhi]`.

Conclude with `hA (by simpa using ha)`. Consider the case `succ n ih`. Take `⟨s, k, hs, hk, hspan⟩` from `ih`. Establish `hsA : s ⊆ A (hi - (n + 1 : ℕ))`. Introduce `x hx`.

Establish `hx' : x ∈ A (hi - n)`. Rewrite using `[hspan _ le_rfl]`. Conclude with `Submodule.subset_span ⟨hx, hk x hx⟩`. Conclude with `hA (by push_cast; omega) hx'`. Take `⟨t, htA, hst, hAt, ht⟩` from `exists_linearIndepOn_id_extension hs hsA`.

Establish `hkt : ∀ x ∈ t, hi - ((n + 1 : ℕ) : ℤ) ≤ (if x ∈ s then k x else hi - (n + 1 : ℕ))`. Introduce `x _`. Use `split_ifs with h`. Use `hk x h` as an intermediate fact. Move the coercions through the operations in `at this ⊢`.

Use linear arithmetic over natural numbers and integers. Conclude with `le_rfl`. Use `⟨t, fun x => if x ∈ s then k x else hi - (n + 1 : ℕ), ht, hkt, fun a ha => ?_⟩` and prove the remaining obligations. Break down `eq_or_lt_of_le ha with h | h` into its components or cases. Substitute `h` using the available equality.

Establish `hset : {x | x ∈ t ∧ hi - ((n + 1 : ℕ) : ℤ) ≤ (if x ∈ s then k x else hi - (n + 1 : ℕ))} = t`. Use extensionality with `x`. Conclude with `⟨fun hx => hx.1, fun hx => ⟨hx, hkt x hx⟩⟩`. Rewrite using `[hset]`. Conclude with `le_antisymm (fun x hx => hAt hx) (Submodule.span_le.2 htA)`.

Establish `ha' : hi - (n : ℤ) ≤ a`. Move the coercions through the operations in `at h`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hspan a ha']`. Use `congr 1`.

Use extensionality with `x`. Simplify using `only [Set.mem_ofPred_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx, hkx⟩`. Conclude with `⟨hst hx, by rw [if_pos hx]; exact hkx⟩`.

Introduce and unpack `⟨hx, hkx⟩ split_ifs at hkx with hxs`. Conclude with `⟨hxs, hkx⟩`. Move the coercions through the operations in `at h hkx`. Use linear arithmetic over natural numbers and integers.
-/
theorem antitone_filtration_exists_adapted_linearIndep_set {L M : Type} [Field L] [AddCommGroup M] [Module L M]
    (A : ℤ → Submodule L M) (hA : Antitone A) (hi : ℤ) (hhi : A hi = ⊥) (n : ℕ) :
    ∃ (s : Set M) (k : M → ℤ), LinearIndepOn L id s ∧ (∀ x ∈ s, hi - n ≤ k x) ∧
      ∀ a, hi - n ≤ a → A a = span L {x | x ∈ s ∧ a ≤ k x} := by
  classical
  induction n with
  | zero =>
    refine ⟨∅, fun _ => hi, linearIndepOn_empty L id, fun x hx => hx.elim, fun a ha => ?_⟩
    simp only [Set.mem_empty_iff_false, false_and, Set.ofPred_false, Submodule.span_empty]
    rw [eq_bot_iff, ← hhi]
    exact hA (by simpa using ha)
  | succ n ih =>
    obtain ⟨s, k, hs, hk, hspan⟩ := ih
    have hsA : s ⊆ A (hi - (n + 1 : ℕ)) := by
      intro x hx
      have hx' : x ∈ A (hi - n) := by
        rw [hspan _ le_rfl]
        exact Submodule.subset_span ⟨hx, hk x hx⟩
      exact hA (by push_cast; omega) hx'
    obtain ⟨t, htA, hst, hAt, ht⟩ := exists_linearIndepOn_id_extension hs hsA
    have hkt : ∀ x ∈ t, hi - ((n + 1 : ℕ) : ℤ) ≤ (if x ∈ s then k x else hi - (n + 1 : ℕ)) := by
      intro x _
      split_ifs with h
      · have := hk x h
        push_cast at this ⊢
        omega
      · exact le_rfl
    refine ⟨t, fun x => if x ∈ s then k x else hi - (n + 1 : ℕ), ht, hkt, fun a ha => ?_⟩
    rcases eq_or_lt_of_le ha with h | h
    · subst h
      have hset : {x | x ∈ t ∧ hi - ((n + 1 : ℕ) : ℤ) ≤
          (if x ∈ s then k x else hi - (n + 1 : ℕ))} = t := by
        ext x
        exact ⟨fun hx => hx.1, fun hx => ⟨hx, hkt x hx⟩⟩
      rw [hset]
      exact le_antisymm (fun x hx => hAt hx) (Submodule.span_le.2 htA)
    · have ha' : hi - (n : ℤ) ≤ a := by
        push_cast at h
        omega
      rw [hspan a ha']
      congr 1
      ext x
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hx, hkx⟩
        exact ⟨hst hx, by rw [if_pos hx]; exact hkx⟩
      · rintro ⟨hx, hkx⟩
        split_ifs at hkx with hxs
        · exact ⟨hxs, hkx⟩
        · push_cast at h hkx
          omega

/- English proof (translation)
Establish `hle : ∀ a, A a ≤ ⨆ b, A b` using `fun a => le_iSup A a`. Establish `hfa : ∀ a, FiniteDimensional L (A a)` using `fun a => Submodule.finiteDimensional_of_le (hle a)`. Choose the witnesses or unpack the hypotheses as in `⟨a0, ha0⟩ : ∃ a0, ∀ a, Module.finrank L (A a0) ≤ Module.finrank L (A a) := by`. Establish `hex : ∃ m, ∃ a, Module.finrank L (A a) = m` using `⟨_, 0, rfl⟩`. Take `⟨a0, h0⟩` from `Nat.find_spec hex`.

Use `⟨a0, fun a => ?_⟩` and prove the remaining obligations. Establish `h` using `Nat.find_min' hex ⟨a, rfl⟩`. Rewrite `h` using `[← h0]`. Conclude with `h`. Establish `hbot : A a0 = ⊥`.

Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Rewrite using `[Submodule.mem_bot]`. Apply `hsep` to reduce the goal to its premises. Introduce `a`.

Break down `le_total a a0 with h | h` into its components or cases. Conclude with `hA h hx`. Rewrite using `[Submodule.eq_of_le_of_finrank_le (hA h) (ha0 a)]`. Conclude with `hx`. Choose the witnesses or unpack the hypotheses as in `⟨a1, ha1⟩ : ∃ a1, ∀ a, Module.finrank L (A a) ≤ Module.finrank L (A a1) := by`.

Establish `hex : ∃ m, ∃ a, Module.finrank L ↥(⨆ b, A b) - Module.finrank L (A a) = m` using `⟨_, 0, rfl⟩`. Take `⟨a1, h1⟩` from `Nat.find_spec hex`. Use `⟨a1, fun a => ?_⟩` and prove the remaining obligations. Establish `h2` using `Nat.find_min' hex ⟨a, rfl⟩`. Rewrite `h2` using `[← h1]`.

Establish `h3` using `Submodule.finrank_mono (hle a)`. Establish `h4` using `Submodule.finrank_mono (hle a1)`. Use linear arithmetic over natural numbers and integers. Establish `htop : ⨆ b, A b = A a1`. Use `le_antisymm (iSup_le fun a => ?_) (hle a1)` and prove the remaining obligations.

Break down `le_total a1 a with h | h` into its components or cases. Conclude with `hA h`. Conclude with `(Submodule.eq_of_le_of_finrank_le (hA h) (ha1 a)).symm.le`. Take `⟨n, hn⟩ : ∃ n : ℕ, a0 - n ≤ a1` from `⟨(a0 - a1).toNat, by omega⟩`. Take `⟨s, k, hs, hk, hspan⟩` from `antitone_filtration_exists_adapted_linearIndep_set A hA a0 hbot n`.

Establish `hlow : ∀ a, a ≤ a0 - n → A a = A (a0 - n)`. Introduce `a ha`. Use `le_antisymm ?_ (hA ha)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `hsU : ∀ x ∈ s, x ∈ (⨆ b, A b : Submodule L M)`.

Introduce `x hx`. Establish `hx' : x ∈ A (a0 - n)`. Rewrite using `[hspan _ le_rfl]`. Conclude with `Submodule.subset_span ⟨hx, hk x hx⟩`. Conclude with `hle _ hx'`.

Establish `hli : LinearIndependent L (fun x : s => (⟨x, hsU x x.2⟩ : (⨆ b, A b : Submodule L M)))` using `LinearIndependent.of_comp (⨆ b, A b).subtype hs`. Establish `hfin : s.Finite` using `Set.finite_coe_iff.1 hli.finite`. Establish `_` using `hfin.fintype`. Set `e : s ≃ Fin (Fintype.card s)` to `Fintype.equivFin s`. Use `⟨Fintype.card s, fun i => (e.symm i : M), fun i => k (e.symm i), LinearIndependent.comp hs e.symm e.symm.injective, fun a => ?_⟩` and prove the remaining obligations.

Use `show A a = Submodule.span L ((fun i => (e.symm i : M)) '' {i | a ≤ k (e.symm i)})`. Establish `himg : (fun i => (e.symm i : M)) '' {i | a ≤ k (e.symm i)} = {x | x ∈ s ∧ a ≤ k x}`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, hi, rfl⟩`.

Conclude with `⟨(e.symm i).2, hi⟩`. Introduce and unpack `⟨hx, hkx⟩`. Conclude with `⟨e ⟨x, hx⟩, by simpa using hkx, by simp⟩`. Rewrite using `[himg]`. Break down `le_or_gt (a0 - n) a with h | h` into its components or cases.

Conclude with `hspan a h`. Rewrite using `[hlow a h.le, hspan _ le_rfl]`. Use `congr 1`. Use extensionality with `x`. Simplify using `only [Set.mem_ofPred_eq]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx, -⟩`. Conclude with `⟨hx, by have := hk x hx; omega⟩`. Introduce and unpack `⟨hx, -⟩`. Conclude with `⟨hx, hk x hx⟩`.
-/
theorem filtration_adapted_basis {L M : Type} [Field L] [AddCommGroup M] [Module L M]
    (A : ℤ → Submodule L M) (hA : Antitone A) (hfd : FiniteDimensional L ↥(⨆ a, A a))
    (hsep : ∀ x, (∀ a, x ∈ A a) → x = 0) :
    ∃ (m : ℕ) (d : Fin m → M) (k : Fin m → ℤ), LinearIndependent L d ∧
      ∀ a, A a = Submodule.span L (d '' {i | a ≤ k i}) := by
  classical
  have hle : ∀ a, A a ≤ ⨆ b, A b := fun a => le_iSup A a
  have hfa : ∀ a, FiniteDimensional L (A a) := fun a => Submodule.finiteDimensional_of_le (hle a)
  obtain ⟨a0, ha0⟩ : ∃ a0, ∀ a, Module.finrank L (A a0) ≤ Module.finrank L (A a) := by
    have hex : ∃ m, ∃ a, Module.finrank L (A a) = m := ⟨_, 0, rfl⟩
    obtain ⟨a0, h0⟩ := Nat.find_spec hex
    refine ⟨a0, fun a => ?_⟩
    have h := Nat.find_min' hex ⟨a, rfl⟩
    rw [← h0] at h
    exact h
  have hbot : A a0 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    apply hsep
    intro a
    rcases le_total a a0 with h | h
    · exact hA h hx
    · rw [Submodule.eq_of_le_of_finrank_le (hA h) (ha0 a)]
      exact hx
  obtain ⟨a1, ha1⟩ : ∃ a1, ∀ a, Module.finrank L (A a) ≤ Module.finrank L (A a1) := by
    have hex : ∃ m, ∃ a, Module.finrank L ↥(⨆ b, A b) - Module.finrank L (A a) = m := ⟨_, 0, rfl⟩
    obtain ⟨a1, h1⟩ := Nat.find_spec hex
    refine ⟨a1, fun a => ?_⟩
    have h2 := Nat.find_min' hex ⟨a, rfl⟩
    rw [← h1] at h2
    have h3 := Submodule.finrank_mono (hle a)
    have h4 := Submodule.finrank_mono (hle a1)
    omega
  have htop : ⨆ b, A b = A a1 := by
    refine le_antisymm (iSup_le fun a => ?_) (hle a1)
    rcases le_total a1 a with h | h
    · exact hA h
    · exact (Submodule.eq_of_le_of_finrank_le (hA h) (ha1 a)).symm.le
  obtain ⟨n, hn⟩ : ∃ n : ℕ, a0 - n ≤ a1 := ⟨(a0 - a1).toNat, by omega⟩
  obtain ⟨s, k, hs, hk, hspan⟩ := antitone_filtration_exists_adapted_linearIndep_set A hA a0 hbot n
  have hlow : ∀ a, a ≤ a0 - n → A a = A (a0 - n) := by
    intro a ha
    refine le_antisymm ?_ (hA ha)
    calc A a ≤ ⨆ c, A c := hle a
      _ = A a1 := htop
      _ ≤ A (a0 - n) := hA hn
  have hsU : ∀ x ∈ s, x ∈ (⨆ b, A b : Submodule L M) := by
    intro x hx
    have hx' : x ∈ A (a0 - n) := by
      rw [hspan _ le_rfl]
      exact Submodule.subset_span ⟨hx, hk x hx⟩
    exact hle _ hx'
  have hli : LinearIndependent L (fun x : s => (⟨x, hsU x x.2⟩ : (⨆ b, A b : Submodule L M))) :=
    LinearIndependent.of_comp (⨆ b, A b).subtype hs
  have hfin : s.Finite := Set.finite_coe_iff.1 hli.finite
  have _ := hfin.fintype
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  refine ⟨Fintype.card s, fun i => (e.symm i : M), fun i => k (e.symm i),
    LinearIndependent.comp hs e.symm e.symm.injective, fun a => ?_⟩
  show A a = Submodule.span L ((fun i => (e.symm i : M)) '' {i | a ≤ k (e.symm i)})
  have himg : (fun i => (e.symm i : M)) '' {i | a ≤ k (e.symm i)} = {x | x ∈ s ∧ a ≤ k x} := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(e.symm i).2, hi⟩
    · rintro ⟨hx, hkx⟩
      exact ⟨e ⟨x, hx⟩, by simpa using hkx, by simp⟩
  rw [himg]
  rcases le_or_gt (a0 - n) a with h | h
  · exact hspan a h
  · rw [hlow a h.le, hspan _ le_rfl]
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hx, -⟩
      exact ⟨hx, by have := hk x hx; omega⟩
    · rintro ⟨hx, -⟩
      exact ⟨hx, hk x hx⟩

end GlobalTheory
