import Mathlib

namespace KStar.Choice

structure IsLevelPair (N a b : ℕ) : Prop where
  prime_fst : a.Prime
  prime_snd : b.Prime
  ne_two : a ≠ 2
  lt : a < b
  lt_two_mul : b < 2 * a
  not_dvd_fst : ¬ a ∣ N
  not_dvd_snd : ¬ b ∣ N

/- English proof (translation)
Assemble the required witnesses or components as `⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩`.
-/
example : IsLevelPair 1 3 5 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

noncomputable def levelFst (N : ℕ) : ℕ := sInf {a | ∃ b, IsLevelPair N a b}

noncomputable def levelSnd (N : ℕ) : ℕ := sInf {b | ∃ a, IsLevelPair N a b}

noncomputable def levelSnd' (N : ℕ) : ℕ := sInf {b | IsLevelPair N (levelFst N) b}

/- English proof (translation)
Establish `hM : max N 2 ≠ 0` using `by omega`. Take `⟨a, ha, hMa, haM⟩` from `Nat.exists_prime_lt_and_le_two_mul (max N 2) hM`. Take `⟨b, hb, hab, hba⟩` from `Nat.exists_prime_lt_and_le_two_mul a ha.ne_zero`. Establish `h1 : N ≤ max N 2` using `le_max_left _ _`. Establish `h2 : 2 ≤ max N 2` using `le_max_right _ _`.

Establish `hne : b ≠ 2 * a`. Introduce `h`. Establish `h2b : 2 ∣ b` using `⟨a, h⟩`. Use `(Nat.prime_dvd_prime_iff_eq Nat.prime_two hb).1 h2b` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use `⟨a, b, ⟨ha, hb, by omega, hab, by omega, ?_, ?_⟩, by omega⟩` and prove the remaining obligations. Introduce `h`. Use `Nat.le_of_dvd (Nat.pos_of_ne_zero hN) h` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Introduce `h`.

Use `Nat.le_of_dvd (Nat.pos_of_ne_zero hN) h` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_isLevelPair {N : ℕ} (hN : N ≠ 0) :
    ∃ a b, IsLevelPair N a b ∧ b < 4 * max N 2 := by
  have hM : max N 2 ≠ 0 := by omega
  obtain ⟨a, ha, hMa, haM⟩ := Nat.exists_prime_lt_and_le_two_mul (max N 2) hM
  obtain ⟨b, hb, hab, hba⟩ := Nat.exists_prime_lt_and_le_two_mul a ha.ne_zero
  have h1 : N ≤ max N 2 := le_max_left _ _
  have h2 : 2 ≤ max N 2 := le_max_right _ _
  have hne : b ≠ 2 * a := by
    intro h
    have h2b : 2 ∣ b := ⟨a, h⟩
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hb).1 h2b
    omega
  refine ⟨a, b, ⟨ha, hb, by omega, hab, by omega, ?_, ?_⟩, by omega⟩
  · intro h
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) h
    omega
  · intro h
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) h
    omega

/- English proof (translation)
Take `⟨a₀, b₀, h₀, hb₀⟩` from `exists_isLevelPair hN`. Establish `hfst : ∀ a b, IsLevelPair N a b → levelFst N ≤ a` using `fun a b h => Nat.sInf_le (s := {a | ∃ b, IsLevelPair N a b}) ⟨b, h⟩`. Establish `hsnd : ∀ a b, IsLevelPair N a b → levelSnd N ≤ b` using `fun a b h => Nat.sInf_le (s := {b | ∃ a, IsLevelPair N a b}) ⟨a, h⟩`. Take `⟨b₁, h₁⟩ : ∃ b, IsLevelPair N (levelFst N) b` from `Nat.sInf_mem (s := {a | ∃ b, IsLevelPair N a b}) ⟨a₀, b₀, h₀⟩`. Take `⟨a₂, h₂⟩ : ∃ a, IsLevelPair N a (levelSnd N)` from `Nat.sInf_mem (s := {b | ∃ a, IsLevelPair N a b}) ⟨b₀, a₀, h₀⟩`.

Establish `hp : IsLevelPair N (levelFst N) (levelSnd N)`. Establish `e1` using `hfst _ _ h₂`. Establish `e2` using `hsnd _ _ h₁`. Establish `e3` using `h₂.lt`. Establish `e4` using `h₁.lt_two_mul`.

Conclude with `⟨h₁.prime_fst, h₂.prime_snd, h₁.ne_two, by omega, by omega, h₁.not_dvd_fst, h₂.not_dvd_snd⟩`. Use `⟨hp, le_antisymm ?_ ?_, lt_of_le_of_lt (hsnd _ _ h₀) hb₀, fun a b h => ⟨hfst a b h, hsnd a b h⟩⟩` and prove the remaining obligations. Conclude with `Nat.sInf_le (s := {b | IsLevelPair N (levelFst N) b}) hp`. Establish `h' : IsLevelPair N (levelFst N) (levelSnd' N)` using `Nat.sInf_mem (s := {b | IsLevelPair N (levelFst N) b}) ⟨_, hp⟩`. Conclude with `hsnd _ _ h'`.
-/
theorem isLevelPair_least {N : ℕ} (hN : N ≠ 0) :
    IsLevelPair N (levelFst N) (levelSnd N) ∧ levelSnd' N = levelSnd N ∧
      levelSnd N < 4 * max N 2 ∧
      ∀ a b, IsLevelPair N a b → levelFst N ≤ a ∧ levelSnd N ≤ b := by
  obtain ⟨a₀, b₀, h₀, hb₀⟩ := exists_isLevelPair hN
  have hfst : ∀ a b, IsLevelPair N a b → levelFst N ≤ a := fun a b h =>
    Nat.sInf_le (s := {a | ∃ b, IsLevelPair N a b}) ⟨b, h⟩
  have hsnd : ∀ a b, IsLevelPair N a b → levelSnd N ≤ b := fun a b h =>
    Nat.sInf_le (s := {b | ∃ a, IsLevelPair N a b}) ⟨a, h⟩
  obtain ⟨b₁, h₁⟩ : ∃ b, IsLevelPair N (levelFst N) b :=
    Nat.sInf_mem (s := {a | ∃ b, IsLevelPair N a b}) ⟨a₀, b₀, h₀⟩
  obtain ⟨a₂, h₂⟩ : ∃ a, IsLevelPair N a (levelSnd N) :=
    Nat.sInf_mem (s := {b | ∃ a, IsLevelPair N a b}) ⟨b₀, a₀, h₀⟩
  have hp : IsLevelPair N (levelFst N) (levelSnd N) := by
    have e1 := hfst _ _ h₂
    have e2 := hsnd _ _ h₁
    have e3 := h₂.lt
    have e4 := h₁.lt_two_mul
    exact ⟨h₁.prime_fst, h₂.prime_snd, h₁.ne_two, by omega, by omega, h₁.not_dvd_fst,
      h₂.not_dvd_snd⟩
  refine ⟨hp, le_antisymm ?_ ?_, lt_of_le_of_lt (hsnd _ _ h₀) hb₀,
    fun a b h => ⟨hfst a b h, hsnd a b h⟩⟩
  · exact Nat.sInf_le (s := {b | IsLevelPair N (levelFst N) b}) hp
  · have h' : IsLevelPair N (levelFst N) (levelSnd' N) :=
      Nat.sInf_mem (s := {b | IsLevelPair N (levelFst N) b}) ⟨_, hp⟩
    exact hsnd _ _ h'

end KStar.Choice
