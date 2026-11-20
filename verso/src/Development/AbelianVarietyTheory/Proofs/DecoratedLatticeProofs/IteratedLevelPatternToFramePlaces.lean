import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

namespace GlobalTheory.PatPlaces

/- English proof (translation)
Distinguish the cases in `h1 : p < κ`. Conclude with `⟨.inl (.inl ⟨p, h1⟩), rfl⟩`. Distinguish the cases in `h2 : p < κ + l`. Conclude with `⟨.inl (.inr ⟨p - κ, by omega⟩), by simp only [zPos]; omega⟩`. Establish `hτ : 0 < τ`.

Break down `Nat.eq_zero_or_pos τ with h | h` into its components or cases. Substitute `h` using the available equality. Simplify using `at hp`. Use linear arithmetic over natural numbers and integers. Conclude with `h`.

Establish `hq : p - (κ + l) < τ * j` using `by rw [mul_comm]; omega`. Use `⟨.inr (⟨(p - (κ + l)) / τ, Nat.div_lt_of_lt_mul hq⟩, ⟨(p - (κ + l)) % τ, Nat.mod_lt _ hτ⟩), ?_⟩` and prove the remaining obligations. Use `Nat.div_add_mod' (p - (κ + l)) τ` as an intermediate fact. Simplify using `only [zPos]`. Use linear arithmetic over natural numbers and integers.
-/
theorem zPos_surj {κ τ l j p : ℕ} (hp : p < κ + l + j * τ) :
    ∃ a : Ix (Fin κ ⊕ Fin l) (Fin τ) j, zPos a = p := by
  by_cases h1 : p < κ
  · exact ⟨.inl (.inl ⟨p, h1⟩), rfl⟩
  by_cases h2 : p < κ + l
  · exact ⟨.inl (.inr ⟨p - κ, by omega⟩), by simp only [zPos]; omega⟩
  · have hτ : 0 < τ := by
      rcases Nat.eq_zero_or_pos τ with h | h
      · subst h; simp at hp; omega
      · exact h
    have hq : p - (κ + l) < τ * j := by rw [mul_comm]; omega
    refine ⟨.inr (⟨(p - (κ + l)) / τ, Nat.div_lt_of_lt_mul hq⟩, ⟨(p - (κ + l)) % τ, Nat.mod_lt _ hτ⟩), ?_⟩
    have := Nat.div_add_mod' (p - (κ + l)) τ
    simp only [zPos]; omega

/- English proof (translation)
Apply the tactic sequence `unfold symIdx; split_ifs <;> omega`.
-/
theorem symIdx_cases (κ ρ i : ℕ) :
    (i < κ ∧ symIdx κ ρ i = i + ρ) ∨ (κ ≤ i ∧ i < κ + ρ ∧ symIdx κ ρ i = i - κ) ∨ (κ + ρ ≤ i ∧ symIdx κ ρ i = i) := by
  unfold symIdx; split_ifs <;> omega

/- English proof (translation)
Establish `: r + i * τ + u - r = u + τ * i` using `by rw [mul_comm]; omega`. Rewrite using `[this, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hu, zero_add]`.
-/
theorem block_div {r τ i u : ℕ} (hu : u < τ) : (r + i * τ + u - r) / τ = i := by
  have : r + i * τ + u - r = u + τ * i := by rw [mul_comm]; omega
  rw [this, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hu, zero_add]

/- English proof (translation)
Introduce `hR`. Establish `key : ∀ a b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j, a ≠ b → ¬ FreeIx ρ a b → R (zPos a) (zPos b) = 0` using `fun a b hab h => by rw [hR a b h, if_neg hab]`. Use `⟨fun p' hp' => ⟨?_, fun p hp hne hc => ?_⟩, fun p p' h1 h2 h3 h4 => ?_⟩` and prove the remaining obligations. Take `⟨b, rfl⟩` from `zPos_surj (κ := κ) (τ := τ) (l := s + 1) (j := j) (p := p') (by omega)`. Rewrite using `[hR b b ?_, if_pos rfl]`.

Break down `b with (i | i) | ⟨i, u⟩` into its components or cases. Simplify using `[FreeIx, FreeTop]`. Simplify using `[FreeIx, FreeTop]`. Simplify using `only [zPos] at hp'`. Use linear arithmetic over natural numbers and integers.

Take `⟨b, rfl⟩` from `zPos_surj (κ := κ) (τ := τ) (l := s + 1) (j := j) (p := p') (by omega)`. Take `⟨a, rfl⟩` from `zPos_surj (κ := κ) (τ := τ) (l := s + 1) (j := j) (p := p) (by omega)`. Use `key a b (fun h => hne (h ▸ rfl)) ?_` and prove the remaining obligations. Establish `c1` using `symIdx_cases κ ρ (zPos a)`. Establish `c2` using `symIdx_cases κ ρ (zPos b)`.

Apply the tactic sequence `rcases a with (i | i) | ⟨i, u⟩ <;> rcases b with (i' | i') | ⟨i', u'⟩ <;>`. Apply the tactic sequence `simp only [zPos, FreeIx, FreeTop, Fin.lt_def, not_lt, not_false_eq_true] at hp' hp hne hc c1 c2 ⊢ <;> omega`. Take `⟨b, rfl⟩` from `zPos_surj (κ := κ) (τ := τ) (l := s + 1) (j := j) (p := p') (by omega)`. Take `⟨a, rfl⟩` from `zPos_surj (κ := κ) (τ := τ) (l := s + 1) (j := j) (p := p) (by omega)`. Break down `b with (i' | i') | ⟨i', u'⟩` into its components or cases.

Simplify using `only [zPos] at h1`. Use linear arithmetic over natural numbers and integers. Simplify using `only [zPos] at h1`. Use linear arithmetic over natural numbers and integers. Break down `a with (i | i) | ⟨i, u⟩` into its components or cases.

Simplify using `only [zPos] at h4; rw [show (i : ℕ) - (κ + s + 1) = 0 by omega, Nat.zero_div] at h4; exact absurd h4 (Nat.not_lt_zero _)`. Simplify using `only [zPos] at h4; rw [show κ + (i : ℕ) - (κ + s + 1) = 0 by omega, Nat.zero_div] at h4; exact absurd h4 (Nat.not_lt_zero _)`. Establish `e1 : κ + (s + 1) + (i' : ℕ) * τ + u' = κ + s + 1 + (i' : ℕ) * τ + u'` using `by omega`. Establish `e2 : κ + (s + 1) + (i : ℕ) * τ + u = κ + s + 1 + (i : ℕ) * τ + u` using `by omega`. Simplify using `only [zPos] at h4`.

Rewrite `h4` using `[e1, e2, block_div u'.isLt, block_div u.isLt]`. Use `key _ _ (fun h => ?_) ?_` and prove the remaining obligations. Simplify using `only [Sum.inr.injEq, Prod.mk.injEq] at h`. Rewrite `h4` using `[h.1]`. Conclude with `lt_irrefl _ h4`.

Simplify using `only [FreeIx, Fin.le_def, not_le]`. Conclude with `h4`.
-/
theorem pattern_to_places (F : Type) [Zero F] [One F] (κ ρ s τ j : ℕ) (R : ℕ → ℕ → F) :
    (∀ (a b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j), ¬ FreeIx ρ a b → R (zPos a) (zPos b) = if a = b then 1 else 0) →
    ((∀ p', p' < κ + s + 1 → R p' p' = 1 ∧ ∀ p, p < κ + s + 1 + j * τ → p ≠ p' →
        (κ + s + 1 ≤ p ∨ symIdx κ ρ p' < symIdx κ ρ p ∨ (p' = κ + ρ ∧ p < κ)) → R p p' = 0) ∧
      (∀ p p', κ + s + 1 ≤ p' → p' < κ + s + 1 + j * τ → p < κ + s + 1 + j * τ →
        (p' - (κ + s + 1)) / τ < (p - (κ + s + 1)) / τ → R p p' = 0)) := by
  intro hR
  have key : ∀ a b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j, a ≠ b → ¬ FreeIx ρ a b → R (zPos a) (zPos b) = 0 :=
    fun a b hab h => by rw [hR a b h, if_neg hab]
  refine ⟨fun p' hp' => ⟨?_, fun p hp hne hc => ?_⟩, fun p p' h1 h2 h3 h4 => ?_⟩
  · obtain ⟨b, rfl⟩ := zPos_surj (κ := κ) (τ := τ) (l := s + 1) (j := j) (p := p') (by omega)
    rw [hR b b ?_, if_pos rfl]
    rcases b with (i | i) | ⟨i, u⟩
    · simp [FreeIx, FreeTop]
    · simp [FreeIx, FreeTop]
    · simp only [zPos] at hp'; omega
  · obtain ⟨b, rfl⟩ := zPos_surj (κ := κ) (τ := τ) (l := s + 1) (j := j) (p := p') (by omega)
    obtain ⟨a, rfl⟩ := zPos_surj (κ := κ) (τ := τ) (l := s + 1) (j := j) (p := p) (by omega)
    refine key a b (fun h => hne (h ▸ rfl)) ?_
    have c1 := symIdx_cases κ ρ (zPos a)
    have c2 := symIdx_cases κ ρ (zPos b)
    rcases a with (i | i) | ⟨i, u⟩ <;> rcases b with (i' | i') | ⟨i', u'⟩ <;>
      simp only [zPos, FreeIx, FreeTop, Fin.lt_def, not_lt, not_false_eq_true] at hp' hp hne hc c1 c2 ⊢ <;> omega
  · obtain ⟨b, rfl⟩ := zPos_surj (κ := κ) (τ := τ) (l := s + 1) (j := j) (p := p') (by omega)
    obtain ⟨a, rfl⟩ := zPos_surj (κ := κ) (τ := τ) (l := s + 1) (j := j) (p := p) (by omega)
    rcases b with (i' | i') | ⟨i', u'⟩
    · simp only [zPos] at h1; omega
    · simp only [zPos] at h1; omega
    rcases a with (i | i) | ⟨i, u⟩
    · simp only [zPos] at h4; rw [show (i : ℕ) - (κ + s + 1) = 0 by omega, Nat.zero_div] at h4; exact absurd h4 (Nat.not_lt_zero _)
    · simp only [zPos] at h4; rw [show κ + (i : ℕ) - (κ + s + 1) = 0 by omega, Nat.zero_div] at h4; exact absurd h4 (Nat.not_lt_zero _)
    have e1 : κ + (s + 1) + (i' : ℕ) * τ + u' = κ + s + 1 + (i' : ℕ) * τ + u' := by omega
    have e2 : κ + (s + 1) + (i : ℕ) * τ + u = κ + s + 1 + (i : ℕ) * τ + u := by omega
    simp only [zPos] at h4
    rw [e1, e2, block_div u'.isLt, block_div u.isLt] at h4
    refine key _ _ (fun h => ?_) ?_
    · simp only [Sum.inr.injEq, Prod.mk.injEq] at h; rw [h.1] at h4; exact lt_irrefl _ h4
    · simp only [FreeIx, Fin.le_def, not_le]; exact h4

end GlobalTheory.PatPlaces
