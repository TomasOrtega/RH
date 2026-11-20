import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.ExistsResQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.PrimeEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.BarFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Introduce `Ω _ _ _ l hl c D hD X T hOn k₀ hk hr hfix`. Take `⟨hne, -, -, -, -, -, hrb, -, -⟩` from `barFacts D hD`. Take `⟨-, -, -, -, haw⟩` from `away D hD`. Establish `hH : ∀ g : G T.F Ω, Raw.bar D.Psi (resQ T.F g) = ((X.φ (resQ T.F g) : ℤ) : ResidueField c.O)` using `fun g => (X.mem_H.1 (hOn.1 ▸ resQ_mem T.F g)).1`. Establish `hps : ∀ g : G T.F Ω, T.rb wPs g = ((X.φ (resQ T.F g) : ℤ) : ResidueField c.O)` using `fun g => by`.

Rewrite using `[hrb, hH]`. Apply the tactic sequence `rcases Int.units_eq_one_or (X.φ (resQ T.F g)) with h | h <;> rw [h] <;> cases T.pr <;> simp [wPs]`. Establish `hal : ∀ g : G T.F Ω, T.rb wAl g = Raw.bar D.ξ (resQ T.F g)` using `fun g => by`. Rewrite using `[hrb]`. Apply the tactic sequence `cases T.pr <;> simp [wAl]`.

Establish `hiff : ∀ g : G T.F Ω, T.rb wPs g = 1 ↔ X.φ (resQ T.F g) = 1` using `fun g => by`. Rewrite using `[hps]`. Apply the tactic sequence `rcases Int.units_eq_one_or (X.φ (resQ T.F g)) with h | h <;> rw [h]`. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Introduce `h'`. Conclude with `absurd (by simpa using h') hne`. Introduce `h'`. Conclude with `absurd h' (by decide)`. Establish `key : ∀ q ∈ D.S, ∀ A : ValuationSubring Ω, A.valuation (q : Ω) < 1 → ∀ g ∈ Dec (F` using `ℚ) A, Raw.bar D.Psi g = 1 → X.κ g = 1 → ∃ s : G T.F Ω, resQ T.F s = g := fun q hq A hA g hg h1 h2 => by`.

Establish `a : X.φ g = 1` using `X.hφ.split q hq A hA hg`. Establish `b : X.η g = 1` using `X.hη.split q (Finset.mem_insert_of_mem hq) A hA hg`. Establish `d : X.η' g = 1` using `X.hη'.split q (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hq)) A hA hg`. Use `exists_resQ ?_` and prove the remaining obligations. Rewrite using `[hOn.1, X.mem_H]`.

Use `⟨?_, b.trans d.symm, h2⟩` and prove the remaining obligations. Rewrite using `[h1, a]`. Simplify using the standard rewrite rules. Use `⟨fun g => ?_, fun A g hg => ?_, fun A hA g hg => ?_, ⟨k₀, hk, hr, fun p hp A hA => ?_, fun g => ?_⟩, X.ord, X.xi, fun A hA => ?_, fun A hA => ?_⟩` and prove the remaining obligations. Rewrite using `[hps]`.

Apply the tactic sequence `rcases Int.units_eq_one_or (X.φ (resQ T.F g)) with h | h <;> rw [h] <;> simp`. Establish `hg'` using `(resQ_Ine T.F A g).1 hg`. Distinguish the cases in `hA : A.valuation (X.p₃ : Ω) < 1`. Rewrite using `[hps, ← hH, Raw.bar, ((haw A X.p₃ X.hφ.prime X.hφ.nm hA).2 _ hg').1]`. Simplify using the standard rewrite rules.

Conclude with `(hiff g).2 (X.hφ.unr A hA hg')`. Conclude with `(hiff g).2 (X.hφ.split l hD.l_mem A hA ((resQ_Dec T.F A g).1 hg))`. Rewrite using `[hfix]`. Use `X.hφ.split p ?_ A hA` and prove the remaining obligations. Simplify using `only [List.mem_cons, List.not_mem_nil, or_false] at hp`.

Break down `hp with rfl | rfl` into its components or cases. Conclude with `hD.two_mem`. Conclude with `hD.l_mem`. Rewrite using `[hfix, MonoidHom.mem_ker]`. Conclude with `hiff g`.

Take `⟨g, hg, h1, h2, h3⟩` from `X.bigL A hA`. Take `⟨s, rfl⟩` from `key l hD.l_mem A hA g hg h1 h2`. Conclude with `⟨s, (resQ_Dec T.F A s).2 hg, by rw [hal]; exact h3⟩`. Take `⟨g, hg, h1, h2, h3⟩` from `X.big2 A hA`. Take `⟨s, rfl⟩` from `key 2 hD.two_mem A (by exact_mod_cast hA) g (Ine_le_Dec A hg) h1 h2`.

Conclude with `⟨s, (resQ_Ine T.F A s).2 hg, by rw [hal]; exact h3⟩`.
-/
theorem UpperTheory.V.Ws.two2 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (X : Set2 D) (T : Tower D), X.On T → ∀ k₀ : IntermediateField ℚ Ω, Module.finrank ℚ k₀ = 2 → IsTotallyReal k₀ → k₀.fixingSubgroup = X.φ.ker → T.Two := by
  intro Ω _ _ _ l hl c D hD X T hOn k₀ hk hr hfix
  obtain ⟨hne, -, -, -, -, -, hrb, -, -⟩ := barFacts D hD
  obtain ⟨-, -, -, -, haw⟩ := away D hD
  have hH : ∀ g : G T.F Ω, Raw.bar D.Psi (resQ T.F g) = ((X.φ (resQ T.F g) : ℤ) : ResidueField c.O) := fun g =>
    (X.mem_H.1 (hOn.1 ▸ resQ_mem T.F g)).1
  have hps : ∀ g : G T.F Ω, T.rb wPs g = ((X.φ (resQ T.F g) : ℤ) : ResidueField c.O) := fun g => by
    rw [hrb, hH]
    rcases Int.units_eq_one_or (X.φ (resQ T.F g)) with h | h <;> rw [h] <;> cases T.pr <;> simp [wPs]
  have hal : ∀ g : G T.F Ω, T.rb wAl g = Raw.bar D.ξ (resQ T.F g) := fun g => by
    rw [hrb]
    cases T.pr <;> simp [wAl]
  have hiff : ∀ g : G T.F Ω, T.rb wPs g = 1 ↔ X.φ (resQ T.F g) = 1 := fun g => by
    rw [hps]
    rcases Int.units_eq_one_or (X.φ (resQ T.F g)) with h | h <;> rw [h]
    · simp
    · constructor
      · intro h'
        exact absurd (by simpa using h') hne
      · intro h'
        exact absurd h' (by decide)
  have key : ∀ q ∈ D.S, ∀ A : ValuationSubring Ω, A.valuation (q : Ω) < 1 → ∀ g ∈ Dec (F := ℚ) A,
      Raw.bar D.Psi g = 1 → X.κ g = 1 → ∃ s : G T.F Ω, resQ T.F s = g := fun q hq A hA g hg h1 h2 => by
    have a : X.φ g = 1 := X.hφ.split q hq A hA hg
    have b : X.η g = 1 := X.hη.split q (Finset.mem_insert_of_mem hq) A hA hg
    have d : X.η' g = 1 := X.hη'.split q (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hq)) A hA hg
    refine exists_resQ ?_
    rw [hOn.1, X.mem_H]
    refine ⟨?_, b.trans d.symm, h2⟩
    rw [h1, a]
    simp
  refine ⟨fun g => ?_, fun A g hg => ?_, fun A hA g hg => ?_, ⟨k₀, hk, hr, fun p hp A hA => ?_, fun g => ?_⟩,
    X.ord, X.xi, fun A hA => ?_, fun A hA => ?_⟩
  · rw [hps]
    rcases Int.units_eq_one_or (X.φ (resQ T.F g)) with h | h <;> rw [h] <;> simp
  · have hg' := (resQ_Ine T.F A g).1 hg
    by_cases hA : A.valuation (X.p₃ : Ω) < 1
    · rw [hps, ← hH, Raw.bar, ((haw A X.p₃ X.hφ.prime X.hφ.nm hA).2 _ hg').1]
      simp
    · exact (hiff g).2 (X.hφ.unr A hA hg')
  · exact (hiff g).2 (X.hφ.split l hD.l_mem A hA ((resQ_Dec T.F A g).1 hg))
  · rw [hfix]
    refine X.hφ.split p ?_ A hA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact hD.two_mem
    · exact hD.l_mem
  · rw [hfix, MonoidHom.mem_ker]
    exact hiff g
  · obtain ⟨g, hg, h1, h2, h3⟩ := X.bigL A hA
    obtain ⟨s, rfl⟩ := key l hD.l_mem A hA g hg h1 h2
    exact ⟨s, (resQ_Dec T.F A s).2 hg, by rw [hal]; exact h3⟩
  · obtain ⟨g, hg, h1, h2, h3⟩ := X.big2 A hA
    obtain ⟨s, rfl⟩ := key 2 hD.two_mem A (by exact_mod_cast hA) g (Ine_le_Dec A hg) h1 h2
    exact ⟨s, (resQ_Ine T.F A s).2 hg, by rw [hal]; exact h3⟩
