import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PlacesOfRationals.PlacesQ

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.X

/- English proof (translation)
Introduce `Ω _ _ _ l _ k _ γ hL T pl K hT hKn hKl z hzlc hzc hzI hzD`. Establish `hlp : l.Prime` using `Fact.out`. Establish `hz1 : z 1 = 0`. Establish `h` using `hzc 1 1`. Simplify using `only [mul_one, map_one, Units.val_one, one_mul] at h`.

Simplify using `using h`. Establish `hconj : ∀ g x, (γ x : k) = 1 → z (g⁻¹ * x * g) = (γ g⁻¹ : k) * z x`. Introduce `g x hx`. Establish `h0 : z g⁻¹ + (γ g⁻¹ : k) * z g = 0` using `by rw [← hzc, inv_mul_cancel, hz1]`. Rewrite using `[mul_assoc, hzc, hzc, hx]`.

Take the linear combination `h0`. Apply `hL z ⟨hzlc, fun g h => by rw [hzc, smul_eq_mul]⟩` to reduce the goal to its premises. Introduce `A`. Distinguish the cases in `hA : ∀ p ∈ T, ¬ A.valuation (p : Ω) < 1`. Use `⟨K, fun h => hKl (dvd_trans h (Subgroup.relIndex_dvd_index_of_normal _ _)), ?_⟩` and prove the remaining obligations.

Introduce `g hgK hgA _`. Conclude with `hzI A hA g hgA hgK`. Use `push_neg at hA`. Take `⟨p, hpT, hAp⟩` from `hA`. Take `⟨hpp, hplp⟩` from `hT p hpT`.

Take `⟨m, hm⟩` from `hzD p hpT`. Take `⟨g, hg⟩` from `(B3.placesQ Ω).2.2 p (pl p) A hpp hplp hAp`. Use `⟨⊤, by rw [Subgroup.relIndex_top_left]; exact hlp.not_dvd_one, ?_⟩` and prove the remaining obligations. Introduce `x _ hxA hγx`. Establish `hγx' : (γ x : k) = 1` using `by rw [hγx, Units.val_one]`.

Establish `hγc : (γ (g⁻¹ * x * g) : k) = 1` using `by simp [map_mul, hγx]`. Establish `hin : g⁻¹ * x * g ∈ Dec (pl p)` using `Ine_le_Dec (pl p) (hg x hxA)`. Establish `h1` using `hm _ hin`. Rewrite `h1` using `[hconj g x hγx', hγc, one_mul, sub_self]`. Conclude with `(mul_eq_zero.mp h1).resolve_left (Units.ne_zero _)`.
-/
theorem UpperTheory.V.X.vanOf :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (k : Type) [Field k] (γ : G ℚ Ω →* kˣ), (∀ z : G ℚ Ω → k, ML.IsCoc γ z → UnrEv l γ z → ∃ m : k, ∀ g, z g = (γ g : k) * m - m) → ∀ (T : Finset ℕ) (pl : ℕ → ValuationSubring Ω) (K : Subgroup (G ℚ Ω)), (∀ p ∈ T, p.Prime ∧ (pl p).valuation (p : Ω) < 1) → K.Normal → ¬ l ∣ K.index → Van T pl K γ := by
  intro Ω _ _ _ l _ k _ γ hL T pl K hT hKn hKl z hzlc hzc hzI hzD
  have hlp : l.Prime := Fact.out
  have hz1 : z 1 = 0 := by
    have h := hzc 1 1
    simp only [mul_one, map_one, Units.val_one, one_mul] at h
    simpa using h
  have hconj : ∀ g x, (γ x : k) = 1 → z (g⁻¹ * x * g) = (γ g⁻¹ : k) * z x := by
    intro g x hx
    have h0 : z g⁻¹ + (γ g⁻¹ : k) * z g = 0 := by rw [← hzc, inv_mul_cancel, hz1]
    rw [mul_assoc, hzc, hzc, hx]
    linear_combination h0
  apply hL z ⟨hzlc, fun g h => by rw [hzc, smul_eq_mul]⟩
  intro A
  by_cases hA : ∀ p ∈ T, ¬ A.valuation (p : Ω) < 1
  · refine ⟨K, fun h => hKl (dvd_trans h (Subgroup.relIndex_dvd_index_of_normal _ _)), ?_⟩
    intro g hgK hgA _
    exact hzI A hA g hgA hgK
  · push_neg at hA
    obtain ⟨p, hpT, hAp⟩ := hA
    obtain ⟨hpp, hplp⟩ := hT p hpT
    obtain ⟨m, hm⟩ := hzD p hpT
    obtain ⟨g, hg⟩ := (B3.placesQ Ω).2.2 p (pl p) A hpp hplp hAp
    refine ⟨⊤, by rw [Subgroup.relIndex_top_left]; exact hlp.not_dvd_one, ?_⟩
    intro x _ hxA hγx
    have hγx' : (γ x : k) = 1 := by rw [hγx, Units.val_one]
    have hγc : (γ (g⁻¹ * x * g) : k) = 1 := by simp [map_mul, hγx]
    have hin : g⁻¹ * x * g ∈ Dec (pl p) := Ine_le_Dec (pl p) (hg x hxA)
    have h1 := hm _ hin
    rw [hconj g x hγx', hγc, one_mul, sub_self] at h1
    exact (mul_eq_zero.mp h1).resolve_left (Units.ne_zero _)
