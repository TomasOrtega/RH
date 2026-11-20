import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.IsTwistTwD
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ConjPlace

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5 GlobalTheory.GalOfCusp

/- English proof (translation)
Introduce `l _ L Ω _ _ _ _ _ _ s V`. Use `⟨(phiKer V).2.1, ?_, ?_⟩` and prove the remaining obligations. Introduce `g`. Establish `hin : s.c * resP L Ω g * s.c⁻¹ ∈ (resP L Ω).range`. Rewrite using `[← V.hη]`.

Establish `h1 : V.η (toGS Ω V.S' (resP L Ω g)) = 1` using `(V.hη _).mpr ⟨g, rfl⟩`. Simplify using `only [map_mul, map_inv, h1, mul_one, mul_inv_cancel]`. Take `⟨g', hg'⟩` from `hin`. Use `⟨g', hg', ?_⟩` and prove the remaining obligations. Establish `e1 : toGS Ω V.S' (s.c * resP L Ω g * s.c⁻¹) = toGS Ω V.S' s.c * ((V.pr g : V.η.ker) : GS Ω V.S') * (toGS Ω V.S' s.c)⁻¹`.

Rewrite using `[map_mul, map_mul, map_inv]`. Apply the tactic sequence `all_goals rfl`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show toGS Ω V.S' s.c * ((V.pr g : V.η.ker) : GS Ω V.S') * (toGS Ω V.S' s.c)⁻¹ = ((V.pr g' : V.η.ker) : GS Ω V.S')`. Rewrite using `[← e1, ← hg']`.

Apply the tactic sequence `all_goals rfl`. Introduce `H _ hcl _ hine`. Apply `(phiKer V).2.2 H hcl` to reduce the goal to its premises. Introduce `A v hAv hv`. Apply `hine A` to reduce the goal to its premises.

Introduce `hlt`. Apply `hv` to reduce the goal to its premises. Apply `V.sub` to reduce the goal to its premises. Establish `hmem` using `(hAv (l : 𝓞 (Lp L))).mp (by simpa using hlt)`. Conclude with `Or.inl (by simpa using hmem)`.
-/
theorem UpperTheory.V.Ws.H5.prFacts :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : HidaSetting l L Ω} (V : s.Lev), Topology.IsQuotientMap V.pr ∧ (∀ g : G L Ω, ∃ g' : G L Ω, resP L Ω g' = s.c * resP L Ω g * s.c⁻¹ ∧ V.frame.conj (V.pr g) = V.pr g') ∧ ∀ H : Subgroup (G L Ω), H.Normal → IsClosed (H : Set (G L Ω)) → (∀ g g' : G L Ω, resP L Ω g' = s.c * resP L Ω g * s.c⁻¹ → g ∈ H → g' ∈ H) → (∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → Ine (F := L) A ≤ H) → V.pr.ker ≤ H := by
  intro l _ L Ω _ _ _ _ _ _ s V
  refine ⟨(phiKer V).2.1, ?_, ?_⟩
  · intro g
    have hin : s.c * resP L Ω g * s.c⁻¹ ∈ (resP L Ω).range := by
      rw [← V.hη]
      have h1 : V.η (toGS Ω V.S' (resP L Ω g)) = 1 := (V.hη _).mpr ⟨g, rfl⟩
      simp only [map_mul, map_inv, h1, mul_one, mul_inv_cancel]
    obtain ⟨g', hg'⟩ := hin
    refine ⟨g', hg', ?_⟩
    have e1 : toGS Ω V.S' (s.c * resP L Ω g * s.c⁻¹) =
        toGS Ω V.S' s.c * ((V.pr g : V.η.ker) : GS Ω V.S') * (toGS Ω V.S' s.c)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
      all_goals rfl
    apply Subtype.ext
    show toGS Ω V.S' s.c * ((V.pr g : V.η.ker) : GS Ω V.S') * (toGS Ω V.S' s.c)⁻¹ =
      ((V.pr g' : V.η.ker) : GS Ω V.S')
    rw [← e1, ← hg']
    all_goals rfl
  · intro H _ hcl _ hine
    apply (phiKer V).2.2 H hcl
    intro A v hAv hv
    apply hine A
    intro hlt
    apply hv
    apply V.sub
    have hmem := (hAv (l : 𝓞 (Lp L))).mp (by simpa using hlt)
    exact Or.inl (by simpa using hmem)
