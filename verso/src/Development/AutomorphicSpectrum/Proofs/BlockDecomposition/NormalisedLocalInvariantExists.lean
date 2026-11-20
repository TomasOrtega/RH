import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBrauerRootsUnityEquivStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalInvariantCupUniformizerStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalInvariantCupKummerStatement

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory.CompanionTheory.LocalInvariant

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ l _ r hr ζ hζ A v hA`. Take `⟨e⟩` from `GlobalTheory.T.local_brauer_roots_unity_equiv F Ω l r hr A v hA`. Distinguish the cases in `hN : IsNormalised ζ A v (e : H2 (muLoc F l r A) →ₗ[ZMod (l ^ r)] ZMod (l ^ r))`. Conclude with `⟨e, e.bijective, hN⟩`. Simplify using `only [IsNormalised, not_forall] at hN`.

Take `⟨ϖ, y, κ, χ, z, h1, h2, h3, h4, h5, h6, h7, h8, -⟩` from `hN`. Establish `hgen` using `GlobalTheory.T.local_invariant_cup_uniformizer F Ω l r hr ζ hζ A v hA ϖ y κ χ z h1 h2 h3 h4 h5 h6 h7 h8`. Use `set c : H2 (muLoc F l r A) := Submodule.Quotient.mk z with hc`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a : ZMod (l ^ r), a * e c = 1 := by`. Establish `hmem : e.symm 1 ∈ Submodule.span (ZMod (l ^ r)) {c}`.

Rewrite using `[hgen]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨a, hac⟩` from `Submodule.mem_span_singleton.1 hmem`. Use `⟨a, ?_⟩` and prove the remaining obligations. Use `congrArg e hac` as an intermediate fact.

Simplify using `using this`. Establish `ha' : e c * a = 1` using `by rw [mul_comm]; exact ha`. Use `⟨a • (e : H2 (muLoc F l r A) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)), ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `x x' hxx`. Establish `hxx' : a * e x = a * e x'` using `by simpa using hxx`.

Apply `e.injective` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Introduce `t`. Use `⟨e.symm (e c * t), ?_⟩` and prove the remaining obligations. Simplify using `[← mul_assoc, ha]`.

Introduce `ϖ' y' κ' χ' z' g1 g2 g3 g4 g5 g6 g7 g8`. Establish `hz` using `GlobalTheory.T.local_invariant_cup_kummer F Ω l r hr ζ hζ A v hA ϖ y κ χ z h1 h2 h3 h4 h5 h6 h7 h8 ϖ' y' κ' χ' z' g1 g2 g3 g4 g5 g6 g7 g8`. Rewrite using `[← hz]`. Simplify using `using ha`.
-/
theorem exists_bijective_isNormalised :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ)
      [Fact l.Prime] (r : ℕ), 0 < r → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ r) →
      ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v →
      ∃ f : H2 (muLoc F l r A) →ₗ[ZMod (l ^ r)] ZMod (l ^ r),
        Function.Bijective f ∧ IsNormalised ζ A v f := by
  intro F Ω _ _ _ _ _ l _ r hr ζ hζ A v hA
  obtain ⟨e⟩ := GlobalTheory.T.local_brauer_roots_unity_equiv F Ω l r hr A v hA
  by_cases hN : IsNormalised ζ A v (e : H2 (muLoc F l r A) →ₗ[ZMod (l ^ r)] ZMod (l ^ r))
  · exact ⟨e, e.bijective, hN⟩
  · simp only [IsNormalised, not_forall] at hN
    obtain ⟨ϖ, y, κ, χ, z, h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := hN
    have hgen := GlobalTheory.T.local_invariant_cup_uniformizer F Ω l r hr ζ hζ A v hA ϖ y κ χ z h1 h2 h3 h4 h5 h6 h7 h8
    set c : H2 (muLoc F l r A) := Submodule.Quotient.mk z with hc

    obtain ⟨a, ha⟩ : ∃ a : ZMod (l ^ r), a * e c = 1 := by
      have hmem : e.symm 1 ∈ Submodule.span (ZMod (l ^ r)) {c} := by
        rw [hgen]; trivial
      obtain ⟨a, hac⟩ := Submodule.mem_span_singleton.1 hmem
      refine ⟨a, ?_⟩
      have := congrArg e hac
      simpa using this
    have ha' : e c * a = 1 := by rw [mul_comm]; exact ha
    refine ⟨a • (e : H2 (muLoc F l r A) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)), ⟨?_, ?_⟩, ?_⟩
    · intro x x' hxx
      have hxx' : a * e x = a * e x' := by simpa using hxx
      apply e.injective
      calc e x = e c * (a * e x) := by rw [← mul_assoc, ha', one_mul]
        _ = e c * (a * e x') := by rw [hxx']
        _ = e x' := by rw [← mul_assoc, ha', one_mul]
    · intro t
      refine ⟨e.symm (e c * t), ?_⟩
      simp [← mul_assoc, ha]
    · intro ϖ' y' κ' χ' z' g1 g2 g3 g4 g5 g6 g7 g8
      have hz := GlobalTheory.T.local_invariant_cup_kummer F Ω l r hr ζ hζ A v hA ϖ y κ χ z h1 h2 h3 h4 h5 h6 h7 h8
        ϖ' y' κ' χ' z' g1 g2 g3 g4 g5 g6 g7 g8
      rw [← hz]
      simpa using ha

end GlobalTheory.CompanionTheory.LocalInvariant
