import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowMulMemAdd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToZModPowKummerEqIff
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

/- English proof (translation)
Introduce `l _ Ω _ _ _ e S A W hW a ha`. Use `set T : Subgroup (G ℚ Ω) := W.ker ⊓ (cycZ ℚ Ω l).ker with hT`. Establish `hTc : IsClosed (T : Set (G ℚ Ω))`. Establish `h1 : IsClosed (W.ker : Set (G ℚ Ω))` using `isClosed_singleton.preimage hW.cont`. Establish `h2 : IsClosed ((cycZ ℚ Ω l).ker : Set (G ℚ Ω))` using `isClosed_singleton.preimage (continuous_cycZ ℚ Ω l)`.

Conclude with `h1.inter h2`. Establish `hNS : NS Ω (S : Set Pl) ≤ T`. Use `Subgroup.topologicalClosure_minimal _ ?_ hTc` and prove the remaining obligations. Apply `Subgroup.normalClosure_le_normal` to reduce the goal to its premises. Introduce `τ hτ`.

Simplify using `only [Set.mem_iUnion] at hτ`. Take `⟨v, hv, B, hB, hτ⟩` from `hτ`. Use `⟨hW.unr v hv B hB hτ, ?_⟩` and prove the remaining obligations. Establish `hl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal` using `fun h => hv (hW.above v h)`. Conclude with `GlobalTheory.WeilDeligne.cycZ_of_mem_Ine hB hl hτ`.

Establish `haT : a ∈ T` using `hNS ((QuotientGroup.eq_one_iff _).mp ha)`. Establish `hWa : W a = 1` using `haT.1`. Establish `hca : cycZ ℚ Ω l a = 1` using `haT.2`. Establish `hcb : cycBar ℚ Ω l a = 1` using `by simp [cycBar, hca]`. Establish `hdt : dt W a = 1` using `by simp [dt, hWa]`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[dual1, tw_val]`. Simplify using `[hcb, hdt, hWa]`.
-/
theorem galoisRepRankTwoTateDual_eq_one_of_mem_ker_unramified : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ a ∈ (toGS Ω (S : Set Pl)).ker, dual1 W a = 1 := by
  intro l _ Ω _ _ _ e S A W hW a ha
  set T : Subgroup (G ℚ Ω) := W.ker ⊓ (cycZ ℚ Ω l).ker with hT
  have hTc : IsClosed (T : Set (G ℚ Ω)) := by
    have h1 : IsClosed (W.ker : Set (G ℚ Ω)) := isClosed_singleton.preimage hW.cont
    have h2 : IsClosed ((cycZ ℚ Ω l).ker : Set (G ℚ Ω)) := isClosed_singleton.preimage (continuous_cycZ ℚ Ω l)
    exact h1.inter h2
  have hNS : NS Ω (S : Set Pl) ≤ T := by
    refine Subgroup.topologicalClosure_minimal _ ?_ hTc
    apply Subgroup.normalClosure_le_normal
    intro τ hτ
    simp only [Set.mem_iUnion] at hτ
    obtain ⟨v, hv, B, hB, hτ⟩ := hτ
    refine ⟨hW.unr v hv B hB hτ, ?_⟩
    have hl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun h => hv (hW.above v h)
    exact GlobalTheory.WeilDeligne.cycZ_of_mem_Ine hB hl hτ
  have haT : a ∈ T := hNS ((QuotientGroup.eq_one_iff _).mp ha)
  have hWa : W a = 1 := haT.1
  have hca : cycZ ℚ Ω l a = 1 := haT.2
  have hcb : cycBar ℚ Ω l a = 1 := by simp [cycBar, hca]
  have hdt : dt W a = 1 := by simp [dt, hWa]
  apply Units.ext
  rw [dual1, tw_val]
  simp [hcb, hdt, hWa]

end GlobalTheory.Ord2
