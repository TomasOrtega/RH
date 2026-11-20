import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalParameterLawsOfWeilDeligneIdentification
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParameterMonodromyZeroOfUnramified
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharPolLpCharOfUnr

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

namespace GlobalTheory.InertialTypes

/- English proof (translation)
Introduce `hw'`. Establish `hc : IsCoprime (p : 𝓞 E) (q : 𝓞 E)` using `Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)`. Take `⟨a, b, hab⟩` from `hc`. Apply `w.isPrime.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one, ← hab]`.

Conclude with `w.asIdeal.add_mem (w.asIdeal.mul_mem_left a hw) (w.asIdeal.mul_mem_left b hw')`.
-/
theorem not_mem_placesOver_of_ne {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) {w : HeightOneSpectrum (𝓞 E)} (hw : w ∈ placesOver E p) : w ∉ placesOver E q := by
  intro hw'
  have hc : IsCoprime (p : 𝓞 E) (q : 𝓞 E) := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left a hw) (w.asIdeal.mul_mem_left b hw')

/- English proof (translation)
Introduce `D T S hTS hBS hL hS hchi hT hB`. Use `⟨fun i P w hSQ hc => ?_, fun i P w hwS _ _ hm => ?_, (GlobalTheory.RowLaws.main _ _ _ _ _ T).2.2⟩` and prove the remaining obligations. Establish `hw` using `D.nd.SQ_split i w hSQ`. Use `GlobalTheory.TameType.inertialType_of_tame _ _ _ _ _ T S i w hw hTS hL (hT i w hw ?_) (hchi i w (D.nd.SQ_l i w hSQ)) P` and prove the remaining obligations. Distinguish the cases in `hQ : w ∈ D.nd.Q i`.

Conclude with `Or.inl hQ`. Use `Or.inr ⟨hSQ.resolve_right hQ, fun k => ?_⟩` and prove the remaining obligations. Break down `(hc.resolve_left hQ).2 with h | ⟨-, h⟩` into its components or cases. Conclude with `not_mem_placesOver_of_ne D.host.pde_prime (D.host.g_prime k) (D.host.pde_ne_g k).1 h`. Conclude with `not_mem_placesOver_of_ne D.host.pde'_prime (D.host.g_prime k) (D.host.pde_ne_g k).2 h`.

Establish `hw` using `D.nd.SQ_split i w (Or.inl hwS)`. Conclude with `GlobalTheory.SplitRead.BlockParam.split_param _ _ _ _ _ T S i w hw hBS hL hS (hB i w hw (Or.inl hwS)) (hchi i w (D.nd.SQ_l i w (Or.inl hwS))) P hm`.
-/
theorem main : ∀ (D : D7) (T : WDTie D.nd D.naut) (S : Reading T), TameSplitAll D.host.E → BlockSplitAll D.host.E → Laws S → SuppLaws S → ChiIne D.nd D.naut → (∀ i w hw, (w ∈ D.nd.Q i ∨ (w ∈ D.nd.S i ∧ ∀ k, w ∉ placesOver D.host.E (D.host.g k))) → TypeTame S i w hw) → (∀ i w hw, (w ∈ D.nd.S i ∨ w ∈ D.nd.Q i) → TypeBlock S i w hw) → Formalism.MainNotions.SumRepresentations.ArchimedeanSignatureMatching D := by
  intro D T S hTS hBS hL hS hchi hT hB
  refine ⟨fun i P w hSQ hc => ?_, fun i P w hwS _ _ hm => ?_, (GlobalTheory.RowLaws.main _ _ _ _ _ T).2.2⟩
  · have hw := D.nd.SQ_split i w hSQ
    refine GlobalTheory.TameType.inertialType_of_tame _ _ _ _ _ T S i w hw hTS hL (hT i w hw ?_)
      (hchi i w (D.nd.SQ_l i w hSQ)) P
    by_cases hQ : w ∈ D.nd.Q i
    · exact Or.inl hQ
    · refine Or.inr ⟨hSQ.resolve_right hQ, fun k => ?_⟩
      rcases (hc.resolve_left hQ).2 with h | ⟨-, h⟩
      · exact not_mem_placesOver_of_ne D.host.pde_prime (D.host.g_prime k) (D.host.pde_ne_g k).1 h
      · exact not_mem_placesOver_of_ne D.host.pde'_prime (D.host.g_prime k) (D.host.pde_ne_g k).2 h
  · have hw := D.nd.SQ_split i w (Or.inl hwS)
    exact GlobalTheory.SplitRead.BlockParam.split_param _ _ _ _ _ T S i w hw hBS hL hS (hB i w hw (Or.inl hwS))
      (hchi i w (D.nd.SQ_l i w (Or.inl hwS))) P hm

end GlobalTheory.InertialTypes
