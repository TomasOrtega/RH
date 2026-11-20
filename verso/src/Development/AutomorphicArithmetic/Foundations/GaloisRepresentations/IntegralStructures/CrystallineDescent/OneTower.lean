import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.PatchOneAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResInjective

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.V.Af.Bc (res)
open UpperTheory.Gal.Int.Core

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Separate the alternatives or extract the components of the hypothesis. It suffices to derive a contradiction. Establish an intermediate fact. A detailed English derivation is pending.
-/
private theorem normV_under_eq_of_normV_prime {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (w : HeightOneSpectrum (𝓞 M)) (hp : (normV w).Prime) : normV (w.under (𝓞 K)) = normV w := by
  let f : 𝓞 K ⧸ (w.under (𝓞 K)).asIdeal →+* 𝓞 M ⧸ w.asIdeal :=
    Ideal.quotientMap w.asIdeal (algebraMap (𝓞 K) (𝓞 M)) le_rfl
  have hf : Function.Injective f := Ideal.quotientMap_injective' le_rfl
  have hd : normV (w.under (𝓞 K)) ∣ normV w := by
    have h1 := AddSubgroup.card_addSubgroup_dvd_card f.toAddMonoidHom.range
    rwa [← Nat.card_congr (AddMonoidHom.ofInjective (f := f.toAddMonoidHom) hf).toEquiv] at h1
  rcases (Nat.dvd_prime hp).1 hd with h | h
  · exfalso
    haveI : (w.under (𝓞 K)).asIdeal.IsPrime := (w.under (𝓞 K)).isPrime
    have h2 := (Nat.card_eq_one_iff_unique.1 h).1
    exact not_subsingleton (𝓞 K ⧸ (w.under (𝓞 K)).asIdeal) h2
  · exact h

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Apply an available result and prove the equalities needed to match it to the conclusion. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.Int.Core.oneTower_holds :
    OneTower := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ M _ _ _ _ _ _ _ _ _ l _ ι a sat r hK
  unfold AttOne at hK ⊢
  have hT : Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 M) => w.under (𝓞 K))
      Filter.cofinite Filter.cofinite := by
    refine ((Filter.tendstoCofinite_iff_finite_preimage_singleton _).2 ?_).tendsto_cofinite
    intro v
    refine (Ideal.finite_factors (I := v.asIdeal.map (algebraMap (𝓞 K) (𝓞 M))) ?_).subset ?_
    · exact Ideal.map_ne_bot_of_ne_bot v.ne_bot
    · intro w hw
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hw
      show w.asIdeal ∣ _
      rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← hw]
      exact le_rfl
  filter_upwards [hT.eventually hK] with w hw hp
  have hn := normV_under_eq_of_normV_prime (K := K) w hp
  obtain ⟨B, hB, hF⟩ := hw (hn ▸ hp)
  refine ⟨B, ?_, ?_⟩
  · convert hB using 2
    ext x
    show algebraMap (𝓞 F) (𝓞 M) x ∈ w.asIdeal ↔ algebraMap (𝓞 K) (𝓞 M) (algebraMap (𝓞 F) (𝓞 K) x) ∈ w.asIdeal
    rw [show algebraMap (𝓞 K) (𝓞 M) (algebraMap (𝓞 F) (𝓞 K) x) = algebraMap (𝓞 F) (𝓞 M) x from
      Subtype.ext (IsScalarTower.algebraMap_apply F K M (x : F)).symm]
  · rw [hn] at hF
    intro A hA
    have hA' : IsPlaceOver A (w.under (𝓞 K)) := by
      intro x
      rw [show algebraMap K Ω (x : K) = algebraMap M Ω ((algebraMap (𝓞 K) (𝓞 M) x : 𝓞 M) : M) from
        IsScalarTower.algebraMap_apply K M Ω (x : K)]
      exact hA _
    obtain ⟨hI, hFr⟩ := hF A hA'
    refine ⟨fun s hs => hI _ ?_, fun σ hσ => ?_⟩
    · obtain ⟨hs1, hs2⟩ := hs
      exact ⟨hs1, fun x hx => hs2 x hx⟩
    · have h3 := hFr (res K Ω M σ) ⟨hσ.1, fun x hx => by rw [hn]; exact hσ.2 x hx⟩
      rw [MonoidHom.comp_apply, map_inv]
      exact h3
