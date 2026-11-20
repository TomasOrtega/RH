import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotZeroChi
import Development.AbelianVarietyTheory.Definitions.Foundations.ZetaSysUOfHalves
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPolyInRootOfInertiaCyclotomicFixedStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaFixedValuationEqZpowPrimeValuationStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationPrimitiveRootSubOnePowTotientStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralPolyOfPrimitiveRootTotallyRamifiedStatement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

namespace GlobalTheory.CycIne

/- English proof (translation)
Introduce `l _ Ω _ _ _ A hA m ζ hζ u hu hfix`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective`. Break down `Nat.eq_zero_or_pos m with rfl | hm` into its components or cases. Use `⟨Polynomial.C u, ?_, by simp⟩` and prove the remaining obligations. Introduce `x hx`.

Establish `hxu : x = u`. Take `⟨n, hn, rfl⟩` from `Polynomial.mem_coeffs_iff.1 hx`. Rewrite `hn` using `[Polynomial.mem_support_iff, Polynomial.coeff_C]`. Rewrite using `[Polynomial.coeff_C]`. Use `split_ifs at hn ⊢ with h`.

Both sides reduce to the same expression. Conclude with `absurd rfl hn`. Substitute `hxu` using the available equality. Use `haveI : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance`. Conclude with `⟨hu, fun s hs => hfix s hs (Units.ext (Subsingleton.elim _ _))⟩`.

Take `⟨Q, hQ, hQe⟩` from `GlobalTheory.T.exists_poly_in_root_of_inertia_cyclotomic_fixed l Ω A m ζ hζ u hfix`. Establish `hl : A.valuation (l : Ω) < 1`. Take `⟨v, hv, hlv⟩` from `hA`. Use `(hv (l : 𝓞 ℚ)).2 hlv` as an intermediate fact. Simplify using `using this`.

Set `K : Subfield Ω` to `(IntermediateField.fixedField (Ine (F := ℚ) A)).toSubfield`. Establish `hK : ∀ x, x ∈ K ↔ ∀ s ∈ Ine (F` using `ℚ) A, s x = x := fun x => IntermediateField.mem_fixedField_iff _ x`. Take `⟨P, hP, hPe⟩` from `GlobalTheory.T.exists_integral_poly_eval_zeta_of_totally_ramified l Ω A hl K (fun x hx hx0 => GlobalTheory.T.inertia_fixed_valuation_eq_zpow_prime_valuation l Ω A hA x hx0 ((hK x).1 hx)) m hm ζ hζ (GlobalTheory.T.valuationSubring_primitiveRoot_sub_one_pow_totient_charZero l Ω A m …`. Conclude with `⟨P, fun x hx => ⟨(hP x hx).1, (hK x).1 (hP x hx).2⟩, hPe⟩`.
-/
theorem exists_poly_of_fixed : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (m : ℕ) (ζ : Ω), IsPrimitiveRoot ζ (l ^ m) → ∀ u ∈ A, (∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 → s u = u) → ∃ P : Polynomial Ω, (∀ x ∈ P.coeffs, x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x) ∧ P.eval ζ = u := by
  intro l _ Ω _ _ _ A hA m ζ hζ u hu hfix
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨Polynomial.C u, ?_, by simp⟩
    intro x hx
    have hxu : x = u := by
      obtain ⟨n, hn, rfl⟩ := Polynomial.mem_coeffs_iff.1 hx
      rw [Polynomial.mem_support_iff, Polynomial.coeff_C] at hn
      rw [Polynomial.coeff_C]
      split_ifs at hn ⊢ with h
      · rfl
      · exact absurd rfl hn
    subst hxu
    haveI : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance
    exact ⟨hu, fun s hs => hfix s hs (Units.ext (Subsingleton.elim _ _))⟩
  · obtain ⟨Q, hQ, hQe⟩ := GlobalTheory.T.exists_poly_in_root_of_inertia_cyclotomic_fixed l Ω A m ζ hζ u hfix
    have hl : A.valuation (l : Ω) < 1 := by
      obtain ⟨v, hv, hlv⟩ := hA
      have := (hv (l : 𝓞 ℚ)).2 hlv
      simpa using this
    let K : Subfield Ω := (IntermediateField.fixedField (Ine (F := ℚ) A)).toSubfield
    have hK : ∀ x, x ∈ K ↔ ∀ s ∈ Ine (F := ℚ) A, s x = x := fun x =>
      IntermediateField.mem_fixedField_iff _ x
    obtain ⟨P, hP, hPe⟩ := GlobalTheory.T.exists_integral_poly_eval_zeta_of_totally_ramified l Ω A hl K
      (fun x hx hx0 => GlobalTheory.T.inertia_fixed_valuation_eq_zpow_prime_valuation l Ω A hA x hx0 ((hK x).1 hx)) m hm ζ hζ
      (GlobalTheory.T.valuationSubring_primitiveRoot_sub_one_pow_totient_charZero l Ω A m hm ζ hζ) u hu ⟨Q, fun x hx => (hK x).2 (hQ x hx), hQe⟩
    exact ⟨P, fun x hx => ⟨(hP x hx).1, (hK x).1 (hP x hx).2⟩, hPe⟩

end GlobalTheory.CycIne
