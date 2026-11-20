import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ArtEx
import Development.DiscreteGroups.GlobalIrreducibility.ExistsIneOfVEqOne
import Development.DiscreteGroups.GlobalIrreducibility.DzTame
import Development.DiscreteGroups.GlobalIrreducibility.DzNormV
import Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.DepthZeroMonomial.ValLtOneIff

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

/- English proof (translation)
Set `c' : Ine (F` to `E) A := ⟨(frob h : G E Ω) * t * (frob h : G E Ω)⁻¹, conj_mem_Ine (isFrob_frob (h := h)).1 t.2⟩`. Establish `h1 : ξ (ineIncl h (c' * (t ^ normV w)⁻¹)) = 1` using `hW _ (DiscreteGroups.sglob.DzType.isWild_frob (isFrob_frob (h := h)) t)`. Establish `h2 : ineIncl h (c' * (t ^ normV w)⁻¹) = frob h * ineIncl h t * (frob h)⁻¹ * (ineIncl h t ^ normV w)⁻¹` using `Subtype.ext rfl`. Rewrite `h1` using `[h2]`. Simplify using `only [map_mul, map_inv, map_pow] at h1`.

Establish `h3 : ξ (ineIncl h t) = ξ (ineIncl h t) ^ normV w`. Rewrite `h1` using `[mul_inv_eq_one, mul_comm (ξ (frob h)), mul_inv_cancel_right]`. Conclude with `h1`. Establish `hq : 1 ≤ normV w` using `Nat.pos_of_ne_zero fun h0 => by`. Establish `: Finite (𝓞 E ⧸ w.asIdeal)` using `w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot`.

Conclude with `(Nat.card_pos (α := 𝓞 E ⧸ w.asIdeal)).ne' h0`. Establish `h4 : ξ (ineIncl h t) ^ (normV w - 1) * ξ (ineIncl h t) = 1 * ξ (ineIncl h t)`. Rewrite using `[← pow_succ, Nat.sub_add_cancel hq, one_mul]`. Conclude with `h3.symm`. Conclude with `mul_right_cancel h4`.
-/
private theorem pow_ine_eq_one (ξ : Weil h →* ℂˣ)
    (hW : ∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → ξ σ = 1) (t : Ine (F := E) A) :
    ξ (ineIncl h t) ^ (normV w - 1) = 1 := by
  let c' : Ine (F := E) A :=
    ⟨(frob h : G E Ω) * t * (frob h : G E Ω)⁻¹, conj_mem_Ine (isFrob_frob (h := h)).1 t.2⟩
  have h1 : ξ (ineIncl h (c' * (t ^ normV w)⁻¹)) = 1 :=
    hW _ (DiscreteGroups.sglob.DzType.isWild_frob (isFrob_frob (h := h)) t)
  have h2 : ineIncl h (c' * (t ^ normV w)⁻¹) =
      frob h * ineIncl h t * (frob h)⁻¹ * (ineIncl h t ^ normV w)⁻¹ := Subtype.ext rfl
  rw [h2] at h1
  simp only [map_mul, map_inv, map_pow] at h1
  have h3 : ξ (ineIncl h t) = ξ (ineIncl h t) ^ normV w := by
    rw [mul_inv_eq_one, mul_comm (ξ (frob h)), mul_inv_cancel_right] at h1
    exact h1
  have hq : 1 ≤ normV w := Nat.pos_of_ne_zero fun h0 => by
    have : Finite (𝓞 E ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
    exact (Nat.card_pos (α := 𝓞 E ⧸ w.asIdeal)).ne' h0
  have h4 : ξ (ineIncl h t) ^ (normV w - 1) * ξ (ineIncl h t) = 1 * ξ (ineIncl h t) := by
    rw [← pow_succ, Nat.sub_add_cancel hq, one_mul]
    exact h3.symm
  exact mul_right_cancel h4

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h a ha χ hχ`. Prove the components needed by the constructor for the conclusion. Introduce `hT σ hσ`. Conclude with `hT _ ((PositivityTheory.DzMono.val_lt_one_iff_alt _).2 (PositivityTheory.LocalParametersCuspidal.DZC.wild_to_unitsOne a ha σ hσ))`. Introduce `hW u hu`.

Establish `hu' : Valued.v ((u : w.adicCompletion E) - 1) < 1` using `(PositivityTheory.DzMono.val_lt_one_iff_alt _).1 hu`. Establish `hv1 : Valued.v (u : w.adicCompletion E) = 1`. Use `Valuation.map_one_add_of_lt Valued.v hu'` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis. Use `letI : Field (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal`.

Use `haveI : Finite (𝓞 E ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot`. Use `letI := Fintype.ofFinite (𝓞 E ⧸ w.asIdeal)`. Take `⟨p, hpc⟩` from `CharP.exists (𝓞 E ⧸ w.asIdeal)`. Take `⟨n, hp, hcard⟩` from `FiniteField.card (𝓞 E ⧸ w.asIdeal) p`. Use `haveI : Fact p.Prime := ⟨hp⟩`.

Establish `hN : normV w = p ^ (n : ℕ)`. Rewrite using `[← hcard, ← Nat.card_eq_fintype_card]`. Both sides reduce to the same expression. Establish `hpow : ∀ t : Ine (F` using `E) A, (χ.comp a) (ineIncl h t) ^ (p ^ (n : ℕ) - 1) = 1 := fun t => by`. Rewrite using `[← hN]`.

Conclude with `pow_ine_eq_one (χ.comp a) hW t`. Take `⟨ξ, hξ⟩` from `DiscreteGroups.sglob.DzType.exists_resChar p A w h (n : ℕ) n.pos hN a ha (𝓞 E ⧸ w.asIdeal) (Ideal.Quotient.mk w.asIdeal) Ideal.Quotient.mk_surjective (Ideal.mk_ker) (χ.comp a) (ha.smooth hχ) hpow`. Take `⟨t, ht⟩` from `DiscreteGroups.sglob.DzType.exists_ine_of_v_eq_one ha u hv1`. Establish `h1` using `hξ t 1 1 (by simp) (by simpa [ht] using hu')`. Rewrite `h1` using `[map_one]`.

Rewrite using `[← ht]`. Conclude with `h1.symm`.
-/
theorem _root_.UpperTheory.Zero.LLC.tameArt :
    UpperTheory.Zero.LLC.TameArt := by
  intro E Ω _ _ _ _ _ A w h a ha χ hχ
  constructor
  · intro hT σ hσ
    exact hT _ ((PositivityTheory.DzMono.val_lt_one_iff_alt _).2 (PositivityTheory.LocalParametersCuspidal.DZC.wild_to_unitsOne a ha σ hσ))
  · intro hW u hu
    have hu' : Valued.v ((u : w.adicCompletion E) - 1) < 1 := (PositivityTheory.DzMono.val_lt_one_iff_alt _).1 hu
    have hv1 : Valued.v (u : w.adicCompletion E) = 1 := by
      have := Valuation.map_one_add_of_lt Valued.v hu'
      rwa [add_sub_cancel] at this
    letI : Field (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
    haveI : Finite (𝓞 E ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
    letI := Fintype.ofFinite (𝓞 E ⧸ w.asIdeal)
    obtain ⟨p, hpc⟩ := CharP.exists (𝓞 E ⧸ w.asIdeal)
    obtain ⟨n, hp, hcard⟩ := FiniteField.card (𝓞 E ⧸ w.asIdeal) p
    haveI : Fact p.Prime := ⟨hp⟩
    have hN : normV w = p ^ (n : ℕ) := by
      rw [← hcard, ← Nat.card_eq_fintype_card]; rfl
    have hpow : ∀ t : Ine (F := E) A, (χ.comp a) (ineIncl h t) ^ (p ^ (n : ℕ) - 1) = 1 := fun t => by
      rw [← hN]
      exact pow_ine_eq_one (χ.comp a) hW t
    obtain ⟨ξ, hξ⟩ := DiscreteGroups.sglob.DzType.exists_resChar p A w h (n : ℕ) n.pos hN a ha (𝓞 E ⧸ w.asIdeal)
      (Ideal.Quotient.mk w.asIdeal) Ideal.Quotient.mk_surjective (Ideal.mk_ker) (χ.comp a) (ha.smooth hχ) hpow
    obtain ⟨t, ht⟩ := DiscreteGroups.sglob.DzType.exists_ine_of_v_eq_one ha u hv1
    have h1 := hξ t 1 1 (by simp) (by simpa [ht] using hu')
    rw [map_one] at h1
    rw [← ht]
    exact h1.symm

end UpperTheory.Zero.LLC

end
