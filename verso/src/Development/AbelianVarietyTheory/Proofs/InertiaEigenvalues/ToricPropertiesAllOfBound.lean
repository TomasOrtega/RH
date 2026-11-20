import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BoundedDenominatorsOfBeta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumEqHeckeLValueMulAuxiliaryFactorsStatement
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassTermBoundBetaOfToricDenominator

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.ToricDistribution

namespace GlobalTheory.ToricAssembly

/- English proof (translation)
The claim follows from `GlobalTheory.T.toric_sum_eq_hecke_L_value_mul_auxiliary_factors exists_isHeckeL_of_hasInf`.
-/
theorem toricSumFormula : ToricSumFormula :=
  GlobalTheory.T.toric_sum_eq_hecke_L_value_mul_auxiliary_factors exists_isHeckeL_of_hasInf

/- English proof (translation)
Take `⟨M, hM, hle⟩` from `Ideal.exists_le_maximal _ hb.2.1`. Set `v : HeightOneSpectrum (OF E)` to `⟨M, hM.isPrime, fun h => hb.1 (le_bot_iff.1 (h ▸ hle))⟩`. Establish `hv : v.asIdeal ∣ 𝔣` using `Ideal.dvd_iff_le.2 hle`. Take `⟨P, -, -, hP, -⟩` from `(hb.2.2 v hv).1`. Conclude with `GlobalTheory.HeckeOne.not_isNormPow_of_not_unrAt (((hχ.2.2.2 v P hP).2 (Finset.notMem_empty v)).not_unrAt (multiplicity_ne_zero.2 hv))`.
-/
theorem not_isNormPow {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ}
    {𝔣 : Ideal (OF E)} {χ : HChar E} (hb : IsBaseCond 𝔣) (hχ : IsValChar φ s κ 𝔣 ∅ χ) :
    ¬ ∃ t : ℝ, GlobalTheory.HeckeOne.IsNormPow χ t := by
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hb.2.1
  let v : HeightOneSpectrum (OF E) := ⟨M, hM.isPrime, fun h => hb.1 (le_bot_iff.1 (h ▸ hle))⟩
  have hv : v.asIdeal ∣ 𝔣 := Ideal.dvd_iff_le.2 hle
  obtain ⟨P, -, -, hP, -⟩ := (hb.2.2 v hv).1
  exact GlobalTheory.HeckeOne.not_isNormPow_of_not_unrAt
    (((hχ.2.2.2 v P hP).2 (Finset.notMem_empty v)).not_unrAt (multiplicity_ne_zero.2 hv))

section Record

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ h => absurd h (Finset.notMem_empty _), Finset.disjoint_empty_left _, fun _ h => absurd h (Finset.notMem_empty _)⟩`.
-/
theorem qOk_empty (i : X.Tw) : BlochKatoReduction.Gen.QOk X i ∅ :=
  ⟨fun _ h => absurd h (Finset.notMem_empty _), Finset.disjoint_empty_left _, fun _ h => absurd h (Finset.notMem_empty _)⟩

/- English proof (translation)
Establish `: IsCMField D.host.E` using `D.host.isCMField_hostE`. Take `⟨I, _, φ, κ, 𝔣, χ, u, hD, h𝔣, -, hu, hth⟩` from `ht`. Take `⟨hfin, π, T, -, hT, hδ⟩` from `hth ∅ (qOk_empty i)`. Establish `he : belowSet (∅ : Finset (HeightOneSpectrum (𝓞 D.host.E))) = ∅` using `Finset.image_empty _`. Take `⟨hφ, -, hs, -, hb, hχ⟩` from `hD`.

Establish `hn` using `not_isNormPow hb hχ`. Take `⟨Λ, hΛ⟩` from `GlobalTheory.HeckeOne.entire_of_not_normPow hχ.1 hn`. Establish `h0 : Λ s ≠ 0` using `GlobalTheory.HeckePartial.IsHeckeL.ne_zero_of_one_le hχ.1 hn hΛ (by exact_mod_cast hs)`. Choose the witnesses or unpack the hypotheses as in `⟨P₀⟩ : Nonempty (HeightOneSpectrum (𝓞 D.host.E)) := by`. Take `⟨M, hM⟩` from `Ideal.exists_maximal (𝓞 D.host.E)`.

Conclude with `⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)⟩⟩`. Establish `t1` using `hL _ I φ hφ s κ 𝔣 ∅ χ (fun _ => P₀) Λ host_unramFin hs hb (fun _ h => absurd h (Finset.notMem_empty _)) hχ (fun _ h => absurd h (Finset.notMem_empty _)) hΛ`. Rewrite `t1` using `[Finset.filter_empty, Finset.prod_empty, mul_one, ← he]`. Use `Fintype.ofFinite (PicO (condQ 𝔣 (belowSet ∅)))` as an intermediate fact. Establish `e : Λ s = ∑ q, T q` using `t1.unique ((isToricSum_iff _ _ _ _ _ _).2 ⟨hfin, T, hT, (finsum_eq_sum_of_fintype _).symm⟩)`.

Introduce `hz`. Establish `h1` using `congrArg (algebraMap (FractionRing (X.O i)) (Kbar X i)) hz`. Rewrite `h1` using `[map_sum, map_zero, Finset.sum_congr rfl fun δ _ => hδ δ, ← Finset.mul_sum, ← map_sum]`. Use `mul_ne_zero hu ((map_ne_zero ι).2 ?_) h1` and prove the remaining obligations. Rewrite `h0` using `[e, ← Finset.sum_fiberwise Finset.univ (fun q => π q⁻¹)]`.

Use `h0 using 2 with δ` and compare the differences between its conclusion and the goal. Rewrite using `[show {q | π q⁻¹ = δ} = ↑(Finset.univ.filter fun q => π q⁻¹ = δ) by ext; simp, finsum_mem_coe_finset]`.
-/
theorem sum_ne_zero_at (hL : ToricSumFormula) {i : X.Tw} {ι : ℂ →+* Kbar X i} {lam : X.abelian₂ i} {s : ℕ}
    (ht : IsToricEltAt X i ι lam s) : ∑ δ, X.th i ∅ lam δ ≠ 0 := by
  classical
  have : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨I, _, φ, κ, 𝔣, χ, u, hD, h𝔣, -, hu, hth⟩ := ht
  obtain ⟨hfin, π, T, -, hT, hδ⟩ := hth ∅ (qOk_empty i)
  have he : belowSet (∅ : Finset (HeightOneSpectrum (𝓞 D.host.E))) = ∅ := Finset.image_empty _
  obtain ⟨hφ, -, hs, -, hb, hχ⟩ := hD
  have hn := not_isNormPow hb hχ
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.HeckeOne.entire_of_not_normPow hχ.1 hn
  have h0 : Λ s ≠ 0 := GlobalTheory.HeckePartial.IsHeckeL.ne_zero_of_one_le hχ.1 hn hΛ (by exact_mod_cast hs)
  obtain ⟨P₀⟩ : Nonempty (HeightOneSpectrum (𝓞 D.host.E)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.E)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)⟩⟩
  have t1 := hL _ I φ hφ s κ 𝔣 ∅ χ (fun _ => P₀) Λ host_unramFin hs hb (fun _ h => absurd h (Finset.notMem_empty _)) hχ
    (fun _ h => absurd h (Finset.notMem_empty _)) hΛ
  rw [Finset.filter_empty, Finset.prod_empty, mul_one, ← he] at t1
  have := Fintype.ofFinite (PicO (condQ 𝔣 (belowSet ∅)))
  have e : Λ s = ∑ q, T q :=
    t1.unique ((isToricSum_iff _ _ _ _ _ _).2 ⟨hfin, T, hT, (finsum_eq_sum_of_fintype _).symm⟩)
  intro hz
  have h1 := congrArg (algebraMap (FractionRing (X.O i)) (Kbar X i)) hz
  rw [map_sum, map_zero, Finset.sum_congr rfl fun δ _ => hδ δ, ← Finset.mul_sum, ← map_sum] at h1
  refine mul_ne_zero hu ((map_ne_zero ι).2 ?_) h1
  rw [e, ← Finset.sum_fiberwise Finset.univ (fun q => π q⁻¹)] at h0
  convert h0 using 2 with δ
  rw [show {q | π q⁻¹ = δ} = ↑(Finset.univ.filter fun q => π q⁻¹ = δ) by ext; simp, finsum_mem_coe_finset]

/- English proof (translation)
Take `⟨s, hs⟩` from `hs`. Take `⟨s, rfl⟩` from `Int.eq_ofNat_of_zero_le (le_trans zero_le_one hs.2.1)`. Take `⟨ι, -, hι⟩` from `ht i hi`. Conclude with `sum_ne_zero_at hL (hι lam s hs)`.
-/
theorem gen_sum_ne_zero (hL : ToricSumFormula) (ht : IsToricElt X) (i : X.Tw) (hi : X.NonzeroIndexPlace i) (lam : X.abelian₂ i)
    (hs : ∃ s : ℤ, BlochKatoReduction.Gen.SOk X i lam s) : ∑ δ, X.th i ∅ lam δ ≠ 0 := by
  obtain ⟨s, hs⟩ := hs
  obtain ⟨s, rfl⟩ := Int.eq_ofNat_of_zero_le (le_trans zero_le_one hs.2.1)
  obtain ⟨ι, -, hι⟩ := ht i hi
  exact sum_ne_zero_at hL (hι lam s hs)

/- English proof (translation)
Take `⟨N0, h⟩` from `exists_gen_bound X hB ht`. Conclude with `⟨N0, h, gen_relation hA hL ht, gen_sum_ne_zero hL ht⟩`.
-/
theorem gen_toric_properties (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hL : ToricSumFormula) (hB : ClassTermBound)
    (ht : IsToricElt X) :
    ∃ N0 : X.Tw → ℕ, BlochKatoReduction.Gen.adm9 X N0 ∧ BlochKatoReduction.Gen.adm10 X ∧
      ∀ i, X.NonzeroIndexPlace i → ∀ lam : X.abelian₂ i, (∃ s : ℤ, BlochKatoReduction.Gen.SOk X i lam s) → ∑ δ, X.th i ∅ lam δ ≠ 0 := by
  obtain ⟨N0, h⟩ := exists_gen_bound X hB ht
  exact ⟨N0, h, gen_relation hA hL ht, gen_sum_ne_zero hL ht⟩

end Record

/- English proof (translation)
The claim follows from `gen_toric_properties hA toricSumFormula hB ht`.
-/
theorem toric_properties_of_bound (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hB : ClassTermBound) (D : D7)
    (ht : IsToricElt D.ntw) :
    ∃ N0 : D.ntw.Tw → ℕ, BlochKatoReduction.adm9 D N0 ∧ BlochKatoReduction.adm10 D ∧
      ∀ i, D.ntw.NonzeroIndexPlace i → ∀ lam : D.ntw.abelian₂ i, (∃ s : ℤ, BlochKatoReduction.Gen.SOk D.ntw i lam s) → ∑ δ, D.ntw.th i ∅ lam δ ≠ 0 :=
  gen_toric_properties hA toricSumFormula hB ht

/- English proof (translation)
The claim follows from `toric_properties_of_bound hA (GlobalTheory.ToricDenomBridge.classTermBound_of_toricDenominator hB) D ht`.
-/
theorem toric_properties (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hB : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator) (D : D7)
    (ht : IsToricElt D.ntw) :
    ∃ N0 : D.ntw.Tw → ℕ, BlochKatoReduction.adm9 D N0 ∧ BlochKatoReduction.adm10 D ∧
      ∀ i, D.ntw.NonzeroIndexPlace i → ∀ lam : D.ntw.abelian₂ i, (∃ s : ℤ, BlochKatoReduction.Gen.SOk D.ntw i lam s) → ∑ δ, D.ntw.th i ∅ lam δ ≠ 0 :=
  toric_properties_of_bound hA (GlobalTheory.ToricDenomBridge.classTermBound_of_toricDenominator hB) D ht

end GlobalTheory.ToricAssembly
