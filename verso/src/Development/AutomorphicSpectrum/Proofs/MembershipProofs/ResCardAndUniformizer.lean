import Mathlib
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.SwapCApply
import GroundTheory.GlobalFields.LocalFieldAtPlace
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix ValuativeRel NumberField IsDedekindDomain GlobalTheory.CompanionTheory.IdxAd
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.IdxAd.Unif

/- English proof (translation)
Introduce `F _ _ v`. Establish `hS : (Valuation.integer (ValuativeRel.valuation (v.adicCompletion F))) = (v.adicCompletionIntegers F).toSubring`. Use extensionality with `x`. Conclude with `GroundTheory.Global.mem_valuationInteger_iff v x`. Set `e : 𝒪[v.adicCompletion F] ≃+* v.adicCompletionIntegers F` to `RingEquiv.subringCongr hS`.

Establish `hle : ∀ {x : v.adicCompletion F}, Valued.v x ≤ 1 → x ∈ 𝒪[v.adicCompletion F]` using `fun hx => (GroundTheory.Global.mem_valuationInteger_iff v _).2 ((HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F v).2 hx)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h` using `GroundTheory.Global.natCard_residueField_adicCompletionIntegers (K := F) v`. Rewrite using `[← h]`. Conclude with `Nat.card_congr (IsLocalRing.ResidueField.mapEquiv e).toEquiv`.

Take `⟨q, hq⟩` from `IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)`. Establish `hval : Valued.v (q : v.adicCompletion F) = WithZero.exp (-1 : ℤ)` using `GroundTheory.Global.valued_of_irreducible v hq`. Establish `hq0 : (q : v.adicCompletion F) ≠ 0` using `fun h => hq.ne_zero (Subtype.ext h)`. Establish `hp : Irreducible (e.symm q)` using `(MulEquiv.irreducible_iff e.symm).2 hq`. Use `⟨Units.mk0 _ hq0, ⟨_, hp, rfl⟩, fun t => ?_⟩` and prove the remaining obligations.

Establish `ht : Valued.v (t : v.adicCompletion F) ≠ 0` using `(Valued.v).ne_zero_iff.2 t.ne_zero`. Use `set a : ℤ := - WithZero.log (Valued.v (t : v.adicCompletion F)) with ha`. Establish `hu : Valued.v (((t * (Units.mk0 _ hq0) ^ (-a) : (v.adicCompletion F)ˣ)) : v.adicCompletion F) = 1`. Rewrite using `[Units.val_mul, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, Units.val_mk0, hval, ← WithZero.exp_zsmul, ← WithZero.exp_log ht, ← WithZero.exp_add, smul_eq_mul, ha]`. Simplify using the standard rewrite rules.

Use `⟨a, t * (Units.mk0 _ hq0) ^ (-a), hle hu.le, hle ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]`. Simplify using `[mul_assoc]`. Rewrite using `[ha, Int.natAbs_neg]`.
-/
theorem resCard_and_uniformizer : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), GlobalTheory.SplitWeil.resCard (v.adicCompletion F) = Ideal.absNorm v.asIdeal ∧ ∃ ϖ : (v.adicCompletion F)ˣ, (∃ p : 𝒪[v.adicCompletion F], Irreducible p ∧ (p : v.adicCompletion F) = ϖ) ∧ ∀ t : (v.adicCompletion F)ˣ, ∃ (a : ℤ) (u : (v.adicCompletion F)ˣ), (u : v.adicCompletion F) ∈ 𝒪[v.adicCompletion F] ∧ ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ 𝒪[v.adicCompletion F] ∧ t = u * ϖ ^ a ∧ a.natAbs = (WithZero.log (Valued.v (t : v.adicCompletion F))).natAbs := by
  intro F _ _ v
  have hS : (Valuation.integer (ValuativeRel.valuation (v.adicCompletion F))) =
      (v.adicCompletionIntegers F).toSubring := by
    ext x
    exact GroundTheory.Global.mem_valuationInteger_iff v x
  let e : 𝒪[v.adicCompletion F] ≃+* v.adicCompletionIntegers F := RingEquiv.subringCongr hS
  have hle : ∀ {x : v.adicCompletion F}, Valued.v x ≤ 1 → x ∈ 𝒪[v.adicCompletion F] := fun hx =>
    (GroundTheory.Global.mem_valuationInteger_iff v _).2
      ((HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F v).2 hx)
  refine ⟨?_, ?_⟩
  · have h := GroundTheory.Global.natCard_residueField_adicCompletionIntegers (K := F) v
    rw [← h]
    exact Nat.card_congr (IsLocalRing.ResidueField.mapEquiv e).toEquiv
  · obtain ⟨q, hq⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)
    have hval : Valued.v (q : v.adicCompletion F) = WithZero.exp (-1 : ℤ) :=
      GroundTheory.Global.valued_of_irreducible v hq
    have hq0 : (q : v.adicCompletion F) ≠ 0 := fun h => hq.ne_zero (Subtype.ext h)
    have hp : Irreducible (e.symm q) :=
      (MulEquiv.irreducible_iff e.symm).2 hq
    refine ⟨Units.mk0 _ hq0, ⟨_, hp, rfl⟩, fun t => ?_⟩
    have ht : Valued.v (t : v.adicCompletion F) ≠ 0 :=
      (Valued.v).ne_zero_iff.2 t.ne_zero
    set a : ℤ := - WithZero.log (Valued.v (t : v.adicCompletion F)) with ha
    have hu : Valued.v (((t * (Units.mk0 _ hq0) ^ (-a) : (v.adicCompletion F)ˣ)) :
        v.adicCompletion F) = 1 := by
      rw [Units.val_mul, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, Units.val_mk0, hval,
        ← WithZero.exp_zsmul, ← WithZero.exp_log ht, ← WithZero.exp_add, smul_eq_mul, ha]
      simp
    refine ⟨a, t * (Units.mk0 _ hq0) ^ (-a), hle hu.le, hle ?_, ?_, ?_⟩
    · rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
    · simp [mul_assoc]
    · rw [ha, Int.natAbs_neg]

end GlobalTheory.CompanionTheory.IdxAd.Unif
