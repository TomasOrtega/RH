import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniTrait
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsFinExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointsAlgClosureFractionRingBijective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

open GlobalTheory.ArcPull GlobalTheory.TorusExt

/- English proof (translation)
Introduce `R₁ _ _ _ hR D₁ n hn`. Establish `hL : Laws` using `GlobalTheory.firstFiveLaws.1`. Establish `hG` using `hL.globalFns`. Establish `hB₁` using `D₁.tau_bimult`. Use `hR.2` as an intermediate fact.

Establish `: CharZero (Kb R₁)` using `(RingHom.charZero_iff (algebraMap (FractionRing R₁) (Kb R₁)).injective).1 inferInstance`. Take `⟨M, hM, H⟩` from `GlobalTheory.QkNumberField.exists_finite_qk (D := D₁.toPre) (L := Kb R₁) hL hB₁ (N := n) (Nat.cast_ne_zero.2 (by omega))`. Use `⟨M, hM, ?_⟩` and prove the remaining obligations. Introduce `R₂ _ _ _ i₁₂ e hfin _ he D₂ ⟨hD⟩ p`. Establish `hB₂` using `D₂.tau_bimult`.

Establish `hi : Function.Injective i₁₂` using `hfin.2.1`. Use `letI : Algebra (FractionRing R₁) (FractionRing R₂) := (fracMap hi).toAlgebra`. Establish `he' : e.comp (algebraMap (FractionRing R₁) M) = algebraMap (FractionRing R₁) (FractionRing R₂)` using `IsLocalization.ringHom_ext (nonZeroDivisors R₁) (RingHom.ext fun r => (he r).trans (fracMap_algebraMap hi r).symm)`. Use `letI : Algebra (FractionRing R₁) (Kb R₂) := ((algebraMap (FractionRing R₂) (Kb R₂)).comp (fracMap hi)).toAlgebra`. Establish `cK : Compat i₁₂ (Kb R₂)` using `fun r => congrArg (algebraMap (FractionRing R₂) (Kb R₂)) (fracMap_algebraMap hi r)`.

Establish `cF : Compat i₁₂ (FractionRing R₂)` using `fracMap_algebraMap hi`. Use `letI : Algebra M (Kb R₂) := ((algebraMap (FractionRing R₂) (Kb R₂)).comp e).toAlgebra`. Use `haveI : Module.IsTorsionFree M (Kb R₂) := DivisionSemiring.to_moduleIsTorsionFree`. Use `haveI : Module.IsTorsionFree M (Kb R₁) := DivisionSemiring.to_moduleIsTorsionFree`. Use `haveI : Algebra.IsAlgebraic M (Kb R₁) := Algebra.IsAlgebraic.tower_top (K := FractionRing R₁) M`.

Set `σ' : Kb R₁ →ₐ[M] Kb R₂` to `IsAlgClosed.lift`. Establish `hσ' : ∀ m : M, σ' (m : Kb R₁) = algebraMap (FractionRing R₂) (Kb R₂) (e m)` using `fun m => σ'.commutes m`. Set `σ : Kb R₁ →ₐ[FractionRing R₁] Kb R₂` to `⟨σ'.toRingHom, fun x => by show σ' (algebraMap (FractionRing R₁) (Kb R₁) x) = _`. Conclude with `(hσ' (algebraMap (FractionRing R₁) M x)).trans (congrArg (algebraMap (FractionRing R₂) (Kb R₂)) (RingHom.congr_fun he' x))⟩`. Establish `key : σ.toRingHom.comp M.val.toRingHom = (algebraMap (FractionRing R₂) (Kb R₂)).comp e` using `RingHom.ext fun m => hσ' m`.

Take `⟨q, rfl⟩` from `pullQk_surjective hD hG cK hB₁ hB₂ p`. Take `⟨q₀, hq₀⟩` from `GlobalTheory.LabTrans.exists_of_ext hB₁ σ hn q`. Take `⟨z, rfl⟩` from `H n dvd_rfl q₀`. Set `z' : QkPt D₁.toPre (FractionRing R₂) n` to `qkExt hB₁ e he' z`. Set `p₀` to `pullQk hD hG cF hB₁ hB₂ z'`.

Set `p₁` to `qkExt hB₂ (algebraMap (FractionRing R₂) (Kb R₂)) (RingHom.comp_id _) p₀`. Establish `hp₁ : QkExt (algebraMap (FractionRing R₂) (Kb R₂)) p₀ p₁` using `(qkExt_iff hB₂ _ _ _ _).2 rfl`. Establish `hf₂ : (algebraMap (FractionRing R₂) (Kb R₂)).comp (algebraMap (FractionRing R₁) (FractionRing R₂)) = algebraMap (FractionRing R₁) (Kb R₂)` using `rfl`. Set `w` to `qkExt hB₁ (algebraMap (FractionRing R₂) (Kb R₂)) hf₂ z'`. Establish `hw : QkExt (algebraMap (FractionRing R₂) (Kb R₂)) z' w` using `(qkExt_iff hB₁ _ _ _ _).2 rfl`.

Establish `hz' : QkExt e z z'` using `(qkExt_iff hB₁ _ _ _ _).2 rfl`. Establish `hz : QkExt M.val.toRingHom z (qkExt hB₁ M.val.toRingHom (GlobalTheory.QkNumberField.val_comp M) z)` using `(qkExt_iff hB₁ _ _ _ _).2 rfl`. Establish `t₁` using `GlobalTheory.LabTrans.qkExt_trans hz hq₀`. Establish `t₂` using `GlobalTheory.LabTrans.qkExt_trans hz' hw`. Rewrite `t₂` using `[← key]`.

Establish `hqw : q = w` using `GlobalTheory.QkClosure.qkExt_unique (σ.toRingHom.comp M.val.toRingHom) (σ.comp_algebraMap ▸ rfl) t₁ t₂`. Use `⟨p₀, p₁, hp₁, ?_⟩` and prove the remaining obligations. Establish `e₁ : p₁ = pullQk hD hG cK hB₁ hB₂ q`. Rewrite using `[eq_pullQk_iff]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hqw]`. Both sides reduce to the same expression. Rewrite using `[hqw]`. Conclude with `isPullGtF_ext hD cK _ (RingHom.comp_id _) (isPullGtF_pullGt hD hG cF z'.g) hw hp₁`. Rewrite using `[e₁]`.

Conclude with `qk_equiv_refl hB₂ _`.
-/
theorem qkPt_rational_of_pull : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], Base R₁ → ∀ (D₁ : DegData R₁ (maximalIdeal R₁)) (n : ℕ), 1 ≤ n → ∃ E : IntermediateField (FractionRing R₁) (Kb R₁), FiniteDimensional (FractionRing R₁) E ∧ ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (i₁₂ : R₁ →+* R₂) (e : E →+* FractionRing R₂), FinExt i₁₂ → IsLocalHom i₁₂ → (∀ r : R₁, e (algebraMap (FractionRing R₁) E (algebraMap R₁ (FractionRing R₁) r)) = algebraMap R₂ (FractionRing R₂) (i₁₂ r)) → ∀ (D₂ : DegData R₂ (maximalIdeal R₂)), Nonempty (IsPullDeg i₁₂ D₁.toPre D₂.toPre) → ∀ p : QkPt D₂.toPre (Kb R₂) n, ∃ (p₀ : QkPt D₂.toPre (FractionRing R₂) n) (p₁ : QkPt D₂.toPre (Kb R₂) n), QkExt (algebraMap (FractionRing R₂) (Kb R₂)) p₀ p₁ ∧ QkPt.Equiv D₂.toPre (Kb R₂) p₁ p := by
  intro R₁ _ _ _ hR D₁ n hn
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hG := hL.globalFns
  have hB₁ := D₁.tau_bimult
  have := hR.2
  have : CharZero (Kb R₁) := (RingHom.charZero_iff (algebraMap (FractionRing R₁) (Kb R₁)).injective).1 inferInstance
  obtain ⟨M, hM, H⟩ := GlobalTheory.QkNumberField.exists_finite_qk (D := D₁.toPre) (L := Kb R₁) hL hB₁ (N := n)
    (Nat.cast_ne_zero.2 (by omega))
  refine ⟨M, hM, ?_⟩
  intro R₂ _ _ _ i₁₂ e hfin _ he D₂ ⟨hD⟩ p
  have hB₂ := D₂.tau_bimult
  have hi : Function.Injective i₁₂ := hfin.2.1
  letI : Algebra (FractionRing R₁) (FractionRing R₂) := (fracMap hi).toAlgebra
  have he' : e.comp (algebraMap (FractionRing R₁) M) = algebraMap (FractionRing R₁) (FractionRing R₂) :=
    IsLocalization.ringHom_ext (nonZeroDivisors R₁) (RingHom.ext fun r => (he r).trans (fracMap_algebraMap hi r).symm)
  letI : Algebra (FractionRing R₁) (Kb R₂) := ((algebraMap (FractionRing R₂) (Kb R₂)).comp (fracMap hi)).toAlgebra
  have cK : Compat i₁₂ (Kb R₂) := fun r => congrArg (algebraMap (FractionRing R₂) (Kb R₂)) (fracMap_algebraMap hi r)
  have cF : Compat i₁₂ (FractionRing R₂) := fracMap_algebraMap hi
  letI : Algebra M (Kb R₂) := ((algebraMap (FractionRing R₂) (Kb R₂)).comp e).toAlgebra
  haveI : Module.IsTorsionFree M (Kb R₂) := DivisionSemiring.to_moduleIsTorsionFree
  haveI : Module.IsTorsionFree M (Kb R₁) := DivisionSemiring.to_moduleIsTorsionFree
  haveI : Algebra.IsAlgebraic M (Kb R₁) := Algebra.IsAlgebraic.tower_top (K := FractionRing R₁) M
  let σ' : Kb R₁ →ₐ[M] Kb R₂ := IsAlgClosed.lift
  have hσ' : ∀ m : M, σ' (m : Kb R₁) = algebraMap (FractionRing R₂) (Kb R₂) (e m) := fun m => σ'.commutes m
  let σ : Kb R₁ →ₐ[FractionRing R₁] Kb R₂ := ⟨σ'.toRingHom, fun x => by
    show σ' (algebraMap (FractionRing R₁) (Kb R₁) x) = _
    exact (hσ' (algebraMap (FractionRing R₁) M x)).trans (congrArg (algebraMap (FractionRing R₂) (Kb R₂)) (RingHom.congr_fun he' x))⟩
  have key : σ.toRingHom.comp M.val.toRingHom = (algebraMap (FractionRing R₂) (Kb R₂)).comp e :=
    RingHom.ext fun m => hσ' m
  obtain ⟨q, rfl⟩ := pullQk_surjective hD hG cK hB₁ hB₂ p
  obtain ⟨q₀, hq₀⟩ := GlobalTheory.LabTrans.exists_of_ext hB₁ σ hn q
  obtain ⟨z, rfl⟩ := H n dvd_rfl q₀
  let z' : QkPt D₁.toPre (FractionRing R₂) n := qkExt hB₁ e he' z
  let p₀ := pullQk hD hG cF hB₁ hB₂ z'
  let p₁ := qkExt hB₂ (algebraMap (FractionRing R₂) (Kb R₂)) (RingHom.comp_id _) p₀
  have hp₁ : QkExt (algebraMap (FractionRing R₂) (Kb R₂)) p₀ p₁ := (qkExt_iff hB₂ _ _ _ _).2 rfl
  have hf₂ : (algebraMap (FractionRing R₂) (Kb R₂)).comp (algebraMap (FractionRing R₁) (FractionRing R₂)) =
      algebraMap (FractionRing R₁) (Kb R₂) := rfl
  let w := qkExt hB₁ (algebraMap (FractionRing R₂) (Kb R₂)) hf₂ z'
  have hw : QkExt (algebraMap (FractionRing R₂) (Kb R₂)) z' w := (qkExt_iff hB₁ _ _ _ _).2 rfl
  have hz' : QkExt e z z' := (qkExt_iff hB₁ _ _ _ _).2 rfl
  have hz : QkExt M.val.toRingHom z (qkExt hB₁ M.val.toRingHom (GlobalTheory.QkNumberField.val_comp M) z) :=
    (qkExt_iff hB₁ _ _ _ _).2 rfl
  have t₁ := GlobalTheory.LabTrans.qkExt_trans hz hq₀
  have t₂ := GlobalTheory.LabTrans.qkExt_trans hz' hw
  rw [← key] at t₂
  have hqw : q = w := GlobalTheory.QkClosure.qkExt_unique (σ.toRingHom.comp M.val.toRingHom) (σ.comp_algebraMap ▸ rfl) t₁ t₂
  refine ⟨p₀, p₁, hp₁, ?_⟩
  have e₁ : p₁ = pullQk hD hG cK hB₁ hB₂ q := by
    rw [eq_pullQk_iff]
    refine ⟨?_, ?_⟩
    · rw [hqw]; rfl
    · rw [hqw]
      exact isPullGtF_ext hD cK _ (RingHom.comp_id _) (isPullGtF_pullGt hD hG cF z'.g) hw hp₁
  rw [e₁]
  exact qk_equiv_refl hB₂ _

end GlobalTheory.Mum
