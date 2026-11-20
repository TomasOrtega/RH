import Mathlib
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValIotaLeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingClassGroupOfConductorNeZero

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.Euler

/- English proof (translation)
Introduce `E _ _ c hc`. Set `U : Subgroup (Af E)ˣ` to `(PicFin.intR E).toSubmonoid.units`. Establish `h1 : ((hatOUnits c).subgroupOf U).FiniteIndex` using `PicFin.finiteIndex_units hc`. Establish `h2 : Finite (U ⧸ (hatOUnits c).subgroupOf U)` using `Subgroup.finite_quotient_of_finiteIndex`. Use `Fintype.ofFinite (U ⧸ (hatOUnits c).subgroupOf U)` as an intermediate fact.

Use `⟨Finset.univ.image fun q : U ⧸ (hatOUnits c).subgroupOf U => (q.out : U).1, fun y hy => ?_⟩` and prove the remaining obligations. Establish `hyU : y ∈ U` using `(Submonoid.mem_units_iff _ _).2 ⟨fun v => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hy v).le, fun v => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (by rw [inv_coord, map_inv₀, hy v, inv_one])⟩`. Use `⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (QuotientGroup.mk ⟨y, hyU⟩)), ?_⟩` and prove the remaining obligations. Establish `h3` using `(QuotientGroup.eq (s := (hatOUnits c).subgroupOf U)).1 (QuotientGroup.out_eq' (QuotientGroup.mk ⟨y, hyU⟩ : U ⧸ (hatOUnits c).subgroupOf U))`. Conclude with `Subgroup.mem_subgroupOf.1 h3`.
-/
theorem exists_finset_cover_units : ∀ (E : Type) [Field E] [NumberField E] (c : Ideal (OF E)), c ≠ ⊥ →
    ∃ R : Finset (Af E)ˣ, ∀ y : (Af E)ˣ, (∀ w, Valued.v ((y : Af E) w) = 1) → ∃ r ∈ R, r⁻¹ * y ∈ hatOUnits c := by
  classical
  intro E _ _ c hc
  let U : Subgroup (Af E)ˣ := (PicFin.intR E).toSubmonoid.units
  have h1 : ((hatOUnits c).subgroupOf U).FiniteIndex := PicFin.finiteIndex_units hc
  have h2 : Finite (U ⧸ (hatOUnits c).subgroupOf U) := Subgroup.finite_quotient_of_finiteIndex
  have := Fintype.ofFinite (U ⧸ (hatOUnits c).subgroupOf U)
  refine ⟨Finset.univ.image fun q : U ⧸ (hatOUnits c).subgroupOf U => (q.out : U).1, fun y hy => ?_⟩
  have hyU : y ∈ U := (Submonoid.mem_units_iff _ _).2
    ⟨fun v => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hy v).le,
     fun v => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2
      (by rw [inv_coord, map_inv₀, hy v, inv_one])⟩
  refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (QuotientGroup.mk ⟨y, hyU⟩)), ?_⟩
  have h3 := (QuotientGroup.eq (s := (hatOUnits c).subgroupOf U)).1
    (QuotientGroup.out_eq' (QuotientGroup.mk ⟨y, hyU⟩ : U ⧸ (hatOUnits c).subgroupOf U))
  exact Subgroup.mem_subgroupOf.1 h3

end GlobalTheory.CMVal.Euler
