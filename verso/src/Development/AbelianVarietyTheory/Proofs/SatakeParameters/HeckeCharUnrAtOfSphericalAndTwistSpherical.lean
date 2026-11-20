import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TranslateMemTwistedJacquetKernelRamifiedStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalTranslationCompCommutingOperatorStatement
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfRegularAlgebraicPolarizedP
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicHeckeCharSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.CsdTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharParallelWeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharAlgebraicOfSign
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory.SphTwistUnr

open GlobalTheory.PRep

/- English proof (translation)
Establish `h : (twKer ρ K 1).map S ≤ twKer ρ K 1`. Rewrite using `[twKer, Submodule.map_span_le]`. Introduce and unpack `_ ⟨n, u, rfl⟩`. Use `Submodule.subset_span ⟨n, S u, ?_⟩` and prove the remaining obligations. Use `LinearMap.congr_fun (hS n) u` as an intermediate fact.

Simplify using `only [LinearMap.comp_apply] at this`. Simplify using `[this]`. Conclude with `h ⟨v, hv, rfl⟩`.
-/
theorem map_mem_twKer {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G}
    (S : V →ₗ[ℂ] V) (hS : ∀ h, S ∘ₗ ρ h = ρ h ∘ₗ S) {v : V} (hv : v ∈ twKer ρ K 1) : S v ∈ twKer ρ K 1 := by
  have h : (twKer ρ K 1).map S ≤ twKer ρ K 1 := by
    rw [twKer, Submodule.map_span_le]
    rintro _ ⟨n, u, rfl⟩
    refine Submodule.subset_span ⟨n, S u, ?_⟩
    have := LinearMap.congr_fun (hS n) u
    simp only [LinearMap.comp_apply] at this
    simp [this]
  exact h ⟨v, hv, rfl⟩

/- English proof (translation)
Introduce `E _ _ _ a ha π ξ w hB hsph`. Take `⟨B, hB⟩` from `hB`. Establish `hS : GlobalTheory.LFun.HasSatGL w (π.locRep w) B` using `(CG.hasSat_mk π w B).1 hB`. Establish `hK : IsCompact ((GlobalTheory.LFun.KGL w a : Subgroup _) : Set (GL (Fin a) (w.adicCompletion E)))` using `(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2`. Establish `hsm : IsSmooth (π.locRep w)` using `π.isSmooth_locRep w`.

Take `⟨x, hx, hx0⟩` from `(Submodule.ne_bot_iff _).1 hS.1`. Take `⟨z, hz, hz0⟩` from `(Submodule.ne_bot_iff _).1 hsph`. Establish `hT : ∀ g v, (π.twist ξ).locRep w g (π.toTwist ξ v) = ((ξ.loc w (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • π.toTwist ξ (π.locRep w g v)`. Introduce `g v`. Rewrite using `[CuspSub.locRep_eq, CuspSub.op_toTwist, opAdd, zero_smul, add_zero, map_smul, opMul, CuspSub.chiDet_locGL]`.

Both sides reduce to the same expression. Take `⟨y, rfl⟩` from `(π.toTwist ξ).surjective z`. Establish `hy0 : y ≠ 0` using `fun h => hz0 (by rw [h, map_zero])`. Establish `hy : ∀ k ∈ GlobalTheory.LFun.KGL w a, π.locRep w k y = (((ξ.loc w (Matrix.GeneralLinearGroup.det k))⁻¹ : ℂˣ) : ℂ) • y`. Introduce `k hk`.

Establish `h1` using `GlobalTheory.LGrp.mem_fixed.1 hz k hk`. Rewrite `h1` using `[hT]`. Apply `(π.toTwist ξ).injective` to reduce the goal to its premises. Rewrite using `[map_smul, ← h1, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]`. Assume the negation of the conclusion as `hne`.

Choose the witnesses or unpack the hypotheses as in `⟨u, hu, hξu⟩ : ∃ u, Formalism.L2.Host.IsUnitAt w u ∧ ξ.loc w u ≠ 1 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hne h`. Establish `hall` using `GlobalTheory.T.translate_mem_twistedJacquetKernel_ramified E w a π.V (π.locRep w) (ξ.loc w) u ha hu hξu y hy`.

Set `Wl : Submodule ℂ π.V` to `⨅ g, (twKer (π.locRep w) (GlobalTheory.LFun.KGL w a) 1).comap (π.locRep w g)`. Establish `memWl : ∀ v, v ∈ Wl ↔ ∀ g, π.locRep w g v ∈ twKer (π.locRep w) (GlobalTheory.LFun.KGL w a) 1` using `fun v => by`. Simplify using `[Wl, Submodule.mem_iInf]`. Establish `stab : GlobalTheory.CuspRep.IsStable (Wl.map π.V.subtype)`. Introduce and unpack `o _ ⟨v, hv, rfl⟩`.

Take `⟨g, S, hS, ho⟩` from `GlobalTheory.T.exists_localTranslation_comp_commuting_operator E a π w o`. Establish `hv'` using `(memWl v).1 hv`. Use `⟨π.op o v, (memWl _).2 fun h => ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[ho, LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul]`. Establish `e` using `LinearMap.congr_fun (hS (h * g)) v`.

Simplify using `only [LinearMap.comp_apply] at e`. Rewrite using `[← e]`. Conclude with `map_mem_twKer S hS (hv' (h * g))`. Break down `π.irred _ (Submodule.map_subtype_le _ _) stab with h | h` into its components or cases. Establish `h1 : (y : GlobalTheory.CuspRep.Sm E a) ∈ Wl.map π.V.subtype` using `⟨y, (memWl y).2 hall, rfl⟩`.

Rewrite `h1` using `[h, Submodule.mem_bot]`. Conclude with `hy0 (Subtype.ext h1)`. Establish `h1 : (x : GlobalTheory.CuspRep.Sm E a) ∈ Wl.map π.V.subtype` using `by rw [h]; exact x.2`. Take `⟨x', hx', e⟩` from `h1`. Take `rfl : x' = x` from `Subtype.ext e`.

Establish `h2` using `(memWl x').1 hx' 1`. Rewrite `h2` using `[map_one, Module.End.one_apply]`. Conclude with `hx0 (Submodule.disjoint_def.1 (GlobalTheory.LocGL.isCompl_fixed_twKer hsm hK).disjoint x' hx h2)`.
-/
theorem unrAt_of_isSpherical_twist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (ξ : HChar E) (w : HeightOneSpectrum (𝓞 E)), (∃ B, (CG.mk π).HasSat w B) → GlobalTheory.LGrp.IsSpherical ((π.twist ξ).locRep w) (GlobalTheory.LFun.KGL w a) → ξ.UnrAt w := by
  intro E _ _ _ a ha π ξ w hB hsph
  obtain ⟨B, hB⟩ := hB
  have hS : GlobalTheory.LFun.HasSatGL w (π.locRep w) B := (CG.hasSat_mk π w B).1 hB
  have hK : IsCompact ((GlobalTheory.LFun.KGL w a : Subgroup _) : Set (GL (Fin a) (w.adicCompletion E))) :=
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2
  have hsm : IsSmooth (π.locRep w) := π.isSmooth_locRep w
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hS.1
  obtain ⟨z, hz, hz0⟩ := (Submodule.ne_bot_iff _).1 hsph
  have hT : ∀ g v, (π.twist ξ).locRep w g (π.toTwist ξ v) =
      ((ξ.loc w (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • π.toTwist ξ (π.locRep w g v) := by
    intro g v
    rw [CuspSub.locRep_eq, CuspSub.op_toTwist, opAdd, zero_smul, add_zero, map_smul, opMul, CuspSub.chiDet_locGL]
    rfl
  obtain ⟨y, rfl⟩ := (π.toTwist ξ).surjective z
  have hy0 : y ≠ 0 := fun h => hz0 (by rw [h, map_zero])
  have hy : ∀ k ∈ GlobalTheory.LFun.KGL w a, π.locRep w k y =
      (((ξ.loc w (Matrix.GeneralLinearGroup.det k))⁻¹ : ℂˣ) : ℂ) • y := by
    intro k hk
    have h1 := GlobalTheory.LGrp.mem_fixed.1 hz k hk
    rw [hT] at h1
    apply (π.toTwist ξ).injective
    rw [map_smul, ← h1, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  by_contra hne
  obtain ⟨u, hu, hξu⟩ : ∃ u, Formalism.L2.Host.IsUnitAt w u ∧ ξ.loc w u ≠ 1 := by
    by_contra h
    push_neg at h
    exact hne h
  have hall := GlobalTheory.T.translate_mem_twistedJacquetKernel_ramified E w a π.V (π.locRep w) (ξ.loc w) u ha hu hξu y hy
  let Wl : Submodule ℂ π.V := ⨅ g, (twKer (π.locRep w) (GlobalTheory.LFun.KGL w a) 1).comap (π.locRep w g)
  have memWl : ∀ v, v ∈ Wl ↔ ∀ g, π.locRep w g v ∈ twKer (π.locRep w) (GlobalTheory.LFun.KGL w a) 1 := fun v => by
    simp [Wl, Submodule.mem_iInf]
  have stab : GlobalTheory.CuspRep.IsStable (Wl.map π.V.subtype) := by
    rintro o _ ⟨v, hv, rfl⟩
    obtain ⟨g, S, hS, ho⟩ := GlobalTheory.T.exists_localTranslation_comp_commuting_operator E a π w o
    have hv' := (memWl v).1 hv
    refine ⟨π.op o v, (memWl _).2 fun h => ?_, rfl⟩
    rw [ho, LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul]
    have e := LinearMap.congr_fun (hS (h * g)) v
    simp only [LinearMap.comp_apply] at e
    rw [← e]
    exact map_mem_twKer S hS (hv' (h * g))
  rcases π.irred _ (Submodule.map_subtype_le _ _) stab with h | h
  · have h1 : (y : GlobalTheory.CuspRep.Sm E a) ∈ Wl.map π.V.subtype := ⟨y, (memWl y).2 hall, rfl⟩
    rw [h, Submodule.mem_bot] at h1
    exact hy0 (Subtype.ext h1)
  · have h1 : (x : GlobalTheory.CuspRep.Sm E a) ∈ Wl.map π.V.subtype := by rw [h]; exact x.2
    obtain ⟨x', hx', e⟩ := h1
    obtain rfl : x' = x := Subtype.ext e
    have h2 := (memWl x').1 hx' 1
    rw [map_one, Module.End.one_apply] at h2
    exact hx0 (Submodule.disjoint_def.1 (GlobalTheory.LocGL.isCompl_fixed_twKer hsm hK).disjoint x' hx h2)

end GlobalTheory.SphTwistUnr
