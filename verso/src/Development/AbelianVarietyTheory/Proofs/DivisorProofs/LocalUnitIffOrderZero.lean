import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TmulMemLocId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedCompW
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt

noncomputable section

namespace GlobalTheory.TateUnits

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler GlobalTheory.LocIdeal
open GlobalTheory.Doubling (absE)
open Formalism.L2.Host (aboveF)
open GlobalTheory.TateUnr
open Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `h1` using `GlobalTheory.AutFunCompare.map_tensNU_self _ _ (singleFin_mul v) (evalV_singleFin_self v) y`. Use `set Y := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (singleFin v) (singleFin_mul v) y with hY`. Establish `h2 : ∀ u : HeightOneSpectrum (𝓞 E), finAdEquiv F E Y u ∈ Ov E u` using `fun u => by`. Distinguish the cases in `e : u.under (𝓞 F) = v`. Rewrite using `[finAdEquiv_apply e, h1]`.

Conclude with `hy u e`. Rewrite using `[finAdEquiv_apply rfl, GlobalTheory.AutFunCompare.map_tensNU_zero _ _ _ (evalV_singleFin_ne e), map_zero]`. Conclude with `zero_mem _`. Set `c` to `(Algebra.TensorProduct.comm F E (Af F)).toRingEquiv`. Establish `hι : ∀ x a, ((toFinAd F E).comp c.toRingHom) (x ⊗ₜ[F] a) = algebraMap E _ x * GlobalTheory.AdeleBaseChange.adMap F E a` using `fun x a => (toFinAd_tmul a x).trans (mul_comm _ _)`.

Establish `h4` using `GlobalTheory.AdeleBaseChange.mem_int_of_map hι (y := c.symm Y) fun u => by`. Express the relevant statement in the definitionally equal form `finAdEquiv F E (c (c.symm Y)) u ∈ _`. Rewrite using `[c.apply_symm_apply]`. Conclude with `h2 u`. Take `⟨m, g, hg⟩` from `Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)`.

Take `⟨r, hr, e⟩` from `P.levelaf_decomp g hg h4`. Rewrite using `[← h1, ← c.apply_symm_apply Y, e, map_sum, map_sum]`. Conclude with `sum_mem fun j _ => tmul_mem_intLoc (hr j v) (g j)`.
-/
theorem mem_intLoc_of_toCompl {v : HeightOneSpectrum (𝓞 F)} (y : Fv F v ⊗[F] E)
    (hy : ∀ (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), toCompl h y ∈ Ov E w) : y ∈ intLoc F E v := by
  have h1 := GlobalTheory.AutFunCompare.map_tensNU_self _ _ (singleFin_mul v) (evalV_singleFin_self v) y
  set Y := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (singleFin v) (singleFin_mul v) y with hY
  have h2 : ∀ u : HeightOneSpectrum (𝓞 E), finAdEquiv F E Y u ∈ Ov E u := fun u => by
    by_cases e : u.under (𝓞 F) = v
    · rw [finAdEquiv_apply e, h1]; exact hy u e
    · rw [finAdEquiv_apply rfl, GlobalTheory.AutFunCompare.map_tensNU_zero _ _ _ (evalV_singleFin_ne e), map_zero]
      exact zero_mem _
  let c := (Algebra.TensorProduct.comm F E (Af F)).toRingEquiv
  have hι : ∀ x a, ((toFinAd F E).comp c.toRingHom) (x ⊗ₜ[F] a) =
      algebraMap E _ x * GlobalTheory.AdeleBaseChange.adMap F E a := fun x a => (toFinAd_tmul a x).trans (mul_comm _ _)
  have h4 := GlobalTheory.AdeleBaseChange.mem_int_of_map hι (y := c.symm Y) fun u => by
    change finAdEquiv F E (c (c.symm Y)) u ∈ _
    rw [c.apply_symm_apply]
    exact h2 u
  obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
  obtain ⟨r, hr, e⟩ := P.levelaf_decomp g hg h4
  rw [← h1, ← c.apply_symm_apply Y, e, map_sum, map_sum]
  exact sum_mem fun j _ => tmul_mem_intLoc (hr j v) (g j)

/- English proof (translation)
Rewrite using `[← compW_apply]`. Express the relevant statement in the definitionally equal form `_ ∈ w.adicCompletionIntegers E ↔ _`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, valued_compW, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem toCompl_mem_Ov_iff {v : Pl F} (m : idelesAt E (evFin F v)) {w : HeightOneSpectrum (𝓞 E)}
    (hw : w.under (𝓞 F) = v) : toCompl hw (compFin F E v (m.1 : AE F E)) ∈ Ov E w ↔ 0 ≤ ordW hw m := by
  rw [← compW_apply]
  change _ ∈ w.adicCompletionIntegers E ↔ _
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_compW, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

/- English proof (translation)
The claim follows from `congrFun (ordV_inv v m) ⟨w, mem_aboveF.2 hw⟩`.
-/
theorem ordW_inv {v : Pl F} (m : idelesAt E (evFin F v)) {w : HeightOneSpectrum (𝓞 E)}
    (hw : w.under (𝓞 F) = v) : ordW hw m⁻¹ = -ordW hw m :=
  congrFun (ordV_inv v m) ⟨w, mem_aboveF.2 hw⟩

/- English proof (translation)
Rewrite using `[mem_unitsAt]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, h1, h2⟩`. Use function extensionality and compare the values at `⟨w, hw⟩`. Establish `a` using `(toCompl_mem_Ov_iff l (mem_aboveF.1 hw)).1 (InertChart.toCompl_mem _ h1)`.

Establish `b` using `(toCompl_mem_Ov_iff l⁻¹ (mem_aboveF.1 hw)).1 (InertChart.toCompl_mem _ h2)`. Rewrite `b` using `[ordW_inv]`. Express the relevant statement in the definitionally equal form `ordW (mem_aboveF.1 hw) l = 0`. Use linear arithmetic over natural numbers and integers. Introduce `h`.

Establish `h0 : ∀ (w : HeightOneSpectrum (𝓞 E)) (hw : w.under (𝓞 F) = v), ordW hw l = 0` using `fun w hw => congrFun h ⟨w, mem_aboveF.2 hw⟩`. Use `⟨l.2, mem_intLoc_of_toCompl _ fun w hw => ?_, mem_intLoc_of_toCompl _ fun w hw => ?_⟩` and prove the remaining obligations. Conclude with `(toCompl_mem_Ov_iff l hw).2 (h0 w hw).ge`. Use `(toCompl_mem_Ov_iff l⁻¹ hw).2 ?_` and prove the remaining obligations. Rewrite using `[ordW_inv, h0 w hw]`.

Conclude with `le_refl _`.
-/
theorem mem_unitsAt_iff_ordV_eq_zero (v : Pl F) (l : idelesAt E (evFin F v)) :
    l.1 ∈ unitsAt E v ↔ ordV v l = 0 := by
  rw [mem_unitsAt]
  constructor
  · rintro ⟨-, h1, h2⟩
    funext ⟨w, hw⟩
    have a := (toCompl_mem_Ov_iff l (mem_aboveF.1 hw)).1 (InertChart.toCompl_mem _ h1)
    have b := (toCompl_mem_Ov_iff l⁻¹ (mem_aboveF.1 hw)).1 (InertChart.toCompl_mem _ h2)
    rw [ordW_inv] at b
    change ordW (mem_aboveF.1 hw) l = 0
    omega
  · intro h
    have h0 : ∀ (w : HeightOneSpectrum (𝓞 E)) (hw : w.under (𝓞 F) = v), ordW hw l = 0 := fun w hw =>
      congrFun h ⟨w, mem_aboveF.2 hw⟩
    refine ⟨l.2, mem_intLoc_of_toCompl _ fun w hw => ?_, mem_intLoc_of_toCompl _ fun w hw => ?_⟩
    · exact (toCompl_mem_Ov_iff l hw).2 (h0 w hw).ge
    · refine (toCompl_mem_Ov_iff l⁻¹ hw).2 ?_
      rw [ordW_inv, h0 w hw]; exact le_refl _

end GlobalTheory.TateUnits

end
