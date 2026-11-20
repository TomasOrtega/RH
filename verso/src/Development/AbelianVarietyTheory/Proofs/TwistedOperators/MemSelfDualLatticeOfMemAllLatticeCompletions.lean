import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticesAgreeAlmostEverywhere
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlacesIffPlaceSetProd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionEqOfLocalAgreement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionAtPlacesMemCompletedHermitianLa
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationEqStdAtOfCongruentOneAtPrime

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.FinPl.LocGlob

variable {D : D7}

/- English proof (translation)
Establish `h1 : finPart D ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] e) = α ⊗ₜ[D.host.F] e`. Unfold `finPart`. Rewrite using `[AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]`. Both sides reduce to the same expression. Rewrite using `[h1]`.

Both sides reduce to the same expression.
-/
theorem swap_finPart_pure (α : Af D.host.F) (e : D.host.E) :
    Formalism.IndefR.Lev.swapAE D (finPart D ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] e)) = e ⊗ₜ[D.host.F] α := by
  have h1 : finPart D ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] e) = α ⊗ₜ[D.host.F] e := by
    unfold finPart
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
    rfl
  rw [h1]
  rfl

/- English proof (translation)
Establish `hlat` using `hL.1`. Take `⟨d, hd, hdz⟩` from `GlobalTheory.FinPl.exists_int_smul_le (Submodule.span (𝓞 D.host.E) {z}) L (Submodule.fg_span_singleton z) hlat.span_eq_top`. Use `set T := (GlobalTheory.FinPl.finite_places_int (D := D) d hd).toFinset with hT`. Use `set β : Af D.host.F := 1 - ∑ v ∈ T, GlobalTheory.FinPl.LatMem.indP D.host.F (· = v) with hβ`. Establish `hβv : ∀ w, evalV D.host.F w β = if w ∈ T then 0 else 1`.

Introduce `w`. Rewrite using `[hβ, map_sub, map_one, map_sum]`. Simplify using `only [GlobalTheory.FinPl.LatMem.evalV_indP]`. Rewrite using `[Finset.sum_ite_eq]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hoff : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] ((1 : D.host.E) * z i)) ∈ GlobalTheory.FinPl.latV S L (fun w => w ∉ T)`. Apply `GlobalTheory.FinPl.LocAgree.latV_le_of_int_smul_on S (Submodule.span (𝓞 D.host.E) {z}) L d hd hdz` to reduce the goal to its premises. Introduce `v hv hmem`. Conclude with `hv ((Set.Finite.mem_toFinset _).2 hmem)`. Apply `AddSubgroup.subset_closure` to reduce the goal to its premises.

Use `⟨β, fun w => ?_, fun w hw => ?_, 1, rfl, z, Submodule.mem_span_singleton_self z, rfl⟩` and prove the remaining obligations. Rewrite using `[hβv] split_ifs`. Conclude with `zero_mem _`. Conclude with `one_mem _`. Rewrite using `[hβv, if_pos (not_not.1 hw)]`.

Establish `hall : (fun i => pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i) ∈ GlobalTheory.FinPl.latV S L (fun _ => True)`. Establish `e : (fun i => pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i) = ∑ v ∈ T, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) + (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] ((1 : D.host.E) * z i))`. Use function extensionality and compare the values at `i`. Rewrite using `[Pi.add_apply, Finset.sum_apply, one_mul, ← TensorProduct.sum_tmul, ← TensorProduct.add_tmul]`. Use `congr 1`.

Establish `hpa : ∀ a b : Af D.host.F, pairA D.host.F 0 a + pairA D.host.F 0 b = pairA D.host.F 0 (a + b)` using `fun a b => Prod.ext (add_zero 0) rfl`. Establish `hsum : ∀ (s : Finset (Pl D)) (f : Pl D → Af D.host.F), ∑ v ∈ s, pairA D.host.F 0 (f v) = pairA D.host.F 0 (∑ v ∈ s, f v)`. Introduce `s f`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact Prod.ext rfl rfl`.

Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, hpa]`. Rewrite using `[hsum, hpa, hβ, add_sub_cancel]`. Rewrite using `[e]`. Conclude with `add_mem (sum_mem fun v _ => GlobalTheory.FinPl.KSplit.latV_mono S L (fun _ _ => trivial) (hz v)) (GlobalTheory.FinPl.KSplit.latV_mono S L (fun _ _ => trivial) hoff)`. Establish `hhat` using `GlobalTheory.LatVHat.latV_mem_hatL D S L _ _ hall`.

Establish `e2 : (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i))) = fun i => Formalism.L2.Col.iA D.host.F D.host.E (z i)`. Use function extensionality and compare the values at `i`. Rewrite using `[swap_finPart_pure]`. Both sides reduce to the same expression. Rewrite `hhat` using `[e2]`.

Conclude with `(GlobalTheory.CongStdLoc.incl_mem_hatL_iff hlat.fg hlat.span_eq_top z).1 hhat`.
-/
theorem mem_of_local {S : HSp D} {L : GlobalTheory.FinPl.Lat S} (hL : IsSelfDualC S L) (z : Fin S.rank → D.host.E)
    (hz : ∀ v : GlobalTheory.FinPl.Pl D, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) ∈
      GlobalTheory.FinPl.latV S L (· = v)) : z ∈ L := by
  classical
  have hlat := hL.1
  obtain ⟨d, hd, hdz⟩ := GlobalTheory.FinPl.exists_int_smul_le (Submodule.span (𝓞 D.host.E) {z}) L
    (Submodule.fg_span_singleton z) hlat.span_eq_top
  set T := (GlobalTheory.FinPl.finite_places_int (D := D) d hd).toFinset with hT
  set β : Af D.host.F := 1 - ∑ v ∈ T, GlobalTheory.FinPl.LatMem.indP D.host.F (· = v) with hβ
  have hβv : ∀ w, evalV D.host.F w β = if w ∈ T then 0 else 1 := by
    intro w
    rw [hβ, map_sub, map_one, map_sum]
    simp only [GlobalTheory.FinPl.LatMem.evalV_indP]
    rw [Finset.sum_ite_eq]
    split_ifs <;> simp
  have hoff : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] ((1 : D.host.E) * z i)) ∈
      GlobalTheory.FinPl.latV S L (fun w => w ∉ T) := by
    apply GlobalTheory.FinPl.LocAgree.latV_le_of_int_smul_on S (Submodule.span (𝓞 D.host.E) {z}) L d hd hdz
    · intro v hv hmem
      exact hv ((Set.Finite.mem_toFinset _).2 hmem)
    · apply AddSubgroup.subset_closure
      refine ⟨β, fun w => ?_, fun w hw => ?_, 1, rfl, z, Submodule.mem_span_singleton_self z, rfl⟩
      · rw [hβv]
        split_ifs
        · exact zero_mem _
        · exact one_mem _
      · rw [hβv, if_pos (not_not.1 hw)]
  have hall : (fun i => pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i) ∈ GlobalTheory.FinPl.latV S L (fun _ => True) := by
    have e : (fun i => pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i) =
        ∑ v ∈ T, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) +
          (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] ((1 : D.host.E) * z i)) := by
      funext i
      rw [Pi.add_apply, Finset.sum_apply, one_mul, ← TensorProduct.sum_tmul, ← TensorProduct.add_tmul]
      congr 1
      have hpa : ∀ a b : Af D.host.F, pairA D.host.F 0 a + pairA D.host.F 0 b = pairA D.host.F 0 (a + b) :=
        fun a b => Prod.ext (add_zero 0) rfl
      have hsum : ∀ (s : Finset (Pl D)) (f : Pl D → Af D.host.F),
          ∑ v ∈ s, pairA D.host.F 0 (f v) = pairA D.host.F 0 (∑ v ∈ s, f v) := by
        intro s f
        induction s using Finset.induction_on with
        | empty => exact Prod.ext rfl rfl
        | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, hpa]
      rw [hsum, hpa, hβ, add_sub_cancel]
    rw [e]
    exact add_mem (sum_mem fun v _ => GlobalTheory.FinPl.KSplit.latV_mono S L (fun _ _ => trivial) (hz v))
      (GlobalTheory.FinPl.KSplit.latV_mono S L (fun _ _ => trivial) hoff)
  have hhat := GlobalTheory.LatVHat.latV_mem_hatL D S L _ _ hall
  have e2 : (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i))) =
      fun i => Formalism.L2.Col.iA D.host.F D.host.E (z i) := by
    funext i
    rw [swap_finPart_pure]
    rfl
  rw [e2] at hhat
  exact (GlobalTheory.CongStdLoc.incl_mem_hatL_iff hlat.fg hlat.span_eq_top z).1 hhat

/- English proof (translation)
Introduce `hL z hz` and use `mem_of_local hL z hz`.
-/
theorem mem_of_mem_latV_all : ∀ {D : D7} {S : HSp D} {L : Lat S}, IsSelfDualC S L → (∀ z : Fin S.rank → D.host.E, (∀ v : GlobalTheory.FinPl.Pl D, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) ∈ latV S L (· = v)) → z ∈ L) :=
  fun hL z hz => mem_of_local hL z hz

end GlobalTheory.FinPl.LocGlob
