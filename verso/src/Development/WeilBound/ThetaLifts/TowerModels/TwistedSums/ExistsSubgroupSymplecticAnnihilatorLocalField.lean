import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.IsLocallyConstantHeisenbergLatticeVacuumFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplittingSplitOm

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace Tw.SympDualNbhd
open _root_.GlobalTheory

/- English proof (translation)
Introduce `F _ _ v ψ hψc hψ κ _ N hN`. Take `⟨U₀, hU₀⟩` from `Tw.HeisLatVac.lc_exists_open_ker ψ hψc`. Take `⟨t₀, ht₀⟩` from `AddChar.ne_one_iff.1 hψ`. Establish `ht₀0 : t₀ ≠ 0` using `by rintro rfl; exact ht₀ (AddChar.map_zero_eq_one ψ)`. Use `haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v`.

Establish `hOc : IsCompact ((v.adicCompletionIntegers F : Set (Fv F v)))` using `isCompact_iff_compactSpace.2 ‹_›`. Use `set C : Set ((κ → Fv F v) × (κ → Fv F v)) := Set.univ.pi (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) ×ˢ Set.univ.pi (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) with hC`. Establish `hCc : IsCompact C` using `(isCompact_univ_pi fun _ => hOc).prod (isCompact_univ_pi fun _ => hOc)`. Establish `hev : ∀ᶠ a in nhds (0 : Fv F v), ∀ w ∈ C, a • w ∈ N`. Use `hCc.eventually_forall_of_forall_eventually fun w _ => ?_` and prove the remaining obligations.

Establish `h1 : Filter.Tendsto (fun z : Fv F v × ((κ → Fv F v) × (κ → Fv F v)) => z.1 • z.2) (nhds (0, w)) (nhds ((0 : Fv F v) • w))` using `continuous_smul.continuousAt`. Rewrite `h1` using `[zero_smul]`. Conclude with `h1 hN`. Use `haveI hne : (nhdsWithin (0 : Fv F v) {0}ᶜ).NeBot := by`. Use `letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _`.

Conclude with `NormedField.nhdsNE_neBot 0`. Take `⟨a, haC, ha0⟩` from `((hev.filter_mono nhdsWithin_le_nhds).and (eventually_mem_nhdsWithin (a := (0 : Fv F v)) (s := {0}ᶜ))).exists`. Establish `ha0' : a ≠ 0` using `ha0`. Use `set b : Fv F v := a * t₀⁻¹ with hb`. Establish `hb0 : b ≠ 0` using `mul_ne_zero ha0' (inv_ne_zero ht₀0)`.

Set `Y : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))` to `{ carrier := {w | ∀ i, b * w.1 i ∈ v.adicCompletionIntegers F ∧ b * w.2 i ∈ v.adicCompletionIntegers F} add_mem' := fun {x y} hx hy i => ⟨by simpa [mul_add] using add_mem (hx i).1 (hy i).1, by simpa [mul_add] using add_mem (hx i).2 (hy i).2⟩ zero_mem' := fun i => by simp neg_mem' …`. Establish `hYC : ∀ w ∈ Y, w ∈ (fun x => b⁻¹ • x) '' C`. Introduce `w hw`. Use `⟨b • w, ?_, inv_smul_smul₀ hb0 w⟩` and prove the remaining obligations. Simplify using `only [hC, Set.mem_prod, Set.mem_univ_pi, SetLike.mem_coe]`.

Conclude with `⟨fun i => (hw i).1, fun i => (hw i).2⟩`. Establish `hev2 : ∀ᶠ w' in nhds (0 : (κ → Fv F v) × (κ → Fv F v)), ∀ w ∈ (fun x => b⁻¹ • x) '' C, (w'.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ w'.2) ∈ (U₀ : Set (Fv F v))`. Use `(hCc.image (continuous_const_smul b⁻¹)).eventually_forall_of_forall_eventually fun w _ => ?_` and prove the remaining obligations. Establish `hc : Continuous fun z : ((κ → Fv F v) × (κ → Fv F v)) × ((κ → Fv F v) × (κ → Fv F v)) => z.1.1 ⬝ᵥ z.2.2 - z.2.1 ⬝ᵥ z.1.2` using `((continuous_fst.fst).dotProduct continuous_snd.snd).sub ((continuous_snd.fst).dotProduct continuous_fst.snd)`. Establish `h1 : Filter.Tendsto (fun z : ((κ → Fv F v) × (κ → Fv F v)) × ((κ → Fv F v) × (κ → Fv F v)) => z.1.1 ⬝ᵥ z.2.2 - z.2.1 ⬝ᵥ z.1.2) (nhds ((0 : (κ → Fv F v) × (κ → Fv F v)), w)) (nhds 0)`.

Use `hc.tendsto ((0 : (κ → Fv F v) × (κ → Fv F v)), w) using 2` and compare the differences between its conclusion and the goal. Simplify using the standard rewrite rules. Conclude with `h1 (U₀.isOpen.mem_nhds U₀.zero_mem)`. Use `⟨Y, ?_, _, hev2, fun w' hw' w hw => hU₀ _ (hw' w (hYC w hw))⟩` and prove the remaining obligations. Introduce `w' hw'`.

Assume the negation of the conclusion as `hN'`. Establish `hnC : a⁻¹ • w' ∉ C`. Introduce `h`. Apply `hN'` to reduce the goal to its premises. Use `haC _ h` as an intermediate fact.

Rewrite `this` using `[smul_inv_smul₀ ha0']`. Then use the resulting hypothesis. Simplify using `only [hC, Set.mem_prod, Set.mem_univ_pi, SetLike.mem_coe, not_and_or, not_forall] at hnC`. Break down `hnC with ⟨i, hi⟩ | ⟨i, hi⟩` into its components or cases. Establish `ht : w'.1 i ≠ 0`. Introduce `h`.

Apply `hi` to reduce the goal to its premises. Simplify using `[h]`. Establish `hinv : (a⁻¹ * w'.1 i)⁻¹ ∈ v.adicCompletionIntegers F` using `(ValuationSubring.mem_or_inv_mem _ _).resolve_left (by simpa using hi)`. Establish `hw : ((0 : κ → Fv F v), Pi.single i (t₀ / w'.1 i)) ∈ Y`. Introduce `j`.

Use `⟨by simp, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Use `hinv using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Pi.single_eq_same, hb]`.

Clear the denominators using the available nonvanishing facts. Simplify using `[Pi.single_apply, hj]`. Apply `ht₀` to reduce the goal to its premises. Use `hw' _ hw using 2` and compare the differences between its conclusion and the goal. Simplify using `[dotProduct_single]`.

Clear the denominators using the available nonvanishing facts. Establish `ht : w'.2 i ≠ 0`. Introduce `h`. Apply `hi` to reduce the goal to its premises. Simplify using `[h]`.

Establish `hinv : (a⁻¹ * w'.2 i)⁻¹ ∈ v.adicCompletionIntegers F` using `(ValuationSubring.mem_or_inv_mem _ _).resolve_left (by simpa using hi)`. Establish `hw : (Pi.single i (-(t₀ / w'.2 i)), (0 : κ → Fv F v)) ∈ Y`. Introduce `j`. Use `⟨?_, by simp⟩` and prove the remaining obligations. Distinguish the cases in `hj : j = i`.

Substitute `hj` using the available equality. Use `neg_mem hinv` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Pi.single_eq_same, hb]`. Clear the denominators using the available nonvanishing facts.

Simplify using `[Pi.single_apply, hj]`. Apply `ht₀` to reduce the goal to its premises. Use `hw' _ hw using 2` and compare the differences between its conclusion and the goal. Simplify using `[single_dotProduct]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_dual_nbhd : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (ψ : AddChar (Fv F v) ℂ),
    Continuous ψ → ψ ≠ 1 → ∀ {κ : Type} [Fintype κ] (N : Set ((κ → Fv F v) × (κ → Fv F v))), N ∈ nhds 0 →
    ∃ Y : AddSubgroup ((κ → Fv F v) × (κ → Fv F v)),
      (∀ w' : (κ → Fv F v) × (κ → Fv F v), (∀ w ∈ Y, ψ (w'.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ w'.2) = 1) → w' ∈ N) ∧
      ∃ N' ∈ nhds (0 : (κ → Fv F v) × (κ → Fv F v)), ∀ w' ∈ N', ∀ w ∈ Y, ψ (w'.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ w'.2) = 1 := by
  intro F _ _ v ψ hψc hψ κ _ N hN
  obtain ⟨U₀, hU₀⟩ := Tw.HeisLatVac.lc_exists_open_ker ψ hψc
  obtain ⟨t₀, ht₀⟩ := AddChar.ne_one_iff.1 hψ
  have ht₀0 : t₀ ≠ 0 := by rintro rfl; exact ht₀ (AddChar.map_zero_eq_one ψ)
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  have hOc : IsCompact ((v.adicCompletionIntegers F : Set (Fv F v))) :=
    isCompact_iff_compactSpace.2 ‹_›
  set C : Set ((κ → Fv F v) × (κ → Fv F v)) :=
    Set.univ.pi (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) ×ˢ
      Set.univ.pi (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) with hC
  have hCc : IsCompact C := (isCompact_univ_pi fun _ => hOc).prod (isCompact_univ_pi fun _ => hOc)
  have hev : ∀ᶠ a in nhds (0 : Fv F v), ∀ w ∈ C, a • w ∈ N := by
    refine hCc.eventually_forall_of_forall_eventually fun w _ => ?_
    have h1 : Filter.Tendsto (fun z : Fv F v × ((κ → Fv F v) × (κ → Fv F v)) => z.1 • z.2)
        (nhds (0, w)) (nhds ((0 : Fv F v) • w)) := continuous_smul.continuousAt
    rw [zero_smul] at h1
    exact h1 hN
  haveI hne : (nhdsWithin (0 : Fv F v) {0}ᶜ).NeBot := by
    letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _
    exact NormedField.nhdsNE_neBot 0
  obtain ⟨a, haC, ha0⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (eventually_mem_nhdsWithin (a := (0 : Fv F v)) (s := {0}ᶜ))).exists
  have ha0' : a ≠ 0 := ha0
  set b : Fv F v := a * t₀⁻¹ with hb
  have hb0 : b ≠ 0 := mul_ne_zero ha0' (inv_ne_zero ht₀0)
  let Y : AddSubgroup ((κ → Fv F v) × (κ → Fv F v)) :=
    { carrier := {w | ∀ i, b * w.1 i ∈ v.adicCompletionIntegers F ∧ b * w.2 i ∈ v.adicCompletionIntegers F}
      add_mem' := fun {x y} hx hy i =>
        ⟨by simpa [mul_add] using add_mem (hx i).1 (hy i).1,
         by simpa [mul_add] using add_mem (hx i).2 (hy i).2⟩
      zero_mem' := fun i => by simp
      neg_mem' := fun {x} hx i =>
        ⟨by simpa [mul_neg] using neg_mem (hx i).1, by simpa [mul_neg] using neg_mem (hx i).2⟩ }
  have hYC : ∀ w ∈ Y, w ∈ (fun x => b⁻¹ • x) '' C := by
    intro w hw
    refine ⟨b • w, ?_, inv_smul_smul₀ hb0 w⟩
    simp only [hC, Set.mem_prod, Set.mem_univ_pi, SetLike.mem_coe]
    exact ⟨fun i => (hw i).1, fun i => (hw i).2⟩
  have hev2 : ∀ᶠ w' in nhds (0 : (κ → Fv F v) × (κ → Fv F v)), ∀ w ∈ (fun x => b⁻¹ • x) '' C,
      (w'.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ w'.2) ∈ (U₀ : Set (Fv F v)) := by
    refine (hCc.image (continuous_const_smul b⁻¹)).eventually_forall_of_forall_eventually fun w _ => ?_
    have hc : Continuous fun z : ((κ → Fv F v) × (κ → Fv F v)) × ((κ → Fv F v) × (κ → Fv F v)) =>
        z.1.1 ⬝ᵥ z.2.2 - z.2.1 ⬝ᵥ z.1.2 :=
      ((continuous_fst.fst).dotProduct continuous_snd.snd).sub
        ((continuous_snd.fst).dotProduct continuous_fst.snd)
    have h1 : Filter.Tendsto (fun z : ((κ → Fv F v) × (κ → Fv F v)) × ((κ → Fv F v) × (κ → Fv F v)) =>
        z.1.1 ⬝ᵥ z.2.2 - z.2.1 ⬝ᵥ z.1.2) (nhds ((0 : (κ → Fv F v) × (κ → Fv F v)), w)) (nhds 0) := by
      convert hc.tendsto ((0 : (κ → Fv F v) × (κ → Fv F v)), w) using 2
      simp
    exact h1 (U₀.isOpen.mem_nhds U₀.zero_mem)
  refine ⟨Y, ?_, _, hev2, fun w' hw' w hw => hU₀ _ (hw' w (hYC w hw))⟩
  intro w' hw'
  by_contra hN'
  have hnC : a⁻¹ • w' ∉ C := by
    intro h
    apply hN'
    have := haC _ h
    rwa [smul_inv_smul₀ ha0'] at this
  simp only [hC, Set.mem_prod, Set.mem_univ_pi, SetLike.mem_coe, not_and_or, not_forall] at hnC
  rcases hnC with ⟨i, hi⟩ | ⟨i, hi⟩
  · have ht : w'.1 i ≠ 0 := by
      intro h; apply hi; simp [h]
    have hinv : (a⁻¹ * w'.1 i)⁻¹ ∈ v.adicCompletionIntegers F :=
      (ValuationSubring.mem_or_inv_mem _ _).resolve_left (by simpa using hi)
    have hw : ((0 : κ → Fv F v), Pi.single i (t₀ / w'.1 i)) ∈ Y := by
      intro j
      refine ⟨by simp, ?_⟩
      by_cases hj : j = i
      · subst hj
        convert hinv using 1
        simp only [Pi.single_eq_same, hb]
        field_simp
      · simp [Pi.single_apply, hj]
    apply ht₀
    convert hw' _ hw using 2
    simp [dotProduct_single]
    field_simp
  · have ht : w'.2 i ≠ 0 := by
      intro h; apply hi; simp [h]
    have hinv : (a⁻¹ * w'.2 i)⁻¹ ∈ v.adicCompletionIntegers F :=
      (ValuationSubring.mem_or_inv_mem _ _).resolve_left (by simpa using hi)
    have hw : (Pi.single i (-(t₀ / w'.2 i)), (0 : κ → Fv F v)) ∈ Y := by
      intro j
      refine ⟨?_, by simp⟩
      by_cases hj : j = i
      · subst hj
        have := neg_mem hinv
        convert this using 1
        simp only [Pi.single_eq_same, hb]
        field_simp
      · simp [Pi.single_apply, hj]
    apply ht₀
    convert hw' _ hw using 2
    simp [single_dotProduct]
    field_simp
