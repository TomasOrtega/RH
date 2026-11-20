import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RestrProdSt

noncomputable section

namespace PI.VolStabS.RPA

open MeasureTheory Filter Finset
open scoped NNReal ENNReal

variable {ι : Type} {W : ι → Type} [∀ i, MeasurableSpace (W i)]
variable (m : ∀ i, Measure (W i)) (L : ∀ i, Set (W i))

def am (i : ι) : ℝ≥0 := (m i (L i)).toNNReal

def tl (S : Finset ι) : ℝ≥0 := ∏' i : {i // i ∉ S}, am m L i.1

def TailH : Prop :=
  ∀ S : Finset ι, ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ HasProd (fun i : {i // i ∉ S} => m i.1 (L i.1)) c

variable {m L}

/- English proof (translation)
Take `⟨c, hc, hP⟩` from `hT S`. Establish `h2 : HasProd (fun i : {i // i ∉ S} => am m L i.1) c.toNNReal`. Unfold `HasProd at hP ⊢`. Establish `h3` using `(ENNReal.tendsto_toNNReal hc).comp hP`. Use `h3.congr (fun s => ?_)` and prove the remaining obligations.

Simplify using `only [Function.comp, am, ENNReal.toNNReal_prod]`. Rewrite using `[tl, h2.tprod_eq]`. Conclude with `h2`.
-/
lemma hasProd_tl (hT : TailH m L) (S : Finset ι) :
    HasProd (fun i : {i // i ∉ S} => am m L i.1) (tl m L S) := by
  obtain ⟨c, hc, hP⟩ := hT S
  have h2 : HasProd (fun i : {i // i ∉ S} => am m L i.1) c.toNNReal := by
    unfold HasProd at hP ⊢
    have h3 := (ENNReal.tendsto_toNNReal hc).comp hP
    refine h3.congr (fun s => ?_)
    simp only [Function.comp, am, ENNReal.toNNReal_prod]
  rw [tl, h2.tprod_eq]
  exact h2

/- English proof (translation)
Conclude with `hasProd_subtype_iff_mulIndicator.mp (hasProd_tl hT S)`.
-/
lemma hasProd_ind (hT : TailH m L) (S : Finset ι) :
    HasProd (({i | i ∉ S} : Set ι).mulIndicator (am m L)) (tl m L S) := by
  exact hasProd_subtype_iff_mulIndicator.mp (hasProd_tl hT S)

/- English proof (translation)
Establish `hS` using `hasProd_ind hT S`. Establish `hT'` using `hasProd_ind hT T`. Establish `hfin : HasProd ((↑(T \ S) : Set ι).mulIndicator (am m L)) (∏ i ∈ T \ S, am m L i)`. Establish `h` using `hasProd_prod_of_ne_finset_one (f := (↑(T \ S) : Set ι).mulIndicator (am m L)) (s := T \ S) (L := SummationFilter.unconditional ι) (fun b hb => Set.mulIndicator_of_notMem (by simpa using hb) _)`. Rewrite `h` using `[Finset.prod_congr rfl (fun b hb => Set.mulIndicator_of_mem (by simpa using hb) (am m L))]`. Then use the resulting hypothesis.

Establish `hmul` using `hfin.mul hT'`. Establish `heq : (fun b => (↑(T \ S) : Set ι).mulIndicator (am m L) b * ({i | i ∉ T} : Set ι).mulIndicator (am m L) b) = ({i | i ∉ S} : Set ι).mulIndicator (am m L)`. Use function extensionality and compare the values at `b`. Apply the tactic sequence `by_cases hbT : b ∈ T <;> by_cases hbS : b ∈ S`. Simplify using `[Set.mulIndicator, hbT, hbS]`.

Simplify using `[Set.mulIndicator, hbT, hbS]`. Conclude with `absurd (h hbS) hbT`. Simplify using `[Set.mulIndicator, hbT, hbS]`. Rewrite `hmul` using `[heq]`. Conclude with `hS.unique hmul`.
-/
lemma tl_split [DecidableEq ι] (hT : TailH m L) {S T : Finset ι} (h : S ⊆ T) :
    tl m L S = (∏ i ∈ T \ S, am m L i) * tl m L T := by
  have hS := hasProd_ind hT S
  have hT' := hasProd_ind hT T
  have hfin : HasProd ((↑(T \ S) : Set ι).mulIndicator (am m L)) (∏ i ∈ T \ S, am m L i) := by
    have h := hasProd_prod_of_ne_finset_one (f := (↑(T \ S) : Set ι).mulIndicator (am m L)) (s := T \ S)
      (L := SummationFilter.unconditional ι)
      (fun b hb => Set.mulIndicator_of_notMem (by simpa using hb) _)
    rwa [Finset.prod_congr rfl (fun b hb => Set.mulIndicator_of_mem (by simpa using hb) (am m L))] at h
  have hmul := hfin.mul hT'
  have heq : (fun b => (↑(T \ S) : Set ι).mulIndicator (am m L) b * ({i | i ∉ T} : Set ι).mulIndicator (am m L) b) =
      ({i | i ∉ S} : Set ι).mulIndicator (am m L) := by
    funext b
    by_cases hbT : b ∈ T <;> by_cases hbS : b ∈ S
    · simp [Set.mulIndicator, hbT, hbS]
    · simp [Set.mulIndicator, hbT, hbS]
    · exact absurd (h hbS) hbT
    · simp [Set.mulIndicator, hbT, hbS]
  rw [heq] at hmul
  exact hS.unique hmul

/- English proof (translation)
Establish `h` using `tl_split hT (Finset.subset_insert i S)`. Rewrite `h` using `[Finset.insert_sdiff_of_notMem _ hi, Finset.sdiff_self, insert_empty_eq, Finset.prod_singleton, h0, zero_mul]`. Conclude with `h`.
-/
lemma tl_zero [DecidableEq ι] (hT : TailH m L) {S : Finset ι} {i : ι} (hi : i ∉ S)
    (h0 : am m L i = 0) : tl m L S = 0 := by
  have h := tl_split hT (Finset.subset_insert i S)
  rw [Finset.insert_sdiff_of_notMem _ hi, Finset.sdiff_self, insert_empty_eq, Finset.prod_singleton, h0,
    zero_mul] at h
  exact h

variable (m L)

def Pn (i : ι) : Measure (W i) := (m i (L i))⁻¹ • (m i).restrict (L i)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Simplify using `only [Pn, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]`. Conclude with `ENNReal.inv_mul_cancel h.1 h.2`.
-/
lemma Pn_prob {i : ι} (h : m i (L i) ≠ 0 ∧ m i (L i) ≠ ⊤) : IsProbabilityMeasure (Pn m L i) := by
  constructor
  simp only [Pn, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel h.1 h.2

open Classical in

def Qm (S : Finset ι) : Measure (∀ i : {i // i ∉ S}, W i) :=
  if h : ∀ i, i ∉ S → m i (L i) ≠ 0 ∧ m i (L i) ≠ ⊤ then
    haveI : ∀ i : {i // i ∉ S}, IsProbabilityMeasure (Pn m L i.1) := fun i => Pn_prob m L (h i.1 i.2)
    tl m L S • Measure.infinitePi (fun i : {i // i ∉ S} => Pn m L i.1)
  else 0

instance Qm_fin (S : Finset ι) : IsFiniteMeasure (Qm m L S) := by
  unfold Qm; split_ifs with h
  · haveI : ∀ i : {i // i ∉ S}, IsProbabilityMeasure (Pn m L i.1) :=
      fun i => Pn_prob m L (h i.1 i.2)
    infer_instance
  · infer_instance

def Rm (S : Finset ι) : Measure (∀ i : {i // i ∈ S}, W i) :=
  Measure.pi (fun i : {i // i ∈ S} => (m i.1).restrict (L i.1)ᶜ)

open Classical in

def eS (S : Finset ι) : (∀ i, W i) ≃ᵐ (∀ i : {i // i ∈ S}, W i) × (∀ i : {i // i ∉ S}, W i) :=
  MeasurableEquiv.piEquivPiSubtypeProd W (fun i => i ∈ S)

def kap [∀ i, SigmaFinite (m i)] (S : Finset ι) : Measure (∀ i, W i) :=
  ((Rm m L S).prod (Qm m L S)).map (eS S).symm

open Classical in

def mu (S : Finset ι) (i : ι) : Measure (W i) :=
  if i ∈ S then (m i).restrict (L i)ᶜ else (m i).restrict (L i)

open Classical in
/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma eS_symm_apply (S : Finset ι) (p : (∀ i : {i // i ∈ S}, W i) × (∀ i : {i // i ∉ S}, W i))
    (i : ι) : (eS S).symm p i = if h : i ∈ S then p.1 ⟨i, h⟩ else p.2 ⟨i, h⟩ := by
  rfl

variable [∀ i, SigmaFinite (m i)]

instance kap_sfin (S : Finset ι) : SFinite (kap m L S) := by unfold kap Rm; infer_instance

variable {m L}

/- English proof (translation)
Establish `hmeas : MeasurableSet {x : ∀ i, W i | x i ∈ A}` using `measurable_pi_apply i hA`. Rewrite using `[kap, Measure.map_apply (eS S).symm.measurable hmeas]`. Distinguish the cases in `hi : i ∈ S`. Establish `hmu : (m i).restrict (L i)ᶜ A = 0` using `by simpa [mu, hi] using h`. Establish `hpre : (eS S).symm ⁻¹' {x | x i ∈ A} = (Function.eval (⟨i, hi⟩ : {i // i ∈ S}) ⁻¹' A) ×ˢ Set.univ`.

Use extensionality with `p`. Simplify using `[eS_symm_apply, hi]`. Rewrite using `[hpre, Measure.prod_prod]`. Establish `h0 : Rm m L S (Function.eval (⟨i, hi⟩ : {i // i ∈ S}) ⁻¹' A) = 0` using `Measure.pi_eval_preimage_null _ hmu`. Rewrite using `[h0, zero_mul]`.

Establish `hmu : (m i).restrict (L i) A = 0` using `by simpa [mu, hi] using h`. Establish `hpre : (eS S).symm ⁻¹' {x | x i ∈ A} = Set.univ ×ˢ (Function.eval (⟨i, hi⟩ : {i // i ∉ S}) ⁻¹' A)`. Use extensionality with `p`. Simplify using `[eS_symm_apply, hi]`. Rewrite using `[hpre, Measure.prod_prod]`.

Establish `h0 : Qm m L S (Function.eval (⟨i, hi⟩ : {i // i ∉ S}) ⁻¹' A) = 0`. Unfold `Qm`. Use `split_ifs with hc`. Rewrite using `[Measure.smul_apply] haveI hprob : ∀ j : {j // j ∉ S}, IsProbabilityMeasure (Pn m L j.1) := fun j => Pn_prob m L (hc j.1 j.2)`. Establish `e` using `Measure.infinitePi_map_eval (fun j : {j // j ∉ S} => Pn m L j.1) ⟨i, hi⟩`.

Establish `e2 : Measure.infinitePi (fun j : {j // j ∉ S} => Pn m L j.1) (Function.eval (⟨i, hi⟩ : {i // i ∉ S}) ⁻¹' A) = Pn m L i A`. Rewrite using `[← e]`. Conclude with `(Measure.map_apply (measurable_pi_apply (⟨i, hi⟩ : {j // j ∉ S})) hA).symm`. Rewrite using `[e2]`. Simplify using `[Pn, hmu]`.

Both sides reduce to the same expression. Rewrite using `[h0, mul_zero]`.
-/
lemma kap_eval_null {S : Finset ι} {i : ι} {A : Set (W i)} (hA : MeasurableSet A)
    (h : mu m L S i A = 0) : kap m L S {x | x i ∈ A} = 0 := by
  classical
  have hmeas : MeasurableSet {x : ∀ i, W i | x i ∈ A} := measurable_pi_apply i hA
  rw [kap, Measure.map_apply (eS S).symm.measurable hmeas]
  by_cases hi : i ∈ S
  · have hmu : (m i).restrict (L i)ᶜ A = 0 := by simpa [mu, hi] using h
    have hpre : (eS S).symm ⁻¹' {x | x i ∈ A} =
        (Function.eval (⟨i, hi⟩ : {i // i ∈ S}) ⁻¹' A) ×ˢ Set.univ := by
      ext p
      simp [eS_symm_apply, hi]
    rw [hpre, Measure.prod_prod]
    have h0 : Rm m L S (Function.eval (⟨i, hi⟩ : {i // i ∈ S}) ⁻¹' A) = 0 :=
      Measure.pi_eval_preimage_null _ hmu
    rw [h0, zero_mul]
  · have hmu : (m i).restrict (L i) A = 0 := by simpa [mu, hi] using h
    have hpre : (eS S).symm ⁻¹' {x | x i ∈ A} =
        Set.univ ×ˢ (Function.eval (⟨i, hi⟩ : {i // i ∉ S}) ⁻¹' A) := by
      ext p
      simp [eS_symm_apply, hi]
    rw [hpre, Measure.prod_prod]
    have h0 : Qm m L S (Function.eval (⟨i, hi⟩ : {i // i ∉ S}) ⁻¹' A) = 0 := by
      unfold Qm
      split_ifs with hc
      · rw [Measure.smul_apply]
        haveI hprob : ∀ j : {j // j ∉ S}, IsProbabilityMeasure (Pn m L j.1) :=
          fun j => Pn_prob m L (hc j.1 j.2)
        have e := Measure.infinitePi_map_eval (fun j : {j // j ∉ S} => Pn m L j.1) ⟨i, hi⟩
        have e2 : Measure.infinitePi (fun j : {j // j ∉ S} => Pn m L j.1)
            (Function.eval (⟨i, hi⟩ : {i // i ∉ S}) ⁻¹' A) = Pn m L i A := by
          rw [← e]
          exact (Measure.map_apply (measurable_pi_apply (⟨i, hi⟩ : {j // j ∉ S})) hA).symm
        rw [e2]
        simp [Pn, hmu]
      · rfl
    rw [h0, mul_zero]

/- English proof (translation)
Rewrite using `[ae_all_iff]`. Introduce `i`. Rewrite using `[ae_iff]`. Distinguish the cases in `hi : i ∈ S`. Establish `h0 : kap m L S {x | x i ∈ L i} = 0` using `kap_eval_null (hLm i) (by simp [mu, hi, Measure.restrict_apply (hLm i)])`.

Use `measure_mono_null ?_ h0` and prove the remaining obligations. Introduce `x hx`. Simplify using `only [Set.mem_setOf_eq] at hx ⊢`. Assume the negation of the conclusion as `hxL`. Conclude with `hx ⟨fun _ => hxL, fun h => absurd hi h⟩`.

Establish `h0 : kap m L S {x | x i ∈ (L i)ᶜ} = 0` using `kap_eval_null (hLm i).compl (by simp [mu, hi, Measure.restrict_apply (hLm i).compl])`. Use `measure_mono_null ?_ h0` and prove the remaining obligations. Introduce `x hx`. Simplify using `only [Set.mem_setOf_eq, Set.mem_compl_iff] at hx ⊢`. Introduce `hxL`.

Conclude with `hx ⟨fun h => absurd h hi, fun _ => hxL⟩`.
-/
lemma kap_ae [Countable ι] (hLm : ∀ i, MeasurableSet (L i)) (S : Finset ι) :
    ∀ᵐ x ∂kap m L S, ∀ i, (i ∈ S → x i ∉ L i) ∧ (i ∉ S → x i ∈ L i) := by
  rw [ae_all_iff]
  intro i
  rw [ae_iff]
  by_cases hi : i ∈ S
  · have h0 : kap m L S {x | x i ∈ L i} = 0 :=
      kap_eval_null (hLm i) (by simp [mu, hi, Measure.restrict_apply (hLm i)])
    refine measure_mono_null ?_ h0
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    by_contra hxL
    exact hx ⟨fun _ => hxL, fun h => absurd hi h⟩
  · have h0 : kap m L S {x | x i ∈ (L i)ᶜ} = 0 :=
      kap_eval_null (hLm i).compl (by simp [mu, hi, Measure.restrict_apply (hLm i).compl])
    refine measure_mono_null ?_ h0
    intro x hx
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff] at hx ⊢
    intro hxL
    exact hx ⟨fun h => absurd h hi, fun _ => hxL⟩

end PI.VolStabS.RPA
