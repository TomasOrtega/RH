import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsFolnerUWset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClosedSubgroupBesselHaarFiniteCompactPosOpenStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCompactNormBoundedBesselClosedSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelUnitaryGroupOpNormPropertiesStatement

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SgGrowth

variable {k r : ℕ}

/- English proof (translation)
Use `set f : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℝ] (Fin (2 * r + k + 1) → ℂ) := (Matrix.toLin' hᵀ).restrictScalars ℝ with hfdef`. Establish `hdet : LinearMap.det f = 1`. Rewrite using `[hfdef, LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, Matrix.det_transpose, Complex.normSq_eq_norm_sq, hd]`. Evaluate the numerical expressions. Establish `hrow : MeasurePreserving (fun v : Fin (2 * r + k + 1) → ℂ => v ᵥ* h) volume volume`.

Establish `hfe : (fun v : Fin (2 * r + k + 1) → ℂ => v ᵥ* h) = f`. Use extensionality with `v`. Simplify using `[hfdef, Matrix.toLin'_apply, Matrix.mulVec_transpose]`. Rewrite using `[hfe]`. Use `⟨f.continuous_of_finiteDimensional.measurable, ?_⟩` and prove the remaining obligations.

Use `Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (Fin (2 * r + k + 1) → ℂ))) (f := f) (by rw [hdet]; norm_num)` as an intermediate fact. Rewrite `this` using `[hdet]`. Simplify using `using this`. Establish `hr : (rmulM h : Mt k r → Mt k r) = fun x i => (fun v : Fin (2 * r + k + 1) → ℂ => v ᵥ* h) (x i)`. Use function extensionality and compare the values at `x i j`.

Both sides reduce to the same expression. Rewrite using `[hr, volume_pi]`. Conclude with `measurePreserving_pi _ _ fun _ => hrow`.
-/
theorem measurePreserving_rmulM {h : Mat k r} (hd : ‖h.det‖ = 1) :
    MeasurePreserving (rmulM h : Mt k r → Mt k r) volume volume := by
  set f : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℝ] (Fin (2 * r + k + 1) → ℂ) :=
    (Matrix.toLin' hᵀ).restrictScalars ℝ with hfdef
  have hdet : LinearMap.det f = 1 := by
    rw [hfdef, LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply,
      Matrix.det_transpose, Complex.normSq_eq_norm_sq, hd]
    norm_num
  have hrow : MeasurePreserving (fun v : Fin (2 * r + k + 1) → ℂ => v ᵥ* h) volume volume := by
    have hfe : (fun v : Fin (2 * r + k + 1) → ℂ => v ᵥ* h) = f := by
      ext v; simp [hfdef, Matrix.toLin'_apply, Matrix.mulVec_transpose]
    rw [hfe]
    refine ⟨f.continuous_of_finiteDimensional.measurable, ?_⟩
    have := Measure.map_linearMap_addHaar_eq_smul_addHaar
      (μ := (volume : Measure (Fin (2 * r + k + 1) → ℂ))) (f := f) (by rw [hdet]; norm_num)
    rw [hdet] at this
    simpa using this
  have hr : (rmulM h : Mt k r → Mt k r) =
      fun x i => (fun v : Fin (2 * r + k + 1) → ℂ => v ᵥ* h) (x i) := by
    funext x i j; rfl
  rw [hr, volume_pi]
  exact measurePreserving_pi _ _ fun _ => hrow

/- English proof (translation)
Unfold `opn`. Rewrite using `[map_add]`. Conclude with `norm_add_le _ _`.
-/
theorem opn_add_le (a b : Mat k r) : opn (a + b) ≤ opn a + opn b := by
  unfold opn; rw [map_add]; exact norm_add_le _ _

/- English proof (translation)
Unfold `opn`. Rewrite using `[map_sub]`. Conclude with `norm_sub_le _ _`.
-/
theorem opn_sub_le (a b : Mat k r) : opn (a - b) ≤ opn a + opn b := by
  unfold opn; rw [map_sub]; exact norm_sub_le _ _

/- English proof (translation)
Unfold `opn`. Rewrite using `[map_zero, norm_zero]`.
-/
theorem opn_zero' : opn (0 : Mat k r) = 0 := by
  unfold opn; rw [map_zero, norm_zero]

/- English proof (translation)
Establish `h` using `(GlobalTheory.T.besselModelUnitaryGroup_opNorm_properties k r).2.2.2.1`. Conclude with `(pi_norm_le_iff_of_nonneg (opn_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (opn_nonneg _)).2 fun j => h _ i j`.
-/
theorem norm_le_opn (x : Mt k r) : ‖x‖ ≤ opn (Matrix.of x) := by
  have h := (GlobalTheory.T.besselModelUnitaryGroup_opNorm_properties k r).2.2.2.1
  exact (pi_norm_le_iff_of_nonneg (opn_nonneg _)).2 fun i =>
    (pi_norm_le_iff_of_nonneg (opn_nonneg _)).2 fun j => h _ i j

/- English proof (translation)
The claim follows from `(GlobalTheory.T.besselModelUnitaryGroup_opNorm_properties k r).2.2.1`.
-/
theorem continuous_opn : Continuous (fun x : Mat k r => opn x) := (GlobalTheory.T.besselModelUnitaryGroup_opNorm_properties k r).2.2.1

def nbhdU (k r : ℕ) : Set (Mt k r) := {x | opn (Matrix.of x - 1) < 1 / 4}

def trU (h : Mat k r) : Set (Mt k r) := rmulM h⁻¹ ⁻¹' nbhdU k r

def ballS (S : Set (Mat k r)) (R : ℝ) : Set (Mt k r) := {x | Matrix.of x ∈ S ∧ opn (Matrix.of x) ≤ R}

def Pack (S : Set (Mat k r)) (R : ℝ) (F : Finset (Mat k r)) : Prop :=
  (∀ h ∈ F, h ∈ S ∧ opn h ≤ R) ∧ (F : Set (Mat k r)).PairwiseDisjoint trU

/- English proof (translation)
Establish `: Continuous fun x : Mat k r => opn (x - 1)` using `continuous_opn.comp (continuous_id.sub continuous_const)`. Conclude with `isOpen_lt this continuous_const`.
-/
theorem isOpen_nbhdU : IsOpen (nbhdU k r) := by
  have : Continuous fun x : Mat k r => opn (x - 1) := continuous_opn.comp (continuous_id.sub continuous_const)
  exact isOpen_lt this continuous_const

/- English proof (translation)
Use `haveI : (volume : Measure (Fin (2 * r + k + 1) → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _`. Conclude with `Measure.pi.isAddHaarMeasure _`.
-/
theorem isAddHaarMeasure_volume_Mt : (volume : Measure (Mt k r)).IsAddHaarMeasure := by
  haveI : (volume : Measure (Fin (2 * r + k + 1) → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact Measure.pi.isAddHaarMeasure _

attribute [local instance] isAddHaarMeasure_volume_Mt

/- English proof (translation)
Use `isOpen_nbhdU.measure_ne_zero volume ⟨(1 : Mat k r), ?_⟩` and prove the remaining obligations. Use `show opn ((1 : Mat k r) - 1) < 1 / 4`. Rewrite using `[sub_self, opn_zero']`. Evaluate the numerical expressions.
-/
theorem volume_nbhdU_ne_zero : volume (nbhdU k r) ≠ 0 := by
  refine isOpen_nbhdU.measure_ne_zero volume ⟨(1 : Mat k r), ?_⟩
  show opn ((1 : Mat k r) - 1) < 1 / 4
  rw [sub_self, opn_zero']
  norm_num

/- English proof (translation)
The claim follows from `isOpen_nbhdU.measurableSet.preimage (continuous_rmulM h⁻¹).measurable`.
-/
theorem measurableSet_trU (h : Mat k r) : MeasurableSet (trU h) :=
  isOpen_nbhdU.measurableSet.preimage (continuous_rmulM h⁻¹).measurable

/- English proof (translation)
The claim follows from `(measurePreserving_rmulM (norm_det_of_mem_GG (isClosedSub_GG.2.2.2.2 h hh))).measure_preimage isOpen_nbhdU.measurableSet.nullMeasurableSet`.
-/
theorem volume_trU {h : Mat k r} (hh : h ∈ GG k r) : volume (trU h) = volume (nbhdU k r) :=
  (measurePreserving_rmulM (norm_det_of_mem_GG (isClosedSub_GG.2.2.2.2 h hh))).measure_preimage
    isOpen_nbhdU.measurableSet.nullMeasurableSet

/- English proof (translation)
Introduce `x hx`. Establish `hx' : opn (Matrix.of x * h⁻¹ - 1) < 1 / 4` using `hx`. Establish `hu : IsUnit h.det` using `isUnit_det_of_mem_GG hh`. Establish `e : (Matrix.of x : Mat k r) = (Matrix.of x * h⁻¹) * h`. Rewrite using `[Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]`.

Establish `h1 : opn (Matrix.of x * h⁻¹ : Mat k r) ≤ 5 / 4`. Use `opn_add_le (Matrix.of x * h⁻¹ - 1) 1` as an intermediate fact. Rewrite `this` using `[sub_add_cancel, opn_one]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[mem_closedBall_zero_iff]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem trU_subset {h : Mat k r} (hh : h ∈ GG k r) {R : ℝ} (hR : opn h ≤ R) :
    trU h ⊆ Metric.closedBall (0 : Mt k r) (5 / 4 * R) := by
  intro x hx
  have hx' : opn (Matrix.of x * h⁻¹ - 1) < 1 / 4 := hx
  have hu : IsUnit h.det := isUnit_det_of_mem_GG hh
  have e : (Matrix.of x : Mat k r) = (Matrix.of x * h⁻¹) * h := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
  have h1 : opn (Matrix.of x * h⁻¹ : Mat k r) ≤ 5 / 4 := by
    have := opn_add_le (Matrix.of x * h⁻¹ - 1) 1
    rw [sub_add_cancel, opn_one] at this; linarith
  rw [mem_closedBall_zero_iff]
  calc ‖x‖ ≤ opn (Matrix.of x) := norm_le_opn x
    _ = opn ((Matrix.of x * h⁻¹) * h) := congrArg opn e
    _ ≤ opn (Matrix.of x * h⁻¹) * opn h := opn_mul_le _ _
    _ ≤ 5 / 4 * R := mul_le_mul h1 hR (opn_nonneg _) (by norm_num)

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_congr rfl fun h hh => volume_trU (hS.1 (hF.1 h hh).1)]`. Simplify using the standard rewrite rules. Use `_ = volume (⋃ h ∈ F, trU h) := (measure_biUnion_finset hF.2 fun h _ => measurableSet_trU h).symm`. Use `_ ≤ _ := measure_mono (Set.iUnion₂_subset fun h hh => trU_subset (hS.1 (hF.1 h hh).1) (hF.1 h hh).2)`.
-/
theorem card_mul_le {S : Set (Mat k r)} (hS : IsClosedSub k r S) {R : ℝ} {F : Finset (Mat k r)}
    (hF : Pack S R F) :
    (F.card : ℝ≥0∞) * volume (nbhdU k r) ≤ volume (Metric.closedBall (0 : Mt k r) (5 / 4 * R)) := by
  calc (F.card : ℝ≥0∞) * volume (nbhdU k r) = ∑ h ∈ F, volume (trU h) := by
        rw [Finset.sum_congr rfl fun h hh => volume_trU (hS.1 (hF.1 h hh).1)]; simp
    _ = volume (⋃ h ∈ F, trU h) := (measure_biUnion_finset hF.2 fun h _ => measurableSet_trU h).symm
    _ ≤ _ := measure_mono (Set.iUnion₂_subset fun h hh =>
        trU_subset (hS.1 (hF.1 h hh).1) (hF.1 h hh).2)

/- English proof (translation)
Use `set B := volume (Metric.closedBall (0 : Mt k r) (5 / 4 * R)) / volume (nbhdU k r) with hBdef`. Establish `hB : B ≠ ⊤` using `ENNReal.div_ne_top measure_closedBall_lt_top.ne volume_nbhdU_ne_zero`. Establish `hb : ∀ G, Pack S R G → G.card ≤ ⌊B.toReal⌋₊`. Introduce `G hG`. Establish `h1 : (G.card : ℝ≥0∞) ≤ B` using `(ENNReal.le_div_iff_mul_le (Or.inl volume_nbhdU_ne_zero) (Or.inr measure_closedBall_lt_top.ne)).2 (card_mul_le hS hG)`.

Apply `Nat.le_floor` to reduce the goal to its premises. Use `ENNReal.toReal_mono hB h1` as an intermediate fact. Simplify using `using this`. Use `set P := {m : ℕ | ∃ G, Pack S R G ∧ G.card = m}`. Establish `hne : P.Nonempty` using `⟨0, ∅, ⟨by simp, by simp⟩, rfl⟩`.

Establish `hbdd : BddAbove P` using `⟨⌊B.toReal⌋₊, by rintro m ⟨G, hG, rfl⟩; exact hb G hG⟩`. Take `⟨F, hF, hc⟩` from `Nat.sSup_mem hne hbdd`. Conclude with `⟨F, hF, fun G hG => hc ▸ le_csSup hbdd ⟨G, hG, rfl⟩⟩`.
-/
theorem exists_max_pack {S : Set (Mat k r)} (hS : IsClosedSub k r S) (R : ℝ) :
    ∃ F, Pack S R F ∧ ∀ G, Pack S R G → G.card ≤ F.card := by
  set B := volume (Metric.closedBall (0 : Mt k r) (5 / 4 * R)) / volume (nbhdU k r) with hBdef
  have hB : B ≠ ⊤ := ENNReal.div_ne_top measure_closedBall_lt_top.ne volume_nbhdU_ne_zero
  have hb : ∀ G, Pack S R G → G.card ≤ ⌊B.toReal⌋₊ := by
    intro G hG
    have h1 : (G.card : ℝ≥0∞) ≤ B :=
      (ENNReal.le_div_iff_mul_le (Or.inl volume_nbhdU_ne_zero)
        (Or.inr measure_closedBall_lt_top.ne)).2 (card_mul_le hS hG)
    apply Nat.le_floor
    have := ENNReal.toReal_mono hB h1
    simpa using this
  set P := {m : ℕ | ∃ G, Pack S R G ∧ G.card = m}
  have hne : P.Nonempty := ⟨0, ∅, ⟨by simp, by simp⟩, rfl⟩
  have hbdd : BddAbove P := ⟨⌊B.toReal⌋₊, by rintro m ⟨G, hG, rfl⟩; exact hb G hG⟩
  obtain ⟨F, hF, hc⟩ := Nat.sSup_mem hne hbdd
  exact ⟨F, hF, fun G hG => hc ▸ le_csSup hbdd ⟨G, hG, rfl⟩⟩

/- English proof (translation)
Establish `N` using `GlobalTheory.T.besselModelUnitaryGroup_opNorm_properties k r`. Introduce and unpack `x ⟨hxS, hxR⟩`. Use `set s : Mat k r := Matrix.of x with hsdef`. Establish `hsG` using `hS.1 hxS`. Establish `hsu : IsUnit s.det` using `isUnit_det_of_mem_GG hsG`.

Establish `htS : s⁻¹ ∈ S` using `hS.2.2.2.2 s hxS`. Establish `htR : opn s⁻¹ ≤ R` using `by rw [(N.1 s hsG).1]; exact hxR`. Simplify using `only [Set.mem_iUnion]`. Distinguish the cases in `ht : s⁻¹ ∈ F`. Use `⟨s⁻¹, ht, ?_⟩ show s⁻¹ * s ∈ S ∧ opn (s⁻¹ * s) ≤ 2` and prove the remaining obligations.

Rewrite using `[Matrix.nonsing_inv_mul _ hsu, opn_one]`. Conclude with `⟨hS.2.2.1, by norm_num⟩`. Establish `hnot : ¬ Pack S R (insert s⁻¹ F)`. Introduce `hG`. Use `hmax _ hG` as an intermediate fact.

Rewrite `this` using `[Finset.card_insert_of_notMem ht]`. Use linear arithmetic over natural numbers and integers. Establish `hex : ∃ h ∈ F, ¬ Disjoint (trU s⁻¹) (trU h)`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Apply `hnot` to reduce the goal to its premises. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `g hg`. Break down `Finset.mem_insert.1 hg with rfl | hg` into its components or cases. Conclude with `⟨htS, htR⟩`.

Conclude with `hF.1 g hg`. Rewrite using `[Finset.coe_insert]`. Conclude with `hF.2.insert fun j hj _ => hcon j hj`. Take `⟨h, hhF, hdis⟩` from `hex`. Take `⟨y, hy1, hy2⟩` from `Set.not_disjoint_iff.1 hdis`.

Establish `hhS` using `(hF.1 h hhF).1`. Establish `hhu : IsUnit h.det` using `isUnit_det_of_mem_GG (hS.1 hhS)`. Use `⟨h, hhF, ?_⟩` and prove the remaining obligations. Use `show h * s ∈ S ∧ opn (h * s) ≤ 2`. Use `⟨hS.2.2.2.1 h hhS s hxS, ?_⟩` and prove the remaining obligations.

Establish `hy1' : opn (Matrix.of y * s - 1) < 1 / 4`. Establish `: opn (Matrix.of y * s⁻¹⁻¹ - 1) < 1 / 4` using `hy1`. Rewrite `this` using `[Matrix.nonsing_inv_nonsing_inv _ hsu]`. Then use the resulting hypothesis. Establish `hy2' : opn (Matrix.of y * h⁻¹ - 1) < 1 / 4` using `hy2`. Use `set u : Mat k r := Matrix.of y * s with hudef`.

Use `set u' : Mat k r := Matrix.of y * h⁻¹ with hu'def`. Establish `huv : u' * (h * s) = u`. Rewrite using `[hu'def, hudef, Matrix.mul_assoc, ← Matrix.mul_assoc h⁻¹, Matrix.nonsing_inv_mul _ hhu, Matrix.one_mul]`. Establish `hu : opn u ≤ 5 / 4`. Use `opn_add_le (u - 1) 1` as an intermediate fact.

Rewrite `this` using `[sub_add_cancel, opn_one]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hv : h * s = u - (u' - 1) * (h * s)` using `by rw [sub_mul, one_mul, huv]; abel`. Establish `h1 : opn (h * s) ≤ opn u + opn ((u' - 1) * (h * s))`. Combine the equalities or inequalities in the displayed calculation.

Establish `h2` using `opn_mul_le (u' - 1) (h * s)`. Establish `h3` using `opn_nonneg (h * s)`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hy2'.le h3]`.
-/
theorem ballS_subset {S : Set (Mat k r)} (hS : IsClosedSub k r S) {R : ℝ} {F : Finset (Mat k r)}
    (hF : Pack S R F) (hmax : ∀ G, Pack S R G → G.card ≤ F.card) :
    ballS S R ⊆ ⋃ h ∈ F, lmulM h ⁻¹' ballS S 2 := by
  have N := GlobalTheory.T.besselModelUnitaryGroup_opNorm_properties k r
  rintro x ⟨hxS, hxR⟩
  set s : Mat k r := Matrix.of x with hsdef
  have hsG := hS.1 hxS
  have hsu : IsUnit s.det := isUnit_det_of_mem_GG hsG
  have htS : s⁻¹ ∈ S := hS.2.2.2.2 s hxS
  have htR : opn s⁻¹ ≤ R := by rw [(N.1 s hsG).1]; exact hxR
  simp only [Set.mem_iUnion]
  by_cases ht : s⁻¹ ∈ F
  · refine ⟨s⁻¹, ht, ?_⟩
    show s⁻¹ * s ∈ S ∧ opn (s⁻¹ * s) ≤ 2
    rw [Matrix.nonsing_inv_mul _ hsu, opn_one]
    exact ⟨hS.2.2.1, by norm_num⟩
  · have hnot : ¬ Pack S R (insert s⁻¹ F) := by
      intro hG
      have := hmax _ hG
      rw [Finset.card_insert_of_notMem ht] at this
      omega
    have hex : ∃ h ∈ F, ¬ Disjoint (trU s⁻¹) (trU h) := by
      by_contra hcon
      push_neg at hcon
      apply hnot
      refine ⟨?_, ?_⟩
      · intro g hg
        rcases Finset.mem_insert.1 hg with rfl | hg
        · exact ⟨htS, htR⟩
        · exact hF.1 g hg
      · rw [Finset.coe_insert]
        exact hF.2.insert fun j hj _ => hcon j hj
    obtain ⟨h, hhF, hdis⟩ := hex
    obtain ⟨y, hy1, hy2⟩ := Set.not_disjoint_iff.1 hdis
    have hhS := (hF.1 h hhF).1
    have hhu : IsUnit h.det := isUnit_det_of_mem_GG (hS.1 hhS)
    refine ⟨h, hhF, ?_⟩
    show h * s ∈ S ∧ opn (h * s) ≤ 2
    refine ⟨hS.2.2.2.1 h hhS s hxS, ?_⟩
    have hy1' : opn (Matrix.of y * s - 1) < 1 / 4 := by
      have : opn (Matrix.of y * s⁻¹⁻¹ - 1) < 1 / 4 := hy1
      rwa [Matrix.nonsing_inv_nonsing_inv _ hsu] at this
    have hy2' : opn (Matrix.of y * h⁻¹ - 1) < 1 / 4 := hy2
    set u : Mat k r := Matrix.of y * s with hudef
    set u' : Mat k r := Matrix.of y * h⁻¹ with hu'def
    have huv : u' * (h * s) = u := by
      rw [hu'def, hudef, Matrix.mul_assoc, ← Matrix.mul_assoc h⁻¹, Matrix.nonsing_inv_mul _ hhu,
        Matrix.one_mul]
    have hu : opn u ≤ 5 / 4 := by
      have := opn_add_le (u - 1) 1
      rw [sub_add_cancel, opn_one] at this; linarith
    have hv : h * s = u - (u' - 1) * (h * s) := by rw [sub_mul, one_mul, huv]; abel
    have h1 : opn (h * s) ≤ opn u + opn ((u' - 1) * (h * s)) :=
      calc opn (h * s) = opn (u - (u' - 1) * (h * s)) := congrArg opn hv
        _ ≤ _ := opn_sub_le _ _
    have h2 := opn_mul_le (u' - 1) (h * s)
    have h3 := opn_nonneg (h * s)
    nlinarith [mul_le_mul_of_nonneg_right hy2'.le h3]

/- English proof (translation)
The claim follows from `hS.2.1.inter (isClosed_le continuous_opn continuous_const)`.
-/
theorem isClosed_ballS {S : Set (Mat k r)} (hS : IsClosedSub k r S) (R : ℝ) : IsClosed (ballS S R) :=
  hS.2.1.inter (isClosed_le continuous_opn continuous_const)

/- English proof (translation)
Establish `hc : Continuous (lmulM h : Mt k r → Mt k r)` using `continuous_const.matrix_mul (continuous_id (X := Mat k r))`. Conclude with `hc.measurable`.
-/
theorem measurable_lmulM (h : Mat k r) : Measurable (lmulM h : Mt k r → Mt k r) := by
  have hc : Continuous (lmulM h : Mt k r → Mt k r) := continuous_const.matrix_mul (continuous_id (X := Mat k r))
  exact hc.measurable

/- English proof (translation)
Take `⟨F, hF, hmax⟩` from `exists_max_pack hS R`. Establish `hcard : (F.card : ℝ≥0∞) ≤ volume (Metric.closedBall (0 : Mt k r) (5 / 4 * R)) / volume (nbhdU k r)` using `(ENNReal.le_div_iff_mul_le (Or.inl volume_nbhdU_ne_zero) (Or.inr measure_closedBall_lt_top.ne)).2 (card_mul_le hS hF)`. Establish `hball : volume (Metric.closedBall (0 : Mt k r) (5 / 4 * R)) = ENNReal.ofReal ((5 / 4 * R) ^ Module.finrank ℝ (Mt k r)) * volume (Metric.ball (0 : Mt k r) 1)` using `Measure.addHaar_closedBall volume 0 (by positivity)`. Establish `hinv : ∀ h ∈ F, μ (lmulM h ⁻¹' ballS S 2) = μ (ballS S 2)` using `fun h hh => by`. Rewrite using `[← Measure.map_apply (measurable_lmulM h) (isClosed_ballS hS 2).measurableSet, hμ.2.2.2 h (hF.1 h hh).1]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem measure_ballS_le {S : Set (Mat k r)} (hS : IsClosedSub k r S) {μ : Measure (Mt k r)}
    (hμ : IsHaarOn S μ) {R : ℝ} (hR : 0 ≤ R) :
    μ (ballS S R) ≤ ENNReal.ofReal ((5 / 4 * R) ^ Module.finrank ℝ (Mt k r)) *
      (volume (Metric.ball (0 : Mt k r) 1) / volume (nbhdU k r) * μ (ballS S 2)) := by
  obtain ⟨F, hF, hmax⟩ := exists_max_pack hS R
  have hcard : (F.card : ℝ≥0∞) ≤ volume (Metric.closedBall (0 : Mt k r) (5 / 4 * R)) / volume (nbhdU k r) :=
    (ENNReal.le_div_iff_mul_le (Or.inl volume_nbhdU_ne_zero)
        (Or.inr measure_closedBall_lt_top.ne)).2 (card_mul_le hS hF)
  have hball : volume (Metric.closedBall (0 : Mt k r) (5 / 4 * R)) =
      ENNReal.ofReal ((5 / 4 * R) ^ Module.finrank ℝ (Mt k r)) * volume (Metric.ball (0 : Mt k r) 1) :=
    Measure.addHaar_closedBall volume 0 (by positivity)
  have hinv : ∀ h ∈ F, μ (lmulM h ⁻¹' ballS S 2) = μ (ballS S 2) := fun h hh => by
    rw [← Measure.map_apply (measurable_lmulM h) (isClosed_ballS hS 2).measurableSet,
      hμ.2.2.2 h (hF.1 h hh).1]
  calc μ (ballS S R) ≤ μ (⋃ h ∈ F, lmulM h ⁻¹' ballS S 2) := measure_mono (ballS_subset hS hF hmax)
    _ ≤ ∑ h ∈ F, μ (lmulM h ⁻¹' ballS S 2) := measure_biUnion_finset_le _ _
    _ = ∑ h ∈ F, μ (ballS S 2) := Finset.sum_congr rfl hinv
    _ = F.card * μ (ballS S 2) := by simp
    _ ≤ (volume (Metric.closedBall (0 : Mt k r) (5 / 4 * R)) / volume (nbhdU k r)) * μ (ballS S 2) := by
        gcongr
    _ = _ := by rw [hball]; simp only [div_eq_mul_inv]; ring

/- English proof (translation)
Simplify using `[Module.finrank_pi_fintype, Complex.finrank_real_complex]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem finrank_Mt : (Module.finrank ℝ (Mt k r) : ℝ) = 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by
  simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
  ring

/- English proof (translation)
Introduce `k r S μ A hS hμ hA`. Use `set d := Module.finrank ℝ (Mt k r) with hd`. Establish `hdA : (d : ℝ) < A` using `by rw [hd, finrank_Mt]; exact hA`. Establish `hA0 : 0 < A` using `lt_of_le_of_lt (Nat.cast_nonneg d) hdA`. Use `set K := volume (Metric.ball (0 : Mt k r) 1) / volume (nbhdU k r) * μ (ballS S 2) with hKdef`.

Establish `hK : K < ⊤`. Establish `hV : μ (ballS S 2) < ⊤` using `(GlobalTheory.T.closedSubgroupBessel_haar_finite_compact_pos_open k r S μ hS hμ).1 _ (GlobalTheory.T.isCompact_normBounded_besselClosedSubgroup k r S hS 2)`. Conclude with `ENNReal.mul_lt_top (ENNReal.div_lt_top measure_ball_lt_top.ne volume_nbhdU_ne_zero) hV`. Use `set q : ℝ := (2 : ℝ) ^ d * (2 : ℝ) ^ (-A) with hqdef`. Establish `hq0 : 0 ≤ q` using `by positivity`.

Establish `hq1 : q < 1`. Establish `: q = (2 : ℝ) ^ ((d : ℝ) + -A)`. Rewrite using `[Real.rpow_add (by norm_num), Real.rpow_natCast]`. Rewrite using `[this]`. Conclude with `Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)`.

Establish `hconv : ∀ j : ℕ, ((2 : ℝ) ^ j) ^ (-A) = ((2 : ℝ) ^ (-A)) ^ j` using `fun j => by`. Rewrite using `[← Real.rpow_natCast (2 : ℝ) j, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast ((2 : ℝ) ^ (-A)) j, ← Real.rpow_mul (by norm_num), mul_comm]`. Establish `hae : ∀ᵐ x ∂μ, Matrix.of x ∈ S`. Rewrite using `[ae_iff]`. Conclude with `hμ.2.2.1`.

Establish `hpt : ∀ᵐ x ∂μ, ENNReal.ofReal (opn (Matrix.of x) ^ (-A)) ≤ ∑' j : ℕ, (ballS S ((2 : ℝ) ^ (j + 1))).indicator (fun _ => ENNReal.ofReal (((2 : ℝ) ^ j) ^ (-A))) x` using `by filter_upwards [hae] with x hx`. Establish `h1 : 1 ≤ opn (Matrix.of x)` using `((GlobalTheory.T.besselModelUnitaryGroup_opNorm_properties k r).1 _ (hS.1 hx)).2`. Establish `hex : ∃ j : ℕ, opn (Matrix.of x) < (2 : ℝ) ^ (j + 1)`. Take `⟨j, hj⟩` from `pow_unbounded_of_one_lt (opn (Matrix.of x)) (by norm_num : (1 : ℝ) < 2)`. Conclude with `⟨j, hj.trans (pow_lt_pow_right₀ (by norm_num) (Nat.lt_succ_self j))⟩`.

Use `set j := Nat.find hex with hjdef`. Establish `hj : opn (Matrix.of x) < (2 : ℝ) ^ (j + 1)` using `Nat.find_spec hex`. Establish `hj' : (2 : ℝ) ^ j ≤ opn (Matrix.of x)`. Break down `Nat.eq_zero_or_pos j with h0 | hpos` into its components or cases. Rewrite using `[h0, pow_zero]`.

Conclude with `h1`. Use `Nat.find_min hex (show j - 1 < Nat.find hex by omega)` as an intermediate fact. Rewrite `this` using `[show Nat.find hex - 1 + 1 = j by omega]`. Conclude with `not_lt.1 this`. Use `le_trans ?_ (ENNReal.le_tsum j)` and prove the remaining obligations.

Rewrite using `[Set.indicator_of_mem (show x ∈ ballS S ((2 : ℝ) ^ (j + 1)) from ⟨hx, hj.le⟩)]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Rewrite using `[Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]`. Conclude with `inv_anti₀ (by positivity) (Real.rpow_le_rpow (by positivity) hj' hA0.le)`. Establish `hmeasT : ∀ j : ℕ, MeasurableSet (ballS S ((2 : ℝ) ^ (j + 1)))` using `fun j => (isClosed_ballS hS _).measurableSet`.

Unfold `normInt`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[lintegral_tsum fun j => (measurable_const.indicator (hmeasT j)).aemeasurable]`. Use `congr 1`. Use function extensionality and compare the values at `j`.

Conclude with `lintegral_indicator_const (hmeasT j) _`. Use `_ ≤ ∑' j : ℕ, ENNReal.ofReal ((5 / 2 : ℝ) ^ d) * K * ENNReal.ofReal q ^ j := by`. Use `ENNReal.tsum_le_tsum fun j => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow hq0, hconv j]`.

Establish `e : ((2 : ℝ) ^ (-A)) ^ j * (5 / 4 * (2 : ℝ) ^ (j + 1)) ^ d = (5 / 2 : ℝ) ^ d * q ^ j`. Rewrite using `[hqdef, show (5 / 2 : ℝ) = 5 / 4 * 2 by norm_num]; ring`. Rewrite using `[e, ENNReal.ofReal_mul (by positivity)]; ring`. Use `_ = ENNReal.ofReal ((5 / 2 : ℝ) ^ d) * K * ∑' j : ℕ, ENNReal.ofReal q ^ j := ENNReal.tsum_mul_left`. Use `_ < ⊤ := by`.

Rewrite using `[ENNReal.tsum_geometric]`. Use `ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK) ?_` and prove the remaining obligations. Rewrite using `[ENNReal.inv_lt_top]`. Conclude with `tsub_pos_of_lt (ENNReal.ofReal_lt_one.2 hq1)`.
-/
theorem normInt_lt_top : ∀ (k r : ℕ) (S : Set (Mat k r)) (μ : Measure (Mt k r)) (A : ℝ),
    IsClosedSub k r S → IsHaarOn S μ → 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < A → normInt μ A < ⊤ := by
  intro k r S μ A hS hμ hA
  set d := Module.finrank ℝ (Mt k r) with hd
  have hdA : (d : ℝ) < A := by rw [hd, finrank_Mt]; exact hA
  have hA0 : 0 < A := lt_of_le_of_lt (Nat.cast_nonneg d) hdA
  set K := volume (Metric.ball (0 : Mt k r) 1) / volume (nbhdU k r) * μ (ballS S 2) with hKdef
  have hK : K < ⊤ := by
    have hV : μ (ballS S 2) < ⊤ := (GlobalTheory.T.closedSubgroupBessel_haar_finite_compact_pos_open k r S μ hS hμ).1 _ (GlobalTheory.T.isCompact_normBounded_besselClosedSubgroup k r S hS 2)
    exact ENNReal.mul_lt_top (ENNReal.div_lt_top measure_ball_lt_top.ne volume_nbhdU_ne_zero) hV
  set q : ℝ := (2 : ℝ) ^ d * (2 : ℝ) ^ (-A) with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    have : q = (2 : ℝ) ^ ((d : ℝ) + -A) := by
      rw [Real.rpow_add (by norm_num), Real.rpow_natCast]
    rw [this]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hconv : ∀ j : ℕ, ((2 : ℝ) ^ j) ^ (-A) = ((2 : ℝ) ^ (-A)) ^ j := fun j => by
    rw [← Real.rpow_natCast (2 : ℝ) j, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast ((2 : ℝ) ^ (-A)) j,
      ← Real.rpow_mul (by norm_num), mul_comm]
  have hae : ∀ᵐ x ∂μ, Matrix.of x ∈ S := by
    rw [ae_iff]; exact hμ.2.2.1
  have hpt : ∀ᵐ x ∂μ, ENNReal.ofReal (opn (Matrix.of x) ^ (-A)) ≤
      ∑' j : ℕ, (ballS S ((2 : ℝ) ^ (j + 1))).indicator (fun _ => ENNReal.ofReal (((2 : ℝ) ^ j) ^ (-A))) x := by
    filter_upwards [hae] with x hx
    have h1 : 1 ≤ opn (Matrix.of x) := ((GlobalTheory.T.besselModelUnitaryGroup_opNorm_properties k r).1 _ (hS.1 hx)).2
    have hex : ∃ j : ℕ, opn (Matrix.of x) < (2 : ℝ) ^ (j + 1) := by
      obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (opn (Matrix.of x)) (by norm_num : (1 : ℝ) < 2)
      exact ⟨j, hj.trans (pow_lt_pow_right₀ (by norm_num) (Nat.lt_succ_self j))⟩
    classical
    set j := Nat.find hex with hjdef
    have hj : opn (Matrix.of x) < (2 : ℝ) ^ (j + 1) := Nat.find_spec hex
    have hj' : (2 : ℝ) ^ j ≤ opn (Matrix.of x) := by
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · rw [h0, pow_zero]; exact h1
      · have := Nat.find_min hex (show j - 1 < Nat.find hex by omega)
        rw [show Nat.find hex - 1 + 1 = j by omega] at this
        exact not_lt.1 this
    refine le_trans ?_ (ENNReal.le_tsum j)
    rw [Set.indicator_of_mem (show x ∈ ballS S ((2 : ℝ) ^ (j + 1)) from ⟨hx, hj.le⟩)]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
    exact inv_anti₀ (by positivity) (Real.rpow_le_rpow (by positivity) hj' hA0.le)
  have hmeasT : ∀ j : ℕ, MeasurableSet (ballS S ((2 : ℝ) ^ (j + 1))) := fun j =>
    (isClosed_ballS hS _).measurableSet
  unfold normInt
  calc ∫⁻ x, ENNReal.ofReal (opn (Matrix.of x) ^ (-A)) ∂μ
      ≤ ∫⁻ x, ∑' j : ℕ, (ballS S ((2 : ℝ) ^ (j + 1))).indicator
          (fun _ => ENNReal.ofReal (((2 : ℝ) ^ j) ^ (-A))) x ∂μ := lintegral_mono_ae hpt
    _ = ∑' j : ℕ, ENNReal.ofReal (((2 : ℝ) ^ j) ^ (-A)) * μ (ballS S ((2 : ℝ) ^ (j + 1))) := by
        rw [lintegral_tsum fun j => (measurable_const.indicator (hmeasT j)).aemeasurable]
        congr 1; funext j; exact lintegral_indicator_const (hmeasT j) _
    _ ≤ ∑' j : ℕ, ENNReal.ofReal ((5 / 2 : ℝ) ^ d) * K * ENNReal.ofReal q ^ j := by
        refine ENNReal.tsum_le_tsum fun j => ?_
        calc ENNReal.ofReal (((2 : ℝ) ^ j) ^ (-A)) * μ (ballS S ((2 : ℝ) ^ (j + 1)))
            ≤ ENNReal.ofReal (((2 : ℝ) ^ j) ^ (-A)) *
                (ENNReal.ofReal ((5 / 4 * (2 : ℝ) ^ (j + 1)) ^ d) * K) := by
              gcongr; exact measure_ballS_le hS hμ (by positivity)
          _ = ENNReal.ofReal ((5 / 2 : ℝ) ^ d) * K * ENNReal.ofReal q ^ j := by
              rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow hq0, hconv j]
              have e : ((2 : ℝ) ^ (-A)) ^ j * (5 / 4 * (2 : ℝ) ^ (j + 1)) ^ d = (5 / 2 : ℝ) ^ d * q ^ j := by
                rw [hqdef, show (5 / 2 : ℝ) = 5 / 4 * 2 by norm_num]; ring
              rw [e, ENNReal.ofReal_mul (by positivity)]; ring
    _ = ENNReal.ofReal ((5 / 2 : ℝ) ^ d) * K * ∑' j : ℕ, ENNReal.ofReal q ^ j := ENNReal.tsum_mul_left
    _ < ⊤ := by
        rw [ENNReal.tsum_geometric]
        refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK) ?_
        rw [ENNReal.inv_lt_top]
        exact tsub_pos_of_lt (ENNReal.ofReal_lt_one.2 hq1)

end GlobalTheory.SgGrowth
