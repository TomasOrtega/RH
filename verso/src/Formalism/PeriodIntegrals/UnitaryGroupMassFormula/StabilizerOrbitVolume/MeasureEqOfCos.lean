import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.CosDens

noncomputable section

namespace PI.VolStabSW

open MeasureTheory Topology Set Filter

section CosMeas

variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [MeasurableSpace X] [OpensMeasurableSpace X]

omit [MeasurableSpace X] [OpensMeasurableSpace X] in

def thick (S : Set X) (Λ : AddSubgroup X) : Set X := {x | ∃ s ∈ S, x - s ∈ Λ}

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
/- English proof (translation)
Establish `: thick S Λ = ⋃ s ∈ S, (fun x => x - s) ⁻¹' (Λ : Set X)`. Use extensionality with `x`. Simplify using `[thick]`. Rewrite using `[this]`. Conclude with `isOpen_biUnion fun s _ => hΛ.preimage (continuous_id.sub continuous_const)`.
-/
theorem isOpen_thick (S : Set X) (Λ : AddSubgroup X) (hΛ : IsOpen (Λ : Set X)) :
    IsOpen (thick S Λ) := by
  have : thick S Λ = ⋃ s ∈ S, (fun x => x - s) ⁻¹' (Λ : Set X) := by
    ext x; simp [thick]
  rw [this]
  exact isOpen_biUnion fun s _ => hΛ.preimage (continuous_id.sub continuous_const)

/- English proof (translation)
Establish `hC : ∀ y, IsOpen {z : X | z - y ∈ Λ}` using `fun y => hΛ.preimage (continuous_id.sub continuous_const)`. Establish `hfin : ∀ t : Finset X, m1 (⋃ s ∈ t, {z | z - s ∈ Λ}) = m2 (⋃ s ∈ t, {z | z - s ∈ Λ})`. Introduce `t`. Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => simp`.

Consider the case `insert s0 t hs0 ih`. Rewrite using `[Finset.set_biUnion_insert]`. Distinguish the cases in `hex : ∃ s ∈ t, s0 - s ∈ Λ`. Take `⟨s, hs, hss⟩` from `hex`. Establish `hsub : {z : X | z - s0 ∈ Λ} ⊆ ⋃ s ∈ t, {z | z - s ∈ Λ}`.

Introduce `z hz`. Simplify using `only [Set.mem_iUnion, Set.mem_setOf_eq]`. Conclude with `⟨s, hs, by simpa [sub_add_sub_cancel] using Λ.add_mem hz hss⟩`. Rewrite using `[Set.union_eq_right.2 hsub, ih]`. Use `push_neg at hex`.

Establish `hdisj : Disjoint {z : X | z - s0 ∈ Λ} (⋃ s ∈ t, {z | z - s ∈ Λ})`. Rewrite using `[Set.disjoint_left]`. Introduce `z hz hz'`. Simplify using `only [Set.mem_iUnion, Set.mem_setOf_eq] at hz'`. Take `⟨s, hs, hzs⟩` from `hz'`.

Apply `hex s hs` to reduce the goal to its premises. Simplify `Λ.sub_mem hzs hz` using `[sub_sub_sub_cancel_left]`. Establish `hmeas : MeasurableSet (⋃ s ∈ t, {z : X | z - s ∈ Λ})` using `(isOpen_biUnion fun s _ => hC s).measurableSet`. Rewrite using `[measure_union hdisj hmeas, measure_union hdisj hmeas, h, ih]`. Take `⟨t, htS, hcov⟩` from `hS.elim_nhds_subcover (fun x => {z : X | z - x ∈ Λ}) (fun x _ => (hC x).mem_nhds (by simp [Λ.zero_mem]))`.

Establish `heq : thick S Λ = ⋃ s ∈ t, {z : X | z - s ∈ Λ}`. Use extensionality with `x`. Simplify using `only [thick, Set.mem_setOf_eq, Set.mem_iUnion]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, hxs⟩`.

Take `⟨u, hu, hsu⟩` from `Set.mem_iUnion₂.1 (hcov hs)`. Conclude with `⟨u, hu, by simpa [sub_add_sub_cancel] using Λ.add_mem hxs hsu⟩`. Introduce and unpack `⟨u, hu, hxu⟩`. Conclude with `⟨u, htS u hu, hxu⟩`. Rewrite using `[heq]`.

Conclude with `hfin t`.
-/
theorem measure_thick_eq (m1 m2 : Measure X) (Λ : AddSubgroup X) (hΛ : IsOpen (Λ : Set X))
    (h : ∀ y, m1 {z | z - y ∈ Λ} = m2 {z | z - y ∈ Λ}) (S : Set X) (hS : IsCompact S) :
    m1 (thick S Λ) = m2 (thick S Λ) := by
  classical
  have hC : ∀ y, IsOpen {z : X | z - y ∈ Λ} := fun y =>
    hΛ.preimage (continuous_id.sub continuous_const)
  have hfin : ∀ t : Finset X,
      m1 (⋃ s ∈ t, {z | z - s ∈ Λ}) = m2 (⋃ s ∈ t, {z | z - s ∈ Λ}) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert s0 t hs0 ih =>
      rw [Finset.set_biUnion_insert]
      by_cases hex : ∃ s ∈ t, s0 - s ∈ Λ
      · obtain ⟨s, hs, hss⟩ := hex
        have hsub : {z : X | z - s0 ∈ Λ} ⊆ ⋃ s ∈ t, {z | z - s ∈ Λ} := by
          intro z hz
          simp only [Set.mem_iUnion, Set.mem_setOf_eq]
          exact ⟨s, hs, by simpa [sub_add_sub_cancel] using Λ.add_mem hz hss⟩
        rw [Set.union_eq_right.2 hsub, ih]
      · push_neg at hex
        have hdisj : Disjoint {z : X | z - s0 ∈ Λ} (⋃ s ∈ t, {z | z - s ∈ Λ}) := by
          rw [Set.disjoint_left]
          intro z hz hz'
          simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hz'
          obtain ⟨s, hs, hzs⟩ := hz'
          apply hex s hs
          simpa [sub_sub_sub_cancel_left] using Λ.sub_mem hzs hz
        have hmeas : MeasurableSet (⋃ s ∈ t, {z : X | z - s ∈ Λ}) :=
          (isOpen_biUnion fun s _ => hC s).measurableSet
        rw [measure_union hdisj hmeas, measure_union hdisj hmeas, h, ih]
  obtain ⟨t, htS, hcov⟩ := hS.elim_nhds_subcover (fun x => {z : X | z - x ∈ Λ})
    (fun x _ => (hC x).mem_nhds (by simp [Λ.zero_mem]))
  have heq : thick S Λ = ⋃ s ∈ t, {z : X | z - s ∈ Λ} := by
    ext x
    simp only [thick, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨s, hs, hxs⟩
      obtain ⟨u, hu, hsu⟩ := Set.mem_iUnion₂.1 (hcov hs)
      exact ⟨u, hu, by simpa [sub_add_sub_cancel] using Λ.add_mem hxs hsu⟩
    · rintro ⟨u, hu, hxu⟩
      exact ⟨u, htS u hu, hxu⟩
  rw [heq]
  exact hfin t

omit [MeasurableSpace X] [OpensMeasurableSpace X] in

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Set.mem_iInter, thick, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Assume the negation of the conclusion as `hxS`.

Establish `hc : Continuous fun d : X => x - d` using `continuous_const.sub continuous_id`. Establish `hN : (fun d : X => x - d) ⁻¹' Sᶜ ∈ 𝓝 (0 : X)` using `hc.continuousAt.preimage_mem_nhds (hSc.isOpen_compl.mem_nhds (by simpa using hxS))`. Take `⟨n, hn⟩` from `hb _ hN`. Take `⟨s, hs, hxs⟩` from `hx n`. Establish `h1` using `hn hxs`.

Simplify using `only [Set.mem_preimage, sub_sub_cancel, Set.mem_compl_iff] at h1`. Conclude with `h1 hs`. Introduce `hx n`. Conclude with `⟨x, hx, by simp [(Λ n).zero_mem]⟩`.
-/
theorem iInter_thick (S : Set X) (hSc : IsClosed S) (Λ : ℕ → AddSubgroup X)
    (hb : ∀ N ∈ 𝓝 (0 : X), ∃ n, (Λ n : Set X) ⊆ N) : ⋂ n, thick S (Λ n) = S := by
  ext x
  simp only [Set.mem_iInter, thick, Set.mem_setOf_eq]
  constructor
  · intro hx
    by_contra hxS
    have hc : Continuous fun d : X => x - d := continuous_const.sub continuous_id
    have hN : (fun d : X => x - d) ⁻¹' Sᶜ ∈ 𝓝 (0 : X) :=
      hc.continuousAt.preimage_mem_nhds (hSc.isOpen_compl.mem_nhds (by simpa using hxS))
    obtain ⟨n, hn⟩ := hb _ hN
    obtain ⟨s, hs, hxs⟩ := hx n
    have h1 := hn hxs
    simp only [Set.mem_preimage, sub_sub_cancel, Set.mem_compl_iff] at h1
    exact h1 hs
  · intro hx n
    exact ⟨x, hx, by simp [(Λ n).zero_mem]⟩

/- English proof (translation)
Establish `hmono : Antitone fun n => thick S (Λ n)`. Introduce `i j hij x hx`. Take `⟨s, hs, hxs⟩` from `hx`. Conclude with `⟨s, hs, hanti hij hxs⟩`. Establish `hmeas : ∀ n, MeasurableSet (thick S (Λ n))` using `fun n => (isOpen_thick S (Λ n) (hΛo n)).measurableSet`.

Establish `heq : ∀ n, m1 (thick S (Λ n)) = m2 (thick S (Λ n))` using `fun n => measure_thick_eq m1 m2 (Λ n) (hΛo n) (h n) S hS`. Rewrite using `[← iInter_thick S hSc Λ hb, hmono.measure_iInter (fun n => (hmeas n).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩, hmono.measure_iInter (fun n => (hmeas n).nullMeasurableSet) ⟨0, by rw [← heq 0]; exact measure_ne_top _ _⟩]`. Repeatedly rewrite using `[heq]`.
-/
theorem measure_eq_of_cos (m1 m2 : Measure X) [IsFiniteMeasure m1]
    (Λ : ℕ → AddSubgroup X) (hΛo : ∀ n, IsOpen (Λ n : Set X)) (hanti : Antitone Λ)
    (hb : ∀ N ∈ 𝓝 (0 : X), ∃ n, (Λ n : Set X) ⊆ N)
    (h : ∀ n y, m1 {z | z - y ∈ Λ n} = m2 {z | z - y ∈ Λ n})
    (S : Set X) (hS : IsCompact S) (hSc : IsClosed S) : m1 S = m2 S := by
  have hmono : Antitone fun n => thick S (Λ n) := by
    intro i j hij x hx
    obtain ⟨s, hs, hxs⟩ := hx
    exact ⟨s, hs, hanti hij hxs⟩
  have hmeas : ∀ n, MeasurableSet (thick S (Λ n)) := fun n =>
    (isOpen_thick S (Λ n) (hΛo n)).measurableSet
  have heq : ∀ n, m1 (thick S (Λ n)) = m2 (thick S (Λ n)) := fun n =>
    measure_thick_eq m1 m2 (Λ n) (hΛo n) (h n) S hS
  rw [← iInter_thick S hSc Λ hb,
    hmono.measure_iInter (fun n => (hmeas n).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩,
    hmono.measure_iInter (fun n => (hmeas n).nullMeasurableSet)
      ⟨0, by rw [← heq 0]; exact measure_ne_top _ _⟩]
  simp_rw [heq]

end CosMeas

/- English proof (translation)
Introduce `X _ _ _ _ _ _ ν m _ hν H hHo hHc hanti hb c0 κ hm0 hcos S hS`. Establish `hC : ∀ (n : ℕ) (y : X), IsOpen {z : X | z - y ∈ H n}` using `fun n y => (hHo n).preimage (continuous_id.sub continuous_const)`. Establish `hC0 : MeasurableSet {z : X | z - c0 ∈ H 0}` using `(hC 0 c0).measurableSet`. Establish `hback : ∀ n y z, y - c0 ∉ H 0 → z - y ∈ H n → z - c0 ∉ H 0`. Introduce `n y z hy hz hz0`.

Apply `hy` to reduce the goal to its premises. Establish `hz' : z - y ∈ H 0` using `hanti (Nat.zero_le n) hz`. Simplify `(H 0).sub_mem hz0 hz'` using `[sub_sub_sub_cancel_left]`. Establish `key` using `measure_eq_of_cos m (κ • ν.restrict {z : X | z - c0 ∈ H 0}) H hHo hanti hb ?_ S hS hS.isClosed`. Rewrite using `[key, Measure.smul_apply, Measure.restrict_apply' hC0, smul_eq_mul]`.

Introduce `n y`. Rewrite using `[Measure.smul_apply, Measure.restrict_apply' hC0, smul_eq_mul]`. Distinguish the cases in `hy : y - c0 ∈ H 0`. Establish `hsub : {z : X | z - y ∈ H n} ⊆ {z : X | z - c0 ∈ H 0}`. Introduce `z hz`.

Establish `hz0 : z - y ∈ H 0` using `hanti (Nat.zero_le n) hz`. Simplify `(H 0).add_mem hz0 hy` using `[sub_add_sub_cancel]`. Rewrite using `[Set.inter_eq_left.2 hsub]`. Conclude with `hcos n y hy`. Establish `hdisj : {z : X | z - y ∈ H n} ∩ {z : X | z - c0 ∈ H 0} = ∅`.

Use extensionality with `z`. Simplify using `only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]`. Conclude with `hback n y z hy`. Rewrite using `[hdisj, measure_empty, mul_zero]`. Conclude with `measure_mono_null (fun z hz => hback n y z hy hz) hm0`.
-/
theorem cosDens_holds : CosDens := by
  intro X _ _ _ _ _ _ ν m _ hν H hHo hHc hanti hb c0 κ hm0 hcos S hS
  have hC : ∀ (n : ℕ) (y : X), IsOpen {z : X | z - y ∈ H n} := fun n y =>
    (hHo n).preimage (continuous_id.sub continuous_const)
  have hC0 : MeasurableSet {z : X | z - c0 ∈ H 0} := (hC 0 c0).measurableSet
  have hback : ∀ n y z, y - c0 ∉ H 0 → z - y ∈ H n → z - c0 ∉ H 0 := by
    intro n y z hy hz hz0
    apply hy
    have hz' : z - y ∈ H 0 := hanti (Nat.zero_le n) hz
    simpa [sub_sub_sub_cancel_left] using (H 0).sub_mem hz0 hz'
  have key := measure_eq_of_cos m (κ • ν.restrict {z : X | z - c0 ∈ H 0}) H hHo hanti hb ?_
    S hS hS.isClosed
  · rw [key, Measure.smul_apply, Measure.restrict_apply' hC0, smul_eq_mul]
  · intro n y
    rw [Measure.smul_apply, Measure.restrict_apply' hC0, smul_eq_mul]
    by_cases hy : y - c0 ∈ H 0
    · have hsub : {z : X | z - y ∈ H n} ⊆ {z : X | z - c0 ∈ H 0} := by
        intro z hz
        have hz0 : z - y ∈ H 0 := hanti (Nat.zero_le n) hz
        simpa [sub_add_sub_cancel] using (H 0).add_mem hz0 hy
      rw [Set.inter_eq_left.2 hsub]
      exact hcos n y hy
    · have hdisj : {z : X | z - y ∈ H n} ∩ {z : X | z - c0 ∈ H 0} = ∅ := by
        ext z
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
          not_and]
        exact hback n y z hy
      rw [hdisj, measure_empty, mul_zero]
      exact measure_mono_null (fun z hz => hback n y z hy hz) hm0

end PI.VolStabSW
