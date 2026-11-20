import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PiMapMulRight

noncomputable section

open MeasureTheory Topology
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM

section Fac

variable {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type} [∀ i, MeasurableSpace (α i)]

/- English proof (translation)
Establish `key : ∀ i, ∃ s : Set (α i), MeasurableSet s ∧ μ i s ≠ 0 ∧ μ i s ≠ ∞`. Introduce `i`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Apply `hne i` to reduce the goal to its premises.

Establish `hz : ∀ n, μ i (spanningSets (μ i) n) = 0` using `fun n => by`. Assume the negation of the conclusion as `h0`. Conclude with `(measure_spanningSets_lt_top (μ i) n).ne (hc _ (measurableSet_spanningSets _ n) h0)`. Rewrite using `[← Measure.measure_univ_eq_zero, ← iUnion_spanningSets (μ i)]`. Conclude with `measure_iUnion_null hz`.

Use `choose S hS1 hS2 hS3 using key`. Conclude with `⟨S, hS1, hS2, hS3⟩`.
-/
theorem exists_box_alt (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (hne : ∀ i, μ i ≠ 0) :
    ∃ S : ∀ i, Set (α i), (∀ i, MeasurableSet (S i)) ∧ (∀ i, μ i (S i) ≠ 0) ∧ ∀ i, μ i (S i) ≠ ∞ := by
  have key : ∀ i, ∃ s : Set (α i), MeasurableSet s ∧ μ i s ≠ 0 ∧ μ i s ≠ ∞ := by
    intro i
    by_contra hc
    push_neg at hc
    apply hne i
    have hz : ∀ n, μ i (spanningSets (μ i) n) = 0 := fun n => by
      by_contra h0
      exact (measure_spanningSets_lt_top (μ i) n).ne (hc _ (measurableSet_spanningSets _ n) h0)
    rw [← Measure.measure_univ_eq_zero, ← iUnion_spanningSets (μ i)]
    exact measure_iUnion_null hz
  choose S hS1 hS2 hS3 using key
  exact ⟨S, hS1, hS2, hS3⟩

/- English proof (translation)
Rewrite using `[Measure.pi_pi, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v), Function.update_self]`. Use `congr 1`. Use `Finset.prod_congr rfl fun w hw => ?_` and prove the remaining obligations. Rewrite using `[Function.update_of_ne (Finset.ne_of_mem_erase hw)]`.
-/
theorem pi_box_eval (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (S : ∀ i, Set (α i)) (v : ι) (A : Set (α v)) :
    Measure.pi μ (Set.univ.pi (Function.update S v A)) = μ v A * ∏ w ∈ Finset.univ.erase v, μ w (S w) := by
  rw [Measure.pi_pi, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun w hw => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]

/- English proof (translation)
Take `⟨S, -, hS0, hSt⟩` from `exists_box_alt μ hne`. Use extensionality with `A _`. Establish `h1` using `pi_box_eval μ' S v A`. Establish `h2` using `pi_box_eval μ S v A`. Establish `hP : ∏ w ∈ Finset.univ.erase v, μ' w (S w) = ∏ w ∈ Finset.univ.erase v, μ w (S w)` using `Finset.prod_congr rfl fun w hm => by rw [hw w (Finset.ne_of_mem_erase hm)]`.

Rewrite `h1` using `[h, h2, hP]`. Establish `hP0 : ∏ w ∈ Finset.univ.erase v, μ w (S w) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun w _ => hS0 w`. Establish `hPt : ∏ w ∈ Finset.univ.erase v, μ w (S w) ≠ ∞` using `ENNReal.prod_ne_top fun w _ => hSt w`. Conclude with `((ENNReal.mul_left_inj hP0 hPt).mp h1).symm`.
-/
theorem factor_eq (μ μ' : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (μ' i)]
    (hne : ∀ i, μ i ≠ 0) (v : ι) (hw : ∀ w, w ≠ v → μ' w = μ w) (h : Measure.pi μ' = Measure.pi μ) : μ' v = μ v := by
  obtain ⟨S, -, hS0, hSt⟩ := exists_box_alt μ hne
  ext A _
  have h1 := pi_box_eval μ' S v A
  have h2 := pi_box_eval μ S v A
  have hP : ∏ w ∈ Finset.univ.erase v, μ' w (S w) = ∏ w ∈ Finset.univ.erase v, μ w (S w) :=
    Finset.prod_congr rfl fun w hm => by rw [hw w (Finset.ne_of_mem_erase hm)]
  rw [h, h2, hP] at h1
  have hP0 : ∏ w ∈ Finset.univ.erase v, μ w (S w) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => hS0 w
  have hPt : ∏ w ∈ Finset.univ.erase v, μ w (S w) ≠ ∞ := ENNReal.prod_ne_top fun w _ => hSt w
  exact ((ENNReal.mul_left_inj hP0 hPt).mp h1).symm

/- English proof (translation)
Establish `hsub : Set.univ.pi (Function.update (fun w => (Set.univ : Set (α w))) v (N v)ᶜ) ⊆ (Set.univ.pi N)ᶜ`. Introduce `x hx hxN`. Establish `hv` using `hx v (Set.mem_univ v)`. Rewrite `hv` using `[Function.update_self]`. Conclude with `hv (hxN v (Set.mem_univ v))`.

Establish `h0` using `measure_mono_null hsub hc`. Rewrite `h0` using `[pi_box_eval]`. Break down `mul_eq_zero.mp h0 with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction.

Take `⟨w, -, hw⟩` from `Finset.prod_eq_zero_iff.mp h`. Conclude with `hne w (Measure.measure_univ_eq_zero.mp hw)`.
-/
theorem factor_conc (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (hne : ∀ i, μ i ≠ 0) (N : ∀ i, Set (α i))
    (hc : Measure.pi μ (Set.univ.pi N)ᶜ = 0) (v : ι) : μ v (N v)ᶜ = 0 := by
  have hsub : Set.univ.pi (Function.update (fun w => (Set.univ : Set (α w))) v (N v)ᶜ) ⊆
      (Set.univ.pi N)ᶜ := by
    intro x hx hxN
    have hv := hx v (Set.mem_univ v)
    rw [Function.update_self] at hv
    exact hv (hxN v (Set.mem_univ v))
  have h0 := measure_mono_null hsub hc
  rw [pi_box_eval] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · exact h
  · exfalso
    obtain ⟨w, -, hw⟩ := Finset.prod_eq_zero_iff.mp h
    exact hne w (Measure.measure_univ_eq_zero.mp hw)

/- English proof (translation)
Introduce `hv`. Apply `h` to reduce the goal to its premises. Rewrite using `[← Measure.measure_univ_eq_zero, ← Set.pi_univ Set.univ, Measure.pi_pi]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hv])`.
-/
theorem factor_ne (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (h : Measure.pi μ ≠ 0) (v : ι) : μ v ≠ 0 := by
  intro hv
  apply h
  rw [← Measure.measure_univ_eq_zero, ← Set.pi_univ Set.univ, Measure.pi_pi]
  exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hv])

end Fac

section FacG

variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, IsTopologicalGroup (G v)] [∀ v, SecondCountableTopology (G v)] [∀ v, MeasurableSpace (G v)]
  [∀ v, BorelSpace (G v)]

/- English proof (translation)
Establish `hne : ∀ w, μ w ≠ 0` using `fun w => factor_ne μ h0 w`. Establish `hμc : μ v (H v : Set (G v))ᶜ = 0` using `factor_conc μ hne (fun w => (H w : Set (G w))) hc v`. Establish `hμi : ∀ h ∈ H v, (μ v).map (fun x => h * x) = μ v`. Introduce `h hh`. Set `g : (w : ι) → G w` to `Pi.mulSingle v h`.

Establish `hg : ∀ w, g w ∈ H w`. Introduce `w`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Simplify `hh` using `[g]`.

Simplify using `[g, Pi.mulSingle_eq_of_ne hw, (H w).one_mem]`. Set `μ' : ∀ w, Measure (G w)` to `fun w => (μ w).map (fun x => g w * x)`. Use `haveI hσ : ∀ w, SigmaFinite (μ' w) := fun w => (MeasurableEquiv.mulLeft (g w)).sigmaFinite_map (μ := μ w)`. Establish `hpi : Measure.pi μ' = Measure.pi μ`. Rewrite using `[← Measure.pi_map_pi (fun w => (measurable_const_mul (g w)).aemeasurable)]`.

Conclude with `hi g hg`. Establish `hw : ∀ w, w ≠ v → μ' w = μ w`. Introduce `w hw`. Simplify using `[μ', g, Pi.mulSingle_eq_of_ne hw]`. Use `factor_eq μ μ' hne v hw hpi` as an intermediate fact.

Simplify `this` using `[μ', g]`. Conclude with `uniq_on_closed (H v) (hH v) (μ v) (ν v) hμc (hνc v) hμi (hνi v) (hne v) (hν0 v)`.
-/
theorem factor_uniq (μ : ∀ v, Measure (G v)) [∀ v, SigmaFinite (μ v)] (H : ∀ v, Subgroup (G v))
    (hH : ∀ v, IsClosed (H v : Set (G v))) (ν : ∀ v, Measure (G v)) [∀ v, SigmaFinite (ν v)]
    (hνc : ∀ v, ν v (H v : Set (G v))ᶜ = 0) (hνi : ∀ v, ∀ h ∈ H v, (ν v).map (fun x => h * x) = ν v)
    (hν0 : ∀ v, ν v ≠ 0) (h0 : Measure.pi μ ≠ 0)
    (hc : Measure.pi μ (Set.univ.pi fun v => (H v : Set (G v)))ᶜ = 0)
    (hi : ∀ g : (v : ι) → G v, (∀ v, g v ∈ H v) → (Measure.pi μ).map (fun x => g * x) = Measure.pi μ) (v : ι) :
    ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ μ v = κ • ν v := by
  have hne : ∀ w, μ w ≠ 0 := fun w => factor_ne μ h0 w
  have hμc : μ v (H v : Set (G v))ᶜ = 0 := factor_conc μ hne (fun w => (H w : Set (G w))) hc v
  have hμi : ∀ h ∈ H v, (μ v).map (fun x => h * x) = μ v := by
    intro h hh
    let g : (w : ι) → G w := Pi.mulSingle v h
    have hg : ∀ w, g w ∈ H w := by
      intro w
      by_cases hw : w = v
      · subst hw
        simpa [g] using hh
      · simp [g, Pi.mulSingle_eq_of_ne hw, (H w).one_mem]
    let μ' : ∀ w, Measure (G w) := fun w => (μ w).map (fun x => g w * x)
    haveI hσ : ∀ w, SigmaFinite (μ' w) := fun w =>
      (MeasurableEquiv.mulLeft (g w)).sigmaFinite_map (μ := μ w)
    have hpi : Measure.pi μ' = Measure.pi μ := by
      rw [← Measure.pi_map_pi (fun w => (measurable_const_mul (g w)).aemeasurable)]
      exact hi g hg
    have hw : ∀ w, w ≠ v → μ' w = μ w := by
      intro w hw
      simp [μ', g, Pi.mulSingle_eq_of_ne hw]
    have := factor_eq μ μ' hne v hw hpi
    simpa [μ', g] using this
  exact uniq_on_closed (H v) (hH v) (μ v) (ν v) hμc (hνc v) hμi (hνi v) (hne v) (hν0 v)

end FacG

end Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM
