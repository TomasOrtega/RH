import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open MeasureTheory
open ReciprocityTheory.AnForm.A (regMax tmax kθ)

noncomputable section

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
theorem abs_lt_of_kθ_ne_zero {x : ℝ} (h : kθ x ≠ 0) : |x| < 1 / 2 := by
  have hs : x ∈ Function.support kθ := h
  unfold kθ at hs
  rw [ContDiffBump.support_normed_eq] at hs
  simpa [Real.dist_eq] using hs

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem integral_kθ : ∫ x, kθ x = 1 := by
  unfold kθ
  exact ContDiffBump.integral_normed _

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem le_tmax {ι : Type*} [Fintype ι] [Nonempty ι] (t : ι → ℝ) (i : ι) : t i ≤ tmax t :=
  Finset.le_sup' t (Finset.mem_univ i)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tmax_le {ι : Type*} [Fintype ι] [Nonempty ι] {t : ι → ℝ} {c : ℝ} (h : ∀ i, t i ≤ c) :
    tmax t ≤ c :=
  Finset.sup'_le _ _ fun i _ => h i

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem tmax_comp_equiv {κ ι : Type*} [Fintype κ] [Nonempty κ] [Fintype ι] [Nonempty ι]
    (e : κ ≃ ι) (t : ι → ℝ) : tmax (t ∘ e) = tmax t := by
  refine le_antisymm (tmax_le fun k => le_tmax t (e k)) (tmax_le fun i => ?_)
  have := le_tmax (t ∘ e) (e.symm i)
  simpa using this

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem regMax_comp_equiv {κ ι : Type} [Fintype κ] [Nonempty κ] [Fintype ι] [Nonempty ι]
    (e : κ ≃ ι) (η : ℝ) (t : ι → ℝ) : regMax η (t ∘ e) = regMax η t := by
  unfold regMax
  rw [← (volume_measurePreserving_piCongrLeft (fun _ : ι => ℝ) e).integral_comp']
  congr 1
  funext g
  have hg : ∀ k, (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e) g (e k) = g k := fun k => by
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  set h := (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e) g
  have h1 : tmax (fun j => t j + η * h j) = tmax (fun k => (t ∘ e) k + η * g k) := by
    rw [← tmax_comp_equiv e (fun j => t j + η * h j)]
    congr 1
    funext k
    simp [hg]
  have h2 : ∏ j, kθ (h j) = ∏ k, kθ (g k) := by
    rw [← e.prod_comp]
    simp [hg]
  rw [h1, h2]

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Separate the alternatives or extract the components of the hypothesis.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion repeatedly using the stated equalities.

Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem regMax_subtype {ι : Type} [Fintype ι] [Nonempty ι] (p : ι → Prop) [DecidablePred p]
    [Nonempty {i // p i}] {η : ℝ} (hη : 0 ≤ η) (t : ι → ℝ)
    (hdom : ∀ i, ¬ p i → ∃ k, p k ∧ t i + η ≤ t k) :
    regMax η t = regMax η (fun k : {i // p i} => t k) := by
  unfold regMax
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) p
  have hmp : MeasurePreserving e (volume : Measure (ι → ℝ))
      ((volume : Measure ({i // p i} → ℝ)).prod (volume : Measure ({i // ¬ p i} → ℝ))) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : ι => (volume : Measure ℝ)) p
  rw [← (hmp.symm e).integral_comp']
  have hpt : ∀ q : ({i // p i} → ℝ) × ({i // ¬ p i} → ℝ),
      tmax (fun j => t j + η * e.symm q j) * ∏ j, kθ (e.symm q j) =
        (tmax (fun k : {i // p i} => t k + η * q.1 k) * ∏ k, kθ (q.1 k)) *
          ∏ k, kθ (q.2 k) := by
    intro q
    have hv1 : ∀ k : {i // p i}, e.symm q k = q.1 k := fun k => by
      simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, k.2]
    have hv2 : ∀ k : {i // ¬ p i}, e.symm q k = q.2 k := fun k => by
      simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, k.2]
    have hprod : ∏ j, kθ (e.symm q j) = (∏ k : {i // p i}, kθ (q.1 k)) * ∏ k, kθ (q.2 k) := by
      rw [← Fintype.prod_subtype_mul_prod_subtype p]
      simp [hv1, hv2]
    rw [hprod]
    by_cases hall : ∀ j, kθ (e.symm q j) ≠ 0
    · have hb : ∀ j, |e.symm q j| < 1 / 2 := fun j => abs_lt_of_kθ_ne_zero (hall j)
      have htm : tmax (fun j => t j + η * e.symm q j) =
          tmax (fun k : {i // p i} => t k + η * q.1 k) := by
        refine le_antisymm (tmax_le fun j => ?_) (tmax_le fun k => ?_)
        · by_cases hj : p j
          · have := le_tmax (fun k : {i // p i} => t k + η * q.1 k) ⟨j, hj⟩
            simpa [hv1 ⟨j, hj⟩] using this
          · obtain ⟨k, hk, hjk⟩ := hdom j hj
            have h1 := (abs_lt.1 (hb j)).2
            have h2 := (abs_lt.1 (hb k)).1
            have h3 := le_tmax (fun k : {i // p i} => t k + η * q.1 k) ⟨k, hk⟩
            simp only [← hv1 ⟨k, hk⟩] at h3
            have h4 : η * e.symm q j ≤ η * (1 / 2) := mul_le_mul_of_nonneg_left h1.le hη
            have h5 : η * (-(1 / 2)) ≤ η * e.symm q k := mul_le_mul_of_nonneg_left h2.le hη
            linarith
        · have := le_tmax (fun j => t j + η * e.symm q j) k
          simpa [hv1 k] using this
      rw [htm, mul_assoc]
    · push Not at hall
      obtain ⟨j, hj⟩ := hall
      have h0 : ∏ j, kθ (e.symm q j) = 0 := Finset.prod_eq_zero (Finset.mem_univ j) hj
      rw [hprod] at h0
      rcases mul_eq_zero.1 h0 with h | h
      · rw [h]; ring
      · rw [h]; ring
  simp_rw [hpt]
  rw [integral_prod_mul (fun h1 : {i // p i} → ℝ =>
      tmax (fun k : {i // p i} => t k + η * h1 k) * ∏ k, kθ (h1 k))
    (fun h2 : {i // ¬ p i} → ℝ => ∏ k, kθ (h2 k))]
  have hH : ∫ h2 : {i // ¬ p i} → ℝ, ∏ k, kθ (h2 k) = 1 := by
    rw [show (volume : Measure ({i // ¬ p i} → ℝ)) = Measure.pi fun _ => volume from rfl,
      integral_fintype_prod_eq_prod (fun _ => kθ)]
    simp [integral_kθ]
  rw [hH, mul_one]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem regMax_of_injective {κ ι : Type} [Fintype κ] [Nonempty κ] [Fintype ι] [Nonempty ι]
    (f : κ → ι) (hf : Function.Injective f) {η : ℝ} (hη : 0 ≤ η) (t : ι → ℝ)
    (hdom : ∀ i, (∀ k, f k ≠ i) → ∃ k, t i + η ≤ t (f k)) :
    regMax η t = regMax η (t ∘ f) := by
  classical
  have : Nonempty {i // i ∈ Set.range f} :=
    ⟨⟨f (Classical.arbitrary κ), Set.mem_range_self _⟩⟩
  rw [regMax_subtype (fun i => i ∈ Set.range f) hη t ?_]
  · convert (regMax_comp_equiv (Equiv.ofInjective f hf) η
      (fun k : {i // i ∈ Set.range f} => t k)).symm using 2
    funext k
    simp
  · intro i hi
    obtain ⟨k, hk⟩ := hdom i fun k hk => hi ⟨k, hk⟩
    exact ⟨f k, Set.mem_range_self _, hk⟩

end

end GroundTheory.Heights₂.Heights.Regular
