import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapSubInOfCob2InStatement

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.CocLift

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ} {τ : Type}

/- English proof (translation)
The claim follows from `hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [hu, hv]`.
-/
theorem hasSubst_elim (u v : Fin d → MvPowerSeries τ R) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) : HasSubst (Sum.elim u v) :=
  hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [hu, hv]

/- English proof (translation)
The claim follows from `subst_smul (hasSubst_elim u v hu hv) r c`.
-/
theorem powerSeriesEvalTwoGroups_smul (c : MvPowerSeries (Fin d ⊕ Fin d) R) (r : R) (u v : Fin d → MvPowerSeries τ R)
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    at2 (r • c) u v = r • at2 c u v :=
  subst_smul (hasSubst_elim u v hu hv) r c

/- English proof (translation)
The claim follows from `constantCoeff_subst_eq_zero (hasSubst_elim u v hu hv) (fun s => by cases s <;> simp [hu, hv]) hc`.
-/
theorem constantCoeff_powerSeriesEvalTwoGroups_zero (c : MvPowerSeries (Fin d ⊕ Fin d) R) (u v : Fin d → MvPowerSeries τ R)
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    (hc : constantCoeff c = 0) : constantCoeff (at2 c u v) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_elim u v hu hv) (fun s => by cases s <;> simp [hu, hv]) hc

/- English proof (translation)
Unfold `at2`. Rewrite using `[map_subst (hasSubst_elim u v hu hv)]`. Use `congr 1`. Use function extensionality and compare the values at `s`. Apply the tactic sequence `cases s <;> rfl`.
-/
theorem mvPowerSeriesMap_evalTwoGroups (h : R →+* S) (c : MvPowerSeries (Fin d ⊕ Fin d) R) (u v : Fin d → MvPowerSeries τ R)
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    map h (at2 c u v) = at2 (map h c) (fun i => map h (u i)) (fun i => map h (v i)) := by
  unfold at2
  rw [map_subst (hasSubst_elim u v hu hv)]
  congr 1
  funext s
  cases s <;> rfl

/- English proof (translation)
Introduce `i` and use `constantCoeff_X _`.
-/
theorem constantCoeff_threeGroupsFirstVariables_eq_zero : ∀ i, constantCoeff (x1 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
/- English proof (translation)
Introduce `i` and use `constantCoeff_X _`.
-/
theorem constantCoeff_threeGroupsSecondVariables_eq_zero : ∀ i, constantCoeff (x2 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
/- English proof (translation)
Introduce `i` and use `constantCoeff_X _`.
-/
theorem constantCoeff_threeGroupsThirdVariables_eq_zero : ∀ i, constantCoeff (x3 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _

/- English proof (translation)
Introduce `i` and use `constantCoeff_powerSeriesEvalTwoGroups_zero _ u v hu hv (hμ i)`.
-/
theorem cOp (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (u v : Fin d → MvPowerSeries τ R) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) : ∀ i, constantCoeff (op μ u v i) = 0 :=
  fun i => constantCoeff_powerSeriesEvalTwoGroups_zero _ u v hu hv (hμ i)

/- English proof (translation)
Unfold `cob2`. Rewrite using `[powerSeriesEvalTwoGroups_smul _ _ _ _ constantCoeff_threeGroupsSecondVariables_eq_zero constantCoeff_threeGroupsThirdVariables_eq_zero, powerSeriesEvalTwoGroups_smul _ _ _ _ (cOp μ hμ _ _ constantCoeff_threeGroupsFirstVariables_eq_zero constantCoeff_threeGroupsSecondVariables_eq …`. Simplify using `only [smul_sub, smul_add]`.
-/
theorem formalGroupLawCoboundaryTwo_smul (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (r : R) (c : MvPowerSeries (Fin d ⊕ Fin d) R) : cob2 μ (r • c) = r • cob2 μ c := by
  unfold cob2
  rw [powerSeriesEvalTwoGroups_smul _ _ _ _ constantCoeff_threeGroupsSecondVariables_eq_zero constantCoeff_threeGroupsThirdVariables_eq_zero, powerSeriesEvalTwoGroups_smul _ _ _ _ (cOp μ hμ _ _ constantCoeff_threeGroupsFirstVariables_eq_zero constantCoeff_threeGroupsSecondVariables_eq_zero) constantCoeff_threeGroupsThirdVariables_eq_zero,
    powerSeriesEvalTwoGroups_smul _ _ _ _ constantCoeff_threeGroupsFirstVariables_eq_zero (cOp μ hμ _ _ constantCoeff_threeGroupsSecondVariables_eq_zero constantCoeff_threeGroupsThirdVariables_eq_zero), powerSeriesEvalTwoGroups_smul _ _ _ _ constantCoeff_threeGroupsFirstVariables_eq_zero constantCoeff_threeGroupsSecondVariables_eq_zero]
  simp only [smul_sub, smul_add]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[x1]`.
-/
theorem map_threeGroupsFirstVariables (h : R →+* S) : (fun i => map h (x1 (R := R) (d := d) i)) = x1 := by
  funext i; simp [x1]
/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[x2]`.
-/
theorem map_threeGroupsSecondVariables (h : R →+* S) : (fun i => map h (x2 (R := R) (d := d) i)) = x2 := by
  funext i; simp [x2]
/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[x3]`.
-/
theorem map_threeGroupsThirdVariables (h : R →+* S) : (fun i => map h (x3 (R := R) (d := d) i)) = x3 := by
  funext i; simp [x3]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Conclude with `mvPowerSeriesMap_evalTwoGroups h _ u v hu hv`.
-/
theorem map_op (h : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (u v : Fin d → MvPowerSeries τ R) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    (fun i => map h (op μ u v i)) = op (fun i => map h (μ i)) (fun i => map h (u i)) (fun i => map h (v i)) := by
  funext i
  exact mvPowerSeriesMap_evalTwoGroups h _ u v hu hv

/- English proof (translation)
Unfold `cob2`. Simplify using `only [map_sub, map_add]`. Rewrite using `[mvPowerSeriesMap_evalTwoGroups h _ _ _ constantCoeff_threeGroupsSecondVariables_eq_zero constantCoeff_threeGroupsThirdVariables_eq_zero, mvPowerSeriesMap_evalTwoGroups h _ _ _ (cOp μ hμ _ _ constantCoeff_threeGroupsFirstVariables_eq_zero constantCoeff_threeGroupsSecondVariables_ …`.
-/
theorem map_formalGroupLawCoboundaryTwo (h : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    map h (cob2 μ c) = cob2 (fun i => map h (μ i)) (map h c) := by
  unfold cob2
  simp only [map_sub, map_add]
  rw [mvPowerSeriesMap_evalTwoGroups h _ _ _ constantCoeff_threeGroupsSecondVariables_eq_zero constantCoeff_threeGroupsThirdVariables_eq_zero, mvPowerSeriesMap_evalTwoGroups h _ _ _ (cOp μ hμ _ _ constantCoeff_threeGroupsFirstVariables_eq_zero constantCoeff_threeGroupsSecondVariables_eq_zero) constantCoeff_threeGroupsThirdVariables_eq_zero,
    mvPowerSeriesMap_evalTwoGroups h _ _ _ constantCoeff_threeGroupsFirstVariables_eq_zero (cOp μ hμ _ _ constantCoeff_threeGroupsSecondVariables_eq_zero constantCoeff_threeGroupsThirdVariables_eq_zero), mvPowerSeriesMap_evalTwoGroups h _ _ _ constantCoeff_threeGroupsFirstVariables_eq_zero constantCoeff_threeGroupsSecondVariables_eq_zero,
    map_op h μ _ _ constantCoeff_threeGroupsFirstVariables_eq_zero constantCoeff_threeGroupsSecondVariables_eq_zero, map_op h μ _ _ constantCoeff_threeGroupsSecondVariables_eq_zero constantCoeff_threeGroupsThirdVariables_eq_zero, map_threeGroupsFirstVariables, map_threeGroupsSecondVariables, map_threeGroupsThirdVariables]

/- English proof (translation)
Introduce `i` and use `constantCoeff_X _`.
-/
theorem cYX : ∀ i : Fin d, constantCoeff (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R) = 0 :=
  fun i => constantCoeff_X _
/- English proof (translation)
Introduce `i` and use `constantCoeff_X _`.
-/
theorem cXX : ∀ i : Fin d, constantCoeff (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R) = 0 :=
  fun i => constantCoeff_X _

/- English proof (translation)
The claim follows from `powerSeriesEvalTwoGroups_smul c r _ _ cYX cXX`.
-/
theorem swap_smul (r : R) (c : MvPowerSeries (Fin d ⊕ Fin d) R) : swap (r • c) = r • swap c :=
  powerSeriesEvalTwoGroups_smul c r _ _ cYX cXX

/- English proof (translation)
Unfold `swap`. Rewrite using `[mvPowerSeriesMap_evalTwoGroups h _ _ _ cYX cXX]`. Simplify using the standard rewrite rules.
-/
theorem map_swap (h : R →+* S) (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    map h (swap c) = swap (map h c) := by
  unfold swap
  rw [mvPowerSeriesMap_evalTwoGroups h _ _ _ cYX cXX]
  simp

end GlobalTheory.CocLift

namespace GlobalTheory.CocLift

/- English proof (translation)
Introduce `p _ O C _ _ _ hF d μ hμ a ha c hc0 hcob hsw`. Use `set A : C := algebraMap O C a with hA`. Establish `hAu : IsUnit A`. Take `⟨b, hb⟩` from `ha`. Establish `: (p : C) = A * algebraMap O C b` using `by rw [hA, ← map_mul, ← hb, map_natCast]`.

Conclude with `isUnit_of_mul_isUnit_left (this ▸ hF.unit_p)`. Take `⟨u, hu⟩` from `hAu`. Use `set ai : C := ↑u⁻¹ with hai`. Establish `hAai : A * ai = 1` using `by rw [hai, ← hu, Units.mul_inv]`. Establish `hμc : ∀ i, constantCoeff (up C μ i) = 0` using `fun i => by`.

Simplify using `[up, hμ.const i]`. Use `set c' : MvPowerSeries (Fin d ⊕ Fin d) C := ai • map (algebraMap O C) c with hc'`. Establish `hlift : IsLift (RingHom.id O) μ`. Use `⟨hμ.const, hμ.unit, hμ.comm, ?_⟩` and prove the remaining obligations. Establish `: (fun i => map (RingHom.id O) (μ i)) = μ`.

Use function extensionality and compare the values at `i`. Use extensionality with `α`. Simplify using `[coeff_map]`. Rewrite using `[this]`. Conclude with `hμ`.

Establish `hc'0 : constantCoeff c' = 0`. Simplify using `[hc', hc0]`. Establish `hden : ∀ α, ∃ k : ℕ, ∃ b ∈ (⊤ : Ideal O), (p : C) ^ k * coeff α c' = algebraMap O C b`. Introduce `α`. Take `⟨k, b, hb⟩` from `hF.denom (coeff α c')`.

Conclude with `⟨k, b, Submodule.mem_top, hb⟩`. Establish `hcob' : In (⊤ : Ideal O) (cob2 (up C μ) c')`. Introduce `α`. Take `⟨b, hb⟩` from `hcob α`. Use `⟨b, Submodule.mem_top, ?_⟩` and prove the remaining obligations.

Establish `h1 : cob2 (up C μ) c' = ai • map (algebraMap O C) (cob2 μ c)`. Rewrite using `[hc', formalGroupLawCoboundaryTwo_smul _ hμc, map_formalGroupLawCoboundaryTwo _ _ hμ.const]`. Both sides reduce to the same expression. Rewrite using `[h1, coeff_smul, coeff_map, hb, map_mul, ← mul_assoc, mul_comm ai, hAai, one_mul]`. Establish `hsw' : In (⊤ : Ideal O) (swap c' - c')`.

Introduce `α`. Take `⟨b, hb⟩` from `hsw α`. Use `⟨b, Submodule.mem_top, ?_⟩` and prove the remaining obligations. Establish `h1 : swap c' - c' = ai • map (algebraMap O C) (swap c - c)`. Rewrite using `[hc', swap_smul, map_sub, map_swap, smul_sub]`.

Rewrite using `[h1, coeff_smul, coeff_map, hb, map_mul, ← mul_assoc, mul_comm ai, hAai, one_mul]`. Take `⟨g', hg0, hglin, -, hgIn⟩` from `GlobalTheory.T.swap_sub_in_of_cob2_in p O O C (RingHom.id O) hF d μ hlift ⊤ ⊤ le_rfl c' (Or.inl hμ) hc'0 hden hcob' hsw'`. Establish `hcob1 : cob1 (up C μ) (A • g') = A • cob1 (up C μ) g'` using `formalCoboundary_smul hμc A g'`. Establish `hlin : lin (A • g') = 0`. Use function extensionality and compare the values at `i`.

Use `congrFun hglin i` as an intermediate fact. Simplify using `only [lin, coeff_smul, Pi.zero_apply] at this ⊢`. Rewrite using `[this, mul_zero]`. Use `⟨A • g', ⟨?_, ?_, ?_⟩, hlin, ?_⟩` and prove the remaining obligations. Simplify using `[hg0]`.

Introduce `i; exact ⟨0, Submodule.mem_top, by rw [hlin, map_zero]; rfl⟩`. Introduce `α`. Take `⟨b, -, hb⟩` from `hgIn α`. Use `⟨coeff α c - a * b, Submodule.mem_top, ?_⟩` and prove the remaining obligations. Establish `e : coeff α (cob1 (up C μ) g') = coeff α c' - algebraMap O C b`.

Rewrite using `[← hb, map_sub]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hcob1, coeff_smul, e, hc', coeff_smul, coeff_map, map_sub, map_mul]`. Take the linear combination `(algebraMap O C (coeff α c)) * hAai`. Introduce `α`.

Take `⟨b, -, hb⟩` from `hgIn α`. Use `⟨a * (-b), Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a), ?_⟩` and prove the remaining obligations. Establish `e : coeff α (cob1 (up C μ) g') = coeff α c' - algebraMap O C b`. Rewrite using `[← hb, map_sub]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[map_sub, hcob1, coeff_smul, e, hc', coeff_smul, coeff_map, map_mul, map_neg]`. Take the linear combination `(algebraMap O C (coeff α c)) * hAai`.
-/
theorem cocycle_lift : ∀ (p : ℕ) [Fact p.Prime] (O C : Type) [CommRing O] [CommRing C] [Algebra O C], IsFrame p C (RingHom.id O) → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ (a : O), a ∣ p → ∀ c : MvPowerSeries (Fin d ⊕ Fin d) O, constantCoeff c = 0 → (∀ α, a ∣ coeff α (cob2 μ c)) → (∀ α, a ∣ coeff α (swap c - c)) → ∃ g : MvPowerSeries (Fin d) C, QL μ ⊤ g ∧ lin g = 0 ∧ In (Ideal.span {a}) (cob1 (up C μ) g - map (algebraMap O C) c) := by
  intro p _ O C _ _ _ hF d μ hμ a ha c hc0 hcob hsw
  set A : C := algebraMap O C a with hA
  have hAu : IsUnit A := by
    obtain ⟨b, hb⟩ := ha
    have : (p : C) = A * algebraMap O C b := by rw [hA, ← map_mul, ← hb, map_natCast]
    exact isUnit_of_mul_isUnit_left (this ▸ hF.unit_p)
  obtain ⟨u, hu⟩ := hAu
  set ai : C := ↑u⁻¹ with hai
  have hAai : A * ai = 1 := by rw [hai, ← hu, Units.mul_inv]
  have hμc : ∀ i, constantCoeff (up C μ i) = 0 := fun i => by
    simp [up, hμ.const i]
  set c' : MvPowerSeries (Fin d ⊕ Fin d) C := ai • map (algebraMap O C) c with hc'
  have hlift : IsLift (RingHom.id O) μ := by
    refine ⟨hμ.const, hμ.unit, hμ.comm, ?_⟩
    have : (fun i => map (RingHom.id O) (μ i)) = μ := by
      funext i; ext α; simp [coeff_map]
    rw [this]; exact hμ
  have hc'0 : constantCoeff c' = 0 := by
    simp [hc', hc0]
  have hden : ∀ α, ∃ k : ℕ, ∃ b ∈ (⊤ : Ideal O), (p : C) ^ k * coeff α c' = algebraMap O C b := by
    intro α
    obtain ⟨k, b, hb⟩ := hF.denom (coeff α c')
    exact ⟨k, b, Submodule.mem_top, hb⟩
  have hcob' : In (⊤ : Ideal O) (cob2 (up C μ) c') := by
    intro α
    obtain ⟨b, hb⟩ := hcob α
    refine ⟨b, Submodule.mem_top, ?_⟩
    have h1 : cob2 (up C μ) c' = ai • map (algebraMap O C) (cob2 μ c) := by
      rw [hc', formalGroupLawCoboundaryTwo_smul _ hμc, map_formalGroupLawCoboundaryTwo _ _ hμ.const]; rfl
    rw [h1, coeff_smul, coeff_map, hb, map_mul, ← mul_assoc, mul_comm ai, hAai, one_mul]
  have hsw' : In (⊤ : Ideal O) (swap c' - c') := by
    intro α
    obtain ⟨b, hb⟩ := hsw α
    refine ⟨b, Submodule.mem_top, ?_⟩
    have h1 : swap c' - c' = ai • map (algebraMap O C) (swap c - c) := by
      rw [hc', swap_smul, map_sub, map_swap, smul_sub]
    rw [h1, coeff_smul, coeff_map, hb, map_mul, ← mul_assoc, mul_comm ai, hAai, one_mul]
  obtain ⟨g', hg0, hglin, -, hgIn⟩ := GlobalTheory.T.swap_sub_in_of_cob2_in p O O C (RingHom.id O) hF d μ hlift ⊤ ⊤ le_rfl c'
    (Or.inl hμ) hc'0 hden hcob' hsw'
  have hcob1 : cob1 (up C μ) (A • g') = A • cob1 (up C μ) g' := formalCoboundary_smul hμc A g'
  have hlin : lin (A • g') = 0 := by
    funext i
    have := congrFun hglin i
    simp only [lin, coeff_smul, Pi.zero_apply] at this ⊢
    rw [this, mul_zero]
  refine ⟨A • g', ⟨?_, ?_, ?_⟩, hlin, ?_⟩
  · simp [hg0]
  · intro i; exact ⟨0, Submodule.mem_top, by rw [hlin, map_zero]; rfl⟩
  · intro α
    obtain ⟨b, -, hb⟩ := hgIn α
    refine ⟨coeff α c - a * b, Submodule.mem_top, ?_⟩
    have e : coeff α (cob1 (up C μ) g') = coeff α c' - algebraMap O C b := by
      rw [← hb, map_sub]; ring
    rw [hcob1, coeff_smul, e, hc', coeff_smul, coeff_map, map_sub, map_mul]
    linear_combination (algebraMap O C (coeff α c)) * hAai
  · intro α
    obtain ⟨b, -, hb⟩ := hgIn α
    refine ⟨a * (-b), Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a), ?_⟩
    have e : coeff α (cob1 (up C μ) g') = coeff α c' - algebraMap O C b := by
      rw [← hb, map_sub]; ring
    rw [map_sub, hcob1, coeff_smul, e, hc', coeff_smul, coeff_map, map_mul, map_neg]
    linear_combination (algebraMap O C (coeff α c)) * hAai

end GlobalTheory.CocLift
