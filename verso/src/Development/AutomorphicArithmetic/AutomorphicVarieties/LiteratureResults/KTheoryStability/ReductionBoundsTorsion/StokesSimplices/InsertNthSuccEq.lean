import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.StokesSimplices.SubSlice

open Function MeasureTheory

noncomputable section

namespace PositivityTheory.KB.StokesSlices

namespace Hyp

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma isClosed_Δ (m : ℕ) : IsClosed (Δ m) := by
  have : Δ m = (⋂ j, {t : Fin m → ℝ | 0 ≤ t j}) ∩ {t | ∑ j, t j ≤ 1} := by ext t; simp [Δ]
  rw [this]
  exact (isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)).inter
    (isClosed_le (continuous_finsetSum _ fun j _ => continuous_apply j) continuous_const)

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma measurableSet_Δ (m : ℕ) : MeasurableSet (Δ m) := (isClosed_Δ m).measurableSet

variable {n : ℕ}

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
lemma succAbove_cs_eq (i j : Fin (n + 1)) (h : j ≠ i) : i.castSucc.succAbove j = i.succ.succAbove j := by
  have h' : (j : ℕ) ≠ i := fun e => h (Fin.ext e)
  apply Fin.ext
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> simp_all <;> omega

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
lemma succAbove_cs_self (i : Fin (n + 1)) : i.castSucc.succAbove i = i.succ := by
  apply Fin.ext
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> simp_all

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
lemma succAbove_s_self (i : Fin (n + 1)) : i.succ.succAbove i = i.castSucc := by
  apply Fin.ext
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> simp_all

def invC (i : Fin (n + 1)) (s : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ := update s i (1 - ∑ j, s j)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
lemma sum_eq_removeNth (i : Fin (n + 1)) (s : Fin (n + 1) → ℝ) :
    ∑ j, s j = s i + ∑ j, i.removeNth s j := by
  rw [Fin.sum_univ_succAbove s i]; rfl

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
lemma removeNth_invC (i : Fin (n + 1)) (s : Fin (n + 1) → ℝ) : i.removeNth (invC i s) = i.removeNth s := by
  funext j
  simp [invC, Fin.removeNth]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
lemma sum_invC (i : Fin (n + 1)) (s : Fin (n + 1) → ℝ) : ∑ j, invC i s j = 1 - s i := by
  rw [sum_eq_removeNth i (invC i s), removeNth_invC]
  simp only [invC, update_self]
  rw [sum_eq_removeNth i s]
  ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
lemma invC_invC (i : Fin (n + 1)) (s : Fin (n + 1) → ℝ) : invC i (invC i s) = s := by
  rw [show invC i (invC i s) = update (invC i s) i (1 - ∑ j, invC i s j) from rfl, sum_invC]
  simp [invC]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma invC_mem (i : Fin (n + 1)) {s : Fin (n + 1) → ℝ} (hs : s ∈ Δ (n + 1)) : invC i s ∈ Δ (n + 1) := by
  refine ⟨fun j => ?_, ?_⟩
  · by_cases h : j = i
    · subst h; simp [invC]; linarith [hs.2]
    · simp [invC, update_of_ne h, hs.1 j]
  · rw [sum_invC]; linarith [hs.1 i]

/- English proof (translation)
By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

A detailed English derivation is pending.
-/
lemma preimage_invC (i : Fin (n + 1)) : invC i ⁻¹' Δ (n + 1) = Δ (n + 1) := by
  ext s
  constructor
  · intro h
    have := invC_mem i h
    rwa [invC_invC] at this
  · exact invC_mem i

/- English proof (translation)
A detailed English derivation is pending.
-/
lemma continuous_invC (i : Fin (n + 1)) : Continuous (invC i) :=
  continuous_id.update i (continuous_const.sub (continuous_finsetSum _ fun j _ => continuous_apply j))

def invCE (i : Fin (n + 1)) : (Fin (n + 1) → ℝ) ≃ᵐ (Fin (n + 1) → ℝ) where
  toFun := invC i
  invFun := invC i
  left_inv s := invC_invC i s
  right_inv s := invC_invC i s
  measurable_toFun := (continuous_invC i).measurable
  measurable_invFun := (continuous_invC i).measurable

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
lemma mp_reflect : MeasurePreserving (fun p : ℝ × (Fin n → ℝ) => (1 - ∑ j, p.2 j - p.1, p.2))
    (volume.prod volume) (volume.prod volume) := by
  have hT : MeasurePreserving (fun p : (Fin n → ℝ) × ℝ => (p.1, 1 - ∑ j, p.1 j - p.2))
      (volume.prod volume) (volume.prod volume) := by
    refine (MeasurePreserving.id volume).skew_product (g := fun (r : Fin n → ℝ) (x : ℝ) => 1 - ∑ j, r j - x) ?_ ?_
    · exact (Continuous.sub (continuous_const.sub (continuous_finsetSum _ fun j _ =>
        (continuous_apply j).comp continuous_fst)) continuous_snd).measurable
    · exact Filter.Eventually.of_forall fun r => (Measure.measurePreserving_sub_left volume _).map_eq
  exact (Measure.measurePreserving_swap.comp hT).comp Measure.measurePreserving_swap

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
lemma mp_invC (i : Fin (n + 1)) : MeasurePreserving (invC i) volume volume := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have he : MeasurePreserving e volume (volume.prod volume) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hfun : invC i = e.symm ∘ (fun p : ℝ × (Fin n → ℝ) => (1 - ∑ j, p.2 j - p.1, p.2)) ∘ e := by
    funext s
    apply e.injective
    have he_apply : ∀ s, e s = (s i, i.removeNth s) := fun s => rfl
    rw [comp_apply, comp_apply, MeasurableEquiv.apply_symm_apply, he_apply, he_apply, removeNth_invC]
    refine Prod.ext ?_ rfl
    simp only [invC, update_self]
    rw [sum_eq_removeNth i s]
    ring
  rw [hfun]
  exact he.symm.comp (mp_reflect.comp he)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules.
-/
lemma insertNth_succ_eq (i : Fin (n + 1)) (s : Fin (n + 1) → ℝ) :
    Fin.insertNth (α := fun _ => ℝ) i.succ (1 - ∑ j, s j) s =
      Fin.insertNth (α := fun _ => ℝ) i.castSucc (1 - ∑ j, invC i s j) (invC i s) := by
  rw [sum_invC, sub_sub_cancel]
  funext k
  refine i.succ.succAboveCases ?_ (fun j => ?_) k
  · rw [Fin.insertNth_apply_same, ← succAbove_cs_self, Fin.insertNth_apply_succAbove]
    simp [invC]
  · rw [Fin.insertNth_apply_succAbove]
    by_cases h : j = i
    · subst h
      rw [succAbove_s_self, Fin.insertNth_apply_same]
    · rw [← succAbove_cs_eq i j h, Fin.insertNth_apply_succAbove]
      simp [invC, update_of_ne h]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

A detailed English derivation is pending.
-/
lemma hyp_step (m : ℕ) (G : (Fin (m + 1) → ℝ) → ℝ) (i : Fin m) :
    ∫ s in Δ m, G (i.succ.insertNth (1 - ∑ j, s j) s) =
      ∫ s in Δ m, G (i.castSucc.insertNth (1 - ∑ j, s j) s) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by have := i.pos; omega⟩
  have h := (mp_invC i).setIntegral_preimage_emb (invCE i).measurableEmbedding
    (fun s => G (i.castSucc.insertNth (1 - ∑ j, s j) s)) (Δ (n + 1))
  rw [preimage_invC] at h
  rw [← h]
  refine setIntegral_congr_fun (measurableSet_Δ _) fun s _ => ?_
  exact congrArg G (insertNth_succ_eq i s)

end Hyp

open Hyp in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument.

Reduce the equality to equality of the corresponding arguments. Treat this case separately. A detailed English derivation is pending.
-/
theorem subHyp : SubHyp := by
  intro m G i
  induction i using Fin.induction with
  | zero =>
    congr 1
    funext s
    congr 1
    exact Fin.insertNth_zero' _ _
  | succ i ih => rw [hyp_step, ih]

end PositivityTheory.KB.StokesSlices
