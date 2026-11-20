import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.StokesSimplices.SubSlice

open Function MeasureTheory

noncomputable section

namespace PositivityTheory.KB.StokesSlices

namespace Hyp

/- English proof (translation)
Establish `: Δ m = (⋂ j, {t : Fin m → ℝ | 0 ≤ t j}) ∩ {t | ∑ j, t j ≤ 1}` using `by ext t; simp [Δ]`. Rewrite using `[this]`. Conclude with `(isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)).inter (isClosed_le (continuous_finsetSum _ fun j _ => continuous_apply j) continuous_const)`.
-/
lemma isClosed_Δ (m : ℕ) : IsClosed (Δ m) := by
  have : Δ m = (⋂ j, {t : Fin m → ℝ | 0 ≤ t j}) ∩ {t | ∑ j, t j ≤ 1} := by ext t; simp [Δ]
  rw [this]
  exact (isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)).inter
    (isClosed_le (continuous_finsetSum _ fun j _ => continuous_apply j) continuous_const)

/- English proof (translation)
The claim follows from `(isClosed_Δ m).measurableSet`.
-/
lemma measurableSet_Δ (m : ℕ) : MeasurableSet (Δ m) := (isClosed_Δ m).measurableSet

variable {n : ℕ}

/- English proof (translation)
Establish `h' : (j : ℕ) ≠ i` using `fun e => h (Fin.ext e)`. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]`. Apply the tactic sequence `split_ifs <;> simp_all <;> omega`.
-/
lemma succAbove_cs_eq (i j : Fin (n + 1)) (h : j ≠ i) : i.castSucc.succAbove j = i.succ.succAbove j := by
  have h' : (j : ℕ) ≠ i := fun e => h (Fin.ext e)
  apply Fin.ext
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> simp_all <;> omega

/- English proof (translation)
Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]`. Apply the tactic sequence `split_ifs <;> simp_all`.
-/
lemma succAbove_cs_self (i : Fin (n + 1)) : i.castSucc.succAbove i = i.succ := by
  apply Fin.ext
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> simp_all

/- English proof (translation)
Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]`. Apply the tactic sequence `split_ifs <;> simp_all`.
-/
lemma succAbove_s_self (i : Fin (n + 1)) : i.succ.succAbove i = i.castSucc := by
  apply Fin.ext
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> simp_all

def invC (i : Fin (n + 1)) (s : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ := update s i (1 - ∑ j, s j)

/- English proof (translation)
Rewrite using `[Fin.sum_univ_succAbove s i]`. Both sides reduce to the same expression.
-/
lemma sum_eq_removeNth (i : Fin (n + 1)) (s : Fin (n + 1) → ℝ) :
    ∑ j, s j = s i + ∑ j, i.removeNth s j := by
  rw [Fin.sum_univ_succAbove s i]; rfl

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `[invC, Fin.removeNth]`.
-/
lemma removeNth_invC (i : Fin (n + 1)) (s : Fin (n + 1) → ℝ) : i.removeNth (invC i s) = i.removeNth s := by
  funext j
  simp [invC, Fin.removeNth]

/- English proof (translation)
Rewrite using `[sum_eq_removeNth i (invC i s), removeNth_invC]`. Simplify using `only [invC, update_self]`. Rewrite using `[sum_eq_removeNth i s]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma sum_invC (i : Fin (n + 1)) (s : Fin (n + 1) → ℝ) : ∑ j, invC i s j = 1 - s i := by
  rw [sum_eq_removeNth i (invC i s), removeNth_invC]
  simp only [invC, update_self]
  rw [sum_eq_removeNth i s]
  ring

/- English proof (translation)
Rewrite using `[show invC i (invC i s) = update (invC i s) i (1 - ∑ j, invC i s j) from rfl, sum_invC]`. Simplify using `[invC]`.
-/
lemma invC_invC (i : Fin (n + 1)) (s : Fin (n + 1) → ℝ) : invC i (invC i s) = s := by
  rw [show invC i (invC i s) = update (invC i s) i (1 - ∑ j, invC i s j) from rfl, sum_invC]
  simp [invC]

/- English proof (translation)
Use `⟨fun j => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `[invC]`. Combine the linear relations using `[hs.2]`.

Simplify using `[invC, update_of_ne h, hs.1 j]`. Rewrite using `[sum_invC]`. Combine the linear relations using `[hs.1 i]`.
-/
lemma invC_mem (i : Fin (n + 1)) {s : Fin (n + 1) → ℝ} (hs : s ∈ Δ (n + 1)) : invC i s ∈ Δ (n + 1) := by
  refine ⟨fun j => ?_, ?_⟩
  · by_cases h : j = i
    · subst h; simp [invC]; linarith [hs.2]
    · simp [invC, update_of_ne h, hs.1 j]
  · rw [sum_invC]; linarith [hs.1 i]

/- English proof (translation)
Use extensionality with `s`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `invC_mem i h` as an intermediate fact. Rewrite `this` using `[invC_invC]`. Then use the resulting hypothesis.

Conclude with `invC_mem i`.
-/
lemma preimage_invC (i : Fin (n + 1)) : invC i ⁻¹' Δ (n + 1) = Δ (n + 1) := by
  ext s
  constructor
  · intro h
    have := invC_mem i h
    rwa [invC_invC] at this
  · exact invC_mem i

/- English proof (translation)
The claim follows from `continuous_id.update i (continuous_const.sub (continuous_finsetSum _ fun j _ => continuous_apply j))`.
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
Establish `hT : MeasurePreserving (fun p : (Fin n → ℝ) × ℝ => (p.1, 1 - ∑ j, p.1 j - p.2)) (volume.prod volume) (volume.prod volume)`. Use `(MeasurePreserving.id volume).skew_product (g := fun (r : Fin n → ℝ) (x : ℝ) => 1 - ∑ j, r j - x) ?_ ?_` and prove the remaining obligations. Conclude with `(Continuous.sub (continuous_const.sub (continuous_finsetSum _ fun j _ => (continuous_apply j).comp continuous_fst)) continuous_snd).measurable`. Conclude with `Filter.Eventually.of_forall fun r => (Measure.measurePreserving_sub_left volume _).map_eq`. Conclude with `(Measure.measurePreserving_swap.comp hT).comp Measure.measurePreserving_swap`.
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
Use `set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i`. Establish `he : MeasurePreserving e volume (volume.prod volume)` using `volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i`. Establish `hfun : invC i = e.symm ∘ (fun p : ℝ × (Fin n → ℝ) => (1 - ∑ j, p.2 j - p.1, p.2)) ∘ e`. Use function extensionality and compare the values at `s`. Apply `e.injective` to reduce the goal to its premises.

Establish `he_apply : ∀ s, e s = (s i, i.removeNth s)` using `fun s => rfl`. Rewrite using `[comp_apply, comp_apply, MeasurableEquiv.apply_symm_apply, he_apply, he_apply, removeNth_invC]`. Use `Prod.ext ?_ rfl` and prove the remaining obligations. Simplify using `only [invC, update_self]`. Rewrite using `[sum_eq_removeNth i s]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hfun]`. Conclude with `he.symm.comp (mp_reflect.comp he)`.
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
Rewrite using `[sum_invC, sub_sub_cancel]`. Use function extensionality and compare the values at `k`. Use `i.succ.succAboveCases ?_ (fun j => ?_) k` and prove the remaining obligations. Rewrite using `[Fin.insertNth_apply_same, ← succAbove_cs_self, Fin.insertNth_apply_succAbove]`. Simplify using `[invC]`.

Rewrite using `[Fin.insertNth_apply_succAbove]`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Rewrite using `[succAbove_s_self, Fin.insertNth_apply_same]`. Rewrite using `[← succAbove_cs_eq i j h, Fin.insertNth_apply_succAbove]`.

Simplify using `[invC, update_of_ne h]`.
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
Take `⟨n, rfl⟩ : ∃ n, m = n + 1` from `⟨m - 1, by have := i.pos; omega⟩`. Establish `h` using `(mp_invC i).setIntegral_preimage_emb (invCE i).measurableEmbedding (fun s => G (i.castSucc.insertNth (1 - ∑ j, s j) s)) (Δ (n + 1))`. Rewrite `h` using `[preimage_invC]`. Rewrite using `[← h]`. Use `setIntegral_congr_fun (measurableSet_Δ _) fun s _ => ?_` and prove the remaining obligations.

Conclude with `congrArg G (insertNth_succ_eq i s)`.
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
Introduce `m G i`. Proceed by induction on `i using Fin.induction with`. Consider the case `zero`. Use `congr 1`. Use function extensionality and compare the values at `s`.

Use `congr 1`. Conclude with `Fin.insertNth_zero' _ _`. Consider the case `succ i ih => rw [hyp_step, ih]`.
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
