import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.UnitaryHaarColumns

noncomputable section

open Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.StandardBasisEmbedding

open Formalism.QuantumDeterminants

variable {k r : ℕ}

/- English proof (translation)
Use `congrFun h i` as an intermediate fact. Simplify `this` using `[bvec, Matrix.mulVec, dotProduct, Pi.single_apply]`.
-/
theorem col_of_fix {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} {c : Fin (2 * r + k + 1)}
    (h : s *ᵥ bvec c = bvec c) (i : Fin (2 * r + k + 1)) : s i c = if i = c then 1 else 0 := by
  have := congrFun h i
  simpa [bvec, Matrix.mulVec, dotProduct, Pi.single_apply] using this

/- English proof (translation)
Take `⟨-, hf, hz⟩` from `hs`. Unfold `bl at hc`. Break down `lt_trichotomy c.val (r + k) with h1 | h1 | h1` into its components or cases. Establish `hcr : c.val < r` using `by omega`. Establish `: c = eI k r ⟨c.val, hcr⟩` using `by ext; simp [eI]`.

Rewrite using `[this]`. Conclude with `col_of_fix (hf _).1 i`. Establish `: c = wI k r (Fin.last k)` using `by ext; simp [wI, h1]`. Rewrite using `[this]`. Conclude with `col_of_fix hz i`.

Establish `hc2` using `c.isLt`. Establish `: c = esI k r ⟨2 * r + k - c.val, by omega⟩` using `by ext; simp [esI]; omega`. Rewrite using `[this]`. Conclude with `col_of_fix (hf _).2 i`.
-/
theorem col_std {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hs : s ∈ UWset k r (z0 k r))
    {c : Fin (2 * r + k + 1)} (hc : ¬ bl k r c) (i : Fin (2 * r + k + 1)) :
    s i c = if i = c then 1 else 0 := by
  obtain ⟨-, hf, hz⟩ := hs
  unfold bl at hc
  rcases lt_trichotomy c.val (r + k) with h1 | h1 | h1
  · have hcr : c.val < r := by omega
    have : c = eI k r ⟨c.val, hcr⟩ := by ext; simp [eI]
    rw [this]; exact col_of_fix (hf _).1 i
  · have : c = wI k r (Fin.last k) := by ext; simp [wI, h1]
    rw [this]; exact col_of_fix hz i
  · have hc2 := c.isLt
    have : c = esI k r ⟨2 * r + k - c.val, by omega⟩ := by ext; simp [esI]; omega
    rw [this]; exact col_of_fix (hf _).2 i

/- English proof (translation)
Establish `hU : sᴴ * Hpk k r * s = Hpk k r` using `hs.1`. Establish `e` using `congrFun (congrFun hU c) j`. Rewrite using `[← e, Matrix.mul_apply]`. Use `Finset.sum_congr rfl (fun b _ => ?_)` and prove the remaining obligations. Use `congr 1`.

Rewrite using `[Matrix.mul_apply]`. Apply the tactic sequence `have hst : ∀ x : Fin (2 * r + k + 1), star (if x = c then (1 : ℂ) else 0) = if x = c then 1 else 0 := fun x => by split_ifs <;> simp`. Simplify using `only [Matrix.conjTranspose_apply, col_std hs hc, hst, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.
-/
theorem key {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hs : s ∈ UWset k r (z0 k r))
    {c : Fin (2 * r + k + 1)} (hc : ¬ bl k r c) (j : Fin (2 * r + k + 1)) :
    Hpk k r c j = ∑ b, Hpk k r c b * s b j := by
  have hU : sᴴ * Hpk k r * s = Hpk k r := hs.1
  have e := congrFun (congrFun hU c) j
  rw [← e, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  congr 1
  rw [Matrix.mul_apply]
  have hst : ∀ x : Fin (2 * r + k + 1), star (if x = c then (1 : ℂ) else 0) = if x = c then 1 else 0 :=
    fun x => by split_ifs <;> simp
  simp only [Matrix.conjTranspose_apply, col_std hs hc, hst, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/- English proof (translation)
Establish `hi'` using `hi`. Unfold `bl at hi'`. Establish `hi2` using `i.isLt`. Break down `lt_trichotomy i.val (r + k) with h1 | h1 | h1` into its components or cases. Establish `hir : i.val < r` using `by omega set c : Fin (2 * r + k + 1) := ⟨2 * r + k - i.val, by omega⟩ with hcdef`.

Establish `hc : ¬ bl k r c` using `by simp only [bl, hcdef]; omega`. Establish `e` using `key hs hc j`. Rewrite `e` using `[H_blcol hj, if_neg (by rintro rfl; exact hc hj)]`. Rewrite `e` using `[Finset.sum_eq_single i]`. Rewrite `e` using `[H_hi (by simp only [hcdef]; omega), if_pos (by simp only [hcdef]; omega), one_mul]`.

Conclude with `e.symm`. Introduce `b _ hb`. Rewrite using `[H_hi (by simp only [hcdef]; omega), if_neg, zero_mul]`. Introduce `h`. Apply `hb` to reduce the goal to its premises.

Use `ext`. Simplify using `only [hcdef] at h`. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules. Establish `hc : ¬ bl k r i` using `hi`.

Establish `e` using `key hs hc j`. Rewrite `e` using `[H_blcol hj, if_neg (by rintro rfl; exact hc hj)]`. Rewrite `e` using `[Finset.sum_eq_single i]`. Rewrite `e` using `[H_mid h1, if_pos rfl]`. Establish `: s i j = -(-1 * s i j)` using `by ring`.

Rewrite using `[this, ← e, neg_zero]`. Introduce `b _ hb`. Rewrite using `[H_mid h1, if_neg (Ne.symm hb), zero_mul]`. Simplify using the standard rewrite rules. Use `set c : Fin (2 * r + k + 1) := ⟨2 * r + k - i.val, by omega⟩ with hcdef`.

Establish `hc : ¬ bl k r c` using `by simp only [bl, hcdef]; omega`. Establish `e` using `key hs hc j`. Rewrite `e` using `[H_blcol hj, if_neg (by rintro rfl; exact hc hj)]`. Rewrite `e` using `[Finset.sum_eq_single i]`. Rewrite `e` using `[H_lo (by simp only [hcdef]; omega), if_pos (by simp only [hcdef]; omega), one_mul]`.

Conclude with `e.symm`. Introduce `b _ hb`. Rewrite using `[H_lo (by simp only [hcdef]; omega), if_neg, zero_mul]`. Introduce `h`. Apply `hb` to reduce the goal to its premises.

Use `ext`. Simplify using `only [hcdef] at h`. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules.
-/
theorem row_zero {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hs : s ∈ UWset k r (z0 k r))
    {i j : Fin (2 * r + k + 1)} (hi : ¬ bl k r i) (hj : bl k r j) : s i j = 0 := by
  have hi' := hi
  unfold bl at hi'
  have hi2 := i.isLt

  rcases lt_trichotomy i.val (r + k) with h1 | h1 | h1
  · have hir : i.val < r := by omega
    set c : Fin (2 * r + k + 1) := ⟨2 * r + k - i.val, by omega⟩ with hcdef
    have hc : ¬ bl k r c := by simp only [bl, hcdef]; omega
    have e := key hs hc j
    rw [H_blcol hj, if_neg (by rintro rfl; exact hc hj)] at e
    rw [Finset.sum_eq_single i] at e
    · rw [H_hi (by simp only [hcdef]; omega), if_pos (by simp only [hcdef]; omega), one_mul] at e
      exact e.symm
    · intro b _ hb
      rw [H_hi (by simp only [hcdef]; omega), if_neg, zero_mul]
      intro h; apply hb; ext; simp only [hcdef] at h; omega
    · simp
  · have hc : ¬ bl k r i := hi
    have e := key hs hc j
    rw [H_blcol hj, if_neg (by rintro rfl; exact hc hj)] at e
    rw [Finset.sum_eq_single i] at e
    · rw [H_mid h1, if_pos rfl] at e
      have : s i j = -(-1 * s i j) := by ring
      rw [this, ← e, neg_zero]
    · intro b _ hb
      rw [H_mid h1, if_neg (Ne.symm hb), zero_mul]
    · simp
  · set c : Fin (2 * r + k + 1) := ⟨2 * r + k - i.val, by omega⟩ with hcdef
    have hc : ¬ bl k r c := by simp only [bl, hcdef]; omega
    have e := key hs hc j
    rw [H_blcol hj, if_neg (by rintro rfl; exact hc hj)] at e
    rw [Finset.sum_eq_single i] at e
    · rw [H_lo (by simp only [hcdef]; omega), if_pos (by simp only [hcdef]; omega), one_mul] at e
      exact e.symm
    · intro b _ hb
      rw [H_lo (by simp only [hcdef]; omega), if_neg, zero_mul]
      intro h; apply hb; ext; simp only [hcdef] at h; omega
    · simp

def blk (s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  fun q q' => s (eB k r q) (eB k r q')

/- English proof (translation)
Rewrite using `[Matrix.mem_unitaryGroup_iff']`. Use extensionality with `q q'`. Establish `hU : sᴴ * Hpk k r * s = Hpk k r` using `hs.1`. Establish `e` using `congrFun (congrFun hU (eB k r q)) (eB k r q')`. Rewrite `e` using `[H_blrow (bl_eB q), Matrix.mul_apply]`.

Rewrite `e` using `[sumB _ (fun p hp => by rw [row_zero hs hp (bl_eB q'), mul_zero])]`. Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, H_blcol (bl_eB _), mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at e`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`. Simplify using `only [Matrix.star_apply, blk]`. Rewrite using `[e]`.

Simplify using `[eB_inj.eq_iff]`.
-/
theorem blk_unitary {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hs : s ∈ UWset k r (z0 k r)) : blk s ∈ Matrix.unitaryGroup (Fin k) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext q q'
  have hU : sᴴ * Hpk k r * s = Hpk k r := hs.1
  have e := congrFun (congrFun hU (eB k r q)) (eB k r q')
  rw [H_blrow (bl_eB q), Matrix.mul_apply] at e
  rw [sumB _ (fun p hp => by rw [row_zero hs hp (bl_eB q'), mul_zero])] at e
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, H_blcol (bl_eB _), mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at e
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.star_apply, blk]
  rw [e]
  simp [eB_inj.eq_iff]

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `hj : bl k r j`. Distinguish the cases in `hi : bl k r i`. Take `⟨qi, rfl⟩` from `ex_eB hi`. Take `⟨qj, rfl⟩` from `ex_eB hj`.

Rewrite using `[bw_ee]`. Both sides reduce to the same expression. Rewrite using `[bw_off _ hi hj, row_zero hs hi hj]`. Rewrite using `[bw_col _ _ hj, col_std hs hj]`.
-/
theorem eq_blockW {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hs : s ∈ UWset k r (z0 k r)) : s = Formalism.MainNotions.S.blockW k r (blk s) := by
  ext i j
  by_cases hj : bl k r j
  · by_cases hi : bl k r i
    · obtain ⟨qi, rfl⟩ := ex_eB hi
      obtain ⟨qj, rfl⟩ := ex_eB hj
      rw [bw_ee]; rfl
    · rw [bw_off _ hi hj, row_zero hs hi hj]
  · rw [bw_col _ _ hj, col_std hs hj]

/- English proof (translation)
Establish `hK : IsCompact (Set.pi Set.univ (fun _ : Fin k => Set.pi Set.univ (fun _ : Fin k => Metric.closedBall (0 : ℂ) 1)) : Set (Matrix (Fin k) (Fin k) ℂ))` using `isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall 0 1))`. Establish `hC : IsClosed (unitary (Matrix (Fin k) (Fin k) ℂ) : Set (Matrix (Fin k) (Fin k) ℂ))`. Establish `e : (unitary (Matrix (Fin k) (Fin k) ℂ) : Set (Matrix (Fin k) (Fin k) ℂ)) = {U : Matrix (Fin k) (Fin k) ℂ | Uᴴ * U = 1} ∩ {U | U * Uᴴ = 1}`. Use extensionality with `U`. Simplify using `[Unitary.mem_iff, Matrix.star_eq_conjTranspose]`.

Rewrite using `[e]`. Conclude with `(isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const).inter (isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_conjTranspose) continuous_const)`. Use `hK.of_isClosed_subset hC ?_` and prove the remaining obligations. Introduce `U hU i _ j _`. Simplify using `using entry_norm_bound_of_unitary (n := Fin k) (𝕜 := ℂ) hU i j`.
-/
theorem isCompact_unitary_mat :
    IsCompact (unitary (Matrix (Fin k) (Fin k) ℂ) : Set (Matrix (Fin k) (Fin k) ℂ)) := by
  have hK : IsCompact (Set.pi Set.univ (fun _ : Fin k => Set.pi Set.univ
      (fun _ : Fin k => Metric.closedBall (0 : ℂ) 1)) : Set (Matrix (Fin k) (Fin k) ℂ)) :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall 0 1))
  have hC : IsClosed (unitary (Matrix (Fin k) (Fin k) ℂ) : Set (Matrix (Fin k) (Fin k) ℂ)) := by
    have e : (unitary (Matrix (Fin k) (Fin k) ℂ) : Set (Matrix (Fin k) (Fin k) ℂ)) =
        {U : Matrix (Fin k) (Fin k) ℂ | Uᴴ * U = 1} ∩ {U | U * Uᴴ = 1} := by
      ext U; simp [Unitary.mem_iff, Matrix.star_eq_conjTranspose]
    rw [e]
    exact (isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const).inter
      (isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_conjTranspose) continuous_const)
  refine hK.of_isClosed_subset hC ?_
  intro U hU i _ j _
  simpa using entry_norm_bound_of_unitary (n := Fin k) (𝕜 := ℂ) hU i j

@[instance_reducible] def measUG (k : ℕ) : MeasurableSpace (unitary (Matrix (Fin k) (Fin k) ℂ)) := borel _

attribute [local instance] measUG

/- English proof (translation)
Assemble the required witnesses or components as `⟨rfl⟩`.
-/
theorem borelUG : BorelSpace (unitary (Matrix (Fin k) (Fin k) ℂ)) := ⟨rfl⟩

attribute [local instance] borelUG

/- English proof (translation)
The claim follows from `isCompact_iff_compactSpace.mp isCompact_unitary_mat`.
-/
theorem compactUG : CompactSpace (unitary (Matrix (Fin k) (Fin k) ℂ)) :=
  isCompact_iff_compactSpace.mp isCompact_unitary_mat

attribute [local instance] compactUG

def FW (k r : ℕ) (u : unitary (Matrix (Fin k) (Fin k) ℂ)) : Mt k r :=
  fun i j => Formalism.MainNotions.S.blockW k r u.1 i j

/- English proof (translation)
Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Simplify using `only [FW, Formalism.MainNotions.S.blockW]`. Use `split_ifs`. Apply the tactic sequence `all_goals first | exact continuous_subtype_val.matrix_elem _ _ | exact continuous_const`.
-/
theorem contFW : Continuous (FW k r) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [FW, Formalism.MainNotions.S.blockW]
  split_ifs
  all_goals first | exact continuous_subtype_val.matrix_elem _ _ | exact continuous_const

/- English proof (translation)
Establish `hc : Continuous (lmulM (k` using `k) (r := r) s) := by`. Unfold `lmulM`. Conclude with `continuous_const.matrix_mul continuous_id`. Conclude with `hc.measurable`.
-/
theorem measurable_lmulM' (s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable (lmulM (k := k) (r := r) s) := by
  have hc : Continuous (lmulM (k := k) (r := r) s) := by
    unfold lmulM
    exact continuous_const.matrix_mul continuous_id
  exact hc.measurable

/- English proof (translation)
Use `haveI : Nonempty (unitary (Matrix (Fin k) (Fin k) ℂ)) := ⟨1⟩`. Set `ν : Measure (unitary (Matrix (Fin k) (Fin k) ℂ))` to `Measure.haarMeasure ⊤`. Establish `hν : ν Set.univ = 1`. Use `Measure.haarMeasure_self (G := unitary (Matrix (Fin k) (Fin k) ℂ)) (K₀ := ⊤)` as an intermediate fact. Simplify `this` using `[TopologicalSpace.PositiveCompacts.coe_top]`.

Establish `hFm : Measurable (FW k r)` using `contFW.measurable`. Establish `huniv : ν.map (FW k r) Set.univ = 1`. Rewrite using `[Measure.map_apply hFm MeasurableSet.univ]`. Simplify using `using hν`. Use `haveI : IsProbabilityMeasure (ν.map (FW k r)) := ⟨huniv⟩`.

Use `⟨ν.map (FW k r), ⟨inferInstance, ?_, ?_, ?_⟩, huniv⟩` and prove the remaining obligations. Introduce `h`. Rewrite `huniv` using `[h]`. Simplify using `at huniv`. Establish `hsub : {x : Mt k r | Matrix.of x ∉ UWset k r (z0 k r)} ⊆ (Set.range (FW k r))ᶜ`.

Introduce and unpack `x hx ⟨u, rfl⟩`. Conclude with `hx (mem_UW u.2)`. Establish `hmeas : MeasurableSet (Set.range (FW k r))ᶜ` using `(isCompact_range contFW).isClosed.measurableSet.compl`. Use `le_antisymm ?_ bot_le` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Introduce `s hs`. Set `u0 : unitary (Matrix (Fin k) (Fin k) ℂ)` to `⟨blk s, blk_unitary hs⟩`. Establish `hcomp : lmulM s ∘ FW k r = FW k r ∘ (fun u => u0 * u)`. Use function extensionality and compare the values at `u`. Express the relevant statement in the definitionally equal form `(s * Formalism.MainNotions.S.blockW k r u.1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = (Formalism.MainNotions.S.blockW k r (blk s * u.1) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)`.

Rewrite using `[blockW_mul, ← eq_blockW hs]`. Rewrite using `[Measure.map_map (measurable_lmulM' s) hFm, hcomp, ← Measure.map_map hFm (continuous_const_mul u0).measurable, map_mul_left_eq_self]`.
-/
theorem main (k r : ℕ) : ∃ μW : Measure (Mt k r),
    Formalism.MainNotions.S.IsHaarOn (UWset k r (z0 k r)) μW ∧ μW Set.univ = 1 := by
  haveI : Nonempty (unitary (Matrix (Fin k) (Fin k) ℂ)) := ⟨1⟩
  let ν : Measure (unitary (Matrix (Fin k) (Fin k) ℂ)) := Measure.haarMeasure ⊤
  have hν : ν Set.univ = 1 := by
    have := Measure.haarMeasure_self (G := unitary (Matrix (Fin k) (Fin k) ℂ)) (K₀ := ⊤)
    simpa [TopologicalSpace.PositiveCompacts.coe_top] using this
  have hFm : Measurable (FW k r) := contFW.measurable
  have huniv : ν.map (FW k r) Set.univ = 1 := by
    rw [Measure.map_apply hFm MeasurableSet.univ]; simpa using hν
  haveI : IsProbabilityMeasure (ν.map (FW k r)) := ⟨huniv⟩
  refine ⟨ν.map (FW k r), ⟨inferInstance, ?_, ?_, ?_⟩, huniv⟩
  · intro h; rw [h] at huniv; simp at huniv
  · have hsub : {x : Mt k r | Matrix.of x ∉ UWset k r (z0 k r)} ⊆ (Set.range (FW k r))ᶜ := by
      rintro x hx ⟨u, rfl⟩
      exact hx (mem_UW u.2)
    have hmeas : MeasurableSet (Set.range (FW k r))ᶜ :=
      (isCompact_range contFW).isClosed.measurableSet.compl
    refine le_antisymm ?_ bot_le
    calc _ ≤ ν.map (FW k r) (Set.range (FW k r))ᶜ := measure_mono hsub
      _ = 0 := by rw [Measure.map_apply hFm hmeas]; simp
  · intro s hs
    let u0 : unitary (Matrix (Fin k) (Fin k) ℂ) := ⟨blk s, blk_unitary hs⟩
    have hcomp : lmulM s ∘ FW k r = FW k r ∘ (fun u => u0 * u) := by
      funext u
      change (s * Formalism.MainNotions.S.blockW k r u.1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) =
        (Formalism.MainNotions.S.blockW k r (blk s * u.1) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
      rw [blockW_mul, ← eq_blockW hs]
    rw [Measure.map_map (measurable_lmulM' s) hFm, hcomp,
      ← Measure.map_map hFm (continuous_const_mul u0).measurable, map_mul_left_eq_self]

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.StandardBasisEmbedding
