import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.Transfer

noncomputable section

open NumberField InfinitePlace Pointwise

namespace PositivityTheory.KB.SplitAffineSpectral.unitAtAlt

variable {L : Type} [Field L] [NumberField L]

omit [NumberField L] in
/- English proof (translation)
The claim follows from `w.pos_iff.mpr (by simp)`.
-/
theorem place_pos (v : (𝓞 L)ˣ) (w : InfinitePlace L) : 0 < w (algebraMap (𝓞 L) L (v : 𝓞 L)) := w.pos_iff.mpr (by simp)

def lchar (a : InfinitePlace L → ℕ) : (𝓞 L)ˣ →* Multiplicative ℝ where
  toFun v := Multiplicative.ofAdd (∑ w, (a w : ℝ) * Real.log (w (algebraMap (𝓞 L) L (v : 𝓞 L))))
  map_one' := by simp
  map_mul' x y := by
    rw [← ofAdd_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Units.val_mul, map_mul, map_mul, Real.log_mul (place_pos x w).ne' (place_pos y w).ne']
    ring

/- English proof (translation)
Establish `hpos : ∀ w : InfinitePlace L, 0 < w (algebraMap (𝓞 L) L (v : 𝓞 L)) ^ a w` using `fun w => pow_pos (place_pos v w) _`. Establish `hP : 0 < ∏ w, w (algebraMap (𝓞 L) L (v : 𝓞 L)) ^ a w` using `Finset.prod_pos fun w _ => hpos w`. Establish `hlog : Real.log (∏ w, w (algebraMap (𝓞 L) L (v : 𝓞 L)) ^ a w) = ∑ w, (a w : ℝ) * Real.log (w (algebraMap (𝓞 L) L (v : 𝓞 L)))`. Rewrite using `[Real.log_prod (fun w _ => (hpos w).ne')]`. Conclude with `Finset.sum_congr rfl fun w _ => Real.log_pow _ _`.

Express the relevant statement in the definitionally equal form `Multiplicative.ofAdd (∑ w, (a w : ℝ) * Real.log (w (algebraMap (𝓞 L) L (v : 𝓞 L)))) = 1 ↔ _`. Rewrite using `[ofAdd_eq_one, ← hlog]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[← Real.exp_log hP, h, Real.exp_zero]`.

Introduce `h`. Rewrite using `[h, Real.log_one]`.
-/
theorem lchar_eq_one_iff (a : InfinitePlace L → ℕ) (v : (𝓞 L)ˣ) :
    lchar a v = 1 ↔ ∏ w, (w (algebraMap (𝓞 L) L (v : 𝓞 L))) ^ a w = 1 := by
  have hpos : ∀ w : InfinitePlace L, 0 < w (algebraMap (𝓞 L) L (v : 𝓞 L)) ^ a w :=
    fun w => pow_pos (place_pos v w) _
  have hP : 0 < ∏ w, w (algebraMap (𝓞 L) L (v : 𝓞 L)) ^ a w :=
    Finset.prod_pos fun w _ => hpos w
  have hlog : Real.log (∏ w, w (algebraMap (𝓞 L) L (v : 𝓞 L)) ^ a w) =
      ∑ w, (a w : ℝ) * Real.log (w (algebraMap (𝓞 L) L (v : 𝓞 L))) := by
    rw [Real.log_prod (fun w _ => (hpos w).ne')]
    exact Finset.sum_congr rfl fun w _ => Real.log_pow _ _
  change Multiplicative.ofAdd (∑ w, (a w : ℝ) * Real.log (w (algebraMap (𝓞 L) L (v : 𝓞 L)))) = 1 ↔ _
  rw [ofAdd_eq_one, ← hlog]
  constructor
  · intro h
    rw [← Real.exp_log hP, h, Real.exp_zero]
  · intro h
    rw [h, Real.log_one]

/- English proof (translation)
Establish `hcard : ∑ w, a w < Fintype.card (InfinitePlace L)`. Rewrite using `[card_eq_nrRealPlaces_add_nrComplexPlaces]`. Use linear arithmetic over natural numbers and integers. Choose the witnesses or unpack the hypotheses as in `⟨w₁, hw₁⟩ : ∃ w₁, a w₁ = 0 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Establish `h1 : ∑ _w : InfinitePlace L, 1 ≤ ∑ w, a w` using `Finset.sum_le_sum fun w _ => Nat.one_le_iff_ne_zero.mpr (h w)`. Simplify using `at h1`. Use linear arithmetic over natural numbers and integers. Choose the witnesses or unpack the hypotheses as in `⟨w₂, hw₂⟩ : ∃ w₂, 0 < a w₂ := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `h0 : ∑ w, a w = 0` using `Finset.sum_eq_zero fun w _ => by`. Use `h w` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use linear arithmetic over natural numbers and integers. Establish `hne : w₂ ≠ w₁`. Introduce and unpack `rfl`. Use linear arithmetic over natural numbers and integers. Take `⟨u, hu⟩` from `NumberField.Units.dirichletUnitTheorem.exists_unit L w₁`.

Use `⟨u, fun h => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Multiplicative.ofAdd (∑ w, (a w : ℝ) * Real.log (w (algebraMap (𝓞 L) L (u : 𝓞 L)))) = 1 at h`. Rewrite `h` using `[ofAdd_eq_one]`. Establish `hlt : ∑ w, (a w : ℝ) * Real.log (w (algebraMap (𝓞 L) L (u : 𝓞 L))) < ∑ _w : InfinitePlace L, (0 : ℝ)`. Apply `Finset.sum_lt_sum` to reduce the goal to its premises.

Introduce `w _`. Distinguish the cases in `hw : w = w₁`. Substitute `hw` using the available equality. Simplify using `[hw₁]`. Conclude with `mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (hu w hw).le`.

Conclude with `⟨w₂, Finset.mem_univ _, mul_neg_of_pos_of_neg (by exact_mod_cast hw₂) (hu w₂ hne)⟩`. Rewrite `hlt` using `[Finset.sum_const_zero, h]`. Conclude with `lt_irrefl _ hlt`.
-/
theorem lchar_nontrivial (hC : IsTotallyComplex L) (a : InfinitePlace L → ℕ) (ha : 0 < ∑ w, a w)
    (hm : ∑ w, a w < nrComplexPlaces L) : ∃ v, lchar a v ≠ 1 := by
  classical
  have hcard : ∑ w, a w < Fintype.card (InfinitePlace L) := by
    rw [card_eq_nrRealPlaces_add_nrComplexPlaces]
    omega
  obtain ⟨w₁, hw₁⟩ : ∃ w₁, a w₁ = 0 := by
    by_contra h
    push_neg at h
    have h1 : ∑ _w : InfinitePlace L, 1 ≤ ∑ w, a w :=
      Finset.sum_le_sum fun w _ => Nat.one_le_iff_ne_zero.mpr (h w)
    simp at h1
    omega
  obtain ⟨w₂, hw₂⟩ : ∃ w₂, 0 < a w₂ := by
    by_contra h
    push_neg at h
    have h0 : ∑ w, a w = 0 := Finset.sum_eq_zero fun w _ => by
      have := h w
      omega
    omega
  have hne : w₂ ≠ w₁ := by
    rintro rfl
    omega
  obtain ⟨u, hu⟩ := NumberField.Units.dirichletUnitTheorem.exists_unit L w₁
  refine ⟨u, fun h => ?_⟩
  change Multiplicative.ofAdd (∑ w, (a w : ℝ) * Real.log (w (algebraMap (𝓞 L) L (u : 𝓞 L)))) = 1 at h
  rw [ofAdd_eq_one] at h
  have hlt : ∑ w, (a w : ℝ) * Real.log (w (algebraMap (𝓞 L) L (u : 𝓞 L))) <
      ∑ _w : InfinitePlace L, (0 : ℝ) := by
    apply Finset.sum_lt_sum
    · intro w _
      by_cases hw : w = w₁
      · subst hw
        simp [hw₁]
      · exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (hu w hw).le
    · exact ⟨w₂, Finset.mem_univ _,
        mul_neg_of_pos_of_neg (by exact_mod_cast hw₂) (hu w₂ hne)⟩
  rw [Finset.sum_const_zero, h] at hlt
  exact lt_irrefl _ hlt

/- English proof (translation)
Introduce `hfi`. Take `⟨v, hv⟩` from `lchar_nontrivial hC a ha hm`. Apply `hv` to reduce the goal to its premises. Establish `hmem` using `(lchar a).ker.pow_index_mem v`. Rewrite `hmem` using `[MonoidHom.mem_ker, map_pow]`.

Establish `hidx : (lchar a).ker.index ≠ 0` using `Subgroup.FiniteIndex.index_ne_zero`. Establish `h1 : Multiplicative.toAdd (lchar a v ^ (lchar a).ker.index) = 0`. Rewrite using `[hmem]`. Both sides reduce to the same expression. Rewrite `h1` using `[toAdd_pow, nsmul_eq_mul, mul_eq_zero]`.

Break down `h1 with h1 | h1` into its components or cases. Conclude with `absurd (by exact_mod_cast h1) hidx`. Conclude with `toAdd_eq_zero.mp h1`.
-/
theorem lchar_ker_not_finiteIndex (hC : IsTotallyComplex L) (a : InfinitePlace L → ℕ) (ha : 0 < ∑ w, a w)
    (hm : ∑ w, a w < nrComplexPlaces L) : ¬ (lchar a).ker.FiniteIndex := by
  intro hfi
  obtain ⟨v, hv⟩ := lchar_nontrivial hC a ha hm
  apply hv
  have hmem := (lchar a).ker.pow_index_mem v
  rw [MonoidHom.mem_ker, map_pow] at hmem
  have hidx : (lchar a).ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have h1 : Multiplicative.toAdd (lchar a v ^ (lchar a).ker.index) = 0 := by
    rw [hmem]
    rfl
  rw [toAdd_pow, nsmul_eq_mul, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact absurd (by exact_mod_cast h1) hidx
  · exact toAdd_eq_zero.mp h1

end PositivityTheory.KB.SplitAffineSpectral.unitAtAlt

open PositivityTheory.KB.SplitAffineSpectral.unitAtAlt in
/- English proof (translation)
Unfold `PositivityTheory.KB.SplitAffineSpectral.Unit`. Introduce `L _ _ hC m hm`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Set `s : Finset (InfinitePlace L → ℕ)` to `(Fintype.piFinset fun _ => Finset.range (m + 1)).filter fun a => 0 < ∑ w, a w ∧ ∑ w, a w ≤ m`.

Take `⟨k, hk, hfi⟩` from `Subgroup.exists_finiteIndex_of_leftCoset_cover (H := fun a => (lchar a).ker) (g := fun _ => 1) (s := s) (by`. Use extensionality with `v`. Simplify using `only [Set.mem_iUnion, Set.mem_univ, iff_true, one_smul]`. Take `⟨a, ha0, ham, hprod⟩` from `hcon v`. Use `⟨a, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [s, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]`. Use `⟨fun w => ?_, ha0, ham⟩` and prove the remaining obligations. Use `Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ w)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `(MonoidHom.mem_ker).mpr ((lchar_eq_one_iff a v).mpr hprod))`.

Simplify using `only [s, Finset.mem_filter] at hk`. Conclude with `lchar_ker_not_finiteIndex hC k hk.2.1 (lt_of_le_of_lt hk.2.2 hm) hfi`.
-/
theorem PositivityTheory.KB.SplitAffineSpectral.unit : PositivityTheory.KB.SplitAffineSpectral.Unit := by
  unfold PositivityTheory.KB.SplitAffineSpectral.Unit
  intro L _ _ hC m hm
  classical
  by_contra hcon
  push_neg at hcon
  let s : Finset (InfinitePlace L → ℕ) :=
    (Fintype.piFinset fun _ => Finset.range (m + 1)).filter
      fun a => 0 < ∑ w, a w ∧ ∑ w, a w ≤ m
  obtain ⟨k, hk, hfi⟩ := Subgroup.exists_finiteIndex_of_leftCoset_cover
    (H := fun a => (lchar a).ker) (g := fun _ => 1) (s := s) (by
      ext v
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true, one_smul]
      obtain ⟨a, ha0, ham, hprod⟩ := hcon v
      refine ⟨a, ?_, ?_⟩
      · simp only [s, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
        refine ⟨fun w => ?_, ha0, ham⟩
        have := Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ w)
        omega
      · exact (MonoidHom.mem_ker).mpr ((lchar_eq_one_iff a v).mpr hprod))
  simp only [s, Finset.mem_filter] at hk
  exact lchar_ker_not_finiteIndex hC k hk.2.1 (lt_of_le_of_lt hk.2.2 hm) hfi
