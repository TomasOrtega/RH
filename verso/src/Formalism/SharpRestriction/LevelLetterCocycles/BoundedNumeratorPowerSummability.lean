import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.ArcIffLocalOfAdmissible
import Formalism.TruncatedSeriesCounting.EtaDeterminantPolynomialIdentities
import Formalism.GaussValuationBounds.NokLemmaCVal
import Formalism.WindowSums.PowerSeriesRelationList
import Formalism.DistinguishedUnitIdeals.DescentLemmasAllHold

noncomputable section

namespace Formalism.MainNotions.WachCoordinates

/- English proof (translation)
Establish `hu : IsUnit (1 + (l : ℤ_[l]))`. Rewrite using `[PadicInt.isUnit_iff]`. Establish `h1 : ‖(l : ℤ_[l])‖ < 1`. Rewrite using `[PadicInt.norm_p]`. Apply `inv_lt_one_of_one_lt₀` to reduce the goal to its premises.

Conclude with `(Fact.out : l.Prime).one_lt` after adjusting the coercions. Establish `h2 : ‖(1 : ℤ_[l]) + l‖ = max ‖(1 : ℤ_[l])‖ ‖(l : ℤ_[l])‖` using `PadicInt.norm_add_eq_max_of_ne (by rw [norm_one]; exact h1.ne')`. Rewrite using `[h2, norm_one]`. Conclude with `max_eq_left h1.le`. Use `⟨hu.unit, ?_⟩` and prove the remaining obligations.

Establish `: ((hu.unit : ℤ_[l]ˣ) : ℤ_[l]) - 1 = (l : ℤ_[l])`. Rewrite using `[IsUnit.unit_spec]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `PadicInt.valuation_p`.
-/
theorem exists_chi (l : ℕ) [Fact l.Prime] :
    ∃ χ : ℤ_[l]ˣ, PadicInt.valuation ((χ : ℤ_[l]) - 1) = 1 := by
  have hu : IsUnit (1 + (l : ℤ_[l])) := by
    rw [PadicInt.isUnit_iff]
    have h1 : ‖(l : ℤ_[l])‖ < 1 := by
      rw [PadicInt.norm_p]
      apply inv_lt_one_of_one_lt₀
      exact_mod_cast (Fact.out : l.Prime).one_lt
    have h2 : ‖(1 : ℤ_[l]) + l‖ = max ‖(1 : ℤ_[l])‖ ‖(l : ℤ_[l])‖ :=
      PadicInt.norm_add_eq_max_of_ne (by rw [norm_one]; exact h1.ne')
    rw [h2, norm_one]; exact max_eq_left h1.le
  refine ⟨hu.unit, ?_⟩
  have : ((hu.unit : ℤ_[l]ˣ) : ℤ_[l]) - 1 = (l : ℤ_[l]) := by
    rw [IsUnit.unit_spec]; ring
  rw [this]; exact PadicInt.valuation_p

/- English proof (translation)
Establish `h1 : s.sup f ≤ ⌊B⌋₊` using `Finset.sup_le fun x hx => Nat.le_floor (h x hx)`. Conclude with `le_trans (by exact_mod_cast h1) (Nat.floor_le hB)`.
-/
theorem cast_sup_le {ι : Type*} (s : Finset ι) (f : ι → ℕ) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ x ∈ s, (f x : ℝ) ≤ B) : ((s.sup f : ℕ) : ℝ) ≤ B := by
  have h1 : s.sup f ≤ ⌊B⌋₊ := Finset.sup_le fun x hx => Nat.le_floor (h x hx)
  exact le_trans (by exact_mod_cast h1) (Nat.floor_le hB)

/- English proof (translation)
Unfold `wins at hw`. Rewrite `hw` using `[Finset.mem_image]`. Take `⟨p, hp, rfl⟩` from `hw`. Rewrite `hp` using `[Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]`. Conclude with `⟨p.1, p.2, rfl, hp.1.1.1, by omega, hp.2⟩`.
-/
theorem exists_eq_Ico_of_mem_windows {g h : ℕ} {w : Finset ℤ} (hw : w ∈ wins g h) :
    ∃ (a : ℤ) (k : ℕ), w = Finset.Ico a (a + (k : ℤ)) ∧ -(2 * h : ℤ) ≤ a ∧ k ≤ 3 * g ∧
      a + (k : ℤ) ≤ 2 * h + 1 := by
  unfold wins at hw
  rw [Finset.mem_image] at hw
  obtain ⟨p, hp, rfl⟩ := hw
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hp
  exact ⟨p.1, p.2, rfl, hp.1.1.1, by omega, hp.2⟩

/- English proof (translation)
Establish `: Fact l.Prime` using `⟨hl⟩`. Take `⟨χ, hχ⟩` from `exists_chi l`. Take `⟨a₁, k₁, rfl, ha₁, hk₁, hb₁⟩` from `exists_eq_Ico_of_mem_windows h₁`. Take `⟨a₂, k₂, rfl, ha₂, hk₂, hb₂⟩` from `exists_eq_Ico_of_mem_windows h₂`. Take `⟨a₃, k₃, rfl, ha₃, hk₃, hb₃⟩` from `exists_eq_Ico_of_mem_windows h₃`.

Use `set JJ : Finset ℤ := Finset.Ico a₁ (a₁ + (k₁ : ℤ)) ∪ Finset.Ico a₂ (a₂ + (k₂ : ℤ)) ∪ Finset.Ico a₃ (a₃ + (k₃ : ℤ)) with hJJ`. Establish `hK` using `Formalism.NOK.kapBound_proof l h2 χ hχ ell g h ![a₁, a₂, a₃, a₁, a₁] JJ (by`. Introduce `i hi`. Rewrite `hi` using `[hJJ, Finset.mem_union, Finset.mem_union, Finset.mem_Ico, Finset.mem_Ico, Finset.mem_Ico]`. Rewrite using `[Finset.mem_biUnion]`.

Break down `hi with (hi | hi) | hi` into its components or cases. Conclude with `⟨0, Finset.mem_univ _, by`. Simplify using `only [Matrix.cons_val_zero, Finset.mem_Ico]`. Use the proof step `omega⟩`. Conclude with `⟨1, Finset.mem_univ _, by`.

Simplify using `only [Matrix.cons_val_one, Matrix.cons_val_zero, Finset.mem_Ico]`. Use the proof step `omega⟩`. Conclude with `⟨2, Finset.mem_univ _, by`. Simplify using `only [Matrix.cons_val, Finset.mem_Ico]`. Use the proof step `omega⟩)`.

Use the proof step `(by`. Introduce `i hi`. Rewrite `hi` using `[hJJ, Finset.mem_union, Finset.mem_union, Finset.mem_Ico, Finset.mem_Ico, Finset.mem_Ico]`. Rewrite using `[abs_le]`. Use the proof step `omega)`.

Establish `hV` using `(Formalism.WindowSums.arc_KillerVal l h2 χ hχ ell JJ).2`. Establish `hE : vPP1 l ell JJ = PadicInt.valuation ((Formalism.WindowSums.PP l χ ell JJ).eval 1)`. Rewrite using `[hV]`. Unfold `vPP1`. Rewrite using `[add_comm]`.

Use `congr 1`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Rewrite using `[hE]`. Conclude with `hK.2`.
-/
theorem vPP1_le (l : ℕ) (hl : l.Prime) (h2 : l ≠ 2) (ell g h : ℕ) (w₁ w₂ w₃ : Finset ℤ)
    (h₁ : w₁ ∈ wins g h) (h₂ : w₂ ∈ wins g h) (h₃ : w₃ ∈ wins g h) :
    (vPP1 l ell (w₁ ∪ w₂ ∪ w₃) : ℝ) ≤
      ell + 20 * g * (1 + ell) + 5 * (4 * g / ((l : ℝ) - 1) + Real.logb l (2 * h)) := by
  have : Fact l.Prime := ⟨hl⟩
  obtain ⟨χ, hχ⟩ := exists_chi l
  obtain ⟨a₁, k₁, rfl, ha₁, hk₁, hb₁⟩ := exists_eq_Ico_of_mem_windows h₁
  obtain ⟨a₂, k₂, rfl, ha₂, hk₂, hb₂⟩ := exists_eq_Ico_of_mem_windows h₂
  obtain ⟨a₃, k₃, rfl, ha₃, hk₃, hb₃⟩ := exists_eq_Ico_of_mem_windows h₃
  set JJ : Finset ℤ := Finset.Ico a₁ (a₁ + (k₁ : ℤ)) ∪ Finset.Ico a₂ (a₂ + (k₂ : ℤ)) ∪
    Finset.Ico a₃ (a₃ + (k₃ : ℤ)) with hJJ
  have hK := Formalism.NOK.kapBound_proof l h2 χ hχ ell g h ![a₁, a₂, a₃, a₁, a₁] JJ
    (by
      intro i hi
      rw [hJJ, Finset.mem_union, Finset.mem_union, Finset.mem_Ico, Finset.mem_Ico,
        Finset.mem_Ico] at hi
      rw [Finset.mem_biUnion]
      rcases hi with (hi | hi) | hi
      · exact ⟨0, Finset.mem_univ _, by
          simp only [Matrix.cons_val_zero, Finset.mem_Ico]; omega⟩
      · exact ⟨1, Finset.mem_univ _, by
          simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Finset.mem_Ico]; omega⟩
      · exact ⟨2, Finset.mem_univ _, by
          simp only [Matrix.cons_val, Finset.mem_Ico]; omega⟩)
    (by
      intro i hi
      rw [hJJ, Finset.mem_union, Finset.mem_union, Finset.mem_Ico, Finset.mem_Ico,
        Finset.mem_Ico] at hi
      rw [abs_le]
      omega)
  have hV := (Formalism.WindowSums.arc_KillerVal l h2 χ hχ ell JJ).2
  have hE : vPP1 l ell JJ = PadicInt.valuation ((Formalism.WindowSums.PP l χ ell JJ).eval 1) := by
    rw [hV]; unfold vPP1
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hE]
  exact hK.2

/- English proof (translation)
Establish `hl' : (3 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hgeo : Summable fun a : ℕ => ((2 * h : ℝ) + K + 3) * (((l : ℝ) - 1)⁻¹) ^ a`. Apply `Summable.mul_left` to reduce the goal to its premises. Apply `summable_geometric_of_lt_one` to reduce the goal to its premises. Apply `inv_nonneg.mpr` to reduce the goal to its premises.

Combine the linear equalities and inequalities to obtain the conclusion. Apply `inv_lt_one_of_one_lt₀` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Use `Summable.of_nonneg_of_le (fun a => ?_) (fun a => ?_) hgeo` and prove the remaining obligations. Apply `div_nonneg` to reduce the goal to its premises.

Check the signs of the components of the expression. Apply `pow_nonneg` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[inv_pow, ← div_eq_mul_inv]`. Apply `div_le_div_of_nonneg_right` to reduce the goal to its premises.

Establish `: (H (c + ((a + 1 : ℕ) : ZMod n)) : ℝ) ≤ 2 * h` using `by exact_mod_cast hH _`. Combine the linear equalities and inequalities to obtain the conclusion. Apply `pow_nonneg` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem summable_nine_pow_mul_inv_sq_succ (l : ℕ) (hl : 3 ≤ l) (n : ℕ) (H : ZMod n → ℕ) (h : ℕ) (c : ZMod n) (K : ℝ)
    (hK : 0 ≤ K) (hH : ∀ x, H x ≤ 2 * h) :
    Summable fun a : ℕ => ((H (c + ((a + 1 : ℕ) : ZMod n)) : ℝ) + K + 3) / ((l : ℝ) - 1) ^ a := by
  have hl' : (3 : ℝ) ≤ l := by exact_mod_cast hl
  have hgeo : Summable fun a : ℕ => ((2 * h : ℝ) + K + 3) * (((l : ℝ) - 1)⁻¹) ^ a := by
    apply Summable.mul_left
    apply summable_geometric_of_lt_one
    · apply inv_nonneg.mpr; linarith
    · apply inv_lt_one_of_one_lt₀; linarith
  refine Summable.of_nonneg_of_le (fun a => ?_) (fun a => ?_) hgeo
  · apply div_nonneg
    · positivity
    · apply pow_nonneg; linarith
  · rw [inv_pow, ← div_eq_mul_inv]
    apply div_le_div_of_nonneg_right
    · have : (H (c + ((a + 1 : ℕ) : ZMod n)) : ℝ) ≤ 2 * h := by exact_mod_cast hH _
      linarith
    · apply pow_nonneg; linarith

/- English proof (translation)
Establish `hl' : (3 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hHm : Hmax n H ≤ 2 * h` using `Finset.sup_le fun x _ => hH x`. Establish `hcc : ccPar l (Hmax n H) ≤ ⌈1 + Real.logb l (2 * (h : ℝ) + 1)⌉₊`. Unfold `ccPar`. Apply `Nat.ceil_mono` to reduce the goal to its premises.

Establish `: Real.logb l ((Hmax n H : ℝ) + 1) ≤ Real.logb l (2 * (h : ℝ) + 1)`. Apply `Real.logb_le_logb_of_le (by linarith) (by positivity)` to reduce the goal to its premises. Establish `: (Hmax n H : ℝ) ≤ 2 * h` using `by exact_mod_cast hHm`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hccR : (ccPar l (Hmax n H) : ℝ) ≤ (⌈1 + Real.logb l (2 * (h : ℝ) + 1)⌉₊ : ℝ)`. Conclude with `hcc` after adjusting the coercions. Establish `hs0 : 0 ≤ sBd l n H c`. Unfold `sBd`. Apply `tsum_nonneg` to reduce the goal to its premises.

Introduce `a`. Apply `div_nonneg` to reduce the goal to its premises. Check the signs of the components of the expression. Apply `pow_nonneg` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hs : sBd l n H c ≤ ∑' a : ℕ, ((H (c + ((a + 1 : ℕ) : ZMod n)) : ℝ) + (⌈1 + Real.logb l (2 * (h : ℝ) + 1)⌉₊ : ℝ) + 3) / ((l : ℝ) - 1) ^ a`. Unfold `sBd`. Apply `Summable.tsum_le_tsum _ (summable_nine_pow_mul_inv_sq_succ l hl n H h c _ (by positivity) hH) (summable_nine_pow_mul_inv_sq_succ l hl n H h c _ (by positivity) hH)` to reduce the goal to its premises. Introduce `a`. Apply `div_le_div_of_nonneg_right` to reduce the goal to its premises.

Combine the linear equalities and inequalities to obtain the conclusion. Apply `pow_nonneg` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Use `Formalism.TruncatedSeriesCounting.WachCoordinates.remainder_bound_of_tsum l hl n H G h j c (sBd l n H c) (rF l n H c) h1 hH hG hs ?_` and prove the remaining obligations. Unfold `rF`.

Use `push_cast`. Establish `hq : 0 ≤ (l : ℝ) / ((l : ℝ) - 1) ^ 2` using `by positivity`. Establish `hm0 : 0 ≤ min (⌊sBd l n H c⌋₊ : ℝ) (Hmax n H : ℝ)` using `le_min (by positivity) (by positivity)`. Establish `hm : min (⌊sBd l n H c⌋₊ : ℝ) (Hmax n H : ℝ) ≤ sBd l n H c` using `le_trans (min_le_left _ _) (Nat.floor_le hs0)`. Establish `hfl : (⌊min (⌊sBd l n H c⌋₊ : ℝ) (Hmax n H : ℝ) * l / ((l : ℝ) - 1) ^ 2⌋₊ : ℝ) ≤ min (⌊sBd l n H c⌋₊ : ℝ) (Hmax n H : ℝ) * l / ((l : ℝ) - 1) ^ 2`.

Apply `Nat.floor_le` to reduce the goal to its premises. Rewrite using `[mul_div_assoc]`. Conclude with `mul_nonneg hm0 hq`. Establish `hmul : min (⌊sBd l n H c⌋₊ : ℝ) (Hmax n H : ℝ) * l / ((l : ℝ) - 1) ^ 2 ≤ sBd l n H c * l / ((l : ℝ) - 1) ^ 2`. Rewrite using `[mul_div_assoc, mul_div_assoc]`.

Conclude with `mul_le_mul_of_nonneg_right hm hq`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem rF_le (l : ℕ) (hl : 3 ≤ l) (n : ℕ) [NeZero n] (H : ZMod n → ℕ) (G h j : ℕ) (c : ZMod n)
    (h1 : 1 ≤ h) (hH : ∀ x, H x ≤ 2 * h)
    (hG : ∀ k : ℕ, 1 ≤ k → k ≤ j → H (c + (k : ZMod n)) ≤ 2 * G) :
    (rF l n H c : ℝ) ≤
      20 * ((G : ℝ) / l + (h : ℝ) / ((l : ℝ) - 1) ^ (j + 1) + Real.logb l h + 1) := by
  have hl' : (3 : ℝ) ≤ l := by exact_mod_cast hl
  have hHm : Hmax n H ≤ 2 * h := Finset.sup_le fun x _ => hH x
  have hcc : ccPar l (Hmax n H) ≤ ⌈1 + Real.logb l (2 * (h : ℝ) + 1)⌉₊ := by
    unfold ccPar
    apply Nat.ceil_mono
    have : Real.logb l ((Hmax n H : ℝ) + 1) ≤ Real.logb l (2 * (h : ℝ) + 1) := by
      apply Real.logb_le_logb_of_le (by linarith) (by positivity)
      have : (Hmax n H : ℝ) ≤ 2 * h := by exact_mod_cast hHm
      linarith
    linarith
  have hccR : (ccPar l (Hmax n H) : ℝ) ≤ (⌈1 + Real.logb l (2 * (h : ℝ) + 1)⌉₊ : ℝ) := by
    exact_mod_cast hcc
  have hs0 : 0 ≤ sBd l n H c := by
    unfold sBd
    apply tsum_nonneg
    intro a
    apply div_nonneg
    · positivity
    · apply pow_nonneg; linarith
  have hs : sBd l n H c ≤ ∑' a : ℕ, ((H (c + ((a + 1 : ℕ) : ZMod n)) : ℝ) +
        (⌈1 + Real.logb l (2 * (h : ℝ) + 1)⌉₊ : ℝ) + 3) / ((l : ℝ) - 1) ^ a := by
    unfold sBd
    apply Summable.tsum_le_tsum _ (summable_nine_pow_mul_inv_sq_succ l hl n H h c _ (by positivity) hH)
      (summable_nine_pow_mul_inv_sq_succ l hl n H h c _ (by positivity) hH)
    intro a
    apply div_le_div_of_nonneg_right
    · linarith
    · apply pow_nonneg; linarith
  refine Formalism.TruncatedSeriesCounting.WachCoordinates.remainder_bound_of_tsum l hl n H G h j c (sBd l n H c) (rF l n H c) h1 hH hG hs ?_
  unfold rF
  push_cast
  have hq : 0 ≤ (l : ℝ) / ((l : ℝ) - 1) ^ 2 := by positivity
  have hm0 : 0 ≤ min (⌊sBd l n H c⌋₊ : ℝ) (Hmax n H : ℝ) := le_min (by positivity) (by positivity)
  have hm : min (⌊sBd l n H c⌋₊ : ℝ) (Hmax n H : ℝ) ≤ sBd l n H c :=
    le_trans (min_le_left _ _) (Nat.floor_le hs0)
  have hfl : (⌊min (⌊sBd l n H c⌋₊ : ℝ) (Hmax n H : ℝ) * l / ((l : ℝ) - 1) ^ 2⌋₊ : ℝ) ≤
      min (⌊sBd l n H c⌋₊ : ℝ) (Hmax n H : ℝ) * l / ((l : ℝ) - 1) ^ 2 := by
    apply Nat.floor_le
    rw [mul_div_assoc]; exact mul_nonneg hm0 hq
  have hmul : min (⌊sBd l n H c⌋₊ : ℝ) (Hmax n H : ℝ) * l / ((l : ℝ) - 1) ^ 2 ≤
      sBd l n H c * l / ((l : ℝ) - 1) ^ 2 := by
    rw [mul_div_assoc, mul_div_assoc]; exact mul_le_mul_of_nonneg_right hm hq
  linarith

/- English proof (translation)
Unfold `sigPar Formalism.TruncatedSeriesCounting.WachCoordinates.sigE Mpar Formalism.TruncatedSeriesCounting.WachCoordinates.Mpar`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem sigPar_eq (l g h j : ℕ) : sigPar l g h j = Formalism.TruncatedSeriesCounting.WachCoordinates.sigE l g h j := by
  unfold sigPar Formalism.TruncatedSeriesCounting.WachCoordinates.sigE Mpar Formalism.TruncatedSeriesCounting.WachCoordinates.Mpar
  push_cast
  rfl

/- English proof (translation)
Introduce `l hlp hl2 n _ j G S η h ty cuts arcLen H₁ H₂ hcuts hgh hH hHG`. Establish `hl : 3 ≤ l`. Use `hlp.two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hl' : (3 : ℝ) ≤ l` using `by exact_mod_cast hl`.

Take `⟨hne, hj, harc, -, -⟩` from `hcuts`. Establish `hg1 : 1 ≤ gPar G S η` using `le_max_right _ _`. Establish `hGg : G ≤ gPar G S η` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)`. Establish `hh1 : 1 ≤ h` using `le_trans hg1 hgh`. Establish `hell : 1 ≤ ellMax cuts arcLen`.

Take `⟨c, hc⟩` from `hne`. Conclude with `le_trans (harc c hc).1 (Finset.le_sup (f := arcLen) hc)`. Establish `hlog : 0 ≤ Real.logb l h`. Apply `Real.logb_nonneg (by linarith)` to reduce the goal to its premises. Conclude with `hh1` after adjusting the coercions.

Establish `hrr : ((rrPar l n H₁ H₂ cuts : ℕ) : ℝ) ≤ 20 * ((G : ℝ) / l + (h : ℝ) / ((l : ℝ) - 1) ^ (j + 1) + Real.logb l h + 1)`. Unfold `rrPar`. Apply `cast_sup_le` to reduce the goal to its premises. Establish `: 0 ≤ (h : ℝ) / ((l : ℝ) - 1) ^ (j + 1)`. Apply `div_nonneg (by positivity); apply pow_nonneg; linarith` to reduce the goal to its premises.

Check the signs of the components of the expression. Introduce `c hc`. Rewrite using `[Nat.cast_max]`. Apply `max_le` to reduce the goal to its premises. Conclude with `rF_le l hl n H₁ G h j c hh1 (fun x => (hH x).1) fun k h1 h2 => (hHG c hc k h1 h2).1`.

Conclude with `rF_le l hl n H₂ G h j c hh1 (fun x => (hH x).2) fun k h1 h2 => (hHG c hc k h1 h2).2`. Establish `hkap : ((kapPar l (gPar G S η) h (ellMax cuts arcLen) : ℕ) : ℝ) ≤ (ellMax cuts arcLen : ℝ) + 20 * (gPar G S η : ℝ) * (1 + (ellMax cuts arcLen : ℝ)) + 5 * (4 * (gPar G S η : ℝ) / ((l : ℝ) - 1) + Real.logb l (2 * h))`. Unfold `kapPar`. Apply `cast_sup_le` to reduce the goal to its premises. Establish `h1 : 0 ≤ Real.logb l (2 * (h : ℝ))`.

Apply `Real.logb_nonneg (by linarith)` to reduce the goal to its premises. Establish `: (1 : ℝ) ≤ h` using `by exact_mod_cast hh1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : 0 ≤ 4 * (gPar G S η : ℝ) / ((l : ℝ) - 1)`. Apply `div_nonneg (by positivity); linarith` to reduce the goal to its premises.

Check the signs of the components of the expression. Introduce `w hw`. Rewrite `hw` using `[Finset.mem_product, Finset.mem_product]`. Conclude with `vPP1_le l hlp (by omega) _ _ _ _ _ _ hw.1 hw.2.1 hw.2.2`. Establish `hE` using `Formalism.TruncatedSeriesCounting.WachCoordinates.total_exponent_le_eight_hundred l hl G (gPar G S η) h j (ellMax cuts arcLen) (rrPar l n H₁ H₂ cuts : ℝ) (kapPar l (gPar G S η) h (ellMax cuts arcLen) : ℝ) hj hGg hg1 hgh hell hrr hkap`.

Establish `heq : (ePar l n j (gPar G S η) h H₁ H₂ cuts arcLen : ℝ) = Formalism.TruncatedSeriesCounting.WachCoordinates.eE l (gPar G S η) h j (ellMax cuts arcLen) (rrPar l n H₁ H₂ cuts : ℝ) (kapPar l (gPar G S η) h (ellMax cuts arcLen) : ℝ)`. Unfold `ePar initialExponentBound Formalism.TruncatedSeriesCounting.WachCoordinates.eE Formalism.TruncatedSeriesCounting.WachCoordinates.a0E`. Rewrite using `[sigPar_eq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[heq]`. Conclude with `hE`.
-/
theorem thmEBound_holds : ThmEBound 800 := by
  intro l hlp hl2 n _ j G S η h ty cuts arcLen H₁ H₂ hcuts hgh hH hHG
  have hl : 3 ≤ l := by
    have := hlp.two_le
    omega
  have hl' : (3 : ℝ) ≤ l := by exact_mod_cast hl
  obtain ⟨hne, hj, harc, -, -⟩ := hcuts
  have hg1 : 1 ≤ gPar G S η := le_max_right _ _
  have hGg : G ≤ gPar G S η :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have hh1 : 1 ≤ h := le_trans hg1 hgh
  have hell : 1 ≤ ellMax cuts arcLen := by
    obtain ⟨c, hc⟩ := hne
    exact le_trans (harc c hc).1 (Finset.le_sup (f := arcLen) hc)
  have hlog : 0 ≤ Real.logb l h := by
    apply Real.logb_nonneg (by linarith)
    exact_mod_cast hh1
  have hrr : ((rrPar l n H₁ H₂ cuts : ℕ) : ℝ) ≤
      20 * ((G : ℝ) / l + (h : ℝ) / ((l : ℝ) - 1) ^ (j + 1) + Real.logb l h + 1) := by
    unfold rrPar
    apply cast_sup_le
    · have : 0 ≤ (h : ℝ) / ((l : ℝ) - 1) ^ (j + 1) := by
        apply div_nonneg (by positivity); apply pow_nonneg; linarith
      positivity
    · intro c hc
      rw [Nat.cast_max]
      apply max_le
      · exact rF_le l hl n H₁ G h j c hh1 (fun x => (hH x).1) fun k h1 h2 => (hHG c hc k h1 h2).1
      · exact rF_le l hl n H₂ G h j c hh1 (fun x => (hH x).2) fun k h1 h2 => (hHG c hc k h1 h2).2
  have hkap : ((kapPar l (gPar G S η) h (ellMax cuts arcLen) : ℕ) : ℝ) ≤
      (ellMax cuts arcLen : ℝ) + 20 * (gPar G S η : ℝ) * (1 + (ellMax cuts arcLen : ℝ)) +
        5 * (4 * (gPar G S η : ℝ) / ((l : ℝ) - 1) + Real.logb l (2 * h)) := by
    unfold kapPar
    apply cast_sup_le
    · have h1 : 0 ≤ Real.logb l (2 * (h : ℝ)) := by
        apply Real.logb_nonneg (by linarith)
        have : (1 : ℝ) ≤ h := by exact_mod_cast hh1
        linarith
      have h2 : 0 ≤ 4 * (gPar G S η : ℝ) / ((l : ℝ) - 1) := by
        apply div_nonneg (by positivity); linarith
      positivity
    · intro w hw
      rw [Finset.mem_product, Finset.mem_product] at hw
      exact vPP1_le l hlp (by omega) _ _ _ _ _ _ hw.1 hw.2.1 hw.2.2
  have hE := Formalism.TruncatedSeriesCounting.WachCoordinates.total_exponent_le_eight_hundred l hl G (gPar G S η) h j (ellMax cuts arcLen)
    (rrPar l n H₁ H₂ cuts : ℝ) (kapPar l (gPar G S η) h (ellMax cuts arcLen) : ℝ)
    hj hGg hg1 hgh hell hrr hkap
  have heq : (ePar l n j (gPar G S η) h H₁ H₂ cuts arcLen : ℝ) =
      Formalism.TruncatedSeriesCounting.WachCoordinates.eE l (gPar G S η) h j (ellMax cuts arcLen) (rrPar l n H₁ H₂ cuts : ℝ)
        (kapPar l (gPar G S η) h (ellMax cuts arcLen) : ℝ) := by
    unfold ePar initialExponentBound Formalism.TruncatedSeriesCounting.WachCoordinates.eE Formalism.TruncatedSeriesCounting.WachCoordinates.a0E
    rw [sigPar_eq]
    push_cast
    ring
  rw [heq]
  exact hE

end Formalism.MainNotions.WachCoordinates

namespace Formalism.MainNotions.WachCoordinates

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section KillerBridge

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

/- English proof (translation)
Rewrite using `[← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]`. Both sides reduce to the same expression.
-/
theorem γD_smulA (T : LocLat G Qp LL O) (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]
  rfl

def Pi0Stable : Prop := ∀ g : W.Gam, ∃ u ∈ W.AΔ, W.γA g W.π₀ = W.π₀ * u

/- English proof (translation)
Use `⟨(W.N T).smul_mem _ (W.N_Γ T g y hy.1), fun δ hδ => ?_⟩` and prove the remaining obligations. Rewrite using `[γD_smulA, hu δ hδ, ← W.γD_mul, mul_comm, W.γD_mul, hy.2 δ hδ]`.
-/
theorem NΔ_stable (T : LocLat G Qp LL O) (g : W.Gam) (u : LetA O n) (hu : u ∈ W.AΔ)
    (y : W.DD T) (hy : y ∈ W.NΔ T) : u • W.γD T g y ∈ W.NΔ T := by
  refine ⟨(W.N T).smul_mem _ (W.N_Γ T g y hy.1), fun δ hδ => ?_⟩
  rw [γD_smulA, hu δ hδ, ← W.γD_mul, mul_comm, W.γD_mul, hy.2 δ hδ]

def piN (T : LocLat G Qp LL O) : Submodule O (W.DD T) where
  carrier := mulSet W T W.π₀ (W.NΔ T)
  zero_mem' := ⟨0, (W.NΔ T).zero_mem, (smul_zero _).symm⟩
  add_mem' := by
    rintro _ _ ⟨y₁, h₁, rfl⟩ ⟨y₂, h₂, rfl⟩
    exact ⟨y₁ + y₂, (W.NΔ T).add_mem h₁ h₂, (smul_add _ _ _).symm⟩
  smul_mem' := by
    rintro c _ ⟨y, h, rfl⟩
    exact ⟨c • y, (W.NΔ T).smul_mem c h, smul_comm _ _ _⟩

/- English proof (translation)
Introduce `T c γ χ ell JS w _ _ _ hw`. Establish `hst : ∀ u ∈ piN W T, W.γD T γ u ∈ piN W T`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Take `⟨u, hu, hπ⟩` from `h γ`. Use `⟨u • W.γD T γ y, NΔ_stable W T γ u hu y hy, ?_⟩` and prove the remaining obligations.

Rewrite using `[γD_smulA, hπ, mul_smul]`. Conclude with `Formalism.ExponentWindows.aeval_sub_eval_one_smul_mem O (W.DD T) (W.γD T γ) (piN W T) hst (PPO PD.p χ ell JS) w hw`.
-/
theorem killerModule_of_stable (h : Pi0Stable W) : KillerMod W := by
  intro T c γ χ ell JS w _ _ _ hw
  have hst : ∀ u ∈ piN W T, W.γD T γ u ∈ piN W T := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨u, hu, hπ⟩ := h γ
    refine ⟨u • W.γD T γ y, NΔ_stable W T γ u hu y hy, ?_⟩
    rw [γD_smulA, hπ, mul_smul]
  exact Formalism.ExponentWindows.aeval_sub_eval_one_smul_mem O (W.DD T) (W.γD T γ) (piN W T) hst (PPO PD.p χ ell JS) w hw

end KillerBridge

/- English proof (translation)
Assemble the required witnesses or components as `⟨Formalism.WindowSums.arc_KillerVal, Formalism.WindowSums.arc_KillerKills, fun l _ K LL hc h5 => killerModule_of_stable _ (h l K LL hc h5)⟩`.
-/
theorem killer_conditions_of_stable (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (h : AtCaseA fun l _ K LL h => Pi0Stable ((HW l).W K 1 LL h.2.2)) : adm11 D HW F :=
  ⟨Formalism.WindowSums.arc_KillerVal, Formalism.WindowSums.arc_KillerKills,
    fun l _ K LL hc h5 => killerModule_of_stable _ (h l K LL hc h5)⟩

end Formalism.MainNotions.WachCoordinates

namespace Formalism.MainNotions.WachCoordinates

def tyA {n : ℕ} (b η : ℕ) (typ : ZMod n → Bool) (sz : ZMod n → ℕ) (i : ZMod n) : LT :=
  if b ≤ sz i ∧ sz i ≤ b + η then (if typ i then LT.up (sz i) else LT.down (sz i)) else LT.thin

def hA {n : ℕ} (b w S η : ℕ) (sz : ZMod n → ℕ) : ℕ := max (hCor b w S η sz) 1

def bdA {n : ℕ} (b w S η : ℕ) (sz : ZMod n → ℕ) (i : ZMod n) : ℕ :=
  if b ≤ sz i ∧ sz i ≤ b + η then hA b w S η sz else w + S + η

/- English proof (translation)
Unfold `gPar`. Use linear arithmetic over natural numbers and integers.
-/
theorem gPar_A (w S η : ℕ) : gPar (w + S + η) S η = max (w + S + η) 1 := by
  unfold gPar; omega

/- English proof (translation)
Unfold `hCor`. Conclude with `if_pos hex`.
-/
theorem hCor_pos {n : ℕ} {b w S η : ℕ} {sz : ZMod n → ℕ} (hex : ∃ i, b ≤ sz i ∧ sz i ≤ b + η) :
    hCor b w S η sz = b + η + S := by
  unfold hCor; exact if_pos hex

/- English proof (translation)
Unfold `hCor`. Conclude with `if_neg hex`.
-/
theorem hCor_neg {n : ℕ} {b w S η : ℕ} {sz : ZMod n → ℕ} (hex : ¬ ∃ i, b ≤ sz i ∧ sz i ≤ b + η) :
    hCor b w S η sz = w + S + η := by
  unfold hCor; exact if_neg hex

/- English proof (translation)
Unfold `tyA`. Distinguish the cases in `ht : b ≤ sz i ∧ sz i ≤ b + η`. Rewrite using `[if_pos ht]`. Apply the tactic sequence `cases typ i <;> simp [LT.thick, ht]`. Rewrite using `[if_neg ht]`.

Simplify using `[LT.thick, ht]`.
-/
theorem tyA_thick {n : ℕ} (b η : ℕ) (typ : ZMod n → Bool) (sz : ZMod n → ℕ) (i : ZMod n) :
    (tyA b η typ sz i).thick = true ↔ (b ≤ sz i ∧ sz i ≤ b + η) := by
  unfold tyA
  by_cases ht : b ≤ sz i ∧ sz i ≤ b + η
  · rw [if_pos ht]
    cases typ i <;> simp [LT.thick, ht]
  · rw [if_neg ht]
    simp [LT.thick, ht]

/- English proof (translation)
Unfold `tyA`. Conclude with `if_neg ht`.
-/
theorem tyA_thin {n : ℕ} {b η : ℕ} {typ : ZMod n → Bool} {sz : ZMod n → ℕ} {i : ZMod n}
    (ht : ¬ (b ≤ sz i ∧ sz i ≤ b + η)) : tyA b η typ sz i = LT.thin := by
  unfold tyA; exact if_neg ht

/- English proof (translation)
Unfold `tyA at h`. Distinguish the cases in `ht : b ≤ sz i ∧ sz i ≤ b + η`. Use `⟨ht, ?_⟩` and prove the remaining obligations. Rewrite `h` using `[if_pos ht]`. Generalize the expression as in `typ i = t at h`.

Apply the tactic sequence `cases t <;> simpa using h`. Rewrite `h` using `[if_neg ht]`. Simplify using `at h`.
-/
theorem tyA_size {n : ℕ} {b η : ℕ} {typ : ZMod n → Bool} {sz : ZMod n → ℕ} {i : ZMod n} {x : ℕ}
    (h : tyA b η typ sz i = LT.up x ∨ tyA b η typ sz i = LT.down x) :
    (b ≤ sz i ∧ sz i ≤ b + η) ∧ sz i = x := by
  unfold tyA at h
  by_cases ht : b ≤ sz i ∧ sz i ≤ b + η
  · refine ⟨ht, ?_⟩
    rw [if_pos ht] at h
    generalize typ i = t at h
    cases t <;> simpa using h
  · rw [if_neg ht] at h
    simp at h

/- English proof (translation)
Unfold `tyA`. Distinguish the cases in `ht : b ≤ sz i ∧ sz i ≤ b + η`. Rewrite using `[if_pos ht]`. Generalize the expression as in `typ i = t`. Introduce `x hx`.

Apply the tactic sequence `cases t <;> simpa [LT.win] using hx`. Rewrite using `[if_neg ht]`. Establish `hw : sz i ≤ w` using `h.resolve_left ht`. Generalize the expression as in `typ i = t`. Introduce `x hx`.

Apply the tactic sequence `cases t <;>`. Simplify using `only [Bool.false_eq_true, if_false, if_true, LT.win, Set.mem_union, Set.mem_Icc] at hx ⊢`. Use `push_cast`. Use linear arithmetic over natural numbers and integers.
-/
theorem winA_subset {n : ℕ} (b w S η : ℕ) (typ : ZMod n → Bool) (sz : ZMod n → ℕ) (i : ZMod n)
    (h : Thick b η sz i ∨ sz i ≤ w) :
    (if typ i then (LT.up (sz i)).win 0 S η else (LT.down (sz i)).win 0 S η) ⊆
      (tyA b η typ sz i).win (w + S + η) S η := by
  unfold tyA
  by_cases ht : b ≤ sz i ∧ sz i ≤ b + η
  · rw [if_pos ht]
    generalize typ i = t
    intro x hx
    cases t <;> simpa [LT.win] using hx
  · rw [if_neg ht]
    have hw : sz i ≤ w := h.resolve_left ht
    generalize typ i = t
    intro x hx
    cases t <;>
      · simp only [Bool.false_eq_true, if_false, if_true, LT.win, Set.mem_union, Set.mem_Icc] at hx ⊢
        push_cast
        omega

/- English proof (translation)
Unfold `tyA bdA`. Distinguish the cases in `ht : b ≤ sz i ∧ sz i ≤ b + η`. Rewrite using `[if_pos ht, if_pos ht]`. Establish `h1 : b + η + S ≤ hA b w S η sz`. Unfold `hA`.

Rewrite using `[hCor_pos ⟨i, ht⟩]`. Conclude with `le_max_left _ _`. Generalize the expression as in `typ i = t`. Introduce `x hx`. Apply the tactic sequence `cases t <;>`.

Simplify using `only [Bool.false_eq_true, if_false, if_true, LT.win, Set.mem_union, Set.mem_Icc] at hx ⊢`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg ht, if_neg ht]`. Introduce `x hx`. Simplify `hx` using `[LT.win]`.
-/
theorem tyA_win_subset {n : ℕ} (b w S η : ℕ) (typ : ZMod n → Bool) (sz : ZMod n → ℕ) (i : ZMod n) :
    (tyA b η typ sz i).win (w + S + η) S η ⊆
      Set.Icc (-(bdA b w S η sz i : ℤ)) (bdA b w S η sz i) := by
  unfold tyA bdA
  by_cases ht : b ≤ sz i ∧ sz i ≤ b + η
  · rw [if_pos ht, if_pos ht]
    have h1 : b + η + S ≤ hA b w S η sz := by
      unfold hA; rw [hCor_pos ⟨i, ht⟩]; exact le_max_left _ _
    generalize typ i = t
    intro x hx
    cases t <;>
      · simp only [Bool.false_eq_true, if_false, if_true, LT.win, Set.mem_union, Set.mem_Icc] at hx ⊢
        omega
  · rw [if_neg ht, if_neg ht]
    intro x hx
    simpa [LT.win] using hx

/- English proof (translation)
Introduce `a ha k hk1 hkj hak k' hk1' hkj'`. Break down `h a ha with h0 | ⟨d, hd1, hdj, -, hrest⟩` into its components or cases. Conclude with `absurd hak (h0 k hk1 hkj)`. Establish `hkd : k = d`. Assume the negation of the conclusion as `hne`.

Conclude with `hrest k hk1 (by omega) hne hak`. Substitute `hkd` using the available equality. Use `hrest (k + k') (by omega) (by omega) (by omega)` as an intermediate fact. Rewrite `this` using `[Nat.cast_add, ← sub_sub]`. Then use the resulting hypothesis.
-/
theorem clusters_sep {n : ℕ} {j : ℕ} {thick : ZMod n → Prop} (h : Clusters j thick) :
    ∀ a : ZMod n, thick a → ∀ k : ℕ, 1 ≤ k → k ≤ j → thick (a - k) →
      ∀ k' : ℕ, 1 ≤ k' → k' ≤ j → ¬ thick (a - k - k') := by
  intro a ha k hk1 hkj hak k' hk1' hkj'
  rcases h a ha with h0 | ⟨d, hd1, hdj, -, hrest⟩
  · exact absurd hak (h0 k hk1 hkj)
  · have hkd : k = d := by
      by_contra hne
      exact hrest k hk1 (by omega) hne hak
    subst hkd
    have := hrest (k + k') (by omega) (by omega) (by omega)
    rwa [Nat.cast_add, ← sub_sub] at this

def AprimeConfig (C : ℝ) : Prop :=
  ∀ l : ℕ, 11 ≤ l →
    ∀ (n : ℕ) [NeZero n] (j b w S η : ℕ) (typ : ZMod n → Bool) (sz : ZMod n → ℕ),
      1 ≤ j → j + 1 ≤ n → (∀ i, Thick b η sz i ∨ sz i ≤ w) →
      C * ((j : ℝ) + 1) * (((w + S + η : ℕ) : ℝ) + 1) ≤ b → Clusters j (Thick b η sz) →
      ∃ (cuts : Finset (ZMod n)) (arcLen : ZMod n → ℕ),
        gPar (w + S + η) S η ≤ hA b w S η sz ∧
        SizesOK (gPar (w + S + η) S η) S (hA b w S η sz) (tyA b η typ sz) ∧
        CutsOK n j (tyA b η typ sz) cuts arcLen ∧
        ThickLe2 (tyA b η typ sz) cuts arcLen ∧
        ellMax cuts arcLen ≤ 3 * j + 1 ∧
        ∀ H₁ H₂ : ZMod n → ℕ,
          (∀ i, H₁ i ≤ 2 * hA b w S η sz ∧ H₂ i ≤ 2 * hA b w S η sz) →
          (∀ i, ¬ Thick b η sz i → H₁ i ≤ 2 * (w + S + η) ∧ H₂ i ≤ 2 * (w + S + η)) →
          WordOK l (initialExponentBound l n j (gPar (w + S + η) S η) (hA b w S η sz) H₁ H₂ cuts arcLen)
            (tyA b η typ sz) cuts arcLen

/- English proof (translation)
Take `⟨C₀, hC₀, hcore⟩` from `Formalism.ExponentWindows.exists_cuts_exponent_bounds`. Use `⟨max C₀ 1, le_max_right _ _, ?_⟩` and prove the remaining obligations. Introduce `l hl n _ j b w S η typ sz hj hn hthick hCb hclus`. Establish `hjR : (1 : ℝ) ≤ j` using `by exact_mod_cast hj`. Establish `hGpos : (0 : ℝ) ≤ ((w + S + η : ℕ) : ℝ) + 1` using `by positivity`.

Establish `hCb0 : C₀ * ((j : ℝ) + 1) * (((w + S + η : ℕ) : ℝ) + 1) ≤ b`. Use `le_trans ?_ hCb` and prove the remaining obligations. Apply `mul_le_mul_of_nonneg_right _ hGpos` to reduce the goal to its premises. Apply `mul_le_mul_of_nonneg_right (le_max_left _ _)` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hb2R : (2 : ℝ) * (((w + S + η : ℕ) : ℝ) + 1) ≤ b`. Use `le_trans ?_ hCb` and prove the remaining obligations. Apply `mul_le_mul_of_nonneg_right _ hGpos` to reduce the goal to its premises. Establish `h1 : (1 : ℝ) ≤ max C₀ 1` using `le_max_right _ _`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hb2 : 2 * (w + S + η + 1) ≤ b` using `by exact_mod_cast hb2R`. Take `⟨cuts, ell, hne, hc⟩` from `hcore l hl n j sz b w S η (20 * (((w + S + η : ℕ) : ℝ) / l + ((b + η + S : ℕ) : ℝ) / ((l : ℝ) - 1) ^ (j + 1) + Real.logb l (b + η + S : ℕ) + 1)) hj hn hthick hCb0 (clusters_sep hclus) le_rfl`. Establish `hg : gPar (w + S + η) S η = max (w + S + η) 1` using `gPar_A w S η`. Establish `hhA : ∀ i, (b ≤ sz i ∧ sz i ≤ b + η) → hA b w S η sz = b + η + S`. Introduce `i hi`.

Unfold `hA`. Rewrite using `[hCor_pos ⟨i, hi⟩]`. Use linear arithmetic over natural numbers and integers. Establish `hell : ellMax cuts ell ≤ 3 * j + 1` using `Finset.sup_le fun c hc' => (hc c hc').2.2.1`. Use `⟨cuts, ell, ?_, ?_, ?_, ?_, hell, ?_⟩` and prove the remaining obligations.

Rewrite using `[hg]`. Distinguish the cases in `hex : ∃ i, b ≤ sz i ∧ sz i ≤ b + η`. Take `⟨i, hi⟩` from `hex`. Rewrite using `[hhA i hi]`. Use linear arithmetic over natural numbers and integers.

Unfold `hA`. Rewrite using `[hCor_neg hex]`. Introduce `i`. Distinguish the cases in `ht : b ≤ sz i ∧ sz i ≤ b + η`. Use `left`.

Rewrite using `[hg, hhA i ht]`. Unfold `tyA`. Rewrite using `[if_pos ht]`. Generalize the expression as in `typ i = t`. Apply the tactic sequence `cases t <;> simp only [Bool.false_eq_true, if_false, if_true, LT.ok, LT.size] <;> omega`.

Use `right`. Conclude with `tyA_thin ht`. Use `⟨hne, hj, ?_, fun c hc' => (hc c hc').2.1, ?_⟩` and prove the remaining obligations. Introduce `c hc'`. Take `⟨-, hjl, -, hmem, hno, -⟩` from `hc c hc'`.

Use `⟨le_trans hj hjl, ?_, hmem, hno⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Establish `h0` using `hno n (Nat.pos_of_ne_zero (NeZero.ne n)) (by omega)`. Rewrite `h0` using `[ZMod.natCast_self, sub_zero]`. Conclude with `h0 hc'`.

Introduce `c hc' k hk1 hkj`. Conclude with `tyA_thin ((hc c hc').1 k hk1 hkj)`. Introduce `c hc'`. Establish `hcard` using `(hc c hc').2.2.2.2.2.1`. Establish `heq : thickLv (tyA b η typ sz) ell c = (Finset.range (ell c)).filter (fun k : ℕ => b ≤ sz (c - (k : ZMod n)) ∧ sz (c - (k : ZMod n)) ≤ b + η)` using `Finset.filter_congr fun s _ => tyA_thick b η typ sz _`.

Unfold `ro`. Rewrite using `[heq]`. Conclude with `hcard`. Introduce `H₁ H₂ hH hHG c hc' s₀ s₁ hs01 hs1 b₀ b₁`. Take `⟨-, -, -, -, -, -, -, hword⟩` from `hc c hc'`.

Establish `key : ∀ x y : ℕ, (tyA b η typ sz (c - (s₁ : ZMod n)) = LT.up x ∨ tyA b η typ sz (c - (s₁ : ZMod n)) = LT.down x) → (tyA b η typ sz (c - (s₀ : ZMod n)) = LT.up y ∨ tyA b η typ sz (c - (s₀ : ZMod n)) = LT.down y) → y < l * x ∧ 2 * y ≤ l * x ∧ 2 * initialExponentBound l n j (gPar (w …`. Introduce `x y hx hy`. Take `⟨ht1, rfl⟩` from `tyA_size hx`. Take `⟨ht0, rfl⟩` from `tyA_size hy`. Take `⟨w1, w2, w3⟩` from `hword s₁ s₀ hs1 hs01 ht1 ht0`.

Use `⟨by exact_mod_cast w1, ?_, ?_⟩` and prove the remaining obligations. Establish `: (2 : ℝ) * sz (c - (s₀ : ZMod n)) ≤ l * sz (c - (s₁ : ZMod n))` using `by linarith`. Conclude with `this` after adjusting the coercions. Establish `hl3 : 3 ≤ l` using `by omega`. Establish `hl' : (3 : ℝ) ≤ l` using `by exact_mod_cast hl3`.

Establish `hh` using `hhA _ ht1`. Establish `hh1 : 1 ≤ b + η + S` using `by omega`. Establish `hrr : ((rrPar l n H₁ H₂ cuts : ℕ) : ℝ) ≤ 20 * (((w + S + η : ℕ) : ℝ) / l + ((b + η + S : ℕ) : ℝ) / ((l : ℝ) - 1) ^ (j + 1) + Real.logb l (b + η + S : ℕ) + 1)`. Unfold `rrPar`. Apply `cast_sup_le` to reduce the goal to its premises.

Establish `h1 : 0 ≤ ((b + η + S : ℕ) : ℝ) / ((l : ℝ) - 1) ^ (j + 1)`. Apply `div_nonneg (by positivity); apply pow_nonneg; linarith` to reduce the goal to its premises. Establish `h2 : 0 ≤ Real.logb l ((b + η + S : ℕ) : ℝ)`. Apply `Real.logb_nonneg (by linarith)` to reduce the goal to its premises. Conclude with `hh1` after adjusting the coercions.

Check the signs of the components of the expression. Introduce `c₁ hc₁`. Rewrite using `[Nat.cast_max]`. Apply `max_le` to reduce the goal to its premises. Conclude with `rF_le l hl3 n H₁ (w + S + η) (b + η + S) j c₁ hh1 (fun x => hh ▸ (hH x).1) (fun k h1 h2 => (hHG _ ((hc c₁ hc₁).1 k h1 h2)).1)`.

Conclude with `rF_le l hl3 n H₂ (w + S + η) (b + η + S) j c₁ hh1 (fun x => hh ▸ (hH x).2) (fun k h1 h2 => (hHG _ ((hc c₁ hc₁).1 k h1 h2)).2)`. Establish `hellR : ((ellMax cuts ell : ℕ) : ℝ) ≤ ((3 * j + 1 : ℕ) : ℝ)` using `by exact_mod_cast hell`. Establish `ha : ((initialExponentBound l n j (gPar (w + S + η) S η) (hA b w S η sz) H₁ H₂ cuts ell : ℕ) : ℝ) ≤ Formalism.TruncatedSeriesCounting.WachCoordinates.a0E l (max (w + S + η) 1) (b + η + S) j (3 * j + 1) (20 * (((w + S + η : ℕ) : ℝ) / l + ((b + η + S : ℕ) : ℝ) / ((l : ℝ) - 1) ^ (j …`. Unfold `initialExponentBound Formalism.TruncatedSeriesCounting.WachCoordinates.a0E`. Rewrite using `[hg, hh, sigPar_eq]`.

Move the coercions through the operations in `at hellR hrr ⊢`. Establish `hgn : (0 : ℝ) ≤ 2 * max ((w : ℝ) + S + η) 1` using `by positivity`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hellR hgn]`. Establish `: (2 : ℝ) * (initialExponentBound l n j (gPar (w + S + η) S η) (hA b w S η sz) H₁ H₂ cuts ell : ℕ) < sz (c - (s₁ : ZMod n))` using `by linarith`. Conclude with `this` after adjusting the coercions.

Use `⟨fun h1 h0 => (key b₁ b₀ (Or.inr h1) (Or.inl h0)).1, fun h1 h0 => ?_⟩` and prove the remaining obligations. Conclude with `(key b₁ b₀ (Or.inl h1) (Or.inr h0)).2`.
-/
theorem aprimeConfig_holds : ∃ C : ℝ, 1 ≤ C ∧ AprimeConfig C := by
  obtain ⟨C₀, hC₀, hcore⟩ := Formalism.ExponentWindows.exists_cuts_exponent_bounds
  refine ⟨max C₀ 1, le_max_right _ _, ?_⟩
  intro l hl n _ j b w S η typ sz hj hn hthick hCb hclus
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hGpos : (0 : ℝ) ≤ ((w + S + η : ℕ) : ℝ) + 1 := by positivity
  have hCb0 : C₀ * ((j : ℝ) + 1) * (((w + S + η : ℕ) : ℝ) + 1) ≤ b := by
    refine le_trans ?_ hCb
    apply mul_le_mul_of_nonneg_right _ hGpos
    apply mul_le_mul_of_nonneg_right (le_max_left _ _)
    linarith
  have hb2R : (2 : ℝ) * (((w + S + η : ℕ) : ℝ) + 1) ≤ b := by
    refine le_trans ?_ hCb
    apply mul_le_mul_of_nonneg_right _ hGpos
    have h1 : (1 : ℝ) ≤ max C₀ 1 := le_max_right _ _
    nlinarith
  have hb2 : 2 * (w + S + η + 1) ≤ b := by exact_mod_cast hb2R
  obtain ⟨cuts, ell, hne, hc⟩ := hcore l hl n j sz b w S η
    (20 * (((w + S + η : ℕ) : ℝ) / l + ((b + η + S : ℕ) : ℝ) / ((l : ℝ) - 1) ^ (j + 1) +
        Real.logb l (b + η + S : ℕ) + 1)) hj hn hthick hCb0 (clusters_sep hclus) le_rfl
  have hg : gPar (w + S + η) S η = max (w + S + η) 1 := gPar_A w S η
  have hhA : ∀ i, (b ≤ sz i ∧ sz i ≤ b + η) → hA b w S η sz = b + η + S := by
    intro i hi
    unfold hA; rw [hCor_pos ⟨i, hi⟩]; omega
  have hell : ellMax cuts ell ≤ 3 * j + 1 := Finset.sup_le fun c hc' => (hc c hc').2.2.1
  refine ⟨cuts, ell, ?_, ?_, ?_, ?_, hell, ?_⟩
  · rw [hg]
    by_cases hex : ∃ i, b ≤ sz i ∧ sz i ≤ b + η
    · obtain ⟨i, hi⟩ := hex
      rw [hhA i hi]; omega
    · unfold hA; rw [hCor_neg hex]
  · intro i
    by_cases ht : b ≤ sz i ∧ sz i ≤ b + η
    · left
      rw [hg, hhA i ht]
      unfold tyA
      rw [if_pos ht]
      generalize typ i = t
      cases t <;> simp only [Bool.false_eq_true, if_false, if_true, LT.ok, LT.size] <;> omega
    · right
      exact tyA_thin ht
  · refine ⟨hne, hj, ?_, fun c hc' => (hc c hc').2.1, ?_⟩
    · intro c hc'
      obtain ⟨-, hjl, -, hmem, hno, -⟩ := hc c hc'
      refine ⟨le_trans hj hjl, ?_, hmem, hno⟩
      by_contra hlt
      have h0 := hno n (Nat.pos_of_ne_zero (NeZero.ne n)) (by omega)
      rw [ZMod.natCast_self, sub_zero] at h0
      exact h0 hc'
    · intro c hc' k hk1 hkj
      exact tyA_thin ((hc c hc').1 k hk1 hkj)
  · intro c hc'
    have hcard := (hc c hc').2.2.2.2.2.1
    have heq : thickLv (tyA b η typ sz) ell c = (Finset.range (ell c)).filter
        (fun k : ℕ => b ≤ sz (c - (k : ZMod n)) ∧ sz (c - (k : ZMod n)) ≤ b + η) :=
      Finset.filter_congr fun s _ => tyA_thick b η typ sz _
    unfold ro
    rw [heq]
    exact hcard
  · intro H₁ H₂ hH hHG c hc' s₀ s₁ hs01 hs1 b₀ b₁
    obtain ⟨-, -, -, -, -, -, -, hword⟩ := hc c hc'
    have key : ∀ x y : ℕ,
        (tyA b η typ sz (c - (s₁ : ZMod n)) = LT.up x ∨ tyA b η typ sz (c - (s₁ : ZMod n)) = LT.down x) →
        (tyA b η typ sz (c - (s₀ : ZMod n)) = LT.up y ∨ tyA b η typ sz (c - (s₀ : ZMod n)) = LT.down y) →
        y < l * x ∧ 2 * y ≤ l * x ∧
          2 * initialExponentBound l n j (gPar (w + S + η) S η) (hA b w S η sz) H₁ H₂ cuts ell < x := by
      intro x y hx hy
      obtain ⟨ht1, rfl⟩ := tyA_size hx
      obtain ⟨ht0, rfl⟩ := tyA_size hy
      obtain ⟨w1, w2, w3⟩ := hword s₁ s₀ hs1 hs01 ht1 ht0
      refine ⟨by exact_mod_cast w1, ?_, ?_⟩
      · have : (2 : ℝ) * sz (c - (s₀ : ZMod n)) ≤ l * sz (c - (s₁ : ZMod n)) := by linarith
        exact_mod_cast this
      · have hl3 : 3 ≤ l := by omega
        have hl' : (3 : ℝ) ≤ l := by exact_mod_cast hl3
        have hh := hhA _ ht1
        have hh1 : 1 ≤ b + η + S := by omega
        have hrr : ((rrPar l n H₁ H₂ cuts : ℕ) : ℝ) ≤
            20 * (((w + S + η : ℕ) : ℝ) / l + ((b + η + S : ℕ) : ℝ) / ((l : ℝ) - 1) ^ (j + 1) +
              Real.logb l (b + η + S : ℕ) + 1) := by
          unfold rrPar
          apply cast_sup_le
          · have h1 : 0 ≤ ((b + η + S : ℕ) : ℝ) / ((l : ℝ) - 1) ^ (j + 1) := by
              apply div_nonneg (by positivity); apply pow_nonneg; linarith
            have h2 : 0 ≤ Real.logb l ((b + η + S : ℕ) : ℝ) := by
              apply Real.logb_nonneg (by linarith)
              exact_mod_cast hh1
            positivity
          · intro c₁ hc₁
            rw [Nat.cast_max]
            apply max_le
            · exact rF_le l hl3 n H₁ (w + S + η) (b + η + S) j c₁ hh1
                (fun x => hh ▸ (hH x).1)
                (fun k h1 h2 => (hHG _ ((hc c₁ hc₁).1 k h1 h2)).1)
            · exact rF_le l hl3 n H₂ (w + S + η) (b + η + S) j c₁ hh1
                (fun x => hh ▸ (hH x).2)
                (fun k h1 h2 => (hHG _ ((hc c₁ hc₁).1 k h1 h2)).2)
        have hellR : ((ellMax cuts ell : ℕ) : ℝ) ≤ ((3 * j + 1 : ℕ) : ℝ) := by exact_mod_cast hell
        have ha : ((initialExponentBound l n j (gPar (w + S + η) S η) (hA b w S η sz) H₁ H₂ cuts ell : ℕ) : ℝ) ≤
            Formalism.TruncatedSeriesCounting.WachCoordinates.a0E l (max (w + S + η) 1) (b + η + S) j (3 * j + 1)
              (20 * (((w + S + η : ℕ) : ℝ) / l +
                ((b + η + S : ℕ) : ℝ) / ((l : ℝ) - 1) ^ (j + 1) +
                Real.logb l (b + η + S : ℕ) + 1)) := by
          unfold initialExponentBound Formalism.TruncatedSeriesCounting.WachCoordinates.a0E
          rw [hg, hh, sigPar_eq]
          push_cast at hellR hrr ⊢
          have hgn : (0 : ℝ) ≤ 2 * max ((w : ℝ) + S + η) 1 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hellR hgn]
        have : (2 : ℝ) * (initialExponentBound l n j (gPar (w + S + η) S η) (hA b w S η sz) H₁ H₂ cuts ell : ℕ) <
            sz (c - (s₁ : ZMod n)) := by linarith
        exact_mod_cast this
    refine ⟨fun h1 h0 => (key b₁ b₀ (Or.inr h1) (Or.inl h0)).1, fun h1 h0 => ?_⟩
    exact (key b₁ b₀ (Or.inl h1) (Or.inr h0)).2

/- English proof (translation)
Unfold `bdA`. Use `split_ifs`. Conclude with `le_rfl`. Conclude with `hG`.
-/
theorem bdA_le {n : ℕ} {b w S η : ℕ} {sz : ZMod n → ℕ} (hG : w + S + η ≤ hA b w S η sz)
    (i : ZMod n) : bdA b w S η sz i ≤ hA b w S η sz := by
  unfold bdA
  split_ifs
  · exact le_rfl
  · exact hG

/- English proof (translation)
Unfold `bdA`. Conclude with `if_neg ht`.
-/
theorem bdA_thin {n : ℕ} {b w S η : ℕ} {sz : ZMod n → ℕ} {i : ZMod n}
    (ht : ¬ Thick b η sz i) : bdA b w S η sz i = w + S + η := by
  unfold bdA; exact if_neg ht

/- English proof (translation)
Establish `h0` using `hE l hlp (by omega) n j (w + S + η) S η (hA b w S η sz) (tyA b η typ sz) cuts arcLen H₁ H₂ hcuts hg hH (fun c hc k hk1 hkj => hHG _ (fun ht => by`. Establish `h1` using `hcuts.2.2.2.2 c hc k hk1 hkj`. Establish `h2` using `(tyA_thick b η typ sz (c + (k : ZMod n))).2 ht`. Rewrite `h2` using `[h1]`. Simplify using `[LT.thick] at h2))`.

Use `le_trans h0 ?_` and prove the remaining obligations. Establish `hl' : (11 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hgle : ((gPar (w + S + η) S η : ℕ) : ℝ) ≤ ((w + S + η : ℕ) : ℝ) + 1`. Establish `: gPar (w + S + η) S η ≤ w + S + η + 1` using `by rw [gPar_A]; omega`. Conclude with `this` after adjusting the coercions.

Establish `hellR : ((ellMax cuts arcLen : ℕ) : ℝ) ≤ 3 * ((j : ℝ) + 1)`. Establish `: ellMax cuts arcLen ≤ 3 * (j + 1)` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `hprod : ((gPar (w + S + η) S η : ℕ) : ℝ) * ((ellMax cuts arcLen : ℕ) : ℝ) ≤ 3 * ((((w + S + η : ℕ) : ℝ) + 1) * ((j : ℝ) + 1))`. Combine the equalities or inequalities in the displayed calculation.

Establish `hone : (1 : ℝ) ≤ (((w + S + η : ℕ) : ℝ) + 1) * ((j : ℝ) + 1)`. Establish `h1 : (0 : ℝ) ≤ ((w + S + η : ℕ) : ℝ)` using `by positivity`. Establish `h2 : (0 : ℝ) ≤ (j : ℝ)` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `hX1 : (1 : ℝ) ≤ ((l : ℝ) - 1) ^ (j + 1)` using `one_le_pow₀ (by linarith)`.

Establish `hAdef : hA b w S η sz = max (hCor b w S η sz) 1` using `rfl`. Rewrite using `[hAdef]`. Generalize the expression as in `hCor b w S η sz = hc`. Generalize the expression as in `((l : ℝ) - 1) ^ (j + 1) = X at hX1 ⊢`. Establish `hlog : Real.logb l ((max hc 1 : ℕ) : ℝ) = Real.logb l (hc : ℝ)`.

Break down `Nat.eq_zero_or_pos hc with h | h` into its components or cases. Rewrite using `[h]`. Simplify using the standard rewrite rules. Rewrite using `[max_eq_left h]`. Establish `hlog0 : 0 ≤ Real.logb l (hc : ℝ)`.

Break down `Nat.eq_zero_or_pos hc with h | h` into its components or cases. Rewrite using `[h]`. Simplify using the standard rewrite rules. Apply `Real.logb_nonneg (by linarith)` to reduce the goal to its premises. Conclude with `h` after adjusting the coercions.

Establish `hAle : ((max hc 1 : ℕ) : ℝ) ≤ (hc : ℝ) + 1`. Establish `: max hc 1 ≤ hc + 1` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `hdiv : ((max hc 1 : ℕ) : ℝ) / X ≤ (hc : ℝ) / X + 1`. Combine the equalities or inequalities in the displayed calculation.

Establish `: 1 / X ≤ 1` using `by rw [div_le_one (by linarith)]; exact hX1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hq : 0 ≤ (hc : ℝ) / X` using `div_nonneg (by positivity) (by linarith)`. Rewrite using `[hlog]`. Establish `hsum : ((max hc 1 : ℕ) : ℝ) / X + ((gPar (w + S + η) S η : ℕ) : ℝ) * ((ellMax cuts arcLen : ℕ) : ℝ) + Real.logb l (hc : ℝ) ≤ 4 * ((hc : ℝ) / X + (((w + S + η : ℕ) : ℝ) + 1) * ((j : ℝ) + 1) + Real.logb l (hc : ℝ))`.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.
-/
theorem eA_le (C₁ : ℝ) (hC₁ : 0 ≤ C₁) (hE : ThmEBound C₁) (l : ℕ) (hlp : l.Prime) (hl : 11 ≤ l)
    (n : ℕ) [NeZero n] (j b w S η : ℕ) (typ : ZMod n → Bool) (sz : ZMod n → ℕ)
    (cuts : Finset (ZMod n)) (arcLen : ZMod n → ℕ) (H₁ H₂ : ZMod n → ℕ)
    (hg : gPar (w + S + η) S η ≤ hA b w S η sz)
    (hcuts : CutsOK n j (tyA b η typ sz) cuts arcLen) (hell : ellMax cuts arcLen ≤ 3 * j + 1)
    (hH : ∀ i, H₁ i ≤ 2 * hA b w S η sz ∧ H₂ i ≤ 2 * hA b w S η sz)
    (hHG : ∀ i, ¬ Thick b η sz i → H₁ i ≤ 2 * (w + S + η) ∧ H₂ i ≤ 2 * (w + S + η)) :
    (ePar l n j (gPar (w + S + η) S η) (hA b w S η sz) H₁ H₂ cuts arcLen : ℝ) ≤
      4 * C₁ * ((hCor b w S η sz : ℝ) / ((l : ℝ) - 1) ^ (j + 1) +
        (((w + S + η : ℕ) : ℝ) + 1) * ((j : ℝ) + 1) + Real.logb l (hCor b w S η sz : ℝ)) := by
  have h0 := hE l hlp (by omega) n j (w + S + η) S η (hA b w S η sz) (tyA b η typ sz) cuts arcLen
    H₁ H₂ hcuts hg hH
    (fun c hc k hk1 hkj => hHG _ (fun ht => by
      have h1 := hcuts.2.2.2.2 c hc k hk1 hkj
      have h2 := (tyA_thick b η typ sz (c + (k : ZMod n))).2 ht
      rw [h1] at h2
      simp [LT.thick] at h2))
  refine le_trans h0 ?_
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  have hgle : ((gPar (w + S + η) S η : ℕ) : ℝ) ≤ ((w + S + η : ℕ) : ℝ) + 1 := by
    have : gPar (w + S + η) S η ≤ w + S + η + 1 := by rw [gPar_A]; omega
    exact_mod_cast this
  have hellR : ((ellMax cuts arcLen : ℕ) : ℝ) ≤ 3 * ((j : ℝ) + 1) := by
    have : ellMax cuts arcLen ≤ 3 * (j + 1) := by omega
    exact_mod_cast this
  have hprod : ((gPar (w + S + η) S η : ℕ) : ℝ) * ((ellMax cuts arcLen : ℕ) : ℝ) ≤
      3 * ((((w + S + η : ℕ) : ℝ) + 1) * ((j : ℝ) + 1)) := by
    calc ((gPar (w + S + η) S η : ℕ) : ℝ) * ((ellMax cuts arcLen : ℕ) : ℝ)
        ≤ (((w + S + η : ℕ) : ℝ) + 1) * (3 * ((j : ℝ) + 1)) :=
          mul_le_mul hgle hellR (by positivity) (by positivity)
      _ = 3 * ((((w + S + η : ℕ) : ℝ) + 1) * ((j : ℝ) + 1)) := by ring
  have hone : (1 : ℝ) ≤ (((w + S + η : ℕ) : ℝ) + 1) * ((j : ℝ) + 1) := by
    have h1 : (0 : ℝ) ≤ ((w + S + η : ℕ) : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ (j : ℝ) := by positivity
    nlinarith
  have hX1 : (1 : ℝ) ≤ ((l : ℝ) - 1) ^ (j + 1) := one_le_pow₀ (by linarith)
  have hAdef : hA b w S η sz = max (hCor b w S η sz) 1 := rfl
  rw [hAdef]
  generalize hCor b w S η sz = hc
  generalize ((l : ℝ) - 1) ^ (j + 1) = X at hX1 ⊢
  have hlog : Real.logb l ((max hc 1 : ℕ) : ℝ) = Real.logb l (hc : ℝ) := by
    rcases Nat.eq_zero_or_pos hc with h | h
    · rw [h]; simp
    · rw [max_eq_left h]
  have hlog0 : 0 ≤ Real.logb l (hc : ℝ) := by
    rcases Nat.eq_zero_or_pos hc with h | h
    · rw [h]; simp
    · apply Real.logb_nonneg (by linarith)
      exact_mod_cast h
  have hAle : ((max hc 1 : ℕ) : ℝ) ≤ (hc : ℝ) + 1 := by
    have : max hc 1 ≤ hc + 1 := by omega
    exact_mod_cast this
  have hdiv : ((max hc 1 : ℕ) : ℝ) / X ≤ (hc : ℝ) / X + 1 := by
    calc ((max hc 1 : ℕ) : ℝ) / X ≤ ((hc : ℝ) + 1) / X :=
          div_le_div_of_nonneg_right hAle (by linarith)
      _ = (hc : ℝ) / X + 1 / X := add_div _ _ _
      _ ≤ (hc : ℝ) / X + 1 := by
          have : 1 / X ≤ 1 := by rw [div_le_one (by linarith)]; exact hX1
          linarith
  have hq : 0 ≤ (hc : ℝ) / X := div_nonneg (by positivity) (by linarith)
  rw [hlog]
  have hsum : ((max hc 1 : ℕ) : ℝ) / X +
      ((gPar (w + S + η) S η : ℕ) : ℝ) * ((ellMax cuts arcLen : ℕ) : ℝ) + Real.logb l (hc : ℝ) ≤
      4 * ((hc : ℝ) / X + (((w + S + η : ℕ) : ℝ) + 1) * ((j : ℝ) + 1) + Real.logb l (hc : ℝ)) := by
    linarith
  calc C₁ * (((max hc 1 : ℕ) : ℝ) / X +
        ((gPar (w + S + η) S η : ℕ) : ℝ) * ((ellMax cuts arcLen : ℕ) : ℝ) + Real.logb l (hc : ℝ))
      ≤ C₁ * (4 * ((hc : ℝ) / X + (((w + S + η : ℕ) : ℝ) + 1) * ((j : ℝ) + 1) +
          Real.logb l (hc : ℝ))) := mul_le_mul_of_nonneg_left hsum hC₁
    _ = 4 * C₁ * ((hc : ℝ) / X + (((w + S + η : ℕ) : ℝ) + 1) * ((j : ℝ) + 1) +
          Real.logb l (hc : ℝ)) := by ring

section Apply

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]

/- English proof (translation)
Introduce `τ hτ a ha` and use `hA (h τ hτ a ha)`.
-/
theorem JumpsAtE.mono {T : LocLat G Qp LL O} {n : ℕ} {emb : ZMod n → (K₀ →ₐ[Qp] LL)} {i : ZMod n}
    {A A' : Set ℤ} (h : JumpsAtE PD T emb i A) (hA : A ⊆ A') : JumpsAtE PD T emb i A' :=
  fun τ hτ a ha => hA (h τ hτ a ha)

variable [Fintype (K →ₐ[Qp] LL)]

/- English proof (translation)
Introduce `n _ emb v hLift hLet hp T₁ T₂ F hGood hT₁ hT₂ hOn hsub b w S η j typ sz hj hn hwin hthick hCb hclus`. Take `⟨cuts, arcLen, hg, hsz, hcuts, hle2, hell, hword⟩` from `hcfg PD.p hp n j b w S η typ sz hj hn hthick hCb hclus`. Establish `hGh : w + S + η ≤ hA b w S η sz` using `le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hg`. Establish `hkind : KindJumps PD T₁ emb (w + S + η) S η (tyA b η typ sz)` using `fun i => (hwin i).mono PD (winA_subset b w S η typ sz i (hthick i))`. Establish `hbd₁ : ∀ i, JumpsAtE PD T₁ emb i (Set.Icc (-(bdA b w S η sz i : ℤ)) (bdA b w S η sz i))` using `fun i => (hkind i).mono PD (tyA_win_subset b w S η typ sz i)`.

Establish `hall : ∀ τ : K →ₐ[Qp] LL, JumpsInV PD T₁.ρ τ (Set.Icc (-(hA b w S η sz : ℤ)) (hA b w S η sz))`. Introduce `τ a ha`. Take `⟨i, hi⟩` from `hLet.2.2.2.1.2 (τ.comp (IsScalarTower.toAlgHom Qp K₀ K))`. Establish `h1` using `hbd₁ i τ hi.symm a ha`. Establish `h2 : bdA b w S η sz i ≤ hA b w S η sz` using `bdA_le hGh i`.

Rewrite `h1`, the goal using `[Set.mem_Icc]`. Use linear arithmetic over natural numbers and integers. Establish `hH : ∀ i, (bdA b w S η sz + bdA b w S η sz) i ≤ 2 * hA b w S η sz ∧ (bdA b w S η sz + bdA b w S η sz) i ≤ 2 * hA b w S η sz`. Introduce `i`. Establish `h2 : bdA b w S η sz i ≤ hA b w S η sz` using `bdA_le hGh i`.

Simplify using `only [Pi.add_apply]`. Use linear arithmetic over natural numbers and integers. Establish `hHG : ∀ i, ¬ Thick b η sz i → (bdA b w S η sz + bdA b w S η sz) i ≤ 2 * (w + S + η) ∧ (bdA b w S η sz + bdA b w S η sz) i ≤ 2 * (w + S + η)`. Introduce `i ht`. Simplify using `only [Pi.add_apply, bdA_thin ht]`.

Use linear arithmetic over natural numbers and integers. Use `⟨_, hLift hLet (by omega) T₁ T₂ F hGood hT₁ hT₂ hOn j (w + S + η) S η (hA b w S η sz) (tyA b η typ sz) cuts arcLen (bdA b w S η sz) (bdA b w S η sz) (bdA b w S η sz) (bdA b w S η sz) hkind hall hg hsz hcuts hle2 hbd₁ (fun i => hsub i _ (hbd₁ i)) (hword _ _ hH hHG), ?_⟩` and prove the remaining obligations. Conclude with `eA_le C₁ hC₁ hE PD.p PD.hp hp n j b w S η typ sz cuts arcLen _ _ hg hcuts hell hH hHG`.
-/
theorem liftA_of_thmE (C : ℝ) (hcfg : AprimeConfig C) (C₁ : ℝ) (hC₁ : 0 ≤ C₁)
    (hE : ThmEBound C₁) :
    ∀ (n : ℕ) [NeZero n] (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (v : AddValuation LL (WithTop ℚ)),
    ThmELiftAt PD (O := O) n emb v → Letters PD LL v emb → 11 ≤ PD.p →
    ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L),
      GoodCoeffs (K := K) (Qp := Qp) (LL := LL) (O := O) (V := T₁.V) →
      CrysLat PD T₁ → CrysLat PD T₂ → F.Onto →
      (∀ (i : ZMod n) (A : Set ℤ), JumpsAtE PD T₁ emb i A → JumpsAtE PD T₂ emb i A) →
      ∀ (b w S η j : ℕ) (typ : ZMod n → Bool) (sz : ZMod n → ℕ),
        1 ≤ j → j + 1 ≤ n →
        (∀ i, JumpsAtE PD T₁ emb i (if typ i then (LT.up (sz i)).win 0 S η
          else (LT.down (sz i)).win 0 S η)) →
        (∀ i, Thick b η sz i ∨ sz i ≤ w) →
        C * ((j : ℝ) + 1) * (((w + S + η : ℕ) : ℝ) + 1) ≤ b →
        Clusters j (Thick b η sz) →
        ∃ e : ℕ, F.LiftF PD e ∧ (e : ℝ) ≤ 4 * C₁ *
          ((hCor b w S η sz : ℝ) / ((PD.p : ℝ) - 1) ^ (j + 1) +
            (((w + S + η : ℕ) : ℝ) + 1) * ((j : ℝ) + 1) + Real.logb PD.p (hCor b w S η sz : ℝ)) := by
  intro n _ emb v hLift hLet hp T₁ T₂ F hGood hT₁ hT₂ hOn hsub b w S η j typ sz hj hn hwin
    hthick hCb hclus
  obtain ⟨cuts, arcLen, hg, hsz, hcuts, hle2, hell, hword⟩ :=
    hcfg PD.p hp n j b w S η typ sz hj hn hthick hCb hclus
  have hGh : w + S + η ≤ hA b w S η sz :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hg
  have hkind : KindJumps PD T₁ emb (w + S + η) S η (tyA b η typ sz) := fun i =>
    (hwin i).mono PD (winA_subset b w S η typ sz i (hthick i))
  have hbd₁ : ∀ i, JumpsAtE PD T₁ emb i
      (Set.Icc (-(bdA b w S η sz i : ℤ)) (bdA b w S η sz i)) := fun i =>
    (hkind i).mono PD (tyA_win_subset b w S η typ sz i)
  have hall : ∀ τ : K →ₐ[Qp] LL, JumpsInV PD T₁.ρ τ
      (Set.Icc (-(hA b w S η sz : ℤ)) (hA b w S η sz)) := by
    intro τ a ha
    obtain ⟨i, hi⟩ := hLet.2.2.2.1.2 (τ.comp (IsScalarTower.toAlgHom Qp K₀ K))
    have h1 := hbd₁ i τ hi.symm a ha
    have h2 : bdA b w S η sz i ≤ hA b w S η sz := bdA_le hGh i
    rw [Set.mem_Icc] at h1 ⊢
    omega
  have hH : ∀ i, (bdA b w S η sz + bdA b w S η sz) i ≤ 2 * hA b w S η sz ∧
      (bdA b w S η sz + bdA b w S η sz) i ≤ 2 * hA b w S η sz := by
    intro i
    have h2 : bdA b w S η sz i ≤ hA b w S η sz := bdA_le hGh i
    simp only [Pi.add_apply]
    omega
  have hHG : ∀ i, ¬ Thick b η sz i → (bdA b w S η sz + bdA b w S η sz) i ≤ 2 * (w + S + η) ∧
      (bdA b w S η sz + bdA b w S η sz) i ≤ 2 * (w + S + η) := by
    intro i ht
    simp only [Pi.add_apply, bdA_thin ht]
    omega
  refine ⟨_, hLift hLet (by omega) T₁ T₂ F hGood hT₁ hT₂ hOn j (w + S + η) S η (hA b w S η sz)
    (tyA b η typ sz) cuts arcLen (bdA b w S η sz) (bdA b w S η sz) (bdA b w S η sz)
    (bdA b w S η sz) hkind hall hg hsz hcuts hle2 hbd₁ (fun i => hsub i _ (hbd₁ i))
    (hword _ _ hH hHG), ?_⟩
  exact eA_le C₁ hC₁ hE PD.p PD.hp hp n j b w S η typ sz cuts arcLen _ _ hg hcuts hell hH hHG

end Apply

end Formalism.MainNotions.WachCoordinates

namespace Formalism.MainNotions.WachCoordinates

section CorA

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Module

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]

def JumpsSub (O : Type) [CommRing O] [Algebra O LL] {n : ℕ} (emb : ZMod n → (K₀ →ₐ[Qp] LL)) : Prop :=
  ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), CrysLat PD T₁ → CrysLat PD T₂ → F.Onto →
    ∀ (i : ZMod n) (A : Set ℤ), JumpsAtE PD T₁ emb i A → JumpsAtE PD T₂ emb i A

variable [Fintype (K →ₐ[Qp] LL)]

/- English proof (translation)
Introduce `hLet hp T₁ T₂ F hGood hT₁ hT₂ hOn r b w S η j typ sz hr hj hn hwin hthick hCb hclus`. Establish `hjR : (0 : ℝ) ≤ (j : ℝ) + 1` using `by positivity`. Establish `hGR : (0 : ℝ) ≤ ((w + S + η : ℕ) : ℝ) + 1` using `by positivity`. Establish `hCb' : C * ((j : ℝ) + 1) * (((w + S + η : ℕ) : ℝ) + 1) ≤ b` using `le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hjR) hGR) hCb`. Take `⟨e, hL, he⟩` from `liftA_of_thmE PD C hcfg C₁ hC₁ hE n emb v hLift hLet hp T₁ T₂ F hGood hT₁ hT₂ hOn (hsub T₁ T₂ F hT₁ hT₂ hOn) b w S η j typ sz hj hn hwin hthick hCb' hclus`.

Take `⟨gens, hspan, hcard⟩` from `hgen hLet.1 T₂ hT₂.2.2.2`. Take `⟨k, hk⟩` from `hk`. Take `⟨mm, k', h1, h2, h3⟩` from `Formalism.MainNotions.LocalTheoryWindows.colLeR_of_liftF PD F gens _ e k hk hspan hcard hL`. Use `⟨mm, k', h1, h2, le_trans h3 (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg k'))⟩` and prove the remaining obligations. Establish `hpR : (1 : ℝ) < PD.p`.

Establish `: (11 : ℝ) ≤ PD.p` using `by exact_mod_cast hp`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set X : ℝ := (hCor b w S η sz : ℝ) / ((PD.p : ℝ) - 1) ^ (j + 1) + (((w + S + η : ℕ) : ℝ) + 1) * ((j : ℝ) + 1) + Real.logb PD.p (hCor b w S η sz : ℝ) with hX`. Establish `hlog : 0 ≤ Real.logb PD.p (hCor b w S η sz : ℝ)`. Break down `Nat.eq_zero_or_pos (hCor b w S η sz) with h0 | h0` into its components or cases.

Rewrite using `[h0]`. Simplify using the standard rewrite rules. Conclude with `Real.logb_nonneg hpR (by exact_mod_cast h0)`. Establish `hX0 : 0 ≤ X`. Establish `: 0 ≤ (hCor b w S η sz : ℝ) / ((PD.p : ℝ) - 1) ^ (j + 1)` using `div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith) _)`.

Check the signs of the components of the expression. Rewrite using `[← hLet.2.2.1, hr]`. Use `push_cast`. Establish `hnr : (0 : ℝ) ≤ ((n : ℝ) + 1) * r` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem corAAt_of (C : ℝ) (hcfg : AprimeConfig C) (C₁ : ℝ) (hC₁ : 0 ≤ C₁) (hE : ThmEBound C₁)
    (n : ℕ) [NeZero n] (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (v : AddValuation LL (WithTop ℚ))
    (hLift : ThmELiftAt PD (O := O) n emb v) (hsub : JumpsSub PD O emb)
    (hgen : Formalism.MainNotions.LocalTheoryWindows.H1fGeneratorBound PD LL O) (hk : ∃ k : ℕ, lenOl PD (O := O) = (k : ℕ∞)) :
    CorAAt PD (O := O) n emb v (max C (4 * C₁)) := by
  intro hLet hp T₁ T₂ F hGood hT₁ hT₂ hOn r b w S η j typ sz hr hj hn hwin hthick hCb hclus
  have hjR : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
  have hGR : (0 : ℝ) ≤ ((w + S + η : ℕ) : ℝ) + 1 := by positivity
  have hCb' : C * ((j : ℝ) + 1) * (((w + S + η : ℕ) : ℝ) + 1) ≤ b :=
    le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hjR) hGR) hCb
  obtain ⟨e, hL, he⟩ := liftA_of_thmE PD C hcfg C₁ hC₁ hE n emb v hLift hLet hp T₁ T₂ F hGood hT₁
    hT₂ hOn (hsub T₁ T₂ F hT₁ hT₂ hOn) b w S η j typ sz hj hn hwin hthick hCb' hclus
  obtain ⟨gens, hspan, hcard⟩ := hgen hLet.1 T₂ hT₂.2.2.2
  obtain ⟨k, hk⟩ := hk
  obtain ⟨mm, k', h1, h2, h3⟩ := Formalism.MainNotions.LocalTheoryWindows.colLeR_of_liftF PD F gens _ e k hk hspan hcard hL
  refine ⟨mm, k', h1, h2, le_trans h3 (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg k'))⟩
  have hpR : (1 : ℝ) < PD.p := by
    have : (11 : ℝ) ≤ PD.p := by exact_mod_cast hp
    linarith
  set X : ℝ := (hCor b w S η sz : ℝ) / ((PD.p : ℝ) - 1) ^ (j + 1) +
    (((w + S + η : ℕ) : ℝ) + 1) * ((j : ℝ) + 1) + Real.logb PD.p (hCor b w S η sz : ℝ) with hX
  have hlog : 0 ≤ Real.logb PD.p (hCor b w S η sz : ℝ) := by
    rcases Nat.eq_zero_or_pos (hCor b w S η sz) with h0 | h0
    · rw [h0]; simp
    · exact Real.logb_nonneg hpR (by exact_mod_cast h0)
  have hX0 : 0 ≤ X := by
    have : 0 ≤ (hCor b w S η sz : ℝ) / ((PD.p : ℝ) - 1) ^ (j + 1) :=
      div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith) _)
    positivity
  rw [← hLet.2.2.1, hr]
  push_cast
  have hnr : (0 : ℝ) ≤ ((n : ℝ) + 1) * r := by positivity
  calc ((n : ℝ) + 1) * r * e ≤ ((n : ℝ) + 1) * r * (4 * C₁ * X) :=
        mul_le_mul_of_nonneg_left he hnr
    _ = 4 * C₁ * (((n : ℝ) + 1) * r * X) := by ring
    _ ≤ max C (4 * C₁) * (((n : ℝ) + 1) * r * X) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg hnr hX0)
    _ = max C (4 * C₁) * ((n : ℝ) + 1) * r * X := by ring

end CorA

section RecordA

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

def JumpsSubL (LT : LocTheory) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (n : ℕ) [NeZero n]
    (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)), JumpsSub ((LT l).PD K) ↥(OL LL) emb

/- English proof (translation)
Take `⟨C, hC, hcfg⟩` from `aprimeConfig_holds`. Use `⟨C, hC, fun D C₁ hC₁ h1 hgen hsub l _ K LL n _ emb => ?_⟩` and prove the remaining obligations. Use `haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2`. Use `letI : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Fintype.ofFinite _`. Conclude with `corAAt_of _ C hcfg C₁ hC₁ h1.2 n emb _ (h1.1 l K LL n emb) (hsub l K LL n emb) (hgen l K LL) (Formalism.MainNotions.LocalTheoryWindows.lenOl_finite (D.loc l) K LL)`.
-/
theorem corollary_of_Theorem_E : ∃ C : ℝ, 1 ≤ C ∧ ∀ (D : D7) (C₁ : ℝ), 0 ≤ C₁ → Conclusion1 D C₁ →
    Formalism.MainNotions.LocalTheoryWindows.H1fGeneratorBoundAll D.loc → JumpsSubL D.loc → Conclusion2 D (max C (4 * C₁)) := by
  obtain ⟨C, hC, hcfg⟩ := aprimeConfig_holds
  refine ⟨C, hC, fun D C₁ hC₁ h1 hgen hsub l _ K LL n _ emb => ?_⟩
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  letI : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Fintype.ofFinite _
  exact corAAt_of _ C hcfg C₁ hC₁ h1.2 n emb _ (h1.1 l K LL n emb) (hsub l K LL n emb)
    (hgen l K LL) (Formalism.MainNotions.LocalTheoryWindows.lenOl_finite (D.loc l) K LL)

end RecordA

end Formalism.MainNotions.WachCoordinates
