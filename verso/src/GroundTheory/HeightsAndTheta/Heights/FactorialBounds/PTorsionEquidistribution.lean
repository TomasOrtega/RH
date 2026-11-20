import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Metric Set Topology

noncomputable section

namespace TorsionEquidistribution

/- English proof (translation)
The claim follows from `(AddCircle.coe_eq_zero_iff 1).2 ⟨k, by simp⟩`.
-/
theorem coe_intCast_eq_zero (k : ℤ) : ((k : ℝ) : AddCircle (1 : ℝ)) = 0 :=
  (AddCircle.coe_eq_zero_iff 1).2 ⟨k, by simp⟩

/- English proof (translation)
Take `⟨t, rfl⟩` from `QuotientAddGroup.mk_surjective y`. Establish `hts : (QuotientAddGroup.mk t : AddCircle (1 : ℝ)) = ((t - round t : ℝ) : AddCircle (1 : ℝ))`. Rewrite using `[AddCircle.coe_sub, coe_intCast_eq_zero, sub_zero]`. Establish `hns : ‖((t - round t : ℝ) : AddCircle (1 : ℝ))‖ = |t - round t|`. Rewrite using `[← hts]`.

Conclude with `UnitAddCircle.norm_eq`. Rewrite `hy`, `hn`, the goal using `[hts]`. Rewrite `hn` using `[hns]`. Rewrite `hy` using `[← AddCircle.coe_nsmul, AddCircle.coe_eq_zero_iff]`. Take `⟨k, hk⟩` from `hy`.

Establish `hm' : (0 : ℝ) < m` using `Nat.cast_pos.2 hm`. Establish `hk' : (k : ℝ) = m * (t - round t)` using `by simpa using hk`. Establish `habs : |(k : ℝ)| < 1`. Rewrite using `[hk', abs_mul, abs_of_pos hm']`. Combine the equalities or inequalities in the displayed calculation.

Establish `hk0 : k = 0` using `Int.abs_lt_one_iff.1 (by exact_mod_cast habs)`. Establish `hs0 : t - round t = 0`. Rewrite `hk'` using `[hk0, Int.cast_zero]`. Break down `mul_eq_zero.1 hk'.symm with h | h` into its components or cases. Conclude with `absurd h hm'.ne'`.

Conclude with `h`. Rewrite using `[hs0]`. Both sides reduce to the same expression.
-/
theorem eq_zero_of_nsmul_eq_zero_of_norm_lt {m : ℕ} (hm : 0 < m) {y : AddCircle (1 : ℝ)}
    (hy : m • y = 0) (hn : ‖y‖ < 1 / m) : y = 0 := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective y
  have hts : (QuotientAddGroup.mk t : AddCircle (1 : ℝ)) = ((t - round t : ℝ) : AddCircle (1 : ℝ)) := by
    rw [AddCircle.coe_sub, coe_intCast_eq_zero, sub_zero]
  have hns : ‖((t - round t : ℝ) : AddCircle (1 : ℝ))‖ = |t - round t| := by
    rw [← hts]; exact UnitAddCircle.norm_eq
  rw [hts] at hy hn ⊢
  rw [hns] at hn
  rw [← AddCircle.coe_nsmul, AddCircle.coe_eq_zero_iff] at hy
  obtain ⟨k, hk⟩ := hy
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hk' : (k : ℝ) = m * (t - round t) := by simpa using hk
  have habs : |(k : ℝ)| < 1 := by
    rw [hk', abs_mul, abs_of_pos hm']
    calc (m : ℝ) * |t - round t| < m * (1 / m) := mul_lt_mul_of_pos_left hn hm'
      _ = 1 := by field_simp
  have hk0 : k = 0 := Int.abs_lt_one_iff.1 (by exact_mod_cast habs)
  have hs0 : t - round t = 0 := by
    rw [hk0, Int.cast_zero] at hk'
    rcases mul_eq_zero.1 hk'.symm with h | h
    · exact absurd h hm'.ne'
    · exact h
  rw [hs0]; rfl

/- English proof (translation)
Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_le]`. Apply `hxy` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Establish `hi : ‖x i - y i‖ < 1 / m`.

Rewrite using `[← dist_eq_norm]`. Conclude with `lt_of_le_of_lt (dist_le_pi_dist x y i) h`. Establish `hx' : m • x = 0` using `hx`. Establish `hy' : m • y = 0` using `hy`. Establish `h0 : m • (x i - y i) = 0`.

Establish `h1` using `congrFun hx' i`. Establish `h2` using `congrFun hy' i`. Simplify using `only [Pi.smul_apply, Pi.zero_apply] at h1 h2`. Rewrite using `[smul_sub, h1, h2, sub_zero]`. Conclude with `sub_eq_zero.1 (eq_zero_of_nsmul_eq_zero_of_norm_lt hm h0 hi)`.
-/
theorem one_div_le_dist {n m : ℕ} (hm : 0 < m) {x y : Fin n → AddCircle (1 : ℝ)}
    (hx : x ∈ torusTorsion n m) (hy : y ∈ torusTorsion n m) (hxy : x ≠ y) :
    1 / (m : ℝ) ≤ dist x y := by
  by_contra h
  rw [not_le] at h
  apply hxy
  funext i
  have hi : ‖x i - y i‖ < 1 / m := by
    rw [← dist_eq_norm]; exact lt_of_le_of_lt (dist_le_pi_dist x y i) h
  have hx' : m • x = 0 := hx
  have hy' : m • y = 0 := hy
  have h0 : m • (x i - y i) = 0 := by
    have h1 := congrFun hx' i
    have h2 := congrFun hy' i
    simp only [Pi.smul_apply, Pi.zero_apply] at h1 h2
    rw [smul_sub, h1, h2, sub_zero]
  exact sub_eq_zero.1 (eq_zero_of_nsmul_eq_zero_of_norm_lt hm h0 hi)

def gridPoint (n m : ℕ) (j : Fin n → ℤ) : Fin n → AddCircle (1 : ℝ) :=
  fun i => (((j i : ℝ) / m : ℝ) : AddCircle (1 : ℝ))

/- English proof (translation)
Use `show m • gridPoint n m j = 0`. Use function extensionality and compare the values at `i`. Simplify using `only [gridPoint, Pi.smul_apply, Pi.zero_apply]`. Rewrite using `[← AddCircle.coe_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ (Nat.cast_pos.2 hm).ne']`. Conclude with `coe_intCast_eq_zero _`.
-/
theorem gridPoint_mem {n m : ℕ} (hm : 0 < m) (j : Fin n → ℤ) :
    gridPoint n m j ∈ torusTorsion n m := by
  show m • gridPoint n m j = 0
  funext i
  simp only [gridPoint, Pi.smul_apply, Pi.zero_apply]
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul,
    mul_div_cancel₀ _ (Nat.cast_pos.2 hm).ne']
  exact coe_intCast_eq_zero _

/- English proof (translation)
Establish `hx' : m • x = 0` using `hx`. Establish `hm' : (0 : ℝ) < m` using `Nat.cast_pos.2 hm`. Establish `key : ∀ i, ∃ k : ℤ, 0 ≤ k ∧ k < m ∧ ((((k : ℝ) / m : ℝ)) : AddCircle (1 : ℝ)) = x i`. Introduce `i`. Take `⟨t, ht⟩` from `QuotientAddGroup.mk_surjective (x i)`.

Establish `h1 : m • x i = 0` using `by simpa using congrFun hx' i`. Rewrite `h1` using `[← ht]`. Express the relevant statement in the definitionally equal form `m • ((t : ℝ) : AddCircle (1 : ℝ)) = 0 at h1`. Rewrite `h1` using `[← AddCircle.coe_nsmul, AddCircle.coe_eq_zero_iff]`. Take `⟨q, hq⟩` from `h1`.

Establish `hq' : (q : ℝ) = m * t` using `by simpa using hq`. Use `⟨q % m, Int.emod_nonneg _ (by exact_mod_cast hm.ne'), Int.emod_lt_of_pos _ (by exact_mod_cast hm), ?_⟩` and prove the remaining obligations. Establish `hd` using `Int.emod_add_ediv_mul q m`. Establish `hdiv : ((q % (m : ℤ) : ℤ) : ℝ) / m = t - ((q / (m : ℤ) : ℤ) : ℝ)`. Establish `hd' : ((q % (m : ℤ) : ℤ) : ℝ) + ((q / (m : ℤ) : ℤ) : ℝ) * (m : ℝ) = q`.

Conclude with `hd` after adjusting the coercions. Rewrite using `[div_eq_iff hm'.ne']`. Take the linear combination `hd' + hq'`. Rewrite using `[hdiv, AddCircle.coe_sub, coe_intCast_eq_zero, sub_zero, ← ht]`. Use `choose k hk0 hkm hk using key`.

Conclude with `⟨k, Fintype.mem_piFinset.2 fun i => Finset.mem_Ico.2 ⟨hk0 i, hkm i⟩, funext hk⟩`.
-/
theorem exists_gridPoint {n m : ℕ} (hm : 0 < m) {x : Fin n → AddCircle (1 : ℝ)}
    (hx : x ∈ torusTorsion n m) :
    ∃ j ∈ Fintype.piFinset (fun _ : Fin n => Finset.Ico (0 : ℤ) m), gridPoint n m j = x := by
  have hx' : m • x = 0 := hx
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have key : ∀ i, ∃ k : ℤ, 0 ≤ k ∧ k < m ∧
      ((((k : ℝ) / m : ℝ)) : AddCircle (1 : ℝ)) = x i := by
    intro i
    obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective (x i)
    have h1 : m • x i = 0 := by simpa using congrFun hx' i
    rw [← ht] at h1
    change m • ((t : ℝ) : AddCircle (1 : ℝ)) = 0 at h1
    rw [← AddCircle.coe_nsmul, AddCircle.coe_eq_zero_iff] at h1
    obtain ⟨q, hq⟩ := h1
    have hq' : (q : ℝ) = m * t := by simpa using hq
    refine ⟨q % m, Int.emod_nonneg _ (by exact_mod_cast hm.ne'),
      Int.emod_lt_of_pos _ (by exact_mod_cast hm), ?_⟩
    have hd := Int.emod_add_ediv_mul q m
    have hdiv : ((q % (m : ℤ) : ℤ) : ℝ) / m = t - ((q / (m : ℤ) : ℤ) : ℝ) := by
      have hd' : ((q % (m : ℤ) : ℤ) : ℝ) + ((q / (m : ℤ) : ℤ) : ℝ) * (m : ℝ) = q := by
        exact_mod_cast hd
      rw [div_eq_iff hm'.ne']
      linear_combination hd' + hq'
    rw [hdiv, AddCircle.coe_sub, coe_intCast_eq_zero, sub_zero, ← ht]
  choose k hk0 hkm hk using key
  exact ⟨k, Fintype.mem_piFinset.2 fun i => Finset.mem_Ico.2 ⟨hk0 i, hkm i⟩, funext hk⟩

/- English proof (translation)
Introduce `j hj j' hj' h`. Establish `hm' : (0 : ℝ) < m` using `Nat.cast_pos.2 hm`. Use function extensionality and compare the values at `i`. Establish `hji` using `Fintype.mem_piFinset.1 (Finset.mem_coe.1 hj) i`. Establish `hji'` using `Fintype.mem_piFinset.1 (Finset.mem_coe.1 hj') i`.

Establish `h1` using `congrFun h i`. Simplify using `only [gridPoint] at h1`. Rewrite `h1` using `[← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]`. Take `⟨q, hq⟩` from `h1`. Establish `hq' : ((j i - j' i : ℤ) : ℝ) = ((q * m : ℤ) : ℝ)`.

Rewrite `hq` using `[zsmul_eq_mul, mul_one, div_sub_div_same, eq_div_iff hm'.ne']`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hint : j i - j' i = q * m` using `by exact_mod_cast hq'`. Establish `hlt` using `hW i _ hji _ hji'`.

Establish `hmz : (0 : ℤ) < m` using `by exact_mod_cast hm`. Rewrite `hlt` using `[hint, abs_mul, abs_of_pos hmz]`. Establish `hq1 : |q| < 1` using `by nlinarith`. Establish `hq0 : q = 0` using `Int.abs_lt_one_iff.1 hq1`. Rewrite `hint` using `[hq0, zero_mul, sub_eq_zero]`.

Conclude with `hint`.
-/
theorem gridPoint_injOn {n m : ℕ} (hm : 0 < m) {W : Fin n → Finset ℤ}
    (hW : ∀ i, ∀ a ∈ W i, ∀ b ∈ W i, |a - b| < m) :
    InjOn (gridPoint n m) (Fintype.piFinset W : Set (Fin n → ℤ)) := by
  intro j hj j' hj' h
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  funext i
  have hji := Fintype.mem_piFinset.1 (Finset.mem_coe.1 hj) i
  have hji' := Fintype.mem_piFinset.1 (Finset.mem_coe.1 hj') i
  have h1 := congrFun h i
  simp only [gridPoint] at h1
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff] at h1
  obtain ⟨q, hq⟩ := h1
  have hq' : ((j i - j' i : ℤ) : ℝ) = ((q * m : ℤ) : ℝ) := by
    rw [zsmul_eq_mul, mul_one, div_sub_div_same, eq_div_iff hm'.ne'] at hq
    push_cast; linarith
  have hint : j i - j' i = q * m := by exact_mod_cast hq'
  have hlt := hW i _ hji _ hji'
  have hmz : (0 : ℤ) < m := by exact_mod_cast hm
  rw [hint, abs_mul, abs_of_pos hmz] at hlt
  have hq1 : |q| < 1 := by nlinarith
  have hq0 : q = 0 := Int.abs_lt_one_iff.1 hq1
  rw [hq0, zero_mul, sub_eq_zero] at hint
  exact hint

/- English proof (translation)
Rewrite using `[UnitAddCircle.norm_eq]`. Break down `le_or_gt (round t) 0 with h | h` into its components or cases. Establish `h' : (round t : ℝ) ≤ 0` using `by exact_mod_cast h`. Rewrite using `[abs_of_nonneg (by linarith)]; linarith`. Establish `h0 : (1 : ℤ) ≤ round t` using `h`.

Establish `h' : (1 : ℝ) ≤ round t` using `by exact_mod_cast h0`. Rewrite using `[abs_of_nonpos (by linarith)]; linarith`.
-/
theorem quarter_le_norm {t : ℝ} (h1 : 1 / 4 ≤ t) (h2 : t ≤ 3 / 4) :
    (1 / 4 : ℝ) ≤ ‖(t : AddCircle (1 : ℝ))‖ := by
  rw [UnitAddCircle.norm_eq]
  rcases le_or_gt (round t) 0 with h | h
  · have h' : (round t : ℝ) ≤ 0 := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]; linarith
  · have h0 : (1 : ℤ) ≤ round t := h
    have h' : (1 : ℝ) ≤ round t := by exact_mod_cast h0
    rw [abs_of_nonpos (by linarith)]; linarith

/- English proof (translation)
Use `set ε : ENNReal := ENNReal.ofReal ((2 / 3 : ℝ) ^ n / 12) with hε`. Establish `hεpos : 0 < ε` using `ENNReal.ofReal_pos.2 (by positivity)`. Establish `hlim : Tendsto (fun r : ℝ => volume (cthickening r Z)) (𝓝 0) (𝓝 0)`. Use `tendsto_measure_cthickening_of_isClosed (μ := volume) (s := Z) ⟨1, one_pos, measure_ne_top _ _⟩ hZ` as an intermediate fact. Rewrite `this` using `[hZ0]`. Then use the resulting hypothesis.

Establish `hr : Tendsto (fun m : ℕ => (1 / 3 : ℝ) / m) atTop (𝓝 0)` using `tendsto_const_div_atTop_nhds_zero_nat _`. Establish `hev` using `(hlim.comp hr).eventually (gt_mem_nhds hεpos)`. Use `filter_upwards [hev, eventually_ge_atTop 1] with m hvol hm1`. Simplify using `only [Function.comp_apply] at hvol`. Establish `hm : 0 < m` using `hm1`.

Establish `hm' : (0 : ℝ) < m` using `Nat.cast_pos.2 hm`. Use `set r : ℝ := (1 / 3 : ℝ) / m with hrdef`. Establish `hr0 : 0 < r` using `by positivity`. Establish `hTfin : (torusTorsion n m).Finite`. Use `((Fintype.piFinset fun _ : Fin n => Finset.Ico (0 : ℤ) m).finite_toSet.image (gridPoint n m)).subset ?_` and prove the remaining obligations.

Introduce `x hx`. Take `⟨j, hj, rfl⟩` from `exists_gridPoint hm hx`. Conclude with `⟨j, hj, rfl⟩`. Establish `hSfin : (torusTorsion n m ∩ Z).Finite` using `hTfin.subset inter_subset_left`. Use `set F := hSfin.toFinset with hF`.

Establish `hdisj : PairwiseDisjoint (F : Set (Fin n → AddCircle (1 : ℝ))) fun x => closedBall x r`. Introduce `x hx y hy hxy`. Simplify using `only [hF, Set.Finite.coe_toFinset] at hx hy`. Apply `closedBall_disjoint_closedBall` to reduce the goal to its premises. Use `one_div_le_dist hm hx.1 hy.1 hxy` as an intermediate fact.

Establish `h2 : r + r < 1 / m`. Rewrite using `[hrdef]`. Clear the denominators using the available nonvanishing facts. Evaluate the numerical expressions. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hball : ∀ x : Fin n → AddCircle (1 : ℝ), volume (closedBall x r) = ENNReal.ofReal (2 * r) ^ n`. Introduce `x`. Rewrite using `[volume_pi_closedBall _ hr0.le]`. Simplify using `only [AddCircle.volume_closedBall]`. Establish `: min (1 : ℝ) (2 * r) = 2 * r`.

Apply `min_eq_right` to reduce the goal to its premises. Establish `h1 : (1 : ℝ) ≤ m` using `by exact_mod_cast hm1`. Establish `h2 : (1 / 3 : ℝ) / m ≤ 1 / 3` using `div_le_self (by norm_num) h1`. Rewrite using `[hrdef]`. Combine the linear equalities and inequalities to obtain the conclusion.

Simplify using `[this]`. Establish `hsub : (⋃ x ∈ F, closedBall x r) ⊆ cthickening r Z`. Introduce `y hy`. Simplify using `only [mem_iUnion] at hy`. Take `⟨x, hx, hy⟩` from `hy`.

Simplify using `only [hF, Set.Finite.mem_toFinset] at hx`. Conclude with `closedBall_subset_cthickening hx.2 r hy`. Establish `hsum : (F.card : ENNReal) * ENNReal.ofReal (2 * r) ^ n < ε`. Combine the equalities or inequalities in the displayed calculation. Rewrite `hsum` using `[← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), hε, ENNReal.ofReal_lt_ofReal_iff (by positivity)]`.

Establish `hcard : (torusTorsion n m ∩ Z).ncard = F.card`. Rewrite using `[hF, Set.ncard_eq_toFinset_card _ hSfin]`. Rewrite using `[hcard]`. Establish `h2r : 2 * r = (2 / 3) / m` using `by rw [hrdef]; ring`. Rewrite `hsum` using `[h2r, div_pow]`.

Establish `hmn : (0 : ℝ) < (m : ℝ) ^ n` using `by positivity`. Establish `ha : (0 : ℝ) < (2 / 3 : ℝ) ^ n` using `by positivity`. Rewrite `hsum` using `[mul_div_assoc', div_lt_div_iff₀ hmn (by norm_num)]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem eventually_ncard_inter_lt {n : ℕ} (Z : Set (Fin n → AddCircle (1 : ℝ)))
    (hZ : IsClosed Z) (hZ0 : volume Z = 0) :
    ∀ᶠ m : ℕ in atTop, ((torusTorsion n m ∩ Z).ncard : ℝ) * 12 < (m : ℝ) ^ n := by
  set ε : ENNReal := ENNReal.ofReal ((2 / 3 : ℝ) ^ n / 12) with hε
  have hεpos : 0 < ε := ENNReal.ofReal_pos.2 (by positivity)
  have hlim : Tendsto (fun r : ℝ => volume (cthickening r Z)) (𝓝 0) (𝓝 0) := by
    have := tendsto_measure_cthickening_of_isClosed (μ := volume) (s := Z)
      ⟨1, one_pos, measure_ne_top _ _⟩ hZ
    rwa [hZ0] at this
  have hr : Tendsto (fun m : ℕ => (1 / 3 : ℝ) / m) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hev := (hlim.comp hr).eventually (gt_mem_nhds hεpos)
  filter_upwards [hev, eventually_ge_atTop 1] with m hvol hm1
  simp only [Function.comp_apply] at hvol
  have hm : 0 < m := hm1
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  set r : ℝ := (1 / 3 : ℝ) / m with hrdef
  have hr0 : 0 < r := by positivity
  have hTfin : (torusTorsion n m).Finite := by
    refine ((Fintype.piFinset fun _ : Fin n => Finset.Ico (0 : ℤ) m).finite_toSet.image
      (gridPoint n m)).subset ?_
    intro x hx
    obtain ⟨j, hj, rfl⟩ := exists_gridPoint hm hx
    exact ⟨j, hj, rfl⟩
  have hSfin : (torusTorsion n m ∩ Z).Finite := hTfin.subset inter_subset_left
  set F := hSfin.toFinset with hF
  have hdisj : PairwiseDisjoint (F : Set (Fin n → AddCircle (1 : ℝ))) fun x => closedBall x r := by
    intro x hx y hy hxy
    simp only [hF, Set.Finite.coe_toFinset] at hx hy
    apply closedBall_disjoint_closedBall
    have := one_div_le_dist hm hx.1 hy.1 hxy
    have h2 : r + r < 1 / m := by
      rw [hrdef]; field_simp; norm_num
    linarith
  have hball : ∀ x : Fin n → AddCircle (1 : ℝ), volume (closedBall x r) = ENNReal.ofReal (2 * r) ^ n := by
    intro x
    rw [volume_pi_closedBall _ hr0.le]
    simp only [AddCircle.volume_closedBall]
    have : min (1 : ℝ) (2 * r) = 2 * r := by
      apply min_eq_right
      have h1 : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      have h2 : (1 / 3 : ℝ) / m ≤ 1 / 3 := div_le_self (by norm_num) h1
      rw [hrdef]; linarith
    simp [this]
  have hsub : (⋃ x ∈ F, closedBall x r) ⊆ cthickening r Z := by
    intro y hy
    simp only [mem_iUnion] at hy
    obtain ⟨x, hx, hy⟩ := hy
    simp only [hF, Set.Finite.mem_toFinset] at hx
    exact closedBall_subset_cthickening hx.2 r hy
  have hsum : (F.card : ENNReal) * ENNReal.ofReal (2 * r) ^ n < ε := by
    calc (F.card : ENNReal) * ENNReal.ofReal (2 * r) ^ n
        = ∑ x ∈ F, volume (closedBall x r) := by simp [hball]
      _ = volume (⋃ x ∈ F, closedBall x r) :=
          (measure_biUnion_finset hdisj fun _ _ => measurableSet_closedBall).symm
      _ ≤ volume (cthickening r Z) := measure_mono hsub
      _ < ε := hvol
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity), hε,
    ENNReal.ofReal_lt_ofReal_iff (by positivity)] at hsum
  have hcard : (torusTorsion n m ∩ Z).ncard = F.card := by
    rw [hF, Set.ncard_eq_toFinset_card _ hSfin]
  rw [hcard]
  have h2r : 2 * r = (2 / 3) / m := by rw [hrdef]; ring
  rw [h2r, div_pow] at hsum
  have hmn : (0 : ℝ) < (m : ℝ) ^ n := by positivity
  have ha : (0 : ℝ) < (2 / 3 : ℝ) ^ n := by positivity
  rw [mul_div_assoc', div_lt_div_iff₀ hmn (by norm_num)] at hsum
  nlinarith

/- English proof (translation)
Introduce `n hn Z c hZ hZ0 _hc`. Take `⟨k, rfl⟩ : ∃ k, n = k + 1` from `⟨n - 1, by omega⟩`. Use `filter_upwards [eventually_ncard_inter_lt Z hZ hZ0, eventually_ge_atTop 12] with m hz hm12`. Establish `hm : 0 < m` using `by omega`. Establish `hm' : (0 : ℝ) < m` using `Nat.cast_pos.2 hm`.

Establish `hm12' : (12 : ℝ) ≤ m` using `by exact_mod_cast hm12`. Use `set T := torusTorsion (k + 1) m with hT`. Use `set i₀ : Fin (k + 1) := ⟨0, hn⟩ with hi₀`. Use `set S := T ∩ Z with hS`. Use `set G' := {x ∈ T \ Z | (1 / 4 : ℝ) ≤ ‖x i₀ + (c : AddCircle (1 : ℝ))‖} with hG'`.

Express the relevant statement in the definitionally equal form `(T \ Z).ncard ≤ 3 * G'.ncard`. Establish `hTsub : T ⊆ gridPoint (k + 1) m '' (Fintype.piFinset fun _ : Fin (k + 1) => Finset.Ico (0 : ℤ) m)`. Introduce `x hx`. Take `⟨j, hj, rfl⟩` from `exists_gridPoint hm hx`. Conclude with `⟨j, hj, rfl⟩`.

Establish `hTfin : T.Finite` using `((Finset.finite_toSet _).image _).subset hTsub`. Establish `hTcard : T.ncard ≤ m ^ (k + 1)`. Use `(ncard_le_ncard hTsub ((Finset.finite_toSet _).image _)).trans ?_` and prove the remaining obligations. Use `(ncard_image_le (Finset.finite_toSet _)).trans ?_` and prove the remaining obligations. Rewrite using `[ncard_coe_finset, Fintype.card_piFinset]`.

Simplify using `[Int.card_Ico]`. Use `set G := {x ∈ T | (1 / 4 : ℝ) ≤ ‖x i₀ + (c : AddCircle (1 : ℝ))‖} with hG`. Use `set a : ℤ := ⌈(m : ℝ) / 4 - m * c⌉ with ha`. Use `set b : ℤ := ⌊3 * (m : ℝ) / 4 - m * c⌋ with hb`. Establish `ha1 : (m : ℝ) / 4 - m * c ≤ a` using `Int.le_ceil _`.

Establish `ha2 : (a : ℝ) < (m : ℝ) / 4 - m * c + 1` using `Int.ceil_lt_add_one _`. Establish `hb1 : (b : ℝ) ≤ 3 * (m : ℝ) / 4 - m * c` using `Int.floor_le _`. Establish `hb2 : 3 * (m : ℝ) / 4 - m * c < b + 1` using `Int.lt_floor_add_one _`. Use `set W : Fin (k + 1) → Finset ℤ := fun i => if i = i₀ then Finset.Icc a b else Finset.Ico 0 m with hW`. Establish `hWwidth : ∀ i, ∀ u ∈ W i, ∀ v ∈ W i, |u - v| < m`.

Introduce `i u hu v hv`. Distinguish the cases in `hi : i = i₀`. Simplify using `only [hW, hi, if_true, Finset.mem_Icc] at hu hv`. Establish `h1 : ((b - a : ℤ) : ℝ) < m` using `by push_cast; linarith`. Establish `h2 : b - a < m` using `by exact_mod_cast h1`.

Apply the tactic sequence `rw [abs_lt]; constructor <;> omega`. Simplify using `only [hW, hi, if_false, Finset.mem_Ico] at hu hv`. Apply the tactic sequence `rw [abs_lt]; constructor <;> omega`. Establish `hGsub : gridPoint (k + 1) m '' (Fintype.piFinset W) ⊆ G`. Introduce and unpack `_ ⟨j, hj, rfl⟩`.

Use `⟨gridPoint_mem hm j, ?_⟩` and prove the remaining obligations. Establish `hj0` using `Fintype.mem_piFinset.1 (Finset.mem_coe.1 hj) i₀`. Simplify using `only [hW, if_true, Finset.mem_Icc] at hj0`. Establish `hlo : (a : ℝ) ≤ j i₀` using `by exact_mod_cast hj0.1`. Establish `hhi : (j i₀ : ℝ) ≤ b` using `by exact_mod_cast hj0.2`.

Establish `e : gridPoint (k + 1) m j i₀ + (c : AddCircle (1 : ℝ)) = (((j i₀ : ℝ) / m + c : ℝ) : AddCircle (1 : ℝ))`. Rewrite using `[AddCircle.coe_add]`. Both sides reduce to the same expression. Rewrite using `[e]`. Apply `quarter_le_norm` to reduce the goal to its premises.

Establish `h1 : (1 / 4 - c) * m ≤ j i₀` using `by linarith`. Use `(le_div_iff₀ hm').2 h1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1 : (j i₀ : ℝ) ≤ (3 / 4 - c) * m` using `by linarith`. Use `(div_le_iff₀ hm').2 h1` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hGfin : G.Finite` using `hTfin.subset fun x hx => hx.1`. Establish `hGcard : (b + 1 - a).toNat * m ^ k ≤ G.ncard`. Combine the equalities or inequalities in the displayed calculation. Establish `hW0 : W 0 = Finset.Icc a b` using `if_pos (Fin.ext (by simp [hi₀]))`.

Establish `hWs : ∀ i : Fin k, W i.succ = Finset.Ico (0 : ℤ) m` using `fun i => if_neg (fun h => by simp [hi₀, Fin.ext_iff] at h)`. Rewrite using `[Fintype.card_piFinset, Fin.prod_univ_succ, hW0]`. Simplify using `only [hWs, Int.card_Icc, Int.card_Ico, Finset.prod_const, Finset.card_univ, Fintype.card_fin, sub_zero, Int.toNat_natCast]`. Use `_ = (gridPoint (k + 1) m '' (Fintype.piFinset W)).ncard := by`. Rewrite using `[(gridPoint_injOn hm hWwidth).ncard_image, ncard_coe_finset]`.

Use `_ ≤ G.ncard := ncard_le_ncard hGsub hGfin`. Establish `hSfin : S.Finite` using `hTfin.subset inter_subset_left`. Establish `hG'fin : G'.Finite` using `hTfin.subset fun x hx => hx.1.1`. Establish `hGG' : G.ncard ≤ G'.ncard + S.ncard`. Use `(ncard_le_ncard_sdiff_add_ncard G S hSfin).trans (Nat.add_le_add_right ?_ _)` and prove the remaining obligations.

Use `ncard_le_ncard ?_ hG'fin` and prove the remaining obligations. Introduce and unpack `x ⟨⟨hxT, hx⟩, hxS⟩`. Conclude with `⟨⟨hxT, fun hxZ => hxS ⟨hxT, hxZ⟩⟩, hx⟩`. Establish `hT'card : (T \ Z).ncard ≤ T.ncard` using `ncard_le_ncard sdiff_subset hTfin`. Establish `hP : (0 : ℝ) ≤ (m : ℝ) ^ k` using `by positivity`.

Establish `hab : ((b + 1 - a : ℤ) : ℝ) ≤ (((b + 1 - a).toNat : ℕ) : ℝ)`. Conclude with `Int.self_le_toNat _` after adjusting the coercions. Establish `h1 : ((m : ℝ) / 2 - 1) * (m : ℝ) ^ k ≤ G.ncard`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : 0 ≤ ((m : ℝ) - 12) * (m : ℝ) ^ k` using `mul_nonneg (by linarith) hP`.

Establish `h3 : ((T \ Z).ncard : ℝ) ≤ (m : ℝ) ^ k * m`. Rewrite using `[← pow_succ]`. Conclude with `hT'card.trans hTcard` after adjusting the coercions. Establish `h4 : (G.ncard : ℝ) ≤ G'.ncard + S.ncard` using `by exact_mod_cast hGG'`. Rewrite `hz` using `[pow_succ]`.

Rewrite using `[← Nat.cast_le (α := ℝ)]`. Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem proof : TorsionEquidistribution.Statement := by
  intro n hn Z c hZ hZ0 _hc
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  filter_upwards [eventually_ncard_inter_lt Z hZ hZ0, eventually_ge_atTop 12] with m hz hm12
  have hm : 0 < m := by omega
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hm12' : (12 : ℝ) ≤ m := by exact_mod_cast hm12
  set T := torusTorsion (k + 1) m with hT
  set i₀ : Fin (k + 1) := ⟨0, hn⟩ with hi₀
  set S := T ∩ Z with hS
  set G' := {x ∈ T \ Z | (1 / 4 : ℝ) ≤ ‖x i₀ + (c : AddCircle (1 : ℝ))‖} with hG'
  change (T \ Z).ncard ≤ 3 * G'.ncard

  have hTsub : T ⊆ gridPoint (k + 1) m ''
      (Fintype.piFinset fun _ : Fin (k + 1) => Finset.Ico (0 : ℤ) m) := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := exists_gridPoint hm hx
    exact ⟨j, hj, rfl⟩
  have hTfin : T.Finite := ((Finset.finite_toSet _).image _).subset hTsub
  have hTcard : T.ncard ≤ m ^ (k + 1) := by
    refine (ncard_le_ncard hTsub ((Finset.finite_toSet _).image _)).trans ?_
    refine (ncard_image_le (Finset.finite_toSet _)).trans ?_
    rw [ncard_coe_finset, Fintype.card_piFinset]
    simp [Int.card_Ico]

  set G := {x ∈ T | (1 / 4 : ℝ) ≤ ‖x i₀ + (c : AddCircle (1 : ℝ))‖} with hG
  set a : ℤ := ⌈(m : ℝ) / 4 - m * c⌉ with ha
  set b : ℤ := ⌊3 * (m : ℝ) / 4 - m * c⌋ with hb
  have ha1 : (m : ℝ) / 4 - m * c ≤ a := Int.le_ceil _
  have ha2 : (a : ℝ) < (m : ℝ) / 4 - m * c + 1 := Int.ceil_lt_add_one _
  have hb1 : (b : ℝ) ≤ 3 * (m : ℝ) / 4 - m * c := Int.floor_le _
  have hb2 : 3 * (m : ℝ) / 4 - m * c < b + 1 := Int.lt_floor_add_one _
  set W : Fin (k + 1) → Finset ℤ := fun i => if i = i₀ then Finset.Icc a b else Finset.Ico 0 m
    with hW
  have hWwidth : ∀ i, ∀ u ∈ W i, ∀ v ∈ W i, |u - v| < m := by
    intro i u hu v hv
    by_cases hi : i = i₀
    · simp only [hW, hi, if_true, Finset.mem_Icc] at hu hv
      have h1 : ((b - a : ℤ) : ℝ) < m := by push_cast; linarith
      have h2 : b - a < m := by exact_mod_cast h1
      rw [abs_lt]; constructor <;> omega
    · simp only [hW, hi, if_false, Finset.mem_Ico] at hu hv
      rw [abs_lt]; constructor <;> omega
  have hGsub : gridPoint (k + 1) m '' (Fintype.piFinset W) ⊆ G := by
    rintro _ ⟨j, hj, rfl⟩
    refine ⟨gridPoint_mem hm j, ?_⟩
    have hj0 := Fintype.mem_piFinset.1 (Finset.mem_coe.1 hj) i₀
    simp only [hW, if_true, Finset.mem_Icc] at hj0
    have hlo : (a : ℝ) ≤ j i₀ := by exact_mod_cast hj0.1
    have hhi : (j i₀ : ℝ) ≤ b := by exact_mod_cast hj0.2
    have e : gridPoint (k + 1) m j i₀ + (c : AddCircle (1 : ℝ)) =
        (((j i₀ : ℝ) / m + c : ℝ) : AddCircle (1 : ℝ)) := by
      rw [AddCircle.coe_add]; rfl
    rw [e]
    apply quarter_le_norm
    · have h1 : (1 / 4 - c) * m ≤ j i₀ := by linarith
      have := (le_div_iff₀ hm').2 h1; linarith
    · have h1 : (j i₀ : ℝ) ≤ (3 / 4 - c) * m := by linarith
      have := (div_le_iff₀ hm').2 h1; linarith
  have hGfin : G.Finite := hTfin.subset fun x hx => hx.1
  have hGcard : (b + 1 - a).toNat * m ^ k ≤ G.ncard := by
    calc (b + 1 - a).toNat * m ^ k = (Fintype.piFinset W).card := by
          have hW0 : W 0 = Finset.Icc a b := if_pos (Fin.ext (by simp [hi₀]))
          have hWs : ∀ i : Fin k, W i.succ = Finset.Ico (0 : ℤ) m := fun i =>
            if_neg (fun h => by simp [hi₀, Fin.ext_iff] at h)
          rw [Fintype.card_piFinset, Fin.prod_univ_succ, hW0]
          simp only [hWs, Int.card_Icc, Int.card_Ico, Finset.prod_const, Finset.card_univ,
            Fintype.card_fin, sub_zero, Int.toNat_natCast]
      _ = (gridPoint (k + 1) m '' (Fintype.piFinset W)).ncard := by
          rw [(gridPoint_injOn hm hWwidth).ncard_image, ncard_coe_finset]
      _ ≤ G.ncard := ncard_le_ncard hGsub hGfin

  have hSfin : S.Finite := hTfin.subset inter_subset_left
  have hG'fin : G'.Finite := hTfin.subset fun x hx => hx.1.1
  have hGG' : G.ncard ≤ G'.ncard + S.ncard := by
    refine (ncard_le_ncard_sdiff_add_ncard G S hSfin).trans (Nat.add_le_add_right ?_ _)
    refine ncard_le_ncard ?_ hG'fin
    rintro x ⟨⟨hxT, hx⟩, hxS⟩
    exact ⟨⟨hxT, fun hxZ => hxS ⟨hxT, hxZ⟩⟩, hx⟩
  have hT'card : (T \ Z).ncard ≤ T.ncard := ncard_le_ncard sdiff_subset hTfin

  have hP : (0 : ℝ) ≤ (m : ℝ) ^ k := by positivity
  have hab : ((b + 1 - a : ℤ) : ℝ) ≤ (((b + 1 - a).toNat : ℕ) : ℝ) := by
    exact_mod_cast Int.self_le_toNat _
  have h1 : ((m : ℝ) / 2 - 1) * (m : ℝ) ^ k ≤ G.ncard := by
    calc ((m : ℝ) / 2 - 1) * (m : ℝ) ^ k ≤ ((b + 1 - a : ℤ) : ℝ) * (m : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right (by push_cast; linarith) hP
      _ ≤ (((b + 1 - a).toNat : ℕ) : ℝ) * (m : ℝ) ^ k := mul_le_mul_of_nonneg_right hab hP
      _ ≤ G.ncard := by exact_mod_cast hGcard
  have h2 : 0 ≤ ((m : ℝ) - 12) * (m : ℝ) ^ k := mul_nonneg (by linarith) hP
  have h3 : ((T \ Z).ncard : ℝ) ≤ (m : ℝ) ^ k * m := by
    rw [← pow_succ]; exact_mod_cast hT'card.trans hTcard
  have h4 : (G.ncard : ℝ) ≤ G'.ncard + S.ncard := by exact_mod_cast hGG'
  rw [pow_succ] at hz
  rw [← Nat.cast_le (α := ℝ)]
  push_cast
  nlinarith

end TorsionEquidistribution

end

end GroundTheory.Heights₂.Heights
