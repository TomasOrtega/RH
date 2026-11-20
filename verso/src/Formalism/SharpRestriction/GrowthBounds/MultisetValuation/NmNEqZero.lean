import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.RationalLowerBounds

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open scoped Classical

variable {K : Type*} [Field K] {R : Subring K} {p : ℕ}

variable (R p) in

def nm_N (x : K) : ℝ := if x = 0 then 0 else (p : ℝ) ^ (-nm_v R p x)

/- English proof (translation)
Simplify using `[nm_N]`.
-/
theorem nm_N_zero : nm_N R p (0 : K) = 0 := by
  simp [nm_N]

/- English proof (translation)
Simplify using `[nm_N, hx]`.
-/
theorem nm_N_of_ne {x : K} (hx : x ≠ 0) : nm_N R p x = (p : ℝ) ^ (-nm_v R p x) := by
  simp [nm_N, hx]

/- English proof (translation)
Conclude with `h.one_lt` after adjusting the coercions.
-/
theorem nm_pR (h : nm_Hyp R p) : (1 : ℝ) < p := by
  exact_mod_cast h.one_lt

/- English proof (translation)
Unfold `nm_N`. Use `split_ifs`. Conclude with `le_rfl`. Conclude with `(Real.rpow_pos_of_pos (zero_lt_one.trans (nm_pR h)) _).le`.
-/
theorem nm_N_nonneg (h : nm_Hyp R p) (x : K) : 0 ≤ nm_N R p x := by
  unfold nm_N
  split_ifs
  · exact le_rfl
  · exact (Real.rpow_pos_of_pos (zero_lt_one.trans (nm_pR h)) _).le

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Simplify using `[nm_N, hx]`. Distinguish the cases in `hy : y = 0`. Simplify using `[nm_N, hy]`. Rewrite using `[nm_N_of_ne (mul_ne_zero hx hy), nm_N_of_ne hx, nm_N_of_ne hy, nm_v_mul h hx hy, neg_add, Real.rpow_add (zero_lt_one.trans (nm_pR h))]`.
-/
theorem nm_N_mul (h : nm_Hyp R p) (x y : K) : nm_N R p (x * y) = nm_N R p x * nm_N R p y := by
  by_cases hx : x = 0
  · simp [nm_N, hx]
  by_cases hy : y = 0
  · simp [nm_N, hy]
  rw [nm_N_of_ne (mul_ne_zero hx hy), nm_N_of_ne hx, nm_N_of_ne hy, nm_v_mul h hx hy, neg_add,
    Real.rpow_add (zero_lt_one.trans (nm_pR h))]

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Simplify using `[nm_N, hx]`. Rewrite using `[nm_N_of_ne hx]`. Simplify using `only [hx, iff_false]`. Conclude with `(Real.rpow_pos_of_pos (zero_lt_one.trans (nm_pR h)) _).ne'`.
-/
theorem nm_N_eq_zero (h : nm_Hyp R p) (x : K) : nm_N R p x = 0 ↔ x = 0 := by
  by_cases hx : x = 0
  · simp [nm_N, hx]
  · rw [nm_N_of_ne hx]
    simp only [hx, iff_false]
    exact (Real.rpow_pos_of_pos (zero_lt_one.trans (nm_pR h)) _).ne'

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Simplify using `only [hx, zero_add, nm_N_zero]`. Conclude with `le_max_right _ _`. Distinguish the cases in `hy : y = 0`. Simplify using `only [hy, add_zero, nm_N_zero]`.

Conclude with `le_max_left _ _`. Distinguish the cases in `hxy : x + y = 0`. Rewrite using `[hxy, nm_N_zero]`. Conclude with `le_max_of_le_left (nm_N_nonneg h x)`. Rewrite using `[nm_N_of_ne hxy, nm_N_of_ne hx, nm_N_of_ne hy]`.

Establish `hp1 : (1 : ℝ) ≤ p` using `(nm_pR h).le`. Establish `hm` using `nm_v_add h hx hy hxy`. Break down `le_total (nm_v R p x) (nm_v R p y) with hle | hle` into its components or cases. Rewrite `hm` using `[min_eq_left hle]`. Conclude with `le_max_of_le_left (Real.rpow_le_rpow_of_exponent_le hp1 (by linarith))`.

Rewrite `hm` using `[min_eq_right hle]`. Conclude with `le_max_of_le_right (Real.rpow_le_rpow_of_exponent_le hp1 (by linarith))`.
-/
theorem nm_N_add (h : nm_Hyp R p) (x y : K) : nm_N R p (x + y) ≤ max (nm_N R p x) (nm_N R p y) := by
  by_cases hx : x = 0
  · simp only [hx, zero_add, nm_N_zero]
    exact le_max_right _ _
  by_cases hy : y = 0
  · simp only [hy, add_zero, nm_N_zero]
    exact le_max_left _ _
  by_cases hxy : x + y = 0
  · rw [hxy, nm_N_zero]
    exact le_max_of_le_left (nm_N_nonneg h x)
  rw [nm_N_of_ne hxy, nm_N_of_ne hx, nm_N_of_ne hy]
  have hp1 : (1 : ℝ) ≤ p := (nm_pR h).le
  have hm := nm_v_add h hx hy hxy
  rcases le_total (nm_v R p x) (nm_v R p y) with hle | hle
  · rw [min_eq_left hle] at hm
    exact le_max_of_le_left (Real.rpow_le_rpow_of_exponent_le hp1 (by linarith))
  · rw [min_eq_right hle] at hm
    exact le_max_of_le_right (Real.rpow_le_rpow_of_exponent_le hp1 (by linarith))

/- English proof (translation)
Rewrite using `[nm_N_of_ne (nm_p_ne h), nm_v_p h, Real.rpow_neg_one]`.
-/
theorem nm_N_p (h : nm_Hyp R p) : nm_N R p (p : K) = (p : ℝ)⁻¹ := by
  rw [nm_N_of_ne (nm_p_ne h), nm_v_p h, Real.rpow_neg_one]

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Simplify using `only [nm_N_zero, zero_le_one, true_iff]`. Conclude with `R.zero_mem`. Rewrite using `[nm_N_of_ne hx, ← nm_v_nonneg_iff h hx]`.

Establish `e : (1 : ℝ) = (p : ℝ) ^ (0 : ℝ)` using `(Real.rpow_zero _).symm`. Rewrite using `[e, Real.rpow_le_rpow_left_iff (nm_pR h), neg_nonpos]`.
-/
theorem nm_N_le_one (h : nm_Hyp R p) (x : K) : nm_N R p x ≤ 1 ↔ x ∈ R := by
  by_cases hx : x = 0
  · subst hx
    simp only [nm_N_zero, zero_le_one, true_iff]
    exact R.zero_mem
  rw [nm_N_of_ne hx, ← nm_v_nonneg_iff h hx]
  have e : (1 : ℝ) = (p : ℝ) ^ (0 : ℝ) := (Real.rpow_zero _).symm
  rw [e, Real.rpow_le_rpow_left_iff (nm_pR h), neg_nonpos]

def nm_abs (h : nm_Hyp R p) : AbsoluteValue K ℝ where
  toFun := nm_N R p
  map_mul' := nm_N_mul h
  nonneg' := nm_N_nonneg h
  eq_zero' := nm_N_eq_zero h
  add_le' x y := le_trans (nm_N_add h x y) (max_le_add_of_nonneg (nm_N_nonneg h x) (nm_N_nonneg h y))

/- English proof (translation)
Set `nK : NormedField K` to `N.toNormedField`. Establish `hnorm : ∀ x : K, ‖x‖ = N x` using `fun _ => rfl`. Establish `hnatK : ∀ n : ℕ, N (n : K) ≤ 1`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Nat.cast_succ]`. Conclude with `le_trans (hna _ _) (max_le ih (by simp))`. Establish `hcast : ∀ n : ℕ, ((n : K) : UniformSpace.Completion K) = (n : UniformSpace.Completion K)` using `fun n => map_natCast (UniformSpace.Completion.coeRingHom (α := K)) n`.

Establish `hnatC : ∀ n : ℕ, ‖(n : UniformSpace.Completion K)‖ ≤ 1`. Introduce `n`. Rewrite using `[← hcast, UniformSpace.Completion.norm_coe]`. Conclude with `hnatK n`. Establish `uC : IsUltrametricDist (UniformSpace.Completion K)` using `IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one hnatC`.

Set `nnC : NontriviallyNormedField (UniformSpace.Completion K)` to `{ (inferInstance : NormedField (UniformSpace.Completion K)) with non_trivial := ⟨(c : UniformSpace.Completion K), by rw [UniformSpace.Completion.norm_coe]; exact hc⟩ }`. Set `nL : NormedField (AlgebraicClosure (UniformSpace.Completion K))` to `spectralNorm.normedField (UniformSpace.Completion K) (AlgebraicClosure (UniformSpace.Completion K))`. Establish `hext : ∀ z : UniformSpace.Completion K, ‖algebraMap (UniformSpace.Completion K) (AlgebraicClosure (UniformSpace.Completion K)) z‖ = ‖z‖` using `fun z => spectralNorm_extends z`. Set `aL : Algebra K (AlgebraicClosure (UniformSpace.Completion K))` to `((algebraMap (UniformSpace.Completion K) (AlgebraicClosure (UniformSpace.Completion K))).comp (UniformSpace.Completion.coeRingHom (α := K))).toAlgebra`. Use `⟨AlgebraicClosure (UniformSpace.Completion K), nL, aL, ?_, inferInstance, ?_⟩` and prove the remaining obligations.

Apply `IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one` to reduce the goal to its premises. Introduce `n`. Use `hext (n : UniformSpace.Completion K)` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Rewrite using `[this]`.

Conclude with `hnatC n`. Introduce `x show ‖algebraMap (UniformSpace.Completion K) (AlgebraicClosure (UniformSpace.Completion K)) (x : UniformSpace.Completion K)‖ = N x`. Rewrite using `[hext, UniformSpace.Completion.norm_coe]`. Both sides reduce to the same expression.
-/
theorem nm_extG {K : Type} [Field K] (N : AbsoluteValue K ℝ) (hna : ∀ x y, N (x + y) ≤ max (N x) (N y)) (c : K)
    (hc : 1 < N c) :
    ∃ (K' : Type) (_ : NormedField K') (_ : Algebra K K'), IsUltrametricDist K' ∧ IsAlgClosed K' ∧
      ∀ x, ‖algebraMap K K' x‖ = N x := by
  let nK : NormedField K := N.toNormedField
  have hnorm : ∀ x : K, ‖x‖ = N x := fun _ => rfl
  have hnatK : ∀ n : ℕ, N (n : K) ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ]
      exact le_trans (hna _ _) (max_le ih (by simp))
  have hcast : ∀ n : ℕ, ((n : K) : UniformSpace.Completion K) = (n : UniformSpace.Completion K) := fun n =>
    map_natCast (UniformSpace.Completion.coeRingHom (α := K)) n
  have hnatC : ∀ n : ℕ, ‖(n : UniformSpace.Completion K)‖ ≤ 1 := by
    intro n
    rw [← hcast, UniformSpace.Completion.norm_coe]
    exact hnatK n
  have uC : IsUltrametricDist (UniformSpace.Completion K) :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one hnatC
  let nnC : NontriviallyNormedField (UniformSpace.Completion K) :=
    { (inferInstance : NormedField (UniformSpace.Completion K)) with
      non_trivial := ⟨(c : UniformSpace.Completion K), by rw [UniformSpace.Completion.norm_coe]; exact hc⟩ }
  let nL : NormedField (AlgebraicClosure (UniformSpace.Completion K)) :=
    spectralNorm.normedField (UniformSpace.Completion K) (AlgebraicClosure (UniformSpace.Completion K))
  have hext : ∀ z : UniformSpace.Completion K,
      ‖algebraMap (UniformSpace.Completion K) (AlgebraicClosure (UniformSpace.Completion K)) z‖ = ‖z‖ :=
    fun z => spectralNorm_extends z
  let aL : Algebra K (AlgebraicClosure (UniformSpace.Completion K)) :=
    ((algebraMap (UniformSpace.Completion K) (AlgebraicClosure (UniformSpace.Completion K))).comp
      (UniformSpace.Completion.coeRingHom (α := K))).toAlgebra
  refine ⟨AlgebraicClosure (UniformSpace.Completion K), nL, aL, ?_, inferInstance, ?_⟩
  · apply IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one
    intro n
    have := hext (n : UniformSpace.Completion K)
    rw [map_natCast] at this
    rw [this]
    exact hnatC n
  · intro x
    show ‖algebraMap (UniformSpace.Completion K) (AlgebraicClosure (UniformSpace.Completion K))
      (x : UniformSpace.Completion K)‖ = N x
    rw [hext, UniformSpace.Completion.norm_coe]
    rfl

end Formalism.MainNotions.FormalGroupSystem.Pf
