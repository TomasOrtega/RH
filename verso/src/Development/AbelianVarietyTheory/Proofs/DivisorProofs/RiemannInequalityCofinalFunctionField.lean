import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceIsDVRAndResidueEqGroundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldFiniteSupportSumOrderEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsManyBoundedByPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldZerosFiniteSumOrderEqFinrankStatement

open scoped IntermediateField Polynomial RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

namespace RiemannCofinal

variable {k F : Type} [Field k] [Field F] [Algebra k F]

/- English proof (translation)
The claim follows from `(Valuation.ne_zero_iff _).2 hx`.
-/
theorem val_ne_zero (v : Place k F) {x : F} (hx : x ≠ 0) : v.1 x ≠ 0 :=
  (Valuation.ne_zero_iff _).2 hx

/- English proof (translation)
Unfold `ord`. Rewrite using `[map_mul, WithZero.log_mul (val_ne_zero v hx) (val_ne_zero v hy)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ord_mul (v : Place k F) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    ord v (x * y) = ord v x + ord v y := by
  unfold ord
  rw [map_mul, WithZero.log_mul (val_ne_zero v hx) (val_ne_zero v hy)]
  ring

/- English proof (translation)
Unfold `ord`. Rewrite using `[map_inv₀, WithZero.log_inv]`.
-/
theorem ord_inv (v : Place k F) (x : F) : ord v x⁻¹ = -ord v x := by
  unfold ord
  rw [map_inv₀, WithZero.log_inv]

/- English proof (translation)
Unfold `ord`. Rewrite using `[map_pow, WithZero.log_pow]`. Simplify using the standard rewrite rules.
-/
theorem ord_pow (v : Place k F) (x : F) (n : ℕ) : ord v (x ^ n) = n * ord v x := by
  unfold ord
  rw [map_pow, WithZero.log_pow]
  simp

/- English proof (translation)
Simplify using `[ord]`.
-/
theorem ord_one (v : Place k F) : ord v 1 = 0 := by simp [ord]

/- English proof (translation)
Unfold `ord`. Use `(WithZero.log_le_log (val_ne_zero v hx) (val_ne_zero v hy)).2 h` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem ord_le_ord (v : Place k F) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) (h : v.1 x ≤ v.1 y) :
    ord v y ≤ ord v x := by
  unfold ord
  have := (WithZero.log_le_log (val_ne_zero v hx) (val_ne_zero v hy)).2 h
  omega

/- English proof (translation)
Unfold `ord`. Rewrite using `[← WithZero.log_le_log (val_ne_zero v hx) one_ne_zero, WithZero.log_one]`. Apply the tactic sequence `constructor <;> intro <;> omega`.
-/
theorem le_one_iff (v : Place k F) {x : F} (hx : x ≠ 0) : v.1 x ≤ 1 ↔ 0 ≤ ord v x := by
  unfold ord
  rw [← WithZero.log_le_log (val_ne_zero v hx) one_ne_zero, WithZero.log_one]
  constructor <;> intro <;> omega

/- English proof (translation)
Unfold `ord`. Rewrite using `[← WithZero.log_lt_log (val_ne_zero v hx) one_ne_zero, WithZero.log_one]`. Apply the tactic sequence `constructor <;> intro <;> omega`.
-/
theorem lt_one_iff (v : Place k F) {x : F} (hx : x ≠ 0) : v.1 x < 1 ↔ 0 < ord v x := by
  unfold ord
  rw [← WithZero.log_lt_log (val_ne_zero v hx) one_ne_zero, WithZero.log_one]
  constructor <;> intro <;> omega

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [ord_one]`. Consider the case `@insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha, ord_mul v (hx a (Finset.mem_insert_self a s)) (Finset.prod_ne_zero_iff.2 fun i hi => hx i (Finset.mem_insert_of_mem hi)), ih fun i hi => hx i (Finset.mem_insert_of_mem hi)]`.
-/
theorem ord_prod {ι : Type} (v : Place k F) (s : Finset ι) (x : ι → F) (hx : ∀ i ∈ s, x i ≠ 0) :
    ord v (∏ i ∈ s, x i) = ∑ i ∈ s, ord v (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ord_one]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      ord_mul v (hx a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.2 fun i hi => hx i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hx i (Finset.mem_insert_of_mem hi)]

/- English proof (translation)
Distinguish the cases in `hc : c = 0`. Simplify using `[hc]`. Rewrite using `[v.2.2 c hc]`.
-/
theorem val_algebraMap_le (v : Place k F) (c : k) : v.1 (algebraMap k F c) ≤ 1 := by
  by_cases hc : c = 0
  · simp [hc]
  · rw [v.2.2 c hc]

end RiemannCofinal

end GlobalTheory.Nef

namespace GlobalTheory.Nef

open RiemannCofinal

/- English proof (translation)
Introduce `k F _ _ _ _ _ hFF`. Take `⟨t, ht, -⟩` from `id hFF`. Establish `ht0 : t ≠ 0` using `fun h => ht (h ▸ isAlgebraic_zero)`. Establish `hti : Transcendental k t⁻¹` using `fun h => ht (IsAlgebraic.inv_iff.1 h)`. Establish `hadj : k⟮t⁻¹⟯ = k⟮t⟯` using `le_antisymm (IntermediateField.adjoin_simple_le_iff.2 (inv_mem (IntermediateField.mem_adjoin_simple_self k t))) (IntermediateField.adjoin_simple_le_iff.2 (by simpa using inv_mem (IntermediateField.mem_adjoin_simple_self k t⁻¹)))`.

Take `⟨c, hc⟩` from `GlobalTheory.T.exists_linearIndependent_bounded_by_pow_of_transcendental k F hFF t ht`. Take `⟨hPfin, hPdeg⟩` from `GlobalTheory.T.functionField_zeros_finite_sum_order_eq_finrank k F hFF t⁻¹ hti`. Rewrite `hPdeg` using `[hadj]`. Use `⟨c * Module.finrank k⟮t⟯ F, fun D => ?_⟩` and prove the remaining obligations. Establish `hpole : ∀ w : Place k F, ¬ w.1 t ≤ 1 ↔ w.1 t⁻¹ < 1`.

Introduce `w`. Rewrite using `[lt_one_iff w (inv_ne_zero ht0), ord_inv, le_one_iff w ht0]`. Apply the tactic sequence `constructor <;> intro <;> omega`. Establish `hres : ∀ v : Place k F, v.1 t ≤ 1 → ∃ a : k, v.1 (t - algebraMap k F a) < 1` using `fun v => (GlobalTheory.T.functionFieldPlace_isDVR_and_residue_eq_ground k F hFF v).2 t`. Take `⟨r, hr⟩ : ∃ r : Place k F → k, ∀ v : Place k F, v.1 t ≤ 1 → v.1 (t - algebraMap k F (r v)) < 1` from `⟨fun v => if h : v.1 t ≤ 1 then (hres v h).choose else 0, fun v h => by`.

Simplify using `only [dif_pos h]`. Conclude with `(hres v h).choose_spec⟩`. Establish `hlin0 : ∀ a : k, t - algebraMap k F a ≠ 0` using `fun a h => ht (sub_eq_zero.1 h ▸ isAlgebraic_algebraMap a)`. Take `⟨M, hM⟩ : ∃ M : ℕ, M = ∑ v ∈ D.support, (D v).natAbs` from `⟨_, rfl⟩`. Take `⟨h, hh⟩ : ∃ h : F, h = ∏ v ∈ D.support, (t - algebraMap k F (r v)) ^ (D v).natAbs` from `⟨_, rfl⟩`.

Establish `hh0 : h ≠ 0` using `hh ▸ Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (hlin0 _)`. Establish `hordh : ∀ w : Place k F, ord w h = ∑ v ∈ D.support, ((D v).natAbs : ℤ) * ord w (t - algebraMap k F (r v))`. Introduce `w`. Rewrite using `[hh, ord_prod w _ _ (fun v _ => pow_ne_zero _ (hlin0 _))]`. Conclude with `Finset.sum_congr rfl fun v _ => ord_pow w _ _`.

Take `⟨hhfin, hhsum⟩` from `GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k F hFF h hh0`. Take `⟨n, f, hli, hn, hf⟩` from `hc (2 * M)`. Take `⟨P, hP⟩ : ∃ P : Place k F → ℤ, P = {v : Place k F | v.1 t⁻¹ < 1}.indicator fun v => ord v t⁻¹` from `⟨_, rfl⟩`. Establish `hPpole : ∀ w : Place k F, ¬ w.1 t ≤ 1 → P w = -ord w t`. Introduce `w hw`.

Rewrite using `[hP, Set.indicator_of_mem (show w ∈ {v : Place k F | v.1 t⁻¹ < 1} from (hpole w).1 hw), ord_inv]`. Establish `hPint : ∀ w : Place k F, w.1 t ≤ 1 → P w = 0`. Introduce `w hw`. Rewrite using `[hP, Set.indicator_of_notMem (show w ∉ {v : Place k F | v.1 t⁻¹ < 1} from fun h' => (hpole w).2 h' hw)]`. Establish `hPsupp : Function.support P ⊆ {v : Place k F | v.1 t⁻¹ < 1}`.

Introduce `w hw`. Assume the negation of the conclusion as `hw'`. Conclude with `hw (hPint w (by by_contra h'; exact hw' ((hpole w).1 h')))`. Establish `hhsupp : Function.support (fun v : Place k F => ord v h) ⊆ {v : Place k F | v.1 h ≠ 1}`. Introduce `v hv hv1`.

Conclude with `hv (show ord v h = 0 by simp [ord, hv1])`. Take `⟨g, hg⟩ : ∃ g : Place k F → ℤ, g = fun v => ((2 * M : ℕ) : ℤ) * P v + ord v h` from `⟨_, rfl⟩`. Establish `hgfin : (Function.support g).Finite`. Use `(hPfin.union hhfin).subset fun v hv => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hnot`.

Simplify using `only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hnot`. Apply `hv` to reduce the goal to its premises. Establish `h1 : P v = 0`. Assume the negation of the conclusion as `h'`. Conclude with `hnot.1 (hPsupp h')`.

Establish `h2 : ord v h = 0` using `by simp [ord, hnot.2]`. Simplify using `[hg, h1, h2]`. Use `⟨Finsupp.ofSupportFinite g hgfin, ?_, n, fun i => f i * h⁻¹, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `w`. Use `show D w ≤ g w`.

Simplify using `only [hg]`. Establish `hDM : D w ≤ (M : ℤ)`. Distinguish the cases in `hw : w ∈ D.support`. Establish `h1` using `Finset.single_le_sum (f := fun v => (D v).natAbs) (fun _ _ => Nat.zero_le _) hw`. Establish `h2 : D w ≤ ((D w).natAbs : ℤ)` using `Int.le_natAbs`.

Rewrite using `[hM]`. Establish `h3 : (((D w).natAbs : ℕ) : ℤ) ≤ ((∑ v ∈ D.support, (D v).natAbs : ℕ) : ℤ)` using `Nat.cast_le.2 h1`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Finsupp.notMem_support_iff.1 hw]`. Check the signs of the components of the expression.

Distinguish the cases in `ht1 : w.1 t ≤ 1`. Establish `hnn : ∀ v, 0 ≤ ord w (t - algebraMap k F (r v))` using `fun v => (le_one_iff w (hlin0 _)).1 ((Valuation.map_sub _ _ _).trans (max_le ht1 (val_algebraMap_le w _)))`. Simplify using `only [hPint w ht1, mul_zero, zero_add, hordh w]`. Distinguish the cases in `hw : w ∈ D.support`. Establish `hone : 0 < ord w (t - algebraMap k F (r w))` using `(lt_one_iff w (hlin0 _)).1 (hr w ht1)`.

Establish `h2 : D w ≤ ((D w).natAbs : ℤ)` using `Int.le_natAbs`. Establish `h3` using `Finset.single_le_sum (f := fun v => ((D v).natAbs : ℤ) * ord w (t - algebraMap k F (r v))) (fun v _ => mul_nonneg (by positivity) (hnn v)) hw`. Establish `h4 : ((D w).natAbs : ℤ) ≤ ((D w).natAbs : ℤ) * ord w (t - algebraMap k F (r w))`. Use the polynomial consequences of the given equalities and inequalities. Use linear arithmetic over natural numbers and integers.

Rewrite using `[Finsupp.notMem_support_iff.1 hw]`. Conclude with `Finset.sum_nonneg fun v _ => mul_nonneg (by positivity) (hnn v)`. Establish `hge : ∀ v, ord w t ≤ ord w (t - algebraMap k F (r v))` using `fun v => ord_le_ord w (hlin0 _) ht0 ((Valuation.map_sub _ _ _).trans (max_le le_rfl ((val_algebraMap_le w _).trans (le_of_lt (not_le.1 ht1)))))`. Establish `hsum : (M : ℤ) * ord w t ≤ ord w h`. Rewrite using `[hordh, hM]`.

Use `push_cast`. Rewrite using `[Finset.sum_mul]`. Conclude with `Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (hge v) (by positivity)`. Establish `hneg : ord w t < 0`. Use `(le_one_iff w ht0).not.1 ht1` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hPpole w ht1]`. Use `push_cast`. Establish `hM0 : (0 : ℤ) ≤ M` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.

Conclude with `hli.map' (LinearMap.mulRight k h⁻¹) (LinearMap.ker_eq_bot.2 (mul_left_injective₀ (inv_ne_zero hh0)))`. Establish `hsub : Function.support g ⊆ ↑(Finsupp.ofSupportFinite g hgfin).support`. Introduce `v hv`. Conclude with `Finsupp.mem_support_iff.2 hv`. Establish `hdeg : ((Finsupp.ofSupportFinite g hgfin).sum fun _ m => m) = ((2 * M : ℕ) : ℤ) * Module.finrank k⟮t⟯ F`.

Establish `h1 : ((Finsupp.ofSupportFinite g hgfin).sum fun _ m => m) = ∑ᶠ v, g v`. Rewrite using `[finsum_eq_sum_of_support_subset g hsub]`. Both sides reduce to the same expression. Establish `hPsum : ∑ᶠ v, P v = Module.finrank k⟮t⟯ F`. Rewrite `hPdeg` using `[finsum_mem_def]`.

Rewrite using `[hP]`. Conclude with `hPdeg`. Rewrite using `[h1, hg]`. Rewrite using `[finsum_add_distrib ((hPfin.subset hPsupp).subset fun v hv h0 => hv (by simp [h0])) (hhfin.subset hhsupp), ← mul_finsum, hhsum, hPsum, add_zero]`. Rewrite using `[hdeg]`.

Use `push_cast`. Combine the equalities or inequalities in the displayed calculation. Introduce `i w`. Establish `hfi : f i ≠ 0` using `hli.ne_zero i`. Use `show -(g w) ≤ ord w (f i * h⁻¹)`.

Rewrite using `[ord_mul w hfi (inv_ne_zero hh0), ord_inv, hg]`. Establish `key : -(((2 * M : ℕ) : ℤ) * P w) ≤ ord w (f i)`. Distinguish the cases in `ht1 : w.1 t ≤ 1`. Establish `h1 : w.1 (f i) ≤ 1` using `by simpa [max_eq_left ht1] using hf i w`. Rewrite using `[hPint w ht1]`.

Simplify using `using (le_one_iff w hfi).1 h1`. Establish `h1 : w.1 (f i) ≤ w.1 (t ^ (2 * M))`. Rewrite using `[map_pow]`. Simplify `hf i w` using `[max_eq_right (le_of_lt (not_le.1 ht1))]`. Use `ord_le_ord w hfi (pow_ne_zero _ ht0) h1` as an intermediate fact.

Rewrite `this` using `[ord_pow]`. Rewrite using `[hPpole w ht1]`. Move the coercions through the operations in `at this ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem riemann_cofinal : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∃ γ : ℕ, ∀ D : Place k F →₀ ℤ, ∃ D' : Place k F →₀ ℤ, D ≤ D' ∧ ∃ (n : ℕ) (f : Fin n → F), LinearIndependent k f ∧ (D'.sum fun _ m => m) - γ ≤ n ∧ ∀ (i : Fin n) (v : Place k F), -D' v ≤ ord v (f i) := by
  intro k F _ _ _ _ _ hFF
  classical
  obtain ⟨t, ht, -⟩ := id hFF
  have ht0 : t ≠ 0 := fun h => ht (h ▸ isAlgebraic_zero)
  have hti : Transcendental k t⁻¹ := fun h => ht (IsAlgebraic.inv_iff.1 h)
  have hadj : k⟮t⁻¹⟯ = k⟮t⟯ := le_antisymm
    (IntermediateField.adjoin_simple_le_iff.2 (inv_mem (IntermediateField.mem_adjoin_simple_self k t)))
    (IntermediateField.adjoin_simple_le_iff.2
      (by simpa using inv_mem (IntermediateField.mem_adjoin_simple_self k t⁻¹)))
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_linearIndependent_bounded_by_pow_of_transcendental k F hFF t ht
  obtain ⟨hPfin, hPdeg⟩ := GlobalTheory.T.functionField_zeros_finite_sum_order_eq_finrank k F hFF t⁻¹ hti
  rw [hadj] at hPdeg
  refine ⟨c * Module.finrank k⟮t⟯ F, fun D => ?_⟩

  have hpole : ∀ w : Place k F, ¬ w.1 t ≤ 1 ↔ w.1 t⁻¹ < 1 := by
    intro w
    rw [lt_one_iff w (inv_ne_zero ht0), ord_inv, le_one_iff w ht0]
    constructor <;> intro <;> omega

  have hres : ∀ v : Place k F, v.1 t ≤ 1 → ∃ a : k, v.1 (t - algebraMap k F a) < 1 :=
    fun v => (GlobalTheory.T.functionFieldPlace_isDVR_and_residue_eq_ground k F hFF v).2 t
  obtain ⟨r, hr⟩ : ∃ r : Place k F → k, ∀ v : Place k F, v.1 t ≤ 1 → v.1 (t - algebraMap k F (r v)) < 1 :=
    ⟨fun v => if h : v.1 t ≤ 1 then (hres v h).choose else 0, fun v h => by
      simp only [dif_pos h]; exact (hres v h).choose_spec⟩
  have hlin0 : ∀ a : k, t - algebraMap k F a ≠ 0 := fun a h =>
    ht (sub_eq_zero.1 h ▸ isAlgebraic_algebraMap a)
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = ∑ v ∈ D.support, (D v).natAbs := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : F, h = ∏ v ∈ D.support, (t - algebraMap k F (r v)) ^ (D v).natAbs :=
    ⟨_, rfl⟩
  have hh0 : h ≠ 0 := hh ▸ Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (hlin0 _)
  have hordh : ∀ w : Place k F,
      ord w h = ∑ v ∈ D.support, ((D v).natAbs : ℤ) * ord w (t - algebraMap k F (r v)) := by
    intro w
    rw [hh, ord_prod w _ _ (fun v _ => pow_ne_zero _ (hlin0 _))]
    exact Finset.sum_congr rfl fun v _ => ord_pow w _ _
  obtain ⟨hhfin, hhsum⟩ := GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k F hFF h hh0
  obtain ⟨n, f, hli, hn, hf⟩ := hc (2 * M)
  obtain ⟨P, hP⟩ : ∃ P : Place k F → ℤ,
      P = {v : Place k F | v.1 t⁻¹ < 1}.indicator fun v => ord v t⁻¹ := ⟨_, rfl⟩
  have hPpole : ∀ w : Place k F, ¬ w.1 t ≤ 1 → P w = -ord w t := by
    intro w hw
    rw [hP, Set.indicator_of_mem (show w ∈ {v : Place k F | v.1 t⁻¹ < 1} from (hpole w).1 hw),
      ord_inv]
  have hPint : ∀ w : Place k F, w.1 t ≤ 1 → P w = 0 := by
    intro w hw
    rw [hP, Set.indicator_of_notMem (show w ∉ {v : Place k F | v.1 t⁻¹ < 1} from
      fun h' => (hpole w).2 h' hw)]
  have hPsupp : Function.support P ⊆ {v : Place k F | v.1 t⁻¹ < 1} := by
    intro w hw
    by_contra hw'
    exact hw (hPint w (by by_contra h'; exact hw' ((hpole w).1 h')))
  have hhsupp : Function.support (fun v : Place k F => ord v h) ⊆ {v : Place k F | v.1 h ≠ 1} := by
    intro v hv hv1
    exact hv (show ord v h = 0 by simp [ord, hv1])
  obtain ⟨g, hg⟩ : ∃ g : Place k F → ℤ, g = fun v => ((2 * M : ℕ) : ℤ) * P v + ord v h := ⟨_, rfl⟩
  have hgfin : (Function.support g).Finite := by
    refine (hPfin.union hhfin).subset fun v hv => ?_
    by_contra hnot
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hnot
    apply hv
    have h1 : P v = 0 := by
      by_contra h'; exact hnot.1 (hPsupp h')
    have h2 : ord v h = 0 := by simp [ord, hnot.2]
    simp [hg, h1, h2]
  refine ⟨Finsupp.ofSupportFinite g hgfin, ?_, n, fun i => f i * h⁻¹, ?_, ?_, ?_⟩
  ·
    intro w
    show D w ≤ g w
    simp only [hg]
    have hDM : D w ≤ (M : ℤ) := by
      by_cases hw : w ∈ D.support
      · have h1 := Finset.single_le_sum (f := fun v => (D v).natAbs) (fun _ _ => Nat.zero_le _) hw
        have h2 : D w ≤ ((D w).natAbs : ℤ) := Int.le_natAbs
        rw [hM]
        have h3 : (((D w).natAbs : ℕ) : ℤ) ≤ ((∑ v ∈ D.support, (D v).natAbs : ℕ) : ℤ) :=
          Nat.cast_le.2 h1
        omega
      · rw [Finsupp.notMem_support_iff.1 hw]; positivity
    by_cases ht1 : w.1 t ≤ 1
    · have hnn : ∀ v, 0 ≤ ord w (t - algebraMap k F (r v)) := fun v =>
        (le_one_iff w (hlin0 _)).1
          ((Valuation.map_sub _ _ _).trans (max_le ht1 (val_algebraMap_le w _)))
      simp only [hPint w ht1, mul_zero, zero_add, hordh w]
      by_cases hw : w ∈ D.support
      · have hone : 0 < ord w (t - algebraMap k F (r w)) := (lt_one_iff w (hlin0 _)).1 (hr w ht1)
        have h2 : D w ≤ ((D w).natAbs : ℤ) := Int.le_natAbs
        have h3 := Finset.single_le_sum
          (f := fun v => ((D v).natAbs : ℤ) * ord w (t - algebraMap k F (r v)))
          (fun v _ => mul_nonneg (by positivity) (hnn v)) hw
        have h4 : ((D w).natAbs : ℤ) ≤ ((D w).natAbs : ℤ) * ord w (t - algebraMap k F (r w)) := by
          nlinarith
        omega
      · rw [Finsupp.notMem_support_iff.1 hw]
        exact Finset.sum_nonneg fun v _ => mul_nonneg (by positivity) (hnn v)
    · have hge : ∀ v, ord w t ≤ ord w (t - algebraMap k F (r v)) := fun v =>
        ord_le_ord w (hlin0 _) ht0 ((Valuation.map_sub _ _ _).trans
          (max_le le_rfl ((val_algebraMap_le w _).trans (le_of_lt (not_le.1 ht1)))))
      have hsum : (M : ℤ) * ord w t ≤ ord w h := by
        rw [hordh, hM]
        push_cast
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (hge v) (by positivity)
      have hneg : ord w t < 0 := by
        have := (le_one_iff w ht0).not.1 ht1
        omega
      rw [hPpole w ht1]
      push_cast
      have hM0 : (0 : ℤ) ≤ M := by positivity
      nlinarith
  ·
    exact hli.map' (LinearMap.mulRight k h⁻¹)
      (LinearMap.ker_eq_bot.2 (mul_left_injective₀ (inv_ne_zero hh0)))
  ·
    have hsub : Function.support g ⊆ ↑(Finsupp.ofSupportFinite g hgfin).support := by
      intro v hv
      exact Finsupp.mem_support_iff.2 hv
    have hdeg : ((Finsupp.ofSupportFinite g hgfin).sum fun _ m => m) =
        ((2 * M : ℕ) : ℤ) * Module.finrank k⟮t⟯ F := by
      have h1 : ((Finsupp.ofSupportFinite g hgfin).sum fun _ m => m) = ∑ᶠ v, g v := by
        rw [finsum_eq_sum_of_support_subset g hsub]
        rfl
      have hPsum : ∑ᶠ v, P v = Module.finrank k⟮t⟯ F := by
        rw [finsum_mem_def] at hPdeg
        rw [hP]; exact hPdeg
      rw [h1, hg]
      rw [finsum_add_distrib
        ((hPfin.subset hPsupp).subset fun v hv h0 => hv (by simp [h0]))
        (hhfin.subset hhsupp), ← mul_finsum, hhsum, hPsum, add_zero]
    rw [hdeg]
    push_cast
    calc ((2 * M : ℕ) : ℤ) * Module.finrank k⟮t⟯ F - c * Module.finrank k⟮t⟯ F
        = (((2 * M : ℕ) : ℤ) - c) * Module.finrank k⟮t⟯ F := by ring
      _ ≤ n := hn
  ·
    intro i w
    have hfi : f i ≠ 0 := hli.ne_zero i
    show -(g w) ≤ ord w (f i * h⁻¹)
    rw [ord_mul w hfi (inv_ne_zero hh0), ord_inv, hg]
    have key : -(((2 * M : ℕ) : ℤ) * P w) ≤ ord w (f i) := by
      by_cases ht1 : w.1 t ≤ 1
      · have h1 : w.1 (f i) ≤ 1 := by simpa [max_eq_left ht1] using hf i w
        rw [hPint w ht1]
        simpa using (le_one_iff w hfi).1 h1
      · have h1 : w.1 (f i) ≤ w.1 (t ^ (2 * M)) := by
          rw [map_pow]; simpa [max_eq_right (le_of_lt (not_le.1 ht1))] using hf i w
        have := ord_le_ord w hfi (pow_ne_zero _ ht0) h1
        rw [ord_pow] at this
        rw [hPpole w ht1]
        push_cast at this ⊢
        linarith
    simp only
    linarith

end GlobalTheory.Nef
