import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.CjDefs

noncomputable section

namespace PI.VolSemiDirect.W.Cj

open Matrix

def genSet (A : Type) [CommRing A] (k : ℕ) : Set (GL (Fin k) A) :=
  {g | ∃ i j c, i ≠ j ∧ (g : Matrix (Fin k) (Fin k) A) = transvection i j c} ∪
    {g | ∃ d : Fin k → A, (g : Matrix (Fin k) (Fin k) A) = diagonal d}

section

variable {A : Type} [CommRing A] {k : ℕ}

def InG (M : Matrix (Fin k) (Fin k) A) : Prop :=
  ∃ g ∈ Subgroup.closure (genSet A k), (g : Matrix (Fin k) (Fin k) A) = M

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, Subgroup.one_mem _, Units.val_one⟩`.
-/
theorem inG_one : InG (1 : Matrix (Fin k) (Fin k) A) :=
  ⟨1, Subgroup.one_mem _, Units.val_one⟩

/- English proof (translation)
Take `⟨g, hg, rfl⟩` from `hM`. Take `⟨h, hh, rfl⟩` from `hN`. Conclude with `⟨g * h, Subgroup.mul_mem _ hg hh, Units.val_mul _ _⟩`.
-/
theorem inG_mul {M N : Matrix (Fin k) (Fin k) A} (hM : InG M) (hN : InG N) : InG (M * N) := by
  obtain ⟨g, hg, rfl⟩ := hM
  obtain ⟨h, hh, rfl⟩ := hN
  exact ⟨g * h, Subgroup.mul_mem _ hg hh, Units.val_mul _ _⟩

/- English proof (translation)
Set `g : GL (Fin k) A` to `⟨transvection i j c, transvection i j (-c), by rw [transvection_mul_transvection_same i j hij, add_neg_cancel, transvection_zero], by rw [transvection_mul_transvection_same i j hij, neg_add_cancel, transvection_zero]⟩`. Conclude with `⟨g, Subgroup.subset_closure (Or.inl ⟨i, j, c, hij, rfl⟩), rfl⟩`.
-/
theorem inG_transvection {i j : Fin k} (hij : i ≠ j) (c : A) : InG (transvection i j c) := by
  let g : GL (Fin k) A :=
    ⟨transvection i j c, transvection i j (-c),
      by rw [transvection_mul_transvection_same i j hij, add_neg_cancel, transvection_zero],
      by rw [transvection_mul_transvection_same i j hij, neg_add_cancel, transvection_zero]⟩
  exact ⟨g, Subgroup.subset_closure (Or.inl ⟨i, j, c, hij, rfl⟩), rfl⟩

/- English proof (translation)
Set `g : GL (Fin k) A` to `⟨diagonal d, diagonal (fun i => ((hd i).unit⁻¹ : Aˣ)), by rw [diagonal_mul_diagonal]; convert diagonal_one with i; exact (hd i).mul_val_inv, by rw [diagonal_mul_diagonal]; convert diagonal_one with i; exact (hd i).val_inv_mul⟩`. Conclude with `⟨g, Subgroup.subset_closure (Or.inr ⟨d, rfl⟩), rfl⟩`.
-/
theorem inG_diag (d : Fin k → A) (hd : ∀ i, IsUnit (d i)) : InG (diagonal d) := by
  let g : GL (Fin k) A :=
    ⟨diagonal d, diagonal (fun i => ((hd i).unit⁻¹ : Aˣ)),
      by rw [diagonal_mul_diagonal]; convert diagonal_one with i; exact (hd i).mul_val_inv,
      by rw [diagonal_mul_diagonal]; convert diagonal_one with i; exact (hd i).val_inv_mul⟩
  exact ⟨g, Subgroup.subset_closure (Or.inr ⟨d, rfl⟩), rfl⟩

/- English proof (translation)
Use `revert hp`. Use `Finset.induction_on s (fun _ => ?_) (fun a t ha ih hp => ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_empty, add_zero]`. Conclude with `inG_one`. Establish `hpa : p ≠ a` using `fun h => hp (by rw [h]; exact Finset.mem_insert_self a t)`.

Establish `hpt : p ∉ t` using `fun h => hp (Finset.mem_insert_of_mem h)`. Rewrite using `[Finset.sum_insert ha]`. Establish `e : (1 : Matrix (Fin k) (Fin k) A) + (single p a (c a) + ∑ i ∈ t, single p i (c i)) = transvection p a (c a) * (1 + ∑ i ∈ t, single p i (c i))`. Rewrite using `[transvection, add_mul, one_mul, mul_add, mul_one, Finset.mul_sum, Finset.sum_eq_zero (fun i _ => single_mul_single_of_ne (c a) p a p (Ne.symm hpa) (c i)), add_zero]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e]`. Conclude with `inG_mul (inG_transvection hpa (c a)) (ih hpt)`.
-/
theorem inG_rowT (p : Fin k) (c : Fin k → A) (s : Finset (Fin k)) (hp : p ∉ s) :
    InG (1 + ∑ i ∈ s, single p i (c i)) := by
  revert hp
  refine Finset.induction_on s (fun _ => ?_) (fun a t ha ih hp => ?_)
  · rw [Finset.sum_empty, add_zero]
    exact inG_one
  · have hpa : p ≠ a := fun h => hp (by rw [h]; exact Finset.mem_insert_self a t)
    have hpt : p ∉ t := fun h => hp (Finset.mem_insert_of_mem h)
    rw [Finset.sum_insert ha]
    have e : (1 : Matrix (Fin k) (Fin k) A) + (single p a (c a) + ∑ i ∈ t, single p i (c i)) =
        transvection p a (c a) * (1 + ∑ i ∈ t, single p i (c i)) := by
      rw [transvection, add_mul, one_mul, mul_add, mul_one, Finset.mul_sum,
        Finset.sum_eq_zero (fun i _ => single_mul_single_of_ne (c a) p a p (Ne.symm hpa) (c i)),
        add_zero]
      abel
    rw [e]
    exact inG_mul (inG_transvection hpa (c a)) (ih hpt)

/- English proof (translation)
Use `revert hp`. Use `Finset.induction_on s (fun _ => ?_) (fun a t ha ih hp => ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_empty, add_zero]`. Conclude with `inG_one`. Establish `hpa : p ≠ a` using `fun h => hp (by rw [h]; exact Finset.mem_insert_self a t)`.

Establish `hpt : p ∉ t` using `fun h => hp (Finset.mem_insert_of_mem h)`. Rewrite using `[Finset.sum_insert ha]`. Establish `e : (1 : Matrix (Fin k) (Fin k) A) + (single a p (c a) + ∑ i ∈ t, single i p (c i)) = transvection a p (c a) * (1 + ∑ i ∈ t, single i p (c i))`. Rewrite using `[transvection, add_mul, one_mul, mul_add, mul_one, Finset.mul_sum, Finset.sum_eq_zero (fun i hi => single_mul_single_of_ne (c a) a p i (fun h => hpt (by rw [h]; exact hi)) (c i)), add_zero]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e]`. Conclude with `inG_mul (inG_transvection (Ne.symm hpa) (c a)) (ih hpt)`.
-/
theorem inG_colT (p : Fin k) (c : Fin k → A) (s : Finset (Fin k)) (hp : p ∉ s) :
    InG (1 + ∑ i ∈ s, single i p (c i)) := by
  revert hp
  refine Finset.induction_on s (fun _ => ?_) (fun a t ha ih hp => ?_)
  · rw [Finset.sum_empty, add_zero]
    exact inG_one
  · have hpa : p ≠ a := fun h => hp (by rw [h]; exact Finset.mem_insert_self a t)
    have hpt : p ∉ t := fun h => hp (Finset.mem_insert_of_mem h)
    rw [Finset.sum_insert ha]
    have e : (1 : Matrix (Fin k) (Fin k) A) + (single a p (c a) + ∑ i ∈ t, single i p (c i)) =
        transvection a p (c a) * (1 + ∑ i ∈ t, single i p (c i)) := by
      rw [transvection, add_mul, one_mul, mul_add, mul_one, Finset.mul_sum,
        Finset.sum_eq_zero (fun i hi => single_mul_single_of_ne (c a) a p i
          (fun h => hpt (by rw [h]; exact hi)) (c i)),
        add_zero]
      abel
    rw [e]
    exact inG_mul (inG_transvection (Ne.symm hpa) (c a)) (ih hpt)

/- English proof (translation)
Rewrite using `[add_mul, one_mul, Finset.sum_mul, Matrix.add_apply, Matrix.sum_apply]`. Use `congr 1`. Use `split_ifs with ha`. Substitute `ha` using the available equality. Conclude with `Finset.sum_congr rfl (fun i _ => single_mul_apply_same _ _ _ _ _)`.

Conclude with `Finset.sum_eq_zero (fun i _ => single_mul_apply_of_ne _ _ _ _ _ ha _)`.
-/
theorem rowT_mul_apply (p : Fin k) (c : Fin k → A) (s : Finset (Fin k))
    (X : Matrix (Fin k) (Fin k) A) (a b : Fin k) :
    ((1 + ∑ i ∈ s, single p i (c i)) * X) a b =
      X a b + if a = p then ∑ i ∈ s, c i * X i b else 0 := by
  rw [add_mul, one_mul, Finset.sum_mul, Matrix.add_apply, Matrix.sum_apply]
  congr 1
  split_ifs with ha
  · subst ha
    exact Finset.sum_congr rfl (fun i _ => single_mul_apply_same _ _ _ _ _)
  · exact Finset.sum_eq_zero (fun i _ => single_mul_apply_of_ne _ _ _ _ _ ha _)

/- English proof (translation)
Rewrite using `[add_mul, one_mul, Finset.sum_mul, Matrix.add_apply, Matrix.sum_apply]`. Use `congr 1`. Use `split_ifs with ha`. Rewrite using `[Finset.sum_eq_single a]`. Conclude with `single_mul_apply_same _ _ _ _ _`.

Introduce `i _ hia`. Conclude with `single_mul_apply_of_ne _ _ _ _ _ (Ne.symm hia) _`. Introduce `h`. Conclude with `absurd ha h`. Conclude with `Finset.sum_eq_zero (fun i hi => single_mul_apply_of_ne _ _ _ _ _ (fun h => ha (by rw [h]; exact hi)) _)`.
-/
theorem colT_mul_apply (p : Fin k) (c : Fin k → A) (s : Finset (Fin k))
    (X : Matrix (Fin k) (Fin k) A) (a b : Fin k) :
    ((1 + ∑ i ∈ s, single i p (c i)) * X) a b =
      X a b + if a ∈ s then c a * X p b else 0 := by
  rw [add_mul, one_mul, Finset.sum_mul, Matrix.add_apply, Matrix.sum_apply]
  congr 1
  split_ifs with ha
  · rw [Finset.sum_eq_single a]
    · exact single_mul_apply_same _ _ _ _ _
    · intro i _ hia
      exact single_mul_apply_of_ne _ _ _ _ _ (Ne.symm hia) _
    · intro h
      exact absurd ha h
  · exact Finset.sum_eq_zero (fun i hi => single_mul_apply_of_ne _ _ _ _ _
      (fun h => ha (by rw [h]; exact hi)) _)

/- English proof (translation)
Rewrite using `[mul_add, mul_one, Finset.mul_sum, Matrix.add_apply, Matrix.sum_apply]`. Use `congr 1`. Use `split_ifs with hb`. Rewrite using `[Finset.sum_eq_single b]`. Conclude with `mul_single_apply_same _ _ _ _ _`.

Introduce `j _ hjb`. Conclude with `mul_single_apply_of_ne _ _ _ _ _ (Ne.symm hjb) _`. Introduce `h`. Conclude with `absurd hb h`. Conclude with `Finset.sum_eq_zero (fun j hj => mul_single_apply_of_ne _ _ _ _ _ (fun h => hb (by rw [h]; exact hj)) _)`.
-/
theorem mul_rowT_apply (p : Fin k) (c : Fin k → A) (s : Finset (Fin k))
    (X : Matrix (Fin k) (Fin k) A) (a b : Fin k) :
    (X * (1 + ∑ j ∈ s, single p j (c j))) a b =
      X a b + if b ∈ s then X a p * c b else 0 := by
  rw [mul_add, mul_one, Finset.mul_sum, Matrix.add_apply, Matrix.sum_apply]
  congr 1
  split_ifs with hb
  · rw [Finset.sum_eq_single b]
    · exact mul_single_apply_same _ _ _ _ _
    · intro j _ hjb
      exact mul_single_apply_of_ne _ _ _ _ _ (Ne.symm hjb) _
    · intro h
      exact absurd hb h
  · exact Finset.sum_eq_zero (fun j hj => mul_single_apply_of_ne _ _ _ _ _
      (fun h => hb (by rw [h]; exact hj)) _)

def Red (m : ℕ) (M : Matrix (Fin k) (Fin k) A) : Prop :=
  ∀ i j : Fin k, (i.val < m ∨ j.val < m) → M i j = (1 : Matrix (Fin k) (Fin k) A) i j

/- English proof (translation)
Establish `nev : ∀ i j : Fin k, i.val ≠ j.val → i ≠ j` using `fun i j h e => h (congrArg Fin.val e)`. Use `set p : Fin k := ⟨m, hm⟩ with hpdef`. Establish `hpv : p.val = m` using `rfl`. Use `set s : Finset (Fin k) := Finset.univ.filter (fun i : Fin k => m < i.val) with hsdef`. Establish `mem_s : ∀ i : Fin k, i ∈ s ↔ m < i.val`.

Introduce `i`. Simplify using `[hsdef]`. Establish `hps : p ∉ s`. Rewrite using `[mem_s, hpv]`. Conclude with `lt_irrefl m`.

Establish `tri : ∀ i : Fin k, i.val < m ∨ i = p ∨ i ∈ s`. Introduce `i`. Break down `lt_trichotomy i.val m with h | h | h` into its components or cases. Conclude with `Or.inl h`. Conclude with `Or.inr (Or.inl (Fin.ext (h.trans hpv.symm)))`.

Conclude with `Or.inr (Or.inr ((mem_s i).2 h))`. Use `set Xm : Matrix (Fin k) (Fin k) A := (X : Matrix (Fin k) (Fin k) A) with hXm`. Establish `z1 : ∀ i j : Fin k, i.val < m → i ≠ j → Xm i j = 0` using `fun i j hi hij => by`. Rewrite using `[hX i j (Or.inl hi), Matrix.one_apply_ne hij]`. Establish `z2 : ∀ i j : Fin k, j.val < m → i ≠ j → Xm i j = 0` using `fun i j hj hij => by`.

Rewrite using `[hX i j (Or.inr hj), Matrix.one_apply_ne hij]`. Use `set Y : Matrix (Fin k) (Fin k) A := ((X⁻¹ : GL (Fin k) A) : Matrix (Fin k) (Fin k) A) with hY`. Establish `hYX : Y * Xm = 1`. Rewrite using `[hY, hXm, ← Units.val_mul, inv_mul_cancel, Units.val_one]`. Establish `hsum : Xm p p * Y p p + (∑ i ∈ s, Xm i p * Y p i) * 1 = 1`.

Establish `h1` using `congrFun (congrFun hYX p) p`. Rewrite `h1` using `[Matrix.mul_apply, Matrix.one_apply_eq]`. Rewrite using `[mul_one, ← h1, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin k => m < i.val), add_comm]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl (fun i _ => mul_comm _ _)`.

Rewrite using `[Finset.sum_eq_single p]`. Conclude with `mul_comm _ _`. Introduce `i hi hip`. Establish `hi' : ¬ m < i.val` using `(Finset.mem_filter.1 hi).2`. Establish `hne : i.val ≠ m` using `fun h => hip (Fin.ext (h.trans hpv.symm))`.

Rewrite using `[z1 i p (by omega) hip, mul_zero]`. Introduce `hp`. Conclude with `absurd (Finset.mem_filter.2 ⟨Finset.mem_univ p, by rw [hpv]; exact lt_irrefl m⟩) hp`. Take `⟨t, ht⟩` from `hA _ _ _ _ hsum`. Use `set c1 : Fin k → A := fun i => t * Y p i with hc1`.

Use `set R1 : Matrix (Fin k) (Fin k) A := 1 + ∑ i ∈ s, single p i (c1 i) with hR1`. Use `set X1 : Matrix (Fin k) (Fin k) A := R1 * Xm with hX1d`. Establish `hX1 : ∀ a b, X1 a b = Xm a b + if a = p then ∑ i ∈ s, c1 i * Xm i b else 0` using `fun a b => rowT_mul_apply p c1 s Xm a b`. Establish `hX1pp : X1 p p = Xm p p + t * ∑ i ∈ s, Xm i p * Y p i`. Rewrite using `[hX1, if_pos rfl, Finset.mul_sum]`.

Use `congr 1`. Conclude with `Finset.sum_congr rfl (fun i _ => by rw [hc1]; ring)`. Establish `hUnit : IsUnit (X1 p p)`. Rewrite using `[hX1pp]`. Conclude with `ht`.

Use `set w : A := ((hUnit.unit⁻¹ : Aˣ) : A) with hw`. Establish `huw : X1 p p * w = 1` using `hUnit.mul_val_inv`. Establish `hwu : w * X1 p p = 1` using `hUnit.val_inv_mul`. Establish `X1_ne : ∀ a b, a ≠ p → X1 a b = Xm a b`. Introduce `a b ha`.

Rewrite using `[hX1, if_neg ha, add_zero]`. Establish `X1_p_low : ∀ b : Fin k, b.val < m → X1 p b = 0`. Introduce `b hb`. Rewrite using `[hX1, if_pos rfl, z2 p b hb (nev p b (by omega)), zero_add]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `i hi`. Use `(mem_s i).1 hi` as an intermediate fact. Rewrite using `[z2 i b hb (nev i b (by omega)), mul_zero]`. Use `set c2 : Fin k → A := fun i => -(X1 i p * w) with hc2`. Use `set C : Matrix (Fin k) (Fin k) A := 1 + ∑ i ∈ s, single i p (c2 i) with hC`.

Use `set X2 : Matrix (Fin k) (Fin k) A := C * X1 with hX2d`. Establish `hX2 : ∀ a b, X2 a b = X1 a b + if a ∈ s then c2 a * X1 p b else 0` using `fun a b => colT_mul_apply p c2 s X1 a b`. Establish `X2_notin : ∀ a b, a ∉ s → X2 a b = X1 a b`. Introduce `a b ha`. Rewrite using `[hX2, if_neg ha, add_zero]`.

Establish `X2_s_p : ∀ a, a ∈ s → X2 a p = 0`. Introduce `a ha`. Rewrite using `[hX2, if_pos ha, hc2]`. Take the linear combination `(-(X1 a p)) * hwu`. Establish `X2_s_low : ∀ a b, a ∈ s → b.val < m → X2 a b = 0`.

Introduce `a b ha hb`. Use `(mem_s a).1 ha` as an intermediate fact. Rewrite using `[hX2, if_pos ha, X1_p_low b hb, mul_zero, add_zero, X1_ne a b (fun h => hps (h ▸ ha))]`. Conclude with `z2 a b hb (nev a b (by omega))`. Use `set c3 : Fin k → A := fun j => -(w * X2 p j) with hc3`.

Use `set Rr : Matrix (Fin k) (Fin k) A := 1 + ∑ j ∈ s, single p j (c3 j) with hRr`. Use `set X3 : Matrix (Fin k) (Fin k) A := X2 * Rr with hX3d`. Establish `hX3 : ∀ a b, X3 a b = X2 a b + if b ∈ s then X2 a p * c3 b else 0` using `fun a b => mul_rowT_apply p c3 s X2 a b`. Use `set d : Fin k → A := fun i => if i = p then w else 1 with hdd`. Use `set X4 : Matrix (Fin k) (Fin k) A := diagonal d * X3 with hX4d`.

Establish `hX4 : ∀ a b, X4 a b = d a * X3 a b` using `fun a b => diagonal_mul d X3 a b`. Establish `hd : ∀ i, IsUnit (d i)`. Introduce `i`. Rewrite using `[hdd]`. Simplify using `only`.

Use `split_ifs`. Conclude with `(hUnit.unit⁻¹).isUnit`. Conclude with `isUnit_one`. Establish `dp : d p = w`. Rewrite using `[hdd]`.

Conclude with `if_pos rfl`. Establish `dne : ∀ a, a ≠ p → d a = 1`. Introduce `a ha`. Rewrite using `[hdd]`. Conclude with `if_neg ha`.

Establish `gL : InG (diagonal d * C * R1)` using `inG_mul (inG_mul (inG_diag d hd) (inG_colT p c2 s hps)) (inG_rowT p c1 s hps)`. Establish `gR : InG Rr` using `inG_rowT p c3 s hps`. Take `⟨g, hg, hgv⟩` from `gL`. Take `⟨h, hh, hhv⟩` from `gR`. Use `⟨g, hg, h, hh, ?_⟩` and prove the remaining obligations.

Establish `e : ((g * X * h : GL (Fin k) A) : Matrix (Fin k) (Fin k) A) = X4`. Rewrite using `[Units.val_mul, Units.val_mul, hgv, hhv, hX4d, hX3d, hX2d, hX1d, hXm]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[e]`. Introduce `a b hab`.

Rewrite using `[hX4]`. Break down `tri a with ha | ha | ha` into its components or cases. Establish `hap : a ≠ p` using `nev a p (by omega)`. Establish `has : a ∉ s` using `fun h => by have := (mem_s a).1 h; omega`. Rewrite using `[dne a hap, one_mul, hX3, X2_notin a p has, X1_ne a p hap, z1 a p ha hap, zero_mul, ite_self, add_zero, X2_notin a b has, X1_ne a b hap]`.

Conclude with `hX a b (Or.inl ha)`. Rewrite using `[ha, dp]`. Break down `tri b with hb | hb | hb` into its components or cases. Rewrite using `[hX3, if_neg (fun h => by have := (mem_s b).1 h; omega), add_zero, X2_notin p b hps, X1_p_low b hb, mul_zero, Matrix.one_apply_ne (nev p b (by omega))]`. Rewrite using `[hb, hX3, if_neg hps, add_zero, X2_notin p p hps, Matrix.one_apply_eq]`.

Conclude with `hwu`. Use `(mem_s b).1 hb` as an intermediate fact. Rewrite using `[hX3, if_pos hb, hc3, X2_notin p b hps, X2_notin p p hps, Matrix.one_apply_ne (nev p b (by omega))]`. Take the linear combination `(-(w * X1 p b)) * huw - (w ^ 2 * X1 p p) * X2_notin p b hps`. Establish `ham` using `(mem_s a).1 ha`.

Establish `hap : a ≠ p` using `nev a p (by omega)`. Establish `hb' : b.val < m + 1`. Break down `hab with h | h` into its components or cases. Use linear arithmetic over natural numbers and integers. Conclude with `h`.

Rewrite using `[dne a hap, one_mul, hX3, if_neg (fun h => by have := (mem_s b).1 h; omega), add_zero]`. Break down `tri b with hb | hb | hb` into its components or cases. Rewrite using `[X2_s_low a b ha hb, Matrix.one_apply_ne (nev a b (by omega))]`. Rewrite using `[hb, X2_s_p a ha, Matrix.one_apply_ne hap]`. Use `(mem_s b).1 hb` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem step (hA : HasStableRangeOne A) (m : ℕ) (hm : m < k) (X : GL (Fin k) A)
    (hX : Red m (X : Matrix (Fin k) (Fin k) A)) :
    ∃ g ∈ Subgroup.closure (genSet A k), ∃ h ∈ Subgroup.closure (genSet A k),
      Red (m + 1) ((g * X * h : GL (Fin k) A) : Matrix (Fin k) (Fin k) A) := by
  have nev : ∀ i j : Fin k, i.val ≠ j.val → i ≠ j := fun i j h e => h (congrArg Fin.val e)
  set p : Fin k := ⟨m, hm⟩ with hpdef
  have hpv : p.val = m := rfl
  set s : Finset (Fin k) := Finset.univ.filter (fun i : Fin k => m < i.val) with hsdef
  have mem_s : ∀ i : Fin k, i ∈ s ↔ m < i.val := by
    intro i
    simp [hsdef]
  have hps : p ∉ s := by
    rw [mem_s, hpv]
    exact lt_irrefl m
  have tri : ∀ i : Fin k, i.val < m ∨ i = p ∨ i ∈ s := by
    intro i
    rcases lt_trichotomy i.val m with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (Fin.ext (h.trans hpv.symm)))
    · exact Or.inr (Or.inr ((mem_s i).2 h))
  set Xm : Matrix (Fin k) (Fin k) A := (X : Matrix (Fin k) (Fin k) A) with hXm
  have z1 : ∀ i j : Fin k, i.val < m → i ≠ j → Xm i j = 0 := fun i j hi hij => by
    rw [hX i j (Or.inl hi), Matrix.one_apply_ne hij]
  have z2 : ∀ i j : Fin k, j.val < m → i ≠ j → Xm i j = 0 := fun i j hj hij => by
    rw [hX i j (Or.inr hj), Matrix.one_apply_ne hij]

  set Y : Matrix (Fin k) (Fin k) A := ((X⁻¹ : GL (Fin k) A) : Matrix (Fin k) (Fin k) A) with hY
  have hYX : Y * Xm = 1 := by
    rw [hY, hXm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hsum : Xm p p * Y p p + (∑ i ∈ s, Xm i p * Y p i) * 1 = 1 := by
    have h1 := congrFun (congrFun hYX p) p
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
    rw [mul_one, ← h1, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin k => m < i.val),
      add_comm]
    congr 1
    · exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    · rw [Finset.sum_eq_single p]
      · exact mul_comm _ _
      · intro i hi hip
        have hi' : ¬ m < i.val := (Finset.mem_filter.1 hi).2
        have hne : i.val ≠ m := fun h => hip (Fin.ext (h.trans hpv.symm))
        rw [z1 i p (by omega) hip, mul_zero]
      · intro hp
        exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ p, by rw [hpv]; exact lt_irrefl m⟩) hp
  obtain ⟨t, ht⟩ := hA _ _ _ _ hsum

  set c1 : Fin k → A := fun i => t * Y p i with hc1
  set R1 : Matrix (Fin k) (Fin k) A := 1 + ∑ i ∈ s, single p i (c1 i) with hR1
  set X1 : Matrix (Fin k) (Fin k) A := R1 * Xm with hX1d
  have hX1 : ∀ a b, X1 a b = Xm a b + if a = p then ∑ i ∈ s, c1 i * Xm i b else 0 :=
    fun a b => rowT_mul_apply p c1 s Xm a b
  have hX1pp : X1 p p = Xm p p + t * ∑ i ∈ s, Xm i p * Y p i := by
    rw [hX1, if_pos rfl, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by rw [hc1]; ring)
  have hUnit : IsUnit (X1 p p) := by
    rw [hX1pp]
    exact ht
  set w : A := ((hUnit.unit⁻¹ : Aˣ) : A) with hw
  have huw : X1 p p * w = 1 := hUnit.mul_val_inv
  have hwu : w * X1 p p = 1 := hUnit.val_inv_mul
  have X1_ne : ∀ a b, a ≠ p → X1 a b = Xm a b := by
    intro a b ha
    rw [hX1, if_neg ha, add_zero]
  have X1_p_low : ∀ b : Fin k, b.val < m → X1 p b = 0 := by
    intro b hb
    rw [hX1, if_pos rfl, z2 p b hb (nev p b (by omega)), zero_add]
    apply Finset.sum_eq_zero
    intro i hi
    have := (mem_s i).1 hi
    rw [z2 i b hb (nev i b (by omega)), mul_zero]

  set c2 : Fin k → A := fun i => -(X1 i p * w) with hc2
  set C : Matrix (Fin k) (Fin k) A := 1 + ∑ i ∈ s, single i p (c2 i) with hC
  set X2 : Matrix (Fin k) (Fin k) A := C * X1 with hX2d
  have hX2 : ∀ a b, X2 a b = X1 a b + if a ∈ s then c2 a * X1 p b else 0 :=
    fun a b => colT_mul_apply p c2 s X1 a b
  have X2_notin : ∀ a b, a ∉ s → X2 a b = X1 a b := by
    intro a b ha
    rw [hX2, if_neg ha, add_zero]
  have X2_s_p : ∀ a, a ∈ s → X2 a p = 0 := by
    intro a ha
    rw [hX2, if_pos ha, hc2]
    linear_combination (-(X1 a p)) * hwu
  have X2_s_low : ∀ a b, a ∈ s → b.val < m → X2 a b = 0 := by
    intro a b ha hb
    have := (mem_s a).1 ha
    rw [hX2, if_pos ha, X1_p_low b hb, mul_zero, add_zero, X1_ne a b (fun h => hps (h ▸ ha))]
    exact z2 a b hb (nev a b (by omega))

  set c3 : Fin k → A := fun j => -(w * X2 p j) with hc3
  set Rr : Matrix (Fin k) (Fin k) A := 1 + ∑ j ∈ s, single p j (c3 j) with hRr
  set X3 : Matrix (Fin k) (Fin k) A := X2 * Rr with hX3d
  have hX3 : ∀ a b, X3 a b = X2 a b + if b ∈ s then X2 a p * c3 b else 0 :=
    fun a b => mul_rowT_apply p c3 s X2 a b

  set d : Fin k → A := fun i => if i = p then w else 1 with hdd
  set X4 : Matrix (Fin k) (Fin k) A := diagonal d * X3 with hX4d
  have hX4 : ∀ a b, X4 a b = d a * X3 a b := fun a b => diagonal_mul d X3 a b
  have hd : ∀ i, IsUnit (d i) := by
    intro i
    rw [hdd]
    dsimp only
    split_ifs
    · exact (hUnit.unit⁻¹).isUnit
    · exact isUnit_one
  have dp : d p = w := by
    rw [hdd]
    exact if_pos rfl
  have dne : ∀ a, a ≠ p → d a = 1 := by
    intro a ha
    rw [hdd]
    exact if_neg ha
  have gL : InG (diagonal d * C * R1) :=
    inG_mul (inG_mul (inG_diag d hd) (inG_colT p c2 s hps)) (inG_rowT p c1 s hps)
  have gR : InG Rr := inG_rowT p c3 s hps
  obtain ⟨g, hg, hgv⟩ := gL
  obtain ⟨h, hh, hhv⟩ := gR
  refine ⟨g, hg, h, hh, ?_⟩
  have e : ((g * X * h : GL (Fin k) A) : Matrix (Fin k) (Fin k) A) = X4 := by
    rw [Units.val_mul, Units.val_mul, hgv, hhv, hX4d, hX3d, hX2d, hX1d, hXm]
    simp only [Matrix.mul_assoc]
  rw [e]
  intro a b hab
  rw [hX4]
  rcases tri a with ha | ha | ha
  · have hap : a ≠ p := nev a p (by omega)
    have has : a ∉ s := fun h => by have := (mem_s a).1 h; omega
    rw [dne a hap, one_mul, hX3, X2_notin a p has, X1_ne a p hap, z1 a p ha hap, zero_mul,
      ite_self, add_zero, X2_notin a b has, X1_ne a b hap]
    exact hX a b (Or.inl ha)
  · rw [ha, dp]
    rcases tri b with hb | hb | hb
    · rw [hX3, if_neg (fun h => by have := (mem_s b).1 h; omega), add_zero, X2_notin p b hps,
        X1_p_low b hb, mul_zero, Matrix.one_apply_ne (nev p b (by omega))]
    · rw [hb, hX3, if_neg hps, add_zero, X2_notin p p hps, Matrix.one_apply_eq]
      exact hwu
    · have := (mem_s b).1 hb
      rw [hX3, if_pos hb, hc3, X2_notin p b hps, X2_notin p p hps,
        Matrix.one_apply_ne (nev p b (by omega))]
      linear_combination (-(w * X1 p b)) * huw - (w ^ 2 * X1 p p) * X2_notin p b hps
  · have ham := (mem_s a).1 ha
    have hap : a ≠ p := nev a p (by omega)
    have hb' : b.val < m + 1 := by
      rcases hab with h | h
      · omega
      · exact h
    rw [dne a hap, one_mul, hX3, if_neg (fun h => by have := (mem_s b).1 h; omega), add_zero]
    rcases tri b with hb | hb | hb
    · rw [X2_s_low a b ha hb, Matrix.one_apply_ne (nev a b (by omega))]
    · rw [hb, X2_s_p a ha, Matrix.one_apply_ne hap]
    · have := (mem_s b).1 hb
      omega

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `X hX`. Establish `hX1 : X = 1` using `Units.ext (Matrix.ext fun i j => by`.

Rewrite using `[Units.val_one]`. Conclude with `hX i j (Or.inl (by have := i.isLt; omega)))`. Rewrite using `[hX1]`. Conclude with `Subgroup.one_mem _`. Consider the case `succ n ih`.

Introduce `X hX`. Distinguish the cases in `hkn : k ≤ n`. Establish `e : k - (n + 1) = k - n` using `by omega`. Rewrite `hX` using `[e]`. Conclude with `ih X hX`.

Establish `hm : k - (n + 1) < k` using `by omega`. Take `⟨g, hg, h, hh, hred⟩` from `step hA (k - (n + 1)) hm X hX`. Establish `e : k - (n + 1) + 1 = k - n` using `by omega`. Rewrite `hred` using `[e]`. Establish `hmem` using `ih _ hred`.

Establish `hX' : X = g⁻¹ * (g * X * h) * h⁻¹` using `by group`. Rewrite using `[hX']`. Conclude with `Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) hmem) (Subgroup.inv_mem _ hh)`.
-/
theorem reduce (hA : HasStableRangeOne A) : ∀ n : ℕ, ∀ X : GL (Fin k) A,
    Red (k - n) (X : Matrix (Fin k) (Fin k) A) → X ∈ Subgroup.closure (genSet A k) := by
  intro n
  induction n with
  | zero =>
    intro X hX
    have hX1 : X = 1 := Units.ext (Matrix.ext fun i j => by
      rw [Units.val_one]
      exact hX i j (Or.inl (by have := i.isLt; omega)))
    rw [hX1]
    exact Subgroup.one_mem _
  | succ n ih =>
    intro X hX
    by_cases hkn : k ≤ n
    · have e : k - (n + 1) = k - n := by omega
      rw [e] at hX
      exact ih X hX
    · have hm : k - (n + 1) < k := by omega
      obtain ⟨g, hg, h, hh, hred⟩ := step hA (k - (n + 1)) hm X hX
      have e : k - (n + 1) + 1 = k - n := by omega
      rw [e] at hred
      have hmem := ih _ hred
      have hX' : X = g⁻¹ * (g * X * h) * h⁻¹ := by group
      rw [hX']
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) hmem) (Subgroup.inv_mem _ hh)

end

/- English proof (translation)
Introduce `A _ hA k X`. Conclude with `reduce hA k X (by`. Introduce `i j h`. It suffices to derive a contradiction. Use the proof step `omega)`.
-/
theorem gl_generated_transvections_diag : ElimSR1 := by
  intro A _ hA k X
  exact reduce hA k X (by
    intro i j h
    exfalso
    omega)

end PI.VolSemiDirect.W.Cj
