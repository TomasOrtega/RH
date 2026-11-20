import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassDivisorBoundStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OneSubTwoDivLeSquarefreeLabelMassStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassRootsNotDistinctLeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MassNotRootsAvoidLeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassHasDivisorOfDegreeLeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassNoLargePrimeFactorLeStatement

noncomputable section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

variable (g : ℕ) [Fact g.Prime]

def tupleMass {ι : Type} [Fintype ι] (N : ℕ) (P : (ι → (ZMod g)[X]) → Prop) : ℝ :=
  ∑ F ∈ Fintype.piFinset fun _ : ι => sqSet g N, if P F then ∏ v, ((torusCard g (F v) : ℝ))⁻¹ else 0

variable {g} {ι : Type} [Fintype ι] {N : ℕ}

/- English proof (translation)
Conclude with `Finset.prod_nonneg fun v _ => inv_nonneg.mpr (Nat.cast_nonneg _)`.
-/
theorem tupleWeight_nonneg (F : ι → (ZMod g)[X]) : 0 ≤ ∏ v, ((torusCard g (F v) : ℝ))⁻¹ := by
  exact Finset.prod_nonneg fun v _ => inv_nonneg.mpr (Nat.cast_nonneg _)

/- English proof (translation)
Unfold `tupleMass`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_le_sum fun F hF => ?_` and prove the remaining obligations. Establish `hw` using `tupleWeight_nonneg F`. Establish `hmem : ∀ v, F v ∈ sqSet g N` using `fun v => Fintype.mem_piFinset.mp hF v`.

Distinguish the cases in `hP : P F`. Rewrite using `[if_pos hP]`. Break down `h F hmem hP with hQ | hR` into its components or cases. Apply the tactic sequence `rw [if_pos hQ]; split_ifs <;> linarith`. Apply the tactic sequence `rw [if_pos hR]; split_ifs <;> linarith`.

Apply the tactic sequence `rw [if_neg hP]; split_ifs <;> linarith`.
-/
theorem tupleMass_le_add {P Q R : (ι → (ZMod g)[X]) → Prop}
    (h : ∀ F, (∀ v, F v ∈ sqSet g N) → P F → Q F ∨ R F) :
    tupleMass g N P ≤ tupleMass g N Q + tupleMass g N R := by
  unfold tupleMass
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun F hF => ?_
  have hw := tupleWeight_nonneg F
  have hmem : ∀ v, F v ∈ sqSet g N := fun v => Fintype.mem_piFinset.mp hF v
  by_cases hP : P F
  · rw [if_pos hP]
    rcases h F hmem hP with hQ | hR
    · rw [if_pos hQ]; split_ifs <;> linarith
    · rw [if_pos hR]; split_ifs <;> linarith
  · rw [if_neg hP]; split_ifs <;> linarith

/- English proof (translation)
Unfold `tupleMass`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_le_sum fun F _ => ?_` and prove the remaining obligations. Establish `hz : ∀ j ∈ s, 0 ≤ (if Q j F then ∏ v, ((torusCard g (F v) : ℝ))⁻¹ else 0)` using `fun j _ => by split_ifs`. Conclude with `tupleWeight_nonneg F`.

Conclude with `le_rfl`. Use `split_ifs with h`. Take `⟨i, hi, hQ⟩` from `h`. Combine the equalities or inequalities in the displayed calculation. Conclude with `Finset.sum_nonneg hz`.
-/
theorem tupleMass_exists_le {κ : Type} (s : Finset κ) (Q : κ → (ι → (ZMod g)[X]) → Prop) :
    tupleMass g N (fun F => ∃ i ∈ s, Q i F) ≤ ∑ i ∈ s, tupleMass g N (Q i) := by
  unfold tupleMass
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun F _ => ?_
  have hz : ∀ j ∈ s, 0 ≤ (if Q j F then ∏ v, ((torusCard g (F v) : ℝ))⁻¹ else 0) := fun j _ => by
    split_ifs
    · exact tupleWeight_nonneg F
    · exact le_rfl
  split_ifs with h
  · obtain ⟨i, hi, hQ⟩ := h
    calc ∏ v, ((torusCard g (F v) : ℝ))⁻¹ = (if Q i F then ∏ v, ((torusCard g (F v) : ℝ))⁻¹ else 0) := by rw [if_pos hQ]
      _ ≤ ∑ j ∈ s, if Q j F then ∏ v, ((torusCard g (F v) : ℝ))⁻¹ else 0 :=
        Finset.single_le_sum (f := fun j => if Q j F then ∏ v, ((torusCard g (F v) : ℝ))⁻¹ else 0) hz hi
  · exact Finset.sum_nonneg hz

/- English proof (translation)
Unfold `tupleMass mass`. Repeatedly rewrite using `[Finset.sum_filter]`. Rewrite using `[Finset.prod_univ_sum]`. Use `Finset.sum_congr rfl fun F _ => ?_` and prove the remaining obligations. Use `split_ifs with h`.

Conclude with `Finset.prod_congr rfl fun v _ => (if_pos (h v)).symm`. Use `push Not at h`. Take `⟨v, hv⟩` from `h`. Conclude with `(Finset.prod_eq_zero (Finset.mem_univ v) (if_neg hv)).symm`.
-/
theorem tupleMass_forall (A : ι → (ZMod g)[X] → Prop) :
    tupleMass g N (fun F => ∀ v, A v (F v)) = ∏ v, mass g N (A v) := by
  unfold tupleMass mass
  simp_rw [Finset.sum_filter]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun F _ => ?_
  split_ifs with h
  · exact Finset.prod_congr rfl fun v _ => (if_pos (h v)).symm
  · push Not at h
    obtain ⟨v, hv⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_univ v) (if_neg hv)).symm

/- English proof (translation)
Establish `hm : ∀ B : (ZMod g)[X] → Prop, 0 ≤ mass g N B` using `fun B => by`. Unfold `mass`. Conclude with `Finset.sum_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)`. Establish `key : tupleMass g N (fun F : ι → (ZMod g)[X] => A (F v)) = tupleMass g N (fun F => ∀ w, (if w = v then A else fun _ => True) (F w))`. Unfold `tupleMass`.

Use `Finset.sum_congr rfl fun F _ => ?_` and prove the remaining obligations. Apply the tactic sequence `have hiff : A (F v) ↔ ∀ w, (if w = v then A else fun _ => True) (F w) := ⟨fun h w => by by_cases hw : w = v <;> simp_all, fun h => by simpa using h v⟩`. Distinguish the cases in `h : A (F v)`. Rewrite using `[if_pos h, if_pos (hiff.mp h)]`. Rewrite using `[if_neg h, if_neg (mt hiff.mpr h)]`.

Rewrite using `[key, tupleMass_forall, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v), if_pos rfl]`. Establish `hrest : ∏ w ∈ Finset.univ.erase v, mass g N (if w = v then A else fun _ => True) ≤ 1`. Apply `Finset.prod_le_one` to reduce the goal to its premises. Conclude with `fun w _ => hm _`. Introduce `w hw`.

Rewrite using `[if_neg (Finset.ne_of_mem_erase hw)]`. Conclude with `h1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem tupleMass_single_le (h1 : (mass g N fun _ => True) ≤ 1) (v : ι) (A : (ZMod g)[X] → Prop) :
    tupleMass g N (fun F : ι → (ZMod g)[X] => A (F v)) ≤ mass g N A := by
  have hm : ∀ B : (ZMod g)[X] → Prop, 0 ≤ mass g N B := fun B => by
    unfold mass
    exact Finset.sum_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)
  have key : tupleMass g N (fun F : ι → (ZMod g)[X] => A (F v)) =
      tupleMass g N (fun F => ∀ w, (if w = v then A else fun _ => True) (F w)) := by
    unfold tupleMass
    refine Finset.sum_congr rfl fun F _ => ?_
    have hiff : A (F v) ↔ ∀ w, (if w = v then A else fun _ => True) (F w) :=
      ⟨fun h w => by by_cases hw : w = v <;> simp_all, fun h => by simpa using h v⟩
    by_cases h : A (F v)
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (mt hiff.mpr h)]
  rw [key, tupleMass_forall, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v), if_pos rfl]
  have hrest : ∏ w ∈ Finset.univ.erase v, mass g N (if w = v then A else fun _ => True) ≤ 1 := by
    apply Finset.prod_le_one
    · exact fun w _ => hm _
    · intro w hw
      rw [if_neg (Finset.ne_of_mem_erase hw)]
      exact h1
  calc mass g N A * _ ≤ mass g N A * 1 := mul_le_mul_of_nonneg_left hrest (hm A)
    _ = _ := mul_one _

/- English proof (translation)
Introduce `g _ N m q d ι _ ch hN hg hqd`. Establish `hm : ∀ B : (ZMod g)[X] → Prop, 0 ≤ mass g N B` using `fun B => by`. Unfold `mass`. Conclude with `Finset.sum_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)`. Establish `h1 : (mass g N fun _ => True) ≤ 1` using `(GlobalTheory.T.squarefreeLabelTorusMass_divisor_bound g).1 N`.

Establish `hg0 : (0 : ℝ) < g` using `by exact_mod_cast (Fact.out : g.Prime).pos`. Establish `hg4 : (4096 : ℝ) ≤ g` using `by exact_mod_cast hg`. Establish `hN' : (100000 : ℝ) ≤ N` using `by exact_mod_cast hN`. Establish `hall : 1 - 2 * (Fintype.card ι : ℝ) / g ≤ tupleMass g N (fun _ : ι → (ZMod g)[X] => True)`. Establish `e` using `tupleMass_forall (g := g) (N := N) (fun (_ : ι) (_ : (ZMod g)[X]) => True)`.

Simplify using `only [implies_true] at e`. Rewrite using `[e]`. Establish `h2 : 0 ≤ 1 - 2 / (g : ℝ)`. Rewrite using `[sub_nonneg, div_le_one hg0]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h3 : (-2 : ℝ) ≤ -2 / g`. Rewrite using `[le_div_iff₀ hg0]`. Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation. Establish `hsq : ∀ f ∈ sqSet g N, (f.Monic ∧ f.natDegree = N ∧ f.coeff 0 ≠ 0) ∧ Squarefree f`.

Introduce `f hf`. Unfold `sqSet at hf`. Rewrite `hf` using `[Finset.mem_filter, Finset.mem_image]`. Take `⟨⟨c, -, rfl⟩, hsf, hc0⟩` from `hf`. Establish `hdeg` using `degree_sum_fin_lt c`.

Use `⟨⟨monic_X_pow_add hdeg, ?_, hc0⟩, hsf⟩` and prove the remaining obligations. Rewrite using `[natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]`. Establish `hE1 : tupleMass g N (fun F : ι → (ZMod g)[X] => ∃ v ∈ Finset.univ, ¬ RootsApart g N (F v)) ≤ (Fintype.card ι : ℝ) * (23 * Real.log g / Real.sqrt g)`. Combine the equalities or inequalities in the displayed calculation. Establish `hE2 : ∀ c : ι → Fin m → (ZMod g)ˣ, tupleMass g N (fun F : ι → (ZMod g)[X] => ∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g (c p.1 p.2) (F p.1)) ≤ (Fintype.card ι : ℝ) * m * (1 / (4 * ((min q d : ℕ) : ℝ)) + (1 + Real.log N) / ((g : ℝ) - 1))`.

Introduce `c`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hE4 : tupleMass g N (fun F : ι → (ZMod g)[X] => ∃ a ∈ Finset.Icc 1 (N / 2), ∀ v, HasDiv g a (F v)) ≤ (N : ℝ) / 2 * (7 / 8) ^ Fintype.card ι`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun a ha => ?_` and prove the remaining obligations. Rewrite `ha` using `[Finset.mem_Icc]`. Combine the equalities or inequalities in the displayed calculation.

Use `_ = ((N / 2 : ℕ) : ℝ) * (7 / 8) ^ Fintype.card ι := by`. Rewrite using `[Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]`. Use `_ ≤ _ := mul_le_mul_of_nonneg_right Nat.cast_div_le (by positivity)`. Establish `hL : (1 : ℝ) ≤ 10 * Real.log N`. Establish `: (1 : ℝ) ≤ Real.log N`.

Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hE5 : tupleMass g N (fun F : ι → (ZMod g)[X] => ∀ v, ¬ HasPrimeFactor g N (F v)) ≤ Real.exp (-((Fintype.card ι : ℝ) / (10 * Real.log N)))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.prod_const, Finset.card_univ]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ (Real.exp (-(1 / (10 * Real.log N)))) ^ Fintype.card ι := by`. Use `pow_le_pow_left₀ ?_ ?_ _` and prove the remaining obligations. Establish `: 1 / (10 * Real.log N) ≤ 1` using `by rw [div_le_one (by linarith)]; exact hL`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the linear relations using `[Real.add_one_le_exp (-(1 / (10 * Real.log N)))]`. Use `_ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring`. Establish `hsplit : ∀ F : ι → (ZMod g)[X], (∀ v, F v ∈ sqSet g N) → True → Good g N ch F ∨ ((∃ v ∈ Finset.univ, ¬ RootsApart g N (F v)) ∨ ((∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g (ch p.1 p.2) (F p.1)) ∨ ((∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g ((fun v j = …`. Introduce `F hF _`. Assume the negation of the conclusion as `hcon`.

Simplify using `only [not_or] at hcon`. Take `⟨hG, h1', h2', h3', h4', h5'⟩` from `hcon`. Apply `hG` to reduce the goal to its premises. Establish `hA : ∀ v, RootsApart g N (F v)` using `fun v => Classical.byContradiction fun h => h1' ⟨v, Finset.mem_univ _, h⟩`. Establish `hB : ∀ v j, RootsAvoid g (ch v j) (F v)` using `fun v j => Classical.byContradiction fun h => h2' ⟨(v, j), Finset.mem_univ _, h⟩`.

Establish `hC : ∀ v j, RootsAvoid g (ch v j)⁻¹ (F v)` using `fun v j => Classical.byContradiction fun h => h3' ⟨(v, j), Finset.mem_univ _, h⟩`. Establish `hD : ∀ a : ℕ, 1 ≤ a → 2 * a ≤ N → ∃ v, ¬ HasDiv g a (F v)` using `fun a ha1 ha2 => by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `h4' ⟨a, Finset.mem_Icc.mpr ⟨ha1, by omega⟩, h⟩`.

Establish `hE : ∃ v, HasPrimeFactor g N (F v)`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `h5' h`. Unfold `Good Formalism.CyclotomicNorms.IsGood`.

Conclude with `⟨⟨fun v => (hsq _ (hF v)).1, fun v => (hsq _ (hF v)).2, fun l hl hl' v => hA v l hl hl', fun l hl hlg v j => hB v j l hl hlg, hD, hE⟩, ⟨fun v => (hsq _ (hF v)).1, fun v => (hsq _ (hF v)).2, fun l hl hl' v => hA v l hl hl', fun l hl hlg v j => hC v j l hl hlg, hD, hE⟩⟩`. Establish `hor : ∀ {P Q : (ι → (ZMod g)[X]) → Prop}, tupleMass g N (fun F => P F ∨ Q F) ≤ tupleMass g N P + tupleMass g N Q` using `fun {_ _} => tupleMass_le_add fun _ _ h => h`. Establish `hgood : tupleMass g N (Good g N ch) = ∑ F ∈ goodSet g N ch, ∏ v, ((torusCard g (F v) : ℝ))⁻¹`. Unfold `tupleMass goodSet`. Rewrite using `[Finset.sum_filter]`.

Establish `s0` using `tupleMass_le_add hsplit`. Establish `s1` using `hor (P := fun F => (∃ v ∈ Finset.univ, ¬ RootsApart g N (F v))) (Q := fun F => (∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g (ch p.1 p.2) (F p.1)) ∨ ((∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g ((fun v j => (ch v j)⁻¹) p.1 p.2) (F p.1)) ∨ ((∃ a ∈ Finset. …`. Establish `s2` using `hor (P := fun F => (∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g (ch p.1 p.2) (F p.1))) (Q := fun F => (∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g ((fun v j => (ch v j)⁻¹) p.1 p.2) (F p.1)) ∨ ((∃ a ∈ Finset.Icc 1 (N / 2), ∀ v, HasDiv g a (F v)) ∨ (∀ v, ¬ …`. Establish `s3` using `hor (P := fun F => (∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g ((fun v j => (ch v j)⁻¹) p.1 p.2) (F p.1))) (Q := fun F => (∃ a ∈ Finset.Icc 1 (N / 2), ∀ v, HasDiv g a (F v)) ∨ (∀ v, ¬ HasPrimeFactor g N (F v)))`. Establish `s4` using `hor (P := fun F => (∃ a ∈ Finset.Icc 1 (N / 2), ∀ v, HasDiv g a (F v))) (Q := fun F => (∀ v, ¬ HasPrimeFactor g N (F v)))`.

Use `beta_reduce at s0 s1 s2 s3 s4`. Establish `b2` using `hE2 ch`. Establish `b3` using `hE2 (fun v j => (ch v j)⁻¹)`. Establish `hb4` using `s4.trans (add_le_add hE4 hE5)`. Establish `hb3` using `s3.trans (add_le_add b3 hb4)`.

Establish `hb2` using `s2.trans (add_le_add b2 hb3)`. Establish `hb1` using `s1.trans (add_le_add hE1 hb2)`. Establish `hb0` using `s0.trans (add_le_add le_rfl hb1)`. Rewrite using `[← hgood]`. Unfold `badBound`.

Rewrite using `[Real.rpow_natCast]`. Use `ring_nf at hall hb0 ⊢`. Combine the linear relations using `only [hall, hb0]`.
-/
theorem goodSet_weight_ge : ∀ (g : ℕ) [Fact g.Prime], ∀ (N m q d : ℕ) (ι : Type) [Fintype ι] (ch : ι → Fin m → (ZMod g)ˣ), 100000 ≤ N → 2 ^ 12 ≤ g → (q.Prime ∧ d.Prime ∧ q ≠ 2 ∧ d ≠ 2 ∧ q ≠ d ∧ 16 ≤ max q d ∧ 16 * q * d ∣ g - 1) → 1 - (badBound g (Fintype.card ι) m N ((min q d : ℕ) : ℝ) - (Fintype.card ι : ℝ) / g) ≤ ∑ F ∈ goodSet g N ch, ∏ v, ((torusCard g (F v) : ℝ))⁻¹ := by
  intro g _ N m q d ι _ ch hN hg hqd
  have hm : ∀ B : (ZMod g)[X] → Prop, 0 ≤ mass g N B := fun B => by
    unfold mass
    exact Finset.sum_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)
  have h1 : (mass g N fun _ => True) ≤ 1 := (GlobalTheory.T.squarefreeLabelTorusMass_divisor_bound g).1 N
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (Fact.out : g.Prime).pos
  have hg4 : (4096 : ℝ) ≤ g := by exact_mod_cast hg
  have hN' : (100000 : ℝ) ≤ N := by exact_mod_cast hN
  have hall : 1 - 2 * (Fintype.card ι : ℝ) / g ≤ tupleMass g N (fun _ : ι → (ZMod g)[X] => True) := by
    have e := tupleMass_forall (g := g) (N := N) (fun (_ : ι) (_ : (ZMod g)[X]) => True)
    simp only [implies_true] at e
    rw [e]
    have h2 : 0 ≤ 1 - 2 / (g : ℝ) := by
      rw [sub_nonneg, div_le_one hg0]; linarith
    have h3 : (-2 : ℝ) ≤ -2 / g := by
      rw [le_div_iff₀ hg0]; nlinarith
    calc 1 - 2 * (Fintype.card ι : ℝ) / g = 1 + (Fintype.card ι : ℝ) * (-2 / g) := by ring
      _ ≤ (1 + (-2 / (g : ℝ))) ^ Fintype.card ι := one_add_mul_le_pow h3 _
      _ = ∏ _v : ι, (1 - 2 / (g : ℝ)) := by rw [Finset.prod_const, Finset.card_univ]; ring
      _ ≤ ∏ _v : ι, mass g N (fun _ => True) :=
        Finset.prod_le_prod (fun _ _ => h2) (fun _ _ => GlobalTheory.T.one_sub_two_div_le_squarefreeLabelMass g N)
  have hsq : ∀ f ∈ sqSet g N, (f.Monic ∧ f.natDegree = N ∧ f.coeff 0 ≠ 0) ∧ Squarefree f := by
    intro f hf
    unfold sqSet at hf
    rw [Finset.mem_filter, Finset.mem_image] at hf
    obtain ⟨⟨c, -, rfl⟩, hsf, hc0⟩ := hf
    have hdeg := degree_sum_fin_lt c
    refine ⟨⟨monic_X_pow_add hdeg, ?_, hc0⟩, hsf⟩
    rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
  have hE1 : tupleMass g N (fun F : ι → (ZMod g)[X] => ∃ v ∈ Finset.univ, ¬ RootsApart g N (F v)) ≤
      (Fintype.card ι : ℝ) * (23 * Real.log g / Real.sqrt g) := by
    calc _ ≤ ∑ v ∈ Finset.univ, tupleMass g N (fun F : ι → (ZMod g)[X] => ¬ RootsApart g N (F v)) :=
          tupleMass_exists_le (Finset.univ : Finset ι) (fun (v : ι) (F : ι → (ZMod g)[X]) => ¬ RootsApart g N (F v))
      _ ≤ ∑ _v ∈ (Finset.univ : Finset ι), (23 * Real.log g / Real.sqrt g) :=
          Finset.sum_le_sum fun v _ => (tupleMass_single_le h1 v _).trans (GlobalTheory.T.squarefreeLabelTorusMass_rootsNotDistinct_le g N hg)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hE2 : ∀ c : ι → Fin m → (ZMod g)ˣ,
      tupleMass g N (fun F : ι → (ZMod g)[X] =>
        ∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g (c p.1 p.2) (F p.1)) ≤
      (Fintype.card ι : ℝ) * m * (1 / (4 * ((min q d : ℕ) : ℝ)) + (1 + Real.log N) / ((g : ℝ) - 1)) := by
    intro c
    calc _ ≤ ∑ p ∈ (Finset.univ : Finset (ι × Fin m)),
            tupleMass g N (fun F : ι → (ZMod g)[X] => ¬ RootsAvoid g (c p.1 p.2) (F p.1)) :=
          tupleMass_exists_le (Finset.univ : Finset (ι × Fin m))
            (fun (p : ι × Fin m) (F : ι → (ZMod g)[X]) => ¬ RootsAvoid g (c p.1 p.2) (F p.1))
      _ ≤ ∑ _p ∈ (Finset.univ : Finset (ι × Fin m)),
            (1 / (4 * ((min q d : ℕ) : ℝ)) + (1 + Real.log N) / ((g : ℝ) - 1)) :=
          Finset.sum_le_sum fun p _ => (tupleMass_single_le h1 p.1 _).trans (GlobalTheory.T.mass_not_rootsAvoid_le' g N q d _ hqd)
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  have hE4 : tupleMass g N (fun F : ι → (ZMod g)[X] => ∃ a ∈ Finset.Icc 1 (N / 2), ∀ v, HasDiv g a (F v)) ≤
      (N : ℝ) / 2 * (7 / 8) ^ Fintype.card ι := by
    calc _ ≤ ∑ a ∈ Finset.Icc 1 (N / 2), tupleMass g N (fun F : ι → (ZMod g)[X] => ∀ v, HasDiv g a (F v)) :=
          tupleMass_exists_le (Finset.Icc 1 (N / 2)) (fun (a : ℕ) (F : ι → (ZMod g)[X]) => ∀ v, HasDiv g a (F v))
      _ = ∑ a ∈ Finset.Icc 1 (N / 2), ∏ _v : ι, mass g N (HasDiv g a) :=
          Finset.sum_congr rfl fun a _ => tupleMass_forall (fun _ => HasDiv g a)
      _ ≤ ∑ _a ∈ Finset.Icc 1 (N / 2), ((7 : ℝ) / 8) ^ Fintype.card ι := by
          refine Finset.sum_le_sum fun a ha => ?_
          rw [Finset.mem_Icc] at ha
          calc ∏ _v : ι, mass g N (HasDiv g a) ≤ ∏ _v : ι, ((7 : ℝ) / 8) :=
                Finset.prod_le_prod (fun _ _ => hm _) (fun _ _ => GlobalTheory.T.squarefreeLabelTorusMass_hasDivisorOfDegree_le g N a (by omega) (by omega))
            _ = _ := by rw [Finset.prod_const, Finset.card_univ]
      _ = ((N / 2 : ℕ) : ℝ) * (7 / 8) ^ Fintype.card ι := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
      _ ≤ _ := mul_le_mul_of_nonneg_right Nat.cast_div_le (by positivity)
  have hL : (1 : ℝ) ≤ 10 * Real.log N := by
    have : (1 : ℝ) ≤ Real.log N :=
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log N := Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    linarith
  have hE5 : tupleMass g N (fun F : ι → (ZMod g)[X] => ∀ v, ¬ HasPrimeFactor g N (F v)) ≤
      Real.exp (-((Fintype.card ι : ℝ) / (10 * Real.log N))) := by
    calc _ = ∏ _v : ι, mass g N (fun f => ¬ HasPrimeFactor g N f) :=
          tupleMass_forall (fun _ f => ¬ HasPrimeFactor g N f)
      _ ≤ ∏ _v : ι, (1 - 1 / (10 * Real.log N)) :=
          Finset.prod_le_prod (fun _ _ => hm _) (fun _ _ => GlobalTheory.T.squarefreeLabelTorusMass_no_large_prime_factor_le g N hN)
      _ = (1 + (-(1 / (10 * Real.log N)))) ^ Fintype.card ι := by
          rw [Finset.prod_const, Finset.card_univ]; ring
      _ ≤ (Real.exp (-(1 / (10 * Real.log N)))) ^ Fintype.card ι := by
          refine pow_le_pow_left₀ ?_ ?_ _
          · have : 1 / (10 * Real.log N) ≤ 1 := by rw [div_le_one (by linarith)]; exact hL
            linarith
          · linarith [Real.add_one_le_exp (-(1 / (10 * Real.log N)))]
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hsplit : ∀ F : ι → (ZMod g)[X], (∀ v, F v ∈ sqSet g N) → True →
      Good g N ch F ∨
      ((∃ v ∈ Finset.univ, ¬ RootsApart g N (F v)) ∨
      ((∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g (ch p.1 p.2) (F p.1)) ∨
      ((∃ p ∈ (Finset.univ : Finset (ι × Fin m)),
          ¬ RootsAvoid g ((fun v j => (ch v j)⁻¹) p.1 p.2) (F p.1)) ∨
      ((∃ a ∈ Finset.Icc 1 (N / 2), ∀ v, HasDiv g a (F v)) ∨
      (∀ v, ¬ HasPrimeFactor g N (F v)))))) := by
    intro F hF _
    by_contra hcon
    simp only [not_or] at hcon
    obtain ⟨hG, h1', h2', h3', h4', h5'⟩ := hcon
    apply hG
    have hA : ∀ v, RootsApart g N (F v) := fun v =>
      Classical.byContradiction fun h => h1' ⟨v, Finset.mem_univ _, h⟩
    have hB : ∀ v j, RootsAvoid g (ch v j) (F v) := fun v j =>
      Classical.byContradiction fun h => h2' ⟨(v, j), Finset.mem_univ _, h⟩
    have hC : ∀ v j, RootsAvoid g (ch v j)⁻¹ (F v) := fun v j =>
      Classical.byContradiction fun h => h3' ⟨(v, j), Finset.mem_univ _, h⟩
    have hD : ∀ a : ℕ, 1 ≤ a → 2 * a ≤ N → ∃ v, ¬ HasDiv g a (F v) := fun a ha1 ha2 => by
      by_contra h
      push Not at h
      exact h4' ⟨a, Finset.mem_Icc.mpr ⟨ha1, by omega⟩, h⟩
    have hE : ∃ v, HasPrimeFactor g N (F v) := by
      by_contra h
      push Not at h
      exact h5' h
    unfold Good Formalism.CyclotomicNorms.IsGood
    exact ⟨⟨fun v => (hsq _ (hF v)).1, fun v => (hsq _ (hF v)).2,
        fun l hl hl' v => hA v l hl hl', fun l hl hlg v j => hB v j l hl hlg, hD, hE⟩,
      ⟨fun v => (hsq _ (hF v)).1, fun v => (hsq _ (hF v)).2,
        fun l hl hl' v => hA v l hl hl', fun l hl hlg v j => hC v j l hl hlg, hD, hE⟩⟩
  have hor : ∀ {P Q : (ι → (ZMod g)[X]) → Prop},
      tupleMass g N (fun F => P F ∨ Q F) ≤ tupleMass g N P + tupleMass g N Q :=
    fun {_ _} => tupleMass_le_add fun _ _ h => h
  have hgood : tupleMass g N (Good g N ch) = ∑ F ∈ goodSet g N ch, ∏ v, ((torusCard g (F v) : ℝ))⁻¹ := by
    unfold tupleMass goodSet
    rw [Finset.sum_filter]
  have s0 := tupleMass_le_add hsplit
  have s1 := hor (P := fun F => (∃ v ∈ Finset.univ, ¬ RootsApart g N (F v)))
    (Q := fun F => (∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g (ch p.1 p.2) (F p.1)) ∨ ((∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g ((fun v j => (ch v j)⁻¹) p.1 p.2) (F p.1)) ∨ ((∃ a ∈ Finset.Icc 1 (N / 2), ∀ v, HasDiv g a (F v)) ∨ (∀ v, ¬ HasPrimeFactor g N (F v)))))
  have s2 := hor (P := fun F => (∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g (ch p.1 p.2) (F p.1)))
    (Q := fun F => (∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g ((fun v j => (ch v j)⁻¹) p.1 p.2) (F p.1)) ∨ ((∃ a ∈ Finset.Icc 1 (N / 2), ∀ v, HasDiv g a (F v)) ∨ (∀ v, ¬ HasPrimeFactor g N (F v))))
  have s3 := hor (P := fun F => (∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g ((fun v j => (ch v j)⁻¹) p.1 p.2) (F p.1)))
    (Q := fun F => (∃ a ∈ Finset.Icc 1 (N / 2), ∀ v, HasDiv g a (F v)) ∨ (∀ v, ¬ HasPrimeFactor g N (F v)))
  have s4 := hor (P := fun F => (∃ a ∈ Finset.Icc 1 (N / 2), ∀ v, HasDiv g a (F v)))
    (Q := fun F => (∀ v, ¬ HasPrimeFactor g N (F v)))
  beta_reduce at s0 s1 s2 s3 s4
  have b2 := hE2 ch
  have b3 := hE2 (fun v j => (ch v j)⁻¹)
  have hb4 := s4.trans (add_le_add hE4 hE5)
  have hb3 := s3.trans (add_le_add b3 hb4)
  have hb2 := s2.trans (add_le_add b2 hb3)
  have hb1 := s1.trans (add_le_add hE1 hb2)
  have hb0 := s0.trans (add_le_add le_rfl hb1)
  rw [← hgood]
  unfold badBound
  rw [Real.rpow_natCast]
  ring_nf at hall hb0 ⊢
  linarith only [hall, hb0]

end GlobalTheory.BadShare
