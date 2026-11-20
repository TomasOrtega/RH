import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.EulerZetaGammaInvIdentity

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.M Finset

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSPh

def height (P : M.Par) (ρ : M.Ty P) : ℕ := ∑ i, ((ρ i : Fin _) : ℕ)

/- English proof (translation)
Rewrite `hl` using `[Finset.mem_Icc]`. Rewrite using `[Finset.sum_eq_single ⟨l - 1, by omega⟩]`. Rewrite using `[if_pos (by simp; omega)]`. Introduce `b _ hb`. Rewrite using `[if_neg]`.

Introduce `h`. Apply `hb` to reduce the goal to its premises. Use `ext`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem sum_ind (P : M.Par) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) :
    ∑ i : Fin (P.k - 1), (if (i : ℕ) + 1 = l then 1 else 0) = 1 := by
  rw [Finset.mem_Icc] at hl
  rw [Finset.sum_eq_single ⟨l - 1, by omega⟩]
  · rw [if_pos (by simp; omega)]
  · intro b _ hb
    rw [if_neg]
    intro h
    apply hb
    ext
    simp
    omega
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Unfold `height`. Rewrite using `[Finset.sum_congr rfl (fun i _ => hU i), Finset.sum_add_distrib, sum_ind P l hl]`.
-/
theorem up_height (P : M.Par) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (ρ ρ' : M.Ty P) (hU : M.Up P l ρ ρ') :
    height P ρ' = height P ρ + 1 := by
  unfold height
  rw [Finset.sum_congr rfl (fun i _ => hU i), Finset.sum_add_distrib, sum_ind P l hl]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, ((ρ' i : Fin _) : ℕ) ≠ 0 := by`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Apply `h` to reduce the goal to its premises. Unfold `height`.

Conclude with `Finset.sum_eq_zero fun i _ => hall i`. Use `⟨(i : ℕ) + 1, ?_, fun j => if hj : j = i then ⟨((ρ' j : Fin _) : ℕ) - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) (ρ' j).isLt⟩ else ρ' j, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.mem_Icc]`. Use `i.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Introduce `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Simplify using `only [hj, dif_neg, not_false_eq_true]`. Rewrite using `[if_neg]`. Simplify using the standard rewrite rules. Introduce `h2`. Apply `hj` to reduce the goal to its premises.

Use `ext`. Use linear arithmetic over natural numbers and integers.
-/
theorem pred_exists (P : M.Par) (ρ' : M.Ty P) (h : height P ρ' ≠ 0) :
    ∃ l ∈ Icc 1 (P.k - 1), ∃ ρ, M.Up P l ρ ρ' := by
  obtain ⟨i, hi⟩ : ∃ i, ((ρ' i : Fin _) : ℕ) ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply h
    unfold height
    exact Finset.sum_eq_zero fun i _ => hall i
  refine ⟨(i : ℕ) + 1, ?_, fun j => if hj : j = i then ⟨((ρ' j : Fin _) : ℕ) - 1,
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) (ρ' j).isLt⟩ else ρ' j, ?_⟩
  · rw [Finset.mem_Icc]
    have := i.isLt
    omega
  · intro j
    by_cases hj : j = i
    · subst hj
      simp
      omega
    · simp only [hj, dif_neg, not_false_eq_true]
      rw [if_neg]
      · simp
      · intro h2
        apply hj
        ext
        omega

/- English proof (translation)
Establish `key : ∀ n : ℕ, ∃ u : M.Ty P → ℂ, (∀ ρ, ‖u ρ‖ = 1) ∧ ∀ l ∈ Icc 1 (P.k - 1), ∀ ρ ρ', M.Up P l ρ ρ' → height P ρ' ≤ n → u ρ' = w l ρ ρ' * u ρ`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Use `⟨fun _ => 1, fun _ => by simp, fun l hl ρ ρ' hU hh => ?_⟩` and prove the remaining obligations.

Rewrite `hh` using `[up_height P l hl ρ ρ' hU]`. Use linear arithmetic over natural numbers and integers. Consider the case `succ n ih`. Take `⟨u, hu1, hu⟩` from `ih`. Set `u' : M.Ty P → ℂ` to `fun ρ' => if hh : height P ρ' = n + 1 then (let hp := pred_exists P ρ' (by omega) w hp.choose hp.choose_spec.2.choose ρ' * u hp.choose_spec.2.choose) else u ρ'`.

Establish `hu'1 : ∀ ρ, ‖u' ρ‖ = 1`. Introduce `ρ'`. Simplify using `only [u']`. Use `split_ifs with hh`. Establish `hp` using `pred_exists P ρ' (by omega)`.

Rewrite using `[norm_mul, hw1 _ (pred_exists P ρ' (by omega)).choose_spec.1 _ _ (pred_exists P ρ' (by omega)).choose_spec.2.choose_spec, hu1, one_mul]`. Conclude with `hu1 ρ'`. Use `⟨u', hu'1, fun l hl ρ ρ' hU hh => ?_⟩` and prove the remaining obligations. Establish `hhρ` using `up_height P l hl ρ ρ' hU`. Establish `hρ : u' ρ = u ρ`.

Simplify using `only [u']`. Rewrite using `[dif_neg (by omega)]`. Rewrite using `[hρ]`. Distinguish the cases in `hn : height P ρ' = n + 1`. Simplify using `only [u']`.

Rewrite using `[dif_pos hn]`. Use `set hp := pred_exists P ρ' (by omega) with hpdef`. Use `set l0 := hp.choose with hl0`. Establish `hl0m : l0 ∈ Icc 1 (P.k - 1)` using `hp.choose_spec.1`. Use `set ρ0 := hp.choose_spec.2.choose with hρ0`.

Establish `hU0 : M.Up P l0 ρ0 ρ'` using `hp.choose_spec.2.choose_spec`. Use `show w l0 ρ0 ρ' * u ρ0 = w l ρ ρ' * u ρ`. Distinguish the cases in `hll : l0 = l`. Establish `e : ρ0 = ρ` using `Formalism.FourierDecayAlt.P.Mx4.up_inj P l ρ' ρ0 ρ (hll ▸ hU0) hU`. Rewrite using `[e, hll]`.

Take `⟨σ, hσ1, hσ2⟩` from `Formalism.FourierDecayAlt.P.Mx4.up_mixed1 P l0 l (Ne.symm hll) ρ ρ' ρ0 hU hU0`. Establish `h0` using `up_height P l0 hl0m ρ0 ρ' hU0`. Establish `e1 : u ρ0 = w l σ ρ0 * u σ` using `hu l hl σ ρ0 hσ2 (by omega)`. Establish `e2 : u ρ = w l0 σ ρ * u σ` using `hu l0 hl0m σ ρ hσ1 (by omega)`. Establish `hc'` using `hcoc l0 hl0m l hl (Ne.symm hll) σ ρ ρ0 ρ' hσ1 hσ2 hU hU0`.

Rewrite using `[e1, e2, ← mul_assoc, ← mul_assoc, hc']`. Establish `hle : height P ρ' ≤ n` using `by omega`. Simplify using `only [u']`. Rewrite using `[dif_neg hn]`. Conclude with `hu l hl ρ ρ' hU hle`.

Take `⟨u, hu1, hu⟩` from `key (Finset.univ.sup (height P))`. Conclude with `⟨u, hu1, fun l hl ρ ρ' hU => hu l hl ρ ρ' hU (Finset.le_sup (Finset.mem_univ ρ'))⟩`.
-/
theorem phase_exists (P : M.Par) (w : ℕ → M.Ty P → M.Ty P → ℂ)
    (hw1 : ∀ l ∈ Icc 1 (P.k - 1), ∀ ρ ρ', M.Up P l ρ ρ' → ‖w l ρ ρ'‖ = 1)
    (hcoc : ∀ l ∈ Icc 1 (P.k - 1), ∀ j ∈ Icc 1 (P.k - 1), j ≠ l → ∀ ρ ρl ρj ρlj : M.Ty P,
      M.Up P l ρ ρl → M.Up P j ρ ρj → M.Up P j ρl ρlj → M.Up P l ρj ρlj →
        w j ρl ρlj * w l ρ ρl = w l ρj ρlj * w j ρ ρj) :
    ∃ u : M.Ty P → ℂ, (∀ ρ, ‖u ρ‖ = 1) ∧
      ∀ l ∈ Icc 1 (P.k - 1), ∀ ρ ρ', M.Up P l ρ ρ' → u ρ' = w l ρ ρ' * u ρ := by
  classical
  have key : ∀ n : ℕ, ∃ u : M.Ty P → ℂ, (∀ ρ, ‖u ρ‖ = 1) ∧
      ∀ l ∈ Icc 1 (P.k - 1), ∀ ρ ρ', M.Up P l ρ ρ' → height P ρ' ≤ n → u ρ' = w l ρ ρ' * u ρ := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun _ => 1, fun _ => by simp, fun l hl ρ ρ' hU hh => ?_⟩
      rw [up_height P l hl ρ ρ' hU] at hh
      omega
    | succ n ih =>
      obtain ⟨u, hu1, hu⟩ := ih
      let u' : M.Ty P → ℂ := fun ρ' =>
        if hh : height P ρ' = n + 1 then
          (let hp := pred_exists P ρ' (by omega)
           w hp.choose hp.choose_spec.2.choose ρ' * u hp.choose_spec.2.choose)
        else u ρ'
      have hu'1 : ∀ ρ, ‖u' ρ‖ = 1 := by
        intro ρ'
        simp only [u']
        split_ifs with hh
        · have hp := pred_exists P ρ' (by omega)
          rw [norm_mul, hw1 _ (pred_exists P ρ' (by omega)).choose_spec.1 _ _
            (pred_exists P ρ' (by omega)).choose_spec.2.choose_spec, hu1, one_mul]
        · exact hu1 ρ'
      refine ⟨u', hu'1, fun l hl ρ ρ' hU hh => ?_⟩
      have hhρ := up_height P l hl ρ ρ' hU
      have hρ : u' ρ = u ρ := by
        simp only [u']
        rw [dif_neg (by omega)]
      rw [hρ]
      by_cases hn : height P ρ' = n + 1
      · simp only [u']
        rw [dif_pos hn]
        set hp := pred_exists P ρ' (by omega) with hpdef
        set l0 := hp.choose with hl0
        have hl0m : l0 ∈ Icc 1 (P.k - 1) := hp.choose_spec.1
        set ρ0 := hp.choose_spec.2.choose with hρ0
        have hU0 : M.Up P l0 ρ0 ρ' := hp.choose_spec.2.choose_spec
        show w l0 ρ0 ρ' * u ρ0 = w l ρ ρ' * u ρ
        by_cases hll : l0 = l
        · have e : ρ0 = ρ := Formalism.FourierDecayAlt.P.Mx4.up_inj P l ρ' ρ0 ρ (hll ▸ hU0) hU
          rw [e, hll]
        · obtain ⟨σ, hσ1, hσ2⟩ := Formalism.FourierDecayAlt.P.Mx4.up_mixed1 P l0 l (Ne.symm hll) ρ ρ' ρ0 hU hU0

          have h0 := up_height P l0 hl0m ρ0 ρ' hU0
          have e1 : u ρ0 = w l σ ρ0 * u σ := hu l hl σ ρ0 hσ2 (by omega)
          have e2 : u ρ = w l0 σ ρ * u σ := hu l0 hl0m σ ρ hσ1 (by omega)
          have hc' := hcoc l0 hl0m l hl (Ne.symm hll) σ ρ ρ0 ρ' hσ1 hσ2 hU hU0
          rw [e1, e2, ← mul_assoc, ← mul_assoc, hc']
      · have hle : height P ρ' ≤ n := by omega
        simp only [u']
        rw [dif_neg hn]
        exact hu l hl ρ ρ' hU hle
  obtain ⟨u, hu1, hu⟩ := key (Finset.univ.sup (height P))
  exact ⟨u, hu1, fun l hl ρ ρ' hU => hu l hl ρ ρ' hU (Finset.le_sup (Finset.mem_univ ρ'))⟩

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSPh
