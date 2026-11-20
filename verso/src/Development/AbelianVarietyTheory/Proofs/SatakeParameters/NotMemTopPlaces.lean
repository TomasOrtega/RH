import Mathlib
import Formalism.SharpRestriction.ParConsts
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.LongRows

/- English proof (translation)
Introduce `hm`. Unfold `Host.topPlaces at hm`. Take `⟨t, ht, hte⟩` from `Finset.mem_image.1 hm`. Unfold `tauPl at hte`. Rewrite `hte` using `[Equiv.apply_symm_apply]`.

Take `⟨b, s⟩` from `z`. Consider the cases of `b with`. Consider the case `true`. Establish `h1` using `congrArg (fun g : D.R.GG => g.1.1) hte`. Simplify using `[plGG, Formalism.HC.Frame.tau1, Formalism.HC.Frame.tau2] at h1`.

Consider the case `false`. Establish `h1` using `congrArg (fun g : D.R.GG => g.2) hte`. Simplify using `only [plGG, Formalism.HC.Frame.tau1, Bool.false_eq_true, if_false] at h1`. Use `D.R.toFrame.iota_bijective.1 h1` as an intermediate fact. Substitute `this` using the available equality.

Conclude with `h ⟨rfl, ht⟩`.
-/
theorem not_mem_topPlaces (D : D7) (z : Bool × HH D) (h : ¬ IsTopPl D z) :
    (D.eTau (tauPl D z) : D.R.GG) ∉ D.host.topPlaces := by
  intro hm
  unfold Host.topPlaces at hm
  obtain ⟨t, ht, hte⟩ := Finset.mem_image.1 hm
  unfold tauPl at hte
  rw [Equiv.apply_symm_apply] at hte
  obtain ⟨b, s⟩ := z
  cases b with
  | true =>
    have h1 := congrArg (fun g : D.R.GG => g.1.1) hte
    simp [plGG, Formalism.HC.Frame.tau1, Formalism.HC.Frame.tau2] at h1
  | false =>
    have h1 := congrArg (fun g : D.R.GG => g.2) hte
    simp only [plGG, Formalism.HC.Frame.tau1, Bool.false_eq_true, if_false] at h1
    have := D.R.toFrame.iota_bijective.1 h1
    subst this
    exact h ⟨rfl, ht⟩

/- English proof (translation)
Establish `hw : wPl D (j + 1) z = (((D.hcW u (tauPl D z)).e ⟨j, hj⟩ : ℚ) : ℝ)`. Unfold `wPl wj`. Rewrite using `[dif_pos (by simpa using hj), D.hcW_e]`. Both sides reduce to the same expression. Establish `h1 : D.R.N j + (D.R.t + 1) ≤ D.R.N D.R.m`.

Unfold `Ranks.N`. Establish `: (j + 1) * (D.R.t + 1) ≤ D.R.m * (D.R.t + 1)` using `Nat.mul_le_mul_right _ hj`. Rewrite `this` using `[Nat.add_mul]`. Use linear arithmetic over natural numbers and integers. Establish `h2 : r < D.R.N j` using `by unfold Ranks.N; omega`.

Establish `h1' : (D.R.N j : ℝ) + (D.R.t + 1) ≤ D.R.N D.R.m` using `by exact_mod_cast h1`. Establish `h2' : (r : ℝ) < D.R.N j` using `by exact_mod_cast h2`. Establish `ht : (0 : ℝ) ≤ D.R.t` using `Nat.cast_nonneg _`. Establish `hr0 : (0 : ℝ) ≤ r` using `Nat.cast_nonneg _`. Rewrite using `[RowWeightLemmas.nuRow_head D u j hj _ r hr, hw]`.

Use `push_cast`. Apply the tactic sequence `constructor <;> linarith`.
-/
theorem row_bounds (D : D7) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m) (z : Bool × HH D) (r : ℕ) (hr : r < D.R.k) :
    wPl D (j + 1) z + (((D.hcW u (tauPl D z)).u ⟨r, hr⟩ : ℚ) : ℝ) - D.R.N D.R.m < DV.nuRow D u (j + 1) (tauPl D z) r ∧
    DV.nuRow D u (j + 1) (tauPl D z) r < wPl D (j + 1) z + (((D.hcW u (tauPl D z)).u ⟨r, hr⟩ : ℚ) : ℝ) := by
  have hw : wPl D (j + 1) z = (((D.hcW u (tauPl D z)).e ⟨j, hj⟩ : ℚ) : ℝ) := by
    unfold wPl wj
    rw [dif_pos (by simpa using hj), D.hcW_e]
    rfl
  have h1 : D.R.N j + (D.R.t + 1) ≤ D.R.N D.R.m := by
    unfold Ranks.N
    have : (j + 1) * (D.R.t + 1) ≤ D.R.m * (D.R.t + 1) := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul] at this
    omega
  have h2 : r < D.R.N j := by unfold Ranks.N; omega
  have h1' : (D.R.N j : ℝ) + (D.R.t + 1) ≤ D.R.N D.R.m := by exact_mod_cast h1
  have h2' : (r : ℝ) < D.R.N j := by exact_mod_cast h2
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  rw [RowWeightLemmas.nuRow_head D u j hj _ r hr, hw]
  push_cast
  constructor <;> linarith

/- English proof (translation)
Establish `hk : 5 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega`. Distinguish the cases in `h0 : r = 0`. Substitute `h0` using the available equality. Rewrite using `[if_pos rfl, D.hcW_first u τ hr]`. Establish `h1` using `P.cloud_place_bound τ (by omega) hτ`.

Establish `h2` using `L.cloud_v τ ⟨0, by omega⟩`. Establish `h3 : (((D.hc τ).v ⟨0, by omega⟩ : ℚ) : ℝ) < (((D.hc τ).u ⟨0, hr⟩ : ℚ) : ℝ)`. Conclude with `(D.hc τ).u_gt_v ⟨0, by omega⟩` after adjusting the coercions. Move the coercions through the operations in `at h1`. Apply the tactic sequence `constructor <;> linarith [h2.1, h2.2]`.

Rewrite using `[if_neg h0]`. Distinguish the cases in `hl : r + 1 < D.R.k`. Use `L.cloud_u u τ ⟨r, hr⟩ (by show 1 ≤ r; omega) hl` as an intermediate fact. Apply the tactic sequence `constructor <;> linarith [this.1, this.2]`. Take `rfl : r = D.R.k - 1` from `by omega`.

Rewrite using `[D.hcW_last u τ (by omega), P.uk_extreme τ (by omega) hτ]`. Establish `h2` using `L.cloud_v τ ⟨D.R.k - 2, by omega⟩`. Use `push_cast`. Apply the tactic sequence `constructor <;> linarith [h2.1, h2.2]`.
-/
theorem u_bounds_off {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (u : D.what₂.Word) (τ : D.what₂.Tau)
    (hτ : (D.eTau τ : D.R.GG) ∉ D.host.topPlaces) (r : ℕ) (hr : r < D.R.k) :
    -(1 / 2 : ℝ) ≤ (((D.hcW u τ).u ⟨r, hr⟩ : ℚ) : ℝ) ∧
      (((D.hcW u τ).u ⟨r, hr⟩ : ℚ) : ℝ) ≤ if r = 0 then 3 * L.Sc else L.Sc := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  by_cases h0 : r = 0
  · subst h0
    rw [if_pos rfl, D.hcW_first u τ hr]
    have h1 := P.cloud_place_bound τ (by omega) hτ
    have h2 := L.cloud_v τ ⟨0, by omega⟩
    have h3 : (((D.hc τ).v ⟨0, by omega⟩ : ℚ) : ℝ) < (((D.hc τ).u ⟨0, hr⟩ : ℚ) : ℝ) := by
      exact_mod_cast (D.hc τ).u_gt_v ⟨0, by omega⟩
    push_cast at h1
    constructor <;> linarith [h2.1, h2.2]
  · rw [if_neg h0]
    by_cases hl : r + 1 < D.R.k
    · have := L.cloud_u u τ ⟨r, hr⟩ (by show 1 ≤ r; omega) hl
      constructor <;> linarith [this.1, this.2]
    · obtain rfl : r = D.R.k - 1 := by omega
      rw [D.hcW_last u τ (by omega), P.uk_extreme τ (by omega) hτ]
      have h2 := L.cloud_v τ ⟨D.R.k - 2, by omega⟩
      push_cast
      constructor <;> linarith [h2.1, h2.2]

/- English proof (translation)
Introduce `eps Fm`. Use `⟨0, fun x _ hx i u j hj z r hr => ?_⟩` and prove the remaining obligations. Take `⟨h1, h2⟩` from `row_bounds (Fm.D x i) u j hj z r hr`. Use `⟨fun hz => ?_, fun _ hr1 hr2 => ?_⟩` and prove the remaining obligations. Take `⟨h3, h4⟩` from `u_bounds_off (Fm.params x hx i) u _ (not_mem_topPlaces _ z hz) r hr`.

Apply the tactic sequence `constructor <;> linarith`. Take `⟨h3, h4⟩` from `(Fm.L x i).cloud_u u (tauPl (Fm.D x i) z) ⟨r, hr⟩ hr1 hr2`. Apply the tactic sequence `constructor <;> linarith`.
-/
theorem longRows : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), ∀ r < (Fm.D x i).R.k, (¬ IsTopPl (Fm.D x i) z → wPl (Fm.D x i) (j + 1) z - (Fm.D x i).R.N (Fm.D x i).R.m - 1 / 2 < DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) r ∧ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) r < wPl (Fm.D x i) (j + 1) z + (if r = 0 then 3 * (Fm.L x i).Sc else (Fm.L x i).Sc)) ∧ (IsTopPl (Fm.D x i) z → 1 ≤ r → r + 1 < (Fm.D x i).R.k → wPl (Fm.D x i) (j + 1) z - (Fm.D x i).R.N (Fm.D x i).R.m < DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) r ∧ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) r < wPl (Fm.D x i) (j + 1) z + (Fm.L x i).Sc) := by
  intro eps Fm
  refine ⟨0, fun x _ hx i u j hj z r hr => ?_⟩
  obtain ⟨h1, h2⟩ := row_bounds (Fm.D x i) u j hj z r hr
  refine ⟨fun hz => ?_, fun _ hr1 hr2 => ?_⟩
  · obtain ⟨h3, h4⟩ := u_bounds_off (Fm.params x hx i) u _ (not_mem_topPlaces _ z hz) r hr
    constructor <;> linarith
  · obtain ⟨h3, h4⟩ := (Fm.L x i).cloud_u u (tauPl (Fm.D x i) z) ⟨r, hr⟩ hr1 hr2
    constructor <;> linarith

end GlobalTheory.LongRows
