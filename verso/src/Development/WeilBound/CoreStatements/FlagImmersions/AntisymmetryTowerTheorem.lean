import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.AntisymmetricPerturbationBoundStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PolarizationPolynomialCoeffBoundStatement

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

/- English proof (translation)
Use function extensionality and compare the values at `z`. Take `⟨s, i⟩` from `z`. Simplify using `only [swapWt, Function.comp_apply, Equiv.swap_apply_def, Prod.mk.injEq]`. Distinguish the cases in `hs : s = τ`. Substitute `hs` using the available equality.

Distinguish the cases in `hia : i = a`. Substitute `hia` using the available equality. Simplify using the standard rewrite rules. Distinguish the cases in `hib : i = b`. Substitute `hib` using the available equality.

Simplify using `[hia]`. Simplify using `[hia, hib]`. Simplify using `[hs]`.
-/
private theorem comp_swap_eq_swapWt {Ψ : Type} [DecidableEq Ψ] {N : ℕ} (x : Ψ × Fin N → ℝ) (τ : Ψ) (a b : Fin N) :
    x ∘ ⇑(Equiv.swap (τ, a) (τ, b)) = fun z : Ψ × Fin N => swapWt τ a b (fun s i => x (s, i)) z.1 z.2 := by
  funext z
  obtain ⟨s, i⟩ := z
  simp only [swapWt, Function.comp_apply, Equiv.swap_apply_def, Prod.mk.injEq]
  by_cases hs : s = τ
  · subst hs
    by_cases hia : i = a
    · subst hia
      simp
    · by_cases hib : i = b
      · subst hib
        simp [hia]
      · simp [hia, hib]
  · simp [hs]

/- English proof (translation)
Establish `hN : (0 : ℝ) < (N : ℝ) + 1` using `by positivity`. Take `⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 1 / (4 * ((N : ℝ) + 1))` from `⟨_, rfl⟩`. Establish `hδpos : 0 < δ` using `by rw [hδ]; positivity`. Establish `hδN : δ * ((N : ℝ) + 1) = 1 / 4`. Rewrite using `[hδ]`.

Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try ring`. Establish `hr : 1 / (16 * ((N : ℝ) + 1)) = δ / 4`. Rewrite using `[hδ]`. Clear the denominators using the available nonvanishing facts.

Apply the tactic sequence `try ring`. Establish `hc : 1 / (8 * ((N : ℝ) + 1)) = δ / 2`. Rewrite using `[hδ]`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try ring`.

Rewrite `hx` using `[← hδ, hr]`. Rewrite using `[hc]`. Establish `hb : ∀ (s : Ψ) (i : Fin N), |x (s, i) - -(δ * (((i : ℕ) : ℝ) - if s = τ ∧ j ≤ (i : ℕ) then 1 else 0))| ≤ δ / 4`. Introduce `s i`. Establish `h1` using `(dist_pi_le_iff (by linarith)).1 (Metric.mem_closedBall.1 hx) (s, i)`.

Rewrite `h1` using `[Real.dist_eq]`. Then use the resulting hypothesis. Establish `G : ∀ (s : Ψ) (a b : Fin N), (b : ℕ) = (a : ℕ) + 1 → ¬ (s = τ ∧ (b : ℕ) = j) → δ / 2 ≤ x (s, a) - x (s, b)`. Introduce `s a b hab hn`. Establish `hite : (if s = τ ∧ j ≤ (a : ℕ) then (1 : ℝ) else 0) = if s = τ ∧ j ≤ (b : ℕ) then 1 else 0`. Distinguish the cases in `hs : s = τ`.

Establish `hbj : (b : ℕ) ≠ j` using `fun h => hn ⟨hs, h⟩`. Simplify using `only [hs, true_and]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`. Simplify using `[hs]`. Establish `hbR : ((b : ℕ) : ℝ) = ((a : ℕ) : ℝ) + 1` using `by exact_mod_cast hab`.

Establish `ha` using `abs_le.1 (hb s a)`. Establish `hb2` using `abs_le.1 (hb s b)`. Rewrite `ha` using `[hite]`. Rewrite `hb2` using `[hbR]`. Combine the linear relations using `[ha.1, ha.2, hb2.1, hb2.2]`.

Establish `hcons : ∀ (s : Ψ) (a b : Fin N), (b : ℕ) = (a : ℕ) + 1 → x (s, b) ≤ x (s, a)`. Introduce `s a b hab`. Distinguish the cases in `hs : s = τ ∧ (b : ℕ) = j`. Take `⟨rfl, hbj⟩` from `hs`. Establish `ha : a = ⟨j - 1, Nat.lt_of_le_of_lt (Nat.sub_le j 1) hjN⟩` using `Fin.ext (show (a : ℕ) = j - 1 by omega)`.

Establish `hb' : b = ⟨j, hjN⟩` using `Fin.ext hbj`. Establish `e1 : x (s, b) = x (s, ⟨j, hjN⟩)` using `congrArg (fun i => x (s, i)) hb'`. Establish `e2 : x (s, a) = x (s, ⟨j - 1, Nat.lt_of_le_of_lt (Nat.sub_le j 1) hjN⟩)` using `congrArg (fun i => x (s, i)) ha`. Rewrite using `[e1, e2]`. Conclude with `hxe.ge`.

Use `G s a b hab hs` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hdom : ∀ (s : Ψ) (k : ℕ) (a b : Fin N), (b : ℕ) = (a : ℕ) + k → x (s, b) ≤ x (s, a)`. Introduce `s k`. Proceed by induction on `k with`.

Consider the case `zero`. Introduce `a b h`. Establish `: b = a` using `Fin.ext (by omega)`. Rewrite using `[this]`. Consider the case `succ k ih`.

Introduce `a b h`. Establish `hbl` using `b.isLt`. Establish `hc : (a : ℕ) + k < N` using `by omega`. Conclude with `le_trans (hcons s ⟨(a : ℕ) + k, hc⟩ b (show (b : ℕ) = (a : ℕ) + k + 1 by omega)) (ih a ⟨(a : ℕ) + k, hc⟩ rfl)`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Use `show _ ∧ _ ∧ _ ∧ _`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `(pi_norm_le_iff_of_nonneg (by norm_num)).2 fun s => (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_ show ‖x (s, i)‖ ≤ 1 / 2` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs]`. Establish `hiN : ((i : ℕ) : ℝ) ≤ N` using `by exact_mod_cast i.isLt.le`.

Establish `hI0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) - (if s = τ ∧ j ≤ (i : ℕ) then 1 else 0)` using `by split_ifs with hh`. Establish `h1 : 1 ≤ (i : ℕ)` using `le_trans hj0 hh.2`. Establish `h2 : (1 : ℝ) ≤ ((i : ℕ) : ℝ)` using `by exact_mod_cast h1`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using the standard rewrite rules.

Apply the tactic sequence `have hI1 : ((i : ℕ) : ℝ) - (if s = τ ∧ j ≤ (i : ℕ) then 1 else 0) ≤ N := by split_ifs <;> linarith`. Establish `hA` using `mul_nonneg hδpos.le hI0`. Establish `hB` using `mul_le_mul_of_nonneg_left hI1 hδpos.le`. Establish `h1` using `abs_le.1 (hb s i)`. Rewrite using `[abs_le]`.

Apply the tactic sequence `constructor <;> linarith [h1.1, h1.2]`. Simplify using `only [gap, ent, dif_pos (show j - 1 < N by omega), dif_pos hjN]`. Conclude with `sub_eq_zero.2 hxe`. Introduce `τ' hτ'`. Simplify using `only [gap, ent, dif_pos (show j - 1 < N by omega), dif_pos hjN]`.

Conclude with `G τ' ⟨j - 1, by omega⟩ ⟨j, hjN⟩ (show j = j - 1 + 1 by omega) (fun h => hτ' h.1)`. Introduce `s i hi hij`. Simplify using `only [ent, dif_pos (show i < N by omega), dif_pos hi]`. Conclude with `G s ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl (fun h => hij h.2)`. Introduce `s a b hab`.

Conclude with `hdom s ((b : ℕ) - (a : ℕ)) a b (by have := Fin.le_iff_val_le_val.1 hab; omega)`.
-/
private theorem inWall_and_dominant_of_eq_neighbors {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} (hj0 : 1 ≤ j) (hjN : j < N)
    (τ : Ψ) (x : Ψ × Fin N → ℝ)
    (hx : x ∈ Metric.closedBall (fun y : Ψ × Fin N => -(1 / (4 * ((N : ℝ) + 1)) *
        (((y.2 : ℕ) : ℝ) - if y.1 = τ ∧ j ≤ (y.2 : ℕ) then 1 else 0))) (1 / (16 * ((N : ℝ) + 1))))
    (hxe : x (τ, ⟨j - 1, by omega⟩) = x (τ, ⟨j, hjN⟩)) :
    InWall j τ (1 / (8 * ((N : ℝ) + 1))) (fun s i => x (s, i)) ∧
      Dominant (Ψ := Ψ) (N := N) (fun s i => x (s, i)) := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 1 / (4 * ((N : ℝ) + 1)) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδN : δ * ((N : ℝ) + 1) = 1 / 4 := by
    rw [hδ]
    field_simp
    try ring
  have hr : 1 / (16 * ((N : ℝ) + 1)) = δ / 4 := by
    rw [hδ]
    field_simp
    try ring
  have hc : 1 / (8 * ((N : ℝ) + 1)) = δ / 2 := by
    rw [hδ]
    field_simp
    try ring
  rw [← hδ, hr] at hx
  rw [hc]
  have hb : ∀ (s : Ψ) (i : Fin N),
      |x (s, i) - -(δ * (((i : ℕ) : ℝ) - if s = τ ∧ j ≤ (i : ℕ) then 1 else 0))| ≤ δ / 4 := by
    intro s i
    have h1 := (dist_pi_le_iff (by linarith)).1 (Metric.mem_closedBall.1 hx) (s, i)
    rwa [Real.dist_eq] at h1
  have G : ∀ (s : Ψ) (a b : Fin N), (b : ℕ) = (a : ℕ) + 1 → ¬ (s = τ ∧ (b : ℕ) = j) →
      δ / 2 ≤ x (s, a) - x (s, b) := by
    intro s a b hab hn
    have hite : (if s = τ ∧ j ≤ (a : ℕ) then (1 : ℝ) else 0) = if s = τ ∧ j ≤ (b : ℕ) then 1 else 0 := by
      by_cases hs : s = τ
      · have hbj : (b : ℕ) ≠ j := fun h => hn ⟨hs, h⟩
        simp only [hs, true_and]
        split_ifs <;> first | rfl | (exfalso; omega)
      · simp [hs]
    have hbR : ((b : ℕ) : ℝ) = ((a : ℕ) : ℝ) + 1 := by exact_mod_cast hab
    have ha := abs_le.1 (hb s a)
    have hb2 := abs_le.1 (hb s b)
    rw [hite] at ha
    rw [hbR] at hb2
    linarith [ha.1, ha.2, hb2.1, hb2.2]
  have hcons : ∀ (s : Ψ) (a b : Fin N), (b : ℕ) = (a : ℕ) + 1 → x (s, b) ≤ x (s, a) := by
    intro s a b hab
    by_cases hs : s = τ ∧ (b : ℕ) = j
    · obtain ⟨rfl, hbj⟩ := hs
      have ha : a = ⟨j - 1, Nat.lt_of_le_of_lt (Nat.sub_le j 1) hjN⟩ := Fin.ext (show (a : ℕ) = j - 1 by omega)
      have hb' : b = ⟨j, hjN⟩ := Fin.ext hbj
      have e1 : x (s, b) = x (s, ⟨j, hjN⟩) := congrArg (fun i => x (s, i)) hb'
      have e2 : x (s, a) = x (s, ⟨j - 1, Nat.lt_of_le_of_lt (Nat.sub_le j 1) hjN⟩) :=
        congrArg (fun i => x (s, i)) ha
      rw [e1, e2]
      exact hxe.ge
    · have := G s a b hab hs
      linarith
  have hdom : ∀ (s : Ψ) (k : ℕ) (a b : Fin N), (b : ℕ) = (a : ℕ) + k → x (s, b) ≤ x (s, a) := by
    intro s k
    induction k with
    | zero =>
      intro a b h
      have : b = a := Fin.ext (by omega)
      rw [this]
    | succ k ih =>
      intro a b h
      have hbl := b.isLt
      have hc : (a : ℕ) + k < N := by omega
      exact le_trans (hcons s ⟨(a : ℕ) + k, hc⟩ b (show (b : ℕ) = (a : ℕ) + k + 1 by omega))
        (ih a ⟨(a : ℕ) + k, hc⟩ rfl)
  refine ⟨?_, ?_⟩
  · show _ ∧ _ ∧ _ ∧ _
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun s =>
        (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
      show ‖x (s, i)‖ ≤ 1 / 2
      rw [Real.norm_eq_abs]
      have hiN : ((i : ℕ) : ℝ) ≤ N := by exact_mod_cast i.isLt.le
      have hI0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) - (if s = τ ∧ j ≤ (i : ℕ) then 1 else 0) := by
        split_ifs with hh
        · have h1 : 1 ≤ (i : ℕ) := le_trans hj0 hh.2
          have h2 : (1 : ℝ) ≤ ((i : ℕ) : ℝ) := by exact_mod_cast h1
          linarith
        · simp
      have hI1 : ((i : ℕ) : ℝ) - (if s = τ ∧ j ≤ (i : ℕ) then 1 else 0) ≤ N := by
        split_ifs <;> linarith
      have hA := mul_nonneg hδpos.le hI0
      have hB := mul_le_mul_of_nonneg_left hI1 hδpos.le
      have h1 := abs_le.1 (hb s i)
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2]
    · simp only [gap, ent, dif_pos (show j - 1 < N by omega), dif_pos hjN]
      exact sub_eq_zero.2 hxe
    · intro τ' hτ'
      simp only [gap, ent, dif_pos (show j - 1 < N by omega), dif_pos hjN]
      exact G τ' ⟨j - 1, by omega⟩ ⟨j, hjN⟩ (show j = j - 1 + 1 by omega) (fun h => hτ' h.1)
    · intro s i hi hij
      simp only [ent, dif_pos (show i < N by omega), dif_pos hi]
      exact G s ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl (fun h => hij h.2)
  · intro s a b hab
    exact hdom s ((b : ℕ) - (a : ℕ)) a b (by have := Fin.le_iff_val_le_val.1 hab; omega)

set_option maxHeartbeats 800000 in
open GroundTheory.Heights₂.Heights in
/- English proof (translation)
Introduce `hS II Ψ _ _ N T hh hprop hW h8 h9`. Take `⟨hvol, -, -⟩` from `hprop`. Establish `hj0 : 1 ≤ T.j` using `T.j_pos`. Establish `hjN : T.j < N` using `T.j_lt`. Establish `hv : 0 < T.volT` using `by show 0 < ∑ c : T.Comp, T.vol c`.

Conclude with `Finset.sum_pos (fun c _ => hvol c) Finset.univ_nonempty`. Take `⟨h, hhom, hev, -, -⟩` from `GlobalTheory.T.polarization_polynomial_coeff_bound (Ψ × Fin N) (dimFl Ψ N + 1) hh`. Set `x0 : Ψ → Ψ × Fin N → ℝ` to `fun τ y => -(1 / (4 * ((N : ℝ) + 1)) * (((y.2 : ℕ) : ℝ) - if y.1 = τ ∧ T.j ≤ (y.2 : ℕ) then 1 else 0))`. Set `K : Ψ → Set (Ψ × Fin N → ℝ)` to `fun τ => diagHyperplane Ψ N τ ⟨T.j - 1, by omega⟩ ⟨T.j, hjN⟩ ∩ Metric.closedBall (x0 τ) (1 / (16 * ((N : ℝ) + 1)))`. Establish `hK : ∀ τ : Ψ, IsCompact (K τ) ∧ K τ ⊆ diagHyperplane Ψ N τ ⟨T.j - 1, by omega⟩ ⟨T.j, hjN⟩ ∧ (∃ O : Set (Ψ × Fin N → ℝ), IsOpen O ∧ (O ∩ diagHyperplane Ψ N τ ⟨T.j - 1, by omega⟩ ⟨T.j, hjN⟩).Nonempty ∧ O ∩ diagHyperplane Ψ N τ ⟨T.j - 1, by omega⟩ ⟨T.j, hjN⟩ ⊆ K τ) ∧ ∀ x ∈ K τ, eval …`.

Introduce `τ`. Establish `hHc : IsClosed (diagHyperplane Ψ N τ ⟨T.j - 1, by omega⟩ ⟨T.j, hjN⟩)` using `isClosed_eq (continuous_apply _) (continuous_apply _)`. Use `⟨(isCompact_closedBall _ _).inter_left hHc, Set.inter_subset_left, ⟨Metric.ball (x0 τ) (1 / (16 * ((N : ℝ) + 1))), Metric.isOpen_ball, ⟨x0 τ, Metric.mem_ball_self (by positivity), ?_⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show x0 τ (τ, ⟨T.j - 1, by omega⟩) = x0 τ (τ, ⟨T.j, hjN⟩)`. Simplify using `[x0, show ¬ T.j ≤ T.j - 1 by omega, Nat.cast_sub hj0]`.

Introduce and unpack `x ⟨hxO, hxH⟩`. Conclude with `⟨hxH, Metric.ball_subset_closedBall hxO⟩`. Introduce and unpack `x ⟨hxH, hxB⟩`. Take `⟨-, hdom⟩` from `inWall_and_dominant_of_eq_neighbors hj0 hjN τ x hxB hxH`. Rewrite using `[hev x]`.

Conclude with `h9.1 (fun s i => x (s, i)) hdom ⟨τ, ⟨T.j - 1, by omega⟩, ⟨T.j, hjN⟩, (show T.j = T.j - 1 + 1 by omega), hxH⟩`. Take `⟨C0, hC⟩` from `hS Ψ N T.j (by omega) hjN h K hK`. Take `⟨CW, B₁, hB⟩` from `hW (1 / (8 * ((N : ℝ) + 1))) (by positivity)`. Unfold `RootTower.ThmB`. Use `⟨C0 * CW, max B₁ 2, fun B hB₂ => ?_⟩` and prove the remaining obligations.

Establish `hB1 : B₁ ≤ B` using `le_trans (le_max_left _ _) hB₂`. Establish `hB2 : 2 ≤ B` using `le_trans (le_max_right _ _) hB₂`. Set `L : RP Ψ N →ₗ[ℝ] ℝ` to `∑ c : T.Comp, ((T.M B c).PP II).comp (rename (some : Ψ × Fin N → Option (Ψ × Fin N))).toLinearMap`. Establish `hL : ∀ F, L F = T.PPt II B F`. Introduce `F`.

Simplify using `[L, RootTower.PPt, RootTower.PPc, toA, LinearMap.sum_apply]`. Take `⟨P, hPhom, hPev, -, -⟩` from `GlobalTheory.T.polarization_polynomial_coeff_bound (Ψ × Fin N) (dimFl Ψ N + 1) L`. Establish `hQev : ∀ x : Ψ × Fin N → ℝ, eval x (P - T.volT • h) = (L - T.volT • hh) ((-∑ z, MvPolynomial.C (x z) * X z) ^ (dimFl Ψ N + 1))`. Introduce `x`. Rewrite using `[map_sub, MvPolynomial.smul_eval, hPev, hev]`.

Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]`. Establish `hQhom : (P - T.volT • h).IsHomogeneous (dimFl Ψ N + 1)` using `(mem_homogeneousSubmodule _ _).1 (Submodule.sub_mem _ ((mem_homogeneousSubmodule _ _).2 hPhom) (Submodule.smul_mem _ _ ((mem_homogeneousSubmodule _ _).2 hhom)))`. Establish `key : ∀ F, T.PPt II B F - T.volT * hh F = ∑ c, (T.PPc II B c F - T.vol c * hh F)`. Introduce `F`. Simplify using `only [RootTower.PPt, RootTower.volT, Finset.sum_sub_distrib, Finset.sum_mul]`.

Establish `hanti : P - T.volT • h ∈ antisymSpace Ψ N T.j` using `by show _ ∧ _`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hd : antisymDegree Ψ N + 1 = dimFl Ψ N + 1`. Simplify using `only [antisymDegree, dimFl, Nat.choose_two_right]`. Rewrite using `[hd]`.

Conclude with `(mem_homogeneousSubmodule _ _).2 hQhom`. Introduce and unpack `σ ⟨τ, a, b, hab, hj, rfl⟩`. Establish `hbj : (b : ℕ) ≠ T.j` using `by omega`. Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `x`.

Rewrite using `[eval_rename, map_neg, hQev, hQev, comp_swap_eq_swapWt x τ a b]`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hL]`. Rewrite using `[key, key]`. Establish `hsum` using `Finset.sum_congr rfl fun c (_ : c ∈ (Finset.univ : Finset T.Comp)) => h8 B hB2 c τ a b hab hbj (fun s i => x (s, i))`. Rewrite `hsum` using `[Finset.sum_neg_distrib]`.

Conclude with `hsum`. Establish `hsmall : ∀ τ : Ψ, ∀ x ∈ K τ, |eval x P| ≤ CW * Real.log B / B`. Introduce and unpack `τ x ⟨hxH, hxB⟩`. Take `⟨hwall, -⟩` from `inWall_and_dominant_of_eq_neighbors hj0 hjN τ x hxB hxH`. Rewrite using `[hPev x, hL]`.

Conclude with `hB B hB1 τ (fun s i => x (s, i)) hwall`. Take `⟨l, hl, hlc⟩` from `hC P T.volT (CW * Real.log B / B) hanti hsmall`. Take `⟨α, β, hαβ⟩` from `GlobalTheory.T.antisymmetric_perturbation_bound Ψ N T.j (L - T.volT • hh) T.volT (C0 * (CW * Real.log B / B)) (P - T.volT • h) l hv (fun lam => hQev _) hQhom hl hlc`. Use `⟨α, β, fun m hm => ?_⟩` and prove the remaining obligations. Establish `h1` using `hαβ m hm`.

Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hL] at h1`. Rewrite using `[show C0 * CW * Real.log B / B = C0 * (CW * Real.log B / B) by ring]`. Use `(le_of_eq ?_).trans h1` and prove the remaining obligations. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem antisymmetry_tower_theorem : GroundTheory.Heights₂.Heights.AntisymPerturbation.Statement → ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ), T.Proportional → T.ThmW II → T.I8 II hh → I9 (Ψ := Ψ) (N := N) hh → T.ThmB II hh := by
  intro hS II Ψ _ _ N T hh hprop hW h8 h9
  obtain ⟨hvol, -, -⟩ := hprop
  have hj0 : 1 ≤ T.j := T.j_pos
  have hjN : T.j < N := T.j_lt
  have hv : 0 < T.volT := by
    show 0 < ∑ c : T.Comp, T.vol c
    exact Finset.sum_pos (fun c _ => hvol c) Finset.univ_nonempty
  obtain ⟨h, hhom, hev, -, -⟩ := GlobalTheory.T.polarization_polynomial_coeff_bound (Ψ × Fin N) (dimFl Ψ N + 1) hh
  let x0 : Ψ → Ψ × Fin N → ℝ := fun τ y => -(1 / (4 * ((N : ℝ) + 1)) *
    (((y.2 : ℕ) : ℝ) - if y.1 = τ ∧ T.j ≤ (y.2 : ℕ) then 1 else 0))
  let K : Ψ → Set (Ψ × Fin N → ℝ) := fun τ =>
    diagHyperplane Ψ N τ ⟨T.j - 1, by omega⟩ ⟨T.j, hjN⟩ ∩ Metric.closedBall (x0 τ) (1 / (16 * ((N : ℝ) + 1)))
  have hK : ∀ τ : Ψ, IsCompact (K τ) ∧ K τ ⊆ diagHyperplane Ψ N τ ⟨T.j - 1, by omega⟩ ⟨T.j, hjN⟩ ∧
      (∃ O : Set (Ψ × Fin N → ℝ), IsOpen O ∧
        (O ∩ diagHyperplane Ψ N τ ⟨T.j - 1, by omega⟩ ⟨T.j, hjN⟩).Nonempty ∧
        O ∩ diagHyperplane Ψ N τ ⟨T.j - 1, by omega⟩ ⟨T.j, hjN⟩ ⊆ K τ) ∧
      ∀ x ∈ K τ, eval x h = 0 := by
    intro τ
    have hHc : IsClosed (diagHyperplane Ψ N τ ⟨T.j - 1, by omega⟩ ⟨T.j, hjN⟩) :=
      isClosed_eq (continuous_apply _) (continuous_apply _)
    refine ⟨(isCompact_closedBall _ _).inter_left hHc, Set.inter_subset_left,
      ⟨Metric.ball (x0 τ) (1 / (16 * ((N : ℝ) + 1))), Metric.isOpen_ball,
        ⟨x0 τ, Metric.mem_ball_self (by positivity), ?_⟩, ?_⟩, ?_⟩
    · show x0 τ (τ, ⟨T.j - 1, by omega⟩) = x0 τ (τ, ⟨T.j, hjN⟩)
      simp [x0, show ¬ T.j ≤ T.j - 1 by omega, Nat.cast_sub hj0]
    · rintro x ⟨hxO, hxH⟩
      exact ⟨hxH, Metric.ball_subset_closedBall hxO⟩
    · rintro x ⟨hxH, hxB⟩
      obtain ⟨-, hdom⟩ := inWall_and_dominant_of_eq_neighbors hj0 hjN τ x hxB hxH
      rw [hev x]
      exact h9.1 (fun s i => x (s, i)) hdom
        ⟨τ, ⟨T.j - 1, by omega⟩, ⟨T.j, hjN⟩, (show T.j = T.j - 1 + 1 by omega), hxH⟩
  obtain ⟨C0, hC⟩ := hS Ψ N T.j (by omega) hjN h K hK
  obtain ⟨CW, B₁, hB⟩ := hW (1 / (8 * ((N : ℝ) + 1))) (by positivity)
  unfold RootTower.ThmB
  refine ⟨C0 * CW, max B₁ 2, fun B hB₂ => ?_⟩
  have hB1 : B₁ ≤ B := le_trans (le_max_left _ _) hB₂
  have hB2 : 2 ≤ B := le_trans (le_max_right _ _) hB₂
  let L : RP Ψ N →ₗ[ℝ] ℝ :=
    ∑ c : T.Comp, ((T.M B c).PP II).comp (rename (some : Ψ × Fin N → Option (Ψ × Fin N))).toLinearMap
  have hL : ∀ F, L F = T.PPt II B F := by
    intro F
    simp [L, RootTower.PPt, RootTower.PPc, toA, LinearMap.sum_apply]
  obtain ⟨P, hPhom, hPev, -, -⟩ := GlobalTheory.T.polarization_polynomial_coeff_bound (Ψ × Fin N) (dimFl Ψ N + 1) L
  have hQev : ∀ x : Ψ × Fin N → ℝ, eval x (P - T.volT • h) =
      (L - T.volT • hh) ((-∑ z, MvPolynomial.C (x z) * X z) ^ (dimFl Ψ N + 1)) := by
    intro x
    rw [map_sub, MvPolynomial.smul_eval, hPev, hev]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  have hQhom : (P - T.volT • h).IsHomogeneous (dimFl Ψ N + 1) :=
    (mem_homogeneousSubmodule _ _).1 (Submodule.sub_mem _ ((mem_homogeneousSubmodule _ _).2 hPhom)
      (Submodule.smul_mem _ _ ((mem_homogeneousSubmodule _ _).2 hhom)))
  have key : ∀ F, T.PPt II B F - T.volT * hh F = ∑ c, (T.PPc II B c F - T.vol c * hh F) := by
    intro F
    simp only [RootTower.PPt, RootTower.volT, Finset.sum_sub_distrib, Finset.sum_mul]
  have hanti : P - T.volT • h ∈ antisymSpace Ψ N T.j := by
    show _ ∧ _
    refine ⟨?_, ?_⟩
    · have hd : antisymDegree Ψ N + 1 = dimFl Ψ N + 1 := by
        simp only [antisymDegree, dimFl, Nat.choose_two_right]
      rw [hd]
      exact (mem_homogeneousSubmodule _ _).2 hQhom
    · rintro σ ⟨τ, a, b, hab, hj, rfl⟩
      have hbj : (b : ℕ) ≠ T.j := by omega
      apply MvPolynomial.funext
      intro x
      rw [eval_rename, map_neg, hQev, hQev, comp_swap_eq_swapWt x τ a b]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hL]
      rw [key, key]
      have hsum := Finset.sum_congr rfl fun c (_ : c ∈ (Finset.univ : Finset T.Comp)) =>
        h8 B hB2 c τ a b hab hbj (fun s i => x (s, i))
      rw [Finset.sum_neg_distrib] at hsum
      exact hsum
  have hsmall : ∀ τ : Ψ, ∀ x ∈ K τ, |eval x P| ≤ CW * Real.log B / B := by
    rintro τ x ⟨hxH, hxB⟩
    obtain ⟨hwall, -⟩ := inWall_and_dominant_of_eq_neighbors hj0 hjN τ x hxB hxH
    rw [hPev x, hL]
    exact hB B hB1 τ (fun s i => x (s, i)) hwall
  obtain ⟨l, hl, hlc⟩ := hC P T.volT (CW * Real.log B / B) hanti hsmall
  obtain ⟨α, β, hαβ⟩ := GlobalTheory.T.antisymmetric_perturbation_bound Ψ N T.j (L - T.volT • hh) T.volT (C0 * (CW * Real.log B / B))
    (P - T.volT • h) l hv (fun lam => hQev _) hQhom hl hlc
  refine ⟨α, β, fun m hm => ?_⟩
  have h1 := hαβ m hm
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hL] at h1
  rw [show C0 * CW * Real.log B / B = C0 * (CW * Real.log B / B) by ring]
  refine (le_of_eq ?_).trans h1
  congr 1
  ring

end RootFieldNumerics
