import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRootsNear
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Filter Topology

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a s ih`. Rewrite using `[Multiset.map_cons, Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ, mul_comm]`. Establish `h1 : ε ≤ ‖t₀ - a‖`.

Rewrite using `[← dist_eq_norm, dist_comm]`. Conclude with `h a (Multiset.mem_cons_self _ _)`. Establish `h2` using `ih (fun b hb => h b (Multiset.mem_cons_of_mem hb))`. Conclude with `mul_le_mul h1 h2 (pow_nonneg hε _) (norm_nonneg _)`.
-/
theorem RootsNear.pow_card_le_norm_prod (s : Multiset ℂ) (t₀ : ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ a ∈ s, ε ≤ dist a t₀) :
    ε ^ Multiset.card s ≤ ‖(s.map fun a => t₀ - a).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ, mul_comm]
    have h1 : ε ≤ ‖t₀ - a‖ := by
      rw [← dist_eq_norm, dist_comm]; exact h a (Multiset.mem_cons_self _ _)
    have h2 := ih (fun b hb => h b (Multiset.mem_cons_of_mem hb))
    exact mul_le_mul h1 h2 (pow_nonneg hε _) (norm_nonneg _)

/- English proof (translation)
Simplify using `only [Polynomial.eval₂_eq_sum_range]`. Use `continuous_finsetSum _ fun i _ => Continuous.mul ?_ continuous_const` and prove the remaining obligations. Establish `: (fun y : Fin e → ℂ => (aeval y).toRingHom (G.coeff i)) = fun y => eval y (MvPolynomial.map (algebraMap ℚ ℂ) (G.coeff i))`. Use function extensionality and compare the values at `y`. Simplify using `[MvPolynomial.eval_map, MvPolynomial.aeval_def]`.

Rewrite using `[this]`. Conclude with `MvPolynomial.continuous_eval _`.
-/
theorem RootsNear.continuous_eval₂ {e : ℕ} (G : Polynomial (MvPolynomial (Fin e) ℚ)) (t : ℂ) :
    Continuous fun y : Fin e → ℂ => G.eval₂ (aeval y).toRingHom t := by
  simp only [Polynomial.eval₂_eq_sum_range]
  refine continuous_finsetSum _ fun i _ => Continuous.mul ?_ continuous_const
  have : (fun y : Fin e → ℂ => (aeval y).toRingHom (G.coeff i)) =
      fun y => eval y (MvPolynomial.map (algebraMap ℚ ℂ) (G.coeff i)) := by
    funext y
    simp [MvPolynomial.eval_map, MvPolynomial.aeval_def]
  rw [this]
  exact MvPolynomial.continuous_eval _

/- English proof (translation)
Introduce `e G hG y₀ t₀ h0 ε hε`. Establish `hpos : (0 : ℝ) < ε ^ G.natDegree` using `pow_pos hε _`. Establish `ht` using `(RootsNear.continuous_eval₂ G t₀).tendsto y₀`. Rewrite `ht` using `[h0]`. Use `filter_upwards [ht (Metric.ball_mem_nhds 0 hpos)] with y hy`.

Rewrite `hy` using `[Set.mem_preimage, mem_ball_zero_iff]`. Assume the negation of the conclusion as `hno`. Use `push Not at hno`. Use `set p := G.map (aeval y).toRingHom with hp`. Establish `hpm : p.Monic` using `hG.map _`.

Establish `hdeg : p.natDegree = G.natDegree` using `hG.natDegree_map _`. Establish `hcard : Multiset.card p.roots = p.natDegree` using `IsAlgClosed.card_roots_eq_natDegree`. Establish `hprod` using `Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hpm hcard`. Establish `hev : G.eval₂ (aeval y).toRingHom t₀ = (p.roots.map fun a => t₀ - a).prod`. Rewrite using `[← Polynomial.eval_map, ← hp]`.

Use `conv_lhs => rw [← hprod]`. Rewrite using `[Polynomial.eval_multiset_prod, Multiset.map_map]`. Use `congr 1`. Apply `Multiset.map_congr rfl` to reduce the goal to its premises. Introduce `a _`.

Simplify using the standard rewrite rules. Establish `hle` using `RootsNear.pow_card_le_norm_prod p.roots t₀ hε.le (fun a ha => by`. Establish `ha' : p.eval₂ (RingHom.id ℂ) a = 0`. Rewrite using `[Polynomial.eval₂_id]`. Conclude with `(Polynomial.mem_roots hpm.ne_zero).1 ha`.

Use `hno a (by rw [hp, Polynomial.eval₂_map] at ha'; simpa using ha')` as an intermediate fact. Conclude with `this)`. Rewrite `hle` using `[hcard, hdeg, ← hev]`. Conclude with `absurd hy (not_lt.2 hle)`.
-/
theorem RootsNear.proof : RootsNear.Statement := by
  intro e G hG y₀ t₀ h0 ε hε
  have hpos : (0 : ℝ) < ε ^ G.natDegree := pow_pos hε _
  have ht := (RootsNear.continuous_eval₂ G t₀).tendsto y₀
  rw [h0] at ht
  filter_upwards [ht (Metric.ball_mem_nhds 0 hpos)] with y hy
  rw [Set.mem_preimage, mem_ball_zero_iff] at hy
  by_contra hno
  push Not at hno
  set p := G.map (aeval y).toRingHom with hp
  have hpm : p.Monic := hG.map _
  have hdeg : p.natDegree = G.natDegree := hG.natDegree_map _
  have hcard : Multiset.card p.roots = p.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hprod := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hpm hcard
  have hev : G.eval₂ (aeval y).toRingHom t₀ = (p.roots.map fun a => t₀ - a).prod := by
    rw [← Polynomial.eval_map, ← hp]
    conv_lhs => rw [← hprod]
    rw [Polynomial.eval_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    simp
  have hle := RootsNear.pow_card_le_norm_prod p.roots t₀ hε.le (fun a ha => by
    have ha' : p.eval₂ (RingHom.id ℂ) a = 0 := by
      rw [Polynomial.eval₂_id]; exact (Polynomial.mem_roots hpm.ne_zero).1 ha
    have := hno a (by rw [hp, Polynomial.eval₂_map] at ha'; simpa using ha')
    exact this)
  rw [hcard, hdeg, ← hev] at hle
  exact absurd hy (not_lt.2 hle)

end GroundTheory.Heights₂.Heights.HilbertSamuel
