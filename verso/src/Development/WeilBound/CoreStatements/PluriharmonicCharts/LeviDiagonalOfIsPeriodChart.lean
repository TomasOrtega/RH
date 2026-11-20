import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.AnalyticForms.LeviForms.HomDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsOpenFlagDomainNondegenerateMinorsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetComparableGramBoundStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GramLogUnitaryTriangularInvarianceStatement
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XPerCell
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPotentialLeviFormCellStatement

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgp.per_diag

namespace PerDiag

variable {e N : ℕ}

def PlurRe (z0 : Fin e → ℂ) (f : (Fin e → ℂ) → ℝ) : Prop :=
  ∃ H : (Fin e → ℂ) → ℂ, AnalyticAt ℂ H z0 ∧ f =ᶠ[𝓝 z0] fun w => (H w).re

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ => 0, analyticAt_const, Filter.Eventually.of_forall fun _ => by simp⟩`.
-/
theorem PlurRe.zero (z0 : Fin e → ℂ) : PlurRe z0 fun _ => 0 := ⟨fun _ => 0, analyticAt_const, Filter.Eventually.of_forall fun _ => by simp⟩

/- English proof (translation)
Take `⟨H, hH, hev⟩` from `h`. Conclude with `⟨H, hH, hf.trans hev⟩`.
-/
theorem PlurRe.congr {z0 : Fin e → ℂ} {f f' : (Fin e → ℂ) → ℝ} (h : PlurRe z0 f)
    (hf : f' =ᶠ[𝓝 z0] f) : PlurRe z0 f' := by
  obtain ⟨H, hH, hev⟩ := h
  exact ⟨H, hH, hf.trans hev⟩

/- English proof (translation)
Take `⟨H, hH, e1⟩` from `h`. Take `⟨H', hH', e2⟩` from `h'`. Use `⟨fun w => H w + H' w, hH.add hH', ?_⟩` and prove the remaining obligations. Use `filter_upwards [e1, e2] with w h1 h2`. Simplify using `[h1, h2]`.
-/
theorem PlurRe.add {z0 : Fin e → ℂ} {f f' : (Fin e → ℂ) → ℝ} (h : PlurRe z0 f)
    (h' : PlurRe z0 f') : PlurRe z0 fun w => f w + f' w := by
  obtain ⟨H, hH, e1⟩ := h
  obtain ⟨H', hH', e2⟩ := h'
  refine ⟨fun w => H w + H' w, hH.add hH', ?_⟩
  filter_upwards [e1, e2] with w h1 h2
  simp [h1, h2]

/- English proof (translation)
Take `⟨H, hH, e1⟩` from `h`. Take `⟨H', hH', e2⟩` from `h'`. Use `⟨fun w => H w - H' w, hH.sub hH', ?_⟩` and prove the remaining obligations. Use `filter_upwards [e1, e2] with w h1 h2`. Simplify using `[h1, h2]`.
-/
theorem PlurRe.sub {z0 : Fin e → ℂ} {f f' : (Fin e → ℂ) → ℝ} (h : PlurRe z0 f)
    (h' : PlurRe z0 f') : PlurRe z0 fun w => f w - f' w := by
  obtain ⟨H, hH, e1⟩ := h
  obtain ⟨H', hH', e2⟩ := h'
  refine ⟨fun w => H w - H' w, hH.sub hH', ?_⟩
  filter_upwards [e1, e2] with w h1 h2
  simp [h1, h2]

/- English proof (translation)
Use `choose H hH hev using h`. Use `⟨fun w => ∑ a, H a w, Finset.analyticAt_fun_sum _ fun a _ => hH a, ?_⟩` and prove the remaining obligations. Use `filter_upwards [eventually_all.2 hev] with w hw`. Simplify using `[hw]`.
-/
theorem PlurRe.sum {z0 : Fin e → ℂ} {ι : Type} [Fintype ι] {f : ι → (Fin e → ℂ) → ℝ}
    (h : ∀ a, PlurRe z0 (f a)) : PlurRe z0 fun w => ∑ a, f a w := by
  choose H hH hev using h
  refine ⟨fun w => ∑ a, H a w, Finset.analyticAt_fun_sum _ fun a _ => hH a, ?_⟩
  filter_upwards [eventually_all.2 hev] with w hw
  simp [hw]

/- English proof (translation)
Use `⟨fun w => Complex.log (B w / B z0) + (Real.log ‖B z0‖ : ℂ), ?_, ?_⟩` and prove the remaining obligations. Use `AnalyticAt.add ?_ analyticAt_const` and prove the remaining obligations. Use `(hB.div analyticAt_const h0).clog ?_` and prove the remaining obligations. Simplify using `[div_self h0]`. Use `filter_upwards [hB.continuousAt.eventually_ne h0] with w hw`.

Simplify using `only [Complex.add_re, Complex.log_re, Complex.ofReal_re]`. Rewrite using `[norm_div, Real.log_div (norm_ne_zero_iff.2 hw) (norm_ne_zero_iff.2 h0)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem plurRe_log_norm {z0 : Fin e → ℂ} {B : (Fin e → ℂ) → ℂ} (hB : AnalyticAt ℂ B z0)
    (h0 : B z0 ≠ 0) : PlurRe z0 fun w => Real.log ‖B w‖ := by
  refine ⟨fun w => Complex.log (B w / B z0) + (Real.log ‖B z0‖ : ℂ), ?_, ?_⟩
  · refine AnalyticAt.add ?_ analyticAt_const
    refine (hB.div analyticAt_const h0).clog ?_
    simp [div_self h0]
  · filter_upwards [hB.continuousAt.eventually_ne h0] with w hw
    simp only [Complex.add_re, Complex.log_re, Complex.ofReal_re]
    rw [norm_div, Real.log_div (norm_ne_zero_iff.2 hw) (norm_ne_zero_iff.2 h0)]
    ring

def diagLog (b : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) : ℝ :=
  ∑ a : Fin N, if (a : ℕ) < k then Real.log ‖b a a‖ else 0

/- English proof (translation)
Use `PlurRe.sum fun a => ?_` and prove the remaining obligations. Distinguish the cases in `h : (a : ℕ) < k`. Simplify `plurRe_log_norm (hb a) (h0 a)` using `[h]`. Simplify `PlurRe.zero z0` using `[h]`.
-/
theorem plurRe_diagLog {z0 : Fin e → ℂ} {b : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ}
    (hb : ∀ a, AnalyticAt ℂ (fun w => b w a a) z0) (h0 : ∀ a, b z0 a a ≠ 0) (k : ℕ) :
    PlurRe z0 fun w => diagLog (b w) k := by
  refine PlurRe.sum fun a => ?_
  by_cases h : (a : ℕ) < k
  · simpa [h] using plurRe_log_norm (hb a) (h0 a)
  · simpa [h] using PlurRe.zero z0

def stepCorr (N j : ℕ) (i : Fin N) (b : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  if (i : ℕ) + 1 ≤ j then diagLog b (N - j + ((i : ℕ) + 1)) - diagLog b (N - j)
  else diagLog b N - diagLog b (N - j) + diagLog b ((i : ℕ) + 1 - j)

/- English proof (translation)
Distinguish the cases in `hc : (i : ℕ) + 1 ≤ j`. Simplify using `only [stepCorr, hc, ↓reduceIte]`. Conclude with `(plurRe_diagLog hb h0 _).sub (plurRe_diagLog hb h0 _)`. Simplify using `only [stepCorr, hc, ↓reduceIte]`. Conclude with `((plurRe_diagLog hb h0 _).sub (plurRe_diagLog hb h0 _)).add (plurRe_diagLog hb h0 _)`.
-/
theorem plurRe_stepCorr {z0 : Fin e → ℂ} {b : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ}
    (hb : ∀ a, AnalyticAt ℂ (fun w => b w a a) z0) (h0 : ∀ a, b z0 a a ≠ 0) (j : ℕ) (i : Fin N) :
    PlurRe z0 fun w => stepCorr N j i (b w) := by
  by_cases hc : (i : ℕ) + 1 ≤ j
  · simp only [stepCorr, hc, ↓reduceIte]
    exact (plurRe_diagLog hb h0 _).sub (plurRe_diagLog hb h0 _)
  · simp only [stepCorr, hc, ↓reduceIte]
    exact ((plurRe_diagLog hb h0 _).sub (plurRe_diagLog hb h0 _)).add (plurRe_diagLog hb h0 _)

/- English proof (translation)
Establish `h k` using `(GlobalTheory.T.gram_log_unitary_triangular_invariance N (sigForm N j) k g u 1).1 hu`. Unfold `stepPot`. Simplify using `only [h]`.
-/
theorem stepPot_unitary_mul {j : ℕ} {u : Matrix (Fin N) (Fin N) ℂ}
    (hu : gramOf (sigForm N j) u = diagonal fun i => ((sigForm N j i : ℝ) : ℂ))
    (i : Fin N) (g : Matrix (Fin N) (Fin N) ℂ) : stepPot N j i (u * g) = stepPot N j i g := by
  have h k := (GlobalTheory.T.gram_log_unitary_triangular_invariance N (sigForm N j) k g u 1).1 hu
  unfold stepPot
  simp only [h]

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]`. Rewrite using `[← Fintype.sum_subtype_add_sum_subtype (fun b : Fin N => (b : ℕ) < k)]`. Establish `h1 : ∀ b : {b : Fin N // ¬ (b : ℕ) < k}, (if h : ((b : Fin N) : ℕ) < k then v ⟨b, h⟩ else 0) = 0` using `fun b => dif_neg b.2`. Establish `h2 : ∀ b : {b : Fin N // (b : ℕ) < k}, (if h : ((b : Fin N) : ℕ) < k then v ⟨b, h⟩ else 0) = v b` using `fun b => dif_pos b.2`. Simplify using `only [h1, h2, mul_zero, Finset.sum_const_zero, add_zero]`.
-/
private theorem submatrix_mulVec_eq_mulVec_extend (G : Matrix (Fin N) (Fin N) ℂ) (k : ℕ)
    (v : {a : Fin N // (a : ℕ) < k} → ℂ) (a : {a : Fin N // (a : ℕ) < k}) :
    (G.submatrix Subtype.val Subtype.val *ᵥ v) a =
      (G *ᵥ fun b => if h : (b : ℕ) < k then v ⟨b, h⟩ else 0) a := by
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun b : Fin N => (b : ℕ) < k)]
  have h1 : ∀ b : {b : Fin N // ¬ (b : ℕ) < k},
      (if h : ((b : Fin N) : ℕ) < k then v ⟨b, h⟩ else 0) = 0 := fun b => dif_neg b.2
  have h2 : ∀ b : {b : Fin N // (b : ℕ) < k},
      (if h : ((b : Fin N) : ℕ) < k then v ⟨b, h⟩ else 0) = v b := fun b => dif_pos b.2
  simp only [h1, h2, mul_zero, Finset.sum_const_zero, add_zero]

/- English proof (translation)
Simplify using `only [dotProduct, submatrix_mulVec_eq_mulVec_extend]`. Rewrite using `[← Fintype.sum_subtype_add_sum_subtype (fun b : Fin N => (b : ℕ) < k)]`. Establish `h1 : ∀ b : {b : Fin N // ¬ (b : ℕ) < k}, (star fun b : Fin N => if h : (b : ℕ) < k then v ⟨b, h⟩ else 0) b = 0` using `fun b => by`. Simplify using `[dif_neg b.2]`. Establish `h2 : ∀ b : {b : Fin N // (b : ℕ) < k}, (star fun b : Fin N => if h : (b : ℕ) < k then v ⟨b, h⟩ else 0) b = star v b` using `fun b => by`.

Simplify using `[dif_pos b.2]`. Simplify using `only [h1, h2, zero_mul, Finset.sum_const_zero, add_zero]`.
-/
private theorem submatrix_quadForm_eq_quadForm_extend (G : Matrix (Fin N) (Fin N) ℂ) (k : ℕ)
    (v : {a : Fin N // (a : ℕ) < k} → ℂ) :
    star v ⬝ᵥ (G.submatrix Subtype.val Subtype.val *ᵥ v) =
      star (fun b : Fin N => if h : (b : ℕ) < k then v ⟨b, h⟩ else 0) ⬝ᵥ
        (G *ᵥ fun b => if h : (b : ℕ) < k then v ⟨b, h⟩ else 0) := by
  simp only [dotProduct, submatrix_mulVec_eq_mulVec_extend]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun b : Fin N => (b : ℕ) < k)]
  have h1 : ∀ b : {b : Fin N // ¬ (b : ℕ) < k},
      (star fun b : Fin N => if h : (b : ℕ) < k then v ⟨b, h⟩ else 0) b = 0 := fun b => by
    simp [dif_neg b.2]
  have h2 : ∀ b : {b : Fin N // (b : ℕ) < k},
      (star fun b : Fin N => if h : (b : ℕ) < k then v ⟨b, h⟩ else 0) b = star v b := fun b => by
    simp [dif_pos b.2]
  simp only [h1, h2, zero_mul, Finset.sum_const_zero, add_zero]

/- English proof (translation)
Unfold `dotProduct`. Apply the tactic sequence `exact Finset.sum_eq_zero fun a _ => by rcases h a with h | h <;> simp [h]`.
-/
private theorem dotProduct_eq_zero_of_disjoint_support (f g : Fin N → ℂ) (h : ∀ a, f a = 0 ∨ g a = 0) : f ⬝ᵥ g = 0 := by
  unfold dotProduct
  exact Finset.sum_eq_zero fun a _ => by rcases h a with h | h <;> simp [h]

/- English proof (translation)
Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]`.
-/
private theorem quadForm_conjTranspose_mul_mul (c D : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → ℂ) :
    star x ⬝ᵥ ((cᴴ * D * c) *ᵥ x) = star (c *ᵥ x) ⬝ᵥ (D *ᵥ (c *ᵥ x)) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

/- English proof (translation)
Establish `e1 : star y ⬝ᵥ (G *ᵥ v) = 0` using `dotProduct_eq_zero_of_disjoint_support _ _ fun a => by`. Apply the tactic sequence `rcases ha a with h | h <;> simp [h]`. Establish `e2 : star v ⬝ᵥ (G *ᵥ v) = 0` using `dotProduct_eq_zero_of_disjoint_support _ _ fun a => by`. Apply the tactic sequence `rcases hb a with h | h <;> simp [h]`. Establish `e3 : star v ⬝ᵥ (G *ᵥ y) = 0`.

Rewrite using `[Matrix.dotProduct_mulVec, ← hG, ← Matrix.conjTranspose_conjTranspose G, hG, ← Matrix.star_mulVec, hG]`. Rewrite using `[dotProduct_comm]`. Apply the tactic sequence `exact dotProduct_eq_zero_of_disjoint_support _ _ fun a => by rcases ha a with h | h <;> simp [h]`. Simplify using `only [Matrix.mulVec_add, Matrix.mulVec_smul, star_add, star_smul, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, e1, e2, e3, smul_zero, add_zero]`.
-/
private theorem quadForm_add_smul_eq_of_orthogonal_support (G : Matrix (Fin N) (Fin N) ℂ) (hG : Gᴴ = G) (y v : Fin N → ℂ)
    (t : ℂ) (ha : ∀ a, y a = 0 ∨ (G *ᵥ v) a = 0) (hb : ∀ a, v a = 0 ∨ (G *ᵥ v) a = 0) :
    star (y + t • v) ⬝ᵥ (G *ᵥ (y + t • v)) = star y ⬝ᵥ (G *ᵥ y) := by
  have e1 : star y ⬝ᵥ (G *ᵥ v) = 0 := dotProduct_eq_zero_of_disjoint_support _ _ fun a => by
    rcases ha a with h | h <;> simp [h]
  have e2 : star v ⬝ᵥ (G *ᵥ v) = 0 := dotProduct_eq_zero_of_disjoint_support _ _ fun a => by
    rcases hb a with h | h <;> simp [h]
  have e3 : star v ⬝ᵥ (G *ᵥ y) = 0 := by
    rw [Matrix.dotProduct_mulVec, ← hG, ← Matrix.conjTranspose_conjTranspose G, hG,
      ← Matrix.star_mulVec, hG]
    rw [dotProduct_comm]
    exact dotProduct_eq_zero_of_disjoint_support _ _ fun a => by rcases ha a with h | h <;> simp [h]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, star_add, star_smul, add_dotProduct,
    dotProduct_add, smul_dotProduct, dotProduct_smul, e1, e2, e3, smul_zero, add_zero]

/- English proof (translation)
Unfold `dotProduct`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_diagonal]`. Distinguish the cases in `h : (a : ℕ) < m`. Simplify using `[hu a h]`.

Simplify using `[hd a h]`.
-/
private theorem quadForm_diagonal_eq_of_support (m : ℕ) (d : Fin N → ℂ) (hd : ∀ a : Fin N, ¬ (a : ℕ) < m → d a = 1)
    (u : Fin N → ℂ) (hu : ∀ a : Fin N, (a : ℕ) < m → u a = 0) :
    star u ⬝ᵥ (Matrix.diagonal d *ᵥ u) = star u ⬝ᵥ u := by
  unfold dotProduct
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mulVec_diagonal]
  by_cases h : (a : ℕ) < m
  · simp [hu a h]
  · simp [hd a h]

/- English proof (translation)
Take `⟨hcu, hneg⟩` from `hc`. Establish `hmN : N - j ≤ N` using `Nat.sub_le N j`. Establish `hGH : (gramOf (sigForm N j) c)ᴴ = gramOf (sigForm N j) c`. Establish `hs : (star fun i : Fin N => ((sigForm N j i : ℝ) : ℂ)) = fun i => ((sigForm N j i : ℝ) : ℂ)`. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules. Simplify using `only [gramOf, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose, hs, Matrix.mul_assoc]`. Establish `hnq : ∀ y : Fin N → ℂ, (∀ a : Fin N, ¬ (a : ℕ) < N - j → y a = 0) → y ≠ 0 → star y ⬝ᵥ (gramOf (sigForm N j) c *ᵥ y) < 0`. Introduce `y hy hy0`. Establish `hext : (fun b : Fin N => if h : (b : ℕ) < N - j then y b else 0) = y`.

Use function extensionality and compare the values at `b`. Distinguish the cases in `h : (b : ℕ) < N - j`. Simplify using `[h]`. Simplify using `[h, hy b h]`. Establish `hy''0 : (fun b : {a : Fin N // (a : ℕ) < N - j} => y b) ≠ 0`.

Introduce `h0`. Apply `hy0` to reduce the goal to its premises. Rewrite using `[← hext]`. Use function extensionality and compare the values at `b`. Use `split_ifs with h`.

Conclude with `congrFun h0 ⟨b, h⟩`. Both sides reduce to the same expression. Establish `h1` using `hneg.dotProduct_mulVec_pos hy''0`. Rewrite `h1` using `[Matrix.neg_mulVec, dotProduct_neg, neg_pos]`. Establish `h2` using `submatrix_quadForm_eq_quadForm_extend (gramOf (sigForm N j) c) (N - j) (fun b : {a : Fin N // (a : ℕ) < N - j} => y b)`.

Simplify using `only [gramHead] at h1`. Rewrite `h1` using `[h2]`. Simplify `h1` using `only [hext]`. Introduce `hdet`. Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 hdet`.

Use `set v' : Fin N → ℂ := fun b => if h : (b : ℕ) < k then v ⟨b, h⟩ else 0 with hvEq`. Establish `hGv : ∀ a : Fin N, (a : ℕ) < k → (gramOf (sigForm N j) c *ᵥ v') a = 0` using `fun a ha => by`. Establish `h1` using `congrFun hv ⟨a, ha⟩`. Simplify using `only [gramHead] at h1`. Rewrite `h1` using `[submatrix_mulVec_eq_mulVec_extend]`.

Conclude with `h1`. Establish `hvs : ∀ a : Fin N, ¬ (a : ℕ) < k → v' a = 0` using `fun a ha => by simp [hvEq, ha]`. Establish `hv'0 : v' ≠ 0`. Introduce `h0`. Apply `hv0` to reduce the goal to its premises.

Use function extensionality and compare the values at `b`. Establish `h1` using `congrFun h0 b`. Simplify `h1` using `[hvEq, b.2]`. Establish `hQv : star v' ⬝ᵥ (gramOf (sigForm N j) c *ᵥ v') = 0` using `dotProduct_eq_zero_of_disjoint_support _ _ fun a => by`. Distinguish the cases in `h : (a : ℕ) < k`.

Conclude with `Or.inr (hGv a h)`. Conclude with `Or.inl (by simp [hvs a h])`. Distinguish the cases in `hkm : k ≤ N - j`. Conclude with `hv'0 (by_contra fun h => (hnq v' (fun a ha => hvs a (by omega)) h).ne hQv)`. Use `push_neg at hkm`.

Set `Bm : Matrix (Fin N) (Option (Fin (N - j))) ℂ` to `fun a s => match s with`. Consider the case `none => v' a`. Consider the case `some s => if (a : ℕ) = s then 1 else 0`. Set `Mx : Matrix (Option (Fin (N - j))) (Option (Fin (N - j))) ℂ` to `fun r s => match r with`. Consider the case `none => 0`.

Consider the case `some r => (c * Bm) (Fin.castLE hmN r) s`. Establish `hdet0 : Mx.det = 0` using `Matrix.det_eq_zero_of_row_eq_zero none fun s => rfl`. Take `⟨z, hz0, hz⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 hdet0`. Establish `hu : ∀ a : Fin N, (a : ℕ) < N - j → (c *ᵥ (Bm *ᵥ z)) a = 0` using `fun a ha => by`. Establish `h1 : ((c * Bm) *ᵥ z) (Fin.castLE hmN ⟨a, ha⟩) = 0` using `congrFun hz (some ⟨a, ha⟩)`.

Rewrite `h1` using `[← Matrix.mulVec_mulVec]`. Establish `h2 : Fin.castLE hmN ⟨a, ha⟩ = a` using `Fin.ext rfl`. Rewrite `h1` using `[h2]`. Then use the resulting hypothesis. Set `y' : Fin N → ℂ` to `fun a => ∑ s : Fin (N - j), (if (a : ℕ) = s then 1 else 0) * z (some s)`. Establish `hx : Bm *ᵥ z = y' + z none • v'`.

Use function extensionality and compare the values at `a`. Simplify using `only [Matrix.mulVec, dotProduct, Fintype.sum_option, Bm, y', Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hys : ∀ a : Fin N, ¬ (a : ℕ) < N - j → y' a = 0` using `fun a ha => Finset.sum_eq_zero fun s _ => by`. Establish `h1 : (a : ℕ) ≠ s` using `fun h => ha (h ▸ s.2)`.

Simplify using `[h1]`. Establish `hcross : star (Bm *ᵥ z) ⬝ᵥ (gramOf (sigForm N j) c *ᵥ (Bm *ᵥ z)) = star y' ⬝ᵥ (gramOf (sigForm N j) c *ᵥ y')`. Rewrite using `[hx]`. Use `quadForm_add_smul_eq_of_orthogonal_support _ hGH _ _ _ (fun a => ?_) (fun a => ?_)` and prove the remaining obligations. Distinguish the cases in `h : (a : ℕ) < N - j`.

Conclude with `Or.inr (hGv a (by omega))`. Conclude with `Or.inl (hys a h)`. Distinguish the cases in `h : (a : ℕ) < k`. Conclude with `Or.inr (hGv a h)`. Conclude with `Or.inl (hvs a h)`.

Establish `hQD : star (Bm *ᵥ z) ⬝ᵥ (gramOf (sigForm N j) c *ᵥ (Bm *ᵥ z)) = star (c *ᵥ (Bm *ᵥ z)) ⬝ᵥ (c *ᵥ (Bm *ᵥ z))`. Rewrite using `[gramOf, quadForm_conjTranspose_mul_mul]`. Conclude with `quadForm_diagonal_eq_of_support (N - j) _ (fun a ha => by simp [sigForm, ha]) _ hu`. Establish `hnonneg : 0 ≤ star (c *ᵥ (Bm *ᵥ z)) ⬝ᵥ (c *ᵥ (Bm *ᵥ z))` using `by first`. Consider the case `exact dotProduct_star_self_nonneg _`.

Consider the case `exact Matrix.dotProduct_star_self_nonneg _`. Establish `hy0 : y' = 0`. Assume the negation of the conclusion as `h`. Establish `h1` using `hnq y' hys h`. Rewrite `h1` using `[← hcross, hQD]`.

Conclude with `absurd (h1.trans_le hnonneg) (lt_irrefl _)`. Establish `hu0 : c *ᵥ (Bm *ᵥ z) = 0`. Establish `h1 : star (c *ᵥ (Bm *ᵥ z)) ⬝ᵥ (c *ᵥ (Bm *ᵥ z)) = 0`. Rewrite using `[← hQD, hcross, hy0]`. Simplify using the standard rewrite rules.

Use `first`. Consider the case `exact dotProduct_star_self_eq_zero.1 h1`. Consider the case `exact Matrix.dotProduct_star_self_eq_zero.1 h1`. Establish `hx0 : Bm *ᵥ z = 0`. Establish `h1 : c⁻¹ *ᵥ (c *ᵥ (Bm *ᵥ z)) = Bm *ᵥ z`.

Rewrite using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul c hcu, Matrix.one_mulVec]`. Rewrite using `[← h1, hu0, Matrix.mulVec_zero]`. Establish `hzn : z none = 0`. Rewrite `hx0` using `[hx, hy0, zero_add]`. Conclude with `(smul_eq_zero.1 hx0).resolve_right hv'0`.

Establish `hzs : ∀ s : Fin (N - j), z (some s) = 0` using `fun s => by`. Establish `h1` using `congrFun hy0 (Fin.castLE hmN s)`. Simplify using `only [y', Pi.zero_apply] at h1`. Rewrite `h1` using `[Finset.sum_eq_single s]`. Simplify using `using h1`.

Introduce `b _ hb`. Establish `h2 : (s : ℕ) ≠ b` using `fun h => hb (Fin.ext h.symm)`. Simplify using `[Fin.coe_castLE, h2]`. Simplify using the standard rewrite rules. Apply `hz0` to reduce the goal to its premises.

Use function extensionality and compare the values at `o`. Consider the cases of `o with`. Consider the case `none => exact hzn`. Consider the case `some s => exact hzs s`.
-/
private theorem gramHead_det_ne_zero_of_inFlagDomain {j : ℕ} {c : Matrix (Fin N) (Fin N) ℂ} (hc : InFlagDomain N j c)
    (k : ℕ) : (gramHead (sigForm N j) k c).det ≠ 0 := by
  obtain ⟨hcu, hneg⟩ := hc
  have hmN : N - j ≤ N := Nat.sub_le N j
  have hGH : (gramOf (sigForm N j) c)ᴴ = gramOf (sigForm N j) c := by
    have hs : (star fun i : Fin N => ((sigForm N j i : ℝ) : ℂ)) = fun i => ((sigForm N j i : ℝ) : ℂ) := by
      funext i
      simp
    simp only [gramOf, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.diagonal_conjTranspose, hs, Matrix.mul_assoc]
  have hnq : ∀ y : Fin N → ℂ, (∀ a : Fin N, ¬ (a : ℕ) < N - j → y a = 0) → y ≠ 0 →
      star y ⬝ᵥ (gramOf (sigForm N j) c *ᵥ y) < 0 := by
    intro y hy hy0
    have hext : (fun b : Fin N => if h : (b : ℕ) < N - j then y b else 0) = y := by
      funext b
      by_cases h : (b : ℕ) < N - j
      · simp [h]
      · simp [h, hy b h]
    have hy''0 : (fun b : {a : Fin N // (a : ℕ) < N - j} => y b) ≠ 0 := by
      intro h0
      apply hy0
      rw [← hext]
      funext b
      split_ifs with h
      · exact congrFun h0 ⟨b, h⟩
      · rfl
    have h1 := hneg.dotProduct_mulVec_pos hy''0
    rw [Matrix.neg_mulVec, dotProduct_neg, neg_pos] at h1
    have h2 := submatrix_quadForm_eq_quadForm_extend (gramOf (sigForm N j) c) (N - j)
      (fun b : {a : Fin N // (a : ℕ) < N - j} => y b)
    simp only [gramHead] at h1
    rw [h2] at h1
    simpa only [hext] using h1
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  set v' : Fin N → ℂ := fun b => if h : (b : ℕ) < k then v ⟨b, h⟩ else 0 with hvEq
  have hGv : ∀ a : Fin N, (a : ℕ) < k → (gramOf (sigForm N j) c *ᵥ v') a = 0 := fun a ha => by
    have h1 := congrFun hv ⟨a, ha⟩
    simp only [gramHead] at h1
    rw [submatrix_mulVec_eq_mulVec_extend] at h1
    exact h1
  have hvs : ∀ a : Fin N, ¬ (a : ℕ) < k → v' a = 0 := fun a ha => by simp [hvEq, ha]
  have hv'0 : v' ≠ 0 := by
    intro h0
    apply hv0
    funext b
    have h1 := congrFun h0 b
    simpa [hvEq, b.2] using h1
  have hQv : star v' ⬝ᵥ (gramOf (sigForm N j) c *ᵥ v') = 0 := dotProduct_eq_zero_of_disjoint_support _ _ fun a => by
    by_cases h : (a : ℕ) < k
    · exact Or.inr (hGv a h)
    · exact Or.inl (by simp [hvs a h])
  by_cases hkm : k ≤ N - j
  · exact hv'0 (by_contra fun h => (hnq v' (fun a ha => hvs a (by omega)) h).ne hQv)
  push_neg at hkm
  let Bm : Matrix (Fin N) (Option (Fin (N - j))) ℂ := fun a s =>
    match s with
    | none => v' a
    | some s => if (a : ℕ) = s then 1 else 0
  let Mx : Matrix (Option (Fin (N - j))) (Option (Fin (N - j))) ℂ := fun r s =>
    match r with
    | none => 0
    | some r => (c * Bm) (Fin.castLE hmN r) s
  have hdet0 : Mx.det = 0 := Matrix.det_eq_zero_of_row_eq_zero none fun s => rfl
  obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet0
  have hu : ∀ a : Fin N, (a : ℕ) < N - j → (c *ᵥ (Bm *ᵥ z)) a = 0 := fun a ha => by
    have h1 : ((c * Bm) *ᵥ z) (Fin.castLE hmN ⟨a, ha⟩) = 0 := congrFun hz (some ⟨a, ha⟩)
    rw [← Matrix.mulVec_mulVec] at h1
    have h2 : Fin.castLE hmN ⟨a, ha⟩ = a := Fin.ext rfl
    rwa [h2] at h1
  let y' : Fin N → ℂ := fun a => ∑ s : Fin (N - j), (if (a : ℕ) = s then 1 else 0) * z (some s)
  have hx : Bm *ᵥ z = y' + z none • v' := by
    funext a
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_option, Bm, y', Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  have hys : ∀ a : Fin N, ¬ (a : ℕ) < N - j → y' a = 0 := fun a ha =>
    Finset.sum_eq_zero fun s _ => by
      have h1 : (a : ℕ) ≠ s := fun h => ha (h ▸ s.2)
      simp [h1]
  have hcross : star (Bm *ᵥ z) ⬝ᵥ (gramOf (sigForm N j) c *ᵥ (Bm *ᵥ z)) =
      star y' ⬝ᵥ (gramOf (sigForm N j) c *ᵥ y') := by
    rw [hx]
    refine quadForm_add_smul_eq_of_orthogonal_support _ hGH _ _ _ (fun a => ?_) (fun a => ?_)
    · by_cases h : (a : ℕ) < N - j
      · exact Or.inr (hGv a (by omega))
      · exact Or.inl (hys a h)
    · by_cases h : (a : ℕ) < k
      · exact Or.inr (hGv a h)
      · exact Or.inl (hvs a h)
  have hQD : star (Bm *ᵥ z) ⬝ᵥ (gramOf (sigForm N j) c *ᵥ (Bm *ᵥ z)) =
      star (c *ᵥ (Bm *ᵥ z)) ⬝ᵥ (c *ᵥ (Bm *ᵥ z)) := by
    rw [gramOf, quadForm_conjTranspose_mul_mul]
    exact quadForm_diagonal_eq_of_support (N - j) _ (fun a ha => by simp [sigForm, ha]) _ hu
  have hnonneg : 0 ≤ star (c *ᵥ (Bm *ᵥ z)) ⬝ᵥ (c *ᵥ (Bm *ᵥ z)) := by
    first
      | exact dotProduct_star_self_nonneg _
      | exact Matrix.dotProduct_star_self_nonneg _
  have hy0 : y' = 0 := by
    by_contra h
    have h1 := hnq y' hys h
    rw [← hcross, hQD] at h1
    exact absurd (h1.trans_le hnonneg) (lt_irrefl _)
  have hu0 : c *ᵥ (Bm *ᵥ z) = 0 := by
    have h1 : star (c *ᵥ (Bm *ᵥ z)) ⬝ᵥ (c *ᵥ (Bm *ᵥ z)) = 0 := by
      rw [← hQD, hcross, hy0]
      simp
    first
      | exact dotProduct_star_self_eq_zero.1 h1
      | exact Matrix.dotProduct_star_self_eq_zero.1 h1
  have hx0 : Bm *ᵥ z = 0 := by
    have h1 : c⁻¹ *ᵥ (c *ᵥ (Bm *ᵥ z)) = Bm *ᵥ z := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul c hcu, Matrix.one_mulVec]
    rw [← h1, hu0, Matrix.mulVec_zero]
  have hzn : z none = 0 := by
    rw [hx, hy0, zero_add] at hx0
    exact (smul_eq_zero.1 hx0).resolve_right hv'0
  have hzs : ∀ s : Fin (N - j), z (some s) = 0 := fun s => by
    have h1 := congrFun hy0 (Fin.castLE hmN s)
    simp only [y', Pi.zero_apply] at h1
    rw [Finset.sum_eq_single s] at h1
    · simpa using h1
    · intro b _ hb
      have h2 : (s : ℕ) ≠ b := fun h => hb (Fin.ext h.symm)
      simp [Fin.coe_castLE, h2]
    · simp
  apply hz0
  funext o
  cases o with
  | none => exact hzn
  | some s => exact hzs s

/- English proof (translation)
Establish `key : ∀ k, gramLog (sigForm N j) k (c * b) = gramLog (sigForm N j) k c + diagLog b k` using `fun k => (gramLog_inv N (sigForm N j) k c 1 b).2 hb hu (gramHead_det_ne_zero_of_inFlagDomain hc k)`. Establish `hi` using `i.isLt`. Unfold `stepPot stepCorr`. Use `split_ifs with h`. Rewrite using `[key (N - j + (↑i + 1)), key (N - j)]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key N, key (N - j), key (↑i + 1 - j)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem stepPot_mul_triangular {j : ℕ} (hj : j ≤ N) {c b : Matrix (Fin N) (Fin N) ℂ}
    (hc : InFlagDomain N j c) (hb : b.BlockTriangular id) (hu : IsUnit b.det) (i : Fin N) :
    stepPot N j i (c * b) = stepPot N j i c + stepCorr N j i b := by
  have key : ∀ k, gramLog (sigForm N j) k (c * b) = gramLog (sigForm N j) k c + diagLog b k :=
    fun k => (gramLog_inv N (sigForm N j) k c 1 b).2 hb hu (gramHead_det_ne_zero_of_inFlagDomain hc k)
  have hi := i.isLt
  unfold stepPot stepCorr
  split_ifs with h
  · rw [key (N - j + (↑i + 1)), key (N - j)]
    ring
  · rw [key N, key (N - j), key (↑i + 1 - j)]
    ring

/- English proof (translation)
Establish `h1 : gramOf hd g *ᵥ y = gᴴ *ᵥ (diagonal (fun i => ((hd i : ℝ) : ℂ)) *ᵥ (g *ᵥ y))`. Simplify using `only [gramOf, Matrix.mulVec_mulVec, Matrix.mul_assoc]`. Rewrite using `[h1, dotProduct_mulVec, ← star_mulVec]`. Simplify using `only [dotProduct, mulVec_diagonal, Pi.star_apply]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.
-/
private theorem bilinForm_gramOf_eq_sum (hd : Fin N → ℝ) (g : Matrix (Fin N) (Fin N) ℂ) (x y : Fin N → ℂ) :
    star x ⬝ᵥ (gramOf hd g *ᵥ y) =
      ∑ i, ((hd i : ℝ) : ℂ) * (star ((g *ᵥ x) i) * (g *ᵥ y) i) := by
  have h1 : gramOf hd g *ᵥ y =
      gᴴ *ᵥ (diagonal (fun i => ((hd i : ℝ) : ℂ)) *ᵥ (g *ᵥ y)) := by
    simp only [gramOf, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [h1, dotProduct_mulVec, ← star_mulVec]
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

/- English proof (translation)
Rewrite using `[bilinForm_gramOf_eq_sum, bilinForm_gramOf_eq_sum, star_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [star_mul', star_star, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem star_quadForm_gramOf_swap (hd : Fin N → ℝ) (g : Matrix (Fin N) (Fin N) ℂ) (x y : Fin N → ℂ) :
    star (star x ⬝ᵥ (gramOf hd g *ᵥ y)) = star y ⬝ᵥ (gramOf hd g *ᵥ x) := by
  rw [bilinForm_gramOf_eq_sum, bilinForm_gramOf_eq_sum, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [star_mul', star_star, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
  ring

/- English proof (translation)
Establish `h` using `star_quadForm_gramOf_swap hd g y y`. Establish `h2` using `congrArg Complex.im h`. Rewrite `h2` using `[Complex.star_def, Complex.conj_im]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem im_quadForm_gramOf_eq_zero (hd : Fin N → ℝ) (g : Matrix (Fin N) (Fin N) ℂ) (y : Fin N → ℂ) :
    (star y ⬝ᵥ (gramOf hd g *ᵥ y)).im = 0 := by
  have h := star_quadForm_gramOf_swap hd g y y
  have h2 := congrArg Complex.im h
  rw [Complex.star_def, Complex.conj_im] at h2
  linarith

/- English proof (translation)
Take `⟨_, hP⟩` from `hg`. Use `set x : {a : Fin N // (a : ℕ) < N - j} → ℂ := fun a => w a.1 with hx`. Establish `hx0 : x ≠ 0`. Introduce `h`. Apply `hw0` to reduce the goal to its premises.

Use function extensionality and compare the values at `m`. Distinguish the cases in `hm : (m : ℕ) < N - j`. Conclude with `congrFun h ⟨m, hm⟩`. Conclude with `hw m (not_lt.1 hm)`. Establish `h1` using `hP.dotProduct_mulVec_pos hx0`.

Establish `hsplit : ∀ f : Fin N → ℂ, (∀ m : Fin N, N - j ≤ (m : ℕ) → f m = 0) → ∑ a : {a : Fin N // (a : ℕ) < N - j}, f a.1 = ∑ m, f m`. Introduce `f hf`. Rewrite using `[← Fintype.sum_subtype_add_sum_subtype (fun m : Fin N => (m : ℕ) < N - j) f]`. Establish `: ∑ m : {m : Fin N // ¬ (m : ℕ) < N - j}, f m.1 = 0` using `Finset.sum_eq_zero fun m _ => hf m.1 (not_lt.1 m.2)`. Rewrite using `[this, add_zero]`.

Establish `key : star x ⬝ᵥ ((-gramHead (sigForm N j) (N - j) g) *ᵥ x) = -(star w ⬝ᵥ (gramOf (sigForm N j) g *ᵥ w))`. Rewrite using `[Matrix.neg_mulVec, dotProduct_neg]`. Use `congr 1`. Simplify using `only [dotProduct, mulVec, gramHead, Matrix.submatrix_apply, x, Pi.star_apply]`. Establish `hin : ∀ a : Fin N, ∑ b : {b : Fin N // (b : ℕ) < N - j}, gramOf (sigForm N j) g a b.1 * w b.1 = ∑ b, gramOf (sigForm N j) g a b * w b` using `fun a => hsplit (fun b => gramOf (sigForm N j) g a b * w b) (fun m hm => by rw [hw m hm, mul_zero])`.

Simplify using `only [hin]`. Establish `hout` using `hsplit (fun a => star (w a) * ∑ b, gramOf (sigForm N j) g a b * w b) (fun m hm => by rw [hw m hm]; simp)`. Conclude with `hout`. Rewrite `h1` using `[key]`. Establish `h2` using `(Complex.pos_iff.1 h1).1`.

Rewrite `h2` using `[Complex.neg_re]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem re_quadForm_gramOf_neg_of_inFlagDomain {j : ℕ} {g : Matrix (Fin N) (Fin N) ℂ} (hg : InFlagDomain N j g)
    (w : Fin N → ℂ) (hw : ∀ m : Fin N, N - j ≤ (m : ℕ) → w m = 0) (hw0 : w ≠ 0) :
    (star w ⬝ᵥ (gramOf (sigForm N j) g *ᵥ w)).re < 0 := by
  classical
  obtain ⟨_, hP⟩ := hg
  set x : {a : Fin N // (a : ℕ) < N - j} → ℂ := fun a => w a.1 with hx
  have hx0 : x ≠ 0 := by
    intro h
    apply hw0
    funext m
    by_cases hm : (m : ℕ) < N - j
    · exact congrFun h ⟨m, hm⟩
    · exact hw m (not_lt.1 hm)
  have h1 := hP.dotProduct_mulVec_pos hx0
  have hsplit : ∀ f : Fin N → ℂ, (∀ m : Fin N, N - j ≤ (m : ℕ) → f m = 0) →
      ∑ a : {a : Fin N // (a : ℕ) < N - j}, f a.1 = ∑ m, f m := by
    intro f hf
    rw [← Fintype.sum_subtype_add_sum_subtype (fun m : Fin N => (m : ℕ) < N - j) f]
    have : ∑ m : {m : Fin N // ¬ (m : ℕ) < N - j}, f m.1 = 0 :=
      Finset.sum_eq_zero fun m _ => hf m.1 (not_lt.1 m.2)
    rw [this, add_zero]
  have key : star x ⬝ᵥ ((-gramHead (sigForm N j) (N - j) g) *ᵥ x) =
      -(star w ⬝ᵥ (gramOf (sigForm N j) g *ᵥ w)) := by
    rw [Matrix.neg_mulVec, dotProduct_neg]
    congr 1
    simp only [dotProduct, mulVec, gramHead, Matrix.submatrix_apply, x, Pi.star_apply]
    have hin : ∀ a : Fin N, ∑ b : {b : Fin N // (b : ℕ) < N - j}, gramOf (sigForm N j) g a b.1 * w b.1 =
        ∑ b, gramOf (sigForm N j) g a b * w b := fun a =>
      hsplit (fun b => gramOf (sigForm N j) g a b * w b) (fun m hm => by rw [hw m hm, mul_zero])
    simp only [hin]
    have hout := hsplit (fun a => star (w a) * ∑ b, gramOf (sigForm N j) g a b * w b)
      (fun m hm => by rw [hw m hm]; simp)
    exact hout
  rw [key] at h1
  have h2 := (Complex.pos_iff.1 h1).1
  rw [Complex.neg_re] at h2
  linarith
/- English proof (translation)
Establish `h1 : gramOf hd g *ᵥ y = gᴴ *ᵥ (diagonal (fun i => ((hd i : ℝ) : ℂ)) *ᵥ (g *ᵥ y))`. Simplify using `only [gramOf, Matrix.mulVec_mulVec, Matrix.mul_assoc]`. Rewrite using `[h1, dotProduct_mulVec, ← star_mulVec]`. Simplify using `only [dotProduct, mulVec_diagonal, Pi.star_apply]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.
-/
private theorem quadForm_gramOf_eq_sum (hd : Fin N → ℝ) (g : Matrix (Fin N) (Fin N) ℂ) (y : Fin N → ℂ) :
    star y ⬝ᵥ (gramOf hd g *ᵥ y) =
      ∑ i, ((hd i : ℝ) : ℂ) * (star ((g *ᵥ y) i) * (g *ᵥ y) i) := by
  have h1 : gramOf hd g *ᵥ y =
      gᴴ *ᵥ (diagonal (fun i => ((hd i : ℝ) : ℂ)) *ᵥ (g *ᵥ y)) := by
    simp only [gramOf, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [h1, dotProduct_mulVec, ← star_mulVec]
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

/- English proof (translation)
Use `set G := gramOf (sigForm N j) g with hG`. Use `set M : Matrix (Option {a : Fin N // (a : ℕ) < N - j}) (Option {a : Fin N // (a : ℕ) < N - j}) ℂ := Matrix.of fun r s => r.elim 0 fun i => (g *ᵥ V s) i.1 with hM`. Establish `hdet : M.det = 0` using `Matrix.det_eq_zero_of_row_eq_zero none fun s => rfl`. Take `⟨x, hx0, hMx⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 hdet`. Use `set y : Fin N → ℂ := ∑ s, x s • V s with hy`.

Establish `hgy : ∀ i : {a : Fin N // (a : ℕ) < N - j}, (g *ᵥ y) i.1 = 0`. Introduce `i`. Establish `h` using `congrFun hMx (some i)`. Rewrite `h` using `[Matrix.mulVec, dotProduct]`. Simplify using `only [M, Matrix.of_apply, Option.elim, Pi.zero_apply] at h`.

Rewrite using `[hy, Matrix.mulVec_sum, Finset.sum_apply, ← h]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, mul_comm]`. Establish `hexp : star y ⬝ᵥ (G *ᵥ y) = ∑ s, star (x s) * x s * (star (V s) ⬝ᵥ (G *ᵥ V s))`. Rewrite using `[hy, Matrix.mulVec_sum, star_sum, sum_dotProduct]`.

Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[dotProduct_sum, Finset.sum_eq_single s]`. Rewrite using `[Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul]`. Simplify using `only [smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `t _ hts`. Rewrite using `[Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, horth s t (Ne.symm hts)]`. Simplify using the standard rewrite rules. Introduce `h`. Conclude with `absurd (Finset.mem_univ s) h`.

Establish `hsq : ∀ z : ℂ, star z * z = ((Complex.normSq z : ℝ) : ℂ)`. Introduce `z`. Rewrite using `[Complex.normSq_eq_conj_mul_self]`. Both sides reduce to the same expression. Establish `hT : ∀ i, 0 ≤ (((sigForm N j i : ℝ) : ℂ) * (star ((g *ᵥ y) i) * (g *ᵥ y) i)).re`.

Introduce `i`. Distinguish the cases in `hi : (i : ℕ) < N - j`. Rewrite using `[hgy ⟨i, hi⟩]`. Simplify using the standard rewrite rules. Establish `hs : sigForm N j i = 1` using `by simp [sigForm, hi]`.

Rewrite using `[hs, hsq, Complex.ofReal_one, one_mul, Complex.ofReal_re]`. Conclude with `Complex.normSq_nonneg _`. Establish `hqf : (star y ⬝ᵥ (G *ᵥ y)).re = ∑ i, (((sigForm N j i : ℝ) : ℂ) * (star ((g *ᵥ y) i) * (g *ᵥ y) i)).re`. Rewrite using `[hG, quadForm_gramOf_eq_sum, Complex.re_sum]`. Establish `hpos : 0 ≤ (star y ⬝ᵥ (G *ᵥ y)).re`.

Rewrite using `[hqf]`. Conclude with `Finset.sum_nonneg fun i _ => hT i`. Establish `hre : (star y ⬝ᵥ (G *ᵥ y)).re = ∑ s, Complex.normSq (x s) * (star (V s) ⬝ᵥ (G *ᵥ V s)).re`. Rewrite using `[hexp, Complex.re_sum]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations.

Rewrite using `[hsq, Complex.re_ofReal_mul]`. Establish `hnp : ∀ s, Complex.normSq (x s) * (star (V s) ⬝ᵥ (G *ᵥ V s)).re ≤ 0`. Introduce `s`. Consider the cases of `s with`. Consider the case `none => exact mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) hk`.

Consider the case `some a => exact mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) (hneg a).le`. Distinguish the cases in `hex : ∃ a, x (some a) ≠ 0`. Take `⟨a, ha⟩` from `hex`. Establish `hlt : Complex.normSq (x (some a)) * (star (V (some a)) ⬝ᵥ (G *ᵥ V (some a))).re < 0` using `mul_neg_of_pos_of_neg (Complex.normSq_pos.2 ha) (hneg a)`. Establish `hle : ∑ s, Complex.normSq (x s) * (star (V s) ⬝ᵥ (G *ᵥ V s)).re ≤ Complex.normSq (x (some a)) * (star (V (some a)) ⬝ᵥ (G *ᵥ V (some a))).re`.

Establish `h` using `Finset.single_le_sum (f := fun s => -(Complex.normSq (x s) * (star (V s) ⬝ᵥ (G *ᵥ V s)).re)) (fun s _ => neg_nonneg.2 (hnp s)) (Finset.mem_univ (some a))`. Simplify using `only [Finset.sum_neg_distrib] at h`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Use `push_neg at hex`.

Establish `hxn : x none ≠ 0`. Introduce `h0`. Apply `hx0` to reduce the goal to its premises. Use function extensionality and compare the values at `s`. Consider the cases of `s with`.

Consider the case `none => exact h0`. Consider the case `some a => exact hex a`. Establish `hy' : y = x none • V none`. Rewrite using `[hy, Fintype.sum_option]`. Simplify using `[hex]`.

Establish `hzero : (star y ⬝ᵥ (G *ᵥ y)).re = 0`. Establish `: (star y ⬝ᵥ (G *ᵥ y)).re ≤ 0`. Rewrite using `[hre]`. Conclude with `Finset.sum_nonpos fun s _ => hnp s`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hall` using `(Finset.sum_eq_zero_iff_of_nonneg fun i _ => hT i).1 (by rw [← hqf]; exact hzero)`. Establish `hgy0 : g *ᵥ y = 0`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : (i : ℕ) < N - j`. Conclude with `hgy ⟨i, hi⟩`.

Establish `hs : sigForm N j i = 1` using `by simp [sigForm, hi]`. Establish `h` using `hall i (Finset.mem_univ i)`. Rewrite `h` using `[hs, hsq, Complex.ofReal_one, one_mul, Complex.ofReal_re]`. Simplify using `using Complex.normSq_eq_zero.1 h`. Establish `hinj : Function.Injective g.mulVec` using `Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det g).2 hgU)`.

Establish `hy0 : y = 0` using `hinj (by rw [hgy0, Matrix.mulVec_zero])`. Rewrite `hy0` using `[hy']`. Conclude with `hw ((smul_eq_zero.1 hy0).resolve_left hxn)`.
-/
private theorem false_of_gramOf_orthogonal_nonpos_family {j : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (hgU : IsUnit g.det)
    (V : Option {a : Fin N // (a : ℕ) < N - j} → Fin N → ℂ)
    (horth : ∀ s s', s ≠ s' → star (V s) ⬝ᵥ (gramOf (sigForm N j) g *ᵥ V s') = 0)
    (hneg : ∀ a, (star (V (some a)) ⬝ᵥ (gramOf (sigForm N j) g *ᵥ V (some a))).re < 0)
    (hk : (star (V none) ⬝ᵥ (gramOf (sigForm N j) g *ᵥ V none)).re ≤ 0)
    (hw : V none ≠ 0) : False := by
  classical
  set G := gramOf (sigForm N j) g with hG
  set M : Matrix (Option {a : Fin N // (a : ℕ) < N - j}) (Option {a : Fin N // (a : ℕ) < N - j}) ℂ :=
    Matrix.of fun r s => r.elim 0 fun i => (g *ᵥ V s) i.1 with hM
  have hdet : M.det = 0 := Matrix.det_eq_zero_of_row_eq_zero none fun s => rfl
  obtain ⟨x, hx0, hMx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  set y : Fin N → ℂ := ∑ s, x s • V s with hy
  have hgy : ∀ i : {a : Fin N // (a : ℕ) < N - j}, (g *ᵥ y) i.1 = 0 := by
    intro i
    have h := congrFun hMx (some i)
    rw [Matrix.mulVec, dotProduct] at h
    simp only [M, Matrix.of_apply, Option.elim, Pi.zero_apply] at h
    rw [hy, Matrix.mulVec_sum, Finset.sum_apply, ← h]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  have hexp : star y ⬝ᵥ (G *ᵥ y) =
      ∑ s, star (x s) * x s * (star (V s) ⬝ᵥ (G *ᵥ V s)) := by
    rw [hy, Matrix.mulVec_sum, star_sum, sum_dotProduct]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [dotProduct_sum, Finset.sum_eq_single s]
    · rw [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul]
      simp only [smul_eq_mul]
      ring
    · intro t _ hts
      rw [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, horth s t (Ne.symm hts)]
      simp
    · intro h
      exact absurd (Finset.mem_univ s) h
  have hsq : ∀ z : ℂ, star z * z = ((Complex.normSq z : ℝ) : ℂ) := by
    intro z
    rw [Complex.normSq_eq_conj_mul_self]
    rfl
  have hT : ∀ i, 0 ≤ (((sigForm N j i : ℝ) : ℂ) * (star ((g *ᵥ y) i) * (g *ᵥ y) i)).re := by
    intro i
    by_cases hi : (i : ℕ) < N - j
    · rw [hgy ⟨i, hi⟩]
      simp
    · have hs : sigForm N j i = 1 := by simp [sigForm, hi]
      rw [hs, hsq, Complex.ofReal_one, one_mul, Complex.ofReal_re]
      exact Complex.normSq_nonneg _
  have hqf : (star y ⬝ᵥ (G *ᵥ y)).re =
      ∑ i, (((sigForm N j i : ℝ) : ℂ) * (star ((g *ᵥ y) i) * (g *ᵥ y) i)).re := by
    rw [hG, quadForm_gramOf_eq_sum, Complex.re_sum]
  have hpos : 0 ≤ (star y ⬝ᵥ (G *ᵥ y)).re := by
    rw [hqf]
    exact Finset.sum_nonneg fun i _ => hT i
  have hre : (star y ⬝ᵥ (G *ᵥ y)).re =
      ∑ s, Complex.normSq (x s) * (star (V s) ⬝ᵥ (G *ᵥ V s)).re := by
    rw [hexp, Complex.re_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hsq, Complex.re_ofReal_mul]
  have hnp : ∀ s, Complex.normSq (x s) * (star (V s) ⬝ᵥ (G *ᵥ V s)).re ≤ 0 := by
    intro s
    cases s with
    | none => exact mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) hk
    | some a => exact mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) (hneg a).le
  by_cases hex : ∃ a, x (some a) ≠ 0
  · obtain ⟨a, ha⟩ := hex
    have hlt : Complex.normSq (x (some a)) * (star (V (some a)) ⬝ᵥ (G *ᵥ V (some a))).re < 0 :=
      mul_neg_of_pos_of_neg (Complex.normSq_pos.2 ha) (hneg a)
    have hle : ∑ s, Complex.normSq (x s) * (star (V s) ⬝ᵥ (G *ᵥ V s)).re ≤
        Complex.normSq (x (some a)) * (star (V (some a)) ⬝ᵥ (G *ᵥ V (some a))).re := by
      have h := Finset.single_le_sum
        (f := fun s => -(Complex.normSq (x s) * (star (V s) ⬝ᵥ (G *ᵥ V s)).re))
        (fun s _ => neg_nonneg.2 (hnp s)) (Finset.mem_univ (some a))
      simp only [Finset.sum_neg_distrib] at h
      linarith
    linarith
  · push_neg at hex
    have hxn : x none ≠ 0 := by
      intro h0
      apply hx0
      funext s
      cases s with
      | none => exact h0
      | some a => exact hex a
    have hy' : y = x none • V none := by
      rw [hy, Fintype.sum_option]
      simp [hex]
    have hzero : (star y ⬝ᵥ (G *ᵥ y)).re = 0 := by
      have : (star y ⬝ᵥ (G *ᵥ y)).re ≤ 0 := by
        rw [hre]
        exact Finset.sum_nonpos fun s _ => hnp s
      linarith
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hT i).1 (by rw [← hqf]; exact hzero)
    have hgy0 : g *ᵥ y = 0 := by
      funext i
      by_cases hi : (i : ℕ) < N - j
      · exact hgy ⟨i, hi⟩
      · have hs : sigForm N j i = 1 := by simp [sigForm, hi]
        have h := hall i (Finset.mem_univ i)
        rw [hs, hsq, Complex.ofReal_one, one_mul, Complex.ofReal_re] at h
        simpa using Complex.normSq_eq_zero.1 h
    have hinj : Function.Injective g.mulVec :=
      Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det g).2 hgU)
    have hy0 : y = 0 := hinj (by rw [hgy0, Matrix.mulVec_zero])
    rw [hy'] at hy0
    exact hw ((smul_eq_zero.1 hy0).resolve_left hxn)
/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `_`. Use `⟨fun a => Pi.single a 1, fun a m ham => ?_, fun a => by simp, fun a b hab => ?_⟩` and prove the remaining obligations.

Simplify using `[Pi.single_apply, (ne_of_lt ham).symm]`. Use linear arithmetic over natural numbers and integers. Consider the case `succ k ih`. Introduce `hk`. Take `⟨v, hsup, hdg, hor⟩` from `ih (by omega)`.

Use `set G := gramOf (sigForm N j) g with hG`. Use `set kk : Fin N := ⟨k, by omega⟩ with hkk`. Use `set h := star (v kk) ⬝ᵥ (G *ᵥ v kk) with hh`. Establish `hreal : h = ((h.re : ℝ) : ℂ)` using `Complex.ext (by simp) (by simp [hh, hG, im_quadForm_gramOf_eq_zero])`. Establish `hw0 : v kk ≠ 0` using `fun h0 => hdg kk (by rw [h0]; rfl)`.

Establish `hsgn : h.re = sigForm N j kk * |h.re| ∧ h.re ≠ 0`. Distinguish the cases in `hkj : k < N - j`. Establish `hs : sigForm N j kk = -1` using `by simp [sigForm, hkk, hkj]`. Establish `hneg : h.re < 0` using `re_quadForm_gramOf_neg_of_inFlagDomain hg (v kk) (fun m hm => hsup kk m (by rw [Fin.lt_def]; simp only [hkk]; omega)) hw0`. Rewrite using `[hs, abs_of_neg hneg]`.

Conclude with `⟨by ring, hneg.ne⟩`. Establish `hs : sigForm N j kk = 1` using `by simp [sigForm, hkk, hkj]`. Establish `hpos : 0 < h.re`. Assume the negation of the conclusion as `hle`. Use `push_neg at hle`.

Use `false_of_gramOf_orthogonal_nonpos_family g hg.1 (fun s => s.elim (v kk) fun a => v a.1) ?_ ?_ hle hw0` and prove the remaining obligations. Introduce `s s' hss`. Consider the cases of `s with`. Consider the case `none`. Consider the cases of `s' with`.

Consider the case `none => exact absurd rfl hss`. Consider the case `some b`. Establish `hb : (b.1 : ℕ) < k` using `by have := b.2; omega`. Establish `hne : kk ≠ b.1`. Introduce `e`.

Rewrite `hb` using `[← e]`. Simplify using `[hkk] at hb`. Simplify using `only [Option.elim]`. Rewrite using `[hor kk b.1 (Or.inr hb)]`. Simplify using `[hne]`.

Consider the case `some a`. Establish `ha : (a.1 : ℕ) < k` using `by have := a.2; omega`. Consider the cases of `s' with`. Consider the case `none`. Establish `hne : a.1 ≠ kk`.

Introduce `e`. Rewrite `ha` using `[e]`. Simplify using `[hkk] at ha`. Simplify using `only [Option.elim]`. Rewrite using `[hor a.1 kk (Or.inl ha)]`.

Simplify using `[hne]`. Consider the case `some b`. Establish `hne : a.1 ≠ b.1` using `fun e => hss (by rw [Subtype.ext e])`. Simplify using `only [Option.elim]`. Rewrite using `[hor a.1 b.1 (Or.inl ha)]`.

Simplify using `[hne]`. Introduce `a`. Establish `ha : (a.1 : ℕ) < k` using `by have := a.2; omega`. Simplify using `only [Option.elim]`. Rewrite using `[hor a.1 a.1 (Or.inl ha)]`.

Simplify using `[sigForm, a.2]`. Rewrite using `[hs, abs_of_pos hpos]`. Conclude with `⟨by ring, hpos.ne'⟩`. Take `⟨hsg, hne⟩` from `hsgn`. Use `set r := |h.re| with hr`.

Establish `hr0 : 0 < r` using `abs_pos.2 hne`. Use `set t : ℝ := (Real.sqrt r)⁻¹ with ht`. Establish `htt : t * t * r = 1`. Rewrite using `[ht, ← mul_inv, Real.mul_self_sqrt hr0.le, inv_mul_cancel₀ hr0.ne']`. Establish `ht0 : (t : ℂ) ≠ 0`.

Rewrite using `[Complex.ofReal_ne_zero, ht]`. Conclude with `inv_ne_zero (Real.sqrt_pos.2 hr0).ne'`. Establish `hh0 : h ≠ 0` using `fun e => hne (by rw [e]; simp)`. Establish `hstar : star (t : ℂ) = t` using `by rw [Complex.star_def, Complex.conj_ofReal]`. Use `set v' : Fin N → Fin N → ℂ := fun a => if a = kk then (t : ℂ) • v kk else if kk < a then v a - (star (v kk) ⬝ᵥ (G *ᵥ v a) / h) • v kk else v a with hv'`.

Establish `hlow : ∀ b : Fin N, ¬ b = kk → ¬ kk < b → (b : ℕ) < k`. Introduce `b h1 h2`. Rewrite `h2` using `[Fin.lt_def]`. Establish `: (b : ℕ) ≠ k` using `fun e => h1 (Fin.ext e)`. Simplify using `only [hkk] at h2`.

Use linear arithmetic over natural numbers and integers. Establish `main : ∀ a b : Fin N, (a : ℕ) < k + 1 → star (v' a) ⬝ᵥ (G *ᵥ v' b) = if a = b then ((sigForm N j a : ℝ) : ℂ) else 0`. Introduce `a b ha`. Distinguish the cases in `ha1 : a = kk`. Substitute `ha1` using the available equality.

Distinguish the cases in `hb1 : b = kk`. Substitute `hb1` using the available equality. Simplify using `only [hv', if_pos rfl, Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct, smul_eq_mul, hstar]`. Rewrite using `[← hh, hreal, hsg]`. Establish `: (t : ℂ) * (t * ((sigForm N j kk * r : ℝ) : ℂ)) = ((t * t * r * sigForm N j kk : ℝ) : ℂ)`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, htt, one_mul, if_pos trivial]`. Establish `hkb : kk ≠ b` using `fun e => hb1 e.symm`. Distinguish the cases in `hb2 : kk < b`.

Simplify using `only [hv', if_pos rfl, if_neg hb1, if_pos hb2, if_neg hkb, Matrix.mulVec_smul, Matrix.mulVec_sub, dotProduct_smul, dotProduct_sub, star_smul, smul_dotProduct, smul_eq_mul, hstar]`. Rewrite using `[← hh]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hb : (b : ℕ) < k` using `hlow b hb1 hb2`.

Simplify using `only [hv', if_pos rfl, if_neg hb1, if_neg hb2, if_neg hkb, Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct, smul_eq_mul, hstar]`. Establish `h1` using `hor b kk (Or.inl hb)`. Rewrite `h1` using `[if_neg hb1]`. Rewrite using `[← star_quadForm_gramOf_swap, h1]`. Simplify using the standard rewrite rules.

Establish `ha2 : ¬ kk < a`. Introduce `e`. Rewrite `e` using `[Fin.lt_def]`. Simplify using `only [hkk] at e`. Use linear arithmetic over natural numbers and integers.

Establish `hak : (a : ℕ) < k` using `hlow a ha1 ha2`. Distinguish the cases in `hb1 : b = kk`. Substitute `hb1` using the available equality. Simplify using `only [hv', if_neg ha1, if_neg ha2, if_pos rfl, if_neg ha1, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]`. Rewrite using `[hor a kk (Or.inl hak), if_neg ha1]`.

Simplify using the standard rewrite rules. Distinguish the cases in `hb2 : kk < b`. Simplify using `only [hv', if_neg ha1, if_neg ha2, if_neg hb1, if_pos hb2, Matrix.mulVec_smul, Matrix.mulVec_sub, dotProduct_smul, dotProduct_sub, smul_eq_mul]`. Rewrite using `[hor a b (Or.inl hak), hor a kk (Or.inl hak), if_neg ha1]`. Simplify using the standard rewrite rules.

Simplify using `only [hv', if_neg ha1, if_neg ha2, if_neg hb1, if_neg hb2]`. Conclude with `hor a b (Or.inl hak)`. Use `⟨v', fun a m ham => ?_, fun a => ?_, fun a b hab => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h1 : a = kk`. Substitute `h1` using the available equality.

Simplify using `[hv', hsup _ m ham]`. Distinguish the cases in `h2 : kk < a`. Simplify using `[hv', h1, h2, hsup a m ham, hsup kk m (h2.trans ham)]`. Simplify using `[hv', h1, h2, hsup a m ham]`. Distinguish the cases in `h1 : a = kk`.

Substitute `h1` using the available equality. Simplify using `only [hv', if_pos rfl, Pi.smul_apply, smul_eq_mul]`. Conclude with `mul_ne_zero ht0 (hdg _)`. Distinguish the cases in `h2 : kk < a`. Simplify using `[hv', h1, h2, hsup kk a h2, hdg a]`.

Simplify using `[hv', h1, h2, hdg a]`. Break down `hab with hab | hab` into its components or cases. Conclude with `main a b hab`. Rewrite using `[← star_quadForm_gramOf_swap, main b a hab]`. Distinguish the cases in `e : b = a`.

Substitute `e` using the available equality. Simplify using `[Complex.star_def, Complex.conj_ofReal]`. Simplify using `[e, Ne.symm e]`.
-/
private theorem exists_triangular_gram_orthonormal_of_inFlagDomain {j : ℕ} {g : Matrix (Fin N) (Fin N) ℂ} (hg : InFlagDomain N j g) :
    ∀ k ≤ N, ∃ v : Fin N → Fin N → ℂ, (∀ a m : Fin N, a < m → v a m = 0) ∧ (∀ a, v a a ≠ 0) ∧
      ∀ a b : Fin N, ((a : ℕ) < k ∨ (b : ℕ) < k) →
        star (v a) ⬝ᵥ (gramOf (sigForm N j) g *ᵥ v b) =
          if a = b then ((sigForm N j a : ℝ) : ℂ) else 0 := by
  classical
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun a => Pi.single a 1, fun a m ham => ?_, fun a => by simp, fun a b hab => ?_⟩
    · simp [Pi.single_apply, (ne_of_lt ham).symm]
    · omega
  | succ k ih =>
    intro hk
    obtain ⟨v, hsup, hdg, hor⟩ := ih (by omega)
    set G := gramOf (sigForm N j) g with hG
    set kk : Fin N := ⟨k, by omega⟩ with hkk
    set h := star (v kk) ⬝ᵥ (G *ᵥ v kk) with hh
    have hreal : h = ((h.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hh, hG, im_quadForm_gramOf_eq_zero])
    have hw0 : v kk ≠ 0 := fun h0 => hdg kk (by rw [h0]; rfl)
    have hsgn : h.re = sigForm N j kk * |h.re| ∧ h.re ≠ 0 := by
      by_cases hkj : k < N - j
      · have hs : sigForm N j kk = -1 := by simp [sigForm, hkk, hkj]
        have hneg : h.re < 0 := re_quadForm_gramOf_neg_of_inFlagDomain hg (v kk)
          (fun m hm => hsup kk m (by rw [Fin.lt_def]; simp only [hkk]; omega)) hw0
        rw [hs, abs_of_neg hneg]
        exact ⟨by ring, hneg.ne⟩
      · have hs : sigForm N j kk = 1 := by simp [sigForm, hkk, hkj]
        have hpos : 0 < h.re := by
          by_contra hle
          push_neg at hle
          refine false_of_gramOf_orthogonal_nonpos_family g hg.1 (fun s => s.elim (v kk) fun a => v a.1) ?_ ?_ hle hw0
          · intro s s' hss
            cases s with
            | none =>
              cases s' with
              | none => exact absurd rfl hss
              | some b =>
                have hb : (b.1 : ℕ) < k := by have := b.2; omega
                have hne : kk ≠ b.1 := by
                  intro e
                  rw [← e] at hb
                  simp [hkk] at hb
                simp only [Option.elim]
                rw [hor kk b.1 (Or.inr hb)]
                simp [hne]
            | some a =>
              have ha : (a.1 : ℕ) < k := by have := a.2; omega
              cases s' with
              | none =>
                have hne : a.1 ≠ kk := by
                  intro e
                  rw [e] at ha
                  simp [hkk] at ha
                simp only [Option.elim]
                rw [hor a.1 kk (Or.inl ha)]
                simp [hne]
              | some b =>
                have hne : a.1 ≠ b.1 := fun e => hss (by rw [Subtype.ext e])
                simp only [Option.elim]
                rw [hor a.1 b.1 (Or.inl ha)]
                simp [hne]
          · intro a
            have ha : (a.1 : ℕ) < k := by have := a.2; omega
            simp only [Option.elim]
            rw [hor a.1 a.1 (Or.inl ha)]
            simp [sigForm, a.2]
        rw [hs, abs_of_pos hpos]
        exact ⟨by ring, hpos.ne'⟩
    obtain ⟨hsg, hne⟩ := hsgn
    set r := |h.re| with hr
    have hr0 : 0 < r := abs_pos.2 hne
    set t : ℝ := (Real.sqrt r)⁻¹ with ht
    have htt : t * t * r = 1 := by
      rw [ht, ← mul_inv, Real.mul_self_sqrt hr0.le, inv_mul_cancel₀ hr0.ne']
    have ht0 : (t : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero, ht]
      exact inv_ne_zero (Real.sqrt_pos.2 hr0).ne'
    have hh0 : h ≠ 0 := fun e => hne (by rw [e]; simp)
    have hstar : star (t : ℂ) = t := by rw [Complex.star_def, Complex.conj_ofReal]
    set v' : Fin N → Fin N → ℂ := fun a => if a = kk then (t : ℂ) • v kk
      else if kk < a then v a - (star (v kk) ⬝ᵥ (G *ᵥ v a) / h) • v kk else v a with hv'
    have hlow : ∀ b : Fin N, ¬ b = kk → ¬ kk < b → (b : ℕ) < k := by
      intro b h1 h2
      rw [Fin.lt_def] at h2
      have : (b : ℕ) ≠ k := fun e => h1 (Fin.ext e)
      simp only [hkk] at h2
      omega
    have main : ∀ a b : Fin N, (a : ℕ) < k + 1 → star (v' a) ⬝ᵥ (G *ᵥ v' b) =
        if a = b then ((sigForm N j a : ℝ) : ℂ) else 0 := by
      intro a b ha
      by_cases ha1 : a = kk
      · subst ha1
        by_cases hb1 : b = kk
        · subst hb1
          simp only [hv', if_pos rfl, Matrix.mulVec_smul, dotProduct_smul, star_smul,
            smul_dotProduct, smul_eq_mul, hstar]
          rw [← hh, hreal, hsg]
          have : (t : ℂ) * (t * ((sigForm N j kk * r : ℝ) : ℂ)) = ((t * t * r * sigForm N j kk : ℝ) : ℂ) := by
            push_cast
            ring
          rw [this, htt, one_mul, if_pos trivial]
        · have hkb : kk ≠ b := fun e => hb1 e.symm
          by_cases hb2 : kk < b
          · simp only [hv', if_pos rfl, if_neg hb1, if_pos hb2, if_neg hkb, Matrix.mulVec_smul,
              Matrix.mulVec_sub, dotProduct_smul, dotProduct_sub, star_smul, smul_dotProduct,
              smul_eq_mul, hstar]
            rw [← hh]
            field_simp
            ring
          · have hb : (b : ℕ) < k := hlow b hb1 hb2
            simp only [hv', if_pos rfl, if_neg hb1, if_neg hb2, if_neg hkb, Matrix.mulVec_smul,
              dotProduct_smul, star_smul, smul_dotProduct, smul_eq_mul, hstar]
            have h1 := hor b kk (Or.inl hb)
            rw [if_neg hb1] at h1
            rw [← star_quadForm_gramOf_swap, h1]
            simp
      · have ha2 : ¬ kk < a := by
          intro e
          rw [Fin.lt_def] at e
          simp only [hkk] at e
          omega
        have hak : (a : ℕ) < k := hlow a ha1 ha2
        by_cases hb1 : b = kk
        · subst hb1
          simp only [hv', if_neg ha1, if_neg ha2, if_pos rfl, if_neg ha1, Matrix.mulVec_smul,
            dotProduct_smul, smul_eq_mul]
          rw [hor a kk (Or.inl hak), if_neg ha1]
          simp
        · by_cases hb2 : kk < b
          · simp only [hv', if_neg ha1, if_neg ha2, if_neg hb1, if_pos hb2, Matrix.mulVec_smul,
              Matrix.mulVec_sub, dotProduct_smul, dotProduct_sub, smul_eq_mul]
            rw [hor a b (Or.inl hak), hor a kk (Or.inl hak), if_neg ha1]
            simp
          · simp only [hv', if_neg ha1, if_neg ha2, if_neg hb1, if_neg hb2]
            exact hor a b (Or.inl hak)
    refine ⟨v', fun a m ham => ?_, fun a => ?_, fun a b hab => ?_⟩
    · by_cases h1 : a = kk
      · subst h1
        simp [hv', hsup _ m ham]
      · by_cases h2 : kk < a
        · simp [hv', h1, h2, hsup a m ham, hsup kk m (h2.trans ham)]
        · simp [hv', h1, h2, hsup a m ham]
    · by_cases h1 : a = kk
      · subst h1
        simp only [hv', if_pos rfl, Pi.smul_apply, smul_eq_mul]
        exact mul_ne_zero ht0 (hdg _)
      · by_cases h2 : kk < a
        · simp [hv', h1, h2, hsup kk a h2, hdg a]
        · simp [hv', h1, h2, hdg a]
    · rcases hab with hab | hab
      · exact main a b hab
      · rw [← star_quadForm_gramOf_swap, main b a hab]
        by_cases e : b = a
        · subst e
          simp [Complex.star_def, Complex.conj_ofReal]
        · simp [e, Ne.symm e]
/- English proof (translation)
Take `⟨v, hsup, hdg, hor⟩` from `exists_triangular_gram_orthonormal_of_inFlagDomain hg N le_rfl`. Use `set c : Matrix (Fin N) (Fin N) ℂ := Matrix.of fun m a => v a m with hc`. Establish `hct : c.BlockTriangular id` using `fun i j hji => hsup j i hji`. Establish `hcU : IsUnit c.det`. Rewrite using `[Matrix.det_of_upperTriangular hct]`.

Conclude with `isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun a _ => hdg a)`. Establish `hent : ∀ a b, (cᴴ * gramOf (sigForm N j) g * c) a b = star (v a) ⬝ᵥ (gramOf (sigForm N j) g *ᵥ v b)`. Introduce `a b`. Simplify using `only [c, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Conclude with `Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => by ring`. Use `haveI := Matrix.invertibleOfIsUnitDet c hcU`. Use `⟨g * c, c⁻¹, ?_, ?_, Matrix.blockTriangular_inv_of_blockTriangular hct, Matrix.isUnit_nonsing_inv_det c hcU, ?_⟩` and prove the remaining obligations. Use extensionality with `a b`. Rewrite using `[gramOf_mul, hent, hor a b (Or.inl a.2), Matrix.diagonal_apply]`.

Rewrite using `[Matrix.det_mul]`. Conclude with `hg.1.mul hcU`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_nonsing_inv c hcU, Matrix.mul_one]`.
-/
private theorem exists_unitary_mul_blockTriangular_of_inFlagDomain {j : ℕ} (hj : j ≤ N) {g : Matrix (Fin N) (Fin N) ℂ}
    (hg : InFlagDomain N j g) :
    ∃ u b : Matrix (Fin N) (Fin N) ℂ,
      gramOf (sigForm N j) u = diagonal (fun i => ((sigForm N j i : ℝ) : ℂ)) ∧
      IsUnit u.det ∧ b.BlockTriangular id ∧ IsUnit b.det ∧ g = u * b := by
  classical
  obtain ⟨v, hsup, hdg, hor⟩ := exists_triangular_gram_orthonormal_of_inFlagDomain hg N le_rfl
  set c : Matrix (Fin N) (Fin N) ℂ := Matrix.of fun m a => v a m with hc
  have hct : c.BlockTriangular id := fun i j hji => hsup j i hji
  have hcU : IsUnit c.det := by
    rw [Matrix.det_of_upperTriangular hct]
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun a _ => hdg a)
  have hent : ∀ a b, (cᴴ * gramOf (sigForm N j) g * c) a b =
      star (v a) ⬝ᵥ (gramOf (sigForm N j) g *ᵥ v b) := by
    intro a b
    simp only [c, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, dotProduct,
      Matrix.mulVec, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => by ring
  haveI := Matrix.invertibleOfIsUnitDet c hcU
  refine ⟨g * c, c⁻¹, ?_, ?_, Matrix.blockTriangular_inv_of_blockTriangular hct,
    Matrix.isUnit_nonsing_inv_det c hcU, ?_⟩
  · ext a b
    rw [gramOf_mul, hent, hor a b (Or.inl a.2), Matrix.diagonal_apply]
  · rw [Matrix.det_mul]
    exact hg.1.mul hcU
  · rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv c hcU, Matrix.mul_one]
/- English proof (translation)
Take `⟨hgU, hgP⟩` from `hg`. Establish `hinv : gramOf (sigForm N j) u⁻¹ = diagonal (fun i => ((sigForm N j i : ℝ) : ℂ))`. Establish `h1` using `gramOf_mul (sigForm N j) u u⁻¹`. Rewrite `h1` using `[Matrix.mul_nonsing_inv u huU, hu]`. Establish `h2 : gramOf (sigForm N j) (1 : Matrix (Fin N) (Fin N) ℂ) = diagonal (fun i => ((sigForm N j i : ℝ) : ℂ))`.

Simplify using `[gramOf]`. Rewrite `h1` using `[h2]`. Conclude with `h1.symm`. Establish `hG : gramOf (sigForm N j) (u⁻¹ * g * c) = cᴴ * gramOf (sigForm N j) g * c`. Rewrite using `[gramOf_mul, gramOf_mul, hinv]`.

Both sides reduce to the same expression. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_mul, Matrix.det_mul]`. Conclude with `((Matrix.isUnit_nonsing_inv_det u huU).mul hgU).mul hcU`. Establish `hv1 : Function.Injective (Subtype.val : {a : Fin N // (a : ℕ) < N - j} → Fin N)` using `Subtype.val_injective`.

Establish `hv2 : ∀ (i : Fin N) (c' : {a : Fin N // (a : ℕ) < N - j}), (∀ a : {a : Fin N // (a : ℕ) < N - j}, i ≠ a.1) → c'.1 < i`. Introduce `i c' hi`. Establish `h3 : ¬ ((i : ℕ) < N - j)` using `fun h => hi ⟨i, h⟩ rfl`. Establish `h4` using `c'.2`. Rewrite using `[Fin.lt_def]`.

Use linear arithmetic over natural numbers and integers. Establish `hsub` using `head_conj_mul (Subtype.val : {a : Fin N // (a : ℕ) < N - j} → Fin N) hv1 hv2 (gramOf (sigForm N j) g) c hc`. Establish `hcd : ∀ a, c a a ≠ 0`. Introduce `a`. Establish `h` using `hcU.ne_zero`.

Rewrite `h` using `[Matrix.det_of_upperTriangular hc]`. Conclude with `Finset.prod_ne_zero_iff.1 h a (Finset.mem_univ a)`. Use `show (-(gramOf (sigForm N j) (u⁻¹ * g * c)).submatrix Subtype.val Subtype.val).PosDef`. Rewrite using `[hG, hsub]`. Establish `hneg : ∀ (A B : Matrix {a : Fin N // (a : ℕ) < N - j} {a : Fin N // (a : ℕ) < N - j} ℂ), -(Bᴴ * A * B) = Bᴴ * (-A) * B`.

Introduce `A B`. Simplify using `[Matrix.mul_neg, Matrix.neg_mul]`. Rewrite using `[hneg]`. Use `Matrix.PosDef.conjTranspose_mul_mul_same hgP ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det]`.

Establish `hCt : (c.submatrix (Subtype.val : {a : Fin N // (a : ℕ) < N - j} → Fin N) Subtype.val).BlockTriangular id` using `hc.submatrix`. Rewrite using `[Matrix.det_of_upperTriangular hCt]`. Conclude with `isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun a _ => hcd a)`.
-/
private theorem inFlagDomain_inv_mul_mul {j : ℕ} {u g c : Matrix (Fin N) (Fin N) ℂ}
    (hu : gramOf (sigForm N j) u = diagonal (fun i => ((sigForm N j i : ℝ) : ℂ)))
    (huU : IsUnit u.det) (hg : InFlagDomain N j g) (hc : c.BlockTriangular id)
    (hcU : IsUnit c.det) : InFlagDomain N j (u⁻¹ * g * c) := by
  classical
  obtain ⟨hgU, hgP⟩ := hg
  have hinv : gramOf (sigForm N j) u⁻¹ = diagonal (fun i => ((sigForm N j i : ℝ) : ℂ)) := by
    have h1 := gramOf_mul (sigForm N j) u u⁻¹
    rw [Matrix.mul_nonsing_inv u huU, hu] at h1
    have h2 : gramOf (sigForm N j) (1 : Matrix (Fin N) (Fin N) ℂ) =
        diagonal (fun i => ((sigForm N j i : ℝ) : ℂ)) := by
      simp [gramOf]
    rw [h2] at h1
    exact h1.symm
  have hG : gramOf (sigForm N j) (u⁻¹ * g * c) = cᴴ * gramOf (sigForm N j) g * c := by
    rw [gramOf_mul, gramOf_mul, hinv]
    rfl
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_mul]
    exact ((Matrix.isUnit_nonsing_inv_det u huU).mul hgU).mul hcU
  · have hv1 : Function.Injective (Subtype.val : {a : Fin N // (a : ℕ) < N - j} → Fin N) :=
      Subtype.val_injective
    have hv2 : ∀ (i : Fin N) (c' : {a : Fin N // (a : ℕ) < N - j}),
        (∀ a : {a : Fin N // (a : ℕ) < N - j}, i ≠ a.1) → c'.1 < i := by
      intro i c' hi
      have h3 : ¬ ((i : ℕ) < N - j) := fun h => hi ⟨i, h⟩ rfl
      have h4 := c'.2
      rw [Fin.lt_def]
      omega
    have hsub := head_conj_mul (Subtype.val : {a : Fin N // (a : ℕ) < N - j} → Fin N) hv1 hv2
      (gramOf (sigForm N j) g) c hc
    have hcd : ∀ a, c a a ≠ 0 := by
      intro a
      have h := hcU.ne_zero
      rw [Matrix.det_of_upperTriangular hc] at h
      exact Finset.prod_ne_zero_iff.1 h a (Finset.mem_univ a)
    show (-(gramOf (sigForm N j) (u⁻¹ * g * c)).submatrix Subtype.val Subtype.val).PosDef
    rw [hG, hsub]
    have hneg : ∀ (A B : Matrix {a : Fin N // (a : ℕ) < N - j} {a : Fin N // (a : ℕ) < N - j} ℂ),
        -(Bᴴ * A * B) = Bᴴ * (-A) * B := by
      intro A B
      simp [Matrix.mul_neg, Matrix.neg_mul]
    rw [hneg]
    refine Matrix.PosDef.conjTranspose_mul_mul_same hgP ?_
    rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det]
    have hCt : (c.submatrix (Subtype.val : {a : Fin N // (a : ℕ) < N - j} → Fin N)
        Subtype.val).BlockTriangular id := hc.submatrix
    rw [Matrix.det_of_upperTriangular hCt]
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun a _ => hcd a)

/- English proof (translation)
Establish `hg0 : InFlagDomain N j (gc z0)` using `hdom.self_of_nhds`. Take `⟨u, b0, hu, huU, hb0, hb0U, hgu⟩` from `exists_unitary_mul_blockTriangular_of_inFlagDomain hj hg0`. Establish `hinvu : u⁻¹ * u = 1` using `Matrix.nonsing_inv_mul u huU`. Establish `huinv : u * u⁻¹ = 1` using `Matrix.mul_nonsing_inv u huU`. Use `set bf : Fin N → Fin N → ℂ := fun a b => b0 a b with hbf`.

Use `set M : (Fin e → ℂ) → (Fin N → Fin N → ℂ) := fun w a b => (u⁻¹ * gc w) a b with hM`. Establish `hMab : ∀ a b, AnalyticAt ℂ (fun w => M w a b) z0`. Introduce `a b`. Establish `h : AnalyticAt ℂ (∑ c, fun w => u⁻¹ a c * gc w c b) z0` using `Finset.analyticAt_sum _ fun c _ => analyticAt_const.mul (han c b)`. Use `h using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `w`. Simplify using `[M, Matrix.mul_apply, Finset.sum_apply]`. Establish `hMan : AnalyticAt ℂ M z0` using `AnalyticAt.pi fun a => AnalyticAt.pi fun b => hMab a b`. Establish `hF0 : PositivityTheory.Xgp.per_cell.FF bf = bf`. Use function extensionality and compare the values at `a b`.

Simplify using `[PositivityTheory.Xgp.per_cell.FF, bf, PositivityTheory.Xgp.per_cell.low_tri hb0, PositivityTheory.Xgp.per_cell.up_of_tri hb0, cellMat_zero N]`. Establish `hMz0 : M z0 = PositivityTheory.Xgp.per_cell.FF bf`. Rewrite using `[hF0]`. Use function extensionality and compare the values at `a b`. Simplify using `only [M, bf, hgu, ← Matrix.mul_assoc, hinvu, Matrix.one_mul]`.

Take `⟨ψ, hψ, hψ0, hψinv, hψd⟩` from `PositivityTheory.Xgp.per_cell.inv_an PositivityTheory.Xgp.per_cell.FF bf (PositivityTheory.Xgp.per_cell.LL b0) (PositivityTheory.Xgp.per_cell.an_FF _) (PositivityTheory.Xgp.per_cell.der_FF hb0) (PositivityTheory.Xgp.per_cell.inj_LL hb0 hb0U)`. Establish `hψ' : AnalyticAt ℂ ψ (M z0)` using `hMz0 ▸ hψ`. Use `set P : (Fin e → ℂ) → (Fin N → Fin N → ℂ) := fun w => ψ (M w) with hP`. Establish `hPan : AnalyticAt ℂ P z0` using `hψ'.comp hMan`. Establish `hP0 : P z0 = bf` using `by simp only [P, hMz0, hψ0]`.

Establish `hev : ∀ᶠ w in 𝓝 z0, PositivityTheory.Xgp.per_cell.FF (P w) = M w`. Establish `ht : Tendsto M (𝓝 z0) (𝓝 (PositivityTheory.Xgp.per_cell.FF bf))` using `hMz0 ▸ hMan.continuousAt.tendsto`. Conclude with `ht.eventually hψinv`. Establish `hdiag : ∀ a, b0 a a ≠ 0`. Introduce `a`.

Establish `h` using `hb0U.ne_zero`. Rewrite `h` using `[Matrix.det_of_upperTriangular hb0]`. Conclude with `Finset.prod_ne_zero_iff.1 h a (Finset.mem_univ a)`. Establish `hB0 : Matrix.of (PositivityTheory.Xgp.per_cell.up (P z0)) = b0`. Rewrite using `[hP0, PositivityTheory.Xgp.per_cell.up_of_tri hb0]`.

Both sides reduce to the same expression. Use `⟨fun w => PositivityTheory.Xgp.per_cell.low (P w), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(PositivityTheory.Xgp.per_cell.low.analyticAt _).comp hPan`. Simplify using `only [hP0, bf]`. Conclude with `PositivityTheory.Xgp.per_cell.low_tri hb0`.

Introduce `i`. Establish `hBan : ∀ a, AnalyticAt ℂ (fun w => Matrix.of (PositivityTheory.Xgp.per_cell.up (P w)) a a) z0`. Introduce `a`. Conclude with `((((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) a).comp (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => Fin N → ℂ) a)).comp PositivityTheory.Xgp.per_cell.up).analyticAt _).comp hPan`. Establish `hB0ne : ∀ a, Matrix.of (PositivityTheory.Xgp.per_cell.up (P z0)) a a ≠ 0`.

Introduce `a`. Rewrite using `[hB0]`. Conclude with `hdiag a`. Establish `hdetB : ∀ᶠ w in 𝓝 z0, IsUnit (Matrix.of (PositivityTheory.Xgp.per_cell.up (P w))).det`. Establish `hc : ContinuousAt (fun w => (Matrix.of (PositivityTheory.Xgp.per_cell.up (P w))).det) z0` using `(Continuous.matrix_det continuous_id).continuousAt.comp (PositivityTheory.Xgp.per_cell.up.continuous.continuousAt.comp hPan.continuousAt)`.

Establish `h0 : (Matrix.of (PositivityTheory.Xgp.per_cell.up (P z0))).det ≠ 0`. Rewrite using `[hB0]`. Conclude with `hb0U.ne_zero`. Use `filter_upwards [hc.eventually_ne h0] with w hw`. Conclude with `isUnit_iff_ne_zero.2 hw`.

Establish `hfac : ∀ᶠ w in 𝓝 z0, gc w = u * (cellMat N (PositivityTheory.Xgp.per_cell.low (P w)) * Matrix.of (PositivityTheory.Xgp.per_cell.up (P w)))` using `by filter_upwards [hev] with w hw`. Establish `hw' : cellMat N (PositivityTheory.Xgp.per_cell.low (P w)) * Matrix.of (PositivityTheory.Xgp.per_cell.up (P w)) = u⁻¹ * gc w`. Use extensionality with `a b`. Conclude with `congrFun (congrFun hw a) b`. Rewrite using `[hw', ← Matrix.mul_assoc, huinv, Matrix.one_mul]`.

Use `PlurRe.congr (plurRe_stepCorr (b := fun w => Matrix.of (PositivityTheory.Xgp.per_cell.up (P w))) hBan hB0ne j i) ?_` and prove the remaining obligations. Use `filter_upwards [hfac, hdetB, hdom] with w hw hdw hdom'`. Establish `hcell : InFlagDomain N j (cellMat N (PositivityTheory.Xgp.per_cell.low (P w)))` using `by haveI := Matrix.invertibleOfIsUnitDet _ hdw`. Use `inFlagDomain_inv_mul_mul hu huU hdom' (c := (Matrix.of (PositivityTheory.Xgp.per_cell.up (P w)))⁻¹) (Matrix.blockTriangular_inv_of_blockTriangular (PositivityTheory.Xgp.per_cell.up_tri _)) (Matrix.isUnit_nonsing_inv_det _ hdw)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[hw, ← Matrix.mul_assoc, hinvu, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdw, Matrix.mul_one]`. Rewrite using `[hw, stepPot_unitary_mul hu, stepPot_mul_triangular hj hcell (PositivityTheory.Xgp.per_cell.up_tri _) hdw]`. Expand and normalize the polynomial expressions, which then agree. Introduce `v`. Establish `hz : HasFDerivAt (fun w => PositivityTheory.Xgp.per_cell.low (P w)) (PositivityTheory.Xgp.per_cell.low.comp ((fderiv ℂ ψ (M z0)).comp (fderiv ℂ M z0))) z0` using `PositivityTheory.Xgp.per_cell.low.hasFDerivAt.comp z0 (hψ'.differentiableAt.hasFDerivAt.comp z0 hMan.differentiableAt.hasFDerivAt)`.

Rewrite using `[hz.fderiv]`. Simplify using `only [ContinuousLinearMap.comp_apply]`. Establish `hcomp : ∀ a b, fderiv ℂ M z0 v a b = fderiv ℂ (fun w => M w a b) z0 v`. Introduce `a b`. Establish `h : HasFDerivAt (fun w => M w a b) (((ContinuousLinearMap.proj (R` using `ℂ) (φ := fun _ : Fin N => ℂ) b).comp (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => Fin N → ℂ) a)).comp (fderiv ℂ M z0)) z0 := (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) b).comp (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => Fin N → ℂ) a) …`.

Rewrite using `[h.fderiv]`. Both sides reduce to the same expression. Establish `hent : ∀ a b, fderiv ℂ (fun w => M w a b) z0 v = ∑ c, u⁻¹ a c * fderiv ℂ (fun w => gc w c b) z0 v`. Introduce `a b`. Establish `h : HasFDerivAt (fun w => M w a b) (∑ c, u⁻¹ a c • fderiv ℂ (fun w => gc w c b) z0) z0`.

Use `HasFDerivAt.sum (u := Finset.univ) (fun c _ => ((han c b).differentiableAt.hasFDerivAt).const_mul (u⁻¹ a c))` as an intermediate fact. Use `this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)` and prove the remaining obligations. Simplify using `[M, Matrix.mul_apply, Finset.sum_apply]`. Rewrite using `[h.fderiv]`. Simplify using the standard rewrite rules.

Establish `hy : Matrix.of (fderiv ℂ M z0 v) = u⁻¹ * Matrix.of fun a b => fderiv ℂ (fun w => gc w a b) z0 v`. Use extensionality with `a b`. Rewrite using `[Matrix.of_apply, hcomp, hent, Matrix.mul_apply]`. Both sides reduce to the same expression. Rewrite using `[hMz0]`.

Establish `hL` using `hψd (fderiv ℂ M z0 v)`. Establish `hLL` using `PositivityTheory.Xgp.per_cell.LL_apply b0 (fderiv ℂ ψ (PositivityTheory.Xgp.per_cell.FF bf) (fderiv ℂ M z0 v))`. Rewrite `hLL` using `[hL, hy]`. Rewrite using `[hgu, Matrix.mul_inv_rev, Matrix.mul_assoc, hLL]`. Conclude with `PositivityTheory.Xgp.per_cell.key b0 _ hb0 hb0U (PositivityTheory.Xgp.per_cell.up_tri _) _`.
-/
theorem exists_cell_coords {j : ℕ} (hj : j ≤ N) (gc : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (z0 : Fin e → ℂ) (han : ∀ a b, AnalyticAt ℂ (fun w => gc w a b) z0)
    (hdom : ∀ᶠ w in 𝓝 z0, InFlagDomain N j (gc w)) :
    ∃ z : (Fin e → ℂ) → Pairs N → ℂ, AnalyticAt ℂ z z0 ∧ z z0 = 0 ∧
      (∀ i, PlurRe z0 fun w => stepPot N j i (gc w) - stepPot N j i (cellMat N (z w))) ∧
      ∀ v, fderiv ℂ z z0 v = 0 ↔
        ((gc z0)⁻¹ * Matrix.of fun a b => fderiv ℂ (fun w => gc w a b) z0 v).BlockTriangular id := by
  have hg0 : InFlagDomain N j (gc z0) := hdom.self_of_nhds
  obtain ⟨u, b0, hu, huU, hb0, hb0U, hgu⟩ := exists_unitary_mul_blockTriangular_of_inFlagDomain hj hg0
  have hinvu : u⁻¹ * u = 1 := Matrix.nonsing_inv_mul u huU
  have huinv : u * u⁻¹ = 1 := Matrix.mul_nonsing_inv u huU
  set bf : Fin N → Fin N → ℂ := fun a b => b0 a b with hbf
  set M : (Fin e → ℂ) → (Fin N → Fin N → ℂ) := fun w a b => (u⁻¹ * gc w) a b with hM
  have hMab : ∀ a b, AnalyticAt ℂ (fun w => M w a b) z0 := by
    intro a b
    have h : AnalyticAt ℂ (∑ c, fun w => u⁻¹ a c * gc w c b) z0 :=
      Finset.analyticAt_sum _ fun c _ => analyticAt_const.mul (han c b)
    convert h using 1
    ext w
    simp [M, Matrix.mul_apply, Finset.sum_apply]
  have hMan : AnalyticAt ℂ M z0 := AnalyticAt.pi fun a => AnalyticAt.pi fun b => hMab a b
  have hF0 : PositivityTheory.Xgp.per_cell.FF bf = bf := by
    funext a b
    simp [PositivityTheory.Xgp.per_cell.FF, bf, PositivityTheory.Xgp.per_cell.low_tri hb0, PositivityTheory.Xgp.per_cell.up_of_tri hb0,
      cellMat_zero N]
  have hMz0 : M z0 = PositivityTheory.Xgp.per_cell.FF bf := by
    rw [hF0]
    funext a b
    simp only [M, bf, hgu, ← Matrix.mul_assoc, hinvu, Matrix.one_mul]
  obtain ⟨ψ, hψ, hψ0, hψinv, hψd⟩ := PositivityTheory.Xgp.per_cell.inv_an PositivityTheory.Xgp.per_cell.FF bf
    (PositivityTheory.Xgp.per_cell.LL b0) (PositivityTheory.Xgp.per_cell.an_FF _) (PositivityTheory.Xgp.per_cell.der_FF hb0)
    (PositivityTheory.Xgp.per_cell.inj_LL hb0 hb0U)
  have hψ' : AnalyticAt ℂ ψ (M z0) := hMz0 ▸ hψ
  set P : (Fin e → ℂ) → (Fin N → Fin N → ℂ) := fun w => ψ (M w) with hP
  have hPan : AnalyticAt ℂ P z0 := hψ'.comp hMan
  have hP0 : P z0 = bf := by simp only [P, hMz0, hψ0]
  have hev : ∀ᶠ w in 𝓝 z0, PositivityTheory.Xgp.per_cell.FF (P w) = M w := by
    have ht : Tendsto M (𝓝 z0) (𝓝 (PositivityTheory.Xgp.per_cell.FF bf)) := hMz0 ▸ hMan.continuousAt.tendsto
    exact ht.eventually hψinv
  have hdiag : ∀ a, b0 a a ≠ 0 := by
    intro a
    have h := hb0U.ne_zero
    rw [Matrix.det_of_upperTriangular hb0] at h
    exact Finset.prod_ne_zero_iff.1 h a (Finset.mem_univ a)
  have hB0 : Matrix.of (PositivityTheory.Xgp.per_cell.up (P z0)) = b0 := by
    rw [hP0, PositivityTheory.Xgp.per_cell.up_of_tri hb0]
    rfl
  refine ⟨fun w => PositivityTheory.Xgp.per_cell.low (P w), ?_, ?_, ?_, ?_⟩
  · exact (PositivityTheory.Xgp.per_cell.low.analyticAt _).comp hPan
  · simp only [hP0, bf]
    exact PositivityTheory.Xgp.per_cell.low_tri hb0
  · intro i
    have hBan : ∀ a, AnalyticAt ℂ (fun w => Matrix.of (PositivityTheory.Xgp.per_cell.up (P w)) a a) z0 := by
      intro a
      exact ((((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) a).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => Fin N → ℂ) a)).comp
          PositivityTheory.Xgp.per_cell.up).analyticAt _).comp hPan
    have hB0ne : ∀ a, Matrix.of (PositivityTheory.Xgp.per_cell.up (P z0)) a a ≠ 0 := by
      intro a
      rw [hB0]
      exact hdiag a
    have hdetB : ∀ᶠ w in 𝓝 z0, IsUnit (Matrix.of (PositivityTheory.Xgp.per_cell.up (P w))).det := by
      have hc : ContinuousAt (fun w => (Matrix.of (PositivityTheory.Xgp.per_cell.up (P w))).det) z0 :=
        (Continuous.matrix_det continuous_id).continuousAt.comp
          (PositivityTheory.Xgp.per_cell.up.continuous.continuousAt.comp hPan.continuousAt)
      have h0 : (Matrix.of (PositivityTheory.Xgp.per_cell.up (P z0))).det ≠ 0 := by
        rw [hB0]
        exact hb0U.ne_zero
      filter_upwards [hc.eventually_ne h0] with w hw
      exact isUnit_iff_ne_zero.2 hw
    have hfac : ∀ᶠ w in 𝓝 z0, gc w = u * (cellMat N (PositivityTheory.Xgp.per_cell.low (P w)) *
        Matrix.of (PositivityTheory.Xgp.per_cell.up (P w))) := by
      filter_upwards [hev] with w hw
      have hw' : cellMat N (PositivityTheory.Xgp.per_cell.low (P w)) * Matrix.of (PositivityTheory.Xgp.per_cell.up (P w)) =
          u⁻¹ * gc w := by
        ext a b
        exact congrFun (congrFun hw a) b
      rw [hw', ← Matrix.mul_assoc, huinv, Matrix.one_mul]
    refine PlurRe.congr (plurRe_stepCorr (b := fun w => Matrix.of (PositivityTheory.Xgp.per_cell.up (P w)))
      hBan hB0ne j i) ?_
    filter_upwards [hfac, hdetB, hdom] with w hw hdw hdom'
    have hcell : InFlagDomain N j (cellMat N (PositivityTheory.Xgp.per_cell.low (P w))) := by
      haveI := Matrix.invertibleOfIsUnitDet _ hdw
      have := inFlagDomain_inv_mul_mul hu huU hdom' (c := (Matrix.of (PositivityTheory.Xgp.per_cell.up (P w)))⁻¹)
        (Matrix.blockTriangular_inv_of_blockTriangular (PositivityTheory.Xgp.per_cell.up_tri _))
        (Matrix.isUnit_nonsing_inv_det _ hdw)
      convert this using 1
      rw [hw, ← Matrix.mul_assoc, hinvu, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hdw, Matrix.mul_one]
    rw [hw, stepPot_unitary_mul hu, stepPot_mul_triangular hj hcell (PositivityTheory.Xgp.per_cell.up_tri _) hdw]
    ring
  · intro v
    have hz : HasFDerivAt (fun w => PositivityTheory.Xgp.per_cell.low (P w))
        (PositivityTheory.Xgp.per_cell.low.comp ((fderiv ℂ ψ (M z0)).comp (fderiv ℂ M z0))) z0 :=
      PositivityTheory.Xgp.per_cell.low.hasFDerivAt.comp z0
        (hψ'.differentiableAt.hasFDerivAt.comp z0 hMan.differentiableAt.hasFDerivAt)
    rw [hz.fderiv]
    simp only [ContinuousLinearMap.comp_apply]
    have hcomp : ∀ a b, fderiv ℂ M z0 v a b = fderiv ℂ (fun w => M w a b) z0 v := by
      intro a b
      have h : HasFDerivAt (fun w => M w a b)
          (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) b).comp
            (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => Fin N → ℂ) a)).comp
              (fderiv ℂ M z0)) z0 :=
        (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) b).comp
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => Fin N → ℂ) a)).hasFDerivAt).comp z0
            hMan.differentiableAt.hasFDerivAt
      rw [h.fderiv]
      rfl
    have hent : ∀ a b, fderiv ℂ (fun w => M w a b) z0 v =
        ∑ c, u⁻¹ a c * fderiv ℂ (fun w => gc w c b) z0 v := by
      intro a b
      have h : HasFDerivAt (fun w => M w a b) (∑ c, u⁻¹ a c • fderiv ℂ (fun w => gc w c b) z0) z0 := by
        have := HasFDerivAt.sum (u := Finset.univ)
          (fun c _ => ((han c b).differentiableAt.hasFDerivAt).const_mul (u⁻¹ a c))
        refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
        simp [M, Matrix.mul_apply, Finset.sum_apply]
      rw [h.fderiv]
      simp
    have hy : Matrix.of (fderiv ℂ M z0 v) =
        u⁻¹ * Matrix.of fun a b => fderiv ℂ (fun w => gc w a b) z0 v := by
      ext a b
      rw [Matrix.of_apply, hcomp, hent, Matrix.mul_apply]
      rfl
    rw [hMz0]
    have hL := hψd (fderiv ℂ M z0 v)
    have hLL := PositivityTheory.Xgp.per_cell.LL_apply b0 (fderiv ℂ ψ (PositivityTheory.Xgp.per_cell.FF bf) (fderiv ℂ M z0 v))
    rw [hL, hy] at hLL
    rw [hgu, Matrix.mul_inv_rev, Matrix.mul_assoc, hLL]
    exact PositivityTheory.Xgp.per_cell.key b0 _ hb0 hb0U (PositivityTheory.Xgp.per_cell.up_tri _) _

def rel (N j : ℕ) (a : Fin N) : ℕ := if (a : ℕ) < N - j then j + a else a - (N - j)

/- English proof (translation)
Set `e : Fin k ≃ {a : Fin N // (a : ℕ) < k}` to `{ toFun := fun b => ⟨Fin.castLE hk b, b.2⟩ invFun := fun a => ⟨a.1.val, a.2⟩ left_inv := fun b => rfl right_inv := fun a => rfl }`. Establish `hdet : ((gramOf hd (cellMat N u)).submatrix (Fin.castLE hk) (Fin.castLE hk)).det = (gramHead hd k (cellMat N u)).det`. Rewrite using `[gramHead, ← Matrix.det_submatrix_equiv_self e]`. Both sides reduce to the same expression. Establish `e1` using `congrFun (logDetFlag_eq N hd k hk) u`.

Simplify using `only [logDetFlag] at e1`. Rewrite `e1` using `[Real.log_abs]`. Rewrite using `[gramLog, ← hdet, ← e1]`. Both sides reduce to the same expression.
-/
private theorem gramLog_cellMat_eq_half_log_detGram (hd : Fin N → ℝ) (k : ℕ) (hk : k ≤ N) (u : Pairs N → ℂ) :
    gramLog hd k (cellMat N u) = 1 / 2 * Real.log (detGram N hd k hk u) := by
  let e : Fin k ≃ {a : Fin N // (a : ℕ) < k} :=
    { toFun := fun b => ⟨Fin.castLE hk b, b.2⟩
      invFun := fun a => ⟨a.1.val, a.2⟩
      left_inv := fun b => rfl
      right_inv := fun a => rfl }
  have hdet : ((gramOf hd (cellMat N u)).submatrix (Fin.castLE hk) (Fin.castLE hk)).det =
      (gramHead hd k (cellMat N u)).det := by
    rw [gramHead, ← Matrix.det_submatrix_equiv_self e]
    rfl
  have e1 := congrFun (logDetFlag_eq N hd k hk) u
  simp only [logDetFlag] at e1
  rw [Real.log_abs] at e1
  rw [gramLog, ← hdet, ← e1]
  rfl

/- English proof (translation)
Establish `hd : ∀ a : Fin N, sigForm N j a ≠ 0`. Introduce `a`. Unfold `sigForm`. Apply the tactic sequence `split_ifs <;> norm_num`. Take `⟨hcd, h0, hder⟩` from `detGram_deriv N (sigForm N j) k hk`.

Establish `hP : (∏ a : Fin k, sigForm N j (Fin.castLE hk a)) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun a _ => hd _`. Establish `hne : detGram N (sigForm N j) k hk 0 ≠ 0`. Rewrite using `[h0]`. Conclude with `hP`. Use `⟨contDiffAt_const.mul (hcd.contDiffAt.log hne), fun w => ?_⟩` and prove the remaining obligations.

Establish `h1` using `leviHalfLogAbs (detGram N (sigForm N j) k hk) 0 hcd.contDiffAt hne hder w`. Simplify using `only [Real.log_abs] at h1`. Rewrite using `[h1, detGram_levi N (sigForm N j) hd k hk w, h0, mul_comm (2 : ℝ), mul_div_mul_left _ _ hP]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem levi_half_log_detGram_at_zero (j k : ℕ) (hk : k ≤ N) :
    ContDiffAt ℝ 2 (fun u : Pairs N → ℂ => 1 / 2 * Real.log (detGram N (sigForm N j) k hk u)) 0 ∧
    ∀ w, levi (fun u : Pairs N → ℂ => 1 / 2 * Real.log (detGram N (sigForm N j) k hk u)) 0 w =
      1 / 2 * ∑ p : Pairs N, if (p.1.1 : ℕ) < k ∧ k ≤ (p.1.2 : ℕ) then
        sigForm N j p.1.2 / sigForm N j p.1.1 * ‖w p‖ ^ 2 else 0 := by
  have hd : ∀ a : Fin N, sigForm N j a ≠ 0 := by
    intro a
    unfold sigForm
    split_ifs <;> norm_num
  obtain ⟨hcd, h0, hder⟩ := detGram_deriv N (sigForm N j) k hk
  have hP : (∏ a : Fin k, sigForm N j (Fin.castLE hk a)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun a _ => hd _
  have hne : detGram N (sigForm N j) k hk 0 ≠ 0 := by
    rw [h0]
    exact hP
  refine ⟨contDiffAt_const.mul (hcd.contDiffAt.log hne), fun w => ?_⟩
  have h1 := leviHalfLogAbs (detGram N (sigForm N j) k hk) 0 hcd.contDiffAt hne hder w
  simp only [Real.log_abs] at h1
  rw [h1, detGram_levi N (sigForm N j) hd k hk w, h0, mul_comm (2 : ℝ), mul_div_mul_left _ _ hP]
  ring

/- English proof (translation)
Establish `hi` using `i.isLt`. Distinguish the cases in `hc : (i : ℕ) + 1 ≤ j`. Establish `k1 : N - j + ((i : ℕ) + 1) ≤ N` using `by omega`. Establish `k2 : N - j ≤ N` using `Nat.sub_le N j`. Establish `eqS : (fun u : Pairs N → ℂ => stepPot N j i (cellMat N u)) = fun u => 1 / 2 * Real.log (detGram N (sigForm N j) _ k1 u) + (-1) * (1 / 2 * Real.log (detGram N (sigForm N j) _ k2 u))`.

Use function extensionality and compare the values at `u`. Simplify using `only [stepPot, hc, ↓reduceIte, gramLog_cellMat_eq_half_log_detGram _ _ k1, gramLog_cellMat_eq_half_log_detGram _ _ k2]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[eqS]`. Take `⟨c1, l1⟩` from `levi_half_log_detGram_at_zero (N := N) j _ k1`.

Take `⟨c2, l2⟩` from `levi_half_log_detGram_at_zero (N := N) j _ k2`. Use `⟨c1.add (contDiffAt_const.mul c2), fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[levi_add_smul (-1) c1 c2 w, l1 w, l2 w]`. Simplify using `only [Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations.

Take `⟨⟨a, b⟩, hab⟩` from `p`. Establish `hab' : (a : ℕ) < b` using `hab`. Establish `ha` using `a.isLt`. Establish `hb` using `b.isLt`. Simplify using `only`.

Simplify using `only [sigForm, rel]`. Apply the tactic sequence `split_ifs <;> first | (exfalso; omega) | ring | norm_num`. Establish `k1 : N ≤ N` using `le_refl N`. Establish `k2 : N - j ≤ N` using `Nat.sub_le N j`. Establish `k3 : (i : ℕ) + 1 - j ≤ N` using `by omega`.

Establish `eqS : (fun u : Pairs N → ℂ => stepPot N j i (cellMat N u)) = fun u => (1 / 2 * Real.log (detGram N (sigForm N j) _ k1 u) + (-1) * (1 / 2 * Real.log (detGram N (sigForm N j) _ k2 u))) + 1 * (1 / 2 * Real.log (detGram N (sigForm N j) _ k3 u))`. Use function extensionality and compare the values at `u`. Simplify using `only [stepPot, hc, ↓reduceIte, gramLog_cellMat_eq_half_log_detGram _ _ k1, gramLog_cellMat_eq_half_log_detGram _ _ k2, gramLog_cellMat_eq_half_log_detGram _ _ k3]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[eqS]`.

Take `⟨c1, l1⟩` from `levi_half_log_detGram_at_zero (N := N) j _ k1`. Take `⟨c2, l2⟩` from `levi_half_log_detGram_at_zero (N := N) j _ k2`. Take `⟨c3, l3⟩` from `levi_half_log_detGram_at_zero (N := N) j _ k3`. Establish `c12 : ContDiffAt ℝ 2 (fun u : Pairs N → ℂ => 1 / 2 * Real.log (detGram N (sigForm N j) _ k1 u) + (-1) * (1 / 2 * Real.log (detGram N (sigForm N j) _ k2 u))) 0` using `c1.add (contDiffAt_const.mul c2)`. Use `⟨c12.add (contDiffAt_const.mul c3), fun w => ?_⟩` and prove the remaining obligations.

Rewrite using `[levi_add_smul 1 c12 c3 w, levi_add_smul (-1) c1 c2 w, l1 w, l2 w, l3 w]`. Simplify using `only [Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Take `⟨⟨a, b⟩, hab⟩` from `p`. Establish `hab' : (a : ℕ) < b` using `hab`.

Establish `ha` using `a.isLt`. Establish `hb` using `b.isLt`. Simplify using `only`. Simplify using `only [sigForm, rel]`. Apply the tactic sequence `split_ifs <;> first | (exfalso; omega) | ring | norm_num`.
-/
private theorem levi_cellMat_potential_at_zero_eq_sum {j : ℕ} (hj : j ≤ N) (i : Fin N) :
    ContDiffAt ℝ 2 (fun u : Pairs N → ℂ => stepPot N j i (cellMat N u)) 0 ∧
    ∀ w : Pairs N → ℂ, levi (fun u : Pairs N → ℂ => stepPot N j i (cellMat N u)) 0 w =
      ∑ p : Pairs N, if min (rel N j p.1.1) (rel N j p.1.2) ≤ (i : ℕ) ∧
        (i : ℕ) < max (rel N j p.1.1) (rel N j p.1.2) then (1 / 2 : ℝ) * ‖w p‖ ^ 2 else 0 := by
  have hi := i.isLt
  by_cases hc : (i : ℕ) + 1 ≤ j
  · have k1 : N - j + ((i : ℕ) + 1) ≤ N := by omega
    have k2 : N - j ≤ N := Nat.sub_le N j
    have eqS : (fun u : Pairs N → ℂ => stepPot N j i (cellMat N u)) = fun u =>
        1 / 2 * Real.log (detGram N (sigForm N j) _ k1 u) +
          (-1) * (1 / 2 * Real.log (detGram N (sigForm N j) _ k2 u)) := by
      funext u
      simp only [stepPot, hc, ↓reduceIte, gramLog_cellMat_eq_half_log_detGram _ _ k1, gramLog_cellMat_eq_half_log_detGram _ _ k2]
      ring
    rw [eqS]
    obtain ⟨c1, l1⟩ := levi_half_log_detGram_at_zero (N := N) j _ k1
    obtain ⟨c2, l2⟩ := levi_half_log_detGram_at_zero (N := N) j _ k2
    refine ⟨c1.add (contDiffAt_const.mul c2), fun w => ?_⟩
    rw [levi_add_smul (-1) c1 c2 w, l1 w, l2 w]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    obtain ⟨⟨a, b⟩, hab⟩ := p
    have hab' : (a : ℕ) < b := hab
    have ha := a.isLt
    have hb := b.isLt
    dsimp only
    simp only [sigForm, rel]
    split_ifs <;> first | (exfalso; omega) | ring | norm_num
  · have k1 : N ≤ N := le_refl N
    have k2 : N - j ≤ N := Nat.sub_le N j
    have k3 : (i : ℕ) + 1 - j ≤ N := by omega
    have eqS : (fun u : Pairs N → ℂ => stepPot N j i (cellMat N u)) = fun u =>
        (1 / 2 * Real.log (detGram N (sigForm N j) _ k1 u) +
          (-1) * (1 / 2 * Real.log (detGram N (sigForm N j) _ k2 u))) +
          1 * (1 / 2 * Real.log (detGram N (sigForm N j) _ k3 u)) := by
      funext u
      simp only [stepPot, hc, ↓reduceIte, gramLog_cellMat_eq_half_log_detGram _ _ k1, gramLog_cellMat_eq_half_log_detGram _ _ k2,
        gramLog_cellMat_eq_half_log_detGram _ _ k3]
      ring
    rw [eqS]
    obtain ⟨c1, l1⟩ := levi_half_log_detGram_at_zero (N := N) j _ k1
    obtain ⟨c2, l2⟩ := levi_half_log_detGram_at_zero (N := N) j _ k2
    obtain ⟨c3, l3⟩ := levi_half_log_detGram_at_zero (N := N) j _ k3
    have c12 : ContDiffAt ℝ 2 (fun u : Pairs N → ℂ => 1 / 2 * Real.log (detGram N (sigForm N j) _ k1 u) +
        (-1) * (1 / 2 * Real.log (detGram N (sigForm N j) _ k2 u))) 0 :=
      c1.add (contDiffAt_const.mul c2)
    refine ⟨c12.add (contDiffAt_const.mul c3), fun w => ?_⟩
    rw [levi_add_smul 1 c12 c3 w, levi_add_smul (-1) c1 c2 w, l1 w, l2 w, l3 w]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    obtain ⟨⟨a, b⟩, hab⟩ := p
    have hab' : (a : ℕ) < b := hab
    have ha := a.isLt
    have hb := b.isLt
    dsimp only
    simp only [sigForm, rel]
    split_ifs <;> first | (exfalso; omega) | ring | norm_num

/- English proof (translation)
Take `⟨H, hH, hHe⟩` from `hf`. Take `⟨hS2, hSl⟩` from `levi_cellMat_potential_at_zero_eq_sum (N := N) hj i`. Establish `hS2' : ContDiffAt ℝ 2 (fun u : Pairs N → ℂ => stepPot N j i (cellMat N u)) (z z0)`. Rewrite using `[hz0]`. Conclude with `hS2`.

Establish `hz2 : ContDiffAt ℝ 2 (fun w => stepPot N j i (cellMat N (z w))) z0` using `hS2'.comp z0 (hz.contDiffAt.restrict_scalars ℝ)`. Establish `hH2 : ContDiffAt ℝ 2 (fun w => (H w).re) z0` using `Complex.reCLM.contDiff.contDiffAt.comp z0 (hH.contDiffAt.restrict_scalars ℝ)`. Establish `hfe : f =ᶠ[𝓝 z0] fun w => stepPot N j i (cellMat N (z w)) + 1 * (H w).re` using `by filter_upwards [hHe] with w hw`. Combine the linear relations using `[show f w - stepPot N j i (cellMat N (z w)) = (H w).re from hw]`. Use `⟨(hz2.add (contDiffAt_const.mul hH2)).congr_of_eventuallyEq hfe, fun v => ?_⟩` and prove the remaining obligations.

Rewrite using `[levi_congr hfe v, levi_add_smul 1 hz2 hH2 v, levi_re_analytic hH v, mul_zero, add_zero]`. Rewrite using `[show (fun w => stepPot N j i (cellMat N (z w))) = (fun u : Pairs N → ℂ => stepPot N j i (cellMat N u)) ∘ z from rfl]`. Rewrite using `[levi_comp v hz hS2', hz0, hSl]`.
-/
theorem levi_of_cell {j : ℕ} (hj : j ≤ N) (i : Fin N) {z0 : Fin e → ℂ} {f : (Fin e → ℂ) → ℝ}
    {z : (Fin e → ℂ) → Pairs N → ℂ} (hz : AnalyticAt ℂ z z0) (hz0 : z z0 = 0)
    (hf : PlurRe z0 fun w => f w - stepPot N j i (cellMat N (z w))) :
    ContDiffAt ℝ 2 f z0 ∧ ∀ v, levi f z0 v = ∑ p : Pairs N,
      if min (rel N j p.1.1) (rel N j p.1.2) ≤ (i : ℕ) ∧ (i : ℕ) < max (rel N j p.1.1) (rel N j p.1.2)
      then (1 / 2 : ℝ) * ‖fderiv ℂ z z0 v p‖ ^ 2 else 0 := by
  obtain ⟨H, hH, hHe⟩ := hf
  obtain ⟨hS2, hSl⟩ := levi_cellMat_potential_at_zero_eq_sum (N := N) hj i
  have hS2' : ContDiffAt ℝ 2 (fun u : Pairs N → ℂ => stepPot N j i (cellMat N u)) (z z0) := by
    rw [hz0]
    exact hS2
  have hz2 : ContDiffAt ℝ 2 (fun w => stepPot N j i (cellMat N (z w))) z0 :=
    hS2'.comp z0 (hz.contDiffAt.restrict_scalars ℝ)
  have hH2 : ContDiffAt ℝ 2 (fun w => (H w).re) z0 :=
    Complex.reCLM.contDiff.contDiffAt.comp z0 (hH.contDiffAt.restrict_scalars ℝ)
  have hfe : f =ᶠ[𝓝 z0] fun w => stepPot N j i (cellMat N (z w)) + 1 * (H w).re := by
    filter_upwards [hHe] with w hw
    linarith [show f w - stepPot N j i (cellMat N (z w)) = (H w).re from hw]
  refine ⟨(hz2.add (contDiffAt_const.mul hH2)).congr_of_eventuallyEq hfe, fun v => ?_⟩
  rw [levi_congr hfe v, levi_add_smul 1 hz2 hH2 v, levi_re_analytic hH v, mul_zero, add_zero]
  rw [show (fun w => stepPot N j i (cellMat N (z w))) =
    (fun u : Pairs N → ℂ => stepPot N j i (cellMat N u)) ∘ z from rfl]
  rw [levi_comp v hz hS2', hz0, hSl]

/- English proof (translation)
Use `a.2` as an intermediate fact. Unfold `rel`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem rel_lt {j : ℕ} (hj : j ≤ N) (a : Fin N) : rel N j a < N := by
  have := a.2
  unfold rel
  split_ifs <;> omega

def relF {j : ℕ} (hj : j ≤ N) (a : Fin N) : Fin N := ⟨rel N j a, rel_lt hj a⟩

/- English proof (translation)
Introduce `a b h`. Establish `h'` using `congrArg Fin.val h`. Simplify using `only [relF] at h'`. Unfold `rel at h'`. Apply `Fin.ext` to reduce the goal to its premises.

Use `a.isLt` as an intermediate fact. Use `b.isLt` as an intermediate fact. Apply the tactic sequence `split_ifs at h' <;> omega`.
-/
theorem relF_injective {j : ℕ} (hj : j ≤ N) : Function.Injective (relF (N := N) hj) := by
  intro a b h
  have h' := congrArg Fin.val h
  simp only [relF] at h'
  unfold rel at h'
  apply Fin.ext
  have := a.isLt
  have := b.isLt
  split_ifs at h' <;> omega

def pairMap (σ : Fin N → Fin N) (hσ : Function.Injective σ) (p : Pairs N) : Pairs N :=
  ⟨(min (σ p.1.1) (σ p.1.2), max (σ p.1.1) (σ p.1.2)), min_lt_max.2 (hσ.ne p.2.ne)⟩

/- English proof (translation)
Introduce and unpack `⟨⟨a, b⟩, hab⟩ ⟨⟨c, d⟩, hcd⟩ h`. Simplify using `only [pairMap, Subtype.mk.injEq, Prod.mk.injEq] at h`. Take `⟨h1, h2⟩` from `h`. Simplify using `only at hab hcd`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply the tactic sequence `rcases le_total (σ a) (σ b) with h3 | h3 <;> rcases le_total (σ c) (σ d) with h4 | h4`. Use `all_goals`. Simplify using `only [min_eq_left h3, max_eq_right h3, min_eq_right h3, max_eq_left h3, min_eq_left h4, max_eq_right h4, min_eq_right h4, max_eq_left h4] at h1 h2`. Establish `e1` using `hσ h1`. Establish `e2` using `hσ h2`.

Substitute `e1 e2` using the available equality. Use `first`. Consider the case `rfl`. Consider the case `exact absurd (hab.trans hcd) (lt_irrefl _)`.
-/
theorem pairMap_injective (σ : Fin N → Fin N) (hσ : Function.Injective σ) :
    Function.Injective (pairMap σ hσ) := by
  rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨c, d⟩, hcd⟩ h
  simp only [pairMap, Subtype.mk.injEq, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  dsimp only at hab hcd
  apply Subtype.ext
  rcases le_total (σ a) (σ b) with h3 | h3 <;> rcases le_total (σ c) (σ d) with h4 | h4
  all_goals
    simp only [min_eq_left h3, max_eq_right h3, min_eq_right h3, max_eq_left h3,
      min_eq_left h4, max_eq_right h4, min_eq_right h4, max_eq_left h4] at h1 h2
    have e1 := hσ h1
    have e2 := hσ h2
    subst e1 e2
    first
      | rfl
      | exact absurd (hab.trans hcd) (lt_irrefl _)

def pairEquiv {j : ℕ} (hj : j ≤ N) : Pairs N ≃ Pairs N :=
  Equiv.ofBijective (pairMap (relF hj) (relF_injective hj))
    (pairMap_injective _ _).bijective_of_finite

/- English proof (translation)
Simplify using `only [pairEquiv, Equiv.ofBijective_apply, pairMap, min_le_iff, Fin.le_def, relF]`.
-/
theorem pairEquiv_fst_le {j : ℕ} (hj : j ≤ N) (p : Pairs N) (i : Fin N) :
    (pairEquiv hj p).1.1 ≤ i ↔ min (rel N j p.1.1) (rel N j p.1.2) ≤ (i : ℕ) := by
  simp only [pairEquiv, Equiv.ofBijective_apply, pairMap, min_le_iff, Fin.le_def, relF]

/- English proof (translation)
Simplify using `only [pairEquiv, Equiv.ofBijective_apply, pairMap, lt_max_iff, Fin.lt_def, relF]`.
-/
theorem pairEquiv_lt_snd {j : ℕ} (hj : j ≤ N) (p : Pairs N) (i : Fin N) :
    i < (pairEquiv hj p).1.2 ↔ (i : ℕ) < max (rel N j p.1.1) (rel N j p.1.2) := by
  simp only [pairEquiv, Equiv.ofBijective_apply, pairMap, lt_max_iff, Fin.lt_def, relF]

end PerDiag

open PerDiag in

/- English proof (translation)
Introduce `e X _ A Ψ _ _ N j hj pot x V g hP k hx`. Take `⟨hVo, hxV, hhol, hdom, hpot⟩` from `hP`. Establish `hz0t : A.chart k x ∈ (A.chart k).target` using `(A.chart k).map_source hx`. Establish `hsx : (A.chart k).symm (A.chart k x) = x` using `(A.chart k).left_inv hx`. Establish `hmem : A.chart k x ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' V` using `⟨hz0t, by simp only [Set.mem_preimage, hsx]; exact hxV⟩`.

Establish `hev : ∀ᶠ w in 𝓝 (A.chart k x), (A.chart k).symm w ∈ V`. Establish `hc : ContinuousAt (A.chart k).symm (A.chart k x)` using `(A.chart k).continuousAt_symm hz0t`. Conclude with `hc.preimage_mem_nhds (by rw [hsx]; exact hVo.mem_nhds hxV)`. Establish `hcell : ∀ τ : Ψ, ∃ z : (Fin e → ℂ) → Pairs N → ℂ, AnalyticAt ℂ z (A.chart k x) ∧ z (A.chart k x) = 0 ∧ (∀ i, PlurRe (A.chart k x) fun w => stepPot N j i (g τ ((A.chart k).symm w)) - stepPot N j i (cellMat N (z w))) ∧ ∀ v, fderiv ℂ z (A.chart k x) v = 0 ↔ ((g τ ((A.chart k).symm ( …`. Introduce `τ`.

Use `exists_cell_coords hj (fun w => g τ ((A.chart k).symm w)) (A.chart k x) (fun a b => ?_) ?_` and prove the remaining obligations. Conclude with `hhol τ a b k (A.chart k x) hmem`. Use `filter_upwards [hev] with w hw`. Conclude with `hdom τ _ hw`. Use `choose zc hzan hz0' hzpl hzker using hcell`.

Set `Lm : (Fin e → ℂ) →ₗ[ℂ] (Ψ × Pairs N → ℂ)` to `{ toFun := fun v tq => fderiv ℂ (zc tq.1) (A.chart k x) v ((pairEquiv hj).symm tq.2) map_add' := by`. Introduce `v w`. Use extensionality with `tq`. Simplify using the standard rewrite rules. Use the proof step `map_smul' := by`.

Introduce `c v`. Use extensionality with `tq`. Simplify using `}`. Establish `hf : ∀ p : Ψ × Fin N, PlurRe (A.chart k x) fun w => ((pot p).φ x ∘ (A.chart k).symm) w - stepPot N j p.2 (cellMat N (zc p.1 w))`. Introduce `p`.

Take `⟨G, hG, hGe⟩` from `hpot p`. Establish `h1 : PlurRe (A.chart k x) fun w => (G ((A.chart k).symm w)).re` using `⟨fun w => G ((A.chart k).symm w), hG k (A.chart k x) hmem, Filter.Eventually.of_forall fun _ => rfl⟩`. Use `(h1.add (hzpl p.1 p.2)).congr ?_` and prove the remaining obligations. Use `filter_upwards [hev] with w hw`. Simplify using `only [Function.comp_apply, hGe _ hw]`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨Lm, fun p => (levi_of_cell hj p.2 (hzan p.1) (hz0' p.1) (hf p)).1, ?_, ?_⟩` and prove the remaining obligations. Introduce `p v`. Rewrite using `[(levi_of_cell hj p.2 (hzan p.1) (hz0' p.1) (hf p)).2 v]`. Use `Eq.trans ?_ ((pairEquiv hj).sum_comp _)` and prove the remaining obligations.

Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Simplify using `only [Lm, LinearMap.coe_mk, AddHom.coe_mk, Equiv.symm_apply_apply, pairEquiv_fst_le, pairEquiv_lt_snd]`. Introduce `himm`. Use `(injective_iff_map_eq_zero Lm).2 fun v hv => ?_` and prove the remaining obligations. Use `himm k hx v fun τ => ?_` and prove the remaining obligations.

Establish `hz : fderiv ℂ (zc τ) (A.chart k x) v = 0`. Use extensionality with `q`. Use `congrFun hv (τ, pairEquiv hj q)` as an intermediate fact. Simplify `this` using `[Lm]`. Use `(hzker τ v).1 hz` as an intermediate fact.

Rewrite `this` using `[hsx]`. Then use the resulting hypothesis.
-/
theorem levi_diagonal_of_isPeriodChart :
    ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ), j ≤ N → ∀ (pot : Ψ × Fin N → LocPot X) (x : X) (V : Set X) (g : Ψ → X → Matrix (Fin N) (Fin N) ℂ), IsPeriodChart A j pot x V g → ∀ k, x ∈ (A.chart k).source → ∃ Lm : (Fin e → ℂ) →ₗ[ℂ] (Ψ × Pairs N → ℂ), (∀ p, ContDiffAt ℝ 2 ((pot p).φ x ∘ (A.chart k).symm) (A.chart k x)) ∧ (∀ (p : Ψ × Fin N) v, levi ((pot p).φ x ∘ (A.chart k).symm) (A.chart k x) v = ∑ q : Pairs N, if q.1.1 ≤ p.2 ∧ p.2 < q.1.2 then (1 / 2 : ℝ) * ‖Lm v (p.1, q)‖ ^ 2 else 0) ∧ (IsFlagImmersionAt A g x → Function.Injective Lm) := by
  intro e X _ A Ψ _ _ N j hj pot x V g hP k hx
  obtain ⟨hVo, hxV, hhol, hdom, hpot⟩ := hP
  have hz0t : A.chart k x ∈ (A.chart k).target := (A.chart k).map_source hx
  have hsx : (A.chart k).symm (A.chart k x) = x := (A.chart k).left_inv hx
  have hmem : A.chart k x ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' V :=
    ⟨hz0t, by simp only [Set.mem_preimage, hsx]; exact hxV⟩
  have hev : ∀ᶠ w in 𝓝 (A.chart k x), (A.chart k).symm w ∈ V := by
    have hc : ContinuousAt (A.chart k).symm (A.chart k x) := (A.chart k).continuousAt_symm hz0t
    exact hc.preimage_mem_nhds (by rw [hsx]; exact hVo.mem_nhds hxV)
  have hcell : ∀ τ : Ψ, ∃ z : (Fin e → ℂ) → Pairs N → ℂ, AnalyticAt ℂ z (A.chart k x) ∧
      z (A.chart k x) = 0 ∧
      (∀ i, PlurRe (A.chart k x) fun w =>
        stepPot N j i (g τ ((A.chart k).symm w)) - stepPot N j i (cellMat N (z w))) ∧
      ∀ v, fderiv ℂ z (A.chart k x) v = 0 ↔
        ((g τ ((A.chart k).symm (A.chart k x)))⁻¹ * Matrix.of fun a b =>
          fderiv ℂ (fun w => g τ ((A.chart k).symm w) a b) (A.chart k x) v).BlockTriangular id := by
    intro τ
    refine exists_cell_coords hj (fun w => g τ ((A.chart k).symm w)) (A.chart k x) (fun a b => ?_) ?_
    · exact hhol τ a b k (A.chart k x) hmem
    · filter_upwards [hev] with w hw
      exact hdom τ _ hw
  choose zc hzan hz0' hzpl hzker using hcell
  let Lm : (Fin e → ℂ) →ₗ[ℂ] (Ψ × Pairs N → ℂ) :=
    { toFun := fun v tq => fderiv ℂ (zc tq.1) (A.chart k x) v ((pairEquiv hj).symm tq.2)
      map_add' := by
        intro v w
        ext tq
        simp
      map_smul' := by
        intro c v
        ext tq
        simp }
  have hf : ∀ p : Ψ × Fin N, PlurRe (A.chart k x) fun w =>
      ((pot p).φ x ∘ (A.chart k).symm) w - stepPot N j p.2 (cellMat N (zc p.1 w)) := by
    intro p
    obtain ⟨G, hG, hGe⟩ := hpot p
    have h1 : PlurRe (A.chart k x) fun w => (G ((A.chart k).symm w)).re :=
      ⟨fun w => G ((A.chart k).symm w), hG k (A.chart k x) hmem, Filter.Eventually.of_forall fun _ => rfl⟩
    refine (h1.add (hzpl p.1 p.2)).congr ?_
    filter_upwards [hev] with w hw
    simp only [Function.comp_apply, hGe _ hw]
    ring
  refine ⟨Lm, fun p => (levi_of_cell hj p.2 (hzan p.1) (hz0' p.1) (hf p)).1, ?_, ?_⟩
  · intro p v
    rw [(levi_of_cell hj p.2 (hzan p.1) (hz0' p.1) (hf p)).2 v]
    refine Eq.trans ?_ ((pairEquiv hj).sum_comp _)
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [Lm, LinearMap.coe_mk, AddHom.coe_mk, Equiv.symm_apply_apply, pairEquiv_fst_le,
      pairEquiv_lt_snd]
  · intro himm
    refine (injective_iff_map_eq_zero Lm).2 fun v hv => ?_
    refine himm k hx v fun τ => ?_
    have hz : fderiv ℂ (zc τ) (A.chart k x) v = 0 := by
      ext q
      have := congrFun hv (τ, pairEquiv hj q)
      simpa [Lm] using this
    have := (hzker τ v).1 hz
    rwa [hsx] at this

end PositivityTheory.Xgp.per_diag
