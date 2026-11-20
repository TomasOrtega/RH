import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColJoinColLColR
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold.Summand

variable {D : D7}

/- English proof (translation)
Simplify using `only [Matrix.trace, Matrix.diag_apply]`. Rewrite using `[Fin.sum_univ_add]`. Apply the tactic sequence `congr 1 <;> refine Finset.sum_congr rfl fun j _ => ?_ <;>`. Simplify using `[GlobalTheory.StdUnn.inner, adj, Matrix.mul_apply]`.
-/
theorem trace_inner_join (V : HSp D) {r s : ℕ} (x₁ y₁ : Mx D V.rank r) (x₂ y₂ : Mx D V.rank s) :
    Matrix.trace (GlobalTheory.StdUnn.inner V (colJoin x₁ x₂) (colJoin y₁ y₂)) =
      Matrix.trace (GlobalTheory.StdUnn.inner V x₁ y₁) + Matrix.trace (GlobalTheory.StdUnn.inner V x₂ y₂) := by
  simp only [Matrix.trace, Matrix.diag_apply]
  rw [Fin.sum_univ_add]
  congr 1 <;> refine Finset.sum_congr rfl fun j _ => ?_ <;>
    simp [GlobalTheory.StdUnn.inner, adj, Matrix.mul_apply]

/- English proof (translation)
Establish `e : GlobalTheory.StdUnn.inner V (HMul.hMul U A) (HMul.hMul W A') = HMul.hMul (adj A) (HMul.hMul (GlobalTheory.StdUnn.inner V U W) A')`. Simplify using `only [GlobalTheory.StdUnn.inner, adj_mul, Matrix.mul_assoc]`. Rewrite using `[e, Matrix.trace_mul_comm, Matrix.mul_assoc, h, Matrix.mul_one]`.
-/
theorem trace_inner_mul (V : HSp D) {n : ℕ} (U W : Mx D V.rank n) (A A' : Mx D n n)
    (h : HMul.hMul A' (adj A) = (1 : Mx D n n)) :
    Matrix.trace (GlobalTheory.StdUnn.inner V (HMul.hMul U A) (HMul.hMul W A')) = Matrix.trace (GlobalTheory.StdUnn.inner V U W) := by
  have e : GlobalTheory.StdUnn.inner V (HMul.hMul U A) (HMul.hMul W A') =
      HMul.hMul (adj A) (HMul.hMul (GlobalTheory.StdUnn.inner V U W) A') := by
    simp only [GlobalTheory.StdUnn.inner, adj_mul, Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, h, Matrix.mul_one]

/- English proof (translation)
Establish `: adj (-x) = -adj x` using `by ext i j; simp [adj]`. Simplify using `only [GlobalTheory.StdUnn.inner, this, Matrix.neg_mul]`.
-/
theorem inner_neg_left (V : HSp D) {n : ℕ} (x y : Mx D V.rank n) :
    GlobalTheory.StdUnn.inner V (-x) y = -GlobalTheory.StdUnn.inner V x y := by
  have : adj (-x) = -adj x := by ext i j; simp [adj]
  simp only [GlobalTheory.StdUnn.inner, this, Matrix.neg_mul]

/- English proof (translation)
Simplify using `only [GlobalTheory.StdUnn.inner, Matrix.mul_neg]`.
-/
theorem inner_neg_right (V : HSp D) {n : ℕ} (x y : Mx D V.rank n) :
    GlobalTheory.StdUnn.inner V x (-y) = -GlobalTheory.StdUnn.inner V x y := by
  simp only [GlobalTheory.StdUnn.inner, Matrix.mul_neg]

/- English proof (translation)
Establish `: adj (x - x') = adj x - adj x'` using `by ext i j; simp [adj]`. Simplify using `only [GlobalTheory.StdUnn.inner, this, Matrix.sub_mul]`.
-/
theorem inner_sub_left (V : HSp D) {n : ℕ} (x x' y : Mx D V.rank n) :
    GlobalTheory.StdUnn.inner V (x - x') y = GlobalTheory.StdUnn.inner V x y - GlobalTheory.StdUnn.inner V x' y := by
  have : adj (x - x') = adj x - adj x' := by ext i j; simp [adj]
  simp only [GlobalTheory.StdUnn.inner, this, Matrix.sub_mul]

/- English proof (translation)
Simplify using `only [GlobalTheory.StdUnn.inner, Matrix.mul_sub]`.
-/
theorem inner_sub_right (V : HSp D) {n : ℕ} (x y y' : Mx D V.rank n) :
    GlobalTheory.StdUnn.inner V x (y - y') = GlobalTheory.StdUnn.inner V x y - GlobalTheory.StdUnn.inner V x y' := by
  simp only [GlobalTheory.StdUnn.inner, Matrix.mul_sub]

/- English proof (translation)
Establish `: adj (0 : Mx D V.rank n) = 0` using `by ext i j; simp [adj]`. Simplify using `only [GlobalTheory.StdUnn.inner, this, Matrix.zero_mul]`.
-/
theorem inner_zero_left (V : HSp D) {n : ℕ} (y : Mx D V.rank n) :
    GlobalTheory.StdUnn.inner V (0 : Mx D V.rank n) y = 0 := by
  have : adj (0 : Mx D V.rank n) = 0 := by ext i j; simp [adj]
  simp only [GlobalTheory.StdUnn.inner, this, Matrix.zero_mul]

/- English proof (translation)
Simplify using `only [GlobalTheory.StdUnn.inner, Matrix.mul_assoc]`.
-/
theorem inner_mul_right (V : HSp D) {n : ℕ} (x y : Mx D V.rank n) (B : Mx D n n) :
    GlobalTheory.StdUnn.inner V x (HMul.hMul y B) = HMul.hMul (GlobalTheory.StdUnn.inner V x y) B := by
  simp only [GlobalTheory.StdUnn.inner, Matrix.mul_assoc]

/- English proof (translation)
Simplify using `[Matrix.trace, adj, map_sum]`.
-/
theorem trace_adj {n : ℕ} (M : Mx D n n) : Matrix.trace (adj M) = cA D (Matrix.trace M) := by
  simp [Matrix.trace, adj, map_sum]

/- English proof (translation)
Simplify using `only [GlobalTheory.StdUnn.inner, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc]`.
-/
theorem adj_inner (V : HSp D) {n : ℕ} (x y : Mx D V.rank n) :
    adj (GlobalTheory.StdUnn.inner V x y) = GlobalTheory.StdUnn.inner V y x := by
  simp only [GlobalTheory.StdUnn.inner, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc]

/- English proof (translation)
Rewrite using `[← trace_adj, adj_mul, adj_inner, hB, Matrix.trace_mul_comm]`.
-/
theorem trace_swap (V : HSp D) {n : ℕ} (x y : Mx D V.rank n) (B : Mx D n n) (hB : adj B = B) :
    Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V y x) B) =
      cA D (Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V x y) B)) := by
  rw [← trace_adj, adj_mul, adj_inner, hB, Matrix.trace_mul_comm]

/- English proof (translation)
Take the linear combination `t₁ * h`.
-/
theorem exp_ring {R : Type*} [CommRing R] (c t₁ t₃ t₄ t₅ : R) (h : c + c = 1) :
    -t₁ + t₅ + c * t₃ + c * t₄ = t₅ + c * (t₃ - t₁ - t₁ + t₄) := by
  linear_combination t₁ * h

/- English proof (translation)
Normalize the expressions using the abelian group laws.
-/
theorem sub_group {G : Type*} [AddCommGroup G] (a b c d : G) : a - b - (c - d) = a - b - c + d := by
  abel

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem halfTr_eq (z : AE D) : halfTr z = algebraMap D.host.F (AF D.host.F) (1 / 2) * trA z := rfl

/- English proof (translation)
Rewrite using `[← map_add, add_halves, map_one]`.
-/
theorem half_add_half : algebraMap D.host.F (AF D.host.F) (1 / 2) + algebraMap D.host.F (AF D.host.F) (1 / 2) = 1 := by
  rw [← map_add, add_halves, map_one]

/- English proof (translation)
Establish `: halfTr (incA D e) = algebraMap D.host.F (AF D.host.F) (1 / 2 * Algebra.trace D.host.F D.host.E e)`. Establish `h : Algebra.trace (AF D.host.F) (AE D) (incA D e) = algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E e)` using `by show Algebra.trace (AF D.host.F) (AE D) ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) = _`. Rewrite using `[Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]`. Rewrite using `[halfTr_eq, map_mul, trA, h]`. Rewrite using `[this]`.

Conclude with `hψ.2.2.1 _`.
-/
theorem psi_halfTr_incA (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (e : D.host.E) :
    ψ (halfTr (incA D e)) = 1 := by
  have : halfTr (incA D e) = algebraMap D.host.F (AF D.host.F) (1 / 2 * Algebra.trace D.host.F D.host.E e) := by
    have h : Algebra.trace (AF D.host.F) (AE D) (incA D e) =
        algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E e) := by
      show Algebra.trace (AF D.host.F) (AE D) ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) = _
      rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]
    rw [halfTr_eq, map_mul, trA, h]
  rw [this]
  exact hψ.2.2.1 _

/- English proof (translation)
Use `⟨Matrix.trace (pᴴ * (HSpace.gram V * p) * b), ?_⟩` and prove the remaining obligations. Establish `: HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) (rat p)) (rat b) = rat (pᴴ * (HSpace.gram V * p) * b)`. Rewrite using `[rat_mul, rat_mul, rat_mul, rat_conjTranspose]`. Both sides reduce to the same expression. Rewrite using `[this]`.

Simplify using `only [Matrix.trace, Matrix.diag_apply, rat, Matrix.map_apply, map_sum]`.
-/
theorem trace_inner_rat (V : HSp D) {n : ℕ} (p : Matrix (Fin V.rank) (Fin n) D.host.E) (b : Matrix (Fin n) (Fin n) D.host.E) :
    ∃ e : D.host.E, Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) (rat p)) (rat b)) = incA D e := by
  refine ⟨Matrix.trace (pᴴ * (HSpace.gram V * p) * b), ?_⟩
  have : HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) (rat p)) (rat b) = rat (pᴴ * (HSpace.gram V * p) * b) := by
    rw [rat_mul, rat_mul, rat_mul, rat_conjTranspose]
    rfl
  rw [this]
  simp only [Matrix.trace, Matrix.diag_apply, rat, Matrix.map_apply, map_sum]

/- English proof (translation)
Substitute `e₁ e₂ e₃` using the available equality. Establish `h : trA (-t₁ + t₅) + halfTr Y + halfTr t₄ = trA t₅ + halfTr (Y - cA D t₁ - t₁ + t₄)`. Simplify using `only [halfTr_eq, trA, map_add, map_sub, map_neg, GlobalTheory.DualPairCheck.trace_cA]`. Conclude with `exp_ring _ _ _ _ _ half_add_half`. Rewrite using `[← AddChar.map_add_eq_mul, ← h, AddChar.map_add_eq_mul ψ _ (halfTr t₄), e₄, mul_one]`.
-/
theorem psi_combine (ψ : AddChar (AF D.host.F) ℂ) (X Y T t₁ t₃ t₄ t₅ : AE D) (e₁ : X = -t₁ + t₅) (e₂ : Y = t₃)
    (e₃ : T = t₃ - cA D t₁ - t₁ + t₄) (e₄ : ψ (halfTr t₄) = 1) :
    ψ (trA X + halfTr Y) = ψ (trA t₅) * ψ (halfTr T) := by
  subst e₁ e₂ e₃
  have h : trA (-t₁ + t₅) + halfTr Y + halfTr t₄ = trA t₅ + halfTr (Y - cA D t₁ - t₁ + t₄) := by
    simp only [halfTr_eq, trA, map_add, map_sub, map_neg, GlobalTheory.DualPairCheck.trace_cA]
    exact exp_ring _ _ _ _ _ half_add_half
  rw [← AddChar.map_add_eq_mul, ← h, AddChar.map_add_eq_mul ψ _ (halfTr t₄), e₄, mul_one]

/- English proof (translation)
Establish `hunit : IsUnit (aᴴ).det`. Rewrite using `[Matrix.det_conjTranspose]`. Conclude with `ha.star`. Establish `hA : HMul.hMul (rat (cT (D.sp.cm.sig : D.host.E →+* D.host.E) a)⁻¹) (adj (rat a)) = (1 : Mx D (r + s) (r + s))`. Establish `: cT (D.sp.cm.sig : D.host.E →+* D.host.E) a = aᴴ` using `rfl`.

Rewrite using `[this, ← rat_conjTranspose, ← rat_mul, Matrix.nonsing_inv_mul _ hunit, rat_one]`. Establish `hB : adj (rat b) = rat b`. Rewrite using `[← rat_conjTranspose]`. Conclude with `congrArg rat hb`. Establish `hz : rat (colJoin p q * a) = HMul.hMul (colJoin (rat p) (rat q)) (rat a)`.

Rewrite using `[rat_mul, rat_colJoin]`. Establish `hzx : rat (colJoin p q * a) + xPart v = HMul.hMul (colJoin (rat p - y₁) (rat q)) (rat a)`. Rewrite using `[hz, hx, ← sub_eq_add_neg, ← Matrix.sub_mul, ← colJoin_sub, sub_zero]`. Take `⟨e, he⟩` from `trace_inner_rat V p b`. Establish `e₄ : ψ (halfTr (Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) (rat p)) (rat b)))) = 1`.

Rewrite using `[he]`. Conclude with `psi_halfTr_incA ψ hψ e`. Establish `e1 : Matrix.trace (GlobalTheory.StdUnn.inner V (rat (colJoin p q * a)) (yPart v)) = -Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) y₁) (rat b)) + Matrix.trace (GlobalTheory.StdUnn.inner V (rat q) y₂)`. Rewrite using `[hz, hy, trace_inner_mul V _ _ _ _ hA, trace_inner_join, inner_neg_right, inner_mul_right, Matrix.trace_neg]`. Establish `e2 : Matrix.trace (GlobalTheory.StdUnn.inner V (xPart v) (yPart v)) = Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V y₁ y₁) (rat b))`.

Rewrite using `[hx, hy, ← Matrix.neg_mul, trace_inner_mul V _ _ _ _ hA]`. Establish `: -colJoin y₁ (0 : Mx D V.rank s) = colJoin (-y₁) (0 : Mx D V.rank s)`. Rewrite using `[← colJoin_neg, neg_zero]`. Rewrite using `[this, trace_inner_join, inner_zero_left, inner_neg_left, inner_neg_right, inner_mul_right]`. Simplify using the standard rewrite rules.

Establish `e3 : Matrix.trace (HMul.hMul (rat b) (GlobalTheory.StdUnn.inner V (y₁ - rat p) (y₁ - rat p)) : Mx D r r) = Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V y₁ y₁) (rat b)) - cA D (Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) y₁) (rat b))) - Matrix.trace (HMul. …`. Rewrite using `[Matrix.trace_mul_comm, ← trace_swap V (rat p) y₁ (rat b) hB, inner_sub_left, inner_sub_right, inner_sub_right]`. Simplify using `only [Matrix.sub_mul, Matrix.trace_sub]`. Conclude with `sub_group _ _ _ _`. Establish `hc` using `psi_combine ψ _ _ _ _ _ _ _ e1 e2 e3 e₄`.

Use `show ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V (rat (colJoin p q * a)) (yPart v))) + halfTr (Matrix.trace (GlobalTheory.StdUnn.inner V (xPart v) (yPart v)))) * Φ (rat (colJoin p q * a) + xPart v) = _`. Rewrite using `[hc, hzx, mul_assoc]`. Both sides reduce to the same expression.
-/
theorem summand (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (V : HSp D) (r s : ℕ)
    (b : Matrix (Fin r) (Fin r) D.host.E) (hb : (b.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose = b)
    (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E) (ha : IsUnit a.det)
    (Φ : Mx D V.rank (r + s) → ℂ) (y₁ : Mx D V.rank r) (y₂ : Mx D V.rank s) (v : Mx D V.rank ((r + s) + (r + s)))
    (hx : xPart v = -HMul.hMul (colJoin y₁ (0 : Mx D V.rank s)) (rat a))
    (hy : yPart v = HMul.hMul (colJoin (-HMul.hMul y₁ (rat b)) y₂) (rat (cT (D.sp.cm.sig : D.host.E →+* D.host.E) a)⁻¹))
    (p : Matrix (Fin V.rank) (Fin r) D.host.E) (q : Matrix (Fin V.rank) (Fin s) D.host.E) :
    Heisenberg₂ ψ V v Φ (rat (colJoin p q * a)) = cellTerm ψ V b a Φ p q y₁ y₂ := by
  have hunit : IsUnit (aᴴ).det := by
    rw [Matrix.det_conjTranspose]; exact ha.star
  have hA : HMul.hMul (rat (cT (D.sp.cm.sig : D.host.E →+* D.host.E) a)⁻¹) (adj (rat a)) = (1 : Mx D (r + s) (r + s)) := by
    have : cT (D.sp.cm.sig : D.host.E →+* D.host.E) a = aᴴ := rfl
    rw [this, ← rat_conjTranspose, ← rat_mul, Matrix.nonsing_inv_mul _ hunit, rat_one]
  have hB : adj (rat b) = rat b := by
    rw [← rat_conjTranspose]
    exact congrArg rat hb
  have hz : rat (colJoin p q * a) = HMul.hMul (colJoin (rat p) (rat q)) (rat a) := by
    rw [rat_mul, rat_colJoin]
  have hzx : rat (colJoin p q * a) + xPart v = HMul.hMul (colJoin (rat p - y₁) (rat q)) (rat a) := by
    rw [hz, hx, ← sub_eq_add_neg, ← Matrix.sub_mul, ← colJoin_sub, sub_zero]
  obtain ⟨e, he⟩ := trace_inner_rat V p b
  have e₄ : ψ (halfTr (Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) (rat p)) (rat b)))) = 1 := by
    rw [he]
    exact psi_halfTr_incA ψ hψ e
  have e1 : Matrix.trace (GlobalTheory.StdUnn.inner V (rat (colJoin p q * a)) (yPart v)) =
      -Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) y₁) (rat b)) + Matrix.trace (GlobalTheory.StdUnn.inner V (rat q) y₂) := by
    rw [hz, hy, trace_inner_mul V _ _ _ _ hA, trace_inner_join, inner_neg_right, inner_mul_right, Matrix.trace_neg]
  have e2 : Matrix.trace (GlobalTheory.StdUnn.inner V (xPart v) (yPart v)) =
      Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V y₁ y₁) (rat b)) := by
    rw [hx, hy, ← Matrix.neg_mul, trace_inner_mul V _ _ _ _ hA]
    have : -colJoin y₁ (0 : Mx D V.rank s) = colJoin (-y₁) (0 : Mx D V.rank s) := by
      rw [← colJoin_neg, neg_zero]
    rw [this, trace_inner_join, inner_zero_left, inner_neg_left, inner_neg_right, inner_mul_right]
    simp
  have e3 : Matrix.trace (HMul.hMul (rat b) (GlobalTheory.StdUnn.inner V (y₁ - rat p) (y₁ - rat p)) : Mx D r r) =
      Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V y₁ y₁) (rat b))
        - cA D (Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) y₁) (rat b)))
        - Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) y₁) (rat b))
        + Matrix.trace (HMul.hMul (GlobalTheory.StdUnn.inner V (rat p) (rat p)) (rat b)) := by
    rw [Matrix.trace_mul_comm, ← trace_swap V (rat p) y₁ (rat b) hB, inner_sub_left, inner_sub_right, inner_sub_right]
    simp only [Matrix.sub_mul, Matrix.trace_sub]
    exact sub_group _ _ _ _
  have hc := psi_combine ψ _ _ _ _ _ _ _ e1 e2 e3 e₄
  show ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V (rat (colJoin p q * a)) (yPart v))) +
      halfTr (Matrix.trace (GlobalTheory.StdUnn.inner V (xPart v) (yPart v)))) * Φ (rat (colJoin p q * a) + xPart v) = _
  rw [hc, hzx, mul_assoc]
  rfl

end GlobalTheory.CompanionTheory.EisUnfold.Summand
