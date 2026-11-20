import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantExpansionBoundStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.ChDens

open scoped MatrixOrder in

/- English proof (translation)
Take `⟨B, hB⟩` from `CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.inv.posSemidef.nonneg`. Rewrite `hB` using `[star_eq_conjTranspose]`. Establish `hu : IsUnit H.det` using `(Matrix.isUnit_iff_isUnit_det _).1 hH.isUnit`. Establish `hC : B * H * Bᴴ = 1`. Rewrite using `[Matrix.mul_assoc, mul_eq_one_comm, Matrix.mul_assoc, ← hB]`.

Conclude with `Matrix.mul_nonsing_inv _ hu`. Establish `hd : ∀ (Y : Matrix (Fin m) (Fin m) ℂ) (k : Fin m), (B * Y * Bᴴ) k k = form Y (B k) (B k)`. Introduce `Y k`. Rewrite using `[form_eq_sum, Matrix.mul_apply, Finset.sum_comm]`. Simplify using `[Matrix.mul_apply, Finset.sum_mul]`.

Establish `e1 : X.trace = ∑ k, form H (X *ᵥ B k) (B k)`. Establish `h1 : X.trace = (B * (Xᵀ * H) * Bᴴ).trace`. Rewrite using `[Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← hB, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, Matrix.trace_transpose]`. Rewrite using `[h1, Matrix.trace]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.diag_apply, hd, form, form, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]`. Establish `hn : ∀ k, gnorm H (B k) = 1` using `fun k => by`. Rewrite using `[gnorm, ← hd, hC]`. Simplify using the standard rewrite rules. Rewrite using `[e1]`.

Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Establish `: ∀ k, ‖form H (X *ᵥ B k) (B k)‖ ≤ opNorm H H X` using `fun k => by`. Use `(norm_form_le hH.posSemidef _ _).trans ?_` and prove the remaining obligations. Use `gnorm_mulVec_le hH hH.posSemidef X (B k)` as an intermediate fact. Rewrite `this`, the goal using `[hn k]`.

Simplify using `using this`. Simplify `Finset.sum_le_card_nsmul Finset.univ _ _ fun k _ => this k` using `[Finset.card_univ]`.
-/
theorem trace_le (m : ℕ) (H X : Matrix (Fin m) (Fin m) ℂ) (hH : H.PosDef) :
    ‖X.trace‖ ≤ m * opNorm H H X := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.inv.posSemidef.nonneg
  rw [star_eq_conjTranspose] at hB
  have hu : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det _).1 hH.isUnit
  have hC : B * H * Bᴴ = 1 := by
    rw [Matrix.mul_assoc, mul_eq_one_comm, Matrix.mul_assoc, ← hB]
    exact Matrix.mul_nonsing_inv _ hu
  have hd : ∀ (Y : Matrix (Fin m) (Fin m) ℂ) (k : Fin m), (B * Y * Bᴴ) k k = form Y (B k) (B k) := by
    intro Y k
    rw [form_eq_sum, Matrix.mul_apply, Finset.sum_comm]
    simp [Matrix.mul_apply, Finset.sum_mul]
  have e1 : X.trace = ∑ k, form H (X *ᵥ B k) (B k) := by
    have h1 : X.trace = (B * (Xᵀ * H) * Bᴴ).trace := by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← hB, Matrix.trace_mul_comm, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, Matrix.trace_transpose]
    rw [h1, Matrix.trace]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.diag_apply, hd, form, form, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  have hn : ∀ k, gnorm H (B k) = 1 := fun k => by
    rw [gnorm, ← hd, hC]; simp
  rw [e1]
  refine (norm_sum_le _ _).trans ?_
  have : ∀ k, ‖form H (X *ᵥ B k) (B k)‖ ≤ opNorm H H X := fun k => by
    refine (norm_form_le hH.posSemidef _ _).trans ?_
    have := gnorm_mulVec_le hH hH.posSemidef X (B k)
    rw [hn k] at this ⊢
    simpa using this
  simpa [Finset.card_univ] using Finset.sum_le_card_nsmul Finset.univ _ _ fun k _ => this k

/- English proof (translation)
Introduce `n T _ μ Hm F G C hP hG hC hb ξ₁ η₁ ξ₂ η₂`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_le_sum fun τ _ => ?_` and prove the remaining obligations. Establish `htr : ∀ X Y : Matrix (Fin (μ τ)) (Fin (μ τ)) ℂ, ∑ a, ∑ b, X a b * Y b a = (X * Y).trace`.

Introduce `X Y`. Simplify using `[Matrix.trace, Matrix.mul_apply]`. Establish `hw : ∑ a, ∑ b, HermFrame.wedge (fun ξ η => F τ ξ η a b) (fun ξ η => F τ ξ η b a) ξ₁ η₁ ξ₂ η₂ = (F τ ξ₁ η₁ * F τ ξ₂ η₂).trace + (F τ ξ₂ η₂ * F τ ξ₁ η₁).trace - (F τ ξ₁ η₂ * F τ ξ₂ η₁).trace - (F τ ξ₂ η₁ * F τ ξ₁ η₂).trace`. Simplify using `only [HermFrame.wedge, ← htr, Finset.sum_add_distrib, Finset.sum_sub_distrib]`. Establish `hm : ∀ ξ η ξ' η' : V n, ‖(F τ ξ η * F τ ξ' η').trace‖ ≤ μ τ * (C ^ 2 * (gnorm G ξ.ofLp * gnorm G η.ofLp * (gnorm G ξ'.ofLp * gnorm G η'.ofLp)))`.

Introduce `ξ η ξ' η'`. Use `(trace_le _ _ _ (hP τ)).trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))` and prove the remaining obligations. Use `(opNorm_mul_le (hP τ) (hP τ) (hP τ).posSemidef _ _).trans ?_` and prove the remaining obligations. Establish `h0 : 0 ≤ C * gnorm G ξ.ofLp * gnorm G η.ofLp`. Use `gnorm_nonneg G ξ.ofLp` as an intermediate fact.

Use `gnorm_nonneg G η.ofLp` as an intermediate fact. Check the signs of the components of the expression. Combine the equalities or inequalities in the displayed calculation. Use `set P := gnorm G ξ₁.ofLp * gnorm G η₁.ofLp * (gnorm G ξ₂.ofLp * gnorm G η₂.ofLp) with hPd`. Establish `e2 : gnorm G ξ₂.ofLp * gnorm G η₂.ofLp * (gnorm G ξ₁.ofLp * gnorm G η₁.ofLp) = P` using `by rw [hPd]; ring`.

Establish `e3 : gnorm G ξ₁.ofLp * gnorm G η₂.ofLp * (gnorm G ξ₂.ofLp * gnorm G η₁.ofLp) = P` using `by rw [hPd]; ring`. Establish `e4 : gnorm G ξ₂.ofLp * gnorm G η₁.ofLp * (gnorm G ξ₁.ofLp * gnorm G η₂.ofLp) = P` using `by rw [hPd]; ring`. Establish `m1` using `hm ξ₁ η₁ ξ₂ η₂`. Establish `m2` using `hm ξ₂ η₂ ξ₁ η₁`. Establish `m3` using `hm ξ₁ η₂ ξ₂ η₁`.

Establish `m4` using `hm ξ₂ η₁ ξ₁ η₂`. Rewrite `m2` using `[e2]`. Rewrite `m3` using `[e3]`. Rewrite `m4` using `[e4]`. Rewrite `m1` using `[← hPd]`.

Establish `hs : ‖(F τ ξ₁ η₁ * F τ ξ₂ η₂).trace + (F τ ξ₂ η₂ * F τ ξ₁ η₁).trace - (F τ ξ₁ η₂ * F τ ξ₂ η₁).trace - (F τ ξ₂ η₁ * F τ ξ₁ η₂).trace‖ ≤ 4 * (μ τ * (C ^ 2 * P))`. Establish `t1` using `norm_add_le (F τ ξ₁ η₁ * F τ ξ₂ η₂).trace (F τ ξ₂ η₂ * F τ ξ₁ η₁).trace`. Establish `t2` using `norm_sub_le ((F τ ξ₁ η₁ * F τ ξ₂ η₂).trace + (F τ ξ₂ η₂ * F τ ξ₁ η₁).trace) (F τ ξ₁ η₂ * F τ ξ₂ η₁).trace`. Establish `t3` using `norm_sub_le ((F τ ξ₁ η₁ * F τ ξ₂ η₂).trace + (F τ ξ₂ η₂ * F τ ξ₁ η₁).trace - (F τ ξ₁ η₂ * F τ ξ₂ η₁).trace) (F τ ξ₂ η₁ * F τ ξ₁ η₂).trace`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[norm_mul, hw]`. Establish `hk : ‖kappa ^ 2 / 2‖ = ‖kappa‖ ^ 2 / 2` using `by simp [norm_div, norm_pow]`. Rewrite using `[hk]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem wedge_le : ∀ (n : ℕ) (T : Type) [Fintype T] (μ : T → ℕ) (Hm : ∀ τ, Matrix (Fin (μ τ)) (Fin (μ τ)) ℂ)
    (F : ∀ τ, V n → V n → Matrix (Fin (μ τ)) (Fin (μ τ)) ℂ) (G : Matrix (Fin n) (Fin n) ℂ) (C : ℝ),
    (∀ τ, (Hm τ).PosDef) → G.PosSemidef → 0 ≤ C →
    (∀ τ ξ η, opNorm (Hm τ) (Hm τ) (F τ ξ η) ≤ C * gnorm G ξ.ofLp * gnorm G η.ofLp) → ∀ ξ₁ η₁ ξ₂ η₂ : V n,
    ‖∑ τ, kappa ^ 2 / 2 * ∑ a, ∑ b, HermFrame.wedge (fun ξ η => F τ ξ η a b) (fun ξ η => F τ ξ η b a) ξ₁ η₁ ξ₂ η₂‖ ≤
      (∑ τ, 2 * ‖kappa‖ ^ 2 * (μ τ : ℝ) * C ^ 2) *
        (gnorm G ξ₁.ofLp * gnorm G η₁.ofLp * (gnorm G ξ₂.ofLp * gnorm G η₂.ofLp)) := by
  intro n T _ μ Hm F G C hP hG hC hb ξ₁ η₁ ξ₂ η₂
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun τ _ => ?_
  have htr : ∀ X Y : Matrix (Fin (μ τ)) (Fin (μ τ)) ℂ, ∑ a, ∑ b, X a b * Y b a = (X * Y).trace := by
    intro X Y; simp [Matrix.trace, Matrix.mul_apply]
  have hw : ∑ a, ∑ b, HermFrame.wedge (fun ξ η => F τ ξ η a b) (fun ξ η => F τ ξ η b a) ξ₁ η₁ ξ₂ η₂ =
      (F τ ξ₁ η₁ * F τ ξ₂ η₂).trace + (F τ ξ₂ η₂ * F τ ξ₁ η₁).trace -
        (F τ ξ₁ η₂ * F τ ξ₂ η₁).trace - (F τ ξ₂ η₁ * F τ ξ₁ η₂).trace := by
    simp only [HermFrame.wedge, ← htr, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hm : ∀ ξ η ξ' η' : V n, ‖(F τ ξ η * F τ ξ' η').trace‖ ≤
      μ τ * (C ^ 2 * (gnorm G ξ.ofLp * gnorm G η.ofLp * (gnorm G ξ'.ofLp * gnorm G η'.ofLp))) := by
    intro ξ η ξ' η'
    refine (trace_le _ _ _ (hP τ)).trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    refine (opNorm_mul_le (hP τ) (hP τ) (hP τ).posSemidef _ _).trans ?_
    have h0 : 0 ≤ C * gnorm G ξ.ofLp * gnorm G η.ofLp := by
      have := gnorm_nonneg G ξ.ofLp; have := gnorm_nonneg G η.ofLp; positivity
    calc _ ≤ (C * gnorm G ξ.ofLp * gnorm G η.ofLp) * (C * gnorm G ξ'.ofLp * gnorm G η'.ofLp) :=
          mul_le_mul (hb τ ξ η) (hb τ ξ' η') (opNorm_nonneg _ _ _) h0
      _ = _ := by ring
  set P := gnorm G ξ₁.ofLp * gnorm G η₁.ofLp * (gnorm G ξ₂.ofLp * gnorm G η₂.ofLp) with hPd
  have e2 : gnorm G ξ₂.ofLp * gnorm G η₂.ofLp * (gnorm G ξ₁.ofLp * gnorm G η₁.ofLp) = P := by rw [hPd]; ring
  have e3 : gnorm G ξ₁.ofLp * gnorm G η₂.ofLp * (gnorm G ξ₂.ofLp * gnorm G η₁.ofLp) = P := by rw [hPd]; ring
  have e4 : gnorm G ξ₂.ofLp * gnorm G η₁.ofLp * (gnorm G ξ₁.ofLp * gnorm G η₂.ofLp) = P := by rw [hPd]; ring
  have m1 := hm ξ₁ η₁ ξ₂ η₂
  have m2 := hm ξ₂ η₂ ξ₁ η₁
  have m3 := hm ξ₁ η₂ ξ₂ η₁
  have m4 := hm ξ₂ η₁ ξ₁ η₂
  rw [e2] at m2; rw [e3] at m3; rw [e4] at m4; rw [← hPd] at m1
  have hs : ‖(F τ ξ₁ η₁ * F τ ξ₂ η₂).trace + (F τ ξ₂ η₂ * F τ ξ₁ η₁).trace -
        (F τ ξ₁ η₂ * F τ ξ₂ η₁).trace - (F τ ξ₂ η₁ * F τ ξ₁ η₂).trace‖ ≤ 4 * (μ τ * (C ^ 2 * P)) := by
    have t1 := norm_add_le (F τ ξ₁ η₁ * F τ ξ₂ η₂).trace (F τ ξ₂ η₂ * F τ ξ₁ η₁).trace
    have t2 := norm_sub_le ((F τ ξ₁ η₁ * F τ ξ₂ η₂).trace + (F τ ξ₂ η₂ * F τ ξ₁ η₁).trace)
      (F τ ξ₁ η₂ * F τ ξ₂ η₁).trace
    have t3 := norm_sub_le ((F τ ξ₁ η₁ * F τ ξ₂ η₂).trace + (F τ ξ₂ η₂ * F τ ξ₁ η₁).trace -
      (F τ ξ₁ η₂ * F τ ξ₂ η₁).trace) (F τ ξ₂ η₁ * F τ ξ₁ η₂).trace
    linarith
  rw [norm_mul, hw]
  have hk : ‖kappa ^ 2 / 2‖ = ‖kappa‖ ^ 2 / 2 := by simp [norm_div, norm_pow]
  rw [hk]
  calc ‖kappa‖ ^ 2 / 2 * ‖(F τ ξ₁ η₁ * F τ ξ₂ η₂).trace + (F τ ξ₂ η₂ * F τ ξ₁ η₁).trace -
        (F τ ξ₁ η₂ * F τ ξ₂ η₁).trace - (F τ ξ₂ η₁ * F τ ξ₁ η₂).trace‖
        ≤ ‖kappa‖ ^ 2 / 2 * (4 * (μ τ * (C ^ 2 * P))) := by gcongr
    _ = 2 * ‖kappa‖ ^ 2 * (μ τ : ℝ) * C ^ 2 * P := by ring

/- English proof (translation)
Simplify using `[bas, EuclideanSpace.single]`.
-/
theorem toLp_single (n : ℕ) (p : Fin n) : (WithLp.toLp 2 (Pi.single p (1 : ℂ)) : V n) = bas n p := by
  simp [bas, EuclideanSpace.single]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `x x' y`. Simplify using `[WithLp.toLp_add, hF.add_left]`. Introduce `c x y`. Simplify using `[WithLp.toLp_smul, hF.smul_left]`.

Introduce `x y y'`. Simplify using `[WithLp.toLp_add, hF.add_right]`. Introduce `c x y`. Simplify using `[WithLp.toLp_smul, hF.smul_right]`.
-/
theorem isSesq_entry {n m : ℕ} {F : V n → V n → Matrix (Fin m) (Fin m) ℂ} (hF : IsSesq F) (a b : Fin m) :
    IsSesq (fun x y : Fin n → ℂ => F (WithLp.toLp 2 x) (WithLp.toLp 2 y) a b) := by
  constructor
  · intro x x' y; simp [WithLp.toLp_add, hF.add_left]
  · intro c x y; simp [WithLp.toLp_smul, hF.smul_left]
  · intro x y y'; simp [WithLp.toLp_add, hF.add_right]
  · intro c x y; simp [WithLp.toLp_smul, hF.smul_right]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `x x' y`. Simplify using `[WithLp.toLp_add, (hF _).add_left, Finset.sum_add_distrib]`. Expand and normalize the polynomial expressions, which then agree. Introduce `c x y`.

Simplify using `[WithLp.toLp_smul, (hF _).smul_left, Finset.mul_sum]`. Introduce `x y y'`. Simplify using `[WithLp.toLp_add, (hF _).add_right, Finset.sum_add_distrib]`. Expand and normalize the polynomial expressions, which then agree. Introduce `c x y`.

Simplify using `[WithLp.toLp_smul, (hF _).smul_right, Finset.mul_sum]`.
-/
theorem isSesq_trace {n : ℕ} {T : Type} [Fintype T] {μ : T → ℕ}
    {F : ∀ τ, V n → V n → Matrix (Fin (μ τ)) (Fin (μ τ)) ℂ} (hF : ∀ τ, IsSesq (F τ)) :
    IsSesq (fun x y : Fin n → ℂ => -∑ τ, (F τ (WithLp.toLp 2 x) (WithLp.toLp 2 y)).trace) := by
  constructor
  · intro x x' y; simp [WithLp.toLp_add, (hF _).add_left, Finset.sum_add_distrib]; ring
  · intro c x y; simp [WithLp.toLp_smul, (hF _).smul_left, Finset.mul_sum]
  · intro x y y'; simp [WithLp.toLp_add, (hF _).add_right, Finset.sum_add_distrib]; ring
  · intro c x y; simp [WithLp.toLp_smul, (hF _).smul_right, Finset.mul_sum]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `x x' y`. Simplify using `only [hg.add_left]`. Expand and normalize the polynomial expressions, which then agree. Introduce `c x y`.

Simplify using `only [hg.smul_left, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Introduce `x y y'`. Simplify using `only [hg.add_right]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `c x y`. Simplify using `only [hg.smul_right, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isSesq_mul {n : ℕ} {g : (Fin n → ℂ) → (Fin n → ℂ) → ℂ} (hg : IsSesq g) (d : ℂ) :
    IsSesq (fun x y => d * g x y) := by
  constructor
  · intro x x' y; simp only [hg.add_left]; ring
  · intro c x y; simp only [hg.smul_left, smul_eq_mul]; ring
  · intro x y y'; simp only [hg.add_right]; ring
  · intro c x y; simp only [hg.smul_right, smul_eq_mul]; ring

/- English proof (translation)
Introduce `e T _ μ C`. Use `set C₀ := max C 0 with hC₀`. Establish `hC₀0 : 0 ≤ C₀` using `le_max_right _ _`. Use `set K1 : ℝ := ∑ τ, 2 * ‖kappa‖ ^ 2 * (μ τ : ℝ) * C₀ ^ 2 with hK1d`. Use `set K2 : ℝ := ∑ τ, (μ τ : ℝ) * C₀ with hK2d`.

Establish `hK1 : 0 ≤ K1` using `Finset.sum_nonneg fun τ _ => by positivity`. Establish `hK2 : 0 ≤ K2` using `Finset.sum_nonneg fun τ _ => by positivity`. Use `⟨((e + 2).factorial : ℝ) ^ 2 * (K1 * K2 ^ e) / Real.pi ^ e, by positivity, ?_⟩` and prove the remaining obligations. Introduce `U H hH u hu G hG hC`. Establish `hCb : ∀ τ (ξ η : V (e + 2)), opNorm (H τ u) (H τ u) (curv (H τ) u ξ η) ≤ C₀ * gnorm G ξ.ofLp * gnorm G η.ofLp` using `fun τ ξ η => (hC τ ξ η).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (gnorm_nonneg _ _)) (gnorm_nonneg _ _))`.

Establish `hS : ∀ τ, IsSesq (curv (H τ) u)` using `fun τ => isSesq_curv ((hH τ).isHermFrame.two hu) ((hH τ).isHermFrame.isUnit u hu)`. Establish `hP : ∀ τ, (H τ u).PosDef` using `fun τ => (hH τ).posDef u hu`. Set `ent : ∀ τ, Fin (μ τ) → Fin (μ τ) → (Fin (e + 2) → ℂ) → (Fin (e + 2) → ℂ) → ℂ` to `fun τ a b x y => curv (H τ) u (WithLp.toLp 2 x) (WithLp.toLp 2 y) a b`. Set `atr : (Fin (e + 2) → ℂ) → (Fin (e + 2) → ℂ) → ℂ` to `fun x y => -∑ τ, (curv (H τ) u (WithLp.toLp 2 x) (WithLp.toLp 2 y)).trace`. Set `c : ℂ` to `kappa ^ 2 / 2`.

Set `J` to `(τ : T) × (Fin (μ τ) × Fin (μ τ) × Fin 4)`. Set `f : J → Fin (e + 2) → (Fin (e + 2) → ℂ) → (Fin (e + 2) → ℂ) → ℂ` to `fun j => Fin.cons (![fun x y => c * ent j.1 j.2.1 j.2.2.1 x y, fun x y => c * ent j.1 j.2.2.1 j.2.1 x y, fun x y => -(c * ent j.1 j.2.1 j.2.2.1 x y), fun x y => -(c * ent j.1 j.2.2.1 j.2.1 x y)] j.2.2.2) (Fin.cons (![ent j.1 j.2.2.1 j.2.1, ent j.1 j.2.1 j.2.2.1, ent j.1 j.2.2.1 j …`. Set `π : J → Equiv.Perm (Fin (e + 2))` to `fun j => ![1, 1, Equiv.swap 0 1, Equiv.swap 0 1] j.2.2.2`. Set `Θ : V (e + 2) → V (e + 2) → V (e + 2) → V (e + 2) → ℂ` to `fun ξ₁ η₁ ξ₂ η₂ => ∑ τ, chTwo (H τ) u ξ₁ η₁ ξ₂ η₂`. Set `ψ : (Fin (e + 2) → Fin (e + 2) → ℂ) → (Fin (e + 2) → Fin (e + 2) → ℂ) → ℂ` to `fun x y => Θ (WithLp.toLp 2 (x 0)) (WithLp.toLp 2 (y 0)) (WithLp.toLp 2 (x 1)) (WithLp.toLp 2 (y 1)) * ∏ i : Fin e, atr (x i.succ.succ) (y i.succ.succ)`.

Establish `key : ∀ x y, ∑ j, ∏ k, f j k (x k) (y (π j k)) = ψ x y`. Introduce `x y`. Rewrite using `[show (∑ j : J, ∏ k, f j k (x k) (y (π j k))) = ∑ τ : T, ∑ p : Fin (μ τ) × Fin (μ τ) × Fin 4, ∏ k, f ⟨τ, p⟩ k (x k) (y (π ⟨τ, p⟩ k)) from Fintype.sum_sigma _]`. Simplify using `only [Fintype.sum_prod_type, ψ, Θ, chTwo, HermFrame.wedge, Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Establish `h01 : ∀ i : Fin e, (Equiv.swap (0 : Fin (e + 2)) 1) i.succ.succ = i.succ.succ` using `fun i => Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (by`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `at this)`. Simplify using `[f, π, ent, c, Fin.sum_univ_four, Fin.prod_univ_succ, h01]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hsesq : ∀ j k, IsSesq (f j k)`. Introduce and unpack `⟨τ, a, b, q⟩ k`. Apply the tactic sequence `have hE : ∀ a b, IsSesq (ent τ a b) := fun a b => isSesq_entry (hS τ) a b`. Use `Fin.cases ?_ (fun k => Fin.cases ?_ (fun i => ?_) k) k` and prove the remaining obligations.

Use `fin_cases q`. Conclude with `isSesq_mul (hE a b) c`. Conclude with `isSesq_mul (hE b a) c`. Simplify `isSesq_mul (hE a b) (-c)` using `[f, neg_mul]`. Simplify `isSesq_mul (hE b a) (-c)` using `[f, neg_mul]`.

Use `fin_cases q`. Conclude with `hE b a`. Conclude with `hE a b`. Conclude with `hE b a`. Conclude with `hE a b`.

Conclude with `isSesq_trace hS`. Establish `hb : ∀ x y : Fin (e + 2) → Fin (e + 2) → ℂ, ‖∑ j, ∏ k, f j k (x k) (y (π j k))‖ ≤ (K1 * K2 ^ e) * ∏ k, (gnorm G (x k) * gnorm G (y k))`. Introduce `x y`. Rewrite using `[key]`. Establish `hΘ` using `wedge_le (e + 2) T μ (fun τ => H τ u) (fun τ => curv (H τ) u) G C₀ hP hG hC₀0 hCb (WithLp.toLp 2 (x 0)) (WithLp.toLp 2 (y 0)) (WithLp.toLp 2 (x 1)) (WithLp.toLp 2 (y 1))`.

Establish `hA : ∀ v w : Fin (e + 2) → ℂ, ‖atr v w‖ ≤ K2 * (gnorm G v * gnorm G w)`. Introduce `v w`. Rewrite using `[norm_neg, hK2d, Finset.sum_mul]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun τ _ => ?_)` and prove the remaining obligations. Use `(trace_le _ (H τ u) _ (hP τ)).trans ?_` and prove the remaining obligations.

Use `hCb τ (WithLp.toLp 2 v) (WithLp.toLp 2 w)` as an intermediate fact. Simplify using `only [WithLp.ofLp_toLp] at this`. Combine the equalities or inequalities in the displayed calculation. Establish `hP2 : ∏ i : Fin e, ‖atr (x i.succ.succ) (y i.succ.succ)‖ ≤ K2 ^ e * ∏ i : Fin e, (gnorm G (x i.succ.succ) * gnorm G (y i.succ.succ))`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Simplify using `only [ψ, Θ, norm_mul, norm_prod]`. Simplify using `only [chTwo, WithLp.ofLp_toLp] at hΘ ⊢`. Rewrite using `[Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.succ_zero_eq_one]`. Establish `n1 : 0 ≤ ∏ i : Fin e, (gnorm G (x i.succ.succ) * gnorm G (y i.succ.succ))` using `Finset.prod_nonneg fun i _ => mul_nonneg (gnorm_nonneg _ _) (gnorm_nonneg _ _)`.

Establish `n2 : 0 ≤ gnorm G (x 0) * gnorm G (y 0) * (gnorm G (x 1) * gnorm G (y 1))`. Use `gnorm_nonneg G (x 0)` as an intermediate fact. Use `gnorm_nonneg G (y 0)` as an intermediate fact. Use `gnorm_nonneg G (x 1)` as an intermediate fact. Use `gnorm_nonneg G (y 1)` as an intermediate fact.

Check the signs of the components of the expression. Combine the equalities or inequalities in the displayed calculation. Establish `h` using `GlobalTheory.T.determinant_expansion_bound (e + 2) J f π G (K1 * K2 ^ e) hsesq hG hb`. Establish `e1 : ∀ s t : Equiv.Perm (Fin (e + 2)), (∑ τ, chTwo (H τ) u (bas _ (s 0)) (bas _ (t 0)) (bas _ (s 1)) (bas _ (t 1))) * ∏ i : Fin e, (Matrix.of fun a b => -∑ τ, (curv (H τ) u (bas _ a) (bas _ b)).trace) (s i.succ.succ) (t i.succ.succ) = ∑ j, ∏ k, f j k (Pi.single (s k) 1) (Pi.singl …`. Introduce `s t`.

Rewrite using `[key (fun k => Pi.single (s k) 1) (fun k => Pi.single (t k) 1)]`. Simplify using `only [ψ, Θ, atr, toLp_single, Matrix.of_apply]`. Unfold `secondChernDensity`. Simplify using `only [e1]`. Rewrite using `[abs_div, abs_neg, abs_of_pos (pow_pos Real.pi_pos e), div_le_iff₀ (pow_pos Real.pi_pos e)]`.

Use `(Complex.abs_re_le_norm _).trans (h.trans (le_of_eq ?_))` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts.
-/
theorem dens22_le : ∀ (e : ℕ) (T : Type) [Fintype T] (μ : T → ℕ) (C : ℝ), ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (U : Set (V (e + 2))) (H : ∀ τ, V (e + 2) → Matrix (Fin (μ τ)) (Fin (μ τ)) ℂ), (∀ τ, IsPosFrame U (H τ)) → ∀ u ∈ U, ∀ G : Matrix (Fin (e + 2)) (Fin (e + 2)) ℂ, G.PosSemidef → (∀ τ (ξ η : V (e + 2)), opNorm (H τ u) (H τ u) (curv (H τ) u ξ η) ≤ C * gnorm G ξ.ofLp * gnorm G η.ofLp) → |secondChernDensity e (fun ξ₁ η₁ ξ₂ η₂ => ∑ τ, chTwo (H τ) u ξ₁ η₁ ξ₂ η₂) (Matrix.of fun a b => -∑ τ, (curv (H τ) u (bas _ a) (bas _ b)).trace)| ≤ C' * G.det.re := by
  intro e T _ μ C
  set C₀ := max C 0 with hC₀
  have hC₀0 : 0 ≤ C₀ := le_max_right _ _
  set K1 : ℝ := ∑ τ, 2 * ‖kappa‖ ^ 2 * (μ τ : ℝ) * C₀ ^ 2 with hK1d
  set K2 : ℝ := ∑ τ, (μ τ : ℝ) * C₀ with hK2d
  have hK1 : 0 ≤ K1 := Finset.sum_nonneg fun τ _ => by positivity
  have hK2 : 0 ≤ K2 := Finset.sum_nonneg fun τ _ => by positivity
  refine ⟨((e + 2).factorial : ℝ) ^ 2 * (K1 * K2 ^ e) / Real.pi ^ e, by positivity, ?_⟩
  intro U H hH u hu G hG hC
  have hCb : ∀ τ (ξ η : V (e + 2)), opNorm (H τ u) (H τ u) (curv (H τ) u ξ η) ≤
      C₀ * gnorm G ξ.ofLp * gnorm G η.ofLp := fun τ ξ η =>
    (hC τ ξ η).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (gnorm_nonneg _ _)) (gnorm_nonneg _ _))
  have hS : ∀ τ, IsSesq (curv (H τ) u) := fun τ =>
    isSesq_curv ((hH τ).isHermFrame.two hu) ((hH τ).isHermFrame.isUnit u hu)
  have hP : ∀ τ, (H τ u).PosDef := fun τ => (hH τ).posDef u hu
  let ent : ∀ τ, Fin (μ τ) → Fin (μ τ) → (Fin (e + 2) → ℂ) → (Fin (e + 2) → ℂ) → ℂ :=
    fun τ a b x y => curv (H τ) u (WithLp.toLp 2 x) (WithLp.toLp 2 y) a b
  let atr : (Fin (e + 2) → ℂ) → (Fin (e + 2) → ℂ) → ℂ :=
    fun x y => -∑ τ, (curv (H τ) u (WithLp.toLp 2 x) (WithLp.toLp 2 y)).trace
  let c : ℂ := kappa ^ 2 / 2
  let J := (τ : T) × (Fin (μ τ) × Fin (μ τ) × Fin 4)
  let f : J → Fin (e + 2) → (Fin (e + 2) → ℂ) → (Fin (e + 2) → ℂ) → ℂ := fun j =>
    Fin.cons (![fun x y => c * ent j.1 j.2.1 j.2.2.1 x y, fun x y => c * ent j.1 j.2.2.1 j.2.1 x y,
        fun x y => -(c * ent j.1 j.2.1 j.2.2.1 x y), fun x y => -(c * ent j.1 j.2.2.1 j.2.1 x y)] j.2.2.2)
      (Fin.cons (![ent j.1 j.2.2.1 j.2.1, ent j.1 j.2.1 j.2.2.1, ent j.1 j.2.2.1 j.2.1,
        ent j.1 j.2.1 j.2.2.1] j.2.2.2) fun _ => atr)
  let π : J → Equiv.Perm (Fin (e + 2)) := fun j => ![1, 1, Equiv.swap 0 1, Equiv.swap 0 1] j.2.2.2
  let Θ : V (e + 2) → V (e + 2) → V (e + 2) → V (e + 2) → ℂ :=
    fun ξ₁ η₁ ξ₂ η₂ => ∑ τ, chTwo (H τ) u ξ₁ η₁ ξ₂ η₂
  let ψ : (Fin (e + 2) → Fin (e + 2) → ℂ) → (Fin (e + 2) → Fin (e + 2) → ℂ) → ℂ := fun x y =>
    Θ (WithLp.toLp 2 (x 0)) (WithLp.toLp 2 (y 0)) (WithLp.toLp 2 (x 1)) (WithLp.toLp 2 (y 1)) *
      ∏ i : Fin e, atr (x i.succ.succ) (y i.succ.succ)
  have key : ∀ x y, ∑ j, ∏ k, f j k (x k) (y (π j k)) = ψ x y := by
    intro x y
    rw [show (∑ j : J, ∏ k, f j k (x k) (y (π j k))) = ∑ τ : T, ∑ p : Fin (μ τ) × Fin (μ τ) × Fin 4,
        ∏ k, f ⟨τ, p⟩ k (x k) (y (π ⟨τ, p⟩ k)) from Fintype.sum_sigma _]
    simp only [Fintype.sum_prod_type, ψ, Θ, chTwo, HermFrame.wedge, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have h01 : ∀ i : Fin e, (Equiv.swap (0 : Fin (e + 2)) 1) i.succ.succ = i.succ.succ := fun i =>
      Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (by
        intro h; have := congrArg Fin.val h; simp at this)
    simp [f, π, ent, c, Fin.sum_univ_four, Fin.prod_univ_succ, h01]
    ring
  have hsesq : ∀ j k, IsSesq (f j k) := by
    rintro ⟨τ, a, b, q⟩ k
    have hE : ∀ a b, IsSesq (ent τ a b) := fun a b => isSesq_entry (hS τ) a b
    refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun i => ?_) k) k
    · fin_cases q
      · exact isSesq_mul (hE a b) c
      · exact isSesq_mul (hE b a) c
      · simpa [f, neg_mul] using isSesq_mul (hE a b) (-c)
      · simpa [f, neg_mul] using isSesq_mul (hE b a) (-c)
    · fin_cases q
      · exact hE b a
      · exact hE a b
      · exact hE b a
      · exact hE a b
    · exact isSesq_trace hS
  have hb : ∀ x y : Fin (e + 2) → Fin (e + 2) → ℂ, ‖∑ j, ∏ k, f j k (x k) (y (π j k))‖ ≤
      (K1 * K2 ^ e) * ∏ k, (gnorm G (x k) * gnorm G (y k)) := by
    intro x y
    rw [key]
    have hΘ := wedge_le (e + 2) T μ (fun τ => H τ u) (fun τ => curv (H τ) u) G C₀ hP hG hC₀0 hCb
      (WithLp.toLp 2 (x 0)) (WithLp.toLp 2 (y 0)) (WithLp.toLp 2 (x 1)) (WithLp.toLp 2 (y 1))
    have hA : ∀ v w : Fin (e + 2) → ℂ, ‖atr v w‖ ≤ K2 * (gnorm G v * gnorm G w) := by
      intro v w
      rw [norm_neg, hK2d, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
      refine (trace_le _ (H τ u) _ (hP τ)).trans ?_
      have := hCb τ (WithLp.toLp 2 v) (WithLp.toLp 2 w)
      simp only [WithLp.ofLp_toLp] at this
      calc (μ τ : ℝ) * opNorm (H τ u) (H τ u) (curv (H τ) u (WithLp.toLp 2 v) (WithLp.toLp 2 w))
          ≤ (μ τ : ℝ) * (C₀ * gnorm G v * gnorm G w) := by gcongr
        _ = (μ τ : ℝ) * C₀ * (gnorm G v * gnorm G w) := by ring
    have hP2 : ∏ i : Fin e, ‖atr (x i.succ.succ) (y i.succ.succ)‖ ≤
        K2 ^ e * ∏ i : Fin e, (gnorm G (x i.succ.succ) * gnorm G (y i.succ.succ)) := by
      calc ∏ i : Fin e, ‖atr (x i.succ.succ) (y i.succ.succ)‖
          ≤ ∏ i : Fin e, (K2 * (gnorm G (x i.succ.succ) * gnorm G (y i.succ.succ))) :=
            Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => hA _ _
        _ = K2 ^ e * ∏ i : Fin e, (gnorm G (x i.succ.succ) * gnorm G (y i.succ.succ)) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    simp only [ψ, Θ, norm_mul, norm_prod]
    simp only [chTwo, WithLp.ofLp_toLp] at hΘ ⊢
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.succ_zero_eq_one]
    have n1 : 0 ≤ ∏ i : Fin e, (gnorm G (x i.succ.succ) * gnorm G (y i.succ.succ)) :=
      Finset.prod_nonneg fun i _ => mul_nonneg (gnorm_nonneg _ _) (gnorm_nonneg _ _)
    have n2 : 0 ≤ gnorm G (x 0) * gnorm G (y 0) * (gnorm G (x 1) * gnorm G (y 1)) := by
      have := gnorm_nonneg G (x 0); have := gnorm_nonneg G (y 0); have := gnorm_nonneg G (x 1)
      have := gnorm_nonneg G (y 1); positivity
    calc _ ≤ (K1 * (gnorm G (x 0) * gnorm G (y 0) * (gnorm G (x 1) * gnorm G (y 1)))) *
          (K2 ^ e * ∏ i : Fin e, (gnorm G (x i.succ.succ) * gnorm G (y i.succ.succ))) :=
          mul_le_mul hΘ hP2 (Finset.prod_nonneg fun i _ => norm_nonneg _) (mul_nonneg hK1 n2)
      _ = _ := by ring
  have h := GlobalTheory.T.determinant_expansion_bound (e + 2) J f π G (K1 * K2 ^ e) hsesq hG hb
  have e1 : ∀ s t : Equiv.Perm (Fin (e + 2)),
      (∑ τ, chTwo (H τ) u (bas _ (s 0)) (bas _ (t 0)) (bas _ (s 1)) (bas _ (t 1))) *
        ∏ i : Fin e, (Matrix.of fun a b => -∑ τ, (curv (H τ) u (bas _ a) (bas _ b)).trace)
          (s i.succ.succ) (t i.succ.succ) =
      ∑ j, ∏ k, f j k (Pi.single (s k) 1) (Pi.single (t (π j k)) 1) := by
    intro s t
    rw [key (fun k => Pi.single (s k) 1) (fun k => Pi.single (t k) 1)]
    simp only [ψ, Θ, atr, toLp_single, Matrix.of_apply]
  unfold secondChernDensity
  simp only [e1]
  rw [abs_div, abs_neg, abs_of_pos (pow_pos Real.pi_pos e), div_le_iff₀ (pow_pos Real.pi_pos e)]
  refine (Complex.abs_re_le_norm _).trans (h.trans (le_of_eq ?_))
  field_simp

end GlobalTheory.ChDens
