import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutDec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace

namespace Formalism.FourierDecayAlt.P.CutBP2

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants MeasureTheory
open scoped ENNReal

noncomputable section

def shP (P : M.Par) (u u' : ℕ → ℝ) : M.Par := ⟨P.k, P.r, P.T, P.T', u, u'⟩

section sh

variable {P : M.Par} {Wp Wq Wqp Wqm : Type}
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp]
  [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm]
  {up up' um um' : ℕ → ℝ}

def fpmSh (q : KB.Pl (shP P up up') Wp Wqp) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (A : B.Mat P.k P.r → (Wqp →L[ℂ] Wq)) (p₀ : ℕ) : B.Mat P.k P.r → (Wqp →L[ℂ] Wp) :=
  fun g => ((Gf P.k P.r q.T.base.z q.T.base.z' g ^ p₀ : ℝ) : ℂ) • (f g).comp (A g)

def NormAtSh (p : KB.Pl P Wp Wq) (pp : KB.Pl (shP P up up') Wp Wqp) (pm : KB.Pl (shP P um um') Wp Wqm)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Fp : B.Mat P.k P.r → (Wqp →L[ℂ] Wp))
    (Fm : B.Mat P.k P.r → (Wqm →L[ℂ] Wp)) (b : ℝ) (n₀ p₀ : ℕ) : Prop :=
  (∀ γ : C.LPt, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ →
    Ew p (fun _ => 1) f (P.r + 1) [] γ ≤ (3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀) *
      (Ew pp (fun _ => 1) Fp (P.r + 1) [] γ + Ew pm (fun _ => 1) Fm (P.r + 1) [] γ)) ∧
  (∀ c : Fin (P.r + 1) → ℂ, Ew pp (fun _ => 1) Fp (P.r + 1) [] (bigPt P.r c) ≤
      ‖(D.ptMatN (bigPt P.r c) (P.r + 1)).det‖ ^ (2 * (2 * p₀ + n₀)) * (Tq p)⁻¹ ^ n₀ *
        Ew p (fun _ => 1) f (P.r + 1) [] (bigPt P.r c)) ∧
  (∀ c : Fin (P.r + 1) → ℂ, Ew pm (fun _ => 1) Fm (P.r + 1) [] (bigPt P.r c) ≤
      ‖(D.ptMatN (bigPt P.r c) (P.r + 1)).det‖ ^ (2 * (2 * p₀ + n₀)) * (Tq p)⁻¹ ^ n₀ *
        Ew p (fun _ => 1) f (P.r + 1) [] (bigPt P.r c))

def AmapsSh (p : KB.Pl P Wp Wq) (pp : KB.Pl (shP P up up') Wp Wqp) (pm : KB.Pl (shP P um um') Wp Wqm)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Ap : B.Mat P.k P.r → (Wqp →L[ℂ] Wq))
    (Am : B.Mat P.k P.r → (Wqm →L[ℂ] Wq)) (ApPt : C.LPt → (Wqp →L[ℂ] Wq)) (AmPt : C.LPt → (Wqm →L[ℂ] Wq))
    (b : ℝ) (n₀ : ℕ) : Prop :=
  (∀ γ, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ →
      pp.V (fun g => (f g).comp (Ap g)) γ = (p.V f γ).comp (ApPt γ)) ∧
  (∀ γ, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ →
      pm.V (fun g => (f g).comp (Am g)) γ = (p.V f γ).comp (AmPt γ)) ∧
  (∀ γ, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ → ∀ v : Wq,
      ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ *
        (‖(ContinuousLinearMap.adjoint (ApPt γ)) v‖ ^ 2 + ‖(ContinuousLinearMap.adjoint (AmPt γ)) v‖ ^ 2)) ∧
  (∀ γ, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ → ‖ApPt γ‖ ^ 2 ≤ (Gp p γ / Tq p) ^ n₀) ∧
  (∀ γ, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ → ‖AmPt γ‖ ^ 2 ≤ (Gp p γ / Tq p) ^ n₀)

def NormAtShOfAmaps : Prop :=
  ∀ (P : M.Par) (Wp Wq Wqp Wqm : Type)
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp]
    [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm]
    (up up' um um' : ℕ → ℝ) (p : KB.Pl P Wp Wq) (pp : KB.Pl (shP P up up') Wp Wqp)
    (pm : KB.Pl (shP P um um') Wp Wqm) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Ap : B.Mat P.k P.r → (Wqp →L[ℂ] Wq)) (Am : B.Mat P.k P.r → (Wqm →L[ℂ] Wq))
    (ApPt : C.LPt → (Wqp →L[ℂ] Wq)) (AmPt : C.LPt → (Wqm →L[ℂ] Wq)) (b : ℝ) (n₀ p₀ : ℕ),
    pp.T.base.z = p.T.base.z → pp.T.base.z' = p.T.base.z' →
    pm.T.base.z = p.T.base.z → pm.T.base.z' = p.T.base.z' →
    AmapsSh p pp pm f Ap Am ApPt AmPt b n₀ →
    NormAtSh p pp pm f (fpmSh pp f Ap p₀) (fpmSh pm f Am p₀) b n₀ p₀

/- English proof (translation)
Unfold `Gp`. Rewrite using `[h]`. Both sides reduce to the same expression.
-/
theorem gp_eq {Wq' : Type} [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
    (p : KB.Pl P Wp Wq) (q : KB.Pl (shP P up up') Wp Wq') (h : TTp q = TTp p) (γ : C.LPt) : Gp q γ = Gp p γ := by
  unfold Gp; rw [h]; rfl

/- English proof (translation)
Establish `hT0 : 0 ≤ (Tq p)⁻¹ ^ n₀`. Establish `: 0 < Tq p` using `by linarith`. Check the signs of the components of the expression. Unfold `jN2 bigCellDetWeightedEnergyIntegral`. Rewrite using `[← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`.

Use `lintegral_mono fun c => ?_` and prove the remaining obligations. Rewrite using `[← ENNReal.ofReal_mul hT0]`. Use `ENNReal.ofReal_le_ofReal ((h c).trans (le_of_eq ?_))` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_sq_le_shifted {Wq' : Type} [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
    (p : KB.Pl P Wp Wq) (q : KB.Pl (shP P up up') Wp Wq') (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (F : B.Mat P.k P.r → (Wq' →L[ℂ] Wp)) (n₀ p₀ : ℕ) (hT : 1 ≤ Tq p)
    (h : ∀ c : Fin (P.r + 1) → ℂ, Ew q (fun _ => 1) F (P.r + 1) [] (bigPt P.r c) ≤
      ‖(D.ptMatN (bigPt P.r c) (P.r + 1)).det‖ ^ (2 * (2 * p₀ + n₀)) * (Tq p)⁻¹ ^ n₀ *
        Ew p (fun _ => 1) f (P.r + 1) [] (bigPt P.r c)) :
    jN2 q F ≤ ENNReal.ofReal ((Tq p)⁻¹ ^ n₀) * bigCellDetWeightedEnergyIntegral p f (2 * p₀ + n₀) := by
  have hT0 : 0 ≤ (Tq p)⁻¹ ^ n₀ := by
    have : 0 < Tq p := by linarith
    positivity
  unfold jN2 bigCellDetWeightedEnergyIntegral
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun c => ?_
  rw [← ENNReal.ofReal_mul hT0]
  refine ENNReal.ofReal_le_ofReal ((h c).trans (le_of_eq ?_))
  ring

end sh

/- English proof (translation)
Establish `hb0 : 0 < b` using `by linarith`. Establish `hb1 : 1 ≤ b` using `by linarith`. Establish `hN : ((2 * r + 2 : ℕ) : ℝ) = 2 * (r : ℝ) + 2` using `by push_cast; ring`. Establish `ha : ((2 * p₀ + n₀ : ℕ) : ℝ) = 2 * (p₀ : ℝ) + n₀` using `by push_cast; ring`. Rewrite using `[ha]`.

Rewrite `hΛb`, `hκb`, the goal using `[hN]`. Establish `hr : (0 : ℝ) ≤ r` using `Nat.cast_nonneg r`. Establish `hn' : (n₀ : ℝ) ≤ 30 * ((r : ℝ) + 1) ^ 2 + 6` using `by exact_mod_cast hn`. Establish `e1 : (3 * b) ^ (2 * n₀) ≤ b ^ (4 * (n₀ : ℝ))`. Establish `: b ^ (4 * (n₀ : ℝ)) = (b ^ 2) ^ (2 * n₀)`.

Rewrite using `[← pow_mul, ← Real.rpow_natCast]`. Use `push_cast`. Put the polynomial expressions in normal form. Rewrite using `[this]`. Conclude with `pow_le_pow_left₀ (by positivity) (by nlinarith) _`.

Establish `e2 : (2 : ℝ) ≤ b ^ (1 : ℝ)`. Rewrite using `[Real.rpow_one]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e3 : κ₀ ≤ b ^ (|Cκ| * (2 * (r : ℝ) + 2) ^ 2)` using `hκb.trans (Real.rpow_le_rpow_of_exponent_le hb1 (mul_le_mul_of_nonneg_right (le_abs_self Cκ) (sq_nonneg _)))`. Establish `e4 : (C₂ * Λ ^ 2) ^ (r + 1) ≤ b ^ (((m : ℝ) + 2 * CΛ * (2 * (r : ℝ) + 2)) * ((r : ℝ) + 1))`.

Establish `h1 : C₂ ≤ b ^ (m : ℝ)`. Rewrite using `[Real.rpow_natCast]`. Conclude with `hm.trans (pow_le_pow_left₀ (by norm_num) hb m)`. Establish `h2 : Λ ^ 2 ≤ b ^ (2 * CΛ * (2 * (r : ℝ) + 2))`. Establish `: b ^ (2 * CΛ * (2 * (r : ℝ) + 2)) = (b ^ (CΛ * (2 * (r : ℝ) + 2))) ^ 2`.

Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hb0.le]`. Use `push_cast`. Put the polynomial expressions in normal form. Rewrite using `[this]`. Conclude with `pow_le_pow_left₀ (by linarith) hΛb 2`.

Establish `h3 : C₂ * Λ ^ 2 ≤ b ^ ((m : ℝ) + 2 * CΛ * (2 * (r : ℝ) + 2))`. Rewrite using `[Real.rpow_add hb0]`. Conclude with `mul_le_mul h1 h2 (by positivity) (by positivity)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hb0.le]`.

Use `push_cast`. Put the polynomial expressions in normal form. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.rpow_add hb0, Real.rpow_add hb0, Real.rpow_add hb0, Real.rpow_add hb0]`. Use `_ ≤ _ := by`.

Apply `Real.rpow_le_rpow_of_exponent_le hb1` to reduce the goal to its premises. Establish `hm0 : (0 : ℝ) ≤ m` using `Nat.cast_nonneg m`. Establish `hk0 : 0 ≤ |Cκ|` using `abs_nonneg Cκ`. Establish `hs : 1 ≤ (r : ℝ) + 1` using `by linarith`. Establish `hs2 : (r + 1 : ℝ) ≤ ((r : ℝ) + 1) ^ 2` using `by nlinarith`.

Establish `hs4 : ((r : ℝ) + 1) ^ 2 ≤ ((r : ℝ) + 1) ^ 4`. Establish `h22 : (1 : ℝ) ≤ ((r : ℝ) + 1) ^ 2` using `by linarith`. Establish `: ((r : ℝ) + 1) ^ 4 = ((r : ℝ) + 1) ^ 2 * ((r : ℝ) + 1) ^ 2` using `by ring`. Rewrite using `[this]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hN2 : (2 * (r : ℝ) + 2) ^ 2 ≤ (2 * (r : ℝ) + 2) ^ 4` using `by linarith`. Establish `p1 : 4 * (n₀ : ℝ) + 1 ≤ 37 * (2 * (r : ℝ) + 2) ^ 4` using `by linarith`. Establish `p2 : |Cκ| * (2 * (r : ℝ) + 2) ^ 2 ≤ |Cκ| * (2 * (r : ℝ) + 2) ^ 4` using `mul_le_mul_of_nonneg_left hN2 hk0`. Establish `p3 : ((m : ℝ) + 2 * CΛ * (2 * (r : ℝ) + 2)) * ((r : ℝ) + 1) ≤ ((m : ℝ) + 2 * CΛ) * (2 * (r : ℝ) + 2) ^ 4`. Establish `q1 : (m : ℝ) * ((r : ℝ) + 1) ≤ m * (2 * (r : ℝ) + 2) ^ 4`.

Apply `mul_le_mul_of_nonneg_left _ hm0` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Establish `q2 : CΛ * ((2 * (r : ℝ) + 2) * ((r : ℝ) + 1)) ≤ CΛ * (2 * (r : ℝ) + 2) ^ 4`. Apply `mul_le_mul_of_nonneg_left _ hCΛ` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hA : 2 * (p₀ : ℝ) + n₀ ≤ (3 * C₀ + 10) * (2 * (r : ℝ) + 2) ^ 2`. Establish `: C₀ * (2 * (r : ℝ) + 2) ≤ C₀ * (2 * (r : ℝ) + 2) ^ 2`. Apply `mul_le_mul_of_nonneg_left _ (by linarith)` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `p4 : 2 * C₃ * (2 * (r : ℝ) + 2) ^ 2 * (2 * (p₀ : ℝ) + n₀) ≤ 2 * C₃ * (3 * C₀ + 10) * (2 * (r : ℝ) + 2) ^ 4`. Use `mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ 2 * C₃ * (2 * (r : ℝ) + 2) ^ 2)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem pow_mul_le_pow_of_param_bounds (C₃ CΛ C₀ C₂ Cκ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀)
    (hC₂ : 0 < C₂) (m : ℕ) (hm : C₂ ≤ 3 ^ m) (r n₀ p₀ : ℕ) (b Λ κ₀ : ℝ) (hb : 3 ≤ b) (hΛ : 1 ≤ Λ)
    (hΛb : Λ ≤ b ^ (CΛ * ((2 * r + 2 : ℕ) : ℝ))) (hκ : 0 < κ₀)
    (hκb : κ₀ ≤ b ^ (Cκ * ((2 * r + 2 : ℕ) : ℝ) ^ 2)) (hn : n₀ ≤ 30 * (r + 1) ^ 2 + 6)
    (hp : (p₀ : ℝ) ≤ C₀ * (3 * ((r : ℝ) + 1)) + 1) :
    (3 * b) ^ (2 * n₀) * 2 * (κ₀ * (C₂ * Λ ^ 2) ^ (r + 1)) *
        b ^ (2 * C₃ * ((2 * r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ)) ≤
      b ^ ((37 + |Cκ| + m + 2 * CΛ + 2 * C₃ * (3 * C₀ + 10)) * ((2 * r + 2 : ℕ) : ℝ) ^ 4) := by
  have hb0 : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hN : ((2 * r + 2 : ℕ) : ℝ) = 2 * (r : ℝ) + 2 := by push_cast; ring
  have ha : ((2 * p₀ + n₀ : ℕ) : ℝ) = 2 * (p₀ : ℝ) + n₀ := by push_cast; ring
  rw [ha]
  rw [hN] at hΛb hκb ⊢
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hn' : (n₀ : ℝ) ≤ 30 * ((r : ℝ) + 1) ^ 2 + 6 := by exact_mod_cast hn
  have e1 : (3 * b) ^ (2 * n₀) ≤ b ^ (4 * (n₀ : ℝ)) := by
    have : b ^ (4 * (n₀ : ℝ)) = (b ^ 2) ^ (2 * n₀) := by
      rw [← pow_mul, ← Real.rpow_natCast]
      push_cast
      ring_nf
    rw [this]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) _
  have e2 : (2 : ℝ) ≤ b ^ (1 : ℝ) := by
    rw [Real.rpow_one]
    linarith
  have e3 : κ₀ ≤ b ^ (|Cκ| * (2 * (r : ℝ) + 2) ^ 2) :=
    hκb.trans (Real.rpow_le_rpow_of_exponent_le hb1
      (mul_le_mul_of_nonneg_right (le_abs_self Cκ) (sq_nonneg _)))
  have e4 : (C₂ * Λ ^ 2) ^ (r + 1) ≤ b ^ (((m : ℝ) + 2 * CΛ * (2 * (r : ℝ) + 2)) * ((r : ℝ) + 1)) := by
    have h1 : C₂ ≤ b ^ (m : ℝ) := by
      rw [Real.rpow_natCast]
      exact hm.trans (pow_le_pow_left₀ (by norm_num) hb m)
    have h2 : Λ ^ 2 ≤ b ^ (2 * CΛ * (2 * (r : ℝ) + 2)) := by
      have : b ^ (2 * CΛ * (2 * (r : ℝ) + 2)) = (b ^ (CΛ * (2 * (r : ℝ) + 2))) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le]
        push_cast
        ring_nf
      rw [this]
      exact pow_le_pow_left₀ (by linarith) hΛb 2
    have h3 : C₂ * Λ ^ 2 ≤ b ^ ((m : ℝ) + 2 * CΛ * (2 * (r : ℝ) + 2)) := by
      rw [Real.rpow_add hb0]
      exact mul_le_mul h1 h2 (by positivity) (by positivity)
    calc (C₂ * Λ ^ 2) ^ (r + 1) ≤ (b ^ ((m : ℝ) + 2 * CΛ * (2 * (r : ℝ) + 2))) ^ (r + 1) :=
          pow_le_pow_left₀ (by positivity) h3 _
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le]
        push_cast
        ring_nf
  calc (3 * b) ^ (2 * n₀) * 2 * (κ₀ * (C₂ * Λ ^ 2) ^ (r + 1)) *
        b ^ (2 * C₃ * (2 * (r : ℝ) + 2) ^ 2 * (2 * (p₀ : ℝ) + n₀))
      ≤ b ^ (4 * (n₀ : ℝ)) * b ^ (1 : ℝ) *
          (b ^ (|Cκ| * (2 * (r : ℝ) + 2) ^ 2) *
            b ^ (((m : ℝ) + 2 * CΛ * (2 * (r : ℝ) + 2)) * ((r : ℝ) + 1))) *
          b ^ (2 * C₃ * (2 * (r : ℝ) + 2) ^ 2 * (2 * (p₀ : ℝ) + n₀)) := by
        gcongr
    _ = b ^ (4 * (n₀ : ℝ) + 1 + (|Cκ| * (2 * (r : ℝ) + 2) ^ 2 +
          ((m : ℝ) + 2 * CΛ * (2 * (r : ℝ) + 2)) * ((r : ℝ) + 1)) +
          2 * C₃ * (2 * (r : ℝ) + 2) ^ 2 * (2 * (p₀ : ℝ) + n₀)) := by
        rw [Real.rpow_add hb0, Real.rpow_add hb0, Real.rpow_add hb0, Real.rpow_add hb0]
    _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le hb1
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        have hk0 : 0 ≤ |Cκ| := abs_nonneg Cκ
        have hs : 1 ≤ (r : ℝ) + 1 := by linarith
        have hs2 : (r + 1 : ℝ) ≤ ((r : ℝ) + 1) ^ 2 := by nlinarith
        have hs4 : ((r : ℝ) + 1) ^ 2 ≤ ((r : ℝ) + 1) ^ 4 := by
          have h22 : (1 : ℝ) ≤ ((r : ℝ) + 1) ^ 2 := by linarith
          have : ((r : ℝ) + 1) ^ 4 = ((r : ℝ) + 1) ^ 2 * ((r : ℝ) + 1) ^ 2 := by ring
          rw [this]
          nlinarith
        have hN2 : (2 * (r : ℝ) + 2) ^ 2 ≤ (2 * (r : ℝ) + 2) ^ 4 := by linarith
        have p1 : 4 * (n₀ : ℝ) + 1 ≤ 37 * (2 * (r : ℝ) + 2) ^ 4 := by linarith
        have p2 : |Cκ| * (2 * (r : ℝ) + 2) ^ 2 ≤ |Cκ| * (2 * (r : ℝ) + 2) ^ 4 :=
          mul_le_mul_of_nonneg_left hN2 hk0
        have p3 : ((m : ℝ) + 2 * CΛ * (2 * (r : ℝ) + 2)) * ((r : ℝ) + 1) ≤
            ((m : ℝ) + 2 * CΛ) * (2 * (r : ℝ) + 2) ^ 4 := by
          have q1 : (m : ℝ) * ((r : ℝ) + 1) ≤ m * (2 * (r : ℝ) + 2) ^ 4 := by
            apply mul_le_mul_of_nonneg_left _ hm0
            linarith
          have q2 : CΛ * ((2 * (r : ℝ) + 2) * ((r : ℝ) + 1)) ≤ CΛ * (2 * (r : ℝ) + 2) ^ 4 := by
            apply mul_le_mul_of_nonneg_left _ hCΛ
            linarith
          linarith
        have hA : 2 * (p₀ : ℝ) + n₀ ≤ (3 * C₀ + 10) * (2 * (r : ℝ) + 2) ^ 2 := by
          have : C₀ * (2 * (r : ℝ) + 2) ≤ C₀ * (2 * (r : ℝ) + 2) ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ (by linarith)
            linarith
          linarith
        have p4 : 2 * C₃ * (2 * (r : ℝ) + 2) ^ 2 * (2 * (p₀ : ℝ) + n₀) ≤
            2 * C₃ * (3 * C₀ + 10) * (2 * (r : ℝ) + 2) ^ 4 := by
          have := mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ 2 * C₃ * (2 * (r : ℝ) + 2) ^ 2)
          linarith
        linarith

/- English proof (translation)
Take `⟨m, hm⟩` from `pow_unbounded_of_one_lt C₂ (by norm_num : (1 : ℝ) < 3)`. Use `⟨37 + |Cκ| + m + 2 * CΛ + 2 * C₃ * (3 * C₀ + 10), ?_⟩` and prove the remaining obligations. Introduce `P Wp Wq Wqp Wqm _ _ _ _ _ _ _ _ _ _ _ _ up up' um um' p pp pm f Fp Fm b Λ κ₀ n₀ p₀ hb hΛ hΛb hκ hκb hT hn hp hpp hpm hNA hPp hPm hR`. Unfold `ThmBpAt`. Introduce `γ hγ hG`.

Establish `hGp : Gp pp γ = Gp p γ` using `gp_eq p pp hpp γ`. Establish `hGm : Gp pm γ = Gp p γ` using `gp_eq p pm hpm γ`. Establish `hb0 : 0 < b` using `by linarith`. Establish `hT0 : 0 < Tq p` using `by linarith`. Establish `hK : 0 ≤ κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1)` using `by positivity`.

Establish `hTn : 0 ≤ (Tq p)⁻¹ ^ n₀` using `by positivity`. Establish `hA : 0 ≤ (3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀)` using `by positivity`. Establish `hDN` using `hR (2 * p₀ + n₀) le_rfl`. Establish `hJp` using `(norm_sq_le_shifted p pp f Fp n₀ p₀ hT hNA.2.1).trans (mul_le_mul_right hDN _)`. Establish `hJm` using `(norm_sq_le_shifted p pm f Fm n₀ p₀ hT hNA.2.2).trans (mul_le_mul_right hDN _)`.

Establish `hEp` using `(hPp γ hγ (by rw [hGp]; exact hG)).trans (mul_le_mul_right hJp _)`. Establish `hEm` using `(hPm γ hγ (by rw [hGm]; exact hG)).trans (mul_le_mul_right hJm _)`. Establish `key` using `pow_mul_le_pow_of_param_bounds C₃ CΛ C₀ C₂ Cκ hC₃ hCΛ hC₀ hC₂ m hm.le P.r n₀ p₀ b Λ κ₀ hb hΛ hΛb hκ hκb hn hp`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ENNReal.ofReal_mul hA]`.

Use `gcongr`. Conclude with `ENNReal.ofReal_add_le`. Use `_ ≤ ENNReal.ofReal ((3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀)) * (ENNReal.ofReal (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1)) * (ENNReal.ofReal ((Tq p)⁻¹ ^ n₀) * (ENNReal.ofReal (b ^ (2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ))) * jN2 p f)) + ENNRea …`. Conclude with `hEp`. Conclude with `hEm`.

Use `_ = ENNReal.ofReal ((3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀) * (2 * (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1) * ((Tq p)⁻¹ ^ n₀ * b ^ (2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ)))))) * jN2 p f := by conv_rhs =>`. Rewrite using `[ENNReal.ofReal_mul hA, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_mul hK, ENNReal.ofReal_mul hTn, ENNReal.ofReal_ofNat]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ ENNReal.ofReal (b ^ ((37 + |Cκ| + m + 2 * CΛ + 2 * C₃ * (3 * C₀ + 10)) * ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) * (Gp p γ)⁻¹ ^ (2 * p₀ + n₀)) * jN2 p f := by`. Use `mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _` and prove the remaining obligations.

Establish `hx : (Tq p / Gp p γ) ^ n₀ * (Tq p)⁻¹ ^ n₀ = (Gp p γ)⁻¹ ^ n₀`. Rewrite using `[← mul_pow, div_mul_eq_mul_div, mul_inv_cancel₀ hT0.ne', one_div]`. Establish `e : (3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀) * (2 * (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1) * ((Tq p)⁻¹ ^ n₀ * b ^ (2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ))))) = ((3 * b) ^ (2 * n₀) * 2 * (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1)) * b ^ (2 * C₃ * ((2 * …`. Rewrite using `[pow_add (Gp p γ)⁻¹ (2 * p₀) n₀, ← hx]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `mul_le_mul_of_nonneg_right key (by positivity)`.
-/
theorem thmBpOfPartsSh (C₃ CΛ C₀ C₂ Cκ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀) (hC₂ : 0 < C₂) :
    ∃ C₄ : ℝ, ∀ (P : M.Par) (Wp Wq Wqp Wqm : Type)
      [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
      [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
      [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp]
      [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm]
      (up up' um um' : ℕ → ℝ) (p : KB.Pl P Wp Wq) (pp : KB.Pl (shP P up up') Wp Wqp)
      (pm : KB.Pl (shP P um um') Wp Wqm) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
      (Fp : B.Mat P.k P.r → (Wqp →L[ℂ] Wp)) (Fm : B.Mat P.k P.r → (Wqm →L[ℂ] Wp)) (b Λ κ₀ : ℝ) (n₀ p₀ : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 0 < κ₀ →
      κ₀ ≤ b ^ (Cκ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2) → 1 ≤ Tq p →
      n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      TTp pp = TTp p → TTp pm = TTp p →
      NormAtSh p pp pm f Fp Fm b n₀ p₀ → PtBound pp Fp (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1)) →
      PtBound pm Fm (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1)) → RegularityBoundBigCell p f b C₃ (2 * p₀ + n₀) → ThmBpAt p f b C₄ n₀ p₀ := by
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt C₂ (by norm_num : (1 : ℝ) < 3)
  refine ⟨37 + |Cκ| + m + 2 * CΛ + 2 * C₃ * (3 * C₀ + 10), ?_⟩
  intro P Wp Wq Wqp Wqm _ _ _ _ _ _ _ _ _ _ _ _ up up' um um' p pp pm f Fp Fm b Λ κ₀ n₀ p₀
    hb hΛ hΛb hκ hκb hT hn hp hpp hpm hNA hPp hPm hR
  unfold ThmBpAt
  intro γ hγ hG
  have hGp : Gp pp γ = Gp p γ := gp_eq p pp hpp γ
  have hGm : Gp pm γ = Gp p γ := gp_eq p pm hpm γ
  have hb0 : 0 < b := by linarith
  have hT0 : 0 < Tq p := by linarith
  have hK : 0 ≤ κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1) := by positivity
  have hTn : 0 ≤ (Tq p)⁻¹ ^ n₀ := by positivity
  have hA : 0 ≤ (3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀) := by positivity
  have hDN := hR (2 * p₀ + n₀) le_rfl
  have hJp := (norm_sq_le_shifted p pp f Fp n₀ p₀ hT hNA.2.1).trans (mul_le_mul_right hDN _)
  have hJm := (norm_sq_le_shifted p pm f Fm n₀ p₀ hT hNA.2.2).trans (mul_le_mul_right hDN _)
  have hEp := (hPp γ hγ (by rw [hGp]; exact hG)).trans (mul_le_mul_right hJp _)
  have hEm := (hPm γ hγ (by rw [hGm]; exact hG)).trans (mul_le_mul_right hJm _)
  have key := pow_mul_le_pow_of_param_bounds C₃ CΛ C₀ C₂ Cκ hC₃ hCΛ hC₀ hC₂ m hm.le P.r n₀ p₀ b Λ κ₀ hb hΛ hΛb hκ hκb hn hp
  calc ENNReal.ofReal (Ew p (fun _ => 1) f (P.r + 1) [] γ)
      ≤ ENNReal.ofReal ((3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀) *
          (Ew pp (fun _ => 1) Fp (P.r + 1) [] γ + Ew pm (fun _ => 1) Fm (P.r + 1) [] γ)) :=
        ENNReal.ofReal_le_ofReal (hNA.1 γ hγ hG)
    _ ≤ ENNReal.ofReal ((3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀)) *
          (ENNReal.ofReal (Ew pp (fun _ => 1) Fp (P.r + 1) [] γ) +
            ENNReal.ofReal (Ew pm (fun _ => 1) Fm (P.r + 1) [] γ)) := by
        rw [ENNReal.ofReal_mul hA]
        gcongr
        exact ENNReal.ofReal_add_le
    _ ≤ ENNReal.ofReal ((3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀)) *
          (ENNReal.ofReal (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1)) *
              (ENNReal.ofReal ((Tq p)⁻¹ ^ n₀) *
                (ENNReal.ofReal (b ^ (2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ))) *
                  jN2 p f)) +
            ENNReal.ofReal (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1)) *
              (ENNReal.ofReal ((Tq p)⁻¹ ^ n₀) *
                (ENNReal.ofReal (b ^ (2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ))) *
                  jN2 p f))) := by
        gcongr
        · exact hEp
        · exact hEm
    _ = ENNReal.ofReal ((3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀) *
          (2 * (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1) * ((Tq p)⁻¹ ^ n₀ *
            b ^ (2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ)))))) * jN2 p f := by
        conv_rhs =>
          rw [ENNReal.ofReal_mul hA, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_mul hK,
            ENNReal.ofReal_mul hTn, ENNReal.ofReal_ofNat]
        ring
    _ ≤ ENNReal.ofReal (b ^ ((37 + |Cκ| + m + 2 * CΛ + 2 * C₃ * (3 * C₀ + 10)) *
          ((2 * P.r + 2 : ℕ) : ℝ) ^ 4) * (Gp p γ)⁻¹ ^ (2 * p₀ + n₀)) * jN2 p f := by
        refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
        have hx : (Tq p / Gp p γ) ^ n₀ * (Tq p)⁻¹ ^ n₀ = (Gp p γ)⁻¹ ^ n₀ := by
          rw [← mul_pow, div_mul_eq_mul_div, mul_inv_cancel₀ hT0.ne', one_div]
        have e : (3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ * (Gp p γ)⁻¹ ^ (2 * p₀) *
            (2 * (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1) * ((Tq p)⁻¹ ^ n₀ *
              b ^ (2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ))))) =
            ((3 * b) ^ (2 * n₀) * 2 * (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1)) *
              b ^ (2 * C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ))) *
              (Gp p γ)⁻¹ ^ (2 * p₀ + n₀) := by
          rw [pow_add (Gp p γ)⁻¹ (2 * p₀) n₀, ← hx]
          ring
        rw [e]
        exact mul_le_mul_of_nonneg_right key (by positivity)

section dec

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def EigDec (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (n : ℕ)
    (h : Fin n → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) : Prop :=
  (∀ i, jN2 p (h i) ≤ jN2 p f) ∧
    ∀ γ : C.LPt, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ → p.V f γ = ∑ i, p.V (h i) γ

end dec

end

end Formalism.FourierDecayAlt.P.CutBP2
