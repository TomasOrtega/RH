import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.SchurEigenProjections.BigProjP
import Development.WeilBound.CoreStatements.BranchingTraces.HilbertSchmidtTraces.IntegralGermIndependentOfSystem
import Development.WeilBound.CoreStatements.BranchingTraces.HilbertSchmidtTraces.UnitaryMatrixCoefficientDecay
import Development.WeilBound.CoreStatements.BranchingTraces.HilbertSchmidtTraces.Imports
import Development.WeilBound.CoreStatements.BranchingTraces.HilbertSchmidtTraces.ColSq

noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants Formalism.L2.Theta GlobalTheory.SmVec GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.PairingAnalysis
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgHe.A.Pf

/- English proof (translation)
Establish `hip : ∀ (g : Γ) (a b : A), ⟪σ g a, σ g b⟫_ℂ = ⟪a, b⟫_ℂ`. Introduce `g a b`. Set `L : A →ₗᵢ[ℂ] A` to `{ toLinearMap := (σ g).toLinearMap, norm_map' := hσ.norm g }`. Conclude with `L.inner_map_map a b`. Establish `key : ∀ g : Γ, star ⟪w, σ (g⁻¹ * x) w⟫_ℂ = ⟪σ x w, σ g w⟫_ℂ`.

Introduce `g`. Establish `h1 : σ (g⁻¹ * x) w = σ g⁻¹ (σ x w)`. Rewrite using `[hσ.mul]`. Both sides reduce to the same expression. Establish `h2 : σ g (σ g⁻¹ (σ x w)) = σ x w`.

Rewrite using `[← ContinuousLinearMap.mul_apply, ← hσ.mul, mul_inv_cancel, hσ.one]`. Both sides reduce to the same expression. Rewrite using `[h1, ← hip g, h2, ← starRingEnd_apply, inner_conj_symm]`. Establish `hint` using `(hd.2 w (σ x w) w w).2`. Establish `hww : ⟪w, w⟫_ℂ = 1`.

Rewrite using `[inner_self_eq_norm_sq_to_K, hw]`. Simplify using the standard rewrite rules. Establish `hc : ⟪σ x w, w⟫_ℂ = star ⟪w, σ x w⟫_ℂ`. Rewrite using `[← starRingEnd_apply, inner_conj_symm]`. Combine the equalities or inequalities in the displayed calculation.

Use `congr 1`. Use function extensionality and compare the values at `g`. Rewrite using `[key g, mul_comm]`. Use `_ = ⟪w, w⟫_ℂ * ⟪σ x w, w⟫_ℂ / (d : ℂ) := hint`. Use `_ = ((d⁻¹ : ℝ) : ℂ) * star ⟪w, σ x w⟫_ℂ := by`.

Rewrite using `[hww, hc]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem conv_of {Γ : Type} [Group Γ] [TopologicalSpace Γ] [MeasurableSpace Γ] (ν : Measure Γ) {A : Type}
    [NormedAddCommGroup A] [InnerProductSpace ℂ A] (σ : Γ → (A →L[ℂ] A)) (d : ℝ) (hσ : IsU σ) (hd : IsFd ν σ d)
    (w : A) (hw : ‖w‖ = 1) (x : Γ) :
    ∫ g, star ⟪w, σ g w⟫_ℂ * star ⟪w, σ (g⁻¹ * x) w⟫_ℂ ∂ν = ((d⁻¹ : ℝ) : ℂ) * star ⟪w, σ x w⟫_ℂ := by
  have hip : ∀ (g : Γ) (a b : A), ⟪σ g a, σ g b⟫_ℂ = ⟪a, b⟫_ℂ := by
    intro g a b
    let L : A →ₗᵢ[ℂ] A := { toLinearMap := (σ g).toLinearMap, norm_map' := hσ.norm g }
    exact L.inner_map_map a b
  have key : ∀ g : Γ, star ⟪w, σ (g⁻¹ * x) w⟫_ℂ = ⟪σ x w, σ g w⟫_ℂ := by
    intro g
    have h1 : σ (g⁻¹ * x) w = σ g⁻¹ (σ x w) := by
      rw [hσ.mul]; rfl
    have h2 : σ g (σ g⁻¹ (σ x w)) = σ x w := by
      rw [← ContinuousLinearMap.mul_apply, ← hσ.mul, mul_inv_cancel, hσ.one]; rfl
    rw [h1, ← hip g, h2, ← starRingEnd_apply, inner_conj_symm]
  have hint := (hd.2 w (σ x w) w w).2
  have hww : ⟪w, w⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hw]; simp
  have hc : ⟪σ x w, w⟫_ℂ = star ⟪w, σ x w⟫_ℂ := by
    rw [← starRingEnd_apply, inner_conj_symm]
  calc ∫ g, star ⟪w, σ g w⟫_ℂ * star ⟪w, σ (g⁻¹ * x) w⟫_ℂ ∂ν
        = ∫ g, ⟪σ x w, σ g w⟫_ℂ * star ⟪w, σ g w⟫_ℂ ∂ν := by
          congr 1; funext g; rw [key g, mul_comm]
    _ = ⟪w, w⟫_ℂ * ⟪σ x w, w⟫_ℂ / (d : ℂ) := hint
    _ = ((d⁻¹ : ℝ) : ℂ) * star ⟪w, σ x w⟫_ℂ := by
          rw [hww, hc]; push_cast; ring

/- English proof (translation)
Use `⟨inv_pos.mpr hK.1, fun v w v' w' => ?_⟩` and prove the remaining obligations. Take `⟨hi, he⟩` from `hK.2 v w v' w'`. Use `⟨hi, ?_⟩` and prove the remaining obligations. Establish `e2 : ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / ((κ⁻¹ : ℝ) : ℂ) = (κ : ℂ) * (⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ)` using `by push_cast; rw [div_inv_eq_mul]; ring`. Rewrite using `[e2]`.

Conclude with `he`.
-/
theorem isFd_of_schurK {m : ℕ} {ε : Fin m → Bool} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    {σ : Matrix (Fin m) (Fin m) ℂ → (K →L[ℂ] K)} {ν : Measure (UJ ε)} {κ : ℝ} (hK : PositivityTheory.RgHe.SchurK ε σ ν κ) :
    IsFd ν (onU ε σ) κ⁻¹ := by
  refine ⟨inv_pos.mpr hK.1, fun v w v' w' => ?_⟩
  obtain ⟨hi, he⟩ := hK.2 v w v' w'
  refine ⟨hi, ?_⟩
  have e2 : ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / ((κ⁻¹ : ℝ) : ℂ) = (κ : ℂ) * (⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ) := by
    push_cast; rw [div_inv_eq_mul]; ring
  rw [e2]
  exact he

set_option maxHeartbeats 1600000 in
/- English proof (translation)
Introduce `hM hA`. Take `⟨hVol, hDec, hIntR, hHInt, hDUp, hLip⟩` from `hA`. Introduce `n ε lam ε' mu B e H H' _ _ _ _ _ _ π σ ν hν hF hP hDSπ hDSσ`. Introduce `κ hK w hw hw1 hwi i η hiso hint hη hηi hηint v hv hv1`. Take `⟨hE1, hE2, hE3, hE4⟩` from `hem`.

Take `⟨ι, hιum, hιstd, -⟩` from `hE1 ε ε' e hF`. Establish `hn2 : 2 ≤ n` using `hP.two`. Establish `hB : 100 * ((n : ℝ) + 1) ^ 3 ≤ B`. Take `⟨a, ha⟩` from `hP.neg`. Establish `hne : ε a ≠ ε (zi e)` using `by rw [ha, hF.1]; simp`.

Establish `h1` using `hP.gap a (zi e) hne`. Establish `h2` using `hP.bd a`. Establish `h3` using `hP.bd (zi e)`. Establish `h4 : |lam a - lam (zi e)| ≤ |lam a| + |lam (zi e)|` using `abs_sub _ _`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hn3 : (3 : ℝ) ≤ (n : ℝ) + 1`. Establish `: (2 : ℝ) ≤ n` using `by exact_mod_cast hn2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h27 : (3 : ℝ) ^ 3 ≤ ((n : ℝ) + 1) ^ 3` using `pow_le_pow_left₀ (by norm_num) hn3 3`. Establish `hB2 : (2 : ℝ) ≤ B` using `by linarith`.

Use `set x : ℝ := 8 * ((n : ℝ) + 1) * B with hx`. Establish `hx16 : (16 : ℝ) ≤ x` using `by rw [hx]; nlinarith`. Establish `hxn : ((n : ℝ) + 1) ≤ x` using `by rw [hx]; nlinarith`. Establish `hx0 : 0 < x` using `by linarith`. Establish `hUπ : IsU (onU ε π)` using `hE3 ε π hDSπ.2.2.1`.

Establish `hUσ : IsU (onU ε' σ)` using `hE3 ε' σ hDSσ.2.2.1`. Use `haveI hμ : (muG ε).IsHaarMeasure := by unfold muG; infer_instance`. Take `⟨-, ⟨dπ, hFdeg, hFd⟩, -⟩` from `hE4 ε lam π (muG ε) hμ hP.hc hDSπ`. Establish `hFdσ : IsFd ν (onU ε' σ) κ⁻¹` using `isFd_of_schurK hK`. Establish `hIso : IsIsoMap (onU ε' σ) (res ι π) i`.

Use `⟨fun h y => ?_, hiso⟩` and prove the remaining obligations. Use `show i (σ (um h) y) = π (umat (ι h)) (i y)`. Rewrite using `[hιum]`. Conclude with `hint h y`. Establish `hIt : Intertw ε' e π σ (ContinuousLinearMap.adjoint i)`.

Use `⟨?_, fun h y => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearIsometryEquiv.norm_map]`. Conclude with `ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun z => by rw [hiso, one_mul])`. Apply `ext_inner_left ℂ` to reduce the goal to its premises. Introduce `z`.

Rewrite using `[ContinuousLinearMap.adjoint_inner_right]`. Establish `a1` using `UnitaryDecomposition.X4.isU_adj hUπ (ι h) (i z) y`. Establish `a2` using `UnitaryDecomposition.X4.isU_adj hUσ h z (ContinuousLinearMap.adjoint i y)`. Establish `e1 : onU ε π (ι h) = π (emb e (um h))` using `by show π (umat (ι h)) = _`. Rewrite using `[hιum]`.

Establish `e2 : onU ε π (ι h)⁻¹ (i z) = i (σ (um h⁻¹) z)`. Rewrite using `[← map_inv]`. Use `show π (umat (ι h⁻¹)) (i z) = _`. Rewrite using `[hιum, hint]`. Rewrite `a1` using `[e1]`.

Rewrite using `[a1, e2, ← ContinuousLinearMap.adjoint_inner_right]`. Conclude with `a2.symm`. Establish `hconv : ∀ y : UJ ε', ∫ h, starRingEnd ℂ ⟪w, σ (um h) w⟫_ℂ * starRingEnd ℂ ⟪w, σ (um (h⁻¹ * y)) w⟫_ℂ ∂ν = (κ : ℂ) * starRingEnd ℂ ⟪w, σ (um y) w⟫_ℂ`. Introduce `y`. Use `conv_of ν (onU ε' σ) κ⁻¹ hUσ hFdσ w hw1 y` as an intermediate fact.

Rewrite `this` using `[inv_inv]`. Conclude with `this`. Establish `hmom` using `hM n ε lam ε' mu B e H H' π σ ν hν hF hP hDSπ hDSσ (ContinuousLinearMap.adjoint i) w κ hIt hw1 (by rw [ContinuousLinearMap.adjoint_adjoint, hiso, hw1]) hK.1 hwi hconv ⟨η, hη, by rw [ContinuousLinearMap.adjoint_adjoint]; exact hηi, by rw [ContinuousLinearMap.adjoint_adjoint]; exac …`. Rewrite `hmom` using `[ContinuousLinearMap.adjoint_adjoint]`. Establish `hone : σ (um (1 : UJ ε')) = 1` using `hUσ.one`.

Establish `hhs1 : hs (um (1 : UJ ε')) ≤ (n : ℝ)`. Establish `h1 : um (1 : UJ ε') = 1` using `rfl`. Rewrite using `[h1]`. Simplify using `only [hs, Matrix.one_apply]`. Establish `h2 : ∀ i j : Fin n, ‖(if i = j then (1 : ℂ) else 0)‖ ^ 2 = if i = j then (1 : ℝ) else 0`.

Apply the tactic sequence `intro i j; split_ifs <;> simp`. Simplify using `only [h2, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]`. Conclude with `le_rfl`. Establish `hgap' : GapAtLeast ε' mu (200 * ((n + 1 : ℕ) : ℝ) ^ 3)` using `by push_cast; exact hP.gap'`. Establish `hdec : ∀ g : UJ ε', ‖⟪w, σ (um g) w⟫_ℂ‖ ≤ Real.exp (6 * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.log n + 12 * ((n + 1 : ℕ) : ℝ) ^ 2) * (n : ℝ) ^ (12 * (n + 1) ^ 2) * hs (um g) ^ (-(6 * ((n + 1 : ℕ) : ℝ) ^ 2))`.

Introduce `g`. Use `hDec n (n + 1) ε' mu H' σ (by omega) (by omega) hP.hc' hDSσ hgap' w hw hw1 1 n hhs1 g` as an intermediate fact. Rewrite `this` using `[hone]`. Simplify `this` using `only [ContinuousLinearMap.one_apply]`. Establish `hC` using `UnitaryDecomposition.X4.num_C (n := n) (x := x) (by omega) (by linarith) (by linarith)`.

Establish `hsnn : ∀ g : UJ ε', 0 ≤ hs (um g)` using `fun g => Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))`. Establish `hφb : ∀ g : UJ ε', ‖⟪w, σ (um g) w⟫_ℂ * starRingEnd ℂ ⟪w, σ (um g) w⟫_ℂ‖ ≤ (x ^ (30 * (n + 1) ^ 2)) ^ 2 * hs (um g) ^ (-(2 * (6 * ((n + 1 : ℕ) : ℝ) ^ 2)))`. Introduce `g`. Establish `hc` using `le_trans (hdec g) (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (hsnn g) _))`. Establish `hn0` using `norm_nonneg ⟪w, σ (um g) w⟫_ℂ`.

Establish `e1 : ‖⟪w, σ (um g) w⟫_ℂ * starRingEnd ℂ ⟪w, σ (um g) w⟫_ℂ‖ = ‖⟪w, σ (um g) w⟫_ℂ‖ ^ 2`. Rewrite using `[norm_mul, RCLike.norm_conj, sq]`. Establish `e2 : hs (um g) ^ (-(2 * (6 * ((n + 1 : ℕ) : ℝ) ^ 2))) = (hs (um g) ^ (-(6 * ((n + 1 : ℕ) : ℝ) ^ 2))) ^ 2`. Rewrite using `[← Real.rpow_mul_natCast (hsnn g)]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2, ← mul_pow]`. Conclude with `pow_le_pow_left₀ hn0 hc 2`. Establish `hc1 : Continuous fun g : UJ ε' => ⟪w, σ (um g) w⟫_ℂ` using `continuous_const.inner (by exact hUσ.cont w : Continuous fun g : UJ ε' => σ (um g) w)`.

Establish `hφc : Continuous fun g : UJ ε' => ⟪w, σ (um g) w⟫_ℂ * starRingEnd ℂ ⟪w, σ (um g) w⟫_ℂ` using `hc1.mul (Complex.continuous_conj.comp hc1)`. Establish `ha : ((n : ℕ) : ℝ) ^ 2 + 1 ≤ 2 * (6 * ((n + 1 : ℕ) : ℝ) ^ 2)` using `by push_cast; nlinarith`. Take `⟨-, hIφ⟩` from `hIntR n ε' ν hν (by omega) _ _ _ hφc ha hφb`. Establish `hww : ⟪w, w⟫_ℂ = 1`. Rewrite using `[inner_self_eq_norm_sq_to_K, hw1]`.

Simplify using the standard rewrite rules. Establish `hκφ : κ ≤ ∫ g, ‖⟪w, σ (um g) w⟫_ℂ * starRingEnd ℂ ⟪w, σ (um g) w⟫_ℂ‖ ∂ν`. Establish `h` using `(hK.2 w w w w).2`. Rewrite `h` using `[hww, mul_one, mul_one]`. Establish `h2 : ∫ g, ⟪w, σ (um g) w⟫_ℂ * starRingEnd ℂ ⟪w, σ (um g) w⟫_ℂ ∂ν = (κ : ℂ)` using `h`.

Establish `h3` using `norm_integral_le_integral_norm (μ := ν) (fun g : UJ ε' => ⟪w, σ (um g) w⟫_ℂ * starRingEnd ℂ ⟪w, σ (um g) w⟫_ℂ)`. Rewrite `h3` using `[h2, Complex.norm_real, Real.norm_eq_abs]`. Conclude with `le_trans (le_abs_self κ) h3`. Establish `hD : 1 / κ⁻¹ ≤ x ^ (67 * (n + 1) ^ 2) * ν.real (ball ε' 1)`. Rewrite using `[one_div, inv_inv]`.

Establish `hnd` using `UnitaryDecomposition.X4.num_D (n := n) (x := x) hx16 (by linarith)`. Establish `hνr : 0 ≤ ν.real (ball ε' 1)` using `measureReal_nonneg`. Combine the equalities or inequalities in the displayed calculation. Establish `hY` using `UnitaryDecomposition.X4.num_Y (N := n + 1) (x := x) (by omega) (by linarith) (by push_cast; linarith)`. Establish `hB1 : 0 < B + 1` using `by linarith`.

Establish `hδ : 0 < ((100 * ((n + 1 : ℕ) : ℝ) * (B + 1)) ^ 2)⁻¹` using `by positivity`. Establish `hδ2 : ((100 * ((n + 1 : ℕ) : ℝ) * (B + 1)) ^ 2)⁻¹ ≤ 2`. Establish `h1 : (1 : ℝ) ≤ (100 * ((n + 1 : ℕ) : ℝ) * (B + 1)) ^ 2`. Apply `one_le_pow₀` to reduce the goal to its premises. Use `push_cast`.

Use the polynomial consequences of the given equalities and inequalities. Use `inv_le_one_of_one_le₀ h1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hV` using `UnitaryDecomposition.X4.num_V (N := n + 1) (B := B) (x := x) (by omega) hB2 (by rw [hx]; push_cast; ring)`. Establish `hgap100 : GapAtLeast ε lam (100 * ((n + 1 : ℕ) : ℝ) ^ 3)`.

Introduce `a b hab`. Use `le_trans ?_ (hP.gap a b hab)` and prove the remaining obligations. Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities. Establish `hDU` using `hDUp (n + 1) ε lam B H π (muG ε) dπ hμ (by omega) hP.hc hDSπ hP.bd hgap100 hFdeg`.

Establish `hvol : ENNReal.ofReal dπ * muG ε {g : UJ ε | hs (umat g) ≤ 64 * ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 2 * x ^ (8 * (n + 1))) ^ 2} ≤ ENNReal.ofReal (4 * x ^ (24 * (n + 1) ^ 3))`. Establish `hsub : {g : UJ ε | hs (umat g) ≤ 64 * ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 2 * x ^ (8 * (n + 1))) ^ 2} ⊆ {g : UJ ε | hs (um g) ≤ (x ^ (10 * (n + 1))) ^ 2}`. Introduce `g hg`. Simplify using `only [Set.mem_setOf_eq] at hg ⊢`. Rewrite using `[← pow_mul]`.

Establish `e : 10 * (n + 1) * 2 = 20 * (n + 1)` using `by ring`. Rewrite using `[e]`. Conclude with `le_trans hg hY`. Establish `h1` using `measure_mono (μ := muG ε) hsub`. Establish `h2` using `hVol (n + 1) ε (muG ε) hμ (by omega) _ (x ^ (10 * (n + 1))) hδ hδ2 (by positivity)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, mul_comm]`. Establish `hY1 : (1 : ℝ) ≤ 2 * x ^ (8 * (n + 1))`. Establish `: (1 : ℝ) ≤ x ^ (8 * (n + 1))` using `one_le_pow₀ (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hK0 : (0 : ℝ) < 4 * x ^ (24 * (n + 1) ^ 3)` using `by positivity`. Establish `hmomG : ∫⁻ g : UJ ε, ENNReal.ofReal (GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq (umat g⁻¹ *ᵥ Pi.single (zi e) 1) * ‖⟪i w, π (umat g) v⟫_ℂ‖ ^ 2) ∂muG ε ≤ ENNReal.ofReal (2 * x ^ (8 * (n + 1)) / 2) * ∫⁻ g : UJ ε, ENNReal.ofReal (‖⟪i w, π (umat g) v⟫_ℂ‖ ^ 2) ∂muG ε`. Establish `e1 : ∀ g : UJ ε, GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq (umat g⁻¹ *ᵥ Pi.single (zi e) 1) = colSq (um g⁻¹) (zi e)` using `fun g => hE2 _ _`. Establish `e2 : 2 * x ^ (8 * (n + 1)) / 2 = x ^ (8 * (n + 1))` using `by ring`. Repeatedly rewrite using `[e1, e2]`.

Conclude with `hmom`. Take `⟨g₀, hg1, hg2⟩` from `hg0 ι (Pi.single (zi e) 1) hιstd π σ (muG ε) ν dπ κ⁻¹ hUπ hUσ hFd hFdσ i hIso v w hv1 hw1 (2 * x ^ (8 * (n + 1))) (4 * x ^ (24 * (n + 1) ^ 3)) (x ^ (67 * (n + 1) ^ 2)) hY1 hK0 hmomG hvol hD`. Use `⟨g₀, le_trans hg1 hY, ?_⟩` and prove the remaining obligations. Establish `hg2' : 1 ≤ 4 * x ^ (67 * (n + 1) ^ 2) * (4 * x ^ (24 * (n + 1) ^ 3)) * ‖ContinuousLinearMap.adjoint i (π (um g₀) v)‖ ^ 2` using `hg2`. Establish `ht0 : 0 ≤ ‖ContinuousLinearMap.adjoint i (π (um g₀) v)‖` using `norm_nonneg _`.

Establish `hM0 : 0 < x ^ (100 * (n + 1) ^ 3)` using `pow_pos hx0 _`. Establish `elog : 100 * ((n : ℝ) + 1) ^ 3 * Real.log x = Real.log (x ^ (100 * (n + 1) ^ 3))`. Rewrite using `[Real.log_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[elog, Real.exp_neg, Real.exp_log hM0]`. Establish `hA0 : 0 ≤ x ^ (67 * (n + 1) ^ 2)` using `pow_nonneg hx0.le _`. Establish `hC0 : 0 ≤ x ^ (24 * (n + 1) ^ 3)` using `pow_nonneg hx0.le _`. Establish `hnat : 1 + 67 * (n + 1) ^ 2 + 24 * (n + 1) ^ 3 ≤ 100 * (n + 1) ^ 3 * 2`. Establish `h1 : (n + 1) ^ 2 ≤ (n + 1) ^ 3` using `Nat.pow_le_pow_right (by omega) (by norm_num)`.

Establish `h2 : 1 ≤ (n + 1) ^ 3` using `Nat.one_le_pow _ _ (by omega)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hbig : 16 * x ^ (67 * (n + 1) ^ 2) * x ^ (24 * (n + 1) ^ 3) ≤ (x ^ (100 * (n + 1) ^ 3)) ^ 2`. Rewrite using `[← pow_mul]`. Combine the equalities or inequalities in the displayed calculation.

Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `hsq : ‖ContinuousLinearMap.adjoint i (π (um g₀) v)‖ ^ 2 < ((x ^ (100 * (n + 1) ^ 3))⁻¹) ^ 2` using `pow_lt_pow_left₀ hlt ht0 (by norm_num)`. Establish `hp : 0 < 16 * x ^ (67 * (n + 1) ^ 2) * x ^ (24 * (n + 1) ^ 3)` using `mul_pos (mul_pos (by norm_num) (pow_pos hx0 _)) (pow_pos hx0 _)`. Establish `s1` using `mul_lt_mul_of_pos_left hsq hp`.

Establish `s2 : 16 * x ^ (67 * (n + 1) ^ 2) * x ^ (24 * (n + 1) ^ 3) * ((x ^ (100 * (n + 1) ^ 3))⁻¹) ^ 2 ≤ (x ^ (100 * (n + 1) ^ 3)) ^ 2 * ((x ^ (100 * (n + 1) ^ 3))⁻¹) ^ 2` using `mul_le_mul_of_nonneg_right hbig (sq_nonneg _)`. Establish `s3 : (x ^ (100 * (n + 1) ^ 3)) ^ 2 * ((x ^ (100 * (n + 1) ^ 3))⁻¹) ^ 2 = 1`. Rewrite using `[← mul_pow, mul_inv_cancel₀ hM0.ne', one_pow]`. Establish `s4 : 4 * x ^ (67 * (n + 1) ^ 2) * (4 * x ^ (24 * (n + 1) ^ 3)) * ‖ContinuousLinearMap.adjoint i (π (um g₀) v)‖ ^ 2 = 16 * x ^ (67 * (n + 1) ^ 2) * x ^ (24 * (n + 1) ^ 3) * ‖ContinuousLinearMap.adjoint i (π (um g₀) v)‖ ^ 2` using `by ring`. Rewrite `hg2'` using `[s4]`.

Conclude with `absurd (lt_of_le_of_lt hg2' (lt_of_lt_of_le s1 (s2.trans s3.le))) (lt_irrefl 1)`.
-/
theorem bigProjP_of (hg0 : PositivityTheory.UnitaryDecomposition.X4.IntegralGermIndependentOfSystem) (hem : PositivityTheory.UnitaryDecomposition.X4.EmbSt) : MomentP → Analysis → BigProjP := by
  intro hM hA
  obtain ⟨hVol, hDec, hIntR, hHInt, hDUp, hLip⟩ := hA
  intro n ε lam ε' mu B e H H' _ _ _ _ _ _ π σ ν hν hF hP hDSπ hDSσ
  intro κ hK w hw hw1 hwi i η hiso hint hη hηi hηint v hv hv1
  obtain ⟨hE1, hE2, hE3, hE4⟩ := hem
  obtain ⟨ι, hιum, hιstd, -⟩ := hE1 ε ε' e hF
  have hn2 : 2 ≤ n := hP.two
  have hB : 100 * ((n : ℝ) + 1) ^ 3 ≤ B := by
    obtain ⟨a, ha⟩ := hP.neg
    have hne : ε a ≠ ε (zi e) := by rw [ha, hF.1]; simp
    have h1 := hP.gap a (zi e) hne
    have h2 := hP.bd a
    have h3 := hP.bd (zi e)
    have h4 : |lam a - lam (zi e)| ≤ |lam a| + |lam (zi e)| := abs_sub _ _
    linarith
  have hn3 : (3 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  have h27 : (3 : ℝ) ^ 3 ≤ ((n : ℝ) + 1) ^ 3 := pow_le_pow_left₀ (by norm_num) hn3 3
  have hB2 : (2 : ℝ) ≤ B := by linarith
  set x : ℝ := 8 * ((n : ℝ) + 1) * B with hx
  have hx16 : (16 : ℝ) ≤ x := by rw [hx]; nlinarith
  have hxn : ((n : ℝ) + 1) ≤ x := by rw [hx]; nlinarith
  have hx0 : 0 < x := by linarith
  have hUπ : IsU (onU ε π) := hE3 ε π hDSπ.2.2.1
  have hUσ : IsU (onU ε' σ) := hE3 ε' σ hDSσ.2.2.1
  haveI hμ : (muG ε).IsHaarMeasure := by unfold muG; infer_instance
  obtain ⟨-, ⟨dπ, hFdeg, hFd⟩, -⟩ := hE4 ε lam π (muG ε) hμ hP.hc hDSπ
  have hFdσ : IsFd ν (onU ε' σ) κ⁻¹ := isFd_of_schurK hK
  have hIso : IsIsoMap (onU ε' σ) (res ι π) i := by
    refine ⟨fun h y => ?_, hiso⟩
    show i (σ (um h) y) = π (umat (ι h)) (i y)
    rw [hιum]
    exact hint h y
  have hIt : Intertw ε' e π σ (ContinuousLinearMap.adjoint i) := by
    refine ⟨?_, fun h y => ?_⟩
    · rw [LinearIsometryEquiv.norm_map]
      exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun z => by rw [hiso, one_mul])
    · apply ext_inner_left ℂ
      intro z
      rw [ContinuousLinearMap.adjoint_inner_right]
      have a1 := UnitaryDecomposition.X4.isU_adj hUπ (ι h) (i z) y
      have a2 := UnitaryDecomposition.X4.isU_adj hUσ h z (ContinuousLinearMap.adjoint i y)
      have e1 : onU ε π (ι h) = π (emb e (um h)) := by
        show π (umat (ι h)) = _
        rw [hιum]
      have e2 : onU ε π (ι h)⁻¹ (i z) = i (σ (um h⁻¹) z) := by
        rw [← map_inv]
        show π (umat (ι h⁻¹)) (i z) = _
        rw [hιum, hint]
      rw [e1] at a1
      rw [a1, e2, ← ContinuousLinearMap.adjoint_inner_right]
      exact a2.symm
  have hconv : ∀ y : UJ ε', ∫ h, starRingEnd ℂ ⟪w, σ (um h) w⟫_ℂ * starRingEnd ℂ ⟪w, σ (um (h⁻¹ * y)) w⟫_ℂ ∂ν
      = (κ : ℂ) * starRingEnd ℂ ⟪w, σ (um y) w⟫_ℂ := by
    intro y
    have := conv_of ν (onU ε' σ) κ⁻¹ hUσ hFdσ w hw1 y
    rw [inv_inv] at this
    exact this
  have hmom := hM n ε lam ε' mu B e H H' π σ ν hν hF hP hDSπ hDSσ (ContinuousLinearMap.adjoint i) w κ hIt hw1
    (by rw [ContinuousLinearMap.adjoint_adjoint, hiso, hw1]) hK.1 hwi hconv
    ⟨η, hη, by rw [ContinuousLinearMap.adjoint_adjoint]; exact hηi,
      by rw [ContinuousLinearMap.adjoint_adjoint]; exact hηint⟩ v hv hv1
  rw [ContinuousLinearMap.adjoint_adjoint] at hmom
  have hone : σ (um (1 : UJ ε')) = 1 := hUσ.one
  have hhs1 : hs (um (1 : UJ ε')) ≤ (n : ℝ) := by
    have h1 : um (1 : UJ ε') = 1 := rfl
    rw [h1]
    simp only [hs, Matrix.one_apply]
    have h2 : ∀ i j : Fin n, ‖(if i = j then (1 : ℂ) else 0)‖ ^ 2 = if i = j then (1 : ℝ) else 0 := by
      intro i j; split_ifs <;> simp
    simp only [h2, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact le_rfl
  have hgap' : GapAtLeast ε' mu (200 * ((n + 1 : ℕ) : ℝ) ^ 3) := by
    push_cast; exact hP.gap'
  have hdec : ∀ g : UJ ε', ‖⟪w, σ (um g) w⟫_ℂ‖ ≤ Real.exp (6 * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.log n
      + 12 * ((n + 1 : ℕ) : ℝ) ^ 2) * (n : ℝ) ^ (12 * (n + 1) ^ 2) * hs (um g) ^ (-(6 * ((n + 1 : ℕ) : ℝ) ^ 2)) := by
    intro g
    have := hDec n (n + 1) ε' mu H' σ (by omega) (by omega) hP.hc' hDSσ hgap' w hw hw1 1 n hhs1 g
    rw [hone] at this
    simpa only [ContinuousLinearMap.one_apply] using this
  have hC := UnitaryDecomposition.X4.num_C (n := n) (x := x) (by omega) (by linarith) (by linarith)
  have hsnn : ∀ g : UJ ε', 0 ≤ hs (um g) := fun g =>
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))
  have hφb : ∀ g : UJ ε', ‖⟪w, σ (um g) w⟫_ℂ * starRingEnd ℂ ⟪w, σ (um g) w⟫_ℂ‖
      ≤ (x ^ (30 * (n + 1) ^ 2)) ^ 2 * hs (um g) ^ (-(2 * (6 * ((n + 1 : ℕ) : ℝ) ^ 2))) := by
    intro g
    have hc := le_trans (hdec g) (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (hsnn g) _))
    have hn0 := norm_nonneg ⟪w, σ (um g) w⟫_ℂ
    have e1 : ‖⟪w, σ (um g) w⟫_ℂ * starRingEnd ℂ ⟪w, σ (um g) w⟫_ℂ‖ = ‖⟪w, σ (um g) w⟫_ℂ‖ ^ 2 := by
      rw [norm_mul, RCLike.norm_conj, sq]
    have e2 : hs (um g) ^ (-(2 * (6 * ((n + 1 : ℕ) : ℝ) ^ 2)))
        = (hs (um g) ^ (-(6 * ((n + 1 : ℕ) : ℝ) ^ 2))) ^ 2 := by
      rw [← Real.rpow_mul_natCast (hsnn g)]
      congr 1
      push_cast
      ring
    rw [e1, e2, ← mul_pow]
    exact pow_le_pow_left₀ hn0 hc 2
  have hc1 : Continuous fun g : UJ ε' => ⟪w, σ (um g) w⟫_ℂ :=
    continuous_const.inner (by exact hUσ.cont w : Continuous fun g : UJ ε' => σ (um g) w)
  have hφc : Continuous fun g : UJ ε' => ⟪w, σ (um g) w⟫_ℂ * starRingEnd ℂ ⟪w, σ (um g) w⟫_ℂ :=
    hc1.mul (Complex.continuous_conj.comp hc1)
  have ha : ((n : ℕ) : ℝ) ^ 2 + 1 ≤ 2 * (6 * ((n + 1 : ℕ) : ℝ) ^ 2) := by
    push_cast; nlinarith
  obtain ⟨-, hIφ⟩ := hIntR n ε' ν hν (by omega) _ _ _ hφc ha hφb
  have hww : ⟪w, w⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hw1]; simp
  have hκφ : κ ≤ ∫ g, ‖⟪w, σ (um g) w⟫_ℂ * starRingEnd ℂ ⟪w, σ (um g) w⟫_ℂ‖ ∂ν := by
    have h := (hK.2 w w w w).2
    rw [hww, mul_one, mul_one] at h
    have h2 : ∫ g, ⟪w, σ (um g) w⟫_ℂ * starRingEnd ℂ ⟪w, σ (um g) w⟫_ℂ ∂ν = (κ : ℂ) := h
    have h3 := norm_integral_le_integral_norm (μ := ν)
      (fun g : UJ ε' => ⟪w, σ (um g) w⟫_ℂ * starRingEnd ℂ ⟪w, σ (um g) w⟫_ℂ)
    rw [h2, Complex.norm_real, Real.norm_eq_abs] at h3
    exact le_trans (le_abs_self κ) h3
  have hD : 1 / κ⁻¹ ≤ x ^ (67 * (n + 1) ^ 2) * ν.real (ball ε' 1) := by
    rw [one_div, inv_inv]
    have hnd := UnitaryDecomposition.X4.num_D (n := n) (x := x) hx16 (by linarith)
    have hνr : 0 ≤ ν.real (ball ε' 1) := measureReal_nonneg
    calc κ ≤ _ := hκφ
      _ ≤ _ := hIφ
      _ ≤ _ := mul_le_mul_of_nonneg_right hnd hνr
  have hY := UnitaryDecomposition.X4.num_Y (N := n + 1) (x := x) (by omega) (by linarith) (by push_cast; linarith)
  have hB1 : 0 < B + 1 := by linarith
  have hδ : 0 < ((100 * ((n + 1 : ℕ) : ℝ) * (B + 1)) ^ 2)⁻¹ := by positivity
  have hδ2 : ((100 * ((n + 1 : ℕ) : ℝ) * (B + 1)) ^ 2)⁻¹ ≤ 2 := by
    have h1 : (1 : ℝ) ≤ (100 * ((n + 1 : ℕ) : ℝ) * (B + 1)) ^ 2 := by
      apply one_le_pow₀
      push_cast
      nlinarith
    have := inv_le_one_of_one_le₀ h1
    linarith
  have hV := UnitaryDecomposition.X4.num_V (N := n + 1) (B := B) (x := x) (by omega) hB2 (by rw [hx]; push_cast; ring)
  have hgap100 : GapAtLeast ε lam (100 * ((n + 1 : ℕ) : ℝ) ^ 3) := by
    intro a b hab
    refine le_trans ?_ (hP.gap a b hab)
    push_cast
    nlinarith
  have hDU := hDUp (n + 1) ε lam B H π (muG ε) dπ hμ (by omega) hP.hc hDSπ hP.bd hgap100 hFdeg
  have hvol : ENNReal.ofReal dπ * muG ε {g : UJ ε | hs (umat g) ≤ 64 * ((n + 1 : ℕ) : ℝ)
      * (((n + 1 : ℕ) : ℝ) + 2 * x ^ (8 * (n + 1))) ^ 2} ≤ ENNReal.ofReal (4 * x ^ (24 * (n + 1) ^ 3)) := by
    have hsub : {g : UJ ε | hs (umat g) ≤ 64 * ((n + 1 : ℕ) : ℝ)
        * (((n + 1 : ℕ) : ℝ) + 2 * x ^ (8 * (n + 1))) ^ 2} ⊆ {g : UJ ε | hs (um g) ≤ (x ^ (10 * (n + 1))) ^ 2} := by
      intro g hg
      simp only [Set.mem_setOf_eq] at hg ⊢
      rw [← pow_mul]
      have e : 10 * (n + 1) * 2 = 20 * (n + 1) := by ring
      rw [e]
      exact le_trans hg hY
    have h1 := measure_mono (μ := muG ε) hsub
    have h2 := hVol (n + 1) ε (muG ε) hμ (by omega) _ (x ^ (10 * (n + 1))) hδ hδ2 (by positivity)
    calc ENNReal.ofReal dπ * muG ε {g : UJ ε | hs (umat g) ≤ 64 * ((n + 1 : ℕ) : ℝ)
          * (((n + 1 : ℕ) : ℝ) + 2 * x ^ (8 * (n + 1))) ^ 2}
        ≤ ENNReal.ofReal dπ * (ENNReal.ofReal ((4 * ((n + 1 : ℕ) : ℝ) * (√((n + 1 : ℕ) : ℝ) + 1)
            * x ^ (10 * (n + 1)) / ((100 * ((n + 1 : ℕ) : ℝ) * (B + 1)) ^ 2)⁻¹) ^ (2 * (n + 1) ^ 2))
            * muG ε (ball ε ((100 * ((n + 1 : ℕ) : ℝ) * (B + 1)) ^ 2)⁻¹)) := by gcongr; exact h1.trans h2
      _ = ENNReal.ofReal ((4 * ((n + 1 : ℕ) : ℝ) * (√((n + 1 : ℕ) : ℝ) + 1)
            * x ^ (10 * (n + 1)) / ((100 * ((n + 1 : ℕ) : ℝ) * (B + 1)) ^ 2)⁻¹) ^ (2 * (n + 1) ^ 2))
            * (ENNReal.ofReal dπ * muG ε (ball ε ((100 * ((n + 1 : ℕ) : ℝ) * (B + 1)) ^ 2)⁻¹)) := by ring
      _ ≤ ENNReal.ofReal ((4 * ((n + 1 : ℕ) : ℝ) * (√((n + 1 : ℕ) : ℝ) + 1)
            * x ^ (10 * (n + 1)) / ((100 * ((n + 1 : ℕ) : ℝ) * (B + 1)) ^ 2)⁻¹) ^ (2 * (n + 1) ^ 2)) * 4 :=
          by gcongr
      _ ≤ ENNReal.ofReal (x ^ (24 * (n + 1) ^ 3)) * 4 := by gcongr
      _ = ENNReal.ofReal (4 * x ^ (24 * (n + 1) ^ 3)) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, mul_comm]
  have hY1 : (1 : ℝ) ≤ 2 * x ^ (8 * (n + 1)) := by
    have : (1 : ℝ) ≤ x ^ (8 * (n + 1)) := one_le_pow₀ (by linarith)
    linarith
  have hK0 : (0 : ℝ) < 4 * x ^ (24 * (n + 1) ^ 3) := by positivity
  have hmomG : ∫⁻ g : UJ ε, ENNReal.ofReal (GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq (umat g⁻¹ *ᵥ Pi.single (zi e) 1)
        * ‖⟪i w, π (umat g) v⟫_ℂ‖ ^ 2) ∂muG ε
      ≤ ENNReal.ofReal (2 * x ^ (8 * (n + 1)) / 2)
        * ∫⁻ g : UJ ε, ENNReal.ofReal (‖⟪i w, π (umat g) v⟫_ℂ‖ ^ 2) ∂muG ε := by
    have e1 : ∀ g : UJ ε, GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.nsq (umat g⁻¹ *ᵥ Pi.single (zi e) 1) = colSq (um g⁻¹) (zi e) :=
      fun g => hE2 _ _
    have e2 : 2 * x ^ (8 * (n + 1)) / 2 = x ^ (8 * (n + 1)) := by ring
    simp_rw [e1, e2]
    exact hmom
  obtain ⟨g₀, hg1, hg2⟩ := hg0 ι (Pi.single (zi e) 1) hιstd π σ (muG ε) ν dπ κ⁻¹ hUπ hUσ hFd hFdσ i hIso
    v w hv1 hw1 (2 * x ^ (8 * (n + 1))) (4 * x ^ (24 * (n + 1) ^ 3)) (x ^ (67 * (n + 1) ^ 2)) hY1 hK0
    hmomG hvol hD
  refine ⟨g₀, le_trans hg1 hY, ?_⟩
  have hg2' : 1 ≤ 4 * x ^ (67 * (n + 1) ^ 2) * (4 * x ^ (24 * (n + 1) ^ 3))
      * ‖ContinuousLinearMap.adjoint i (π (um g₀) v)‖ ^ 2 := hg2
  have ht0 : 0 ≤ ‖ContinuousLinearMap.adjoint i (π (um g₀) v)‖ := norm_nonneg _
  have hM0 : 0 < x ^ (100 * (n + 1) ^ 3) := pow_pos hx0 _
  have elog : 100 * ((n : ℝ) + 1) ^ 3 * Real.log x = Real.log (x ^ (100 * (n + 1) ^ 3)) := by
    rw [Real.log_pow]; push_cast; ring
  rw [elog, Real.exp_neg, Real.exp_log hM0]
  have hA0 : 0 ≤ x ^ (67 * (n + 1) ^ 2) := pow_nonneg hx0.le _
  have hC0 : 0 ≤ x ^ (24 * (n + 1) ^ 3) := pow_nonneg hx0.le _
  have hnat : 1 + 67 * (n + 1) ^ 2 + 24 * (n + 1) ^ 3 ≤ 100 * (n + 1) ^ 3 * 2 := by
    have h1 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h2 : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    linarith
  have hbig : 16 * x ^ (67 * (n + 1) ^ 2) * x ^ (24 * (n + 1) ^ 3) ≤ (x ^ (100 * (n + 1) ^ 3)) ^ 2 := by
    rw [← pow_mul]
    calc 16 * x ^ (67 * (n + 1) ^ 2) * x ^ (24 * (n + 1) ^ 3)
        ≤ x * x ^ (67 * (n + 1) ^ 2) * x ^ (24 * (n + 1) ^ 3) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hx16 hA0) hC0
      _ = x ^ (1 + 67 * (n + 1) ^ 2 + 24 * (n + 1) ^ 3) := by rw [pow_add, pow_add, pow_one]
      _ ≤ x ^ (100 * (n + 1) ^ 3 * 2) := pow_le_pow_right₀ (by linarith) hnat
  by_contra hlt
  push_neg at hlt
  have hsq : ‖ContinuousLinearMap.adjoint i (π (um g₀) v)‖ ^ 2 < ((x ^ (100 * (n + 1) ^ 3))⁻¹) ^ 2 :=
    pow_lt_pow_left₀ hlt ht0 (by norm_num)
  have hp : 0 < 16 * x ^ (67 * (n + 1) ^ 2) * x ^ (24 * (n + 1) ^ 3) :=
    mul_pos (mul_pos (by norm_num) (pow_pos hx0 _)) (pow_pos hx0 _)
  have s1 := mul_lt_mul_of_pos_left hsq hp
  have s2 : 16 * x ^ (67 * (n + 1) ^ 2) * x ^ (24 * (n + 1) ^ 3) * ((x ^ (100 * (n + 1) ^ 3))⁻¹) ^ 2
      ≤ (x ^ (100 * (n + 1) ^ 3)) ^ 2 * ((x ^ (100 * (n + 1) ^ 3))⁻¹) ^ 2 :=
    mul_le_mul_of_nonneg_right hbig (sq_nonneg _)
  have s3 : (x ^ (100 * (n + 1) ^ 3)) ^ 2 * ((x ^ (100 * (n + 1) ^ 3))⁻¹) ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hM0.ne', one_pow]
  have s4 : 4 * x ^ (67 * (n + 1) ^ 2) * (4 * x ^ (24 * (n + 1) ^ 3))
      * ‖ContinuousLinearMap.adjoint i (π (um g₀) v)‖ ^ 2
      = 16 * x ^ (67 * (n + 1) ^ 2) * x ^ (24 * (n + 1) ^ 3)
      * ‖ContinuousLinearMap.adjoint i (π (um g₀) v)‖ ^ 2 := by ring
  rw [s4] at hg2'
  exact absurd (lt_of_le_of_lt hg2' (lt_of_lt_of_le s1 (s2.trans s3.le))) (lt_irrefl 1)

/- English proof (translation)
The claim follows from `bigProjP_of PositivityTheory.UnitaryDecomposition.X4.g0 PositivityTheory.UnitaryDecomposition.X4.emb`.
-/
theorem bigProjP : MomentP → Analysis → BigProjP := bigProjP_of PositivityTheory.UnitaryDecomposition.X4.g0 PositivityTheory.UnitaryDecomposition.X4.emb

end PositivityTheory.RgHe.A.Pf
