import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallAlgHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousReadOnAffineOpenRingHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairNormIndependentOfFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxPrincipleNear
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

/- English proof (translation)
Introduce `k _ X _ p D hX P a b r f hf hli`. Establish `h1 : genericPoint X ∈ ⨆ i, P.L.B.U i` using `by rw [P.L.isLB.cover]; trivial`. Establish `h2 : genericPoint X ∈ ⨆ j, P.A.B.U j` using `by rw [P.A.isLB.cover]; trivial`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 h1`. Take `⟨j, hj⟩` from `TopologicalSpace.Opens.mem_iSup.1 h2`.

Take `⟨U, hU, hgU, hle⟩` from `exists_isAffineOpen_mem_and_subset (x := genericPoint X) (U := P.L.B.U i ⊓ P.A.B.U j) ⟨hi, hj⟩`. Establish `hl : U ≤ P.L.B.U i` using `fun x hx => (hle hx).1`. Establish `hr : U ≤ P.A.B.U j` using `fun x hx => (hle hx).2`. Establish `: Nonempty U` using `⟨⟨_, hgU⟩⟩`. Establish `: CharZero Γ(X, U)` using `((resG X (le_top : U ≤ ⊤)).charZero_iff (map_injective_of_isIntegral X _)).1 hX.charZero`.

Use `finiteType_int_of_isAffineOpen hX hU` as an intermediate fact. Establish `hg : ∀ l, ∃ g, fnOf U hgU g = P.loc a b (f l) i j` using `fun l => exists_fnOf_eq hgU fun x hx => hf l x i j (hl hx) (hr hx)`. Use `choose g hg using hg`. Use `set c0 : X.functionField := (P.r i : X.functionField) ^ a * (P.r' j : X.functionField) ^ b with hc0def`. Establish `hloc : ∀ h, P.loc a b h i j = h * c0` using `fun h => by simp only [Pair.loc, c0, mul_assoc]`.

Establish `hc0 : c0 ≠ 0` using `mul_ne_zero (zpow_ne_zero _ (P.r i).ne_zero) (zpow_ne_zero _ (P.r' j).ne_zero)`. Establish `hlig : LinearIndependent ℤ g`. Establish `h3 : LinearIndependent ℤ ((LinearMap.mulRight ℤ c0) ∘ f)` using `hli.map' _ (LinearMap.ker_eq_bot.2 (mul_left_injective₀ hc0))`. Use `LinearIndependent.of_comp (fnOf U hgU).toAddMonoidHom.toIntLinearMap ?_` and prove the remaining obligations. Establish `e : (⇑(fnOf U hgU).toAddMonoidHom.toIntLinearMap ∘ g) = ⇑(LinearMap.mulRight ℤ c0) ∘ f`.

Use function extensionality and compare the values at `l`. Simplify using `[hg, hloc]`. Rewrite using `[e]`. Conclude with `h3`. Take `⟨x, hx⟩` from `GlobalTheory.CxPointsSep.exists_det_ne_zero Γ(X, U) r g hlig`.

Take `⟨-, -, -, hsurj, -⟩` from `GlobalTheory.ContRead.exists_continuous_read k X p D hX U hU (fun _ _ => 0) fun _ => continuousOn_const`. Use `choose σ y hy hyx using hsurj`. Set `M : Matrix (Fin r) (Fin r) ℂ` to `Matrix.of fun s l => x s (g l)`. Set `w : Fin r → ℝ` to `fun s => Real.exp ((a * (P.L.φ (σ (x s))).φ i (y (x s)) + b * (P.A.φ (σ (x s))).φ j (y (x s))) / 2)`. Set `E : ℝ` to `∑ s, w s`.

Set `K : ℝ` to `∑ l, ∑ s, ‖M⁻¹ l s‖`. Establish `hE : 0 ≤ E` using `Finset.sum_nonneg fun s _ => (Real.exp_pos _).le`. Establish `hK : 0 ≤ K` using `Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun s _ => norm_nonneg _`. Use `⟨K * E, mul_nonneg hK hE, fun cc R hR l => ?_⟩` and prove the remaining obligations. Use `set v : Fin r → ℂ := Matrix.mulVec M fun l => (cc l : ℂ) with hvdef`.

Establish `hsum : P.loc a b (∑ l, cc l • f l) i j = fnOf U hgU (∑ l, cc l • g l)`. Rewrite using `[hloc, Finset.sum_mul, map_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, hg, hloc, smul_mul_assoc]`. Establish `key : ∀ s, ‖v s‖ ≤ R * w s`.

Introduce `s`. Establish `e` using `GlobalTheory.VolBr.nu_eq k X p P a b _ hR.1 (σ (x s)) (y (x s)) i j (ptsIn_mono hl (hy (x s))) (ptsIn_mono hr (hy (x s)))`. Rewrite `e` using `[hsum, ratVal_fnOf (hy (x s)), ev_eq (hy (x s)), hyx]`. Establish `hv : v s = x s (∑ l, cc l • g l)`. Simplify using `[v, M, Matrix.mulVec, dotProduct, map_sum, map_zsmul, mul_comm]`.

Establish `hb` using `hR.2 (σ (x s)) (y (x s))`. Rewrite `hb` using `[e]`. Rewrite using `[hv]`. Establish `hw : ‖x s (∑ l, cc l • g l)‖ = ‖x s (∑ l, cc l • g l)‖ * Real.exp (-(a * (P.L.φ (σ (x s))).φ i (y (x s)) + b * (P.A.φ (σ (x s))).φ j (y (x s))) / 2) * w s`. Rewrite using `[mul_assoc, ← Real.exp_add]`.

Establish `: -(a * (P.L.φ (σ (x s))).φ i (y (x s)) + b * (P.A.φ (σ (x s))).φ j (y (x s))) / 2 + (a * (P.L.φ (σ (x s))).φ i (y (x s)) + b * (P.A.φ (σ (x s))).φ j (y (x s))) / 2 = 0` using `by ring`. Rewrite using `[this, Real.exp_zero, mul_one]`. Rewrite using `[hw]`. Conclude with `mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le`. Establish `hR0 : 0 ≤ R`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Use `mul_neg_of_neg_of_pos h (Real.exp_pos _ : (0 : ℝ) < w l)` as an intermediate fact. Combine the linear relations using `[key l, norm_nonneg (v l)]`. Establish `hinv : (fun l => (cc l : ℂ)) = Matrix.mulVec M⁻¹ v`.

Rewrite using `[hvdef, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hx), Matrix.one_mulVec]`. Establish `habs : |(cc l : ℝ)| = ‖(cc l : ℂ)‖` using `by simp`. Rewrite using `[habs, congrFun hinv l]`. Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hE) hR0` and prove the remaining obligations.

Conclude with `Finset.single_le_sum (f := fun l => ∑ s, ‖M⁻¹ l s‖) (fun t _ => Finset.sum_nonneg fun s _ => norm_nonneg _) (Finset.mem_univ l)`.
-/
theorem exists_coeff_le_of_linearIndependent : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a b : ℤ) (r : ℕ) (f : Fin r → X.functionField), (∀ j, f j ∈ P.H a b) → LinearIndependent ℤ f → ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : Fin r → ℤ) (R : ℝ), (∑ j, c j • f j) ∈ P.Bl a b R → ∀ j, |(c j : ℝ)| ≤ C * R := by
  intro k _ X _ p D hX P a b r f hf hli
  classical
  have h1 : genericPoint X ∈ ⨆ i, P.L.B.U i := by rw [P.L.isLB.cover]; trivial
  have h2 : genericPoint X ∈ ⨆ j, P.A.B.U j := by rw [P.A.isLB.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h1
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 h2
  obtain ⟨U, hU, hgU, hle⟩ := exists_isAffineOpen_mem_and_subset (x := genericPoint X)
    (U := P.L.B.U i ⊓ P.A.B.U j) ⟨hi, hj⟩
  have hl : U ≤ P.L.B.U i := fun x hx => (hle hx).1
  have hr : U ≤ P.A.B.U j := fun x hx => (hle hx).2
  have : Nonempty U := ⟨⟨_, hgU⟩⟩
  have : CharZero Γ(X, U) :=
    ((resG X (le_top : U ≤ ⊤)).charZero_iff (map_injective_of_isIntegral X _)).1 hX.charZero
  have := finiteType_int_of_isAffineOpen hX hU
  have hg : ∀ l, ∃ g, fnOf U hgU g = P.loc a b (f l) i j := fun l =>
    exists_fnOf_eq hgU fun x hx => hf l x i j (hl hx) (hr hx)
  choose g hg using hg
  set c0 : X.functionField := (P.r i : X.functionField) ^ a * (P.r' j : X.functionField) ^ b with hc0def
  have hloc : ∀ h, P.loc a b h i j = h * c0 := fun h => by simp only [Pair.loc, c0, mul_assoc]
  have hc0 : c0 ≠ 0 := mul_ne_zero (zpow_ne_zero _ (P.r i).ne_zero) (zpow_ne_zero _ (P.r' j).ne_zero)
  have hlig : LinearIndependent ℤ g := by
    have h3 : LinearIndependent ℤ ((LinearMap.mulRight ℤ c0) ∘ f) :=
      hli.map' _ (LinearMap.ker_eq_bot.2 (mul_left_injective₀ hc0))
    refine LinearIndependent.of_comp (fnOf U hgU).toAddMonoidHom.toIntLinearMap ?_
    have e : (⇑(fnOf U hgU).toAddMonoidHom.toIntLinearMap ∘ g) = ⇑(LinearMap.mulRight ℤ c0) ∘ f := by
      funext l
      simp [hg, hloc]
    rw [e]
    exact h3
  obtain ⟨x, hx⟩ := GlobalTheory.CxPointsSep.exists_det_ne_zero Γ(X, U) r g hlig
  obtain ⟨-, -, -, hsurj, -⟩ := GlobalTheory.ContRead.exists_continuous_read k X p D hX U hU (fun _ _ => 0)
    fun _ => continuousOn_const
  choose σ y hy hyx using hsurj
  let M : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun s l => x s (g l)
  let w : Fin r → ℝ := fun s => Real.exp ((a * (P.L.φ (σ (x s))).φ i (y (x s)) +
    b * (P.A.φ (σ (x s))).φ j (y (x s))) / 2)
  let E : ℝ := ∑ s, w s
  let K : ℝ := ∑ l, ∑ s, ‖M⁻¹ l s‖
  have hE : 0 ≤ E := Finset.sum_nonneg fun s _ => (Real.exp_pos _).le
  have hK : 0 ≤ K := Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun s _ => norm_nonneg _
  refine ⟨K * E, mul_nonneg hK hE, fun cc R hR l => ?_⟩
  set v : Fin r → ℂ := Matrix.mulVec M fun l => (cc l : ℂ) with hvdef
  have hsum : P.loc a b (∑ l, cc l • f l) i j = fnOf U hgU (∑ l, cc l • g l) := by
    rw [hloc, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_zsmul, hg, hloc, smul_mul_assoc]
  have key : ∀ s, ‖v s‖ ≤ R * w s := by
    intro s
    have e := GlobalTheory.VolBr.nu_eq k X p P a b _ hR.1 (σ (x s)) (y (x s)) i j
      (ptsIn_mono hl (hy (x s))) (ptsIn_mono hr (hy (x s)))
    rw [hsum, ratVal_fnOf (hy (x s)), ev_eq (hy (x s)), hyx] at e
    have hv : v s = x s (∑ l, cc l • g l) := by
      simp [v, M, Matrix.mulVec, dotProduct, map_sum, map_zsmul, mul_comm]
    have hb := hR.2 (σ (x s)) (y (x s))
    rw [e] at hb
    rw [hv]
    have hw : ‖x s (∑ l, cc l • g l)‖ = ‖x s (∑ l, cc l • g l)‖ *
        Real.exp (-(a * (P.L.φ (σ (x s))).φ i (y (x s)) + b * (P.A.φ (σ (x s))).φ j (y (x s))) / 2) * w s := by
      rw [mul_assoc, ← Real.exp_add]
      have : -(a * (P.L.φ (σ (x s))).φ i (y (x s)) + b * (P.A.φ (σ (x s))).φ j (y (x s))) / 2 +
          (a * (P.L.φ (σ (x s))).φ i (y (x s)) + b * (P.A.φ (σ (x s))).φ j (y (x s))) / 2 = 0 := by ring
      rw [this, Real.exp_zero, mul_one]
    rw [hw]
    exact mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
  have hR0 : 0 ≤ R := by
    by_contra h
    push_neg at h
    have := mul_neg_of_neg_of_pos h (Real.exp_pos _ : (0 : ℝ) < w l)
    linarith [key l, norm_nonneg (v l)]
  have hinv : (fun l => (cc l : ℂ)) = Matrix.mulVec M⁻¹ v := by
    rw [hvdef, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hx), Matrix.one_mulVec]
  have habs : |(cc l : ℝ)| = ‖(cc l : ℂ)‖ := by simp
  rw [habs, congrFun hinv l]
  calc ‖Matrix.mulVec M⁻¹ v l‖ = ‖∑ s, M⁻¹ l s * v s‖ := rfl
    _ ≤ ∑ s, ‖M⁻¹ l s‖ * ‖v s‖ := (norm_sum_le _ _).trans (le_of_eq (by simp [norm_mul]))
    _ ≤ ∑ s, ‖M⁻¹ l s‖ * (R * E) := Finset.sum_le_sum fun s _ =>
        mul_le_mul_of_nonneg_left ((key s).trans (mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (f := w) (fun t _ => (Real.exp_pos _).le) (Finset.mem_univ s)) hR0)) (norm_nonneg _)
    _ = (∑ s, ‖M⁻¹ l s‖) * E * R := by rw [← Finset.sum_mul]; ring
    _ ≤ K * E * R := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hE) hR0
        exact Finset.single_le_sum (f := fun l => ∑ s, ‖M⁻¹ l s‖)
          (fun t _ => Finset.sum_nonneg fun s _ => norm_nonneg _) (Finset.mem_univ l)

end GlobalTheory.HSNef
