import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArithKleiman
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsCurvePointsFinite
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDerived
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 Filter Topology

noncomputable section

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Apply `Filter.EventuallyEq.fderiv_eq` to reduce the goal to its premises. Use `filter_upwards [h.eventually_nhds] with y' hy'`. Establish `hfg : f =ᶠ[𝓝 y'] fun x => g x + b` using `hy'`. Rewrite using `[hfg.fderiv_eq, fderiv_add_const]`.
-/
theorem G5.fderiv_fderiv_eq_of_add_const {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : E → ℝ} {y : E}
    (b : ℝ) (h : ∀ᶠ y' in 𝓝 y, f y' = g y' + b) : fderiv ℝ (fderiv ℝ f) y = fderiv ℝ (fderiv ℝ g) y := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [h.eventually_nhds] with y' hy'
  have hfg : f =ᶠ[𝓝 y'] fun x => g x + b := hy'
  rw [hfg.fderiv_eq, fderiv_add_const]

/- English proof (translation)
Establish `hs : ∀ Ψ y w, sheetDensity P Ψ φ g y w = sheetDensity P Ψ ψ g y w`. Introduce `Ψ y w`. Unfold `sheetDensity`. Use `split_ifs with hγ`. Use `congr 1`.

Establish `hH : ∀ j, cxHessian (fun y' => φ j (hγ.choose y')) y = cxHessian (fun y' => ψ j (hγ.choose y')) y`. Introduce `j`. Take `⟨b, hb⟩` from `h j`. Establish `hev : ∀ᶠ y' in 𝓝 y, φ j (hγ.choose y') = ψ j (hγ.choose y') + b` using `hγ.choose_spec.2.mono fun y' hy' => hb _ hy'.2.1`. Unfold `cxHessian`.

Rewrite using `[G5.fderiv_fderiv_eq_of_add_const b hev]`. Simplify using `only [maDensity, hH]`. Both sides reduce to the same expression. Unfold `ptsIntegral ptsIntegralAt`. Simplify using `only [hs]`.
-/
theorem G5.ptsIntegral_eq_of_add_const {e : ℕ} (P : Ideal (MRing ι)) (φ ψ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (h : ∀ j, ∃ b : ℝ, ∀ z ∈ mcPts P, φ j z = ψ j z + b) (g : ((Σ k, ι k) → ℂ) → ℝ) :
    ptsIntegral P φ g = ptsIntegral P ψ g := by
  have hs : ∀ Ψ y w, sheetDensity P Ψ φ g y w = sheetDensity P Ψ ψ g y w := by
    intro Ψ y w
    unfold sheetDensity
    split_ifs with hγ
    · congr 1
      have hH : ∀ j, cxHessian (fun y' => φ j (hγ.choose y')) y = cxHessian (fun y' => ψ j (hγ.choose y')) y := by
        intro j
        obtain ⟨b, hb⟩ := h j
        have hev : ∀ᶠ y' in 𝓝 y, φ j (hγ.choose y') = ψ j (hγ.choose y') + b :=
          hγ.choose_spec.2.mono fun y' hy' => hb _ hy'.2.1
        unfold cxHessian
        rw [G5.fderiv_fderiv_eq_of_add_const b hev]
      simp only [maDensity, hH]
    · rfl
  unfold ptsIntegral ptsIntegralAt
  simp only [hs]

/- English proof (translation)
Unfold `ptsIntegral`. Use `split_ifs with hΨ`. Unfold `ptsIntegralAt`. Rewrite using `[← MeasureTheory.integral_const_mul]`. Use `congr 1`.

Use function extensionality and compare the values at `y`. Rewrite using `[mul_finsum_mem]`. Use `finsum_mem_congr rfl fun w _ => ?_` and prove the remaining obligations. Unfold `sheetDensity`. Apply the tactic sequence `split_ifs <;> ring`.

Simplify using the standard rewrite rules.
-/
theorem G5.ptsIntegral_const {e : ℕ} (P : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (c : ℝ) :
    ptsIntegral P φ (fun _ => c) = c * ptsIntegral P φ (fun _ => 1) := by
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext y
    rw [mul_finsum_mem]
    refine finsum_mem_congr rfl fun w _ => ?_
    unfold sheetDensity
    split_ifs <;> ring
  · simp

/- English proof (translation)
Use `show ContDiffOn ℝ _ (fun _ => Real.exp (-c)) _`. Conclude with `contDiffOn_const`.
-/
theorem G5.isSmoothHerm_constLine (c : ℝ) : IsSmoothHerm (constLine (ι := ι) c) := by
  show ContDiffOn ℝ _ (fun _ => Real.exp (-c)) _
  exact contDiffOn_const

/- English proof (translation)
Use `show Real.log (A.h z * Real.exp (-c)) = _`. Rewrite using `[Real.log_mul (A.pos z hz).ne' (Real.exp_pos _).ne', Real.log_exp]`.
-/
theorem G5.log_tensor_constLine (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ℝ) (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log ((A.tensor (constLine c)).h z) = Real.log (A.h z) + -c := by
  show Real.log (A.h z * Real.exp (-c)) = _
  rw [Real.log_mul (A.pos z hz).ne' (Real.exp_pos _).ne', Real.log_exp]

/- English proof (translation)
Use `set A' := A.tensor (constLine (ι := ι) c) with hA'def`. Establish `hA' : IsSmoothHerm A'` using `hA.mul (G5.isSmoothHerm_constLine c)`. Set `L : ℕ → Fin (D + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι` to `fun k j => if (j : ℕ) < k then A' else A`. Establish `hL2 : ∀ k j, L k j = A ∨ L k j = A'` using `fun k j => by`. Distinguish the cases in `h : (j : ℕ) < k`.

Conclude with `Or.inr (if_pos h)`. Conclude with `Or.inl (if_neg h)`. Establish `hLs : ∀ k j, IsSmoothHerm (L k j)` using `fun k j => (hL2 k j).elim (fun h => h ▸ hA) (fun h => h ▸ hA')`. Establish `hint : ∀ M : Fin D → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, (∀ j, M j = A ∨ M j = A') → ptsIntegral P (pot M) (fun _ => c) = c * geomDeg P A D`. Introduce `M hM`.

Rewrite using `[G5.ptsIntegral_const]`. Use `congr 1`. Use `G5.ptsIntegral_eq_of_add_const P _ _ (fun j => ?_) _` and prove the remaining obligations. Break down `hM j with h | h` into its components or cases. Conclude with `⟨0, fun z _ => by simp [pot, h]⟩`.

Conclude with `⟨-c, fun z hz => by simp only [pot, h]; exact G5.log_tensor_constLine A c z hz.1⟩`. Establish `step : ∀ k, k ≤ D + 1 → I P (D + 1) (L k) = I P (D + 1) (fun _ => A) - (k : ℝ) * c * geomDeg P A D`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`.

Introduce `_`. Establish `: L 0 = fun _ => A` using `by funext j; simp [L]`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Consider the case `succ k ih`.

Introduce `hk`. Establish `hkD : k < D + 1` using `by omega`. Use `set i : Fin (D + 1) := ⟨k, hkD⟩`. Use `set σ := Equiv.swap i (Fin.last D)`. Use `set M : Fin D → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun j => L (k + 1) (σ (Fin.castSucc j))`.

Establish `hne : ∀ j : Fin D, σ (Fin.castSucc j) ≠ i`. Introduce `j hj`. Rewrite `hj` using `[Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]`. Conclude with `(Fin.castSucc_lt_last j).ne hj`. Establish `hMk : ∀ j : Fin D, L k (σ (Fin.castSucc j)) = M j`.

Introduce `j`. Establish `h1 : ((σ (Fin.castSucc j) : Fin (D + 1)) : ℕ) ≠ k` using `fun h => hne j (Fin.ext h)`. Simplify using `only [M, L]`. Distinguish the cases in `h2 : ((σ (Fin.castSucc j) : Fin (D + 1)) : ℕ) < k`. Rewrite using `[if_pos h2, if_pos (by omega)]`.

Rewrite using `[if_neg h2, if_neg (by omega)]`. Establish `hσi : σ (Fin.last D) = i` using `Equiv.swap_apply_right _ _`. Establish `e1 : L (k + 1) ∘ σ = Fin.snoc M A'`. Use function extensionality and compare the values at `x`. Use `Fin.lastCases ?_ (fun j => ?_) x` and prove the remaining obligations.

Simplify using `only [Function.comp_apply, Fin.snoc_last, hσi, L, i]`. Conclude with `if_pos (Nat.lt_succ_self k)`. Simplify using `only [Function.comp_apply, Fin.snoc_castSucc, M]`. Establish `e0 : L k ∘ σ = Fin.snoc M A`. Use function extensionality and compare the values at `x`.

Use `Fin.lastCases ?_ (fun j => ?_) x` and prove the remaining obligations. Simplify using `only [Function.comp_apply, Fin.snoc_last, hσi, L, i]`. Conclude with `if_neg (lt_irrefl k)`. Simplify using `only [Function.comp_apply, Fin.snoc_castSucc]`. Conclude with `hMk j`.

Establish `hM : ∀ j, M j = A ∨ M j = A'` using `fun j => hL2 _ _`. Establish `hMs : ∀ j, IsSmoothHerm (M j)` using `fun j => hLs _ _`. Establish `hmc` using `metricChange K ι I hI P D M A (fun _ => c) (fun _ _ _ => rfl) hP hMs hA contDiffOn_const`. Establish `s1` using `hI.1 P (D + 1) (L (k + 1)) σ hP (hLs _)`. Establish `s0` using `hI.1 P (D + 1) (L k) σ hP (hLs _)`.

Rewrite `s1` using `[e1]`. Rewrite `s0` using `[e0]`. Establish `hsnoc : I P (D + 1) (Fin.snoc M A') = I P (D + 1) (Fin.snoc M A) - ptsIntegral P (pot M) (fun _ => c)` using `hmc`. Rewrite using `[← s1, hsnoc, s0, ih (by omega), hint M hM]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hall : L (D + 1) = fun _ => A'`. Use function extensionality and compare the values at `j`. Conclude with `if_pos j.isLt`. Use `step (D + 1) le_rfl` as an intermediate fact.

Rewrite `this` using `[hall]`. Rewrite using `[this]`.
-/
theorem G5.top_tensor_constLine (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ)
    (hI : IsIntersectionFamily I) (P : Ideal (MRing ι)) (D : ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ℝ)
    (hP : IsArithVar P (D + 1)) (hA : IsSmoothHerm A) :
    I P (D + 1) (fun _ => A.tensor (constLine c)) =
      I P (D + 1) (fun _ => A) - ((D + 1 : ℕ) : ℝ) * c * geomDeg P A D := by
  set A' := A.tensor (constLine (ι := ι) c) with hA'def
  have hA' : IsSmoothHerm A' := hA.mul (G5.isSmoothHerm_constLine c)
  let L : ℕ → Fin (D + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun k j => if (j : ℕ) < k then A' else A
  have hL2 : ∀ k j, L k j = A ∨ L k j = A' := fun k j => by
    by_cases h : (j : ℕ) < k
    · exact Or.inr (if_pos h)
    · exact Or.inl (if_neg h)
  have hLs : ∀ k j, IsSmoothHerm (L k j) := fun k j => (hL2 k j).elim (fun h => h ▸ hA) (fun h => h ▸ hA')

  have hint : ∀ M : Fin D → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, (∀ j, M j = A ∨ M j = A') →
      ptsIntegral P (pot M) (fun _ => c) = c * geomDeg P A D := by
    intro M hM
    rw [G5.ptsIntegral_const]
    congr 1
    refine G5.ptsIntegral_eq_of_add_const P _ _ (fun j => ?_) _
    rcases hM j with h | h
    · exact ⟨0, fun z _ => by simp [pot, h]⟩
    · exact ⟨-c, fun z hz => by simp only [pot, h]; exact G5.log_tensor_constLine A c z hz.1⟩
  have step : ∀ k, k ≤ D + 1 → I P (D + 1) (L k) = I P (D + 1) (fun _ => A) - (k : ℝ) * c * geomDeg P A D := by
    intro k
    induction k with
    | zero =>
      intro _
      have : L 0 = fun _ => A := by funext j; simp [L]
      rw [this]; simp
    | succ k ih =>
      intro hk
      have hkD : k < D + 1 := by omega
      set i : Fin (D + 1) := ⟨k, hkD⟩
      set σ := Equiv.swap i (Fin.last D)
      set M : Fin D → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun j => L (k + 1) (σ (Fin.castSucc j))
      have hne : ∀ j : Fin D, σ (Fin.castSucc j) ≠ i := by
        intro j hj
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at hj
        exact (Fin.castSucc_lt_last j).ne hj
      have hMk : ∀ j : Fin D, L k (σ (Fin.castSucc j)) = M j := by
        intro j
        have h1 : ((σ (Fin.castSucc j) : Fin (D + 1)) : ℕ) ≠ k := fun h => hne j (Fin.ext h)
        simp only [M, L]
        by_cases h2 : ((σ (Fin.castSucc j) : Fin (D + 1)) : ℕ) < k
        · rw [if_pos h2, if_pos (by omega)]
        · rw [if_neg h2, if_neg (by omega)]
      have hσi : σ (Fin.last D) = i := Equiv.swap_apply_right _ _
      have e1 : L (k + 1) ∘ σ = Fin.snoc M A' := by
        funext x
        refine Fin.lastCases ?_ (fun j => ?_) x
        · simp only [Function.comp_apply, Fin.snoc_last, hσi, L, i]
          exact if_pos (Nat.lt_succ_self k)
        · simp only [Function.comp_apply, Fin.snoc_castSucc, M]
      have e0 : L k ∘ σ = Fin.snoc M A := by
        funext x
        refine Fin.lastCases ?_ (fun j => ?_) x
        · simp only [Function.comp_apply, Fin.snoc_last, hσi, L, i]
          exact if_neg (lt_irrefl k)
        · simp only [Function.comp_apply, Fin.snoc_castSucc]
          exact hMk j
      have hM : ∀ j, M j = A ∨ M j = A' := fun j => hL2 _ _
      have hMs : ∀ j, IsSmoothHerm (M j) := fun j => hLs _ _
      have hmc := metricChange K ι I hI P D M A (fun _ => c) (fun _ _ _ => rfl) hP hMs hA contDiffOn_const
      have s1 := hI.1 P (D + 1) (L (k + 1)) σ hP (hLs _)
      have s0 := hI.1 P (D + 1) (L k) σ hP (hLs _)
      rw [e1] at s1
      rw [e0] at s0
      have hsnoc : I P (D + 1) (Fin.snoc M A') =
          I P (D + 1) (Fin.snoc M A) - ptsIntegral P (pot M) (fun _ => c) := hmc
      rw [← s1, hsnoc, s0, ih (by omega), hint M hM]
      push_cast
      ring
  have hall : L (D + 1) = fun _ => A' := by
    funext j
    exact if_pos j.isLt
  have := step (D + 1) le_rfl
  rw [hall] at this
  rw [this]

/- English proof (translation)
Introduce `K _ ι _ P P0 D A e II hII hP hP0 hsemi hnef hconj hW`. Use `set A' := A.tensor (constLine (ι := ι) e) with hA'def`. Establish `hA : IsSmoothHerm A` using `hsemi.1`. Establish `hA' : IsSmoothHerm A'` using `hA.mul (G5.isSmoothHerm_constLine e)`. Establish `hU : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}`.

Simplify using `only [Set.ofPred_forall, Set.ofPred_exists]`. Conclude with `isOpen_iInter_of_finite fun k => isOpen_iUnion fun i => isOpen_ne_fun (continuous_apply _) continuous_const`. Establish `hsemi' : IsSemipositiveRel P0 P A'`. Use `⟨hA', fun z hz w hw => ?_⟩` and prove the remaining obligations. Establish `hev : ∀ᶠ z' in 𝓝 z, Real.log (A'.h z') = Real.log (A.h z') + -e` using `(show ∀ᶠ z' in 𝓝 z, ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0 from hU.mem_nhds hz.1).mono fun z' hz' => G5.log_tensor_constLine A e z' hz'`.

Establish `: leviForm (fun z => Real.log (A'.h z)) z w = leviForm (fun z => Real.log (A.h z)) z w`. Unfold `leviForm`. Rewrite using `[G5.fderiv_fderiv_eq_of_add_const (-e) hev]`. Rewrite using `[this]`. Conclude with `hsemi.2 z hz w hw`.

Establish `ha : A'.a = A.a` using `by show A.a + 0 = A.a`. Rewrite using `[add_zero]`. Establish `hnef' : NefOnFibres P A'.a` using `ha ▸ hnef`. Establish `hconj' : IsConjInvariantH A'` using `fun z => by show A.h _ * Real.exp (-e) = A.h z * Real.exp (-e)`. Rewrite using `[hconj z]`.

Establish `hW' : ∀ W, IsArithVar W 1 → P ≤ W → 0 ≤ II K ι W 1 ![A']`. Introduce `W hW1 hPW`. Establish `hsn : ∀ B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, (Fin.snoc (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) B : Fin 1 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) = ![B]`. Introduce `B`. Use function extensionality and compare the values at `j`.

Use `fin_cases j`. Both sides reduce to the same expression. Establish `hmc` using `metricChange K ι (II K ι) (hII K ι) W 0 ![] A (fun _ => e) (fun _ _ _ => rfl) hW1 (fun j => j.elim0) hA contDiffOn_const`. Rewrite `hmc` using `[hsn, hsn]`. Establish `: Nonempty K` using `hW1.1`.

Establish `: Finite (GroundTheory.Heights₂.Heights.projPts W)` using `hF K ι W hW1`. Establish `hpot : pot (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) = Fin.elim0` using `Subsingleton.elim _ _`. Establish `hpts` using `hPts K ι W (fun _ => e) inferInstance (fun _ _ _ _ => rfl)`. Establish `hcount : ptsIntegral W (pot (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)) (fun _ => e) = e * degC W`. Rewrite using `[hpot, hpts]`.

Use `letI := Fintype.ofFinite (GroundTheory.Heights₂.Heights.projPts W)`. Rewrite using `[finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, GroundTheory.Heights₂.Heights.degC_eq_card_projPts, Nat.card_eq_fintype_card]`. Expand and normalize the polynomial expressions, which then agree. Establish `hA'W : II K ι W 1 ![A'] = II K ι W 1 ![A] - e * degC W`. Rewrite using `[← hcount]`.

Conclude with `hmc`. Rewrite using `[hA'W]`. Combine the linear relations using `[hW W hW1 hPW]`. Establish `hkl` using `hK K ι P P0 D A' II hII hP hP0 hsemi' hnef' hconj' hW'`. Establish `htop` using `G5.top_tensor_constLine (II K ι) (hII K ι) P D A e hP hA`.

Rewrite `htop` using `[← hA'def]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem G5.proof (hK : ArithKleiman.Statement) (hF : CurvePointsFinite.Statement)
    (hPts : GroundTheory.Heights₂.Heights.PtsIntegralPoints.Statement) : G5.Statement := by
  intro K _ ι _ P P0 D A e II hII hP hP0 hsemi hnef hconj hW
  set A' := A.tensor (constLine (ι := ι) e) with hA'def
  have hA : IsSmoothHerm A := hsemi.1
  have hA' : IsSmoothHerm A' := hA.mul (G5.isSmoothHerm_constLine e)
  have hU : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  have hsemi' : IsSemipositiveRel P0 P A' := by
    refine ⟨hA', fun z hz w hw => ?_⟩
    have hev : ∀ᶠ z' in 𝓝 z, Real.log (A'.h z') = Real.log (A.h z') + -e :=
      (show ∀ᶠ z' in 𝓝 z, ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0 from hU.mem_nhds hz.1).mono fun z' hz' => G5.log_tensor_constLine A e z' hz'
    have : leviForm (fun z => Real.log (A'.h z)) z w = leviForm (fun z => Real.log (A.h z)) z w := by
      unfold leviForm
      rw [G5.fderiv_fderiv_eq_of_add_const (-e) hev]
    rw [this]
    exact hsemi.2 z hz w hw
  have ha : A'.a = A.a := by
    show A.a + 0 = A.a
    rw [add_zero]
  have hnef' : NefOnFibres P A'.a := ha ▸ hnef
  have hconj' : IsConjInvariantH A' := fun z => by
    show A.h _ * Real.exp (-e) = A.h z * Real.exp (-e)
    rw [hconj z]
  have hW' : ∀ W, IsArithVar W 1 → P ≤ W → 0 ≤ II K ι W 1 ![A'] := by
    intro W hW1 hPW
    have hsn : ∀ B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, (Fin.snoc (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) B : Fin 1 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) = ![B] := by
      intro B
      funext j
      fin_cases j
      rfl
    have hmc := metricChange K ι (II K ι) (hII K ι) W 0 ![] A (fun _ => e) (fun _ _ _ => rfl) hW1
      (fun j => j.elim0) hA contDiffOn_const
    rw [hsn, hsn] at hmc
    have : Nonempty K := hW1.1
    have : Finite (GroundTheory.Heights₂.Heights.projPts W) := hF K ι W hW1
    have hpot : pot (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) = Fin.elim0 := Subsingleton.elim _ _
    have hpts := hPts K ι W (fun _ => e) inferInstance (fun _ _ _ _ => rfl)
    have hcount : ptsIntegral W (pot (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)) (fun _ => e) = e * degC W := by
      rw [hpot, hpts]
      letI := Fintype.ofFinite (GroundTheory.Heights₂.Heights.projPts W)
      rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        GroundTheory.Heights₂.Heights.degC_eq_card_projPts, Nat.card_eq_fintype_card]
      ring
    have hA'W : II K ι W 1 ![A'] = II K ι W 1 ![A] - e * degC W := by
      rw [← hcount]
      exact hmc
    rw [hA'W]
    linarith [hW W hW1 hPW]
  have hkl := hK K ι P P0 D A' II hII hP hP0 hsemi' hnef' hconj' hW'
  have htop := G5.top_tensor_constLine (II K ι) (hII K ι) P D A e hP hA
  rw [← hA'def] at htop
  linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
