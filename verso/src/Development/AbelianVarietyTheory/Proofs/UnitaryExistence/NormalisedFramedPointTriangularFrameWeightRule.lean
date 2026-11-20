import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TriangularFrameMovesPeriodBlockTriangularStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaPointsChangeLevelIsometryLinearMapStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtIffIsDerivAt0
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.NormUnBor

/- English proof (translation)
Establish `hdet : A.det = ∏ i, A i i`. Rewrite using `[Matrix.det_apply, Finset.sum_eq_single (1 : Equiv.Perm (Fin g))]`. Simplify using the standard rewrite rules. Introduce `s _ hs`. Assume the negation of the conclusion as `hne`.

Establish `hp : ∏ i, A (s i) i ≠ 0` using `fun h0 => hne (by rw [h0, smul_zero])`. Establish `hall : ∀ i, A (s i) i ≠ 0` using `fun i => Finset.prod_ne_zero_iff.1 hp i (Finset.mem_univ i)`. Establish `hsum : ∑ i, ((e (s i)).2 : ℕ) = ∑ i, ((e i).2 : ℕ)` using `Equiv.sum_comp s (fun i => ((e i).2 : ℕ))`. Establish `heq` using `(Finset.sum_eq_sum_iff_of_le (fun i _ => (htri _ _ (hall i)).2)).1 hsum`. Apply `hs` to reduce the goal to its premises.

Use extensionality with `i`. Establish `h1` using `(htri _ _ (hall i)).1`. Establish `h2` using `heq i (Finset.mem_univ i)`. Establish `: e (s i) = e i` using `Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).2 h2)`. Simplify using `[e.injective this]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Rewrite `hA` using `[hdet]`. Conclude with `Finset.prod_ne_zero_iff.1 hA j (Finset.mem_univ j)`.
-/
theorem diag_ne_zero {T : Type} {m : T → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : T, Fin (m τ))
    (A : Matrix (Fin g) (Fin g) ℂ) (hA : A.det ≠ 0)
    (htri : ∀ j j', A j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) (j : Fin g) : A j j ≠ 0 := by
  have hdet : A.det = ∏ i, A i i := by
    rw [Matrix.det_apply, Finset.sum_eq_single (1 : Equiv.Perm (Fin g))]
    · simp
    · intro s _ hs
      by_contra hne
      have hp : ∏ i, A (s i) i ≠ 0 := fun h0 => hne (by rw [h0, smul_zero])
      have hall : ∀ i, A (s i) i ≠ 0 := fun i => Finset.prod_ne_zero_iff.1 hp i (Finset.mem_univ i)
      have hsum : ∑ i, ((e (s i)).2 : ℕ) = ∑ i, ((e i).2 : ℕ) :=
        Equiv.sum_comp s (fun i => ((e i).2 : ℕ))
      have heq := (Finset.sum_eq_sum_iff_of_le (fun i _ => (htri _ _ (hall i)).2)).1 hsum
      apply hs
      ext i
      have h1 := (htri _ _ (hall i)).1
      have h2 := heq i (Finset.mem_univ i)
      have : e (s i) = e i := Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).2 h2)
      simp [e.injective this]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hdet] at hA
  exact Finset.prod_ne_zero_iff.1 hA j (Finset.mem_univ j)

/- English proof (translation)
Use function extensionality and compare the values at `p`. Take `⟨⟨τ', i'⟩, rfl⟩` from `e.symm.surjective p`. Rewrite using `[Matrix.mulVec_single_one, Finset.sum_apply]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Matrix.col_apply]`. Distinguish the cases in `hτ : τ' = τ`.

Substitute `hτ` using the available equality. Rewrite using `[Finset.sum_eq_single i']`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Rewrite using `[Pi.single_eq_of_ne, mul_zero]`.

Introduce `h`. Conclude with `hj (sigma_mk_injective (β := fun τ => Fin (m τ)) (e.symm.injective h)).symm`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Establish `h0 : A (e.symm ⟨τ', i'⟩) (e.symm ⟨τ, i⟩) = 0`.

Assume the negation of the conclusion as `hne`. Use `(htri _ _ hne).1` as an intermediate fact. Rewrite `this` using `[e.apply_symm_apply, e.apply_symm_apply]`. Conclude with `hτ this`. Rewrite using `[h0]`.

Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.single_eq_of_ne, mul_zero]`. Introduce `h`. Conclude with `hτ (congrArg Sigma.fst (e.symm.injective h))`.
-/
theorem col_eq_sum {T : Type} {m : T → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : T, Fin (m τ))
    (A : Matrix (Fin g) (Fin g) ℂ)
    (htri : ∀ j j', A j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) (τ : T) (i : Fin (m τ)) :
    ∑ i' : Fin (m τ), A (e.symm ⟨τ, i'⟩) (e.symm ⟨τ, i⟩) • (Pi.single (e.symm ⟨τ, i'⟩) (1 : ℂ) : Fin g → ℂ) =
      A *ᵥ Pi.single (e.symm ⟨τ, i⟩) 1 := by
  funext p
  obtain ⟨⟨τ', i'⟩, rfl⟩ := e.symm.surjective p
  rw [Matrix.mulVec_single_one, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.col_apply]
  by_cases hτ : τ' = τ
  · subst hτ
    rw [Finset.sum_eq_single i']
    · simp
    · intro j _ hj
      rw [Pi.single_eq_of_ne, mul_zero]
      intro h
      exact hj (sigma_mk_injective (β := fun τ => Fin (m τ)) (e.symm.injective h)).symm
    · intro h; exact absurd (Finset.mem_univ _) h
  · have h0 : A (e.symm ⟨τ', i'⟩) (e.symm ⟨τ, i⟩) = 0 := by
      by_contra hne
      have := (htri _ _ hne).1
      rw [e.apply_symm_apply, e.apply_symm_apply] at this
      exact hτ this
    rw [h0]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Pi.single_eq_of_ne, mul_zero]
    intro h
    exact hτ (congrArg Sigma.fst (e.symm.injective h))

/- English proof (translation)
Use `Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (div_pos (by positivity) ?_)).ne'` and prove the remaining obligations. Conclude with `Finset.prod_pos fun j _ => mul_pos two_pos (norm_pos_iff.2 ((map_ne_zero _).2 h))`.
-/
theorem normConst_ne_zero {E : Type} [Field E] {g : ℕ} (ty : Fin g → (E →+* ℂ)) {ξ₀ : E} (h : ξ₀ ≠ 0) :
    (normConst ty ξ₀ : ℂ) ≠ 0 := by
  refine Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (div_pos (by positivity) ?_)).ne'
  exact Finset.prod_pos fun j _ => mul_pos two_pos (norm_pos_iff.2 ((map_ne_zero _).2 h))

/- English proof (translation)
Introduce `hS E _ _ _ H Dw l Xo c σ g e F r M un k T hG hB hN hU x b hb h`. Take `⟨h₀, hdet, hP, htri, -, -, hw⟩` from `GlobalTheory.T.triangularFrame_moves_period_blockTriangular E H Dw l Xo c σ g e F r M hG hB hN k T.Pf T.per x.1 x.2 b hb`. Take `⟨κ, hκ, hy⟩` from `hU x`. Take `⟨κ', hκ', hy'⟩` from `hU ⟨_, h⟩`. Establish `hx : T.co.symm x.1 ∈ T.co ⁻¹' (M.X k).dom`.

Simplify `x.2` using `only [Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply]`. Establish `hx' : T.co.symm (rmul x.1 b) ∈ T.co ⁻¹' (M.X k).dom`. Simplify `h` using `only [Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply]`. Take `⟨hxx, hder, t₀, hsec, ht₀⟩` from `GlobalTheory.T.thetaPoints_change_levelIsometry_linearMap hS E H Dw l Xo c σ g e F r M k T _ hx _ hx' κ κ' _ _ (LinearEquiv.refl _ _) h₀ hy hy' ⟨fun _ _ => rfl, fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩⟩ (fun a => by`. Simplify using `only [ContinuousLinearEquiv.apply_symm_apply, LinearEquiv.refl_apply]`.

Conclude with `hP a)`. Establish `hsq : toC (t₀ : CAt σ) ^ 2 * h₀.det = 1`. Establish `hc` using `normConst_ne_zero (fun j => relab c σ (e j).1) (M.X k).ξ0_ne`. Establish `h1` using `(T.norm _ hx).1.ne_zero`. Establish `h2` using `(T.norm _ hx').1.ne_zero`.

Rewrite `ht₀` using `[hκ, hκ']`. Apply `mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hc h1) h2)` to reduce the goal to its premises. Take the linear combination `ht₀`. Establish `hinv : (h₀⁻¹).det ≠ 0` using `(Matrix.isUnit_nonsing_inv_det h₀ hdet).ne_zero`. Establish `hdiag` using `diag_ne_zero e h₀⁻¹ hinv htri`.

Set `d : Fin g → (CAt σ)ˣ` to `fun j => (Units.mk0 (h₀⁻¹ j j) (hdiag j) : ℂˣ)`. Set `t : Ix Dw → (CAt σ)ˣ` to `fun o => Option.elim o t₀ (fun p => d (e.symm p))`. Use `⟨t, ⟨hxx, fun τ i => ⟨fun i' => (h₀⁻¹ (e.symm ⟨τ, i'⟩) (e.symm ⟨τ, i⟩) : ℂ), rfl, ?_, ?_⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `j hj`. Assume the negation of the conclusion as `hne`.

Use `(htri _ _ hne).2` as an intermediate fact. Rewrite `this` using `[e.apply_symm_apply, e.apply_symm_apply]`. Conclude with `absurd hj (not_lt.2 this)`. Rewrite using `[hy.1]`. Use `(GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F k _ (T.isPer _ hx) _ _ _ (hy.2.1 τ) _ _).2 ?_` and prove the remaining obligations.

Rewrite using `[col_eq_sum e h₀⁻¹ htri]`. Conclude with `hder τ i`. Take `⟨pm, h1, h2, h3⟩` from `hsec`. Use `⟨pm, h1, ?_, h3⟩` and prove the remaining obligations. Rewrite using `[h2]`.

Simplify using `[spMap]`. Introduce `a n hD`. Rewrite using `[← hw un a n (toC (t₀ : CAt σ)) hD.2 hsq]`. Use `show (∏ o : Ix Dw, toC ((t o : (CAt σ)ˣ) : CAt σ) ^ ex Dw a n o) = _`. Rewrite using `[Fintype.prod_option, mul_comm]`.

Use `congr 1`. Rewrite using `[← Equiv.prod_comp e]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `show h₀⁻¹ (e.symm (e j)) (e.symm (e j)) ^ a ((e j).1, (e j).2) = _`. Rewrite using `[e.symm_apply_apply]`.
-/
theorem normUn_bor : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (k : Fin F.n) (T : ThetaData e F M k), GoodEmb c σ → ModelBase M → NegXi M → IsNormUn T (un k) → ∀ (x : (M.X k).dom) b (_hb : b ∈ Bor (M.X k).Ψ r) (h : rmul x.1 b ∈ (M.X k).dom), ∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (un k x) (un k ⟨_, h⟩) ∧ ∀ a n, Dom a n → toC (wchar (ex Dw a n) t) = bchar (laU (unfOf e F M un) a n k) b := by
  intro hS E _ _ _ H Dw l Xo c σ g e F r M un k T hG hB hN hU x b hb h
  obtain ⟨h₀, hdet, hP, htri, -, -, hw⟩ :=
    GlobalTheory.T.triangularFrame_moves_period_blockTriangular E H Dw l Xo c σ g e F r M hG hB hN k T.Pf T.per x.1 x.2 b hb
  obtain ⟨κ, hκ, hy⟩ := hU x
  obtain ⟨κ', hκ', hy'⟩ := hU ⟨_, h⟩
  have hx : T.co.symm x.1 ∈ T.co ⁻¹' (M.X k).dom := by
    simpa only [Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using x.2
  have hx' : T.co.symm (rmul x.1 b) ∈ T.co ⁻¹' (M.X k).dom := by
    simpa only [Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using h
  obtain ⟨hxx, hder, t₀, hsec, ht₀⟩ := GlobalTheory.T.thetaPoints_change_levelIsometry_linearMap hS E H Dw l Xo c σ g e F r M k T _ hx _ hx' κ κ' _ _
    (LinearEquiv.refl _ _) h₀ hy hy'
    ⟨fun _ _ => rfl, fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩⟩
    (fun a => by
      simp only [ContinuousLinearEquiv.apply_symm_apply, LinearEquiv.refl_apply]
      exact hP a)
  have hsq : toC (t₀ : CAt σ) ^ 2 * h₀.det = 1 := by
    have hc := normConst_ne_zero (fun j => relab c σ (e j).1) (M.X k).ξ0_ne
    have h1 := (T.norm _ hx).1.ne_zero
    have h2 := (T.norm _ hx').1.ne_zero
    rw [hκ, hκ'] at ht₀
    apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hc h1) h2)
    linear_combination ht₀
  have hinv : (h₀⁻¹).det ≠ 0 := (Matrix.isUnit_nonsing_inv_det h₀ hdet).ne_zero
  have hdiag := diag_ne_zero e h₀⁻¹ hinv htri
  let d : Fin g → (CAt σ)ˣ := fun j => (Units.mk0 (h₀⁻¹ j j) (hdiag j) : ℂˣ)
  let t : Ix Dw → (CAt σ)ˣ := fun o => Option.elim o t₀ (fun p => d (e.symm p))
  refine ⟨t, ⟨hxx, fun τ i => ⟨fun i' => (h₀⁻¹ (e.symm ⟨τ, i'⟩) (e.symm ⟨τ, i⟩) : ℂ), rfl, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro j hj
    by_contra hne
    have := (htri _ _ hne).2
    rw [e.apply_symm_apply, e.apply_symm_apply] at this
    exact absurd hj (not_lt.2 this)
  · rw [hy.1]
    refine (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F k _ (T.isPer _ hx) _ _ _ (hy.2.1 τ) _ _).2 ?_
    rw [col_eq_sum e h₀⁻¹ htri]
    exact hder τ i
  · obtain ⟨pm, h1, h2, h3⟩ := hsec
    refine ⟨pm, h1, ?_, h3⟩
    rw [h2]
    simp [spMap]
  · intro a n hD
    rw [← hw un a n (toC (t₀ : CAt σ)) hD.2 hsq]
    show (∏ o : Ix Dw, toC ((t o : (CAt σ)ˣ) : CAt σ) ^ ex Dw a n o) = _
    rw [Fintype.prod_option, mul_comm]
    congr 1
    rw [← Equiv.prod_comp e]
    refine Finset.prod_congr rfl fun j _ => ?_
    show h₀⁻¹ (e.symm (e j)) (e.symm (e j)) ^ a ((e j).1, (e j).2) = _
    rw [e.symm_apply_apply]

end GlobalTheory.NormUnBor
