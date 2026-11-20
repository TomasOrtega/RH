import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsGrassHeightE
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Assembly
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootHeightNE
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights MvPolynomial Matrix

noncomputable section

namespace GrassHeightEAux

/- English proof (translation)
Use `set S : ℝ := ∑ I : PlIdx j m, ‖(colsOf (onePipe Z) I).det‖ ^ 2 with hSdef`. Establish `hS0 : 0 ≤ S` using `Finset.sum_nonneg fun _ _ => sq_nonneg _`. Establish `hnorm : ‖WithLp.toLp 2 v‖ = ‖a‖ * Real.sqrt S`. Rewrite using `[EuclideanSpace.norm_eq]`. Establish `hs : ∑ I, ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (PlIdx j m)) I‖ ^ 2 = ‖a‖ ^ 2 * S`.

Rewrite using `[hSdef, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun I _ => ?_` and prove the remaining obligations. Simplify using `[hv, mul_pow]`. Rewrite using `[hs, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]`. Establish `ha' : 0 < ‖a‖` using `norm_pos_iff.mpr ha`.

Establish `hdet : S = (1 + Z * Zᴴ).det.re`. Rewrite using `[← PlueckerNormSq.full j m Z, Complex.ofReal_re]`. Establish `hb` using `he Zᴴ fun a b => by rw [conjTranspose_apply, norm_star, hZ b a]`. Rewrite `hb` using `[conjTranspose_conjTranspose, det_one_add_mul_comm, ← hdet]`. Rewrite using `[hnorm, div_mul_cancel_left₀ ha'.ne', Real.log_inv, Real.log_sqrt hS0]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem log_block (j m : ℕ) (e : ℝ) (he : UnitDetBound m j e) (Z : Matrix (Fin j) (Fin m) ℂ)
    (hZ : ∀ a b, ‖Z a b‖ = 1) (a : ℂ) (ha : a ≠ 0) (v : PlIdx j m → ℂ)
    (hv : ∀ I, v I = a * (colsOf (onePipe Z) I).det) :
    -e ≤ Real.log (‖a‖ / ‖WithLp.toLp 2 v‖) := by
  set S : ℝ := ∑ I : PlIdx j m, ‖(colsOf (onePipe Z) I).det‖ ^ 2 with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hnorm : ‖WithLp.toLp 2 v‖ = ‖a‖ * Real.sqrt S := by
    rw [EuclideanSpace.norm_eq]
    have hs : ∑ I, ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (PlIdx j m)) I‖ ^ 2 = ‖a‖ ^ 2 * S := by
      rw [hSdef, Finset.mul_sum]
      refine Finset.sum_congr rfl fun I _ => ?_
      simp [hv, mul_pow]
    rw [hs, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hdet : S = (1 + Z * Zᴴ).det.re := by
    rw [← PlueckerNormSq.full j m Z, Complex.ofReal_re]
  have hb := he Zᴴ fun a b => by rw [conjTranspose_apply, norm_star, hZ b a]
  rw [conjTranspose_conjTranspose, det_one_add_mul_comm, ← hdet] at hb
  rw [hnorm, div_mul_cancel_left₀ ha'.ne', Real.log_inv, Real.log_sqrt hS0]
  linarith

end GrassHeightEAux

open GrassHeightEAux in

/- English proof (translation)
Introduce `f j m e ζ he hζ z hz`. Establish `h₁` using `RootAnchorNonzero.proof`. Establish `hpos : ∀ τ : Fin f, 0 < ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖` using `fun τ => (fsMetric (PlIdx j m)).pos _ fun h0 => by`. Take `⟨i, hi⟩` from `hz.1 τ`. Conclude with `hi (congrFun h0 i)`.

Establish `key : ∀ τ : Fin f, -e ≤ Real.log (‖z ⟨τ, plAnchor j m⟩‖ / ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖)`. Introduce `τ`. Take `⟨ζ', hζ', hz'⟩` from `RootPointConj.full f j m ζ hζ z hz τ`. Conclude with `log_block j m e he ζ' (fun a b => by`. Take `⟨k, hk, h⟩` from `hζ' a b`.

Conclude with `Complex.norm_eq_one_of_pow_eq_one h hk.ne')`. Use `_ (h₁ f j m ζ hζ z hz τ) _ hz'`. Establish `hne : ∀ τ ∈ (Finset.univ : Finset (Fin f)), ‖z ⟨τ, plAnchor j m⟩‖ / ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖ ≠ 0` using `fun τ _ => div_ne_zero (norm_ne_zero_iff.mpr (h₁ f j m ζ hζ z hz τ)) (hpos τ).ne'`. Establish `e' : logNorm (fsMulti (plBlocks f j m)) (rootAnchorSection f j m) z = ∑ τ, Real.log (‖z ⟨τ, plAnchor j m⟩‖ / ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖)`. Rewrite using `[← Real.log_prod hne]`.

Simplify using `[logNorm, fsMulti, HermLine.ofMetrics, fsMetric, rootAnchorSection, Finset.prod_div_distrib]`. Rewrite using `[e']`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ _ := Finset.sum_le_sum fun τ _ => key τ`.
-/
theorem RootLogNormBoundE.full : RootLogNormBoundE.Statement := by
  intro f j m e ζ he hζ z hz
  have h₁ := RootAnchorNonzero.proof
  have hpos : ∀ τ : Fin f, 0 < ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖ := fun τ =>
    (fsMetric (PlIdx j m)).pos _ fun h0 => by
      obtain ⟨i, hi⟩ := hz.1 τ
      exact hi (congrFun h0 i)
  have key : ∀ τ : Fin f, -e ≤
      Real.log (‖z ⟨τ, plAnchor j m⟩‖ / ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖) := by
    intro τ
    obtain ⟨ζ', hζ', hz'⟩ := RootPointConj.full f j m ζ hζ z hz τ
    exact log_block j m e he ζ' (fun a b => by
        obtain ⟨k, hk, h⟩ := hζ' a b
        exact Complex.norm_eq_one_of_pow_eq_one h hk.ne')
      _ (h₁ f j m ζ hζ z hz τ) _ hz'
  have hne : ∀ τ ∈ (Finset.univ : Finset (Fin f)),
      ‖z ⟨τ, plAnchor j m⟩‖ / ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖ ≠ 0 := fun τ _ =>
    div_ne_zero (norm_ne_zero_iff.mpr (h₁ f j m ζ hζ z hz τ)) (hpos τ).ne'
  have e' : logNorm (fsMulti (plBlocks f j m)) (rootAnchorSection f j m) z =
      ∑ τ, Real.log (‖z ⟨τ, plAnchor j m⟩‖ / ‖WithLp.toLp 2 (fun I : PlIdx j m => z ⟨τ, I⟩)‖) := by
    rw [← Real.log_prod hne]
    simp [logNorm, fsMulti, HermLine.ofMetrics, fsMetric, rootAnchorSection, Finset.prod_div_distrib]
  rw [e']
  calc -((f : ℝ) * e) = ∑ _τ : Fin f, -e := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    _ ≤ _ := Finset.sum_le_sum fun τ _ => key τ

/- English proof (translation)
Introduce `f j m e ζ hf he hζ II hII`. Establish `: Nonempty (Fin f)` using `⟨⟨0, hf⟩⟩`. Establish `hV` using `RootArithVar.full f j m ζ hf hζ`. Establish `hmem : rootAnchorSection f j m ∉ rootPointIdeal ζ`. Rewrite using `[rootPointIdeal, MultiHomogMemCoord.proof (Fin f) (plBlocks f j m) ℂ (rootCoord ζ) _ _ (anchor_homog f j m)]`.

Simplify using `[rootAnchorSection, rootCoord, anchor_minor]`. Establish `hsm : IsSmoothHerm (fsMulti (plBlocks f j m))` using `FsLineSmooth.proof _ _`. Establish `hR` using `(hII (Fin f) (plBlocks f j m)).2.2 (rootPointIdeal ζ) 0 Fin.elim0 (fsMulti (plBlocks f j m)) (rootAnchorSection f j m) (fun _ => 1) hV (fun j => j.elim0) hsm (fun _ => by simp [fsMulti, HermLine.ofMetrics]) (anchor_homog f j m) hmem`. Establish `e1 : (Fin.snoc (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (plBlocks f j m)) (fsMulti (plBlocks f j m)) : Fin (0 + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (plBlocks f j m)) = ![fsMulti (plBlocks f j m)]`. Use function extensionality and compare the values at `i`.

Use `fin_cases i`. Both sides reduce to the same expression. Rewrite `hR` using `[e1]`. Establish `hlow` using `PtsIntegralZeroLowerNE.proof (Fin f) (plBlocks f j m) (rootPointIdeal ζ) (fun i z => Real.log (((Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (plBlocks f j m)) i).h z)) (logNorm (fsMulti (plBlocks f j m)) (rootAnchorSection f j m)) (-((f : ℝ) * e)) hV.2.1 …`. Establish `: recR (II (Fin f) (plBlocks f j m)) (rootPointIdeal ζ) (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (plBlocks f j m)) (fsMulti (plBlocks f j m)) (rootAnchorSection f j m) = - arInt (rootPointIdeal ζ) (rootAnchorSection f j m) (fsMulti (plBlocks f j m)) …`.

Simplify using `[recR, RootDivSuppEmpty.proof f j m ζ hζ]`. Rewrite `hR` using `[this]`. Use `show II _ _ _ 1 _ ≤ _`. Rewrite using `[hR]`. Simplify using `only [arInt]`.

Use `hlow` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Introduce `u z hu hz`. Establish `hh` using `(fsMulti (plBlocks f j m)).smul u z hu`. Establish `hfa : (fsMulti (plBlocks f j m)).a = fun _ => 1` using `rfl`.

Simplify using `only [logNorm, hh, hfa, zpow_one]`. Establish `hs : eval (fun p : (Σ _ : Fin f, PlIdx j m) => u p.1 * z p) (map (Int.castRingHom ℂ) (rootAnchorSection f j m)) = (∏ k, u k) * eval z (map (Int.castRingHom ℂ) (rootAnchorSection f j m))`. Simplify using `[rootAnchorSection, Finset.prod_mul_distrib]`. Establish `hu0 : (∏ k, ‖u k‖) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => norm_ne_zero_iff.mpr (hu k)`. Use `congr 1`.

Use `erw [hs]`. Rewrite using `[norm_mul, norm_prod]`. Clear the denominators using the available nonvanishing facts.
-/
theorem RootHeightE.full : RootHeightE.Statement := by
  intro f j m e ζ hf he hζ II hII
  have : Nonempty (Fin f) := ⟨⟨0, hf⟩⟩
  have hV := RootArithVar.full f j m ζ hf hζ
  have hmem : rootAnchorSection f j m ∉ rootPointIdeal ζ := by
    rw [rootPointIdeal, MultiHomogMemCoord.proof (Fin f) (plBlocks f j m) ℂ (rootCoord ζ) _ _ (anchor_homog f j m)]
    simp [rootAnchorSection, rootCoord, anchor_minor]
  have hsm : IsSmoothHerm (fsMulti (plBlocks f j m)) := FsLineSmooth.proof _ _
  have hR := (hII (Fin f) (plBlocks f j m)).2.2 (rootPointIdeal ζ) 0 Fin.elim0
    (fsMulti (plBlocks f j m)) (rootAnchorSection f j m) (fun _ => 1) hV (fun j => j.elim0) hsm
    (fun _ => by simp [fsMulti, HermLine.ofMetrics]) (anchor_homog f j m) hmem
  have e1 : (Fin.snoc (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (plBlocks f j m)) (fsMulti (plBlocks f j m)) :
      Fin (0 + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (plBlocks f j m)) = ![fsMulti (plBlocks f j m)] := by
    funext i; fin_cases i; rfl
  rw [e1] at hR
  have hlow := PtsIntegralZeroLowerNE.proof (Fin f) (plBlocks f j m) (rootPointIdeal ζ)
    (fun i z => Real.log (((Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (plBlocks f j m)) i).h z))
    (logNorm (fsMulti (plBlocks f j m)) (rootAnchorSection f j m)) (-((f : ℝ) * e))
    hV.2.1.2.1 (RootPointsFinite.full f j m ζ hζ) ?_ (RootLogNormBoundE.full f j m e ζ he hζ)
  · have : recR (II (Fin f) (plBlocks f j m)) (rootPointIdeal ζ)
        (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (plBlocks f j m)) (fsMulti (plBlocks f j m)) (rootAnchorSection f j m) =
        - arInt (rootPointIdeal ζ) (rootAnchorSection f j m) (fsMulti (plBlocks f j m)) Fin.elim0 := by
      simp [recR, RootDivSuppEmpty.proof f j m ζ hζ]
    rw [this] at hR
    show II _ _ _ 1 _ ≤ _
    rw [hR]
    simp only [arInt]
    have := hlow
    nlinarith
  · intro u z hu hz
    have hh := (fsMulti (plBlocks f j m)).smul u z hu
    have hfa : (fsMulti (plBlocks f j m)).a = fun _ => 1 := rfl
    simp only [logNorm, hh, hfa, zpow_one]
    have hs : eval (fun p : (Σ _ : Fin f, PlIdx j m) => u p.1 * z p)
        (map (Int.castRingHom ℂ) (rootAnchorSection f j m))
        = (∏ k, u k) * eval z (map (Int.castRingHom ℂ) (rootAnchorSection f j m)) := by
      simp [rootAnchorSection, Finset.prod_mul_distrib]
    have hu0 : (∏ k, ‖u k‖) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => norm_ne_zero_iff.mpr (hu k)
    congr 1
    erw [hs]
    rw [norm_mul, norm_prod]
    field_simp

/- English proof (translation)
Introduce `hZ2 f j m e hf he II hII`. Use `hZ2 (Fin f) (plBlocks f j m) (grassIdeal f j m) ⊥ (f * j * m) (fsMulti (plBlocks f j m)) ((f : ℝ) * e) (rootFamily f j m) II hII (GrassArithVar.full f j m hf) bot_le (FsLineSemipositive.full _ _ _) (NefOfNonneg.proof _ _ _ _ fun _ => ?_) (FsConjInvariant.proof _ _) ?_ (RootDense. …` and prove the remaining obligations. Use `show (0 : ℤ) ≤ 1`. Conclude with `zero_le_one`. Introduce and unpack `W ⟨ζ, hζ, rfl⟩`.

Conclude with `⟨RootArithVar.full f j m ζ hf hζ, GrassLeRoot.proof f j m ζ, RootHeightE.full f j m e ζ hf he hζ II hII⟩`.
-/
theorem GrassHeightE.full : GrassHeightE.Statement := by
  intro hZ2 f j m e hf he II hII
  refine hZ2 (Fin f) (plBlocks f j m) (grassIdeal f j m) ⊥ (f * j * m) (fsMulti (plBlocks f j m))
    ((f : ℝ) * e) (rootFamily f j m) II hII (GrassArithVar.full f j m hf) bot_le
    (FsLineSemipositive.full _ _ _) (NefOfNonneg.proof _ _ _ _ fun _ => ?_) (FsConjInvariant.proof _ _) ?_
    (RootDense.full f j m)
  · show (0 : ℤ) ≤ 1
    exact zero_le_one
  · rintro W ⟨ζ, hζ, rfl⟩
    exact ⟨RootArithVar.full f j m ζ hf hζ, GrassLeRoot.proof f j m ζ, RootHeightE.full f j m e ζ hf he hζ II hII⟩

end

end GroundTheory.Heights₂.Heights.LowerBoundFree
