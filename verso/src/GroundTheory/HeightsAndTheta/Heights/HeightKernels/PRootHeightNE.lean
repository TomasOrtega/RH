import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeightNE
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

/- English proof (translation)
Introduce `μ hμ k`. Establish `hdeg : rootAnchorSection f j m = monomial (∑ τ : Fin f, Finsupp.single (⟨τ, plAnchor j m⟩ : Σ _ : Fin f, PlIdx j m) 1) 1`. Rewrite using `[MvPolynomial.monomial_sum_one]`. Both sides reduce to the same expression. Rewrite `hμ` using `[hdeg]`.

Use `MvPolynomial.support_monomial_subset hμ` as an intermediate fact. Rewrite `this` using `[Finset.mem_singleton]`. Substitute `this` using the available equality. Simplify using `only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]`. Rewrite using `[Finset.sum_comm, Finset.sum_eq_single k]`.

Rewrite using `[Finset.sum_eq_single (plAnchor j m)]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[hb.symm]`. Simplify using the standard rewrite rules.

Introduce `τ _ hτ`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[if_neg]`. Introduce `h`.

Conclude with `hτ (congrArg Sigma.fst h)`. Simplify using the standard rewrite rules.
-/
theorem anchor_homog (f j m : ℕ) : IsMultiHomog (rootAnchorSection f j m) (fun _ => 1) := by
  classical
  intro μ hμ k
  have hdeg : rootAnchorSection f j m = monomial (∑ τ : Fin f, Finsupp.single (⟨τ, plAnchor j m⟩ : Σ _ : Fin f, PlIdx j m) 1) 1 := by
    rw [MvPolynomial.monomial_sum_one]; rfl
  rw [hdeg] at hμ
  have := MvPolynomial.support_monomial_subset hμ
  rw [Finset.mem_singleton] at this
  subst this
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
  rw [Finset.sum_comm, Finset.sum_eq_single k]
  · rw [Finset.sum_eq_single (plAnchor j m)]
    · simp
    · intro b _ hb
      simp [hb.symm]
    · simp
  · intro τ _ hτ
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    intro h
    exact hτ (congrArg Sigma.fst h)
  · simp

/- English proof (translation)
Introduce `f j m ζ hf hζ II hII`. Establish `: Nonempty (Fin f)` using `⟨⟨0, hf⟩⟩`. Establish `hV` using `hA f j m ζ hf hζ`. Establish `hmem : rootAnchorSection f j m ∉ rootPointIdeal ζ`. Rewrite using `[rootPointIdeal, hM (Fin f) (plBlocks f j m) ℂ (rootCoord ζ) _ _ (anchor_homog f j m)]`.

Simplify using `[rootAnchorSection, rootCoord, anchor_minor]`. Establish `hsm : IsSmoothHerm (fsMulti (plBlocks f j m))` using `hS _ _`. Establish `hR` using `(hII (Fin f) (plBlocks f j m)).2.2 (rootPointIdeal ζ) 0 Fin.elim0 (fsMulti (plBlocks f j m)) (rootAnchorSection f j m) (fun _ => 1) hV (fun j => j.elim0) hsm (fun _ => by simp [fsMulti, HermLine.ofMetrics]) (anchor_homog f j m) hmem`. Establish `e1 : (Fin.snoc (Fin.elim0 : Fin 0 → HermLine (plBlocks f j m)) (fsMulti (plBlocks f j m)) : Fin (0 + 1) → HermLine (plBlocks f j m)) = ![fsMulti (plBlocks f j m)]`. Use function extensionality and compare the values at `i`.

Use `fin_cases i`. Both sides reduce to the same expression. Rewrite `hR` using `[e1]`. Establish `hlow` using `hP (Fin f) (plBlocks f j m) (rootPointIdeal ζ) (fun i z => Real.log (((Fin.elim0 : Fin 0 → HermLine (plBlocks f j m)) i).h z)) (logNorm (fsMulti (plBlocks f j m)) (rootAnchorSection f j m)) (-grassConst f j m) hV.2.1.2.1 (hF f j m ζ hζ) ?_ (hL f j m ζ hζ)`. Establish `: recR (II (Fin f) (plBlocks f j m)) (rootPointIdeal ζ) (Fin.elim0 : Fin 0 → HermLine (plBlocks f j m)) (fsMulti (plBlocks f j m)) (rootAnchorSection f j m) = - arInt (rootPointIdeal ζ) (rootAnchorSection f j m) (fsMulti (plBlocks f j m)) Fin.elim0`.

Simplify using `[recR, hD f j m ζ hζ]`. Rewrite `hR` using `[this]`. Use `show II _ _ _ 1 _ ≤ _`. Rewrite using `[hR]`. Simplify using `only [arInt]`.

Use `hlow` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Introduce `u z hu hz`. Establish `hh` using `(fsMulti (plBlocks f j m)).smul u z hu`. Establish `hpos` using `(fsMulti (plBlocks f j m)).pos z hz.1`.

Establish `hfa : (fsMulti (plBlocks f j m)).a = fun _ => 1` using `rfl`. Simplify using `only [logNorm, hh, hfa, zpow_one]`. Establish `hs : eval (fun p : (Σ _ : Fin f, PlIdx j m) => u p.1 * z p) (map (Int.castRingHom ℂ) (rootAnchorSection f j m)) = (∏ k, u k) * eval z (map (Int.castRingHom ℂ) (rootAnchorSection f j m))`. Simplify using `[rootAnchorSection, Finset.prod_mul_distrib]`. Establish `hu0 : (∏ k, ‖u k‖) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => norm_ne_zero_iff.mpr (hu k)`.

Use `congr 1`. Use `erw [hs]`. Rewrite using `[norm_mul, norm_prod]`. Clear the denominators using the available nonvanishing facts.
-/
theorem RootHeight.proofNE (hA : RootArithVar.Statement) (hD : RootDivSuppEmpty.Statement)
    (hL : RootLogNormBound.Statement) (hF : RootPointsFinite.Statement) (hP : PtsIntegralZeroLowerNE.Statement)
    (hM : MultiHomogMemCoord.Statement) (hS : FsLineSmooth.Statement) : RootHeight.Statement := by
  intro f j m ζ hf hζ II hII
  have : Nonempty (Fin f) := ⟨⟨0, hf⟩⟩
  have hV := hA f j m ζ hf hζ
  have hmem : rootAnchorSection f j m ∉ rootPointIdeal ζ := by
    rw [rootPointIdeal, hM (Fin f) (plBlocks f j m) ℂ (rootCoord ζ) _ _ (anchor_homog f j m)]
    simp [rootAnchorSection, rootCoord, anchor_minor]
  have hsm : IsSmoothHerm (fsMulti (plBlocks f j m)) := hS _ _
  have hR := (hII (Fin f) (plBlocks f j m)).2.2 (rootPointIdeal ζ) 0 Fin.elim0
    (fsMulti (plBlocks f j m)) (rootAnchorSection f j m) (fun _ => 1) hV (fun j => j.elim0) hsm
    (fun _ => by simp [fsMulti, HermLine.ofMetrics]) (anchor_homog f j m) hmem
  have e1 : (Fin.snoc (Fin.elim0 : Fin 0 → HermLine (plBlocks f j m)) (fsMulti (plBlocks f j m)) :
      Fin (0 + 1) → HermLine (plBlocks f j m)) = ![fsMulti (plBlocks f j m)] := by
    funext i; fin_cases i; rfl
  rw [e1] at hR
  have hlow := hP (Fin f) (plBlocks f j m) (rootPointIdeal ζ)
    (fun i z => Real.log (((Fin.elim0 : Fin 0 → HermLine (plBlocks f j m)) i).h z))
    (logNorm (fsMulti (plBlocks f j m)) (rootAnchorSection f j m)) (-grassConst f j m)
    hV.2.1.2.1 (hF f j m ζ hζ) ?_ (hL f j m ζ hζ)
  · have : recR (II (Fin f) (plBlocks f j m)) (rootPointIdeal ζ)
        (Fin.elim0 : Fin 0 → HermLine (plBlocks f j m)) (fsMulti (plBlocks f j m)) (rootAnchorSection f j m) =
        - arInt (rootPointIdeal ζ) (rootAnchorSection f j m) (fsMulti (plBlocks f j m)) Fin.elim0 := by
      simp [recR, hD f j m ζ hζ]
    rw [this] at hR
    show II _ _ _ 1 _ ≤ _
    rw [hR]
    simp only [arInt]
    have := hlow
    nlinarith
  · intro u z hu hz
    have hh := (fsMulti (plBlocks f j m)).smul u z hu
    have hpos := (fsMulti (plBlocks f j m)).pos z hz.1
    have hfa : (fsMulti (plBlocks f j m)).a = fun _ => 1 := rfl
    simp only [logNorm, hh, hfa, zpow_one]
    have hs : eval (fun p : (Σ _ : Fin f, PlIdx j m) => u p.1 * z p) (map (Int.castRingHom ℂ) (rootAnchorSection f j m))
        = (∏ k, u k) * eval z (map (Int.castRingHom ℂ) (rootAnchorSection f j m)) := by
      simp [rootAnchorSection, Finset.prod_mul_distrib]
    have hu0 : (∏ k, ‖u k‖) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => norm_ne_zero_iff.mpr (hu k)
    congr 1
    erw [hs]
    rw [norm_mul, norm_prod]
    field_simp

end

end GroundTheory.Heights₂.Heights
