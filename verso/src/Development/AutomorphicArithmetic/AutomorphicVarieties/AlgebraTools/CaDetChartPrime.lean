import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CotInd
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DetLocus
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetChartCot
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaPolyReg
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCotQuot

open IsLocalRing UpperTheory.V.AlgebraTools

/- English proof (translation)
Introduce `P _ _ ι _ _ z m hx c Q _ hQ`. Take `⟨_, hcot⟩` from `regular_polynomial_localization P ι Q hQ`. Set `φ : MvPolynomial ι P →+* Localization.AtPrime Q` to `algebraMap _ _`. Set `w : ι → Localization.AtPrime Q` to `fun j => φ (MvPolynomial.C (m j))`. Set `l : ι → Localization.AtPrime Q` to `fun j => φ (lam P c j)`.

Set `y : Matrix ι ι (Localization.AtPrime Q)` to `z.map (φ.comp MvPolynomial.C)`. Establish `h1 : CotInd (Localization.AtPrime Q) (Sum.elim (fun ij : ι × ι => y ij.1 ij.2) w)`. Establish `h` using `hcot _ _ hx`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`.

Apply the tactic sequence `rcases k with k | k <;> rfl`. Establish `hl : l c = 1`. Simplify using `[l, lam]`. Establish `h2` using `chartGen_cotInd (Localization.AtPrime Q) ι y w l c h1 hl`. Establish `h3` using `(regular_quotient_cotInd (Localization.AtPrime Q) _ _ h2).2.2`.

Establish `hf : ⇑φ ∘ chartGen z m c = Sum.elim (y.mulVec l) fun j : {j : ι // j ≠ c} => w j - l j * w c`. Use function extensionality and compare the values at `k`. Break down `k with k | k` into its components or cases. Simplify using `only [Function.comp, chartGen, Sum.elim_inl]`. Rewrite using `[RingHom.map_mulVec, Matrix.map_map]`.

Both sides reduce to the same expression. Simplify using `[chartGen, w, l]`. Establish `key : (chartIdeal z m c).map φ = Ideal.span (Set.range (Sum.elim (y.mulVec l) fun j : {j : ι // j ≠ c} => w j - l j * w c))`. Rewrite using `[chartIdeal, Ideal.map_span, ← Set.range_comp, hf]`. Conclude with `key ▸ h3`.
-/
theorem UpperTheory.V.AlgebraTools.chartIdeal_localization_isPrime :
    ∀ (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P),
      CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) →
      ∀ (c : ι) (Q : Ideal (MvPolynomial ι P)) [Q.IsPrime],
      (maximalIdeal P).map (MvPolynomial.C : P →+* MvPolynomial ι P) ≤ Q →
      ((chartIdeal z m c).map (algebraMap _ (Localization.AtPrime Q))).IsPrime := by
  intro P _ _ ι _ _ z m hx c Q _ hQ
  obtain ⟨_, hcot⟩ := regular_polynomial_localization P ι Q hQ
  let φ : MvPolynomial ι P →+* Localization.AtPrime Q := algebraMap _ _
  let w : ι → Localization.AtPrime Q := fun j => φ (MvPolynomial.C (m j))
  let l : ι → Localization.AtPrime Q := fun j => φ (lam P c j)
  let y : Matrix ι ι (Localization.AtPrime Q) := z.map (φ.comp MvPolynomial.C)
  have h1 : CotInd (Localization.AtPrime Q) (Sum.elim (fun ij : ι × ι => y ij.1 ij.2) w) := by
    have h := hcot _ _ hx
    convert h using 1
    funext k
    rcases k with k | k <;> rfl
  have hl : l c = 1 := by
    simp [l, lam]
  have h2 := chartGen_cotInd (Localization.AtPrime Q) ι y w l c h1 hl
  have h3 := (regular_quotient_cotInd (Localization.AtPrime Q) _ _ h2).2.2
  have hf : ⇑φ ∘ chartGen z m c = Sum.elim (y.mulVec l) fun j : {j : ι // j ≠ c} => w j - l j * w c := by
    funext k
    rcases k with k | k
    · simp only [Function.comp, chartGen, Sum.elim_inl]
      rw [RingHom.map_mulVec, Matrix.map_map]
      rfl
    · simp [chartGen, w, l]
  have key : (chartIdeal z m c).map φ =
      Ideal.span (Set.range (Sum.elim (y.mulVec l) fun j : {j : ι // j ≠ c} => w j - l j * w c)) := by
    rw [chartIdeal, Ideal.map_span, ← Set.range_comp, hf]
  exact key ▸ h3
