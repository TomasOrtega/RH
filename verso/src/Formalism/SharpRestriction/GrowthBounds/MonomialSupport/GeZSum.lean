import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.RestPlOf
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.LowestWeightCNonpos
import Formalism.SharpRestriction.GrowthBounds.RootWeights.ValuationBoundDetPowerFactor
import Formalism.SharpRestriction.GrowthBounds.RootWeights.DerivativeValuationBounds

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.LetterSubstitution

open Formalism.MainNotions.G Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideWords Formalism.MainNotions.Proposition5Numerics Formalism.MainNotions.PairMembershipBlocks

/- English proof (translation)
Introduce `R _ _ ι n _ LL S F hF`. Set `Good : Set (ι × Fin n)` to `{v | v.1 ∈ S → LL.vec v.1 = true}`. Establish `hmem : F ∈ supported R Good`. Rewrite using `[mem_supported]`. Introduce `v hv`.

Conclude with `hF v (Finset.mem_coe.1 hv)`. Use `clear hF`. Rewrite `hmem` using `[supported_eq_adjoin_X]`. Proceed by induction on `hmem using Algebra.adjoin_induction with`. Consider the case `mem x hx`.

Take `⟨v, hv, rfl⟩` from `hx`. Establish `h1` using `Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.valS_X_mul_of LL S (1 : MvPolynomial (ι × Fin n) R) v hv`. Rewrite `h1` using `[mul_one]`. Use `le_trans ?_ h1` and prove the remaining obligations. Use `valS_C_nnR (n := n) LL S (1 : R)` as an intermediate fact.

Rewrite `this` using `[C_1]`. Then use the resulting hypothesis. Consider the case `algebraMap c`. Conclude with `valS_C_nnR LL S c`. Consider the case `add x y _ _ hx hy`. Conclude with `le_trans (le_min hx hy) (Formalism.MainNotions.G.GLWeightTheory.mul_valS_add LL S x y)`.

Consider the case `mul x y _ _ hx hy`. Conclude with `le_trans (add_nonneg hx hy) (Formalism.MainNotions.G.GLWeightTheory.flt_valS_mul_ge LL S x y)`.
-/
theorem valNN : ValNN := by
  intro R _ _ ι n _ LL S F hF
  let Good : Set (ι × Fin n) := {v | v.1 ∈ S → LL.vec v.1 = true}
  have hmem : F ∈ supported R Good := by
    rw [mem_supported]
    intro v hv
    exact hF v (Finset.mem_coe.1 hv)
  clear hF
  rw [supported_eq_adjoin_X] at hmem
  induction hmem using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    have h1 := Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.valS_X_mul_of LL S (1 : MvPolynomial (ι × Fin n) R) v hv
    rw [mul_one] at h1
    refine le_trans ?_ h1
    have := valS_C_nnR (n := n) LL S (1 : R)
    rwa [C_1] at this
  | algebraMap c =>
    exact valS_C_nnR LL S c
  | add x y _ _ hx hy =>
    exact le_trans (le_min hx hy) (Formalism.MainNotions.G.GLWeightTheory.mul_valS_add LL S x y)
  | mul x y _ _ hx hy =>
    exact le_trans (add_nonneg hx hy) (Formalism.MainNotions.G.GLWeightTheory.flt_valS_mul_ge LL S x y)

/- English proof (translation)
Introduce `R _ ι n F`. Use `⟨F.support.image (fun mo => multideg mo), ?_⟩` and prove the remaining obligations. Establish `key` using `Finset.sum_fiberwise_of_maps_to (s := F.support) (t := F.support.image fun mo => multideg mo) (g := fun mo => multideg mo) (fun mo hmo => Finset.mem_image_of_mem _ hmo) (fun mo => monomial mo (F.coeff mo))`. Rewrite `key` using `[F.support_sum_monomial_coeff]`. Use `conv_lhs => rw [← key]`.

Use `Finset.sum_congr rfl (fun δ _ => ?_)` and prove the remaining obligations. Simplify using `only [homComp]`. Use `Finset.sum_congr ?_ (fun _ _ => rfl)` and prove the remaining obligations. Use extensionality with `mo`. Simplify using `only [Finset.mem_filter, funext_iff]`.
-/
theorem homDec : HomDec := by
  intro R _ ι n F
  refine ⟨F.support.image (fun mo => multideg mo), ?_⟩
  have key := Finset.sum_fiberwise_of_maps_to (s := F.support) (t := F.support.image fun mo => multideg mo)
    (g := fun mo => multideg mo) (fun mo hmo => Finset.mem_image_of_mem _ hmo) (fun mo => monomial mo (F.coeff mo))
  rw [F.support_sum_monomial_coeff] at key
  conv_lhs => rw [← key]
  refine Finset.sum_congr rfl (fun δ _ => ?_)
  simp only [homComp]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext mo
  simp only [Finset.mem_filter, funext_iff]

/- English proof (translation)
Introduce `k hk`. Unfold `valS at hk`. Distinguish the cases in `hne : (sDegs LL S (lastIdx n) (∑ i ∈ s, f i)).Nonempty`. Take `⟨d, hd, he⟩` from `Finset.exists_mem_eq_inf _ hne (fun k : ℤ => (k : WithTop ℤ))`. Rewrite `hk` using `[he]`.

Establish `hkd : d = k` using `WithTop.coe_injective hk`. Substitute `hkd` using the available equality. Simplify using `only [sDegs, Finset.mem_biUnion, map_sum, MvPolynomial.coeff_sum] at hd`. Take `⟨m, -, hdm⟩` from `hd`. Rewrite `hdm` using `[Finsupp.mem_support_iff]`.

Establish `hdm' : ∑ i ∈ s, ((MvPolynomial.coeff m (twistSub LL S (lastIdx n) (f i))).coeff d) ≠ 0`. Simplify `hdm` using `[AddMonoidAlgebra.coeff, Finsupp.finset_sum_apply]`. Take `⟨i, hi, hne'⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hdm'`. Establish `hmem : d ∈ sDegs LL S (lastIdx n) (f i)`. Simplify using `only [sDegs, Finset.mem_biUnion]`.

Use `⟨m, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.mem_support_iff]`. Introduce `h0`. Apply `hne'` to reduce the goal to its premises. Rewrite using `[h0]`.

Both sides reduce to the same expression. Rewrite using `[Finsupp.mem_support_iff]`. Conclude with `hne'`. Establish `hle : valS LL S (f i) ≤ (d : WithTop ℤ)` using `Finset.inf_le (f := fun k : ℤ => (k : WithTop ℤ)) hmem`. Consider the cases of `hv : valS LL S (f i) with`.

Consider the case `top => rw [hv] at hle; exact absurd hle (by simp)`. Consider the case `coe k'`. Rewrite `hle` using `[hv]`. Establish `hk' : k' ≤ d` using `WithTop.coe_le_coe.1 hle`. Use `h i hi k' hv` as an intermediate fact.

Conclude with `this.trans (by exact_mod_cast hk')`. Rewrite `hne` using `[Finset.not_nonempty_iff_eq_empty]`. Rewrite `hk` using `[hne, Finset.inf_empty]`. Conclude with `absurd hk (by simp)`.
-/
theorem geZ_sum {R : Type} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι) {κ : Type*}
    (s : Finset κ) (f : κ → MvPolynomial (ι × Fin n) R) (t : ℝ)
    (h : ∀ i ∈ s, geZ (valS LL S (f i)) t) : geZ (valS LL S (∑ i ∈ s, f i)) t := by
  intro k hk
  unfold valS at hk
  by_cases hne : (sDegs LL S (lastIdx n) (∑ i ∈ s, f i)).Nonempty
  · obtain ⟨d, hd, he⟩ := Finset.exists_mem_eq_inf _ hne (fun k : ℤ => (k : WithTop ℤ))
    rw [he] at hk
    have hkd : d = k := WithTop.coe_injective hk
    subst hkd
    simp only [sDegs, Finset.mem_biUnion, map_sum, MvPolynomial.coeff_sum] at hd
    obtain ⟨m, -, hdm⟩ := hd
    rw [Finsupp.mem_support_iff] at hdm
    have hdm' : ∑ i ∈ s, ((MvPolynomial.coeff m (twistSub LL S (lastIdx n) (f i))).coeff d) ≠ 0 := by
      simpa [AddMonoidAlgebra.coeff, Finsupp.finset_sum_apply] using hdm
    obtain ⟨i, hi, hne'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hdm'
    have hmem : d ∈ sDegs LL S (lastIdx n) (f i) := by
      simp only [sDegs, Finset.mem_biUnion]
      refine ⟨m, ?_, ?_⟩
      · rw [MvPolynomial.mem_support_iff]
        intro h0
        apply hne'
        rw [h0]
        rfl
      · rw [Finsupp.mem_support_iff]
        exact hne'
    have hle : valS LL S (f i) ≤ (d : WithTop ℤ) := Finset.inf_le (f := fun k : ℤ => (k : WithTop ℤ)) hmem
    cases hv : valS LL S (f i) with
    | top => rw [hv] at hle; exact absurd hle (by simp)
    | coe k' =>
      rw [hv] at hle
      have hk' : k' ≤ d := WithTop.coe_le_coe.1 hle
      have := h i hi k' hv
      exact this.trans (by exact_mod_cast hk')
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.inf_empty] at hk
    exact absurd hk (by simp)

end Formalism.MainNotions.LetterSubstitution
