import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver)

noncomputable section

section Homog

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]`. Simplify using `[NumbersDVR.blockWeight, Pi.single_apply]`.
-/
theorem sum_block_eq_blockWeight (e : (Σ k, ι k) →₀ ℕ) (k : K) :
    ∑ i, e ⟨k, i⟩ = Finsupp.weight (NumbersDVR.blockWeight ι) e k := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
  simp [NumbersDVR.blockWeight, Pi.single_apply]

omit [DecidableEq K] in

/- English proof (translation)
Use `conv_lhs => rw [f.as_sum]`. Use `conv_rhs => rw [f.as_sum]`. Rewrite using `[map_sum, map_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun e he => ?_` and prove the remaining obligations. Establish `hX : ∏ p : (Σ k, ι k), (MvPolynomial.X p.1 : MvPolynomial K Ω) ^ e p = ∏ k, MvPolynomial.X k ^ d k`.

Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `show ∏ i, (MvPolynomial.X k : MvPolynomial K Ω) ^ e ⟨k, i⟩ = _`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hf e he k]`. Simplify using `only [mConeMapOver, aeval_monomial]`.

Rewrite using `[Finsupp.prod_fintype _ _ (fun i => by simp), Finsupp.prod_fintype _ _ (fun i => by simp)]`. Simplify using `only [mul_pow, Finset.prod_mul_distrib, hX, map_mul, map_prod, map_pow, MvPolynomial.algebraMap_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mConeMapOver_eq_of_block (y : (Σ k, ι k) → Ω) {f : MvPolynomial (Σ k, ι k) S} {d : K → ℕ}
    (hf : ∀ e ∈ f.support, ∀ k, ∑ i, e ⟨k, i⟩ = d k) :
    mConeMapOver S y f = MvPolynomial.C (aeval y f) * ∏ k, MvPolynomial.X k ^ d k := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun e he => ?_
  have hX : ∏ p : (Σ k, ι k), (MvPolynomial.X p.1 : MvPolynomial K Ω) ^ e p =
      ∏ k, MvPolynomial.X k ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (MvPolynomial.X k : MvPolynomial K Ω) ^ e ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hf e he k]
  simp only [mConeMapOver, aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun i => by simp), Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, hX, map_mul, map_prod, map_pow,
    MvPolynomial.algebraMap_apply]
  ring

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on' with`. Consider the case `monomial e c`. Establish `hm` using `isWeightedHomogeneous_monomial (NumbersDVR.blockWeight ι) e c (rfl : Finsupp.weight (NumbersDVR.blockWeight ι) e = _)`. Establish `hb : ∀ e' ∈ (monomial e c : MvPolynomial (Σ k, ι k) S).support, ∀ k, ∑ i, e' ⟨k, i⟩ = Finsupp.weight (NumbersDVR.blockWeight ι) e k`. Introduce `e' he' k`.

Rewrite using `[sum_block_eq_blockWeight, hm (mem_support_iff.mp he')]`. Rewrite using `[mConeMapOver_eq_of_block y hb, weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hm)]`. Establish `hX : (∏ k, (X k : MvPolynomial K Ω) ^ Finsupp.weight (NumbersDVR.blockWeight ι) e k) = monomial (Finsupp.equivFunOnFinite.symm (Finsupp.weight (NumbersDVR.blockWeight ι) e)) 1`. Rewrite using `[monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp)]`. Simplify using the standard rewrite rules.

Rewrite using `[hX, coeff_C_mul, coeff_monomial]`. Distinguish the cases in `h : b = Finsupp.weight (NumbersDVR.blockWeight ι) e`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg h, if_neg (fun h' => h (Finsupp.equivFunOnFinite.symm.injective h').symm)]`.

Simplify using the standard rewrite rules. Consider the case `add p q hp hq => rw [map_add, coeff_add, hp, hq, map_add, map_add]`.
-/
theorem coeff_mConeMapOver (y : (Σ k, ι k) → Ω) (b : K → ℕ) (f : MvPolynomial (Σ k, ι k) S) :
    coeff (Finsupp.equivFunOnFinite.symm b) (mConeMapOver S y f) =
      aeval y (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial e c =>
    have hm := isWeightedHomogeneous_monomial (NumbersDVR.blockWeight ι) e c
      (rfl : Finsupp.weight (NumbersDVR.blockWeight ι) e = _)
    have hb : ∀ e' ∈ (monomial e c : MvPolynomial (Σ k, ι k) S).support, ∀ k,
        ∑ i, e' ⟨k, i⟩ = Finsupp.weight (NumbersDVR.blockWeight ι) e k := by
      intro e' he' k
      rw [sum_block_eq_blockWeight, hm (mem_support_iff.mp he')]
    rw [mConeMapOver_eq_of_block y hb,
      weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hm)]
    have hX : (∏ k, (X k : MvPolynomial K Ω) ^ Finsupp.weight (NumbersDVR.blockWeight ι) e k) =
        monomial (Finsupp.equivFunOnFinite.symm (Finsupp.weight (NumbersDVR.blockWeight ι) e)) 1 := by
      rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp)]
      simp
    rw [hX, coeff_C_mul, coeff_monomial]
    by_cases h : b = Finsupp.weight (NumbersDVR.blockWeight ι) e
    · subst h; simp
    · rw [if_neg h, if_neg (fun h' => h (Finsupp.equivFunOnFinite.symm.injective h').symm)]
      simp
  | add p q hp hq => rw [map_add, coeff_add, hp, hq, map_add, map_add]

/- English proof (translation)
Introduce `f hf b`. Establish `hf' : mConeMapOver S y f = 0` using `RingHom.mem_ker.mp hf`. Use `RingHom.mem_ker.mpr ?_` and prove the remaining obligations. Establish `hb : ∀ e' ∈ (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f).support, ∀ k, ∑ i, e' ⟨k, i⟩ = b k`. Introduce `e' he' k`.

Rewrite using `[sum_block_eq_blockWeight, weightedHomogeneousComponent_isWeightedHomogeneous b f (mem_support_iff.mp he')]`. Rewrite using `[mConeMapOver_eq_of_block y hb, ← coeff_mConeMapOver, hf', coeff_zero, map_zero, zero_mul]`.
-/
theorem isMultiHomogIdeal_mIdealOver (y : (Σ k, ι k) → Ω) :
    NumbersDVR.IsMultiHomogIdeal (R := S) (mIdealOver S y) := by
  intro f hf b
  have hf' : mConeMapOver S y f = 0 := RingHom.mem_ker.mp hf
  refine RingHom.mem_ker.mpr ?_
  have hb : ∀ e' ∈ (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f).support, ∀ k,
      ∑ i, e' ⟨k, i⟩ = b k := by
    intro e' he' k
    rw [sum_block_eq_blockWeight,
      weightedHomogeneousComponent_isWeightedHomogeneous b f (mem_support_iff.mp he')]
  rw [mConeMapOver_eq_of_block y hb, ← coeff_mConeMapOver, hf', coeff_zero, map_zero, zero_mul]

/- English proof (translation)
The claim follows from `RingHom.ker_isPrime _ multiHomog := isMultiHomogIdeal_mIdealOver y relevant k := by obtain ⟨i, hi⟩ := hy k refine ⟨i, fun h => ?_⟩ have h' : mConeMapOver S y (X ⟨k, i⟩) = 0 := RingHom.mem_ker.mp h simp only [mConeMapOver, aeval_X] at h' exact mul_ne_zero (by rwa [Ne, MvPolynomial …`.
-/
theorem isMultiProjPrime_mIdealOver (y : (Σ k, ι k) → Ω) (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) :
    NumbersDVR.IsMultiProjPrime (R := S) (mIdealOver S y) where
  isPrime := RingHom.ker_isPrime _
  multiHomog := isMultiHomogIdeal_mIdealOver y
  relevant k := by
    obtain ⟨i, hi⟩ := hy k
    refine ⟨i, fun h => ?_⟩
    have h' : mConeMapOver S y (X ⟨k, i⟩) = 0 := RingHom.mem_ker.mp h
    simp only [mConeMapOver, aeval_X] at h'
    exact mul_ne_zero (by rwa [Ne, MvPolynomial.C_eq_zero]) (X_ne_zero _) h'

end Homog

section Graph

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N m : ℕ}

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using `[mConeMapOver, Kleiman.cone, ReciprocityTheory.ChartRestriction.G.Geo.coneMap]`.
-/
theorem mConeMapOver_graph_comp_base (x : Fin (N + 1) → Ω) (s : Fin m → Ω) :
    (mConeMapOver S (graphVec x s)).comp
        (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ b, graphIdx N m b)) =
      ((Polynomial.aeval (X baseBlock : MvPolynomial (Unit ⊕ Unit) Ω)).restrictScalars S).comp
        (Kleiman.cone (S := S) x) := by
  apply MvPolynomial.algHom_ext
  intro a
  simp [mConeMapOver, Kleiman.cone, ReciprocityTheory.ChartRestriction.G.Geo.coneMap]

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using `[mConeMapOver, Kleiman.cone, ReciprocityTheory.ChartRestriction.G.Geo.coneMap]`.
-/
theorem cone_eq_graph_comp (x : Fin (N + 1) → Ω) (s : Fin m → Ω) :
    Kleiman.cone (S := S) x =
      ((aeval fun _ : Unit ⊕ Unit => (Polynomial.X : Polynomial Ω)).restrictScalars S).comp
        ((mConeMapOver S (graphVec x s)).comp
          (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ b, graphIdx N m b))) := by
  apply MvPolynomial.algHom_ext
  intro a
  simp [mConeMapOver, Kleiman.cone, ReciprocityTheory.ChartRestriction.G.Geo.coneMap]

/- English proof (translation)
Use extensionality with `f`. Rewrite using `[Ideal.mem_comap, Kleiman.primeOf_eq, RingHom.mem_ker]`. Express the relevant statement in the definitionally equal form `mConeMapOver S (graphVec x s) (rename _ f) = 0 ↔ _`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Rewrite using `[cone_eq_graph_comp x s, AlgHom.comp_apply, AlgHom.comp_apply, h, map_zero]`. Introduce `h`. Rewrite using `[← AlgHom.comp_apply, mConeMapOver_graph_comp_base, AlgHom.comp_apply, h, map_zero]`.
-/
theorem comap_mIdealOver_graph (x : Fin (N + 1) → Ω) (s : Fin m → Ω) :
    (mIdealOver S (graphVec x s)).comap
        (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ b, graphIdx N m b)) =
      Kleiman.primeOf (S := S) x := by
  ext f
  rw [Ideal.mem_comap, Kleiman.primeOf_eq, RingHom.mem_ker]
  change mConeMapOver S (graphVec x s) (rename _ f) = 0 ↔ _
  constructor
  · intro h
    rw [cone_eq_graph_comp x s, AlgHom.comp_apply, AlgHom.comp_apply, h, map_zero]
  · intro h
    rw [← AlgHom.comp_apply, mConeMapOver_graph_comp_base, AlgHom.comp_apply, h, map_zero]

/- English proof (translation)
The claim follows from `isMultiProjPrime_mIdealOver _ (by rintro (⟨⟩ | ⟨⟩); exacts [hx, hs])`.
-/
theorem isMultiProjPrime_mIdealOver_graph (x : Fin (N + 1) → Ω) (s : Fin m → Ω) (hx : ∃ i, x i ≠ 0)
    (hs : ∃ j, s j ≠ 0) : NumbersDVR.IsMultiProjPrime (R := S) (mIdealOver S (graphVec x s)) :=
  isMultiProjPrime_mIdealOver _ (by rintro (⟨⟩ | ⟨⟩); exacts [hx, hs])

end Graph

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
