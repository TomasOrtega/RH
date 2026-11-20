import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TransPtBase

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph.RegField

/- English proof (translation)
Use `conv_lhs => rw [MvPolynomial.as_sum f]`. Use `conv_rhs => rw [MvPolynomial.as_sum f]`. Rewrite using `[map_sum, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]`.

Establish `key : (m.prod fun q e => (t q.1 * w q) ^ e) = (∏ k, t k ^ d k) * m.prod fun q e => w q ^ e`. Repeatedly rewrite using `[mul_pow]`. Rewrite using `[Finsupp.prod_mul]`. Use `congr 1`. Rewrite using `[Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fintype.prod_sigma]`.

Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `show ∏ i, t k ^ m ⟨k, i⟩ = _`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hf m hm k]`. Rewrite using `[key]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem aeval_mul_scale_of_homog {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {S : Type} [CommRing S] [Algebra ℤ S] (f : MvPolynomial (Σ k, ι k) ℤ) (d : K → ℕ)
    (hf : ∀ m ∈ f.support, ∀ k, ∑ i, m ⟨k, i⟩ = d k) (t : K → S) (w : (Σ k, ι k) → S) :
    MvPolynomial.aeval (fun q : Σ k, ι k => t q.1 * w q) f = (∏ k, t k ^ d k) * MvPolynomial.aeval w f := by
  conv_lhs => rw [MvPolynomial.as_sum f]
  conv_rhs => rw [MvPolynomial.as_sum f]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]
  have key : (m.prod fun q e => (t q.1 * w q) ^ e) = (∏ k, t k ^ d k) * m.prod fun q e => w q ^ e := by
    simp_rw [mul_pow]
    rw [Finsupp.prod_mul]
    congr 1
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, t k ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hf m hm k]
  rw [key]
  ring

/- English proof (translation)
Establish `e : (fun p : Σ k, ι k => MvPolynomial.C (y p) * (MvPolynomial.X p.1 : MvPolynomial K Ω)) = fun p => (MvPolynomial.X p.1 : MvPolynomial K Ω) * MvPolynomial.C (y p)`. Use function extensionality and compare the values at `p`. Expand and normalize the polynomial expressions, which then agree. Use `show MvPolynomial.aeval _ h = _`. Rewrite using `[e, aeval_mul_scale_of_homog h d hh (fun k => (MvPolynomial.X k : MvPolynomial K Ω)) (fun p => MvPolynomial.C (y p))]`.

Use `congr 1`. Conclude with `MvPolynomial.aeval_algebraMap_apply (MvPolynomial K Ω) y h`.
-/
private theorem mConeMap_eq_prod_X_pow_mul_C {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (h : MvPolynomial (Σ k, ι k) ℤ) (d : K → ℕ)
    (hh : ∀ m ∈ h.support, ∀ k, ∑ i, m ⟨k, i⟩ = d k) :
    mConeMap y h = (∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k) * MvPolynomial.C (MvPolynomial.aeval y h) := by
  have e : (fun p : Σ k, ι k => MvPolynomial.C (y p) * (MvPolynomial.X p.1 : MvPolynomial K Ω)) =
      fun p => (MvPolynomial.X p.1 : MvPolynomial K Ω) * MvPolynomial.C (y p) := by
    funext p
    ring
  show MvPolynomial.aeval _ h = _
  rw [e, aeval_mul_scale_of_homog h d hh (fun k => (MvPolynomial.X k : MvPolynomial K Ω))
    (fun p => MvPolynomial.C (y p))]
  congr 1
  exact MvPolynomial.aeval_algebraMap_apply (MvPolynomial K Ω) y h

/- English proof (translation)
Introduce `K _ ι _ Φ _ _ y Ψ N j M zb s hzb hreg`. Take `⟨d, g, h, hg, hh, hQ, hgs⟩` from `hreg`. Take `⟨-, hzv⟩` from `hzb`. Establish `hxh : MvPolynomial.aeval M.x h ≠ 0`. Introduce `h0`.

Apply `hQ` to reduce the goal to its premises. Establish `hker : h ∈ mCoordIdeal M.x`. Rewrite using `[mCoordIdeal, RingHom.mem_ker, mConeMap_eq_prod_X_pow_mul_C M.x h d hh, h0, map_zero, mul_zero]`. Establish `hz` using `hzv h hker`. Establish `hz' : MvPolynomial.aeval zb h = 0`.

Rewrite using `[MvPolynomial.aeval_def, algebraMap_int_eq, ← MvPolynomial.eval_map]`. Conclude with `hz`. Rewrite using `[mCoordIdeal, RingHom.mem_ker, mConeMap_eq_prod_X_pow_mul_C zb h d hh, hz', map_zero, mul_zero]`. Establish `hs : s = MvPolynomial.aeval M.x g / MvPolynomial.aeval M.x h` using `eq_div_of_mul_eq hxh hgs.symm`. Rewrite using `[hs, map_div₀, ← MvPolynomial.aeval_algebraMap_apply, ← MvPolynomial.aeval_algebraMap_apply]`.

Establish `hne : ∀ k, ∃ i, (⇑(algebraMap M.Ω Φ) ∘ M.x) ⟨k, i⟩ ≠ 0` using `fun k => by`. Take `⟨i, hi⟩` from `M.x_ne k`. Conclude with `⟨i, (map_ne_zero _).mpr hi⟩`. Use `choose c hc using hne`. Establish `hYy : ∀ q, (⇑(algebraMap M.Ω Φ) ∘ M.x) q = y ⟨q.1.val, q.2⟩` using `fun q => (M.y_base q).symm`.

Generalize the expression as in `(⇑(algebraMap M.Ω Φ) ∘ M.x) = Y at hYy hc ⊢`. Establish `hsc : ∀ p : MvPolynomial (Σ k, baseIdx ι M.blk k) ℤ, (∀ m ∈ p.support, ∀ k, ∑ i, m ⟨k, i⟩ = d k) → MvPolynomial.aeval Y p = (∏ k, Y ⟨k, c k⟩ ^ d k) * MvPolynomial.aeval (fun q => Y q / Y ⟨q.1, c q.1⟩) p`. Introduce `p hp`. Establish `eY : Y = fun q : Σ k, baseIdx ι M.blk k => Y ⟨q.1, c q.1⟩ * (Y q / Y ⟨q.1, c q.1⟩)`. Use function extensionality and compare the values at `q`.

Rewrite using `[mul_comm, div_mul_cancel₀ _ (hc q.1)]`. Use `conv_lhs => rw [eY]`. Conclude with `aeval_mul_scale_of_homog p d hp (fun k => Y ⟨k, c k⟩) (fun q => Y q / Y ⟨q.1, c q.1⟩)`. Establish `hP : (∏ k, Y ⟨k, c k⟩ ^ d k) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)`. Rewrite using `[hsc g hg, hsc h hh, mul_div_mul_left _ _ hP]`.

Establish `hw : ∀ q, Y q / Y ⟨q.1, c q.1⟩ ∈ blockFnField y`. Introduce `q`. Rewrite using `[hYy, hYy]`. Apply `IntermediateField.subset_adjoin` to reduce the goal to its premises. Conclude with `⟨⟨q.1.val, q.2⟩, ⟨q.1.val, c q.1⟩, rfl, rfl⟩`.

Establish `hmem : ∀ p : MvPolynomial (Σ k, baseIdx ι M.blk k) ℤ, MvPolynomial.aeval (fun q => Y q / Y ⟨q.1, c q.1⟩) p ∈ blockFnField y`. Introduce `p`. Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a`. Rewrite using `[MvPolynomial.aeval_C, algebraMap_int_eq, eq_intCast]`.

Conclude with `intCast_mem _ a`. Consider the case `add p q hp hq`. Rewrite using `[map_add]`. Conclude with `add_mem hp hq`. Consider the case `mul_X p n hp`.

Rewrite using `[map_mul, MvPolynomial.aeval_X]`. Conclude with `mul_mem hp (hw n)`. Conclude with `div_mem (hmem g) (hmem h)`.
-/
theorem algebraMap_mem_blockFnField :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] [CharZero Φ]
      (y : (Σ k, ι k) → Φ) (Ψ : Type) (N j : ℕ) (M : FlagModel y Ψ N j) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (s : M.Ω),
      zb ∈ mcPts (mCoordIdeal M.x) → RegAt M.x (mCoordIdeal zb) s → algebraMap M.Ω Φ s ∈ blockFnField y := by
  intro K _ ι _ Φ _ _ y Ψ N j M zb s hzb hreg
  obtain ⟨d, g, h, hg, hh, hQ, hgs⟩ := hreg
  obtain ⟨-, hzv⟩ := hzb
  have hxh : MvPolynomial.aeval M.x h ≠ 0 := by
    intro h0
    apply hQ
    have hker : h ∈ mCoordIdeal M.x := by
      rw [mCoordIdeal, RingHom.mem_ker, mConeMap_eq_prod_X_pow_mul_C M.x h d hh, h0, map_zero, mul_zero]
    have hz := hzv h hker
    have hz' : MvPolynomial.aeval zb h = 0 := by
      rw [MvPolynomial.aeval_def, algebraMap_int_eq, ← MvPolynomial.eval_map]
      exact hz
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap_eq_prod_X_pow_mul_C zb h d hh, hz', map_zero, mul_zero]
  have hs : s = MvPolynomial.aeval M.x g / MvPolynomial.aeval M.x h := eq_div_of_mul_eq hxh hgs.symm
  rw [hs, map_div₀, ← MvPolynomial.aeval_algebraMap_apply, ← MvPolynomial.aeval_algebraMap_apply]
  have hne : ∀ k, ∃ i, (⇑(algebraMap M.Ω Φ) ∘ M.x) ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := M.x_ne k
    exact ⟨i, (map_ne_zero _).mpr hi⟩
  choose c hc using hne
  have hYy : ∀ q, (⇑(algebraMap M.Ω Φ) ∘ M.x) q = y ⟨q.1.val, q.2⟩ := fun q => (M.y_base q).symm
  generalize (⇑(algebraMap M.Ω Φ) ∘ M.x) = Y at hYy hc ⊢
  have hsc : ∀ p : MvPolynomial (Σ k, baseIdx ι M.blk k) ℤ, (∀ m ∈ p.support, ∀ k, ∑ i, m ⟨k, i⟩ = d k) →
      MvPolynomial.aeval Y p =
        (∏ k, Y ⟨k, c k⟩ ^ d k) * MvPolynomial.aeval (fun q => Y q / Y ⟨q.1, c q.1⟩) p := by
    intro p hp
    have eY : Y = fun q : Σ k, baseIdx ι M.blk k => Y ⟨q.1, c q.1⟩ * (Y q / Y ⟨q.1, c q.1⟩) := by
      funext q
      rw [mul_comm, div_mul_cancel₀ _ (hc q.1)]
    conv_lhs => rw [eY]
    exact aeval_mul_scale_of_homog p d hp (fun k => Y ⟨k, c k⟩) (fun q => Y q / Y ⟨q.1, c q.1⟩)
  have hP : (∏ k, Y ⟨k, c k⟩ ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  rw [hsc g hg, hsc h hh, mul_div_mul_left _ _ hP]
  have hw : ∀ q, Y q / Y ⟨q.1, c q.1⟩ ∈ blockFnField y := by
    intro q
    rw [hYy, hYy]
    apply IntermediateField.subset_adjoin
    exact ⟨⟨q.1.val, q.2⟩, ⟨q.1.val, c q.1⟩, rfl, rfl⟩
  have hmem : ∀ p : MvPolynomial (Σ k, baseIdx ι M.blk k) ℤ,
      MvPolynomial.aeval (fun q => Y q / Y ⟨q.1, c q.1⟩) p ∈ blockFnField y := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.aeval_C, algebraMap_int_eq, eq_intCast]
      exact intCast_mem _ a
    | add p q hp hq =>
      rw [map_add]
      exact add_mem hp hq
    | mul_X p n hp =>
      rw [map_mul, MvPolynomial.aeval_X]
      exact mul_mem hp (hw n)
  exact div_mem (hmem g) (hmem h)

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph.RegField
