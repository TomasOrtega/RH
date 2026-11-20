import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TransPtBase

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph.RegField

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion repeatedly using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
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
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Establish an intermediate fact. Replace the chosen expression with an arbitrary variable. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Supply the required witnesses or components. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Rewrite the conclusion using the stated equalities. Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
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
