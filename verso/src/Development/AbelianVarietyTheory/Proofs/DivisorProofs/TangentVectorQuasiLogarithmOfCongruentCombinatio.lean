import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFreePDThickeningFrameValuationIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFreePDThickeningFrameValuationIntegersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupDualTangentOfQuasiLogarithmStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupDualTangentLinearKillsIntegralStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

namespace GlobalTheory.TangentComb

/- English proof (translation)
Introduce `α`. Take `⟨b, -, hb⟩` from `hf α`. Take `⟨b', -, hb'⟩` from `hg α`. Use `⟨b + a * b', trivial, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_smul, hb, hb', map_add, map_mul, smul_eq_mul]`.
-/
theorem in_top_add_smul {O Q σ : Type} [CommRing O] [CommRing Q] [Algebra O Q]
    {f g : MvPowerSeries σ Q} (hf : In (⊤ : Ideal O) f) (hg : In (⊤ : Ideal O) g) (a : O) :
    In (⊤ : Ideal O) (f + algebraMap O Q a • g) := by
  intro α
  obtain ⟨b, -, hb⟩ := hf α
  obtain ⟨b', -, hb'⟩ := hg α
  refine ⟨b + a * b', trivial, ?_⟩
  rw [map_add, map_smul, hb, hb', map_add, map_mul, smul_eq_mul]

/- English proof (translation)
Establish `hμ' : ∀ i, constantCoeff (up Q μ i) = 0` using `fun i => by`. Rewrite using `[up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hμ, map_zero]`. Use `⟨?_, fun i => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, map_add, map_smul, coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, hf.1, hg.1, smul_zero, add_zero]`. Take `⟨b, -, hb⟩` from `hf.2.1 i`.

Take `⟨b', -, hb'⟩` from `hg.2.1 i`. Use `⟨b + a * b', trivial, ?_⟩` and prove the remaining obligations. Simplify using `only [lin] at hb hb' ⊢`. Rewrite using `[map_add, map_smul, hb, hb', map_add, map_mul, smul_eq_mul]`. Rewrite using `[formalCoboundary_add hμ', formalCoboundary_smul hμ']`.

Conclude with `in_top_add_smul hf.2.2 hg.2.2 a`.
-/
theorem ql_add_smul {O Q : Type} [CommRing O] [CommRing Q] [Algebra O Q] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, constantCoeff (μ i) = 0)
    {f g : MvPowerSeries (Fin d) Q} (hf : QL μ ⊤ f) (hg : QL μ ⊤ g) (a : O) :
    QL μ ⊤ (f + algebraMap O Q a • g) := by
  have hμ' : ∀ i, constantCoeff (up Q μ i) = 0 := fun i => by
    rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      hμ, map_zero]
  refine ⟨?_, fun i => ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, map_add, map_smul, coeff_zero_eq_constantCoeff_apply,
      coeff_zero_eq_constantCoeff_apply, hf.1, hg.1, smul_zero, add_zero]
  · obtain ⟨b, -, hb⟩ := hf.2.1 i
    obtain ⟨b', -, hb'⟩ := hg.2.1 i
    refine ⟨b + a * b', trivial, ?_⟩
    simp only [lin] at hb hb' ⊢
    rw [map_add, map_smul, hb, hb', map_add, map_mul, smul_eq_mul]
  · rw [formalCoboundary_add hμ', formalCoboundary_smul hμ']
    exact in_top_add_smul hf.2.2 hg.2.2 a

/- English proof (translation)
Establish `hμ' : ∀ i, constantCoeff (up Q μ i) = 0` using `fun i => by`. Rewrite using `[up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hμ, map_zero]`. Establish `h0 : cob1 (up Q μ) (0 : MvPowerSeries (Fin d) Q) = 0`. Use `formalCoboundary_smul hμ' (0 : Q) (0 : MvPowerSeries (Fin d) Q)` as an intermediate fact. Rewrite `this` using `[zero_smul, zero_smul]`. Then use the resulting hypothesis.

Use `⟨map_zero _, fun i => ⟨0, trivial, ?_⟩, ?_⟩` and prove the remaining obligations. Simplify using `[lin]`. Rewrite using `[h0]`. Conclude with `In.top_iff.2 ⟨0, map_zero _⟩`.
-/
theorem ql_zero {O Q : Type} [CommRing O] [CommRing Q] [Algebra O Q] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, constantCoeff (μ i) = 0) :
    QL μ ⊤ (0 : MvPowerSeries (Fin d) Q) := by
  have hμ' : ∀ i, constantCoeff (up Q μ i) = 0 := fun i => by
    rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      hμ, map_zero]
  have h0 : cob1 (up Q μ) (0 : MvPowerSeries (Fin d) Q) = 0 := by
    have := formalCoboundary_smul hμ' (0 : Q) (0 : MvPowerSeries (Fin d) Q)
    rwa [zero_smul, zero_smul] at this
  refine ⟨map_zero _, fun i => ⟨0, trivial, ?_⟩, ?_⟩
  · simp [lin]
  · rw [h0]
    exact In.top_iff.2 ⟨0, map_zero _⟩

end GlobalTheory.TangentComb

open GlobalTheory.TangentComb in
/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ _ hv G d c ι _ e he L hL g hg a hint`. Establish `hF : IsFrame p C (RingHom.id O)` using `GlobalTheory.T.isTorsionFreePDThickeningFrame_valuation_integers p C v O hv`. Establish `lin` using `GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c C hF`. Establish `hμ` using `c.isLaw.const`. Establish `key : ∀ s : Finset ι, QL c.μ ⊤ (∑ m ∈ s, algebraMap O C (a m) • e m) ∧ c.IsLie (∑ m ∈ s, algebraMap O C (a m) • e m) (∑ m ∈ s, a m • L m)`.

Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.sum_empty]`. Conclude with `⟨ql_zero hμ, c.isLie_zero hF.inj⟩`.

Consider the case `insert j s hj ih`. Rewrite using `[Finset.sum_insert hj, Finset.sum_insert hj, add_comm, add_comm (a j • L j)]`. Conclude with `⟨ql_add_smul hμ ih.1 (he j) (a j), (lin _ _ _ _ (a j) ih.2 (hL j)).1 ih.1 (he j)⟩`. Take `⟨hQ, hI⟩` from `key Finset.univ`. Take `⟨l, hl, -⟩` from `GlobalTheory.T.pDivGroup_dual_tangent_of_quasiLogarithm p C v O hv G d c C hF g hg`.

Establish `h1` using `(lin g (comb a e) l (∑ m, a m • L m) (-1) hl hI).1 hg hQ`. Establish `hser : g + algebraMap O C (-1) • comb a e = g - comb a e`. Rewrite using `[map_neg, map_one, neg_one_smul, sub_eq_add_neg]`. Rewrite `h1` using `[hser]`. Take `⟨s, hs⟩` from `In.top_iff.1 hint`.

Establish `h0` using `(lin _ (comb a e) _ (∑ m, a m • L m) 0 h1 hI).2.1 ⟨s, hs.symm⟩`. Rewrite `h0` using `[neg_one_smul, ← sub_eq_add_neg, sub_eq_zero]`. Conclude with `h0 ▸ hl`.
-/
theorem GlobalTheory.TangentComb.main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) {ι : Type} [Fintype ι] (e : ι → MvPowerSeries (Fin d) C), (∀ m, QL c.μ ⊤ (e m)) → ∀ (L : ι → G.dual.Lie), (∀ m, c.IsLie (e m) (L m)) → ∀ (g : MvPowerSeries (Fin d) C), QL c.μ ⊤ g → ∀ (a : ι → O), In (⊤ : Ideal O) (g - comb a e) → c.IsLie g (∑ m, a m • L m) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c ι _ e he L hL g hg a hint
  classical
  have hF : IsFrame p C (RingHom.id O) := GlobalTheory.T.isTorsionFreePDThickeningFrame_valuation_integers p C v O hv
  have lin := GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral p C v O hv G d c C hF
  have hμ := c.isLaw.const

  have key : ∀ s : Finset ι, QL c.μ ⊤ (∑ m ∈ s, algebraMap O C (a m) • e m) ∧
      c.IsLie (∑ m ∈ s, algebraMap O C (a m) • e m) (∑ m ∈ s, a m • L m) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact ⟨ql_zero hμ, c.isLie_zero hF.inj⟩
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj, add_comm, add_comm (a j • L j)]
      exact ⟨ql_add_smul hμ ih.1 (he j) (a j),
        (lin _ _ _ _ (a j) ih.2 (hL j)).1 ih.1 (he j)⟩
  obtain ⟨hQ, hI⟩ := key Finset.univ
  obtain ⟨l, hl, -⟩ := GlobalTheory.T.pDivGroup_dual_tangent_of_quasiLogarithm p C v O hv G d c C hF g hg
  have h1 := (lin g (comb a e) l (∑ m, a m • L m) (-1) hl hI).1 hg hQ
  have hser : g + algebraMap O C (-1) • comb a e = g - comb a e := by
    rw [map_neg, map_one, neg_one_smul, sub_eq_add_neg]
  rw [hser] at h1
  obtain ⟨s, hs⟩ := In.top_iff.1 hint
  have h0 := (lin _ (comb a e) _ (∑ m, a m • L m) 0 h1 hI).2.1 ⟨s, hs.symm⟩
  rw [neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at h0
  exact h0 ▸ hl
