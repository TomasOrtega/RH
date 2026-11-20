import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

noncomputable section

namespace GlobalTheory.WeilDeligne

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[pow_succ', AlgEquiv.mul_apply, ih, FiniteField.frobeniusAlgEquivOfAlgebraic_apply, ← pow_mul, pow_succ]`.
-/
theorem frobAlg_pow_apply (K L : Type*) [Field K] [Fintype K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (m : ℕ) (a : L) :
    (FiniteField.frobeniusAlgEquivOfAlgebraic K L ^ m) a = a ^ (Fintype.card K ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, FiniteField.frobeniusAlgEquivOfAlgebraic_apply,
      ← pow_mul, pow_succ]

end GlobalTheory.WeilDeligne

open GlobalTheory.WeilDeligne Pointwise in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `hA L hL g hg`. Use `set Q := primeBelow (F := E) A with hQ`. Use `haveI : w.asIdeal.IsMaximal := w.isMaximal`. Use `haveI : Q.LiesOver w.asIdeal := ⟨(under_primeBelow hA).symm⟩`. Use `haveI : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := 𝓞 E) Q (by rw [show Ideal.comap (algebraMap (𝓞 E) (IntCl E Ω)) Q = w.asIdeal from under_primeBelow hA]; exact w.isMaximal)`.

Use `letI : Field (IntCl E Ω ⧸ Q) := Ideal.Quotient.field Q`. Use `letI : Field (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal`. Use `haveI : Finite (𝓞 E ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot`. Use `letI : Fintype (𝓞 E ⧸ w.asIdeal) := Fintype.ofFinite _`. Use `haveI : Algebra.IsIntegral (𝓞 E ⧸ w.asIdeal) (IntCl E Ω ⧸ Q) := Ideal.Quotient.algebra_isIntegral_of_liesOver Q w.asIdeal`.

Use `haveI : Algebra.IsAlgebraic (𝓞 E ⧸ w.asIdeal) (IntCl E Ω ⧸ Q) := Algebra.IsIntegral.isAlgebraic`. Establish `hqc : Fintype.card (𝓞 E ⧸ w.asIdeal) = normV w` using `Fintype.card_eq_nat_card`. Establish `hq1 : 1 < normV w` using `one_lt_normV w`. Establish `hgQ : g • Q = Q` using `by rw [hQ, ← primeBelow_smul, (mem_Dec.mp hg)]`. Set `ψ` to `Ideal.Quotient.stabilizerHom Q w.asIdeal (Ω ≃ₐ[E] Ω) ⟨g, hgQ⟩`.

Establish `hψ : ∀ b : IntCl E Ω, ψ (Ideal.Quotient.mk Q b) = Ideal.Quotient.mk Q (g • b)` using `fun b => Ideal.Quotient.stabilizerHom_apply _ _ _ _ b`. Use `set n := Module.finrank E L with hn`. Use `set M := n.factorial with hM`. Establish `hres : ∀ b : IntCl E Ω, (b : Ω) ∈ L → (Ideal.Quotient.mk Q b) ^ (normV w ^ M) = Ideal.Quotient.mk Q b`. Introduce `b hbL`.

Use `set y := Ideal.Quotient.mk Q b with hy`. Establish `hbi : IsIntegral (𝓞 E) (b : Ω)` using `b.2`. Use `set f := minpoly (𝓞 E) (b : Ω) with hf`. Establish `hdeg : f.natDegree ≤ n`. Establish `h1` using `minpoly.isIntegrallyClosed_eq_field_fractions' E hbi`.

Establish `h2 : (minpoly E (b : Ω)).natDegree ≤ n`. Establish `h3` using `minpoly.algebraMap_eq (A := E) (algebraMap L Ω).injective (⟨b, hbL⟩ : L)`. Rewrite using `[show (b : Ω) = algebraMap L Ω ⟨b, hbL⟩ from rfl, h3]`. Conclude with `minpoly.natDegree_le _`. Rewrite `h2` using `[h1, (minpoly.monic hbi).natDegree_map]`. Then use the resulting hypothesis.

Establish `hbf : Polynomial.aeval b f = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Polynomial.aeval_subalgebra_coe]`. Conclude with `minpoly.aeval _ _`. Establish `hy0 : Polynomial.aeval y (f.map (algebraMap (𝓞 E) (𝓞 E ⧸ w.asIdeal))) = 0`.

Rewrite using `[Polynomial.aeval_map_algebraMap, hy, ← Ideal.Quotient.mkₐ_eq_mk (𝓞 E), Polynomial.aeval_algHom_apply, hbf, map_zero]`. Establish `hmon` using `(minpoly.monic hbi).map (algebraMap (𝓞 E) (𝓞 E ⧸ w.asIdeal))`. Establish `hyInt : IsIntegral (𝓞 E ⧸ w.asIdeal) y` using `⟨_, hmon, hy0⟩`. Establish `hdvd` using `minpoly.dvd (𝓞 E ⧸ w.asIdeal) y hy0`. Establish `hle : (minpoly (𝓞 E ⧸ w.asIdeal) y).natDegree ≤ n`.

Use `Polynomial.natDegree_le_of_dvd hdvd hmon.ne_zero` as an intermediate fact. Rewrite `this` using `[(minpoly.monic hbi).natDegree_map]`. Conclude with `this.trans hdeg`. Establish `hpos` using `minpoly.natDegree_pos hyInt`. Use `set K' := IntermediateField.adjoin (𝓞 E ⧸ w.asIdeal) ({y} : Set (IntCl E Ω ⧸ Q))`.

Use `haveI : FiniteDimensional (𝓞 E ⧸ w.asIdeal) K' := IntermediateField.adjoin.finiteDimensional hyInt`. Use `haveI : Finite K' := Module.finite_of_finite (𝓞 E ⧸ w.asIdeal)`. Use `letI : Fintype K' := Fintype.ofFinite _`. Establish `hcard : Fintype.card K' = normV w ^ (minpoly (𝓞 E ⧸ w.asIdeal) y).natDegree`. Rewrite using `[Module.card_eq_pow_finrank (K := 𝓞 E ⧸ w.asIdeal), hqc, IntermediateField.adjoin.finrank hyInt]`.

Take `⟨m, hm⟩` from `Nat.dvd_factorial hpos hle`. Establish `key` using `FiniteField.pow_card_pow m (⟨y, IntermediateField.mem_adjoin_simple_self _ y⟩ : K')`. Rewrite `key` using `[hcard, ← pow_mul, ← hm]`. Conclude with `congrArg Subtype.val key`. Set `frob` to `FiniteField.frobeniusAlgEquivOfAlgebraic (𝓞 E ⧸ w.asIdeal) (IntCl E Ω ⧸ Q)`.

Set `τ` to `frob ^ M`. Establish `hτ : ∀ y, τ y = y ^ (normV w ^ M)` using `fun y => by`. Rewrite using `[frobAlg_pow_apply, hqc]`. Set `R` to `IntermediateField.fixedField (Subgroup.zpowers τ)`. Establish `hmemR : ∀ y, y ∈ R ↔ y ^ (normV w ^ M) = y`.

Introduce `y`. Rewrite using `[← hτ]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `(IntermediateField.mem_fixedField_iff _ _).mp h τ (Subgroup.mem_zpowers τ)`.

Introduce `h`. Rewrite using `[IntermediateField.mem_fixedField_iff]`. Introduce `f hf`. Establish `hs : τ ∈ MulAction.stabilizer ((IntCl E Ω ⧸ Q) ≃ₐ[𝓞 E ⧸ w.asIdeal] (IntCl E Ω ⧸ Q)) y` using `h`. Conclude with `(Subgroup.zpowers_le.mpr hs) hf`.

Establish `hqM : 1 < normV w ^ M` using `Nat.one_lt_pow (Nat.factorial_ne_zero n) hq1`. Use `haveI : Finite R := by`. Establish `hfin` using `(Polynomial.X ^ (normV w ^ M) - Polynomial.X : Polynomial (𝓞 E ⧸ w.asIdeal)).rootSet_finite (IntCl E Ω ⧸ Q)`. Use `Set.Finite.to_subtype (hfin.subset fun y hy => ?_)` and prove the remaining obligations. Rewrite using `[Polynomial.mem_rootSet]`.

Use `⟨FiniteField.X_pow_card_sub_X_ne_zero _ hqM, ?_⟩` and prove the remaining obligations. Simplify using `only [map_sub, map_pow, Polynomial.aeval_X]`. Rewrite using `[(hmemR y).mp hy, sub_self]`. Take `⟨j, hj⟩` from `(FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (𝓞 E ⧸ w.asIdeal) R).2 (ψ.restrictNormal R)`. Establish `hj' : FiniteField.frobeniusAlgEquivOfAlgebraic (𝓞 E ⧸ w.asIdeal) R ^ (j : ℕ) = ψ.restrictNormal R` using `hj`.

Establish `hψR : ∀ y ∈ R, ψ y = y ^ (normV w ^ (j : ℕ))`. Introduce `y hy`. Establish `h1` using `AlgEquiv.restrictNormal_commutes ψ R ⟨y, hy⟩`. Rewrite `h1` using `[← hj', frobAlg_pow_apply, hqc]`. Simplify `h1.symm` using `[IntermediateField.algebraMap_apply]`.

Take `⟨m, hm⟩` from `Nat.exists_eq_succ_of_ne_zero (Nat.factorial_ne_zero n)`. Use `⟨m * (j : ℕ), fun x hxL hx => ?_⟩` and prove the remaining obligations. Set `b : IntCl E Ω` to `⟨x, hx.tower_top⟩`. Establish `hbR : Ideal.Quotient.mk Q b ∈ R` using `(hmemR _).mpr (hres b hxL)`. Establish `hfix : ∀ t : ℕ, (Ideal.Quotient.mk Q b) ^ (normV w ^ (M * t)) = Ideal.Quotient.mk Q b`.

Introduce `t`. Proceed by induction on `t with`. Consider the case `zero => simp`. Consider the case `succ t ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hres b hxL]`. Establish `h2 : (g • b) ^ (normV w ^ (m * (j : ℕ))) - b ∈ Q`.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, ← hψ, hψR _ hbR, ← pow_mul, ← pow_add, show (j : ℕ) + m * j = M * j by rw [hM, hm, Nat.succ_mul, add_comm], hfix, sub_self]`. Conclude with `h2`.
-/
theorem GlobalTheory.WeilDeligne.exists_pow_normV_resPow (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) :
    IsPlaceOver A w → ∀ (L : IntermediateField E Ω), FiniteDimensional E L → ∀ g : G E Ω,
      g ∈ Dec (F := E) A → ∃ k : ℕ, ∀ x ∈ L, IsIntegral ℤ x →
        A.valuation ((g x) ^ (normV w ^ k) - x) < 1 := by
  intro hA L hL g hg
  classical
  set Q := primeBelow (F := E) A with hQ
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  haveI : Q.LiesOver w.asIdeal := ⟨(under_primeBelow hA).symm⟩
  haveI : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := 𝓞 E) Q
    (by rw [show Ideal.comap (algebraMap (𝓞 E) (IntCl E Ω)) Q = w.asIdeal from
      under_primeBelow hA]; exact w.isMaximal)
  letI : Field (IntCl E Ω ⧸ Q) := Ideal.Quotient.field Q
  letI : Field (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  haveI : Finite (𝓞 E ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  letI : Fintype (𝓞 E ⧸ w.asIdeal) := Fintype.ofFinite _
  haveI : Algebra.IsIntegral (𝓞 E ⧸ w.asIdeal) (IntCl E Ω ⧸ Q) :=
    Ideal.Quotient.algebra_isIntegral_of_liesOver Q w.asIdeal
  haveI : Algebra.IsAlgebraic (𝓞 E ⧸ w.asIdeal) (IntCl E Ω ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  have hqc : Fintype.card (𝓞 E ⧸ w.asIdeal) = normV w := Fintype.card_eq_nat_card
  have hq1 : 1 < normV w := one_lt_normV w

  have hgQ : g • Q = Q := by rw [hQ, ← primeBelow_smul, (mem_Dec.mp hg)]
  let ψ := Ideal.Quotient.stabilizerHom Q w.asIdeal (Ω ≃ₐ[E] Ω) ⟨g, hgQ⟩
  have hψ : ∀ b : IntCl E Ω, ψ (Ideal.Quotient.mk Q b) = Ideal.Quotient.mk Q (g • b) :=
    fun b => Ideal.Quotient.stabilizerHom_apply _ _ _ _ b

  set n := Module.finrank E L with hn
  set M := n.factorial with hM

  have hres : ∀ b : IntCl E Ω, (b : Ω) ∈ L →
      (Ideal.Quotient.mk Q b) ^ (normV w ^ M) = Ideal.Quotient.mk Q b := by
    intro b hbL
    set y := Ideal.Quotient.mk Q b with hy
    have hbi : IsIntegral (𝓞 E) (b : Ω) := b.2
    set f := minpoly (𝓞 E) (b : Ω) with hf
    have hdeg : f.natDegree ≤ n := by
      have h1 := minpoly.isIntegrallyClosed_eq_field_fractions' E hbi
      have h2 : (minpoly E (b : Ω)).natDegree ≤ n := by
        have h3 := minpoly.algebraMap_eq (A := E) (algebraMap L Ω).injective (⟨b, hbL⟩ : L)
        rw [show (b : Ω) = algebraMap L Ω ⟨b, hbL⟩ from rfl, h3]
        exact minpoly.natDegree_le _
      rwa [h1, (minpoly.monic hbi).natDegree_map] at h2
    have hbf : Polynomial.aeval b f = 0 := by
      apply Subtype.ext
      rw [Polynomial.aeval_subalgebra_coe]
      exact minpoly.aeval _ _
    have hy0 : Polynomial.aeval y (f.map (algebraMap (𝓞 E) (𝓞 E ⧸ w.asIdeal))) = 0 := by
      rw [Polynomial.aeval_map_algebraMap, hy, ← Ideal.Quotient.mkₐ_eq_mk (𝓞 E),
        Polynomial.aeval_algHom_apply, hbf, map_zero]
    have hmon := (minpoly.monic hbi).map (algebraMap (𝓞 E) (𝓞 E ⧸ w.asIdeal))
    have hyInt : IsIntegral (𝓞 E ⧸ w.asIdeal) y := ⟨_, hmon, hy0⟩
    have hdvd := minpoly.dvd (𝓞 E ⧸ w.asIdeal) y hy0
    have hle : (minpoly (𝓞 E ⧸ w.asIdeal) y).natDegree ≤ n := by
      have := Polynomial.natDegree_le_of_dvd hdvd hmon.ne_zero
      rw [(minpoly.monic hbi).natDegree_map] at this
      exact this.trans hdeg
    have hpos := minpoly.natDegree_pos hyInt
    set K' := IntermediateField.adjoin (𝓞 E ⧸ w.asIdeal) ({y} : Set (IntCl E Ω ⧸ Q))
    haveI : FiniteDimensional (𝓞 E ⧸ w.asIdeal) K' := IntermediateField.adjoin.finiteDimensional hyInt
    haveI : Finite K' := Module.finite_of_finite (𝓞 E ⧸ w.asIdeal)
    letI : Fintype K' := Fintype.ofFinite _
    have hcard : Fintype.card K' = normV w ^ (minpoly (𝓞 E ⧸ w.asIdeal) y).natDegree := by
      rw [Module.card_eq_pow_finrank (K := 𝓞 E ⧸ w.asIdeal), hqc,
        IntermediateField.adjoin.finrank hyInt]
    obtain ⟨m, hm⟩ := Nat.dvd_factorial hpos hle
    have key := FiniteField.pow_card_pow m
      (⟨y, IntermediateField.mem_adjoin_simple_self _ y⟩ : K')
    rw [hcard, ← pow_mul, ← hm] at key
    exact congrArg Subtype.val key

  let frob := FiniteField.frobeniusAlgEquivOfAlgebraic (𝓞 E ⧸ w.asIdeal) (IntCl E Ω ⧸ Q)
  let τ := frob ^ M
  have hτ : ∀ y, τ y = y ^ (normV w ^ M) := fun y => by
    rw [frobAlg_pow_apply, hqc]
  let R := IntermediateField.fixedField (Subgroup.zpowers τ)
  have hmemR : ∀ y, y ∈ R ↔ y ^ (normV w ^ M) = y := by
    intro y
    rw [← hτ]
    constructor
    · intro h; exact (IntermediateField.mem_fixedField_iff _ _).mp h τ (Subgroup.mem_zpowers τ)
    · intro h
      rw [IntermediateField.mem_fixedField_iff]
      intro f hf
      have hs : τ ∈ MulAction.stabilizer
        ((IntCl E Ω ⧸ Q) ≃ₐ[𝓞 E ⧸ w.asIdeal] (IntCl E Ω ⧸ Q)) y := h
      exact (Subgroup.zpowers_le.mpr hs) hf
  have hqM : 1 < normV w ^ M := Nat.one_lt_pow (Nat.factorial_ne_zero n) hq1
  haveI : Finite R := by
    have hfin := (Polynomial.X ^ (normV w ^ M) - Polynomial.X :
      Polynomial (𝓞 E ⧸ w.asIdeal)).rootSet_finite (IntCl E Ω ⧸ Q)
    refine Set.Finite.to_subtype (hfin.subset fun y hy => ?_)
    rw [Polynomial.mem_rootSet]
    refine ⟨FiniteField.X_pow_card_sub_X_ne_zero _ hqM, ?_⟩
    simp only [map_sub, map_pow, Polynomial.aeval_X]
    rw [(hmemR y).mp hy, sub_self]

  obtain ⟨j, hj⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (𝓞 E ⧸ w.asIdeal) R).2 (ψ.restrictNormal R)
  have hj' : FiniteField.frobeniusAlgEquivOfAlgebraic (𝓞 E ⧸ w.asIdeal) R ^ (j : ℕ) =
      ψ.restrictNormal R := hj
  have hψR : ∀ y ∈ R, ψ y = y ^ (normV w ^ (j : ℕ)) := by
    intro y hy
    have h1 := AlgEquiv.restrictNormal_commutes ψ R ⟨y, hy⟩
    rw [← hj', frobAlg_pow_apply, hqc] at h1
    simpa [IntermediateField.algebraMap_apply] using h1.symm

  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.factorial_ne_zero n)
  refine ⟨m * (j : ℕ), fun x hxL hx => ?_⟩
  let b : IntCl E Ω := ⟨x, hx.tower_top⟩
  have hbR : Ideal.Quotient.mk Q b ∈ R := (hmemR _).mpr (hres b hxL)
  have hfix : ∀ t : ℕ, (Ideal.Quotient.mk Q b) ^ (normV w ^ (M * t)) = Ideal.Quotient.mk Q b := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hres b hxL]
  have h2 : (g • b) ^ (normV w ^ (m * (j : ℕ))) - b ∈ Q := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, ← hψ, hψR _ hbR, ← pow_mul, ← pow_add,
      show (j : ℕ) + m * j = M * j by rw [hM, hm, Nat.succ_mul, add_comm], hfix, sub_self]
  exact h2
