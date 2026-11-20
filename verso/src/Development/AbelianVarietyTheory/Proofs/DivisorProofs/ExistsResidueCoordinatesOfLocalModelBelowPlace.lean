import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasiRegularSeqSelfIffLocalizationMaximal
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.FieldPair

open IsLocalRing in

/- English proof (translation)
Introduce `L _ c Q hQ`. Use `letI := hQ.isLocalRing`. Introduce `N r V hC u hx hm hunitP hloc`. Set `φ : Q →+* V.ring` to `Q.subtype.codRestrict V.ring fun q => hC _ q.2`. Use `letI : Algebra ℂ V.ring := V.const.toAlgebra`.

Use `letI : Algebra ℂ L := c.toAlgebra`. Use `letI : Algebra ℂ Q := (c.codRestrict Q hQ.const_mem).toAlgebra`. Use `letI : Algebra Q V.ring := φ.toAlgebra`. Use `haveI : IsScalarTower ℂ V.ring L := IsScalarTower.of_algebraMap_eq' rfl`. Use `haveI : IsScalarTower ℂ Q V.ring := IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl`.

Use `haveI : IsLocalHom (algebraMap Q V.ring) := ⟨fun q hq => by`. Assume the negation of the conclusion as `hq'`. Establish `hqm : q ∈ maximalIdeal Q` using `(mem_maximalIdeal _).2 hq'`. Conclude with `(mem_maximalIdeal _).1 (hm q hqm) hq⟩`. Use `haveI : Algebra.EssFiniteType ℂ V.ring := V.essFiniteType`.

Use `haveI := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ V.ring`. Take `⟨x, hx⟩` from `hx`. Establish `h2` using `IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hx`. Rewrite `h2` using `[Cardinal.mk_fin]`. Establish `h3` using `trdeg_residueField_of_trdeg ℂ V.ring L h2.symm`.

Take `⟨t, ht⟩` from `IsDiscreteValuationRing.exists_irreducible V.ring`. Take `⟨hN, -⟩` from `exists_basis_kaehler_of_trdeg ℂ L h2.symm ht`. Set `ub : Fin r → ResidueField V.ring` to `fun i => residue V.ring (u i)`. Establish `key : ∀ P : MvPolynomial (Fin r) Q, residue V.ring (MvPolynomial.eval₂ φ u P) = MvPolynomial.aeval ub (P.map (residue Q))`. Introduce `P`.

Rewrite using `[MvPolynomial.eval₂_comp_left, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]`. Use `congr 1`. Establish `hmem : ∀ Pb : MvPolynomial (Fin r) (ResidueField Q), MvPolynomial.aeval ub Pb ∈ Algebra.adjoin (ResidueField Q) (Set.range ub)` using `fun Pb => by`. Rewrite using `[Algebra.adjoin_range_eq_range_aeval]`. Conclude with `⟨Pb, rfl⟩`.

Establish `hind : AlgebraicIndependent (ResidueField Q) ub`. Rewrite using `[algebraicIndependent_iff]`. Introduce `Pb hPb`. Assume the negation of the conclusion as `hne`. Take `⟨P, rfl⟩` from `MvPolynomial.map_surjective (residue Q) residue_surjective Pb`.

Take `⟨α, hα⟩` from `MvPolynomial.ne_zero_iff.1 hne`. Rewrite `hα` using `[MvPolynomial.coeff_map]`. Establish `hu` using `hunitP P ⟨α, fun h => hα ((residue_eq_zero_iff _).2 h)⟩`. Rewrite `hu` using `[← residue_ne_zero_iff_isUnit]`. Conclude with `hu ((key P).trans hPb)`.

Establish `halg : Algebra.IsAlgebraic (Algebra.adjoin (ResidueField Q) (Set.range ub)) (ResidueField V.ring)`. Prove the components needed by the constructor for the conclusion. Introduce `y`. Take `⟨f, rfl⟩` from `residue_surjective y`. Take `⟨P, R, hR, hf⟩` from `hloc f`.

Set `a : Algebra.adjoin (ResidueField Q) (Set.range ub)` to `⟨_, hmem (P.map (residue Q))⟩`. Set `b : Algebra.adjoin (ResidueField Q) (Set.range ub)` to `⟨_, hmem (R.map (residue Q))⟩`. Establish `hb : (b : ResidueField V.ring) ≠ 0`. Express the relevant statement in the definitionally equal form `MvPolynomial.aeval ub (R.map (residue Q)) ≠ 0`. Rewrite using `[← key]`.

Conclude with `(residue_ne_zero_iff_isUnit _).2 hR`. Establish `hb0 : b ≠ 0` using `fun h => hb (by rw [h]; rfl)`. Use `⟨Polynomial.C b * Polynomial.X - Polynomial.C a, fun h => hb0 ?_, ?_⟩` and prove the remaining obligations. Simplify using `using congrArg (Polynomial.coeff · 1) h`. Establish `e` using `congrArg (residue V.ring) hf`.

Rewrite `e` using `[map_mul, key, key]`. Simplify using `only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]`. Express the relevant statement in the definitionally equal form `(b : ResidueField V.ring) * residue V.ring f - (a : ResidueField V.ring) = 0`. Express the relevant statement in the definitionally equal form `residue V.ring f * (b : ResidueField V.ring) = (a : ResidueField V.ring) at e`. Rewrite using `[mul_comm, e, sub_self]`.

Establish `hub : IsTranscendenceBasis (ResidueField Q) ub` using `hind.isTranscendenceBasis_iff_isAlgebraic.2 halg`. Take `⟨T, hT⟩` from `exists_isTranscendenceBasis ℂ (ResidueField Q)`. Establish `hB` using `hT.sumElim_comp hub`. Establish `hc : (r : Cardinal) + Cardinal.mk T = ((N - 1 : ℕ) : Cardinal)`. Rewrite using `[← h3, ← hB.cardinalMk_eq_trdeg, Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id, Cardinal.mk_fin]`.

Use `haveI hfin : Finite T := Cardinal.lt_aleph0_iff_finite.1 (lt_of_le_of_lt le_add_self (by rw [hc]; exact Cardinal.natCast_lt_aleph0))`. Establish `hcard : r + Nat.card T = N - 1`. Rewrite `hc` using `[← Nat.cast_card (α := T)]`. Conclude with `hc` after adjusting the coercions. Use `set j := Nat.card T with hj`.

Set `e : Fin j ≃ T` to `(Finite.equivFin T).symm`. Set `s : Fin j → Q` to `fun i => Function.surjInv residue_surjective ((e i : ResidueField Q))`. Establish `hs : ∀ i, residue Q (s i) = (e i : ResidueField Q)` using `fun i => Function.surjInv_eq residue_surjective _`. Set `g : Fin (r + j) → Fin r ⊕ T` to `fun i => Sum.map id e (finSumFinEquiv.symm i)`. Establish `hg : Function.Injective g` using `(Sum.map_injective.2 ⟨Function.injective_id, e.injective⟩).comp finSumFinEquiv.symm.injective`.

Establish `hind2` using `hB.1.comp g hg`. Establish `hv : residue V.ring ∘ (Fin.append u fun i => (⟨s i, hC _ (s i).2⟩ : V.ring)) = Sum.elim ub (algebraMap (ResidueField Q) (ResidueField V.ring) ∘ Subtype.val) ∘ g`. Use function extensionality and compare the values at `i`. Use `Fin.addCases (fun i => ?_) (fun i => ?_) i` and prove the remaining obligations. Simplify using `[g, ub, Fin.append_left]`.

Simplify using `only [Function.comp_apply, Fin.append_right, g, finSumFinEquiv_symm_apply_natAdd, Sum.map_inr, Sum.elim_inr]`. Rewrite using `[← hs, ResidueField.algebraMap_residue]`. Both sides reduce to the same expression. Use `⟨j, s, by omega, fun P hP => ?_⟩` and prove the remaining obligations. Rewrite using `[← residue_ne_zero_iff_isUnit, MvPolynomial.eval₂_comp_left]`.

Express the relevant statement in the definitionally equal form `MvPolynomial.aeval (residue V.ring ∘ _) P ≠ 0`. Rewrite using `[hv]`. Conclude with `fun h0 => hP (algebraicIndependent_iff.1 hind2 P h0)`.
-/
theorem exists_residue_coords_of_locModel : ∀ {L : Type} [Field L] (c : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel c Q),
    letI := hQ.isLocalRing; ∀ (N r : ℕ) (V : Place c) (hC : V.Contains Q) (u : Fin r → V.ring),
    (∃ x : Fin N → L, TrBasis c x) →
    (∀ q ∈ IsLocalRing.maximalIdeal Q,
      (⟨q, hC _ q.2⟩ : V.ring) ∈ IsLocalRing.maximalIdeal V.ring) →
    (∀ P : MvPolynomial (Fin r) Q, (∃ α, P.coeff α ∉ IsLocalRing.maximalIdeal Q) →
      IsUnit (MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u P)) →
    (∀ f : V.ring, ∃ P R : MvPolynomial (Fin r) Q,
      IsUnit (MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u R) ∧
      f * MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u R =
        MvPolynomial.eval₂ (Q.subtype.codRestrict V.ring fun q => hC _ q.2) u P) →
    ∃ (j : ℕ) (s : Fin j → Q), r + j + 1 = N ∧
      ∀ P : MvPolynomial (Fin (r + j)) ℂ, P ≠ 0 →
        IsUnit (MvPolynomial.eval₂ V.const
          (Fin.append u fun i => (⟨s i, hC _ (s i).2⟩ : V.ring)) P) := by
  intro L _ c Q hQ
  letI := hQ.isLocalRing
  intro N r V hC u hx hm hunitP hloc
  classical
  let φ : Q →+* V.ring := Q.subtype.codRestrict V.ring fun q => hC _ q.2
  letI : Algebra ℂ V.ring := V.const.toAlgebra
  letI : Algebra ℂ L := c.toAlgebra
  letI : Algebra ℂ Q := (c.codRestrict Q hQ.const_mem).toAlgebra
  letI : Algebra Q V.ring := φ.toAlgebra
  haveI : IsScalarTower ℂ V.ring L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower ℂ Q V.ring := IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl
  haveI : IsLocalHom (algebraMap Q V.ring) := ⟨fun q hq => by
    by_contra hq'
    have hqm : q ∈ maximalIdeal Q := (mem_maximalIdeal _).2 hq'
    exact (mem_maximalIdeal _).1 (hm q hqm) hq⟩
  haveI : Algebra.EssFiniteType ℂ V.ring := V.essFiniteType
  haveI := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ V.ring
  obtain ⟨x, hx⟩ := hx
  have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hx
  rw [Cardinal.mk_fin] at h2
  have h3 := trdeg_residueField_of_trdeg ℂ V.ring L h2.symm
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible V.ring
  obtain ⟨hN, -⟩ := exists_basis_kaehler_of_trdeg ℂ L h2.symm ht
  let ub : Fin r → ResidueField V.ring := fun i => residue V.ring (u i)
  have key : ∀ P : MvPolynomial (Fin r) Q, residue V.ring (MvPolynomial.eval₂ φ u P) =
      MvPolynomial.aeval ub (P.map (residue Q)) := by
    intro P
    rw [MvPolynomial.eval₂_comp_left, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    congr 1
  have hmem : ∀ Pb : MvPolynomial (Fin r) (ResidueField Q),
      MvPolynomial.aeval ub Pb ∈ Algebra.adjoin (ResidueField Q) (Set.range ub) := fun Pb => by
    rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨Pb, rfl⟩
  have hind : AlgebraicIndependent (ResidueField Q) ub := by
    rw [algebraicIndependent_iff]
    intro Pb hPb
    by_contra hne
    obtain ⟨P, rfl⟩ := MvPolynomial.map_surjective (residue Q) residue_surjective Pb
    obtain ⟨α, hα⟩ := MvPolynomial.ne_zero_iff.1 hne
    rw [MvPolynomial.coeff_map] at hα
    have hu := hunitP P ⟨α, fun h => hα ((residue_eq_zero_iff _).2 h)⟩
    rw [← residue_ne_zero_iff_isUnit] at hu
    exact hu ((key P).trans hPb)
  have halg : Algebra.IsAlgebraic (Algebra.adjoin (ResidueField Q) (Set.range ub))
      (ResidueField V.ring) := by
    constructor
    intro y
    obtain ⟨f, rfl⟩ := residue_surjective y
    obtain ⟨P, R, hR, hf⟩ := hloc f
    let a : Algebra.adjoin (ResidueField Q) (Set.range ub) := ⟨_, hmem (P.map (residue Q))⟩
    let b : Algebra.adjoin (ResidueField Q) (Set.range ub) := ⟨_, hmem (R.map (residue Q))⟩
    have hb : (b : ResidueField V.ring) ≠ 0 := by
      change MvPolynomial.aeval ub (R.map (residue Q)) ≠ 0
      rw [← key]; exact (residue_ne_zero_iff_isUnit _).2 hR
    have hb0 : b ≠ 0 := fun h => hb (by rw [h]; rfl)
    refine ⟨Polynomial.C b * Polynomial.X - Polynomial.C a, fun h => hb0 ?_, ?_⟩
    · simpa using congrArg (Polynomial.coeff · 1) h
    · have e := congrArg (residue V.ring) hf
      rw [map_mul, key, key] at e
      simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
      change (b : ResidueField V.ring) * residue V.ring f - (a : ResidueField V.ring) = 0
      change residue V.ring f * (b : ResidueField V.ring) = (a : ResidueField V.ring) at e
      rw [mul_comm, e, sub_self]
  have hub : IsTranscendenceBasis (ResidueField Q) ub := hind.isTranscendenceBasis_iff_isAlgebraic.2 halg
  obtain ⟨T, hT⟩ := exists_isTranscendenceBasis ℂ (ResidueField Q)
  have hB := hT.sumElim_comp hub
  have hc : (r : Cardinal) + Cardinal.mk T = ((N - 1 : ℕ) : Cardinal) := by
    rw [← h3, ← hB.cardinalMk_eq_trdeg, Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id,
      Cardinal.mk_fin]
  haveI hfin : Finite T := Cardinal.lt_aleph0_iff_finite.1
    (lt_of_le_of_lt le_add_self (by rw [hc]; exact Cardinal.natCast_lt_aleph0))
  have hcard : r + Nat.card T = N - 1 := by
    rw [← Nat.cast_card (α := T)] at hc
    exact_mod_cast hc
  set j := Nat.card T with hj
  let e : Fin j ≃ T := (Finite.equivFin T).symm
  let s : Fin j → Q := fun i => Function.surjInv residue_surjective ((e i : ResidueField Q))
  have hs : ∀ i, residue Q (s i) = (e i : ResidueField Q) := fun i =>
    Function.surjInv_eq residue_surjective _
  let g : Fin (r + j) → Fin r ⊕ T := fun i => Sum.map id e (finSumFinEquiv.symm i)
  have hg : Function.Injective g :=
    (Sum.map_injective.2 ⟨Function.injective_id, e.injective⟩).comp finSumFinEquiv.symm.injective
  have hind2 := hB.1.comp g hg
  have hv : residue V.ring ∘ (Fin.append u fun i => (⟨s i, hC _ (s i).2⟩ : V.ring)) =
      Sum.elim ub (algebraMap (ResidueField Q) (ResidueField V.ring) ∘ Subtype.val) ∘ g := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp [g, ub, Fin.append_left]
    · simp only [Function.comp_apply, Fin.append_right, g, finSumFinEquiv_symm_apply_natAdd,
        Sum.map_inr, Sum.elim_inr]
      rw [← hs, ResidueField.algebraMap_residue]
      rfl
  refine ⟨j, s, by omega, fun P hP => ?_⟩
  rw [← residue_ne_zero_iff_isUnit, MvPolynomial.eval₂_comp_left]
  change MvPolynomial.aeval (residue V.ring ∘ _) P ≠ 0
  rw [hv]
  exact fun h0 => hP (algebraicIndependent_iff.1 hind2 P h0)

end GlobalTheory.FieldPair
