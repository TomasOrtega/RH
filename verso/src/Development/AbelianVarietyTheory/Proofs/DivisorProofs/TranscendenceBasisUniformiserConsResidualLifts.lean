import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.AdjKltOfLtDisc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrdDFormUniformiserCons
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

open IsLocalRing Polynomial

/- English proof (translation)
It suffices to establish `h : ∀ d (p : R[X]), p.natDegree = d → (∀ i, p.coeff i ≠ 0 → IsUnit (p.coeff i)) → p.eval f = 0 → p = 0 from h _ p rfl hu he`. Introduce `d`. Proceed by induction on `d using Nat.strong_induction_on with`. Consider the case `_ d ih`. Introduce `p hd hu he`.

Establish `hsplit` using `X_mul_divX_add p`. Establish `h2 : p.eval f = f * (divX p).eval f + p.coeff 0`. Establish `h3` using `congrArg (Polynomial.eval f) hsplit`. Simplify using `only [eval_add, eval_mul, eval_X, eval_C] at h3`. Conclude with `h3.symm`.

Establish `he' : f * (divX p).eval f + p.coeff 0 = 0` using `by rw [← h2]; exact he`. Establish `hc0 : p.coeff 0 = 0`. Assume the negation of the conclusion as `hc`. Establish `hmem : p.coeff 0 ∈ maximalIdeal R`. Establish `e : p.coeff 0 = -(f * (divX p).eval f)` using `by linear_combination he'`.

Rewrite using `[e]`. Conclude with `(maximalIdeal R).neg_mem ((maximalIdeal R).mul_mem_right _ hfm)`. Conclude with `(mem_maximalIdeal _).1 hmem (hu 0 hc)`. Establish `hdv : (divX p).eval f = 0`. Rewrite `he'` using `[hc0, add_zero]`.

Conclude with `(mul_eq_zero.1 he').resolve_left hf0`. Break down `Nat.eq_zero_or_pos d with hd0 | hdpos` into its components or cases. Rewrite using `[eq_C_of_natDegree_eq_zero (hd.trans hd0), hc0, C_0]`. Establish `h0 : divX p = 0` using `ih (d - 1) (by omega) (divX p) (by rw [natDegree_divX_eq_natDegree_tsub_one, hd]) (fun i hi => by rw [coeff_divX] at hi ⊢; exact hu _ hi) hdv`. Rewrite using `[← hsplit, h0, hc0, mul_zero, C_0, add_zero]`.
-/
theorem eq_zero_of_eval_mem_maximalIdeal {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    {f : R} (hf0 : f ≠ 0) (hfm : f ∈ maximalIdeal R) (p : R[X])
    (hu : ∀ i, p.coeff i ≠ 0 → IsUnit (p.coeff i)) (he : p.eval f = 0) : p = 0 := by
  suffices h : ∀ d (p : R[X]), p.natDegree = d → (∀ i, p.coeff i ≠ 0 → IsUnit (p.coeff i)) →
      p.eval f = 0 → p = 0 from h _ p rfl hu he
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro p hd hu he
  have hsplit := X_mul_divX_add p
  have h2 : p.eval f = f * (divX p).eval f + p.coeff 0 := by
    have h3 := congrArg (Polynomial.eval f) hsplit
    simp only [eval_add, eval_mul, eval_X, eval_C] at h3
    exact h3.symm
  have he' : f * (divX p).eval f + p.coeff 0 = 0 := by rw [← h2]; exact he
  have hc0 : p.coeff 0 = 0 := by
    by_contra hc
    have hmem : p.coeff 0 ∈ maximalIdeal R := by
      have e : p.coeff 0 = -(f * (divX p).eval f) := by linear_combination he'
      rw [e]
      exact (maximalIdeal R).neg_mem ((maximalIdeal R).mul_mem_right _ hfm)
    exact (mem_maximalIdeal _).1 hmem (hu 0 hc)
  have hdv : (divX p).eval f = 0 := by
    rw [hc0, add_zero] at he'
    exact (mul_eq_zero.1 he').resolve_left hf0
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · rw [eq_C_of_natDegree_eq_zero (hd.trans hd0), hc0, C_0]
  · have h0 : divX p = 0 := ih (d - 1) (by omega) (divX p)
      (by rw [natDegree_divX_eq_natDegree_tsub_one, hd])
      (fun i hi => by rw [coeff_divX] at hi ⊢; exact hu _ hi) hdv
    rw [← hsplit, h0, hc0, mul_zero, C_0, add_zero]

/- English proof (translation)
Introduce `L K _ _ cL cK n S ψ f w hψ hc hf hwK`. Use `letI : Algebra ℂ S.ring := S.const.toAlgebra`. Use `letI : Algebra ℂ L := cL.toAlgebra`. Use `letI : Algebra ℂ K := cK.toAlgebra`. Use `haveI : IsScalarTower ℂ S.ring L := IsScalarTower.of_algebraMap_eq' rfl`.

Establish `hcomp : ψ.comp (algebraMap ℂ S.ring) = algebraMap ℂ K` using `RingHom.ext hc`. Use `haveI : Algebra.EssFiniteType ℂ S.ring := S.essFiniteType`. Use `haveI := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ S.ring`. Establish `hker : RingHom.ker ψ = maximalIdeal S.ring` using `by haveI := RingHom.ker_isMaximal_of_surjective ψ hψ`. Conclude with `IsLocalRing.eq_maximalIdeal this`.

Establish `hunit : ∀ g : S.ring, ψ g ≠ 0 → IsUnit g`. Introduce `g hg`. Assume the negation of the conclusion as `hu`. Conclude with `hg (by rw [← RingHom.mem_ker, hker]; exact hu)`. Establish `hwu : ∀ P : MvPolynomial (Fin n) ℂ, P ≠ 0 → IsUnit (MvPolynomial.eval₂ (algebraMap ℂ S.ring) w P)`.

Introduce `P hP`. Apply `hunit` to reduce the goal to its premises. Rewrite using `[MvPolynomial.hom_eval₂, hcomp]`. Introduce `h0`. Establish `hind : AlgebraicIndependent ℂ (fun i => ψ (w i))` using `hwK.1`.

Conclude with `hP ((algebraicIndependent_iff.1 hind) P h0)`. Take `⟨m, z, b, -, -⟩` from `exists_basis_kaehler_uniformiser ℂ hf`. Establish `hL : Algebra.trdeg ℂ L = (m + 1 : ℕ)` using `trdeg_eq_of_basis_kaehler ℂ L b`. Establish `hR` using `trdeg_residueField_of_trdeg ℂ S.ring L hL`. Simplify using `only [add_tsub_cancel_right] at hR`.

Establish `hK : Algebra.trdeg ℂ K = n`. Use `IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hwK` as an intermediate fact. Rewrite `this` using `[Cardinal.mk_fin]`. Conclude with `this.symm`. Establish `hmn : m ≤ n`.

Take `⟨s, hs⟩` from `exists_isTranscendenceBasis ℂ (ResidueField S.ring)`. Set `res` to `IsLocalRing.residue S.ring`. Set `lift : s → S.ring` to `fun i => Function.surjInv IsLocalRing.residue_surjective (i : _)`. Establish `hlift : res ∘ lift = Subtype.val` using `funext fun i => Function.surjInv_eq IsLocalRing.residue_surjective _`. Establish `hg : AlgebraicIndependent ℂ (fun i => ψ (lift i))`.

Use `algebraicIndependent_iff.2 fun P hP => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `hu : IsUnit (MvPolynomial.eval₂ (algebraMap ℂ S.ring) lift P)`. Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, MvPolynomial.eval₂_comp_left]`. Express the relevant statement in the definitionally equal form `MvPolynomial.aeval (res ∘ lift) P ≠ 0`.

Rewrite using `[hlift]`. Conclude with `fun h0 => hne (algebraicIndependent_iff.1 hs.1 P h0)`. Apply `(hu.map ψ).ne_zero` to reduce the goal to its premises. Rewrite using `[MvPolynomial.hom_eval₂, hcomp]`. Conclude with `hP`.

Establish `h1` using `hg.cardinalMk_le_trdeg`. Rewrite `h1` using `[hs.cardinalMk_eq_trdeg, hR, hK]`. Conclude with `h1` after adjusting the coercions. Establish `hsplit : ∀ P : MvPolynomial (Fin (n + 1)) ℂ, MvPolynomial.eval₂ (algebraMap ℂ S.ring) (Fin.cons f w : Fin (n + 1) → S.ring) P = Polynomial.eval f (Polynomial.map (MvPolynomial.eval₂Hom (algebraMap ℂ S.ring) w) (MvPolynomial.finSuccEquiv ℂ n P))`. Introduce `P`.

Establish `hrh : MvPolynomial.eval₂Hom (algebraMap ℂ S.ring) (Fin.cons f w : Fin (n + 1) → S.ring) = (Polynomial.evalRingHom f).comp ((Polynomial.mapRingHom (MvPolynomial.eval₂Hom (algebraMap ℂ S.ring) w)).comp (MvPolynomial.finSuccEquiv ℂ n : MvPolynomial (Fin (n + 1)) ℂ →+* _))`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using `[MvPolynomial.finSuccEquiv_apply]`. Introduce `i`.

Apply the tactic sequence `refine Fin.cases ?_ (fun j => ?_) i <;>`. Simplify using `[MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ]`. Conclude with `RingHom.congr_fun hrh P`. Establish `hcoe : ∀ P : MvPolynomial (Fin (n + 1)) ℂ, MvPolynomial.aeval (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L) P = ((MvPolynomial.eval₂ (algebraMap ℂ S.ring) (Fin.cons f w : Fin (n + 1) → S.ring) P : S.ring) : L)`. Introduce `P`.

Establish `h` using `MvPolynomial.hom_eval₂ P (algebraMap ℂ S.ring) S.ring.subtype (Fin.cons f w : Fin (n + 1) → S.ring)`. Rewrite `h` using `[ValuationSubring.subtype_apply]`. Rewrite using `[h, MvPolynomial.aeval_def]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Apply the tactic sequence `refine Fin.cases ?_ (fun j => ?_) i <;> simp`. Establish `hind : AlgebraicIndependent ℂ (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L)`. Use `algebraicIndependent_iff.2 fun P hP => ?_` and prove the remaining obligations. Rewrite `hP` using `[hcoe, ZeroMemClass.coe_eq_zero, hsplit]`. Use `set Q := MvPolynomial.finSuccEquiv ℂ n P with hQ`.

Establish `hq` using `eq_zero_of_eval_mem_maximalIdeal hf.ne_zero hf.not_isUnit _ (fun i hi => by`. Rewrite `hi`, the goal using `[Polynomial.coeff_map]`. Use `hwu _ fun h0 => hi ?_` and prove the remaining obligations. Rewrite using `[h0, map_zero]) hP`. Establish `hQ0 : Q = 0` using `by ext1 i`.

Rewrite using `[Polynomial.coeff_zero]`. Assume the negation of the conclusion as `h0`. Apply `(hwu _ h0).ne_zero` to reduce the goal to its premises. Use `congrArg (fun p => Polynomial.coeff p i) hq` as an intermediate fact. Simplify `this` using `[Polynomial.coeff_map]`.

Conclude with `(MvPolynomial.finSuccEquiv ℂ n).injective (by rw [← hQ, hQ0, map_zero])`. Establish `htr : TrBasis cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L)`. Unfold `TrBasis`. Use `hind.isTranscendenceBasis_of_trdeg_le_of_finite ?_` and prove the remaining obligations. Rewrite using `[hL, Cardinal.mk_fin]`.

Conclude with `(by omega : m + 1 ≤ n + 1)` after adjusting the coercions. Use `⟨htr, ?_, S.ord_irreducible hf, fun g hg => S.ord_eq_zero (hunit g hg)⟩` and prove the remaining obligations. Conclude with `GlobalTheory.formOrd_dForm_uniformiser_cons cL n S f w hf hwu ⟨_, htr⟩`.
-/
theorem trBasis_uniformiser_cons : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K)
    (n : ℕ) (S : Place cL) (ψ : S.ring →+* K) (f : S.ring) (w : Fin n → S.ring),
    Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) → Irreducible f →
    TrBasis cK (fun i => ψ (w i)) →
    TrBasis cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L) ∧
      S.formOrd (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L)) = 0 ∧
      S.ord (f : L) = 1 ∧ ∀ g : S.ring, ψ g ≠ 0 → S.ord (g : L) = 0 := by
  intro L K _ _ cL cK n S ψ f w hψ hc hf hwK
  letI : Algebra ℂ S.ring := S.const.toAlgebra
  letI : Algebra ℂ L := cL.toAlgebra
  letI : Algebra ℂ K := cK.toAlgebra
  haveI : IsScalarTower ℂ S.ring L := IsScalarTower.of_algebraMap_eq' rfl
  have hcomp : ψ.comp (algebraMap ℂ S.ring) = algebraMap ℂ K := RingHom.ext hc
  haveI : Algebra.EssFiniteType ℂ S.ring := S.essFiniteType
  haveI := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ S.ring
  have hker : RingHom.ker ψ = maximalIdeal S.ring := by
    haveI := RingHom.ker_isMaximal_of_surjective ψ hψ
    exact IsLocalRing.eq_maximalIdeal this
  have hunit : ∀ g : S.ring, ψ g ≠ 0 → IsUnit g := by
    intro g hg
    by_contra hu
    exact hg (by rw [← RingHom.mem_ker, hker]; exact hu)
  have hwu : ∀ P : MvPolynomial (Fin n) ℂ, P ≠ 0 →
      IsUnit (MvPolynomial.eval₂ (algebraMap ℂ S.ring) w P) := by
    intro P hP
    apply hunit
    rw [MvPolynomial.hom_eval₂, hcomp]
    intro h0
    have hind : AlgebraicIndependent ℂ (fun i => ψ (w i)) := hwK.1
    exact hP ((algebraicIndependent_iff.1 hind) P h0)

  obtain ⟨m, z, b, -, -⟩ := exists_basis_kaehler_uniformiser ℂ hf
  have hL : Algebra.trdeg ℂ L = (m + 1 : ℕ) := trdeg_eq_of_basis_kaehler ℂ L b
  have hR := trdeg_residueField_of_trdeg ℂ S.ring L hL
  simp only [add_tsub_cancel_right] at hR
  have hK : Algebra.trdeg ℂ K = n := by
    have := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hwK
    rw [Cardinal.mk_fin] at this
    exact this.symm
  have hmn : m ≤ n := by
    obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℂ (ResidueField S.ring)
    let res := IsLocalRing.residue S.ring
    let lift : s → S.ring := fun i => Function.surjInv IsLocalRing.residue_surjective (i : _)
    have hlift : res ∘ lift = Subtype.val := funext fun i =>
      Function.surjInv_eq IsLocalRing.residue_surjective _
    have hg : AlgebraicIndependent ℂ (fun i => ψ (lift i)) := by
      refine algebraicIndependent_iff.2 fun P hP => ?_
      by_contra hne
      have hu : IsUnit (MvPolynomial.eval₂ (algebraMap ℂ S.ring) lift P) := by
        rw [← IsLocalRing.residue_ne_zero_iff_isUnit, MvPolynomial.eval₂_comp_left]
        change MvPolynomial.aeval (res ∘ lift) P ≠ 0
        rw [hlift]
        exact fun h0 => hne (algebraicIndependent_iff.1 hs.1 P h0)
      apply (hu.map ψ).ne_zero
      rw [MvPolynomial.hom_eval₂, hcomp]
      exact hP
    have h1 := hg.cardinalMk_le_trdeg
    rw [hs.cardinalMk_eq_trdeg, hR, hK] at h1
    exact_mod_cast h1

  have hsplit : ∀ P : MvPolynomial (Fin (n + 1)) ℂ,
      MvPolynomial.eval₂ (algebraMap ℂ S.ring) (Fin.cons f w : Fin (n + 1) → S.ring) P =
        Polynomial.eval f (Polynomial.map (MvPolynomial.eval₂Hom (algebraMap ℂ S.ring) w)
          (MvPolynomial.finSuccEquiv ℂ n P)) := by
    intro P
    have hrh : MvPolynomial.eval₂Hom (algebraMap ℂ S.ring) (Fin.cons f w : Fin (n + 1) → S.ring) =
        (Polynomial.evalRingHom f).comp
          ((Polynomial.mapRingHom (MvPolynomial.eval₂Hom (algebraMap ℂ S.ring) w)).comp
            (MvPolynomial.finSuccEquiv ℂ n : MvPolynomial (Fin (n + 1)) ℂ →+* _)) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [MvPolynomial.finSuccEquiv_apply]
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i <;>
          simp [MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ]
    exact RingHom.congr_fun hrh P
  have hcoe : ∀ P : MvPolynomial (Fin (n + 1)) ℂ,
      MvPolynomial.aeval (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L) P =
        ((MvPolynomial.eval₂ (algebraMap ℂ S.ring) (Fin.cons f w : Fin (n + 1) → S.ring) P :
          S.ring) : L) := by
    intro P
    have h := MvPolynomial.hom_eval₂ P (algebraMap ℂ S.ring) S.ring.subtype
      (Fin.cons f w : Fin (n + 1) → S.ring)
    rw [ValuationSubring.subtype_apply] at h
    rw [h, MvPolynomial.aeval_def]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have hind : AlgebraicIndependent ℂ (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L) := by
    refine algebraicIndependent_iff.2 fun P hP => ?_
    rw [hcoe, ZeroMemClass.coe_eq_zero, hsplit] at hP
    set Q := MvPolynomial.finSuccEquiv ℂ n P with hQ
    have hq := eq_zero_of_eval_mem_maximalIdeal hf.ne_zero hf.not_isUnit _ (fun i hi => by
      rw [Polynomial.coeff_map] at hi ⊢
      refine hwu _ fun h0 => hi ?_
      rw [h0, map_zero]) hP
    have hQ0 : Q = 0 := by
      ext1 i
      rw [Polynomial.coeff_zero]
      by_contra h0
      apply (hwu _ h0).ne_zero
      have := congrArg (fun p => Polynomial.coeff p i) hq
      simpa [Polynomial.coeff_map] using this
    exact (MvPolynomial.finSuccEquiv ℂ n).injective (by rw [← hQ, hQ0, map_zero])
  have htr : TrBasis cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L) := by
    unfold TrBasis
    refine hind.isTranscendenceBasis_of_trdeg_le_of_finite ?_
    rw [hL, Cardinal.mk_fin]
    exact_mod_cast (by omega : m + 1 ≤ n + 1)
  refine ⟨htr, ?_, S.ord_irreducible hf, fun g hg => S.ord_eq_zero (hunit g hg)⟩
  exact GlobalTheory.formOrd_dForm_uniformiser_cons cL n S f w hf hwu ⟨_, htr⟩

end GlobalTheory.FieldPair
