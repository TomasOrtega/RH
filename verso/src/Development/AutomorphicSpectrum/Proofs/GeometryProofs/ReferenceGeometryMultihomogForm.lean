import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GapN
import Development.WeilBound.CoreStatements.VolumeEquality.ChartMeetsPoint
import Development.WeilBound.CoreStatements.VolumeEquality.CoverRootsSch
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRingHomComplexCompEqOfCountable
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointComponentLocalRing
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFibreNormDehomRoots
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.ExRefEff

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ExRefEff.BdForm

open MvPolynomial

section Forms

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

def bdeg (m : (Σ k, J k) →₀ ℕ) : K → ℕ := fun k => ∑ i, m ⟨k, i⟩

open Classical in

def bcomp (g : MRing J) (d : K → ℕ) : MRing J :=
  ∑ m ∈ g.support.filter (fun m => bdeg m = d), monomial m (coeff m g)

open Classical in
/- English proof (translation)
Rewrite using `[bcomp, coeff_sum]`. Simplify using `only [coeff_monomial]`. Rewrite using `[Finset.sum_ite_eq']`. Simplify using `only [Finset.mem_filter, mem_support_iff]`. Apply the tactic sequence `by_cases h : bdeg m = d <;> by_cases h' : coeff m g = 0 <;> simp [h, h']`.
-/
theorem coeff_bcomp (g : MRing J) (d : K → ℕ) (m : (Σ k, J k) →₀ ℕ) :
    coeff m (bcomp g d) = if bdeg m = d then coeff m g else 0 := by
  rw [bcomp, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, mem_support_iff]
  by_cases h : bdeg m = d <;> by_cases h' : coeff m g = 0 <;> simp [h, h']

/- English proof (translation)
Introduce `m hm k`. Rewrite `hm` using `[mem_support_iff, coeff_bcomp]`. Establish `h : bdeg m = d`. Assume the negation of the conclusion as `h`. Conclude with `hm (if_neg h)`.

Conclude with `congrFun h k`.
-/
theorem bcomp_homog (g : MRing J) (d : K → ℕ) : IsMultiHomog (bcomp g d) d := by
  classical
  intro m hm k
  rw [mem_support_iff, coeff_bcomp] at hm
  have h : bdeg m = d := by
    by_contra h
    exact hm (if_neg h)
  exact congrFun h k

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[coeff_sum]`. Distinguish the cases in `h : coeff m g = 0`. Rewrite using `[h]`. Use `Finset.sum_eq_zero fun d _ => ?_` and prove the remaining obligations.

Rewrite using `[coeff_bcomp]`. Use `split_ifs`. Conclude with `h`. Both sides reduce to the same expression. Rewrite using `[Finset.sum_eq_single (bdeg m)]`.

Rewrite using `[coeff_bcomp, if_pos rfl]`. Introduce `d _ hd`. Rewrite using `[coeff_bcomp, if_neg (Ne.symm hd)]`. Introduce `hn`. Conclude with `absurd (Finset.mem_image_of_mem _ (mem_support_iff.2 h)) hn`.
-/
theorem sum_bcomp [DecidableEq (K → ℕ)] (g : MRing J) : ∑ d ∈ g.support.image bdeg, bcomp g d = g := by
  classical
  ext m
  rw [coeff_sum]
  by_cases h : coeff m g = 0
  · rw [h]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [coeff_bcomp]
    split_ifs
    · exact h
    · rfl
  · rw [Finset.sum_eq_single (bdeg m)]
    · rw [coeff_bcomp, if_pos rfl]
    · intro d _ hd
      rw [coeff_bcomp, if_neg (Ne.symm hd)]
    · intro hn
      exact absurd (Finset.mem_image_of_mem _ (mem_support_iff.2 h)) hn

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[coeff_bcomp, coeff_zero]`. Use `split_ifs with e`. Assume the negation of the conclusion as `h0`. Conclude with `h (e ▸ Finset.mem_image_of_mem _ (mem_support_iff.2 h0))`.

Both sides reduce to the same expression.
-/
theorem bcomp_eq_zero [DecidableEq (K → ℕ)] (g : MRing J) {d : K → ℕ} (h : d ∉ g.support.image bdeg) : bcomp g d = 0 := by
  classical
  ext m
  rw [coeff_bcomp, coeff_zero]
  split_ifs with e
  · by_contra h0
    exact h (e ▸ Finset.mem_image_of_mem _ (mem_support_iff.2 h0))
  · rfl

/- English proof (translation)
Rewrite `h` using `[← sum_bcomp g, map_sum]`. Take `⟨d, -, hd⟩` from `Finset.exists_ne_zero_of_sum_ne_zero h`. Conclude with `⟨d, hd⟩`.
-/
theorem exists_aeval_bcomp_ne {Ω : Type} [Field Ω] (t : (Σ k, J k) → Ω) (g : MRing J) (h : aeval t g ≠ 0) :
    ∃ d : K → ℕ, aeval t (bcomp g d) ≠ 0 := by
  classical
  rw [← sum_bcomp g, map_sum] at h
  obtain ⟨d, -, hd⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨d, hd⟩

/- English proof (translation)
Establish `h0 : mConeMap w g = 0`. Use `funext_set (fun _ => ({0}ᶜ : Set ℂ)) (fun _ => (Set.finite_singleton (0 : ℂ)).infinite_compl) fun c hc => ?_` and prove the remaining obligations. Rewrite using `[map_zero, GroundTheory.Heights₂.Heights.HilbertSamuel.FibreNormDehomRoots.eval_mConeMap]`. Conclude with `h c fun k => hc k (Set.mem_univ k)`. Establish `h1 : mConeMap w g = ∑ d' ∈ g.support.image bdeg, C (aeval w (bcomp g d')) * ∏ k, X k ^ d' k` using `by conv_lhs => rw [← sum_bcomp g, map_sum]`.

Conclude with `Finset.sum_congr rfl fun d' _ => GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.mConeMap_eq_of_isMultiHomog w (bcomp_homog g d')`. Establish `hm : ∀ d' : K → ℕ, (∏ k, (X k : MvPolynomial K ℂ) ^ d' k) = monomial (Finsupp.equivFunOnFinite.symm d') 1`. Introduce `d'`. Rewrite using `[monomial_eq, C_1, _root_.one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]`. Both sides reduce to the same expression.

Distinguish the cases in `hd : d ∈ g.support.image bdeg`. Establish `h2` using `congrArg (coeff (Finsupp.equivFunOnFinite.symm d)) (h1.symm.trans h0)`. Rewrite `h2` using `[coeff_sum, coeff_zero]`. Simplify using `only [hm, coeff_C_mul, coeff_monomial, mul_ite, _root_.mul_one, mul_zero, EmbeddingLike.apply_eq_iff_eq] at h2`. Rewrite `h2` using `[Finset.sum_ite_eq', if_pos hd]`. Then use the resulting hypothesis.

Rewrite using `[bcomp_eq_zero g hd, map_zero]`.
-/
theorem aeval_bcomp_eq_zero (w : (Σ k, J k) → ℂ) (g : MRing J)
    (h : ∀ c : K → ℂ, (∀ k, c k ≠ 0) → aeval (fun p => w p * c p.1) g = 0) (d : K → ℕ) :
    aeval w (bcomp g d) = 0 := by
  classical
  have h0 : mConeMap w g = 0 := by
    refine funext_set (fun _ => ({0}ᶜ : Set ℂ)) (fun _ => (Set.finite_singleton (0 : ℂ)).infinite_compl) fun c hc => ?_
    rw [map_zero, GroundTheory.Heights₂.Heights.HilbertSamuel.FibreNormDehomRoots.eval_mConeMap]
    exact h c fun k => hc k (Set.mem_univ k)
  have h1 : mConeMap w g = ∑ d' ∈ g.support.image bdeg, C (aeval w (bcomp g d')) * ∏ k, X k ^ d' k := by
    conv_lhs => rw [← sum_bcomp g, map_sum]
    exact Finset.sum_congr rfl fun d' _ =>
      GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.mConeMap_eq_of_isMultiHomog w (bcomp_homog g d')
  have hm : ∀ d' : K → ℕ, (∏ k, (X k : MvPolynomial K ℂ) ^ d' k) = monomial (Finsupp.equivFunOnFinite.symm d') 1 := by
    intro d'
    rw [monomial_eq, C_1, _root_.one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rfl
  by_cases hd : d ∈ g.support.image bdeg
  · have h2 := congrArg (coeff (Finsupp.equivFunOnFinite.symm d)) (h1.symm.trans h0)
    rw [coeff_sum, coeff_zero] at h2
    simp only [hm, coeff_C_mul, coeff_monomial, mul_ite, _root_.mul_one, mul_zero, EmbeddingLike.apply_eq_iff_eq] at h2
    rwa [Finset.sum_ite_eq', if_pos hd] at h2
  · rw [bcomp_eq_zero g hd, map_zero]

/- English proof (translation)
Introduce `c _`. Establish `hprod : ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (d k : ℤ))) = ∏ k, (y ⟨k, c k⟩)⁻¹ ^ d k`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Nat.cast_one, _root_.one_mul, zpow_neg, zpow_natCast, inv_pow]`. Rewrite using `[hprod, ← GroundTheory.Heights₂.Heights.HilbertSamuel.FibreNormDehomRoots.aeval_scale hg y (fun k => (y ⟨k, c k⟩)⁻¹), chartRingZ, Algebra.adjoin_range_eq_range_aeval]`.

Use `⟨g, ?_⟩` and prove the remaining obligations. Simplify using `only [div_eq_mul_inv]`. Both sides reduce to the same expression.
-/
theorem mem_chartLat {Ω : Type} [Field Ω] {y : (Σ k, J k) → Ω} {g : MRing J} {d : K → ℕ} (hg : IsMultiHomog g d) :
    aeval y g ∈ chartLat y (fun κ => (d κ : ℤ)) 1 := by
  intro c _
  have hprod : ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (d k : ℤ))) = ∏ k, (y ⟨k, c k⟩)⁻¹ ^ d k := by
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Nat.cast_one, _root_.one_mul, zpow_neg, zpow_natCast, inv_pow]
  rw [hprod, ← GroundTheory.Heights₂.Heights.HilbertSamuel.FibreNormDehomRoots.aeval_scale hg y (fun k => (y ⟨k, c k⟩)⁻¹),
    chartRingZ, Algebra.adjoin_range_eq_range_aeval]
  refine ⟨g, ?_⟩
  simp only [div_eq_mul_inv]
  rfl

/- English proof (translation)
Establish `hprod : ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (d k : ℤ))) = ∏ k, (y ⟨k, c k⟩)⁻¹ ^ d k`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Nat.cast_one, _root_.one_mul, zpow_neg, zpow_natCast, inv_pow]`. Rewrite using `[hprod, ← GroundTheory.Heights₂.Heights.HilbertSamuel.FibreNormDehomRoots.aeval_scale hg y (fun k => (y ⟨k, c k⟩)⁻¹)]`. Simplify using `only [div_eq_mul_inv]`.
-/
theorem dehom_eq {Ω : Type} [Field Ω] (y : (Σ k, J k) → Ω) {g : MRing J} {d : K → ℕ} (hg : IsMultiHomog g d)
    (c : ∀ k, J k) :
    aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-((1 : ℕ) * (d k : ℤ))) = aeval (fun p => y p / y ⟨p.1, c p.1⟩) g := by
  have hprod : ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (d k : ℤ))) = ∏ k, (y ⟨k, c k⟩)⁻¹ ^ d k := by
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Nat.cast_one, _root_.one_mul, zpow_neg, zpow_natCast, inv_pow]
  rw [hprod, ← GroundTheory.Heights₂.Heights.HilbertSamuel.FibreNormDehomRoots.aeval_scale hg y (fun k => (y ⟨k, c k⟩)⁻¹)]
  simp only [div_eq_mul_inv]

end Forms

/- English proof (translation)
The claim follows from `(GlobalTheory.nonempty_algHom_complex_of_countable ℤ k).map AlgHom.toRingHom`.
-/
theorem nonempty_hom_complex (k : Type) [Field k] [CharZero k] [Countable k] : Nonempty (k →+* ℂ) :=
  (GlobalTheory.nonempty_algHom_complex_of_countable ℤ k).map AlgHom.toRingHom

/- English proof (translation)
Set `B` to `A ⧸ P`. Set `F` to `FractionRing B`. Establish `hinj : Function.Injective (algebraMap B F)` using `IsFractionRing.injective B F`. Establish `hB : Countable B` using `Quotient.countable`. Establish `hF : Countable F`.

Use `Function.Surjective.countable (f := fun q : B × B => algebraMap B F q.1 / algebraMap B F q.2) ?_` and prove the remaining obligations. Introduce `x`. Take `⟨a, b, -, rfl⟩` from `IsFractionRing.div_surjective (A := B) x`. Conclude with `⟨(a, b), rfl⟩`. Establish `hc : CharZero F`.

Take `⟨q, hq⟩` from `CharP.exists F`. Break down `CharP.char_is_prime_or_zero F q with h | h` into its components or cases. It suffices to derive a contradiction. Use `hP q h ?_` and prove the remaining obligations. Establish `h1 : algebraMap B F (q : B) = 0`.

Rewrite using `[map_natCast]`. Conclude with `(CharP.cast_eq_zero_iff F q q).2 dvd_rfl`. Establish `h2 : (q : B) = 0` using `hinj (h1.trans (map_zero _).symm)`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`. Conclude with `h2`.

Substitute `h` using the available equality. Conclude with `CharP.charP_to_charZero F`. Take `⟨j⟩` from `nonempty_hom_complex F`. Use `⟨j.comp ((algebraMap B F).comp (Ideal.Quotient.mk P)), fun a => ?_⟩` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply]`.

Rewrite using `[map_eq_zero_iff _ j.injective, map_eq_zero_iff _ hinj, Ideal.Quotient.eq_zero_iff_mem]`.
-/
theorem exists_hom_ker {A : Type} [CommRing A] [Countable A] (P : Ideal A) [P.IsPrime]
    (hP : ∀ r : ℕ, r.Prime → (r : A) ∉ P) : ∃ ψ : A →+* ℂ, ∀ a, ψ a = 0 ↔ a ∈ P := by
  let B := A ⧸ P
  let F := FractionRing B
  have hinj : Function.Injective (algebraMap B F) := IsFractionRing.injective B F
  have hB : Countable B := Quotient.countable
  have hF : Countable F := by
    refine Function.Surjective.countable (f := fun q : B × B => algebraMap B F q.1 / algebraMap B F q.2) ?_
    intro x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    exact ⟨(a, b), rfl⟩
  have hc : CharZero F := by
    obtain ⟨q, hq⟩ := CharP.exists F
    rcases CharP.char_is_prime_or_zero F q with h | h
    · exfalso
      refine hP q h ?_
      have h1 : algebraMap B F (q : B) = 0 := by
        rw [map_natCast]
        exact (CharP.cast_eq_zero_iff F q q).2 dvd_rfl
      have h2 : (q : B) = 0 := hinj (h1.trans (map_zero _).symm)
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact h2
    · subst h
      exact CharP.charP_to_charZero F
  obtain ⟨j⟩ := nonempty_hom_complex F
  refine ⟨j.comp ((algebraMap B F).comp (Ideal.Quotient.mk P)), fun a => ?_⟩
  simp only [RingHom.comp_apply]
  rw [map_eq_zero_iff _ j.injective, map_eq_zero_iff _ hinj, Ideal.Quotient.eq_zero_iff_mem]

section Points

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

/- English proof (translation)
Use `⟨fun k => (h.1 k).imp fun i hi => hi.mul (Ne.isUnit (hc k)), fun k i hu => ?_⟩` and prove the remaining obligations. Establish `hu' : IsUnit (w ⟨k, i⟩)` using `Ne.isUnit (left_ne_zero_of_mul hu.ne_zero)`. Take `⟨h0, h1⟩` from `h.2 k i hu'`. Use `⟨h0, fun j => ?_⟩` and prove the remaining obligations. Take `⟨r, hr, e⟩` from `h1 j`.

Use `⟨r, hr, ?_⟩` and prove the remaining obligations. Use `show w ⟨k, j⟩ * c k = r * (w ⟨k, i⟩ * c k)`. Rewrite using `[e, _root_.mul_assoc]`.
-/
theorem coordsAt_scale {K : Type} {J : K → Type} {y : (Σ k, J k) → Ω} {z : Spec (CommRingCat.of ℂ) ⟶ X}
    {w : (Σ k, J k) → ℂ} (h : CoordsAt ξ y z w) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) :
    CoordsAt ξ y z (fun p => w p * c p.1) := by
  refine ⟨fun k => (h.1 k).imp fun i hi => hi.mul (Ne.isUnit (hc k)), fun k i hu => ?_⟩
  have hu' : IsUnit (w ⟨k, i⟩) := Ne.isUnit (left_ne_zero_of_mul hu.ne_zero)
  obtain ⟨h0, h1⟩ := h.2 k i hu'
  refine ⟨h0, fun j => ?_⟩
  obtain ⟨r, hr, e⟩ := h1 j
  refine ⟨r, hr, ?_⟩
  show w ⟨k, j⟩ * c k = r * (w ⟨k, i⟩ * c k)
  rw [e, _root_.mul_assoc]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, rfl⟩`. Conclude with `⟨(u.isUnit.map (genMap ξ p)).ne_zero, ⟨_, rfl⟩, ⟨((u⁻¹ : (X.presheaf.stalk p.1)ˣ) : X.presheaf.stalk p.1), map_units_inv (genMap ξ p) u⟩⟩`. Introduce and unpack `⟨h0, -, t, ht⟩`. Use `isUnit_iff_exists_inv.2 ⟨t, hξ.inj p ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, ht, mul_inv_cancel₀ h0, map_one]`.
-/
theorem isUnit_stalk_iff (hξ : IsCptGen ξ) (p : Cpt ξ) (s : X.presheaf.stalk p.1) :
    IsUnit s ↔ unitAt ξ p (genMap ξ p s) := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨(u.isUnit.map (genMap ξ p)).ne_zero, ⟨_, rfl⟩, ⟨((u⁻¹ : (X.presheaf.stalk p.1)ˣ) : X.presheaf.stalk p.1),
      map_units_inv (genMap ξ p) u⟩⟩
  · rintro ⟨h0, -, t, ht⟩
    refine isUnit_iff_exists_inv.2 ⟨t, hξ.inj p ?_⟩
    rw [map_mul, ht, mul_inv_cancel₀ h0, map_one]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => (h.map (Scheme.stalkClosedPointTo z).hom).ne_zero, fun h => (Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit s (isUnit_iff_ne_zero.mpr h)⟩`.
-/
theorem isUnit_stalk_point {z : Spec (CommRingCat.of ℂ) ⟶ X} (s : X.presheaf.stalk (centre z)) :
    IsUnit s ↔ (Scheme.stalkClosedPointTo z).hom s ≠ 0 :=
  ⟨fun h => (h.map (Scheme.stalkClosedPointTo z).hom).ne_zero, fun h =>
    (Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit s (isUnit_iff_ne_zero.mpr h)⟩

/- English proof (translation)
Take `⟨U, hU, hmem⟩` from `T.affine c hc`. Establish `hpU : p.1 ∈ U` using `(hmem _).2 ⟨p.2, hp⟩`. Establish `hzU : centre z ∈ U`. Use `(hmem _).2 ⟨hz, hc, fun j => ?_⟩` and prove the remaining obligations. Take `⟨h, s, e, -⟩` from `hval ⟨x j / x c, Algebra.subset_adjoin ⟨j, rfl⟩⟩`.

Conclude with `⟨s, e⟩`. Establish `hg : genPt ξ ∈ U` using `p.2.mem_open U.isOpen hpU`. Set `q : Cpt ξ` to `⟨centre z, hz⟩`. Establish `key : ∀ f : Γ(X, U), p.1 ∈ X.basicOpen f ↔ centre z ∈ X.basicOpen f`. Introduce `f`.

Establish `e1` using `SheetDecomposition.CovSch.genMap_germ' p U hpU hg f`. Establish `e2` using `SheetDecomposition.CovSch.genMap_germ' q U hzU hg f`. Establish `ha : SheetDecomposition.CovSch.val ξ U hg f ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c)` using `(T.ring c hc _).2 fun r hr => ⟨_, SheetDecomposition.CovSch.genMap_germ' r U ((hmem _).2 ⟨r.2, hr⟩) hg f⟩`. Take `⟨h, s, e3, e4⟩` from `hval ⟨_, ha⟩`. Establish `hs : s = X.presheaf.germ U (centre z) hzU f` using `T.gen.inj q (e3.trans e2.symm)`.

Rewrite using `[Scheme.mem_basicOpen _ f _ hpU, Scheme.mem_basicOpen _ f _ hzU, isUnit_stalk_iff T.gen p, e1, ← hs, isUnit_stalk_point, e4, ne_eq, hψ, not_not]`. Establish `hP : ∀ (t : U) (f : Γ(X, U)), f ∉ (hU.primeIdealOf t).asIdeal ↔ t.1 ∈ X.basicOpen f`. Introduce `t f`. Establish `h1 : hU.fromSpec (hU.primeIdealOf t) = t.1` using `hU.fromSpec_primeIdealOf t`. Establish `h2 : hU.primeIdealOf t ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f ↔ t.1 ∈ X.basicOpen f`.

Rewrite using `[← h1]`. Both sides reduce to the same expression. Rewrite `h2` using `[hU.fromSpec_preimage_basicOpen f]`. Conclude with `h2`. Establish `hEq : hU.primeIdealOf ⟨p.1, hpU⟩ = hU.primeIdealOf ⟨centre z, hzU⟩`.

Use `PrimeSpectrum.ext (Ideal.ext fun f => ?_)` and prove the remaining obligations. Establish `h1` using `hP ⟨p.1, hpU⟩ f`. Establish `h2` using `hP ⟨centre z, hzU⟩ f`. Conclude with `not_iff_not.1 (h1.trans ((key f).trans h2.symm))`. Establish `h1 : hU.fromSpec (hU.primeIdealOf ⟨p.1, hpU⟩) = p.1` using `hU.fromSpec_primeIdealOf ⟨p.1, hpU⟩`.

Establish `h2 : hU.fromSpec (hU.primeIdealOf ⟨centre z, hzU⟩) = centre z` using `hU.fromSpec_primeIdealOf ⟨centre z, hzU⟩`. Rewrite using `[← h2, ← hEq, h1]`.
-/
theorem centre_eq_of_ker {κ : Type} {x : κ → Ω} (T : CoordTie ℤ ξ x) (c : κ) (hc : x c ≠ 0) (p : Cpt ξ)
    (hp : InChart ξ x c p) (ψ : Algebra.adjoin ℤ (Set.range fun j => x j / x c) →+* ℂ)
    (hψ : ∀ a, ψ a = 0 ↔ ¬ unitAt ξ p (a : Ω)) {z : Spec (CommRingCat.of ℂ) ⟶ X} (hz : genPt ξ ⤳ centre z)
    (hval : ∀ a : Algebra.adjoin ℤ (Set.range fun j => x j / x c), ValAt ξ z (a : Ω) (ψ a)) : centre z = p.1 := by
  obtain ⟨U, hU, hmem⟩ := T.affine c hc
  have hpU : p.1 ∈ U := (hmem _).2 ⟨p.2, hp⟩
  have hzU : centre z ∈ U := by
    refine (hmem _).2 ⟨hz, hc, fun j => ?_⟩
    obtain ⟨h, s, e, -⟩ := hval ⟨x j / x c, Algebra.subset_adjoin ⟨j, rfl⟩⟩
    exact ⟨s, e⟩
  have hg : genPt ξ ∈ U := p.2.mem_open U.isOpen hpU
  let q : Cpt ξ := ⟨centre z, hz⟩
  have key : ∀ f : Γ(X, U), p.1 ∈ X.basicOpen f ↔ centre z ∈ X.basicOpen f := by
    intro f
    have e1 := SheetDecomposition.CovSch.genMap_germ' p U hpU hg f
    have e2 := SheetDecomposition.CovSch.genMap_germ' q U hzU hg f
    have ha : SheetDecomposition.CovSch.val ξ U hg f ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) :=
      (T.ring c hc _).2 fun r hr => ⟨_, SheetDecomposition.CovSch.genMap_germ' r U ((hmem _).2 ⟨r.2, hr⟩) hg f⟩
    obtain ⟨h, s, e3, e4⟩ := hval ⟨_, ha⟩
    have hs : s = X.presheaf.germ U (centre z) hzU f := T.gen.inj q (e3.trans e2.symm)
    rw [Scheme.mem_basicOpen _ f _ hpU, Scheme.mem_basicOpen _ f _ hzU, isUnit_stalk_iff T.gen p, e1, ← hs,
      isUnit_stalk_point, e4, ne_eq, hψ, not_not]
  have hP : ∀ (t : U) (f : Γ(X, U)), f ∉ (hU.primeIdealOf t).asIdeal ↔ t.1 ∈ X.basicOpen f := by
    intro t f
    have h1 : hU.fromSpec (hU.primeIdealOf t) = t.1 := hU.fromSpec_primeIdealOf t
    have h2 : hU.primeIdealOf t ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f ↔ t.1 ∈ X.basicOpen f := by
      rw [← h1]
      rfl
    rw [hU.fromSpec_preimage_basicOpen f] at h2
    exact h2
  have hEq : hU.primeIdealOf ⟨p.1, hpU⟩ = hU.primeIdealOf ⟨centre z, hzU⟩ := by
    refine PrimeSpectrum.ext (Ideal.ext fun f => ?_)
    have h1 := hP ⟨p.1, hpU⟩ f
    have h2 := hP ⟨centre z, hzU⟩ f
    exact not_iff_not.1 (h1.trans ((key f).trans h2.symm))
  have h1 : hU.fromSpec (hU.primeIdealOf ⟨p.1, hpU⟩) = p.1 := hU.fromSpec_primeIdealOf ⟨p.1, hpU⟩
  have h2 : hU.fromSpec (hU.primeIdealOf ⟨centre z, hzU⟩) = centre z := hU.fromSpec_primeIdealOf ⟨centre z, hzU⟩
  rw [← h2, ← hEq, h1]

/- English proof (translation)
Take `⟨x, hx⟩ : ∃ x : ((k : K) → J k) → Ω, x = fun c' => ∏ k, y ⟨k, c' k⟩` from `⟨_, rfl⟩`. Rewrite `T`, `hp` using `[← hx]`. Establish `hc : x cc ≠ 0` using `hp.1`. Establish `hy : ∀ k, y ⟨k, cc k⟩ ≠ 0` using `fun k => by`. Rewrite `hc` using `[hx]`.

Conclude with `(Finset.prod_ne_zero_iff.1 hc) k (Finset.mem_univ k)`. Establish `hreg : ∀ a : Algebra.adjoin ℤ (Set.range fun j => x j / x cc), (a : Ω) ∈ regAt ξ p` using `fun a => (T.ring cc hc a).1 a.2 p hp`. Set `inc : Algebra.adjoin ℤ (Set.range fun j => x j / x cc) →+* regAt ξ p` to `{ toFun := fun a => ⟨a, hreg a⟩ map_one' := rfl map_mul' := fun _ _ => rfl map_zero' := rfl map_add' := fun _ _ => rfl }`. Use `haveI : IsLocalRing (regAt ξ p) := GlobalTheory.CompanionTheory.Ar.Flat.CPoint.isLocalRing_regAt X Ω ξ T.gen p`. Set `P : Ideal (Algebra.adjoin ℤ (Set.range fun j => x j / x cc))` to `(IsLocalRing.maximalIdeal (regAt ξ p)).comap inc`.

Use `haveI : P.IsPrime := Ideal.comap_isPrime _ _`. Establish `hPmem : ∀ a, a ∈ P ↔ ¬ unitAt ξ p (a : Ω)`. Introduce `a`. Rewrite using `[Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_iff_not]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Take `⟨b, hb⟩` from `isUnit_iff_exists_inv.1 h`. Establish `hb' : (a : Ω) * (b : Ω) = 1` using `congrArg Subtype.val hb`. Establish `h0 : (a : Ω) ≠ 0` using `left_ne_zero_of_mul_eq_one hb'`. Conclude with `⟨h0, hreg a, by rw [inv_eq_of_mul_eq_one_right hb']; exact b.2⟩`.

Introduce and unpack `⟨h0, -, h2⟩`. Conclude with `isUnit_iff_exists_inv.2 ⟨⟨_, h2⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩`. Establish `hcount : Countable (Algebra.adjoin ℤ (Set.range fun j => x j / x cc))`. Establish `hcm : Countable (MvPolynomial ((k : K) → J k) ℤ)`. Rewrite using `[← Cardinal.mk_le_aleph0_iff]`.

Use `MvPolynomial.cardinalMk_le_max.trans ?_` and prove the remaining obligations. Use `first`. Consider the case `exact max_le (max_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl`. Consider the case `exact max_le (max_le (Cardinal.lift_le_aleph0.2 Cardinal.mk_le_aleph0) (Cardinal.lift_le_aleph0.2 Cardinal.mk_le_aleph0)) le_rfl`. Establish `hs : (((Algebra.adjoin ℤ (Set.range fun j => x j / x cc) : Subalgebra ℤ Ω)) : Set Ω).Countable`.

Rewrite using `[Algebra.adjoin_range_eq_range_aeval, AlgHom.coe_range]`. Conclude with `Set.countable_range _`. Conclude with `hs.to_subtype`. Establish `hP : ∀ r : ℕ, r.Prime → (r : Algebra.adjoin ℤ (Set.range fun j => x j / x cc)) ∉ P`. Introduce `r hr h`.

Use `(hPmem _).1 h ?_` and prove the remaining obligations. Use `hchar r hr` as an intermediate fact. Simplify using `using this`. Take `⟨ψ, hψ⟩` from `exists_hom_ker P hP`. Take `⟨z, hz, hval⟩` from `SheetDecomposition.ChartForm.exists_point_hom T cc hc ψ`.

Establish `htA : ∀ s : Σ k, J k, y s / y ⟨s.1, cc s.1⟩ ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x cc)`. Introduce and unpack `⟨k, i⟩`. Establish `h1 : y ⟨k, i⟩ / y ⟨k, cc k⟩ = x (Function.update cc k i) / x cc`. Rewrite using `[hx]`. Conclude with `(GlobalTheory.CompanionTheory.Ar.TiePoints.ratio_update y cc hy k i).symm`.

Rewrite using `[h1]`. Conclude with `Algebra.subset_adjoin ⟨_, rfl⟩`. Set `t' : (Σ k, J k) → Algebra.adjoin ℤ (Set.range fun j => x j / x cc)` to `fun s => ⟨_, htA s⟩`. Use `⟨z, fun s => ψ (t' s), centre_eq_of_ker T cc hc p hp ψ (fun a => (hψ a).trans (hPmem a)) hz hval, SheetDecomposition.CovSch.coordsAt_of_val cc hy (fun s => hval (t' s)) (fun k => ?_), fun g hg h0 => ?_⟩` and prove the remaining obligations. Establish `: t' ⟨k, cc k⟩ = 1` using `Subtype.ext (div_self (hy k))`.

Rewrite using `[this, map_one]`. Establish `e1 : aeval (fun s => ψ (t' s)) g = ψ (aeval t' g)` using `(GroundTheory.Heights₂.Heights.HilbertSamuel.FibreNormDehomRoots.ringHom_aeval ψ t' g).symm`. Establish `e2 : ((aeval t' g : Algebra.adjoin ℤ (Set.range fun j => x j / x cc)) : Ω) = aeval (fun s => y s / y ⟨s.1, cc s.1⟩) g` using `GroundTheory.Heights₂.Heights.HilbertSamuel.FibreNormDehomRoots.ringHom_aeval (Algebra.adjoin ℤ (Set.range fun j => x j / x cc)).val.toRingHom t' g`. Rewrite `h0` using `[e1]`. Use `(hψ _).1 h0 |> (hPmem _).1 <| ?_` and prove the remaining obligations.

Rewrite using `[e2]`. Conclude with `hg`.
-/
theorem exists_point_at {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
    (T : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) (cc : ∀ k, J k) (p : Cpt ξ)
    (hp : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) cc p)
    (hchar : ∀ r : ℕ, r.Prime → unitAt ξ p (r : Ω)) :
    ∃ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), centre z = p.1 ∧ CoordsAt ξ y z w ∧
      ∀ g : MRing J, unitAt ξ p (aeval (fun s => y s / y ⟨s.1, cc s.1⟩) g) → aeval w g ≠ 0 := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : ((k : K) → J k) → Ω, x = fun c' => ∏ k, y ⟨k, c' k⟩ := ⟨_, rfl⟩
  rw [← hx] at T hp
  have hc : x cc ≠ 0 := hp.1
  have hy : ∀ k, y ⟨k, cc k⟩ ≠ 0 := fun k => by
    rw [hx] at hc
    exact (Finset.prod_ne_zero_iff.1 hc) k (Finset.mem_univ k)
  have hreg : ∀ a : Algebra.adjoin ℤ (Set.range fun j => x j / x cc), (a : Ω) ∈ regAt ξ p :=
    fun a => (T.ring cc hc a).1 a.2 p hp
  let inc : Algebra.adjoin ℤ (Set.range fun j => x j / x cc) →+* regAt ξ p :=
    { toFun := fun a => ⟨a, hreg a⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  haveI : IsLocalRing (regAt ξ p) := GlobalTheory.CompanionTheory.Ar.Flat.CPoint.isLocalRing_regAt X Ω ξ T.gen p
  let P : Ideal (Algebra.adjoin ℤ (Set.range fun j => x j / x cc)) := (IsLocalRing.maximalIdeal (regAt ξ p)).comap inc
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  have hPmem : ∀ a, a ∈ P ↔ ¬ unitAt ξ p (a : Ω) := by
    intro a
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_iff_not]
    constructor
    · intro h
      obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 h
      have hb' : (a : Ω) * (b : Ω) = 1 := congrArg Subtype.val hb
      have h0 : (a : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one hb'
      exact ⟨h0, hreg a, by rw [inv_eq_of_mul_eq_one_right hb']; exact b.2⟩
    · rintro ⟨h0, -, h2⟩
      exact isUnit_iff_exists_inv.2 ⟨⟨_, h2⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
  have hcount : Countable (Algebra.adjoin ℤ (Set.range fun j => x j / x cc)) := by
    have hcm : Countable (MvPolynomial ((k : K) → J k) ℤ) := by
      rw [← Cardinal.mk_le_aleph0_iff]
      refine MvPolynomial.cardinalMk_le_max.trans ?_
      first
        | exact max_le (max_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl
        | exact max_le (max_le (Cardinal.lift_le_aleph0.2 Cardinal.mk_le_aleph0) (Cardinal.lift_le_aleph0.2 Cardinal.mk_le_aleph0)) le_rfl
    have hs : (((Algebra.adjoin ℤ (Set.range fun j => x j / x cc) : Subalgebra ℤ Ω)) : Set Ω).Countable := by
      rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.coe_range]
      exact Set.countable_range _
    exact hs.to_subtype
  have hP : ∀ r : ℕ, r.Prime → (r : Algebra.adjoin ℤ (Set.range fun j => x j / x cc)) ∉ P := by
    intro r hr h
    refine (hPmem _).1 h ?_
    have := hchar r hr
    simpa using this
  obtain ⟨ψ, hψ⟩ := exists_hom_ker P hP
  obtain ⟨z, hz, hval⟩ := SheetDecomposition.ChartForm.exists_point_hom T cc hc ψ
  have htA : ∀ s : Σ k, J k, y s / y ⟨s.1, cc s.1⟩ ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x cc) := by
    rintro ⟨k, i⟩
    have h1 : y ⟨k, i⟩ / y ⟨k, cc k⟩ = x (Function.update cc k i) / x cc := by
      rw [hx]
      exact (GlobalTheory.CompanionTheory.Ar.TiePoints.ratio_update y cc hy k i).symm
    rw [h1]
    exact Algebra.subset_adjoin ⟨_, rfl⟩
  let t' : (Σ k, J k) → Algebra.adjoin ℤ (Set.range fun j => x j / x cc) := fun s => ⟨_, htA s⟩
  refine ⟨z, fun s => ψ (t' s), centre_eq_of_ker T cc hc p hp ψ (fun a => (hψ a).trans (hPmem a)) hz hval,
    SheetDecomposition.CovSch.coordsAt_of_val cc hy (fun s => hval (t' s)) (fun k => ?_), fun g hg h0 => ?_⟩
  · have : t' ⟨k, cc k⟩ = 1 := Subtype.ext (div_self (hy k))
    rw [this, map_one]
  · have e1 : aeval (fun s => ψ (t' s)) g = ψ (aeval t' g) :=
      (GroundTheory.Heights₂.Heights.HilbertSamuel.FibreNormDehomRoots.ringHom_aeval ψ t' g).symm
    have e2 : ((aeval t' g : Algebra.adjoin ℤ (Set.range fun j => x j / x cc)) : Ω) =
        aeval (fun s => y s / y ⟨s.1, cc s.1⟩) g :=
      GroundTheory.Heights₂.Heights.HilbertSamuel.FibreNormDehomRoots.ringHom_aeval (Algebra.adjoin ℤ (Set.range fun j => x j / x cc)).val.toRingHom t' g
    rw [e1] at h0
    refine (hψ _).1 h0 |> (hPmem _).1 <| ?_
    rw [e2]
    exact hg

end Points

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β₀ : O →+* c.F} {Y : Model Xo c β₀}

/- English proof (translation)
Take `⟨c, hc⟩` from `G.𝔐.tie.cover ⟨genPt G.𝔐.ξ, specializes_rfl⟩`. Establish `hy : ∀ k, G.y ⟨k, c k⟩ ≠ 0` using `fun k => (Finset.prod_ne_zero_iff.1 hc.1) k (Finset.mem_univ k)`. Assume the negation of the conclusion as `hno`. Establish `hz : ∀ g ∈ G.bd, aeval (fun p => G.y p / G.y ⟨p.1, c p.1⟩) g = 0`. Introduce `g hg`.

Assume the negation of the conclusion as `h`. Conclude with `hno ⟨c, g, hg, hy, h⟩`. Take `⟨m, f, a, -, -, hsum, hS⟩` from `G.snc c hy`. Choose the witnesses or unpack the hypotheses as in `⟨l, hl⟩ : ∃ l, f l ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Simplify using `[h] at hsum`. Take `⟨-, z, n, -, hli, -, hq⟩` from `hS l hl _ rfl`. Take `⟨i, -, hi⟩` from `(hq ⊥ Ideal.isPrime_bot).1 fun g hg s hs => Ideal.mem_bot.2 (Subtype.ext (hs.trans (hz g hg)))`. Establish `h1` using `hli.ne_zero i`.

Rewrite `h1` using `[Ideal.mem_bot.1 hi, map_zero]`. Conclude with `h1 rfl`.
-/
theorem exists_chart_form (G : RefGeo Y) : ∃ (c : ∀ k, G.J k) (g : MRing G.J), g ∈ G.bd ∧ (∀ k, G.y ⟨k, c k⟩ ≠ 0) ∧
    aeval (fun p => G.y p / G.y ⟨p.1, c p.1⟩) g ≠ 0 := by
  obtain ⟨c, hc⟩ := G.𝔐.tie.cover ⟨genPt G.𝔐.ξ, specializes_rfl⟩
  have hy : ∀ k, G.y ⟨k, c k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.1 hc.1) k (Finset.mem_univ k)
  by_contra hno
  have hz : ∀ g ∈ G.bd, aeval (fun p => G.y p / G.y ⟨p.1, c p.1⟩) g = 0 := by
    intro g hg
    by_contra h
    exact hno ⟨c, g, hg, hy, h⟩
  obtain ⟨m, f, a, -, -, hsum, hS⟩ := G.snc c hy
  obtain ⟨l, hl⟩ : ∃ l, f l ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h] at hsum
  obtain ⟨-, z, n, -, hli, -, hq⟩ := hS l hl _ rfl
  obtain ⟨i, -, hi⟩ := (hq ⊥ Ideal.isPrime_bot).1 fun g hg s hs =>
    Ideal.mem_bot.2 (Subtype.ext (hs.trans (hz g hg)))
  have h1 := hli.ne_zero i
  rw [Ideal.mem_bot.1 hi, map_zero] at h1
  exact h1 rfl

end Main

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c O _ β₀ Y G`. Take `⟨c₀, g, hg, hy, hne⟩` from `exists_chart_form G`. Take `⟨d, hd⟩` from `exists_aeval_bcomp_ne _ g hne`. Establish `hhom` using `bcomp_homog g d`. Establish `hyne : aeval G.y (bcomp g d) ≠ 0`.

Introduce `h0`. Rewrite `hd` using `[← dehom_eq G.y hhom c₀, h0, zero_mul]`. Conclude with `hd rfl`. Use `⟨bcomp g d, d, hhom, fun hm => hyne ?_, hyne, mem_chartLat hhom, fun p hchar hab cc hp hu => ?_⟩` and prove the remaining obligations. Establish `h1` using `GroundTheory.Heights₂.Heights.HilbertSamuel.FibreNormDehomRoots.aeval_eq_zero_of_mem hm (fun _ => 1)`.

Simplify using `using h1`. Rewrite `hu` using `[dehom_eq G.y hhom cc]`. Take `⟨z, w, hcen, hco, hval⟩` from `exists_point_at G.𝔐.tie cc p hp (fun r hr => not_not.1 (hchar r hr))`. Use `hval _ hu (aeval_bcomp_eq_zero w g (fun t ht => ?_) d)` and prove the remaining obligations. Establish `hnot : ¬ G.𝔐.Interior z` using `fun hi => hab (hcen ▸ hi)`.

Establish `h1` using `(G.bd_iff z _ (coordsAt_scale hco ht)).2 hnot`. Establish `h2` using `h1.2 g hg`. Rewrite `h2` using `[MvPolynomial.eval_map]`. Then use the resulting hypothesis.
-/
theorem bd_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β₀ : O →+* c.F) (Y : Model Xo c β₀) (G : RefGeo Y), ∃ (β : MRing G.J) (dβ : G.K → ℕ), IsMultiHomog β dβ ∧ β ∉ mCoordIdeal G.y ∧ MvPolynomial.aeval G.y β ≠ 0 ∧ MvPolynomial.aeval G.y β ∈ chartLat G.y (fun κ => (dβ κ : ℤ)) 1 ∧ ∀ p : Cpt G.𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre G.𝔐.ξ r p) → p.1 ∉ abLocus G.𝔐.t.G → ∀ cc : ∀ k, G.J k, InChart G.𝔐.ξ (fun c' : ∀ k, G.J k => ∏ k, G.y ⟨k, c' k⟩) cc p → ¬ unitAt G.𝔐.ξ p (MvPolynomial.aeval G.y β * ∏ k, G.y ⟨k, cc k⟩ ^ (-((1 : ℕ) * (dβ k : ℤ)))) := by
  intro E _ _ _ H D l Xo c O _ β₀ Y G
  obtain ⟨c₀, g, hg, hy, hne⟩ := exists_chart_form G
  obtain ⟨d, hd⟩ := exists_aeval_bcomp_ne _ g hne
  have hhom := bcomp_homog g d
  have hyne : aeval G.y (bcomp g d) ≠ 0 := by
    intro h0
    rw [← dehom_eq G.y hhom c₀, h0, zero_mul] at hd
    exact hd rfl
  refine ⟨bcomp g d, d, hhom, fun hm => hyne ?_, hyne, mem_chartLat hhom, fun p hchar hab cc hp hu => ?_⟩
  · have h1 := GroundTheory.Heights₂.Heights.HilbertSamuel.FibreNormDehomRoots.aeval_eq_zero_of_mem hm (fun _ => 1)
    simpa using h1
  · rw [dehom_eq G.y hhom cc] at hu
    obtain ⟨z, w, hcen, hco, hval⟩ := exists_point_at G.𝔐.tie cc p hp (fun r hr => not_not.1 (hchar r hr))
    refine hval _ hu (aeval_bcomp_eq_zero w g (fun t ht => ?_) d)
    have hnot : ¬ G.𝔐.Interior z := fun hi => hab (hcen ▸ hi)
    have h1 := (G.bd_iff z _ (coordsAt_scale hco ht)).2 hnot
    have h2 := h1.2 g hg
    rwa [MvPolynomial.eval_map] at h2

end GlobalTheory.CompanionTheory.Ar.ExRefEff.BdForm
