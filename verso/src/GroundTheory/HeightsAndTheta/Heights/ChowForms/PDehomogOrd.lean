import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsDehomogOrd
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartLocalOrder
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartLocDomain
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace DehomogOrd

/- English proof (translation)
Establish `H : P.primeCompl.map e.toMonoidHom = P'.primeCompl`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl⟩`. Express the relevant statement in the definitionally equal form `e z ∉ P'`.

Rewrite using `[h]`. Simplify using `using hz`. Introduce `hy`. Use `⟨e.symm y, ?_, by simp⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `e.symm y ∉ P`.

Rewrite using `[← h]`. Conclude with `hy`. Set `f` to `IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime P) (Localization.AtPrime P') e H`. Establish `hf : f (algebraMap S _ x) = algebraMap T _ (e x)` using `IsLocalization.ringEquivOfRingEquiv_eq (S := Localization.AtPrime P) (Q := Localization.AtPrime P') H x`. Rewrite using `[← hf]`.

Conclude with `ord_ringEquiv f _`.
-/
theorem ord_atPrime_ringEquiv {S T : Type*} [CommRing S] [CommRing T] (e : S ≃+* T) (P : Ideal S)
    (P' : Ideal T) [P.IsPrime] [P'.IsPrime] (h : ∀ y, y ∈ P' ↔ e.symm y ∈ P) (x : S) :
    Ring.ord (Localization.AtPrime P') (algebraMap T _ (e x)) =
      Ring.ord (Localization.AtPrime P) (algebraMap S _ x) := by
  have H : P.primeCompl.map e.toMonoidHom = P'.primeCompl := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      change e z ∉ P'
      rw [h]
      simpa using hz
    · intro hy
      refine ⟨e.symm y, ?_, by simp⟩
      change e.symm y ∉ P
      rw [← h]
      exact hy
  let f := IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime P) (Localization.AtPrime P') e H
  have hf : f (algebraMap S _ x) = algebraMap T _ (e x) :=
    IsLocalization.ringEquivOfRingEquiv_eq (S := Localization.AtPrime P) (Q := Localization.AtPrime P') H x
  rw [← hf]
  exact ord_ringEquiv f _

/- English proof (translation)
Rewrite using `[← Ideal.Quotient.isDomain_iff_prime]`. Conclude with `MulEquiv.isDomain (MvPolynomial σ (R ⧸ p)) (quotientEquivQuotientMvPolynomial (σ := σ) p).toRingEquiv.toMulEquiv.symm`.
-/
theorem isPrime_map_C {R : Type*} [CommRing R] (σ : Type*) (p : Ideal R) [p.IsPrime] :
    (Ideal.map (C : R →+* MvPolynomial σ R) p).IsPrime := by
  rw [← Ideal.Quotient.isDomain_iff_prime]
  exact MulEquiv.isDomain (MvPolynomial σ (R ⧸ p))
    (quotientEquivQuotientMvPolynomial (σ := σ) p).toRingEquiv.toMulEquiv.symm

/- English proof (translation)
Rewrite using `[Set.disjoint_left]`. Introduce and unpack `_ ⟨k, rfl⟩ hk`. Conclude with `hx (hP.mem_of_pow_mem k hk)`.
-/
theorem disjoint_powers {R : Type*} [CommRing R] (P : Ideal R) [hP : P.IsPrime] {x : R} (hx : x ∉ P) :
    Disjoint ((Submonoid.powers x : Submonoid R) : Set R) P := by
  rw [Set.disjoint_left]
  rintro _ ⟨k, rfl⟩ hk
  exact hx (hP.mem_of_pow_mem k hk)

/- English proof (translation)
Establish `h : IsUnit (algebraMap A (Localization.AtPrime P) u)` using `(IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P u).mpr hu`. Rewrite using `[map_mul]`. Conclude with `Ring.ord_mul_of_isUnit_left h _`.
-/
theorem ord_atPrime_mul_of_notMem {A : Type*} [CommRing A] (P : Ideal A) [P.IsPrime] {u : A} (hu : u ∉ P)
    (x : A) :
    Ring.ord (Localization.AtPrime P) (algebraMap A _ (u * x)) =
      Ring.ord (Localization.AtPrime P) (algebraMap A _ x) := by
  have h : IsUnit (algebraMap A (Localization.AtPrime P) u) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P u).mpr hu
  rw [map_mul]
  exact Ring.ord_mul_of_isUnit_left h _

/- English proof (translation)
Establish `hX : (X () : MvPolynomial Unit Q) ∉ Ideal.map (C : Q →+* MvPolynomial Unit Q) p`. Introduce `h`. Rewrite `h` using `[MvPolynomial.mem_map_C_iff]`. Establish `h1 : (1 : Q) ∈ p` using `by simpa using h (Finsupp.single () 1)`. Conclude with `Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).mpr h1)`.

Rewrite using `[ord_atPrime_mul_of_notMem _ (fun h => hX (Ideal.IsPrime.mem_of_pow_mem ‹_› d h))]`. Conclude with `h₁ Q Unit p q`.
-/
theorem ord_X_pow_mul_C (h₁ : OrdPolynomialLocalization.Statement) {Q : Type} [CommRing Q] (p : Ideal Q)
    [p.IsPrime] [(Ideal.map (C : Q →+* MvPolynomial Unit Q) p).IsPrime] (q : Q) (d : ℕ) :
    Ring.ord (Localization.AtPrime (Ideal.map (C : Q →+* MvPolynomial Unit Q) p))
        (algebraMap (MvPolynomial Unit Q) _ (X () ^ d * C q)) =
      Ring.ord (Localization.AtPrime p) (algebraMap Q _ q) := by
  have hX : (X () : MvPolynomial Unit Q) ∉ Ideal.map (C : Q →+* MvPolynomial Unit Q) p := by
    intro h
    rw [MvPolynomial.mem_map_C_iff] at h
    have h1 : (1 : Q) ∈ p := by simpa using h (Finsupp.single () 1)
    exact Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).mpr h1)
  rw [ord_atPrime_mul_of_notMem _ (fun h => hX (Ideal.IsPrime.mem_of_pow_mem ‹_› d h))]
  exact h₁ Q Unit p q

variable {F : Type} [Field F] {n : ℕ} (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F)

/- English proof (translation)
Establish `key : aeval (fun m => c * π (X m)) g = c ^ d * aeval (fun m => π (X m)) g` using `by conv_lhs => rw [g.as_sum] conv_rhs => rw [g.as_sum]`. Rewrite using `[map_sum, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun s hs => ?_` and prove the remaining obligations. Establish `hd` using `hg (mem_support_iff.mp hs)`. Simplify using `only [aeval_monomial, mul_pow]`.

Rewrite using `[Finsupp.prod_mul, Finsupp.prod_pow, Finsupp.prod_pow, Finset.prod_pow_eq_pow_sum, ← hd, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]`. Simplify using `only [smul_eq_mul, Pi.one_apply, mul_one]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`. Use `congr 1`.

Rewrite using `[← comp_aeval_apply]`. Simplify using the standard rewrite rules.
-/
theorem aeval_smul_hom {B : Type*} [CommSemiring B] [Algebra F B] (π : MvPolynomial (Fin n) F →ₐ[F] B) (c : B)
    {g : MvPolynomial (Fin n) F} {d : ℕ} (hg : g.IsHomogeneous d) :
    aeval (fun m => c * π (X m)) g = c ^ d * π g := by
  have key : aeval (fun m => c * π (X m)) g = c ^ d * aeval (fun m => π (X m)) g := by
    conv_lhs => rw [g.as_sum]
    conv_rhs => rw [g.as_sum]
    rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hd := hg (mem_support_iff.mp hs)
    simp only [aeval_monomial, mul_pow]
    rw [Finsupp.prod_mul, Finsupp.prod_pow, Finsupp.prod_pow, Finset.prod_pow_eq_pow_sum, ← hd,
      Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp only [smul_eq_mul, Pi.one_apply, mul_one]
    ring
  rw [key]
  congr 1
  rw [← comp_aeval_apply]
  simp

/- English proof (translation)
Rewrite using `[← sum_homogeneousComponent g, map_sum]`. Conclude with `Finset.sum_eq_zero fun k _ => hf g hg k`.
-/
theorem map_eq_zero_of_components {B G : Type*} [CommRing B] [FunLike G (MvPolynomial (Fin n) F) B]
    [RingHomClass G (MvPolynomial (Fin n) F) B] (f : G)
    {K : Ideal (MvPolynomial (Fin n) F)}
    (hf : ∀ g ∈ K, ∀ k, f (homogeneousComponent k g) = 0) {g : MvPolynomial (Fin n) F} (hg : g ∈ K) :
    f g = 0 := by
  rw [← sum_homogeneousComponent g, map_sum]
  exact Finset.sum_eq_zero fun k _ => hf g hg k

abbrev chartIdealOf : Ideal (MvPolynomial (Fin n) F) := I ⊔ Ideal.span {linForm t - 1}

abbrev ChartRing := MvPolynomial (Fin n) F ⧸ chartIdealOf I t

abbrev linClass : MvPolynomial (Fin n) F ⧸ I := Ideal.Quotient.mk I (linForm t)

/- English proof (translation)
Rewrite using `[← sub_eq_zero, ← map_one (Ideal.Quotient.mk (chartIdealOf I t)), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)`.
-/
theorem mk_linForm_chart : Ideal.Quotient.mk (chartIdealOf I t) (linForm t) = 1 := by
  rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk (chartIdealOf I t)), ← map_sub,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)

def toPoly : MvPolynomial (Fin n) F →ₐ[F] MvPolynomial Unit (ChartRing I t) :=
  aeval fun m => X () * (IsScalarTower.toAlgHom F (ChartRing I t) (MvPolynomial Unit (ChartRing I t))).comp
    (Ideal.Quotient.mkₐ F (chartIdealOf I t)) (X m)

/- English proof (translation)
Establish `h` using `aeval_smul_hom ((IsScalarTower.toAlgHom F (ChartRing I t) (MvPolynomial Unit (ChartRing I t))).comp (Ideal.Quotient.mkₐ F (chartIdealOf I t))) (X ()) hg`. Use `h.trans ?_` and prove the remaining obligations. Simplify using `only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', Ideal.Quotient.mkₐ_eq_mk, MvPolynomial.algebraMap_eq]`.
-/
theorem toPoly_hom {g : MvPolynomial (Fin n) F} {d : ℕ} (hg : g.IsHomogeneous d) :
    toPoly I t g = X () ^ d * C (Ideal.Quotient.mk (chartIdealOf I t) g) := by
  have h := aeval_smul_hom ((IsScalarTower.toAlgHom F (ChartRing I t) (MvPolynomial Unit (ChartRing I t))).comp
    (Ideal.Quotient.mkₐ F (chartIdealOf I t))) (X ()) hg
  refine h.trans ?_
  simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', Ideal.Quotient.mkₐ_eq_mk, MvPolynomial.algebraMap_eq]

/- English proof (translation)
The claim follows from `map_eq_zero_of_components (toPoly I t) (fun g hg k => by rw [toPoly_hom I t (homogeneousComponent_isHomogeneous k g), Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (hI g hg k)), map_zero, mul_zero]) ha`.
-/
theorem toPoly_eq_zero (hI : IsHomogIdeal I) {a : MvPolynomial (Fin n) F} (ha : a ∈ I) : toPoly I t a = 0 :=
  map_eq_zero_of_components (toPoly I t) (fun g hg k => by
    rw [toPoly_hom I t (homogeneousComponent_isHomogeneous k g),
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (hI g hg k)), map_zero, mul_zero]) ha

def toPolyR (hI : IsHomogIdeal I) : MvPolynomial (Fin n) F ⧸ I →+* MvPolynomial Unit (ChartRing I t) :=
  Ideal.Quotient.lift I (toPoly I t).toRingHom fun _ ha => toPoly_eq_zero I t hI ha

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toPolyR_mk (hI : IsHomogIdeal I) (a : MvPolynomial (Fin n) F) :
    toPolyR I t hI (Ideal.Quotient.mk I a) = toPoly I t a := rfl

/- English proof (translation)
Rewrite using `[toPolyR_mk, toPoly_hom I t (ChartLocDomain.linForm_isHomogeneous t), mk_linForm_chart, map_one, pow_one, mul_one]`.
-/
theorem toPolyR_linClass (hI : IsHomogIdeal I) : toPolyR I t hI (linClass I t) = X () := by
  rw [toPolyR_mk, toPoly_hom I t (ChartLocDomain.linForm_isHomogeneous t), mk_linForm_chart, map_one,
    pow_one, mul_one]

def fromChart : MvPolynomial (Fin n) F →ₐ[F] Localization.Away (linClass I t) :=
  aeval fun m => IsLocalization.Away.invSelf (linClass I t) *
    (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F ⧸ I) (Localization.Away (linClass I t))).comp
      (Ideal.Quotient.mkₐ F I) (X m)

/- English proof (translation)
Rewrite using `[fromChart, aeval_smul_hom _ _ hg]`. Simplify using `only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', Ideal.Quotient.mkₐ_eq_mk]`.
-/
theorem fromChart_hom {g : MvPolynomial (Fin n) F} {d : ℕ} (hg : g.IsHomogeneous d) :
    fromChart I t g = IsLocalization.Away.invSelf (linClass I t) ^ d *
      algebraMap _ (Localization.Away (linClass I t)) (Ideal.Quotient.mk I g) := by
  rw [fromChart, aeval_smul_hom _ _ hg]
  simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', Ideal.Quotient.mkₐ_eq_mk]

/- English proof (translation)
Establish `hle : chartIdealOf I t ≤ RingHom.ker (fromChart I t)`. Use `sup_le (fun g hg => ?_) ?_` and prove the remaining obligations. Rewrite using `[RingHom.mem_ker]`. Use `map_eq_zero_of_components (fromChart I t) (fun g hg k => ?_) hg` and prove the remaining obligations. Rewrite using `[fromChart_hom I t (homogeneousComponent_isHomogeneous k g), Ideal.Quotient.eq_zero_iff_mem.mpr (hI g hg k), map_zero, mul_zero]`.

Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]`. Express the relevant statement in the definitionally equal form `fromChart I t (linForm t - 1) = 0`. Rewrite using `[map_sub, map_one, fromChart_hom I t (ChartLocDomain.linForm_isHomogeneous t), pow_one, mul_comm, IsLocalization.Away.mul_invSelf, sub_self]`. Conclude with `hle ha`.
-/
theorem fromChart_eq_zero (hI : IsHomogIdeal I) {a : MvPolynomial (Fin n) F} (ha : a ∈ chartIdealOf I t) :
    fromChart I t a = 0 := by
  have hle : chartIdealOf I t ≤ RingHom.ker (fromChart I t) := by
    refine sup_le (fun g hg => ?_) ?_
    · rw [RingHom.mem_ker]
      refine map_eq_zero_of_components (fromChart I t) (fun g hg k => ?_) hg
      rw [fromChart_hom I t (homogeneousComponent_isHomogeneous k g),
        Ideal.Quotient.eq_zero_iff_mem.mpr (hI g hg k), map_zero, mul_zero]
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
      change fromChart I t (linForm t - 1) = 0
      rw [map_sub, map_one, fromChart_hom I t (ChartLocDomain.linForm_isHomogeneous t), pow_one, mul_comm,
        IsLocalization.Away.mul_invSelf, sub_self]
  exact hle ha

def fromChartQ (hI : IsHomogIdeal I) : ChartRing I t →+* Localization.Away (linClass I t) :=
  Ideal.Quotient.lift _ (fromChart I t).toRingHom fun _ ha => fromChart_eq_zero I t hI ha

def fromPoly (hI : IsHomogIdeal I) : MvPolynomial Unit (ChartRing I t) →+* Localization.Away (linClass I t) :=
  eval₂Hom (fromChartQ I t hI) fun _ => algebraMap _ _ (linClass I t)

/- English proof (translation)
Simplify using `only [fromPoly, fromChartQ, coe_eval₂Hom, eval₂_C, Ideal.Quotient.lift_mk]`. Both sides reduce to the same expression.
-/
theorem fromPoly_C_mk (hI : IsHomogIdeal I) (a : MvPolynomial (Fin n) F) :
    fromPoly I t hI (C (Ideal.Quotient.mk _ a)) = fromChart I t a := by
  simp only [fromPoly, fromChartQ, coe_eval₂Hom, eval₂_C, Ideal.Quotient.lift_mk]
  rfl

/- English proof (translation)
Simplify using `[fromPoly]`.
-/
theorem fromPoly_X (hI : IsHomogIdeal I) :
    fromPoly I t hI (X ()) = algebraMap _ _ (linClass I t) := by
  simp [fromPoly]

/- English proof (translation)
Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective r`. Rewrite using `[toPolyR_mk]`. Express the relevant statement in the definitionally equal form `((fromPoly I t hI).comp (toPoly I t).toRingHom) a = ((algebraMap _ (Localization.Away (linClass I t))).comp (Ideal.Quotient.mk I)) a`. Use `congr 1`. Use `MvPolynomial.ringHom_ext (fun c => ?_) (fun m => ?_)` and prove the remaining obligations.

Simplify using `only [RingHom.coe_comp, Function.comp_apply]`. Rewrite using `[AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, MvPolynomial.algebraMap_apply, show algebraMap F (ChartRing I t) c = Ideal.Quotient.mk _ (algebraMap F _ c) from rfl, fromPoly_C_mk, AlgHom.commutes]`. Both sides reduce to the same expression. Simplify using `only [RingHom.coe_comp, Function.comp_apply]`. Rewrite using `[AlgHom.toRingHom_eq_coe, RingHom.coe_coe, toPoly, aeval_X, map_mul, fromPoly_X]`.

Express the relevant statement in the definitionally equal form `_ * fromPoly I t hI (C (Ideal.Quotient.mk _ (X m))) = _`. Rewrite using `[fromPoly_C_mk, fromChart, aeval_X, ← mul_assoc, IsLocalization.Away.mul_invSelf, one_mul]`. Both sides reduce to the same expression.
-/
theorem fromPoly_toPolyR (hI : IsHomogIdeal I) (r : MvPolynomial (Fin n) F ⧸ I) :
    fromPoly I t hI (toPolyR I t hI r) = algebraMap _ _ r := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [toPolyR_mk]
  change ((fromPoly I t hI).comp (toPoly I t).toRingHom) a =
    ((algebraMap _ (Localization.Away (linClass I t))).comp (Ideal.Quotient.mk I)) a
  congr 1
  refine MvPolynomial.ringHom_ext (fun c => ?_) (fun m => ?_)
  · simp only [RingHom.coe_comp, Function.comp_apply]
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← MvPolynomial.algebraMap_eq, AlgHom.commutes,
      MvPolynomial.algebraMap_apply,
      show algebraMap F (ChartRing I t) c = Ideal.Quotient.mk _ (algebraMap F _ c) from rfl, fromPoly_C_mk,
      AlgHom.commutes]
    rfl
  · simp only [RingHom.coe_comp, Function.comp_apply]
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, toPoly, aeval_X, map_mul, fromPoly_X]
    change _ * fromPoly I t hI (C (Ideal.Quotient.mk _ (X m))) = _
    rw [fromPoly_C_mk, fromChart, aeval_X, ← mul_assoc, IsLocalization.Away.mul_invSelf, one_mul]
    rfl

def toLoc (hI : IsHomogIdeal I) :
    Localization.Away (linClass I t) →+* Localization.Away (X () : MvPolynomial Unit (ChartRing I t)) :=
  IsLocalization.Away.lift (linClass I t)
    (g := (algebraMap _ (Localization.Away (X () : MvPolynomial Unit (ChartRing I t)))).comp (toPolyR I t hI))
    (by rw [RingHom.comp_apply, toPolyR_linClass]; exact IsLocalization.Away.algebraMap_isUnit _)

/- English proof (translation)
The claim follows from `IsLocalization.Away.lift_eq _ _ r`.
-/
theorem toLoc_algebraMap (hI : IsHomogIdeal I) (r : MvPolynomial (Fin n) F ⧸ I) :
    toLoc I t hI (algebraMap _ _ r) = algebraMap _ _ (toPolyR I t hI r) :=
  IsLocalization.Away.lift_eq _ _ r

def fromLoc (hI : IsHomogIdeal I) :
    Localization.Away (X () : MvPolynomial Unit (ChartRing I t)) →+* Localization.Away (linClass I t) :=
  IsLocalization.Away.lift (X () : MvPolynomial Unit (ChartRing I t)) (g := fromPoly I t hI)
    (by rw [fromPoly_X]; exact IsLocalization.Away.algebraMap_isUnit _)

/- English proof (translation)
The claim follows from `IsLocalization.Away.lift_eq _ _ b`.
-/
theorem fromLoc_algebraMap (hI : IsHomogIdeal I) (b : MvPolynomial Unit (ChartRing I t)) :
    fromLoc I t hI (algebraMap _ _ b) = fromPoly I t hI b :=
  IsLocalization.Away.lift_eq _ _ b

/- English proof (translation)
Establish `: (fromLoc I t hI).comp (toLoc I t hI) = RingHom.id _` using `IsLocalization.ringHom_ext (Submonoid.powers (linClass I t)) (RingHom.ext fun r => by`. Simplify using `only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply]`. Rewrite using `[toLoc_algebraMap, fromLoc_algebraMap, fromPoly_toPolyR])`. Conclude with `congrArg (· x) this`.
-/
theorem fromLoc_toLoc (hI : IsHomogIdeal I) (x : Localization.Away (linClass I t)) :
    fromLoc I t hI (toLoc I t hI x) = x := by
  have : (fromLoc I t hI).comp (toLoc I t hI) = RingHom.id _ :=
    IsLocalization.ringHom_ext (Submonoid.powers (linClass I t)) (RingHom.ext fun r => by
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply]
      rw [toLoc_algebraMap, fromLoc_algebraMap, fromPoly_toPolyR])
  exact congrArg (· x) this

/- English proof (translation)
Establish `hv : toLoc I t hI (IsLocalization.Away.invSelf (linClass I t)) * algebraMap (MvPolynomial Unit (ChartRing I t)) (Localization.Away (X () : MvPolynomial Unit (ChartRing I t))) (X ()) = 1`. Establish `h2 : algebraMap (MvPolynomial Unit (ChartRing I t)) (Localization.Away (X () : MvPolynomial Unit (ChartRing I t))) (X ()) = toLoc I t hI (algebraMap _ _ (linClass I t))`. Rewrite using `[toLoc_algebraMap, toPolyR_linClass]`. Rewrite using `[h2, ← map_mul, mul_comm, IsLocalization.Away.mul_invSelf, map_one]`. Express the relevant statement in the definitionally equal form `((toLoc I t hI).comp (fromPoly I t hI)) b = (algebraMap _ _) b`.

Use `congr 1`. Use `MvPolynomial.ringHom_ext (fun q => ?_) (fun _ => ?_)` and prove the remaining obligations. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective q`. Simplify using `only [RingHom.coe_comp, Function.comp_apply]`. Rewrite using `[fromPoly_C_mk]`.

Express the relevant statement in the definitionally equal form `((toLoc I t hI).comp (fromChart I t).toRingHom) a = ((algebraMap _ (Localization.Away (X () : MvPolynomial Unit (ChartRing I t)))).comp (C.comp (Ideal.Quotient.mk _))) a`. Use `congr 1`. Use `MvPolynomial.ringHom_ext (fun c => ?_) (fun m => ?_)` and prove the remaining obligations. Simplify using `only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]`. Rewrite using `[← MvPolynomial.algebraMap_eq, AlgHom.commutes, show algebraMap F (Localization.Away (linClass I t)) c = algebraMap _ _ (Ideal.Quotient.mk I (algebraMap F _ c)) from rfl, toLoc_algebraMap, toPolyR_mk, AlgHom.commutes, MvPolynomial.algebraMap_apply]`.

Both sides reduce to the same expression. Simplify using `only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]`. Rewrite using `[fromChart, aeval_X, map_mul]`. Express the relevant statement in the definitionally equal form `_ * toLoc I t hI (algebraMap _ _ (Ideal.Quotient.mk I (X m))) = _`. Rewrite using `[toLoc_algebraMap, toPolyR_mk, toPoly, aeval_X, map_mul, ← mul_assoc, hv, one_mul]`.

Simplify using `only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', Ideal.Quotient.mkₐ_eq_mk, MvPolynomial.algebraMap_eq]`. Simplify using `only [RingHom.coe_comp, Function.comp_apply]`. Rewrite using `[fromPoly_X, toLoc_algebraMap, toPolyR_linClass]`.
-/
theorem toLoc_fromPoly (hI : IsHomogIdeal I) (b : MvPolynomial Unit (ChartRing I t)) :
    toLoc I t hI (fromPoly I t hI b) = algebraMap _ _ b := by
  have hv : toLoc I t hI (IsLocalization.Away.invSelf (linClass I t)) *
      algebraMap (MvPolynomial Unit (ChartRing I t)) (Localization.Away (X () : MvPolynomial Unit (ChartRing I t)))
        (X ()) = 1 := by
    have h2 : algebraMap (MvPolynomial Unit (ChartRing I t))
        (Localization.Away (X () : MvPolynomial Unit (ChartRing I t))) (X ()) =
        toLoc I t hI (algebraMap _ _ (linClass I t)) := by
      rw [toLoc_algebraMap, toPolyR_linClass]
    rw [h2, ← map_mul, mul_comm, IsLocalization.Away.mul_invSelf, map_one]
  change ((toLoc I t hI).comp (fromPoly I t hI)) b = (algebraMap _ _) b
  congr 1
  refine MvPolynomial.ringHom_ext (fun q => ?_) (fun _ => ?_)
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [fromPoly_C_mk]
    change ((toLoc I t hI).comp (fromChart I t).toRingHom) a =
      ((algebraMap _ (Localization.Away (X () : MvPolynomial Unit (ChartRing I t)))).comp
        (C.comp (Ideal.Quotient.mk _))) a
    congr 1
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun m => ?_)
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes,
        show algebraMap F (Localization.Away (linClass I t)) c =
          algebraMap _ _ (Ideal.Quotient.mk I (algebraMap F _ c)) from rfl,
        toLoc_algebraMap, toPolyR_mk, AlgHom.commutes, MvPolynomial.algebraMap_apply]
      rfl
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [fromChart, aeval_X, map_mul]
      change _ * toLoc I t hI (algebraMap _ _ (Ideal.Quotient.mk I (X m))) = _
      rw [toLoc_algebraMap, toPolyR_mk, toPoly, aeval_X, map_mul, ← mul_assoc, hv, one_mul]
      simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', Ideal.Quotient.mkₐ_eq_mk,
        MvPolynomial.algebraMap_eq]
  · simp only [RingHom.coe_comp, Function.comp_apply]
    rw [fromPoly_X, toLoc_algebraMap, toPolyR_linClass]

/- English proof (translation)
Establish `: (toLoc I t hI).comp (fromLoc I t hI) = RingHom.id _` using `IsLocalization.ringHom_ext (Submonoid.powers (X () : MvPolynomial Unit (ChartRing I t))) (RingHom.ext fun b => by`. Simplify using `only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply]`. Rewrite using `[fromLoc_algebraMap, toLoc_fromPoly])`. Conclude with `congrArg (· y) this`.
-/
theorem toLoc_fromLoc (hI : IsHomogIdeal I) (y : Localization.Away (X () : MvPolynomial Unit (ChartRing I t))) :
    toLoc I t hI (fromLoc I t hI y) = y := by
  have : (toLoc I t hI).comp (fromLoc I t hI) = RingHom.id _ :=
    IsLocalization.ringHom_ext (Submonoid.powers (X () : MvPolynomial Unit (ChartRing I t))) (RingHom.ext fun b => by
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply]
      rw [fromLoc_algebraMap, toLoc_fromPoly])
  exact congrArg (· y) this

def locEquiv (hI : IsHomogIdeal I) :
    Localization.Away (linClass I t) ≃+* Localization.Away (X () : MvPolynomial Unit (ChartRing I t)) :=
  RingEquiv.ofRingHom (toLoc I t hI) (fromLoc I t hI) (RingHom.ext (toLoc_fromLoc I t hI))
    (RingHom.ext (fromLoc_toLoc I t hI))

end DehomogOrd

open DehomogOrd in

/- English proof (translation)
Introduce `F _ n I W t hI hW hIW htW hP hPQ g d hg`. Use `set P := W.map (Ideal.Quotient.mk I) with hPdef`. Use `set PQ : Ideal (ChartRing I t) := W.map (Ideal.Quotient.mk (chartIdealOf I t)) with hPQdef`. Establish `hPB : (Ideal.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t)) PQ).IsPrime` using `isPrime_map_C Unit PQ`. Establish `hmemP : ∀ a, Ideal.Quotient.mk I a ∈ P ↔ a ∈ W` using `fun a => Ideal.mem_quotient_iff_mem hIW`.

Establish `hℓP : linClass I t ∉ P` using `fun h => htW ((hmemP _).mp h)`. Establish `hsPB : (X () : MvPolynomial Unit (ChartRing I t)) ∉ PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t))`. Introduce `h`. Rewrite `h` using `[MvPolynomial.mem_map_C_iff]`. Establish `h1 : (1 : ChartRing I t) ∈ PQ` using `by simpa using h (Finsupp.single () 1)`.

Conclude with `hPQ.ne_top ((Ideal.eq_top_iff_one _).mpr h1)`. Establish `hdR` using `disjoint_powers P hℓP`. Establish `hdB` using `disjoint_powers (PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t))) hsPB`. Establish `hP' : (P.map (algebraMap _ (Localization.Away (linClass I t)))).IsPrime` using `IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (linClass I t)) _ P hP hdR`. Establish `hPS : ((PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t))).map (algebraMap (MvPolynomial Unit (ChartRing I t)) (Localization.Away (X () : MvPolynomial Unit (ChartRing I t))))).IsPrime` using `IsLocalization.isPrime_of_isPrime_disjoint _ _ _ hPB hdB`.

Establish `hφP : ∀ r ∈ P, toPolyR I t hI r ∈ PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t))`. Introduce `r hr`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective r`. Establish `ha : a ∈ W` using `(hmemP a).mp hr`. Rewrite using `[toPolyR_mk, ← sum_homogeneousComponent a, map_sum]`.

Use `Ideal.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[toPoly_hom I t (homogeneousComponent_isHomogeneous k a)]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (hW a ha k)))`. Establish `hψPQ : ∀ q ∈ PQ, fromPoly I t hI (C q) ∈ P.map (algebraMap _ (Localization.Away (linClass I t)))`. Establish `hle : PQ ≤ Ideal.comap ((fromPoly I t hI).comp C) (P.map (algebraMap _ (Localization.Away (linClass I t))))`.

Rewrite using `[hPQdef, Ideal.map_le_iff_le_comap, Ideal.comap_comap]`. Introduce `w hw`. Rewrite using `[Ideal.mem_comap, RingHom.comp_apply, RingHom.comp_apply, fromPoly_C_mk, ← sum_homogeneousComponent w, map_sum]`. Use `Ideal.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[fromChart_hom I t (homogeneousComponent_isHomogeneous k w)]`.

Conclude with `Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ((hmemP _).mpr (hW w hw k)))`. Conclude with `fun q hq => hle hq`. Establish `hΨin : ∀ y ∈ (PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t))).map (algebraMap (MvPolynomial Unit (ChartRing I t)) (Localization.Away (X () : MvPolynomial Unit (ChartRing I t)))), fromLoc I t hI y ∈ P.map (algebraMap _ (Localization.Away (linClass I t)))`. Establish `hle : (PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t))).map (algebraMap (MvPolynomial Unit (ChartRing I t)) (Localization.Away (X () : MvPolynomial Unit (ChartRing I t)))) ≤ Ideal.comap (fromLoc I t hI) (P.map (algebraMap _ (Localization.Away (linClass I t))))`. Rewrite using `[Ideal.map_le_iff_le_comap, Ideal.comap_comap, Ideal.map_le_iff_le_comap, Ideal.comap_comap]`.

Introduce `q hq`. Rewrite using `[Ideal.mem_comap, RingHom.comp_apply, RingHom.comp_apply, fromLoc_algebraMap]`. Conclude with `hψPQ q hq`. Conclude with `fun y hy => hle hy`. Establish `hΦin : ∀ x ∈ P.map (algebraMap _ (Localization.Away (linClass I t))), toLoc I t hI x ∈ (PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t))).map (algebraMap (MvPolynomial Unit (ChartRing I t)) (Localization.Away (X () : MvPolynomial Unit (ChartRing I t))))`.

Establish `hle : P.map (algebraMap _ (Localization.Away (linClass I t))) ≤ Ideal.comap (toLoc I t hI) ((PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t))).map (algebraMap (MvPolynomial Unit (ChartRing I t)) (Localization.Away (X () : MvPolynomial Unit (ChartRing I t)))))`. Rewrite using `[Ideal.map_le_iff_le_comap, Ideal.comap_comap]`. Introduce `r hr`. Rewrite using `[Ideal.mem_comap, RingHom.comp_apply, toLoc_algebraMap]`. Conclude with `Ideal.mem_map_of_mem _ (hφP r hr)`.

Conclude with `fun x hx => hle hx`. Establish `hcorr : ∀ y, y ∈ (PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t))).map (algebraMap (MvPolynomial Unit (ChartRing I t)) (Localization.Away (X () : MvPolynomial Unit (ChartRing I t)))) ↔ (locEquiv I t hI).symm y ∈ P.map (algebraMap _ (Localization.Away (linClass I …`. Introduce `y`. Express the relevant statement in the definitionally equal form `_ ↔ fromLoc I t hI y ∈ _`. Use `⟨hΨin y, fun h => ?_⟩` and prove the remaining obligations.

Use `hΦin _ h` as an intermediate fact. Rewrite `this` using `[toLoc_fromLoc]`. Then use the resulting hypothesis. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[show locEquiv I t hI (algebraMap _ _ (Ideal.Quotient.mk I g)) = toLoc I t hI (algebraMap _ _ (Ideal.Quotient.mk I g)) from rfl, toLoc_algebraMap]`. Use `_ = Ring.ord (Localization.AtPrime (PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t)))) (algebraMap _ _ (toPolyR I t hI (Ideal.Quotient.mk I g))) := ord_atPrime_map_localization (Submonoid.powers _) (PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t))) …`.

Use `_ = Ring.ord (Localization.AtPrime PQ) (algebraMap _ _ (Ideal.Quotient.mk (chartIdealOf I t) g)) := by`. Rewrite using `[toPolyR_mk, toPoly_hom I t hg]`. Conclude with `ord_X_pow_mul_C h₁ PQ _ d`.
-/
theorem DehomogOrd.proof (h₁ : OrdPolynomialLocalization.Statement) : DehomogOrd.Statement := by
  intro F _ n I W t hI hW hIW htW hP hPQ g d hg
  set P := W.map (Ideal.Quotient.mk I) with hPdef
  set PQ : Ideal (ChartRing I t) := W.map (Ideal.Quotient.mk (chartIdealOf I t)) with hPQdef
  have hPB : (Ideal.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t)) PQ).IsPrime :=
    isPrime_map_C Unit PQ
  have hmemP : ∀ a, Ideal.Quotient.mk I a ∈ P ↔ a ∈ W := fun a => Ideal.mem_quotient_iff_mem hIW
  have hℓP : linClass I t ∉ P := fun h => htW ((hmemP _).mp h)
  have hsPB : (X () : MvPolynomial Unit (ChartRing I t)) ∉ PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t)) := by
    intro h
    rw [MvPolynomial.mem_map_C_iff] at h
    have h1 : (1 : ChartRing I t) ∈ PQ := by simpa using h (Finsupp.single () 1)
    exact hPQ.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have hdR := disjoint_powers P hℓP
  have hdB := disjoint_powers (PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t))) hsPB
  have hP' : (P.map (algebraMap _ (Localization.Away (linClass I t)))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (linClass I t)) _ P hP hdR
  have hPS : ((PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t))).map (algebraMap (MvPolynomial Unit (ChartRing I t))
      (Localization.Away (X () : MvPolynomial Unit (ChartRing I t))))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ _ _ hPB hdB

  have hφP : ∀ r ∈ P, toPolyR I t hI r ∈ PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t)) := by
    intro r hr
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    have ha : a ∈ W := (hmemP a).mp hr
    rw [toPolyR_mk, ← sum_homogeneousComponent a, map_sum]
    refine Ideal.sum_mem _ fun k _ => ?_
    rw [toPoly_hom I t (homogeneousComponent_isHomogeneous k a)]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (hW a ha k)))
  have hψPQ : ∀ q ∈ PQ, fromPoly I t hI (C q) ∈ P.map (algebraMap _ (Localization.Away (linClass I t))) := by
    have hle : PQ ≤ Ideal.comap ((fromPoly I t hI).comp C)
        (P.map (algebraMap _ (Localization.Away (linClass I t)))) := by
      rw [hPQdef, Ideal.map_le_iff_le_comap, Ideal.comap_comap]
      intro w hw
      rw [Ideal.mem_comap, RingHom.comp_apply, RingHom.comp_apply, fromPoly_C_mk, ← sum_homogeneousComponent w,
        map_sum]
      refine Ideal.sum_mem _ fun k _ => ?_
      rw [fromChart_hom I t (homogeneousComponent_isHomogeneous k w)]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ((hmemP _).mpr (hW w hw k)))
    exact fun q hq => hle hq
  have hΨin : ∀ y ∈ (PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t))).map (algebraMap (MvPolynomial Unit (ChartRing I t))
      (Localization.Away (X () : MvPolynomial Unit (ChartRing I t)))),
      fromLoc I t hI y ∈ P.map (algebraMap _ (Localization.Away (linClass I t))) := by
    have hle : (PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t))).map (algebraMap (MvPolynomial Unit (ChartRing I t))
        (Localization.Away (X () : MvPolynomial Unit (ChartRing I t)))) ≤
        Ideal.comap (fromLoc I t hI) (P.map (algebraMap _ (Localization.Away (linClass I t)))) := by
      rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, Ideal.map_le_iff_le_comap, Ideal.comap_comap]
      intro q hq
      rw [Ideal.mem_comap, RingHom.comp_apply, RingHom.comp_apply, fromLoc_algebraMap]
      exact hψPQ q hq
    exact fun y hy => hle hy
  have hΦin : ∀ x ∈ P.map (algebraMap _ (Localization.Away (linClass I t))),
      toLoc I t hI x ∈ (PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t))).map (algebraMap (MvPolynomial Unit (ChartRing I t))
        (Localization.Away (X () : MvPolynomial Unit (ChartRing I t)))) := by
    have hle : P.map (algebraMap _ (Localization.Away (linClass I t))) ≤
        Ideal.comap (toLoc I t hI) ((PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t))).map (algebraMap (MvPolynomial Unit (ChartRing I t))
          (Localization.Away (X () : MvPolynomial Unit (ChartRing I t))))) := by
      rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap]
      intro r hr
      rw [Ideal.mem_comap, RingHom.comp_apply, toLoc_algebraMap]
      exact Ideal.mem_map_of_mem _ (hφP r hr)
    exact fun x hx => hle hx
  have hcorr : ∀ y, y ∈ (PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t))).map (algebraMap (MvPolynomial Unit (ChartRing I t))
        (Localization.Away (X () : MvPolynomial Unit (ChartRing I t)))) ↔
      (locEquiv I t hI).symm y ∈ P.map (algebraMap _ (Localization.Away (linClass I t))) := by
    intro y
    change _ ↔ fromLoc I t hI y ∈ _
    refine ⟨hΨin y, fun h => ?_⟩
    have := hΦin _ h
    rwa [toLoc_fromLoc] at this

  calc Ring.ord (Localization.AtPrime P) (algebraMap _ _ (Ideal.Quotient.mk I g))
      = Ring.ord (Localization.AtPrime (P.map (algebraMap _ (Localization.Away (linClass I t)))))
          (algebraMap _ _ (algebraMap _ (Localization.Away (linClass I t)) (Ideal.Quotient.mk I g))) :=
        (ord_atPrime_map_localization (Submonoid.powers (linClass I t)) P hdR _).symm
    _ = Ring.ord (Localization.AtPrime ((PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t))).map (algebraMap (MvPolynomial Unit (ChartRing I t))
          (Localization.Away (X () : MvPolynomial Unit (ChartRing I t))))))
          (algebraMap _ _ (locEquiv I t hI (algebraMap _ _ (Ideal.Quotient.mk I g)))) :=
        (ord_atPrime_ringEquiv (locEquiv I t hI) _ _ hcorr _).symm
    _ = Ring.ord (Localization.AtPrime ((PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t))).map (algebraMap (MvPolynomial Unit (ChartRing I t))
          (Localization.Away (X () : MvPolynomial Unit (ChartRing I t))))))
          (algebraMap _ _ (algebraMap (MvPolynomial Unit (ChartRing I t))
            (Localization.Away (X () : MvPolynomial Unit (ChartRing I t)))
            (toPolyR I t hI (Ideal.Quotient.mk I g)))) := by
        rw [show locEquiv I t hI (algebraMap _ _ (Ideal.Quotient.mk I g)) =
          toLoc I t hI (algebraMap _ _ (Ideal.Quotient.mk I g)) from rfl, toLoc_algebraMap]
    _ = Ring.ord (Localization.AtPrime (PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t))))
          (algebraMap _ _ (toPolyR I t hI (Ideal.Quotient.mk I g))) :=
        ord_atPrime_map_localization (Submonoid.powers _) (PQ.map (C : ChartRing I t →+* MvPolynomial Unit (ChartRing I t))) hdB _
    _ = Ring.ord (Localization.AtPrime PQ) (algebraMap _ _ (Ideal.Quotient.mk (chartIdealOf I t) g)) := by
        rw [toPolyR_mk, toPoly_hom I t hg]
        exact ord_X_pow_mul_C h₁ PQ _ d

end

end GroundTheory.Heights₂.Heights
