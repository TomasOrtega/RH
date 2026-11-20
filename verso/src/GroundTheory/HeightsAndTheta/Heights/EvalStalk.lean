import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexPointsBase
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory MvPolynomial GroundTheory.Arith.SchemeCoh
open scoped LinearAlgebra.Projectivization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

variable {A : Type u} [CommRing A] {N : ℕ}

def IsOver (ρ : A →+* ℂ) (w : Fin (N + 1) → ℂ) (x : ProjectiveSpectrum (ProjSpace.grading A N)) :
    Prop :=
  ∀ d, ∀ f ∈ ProjSpace.grading A N d, f ∈ x.asHomogeneousIdeal ↔ evalAt ρ w f = 0

/- English proof (translation)
Introduce `_ _ hf` and use `mem_projPointOf ρ _ hf`.
-/
lemma isOver_projPoint (ρ : A →+* ℂ) (v : CP N) : IsOver ρ v.rep (projPoint ρ v) :=
  fun _ _ hf => mem_projPointOf ρ _ hf

/- English proof (translation)
Introduce `d f hf`. Rewrite using `[h d f hf, evalAt_smul ρ hf, mul_eq_zero, or_iff_right (pow_ne_zero _ hc)]`.
-/
lemma IsOver.smul {ρ : A →+* ℂ} {w : Fin (N + 1) → ℂ} {x : ProjectiveSpectrum (ProjSpace.grading A N)}
    (h : IsOver ρ w x) {c : ℂ} (hc : c ≠ 0) : IsOver ρ (c • w) x := by
  intro d f hf
  rw [h d f hf, evalAt_smul ρ hf, mul_eq_zero, or_iff_right (pow_ne_zero _ hc)]

/- English proof (translation)
Introduce `d f hf`. Rewrite using `[h d f hf, evalAt_conj, map_eq_zero]`.
-/
lemma IsOver.conj {ρ : A →+* ℂ} {w : Fin (N + 1) → ℂ} {x : ProjectiveSpectrum (ProjSpace.grading A N)}
    (h : IsOver ρ w x) : IsOver ((starRingEnd ℂ).comp ρ) (CP.conjVec w) x := by
  intro d f hf
  rw [h d f hf, evalAt_conj, map_eq_zero]

def evalLine (ρ : A →+* ℂ) (w : Fin (N + 1) → ℂ) : MvPolynomial (Fin (N + 1)) A →+* Polynomial ℂ :=
  eval₂Hom (Polynomial.C.comp ρ) (fun k => Polynomial.C (w k) * Polynomial.X)

/- English proof (translation)
Rewrite using `[evalLine, coe_eval₂Hom, eval₂_eq', evalAt, eval₂_eq', map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Establish `hd : ∑ k, m k = d`. Use `hf (mem_support_iff.mp hm)` as an intermediate fact. Simplify `this` using `[Finsupp.weight_apply, Finsupp.sum_fintype]`.

Simplify using `only [RingHom.comp_apply, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd, map_mul, map_prod, map_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma evalLine_of_isHomogeneous (ρ : A →+* ℂ) (w : Fin (N + 1) → ℂ)
    {f : MvPolynomial (Fin (N + 1)) A} {d : ℕ} (hf : f.IsHomogeneous d) :
    evalLine ρ w f = Polynomial.C (evalAt ρ w f) * Polynomial.X ^ d := by
  rw [evalLine, coe_eval₂Hom, eval₂_eq', evalAt, eval₂_eq', map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ k, m k = d := by
    have := hf (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  simp only [RingHom.comp_apply, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd,
    map_mul, map_prod, map_pow]
  ring

/- English proof (translation)
Use `conv_lhs => rw [← sum_homogeneousComponent f]`. Rewrite using `[map_sum, Polynomial.finsetSum_coeff]`. Repeatedly rewrite using `[evalLine_of_isHomogeneous ρ w (homogeneousComponent_isHomogeneous _ _), Polynomial.coeff_C_mul_X_pow]`. Rewrite using `[Finset.sum_ite_eq]`. Use `split_ifs with h`.

Both sides reduce to the same expression. Rewrite `h` using `[Finset.mem_range, not_lt]`. Rewrite using `[homogeneousComponent_eq_zero _ _ (Nat.lt_of_succ_le h)]`. Simplify using the standard rewrite rules.
-/
lemma coeff_evalLine (ρ : A →+* ℂ) (w : Fin (N + 1) → ℂ) (f : MvPolynomial (Fin (N + 1)) A)
    (d : ℕ) : (evalLine ρ w f).coeff d = evalAt ρ w (homogeneousComponent d f) := by
  conv_lhs => rw [← sum_homogeneousComponent f]
  rw [map_sum, Polynomial.finsetSum_coeff]
  simp_rw [evalLine_of_isHomogeneous ρ w (homogeneousComponent_isHomogeneous _ _),
    Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [Finset.mem_range, not_lt] at h
    rw [homogeneousComponent_eq_zero _ _ (Nat.lt_of_succ_le h)]
    simp

/- English proof (translation)
Introduce `h0`. Apply `hf` to reduce the goal to its premises. Rewrite using `[← sum_homogeneousComponent f]`. Use `Ideal.sum_mem _ fun d _ => ?_` and prove the remaining obligations. Use `(h d _ (homogeneousComponent_isHomogeneous d f)).2 ?_` and prove the remaining obligations.

Rewrite using `[← coeff_evalLine, h0, Polynomial.coeff_zero]`.
-/
lemma evalLine_ne_zero {ρ : A →+* ℂ} {w : Fin (N + 1) → ℂ} {x : ProjectiveSpectrum (ProjSpace.grading A N)}
    (h : IsOver ρ w x) {f : MvPolynomial (Fin (N + 1)) A} (hf : f ∉ x.asHomogeneousIdeal) :
    evalLine ρ w f ≠ 0 := by
  intro h0
  apply hf
  rw [← sum_homogeneousComponent f]
  refine Ideal.sum_mem _ fun d _ => ?_
  refine (h d _ (homogeneousComponent_isHomogeneous d f)).2 ?_
  rw [← coeff_evalLine, h0, Polynomial.coeff_zero]

variable {ρ : A →+* ℂ} {w : Fin (N + 1) → ℂ} {x : ProjectiveSpectrum (ProjSpace.grading A N)}

def locToRatFunc (h : IsOver ρ w x) :
    Localization.AtPrime x.asHomogeneousIdeal.toIdeal →+* RatFunc ℂ :=
  IsLocalization.lift (M := x.asHomogeneousIdeal.toIdeal.primeCompl)
    (g := (algebraMap (Polynomial ℂ) (RatFunc ℂ)).comp (evalLine ρ w)) fun y => by
      rw [isUnit_iff_ne_zero, RingHom.comp_apply, ne_eq,
        map_eq_zero_iff _ (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ))]
      exact evalLine_ne_zero h y.2

def atPrimeToRatFunc (h : IsOver ρ w x) :
    HomogeneousLocalization.AtPrime (ProjSpace.grading A N) x.asHomogeneousIdeal.toIdeal →+*
      RatFunc ℂ :=
  (locToRatFunc h).comp (algebraMap _ _)

/- English proof (translation)
Establish `hden : evalAt ρ w (c.den : MvPolynomial (Fin (N + 1)) A) ≠ 0` using `fun h0 => c.den_mem ((h _ _ c.den.2).2 h0)`. Rewrite using `[atPrimeToRatFunc, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.val_mk, Localization.mk_eq_mk', locToRatFunc, IsLocalization.lift_mk'_spec]`. Simplify using `only [RingHom.comp_apply]`. Rewrite using `[evalLine_of_isHomogeneous ρ w (c.num.2), evalLine_of_isHomogeneous ρ w (c.den.2), IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) (RatFunc ℂ), ← map_mul]`. Use `congr 1`.

Rewrite using `[Polynomial.algebraMap_eq, mul_comm (Polynomial.C (evalAt ρ w c.den) * _), ← mul_assoc, ← Polynomial.C_mul, div_mul_cancel₀ _ hden]`.
-/
lemma atPrimeToRatFunc_mk (h : IsOver ρ w x)
    (c : HomogeneousLocalization.NumDenSameDeg (ProjSpace.grading A N)
      x.asHomogeneousIdeal.toIdeal.primeCompl) :
    atPrimeToRatFunc h (HomogeneousLocalization.mk c) =
      algebraMap ℂ (RatFunc ℂ) (evalAt ρ w c.num / evalAt ρ w c.den) := by
  have hden : evalAt ρ w (c.den : MvPolynomial (Fin (N + 1)) A) ≠ 0 := fun h0 =>
    c.den_mem ((h _ _ c.den.2).2 h0)
  rw [atPrimeToRatFunc, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.val_mk, Localization.mk_eq_mk', locToRatFunc,
    IsLocalization.lift_mk'_spec]
  simp only [RingHom.comp_apply]
  rw [evalLine_of_isHomogeneous ρ w (c.num.2), evalLine_of_isHomogeneous ρ w (c.den.2),
    IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) (RatFunc ℂ), ← map_mul]
  congr 1
  rw [Polynomial.algebraMap_eq, mul_comm (Polynomial.C (evalAt ρ w c.den) * _), ← mul_assoc,
    ← Polynomial.C_mul, div_mul_cancel₀ _ hden]

/- English proof (translation)
Take `⟨c, rfl⟩` from `HomogeneousLocalization.mk_surjective y`. Rewrite using `[atPrimeToRatFunc_mk]`. Conclude with `⟨_, rfl⟩`.
-/
lemma atPrimeToRatFunc_mem_range (h : IsOver ρ w x)
    (y : HomogeneousLocalization.AtPrime (ProjSpace.grading A N) x.asHomogeneousIdeal.toIdeal) :
    atPrimeToRatFunc h y ∈ (algebraMap ℂ (RatFunc ℂ)).range := by
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective y
  rw [atPrimeToRatFunc_mk]
  exact ⟨_, rfl⟩

def constEquiv : (algebraMap ℂ (RatFunc ℂ)).range ≃+* ℂ :=
  (RingEquiv.ofBijective (algebraMap ℂ (RatFunc ℂ)).rangeRestrict
    ⟨fun _ _ hab => (algebraMap ℂ (RatFunc ℂ)).injective (congrArg Subtype.val hab),
      RingHom.rangeRestrict_surjective _⟩).symm

def evalAtPrime (h : IsOver ρ w x) :
    HomogeneousLocalization.AtPrime (ProjSpace.grading A N) x.asHomogeneousIdeal.toIdeal →+* ℂ :=
  constEquiv.toRingHom.comp ((atPrimeToRatFunc h).codRestrict _ (atPrimeToRatFunc_mem_range h))

/- English proof (translation)
Take `⟨c, hc⟩` from `atPrimeToRatFunc_mem_range h y`. Establish `: evalAtPrime h y = c`. Rewrite using `[evalAtPrime, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, constEquiv, RingEquiv.symm_apply_eq]`. Conclude with `Subtype.ext hc.symm`. Rewrite using `[this, hc]`.
-/
lemma algebraMap_evalAtPrime (h : IsOver ρ w x)
    (y : HomogeneousLocalization.AtPrime (ProjSpace.grading A N) x.asHomogeneousIdeal.toIdeal) :
    algebraMap ℂ (RatFunc ℂ) (evalAtPrime h y) = atPrimeToRatFunc h y := by
  obtain ⟨c, hc⟩ := atPrimeToRatFunc_mem_range h y
  have : evalAtPrime h y = c := by
    rw [evalAtPrime, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      constEquiv, RingEquiv.symm_apply_eq]
    exact Subtype.ext hc.symm
  rw [this, hc]

/- English proof (translation)
Apply `(algebraMap ℂ (RatFunc ℂ)).injective` to reduce the goal to its premises. Rewrite using `[algebraMap_evalAtPrime, atPrimeToRatFunc_mk]`.
-/
theorem evalAtPrime_mk (h : IsOver ρ w x)
    (c : HomogeneousLocalization.NumDenSameDeg (ProjSpace.grading A N)
      x.asHomogeneousIdeal.toIdeal.primeCompl) :
    evalAtPrime h (HomogeneousLocalization.mk c) = evalAt ρ w c.num / evalAt ρ w c.den := by
  apply (algebraMap ℂ (RatFunc ℂ)).injective
  rw [algebraMap_evalAtPrime, atPrimeToRatFunc_mk]

/- English proof (translation)
Take `⟨c, rfl⟩` from `HomogeneousLocalization.mk_surjective y`. Rewrite `hy` using `[evalAtPrime_mk, div_ne_zero_iff]`. Establish `hnum : (c.num : MvPolynomial (Fin (N + 1)) A) ∈ x.asHomogeneousIdeal.toIdeal.primeCompl` using `fun hm => hy.1 ((h _ _ c.num.2).1 hm)`. Rewrite using `[← HomogeneousLocalization.isUnit_iff_isUnit_val, HomogeneousLocalization.val_mk, Localization.mk_eq_mk']`. Use `isUnit_of_mul_isUnit_left (y := algebraMap (MvPolynomial (Fin (N + 1)) A) (Localization.AtPrime x.asHomogeneousIdeal.toIdeal) (c.den : MvPolynomial (Fin (N + 1)) A)) ?_` and prove the remaining obligations.

Rewrite using `[IsLocalization.mk'_spec]`. Conclude with `IsLocalization.map_units _ ⟨_, hnum⟩`.
-/
theorem isUnit_of_evalAtPrime_ne_zero (h : IsOver ρ w x)
    {y : HomogeneousLocalization.AtPrime (ProjSpace.grading A N) x.asHomogeneousIdeal.toIdeal}
    (hy : evalAtPrime h y ≠ 0) : IsUnit y := by
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective y
  rw [evalAtPrime_mk, div_ne_zero_iff] at hy
  have hnum : (c.num : MvPolynomial (Fin (N + 1)) A) ∈ x.asHomogeneousIdeal.toIdeal.primeCompl :=
    fun hm => hy.1 ((h _ _ c.num.2).1 hm)
  rw [← HomogeneousLocalization.isUnit_iff_isUnit_val, HomogeneousLocalization.val_mk,
    Localization.mk_eq_mk']
  refine isUnit_of_mul_isUnit_left (y := algebraMap (MvPolynomial (Fin (N + 1)) A)
    (Localization.AtPrime x.asHomogeneousIdeal.toIdeal) (c.den : MvPolynomial (Fin (N + 1)) A)) ?_
  rw [IsLocalization.mk'_spec]
  exact IsLocalization.map_units _ ⟨_, hnum⟩

def evalStalkProj (h : IsOver ρ w x) : (projectiveSpace A N).presheaf.stalk x →+* ℂ :=
  (evalAtPrime h).comp (Proj.stalkIso (ProjSpace.grading A N) x).hom.hom

/- English proof (translation)
Establish `hu` using `isUnit_of_evalAtPrime_ne_zero h hy`. Conclude with `(isUnit_map_iff (Proj.stalkIso (ProjSpace.grading A N) x).commRingCatIsoToRingEquiv y).1 hu`.
-/
theorem isUnit_of_evalStalkProj_ne_zero (h : IsOver ρ w x)
    {y : (projectiveSpace A N).presheaf.stalk x} (hy : evalStalkProj h y ≠ 0) : IsUnit y := by
  have hu := isUnit_of_evalAtPrime_ne_zero h hy
  exact (isUnit_map_iff (Proj.stalkIso (ProjSpace.grading A N) x).commRingCatIsoToRingEquiv y).1 hu

/- English proof (translation)
Take `⟨z, rfl⟩` from `HomogeneousLocalization.mk_surjective y`. Rewrite using `[evalAtPrime_mk, evalAtPrime_mk, evalAt_smul ρ ((mem_homogeneousSubmodule _ _).1 z.num.2), evalAt_smul ρ ((mem_homogeneousSubmodule _ _).1 z.den.2), mul_div_mul_left _ _ (pow_ne_zero _ hc)]`.
-/
lemma evalAtPrime_smul (h : IsOver ρ w x) {c : ℂ} (hc : c ≠ 0)
    (y : HomogeneousLocalization.AtPrime (ProjSpace.grading A N) x.asHomogeneousIdeal.toIdeal) :
    evalAtPrime (h.smul hc) y = evalAtPrime h y := by
  obtain ⟨z, rfl⟩ := HomogeneousLocalization.mk_surjective y
  rw [evalAtPrime_mk, evalAtPrime_mk, evalAt_smul ρ ((mem_homogeneousSubmodule _ _).1 z.num.2),
    evalAt_smul ρ ((mem_homogeneousSubmodule _ _).1 z.den.2),
    mul_div_mul_left _ _ (pow_ne_zero _ hc)]

/- English proof (translation)
Take `⟨z, rfl⟩` from `HomogeneousLocalization.mk_surjective y`. Rewrite using `[evalAtPrime_mk, evalAtPrime_mk, evalAt_conj, evalAt_conj, map_div₀]`.
-/
lemma evalAtPrime_conj (h : IsOver ρ w x)
    (y : HomogeneousLocalization.AtPrime (ProjSpace.grading A N) x.asHomogeneousIdeal.toIdeal) :
    evalAtPrime h.conj y = starRingEnd ℂ (evalAtPrime h y) := by
  obtain ⟨z, rfl⟩ := HomogeneousLocalization.mk_surjective y
  rw [evalAtPrime_mk, evalAtPrime_mk, evalAt_conj, evalAt_conj, map_div₀]

/- English proof (translation)
The claim follows from `evalAtPrime_smul h hc _`.
-/
lemma evalStalkProj_smul (h : IsOver ρ w x) {c : ℂ} (hc : c ≠ 0)
    (y : (projectiveSpace A N).presheaf.stalk x) :
    evalStalkProj (h.smul hc) y = evalStalkProj h y :=
  evalAtPrime_smul h hc _

/- English proof (translation)
The claim follows from `evalAtPrime_conj h _`.
-/
lemma evalStalkProj_conj (h : IsOver ρ w x) (y : (projectiveSpace A N).presheaf.stalk x) :
    evalStalkProj h.conj y = starRingEnd ℂ (evalStalkProj h y) :=
  evalAtPrime_conj h _

namespace ProjScheme

variable (X : ProjScheme A N)

def evalStalk {p : X.X} (h : IsOver ρ w (X.ι.base p)) : X.X.presheaf.stalk p →+* ℂ :=
  RingHom.liftOfSurjective (X.ι.stalkMap p).hom (X.ι.stalkMap_surjective p)
    ⟨evalStalkProj h, fun y hy => by
      rw [RingHom.mem_ker] at hy ⊢
      by_contra hne
      have hu := (isUnit_of_evalStalkProj_ne_zero h hne).map (X.ι.stalkMap p).hom
      rw [hy, isUnit_zero_iff] at hu
      exact zero_ne_one hu⟩

/- English proof (translation)
The claim follows from `RingHom.liftOfRightInverse_comp_apply _ _ _ _ _`.
-/
theorem evalStalk_stalkMap {p : X.X} (h : IsOver ρ w (X.ι.base p))
    (y : (projectiveSpace A N).presheaf.stalk (X.ι.base p)) :
    X.evalStalk h ((X.ι.stalkMap p).hom y) = evalStalkProj h y :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ _

/- English proof (translation)
Use extensionality with `y`. Take `⟨z, rfl⟩` from `X.ι.stalkMap_surjective p y`. Rewrite using `[evalStalk_stalkMap, evalStalk_stalkMap]`. Conclude with `evalStalkProj_smul h hc z`.
-/
theorem evalStalk_smul {p : X.X} (h : IsOver ρ w (X.ι.base p)) {c : ℂ} (hc : c ≠ 0) :
    X.evalStalk (h.smul hc) = X.evalStalk h := by
  ext y
  obtain ⟨z, rfl⟩ := X.ι.stalkMap_surjective p y
  rw [evalStalk_stalkMap, evalStalk_stalkMap]
  exact evalStalkProj_smul h hc z

/- English proof (translation)
Use extensionality with `y`. Take `⟨z, rfl⟩` from `X.ι.stalkMap_surjective p y`. Rewrite using `[evalStalk_stalkMap, RingHom.comp_apply, evalStalk_stalkMap]`. Conclude with `evalStalkProj_conj h z`.
-/
theorem evalStalk_conj {p : X.X} (h : IsOver ρ w (X.ι.base p)) :
    X.evalStalk h.conj = (starRingEnd ℂ).comp (X.evalStalk h) := by
  ext y
  obtain ⟨z, rfl⟩ := X.ι.stalkMap_surjective p y
  rw [evalStalk_stalkMap, RingHom.comp_apply, evalStalk_stalkMap]
  exact evalStalkProj_conj h z

end ProjScheme

end

end GroundTheory.Heights₂.Heights
