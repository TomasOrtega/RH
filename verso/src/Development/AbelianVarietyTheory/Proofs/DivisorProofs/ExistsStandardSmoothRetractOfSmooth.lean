import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsWitnessesOfFormallySmoothQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothPresentationRelationsCombinationNormalStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SmoothRetract

open MvPolynomial

variable {R₀ : Type} [CommRing R₀] {n r : ℕ}

def tang (g : Fin r → MvPolynomial (Fin n) R₀) (a : Fin n → Fin r → MvPolynomial (Fin n) R₀)
    (i l : Fin n) : MvPolynomial (Fin n) R₀ :=
  (if i = l then 1 else 0) + ∑ k, a i k * pderiv l (g k)

def rel (g : Fin r → MvPolynomial (Fin n) R₀) (a : Fin n → Fin r → MvPolynomial (Fin n) R₀)
    (i : Fin n) : MvPolynomial (Fin n ⊕ Fin n) R₀ :=
  rename Sum.inr (∑ k, a i k * g k) +
    ∑ l, rename Sum.inr (tang g a i l) * (X (Sum.inl l) - X (Sum.inr l))

/- English proof (translation)
Simplify using `[rel, Derivation.leibniz, pderiv_rename Sum.inr_injective, pderiv_X, Pi.single_apply, aeval_rename, Function.comp_def, hg, tang, Finset.sum_add_distrib, mul_add, add_mul]`. Conclude with `if_congr eq_comm rfl rfl`.
-/
theorem aeval_pderiv_rel (g : Fin r → MvPolynomial (Fin n) R₀)
    (a : Fin n → Fin r → MvPolynomial (Fin n) R₀) {B : Type} [CommRing B] [Algebra R₀ B]
    (xb : Fin n → B) (hg : ∀ k, aeval xb (g k) = 0) (i j : Fin n) :
    aeval (Sum.elim xb xb) (pderiv (Sum.inr i) (rel g a j)) = -(if i = j then 1 else 0) := by
  classical
  simp [rel, Derivation.leibniz, pderiv_rename Sum.inr_injective, pderiv_X, Pi.single_apply,
    aeval_rename, Function.comp_def, hg, tang, Finset.sum_add_distrib, mul_add, add_mul]
  exact if_congr eq_comm rfl rfl

/- English proof (translation)
Simplify using `[tang, mul_add, Finset.sum_add_distrib]`.
-/
theorem sum_pderiv_mul_tang (g : Fin r → MvPolynomial (Fin n) R₀)
    (a : Fin n → Fin r → MvPolynomial (Fin n) R₀) (j : Fin r) (l : Fin n) :
    ∑ i, pderiv i (g j) * tang g a i l =
      pderiv l (g j) + ∑ i, pderiv i (g j) * ∑ k, a i k * pderiv l (g k) := by
  classical
  simp [tang, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Use `set J : Ideal (MvPolynomial (Fin n) R₀) := Ideal.span (Set.range g) with hJ`. Use `set K : Ideal (MvPolynomial (Fin n ⊕ Fin n) R₀) := Ideal.span (Set.range (rel g a)) with hK`. Set `xb : Fin n → MvPolynomial (Fin n) R₀ ⧸ J` to `fun l => Ideal.Quotient.mk J (X l)`. Establish `hxb : ∀ p, aeval xb p = Ideal.Quotient.mk J p` using `fun p => AlgHom.congr_fun (MvPolynomial.algHom_ext (f := aeval xb) (g := Ideal.Quotient.mkₐ R₀ J) fun l => by simp [xb]) p`. Establish `hg0 : ∀ k, Ideal.Quotient.mk J (g k) = 0` using `fun k => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨k, rfl⟩)`.

Set `r₀' : MvPolynomial (Fin n ⊕ Fin n) R₀ →ₐ[R₀] MvPolynomial (Fin n) R₀ ⧸ J` to `aeval (Sum.elim xb xb)`. Establish `hren : ∀ p, r₀' (rename Sum.inr p) = Ideal.Quotient.mk J p` using `fun p => by`. Simplify using `[r₀', aeval_rename, Function.comp_def, ← hxb]`. Establish `hs0 : ∀ l, r₀' (X (Sum.inl l) - X (Sum.inr l)) = 0` using `fun l => by simp [r₀']`. Establish `hrel : ∀ i, r₀' (rel g a i) = 0`.

Introduce `i`. Simplify using `only [rel, map_add, map_sum, map_mul, hren, hs0, mul_zero, Finset.sum_const_zero, add_zero, hg0]`. Establish `hKle : K ≤ RingHom.ker r₀'` using `Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hrel i)`. Set `r₀ : (MvPolynomial (Fin n ⊕ Fin n) R₀ ⧸ K) →ₐ[R₀] MvPolynomial (Fin n) R₀ ⧸ J` to `Ideal.Quotient.liftₐ K r₀' (fun x hx => hKle hx)`. Establish `hr₀ : ∀ p, r₀ (Ideal.Quotient.mk K p) = r₀' p` using `fun p => rfl`.

Set `P` to `Algebra.PreSubmersivePresentation.naive (v := rel g a) Sum.inr Sum.inr_injective`. Establish `hval : ∀ v, P.val v = Ideal.Quotient.mk K (X v)` using `fun v => by`. Simplify using `[P]`. Both sides reduce to the same expression. Establish `hr₀alg : ∀ p, r₀ (algebraMap P.Ring _ p) = r₀' p`.

Introduce `p`. Rewrite using `[Algebra.Generators.algebraMap_apply]`. Establish `: r₀.comp (aeval P.val) = r₀'` using `MvPolynomial.algHom_ext fun v => by simp [hval, hr₀]`. Conclude with `AlgHom.congr_fun this p`. Establish `hjac : IsUnit (r₀ P.jacobian)`.

Rewrite using `[P.jacobian_eq_jacobiMatrix_det, hr₀alg]`. Establish `hM : r₀'.toRingHom.mapMatrix P.jacobiMatrix = -1`. Use extensionality with `i j`. Rewrite using `[RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.PreSubmersivePresentation.jacobiMatrix_naive]`. Express the relevant statement in the definitionally equal form `aeval (Sum.elim xb xb) _ = _`.

Rewrite using `[aeval_pderiv_rel g a xb (fun k => by rw [hxb, hg0])]`. Simplify using `[Matrix.one_apply]`. Establish `: r₀' P.jacobiMatrix.det = (r₀'.toRingHom.mapMatrix P.jacobiMatrix).det` using `RingHom.map_det _ _`. Rewrite using `[this, hM, Matrix.det_neg, Matrix.det_one, _root_.mul_one]`. Conclude with `(isUnit_one.neg).pow _`.

Set `D` to `MvPolynomial (Fin n ⊕ Fin n) R₀ ⧸ K`. Set `T1` to `Localization.Away P.jacobian`. Use `haveI hT1 : Algebra.IsStandardSmooth R₀ T1 := by`. Set `Q` to `Algebra.SubmersivePresentation.localizationAway T1 P.jacobian`. Set `P' : Algebra.SubmersivePresentation R₀ T1 (Unit ⊕ (Fin n ⊕ Fin n)) (Unit ⊕ Fin n)` to `{ __ := Q.toPreSubmersivePresentation.comp P jacobian_isUnit := by`.

Rewrite using `[Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian, Algebra.smul_def]`. Conclude with `(IsLocalization.Away.algebraMap_isUnit _).mul Q.jacobian_isUnit }`. Conclude with `P'.isStandardSmooth`. Set `r₁ : T1 →ₐ[R₀] MvPolynomial (Fin n) R₀ ⧸ J` to `IsLocalization.Away.liftAlgHom P.jacobian (f := r₀) hjac`. Establish `hr₁ : ∀ y, r₁ (algebraMap D T1 y) = r₀ y` using `fun y => by`.

Rewrite using `[IsLocalization.Away.liftAlgHom_apply]`. Conclude with `IsLocalization.Away.lift_eq _ _ _`. Set `φ : MvPolynomial (Fin n) R₀ →+* D` to `(Ideal.Quotient.mk K).comp (rename Sum.inr : _ →ₐ[R₀] MvPolynomial (Fin n ⊕ Fin n) R₀).toRingHom`. Establish `hφ : ∀ p, φ p = Ideal.Quotient.mk K (rename Sum.inr p)` using `fun p => rfl`. Set `G : Fin r → D` to `fun k => φ (g k)`.

Set `s : Fin n → D` to `fun l => Ideal.Quotient.mk K (X (Sum.inl l) - X (Sum.inr l))`. Set `JD : Ideal D` to `Ideal.span (Set.range G)`. Set `L : Ideal D` to `JD ⊔ Ideal.span (Set.range s)`. Establish `hJD : J.map φ = JD`. Simplify using `only [hJ, Ideal.map_span, JD, G, ← Set.range_comp]`.

Both sides reduce to the same expression. Establish `hrelD : ∀ i, φ (∑ k, a i k * g k) + ∑ l, φ (tang g a i l) * s l = 0`. Introduce `i`. Establish `: Ideal.Quotient.mk K (rel g a i) = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)`. Rewrite using `[← this]`.

Simplify using `only [rel, map_add, map_sum, map_mul, hφ, s]`. Establish `key : ∀ j, G j ∈ L * JD`. Introduce `j`. Establish `e1 : φ (g j + ∑ i, pderiv i (g j) * ∑ k, a i k * g k) = G j + ∑ i, φ (pderiv i (g j)) * φ (∑ k, a i k * g k)`. Rewrite using `[map_add, map_sum]`.

Simplify using `only [map_mul, G]`. Establish `hs : ∑ i, φ (pderiv i (g j)) * φ (∑ k, a i k * g k) + ∑ i, φ (pderiv i (g j)) * ∑ l, φ (tang g a i l) * s l = 0`. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_eq_zero fun i _ => by rw [← mul_add, hrelD i, mul_zero]`. Establish `e3 : ∑ l, s l * φ (∑ i, pderiv i (g j) * tang g a i l) = ∑ i, φ (pderiv i (g j)) * ∑ l, φ (tang g a i l) * s l`.

Simplify using `only [map_sum, map_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`. Establish `eq : G j = φ (g j + ∑ i, pderiv i (g j) * ∑ k, a i k * g k) + ∑ l, s l * φ (∑ i, pderiv i (g j) * tang g a i l)`. Rewrite using `[e3]`.

Take the linear combination `-e1 - hs`. Rewrite using `[eq]`. Use `Ideal.add_mem _ ?_ (Ideal.sum_mem _ fun l _ => ?_)` and prove the remaining obligations. Establish `: φ (g j + ∑ i, pderiv i (g j) * ∑ k, a i k * g k) ∈ JD ^ 2`. Rewrite using `[← hJD, ← Ideal.map_pow]`.

Conclude with `Ideal.mem_map_of_mem φ (h1 j)`. Rewrite `this` using `[pow_two]`. Conclude with `Ideal.mul_mono_left le_sup_left this`. Use `Ideal.mul_mem_mul (Ideal.mem_sup_right (Ideal.subset_span ⟨l, rfl⟩)) ?_` and prove the remaining obligations. Rewrite using `[sum_pderiv_mul_tang, ← hJD]`.

Conclude with `Ideal.mem_map_of_mem φ (h2 j l)`. Take `⟨e, he1, he⟩` from `Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul L JD (Submodule.fg_span (Set.finite_range G)) (by`. Rewrite using `[Ideal.smul_eq_mul]`. Conclude with `Ideal.span_le.2 (by rintro _ ⟨j, rfl⟩; exact key j))`. Establish `hL : L ≤ RingHom.ker r₀`.

Use `sup_le (Ideal.span_le.2 ?_) (Ideal.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Express the relevant statement in the definitionally equal form `r₀ (Ideal.Quotient.mk K (rename Sum.inr (g k))) = 0`. Rewrite using `[hr₀, hren, hg0]`. Introduce and unpack `_ ⟨l, rfl⟩`.

Express the relevant statement in the definitionally equal form `r₀ (Ideal.Quotient.mk K _) = 0`. Rewrite using `[hr₀, hs0]`. Establish `hre : r₀ e = 1`. Use `hL he1` as an intermediate fact. Rewrite `this` using `[RingHom.mem_ker, map_sub, map_one, sub_eq_zero]`.

Conclude with `this`. Set `C₀` to `Localization.Away (algebraMap D T1 e)`. Use `haveI : Algebra.IsStandardSmooth T1 C₀ := Algebra.IsStandardSmooth.localization_away (algebraMap D T1 e)`. Establish `hC : Algebra.IsStandardSmooth R₀ C₀` using `Algebra.IsStandardSmooth.trans R₀ T1 C₀`. Set `r₂ : C₀ →ₐ[R₀] MvPolynomial (Fin n) R₀ ⧸ J` to `IsLocalization.Away.liftAlgHom (algebraMap D T1 e) (f := r₁) (by rw [hr₁, hre]; exact isUnit_one)`.

Establish `hr₂ : ∀ y, r₂ (algebraMap T1 C₀ y) = r₁ y` using `fun y => by`. Rewrite using `[IsLocalization.Away.liftAlgHom_apply]`. Conclude with `IsLocalization.Away.lift_eq _ _ _`. Set `ψ : D →ₐ[R₀] C₀` to `(IsScalarTower.toAlgHom R₀ T1 C₀).comp (IsScalarTower.toAlgHom R₀ D T1)`. Establish `hψe : IsUnit (ψ e)` using `IsLocalization.Away.algebraMap_isUnit (algebraMap D T1 e)`.

Establish `hψG : ∀ k, ψ (G k) = 0`. Introduce `k`. Establish `h0 : e * G k = 0` using `he (G k) (Ideal.subset_span ⟨k, rfl⟩)`. Establish `: ψ e * ψ (G k) = 0` using `by rw [← map_mul, h0, map_zero]`. Conclude with `(hψe.mul_right_eq_zero).1 this`.

Establish `hJle : J ≤ RingHom.ker (ψ.comp ((Ideal.Quotient.mkₐ R₀ K).comp (rename Sum.inr : _ →ₐ[R₀] MvPolynomial (Fin n ⊕ Fin n) R₀)))` using `Ideal.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hψG k)`. Set `i : (MvPolynomial (Fin n) R₀ ⧸ J) →ₐ[R₀] C₀` to `Ideal.Quotient.liftₐ J _ (fun x hx => hJle hx)`. Use `⟨C₀, inferInstance, inferInstance, i, r₂, hC, fun x => ?_⟩` and prove the remaining obligations. Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Express the relevant statement in the definitionally equal form `r₂ (algebraMap T1 C₀ (algebraMap D T1 (Ideal.Quotient.mk K (rename Sum.inr p)))) = _`.

Rewrite using `[hr₂, hr₁, hr₀, hren]`.
-/
theorem core (g : Fin r → MvPolynomial (Fin n) R₀) (a : Fin n → Fin r → MvPolynomial (Fin n) R₀)
    (h1 : ∀ j, g j + ∑ i, pderiv i (g j) * ∑ k, a i k * g k ∈ Ideal.span (Set.range g) ^ 2)
    (h2 : ∀ j m, pderiv m (g j) + ∑ i, pderiv i (g j) * ∑ k, a i k * pderiv m (g k) ∈
      Ideal.span (Set.range g)) :
    ∃ (C₀ : Type) (_ : CommRing C₀) (_ : Algebra R₀ C₀)
      (i : (MvPolynomial (Fin n) R₀ ⧸ Ideal.span (Set.range g)) →ₐ[R₀] C₀)
      (r : C₀ →ₐ[R₀] (MvPolynomial (Fin n) R₀ ⧸ Ideal.span (Set.range g))),
      Algebra.IsStandardSmooth R₀ C₀ ∧ ∀ x, r (i x) = x := by
  classical
  set J : Ideal (MvPolynomial (Fin n) R₀) := Ideal.span (Set.range g) with hJ
  set K : Ideal (MvPolynomial (Fin n ⊕ Fin n) R₀) := Ideal.span (Set.range (rel g a)) with hK
  let xb : Fin n → MvPolynomial (Fin n) R₀ ⧸ J := fun l => Ideal.Quotient.mk J (X l)
  have hxb : ∀ p, aeval xb p = Ideal.Quotient.mk J p := fun p =>
    AlgHom.congr_fun (MvPolynomial.algHom_ext (f := aeval xb) (g := Ideal.Quotient.mkₐ R₀ J)
      fun l => by simp [xb]) p
  have hg0 : ∀ k, Ideal.Quotient.mk J (g k) = 0 := fun k =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨k, rfl⟩)
  let r₀' : MvPolynomial (Fin n ⊕ Fin n) R₀ →ₐ[R₀] MvPolynomial (Fin n) R₀ ⧸ J :=
    aeval (Sum.elim xb xb)
  have hren : ∀ p, r₀' (rename Sum.inr p) = Ideal.Quotient.mk J p := fun p => by
    simp [r₀', aeval_rename, Function.comp_def, ← hxb]
  have hs0 : ∀ l, r₀' (X (Sum.inl l) - X (Sum.inr l)) = 0 := fun l => by simp [r₀']
  have hrel : ∀ i, r₀' (rel g a i) = 0 := by
    intro i
    simp only [rel, map_add, map_sum, map_mul, hren, hs0, mul_zero, Finset.sum_const_zero,
      add_zero, hg0]
  have hKle : K ≤ RingHom.ker r₀' := Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hrel i)
  let r₀ : (MvPolynomial (Fin n ⊕ Fin n) R₀ ⧸ K) →ₐ[R₀] MvPolynomial (Fin n) R₀ ⧸ J :=
    Ideal.Quotient.liftₐ K r₀' (fun x hx => hKle hx)
  have hr₀ : ∀ p, r₀ (Ideal.Quotient.mk K p) = r₀' p := fun p => rfl
  let P := Algebra.PreSubmersivePresentation.naive (v := rel g a) Sum.inr Sum.inr_injective
  have hval : ∀ v, P.val v = Ideal.Quotient.mk K (X v) := fun v => by
    simp [P]
    rfl
  have hr₀alg : ∀ p, r₀ (algebraMap P.Ring _ p) = r₀' p := by
    intro p
    rw [Algebra.Generators.algebraMap_apply]
    have : r₀.comp (aeval P.val) = r₀' :=
      MvPolynomial.algHom_ext fun v => by simp [hval, hr₀]
    exact AlgHom.congr_fun this p
  have hjac : IsUnit (r₀ P.jacobian) := by
    rw [P.jacobian_eq_jacobiMatrix_det, hr₀alg]
    have hM : r₀'.toRingHom.mapMatrix P.jacobiMatrix = -1 := by
      ext i j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply,
        Algebra.PreSubmersivePresentation.jacobiMatrix_naive]
      change aeval (Sum.elim xb xb) _ = _
      rw [aeval_pderiv_rel g a xb (fun k => by rw [hxb, hg0])]
      simp [Matrix.one_apply]
    have : r₀' P.jacobiMatrix.det = (r₀'.toRingHom.mapMatrix P.jacobiMatrix).det :=
      RingHom.map_det _ _
    rw [this, hM, Matrix.det_neg, Matrix.det_one, _root_.mul_one]
    exact (isUnit_one.neg).pow _
  let D := MvPolynomial (Fin n ⊕ Fin n) R₀ ⧸ K
  let T1 := Localization.Away P.jacobian
  haveI hT1 : Algebra.IsStandardSmooth R₀ T1 := by
    let Q := Algebra.SubmersivePresentation.localizationAway T1 P.jacobian
    let P' : Algebra.SubmersivePresentation R₀ T1 (Unit ⊕ (Fin n ⊕ Fin n)) (Unit ⊕ Fin n) :=
      { __ := Q.toPreSubmersivePresentation.comp P
        jacobian_isUnit := by
          rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
            Algebra.smul_def]
          exact (IsLocalization.Away.algebraMap_isUnit _).mul Q.jacobian_isUnit }
    exact P'.isStandardSmooth
  let r₁ : T1 →ₐ[R₀] MvPolynomial (Fin n) R₀ ⧸ J :=
    IsLocalization.Away.liftAlgHom P.jacobian (f := r₀) hjac
  have hr₁ : ∀ y, r₁ (algebraMap D T1 y) = r₀ y := fun y => by
    rw [IsLocalization.Away.liftAlgHom_apply]
    exact IsLocalization.Away.lift_eq _ _ _

  let φ : MvPolynomial (Fin n) R₀ →+* D :=
    (Ideal.Quotient.mk K).comp (rename Sum.inr : _ →ₐ[R₀] MvPolynomial (Fin n ⊕ Fin n) R₀).toRingHom
  have hφ : ∀ p, φ p = Ideal.Quotient.mk K (rename Sum.inr p) := fun p => rfl
  let G : Fin r → D := fun k => φ (g k)
  let s : Fin n → D := fun l => Ideal.Quotient.mk K (X (Sum.inl l) - X (Sum.inr l))
  let JD : Ideal D := Ideal.span (Set.range G)
  let L : Ideal D := JD ⊔ Ideal.span (Set.range s)
  have hJD : J.map φ = JD := by
    simp only [hJ, Ideal.map_span, JD, G, ← Set.range_comp]
    rfl
  have hrelD : ∀ i, φ (∑ k, a i k * g k) + ∑ l, φ (tang g a i l) * s l = 0 := by
    intro i
    have : Ideal.Quotient.mk K (rel g a i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)
    rw [← this]
    simp only [rel, map_add, map_sum, map_mul, hφ, s]
  have key : ∀ j, G j ∈ L * JD := by
    intro j
    have e1 : φ (g j + ∑ i, pderiv i (g j) * ∑ k, a i k * g k) =
        G j + ∑ i, φ (pderiv i (g j)) * φ (∑ k, a i k * g k) := by
      rw [map_add, map_sum]
      simp only [map_mul, G]
    have hs : ∑ i, φ (pderiv i (g j)) * φ (∑ k, a i k * g k) +
        ∑ i, φ (pderiv i (g j)) * ∑ l, φ (tang g a i l) * s l = 0 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero fun i _ => by rw [← mul_add, hrelD i, mul_zero]
    have e3 : ∑ l, s l * φ (∑ i, pderiv i (g j) * tang g a i l) =
        ∑ i, φ (pderiv i (g j)) * ∑ l, φ (tang g a i l) * s l := by
      simp only [map_sum, map_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have eq : G j = φ (g j + ∑ i, pderiv i (g j) * ∑ k, a i k * g k) +
        ∑ l, s l * φ (∑ i, pderiv i (g j) * tang g a i l) := by
      rw [e3]
      linear_combination -e1 - hs
    rw [eq]
    refine Ideal.add_mem _ ?_ (Ideal.sum_mem _ fun l _ => ?_)
    · have : φ (g j + ∑ i, pderiv i (g j) * ∑ k, a i k * g k) ∈ JD ^ 2 := by
        rw [← hJD, ← Ideal.map_pow]
        exact Ideal.mem_map_of_mem φ (h1 j)
      rw [pow_two] at this
      exact Ideal.mul_mono_left le_sup_left this
    · refine Ideal.mul_mem_mul (Ideal.mem_sup_right (Ideal.subset_span ⟨l, rfl⟩)) ?_
      rw [sum_pderiv_mul_tang, ← hJD]
      exact Ideal.mem_map_of_mem φ (h2 j l)
  obtain ⟨e, he1, he⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul L JD
    (Submodule.fg_span (Set.finite_range G)) (by
      rw [Ideal.smul_eq_mul]
      exact Ideal.span_le.2 (by rintro _ ⟨j, rfl⟩; exact key j))
  have hL : L ≤ RingHom.ker r₀ := by
    refine sup_le (Ideal.span_le.2 ?_) (Ideal.span_le.2 ?_)
    · rintro _ ⟨k, rfl⟩
      change r₀ (Ideal.Quotient.mk K (rename Sum.inr (g k))) = 0
      rw [hr₀, hren, hg0]
    · rintro _ ⟨l, rfl⟩
      change r₀ (Ideal.Quotient.mk K _) = 0
      rw [hr₀, hs0]
  have hre : r₀ e = 1 := by
    have := hL he1
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at this
    exact this
  let C₀ := Localization.Away (algebraMap D T1 e)
  haveI : Algebra.IsStandardSmooth T1 C₀ :=
    Algebra.IsStandardSmooth.localization_away (algebraMap D T1 e)
  have hC : Algebra.IsStandardSmooth R₀ C₀ := Algebra.IsStandardSmooth.trans R₀ T1 C₀
  let r₂ : C₀ →ₐ[R₀] MvPolynomial (Fin n) R₀ ⧸ J :=
    IsLocalization.Away.liftAlgHom (algebraMap D T1 e) (f := r₁) (by rw [hr₁, hre]; exact isUnit_one)
  have hr₂ : ∀ y, r₂ (algebraMap T1 C₀ y) = r₁ y := fun y => by
    rw [IsLocalization.Away.liftAlgHom_apply]
    exact IsLocalization.Away.lift_eq _ _ _
  let ψ : D →ₐ[R₀] C₀ := (IsScalarTower.toAlgHom R₀ T1 C₀).comp (IsScalarTower.toAlgHom R₀ D T1)
  have hψe : IsUnit (ψ e) := IsLocalization.Away.algebraMap_isUnit (algebraMap D T1 e)
  have hψG : ∀ k, ψ (G k) = 0 := by
    intro k
    have h0 : e * G k = 0 := he (G k) (Ideal.subset_span ⟨k, rfl⟩)
    have : ψ e * ψ (G k) = 0 := by rw [← map_mul, h0, map_zero]
    exact (hψe.mul_right_eq_zero).1 this
  have hJle : J ≤ RingHom.ker (ψ.comp ((Ideal.Quotient.mkₐ R₀ K).comp
      (rename Sum.inr : _ →ₐ[R₀] MvPolynomial (Fin n ⊕ Fin n) R₀))) :=
    Ideal.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hψG k)
  let i : (MvPolynomial (Fin n) R₀ ⧸ J) →ₐ[R₀] C₀ :=
    Ideal.Quotient.liftₐ J _ (fun x hx => hJle hx)
  refine ⟨C₀, inferInstance, inferInstance, i, r₂, hC, fun x => ?_⟩
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  change r₂ (algebraMap T1 C₀ (algebraMap D T1 (Ideal.Quotient.mk K (rename Sum.inr p)))) = _
  rw [hr₂, hr₁, hr₀, hren]

/- English proof (translation)
Introduce `R₀ B₀ _ _ _ hsm`. Take `⟨n, f, hf, hfg⟩` from `Algebra.FinitePresentation.out (R := R₀) (A := B₀)`. Take `⟨r, g, hg⟩` from `Submodule.fg_iff_exists_fin_generating_family.1 hfg`. Set `e : (MvPolynomial (Fin n) R₀ ⧸ Ideal.span (Set.range g)) ≃ₐ[R₀] B₀` to `(Ideal.quotientEquivAlgOfEq R₀ hg).trans (Ideal.quotientKerAlgEquivOfSurjective hf)`. Use `haveI : Algebra.FormallySmooth R₀ (MvPolynomial (Fin n) R₀ ⧸ Ideal.span (Set.range g)) := Algebra.FormallySmooth.of_equiv e.symm`.

Take `⟨a, b, hab⟩` from `GlobalTheory.exists_witnesses_of_formallySmooth_quotient (Fin n) R₀ r g inferInstance`. Take `⟨h1, h2⟩` from `GlobalTheory.T.smoothPresentation_relations_combination_normal R₀ n r g a b hab`. Take `⟨C₀, i1, i2, i, ρ, hstd, hret⟩` from `core g a h1 h2`. Conclude with `⟨C₀, i1, i2, i.comp e.symm.toAlgHom, e.toAlgHom.comp ρ, hstd, fun x => by simp [hret]⟩`.
-/
theorem exists_retract_isStandardSmooth : ∀ (R₀ B₀ : Type) [CommRing R₀] [CommRing B₀] [Algebra R₀ B₀],
    Algebra.Smooth R₀ B₀ → ∃ (C₀ : Type) (_ : CommRing C₀) (_ : Algebra R₀ C₀) (i : B₀ →ₐ[R₀] C₀)
      (r : C₀ →ₐ[R₀] B₀), Algebra.IsStandardSmooth R₀ C₀ ∧ ∀ x, r (i x) = x := by
  intro R₀ B₀ _ _ _ hsm
  obtain ⟨n, f, hf, hfg⟩ := Algebra.FinitePresentation.out (R := R₀) (A := B₀)
  obtain ⟨r, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
  let e : (MvPolynomial (Fin n) R₀ ⧸ Ideal.span (Set.range g)) ≃ₐ[R₀] B₀ :=
    (Ideal.quotientEquivAlgOfEq R₀ hg).trans (Ideal.quotientKerAlgEquivOfSurjective hf)
  haveI : Algebra.FormallySmooth R₀ (MvPolynomial (Fin n) R₀ ⧸ Ideal.span (Set.range g)) :=
    Algebra.FormallySmooth.of_equiv e.symm
  obtain ⟨a, b, hab⟩ :=
    GlobalTheory.exists_witnesses_of_formallySmooth_quotient (Fin n) R₀ r g inferInstance
  obtain ⟨h1, h2⟩ := GlobalTheory.T.smoothPresentation_relations_combination_normal R₀ n r g a b hab
  obtain ⟨C₀, i1, i2, i, ρ, hstd, hret⟩ := core g a h1 h2
  exact ⟨C₀, i1, i2, i.comp e.symm.toAlgHom, e.toAlgHom.comp ρ, hstd, fun x => by simp [hret]⟩

end GlobalTheory.SmoothRetract
