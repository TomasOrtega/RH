import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

namespace HomogMinPrime

open MvPolynomial

/- English proof (translation)
Rewrite using `[F.as_sum, map_sum, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Establish `hdeg : d.degree = e`. Assume the negation of the conclusion as `h`. Conclude with `(mem_support_iff.mp hd) (hF.coeff_eq_zero h)`.

Rewrite using `[eval₂Hom_monomial, eval₂Hom_monomial, ← hdeg]`. Simplify using `only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eval_scale {o σ A : Type} [CommRing o] [CommRing A] (f : o →+* A) (g : σ → A) (c : A)
    {F : MvPolynomial σ o} {e : ℕ} (hF : F.IsHomogeneous e) :
    eval₂Hom f (fun a => g a * c) F = c ^ e * eval₂Hom f g F := by
  classical
  rw [F.as_sum, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d.degree = e := by
    by_contra h
    exact (mem_support_iff.mp hd) (hF.coeff_eq_zero h)
  rw [eval₂Hom_monomial, eval₂Hom_monomial, ← hdeg]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Finsupp.degree_apply]
  ring

/- English proof (translation)
Rewrite using `[eval_scale _ (fun a => Polynomial.C (u a)) Polynomial.X hF, ← Polynomial.C_mul_X_pow_eq_monomial, mul_comm]`. Use `congr 1`. Conclude with `(map_eval₂Hom β u (Polynomial.C : K →+* Polynomial K) F).symm`.
-/
theorem eval_cone {o σ K : Type} [CommRing o] [Field K] (β : o →+* K) (u : σ → K)
    {F : MvPolynomial σ o} {e : ℕ} (hF : F.IsHomogeneous e) :
    eval₂Hom ((Polynomial.C : K →+* Polynomial K).comp β)
      (fun a => Polynomial.C (u a) * Polynomial.X) F
      = Polynomial.monomial e (eval₂Hom β u F) := by
  rw [eval_scale _ (fun a => Polynomial.C (u a)) Polynomial.X hF,
    ← Polynomial.C_mul_X_pow_eq_monomial, mul_comm]
  congr 1
  exact (map_eval₂Hom β u (Polynomial.C : K →+* Polynomial K) F).symm

/- English proof (translation)
Rewrite using `[RingHom.mem_ker]`. Establish `h : eval₂Hom ((Polynomial.C : K →+* Polynomial K).comp β) (fun a => Polynomial.C (u a) * Polynomial.X) F = ∑ e ∈ Finset.range (F.totalDegree + 1), Polynomial.monomial e (eval₂Hom β u (homogeneousComponent e F))` using `by conv_lhs => rw [← sum_homogeneousComponent F, map_sum]`. Conclude with `Finset.sum_congr rfl fun e _ => eval_cone β u (homogeneousComponent_isHomogeneous e F)`. Rewrite using `[h]`. Prove the components needed by the constructor for the conclusion.

Introduce `h0 e`. Distinguish the cases in `he : e ∈ Finset.range (F.totalDegree + 1)`. Use `congrArg (fun p => Polynomial.coeff p e) h0` as an intermediate fact. Simplify using `only [Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero, Finset.sum_ite_eq', he, if_true] at this`. Conclude with `this`.

Rewrite using `[homogeneousComponent_eq_zero, map_zero]`. Rewrite `he` using `[Finset.mem_range]`. Use linear arithmetic over natural numbers and integers. Introduce `h0`. Conclude with `Finset.sum_eq_zero fun e _ => by rw [h0, map_zero]`.
-/
theorem mem_ker_cone {o σ K : Type} [CommRing o] [Field K] (β : o →+* K) (u : σ → K)
    (F : MvPolynomial σ o) :
    F ∈ RingHom.ker (eval₂Hom ((Polynomial.C : K →+* Polynomial K).comp β)
      (fun a => Polynomial.C (u a) * Polynomial.X)) ↔
      ∀ e, eval₂Hom β u (homogeneousComponent e F) = 0 := by
  rw [RingHom.mem_ker]
  have h : eval₂Hom ((Polynomial.C : K →+* Polynomial K).comp β)
      (fun a => Polynomial.C (u a) * Polynomial.X) F =
      ∑ e ∈ Finset.range (F.totalDegree + 1),
        Polynomial.monomial e (eval₂Hom β u (homogeneousComponent e F)) := by
    conv_lhs => rw [← sum_homogeneousComponent F, map_sum]
    exact Finset.sum_congr rfl fun e _ => eval_cone β u (homogeneousComponent_isHomogeneous e F)
  rw [h]
  constructor
  · intro h0 e
    by_cases he : e ∈ Finset.range (F.totalDegree + 1)
    · have := congrArg (fun p => Polynomial.coeff p e) h0
      simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero,
        Finset.sum_ite_eq', he, if_true] at this
      exact this
    · rw [homogeneousComponent_eq_zero, map_zero]
      rw [Finset.mem_range] at he
      omega
  · intro h0
    exact Finset.sum_eq_zero fun e _ => by rw [h0, map_zero]

end HomogMinPrime

open HomogMinPrime in

/- English proof (translation)
Introduce `o σ K _ _ I β u i hI hu hmin`. Establish `hIφ : I ≤ RingHom.ker (MvPolynomial.eval₂Hom β u)` using `le_sup_left.trans hmin.1.2`. Use `⟨⟨RingHom.ker_isPrime _, fun F hF => (mem_ker_cone β u F).2 fun e => hIφ (hI F hF e)⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `Q ⟨hQ, hIQ⟩ hQψ`. Establish `hQφ : ∀ F ∈ Q, MvPolynomial.eval₂Hom β u F = 0`.

Introduce `F hF`. Use `(mem_ker_cone β u F).1 (hQψ hF)` as an intermediate fact. Rewrite using `[← MvPolynomial.sum_homogeneousComponent F, map_sum]`. Conclude with `Finset.sum_eq_zero fun e _ => this e`. Set `L` to `FractionRing (MvPolynomial σ o ⧸ Q)`.

Set `π : MvPolynomial σ o →+* L` to `(algebraMap (MvPolynomial σ o ⧸ Q) L).comp (Ideal.Quotient.mk Q)`. Establish `hπ : ∀ F, π F = 0 ↔ F ∈ Q`. Introduce `F`. Simplify using `only [π, RingHom.comp_apply]`. Rewrite using `[map_eq_zero_iff _ (IsFractionRing.injective _ L), Ideal.Quotient.eq_zero_iff_mem]`.

Establish `hx : π (MvPolynomial.X i) ≠ 0`. Introduce `h`. Use `hQφ _ ((hπ _).1 h)` as an intermediate fact. Rewrite `this` using `[MvPolynomial.eval₂Hom_X', hu]`. Conclude with `one_ne_zero this`.

Set `χ : MvPolynomial σ o →+* L` to `MvPolynomial.eval₂Hom (π.comp MvPolynomial.C) (fun a => π (MvPolynomial.X a) * (π (MvPolynomial.X i))⁻¹)`. Establish `hπe : MvPolynomial.eval₂Hom (π.comp MvPolynomial.C) (fun a => π (MvPolynomial.X a)) = π`. Apply the tactic sequence `apply MvPolynomial.ringHom_ext <;> simp`. Establish `hχ : ∀ (F : MvPolynomial σ o) e, χ (MvPolynomial.homogeneousComponent e F) = (π (MvPolynomial.X i))⁻¹ ^ e * π (MvPolynomial.homogeneousComponent e F)`. Introduce `F e`.

Use `eval_scale (π.comp MvPolynomial.C) (fun a => π (MvPolynomial.X a)) (π (MvPolynomial.X i))⁻¹ (MvPolynomial.homogeneousComponent_isHomogeneous e F)` as an intermediate fact. Rewrite `this` using `[hπe]`. Conclude with `this`. Establish `h1 : I ⊔ Ideal.span {MvPolynomial.X i - 1} ≤ RingHom.ker χ`. Use `sup_le (fun F hF => ?_) ?_` and prove the remaining obligations.

Rewrite using `[RingHom.mem_ker, ← MvPolynomial.sum_homogeneousComponent F, map_sum]`. Use `Finset.sum_eq_zero fun e _ => ?_` and prove the remaining obligations. Rewrite using `[hχ, (hπ _).2 (hIQ (hI F hF e)), mul_zero]`. Rewrite using `[Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, map_sub, map_one]`. Simplify using `only [χ, MvPolynomial.eval₂Hom_X']`.

Rewrite using `[mul_inv_cancel₀ hx, sub_self]`. Establish `h2 : RingHom.ker χ ≤ RingHom.ker (MvPolynomial.eval₂Hom β u)`. Introduce `F hF`. Rewrite `hF`, the goal using `[RingHom.mem_ker]`. Establish `hG : (∑ e ∈ Finset.range (F.totalDegree + 1), MvPolynomial.X i ^ (F.totalDegree - e) * MvPolynomial.homogeneousComponent e F) ∈ Q`.

Rewrite using `[← hπ, map_sum]`. Rewrite `hF` using `[← MvPolynomial.sum_homogeneousComponent F, map_sum]`. Use `congrArg (fun y => π (MvPolynomial.X i) ^ F.totalDegree * y) hF` as an intermediate fact. Simplify using `only [mul_zero, Finset.mul_sum] at this`. Rewrite using `[← this]`.

Use `Finset.sum_congr rfl fun e he => ?_` and prove the remaining obligations. Establish `he' : e ≤ F.totalDegree` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp he)`. Rewrite using `[hχ, map_mul, map_pow, pow_sub₀ _ hx he', inv_pow, _root_.mul_assoc]`. Use `hQφ _ hG` as an intermediate fact. Rewrite `this` using `[map_sum]`.

Rewrite using `[← MvPolynomial.sum_homogeneousComponent F, map_sum, ← this]`. Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, MvPolynomial.eval₂Hom_X', hu, one_pow, _root_.one_mul]`. Establish `h3` using `hmin.2 ⟨RingHom.ker_isPrime χ, h1⟩ h2`. Introduce `F hF`.

Rewrite `hF` using `[mem_ker_cone]`. Rewrite using `[← MvPolynomial.sum_homogeneousComponent F]`. Use `Q.sum_mem fun e _ => ?_` and prove the remaining obligations. Establish `h4 : χ (MvPolynomial.homogeneousComponent e F) = 0` using `h3 (hF e)`. Rewrite `h4` using `[hχ]`.

Conclude with `(hπ _).1 ((mul_eq_zero.1 h4).resolve_left (pow_ne_zero _ (inv_ne_zero hx)))`.
-/
theorem ker_cone_mem_minimalPrimes : ∀ (o σ K : Type) [CommRing o] [Field K] (I : Ideal (MvPolynomial σ o)) (β : o →+* K) (u : σ → K) (i : σ), (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) → u i = 1 → RingHom.ker (MvPolynomial.eval₂Hom β u) ∈ (I ⊔ Ideal.span {MvPolynomial.X i - 1}).minimalPrimes → RingHom.ker (MvPolynomial.eval₂Hom ((Polynomial.C : K →+* Polynomial K).comp β) (fun a => Polynomial.C (u a) * Polynomial.X)) ∈ I.minimalPrimes := by
  intro o σ K _ _ I β u i hI hu hmin
  have hIφ : I ≤ RingHom.ker (MvPolynomial.eval₂Hom β u) := le_sup_left.trans hmin.1.2
  refine ⟨⟨RingHom.ker_isPrime _, fun F hF => (mem_ker_cone β u F).2 fun e => hIφ (hI F hF e)⟩, ?_⟩
  rintro Q ⟨hQ, hIQ⟩ hQψ
  have hQφ : ∀ F ∈ Q, MvPolynomial.eval₂Hom β u F = 0 := by
    intro F hF
    have := (mem_ker_cone β u F).1 (hQψ hF)
    rw [← MvPolynomial.sum_homogeneousComponent F, map_sum]
    exact Finset.sum_eq_zero fun e _ => this e
  let L := FractionRing (MvPolynomial σ o ⧸ Q)
  let π : MvPolynomial σ o →+* L := (algebraMap (MvPolynomial σ o ⧸ Q) L).comp (Ideal.Quotient.mk Q)
  have hπ : ∀ F, π F = 0 ↔ F ∈ Q := by
    intro F
    simp only [π, RingHom.comp_apply]
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ L), Ideal.Quotient.eq_zero_iff_mem]
  have hx : π (MvPolynomial.X i) ≠ 0 := by
    intro h
    have := hQφ _ ((hπ _).1 h)
    rw [MvPolynomial.eval₂Hom_X', hu] at this
    exact one_ne_zero this
  let χ : MvPolynomial σ o →+* L := MvPolynomial.eval₂Hom (π.comp MvPolynomial.C)
    (fun a => π (MvPolynomial.X a) * (π (MvPolynomial.X i))⁻¹)
  have hπe : MvPolynomial.eval₂Hom (π.comp MvPolynomial.C) (fun a => π (MvPolynomial.X a)) = π := by
    apply MvPolynomial.ringHom_ext <;> simp
  have hχ : ∀ (F : MvPolynomial σ o) e, χ (MvPolynomial.homogeneousComponent e F) =
      (π (MvPolynomial.X i))⁻¹ ^ e * π (MvPolynomial.homogeneousComponent e F) := by
    intro F e
    have := eval_scale (π.comp MvPolynomial.C) (fun a => π (MvPolynomial.X a))
      (π (MvPolynomial.X i))⁻¹ (MvPolynomial.homogeneousComponent_isHomogeneous e F)
    rw [hπe] at this
    exact this
  have h1 : I ⊔ Ideal.span {MvPolynomial.X i - 1} ≤ RingHom.ker χ := by
    refine sup_le (fun F hF => ?_) ?_
    · rw [RingHom.mem_ker, ← MvPolynomial.sum_homogeneousComponent F, map_sum]
      refine Finset.sum_eq_zero fun e _ => ?_
      rw [hχ, (hπ _).2 (hIQ (hI F hF e)), mul_zero]
    · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, map_sub, map_one]
      simp only [χ, MvPolynomial.eval₂Hom_X']
      rw [mul_inv_cancel₀ hx, sub_self]
  have h2 : RingHom.ker χ ≤ RingHom.ker (MvPolynomial.eval₂Hom β u) := by
    intro F hF
    rw [RingHom.mem_ker] at hF ⊢
    have hG : (∑ e ∈ Finset.range (F.totalDegree + 1),
        MvPolynomial.X i ^ (F.totalDegree - e) * MvPolynomial.homogeneousComponent e F) ∈ Q := by
      rw [← hπ, map_sum]
      rw [← MvPolynomial.sum_homogeneousComponent F, map_sum] at hF
      have := congrArg (fun y => π (MvPolynomial.X i) ^ F.totalDegree * y) hF
      simp only [mul_zero, Finset.mul_sum] at this
      rw [← this]
      refine Finset.sum_congr rfl fun e he => ?_
      have he' : e ≤ F.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp he)
      rw [hχ, map_mul, map_pow, pow_sub₀ _ hx he', inv_pow, _root_.mul_assoc]
    have := hQφ _ hG
    rw [map_sum] at this
    rw [← MvPolynomial.sum_homogeneousComponent F, map_sum, ← this]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [map_mul, map_pow, MvPolynomial.eval₂Hom_X', hu, one_pow, _root_.one_mul]
  have h3 := hmin.2 ⟨RingHom.ker_isPrime χ, h1⟩ h2
  intro F hF
  rw [mem_ker_cone] at hF
  rw [← MvPolynomial.sum_homogeneousComponent F]
  refine Q.sum_mem fun e _ => ?_
  have h4 : χ (MvPolynomial.homogeneousComponent e F) = 0 := h3 (hF e)
  rw [hχ] at h4
  exact (hπ _).1 ((mul_eq_zero.1 h4).resolve_left (pow_ne_zero _ (inv_ne_zero hx)))

end GlobalTheory
