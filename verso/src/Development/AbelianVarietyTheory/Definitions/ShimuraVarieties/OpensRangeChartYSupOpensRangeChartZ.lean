import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.AwayLiftCompFromZeroRingHom

open AlgebraicGeometry CategoryTheory HomogeneousLocalization HomogeneousIdeal Limits

universe u

noncomputable section

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Rewrite using `[hp.degree_eq_sum_deg_support hd]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eval₂_smul_of_isHomogeneous {σ R A : Type*} [CommRing R] [CommRing A] (ρ : R →+* A)
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n) (c : A) (P : σ → A) :
    MvPolynomial.eval₂ ρ (c • P) p = c ^ n * MvPolynomial.eval₂ ρ P p := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [hp.degree_eq_sum_deg_support hd]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  ring

namespace WeierstrassCurve

attribute [local instance] MvPolynomial.gradedAlgebra

section Unimodular

variable {A B : Type*} [CommRing A] [CommRing B]

structure IsUnimodularSol (V : WeierstrassCurve A) (P : Fin 3 → A) : Prop where

  equation : V.toProjective.Equation P

  span_eq_top : Ideal.span (Set.range P) = ⊤

/- English proof (translation)
Assemble the required witnesses or components as `⟨h, Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) hi⟩`.
-/
theorem IsUnimodularSol.of_isUnit {V : WeierstrassCurve A} {P : Fin 3 → A}
    (h : V.toProjective.Equation P) (i : Fin 3) (hi : IsUnit (P i)) : IsUnimodularSol V P :=
  ⟨h, Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) hi⟩

/- English proof (translation)
The claim follows from `.of_isUnit WeierstrassCurve.Projective.equation_zero 1 isUnit_one`.
-/
theorem isUnimodularSol_zero (V : WeierstrassCurve A) : IsUnimodularSol V ![0, 1, 0] :=
  .of_isUnit WeierstrassCurve.Projective.equation_zero 1 isUnit_one

/- English proof (translation)
The claim follows from `.of_isUnit ((WeierstrassCurve.Projective.equation_some a b).mpr h) 2 isUnit_one`.
-/
theorem isUnimodularSol_some {V : WeierstrassCurve A} {a b : A} (h : V.toAffine.Equation a b) :
    IsUnimodularSol V ![a, b, 1] :=
  .of_isUnit ((WeierstrassCurve.Projective.equation_some a b).mpr h) 2 isUnit_one

/- English proof (translation)
Rewrite using `[WeierstrassCurve.Projective.equation_iff]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]`. Apply the tactic sequence `constructor <;> intro h <;> linear_combination h`.
-/
theorem equation_origin_iff (V : WeierstrassCurve A) (z w : A) :
    V.toProjective.Equation ![z, -1, w] ↔
      w = z ^ 3 + V.a₁ * z * w + V.a₂ * z ^ 2 * w + V.a₃ * w ^ 2 + V.a₄ * z * w ^ 2
        + V.a₆ * w ^ 3 := by
  rw [WeierstrassCurve.Projective.equation_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  constructor <;> intro h <;> linear_combination h

/- English proof (translation)
The claim follows from `.of_isUnit h 1 isUnit_one.neg`.
-/
theorem isUnimodularSol_origin {V : WeierstrassCurve A} {z w : A}
    (h : V.toProjective.Equation ![z, -1, w]) : IsUnimodularSol V ![z, -1, w] :=
  .of_isUnit h 1 isUnit_one.neg

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.equation.map g, by rw [Set.range_comp, ← Ideal.map_span, h.span_eq_top, Ideal.map_top]⟩`.
-/
theorem IsUnimodularSol.map {V : WeierstrassCurve A} {P : Fin 3 → A} (h : IsUnimodularSol V P)
    (g : A →+* B) : IsUnimodularSol (V.map g) (g ∘ P) :=
  ⟨h.equation.map g, by rw [Set.range_comp, ← Ideal.map_span, h.span_eq_top, Ideal.map_top]⟩

/- English proof (translation)
The claim follows from `h.map g`.
-/
theorem IsUnimodularSol.map_comp {R : Type*} [CommRing R] {W : WeierstrassCurve R} {ρ : R →+* A}
    {P : Fin 3 → A} (h : IsUnimodularSol (W.map ρ) P) (g : A →+* B) :
    IsUnimodularSol (W.map (g.comp ρ)) (g ∘ P) := h.map g

/- English proof (translation)
Use `h.map (g : A →+* B)` as an intermediate fact. Rewrite `this` using `[WeierstrassCurve.map_baseChange]`. Then use the resulting hypothesis.
-/
theorem IsUnimodularSol.baseChange {R : Type*} [CommRing R] [Algebra R A] [Algebra R B]
    {W : WeierstrassCurve R} {P : Fin 3 → A} (h : IsUnimodularSol (W.baseChange A) P)
    (g : A →ₐ[R] B) : IsUnimodularSol (W.baseChange B) (g ∘ P) := by
  have := h.map (g : A →+* B)
  rwa [WeierstrassCurve.map_baseChange] at this

/- English proof (translation)
The claim follows from `h`.
-/
theorem IsUnimodularSol.of_baseChange {R : Type*} [CommRing R] [Algebra R A]
    {W : WeierstrassCurve R} {P : Fin 3 → A} (h : IsUnimodularSol (W.baseChange A) P) :
    IsUnimodularSol (W.map (algebraMap R A)) P := h

/- English proof (translation)
Use `⟨(WeierstrassCurve.Projective.equation_smul P hc).mpr h.equation, ?_⟩` and prove the remaining obligations. Rewrite using `[_root_.eq_top_iff, ← h.span_eq_top, Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Take `⟨v, rfl⟩` from `hc`. Establish `: P i = (v⁻¹ : Aˣ) * ((v : A) • P) i` using `by simp`.

Rewrite using `[this]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)`.
-/
theorem IsUnimodularSol.smul {V : WeierstrassCurve A} {P : Fin 3 → A} (h : IsUnimodularSol V P)
    {c : A} (hc : IsUnit c) : IsUnimodularSol V (c • P) := by
  refine ⟨(WeierstrassCurve.Projective.equation_smul P hc).mpr h.equation, ?_⟩
  rw [_root_.eq_top_iff, ← h.span_eq_top, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨v, rfl⟩ := hc
  have : P i = (v⁻¹ : Aˣ) * ((v : A) • P) i := by simp
  rw [this]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

/- English proof (translation)
Use `⟨by rw [WeierstrassCurve.Projective.equation_iff]; simp, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.eq_top_iff_one]`. Establish `: (1 : ℤ) = (-2) * ![2, -5, 8] 0 + (-1) * ![2, -5, 8] 1` using `by simp`. Rewrite using `[this]`. Conclude with `add_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨0, rfl⟩)) (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨1, rfl⟩))`.
-/
example : IsUnimodularSol (⟨0, 0, 1, -1, 0⟩ : WeierstrassCurve ℤ) ![2, -5, 8] := by
  refine ⟨by rw [WeierstrassCurve.Projective.equation_iff]; simp, ?_⟩
  rw [Ideal.eq_top_iff_one]
  have : (1 : ℤ) = (-2) * ![2, -5, 8] 0 + (-1) * ![2, -5, 8] 1 := by simp
  rw [this]
  exact add_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨0, rfl⟩))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨1, rfl⟩))

/- English proof (translation)
Introduce `h`. Establish `h2 : Ideal.span (Set.range ![(0 : ℤ), 2, 0]) ≤ Ideal.span {2}`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Apply the tactic sequence `fin_cases i <;> simp`.

Rewrite `h2` using `[h.span_eq_top, top_le_iff, Ideal.span_singleton_eq_top, Int.isUnit_iff]`. Use linear arithmetic over natural numbers and integers.
-/
example (V : WeierstrassCurve ℤ) : ¬ IsUnimodularSol V ![0, 2, 0] := by
  intro h
  have h2 : Ideal.span (Set.range ![(0 : ℤ), 2, 0]) ≤ Ideal.span {2} := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> simp
  rw [h.span_eq_top, top_le_iff, Ideal.span_singleton_eq_top, Int.isUnit_iff] at h2
  omega

end Unimodular

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/- English proof (translation)
Establish `hX` using `fun i : Fin 3 => MvPolynomial.isHomogeneous_X R i`. Establish `hC` using `fun r : R => MvPolynomial.isHomogeneous_C (Fin 3) r`. Rewrite using `[WeierstrassCurve.Projective.polynomial]`. Use `.sub (.add (.add ?_ ?_) ?_) (.add (.add (.add ?_ ?_) ?_) ?_)` and prove the remaining obligations. Conclude with `((hX 1).pow 2).mul (hX 2)`.

Conclude with `(((hC _).mul (hX 0)).mul (hX 1)).mul (hX 2)`. Conclude with `((hC _).mul (hX 1)).mul ((hX 2).pow 2)`. Conclude with `(hX 0).pow 3`. Conclude with `((hC _).mul ((hX 0).pow 2)).mul (hX 2)`. Conclude with `((hC _).mul (hX 0)).mul ((hX 2).pow 2)`.

Conclude with `(hC _).mul ((hX 2).pow 3)`.
-/
theorem isHomogeneous_polynomial : W.toProjective.polynomial.IsHomogeneous 3 := by
  have hX := fun i : Fin 3 => MvPolynomial.isHomogeneous_X R i
  have hC := fun r : R => MvPolynomial.isHomogeneous_C (Fin 3) r
  rw [WeierstrassCurve.Projective.polynomial]
  refine .sub (.add (.add ?_ ?_) ?_) (.add (.add (.add ?_ ?_) ?_) ?_)
  · exact ((hX 1).pow 2).mul (hX 2)
  · exact (((hC _).mul (hX 0)).mul (hX 1)).mul (hX 2)
  · exact ((hC _).mul (hX 1)).mul ((hX 2).pow 2)
  · exact (hX 0).pow 3
  · exact ((hC _).mul ((hX 0).pow 2)).mul (hX 2)
  · exact ((hC _).mul (hX 0)).mul ((hX 2).pow 2)
  · exact (hC _).mul ((hX 2).pow 3)

def cubicIdeal : Ideal (MvPolynomial (Fin 3) R) := Ideal.span {W.toProjective.polynomial}

/- English proof (translation)
The claim follows from `Ideal.homogeneous_span _ _ (by rintro _ rfl; exact ⟨3, isHomogeneous_polynomial W⟩)`.
-/
theorem isHomogeneous_cubicIdeal :
    (cubicIdeal W).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) R) :=
  Ideal.homogeneous_span _ _ (by rintro _ rfl; exact ⟨3, isHomogeneous_polynomial W⟩)

abbrev HomRing : Type u := MvPolynomial (Fin 3) R ⧸ cubicIdeal W

def grading : ℕ → Submodule R (HomRing W) :=
  quotGrading (MvPolynomial.homogeneousSubmodule (Fin 3) R) (cubicIdeal W)

instance gradedAlgebra : GradedAlgebra (grading W) :=
  quotGradedAlgebra _ (isHomogeneous_cubicIdeal W)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_grading_iff {n : ℕ} {a : HomRing W} :
    a ∈ grading W n ↔ ∃ p : MvPolynomial (Fin 3) R, p.IsHomogeneous n ∧
      Ideal.Quotient.mk _ p = a := Iff.rfl

def coord (i : Fin 3) : HomRing W := Ideal.Quotient.mk _ (MvPolynomial.X i)

/- English proof (translation)
Assemble the required witnesses or components as `⟨_, MvPolynomial.isHomogeneous_X R i, rfl⟩`.
-/
theorem coord_mem (i : Fin 3) : coord W i ∈ grading W 1 :=
  ⟨_, MvPolynomial.isHomogeneous_X R i, rfl⟩

/- English proof (translation)
The claim follows from `Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext h₀ h₁)`.
-/
theorem homRing_hom_ext {A : Type*} [CommRing A] {f g : HomRing W →+* A}
    (h₀ : ∀ r : R, f (algebraMap R _ r) = g (algebraMap R _ r))
    (h₁ : ∀ i, f (coord W i) = g (coord W i)) : f = g :=
  Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext h₀ h₁)

/- English proof (translation)
Establish `: MvPolynomial.eval₂Hom (algebraMap R (HomRing W)) (coord W) = Ideal.Quotient.mk _` using `MvPolynomial.ringHom_ext (fun r => by simp; rfl) (fun i => by simp [coord])`. Express the relevant statement in the definitionally equal form `(W.toProjective.map _).Equation _`. Rewrite using `[WeierstrassCurve.Projective.Equation, WeierstrassCurve.Projective.map_polynomial, MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom, this, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.subset_span rfl`.
-/
theorem equation_coord : (W.baseChange (HomRing W)).toProjective.Equation (coord W) := by
  have : MvPolynomial.eval₂Hom (algebraMap R (HomRing W)) (coord W) = Ideal.Quotient.mk _ :=
    MvPolynomial.ringHom_ext (fun r => by simp; rfl) (fun i => by simp [coord])
  change (W.toProjective.map _).Equation _
  rw [WeierstrassCurve.Projective.Equation, WeierstrassCurve.Projective.map_polynomial,
    MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom, this, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[toIdeal_irrelevant_le]`. Introduce and unpack `n hn _ ⟨p, hp, rfl⟩`. Establish `hp' : p ∈ Ideal.span (MvPolynomial.X '' (Set.univ : Set (Fin 3)))`. Rewrite using `[MvPolynomial.mem_ideal_span_X_image]`.

Introduce `m hm`. Use `by_contra! h`. Establish `hm0 : m = 0` using `Finsupp.ext fun i => h i trivial`. Use `MvPolynomial.IsHomogeneous.degree_eq_sum_deg_support hp hm` as an intermediate fact. Simplify using `[hm0] at this`.

Use linear arithmetic over natural numbers and integers. Use `Ideal.mem_map_of_mem (Ideal.Quotient.mk (cubicIdeal W)) hp'` as an intermediate fact. Rewrite `this` using `[Ideal.map_span, Set.image_univ, ← Set.range_comp]`. Then use the resulting hypothesis. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Conclude with `mem_irrelevant_of_mem _ one_pos (coord_mem W i)`.
-/
theorem irrelevant_eq_span_coord :
    (irrelevant (grading W)).toIdeal = Ideal.span (Set.range (coord W)) := by
  apply le_antisymm
  · rw [toIdeal_irrelevant_le]
    rintro n hn _ ⟨p, hp, rfl⟩
    have hp' : p ∈ Ideal.span (MvPolynomial.X '' (Set.univ : Set (Fin 3))) := by
      rw [MvPolynomial.mem_ideal_span_X_image]
      intro m hm
      by_contra! h
      have hm0 : m = 0 := Finsupp.ext fun i => h i trivial
      have := MvPolynomial.IsHomogeneous.degree_eq_sum_deg_support hp hm
      simp [hm0] at this
      omega
    have := Ideal.mem_map_of_mem (Ideal.Quotient.mk (cubicIdeal W)) hp'
    rwa [Ideal.map_span, Set.image_univ, ← Set.range_comp] at this
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact mem_irrelevant_of_mem _ one_pos (coord_mem W i)

section Eval

variable {A B : Type*} [CommRing A] [CommRing B]

def evalHom (ρ : R →+* A) (P : Fin 3 → A) (h : (W.map ρ).toProjective.Equation P) :
    HomRing W →+* A :=
  Ideal.Quotient.lift _ (MvPolynomial.eval₂Hom ρ P) (by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    change (W.toProjective.map _).Equation _ at h
    rw [WeierstrassCurve.Projective.Equation, WeierstrassCurve.Projective.map_polynomial,
      MvPolynomial.eval_map] at h
    rw [map_mul, MvPolynomial.coe_eval₂Hom, h, mul_zero])

variable (ρ : R →+* A) (P : Fin 3 → A) (h : (W.map ρ).toProjective.Equation P)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evalHom_mk (p : MvPolynomial (Fin 3) R) :
    evalHom W ρ P h (Ideal.Quotient.mk _ p) = MvPolynomial.eval₂ ρ P p := rfl

/- English proof (translation)
The claim follows from `MvPolynomial.eval₂_X ..`.
-/
@[simp] theorem evalHom_coord (i : Fin 3) : evalHom W ρ P h (coord W i) = P i :=
  MvPolynomial.eval₂_X ..

/- English proof (translation)
The claim follows from `MvPolynomial.eval₂_C ..`.
-/
@[simp] theorem evalHom_algebraMap (r : R) : evalHom W ρ P h (algebraMap R _ r) = ρ r :=
  MvPolynomial.eval₂_C ..

/- English proof (translation)
The claim follows from `homRing_hom_ext W (fun _ => (congrArg g (evalHom_algebraMap ..)).trans (evalHom_algebraMap W (g.comp ρ) ..).symm) (fun _ => (congrArg g (evalHom_coord ..)).trans (evalHom_coord W (g.comp ρ) (g ∘ P) ..).symm)`.
-/
theorem comp_evalHom (g : A →+* B) :
    g.comp (evalHom W ρ P h) = evalHom W (g.comp ρ) (g ∘ P) (h.map g) :=
  homRing_hom_ext W
    (fun _ => (congrArg g (evalHom_algebraMap ..)).trans (evalHom_algebraMap W (g.comp ρ) ..).symm)
    (fun _ => (congrArg g (evalHom_coord ..)).trans (evalHom_coord W (g.comp ρ) (g ∘ P) ..).symm)

/- English proof (translation)
Take `⟨p, hp, rfl⟩` from `ha`. Conclude with `eval₂_smul_of_isHomogeneous ρ hp c P`.
-/
theorem evalHom_smul (c : A) (h' : (W.map ρ).toProjective.Equation (c • P)) {n : ℕ}
    {a : HomRing W} (ha : a ∈ grading W n) :
    evalHom W ρ (c • P) h' a = c ^ n * evalHom W ρ P h a := by
  obtain ⟨p, hp, rfl⟩ := ha
  exact eval₂_smul_of_isHomogeneous ρ hp c P

variable {ρ P} in

/- English proof (translation)
Rewrite using `[irrelevant_eq_span_coord, Ideal.map_span, ← Set.range_comp, ← h.span_eq_top]`. Use `congr 2`. Use extensionality with `i`. Simplify using the standard rewrite rules.
-/
theorem map_irrelevant_evalHom (h : IsUnimodularSol (W.map ρ) P) :
    (irrelevant (grading W)).toIdeal.map (evalHom W ρ P h.equation) = ⊤ := by
  rw [irrelevant_eq_span_coord, Ideal.map_span, ← Set.range_comp, ← h.span_eq_top]
  congr 2
  ext i
  simp

end Eval

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `r s hrs`. Use `congrArg (fun a : grading W 0 => evalHom W (RingHom.id R) ![0, 1, 0] WeierstrassCurve.Projective.equation_zero (a : HomRing W)) hrs` as an intermediate fact. Simplify using `using this`. Introduce and unpack `⟨_, p, hp, rfl⟩`.

Rewrite `hp` using `[MvPolynomial.homogeneousSubmodule_zero]`. Take `⟨r, rfl⟩` from `Submodule.mem_one.mp hp`. Conclude with `⟨r, rfl⟩`.
-/
theorem bijective_algebraMap_grading_zero : Function.Bijective (algebraMap R (grading W 0)) := by
  constructor
  · intro r s hrs
    have := congrArg (fun a : grading W 0 => evalHom W (RingHom.id R) ![0, 1, 0]
      WeierstrassCurve.Projective.equation_zero (a : HomRing W)) hrs
    simpa using this
  · rintro ⟨_, p, hp, rfl⟩
    rw [MvPolynomial.homogeneousSubmodule_zero] at hp
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hp
    exact ⟨r, rfl⟩

def scheme : Scheme.{u} := Proj (grading W)

def toSpec : scheme W ⟶ Spec (.of R) :=
  Proj.toSpecZero (grading W) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (grading W 0)))

instance : (scheme W).Over (Spec (.of R)) := ⟨toSpec W⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem over_eq_toSpec : scheme W ↘ Spec (.of R) = toSpec W := rfl

abbrev schemeOver : Over (Spec (.of R)) := Over.mk (toSpec W)

def coordOpen (i : Fin 3) : (scheme W).Opens := Proj.basicOpen (grading W) (coord W i)

/- English proof (translation)
Use `top_le_iff.mp fun x _ => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hx`. Establish `h1 : coord W 1 ∈ x.asHomogeneousIdeal.toIdeal`. Assume the negation of the conclusion as `h`. Conclude with `hx (Or.inl h)`.

Establish `h2 : coord W 2 ∈ x.asHomogeneousIdeal.toIdeal`. Assume the negation of the conclusion as `h`. Conclude with `hx (Or.inr h)`. Establish `h0 : coord W 0 ∈ x.asHomogeneousIdeal.toIdeal`. Use `x.isPrime.mem_of_pow_mem 3 ?_` and prove the remaining obligations.

Establish `e` using `(WeierstrassCurve.Projective.equation_iff _).mp (equation_coord W)`. Use `set V := W.baseChange (HomRing W)`. Establish `: coord W 0 ^ 3 = (coord W 1 ^ 2 + V.a₁ * coord W 0 * coord W 1 + V.a₃ * coord W 1 * coord W 2 - (V.a₂ * coord W 0 ^ 2 + V.a₄ * coord W 0 * coord W 2 + V.a₆ * coord W 2 ^ 2)) * coord W 2` using `by linear_combination -e`. Rewrite using `[this]`. Conclude with `Ideal.mul_mem_left _ _ h2`.

Use `x.not_irrelevant_le (toIdeal_le_toIdeal_iff.mp ?_)` and prove the remaining obligations. Rewrite using `[irrelevant_eq_span_coord, Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Apply the tactic sequence `fin_cases i <;> assumption`.
-/
theorem coordOpen_one_sup_coordOpen_two : coordOpen W 1 ⊔ coordOpen W 2 = ⊤ := by
  refine top_le_iff.mp fun x _ => ?_
  by_contra hx
  have h1 : coord W 1 ∈ x.asHomogeneousIdeal.toIdeal := by
    by_contra h
    exact hx (Or.inl h)
  have h2 : coord W 2 ∈ x.asHomogeneousIdeal.toIdeal := by
    by_contra h
    exact hx (Or.inr h)
  have h0 : coord W 0 ∈ x.asHomogeneousIdeal.toIdeal := by
    refine x.isPrime.mem_of_pow_mem 3 ?_
    have e := (WeierstrassCurve.Projective.equation_iff _).mp (equation_coord W)
    set V := W.baseChange (HomRing W)
    have : coord W 0 ^ 3 = (coord W 1 ^ 2 + V.a₁ * coord W 0 * coord W 1
        + V.a₃ * coord W 1 * coord W 2 - (V.a₂ * coord W 0 ^ 2 + V.a₄ * coord W 0 * coord W 2
        + V.a₆ * coord W 2 ^ 2)) * coord W 2 := by linear_combination -e
    rw [this]
    exact Ideal.mul_mem_left _ _ h2
  refine x.not_irrelevant_le (toIdeal_le_toIdeal_iff.mp ?_)
  rw [irrelevant_eq_span_coord, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i <;> assumption

section Points

variable {A B : Type u} [CommRing A] [CommRing B]

def ptHom (ρ : R →+* A) (P : Fin 3 → A) (h : IsUnimodularSol (W.map ρ) P) :
    Spec (.of A) ⟶ scheme W :=
  ProjPoint.ofHom (grading W) (evalHom W ρ P h.equation) (map_irrelevant_evalHom W h)

section

variable (ρ : R →+* A) (P : Fin 3 → A) (h : IsUnimodularSol (W.map ρ) P)

@[reassoc (attr := simp)]
/- English proof (translation)
Use `(ProjPoint.ofHom_toSpecZero_assoc (grading W) _ _ _).trans ?_` and prove the remaining obligations. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Use extensionality with `r`. Conclude with `evalHom_algebraMap W ρ P h.equation r`.

Use the proof step `@[reassoc]`.
-/
theorem ptHom_toSpec : ptHom W ρ P h ≫ toSpec W = Spec.map (CommRingCat.ofHom ρ) := by
  refine (ProjPoint.ofHom_toSpecZero_assoc (grading W) _ _ _).trans ?_
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  exact evalHom_algebraMap W ρ P h.equation r

@[reassoc]
/- English proof (translation)
Use `(ProjPoint.SpecMap_ofHom (grading W) _ _ _).trans ?_` and prove the remaining obligations. Simplify using `only [comp_evalHom]`. Both sides reduce to the same expression.
-/
theorem SpecMap_ptHom (g : A →+* B) :
    Spec.map (CommRingCat.ofHom g) ≫ ptHom W ρ P h =
      ptHom W (g.comp ρ) (g ∘ P) (h.map_comp g) := by
  refine (ProjPoint.SpecMap_ofHom (grading W) _ _ _).trans ?_
  simp only [comp_evalHom]
  rfl

/- English proof (translation)
The claim follows from `ProjPoint.ofHom_eq_of_scale (grading W) _ _ c fun _ _ ha => evalHom_smul W ρ P _ c _ ha`.
-/
theorem ptHom_smul {c : A} (hc : IsUnit c) : ptHom W ρ (c • P) (h.smul hc) = ptHom W ρ P h :=
  ProjPoint.ofHom_eq_of_scale (grading W) _ _ c fun _ _ ha => evalHom_smul W ρ P _ c _ ha

/- English proof (translation)
The claim follows from `(ProjPoint.ofHom_preimage_basicOpen (grading W) _ _ one_pos (coord_mem W i)).trans (by rw [evalHom_coord])`.
-/
theorem ptHom_preimage_coordOpen (i : Fin 3) :
    ptHom W ρ P h ⁻¹ᵁ coordOpen W i = PrimeSpectrum.basicOpen (P i) :=
  (ProjPoint.ofHom_preimage_basicOpen (grading W) _ _ one_pos (coord_mem W i)).trans
    (by rw [evalHom_coord])

/- English proof (translation)
Substitute `hρ hP` using the available equality. Both sides reduce to the same expression.
-/
theorem ptHom_congr {ρ' : R →+* A} {P' : Fin 3 → A} (hρ : ρ = ρ') (hP : P = P')
    (h' : IsUnimodularSol (W.map ρ') P') : ptHom W ρ P h = ptHom W ρ' P' h' := by
  subst hρ hP
  rfl

end

variable [Algebra R A] [Algebra R B]

def pt (P : Fin 3 → A) (h : IsUnimodularSol (W.baseChange A) P) : Spec (.of A) ⟶ scheme W :=
  ptHom W (algebraMap R A) P h

variable (P : Fin 3 → A) (h : IsUnimodularSol (W.baseChange A) P)

/- English proof (translation)
The claim follows from `rfl @[reassoc (attr := simp)]`.
-/
theorem pt_eq_ptHom : pt W P h = ptHom W (algebraMap R A) P h.of_baseChange := rfl

@[reassoc (attr := simp)]
/- English proof (translation)
The claim follows from `ptHom_toSpec .. @[reassoc]`.
-/
theorem pt_toSpec : pt W P h ≫ toSpec W = Spec.map (CommRingCat.ofHom (algebraMap R A)) :=
  ptHom_toSpec ..

@[reassoc]
/- English proof (translation)
The claim follows from `(SpecMap_ptHom W (algebraMap R A) P h (g : A →+* B)).trans (ptHom_congr W _ _ _ g.comp_algebraMap rfl (h.baseChange g))`.
-/
theorem SpecMap_pt (g : A →ₐ[R] B) :
    Spec.map (CommRingCat.ofHom (g : A →+* B)) ≫ pt W P h = pt W (g ∘ P) (h.baseChange g) :=
  (SpecMap_ptHom W (algebraMap R A) P h (g : A →+* B)).trans
    (ptHom_congr W _ _ _ g.comp_algebraMap rfl (h.baseChange g))

/- English proof (translation)
The claim follows from `ptHom_smul W _ P h hc`.
-/
theorem pt_smul {c : A} (hc : IsUnit c) : pt W (c • P) (h.smul hc) = pt W P h :=
  ptHom_smul W _ P h hc

/- English proof (translation)
The claim follows from `ptHom_preimage_coordOpen ..`.
-/
theorem pt_preimage_coordOpen (i : Fin 3) :
    pt W P h ⁻¹ᵁ coordOpen W i = PrimeSpectrum.basicOpen (P i) :=
  ptHom_preimage_coordOpen ..

def ptOver : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶ schemeOver W :=
  Over.homMk (pt W P h) (pt_toSpec W P h)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem ptOver_left : (ptOver W P h).left = pt W P h := rfl

/- English proof (translation)
Substitute `hP` using the available equality. Both sides reduce to the same expression.
-/
theorem pt_congr {P' : Fin 3 → A} (hP : P = P') (h' : IsUnimodularSol (W.baseChange A) P') :
    pt W P h = pt W P' h' := by
  subst hP
  rfl

end Points

def zero : Spec (.of R) ⟶ scheme W := pt W (A := R) ![0, 1, 0] (isUnimodularSol_zero _)

@[reassoc (attr := simp)]
/- English proof (translation)
Rewrite using `[zero, pt_toSpec]`. Conclude with `Spec.map_id _`. Use the proof step `@[reassoc]`.
-/
theorem zero_toSpec : zero W ≫ toSpec W = 𝟙 _ := by
  rw [zero, pt_toSpec]
  exact Spec.map_id _

@[reassoc]
/- English proof (translation)
The claim follows from `(SpecMap_ptHom W (algebraMap R R) ![0, 1, 0] (isUnimodularSol_zero _) ρ).trans (ptHom_congr W _ _ _ (RingHom.comp_id ρ) (by ext i; fin_cases i <;> simp) _) @[reassoc]`.
-/
theorem SpecMap_zero {A : Type u} [CommRing A] (ρ : R →+* A) :
    Spec.map (CommRingCat.ofHom ρ) ≫ zero W =
      ptHom W ρ ![0, 1, 0] (isUnimodularSol_zero _) :=
  (SpecMap_ptHom W (algebraMap R R) ![0, 1, 0] (isUnimodularSol_zero _) ρ).trans
    (ptHom_congr W _ _ _ (RingHom.comp_id ρ) (by ext i; fin_cases i <;> simp) _)

@[reassoc]
/- English proof (translation)
The claim follows from `SpecMap_zero W _`.
-/
theorem SpecMap_algebraMap_zero (A : Type u) [CommRing A] [Algebra R A] :
    Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ zero W =
      pt W (A := A) ![0, 1, 0] (isUnimodularSol_zero _) :=
  SpecMap_zero W _

/- English proof (translation)
Rewrite using `[zero, pt_preimage_coordOpen]`. Conclude with `PrimeSpectrum.basicOpen_zero`.
-/
theorem zero_preimage_coordOpen_two : zero W ⁻¹ᵁ coordOpen W 2 = ⊥ := by
  rw [zero, pt_preimage_coordOpen]
  exact PrimeSpectrum.basicOpen_zero

/- English proof (translation)
Rewrite using `[zero, pt_preimage_coordOpen]`. Conclude with `PrimeSpectrum.basicOpen_one`.
-/
theorem zero_preimage_coordOpen_one : zero W ⁻¹ᵁ coordOpen W 1 = ⊤ := by
  rw [zero, pt_preimage_coordOpen]
  exact PrimeSpectrum.basicOpen_one

section Away

variable (i : Fin 3)

abbrev AwayRing : Type u := Away (grading W) (coord W i)

def awayConst : R →+* AwayRing W i :=
  (fromZeroRingHom (grading W) _).comp (algebraMap R (grading W 0))

def awayCoord (j : Fin 3) : AwayRing W i :=
  Away.mk (grading W) (coord_mem W i) 1 (coord W j) (coord_mem W j)

/- English proof (translation)
Use `ext`. Simplify using `[awayCoord]`.
-/
@[simp] theorem awayCoord_self : awayCoord W i i = 1 := by
  ext
  simp [awayCoord]

/- English proof (translation)
Use extensionality with `r`. Express the relevant statement in the definitionally equal form `algebraMap (AwayRing W i) _ (algebraMap (grading W 0) _ _) = _`. Rewrite using `[← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (grading W 0) (HomRing W)]`. Both sides reduce to the same expression.
-/
theorem algebraMap_comp_awayConst :
    (algebraMap (AwayRing W i) (Localization.Away (coord W i))).comp (awayConst W i) =
      (algebraMap (HomRing W) _).comp (algebraMap R (HomRing W)) := by
  ext r
  change algebraMap (AwayRing W i) _ (algebraMap (grading W 0) _ _) = _
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (grading W 0) (HomRing W)]
  rfl

/- English proof (translation)
Use extensionality with `j`. Simplify using `only [Function.comp_apply, awayCoord, HomogeneousLocalization.algebraMap_apply, Away.val_mk, Pi.smul_apply, smul_eq_mul, Localization.mk_eq_mk', IsLocalization.Away.invSelf]`. Rewrite using `[IsLocalization.mk'_eq_mul_mk'_one, mul_comm]`. Simplify using the standard rewrite rules.
-/
theorem algebraMap_comp_awayCoord :
    algebraMap (AwayRing W i) (Localization.Away (coord W i)) ∘ awayCoord W i =
      (IsLocalization.Away.invSelf (coord W i) : Localization.Away (coord W i)) •
        (algebraMap (HomRing W) _ ∘ coord W) := by
  ext j
  simp only [Function.comp_apply, awayCoord, HomogeneousLocalization.algebraMap_apply,
    Away.val_mk, Pi.smul_apply, smul_eq_mul, Localization.mk_eq_mk', IsLocalization.Away.invSelf]
  rw [IsLocalization.mk'_eq_mul_mk'_one, mul_comm]
  simp

/- English proof (translation)
The claim follows from `IsUnit.of_mul_eq_one_right _ (IsLocalization.Away.mul_invSelf (coord W i))`.
-/
private theorem isUnit_invSelf :
    IsUnit (IsLocalization.Away.invSelf (coord W i) : Localization.Away (coord W i)) :=
  IsUnit.of_mul_eq_one_right _ (IsLocalization.Away.mul_invSelf (coord W i))

/- English proof (translation)
Rewrite using `[← WeierstrassCurve.Projective.map_equation _ (f := algebraMap (AwayRing W i) (Localization.Away (coord W i))) (val_injective _)]`. Establish `e` using `WeierstrassCurve.map_map W (awayConst W i) (algebraMap (AwayRing W i) (Localization.Away (coord W i)))`. Simplify using `only [WeierstrassCurve.Projective.map, WeierstrassCurve.toProjective]`. Rewrite using `[e, algebraMap_comp_awayConst, algebraMap_comp_awayCoord, WeierstrassCurve.Projective.equation_smul _ (isUnit_invSelf W i)]`. Conclude with `WeierstrassCurve.Projective.Equation.map (W' := (W.map (algebraMap R (HomRing W))).toProjective) (algebraMap (HomRing W) (Localization.Away (coord W i))) (equation_coord W)`.
-/
theorem equation_awayCoord : (W.map (awayConst W i)).toProjective.Equation (awayCoord W i) := by
  rw [← WeierstrassCurve.Projective.map_equation _
    (f := algebraMap (AwayRing W i) (Localization.Away (coord W i))) (val_injective _)]
  have e := WeierstrassCurve.map_map W (awayConst W i)
    (algebraMap (AwayRing W i) (Localization.Away (coord W i)))
  simp only [WeierstrassCurve.Projective.map, WeierstrassCurve.toProjective]
  rw [e, algebraMap_comp_awayConst, algebraMap_comp_awayCoord,
    WeierstrassCurve.Projective.equation_smul _ (isUnit_invSelf W i)]
  exact WeierstrassCurve.Projective.Equation.map
    (W' := (W.map (algebraMap R (HomRing W))).toProjective)
    (algebraMap (HomRing W) (Localization.Away (coord W i))) (equation_coord W)

/- English proof (translation)
The claim follows from `.of_isUnit (equation_awayCoord W i) i (by simp)`.
-/
theorem isUnimodularSol_awayCoord : IsUnimodularSol (W.map (awayConst W i)) (awayCoord W i) :=
  .of_isUnit (equation_awayCoord W i) i (by simp)

/- English proof (translation)
Take `⟨p, hp, rfl⟩` from `id ha`. Apply `val_injective` to reduce the goal to its premises. Establish `hp' : p.IsHomogeneous n` using `by simpa using hp`. Express the relevant statement in the definitionally equal form `algebraMap (AwayRing W i) (Localization.Away (coord W i)) (MvPolynomial.eval₂ _ _ p) = _`. Establish `e : MvPolynomial.eval₂ (algebraMap R (HomRing W)) (coord W) p = Ideal.Quotient.mk _ p` using `RingHom.congr_fun (homRing_hom_ext W (f := evalHom W (algebraMap R (HomRing W)) (coord W) (equation_coord W)) (g := RingHom.id _) (fun r => evalHom_algebraMap ..) (fun j => evalHom_coord ..)) (Ideal.Quotient.mk _ p)`.

Rewrite using `[MvPolynomial.eval₂_comp_left, algebraMap_comp_awayConst, algebraMap_comp_awayCoord, eval₂_smul_of_isHomogeneous _ hp', ← MvPolynomial.eval₂_comp_left, e, Away.val_mk, Localization.mk_eq_mk', IsLocalization.eq_mk'_iff_mul_eq]`. Express the relevant statement in the definitionally equal form `_ * algebraMap _ _ (coord W i ^ n) = algebraMap _ _ (Ideal.Quotient.mk _ p)`. Rewrite using `[map_pow, mul_right_comm, ← mul_pow, mul_comm _ (algebraMap _ _ (coord W i)), IsLocalization.Away.mul_invSelf, one_pow, one_mul]`.
-/
theorem evalHom_awayCoord (n : ℕ) (a : HomRing W) (ha : a ∈ grading W (n • 1)) :
    evalHom W (awayConst W i) (awayCoord W i) (equation_awayCoord W i) a =
      Away.mk (grading W) (coord_mem W i) n a ha := by
  obtain ⟨p, hp, rfl⟩ := id ha
  apply val_injective
  have hp' : p.IsHomogeneous n := by simpa using hp
  change algebraMap (AwayRing W i) (Localization.Away (coord W i))
    (MvPolynomial.eval₂ _ _ p) = _
  have e : MvPolynomial.eval₂ (algebraMap R (HomRing W)) (coord W) p = Ideal.Quotient.mk _ p :=
    RingHom.congr_fun (homRing_hom_ext W
      (f := evalHom W (algebraMap R (HomRing W)) (coord W) (equation_coord W)) (g := RingHom.id _)
      (fun r => evalHom_algebraMap ..) (fun j => evalHom_coord ..)) (Ideal.Quotient.mk _ p)
  rw [MvPolynomial.eval₂_comp_left, algebraMap_comp_awayConst, algebraMap_comp_awayCoord,
    eval₂_smul_of_isHomogeneous _ hp', ← MvPolynomial.eval₂_comp_left, e, Away.val_mk,
    Localization.mk_eq_mk', IsLocalization.eq_mk'_iff_mul_eq]
  change _ * algebraMap _ _ (coord W i ^ n) = algebraMap _ _ (Ideal.Quotient.mk _ p)
  rw [map_pow, mul_right_comm, ← mul_pow, mul_comm _ (algebraMap _ _ (coord W i)),
    IsLocalization.Away.mul_invSelf, one_pow, one_mul]

variable {A : Type u} [CommRing A]

/- English proof (translation)
Use extensionality with `x`. Take `⟨n, a, ha, rfl⟩` from `Away.mk_surjective (grading W) (coord_mem W i) x`. Rewrite using `[← evalHom_awayCoord]`. Conclude with `RingHom.congr_fun (homRing_hom_ext W (f := f.comp (evalHom W _ _ (equation_awayCoord W i))) (g := g.comp (evalHom W _ _ (equation_awayCoord W i))) (fun r => by simpa using h₀ r) (fun j => by simpa using h₁ j)) a`.
-/
theorem awayRing_hom_ext {A : Type*} [CommRing A] {f g : AwayRing W i →+* A}
    (h₀ : ∀ r : R, f (awayConst W i r) = g (awayConst W i r))
    (h₁ : ∀ j, f (awayCoord W i j) = g (awayCoord W i j)) : f = g := by
  ext x
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (grading W) (coord_mem W i) x
  rw [← evalHom_awayCoord]
  exact RingHom.congr_fun (homRing_hom_ext W
    (f := f.comp (evalHom W _ _ (equation_awayCoord W i)))
    (g := g.comp (evalHom W _ _ (equation_awayCoord W i)))
    (fun r => by simpa using h₀ r) (fun j => by simpa using h₁ j)) a

def awayEval (ρ : R →+* A) (P : Fin 3 → A) (h : (W.map ρ).toProjective.Equation P)
    (hi : IsUnit (P i)) : AwayRing W i →+* A :=
  ProjPoint.awayLift (grading W) (evalHom W ρ P h) (coord W i) (by rwa [evalHom_coord])

variable (ρ : R →+* A) (P : Fin 3 → A)

/- English proof (translation)
The claim follows from `(RingHom.congr_fun (ProjPoint.awayLift_comp_fromZeroRingHom (grading W) (evalHom W ρ P h) (coord W i) (by rwa [evalHom_coord])) (algebraMap R (grading W 0) r)).trans (evalHom_algebraMap W ρ P h r)`.
-/
@[simp] theorem awayEval_awayConst (h : (W.map ρ).toProjective.Equation P) (hi : IsUnit (P i))
    (r : R) : awayEval W i ρ P h hi (awayConst W i r) = ρ r :=
  (RingHom.congr_fun (ProjPoint.awayLift_comp_fromZeroRingHom (grading W) (evalHom W ρ P h)
    (coord W i) (by rwa [evalHom_coord])) (algebraMap R (grading W 0) r)).trans
    (evalHom_algebraMap W ρ P h r)

/- English proof (translation)
Use `ProjPoint.awayLift_mk_mul (grading W) (evalHom W ρ P h) (f := coord W i) (by rwa [evalHom_coord]) (coord_mem W i) 1 (coord W j) (coord_mem W j)` as an intermediate fact. Simplify using `only [pow_one, evalHom_coord] at this`. Conclude with `this`.
-/
theorem awayEval_awayCoord_mul (h : (W.map ρ).toProjective.Equation P) (hi : IsUnit (P i))
    (j : Fin 3) : awayEval W i ρ P h hi (awayCoord W i j) * P i = P j := by
  have := ProjPoint.awayLift_mk_mul (grading W) (evalHom W ρ P h) (f := coord W i)
    (by rwa [evalHom_coord]) (coord_mem W i) 1 (coord W j) (coord_mem W j)
  simp only [pow_one, evalHom_coord] at this
  exact this

def awayChart : Spec (.of (AwayRing W i)) ⟶ scheme W :=
  Proj.awayι (grading W) (coord W i) (coord_mem W i) one_pos

instance : IsOpenImmersion (awayChart W i) :=
  inferInstanceAs (IsOpenImmersion (Proj.awayι (grading W) (coord W i) (coord_mem W i) one_pos))

/- English proof (translation)
The claim follows from `Proj.opensRange_awayι ..`.
-/
theorem opensRange_awayChart : (awayChart W i).opensRange = coordOpen W i :=
  Proj.opensRange_awayι ..

/- English proof (translation)
The claim follows from `Proj.isAffineOpen_basicOpen _ _ (coord_mem W i) one_pos`.
-/
theorem isAffineOpen_coordOpen : IsAffineOpen (coordOpen W i) :=
  Proj.isAffineOpen_basicOpen _ _ (coord_mem W i) one_pos

/- English proof (translation)
The claim follows from `ProjPoint.ofHom_eq_awayι (grading W) _ _ one_pos (coord_mem W i) _`.
-/
theorem ptHom_eq_awayChart (h : IsUnimodularSol (W.map ρ) P) (hi : IsUnit (P i)) :
    ptHom W ρ P h =
      Spec.map (CommRingCat.ofHom (awayEval W i ρ P h.equation hi)) ≫ awayChart W i :=
  ProjPoint.ofHom_eq_awayι (grading W) _ _ one_pos (coord_mem W i) _

/- English proof (translation)
Establish `hi : IsUnit (awayCoord W i i)` using `by simp`. Establish `: awayEval W i _ _ (equation_awayCoord W i) hi = RingHom.id _` using `awayRing_hom_ext W i (fun r => awayEval_awayConst ..) fun j => by`. Simplify using `using awayEval_awayCoord_mul W i _ _ (equation_awayCoord W i) hi j`. Rewrite using `[ptHom_eq_awayChart W i _ _ _ hi, this]`. Simplify using the standard rewrite rules.

Use the proof step `@[reassoc]`.
-/
theorem awayChart_eq_ptHom :
    awayChart W i = ptHom W (awayConst W i) (awayCoord W i) (isUnimodularSol_awayCoord W i) := by
  have hi : IsUnit (awayCoord W i i) := by simp
  have : awayEval W i _ _ (equation_awayCoord W i) hi = RingHom.id _ :=
    awayRing_hom_ext W i (fun r => awayEval_awayConst ..) fun j => by
      simpa using awayEval_awayCoord_mul W i _ _ (equation_awayCoord W i) hi j
  rw [ptHom_eq_awayChart W i _ _ _ hi, this]
  simp

@[reassoc]
/- English proof (translation)
Rewrite using `[awayChart_eq_ptHom, SpecMap_ptHom]`. Use the proof step `@[reassoc (attr := simp)]`.
-/
theorem SpecMap_awayChart (g : AwayRing W i →+* A) :
    Spec.map (CommRingCat.ofHom g) ≫ awayChart W i = ptHom W (g.comp (awayConst W i))
      (g ∘ awayCoord W i) ((isUnimodularSol_awayCoord W i).map_comp g) := by
  rw [awayChart_eq_ptHom, SpecMap_ptHom]

@[reassoc (attr := simp)]
/- English proof (translation)
Rewrite using `[awayChart_eq_ptHom, ptHom_toSpec]`.
-/
theorem awayChart_toSpec :
    awayChart W i ≫ toSpec W = Spec.map (CommRingCat.ofHom (awayConst W i)) := by
  rw [awayChart_eq_ptHom, ptHom_toSpec]

/- English proof (translation)
Establish `: IsIso (CommRingCat.ofHom (awayEval W i ρ P h.equation hi))` using `(ConcreteCategory.isIso_iff_bijective _).mpr hb`. Rewrite using `[ptHom_eq_awayChart W i ρ P h hi]`. Use `infer_instance`.
-/
theorem isOpenImmersion_ptHom (h : IsUnimodularSol (W.map ρ) P) (hi : IsUnit (P i))
    (hb : Function.Bijective (awayEval W i ρ P h.equation hi)) :
    IsOpenImmersion (ptHom W ρ P h) := by
  have : IsIso (CommRingCat.ofHom (awayEval W i ρ P h.equation hi)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hb
  rw [ptHom_eq_awayChart W i ρ P h hi]
  infer_instance

/- English proof (translation)
Establish `: IsIso (CommRingCat.ofHom (awayEval W i ρ P h.equation hi))` using `(ConcreteCategory.isIso_iff_bijective _).mpr hb`. Rewrite using `[ptHom_eq_awayChart W i ρ P h hi, ← opensRange_awayChart, ← Scheme.Hom.coe_opensRange, Scheme.Hom.opensRange_comp_of_isIso]`.
-/
theorem range_ptHom (h : IsUnimodularSol (W.map ρ) P) (hi : IsUnit (P i))
    (hb : Function.Bijective (awayEval W i ρ P h.equation hi)) :
    Set.range (ptHom W ρ P h) = coordOpen W i := by
  have : IsIso (CommRingCat.ofHom (awayEval W i ρ P h.equation hi)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hb
  rw [ptHom_eq_awayChart W i ρ P h hi, ← opensRange_awayChart, ← Scheme.Hom.coe_opensRange,
    Scheme.Hom.opensRange_comp_of_isIso]

end Away

section ChartZ

open Polynomial
open scoped Polynomial.Bivariate

def affineX : W.toAffine.CoordinateRing :=
  WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (C X)

def affineY : W.toAffine.CoordinateRing :=
  WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine Y

variable {A : Type*} [CommRing A]

/- English proof (translation)
Rewrite using `[WeierstrassCurve.Affine.equation_iff', WeierstrassCurve.Affine.polynomial]`. Simplify using `only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, coe_eval₂RingHom, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]`. Apply the tactic sequence `constructor <;> intro h <;> linear_combination h`.
-/
theorem affine_equation_map_iff (ρ : R →+* A) (a b : A) :
    (W.map ρ).toAffine.Equation a b ↔ W.toAffine.polynomial.eval₂ (eval₂RingHom ρ a) b = 0 := by
  rw [WeierstrassCurve.Affine.equation_iff', WeierstrassCurve.Affine.polynomial]
  simp only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, coe_eval₂RingHom,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  constructor <;> intro h <;> linear_combination h

/- English proof (translation)
Use `(affine_equation_map_iff W _ _ _).mpr ?_` and prove the remaining obligations. Establish `: eval₂RingHom (algebraMap R W.toAffine.CoordinateRing) (affineX W) = AdjoinRoot.of W.toAffine.polynomial`. Use `Polynomial.ringHom_ext (fun r => ?_) ?_` and prove the remaining obligations. Rewrite using `[coe_eval₂RingHom, eval₂_C]`. Both sides reduce to the same expression.

Rewrite using `[coe_eval₂RingHom, eval₂_X]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `AdjoinRoot.eval₂_root W.toAffine.polynomial`.
-/
theorem equation_affineX_affineY :
    (W.baseChange W.toAffine.CoordinateRing).toAffine.Equation (affineX W) (affineY W) := by
  refine (affine_equation_map_iff W _ _ _).mpr ?_
  have : eval₂RingHom (algebraMap R W.toAffine.CoordinateRing) (affineX W) =
      AdjoinRoot.of W.toAffine.polynomial := by
    refine Polynomial.ringHom_ext (fun r => ?_) ?_
    · rw [coe_eval₂RingHom, eval₂_C]; rfl
    · rw [coe_eval₂RingHom, eval₂_X]; rfl
  rw [this]
  exact AdjoinRoot.eval₂_root W.toAffine.polynomial

def affineEval (ρ : R →+* A) (a b : A) (h : (W.map ρ).toAffine.Equation a b) :
    W.toAffine.CoordinateRing →+* A :=
  AdjoinRoot.lift (eval₂RingHom ρ a) b ((affine_equation_map_iff W ρ a b).mp h)

section

variable (ρ : R →+* A) (a b : A) (h : (W.map ρ).toAffine.Equation a b)

/- English proof (translation)
Simplify using `[affineEval, affineX]`.
-/
@[simp] theorem affineEval_affineX : affineEval W ρ a b h (affineX W) = a := by
  simp [affineEval, affineX]

/- English proof (translation)
Simplify using `[affineEval, affineY]`.
-/
@[simp] theorem affineEval_affineY : affineEval W ρ a b h (affineY W) = b := by
  simp [affineEval, affineY]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `AdjoinRoot.lift _ _ _ (AdjoinRoot.of _ (C r)) = _`. Simplify using the standard rewrite rules.
-/
@[simp] theorem affineEval_algebraMap (r : R) :
    affineEval W ρ a b h (algebraMap R _ r) = ρ r := by
  change AdjoinRoot.lift _ _ _ (AdjoinRoot.of _ (C r)) = _
  simp

end

/- English proof (translation)
The claim follows from `AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext h₀ hx) hy`.
-/
theorem affine_hom_ext {f g : W.toAffine.CoordinateRing →+* A}
    (h₀ : ∀ r : R, f (algebraMap R _ r) = g (algebraMap R _ r))
    (hx : f (affineX W) = g (affineX W)) (hy : f (affineY W) = g (affineY W)) : f = g :=
  AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext h₀ hx) hy

def affineAeval [Algebra R A] (a b : A) (h : (W.baseChange A).toAffine.Equation a b) :
    W.toAffine.CoordinateRing →ₐ[R] A where
  toRingHom := affineEval W (algebraMap R A) a b h
  commutes' := affineEval_algebraMap W _ a b h

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_affineAeval [Algebra R A] (a b : A)
    (h : (W.baseChange A).toAffine.Equation a b) :
    (affineAeval W a b h : W.toAffine.CoordinateRing →+* A) =
      affineEval W (algebraMap R A) a b h := rfl

def chartZ : Spec (.of W.toAffine.CoordinateRing) ⟶ scheme W :=
  pt W ![affineX W, affineY W, 1] (isUnimodularSol_some (equation_affineX_affineY W))

/- English proof (translation)
Apply the tactic sequence `have hc : awayCoord W 2 = ![awayCoord W 2 0, awayCoord W 2 1, 1] := by ext1 j; fin_cases j <;> simp`. Establish `he : (W.map (awayConst W 2)).toAffine.Equation (awayCoord W 2 0) (awayCoord W 2 1)`. Rewrite using `[← WeierstrassCurve.Projective.equation_some, ← hc]`. Conclude with `equation_awayCoord W 2`. Establish `hm` using `awayEval_awayCoord_mul W 2 (algebraMap R _) ![affineX W, affineY W, 1] (isUnimodularSol_some (equation_affineX_affineY W)).equation isUnit_one`.

Use `set ℓ := awayEval W 2 (algebraMap R _) ![affineX W, affineY W, 1] (isUnimodularSol_some (equation_affineX_affineY W)).equation isUnit_one with hℓ`. Establish `h0 : ℓ (awayCoord W 2 0) = affineX W` using `by simpa using hm 0`. Establish `h1 : ℓ (awayCoord W 2 1) = affineY W` using `by simpa using hm 1`. Establish `hr : ∀ r, ℓ (awayConst W 2 r) = algebraMap R _ r` using `awayEval_awayConst W 2 _ _ _ _`. Use `(RingEquiv.ofRingHom ℓ (affineEval W _ _ _ he) ?_ ?_).bijective` and prove the remaining obligations.

Conclude with `affine_hom_ext W (fun r => by simp [hr]) (by simp [h0]) (by simp [h1])`. Apply the tactic sequence `refine awayRing_hom_ext W 2 (fun r => by simp [hr]) fun j => ?_ fin_cases j <;> simp [h0, h1]`.
-/
theorem bijective_awayEval_affine : Function.Bijective (awayEval W 2 (algebraMap R _)
    ![affineX W, affineY W, 1] (isUnimodularSol_some (equation_affineX_affineY W)).equation
    isUnit_one) := by
  have hc : awayCoord W 2 = ![awayCoord W 2 0, awayCoord W 2 1, 1] := by
    ext1 j; fin_cases j <;> simp
  have he : (W.map (awayConst W 2)).toAffine.Equation (awayCoord W 2 0) (awayCoord W 2 1) := by
    rw [← WeierstrassCurve.Projective.equation_some, ← hc]
    exact equation_awayCoord W 2
  have hm := awayEval_awayCoord_mul W 2 (algebraMap R _) ![affineX W, affineY W, 1]
    (isUnimodularSol_some (equation_affineX_affineY W)).equation isUnit_one
  set ℓ := awayEval W 2 (algebraMap R _) ![affineX W, affineY W, 1]
    (isUnimodularSol_some (equation_affineX_affineY W)).equation isUnit_one with hℓ
  have h0 : ℓ (awayCoord W 2 0) = affineX W := by simpa using hm 0
  have h1 : ℓ (awayCoord W 2 1) = affineY W := by simpa using hm 1
  have hr : ∀ r, ℓ (awayConst W 2 r) = algebraMap R _ r := awayEval_awayConst W 2 _ _ _ _
  refine (RingEquiv.ofRingHom ℓ (affineEval W _ _ _ he) ?_ ?_).bijective
  · exact affine_hom_ext W (fun r => by simp [hr]) (by simp [h0]) (by simp [h1])
  · refine awayRing_hom_ext W 2 (fun r => by simp [hr]) fun j => ?_
    fin_cases j <;> simp [h0, h1]

instance : IsOpenImmersion (chartZ W) :=
  isOpenImmersion_ptHom W 2 _ _ (isUnimodularSol_some (equation_affineX_affineY W)) isUnit_one
    (bijective_awayEval_affine W)

/- English proof (translation)
The claim follows from `TopologicalSpace.Opens.ext (range_ptHom W 2 _ _ (isUnimodularSol_some (equation_affineX_affineY W)) isUnit_one (bijective_awayEval_affine W)) @[reassoc (attr := simp)]`.
-/
theorem opensRange_chartZ : (chartZ W).opensRange = coordOpen W 2 :=
  TopologicalSpace.Opens.ext (range_ptHom W 2 _ _
    (isUnimodularSol_some (equation_affineX_affineY W)) isUnit_one (bijective_awayEval_affine W))

@[reassoc (attr := simp)]
/- English proof (translation)
The claim follows from `pt_toSpec .. @[reassoc]`.
-/
theorem chartZ_toSpec : chartZ W ≫ toSpec W =
    Spec.map (CommRingCat.ofHom (algebraMap R W.toAffine.CoordinateRing)) :=
  pt_toSpec ..

@[reassoc]
/- English proof (translation)
The claim follows from `(SpecMap_ptHom W _ _ (isUnimodularSol_some (equation_affineX_affineY W)) _).trans (ptHom_congr W _ _ _ (RingHom.ext (affineEval_algebraMap W ρ a b h)) (by ext i; fin_cases i <;> simp) _) @[reassoc]`.
-/
theorem SpecMap_affineEval_chartZ {A : Type u} [CommRing A] (ρ : R →+* A) (a b : A)
    (h : (W.map ρ).toAffine.Equation a b) :
    Spec.map (CommRingCat.ofHom (affineEval W ρ a b h)) ≫ chartZ W =
      ptHom W ρ ![a, b, 1] (isUnimodularSol_some h) :=
  (SpecMap_ptHom W _ _ (isUnimodularSol_some (equation_affineX_affineY W)) _).trans
    (ptHom_congr W _ _ _ (RingHom.ext (affineEval_algebraMap W ρ a b h))
      (by ext i; fin_cases i <;> simp) _)

@[reassoc]
/- English proof (translation)
The claim follows from `SpecMap_affineEval_chartZ W (algebraMap R A) a b h`.
-/
theorem SpecMap_affineAeval_chartZ {A : Type u} [CommRing A] [Algebra R A] (a b : A)
    (h : (W.baseChange A).toAffine.Equation a b) :
    Spec.map (CommRingCat.ofHom (affineAeval W a b h : W.toAffine.CoordinateRing →+* A)) ≫
      chartZ W = pt W ![a, b, 1] (isUnimodularSol_some h) :=
  SpecMap_affineEval_chartZ W (algebraMap R A) a b h

def awayEquivAffine : AwayRing W 2 ≃+* W.toAffine.CoordinateRing :=
  RingEquiv.ofBijective _ (bijective_awayEval_affine W)

/- English proof (translation)
The claim follows from `ptHom_eq_awayChart W 2 _ _ (isUnimodularSol_some (equation_affineX_affineY W)) isUnit_one`.
-/
theorem chartZ_eq : chartZ W = Spec.map (CommRingCat.ofHom
    (awayEquivAffine W : AwayRing W 2 →+* W.toAffine.CoordinateRing)) ≫ awayChart W 2 :=
  ptHom_eq_awayChart W 2 _ _ (isUnimodularSol_some (equation_affineX_affineY W)) isUnit_one

end ChartZ

section ChartY

open Polynomial
open scoped Polynomial.Bivariate

def originPolynomial : R[X][Y] :=
  Y ^ 3 + C (C W.a₂ * X) * Y ^ 2 + C (C W.a₁ * X + C W.a₄ * X ^ 2) * Y
    + C (C W.a₃ * X ^ 2 + C W.a₆ * X ^ 3 - X)

/- English proof (translation)
Unfold `originPolynomial`. Use `monicity!`.
-/
theorem monic_originPolynomial : (originPolynomial W).Monic := by
  unfold originPolynomial
  monicity!

/- English proof (translation)
Unfold `originPolynomial`. Use `compute_degree!`.
-/
theorem natDegree_originPolynomial [Nontrivial R] : (originPolynomial W).natDegree = 3 := by
  unfold originPolynomial
  compute_degree!

abbrev OriginRing : Type u := AdjoinRoot (originPolynomial W)

instance : Module.Free R[X] (OriginRing W) := (monic_originPolynomial W).free_adjoinRoot

instance : Module.Finite R[X] (OriginRing W) := (monic_originPolynomial W).finite_adjoinRoot

instance : Module.Free R (OriginRing W) := .trans (S := R[X])

def originZ : OriginRing W := AdjoinRoot.mk (originPolynomial W) Y

def originW : OriginRing W := AdjoinRoot.mk (originPolynomial W) (C X)

variable {A : Type*} [CommRing A]

/- English proof (translation)
Rewrite using `[equation_origin_iff, originPolynomial]`. Simplify using `only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, coe_eval₂RingHom, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]`. Apply the tactic sequence `constructor <;> intro h <;> linear_combination -h`.
-/
theorem origin_equation_map_iff (ρ : R →+* A) (z w : A) :
    (W.map ρ).toProjective.Equation ![z, -1, w] ↔
      (originPolynomial W).eval₂ (eval₂RingHom ρ w) z = 0 := by
  rw [equation_origin_iff, originPolynomial]
  simp only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, coe_eval₂RingHom,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  constructor <;> intro h <;> linear_combination -h

/- English proof (translation)
Use `(origin_equation_map_iff W _ _ _).mpr ?_` and prove the remaining obligations. Establish `: eval₂RingHom (algebraMap R (OriginRing W)) (originW W) = AdjoinRoot.of (originPolynomial W)`. Use `Polynomial.ringHom_ext (fun r => ?_) ?_` and prove the remaining obligations. Rewrite using `[coe_eval₂RingHom, eval₂_C]`. Both sides reduce to the same expression.

Rewrite using `[coe_eval₂RingHom, eval₂_X]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `AdjoinRoot.eval₂_root (originPolynomial W)`.
-/
theorem equation_originZ_originW :
    (W.baseChange (OriginRing W)).toProjective.Equation ![originZ W, -1, originW W] := by
  refine (origin_equation_map_iff W _ _ _).mpr ?_
  have : eval₂RingHom (algebraMap R (OriginRing W)) (originW W) =
      AdjoinRoot.of (originPolynomial W) := by
    refine Polynomial.ringHom_ext (fun r => ?_) ?_
    · rw [coe_eval₂RingHom, eval₂_C]; rfl
    · rw [coe_eval₂RingHom, eval₂_X]; rfl
  rw [this]
  exact AdjoinRoot.eval₂_root (originPolynomial W)

def originEval (ρ : R →+* A) (z w : A) (h : (W.map ρ).toProjective.Equation ![z, -1, w]) :
    OriginRing W →+* A :=
  AdjoinRoot.lift (eval₂RingHom ρ w) z ((origin_equation_map_iff W ρ z w).mp h)

section

variable (ρ : R →+* A) (z w : A) (h : (W.map ρ).toProjective.Equation ![z, -1, w])

/- English proof (translation)
Simplify using `[originEval, originZ]`.
-/
@[simp] theorem originEval_originZ : originEval W ρ z w h (originZ W) = z := by
  simp [originEval, originZ]

/- English proof (translation)
Simplify using `[originEval, originW]`.
-/
@[simp] theorem originEval_originW : originEval W ρ z w h (originW W) = w := by
  simp [originEval, originW]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `AdjoinRoot.lift _ _ _ (AdjoinRoot.of _ (C r)) = _`. Simplify using the standard rewrite rules.
-/
@[simp] theorem originEval_algebraMap (r : R) :
    originEval W ρ z w h (algebraMap R _ r) = ρ r := by
  change AdjoinRoot.lift _ _ _ (AdjoinRoot.of _ (C r)) = _
  simp

end

/- English proof (translation)
The claim follows from `AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext h₀ hw) hz`.
-/
theorem origin_hom_ext {f g : OriginRing W →+* A}
    (h₀ : ∀ r : R, f (algebraMap R _ r) = g (algebraMap R _ r))
    (hz : f (originZ W) = g (originZ W)) (hw : f (originW W) = g (originW W)) : f = g :=
  AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext h₀ hw) hz

def originAeval [Algebra R A] (z w : A)
    (h : (W.baseChange A).toProjective.Equation ![z, -1, w]) : OriginRing W →ₐ[R] A where
  toRingHom := originEval W (algebraMap R A) z w h
  commutes' := originEval_algebraMap W _ z w h

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_originAeval [Algebra R A] (z w : A)
    (h : (W.baseChange A).toProjective.Equation ![z, -1, w]) :
    (originAeval W z w h : OriginRing W →+* A) = originEval W (algebraMap R A) z w h := rfl

def chartY : Spec (.of (OriginRing W)) ⟶ scheme W :=
  pt W ![originZ W, -1, originW W] (isUnimodularSol_origin (equation_originZ_originW W))

/- English proof (translation)
Apply the tactic sequence `have hc : (-1 : AwayRing W 1) • awayCoord W 1 = ![-awayCoord W 1 0, -1, -awayCoord W 1 2] := by ext1 j; fin_cases j <;> simp`. Establish `he : (W.map (awayConst W 1)).toProjective.Equation ![-awayCoord W 1 0, -1, -awayCoord W 1 2]`. Rewrite using `[← hc, WeierstrassCurve.Projective.equation_smul _ isUnit_one.neg]`. Conclude with `equation_awayCoord W 1`. Establish `hm` using `awayEval_awayCoord_mul W 1 (algebraMap R _) ![originZ W, -1, originW W] (equation_originZ_originW W) isUnit_one.neg`.

Use `set ℓ := awayEval W 1 (algebraMap R _) ![originZ W, -1, originW W] (equation_originZ_originW W) isUnit_one.neg with hℓ`. Establish `h0 : ℓ (awayCoord W 1 0) = -originZ W` using `by simpa [neg_eq_iff_eq_neg] using hm 0`. Establish `h2 : ℓ (awayCoord W 1 2) = -originW W` using `by simpa [neg_eq_iff_eq_neg] using hm 2`. Establish `hr : ∀ r, ℓ (awayConst W 1 r) = algebraMap R _ r` using `awayEval_awayConst W 1 _ _ _ _`. Use `(RingEquiv.ofRingHom ℓ (originEval W _ _ _ he) ?_ ?_).bijective` and prove the remaining obligations.

Conclude with `origin_hom_ext W (fun r => by simp [hr]) (by simp [h0]) (by simp [h2])`. Apply the tactic sequence `refine awayRing_hom_ext W 1 (fun r => by simp [hr]) fun j => ?_ fin_cases j <;> simp [h0, h2]`.
-/
theorem bijective_awayEval_origin : Function.Bijective (awayEval W 1 (algebraMap R _)
    ![originZ W, -1, originW W] (equation_originZ_originW W) isUnit_one.neg) := by
  have hc : (-1 : AwayRing W 1) • awayCoord W 1 = ![-awayCoord W 1 0, -1, -awayCoord W 1 2] := by
    ext1 j; fin_cases j <;> simp
  have he : (W.map (awayConst W 1)).toProjective.Equation
      ![-awayCoord W 1 0, -1, -awayCoord W 1 2] := by
    rw [← hc, WeierstrassCurve.Projective.equation_smul _ isUnit_one.neg]
    exact equation_awayCoord W 1
  have hm := awayEval_awayCoord_mul W 1 (algebraMap R _) ![originZ W, -1, originW W]
    (equation_originZ_originW W) isUnit_one.neg
  set ℓ := awayEval W 1 (algebraMap R _) ![originZ W, -1, originW W]
    (equation_originZ_originW W) isUnit_one.neg with hℓ
  have h0 : ℓ (awayCoord W 1 0) = -originZ W := by simpa [neg_eq_iff_eq_neg] using hm 0
  have h2 : ℓ (awayCoord W 1 2) = -originW W := by simpa [neg_eq_iff_eq_neg] using hm 2
  have hr : ∀ r, ℓ (awayConst W 1 r) = algebraMap R _ r := awayEval_awayConst W 1 _ _ _ _
  refine (RingEquiv.ofRingHom ℓ (originEval W _ _ _ he) ?_ ?_).bijective
  · exact origin_hom_ext W (fun r => by simp [hr]) (by simp [h0]) (by simp [h2])
  · refine awayRing_hom_ext W 1 (fun r => by simp [hr]) fun j => ?_
    fin_cases j <;> simp [h0, h2]

instance : IsOpenImmersion (chartY W) :=
  isOpenImmersion_ptHom W 1 _ _ (isUnimodularSol_origin (equation_originZ_originW W))
    isUnit_one.neg (bijective_awayEval_origin W)

/- English proof (translation)
The claim follows from `TopologicalSpace.Opens.ext (range_ptHom W 1 _ _ (isUnimodularSol_origin (equation_originZ_originW W)) isUnit_one.neg (bijective_awayEval_origin W)) @[reassoc (attr := simp)]`.
-/
theorem opensRange_chartY : (chartY W).opensRange = coordOpen W 1 :=
  TopologicalSpace.Opens.ext (range_ptHom W 1 _ _
    (isUnimodularSol_origin (equation_originZ_originW W)) isUnit_one.neg
    (bijective_awayEval_origin W))

@[reassoc (attr := simp)]
/- English proof (translation)
The claim follows from `pt_toSpec .. @[reassoc]`.
-/
theorem chartY_toSpec : chartY W ≫ toSpec W =
    Spec.map (CommRingCat.ofHom (algebraMap R (OriginRing W))) :=
  pt_toSpec ..

@[reassoc]
/- English proof (translation)
The claim follows from `(SpecMap_ptHom W _ _ (isUnimodularSol_origin (equation_originZ_originW W)) _).trans (ptHom_congr W _ _ _ (RingHom.ext (originEval_algebraMap W ρ z w h)) (by ext i; fin_cases i <;> simp) _) @[reassoc]`.
-/
theorem SpecMap_originEval_chartY {A : Type u} [CommRing A] (ρ : R →+* A) (z w : A)
    (h : (W.map ρ).toProjective.Equation ![z, -1, w]) :
    Spec.map (CommRingCat.ofHom (originEval W ρ z w h)) ≫ chartY W =
      ptHom W ρ ![z, -1, w] (isUnimodularSol_origin h) :=
  (SpecMap_ptHom W _ _ (isUnimodularSol_origin (equation_originZ_originW W)) _).trans
    (ptHom_congr W _ _ _ (RingHom.ext (originEval_algebraMap W ρ z w h))
      (by ext i; fin_cases i <;> simp) _)

@[reassoc]
/- English proof (translation)
The claim follows from `SpecMap_originEval_chartY W (algebraMap R A) z w h`.
-/
theorem SpecMap_originAeval_chartY {A : Type u} [CommRing A] [Algebra R A] (z w : A)
    (h : (W.baseChange A).toProjective.Equation ![z, -1, w]) :
    Spec.map (CommRingCat.ofHom (originAeval W z w h : OriginRing W →+* A)) ≫ chartY W =
      pt W ![z, -1, w] (isUnimodularSol_origin h) :=
  SpecMap_originEval_chartY W (algebraMap R A) z w h

def awayEquivOrigin : AwayRing W 1 ≃+* OriginRing W :=
  RingEquiv.ofBijective _ (bijective_awayEval_origin W)

/- English proof (translation)
The claim follows from `ptHom_eq_awayChart W 1 _ _ (isUnimodularSol_origin (equation_originZ_originW W)) isUnit_one.neg`.
-/
theorem chartY_eq : chartY W = Spec.map (CommRingCat.ofHom
    (awayEquivOrigin W : AwayRing W 1 →+* OriginRing W)) ≫ awayChart W 1 :=
  ptHom_eq_awayChart W 1 _ _ (isUnimodularSol_origin (equation_originZ_originW W)) isUnit_one.neg

def originAug : OriginRing W →ₐ[R] R :=
  originAeval W 0 0 ((equation_origin_iff _ _ _).mpr (by simp))

/- English proof (translation)
The claim follows from `originEval_originZ W (algebraMap R R) 0 0 ((equation_origin_iff _ _ _).mpr (by simp))`.
-/
@[simp] theorem originAug_originZ : originAug W (originZ W) = 0 :=
  originEval_originZ W (algebraMap R R) 0 0 ((equation_origin_iff _ _ _).mpr (by simp))

/- English proof (translation)
The claim follows from `originEval_originW W (algebraMap R R) 0 0 ((equation_origin_iff _ _ _).mpr (by simp)) @[reassoc]`.
-/
@[simp] theorem originAug_originW : originAug W (originW W) = 0 :=
  originEval_originW W (algebraMap R R) 0 0 ((equation_origin_iff _ _ _).mpr (by simp))

@[reassoc]
/- English proof (translation)
Use `(SpecMap_originEval_chartY W (algebraMap R R) 0 0 ((equation_origin_iff _ _ _).mpr (by simp))).trans ?_` and prove the remaining obligations. Rewrite using `[zero, ← pt_smul W (A := R) _ _ isUnit_one.neg]`. Conclude with `ptHom_congr W _ _ _ rfl (by simp) _`.
-/
theorem SpecMap_originAug_chartY :
    Spec.map (CommRingCat.ofHom (originAug W : OriginRing W →+* R)) ≫ chartY W = zero W := by
  refine (SpecMap_originEval_chartY W (algebraMap R R) 0 0
    ((equation_origin_iff _ _ _).mpr (by simp))).trans ?_
  rw [zero, ← pt_smul W (A := R) _ _ isUnit_one.neg]
  exact ptHom_congr W _ _ _ rfl (by simp) _

end ChartY

/- English proof (translation)
Rewrite using `[opensRange_chartY, opensRange_chartZ, coordOpen_one_sup_coordOpen_two]`.
-/
theorem opensRange_chartY_sup_opensRange_chartZ :
    (chartY W).opensRange ⊔ (chartZ W).opensRange = ⊤ := by
  rw [opensRange_chartY, opensRange_chartZ, coordOpen_one_sup_coordOpen_two]

/- English proof (translation)
The claim follows from `pt_preimage_coordOpen ..`.
-/
theorem chartY_preimage_coordOpen_two :
    chartY W ⁻¹ᵁ coordOpen W 2 = PrimeSpectrum.basicOpen (originW W) :=
  pt_preimage_coordOpen ..

/- English proof (translation)
The claim follows from `pt_preimage_coordOpen ..`.
-/
theorem chartZ_preimage_coordOpen_one :
    chartZ W ⁻¹ᵁ coordOpen W 1 = PrimeSpectrum.basicOpen (affineY W) :=
  pt_preimage_coordOpen ..

/- English proof (translation)
The claim follows from `(opensRange_chartY_sup_opensRange_chartZ W).ge (Set.mem_univ x)`.
-/
theorem exists_chartY_or_chartZ (x : scheme W) :
    (∃ y, chartY W y = x) ∨ ∃ y, chartZ W y = x :=
  (opensRange_chartY_sup_opensRange_chartZ W).ge (Set.mem_univ x)

def chartCover : (scheme W).AffineOpenCover where
  I₀ := Bool
  X b := match b with
    | true => .of (OriginRing W)
    | false => .of W.toAffine.CoordinateRing
  f b := match b with
    | true => chartY W
    | false => chartZ W
  idx x := by classical exact decide (x ∈ Set.range (chartY W))
  covers x := by
    classical
    by_cases hx : x ∈ Set.range (chartY W)
    · rw [decide_eq_true hx]; exact hx
    · rw [decide_eq_false hx]; exact (exists_chartY_or_chartZ W x).resolve_left hx
  map_prop b := match b with
    | true => inferInstanceAs (IsOpenImmersion (chartY W))
    | false => inferInstanceAs (IsOpenImmersion (chartZ W))

/- English proof (translation)
The claim follows from `(chartCover W).openCover.hom_ext _ _ fun b => match b with | true => hY | false => hZ`.
-/
theorem scheme_hom_ext {T : Scheme.{u}} {f g : scheme W ⟶ T}
    (hY : chartY W ≫ f = chartY W ≫ g) (hZ : chartZ W ≫ f = chartZ W ≫ g) : f = g :=
  (chartCover W).openCover.hom_ext _ _ fun b => match b with
    | true => hY
    | false => hZ

def awayCover : (scheme W).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan (grading W) (coord W) (coord_mem W) (fun _ => one_pos)
    (irrelevant_eq_span_coord W).le

instance finiteType_grading_zero : Algebra.FiniteType (grading W 0) (HomRing W) :=
  have : IsScalarTower R (grading W 0) (HomRing W) := .of_algebraMap_eq fun _ => rfl
  Algebra.FiniteType.of_restrictScalars_finiteType R (grading W 0) (HomRing W)

instance isProper_toSpec : IsProper (toSpec W) := by
  have : IsIso (CommRingCat.ofHom (algebraMap R (grading W 0))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_algebraMap_grading_zero W)
  exact inferInstanceAs (IsProper (Proj.toSpecZero (grading W) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (grading W 0)))))

section BaseChange

variable {R' R'' : Type u} [CommRing R'] [CommRing R''] {W' : WeierstrassCurve R'}
  {W'' : WeierstrassCurve R''}

variable {W} in

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem map_comp_eq {A : Type*} [CommRing A] {f : R →+* R'} (h : W.map f = W') (ρ : R' →+* A) :
    W.map (ρ.comp f) = W'.map ρ := by
  subst h
  rfl

variable {W} in

/- English proof (translation)
The claim follows from `(map_comp_eq h ρ).symm ▸ hP`.
-/
theorem IsUnimodularSol.comp_of_map_eq {A : Type*} [CommRing A] {f : R →+* R'}
    (h : W.map f = W') {ρ : R' →+* A} {P : Fin 3 → A} (hP : IsUnimodularSol (W'.map ρ) P) :
    IsUnimodularSol (W.map (ρ.comp f)) P :=
  (map_comp_eq h ρ).symm ▸ hP

variable (f : R →+* R') (h : W.map f = W')

def homRingMap : HomRing W →+* HomRing W' :=
  evalHom W ((algebraMap R' (HomRing W')).comp f) (coord W')
    ((map_comp_eq h (algebraMap R' (HomRing W'))).symm ▸ equation_coord W')

/- English proof (translation)
The claim follows from `evalHom_coord ..`.
-/
@[simp] theorem homRingMap_coord (i : Fin 3) : homRingMap W f h (coord W i) = coord W' i :=
  evalHom_coord ..

/- English proof (translation)
The claim follows from `evalHom_algebraMap ..`.
-/
@[simp] theorem homRingMap_algebraMap (r : R) :
    homRingMap W f h (algebraMap R _ r) = algebraMap R' _ (f r) :=
  evalHom_algebraMap ..

/- English proof (translation)
The claim follows from `RingHom.congr_fun (MvPolynomial.ringHom_ext (f := (homRingMap W f h).comp (Ideal.Quotient.mk _)) (g := (Ideal.Quotient.mk _).comp (MvPolynomial.map f)) (fun r => (homRingMap_algebraMap W f h r).trans (congrArg (Ideal.Quotient.mk _) (MvPolynomial.map_C f r)).symm) (fun i => (homRi …`.
-/
theorem homRingMap_mk (p : MvPolynomial (Fin 3) R) :
    homRingMap W f h (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (MvPolynomial.map f p) :=
  RingHom.congr_fun (MvPolynomial.ringHom_ext
    (f := (homRingMap W f h).comp (Ideal.Quotient.mk _))
    (g := (Ideal.Quotient.mk _).comp (MvPolynomial.map f))
    (fun r => (homRingMap_algebraMap W f h r).trans
      (congrArg (Ideal.Quotient.mk _) (MvPolynomial.map_C f r)).symm)
    (fun i => (homRingMap_coord W f h i).trans
      (congrArg (Ideal.Quotient.mk _) (MvPolynomial.map_X f i)).symm)) p

def gradedMap : grading W →+*ᵍ grading W' where
  toRingHom := homRingMap W f h
  map_mem := by
    rintro n _ ⟨p, hp, rfl⟩
    exact ⟨_, MvPolynomial.IsHomogeneous.map hp f, (homRingMap_mk W f h p).symm⟩

/- English proof (translation)
Rewrite using `[← toIdeal_le_toIdeal_iff, irrelevant_eq_span_coord, Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[← homRingMap_coord W f h i]`. Conclude with `Ideal.mem_map_of_mem (gradedMap W f h) (mem_irrelevant_of_mem _ one_pos (coord_mem W i))`.
-/
theorem irrelevant_le_map_gradedMap :
    irrelevant (grading W') ≤ (irrelevant (grading W)).map (gradedMap W f h) := by
  rw [← toIdeal_le_toIdeal_iff, irrelevant_eq_span_coord, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [← homRingMap_coord W f h i]
  exact Ideal.mem_map_of_mem (gradedMap W f h) (mem_irrelevant_of_mem _ one_pos (coord_mem W i))

def mapHom : scheme W' ⟶ scheme W :=
  Proj.map (gradedMap W f h) (irrelevant_le_map_gradedMap W f h)

@[reassoc]
/- English proof (translation)
Use `(ProjPoint.ofHom_map (gradedMap W f h) (irrelevant_le_map_gradedMap W f h) _ (map_irrelevant_evalHom W' hP)).trans ?_` and prove the remaining obligations. Establish `: (evalHom W' ρ P hP.equation).comp (gradedMap W f h).toRingHom = evalHom W (ρ.comp f) P (hP.comp_of_map_eq h).equation` using `homRing_hom_ext W (fun r => by simp [gradedMap]) (fun i => by simp [gradedMap])`. Simplify using `only [this]`. Both sides reduce to the same expression.
-/
theorem ptHom_mapHom {A : Type u} [CommRing A] (ρ : R' →+* A) (P : Fin 3 → A)
    (hP : IsUnimodularSol (W'.map ρ) P) :
    ptHom W' ρ P hP ≫ mapHom W f h = ptHom W (ρ.comp f) P (hP.comp_of_map_eq h) := by
  refine (ProjPoint.ofHom_map (gradedMap W f h) (irrelevant_le_map_gradedMap W f h) _
    (map_irrelevant_evalHom W' hP)).trans ?_
  have : (evalHom W' ρ P hP.equation).comp (gradedMap W f h).toRingHom =
      evalHom W (ρ.comp f) P (hP.comp_of_map_eq h).equation :=
    homRing_hom_ext W (fun r => by simp [gradedMap]) (fun i => by simp [gradedMap])
  simp only [this]
  rfl

/- English proof (translation)
The claim follows from `(Proj.map_preimage_basicOpen (gradedMap W f h) (irrelevant_le_map_gradedMap W f h) _).trans (congrArg (Proj.basicOpen (grading W')) (homRingMap_coord W f h i)) @[reassoc]`.
-/
theorem mapHom_preimage_coordOpen (i : Fin 3) :
    mapHom W f h ⁻¹ᵁ coordOpen W i = coordOpen W' i :=
  (Proj.map_preimage_basicOpen (gradedMap W f h) (irrelevant_le_map_gradedMap W f h) _).trans
    (congrArg (Proj.basicOpen (grading W')) (homRingMap_coord W f h i))

@[reassoc]
/- English proof (translation)
Apply `scheme_hom_ext` to reduce the goal to its premises. Rewrite using `[chartY_toSpec_assoc, chartY, pt_eq_ptHom, ptHom_mapHom_assoc, ptHom_toSpec, ← Spec.map_comp, CommRingCat.ofHom_comp]`. Rewrite using `[chartZ_toSpec_assoc, chartZ, pt_eq_ptHom, ptHom_mapHom_assoc, ptHom_toSpec, ← Spec.map_comp, CommRingCat.ofHom_comp]`. Use the proof step `@[reassoc]`.
-/
theorem mapHom_toSpec :
    mapHom W f h ≫ toSpec W = toSpec W' ≫ Spec.map (CommRingCat.ofHom f) := by
  apply scheme_hom_ext
  · rw [chartY_toSpec_assoc, chartY, pt_eq_ptHom, ptHom_mapHom_assoc, ptHom_toSpec,
      ← Spec.map_comp, CommRingCat.ofHom_comp]
  · rw [chartZ_toSpec_assoc, chartZ, pt_eq_ptHom, ptHom_mapHom_assoc, ptHom_toSpec,
      ← Spec.map_comp, CommRingCat.ofHom_comp]

@[reassoc]
/- English proof (translation)
Rewrite using `[SpecMap_zero]`. Conclude with `ptHom_mapHom W f h (RingHom.id R') ![0, 1, 0] (isUnimodularSol_zero _)`.
-/
theorem zero_mapHom : zero W' ≫ mapHom W f h = Spec.map (CommRingCat.ofHom f) ≫ zero W := by
  rw [SpecMap_zero]
  exact ptHom_mapHom W f h (RingHom.id R') ![0, 1, 0] (isUnimodularSol_zero _)

/- English proof (translation)
Apply `scheme_hom_ext` to reduce the goal to its premises. Rewrite using `[chartY, pt_eq_ptHom, ptHom_mapHom, Category.comp_id]`. Both sides reduce to the same expression. Rewrite using `[chartZ, pt_eq_ptHom, ptHom_mapHom, Category.comp_id]`. Both sides reduce to the same expression.

Use the proof step `@[reassoc]`.
-/
theorem mapHom_id : mapHom W (RingHom.id R) W.map_id = 𝟙 _ := by
  apply scheme_hom_ext
  · rw [chartY, pt_eq_ptHom, ptHom_mapHom, Category.comp_id]
    rfl
  · rw [chartZ, pt_eq_ptHom, ptHom_mapHom, Category.comp_id]
    rfl

@[reassoc]
/- English proof (translation)
Rewrite using `[pt_eq_ptHom, ptHom_mapHom, pt_eq_ptHom]`. Conclude with `ptHom_congr W _ _ _ (IsScalarTower.algebraMap_eq R R' A).symm rfl _`. Use the proof step `@[reassoc]`.
-/
theorem pt_mapHom {A : Type u} [CommRing A] [Algebra R R'] [Algebra R' A] [Algebra R A]
    [IsScalarTower R R' A] (h : W.map (algebraMap R R') = W') (P : Fin 3 → A)
    (hP' : IsUnimodularSol (W'.baseChange A) P) (hP : IsUnimodularSol (W.baseChange A) P) :
    pt W' P hP' ≫ mapHom W (algebraMap R R') h = pt W P hP := by
  rw [pt_eq_ptHom, ptHom_mapHom, pt_eq_ptHom]
  exact ptHom_congr W _ _ _ (IsScalarTower.algebraMap_eq R R' A).symm rfl _

@[reassoc]
/- English proof (translation)
Apply `scheme_hom_ext` to reduce the goal to its premises. Rewrite using `[chartY, pt_eq_ptHom, ptHom_mapHom_assoc, ptHom_mapHom, ptHom_mapHom]`. Both sides reduce to the same expression. Rewrite using `[chartZ, pt_eq_ptHom, ptHom_mapHom_assoc, ptHom_mapHom, ptHom_mapHom]`. Both sides reduce to the same expression.
-/
theorem mapHom_comp (g : R' →+* R'') (h' : W'.map g = W'') :
    mapHom W' g h' ≫ mapHom W f h = mapHom W (g.comp f) ((map_comp_eq h g).trans h') := by
  apply scheme_hom_ext
  · rw [chartY, pt_eq_ptHom, ptHom_mapHom_assoc, ptHom_mapHom, ptHom_mapHom]
    rfl
  · rw [chartZ, pt_eq_ptHom, ptHom_mapHom_assoc, ptHom_mapHom, ptHom_mapHom]
    rfl

def awayRingMap (i : Fin 3) : AwayRing W i →+* AwayRing W' i :=
  awayEval W i ((awayConst W' i).comp f) (awayCoord W' i)
    ((isUnimodularSol_awayCoord W' i).comp_of_map_eq h).equation (by simp)

/- English proof (translation)
The claim follows from `awayEval_awayConst W i ((awayConst W' i).comp f) (awayCoord W' i) ((isUnimodularSol_awayCoord W' i).comp_of_map_eq h).equation (by simp) r`.
-/
@[simp] theorem awayRingMap_awayConst (i : Fin 3) (r : R) :
    awayRingMap W f h i (awayConst W i r) = awayConst W' i (f r) :=
  awayEval_awayConst W i ((awayConst W' i).comp f) (awayCoord W' i)
    ((isUnimodularSol_awayCoord W' i).comp_of_map_eq h).equation (by simp) r

/- English proof (translation)
Use `awayEval_awayCoord_mul W i ((awayConst W' i).comp f) (awayCoord W' i) ((isUnimodularSol_awayCoord W' i).comp_of_map_eq h).equation (by simp) j` as an intermediate fact. Simplify using `only [awayCoord_self, mul_one] at this`. Conclude with `this`. Use the proof step `@[reassoc]`.
-/
@[simp] theorem awayRingMap_awayCoord (i j : Fin 3) :
    awayRingMap W f h i (awayCoord W i j) = awayCoord W' i j := by
  have := awayEval_awayCoord_mul W i ((awayConst W' i).comp f) (awayCoord W' i)
    ((isUnimodularSol_awayCoord W' i).comp_of_map_eq h).equation (by simp) j
  simp only [awayCoord_self, mul_one] at this
  exact this

@[reassoc]
/- English proof (translation)
Rewrite using `[awayChart_eq_ptHom W', ptHom_mapHom]`. Conclude with `ptHom_eq_awayChart W i _ _ _ _`.
-/
theorem awayChart_mapHom (i : Fin 3) : awayChart W' i ≫ mapHom W f h =
    Spec.map (CommRingCat.ofHom (awayRingMap W f h i)) ≫ awayChart W i := by
  rw [awayChart_eq_ptHom W', ptHom_mapHom]
  exact ptHom_eq_awayChart W i _ _ _ _

/- English proof (translation)
Establish `w : CommRingCat.ofHom (awayConst W i) ≫ CommRingCat.ofHom (awayRingMap W f h i) = CommRingCat.ofHom f ≫ CommRingCat.ofHom (awayConst W' i)` using `by ext1`. Conclude with `RingHom.ext (awayRingMap_awayConst W f h i)`. Establish `hs (s : PushoutCocone (CommRingCat.ofHom (awayConst W i)) (CommRingCat.ofHom f)) : s.inl.hom.comp (awayConst W i) = s.inr.hom.comp f` using `congrArg (·.hom) s.condition`. Establish `he (s : PushoutCocone (CommRingCat.ofHom (awayConst W i)) (CommRingCat.ofHom f)) : (W'.map s.inr.hom).toProjective.Equation (s.inl.hom ∘ awayCoord W i)`. Rewrite using `[← map_comp_eq h, ← hs]`.

Conclude with `((isUnimodularSol_awayCoord W i).map_comp s.inl.hom).equation`. Establish `hu (s : PushoutCocone (CommRingCat.ofHom (awayConst W i)) (CommRingCat.ofHom f)) : IsUnit ((s.inl.hom ∘ awayCoord W i) i)` using `by simp`. Establish `hc (s : PushoutCocone (CommRingCat.ofHom (awayConst W i)) (CommRingCat.ofHom f)) (j) : awayEval W' i s.inr.hom _ (he s) (hu s) (awayCoord W' i j) = s.inl.hom (awayCoord W i j)`. Use `awayEval_awayCoord_mul W' i s.inr.hom _ (he s) (hu s) j` as an intermediate fact. Simplify using `only [Function.comp_apply, awayCoord_self, map_one, mul_one] at this`.

Conclude with `this`. Use `⟨⟨w⟩, ⟨PushoutCocone.IsColimit.mk w (fun s => CommRingCat.ofHom (awayEval W' i s.inr.hom _ (he s) (hu s))) ?_ ?_ ?_⟩⟩` and prove the remaining obligations. Introduce `s ext1`. Use `awayRing_hom_ext W i (fun r => ?_) (fun j => ?_)` and prove the remaining obligations. Simplify using `using (RingHom.congr_fun (hs s) r).symm`.

Simplify using `using hc s j`. Introduce `s ext1`. Conclude with `RingHom.ext (awayEval_awayConst W' i s.inr.hom _ (he s) (hu s))`. Introduce `s m h₁ h₂ ext1`. Use `awayRing_hom_ext W' i (fun r => ?_) (fun j => ?_)` and prove the remaining obligations.

Simplify using `[← h₂]`. Rewrite using `[CommRingCat.hom_ofHom, hc, ← h₁]`. Simplify using the standard rewrite rules.
-/
theorem isPushout_awayRingMap (i : Fin 3) :
    IsPushout (CommRingCat.ofHom (awayConst W i)) (CommRingCat.ofHom f)
      (CommRingCat.ofHom (awayRingMap W f h i)) (CommRingCat.ofHom (awayConst W' i)) := by
  have w : CommRingCat.ofHom (awayConst W i) ≫ CommRingCat.ofHom (awayRingMap W f h i) =
      CommRingCat.ofHom f ≫ CommRingCat.ofHom (awayConst W' i) := by
    ext1
    exact RingHom.ext (awayRingMap_awayConst W f h i)
  have hs (s : PushoutCocone (CommRingCat.ofHom (awayConst W i)) (CommRingCat.ofHom f)) :
      s.inl.hom.comp (awayConst W i) = s.inr.hom.comp f := congrArg (·.hom) s.condition
  have he (s : PushoutCocone (CommRingCat.ofHom (awayConst W i)) (CommRingCat.ofHom f)) :
      (W'.map s.inr.hom).toProjective.Equation (s.inl.hom ∘ awayCoord W i) := by
    rw [← map_comp_eq h, ← hs]
    exact ((isUnimodularSol_awayCoord W i).map_comp s.inl.hom).equation
  have hu (s : PushoutCocone (CommRingCat.ofHom (awayConst W i)) (CommRingCat.ofHom f)) :
      IsUnit ((s.inl.hom ∘ awayCoord W i) i) := by simp
  have hc (s : PushoutCocone (CommRingCat.ofHom (awayConst W i)) (CommRingCat.ofHom f)) (j) :
      awayEval W' i s.inr.hom _ (he s) (hu s) (awayCoord W' i j) =
        s.inl.hom (awayCoord W i j) := by
    have := awayEval_awayCoord_mul W' i s.inr.hom _ (he s) (hu s) j
    simp only [Function.comp_apply, awayCoord_self, map_one, mul_one] at this
    exact this
  refine ⟨⟨w⟩, ⟨PushoutCocone.IsColimit.mk w
    (fun s => CommRingCat.ofHom (awayEval W' i s.inr.hom _ (he s) (hu s))) ?_ ?_ ?_⟩⟩
  · intro s
    ext1
    refine awayRing_hom_ext W i (fun r => ?_) (fun j => ?_)
    · simpa using (RingHom.congr_fun (hs s) r).symm
    · simpa using hc s j
  · intro s
    ext1
    exact RingHom.ext (awayEval_awayConst W' i s.inr.hom _ (he s) (hu s))
  · intro s m h₁ h₂
    ext1
    refine awayRing_hom_ext W' i (fun r => ?_) (fun j => ?_)
    · simp [← h₂]
    · rw [CommRingCat.hom_ofHom, hc, ← h₁]
      simp

/- English proof (translation)
The claim follows from `IsOpenImmersion.isPullback _ _ _ _ (awayChart_mapHom W f h i) (by rw [opensRange_awayChart, opensRange_awayChart, mapHom_preimage_coordOpen])`.
-/
theorem isPullback_awayChart (i : Fin 3) :
    IsPullback (Spec.map (CommRingCat.ofHom (awayRingMap W f h i))) (awayChart W' i)
      (awayChart W i) (mapHom W f h) :=
  IsOpenImmersion.isPullback _ _ _ _ (awayChart_mapHom W f h i)
    (by rw [opensRange_awayChart, opensRange_awayChart, mapHom_preimage_coordOpen])

/- English proof (translation)
Use `Scheme.isPullback_of_openCover _ _ _ _ (awayCover W).openCover fun (i : Fin 3) => ?_` and prove the remaining obligations. Establish `h₁` using `isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_awayRingMap W f h i)`. Rewrite `h₁` using `[← awayChart_toSpec W, ← awayChart_toSpec W']`. Establish `h₂` using `(isPullback_awayChart W f h i).flip`. Use `h₁.of_iso h₂.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_` and prove the remaining obligations.

Conclude with `(Category.comp_id _).trans h₂.isoPullback_hom_snd.symm`. Conclude with `(Category.comp_id _).trans (h₂.isoPullback_hom_fst_assoc _).symm`. Conclude with `(Category.comp_id _).trans (Category.id_comp _).symm`. Conclude with `(Category.comp_id _).trans (Category.id_comp _).symm`.
-/
theorem isPullback_mapHom :
    IsPullback (mapHom W f h) (toSpec W') (toSpec W) (Spec.map (CommRingCat.ofHom f)) := by
  refine Scheme.isPullback_of_openCover _ _ _ _ (awayCover W).openCover fun (i : Fin 3) => ?_
  have h₁ := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_awayRingMap W f h i)
  rw [← awayChart_toSpec W, ← awayChart_toSpec W'] at h₁
  have h₂ := (isPullback_awayChart W f h i).flip
  refine h₁.of_iso h₂.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (Category.comp_id _).trans h₂.isoPullback_hom_snd.symm
  · exact (Category.comp_id _).trans (h₂.isoPullback_hom_fst_assoc _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm

def affineMap : W.toAffine.CoordinateRing →+* W'.toAffine.CoordinateRing :=
  affineEval W ((algebraMap R' _).comp f) (affineX W') (affineY W')
    ((map_comp_eq h (algebraMap R' W'.toAffine.CoordinateRing)).symm ▸
      equation_affineX_affineY W')

def originMap : OriginRing W →+* OriginRing W' :=
  originEval W ((algebraMap R' _).comp f) (originZ W') (originW W')
    ((map_comp_eq h (algebraMap R' (OriginRing W'))).symm ▸ equation_originZ_originW W')

/- English proof (translation)
Simplify using `[affineMap]`.
-/
@[simp] theorem affineMap_affineX : affineMap W f h (affineX W) = affineX W' := by
  simp [affineMap]

/- English proof (translation)
Simplify using `[affineMap]`.
-/
@[simp] theorem affineMap_affineY : affineMap W f h (affineY W) = affineY W' := by
  simp [affineMap]

/- English proof (translation)
Rewrite using `[affineMap, affineEval_algebraMap, RingHom.comp_apply]`.
-/
@[simp] theorem affineMap_algebraMap (r : R) :
    affineMap W f h (algebraMap R _ r) = algebraMap R' _ (f r) := by
  rw [affineMap, affineEval_algebraMap, RingHom.comp_apply]

/- English proof (translation)
Simplify using `[originMap]`.
-/
@[simp] theorem originMap_originZ : originMap W f h (originZ W) = originZ W' := by
  simp [originMap]

/- English proof (translation)
Simplify using `[originMap]`.
-/
@[simp] theorem originMap_originW : originMap W f h (originW W) = originW W' := by
  simp [originMap]

/- English proof (translation)
Rewrite using `[originMap, originEval_algebraMap, RingHom.comp_apply]`.
-/
@[simp] theorem originMap_algebraMap (r : R) :
    originMap W f h (algebraMap R _ r) = algebraMap R' _ (f r) := by
  rw [originMap, originEval_algebraMap, RingHom.comp_apply]

/- English proof (translation)
The claim follows from `IsOpenImmersion.isPullback _ _ _ _ (by rw [affineMap, SpecMap_affineEval_chartZ, chartZ, pt_eq_ptHom, ptHom_mapHom]) (by rw [opensRange_chartZ, opensRange_chartZ, mapHom_preimage_coordOpen])`.
-/
theorem isPullback_chartZ : IsPullback (Spec.map (CommRingCat.ofHom (affineMap W f h)))
    (chartZ W') (chartZ W) (mapHom W f h) :=
  IsOpenImmersion.isPullback _ _ _ _
    (by rw [affineMap, SpecMap_affineEval_chartZ, chartZ, pt_eq_ptHom, ptHom_mapHom])
    (by rw [opensRange_chartZ, opensRange_chartZ, mapHom_preimage_coordOpen])

/- English proof (translation)
The claim follows from `IsOpenImmersion.isPullback _ _ _ _ (by rw [originMap, SpecMap_originEval_chartY, chartY, pt_eq_ptHom, ptHom_mapHom]) (by rw [opensRange_chartY, opensRange_chartY, mapHom_preimage_coordOpen])`.
-/
theorem isPullback_chartY : IsPullback (Spec.map (CommRingCat.ofHom (originMap W f h)))
    (chartY W') (chartY W) (mapHom W f h) :=
  IsOpenImmersion.isPullback _ _ _ _
    (by rw [originMap, SpecMap_originEval_chartY, chartY, pt_eq_ptHom, ptHom_mapHom])
    (by rw [opensRange_chartY, opensRange_chartY, mapHom_preimage_coordOpen])

def pullbackIso : pullback (toSpec W) (Spec.map (CommRingCat.ofHom f)) ≅ scheme W' :=
  (isPullback_mapHom W f h).isoPullback.symm

@[reassoc (attr := simp)]
/- English proof (translation)
The claim follows from `(isPullback_mapHom W f h).isoPullback_inv_fst @[reassoc (attr := simp)]`.
-/
theorem pullbackIso_hom_mapHom :
    (pullbackIso W f h).hom ≫ mapHom W f h = pullback.fst _ _ :=
  (isPullback_mapHom W f h).isoPullback_inv_fst

@[reassoc (attr := simp)]
/- English proof (translation)
The claim follows from `(isPullback_mapHom W f h).isoPullback_inv_snd @[reassoc (attr := simp)]`.
-/
theorem pullbackIso_hom_toSpec :
    (pullbackIso W f h).hom ≫ toSpec W' = pullback.snd _ _ :=
  (isPullback_mapHom W f h).isoPullback_inv_snd

@[reassoc (attr := simp)]
/- English proof (translation)
The claim follows from `(isPullback_mapHom W f h).isoPullback_hom_fst @[reassoc (attr := simp)]`.
-/
theorem pullbackIso_inv_fst : (pullbackIso W f h).inv ≫ pullback.fst _ _ = mapHom W f h :=
  (isPullback_mapHom W f h).isoPullback_hom_fst

@[reassoc (attr := simp)]
/- English proof (translation)
The claim follows from `(isPullback_mapHom W f h).isoPullback_hom_snd`.
-/
theorem pullbackIso_inv_snd : (pullbackIso W f h).inv ≫ pullback.snd _ _ = toSpec W' :=
  (isPullback_mapHom W f h).isoPullback_hom_snd

abbrev baseChangeIso (f : R →+* R') :
    pullback (toSpec W) (Spec.map (CommRingCat.ofHom f)) ≅ scheme (W.map f) :=
  pullbackIso W f rfl

end BaseChange

/- English proof (translation)
Introduce `e`. Establish `h₁` using `pt_preimage_coordOpen W (A := R) ![a, b, 1] (isUnimodularSol_some h) 2`. Rewrite `h₁` using `[e, zero_preimage_coordOpen_two]`. Establish `h₂ : PrimeSpectrum.basicOpen (1 : R) = ⊥` using `h₁.symm`. Rewrite `h₂` using `[PrimeSpectrum.basicOpen_eq_bot_iff]`.

Conclude with `not_isNilpotent_one h₂`.
-/
theorem pt_some_ne_zero [Nontrivial R] {a b : R} (h : W.toAffine.Equation a b) :
    pt W (A := R) ![a, b, 1] (isUnimodularSol_some h) ≠ zero W := by
  intro e
  have h₁ := pt_preimage_coordOpen W (A := R) ![a, b, 1] (isUnimodularSol_some h) 2
  rw [e, zero_preimage_coordOpen_two] at h₁
  have h₂ : PrimeSpectrum.basicOpen (1 : R) = ⊥ := h₁.symm
  rw [PrimeSpectrum.basicOpen_eq_bot_iff] at h₂
  exact not_isNilpotent_one h₂

instance [Nontrivial R] : Nonempty (scheme W) :=
  ⟨zero W (Classical.arbitrary (PrimeSpectrum R))⟩

/- English proof (translation)
The claim follows from `pt_some_ne_zero _ (by simp)`.
-/
example : pt (⟨0, 0, 1, -1, 0⟩ : WeierstrassCurve ℤ) (A := ℤ) ![0, 0, 1]
    (isUnimodularSol_some (by simp [WeierstrassCurve.baseChange])) ≠ zero _ :=
  pt_some_ne_zero _ (by simp)

/- English proof (translation)
The claim follows from `pt_smul W _ _ isUnit_one.neg`.
-/
example : pt W (A := R) ((-1 : R) • ![0, 1, 0]) ((isUnimodularSol_zero _).smul isUnit_one.neg) =
    zero W :=
  pt_smul W _ _ isUnit_one.neg

/- English proof (translation)
Rewrite using `[equation_origin_iff]`. Simplify using the standard rewrite rules.
-/
example (t : R) : (⟨0, 0, 0, 0, 0⟩ : WeierstrassCurve R).toProjective.Equation ![t, -1, t ^ 3] := by
  rw [equation_origin_iff]
  simp

/- English proof (translation)
The claim follows from `(equation_origin_iff _ _ _).mp (equation_originZ_originW W)`.
-/
example : originW W = originZ W ^ 3 + algebraMap R _ W.a₁ * originZ W * originW W
    + algebraMap R _ W.a₂ * originZ W ^ 2 * originW W + algebraMap R _ W.a₃ * originW W ^ 2
    + algebraMap R _ W.a₄ * originZ W * originW W ^ 2 + algebraMap R _ W.a₆ * originW W ^ 3 :=
  (equation_origin_iff _ _ _).mp (equation_originZ_originW W)

end WeierstrassCurve

end GlobalTheory
