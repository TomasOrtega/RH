import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.StarDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.InjTest

open Polynomial Matrix UpperTheory.V UpperTheory.V.W

/- English proof (translation)
Establish `h1 : ∀ (u : Bˣ) (k : ℤ), φ ((u ^ k : Bˣ) : B) = ((Units.map (φ : B →* B') u ^ k : B'ˣ) : B')`. Introduce `u k`. Rewrite using `[← map_zpow]`. Both sides reduce to the same expression. Proceed by induction on `y using MonoidAlgebra.induction_linear with`.

Consider the case `zero => simp [GFrame.star]`. Consider the case `add a b ha hb`. Simplify using `only [map_add, GFrame.star, MulOpposite.unop_add] at *`. Rewrite using `[ha, hb]`. Consider the case `single g b`.

Simplify using `only [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single, GFrame.eps, MonoidAlgebra.mapRingHom_single]`. Simplify using the standard rewrite rules. Rewrite using `[h1]`. Use `congr 3`. Use `ext`.

Simplify using `[← hφ]`.
-/
private theorem star_mapRingHom_eq_mapRingHom_star {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (B B' : Type) [CommRing B] [CommRing B'] [Algebra O B] [Algebra O B'] (n : ℕ) (φ : B →+* B') (hφ : φ.comp (algebraMap O B) = algebraMap O B') (y : MonoidAlgebra B F.G₀) :
    F.star O B' n (MonoidAlgebra.mapRingHom F.G₀ φ y) = MonoidAlgebra.mapRingHom F.G₀ φ (F.star O B n y) := by
  have h1 : ∀ (u : Bˣ) (k : ℤ), φ ((u ^ k : Bˣ) : B) = ((Units.map (φ : B →* B') u ^ k : B'ˣ) : B') := by
    intro u k
    rw [← map_zpow]
    rfl
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp [GFrame.star]
  | add a b ha hb =>
    simp only [map_add, GFrame.star, MulOpposite.unop_add] at *
    rw [ha, hb]
  | single g b =>
    simp only [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single, GFrame.eps, MonoidAlgebra.mapRingHom_single]
    simp
    rw [h1]
    congr 3
    ext
    simp [← hφ]

/- English proof (translation)
Introduce `l _ F O _ _ R _ _ n D X K _ _ f hf h`. Introduce `B _ _ _ _ y`. Set `u : MonoidAlgebra (MvPolynomial F.G₀ R) F.G₀` to `y.coeff.support.sum fun g => MonoidAlgebra.single g (MvPolynomial.X g)`. Set `ev : MvPolynomial F.G₀ R →ₐ[R] B` to `MvPolynomial.aeval fun g => y.coeff g`. Establish `hev : MonoidAlgebra.mapRingHom F.G₀ (ev : MvPolynomial F.G₀ R →+* B) u = y`.

Simplify using `only [u, map_sum, MonoidAlgebra.mapRingHom_single]`. Simplify using `only [ev, AlgHom.coe_toRingHom, MvPolynomial.aeval_X]`. Conclude with `y.sum_single`. Establish `hevO : (ev : MvPolynomial F.G₀ R →+* B).comp (algebraMap O (MvPolynomial F.G₀ R)) = algebraMap O B`. Use extensionality with `o`.

Simplify using `[ev, MvPolynomial.algebraMap_eq, IsScalarTower.algebraMap_apply O R B]`. Establish `key : D.D _ (F.star O _ n u) = D.D _ u`. Rewrite using `[← sub_eq_zero]`. Use extensionality with `m`. Rewrite using `[MvPolynomial.coeff_zero]`.

Apply `hf` to reduce the goal to its premises. Introduce `x`. Use `letI : Algebra R (MvPolynomial F.G₀ (K x)) := ((algebraMap (K x) (MvPolynomial F.G₀ (K x))).comp (f x : R →+* K x)).toAlgebra`. Set `φ : MvPolynomial F.G₀ R →ₐ[R] MvPolynomial F.G₀ (K x)` to `MvPolynomial.aeval MvPolynomial.X`. Establish `hφ : (φ : MvPolynomial F.G₀ R →+* MvPolynomial F.G₀ (K x)) = MvPolynomial.map (f x : R →+* K x)`.

Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using `[φ, RingHom.algebraMap_toAlgebra, MvPolynomial.algebraMap_eq]`. Introduce `i`. Simplify using `[φ]`.

Establish `hφO : (φ : MvPolynomial F.G₀ R →+* MvPolynomial F.G₀ (K x)).comp (algebraMap O (MvPolynomial F.G₀ R)) = algebraMap O (MvPolynomial F.G₀ (K x))`. Rewrite using `[hφ]`. Use `RingHom.ext fun o => ?_` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, MvPolynomial.algebraMap_apply, MvPolynomial.algebraMap_apply, MvPolynomial.map_C]`. Use `congr 1`.

Conclude with `(f x).commutes o`. Establish `hz : MvPolynomial.map (f x : R →+* K x) (D.D _ (F.star O _ n u) - D.D _ u) = 0`. Rewrite using `[← hφ, map_sub, sub_eq_zero]`. Establish `hx` using `h x (MvPolynomial F.G₀ (K x)) (MonoidAlgebra.mapRingHom F.G₀ (φ : MvPolynomial F.G₀ R →+* MvPolynomial F.G₀ (K x)) u)`. Rewrite `hx` using `[star_mapRingHom_eq_mapRingHom_star F O _ _ n _ hφO]`.

Express the relevant statement in the definitionally equal form `D.D _ (MonoidAlgebra.mapRingHom F.G₀ (φ : MvPolynomial F.G₀ R →+* MvPolynomial F.G₀ (K x)) (F.star O _ n u)) = D.D _ (MonoidAlgebra.mapRingHom F.G₀ (φ : MvPolynomial F.G₀ R →+* MvPolynomial F.G₀ (K x)) u) at hx`. Rewrite `hx` using `[D.nat _ _ φ, D.nat _ _ φ]`. Conclude with `hx`. Establish `hc` using `congrArg (MvPolynomial.coeff m) hz`. Rewrite `hc` using `[MvPolynomial.coeff_map]`.

Simplify using `using hc`. Rewrite using `[← hev, star_mapRingHom_eq_mapRingHom_star F O _ _ n _ hevO, D.nat _ _ ev, D.nat _ _ ev, key]`.
-/
theorem UpperTheory.V.AlgebraTools.Det.polarInj :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (D : GDet n R F.G₀) {X : Type} (K : X → Type) [∀ x, CommRing (K x)] [∀ x, Algebra O (K x)] (f : ∀ x, R →ₐ[O] K x),
    (∀ a, (∀ x, f x a = 0) → a = 0) → (∀ x, F.IsPolar O (D.map (f x : R →+* K x))) → F.IsPolar O D := by
  intro l _ F O _ _ R _ _ n D X K _ _ f hf h
  intro B _ _ _ _ y
  classical
  let u : MonoidAlgebra (MvPolynomial F.G₀ R) F.G₀ := y.coeff.support.sum fun g => MonoidAlgebra.single g (MvPolynomial.X g)
  let ev : MvPolynomial F.G₀ R →ₐ[R] B := MvPolynomial.aeval fun g => y.coeff g
  have hev : MonoidAlgebra.mapRingHom F.G₀ (ev : MvPolynomial F.G₀ R →+* B) u = y := by
    simp only [u, map_sum, MonoidAlgebra.mapRingHom_single]
    simp only [ev, AlgHom.coe_toRingHom, MvPolynomial.aeval_X]
    exact y.sum_single
  have hevO : (ev : MvPolynomial F.G₀ R →+* B).comp (algebraMap O (MvPolynomial F.G₀ R)) = algebraMap O B := by
    ext o
    simp [ev, MvPolynomial.algebraMap_eq, IsScalarTower.algebraMap_apply O R B]
  have key : D.D _ (F.star O _ n u) = D.D _ u := by
    rw [← sub_eq_zero]
    ext m
    rw [MvPolynomial.coeff_zero]
    apply hf
    intro x
    letI : Algebra R (MvPolynomial F.G₀ (K x)) := ((algebraMap (K x) (MvPolynomial F.G₀ (K x))).comp (f x : R →+* K x)).toAlgebra
    let φ : MvPolynomial F.G₀ R →ₐ[R] MvPolynomial F.G₀ (K x) := MvPolynomial.aeval MvPolynomial.X
    have hφ : (φ : MvPolynomial F.G₀ R →+* MvPolynomial F.G₀ (K x)) = MvPolynomial.map (f x : R →+* K x) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [φ, RingHom.algebraMap_toAlgebra, MvPolynomial.algebraMap_eq]
      · intro i
        simp [φ]
    have hφO : (φ : MvPolynomial F.G₀ R →+* MvPolynomial F.G₀ (K x)).comp (algebraMap O (MvPolynomial F.G₀ R)) = algebraMap O (MvPolynomial F.G₀ (K x)) := by
      rw [hφ]
      refine RingHom.ext fun o => ?_
      rw [RingHom.comp_apply, MvPolynomial.algebraMap_apply, MvPolynomial.algebraMap_apply, MvPolynomial.map_C]
      congr 1
      exact (f x).commutes o
    have hz : MvPolynomial.map (f x : R →+* K x) (D.D _ (F.star O _ n u) - D.D _ u) = 0 := by
      rw [← hφ, map_sub, sub_eq_zero]
      have hx := h x (MvPolynomial F.G₀ (K x)) (MonoidAlgebra.mapRingHom F.G₀ (φ : MvPolynomial F.G₀ R →+* MvPolynomial F.G₀ (K x)) u)
      rw [star_mapRingHom_eq_mapRingHom_star F O _ _ n _ hφO] at hx
      change D.D _ (MonoidAlgebra.mapRingHom F.G₀ (φ : MvPolynomial F.G₀ R →+* MvPolynomial F.G₀ (K x)) (F.star O _ n u)) = D.D _ (MonoidAlgebra.mapRingHom F.G₀ (φ : MvPolynomial F.G₀ R →+* MvPolynomial F.G₀ (K x)) u) at hx
      rw [D.nat _ _ φ, D.nat _ _ φ] at hx
      exact hx
    have hc := congrArg (MvPolynomial.coeff m) hz
    rw [MvPolynomial.coeff_map] at hc
    simpa using hc
  rw [← hev, star_mapRingHom_eq_mapRingHom_star F O _ _ n _ hevO, D.nat _ _ ev, D.nat _ _ ev, key]
