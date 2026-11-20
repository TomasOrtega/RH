import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReducedFiniteTypeIffTestRing
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

/- English proof (translation)
Use `⟨fun τ => ?_, fun T _ _ ψ g a hg => ?_⟩` and prove the remaining obligations. Use `(h.1 τ).map (e : A →+* B)` as an intermediate fact. Rewrite `this` using `[RingHom.map_det]`. Conclude with `this`. Take `⟨k, ⟨h1, h2, h3⟩, hu⟩` from `h.2 T ψ g a hg`.

Use `⟨k.comp (e.symm : B →ₐ[K] A), ⟨?_, fun τ => ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← h1]`. Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite using `[← h2 τ]`.

Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[← h3]`. Simplify using the standard rewrite rules. Introduce and unpack `k' ⟨h1', h2', h3'⟩`.

Establish `: k'.comp (e : A →ₐ[K] B) = k`. Use `hu _ ⟨?_, fun τ => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← h1']`. Both sides reduce to the same expression. Rewrite using `[← h2' τ]`.

Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[← h3']`. Simplify using the standard rewrite rules. Rewrite using `[← this]`.

Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
theorem FrameRing_of_algEquiv {K : Type} [Field K] {J : Type} (m : J → ℕ) {R A B : Type} [CommRing R] [Algebra K R]
    [CommRing A] [Algebra K A] [CommRing B] [Algebra K B] (π : R →ₐ[K] A)
    (X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A) (s : Aˣ) (h : FrameRing m π X s) (e : A ≃ₐ[K] B) :
    FrameRing m ((e : A →ₐ[K] B).comp π) (fun τ => (X τ).map e) (Units.map (e : A →* B) s) := by
  refine ⟨fun τ => ?_, fun T _ _ ψ g a hg => ?_⟩
  · have := (h.1 τ).map (e : A →+* B)
    rw [RingHom.map_det] at this
    exact this
  · obtain ⟨k, ⟨h1, h2, h3⟩, hu⟩ := h.2 T ψ g a hg
    refine ⟨k.comp (e.symm : B →ₐ[K] A), ⟨?_, fun τ => ?_, ?_⟩, ?_⟩
    · rw [← h1]; ext x; simp
    · rw [← h2 τ]; ext i j; simp
    · rw [← h3]; simp
    · rintro k' ⟨h1', h2', h3'⟩
      have : k'.comp (e : A →ₐ[K] B) = k := by
        refine hu _ ⟨?_, fun τ => ?_, ?_⟩
        · rw [← h1']; rfl
        · rw [← h2' τ]; ext i j; simp
        · rw [← h3']; simp
      rw [← this]; ext x; simp

/- English proof (translation)
Set `σ` to `Option (Σ τ, Fin (m τ) × Fin (m τ))`. Set `P` to `MvPolynomial σ R`. Set `Y : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) P` to `fun τ => Matrix.of fun i j => MvPolynomial.X (some ⟨τ, i, j⟩)`. Set `d : P` to `MvPolynomial.X none * ∏ τ, (Y τ).det`. Set `A` to `Localization.Away d`.

Establish `hd : IsUnit (algebraMap P A d)` using `IsLocalization.Away.algebraMap_isUnit d`. Establish `hs : IsUnit (algebraMap P A (MvPolynomial.X none))`. Conclude with `isUnit_of_dvd_unit (map_dvd (algebraMap P A) (dvd_mul_right _ _)) hd`. Establish `hY : ∀ τ, IsUnit (algebraMap P A (Y τ).det)`. Introduce `τ`.

Establish `h0 : (Y τ).det ∣ d` using `Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun τ => (Y τ).det) (Finset.mem_univ τ)) _`. Conclude with `isUnit_of_dvd_unit (map_dvd (algebraMap P A) h0) hd`. Establish `hPred : IsReduced P` using `inferInstance`. Establish `hPft : Algebra.FiniteType R P` using `inferInstance`. Establish `hAft : Algebra.FiniteType P A` using `inferInstance`.

Establish `hPft' : Algebra.FiniteType K P` using `Algebra.FiniteType.trans inferInstance hPft`. Use `⟨A, inferInstance, inferInstance, IsScalarTower.toAlgHom K R A, fun τ => (Y τ).map (algebraMap P A), hs.unit, Algebra.FiniteType.trans hPft' hAft, inferInstance, fun τ => ?_, fun T _ _ ψ g a hg => ?_⟩` and prove the remaining obligations. Use `hY τ` as an intermediate fact. Rewrite `this` using `[RingHom.map_det]`. Conclude with `this`.

Set `v : σ → T` to `fun o => Option.elim o (a : T) (fun x => g x.1 x.2.1 x.2.2)`. Set `φ : P →ₐ[K] T` to `MvPolynomial.aevalTower ψ v`. Establish `hφY : ∀ τ, (Y τ).map φ = g τ`. Introduce `τ`. Use extensionality with `i j`.

Simplify using `[φ, Y, v, P]`. Establish `hφs : φ (MvPolynomial.X none) = a` using `by simp [φ, v, P]`. Establish `hφd : IsUnit (φ d)`. Simplify using `only [d, map_mul, map_prod, hφs]`. Use `a.isUnit.mul (IsUnit.prod_univ_iff.2 fun τ => ?_)` and prove the remaining obligations.

Rewrite using `[AlgHom.map_det]`. Use `hg τ` as an intermediate fact. Rewrite `this` using `[← hφY τ]`. Conclude with `this`. Set `k : A →ₐ[K] T` to `IsLocalization.liftAlgHom (M := Submonoid.powers d) (f := φ) (by`.

Introduce and unpack `⟨_, n, rfl⟩`. Simplify using `using hφd.pow n)`. Establish `hk : ∀ x : P, k (algebraMap P A x) = φ x` using `fun x => by simp [k]`. Use `⟨k, ⟨?_, fun τ => ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `x`.

Express the relevant statement in the definitionally equal form `k (algebraMap R A x) = ψ x`. Rewrite using `[IsScalarTower.algebraMap_apply R P A, hk]`. Simplify using `[φ, P]`. Rewrite using `[← hφY τ]`. Use extensionality with `i j`.

Simplify using `[hk]`. Simplify using `[hk, hφs]`. Introduce and unpack `k' ⟨h1, h2, h3⟩`. Establish `key : (k' : A →+* T).comp (algebraMap P A) = (φ : P →+* T)`. Use `MvPolynomial.ringHom_ext (fun r => ?_) (fun o => ?_)` and prove the remaining obligations.

Use `AlgHom.congr_fun h1 r` as an intermediate fact. Express the relevant statement in the definitionally equal form `k' (algebraMap R A r) = ψ r at this`. Rewrite `this` using `[IsScalarTower.algebraMap_apply R P A]`. Establish `h' : φ (MvPolynomial.C r) = ψ r` using `by simp [φ, P]`. Conclude with `this.trans h'.symm`.

Break down `o with _ | ⟨τ, i, j⟩` into its components or cases. Conclude with `h3.trans hφs.symm`. Establish `a1` using `congrFun (congrFun (h2 τ) i) j`. Establish `a2` using `congrFun (congrFun (hφY τ) i) j`. Conclude with `a1.trans a2.symm`.

Apply `AlgHom.coe_ringHom_injective` to reduce the goal to its premises. Apply `IsLocalization.ringHom_ext (Submonoid.powers d)` to reduce the goal to its premises. Rewrite using `[key]`. Use extensionality with `x`. Conclude with `(hk _).symm`.

Conclude with `(hk _).symm`.
-/
theorem exists_frameRing_reduced {K : Type} [Field K] {J : Type} [Fintype J] (m : J → ℕ) (R : Type) [CommRing R]
    [Algebra K R] [Algebra.FiniteType K R] [IsReduced R] :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra K A) (π : R →ₐ[K] A)
      (X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A) (s : Aˣ),
      Algebra.FiniteType K A ∧ IsReduced A ∧ FrameRing m π X s := by
  let σ := Option (Σ τ, Fin (m τ) × Fin (m τ))
  let P := MvPolynomial σ R
  let Y : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) P := fun τ => Matrix.of fun i j => MvPolynomial.X (some ⟨τ, i, j⟩)
  let d : P := MvPolynomial.X none * ∏ τ, (Y τ).det
  let A := Localization.Away d
  have hd : IsUnit (algebraMap P A d) := IsLocalization.Away.algebraMap_isUnit d
  have hs : IsUnit (algebraMap P A (MvPolynomial.X none)) := by
    exact isUnit_of_dvd_unit (map_dvd (algebraMap P A) (dvd_mul_right _ _)) hd
  have hY : ∀ τ, IsUnit (algebraMap P A (Y τ).det) := by
    intro τ
    have h0 : (Y τ).det ∣ d :=
      Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun τ => (Y τ).det) (Finset.mem_univ τ)) _
    exact isUnit_of_dvd_unit (map_dvd (algebraMap P A) h0) hd
  have hPred : IsReduced P := inferInstance
  have hPft : Algebra.FiniteType R P := inferInstance
  have hAft : Algebra.FiniteType P A := inferInstance
  have hPft' : Algebra.FiniteType K P := Algebra.FiniteType.trans inferInstance hPft
  refine ⟨A, inferInstance, inferInstance, IsScalarTower.toAlgHom K R A, fun τ => (Y τ).map (algebraMap P A),
    hs.unit, Algebra.FiniteType.trans hPft' hAft, inferInstance, fun τ => ?_, fun T _ _ ψ g a hg => ?_⟩
  · have := hY τ
    rw [RingHom.map_det] at this
    exact this
  · let v : σ → T := fun o => Option.elim o (a : T) (fun x => g x.1 x.2.1 x.2.2)
    let φ : P →ₐ[K] T := MvPolynomial.aevalTower ψ v
    have hφY : ∀ τ, (Y τ).map φ = g τ := by
      intro τ; ext i j
      simp [φ, Y, v, P]
    have hφs : φ (MvPolynomial.X none) = a := by simp [φ, v, P]
    have hφd : IsUnit (φ d) := by
      simp only [d, map_mul, map_prod, hφs]
      refine a.isUnit.mul (IsUnit.prod_univ_iff.2 fun τ => ?_)
      rw [AlgHom.map_det]
      have := hg τ
      rw [← hφY τ] at this
      exact this
    let k : A →ₐ[K] T := IsLocalization.liftAlgHom (M := Submonoid.powers d) (f := φ) (by
      rintro ⟨_, n, rfl⟩
      simpa using hφd.pow n)
    have hk : ∀ x : P, k (algebraMap P A x) = φ x := fun x => by simp [k]
    refine ⟨k, ⟨?_, fun τ => ?_, ?_⟩, ?_⟩
    · ext x
      change k (algebraMap R A x) = ψ x
      rw [IsScalarTower.algebraMap_apply R P A, hk]
      simp [φ, P]
    · rw [← hφY τ]; ext i j; simp [hk]
    · simp [hk, hφs]
    · rintro k' ⟨h1, h2, h3⟩
      have key : (k' : A →+* T).comp (algebraMap P A) = (φ : P →+* T) := by
        refine MvPolynomial.ringHom_ext (fun r => ?_) (fun o => ?_)
        · have := AlgHom.congr_fun h1 r
          change k' (algebraMap R A r) = ψ r at this
          rw [IsScalarTower.algebraMap_apply R P A] at this
          have h' : φ (MvPolynomial.C r) = ψ r := by simp [φ, P]
          exact this.trans h'.symm
        · rcases o with _ | ⟨τ, i, j⟩
          · exact h3.trans hφs.symm
          · have a1 := congrFun (congrFun (h2 τ) i) j
            have a2 := congrFun (congrFun (hφY τ) i) j
            exact a1.trans a2.symm
      apply AlgHom.coe_ringHom_injective
      apply IsLocalization.ringHom_ext (Submonoid.powers d)
      rw [key]
      ext x
      · exact (hk _).symm
      · exact (hk _).symm

/- English proof (translation)
Introduce `K _ J _ m p`. Take `⟨h1, h2⟩` from `(reduced_finiteType_iff_testRing K).2 p`. Take `⟨A, _, _, π, X, s, hft, hred, hF⟩` from `exists_frameRing_reduced (K := K) m p.R`. Take `⟨q, ⟨e⟩⟩` from `(reduced_finiteType_iff_testRing K).1 A hft hred`. Conclude with `⟨q, _, _, _, FrameRing_of_algEquiv m π X s hF e.symm⟩`.
-/
theorem exists_frameRing_testRing :
    ∀ (K : Type) [Field K] (J : Type) [Fintype J] (m : J → ℕ) (p : TRing K), ∃ (A : TRing K) (π : p.R →ₐ[K] A.R) (X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A.R) (s : (A.R)ˣ), FrameRing m π X s := by
  intro K _ J _ m p
  obtain ⟨h1, h2⟩ := (reduced_finiteType_iff_testRing K).2 p
  obtain ⟨A, _, _, π, X, s, hft, hred, hF⟩ := exists_frameRing_reduced (K := K) m p.R
  obtain ⟨q, ⟨e⟩⟩ := (reduced_finiteType_iff_testRing K).1 A hft hred
  exact ⟨q, _, _, _, FrameRing_of_algEquiv m π X s hF e.symm⟩

end GlobalTheory
