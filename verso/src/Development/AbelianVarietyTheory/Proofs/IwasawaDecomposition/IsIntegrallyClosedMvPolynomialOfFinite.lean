import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
open GlobalTheory.Frames

namespace GlobalTheory

/- English proof (translation)
Establish `h : ∀ n : ℕ, IsIntegrallyClosed (MvPolynomial (Fin n) R)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => exact IsIntegrallyClosed.of_equiv (MvPolynomial.isEmptyRingEquiv R (Fin 0)).symm`. Consider the case `succ n ih => exact IsIntegrallyClosed.of_equiv (MvPolynomial.finSuccEquiv R n).symm.toRingEquiv`.

Take `⟨n, ⟨e⟩⟩` from `Finite.exists_equiv_fin σ`. Use `h n` as an intermediate fact. Conclude with `IsIntegrallyClosed.of_equiv (MvPolynomial.renameEquiv R e).symm.toRingEquiv`.
-/
theorem isIntegrallyClosed_mvPolynomial_of_finite (σ : Type) [Finite σ] (R : Type) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] : IsIntegrallyClosed (MvPolynomial σ R) := by
  have h : ∀ n : ℕ, IsIntegrallyClosed (MvPolynomial (Fin n) R) := by
    intro n
    induction n with
    | zero => exact IsIntegrallyClosed.of_equiv (MvPolynomial.isEmptyRingEquiv R (Fin 0)).symm
    | succ n ih => exact IsIntegrallyClosed.of_equiv (MvPolynomial.finSuccEquiv R n).symm.toRingEquiv
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  have := h n
  exact IsIntegrallyClosed.of_equiv (MvPolynomial.renameEquiv R e).symm.toRingEquiv

/- English proof (translation)
Introduce `K _ J _ m R _ _ _ _`. Set `σ` to `Option (Σ τ, Fin (m τ) × Fin (m τ))`. Set `P` to `MvPolynomial σ R`. Set `Y : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) P` to `fun τ => Matrix.of fun i j => MvPolynomial.X (some ⟨τ, i, j⟩)`. Set `d : P` to `MvPolynomial.X none * ∏ τ, (Y τ).det`.

Set `A` to `Localization.Away d`. Establish `hd : IsUnit (algebraMap P A d)` using `IsLocalization.Away.algebraMap_isUnit d`. Establish `hs : IsUnit (algebraMap P A (MvPolynomial.X none))`. Conclude with `isUnit_of_dvd_unit (map_dvd (algebraMap P A) (dvd_mul_right _ _)) hd`. Establish `hY : ∀ τ, IsUnit (algebraMap P A (Y τ).det)`.

Introduce `τ`. Establish `h0 : (Y τ).det ∣ d` using `Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun τ => (Y τ).det) (Finset.mem_univ τ)) _`. Conclude with `isUnit_of_dvd_unit (map_dvd (algebraMap P A) h0) hd`. Establish `hd0 : d ≠ 0`. Introduce `h0`.

Set `w : σ → R` to `fun o => Option.elim o 1 (fun x => (1 : Matrix (Fin (m x.1)) (Fin (m x.1)) R) x.2.1 x.2.2)`. Set `ev : P →+* R` to `MvPolynomial.eval w`. Establish `h1 : ∀ τ, ev.mapMatrix (Y τ) = 1`. Introduce `τ`. Use extensionality with `i j`.

Simplify using `[ev, Y, w, P]`. Establish `h2 : ev d = 1`. Simplify using `only [d, map_mul, map_prod, RingHom.map_det, h1, Matrix.det_one, Finset.prod_const_one, mul_one]`. Simplify using `[ev, w, P]`. Rewrite `h2` using `[h0, map_zero]`.

Conclude with `zero_ne_one h2`. Establish `hle : Submonoid.powers d ≤ nonZeroDivisors P` using `powers_le_nonZeroDivisors_of_noZeroDivisors hd0`. Establish `hdom : IsDomain A` using `IsLocalization.isDomain_localization hle`. Establish `hP : IsIntegrallyClosed P` using `isIntegrallyClosed_mvPolynomial_of_finite σ R`. Establish `hA : IsIntegrallyClosed A` using `isIntegrallyClosed_of_isLocalization A _ hle`.

Use `⟨A, inferInstance, inferInstance, hdom, IsScalarTower.toAlgHom K R A, fun τ => (Y τ).map (algebraMap P A), hs.unit, hA, fun τ => ?_, fun T _ _ ψ g a hg => ?_⟩` and prove the remaining obligations. Use `hY τ` as an intermediate fact. Rewrite `this` using `[RingHom.map_det]`. Conclude with `this`. Set `v : σ → T` to `fun o => Option.elim o (a : T) (fun x => g x.1 x.2.1 x.2.2)`.

Set `φ : P →ₐ[K] T` to `MvPolynomial.aevalTower ψ v`. Establish `hφY : ∀ τ, (Y τ).map φ = g τ`. Introduce `τ`. Use extensionality with `i j`. Simplify using `[φ, Y, v, P]`.

Establish `hφs : φ (MvPolynomial.X none) = a` using `by simp [φ, v, P]`. Establish `hφd : IsUnit (φ d)`. Simplify using `only [d, map_mul, map_prod, hφs]`. Use `a.isUnit.mul (IsUnit.prod_univ_iff.2 fun τ => ?_)` and prove the remaining obligations. Rewrite using `[AlgHom.map_det]`.

Use `hg τ` as an intermediate fact. Rewrite `this` using `[← hφY τ]`. Conclude with `this`. Set `k : A →ₐ[K] T` to `IsLocalization.liftAlgHom (M := Submonoid.powers d) (f := φ) (by`. Introduce and unpack `⟨_, n, rfl⟩`.

Simplify using `using hφd.pow n)`. Establish `hk : ∀ x : P, k (algebraMap P A x) = φ x` using `fun x => by simp [k]`. Use `⟨k, ⟨?_, fun τ => ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `k (algebraMap R A x) = ψ x`.

Rewrite using `[IsScalarTower.algebraMap_apply R P A, hk]`. Simplify using `[φ, P]`. Rewrite using `[← hφY τ]`. Use extensionality with `i j`. Simplify using `[hk]`.

Simplify using `[hk, hφs]`. Introduce and unpack `k' ⟨h1, h2, h3⟩`. Establish `key : (k' : A →+* T).comp (algebraMap P A) = (φ : P →+* T)`. Use `MvPolynomial.ringHom_ext (fun r => ?_) (fun o => ?_)` and prove the remaining obligations. Use `AlgHom.congr_fun h1 r` as an intermediate fact.

Express the relevant statement in the definitionally equal form `k' (algebraMap R A r) = ψ r at this`. Rewrite `this` using `[IsScalarTower.algebraMap_apply R P A]`. Establish `h' : φ (MvPolynomial.C r) = ψ r` using `by simp [φ, P]`. Conclude with `this.trans h'.symm`. Break down `o with _ | ⟨τ, i, j⟩` into its components or cases.

Conclude with `h3.trans hφs.symm`. Establish `a1` using `congrFun (congrFun (h2 τ) i) j`. Establish `a2` using `congrFun (congrFun (hφY τ) i) j`. Conclude with `a1.trans a2.symm`. Apply `AlgHom.coe_ringHom_injective` to reduce the goal to its premises.

Apply `IsLocalization.ringHom_ext (Submonoid.powers d)` to reduce the goal to its premises. Rewrite using `[key]`. Use extensionality with `x`. Conclude with `(hk _).symm`. Conclude with `(hk _).symm`.
-/
theorem exists_frameRing_integrallyClosed :
    ∀ (K : Type) [Field K] (J : Type) [Fintype J] (m : J → ℕ) (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Algebra K R], ∃ (A : Type) (_ : CommRing A) (_ : Algebra K A) (_ : IsDomain A) (π : R →ₐ[K] A) (X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A) (s : Aˣ), IsIntegrallyClosed A ∧ FrameRing m π X s := by
  intro K _ J _ m R _ _ _ _
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
  have hd0 : d ≠ 0 := by
    intro h0
    let w : σ → R := fun o => Option.elim o 1 (fun x => (1 : Matrix (Fin (m x.1)) (Fin (m x.1)) R) x.2.1 x.2.2)
    let ev : P →+* R := MvPolynomial.eval w
    have h1 : ∀ τ, ev.mapMatrix (Y τ) = 1 := by
      intro τ; ext i j
      simp [ev, Y, w, P]
    have h2 : ev d = 1 := by
      simp only [d, map_mul, map_prod, RingHom.map_det, h1, Matrix.det_one, Finset.prod_const_one, mul_one]
      simp [ev, w, P]
    rw [h0, map_zero] at h2
    exact zero_ne_one h2
  have hle : Submonoid.powers d ≤ nonZeroDivisors P := powers_le_nonZeroDivisors_of_noZeroDivisors hd0
  have hdom : IsDomain A := IsLocalization.isDomain_localization hle
  have hP : IsIntegrallyClosed P := isIntegrallyClosed_mvPolynomial_of_finite σ R
  have hA : IsIntegrallyClosed A := isIntegrallyClosed_of_isLocalization A _ hle
  refine ⟨A, inferInstance, inferInstance, hdom, IsScalarTower.toAlgHom K R A,
    fun τ => (Y τ).map (algebraMap P A), hs.unit, hA, fun τ => ?_, fun T _ _ ψ g a hg => ?_⟩
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

end GlobalTheory
