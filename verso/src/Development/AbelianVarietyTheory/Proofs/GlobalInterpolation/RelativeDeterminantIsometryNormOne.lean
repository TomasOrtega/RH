import Mathlib
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.L2.Ker

namespace GlobalTheory

/- English proof (translation)
Use `set A := LinearMap.toMatrix' φ with hA`. Establish `key : ((algebraMap K E).mapMatrix A).transpose * (cj.mapMatrix ((algebraMap K E).mapMatrix A)) = 1`. Use extensionality with `i j`. Use `h (Pi.single i 1) (Pi.single j 1)` as an intermediate fact. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply, hA, LinearMap.toMatrix'_apply]`.

Rewrite using `[this, Finset.sum_eq_single i]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hij]`.

Introduce `b _ hb`. Simplify using `[Pi.single_apply, hb]`. Simplify using the standard rewrite rules. Establish `hd` using `congrArg Matrix.det key`. Rewrite `hd` using `[Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, ← RingHom.map_det, ← RingHom.map_det, ← RingHom.map_det, hA, LinearMap.det_toMatrix']`.

Conclude with `hd`.
-/
theorem det_mul_conj_eq_one_of_preserves {K E : Type} [Field K] [Field E] [Algebra K E] (cj : E →+* E)
    {n : Type} [Fintype n] [DecidableEq n] (φ : (n → K) →ₗ[K] (n → K))
    (h : ∀ v u : n → K, ∑ w, algebraMap K E (φ v w) * cj (algebraMap K E (φ u w))
      = ∑ w, algebraMap K E (v w) * cj (algebraMap K E (u w))) :
    algebraMap K E (LinearMap.det φ) * cj (algebraMap K E (LinearMap.det φ)) = 1 := by
  set A := LinearMap.toMatrix' φ with hA
  have key : ((algebraMap K E).mapMatrix A).transpose * (cj.mapMatrix ((algebraMap K E).mapMatrix A)) = 1 := by
    ext i j
    have := h (Pi.single i 1) (Pi.single j 1)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply, hA,
      LinearMap.toMatrix'_apply]
    rw [this, Finset.sum_eq_single i]
    · by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  have hd := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, ← RingHom.map_det, ← RingHom.map_det, ← RingHom.map_det, hA,
    LinearMap.det_toMatrix'] at hd
  exact hd

/- English proof (translation)
Use `det_mul_conj_eq_one_of_preserves (K := D.host.K) (E := D.host.E) (D.host.conj : D.host.E →+* D.host.E) _ ?_` and prove the remaining obligations. Introduce `v u`. Establish `h1` using `γ.isom (γ₀.g.symm v) (γ₀.g.symm u)`. Establish `h2` using `γ₀.isom (γ₀.g.symm v) (γ₀.g.symm u)`. Simplify using `only [LinearEquiv.apply_symm_apply] at h2`.

Conclude with `h1.trans h2.symm`.
-/
theorem detRel_mul_conj_eq_one (D : D7) (γ₀ γ : IsoK D) :
    ((γ.detRel γ₀ : D.host.K) : D.host.E) * D.host.conj ((γ.detRel γ₀ : D.host.K) : D.host.E) = 1 := by
  refine det_mul_conj_eq_one_of_preserves (K := D.host.K) (E := D.host.E) (D.host.conj : D.host.E →+* D.host.E) _ ?_
  intro v u
  have h1 := γ.isom (γ₀.g.symm v) (γ₀.g.symm u)
  have h2 := γ₀.isom (γ₀.g.symm v) (γ₀.g.symm u)
  simp only [LinearEquiv.apply_symm_apply] at h2
  exact h1.trans h2.symm

end GlobalTheory
