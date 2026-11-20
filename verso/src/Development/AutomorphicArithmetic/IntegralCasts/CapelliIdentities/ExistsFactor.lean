import Mathlib

/- English proof (translation)
Introduce `K _ n e he`. Set `f : (Fin n → K) →ₗ[K] (Fin n → K)` to `Matrix.toLin' e`. Establish `hf : ∀ v, f (f v) = f v`. Introduce `v`. Establish `h : f.comp f = f` using `by show (Matrix.toLin' e).comp (Matrix.toLin' e) = Matrix.toLin' e`.

Rewrite using `[← Matrix.toLin'_mul, he]`. Conclude with `LinearMap.congr_fun h v`. Set `b` to `Module.finBasis K (LinearMap.range f)`. Set `c` to `Pi.basisFun K (Fin n)`. Use `⟨Module.finrank K (LinearMap.range f), LinearMap.toMatrix b c (LinearMap.range f).subtype, LinearMap.toMatrix c b f.rangeRestrict, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← LinearMap.toMatrix_comp]`. Establish `h : f.rangeRestrict.comp (LinearMap.range f).subtype = LinearMap.id`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce and unpack `⟨x, v, rfl⟩`. Apply `Subtype.ext` to reduce the goal to its premises.

Conclude with `hf v`. Rewrite using `[h, LinearMap.toMatrix_id]`. Rewrite using `[← LinearMap.toMatrix_comp]`. Establish `h : (LinearMap.range f).subtype.comp f.rangeRestrict = f`. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `v`. Both sides reduce to the same expression. Rewrite using `[h]`. Use `show LinearMap.toMatrix (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin n)) (Matrix.toLin' e) = e`. Rewrite using `[LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']`.
-/
theorem UpperTheory.Reformulated.B.ExistsFactor.exists_factor :
    ∀ {K : Type} [inst : Field K] {n : ℕ} (e : Matrix (Fin n) (Fin n) K),
    e * e = e →
      ∃ (r : ℕ) (M : Matrix (Fin n) (Fin r) K) (N : Matrix (Fin r) (Fin n) K),
        N * M = (1 : Matrix (Fin r) (Fin r) K) ∧ M * N = e := by
  intro K _ n e he
  let f : (Fin n → K) →ₗ[K] (Fin n → K) := Matrix.toLin' e
  have hf : ∀ v, f (f v) = f v := by
    intro v
    have h : f.comp f = f := by
      show (Matrix.toLin' e).comp (Matrix.toLin' e) = Matrix.toLin' e
      rw [← Matrix.toLin'_mul, he]
    exact LinearMap.congr_fun h v
  let b := Module.finBasis K (LinearMap.range f)
  let c := Pi.basisFun K (Fin n)
  refine ⟨Module.finrank K (LinearMap.range f),
    LinearMap.toMatrix b c (LinearMap.range f).subtype,
    LinearMap.toMatrix c b f.rangeRestrict, ?_, ?_⟩
  · rw [← LinearMap.toMatrix_comp]
    have h : f.rangeRestrict.comp (LinearMap.range f).subtype = LinearMap.id := by
      apply LinearMap.ext
      rintro ⟨x, v, rfl⟩
      apply Subtype.ext
      exact hf v
    rw [h, LinearMap.toMatrix_id]
  · rw [← LinearMap.toMatrix_comp]
    have h : (LinearMap.range f).subtype.comp f.rangeRestrict = f := by
      apply LinearMap.ext
      intro v
      rfl
    rw [h]
    show LinearMap.toMatrix (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin n)) (Matrix.toLin' e) = e
    rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
