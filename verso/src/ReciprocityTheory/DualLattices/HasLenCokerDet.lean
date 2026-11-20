import ReciprocityTheory.DualLattices.LenIdBStatement
import ReciprocityTheory.DualLattices.UpSmith

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

/- English proof (translation)
Take `⟨k, c, ⟨f⟩, hx⟩` from `h`. Conclude with `⟨k, c, ⟨e.trans f⟩, hx⟩`.
-/
lemma hasLen_of_equiv {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) {x : NNReal} (h : HasLen v R N x) : HasLen v R M x := by
  obtain ⟨k, c, ⟨f⟩, hx⟩ := h
  exact ⟨k, c, ⟨e.trans f⟩, hx⟩

/- English proof (translation)
Use `set e := Fintype.equivFin κ`. Use `set X' := X.submatrix e.symm e.symm`. Establish `hdet : X'.det = X.det` using `Matrix.det_submatrix_equiv_self e.symm X`. Set `Φ : (κ → R) ≃ₗ[R] (Fin (Fintype.card κ) → R)` to `LinearEquiv.funCongrLeft R R e.symm`. Establish `hrange : (LinearMap.range X.mulVecLin).map (Φ : (κ → R) →ₗ[R] (Fin (Fintype.card κ) → R)) = LinearMap.range X'.mulVecLin`.

Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨y, rfl⟩, rfl⟩`. Use `⟨y ∘ e.symm, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Use `show (X' *ᵥ (y ∘ e.symm)) i = (X *ᵥ y) (e.symm i)`. Simplify using `only [X', Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Function.comp_apply]`. Conclude with `Equiv.sum_comp e.symm (fun k => X (e.symm i) k * y k)`. Introduce and unpack `⟨y, rfl⟩`. Use `⟨X *ᵥ (y ∘ e), ⟨y ∘ e, rfl⟩, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mulVecLin_apply, X', Matrix.submatrix_mulVec_equiv, Φ, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Function.comp_apply]`. Simplify using the standard rewrite rules. Establish `h` using `Smith.hasLen_coker_det hv X'`. Rewrite `h` using `[hdet]`.

Conclude with `hasLen_of_equiv (Submodule.Quotient.equiv _ _ Φ hrange) h`.
-/
theorem hasLen_coker_det' {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (hv : v.Integers R) (κ : Type) [Fintype κ] [DecidableEq κ] (X : Matrix κ κ R) :
    HasLen v R ((κ → R) ⧸ LinearMap.range X.mulVecLin) (v (algebraMap R C X.det)) := by
  set e := Fintype.equivFin κ
  set X' := X.submatrix e.symm e.symm
  have hdet : X'.det = X.det := Matrix.det_submatrix_equiv_self e.symm X
  let Φ : (κ → R) ≃ₗ[R] (Fin (Fintype.card κ) → R) := LinearEquiv.funCongrLeft R R e.symm
  have hrange : (LinearMap.range X.mulVecLin).map (Φ : (κ → R) →ₗ[R] (Fin (Fintype.card κ) → R)) =
      LinearMap.range X'.mulVecLin := by
    ext z
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      refine ⟨y ∘ e.symm, ?_⟩
      funext i
      show (X' *ᵥ (y ∘ e.symm)) i = (X *ᵥ y) (e.symm i)
      simp only [X', Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Function.comp_apply]
      exact Equiv.sum_comp e.symm (fun k => X (e.symm i) k * y k)
    · rintro ⟨y, rfl⟩
      refine ⟨X *ᵥ (y ∘ e), ⟨y ∘ e, rfl⟩, ?_⟩
      funext i
      simp only [Matrix.mulVecLin_apply, X', Matrix.submatrix_mulVec_equiv, Φ,
        LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Function.comp_apply]
      simp
  have h := Smith.hasLen_coker_det hv X'
  rw [hdet] at h
  exact hasLen_of_equiv (Submodule.Quotient.equiv _ _ Φ hrange) h

/- English proof (translation)
The claim follows from `lenId_of (fun C _ v R _ _ hv => hasLen_coker_det' v R hv) hB`.
-/
theorem lenId_of_B (hB : LenIdBStatement) : LenIdStatement :=
  lenId_of (fun C _ v R _ _ hv => hasLen_coker_det' v R hv) hB

/- English proof (translation)
The claim follows from `hasLen_ext (hasLen_coker_det' v R hv) ι π hι hπ hex ha hc`.
-/
theorem hasLen_ext' {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] (hv : v.Integers R)
    {A B D : Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup D]
    [Module R D] (ι : A →ₗ[R] B) (π : B →ₗ[R] D) (hι : Function.Injective ι)
    (hπ : Function.Surjective π) (hex : LinearMap.range ι = LinearMap.ker π) {a c : NNReal}
    (ha : HasLen v R A a) (hc : HasLen v R D c) : HasLen v R B (a * c) :=
  hasLen_ext (hasLen_coker_det' v R hv) ι π hι hπ hex ha hc

end ReciprocityTheory.PGsh.Up
