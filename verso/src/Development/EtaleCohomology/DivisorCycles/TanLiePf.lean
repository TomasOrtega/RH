import Development.EtaleCohomology.DivisorCycles.OpenCoset

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.TanLiePf
open LateralTheory.DivDb

/- English proof (translation)
Simplify using `[DX, MvPolynomial.mkDerivation_X]`.
-/
theorem DX_X {C : Type} [Field C] {N : ℕ} (Y : Mat C N) (p : Fin N × Fin N) :
    DX Y (MvPolynomial.X p) = ∑ k, MvPolynomial.C (Y p.1 k) * MvPolynomial.X (k, p.2) := by
  simp [DX, MvPolynomial.mkDerivation_X]

/- English proof (translation)
Apply `MvPolynomial.derivation_ext` to reduce the goal to its premises. Introduce `p`. Rewrite using `[Derivation.commutator_apply, DX_X, DX_X, DX_X]`. Simplify using `only [map_sum, MvPolynomial.C_mul', map_smul, DX_X, Finset.smul_sum, smul_smul]`. Simplify using `only [Matrix.sub_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib]`.

Simplify using `only [sub_smul, Finset.sum_smul, ← Finset.sum_sub_distrib]`. Rewrite using `[Finset.sum_comm]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `a _`. Rewrite using `[Derivation.map_smul, Derivation.map_smul, DX_X, DX_X]`.

Simplify using `only [MvPolynomial.C_mul', Finset.smul_sum, smul_smul, ← Finset.sum_sub_distrib]`.
-/
theorem DX_comm {C : Type} [Field C] {N : ℕ} (Y Z : Mat C N) :
    ⁅DX Y, DX Z⁆ = DX (Z * Y - Y * Z) := by
  apply MvPolynomial.derivation_ext
  intro p
  rw [Derivation.commutator_apply, DX_X, DX_X, DX_X]
  simp only [map_sum, MvPolynomial.C_mul', map_smul, DX_X, Finset.smul_sum, smul_smul]
  simp only [Matrix.sub_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib]
  simp only [sub_smul, Finset.sum_smul, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  rw [Derivation.map_smul, Derivation.map_smul, DX_X, DX_X]
  simp only [MvPolynomial.C_mul', Finset.smul_sum, smul_smul, ← Finset.sum_sub_distrib]

end LateralTheory.DivDb.TanLiePf

namespace LateralTheory.DivDb
open LateralTheory.DivDb.TanLiePf

/- English proof (translation)
Introduce `C _ N S Y hY Z hZ`. Establish `hY'` using `(hF C N S Y).1 hY`. Establish `hZ'` using `(hF C N S Z).1 hZ`. Establish `h : Z * Y - Y * Z ∈ Tan (S : Set (Mat C N))`. Rewrite using `[hF C N S]`.

Introduce `f hf`. Rewrite using `[← DX_comm, Derivation.commutator_apply]`. Introduce `x hx`. Establish `h1` using `hY' _ (hZ' f hf) x hx`. Establish `h2` using `hZ' _ (hY' f hf) x hx`.

Simplify using `only [ev, map_sub] at h1 h2 ⊢`. Rewrite using `[h1, h2, sub_zero]`. Use `(Tan (S : Set (Mat C N))).neg_mem h` as an intermediate fact. Simplify using `using this`.
-/
theorem TanLie_of (hF : TanField) : TanLie := by
  intro C _ N S Y hY Z hZ
  have hY' := (hF C N S Y).1 hY
  have hZ' := (hF C N S Z).1 hZ
  have h : Z * Y - Y * Z ∈ Tan (S : Set (Mat C N)) := by
    rw [hF C N S]
    intro f hf
    rw [← DX_comm, Derivation.commutator_apply]
    intro x hx
    have h1 := hY' _ (hZ' f hf) x hx
    have h2 := hZ' _ (hY' f hf) x hx
    simp only [ev, map_sub] at h1 h2 ⊢
    rw [h1, h2, sub_zero]
  have := (Tan (S : Set (Mat C N))).neg_mem h
  simpa using this

end LateralTheory.DivDb
