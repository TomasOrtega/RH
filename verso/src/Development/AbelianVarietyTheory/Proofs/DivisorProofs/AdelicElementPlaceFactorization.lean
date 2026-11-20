import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPlaceDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStableAlmostAllPlacesRight
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.AdelicPlaceDecomp

open Matrix GlobalTheory.UnitaryPlaceSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def idemInf : AF F := LinearMap.inl F (Ainf F) (Af F) 1

/- English proof (translation)
Rewrite using `[map_sub, map_one, evFin_idemAt, sub_self]`.
-/
theorem evFin_one_sub_idemAt (w : Pl F) : evFin F w (1 - idemAt w) = 0 := by
  rw [map_sub, map_one, evFin_idemAt, sub_self]

def cOff (L : List (Pl F)) : AF F := (L.map fun w => 1 - idemAt w).prod

end GlobalTheory.AdelicPlaceDecomp

namespace GlobalTheory.AdelicPlaceDecomp

open Matrix GlobalTheory.UnitaryPlaceSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end GlobalTheory.AdelicPlaceDecomp

namespace GlobalTheory.AdelicPlaceDecomp

open Matrix GlobalTheory.UnitaryPlaceSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Introduce `γ hγ`. Proceed by induction on `hγ using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, -, x, -, y, -, rfl⟩` from `hz`. Establish `h1 : (1 - idemAt w) • a = 0` using `ha _ (evFin_one_sub_idemAt w)`.

Rewrite `h1` using `[smul_eq_mul, sub_mul, one_mul, sub_eq_zero]`. Rewrite using `[smul_smul, ← h1]`. Consider the case `zero => rw [smul_zero]`. Consider the case `add x y _ _ hx hy => rw [smul_add, hx, hy]`. Consider the case `neg x _ hx => rw [smul_neg, hx]`.
-/
theorem idemAt_smul_of_mem_latAtV {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (w : Pl F) :
    ∀ γ ∈ latAtV X Y w, idemAt w • γ = γ := by
  intro γ hγ
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, -, x, -, y, -, rfl⟩ := hz
    have h1 : (1 - idemAt w) • a = 0 := ha _ (evFin_one_sub_idemAt w)
    rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h1
    rw [smul_smul, ← h1]
  | zero => rw [smul_zero]
  | add x y _ _ hx hy => rw [smul_add, hx, hy]
  | neg x _ hx => rw [smul_neg, hx]

/- English proof (translation)
Establish `hK' : K = s • (H - 1) + 1` using `sub_eq_iff_eq_add.1 hK`. Establish `hY : e • (δ * (H - 1)ᵀ) = δ * (H - 1)ᵀ` using `by rw [← Matrix.smul_mul, hδ]`. Establish `h2 : s • (δ * (H - 1)ᵀ) = δ * (H - 1)ᵀ` using `by rw [← hY, smul_smul, hs]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hK', transpose_add, transpose_smul, transpose_one, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]`.

Use `_ = δ * (H - 1)ᵀ + δ := by rw [h2]`. Use `_ = δ * Hᵀ := by rw [transpose_sub, transpose_one, Matrix.mul_sub, Matrix.mul_one, sub_add_cancel]`.
-/
theorem mul_transpose_eq {n d : ℕ} {e s : AF F} (hs : s * e = e) {δ : Matrix (Fin n) (Fin d) (AE F E)}
    (hδ : e • δ = δ) {K H : Matrix (Fin d) (Fin d) (AE F E)} (hK : K - 1 = s • (H - 1)) : δ * Kᵀ = δ * Hᵀ := by
  have hK' : K = s • (H - 1) + 1 := sub_eq_iff_eq_add.1 hK
  have hY : e • (δ * (H - 1)ᵀ) = δ * (H - 1)ᵀ := by rw [← Matrix.smul_mul, hδ]
  have h2 : s • (δ * (H - 1)ᵀ) = δ * (H - 1)ᵀ := by rw [← hY, smul_smul, hs]
  calc δ * Kᵀ = s • (δ * (H - 1)ᵀ) + δ := by
        rw [hK', transpose_add, transpose_smul, transpose_one, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
    _ = δ * (H - 1)ᵀ + δ := by rw [h2]
    _ = δ * Hᵀ := by rw [transpose_sub, transpose_one, Matrix.mul_sub, Matrix.mul_one, sub_add_cancel]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hγ`. Establish `h` using `s2 _ hγ`. Rewrite `h` using `[← mul_transpose_eq hs (idemAt_smul_of_mem_latAtV X Y w _ hγ) hKi, Matrix.mul_assoc, ← transpose_mul, hKK, transpose_one, Matrix.mul_one]`. Then use the resulting hypothesis. Introduce `hγ`.

Rewrite using `[mul_transpose_eq hs (idemAt_smul_of_mem_latAtV X Y w _ hγ) hK]`. Conclude with `s1 _ hγ`.
-/
theorem mul_transpose_mem_iff {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (w : Pl F) {s : AF F}
    (hs : s * idemAt w = idemAt w) {K Ki H Hi : Matrix (Fin d) (Fin d) (AE F E)} (hK : K - 1 = s • (H - 1))
    (hKi : Ki - 1 = s • (Hi - 1)) (hKK : Ki * K = 1) (s1 : ∀ γ ∈ latAtV X Y w, γ * Hᵀ ∈ latAtV X Y w)
    (s2 : ∀ γ ∈ latAtV X Y w, γ * Hiᵀ ∈ latAtV X Y w) (γ : Matrix (Fin n) (Fin d) (AE F E)) :
    γ * Kᵀ ∈ latAtV X Y w ↔ γ ∈ latAtV X Y w := by
  constructor
  · intro hγ
    have h := s2 _ hγ
    rwa [← mul_transpose_eq hs (idemAt_smul_of_mem_latAtV X Y w _ hγ) hKi, Matrix.mul_assoc, ← transpose_mul, hKK,
      transpose_one, Matrix.mul_one] at h
  · intro hγ
    rw [mul_transpose_eq hs (idemAt_smul_of_mem_latAtV X Y w _ hγ) hK]
    exact s1 _ hγ

end GlobalTheory.AdelicPlaceDecomp

namespace GlobalTheory.AdelicPlaceDecomp

open Matrix GlobalTheory.UnitaryPlaceSplit

end GlobalTheory.AdelicPlaceDecomp

end
