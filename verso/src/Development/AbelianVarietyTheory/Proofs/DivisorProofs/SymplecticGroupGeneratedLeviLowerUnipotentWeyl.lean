import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

open private exists_symmetric_X_isUnit_det_add_mul_of_symplectic from Mathlib.LinearAlgebra.SymplecticGroup

namespace GlobalTheory.SpGen
open Matrix

/- English proof (translation)
Simplify using `[fromBlocks_multiply]`.
-/
theorem upper_unipotent_eq {K : Type} [Field K] {κ : Type} [Fintype κ] [DecidableEq κ]
    (s : Matrix κ κ K) :
    (fromBlocks 1 s 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) =
      fromBlocks 0 1 (-1) 0 * fromBlocks 1 0 (-s) 1 * fromBlocks 0 1 (-1) 0 *
        fromBlocks (-1) 0 0 (-1) := by
  simp [fromBlocks_multiply]

/- English proof (translation)
Introduce `K _ κ _ _ P hmul hlevi hlow hJ a ha`. Establish `hup : ∀ s : Matrix κ κ K, sᵀ = s → P (fromBlocks 1 s 0 1)`. Introduce `s hs`. Rewrite using `[upper_unipotent_eq]`. Conclude with `hmul _ _ (hmul _ _ (hmul _ _ hJ (hlow _ (by simp [hs]))) hJ) (hlevi _ _ (by simp))`.

Establish `hJ0 : (fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) = -J κ K`. Simplify using `[J, fromBlocks_neg]`. Establish `hsp : a ∈ symplecticGroup κ K`. Rewrite using `[SymplecticGroup.mem_iff']`. Rewrite `ha` using `[hJ0]`.

Simplify `ha` using `[Matrix.mul_neg, Matrix.neg_mul]`. Take `⟨A, B, C, D, rfl⟩ : ∃ A B C D, a = fromBlocks A B C D` from `⟨_, _, _, _, a.fromBlocks_toBlocks.symm⟩`. Take `⟨X, hX, hu⟩` from `exists_symmetric_X_isUnit_det_add_mul_of_symplectic hsp`. Establish `hUX : (fromBlocks 1 X 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) ∈ symplecticGroup κ K`. Simplify using `[SymplecticGroup.fromBlocks_mem_iff, hX.eq]`.

Establish `hprod : (fromBlocks 1 X 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * fromBlocks A B C D = fromBlocks (A + X * C) (B + X * D) C D`. Simplify using `[fromBlocks_multiply]`. Generalize the expression as in `hc : A + X * C = c at hu hprod`. Establish `hcT : IsUnit cᵀ.det` using `by rwa [det_transpose]`. Establish `hLev : (fromBlocks c⁻¹ 0 0 cᵀ : Matrix (κ ⊕ κ) (κ ⊕ κ) K) ∈ symplecticGroup κ K`.

Rewrite using `[SymplecticGroup.fromBlocks_mem_iff]`. Use `⟨by simp, by simp, ?_⟩` and prove the remaining obligations. Rewrite using `[transpose_nonsing_inv]`. Simplify using `[nonsing_inv_mul _ hcT]`. Establish `hnsp` using `mul_mem (mul_mem hLev hUX) hsp`.

Establish `hn : (fromBlocks c⁻¹ 0 0 cᵀ : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * fromBlocks 1 X 0 1 * fromBlocks A B C D = fromBlocks 1 (c⁻¹ * (B + X * D)) (cᵀ * C) (cᵀ * D)`. Rewrite using `[Matrix.mul_assoc, hprod, fromBlocks_multiply]`. Simplify using `[nonsing_inv_mul _ hu]`. Rewrite `hnsp` using `[hn]`. Generalize the expression as in `c⁻¹ * (B + X * D) = Z at hn hnsp`.

Generalize the expression as in `cᵀ * C = Wm at hn hnsp`. Generalize the expression as in `cᵀ * D = V at hn hnsp`. Take `⟨h1, h2, h3⟩` from `SymplecticGroup.fromBlocks_mem_iff.1 hnsp`. Simplify using `only [transpose_one, Matrix.one_mul, Matrix.mul_one] at h1 h3`. Establish `hW : Wmᵀ = Wm` using `h1.symm`.

Rewrite `h3` using `[hW]`. Establish `hV : V = Wm * Z + 1` using `by rw [← h3]; abel`. Establish `hZ : Zᵀ = Z`. Rewrite `h2` using `[hV, transpose_add, transpose_mul, hW, transpose_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, ← Matrix.mul_assoc]`. Simplify using `using h2`.

Establish `hfac : (fromBlocks 1 Z Wm V : Matrix (κ ⊕ κ) (κ ⊕ κ) K) = fromBlocks 1 0 Wm 1 * fromBlocks 1 Z 0 1`. Rewrite using `[fromBlocks_multiply, hV]`. Simplify using the standard rewrite rules. Establish `e2 : (fromBlocks c 0 0 cᵀ⁻¹ : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * fromBlocks c⁻¹ 0 0 cᵀ = 1`. Rewrite using `[fromBlocks_multiply]`.

Simplify using `[mul_nonsing_inv _ hu, nonsing_inv_mul _ hcT]`. Establish `e3 : (fromBlocks 1 (-X) 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * fromBlocks 1 X 0 1 = 1`. Simplify using `[fromBlocks_multiply]`. Establish `hdec : fromBlocks A B C D = (fromBlocks 1 (-X) 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * fromBlocks c 0 0 cᵀ⁻¹ * (fromBlocks c⁻¹ 0 0 cᵀ * fromBlocks 1 X 0 1 * fromBlocks A B C D)`. Rewrite using `[Matrix.mul_assoc (fromBlocks 1 (-X) 0 1), ← Matrix.mul_assoc (fromBlocks c 0 0 cᵀ⁻¹), ← Matrix.mul_assoc (fromBlocks c 0 0 cᵀ⁻¹), e2, Matrix.one_mul, ← Matrix.mul_assoc, e3, Matrix.one_mul]`.

Rewrite using `[hdec, hn, hfac]`. Use `hmul _ _ (hmul _ _ (hup _ (by simp [hX.eq])) (hlevi _ _ ?_)) (hmul _ _ (hlow _ hW) (hup _ hZ))` and prove the remaining obligations. Conclude with `mul_nonsing_inv _ hcT`.
-/
theorem symplectic_generated_levi_lower_weyl :
    ∀ (K : Type) [Field K] (κ : Type) [Fintype κ] [DecidableEq κ] (P : Matrix (κ ⊕ κ) (κ ⊕ κ) K → Prop),
    (∀ a b, P a → P b → P (a * b)) → (∀ g h : Matrix κ κ K, gᵀ * h = 1 → P (Matrix.fromBlocks g 0 0 h)) →
    (∀ b : Matrix κ κ K, bᵀ = b → P (Matrix.fromBlocks 1 0 b 1)) → P (Matrix.fromBlocks 0 1 (-1) 0) →
    ∀ a : Matrix (κ ⊕ κ) (κ ⊕ κ) K, aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * a = Matrix.fromBlocks 0 1 (-1) 0 → P a := by
  intro K _ κ _ _ P hmul hlevi hlow hJ a ha
  have hup : ∀ s : Matrix κ κ K, sᵀ = s → P (fromBlocks 1 s 0 1) := by
    intro s hs
    rw [upper_unipotent_eq]
    exact hmul _ _ (hmul _ _ (hmul _ _ hJ (hlow _ (by simp [hs]))) hJ) (hlevi _ _ (by simp))
  have hJ0 : (fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) = -J κ K := by
    simp [J, fromBlocks_neg]
  have hsp : a ∈ symplecticGroup κ K := by
    rw [SymplecticGroup.mem_iff']
    rw [hJ0] at ha
    simpa [Matrix.mul_neg, Matrix.neg_mul] using ha
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, a = fromBlocks A B C D :=
    ⟨_, _, _, _, a.fromBlocks_toBlocks.symm⟩
  obtain ⟨X, hX, hu⟩ := exists_symmetric_X_isUnit_det_add_mul_of_symplectic hsp
  have hUX : (fromBlocks 1 X 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) ∈ symplecticGroup κ K := by
    simp [SymplecticGroup.fromBlocks_mem_iff, hX.eq]
  have hprod : (fromBlocks 1 X 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * fromBlocks A B C D =
      fromBlocks (A + X * C) (B + X * D) C D := by
    simp [fromBlocks_multiply]
  generalize hc : A + X * C = c at hu hprod
  have hcT : IsUnit cᵀ.det := by rwa [det_transpose]
  have hLev : (fromBlocks c⁻¹ 0 0 cᵀ : Matrix (κ ⊕ κ) (κ ⊕ κ) K) ∈ symplecticGroup κ K := by
    rw [SymplecticGroup.fromBlocks_mem_iff]
    refine ⟨by simp, by simp, ?_⟩
    rw [transpose_nonsing_inv]
    simp [nonsing_inv_mul _ hcT]
  have hnsp := mul_mem (mul_mem hLev hUX) hsp
  have hn : (fromBlocks c⁻¹ 0 0 cᵀ : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * fromBlocks 1 X 0 1 *
      fromBlocks A B C D = fromBlocks 1 (c⁻¹ * (B + X * D)) (cᵀ * C) (cᵀ * D) := by
    rw [Matrix.mul_assoc, hprod, fromBlocks_multiply]
    simp [nonsing_inv_mul _ hu]
  rw [hn] at hnsp
  generalize c⁻¹ * (B + X * D) = Z at hn hnsp
  generalize cᵀ * C = Wm at hn hnsp
  generalize cᵀ * D = V at hn hnsp
  obtain ⟨h1, h2, h3⟩ := SymplecticGroup.fromBlocks_mem_iff.1 hnsp
  simp only [transpose_one, Matrix.one_mul, Matrix.mul_one] at h1 h3
  have hW : Wmᵀ = Wm := h1.symm
  rw [hW] at h3
  have hV : V = Wm * Z + 1 := by rw [← h3]; abel
  have hZ : Zᵀ = Z := by
    rw [hV, transpose_add, transpose_mul, hW, transpose_one, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_one, Matrix.one_mul, ← Matrix.mul_assoc] at h2
    simpa using h2
  have hfac : (fromBlocks 1 Z Wm V : Matrix (κ ⊕ κ) (κ ⊕ κ) K) =
      fromBlocks 1 0 Wm 1 * fromBlocks 1 Z 0 1 := by
    rw [fromBlocks_multiply, hV]; simp
  have e2 : (fromBlocks c 0 0 cᵀ⁻¹ : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * fromBlocks c⁻¹ 0 0 cᵀ = 1 := by
    rw [fromBlocks_multiply]
    simp [mul_nonsing_inv _ hu, nonsing_inv_mul _ hcT]
  have e3 : (fromBlocks 1 (-X) 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * fromBlocks 1 X 0 1 = 1 := by
    simp [fromBlocks_multiply]
  have hdec : fromBlocks A B C D = (fromBlocks 1 (-X) 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) *
      fromBlocks c 0 0 cᵀ⁻¹ * (fromBlocks c⁻¹ 0 0 cᵀ * fromBlocks 1 X 0 1 * fromBlocks A B C D) := by
    rw [Matrix.mul_assoc (fromBlocks 1 (-X) 0 1), ← Matrix.mul_assoc (fromBlocks c 0 0 cᵀ⁻¹),
      ← Matrix.mul_assoc (fromBlocks c 0 0 cᵀ⁻¹), e2, Matrix.one_mul, ← Matrix.mul_assoc, e3,
      Matrix.one_mul]
  rw [hdec, hn, hfac]
  refine hmul _ _ (hmul _ _ (hup _ (by simp [hX.eq])) (hlevi _ _ ?_)) (hmul _ _ (hlow _ hW) (hup _ hZ))
  exact mul_nonsing_inv _ hcT

end GlobalTheory.SpGen
