import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.Iwasawa

/- English proof (translation)
Establish `key : ∀ (u : GL (Fin n) (ValuativeRel.valuation F).valuationSubring), IsInt 𝒪[F] ((GeneralLinearGroup.map (algebraMap (ValuativeRel.valuation F).valuationSubring F) u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)`. Introduce `u i j`. Establish `h` using `(u.1 i j).2`. Conclude with `h`. Use `⟨key k, ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_inv]`. Conclude with `key k⁻¹`.
-/
theorem map_mem_GLint {F : Type} [Field F] [ValuativeRel F] {n : ℕ}
    (k : GL (Fin n) (ValuativeRel.valuation F).valuationSubring) :
    GeneralLinearGroup.map (algebraMap (ValuativeRel.valuation F).valuationSubring F) k ∈
      GLint 𝒪[F] n := by
  have key : ∀ (u : GL (Fin n) (ValuativeRel.valuation F).valuationSubring),
      IsInt 𝒪[F] ((GeneralLinearGroup.map
        (algebraMap (ValuativeRel.valuation F).valuationSubring F) u : GL (Fin n) F) :
          Matrix (Fin n) (Fin n) F) := by
    intro u i j
    have h := (u.1 i j).2
    exact h
  refine ⟨key k, ?_⟩
  rw [← map_inv]
  exact key k⁻¹

/- English proof (translation)
Take `rfl` from `h.O_eq`. Take `⟨k, b, hb, hg⟩` from `GlobalTheory.ValIwasawa.iwasawa (ValuativeRel.valuation F).valuationSubring F n g⁻¹`. Use `⟨b⁻¹, ?_, _, (GLint _ n).inv_mem (map_mem_GLint k), ?_⟩` and prove the remaining obligations. Set `_ : Invertible (b : Matrix (Fin n) (Fin n) F)` to `Units.invertible b`. Rewrite using `[Matrix.coe_units_inv]`.

Conclude with `Matrix.blockTriangular_inv_of_blockTriangular hb`. Rewrite using `[← _root_.mul_inv_rev, ← hg, inv_inv]`.
-/
theorem exists_upper_mul_int {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
    (h : LF O ϖ nrm q) (n : ℕ) (g : GL (Fin n) F) :
    ∃ b : GL (Fin n) F, (b : Matrix (Fin n) (Fin n) F).BlockTriangular id ∧
      ∃ k ∈ GLint O n, g = b * k := by
  obtain rfl := h.O_eq
  obtain ⟨k, b, hb, hg⟩ :=
    GlobalTheory.ValIwasawa.iwasawa (ValuativeRel.valuation F).valuationSubring F n g⁻¹
  refine ⟨b⁻¹, ?_, _, (GLint _ n).inv_mem (map_mem_GLint k), ?_⟩
  · let _ : Invertible (b : Matrix (Fin n) (Fin n) F) := Units.invertible b
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hb
  · rw [← _root_.mul_inv_rev, ← hg, inv_inv]

end GlobalTheory.CompanionTheory.QL.Iwasawa
