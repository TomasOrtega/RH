import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import GroundTheory.GlobalFields.TateThesis.AdeleMeasure
import GroundTheory.GlobalFields.Adele.Discrete
import GroundTheory.GlobalFields.Adele.IntegersLattice
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory

namespace GlobalTheory.CellDec

/- English proof (translation)
Introduce `E _ _ n C hC`. Set `S : Fin n → Fin n → Set (Ad E)` to `fun i j => if j < i then {0} else if i = j then {1} else C`. Set `P : Set (Matrix (Fin n) (Fin n) (Ad E))` to `Set.univ.pi fun i => Set.univ.pi (S i)`. Establish `hP : IsCompact P`. Use `isCompact_univ_pi fun i => isCompact_univ_pi fun j => ?_` and prove the remaining obligations.

Simplify using `only [S]`. Use `split_ifs`. Conclude with `isCompact_singleton`. Conclude with `isCompact_singleton`. Conclude with `hC`.

Establish `memP : ∀ M : Matrix (Fin n) (Fin n) (Ad E), M ∈ P ↔ (∀ i j, j < i → M i j = 0) ∧ (∀ i, M i i = 1) ∧ ∀ i j, i < j → M i j ∈ C`. Introduce `M`. Express the relevant statement in the definitionally equal form `(∀ i ∈ Set.univ, ∀ j ∈ Set.univ, M i j ∈ S i j) ↔ _`. Simplify using `only [S]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Use `⟨fun i j hji => ?_, fun i => ?_, fun i j hij => ?_⟩` and prove the remaining obligations. Use `h i trivial j trivial` as an intermediate fact. Rewrite `this` using `[if_pos hji]`. Conclude with `this`.

Use `h i trivial i trivial` as an intermediate fact. Rewrite `this` using `[if_neg (lt_irrefl i), if_pos rfl]`. Conclude with `this`. Use `h i trivial j trivial` as an intermediate fact. Rewrite `this` using `[if_neg (not_lt.2 hij.le), if_neg hij.ne]`.

Conclude with `this`. Introduce and unpack `⟨h0, h1, hc⟩ i - j - split_ifs with hji hij`. Conclude with `h0 i j hji`. Substitute `hij` using the available equality. Conclude with `h1 i`.

Conclude with `hc i j (lt_of_le_of_ne (not_lt.1 hji) hij)`. Establish `hdet : ∀ M ∈ P, M.det = 1`. Introduce `M hM`. Take `⟨h0, h1, -⟩` from `(memP M).1 hM`. Rewrite using `[Matrix.det_of_isUpperTriangular (fun i j hji => h0 i j hji)]`.

Simplify using `[h1]`. Rewrite using `[Units.isEmbedding_embedProduct.isCompact_iff]`. Establish `key : (Units.embedProduct (Matrix (Fin n) (Fin n) (Ad E))) '' {g : GA E n | g ∈ GlobalTheory.CellDec.NA E n ∧ ∀ i j : Fin n, i < j → (g : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ C} = (fun M => (M, MulOpposite.op M.adjugate)) '' P`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨g, ⟨hN, hc⟩, rfl⟩`. Take `⟨h0, h1⟩` from `(GlobalTheory.SmGL.mem_unipB (Ad E)).1 hN`. Establish `hgP : (g : Matrix (Fin n) (Fin n) (Ad E)) ∈ P` using `(memP _).2 ⟨h0, h1, hc⟩`. Use `⟨g, hgP, ?_⟩` and prove the remaining obligations. Establish `hadj : (g : Matrix (Fin n) (Fin n) (Ad E)).adjugate = ((g⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E))`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Units.inv_mul, Matrix.one_mul]`. Use `_ = ((g⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) * ((g : Matrix (Fin n) (Fin n) (Ad E)) * (g : Matrix (Fin n) (Fin n) (Ad E)).adjugate) := by`. Rewrite using `[Matrix.mul_assoc]`. Use `_ = ((g⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) := by`.

Rewrite using `[Matrix.mul_adjugate, hdet _ hgP, one_smul, Matrix.mul_one]`. Simplify using `only [Units.embedProduct_apply, hadj]`. Introduce and unpack `⟨M, hM, rfl⟩`. Establish `hd` using `hdet M hM`. Set `g : GA E n` to `⟨M, M.adjugate, by rw [Matrix.mul_adjugate, hd, one_smul], by rw [Matrix.adjugate_mul, hd, one_smul]⟩`.

Take `⟨h0, h1, hc⟩` from `(memP M).1 hM`. Use `⟨g, ⟨(GlobalTheory.SmGL.mem_unipB (Ad E)).2 ⟨h0, h1⟩, hc⟩, ?_⟩` and prove the remaining obligations. Both sides reduce to the same expression. Rewrite using `[key]`. Conclude with `hP.image (continuous_id.prodMk (MulOpposite.continuous_op.comp continuous_id.matrix_adjugate))`.
-/
theorem isCompact_unip_entries_mem :
    ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (C : Set (Ad E)), IsCompact C →
    IsCompact {g : GA E n | g ∈ GlobalTheory.CellDec.NA E n ∧ ∀ i j : Fin n, i < j → (g : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ C} := by
  intro E _ _ n C hC
  classical
  let S : Fin n → Fin n → Set (Ad E) := fun i j => if j < i then {0} else if i = j then {1} else C
  let P : Set (Matrix (Fin n) (Fin n) (Ad E)) := Set.univ.pi fun i => Set.univ.pi (S i)
  have hP : IsCompact P := by
    refine isCompact_univ_pi fun i => isCompact_univ_pi fun j => ?_
    simp only [S]
    split_ifs
    · exact isCompact_singleton
    · exact isCompact_singleton
    · exact hC
  have memP : ∀ M : Matrix (Fin n) (Fin n) (Ad E), M ∈ P ↔
      (∀ i j, j < i → M i j = 0) ∧ (∀ i, M i i = 1) ∧ ∀ i j, i < j → M i j ∈ C := by
    intro M
    change (∀ i ∈ Set.univ, ∀ j ∈ Set.univ, M i j ∈ S i j) ↔ _
    simp only [S]
    constructor
    · intro h
      refine ⟨fun i j hji => ?_, fun i => ?_, fun i j hij => ?_⟩
      · have := h i trivial j trivial; rw [if_pos hji] at this; exact this
      · have := h i trivial i trivial; rw [if_neg (lt_irrefl i), if_pos rfl] at this; exact this
      · have := h i trivial j trivial; rw [if_neg (not_lt.2 hij.le), if_neg hij.ne] at this; exact this
    · rintro ⟨h0, h1, hc⟩ i - j -
      split_ifs with hji hij
      · exact h0 i j hji
      · subst hij; exact h1 i
      · exact hc i j (lt_of_le_of_ne (not_lt.1 hji) hij)
  have hdet : ∀ M ∈ P, M.det = 1 := by
    intro M hM
    obtain ⟨h0, h1, -⟩ := (memP M).1 hM
    rw [Matrix.det_of_isUpperTriangular (fun i j hji => h0 i j hji)]
    simp [h1]
  rw [Units.isEmbedding_embedProduct.isCompact_iff]
  have key : (Units.embedProduct (Matrix (Fin n) (Fin n) (Ad E))) ''
      {g : GA E n | g ∈ GlobalTheory.CellDec.NA E n ∧ ∀ i j : Fin n, i < j → (g : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ C} =
      (fun M => (M, MulOpposite.op M.adjugate)) '' P := by
    ext x
    constructor
    · rintro ⟨g, ⟨hN, hc⟩, rfl⟩
      obtain ⟨h0, h1⟩ := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hN
      have hgP : (g : Matrix (Fin n) (Fin n) (Ad E)) ∈ P := (memP _).2 ⟨h0, h1, hc⟩
      refine ⟨g, hgP, ?_⟩
      have hadj : (g : Matrix (Fin n) (Fin n) (Ad E)).adjugate = ((g⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) := by
        calc (g : Matrix (Fin n) (Fin n) (Ad E)).adjugate
            = (((g⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) * g) * (g : Matrix (Fin n) (Fin n) (Ad E)).adjugate := by
              rw [Units.inv_mul, Matrix.one_mul]
          _ = ((g⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) * ((g : Matrix (Fin n) (Fin n) (Ad E)) * (g : Matrix (Fin n) (Fin n) (Ad E)).adjugate) := by
              rw [Matrix.mul_assoc]
          _ = ((g⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) := by
              rw [Matrix.mul_adjugate, hdet _ hgP, one_smul, Matrix.mul_one]
      simp only [Units.embedProduct_apply, hadj]
    · rintro ⟨M, hM, rfl⟩
      have hd := hdet M hM
      let g : GA E n := ⟨M, M.adjugate, by rw [Matrix.mul_adjugate, hd, one_smul],
        by rw [Matrix.adjugate_mul, hd, one_smul]⟩
      obtain ⟨h0, h1, hc⟩ := (memP M).1 hM
      refine ⟨g, ⟨(GlobalTheory.SmGL.mem_unipB (Ad E)).2 ⟨h0, h1⟩, hc⟩, ?_⟩
      rfl
  rw [key]
  exact hP.image (continuous_id.prodMk (MulOpposite.continuous_op.comp continuous_id.matrix_adjugate))

end GlobalTheory.CellDec
