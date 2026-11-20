import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian

open MeasureTheory Formalism.BasicNotions

noncomputable section

namespace GlobalTheory.UpqUnimodular

/- English proof (translation)
Establish `he : Measurable e` using `e.continuous.measurable`. Establish `hs : Measurable e.symm` using `e.symm.continuous.measurable`. Establish `hμ : μ = (μ.map e).map e.symm`. Rewrite using `[Measure.map_map hs he]`. Establish `: (e.symm : H → G) ∘ e = id` using `by ext x; simp`.

Rewrite using `[this, Measure.map_id]`. Use `⟨fun g => ?_⟩` and prove the remaining obligations. Establish `h1` using `h.map_mul_right_eq_self (e g)`. Establish `hc : (fun x : G => x * g) ∘ (e.symm : H → G) = (e.symm : H → G) ∘ (fun y : H => y * e g)`. Use extensionality with `y`.

Simplify using the standard rewrite rules. Use `conv_lhs => rw [hμ]`. Rewrite using `[Measure.map_map (measurable_mul_const g) hs, hc, ← Measure.map_map hs (measurable_mul_const _), h1, ← hμ]`.
-/
theorem isMulRightInvariant_of_continuousMulEquiv {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
    [MeasurableSpace G] [MeasurableSpace H] [BorelSpace G] [BorelSpace H]
    (e : G ≃ₜ* H) (μ : Measure G) (h : (μ.map e).IsMulRightInvariant) :
    μ.IsMulRightInvariant := by
  have he : Measurable e := e.continuous.measurable
  have hs : Measurable e.symm := e.symm.continuous.measurable
  have hμ : μ = (μ.map e).map e.symm := by
    rw [Measure.map_map hs he]
    have : (e.symm : H → G) ∘ e = id := by ext x; simp
    rw [this, Measure.map_id]
  refine ⟨fun g => ?_⟩
  have h1 := h.map_mul_right_eq_self (e g)
  have hc : (fun x : G => x * g) ∘ (e.symm : H → G) = (e.symm : H → G) ∘ (fun y : H => y * e g) := by
    ext y; simp
  conv_lhs => rw [hμ]
  rw [Measure.map_map (measurable_mul_const g) hs, hc,
    ← Measure.map_map hs (measurable_mul_const _), h1, ← hμ]

def signs (P Q : ℕ) : Fin (P + Q) → Bool := fun i => (finSumFinEquiv.symm i).isLeft

/- English proof (translation)
Use extensionality with `i j`. Take `⟨a, rfl⟩` from `finSumFinEquiv.surjective i`. Take `⟨b, rfl⟩` from `finSumFinEquiv.surjective j`. Simplify using `only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Formalism.REAL.Jm, Matrix.diagonal_apply, EmbeddingLike.apply_eq_iff_eq, signs, Formalism.UG.Jpq]`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.one_apply] <;> split_ifs <;> simp`.
-/
theorem reindex_Jpq (P Q : ℕ) :
    Matrix.reindex finSumFinEquiv finSumFinEquiv (Formalism.UG.Jpq P Q) = Formalism.REAL.Jm (signs P Q) := by
  ext i j
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Formalism.REAL.Jm,
    Matrix.diagonal_apply, EmbeddingLike.apply_eq_iff_eq, signs, Formalism.UG.Jpq]
  rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.one_apply] <;> split_ifs <;> simp

def reindexUnits (P Q : ℕ) :
    GL (Fin P ⊕ Fin Q) ℂ ≃ₜ* (Matrix (Fin (P + Q)) (Fin (P + Q)) ℂ)ˣ where
  toMulEquiv := Units.mapEquiv (Matrix.reindexAlgEquiv ℂ ℂ finSumFinEquiv).toMulEquiv
  continuous_toFun := Units.continuous_map
    (f := ((Matrix.reindexAlgEquiv ℂ ℂ (finSumFinEquiv (m := P) (n := Q))).toMulEquiv.toMonoidHom))
    (continuous_id.matrix_reindex _ _)
  continuous_invFun := Units.continuous_map
    (f := ((Matrix.reindexAlgEquiv ℂ ℂ (finSumFinEquiv (m := P) (n := Q))).toMulEquiv.symm.toMonoidHom))
    ((continuous_id.matrix_reindex (finSumFinEquiv (m := P) (n := Q)).symm
      (finSumFinEquiv (m := P) (n := Q)).symm).congr fun _ => rfl)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem reindexUnits_val (P Q : ℕ) (g : GL (Fin P ⊕ Fin Q) ℂ) :
    (reindexUnits P Q g : Matrix (Fin (P + Q)) (Fin (P + Q)) ℂ) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (g : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Formalism.REAL.inUJ (signs P Q) (reindexUnits P Q g : Matrix (Fin (P + Q)) (Fin (P + Q)) ℂ) ↔ (g : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ).conjTranspose * Formalism.UG.Jpq P Q * (g : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) = Formalism.UG.Jpq P Q`. Rewrite using `[Formalism.REAL.inUJ, reindexUnits_val, ← reindex_Jpq, Matrix.conjTranspose_reindex]`. Rewrite using `[← (Matrix.reindex (α := ℂ) (finSumFinEquiv (m := P) (n := Q)) (finSumFinEquiv (m := P) (n := Q))).injective.eq_iff]`. Simplify using `only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]`.
-/
theorem reindexUnits_mem_iff (P Q : ℕ) (g : GL (Fin P ⊕ Fin Q) ℂ) :
    reindexUnits P Q g ∈ Formalism.REAL.UJ (signs P Q) ↔ g ∈ Formalism.UG.Upq P Q := by
  change Formalism.REAL.inUJ (signs P Q) (reindexUnits P Q g : Matrix (Fin (P + Q)) (Fin (P + Q)) ℂ) ↔
    (g : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ).conjTranspose * Formalism.UG.Jpq P Q *
      (g : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) = Formalism.UG.Jpq P Q
  rw [Formalism.REAL.inUJ, reindexUnits_val, ← reindex_Jpq, Matrix.conjTranspose_reindex]
  rw [← (Matrix.reindex (α := ℂ) (finSumFinEquiv (m := P) (n := Q))
    (finSumFinEquiv (m := P) (n := Q))).injective.eq_iff]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

def modelEquiv (P Q : ℕ) : UpqT P Q ≃ₜ* Formalism.REAL.UJ (signs P Q) where
  toFun g := ⟨reindexUnits P Q (g : Formalism.UG.Upq P Q).1,
    (reindexUnits_mem_iff P Q _).2 (g : Formalism.UG.Upq P Q).2⟩
  invFun h := (⟨(reindexUnits P Q).symm h.1,
    (reindexUnits_mem_iff P Q _).1 (by simpa using h.2)⟩ : Formalism.UG.Upq P Q)
  left_inv g := Subtype.ext ((reindexUnits P Q).symm_apply_apply _)
  right_inv h := Subtype.ext ((reindexUnits P Q).apply_symm_apply _)
  map_mul' g h := Subtype.ext (map_mul (reindexUnits P Q) _ _)
  continuous_toFun :=
    ((reindexUnits P Q).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((reindexUnits P Q).symm.continuous.comp continuous_subtype_val).subtype_mk _

/- English proof (translation)
Use `haveI : IsTopologicalGroup (UpqT P Q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))`. Use `haveI : BorelSpace (UpqT P Q) := ⟨rfl⟩`. Use `isMulRightInvariant_of_continuousMulEquiv (modelEquiv P Q) μ ?_` and prove the remaining obligations. Use `haveI : (μ.map (modelEquiv P Q)).IsHaarMeasure := (modelEquiv P Q).isHaarMeasure_map μ`. Use `haveI : (Formalism.REAL.muG (signs P Q)).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular _ _ g⟩`.

Rewrite using `[Measure.isMulLeftInvariant_eq_smul (μ.map (modelEquiv P Q)) (Formalism.REAL.muG (signs P Q))]`. Use `infer_instance`.
-/
theorem isMulRightInvariant_of_isHaarMeasure (P Q : ℕ) (μ : Measure (UpqT P Q))
    (hμ : μ.IsHaarMeasure) : μ.IsMulRightInvariant := by
  haveI : IsTopologicalGroup (UpqT P Q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))
  haveI : BorelSpace (UpqT P Q) := ⟨rfl⟩
  refine isMulRightInvariant_of_continuousMulEquiv (modelEquiv P Q) μ ?_
  haveI : (μ.map (modelEquiv P Q)).IsHaarMeasure := (modelEquiv P Q).isHaarMeasure_map μ
  haveI : (Formalism.REAL.muG (signs P Q)).IsMulRightInvariant :=
    ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular _ _ g⟩
  rw [Measure.isMulLeftInvariant_eq_smul (μ.map (modelEquiv P Q)) (Formalism.REAL.muG (signs P Q))]
  infer_instance

end GlobalTheory.UpqUnimodular
