import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitsAlgebraMap
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousOfMem
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.PolyRealU

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Establish `h1 : Continuous (coord (E` using `E) τ) := by`. Unfold `coord`. Use `split_ifs`. Conclude with `continuous_apply _`. Conclude with `Complex.continuous_conj.comp (continuous_apply _)`.

Establish `h2 : Continuous (pInf E)` using `continuous_pi fun w => ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp (continuous_apply w)).comp continuous_fst`. Establish `h3 : Continuous fun x : infU E n => (x.1.1.val : Matrix (Fin n) (Fin n) (Ad E)) i j` using `(Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).matrix_elem i j`. Conclude with `h1.comp (h2.comp h3)`.
-/
theorem continuous_entry (τ : E →+* ℂ) (i j : Fin n) :
    Continuous fun x : infU E n => (cEmb τ x.1).val i j := by
  have h1 : Continuous (coord (E := E) τ) := by
    unfold coord
    split_ifs
    · exact continuous_apply _
    · exact Complex.continuous_conj.comp (continuous_apply _)
  have h2 : Continuous (pInf E) := continuous_pi fun w =>
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst
  have h3 : Continuous fun x : infU E n => (x.1.1.val : Matrix (Fin n) (Fin n) (Ad E)) i j :=
    (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).matrix_elem i j
  exact h1.comp (h2.comp h3)

omit [NumberField E] [IsCMField E] in

/- English proof (translation)
Unfold `coord`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem coord_star' (τ : E →+* ℂ) (z : Cinf E) : coord τ (star z) = star (coord τ z) := by
  unfold coord
  split_ifs <;> rfl

/- English proof (translation)
Establish `hne : ComplexEmbedding.conjugate τ ≠ τ` using `fun h => (InfinitePlace.isComplex_mk_iff.1 (IsTotallyComplex.isComplex (InfinitePlace.mk τ))) (ComplexEmbedding.isReal_iff.2 h)`. Unfold `coord`. Rewrite using `[InfinitePlace.mk_conjugate_eq]`. Break down `InfinitePlace.embedding_mk_eq τ with h | h` into its components or cases. Rewrite using `[if_pos h, if_neg (by rw [h]; exact hne.symm)]`.

Both sides reduce to the same expression. Rewrite using `[if_pos h, if_neg (by rw [h]; exact hne)]`. Simplify using the standard rewrite rules.
-/
theorem coord_conj (τ : E →+* ℂ) (z : Cinf E) : coord (ComplexEmbedding.conjugate τ) z = star (coord τ z) := by
  have hne : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
    (InfinitePlace.isComplex_mk_iff.1 (IsTotallyComplex.isComplex (InfinitePlace.mk τ)))
      (ComplexEmbedding.isReal_iff.2 h)
  unfold coord
  rw [InfinitePlace.mk_conjugate_eq]
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · rw [if_pos h, if_neg (by rw [h]; exact hne.symm)]
    rfl
  · rw [if_pos h, if_neg (by rw [h]; exact hne)]
    simp

/- English proof (translation)
Establish `hx : Formalism.UG.cT (conjAd E) x.1.val * 1 * x.1.val = 1` using `x.2`. Rewrite `hx` using `[Matrix.mul_one]`. Establish `h1 : (x.1⁻¹).val = Formalism.UG.cT (conjAd E) x.1.val` using `Units.inv_eq_of_mul_eq_one_left hx`. Establish `h2 : ∀ y, pInf E (conjAd E y) = star (pInf E y)` using `fun y => by`. Express the relevant statement in the definitionally equal form `(infEq E).symm (infEq E _) = _`.

Rewrite using `[RingEquiv.symm_apply_apply]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `coord τ (pInf E ((x.1⁻¹).val i j)) = star (coord τ (pInf E (x.1.val j i)))`. Rewrite using `[h1, ← coord_star', ← h2]`. Both sides reduce to the same expression.
-/
theorem entry_inv (τ : E →+* ℂ) (x : UA E n) (i j : Fin n) :
    (cEmb τ x⁻¹).val i j = star ((cEmb τ x).val j i) := by
  have hx : Formalism.UG.cT (conjAd E) x.1.val * 1 * x.1.val = 1 := x.2
  rw [Matrix.mul_one] at hx
  have h1 : (x.1⁻¹).val = Formalism.UG.cT (conjAd E) x.1.val := Units.inv_eq_of_mul_eq_one_left hx
  have h2 : ∀ y, pInf E (conjAd E y) = star (pInf E y) := fun y => by
    change (infEq E).symm (infEq E _) = _
    rw [RingEquiv.symm_apply_apply]
    rfl
  change coord τ (pInf E ((x.1⁻¹).val i j)) = star (coord τ (pInf E (x.1.val j i)))
  rw [h1, ← coord_star', ← h2]
  rfl

/- English proof (translation)
Use `Subtype.ext (Subtype.ext (ga_ext ?_ ?_))` and prove the remaining obligations. Use extensionality with `i j w`. Establish `h1 : coord w.embedding (pInf E (x.1.1.val i j)) = coord w.embedding (pInf E (y.1.1.val i j))` using `h w.embedding i j`. Unfold `coord at h1`. Rewrite `h1` using `[InfinitePlace.mk_embedding, if_pos rfl]`.

Conclude with `h1`. Conclude with `(MonoidHom.mem_ker.1 x.2).trans (MonoidHom.mem_ker.1 y.2).symm`.
-/
theorem eq_of_entry {x y : infU E n} (h : ∀ τ i j, (cEmb τ x.1).val i j = (cEmb τ y.1).val i j) : x = y := by
  refine Subtype.ext (Subtype.ext (ga_ext ?_ ?_))
  · ext i j w
    have h1 : coord w.embedding (pInf E (x.1.1.val i j)) = coord w.embedding (pInf E (y.1.1.val i j)) :=
      h w.embedding i j
    unfold coord at h1
    rw [InfinitePlace.mk_embedding, if_pos rfl] at h1
    exact h1
  · exact (MonoidHom.mem_ker.1 x.2).trans (MonoidHom.mem_ker.1 y.2).symm

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.SplittingAdditive.main`. Consider the case `exact _root_.GlobalTheory.SplittingAdditive.main`. Consider the case `(apply _root_.GlobalTheory.SplittingAdditive.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.SplittingAdditive.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.SplittingAdditive.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.SplittingAdditive.main ..)`.
-/
theorem coprod_adjoin {G : Type} [Mul G] (S : Set (G → ℂ))
    (hS : ∀ p ∈ S, ∃ (m : ℕ) (a b : Fin m → G → ℂ), (∀ i, a i ∈ Algebra.adjoin ℂ S ∧ b i ∈ Algebra.adjoin ℂ S) ∧
      ∀ x k, p (x * k) = ∑ i, a i x * b i k) :
    ∀ p ∈ Algebra.adjoin ℂ S, ∃ (m : ℕ) (a b : Fin m → G → ℂ),
      (∀ i, a i ∈ Algebra.adjoin ℂ S ∧ b i ∈ Algebra.adjoin ℂ S) ∧ ∀ x k, p (x * k) = ∑ i, a i x * b i k := by
  first
  | exact @_root_.GlobalTheory.SplittingAdditive.main
  | exact _root_.GlobalTheory.SplittingAdditive.main
  | (apply _root_.GlobalTheory.SplittingAdditive.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SplittingAdditive.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SplittingAdditive.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SplittingAdditive.main ..)

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.CoordinateEmbeddingSplits.main`. Consider the case `exact _root_.GlobalTheory.CoordinateEmbeddingSplits.main`. Consider the case `(apply _root_.GlobalTheory.CoordinateEmbeddingSplits.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.CoordinateEmbeddingSplits.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.CoordinateEmbeddingSplits.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.CoordinateEmbeddingSplits.main ..)`.
-/
theorem poly_infU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), (∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, Continuous p) ∧ (∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, star p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}) ∧ (∀ x y : infU E n, x ≠ y → ∃ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, p x ≠ p y) ∧ (∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, (fun x => p x⁻¹) ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}) ∧ ∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, ∃ (m : ℕ) (a b : Fin m → infU E n → ℂ), (∀ i, a i ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j} ∧ b i ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}) ∧ ∀ x k, p (x * k) = ∑ i, a i x * b i k := by
  first
  | exact @_root_.GlobalTheory.CoordinateEmbeddingSplits.main
  | exact _root_.GlobalTheory.CoordinateEmbeddingSplits.main
  | (apply _root_.GlobalTheory.CoordinateEmbeddingSplits.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoordinateEmbeddingSplits.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoordinateEmbeddingSplits.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoordinateEmbeddingSplits.main ..)

end GlobalTheory.PolyRealU
