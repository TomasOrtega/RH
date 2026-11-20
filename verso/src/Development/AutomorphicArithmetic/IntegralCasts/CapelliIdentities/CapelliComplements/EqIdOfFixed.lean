import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

namespace Bl.EqIdOfFixed

/- English proof (translation)
Unfold `HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt at h`. Take `⟨-, hc, -, hs⟩` from `h`. Assume the negation of the conclusion as `hne0`. Establish `hne : ∀ z : E, σ z = z` using `fun z => by_contra fun hz => hne0 ⟨z, hz⟩`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`.

Use `hc` as an intermediate fact. Apply `NumberField.IsTotallyComplex.complexEmbedding_not_isReal τ` to reduce the goal to its premises. Rewrite using `[NumberField.ComplexEmbedding.isReal_iff]`. Use extensionality with `z`. Rewrite using `[NumberField.ComplexEmbedding.conjugate_coe_eq]`.

Use `hs τ z` as an intermediate fact. Rewrite `this` using `[hne z]`. Conclude with `this.symm`.
-/
private lemma ne_id_of_cm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) : ∃ y : E, σ y ≠ y := by
  unfold HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt at h
  obtain ⟨-, hc, -, hs⟩ := h
  by_contra hne0
  have hne : ∀ z : E, σ z = z := fun z => by_contra fun hz => hne0 ⟨z, hz⟩
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have := hc
  apply NumberField.IsTotallyComplex.complexEmbedding_not_isReal τ
  rw [NumberField.ComplexEmbedding.isReal_iff]
  ext z
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
  have := hs τ z
  rw [hne z] at this
  exact this.symm

/- English proof (translation)
Establish `hli : LinearIndependent F ![(1 : E), x]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`. Distinguish the cases in `ht : t = 0`. Substitute `ht` using the available equality.

Simplify using `only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst`. Conclude with `⟨hst, rfl⟩`. It suffices to derive a contradiction. Apply `hno (-(s / t))` to reduce the goal to its premises. Establish `h1 : t • x = -(s • (1 : E))` using `eq_neg_of_add_eq_zero_right hst`.

Establish `h2 : x = t⁻¹ • -(s • (1 : E))`. Rewrite using `[← h1, smul_smul, inv_mul_cancel₀ ht, one_smul]`. Rewrite using `[h2, Algebra.algebraMap_eq_smul_one, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]`. Establish `hc : Fintype.card (Fin 2) = Module.finrank F E` using `by simp [hd]`. Set `b` to `basisOfLinearIndependentOfCardEqFinrank hli hc`.

Establish `heq : σ.toLinearMap = (LinearMap.id : E →ₗ[F] E)`. Apply `b.ext` to reduce the goal to its premises. Introduce `i`. Use `fin_cases i`. Simplify using `[b]`.

Simplify using `[b, hx]`. Conclude with `LinearMap.congr_fun heq y`.
-/
private lemma eq_id_of_fix {F E : Type} [Field F] [Field E] [Algebra F E]
    (hd : Module.finrank F E = 2) (σ : E →ₐ[F] E) {x : E} (hx : σ x = x)
    (hno : ∀ t : F, algebraMap F E t ≠ x) (y : E) : σ y = y := by
  have hli : LinearIndependent F ![(1 : E), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply hno (-(s / t))
      have h1 : t • x = -(s • (1 : E)) := eq_neg_of_add_eq_zero_right hst
      have h2 : x = t⁻¹ • -(s • (1 : E)) := by
        rw [← h1, smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [h2, Algebra.algebraMap_eq_smul_one, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
  have hc : Fintype.card (Fin 2) = Module.finrank F E := by simp [hd]
  let b := basisOfLinearIndependentOfCardEqFinrank hli hc
  have heq : σ.toLinearMap = (LinearMap.id : E →ₗ[F] E) := by
    apply b.ext
    intro i
    fin_cases i
    · simp [b]
    · simp [b, hx]
  exact LinearMap.congr_fun heq y

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ h x hx`. Assume the negation of the conclusion as `hno0`. Establish `hno : ∀ t : F, algebraMap F E t ≠ x` using `fun t ht => hno0 ⟨t, ht⟩`. Take `⟨y, hy⟩` from `ne_id_of_cm σ h`. Establish `h'` using `h`.

Unfold `HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt at h'`. Conclude with `hy (eq_id_of_fix h'.2.2.1 σ hx hno y)`.
-/
theorem goal1 :
  ∀ {F E : Type} [inst : Field.{0} F] [inst_1 : NumberField.{0} F] [inst_2 : Field.{0} E] [inst_3 : NumberField.{0} E]
  [inst_4 : Algebra.{0, 0} F E] {σ : AlgHom.{0, 0, 0} F E E},
  HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ →
    ∀ {x : E},
      Eq.{1} (DFunLike.coe.{1, 1, 1} σ x) x →
        Exists.{1} fun (t : F) ↦ Eq.{1} (DFunLike.coe.{1, 1, 1} (Algebra.algebraMap.{0, 0} F E) t) x := by
  intro F E _ _ _ _ _ σ h x hx
  by_contra hno0
  have hno : ∀ t : F, algebraMap F E t ≠ x := fun t ht => hno0 ⟨t, ht⟩
  obtain ⟨y, hy⟩ := ne_id_of_cm σ h
  have h' := h
  unfold HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt at h'
  exact hy (eq_id_of_fix h'.2.2.1 σ hx hno y)

end Bl.EqIdOfFixed
