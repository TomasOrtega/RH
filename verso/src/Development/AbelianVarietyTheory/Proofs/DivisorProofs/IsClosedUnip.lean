import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom

noncomputable section

namespace GlobalTheory.ThK.UnipClosed

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def carrierSet (σ : E →ₐ[F] E) {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) : Set (UA σ W.J) :=
  {u | mat u *ᵥ incV F H'.x = incV F H'.x ∧
    ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_mul {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) :
    mat (g * h) = mat g * mat h := rfl

/- English proof (translation)
Use `show ((g⁻¹ : UA σ J).1.1) * g.1.1 = 1`. Rewrite using `[← Units.val_mul]`. Use `show (((g⁻¹ * g : UA σ J) : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) = 1`. Simplify using the standard rewrite rules.
-/
theorem mat_inv_mul {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) :
    mat g⁻¹ * mat g = 1 := by
  show ((g⁻¹ : UA σ J).1.1) * g.1.1 = 1
  rw [← Units.val_mul]
  show (((g⁻¹ * g : UA σ J) : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) = 1
  simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_one {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} :
    mat (1 : UA σ J) = 1 := rfl

def carrierSub (σ : E →ₐ[F] E) {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) : Subgroup (UA σ W.J) where
  carrier := carrierSet σ W H'
  one_mem' := ⟨by rw [mat_one, Matrix.one_mulVec], fun z => ⟨0, by rw [mat_one, Matrix.one_mulVec, zero_smul, add_zero]⟩⟩
  mul_mem' := by
    rintro u v ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
    refine ⟨by rw [mat_mul, ← Matrix.mulVec_mulVec, hv1, hu1], fun z => ?_⟩
    obtain ⟨a, ha⟩ := hu2 z
    obtain ⟨b, hb⟩ := hv2 z
    refine ⟨a + b, ?_⟩
    rw [mat_mul, ← Matrix.mulVec_mulVec, hb, Matrix.mulVec_add, ha, Matrix.mulVec_smul, hu1, add_smul, add_assoc]
  inv_mem' := by
    rintro u ⟨hu1, hu2⟩
    have hx : mat u⁻¹ *ᵥ incV F H'.x = incV F H'.x := by
      conv_lhs => rw [← hu1]
      rw [Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec]
    refine ⟨hx, fun z => ?_⟩
    obtain ⟨a, ha⟩ := hu2 z
    refine ⟨-a, ?_⟩
    have h1 : mat u⁻¹ *ᵥ (mat u *ᵥ (incM F H'.ι *ᵥ z)) = incM F H'.ι *ᵥ z := by
      rw [Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec]
    rw [ha, Matrix.mulVec_add, Matrix.mulVec_smul, hx] at h1
    rw [neg_smul, ← sub_eq_add_neg, eq_sub_iff_add_eq]
    exact h1

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Conclude with `(Subgroup.closure_le _).2 fun u hu => hu`. Introduce `u hu`. Conclude with `Subgroup.subset_closure hu`.
-/
theorem unip_eq (σ : E →ₐ[F] E) {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) :
    unip σ W H' = carrierSub σ W H' := by
  apply le_antisymm
  · exact (Subgroup.closure_le _).2 fun u hu => hu
  · intro u hu
    exact Subgroup.subset_closure hu

section Top

variable [T2Space (AE F E)] [IsTopologicalRing (AE F E)]

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Establish `: {w : Fin d → AE F E | ∃ a : AE F E, w = a • incV F x} = {0}`. Use extensionality with `w`. Simplify using `only [Set.mem_setOf_eq, Set.mem_singleton_iff]`. Establish `h0 : incV F x = 0`.

Use function extensionality and compare the values at `i`. Simplify using `[incV, hx]`. Simplify using `[h0]`. Rewrite using `[this]`. Conclude with `isClosed_singleton`.

Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, x i ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hx (funext h)`. Establish `hinv : incV F x i * inclR (F` using `F) (AF F) (x i)⁻¹ = 1 := by`.

Simplify using `only [incV, ← map_mul, mul_inv_cancel₀ hi, map_one]`. Establish `: {w : Fin d → AE F E | ∃ a : AE F E, w = a • incV F x} = {w | w = (w i * inclR (F` using `F) (AF F) (x i)⁻¹) • incV F x} := by`. Use extensionality with `w`. Simplify using `only [Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨a, rfl⟩`. Use `congr 1`. Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_assoc, hinv, mul_one]`. Introduce `h`. Conclude with `⟨_, h⟩`.

Rewrite using `[this]`. Conclude with `isClosed_eq continuous_id (((continuous_apply i).mul continuous_const).smul continuous_const)`.
-/
theorem isClosed_line {d : ℕ} (x : Fin d → E) : IsClosed {w : Fin d → AE F E | ∃ a : AE F E, w = a • incV F x} := by
  by_cases hx : x = 0
  · have : {w : Fin d → AE F E | ∃ a : AE F E, w = a • incV F x} = {0} := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      have h0 : incV F x = 0 := by
        funext i
        simp [incV, hx]
      simp [h0]
    rw [this]
    exact isClosed_singleton
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx (funext h)
    have hinv : incV F x i * inclR (F := F) (AF F) (x i)⁻¹ = 1 := by
      simp only [incV, ← map_mul, mul_inv_cancel₀ hi, map_one]
    have : {w : Fin d → AE F E | ∃ a : AE F E, w = a • incV F x} =
        {w | w = (w i * inclR (F := F) (AF F) (x i)⁻¹) • incV F x} := by
      ext w
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨a, rfl⟩
        congr 1
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, hinv, mul_one]
      · intro h
        exact ⟨_, h⟩
    rw [this]
    exact isClosed_eq continuous_id
      (((continuous_apply i).mul continuous_const).smul continuous_const)

end Top

variable [T2Space (AE F E)] [IsTopologicalRing (AE F E)] in
/- English proof (translation)
Establish `hm : Continuous fun u : UA σ W.J => mat u` using `Units.continuous_val.comp continuous_subtype_val`. Establish `h1 : IsClosed {u : UA σ W.J | mat u *ᵥ incV F H'.x = incV F H'.x}` using `isClosed_eq (hm.matrix_mulVec continuous_const) continuous_const`. Establish `h2 : ∀ z : Fin d₁ → AE F E, IsClosed {u : UA σ W.J | ∃ a : AE F E, mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x}`. Introduce `z`. Establish `: {u : UA σ W.J | ∃ a : AE F E, mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x} = (fun u : UA σ W.J => mat u *ᵥ (incM F H'.ι *ᵥ z) - incM F H'.ι *ᵥ z) ⁻¹' {w | ∃ a : AE F E, w = a • incV F H'.x}`.

Use extensionality with `u`. Simplify using `only [Set.mem_setOf_eq, Set.mem_preimage, sub_eq_iff_eq_add']`. Rewrite using `[this]`. Conclude with `(isClosed_line H'.x).preimage ((hm.matrix_mulVec continuous_const).sub continuous_const)`. Establish `: carrierSet σ W H' = {u : UA σ W.J | mat u *ᵥ incV F H'.x = incV F H'.x} ∩ ⋂ z : Fin d₁ → AE F E, {u : UA σ W.J | ∃ a : AE F E, mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x}`.

Use extensionality with `u`. Simplify using `[carrierSet]`. Rewrite using `[this]`. Conclude with `h1.inter (isClosed_iInter h2)`.
-/
theorem isClosed_carrierSet (σ : E →ₐ[F] E) {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) :
    IsClosed (carrierSet σ W H') := by
  have hm : Continuous fun u : UA σ W.J => mat u := Units.continuous_val.comp continuous_subtype_val
  have h1 : IsClosed {u : UA σ W.J | mat u *ᵥ incV F H'.x = incV F H'.x} :=
    isClosed_eq (hm.matrix_mulVec continuous_const) continuous_const
  have h2 : ∀ z : Fin d₁ → AE F E, IsClosed {u : UA σ W.J | ∃ a : AE F E,
      mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x} := by
    intro z
    have : {u : UA σ W.J | ∃ a : AE F E, mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x} =
        (fun u : UA σ W.J => mat u *ᵥ (incM F H'.ι *ᵥ z) - incM F H'.ι *ᵥ z) ⁻¹'
          {w | ∃ a : AE F E, w = a • incV F H'.x} := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_preimage, sub_eq_iff_eq_add']
    rw [this]
    exact (isClosed_line H'.x).preimage ((hm.matrix_mulVec continuous_const).sub continuous_const)
  have : carrierSet σ W H' = {u : UA σ W.J | mat u *ᵥ incV F H'.x = incV F H'.x} ∩
      ⋂ z : Fin d₁ → AE F E, {u : UA σ W.J | ∃ a : AE F E,
        mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x} := by
    ext u
    simp [carrierSet]
  rw [this]
  exact h1.inter (isClosed_iInter h2)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ d d₁ W H'`. Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F`. Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _`. Take `⟨e⟩` from `GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)`.

Use `haveI : T2Space (AE F E) := e.isEmbedding.t2Space`. Rewrite using `[unip_eq]`. Conclude with `isClosed_carrierSet σ W H'`.
-/
theorem isClosed_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d d₁ : ℕ) (W : Spc F E d) (H' : Plane E d d₁), IsClosed ((unip σ W H' : Subgroup (UA σ W.J)) : Set (UA σ W.J)) := by
  intro F E _ _ _ _ _ σ d d₁ W H'
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  rw [unip_eq]
  exact isClosed_carrierSet σ W H'

end GlobalTheory.ThK.UnipClosed
