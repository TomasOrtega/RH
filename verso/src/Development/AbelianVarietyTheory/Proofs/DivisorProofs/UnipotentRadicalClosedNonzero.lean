import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatMulVec
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass

noncomputable section

namespace GlobalTheory.UnipClosed

/- English proof (translation)
Use `haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩`. Use `haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _`. Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F`. Take `⟨e⟩` from `GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)`.

Use `haveI : T2Space (AE F E) := e.isEmbedding.t2Space`. Use `set x : Fin d → AE F E := incV F H'.x with hxdef`. Use `set ι : Matrix (Fin d) (Fin d₁) (AE F E) := incM F H'.ι`. Use `set S : Set (UA σ W.J) := {u | mat u *ᵥ x = x ∧ ∀ z, ∃ a : AE F E, mat u *ᵥ (ι *ᵥ z) = ι *ᵥ z + a • x} with hS`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, H'.x k ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hx (funext h)`. Establish `hcu : IsUnit (x k)`. Establish `: x k = inclR (F` using `F) (AF F) (H'.x k) := rfl`.

Rewrite using `[this]`. Conclude with `(IsUnit.mk0 _ hk).map _`. Use `set c : (AE F E)ˣ := hcu.unit`. Establish `hc : (c : AE F E) = x k` using `hcu.unit_spec`. Establish `hline : ∀ v w : Fin d → AE F E, (∃ a : AE F E, w = v + a • x) ↔ w = v + ((w - v) k * ↑c⁻¹) • x`.

Introduce `v w`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Use `congr 2`. Simplify using `only [add_sub_cancel_left, Pi.smul_apply, smul_eq_mul]`.

Rewrite using `[← hc, mul_assoc, Units.mul_inv, mul_one]`. Introduce `h`. Conclude with `⟨_, h⟩`. Establish `hm : Continuous fun g : UA σ W.J => mat g` using `Units.continuous_val.comp continuous_subtype_val`. Establish `hSc : IsClosed S`.

Establish `h1 : IsClosed {u : UA σ W.J | mat u *ᵥ x = x}` using `isClosed_eq (hm.matrix_mulVec continuous_const) continuous_const`. Establish `h2 : IsClosed {u : UA σ W.J | ∀ z, ∃ a : AE F E, mat u *ᵥ (ι *ᵥ z) = ι *ᵥ z + a • x}`. Simplify using `only [Set.setOf_forall]`. Use `isClosed_iInter fun z => ?_` and prove the remaining obligations. Repeatedly rewrite using `[hline]`.

Establish `hf : Continuous fun u : UA σ W.J => mat u *ᵥ (ι *ᵥ z)` using `hm.matrix_mulVec continuous_const`. Establish `hg : Continuous fun u : UA σ W.J => ((mat u *ᵥ (ι *ᵥ z) - ι *ᵥ z) k * ↑c⁻¹)` using `((continuous_apply k).comp (hf.sub continuous_const)).mul continuous_const`. Conclude with `isClosed_eq hf (continuous_const.add (hg.smul (continuous_const : Continuous fun _ : UA σ W.J => x)))`. Conclude with `h1.inter h2`. Establish `hsub : ∃ H : Subgroup (UA σ W.J), (H : Set (UA σ W.J)) = S`.

Use `⟨{ carrier := S, one_mem' := ?_, mul_mem' := ?_, inv_mem' := ?_ }, rfl⟩` and prove the remaining obligations. Introduce and unpack `u v ⟨hu1, hu2⟩ ⟨hv1, hv2⟩`. Use `⟨by rw [GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, hv1, hu1], fun z => ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `hv2 z`. Take `⟨b, hb⟩` from `hu2 z`.

Use `⟨b + a, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_add, Matrix.mulVec_smul, hb, hu1, add_smul, add_assoc]`. Conclude with `⟨by simp [GlobalTheory.StabHaar.mat_one], fun z => ⟨0, by simp [GlobalTheory.StabHaar.mat_one]⟩⟩`. Introduce and unpack `u ⟨hu1, hu2⟩`. Establish `e1 : mat u⁻¹ *ᵥ x = x` using `by conv_lhs => rw [← hu1]`.

Rewrite using `[Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_inv_mul, Matrix.one_mulVec]`. Use `⟨e1, fun z => ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `hu2 z`. Use `⟨-a, ?_⟩` and prove the remaining obligations. Establish `: mat u⁻¹ *ᵥ (mat u *ᵥ (ι *ᵥ z)) = ι *ᵥ z`.

Rewrite using `[Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_inv_mul, Matrix.one_mulVec]`. Rewrite `this` using `[ha, Matrix.mulVec_add, Matrix.mulVec_smul, e1]`. Rewrite using `[neg_smul, ← sub_eq_add_neg, eq_sub_iff_add_eq, this]`. Take `⟨H, hH⟩` from `hsub`. Establish `: unip σ W H' = H`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[unip, Subgroup.closure_le]`. Conclude with `hH.symm ▸ subset_rfl`. Introduce `g hg`. Establish `: g ∈ S` using `hH ▸ hg`.

Conclude with `Subgroup.subset_closure this`. Rewrite using `[this, hH]`. Conclude with `hSc`.
-/
theorem isClosed_unip (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d d₁ : ℕ) (W : Spc F E d) (H' : Plane E d d₁) (hx : H'.x ≠ 0) :
    IsClosed ((unip σ W H' : Subgroup (UA σ W.J)) : Set (UA σ W.J)) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  set x : Fin d → AE F E := incV F H'.x with hxdef
  set ι : Matrix (Fin d) (Fin d₁) (AE F E) := incM F H'.ι

  set S : Set (UA σ W.J) := {u | mat u *ᵥ x = x ∧ ∀ z, ∃ a : AE F E, mat u *ᵥ (ι *ᵥ z) = ι *ᵥ z + a • x} with hS
  obtain ⟨k, hk⟩ : ∃ k, H'.x k ≠ 0 := by
    by_contra h; push_neg at h; exact hx (funext h)
  have hcu : IsUnit (x k) := by
    have : x k = inclR (F := F) (AF F) (H'.x k) := rfl
    rw [this]; exact (IsUnit.mk0 _ hk).map _
  set c : (AE F E)ˣ := hcu.unit
  have hc : (c : AE F E) = x k := hcu.unit_spec
  have hline : ∀ v w : Fin d → AE F E, (∃ a : AE F E, w = v + a • x) ↔ w = v + ((w - v) k * ↑c⁻¹) • x := by
    intro v w
    constructor
    · rintro ⟨a, rfl⟩
      congr 2
      simp only [add_sub_cancel_left, Pi.smul_apply, smul_eq_mul]
      rw [← hc, mul_assoc, Units.mul_inv, mul_one]
    · intro h; exact ⟨_, h⟩
  have hm : Continuous fun g : UA σ W.J => mat g := Units.continuous_val.comp continuous_subtype_val
  have hSc : IsClosed S := by
    have h1 : IsClosed {u : UA σ W.J | mat u *ᵥ x = x} :=
      isClosed_eq (hm.matrix_mulVec continuous_const) continuous_const
    have h2 : IsClosed {u : UA σ W.J | ∀ z, ∃ a : AE F E, mat u *ᵥ (ι *ᵥ z) = ι *ᵥ z + a • x} := by
      simp only [Set.setOf_forall]
      refine isClosed_iInter fun z => ?_
      simp_rw [hline]
      have hf : Continuous fun u : UA σ W.J => mat u *ᵥ (ι *ᵥ z) := hm.matrix_mulVec continuous_const
      have hg : Continuous fun u : UA σ W.J => ((mat u *ᵥ (ι *ᵥ z) - ι *ᵥ z) k * ↑c⁻¹) :=
        ((continuous_apply k).comp (hf.sub continuous_const)).mul continuous_const
      exact isClosed_eq hf (continuous_const.add (hg.smul (continuous_const : Continuous fun _ : UA σ W.J => x)))
    exact h1.inter h2
  have hsub : ∃ H : Subgroup (UA σ W.J), (H : Set (UA σ W.J)) = S := by
    refine ⟨{ carrier := S, one_mem' := ?_, mul_mem' := ?_, inv_mem' := ?_ }, rfl⟩
    · rintro u v ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
      refine ⟨by rw [GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, hv1, hu1], fun z => ?_⟩
      obtain ⟨a, ha⟩ := hv2 z
      obtain ⟨b, hb⟩ := hu2 z
      refine ⟨b + a, ?_⟩
      rw [GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_add, Matrix.mulVec_smul, hb, hu1, add_smul, add_assoc]
    · exact ⟨by simp [GlobalTheory.StabHaar.mat_one], fun z => ⟨0, by simp [GlobalTheory.StabHaar.mat_one]⟩⟩
    · rintro u ⟨hu1, hu2⟩
      have e1 : mat u⁻¹ *ᵥ x = x := by
        conv_lhs => rw [← hu1]
        rw [Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_inv_mul, Matrix.one_mulVec]
      refine ⟨e1, fun z => ?_⟩
      obtain ⟨a, ha⟩ := hu2 z
      refine ⟨-a, ?_⟩
      have : mat u⁻¹ *ᵥ (mat u *ᵥ (ι *ᵥ z)) = ι *ᵥ z := by
        rw [Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_inv_mul, Matrix.one_mulVec]
      rw [ha, Matrix.mulVec_add, Matrix.mulVec_smul, e1] at this
      rw [neg_smul, ← sub_eq_add_neg, eq_sub_iff_add_eq, this]
  obtain ⟨H, hH⟩ := hsub
  have : unip σ W H' = H := by
    apply le_antisymm
    · rw [unip, Subgroup.closure_le]; exact hH.symm ▸ subset_rfl
    · intro g hg
      have : g ∈ S := hH ▸ hg
      exact Subgroup.subset_closure this
  rw [this, hH]; exact hSc

end GlobalTheory.UnipClosed
