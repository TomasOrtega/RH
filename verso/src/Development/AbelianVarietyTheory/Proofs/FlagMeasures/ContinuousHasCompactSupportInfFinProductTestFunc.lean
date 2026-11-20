import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurableEmbeddingAdelicTupleLocalComponents
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory.ProdCont

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) {M n : ℕ}

noncomputable def glueTup (Y : (Fin n → Fin M → Ainf F ⊗[F] E) × (Fin n → Fin M → Af F ⊗[F] E)) :
    Fin n → Fin M → AF F ⊗[F] E :=
  fun a i => (Algebra.TensorProduct.basis (AF F) b).equivFun.symm fun k =>
    pairA F ((Algebra.TensorProduct.basis (Ainf F) b).repr (Y.1 a i) k)
      ((Algebra.TensorProduct.basis (Af F) b).repr (Y.2 a i) k)

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.Finite.of_basis b`. Use `haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _`. Use `haveI : ContinuousSMul (AF F) (AF F ⊗[F] E) := IsModuleTopology.toContinuousSMul (AF F) _`. Establish `hs : Continuous (Algebra.TensorProduct.basis (AF F) b).equivFun.symm` using `IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis (AF F) b).equivFun.symm.toLinearMap`. Establish `hi : Continuous (Algebra.TensorProduct.basis (Ainf F) b).equivFun` using `IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis (Ainf F) b).equivFun.toLinearMap`.

Establish `hf : Continuous (Algebra.TensorProduct.basis (Af F) b).equivFun` using `IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis (Af F) b).equivFun.toLinearMap`. Use `continuous_pi fun a => continuous_pi fun i => hs.comp (continuous_pi fun k => ?_)` and prove the remaining obligations. Establish `h1 : Continuous fun Y : (Fin n → Fin M → Ainf F ⊗[F] E) × (Fin n → Fin M → Af F ⊗[F] E) => (Algebra.TensorProduct.basis (Ainf F) b).equivFun (Y.1 a i) k` using `(continuous_apply k).comp (hi.comp ((continuous_apply i).comp ((continuous_apply a).comp continuous_fst)))`. Establish `h2 : Continuous fun Y : (Fin n → Fin M → Ainf F ⊗[F] E) × (Fin n → Fin M → Af F ⊗[F] E) => (Algebra.TensorProduct.basis (Af F) b).equivFun (Y.2 a i) k` using `(continuous_apply k).comp (hf.comp ((continuous_apply i).comp ((continuous_apply a).comp continuous_snd)))`. Conclude with `(h1.prodMk h2 :)`.
-/
theorem continuous_glueTup : Continuous (glueTup (F := F) (E := E) b (M := M) (n := n)) := by
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  haveI : ContinuousSMul (AF F) (AF F ⊗[F] E) := IsModuleTopology.toContinuousSMul (AF F) _
  have hs : Continuous (Algebra.TensorProduct.basis (AF F) b).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis (AF F) b).equivFun.symm.toLinearMap
  have hi : Continuous (Algebra.TensorProduct.basis (Ainf F) b).equivFun :=
    IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis (Ainf F) b).equivFun.toLinearMap
  have hf : Continuous (Algebra.TensorProduct.basis (Af F) b).equivFun :=
    IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis (Af F) b).equivFun.toLinearMap
  refine continuous_pi fun a => continuous_pi fun i => hs.comp (continuous_pi fun k => ?_)
  have h1 : Continuous fun Y : (Fin n → Fin M → Ainf F ⊗[F] E) × (Fin n → Fin M → Af F ⊗[F] E) =>
      (Algebra.TensorProduct.basis (Ainf F) b).equivFun (Y.1 a i) k :=
    (continuous_apply k).comp (hi.comp ((continuous_apply i).comp ((continuous_apply a).comp continuous_fst)))
  have h2 : Continuous fun Y : (Fin n → Fin M → Ainf F ⊗[F] E) × (Fin n → Fin M → Af F ⊗[F] E) =>
      (Algebra.TensorProduct.basis (Af F) b).equivFun (Y.2 a i) k :=
    (continuous_apply k).comp (hf.comp ((continuous_apply i).comp ((continuous_apply a).comp continuous_snd)))
  exact (h1.prodMk h2 :)

/- English proof (translation)
Use function extensionality and compare the values at `a i`. Use `GlobalTheory.GaugeGlue.tens_ext b fun k => ?_` and prove the remaining obligations. Simplify using `only [glueTup]`. Rewrite using `[← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]`. Simplify using `only [projInf, projFin, Module.Basis.equivFun_apply, GlobalTheory.GaugeGlue.repr_map]`.

Both sides reduce to the same expression.
-/
theorem glueTup_proj (X : Fin n → Fin M → AF F ⊗[F] E) :
    glueTup b (projInf X, projFin X) = X := by
  funext a i
  refine GlobalTheory.GaugeGlue.tens_ext b fun k => ?_
  simp only [glueTup]
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  simp only [projInf, projFin, Module.Basis.equivFun_apply, GlobalTheory.GaugeGlue.repr_map]
  rfl

end GlobalTheory.ProdCont

open GlobalTheory.ProdCont in

/- English proof (translation)
Introduce `F E _ _ _ _ _ M n Φ Φi Φf hci hki hcf hkf hΦ`. Use `haveI : FiniteDimensional F E := inferInstance`. Set `b` to `Module.finBasis F E`. Establish `hpf : Continuous (projFin (F` using `F) (E := E) (M := M) (n := n)) := continuous_pi fun a => continuous_pi fun i => (GlobalTheory.GaugeGlue.continuous_map b (sndA F) GlobalTheory.GaugeGlue.continuous_sndA).comp ((continuous_apply i).comp (continuous_apply a))`. Establish `hpi` using `GlobalTheory.GaugeGlue.continuous_projInf (F := F) (E := E) (M := M) (n := n) b`.

Establish `hEq : Φ = fun X => Φi (projInf X) * Φf (projFin X)` using `funext hΦ`. Use `⟨hEq ▸ (hci.comp hpi).mul (hcf.comp hpf), ?_⟩` and prove the remaining obligations. Establish `hg : Continuous fun X : Fin n → Fin M → AF F ⊗[F] E => (projInf X, projFin X)` using `hpi.prodMk hpf`. Establish `hK : IsCompact (tsupport Φi ×ˢ tsupport Φf)` using `hki.isCompact.prod hkf.isCompact`. Establish `hsub : tsupport Φ ⊆ (fun X => (projInf X, projFin X)) ⁻¹' (tsupport Φi ×ˢ tsupport Φf)`.

Use `closure_minimal (fun X hX => ?_) ((isClosed_tsupport Φi).prod (isClosed_tsupport Φf) |>.preimage hg)` and prove the remaining obligations. Establish `h0 : Φi (projInf X) * Φf (projFin X) ≠ 0` using `by rw [← hΦ]; exact hX`. Conclude with `⟨subset_tsupport _ (left_ne_zero_of_mul h0), subset_tsupport _ (right_ne_zero_of_mul h0)⟩`. Establish `hsub2 : tsupport Φ ⊆ glueTup b '' (tsupport Φi ×ˢ tsupport Φf)` using `fun X hX => ⟨_, hsub hX, glueTup_proj b X⟩`. Conclude with `(hK.image (continuous_glueTup b)).of_isClosed_subset (isClosed_tsupport Φ) hsub2`.
-/
theorem GlobalTheory.prod_continuous_hasCompactSupport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (M n : ℕ) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ), Continuous Φi → HasCompactSupport Φi → Continuous Φf → HasCompactSupport Φf → IsProdInfFin Φ Φi Φf → Continuous Φ ∧ HasCompactSupport Φ := by
  intro F E _ _ _ _ _ M n Φ Φi Φf hci hki hcf hkf hΦ
  haveI : FiniteDimensional F E := inferInstance
  let b := Module.finBasis F E
  have hpf : Continuous (projFin (F := F) (E := E) (M := M) (n := n)) :=
    continuous_pi fun a => continuous_pi fun i =>
      (GlobalTheory.GaugeGlue.continuous_map b (sndA F) GlobalTheory.GaugeGlue.continuous_sndA).comp
        ((continuous_apply i).comp (continuous_apply a))
  have hpi := GlobalTheory.GaugeGlue.continuous_projInf (F := F) (E := E) (M := M) (n := n) b
  have hEq : Φ = fun X => Φi (projInf X) * Φf (projFin X) := funext hΦ
  refine ⟨hEq ▸ (hci.comp hpi).mul (hcf.comp hpf), ?_⟩
  have hg : Continuous fun X : Fin n → Fin M → AF F ⊗[F] E => (projInf X, projFin X) :=
    hpi.prodMk hpf
  have hK : IsCompact (tsupport Φi ×ˢ tsupport Φf) := hki.isCompact.prod hkf.isCompact
  have hsub : tsupport Φ ⊆ (fun X => (projInf X, projFin X)) ⁻¹' (tsupport Φi ×ˢ tsupport Φf) := by
    refine closure_minimal (fun X hX => ?_)
      ((isClosed_tsupport Φi).prod (isClosed_tsupport Φf) |>.preimage hg)
    have h0 : Φi (projInf X) * Φf (projFin X) ≠ 0 := by rw [← hΦ]; exact hX
    exact ⟨subset_tsupport _ (left_ne_zero_of_mul h0), subset_tsupport _ (right_ne_zero_of_mul h0)⟩
  have hsub2 : tsupport Φ ⊆ glueTup b '' (tsupport Φi ×ˢ tsupport Φf) := fun X hX =>
    ⟨_, hsub hX, glueTup_proj b X⟩
  exact (hK.image (continuous_glueTup b)).of_isClosed_subset (isClosed_tsupport Φ) hsub2
