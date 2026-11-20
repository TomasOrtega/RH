import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocAdMul
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Matrix

noncomputable section

namespace GlobalTheory.ColSpanDown

/- English proof (translation)
Use `set q : AF F ⊗[F] E →+* Fv F v := (splitProj τ).toRingHom.comp (compFin F E v) with hq`. Establish `hq' : ∀ z, splitProj τ (compFin F E v z) = q z` using `fun z => rfl`. Simplify using `only [hq']`. Establish `hincl : ∀ x : E, q (inclR (F` using `F) (AF F) x) = τ x := by`. Introduce `x`.

Express the relevant statement in the definitionally equal form `splitProj τ (compFin F E v (inclR (F := F) (AF F) x)) = τ x`. Establish `: compFin F E v (inclR (F` using `F) (AF F) x) = inclR (Fv F v) x := by`. Express the relevant statement in the definitionally equal form `evFin F v 1 ⊗ₜ[F] x = (1 : Fv F v) ⊗ₜ[F] x`. Rewrite using `[map_one]`. Rewrite using `[this, splitProj_inclR]`.

Unfold `GlobalTheory.StdPar.colSpan at hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨i, hi, rfl⟩` from `hx`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Use `⟨i, hi, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `k`. Simplify using `[adMat, Matrix.transpose_apply, Matrix.map_apply, hincl]`. Consider the case `zero`. Establish `e : (fun k : Fin n => q ((0 : Fin n → AF F ⊗[F] E) k)) = 0` using `by funext k; simp`.

Rewrite using `[e]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy`. Use `Submodule.add_mem _ hx hy` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules. Consider the case `smul c x _ hx`. Use `Submodule.smul_mem _ (q c) hx` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules.
-/
theorem mem_span_comp {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v) {n r : ℕ} (X : Matrix (Fin n) (Fin r) E) (I : Set (Fin r))
    (y : Fin n → AF F ⊗[F] E) (hy : y ∈ GlobalTheory.StdPar.colSpan F X I) :
    (fun k => splitProj τ (compFin F E v (y k))) ∈ Submodule.span (Fv F v) ((fun i k => τ (X k i)) '' I) := by
  set q : AF F ⊗[F] E →+* Fv F v := (splitProj τ).toRingHom.comp (compFin F E v) with hq
  have hq' : ∀ z, splitProj τ (compFin F E v z) = q z := fun z => rfl
  simp only [hq']
  have hincl : ∀ x : E, q (inclR (F := F) (AF F) x) = τ x := by
    intro x
    change splitProj τ (compFin F E v (inclR (F := F) (AF F) x)) = τ x
    have : compFin F E v (inclR (F := F) (AF F) x) = inclR (Fv F v) x := by
      change evFin F v 1 ⊗ₜ[F] x = (1 : Fv F v) ⊗ₜ[F] x
      rw [map_one]
    rw [this, splitProj_inclR]
  unfold GlobalTheory.StdPar.colSpan at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨i, hi, ?_⟩
    funext k
    simp [adMat, Matrix.transpose_apply, Matrix.map_apply, hincl]
  | zero =>
    have e : (fun k : Fin n => q ((0 : Fin n → AF F ⊗[F] E) k)) = 0 := by funext k; simp
    rw [e]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have := Submodule.add_mem _ hx hy
    convert this using 1
    funext k; simp
  | smul c x _ hx =>
    have := Submodule.smul_mem _ (q c) hx
    convert this using 1
    funext k; simp

end GlobalTheory.ColSpanDown

end
