import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfSlices
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsAdaptedEmpty
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FrameFamilyRightTranslateStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LanglandsDecompositionUnipotentLeviStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviDecompositionHermitianCentralizerStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianPartLeLeviStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviNormalizesUnipotentVariantStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanIwasawaMinimalParabolicStatement
import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.CuspidalConstantTerms.CoeffSpanCompMem
import GroundTheory.PAdicHodge.NormalizedTrace

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Rg

/- English proof (translation)
Introduce `D θ hθ V U hU ε fr hfr W _ _ _ ρ hρ c m X Y hWF T hT b`. Take `⟨n, hn, mm, hmm, b₀, hb, had⟩` from `GlobalTheory.T.langlands_decomposition_unipotent_levi D θ hθ V ε fr hfr m X Y hWF T b`. Take `⟨mH, hmH, mo, hmo, hcomm, rfl⟩` from `GlobalTheory.T.levi_decomposition_hermitian_centralizer D V m X Y hWF T mm hmm`. Substitute `hb` using the available equality. Establish `hU' : IsOpen ((U.map (MulAut.conj b₀).toMonoidHom : Subgroup (GA D V)) : Set (GA D V))`.

Establish `e : ((U.map (MulAut.conj b₀).toMonoidHom : Subgroup (GA D V)) : Set (GA D V)) = (fun x => b₀⁻¹ * x * b₀) ⁻¹' (U : Set (GA D V))`. Use extensionality with `x`. Simplify using `only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_preimage, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, rfl⟩`.

Simplify `hu` using `[mul_assoc]`. Introduce `hx`. Conclude with `⟨b₀⁻¹ * x * b₀, hx, by group⟩`. Rewrite using `[e]`. Conclude with `hU.preimage (by fun_prop)`.

Establish `hfr'` using `GlobalTheory.T.frame_family_right_translate D θ hθ V ε fr hfr b₀`. Establish `hfin` using `finite_slices_core D θ hθ V _ hU' ε _ hfr' W ρ hρ c m X Y hWF T hT had`. Use `set H := uPart D.sp.cm.sig V.gram X Y T with hH`. Use `set L := levi D.sp.cm.sig V.gram X Y T with hL`. Set `mH' : H` to `⟨mH, hmH⟩`.

Set `R : (H → ℂ) →ₗ[ℂ] (H → ℂ)` to `{ toFun := fun f t => f (t * mH') map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Establish `hsub : sliceSet (cuspOn θ V X Y T U ε fr ρ c) H L (n * (mH * mo) * b₀) ⊆ ((Submodule.span ℂ (sliceSet (cuspOn θ V X Y T (U.map (MulAut.conj b₀).toMonoidHom) ε (fun τ => fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b₀)⁻¹) ρ c) H L 1)).map R : Set (H → ℂ))`. Introduce and unpack `f ⟨φ, hφ, y, hy, hyc, rfl⟩`. Use `⟨fun t : H => φ ((t : GA D V) * (y * mo) * b₀), Submodule.subset_span ⟨fun x => φ (x * b₀), GlobalTheory.T.constant_term_frame_K_type_coefficients D θ hθ V U ε fr hfr W ρ c m X Y T φ hφ b₀, y * mo, mul_mem hy hmo, fun t ht => ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, hyc t ht, mul_assoc, hcomm t ht, mul_assoc]`.

Use function extensionality and compare the values at `t`. Simplify using `[mul_assoc]`. Use function extensionality and compare the values at `t`. Establish `ht : (t : GA D V) ∈ L` using `GlobalTheory.T.hermitian_part_le_levi D V m X Y T t.2`. Establish `hty : (t : GA D V) * y ∈ L` using `mul_mem ht hy`.

Establish `hγ : (t : GA D V) * y * n * ((t : GA D V) * y)⁻¹ ∈ unip D.sp.cm.sig V.gram X T` using `GlobalTheory.T.levi_normalizes_unipotent_variant D V m X Y hWF T _ hty n hn`. Establish `hleft` using `hφ.1.1.left _ (Subgroup.mem_sup_left hγ : _ ∈ (leftSub V X Y T : Subgroup (GA D V))) ((t : GA D V) * y * (mH * mo * b₀))`. Establish `e1 : (t : GA D V) * y * n * ((t : GA D V) * y)⁻¹ * ((t : GA D V) * y * (mH * mo * b₀)) = (t : GA D V) * y * (n * (mH * mo) * b₀)` using `by group`. Establish `e2 : (t : GA D V) * y * (mH * mo * b₀) = (t : GA D V) * mH * (y * mo) * b₀`. Use `hyc mH hmH` as an intermediate fact.

Combine the equalities or inequalities in the displayed calculation. Express the relevant statement in the definitionally equal form `φ ((t : GA D V) * mH * (y * mo) * b₀) = φ ((t : GA D V) * y * (n * (mH * mo) * b₀))`. Rewrite using `[← e1, hleft, e2]`. Use `haveI := hfin`. Conclude with `Submodule.finiteDimensional_of_le (Submodule.span_le.2 hsub)`.
-/
theorem finite_slices_uPart : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)), (∀ τ, IsContRep (ρ τ)) → ∀ (c : D.what₂.Tau → ℕ → ℂ) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ T : Finset (Fin m), T.Nonempty → ∀ b : GA D V, FiniteDimensional ℂ (Submodule.span ℂ (sliceSet (cuspOn θ V X Y T U ε fr ρ c) (uPart D.sp.cm.sig V.gram X Y T) (levi D.sp.cm.sig V.gram X Y T) b)) := by
  intro D θ hθ V U hU ε fr hfr W _ _ _ ρ hρ c m X Y hWF T hT b
  obtain ⟨n, hn, mm, hmm, b₀, hb, had⟩ := GlobalTheory.T.langlands_decomposition_unipotent_levi D θ hθ V ε fr hfr m X Y hWF T b
  obtain ⟨mH, hmH, mo, hmo, hcomm, rfl⟩ := GlobalTheory.T.levi_decomposition_hermitian_centralizer D V m X Y hWF T mm hmm
  subst hb
  have hU' : IsOpen ((U.map (MulAut.conj b₀).toMonoidHom : Subgroup (GA D V)) : Set (GA D V)) := by
    have e : ((U.map (MulAut.conj b₀).toMonoidHom : Subgroup (GA D V)) : Set (GA D V)) =
        (fun x => b₀⁻¹ * x * b₀) ⁻¹' (U : Set (GA D V)) := by
      ext x
      simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_preimage, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      constructor
      · rintro ⟨u, hu, rfl⟩
        simpa [mul_assoc] using hu
      · intro hx
        exact ⟨b₀⁻¹ * x * b₀, hx, by group⟩
    rw [e]
    exact hU.preimage (by fun_prop)
  have hfr' := GlobalTheory.T.frame_family_right_translate D θ hθ V ε fr hfr b₀
  have hfin := finite_slices_core D θ hθ V _ hU' ε _ hfr' W ρ hρ c m X Y hWF T hT had
  set H := uPart D.sp.cm.sig V.gram X Y T with hH
  set L := levi D.sp.cm.sig V.gram X Y T with hL
  let mH' : H := ⟨mH, hmH⟩
  let R : (H → ℂ) →ₗ[ℂ] (H → ℂ) :=
    { toFun := fun f t => f (t * mH')
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hsub : sliceSet (cuspOn θ V X Y T U ε fr ρ c) H L (n * (mH * mo) * b₀) ⊆
      ((Submodule.span ℂ (sliceSet (cuspOn θ V X Y T (U.map (MulAut.conj b₀).toMonoidHom) ε
        (fun τ => fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b₀)⁻¹) ρ c) H L 1)).map R : Set (H → ℂ)) := by
    rintro f ⟨φ, hφ, y, hy, hyc, rfl⟩
    refine ⟨fun t : H => φ ((t : GA D V) * (y * mo) * b₀),
      Submodule.subset_span ⟨fun x => φ (x * b₀), GlobalTheory.T.constant_term_frame_K_type_coefficients D θ hθ V U ε fr hfr W ρ c m X Y T φ hφ b₀, y * mo,
        mul_mem hy hmo, fun t ht => ?_, ?_⟩, ?_⟩
    · rw [← mul_assoc, hyc t ht, mul_assoc, hcomm t ht, mul_assoc]
    · funext t
      simp [mul_assoc]
    · funext t
      have ht : (t : GA D V) ∈ L := GlobalTheory.T.hermitian_part_le_levi D V m X Y T t.2
      have hty : (t : GA D V) * y ∈ L := mul_mem ht hy
      have hγ : (t : GA D V) * y * n * ((t : GA D V) * y)⁻¹ ∈ unip D.sp.cm.sig V.gram X T :=
        GlobalTheory.T.levi_normalizes_unipotent_variant D V m X Y hWF T _ hty n hn
      have hleft := hφ.1.1.left _ (Subgroup.mem_sup_left hγ : _ ∈ (leftSub V X Y T : Subgroup (GA D V)))
        ((t : GA D V) * y * (mH * mo * b₀))
      have e1 : (t : GA D V) * y * n * ((t : GA D V) * y)⁻¹ * ((t : GA D V) * y * (mH * mo * b₀)) =
          (t : GA D V) * y * (n * (mH * mo) * b₀) := by group
      have e2 : (t : GA D V) * y * (mH * mo * b₀) = (t : GA D V) * mH * (y * mo) * b₀ := by
        have := hyc mH hmH
        calc (t : GA D V) * y * (mH * mo * b₀) = (t : GA D V) * (y * mH) * mo * b₀ := by group
          _ = (t : GA D V) * (mH * y) * mo * b₀ := by rw [this]
          _ = (t : GA D V) * mH * (y * mo) * b₀ := by group
      change φ ((t : GA D V) * mH * (y * mo) * b₀) = φ ((t : GA D V) * y * (n * (mH * mo) * b₀))
      rw [← e1, hleft, e2]
  haveI := hfin
  exact Submodule.finiteDimensional_of_le (Submodule.span_le.2 hsub)

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Rg

end
