import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetTensorProductEquivStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionOpenCellModuloWhittakerStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellJacquetMapSurjectiveWhittakerStatement

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier

/- English proof (translation)
Introduce `k _ _ _ _ ψ hψ hψ1 h N d hd X _ _ π hπ`. Take `⟨J, hJs, hJ⟩` from `GlobalTheory.T.open_cell_jacquet_map_surjective_whittaker k ψ hψ h N d hd (piTensor π) (isSmooth_piTensor hπ)`. Take `⟨E⟩` from `GlobalTheory.T.twisted_jacquet_tensor_product_equiv π (fun a => unipB k (Fin (d a))) (fun a => whitChar ψ (d a))`. Use `set T := twKer (multiProd (stdBlocks d hd) π) (unipB k (Fin N)) (whitChar ψ N) with hT`. Use `set S := twKer (piTensor π) (unipM k d) (whitM d ψ) with hS`.

Set `a : openFns d hd (piTensor π) →ₗ[ℂ] (IndSp (stdBlocks d hd) (piTensor π)) ⧸ T` to `T.mkQ ∘ₗ (openFns d hd (piTensor π)).subtype`. Set `b : openFns d hd (piTensor π) →ₗ[ℂ] (⨂[ℂ] a, X a) ⧸ S` to `S.mkQ ∘ₗ J`. Establish `ha : Function.Surjective a`. Introduce `y`. Take `⟨f, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`.

Take `⟨f₀, h0, h1⟩` from `GlobalTheory.T.induced_function_open_cell_modulo_whittaker k ψ hψ hψ1 h N d hd (piTensor π) f`. Use `⟨⟨f₀, h0⟩, ?_⟩` and prove the remaining obligations. Conclude with `((Submodule.Quotient.eq T).2 (by simpa [neg_sub] using T.neg_mem h1))`. Establish `hb : Function.Surjective b`. Introduce `y`.

Take `⟨w, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Take `⟨f, rfl⟩` from `hJs w`. Conclude with `⟨f, rfl⟩`. Establish `hker : LinearMap.ker a = LinearMap.ker b`. Use extensionality with `f`.

Simplify using `only [a, b, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.subtype_apply]`. Conclude with `(hJ f).symm`. Conclude with `⟨(a.quotKerEquivOfSurjective ha).symm.trans ((Submodule.quotEquivOfEq _ _ hker).trans ((b.quotKerEquivOfSurjective hb).trans E))⟩`.
-/
theorem whitHeredity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    WhitHeredity k := by
  intro k _ _ _ _ ψ hψ hψ1 h N d hd X _ _ π hπ
  obtain ⟨J, hJs, hJ⟩ := GlobalTheory.T.open_cell_jacquet_map_surjective_whittaker k ψ hψ h N d hd (piTensor π) (isSmooth_piTensor hπ)
  obtain ⟨E⟩ := GlobalTheory.T.twisted_jacquet_tensor_product_equiv π (fun a => unipB k (Fin (d a))) (fun a => whitChar ψ (d a))
  set T := twKer (multiProd (stdBlocks d hd) π) (unipB k (Fin N)) (whitChar ψ N) with hT
  set S := twKer (piTensor π) (unipM k d) (whitM d ψ) with hS
  let a : openFns d hd (piTensor π) →ₗ[ℂ] (IndSp (stdBlocks d hd) (piTensor π)) ⧸ T :=
    T.mkQ ∘ₗ (openFns d hd (piTensor π)).subtype
  let b : openFns d hd (piTensor π) →ₗ[ℂ] (⨂[ℂ] a, X a) ⧸ S := S.mkQ ∘ₗ J
  have ha : Function.Surjective a := by
    intro y
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨f₀, h0, h1⟩ := GlobalTheory.T.induced_function_open_cell_modulo_whittaker k ψ hψ hψ1 h N d hd (piTensor π) f
    refine ⟨⟨f₀, h0⟩, ?_⟩
    exact ((Submodule.Quotient.eq T).2 (by simpa [neg_sub] using T.neg_mem h1))
  have hb : Function.Surjective b := by
    intro y
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨f, rfl⟩ := hJs w
    exact ⟨f, rfl⟩
  have hker : LinearMap.ker a = LinearMap.ker b := by
    ext f
    simp only [a, b, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.subtype_apply]
    exact (hJ f).symm
  exact ⟨(a.quotKerEquivOfSurjective ha).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans ((b.quotKerEquivOfSurjective hb).trans E))⟩

end GlobalTheory.CompanionTheory.Rodier
