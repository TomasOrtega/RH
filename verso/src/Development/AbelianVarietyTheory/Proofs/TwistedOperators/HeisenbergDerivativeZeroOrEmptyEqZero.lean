import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open scoped Classical

namespace GlobalTheory.HeisDerivZero

/- English proof (translation)
Assemble the required witnesses or components as `⟨((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y, 0), (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y⟩`.
-/
theorem evI_surj {F : Type} [Field F] [NumberField F] (y : mixedEmbedding.mixedSpace F) : ∃ a : AF F, evI F a = y :=
  ⟨((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y, 0), (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y⟩

/- English proof (translation)
Establish `hR : Rest (evI F) g (fun _ => 1)`. Use `⟨fun _ _ _ => rfl, ?_⟩` and prove the remaining obligations. Break down `hc with rfl | hE` into its components or cases. Establish `: tens (evI F) (⇑(0 : SInf F (Fin n × Fin d))) (fun _ => 1) = 0`. Use function extensionality and compare the values at `x`.

Simplify using `[tens]`. Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`. Use `Submodule.subset_span ⟨g, fun _ => 1, ⟨IsLocallyConstant.const 1, ?_⟩, rfl⟩` and prove the remaining obligations. Conclude with `HasCompactSupport.of_compactSpace _`.

Establish `hconst : ∀ t x, M.heisLine ψ u t (tens (evI F) g fun _ => 1) x = tens (evI F) g (fun _ => 1) x`. Introduce `t x`. Break down `hc with rfl | hE` into its components or cases. Simplify using `[Model.heisLine, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, tens]`. Simplify using `only [Model.heisLine, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, dotProduct, Finset.univ_eq_empty, Finset.sum_empty, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul]`.

Use `congr 1`. Conclude with `Subsingleton.elim _ _`. Use extensionality with `y`. Use `choose x hx using fun i => evI_surj (F := F) (y i)`. Establish `h1` using `hA _ hR x`.

Simplify using `only [hconst] at h1`. Establish `h2` using `h1.unique (hasDerivAt_const _ _)`. Simplify `h2` using `[tens, hx]`.
-/
theorem actsD_eq_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (g h : SInf F (Fin n × Fin d)) (u : Matrix (Fin n) (Fin d) (AE F E))
    (hA : ActsD (evI F) (M.heisLine ψ u) g h) (hc : g = 0 ∨ IsEmpty (Fin n × Fin d)) : h = 0 := by
  have hR : Rest (evI F) g (fun _ => 1) := by
    refine ⟨fun _ _ _ => rfl, ?_⟩
    rcases hc with rfl | hE
    · have : tens (evI F) (⇑(0 : SInf F (Fin n × Fin d))) (fun _ => 1) = 0 := by
        funext x; simp [tens]
      rw [this]; exact Submodule.zero_mem _
    · refine Submodule.subset_span ⟨g, fun _ => 1, ⟨IsLocallyConstant.const 1, ?_⟩, rfl⟩
      exact HasCompactSupport.of_compactSpace _
  have hconst : ∀ t x, M.heisLine ψ u t (tens (evI F) g fun _ => 1) x = tens (evI F) g (fun _ => 1) x := by
    intro t x
    rcases hc with rfl | hE
    · simp [Model.heisLine, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, tens]
    · simp only [Model.heisLine, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, dotProduct, Finset.univ_eq_empty,
        Finset.sum_empty, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul]
      congr 1
      exact Subsingleton.elim _ _
  ext y
  choose x hx using fun i => evI_surj (F := F) (y i)
  have h1 := hA _ hR x
  simp only [hconst] at h1
  have h2 := h1.unique (hasDerivAt_const _ _)
  simpa [tens, hx] using h2

end GlobalTheory.HeisDerivZero
