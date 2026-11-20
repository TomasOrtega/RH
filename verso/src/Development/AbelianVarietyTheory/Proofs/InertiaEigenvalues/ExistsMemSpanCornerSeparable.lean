import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepresentationDensityOfIsInternalConstituentStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCornerSeparableCharpolyOfIsInternalStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.SpanRing

/- English proof (translation)
Take `⟨ι, _, _, Vs, hs, hint, -, hspan, hdist⟩` from `h`. Establish `hstab : ∀ j, ∀ M ∈ Submodule.span K (Set.range σ), ∀ v ∈ Vs j, M.mulVec v ∈ Vs j`. Introduce `j M hM`. Proceed by induction on `hM using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨g, rfl⟩` from `hx`. Introduce `v hv`. Conclude with `hs j g v hv`. Consider the case `zero => intro v _`. Simplify using the standard rewrite rules.

Consider the case `add x y _ _ hx hy`. Introduce `v hv`. Rewrite using `[Matrix.add_mulVec]`. Conclude with `(Vs j).add_mem (hx v hv) (hy v hv)`. Consider the case `smul c x _ hx`.

Introduce `v hv`. Rewrite using `[show (c • x).mulVec v = c • x.mulVec v by`. Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]]`. Conclude with `(Vs j).smul_mem c (hx v hv)`.

Take `⟨m, hm, hsep⟩` from `GlobalTheory.T.exists_corner_separable_charpoly_of_isInternal ι Vs a b hint hba (fun j => hstab j _ hab)`. Use `⟨m, ?_, hsep⟩` and prove the remaining obligations. Establish `hlin` using `GlobalTheory.T.span_representation_density_of_isInternal_constituents (matRep σ) ι Vs hs hint hspan hdist (Matrix.toLin' m) (fun j v hv => by simpa [Matrix.toLin'_apply] using hm j v hv)`. Establish `hfun : (⇑(matRep σ)) = ⇑(Matrix.toLin' : Matrix (Fin n) (Fin n) K ≃ₗ[K] _) ∘ ⇑σ` using `rfl`. Rewrite `hlin` using `[hfun, Set.range_comp]`.

Establish `hle : Submodule.span K (⇑(Matrix.toLin' : Matrix (Fin n) (Fin n) K ≃ₗ[K] _) '' Set.range ⇑σ) ≤ (Submodule.span K (Set.range σ)).map (Matrix.toLin' : Matrix (Fin n) (Fin n) K ≃ₗ[K] _).toLinearMap`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨M, hM, rfl⟩`. Conclude with `⟨M, Submodule.subset_span hM, rfl⟩`. Take `⟨y, hy, hye⟩` from `hle hlin`.

Establish `hym : y = m` using `Matrix.toLin'.injective hye`. Rewrite `hy` using `[hym]`. Then use the resulting hypothesis.
-/
theorem exists_mem_span_corner_separable {K Γ : Type} [Field K] [Infinite K] [Group Γ] {n t : ℕ}
    (σ : Γ →* Matrix (Fin n) (Fin n) K) (a : Matrix (Fin n) (Fin t) K)
    (b : Matrix (Fin t) (Fin n) K) (h : AbsIrrDistinct (matRep σ)) (hba : b * a = 1)
    (hab : a * b ∈ Submodule.span K (Set.range σ)) :
    ∃ m ∈ Submodule.span K (Set.range σ), (b * m * a).charpoly.Separable := by
  obtain ⟨ι, _, _, Vs, hs, hint, -, hspan, hdist⟩ := h
  have hstab : ∀ j, ∀ M ∈ Submodule.span K (Set.range σ), ∀ v ∈ Vs j, M.mulVec v ∈ Vs j := by
    intro j M hM
    induction hM using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      intro v hv
      exact hs j g v hv
    | zero => intro v _; simp
    | add x y _ _ hx hy =>
      intro v hv
      rw [Matrix.add_mulVec]
      exact (Vs j).add_mem (hx v hv) (hy v hv)
    | smul c x _ hx =>
      intro v hv
      rw [show (c • x).mulVec v = c • x.mulVec v by
        ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]]
      exact (Vs j).smul_mem c (hx v hv)
  obtain ⟨m, hm, hsep⟩ := GlobalTheory.T.exists_corner_separable_charpoly_of_isInternal ι Vs a b hint hba (fun j => hstab j _ hab)
  refine ⟨m, ?_, hsep⟩
  have hlin := GlobalTheory.T.span_representation_density_of_isInternal_constituents (matRep σ) ι Vs hs hint hspan hdist (Matrix.toLin' m)
    (fun j v hv => by simpa [Matrix.toLin'_apply] using hm j v hv)
  have hfun : (⇑(matRep σ)) = ⇑(Matrix.toLin' : Matrix (Fin n) (Fin n) K ≃ₗ[K] _) ∘ ⇑σ := rfl
  rw [hfun, Set.range_comp] at hlin
  have hle : Submodule.span K (⇑(Matrix.toLin' : Matrix (Fin n) (Fin n) K ≃ₗ[K] _) '' Set.range ⇑σ) ≤
      (Submodule.span K (Set.range σ)).map
        (Matrix.toLin' : Matrix (Fin n) (Fin n) K ≃ₗ[K] _).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨M, hM, rfl⟩
    exact ⟨M, Submodule.subset_span hM, rfl⟩
  obtain ⟨y, hy, hye⟩ := hle hlin
  have hym : y = m := Matrix.toLin'.injective hye
  rwa [hym] at hy

end GlobalTheory.SpanRing
