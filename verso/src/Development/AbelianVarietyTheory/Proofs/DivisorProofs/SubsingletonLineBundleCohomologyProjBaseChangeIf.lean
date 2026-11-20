import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHomologyEquiv

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.AbLaw GlobalTheory.Adelic GlobalTheory.FieldChangeInter

namespace GlobalTheory.CohFieldChange

/- English proof (translation)
Use `letI := algebraΓOfHom f`. Use `letI := algebraΓOfHom f'`. Establish `: CompactSpace X` using `QuasiCompact.compactSpace_of_compactSpace f`. Use `isAffineHom_diagonal_of_isSeparated f` as an intermediate fact. Take `⟨m, D, hD, hc⟩` from `exists_fin_affine_cover (X := X) (V := ⊤) isCompact_univ`.

Establish `hD'` using `isAffineOpen_finset_biInf hD`. Take `⟨e₁⟩` from `nonempty_coh_equiv f hM hc hD' n`. Take `⟨e₂⟩` from `nonempty_coh_equiv f' (LB.isLB_pull hM π) (D := fun i => π ⁻¹ᵁ D i) (by rw [← Scheme.Hom.preimage_iSup, hc]; rfl) (fun s hs => isAffineOpen_biInf_preimage H (hD' s hs)) n`. Take `⟨e₃⟩` from `nonempty_homology_equiv E (cechLB f M D) n`. Establish `e₄` using `((HomologicalComplex.homologyFunctor _ _ n).mapIso (cechLBBaseChangeIso hM H hD')).toLinearEquiv`.

Use `e₂.toEquiv.subsingleton_congr.symm.trans (Iff.trans ?_ e₁.toEquiv.subsingleton_congr)` and prove the remaining obligations. Use `e₄.toEquiv.subsingleton_congr.symm.trans (e₃.toEquiv.subsingleton_congr.trans ?_)` and prove the remaining obligations. Conclude with `Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right k E`.
-/
theorem subsingleton_coh_pull_iff {X X' : Scheme.{0}} {k E : Type} [Field k] [Field E] [Algebra k E]
    {f : X ⟶ Spec (CommRingCat.of k)} {f' : X' ⟶ Spec (CommRingCat.of E)} {π : X' ⟶ X}
    [QuasiCompact f] [IsSeparated f]
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap k E)))) {M : LB X} (hM : M.IsLB) (n : ℕ) :
    Subsingleton (coh (twist (GlobalTheory.structureModule X') (M.pull π)) n) ↔
      Subsingleton (coh (twist (GlobalTheory.structureModule X) M) n) := by
  letI := algebraΓOfHom f
  letI := algebraΓOfHom f'
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have := isAffineHom_diagonal_of_isSeparated f
  obtain ⟨m, D, hD, hc⟩ := exists_fin_affine_cover (X := X) (V := ⊤) isCompact_univ
  have hD' := isAffineOpen_finset_biInf hD
  obtain ⟨e₁⟩ := nonempty_coh_equiv f hM hc hD' n
  obtain ⟨e₂⟩ := nonempty_coh_equiv f' (LB.isLB_pull hM π) (D := fun i => π ⁻¹ᵁ D i)
    (by rw [← Scheme.Hom.preimage_iSup, hc]; rfl) (fun s hs => isAffineOpen_biInf_preimage H (hD' s hs)) n
  obtain ⟨e₃⟩ := nonempty_homology_equiv E (cechLB f M D) n
  have e₄ := ((HomologicalComplex.homologyFunctor _ _ n).mapIso (cechLBBaseChangeIso hM H hD')).toLinearEquiv
  refine e₂.toEquiv.subsingleton_congr.symm.trans (Iff.trans ?_ e₁.toEquiv.subsingleton_congr)
  refine e₄.toEquiv.subsingleton_congr.symm.trans (e₃.toEquiv.subsingleton_congr.trans ?_)
  exact Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right k E

/- English proof (translation)
Introduce `k E _ _ _ Y X p q π H h _ M hM n`. Establish `: IsProper p`. Take `⟨N, i, hi, e⟩` from `h`. Use `isProper_str k N` as an intermediate fact. Rewrite using `[← e]`.

Use `infer_instance`. Conclude with `subsingleton_coh_pull_iff (f := p) (f' := q) H hM n`.
-/
theorem subsingleton_coh_pull_iff_of_isProjOver : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → IsProjOver q → ∀ M : LB Y, M.IsLB → ∀ n : ℕ, (Subsingleton (coh (twist (GlobalTheory.structureModule X) (M.pull π)) n) ↔ Subsingleton (coh (twist (GlobalTheory.structureModule Y) M) n)) := by
  intro k E _ _ _ Y X p q π H h _ M hM n
  have : IsProper p := by
    obtain ⟨N, i, hi, e⟩ := h
    have := isProper_str k N
    rw [← e]
    infer_instance
  exact subsingleton_coh_pull_iff (f := p) (f' := q) H hM n

end GlobalTheory.CohFieldChange
