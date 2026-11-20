import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StatementsFlZArithVar
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StatementsFlZIdealEqCoord
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFlagArithVar
import GroundTheory.HeightsAndTheta.Heights.Intersections.PBlockRatioAlg
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace FlZArithVar

section Rename

variable {K : Type} [Fintype K] {ι ι' : K → Type} [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]

omit [Fintype K] in

/- English proof (translation)
Introduce `m hm k`. Rewrite `hm` using `[support_rename_of_injective (Equiv.sigmaCongrRight e).injective, Finset.mem_image]`. Take `⟨m0, hm0, rfl⟩` from `hm`. Establish `h1 : ∀ i : ι' k, Finsupp.mapDomain (Equiv.sigmaCongrRight e) m0 ⟨k, i⟩ = m0 ⟨k, (e k).symm i⟩`. Introduce `i`.

Establish `: (⟨k, i⟩ : Σ k, ι' k) = Equiv.sigmaCongrRight e ⟨k, (e k).symm i⟩` using `by simp`. Rewrite using `[this, Finsupp.mapDomain_apply (Equiv.sigmaCongrRight e).injective]`. Simplify using `only [h1]`. Rewrite using `[Equiv.sum_comp (e k).symm (fun j => m0 ⟨k, j⟩)]`. Conclude with `hg m0 hm0 k`.
-/
theorem isMultiHomog_rename_sigma (e : ∀ k, ι k ≃ ι' k) {g : MRing ι} {a : K → ℕ}
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (rename (Equiv.sigmaCongrRight e) g : MRing ι') a := by
  classical
  intro m hm k
  rw [support_rename_of_injective (Equiv.sigmaCongrRight e).injective, Finset.mem_image] at hm
  obtain ⟨m0, hm0, rfl⟩ := hm
  have h1 : ∀ i : ι' k, Finsupp.mapDomain (Equiv.sigmaCongrRight e) m0 ⟨k, i⟩ = m0 ⟨k, (e k).symm i⟩ := by
    intro i
    have : (⟨k, i⟩ : Σ k, ι' k) = Equiv.sigmaCongrRight e ⟨k, (e k).symm i⟩ := by simp
    rw [this, Finsupp.mapDomain_apply (Equiv.sigmaCongrRight e).injective]
  simp only [h1]
  rw [Equiv.sum_comp (e k).symm (fun j => m0 ⟨k, j⟩)]
  exact hg m0 hm0 k

/- English proof (translation)
Take `⟨hne, ⟨hprime, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩` from `hP`. Set `E : MRing ι ≃+* MRing ι'` to `(renameEquiv ℤ (Equiv.sigmaCongrRight e)).toRingEquiv`. Establish `hQ : P.comap (rename (Equiv.sigmaCongrRight e) : MRing ι →ₐ[ℤ] MRing ι') = P.map E.symm`. Rewrite using `[Ideal.map_symm]`. Both sides reduce to the same expression.

Establish `hEs : ∀ g, E.symm g = rename (Equiv.sigmaCongrRight fun k => (e k).symm) g`. Introduce `g`. Use `show (renameEquiv ℤ (Equiv.sigmaCongrRight e)).symm g = _`. Rewrite using `[renameEquiv_symm, Equiv.sigmaCongrRight_symm]`. Both sides reduce to the same expression.

Use `⟨hne, ⟨?_, ⟨E.symm '' S, ?_, ?_⟩, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Ideal.comap_isPrime _ _`. Introduce and unpack `_ ⟨g, hg, rfl⟩`. Take `⟨a, ha⟩` from `hS g hg`. Conclude with `⟨a, by rw [hEs]; exact isMultiHomog_rename_sigma (fun k => (e k).symm) ha⟩`.

Rewrite using `[hQ, hPS, Ideal.map_span]`. Introduce `k`. Take `⟨i, hi⟩` from `hrel k`. Use `⟨(e k).symm i, fun hj => hi ?_⟩` and prove the remaining obligations. Rewrite `hj` using `[Ideal.mem_comap]`.

Simplify using `using hj`. Establish `h : Ideal.comap (C : ℤ →+* MRing ι) (P.comap (rename (Equiv.sigmaCongrRight e) : MRing ι →ₐ[ℤ] MRing ι')) = Ideal.comap (C : ℤ →+* MRing ι') P`. Use extensionality with `x`. Simplify using `only [Ideal.mem_comap, rename_C]`. Unfold `IsHorizontal`.

Rewrite using `[h]`. Conclude with `hhor`. Rewrite using `[← hdim]`. Use `ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ P E ?_)` and prove the remaining obligations. Use `show P = Ideal.map (E : MRing ι →+* MRing ι') (Ideal.comap (E : MRing ι →+* MRing ι') P)`.

Conclude with `(Ideal.map_comap_of_surjective (E : MRing ι →+* MRing ι') E.surjective P).symm`.
-/
theorem isArithVar_comap_rename_sigma (e : ∀ k, ι k ≃ ι' k) {P : Ideal (MRing ι')} {d : ℕ}
    (hP : IsArithVar P d) :
    IsArithVar (P.comap (rename (Equiv.sigmaCongrRight e) : MRing ι →ₐ[ℤ] MRing ι')) d := by
  obtain ⟨hne, ⟨hprime, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩ := hP
  let E : MRing ι ≃+* MRing ι' := (renameEquiv ℤ (Equiv.sigmaCongrRight e)).toRingEquiv
  have hQ : P.comap (rename (Equiv.sigmaCongrRight e) : MRing ι →ₐ[ℤ] MRing ι') = P.map E.symm := by
    rw [Ideal.map_symm]
    rfl
  have hEs : ∀ g, E.symm g = rename (Equiv.sigmaCongrRight fun k => (e k).symm) g := by
    intro g
    show (renameEquiv ℤ (Equiv.sigmaCongrRight e)).symm g = _
    rw [renameEquiv_symm, Equiv.sigmaCongrRight_symm]
    rfl
  refine ⟨hne, ⟨?_, ⟨E.symm '' S, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · exact Ideal.comap_isPrime _ _
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨a, ha⟩ := hS g hg
    exact ⟨a, by rw [hEs]; exact isMultiHomog_rename_sigma (fun k => (e k).symm) ha⟩
  · rw [hQ, hPS, Ideal.map_span]
  · intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨(e k).symm i, fun hj => hi ?_⟩
    rw [Ideal.mem_comap] at hj
    simpa using hj
  · have h : Ideal.comap (C : ℤ →+* MRing ι)
        (P.comap (rename (Equiv.sigmaCongrRight e) : MRing ι →ₐ[ℤ] MRing ι')) =
        Ideal.comap (C : ℤ →+* MRing ι') P := by
      ext x
      simp only [Ideal.mem_comap, rename_C]
    unfold IsHorizontal
    rw [h]
    exact hhor
  · rw [← hdim]
    refine ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ P E ?_)
    show P = Ideal.map (E : MRing ι →+* MRing ι') (Ideal.comap (E : MRing ι →+* MRing ι') P)
    exact (Ideal.map_comap_of_surjective (E : MRing ι →+* MRing ι') E.surjective P).symm

end Rename

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)

def setIncrEquiv (q : FlBlock Ψ N) : IndefiniteRowSideFullHecke.LowerBoundFree.Nine.FlZBlk Ψ N q ≃ FlIdx Ψ N q where
  toFun S := ⟨S.1.orderEmbOfFin S.2, (S.1.orderEmbOfFin S.2).strictMono⟩
  invFun A := ⟨Finset.univ.image A.1, by rw [Finset.card_image_of_injective _ A.2.injective, Finset.card_fin]⟩
  left_inv S := by
    apply Subtype.ext
    simp only
    exact Finset.image_orderEmbOfFin_univ S.1 S.2
  right_inv A := by
    apply Subtype.ext
    exact (Finset.orderEmbOfFin_unique _ (fun x => Finset.mem_image_of_mem _ (Finset.mem_univ x)) A.2).symm

omit [Fintype Ψ] [DecidableEq Ψ] in

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem flZIncr_eq : flZIncr Ψ N = Equiv.sigmaCongrRight (setIncrEquiv Ψ N) := rfl

omit [Fintype Ψ] [DecidableEq Ψ] in

/- English proof (translation)
Rewrite using `[flZIncr_eq]`. Use `⟨Function.injective_id, (Equiv.sigmaCongrRight _).injective, fun _ => rfl, fun q _ => ?_⟩` and prove the remaining obligations. Conclude with `(Equiv.sigmaCongrRight (setIncrEquiv Ψ N)).surjective q`.
-/
theorem flZIncr_isBlockMap : IsBlockMap id (flZIncr Ψ N) := by
  rw [flZIncr_eq]
  refine ⟨Function.injective_id, (Equiv.sigmaCongrRight _).injective, fun _ => rfl, fun q _ => ?_⟩
  exact (Equiv.sigmaCongrRight (setIncrEquiv Ψ N)).surjective q

end FlZArithVar

/- English proof (translation)
Introduce `Ψ _ _ _ N hN`. Establish `hA` using `FlagArithVar.proof Ψ N hN`. Establish `hI : IndefiniteRowSideFullHecke.LowerBoundFree.Nine.FlZIdeal Ψ N = imageZ (flZIncr Ψ N) (PFl Ψ N)`. Rewrite using `[h Ψ N, PFl]`. Conclude with `GroundTheory.Heights₂.Heights.Inter.BlockRatioAlgebraic.mCoordIdeal_comp_v (FlZArithVar.flZIncr_isBlockMap Ψ N) (yFl Ψ N)`.

Rewrite using `[hI, imageZ, FlZArithVar.flZIncr_eq]`. Conclude with `FlZArithVar.isArithVar_comap_rename_sigma (FlZArithVar.setIncrEquiv Ψ N) hA`.
-/
theorem FlZArithVar.proof (h : FlZIdealEqCoord.Statement) : FlZArithVar.Statement := by
  intro Ψ _ _ _ N hN
  have hA := FlagArithVar.proof Ψ N hN
  have hI : IndefiniteRowSideFullHecke.LowerBoundFree.Nine.FlZIdeal Ψ N = imageZ (flZIncr Ψ N) (PFl Ψ N) := by
    rw [h Ψ N, PFl]
    exact GroundTheory.Heights₂.Heights.Inter.BlockRatioAlgebraic.mCoordIdeal_comp_v
      (FlZArithVar.flZIncr_isBlockMap Ψ N) (yFl Ψ N)
  rw [hI, imageZ, FlZArithVar.flZIncr_eq]
  exact FlZArithVar.isArithVar_comap_rename_sigma (FlZArithVar.setIncrEquiv Ψ N) hA

end GroundTheory.Heights₂.Heights.LowerBoundFree
