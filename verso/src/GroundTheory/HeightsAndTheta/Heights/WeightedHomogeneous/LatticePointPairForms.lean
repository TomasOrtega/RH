import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.POneBlockStandard
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.LineDegreeBundleStatement
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open NumberField Matrix TensorProduct ComplexAt
open scoped ComplexOrder

noncomputable section

variable {K : Type} [Field K] [NumberField K]

def stdLatticeWith (K : Type) [Field K] [NumberField K] (i : ℕ) (H : (K →+* ℂ) → Matrix (Fin i) (Fin i) ℂ)
    (hH : ∀ σ, (H σ).PosDef) (hc : ∀ σ, H (ComplexEmbedding.conjugate σ) = (H σ).map (starRingEnd ℂ)) :
    HermLattice K i where
  lattice := (HermLattice.standard K i).lattice
  fg := (HermLattice.standard K i).fg
  span_eq := (HermLattice.standard K i).span_eq
  metric := H
  posDef := hH
  conj := hc

def pairForms {d i N : ℕ} (om : Module.Basis (Fin d) ℤ (𝓞 K)) (e : Fin d × Fin i ≃ Fin (N + 1)) :
    Fin (N + 1) → Fin i → K :=
  fun b ↦ Pi.single (e.symm b).2 (om (e.symm b).1 : K)

omit [NumberField K] in

/- English proof (translation)
Use function extensionality and compare the values at `_ t`. Simplify using `only [latticePoint, pairForms]`. Rewrite using `[Finset.sum_eq_single (e.symm t).2 (fun j _ hj ↦ by simp [hj]) (by simp)]`. Simplify using the standard rewrite rules.
-/
theorem latticePoint_pairForms {R : Type*} [CommRing R] {d i N : ℕ} (om : Module.Basis (Fin d) ℤ (𝓞 K))
    (e : Fin d × Fin i ≃ Fin (N + 1)) (σ : K →+* R) (w : Fin i → R) :
    latticePoint (pairForms om e) σ w = fun _ t ↦ σ (om (e.symm t).1 : K) * w (e.symm t).2 := by
  funext _ t
  simp only [latticePoint, pairForms]
  rw [Finset.sum_eq_single (e.symm t).2 (fun j _ hj ↦ by simp [hj]) (by simp)]
  simp

/- English proof (translation)
Take `⟨h, -, -⟩` from `GroundTheory.Heights₂.Heights.OneBlockStandard.proof K e' r om`. Set `g : Fin (N + 1) ≃ Fin (oneBlockSize e' r + 1)` to `e.symm.trans (oneBlockIndex e' r).symm`. Establish `hφ : pairForms om e = oneBlockForms om ∘ g`. Use function extensionality and compare the values at `b`. Simplify using `[pairForms, oneBlockForms, g]`.

Rewrite using `[hφ]`. Conclude with `⟨h.independent.comp g g.injective, by rw [g.surjective.range_comp]; exact h.span_eq⟩`.
-/
theorem isDualBasis_pairForms {e' r N : ℕ} (om : Module.Basis (Fin (e' + 1)) ℤ (𝓞 K))
    (e : Fin (e' + 1) × Fin (r + 1) ≃ Fin (N + 1)) :
    IsDualBasis (HermLattice.standard K (r + 1)).lattice (pairForms om e) := by
  obtain ⟨h, -, -⟩ := GroundTheory.Heights₂.Heights.OneBlockStandard.proof K e' r om
  let g : Fin (N + 1) ≃ Fin (oneBlockSize e' r + 1) := e.symm.trans (oneBlockIndex e' r).symm
  have hφ : pairForms om e = oneBlockForms om ∘ g := by
    funext b
    simp [pairForms, oneBlockForms, g]
  rw [hφ]
  exact ⟨h.independent.comp g g.injective, by rw [g.surjective.range_comp]; exact h.span_eq⟩

/- English proof (translation)
Introduce `hA K _ _ d om i N e H hH hc A hdeg hmet K' _ _ _ E φ hE ψ v hv`. Take `_ | r` from `i`. Conclude with `absurd (funext fun j ↦ j.elim0) hv`. Take `_ | e'` from `d`. Conclude with `absurd (om.repr.injective (Subsingleton.elim _ _) : (1 : 𝓞 K) = 0) one_ne_zero`.

Set `F` to `stdLatticeWith K (r + 1) H hH hc`. Establish `hv' : (fun j ↦ (v j : K')) ≠ 0` using `fun h ↦ hv (funext fun j ↦ by`. Simplify using `using congrFun h j)`. Establish `h` using `(hA K r N F (pairForms om e) (isDualBasis_pairForms om e)).2 A (funext hdeg) (fun σ w hw ↦ by rw [latticePoint_pairForms]; exact hmet σ w hw) K' (fun j ↦ (v j : K')) hv' ψ`. Rewrite `h` using `[latticePoint_pairForms]`.

Rewrite using `[hL K (r + 1) F rfl K' E φ hE v hv]`. Establish `hpt : (fun (_ : Unit) (t : Fin (N + 1)) ↦ (ψ.comp (algebraMap K K')) (om (e.symm t).1 : K) * ψ (v (e.symm t).2 : K')) = fun _ t ↦ ψ (algebraMap K K' (om (e.symm t).1 : K) * (v (e.symm t).2 : K'))`. Use function extensionality and compare the values at `_ t`. Simplify using the standard rewrite rules. Rewrite `h` using `[hpt]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem PointHeightDegree.forward (hL : LineDegreeBundle.Statement) :
    GroundTheory.Heights₂.Heights.PointHeightDegree.Statement → PointHeightDegree.Statement := by
  intro hA K _ _ d om i N e H hH hc A hdeg hmet K' _ _ _ E φ hE ψ v hv
  obtain _ | r := i
  · exact absurd (funext fun j ↦ j.elim0) hv
  obtain _ | e' := d
  · exact absurd (om.repr.injective (Subsingleton.elim _ _) : (1 : 𝓞 K) = 0) one_ne_zero
  let F := stdLatticeWith K (r + 1) H hH hc
  have hv' : (fun j ↦ (v j : K')) ≠ 0 := fun h ↦ hv (funext fun j ↦ by
    simpa using congrFun h j)
  have h := (hA K r N F (pairForms om e) (isDualBasis_pairForms om e)).2 A (funext hdeg)
    (fun σ w hw ↦ by rw [latticePoint_pairForms]; exact hmet σ w hw) K' (fun j ↦ (v j : K')) hv' ψ
  rw [latticePoint_pairForms] at h
  rw [hL K (r + 1) F rfl K' E φ hE v hv]
  have hpt : (fun (_ : Unit) (t : Fin (N + 1)) ↦ (ψ.comp (algebraMap K K')) (om (e.symm t).1 : K) *
      ψ (v (e.symm t).2 : K')) =
      fun _ t ↦ ψ (algebraMap K K' (om (e.symm t).1 : K) * (v (e.symm t).2 : K')) := by
    funext _ t
    simp
  rw [hpt] at h
  linarith

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
