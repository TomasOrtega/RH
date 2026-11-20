import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.ConjPoint

/- English proof (translation)
Break down `h with h | h` into its components or cases. Conclude with `iff_of_true h.1 h.2`. Conclude with `iff_of_false h.1 h.2.1`.
-/
lemma IsConj.mem_lattice_iff {L L' : PeriodPair} {σ : ℂ ≃+* ℂ} {t t' : ℂ}
    (h : IsConj L L' σ t t') : t ∈ L.lattice ↔ t' ∈ L'.lattice := by
  rcases h with h | h
  · exact iff_of_true h.1 h.2
  · exact iff_of_false h.1 h.2.1

/- English proof (translation)
Introduce `L σ α S S' h₂ h₃ hα hS hS'`. Take `⟨s, -, hc⟩` from `exists_conjEquiv h₂ h₃`. Establish `hf : ∀ t : S, ∃ t' : S', IsConj L L σ (t : ℂ) (t' : ℂ)`. Introduce `t`. Take `⟨u, hu⟩` from `latticePoint_surjective L (s (latticePoint L t))`.

Establish `h` using `(hc _ _).2 hu.symm`. Take `⟨P, hP, hd⟩` from `hS'.2.2 u ((IsConj.mul h₂ h₃ hα h).mem_lattice_iff.1 (hS.1 t t.2).1) (fun hm ↦ (hS.1 t t.2).2 (h.mem_lattice_iff.2 hm))`. Conclude with `⟨⟨P, hP⟩, (hc _ _).2 (hu.symm.trans ((latticePoint_eq_iff L).2 hd))⟩`. Use `choose f hf using hf`. Use `⟨Equiv.ofBijective f ⟨fun a b hab ↦ ?_, fun t' ↦ ?_⟩, hf⟩` and prove the remaining obligations.

Establish `ha` using `(hc _ _).1 (hf a)`. Establish `hb` using `(hc _ _).1 (hf b)`. Rewrite `ha` using `[hab, ← hb]`. Conclude with `Subtype.ext (hS.2.1 _ a.2 _ b.2 ((latticePoint_eq_iff L).1 (s.injective ha)))`. Take `⟨Q, hQ⟩` from `s.surjective (latticePoint L t')`.

Take `⟨u, rfl⟩` from `latticePoint_surjective L Q`. Establish `h` using `(hc _ _).2 hQ`. Take `⟨P, hP, hd⟩` from `hS.2.2 u ((IsConj.mul h₂ h₃ hα h).mem_lattice_iff.2 (hS'.1 t' t'.2).1) (fun hm ↦ (hS'.1 t' t'.2).2 (h.mem_lattice_iff.1 hm))`. Use `⟨⟨P, hP⟩, Subtype.ext (hS'.2.1 _ (f _).2 _ t'.2 ((latticePoint_eq_iff L).1 ?_))⟩` and prove the remaining obligations. Rewrite using `[← (hc _ _).1 (hf ⟨P, hP⟩), ← hQ, (latticePoint_eq_iff L).2 hd]`.
-/
theorem exists_equiv_kerReps_isConj :
    ∀ (L : PeriodPair) (σ : ℂ ≃+* ℂ) (α : ℂ) (S S' : Finset ℂ), L.g₂ = σ L.g₂ → L.g₃ = σ L.g₃ →
      MulStable L α → IsKerReps L α S → IsKerReps L (σ α) S' →
      ∃ e : S ≃ S', ∀ t : S, GlobalTheory.ConjPoint.IsConj L L σ (t : ℂ) (e t : ℂ) := by
  intro L σ α S S' h₂ h₃ hα hS hS'
  obtain ⟨s, -, hc⟩ := exists_conjEquiv h₂ h₃
  have hf : ∀ t : S, ∃ t' : S', IsConj L L σ (t : ℂ) (t' : ℂ) := by
    intro t
    obtain ⟨u, hu⟩ := latticePoint_surjective L (s (latticePoint L t))
    have h := (hc _ _).2 hu.symm
    obtain ⟨P, hP, hd⟩ := hS'.2.2 u ((IsConj.mul h₂ h₃ hα h).mem_lattice_iff.1 (hS.1 t t.2).1)
      (fun hm ↦ (hS.1 t t.2).2 (h.mem_lattice_iff.2 hm))
    exact ⟨⟨P, hP⟩, (hc _ _).2 (hu.symm.trans ((latticePoint_eq_iff L).2 hd))⟩
  choose f hf using hf
  refine ⟨Equiv.ofBijective f ⟨fun a b hab ↦ ?_, fun t' ↦ ?_⟩, hf⟩
  · have ha := (hc _ _).1 (hf a)
    have hb := (hc _ _).1 (hf b)
    rw [hab, ← hb] at ha
    exact Subtype.ext (hS.2.1 _ a.2 _ b.2 ((latticePoint_eq_iff L).1 (s.injective ha)))
  · obtain ⟨Q, hQ⟩ := s.surjective (latticePoint L t')
    obtain ⟨u, rfl⟩ := latticePoint_surjective L Q
    have h := (hc _ _).2 hQ
    obtain ⟨P, hP, hd⟩ := hS.2.2 u ((IsConj.mul h₂ h₃ hα h).mem_lattice_iff.2 (hS'.1 t' t'.2).1)
      (fun hm ↦ (hS'.1 t' t'.2).2 (h.mem_lattice_iff.1 hm))
    refine ⟨⟨P, hP⟩, Subtype.ext (hS'.2.1 _ (f _).2 _ t'.2 ((latticePoint_eq_iff L).1 ?_))⟩
    rw [← (hc _ _).1 (hf ⟨P, hP⟩), ← hQ, (latticePoint_eq_iff L).2 hd]

end GlobalTheory.ConjPoint
