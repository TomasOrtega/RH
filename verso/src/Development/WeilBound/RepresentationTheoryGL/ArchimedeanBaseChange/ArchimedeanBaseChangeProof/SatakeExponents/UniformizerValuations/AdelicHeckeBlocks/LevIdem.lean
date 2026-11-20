import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LevIdem
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.IsCompactSub

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelH

/- English proof (translation)
Introduce `E _ _ _ n S d a ha hS hd hPS`. Take `⟨⟨G₁, eG₁⟩, ⟨G₂, eG₂⟩, ⟨o₁, c₁⟩, ⟨o₂, c₂⟩, hpi, hν⟩` from `Lev6.main d hintProd h3 a ha hS hd hPS`. Establish `eL : levSet S d a = Lev6.lvS d S a` using `Set.ext fun h => (Lev6.mem_lvS d S a h).symm`. Establish `e₁ : lev₁ S d a = G₁`. Establish `: lev₁ S d a = Subgroup.closure (G₁ : Set (GL (Fin a) (Af E)))` using `by rw [eG₁, ← eL]; rfl`.

Rewrite using `[this, Subgroup.closure_eq]`. Establish `e₂ : lev₂ S d a = G₂`. Establish `: lev₂ S d a = Subgroup.closure (G₂ : Set (GL (Fin (n - a)) (Af E)))` using `by rw [eG₂, ← eL]; rfl`. Rewrite using `[this, Subgroup.closure_eq]`. Establish `eP : ((G₁.prod G₂ : Subgroup (Hf E a (n - a))) : Set (Hf E a (n - a))) = Lev6.lvS d S a`.

Use extensionality with `⟨g, h⟩`. Use `show g ∈ (G₁ : Set (GL (Fin a) (Af E))) ∧ h ∈ (G₂ : Set (GL (Fin (n - a)) (Af E))) ↔ _`. Rewrite using `[eG₁, eG₂]`. Conclude with `(hpi g h).symm`. Establish `hm : ∀ h : Hf E a (n - a), h ∈ G₁.prod G₂ ↔ h ∈ Lev6.lvS d S a` using `fun h => by`.

Rewrite using `[← SetLike.mem_coe, eP]`. Rewrite using `[e₁, e₂, eP, eL]`. Use `⟨⟨by rw [eG₁]; exact o₁, by rw [eG₁]; exact c₁⟩, ⟨by rw [eG₂]; exact o₂, by rw [eG₂]; exact c₂⟩, rfl, fun ν hνH => ?_⟩` and prove the remaining obligations. Take `⟨hne, hf⟩` from `hν ν hνH`. Use `⟨((ν.real (Lev6.lvS d S a) : ℝ) : ℂ)⁻¹, inv_mul_cancel₀ hne, fun x y h => ?_⟩` and prove the remaining obligations.

Rewrite using `[hf x y h]`. Distinguish the cases in `hc : x = y ∧ h ∈ Lev6.lvS d S a`. Rewrite using `[if_pos hc, if_pos ⟨hc.1, (hm h).2 hc.2⟩]`. Rewrite using `[if_neg hc, if_neg (fun h' => hc ⟨h'.1, (hm h).1 h'.2⟩)]`.
-/
theorem levIdem (h3 : Slots) : LevIdem := by
  intro E _ _ _ n S d a ha hS hd hPS
  obtain ⟨⟨G₁, eG₁⟩, ⟨G₂, eG₂⟩, ⟨o₁, c₁⟩, ⟨o₂, c₂⟩, hpi, hν⟩ := Lev6.main d hintProd h3 a ha hS hd hPS
  have eL : levSet S d a = Lev6.lvS d S a := Set.ext fun h => (Lev6.mem_lvS d S a h).symm
  have e₁ : lev₁ S d a = G₁ := by
    have : lev₁ S d a = Subgroup.closure (G₁ : Set (GL (Fin a) (Af E))) := by rw [eG₁, ← eL]; rfl
    rw [this, Subgroup.closure_eq]
  have e₂ : lev₂ S d a = G₂ := by
    have : lev₂ S d a = Subgroup.closure (G₂ : Set (GL (Fin (n - a)) (Af E))) := by rw [eG₂, ← eL]; rfl
    rw [this, Subgroup.closure_eq]
  have eP : ((G₁.prod G₂ : Subgroup (Hf E a (n - a))) : Set (Hf E a (n - a))) = Lev6.lvS d S a := by
    ext ⟨g, h⟩
    show g ∈ (G₁ : Set (GL (Fin a) (Af E))) ∧ h ∈ (G₂ : Set (GL (Fin (n - a)) (Af E))) ↔ _
    rw [eG₁, eG₂]
    exact (hpi g h).symm
  have hm : ∀ h : Hf E a (n - a), h ∈ G₁.prod G₂ ↔ h ∈ Lev6.lvS d S a := fun h => by
    rw [← SetLike.mem_coe, eP]
  rw [e₁, e₂, eP, eL]
  refine ⟨⟨by rw [eG₁]; exact o₁, by rw [eG₁]; exact c₁⟩, ⟨by rw [eG₂]; exact o₂, by rw [eG₂]; exact c₂⟩, rfl,
    fun ν hνH => ?_⟩
  obtain ⟨hne, hf⟩ := hν ν hνH
  refine ⟨((ν.real (Lev6.lvS d S a) : ℝ) : ℂ)⁻¹, inv_mul_cancel₀ hne, fun x y h => ?_⟩
  rw [hf x y h]
  by_cases hc : x = y ∧ h ∈ Lev6.lvS d S a
  · rw [if_pos hc, if_pos ⟨hc.1, (hm h).2 hc.2⟩]
  · rw [if_neg hc, if_neg (fun h' => hc ⟨h'.1, (hm h).1 h'.2⟩)]

end PositivityTheory.Rg.BcB.F

end
