import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.CuspEmbP
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOrderedFormSnoc

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc GlobalTheory.CompanionTheory.ExhGood

namespace CompanionTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Take `⟨f, hf⟩` from `hf`. Establish `hn'` using `hn`. Take `⟨h, z, hz, ⟨Δ, hΔ, hzL⟩, -⟩` from `hn'`. Set `w : Fin (h + 1) → IrrGL k` to `Fin.snoc (α := fun _ => IrrGL k) z (y 0)`. Establish `hwL : LFactors (𝔫 + {s}) w`.

Use `⟨_, isOrderedForm_snoc hΔ s hp, fun i => ?_⟩` and prove the remaining obligations. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last`. Establish `e : w (Fin.last h) = y 0` using `Fin.snoc_last (α := fun _ => IrrGL k) _ _`. Rewrite using `[e, Fin.snoc_last]`.

Conclude with `hs`. Consider the case `cast i`. Establish `e : w i.castSucc = z i` using `Fin.snoc_castSucc (α := fun _ => IrrGL k) _ _ _`. Rewrite using `[e, Fin.snoc_castSucc]`. Conclude with `hzL i`.

Establish `hwd : ∑ a, (w a).1 = x.1`. Rewrite using `[Fin.sum_univ_castSucc, ← hd, Fin.sum_univ_two, add_comm, ← hz]`. Simplify using `[w]`. Establish `hwr : ∑ a, (w (Fin.rev a)).1 = x.1` using `(Equiv.sum_comp Fin.revPerm fun a => (w a).1).trans hwd`. Establish `hzr : ∑ a, (z (Fin.rev a)).1 = (y 1).1` using `(Equiv.sum_comp Fin.revPerm fun a => (z a).1).trans hz`.

Take `⟨π, hπ⟩` from `HS k (𝔫 + {s}) (h + 1) x.1 w hwd hwL`. Establish `hπL : IsL (𝔫 + {s}) π.ρ` using `⟨_, w, hwd, hwL, hπ⟩`. Establish `hsoc` using `HL (𝔫 + {s}) (h + 1) x.1 w hwr hwL π.ρ hπL`. Establish `hsoc₁` using `HL 𝔫 h (y 1).1 z hzr ⟨Δ, hΔ, hzL⟩ (y 1).rep hn`. Take `⟨-, g, hg, -⟩` from `hsoc₁`.

Take `⟨F, hF⟩` from `embed_family y (w ∘ Fin.rev) (z ∘ Fin.rev) (by simp [w, Function.comp]) (fun i => by simp [w, Function.comp, Fin.rev_succ]) hd hwr hzr g hg`. Take `⟨e⟩` from `hsoc.equiv_of_embeds x.2.rep.irr ⟨F.comp f, hF.comp hf⟩`. Conclude with `hπL.of_equiv e.symm`.
-/
theorem isL_add_segment_of_injective_of_not_precedes [CharZero k] (HS : GlobalTheory.Published.StandardCosocleGL) (HL : LSocleGL k) (x : IrrGL k)
    (y : Fin 2 → IrrGL k) (hd : ∑ a, (y a).1 = x.1) (s : Segment k) (𝔫 : Multiset (Segment k))
    (hs : IsLSeg s (y 0).rep) (hn : IsL 𝔫 (y 1).rep)
    (hf : ∃ f : x.rep.IntertwiningMap (prodIrr y hd), Function.Injective f)
    (hp : ∀ Δ ∈ 𝔫, ¬ Δ.Precedes s) :
    IsL (𝔫 + {s}) x.rep := by
  obtain ⟨f, hf⟩ := hf
  have hn' := hn
  obtain ⟨h, z, hz, ⟨Δ, hΔ, hzL⟩, -⟩ := hn'
  let w : Fin (h + 1) → IrrGL k := Fin.snoc (α := fun _ => IrrGL k) z (y 0)
  have hwL : LFactors (𝔫 + {s}) w := by
    refine ⟨_, isOrderedForm_snoc hΔ s hp, fun i => ?_⟩
    induction i using Fin.lastCases with
    | last =>
      have e : w (Fin.last h) = y 0 := Fin.snoc_last (α := fun _ => IrrGL k) _ _
      rw [e, Fin.snoc_last]
      exact hs
    | cast i =>
      have e : w i.castSucc = z i := Fin.snoc_castSucc (α := fun _ => IrrGL k) _ _ _
      rw [e, Fin.snoc_castSucc]
      exact hzL i
  have hwd : ∑ a, (w a).1 = x.1 := by
    rw [Fin.sum_univ_castSucc, ← hd, Fin.sum_univ_two, add_comm, ← hz]
    simp [w]
  have hwr : ∑ a, (w (Fin.rev a)).1 = x.1 := (Equiv.sum_comp Fin.revPerm fun a => (w a).1).trans hwd
  have hzr : ∑ a, (z (Fin.rev a)).1 = (y 1).1 := (Equiv.sum_comp Fin.revPerm fun a => (z a).1).trans hz
  obtain ⟨π, hπ⟩ := HS k (𝔫 + {s}) (h + 1) x.1 w hwd hwL
  have hπL : IsL (𝔫 + {s}) π.ρ := ⟨_, w, hwd, hwL, hπ⟩
  have hsoc := HL (𝔫 + {s}) (h + 1) x.1 w hwr hwL π.ρ hπL
  have hsoc₁ := HL 𝔫 h (y 1).1 z hzr ⟨Δ, hΔ, hzL⟩ (y 1).rep hn
  obtain ⟨-, g, hg, -⟩ := hsoc₁
  obtain ⟨F, hF⟩ := embed_family y (w ∘ Fin.rev) (z ∘ Fin.rev)
    (by simp [w, Function.comp]) (fun i => by simp [w, Function.comp, Fin.rev_succ]) hd hwr hzr g hg
  obtain ⟨e⟩ := hsoc.equiv_of_embeds x.2.rep.irr ⟨F.comp f, hF.comp hf⟩
  exact hπL.of_equiv e.symm

/- English proof (translation)
Introduce `x y hd Δ 𝔫 hs hn hf hp`. Conclude with `isL_add_segment_of_injective_of_not_precedes h1 h2 x y hd Δ 𝔫 hs hn hf hp`.
-/
theorem peelGoodP (h1 : GlobalTheory.Published.StandardCosocleGL) (h2 : Zc.LSocleGL k) (_h3 : RefineP k) [CharZero k] :
    Zc.PeelGoodP k := by
  intro x y hd Δ 𝔫 hs hn hf hp
  exact isL_add_segment_of_injective_of_not_precedes h1 h2 x y hd Δ 𝔫 hs hn hf hp

end CompanionTheory.Exh

end
