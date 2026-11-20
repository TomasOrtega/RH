import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.JuxtWords
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.JuxtShl
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.JuxtSwap
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.JuxtUniq
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.JuxtDec

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace CompanionTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Introduce `σ b Δ hb hσ`. Express the relevant statement in the definitionally equal form `SubqL σ [nxt Δ, b] at hσ`. Express the relevant statement in the definitionally equal form `IsLSeg (up Δ) σ.rep ∨ EmbL σ [b, nxt Δ]`. Take `⟨l, hl, he⟩` from `hC σ`. Take `⟨P, Q, h1, rfl⟩` from `words_of_subq hA hW σ b Δ hb hσ l hl he`.

Break down `eq_or_ne P [] with rfl | hP` into its components or cases. Use `left`. Use `hD (up Δ) σ ?_` and prove the remaining obligations. Rewrite using `[decW_up]`. Simplify using `only [List.nil_append] at h1 he`.

Rewrite using `[h1]`. Conclude with `he`. Use `right`. Establish `h2` using `emb_move_end hA hS σ Δ P Q h1 hP he`. Take `⟨τ, -, h3⟩` from `hM σ [] (decW Δ) [nxt Δ] (by simpa using h2)`.

Take `⟨u, hu, h4⟩` from `hC τ`. Establish `h5 : EmbL σ (u ++ [nxt Δ])` using `by simpa using hR σ τ [] u [nxt Δ] h4 h3`. Take `⟨P', Q', h6, h7⟩` from `words_of_subq hA hW σ b Δ hb hσ (u ++ [nxt Δ]) (by`. Introduce `ρ hρ`. Break down `List.mem_append.1 hρ with h | h` into its components or cases.

Conclude with `hu ρ h`. Rewrite using `[List.mem_singleton.1 h]`. Conclude with `Δ.isCusp_first.nu _) h5`. Establish `h8` using `eq_decW_of_append hA Δ u P' Q' h6 h7`. Substitute `h8` using the available equality.

Establish `h9` using `eq_of_isLSeg Δ τ b (hD Δ τ h4) hb`. Substitute `h9` using the available equality. Simplify using `using h3`.
-/
theorem juxtP (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hM : MidP k) (hR : RefineP k) (hS : SwapP k)
    (hC : CuspEmbP k) (hW : ShlP k) (hD : DecLP k) : JuxtP k := by
  intro σ b Δ hb hσ
  change SubqL σ [nxt Δ, b] at hσ
  change IsLSeg (up Δ) σ.rep ∨ EmbL σ [b, nxt Δ]
  obtain ⟨l, hl, he⟩ := hC σ
  obtain ⟨P, Q, h1, rfl⟩ := words_of_subq hA hW σ b Δ hb hσ l hl he
  rcases eq_or_ne P [] with rfl | hP
  · left
    refine hD (up Δ) σ ?_
    rw [decW_up]
    simp only [List.nil_append] at h1 he
    rw [h1]
    exact he
  · right
    have h2 := emb_move_end hA hS σ Δ P Q h1 hP he
    obtain ⟨τ, -, h3⟩ := hM σ [] (decW Δ) [nxt Δ] (by simpa using h2)
    obtain ⟨u, hu, h4⟩ := hC τ
    have h5 : EmbL σ (u ++ [nxt Δ]) := by simpa using hR σ τ [] u [nxt Δ] h4 h3
    obtain ⟨P', Q', h6, h7⟩ := words_of_subq hA hW σ b Δ hb hσ (u ++ [nxt Δ])
      (by
        intro ρ hρ
        rcases List.mem_append.1 hρ with h | h
        · exact hu ρ h
        · rw [List.mem_singleton.1 h]; exact Δ.isCusp_first.nu _) h5
    have h8 := eq_decW_of_append hA Δ u P' Q' h6 h7
    subst h8
    have h9 := eq_of_isLSeg Δ τ b (hD Δ τ h4) hb
    subst h9
    simpa using h3

/- English proof (translation)
The claim follows from `juxtP hA hM hR hS hC hW (decLP hF)`.
-/
theorem juxtP_of_fineUniq (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hM : MidP k) (hR : RefineP k) (hS : SwapP k)
    (hC : CuspEmbP k) (hW : ShlP k) (hF : FineUniqP k) : JuxtP k :=
  juxtP hA hM hR hS hC hW (decLP hF)

end CompanionTheory.Exh

end
