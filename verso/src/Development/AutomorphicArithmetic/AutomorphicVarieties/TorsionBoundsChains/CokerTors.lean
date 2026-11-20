import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.MaxIndep
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FullEnum
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.IndexLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.TorsSat
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Transport

open CategoryTheory UpperTheory.V.KH

/- English proof (translation)
Introduce `ι A b L hι hb hL`. Take `⟨hfin, hA⟩` from `hι`. Use `haveI : IsAddTorsionFree (ι →₀ ℤ) := Function.Injective.isAddTorsionFree (Finsupp.coeFnAddHom : (ι →₀ ℤ) →+ (ι → ℤ)) DFunLike.coe_injective`. Take `⟨b₀, -, hb₀L, hb₀i, hb₀⟩` from `maxIndep (ι →₀ ℤ) ∅ L (Set.empty_subset _) (linearIndepOn_empty _ _)`. Take `⟨b₁, h01, hb₁s, hb₁i, hb₁⟩` from `maxIndep (ι →₀ ℤ) b₀ (b₀ ∪ Set.range fun k : ι => Finsupp.single k (1 : ℤ)) Set.subset_union_left hb₀i`.

Take `⟨v, hv, hvr⟩` from `fullEnum ι b₁ hb₁i fun k => hb₁ _ (Or.inr ⟨k, rfl⟩)`. Establish `hshort : ∀ i, l1 (v i) ≤ b`. Introduce `i`. Establish `hi : v i ∈ b₁` using `hvr ▸ Set.mem_range_self i`. Break down `hb₁s hi with h | ⟨k, hk⟩` into its components or cases.

Conclude with `hL _ (hb₀L h)`. Rewrite using `[← hk]`. Unfold `l1`. Rewrite using `[Finsupp.sum_single_index (by simp)]`. Simplify using `using hb`.

Establish `hc` using `indexLe ι v b hv hshort`. Establish `ht` using `torsSat (ι →₀ ℤ) ι L v _ hv (fun x hx => by`. Take `⟨n, hn, hnx⟩` from `hb₀ x hx`. Use `⟨n, hn, Submodule.span_mono ?_ hnx⟩` and prove the remaining obligations. Rewrite using `[hvr]`.

Conclude with `Set.subset_inter h01 hb₀L) hc`. Conclude with `⟨ht.1, ht.2.trans (Nat.pow_le_pow_right hb hA)⟩`.
-/
theorem UpperTheory.V.KH.cokerTors :
    ∀ (ι : Type) (A b : ℕ) (L : Set (ι →₀ ℤ)), CardLe ι A → 1 ≤ b → (∀ x ∈ L, l1 x ≤ b) →
      TorsLe ((ι →₀ ℤ) ⧸ Submodule.span ℤ L) (b ^ A) := by
  intro ι A b L hι hb hL
  obtain ⟨hfin, hA⟩ := hι
  haveI : IsAddTorsionFree (ι →₀ ℤ) :=
    Function.Injective.isAddTorsionFree (Finsupp.coeFnAddHom : (ι →₀ ℤ) →+ (ι → ℤ))
      DFunLike.coe_injective
  obtain ⟨b₀, -, hb₀L, hb₀i, hb₀⟩ := maxIndep (ι →₀ ℤ) ∅ L (Set.empty_subset _)
    (linearIndepOn_empty _ _)
  obtain ⟨b₁, h01, hb₁s, hb₁i, hb₁⟩ := maxIndep (ι →₀ ℤ) b₀
    (b₀ ∪ Set.range fun k : ι => Finsupp.single k (1 : ℤ)) Set.subset_union_left hb₀i
  obtain ⟨v, hv, hvr⟩ := fullEnum ι b₁ hb₁i fun k => hb₁ _ (Or.inr ⟨k, rfl⟩)
  have hshort : ∀ i, l1 (v i) ≤ b := by
    intro i
    have hi : v i ∈ b₁ := hvr ▸ Set.mem_range_self i
    rcases hb₁s hi with h | ⟨k, hk⟩
    · exact hL _ (hb₀L h)
    · rw [← hk]
      unfold l1
      rw [Finsupp.sum_single_index (by simp)]
      simpa using hb
  have hc := indexLe ι v b hv hshort
  have ht := torsSat (ι →₀ ℤ) ι L v _ hv (fun x hx => by
    obtain ⟨n, hn, hnx⟩ := hb₀ x hx
    refine ⟨n, hn, Submodule.span_mono ?_ hnx⟩
    rw [hvr]
    exact Set.subset_inter h01 hb₀L) hc
  exact ⟨ht.1, ht.2.trans (Nat.pow_le_pow_right hb hA)⟩
