import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnipMir
open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier

namespace GlobalTheory.CompanionTheory.MirFourier

/- English proof (translation)
Establish `hmem : ∀ x : Multiplicative (Fin n → k), ∃ N : ℤ, x ∈ box k n N`. Introduce `x`. Use `choose m hm using fun i => exists_mem_valBall_neg_nat (K := k) (Multiplicative.toAdd x i)`. Use `⟨-((∑ i, m i : ℕ) : ℤ), (mem_box k).2 fun i => ?_⟩` and prove the remaining obligations. Establish `h1` using `hm i`.

Establish `hle : m i ≤ ∑ j, m j` using `Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) (Finset.mem_univ i)`. Express the relevant statement in the definitionally equal form `normalizedValuation k _ ≤ WithZero.exp (-(-((m i : ℕ) : ℤ))) at h1`. Express the relevant statement in the definitionally equal form `normalizedValuation k _ ≤ WithZero.exp (-(-((∑ j, m j : ℕ) : ℤ)))`. Use `h1.trans (WithZero.exp_le_exp.2 ?_)` and prove the remaining obligations. Simplify using `only [neg_neg]`.

Conclude with `hle` after adjusting the coercions. Unfold `GlobalTheory.PRep.twKer at hv ⊢`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨g, u, rfl⟩` from `hx`.

Take `⟨N, hN⟩` from `hmem g.1`. Conclude with `⟨N, fun j' hj' => Submodule.subset_span ⟨⟨g.1, box_antitone k n hj' hN⟩, u, rfl⟩⟩`. Consider the case `zero => exact ⟨0, fun j' _ => Submodule.zero_mem _⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha⟩` from `hx`.

Take `⟨b, hb⟩` from `hy`. Conclude with `⟨min a b, fun j' hj' => Submodule.add_mem _ (ha j' (hj'.trans (min_le_left _ _))) (hb j' (hj'.trans (min_le_right _ _)))⟩`. Consider the case `smul c x _ hx`. Take `⟨a, ha⟩` from `hx`. Conclude with `⟨a, fun j' hj' => Submodule.smul_mem _ c (ha j' hj')⟩`.
-/
theorem exists_mem_twKer_box (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Multiplicative (Fin n → k)) V)
    (χ : Multiplicative (Fin n → k) →* ℂˣ) (v : V)
    (hv : v ∈ twKer ρ ⊤ (χ.comp (⊤ : Subgroup (Multiplicative (Fin n → k))).subtype)) :
    ∃ j : ℤ, ∀ j' ≤ j, v ∈ twKer ρ (box k n j') (χ.comp (box k n j').subtype) := by
  classical
  have hmem : ∀ x : Multiplicative (Fin n → k), ∃ N : ℤ, x ∈ box k n N := by
    intro x
    choose m hm using fun i => exists_mem_valBall_neg_nat (K := k) (Multiplicative.toAdd x i)
    refine ⟨-((∑ i, m i : ℕ) : ℤ), (mem_box k).2 fun i => ?_⟩
    have h1 := hm i
    have hle : m i ≤ ∑ j, m j := Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) (Finset.mem_univ i)
    change normalizedValuation k _ ≤ WithZero.exp (-(-((m i : ℕ) : ℤ))) at h1
    change normalizedValuation k _ ≤ WithZero.exp (-(-((∑ j, m j : ℕ) : ℤ)))
    refine h1.trans (WithZero.exp_le_exp.2 ?_)
    simp only [neg_neg]
    exact_mod_cast hle
  unfold GlobalTheory.PRep.twKer at hv ⊢
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, u, rfl⟩ := hx
    obtain ⟨N, hN⟩ := hmem g.1
    exact ⟨N, fun j' hj' => Submodule.subset_span ⟨⟨g.1, box_antitone k n hj' hN⟩, u, rfl⟩⟩
  | zero => exact ⟨0, fun j' _ => Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨min a b, fun j' hj' => Submodule.add_mem _ (ha j' (hj'.trans (min_le_left _ _)))
      (hb j' (hj'.trans (min_le_right _ _)))⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨a, fun j' hj' => Submodule.smul_mem _ c (ha j' hj')⟩

end GlobalTheory.CompanionTheory.MirFourier
