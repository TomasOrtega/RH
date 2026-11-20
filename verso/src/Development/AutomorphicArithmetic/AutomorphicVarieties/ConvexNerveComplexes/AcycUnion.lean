import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveFaceClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.AltDoubleSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.BdMem

open Set UpperTheory.V.ConeExtensionAcyclic

/- English proof (translation)
Introduce `I A B hA hB hAc hBc hABc`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `c hc`. Rewrite `hc` using `[Finsupp.supported_union, Submodule.mem_sup]`. Take `⟨y, hy, z, hz, rfl⟩` from `hc`.

Take `⟨f, hf, rfl⟩` from `hAc.1 y hy`. Take `⟨g, hg, rfl⟩` from `hBc.1 z hz`. Use `⟨f + g, ?_, map_add _ _ _⟩` and prove the remaining obligations. Rewrite using `[Finsupp.supported_union]`. Conclude with `Submodule.add_mem_sup hf hg`.

Introduce `n c hc hcyc`. Rewrite `hc` using `[Finsupp.supported_union, Submodule.mem_sup]`. Take `⟨y, hy, z, hz, rfl⟩` from `hc`. Rewrite `hcyc` using `[map_add]`. Establish `hdA : bd I n y ∈ Finsupp.supported ℤ ℤ (A n)` using `bd_mem hA n y hy`.

Establish `hdB : bd I n y ∈ Finsupp.supported ℤ ℤ (B n)`. Rewrite using `[eq_neg_of_add_eq_zero_left hcyc]`. Conclude with `Submodule.neg_mem _ (bd_mem hB n z hz)`. Establish `hd : bd I n y ∈ Finsupp.supported ℤ ℤ (A n ∩ B n)`. Rewrite using `[Finsupp.supported_inter]`.

Conclude with `⟨hdA, hdB⟩`. Choose the witnesses or unpack the hypotheses as in `⟨e, he, hee⟩ : ∃ e ∈ Finsupp.supported ℤ ℤ (A (n + 1) ∩ B (n + 1)), bd I n e = bd I n y := by`. Consider the cases of `n with`. Consider the case `zero => exact hABc.1 _ hd`. Consider the case `succ m => exact hABc.2 m _ hd (bd_bd I m y)`.

Rewrite `he` using `[Finsupp.supported_inter]`. Take `⟨f, hf, hfe⟩` from `hAc.2 n (y - e) (Submodule.sub_mem _ hy he.1) (by rw [map_sub, hee, sub_self])`. Take `⟨g, hg, hge⟩` from `hBc.2 n (z + e) (Submodule.add_mem _ hz he.2) (by rw [map_add, hee, add_comm]; exact hcyc)`. Use `⟨f + g, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Finsupp.supported_union]`.

Conclude with `Submodule.add_mem_sup hf hg`. Rewrite using `[map_add, hfe, hge]`. Normalize the expressions using the abelian group laws.
-/
theorem UpperTheory.V.ConeExtensionAcyclic.acyc_union :
    ∀ {I : Type} (A B : ∀ n, Set (Fin n → I)), FaceClosed A → FaceClosed B → Acyc A → Acyc B → Acyc (fun n => A n ∩ B n) → Acyc (fun n => A n ∪ B n) := by
  intro I A B hA hB hAc hBc hABc
  refine ⟨?_, ?_⟩
  · intro c hc
    rw [Finsupp.supported_union, Submodule.mem_sup] at hc
    obtain ⟨y, hy, z, hz, rfl⟩ := hc
    obtain ⟨f, hf, rfl⟩ := hAc.1 y hy
    obtain ⟨g, hg, rfl⟩ := hBc.1 z hz
    refine ⟨f + g, ?_, map_add _ _ _⟩
    rw [Finsupp.supported_union]
    exact Submodule.add_mem_sup hf hg
  · intro n c hc hcyc
    rw [Finsupp.supported_union, Submodule.mem_sup] at hc
    obtain ⟨y, hy, z, hz, rfl⟩ := hc
    rw [map_add] at hcyc
    have hdA : bd I n y ∈ Finsupp.supported ℤ ℤ (A n) := bd_mem hA n y hy
    have hdB : bd I n y ∈ Finsupp.supported ℤ ℤ (B n) := by
      rw [eq_neg_of_add_eq_zero_left hcyc]
      exact Submodule.neg_mem _ (bd_mem hB n z hz)
    have hd : bd I n y ∈ Finsupp.supported ℤ ℤ (A n ∩ B n) := by
      rw [Finsupp.supported_inter]
      exact ⟨hdA, hdB⟩
    obtain ⟨e, he, hee⟩ : ∃ e ∈ Finsupp.supported ℤ ℤ (A (n + 1) ∩ B (n + 1)), bd I n e = bd I n y := by
      cases n with
      | zero => exact hABc.1 _ hd
      | succ m => exact hABc.2 m _ hd (bd_bd I m y)
    rw [Finsupp.supported_inter] at he
    obtain ⟨f, hf, hfe⟩ := hAc.2 n (y - e) (Submodule.sub_mem _ hy he.1) (by rw [map_sub, hee, sub_self])
    obtain ⟨g, hg, hge⟩ := hBc.2 n (z + e) (Submodule.add_mem _ hz he.2) (by rw [map_add, hee, add_comm]; exact hcyc)
    refine ⟨f + g, ?_, ?_⟩
    · rw [Finsupp.supported_union]
      exact Submodule.add_mem_sup hf hg
    · rw [map_add, hfe, hge]
      abel
