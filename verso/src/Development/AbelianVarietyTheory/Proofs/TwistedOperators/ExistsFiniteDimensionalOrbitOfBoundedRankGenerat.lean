import Mathlib

namespace GlobalTheory

open Submodule

/- English proof (translation)
Introduce `V ι K _ _ U G P D m L T a hG hDL hGP hDP hmin hTG ha hTD f hf`. Take `⟨Q, hQ0, hQs⟩ : ∃ Q : ℕ → Submodule ℂ V, Q 0 = span ℂ G ∧ ∀ n, Q (n + 1) = Q n ⊔ span ℂ (⋃ u ∈ U, (D u) '' (Q n : Set V))` from `⟨fun n => Nat.rec (span ℂ G) (fun _ R => R ⊔ span ℂ (⋃ u ∈ U, (D u) '' (R : Set V))) n, rfl, fun _ => rfl⟩`. Establish `hmono : Monotone Q` using `monotone_nat_of_le_succ fun n => by`. Rewrite using `[hQs]`. Conclude with `le_sup_left`.

Establish `hDQ : ∀ n, ∀ u ∈ U, ∀ x ∈ Q n, D u x ∈ Q (n + 1)`. Introduce `n u hu x hx`. Rewrite using `[hQs]`. Conclude with `mem_sup_right (subset_span (Set.mem_iUnion₂.2 ⟨u, hu, x, hx, rfl⟩))`. Establish `hfin : ∀ n : ℕ, FiniteDimensional ℂ (Q n)`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => rw [hQ0]`. Conclude with `hG`. Consider the case `succ n ih`.

Rewrite using `[hQs]`. Establish `hle : span ℂ (⋃ u ∈ U, (D u) '' (Q n : Set V)) ≤ ⨆ i, (Q n).map (L i)`. Use `span_le.2 (Set.iUnion₂_subset fun u hu => ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Use `(span_le.2 ?_) (hDL u hu x)` and prove the remaining obligations.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `mem_iSup_of_mem i (mem_map_of_mem hx)`. Use `haveI : FiniteDimensional ℂ (span ℂ (⋃ u ∈ U, (D u) '' (Q n : Set V))) := Submodule.finiteDimensional_of_le hle`. Conclude with `Submodule.finiteDimensional_sup _ _`. Establish `hQP : ∀ n, Q n ≤ P`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => rw [hQ0]`. Conclude with `span_le.2 hGP`. Consider the case `succ n ih`.

Rewrite using `[hQs]`. Use `sup_le ih (span_le.2 (Set.iUnion₂_subset fun u hu => ?_))` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `hDP u hu y (ih hy)`. Establish `hT : ∀ n k, Q n ≤ (Q n).comap (T k)`.

Introduce `n k`. Proceed by induction on `n with`. Consider the case `zero => rw [hQ0]`. Conclude with `span_le.2 fun g hg => hTG k g hg`. Consider the case `succ n ih`.

Rewrite using `[hQs]`. Use `sup_le (ih.trans (comap_mono le_sup_left)) ?_` and prove the remaining obligations. Use `span_le.2 (Set.iUnion₂_subset fun u hu => ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Establish `hxP : x ∈ P` using `hQP n hx`.

Rewrite using `[SetLike.mem_coe, mem_comap, ← hQs, hTD k u hu x hxP]`. Conclude with `hDQ n (a k u) (ha k u hu) (T k x) (ih hx)`. Establish `hGN : G ⊆ (⨆ n, Q n : Submodule ℂ V)` using `fun g hg => mem_iSup_of_mem 0 (hQ0 ▸ subset_span hg)`. Establish `hDN : ∀ u ∈ U, ∀ x ∈ (⨆ n, Q n : Submodule ℂ V), D u x ∈ (⨆ n, Q n : Submodule ℂ V)`. Introduce `u hu x hx`.

Take `⟨n, hn⟩` from `(mem_iSup_of_directed Q hmono.directed_le).1 hx`. Conclude with `mem_iSup_of_mem (n + 1) (hDQ n u hu x hn)`. Take `⟨n, hn⟩` from `(mem_iSup_of_directed Q hmono.directed_le).1 (hmin _ hGN hDN hf)`. Conclude with `⟨Q n, hfin n, fun k => hT n k hn⟩`.
-/
theorem exists_finiteDimensional_orbit_of_generated :
    ∀ (V ι K : Type) [AddCommGroup V] [Module ℂ V] (U : Set ι) (G : Set V) (P : Submodule ℂ V) (D : ι → V →ₗ[ℂ] V)
    (m : ℕ) (L : Fin m → V →ₗ[ℂ] V) (T : K → V →ₗ[ℂ] V) (a : K → ι → ι),
    FiniteDimensional ℂ (Submodule.span ℂ G) →
    (∀ u ∈ U, ∀ f, D u f ∈ Submodule.span ℂ (Set.range fun i => L i f)) →
    G ⊆ P → (∀ u ∈ U, ∀ f ∈ P, D u f ∈ P) →
    (∀ N : Submodule ℂ V, G ⊆ N → (∀ u ∈ U, ∀ f ∈ N, D u f ∈ N) → P ≤ N) →
    (∀ k, ∀ g ∈ G, T k g ∈ Submodule.span ℂ G) → (∀ k, ∀ u ∈ U, a k u ∈ U) →
    (∀ k, ∀ u ∈ U, ∀ f ∈ P, T k (D u f) = D (a k u) (T k f)) →
    ∀ f ∈ P, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ ∀ k, T k f ∈ S := by
  intro V ι K _ _ U G P D m L T a hG hDL hGP hDP hmin hTG ha hTD f hf
  obtain ⟨Q, hQ0, hQs⟩ : ∃ Q : ℕ → Submodule ℂ V, Q 0 = span ℂ G ∧
      ∀ n, Q (n + 1) = Q n ⊔ span ℂ (⋃ u ∈ U, (D u) '' (Q n : Set V)) :=
    ⟨fun n => Nat.rec (span ℂ G) (fun _ R => R ⊔ span ℂ (⋃ u ∈ U, (D u) '' (R : Set V))) n,
      rfl, fun _ => rfl⟩
  have hmono : Monotone Q := monotone_nat_of_le_succ fun n => by
    rw [hQs]; exact le_sup_left
  have hDQ : ∀ n, ∀ u ∈ U, ∀ x ∈ Q n, D u x ∈ Q (n + 1) := by
    intro n u hu x hx
    rw [hQs]
    exact mem_sup_right (subset_span (Set.mem_iUnion₂.2 ⟨u, hu, x, hx, rfl⟩))
  have hfin : ∀ n : ℕ, FiniteDimensional ℂ (Q n) := by
    intro n
    induction n with
    | zero => rw [hQ0]; exact hG
    | succ n ih =>
      rw [hQs]
      have hle : span ℂ (⋃ u ∈ U, (D u) '' (Q n : Set V)) ≤ ⨆ i, (Q n).map (L i) := by
        refine span_le.2 (Set.iUnion₂_subset fun u hu => ?_)
        rintro _ ⟨x, hx, rfl⟩
        refine (span_le.2 ?_) (hDL u hu x)
        rintro _ ⟨i, rfl⟩
        exact mem_iSup_of_mem i (mem_map_of_mem hx)
      haveI : FiniteDimensional ℂ (span ℂ (⋃ u ∈ U, (D u) '' (Q n : Set V))) :=
        Submodule.finiteDimensional_of_le hle
      exact Submodule.finiteDimensional_sup _ _
  have hQP : ∀ n, Q n ≤ P := by
    intro n
    induction n with
    | zero => rw [hQ0]; exact span_le.2 hGP
    | succ n ih =>
      rw [hQs]
      refine sup_le ih (span_le.2 (Set.iUnion₂_subset fun u hu => ?_))
      rintro _ ⟨y, hy, rfl⟩
      exact hDP u hu y (ih hy)
  have hT : ∀ n k, Q n ≤ (Q n).comap (T k) := by
    intro n k
    induction n with
    | zero => rw [hQ0]; exact span_le.2 fun g hg => hTG k g hg
    | succ n ih =>
      rw [hQs]
      refine sup_le (ih.trans (comap_mono le_sup_left)) ?_
      refine span_le.2 (Set.iUnion₂_subset fun u hu => ?_)
      rintro _ ⟨x, hx, rfl⟩
      have hxP : x ∈ P := hQP n hx
      rw [SetLike.mem_coe, mem_comap, ← hQs, hTD k u hu x hxP]
      exact hDQ n (a k u) (ha k u hu) (T k x) (ih hx)
  have hGN : G ⊆ (⨆ n, Q n : Submodule ℂ V) := fun g hg =>
    mem_iSup_of_mem 0 (hQ0 ▸ subset_span hg)
  have hDN : ∀ u ∈ U, ∀ x ∈ (⨆ n, Q n : Submodule ℂ V), D u x ∈ (⨆ n, Q n : Submodule ℂ V) := by
    intro u hu x hx
    obtain ⟨n, hn⟩ := (mem_iSup_of_directed Q hmono.directed_le).1 hx
    exact mem_iSup_of_mem (n + 1) (hDQ n u hu x hn)
  obtain ⟨n, hn⟩ := (mem_iSup_of_directed Q hmono.directed_le).1 (hmin _ hGN hDN hf)
  exact ⟨Q n, hfin n, fun k => hT n k hn⟩

end GlobalTheory
