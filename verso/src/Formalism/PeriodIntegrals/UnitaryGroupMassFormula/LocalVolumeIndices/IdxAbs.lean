import Mathlib

namespace PI.MassDataKppVolLemmas

/- English proof (translation)
Use `Nat.card_congr (Equiv.ofBijective (fun c => f (Function.surjInv hq c)) ⟨?_, ?_⟩)` and prove the remaining obligations. Introduce `c c' hcc`. Establish `h1` using `(h (Function.surjInv hq c) (Function.surjInv hq c')).2 hcc`. Simplify `h1` using `only [Function.surjInv_eq hq]`. Introduce `b`.

Take `⟨a, rfl⟩` from `hf b`. Conclude with `⟨q a, (h _ _).1 (Function.surjInv_eq hq (q a))⟩`.
-/
private theorem natCard_eq_of_surjective_of_same_fibres {α β γ : Type*} (q : α → γ) (f : α → β)
    (hq : Function.Surjective q) (hf : Function.Surjective f)
    (h : ∀ a b, q a = q b ↔ f a = f b) : Nat.card γ = Nat.card β := by
  refine Nat.card_congr (Equiv.ofBijective (fun c => f (Function.surjInv hq c)) ⟨?_, ?_⟩)
  · intro c c' hcc
    have h1 := (h (Function.surjInv hq c) (Function.surjInv hq c')).2 hcc
    simpa only [Function.surjInv_eq hq] using h1
  · intro b
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨q a, (h _ _).1 (Function.surjInv_eq hq (q a))⟩

/- English proof (translation)
Unfold `Subgroup.index`. Rewrite using `[← Nat.card_pi]`. Use `natCard_eq_of_surjective_of_same_fibres (fun a : A => (a : A ⧸ S)) (fun a i => ((ψ i a : B i) : B i ⧸ T i)) QuotientGroup.mk_surjective ?_ ?_` and prove the remaining obligations. Introduce `f choose g hg using fun i => QuotientGroup.mk_surjective (f i)`. Take `⟨a, ha⟩` from `hsurj g`.

Conclude with `⟨a, funext fun i => by simp only [ha, hg]⟩`. Introduce `a b`. Simplify using `only [funext_iff, QuotientGroup.eq, hmem, map_mul, map_inv]`.
-/
private theorem index_eq_prod_index_of_surjective_prod {A : Type*} [Group A] (S : Subgroup A) {ι : Type*}
    [Fintype ι] {B : ι → Type*} [∀ i, Group (B i)] (T : ∀ i, Subgroup (B i))
    (ψ : ∀ i, A →* B i) (hsurj : ∀ f : ∀ i, B i, ∃ a, ∀ i, ψ i a = f i)
    (hmem : ∀ a, a ∈ S ↔ ∀ i, ψ i a ∈ T i) :
    S.index = ∏ i, (T i).index := by
  unfold Subgroup.index
  rw [← Nat.card_pi]
  refine natCard_eq_of_surjective_of_same_fibres (fun a : A => (a : A ⧸ S))
    (fun a i => ((ψ i a : B i) : B i ⧸ T i)) QuotientGroup.mk_surjective ?_ ?_
  · intro f
    choose g hg using fun i => QuotientGroup.mk_surjective (f i)
    obtain ⟨a, ha⟩ := hsurj g
    exact ⟨a, funext fun i => by simp only [ha, hg]⟩
  · intro a b
    simp only [funext_iff, QuotientGroup.eq, hmem, map_mul, map_inv]

/- English proof (translation)
Take `⟨ψ, hψ⟩ : ∃ ψ : ∀ i, K →* Lp i, ∀ i (a : K), ((ψ i a : Lp i) : Gp i) = π i a` from `⟨fun i => ((π i).comp K.subtype).codRestrict (Lp i) (fun z => hK i z z.2), fun _ _ => rfl⟩`. Establish `hs : ∀ f : ∀ i, Lp i, ∃ a : K, ∀ i, ψ i a = f i`. Introduce `f`. Take `⟨z, hzK, hz⟩` from `hsurj f`. Conclude with `⟨⟨z, hzK⟩, fun i => Subtype.ext ((hψ i ⟨z, hzK⟩).trans (hz i))⟩`.

Establish `hm : ∀ a : K, a ∈ K2.subgroupOf K ↔ ∀ i, ψ i a ∈ (K2.map (π i)).subgroupOf (Lp i)`. Introduce `a`. Simplify using `only [Subgroup.mem_subgroupOf, Subgroup.mem_map, hψ]`. Conclude with `⟨fun ha _ => ⟨(a : G), ha, rfl⟩, fun h => hloc a a.2 h⟩`. Establish `key` using `index_eq_prod_index_of_surjective_prod (K2.subgroupOf K) (fun i => (K2.map (π i)).subgroupOf (Lp i)) ψ hs hm`.

Conclude with `key`.
-/
theorem IdxAbs_relIndex {G : Type} [Group G] (K K2 : Subgroup G) {ι : Type} [Fintype ι]
    {Gp : ι → Type} [∀ i, Group (Gp i)] (π : ∀ i, G →* Gp i) (Lp : ∀ i, Subgroup (Gp i))
    (hK : ∀ i, ∀ z ∈ K, π i z ∈ Lp i)
    (hsurj : ∀ f : ∀ i, Lp i, ∃ z ∈ K, ∀ i, π i z = f i)
    (hloc : ∀ z ∈ K, (∀ i, ∃ w ∈ K2, π i w = π i z) → z ∈ K2) :
    K2.relIndex K = ∏ i, (K2.map (π i)).relIndex (Lp i) := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ∀ i, K →* Lp i, ∀ i (a : K), ((ψ i a : Lp i) : Gp i) = π i a :=
    ⟨fun i => ((π i).comp K.subtype).codRestrict (Lp i) (fun z => hK i z z.2),
      fun _ _ => rfl⟩
  have hs : ∀ f : ∀ i, Lp i, ∃ a : K, ∀ i, ψ i a = f i := by
    intro f
    obtain ⟨z, hzK, hz⟩ := hsurj f
    exact ⟨⟨z, hzK⟩, fun i => Subtype.ext ((hψ i ⟨z, hzK⟩).trans (hz i))⟩
  have hm : ∀ a : K, a ∈ K2.subgroupOf K ↔
      ∀ i, ψ i a ∈ (K2.map (π i)).subgroupOf (Lp i) := by
    intro a
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, hψ]
    exact ⟨fun ha _ => ⟨(a : G), ha, rfl⟩, fun h => hloc a a.2 h⟩
  have key := index_eq_prod_index_of_surjective_prod (K2.subgroupOf K)
    (fun i => (K2.map (π i)).subgroupOf (Lp i)) ψ hs hm
  exact key

end PI.MassDataKppVolLemmas
