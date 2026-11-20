import Mathlib

namespace GlobalTheory

/- English proof (translation)
Establish `key : ∀ y ∈ L, (y ∈ L.map T ↔ Φ y ∈ (L.map Φ).map h)`. Introduce `y hy`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨Φ x, ⟨x, hx, rfl⟩, (hΦT x).symm⟩`.

Introduce and unpack `⟨_, ⟨x, hx, rfl⟩, hxy⟩`. Establish `h0 : Φ (T x - y) = 0` using `by rw [map_sub, hΦT, hxy, sub_self]`. Establish `hp : p (T x) = p y`. Use `hΦ _ h0` as an intermediate fact. Rewrite `this` using `[map_sub, sub_eq_zero]`. Then use the resulting hypothesis.

Use `⟨p x + (y - p y), L.add_mem (hpL x hx) (L.sub_mem hy (hpL y hy)), ?_⟩` and prove the remaining obligations. Use `show T (p x + (y - p y)) = y`. Rewrite using `[map_add, hT1, hTp, hp]`. Normalize the expressions using the abelian group laws. Set `ψ : L →+ L.map Φ` to `(Φ.comp L.subtype).codRestrict (L.map Φ) (fun x => ⟨x.1, x.2, rfl⟩)`.

Establish `hψ : Function.Surjective ψ`. Introduce and unpack `⟨_, x, hx, rfl⟩`. Conclude with `⟨⟨x, hx⟩, rfl⟩`. Establish `hc : (L.map T).addSubgroupOf L = (((L.map Φ).map h).addSubgroupOf (L.map Φ)).comap ψ`. Use extensionality with `⟨y, hy⟩`.

Rewrite using `[AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]`. Conclude with `key y hy`. Unfold `AddSubgroup.relIndex`. Rewrite using `[hc, AddSubgroup.index_comap_of_surjective _ hψ]`.
-/
theorem index_transfer_along_projection {M N : Type} [AddCommGroup M] [AddCommGroup N]
    (L : AddSubgroup M) (T p : M →+ M) (Φ : M →+ N) (h : N →+ N)
    (hpL : ∀ y ∈ L, p y ∈ L) (hTp : ∀ y, T (p y) = p (T y))
    (hT1 : ∀ y, T (y - p y) = y - p y) (hΦ : ∀ y, Φ y = 0 → p y = 0)
    (hΦT : ∀ y, Φ (T y) = h (Φ y)) :
    (L.map T).relIndex L = ((L.map Φ).map h).relIndex (L.map Φ) := by
  have key : ∀ y ∈ L, (y ∈ L.map T ↔ Φ y ∈ (L.map Φ).map h) := by
    intro y hy
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Φ x, ⟨x, hx, rfl⟩, (hΦT x).symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, hxy⟩
      have h0 : Φ (T x - y) = 0 := by rw [map_sub, hΦT, hxy, sub_self]
      have hp : p (T x) = p y := by
        have := hΦ _ h0
        rwa [map_sub, sub_eq_zero] at this
      refine ⟨p x + (y - p y), L.add_mem (hpL x hx) (L.sub_mem hy (hpL y hy)), ?_⟩
      show T (p x + (y - p y)) = y
      rw [map_add, hT1, hTp, hp]
      abel
  let ψ : L →+ L.map Φ :=
    (Φ.comp L.subtype).codRestrict (L.map Φ) (fun x => ⟨x.1, x.2, rfl⟩)
  have hψ : Function.Surjective ψ := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hc : (L.map T).addSubgroupOf L =
      (((L.map Φ).map h).addSubgroupOf (L.map Φ)).comap ψ := by
    ext ⟨y, hy⟩
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
    exact key y hy
  unfold AddSubgroup.relIndex
  rw [hc, AddSubgroup.index_comap_of_surjective _ hψ]

end GlobalTheory
