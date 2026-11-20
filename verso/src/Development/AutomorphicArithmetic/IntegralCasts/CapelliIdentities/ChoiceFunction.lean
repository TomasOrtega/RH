import Mathlib

/- English proof (translation)
Introduce `k D _ P p0 hp0 W hW n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `Y _ h`. Use `⟨fun _ => p0, fun _ => hp0, fun f hf _ => ?_⟩` and prove the remaining obligations.

Establish `heq : Y ⊓ W = Y` using `Submodule.eq_of_le_of_finrank_le inf_le_left (by simpa using h)`. Rewrite `hf` using `[← heq]`. Conclude with `hf.2`. Consider the case `succ n ih`. Introduce `Y _ h`.

Distinguish the cases in `hYW : Y ≤ W`. Conclude with `⟨fun _ => p0, fun _ => hp0, fun f hf _ => hYW hf⟩`. Take `⟨g, hgY, hgW⟩` from `SetLike.not_le_iff_exists.mp hYW`. Rewrite `hgW` using `[hW]`. Simplify using `only [not_forall] at hgW`.

Take `⟨p, hp, hgp⟩` from `hgW`. Set `K : Submodule k (D → k)` to `LinearMap.ker (LinearMap.proj p : (D → k) →ₗ[k] k)`. Establish `hK : ∀ f : D → k, f ∈ K ↔ f p = 0` using `fun f => LinearMap.mem_ker`. Establish `hWK : W ≤ K` using `fun f hf => (hK f).2 ((hW f).1 hf p hp)`. Use `haveI : FiniteDimensional k ↥(Y ⊓ K) := Submodule.finiteDimensional_of_le inf_le_left`.

Establish `hlt : Y ⊓ K < Y`. Use `lt_of_le_of_ne inf_le_left fun he => hgp ?_` and prove the remaining obligations. Rewrite `hgY` using `[← he]`. Conclude with `(hK g).1 hgY.2`. Establish `hrank` using `Submodule.finrank_lt_finrank_of_lt hlt`.

Establish `hinf : (Y ⊓ K) ⊓ W = Y ⊓ W`. Rewrite using `[inf_assoc, inf_eq_right.2 hWK]`. Take `⟨u, hu, hu'⟩` from `ih (Y ⊓ K) (by rw [hinf]; omega)`. Use `⟨Fin.cons p u, fun a => ?_, fun f hf hz => ?_⟩` and prove the remaining obligations. Use `Fin.cases ?_ (fun i => ?_) a` and prove the remaining obligations.

Simplify using `using hp`. Simplify using `using hu i`. Use `hu' f ⟨hf, (hK f).2 ?_⟩ fun a => ?_` and prove the remaining obligations. Simplify using `using hz 0`. Simplify using `using hz a.succ`.
-/
theorem UpperTheory.Reformulated.B.InterpolationPointsOfFinrankBound.pick :
    ∀ {k D : Type} [inst : Field k] (P : Set D) {p0 : D},
    p0 ∈ P →
      ∀ (W : Submodule k (D → k)),
        (∀ (f : D → k), f ∈ W ↔ ∀ p ∈ P, f p = (0 : k)) →
          ∀ (n : ℕ) (Y : Submodule k (D → k)) [FiniteDimensional k ↥Y],
            Module.finrank k ↥Y ≤ n + Module.finrank k ↥(Y ⊓ W) →
              ∃ (u : Fin n → D), (∀ (a : Fin n), u a ∈ P) ∧ ∀ f ∈ Y, (∀ (a : Fin n), f (u a) = (0 : k)) → f ∈ W := by
  intro k D _ P p0 hp0 W hW n
  induction n with
  | zero =>
    intro Y _ h
    refine ⟨fun _ => p0, fun _ => hp0, fun f hf _ => ?_⟩
    have heq : Y ⊓ W = Y :=
      Submodule.eq_of_le_of_finrank_le inf_le_left (by simpa using h)
    rw [← heq] at hf
    exact hf.2
  | succ n ih =>
    intro Y _ h
    by_cases hYW : Y ≤ W
    · exact ⟨fun _ => p0, fun _ => hp0, fun f hf _ => hYW hf⟩
    · obtain ⟨g, hgY, hgW⟩ := SetLike.not_le_iff_exists.mp hYW
      rw [hW] at hgW
      simp only [not_forall] at hgW
      obtain ⟨p, hp, hgp⟩ := hgW
      let K : Submodule k (D → k) := LinearMap.ker (LinearMap.proj p : (D → k) →ₗ[k] k)
      have hK : ∀ f : D → k, f ∈ K ↔ f p = 0 := fun f => LinearMap.mem_ker
      have hWK : W ≤ K := fun f hf => (hK f).2 ((hW f).1 hf p hp)
      haveI : FiniteDimensional k ↥(Y ⊓ K) := Submodule.finiteDimensional_of_le inf_le_left
      have hlt : Y ⊓ K < Y := by
        refine lt_of_le_of_ne inf_le_left fun he => hgp ?_
        rw [← he] at hgY
        exact (hK g).1 hgY.2
      have hrank := Submodule.finrank_lt_finrank_of_lt hlt
      have hinf : (Y ⊓ K) ⊓ W = Y ⊓ W := by
        rw [inf_assoc, inf_eq_right.2 hWK]
      obtain ⟨u, hu, hu'⟩ := ih (Y ⊓ K) (by rw [hinf]; omega)
      refine ⟨Fin.cons p u, fun a => ?_, fun f hf hz => ?_⟩
      · refine Fin.cases ?_ (fun i => ?_) a
        · simpa using hp
        · simpa using hu i
      · refine hu' f ⟨hf, (hK f).2 ?_⟩ fun a => ?_
        · simpa using hz 0
        · simpa using hz a.succ
