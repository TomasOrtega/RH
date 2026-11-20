import Mathlib

/- English proof (translation)
Introduce `Γ _ s t h`. Establish `key : ∀ (u : Finset (Γ →* ℂ)) (r : Multiset (Γ →* ℂ)), r.toFinset ⊆ u → ∀ g : Γ, (Multiset.map (fun (f : Γ →* ℂ) ↦ (f : Γ → ℂ) g) r).sum = ∑ f ∈ u, (r.count f : ℂ) * f g`. Introduce `u r hr g`. Rewrite using `[Finset.sum_multiset_map_count, Finset.sum_subset hr]`. Conclude with `Finset.sum_congr rfl fun f _ => by simp`.

Introduce `f _ hf`. Establish `: r.count f = 0` using `Multiset.count_eq_zero.2 (by simpa using hf)`. Simplify using `[this]`. Use `set u : Finset (Γ →* ℂ) := s.toFinset ∪ t.toFinset with hu`. Establish `hs : s.toFinset ⊆ u` using `Finset.subset_union_left`.

Establish `ht : t.toFinset ⊆ u` using `Finset.subset_union_right`. Establish `lin` using `linearIndependent_iff'.1 (linearIndependent_monoidHom Γ ℂ) u (fun f => (s.count f : ℂ) - (t.count f : ℂ)) (by`. Use function extensionality and compare the values at `g`. Establish `e` using `h g`. Rewrite `e` using `[key u s hs g, key u t ht g]`.

Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_mul, Finset.sum_sub_distrib]`. Conclude with `sub_eq_zero.2 e)`. Use extensionality with `f`. Distinguish the cases in `hf : f ∈ u`. Use `lin f hf` as an intermediate fact.

Conclude with `sub_eq_zero.1 this` after adjusting the coercions. Establish `h1 : f ∉ s` using `fun m => hf (hs (by simpa using m))`. Establish `h2 : f ∉ t` using `fun m => hf (ht (by simpa using m))`. Rewrite using `[Multiset.count_eq_zero.2 h1, Multiset.count_eq_zero.2 h2]`.
-/
theorem UpperTheory.Reformulated.B.Qf50.multiset_eq_of_sum :
    ∀ {Γ : Type} [inst : Monoid Γ] (s t : Multiset (Γ →* ℂ)),
    (∀ (g : Γ),
        (Multiset.map (fun (f : Γ →* ℂ) ↦ (f : Γ → ℂ) g) s).sum =
          (Multiset.map (fun (f : Γ →* ℂ) ↦ (f : Γ → ℂ) g) t).sum) →
      s = t := by
  classical
  intro Γ _ s t h
  have key : ∀ (u : Finset (Γ →* ℂ)) (r : Multiset (Γ →* ℂ)), r.toFinset ⊆ u → ∀ g : Γ,
      (Multiset.map (fun (f : Γ →* ℂ) ↦ (f : Γ → ℂ) g) r).sum
        = ∑ f ∈ u, (r.count f : ℂ) * f g := by
    intro u r hr g
    rw [Finset.sum_multiset_map_count, Finset.sum_subset hr]
    · exact Finset.sum_congr rfl fun f _ => by simp
    · intro f _ hf
      have : r.count f = 0 := Multiset.count_eq_zero.2 (by simpa using hf)
      simp [this]
  set u : Finset (Γ →* ℂ) := s.toFinset ∪ t.toFinset with hu
  have hs : s.toFinset ⊆ u := Finset.subset_union_left
  have ht : t.toFinset ⊆ u := Finset.subset_union_right
  have lin := linearIndependent_iff'.1 (linearIndependent_monoidHom Γ ℂ) u
    (fun f => (s.count f : ℂ) - (t.count f : ℂ)) (by
      funext g
      have e := h g
      rw [key u s hs g, key u t ht g] at e
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_mul,
        Finset.sum_sub_distrib]
      exact sub_eq_zero.2 e)
  ext f
  by_cases hf : f ∈ u
  · have := lin f hf
    exact_mod_cast sub_eq_zero.1 this
  · have h1 : f ∉ s := fun m => hf (hs (by simpa using m))
    have h2 : f ∉ t := fun m => hf (ht (by simpa using m))
    rw [Multiset.count_eq_zero.2 h1, Multiset.count_eq_zero.2 h2]
