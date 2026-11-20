import Mathlib

namespace GlobalTheory

/- English proof (translation)
Establish `hc : ∀ c, Fintype.card {i // g' i = c} = Fintype.card {i // g i = c}`. Introduce `c`. Use `congrArg (Multiset.count c) h` as an intermediate fact. Rewrite `this` using `[Multiset.count_map, Multiset.count_map]`. Rewrite using `[Fintype.card_subtype, Fintype.card_subtype]`.

Simplify using `only [Finset.card, Finset.filter_val]`. Simplify `this.symm` using `only [eq_comm]`. Conclude with `⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hc c)), fun i => Equiv.ofFiberEquiv_map _ i⟩`.
-/
theorem exists_perm_of_univ_map_eq {ι β : Type} [Fintype ι] (g g' : ι → β)
    (h : Finset.univ.val.map g = Finset.univ.val.map g') :
    ∃ π : Equiv.Perm ι, ∀ i, g (π i) = g' i := by
  classical
  have hc : ∀ c, Fintype.card {i // g' i = c} = Fintype.card {i // g i = c} := by
    intro c
    have := congrArg (Multiset.count c) h
    rw [Multiset.count_map, Multiset.count_map] at this
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simp only [Finset.card, Finset.filter_val]
    simpa only [eq_comm] using this.symm
  exact ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hc c)),
    fun i => Equiv.ofFiberEquiv_map _ i⟩

/- English proof (translation)
Introduce `m f hf α α' hα h`. Establish `hα' : ∀ i, α' i ≠ 0`. Introduce `i hi`. Establish `hmem : (0 : ℂ) ∈ Finset.univ.val.map α' + Finset.univ.val.map (fun i => (α' i)⁻¹)` using `Multiset.mem_add.2 (Or.inl (Multiset.mem_map.2 ⟨i, Finset.mem_univ_val i, hi⟩))`. Rewrite `hmem` using `[← h]`.

Break down `Multiset.mem_add.1 hmem with h1 | h1` into its components or cases. Take `⟨j, -, hj⟩` from `Multiset.mem_map.1 h1`. Conclude with `hα j hj`. Take `⟨j, -, hj⟩` from `Multiset.mem_map.1 h1`. Conclude with `hα j (inv_eq_zero.1 hj)`.

Establish `h2` using `congrArg (Multiset.map (fun x : ℂ => x + x⁻¹)) h`. Simplify using `only [Multiset.map_add, Multiset.map_map, Function.comp_def, inv_inv] at h2`. Establish `e1 : ∀ γ : Fin m → ℂ, (fun i => (γ i)⁻¹ + γ i) = fun i => γ i + (γ i)⁻¹` using `fun γ => funext fun i => add_comm _ _`. Rewrite `h2` using `[e1 α, e1 α']`. Establish `h3 : Finset.univ.val.map (fun i => α i + (α i)⁻¹) = Finset.univ.val.map (fun i => α' i + (α' i)⁻¹)`.

Use extensionality with `c`. Use `congrArg (Multiset.count c) h2` as an intermediate fact. Simplify using `only [Multiset.count_add] at this`. Use linear arithmetic over natural numbers and integers. Take `⟨π, hπ⟩` from `exists_perm_of_univ_map_eq _ _ h3`.

Establish `hor : ∀ i, α' i = α (π i) ∨ α' i = (α (π i))⁻¹`. Introduce `i`. Establish `h4` using `hπ i`. Establish `ha` using `hα (π i)`. Establish `hb` using `hα' i`.

Establish `h5 : (α' i - α (π i)) * (α' i * α (π i) - 1) = 0`. Clear denominators, using `at h4` for the nonvanishing conditions. Take the linear combination `-h4`. Break down `mul_eq_zero.1 h5 with h6 | h6` into its components or cases. Conclude with `Or.inl (sub_eq_zero.1 h6)`.

Conclude with `Or.inr (eq_inv_of_mul_eq_one_left (sub_eq_zero.1 h6))`. Establish `hβ : ∀ i, (α ∘ π) i ≠ 0` using `fun i => hα _`. Establish `key : ∀ s : Finset (Fin m), f (fun i => if i ∈ s then α' i else (α ∘ π) i) = f (α ∘ π)`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty => simp [Function.comp_def]`. Consider the case `insert j s hj ih`. Rewrite using `[← ih]`. Establish `hne : ∀ i, (fun i => if i ∈ s then α' i else (α ∘ π) i) i ≠ 0`. Introduce `i`.

Distinguish the cases in `hi : i ∈ s`. Simplify `hα' i` using `[hi]`. Simplify `hα (π i)` using `[hi]`. Break down `hor j with h6 | h6` into its components or cases. Use `congr 1`.

Use function extensionality and compare the values at `i`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[hj, h6]`. Simplify using `[hij]`.

Rewrite using `[← (hf _ hne).2 j]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Simplify using `[hj, h6]`. Simplify using `[hij]`. Use `key Finset.univ` as an intermediate fact. Simplify using `only [Finset.mem_univ, if_true] at this`. Rewrite using `[← (hf α hα).1 π, ← this]`.
-/
theorem eq_of_perm_inv_invariant_of_multiset_eq :
    ∀ (m : ℕ) (f : (Fin m → ℂ) → ℂ), (∀ α : Fin m → ℂ, (∀ i, α i ≠ 0) → (∀ π : Equiv.Perm (Fin m), f (α ∘ π) = f α) ∧ ∀ i, f (Function.update α i (α i)⁻¹) = f α) → ∀ α α' : Fin m → ℂ, (∀ i, α i ≠ 0) → Finset.univ.val.map α + Finset.univ.val.map (fun i => (α i)⁻¹) = Finset.univ.val.map α' + Finset.univ.val.map (fun i => (α' i)⁻¹) → f α = f α' := by
  classical
  intro m f hf α α' hα h
  have hα' : ∀ i, α' i ≠ 0 := by
    intro i hi
    have hmem : (0 : ℂ) ∈ Finset.univ.val.map α' + Finset.univ.val.map (fun i => (α' i)⁻¹) :=
      Multiset.mem_add.2 (Or.inl (Multiset.mem_map.2 ⟨i, Finset.mem_univ_val i, hi⟩))
    rw [← h] at hmem
    rcases Multiset.mem_add.1 hmem with h1 | h1
    · obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 h1
      exact hα j hj
    · obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 h1
      exact hα j (inv_eq_zero.1 hj)
  have h2 := congrArg (Multiset.map (fun x : ℂ => x + x⁻¹)) h
  simp only [Multiset.map_add, Multiset.map_map, Function.comp_def, inv_inv] at h2
  have e1 : ∀ γ : Fin m → ℂ, (fun i => (γ i)⁻¹ + γ i) = fun i => γ i + (γ i)⁻¹ :=
    fun γ => funext fun i => add_comm _ _
  rw [e1 α, e1 α'] at h2
  have h3 : Finset.univ.val.map (fun i => α i + (α i)⁻¹)
      = Finset.univ.val.map (fun i => α' i + (α' i)⁻¹) := by
    ext c
    have := congrArg (Multiset.count c) h2
    simp only [Multiset.count_add] at this
    omega
  obtain ⟨π, hπ⟩ := exists_perm_of_univ_map_eq _ _ h3
  have hor : ∀ i, α' i = α (π i) ∨ α' i = (α (π i))⁻¹ := by
    intro i
    have h4 := hπ i
    have ha := hα (π i)
    have hb := hα' i
    have h5 : (α' i - α (π i)) * (α' i * α (π i) - 1) = 0 := by
      field_simp at h4
      linear_combination -h4
    rcases mul_eq_zero.1 h5 with h6 | h6
    · exact Or.inl (sub_eq_zero.1 h6)
    · exact Or.inr (eq_inv_of_mul_eq_one_left (sub_eq_zero.1 h6))
  have hβ : ∀ i, (α ∘ π) i ≠ 0 := fun i => hα _
  have key : ∀ s : Finset (Fin m),
      f (fun i => if i ∈ s then α' i else (α ∘ π) i) = f (α ∘ π) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [Function.comp_def]
    | insert j s hj ih =>
      rw [← ih]
      have hne : ∀ i, (fun i => if i ∈ s then α' i else (α ∘ π) i) i ≠ 0 := by
        intro i
        by_cases hi : i ∈ s
        · simpa [hi] using hα' i
        · simpa [hi] using hα (π i)
      rcases hor j with h6 | h6
      · congr 1
        funext i
        by_cases hij : i = j
        · subst hij
          simp [hj, h6]
        · simp [hij]
      · rw [← (hf _ hne).2 j]
        congr 1
        funext i
        by_cases hij : i = j
        · subst hij
          simp [hj, h6]
        · simp [hij]
  have := key Finset.univ
  simp only [Finset.mem_univ, if_true] at this
  rw [← (hf α hα).1 π, ← this]

end GlobalTheory
