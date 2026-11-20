import Mathlib

universe u_1 u_2

namespace GlobalTheory.CommonEigenvector

/- English proof (translation)
Set `P : Submodule ℂ V → Prop` to `fun W => W ≤ E ∧ W ≠ ⊥ ∧ ∀ i, ∀ x ∈ W, (H i : V → V) x ∈ W`. Establish `hex : ∃ n, ∃ W, P W ∧ Module.finrank ℂ W = n` using `⟨_, E, ⟨le_rfl, hne, hE⟩, rfl⟩`. Take `⟨W, ⟨hWE, hW0, hWi⟩, hWn⟩` from `Nat.find_spec hex`. Establish `hmin : ∀ W', P W' → Module.finrank ℂ W ≤ Module.finrank ℂ W'` using `fun W' hW' => by`. Rewrite using `[hWn]`.

Conclude with `Nat.find_min' hex ⟨W', hW', rfl⟩`. Establish `: FiniteDimensional ℂ W` using `Submodule.finiteDimensional_of_le hWE`. Establish `: Nontrivial W` using `Submodule.nontrivial_iff_ne_bot.mpr hW0`. Use `⟨W, hWE, hW0, fun i => ?_⟩` and prove the remaining obligations. Take `⟨c, hce⟩` from `Module.End.exists_eigenvalue ((H i).restrict (hWi i))`.

Take `⟨w, hw⟩` from `hce.exists_hasEigenvector`. Establish `hwv : (H i : V → V) w = c • (w : V)`. Establish `h1` using `congrArg Subtype.val hw.apply_eq_smul`. Simplify using `using h1`. Set `W' : Submodule ℂ V` to `W ⊓ LinearMap.ker (H i - c • LinearMap.id)`.

Establish `hmem : ∀ x, x ∈ W' ↔ x ∈ W ∧ (H i : V → V) x = c • x`. Introduce `x`. Simplify using `[W', sub_eq_zero]`. Establish `hW'le : W' ≤ W` using `inf_le_left`. Establish `hW'P : P W'`.

Use `⟨hW'le.trans hWE, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Establish `hw' : (w : V) ∈ W'` using `(hmem _).2 ⟨w.2, hwv⟩`. Rewrite `hw'` using `[h, Submodule.mem_bot]`. Conclude with `hw.2 (Subtype.ext hw')`.

Introduce `j x hx`. Take `⟨hxW, hxe⟩` from `(hmem x).1 hx`. Use `(hmem _).2 ⟨hWi j x hxW, ?_⟩` and prove the remaining obligations. Establish `hcom` using `congrArg (fun f : Module.End ℂ V => f x) (hc i j)`. Simplify using `only [Module.End.mul_apply] at hcom`.

Rewrite using `[hcom, hxe, map_smul]`. Establish `hle : Module.finrank ℂ W' ≤ Module.finrank ℂ W` using `LinearMap.finrank_le_finrank_of_injective (Submodule.inclusion_injective hW'le)`. Establish `hEq : W' = W` using `Submodule.eq_of_le_of_finrank_eq hW'le (le_antisymm hle (hmin W' hW'P))`. Use `⟨c, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[← hEq]`.

Conclude with `((hmem x).1 hx).2`.
-/
private lemma exists_common_eigenspace_of_commuting {V : Type u_1} {ι : Type u_2} [AddCommGroup V] [Module ℂ V]
    (H : ι → Module.End ℂ V) (hc : ∀ (i j : ι), H i * H j = H j * H i)
    (E : Submodule ℂ V) [FiniteDimensional ℂ ↥E] (hE : ∀ (i : ι), ∀ x ∈ E, (H i : V → V) x ∈ E)
    (hne : E ≠ ⊥) :
    ∃ W : Submodule ℂ V, W ≤ E ∧ W ≠ ⊥ ∧ ∀ i, ∃ c : ℂ, ∀ x ∈ W, (H i : V → V) x = c • x := by

  classical
  let P : Submodule ℂ V → Prop := fun W => W ≤ E ∧ W ≠ ⊥ ∧ ∀ i, ∀ x ∈ W, (H i : V → V) x ∈ W
  have hex : ∃ n, ∃ W, P W ∧ Module.finrank ℂ W = n := ⟨_, E, ⟨le_rfl, hne, hE⟩, rfl⟩
  obtain ⟨W, ⟨hWE, hW0, hWi⟩, hWn⟩ := Nat.find_spec hex
  have hmin : ∀ W', P W' → Module.finrank ℂ W ≤ Module.finrank ℂ W' := fun W' hW' => by
    rw [hWn]
    exact Nat.find_min' hex ⟨W', hW', rfl⟩
  have : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hWE
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW0
  refine ⟨W, hWE, hW0, fun i => ?_⟩
  obtain ⟨c, hce⟩ := Module.End.exists_eigenvalue ((H i).restrict (hWi i))
  obtain ⟨w, hw⟩ := hce.exists_hasEigenvector
  have hwv : (H i : V → V) w = c • (w : V) := by
    have h1 := congrArg Subtype.val hw.apply_eq_smul
    simpa using h1
  let W' : Submodule ℂ V := W ⊓ LinearMap.ker (H i - c • LinearMap.id)
  have hmem : ∀ x, x ∈ W' ↔ x ∈ W ∧ (H i : V → V) x = c • x := by
    intro x
    simp [W', sub_eq_zero]
  have hW'le : W' ≤ W := inf_le_left
  have hW'P : P W' := by
    refine ⟨hW'le.trans hWE, ?_, ?_⟩
    · intro h
      have hw' : (w : V) ∈ W' := (hmem _).2 ⟨w.2, hwv⟩
      rw [h, Submodule.mem_bot] at hw'
      exact hw.2 (Subtype.ext hw')
    · intro j x hx
      obtain ⟨hxW, hxe⟩ := (hmem x).1 hx
      refine (hmem _).2 ⟨hWi j x hxW, ?_⟩
      have hcom := congrArg (fun f : Module.End ℂ V => f x) (hc i j)
      simp only [Module.End.mul_apply] at hcom
      rw [hcom, hxe, map_smul]
  have hle : Module.finrank ℂ W' ≤ Module.finrank ℂ W :=
    LinearMap.finrank_le_finrank_of_injective (Submodule.inclusion_injective hW'le)
  have hEq : W' = W := Submodule.eq_of_le_of_finrank_eq hW'le (le_antisymm hle (hmin W' hW'P))
  refine ⟨c, fun x hx => ?_⟩
  rw [← hEq] at hx
  exact ((hmem x).1 hx).2

/- English proof (translation)
Take `⟨W, hWE, hW0, hW⟩` from `exists_common_eigenspace_of_commuting H hc E hE hne`. Take `⟨v, hv, hv0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hW0`. Conclude with `⟨v, hWE hv, hv0, fun i => (hW i).imp fun c h => h v hv⟩`.
-/
theorem main {V : Type u_1} {ι : Type u_2} [AddCommGroup V] [Module ℂ V] [Fintype ι]
    (H : ι → Module.End ℂ V) (hc : ∀ (i j : ι), H i * H j = H j * H i)
    (E : Submodule ℂ V) [FiniteDimensional ℂ ↥E] (hE : ∀ (i : ι), ∀ x ∈ E, (H i : V → V) x ∈ E)
    (hne : E ≠ ⊥) :
    ∃ v ∈ E, v ≠ (0 : V) ∧ ∀ (i : ι), ∃ (c : ℂ), (H i : V → V) v = c • v := by
  obtain ⟨W, hWE, hW0, hW⟩ := exists_common_eigenspace_of_commuting H hc E hE hne
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  exact ⟨v, hWE hv, hv0, fun i => (hW i).imp fun c h => h v hv⟩

/- English proof (translation)
Introduce `V ι _ _ _ H hc E _ hE hne`. Take `⟨W, hWE, hW0, hW⟩` from `exists_common_eigenspace_of_commuting H hc E hE hne`. Take `⟨v, hv, hv0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hW0`. Use `⟨v, hWE hv, hv0, fun i => ?_⟩` and prove the remaining obligations. Take `⟨c, hc'⟩` from `hW i`.

Conclude with `⟨c, hc' v hv⟩`.
-/
theorem common_eigenvector : ∀ {V : Type u_1} {ι : Type u_2} [inst : AddCommGroup V] [inst_1 : Module ℂ V] [Fintype ι] (H : ι → Module.End ℂ V), (∀ (i j : ι), H i * H j = H j * H i) → ∀ (E : Submodule ℂ V) [FiniteDimensional ℂ ↥E], (∀ (i : ι), ∀ x ∈ E, (H i : V → V) x ∈ E) → E ≠ ⊥ → ∃ v ∈ E, v ≠ (0 : V) ∧ ∀ (i : ι), ∃ (c : ℂ), (H i : V → V) v = c • v := by
  intro V ι _ _ _ H hc E _ hE hne

  obtain ⟨W, hWE, hW0, hW⟩ := exists_common_eigenspace_of_commuting H hc E hE hne
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  refine ⟨v, hWE hv, hv0, fun i => ?_⟩
  obtain ⟨c, hc'⟩ := hW i
  exact ⟨c, hc' v hv⟩

end GlobalTheory.CommonEigenvector
