import Mathlib

namespace GlobalTheory.AdaptedFamilyIwasawaDecomposition

/- English proof (translation)
Take `⟨C₀, hC₀⟩` from `I.exists_isCompl`. Establish `hdis : Disjoint I (C₀ ⊓ L)` using `hC₀.disjoint.mono_right inf_le_left`. Establish `hsup : I ⊔ (C₀ ⊓ L) = L`. Rewrite using `[← sup_inf_assoc_of_le C₀ hIL, hC₀.sup_eq_top, top_inf_eq]`. Establish `hCL : C₀ ⊓ L ≤ L` using `inf_le_right`.

Generalize the expression as in `C₀ ⊓ L = C at hdis hsup hCL`. Establish `hdim : Module.finrank ℚ I + Module.finrank ℚ C = g`. Establish `h` using `Submodule.finrank_sup_add_finrank_inf_eq I C`. Rewrite `h` using `[hsup, hdis.eq_bot, finrank_bot, hg]`. Use linear arithmetic over natural numbers and integers.

Take `⟨k, ⟨bI⟩⟩ : ∃ k, Nonempty (Module.Basis (Fin k) ℚ I)` from `⟨_, ⟨Module.finBasis ℚ I⟩⟩`. Take `⟨m, ⟨bC⟩⟩ : ∃ m, Nonempty (Module.Basis (Fin m) ℚ C)` from `⟨_, ⟨Module.finBasis ℚ C⟩⟩`. Rewrite `hdim` using `[Module.finrank_eq_card_basis bI, Module.finrank_eq_card_basis bC, Fintype.card_fin, Fintype.card_fin]`. Use `clear hg`. Substitute `hdim` using the available equality.

Set `u : Fin k → Fin r → ℚ` to `I.subtype ∘ bI`. Set `v : Fin m → Fin r → ℚ` to `C.subtype ∘ bC`. Establish `hu : LinearIndependent ℚ u` using `bI.linearIndependent.map' _ (Submodule.ker_subtype I)`. Establish `hv : LinearIndependent ℚ v` using `bC.linearIndependent.map' _ (Submodule.ker_subtype C)`. Establish `huI : ∀ i, u i ∈ I` using `fun i => (bI i).2`.

Establish `hvC : ∀ i, v i ∈ C` using `fun i => (bC i).2`. Establish `hus : Submodule.span ℚ (Set.range u) = I`. Rewrite using `[Set.range_comp, ← Submodule.map_span, bI.span_eq, Submodule.map_top, Submodule.range_subtype]`. Establish `hvs : Submodule.span ℚ (Set.range v) ≤ C`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hvC i`. Establish `hli : LinearIndependent ℚ (Sum.elim u v)` using `hu.sum_type hv (by rw [hus]; exact hdis.mono_right hvs)`. Use `⟨k, Nat.le_add_right k m, Sum.elim u v ∘ finSumFinEquiv.symm, hli.comp _ finSumFinEquiv.symm.injective, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`.

Take `⟨j, rfl⟩` from `finSumFinEquiv.surjective i`. Break down `j with j | j` into its components or cases. Simplify `hIL (huI j)` using `only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl]`. Simplify `hCL (hvC j)` using `only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr]`. Introduce `i hi`.

Take `⟨j, rfl⟩` from `finSumFinEquiv.surjective i`. Break down `j with j | j` into its components or cases. Simplify `huI j` using `only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl]`. Simplify using `at hi`. Introduce `x hx`.

Rewrite `hx` using `[← hus]`. Use `Submodule.span_mono ?_ hx` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`. Use `⟨finSumFinEquiv (Sum.inl j), ?_, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.

Simplify using `only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl]`.
-/
theorem exists_adapted_family (g r : ℕ) (I L : Submodule ℚ (Fin r → ℚ)) (hIL : I ≤ L)
    (hg : Module.finrank ℚ ↥L = g) :
    ∃ rk ≤ g, ∃ (ε : Fin g → Fin r → ℚ), LinearIndependent ℚ ε ∧ (∀ (i : Fin g), ε i ∈ L) ∧
      (∀ (i : Fin g), (↑i : ℕ) < rk → ε i ∈ I) ∧
      ∀ x ∈ I, x ∈ Submodule.span ℚ (ε '' {i : Fin g | (↑i : ℕ) < rk}) := by
  obtain ⟨C₀, hC₀⟩ := I.exists_isCompl
  have hdis : Disjoint I (C₀ ⊓ L) := hC₀.disjoint.mono_right inf_le_left
  have hsup : I ⊔ (C₀ ⊓ L) = L := by
    rw [← sup_inf_assoc_of_le C₀ hIL, hC₀.sup_eq_top, top_inf_eq]
  have hCL : C₀ ⊓ L ≤ L := inf_le_right
  generalize C₀ ⊓ L = C at hdis hsup hCL
  have hdim : Module.finrank ℚ I + Module.finrank ℚ C = g := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq I C
    rw [hsup, hdis.eq_bot, finrank_bot, hg] at h
    omega
  obtain ⟨k, ⟨bI⟩⟩ : ∃ k, Nonempty (Module.Basis (Fin k) ℚ I) := ⟨_, ⟨Module.finBasis ℚ I⟩⟩
  obtain ⟨m, ⟨bC⟩⟩ : ∃ m, Nonempty (Module.Basis (Fin m) ℚ C) := ⟨_, ⟨Module.finBasis ℚ C⟩⟩
  rw [Module.finrank_eq_card_basis bI, Module.finrank_eq_card_basis bC, Fintype.card_fin,
    Fintype.card_fin] at hdim
  clear hg
  subst hdim
  let u : Fin k → Fin r → ℚ := I.subtype ∘ bI
  let v : Fin m → Fin r → ℚ := C.subtype ∘ bC
  have hu : LinearIndependent ℚ u := bI.linearIndependent.map' _ (Submodule.ker_subtype I)
  have hv : LinearIndependent ℚ v := bC.linearIndependent.map' _ (Submodule.ker_subtype C)
  have huI : ∀ i, u i ∈ I := fun i => (bI i).2
  have hvC : ∀ i, v i ∈ C := fun i => (bC i).2
  have hus : Submodule.span ℚ (Set.range u) = I := by
    rw [Set.range_comp, ← Submodule.map_span, bI.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  have hvs : Submodule.span ℚ (Set.range v) ≤ C := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hvC i
  have hli : LinearIndependent ℚ (Sum.elim u v) :=
    hu.sum_type hv (by rw [hus]; exact hdis.mono_right hvs)
  refine ⟨k, Nat.le_add_right k m, Sum.elim u v ∘ finSumFinEquiv.symm,
    hli.comp _ finSumFinEquiv.symm.injective, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
    rcases j with j | j
    · simpa only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl] using hIL (huI j)
    · simpa only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr] using hCL (hvC j)
  · intro i hi
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
    rcases j with j | j
    · simpa only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl] using huI j
    · simp at hi
  · intro x hx
    rw [← hus] at hx
    refine Submodule.span_mono ?_ hx
    rintro _ ⟨j, rfl⟩
    refine ⟨finSumFinEquiv (Sum.inl j), ?_, ?_⟩
    · simp
    · simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl]

end GlobalTheory.AdaptedFamilyIwasawaDecomposition
