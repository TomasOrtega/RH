import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero

open Matrix Complex Unitary
open scoped ComplexOrder

namespace GlobalTheory.PosSemidefShiftByScalar

/- English proof (translation)
Establish `hH` using `hA.isHermitian`. Choose the witnesses or unpack the hypotheses as in `⟨δ, hδ, hle⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ hH.eigenvalues i := by`. Break down `isEmpty_or_nonempty n with h | h` into its components or cases. Conclude with `⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩`. Take `⟨i0, -, hi0⟩` from `Finset.exists_min_image Finset.univ hH.eigenvalues Finset.univ_nonempty`.

Conclude with `⟨_, hA.eigenvalues_pos i0, fun i => hi0 i (Finset.mem_univ i)⟩`. Use `⟨δ, hδ, fun δ' hδ' => ?_⟩` and prove the remaining obligations. Establish `e : A - (δ' : ℂ) • (1 : Matrix n n ℂ) = conjStarAlgAut ℂ _ hH.eigenvectorUnitary (diagonal (fun i => ((hH.eigenvalues i - δ' : ℝ) : ℂ)))`. Establish `d : diagonal (fun i => ((hH.eigenvalues i - δ' : ℝ) : ℂ)) = diagonal (RCLike.ofReal ∘ hH.eigenvalues) - (δ' : ℂ) • (1 : Matrix n n ℂ)`. Apply the tactic sequence `ext i j; by_cases h : i = j <;> simp [diagonal, one_apply, h]`.

Use `conv_lhs => rw [hH.spectral_theorem]`. Rewrite using `[d, map_sub, map_smul, map_one]`. Rewrite using `[e, conjStarAlgAut_apply, isUnit_coe.posSemidef_star_right_conjugate_iff]`. Conclude with `PosSemidef.diagonal fun i => Complex.zero_le_real.2 (sub_nonneg.2 (hδ'.trans (hle i)))`.
-/
theorem posSemidef_sub_smul_one {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.PosDef) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ δ' : ℝ, δ' ≤ δ → (A - (δ' : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := by
  have hH := hA.isHermitian
  obtain ⟨δ, hδ, hle⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ hH.eigenvalues i := by
    rcases isEmpty_or_nonempty n with h | h
    · exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
    · obtain ⟨i0, -, hi0⟩ :=
        Finset.exists_min_image Finset.univ hH.eigenvalues Finset.univ_nonempty
      exact ⟨_, hA.eigenvalues_pos i0, fun i => hi0 i (Finset.mem_univ i)⟩
  refine ⟨δ, hδ, fun δ' hδ' => ?_⟩
  have e : A - (δ' : ℂ) • (1 : Matrix n n ℂ) = conjStarAlgAut ℂ _ hH.eigenvectorUnitary
      (diagonal (fun i => ((hH.eigenvalues i - δ' : ℝ) : ℂ))) := by
    have d : diagonal (fun i => ((hH.eigenvalues i - δ' : ℝ) : ℂ)) =
        diagonal (RCLike.ofReal ∘ hH.eigenvalues) - (δ' : ℂ) • (1 : Matrix n n ℂ) := by
      ext i j; by_cases h : i = j <;> simp [diagonal, one_apply, h]
    conv_lhs => rw [hH.spectral_theorem]
    rw [d, map_sub, map_smul, map_one]
  rw [e, conjStarAlgAut_apply, isUnit_coe.posSemidef_star_right_conjugate_iff]
  exact PosSemidef.diagonal fun i =>
    Complex.zero_le_real.2 (sub_nonneg.2 (hδ'.trans (hle i)))

/- English proof (translation)
Use `choose d hd h using fun τ : Ψ => posSemidef_sub_smul_one (hZ τ)`. Break down `isEmpty_or_nonempty Ψ with hΨ | hΨ` into its components or cases. Conclude with `⟨1, one_pos, fun τ => (IsEmpty.false τ).elim⟩`. Take `⟨τ0, -, hτ0⟩` from `Finset.exists_min_image Finset.univ d Finset.univ_nonempty`. Conclude with `⟨d τ0, hd τ0, fun τ => h τ _ (hτ0 τ (Finset.mem_univ τ))⟩`.
-/
theorem exists_pos_mem_HnGe {N : ℕ} {E : Type} [Field E] (Ψ : Finset (E →+* ℂ))
    {Z : GlobalTheory.SW.CM Ψ N N} (hZ : Z ∈ GlobalTheory.SW.Hn Ψ N) :
    ∃ δ : ℝ, (0 : ℝ) < δ ∧ Z ∈ GlobalTheory.SW.HnGe Ψ N δ := by
  choose d hd h using fun τ : Ψ => posSemidef_sub_smul_one (hZ τ)
  rcases isEmpty_or_nonempty Ψ with hΨ | hΨ
  · exact ⟨1, one_pos, fun τ => (IsEmpty.false τ).elim⟩
  · obtain ⟨τ0, -, hτ0⟩ := Finset.exists_min_image Finset.univ d Finset.univ_nonempty
    exact ⟨d τ0, hd τ0, fun τ => h τ _ (hτ0 τ (Finset.mem_univ τ))⟩

/- English proof (translation)
Introduce `Ψ _ hZ` and use `exists_pos_mem_HnGe Ψ hZ`.
-/
theorem main : ∀ {N : ℕ} {E : Type} [inst : Field E] (Ψ : Finset (E →+* ℂ)) {Z : GlobalTheory.SW.CM Ψ N N},
    Z ∈ GlobalTheory.SW.Hn Ψ N → ∃ (δ : ℝ), (0 : ℝ) < δ ∧ Z ∈ GlobalTheory.SW.HnGe Ψ N δ :=
  fun Ψ _ hZ => exists_pos_mem_HnGe Ψ hZ

end GlobalTheory.PosSemidefShiftByScalar
