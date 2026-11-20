import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds

open scoped InnerProductSpace
open ReciprocityTheory.ChartRestriction.DS (casimirK IsGlRep IsInfUnitary adjSign)

namespace PositivityTheory.CW.EigenOrthogonalForm

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}

/- English proof (translation)
Unfold `casimirK`. Simplify using `only [LinearMap.sum_apply, Module.End.mul_apply, sum_inner, inner_sum]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_` and prove the remaining obligations. Establish `hab : ε b = ε a` using `(Finset.mem_filter.1 hb).2`. Rewrite using `[hu a b, hu b a]`.

Simplify using `[adjSign, hab]`.
-/
theorem cas_symm (hu : IsInfUnitary ε E) (x y : V) :
    ⟪casimirK ε E x, y⟫_ℂ = ⟪x, casimirK ε E y⟫_ℂ := by
  unfold casimirK
  simp only [LinearMap.sum_apply, Module.End.mul_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
  have hab : ε b = ε a := (Finset.mem_filter.1 hb).2
  rw [hu a b, hu b a]
  simp [adjSign, hab]

/- English proof (translation)
Establish `h` using `cas_symm hu v y`. Rewrite `h` using `[hv, hy, inner_smul_left, inner_smul_right, Complex.conj_ofReal]`. Establish `h' : ((μ : ℂ) - μ') * ⟪v, y⟫_ℂ = 0` using `by rw [sub_mul, h, sub_self]`. Break down `mul_eq_zero.1 h' with h0 | h0` into its components or cases. Conclude with `absurd (by exact_mod_cast sub_eq_zero.1 h0) hne`.

Conclude with `h0`.
-/
theorem inner_eq_zero_of_eig (hu : IsInfUnitary ε E) {μ μ' : ℝ} (hne : μ ≠ μ') {v y : V}
    (hv : casimirK ε E v = (μ : ℂ) • v) (hy : casimirK ε E y = (μ' : ℂ) • y) : ⟪v, y⟫_ℂ = 0 := by
  have h := cas_symm hu v y
  rw [hv, hy, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h
  have h' : ((μ : ℂ) - μ') * ⟪v, y⟫_ℂ = 0 := by rw [sub_mul, h, sub_self]
  rcases mul_eq_zero.1 h' with h0 | h0
  · exact absurd (by exact_mod_cast sub_eq_zero.1 h0) hne
  · exact h0

/- English proof (translation)
Establish `h` using `hB v y`. Rewrite `h` using `[hv, hy]`. Simplify using `only [map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, Complex.conj_ofReal, RingHom.id_apply] at h`. Establish `h2 : ((μ : ℂ) - μ') * B v y = 0` using `by rw [sub_mul, h, sub_self]`. Break down `mul_eq_zero.1 h2 with h3 | h3` into its components or cases.

Conclude with `absurd (by exact_mod_cast sub_eq_zero.1 h3) hne`. Conclude with `h3`.
-/
theorem B_eq_zero (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hB : ∀ v y, B (casimirK ε E v) y = B v (casimirK ε E y))
    {μ μ' : ℝ} (hne : μ ≠ μ') {v y : V}
    (hv : casimirK ε E v = (μ : ℂ) • v) (hy : casimirK ε E y = (μ' : ℂ) • y) : B v y = 0 := by
  have h := hB v y
  rw [hv, hy] at h
  simp only [map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, Complex.conj_ofReal,
    RingHom.id_apply] at h
  have h2 : ((μ : ℂ) - μ') * B v y = 0 := by rw [sub_mul, h, sub_self]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd (by exact_mod_cast sub_eq_zero.1 h3) hne
  · exact h3

end PositivityTheory.CW.EigenOrthogonalForm

namespace PositivityTheory.CW

open EigenOrthogonalForm in
/- English proof (translation)
Introduce `n ε V _ _ E _ _ hM Q hQ η`. Set `S : Submodule ℂ V` to `{ carrier := {a | ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖⟪a, y⟫_ℂ‖ ≤ C * Q y} add_mem' := by`. Introduce and unpack `a b ⟨C₁, h₁, ha⟩ ⟨C₂, h₂, hb⟩`. Use `⟨C₁ + C₂, add_nonneg h₁ h₂, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[inner_add_left, add_mul]`.

Conclude with `(norm_add_le _ _).trans (add_le_add (ha y) (hb y))`. Use the proof step `zero_mem' := ⟨0, le_rfl, fun y => by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c a ⟨C, h, ha⟩`. Use `⟨‖c‖ * C, mul_nonneg (norm_nonneg _) h, fun y => ?_⟩` and prove the remaining obligations.

Rewrite using `[inner_smul_left, norm_mul, RCLike.norm_conj, mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left (ha y) (norm_nonneg _) }`. It suffices to establish `hS : S = ⊤ by`. Establish `hη : η ∈ S` using `hS ▸ Submodule.mem_top`. Conclude with `hη`.

Rewrite using `[eq_top_iff, ← hM.span, Submodule.span_le]`. Introduce and unpack `w ⟨μ, hw⟩`. Set `W : Submodule ℂ V` to `Module.End.eigenspace (casimirK ε E) (μ : ℂ)`. Establish `hWmem : ∀ v, v ∈ W ↔ casimirK ε E v = (μ : ℂ) • v` using `fun v => Module.End.mem_eigenspace_iff`. Use `haveI : FiniteDimensional ℂ W := by haveI := hM.fin μ`.

Establish `hle : W ≤ Submodule.span ℂ {v | ∃ μ' ≤ μ, Eig ε E μ' v}` using `fun v hv => Submodule.subset_span ⟨μ, le_rfl, (hWmem v).1 hv⟩`. Conclude with `Submodule.finiteDimensional_of_le hle`. Set `P : (V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) → Prop` to `fun B => (∀ v y, B (casimirK ε E v) y = B v (casimirK ε E y)) ∧ ∀ v y, ‖B v y‖ ≤ Q v * Q y`. Set `G : Set (Module.Dual ℂ W)` to `{g | ∃ B, P B ∧ ∃ v ∈ W, g = (B v).comp W.subtype}`. Establish `hspan : Submodule.span ℂ G = ⊤`.

Establish `hco : (Submodule.span ℂ G).dualCoannihilator = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `y hy`. Rewrite using `[Submodule.mem_bot]`. Assume the negation of the conclusion as `hne`.

Establish `hy0 : (y : V) ≠ 0` using `fun h => hne (Subtype.ext h)`. Take `⟨B, hB1, hB2, hB3⟩` from `hQ y hy0`. Establish `hg : (B y).comp W.subtype ∈ Submodule.span ℂ G` using `Submodule.subset_span ⟨B, ⟨hB1, hB2⟩, y, y.2, rfl⟩`. Conclude with `hB3 ((Submodule.mem_dualCoannihilator _).1 hy _ hg)`. Rewrite using `[← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ G), hco, Submodule.dualAnnihilator_bot]`.

Establish `hl : (innerₛₗ ℂ w).comp W.subtype ∈ Submodule.span ℂ G` using `hspan ▸ Submodule.mem_top`. Take `⟨m, f, g, hfg⟩` from `Submodule.mem_span_set'.1 hl`. Use `choose B hB v hv hgv using fun i => (g i).2`. Establish `hid : innerₛₗ ℂ w = ∑ i, f i • B i (v i)`. Use `LinearMap.ext_on hM.span ?_` and prove the remaining obligations.

Introduce and unpack `y ⟨lam, hy⟩`. Distinguish the cases in `hμ : lam = μ`. Substitute `hμ` using the available equality. Establish `hyW : y ∈ W` using `(hWmem y).2 hy`. Use `LinearMap.congr_fun hfg ⟨y, hyW⟩` as an intermediate fact.

Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, hgv, LinearMap.comp_apply, Submodule.subtype_apply] at this`. Rewrite using `[← this, LinearMap.sum_apply]`. Simplify using `only [LinearMap.smul_apply]`. Establish `h0 : ⟪w, y⟫_ℂ = 0` using `inner_eq_zero_of_eig hM.uni (Ne.symm hμ) hw hy`. Establish `h1 : ∀ i, B i (v i) y = 0` using `fun i => B_eq_zero (B i) (hB i).1 (Ne.symm hμ) ((hWmem _).1 (hv i)) hy`.

Rewrite using `[LinearMap.sum_apply, innerₛₗ_apply_apply, h0]`. Simplify using `[h1]`. Use `show ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖⟪w, y⟫_ℂ‖ ≤ C * Q y`. Use `⟨∑ i, ‖f i‖ * Q (v i), Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (apply_nonneg Q _), fun y => ?_⟩` and prove the remaining obligations. Establish `hwy : ⟪w, y⟫_ℂ = ∑ i, f i * B i (v i) y`.

Establish `h` using `LinearMap.congr_fun hid y`. Rewrite `h` using `[innerₛₗ_apply_apply, LinearMap.sum_apply]`. Rewrite using `[h]`. Simplify using `only [LinearMap.smul_apply, smul_eq_mul]`. Rewrite using `[hwy, Finset.sum_mul]`.

Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left ((hB i).2 _ _) (norm_nonneg _)`.
-/
theorem e2c : CasimirPairingBound := by
  intro n ε V _ _ E _ _ hM Q hQ η
  let S : Submodule ℂ V :=
    { carrier := {a | ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖⟪a, y⟫_ℂ‖ ≤ C * Q y}
      add_mem' := by
        rintro a b ⟨C₁, h₁, ha⟩ ⟨C₂, h₂, hb⟩
        refine ⟨C₁ + C₂, add_nonneg h₁ h₂, fun y => ?_⟩
        rw [inner_add_left, add_mul]
        exact (norm_add_le _ _).trans (add_le_add (ha y) (hb y))
      zero_mem' := ⟨0, le_rfl, fun y => by simp⟩
      smul_mem' := by
        rintro c a ⟨C, h, ha⟩
        refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg _) h, fun y => ?_⟩
        rw [inner_smul_left, norm_mul, RCLike.norm_conj, mul_assoc]
        exact mul_le_mul_of_nonneg_left (ha y) (norm_nonneg _) }
  suffices hS : S = ⊤ by
    have hη : η ∈ S := hS ▸ Submodule.mem_top
    exact hη
  rw [eq_top_iff, ← hM.span, Submodule.span_le]
  rintro w ⟨μ, hw⟩
  let W : Submodule ℂ V := Module.End.eigenspace (casimirK ε E) (μ : ℂ)
  have hWmem : ∀ v, v ∈ W ↔ casimirK ε E v = (μ : ℂ) • v := fun v => Module.End.mem_eigenspace_iff
  haveI : FiniteDimensional ℂ W := by
    haveI := hM.fin μ
    have hle : W ≤ Submodule.span ℂ {v | ∃ μ' ≤ μ, Eig ε E μ' v} :=
      fun v hv => Submodule.subset_span ⟨μ, le_rfl, (hWmem v).1 hv⟩
    exact Submodule.finiteDimensional_of_le hle
  let P : (V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) → Prop := fun B =>
    (∀ v y, B (casimirK ε E v) y = B v (casimirK ε E y)) ∧ ∀ v y, ‖B v y‖ ≤ Q v * Q y
  let G : Set (Module.Dual ℂ W) := {g | ∃ B, P B ∧ ∃ v ∈ W, g = (B v).comp W.subtype}
  have hspan : Submodule.span ℂ G = ⊤ := by
    have hco : (Submodule.span ℂ G).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rw [Submodule.mem_bot]
      by_contra hne
      have hy0 : (y : V) ≠ 0 := fun h => hne (Subtype.ext h)
      obtain ⟨B, hB1, hB2, hB3⟩ := hQ y hy0
      have hg : (B y).comp W.subtype ∈ Submodule.span ℂ G :=
        Submodule.subset_span ⟨B, ⟨hB1, hB2⟩, y, y.2, rfl⟩
      exact hB3 ((Submodule.mem_dualCoannihilator _).1 hy _ hg)
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ G), hco,
      Submodule.dualAnnihilator_bot]
  have hl : (innerₛₗ ℂ w).comp W.subtype ∈ Submodule.span ℂ G := hspan ▸ Submodule.mem_top
  obtain ⟨m, f, g, hfg⟩ := Submodule.mem_span_set'.1 hl
  choose B hB v hv hgv using fun i => (g i).2
  have hid : innerₛₗ ℂ w = ∑ i, f i • B i (v i) := by
    refine LinearMap.ext_on hM.span ?_
    rintro y ⟨lam, hy⟩
    by_cases hμ : lam = μ
    · subst hμ
      have hyW : y ∈ W := (hWmem y).2 hy
      have := LinearMap.congr_fun hfg ⟨y, hyW⟩
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, hgv, LinearMap.comp_apply,
        Submodule.subtype_apply] at this
      rw [← this, LinearMap.sum_apply]
      simp only [LinearMap.smul_apply]
    · have h0 : ⟪w, y⟫_ℂ = 0 := inner_eq_zero_of_eig hM.uni (Ne.symm hμ) hw hy
      have h1 : ∀ i, B i (v i) y = 0 := fun i =>
        B_eq_zero (B i) (hB i).1 (Ne.symm hμ) ((hWmem _).1 (hv i)) hy
      rw [LinearMap.sum_apply, innerₛₗ_apply_apply, h0]
      simp [h1]
  show ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖⟪w, y⟫_ℂ‖ ≤ C * Q y
  refine ⟨∑ i, ‖f i‖ * Q (v i),
    Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (apply_nonneg Q _), fun y => ?_⟩
  have hwy : ⟪w, y⟫_ℂ = ∑ i, f i * B i (v i) y := by
    have h := LinearMap.congr_fun hid y
    rw [innerₛₗ_apply_apply, LinearMap.sum_apply] at h
    rw [h]
    simp only [LinearMap.smul_apply, smul_eq_mul]
  rw [hwy, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left ((hB i).2 _ _) (norm_nonneg _)

end PositivityTheory.CW
