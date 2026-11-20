import Mathlib
open MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory.SchurOrthOnSubgroup

/- English proof (translation)
Rewrite using `[← integral_indicator hΩ, ← integral_indicator hΩ]`. Establish `: (Ω : Set G).indicator (fun g => f (h * g)) = fun g => (Ω : Set G).indicator f (h * g)`. Use function extensionality and compare the values at `g`. Distinguish the cases in `hg : g ∈ Ω`. Establish `hg' : h * g ∈ Ω` using `Ω.mul_mem hh hg`.

Simplify using `[Set.indicator_of_mem, hg, hg']`. Establish `hg' : h * g ∉ Ω` using `fun H => hg ((Ω.mul_mem_cancel_left hh).1 H)`. Simplify using `[Set.indicator_of_notMem, hg, hg']`. Rewrite using `[this, integral_mul_left_eq_self]`.
-/
theorem setIntegral_subgroup_mul_left {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (ν : Measure G) [ν.IsMulLeftInvariant] (Ω : Subgroup G) (hΩ : MeasurableSet (Ω : Set G))
    (f : G → ℂ) {h : G} (hh : h ∈ Ω) :
    ∫ g in (Ω : Set G), f (h * g) ∂ν = ∫ g in (Ω : Set G), f g ∂ν := by
  rw [← integral_indicator hΩ, ← integral_indicator hΩ]
  have : (Ω : Set G).indicator (fun g => f (h * g)) = fun g => (Ω : Set G).indicator f (h * g) := by
    funext g
    by_cases hg : g ∈ Ω
    · have hg' : h * g ∈ Ω := Ω.mul_mem hh hg
      simp [Set.indicator_of_mem, hg, hg']
    · have hg' : h * g ∉ Ω := fun H => hg ((Ω.mul_mem_cancel_left hh).1 H)
      simp [Set.indicator_of_notMem, hg, hg']
  rw [this, integral_mul_left_eq_self]

variable {G : Type} [Group G] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/- English proof (translation)
Use `show (ρ g * ρ g⁻¹) v = v`. Rewrite using `[← map_mul, mul_inv_cancel, map_one]`. Both sides reduce to the same expression.
-/
theorem rep_apply_inv_apply (ρ : G →* Module.End ℂ W) (g : G) (v : W) : ρ g (ρ g⁻¹ v) = v := by
  show (ρ g * ρ g⁻¹) v = v
  rw [← map_mul, mul_inv_cancel, map_one]; rfl

/- English proof (translation)
Rewrite using `[← hU g (ρ g⁻¹ x) y, rep_apply_inv_apply]`.
-/
theorem inner_rep_inv (ρ : G →* Module.End ℂ W) (hU : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (g : G) (x y : W) : ⟪ρ g⁻¹ x, y⟫_ℂ = ⟪x, ρ g y⟫_ℂ := by
  rw [← hU g (ρ g⁻¹ x) y, rep_apply_inv_apply]

/- English proof (translation)
Rewrite using `[← hU g x (ρ g⁻¹ y), rep_apply_inv_apply]`.
-/
theorem inner_rep_inv' (ρ : G →* Module.End ℂ W) (hU : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (g : G) (x y : W) : ⟪x, ρ g⁻¹ y⟫_ℂ = ⟪ρ g x, y⟫_ℂ := by
  rw [← hU g x (ρ g⁻¹ y), rep_apply_inv_apply]

/- English proof (translation)
Rewrite using `[@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, hU]`.
-/
theorem norm_rep (ρ : G →* Module.End ℂ W) (hU : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (g : G) (v : W) : ‖ρ g v‖ = ‖v‖ := by
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, hU]

end GlobalTheory.SchurOrthOnSubgroup

namespace GlobalTheory.SchurOrthOnSubgroup

/- English proof (translation)
Use `set F : W → W → G → ℂ := fun y y' g => star ⟪a, ρ g⁻¹ y⟫_ℂ * ⟪a', ρ g⁻¹ y'⟫_ℂ with hF`. Establish `hfin : ν (Ω : Set G) < ⊤` using `by rw [hν]; exact ENNReal.one_lt_top`. Establish `hint : ∀ y y', IntegrableOn (F y y') Ω ν`. Introduce `y y'`. Establish `hmeas : Measurable (F y y')`.

Establish `h1 : Measurable fun g : G => ⟪a, ρ g⁻¹ y⟫_ℂ` using `(hM a y).comp measurable_inv`. Establish `h2 : Measurable fun g : G => ⟪a', ρ g⁻¹ y'⟫_ℂ` using `(hM a' y').comp measurable_inv`. Conclude with `(continuous_star.measurable.comp h1).mul h2`. Use `Integrable.mono' (g := fun _ => (‖a‖ * ‖y‖) * (‖a'‖ * ‖y'‖)) ?_ hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Conclude with `integrableOn_const hfin.ne`.

Simplify using `only [hF, norm_mul, norm_star] gcongr`. Conclude with `(norm_inner_le_norm _ _).trans (by rw [norm_rep ρ hU])`. Conclude with `(norm_inner_le_norm _ _).trans (by rw [norm_rep ρ hU])`. Use `⟨hint x x', ?_⟩` and prove the remaining obligations. Use `set B : W → W → ℂ := fun y y' => ∫ g in (Ω : Set G), F y y' g ∂ν with hB`.

Set `b` to `stdOrthonormalBasis ℂ W`. Establish `hBadd : ∀ y y1 y2, B y (y1 + y2) = B y y1 + B y y2`. Introduce `y y1 y2`. Simplify using `only [hB]`. Rewrite using `[← integral_add (hint y y1) (hint y y2)]`.

Use `congr 1`. Use function extensionality and compare the values at `g`. Simplify using `only [hF, map_add, inner_add_right, mul_add]`. Establish `hBsmul : ∀ y (c : ℂ) y', B y (c • y') = c * B y y'`. Introduce `y c y'`.

Simplify using `only [hB]`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `g`. Simplify using `only [hF, map_smul, inner_smul_right]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hBexp : ∀ y y', B y y' = ∑ i, ⟪y, b i⟫_ℂ * B (b i) y'`. Introduce `y y'`. Simplify using `only [hB]`. Repeatedly rewrite using `[← integral_const_mul]`.

Rewrite using `[← integral_finset_sum _ (fun i _ => (hint (b i) y').const_mul _)]`. Use `congr 1`. Use function extensionality and compare the values at `g`. Simplify using `only [hF]`. Establish `hs : ∀ z, star ⟪a, ρ g⁻¹ z⟫_ℂ = ⟪z, ρ g a⟫_ℂ`.

Introduce `z`. Rewrite using `[inner_rep_inv' ρ hU]`. Conclude with `inner_conj_symm _ _`. Repeatedly rewrite using `[hs, ← mul_assoc, ← Finset.sum_mul]`. Rewrite using `[b.sum_inner_mul_inner]`.

Establish `hBinv : ∀ h ∈ Ω, ∀ y y', B (ρ h y) (ρ h y') = B y y'`. Introduce `h hh y y'`. Simplify using `only [hB]`. Rewrite using `[← setIntegral_subgroup_mul_left ν Ω hΩ (F y y') (Ω.inv_mem hh)]`. Use `congr 1`.

Use function extensionality and compare the values at `g`. Establish `hg : ∀ z, ρ g⁻¹ (ρ h z) = ρ (h⁻¹ * g)⁻¹ z`. Introduce `z`. Rewrite using `[mul_inv_rev, inv_inv, map_mul]`. Both sides reduce to the same expression.

Simplify using `only [hF, hg]`. Set `T : W →ₗ[ℂ] W` to `{ toFun := fun y' => ∑ i, B (b i) y' • b i map_add' := by`. Introduce `y1 y2`. Simplify using `only [hBadd, add_smul, Finset.sum_add_distrib]`. Use the proof step `map_smul' := by`.

Introduce `c y'`. Simplify using `only [hBsmul, mul_smul, RingHom.id_apply, Finset.smul_sum] }`. Establish `hT : ∀ y y', ⟪y, T y'⟫_ℂ = B y y'`. Introduce `y y'`. Rewrite using `[hBexp y y']`.

Simplify using `only [T, LinearMap.coe_mk, AddHom.coe_mk, inner_sum, inner_smul_right]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Expand and normalize the polynomial expressions, which then agree. Establish `hcomm : ∀ h ∈ Ω, ∀ v, T (ρ h v) = ρ h (T v)`.

Introduce `h hh v`. Apply `ext_inner_left ℂ` to reduce the goal to its premises. Introduce `y`. Rewrite using `[hT, ← inner_rep_inv ρ hU, hT]`. Use `conv_lhs => rw [← rep_apply_inv_apply ρ h y]`.

Conclude with `hBinv h hh _ _`. Establish `hsum : ∑ i, B (b i) (b i) = ⟪a', a⟫_ℂ`. Simplify using `only [hB]`. Rewrite using `[← integral_finset_sum _ (fun i _ => hint (b i) (b i))]`. Establish `: ∀ g, ∑ i, F (b i) (b i) g = ⟪a', a⟫_ℂ`.

Introduce `g`. Simplify using `only [hF]`. Establish `hs : ∀ z, star ⟪a, ρ g⁻¹ z⟫_ℂ = ⟪z, ρ g a⟫_ℂ`. Introduce `z`. Rewrite using `[inner_rep_inv' ρ hU]`.

Conclude with `inner_conj_symm _ _`. Repeatedly rewrite using `[hs, inner_rep_inv' ρ hU]`. Repeatedly rewrite using `[mul_comm (⟪b _, ρ g a⟫_ℂ)]`. Rewrite using `[b.sum_inner_mul_inner, hU]`. Repeatedly rewrite using `[this]`.

Rewrite using `[setIntegral_const, Measure.real, hν]`. Simplify using the standard rewrite rules. Break down `subsingleton_or_nontrivial W with hW | hW` into its components or cases. Establish `ha : a = 0` using `Subsingleton.elim _ _`. Simplify using `[Module.finrank_zero_of_subsingleton, ha]`.

Take `⟨c, hc⟩` from `Module.End.exists_eigenvalue (T : Module.End ℂ W)`. Establish `hU' : Module.End.eigenspace (T : Module.End ℂ W) c = ⊤`. Break down `hirr (Module.End.eigenspace (T : Module.End ℂ W) c) (by` into its components or cases. Introduce `g hg`. Introduce and unpack `_ ⟨v, hv, rfl⟩`.

Rewrite `hv` using `[SetLike.mem_coe, Module.End.mem_eigenspace_iff]`. Rewrite using `[Module.End.mem_eigenspace_iff, hcomm g hg, hv, map_smul]) with h0 | h0`. It suffices to derive a contradiction. Take `⟨v, hv⟩` from `hc.exists_hasEigenvector`. Establish `: v ∈ Module.End.eigenspace (T : Module.End ℂ W) c` using `hv.1`.

Rewrite `this` using `[h0, Submodule.mem_bot]`. Conclude with `hv.2 this`. Conclude with `h0`. Establish `hTc : ∀ v, T v = c • v` using `fun v => Module.End.mem_eigenspace_iff.1 (hU' ▸ Submodule.mem_top)`. Establish `hBc : ∀ y y', B y y' = c * ⟪y, y'⟫_ℂ`.

Introduce `y y'`. Rewrite using `[← hT, hTc, inner_smul_right]`. Establish `hnc : (Module.finrank ℂ W : ℂ) * c = ⟪a', a⟫_ℂ`. Rewrite using `[← hsum]`. Establish `h1 : ∀ i, ⟪b i, b i⟫_ℂ = 1` using `fun i => by`.

Simplify using `using orthonormal_iff_ite.1 b.orthonormal i i`. Simplify using `only [hBc, h1, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Use `show (Module.finrank ℂ W : ℂ) * B x x' = _`. Rewrite using `[hBc, ← mul_assoc, hnc]`.
-/
theorem schur_orthogonality {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
    (ν : Measure G) [ν.IsMulLeftInvariant] (Ω : Subgroup G) (hΩ : MeasurableSet (Ω : Set G))
    (hν : ν (Ω : Set G) = 1) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] (ρ : G →* Module.End ℂ W)
    (hU : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hM : ∀ x y : W, Measurable fun g => ⟪x, ρ g y⟫_ℂ)
    (hirr : ∀ U : Submodule ℂ W, (∀ g ∈ Ω, U.map (ρ g) ≤ U) → U = ⊥ ∨ U = ⊤)
    (a a' x x' : W) :
    IntegrableOn (fun g => star ⟪a, ρ g⁻¹ x⟫_ℂ * ⟪a', ρ g⁻¹ x'⟫_ℂ) Ω ν ∧
      (Module.finrank ℂ W : ℂ) * ∫ g in (Ω : Set G), star ⟪a, ρ g⁻¹ x⟫_ℂ * ⟪a', ρ g⁻¹ x'⟫_ℂ ∂ν
        = ⟪a', a⟫_ℂ * ⟪x, x'⟫_ℂ := by

  set F : W → W → G → ℂ := fun y y' g => star ⟪a, ρ g⁻¹ y⟫_ℂ * ⟪a', ρ g⁻¹ y'⟫_ℂ with hF
  have hfin : ν (Ω : Set G) < ⊤ := by rw [hν]; exact ENNReal.one_lt_top
  have hint : ∀ y y', IntegrableOn (F y y') Ω ν := by
    intro y y'
    have hmeas : Measurable (F y y') := by
      have h1 : Measurable fun g : G => ⟪a, ρ g⁻¹ y⟫_ℂ := (hM a y).comp measurable_inv
      have h2 : Measurable fun g : G => ⟪a', ρ g⁻¹ y'⟫_ℂ := (hM a' y').comp measurable_inv
      exact (continuous_star.measurable.comp h1).mul h2
    refine Integrable.mono' (g := fun _ => (‖a‖ * ‖y‖) * (‖a'‖ * ‖y'‖)) ?_
      hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
    · exact integrableOn_const hfin.ne
    · simp only [hF, norm_mul, norm_star]
      gcongr
      · exact (norm_inner_le_norm _ _).trans (by rw [norm_rep ρ hU])
      · exact (norm_inner_le_norm _ _).trans (by rw [norm_rep ρ hU])
  refine ⟨hint x x', ?_⟩

  set B : W → W → ℂ := fun y y' => ∫ g in (Ω : Set G), F y y' g ∂ν with hB
  let b := stdOrthonormalBasis ℂ W
  have hBadd : ∀ y y1 y2, B y (y1 + y2) = B y y1 + B y y2 := by
    intro y y1 y2
    simp only [hB]
    rw [← integral_add (hint y y1) (hint y y2)]
    congr 1; funext g
    simp only [hF, map_add, inner_add_right, mul_add]
  have hBsmul : ∀ y (c : ℂ) y', B y (c • y') = c * B y y' := by
    intro y c y'
    simp only [hB]
    rw [← integral_const_mul]
    congr 1; funext g
    simp only [hF, map_smul, inner_smul_right]; ring
  have hBexp : ∀ y y', B y y' = ∑ i, ⟪y, b i⟫_ℂ * B (b i) y' := by
    intro y y'
    simp only [hB]
    simp_rw [← integral_const_mul]
    rw [← integral_finset_sum _ (fun i _ => (hint (b i) y').const_mul _)]
    congr 1; funext g
    simp only [hF]
    have hs : ∀ z, star ⟪a, ρ g⁻¹ z⟫_ℂ = ⟪z, ρ g a⟫_ℂ := by
      intro z
      rw [inner_rep_inv' ρ hU]
      exact inner_conj_symm _ _
    simp_rw [hs, ← mul_assoc, ← Finset.sum_mul]
    rw [b.sum_inner_mul_inner]
  have hBinv : ∀ h ∈ Ω, ∀ y y', B (ρ h y) (ρ h y') = B y y' := by
    intro h hh y y'
    simp only [hB]
    rw [← setIntegral_subgroup_mul_left ν Ω hΩ (F y y') (Ω.inv_mem hh)]
    congr 1; funext g
    have hg : ∀ z, ρ g⁻¹ (ρ h z) = ρ (h⁻¹ * g)⁻¹ z := by
      intro z
      rw [mul_inv_rev, inv_inv, map_mul]; rfl
    simp only [hF, hg]

  let T : W →ₗ[ℂ] W :=
    { toFun := fun y' => ∑ i, B (b i) y' • b i
      map_add' := by
        intro y1 y2
        simp only [hBadd, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c y'
        simp only [hBsmul, mul_smul, RingHom.id_apply, Finset.smul_sum] }
  have hT : ∀ y y', ⟪y, T y'⟫_ℂ = B y y' := by
    intro y y'
    rw [hBexp y y']
    simp only [T, LinearMap.coe_mk, AddHom.coe_mk, inner_sum, inner_smul_right]
    congr 1; funext i; ring
  have hcomm : ∀ h ∈ Ω, ∀ v, T (ρ h v) = ρ h (T v) := by
    intro h hh v
    apply ext_inner_left ℂ
    intro y
    rw [hT, ← inner_rep_inv ρ hU, hT]
    conv_lhs => rw [← rep_apply_inv_apply ρ h y]
    exact hBinv h hh _ _
  have hsum : ∑ i, B (b i) (b i) = ⟪a', a⟫_ℂ := by
    simp only [hB]
    rw [← integral_finset_sum _ (fun i _ => hint (b i) (b i))]
    have : ∀ g, ∑ i, F (b i) (b i) g = ⟪a', a⟫_ℂ := by
      intro g
      simp only [hF]
      have hs : ∀ z, star ⟪a, ρ g⁻¹ z⟫_ℂ = ⟪z, ρ g a⟫_ℂ := by
        intro z
        rw [inner_rep_inv' ρ hU]
        exact inner_conj_symm _ _
      simp_rw [hs, inner_rep_inv' ρ hU]
      simp_rw [mul_comm (⟪b _, ρ g a⟫_ℂ)]
      rw [b.sum_inner_mul_inner, hU]
    simp_rw [this]
    rw [setIntegral_const, Measure.real, hν]
    simp
  rcases subsingleton_or_nontrivial W with hW | hW
  · have ha : a = 0 := Subsingleton.elim _ _
    simp [Module.finrank_zero_of_subsingleton, ha]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (T : Module.End ℂ W)
  have hU' : Module.End.eigenspace (T : Module.End ℂ W) c = ⊤ := by
    rcases hirr (Module.End.eigenspace (T : Module.End ℂ W) c) (by
      intro g hg
      rintro _ ⟨v, hv, rfl⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hv
      rw [Module.End.mem_eigenspace_iff, hcomm g hg, hv, map_smul]) with h0 | h0
    · exfalso
      obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
      have : v ∈ Module.End.eigenspace (T : Module.End ℂ W) c := hv.1
      rw [h0, Submodule.mem_bot] at this
      exact hv.2 this
    · exact h0
  have hTc : ∀ v, T v = c • v := fun v =>
    Module.End.mem_eigenspace_iff.1 (hU' ▸ Submodule.mem_top)
  have hBc : ∀ y y', B y y' = c * ⟪y, y'⟫_ℂ := by
    intro y y'
    rw [← hT, hTc, inner_smul_right]
  have hnc : (Module.finrank ℂ W : ℂ) * c = ⟪a', a⟫_ℂ := by
    rw [← hsum]
    have h1 : ∀ i, ⟪b i, b i⟫_ℂ = 1 := fun i => by
      simpa using orthonormal_iff_ite.1 b.orthonormal i i
    simp only [hBc, h1, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  show (Module.finrank ℂ W : ℂ) * B x x' = _
  rw [hBc, ← mul_assoc, hnc]

end GlobalTheory.SchurOrthOnSubgroup
