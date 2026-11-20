import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `x₀ hx₀`. Establish `hK : IsCompact (Metric.sphere (0 : n → ℝ) 1)` using `isCompact_sphere _ _`. Establish `hcont : Continuous (fun p : X × (n → ℝ) => dotProduct (star p.2) ((M p.1).mulVec p.2))` using `(continuous_snd.star).dotProduct ((hc.comp continuous_fst).matrix_mulVec continuous_snd)`. Establish `hev : ∀ᶠ x in nhds x₀, ∀ v ∈ Metric.sphere (0 : n → ℝ) 1, 0 < dotProduct (star v) ((M x).mulVec v)`.

Apply `hK.eventually_forall_of_forall_eventually` to reduce the goal to its premises. Introduce `v hv`. Establish `hv0 : v ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hv`.

Establish `hpos` using `(Matrix.posDef_iff_dotProduct_mulVec.mp hx₀).2 hv0`. Conclude with `(isOpen_lt continuous_const hcont).mem_nhds hpos`. Use `filter_upwards [hev] with x hx`. Use `Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hs x, fun v hv => ?_⟩` and prove the remaining obligations. Establish `hn : 0 < ‖v‖` using `norm_pos_iff.mpr hv`.

Establish `h1` using `hx (‖v‖⁻¹ • v) (by`. Rewrite using `[mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne'])`. Simplify using `only [star_trivial, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h1 ⊢`. Establish `hi : 0 < ‖v‖⁻¹` using `inv_pos.mpr hn`. Conclude with `(mul_pos_iff_of_pos_left hi).mp ((mul_pos_iff_of_pos_left hi).mp h1)`.
-/
theorem isOpen_posDef_of_continuous {X n : Type} [TopologicalSpace X] [Fintype n]
    (M : X → Matrix n n ℝ) (hc : Continuous M) (hs : ∀ x, (M x).IsHermitian) :
    IsOpen {x | (M x).PosDef} := by
  rw [isOpen_iff_mem_nhds]
  intro x₀ hx₀
  have hK : IsCompact (Metric.sphere (0 : n → ℝ) 1) := isCompact_sphere _ _
  have hcont : Continuous (fun p : X × (n → ℝ) => dotProduct (star p.2) ((M p.1).mulVec p.2)) :=
    (continuous_snd.star).dotProduct ((hc.comp continuous_fst).matrix_mulVec continuous_snd)
  have hev : ∀ᶠ x in nhds x₀, ∀ v ∈ Metric.sphere (0 : n → ℝ) 1,
      0 < dotProduct (star v) ((M x).mulVec v) := by
    apply hK.eventually_forall_of_forall_eventually
    intro v hv
    have hv0 : v ≠ 0 := by
      rintro rfl
      simp at hv
    have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hx₀).2 hv0
    exact (isOpen_lt continuous_const hcont).mem_nhds hpos
  filter_upwards [hev] with x hx
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hs x, fun v hv => ?_⟩
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have h1 := hx (‖v‖⁻¹ • v) (by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne'])
  simp only [star_trivial, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h1 ⊢
  have hi : 0 < ‖v‖⁻¹ := inv_pos.mpr hn
  exact (mul_pos_iff_of_pos_left hi).mp ((mul_pos_iff_of_pos_left hi).mp h1)

/- English proof (translation)
Rewrite using `[Sym2.card, Fintype.card_fin, Nat.choose_two_right, Nat.add_sub_cancel, mul_comm]`.
-/
theorem card_sym2_fin (h : ℕ) : Fintype.card (Sym2 (Fin h)) = h * (h + 1) / 2 := by
  rw [Sym2.card, Fintype.card_fin, Nat.choose_two_right, Nat.add_sub_cancel, mul_comm]

/- English proof (translation)
Introduce `h`. Set `e : Sym2 (Fin h) ≃ Fin (h * (h + 1) / 2)` to `Fintype.equivFinOfCardEq (card_sym2_fin h)`. Set `τ : (Fin (h * (h + 1) / 2) → ℂ) → Matrix (Fin h) (Fin h) ℂ` to `fun b => Matrix.of fun i j => b (e s(i, j))`. Establish `hτ : ∀ b i j, τ b i j = b (e s(i, j))` using `fun _ _ _ => rfl`. Establish `hsymm : ∀ b, (τ b).IsSymm`.

Introduce `b`. Use extensionality with `i j`. Rewrite using `[Matrix.transpose_apply, hτ, hτ, Sym2.eq_swap]`. Use `⟨{b | ((τ b).map Complex.im).PosDef}, τ, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Apply `isOpen_posDef_of_continuous (fun b => (τ b).map Complex.im)` to reduce the goal to its premises.

Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Conclude with `Complex.continuous_im.comp (continuous_apply (e s(i, j)))`. Introduce `b`. Use extensionality with `i j`. Simplify using `only [Matrix.conjTranspose_apply, star_trivial, Matrix.map_apply, hτ]`.

Rewrite using `[Sym2.eq_swap]`. Introduce `x hx y hy a b ha hb hab`. Establish `key : (τ (a • x + b • y)).map Complex.im = a • (τ x).map Complex.im + b • (τ y).map Complex.im`. Use extensionality with `i j`. Simplify using `[hτ]`.

Express the relevant statement in the definitionally equal form `((τ (a • x + b • y)).map Complex.im).PosDef`. Rewrite using `[key]`. Break down `ha.eq_or_lt with rfl | ha'` into its components or cases. Establish `: b = 1` using `by simpa using hab`. Substitute `this` using the available equality.

Simplify using `using hy`. Conclude with `(Matrix.PosDef.smul hx ha').add_posSemidef (Matrix.PosSemidef.smul (Matrix.PosDef.posSemidef hy) hb)`. Introduce `i j`. Conclude with `differentiable_apply (𝕜 := ℂ) (e s(i, j))`. Introduce `b hb`.

Conclude with `⟨hsymm b, hb⟩`. Introduce `t ht hp`. Set `f : Sym2 (Fin h) → ℂ` to `Sym2.lift ⟨fun i j => t i j, fun i j => (ht.apply i j).symm⟩`. Establish `hf : τ (fun k => f (e.symm k)) = t`. Use extensionality with `i j`.

Express the relevant statement in the definitionally equal form `f (e.symm (e s(i, j))) = t i j`. Rewrite using `[Equiv.symm_apply_apply]`. Both sides reduce to the same expression. Use `⟨fun k => f (e.symm k), ⟨?_, hf⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((τ (fun k => f (e.symm k))).map Complex.im).PosDef`.

Rewrite using `[hf]`. Conclude with `hp`. Introduce and unpack `b ⟨-, hb⟩`. Use function extensionality and compare the values at `k`. Take `⟨z, rfl⟩` from `e.surjective k`.

Proceed by induction on `z using Sym2.ind with`. Consider the case `_ i j`. Rewrite using `[Equiv.symm_apply_apply]`. Conclude with `congrFun (congrFun hb i) j`.
-/
theorem exists_siegel_coordinates :
    ∀ h : ℕ, ∃ (B : Set (Fin (h * (h + 1) / 2) → ℂ)) (τ : (Fin (h * (h + 1) / 2) → ℂ) → Matrix (Fin h) (Fin h) ℂ), IsOpen B ∧ Convex ℝ B ∧ (∀ i j, Differentiable ℂ (fun b => τ b i j)) ∧ (∀ b ∈ B, (τ b).IsSymm ∧ ((τ b).map Complex.im).PosDef) ∧ ∀ t : Matrix (Fin h) (Fin h) ℂ, t.IsSymm → (t.map Complex.im).PosDef → ∃! b, b ∈ B ∧ τ b = t := by
  intro h
  let e : Sym2 (Fin h) ≃ Fin (h * (h + 1) / 2) := Fintype.equivFinOfCardEq (card_sym2_fin h)
  let τ : (Fin (h * (h + 1) / 2) → ℂ) → Matrix (Fin h) (Fin h) ℂ :=
    fun b => Matrix.of fun i j => b (e s(i, j))
  have hτ : ∀ b i j, τ b i j = b (e s(i, j)) := fun _ _ _ => rfl
  have hsymm : ∀ b, (τ b).IsSymm := by
    intro b
    ext i j
    rw [Matrix.transpose_apply, hτ, hτ, Sym2.eq_swap]
  refine ⟨{b | ((τ b).map Complex.im).PosDef}, τ, ?_, ?_, ?_, ?_, ?_⟩
  · apply isOpen_posDef_of_continuous (fun b => (τ b).map Complex.im)
    · refine continuous_matrix fun i j => ?_
      exact Complex.continuous_im.comp (continuous_apply (e s(i, j)))
    · intro b
      ext i j
      simp only [Matrix.conjTranspose_apply, star_trivial, Matrix.map_apply, hτ]
      rw [Sym2.eq_swap]
  · intro x hx y hy a b ha hb hab
    have key : (τ (a • x + b • y)).map Complex.im
        = a • (τ x).map Complex.im + b • (τ y).map Complex.im := by
      ext i j
      simp [hτ]
    change ((τ (a • x + b • y)).map Complex.im).PosDef
    rw [key]
    rcases ha.eq_or_lt with rfl | ha'
    · have : b = 1 := by simpa using hab
      subst this
      simpa using hy
    · exact (Matrix.PosDef.smul hx ha').add_posSemidef
        (Matrix.PosSemidef.smul (Matrix.PosDef.posSemidef hy) hb)
  · intro i j
    exact differentiable_apply (𝕜 := ℂ) (e s(i, j))
  · intro b hb
    exact ⟨hsymm b, hb⟩
  · intro t ht hp
    let f : Sym2 (Fin h) → ℂ := Sym2.lift ⟨fun i j => t i j, fun i j => (ht.apply i j).symm⟩
    have hf : τ (fun k => f (e.symm k)) = t := by
      ext i j
      change f (e.symm (e s(i, j))) = t i j
      rw [Equiv.symm_apply_apply]
      rfl
    refine ⟨fun k => f (e.symm k), ⟨?_, hf⟩, ?_⟩
    · change ((τ (fun k => f (e.symm k))).map Complex.im).PosDef
      rw [hf]; exact hp
    · rintro b ⟨-, hb⟩
      funext k
      obtain ⟨z, rfl⟩ := e.surjective k
      induction z using Sym2.ind with
      | _ i j =>
        rw [Equiv.symm_apply_apply]
        exact congrFun (congrFun hb i) j

end GlobalTheory
