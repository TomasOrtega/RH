import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

noncomputable section

/- English proof (translation)
Use `haveI : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.injective.countable`. Use `haveI : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))`. Conclude with `Function.Injective.countable (f := fun g : GL (Fin r) E => (g : Matrix (Fin r) (Fin r) E)) fun _ _ h => Units.ext h`.
-/
theorem countable_GL_numberField {E : Type} [Field E] [NumberField E] (r : ℕ) :
    Countable (GL (Fin r) E) := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.injective.countable
  haveI : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))
  exact Function.Injective.countable
    (f := fun g : GL (Fin r) E => (g : Matrix (Fin r) (Fin r) E)) fun _ _ h => Units.ext h

/- English proof (translation)
Establish `h : Continuous fun z : Frame Ψ r => mat z τ` using `continuous_apply τ`. Conclude with `continuous_const.matrix_mul h`.
-/
theorem continuous_mat_lact {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ}
    (g : GL (Fin r) E) (τ : Ψ) :
    Continuous fun z : Frame Ψ r => mat (lact g z) τ := by
  have h : Continuous fun z : Frame Ψ r => mat z τ := continuous_apply τ
  exact continuous_const.matrix_mul h

/- English proof (translation)
Introduce `hW hne hWdom hmove`. Set `C : GL (Fin r) E → Set (Frame X.Ψ r)` to `fun g => {z | ∀ τ : X.Ψ, ∀ p q : Fin r, q < p → ((mat (lact (g * a) z) τ).adjugate * mat (lact c z) τ) p q = 0}`. Establish `hC : ∀ g, IsClosed (C g)`. Introduce `g`. Simplify using `only [C, Set.setOf_forall]`.

Use `isClosed_iInter fun τ => isClosed_iInter fun p => isClosed_iInter fun q => isClosed_iInter fun _ => ?_` and prove the remaining obligations. Conclude with `isClosed_eq ((((continuous_mat_lact (g * a) τ).matrix_adjugate).matrix_mul (continuous_mat_lact c τ)).matrix_elem p q) continuous_const`. Establish `cover : ∀ z ∈ W, ∃ γ ∈ S, z ∈ C γ`. Introduce `z hz`. Take `⟨γ, hγ, b, hb, heq⟩` from `hmove z hz`.

Use `⟨γ, hγ, fun τ p q hqp => ?_⟩` and prove the remaining obligations. Establish `key : mat (lact c z) τ = mat (lact (γ * a) z) τ * mat b τ`. Establish `h1 : mat (lact c z) τ = ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * ((a : Matrix (Fin r) (Fin r) E).map τ.1 * mat z τ)) * mat b τ` using `congrFun heq τ`. Rewrite using `[h1]`. Use `show _ = (((γ * a : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat z τ) * mat b τ`.

Rewrite using `[Units.val_mul, Matrix.map_mul]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[key, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply, smul_eq_mul]`. Establish `: mat b τ p q = 0` using `(hb τ).2 p q hqp`. Rewrite using `[this, mul_zero]`.

Use `haveI : Countable (GL (Fin r) E) := countable_GL_numberField r`. Set `f : Option S → Set (Frame X.Ψ r)` to `fun o => o.elim Wᶜ (fun γ => C γ.1)`. Establish `hf : ∀ o, IsClosed (f o)`. Introduce and unpack `(_ | γ)`. Use `exacts [hW.isClosed_compl, hC γ.1]`.

Establish `hU : ⋃ o, f o = Set.univ`. Use `Set.eq_univ_of_forall fun z => ?_` and prove the remaining obligations. Distinguish the cases in `hz : z ∈ W`. Take `⟨γ, hγ, hzC⟩` from `cover z hz`. Conclude with `Set.mem_iUnion.2 ⟨some ⟨γ, hγ⟩, hzC⟩`.

Conclude with `Set.mem_iUnion.2 ⟨none, hz⟩`. Establish `hD` using `dense_iUnion_interior_of_closed hf hU`. Take `⟨z, hzW, hz⟩` from `hD.inter_open_nonempty W hW hne`. Take `⟨o, ho⟩` from `Set.mem_iUnion.1 hz`. Consider the cases of `o with`.

Consider the case `none => exact absurd hzW (interior_subset ho)`. Consider the case `some γ`. Use `⟨γ.1, γ.2, W ∩ interior (C γ.1), hW.inter isOpen_interior, ⟨z, hzW, ho⟩, fun x hx => hWdom hx.1, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hxd : x ∈ X.dom` using `hWdom hx.1`. Establish `hxC : x ∈ C γ.1` using `interior_subset hx.2`.

Simplify using `only [C, Set.mem_setOf_eq] at hxC`. Generalize the expression as in `γ.1 * a = g at hxC ⊢`. Establish `hdetg : ∀ (g' : GL (Fin r) E) (τ : X.Ψ), ((g' : Matrix (Fin r) (Fin r) E).map τ.1).det ≠ 0`. Introduce `g' τ`. Establish `h` using `RingHom.map_det τ.1 (g' : Matrix (Fin r) (Fin r) E)`.

Rewrite `h` using `[RingHom.mapMatrix_apply]`. Rewrite using `[← h]`. Conclude with `(map_ne_zero τ.1).2 (Matrix.isUnits_det_units g').ne_zero`. Establish `hdetx : ∀ τ : X.Ψ, (mat x τ).det ≠ 0` using `fun τ => (hxd τ).1`. Establish `hdetA : ∀ (g' : GL (Fin r) E) (τ : X.Ψ), (mat (lact g' x) τ).det ≠ 0`.

Introduce `g' τ`. Use `show ((g' : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ).det ≠ 0`. Rewrite using `[Matrix.det_mul]`. Conclude with `mul_ne_zero (hdetg g' τ) (hdetx τ)`. Set `b : Frame X.Ψ r` to `fun τ => ((mat (lact g x) τ)⁻¹ * mat (lact c x) τ : Matrix (Fin r) (Fin r) ℂ)`.

Use `⟨b, fun τ => ⟨?_, fun p q hqp => ?_⟩, ?_⟩` and prove the remaining obligations. Use `show ((mat (lact g x) τ)⁻¹ * mat (lact c x) τ).det ≠ 0`. Rewrite using `[Matrix.det_mul]`. Conclude with `mul_ne_zero (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.2 (hdetA g τ))).ne_zero (hdetA c τ)`. Use `show ((mat (lact g x) τ)⁻¹ * mat (lact c x) τ) p q = 0`.

Rewrite using `[Matrix.inv_def, Matrix.smul_mul, Matrix.smul_apply, hxC τ p q hqp, smul_zero]`. Use function extensionality and compare the values at `τ`. Establish `hginv : ((g : Matrix (Fin r) (Fin r) E).map τ.1)⁻¹ = ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1`. Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]`.

Use `show ((g⁻¹ * c : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = mat x τ * (((g : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ)⁻¹ * ((c : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ))`. Rewrite using `[Matrix.mul_inv_rev, hginv, Units.val_mul, Matrix.map_mul]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (mat x τ) (mat x τ)⁻¹, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hdetx τ)), Matrix.one_mul]`.
-/
theorem baire_one_candidate {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : Data E r) (S : Set (GL (Fin r) E)) (a c : GL (Fin r) E) (W : Set (Frame X.Ψ r)) :
    IsOpen W → W.Nonempty → W ⊆ X.dom →
    (∀ z ∈ W, ∃ γ ∈ S, ∃ b ∈ Bor X.Ψ r, lact c z = rmul (lact γ (lact a z)) b) →
    ∃ γ ∈ S, ∃ V : Set (Frame X.Ψ r), IsOpen V ∧ V.Nonempty ∧ V ⊆ X.dom ∧
      ∀ x ∈ V, ∃ b ∈ Bor X.Ψ r, lact ((γ * a)⁻¹ * c) x = rmul x b := by
  intro hW hne hWdom hmove
  let C : GL (Fin r) E → Set (Frame X.Ψ r) := fun g => {z | ∀ τ : X.Ψ, ∀ p q : Fin r, q < p →
    ((mat (lact (g * a) z) τ).adjugate * mat (lact c z) τ) p q = 0}
  have hC : ∀ g, IsClosed (C g) := by
    intro g
    simp only [C, Set.setOf_forall]
    refine isClosed_iInter fun τ => isClosed_iInter fun p => isClosed_iInter fun q =>
      isClosed_iInter fun _ => ?_
    exact isClosed_eq ((((continuous_mat_lact (g * a) τ).matrix_adjugate).matrix_mul
      (continuous_mat_lact c τ)).matrix_elem p q) continuous_const
  have cover : ∀ z ∈ W, ∃ γ ∈ S, z ∈ C γ := by
    intro z hz
    obtain ⟨γ, hγ, b, hb, heq⟩ := hmove z hz
    refine ⟨γ, hγ, fun τ p q hqp => ?_⟩
    have key : mat (lact c z) τ = mat (lact (γ * a) z) τ * mat b τ := by
      have h1 : mat (lact c z) τ =
          ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * ((a : Matrix (Fin r) (Fin r) E).map τ.1 *
            mat z τ)) * mat b τ := congrFun heq τ
      rw [h1]
      show _ = (((γ * a : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat z τ) * mat b τ
      rw [Units.val_mul, Matrix.map_mul]
      simp only [Matrix.mul_assoc]
    rw [key, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul,
      Matrix.smul_apply, smul_eq_mul]
    have : mat b τ p q = 0 := (hb τ).2 p q hqp
    rw [this, mul_zero]
  haveI : Countable (GL (Fin r) E) := countable_GL_numberField r
  let f : Option S → Set (Frame X.Ψ r) := fun o => o.elim Wᶜ (fun γ => C γ.1)
  have hf : ∀ o, IsClosed (f o) := by
    rintro (_ | γ)
    exacts [hW.isClosed_compl, hC γ.1]
  have hU : ⋃ o, f o = Set.univ := by
    refine Set.eq_univ_of_forall fun z => ?_
    by_cases hz : z ∈ W
    · obtain ⟨γ, hγ, hzC⟩ := cover z hz
      exact Set.mem_iUnion.2 ⟨some ⟨γ, hγ⟩, hzC⟩
    · exact Set.mem_iUnion.2 ⟨none, hz⟩
  have hD := dense_iUnion_interior_of_closed hf hU
  obtain ⟨z, hzW, hz⟩ := hD.inter_open_nonempty W hW hne
  obtain ⟨o, ho⟩ := Set.mem_iUnion.1 hz
  cases o with
  | none => exact absurd hzW (interior_subset ho)
  | some γ =>
    refine ⟨γ.1, γ.2, W ∩ interior (C γ.1), hW.inter isOpen_interior, ⟨z, hzW, ho⟩,
      fun x hx => hWdom hx.1, fun x hx => ?_⟩
    have hxd : x ∈ X.dom := hWdom hx.1
    have hxC : x ∈ C γ.1 := interior_subset hx.2
    simp only [C, Set.mem_setOf_eq] at hxC
    generalize γ.1 * a = g at hxC ⊢
    have hdetg : ∀ (g' : GL (Fin r) E) (τ : X.Ψ),
        ((g' : Matrix (Fin r) (Fin r) E).map τ.1).det ≠ 0 := by
      intro g' τ
      have h := RingHom.map_det τ.1 (g' : Matrix (Fin r) (Fin r) E)
      rw [RingHom.mapMatrix_apply] at h
      rw [← h]
      exact (map_ne_zero τ.1).2 (Matrix.isUnits_det_units g').ne_zero
    have hdetx : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 := fun τ => (hxd τ).1
    have hdetA : ∀ (g' : GL (Fin r) E) (τ : X.Ψ), (mat (lact g' x) τ).det ≠ 0 := by
      intro g' τ
      show ((g' : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ).det ≠ 0
      rw [Matrix.det_mul]
      exact mul_ne_zero (hdetg g' τ) (hdetx τ)
    let b : Frame X.Ψ r := fun τ =>
      ((mat (lact g x) τ)⁻¹ * mat (lact c x) τ : Matrix (Fin r) (Fin r) ℂ)
    refine ⟨b, fun τ => ⟨?_, fun p q hqp => ?_⟩, ?_⟩
    · show ((mat (lact g x) τ)⁻¹ * mat (lact c x) τ).det ≠ 0
      rw [Matrix.det_mul]
      exact mul_ne_zero
        (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.2 (hdetA g τ))).ne_zero (hdetA c τ)
    · show ((mat (lact g x) τ)⁻¹ * mat (lact c x) τ) p q = 0
      rw [Matrix.inv_def, Matrix.smul_mul, Matrix.smul_apply, hxC τ p q hqp, smul_zero]
    · funext τ
      have hginv : ((g : Matrix (Fin r) (Fin r) E).map τ.1)⁻¹ =
          ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 := by
        apply Matrix.inv_eq_right_inv
        rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.map_one _ (map_zero _) (map_one _)]
      show ((g⁻¹ * c : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ =
        mat x τ * (((g : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ)⁻¹ *
          ((c : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ))
      rw [Matrix.mul_inv_rev, hginv, Units.val_mul, Matrix.map_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (mat x τ) (mat x τ)⁻¹,
        Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hdetx τ)), Matrix.one_mul]

end

end GlobalTheory
