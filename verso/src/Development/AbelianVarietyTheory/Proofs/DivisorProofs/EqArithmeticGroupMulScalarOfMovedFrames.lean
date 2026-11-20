import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenScal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelGamS

noncomputable section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

namespace GlobalTheory.LevModel

/- English proof (translation)
Take `⟨y₀, hy₀⟩` from `hne`. Take `⟨ρ, hρ, hball⟩` from `Metric.isOpen_iff.1 hO _ hy₀`. Use `set B₀ := Metric.ball y₀ ρ with hB₀`. Set `f : Option G → Set (Frame Ψ r)` to `fun o => match o with`. Consider the case `none => B₀ᶜ`.

Consider the case `some γ' => ReciprocityTheory.ChartRestriction.G.PullbackSections.TSet Ψ ((γ'.1⁻¹ * h : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)`. Establish `hc : ∀ o, IsClosed (f o)`. Introduce and unpack `(_ | γ')`. Conclude with `Metric.isOpen_ball.isClosed_compl`. Conclude with `ReciprocityTheory.ChartRestriction.G.PullbackSections.isClosed_TSet _ _`.

Establish `hU : ⋃ o, f o = Set.univ`. Use `Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ B₀`. Take `⟨γ', hγ', b, hb, e⟩` from `H1 x (hball hx)`. Conclude with `⟨some ⟨γ', hγ'⟩, ReciprocityTheory.ChartRestriction.G.PullbackSections.mem_TSet Ψ h γ' hb e⟩`.

Conclude with `⟨none, hx⟩`. Establish `hd` using `dense_iUnion_interior_of_closed hc hU`. Take `⟨y, hyB, hyU⟩` from `hd.inter_open_nonempty B₀ Metric.isOpen_ball ⟨_, Metric.mem_ball_self hρ⟩`. Take `⟨o, ho⟩` from `Set.mem_iUnion.1 hyU`. Consider the cases of `o with`.

Consider the case `none => exact absurd hyB (interior_subset ho)`. Consider the case `some γ' => set g : Matrix (Fin r) (Fin r) E := ((γ'.1⁻¹ * h : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) with hg`. Take `⟨κ, hκ⟩` from `ReciprocityTheory.ChartRestriction.G.PullbackSections.scalar_step τ₀ g (W := interior (f (some γ')) ∩ B₀) (isOpen_interior.inter Metric.isOpen_ball) (fun x hx => interior_subset hx.1) (y := y) ⟨ho, hyB⟩ (hdet y (hball hyB))`. Establish `hent : ∀ a b, τ₀.1 (g a b) = if a = b then κ else 0`. Introduce `a b`.

Use `congrFun (congrFun hκ a) b` as an intermediate fact. Simplify `this` using `[Matrix.one_apply]`. Establish `hh : (h : Matrix (Fin r) (Fin r) E) = (γ'.1 : Matrix (Fin r) (Fin r) E) * g`. Rewrite using `[hg, ← Units.val_mul, mul_inv_cancel_left]`. Break down `Nat.eq_zero_or_pos r with hr | hr` into its components or cases.

Substitute `hr` using the available equality. Conclude with `⟨γ'.1, γ'.2, 0, by ext a; exact Fin.elim0 a⟩`. Use `⟨γ'.1, γ'.2, g ⟨0, hr⟩ ⟨0, hr⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hh]`. Use `congr 1`.

Use extensionality with `a b`. Apply `τ₀.1.injective` to reduce the goal to its premises. Rewrite using `[hent a b, Matrix.scalar_apply, Matrix.diagonal_apply]`. Distinguish the cases in `hab : a = b`. Rewrite using `[if_pos hab, if_pos hab, hent, if_pos rfl]`.

Rewrite using `[if_neg hab, if_neg hab, map_zero]`.
-/
theorem orbit_open_scalar {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Ψ : Finset (E →+* ℂ)}
    (τ₀ : Ψ) (G : Subgroup (GL (Fin r) E)) (h : GL (Fin r) E) {O : Set (Frame Ψ r)} (hO : IsOpen O)
    (hne : O.Nonempty) (hdet : ∀ y ∈ O, (mat y τ₀).det ≠ 0)
    (H1 : ∀ y ∈ O, ∃ γ ∈ G, ∃ b ∈ Bor Ψ r, lact h y = rmul (lact γ y) b) :
    ∃ γ ∈ G, ∃ ζ : E, (h : Matrix (Fin r) (Fin r) E) = (γ : Matrix (Fin r) (Fin r) E) * Matrix.scalar (Fin r) ζ := by
  classical
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hO _ hy₀
  set B₀ := Metric.ball y₀ ρ with hB₀
  let f : Option G → Set (Frame Ψ r) := fun o => match o with
    | none => B₀ᶜ
    | some γ' => ReciprocityTheory.ChartRestriction.G.PullbackSections.TSet Ψ ((γ'.1⁻¹ * h : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)
  have hc : ∀ o, IsClosed (f o) := by
    rintro (_ | γ')
    · exact Metric.isOpen_ball.isClosed_compl
    · exact ReciprocityTheory.ChartRestriction.G.PullbackSections.isClosed_TSet _ _
  have hU : ⋃ o, f o = Set.univ := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
    by_cases hx : x ∈ B₀
    · obtain ⟨γ', hγ', b, hb, e⟩ := H1 x (hball hx)
      exact ⟨some ⟨γ', hγ'⟩, ReciprocityTheory.ChartRestriction.G.PullbackSections.mem_TSet Ψ h γ' hb e⟩
    · exact ⟨none, hx⟩
  have hd := dense_iUnion_interior_of_closed hc hU
  obtain ⟨y, hyB, hyU⟩ := hd.inter_open_nonempty B₀ Metric.isOpen_ball ⟨_, Metric.mem_ball_self hρ⟩
  obtain ⟨o, ho⟩ := Set.mem_iUnion.1 hyU
  cases o with
  | none => exact absurd hyB (interior_subset ho)
  | some γ' =>
    set g : Matrix (Fin r) (Fin r) E := ((γ'.1⁻¹ * h : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) with hg
    obtain ⟨κ, hκ⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.scalar_step τ₀ g
      (W := interior (f (some γ')) ∩ B₀) (isOpen_interior.inter Metric.isOpen_ball)
      (fun x hx => interior_subset hx.1) (y := y) ⟨ho, hyB⟩ (hdet y (hball hyB))
    have hent : ∀ a b, τ₀.1 (g a b) = if a = b then κ else 0 := by
      intro a b
      have := congrFun (congrFun hκ a) b
      simpa [Matrix.one_apply] using this
    have hh : (h : Matrix (Fin r) (Fin r) E) = (γ'.1 : Matrix (Fin r) (Fin r) E) * g := by
      rw [hg, ← Units.val_mul, mul_inv_cancel_left]
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      exact ⟨γ'.1, γ'.2, 0, by ext a; exact Fin.elim0 a⟩
    · refine ⟨γ'.1, γ'.2, g ⟨0, hr⟩ ⟨0, hr⟩, ?_⟩
      rw [hh]
      congr 1
      ext a b
      apply τ₀.1.injective
      rw [hent a b, Matrix.scalar_apply, Matrix.diagonal_apply]
      by_cases hab : a = b
      · rw [if_pos hab, if_pos hab, hent, if_pos rfl]
      · rw [if_neg hab, if_neg hab, map_zero]

/- English proof (translation)
Take `⟨τ₁⟩ : Nonempty (E →+* ℂ)` from `⟨(IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom⟩`. Choose the witnesses or unpack the hypotheses as in `⟨τ₀, hτ₀⟩ : ∃ τ, τ ∈ X.Ψ := by`. Distinguish the cases in `hτ : τ₁ ∈ X.Ψ`. Conclude with `⟨τ₁, hτ⟩`. Use `⟨ComplexEmbedding.conjugate τ₁, ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hc`. Conclude with `hτ ((X.cmType τ₁).2 hc)`. Establish `hmem : ∀ τ : X₂.Ψ, τ.1 ∈ X.Ψ` using `fun τ => hΨ ▸ τ.2`. Establish `hmem' : ∀ τ : X.Ψ, τ.1 ∈ X₂.Ψ` using `fun τ => hΨ.symm ▸ τ.2`. Set `back : Frame X.Ψ r → Frame X₂.Ψ r` to `fun y τ => (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat y ⟨τ.1, hmem τ⟩ : Matrix (Fin r) (Fin r) ℂ)`.

Set `fwd : Frame X₂.Ψ r → Frame X.Ψ r` to `fun x τ => ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x ⟨τ.1, hmem' τ⟩ : Matrix (Fin r) (Fin r) ℂ)`. Establish `hback : Continuous back`. Use `continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations. Establish `hm : Continuous fun y : Frame X.Ψ r => mat y ⟨τ.1, hmem τ⟩` using `continuous_apply _`. Conclude with `(continuous_const.matrix_mul hm).matrix_elem a b`.

Establish `hbf : ∀ x, back (fwd x) = x`. Introduce `x`. Use function extensionality and compare the values at `τ`. Use `show (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) : Matrix (Fin r) (Fin r) ℂ) = mat x τ`. Rewrite using `[← Matrix.mul_assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.map_gl_inv_mul, Matrix.one_mul]`.

Establish `hmoved : ∀ y, GlobalTheory.LevModel.Moved X₂ X δ (back y) y`. Introduce `y τ h₂ h₁`. Use `show mat y ⟨τ, h₁⟩ = (δ : Matrix (Fin r) (Fin r) E).map τ * (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ * mat y ⟨τ, h₁⟩)`. Rewrite using `[← Matrix.mul_assoc]`. Use `ReciprocityTheory.ChartRestriction.G.PullbackSections.map_gl_inv_mul τ (δ⁻¹ : GL (Fin r) E)` as an intermediate fact.

Rewrite `this` using `[inv_inv]`. Rewrite using `[this, Matrix.one_mul]`. Establish `hdom : (X₂.dom).Nonempty` using `⟨_, ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfA.dom_of_orth X₂ (ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB.chosenFrame_isOrthogonal X₂)⟩`. Take `⟨x₀, hx₀⟩` from `hdom`. Use `orbit_open_scalar ⟨τ₀, hτ₀⟩ X.Γ h (O := back ⁻¹' X₂.dom) ((ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom X₂).preimage hback) ⟨fwd x₀, by rw [Set.mem_preimage, hbf]; exact hx₀⟩ ?_ (fun y hy => H _ hy y (hmoved y))` and prove the remaining obligations.

Introduce `y hy`. Establish `h1` using `(hy ⟨τ₀, hmem' ⟨τ₀, hτ₀⟩⟩).1`. Establish `h2 : mat (back y) ⟨τ₀, hmem' ⟨τ₀, hτ₀⟩⟩ = ((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ₀ * mat y ⟨τ₀, hτ₀⟩` using `rfl`. Rewrite `h1` using `[h2, Matrix.det_mul]`. Conclude with `right_ne_zero_of_mul h1`.
-/
theorem eq_mul_scalar_of_moved {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X₂ X : Data E r) (δ h : GL (Fin r) E) (hΨ : X₂.Ψ = X.Ψ)
    (H : ∀ x ∈ X₂.dom, ∀ x' : Frame X.Ψ r, GlobalTheory.LevModel.Moved X₂ X δ x x' → ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact h x' = rmul (lact γ x') b) :
    ∃ γ ∈ X.Γ, ∃ ζ : E, (h : Matrix (Fin r) (Fin r) E) = (γ : Matrix (Fin r) (Fin r) E) * Matrix.scalar (Fin r) ζ := by
  classical

  obtain ⟨τ₁⟩ : Nonempty (E →+* ℂ) := ⟨(IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom⟩
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ, τ ∈ X.Ψ := by
    by_cases hτ : τ₁ ∈ X.Ψ
    · exact ⟨τ₁, hτ⟩
    · refine ⟨ComplexEmbedding.conjugate τ₁, ?_⟩
      by_contra hc
      exact hτ ((X.cmType τ₁).2 hc)
  have hmem : ∀ τ : X₂.Ψ, τ.1 ∈ X.Ψ := fun τ => hΨ ▸ τ.2
  have hmem' : ∀ τ : X.Ψ, τ.1 ∈ X₂.Ψ := fun τ => hΨ.symm ▸ τ.2

  let back : Frame X.Ψ r → Frame X₂.Ψ r := fun y τ =>
    (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat y ⟨τ.1, hmem τ⟩ : Matrix (Fin r) (Fin r) ℂ)
  let fwd : Frame X₂.Ψ r → Frame X.Ψ r := fun x τ =>
    ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x ⟨τ.1, hmem' τ⟩ : Matrix (Fin r) (Fin r) ℂ)
  have hback : Continuous back := by
    refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
    have hm : Continuous fun y : Frame X.Ψ r => mat y ⟨τ.1, hmem τ⟩ := continuous_apply _
    exact (continuous_const.matrix_mul hm).matrix_elem a b
  have hbf : ∀ x, back (fwd x) = x := by
    intro x
    funext τ
    show (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
      ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) : Matrix (Fin r) (Fin r) ℂ) = mat x τ
    rw [← Matrix.mul_assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.map_gl_inv_mul, Matrix.one_mul]
  have hmoved : ∀ y, GlobalTheory.LevModel.Moved X₂ X δ (back y) y := by
    intro y τ h₂ h₁
    show mat y ⟨τ, h₁⟩ = (δ : Matrix (Fin r) (Fin r) E).map τ *
      (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ * mat y ⟨τ, h₁⟩)
    rw [← Matrix.mul_assoc]
    have := ReciprocityTheory.ChartRestriction.G.PullbackSections.map_gl_inv_mul τ (δ⁻¹ : GL (Fin r) E)
    rw [inv_inv] at this
    rw [this, Matrix.one_mul]
  have hdom : (X₂.dom).Nonempty := ⟨_, ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfA.dom_of_orth X₂ (ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB.chosenFrame_isOrthogonal X₂)⟩
  obtain ⟨x₀, hx₀⟩ := hdom
  refine orbit_open_scalar ⟨τ₀, hτ₀⟩ X.Γ h (O := back ⁻¹' X₂.dom)
    ((ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom X₂).preimage hback) ⟨fwd x₀, by rw [Set.mem_preimage, hbf]; exact hx₀⟩ ?_
    (fun y hy => H _ hy y (hmoved y))
  intro y hy
  have h1 := (hy ⟨τ₀, hmem' ⟨τ₀, hτ₀⟩⟩).1
  have h2 : mat (back y) ⟨τ₀, hmem' ⟨τ₀, hτ₀⟩⟩ =
      ((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ₀ * mat y ⟨τ₀, hτ₀⟩ := rfl
  rw [h2, Matrix.det_mul] at h1
  exact right_ne_zero_of_mul h1

end GlobalTheory.LevModel
