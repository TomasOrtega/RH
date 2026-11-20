import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ModeHalfStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianLatticeMaps

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace ModeHalfC

open Matrix NumberField Complex ReciprocityTheory.ChartRestriction.G.FD Topology Filter ModeHalfA ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates Module

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Break down `Nat.eq_zero_or_pos N with hN | hN` into its components or cases. Substitute `hN` using the available equality. Conclude with `⟨1, one_pos, fun x hx => absurd (Subsingleton.elim x 0) hx⟩`. Use `haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩`. Set `q : (Fin N → ℝ) → ℝ` to `fun y => y ⬝ᵥ (A *ᵥ y)`.

Establish `hqc : Continuous q` using `continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)`. Establish `hpos : ∀ y : Fin N → ℝ, y ≠ 0 → 0 < q y`. Introduce `y hy`. Establish `h0` using `hA.dotProduct_mulVec_pos hy`. Simplify `h0` using `[q]`.

Take `⟨y0, hy0, hmin⟩` from `(isCompact_sphere (0 : Fin N → ℝ) 1).exists_isMinOn (NormedSpace.sphere_nonempty.mpr zero_le_one) hqc.continuousOn`. Establish `hy0ne : y0 ≠ 0`. Introduce `h`. Rewrite `hy0` using `[h, mem_sphere_zero_iff_norm, norm_zero]`. Conclude with `zero_ne_one hy0`.

Use `⟨q y0, hpos y0 hy0ne, fun x hx => ?_⟩` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, x i ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hx (funext hc)`.

Establish `hs1 : 1 ≤ ‖(fun i => (x i : ℝ))‖`. Establish `h1 : (1 : ℝ) ≤ |(x i : ℝ)|` using `by exact_mod_cast Int.one_le_abs hi`. Combine the equalities or inequalities in the displayed calculation. Use `set xr : Fin N → ℝ := fun i => (x i : ℝ) with hxr`. Establish `hs0 : ‖xr‖ ≠ 0` using `(lt_of_lt_of_le one_pos hs1).ne'`.

Establish `hy : ‖xr‖⁻¹ • xr ∈ Metric.sphere (0 : Fin N → ℝ) 1`. Rewrite using `[mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hs0]`. Establish `hq : q xr = ‖xr‖ ^ 2 * q (‖xr‖⁻¹ • xr)`. Simplify using `only [q, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts.

Establish `h3 : q y0 ≤ q (‖xr‖⁻¹ • xr)` using `hmin hy`. Establish `h4 : 0 < q y0` using `hpos y0 hy0ne`. Establish `hs2 : 1 ≤ ‖xr‖ ^ 2` using `by nlinarith`. Use `show q y0 ≤ q xr`. Rewrite using `[hq]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem posDef_int_lower {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef) :
    ∃ m0 : ℝ, 0 < m0 ∧ ∀ x : Fin N → ℤ, x ≠ 0 →
      m0 ≤ (fun i => (x i : ℝ)) ⬝ᵥ (A *ᵥ fun i => (x i : ℝ)) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact ⟨1, one_pos, fun x hx => absurd (Subsingleton.elim x 0) hx⟩
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let q : (Fin N → ℝ) → ℝ := fun y => y ⬝ᵥ (A *ᵥ y)
  have hqc : Continuous q :=
    continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
  have hpos : ∀ y : Fin N → ℝ, y ≠ 0 → 0 < q y := by
    intro y hy
    have h0 := hA.dotProduct_mulVec_pos hy
    simpa [q] using h0

  obtain ⟨y0, hy0, hmin⟩ := (isCompact_sphere (0 : Fin N → ℝ) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one) hqc.continuousOn
  have hy0ne : y0 ≠ 0 := by
    intro h
    rw [h, mem_sphere_zero_iff_norm, norm_zero] at hy0
    exact zero_ne_one hy0
  refine ⟨q y0, hpos y0 hy0ne, fun x hx => ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hx (funext hc)
  have hs1 : 1 ≤ ‖(fun i => (x i : ℝ))‖ := by
    have h1 : (1 : ℝ) ≤ |(x i : ℝ)| := by exact_mod_cast Int.one_le_abs hi
    calc (1 : ℝ) ≤ ‖(x i : ℝ)‖ := by rw [Real.norm_eq_abs]; exact h1
      _ ≤ ‖(fun i => (x i : ℝ))‖ := norm_le_pi_norm (fun i => (x i : ℝ)) i
  set xr : Fin N → ℝ := fun i => (x i : ℝ) with hxr
  have hs0 : ‖xr‖ ≠ 0 := (lt_of_lt_of_le one_pos hs1).ne'
  have hy : ‖xr‖⁻¹ • xr ∈ Metric.sphere (0 : Fin N → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hs0]
  have hq : q xr = ‖xr‖ ^ 2 * q (‖xr‖⁻¹ • xr) := by
    simp only [q, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    field_simp
  have h3 : q y0 ≤ q (‖xr‖⁻¹ • xr) := hmin hy
  have h4 : 0 < q y0 := hpos y0 hy0ne
  have hs2 : 1 ≤ ‖xr‖ ^ 2 := by nlinarith
  show q y0 ≤ q xr
  rw [hq]
  nlinarith

/- English proof (translation)
Take `⟨b, hb, h⟩` from `ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms.exists_normal_frame (X := X) hx`. Establish `horth : IsOrth X (rmul x b)` using `fun τ => (h τ).1`. Establish `hdet : ∀ τ, (mat (rmul x b) τ).det ≠ 0` using `fun τ => (dom_of_orth X horth τ).1`. Establish `hm : ∀ τ v, X.maj x τ v = ∑ a, ‖((mat (rmul x b) τ)⁻¹ *ᵥ v) a‖ ^ 2` using `fun τ v => (h τ).2 v`. Take `⟨m0, hm0, hlow⟩` from `posDef_int_lower (ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Am_posDef (X := X) (mat (rmul x b)) hdet (ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.zb (X := X)))`.

Establish `hQ : ∀ v ∈ X.Λ, v ≠ 0 → m0 ≤ ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v)`. Introduce `v hv hv0`. Establish `e1 : ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v) = ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy X (mat (rmul x b)) v`. Simplify using `only [ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy, hm]`. Establish `hc : (ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.zb (X` using `X)).repr ⟨v, hv⟩ ≠ 0 := by`.

Introduce `h0`. Establish `h1` using `(LinearEquiv.map_eq_zero_iff _).mp h0`. Conclude with `hv0 (by simpa using congrArg Subtype.val h1)`. Establish `hx0 : (fun i => (ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.zb (X` using `X)).repr ⟨v, hv⟩ i) ≠ 0 := by`. Introduce `h0`.

Apply `hc` to reduce the goal to its premises. Use extensionality with `i`. Conclude with `congrFun h0 i`. Establish `e2` using `ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.quad_int (X := X) (mat (rmul x b)) (ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.zb (X := X)) (fun i => (ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.zb (X := X)).repr ⟨v, hv⟩ i)`. Establish `e3` using `ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps.coe_expand (X := X) (ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.zb (X := X)) ⟨v, hv⟩`.

Rewrite using `[e1]`. Combine the equalities or inequalities in the displayed calculation. Establish `hS : m0 ≤ X.firstMinimumSq x`. Unfold `ReciprocityTheory.ChartRestriction.G.FD.Data.firstMinimumSq`. Take `⟨v, hv, hv0⟩` from `hne`.

Use `le_csInf ⟨_, v, hv, hv0, rfl⟩ ?_` and prove the remaining obligations. Introduce and unpack `t ⟨w, hw, hw0, rfl⟩`. Conclude with `hQ w hw hw0`. Unfold `ReciprocityTheory.ChartRestriction.G.FD.Data.la1`. Conclude with `Real.sqrt_pos.mpr (lt_of_lt_of_le hm0 hS)`.
-/
theorem first_minimum_pos (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (hne : ∃ v ∈ X.Λ, v ≠ 0) :
    0 < X.la1 x := by
  obtain ⟨b, hb, h⟩ := ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms.exists_normal_frame (X := X) hx
  have horth : IsOrth X (rmul x b) := fun τ => (h τ).1
  have hdet : ∀ τ, (mat (rmul x b) τ).det ≠ 0 := fun τ => (dom_of_orth X horth τ).1
  have hm : ∀ τ v, X.maj x τ v = ∑ a, ‖((mat (rmul x b) τ)⁻¹ *ᵥ v) a‖ ^ 2 :=
    fun τ v => (h τ).2 v
  obtain ⟨m0, hm0, hlow⟩ := posDef_int_lower
    (ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Am_posDef (X := X) (mat (rmul x b)) hdet
      (ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.zb (X := X)))

  have hQ : ∀ v ∈ X.Λ, v ≠ 0 → m0 ≤ ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v) := by
    intro v hv hv0
    have e1 : ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v) =
        ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy X (mat (rmul x b)) v := by
      simp only [ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy, hm]
    have hc : (ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.zb (X := X)).repr ⟨v, hv⟩ ≠ 0 := by
      intro h0
      have h1 := (LinearEquiv.map_eq_zero_iff _).mp h0
      exact hv0 (by simpa using congrArg Subtype.val h1)
    have hx0 : (fun i => (ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.zb (X := X)).repr ⟨v, hv⟩ i) ≠ 0 := by
      intro h0
      apply hc
      ext i
      exact congrFun h0 i
    have e2 := ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.quad_int (X := X) (mat (rmul x b))
      (ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.zb (X := X))
      (fun i => (ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.zb (X := X)).repr ⟨v, hv⟩ i)
    have e3 := ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps.coe_expand (X := X)
      (ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.zb (X := X)) ⟨v, hv⟩
    rw [e1]
    calc m0 ≤ _ := hlow _ hx0
      _ = _ := e2
      _ = ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy X (mat (rmul x b)) v := by rw [← e3]
  have hS : m0 ≤ X.firstMinimumSq x := by
    unfold ReciprocityTheory.ChartRestriction.G.FD.Data.firstMinimumSq
    obtain ⟨v, hv, hv0⟩ := hne
    refine le_csInf ⟨_, v, hv, hv0, rfl⟩ ?_
    rintro t ⟨w, hw, hw0, rfl⟩
    exact hQ w hw hw0
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.la1
  exact Real.sqrt_pos.mpr (lt_of_lt_of_le hm0 hS)

/- English proof (translation)
Take `⟨b, hb, h⟩` from `ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms.exists_normal_frame (X := X) hp`. Establish `horth : IsOrth X (rmul p b)` using `fun τ => (h τ).1`. Use `⟨b, hb, horth, fun τ v => ?_⟩` and prove the remaining obligations. Rewrite using `[maj_orth X horth, (h τ).2 v]`.
-/
theorem orthonormalize (X : Data E r) {p : Frame X.Ψ r} (hp : p ∈ X.dom) :
    ∃ b ∈ Bor X.Ψ r, IsOrth X (rmul p b) ∧ ∀ τ v, X.maj (rmul p b) τ v = X.maj p τ v := by
  obtain ⟨b, hb, h⟩ := ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms.exists_normal_frame (X := X) hp
  have horth : IsOrth X (rmul p b) := fun τ => (h τ).1
  refine ⟨b, hb, horth, fun τ v => ?_⟩
  rw [maj_orth X horth, (h τ).2 v]

/- English proof (translation)
Rewrite using `[maj_orth X hu]`. Check the signs of the components of the expression.
-/
theorem maj_nonneg_orth (X : Data E r) {u : Frame X.Ψ r} (hu : IsOrth X u) (τ : X.Ψ) (v : Fin r → ℂ) :
    0 ≤ X.maj u τ v := by
  rw [maj_orth X hu]
  positivity

end ModeHalfC

end ReciprocityTheory.ChartRestriction.G.AR.Up
