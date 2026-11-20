import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantFamilyNorms

namespace ReciprocityTheory.ChartRestriction.G.FD

open Complex ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

/- English proof (translation)
Establish `hG` using `MajorantFamilyNorms.hG_of X τ`. Establish `hdet : (mat x τ).det ≠ 0` using `(hx τ).1`. Establish `hsg` using `MajorantFamilyNorms.hsg_of X hx τ`. Establish `he0` using `(he τ).1`. Establish `key : ∀ i : Fin (r + 1), (dmin X.Gm (X.flowV e s x) τ i).re = (dmin X.Gm x τ i).re * (1 + 2 * X.c τ * (s τ).im * mN τ.1 X.Gm (mat x τ) (e τ) i)`.

Introduce `i`. Rewrite using `[MajorantFamilyNorms.dmin_eq X (X.flowV e s x), MajorantFamilyNorms.dmin_flow X hx e τ he0 s, ← MajorantFamilyNorms.dmin_eq X x, Complex.re_mul_ofReal]`. Establish `hpos : ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re` using `(hx τ).2`. Establish `hb` using `fun (i : ℕ) (hi : i ≤ r) => mN_bounds hG X.p0 X.p0_le (mat x τ) hdet hsg (e τ) he0 i hi`. Establish `hmp` using `mN_pos hG X.p0 X.p0_le (mat x τ) hdet hsg (e τ) he0 (he τ).2`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h0` using `h ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩`. Rewrite `h0` using `[key, ← mul_assoc]`. Conclude with `pos_of_mul_pos_right h0 (hpos _).le`.

Introduce `h i`. Rewrite using `[key, ← mul_assoc]`. Use `mul_pos (hpos i) ?_` and prove the remaining obligations. Take `⟨h0, h1⟩` from `hb i (Nat.le_of_lt_succ i.isLt)`. Break down `le_or_gt 0 (2 * X.c τ * (s τ).im) with hk | hk` into its components or cases.

Use polynomial arithmetic with `[mul_nonneg hk h0]`. Use polynomial arithmetic with `[mul_le_mul_of_nonpos_left h1 hk.le]`.
-/
private theorem minors_iff {r : ℕ} (X : Data E r) (e : X.Ψ → Fin r → ℂ) (he : X.IsIsoV e)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : X.Ψ → ℂ) (τ : X.Ψ) :
    (∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (X.flowV e s x) τ i).re) ↔
      0 < 1 + 2 * X.c τ * (s τ).im * mN τ.1 X.Gm (mat x τ) (e τ) X.p0 := by
  have hG := MajorantFamilyNorms.hG_of X τ
  have hdet : (mat x τ).det ≠ 0 := (hx τ).1
  have hsg := MajorantFamilyNorms.hsg_of X hx τ
  have he0 := (he τ).1
  have key : ∀ i : Fin (r + 1), (dmin X.Gm (X.flowV e s x) τ i).re =
      (dmin X.Gm x τ i).re * (1 + 2 * X.c τ * (s τ).im * mN τ.1 X.Gm (mat x τ) (e τ) i) := by
    intro i
    rw [MajorantFamilyNorms.dmin_eq X (X.flowV e s x), MajorantFamilyNorms.dmin_flow X hx e τ he0 s,
      ← MajorantFamilyNorms.dmin_eq X x, Complex.re_mul_ofReal]
  have hpos : ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := (hx τ).2
  have hb := fun (i : ℕ) (hi : i ≤ r) =>
    mN_bounds hG X.p0 X.p0_le (mat x τ) hdet hsg (e τ) he0 i hi
  have hmp := mN_pos hG X.p0 X.p0_le (mat x τ) hdet hsg (e τ) he0 (he τ).2
  constructor
  · intro h
    have h0 := h ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩
    rw [key, ← mul_assoc] at h0
    exact pos_of_mul_pos_right h0 (hpos _).le
  · intro h i
    rw [key, ← mul_assoc]
    refine mul_pos (hpos i) ?_
    obtain ⟨h0, h1⟩ := hb i (Nat.le_of_lt_succ i.isLt)
    rcases le_or_gt 0 (2 * X.c τ * (s τ).im) with hk | hk
    · nlinarith [mul_nonneg hk h0]
    · nlinarith [mul_le_mul_of_nonpos_left h1 hk.le]

/- English proof (translation)
Introduce `r X e he x hx s`. Establish `hmp : ∀ τ, 0 < mN τ.1 X.Gm (mat x τ) (e τ) X.p0` using `fun τ => mN_pos (MajorantFamilyNorms.hG_of X τ) X.p0 X.p0_le (mat x τ) (hx τ).1 (MajorantFamilyNorms.hsg_of X hx τ) (e τ) (he τ).1 (he τ).2`. Establish `hm : ∀ τ, 1 + (s τ).im / X.ttV e x τ = 1 + 2 * X.c τ * (s τ).im * mN τ.1 X.Gm (mat x τ) (e τ) X.p0`. Introduce `τ`. Rewrite using `[Data.ttV, MajorantFamilyNorms.maj_eq X hx e τ (he τ).1, one_div, div_inv_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hdom : X.flowV e s x ∈ X.dom ↔ ∀ τ, ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (X.flowV e s x) τ i).re`. Prove the components needed by the constructor for the conclusion. Introduce `h τ`. Conclude with `(h τ).2`.

Introduce `h τ`. Use `⟨?_, h τ⟩` and prove the remaining obligations. Use `show (X.flowMatV (e τ) τ (s τ) * mat x τ).det ≠ 0`. Rewrite using `[Matrix.det_mul, MajorantFamilyNorms.det_flowMat X (e τ) τ (s τ) (he τ).1, one_mul]`. Conclude with `(hx τ).1`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hdom]`. Use `forall_congr' fun τ => ?_` and prove the remaining obligations. Rewrite using `[hm τ]`. Conclude with `minors_iff X e he hx s τ`.

Introduce `hf τ`. Establish `hpos` using `(minors_iff X e he hx s τ).1 (hdom.1 hf τ)`. Establish `hc` using `MajorantFamilyNorms.c_pos X τ`. Establish `hm0` using `hmp τ`. Simplify using `only [Data.ttV]`.

Rewrite using `[MajorantFamilyNorms.maj_flow X hx e τ (he τ).1 s hpos.ne', MajorantFamilyNorms.maj_eq X hx e τ (he τ).1]`. Clear the denominators using the available nonvanishing facts.
-/
theorem flowDomainCriterion_holds : FlowDomainCriterion (E := E) := by
  intro r X e he x hx s
  have hmp : ∀ τ, 0 < mN τ.1 X.Gm (mat x τ) (e τ) X.p0 := fun τ =>
    mN_pos (MajorantFamilyNorms.hG_of X τ) X.p0 X.p0_le (mat x τ) (hx τ).1 (MajorantFamilyNorms.hsg_of X hx τ) (e τ)
      (he τ).1 (he τ).2
  have hm : ∀ τ, 1 + (s τ).im / X.ttV e x τ =
      1 + 2 * X.c τ * (s τ).im * mN τ.1 X.Gm (mat x τ) (e τ) X.p0 := by
    intro τ
    rw [Data.ttV, MajorantFamilyNorms.maj_eq X hx e τ (he τ).1, one_div, div_inv_eq_mul]
    ring
  have hdom : X.flowV e s x ∈ X.dom ↔
      ∀ τ, ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (X.flowV e s x) τ i).re := by
    constructor
    · intro h τ
      exact (h τ).2
    · intro h τ
      refine ⟨?_, h τ⟩
      show (X.flowMatV (e τ) τ (s τ) * mat x τ).det ≠ 0
      rw [Matrix.det_mul, MajorantFamilyNorms.det_flowMat X (e τ) τ (s τ) (he τ).1, one_mul]
      exact (hx τ).1
  refine ⟨?_, ?_⟩
  · rw [hdom]
    refine forall_congr' fun τ => ?_
    rw [hm τ]
    exact minors_iff X e he hx s τ
  · intro hf τ
    have hpos := (minors_iff X e he hx s τ).1 (hdom.1 hf τ)
    have hc := MajorantFamilyNorms.c_pos X τ
    have hm0 := hmp τ
    simp only [Data.ttV]
    rw [MajorantFamilyNorms.maj_flow X hx e τ (he τ).1 s hpos.ne', MajorantFamilyNorms.maj_eq X hx e τ (he τ).1]
    field_simp

end ReciprocityTheory.ChartRestriction.G.FD
