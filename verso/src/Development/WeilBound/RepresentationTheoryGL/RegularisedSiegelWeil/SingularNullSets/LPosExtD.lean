import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LPosExtC

noncomputable section

open Set MeasureTheory CompactlySupported

namespace PositivityTheory.Rg.Rsw.L.LPosExt

variable {X : Type} [TopologicalSpace X]

def posCone : PointedCone ℝ C_c(X, ℝ) where
  carrier := {g | ∀ x, 0 ≤ g x}
  zero_mem' := fun x => by simp
  add_mem' := fun hf hg x => by simpa using add_nonneg (hf x) (hg x)
  smul_mem' := fun ⟨c, hc⟩ g hg x => by simpa using mul_nonneg hc (hg x)

/- English proof (translation)
Take `⟨b, hbA, hb0, M, hM, hMb⟩` from `dom A hbump (y := fun x => (f.1 x).re) (Complex.continuous_re.comp (hA _ f.2.1).1) ((hA _ f.2.1).2.comp_left Complex.zero_re)`. Use `set F : A := ⟨f.1, f.2.1⟩`. Use `set Bb : A := ⟨b, hbA⟩`. Establish `h1` using `hpos ((M : ℂ) • Bb - F) (fun x => by`. Use `f.2.2 x` as an intermediate fact.

Simplify using `only [Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Bb, F, (hb0 x).2, this]`. Apply the tactic sequence `constructor <;> linarith [(hMb x).2])`. Establish `h2` using `hpos ((M : ℂ) • Bb) (fun x => by`. Simplify using `only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Bb, (hb0 x).2]`. Apply the tactic sequence `constructor <;> nlinarith [(hb0 x).1])`.

Establish `: L F = L ((M : ℂ) • Bb) - L ((M : ℂ) • Bb - F)` using `by rw [map_sub]; ring`. Rewrite using `[this, Complex.sub_im, h1.2, h2.2, sub_zero]`.
-/
theorem im_L (A : Submodule ℂ (X → ℂ)) (hA : ∀ f ∈ A, Continuous f ∧ HasCompactSupport f)
    (hbump : ∀ C, IsCompact C → ∃ f ∈ A, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) ∧ ∀ x ∈ C, f x = 1)
    (L : A →ₗ[ℂ] ℂ) (hpos : ∀ f : A, (∀ x, 0 ≤ (f.1 x).re ∧ (f.1 x).im = 0) → 0 ≤ (L f).re ∧ (L f).im = 0)
    (f : AR A) : (L ⟨f.1, f.2.1⟩).im = 0 := by
  obtain ⟨b, hbA, hb0, M, hM, hMb⟩ := dom A hbump (y := fun x => (f.1 x).re)
    (Complex.continuous_re.comp (hA _ f.2.1).1) ((hA _ f.2.1).2.comp_left Complex.zero_re)
  set F : A := ⟨f.1, f.2.1⟩
  set Bb : A := ⟨b, hbA⟩
  have h1 := hpos ((M : ℂ) • Bb - F) (fun x => by
    have := f.2.2 x
    simp only [Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Bb, F, (hb0 x).2, this]
    constructor <;> linarith [(hMb x).2])
  have h2 := hpos ((M : ℂ) • Bb) (fun x => by
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Bb, (hb0 x).2]
    constructor <;> nlinarith [(hb0 x).1])
  have : L F = L ((M : ℂ) • Bb) - L ((M : ℂ) • Bb - F) := by rw [map_sub]; ring
  rw [this, Complex.sub_im, h1.2, h2.2, sub_zero]

/- English proof (translation)
Use `set φ := reC A hA`. Set `e` to `LinearEquiv.ofInjective φ (reC_inj A hA)`. Set `fP : C_c(X, ℝ) →ₗ.[ℝ] ℝ` to `⟨LinearMap.range φ, reL A L ∘ₗ e.symm.toLinearMap⟩`. Establish `he : ∀ a : AR A, e.symm ⟨φ a, LinearMap.mem_range_self φ a⟩ = a` using `fun a => by`. Rewrite using `[LinearEquiv.symm_apply_eq]`.

Conclude with `Subtype.ext (LinearEquiv.ofInjective_apply _ _).symm`. Establish `hnonneg : ∀ x : fP.domain, (x : C_c(X, ℝ)) ∈ posCone → 0 ≤ fP x`. Introduce and unpack `⟨y, hy⟩ hx`. Take `⟨a, rfl⟩` from `LinearMap.mem_range.mp hy`. Express the relevant statement in the definitionally equal form `0 ≤ reL A L (e.symm ⟨φ a, _⟩)`.

Rewrite using `[he]`. Conclude with `(hpos ⟨a.1, a.2.1⟩ (fun x => ⟨hx x, a.2.2 x⟩)).1`. Establish `hdense : ∀ y : C_c(X, ℝ), ∃ x : fP.domain, (x : C_c(X, ℝ)) + y ∈ posCone`. Introduce `y`. Take `⟨b, hbA, hb0, M, hM, hMb⟩` from `dom A hbump y.continuous y.hasCompactSupport`.

Set `bR : AR A` to `⟨b, hbA, fun x => (hb0 x).2⟩`. Use `⟨⟨M • φ bR, Submodule.smul_mem _ _ (LinearMap.mem_range_self φ bR)⟩, fun x => ?_⟩` and prove the remaining obligations. Simplify `(hMb x).1` using `[φ, reC, bR]`. Take `⟨g, hg, hgpos⟩` from `riesz_extension posCone fP hnonneg hdense`. Use `⟨PositiveLinearMap.mk₀ g (fun x hx => hgpos x (fun z => hx z)), fun a => ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `g (φ a) = _`. Rewrite using `[hg ⟨φ a, LinearMap.mem_range_self φ a⟩]`. Express the relevant statement in the definitionally equal form `reL A L (e.symm ⟨φ a, _⟩) = _`. Rewrite using `[he]`. Both sides reduce to the same expression.
-/
theorem extend (A : Submodule ℂ (X → ℂ)) (hA : ∀ f ∈ A, Continuous f ∧ HasCompactSupport f)
    (hbump : ∀ C, IsCompact C → ∃ f ∈ A, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) ∧ ∀ x ∈ C, f x = 1)
    (L : A →ₗ[ℂ] ℂ) (hpos : ∀ f : A, (∀ x, 0 ≤ (f.1 x).re ∧ (f.1 x).im = 0) → 0 ≤ (L f).re ∧ (L f).im = 0) :
    ∃ Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ, ∀ a : AR A, Λ (reC A hA a) = (L ⟨a.1, a.2.1⟩).re := by
  set φ := reC A hA
  let e := LinearEquiv.ofInjective φ (reC_inj A hA)
  let fP : C_c(X, ℝ) →ₗ.[ℝ] ℝ := ⟨LinearMap.range φ, reL A L ∘ₗ e.symm.toLinearMap⟩
  have he : ∀ a : AR A, e.symm ⟨φ a, LinearMap.mem_range_self φ a⟩ = a := fun a => by
    rw [LinearEquiv.symm_apply_eq]
    exact Subtype.ext (LinearEquiv.ofInjective_apply _ _).symm
  have hnonneg : ∀ x : fP.domain, (x : C_c(X, ℝ)) ∈ posCone → 0 ≤ fP x := by
    rintro ⟨y, hy⟩ hx
    obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hy
    change 0 ≤ reL A L (e.symm ⟨φ a, _⟩)
    rw [he]
    exact (hpos ⟨a.1, a.2.1⟩ (fun x => ⟨hx x, a.2.2 x⟩)).1
  have hdense : ∀ y : C_c(X, ℝ), ∃ x : fP.domain, (x : C_c(X, ℝ)) + y ∈ posCone := by
    intro y
    obtain ⟨b, hbA, hb0, M, hM, hMb⟩ := dom A hbump y.continuous y.hasCompactSupport
    let bR : AR A := ⟨b, hbA, fun x => (hb0 x).2⟩
    refine ⟨⟨M • φ bR, Submodule.smul_mem _ _ (LinearMap.mem_range_self φ bR)⟩, fun x => ?_⟩
    simpa [φ, reC, bR] using (hMb x).1
  obtain ⟨g, hg, hgpos⟩ := riesz_extension posCone fP hnonneg hdense
  refine ⟨PositiveLinearMap.mk₀ g (fun x hx => hgpos x (fun z => hx z)), fun a => ?_⟩
  change g (φ a) = _
  rw [hg ⟨φ a, LinearMap.mem_range_self φ a⟩]
  change reL A L (e.symm ⟨φ a, _⟩) = _
  rw [he]
  rfl

end PositivityTheory.Rg.Rsw.L.LPosExt
