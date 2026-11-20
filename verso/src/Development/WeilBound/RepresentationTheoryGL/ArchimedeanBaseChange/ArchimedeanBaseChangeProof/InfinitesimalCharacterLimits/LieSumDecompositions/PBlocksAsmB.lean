import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksAsmA
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksExp
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksTwHyp
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksTwCent
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksTwNonPos

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockDerivatives PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAssembly

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r s : ℕ} {U : Submodule ℂ (Sm E (r + s))} {c : ℂ}
  {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)}

/- English proof (translation)
Establish `: 0 < Module.finrank ℚ E` using `Module.finrank_pos`. Conclude with `this` after adjusting the coercions.
-/
theorem d_pos : (0 : ℝ) < (Module.finrank ℚ E : ℝ) := by
  have : 0 < Module.finrank ℚ E := Module.finrank_pos
  exact_mod_cast this

/- English proof (translation)
Use `BlockExponential.exp_span _ _ (fun φ hφ => BlockSlices.LS_aut hT φ (Submodule.subset_span hφ)) ?_` and prove the remaining obligations. Introduce and unpack `ℓ ⟨ψ, hψ, k, g, m₂, hℓ⟩ r' hr' hrr c' hc'`. Take `⟨ψ₁, -, h1, -, hexp⟩` from `hT.left ψ hψ k g m₂`. Establish `e : ℓ = ψ₁` using `Subtype.ext (funext fun m₁ => (hℓ m₁).trans (h1 m₁).symm)`. Rewrite `hc'` using `[e]`.

Take `⟨φ, hφ, hcφ⟩` from `hexp r' hr' hrr c' hc'`. Establish `h` using `hNP φ hφ r' hr' (by omega) c' hcφ`. Establish `hd` using `d_pos (E := E)`. Unfold `pE at h`. Establish `h2 : c'.re / (Module.finrank ℚ E : ℝ) ≤ (r' : ℝ) * (((r + s : ℕ) : ℝ) - r') / 2` using `by linarith`.

Rewrite `h2` using `[div_le_iff₀ hd]`. Establish `e2 : (Module.finrank ℚ E : ℝ) * ((r' : ℝ) * (((r + s : ℕ) : ℝ) - r')) / 2 = (r' : ℝ) * (((r + s : ℕ) : ℝ) - r') / 2 * (Module.finrank ℚ E : ℝ)` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem LS_exp (hU : IsAutSt U) (hNP : NonPos U) (hT : IsSliceMap U c T) :
    ∀ φ ∈ LS U T, ∀ r', 0 < r' → r' < r → ∀ c' ∈ Exp r' φ.1,
      c'.re ≤ (Module.finrank ℚ E : ℝ) * ((r' : ℝ) * (((r + s : ℕ) : ℝ) - r')) / 2 := by
  refine BlockExponential.exp_span _ _ (fun φ hφ => BlockSlices.LS_aut hT φ (Submodule.subset_span hφ)) ?_
  rintro ℓ ⟨ψ, hψ, k, g, m₂, hℓ⟩ r' hr' hrr c' hc'
  obtain ⟨ψ₁, -, h1, -, hexp⟩ := hT.left ψ hψ k g m₂
  have e : ℓ = ψ₁ := Subtype.ext (funext fun m₁ => (hℓ m₁).trans (h1 m₁).symm)
  rw [e] at hc'
  obtain ⟨φ, hφ, hcφ⟩ := hexp r' hr' hrr c' hc'
  have h := hNP φ hφ r' hr' (by omega) c' hcφ
  have hd := d_pos (E := E)
  unfold pE at h
  have h2 : c'.re / (Module.finrank ℚ E : ℝ) ≤ (r' : ℝ) * (((r + s : ℕ) : ℝ) - r') / 2 := by linarith
  rw [div_le_iff₀ hd] at h2
  have e2 : (Module.finrank ℚ E : ℝ) * ((r' : ℝ) * (((r + s : ℕ) : ℝ) - r')) / 2 =
      (r' : ℝ) * (((r + s : ℕ) : ℝ) - r') / 2 * (Module.finrank ℚ E : ℝ) := by ring
  linarith

/- English proof (translation)
Use `BlockExponential.exp_span _ (fun r₂ => (Module.finrank ℚ E : ℝ) * (((r + r₂ : ℕ) : ℝ) * (((r + s : ℕ) : ℝ) - ((r + r₂ : ℕ) : ℝ))) / 2 - c.re) (fun φ hφ => BlockSlices.RS_aut hT φ (Submodule.subset_span hφ)) ?_` and prove the remaining obligations. Introduce and unpack `ℓ ⟨ψ, hψ, k, g, m₁, hℓ⟩ r₂ hr₂ hrs c₂ hc₂`. Take `⟨ψ₂, -, h1, -, hexp⟩` from `hT.right ψ hψ k g m₁`. Establish `e : ℓ = ψ₂` using `Subtype.ext (funext fun m₂ => (hℓ m₂).trans (h1 m₂).symm)`. Rewrite `hc₂` using `[e]`.

Take `⟨φ, hφ, hcφ⟩` from `hexp r₂ hr₂ hrs c₂ hc₂`. Establish `h` using `hNP φ hφ (r + r₂) (by omega) (by omega) (c + c₂) hcφ`. Establish `hd` using `d_pos (E := E)`. Unfold `pE at h`. Rewrite `h` using `[Complex.add_re]`.

Establish `h2 : (c.re + c₂.re) / (Module.finrank ℚ E : ℝ) ≤ ((r + r₂ : ℕ) : ℝ) * (((r + s : ℕ) : ℝ) - ((r + r₂ : ℕ) : ℝ)) / 2` using `by linarith`. Rewrite `h2` using `[div_le_iff₀ hd]`. Establish `e2 : (Module.finrank ℚ E : ℝ) * (((r + r₂ : ℕ) : ℝ) * (((r + s : ℕ) : ℝ) - ((r + r₂ : ℕ) : ℝ))) / 2 = ((r + r₂ : ℕ) : ℝ) * (((r + s : ℕ) : ℝ) - ((r + r₂ : ℕ) : ℝ)) / 2 * (Module.finrank ℚ E : ℝ)` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem RS_exp (hU : IsAutSt U) (hNP : NonPos U) (hT : IsSliceMap U c T) :
    ∀ φ ∈ RS U T, ∀ r₂, 0 < r₂ → r₂ < s → ∀ c₂ ∈ Exp r₂ φ.1,
      c₂.re ≤ (Module.finrank ℚ E : ℝ) * (((r + r₂ : ℕ) : ℝ) * (((r + s : ℕ) : ℝ) - ((r + r₂ : ℕ) : ℝ))) / 2 - c.re := by
  refine BlockExponential.exp_span _ (fun r₂ => (Module.finrank ℚ E : ℝ) * (((r + r₂ : ℕ) : ℝ) *
    (((r + s : ℕ) : ℝ) - ((r + r₂ : ℕ) : ℝ))) / 2 - c.re) (fun φ hφ => BlockSlices.RS_aut hT φ (Submodule.subset_span hφ)) ?_
  rintro ℓ ⟨ψ, hψ, k, g, m₁, hℓ⟩ r₂ hr₂ hrs c₂ hc₂
  obtain ⟨ψ₂, -, h1, -, hexp⟩ := hT.right ψ hψ k g m₁
  have e : ℓ = ψ₂ := Subtype.ext (funext fun m₂ => (hℓ m₂).trans (h1 m₂).symm)
  rw [e] at hc₂
  obtain ⟨φ, hφ, hcφ⟩ := hexp r₂ hr₂ hrs c₂ hc₂
  have h := hNP φ hφ (r + r₂) (by omega) (by omega) (c + c₂) hcφ
  have hd := d_pos (E := E)
  unfold pE at h
  rw [Complex.add_re] at h
  have h2 : (c.re + c₂.re) / (Module.finrank ℚ E : ℝ) ≤
      ((r + r₂ : ℕ) : ℝ) * (((r + s : ℕ) : ℝ) - ((r + r₂ : ℕ) : ℝ)) / 2 := by linarith
  rw [div_le_iff₀ hd] at h2
  have e2 : (Module.finrank ℚ E : ℝ) * (((r + r₂ : ℕ) : ℝ) * (((r + s : ℕ) : ℝ) - ((r + r₂ : ℕ) : ℝ))) / 2 =
      ((r + r₂ : ℕ) : ℝ) * (((r + s : ℕ) : ℝ) - ((r + r₂ : ℕ) : ℝ)) / 2 * (Module.finrank ℚ E : ℝ) := by ring
  linarith

/- English proof (translation)
Introduce `φ hφ t m`. Proceed by induction on `hφ using Submodule.span_induction generalizing m with`. Consider the case `mem x hx`. Take `⟨ψ, hψ, k, g, m₂, hx⟩` from `hx`. Take `⟨ψ₁, -, h1, hc, -⟩` from `hT.left ψ hψ k g m₂`.

Establish `e : x = ψ₁` using `Subtype.ext (funext fun m₁ => (hx m₁).trans (h1 m₁).symm)`. Rewrite using `[e]`. Conclude with `hc t m`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`.

Express the relevant statement in the definitionally equal form `x.1 _ + y.1 _ = _ * (x.1 m + y.1 m)`. Rewrite using `[hx, hy, mul_add]`. Consider the case `smul a x _ hx`. Express the relevant statement in the definitionally equal form `a * x.1 _ = _ * (a * x.1 m)`. Rewrite using `[hx]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem LS_cent (hT : IsSliceMap U c T) :
    ∀ φ ∈ LS U T, ∀ (t : ℝ) m, φ.1 (splitCentre E r t * m) = Complex.exp (c * t) * φ.1 m := by
  intro φ hφ t m
  induction hφ using Submodule.span_induction generalizing m with
  | mem x hx =>
    obtain ⟨ψ, hψ, k, g, m₂, hx⟩ := hx
    obtain ⟨ψ₁, -, h1, hc, -⟩ := hT.left ψ hψ k g m₂
    have e : x = ψ₁ := Subtype.ext (funext fun m₁ => (hx m₁).trans (h1 m₁).symm)
    rw [e]
    exact hc t m
  | zero => simp
  | add x y _ _ hx hy =>
    change x.1 _ + y.1 _ = _ * (x.1 m + y.1 m)
    rw [hx, hy, mul_add]
  | smul a x _ hx =>
    change a * x.1 _ = _ * (a * x.1 m)
    rw [hx]
    ring

/- English proof (translation)
Introduce `φ hφ t m`. Proceed by induction on `hφ using Submodule.span_induction generalizing m with`. Consider the case `mem x hx`. Take `⟨ψ, hψ, k, g, m₁, hx⟩` from `hx`. Take `⟨ψ₂, -, h1, hc, -⟩` from `hT.right ψ hψ k g m₁`.

Establish `e : x = ψ₂` using `Subtype.ext (funext fun m₂ => (hx m₂).trans (h1 m₂).symm)`. Rewrite using `[e]`. Conclude with `hc t m`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`.

Express the relevant statement in the definitionally equal form `x.1 _ + y.1 _ = _ * (x.1 m + y.1 m)`. Rewrite using `[hx, hy, mul_add]`. Consider the case `smul a x _ hx`. Express the relevant statement in the definitionally equal form `a * x.1 _ = _ * (a * x.1 m)`. Rewrite using `[hx]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem RS_cent (hT : IsSliceMap U c T) :
    ∀ φ ∈ RS U T, ∀ (t : ℝ) m, φ.1 (splitCentre E s t * m) = Complex.exp (-c * t) * φ.1 m := by
  intro φ hφ t m
  induction hφ using Submodule.span_induction generalizing m with
  | mem x hx =>
    obtain ⟨ψ, hψ, k, g, m₁, hx⟩ := hx
    obtain ⟨ψ₂, -, h1, hc, -⟩ := hT.right ψ hψ k g m₁
    have e : x = ψ₂ := Subtype.ext (funext fun m₂ => (hx m₂).trans (h1 m₂).symm)
    rw [e]
    exact hc t m
  | zero => simp
  | add x y _ _ hx hy =>
    change x.1 _ + y.1 _ = _ * (x.1 m + y.1 m)
    rw [hx, hy, mul_add]
  | smul a x _ hx =>
    change a * x.1 _ = _ * (a * x.1 m)
    rw [hx]
    ring

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAssembly

end
