import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.PhiZBijective

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Groth

/- English proof (translation)
Unfold `cl0`. Rewrite using `[dif_pos h]`.
-/
theorem GrothendieckClassGeneralLinear.class_gl_eq_class {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (h : HasFiniteLength π) :
    clsGL π h = cl0 π := by
  unfold cl0; rw [dif_pos h]

/- English proof (translation)
Introduce `k _ _ _ _ Z hZ`. Take `⟨hCls, hMul, hAs, hCo, hOne, hPL, hTri, hMO, hJC, hJS, hAlt⟩` from `H k`. Use `haveI : Fact (Assoc k) := ⟨hAs⟩`. Use `haveI : Fact (Comm k) := ⟨hCo⟩`. Use `haveI : Fact (One k) := ⟨hOne⟩`.

Establish `hst : Steps k` using `⟨hCls, hMul, hAs, hCo, hOne, hPL, hTri, hMO, hJC, hJS, hAlt⟩`. Establish `hbij` using `phiZ_bijective hst h1 h2 Z hZ`. Set `e` to `RingEquiv.ofBijective (phiOf fun Δ : Segment k => (⟨Δ.len * Δ.d, Z Δ⟩ : IrrGL k)) hbij`. Use `⟨toR.trans e.symm.toAddEquiv, ?_, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `e.symm (toR (GrothGL.unit k)) = 1`.

Rewrite using `[toR_unit, map_one]`. Introduce `r t V W _ _ _ _ π₁ π₂ h₁ h₂ s₁ s₂ h`. Take `⟨_, hc⟩` from `hMul r t V W π₁ π₂ h₁ h₂ s₁ s₂`. Express the relevant statement in the definitionally equal form `e.symm (toR (clsGL (prod₂ π₁ π₂) h)) = e.symm (toR (clsGL π₁ h₁)) * e.symm (toR (clsGL π₂ h₂))`. Rewrite using `[GrothendieckClassGeneralLinear.class_gl_eq_class, GrothendieckClassGeneralLinear.class_gl_eq_class, GrothendieckClassGeneralLinear.class_gl_eq_class, hc, toR_mulR, map_mul]`.

Introduce `Δ`. Express the relevant statement in the definitionally equal form `e.symm (toR (sg (⟨Δ.len * Δ.d, Z Δ⟩ : IrrGL k))) = MvPolynomial.X Δ`. Rewrite using `[RingEquiv.symm_apply_eq]`. Conclude with `(phiOf_X (fun Δ : Segment k => (⟨Δ.len * Δ.d, Z Δ⟩ : IrrGL k)) Δ).symm`.
-/
theorem groth_of_steps (H : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      Cls k ∧ MulCls k ∧ Assoc k ∧ Comm k ∧ One k ∧ ProdList k ∧ Tri k ∧ MultOne k ∧ JCls k ∧ JSeg k ∧ AltSum k)
    (h1 : TriAut) (h2 : UniTri) : GlobalTheory.Published.GrothendieckRingPolynomial := by
  intro k _ _ _ _ Z hZ
  obtain ⟨hCls, hMul, hAs, hCo, hOne, hPL, hTri, hMO, hJC, hJS, hAlt⟩ := H k
  haveI : Fact (Assoc k) := ⟨hAs⟩
  haveI : Fact (Comm k) := ⟨hCo⟩
  haveI : Fact (One k) := ⟨hOne⟩
  have hst : Steps k := ⟨hCls, hMul, hAs, hCo, hOne, hPL, hTri, hMO, hJC, hJS, hAlt⟩
  have hbij := phiZ_bijective hst h1 h2 Z hZ
  let e := RingEquiv.ofBijective (phiOf fun Δ : Segment k => (⟨Δ.len * Δ.d, Z Δ⟩ : IrrGL k)) hbij
  refine ⟨toR.trans e.symm.toAddEquiv, ?_, ?_, ?_⟩
  · change e.symm (toR (GrothGL.unit k)) = 1
    rw [toR_unit, map_one]
  · intro r t V W _ _ _ _ π₁ π₂ h₁ h₂ s₁ s₂ h
    obtain ⟨_, hc⟩ := hMul r t V W π₁ π₂ h₁ h₂ s₁ s₂
    change e.symm (toR (clsGL (prod₂ π₁ π₂) h)) =
      e.symm (toR (clsGL π₁ h₁)) * e.symm (toR (clsGL π₂ h₂))
    rw [GrothendieckClassGeneralLinear.class_gl_eq_class, GrothendieckClassGeneralLinear.class_gl_eq_class, GrothendieckClassGeneralLinear.class_gl_eq_class, hc, toR_mulR, map_mul]
  · intro Δ
    change e.symm (toR (sg (⟨Δ.len * Δ.d, Z Δ⟩ : IrrGL k))) = MvPolynomial.X Δ
    rw [RingEquiv.symm_apply_eq]
    exact (phiOf_X (fun Δ : Segment k => (⟨Δ.len * Δ.d, Z Δ⟩ : IrrGL k)) Δ).symm

end PositivityTheory.Groth

end
