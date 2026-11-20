import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.SqUniq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

/- English proof (translation)
Rewrite using `[isOpen_iff_forall_mem_open]`. Introduce `g hg`. Use `⟨(fun x => g⁻¹ * x) ⁻¹' S, fun x hx => ?_, hS.preimage (by fun_prop), by simpa using h1⟩` and prove the remaining obligations. Establish `e : x = g * (g⁻¹ * x)` using `by group`. Establish `hg' : ρ g v = v` using `hg`.

Use `show ρ x v = v`. Rewrite using `[e, map_mul, Module.End.mul_apply, h _ hx, hg']`.
-/
private theorem open_fix {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) {S : Set G} (hS : IsOpen S) (h1 : (1 : G) ∈ S) (h : ∀ g ∈ S, ρ g v = v) :
    IsOpen {g | ρ g v = v} := by
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' S, fun x hx => ?_, hS.preimage (by fun_prop), by simpa using h1⟩
  have e : x = g * (g⁻¹ * x) := by group
  have hg' : ρ g v = v := hg
  show ρ x v = v
  rw [e, map_mul, Module.End.mul_apply, h _ hx, hg']

/- English proof (translation)
Introduce `E _ _ _ a ha μ _ r χ hχ φ hφ`. Express the relevant statement in the definitionally equal form `IsOpen {k | finRep E a k (mulChi a χ φ) = mulChi a χ φ} ∧ _`. Proceed by induction on `hφ using Submodule.span_induction with`. Consider the case `mem φ h`. Establish `hl : IsOpen {k | finRep E a k φ = φ}` using `h.level`.

Establish `ho : IsOpen {k | finRep E a k (mulChi a χ φ) = mulChi a χ φ}`. Use `open_fix (finRep E a) _ (hl.inter (isOpen_ker_chiDet (a := a) χ)) ⟨by simp, by simp⟩ ?_` and prove the remaining obligations. Introduce and unpack `k ⟨h1, h2⟩`. Establish `h1' : rt E a (finGL E a k) φ = φ` using `h1`. Establish `h2' : chiDet a χ (finGL E a k) = 1` using `h2`.

Express the relevant statement in the definitionally equal form `rt E a (finGL E a k) (mulChi a χ φ) = _`. Rewrite using `[rt_mulChi, h1', h2']`. Simplify using the standard rewrite rules. Establish `hs` using `sqUniq E a ha r χ hχ φ h.one (by simpa using h.sq [])`. Use `⟨ho, (CuspidalL2GL.memL2_iff_isSqInt (ContAut.continuous_of_isOpen_stab E a _ ho) (fun γ g => ?_) hs.1).2 hs⟩` and prove the remaining obligations.

Rewrite using `[mulChi_apply, mulChi_apply, map_mul, chiDet_ratGL, one_mul, h.left]`. Consider the case `zero`. Rewrite using `[map_zero]`. Conclude with `⟨by simp, fun _ _ _ => rfl, MeasureTheory.MemLp.zero⟩`. Consider the case `add φ ψ _ _ h h'`.

Rewrite using `[map_add]`. Use `⟨open_fix (finRep E a) _ (h.1.inter h'.1) ⟨by simp, by simp⟩ ?_, fun γ hγ g => congrArg₂ (· + ·) (h.2.1 γ hγ g) (h'.2.1 γ hγ g), h.2.2.add h'.2.2⟩` and prove the remaining obligations. Introduce and unpack `k ⟨h1, h2⟩`. Conclude with `(map_add _ _ _).trans (congrArg₂ (· + ·) h1 h2)`. Consider the case `smul c φ _ h`.

Rewrite using `[map_smul]`. Use `⟨open_fix (finRep E a) _ h.1 (by simp) ?_, fun γ hγ g => congrArg (c • ·) (h.2.1 γ hγ g), h.2.2.const_smul c⟩` and prove the remaining obligations. Introduce `k h1`. Conclude with `(map_smul _ _ _).trans (congrArg (c • ·) h1)`.
-/
theorem UpperTheory.V.Lit.Bor.sqMem :
    UpperTheory.V.Lit.Bor.SqMem := by
  intro E _ _ _ a ha μ _ r χ hχ φ hφ
  change IsOpen {k | finRep E a k (mulChi a χ φ) = mulChi a χ φ} ∧ _
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    have hl : IsOpen {k | finRep E a k φ = φ} := h.level
    have ho : IsOpen {k | finRep E a k (mulChi a χ φ) = mulChi a χ φ} := by
      refine open_fix (finRep E a) _ (hl.inter (isOpen_ker_chiDet (a := a) χ)) ⟨by simp, by simp⟩ ?_
      rintro k ⟨h1, h2⟩
      have h1' : rt E a (finGL E a k) φ = φ := h1
      have h2' : chiDet a χ (finGL E a k) = 1 := h2
      change rt E a (finGL E a k) (mulChi a χ φ) = _
      rw [rt_mulChi, h1', h2']
      simp
    have hs := sqUniq E a ha r χ hχ φ h.one (by simpa using h.sq [])
    refine ⟨ho, (CuspidalL2GL.memL2_iff_isSqInt (ContAut.continuous_of_isOpen_stab E a _ ho) (fun γ g => ?_) hs.1).2 hs⟩
    rw [mulChi_apply, mulChi_apply, map_mul, chiDet_ratGL, one_mul, h.left]
  | zero =>
    rw [map_zero]
    exact ⟨by simp, fun _ _ _ => rfl, MeasureTheory.MemLp.zero⟩
  | add φ ψ _ _ h h' =>
    rw [map_add]
    refine ⟨open_fix (finRep E a) _ (h.1.inter h'.1) ⟨by simp, by simp⟩ ?_,
      fun γ hγ g => congrArg₂ (· + ·) (h.2.1 γ hγ g) (h'.2.1 γ hγ g), h.2.2.add h'.2.2⟩
    rintro k ⟨h1, h2⟩
    exact (map_add _ _ _).trans (congrArg₂ (· + ·) h1 h2)
  | smul c φ _ h =>
    rw [map_smul]
    refine ⟨open_fix (finRep E a) _ h.1 (by simp) ?_,
      fun γ hγ g => congrArg (c • ·) (h.2.1 γ hγ g), h.2.2.const_smul c⟩
    intro k h1
    exact (map_smul _ _ _).trans (congrArg (c • ·) h1)
