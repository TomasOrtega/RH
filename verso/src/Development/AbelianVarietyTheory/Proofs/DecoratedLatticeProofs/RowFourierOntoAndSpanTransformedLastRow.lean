import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpanSchwartzBruhatProductEqTop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdFnMemSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocMod.LastRow

open GlobalTheory.LocFlat.CFac

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

/- English proof (translation)
Use `secondCountable k` as an intermediate fact. Use `t2Space k` as an intermediate fact. Take `⟨c, hc⟩` from `(conductor_exists k).1 ψ hψ hne`. Establish `hpsi : ∀ u : k, (ψ (-u) : ℂ) * ψ u = 1`. Introduce `u`.

Rewrite using `[← Circle.coe_mul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, Circle.coe_one]`. Use `⟨(nabs k c * ν.real (𝒪[k] : Set k) ^ 2) ^ Fintype.card I, ?_, fun a g hg => ?_⟩` and prove the remaining obligations. Establish `hO : 0 < ν.real (𝒪[k] : Set k)` using `ENNReal.toReal_pos ((isOpen_int k).measure_pos ν ⟨0, zero_mem _⟩).ne' (isCompact_int k).measure_lt_top.ne`. Use `nabs_pos k c` as an intermediate fact. Check the signs of the components of the expression.

Use `set μI : Measure (I → k) := Measure.pi fun _ => ν with hμI`. Use `set h : (I → k) → ℂ := fun x => g (x + a) with hhdef`. Establish `hh : h ∈ SB (I → k)` using `⟨hg.1.comp_continuous (continuous_add_const a), hg.2.comp_homeomorph (Homeomorph.addRight a)⟩`. Establish `htr : ∀ l : I → k, (ψ (-(l ⬝ᵥ a)) : ℂ) * ∫ x₁, g x₁ * (ψ (x₁ ⬝ᵥ l) : ℂ) ∂μI = ∫ x, h x * (ψ (x ⬝ᵥ l) : ℂ) ∂μI`. Introduce `l`.

Rewrite using `[← integral_const_mul, ← integral_add_right_eq_self _ a]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Establish `e1 : (x + a) ⬝ᵥ l = x ⬝ᵥ l + l ⬝ᵥ a` using `by rw [add_dotProduct, dotProduct_comm a l]`. Rewrite using `[hhdef, e1, AddChar.map_add_eq_mul, Circle.coe_mul]`.

Take the linear combination `(g (x + a) * (ψ (x ⬝ᵥ l) : ℂ)) * hpsi (l ⬝ᵥ a)`. Simplify using `only [htr]`. Take `⟨s, hs⟩` from `FourierPi.fourier_inversion_pi μI hc hh`. Establish `hb : ∀ r : kˣ, μI.real (FourierPi.box I r) = ν.real (cball r) ^ Fintype.card I`. Introduce `r`.

Simplify using `[hμI, Measure.real, FourierPi.box, Measure.pi_pi]`. Rewrite using `[hs, hb, hb, ← mul_pow, measureReal_cball, measureReal_cball]`. Establish `h4 : nabs k c = nabs k s * nabs k (c * s⁻¹)`. Rewrite using `[← nabs_mul, mul_comm, inv_mul_cancel_right]`. Simplify using `only [hhdef, zero_add, h4]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fourier_inversion_const (ψ : AddChar k Circle) (ν : Measure k) (hψ : Continuous ψ) (hne : ψ ≠ 1)
    [ν.IsAddHaarMeasure] (I : Type) [Fintype I] :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : I → k) (g : (I → k) → ℂ), g ∈ SB (I → k) →
      ∫ l : I → k, (ψ (-(l ⬝ᵥ a)) : ℂ) * (∫ x, g x * (ψ (x ⬝ᵥ l) : ℂ) ∂(Measure.pi fun _ => ν))
        ∂(Measure.pi fun _ => ν) = (C : ℂ) * g a := by
  classical
  have := secondCountable k
  have := t2Space k
  obtain ⟨c, hc⟩ := (conductor_exists k).1 ψ hψ hne
  have hpsi : ∀ u : k, (ψ (-u) : ℂ) * ψ u = 1 := by
    intro u
    rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, Circle.coe_one]
  refine ⟨(nabs k c * ν.real (𝒪[k] : Set k) ^ 2) ^ Fintype.card I, ?_, fun a g hg => ?_⟩
  · have hO : 0 < ν.real (𝒪[k] : Set k) :=
      ENNReal.toReal_pos ((isOpen_int k).measure_pos ν ⟨0, zero_mem _⟩).ne' (isCompact_int k).measure_lt_top.ne
    have := nabs_pos k c
    positivity
  set μI : Measure (I → k) := Measure.pi fun _ => ν with hμI
  set h : (I → k) → ℂ := fun x => g (x + a) with hhdef
  have hh : h ∈ SB (I → k) :=
    ⟨hg.1.comp_continuous (continuous_add_const a), hg.2.comp_homeomorph (Homeomorph.addRight a)⟩
  have htr : ∀ l : I → k, (ψ (-(l ⬝ᵥ a)) : ℂ) * ∫ x₁, g x₁ * (ψ (x₁ ⬝ᵥ l) : ℂ) ∂μI =
      ∫ x, h x * (ψ (x ⬝ᵥ l) : ℂ) ∂μI := by
    intro l
    rw [← integral_const_mul, ← integral_add_right_eq_self _ a]
    congr 1
    funext x
    have e1 : (x + a) ⬝ᵥ l = x ⬝ᵥ l + l ⬝ᵥ a := by rw [add_dotProduct, dotProduct_comm a l]
    rw [hhdef, e1, AddChar.map_add_eq_mul, Circle.coe_mul]
    linear_combination (g (x + a) * (ψ (x ⬝ᵥ l) : ℂ)) * hpsi (l ⬝ᵥ a)
  simp only [htr]
  obtain ⟨s, hs⟩ := FourierPi.fourier_inversion_pi μI hc hh
  have hb : ∀ r : kˣ, μI.real (FourierPi.box I r) = ν.real (cball r) ^ Fintype.card I := by
    intro r
    simp [hμI, Measure.real, FourierPi.box, Measure.pi_pi]
  rw [hs, hb, hb, ← mul_pow, measureReal_cball, measureReal_cball]
  have h4 : nabs k c = nabs k s * nabs k (c * s⁻¹) := by
    rw [← nabs_mul, mul_comm, inv_mul_cancel_right]
  simp only [hhdef, zero_add, h4]
  push_cast
  ring

end GlobalTheory.LocMod.LastRow

namespace GlobalTheory.LocMod.LastRow

open GlobalTheory.LocFlat.CFac

/- English proof (translation)
Introduce `k _ _ _ _ _ _ ν hν ψk hψ hne n Z _ _ _ _`. Use `haveI := hν`. Use `haveI := secondCountable k`. Use `haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k`. Use `haveI : NonarchimedeanAddGroup k := ⟨fun V hV => by`.

Take `⟨s, hs⟩` from `GlobalTheory.SplitWeil.exists_cball_subset hV`. Conclude with `⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩, GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩`. Use `haveI : TotallyDisconnectedSpace k := inferInstance`. Use `haveI hTD : ∀ (a b : Type) [Fintype a] [Fintype b], TotallyDisconnectedSpace (Matrix a b k) := fun a b _ _ => inferInstanceAs (TotallyDisconnectedSpace (a → b → k))`. Use `haveI hLC : ∀ (a b : Type) [Fintype a] [Fintype b], LocallyCompactSpace (Matrix a b k) := fun a b _ _ => inferInstanceAs (LocallyCompactSpace (a → b → k))`.

Use `haveI hT2 : ∀ (a b : Type), T2Space (Matrix a b k) := fun a b => inferInstanceAs (T2Space (a → b → k))`. Establish `part1 : ∀ b : SB (Matrix Unit n k), ∃ c : SB (Matrix n Unit k), ∀ η, b.1 η = GlobalTheory.StepData.hat ψk ν (-1) (fun y => c.1 (Matrix.of fun r _ => y r)) (η ())`. Take `⟨C, hC, hinv⟩` from `fourier_inversion_const ψk ν hψ hne n`. Take `⟨c0, hc0⟩` from `(conductor_exists k).1 ψk hψ hne`. Introduce `b`.

Set `e1 : (n → k) ≃ₜ Matrix Unit n k` to `(Homeomorph.funUnique Unit (n → k)).symm`. Set `g : SB (n → k)` to `comapH e1 b`. Establish `hF` using `FourierPi.fourier_mem_SB (Measure.pi fun _ : n => ν) hc0 g.2`. Set `e2 : Matrix n Unit k ≃ₜ (n → k)` to `Homeomorph.piCongrRight fun _ => Homeomorph.funUnique Unit k`. Use `⟨((C : ℂ)⁻¹) • comapH e2 ⟨_, hF⟩, fun η => ?_⟩` and prove the remaining obligations.

Unfold `GlobalTheory.StepData.hat`. Establish `e3 : ∀ y : n → k, ((((C : ℂ)⁻¹) • comapH e2 ⟨_, hF⟩ : SB (Matrix n Unit k)).1 (Matrix.of fun r _ => y r)) * (ψk ((-1) * (η () ⬝ᵥ y)) : ℂ) = (C : ℂ)⁻¹ * ((ψk (-(y ⬝ᵥ η ())) : ℂ) * ∫ x, g.1 x * (ψk (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν))`. Introduce `y`. Rewrite using `[neg_one_mul, dotProduct_comm]`. Express the relevant statement in the definitionally equal form `(C : ℂ)⁻¹ * (∫ x, g.1 x * (ψk (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) * _ = _`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [e3]`. Rewrite using `[integral_const_mul, hinv (η ()) g.1 g.2, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hC.ne'), one_mul]`. Both sides reduce to the same expression. Use `⟨part1, fun Ξ₂ => ?_⟩` and prove the remaining obligations.

Set `e : Matrix (Z ⊕ Unit) n k ≃ₜ Matrix Z n k × Matrix Unit n k` to `Homeomorph.sumArrowHomeomorphProdArrow`. Establish `hspan` using `GlobalTheory.LocFlat.CFac.Span.span_prodSB_eq_top (Matrix Z n k) (Matrix Unit n k)`. Establish `hmem : comapH e.symm Ξ₂ ∈ Submodule.span ℂ (Set.range fun q : SB (Matrix Z n k) × SB (Matrix Unit n k) => prodSB q.1 q.2)`. Rewrite using `[hspan]`. Discharge the goal by the elementary cases of `trivial`.

Take `⟨N, f, q, hq⟩` from `Submodule.mem_span_set'.mp hmem`. Use `choose p hp using fun i => (q i).2`. Use `choose c hc using fun i => part1 (p i).2`. Use `⟨N, fun i => f i • (p i).1, c, fun i => comapH e (prodSB (f i • (p i).1) (p i).2), fun i x => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[comapH_apply, prodSB_apply]`.

Use `congr 1`. Conclude with `hc i _`. Establish `h1 : Ξ₂ = comapH e (comapH e.symm Ξ₂)`. Use extensionality with `x`. Simplify using `only [comapH_apply, Homeomorph.symm_apply_apply]`.

Rewrite using `[h1, ← hq, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, ← hp i]`. Use extensionality with `x`. Simplify using `only [comapH_apply, prodSB_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]`.
-/
theorem transform_onto_and_span_lastRow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψk : AddChar k Circle), Continuous ψk → ψk ≠ 1 → ∀ (n Z : Type) [Fintype n] [DecidableEq n] [Fintype Z] [DecidableEq Z], (∀ b : SB (Matrix Unit n k), ∃ c : SB (Matrix n Unit k), ∀ η, b.1 η = GlobalTheory.StepData.hat ψk ν (-1) (fun y => c.1 (Matrix.of fun r _ => y r)) (η ())) ∧ ∀ Ξ₂ : SB (Matrix (Z ⊕ Unit) n k), ∃ (N : ℕ) (a : Fin N → SB (Matrix Z n k)) (c : Fin N → SB (Matrix n Unit k)) (g : Fin N → SB (Matrix (Z ⊕ Unit) n k)), (∀ i x, (g i).1 x = (a i).1 x.toRows₁ * GlobalTheory.StepData.hat ψk ν (-1) (fun y => (c i).1 (Matrix.of fun r _ => y r)) (x (Sum.inr ()))) ∧ Ξ₂ = ∑ i, g i := by
  intro k _ _ _ _ _ _ ν hν ψk hψ hne n Z _ _ _ _
  haveI := hν
  haveI := secondCountable k
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
      GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
  haveI : TotallyDisconnectedSpace k := inferInstance
  haveI hTD : ∀ (a b : Type) [Fintype a] [Fintype b], TotallyDisconnectedSpace (Matrix a b k) :=
    fun a b _ _ => inferInstanceAs (TotallyDisconnectedSpace (a → b → k))
  haveI hLC : ∀ (a b : Type) [Fintype a] [Fintype b], LocallyCompactSpace (Matrix a b k) :=
    fun a b _ _ => inferInstanceAs (LocallyCompactSpace (a → b → k))
  haveI hT2 : ∀ (a b : Type), T2Space (Matrix a b k) := fun a b => inferInstanceAs (T2Space (a → b → k))
  have part1 : ∀ b : SB (Matrix Unit n k), ∃ c : SB (Matrix n Unit k), ∀ η,
      b.1 η = GlobalTheory.StepData.hat ψk ν (-1) (fun y => c.1 (Matrix.of fun r _ => y r)) (η ()) := by
    obtain ⟨C, hC, hinv⟩ := fourier_inversion_const ψk ν hψ hne n
    obtain ⟨c0, hc0⟩ := (conductor_exists k).1 ψk hψ hne
    intro b
    let e1 : (n → k) ≃ₜ Matrix Unit n k := (Homeomorph.funUnique Unit (n → k)).symm
    let g : SB (n → k) := comapH e1 b
    have hF := FourierPi.fourier_mem_SB (Measure.pi fun _ : n => ν) hc0 g.2
    let e2 : Matrix n Unit k ≃ₜ (n → k) := Homeomorph.piCongrRight fun _ => Homeomorph.funUnique Unit k
    refine ⟨((C : ℂ)⁻¹) • comapH e2 ⟨_, hF⟩, fun η => ?_⟩
    unfold GlobalTheory.StepData.hat
    have e3 : ∀ y : n → k, ((((C : ℂ)⁻¹) • comapH e2 ⟨_, hF⟩ : SB (Matrix n Unit k)).1
        (Matrix.of fun r _ => y r)) * (ψk ((-1) * (η () ⬝ᵥ y)) : ℂ) =
        (C : ℂ)⁻¹ * ((ψk (-(y ⬝ᵥ η ())) : ℂ) * ∫ x, g.1 x * (ψk (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) := by
      intro y
      rw [neg_one_mul, dotProduct_comm]
      change (C : ℂ)⁻¹ * (∫ x, g.1 x * (ψk (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) * _ = _
      ring
    simp only [e3]
    rw [integral_const_mul, hinv (η ()) g.1 g.2, ← mul_assoc,
      inv_mul_cancel₀ (by exact_mod_cast hC.ne'), one_mul]
    rfl
  refine ⟨part1, fun Ξ₂ => ?_⟩
  let e : Matrix (Z ⊕ Unit) n k ≃ₜ Matrix Z n k × Matrix Unit n k := Homeomorph.sumArrowHomeomorphProdArrow
  have hspan := GlobalTheory.LocFlat.CFac.Span.span_prodSB_eq_top (Matrix Z n k) (Matrix Unit n k)
  have hmem : comapH e.symm Ξ₂ ∈ Submodule.span ℂ
      (Set.range fun q : SB (Matrix Z n k) × SB (Matrix Unit n k) => prodSB q.1 q.2) := by
    rw [hspan]; trivial
  obtain ⟨N, f, q, hq⟩ := Submodule.mem_span_set'.mp hmem
  choose p hp using fun i => (q i).2
  choose c hc using fun i => part1 (p i).2
  refine ⟨N, fun i => f i • (p i).1, c, fun i => comapH e (prodSB (f i • (p i).1) (p i).2), fun i x => ?_, ?_⟩
  · rw [comapH_apply, prodSB_apply]
    congr 1
    exact hc i _
  · have h1 : Ξ₂ = comapH e (comapH e.symm Ξ₂) := by
      ext x; simp only [comapH_apply, Homeomorph.symm_apply_apply]
    rw [h1, ← hq, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, ← hp i]
    ext x
    simp only [comapH_apply, prodSB_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]

end GlobalTheory.LocMod.LastRow
