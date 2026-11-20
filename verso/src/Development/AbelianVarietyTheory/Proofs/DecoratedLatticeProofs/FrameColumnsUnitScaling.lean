import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SymRead
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqSecAddCsec
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatMapSupportProof
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PrimSplitLine

open GlobalTheory.FinPl GlobalTheory.FinPl.FrameLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Rewrite using `[← sec_mul_right, RingHom.map_mul, cA_cA]`.
-/
theorem cA_sec_mul' (p : SplitPt D k) (a : AE D) (t : k) :
    cA D (p.sec t) * a = cA D (p.sec (t * p.pr (cA D a))) := by
  rw [← sec_mul_right, RingHom.map_mul, cA_cA]

/- English proof (translation)
Use function extensionality and compare the values at `r`. Express the relevant statement in the definitionally equal form `a * incA D (d.e r i) = _`. Use `conv_lhs => rw [GlobalTheory.SplitIntComp.eq_sec_add_csec q ha]`. Rewrite using `[add_mul, sec_mul_right, cA_sec_mul' q, Pi.add_apply]`.
-/
theorem colMul_split (q : SplitPt D k) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) {a : AE D}
    (ha : a ∈ idAt D (· = q.v)) :
    colMul d.jX i a = (fun r => q.sec (q.pr a * q.pr (incA D (d.e r i)))) +
      (fun r => cA D (q.sec (q.pr (cA D a) * q.pr (cA D (incA D (d.e r i)))))) := by
  funext r
  change a * incA D (d.e r i) = _
  conv_lhs => rw [GlobalTheory.SplitIntComp.eq_sec_add_csec q ha]
  rw [add_mul, sec_mul_right, cA_sec_mul' q, Pi.add_apply]

/- English proof (translation)
Rewrite using `[Valuation.mem_integer_iff, Valuation.mem_integer_iff, Valuation.map_mul, hu, mul_one]`.
-/
theorem mul_unit_mem_iff {b u : k} (hu : valuation k u = 1) : b * u ∈ 𝒪[k] ↔ b ∈ 𝒪[k] := by
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, Valuation.map_mul, hu, mul_one]

/- English proof (translation)
Introduce `D k _ _ _ _ q S S₀ ρ d L Y _ _ F i y₁ y₂ u₁ u₂ hL hF hu₁ hu₂ hcol₁ hcol₂ a`. Establish `hu₁0 : u₁ ≠ 0`. Introduce and unpack `rfl`. Rewrite `hu₁` using `[Valuation.map_zero]`. Conclude with `zero_ne_one hu₁`.

Establish `hu₂i : u₂ ∈ 𝒪[k]` using `(Valuation.mem_integer_iff _ _).2 hu₂.le`. Establish `key : ∀ a ∈ idAt D (· = q.v), (colMul d.jX i a ∈ latV S L (· = q.v) ↔ q.pr a ∈ 𝒪[k] ∧ q.pr (cA D a) ∈ 𝒪[k])`. Introduce `a ha`. Rewrite using `[colMul_split q d i ha, decomp hL]`. Use `and_congr ?_ ?_` and prove the remaining obligations.

Establish `h1 : (fun r => q.sec (q.pr a * q.pr (incA D (d.e r i)))) = fun r => q.sec ((F.β *ᵥ Pi.single y₁ (q.pr a * u₁⁻¹)) r)`. Use function extensionality and compare the values at `r`. Use `congr 1`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, hcol₁]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[h1, ← hF]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `h y₁` as an intermediate fact. Rewrite `this` using `[Pi.single_eq_same]`.

Rewrite `this` using `[mul_unit_mem_iff (by rw [map_inv₀, hu₁, inv_one])]`. Then use the resulting hypothesis. Introduce `h j`. Distinguish the cases in `hj : j = y₁`. Substitute `hj` using the available equality. Rewrite using `[Pi.single_eq_same, mul_unit_mem_iff (by rw [map_inv₀, hu₁, inv_one])]`.

Conclude with `h`. Rewrite using `[Pi.single_eq_of_ne hj]`. Conclude with `zero_mem _`. Rewrite using `[csec_mem_iff hL] set b := q.pr (cA D a) with hb`. Establish `hsum : ∀ y : Y → k, ∑ r, ∑ t, (F.β *ᵥ y) r * q.pr (cA D (incA D (HSpace.gram S r t))) * (b * q.pr (cA D (incA D (d.e t i)))) = b * u₂ * y y₂`.

Introduce `y`. Establish `hr : b * u₂ * y y₂ = ∑ l, y l * b * (∑ r, ∑ t, F.β r l * q.pr (cA D (incA D (HSpace.gram S r t))) * q.pr (cA D (incA D (d.e t i))))`. Simplify using `only [hcol₂, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hr]`.

Simplify using `only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]`. Use `symm`. Use `Finset.sum_comm.trans (Finset.sum_congr rfl fun r _ => Finset.sum_comm.trans (Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun l _ => ?_))` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `h2` using `h (F.β *ᵥ Pi.single y₂ 1) ((hF _).1 fun j => by`. Distinguish the cases in `hj : j = y₂`. Substitute `hj` using the available equality. Rewrite using `[Pi.single_eq_same]`.

Conclude with `one_mem _`. Rewrite using `[Pi.single_eq_of_ne hj]`. Conclude with `zero_mem _)`. Rewrite `h2` using `[hsum, Pi.single_eq_same, mul_one, mul_unit_mem_iff hu₂]`. Conclude with `h2`.

Introduce `hb' x hx`. Establish `hx' : x = F.β *ᵥ (F.γ *ᵥ x)` using `by rw [Matrix.mulVec_mulVec, F.βγ, Matrix.one_mulVec]`. Rewrite `hx`, the goal using `[hx']`. Rewrite using `[hsum]`. Conclude with `mul_mem (mul_mem hb' hu₂i) ((hF _).2 hx y₂)`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `ha` using `GlobalTheory.FinPl.SuppShift.idAt_of_colMul d h`. Conclude with `(GlobalTheory.SplitIntComp.mem_intAt_iff q ha).2 ((key a ha).1 h)`. Introduce `h`.

Conclude with `(key a h.1).2 ((GlobalTheory.SplitIntComp.mem_intAt_iff q h.1).1 h)`.
-/
theorem colMul_mem_latV_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : GlobalTheory.FinPl.Lat S) (Y : Type) [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y) (i : Fin ρ) (y₁ y₂ : Y) (u₁ u₂ : k), IsSelfDualC S L → IntIn q S F L → valuation k u₁ = 1 → valuation k u₂ = 1 → (∀ r, F.β r y₁ = u₁ * q.pr (incA D (d.e r i))) → (∀ l, ∑ r, ∑ t, F.β r l * q.pr (cA D (incA D (HSpace.gram S r t))) * q.pr (cA D (incA D (d.e t i))) = if l = y₂ then u₂ else 0) → ∀ a : AE D, (GlobalTheory.FinPl.colMul d.jX i a ∈ GlobalTheory.FinPl.latV S L (· = q.v) ↔ a ∈ GlobalTheory.FinPl.intAt D (· = q.v)) := by
  intro D k _ _ _ _ q S S₀ ρ d L Y _ _ F i y₁ y₂ u₁ u₂ hL hF hu₁ hu₂ hcol₁ hcol₂ a
  have hu₁0 : u₁ ≠ 0 := by
    rintro rfl
    rw [Valuation.map_zero] at hu₁
    exact zero_ne_one hu₁
  have hu₂i : u₂ ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 hu₂.le
  have key : ∀ a ∈ idAt D (· = q.v), (colMul d.jX i a ∈ latV S L (· = q.v) ↔
      q.pr a ∈ 𝒪[k] ∧ q.pr (cA D a) ∈ 𝒪[k]) := by
    intro a ha
    rw [colMul_split q d i ha, decomp hL]
    refine and_congr ?_ ?_
    · have h1 : (fun r => q.sec (q.pr a * q.pr (incA D (d.e r i)))) =
          fun r => q.sec ((F.β *ᵥ Pi.single y₁ (q.pr a * u₁⁻¹)) r) := by
        funext r
        congr 1
        simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, hcol₁]
        field_simp
      rw [h1, ← hF]
      constructor
      · intro h
        have := h y₁
        rw [Pi.single_eq_same] at this
        rwa [mul_unit_mem_iff (by rw [map_inv₀, hu₁, inv_one])] at this
      · intro h j
        by_cases hj : j = y₁
        · subst hj
          rw [Pi.single_eq_same, mul_unit_mem_iff (by rw [map_inv₀, hu₁, inv_one])]
          exact h
        · rw [Pi.single_eq_of_ne hj]
          exact zero_mem _
    · rw [csec_mem_iff hL]
      set b := q.pr (cA D a) with hb
      have hsum : ∀ y : Y → k, ∑ r, ∑ t, (F.β *ᵥ y) r * q.pr (cA D (incA D (HSpace.gram S r t))) *
          (b * q.pr (cA D (incA D (d.e t i)))) = b * u₂ * y y₂ := by
        intro y
        have hr : b * u₂ * y y₂ = ∑ l, y l * b * (∑ r, ∑ t, F.β r l * q.pr (cA D (incA D (HSpace.gram S r t))) *
            q.pr (cA D (incA D (d.e t i)))) := by
          simp only [hcol₂, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          ring
        rw [hr]
        simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
        symm
        refine Finset.sum_comm.trans (Finset.sum_congr rfl fun r _ => Finset.sum_comm.trans
          (Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun l _ => ?_))
        ring
      constructor
      · intro h
        have h2 := h (F.β *ᵥ Pi.single y₂ 1) ((hF _).1 fun j => by
          by_cases hj : j = y₂
          · subst hj; rw [Pi.single_eq_same]; exact one_mem _
          · rw [Pi.single_eq_of_ne hj]; exact zero_mem _)
        rw [hsum, Pi.single_eq_same, mul_one, mul_unit_mem_iff hu₂] at h2
        exact h2
      · intro hb' x hx
        have hx' : x = F.β *ᵥ (F.γ *ᵥ x) := by rw [Matrix.mulVec_mulVec, F.βγ, Matrix.one_mulVec]
        rw [hx'] at hx ⊢
        rw [hsum]
        exact mul_mem (mul_mem hb' hu₂i) ((hF _).2 hx y₂)
  constructor
  · intro h
    have ha := GlobalTheory.FinPl.SuppShift.idAt_of_colMul d h
    exact (GlobalTheory.SplitIntComp.mem_intAt_iff q ha).2 ((key a ha).1 h)
  · intro h
    exact (key a h.1).2 ((GlobalTheory.SplitIntComp.mem_intAt_iff q h.1).1 h)

end GlobalTheory.PrimSplitLine

end
