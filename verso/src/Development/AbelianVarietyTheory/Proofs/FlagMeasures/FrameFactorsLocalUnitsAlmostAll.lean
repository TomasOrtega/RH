import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped nonZeroDivisors

namespace GlobalTheory.FrameFactorUnit

open Formalism.MainNotions.S.LocNG IsDedekindDomain
open scoped nonZeroDivisors

variable {D : D7}

/- English proof (translation)
Unfold `ddS`. Rewrite using `[Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.map_eq_bot_iff_of_injective]`. Conclude with `differentIdeal_ne_bot`. Conclude with `FaithfulSMul.algebraMap_injective _ _`.
-/
theorem ddS_ne_zero : ddS D ≠ 0 := by
  unfold ddS
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.map_eq_bot_iff_of_injective]
  · exact differentIdeal_ne_bot
  · exact FaithfulSMul.algebraMap_injective _ _

/- English proof (translation)
Establish `hle : ddS D ≤ 1`. Unfold `ddS`. Conclude with `FractionalIdeal.coeIdeal_le_one`. Establish `h1 : (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≤ (ddS D)⁻¹`. Simplify using `using FractionalIdeal.inv_anti_mono ddS_ne_zero one_ne_zero hle`.

Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ]`. Simplify using `using FractionalIdeal.mul_mem_mul ih (h1 (FractionalIdeal.one_mem_one _))`.
-/
theorem one_mem_inv_pow (k : ℕ) : (1 : D.host.E) ∈ (ddS D)⁻¹ ^ k := by
  have hle : ddS D ≤ 1 := by
    unfold ddS
    exact FractionalIdeal.coeIdeal_le_one
  have h1 : (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≤ (ddS D)⁻¹ := by
    simpa using FractionalIdeal.inv_anti_mono ddS_ne_zero one_ne_zero hle
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    simpa using FractionalIdeal.mul_mem_mul ih (h1 (FractionalIdeal.one_mem_one _))

/- English proof (translation)
Take `⟨b, hb, hint⟩` from `J.isFractional`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Use `⟨Ideal.absNorm (Ideal.span {b}), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]`. Conclude with `hb0`.

Introduce `y hy`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {b}))`. Take `⟨z, hz⟩` from `hint y hy`. Use `⟨c * z, ?_⟩` and prove the remaining obligations. Establish `hz' : (z : E) = (b : E) * y`.

Rewrite `hz` using `[Algebra.smul_def]`. Conclude with `hz`. Establish `hN : ((Ideal.absNorm (Ideal.span {b}) : 𝓞 E) : E) = (Ideal.absNorm (Ideal.span {b}) : E)`. Use `push_cast`. Both sides reduce to the same expression.

Combine the equalities or inequalities in the displayed calculation.
-/
private theorem exists_nat_mul_mem_ringOfIntegers_of_fractionalIdeal {E : Type} [Field E] [NumberField E]
    (J : FractionalIdeal (𝓞 E)⁰ E) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ y ∈ J, ∃ z : 𝓞 E, (N : E) * y = (z : E) := by
  obtain ⟨b, hb, hint⟩ := J.isFractional
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  refine ⟨Ideal.absNorm (Ideal.span {b}), ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hb0
  · intro y hy
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {b}))
    obtain ⟨z, hz⟩ := hint y hy
    refine ⟨c * z, ?_⟩
    have hz' : (z : E) = (b : E) * y := by
      rw [Algebra.smul_def] at hz
      exact hz
    have hN : ((Ideal.absNorm (Ideal.span {b}) : 𝓞 E) : E) = (Ideal.absNorm (Ideal.span {b}) : E) := by
      push_cast
      rfl
    calc (Ideal.absNorm (Ideal.span {b}) : E) * y
        = ((c * b : 𝓞 E) : E) * y := by rw [hc, hN]
      _ = (c : E) * ((b : E) * y) := by push_cast; ring
      _ = (c : E) * (z : E) := by rw [hz']
      _ = ((c * z : 𝓞 E) : E) := by push_cast; ring

/- English proof (translation)
Rewrite using `[(D.s.atP p).O_def]`. Establish `h : IsIntegral ℤ ((D.s.atP p).ιE (z : D.host.E))` using `(RingOfIntegers.isIntegral_coe z).map ((D.s.atP p).ιE.toIntAlgHom)`. Conclude with `h.tower_top`.
-/
private theorem ιE_ringOfIntegers_mem_O (D : D7) (p : PlF D) (z : 𝓞 D.host.E) :
    (D.s.atP p).ιE (z : D.host.E) ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def]
  have h : IsIntegral ℤ ((D.s.atP p).ιE (z : D.host.E)) :=
    (RingOfIntegers.isIntegral_coe z).map ((D.s.atP p).ιE.toIntAlgHom)
  exact h.tower_top

/- English proof (translation)
Establish `hI : Ideal.span {(N : 𝓞 D.host.F)} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hN` after adjusting the coercions. Use `(Ideal.finite_factors hI).subset ?_` and prove the remaining obligations. Introduce `p hp`.

Simplify using `only [Set.mem_ofPred_eq] at hp ⊢`. Rewrite using `[Ideal.dvd_span_singleton]`. Assume the negation of the conclusion as `hmem`. Apply `hp` to reduce the goal to its premises. Establish `hv : p.valuation D.host.F (N : D.host.F) = 1`.

Use `(IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (K := D.host.F) (v := p)).mpr hmem` as an intermediate fact. Simplify using `using this`. Establish `hle : (D.s.atP p).ιF ((N : D.host.F)⁻¹) ≤ᵥ (D.s.atP p).ιF 1`. Rewrite using `[(D.s.atP p).val]`. Simplify using `[map_inv₀, hv]`.

Rewrite `hle` using `[map_one]`. Establish `hint : (D.s.atP p).ιF ((N : D.host.F)⁻¹) ∈ Valuation.integer (ValuativeRel.valuation (D.s.atP p).Fp)`. Rewrite using `[Valuation.mem_integer_iff, ← (ValuativeRel.valuation _).vle_one_iff]`. Conclude with `hle`. Establish `hNE : (N : D.host.E) ≠ 0` using `by exact_mod_cast hN`.

Use `⟨algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF ((N : D.host.F)⁻¹)), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[(D.s.atP p).O_def]`. Conclude with `isIntegral_algebraMap (R := Valuation.integer (ValuativeRel.valuation (D.s.atP p).Fp)) (A := (D.s.atP p).Ep) (x := ⟨_, hint⟩)`. Rewrite using `[← (D.s.atP p).compat, ← map_mul, map_inv₀, map_natCast, mul_inv_cancel₀ hNE, map_one]`.
-/
private theorem finite_setOf_not_isUnit_natCast_atP (D : D7) (N : ℕ) (hN : N ≠ 0) :
    {p : PlF D | ¬ ∃ w ∈ (D.s.atP p).O, (D.s.atP p).ιE (N : D.host.E) * w = 1}.Finite := by
  have hI : Ideal.span {(N : 𝓞 D.host.F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  refine (Ideal.finite_factors hI).subset ?_
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp ⊢
  rw [Ideal.dvd_span_singleton]
  by_contra hmem
  apply hp
  have hv : p.valuation D.host.F (N : D.host.F) = 1 := by
    have := (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem
      (K := D.host.F) (v := p)).mpr hmem
    simpa using this
  have hle : (D.s.atP p).ιF ((N : D.host.F)⁻¹) ≤ᵥ (D.s.atP p).ιF 1 := by
    rw [(D.s.atP p).val]
    simp [map_inv₀, hv]
  rw [map_one] at hle
  have hint : (D.s.atP p).ιF ((N : D.host.F)⁻¹) ∈ Valuation.integer (ValuativeRel.valuation (D.s.atP p).Fp) := by
    rw [Valuation.mem_integer_iff, ← (ValuativeRel.valuation _).vle_one_iff]
    exact hle
  have hNE : (N : D.host.E) ≠ 0 := by exact_mod_cast hN
  refine ⟨algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF ((N : D.host.F)⁻¹)), ?_, ?_⟩
  · rw [(D.s.atP p).O_def]
    exact isIntegral_algebraMap (R := Valuation.integer (ValuativeRel.valuation (D.s.atP p).Fp)) (A := (D.s.atP p).Ep) (x := ⟨_, hint⟩)
  · rw [← (D.s.atP p).compat, ← map_mul, map_inv₀, map_natCast, mul_inv_cancel₀ hNE, map_one]

end GlobalTheory.FrameFactorUnit

open GlobalTheory.FrameFactorUnit in

/- English proof (translation)
Introduce `D Z a`. Establish `hL` using `Formalism.L2.SG.Pf.locDiffC_holds D Z`. Unfold `Formalism.L2.SG.Pf.LocDiffC at hL`. Take `⟨N, hN0, hN⟩` from `exists_nat_mul_mem_ringOfIntegers_of_fractionalIdeal (ddS D ^ (-((D.R.rS : ℤ) - ((a : ℕ) : ℤ))))`. Use `(finite_setOf_not_isUnit_natCast_atP D N hN0).subset ?_` and prove the remaining obligations.

Introduce `p hp`. Simplify using `only [Set.mem_ofPred_eq] at hp ⊢`. Introduce `hgood`. Apply `hp` to reduce the goal to its premises. Take `⟨w, hwO, hw1⟩` from `hgood`.

Establish `hO` using `Formalism.L2.SG.Pf.LocFacts.lf_hO Z p`. Establish `hc : Formalism.L2.SG.Pf.LocFacts.cP p Z ^ (D.R.rS - a.val) ∈ (D.s.atP p).O`. Use `Formalism.L2.SG.Pf.LocFacts.lf_mem_pow p Formalism.L2.SG.Pf.dualLoc_holds Z (D.R.rS - a.val) 1 (one_mem_inv_pow _)` as an intermediate fact. Simplify using `using this`. Establish `hunit : IsUnit (Formalism.L2.SG.Pf.LocFacts.cP p Z ^ (D.R.rS - a.val))` using `(Formalism.L2.SG.Pf.LocFacts.isUnit_localConstant p Z).pow _`.

Establish `hinv : frFac Z.δ p a * Formalism.L2.SG.Pf.LocFacts.cP p Z ^ (D.R.rS - a.val) = 1`. Unfold `frFac`. Conclude with `Ring.inverse_mul_cancel _ hunit`. Establish `hmem : frFac Z.δ p a ∈ (Z.M p).L.O`. Establish `hs` using `Submodule.mem_span_singleton_self (R := (Z.M p).L.O) (frFac Z.δ p a)`.

Rewrite `hs` using `[← hL p a]`. Use `revert hs`. Generalize the expression as in `frFac Z.δ p a = f`. Introduce `hs`. Proceed by induction on `hs using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨y, hy, rfl⟩` from `hx`. Take `⟨z, hz⟩` from `hN y hy`. Rewrite using `[hO]`. Establish `hy' : (D.s.atP p).ιE y = w * (D.s.atP p).ιE (z : D.host.E)`.

Rewrite using `[← hz, map_mul, ← mul_assoc, mul_comm w, hw1, one_mul]`. Rewrite using `[hy']`. Conclude with `mul_mem hwO (ιE_ringOfIntegers_mem_O D p z)`. Consider the case `zero => exact zero_mem _`. Consider the case `add x y _ _ hx hy => exact add_mem hx hy`.

Consider the case `smul r x _ hx`. Rewrite using `[Subring.smul_def]`. Conclude with `mul_mem r.2 hx`. Use `show frFac Z.δ p a ∈ (Z.M p).L.O ∧ ∃ y ∈ (Z.M p).L.O, frFac Z.δ p a * y = 1`. Conclude with `⟨hmem, _, hO ▸ hc, hinv⟩`.
-/
theorem GlobalTheory.FrameFactorUnit.frFac_isUnitO_finite : ∀ (D : D7) (Z : LocDat D) (a : Fin (D.R.rS + 1)),
    {p : PlF D | ¬ Formalism.MainNotions.S.LocNG.IsUnitO (Z.M p) (frFac Z.δ p a)}.Finite := by
  intro D Z a
  have hL := Formalism.L2.SG.Pf.locDiffC_holds D Z
  unfold Formalism.L2.SG.Pf.LocDiffC at hL
  obtain ⟨N, hN0, hN⟩ := exists_nat_mul_mem_ringOfIntegers_of_fractionalIdeal (ddS D ^ (-((D.R.rS : ℤ) - ((a : ℕ) : ℤ))))
  refine (finite_setOf_not_isUnit_natCast_atP D N hN0).subset ?_
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp ⊢
  intro hgood
  apply hp
  obtain ⟨w, hwO, hw1⟩ := hgood
  have hO := Formalism.L2.SG.Pf.LocFacts.lf_hO Z p
  have hc : Formalism.L2.SG.Pf.LocFacts.cP p Z ^ (D.R.rS - a.val) ∈ (D.s.atP p).O := by
    have := Formalism.L2.SG.Pf.LocFacts.lf_mem_pow p Formalism.L2.SG.Pf.dualLoc_holds Z (D.R.rS - a.val) 1
      (one_mem_inv_pow _)
    simpa using this
  have hunit : IsUnit (Formalism.L2.SG.Pf.LocFacts.cP p Z ^ (D.R.rS - a.val)) :=
    (Formalism.L2.SG.Pf.LocFacts.isUnit_localConstant p Z).pow _
  have hinv : frFac Z.δ p a * Formalism.L2.SG.Pf.LocFacts.cP p Z ^ (D.R.rS - a.val) = 1 := by
    unfold frFac
    exact Ring.inverse_mul_cancel _ hunit
  have hmem : frFac Z.δ p a ∈ (Z.M p).L.O := by
    have hs := Submodule.mem_span_singleton_self (R := (Z.M p).L.O) (frFac Z.δ p a)
    rw [← hL p a] at hs
    revert hs
    generalize frFac Z.δ p a = f
    intro hs
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨z, hz⟩ := hN y hy
      rw [hO]
      have hy' : (D.s.atP p).ιE y = w * (D.s.atP p).ιE (z : D.host.E) := by
        rw [← hz, map_mul, ← mul_assoc, mul_comm w, hw1, one_mul]
      rw [hy']
      exact mul_mem hwO (ιE_ringOfIntegers_mem_O D p z)
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul r x _ hx =>
      rw [Subring.smul_def]
      exact mul_mem r.2 hx
  show frFac Z.δ p a ∈ (Z.M p).L.O ∧ ∃ y ∈ (Z.M p).L.O, frFac Z.δ p a * y = 1
  exact ⟨hmem, _, hO ▸ hc, hinv⟩
