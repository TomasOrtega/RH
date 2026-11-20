import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharLem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTestVectorExpansion

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormSum.IdealDenom

open Formalism.MainNotions.StandardLatticesGL3 (IhE OhE inc)

/- English proof (translation)
Take `⟨a₀, ha₀, hint⟩` from `D.host.AA0.isFractional`. Establish `ha₀' : (algebraMap (𝓞 D.host.E) D.host.E a₀) ≠ 0`. Introduce `h`. Conclude with `nonZeroDivisors.ne_zero ha₀ (IsFractionRing.injective (𝓞 D.host.E) D.host.E (by simpa using h))`. Take `⟨n, hn, hmem⟩` from `GlobalTheory.NormSum.Expand.denom (inc D (algebraMap (𝓞 D.host.E) D.host.E a₀)⁻¹)`.

Use `⟨n, hn, fun t ht => ?_⟩` and prove the remaining obligations. Proceed by induction on `ht using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨c, hc, a, ha, s, hs, rfl⟩` from `hy`. Take `⟨b, hb⟩` from `hint a ha`.

Establish `hci : IsIntegral ℤ (((c : D.host.K) : D.host.E))` using `(RingOfIntegers.isIntegral_coe c).map (IsScalarTower.toAlgHom ℤ D.host.K D.host.E)`. Establish `hcm : inc D (((c : D.host.K) : D.host.E)) ∈ OhE D` using `GlobalTheory.NormSum.Expand.inc_int (⟨_, hci⟩ : 𝓞 D.host.E)`. Establish `hbm` using `GlobalTheory.NormSum.Expand.inc_int b`. Establish `hab : a = (algebraMap (𝓞 D.host.E) D.host.E a₀)⁻¹ * algebraMap (𝓞 D.host.E) D.host.E b`. Rewrite using `[hb, Algebra.smul_def, ← mul_assoc, inv_mul_cancel₀ ha₀', one_mul]`.

Establish `key : (n : Formalism.MainNotions.StandardLatticesGL3.AE D) * (inc D ((((c : D.host.K) : D.host.E)) * a) * s) = ((n : Formalism.MainNotions.StandardLatticesGL3.AE D) * inc D (algebraMap (𝓞 D.host.E) D.host.E a₀)⁻¹) * (inc D (((c : D.host.K) : D.host.E)) * inc D (algebraMap (𝓞 D.ho …`. Rewrite using `[hab, map_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`. Conclude with `(OhE D).mul_mem hmem ((OhE D).mul_mem ((OhE D).mul_mem hcm hbm) hs)`.

Consider the case `zero => rw [mul_zero]`. Conclude with `(OhE D).zero_mem`. Consider the case `add x y _ _ hx hy => rw [mul_add]`. Conclude with `(OhE D).add_mem hx hy`. Consider the case `neg x _ hx => rw [mul_neg]`.

Conclude with `(OhE D).neg_mem hx`.
-/
theorem exists_nat_mul_mem {D : D7} (cc : Ideal (𝓞 D.host.K)) : ∃ n : ℕ, 0 < n ∧
    ∀ t ∈ IhE D cc, (n : Formalism.MainNotions.StandardLatticesGL3.AE D) * t ∈ OhE D := by
  obtain ⟨a₀, ha₀, hint⟩ := D.host.AA0.isFractional
  have ha₀' : (algebraMap (𝓞 D.host.E) D.host.E a₀) ≠ 0 := by
    intro h
    exact nonZeroDivisors.ne_zero ha₀ (IsFractionRing.injective (𝓞 D.host.E) D.host.E (by simpa using h))
  obtain ⟨n, hn, hmem⟩ := GlobalTheory.NormSum.Expand.denom (inc D (algebraMap (𝓞 D.host.E) D.host.E a₀)⁻¹)
  refine ⟨n, hn, fun t ht => ?_⟩
  induction ht using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, hc, a, ha, s, hs, rfl⟩ := hy
    obtain ⟨b, hb⟩ := hint a ha
    have hci : IsIntegral ℤ (((c : D.host.K) : D.host.E)) :=
      (RingOfIntegers.isIntegral_coe c).map (IsScalarTower.toAlgHom ℤ D.host.K D.host.E)
    have hcm : inc D (((c : D.host.K) : D.host.E)) ∈ OhE D :=
      GlobalTheory.NormSum.Expand.inc_int (⟨_, hci⟩ : 𝓞 D.host.E)
    have hbm := GlobalTheory.NormSum.Expand.inc_int b
    have hab : a = (algebraMap (𝓞 D.host.E) D.host.E a₀)⁻¹ * algebraMap (𝓞 D.host.E) D.host.E b := by
      rw [hb, Algebra.smul_def, ← mul_assoc, inv_mul_cancel₀ ha₀', one_mul]
    have key : (n : Formalism.MainNotions.StandardLatticesGL3.AE D) * (inc D ((((c : D.host.K) : D.host.E)) * a) * s) =
        ((n : Formalism.MainNotions.StandardLatticesGL3.AE D) * inc D (algebraMap (𝓞 D.host.E) D.host.E a₀)⁻¹) *
          (inc D (((c : D.host.K) : D.host.E)) *
            inc D (algebraMap (𝓞 D.host.E) D.host.E b) * s) := by
      rw [hab, map_mul, map_mul]; ring
    rw [key]
    exact (OhE D).mul_mem hmem ((OhE D).mul_mem ((OhE D).mul_mem hcm hbm) hs)
  | zero => rw [mul_zero]; exact (OhE D).zero_mem
  | add x y _ _ hx hy => rw [mul_add]; exact (OhE D).add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact (OhE D).neg_mem hx

/- English proof (translation)
Introduce `D cc r`. Take `⟨n₁, h₁, m₁⟩` from `GlobalTheory.NormSum.Expand.denom (inc D r⁻¹)`. Take `⟨n₂, h₂, m₂⟩` from `exists_nat_mul_mem cc`. Use `⟨n₁ * n₂, Nat.mul_pos h₁ h₂, fun t ht => ?_⟩` and prove the remaining obligations. Establish `key : ((n₁ * n₂ : ℕ) : Formalism.MainNotions.StandardLatticesGL3.AE D) * (inc D r⁻¹ * t) = ((n₁ : Formalism.MainNotions.StandardLatticesGL3.AE D) * inc D r⁻¹) * ((n₂ : Formalism.MainNotions.StandardLatticesGL3.AE D) * t)` using `by push_cast; ring`.

Rewrite using `[key]`. Conclude with `(OhE D).mul_mem m₁ (m₂ t ht)`.
-/
theorem exists_nat_mul_inv_mul_mem : ∀ {D : D7} (cc : Ideal (𝓞 D.host.K)) (r : D.host.E), ∃ M : ℕ, 0 < M ∧
    ∀ t ∈ Formalism.MainNotions.StandardLatticesGL3.IhE D cc, (M : Formalism.MainNotions.StandardLatticesGL3.AE D) * (Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹ * t) ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D := by
  intro D cc r
  obtain ⟨n₁, h₁, m₁⟩ := GlobalTheory.NormSum.Expand.denom (inc D r⁻¹)
  obtain ⟨n₂, h₂, m₂⟩ := exists_nat_mul_mem cc
  refine ⟨n₁ * n₂, Nat.mul_pos h₁ h₂, fun t ht => ?_⟩
  have key : ((n₁ * n₂ : ℕ) : Formalism.MainNotions.StandardLatticesGL3.AE D) * (inc D r⁻¹ * t) =
      ((n₁ : Formalism.MainNotions.StandardLatticesGL3.AE D) * inc D r⁻¹) * ((n₂ : Formalism.MainNotions.StandardLatticesGL3.AE D) * t) := by
    push_cast; ring
  rw [key]
  exact (OhE D).mul_mem m₁ (m₂ t ht)

end GlobalTheory.NormSum.IdealDenom
