import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero

open IsDedekindDomain NumberField
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchDeriv
variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

/- English proof (translation)
Unfold `GlobalTheory.WeilL2Words.arch1`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Conclude with `map_add _ a b`. Conclude with `(add_zero (0 : FiniteAdeleRing (𝓞 F) F)).symm`.
-/
theorem archimedean_map_add (a b : mixedEmbedding.mixedSpace F) :
    GlobalTheory.WeilL2Words.arch1 F (a + b) = GlobalTheory.WeilL2Words.arch1 F a + GlobalTheory.WeilL2Words.arch1 F b := by
  unfold GlobalTheory.WeilL2Words.arch1
  refine Prod.ext ?_ ?_
  · exact map_add _ a b
  · exact (add_zero (0 : FiniteAdeleRing (𝓞 F) F)).symm

/- English proof (translation)
The claim follows from `map_sum (AddMonoidHom.mk' (GlobalTheory.WeilL2Words.arch1 F) (archimedean_map_add F)) f Finset.univ`.
-/
theorem adeleOfMixedSpaceComponent_finsetSum (f : κ → mixedEmbedding.mixedSpace F) :
    GlobalTheory.WeilL2Words.arch1 F (∑ k, f k) = ∑ k, GlobalTheory.WeilL2Words.arch1 F (f k) :=
  map_sum (AddMonoidHom.mk' (GlobalTheory.WeilL2Words.arch1 F) (archimedean_map_add F)) f Finset.univ

/- English proof (translation)
Unfold `GlobalTheory.WeilL2Words.arch1 GlobalTheory.WeilCont.adeleJoin`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Conclude with `(map_mul _ (x k) b).symm`. Conclude with `mul_zero (y k)`.
-/
theorem adeleJoin_mul_arch1 (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) (k : κ)
    (b : mixedEmbedding.mixedSpace F) :
    GlobalTheory.WeilCont.adeleJoin F x y k * GlobalTheory.WeilL2Words.arch1 F b = GlobalTheory.WeilL2Words.arch1 F (x k * b) := by
  unfold GlobalTheory.WeilL2Words.arch1 GlobalTheory.WeilCont.adeleJoin
  refine Prod.ext ?_ ?_
  · exact (map_mul _ (x k) b).symm
  · exact mul_zero (y k)

/- English proof (translation)
Unfold `GlobalTheory.WeilL2Words.arch1`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Conclude with `(map_mul _ a b).symm`. Conclude with `mul_zero (0 : FiniteAdeleRing (𝓞 F) F)`.
-/
theorem adeleOfMixedSpaceComponent_mul (a b : mixedEmbedding.mixedSpace F) :
    GlobalTheory.WeilL2Words.arch1 F a * GlobalTheory.WeilL2Words.arch1 F b = GlobalTheory.WeilL2Words.arch1 F (a * b) := by
  unfold GlobalTheory.WeilL2Words.arch1
  refine Prod.ext ?_ ?_
  · exact (map_mul _ a b).symm
  · exact mul_zero (0 : FiniteAdeleRing (𝓞 F) F)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Conclude with `(map_add _ (x i) (v i)).symm`. Conclude with `add_zero (y i)`.
-/
theorem adeleJoin_add_arch (x v : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    GlobalTheory.WeilCont.adeleJoin F x y + GlobalTheory.WeilL2Words.arch F v = GlobalTheory.WeilCont.adeleJoin F (x + v) y := by
  funext i
  refine Prod.ext ?_ ?_
  · exact (map_add _ (x i) (v i)).symm
  · exact add_zero (y i)

/- English proof (translation)
Rewrite using `[adeleOfMixedSpaceComponent_finsetSum]`. Unfold `dotProduct`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Conclude with `adeleJoin_mul_arch1 F x y k (w k)`.
-/
theorem adeleJoin_dot_arch (x w : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    GlobalTheory.WeilCont.adeleJoin F x y ⬝ᵥ GlobalTheory.WeilL2Words.arch F w = GlobalTheory.WeilL2Words.arch1 F (∑ k, x k * w k) := by
  rw [adeleOfMixedSpaceComponent_finsetSum]
  unfold dotProduct
  refine Finset.sum_congr rfl fun k _ => ?_
  exact adeleJoin_mul_arch1 F x y k (w k)

/- English proof (translation)
Rewrite using `[adeleOfMixedSpaceComponent_finsetSum]`. Unfold `dotProduct`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Conclude with `adeleOfMixedSpaceComponent_mul F (v k) (w k)`.
-/
theorem arch_dot_arch (v w : κ → mixedEmbedding.mixedSpace F) :
    GlobalTheory.WeilL2Words.arch F v ⬝ᵥ GlobalTheory.WeilL2Words.arch F w = GlobalTheory.WeilL2Words.arch1 F (∑ k, v k * w k) := by
  rw [adeleOfMixedSpaceComponent_finsetSum]
  unfold dotProduct
  refine Finset.sum_congr rfl fun k _ => ?_
  exact adeleOfMixedSpaceComponent_mul F (v k) (w k)

/- English proof (translation)
Unfold `GlobalTheory.WeilL2Words.arch1`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show (⅟(2 : AdeleRing (𝓞 F) F)).1 * _ = _`. Rewrite using `[map_mul, RingEquiv.symm_apply_apply]`. Conclude with `mul_zero _`.
-/
theorem mul_arch1 [Invertible (2 : AdeleRing (𝓞 F) F)] (b : mixedEmbedding.mixedSpace F) :
    ⅟(2 : AdeleRing (𝓞 F) F) * GlobalTheory.WeilL2Words.arch1 F b =
      GlobalTheory.WeilL2Words.arch1 F (InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AdeleRing (𝓞 F) F)).1 * b) := by
  unfold GlobalTheory.WeilL2Words.arch1
  refine Prod.ext ?_ ?_
  · show (⅟(2 : AdeleRing (𝓞 F) F)).1 * _ = _
    rw [map_mul, RingEquiv.symm_apply_apply]
  · exact mul_zero _

end GlobalTheory.ArchDeriv

open GlobalTheory.ArchDeriv
namespace GlobalTheory.WeilL2Words

/- English proof (translation)
Introduce `F _ _ _ κ _ ψ ℓ hψ Φ y hs h x`. Use `set s : (κ → mixedEmbedding.mixedSpace F) → ℂ := fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y) with hs_def`. Use `set P : mixedEmbedding.mixedSpace F := ∑ k, x k * h.2 k with hP`. Use `set Q : mixedEmbedding.mixedSpace F := InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AdeleRing (𝓞 F) F)).1 * ∑ k, h.1 k * h.2 k with hQ`. Use `set r : ℝ → ℝ := fun t => t * ℓ P + t ^ 2 * ℓ Q with hr`.

Establish `key : (fun t : ℝ => GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F (t • h)) Φ (GlobalTheory.WeilCont.adeleJoin F x y)) = fun t => Complex.exp (2 * Real.pi * Complex.I * (r t : ℂ)) * s (x + t • h.1)`. Use function extensionality and compare the values at `t`. Establish `e1 : (t • h).1 = t • h.1` using `rfl`. Establish `e2 : (t • h).2 = t • h.2` using `rfl`. Simplify using `only [GlobalTheory.WeilM.schr, GlobalTheory.WeilL2Words.archPair, e1, e2, adeleJoin_add_arch, adeleJoin_dot_arch, arch_dot_arch, mul_arch1, ← archimedean_map_add]`.

Use `congr 1`. Rewrite using `[hψ]`. Use `congr 2`. Establish `q1 : (∑ k, x k * (t • h.2) k) = t • P`. Simplify using `only [hP, Pi.smul_apply, mul_smul_comm, Finset.smul_sum]`.

Establish `q2 : InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AdeleRing (𝓞 F) F)).1 * ∑ k, (t • h.1) k * (t • h.2) k = t ^ 2 • Q`. Simplify using `only [Pi.smul_apply, smul_mul_smul_comm]`. Rewrite using `[← Finset.smul_sum, mul_smul_comm, hQ, pow_two]`. Rewrite using `[q1, q2, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]`. Establish `hr' : HasDerivAt r (ℓ P) 0`.

Establish `h1` using `(hasDerivAt_mul_const (x := (0 : ℝ)) (ℓ P)).add ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (ℓ Q))`. Conclude with `h1.congr_deriv (by simp)`. Establish `hE : HasDerivAt (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * (r t : ℂ))) (Complex.exp (2 * Real.pi * Complex.I * (r 0 : ℂ)) * (2 * Real.pi * Complex.I * (ℓ P : ℂ))) 0` using `(hr'.ofReal_comp.const_mul (2 * Real.pi * Complex.I)).cexp`. Establish `hc : HasDerivAt (fun t : ℝ => x + t • h.1) h.1 0`. Simplify using `using ((hasDerivAt_id (0 : ℝ)).smul_const h.1).const_add x`.

Establish `hS : HasDerivAt (fun t : ℝ => s (x + t • h.1)) (fderiv ℝ s x h.1) 0`. Establish `hf : HasFDerivAt s (fderiv ℝ s x) (x + (0 : ℝ) • h.1)`. Rewrite using `[zero_smul, add_zero]`. Conclude with `(hs x).hasFDerivAt`. Conclude with `hf.comp_hasDerivAt (0 : ℝ) hc`.

Establish `hD` using `hE.mul hS`. Unfold `GlobalTheory.WeilL2Words.dS`. Rewrite using `[key]`. Use `hD.deriv.trans ?_` and prove the remaining obligations. Establish `r0 : r 0 = 0` using `by simp [hr]`.

Simplify using `only [r0, zero_smul, add_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dS_adeleJoin_eq : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ z, ψ (GlobalTheory.WeilL2Words.arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z)) →
    ∀ (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → FiniteAdeleRing (𝓞 F) F),
      Differentiable ℝ (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) →
      ∀ (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) (x : κ → mixedEmbedding.mixedSpace F),
        GlobalTheory.WeilL2Words.dS F ψ h Φ (GlobalTheory.WeilCont.adeleJoin F x y) =
          fderiv ℝ (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x h.1 +
            2 * Real.pi * Complex.I * (ℓ (∑ k, x k * h.2 k) : ℂ) * Φ (GlobalTheory.WeilCont.adeleJoin F x y) := by
  intro F _ _ _ κ _ ψ ℓ hψ Φ y hs h x
  set s : (κ → mixedEmbedding.mixedSpace F) → ℂ := fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y) with hs_def
  set P : mixedEmbedding.mixedSpace F := ∑ k, x k * h.2 k with hP
  set Q : mixedEmbedding.mixedSpace F :=
    InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AdeleRing (𝓞 F) F)).1 * ∑ k, h.1 k * h.2 k with hQ
  set r : ℝ → ℝ := fun t => t * ℓ P + t ^ 2 * ℓ Q with hr
  have key : (fun t : ℝ => GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F (t • h)) Φ (GlobalTheory.WeilCont.adeleJoin F x y)) =
      fun t => Complex.exp (2 * Real.pi * Complex.I * (r t : ℂ)) * s (x + t • h.1) := by
    funext t
    have e1 : (t • h).1 = t • h.1 := rfl
    have e2 : (t • h).2 = t • h.2 := rfl
    simp only [GlobalTheory.WeilM.schr, GlobalTheory.WeilL2Words.archPair, e1, e2, adeleJoin_add_arch, adeleJoin_dot_arch, arch_dot_arch,
      mul_arch1, ← archimedean_map_add]
    congr 1
    · rw [hψ]
      congr 2
      have q1 : (∑ k, x k * (t • h.2) k) = t • P := by
        simp only [hP, Pi.smul_apply, mul_smul_comm, Finset.smul_sum]
      have q2 : InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AdeleRing (𝓞 F) F)).1 *
          ∑ k, (t • h.1) k * (t • h.2) k = t ^ 2 • Q := by
        simp only [Pi.smul_apply, smul_mul_smul_comm]
        rw [← Finset.smul_sum, mul_smul_comm, hQ, pow_two]
      rw [q1, q2, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hr' : HasDerivAt r (ℓ P) 0 := by
    have h1 := (hasDerivAt_mul_const (x := (0 : ℝ)) (ℓ P)).add ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (ℓ Q))
    exact h1.congr_deriv (by simp)
  have hE : HasDerivAt (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * (r t : ℂ)))
      (Complex.exp (2 * Real.pi * Complex.I * (r 0 : ℂ)) * (2 * Real.pi * Complex.I * (ℓ P : ℂ))) 0 :=
    (hr'.ofReal_comp.const_mul (2 * Real.pi * Complex.I)).cexp
  have hc : HasDerivAt (fun t : ℝ => x + t • h.1) h.1 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h.1).const_add x
  have hS : HasDerivAt (fun t : ℝ => s (x + t • h.1)) (fderiv ℝ s x h.1) 0 := by
    have hf : HasFDerivAt s (fderiv ℝ s x) (x + (0 : ℝ) • h.1) := by
      rw [zero_smul, add_zero]
      exact (hs x).hasFDerivAt
    exact hf.comp_hasDerivAt (0 : ℝ) hc
  have hD := hE.mul hS
  unfold GlobalTheory.WeilL2Words.dS
  rw [key]
  refine hD.deriv.trans ?_
  have r0 : r 0 = 0 := by simp [hr]
  simp only [r0, zero_smul, add_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
  ring

end GlobalTheory.WeilL2Words

end
