import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.CurveComplexPoint
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace CurveComplexPoint

/- English proof (translation)
Rewrite using `[eval₂_eq', eval₂_eq', Finset.mul_sum]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Establish `hc : (∏ i : (Σ k, ι k), c i.1 ^ d i) = ∏ k, c k ^ a k`. Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations.

Use `show ∏ y, c k ^ d ⟨k, y⟩ = _`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hf d hd k]`. Simplify using `only [mul_pow, Finset.prod_mul_distrib, hc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eval₂_smul_homog {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {F : Type*} [CommRing F] (f : MRing ι) (a : K → ℕ) (hf : IsMultiHomog f a)
    (c : K → F) (y : (Σ k, ι k) → F) :
    eval₂ (Int.castRingHom F) (fun p => c p.1 * y p) f =
      (∏ k, c k ^ a k) * eval₂ (Int.castRingHom F) y f := by
  rw [eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hc : (∏ i : (Σ k, ι k), c i.1 ^ d i) = ∏ k, c k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ y, c k ^ d ⟨k, y⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hf d hd k]
  simp only [mul_pow, Finset.prod_mul_distrib, hc]
  ring

/- English proof (translation)
Introduce `K _ ι _ W hW`. Take `⟨_, ⟨hprime, ⟨S, hS, hWS⟩, hrel⟩, hhor, _⟩` from `hW`. Use `choose c hc using hrel`. Set `R` to `MRing ι ⧸ W`. Set `F` to `FractionRing R`.

Set `x : (Σ k, ι k) → F` to `fun p => algebraMap R F (Ideal.Quotient.mk W (X p))`. Establish `hx : ∀ k, x ⟨k, c k⟩ ≠ 0` using `fun k h => hc k (Ideal.Quotient.eq_zero_iff_mem.mp (IsFractionRing.injective R F (h.trans (map_zero _).symm)))`. Establish `hxeval : ∀ f : MRing ι, eval₂ (Int.castRingHom F) x f = algebraMap R F (Ideal.Quotient.mk W f)`. Introduce `f`. Establish `h : eval₂Hom (Int.castRingHom F) x = (algebraMap R F).comp (Ideal.Quotient.mk W)` using `ringHom_ext (fun n => by simp) (fun p => by simp [x])`.

Conclude with `RingHom.congr_fun h f`. Establish `: CharZero F` using `charZero_of_inj_zero fun n hn => by`. Establish `h1 : Ideal.Quotient.mk W (C (n : ℤ)) = 0` using `IsFractionRing.injective R F (by simpa using hn)`. Establish `h2 : (n : ℤ) ∈ W.comap (C : ℤ →+* MRing ι)` using `Ideal.mem_comap.mpr (Ideal.Quotient.eq_zero_iff_mem.mp h1)`. Rewrite `h2` using `[hhor, Ideal.mem_bot]`.

Conclude with `h2` after adjusting the coercions. Set `y : (Σ k, ι k) → F` to `fun p => (x ⟨p.1, c p.1⟩)⁻¹ * x p`. Set `ψ : MvPolynomial (Σ k, ι k) ℚ →+* F` to `eval₂Hom (Rat.castHom F) y`. Establish `hψmap : ∀ f : MRing ι, ψ (map (Int.castRingHom ℚ) f) = eval₂ (Int.castRingHom F) y f`. Introduce `f`.

Simplify using `only [ψ, coe_eval₂Hom, eval₂_map]`. Use `congr 1`. Conclude with `RingHom.ext_int _ _`. Establish `hWker : ∀ f ∈ W, map (Int.castRingHom ℚ) f ∈ RingHom.ker ψ`. Introduce `f hf`.

Rewrite `hf` using `[hWS]`. Establish `hle : Ideal.span S ≤ (RingHom.ker ψ).comap (map (Int.castRingHom ℚ))`. Use `Ideal.span_le.mpr fun s hs => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `hS s hs`. Establish `hsW : s ∈ W` using `hWS ▸ Ideal.subset_span hs`.

Use `show ψ (map (Int.castRingHom ℚ) s) = 0`. Rewrite using `[hψmap]`. Use `(eval₂_smul_homog s a ha (fun k => (x ⟨k, c k⟩)⁻¹) x).trans ?_` and prove the remaining obligations. Rewrite using `[hxeval, Ideal.Quotient.eq_zero_iff_mem.mpr hsW, map_zero, mul_zero]`. Conclude with `hle hf`.

Establish `hXker : ∀ k, (X ⟨k, c k⟩ - 1 : MvPolynomial (Σ k, ι k) ℚ) ∈ RingHom.ker ψ`. Introduce `k`. Rewrite using `[RingHom.mem_ker, map_sub, map_one]`. Simplify using `only [ψ, coe_eval₂Hom, eval₂_X, y]`. Rewrite using `[inv_mul_cancel₀ (hx k), sub_self]`.

Take `⟨m, hm, hkm⟩` from `Ideal.exists_le_maximal (RingHom.ker ψ) (RingHom.ker_ne_top ψ)`. Set `L` to `MvPolynomial (Σ k, ι k) ℚ ⧸ m`. Set `: Field L` to `Ideal.Quotient.field m`. Establish `: Module.Finite ℚ L` using `finite_of_finite_type_of_isJacobsonRing ℚ L`. Establish `: Algebra.IsAlgebraic ℚ L` using `Algebra.IsAlgebraic.of_finite ℚ L`.

Set `φ : L →ₐ[ℚ] ℂ` to `IsAlgClosed.lift`. Set `z : (Σ k, ι k) → ℂ` to `fun p => φ (Ideal.Quotient.mk m (X p))`. Establish `hz : ∀ f : MRing ι, eval z (map (Int.castRingHom ℂ) f) = φ (Ideal.Quotient.mk m (map (Int.castRingHom ℚ) f))`. Introduce `f`. Establish `h : eval₂Hom (Int.castRingHom ℂ) z = (φ : L →+* ℂ).comp ((Ideal.Quotient.mk m).comp (map (Int.castRingHom ℚ)))` using `ringHom_ext (fun n => by simp) (fun p => by simp [z])`.

Rewrite using `[eval_map]`. Conclude with `RingHom.congr_fun h f`. Use `⟨z, fun k => ⟨c k, ?_⟩, fun f hf => ?_⟩` and prove the remaining obligations. Establish `h1 : Ideal.Quotient.mk m (X ⟨k, c k⟩) = Ideal.Quotient.mk m 1` using `Ideal.Quotient.eq.mpr (hkm (hXker k))`. Simplify using `only [z, h1, map_one]`.

Conclude with `one_ne_zero`. Rewrite using `[hz, Ideal.Quotient.eq_zero_iff_mem.mpr (hkm (hWker f hf)), map_zero]`.
-/
theorem full : CurveComplexPoint.Statement := by
  intro K _ ι _ W hW
  classical
  obtain ⟨_, ⟨hprime, ⟨S, hS, hWS⟩, hrel⟩, hhor, _⟩ := hW
  choose c hc using hrel
  let R := MRing ι ⧸ W
  let F := FractionRing R
  let x : (Σ k, ι k) → F := fun p => algebraMap R F (Ideal.Quotient.mk W (X p))
  have hx : ∀ k, x ⟨k, c k⟩ ≠ 0 := fun k h => hc k
    (Ideal.Quotient.eq_zero_iff_mem.mp (IsFractionRing.injective R F (h.trans (map_zero _).symm)))
  have hxeval : ∀ f : MRing ι,
      eval₂ (Int.castRingHom F) x f = algebraMap R F (Ideal.Quotient.mk W f) := by
    intro f
    have h : eval₂Hom (Int.castRingHom F) x = (algebraMap R F).comp (Ideal.Quotient.mk W) :=
      ringHom_ext (fun n => by simp) (fun p => by simp [x])
    exact RingHom.congr_fun h f
  have : CharZero F := charZero_of_inj_zero fun n hn => by
    have h1 : Ideal.Quotient.mk W (C (n : ℤ)) = 0 :=
      IsFractionRing.injective R F (by simpa using hn)
    have h2 : (n : ℤ) ∈ W.comap (C : ℤ →+* MRing ι) :=
      Ideal.mem_comap.mpr (Ideal.Quotient.eq_zero_iff_mem.mp h1)
    rw [hhor, Ideal.mem_bot] at h2
    exact_mod_cast h2
  let y : (Σ k, ι k) → F := fun p => (x ⟨p.1, c p.1⟩)⁻¹ * x p
  let ψ : MvPolynomial (Σ k, ι k) ℚ →+* F := eval₂Hom (Rat.castHom F) y
  have hψmap : ∀ f : MRing ι,
      ψ (map (Int.castRingHom ℚ) f) = eval₂ (Int.castRingHom F) y f := by
    intro f
    simp only [ψ, coe_eval₂Hom, eval₂_map]
    congr 1
    exact RingHom.ext_int _ _
  have hWker : ∀ f ∈ W, map (Int.castRingHom ℚ) f ∈ RingHom.ker ψ := by
    intro f hf
    rw [hWS] at hf
    have hle : Ideal.span S ≤ (RingHom.ker ψ).comap (map (Int.castRingHom ℚ)) := by
      refine Ideal.span_le.mpr fun s hs => ?_
      obtain ⟨a, ha⟩ := hS s hs
      have hsW : s ∈ W := hWS ▸ Ideal.subset_span hs
      show ψ (map (Int.castRingHom ℚ) s) = 0
      rw [hψmap]
      refine (eval₂_smul_homog s a ha (fun k => (x ⟨k, c k⟩)⁻¹) x).trans ?_
      rw [hxeval, Ideal.Quotient.eq_zero_iff_mem.mpr hsW, map_zero, mul_zero]
    exact hle hf
  have hXker : ∀ k, (X ⟨k, c k⟩ - 1 : MvPolynomial (Σ k, ι k) ℚ) ∈ RingHom.ker ψ := by
    intro k
    rw [RingHom.mem_ker, map_sub, map_one]
    simp only [ψ, coe_eval₂Hom, eval₂_X, y]
    rw [inv_mul_cancel₀ (hx k), sub_self]
  obtain ⟨m, hm, hkm⟩ := Ideal.exists_le_maximal (RingHom.ker ψ) (RingHom.ker_ne_top ψ)
  let L := MvPolynomial (Σ k, ι k) ℚ ⧸ m
  let : Field L := Ideal.Quotient.field m
  have : Module.Finite ℚ L := finite_of_finite_type_of_isJacobsonRing ℚ L
  have : Algebra.IsAlgebraic ℚ L := Algebra.IsAlgebraic.of_finite ℚ L
  let φ : L →ₐ[ℚ] ℂ := IsAlgClosed.lift
  let z : (Σ k, ι k) → ℂ := fun p => φ (Ideal.Quotient.mk m (X p))
  have hz : ∀ f : MRing ι, eval z (map (Int.castRingHom ℂ) f) =
      φ (Ideal.Quotient.mk m (map (Int.castRingHom ℚ) f)) := by
    intro f
    have h : eval₂Hom (Int.castRingHom ℂ) z =
        (φ : L →+* ℂ).comp ((Ideal.Quotient.mk m).comp (map (Int.castRingHom ℚ))) :=
      ringHom_ext (fun n => by simp) (fun p => by simp [z])
    rw [eval_map]
    exact RingHom.congr_fun h f
  refine ⟨z, fun k => ⟨c k, ?_⟩, fun f hf => ?_⟩
  · have h1 : Ideal.Quotient.mk m (X ⟨k, c k⟩) = Ideal.Quotient.mk m 1 :=
      Ideal.Quotient.eq.mpr (hkm (hXker k))
    simp only [z, h1, map_one]
    exact one_ne_zero
  · rw [hz, Ideal.Quotient.eq_zero_iff_mem.mpr (hkm (hWker f hf)), map_zero]

end CurveComplexPoint

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
