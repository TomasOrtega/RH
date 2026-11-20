import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvCut

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

open Formalism.FourierDecayAlt.P.MAx3.G

section PolyTools

variable {R : Type} [Ring R] [Algebra ℂ R]

/- English proof (translation)
Take `⟨a, ha⟩` from `h`. Conclude with `⟨a, fun s => by rw [e, ha]⟩`.
-/
theorem curv_polyIn_congr {f g : ℂ → R} {d : ℕ} (h : PolyIn f d) (e : ∀ s, g s = f s) : PolyIn g d := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, fun s => by rw [e, ha]⟩

/- English proof (translation)
Take `⟨a, ha⟩` from `hf`. Conclude with `⟨fun k => c • a k, fun s => by dsimp only; rw [ha, Finset.smul_sum]; simp only [smul_comm c]⟩`.
-/
theorem curv_polyIn_csmul {f : ℂ → R} {d : ℕ} (c : ℂ) (hf : PolyIn f d) : PolyIn (fun s => c • f s) d := by
  obtain ⟨a, ha⟩ := hf
  exact ⟨fun k => c • a k, fun s => by dsimp only; rw [ha, Finset.smul_sum]; simp only [smul_comm c]⟩

/- English proof (translation)
The claim follows from `curv_polyIn_congr (polyIn_add hf (curv_polyIn_csmul (-1) hg)) fun s => by simp [sub_eq_add_neg]`.
-/
theorem curv_polyIn_sub {f g : ℂ → R} {d : ℕ} (hf : PolyIn f d) (hg : PolyIn g d) :
    PolyIn (fun s => f s - g s) d :=
  curv_polyIn_congr (polyIn_add hf (curv_polyIn_csmul (-1) hg)) fun s => by simp [sub_eq_add_neg]

/- English proof (translation)
Use `⟨fun k => if k = n then x else 0, fun s => ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[Finset.sum_eq_single n (fun b _ hb => by rw [if_neg hb, smul_zero]) (fun h => absurd (Finset.mem_range.2 (Nat.lt_succ_self n)) h), if_pos rfl]`.
-/
theorem curv_polyIn_monomial (n : ℕ) (x : R) : PolyIn (fun s => s ^ n • x) n := by
  refine ⟨fun k => if k = n then x else 0, fun s => ?_⟩
  dsimp only
  rw [Finset.sum_eq_single n (fun b _ hb => by rw [if_neg hb, smul_zero])
    (fun h => absurd (Finset.mem_range.2 (Nat.lt_succ_self n)) h), if_pos rfl]

end PolyTools

/- English proof (translation)
Rewrite using `[← Module.forall_dual_apply_eq_zero_iff ℂ]`. Introduce `φ`. Use `set p : Polynomial ℂ := Polynomial.C (φ c) * Polynomial.X ^ (n + 1) - ∑ i ∈ Finset.range (n + 1), Polynomial.C (φ (a i)) * Polynomial.X ^ i with hpdef`. Establish `hp : p = 0`. Apply `Polynomial.funext` to reduce the goal to its premises.

Introduce `u`. Establish `hu` using `congrArg φ (h u)`. Simplify using `only [map_smul, map_sum, smul_eq_mul] at hu`. Simplify using `only [hpdef, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_finsetSum, Polynomial.eval_zero]`. Rewrite using `[mul_comm (φ c), hu, sub_eq_zero]`.

Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`. Establish `hc` using `congrArg (fun q => Polynomial.coeff q (n + 1)) hp`. Simplify using `only [hpdef, Polynomial.coeff_sub, Polynomial.coeff_C_mul_X_pow, Polynomial.finsetSum_coeff, Polynomial.coeff_zero] at hc`. Rewrite using `[Finset.sum_eq_zero (fun i hi => by`. Rewrite `hc` using `[if_neg (by have := Finset.mem_range.1 hi; omega)]), sub_zero]`.

Conclude with `hc`.
-/
theorem curv_top_zero {E : Type*} [AddCommGroup E] [Module ℂ E] (n : ℕ) (c : E) (a : ℕ → E)
    (h : ∀ u : ℂ, u ^ (n + 1) • c = ∑ i ∈ Finset.range (n + 1), u ^ i • a i) : c = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  set p : Polynomial ℂ := Polynomial.C (φ c) * Polynomial.X ^ (n + 1) -
    ∑ i ∈ Finset.range (n + 1), Polynomial.C (φ (a i)) * Polynomial.X ^ i with hpdef
  have hp : p = 0 := by
    apply Polynomial.funext
    intro u
    have hu := congrArg φ (h u)
    simp only [map_smul, map_sum, smul_eq_mul] at hu
    simp only [hpdef, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_finsetSum, Polynomial.eval_zero]
    rw [mul_comm (φ c), hu, sub_eq_zero]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hc := congrArg (fun q => Polynomial.coeff q (n + 1)) hp
  simp only [hpdef, Polynomial.coeff_sub, Polynomial.coeff_C_mul_X_pow, Polynomial.finsetSum_coeff,
    Polynomial.coeff_zero] at hc
  rw [Finset.sum_eq_zero (fun i hi => by
    rw [if_neg (by have := Finset.mem_range.1 hi; omega)]), sub_zero] at hc
  exact hc

/- English proof (translation)
Introduce `A _ _ n f g Θ hn hrtt hF hg v`. Use `set T := g v with hT`. Use `set F : ℂ → A := fun u => f u - u ^ (n + 1) • (1 : A) - u ^ n • Θ with hFdef`. Establish `hn' : n - 1 + 1 = n` using `Nat.sub_add_cancel hn`. Establish `hG : PolyIn (fun u => F u * T - T * F u) (n - 1)` using `curv_polyIn_sub (polyIn_mul_const hF T) (polyIn_const_mul T hF)`.

Establish `hSt : PolyIn (fun u => g u * f v - u ^ n • (T * Θ) - T * F u + v • (u ^ n • (Θ * T - T * Θ)) - u • (F u * T - T * F u) + v • (F u * T - T * F u)) n`. Use `polyIn_add (curv_polyIn_sub (polyIn_add (curv_polyIn_sub (curv_polyIn_sub (polyIn_mul_const hg (f v)) (curv_polyIn_monomial n (T * Θ))) (polyIn_mono (polyIn_const_mul T hF) (by omega))) (curv_polyIn_csmul v (curv_polyIn_monomial n (Θ * T - T * Θ)))) ?_) ?_` and prove the remaining obligations. Use `polyIn_smul_var hG` as an intermediate fact. Rewrite `this` using `[hn']`. Conclude with `this`.

Conclude with `polyIn_mono (curv_polyIn_csmul v hG) (by omega)`. Take `⟨s, hs⟩` from `hSt`. Establish `key : ∀ u : ℂ, u ^ (n + 1) • (Θ * T - T * Θ + T) = ∑ i ∈ Finset.range (n + 1), u ^ i • s i`. Introduce `u`. Rewrite using `[← hs u]`.

Establish `hfu : f u = F u + u ^ (n + 1) • (1 : A) + u ^ n • Θ` using `by simp only [hFdef]; abel`. Establish `h` using `hrtt u v`. Rewrite `h` using `[← hT, hfu]`. Simplify using `only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one] at h`. Take the linear combination `(norm := module) h`.

Establish `h0` using `curv_top_zero n _ s key`. Conclude with `eq_neg_of_add_eq_zero_left h0`.
-/
theorem curvature_radial_torus_holds : GTCCurvRTT := by
  intro A _ _ n f g Θ hn hrtt hF hg v
  set T := g v with hT
  set F : ℂ → A := fun u => f u - u ^ (n + 1) • (1 : A) - u ^ n • Θ with hFdef
  have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hG : PolyIn (fun u => F u * T - T * F u) (n - 1) :=
    curv_polyIn_sub (polyIn_mul_const hF T) (polyIn_const_mul T hF)
  have hSt : PolyIn (fun u => g u * f v - u ^ n • (T * Θ) - T * F u + v • (u ^ n • (Θ * T - T * Θ)) -
      u • (F u * T - T * F u) + v • (F u * T - T * F u)) n := by
    refine polyIn_add (curv_polyIn_sub (polyIn_add (curv_polyIn_sub (curv_polyIn_sub (polyIn_mul_const hg (f v))
      (curv_polyIn_monomial n (T * Θ))) (polyIn_mono (polyIn_const_mul T hF) (by omega)))
      (curv_polyIn_csmul v (curv_polyIn_monomial n (Θ * T - T * Θ)))) ?_) ?_
    · have := polyIn_smul_var hG
      rw [hn'] at this
      exact this
    · exact polyIn_mono (curv_polyIn_csmul v hG) (by omega)
  obtain ⟨s, hs⟩ := hSt
  have key : ∀ u : ℂ, u ^ (n + 1) • (Θ * T - T * Θ + T) = ∑ i ∈ Finset.range (n + 1), u ^ i • s i := by
    intro u
    rw [← hs u]
    have hfu : f u = F u + u ^ (n + 1) • (1 : A) + u ^ n • Θ := by simp only [hFdef]; abel
    have h := hrtt u v
    rw [← hT, hfu] at h
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one] at h
    linear_combination (norm := module) h
  have h0 := curv_top_zero n _ s key
  exact eq_neg_of_add_eq_zero_left h0

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
