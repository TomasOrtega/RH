import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.HasInfCharOfIsRegAlg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
import GroundTheory.IdeleRoots.ConstantFrames.GaugeExistence.QdetSub
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

noncomputable section

namespace GlobalTheory.CompanionTheory.CapelliTrace

open Polynomial Formalism.REAL GroundTheory.BlockD.FourierDecayAlt.GaugeExists

/- English proof (translation)
Establish `h` using `prod_linear l.length (fun i => l.get i)`. Establish `e : (List.ofFn fun i : Fin l.length => (X + C (l.get i) : A[X])) = l.map fun b => (X + C b : A[X])` using `by conv_rhs => rw [← List.ofFn_get l, List.map_ofFn]`. Both sides reduce to the same expression. Rewrite `h` using `[e]`. Rewrite using `[h.2.2 k hk]`.

Use `conv_rhs => rw [← List.ofFn_get l, List.sum_ofFn]`.
-/
theorem coeff_prod_lin {A : Type} [Ring A] (l : List A) (k : ℕ) (hk : k + 1 = l.length) :
    ((l.map fun b => (X + C b : A[X])).prod).coeff k = l.sum := by
  have h := prod_linear l.length (fun i => l.get i)
  have e : (List.ofFn fun i : Fin l.length => (X + C (l.get i) : A[X])) = l.map fun b => (X + C b : A[X]) := by
    conv_rhs => rw [← List.ofFn_get l, List.map_ofFn]
    rfl
  rw [e] at h
  rw [h.2.2 k hk]
  conv_rhs => rw [← List.ofFn_get l, List.sum_ofFn]

/- English proof (translation)
Use `(Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun f => ?_` and prove the remaining obligations. Establish `hP : (∑ j ∈ Finset.range N, C (f (w j)) * X ^ j : ℂ[X]) = 0`. Use `Polynomial.funext fun u => ?_` and prove the remaining obligations. Use `congrArg f (h u)` as an intermediate fact. Simplify using `only [map_sum, map_smul, smul_eq_mul, map_zero] at this`.

Simplify using `only [eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X, eval_zero]`. Rewrite using `[← this]`. Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`. Use `congrArg (fun p => coeff p i) hP` as an intermediate fact. Simplify `this` using `[finset_sum_coeff, coeff_C_mul, coeff_X_pow, hi]`.
-/
theorem coeff_eq_zero_of_forall {V : Type} [AddCommGroup V] [Module ℂ V] (N : ℕ) (w : ℕ → V)
    (h : ∀ u : ℂ, ∑ j ∈ Finset.range N, u ^ j • w j = 0) (i : ℕ) (hi : i < N) : w i = 0 := by
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun f => ?_
  have hP : (∑ j ∈ Finset.range N, C (f (w j)) * X ^ j : ℂ[X]) = 0 := by
    refine Polynomial.funext fun u => ?_
    have := congrArg f (h u)
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at this
    simp only [eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X, eval_zero]
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have := congrArg (fun p => coeff p i) hP
  simpa [finset_sum_coeff, coeff_C_mul, coeff_X_pow, hi] using this

section Gen

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons x l ih`. Simplify using `only [List.map_cons, List.prod_cons, map_mul, ih]`. Use `congr 1`.

Simplify using `only [evU_apply, eval₂_add, eval₂_X, eval₂_C, RingHom.id_apply, ← map_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem evU_prod_lin (l : List ℂ) (c v : ℂ) :
    evU v (((l.map fun x => algebraMap ℂ (Module.End ℂ V) (x - c)).map fun b => (X + C b)).prod) =
      algebraMap ℂ (Module.End ℂ V) (l.map (v - c + ·)).prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, ih]
    congr 1
    simp only [evU_apply, eval₂_add, eval₂_X, eval₂_C, RingHom.id_apply, ← map_add]
    congr 1
    ring

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons x l ih`. Simplify using `only [List.map_cons, List.sum_cons, ih, List.length_cons, ← map_add]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_map_lin (l : List ℂ) (c : ℂ) :
    (l.map fun x => algebraMap ℂ (Module.End ℂ V) (x - c)).sum =
      algebraMap ℂ (Module.End ℂ V) (l.sum - l.length * c) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.length_cons, ← map_add]
    congr 1
    push_cast
    ring

/- English proof (translation)
Use `set c : ℂ := (n : ℂ) / 2 with hc`. Use `set L : List (Module.End ℂ V) := l.map fun x => algebraMap ℂ (Module.End ℂ V) (x - c) with hL`. Use `set R : (Module.End ℂ V)[X] := (L.map fun b => (X + C b)).prod with hR`. Use `set D : (Module.End ℂ V)[X] := qdetPoly Eo - R with hD`. Establish `hev : ∀ v, (evU v D) φ = 0` using `fun v => by`.

Rewrite using `[hD, map_sub, evU_qdetPoly, hR, hL, evU_prod_lin, LinearMap.sub_apply, h, Module.algebraMap_end_apply, sub_self]`. Establish `hsum : ∀ v : ℂ, ∑ j ∈ Finset.range (D.natDegree + 1 + (n + 1)), v ^ j • (D.coeff j) φ = 0` using `fun v => by`. Use `hev v` as an intermediate fact. Rewrite `this` using `[evU_apply, eval₂_eq_sum_range' _ (show D.natDegree < D.natDegree + 1 + (n + 1) by omega), LinearMap.sum_apply]`. Rewrite using `[← this]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← map_pow, RingHom.id_apply, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul]`. Establish `h0` using `coeff_eq_zero_of_forall _ (fun j => (D.coeff j) φ) hsum n (by omega)`. Establish `hq : (qdetPoly Eo).coeff n = ∑ k, Eo k k - algebraMap ℂ _ (((n + 1 : ℕ) : ℂ) * (((n + 1 : ℕ) : ℂ) - 1) / 2)`. Rewrite using `[coeff_qdetPoly_top Eo n (by omega), (prod_linear (n + 1) _).2.2 n rfl, Finset.sum_sub_distrib, ← map_sum, sum_fin_cast]`.

Establish `hr : R.coeff n = algebraMap ℂ _ (l.sum - l.length * c)`. Rewrite using `[hR, coeff_prod_lin L n (by simp [hL, hl]), hL, sum_map_lin]`. Simplify using `only [hD, coeff_sub, hq, hr] at h0`. Establish `hs : (∑ k, Eo k k) - algebraMap ℂ (Module.End ℂ V) (((n + 1 : ℕ) : ℂ) * (((n + 1 : ℕ) : ℂ) - 1) / 2) - algebraMap ℂ _ (l.sum - l.length * c) = (∑ k, Eo k k) - algebraMap ℂ _ l.sum`. Rewrite using `[sub_sub, ← map_add]`.

Use `congr 2`. Rewrite using `[hl, hc]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h0` using `[hs, LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero]`.

Conclude with `h0`.
-/
theorem trace_of_qdet {n : ℕ} (Eo : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (l : List ℂ)
    (hl : l.length = n + 1) (φ : V)
    (h : ∀ v : ℂ, qdet Eo v φ = (l.map (v - (n : ℂ) / 2 + ·)).prod • φ) :
    (∑ i, Eo i i) φ = l.sum • φ := by
  set c : ℂ := (n : ℂ) / 2 with hc
  set L : List (Module.End ℂ V) := l.map fun x => algebraMap ℂ (Module.End ℂ V) (x - c) with hL
  set R : (Module.End ℂ V)[X] := (L.map fun b => (X + C b)).prod with hR
  set D : (Module.End ℂ V)[X] := qdetPoly Eo - R with hD
  have hev : ∀ v, (evU v D) φ = 0 := fun v => by
    rw [hD, map_sub, evU_qdetPoly, hR, hL, evU_prod_lin, LinearMap.sub_apply, h, Module.algebraMap_end_apply,
      sub_self]
  have hsum : ∀ v : ℂ, ∑ j ∈ Finset.range (D.natDegree + 1 + (n + 1)), v ^ j • (D.coeff j) φ = 0 := fun v => by
    have := hev v
    rw [evU_apply, eval₂_eq_sum_range' _ (show D.natDegree < D.natDegree + 1 + (n + 1) by omega),
      LinearMap.sum_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← map_pow, RingHom.id_apply, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul]
  have h0 := coeff_eq_zero_of_forall _ (fun j => (D.coeff j) φ) hsum n (by omega)
  have hq : (qdetPoly Eo).coeff n = ∑ k, Eo k k - algebraMap ℂ _ (((n + 1 : ℕ) : ℂ) * (((n + 1 : ℕ) : ℂ) - 1) / 2) := by
    rw [coeff_qdetPoly_top Eo n (by omega), (prod_linear (n + 1) _).2.2 n rfl, Finset.sum_sub_distrib, ← map_sum,
      sum_fin_cast]
  have hr : R.coeff n = algebraMap ℂ _ (l.sum - l.length * c) := by
    rw [hR, coeff_prod_lin L n (by simp [hL, hl]), hL, sum_map_lin]
  simp only [hD, coeff_sub, hq, hr] at h0
  have hs : (∑ k, Eo k k) - algebraMap ℂ (Module.End ℂ V) (((n + 1 : ℕ) : ℂ) * (((n + 1 : ℕ) : ℂ) - 1) / 2) -
      algebraMap ℂ _ (l.sum - l.length * c) = (∑ k, Eo k k) - algebraMap ℂ _ l.sum := by
    rw [sub_sub, ← map_add]
    congr 2
    rw [hl, hc]
    push_cast
    ring
  rw [hs, LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero] at h0
  exact h0

end Gen

/- English proof (translation)
Introduce `E _ _ _ a π τ m hm φ hφ`. Take `⟨hc, hu⟩` from `hm`. Break down `a with _ | n` into its components or cases. Take `rfl : m = 0` from `Multiset.card_eq_zero.1 hc`. Simplify using the standard rewrite rules.

Take `⟨l, rfl⟩` from `Quot.exists_rep m`. Use `trace_of_qdet (Eop τ) l (by simpa using hc) φ fun v => ?_` and prove the remaining obligations. Use `hu (v - (n : ℂ) / 2) φ hφ` as an intermediate fact. Rewrite `this` using `[cap, show v - (n : ℂ) / 2 + (((n + 1 : ℕ) : ℂ) - 1) / 2 = v by push_cast; ring]`. Simplify using `using this`.
-/
theorem trace_Eop_eq : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (τ : E →+* ℂ) (m : Multiset ℂ), π.HasInfChar τ m → ∀ φ ∈ π.V, (∑ i : Fin a, Eop τ i i) φ = m.sum • φ := by
  intro E _ _ _ a π τ m hm φ hφ
  obtain ⟨hc, hu⟩ := hm
  rcases a with _ | n
  · obtain rfl : m = 0 := Multiset.card_eq_zero.1 hc
    simp
  · obtain ⟨l, rfl⟩ := Quot.exists_rep m
    refine trace_of_qdet (Eop τ) l (by simpa using hc) φ fun v => ?_
    have := hu (v - (n : ℂ) / 2) φ hφ
    rw [cap, show v - (n : ℂ) / 2 + (((n + 1 : ℕ) : ℂ) - 1) / 2 = v by push_cast; ring] at this
    simpa using this

end GlobalTheory.CompanionTheory.CapelliTrace

end
