import Formalism.LocalToGlobal.AlgebraicTheory.StatementD
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.TensZEt
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.TensorFourthPowerScaling
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.AlgTh

open Formalism.L2.Th1.H (cmL CmOK matH Sesq altE IsSelfDual IsHerm IsPosDef IsLat IsReps imgLat Th alphaQ opU taylorMv qOf
  dualLat)
open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.L2.Th1.G (linSub)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.CM (omegaK)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

namespace XiTorsion

section General

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Rewrite using `[LinearMap.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, smul_eq_mul]`. Take the linear combination `(H x y) * hs`.
-/
theorem herm_smul (H : Sesq V) (s : ℂ) (hs : s * conj s = 1) (x y : V) : H (s • x) (s • y) = H x y := by
  rw [LinearMap.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, smul_eq_mul]
  linear_combination (H x y) * hs

/- English proof (translation)
Simplify using `only [opU]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem opU_cmul (H : Sesq V) (x : V) (c : ℂ) (G : V → ℂ) (z : V) :
    opU H x (fun v => c * G v) z = c * opU H x G z := by
  simp only [opU]
  ring

/- English proof (translation)
Simplify using `only [opU, Finset.sum_mul]`.
-/
theorem opU_fsum {ι : Type} (H : Sesq V) (x : V) (S : Finset ι) (G : ι → V → ℂ) (z : V) :
    opU H x (fun v => ∑ i ∈ S, G i v) z = ∑ i ∈ S, opU H x (G i) z := by
  simp only [opU, Finset.sum_mul]

/- English proof (translation)
Unfold `cLat imgLat at h`. Take `⟨l, hl, rfl⟩` from `AddSubgroup.mem_map.mp h`. Conclude with `⟨l, hl, rfl⟩`.
-/
theorem mem_cLat {c : ℂ} {Λ : AddSubgroup V} {a : V} (h : a ∈ cLat c Λ) : ∃ l ∈ Λ, a = c • l := by
  unfold cLat imgLat at h
  obtain ⟨l, hl, rfl⟩ := AddSubgroup.mem_map.mp h
  exact ⟨l, hl, rfl⟩

/- English proof (translation)
Unfold `IsSelfDual at hsd`. Establish `hx' : x ∈ dualLat H Λ` using `by rw [hsd]; exact hx`. Conclude with `hx' y hy`.
-/
theorem altE_int {H : Sesq V} {Λ : AddSubgroup V} (hsd : IsSelfDual H Λ) {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    ∃ m : ℤ, altE H x y = m := by
  unfold IsSelfDual at hsd
  have hx' : x ∈ dualLat H Λ := by rw [hsd]; exact hx
  exact hx' y hy

/- English proof (translation)
Simplify using `[altE, LinearMap.map_smulₛₗ]`.
-/
theorem altE_smul_right (H : Sesq V) (x y : V) (c : ℕ) : altE H x ((c : ℂ) • y) = c * altE H x y := by
  simp [altE, LinearMap.map_smulₛₗ]

/- English proof (translation)
Simplify using `[altE]`.
-/
theorem altE_smul_left (H : Sesq V) (x y : V) (c : ℕ) : altE H ((c : ℂ) • x) y = c * altE H x y := by
  simp [altE]

/- English proof (translation)
Take `⟨m, hm⟩` from `altE_int hsd hω hl`. Use `⟨m, ?_⟩` and prove the remaining obligations. Rewrite using `[← hm]`. Establish `hr : (H l l).im = 0`. Establish `h1` using `congrArg Complex.im (hH l l)`.

Simplify using `only [Complex.conj_im] at h1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hom : omegaK dK = ⟨1 / 2, Real.sqrt dK / 2⟩`. Apply the tactic sequence `apply Complex.ext <;> simp [omegaK]`. Simplify using `only [qOf, altE, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, Complex.mul_im, hom, hr]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem q_int (H : Sesq V) (hH : IsHerm H) {Λ : AddSubgroup V} (hsd : IsSelfDual H Λ) (dK : ℕ) {l : V}
    (hl : l ∈ Λ) (hω : omegaK dK • l ∈ Λ) : ∃ k : ℤ, qOf (Real.sqrt dK / 2) H l = k := by
  obtain ⟨m, hm⟩ := altE_int hsd hω hl
  refine ⟨m, ?_⟩
  rw [← hm]
  have hr : (H l l).im = 0 := by
    have h1 := congrArg Complex.im (hH l l)
    simp only [Complex.conj_im] at h1
    linarith
  have hom : omegaK dK = ⟨1 / 2, Real.sqrt dK / 2⟩ := by
    apply Complex.ext <;> simp [omegaK]
  simp only [qOf, altE, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, Complex.mul_im, hom, hr]
  ring

end General

/- English proof (translation)
Take `⟨m, n, rfl⟩` from `h`. Establish `hc : conj (omegaK dK) = 1 - omegaK dK`. Rewrite using `[omegaK, map_div₀, map_add, map_one, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨m + n, -n, ?_⟩` and prove the remaining obligations.

Simplify using `only [map_add, map_mul, map_intCast, hc]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem qint_conj (dK : ℕ) (π : ℂ) (h : IsQInt dK π) : IsQInt dK (conj π) := by
  obtain ⟨m, n, rfl⟩ := h
  have hc : conj (omegaK dK) = 1 - omegaK dK := by
    rw [omegaK, map_div₀, map_add, map_one, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    ring
  refine ⟨m + n, -n, ?_⟩
  simp only [map_add, map_mul, map_intCast, hc]
  push_cast
  ring

section Norms

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Establish `h1 : ‖ι x‖ ^ m = 1` using `by rw [← norm_pow, ← map_pow, hx, map_one, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').mp h1`.
-/
theorem norm_root (ι : ℂ ≃+* ℂ_[p]) (x : ℂ) (m : ℕ) (hm : 0 < m) (hx : x ^ m = 1) : ‖ι x‖ = 1 := by
  have h1 : ‖ι x‖ ^ m = 1 := by rw [← norm_pow, ← map_pow, hx, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').mp h1

/- English proof (translation)
Apply `norm_root ι _ (2 * m) (by omega)` to reduce the goal to its premises. Rewrite using `[← Complex.exp_nat_mul]`. Establish `hy' : (m : ℂ) * (y : ℂ) = (k : ℂ)`. Establish `h0` using `congrArg Complex.ofReal hy`. Move the coercions through the operations in `at h0`.

Conclude with `h0`. Establish `e : ((2 * m : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I * (y : ℂ)) = (k : ℂ) * (2 * Real.pi * Complex.I)`. Use `push_cast`. Take the linear combination `(2 * (Real.pi : ℂ) * Complex.I) * hy'`. Rewrite using `[e, Complex.exp_int_mul_two_pi_mul_I]`.
-/
theorem norm_exp_piI (ι : ℂ ≃+* ℂ_[p]) (y : ℝ) (m : ℕ) (hm : 0 < m) (k : ℤ) (hy : (m : ℝ) * y = k) :
    ‖ι (Complex.exp ((Real.pi : ℂ) * Complex.I * (y : ℂ)))‖ = 1 := by
  apply norm_root ι _ (2 * m) (by omega)
  rw [← Complex.exp_nat_mul]
  have hy' : (m : ℂ) * (y : ℂ) = (k : ℂ) := by
    have h0 := congrArg Complex.ofReal hy
    push_cast at h0
    exact h0
  have e : ((2 * m : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I * (y : ℂ)) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    linear_combination (2 * (Real.pi : ℂ) * Complex.I) * hy'
  rw [e, Complex.exp_int_mul_two_pi_mul_I]

/- English proof (translation)
Establish `h` using `PadicComplex.norm_extends' p (n : ℚ_[p])`. Rewrite `h` using `[map_natCast]`. Rewrite using `[← h]`. Use `congr 1`. Conclude with `(map_natCast (UniformSpace.Completion.coeRingHom : PadicAlgCl p →+* ℂ_[p]) n).symm`.
-/
theorem norm_natCast_eq (n : ℕ) : ‖(n : ℂ_[p])‖ = ‖(n : ℚ_[p])‖ := by
  have h := PadicComplex.norm_extends' p (n : ℚ_[p])
  rw [map_natCast] at h
  rw [← h]
  congr 1
  exact (map_natCast (UniformSpace.Completion.coeRingHom : PadicAlgCl p →+* ℂ_[p]) n).symm

/- English proof (translation)
Establish `h` using `PadicComplex.norm_extends' p (T : ℚ_[p])`. Rewrite `h` using `[map_intCast]`. Rewrite using `[← h]`. Use `congr 1`. Conclude with `(map_intCast (UniformSpace.Completion.coeRingHom : PadicAlgCl p →+* ℂ_[p]) T).symm`.
-/
theorem norm_intCast_eq (T : ℤ) : ‖(T : ℂ_[p])‖ = ‖(T : ℚ_[p])‖ := by
  have h := PadicComplex.norm_extends' p (T : ℚ_[p])
  rw [map_intCast] at h
  rw [← h]
  congr 1
  exact (map_intCast (UniformSpace.Completion.coeRingHom : PadicAlgCl p →+* ℂ_[p]) T).symm

/- English proof (translation)
Rewrite using `[norm_intCast_eq]`. Conclude with `Padic.norm_int_le_one T`.
-/
theorem norm_intCast_le (T : ℤ) : ‖(T : ℂ_[p])‖ ≤ 1 := by
  rw [norm_intCast_eq]
  exact Padic.norm_int_le_one T

/- English proof (translation)
Rewrite `h` using `[norm_intCast_eq]`. Establish `h' : ‖(T : ℤ_[p])‖ < 1` using `by rwa [PadicInt.norm_def, PadicInt.coe_intCast]`. Conclude with `(PadicInt.norm_int_lt_one_iff_dvd T).mp h'`.
-/
theorem dvd_of_norm_intCast_lt (T : ℤ) (h : ‖(T : ℂ_[p])‖ < 1) : (p : ℤ) ∣ T := by
  rw [norm_intCast_eq] at h
  have h' : ‖(T : ℤ_[p])‖ < 1 := by rwa [PadicInt.norm_def, PadicInt.coe_intCast]
  exact (PadicInt.norm_int_lt_one_iff_dvd T).mp h'

/- English proof (translation)
Use `haveI := PadicComplex.isUltrametricDist p`. Establish `hp : p.Prime` using `Fact.out`. Establish `hone : ∀ d : ℕ, ¬ p ∣ d → ‖(d : ℂ_[p])‖ = 1`. Introduce `d hd`. Establish `h1 : ‖((d : ℤ) : ℂ_[p])‖ ≤ 1` using `norm_intCast_le (d : ℤ)`.

Establish `h2 : ¬ ‖((d : ℤ) : ℂ_[p])‖ < 1` using `fun h => hd (Int.natCast_dvd_natCast.mp (dvd_of_norm_intCast_lt _ h))`. Move the coercions through the operations in `at h1 h2`. Conclude with `le_antisymm h1 (not_lt.mp h2)`. Establish `hsq : (2 * omegaK dK - 1) ^ 2 = -(dK : ℂ)`. Establish `h1 : 2 * omegaK dK - 1 = Complex.I * ((Real.sqrt dK : ℝ) : ℂ)` using `by unfold omegaK; ring`.

Rewrite using `[h1, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hn : ‖ι (2 * omegaK dK - 1)‖ = 1`. Establish `h : ‖ι (2 * omegaK dK - 1)‖ ^ 2 = 1`.

Rewrite using `[← norm_pow, ← map_pow, hsq, map_neg, map_natCast, norm_neg, hone dK hpd]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h`. Establish `h2 : ‖(2 : ℂ_[p])‖ = 1`. Establish `h` using `hone 2 (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h))`. Conclude with `h` after adjusting the coercions.

Use `⟨hn, ?_⟩` and prove the remaining obligations. Establish `e : (2 : ℂ_[p]) * ι (omegaK dK) = ι (2 * omegaK dK - 1) + 1`. Rewrite using `[map_sub, map_mul, map_one, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : ‖(2 : ℂ_[p]) * ι (omegaK dK)‖ ≤ 1`.

Rewrite using `[e]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (by rw [hn, norm_one, max_self])`. Rewrite `h3` using `[norm_mul, h2, one_mul]`. Then use the resulting hypothesis.
-/
private theorem norm_two_omegaK_sub_one_and_norm_omegaK_le (dK : ℕ) (hp2 : p ≠ 2) (hpd : ¬ p ∣ dK) (ι : ℂ ≃+* ℂ_[p]) :
    ‖ι (2 * omegaK dK - 1)‖ = 1 ∧ ‖ι (omegaK dK)‖ ≤ 1 := by
  haveI := PadicComplex.isUltrametricDist p
  have hp : p.Prime := Fact.out
  have hone : ∀ d : ℕ, ¬ p ∣ d → ‖(d : ℂ_[p])‖ = 1 := by
    intro d hd
    have h1 : ‖((d : ℤ) : ℂ_[p])‖ ≤ 1 := norm_intCast_le (d : ℤ)
    have h2 : ¬ ‖((d : ℤ) : ℂ_[p])‖ < 1 := fun h => hd (Int.natCast_dvd_natCast.mp (dvd_of_norm_intCast_lt _ h))
    push_cast at h1 h2
    exact le_antisymm h1 (not_lt.mp h2)
  have hsq : (2 * omegaK dK - 1) ^ 2 = -(dK : ℂ) := by
    have h1 : 2 * omegaK dK - 1 = Complex.I * ((Real.sqrt dK : ℝ) : ℂ) := by unfold omegaK; ring
    rw [h1, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    push_cast
    ring
  have hn : ‖ι (2 * omegaK dK - 1)‖ = 1 := by
    have h : ‖ι (2 * omegaK dK - 1)‖ ^ 2 = 1 := by
      rw [← norm_pow, ← map_pow, hsq, map_neg, map_natCast, norm_neg, hone dK hpd]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h
  have h2 : ‖(2 : ℂ_[p])‖ = 1 := by
    have h := hone 2 (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h))
    exact_mod_cast h
  refine ⟨hn, ?_⟩
  have e : (2 : ℂ_[p]) * ι (omegaK dK) = ι (2 * omegaK dK - 1) + 1 := by
    rw [map_sub, map_mul, map_one, map_ofNat]
    ring
  have h3 : ‖(2 : ℂ_[p]) * ι (omegaK dK)‖ ≤ 1 := by
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (by rw [hn, norm_one, max_self])
  rwa [norm_mul, h2, one_mul] at h3

/- English proof (translation)
Use `haveI := PadicComplex.isUltrametricDist p`. Establish `hw` using `(norm_two_omegaK_sub_one_and_norm_omegaK_le dK hp2 hpd ι).2`. Rewrite using `[map_add, map_mul, map_intCast, map_intCast]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (norm_intCast_le a) ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`.

Conclude with `mul_le_one₀ (norm_intCast_le b) (norm_nonneg _) hw`.
-/
private theorem norm_int_add_int_mul_omegaK_le_one (dK : ℕ) (hp2 : p ≠ 2) (hpd : ¬ p ∣ dK) (ι : ℂ ≃+* ℂ_[p]) (a b : ℤ) :
    ‖ι ((a : ℂ) + b * omegaK dK)‖ ≤ 1 := by
  haveI := PadicComplex.isUltrametricDist p
  have hw := (norm_two_omegaK_sub_one_and_norm_omegaK_le dK hp2 hpd ι).2
  rw [map_add, map_mul, map_intCast, map_intCast]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (norm_intCast_le a) ?_)
  rw [norm_mul]
  exact mul_le_one₀ (norm_intCast_le b) (norm_nonneg _) hw

/- English proof (translation)
Use `haveI := PadicComplex.isUltrametricDist p`. Establish `hp : p.Prime` using `Fact.out`. Take `⟨hn, -⟩` from `norm_two_omegaK_sub_one_and_norm_omegaK_le dK hp2 hpd ι`. Take `⟨m, n, hπ⟩` from `hq`. Establish `hc : conj (omegaK dK) = 1 - omegaK dK`.

Rewrite using `[omegaK, map_div₀, map_add, map_one, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree. Establish `hconj : conj π = ((m + n : ℤ) : ℂ) + ((-n : ℤ) : ℂ) * omegaK dK`. Rewrite using `[hπ]`. Simplify using `only [map_add, map_mul, map_intCast, hc]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hsub : ∀ x y : ℂ_[p], ‖x - y‖ ≤ max ‖x‖ ‖y‖` using `fun x y => by`. Rewrite using `[sub_eq_add_neg, ← norm_neg y]`. Conclude with `IsUltrametricDist.norm_add_le_max _ _`.

Establish `hle : ‖ι π‖ ≤ 1` using `by rw [hπ]; exact norm_int_add_int_mul_omegaK_le_one dK hp2 hpd ι m n`. Break down `hle.lt_or_eq with hlt' | heq` into its components or cases. It suffices to derive a contradiction. Establish `hsum : ι π + ι (conj π) = ((2 * m + n : ℤ) : ℂ_[p])`. Rewrite using `[← map_add, hconj, hπ, show (m : ℂ) + n * omegaK dK + (((m + n : ℤ) : ℂ) + ((-n : ℤ) : ℂ) * omegaK dK) = ((2 * m + n : ℤ) : ℂ) by push_cast; ring, map_intCast]`.

Establish `hd1 : (p : ℤ) ∣ 2 * m + n` using `dvd_of_norm_intCast_lt _ (by`. Rewrite using `[← hsum]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hlt' hlt))`. Establish `hdiff : ι π - ι (conj π) = (n : ℂ_[p]) * ι (2 * omegaK dK - 1)`. Rewrite using `[← map_sub, hconj, hπ, show (m : ℂ) + n * omegaK dK - (((m + n : ℤ) : ℂ) + ((-n : ℤ) : ℂ) * omegaK dK) = (n : ℂ) * (2 * omegaK dK - 1) by push_cast; ring, map_mul, map_intCast]`.

Establish `hd2 : (p : ℤ) ∣ n` using `dvd_of_norm_intCast_lt _ (by`. Establish `h` using `(hsub _ _).trans_lt (max_lt hlt' hlt)`. Rewrite `h` using `[hdiff, norm_mul, hn, mul_one]`. Conclude with `h)`. Establish `hpZ : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.mp hp`.

Establish `hd3 : (p : ℤ) ∣ 2 * m`. Establish `h` using `dvd_sub hd1 hd2`. Simplify using `using h`. Establish `hdm : (p : ℤ) ∣ m` using `(hpZ.dvd_or_dvd hd3).resolve_left (fun h => hp2 (by`. Establish `h' : p ∣ 2` using `by exact_mod_cast h`.

Conclude with `(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h'))`. Take `⟨m', rfl⟩` from `hdm`. Take `⟨n', rfl⟩` from `hd2`. Establish `e1 : π = (p : ℂ) * ((m' : ℂ) + n' * omegaK dK)` using `by rw [hπ]; push_cast; ring`. Establish `e2 : conj π = (p : ℂ) * (((m' + n' : ℤ) : ℂ) + ((-n' : ℤ) : ℂ) * omegaK dK)`.

Rewrite using `[e1, map_mul, map_natCast]`. Simplify using `only [map_add, map_mul, map_intCast, hc]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hA : ‖ι π‖ ≤ ‖(p : ℂ_[p])‖`.

Rewrite using `[e1, map_mul, map_natCast, norm_mul]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) (norm_int_add_int_mul_omegaK_le_one dK hp2 hpd ι m' n')`. Establish `hB : ‖ι (conj π)‖ ≤ ‖(p : ℂ_[p])‖`. Rewrite using `[e2, map_mul, map_natCast, norm_mul]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) (norm_int_add_int_mul_omegaK_le_one dK hp2 hpd ι _ _)`.

Establish `hprod : ‖ι π‖ * ‖ι (conj π)‖ = ‖(p : ℂ_[p])‖`. Rewrite using `[← norm_mul, ← map_mul, hpp, map_natCast]`. Establish `hp1 : ‖(p : ℂ_[p])‖ < 1`. Rewrite using `[norm_natCast_eq]`. Conclude with `Padic.norm_p_lt_one`.

Establish `hp0 : 0 < ‖(p : ℂ_[p])‖` using `norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)`. Establish `hm` using `mul_le_mul hA hB (norm_nonneg _) (norm_nonneg _)`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `heq`.
-/
theorem norm_pi_one (dK : ℕ) (hp2 : p ≠ 2) (hpd : ¬ p ∣ dK) (ι : ℂ ≃+* ℂ_[p]) (π : ℂ) (hq : IsQInt dK π)
    (hpp : π * conj π = p) (hlt : ‖ι (conj π)‖ < 1) : ‖ι π‖ = 1 := by
  haveI := PadicComplex.isUltrametricDist p
  have hp : p.Prime := Fact.out
  obtain ⟨hn, -⟩ := norm_two_omegaK_sub_one_and_norm_omegaK_le dK hp2 hpd ι
  obtain ⟨m, n, hπ⟩ := hq
  have hc : conj (omegaK dK) = 1 - omegaK dK := by
    rw [omegaK, map_div₀, map_add, map_one, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    ring
  have hconj : conj π = ((m + n : ℤ) : ℂ) + ((-n : ℤ) : ℂ) * omegaK dK := by
    rw [hπ]
    simp only [map_add, map_mul, map_intCast, hc]
    push_cast
    ring
  have hsub : ∀ x y : ℂ_[p], ‖x - y‖ ≤ max ‖x‖ ‖y‖ := fun x y => by
    rw [sub_eq_add_neg, ← norm_neg y]
    exact IsUltrametricDist.norm_add_le_max _ _
  have hle : ‖ι π‖ ≤ 1 := by rw [hπ]; exact norm_int_add_int_mul_omegaK_le_one dK hp2 hpd ι m n
  rcases hle.lt_or_eq with hlt' | heq
  · exfalso
    have hsum : ι π + ι (conj π) = ((2 * m + n : ℤ) : ℂ_[p]) := by
      rw [← map_add, hconj, hπ, show (m : ℂ) + n * omegaK dK + (((m + n : ℤ) : ℂ) + ((-n : ℤ) : ℂ) * omegaK dK) =
        ((2 * m + n : ℤ) : ℂ) by push_cast; ring, map_intCast]
    have hd1 : (p : ℤ) ∣ 2 * m + n := dvd_of_norm_intCast_lt _ (by
      rw [← hsum]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hlt' hlt))
    have hdiff : ι π - ι (conj π) = (n : ℂ_[p]) * ι (2 * omegaK dK - 1) := by
      rw [← map_sub, hconj, hπ, show (m : ℂ) + n * omegaK dK - (((m + n : ℤ) : ℂ) + ((-n : ℤ) : ℂ) * omegaK dK) =
        (n : ℂ) * (2 * omegaK dK - 1) by push_cast; ring, map_mul, map_intCast]
    have hd2 : (p : ℤ) ∣ n := dvd_of_norm_intCast_lt _ (by
      have h := (hsub _ _).trans_lt (max_lt hlt' hlt)
      rw [hdiff, norm_mul, hn, mul_one] at h
      exact h)
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hd3 : (p : ℤ) ∣ 2 * m := by
      have h := dvd_sub hd1 hd2
      simpa using h
    have hdm : (p : ℤ) ∣ m := (hpZ.dvd_or_dvd hd3).resolve_left (fun h => hp2 (by
      have h' : p ∣ 2 := by exact_mod_cast h
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h'))
    obtain ⟨m', rfl⟩ := hdm
    obtain ⟨n', rfl⟩ := hd2
    have e1 : π = (p : ℂ) * ((m' : ℂ) + n' * omegaK dK) := by rw [hπ]; push_cast; ring
    have e2 : conj π = (p : ℂ) * (((m' + n' : ℤ) : ℂ) + ((-n' : ℤ) : ℂ) * omegaK dK) := by
      rw [e1, map_mul, map_natCast]
      simp only [map_add, map_mul, map_intCast, hc]
      push_cast
      ring
    have hA : ‖ι π‖ ≤ ‖(p : ℂ_[p])‖ := by
      rw [e1, map_mul, map_natCast, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (norm_int_add_int_mul_omegaK_le_one dK hp2 hpd ι m' n')
    have hB : ‖ι (conj π)‖ ≤ ‖(p : ℂ_[p])‖ := by
      rw [e2, map_mul, map_natCast, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (norm_int_add_int_mul_omegaK_le_one dK hp2 hpd ι _ _)
    have hprod : ‖ι π‖ * ‖ι (conj π)‖ = ‖(p : ℂ_[p])‖ := by
      rw [← norm_mul, ← map_mul, hpp, map_natCast]
    have hp1 : ‖(p : ℂ_[p])‖ < 1 := by
      rw [norm_natCast_eq]
      exact Padic.norm_p_lt_one
    have hp0 : 0 < ‖(p : ℂ_[p])‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
    have hm := mul_le_mul hA hB (norm_nonneg _) (norm_nonneg _)
    nlinarith
  · exact heq

end Norms

end XiTorsion

/- English proof (translation)
Introduce `dK n _ _ h Λ hH hsd hα q hq π hπ hΛ1 hΛ2 Sa Sb hSa hSb θ hθ C' hC' hfe Ψ z`. Establish `hρ : π / conj π * conj (π / conj π) = 1`. Establish `hc : conj π ≠ 0` using `(map_ne_zero _).mpr hπ`. Rewrite using `[map_div₀, Complex.conj_conj]`. Clear the denominators using the available nonvanishing facts.

Establish `hfix : θ ∈ Formalism.L2.Th1.H.fixedBy (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ` using `hθ.2`. Establish `key : ∀ b ∈ Sb, alphaQ (Real.sqrt dK / 2) (matH h) b * opU (matH h) ((π / conj π) • b) θ ((π / conj π) • z) = C' * ∑ a ∈ Sa, Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE (matH h) b a : ℂ)) * alphaQ (Real.sqrt dK / 2) (matH h) a * opU (matH h) a θ z`. Introduce `b hb`. Establish `hbΛ : b ∈ Λ` using `hSb.1 b hb`. Establish `hαb2 : alphaQ (Real.sqrt dK / 2) (matH h) b * alphaQ (Real.sqrt dK / 2) (matH h) b = 1`.

Apply the tactic sequence `rcases hα.1 b hbΛ with e | e <;> rw [e] <;> norm_num`. Establish `hinv : ∀ w, θ (w + b) = alphaQ (Real.sqrt dK / 2) (matH h) b * θ w * Complex.exp ((Real.pi : ℂ) * matH h w b + (Real.pi : ℂ) * matH h b b / 2)`. Introduce `w`. Establish `e : alphaQ (Real.sqrt dK / 2) (matH h) b * opU (matH h) b θ w = θ w` using `hfix b hbΛ w`. Simplify using `only [opU] at e`.

Rewrite using `[← e]`. Establish `hx : Complex.exp (-(Real.pi : ℂ) * matH h w b - (Real.pi : ℂ) * matH h b b / 2) * Complex.exp ((Real.pi : ℂ) * matH h w b + (Real.pi : ℂ) * matH h b b / 2) = 1`. Rewrite using `[← Complex.exp_add, show -(Real.pi : ℂ) * matH h w b - (Real.pi : ℂ) * matH h b b / 2 + ((Real.pi : ℂ) * matH h w b + (Real.pi : ℂ) * matH h b b / 2) = 0 by ring, Complex.exp_zero]`. Take the linear combination `(-(θ (w + b)) * Complex.exp (-(Real.pi : ℂ) * matH h w b - (Real.pi : ℂ) * matH h b b / 2) * Complex.exp ((Real.pi : ℂ) * matH h w b + (Real.pi : ℂ) * matH h b b / 2)) * hαb2 + (-(θ (w + b))) * hx`. Simplify using `only [opU]`.

Rewrite using `[← smul_add, XiTorsion.herm_smul (matH h) _ hρ, XiTorsion.herm_smul (matH h) _ hρ, hfe (z + b)]`. Simplify using `only [opU, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[show z + b + a = (z + a) + b by abel, hinv (z + a)]`. Establish `l1 : matH h (z + a) b = matH h z b + matH h a b` using `by rw [map_add, LinearMap.add_apply]`.

Establish `l2 : matH h (z + b) a = matH h z a + matH h b a` using `by rw [map_add, LinearMap.add_apply]`. Establish `hE0 : matH h a b - matH h b a = -(2 * Complex.I * (altE (matH h) b a : ℂ))`. Rewrite using `[hH b a]`. Unfold `altE`. Apply the tactic sequence `apply Complex.ext <;> simp <;> ring`.

Establish `hE : Complex.exp ((Real.pi : ℂ) * matH h (z + a) b + (Real.pi : ℂ) * matH h b b / 2) * Complex.exp (-(Real.pi : ℂ) * matH h (z + b) a - (Real.pi : ℂ) * matH h a a / 2) * Complex.exp (-(Real.pi : ℂ) * matH h z b - (Real.pi : ℂ) * matH h b b / 2) = Complex.exp (-(2 * (Real.pi : ℂ)) …`. Rewrite using `[← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]`. Use `congr 1`. Rewrite using `[l1, l2]`. Take the linear combination `(Real.pi : ℂ) * hE0`.

Take the linear combination `(C' * alphaQ (Real.sqrt dK / 2) (matH h) a * θ (z + a) * (Complex.exp ((Real.pi : ℂ) * matH h (z + a) b + (Real.pi : ℂ) * matH h b b / 2) * Complex.exp (-(Real.pi : ℂ) * matH h (z + b) a - (Real.pi : ℂ) * matH h a a / 2) * Complex.exp (-(Real.pi : ℂ) * matH h z b - (Real.pi : ℂ) …`. Establish `hq0 : (q : ℂ) ≠ 0` using `by exact_mod_cast hq.ne'`. Unfold `xiG xiHat`. Establish `hR : ∀ b ∈ Sb, Ψ b * alphaQ (Real.sqrt dK / 2) (matH h) b * opU (matH h) ((π / conj π) • b) θ ((π / conj π) • z) = Ψ b * (C' * ∑ a ∈ Sa, Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE (matH h) b a : ℂ)) * alphaQ (Real.sqrt dK / 2) (matH h) a * opU (matH h) a θ z)` using `fun b hb => by`. Rewrite using `[mul_assoc, key b hb]`.

Rewrite using `[Finset.sum_congr rfl hR]`. Repeatedly rewrite using `[Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts.

Apply the tactic sequence `try ring`.
-/
theorem xi_swap : XiSwap := by
  intro dK n _ _ h Λ hH hsd hα q hq π hπ hΛ1 hΛ2 Sa Sb hSa hSb θ hθ C' hC' hfe Ψ z
  have hρ : π / conj π * conj (π / conj π) = 1 := by
    have hc : conj π ≠ 0 := (map_ne_zero _).mpr hπ
    rw [map_div₀, Complex.conj_conj]
    field_simp
  have hfix : θ ∈ Formalism.L2.Th1.H.fixedBy (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ := hθ.2
  have key : ∀ b ∈ Sb, alphaQ (Real.sqrt dK / 2) (matH h) b * opU (matH h) ((π / conj π) • b) θ ((π / conj π) • z) =
      C' * ∑ a ∈ Sa, Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE (matH h) b a : ℂ)) *
        alphaQ (Real.sqrt dK / 2) (matH h) a * opU (matH h) a θ z := by
    intro b hb
    have hbΛ : b ∈ Λ := hSb.1 b hb
    have hαb2 : alphaQ (Real.sqrt dK / 2) (matH h) b * alphaQ (Real.sqrt dK / 2) (matH h) b = 1 := by
      rcases hα.1 b hbΛ with e | e <;> rw [e] <;> norm_num
    have hinv : ∀ w, θ (w + b) = alphaQ (Real.sqrt dK / 2) (matH h) b * θ w *
        Complex.exp ((Real.pi : ℂ) * matH h w b + (Real.pi : ℂ) * matH h b b / 2) := by
      intro w
      have e : alphaQ (Real.sqrt dK / 2) (matH h) b * opU (matH h) b θ w = θ w := hfix b hbΛ w
      simp only [opU] at e
      rw [← e]
      have hx : Complex.exp (-(Real.pi : ℂ) * matH h w b - (Real.pi : ℂ) * matH h b b / 2) *
          Complex.exp ((Real.pi : ℂ) * matH h w b + (Real.pi : ℂ) * matH h b b / 2) = 1 := by
        rw [← Complex.exp_add, show -(Real.pi : ℂ) * matH h w b - (Real.pi : ℂ) * matH h b b / 2 +
          ((Real.pi : ℂ) * matH h w b + (Real.pi : ℂ) * matH h b b / 2) = 0 by ring, Complex.exp_zero]
      linear_combination (-(θ (w + b)) * Complex.exp (-(Real.pi : ℂ) * matH h w b - (Real.pi : ℂ) * matH h b b / 2) *
          Complex.exp ((Real.pi : ℂ) * matH h w b + (Real.pi : ℂ) * matH h b b / 2)) * hαb2 +
        (-(θ (w + b))) * hx
    simp only [opU]
    rw [← smul_add, XiTorsion.herm_smul (matH h) _ hρ, XiTorsion.herm_smul (matH h) _ hρ, hfe (z + b)]
    simp only [opU, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show z + b + a = (z + a) + b by abel, hinv (z + a)]
    have l1 : matH h (z + a) b = matH h z b + matH h a b := by rw [map_add, LinearMap.add_apply]
    have l2 : matH h (z + b) a = matH h z a + matH h b a := by rw [map_add, LinearMap.add_apply]
    have hE0 : matH h a b - matH h b a = -(2 * Complex.I * (altE (matH h) b a : ℂ)) := by
      rw [hH b a]
      unfold altE
      apply Complex.ext <;> simp <;> ring
    have hE : Complex.exp ((Real.pi : ℂ) * matH h (z + a) b + (Real.pi : ℂ) * matH h b b / 2) *
        Complex.exp (-(Real.pi : ℂ) * matH h (z + b) a - (Real.pi : ℂ) * matH h a a / 2) *
        Complex.exp (-(Real.pi : ℂ) * matH h z b - (Real.pi : ℂ) * matH h b b / 2) =
        Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE (matH h) b a : ℂ)) *
        Complex.exp (-(Real.pi : ℂ) * matH h z a - (Real.pi : ℂ) * matH h a a / 2) := by
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      rw [l1, l2]
      linear_combination (Real.pi : ℂ) * hE0
    linear_combination (C' * alphaQ (Real.sqrt dK / 2) (matH h) a * θ (z + a) *
        (Complex.exp ((Real.pi : ℂ) * matH h (z + a) b + (Real.pi : ℂ) * matH h b b / 2) *
        Complex.exp (-(Real.pi : ℂ) * matH h (z + b) a - (Real.pi : ℂ) * matH h a a / 2) *
        Complex.exp (-(Real.pi : ℂ) * matH h z b - (Real.pi : ℂ) * matH h b b / 2))) * hαb2 +
      (C' * alphaQ (Real.sqrt dK / 2) (matH h) a * θ (z + a)) * hE
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  unfold xiG xiHat
  have hR : ∀ b ∈ Sb, Ψ b * alphaQ (Real.sqrt dK / 2) (matH h) b *
      opU (matH h) ((π / conj π) • b) θ ((π / conj π) • z) =
      Ψ b * (C' * ∑ a ∈ Sa, Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE (matH h) b a : ℂ)) *
        alphaQ (Real.sqrt dK / 2) (matH h) a * opU (matH h) a θ z) := fun b hb => by
    rw [mul_assoc, key b hb]
  rw [Finset.sum_congr rfl hR]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  field_simp
  try ring

/- English proof (translation)
Introduce `a₀ b₀ c₀ dK ha hdK lam hlam hOK n _ _ h Λ hH _ _ hsd hSt θ hθ p _ hp2 hpd ι hInt hLoc π hπq hpp hlt Sa Sb hSa hSb Ψ hΨ κx _ r t N hr hN hpN ht J _ v hv ν _ A hA`. Establish `hp : p.Prime` using `Fact.out`. Establish `hΛq : ∀ β : ℂ, IsQInt dK β → ∀ x ∈ Λ, β • x ∈ Λ` using `TensorIntegralTorsion.qint_smul_mem Λ b₀ dK (TensorIntegralTorsion.odd_b hOK) hSt`. Establish `hnat : ∀ m : ℕ, IsQInt dK (m : ℂ)` using `fun m => ⟨m, 0, by simp⟩`. Establish `hp0 : (p : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hp.ne_zero`.

Establish `hπ0 : π ≠ 0` using `by rintro rfl; rw [zero_mul] at hpp; exact hp0 hpp.symm`. Establish `hπ'0 : conj π ≠ 0` using `by rwa [ne_eq, map_eq_zero]`. Establish `hcq : IsQInt dK (conj π)` using `XiTorsion.qint_conj dK π hπq`. Establish `hs1 : (conj π / π) * conj (conj π / π) = 1`. Rewrite using `[map_div₀, Complex.conj_conj]`.

Clear the denominators using the available nonvanishing facts. Establish `hSa' : ∀ a ∈ Sa, ∃ l ∈ Λ, a = (conj π / π) • l` using `fun a ha => XiTorsion.mem_cLat (hSa.1 a ha)`. Establish `hpa : ∀ a ∈ Sa, (p : ℂ) • a ∈ Λ`. Introduce `a ha`. Take `⟨l, hl, rfl⟩` from `hSa' a ha`.

Establish `e : (p : ℂ) • (conj π / π) • l = conj π • conj π • l`. Rewrite using `[smul_smul, smul_smul, ← hpp]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`.

Conclude with `hΛq _ hcq _ (hΛq _ hcq _ hl)`. Establish `hπa : ∀ a ∈ Sa, π • a ∈ Λ`. Introduce `a ha`. Take `⟨l, hl, rfl⟩` from `hSa' a ha`. Establish `e : π • (conj π / π) • l = conj π • l`.

Rewrite using `[smul_smul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `hΛq _ hcq _ hl`.

Set `cc : κx × Sa → ℂ` to `fun x => r x.1 * (xiHat (matH h) (p ^ Fintype.card n) Ψ Sb x.2 * alphaQ (Real.sqrt dK / 2) (matH h) x.2) * Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE (matH h) (t x.1) x.2 : ℂ))`. Set `r' : κx × Sa → ℂ_[p]` to `fun x => (p : ℂ_[p]) ^ Fintype.card n * ι (cc x)`. Set `t' : κx × Sa → n → ℂ` to `fun x => t x.1 + x.2`. Establish `hxG : xiG (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) θ (p ^ Fintype.card n) Ψ Sa Sb = fun v => ∑ a ∈ Sa, (xiHat (matH h) (p ^ Fintype.card n) Ψ Sb a * alphaQ (Real.sqrt dK / 2) (matH h) a) * opU (matH h) a θ v`. Use function extensionality and compare the values at `v`.

Both sides reduce to the same expression. Establish `hfun : (fun z => ∑ k, r k * opU (matH h) (t k) (xiG (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) θ (p ^ Fintype.card n) Ψ Sa Sb) z) = fun z => ∑ x ∈ (Finset.univ : Finset (κx × Sa)), cc x * opU (matH h) (t' x) θ z`. Use function extensionality and compare the values at `z`. Rewrite using `[Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[hxG, XiTorsion.opU_fsum, Finset.mul_sum]`. Use `symm`. Use `(Finset.sum_coe_sort Sa (fun a => r k * (xiHat (matH h) (p ^ Fintype.card n) Ψ Sb a * alphaQ (Real.sqrt dK / 2) (matH h) a) * Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE (matH h) (t k) a : ℂ)) * opU (matH h) (t k + a) θ z)).trans ?_` and prove the remaining obligations. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[XiTorsion.opU_cmul, Formalism.L2.Th1.H.opUMul _ (matH h) hH]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hT` using `(Formalism.L2.Th1.H.FormalGroupLawNegation.taylorMv_sum Formalism.L2.Th1.H.taylorMvLinear (Finset.univ : Finset (κx × Sa)) cc (fun x => opU (matH h) (t' x) θ) fun x => Formalism.L2.Th1.H.opUAnalytic _ (matH h) (t' x) θ hθ.1 0 (Set.mem_univ _)).2`. Establish `hser : MvPowerSeries.C ((p : ℂ_[p]) ^ Fintype.card n) * serLin ι h (xiG (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) θ (p ^ Fintype.card n) Ψ Sa Sb) r t (frameM (ι : ℂ →+* ℂ_[p]) v A) = thetaLin (ι : ℂ →+* ℂ_[p]) h θ r' t' (frameM (ι : ℂ →+* ℂ_[p]) v A)`. Unfold `serLin thetaLin`. Rewrite using `[hfun, hT, map_sum, ← Formalism.L2.Th1.G.linSubHom_apply, map_sum, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, MvPowerSeries.map_C, map_mul, Formalism.L2.Th1.G.linSubHom_apply, Formalism.L2.Th1.G.linSubHom_apply, Formalism.L2.Th1.G.linSub_C, ← mul_assoc, ← map_mul]`. Both sides reduce to the same expression. Rewrite using `[hser]`. Establish `hxh : ∀ a ∈ Sa, ‖ι ((p : ℂ) ^ Fintype.card n * xiHat (matH h) (p ^ Fintype.card n) Ψ Sb a)‖ ≤ 1`.

Introduce `a ha`. Establish `e : (p : ℂ) ^ Fintype.card n * xiHat (matH h) (p ^ Fintype.card n) Ψ Sb a = ∑ b ∈ Sb, Ψ b * Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE (matH h) b a : ℂ))`. Unfold `xiHat`. Use `push_cast`. Rewrite using `[← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hp0), one_mul]`.

Rewrite using `[e, map_sum]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun b hb => ?_` and prove the remaining obligations. Take `⟨m, hm⟩` from `XiTorsion.altE_int hsd (hSb.1 b hb) (hpa a ha)`. Rewrite `hm` using `[XiTorsion.altE_smul_right]`. Establish `e2 : Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE (matH h) b a : ℂ)) = Complex.exp ((Real.pi : ℂ) * Complex.I * ((-2 * altE (matH h) b a : ℝ) : ℂ))`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_mul, norm_mul, e2, XiTorsion.norm_exp_piI ι _ p hp.pos (-2 * m) (by push_cast; linear_combination -2 * hm), mul_one]`. Conclude with `hΨ b hb`.

Establish `hr' : ∀ x, ‖r' x‖ ≤ 1`. Introduce and unpack `⟨k, a, haS⟩`. Take `⟨l, hl, hal⟩` from `hSa' a haS`. Establish `h3 : ‖ι (alphaQ (Real.sqrt dK / 2) (matH h) a)‖ = 1`. Establish `e : alphaQ (Real.sqrt dK / 2) (matH h) a = alphaQ (Real.sqrt dK / 2) (matH h) l`.

Unfold `alphaQ qOf`. Rewrite using `[hal, XiTorsion.herm_smul _ _ hs1]`. Take `⟨m, hm⟩` from `XiTorsion.q_int (matH h) hH hsd dK hl (hΛq _ ⟨0, 1, by simp⟩ l hl)`. Rewrite using `[e]`. Unfold `alphaQ`.

Rewrite using `[hm]`. Conclude with `XiTorsion.norm_exp_piI ι _ 1 one_pos m (by simp)`. Establish `h4 : ‖ι (Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE (matH h) (t k) a : ℂ)))‖ = 1`. Take `⟨m, hm⟩` from `XiTorsion.altE_int hsd (ht k) (hpa a haS)`. Rewrite `hm` using `[XiTorsion.altE_smul_left, XiTorsion.altE_smul_right]`.

Establish `e2 : Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE (matH h) (t k) a : ℂ)) = Complex.exp ((Real.pi : ℂ) * Complex.I * ((-altE (matH h) (t k) a : ℝ) : ℂ))`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`.

Conclude with `XiTorsion.norm_exp_piI ι _ (N * p) (Nat.mul_pos hN hp.pos) (-m) (by push_cast; linear_combination -hm)`. Establish `e : r' (k, ⟨a, haS⟩) = ι (r k) * ι ((p : ℂ) ^ Fintype.card n * xiHat (matH h) (p ^ Fintype.card n) Ψ Sb a) * ι (alphaQ (Real.sqrt dK / 2) (matH h) a) * ι (Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE (matH h) (t k) a : ℂ)))`. Simplify using `only [r', cc, map_mul, map_pow, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, norm_mul, norm_mul, norm_mul, h3, h4, mul_one, mul_one]`.

Conclude with `mul_le_one₀ (hr k) (norm_nonneg _) (hxh a haS)`. Establish `hαq : IsQInt dK ((N : ℂ) * π)`. Take `⟨m, k, hm⟩` from `hπq`. Conclude with `⟨N * m, N * k, by rw [hm]; push_cast; ring⟩`. Establish `hαn : ‖ι ((N : ℂ) * π)‖ = 1`.

Rewrite using `[map_mul, map_natCast, norm_mul, LocalJetRescaling.norm_natCast p hpN, one_mul]`. Conclude with `XiTorsion.norm_pi_one dK hp2 hpd ι π hπq hpp hlt`. Establish `hαt : ∀ x, ((N : ℂ) * π) • t' x ∈ Λ`. Introduce and unpack `⟨k, a, haS⟩`. Use `show ((N : ℂ) * π) • (t k + a) ∈ Λ`.

Rewrite using `[smul_add]`. Use `Λ.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`. Conclude with `hΛq π hπq _ (ht k)`. Rewrite using `[mul_smul]`.

Conclude with `hΛq _ (hnat N) _ (hπa a haS)`. Establish `hMt : ∀ x, ((N * p : ℕ) : ℂ) • t' x ∈ Λ`. Introduce and unpack `⟨k, a, haS⟩`. Use `show ((N * p : ℕ) : ℂ) • (t k + a) ∈ Λ`. Rewrite using `[smul_add, Nat.cast_mul]`.

Use `Λ.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`. Conclude with `hΛq _ (hnat p) _ (ht k)`. Rewrite using `[mul_smul]`. Conclude with `hΛq _ (hnat N) _ (hpa a haS)`.

Establish `hA' : ∀ j x, ‖A j x‖ ≤ ‖((N * p : ℕ) : ℂ_[p])‖`. Introduce `j x`. Rewrite using `[Nat.cast_mul, norm_mul, LocalJetRescaling.norm_natCast p hpN, one_mul]`. Conclude with `hA j x`. Conclude with `(hE a₀ b₀ c₀ dK ha hdK lam hlam hOK n h Λ hsd hSt θ hθ p hp2 hpd ι hInt hLoc (κx × Sa) r' t' ((N : ℂ) * π) (N * p) hr' hαq hαn (Nat.mul_pos hN hp.pos) hαt hMt J v hv ν A hA').1`.
-/
theorem xiEt_of (hE : EtLoc) : XiEt := by
  intro a₀ b₀ c₀ dK ha hdK lam hlam hOK n _ _ h Λ hH _ _ hsd hSt θ hθ p _ hp2 hpd ι hInt hLoc π hπq hpp hlt
    Sa Sb hSa hSb Ψ hΨ κx _ r t N hr hN hpN ht J _ v hv ν _ A hA
  classical
  have hp : p.Prime := Fact.out
  have hΛq : ∀ β : ℂ, IsQInt dK β → ∀ x ∈ Λ, β • x ∈ Λ :=
    TensorIntegralTorsion.qint_smul_mem Λ b₀ dK (TensorIntegralTorsion.odd_b hOK) hSt
  have hnat : ∀ m : ℕ, IsQInt dK (m : ℂ) := fun m => ⟨m, 0, by simp⟩
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hπ0 : π ≠ 0 := by rintro rfl; rw [zero_mul] at hpp; exact hp0 hpp.symm
  have hπ'0 : conj π ≠ 0 := by rwa [ne_eq, map_eq_zero]
  have hcq : IsQInt dK (conj π) := XiTorsion.qint_conj dK π hπq
  have hs1 : (conj π / π) * conj (conj π / π) = 1 := by
    rw [map_div₀, Complex.conj_conj]; field_simp
  have hSa' : ∀ a ∈ Sa, ∃ l ∈ Λ, a = (conj π / π) • l := fun a ha => XiTorsion.mem_cLat (hSa.1 a ha)
  have hpa : ∀ a ∈ Sa, (p : ℂ) • a ∈ Λ := by
    intro a ha
    obtain ⟨l, hl, rfl⟩ := hSa' a ha
    have e : (p : ℂ) • (conj π / π) • l = conj π • conj π • l := by
      rw [smul_smul, smul_smul, ← hpp]; congr 1; field_simp
    rw [e]; exact hΛq _ hcq _ (hΛq _ hcq _ hl)
  have hπa : ∀ a ∈ Sa, π • a ∈ Λ := by
    intro a ha
    obtain ⟨l, hl, rfl⟩ := hSa' a ha
    have e : π • (conj π / π) • l = conj π • l := by
      rw [smul_smul]; congr 1; field_simp
    rw [e]; exact hΛq _ hcq _ hl

  let cc : κx × Sa → ℂ := fun x => r x.1 *
    (xiHat (matH h) (p ^ Fintype.card n) Ψ Sb x.2 * alphaQ (Real.sqrt dK / 2) (matH h) x.2) *
      Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE (matH h) (t x.1) x.2 : ℂ))
  let r' : κx × Sa → ℂ_[p] := fun x => (p : ℂ_[p]) ^ Fintype.card n * ι (cc x)
  let t' : κx × Sa → n → ℂ := fun x => t x.1 + x.2
  have hxG : xiG (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) θ (p ^ Fintype.card n) Ψ Sa Sb =
      fun v => ∑ a ∈ Sa, (xiHat (matH h) (p ^ Fintype.card n) Ψ Sb a * alphaQ (Real.sqrt dK / 2) (matH h) a) *
        opU (matH h) a θ v := by
    funext v; rfl
  have hfun : (fun z => ∑ k, r k * opU (matH h) (t k)
      (xiG (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) θ (p ^ Fintype.card n) Ψ Sa Sb) z) =
      fun z => ∑ x ∈ (Finset.univ : Finset (κx × Sa)), cc x * opU (matH h) (t' x) θ z := by
    funext z
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hxG, XiTorsion.opU_fsum, Finset.mul_sum]
    symm
    refine (Finset.sum_coe_sort Sa (fun a => r k *
      (xiHat (matH h) (p ^ Fintype.card n) Ψ Sb a * alphaQ (Real.sqrt dK / 2) (matH h) a) *
        Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE (matH h) (t k) a : ℂ)) * opU (matH h) (t k + a) θ z)).trans ?_
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [XiTorsion.opU_cmul, Formalism.L2.Th1.H.opUMul _ (matH h) hH]
    ring
  have hT := (Formalism.L2.Th1.H.FormalGroupLawNegation.taylorMv_sum Formalism.L2.Th1.H.taylorMvLinear (Finset.univ : Finset (κx × Sa)) cc
    (fun x => opU (matH h) (t' x) θ)
    fun x => Formalism.L2.Th1.H.opUAnalytic _ (matH h) (t' x) θ hθ.1 0 (Set.mem_univ _)).2
  have hser : MvPowerSeries.C ((p : ℂ_[p]) ^ Fintype.card n) *
      serLin ι h (xiG (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) θ (p ^ Fintype.card n) Ψ Sa Sb) r t
        (frameM (ι : ℂ →+* ℂ_[p]) v A) =
      thetaLin (ι : ℂ →+* ℂ_[p]) h θ r' t' (frameM (ι : ℂ →+* ℂ_[p]) v A) := by
    unfold serLin thetaLin
    rw [hfun, hT, map_sum, ← Formalism.L2.Th1.G.linSubHom_apply, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_mul, MvPowerSeries.map_C, map_mul, Formalism.L2.Th1.G.linSubHom_apply, Formalism.L2.Th1.G.linSubHom_apply,
      Formalism.L2.Th1.G.linSub_C, ← mul_assoc, ← map_mul]
    rfl
  rw [hser]

  have hxh : ∀ a ∈ Sa, ‖ι ((p : ℂ) ^ Fintype.card n * xiHat (matH h) (p ^ Fintype.card n) Ψ Sb a)‖ ≤ 1 := by
    intro a ha
    have e : (p : ℂ) ^ Fintype.card n * xiHat (matH h) (p ^ Fintype.card n) Ψ Sb a =
        ∑ b ∈ Sb, Ψ b * Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE (matH h) b a : ℂ)) := by
      unfold xiHat; push_cast
      rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hp0), one_mul]
    rw [e, map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun b hb => ?_
    obtain ⟨m, hm⟩ := XiTorsion.altE_int hsd (hSb.1 b hb) (hpa a ha)
    rw [XiTorsion.altE_smul_right] at hm
    have e2 : Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE (matH h) b a : ℂ)) =
        Complex.exp ((Real.pi : ℂ) * Complex.I * ((-2 * altE (matH h) b a : ℝ) : ℂ)) := by
      congr 1; push_cast; ring
    rw [map_mul, norm_mul, e2, XiTorsion.norm_exp_piI ι _ p hp.pos (-2 * m) (by push_cast; linear_combination -2 * hm),
      mul_one]
    exact hΨ b hb
  have hr' : ∀ x, ‖r' x‖ ≤ 1 := by
    rintro ⟨k, a, haS⟩
    obtain ⟨l, hl, hal⟩ := hSa' a haS
    have h3 : ‖ι (alphaQ (Real.sqrt dK / 2) (matH h) a)‖ = 1 := by
      have e : alphaQ (Real.sqrt dK / 2) (matH h) a = alphaQ (Real.sqrt dK / 2) (matH h) l := by
        unfold alphaQ qOf; rw [hal, XiTorsion.herm_smul _ _ hs1]
      obtain ⟨m, hm⟩ := XiTorsion.q_int (matH h) hH hsd dK hl (hΛq _ ⟨0, 1, by simp⟩ l hl)
      rw [e]; unfold alphaQ; rw [hm]
      exact XiTorsion.norm_exp_piI ι _ 1 one_pos m (by simp)
    have h4 : ‖ι (Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE (matH h) (t k) a : ℂ)))‖ = 1 := by
      obtain ⟨m, hm⟩ := XiTorsion.altE_int hsd (ht k) (hpa a haS)
      rw [XiTorsion.altE_smul_left, XiTorsion.altE_smul_right] at hm
      have e2 : Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE (matH h) (t k) a : ℂ)) =
          Complex.exp ((Real.pi : ℂ) * Complex.I * ((-altE (matH h) (t k) a : ℝ) : ℂ)) := by
        congr 1; push_cast; ring
      rw [e2]
      exact XiTorsion.norm_exp_piI ι _ (N * p) (Nat.mul_pos hN hp.pos) (-m)
        (by push_cast; linear_combination -hm)
    have e : r' (k, ⟨a, haS⟩) = ι (r k) * ι ((p : ℂ) ^ Fintype.card n * xiHat (matH h) (p ^ Fintype.card n) Ψ Sb a) *
        ι (alphaQ (Real.sqrt dK / 2) (matH h) a) *
        ι (Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE (matH h) (t k) a : ℂ))) := by
      simp only [r', cc, map_mul, map_pow, map_natCast]; ring
    rw [e, norm_mul, norm_mul, norm_mul, h3, h4, mul_one, mul_one]
    exact mul_le_one₀ (hr k) (norm_nonneg _) (hxh a haS)
  have hαq : IsQInt dK ((N : ℂ) * π) := by
    obtain ⟨m, k, hm⟩ := hπq
    exact ⟨N * m, N * k, by rw [hm]; push_cast; ring⟩
  have hαn : ‖ι ((N : ℂ) * π)‖ = 1 := by
    rw [map_mul, map_natCast, norm_mul, LocalJetRescaling.norm_natCast p hpN, one_mul]
    exact XiTorsion.norm_pi_one dK hp2 hpd ι π hπq hpp hlt
  have hαt : ∀ x, ((N : ℂ) * π) • t' x ∈ Λ := by
    rintro ⟨k, a, haS⟩
    show ((N : ℂ) * π) • (t k + a) ∈ Λ
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact hΛq π hπq _ (ht k)
    · rw [mul_smul]; exact hΛq _ (hnat N) _ (hπa a haS)
  have hMt : ∀ x, ((N * p : ℕ) : ℂ) • t' x ∈ Λ := by
    rintro ⟨k, a, haS⟩
    show ((N * p : ℕ) : ℂ) • (t k + a) ∈ Λ
    rw [smul_add, Nat.cast_mul]
    refine Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact hΛq _ (hnat p) _ (ht k)
    · rw [mul_smul]; exact hΛq _ (hnat N) _ (hpa a haS)
  have hA' : ∀ j x, ‖A j x‖ ≤ ‖((N * p : ℕ) : ℂ_[p])‖ := by
    intro j x
    rw [Nat.cast_mul, norm_mul, LocalJetRescaling.norm_natCast p hpN, one_mul]
    exact hA j x
  exact (hE a₀ b₀ c₀ dK ha hdK lam hlam hOK n h Λ hsd hSt θ hθ p hp2 hpd ι hInt hLoc (κx × Sa) r' t'
    ((N : ℂ) * π) (N * p) hr' hαq hαn (Nat.mul_pos hN hp.pos) hαt hMt J v hv ν A hA').1

end Formalism.L2.AlgTh
