import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData
import Formalism.LocalToGlobal.KernelLattices.ColumnData.HfTrace
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralClosureCriterion

noncomputable section

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.AR

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Formalism.FrobeniusOrbits
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

variable (D : Car)

abbrev bb : D.host.E := D.host.sqd

abbrev be : ℂ := Complex.I * (Real.sqrt D.host.d : ℂ)

def OKc (z : ℂ) : Prop :=
  ∃ x y : ℤ, Even (x - y) ∧ z = ((x : ℂ) + (y : ℂ) * be D) / 2

/- English proof (translation)
Conclude with `D.host.hyp.2.1.pos` after adjusting the coercions.
-/
theorem d_pos : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos

/- English proof (translation)
The claim follows from `Real.sqrt_pos.2 (d_pos D)`.
-/
theorem sqrt_pos : 0 < Real.sqrt D.host.d := Real.sqrt_pos.2 (d_pos D)

/- English proof (translation)
Rewrite using `[← Complex.ofReal_pow, Real.sq_sqrt (d_pos D).le]`. Simplify using the standard rewrite rules.
-/
theorem sq_sqrtC : ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 = (D.host.d : ℂ) := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (d_pos D).le]; simp

/- English proof (translation)
Rewrite using `[be, mul_pow, Complex.I_sq, sq_sqrtC]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem be_sq : be D ^ 2 = -(D.host.d : ℂ) := by
  rw [be, mul_pow, Complex.I_sq, sq_sqrtC]; ring

/- English proof (translation)
Simplify using `[be, Complex.conj_ofReal]`.
-/
theorem conj_be : starRingEnd ℂ (be D) = -be D := by
  simp [be, Complex.conj_ofReal]

/- English proof (translation)
Assemble the required witnesses or components as `⟨(D.host.d : ℤ) / 4, by have := D.host.hyp.2.2.2.1; omega⟩`.
-/
theorem d_mod : ∃ k : ℤ, (D.host.d : ℤ) = 4 * k + 3 :=
  ⟨(D.host.d : ℤ) / 4, by have := D.host.hyp.2.2.2.1; omega⟩

/- English proof (translation)
The claim follows from `D.host.φ₀_mem`.
-/
theorem phi_b : D.host.φ₀ (bb D) = be D := D.host.φ₀_mem

/- English proof (translation)
Apply `D.host.φ₀.injective` to reduce the goal to its premises. Rewrite using `[map_pow, phi_b, be_sq, map_neg, map_natCast]`.
-/
theorem b_sq : bb D ^ 2 = -(D.host.d : D.host.E) := by
  apply D.host.φ₀.injective
  rw [map_pow, phi_b, be_sq, map_neg, map_natCast]

/- English proof (translation)
The claim follows from `FL.bE_mem D`.
-/
theorem bK_mem : bb D ∈ D.host.K := FL.bE_mem D

def bK : D.host.K := ⟨bb D, bK_mem D⟩

/- English proof (translation)
Rewrite using `[Rat.smul_def, map_mul, map_ratCast]`.
-/
theorem phi_smul (s : ℚ) (x : D.host.E) : D.host.φ₀ (s • x) = (s : ℂ) * D.host.φ₀ x := by
  rw [Rat.smul_def, map_mul, map_ratCast]

/- English proof (translation)
Establish `hK : Module.finrank ℚ D.host.K = 2` using `Formalism.FrobeniusOrbits.SplitK.finrank_K (L := D.host.E) (b := bb D) D.host.hyp.2.1.pos (b_sq D)`. Establish `hli : LinearIndependent ℚ ![(1 : D.host.K), bK D]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`. Establish `h1` using `congrArg (fun x : D.host.K => D.host.φ₀ (x : D.host.E)) hst`.

Simplify using `only [IntermediateField.coe_add, IntermediateField.coe_smul, IntermediateField.coe_one, IntermediateField.coe_zero, map_add, phi_smul, map_one, map_zero, bK, phi_b, mul_one] at h1`. Establish `hre` using `congrArg Complex.re h1`. Establish `him` using `congrArg Complex.im h1`. Simplify using `[be] at hre him`. Establish `hs` using `sqrt_pos D`.

Break down `him with h | h` into its components or cases. Conclude with `⟨by simpa [h] using hre, h⟩`. Conclude with `absurd h D.host.hyp.2.1.ne_zero`. Establish `hsp` using `hli.span_eq_top_of_card_eq_finrank (by simp [hK])`. Establish `hu : u ∈ Submodule.span ℚ (Set.range ![(1 : D.host.K), bK D])` using `by rw [hsp]; trivial`.

Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun ℚ).1 hu`. Use `⟨c 0, c 1, ?_⟩` and prove the remaining obligations. Rewrite using `[← hc, Fin.sum_univ_two]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, IntermediateField.coe_add, IntermediateField.coe_smul, IntermediateField.coe_one, map_add, phi_smul, map_one, mul_one, bK, phi_b]`.
-/
theorem K_repr (u : D.host.K) :
    ∃ p q : ℚ, D.host.φ₀ (u : D.host.E) = (p : ℂ) + (q : ℂ) * be D := by
  have hK : Module.finrank ℚ D.host.K = 2 :=
    Formalism.FrobeniusOrbits.SplitK.finrank_K (L := D.host.E) (b := bb D) D.host.hyp.2.1.pos (b_sq D)
  have hli : LinearIndependent ℚ ![(1 : D.host.K), bK D] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (fun x : D.host.K => D.host.φ₀ (x : D.host.E)) hst
    simp only [IntermediateField.coe_add, IntermediateField.coe_smul, IntermediateField.coe_one,
      IntermediateField.coe_zero, map_add, phi_smul, map_one, map_zero, bK, phi_b, mul_one] at h1
    have hre := congrArg Complex.re h1
    have him := congrArg Complex.im h1
    simp [be] at hre him
    have hs := sqrt_pos D
    rcases him with h | h
    · exact ⟨by simpa [h] using hre, h⟩
    · exact absurd h D.host.hyp.2.1.ne_zero
  have hsp := hli.span_eq_top_of_card_eq_finrank (by simp [hK])
  have hu : u ∈ Submodule.span ℚ (Set.range ![(1 : D.host.K), bK D]) := by rw [hsp]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).1 hu
  refine ⟨c 0, c 1, ?_⟩
  rw [← hc, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    IntermediateField.coe_add, IntermediateField.coe_smul, IntermediateField.coe_one, map_add,
    phi_smul, map_one, mul_one, bK, phi_b]

/- English proof (translation)
Establish `h' : IsIntegral ℤ r`. Use `(isIntegral_algHom_iff (algebraMap ℚ ℂ).toIntAlgHom (algebraMap ℚ ℂ).injective).mp ?_` and prove the remaining obligations. Simplify using `using h`. Take `⟨n, hn⟩` from `IsIntegrallyClosed.isIntegral_iff.mp h'`. Conclude with `⟨n, by rw [← hn]; simp⟩`.
-/
theorem int_of_rat (r : ℚ) (h : IsIntegral ℤ (r : ℂ)) : ∃ n : ℤ, r = n := by
  have h' : IsIntegral ℤ r := by
    refine (isIntegral_algHom_iff (algebraMap ℚ ℂ).toIntAlgHom (algebraMap ℚ ℂ).injective).mp ?_
    simpa using h
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h'
  exact ⟨n, by rw [← hn]; simp⟩

abbrev psi : D.host.K →+* ℂ := D.host.φ₀.comp (algebraMap D.host.K D.host.E)

/- English proof (translation)
Apply the tactic sequence `apply _root_.UpperTheory.Reformulated.B.IntegralClosureCriterion.okc_of <;> assumption`.
-/
theorem okc_of (u : 𝓞 D.host.K) : OKc D (D.host.φ₀ ((u : D.host.K) : D.host.E)) :=
  by apply _root_.UpperTheory.Reformulated.B.IntegralClosureCriterion.okc_of <;> assumption

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.AR

end

noncomputable section

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.AR

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

def Bf (w₁ w₂ : ℂ) : ℝ := (starRingEnd ℂ w₁ * w₂).im

/- English proof (translation)
Simplify using `only [Bf, Complex.mul_im, Complex.conj_re, Complex.conj_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Bf_swap (w₁ w₂ : ℂ) : Bf w₂ w₁ = -Bf w₁ w₂ := by
  simp only [Bf, Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring

/- English proof (translation)
Simplify using `only [Bf, zsmul_eq_mul, map_sub, map_mul, map_intCast, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re, Complex.conj_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Bf_sub_zsmul_left (u w w₂ : ℂ) (q : ℤ) : Bf (u - q • w) w₂ = Bf u w₂ - q * Bf w w₂ := by
  simp only [Bf, zsmul_eq_mul, map_sub, map_mul, map_intCast, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re,
    Complex.conj_im]; ring

/- English proof (translation)
Simplify using `only [Bf, zsmul_eq_mul, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re, Complex.conj_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Bf_sub_zsmul_right (w₁ u w : ℂ) (q : ℤ) : Bf w₁ (u - q • w) = Bf w₁ u - q * Bf w₁ w := by
  simp only [Bf, zsmul_eq_mul, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re,
    Complex.conj_im]; ring

/- English proof (translation)
Apply the tactic sequence `apply Complex.ext <;>`. Apply the tactic sequence `simp only [Bf, Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im] <;> ring`.
-/
theorem cramer (w₁ w₂ u : ℂ) :
    (Bf u w₂ : ℂ) * w₁ + (Bf w₁ u : ℂ) * w₂ = (Bf w₁ w₂ : ℂ) * u := by
  apply Complex.ext <;>
    simp only [Bf, Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im] <;> ring

/- English proof (translation)
Simplify using `only [Bf, map_add, map_mul, Complex.conj_ofReal, Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Bf_comb (w₁ w₂ : ℂ) (s t s' t' : ℝ) :
    Bf ((s : ℂ) * w₁ + (t : ℂ) * w₂) ((s' : ℂ) * w₁ + (t' : ℂ) * w₂) = (s * t' - t * s') * Bf w₁ w₂ := by
  simp only [Bf, map_add, map_mul, Complex.conj_ofReal, Complex.mul_im, Complex.mul_re,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
    Complex.conj_im]; ring

/- English proof (translation)
Rewrite using `[← Int.cast_natCast, Int.toNat_of_nonneg h]`.
-/
theorem cast_toNat (n : ℤ) (h : 0 ≤ n) : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h]

/- English proof (translation)
Establish `hQ : ∃ n : ℕ, 0 < n ∧ ∃ w₁ ∈ Λ, ∃ w₂ ∈ Λ, Bf w₁ w₂ = κ * n`. Take `⟨w₁, h₁, w₂, h₂, h0⟩` from `hne`. Take `⟨n, hn⟩` from `hdisc w₁ h₁ w₂ h₂`. Break down `lt_trichotomy n 0 with hn0 | hn0 | hn0` into its components or cases. Use `⟨(-n).toNat, by omega, w₂, h₂, w₁, h₁, ?_⟩` and prove the remaining obligations.

Rewrite using `[Bf_swap, hn, cast_toNat _ (by omega)]; push_cast; ring`. Conclude with `absurd (by rw [hn, hn0]; simp) h0`. Use `⟨n.toNat, by omega, w₁, h₁, w₂, h₂, ?_⟩` and prove the remaining obligations. Rewrite using `[hn, cast_toNat _ hn0.le]`. Use `set m := Nat.find hQ with hm`.

Take `⟨hm0, w₁, h₁, w₂, h₂, hw⟩` from `Nat.find_spec hQ`. Establish `hmin : ∀ n : ℕ, 0 < n → ∀ u ∈ Λ, ∀ v ∈ Λ, Bf u v = κ * n → m ≤ n` using `fun n hn u hu v hv h => Nat.find_min' hQ ⟨hn, u, hu, v, hv, h⟩`. Establish `harea : area Λ = κ * m`. Unfold `area`. Use `IsLeast.csInf_eq ⟨⟨by positivity, w₁, h₁, w₂, h₂, ?_⟩, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `κ * m = |Bf w₁ w₂|`. Rewrite using `[hw, abs_of_nonneg (by positivity)]`. Introduce and unpack `a ⟨ha, u, hu, v, hv, rfl⟩`. Express the relevant statement in the definitionally equal form `κ * m ≤ |Bf u v|`. Take `⟨n, hn⟩` from `hdisc u hu v hv`.

Break down `lt_trichotomy n 0 with hn0 | hn0 | hn0` into its components or cases. Use `hmin (-n).toNat (by omega) v hv u hu (by` as an intermediate fact. Rewrite using `[Bf_swap, hn, cast_toNat _ (by omega)]; push_cast; ring)`. Rewrite using `[hn, abs_mul, abs_of_pos hκ, abs_of_neg (by exact_mod_cast hn0 : (n : ℝ) < 0)]`. Establish `h' : ((m : ℤ) : ℝ) ≤ ((-n : ℤ) : ℝ)` using `by exact_mod_cast (by omega : (m : ℤ) ≤ -n)`.

Move the coercions through the operations in `at h'`. Conclude with `mul_le_mul_of_nonneg_left h' hκ.le`. It suffices to derive a contradiction. Express the relevant statement in the definitionally equal form `0 < |Bf u v| at ha`. Rewrite `ha` using `[hn, hn0]`.

Simplify using `at ha`. Use `hmin n.toNat (by omega) u hu v hv (by rw [hn, cast_toNat _ hn0.le])` as an intermediate fact. Rewrite using `[hn, abs_mul, abs_of_pos hκ, abs_of_pos (by exact_mod_cast hn0 : (0 : ℝ) < n)]`. Establish `h' : ((m : ℤ) : ℝ) ≤ ((n : ℤ) : ℝ)` using `by exact_mod_cast (by omega : (m : ℤ) ≤ n)`. Move the coercions through the operations in `at h'`.

Conclude with `mul_le_mul_of_nonneg_left h' hκ.le`. Use `⟨m, hm0, harea, ?_⟩` and prove the remaining obligations. Use `set g := κ * m with hg`. Establish `hg0 : 0 < g` using `by positivity`. Establish `hleft : ∀ u ∈ Λ, ∃ q : ℤ, Bf u w₂ = g * q`.

Introduce `u hu`. Take `⟨n, hn⟩` from `hdisc u hu w₂ h₂`. Use `⟨n / m, ?_⟩` and prove the remaining obligations. Establish `hr : Bf (u - (n / m) • w₁) w₂ = κ * ((n % m : ℤ) : ℝ)`. Rewrite using `[Bf_sub_zsmul_left, hn, hw]`.

Use `Int.mul_ediv_add_emod n m` as an intermediate fact. Establish `: (n : ℝ) = ((n % m : ℤ) : ℝ) + m * ((n / m : ℤ) : ℝ)`. Establish `h2 : (n : ℝ) = ((m : ℤ) : ℝ) * ((n / m : ℤ) : ℝ) + ((n % m : ℤ) : ℝ)` using `by exact_mod_cast this.symm`. Rewrite using `[h2]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Establish `hr0 : n % (m : ℤ) = 0`. Assume the negation of the conclusion as `hne0`.

Establish `hpos : 0 < n % (m : ℤ)` using `lt_of_le_of_ne (Int.emod_nonneg _ (by omega)) (Ne.symm hne0)`. Establish `hlt : n % (m : ℤ) < m` using `Int.emod_lt_of_pos _ (by omega)`. Use `hmin (n % (m : ℤ)).toNat (by omega) _ (Λ.sub_mem hu (Λ.zsmul_mem h₁ _)) w₂ h₂ (by rw [hr, cast_toNat _ hpos.le])` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `Int.mul_ediv_add_emod n m` as an intermediate fact.

Rewrite `this` using `[hr0, add_zero]`. Establish `h3 : (n : ℝ) = (m : ℝ) * ((n / m : ℤ) : ℝ)` using `by exact_mod_cast this.symm`. Rewrite using `[hn, hg, h3]`. Expand and normalize the polynomial expressions, which then agree. Establish `hright : ∀ u ∈ Λ, ∃ q : ℤ, Bf w₁ u = g * q`.

Introduce `u hu`. Take `⟨n, hn⟩` from `hdisc w₁ h₁ u hu`. Use `⟨n / m, ?_⟩` and prove the remaining obligations. Establish `hr : Bf w₁ (u - (n / m) • w₂) = κ * ((n % m : ℤ) : ℝ)`. Rewrite using `[Bf_sub_zsmul_right, hn, hw]`.

Use `Int.mul_ediv_add_emod n m` as an intermediate fact. Establish `: (n : ℝ) = ((n % m : ℤ) : ℝ) + m * ((n / m : ℤ) : ℝ)`. Establish `h2 : (n : ℝ) = ((m : ℤ) : ℝ) * ((n / m : ℤ) : ℝ) + ((n % m : ℤ) : ℝ)` using `by exact_mod_cast this.symm`. Rewrite using `[h2]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Establish `hr0 : n % (m : ℤ) = 0`. Assume the negation of the conclusion as `hne0`.

Establish `hpos : 0 < n % (m : ℤ)` using `lt_of_le_of_ne (Int.emod_nonneg _ (by omega)) (Ne.symm hne0)`. Establish `hlt : n % (m : ℤ) < m` using `Int.emod_lt_of_pos _ (by omega)`. Use `hmin (n % (m : ℤ)).toNat (by omega) w₁ h₁ _ (Λ.sub_mem hu (Λ.zsmul_mem h₂ _)) (by rw [hr, cast_toNat _ hpos.le])` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `Int.mul_ediv_add_emod n m` as an intermediate fact.

Rewrite `this` using `[hr0, add_zero]`. Establish `h3 : (n : ℝ) = (m : ℝ) * ((n / m : ℤ) : ℝ)` using `by exact_mod_cast this.symm`. Rewrite using `[hn, hg, h3]`. Expand and normalize the polynomial expressions, which then agree. Establish `hdec : ∀ u ∈ Λ, ∃ s t : ℤ, u = ((s : ℝ) : ℂ) * w₁ + ((t : ℝ) : ℂ) * w₂`.

Introduce `u hu`. Take `⟨s, hs⟩` from `hleft u hu`. Take `⟨t, ht⟩` from `hright u hu`. Use `⟨s, t, ?_⟩` and prove the remaining obligations. Establish `hc` using `cramer w₁ w₂ u`.

Rewrite `hc` using `[hs, ht, hw]`. Establish `hg0' : (g : ℂ) ≠ 0` using `by exact_mod_cast hg0.ne'`. Apply `mul_left_cancel₀ hg0'` to reduce the goal to its premises. Rewrite using `[← hc]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Introduce `u hu v hv`. Take `⟨s, t, rfl⟩` from `hdec u hu`. Take `⟨s', t', rfl⟩` from `hdec v hv`. Use `⟨s * t' - t * s', ?_⟩` and prove the remaining obligations.

Rewrite using `[Bf_comb, hw, harea]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem area_spec (Λ : AddSubgroup ℂ) (κ : ℝ) (hκ : 0 < κ)
    (hdisc : ∀ w₁ ∈ Λ, ∀ w₂ ∈ Λ, ∃ n : ℤ, Bf w₁ w₂ = κ * n)
    (hne : ∃ w₁ ∈ Λ, ∃ w₂ ∈ Λ, Bf w₁ w₂ ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ area Λ = κ * m ∧ ∀ w₁ ∈ Λ, ∀ w₂ ∈ Λ, ∃ n : ℤ, Bf w₁ w₂ = area Λ * n := by
  classical

  have hQ : ∃ n : ℕ, 0 < n ∧ ∃ w₁ ∈ Λ, ∃ w₂ ∈ Λ, Bf w₁ w₂ = κ * n := by
    obtain ⟨w₁, h₁, w₂, h₂, h0⟩ := hne
    obtain ⟨n, hn⟩ := hdisc w₁ h₁ w₂ h₂
    rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
    · refine ⟨(-n).toNat, by omega, w₂, h₂, w₁, h₁, ?_⟩
      rw [Bf_swap, hn, cast_toNat _ (by omega)]; push_cast; ring
    · exact absurd (by rw [hn, hn0]; simp) h0
    · refine ⟨n.toNat, by omega, w₁, h₁, w₂, h₂, ?_⟩
      rw [hn, cast_toNat _ hn0.le]
  set m := Nat.find hQ with hm
  obtain ⟨hm0, w₁, h₁, w₂, h₂, hw⟩ := Nat.find_spec hQ
  have hmin : ∀ n : ℕ, 0 < n → ∀ u ∈ Λ, ∀ v ∈ Λ, Bf u v = κ * n → m ≤ n :=
    fun n hn u hu v hv h => Nat.find_min' hQ ⟨hn, u, hu, v, hv, h⟩

  have harea : area Λ = κ * m := by
    unfold area
    refine IsLeast.csInf_eq ⟨⟨by positivity, w₁, h₁, w₂, h₂, ?_⟩, ?_⟩
    · change κ * m = |Bf w₁ w₂|
      rw [hw, abs_of_nonneg (by positivity)]
    · rintro a ⟨ha, u, hu, v, hv, rfl⟩
      change κ * m ≤ |Bf u v|
      obtain ⟨n, hn⟩ := hdisc u hu v hv
      rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
      · have := hmin (-n).toNat (by omega) v hv u hu (by
          rw [Bf_swap, hn, cast_toNat _ (by omega)]; push_cast; ring)
        rw [hn, abs_mul, abs_of_pos hκ, abs_of_neg (by exact_mod_cast hn0 : (n : ℝ) < 0)]
        have h' : ((m : ℤ) : ℝ) ≤ ((-n : ℤ) : ℝ) := by exact_mod_cast (by omega : (m : ℤ) ≤ -n)
        push_cast at h'
        exact mul_le_mul_of_nonneg_left h' hκ.le
      · exfalso; change 0 < |Bf u v| at ha; rw [hn, hn0] at ha; simp at ha
      · have := hmin n.toNat (by omega) u hu v hv (by rw [hn, cast_toNat _ hn0.le])
        rw [hn, abs_mul, abs_of_pos hκ, abs_of_pos (by exact_mod_cast hn0 : (0 : ℝ) < n)]
        have h' : ((m : ℤ) : ℝ) ≤ ((n : ℤ) : ℝ) := by exact_mod_cast (by omega : (m : ℤ) ≤ n)
        push_cast at h'
        exact mul_le_mul_of_nonneg_left h' hκ.le
  refine ⟨m, hm0, harea, ?_⟩
  set g := κ * m with hg
  have hg0 : 0 < g := by positivity

  have hleft : ∀ u ∈ Λ, ∃ q : ℤ, Bf u w₂ = g * q := by
    intro u hu
    obtain ⟨n, hn⟩ := hdisc u hu w₂ h₂
    refine ⟨n / m, ?_⟩
    have hr : Bf (u - (n / m) • w₁) w₂ = κ * ((n % m : ℤ) : ℝ) := by
      rw [Bf_sub_zsmul_left, hn, hw]
      have := Int.mul_ediv_add_emod n m
      have : (n : ℝ) = ((n % m : ℤ) : ℝ) + m * ((n / m : ℤ) : ℝ) := by
        have h2 : (n : ℝ) = ((m : ℤ) : ℝ) * ((n / m : ℤ) : ℝ) + ((n % m : ℤ) : ℝ) := by exact_mod_cast this.symm
        rw [h2]; push_cast; ring
      rw [this]; ring
    have hr0 : n % (m : ℤ) = 0 := by
      by_contra hne0
      have hpos : 0 < n % (m : ℤ) := lt_of_le_of_ne (Int.emod_nonneg _ (by omega)) (Ne.symm hne0)
      have hlt : n % (m : ℤ) < m := Int.emod_lt_of_pos _ (by omega)
      have := hmin (n % (m : ℤ)).toNat (by omega) _ (Λ.sub_mem hu (Λ.zsmul_mem h₁ _)) w₂ h₂
        (by rw [hr, cast_toNat _ hpos.le])
      omega
    have := Int.mul_ediv_add_emod n m
    rw [hr0, add_zero] at this
    have h3 : (n : ℝ) = (m : ℝ) * ((n / m : ℤ) : ℝ) := by exact_mod_cast this.symm
    rw [hn, hg, h3]; ring
  have hright : ∀ u ∈ Λ, ∃ q : ℤ, Bf w₁ u = g * q := by
    intro u hu
    obtain ⟨n, hn⟩ := hdisc w₁ h₁ u hu
    refine ⟨n / m, ?_⟩
    have hr : Bf w₁ (u - (n / m) • w₂) = κ * ((n % m : ℤ) : ℝ) := by
      rw [Bf_sub_zsmul_right, hn, hw]
      have := Int.mul_ediv_add_emod n m
      have : (n : ℝ) = ((n % m : ℤ) : ℝ) + m * ((n / m : ℤ) : ℝ) := by
        have h2 : (n : ℝ) = ((m : ℤ) : ℝ) * ((n / m : ℤ) : ℝ) + ((n % m : ℤ) : ℝ) := by exact_mod_cast this.symm
        rw [h2]; push_cast; ring
      rw [this]; ring
    have hr0 : n % (m : ℤ) = 0 := by
      by_contra hne0
      have hpos : 0 < n % (m : ℤ) := lt_of_le_of_ne (Int.emod_nonneg _ (by omega)) (Ne.symm hne0)
      have hlt : n % (m : ℤ) < m := Int.emod_lt_of_pos _ (by omega)
      have := hmin (n % (m : ℤ)).toNat (by omega) w₁ h₁ _ (Λ.sub_mem hu (Λ.zsmul_mem h₂ _))
        (by rw [hr, cast_toNat _ hpos.le])
      omega
    have := Int.mul_ediv_add_emod n m
    rw [hr0, add_zero] at this
    have h3 : (n : ℝ) = (m : ℝ) * ((n / m : ℤ) : ℝ) := by exact_mod_cast this.symm
    rw [hn, hg, h3]; ring

  have hdec : ∀ u ∈ Λ, ∃ s t : ℤ, u = ((s : ℝ) : ℂ) * w₁ + ((t : ℝ) : ℂ) * w₂ := by
    intro u hu
    obtain ⟨s, hs⟩ := hleft u hu
    obtain ⟨t, ht⟩ := hright u hu
    refine ⟨s, t, ?_⟩
    have hc := cramer w₁ w₂ u
    rw [hs, ht, hw] at hc
    have hg0' : (g : ℂ) ≠ 0 := by exact_mod_cast hg0.ne'
    apply mul_left_cancel₀ hg0'
    rw [← hc]; push_cast; ring
  intro u hu v hv
  obtain ⟨s, t, rfl⟩ := hdec u hu
  obtain ⟨s', t', rfl⟩ := hdec v hv
  refine ⟨s * t' - t * s', ?_⟩
  rw [Bf_comb, hw, harea]; push_cast; ring

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.AR

end

noncomputable section

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.AR

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

variable (D : Car)

abbrev ph (c : 𝓞 D.host.K) : ℂ := D.host.φ₀ (((c : D.host.K) : D.host.E))

/- English proof (translation)
Take `⟨x, y, ⟨a, ha⟩, rfl⟩` from `hz`. Take `⟨x', y', ⟨a', ha'⟩, rfl⟩` from `hw`. Take `⟨k, hk⟩` from `d_mod D`. Take `rfl : x = y + a + a` from `by omega`. Take `rfl : x' = y' + a' + a'` from `by omega`.

Use `⟨-(2 * k + 1) * y * y' + a * y' + a' * y + 2 * a * a', y * y' + a * y' + a' * y, ⟨-(k + 1) * y * y' + a * a', by ring⟩, ?_⟩` and prove the remaining obligations. Establish `hkC : (D.host.d : ℂ) = 4 * k + 3` using `by exact_mod_cast hk`. Establish `hsq` using `be_sq D`. Use `push_cast`. Take the linear combination `hsq * ((y : ℂ) * y' / 4) - hkC * ((y : ℂ) * y' / 4)`.
-/
theorem okc_mul {z w : ℂ} (hz : OKc D z) (hw : OKc D w) : OKc D (z * w) := by
  obtain ⟨x, y, ⟨a, ha⟩, rfl⟩ := hz
  obtain ⟨x', y', ⟨a', ha'⟩, rfl⟩ := hw
  obtain ⟨k, hk⟩ := d_mod D
  obtain rfl : x = y + a + a := by omega
  obtain rfl : x' = y' + a' + a' := by omega
  refine ⟨-(2 * k + 1) * y * y' + a * y' + a' * y + 2 * a * a', y * y' + a * y' + a' * y,
    ⟨-(k + 1) * y * y' + a * a', by ring⟩, ?_⟩
  have hkC : (D.host.d : ℂ) = 4 * k + 3 := by exact_mod_cast hk
  have hsq := be_sq D
  push_cast
  linear_combination hsq * ((y : ℂ) * y' / 4) - hkC * ((y : ℂ) * y' / 4)

/- English proof (translation)
Take `⟨x, y, ⟨a, ha⟩, rfl⟩` from `hz`. Use `⟨x, -y, ⟨a + y, by omega⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_div₀, map_add, map_mul, conj_be, map_intCast, map_intCast, map_ofNat]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem okc_conj {z : ℂ} (hz : OKc D z) : OKc D (starRingEnd ℂ z) := by
  obtain ⟨x, y, ⟨a, ha⟩, rfl⟩ := hz
  refine ⟨x, -y, ⟨a + y, by omega⟩, ?_⟩
  rw [map_div₀, map_add, map_mul, conj_be, map_intCast, map_intCast, map_ofNat]; push_cast; ring

/- English proof (translation)
Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coord_eq (x y : ℤ) :
    ((x : ℂ) + (y : ℂ) * be D) / 2 =
      (((x : ℝ) / 2 : ℝ) : ℂ) + (((y : ℝ) * Real.sqrt D.host.d / 2 : ℝ) : ℂ) * Complex.I := by
  push_cast; ring

/- English proof (translation)
Rewrite using `[coord_eq]`. Simplify using the standard rewrite rules.
-/
theorem im_coord (x y : ℤ) :
    (((x : ℂ) + (y : ℂ) * be D) / 2).im = (y : ℝ) * Real.sqrt D.host.d / 2 := by
  rw [coord_eq]; simp

/- English proof (translation)
Take `⟨x, y, hxy, rfl⟩` from `hu`. Use `⟨x, y, hxy, ?_⟩` and prove the remaining obligations. Establish `hs : (Real.sqrt D.host.d : ℂ) ≠ 0` using `by exact_mod_cast (sqrt_pos D).ne'`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem good_of_okc {u : ℂ} (hu : OKc D u) : Good D (2 * u / (Real.sqrt D.host.d : ℂ)) := by
  obtain ⟨x, y, hxy, rfl⟩ := hu
  refine ⟨x, y, hxy, ?_⟩
  have hs : (Real.sqrt D.host.d : ℂ) ≠ 0 := by exact_mod_cast (sqrt_pos D).ne'
  push_cast
  field_simp

/- English proof (translation)
Use `⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (k + 1), by monicity!, ?_⟩` and prove the remaining obligations. Simplify using `only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]`. Use `push_cast`. Take the linear combination `hx / 4`.
-/
theorem half_int {F : Type*} [Field F] [CharZero F] (x : F) (k : ℤ)
    (hx : x ^ 2 = -(4 * (k : F) + 3)) : IsIntegral ℤ ((1 + x) / 2) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (k + 1), by monicity!, ?_⟩
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C]
  push_cast
  linear_combination hx / 4

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use `push_cast`. Conclude with `b_sq D`.
-/
theorem bK_sq : bK D ^ 2 = -(D.host.d : D.host.K) := by
  apply Subtype.ext
  push_cast
  exact b_sq D

def om : 𝓞 D.host.K :=
  ⟨(1 + bK D) / 2, half_int _ (d_mod D).choose (by
    have h2 : ((D.host.d : ℤ) : D.host.K) = ((4 * (d_mod D).choose + 3 : ℤ) : D.host.K) :=
      congrArg (fun t : ℤ => (t : D.host.K)) (d_mod D).choose_spec
    push_cast at h2
    rw [bK_sq D]; linear_combination -h2)⟩

/- English proof (translation)
Use `show D.host.φ₀ ((((1 + bK D) / 2 : D.host.K)) : D.host.E) = _`. Establish `h2 : ((2 : D.host.K) : D.host.E) = 2`. Rewrite using `[show (2 : D.host.K) = 1 + 1 by norm_num, IntermediateField.coe_add, IntermediateField.coe_one]`. Evaluate the numerical expressions. Use `push_cast`.

Rewrite using `[h2, map_div₀, map_add, map_one, map_ofNat]`. Conclude with `congrArg (fun t => (1 + t) / 2) (phi_b D)`.
-/
theorem ph_om : ph D (om D) = (1 + be D) / 2 := by
  show D.host.φ₀ ((((1 + bK D) / 2 : D.host.K)) : D.host.E) = _
  have h2 : ((2 : D.host.K) : D.host.E) = 2 := by
    rw [show (2 : D.host.K) = 1 + 1 by norm_num, IntermediateField.coe_add, IntermediateField.coe_one]
    norm_num
  push_cast
  rw [h2, map_div₀, map_add, map_one, map_ofNat]
  exact congrArg (fun t => (1 + t) / 2) (phi_b D)

/- English proof (translation)
Establish `: starRingEnd ℂ (δ * ph D c₁) * (δ * ph D c₂) = (Complex.normSq δ : ℂ) * (starRingEnd ℂ (ph D c₁) * ph D c₂)`. Rewrite using `[Complex.normSq_eq_conj_mul_self, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Bf, this]`. Simplify using `[Complex.mul_im]`.
-/
theorem Bf_lat (δ : ℂ) (c₁ c₂ : 𝓞 D.host.K) :
    Bf (δ * ph D c₁) (δ * ph D c₂) = Complex.normSq δ * (starRingEnd ℂ (ph D c₁) * ph D c₂).im := by
  have : starRingEnd ℂ (δ * ph D c₁) * (δ * ph D c₂) =
      (Complex.normSq δ : ℂ) * (starRingEnd ℂ (ph D c₁) * ph D c₂) := by
    rw [Complex.normSq_eq_conj_mul_self, map_mul]; ring
  rw [Bf, this]; simp [Complex.mul_im]

/- English proof (translation)
The claim follows from `okc_mul D (okc_conj D (okc_of D c₁)) (okc_of D c₂)`.
-/
theorem okc_pair (c₁ c₂ : 𝓞 D.host.K) : OKc D (starRingEnd ℂ (ph D c₁) * ph D c₂) :=
  okc_mul D (okc_conj D (okc_of D c₁)) (okc_of D c₂)

/- English proof (translation)
Establish `hn : 0 < Complex.normSq δ` using `Complex.normSq_pos.2 hδ`. Establish `hs` using `sqrt_pos D`. Establish `hκ : 0 < Complex.normSq δ * (Real.sqrt D.host.d / 2)` using `by positivity`. Establish `hdisc : ∀ w₁ ∈ lamOf D cc δ, ∀ w₂ ∈ lamOf D cc δ, ∃ n : ℤ, Bf w₁ w₂ = Complex.normSq δ * (Real.sqrt D.host.d / 2) * n`. Introduce `w₁ h₁ w₂ h₂`.

Take `⟨c₁, -, rfl⟩` from `FL.lam_mem D cc δ w₁ h₁`. Take `⟨c₂, -, rfl⟩` from `FL.lam_mem D cc δ w₂ h₂`. Take `⟨x, y, -, hz⟩` from `okc_pair D c₁ c₂`. Use `⟨y, ?_⟩` and prove the remaining obligations. Rewrite using `[Bf_lat, hz, im_coord]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hne : ∃ w₁ ∈ lamOf D cc δ, ∃ w₂ ∈ lamOf D cc δ, Bf w₁ w₂ ≠ 0`. Take `⟨c, hc, hc0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hcc`. Use `⟨δ * ph D c, AddSubgroup.subset_closure ⟨c, hc, rfl⟩, δ * ph D (c * om D), AddSubgroup.subset_closure ⟨c * om D, cc.mul_mem_right _ hc, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `hph : ph D (c * om D) = ph D c * ((1 + be D) / 2)`.

Rewrite using `[← ph_om]`. Simplify using `[ph]`. Establish `hc1 : ph D c ≠ 0`. Simplify using `only [ph, map_ne_zero_iff _ D.host.φ₀.injective]`. Conclude with `hc0` after adjusting the coercions.

Rewrite using `[Bf_lat, hph]`. Establish `e : starRingEnd ℂ (ph D c) * (ph D c * ((1 + be D) / 2)) = (Complex.normSq (ph D c) : ℂ) * ((1 + be D) / 2)`. Rewrite using `[Complex.normSq_eq_conj_mul_self]`. Expand and normalize the polynomial expressions, which then agree. Establish `e4 : (1 + be D) / 2 = (((1 : ℝ) / 2 : ℝ) : ℂ) + ((Real.sqrt D.host.d / 2 : ℝ) : ℂ) * Complex.I` using `by push_cast; ring`.

Establish `e5 : ((Complex.normSq (ph D c) : ℂ) * ((((1 : ℝ) / 2 : ℝ) : ℂ) + ((Real.sqrt D.host.d / 2 : ℝ) : ℂ) * Complex.I)).im = Complex.normSq (ph D c) * (Real.sqrt D.host.d / 2)` using `by simp [Complex.mul_im]`. Rewrite using `[e, e4, e5]`. Conclude with `mul_ne_zero hn.ne' (mul_ne_zero (Complex.normSq_pos.2 hc1).ne' (by positivity))`. Take `⟨m, hm, harea, hall⟩` from `area_spec (lamOf D cc δ) _ hκ hdisc hne`. Use `⟨m, hm, harea, fun c hc c' hc' => ?_⟩` and prove the remaining obligations.

Take `⟨x, y, -, hz⟩` from `okc_pair D c' c`. Take `⟨n₁, h₁⟩` from `hall _ (AddSubgroup.subset_closure ⟨c', hc', rfl⟩) _ (AddSubgroup.subset_closure ⟨c, hc, rfl⟩)`. Take `⟨n₂, h₂⟩` from `hall _ (AddSubgroup.subset_closure ⟨c', hc', rfl⟩) _ (AddSubgroup.subset_closure ⟨c * om D, cc.mul_mem_right _ hc, rfl⟩)`. Establish `hph : ph D (c * om D) = ph D c * ((1 + be D) / 2)`. Rewrite using `[← ph_om]`.

Simplify using `[ph]`. Rewrite `h₁` using `[Bf_lat, hz, im_coord, harea]`. Rewrite `h₂` using `[Bf_lat, hph, ← mul_assoc, hz, harea]`. Establish `e2 : ((x : ℂ) + (y : ℂ) * be D) / 2 * ((1 + be D) / 2) = ((((x - D.host.d * y : ℤ) : ℂ) + ((x + y : ℤ) : ℂ) * be D) / 2) / 2` using `by push_cast; linear_combination (y : ℂ) / 4 * be_sq D`. Rewrite `h₂` using `[e2, Complex.div_ofNat_im, im_coord]`.

Establish `hy : (y : ℝ) = m * n₁`. Establish `: Complex.normSq δ * (Real.sqrt D.host.d / 2) * (y - m * n₁) = 0` using `by linear_combination h₁`. Use `(mul_eq_zero.1 this).resolve_left hκ.ne'` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hxy : ((x + y : ℤ) : ℝ) = 2 * (m * n₂)`.

Establish `: Complex.normSq δ * (Real.sqrt D.host.d / 2) * (((x + y : ℤ) : ℝ) - 2 * (m * n₂)) = 0`. Take the linear combination `2 * h₂`. Use `(mul_eq_zero.1 this).resolve_left hκ.ne'` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hyZ : y = m * n₁` using `by exact_mod_cast hy`.

Establish `hxZ : x = 2 * m * n₂ - m * n₁`. Establish `: x + y = 2 * (m * n₂)` using `by exact_mod_cast hxy`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨2 * n₂ - n₁, n₁, ⟨n₂ - n₁, by ring⟩, ?_⟩` and prove the remaining obligations. Establish `hm0 : (m : ℂ) ≠ 0` using `by exact_mod_cast hm.ne'`.

Rewrite using `[hz, hxZ, hyZ]`. Clear the denominators using the available nonvanishing facts. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem div_okc (cc : Ideal (𝓞 D.host.K)) (hcc : cc ≠ ⊥) (δ : ℂ) (hδ : δ ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ area (lamOf D cc δ) = Complex.normSq δ * (Real.sqrt D.host.d / 2) * m ∧
      ∀ c ∈ cc, ∀ c' ∈ cc, OKc D (starRingEnd ℂ (ph D c') * ph D c / m) := by
  have hn : 0 < Complex.normSq δ := Complex.normSq_pos.2 hδ
  have hs := sqrt_pos D
  have hκ : 0 < Complex.normSq δ * (Real.sqrt D.host.d / 2) := by positivity
  have hdisc : ∀ w₁ ∈ lamOf D cc δ, ∀ w₂ ∈ lamOf D cc δ, ∃ n : ℤ,
      Bf w₁ w₂ = Complex.normSq δ * (Real.sqrt D.host.d / 2) * n := by
    intro w₁ h₁ w₂ h₂
    obtain ⟨c₁, -, rfl⟩ := FL.lam_mem D cc δ w₁ h₁
    obtain ⟨c₂, -, rfl⟩ := FL.lam_mem D cc δ w₂ h₂
    obtain ⟨x, y, -, hz⟩ := okc_pair D c₁ c₂
    refine ⟨y, ?_⟩
    rw [Bf_lat, hz, im_coord]; ring
  have hne : ∃ w₁ ∈ lamOf D cc δ, ∃ w₂ ∈ lamOf D cc δ, Bf w₁ w₂ ≠ 0 := by
    obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcc
    refine ⟨δ * ph D c, AddSubgroup.subset_closure ⟨c, hc, rfl⟩,
      δ * ph D (c * om D), AddSubgroup.subset_closure ⟨c * om D, cc.mul_mem_right _ hc, rfl⟩, ?_⟩
    have hph : ph D (c * om D) = ph D c * ((1 + be D) / 2) := by
      rw [← ph_om]; simp [ph]
    have hc1 : ph D c ≠ 0 := by
      simp only [ph, map_ne_zero_iff _ D.host.φ₀.injective]
      exact_mod_cast hc0
    rw [Bf_lat, hph]
    have e : starRingEnd ℂ (ph D c) * (ph D c * ((1 + be D) / 2)) =
        (Complex.normSq (ph D c) : ℂ) * ((1 + be D) / 2) := by
      rw [Complex.normSq_eq_conj_mul_self]; ring
    have e4 : (1 + be D) / 2 =
        (((1 : ℝ) / 2 : ℝ) : ℂ) + ((Real.sqrt D.host.d / 2 : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    have e5 : ((Complex.normSq (ph D c) : ℂ) * ((((1 : ℝ) / 2 : ℝ) : ℂ) +
        ((Real.sqrt D.host.d / 2 : ℝ) : ℂ) * Complex.I)).im =
        Complex.normSq (ph D c) * (Real.sqrt D.host.d / 2) := by simp [Complex.mul_im]
    rw [e, e4, e5]
    exact mul_ne_zero hn.ne' (mul_ne_zero (Complex.normSq_pos.2 hc1).ne' (by positivity))
  obtain ⟨m, hm, harea, hall⟩ := area_spec (lamOf D cc δ) _ hκ hdisc hne
  refine ⟨m, hm, harea, fun c hc c' hc' => ?_⟩
  obtain ⟨x, y, -, hz⟩ := okc_pair D c' c
  obtain ⟨n₁, h₁⟩ := hall _ (AddSubgroup.subset_closure ⟨c', hc', rfl⟩) _
    (AddSubgroup.subset_closure ⟨c, hc, rfl⟩)
  obtain ⟨n₂, h₂⟩ := hall _ (AddSubgroup.subset_closure ⟨c', hc', rfl⟩) _
    (AddSubgroup.subset_closure ⟨c * om D, cc.mul_mem_right _ hc, rfl⟩)
  have hph : ph D (c * om D) = ph D c * ((1 + be D) / 2) := by
    rw [← ph_om]; simp [ph]
  rw [Bf_lat, hz, im_coord, harea] at h₁
  rw [Bf_lat, hph, ← mul_assoc, hz, harea] at h₂
  have e2 : ((x : ℂ) + (y : ℂ) * be D) / 2 * ((1 + be D) / 2) =
      ((((x - D.host.d * y : ℤ) : ℂ) + ((x + y : ℤ) : ℂ) * be D) / 2) / 2 := by
    push_cast; linear_combination (y : ℂ) / 4 * be_sq D
  rw [e2, Complex.div_ofNat_im, im_coord] at h₂
  have hy : (y : ℝ) = m * n₁ := by
    have : Complex.normSq δ * (Real.sqrt D.host.d / 2) * (y - m * n₁) = 0 := by linear_combination h₁
    have := (mul_eq_zero.1 this).resolve_left hκ.ne'
    linarith
  have hxy : ((x + y : ℤ) : ℝ) = 2 * (m * n₂) := by
    have : Complex.normSq δ * (Real.sqrt D.host.d / 2) * (((x + y : ℤ) : ℝ) - 2 * (m * n₂)) = 0 := by
      linear_combination 2 * h₂
    have := (mul_eq_zero.1 this).resolve_left hκ.ne'
    linarith
  have hyZ : y = m * n₁ := by exact_mod_cast hy
  have hxZ : x = 2 * m * n₂ - m * n₁ := by
    have : x + y = 2 * (m * n₂) := by exact_mod_cast hxy
    linarith
  refine ⟨2 * n₂ - n₁, n₁, ⟨n₂ - n₁, by ring⟩, ?_⟩
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [hz, hxZ, hyZ]
  field_simp
  push_cast
  ring

def HYYIntRec : Prop :=
  ∀ D : Car, ∀ N N' (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' →
    ∀ A ∈ YYl D L L', ∀ B ∈ YYl D L L', IsIntegral ℤ (hYY D A B)

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.AR

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO Formalism.L2.Ker.Cd.IntegralLatticeDensity.AR
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

/- English proof (translation)
Introduce `D cc hcc δ hδ h0 N N' L L' hA c hc c' hc' A hA' B hB'`. Take `⟨m, hm, harea, hdiv⟩` from `div_okc D cc hcc.1 δ h0`. Establish `hh : OKc D (D.host.φ₀ ((hYY D A B : D.host.K) : D.host.E))` using `okc_of D ⟨hYY D A B, h D N N' L L' hA A hA' B hB'⟩`. Establish `hprod` using `okc_mul D (hdiv c hc c' hc') hh`. Establish `hg` using `good_of_okc D hprod`.

Use `hg using 1` and compare the differences between its conclusion and the goal. Establish `hnz : (Complex.normSq δ : ℂ) ≠ 0` using `by exact_mod_cast (Complex.normSq_pos.2 h0).ne'`. Establish `hs : (Real.sqrt D.host.d : ℂ) ≠ 0` using `by exact_mod_cast (sqrt_pos D).ne'`. Establish `hm0 : (m : ℂ) ≠ 0` using `by exact_mod_cast hm.ne'`. Establish `hcd : starRingEnd ℂ δ ≠ 0` using `by simpa using h0`.

Rewrite using `[harea]`. Simplify using `only [ph, map_mul]`. Use `push_cast`. Rewrite `hnz`, the goal using `[Complex.normSq_eq_conj_mul_self]`. Clear the denominators using the available nonvanishing facts.
-/
theorem HfArithRec_of_int (h : HYYIntRec) : HfArithRec := by
  intro D cc hcc δ hδ h0 N N' L L' hA c hc c' hc' A hA' B hB'
  obtain ⟨m, hm, harea, hdiv⟩ := div_okc D cc hcc.1 δ h0
  have hh : OKc D (D.host.φ₀ ((hYY D A B : D.host.K) : D.host.E)) :=
    okc_of D ⟨hYY D A B, h D N N' L L' hA A hA' B hB'⟩
  have hprod := okc_mul D (hdiv c hc c' hc') hh
  have hg := good_of_okc D hprod
  convert hg using 1
  have hnz : (Complex.normSq δ : ℂ) ≠ 0 := by exact_mod_cast (Complex.normSq_pos.2 h0).ne'
  have hs : (Real.sqrt D.host.d : ℂ) ≠ 0 := by exact_mod_cast (sqrt_pos D).ne'
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hcd : starRingEnd ℂ δ ≠ 0 := by simpa using h0
  rw [harea]
  simp only [ph, map_mul]
  push_cast
  rw [Complex.normSq_eq_conj_mul_self] at hnz ⊢
  field_simp

end Formalism.L2.Ker.Cd.IntegralLatticeDensity

end
