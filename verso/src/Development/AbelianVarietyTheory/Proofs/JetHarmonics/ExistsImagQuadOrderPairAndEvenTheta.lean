import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvenThetaTwoTorsionBasicProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImConjMulEqIntMulArea
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

noncomputable section

namespace GlobalTheory.MomOne.ThetaZero

/- English proof (translation)
Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t h`. Establish `hs : 0 < Real.sqrt d` using `Real.sqrt_pos.mpr (by exact_mod_cast hd)`. Establish `him` using `congrArg Complex.im h`. Establish `hre` using `congrArg Complex.re h`.

Simplify using `[wK] at him hre`. Establish `ht : t = 0`. Break down `him with h1 | h1` into its components or cases. Conclude with `h1`. Conclude with `absurd h1 (by positivity)`.

Substitute `ht` using the available equality. Simplify using `at hre`. Conclude with `⟨hre, rfl⟩`.
-/
theorem indep {d : ℕ} (hd : 0 < d) : LinearIndependent ℝ ![(1 : ℂ), wK d] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp [wK] at him hre
  have ht : t = 0 := by
    rcases him with h1 | h1
    · exact h1
    · exact absurd h1 (by positivity)
  subst ht
  simp at hre
  exact ⟨hre, rfl⟩

def pair {d : ℕ} (hd : 0 < d) : PeriodPair := ⟨1, wK d, indep hd⟩

/- English proof (translation)
Introduce `z`. Rewrite using `[PeriodPair.mem_lattice]`. Simplify using `only [pair, mul_one, InOK]`. Conclude with `⟨fun ⟨m, n, h⟩ => ⟨m, n, h.symm⟩, fun ⟨m, n, h⟩ => ⟨m, n, h.symm⟩⟩`.
-/
theorem isOK_pair {d : ℕ} (hd : 0 < d) : IsOK d (pair hd) := by
  intro z
  rw [PeriodPair.mem_lattice]
  simp only [pair, mul_one, InOK]
  exact ⟨fun ⟨m, n, h⟩ => ⟨m, n, h.symm⟩, fun ⟨m, n, h⟩ => ⟨m, n, h.symm⟩⟩

/- English proof (translation)
Unfold `PeriodPair.G eis`. Establish `e1` using `tsum_subtype (L.lattice : Set ℂ) (fun w : ℂ => (w ^ (2 * k))⁻¹)`. Establish `e2` using `tsum_subtype {w : ℂ | InOK d w ∧ w ≠ 0} (fun w : ℂ => 1 / w ^ (2 * k))`. Use `e1.trans (Eq.trans ?_ e2.symm)` and prove the remaining obligations. Use `tsum_congr fun w => ?_` and prove the remaining obligations.

Distinguish the cases in `h0 : w = 0`. Substitute `h0` using the available equality. Simplify using `[Set.indicator, hk]`. Establish `hw : w ∈ (L.lattice : Set ℂ) ↔ w ∈ {w : ℂ | InOK d w ∧ w ≠ 0}` using `⟨fun a => ⟨(h w).1 a, h0⟩, fun a => (h w).2 a.1⟩`. Distinguish the cases in `hm : w ∈ (L.lattice : Set ℂ)`.

Rewrite using `[Set.indicator_of_mem hm, Set.indicator_of_mem (hw.1 hm), one_div]`. Rewrite using `[Set.indicator_of_notMem hm, Set.indicator_of_notMem (hw.not.1 hm)]`.
-/
theorem G_eq {d : ℕ} {L : PeriodPair} (h : IsOK d L) {k : ℕ} (hk : k ≠ 0) :
    L.G (2 * k) = eis d k := by
  unfold PeriodPair.G eis
  have e1 := tsum_subtype (L.lattice : Set ℂ) (fun w : ℂ => (w ^ (2 * k))⁻¹)
  have e2 := tsum_subtype {w : ℂ | InOK d w ∧ w ≠ 0} (fun w : ℂ => 1 / w ^ (2 * k))
  refine e1.trans (Eq.trans ?_ e2.symm)
  refine tsum_congr fun w => ?_
  by_cases h0 : w = 0
  · subst h0
    simp [Set.indicator, hk]
  · have hw : w ∈ (L.lattice : Set ℂ) ↔ w ∈ {w : ℂ | InOK d w ∧ w ≠ 0} :=
      ⟨fun a => ⟨(h w).1 a, h0⟩, fun a => (h w).2 a.1⟩
    by_cases hm : w ∈ (L.lattice : Set ℂ)
    · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (hw.1 hm), one_div]
    · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (hw.not.1 hm)]

def lam (d : ℕ) : AddSubgroup ℂ := AddSubgroup.closure {1, wK d}

/- English proof (translation)
Rewrite using `[lam, AddSubgroup.mem_closure_pair]`. Simplify using `only [zsmul_eq_mul, mul_one, InOK]`. Conclude with `⟨fun ⟨m, n, h⟩ => ⟨m, n, h.symm⟩, fun ⟨m, n, h⟩ => ⟨m, n, h.symm⟩⟩`.
-/
theorem mem_lam (d : ℕ) (z : ℂ) : z ∈ lam d ↔ InOK d z := by
  rw [lam, AddSubgroup.mem_closure_pair]
  simp only [zsmul_eq_mul, mul_one, InOK]
  exact ⟨fun ⟨m, n, h⟩ => ⟨m, n, h.symm⟩, fun ⟨m, n, h⟩ => ⟨m, n, h.symm⟩⟩

/- English proof (translation)
Rewrite using `[lam, GlobalTheory.TransInv.area_closure_pair (indep hd)]`. Simplify using `[wK, abs_div]`.
-/
theorem area_lam {d : ℕ} (hd : 0 < d) : Formalism.MainNotions.TaylorLogMetric.area (lam d) = Real.sqrt d / 2 := by
  rw [lam, GlobalTheory.TransInv.area_closure_pair (indep hd)]
  simp [wK, abs_div]

/- English proof (translation)
Simplify using `only [Formalism.MainNotions.TaylorLogMetric.U1, U1, h1, area_lam hd]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem thetaTranslationOperator_apply {d : ℕ} (hd : 0 < d) (x : ℂ) (F : ℂ → ℂ) (z : ℂ) :
    Formalism.MainNotions.TaylorLogMetric.U1 (lam d) x F z = U1 d x F z := by
  simp only [Formalism.MainNotions.TaylorLogMetric.U1, U1, h1, area_lam hd]
  congr 2
  push_cast
  ring

/- English proof (translation)
Simplify using `only [U1]`. Rewrite using `[mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add, add_assoc z a b]`. Use `congr 2`. Simplify using `only [h1, map_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem thetaTranslation_comp_eq_cocycle_mul (d : ℕ) (a b : ℂ) (F : ℂ → ℂ) (z : ℂ) :
    U1 d a (U1 d b F) z =
      Complex.exp ((Real.pi : ℂ) / 2 * (h1 d b a - h1 d a b)) * U1 d (a + b) F z := by
  simp only [U1]
  rw [mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add, add_assoc z a b]
  congr 2
  simp only [h1, map_add]
  ring

/- English proof (translation)
Rewrite using `[mem_lam]`. Introduce and unpack `⟨m, n, e⟩`. Use `(LinearIndependent.pair_iff.1 (indep hd)) ((u + 1 - 2 * m : ℤ) : ℝ) ((v - 2 * n : ℤ) : ℝ) (by` as an intermediate fact. Simplify using `only [Complex.real_smul]`. Use `push_cast`.

Take the linear combination `2 * e)`. Establish `h1 : u + 1 - 2 * m = 0` using `by exact_mod_cast this.1`. Establish `h2 : v - 2 * n = 0` using `by exact_mod_cast this.2`. Conclude with `h ⟨⟨m - 1, by omega⟩, ⟨n, by omega⟩⟩`.
-/
theorem half_not_mem {d : ℕ} (hd : 0 < d) (u v : ℤ) (h : ¬ (Odd u ∧ Even v)) :
    ((u : ℂ) + (v : ℂ) * wK d) / 2 + 1 / 2 ∉ lam d := by
  rw [mem_lam]
  rintro ⟨m, n, e⟩
  have := (LinearIndependent.pair_iff.1 (indep hd)) ((u + 1 - 2 * m : ℤ) : ℝ) ((v - 2 * n : ℤ) : ℝ) (by
    simp only [Complex.real_smul]
    push_cast
    linear_combination 2 * e)
  have h1 : u + 1 - 2 * m = 0 := by exact_mod_cast this.1
  have h2 : v - 2 * n = 0 := by exact_mod_cast this.2
  exact h ⟨⟨m - 1, by omega⟩, ⟨n, by omega⟩⟩

/- English proof (translation)
Establish `hs : Real.sqrt d * Real.sqrt d = d` using `Real.mul_self_sqrt (Nat.cast_nonneg d)`. Establish `hc' : (d : ℝ) + 1 = 8 * c` using `by exact_mod_cast hc`. Simplify using `[Complex.normSq_apply, wK]`. Take the linear combination `(v : ℝ) ^ 2 / 4 * hs + (v : ℝ) ^ 2 / 4 * hc'`.
-/
theorem normSq_eq {d : ℕ} (c : ℤ) (hc : (d : ℤ) + 1 = 8 * c) (u v : ℤ) :
    Complex.normSq ((u : ℂ) + (v : ℂ) * wK d) = ((u ^ 2 + u * v + 2 * c * v ^ 2 : ℤ) : ℝ) := by
  have hs : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (Nat.cast_nonneg d)
  have hc' : (d : ℝ) + 1 = 8 * c := by exact_mod_cast hc
  simp [Complex.normSq_apply, wK]
  linear_combination (v : ℝ) ^ 2 / 4 * hs + (v : ℝ) ^ 2 / 4 * hc'

/- English proof (translation)
Take `⟨k, rfl⟩` from `h`. Rewrite using `[← Complex.exp_int_mul_two_pi_mul_I k]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exp_even {n : ℤ} (h : Even n) : Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ)) = 1 := by
  obtain ⟨k, rfl⟩ := h
  rw [← Complex.exp_int_mul_two_pi_mul_I k]
  congr 1
  push_cast
  ring

/- English proof (translation)
Establish `hs : ((Real.sqrt d : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne'`. Simplify using `only [h1, wK, map_add, map_mul, map_div₀, map_intCast, map_one, Complex.conj_I, Complex.conj_ofReal, map_ofNat]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem comm_eq {d : ℕ} (hd : 0 < d) (u v : ℤ) :
    h1 d (wK d) ((u : ℂ) + (v : ℂ) * wK d) - h1 d ((u : ℂ) + (v : ℂ) * wK d) (wK d) =
      2 * u * Complex.I := by
  have hs : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne'
  simp only [h1, wK, map_add, map_mul, map_div₀, map_intCast, map_one, Complex.conj_I,
    Complex.conj_ofReal, map_ofNat]
  push_cast
  field_simp
  ring

/- English proof (translation)
Establish `hd : 0 < d` using `by omega`. Take `⟨c, hc⟩ : ∃ c : ℤ, (d : ℤ) + 1 = 8 * c` from `⟨((d : ℤ) + 1) / 8, by omega⟩`. Establish `hlat : GlobalTheory.EvenTheta.IsLat (lam d)` using `⟨1, wK d, indep hd, rfl⟩`. Establish `ht : (1 / 2 : ℂ) ∉ lam d`. Simplify using `using half_not_mem hd 0 0 (by simp)`.

Establish `ht2 : 2 * (1 / 2 : ℂ) ∈ lam d` using `(mem_lam d _).2 ⟨1, 0, by simp⟩`. Take `⟨b1, b2, b3, -, b5, b6⟩` from `GlobalTheory.EvenTheta.evenThetaTwoTorsion_basic_properties (lam d) hlat (1 / 2) ht ht2`. Generalize the expression as in `Formalism.MainNotions.GL3Theta.th0 (lam d) (1 / 2) = θ at b1 b2 b3 b5 b6`. Establish `fix : ∀ u v : ℤ, ¬ (Odd u ∧ Even v) → U1 d ((u : ℂ) + (v : ℂ) * wK d) θ = θ`. Introduce `u v h`.

Use function extensionality and compare the values at `z`. Rewrite using `[← thetaTranslationOperator_apply hd]`. Conclude with `b6 _ ((mem_lam d _).2 ⟨u, v, rfl⟩) (half_not_mem hd u v h) z`. Use `⟨θ, b1, b2, b3, ?_, fun z hz => ?_⟩` and prove the remaining obligations. Introduce and unpack `x ⟨u, v, rfl⟩`.

Use function extensionality and compare the values at `z`. Simplify using `only [W1]`. Rewrite using `[normSq_eq c hc, Complex.ofReal_intCast]`. Distinguish the cases in `h : Odd u ∧ Even v`. Establish `f1` using `fix u (v - 1) (by`.

Introduce and unpack `⟨-, h2⟩`. Break down `h2 with ⟨a, ha⟩` into its components or cases. Break down `h.2 with ⟨b, hb⟩` into its components or cases. Use the proof step `omega)`. Establish `f2 : U1 d (wK d) θ = θ` using `by simpa using fix 0 1 (by simp)`.

Establish `k` using `thetaTranslation_comp_eq_cocycle_mul d ((u : ℂ) + ((v - 1 : ℤ) : ℂ) * wK d) (wK d) θ z`. Rewrite `k` using `[f2, f1, comm_eq hd, show (u : ℂ) + ((v - 1 : ℤ) : ℂ) * wK d + wK d = (u : ℂ) + (v : ℂ) * wK d by push_cast; ring]`. Establish `hev : Even (u ^ 2 + u * v + 2 * c * v ^ 2 - u)`. Take `⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩` from `h`. Conclude with `⟨(2 * a + 1) * a + (2 * a + 1) * b + c * (b + b) ^ 2, by ring⟩`.

Establish `e` using `exp_even hev`. Rewrite using `[k]`. Use `congr 1`. Rewrite using `[← one_mul (Complex.exp ((Real.pi : ℂ) / 2 * _)), ← e, ← Complex.exp_add]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hev : Even (u ^ 2 + u * v + 2 * c * v ^ 2)`. Break down `Int.even_or_odd u with ⟨a, rfl⟩ | ⟨a, rfl⟩` into its components or cases. Conclude with `⟨2 * a ^ 2 + a * v + c * v ^ 2, by ring⟩`.

Break down `Int.even_or_odd v with hv | ⟨b, rfl⟩` into its components or cases. Conclude with `absurd ⟨⟨a, rfl⟩, hv⟩ h`. Conclude with `⟨(2 * a + 1) * (a + b + 1) + c * (2 * b + 1) ^ 2, by ring⟩`. Rewrite using `[exp_even hev, one_mul, fix u v h]`. Take `⟨m, n, e⟩` from `(mem_lam d _).1 ((b5 z).1 hz)`.

Conclude with `⟨m - 1, n, by push_cast; linear_combination e⟩`.
-/
theorem exists_isTh {d : ℕ} (hd8 : d % 8 = 7) : ∃ θ : ℂ → ℂ, IsTh d θ := by
  have hd : 0 < d := by omega
  obtain ⟨c, hc⟩ : ∃ c : ℤ, (d : ℤ) + 1 = 8 * c := ⟨((d : ℤ) + 1) / 8, by omega⟩
  have hlat : GlobalTheory.EvenTheta.IsLat (lam d) := ⟨1, wK d, indep hd, rfl⟩
  have ht : (1 / 2 : ℂ) ∉ lam d := by
    simpa using half_not_mem hd 0 0 (by simp)
  have ht2 : 2 * (1 / 2 : ℂ) ∈ lam d := (mem_lam d _).2 ⟨1, 0, by simp⟩
  obtain ⟨b1, b2, b3, -, b5, b6⟩ := GlobalTheory.EvenTheta.evenThetaTwoTorsion_basic_properties (lam d) hlat (1 / 2) ht ht2
  generalize Formalism.MainNotions.GL3Theta.th0 (lam d) (1 / 2) = θ at b1 b2 b3 b5 b6
  have fix : ∀ u v : ℤ, ¬ (Odd u ∧ Even v) → U1 d ((u : ℂ) + (v : ℂ) * wK d) θ = θ := by
    intro u v h
    funext z
    rw [← thetaTranslationOperator_apply hd]
    exact b6 _ ((mem_lam d _).2 ⟨u, v, rfl⟩) (half_not_mem hd u v h) z
  refine ⟨θ, b1, b2, b3, ?_, fun z hz => ?_⟩
  · rintro x ⟨u, v, rfl⟩
    funext z
    simp only [W1]
    rw [normSq_eq c hc, Complex.ofReal_intCast]
    by_cases h : Odd u ∧ Even v
    · have f1 := fix u (v - 1) (by
        rintro ⟨-, h2⟩
        rcases h2 with ⟨a, ha⟩
        rcases h.2 with ⟨b, hb⟩
        omega)
      have f2 : U1 d (wK d) θ = θ := by simpa using fix 0 1 (by simp)
      have k := thetaTranslation_comp_eq_cocycle_mul d ((u : ℂ) + ((v - 1 : ℤ) : ℂ) * wK d) (wK d) θ z
      rw [f2, f1, comm_eq hd,
        show (u : ℂ) + ((v - 1 : ℤ) : ℂ) * wK d + wK d = (u : ℂ) + (v : ℂ) * wK d by
          push_cast; ring] at k
      have hev : Even (u ^ 2 + u * v + 2 * c * v ^ 2 - u) := by
        obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := h
        exact ⟨(2 * a + 1) * a + (2 * a + 1) * b + c * (b + b) ^ 2, by ring⟩
      have e := exp_even hev
      rw [k]
      congr 1
      rw [← one_mul (Complex.exp ((Real.pi : ℂ) / 2 * _)), ← e, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    · have hev : Even (u ^ 2 + u * v + 2 * c * v ^ 2) := by
        rcases Int.even_or_odd u with ⟨a, rfl⟩ | ⟨a, rfl⟩
        · exact ⟨2 * a ^ 2 + a * v + c * v ^ 2, by ring⟩
        · rcases Int.even_or_odd v with hv | ⟨b, rfl⟩
          · exact absurd ⟨⟨a, rfl⟩, hv⟩ h
          · exact ⟨(2 * a + 1) * (a + b + 1) + c * (2 * b + 1) ^ 2, by ring⟩
      rw [exp_even hev, one_mul, fix u v h]
  · obtain ⟨m, n, e⟩ := (mem_lam d _).1 ((b5 z).1 hz)
    exact ⟨m - 1, n, by push_cast; linear_combination e⟩

end GlobalTheory.MomOne.ThetaZero

namespace GlobalTheory.MomOne

/- English proof (translation)
Introduce `d hp h`. Use `⟨⟨ThetaZero.pair hp.pos, ThetaZero.isOK_pair hp.pos, ?_⟩, ThetaZero.exists_isTh (by omega)⟩` and prove the remaining obligations. Establish `h2` using `ThetaZero.G_eq (ThetaZero.isOK_pair hp.pos) (k := 2) (by norm_num)`. Establish `h3` using `ThetaZero.G_eq (ThetaZero.isOK_pair hp.pos) (k := 3) (by norm_num)`. Unfold `discr PeriodPair.g₂ PeriodPair.g₃`.

Rewrite using `[← h2, ← h3]`.
-/
theorem exists_pair_and_isTh : ∀ d : ℕ, d.Prime → d % 16 = 7 → (∃ L : PeriodPair, IsOK d L ∧ L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = discr d) ∧ ∃ θ : ℂ → ℂ, IsTh d θ := by
  intro d hp h
  refine ⟨⟨ThetaZero.pair hp.pos, ThetaZero.isOK_pair hp.pos, ?_⟩, ThetaZero.exists_isTh (by omega)⟩
  have h2 := ThetaZero.G_eq (ThetaZero.isOK_pair hp.pos) (k := 2) (by norm_num)
  have h3 := ThetaZero.G_eq (ThetaZero.isOK_pair hp.pos) (k := 3) (by norm_num)
  unfold discr PeriodPair.g₂ PeriodPair.g₃
  rw [← h2, ← h3]

end GlobalTheory.MomOne
