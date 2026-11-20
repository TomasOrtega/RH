import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DedekindZetaEqSumRealEisenstein
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.CurveLattice

open scoped UpperHalfPlane nonZeroDivisors Real

/- English proof (translation)
Establish `h1 : eisG Λ k = ∑' z : ℂ, ({w : ℂ | w ∈ Λ ∧ w ≠ 0}).indicator (fun w => (w ^ (2 * k))⁻¹) z`. Rewrite using `[← tsum_subtype, eisG]`. Conclude with `tsum_congr fun w => one_div _`. Establish `h2 : L.G (2 * k) = ∑' z : ℂ, (L.lattice : Set ℂ).indicator (fun w => (w ^ (2 * k))⁻¹) z`. Rewrite using `[← tsum_subtype, PeriodPair.G]`.

Both sides reduce to the same expression. Rewrite using `[h1, h2]`. Use `tsum_congr fun z => ?_` and prove the remaining obligations. Break down `eq_or_ne z 0 with rfl | hz` into its components or cases. Simplify using `[Set.indicator, hk]`.

Simplify using `[Set.indicator, hz, h]`.
-/
theorem eisG_eq_G (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice)
    {k : ℕ} (hk : k ≠ 0) : eisG Λ k = L.G (2 * k) := by
  have h1 : eisG Λ k = ∑' z : ℂ, ({w : ℂ | w ∈ Λ ∧ w ≠ 0}).indicator (fun w => (w ^ (2 * k))⁻¹) z := by
    rw [← tsum_subtype, eisG]
    exact tsum_congr fun w => one_div _
  have h2 : L.G (2 * k) = ∑' z : ℂ, (L.lattice : Set ℂ).indicator (fun w => (w ^ (2 * k))⁻¹) z := by
    rw [← tsum_subtype, PeriodPair.G]
    rfl
  rw [h1, h2]
  refine tsum_congr fun z => ?_
  rcases eq_or_ne z 0 with rfl | hz
  · simp [Set.indicator, hk]
  · simp [Set.indicator, hz, h]

section

variable {Λ : AddSubgroup ℂ} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
  (h : ∀ x, x ∈ Λ ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x)
include ha

/- English proof (translation)
Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t e`. Establish `e2 : (s * τ + t : ℂ) = 0` using `mul_left_cancel₀ ha (by`. Simplify using `only [Complex.real_smul] at e`. Take the linear combination `e)`.

Establish `e3 : s = 0` using `by simpa [τ.im_ne_zero] using congrArg Complex.im e2`. Conclude with `⟨e3, by simpa [e3] using e2⟩`.
-/
theorem indep_of_tau : LinearIndependent ℝ ![a * (τ : ℂ), a] := by
  rw [LinearIndependent.pair_iff]
  intro s t e
  have e2 : (s * τ + t : ℂ) = 0 := mul_left_cancel₀ ha (by
    simp only [Complex.real_smul] at e
    linear_combination e)
  have e3 : s = 0 := by simpa [τ.im_ne_zero] using congrArg Complex.im e2
  exact ⟨e3, by simpa [e3] using e2⟩

include h

omit ha in
/- English proof (translation)
Use extensionality with `x`. Rewrite using `[h, AddSubgroup.mem_closure_pair]`. Use `exists_congr fun m => exists_congr fun n => ?_` and prove the remaining obligations. Rewrite using `[zsmul_eq_mul, zsmul_eq_mul, show (m : ℂ) * (a * τ) + n * a = a * (m * τ + n) by ring]`.
-/
theorem eq_closure_of_tau : Λ = AddSubgroup.closure {a * (τ : ℂ), a} := by
  ext x
  rw [h, AddSubgroup.mem_closure_pair]
  refine exists_congr fun m => exists_congr fun n => ?_
  rw [zsmul_eq_mul, zsmul_eq_mul, show (m : ℂ) * (a * τ) + n * a = a * (m * τ + n) by ring]

/- English proof (translation)
Set `L : PeriodPair` to `⟨a * τ, a, indep_of_tau ha⟩`. Establish `hL : ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x` using `fun x => by`. Rewrite using `[PeriodPair.mem_lattice]`. Use `exists_congr fun m => exists_congr fun n => ?_` and prove the remaining obligations. Rewrite using `[show (m : ℂ) * L.ω₁ + n * L.ω₂ = a * (m * τ + n) by simp only [L]; ring]`.

Establish `hh : ∀ z, z ∈ Λ ↔ z ∈ L.lattice` using `fun z => by rw [h, hL]`. Rewrite using `[← latticeCurve_Δ_eq_discriminant ha hL, latticeCurve_Δ, TaylorLogMetric.discr, g2, g3, eisG_eq_G L Λ hh (by norm_num), eisG_eq_G L Λ hh (by norm_num)]`. Both sides reduce to the same expression.
-/
theorem discr_of_tau : TaylorLogMetric.discr Λ = (2 * π / a) ^ 12 * ModularForm.discriminant τ := by
  let L : PeriodPair := ⟨a * τ, a, indep_of_tau ha⟩
  have hL : ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x := fun x => by
    rw [PeriodPair.mem_lattice]
    refine exists_congr fun m => exists_congr fun n => ?_
    rw [show (m : ℂ) * L.ω₁ + n * L.ω₂ = a * (m * τ + n) by simp only [L]; ring]
  have hh : ∀ z, z ∈ Λ ↔ z ∈ L.lattice := fun z => by rw [h, hL]
  rw [← latticeCurve_Δ_eq_discriminant ha hL, latticeCurve_Δ, TaylorLogMetric.discr, g2, g3,
    eisG_eq_G L Λ hh (by norm_num), eisG_eq_G L Λ hh (by norm_num)]
  rfl

/- English proof (translation)
Establish `hy` using `τ.im_pos`. Establish `hp : 0 < ‖a‖ ^ 2 * τ.im` using `by have := norm_pos_iff.2 ha; positivity`. Establish `key : ∀ m n m' n' : ℤ, |((starRingEnd ℂ) (a * (m * (τ : ℂ) + n)) * (a * (m' * (τ : ℂ) + n'))).im| = ‖a‖ ^ 2 * τ.im * |((n * m' - m * n' : ℤ) : ℝ)|` using `fun m n m' n' => by`. Rewrite using `[← abs_of_pos hp, ← abs_mul]`. Use `congr 1`.

Simplify using `[Complex.sq_norm, Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree. Apply `IsLeast.csInf_eq` to reduce the goal to its premises. Prove the components needed by the constructor for the conclusion. Use `⟨hp, _, (h _).2 ⟨0, 1, rfl⟩, _, (h _).2 ⟨1, 0, rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[key]`. Simplify using the standard rewrite rules. Introduce and unpack `r ⟨hr, w₁, h1, w₂, h2, rfl⟩`. Take `⟨m, n, rfl⟩` from `(h _).1 h1`. Take `⟨m', n', rfl⟩` from `(h _).1 h2`.

Rewrite `hr`, the goal using `[key]`. Establish `h0 : (n * m' - m * n' : ℤ) ≠ 0` using `fun e => by simp [e] at hr`. Establish `: (1 : ℝ) ≤ |((n * m' - m * n' : ℤ) : ℝ)|` using `by exact_mod_cast Int.one_le_abs h0`. Conclude with `le_mul_of_one_le_right hp.le this`.
-/
theorem area_of_tau : area Λ = ‖a‖ ^ 2 * τ.im := by
  have hy := τ.im_pos
  have hp : 0 < ‖a‖ ^ 2 * τ.im := by have := norm_pos_iff.2 ha; positivity
  have key : ∀ m n m' n' : ℤ, |((starRingEnd ℂ) (a * (m * (τ : ℂ) + n)) * (a * (m' * (τ : ℂ) + n'))).im| =
      ‖a‖ ^ 2 * τ.im * |((n * m' - m * n' : ℤ) : ℝ)| := fun m n m' n' => by
    rw [← abs_of_pos hp, ← abs_mul]
    congr 1
    simp [Complex.sq_norm, Complex.normSq_apply]
    ring
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨hp, _, (h _).2 ⟨0, 1, rfl⟩, _, (h _).2 ⟨1, 0, rfl⟩, ?_⟩
    rw [key]
    simp
  · rintro r ⟨hr, w₁, h1, w₂, h2, rfl⟩
    obtain ⟨m, n, rfl⟩ := (h _).1 h1
    obtain ⟨m', n', rfl⟩ := (h _).1 h2
    rw [key] at hr ⊢
    have h0 : (n * m' - m * n' : ℤ) ≠ 0 := fun e => by simp [e] at hr
    have : (1 : ℝ) ≤ |((n * m' - m * n' : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs h0
    exact le_mul_of_one_le_right hp.le this

end

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hw`. Proceed by induction on `hw using AddSubgroup.closure_induction with`. Consider the case `mem x hx => exact hx`. Consider the case `zero => exact ⟨0, cc.zero_mem, by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨c, hc, rfl⟩` from `hx`. Take `⟨c', hc', rfl⟩` from `hy`. Conclude with `⟨c + c', cc.add_mem hc hc', by simp [mul_add]⟩`. Consider the case `neg x _ hx`.

Take `⟨c, hc, rfl⟩` from `hx`. Conclude with `⟨-c, cc.neg_mem hc, by simp⟩`. Conclude with `fun hw => AddSubgroup.subset_closure hw`.
-/
theorem mem_lamOf (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ w : ℂ) :
    w ∈ lamOf D cc δ ↔ ∃ c ∈ cc, w = δ * D.host.φ₀ (((c : D.host.K) : D.host.E)) := by
  constructor
  · intro hw
    induction hw using AddSubgroup.closure_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, cc.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hy
      exact ⟨c + c', cc.add_mem hc hc', by simp [mul_add]⟩
    | neg x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨-c, cc.neg_mem hc, by simp⟩
  · exact fun hw => AddSubgroup.subset_closure hw

/- English proof (translation)
The claim follows from `Formalism.FrobeniusOrbits.SplitK.finrank_K D.host.hyp.2.1.pos (D.host.sqd_sq)`.
-/
theorem finrank_hostK (D : D7) : Module.finrank ℚ D.host.K = 2 :=
  Formalism.FrobeniusOrbits.SplitK.finrank_K D.host.hyp.2.1.pos (D.host.sqd_sq)

/- English proof (translation)
The claim follows from `discr_eq_neg_of_sq_eq (finrank_hostK D) D.host.hyp.2.1.squarefree (by have := D.host.hyp.2.2.2.1; omega) (Formalism.FrobeniusOrbits.SplitK.bK_sq (D.host.sqd_sq))`.
-/
theorem discr_hostK (D : D7) : NumberField.discr D.host.K = -(D.host.d : ℤ) :=
  discr_eq_neg_of_sq_eq (finrank_hostK D) D.host.hyp.2.1.squarefree
    (by have := D.host.hyp.2.2.2.1; omega)
    (Formalism.FrobeniusOrbits.SplitK.bK_sq (D.host.sqd_sq))

/- English proof (translation)
Set `σ : D.host.K →+* ℂ` to `D.host.φ₀.comp D.host.K.val.toRingHom`. Set `I : (Ideal (𝓞 D.host.K))⁰` to `⟨cc, mem_nonZeroDivisors_of_ne_zero hcc⟩`. Take `⟨L, hL⟩` from `QuadraticZeta.exists_periodPair (finrank_hostK D) (discr_hostK D) σ (FractionalIdeal.mk0 D.host.K I)`. Take `⟨a, τ, ha, h⟩` from `exists_lattice_eq_mul_tau L`. Establish `h' : ∀ z, z ∈ σ '' (cc : FractionalIdeal (𝓞 D.host.K)⁰ D.host.K) ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = z` using `fun z => by`.

Rewrite using `[← h, ← SetLike.mem_coe, hL]`. Both sides reduce to the same expression. Establish `hN` using `QuadraticZeta.absNorm_eq_of_image (finrank_hostK D) (discr_hostK D) σ ha h'`. Rewrite `hN` using `[FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast]`. Use `⟨a, τ, ha, hN, fun δ x => ?_⟩` and prove the remaining obligations.

Rewrite using `[mem_lamOf]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc, rfl⟩`. Take `⟨m, n, e⟩` from `(h' _).1 ⟨(c : D.host.K), FractionalIdeal.mem_coeIdeal_of_mem _ hc, rfl⟩`. Conclude with `⟨m, n, by rw [mul_assoc, e]; rfl⟩`.

Introduce and unpack `⟨m, n, rfl⟩`. Take `⟨y, hy, e⟩` from `(h' _).2 ⟨m, n, rfl⟩`. Take `⟨c, hc, rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).1 hy`. Conclude with `⟨c, hc, by rw [mul_assoc, ← e]; rfl⟩`.
-/
theorem exists_tau (D : D7) (cc : Ideal (𝓞 D.host.K)) (hcc : cc ≠ ⊥) :
    ∃ (a : ℂ) (τ : ℍ), a ≠ 0 ∧ (Ideal.absNorm cc : ℝ) = 2 * ‖a‖ ^ 2 * τ.im / √(D.host.d) ∧
      ∀ δ x : ℂ, x ∈ lamOf D cc δ ↔ ∃ m n : ℤ, δ * a * (m * (τ : ℂ) + n) = x := by
  let σ : D.host.K →+* ℂ := D.host.φ₀.comp D.host.K.val.toRingHom
  let I : (Ideal (𝓞 D.host.K))⁰ := ⟨cc, mem_nonZeroDivisors_of_ne_zero hcc⟩
  obtain ⟨L, hL⟩ := QuadraticZeta.exists_periodPair (finrank_hostK D) (discr_hostK D) σ
    (FractionalIdeal.mk0 D.host.K I)
  obtain ⟨a, τ, ha, h⟩ := exists_lattice_eq_mul_tau L
  have h' : ∀ z, z ∈ σ '' (cc : FractionalIdeal (𝓞 D.host.K)⁰ D.host.K) ↔
      ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = z := fun z => by
    rw [← h, ← SetLike.mem_coe, hL]
    rfl
  have hN := QuadraticZeta.absNorm_eq_of_image (finrank_hostK D) (discr_hostK D) σ ha h'
  rw [FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast] at hN
  refine ⟨a, τ, ha, hN, fun δ x => ?_⟩
  rw [mem_lamOf]
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨m, n, e⟩ := (h' _).1 ⟨(c : D.host.K), FractionalIdeal.mem_coeIdeal_of_mem _ hc, rfl⟩
    exact ⟨m, n, by rw [mul_assoc, e]; rfl⟩
  · rintro ⟨m, n, rfl⟩
    obtain ⟨y, hy, e⟩ := (h' _).2 ⟨m, n, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    exact ⟨c, hc, by rw [mul_assoc, ← e]; rfl⟩

/- English proof (translation)
Introduce `D _ cc δ ⟨⟨hcc, _⟩, hδ⟩`. Take `⟨a, τ, ha, hN, h⟩` from `exists_tau D cc hcc`. Establish `h1` using `discr_of_tau (by simpa using ha) (h 1)`. Rewrite `h1` using `[one_mul]`. Establish `hδ' : δ ^ 12 = (2 * π / a) ^ 12 * ModularForm.discriminant τ` using `hδ.trans h1`.

Establish `hδ0 : δ ≠ 0`. Introduce and unpack `rfl`. Use `ModularForm.discriminant_ne_zero τ` as an intermediate fact. Use `Real.pi_ne_zero` as an intermediate fact. Simplify using `[*] at hδ'`.

Establish `hda : δ * a ≠ 0` using `mul_ne_zero hδ0 ha`. Use `⟨⟨_, _, indep_of_tau (τ := τ) hda, eq_closure_of_tau (h δ)⟩, hδ0, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[discr_of_tau hda (h δ), show (2 * π / (δ * a) : ℂ) ^ 12 * ModularForm.discriminant τ = ((2 * π / a) ^ 12 * ModularForm.discriminant τ) / δ ^ 12 by field_simp, ← hδ', div_self (pow_ne_zero _ hδ0)]`. Establish `hd : 0 < √(D.host.d : ℝ)` using `Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)`. Rewrite using `[area_of_tau hda (h δ), hN, norm_mul]`.

Clear the denominators using the available nonvanishing facts. Introduce `b w hw`. Take `⟨c, hc, rfl⟩` from `(mem_lamOf D cc δ w).1 hw`. Conclude with `(mem_lamOf D cc δ _).2 ⟨b * c, cc.mul_mem_left b hc, by simp; ring⟩`.
-/
theorem lattice_of_curve : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ (lamOf D cc δ) = AddSubgroup.closure {w₁, w₂}) ∧ δ ≠ 0 ∧ TaylorLogMetric.discr (lamOf D cc δ) = 1 ∧ area (lamOf D cc δ) = ‖δ‖ ^ 2 * (Ideal.absNorm cc : ℝ) * Real.sqrt D.host.d / 2 ∧ (∀ a : 𝓞 D.host.K, ∀ w ∈ (lamOf D cc δ), D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ (lamOf D cc δ)) := by
  intro D _ cc δ ⟨⟨hcc, _⟩, hδ⟩
  obtain ⟨a, τ, ha, hN, h⟩ := exists_tau D cc hcc
  have h1 := discr_of_tau (by simpa using ha) (h 1)
  rw [one_mul] at h1
  have hδ' : δ ^ 12 = (2 * π / a) ^ 12 * ModularForm.discriminant τ := hδ.trans h1
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    have := ModularForm.discriminant_ne_zero τ
    have := Real.pi_ne_zero
    simp [*] at hδ'
  have hda : δ * a ≠ 0 := mul_ne_zero hδ0 ha
  refine ⟨⟨_, _, indep_of_tau (τ := τ) hda, eq_closure_of_tau (h δ)⟩, hδ0, ?_, ?_, ?_⟩
  · rw [discr_of_tau hda (h δ), show (2 * π / (δ * a) : ℂ) ^ 12 * ModularForm.discriminant τ =
      ((2 * π / a) ^ 12 * ModularForm.discriminant τ) / δ ^ 12 by field_simp, ← hδ',
      div_self (pow_ne_zero _ hδ0)]
  · have hd : 0 < √(D.host.d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
    rw [area_of_tau hda (h δ), hN, norm_mul]
    field_simp
  · intro b w hw
    obtain ⟨c, hc, rfl⟩ := (mem_lamOf D cc δ w).1 hw
    exact (mem_lamOf D cc δ _).2 ⟨b * c, cc.mul_mem_left b hc, by simp; ring⟩

end GlobalTheory.CurveLattice
