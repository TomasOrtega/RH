import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.KernelDiagonalOfAbsoluteConvergence
import Formalism.FlagUnipotentLattices.KappaAssemblyOf

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set TopologicalSpace
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def rrk_Psi {G : Type*} [Group G] [MeasurableSpace G] (μ : Measure G) (φ : G → ℂ) (z : G) : ℝ≥0∞ :=
  ∫⁻ g, ‖φ g‖ₑ * ‖φ (g⁻¹ * z)‖ₑ ∂μ

section Abs

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] {μ : Measure G}
  [μ.IsMulLeftInvariant] {Γ : Subgroup G} [Countable Γ] {D : Set G} {φ : G → ℂ}

/- English proof (translation)
Rewrite using `[← rrka_lint h hφm hsa x]`. Unfold `rrk_Kab`. Repeatedly rewrite using `[← ENNReal.tsum_mul_left]`. Establish `hm : ∀ γ : Γ, AEMeasurable (fun y => ‖φ (x⁻¹ * y)‖ₑ * ‖φ (y⁻¹ * (γ : G) * x)‖ₑ) μ` using `fun γ => ((hφm.comp (measurable_const_mul x⁻¹)).enorm.mul (hφm.comp ((measurable_inv.mul_const (γ : G)).mul_const x)).enorm).aemeasurable`. Rewrite using `[lintegral_tsum hm]`.

Use `tsum_congr fun γ => ?_` and prove the remaining obligations. Unfold `rrk_Psi`. Rewrite using `[← lintegral_mul_left_eq_self (fun y => ‖φ (x⁻¹ * y)‖ₑ * ‖φ (y⁻¹ * (γ : G) * x)‖ₑ) x]`. Use `lintegral_congr fun g => ?_` and prove the remaining obligations. Simplify using `[mul_assoc]`.
-/
theorem rrk_Kab_sq (h : rr_FD μ Γ D) (hφm : Measurable φ) (hsa : ∀ z, φ z⁻¹ = star (φ z)) (x : G) :
    ∫⁻ y in D, (rrk_Kab Γ φ x y) ^ 2 ∂μ = ∑' γ : Γ, rrk_Psi μ φ (x⁻¹ * (γ : G) * x) := by
  rw [← rrka_lint h hφm hsa x]
  unfold rrk_Kab
  simp_rw [← ENNReal.tsum_mul_left]
  have hm : ∀ γ : Γ, AEMeasurable (fun y => ‖φ (x⁻¹ * y)‖ₑ * ‖φ (y⁻¹ * (γ : G) * x)‖ₑ) μ := fun γ =>
    ((hφm.comp (measurable_const_mul x⁻¹)).enorm.mul
      (hφm.comp ((measurable_inv.mul_const (γ : G)).mul_const x)).enorm).aemeasurable
  rw [lintegral_tsum hm]
  refine tsum_congr fun γ => ?_
  unfold rrk_Psi
  rw [← lintegral_mul_left_eq_self (fun y => ‖φ (x⁻¹ * y)‖ₑ * ‖φ (y⁻¹ * (γ : G) * x)‖ₑ) x]
  refine lintegral_congr fun g => ?_
  simp [mul_assoc]

end Abs

def ConvDec (X : CData) (q₀ : ℕ) (h' : ℝ) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ z : X.I.GA,
    rrk_Psi (X.I.muA X.μf) X.φ z ≤
      ENNReal.ofReal (M * ∏ v, Real.exp (-(Formalism.HermitianLatticeCounting.S7.decExp h' q₀ (cartanDistance (X.I.ε v) (z.1 v))))) ∧
    (rrk_Psi (X.I.muA X.μf) X.φ z ≠ 0 → z.2 ∈ X.I.Kset)

def AllCount (X : CData) (B : ℝ) : Prop :=
  ∀ᵐ x ∂X.μ, ∃ Ac : ℝ, 0 ≤ Ac ∧ ∀ r : InfinitePlace X.I.F → ℝ, (∀ v, 0 ≤ r v) → ∀ S : Finset X.I.GFset,
    (∀ γ ∈ S, (x⁻¹ * (γ : X.I.GA) * x).2 ∈ X.I.Kset ∧ ∀ v, X.dist x γ v ≤ r v) →
    (S.card : ℝ) ≤ Ac * Real.exp (B * ∑ v, r v)

def ConvDecay (X : CData) (q₀ : ℕ) (h' : ℝ) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ z : X.I.GA,
    rrk_Psi (X.I.muA X.μf) X.φ z ≤
      ENNReal.ofReal (M * ∏ v, Real.exp (-(Formalism.HermitianLatticeCounting.S7.decExp h' q₀ (cartanDistance (X.I.ε v) (z.1 v)))))

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Apply `hz` to reduce the goal to its premises. Unfold `rrk_Psi`. Establish `h0 : ∀ g : X.I.GA, ‖X.φ g‖ₑ * ‖X.φ (g⁻¹ * z)‖ₑ = 0`. Introduce `g`.

Assume the negation of the conclusion as `hne`. Establish `h1 : X.φ g ≠ 0` using `fun e => hne (by simp [e])`. Establish `h2 : X.φ (g⁻¹ * z) ≠ 0` using `fun e => hne (by simp [e])`. Establish `e1 : X.e g.2 ≠ 0` using `fun e => h1 (by unfold CData.φ phe; rw [e, mul_zero])`. Establish `e2 : X.e (g⁻¹ * z).2 ≠ 0` using `fun e => h2 (by unfold CData.φ phe; rw [e, mul_zero])`.

Establish `k1` using `he _ e1`. Establish `k2` using `he _ e2`. Apply `hc` to reduce the goal to its premises. Establish `hmul : z.2 = g.2 * (g⁻¹ * z).2` using `by show z.2 = g.2 * (g.2⁻¹ * z.2) group`. Rewrite using `[hmul]`.

Conclude with `(Formalism.UG.stabGL X.I.Lf).mul_mem k1 k2`. Simplify using `[h0]`.
-/
theorem rrk_Psi_supp (X : CData) (he : ∀ x, X.e x ≠ 0 → x ∈ X.I.Kset) (z : X.I.GA)
    (hz : rrk_Psi (X.I.muA X.μf) X.φ z ≠ 0) : z.2 ∈ X.I.Kset := by
  by_contra hc
  apply hz
  unfold rrk_Psi
  have h0 : ∀ g : X.I.GA, ‖X.φ g‖ₑ * ‖X.φ (g⁻¹ * z)‖ₑ = 0 := by
    intro g
    by_contra hne
    have h1 : X.φ g ≠ 0 := fun e => hne (by simp [e])
    have h2 : X.φ (g⁻¹ * z) ≠ 0 := fun e => hne (by simp [e])
    have e1 : X.e g.2 ≠ 0 := fun e => h1 (by unfold CData.φ phe; rw [e, mul_zero])
    have e2 : X.e (g⁻¹ * z).2 ≠ 0 := fun e => h2 (by unfold CData.φ phe; rw [e, mul_zero])
    have k1 := he _ e1
    have k2 := he _ e2
    apply hc
    have hmul : z.2 = g.2 * (g⁻¹ * z).2 := by
      show z.2 = g.2 * (g.2⁻¹ * z.2)
      group
    rw [hmul]
    exact (Formalism.UG.stabGL X.I.Lf).mul_mem k1 k2
  simp [h0]

/- English proof (translation)
Take `⟨M, hM, hb⟩` from `h`. Conclude with `⟨M, hM, fun z => ⟨hb z, rrk_Psi_supp X hX.1.2.2.2.2.2.2.1.2.2.2.2.1 z⟩⟩`.
-/
theorem ConvDec_of_decay (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) {q₀ : ℕ} {h' : ℝ} (h : ConvDecay X q₀ h') :
    ConvDec X q₀ h' := by
  obtain ⟨M, hM, hb⟩ := h
  exact ⟨M, hM, fun z => ⟨hb z, rrk_Psi_supp X hX.1.2.2.2.2.2.2.1.2.2.2.2.1 z⟩⟩

open Classical in

/- English proof (translation)
Take `⟨hH, hF, -⟩` from `hd`. Use `hH` as an intermediate fact. Establish `: SecondCountableTopology X.I.Gf` using `rr_secondCountable X.I X.μf`. Establish `: (X.I.muA X.μf).IsMulLeftInvariant` using `rr_muA_left X.I X.μf`. Establish `h1` using `rr_FD_of X.I X.μf X.fund hF`.

Take `⟨M, hM, hΨ⟩` from `hc`. Unfold `AbsKernelSquareIntegrable`. Use `filter_upwards [hn] with x hx`. Take `⟨Ac, hAc, hcnt⟩` from `hx`. Establish `e : ∫⁻ y, (∑' γ : X.I.GFset, ‖X.φ (x⁻¹ * (γ : X.I.GA) * y)‖ₑ) ^ 2 ∂X.μ = ∑' γ : X.I.GFset, rrk_Psi (X.I.muA X.μf) X.φ (x⁻¹ * (γ : X.I.GA) * x)` using `rrk_Kab_sq h1 hφ.1 hφ.2.1 x`.

Rewrite using `[e]`. Use `set bd : X.I.GFset → ℝ := fun γ => ∏ v, Real.exp (-(Formalism.HermitianLatticeCounting.S7.decExp h' q₀ (X.dist x γ v))) with hbd`. Establish `hbdn : ∀ γ, 0 ≤ bd γ` using `fun γ => Finset.prod_nonneg fun v _ => (Real.exp_pos _).le`. Use `set Cst : ℝ := max (Ac * (Real.exp B / (1 - Real.exp (-B))) ^ Fintype.card (InfinitePlace X.I.F)) Ac with hCst`. Use `ne_top_of_le_ne_top (b := ENNReal.ofReal (M * Cst)) ENNReal.ofReal_ne_top ?_` and prove the remaining obligations.

Rewrite using `[ENNReal.tsum_eq_iSup_sum]`. Use `iSup_le fun s : Finset X.I.GFset => ?_` and prove the remaining obligations. Use `set S : Finset X.I.GFset := s.filter (fun γ : X.I.GFset => rrk_Psi (X.I.muA X.μf) X.φ (x⁻¹ * (γ : X.I.GA) * x) ≠ 0) with hS`. Establish `hterm : ∀ γ ∈ s, rrk_Psi (X.I.muA X.μf) X.φ (x⁻¹ * (γ : X.I.GA) * x) ≤ (if rrk_Psi (X.I.muA X.μf) X.φ (x⁻¹ * (γ : X.I.GA) * x) ≠ 0 then ENNReal.ofReal (M * bd γ) else 0)`. Introduce `γ _`.

Distinguish the cases in `h0 : rrk_Psi (X.I.muA X.μf) X.φ (x⁻¹ * (γ : X.I.GA) * x) = 0`. Simplify using `[h0]`. Rewrite using `[if_pos h0]`. Conclude with `(hΨ _).1`. Use `le_trans (Finset.sum_le_sum hterm) ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_filter, ← ENNReal.ofReal_sum_of_nonneg (fun γ _ => mul_nonneg hM (hbdn γ)), ← Finset.mul_sum]`. Use `ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hM)` and prove the remaining obligations. Establish `hcS : ∀ r : InfinitePlace X.I.F → ℝ, (∀ v, 0 ≤ r v) → ((S.filter fun γ => ∀ v, X.dist x γ v ≤ r v).card : ℝ) ≤ Ac * Real.exp (B * ∑ v, r v)`. Introduce `r hr`. Use `hcnt r hr _ fun γ hγ => ?_` and prove the remaining obligations.

Establish `h3` using `Finset.mem_filter.1 hγ`. Conclude with `⟨(hΨ _).2 (Finset.mem_filter.1 h3.1).2, h3.2⟩`. Break down `Nat.eq_zero_or_pos q₀ with h0 | hpos` into its components or cases. Use `le_trans ?_ (le_max_right _ _)` and prove the remaining obligations. Establish `hd0 : ∀ γ v, X.dist x γ v = 0` using `fun γ v => cartan_distance_eq_zero_of_definite (by rw [← h0, ← hq v]; rfl) _`.

Establish `hb1 : ∀ γ ∈ S, bd γ ≤ 1`. Introduce `γ _`. Use `Finset.prod_le_one (fun v _ => (Real.exp_pos _).le) fun v _ => ?_` and prove the remaining obligations. Rewrite using `[hd0 γ v]`. Simplify using `[Formalism.HermitianLatticeCounting.S7.decExp]`.

Establish `h2` using `hcS (fun _ => 0) (fun _ => le_rfl)`. Establish `hall : (S.filter fun γ => ∀ v, X.dist x γ v ≤ (fun _ => (0 : ℝ)) v) = S` using `Finset.filter_true_of_mem fun γ _ v => (hd0 γ v).le`. Rewrite `h2` using `[hall]`. Simplify using `only [Finset.sum_const_zero, mul_zero, Real.exp_zero, mul_one] at h2`. Combine the equalities or inequalities in the displayed calculation.

Use `le_trans ?_ (le_max_left _ _)` and prove the remaining obligations. Conclude with `Formalism.HermitianLatticeCounting.Final.NearFarVolumeBounds.allSumRate (InfinitePlace X.I.F) X.I.GFset S (X.dist x) Ac B h' q₀ hpos hAc hB hthr (fun γ _ v => cartan_distance_nonneg _ _) hcS`.
-/
theorem abs_kernel_L2_of_count_and_decay (X : CData) (hd : RegData X) (hφ : PhiIdem X) {q₀ : ℕ} (hq : ∀ v, q0At X.I v = q₀) {h' B : ℝ}
    (hB : 0 < B) (hthr : 16 * B * Real.sqrt (2 * (q₀ : ℝ)) ≤ h') (hc : ConvDec X q₀ h') (hn : AllCount X B) :
    AbsKernelSquareIntegrable X := by
  obtain ⟨hH, hF, -⟩ := hd
  have := hH
  have : SecondCountableTopology X.I.Gf := rr_secondCountable X.I X.μf
  have : (X.I.muA X.μf).IsMulLeftInvariant := rr_muA_left X.I X.μf
  have h1 := rr_FD_of X.I X.μf X.fund hF
  obtain ⟨M, hM, hΨ⟩ := hc
  unfold AbsKernelSquareIntegrable
  filter_upwards [hn] with x hx
  obtain ⟨Ac, hAc, hcnt⟩ := hx
  have e : ∫⁻ y, (∑' γ : X.I.GFset, ‖X.φ (x⁻¹ * (γ : X.I.GA) * y)‖ₑ) ^ 2 ∂X.μ =
      ∑' γ : X.I.GFset, rrk_Psi (X.I.muA X.μf) X.φ (x⁻¹ * (γ : X.I.GA) * x) :=
    rrk_Kab_sq h1 hφ.1 hφ.2.1 x
  rw [e]
  set bd : X.I.GFset → ℝ := fun γ => ∏ v, Real.exp (-(Formalism.HermitianLatticeCounting.S7.decExp h' q₀ (X.dist x γ v))) with hbd
  have hbdn : ∀ γ, 0 ≤ bd γ := fun γ => Finset.prod_nonneg fun v _ => (Real.exp_pos _).le
  set Cst : ℝ := max (Ac * (Real.exp B / (1 - Real.exp (-B))) ^ Fintype.card (InfinitePlace X.I.F)) Ac with hCst
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal (M * Cst)) ENNReal.ofReal_ne_top ?_
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s : Finset X.I.GFset => ?_
  set S : Finset X.I.GFset := s.filter (fun γ : X.I.GFset => rrk_Psi (X.I.muA X.μf) X.φ (x⁻¹ * (γ : X.I.GA) * x) ≠ 0) with hS
  have hterm : ∀ γ ∈ s, rrk_Psi (X.I.muA X.μf) X.φ (x⁻¹ * (γ : X.I.GA) * x) ≤
      (if rrk_Psi (X.I.muA X.μf) X.φ (x⁻¹ * (γ : X.I.GA) * x) ≠ 0 then ENNReal.ofReal (M * bd γ) else 0) := by
    intro γ _
    by_cases h0 : rrk_Psi (X.I.muA X.μf) X.φ (x⁻¹ * (γ : X.I.GA) * x) = 0
    · simp [h0]
    · rw [if_pos h0]
      exact (hΨ _).1
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_filter, ← ENNReal.ofReal_sum_of_nonneg (fun γ _ => mul_nonneg hM (hbdn γ)), ← Finset.mul_sum]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hM)
  have hcS : ∀ r : InfinitePlace X.I.F → ℝ, (∀ v, 0 ≤ r v) →
      ((S.filter fun γ => ∀ v, X.dist x γ v ≤ r v).card : ℝ) ≤ Ac * Real.exp (B * ∑ v, r v) := by
    intro r hr
    refine hcnt r hr _ fun γ hγ => ?_
    have h3 := Finset.mem_filter.1 hγ
    exact ⟨(hΨ _).2 (Finset.mem_filter.1 h3.1).2, h3.2⟩
  rcases Nat.eq_zero_or_pos q₀ with h0 | hpos
  · refine le_trans ?_ (le_max_right _ _)
    have hd0 : ∀ γ v, X.dist x γ v = 0 := fun γ v => cartan_distance_eq_zero_of_definite (by rw [← h0, ← hq v]; rfl) _
    have hb1 : ∀ γ ∈ S, bd γ ≤ 1 := by
      intro γ _
      refine Finset.prod_le_one (fun v _ => (Real.exp_pos _).le) fun v _ => ?_
      rw [hd0 γ v]
      simp [Formalism.HermitianLatticeCounting.S7.decExp]
    have h2 := hcS (fun _ => 0) (fun _ => le_rfl)
    have hall : (S.filter fun γ => ∀ v, X.dist x γ v ≤ (fun _ => (0 : ℝ)) v) = S :=
      Finset.filter_true_of_mem fun γ _ v => (hd0 γ v).le
    rw [hall] at h2
    simp only [Finset.sum_const_zero, mul_zero, Real.exp_zero, mul_one] at h2
    calc ∑ γ ∈ S, bd γ ≤ ∑ _γ ∈ S, (1 : ℝ) := Finset.sum_le_sum hb1
      _ = (S.card : ℝ) := by simp
      _ ≤ Ac := h2
  · refine le_trans ?_ (le_max_left _ _)
    exact Formalism.HermitianLatticeCounting.Final.NearFarVolumeBounds.allSumRate (InfinitePlace X.I.F) X.I.GFset S (X.dist x) Ac B h' q₀ hpos hAc hB hthr
      (fun γ _ v => cartan_distance_nonneg _ _) hcS

/- English proof (translation)
The claim follows from `kernel_diagonal_of_local_projector_of_abs_kernel_L2 D hloc X hX h1 hu (abs_kernel_L2_of_count_and_decay X (RegData_of_HypB X hX) (PhiIdem_of D hloc X hX h1) (X.qq_spec hX).1 hB hthr hc hn)`.
-/
theorem kernel_diagonal_of_lattice_count (D : Formalism.BasicNotions.D7) (hloc : LocalProjectorRealPlace D) (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A)
    (h1 : X.GapAboveThreeHalvesPower) (hu : UnimodA X) {h' B : ℝ} (hB : 0 < B) (hthr : 16 * B * Real.sqrt (2 * (X.qq : ℝ)) ≤ h')
    (hc : ConvDec X X.qq h') (hn : AllCount X B) : X.KernelDiag :=
  kernel_diagonal_of_local_projector_of_abs_kernel_L2 D hloc X hX h1 hu
    (abs_kernel_L2_of_count_and_decay X (RegData_of_HypB X hX) (PhiIdem_of D hloc X hX h1) (X.qq_spec hX).1 hB hthr hc hn)

/- English proof (translation)
Take `⟨v⟩ : Nonempty (InfinitePlace X.I.F)` from `inferInstance`. Establish `h` using `h2 v`. Rewrite `h` using `[(X.qq_spec hX).1 v]`. Rewrite using `[Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]`. Establish `hs : Real.sqrt 2 ≤ 363 / 256`.

Rewrite using `[Real.sqrt_le_left (by norm_num)]`. Evaluate the numerical expressions. Establish `hq : 0 ≤ Real.sqrt (X.qq : ℝ)` using `Real.sqrt_nonneg _`. Establish `hn : 0 ≤ (X.I.n : ℝ) ^ 2` using `by positivity`. Establish `hp : 0 ≤ (X.I.n : ℝ) ^ 2 * Real.sqrt (X.qq : ℝ)` using `mul_nonneg hn hq`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hs hp]`.
-/
theorem rrk_thr (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) (h2 : X.GapAboveSquareRootThreshold 363) :
    16 * (2 * (X.I.n : ℝ) ^ 2) * Real.sqrt (2 * (X.qq : ℝ)) ≤ X.h / 8 := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace X.I.F) := inferInstance
  have h := h2 v
  rw [(X.qq_spec hX).1 v] at h
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hs : Real.sqrt 2 ≤ 363 / 256 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hq : 0 ≤ Real.sqrt (X.qq : ℝ) := Real.sqrt_nonneg _
  have hn : 0 ≤ (X.I.n : ℝ) ^ 2 := by positivity
  have hp : 0 ≤ (X.I.n : ℝ) ^ 2 * Real.sqrt (X.qq : ℝ) := mul_nonneg hn hq
  nlinarith [mul_le_mul_of_nonneg_right hs hp]

/- English proof (translation)
The claim follows from `kernel_diagonal_of_lattice_count D hloc X hX h1 hu (by have : (1 : ℝ) ≤ (X.I.n : ℝ) := by exact_mod_cast hn1 positivity) (rrk_thr X hX h2) (ConvDec_of_decay X hX hc) hn`.
-/
theorem kernel_diagonal_of_decay_threshold (D : Formalism.BasicNotions.D7) (hloc : LocalProjectorRealPlace D) (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A)
    (hn1 : 1 ≤ X.I.n) (h1 : X.GapAboveThreeHalvesPower) (h2 : X.GapAboveSquareRootThreshold 363) (hu : UnimodA X) (hc : ConvDecay X X.qq (X.h / 8))
    (hn : AllCount X (2 * (X.I.n : ℝ) ^ 2)) : X.KernelDiag :=
  kernel_diagonal_of_lattice_count D hloc X hX h1 hu
    (by have : (1 : ℝ) ≤ (X.I.n : ℝ) := by exact_mod_cast hn1
        positivity) (rrk_thr X hX h2) (ConvDec_of_decay X hX hc) hn

end Formalism.MainNotions.LeviCoordinates

end
