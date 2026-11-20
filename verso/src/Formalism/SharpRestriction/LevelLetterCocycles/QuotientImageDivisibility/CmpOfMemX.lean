import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.FrobeniusUniformizerPowDvd
import Formalism.SharpRestriction.LevelLetterCocycles.SaturationPullbackOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.RelayGeneralCaseOfAdmissible

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section D

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

/- English proof (translation)
Rewrite using `[Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T (W.N T).zero_mem]`. Conclude with `map_zero (W.cmp T)`.
-/
theorem cmpD_zero : Formalism.MainNotions.ArcLiftingSetup.cmpD W T 0 = 0 := by
  rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T (W.N T).zero_mem]
  exact map_zero (W.cmp T)

/- English proof (translation)
Simplify using `[LocWach.Q, hs]`.
-/
theorem Q_eq_q (hs : W.s = 1) : W.Q = W.q := by
  simp [LocWach.Q, hs]

/- English proof (translation)
Rewrite using `[Q_eq_q W hs]`. Conclude with `Formalism.MainNotions.UnusedSlot80.ArcF.constantCoeff_q_zero_eq_p W`.
-/
theorem cc_Q (hs : W.s = 1) (i : ZMod n) :
    PowerSeries.constantCoeff (W.Q i) = (PD.p : O) := by
  rw [Q_eq_q W hs]; exact Formalism.MainNotions.UnusedSlot80.ArcF.constantCoeff_q_zero_eq_p W

/- English proof (translation)
Introduce `h`. Apply `Formalism.MainNotions.UnusedSlot80.ArcF.p_ne_zero W'` to reduce the goal to its premises. Use `congrArg (algebraMap O LL) h` as an intermediate fact. Rewrite `this` using `[map_natCast, map_zero]`. Then use the resulting hypothesis.
-/
theorem p_ne_zero_O (W' : LocWach PD LL O v n) : ((PD.p : ℕ) : O) ≠ 0 := by
  intro h
  apply Formalism.MainNotions.UnusedSlot80.ArcF.p_ne_zero W'
  have := congrArg (algebraMap O LL) h
  rwa [map_natCast, map_zero] at this

/- English proof (translation)
Rewrite using `[← algebraMap_smul (LetA O n) o x, ← algebraMap_smul (LetA O n) o (a • x), smul_smul, smul_smul, mul_comm]`.
-/
theorem osmul_comm (a : LetA O n) (o : O) (x : W.DD T) : a • o • x = o • a • x := by
  rw [← algebraMap_smul (LetA O n) o x, ← algebraMap_smul (LetA O n) o (a • x), smul_smul,
    smul_smul, mul_comm]

/- English proof (translation)
Rewrite using `[smul_smul, smul_smul, mul_comm]`.
-/
theorem aself_comm (a b : LetA O n) (x : W.DD T) : a • b • x = b • a • x := by
  rw [smul_smul, smul_smul, mul_comm]

/- English proof (translation)
Take `⟨w, hw⟩` from `hR.2.2.2.2.1`. Establish `hE : Formalism.MainNotions.DeltaInvariantLattices.Eat (fun _ : ZMod n => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) W.π₀ = Formalism.MainNotions.LiftingTheory.qp W`. Use function extensionality and compare the values at `i`. Simplify using `[Formalism.MainNotions.DeltaInvariantLattices.Eat, Formalism.MainNotions.LiftingTheory.qp, LocWach.π₀]`. Rewrite `hw` using `[hE]`.

Establish `hQ` using `Q_eq_q W hs`. Use `⟨((w⁻¹ : (LetA O n)ˣ) : LetA O n), ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[hQ, hw, ← mul_assoc, Units.inv_mul, one_mul]`. Establish `hcq : PowerSeries.constantCoeff (Formalism.MainNotions.LiftingTheory.qp W i) = (PD.p : O)`. Simplify using `[Formalism.MainNotions.LiftingTheory.qp, LocWach.π₀, Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_cc hR]`.

Establish `h1` using `congrArg (fun z : LetA O n => PowerSeries.constantCoeff (z i)) hw`. Simplify using `only [Pi.mul_apply, map_mul] at h1`. Establish `hq : PowerSeries.constantCoeff (W.q i) = (PD.p : O)` using `Formalism.MainNotions.UnusedSlot80.ArcF.constantCoeff_q_zero_eq_p W`. Rewrite `h1` using `[hcq, hq]`. Establish `hw1 : PowerSeries.constantCoeff ((w : LetA O n) i) = 1`.

Establish `h2 : (1 : O) * (PD.p : O) = PowerSeries.constantCoeff ((w : LetA O n) i) * (PD.p : O)`. Rewrite using `[one_mul]`. Conclude with `h1`. Conclude with `(mul_right_cancel₀ (p_ne_zero_O W) h2).symm`. Establish `h3` using `congrArg (fun z : LetA O n => PowerSeries.constantCoeff (z i)) (Units.inv_mul w)`.

Simplify using `only [Pi.mul_apply, map_mul, hw1, mul_one, Pi.one_apply, map_one] at h3`. Conclude with `h3`.
-/
theorem qp_unit [IsDomain O] (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) :
    ∃ u : LetA O n, Formalism.MainNotions.LiftingTheory.qp W = u * W.Q ∧ ∀ i, PowerSeries.constantCoeff (u i) = 1 := by
  obtain ⟨w, hw⟩ := hR.2.2.2.2.1
  have hE : Formalism.MainNotions.DeltaInvariantLattices.Eat (fun _ : ZMod n => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) W.π₀ =
      Formalism.MainNotions.LiftingTheory.qp W := by
    funext i
    simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, Formalism.MainNotions.LiftingTheory.qp, LocWach.π₀]
  rw [hE] at hw
  have hQ := Q_eq_q W hs
  refine ⟨((w⁻¹ : (LetA O n)ˣ) : LetA O n), ?_, fun i => ?_⟩
  · rw [hQ, hw, ← mul_assoc, Units.inv_mul, one_mul]
  · have hcq : PowerSeries.constantCoeff (Formalism.MainNotions.LiftingTheory.qp W i) = (PD.p : O) := by
      simp [Formalism.MainNotions.LiftingTheory.qp, LocWach.π₀, Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_cc hR]
    have h1 := congrArg (fun z : LetA O n => PowerSeries.constantCoeff (z i)) hw
    simp only [Pi.mul_apply, map_mul] at h1
    have hq : PowerSeries.constantCoeff (W.q i) = (PD.p : O) := Formalism.MainNotions.UnusedSlot80.ArcF.constantCoeff_q_zero_eq_p W
    rw [hcq, hq] at h1
    have hw1 : PowerSeries.constantCoeff ((w : LetA O n) i) = 1 := by
      have h2 : (1 : O) * (PD.p : O) = PowerSeries.constantCoeff ((w : LetA O n) i) * (PD.p : O) := by
        rw [one_mul]; exact h1
      exact (mul_right_cancel₀ (p_ne_zero_O W) h2).symm
    have h3 := congrArg (fun z : LetA O n => PowerSeries.constantCoeff (z i)) (Units.inv_mul w)
    simp only [Pi.mul_apply, map_mul, hw1, mul_one, Pi.one_apply, map_one] at h3
    exact h3

/- English proof (translation)
Establish `e` using `Formalism.MainNotions.UnusedSlot80.Relay2.φpow_smul W T 1 (letE (c - 1)) x`. Rewrite `e` using `[Formalism.MainNotions.UnusedSlot80.SatPW.φA_pow_letE W (c - 1) 1, hxi]`. Simplify using `only [pow_one, Nat.cast_one, sub_add_cancel] at e`. Conclude with `e.symm`.
-/
theorem letter_phi (c : ZMod n) {x : W.DD T} (hxi : (letE (c - 1) : LetA O n) • x = x) :
    (letE c : LetA O n) • W.φD T x = W.φD T x := by
  have e := Formalism.MainNotions.UnusedSlot80.Relay2.φpow_smul W T 1 (letE (c - 1)) x
  rw [Formalism.MainNotions.UnusedSlot80.SatPW.φA_pow_letE W (c - 1) 1, hxi] at e
  simp only [pow_one, Nat.cast_one, sub_add_cancel] at e
  exact e.symm

/- English proof (translation)
Assemble the required witnesses or components as `⟨x, hx, by simpa using hxi⟩`.
-/
theorem mem_Nl {i : ZMod n} {x : W.DD T} (hx : x ∈ W.N T) (hxi : (letE i : LetA O n) • x = x) :
    x ∈ W.Nl T i :=
  ⟨x, hx, by simpa using hxi⟩

/- English proof (translation)
Take `⟨y, hy, rfl⟩` from `hx`. Simplify using `only [LinearMap.smul_apply, LinearMap.id_apply]`. Conclude with `⟨(W.N T).smul_mem _ hy, by rw [smul_smul, letE_sq]⟩`.
-/
theorem of_mem_Nl {i : ZMod n} {x : W.DD T} (hx : x ∈ W.Nl T i) :
    x ∈ W.N T ∧ (letE i : LetA O n) • x = x := by
  obtain ⟨y, hy, rfl⟩ := hx
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  exact ⟨(W.N T).smul_mem _ hy, by rw [smul_smul, letE_sq]⟩

/- English proof (translation)
Establish `hw` using `hM x (mem_Nl W T hx hxi)`. Take `⟨u, hu, hcc⟩` from `qp_unit W hs hR`. Establish `e : Formalism.MainNotions.LiftingTheory.qp W ^ B • W.φD T x = u ^ B • (W.Q ^ B • W.φD T x)`. Rewrite using `[hu, mul_pow, mul_smul]`. Use `⟨e ▸ (W.N T).smul_mem _ hw, ?_⟩` and prove the remaining obligations.

Establish `hwl : (letE c : LetA O n) • (W.Q ^ B • W.φD T x) = W.Q ^ B • W.φD T x`. Rewrite using `[aself_comm W T, letter_phi W T c hxi]`. Rewrite using `[e, cmpD_smul_letter W T c (u ^ B) hw hwl]`. Establish `h1 : PowerSeries.constantCoeff ((u ^ B) c) = 1` using `by rw [Pi.pow_apply, map_pow, hcc, one_pow]`. Rewrite using `[h1, map_one, one_smul, Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hw, Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hx]`.

Conclude with `h3.2.2 ⟨x, hx⟩ B hw`.
-/
theorem cmp_qpphi [IsDomain O] (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) {c : ZMod n} {B : ℕ}
    (hM : ∀ z ∈ W.Nl T (c - 1), W.Q ^ B • W.φD T z ∈ W.N T) {x : W.DD T} (hx : x ∈ W.N T)
    (hxi : (letE (c - 1) : LetA O n) • x = x) :
    Formalism.MainNotions.LiftingTheory.qp W ^ B • W.φD T x ∈ W.N T ∧
      Formalism.MainNotions.ArcLiftingSetup.cmpD W T (Formalism.MainNotions.LiftingTheory.qp W ^ B • W.φD T x) =
        (PD.p : LL) ^ B • φVB PD (LL := LL) (V := T.V) (Formalism.MainNotions.ArcLiftingSetup.cmpD W T x) := by
  have hw := hM x (mem_Nl W T hx hxi)
  obtain ⟨u, hu, hcc⟩ := qp_unit W hs hR
  have e : Formalism.MainNotions.LiftingTheory.qp W ^ B • W.φD T x = u ^ B • (W.Q ^ B • W.φD T x) := by
    rw [hu, mul_pow, mul_smul]
  refine ⟨e ▸ (W.N T).smul_mem _ hw, ?_⟩
  have hwl : (letE c : LetA O n) • (W.Q ^ B • W.φD T x) = W.Q ^ B • W.φD T x := by
    rw [aself_comm W T, letter_phi W T c hxi]
  rw [e, cmpD_smul_letter W T c (u ^ B) hw hwl]
  have h1 : PowerSeries.constantCoeff ((u ^ B) c) = 1 := by rw [Pi.pow_apply, map_pow, hcc, one_pow]
  rw [h1, map_one, one_smul, Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hw,
    Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hx]
  exact h3.2.2 ⟨x, hx⟩ B hw

end D

section D1

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

/- English proof (translation)
Take `⟨u', hu', v', hv', huv⟩` from `Submodule.mem_sup.1 hX`. Take `⟨y₀, hy₀, rfl⟩` from `Submodule.mem_map.1 hu'`. Take `⟨z, hz, rfl⟩` from `Submodule.mem_map.1 hv'`. Establish `hy₀' : y₀ ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T c y₀` using `hy₀`. Establish `key : ∀ z ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.PhiPullΔ W T c, Formalism.MainNotions.LiftingTheory.qp W ^ B • z ∈ W.N T ∧ ∃ y ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1), Formalism.MainNotions.ArcLiftingSetup.cmpD W T (Formalism.MainNotion …` using `LL) (V := T.V) (Formalism.MainNotions.ArcLiftingSetup.cmpD W T y) := by`.

Introduce `z hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, x', hx', rfl⟩` from `hz`. Establish `hx'' : x' ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c - 1) x'` using `hx'`.

Take `⟨hN, hcmp⟩` from `cmp_qpphi W T hs hR h3 hM hx''.1 hx''.2.1`. Establish `e : Formalism.MainNotions.LiftingTheory.qp W ^ B • (a • W.φD T x') = a • (Formalism.MainNotions.LiftingTheory.qp W ^ B • W.φD T x')` using `aself_comm W T _ _ _`. Establish `hl : (letE c : LetA O n) • (Formalism.MainNotions.LiftingTheory.qp W ^ B • W.φD T x') = Formalism.MainNotions.LiftingTheory.qp W ^ B • W.φD T x'`. Rewrite using `[aself_comm W T, letter_phi W T c hx''.2.1]`. Use `⟨e ▸ (W.N T).smul_mem a hN, PowerSeries.constantCoeff (a c) • x', (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1)).smul_mem _ hx', ?_⟩` and prove the remaining obligations.

Rewrite using `[e, cmpD_smul_letter W T c a hN hl, hcmp, cmpD_osmul W T _ hx''.1, map_smul, smul_comm]`. Consider the case `zero`. Use `⟨by rw [smul_zero]; exact (W.N T).zero_mem, 0, (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1)).zero_mem, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_zero, cmpD_zero W T, map_zero, smul_zero]`. Consider the case `add z₁ z₂ _ _ h₁ h₂`.

Take `⟨hN₁, y₁, hy₁, e₁⟩` from `h₁`. Take `⟨hN₂, y₂, hy₂, e₂⟩` from `h₂`. Use `⟨by rw [smul_add]; exact (W.N T).add_mem hN₁ hN₂, y₁ + y₂, (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1)).add_mem hy₁ hy₂, ?_⟩` and prove the remaining obligations. Establish `hy₁' : y₁ ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c - 1) y₁` using `hy₁`. Establish `hy₂' : y₂ ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c - 1) y₂` using `hy₂`.

Rewrite using `[smul_add, cmpD_add W T hN₁ hN₂, e₁, e₂, cmpD_add W T hy₁'.1 hy₂'.1, map_add, smul_add]`. Consider the case `smul o z _ h`. Take `⟨hN, y, hy, e⟩` from `h`. Establish `hy' : y ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c - 1) y` using `hy`. Establish `ec : Formalism.MainNotions.LiftingTheory.qp W ^ B • (o • z) = o • (Formalism.MainNotions.LiftingTheory.qp W ^ B • z)` using `osmul_comm W T _ _ _`.

Establish `hoN : o • (Formalism.MainNotions.LiftingTheory.qp W ^ B • z) ∈ W.N T`. Rewrite using `[← algebraMap_smul (LetA O n) o]`. Conclude with `(W.N T).smul_mem _ hN`. Use `⟨ec ▸ hoN, o • y, (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1)).smul_mem o hy, ?_⟩` and prove the remaining obligations. Rewrite using `[ec, cmpD_osmul W T o hN, e, cmpD_osmul W T o hy'.1, map_smul, smul_comm]`.

Take `⟨hN, y, hy, e⟩` from `key z hz`. Use `⟨y, hy, ?_⟩` and prove the remaining obligations. Rewrite using `[← huv]`. Simplify using `only [LinearMap.smul_apply, LinearMap.id_apply]`. Establish `hπN : W.π₀ • y₀ ∈ W.N T` using `(W.N T).smul_mem _ hy₀'.1`.

Rewrite using `[cmpD_add W T hπN hN, e, cmpD_smul_letter W T c W.π₀ hy₀'.1 hy₀'.2.1]`. Establish `h0 : PowerSeries.constantCoeff (W.π₀ c) = 0` using `Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_cc hR`. Rewrite using `[h0, map_zero, zero_smul, zero_add]`.
-/
theorem cmp_of_mem_X [IsDomain O] (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) {c : ZMod n} {B : ℕ}
    (hM : ∀ z ∈ W.Nl T (c - 1), W.Q ^ B • W.φD T z ∈ W.N T) {x : W.DD T}
    (hX : x ∈ (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T c).map (W.π₀ • (LinearMap.id : W.DD T →ₗ[O] W.DD T)) ⊔
      (Formalism.MainNotions.RamifiedCoefficientChains.S9.PhiPullΔ W T c).map
        ((Formalism.MainNotions.LiftingTheory.qp W ^ B) • (LinearMap.id : W.DD T →ₗ[O] W.DD T))) :
    ∃ y ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1), Formalism.MainNotions.ArcLiftingSetup.cmpD W T x =
      (PD.p : LL) ^ B • φVB PD (LL := LL) (V := T.V) (Formalism.MainNotions.ArcLiftingSetup.cmpD W T y) := by
  obtain ⟨u', hu', v', hv', huv⟩ := Submodule.mem_sup.1 hX
  obtain ⟨y₀, hy₀, rfl⟩ := Submodule.mem_map.1 hu'
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hv'
  have hy₀' : y₀ ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T c y₀ := hy₀
  have key : ∀ z ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.PhiPullΔ W T c, Formalism.MainNotions.LiftingTheory.qp W ^ B • z ∈ W.N T ∧
      ∃ y ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1), Formalism.MainNotions.ArcLiftingSetup.cmpD W T (Formalism.MainNotions.LiftingTheory.qp W ^ B • z) =
        (PD.p : LL) ^ B • φVB PD (LL := LL) (V := T.V) (Formalism.MainNotions.ArcLiftingSetup.cmpD W T y) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, ha, x', hx', rfl⟩ := hz
      have hx'' : x' ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c - 1) x' := hx'
      obtain ⟨hN, hcmp⟩ := cmp_qpphi W T hs hR h3 hM hx''.1 hx''.2.1
      have e : Formalism.MainNotions.LiftingTheory.qp W ^ B • (a • W.φD T x') = a • (Formalism.MainNotions.LiftingTheory.qp W ^ B • W.φD T x') :=
        aself_comm W T _ _ _
      have hl : (letE c : LetA O n) • (Formalism.MainNotions.LiftingTheory.qp W ^ B • W.φD T x') =
          Formalism.MainNotions.LiftingTheory.qp W ^ B • W.φD T x' := by
        rw [aself_comm W T, letter_phi W T c hx''.2.1]
      refine ⟨e ▸ (W.N T).smul_mem a hN, PowerSeries.constantCoeff (a c) • x',
        (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1)).smul_mem _ hx', ?_⟩
      rw [e, cmpD_smul_letter W T c a hN hl, hcmp, cmpD_osmul W T _ hx''.1, map_smul, smul_comm]
    | zero =>
      refine ⟨by rw [smul_zero]; exact (W.N T).zero_mem, 0, (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1)).zero_mem, ?_⟩
      rw [smul_zero, cmpD_zero W T, map_zero, smul_zero]
    | add z₁ z₂ _ _ h₁ h₂ =>
      obtain ⟨hN₁, y₁, hy₁, e₁⟩ := h₁
      obtain ⟨hN₂, y₂, hy₂, e₂⟩ := h₂
      refine ⟨by rw [smul_add]; exact (W.N T).add_mem hN₁ hN₂, y₁ + y₂,
        (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1)).add_mem hy₁ hy₂, ?_⟩
      have hy₁' : y₁ ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c - 1) y₁ := hy₁
      have hy₂' : y₂ ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c - 1) y₂ := hy₂
      rw [smul_add, cmpD_add W T hN₁ hN₂, e₁, e₂, cmpD_add W T hy₁'.1 hy₂'.1, map_add, smul_add]
    | smul o z _ h =>
      obtain ⟨hN, y, hy, e⟩ := h
      have hy' : y ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c - 1) y := hy
      have ec : Formalism.MainNotions.LiftingTheory.qp W ^ B • (o • z) = o • (Formalism.MainNotions.LiftingTheory.qp W ^ B • z) := osmul_comm W T _ _ _
      have hoN : o • (Formalism.MainNotions.LiftingTheory.qp W ^ B • z) ∈ W.N T := by
        rw [← algebraMap_smul (LetA O n) o]; exact (W.N T).smul_mem _ hN
      refine ⟨ec ▸ hoN, o • y, (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1)).smul_mem o hy, ?_⟩
      rw [ec, cmpD_osmul W T o hN, e, cmpD_osmul W T o hy'.1, map_smul, smul_comm]
  obtain ⟨hN, y, hy, e⟩ := key z hz
  refine ⟨y, hy, ?_⟩
  rw [← huv]
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  have hπN : W.π₀ • y₀ ∈ W.N T := (W.N T).smul_mem _ hy₀'.1
  rw [cmpD_add W T hπN hN, e, cmpD_smul_letter W T c W.π₀ hy₀'.1 hy₀'.2.1]
  have h0 : PowerSeries.constantCoeff (W.π₀ c) = 0 := Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_cc hR
  rw [h0, map_zero, zero_smul, zero_add]

/- English proof (translation)
Establish `hy' : y ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c - 1) y` using `hy`. Establish `hsp` using `hU y (mem_Nl W T hy'.1 hy'.2.1)`. Establish `key : ∀ z ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1 - 1)), (letE (c - 1) : LetA O n) • z = z ∧ W.Q ^ η' • z ∈ W.N T ∧ ∃ y₂ ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1), Formalism.MainNotions.ArcLiftingSetup.cmpD W T (W.Q ^ …` using `LL) (V := T.V) (Formalism.MainNotions.ArcLiftingSetup.cmpD W T y₂) := by`. Introduce `z hz`. Proceed by induction on `hz using Submodule.span_induction with`.

Consider the case `mem z hz`. Take `⟨x, hxNl, rfl⟩` from `hz`. Take `⟨hxN, hxl⟩` from `of_mem_Nl W T hxNl`. Establish `hw` using `hM' x hxNl`. Take `⟨x', hx', ex⟩` from `cmpD_mem_NDl W T (c - 1 - 1) hmod hxN hxl`.

Use `⟨letter_phi W T (c - 1) hxl, hw, x', hx', ?_⟩` and prove the remaining obligations. Rewrite using `[Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hw, ← ex, Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hxN]`. Conclude with `h3.2.2 ⟨x, hxN⟩ η' hw`. Consider the case `zero`. Use `⟨smul_zero _, by rw [smul_zero]; exact (W.N T).zero_mem, 0, (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1)).zero_mem, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_zero, cmpD_zero W T, map_zero, smul_zero]`. Consider the case `add z₁ z₂ _ _ h₁ h₂`. Take `⟨hl₁, hN₁, y₁, hy₁, e₁⟩` from `h₁`. Take `⟨hl₂, hN₂, y₂, hy₂, e₂⟩` from `h₂`. Establish `hy₁' : y₁ ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c - 1 - 1) y₁` using `hy₁`.

Establish `hy₂' : y₂ ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c - 1 - 1) y₂` using `hy₂`. Use `⟨by rw [smul_add, hl₁, hl₂], by rw [smul_add]; exact (W.N T).add_mem hN₁ hN₂, y₁ + y₂, (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1)).add_mem hy₁ hy₂, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add, cmpD_add W T hN₁ hN₂, e₁, e₂, cmpD_add W T hy₁'.1 hy₂'.1, map_add, smul_add]`. Consider the case `smul a z _ h`. Take `⟨hl, hN, y₂, hy₂, e⟩` from `h`.

Establish `hy₂' : y₂ ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c - 1 - 1) y₂` using `hy₂`. Establish `ec : W.Q ^ η' • (a • z) = a • (W.Q ^ η' • z)` using `aself_comm W T _ _ _`. Establish `hlw : (letE (c - 1) : LetA O n) • (W.Q ^ η' • z) = W.Q ^ η' • z`. Rewrite using `[aself_comm W T, hl]`. Use `⟨by rw [aself_comm W T, hl], ec ▸ (W.N T).smul_mem a hN, PowerSeries.constantCoeff (a (c - 1)) • y₂, (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1)).smul_mem _ hy₂, ?_⟩` and prove the remaining obligations.

Rewrite using `[ec, cmpD_smul_letter W T (c - 1) a hN hlw, e, cmpD_osmul W T _ hy₂'.1, map_smul, smul_comm]`. Take `⟨-, hN, y₂, hy₂, e⟩` from `key _ hsp`. Use `⟨y₂, hy₂, ?_⟩` and prove the remaining obligations. Establish `h2 : Formalism.MainNotions.ArcLiftingSetup.cmpD W T (W.Q ^ η' • (W.Q ^ h' • y)) = (PD.p : LL) ^ η' • ((PD.p : LL) ^ h' • Formalism.MainNotions.ArcLiftingSetup.cmpD W T y)`. Rewrite using `[smul_smul, ← pow_add, cmpD_smul_letter W T (c - 1) _ hy'.1 hy'.2.1, Pi.pow_apply, map_pow, cc_Q W hs, map_pow, map_natCast, pow_add, mul_smul]`.

Rewrite `h2` using `[e]`. Conclude with `((smul_right_injective _ (pow_ne_zero η' (Formalism.MainNotions.UnusedSlot80.ArcF.p_ne_zero W))) h2).symm`.
-/
theorem cmp_up [IsDomain O] (hs : W.s = 1) (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T)
    (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) {c : ZMod n} {h' η' : ℕ}
    (hU : ∀ y ∈ W.Nl T (c - 1), W.Q ^ h' • y ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1 - 1)))
    (hM' : ∀ z ∈ W.Nl T (c - 1 - 1), W.Q ^ η' • W.φD T z ∈ W.N T) {y : W.DD T}
    (hy : y ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1)) :
    ∃ y₂ ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1), (PD.p : LL) ^ h' • Formalism.MainNotions.ArcLiftingSetup.cmpD W T y =
      φVB PD (LL := LL) (V := T.V) (Formalism.MainNotions.ArcLiftingSetup.cmpD W T y₂) := by
  have hy' : y ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c - 1) y := hy
  have hsp := hU y (mem_Nl W T hy'.1 hy'.2.1)
  have key : ∀ z ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1 - 1)),
      (letE (c - 1) : LetA O n) • z = z ∧ W.Q ^ η' • z ∈ W.N T ∧
      ∃ y₂ ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1), Formalism.MainNotions.ArcLiftingSetup.cmpD W T (W.Q ^ η' • z) =
        (PD.p : LL) ^ η' • φVB PD (LL := LL) (V := T.V) (Formalism.MainNotions.ArcLiftingSetup.cmpD W T y₂) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, hxNl, rfl⟩ := hz
      obtain ⟨hxN, hxl⟩ := of_mem_Nl W T hxNl
      have hw := hM' x hxNl
      obtain ⟨x', hx', ex⟩ := cmpD_mem_NDl W T (c - 1 - 1) hmod hxN hxl
      refine ⟨letter_phi W T (c - 1) hxl, hw, x', hx', ?_⟩
      rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hw, ← ex, Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hxN]
      exact h3.2.2 ⟨x, hxN⟩ η' hw
    | zero =>
      refine ⟨smul_zero _, by rw [smul_zero]; exact (W.N T).zero_mem, 0,
        (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1)).zero_mem, ?_⟩
      rw [smul_zero, cmpD_zero W T, map_zero, smul_zero]
    | add z₁ z₂ _ _ h₁ h₂ =>
      obtain ⟨hl₁, hN₁, y₁, hy₁, e₁⟩ := h₁
      obtain ⟨hl₂, hN₂, y₂, hy₂, e₂⟩ := h₂
      have hy₁' : y₁ ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c - 1 - 1) y₁ := hy₁
      have hy₂' : y₂ ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c - 1 - 1) y₂ := hy₂
      refine ⟨by rw [smul_add, hl₁, hl₂], by rw [smul_add]; exact (W.N T).add_mem hN₁ hN₂, y₁ + y₂,
        (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1)).add_mem hy₁ hy₂, ?_⟩
      rw [smul_add, cmpD_add W T hN₁ hN₂, e₁, e₂, cmpD_add W T hy₁'.1 hy₂'.1, map_add, smul_add]
    | smul a z _ h =>
      obtain ⟨hl, hN, y₂, hy₂, e⟩ := h
      have hy₂' : y₂ ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c - 1 - 1) y₂ := hy₂
      have ec : W.Q ^ η' • (a • z) = a • (W.Q ^ η' • z) := aself_comm W T _ _ _
      have hlw : (letE (c - 1) : LetA O n) • (W.Q ^ η' • z) = W.Q ^ η' • z := by
        rw [aself_comm W T, hl]
      refine ⟨by rw [aself_comm W T, hl], ec ▸ (W.N T).smul_mem a hN,
        PowerSeries.constantCoeff (a (c - 1)) • y₂,
        (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1)).smul_mem _ hy₂, ?_⟩
      rw [ec, cmpD_smul_letter W T (c - 1) a hN hlw, e, cmpD_osmul W T _ hy₂'.1, map_smul, smul_comm]
  obtain ⟨-, hN, y₂, hy₂, e⟩ := key _ hsp
  refine ⟨y₂, hy₂, ?_⟩
  have h2 : Formalism.MainNotions.ArcLiftingSetup.cmpD W T (W.Q ^ η' • (W.Q ^ h' • y)) =
      (PD.p : LL) ^ η' • ((PD.p : LL) ^ h' • Formalism.MainNotions.ArcLiftingSetup.cmpD W T y) := by
    rw [smul_smul, ← pow_add, cmpD_smul_letter W T (c - 1) _ hy'.1 hy'.2.1, Pi.pow_apply, map_pow,
      cc_Q W hs, map_pow, map_natCast, pow_add, mul_smul]
  rw [e] at h2
  exact ((smul_right_injective _ (pow_ne_zero η' (Formalism.MainNotions.UnusedSlot80.ArcF.p_ne_zero W))) h2).symm

end D1

end Formalism.MainNotions.N.Pv.LocalLengthBound
