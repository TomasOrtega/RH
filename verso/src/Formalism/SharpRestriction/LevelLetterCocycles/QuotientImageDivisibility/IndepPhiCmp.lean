import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.HasSubstPi0Series

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section PhiInj

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

/- English proof (translation)
Establish `h : ∀ y, φVB PD (LL` using `LL) (V := V) y = ((PD.φ.toLinearMap).lTensor V) y := fun y => by`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x b => simp [φVB]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.

Introduce `a b hab`. Rewrite `hab` using `[h, h]`. Conclude with `Module.Flat.lTensor_preserves_injective_linearMap _ PD.φ_inj hab`.
-/
theorem φVB_inj : Function.Injective (φVB PD (LL := LL) (V := V)) := by
  have h : ∀ y, φVB PD (LL := LL) (V := V) y = ((PD.φ.toLinearMap).lTensor V) y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp [φVB]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  intro a b hab
  rw [h, h] at hab
  exact Module.Flat.lTensor_preserves_injective_linearMap _ PD.φ_inj hab

end PhiInj

section CritB2

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O]
    [Algebra Zl Ai] {RW : Type} [CommRing RW] [Algebra O RW] {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW}
    {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}

/- English proof (translation)
Establish `h0 : (1 : LetA O n) • (0 : W.DD T) ∈ W.N T` using `by rw [smul_zero]; exact (W.N T).zero_mem`. Use `⟨⟨0, fun _ _ => rfl⟩, 1, h0, by rw [map_one]; exact one_ne_zero, fun k => ?_⟩` and prove the remaining obligations. Establish `e : (⟨(1 : LetA O n) • (0 : W.DD T), h0⟩ : ↥(W.N T)) = 0` using `Subtype.ext (smul_zero _)`. Rewrite using `[e, map_zero, conv_eq]`. Simplify using `[smulS]`.
-/
theorem isExp_zero (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ (0 : W.DD T) (fun _ => 0) := by
  have h0 : (1 : LetA O n) • (0 : W.DD T) ∈ W.N T := by rw [smul_zero]; exact (W.N T).zero_mem
  refine ⟨⟨0, fun _ _ => rfl⟩, 1, h0, by rw [map_one]; exact one_ne_zero, fun k => ?_⟩
  have e : (⟨(1 : LetA O n) • (0 : W.DD T), h0⟩ : ↥(W.N T)) = 0 := Subtype.ext (smul_zero _)
  rw [e, map_zero, conv_eq]
  simp [smulS]

/- English proof (translation)
Establish `hs : W.s = 1` using `hA.2.1`. Take `⟨hN, hAg⟩` from `gam_of_tie W hs C`. Take `⟨-, -, hAdd, -, -, -, -⟩` from `expRules_of W h4 hN hAg hA T hT i ζ hζ`. Introduce `x hx`. Unfold `Formalism.MainNotions.CrystallineLiftingInputs.pullJ at hx`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨y, ⟨hy, hyD⟩, rfl⟩` from `hx`. Rewrite using `[pow_one]`. Take `⟨d, hd, hn, -⟩` from `phi_exp W hs C h4W T hT i hζ y hy hyD.1`.

Conclude with `⟨d, hd, hn⟩`. Consider the case `zero => exact ⟨fun _ => 0, isExp_zero W T i ζ, fun _ _ => rfl⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨d, hd, hn⟩` from `hx`. Take `⟨e, he, hn'⟩` from `hy`.

Conclude with `⟨d + e, hAdd _ _ _ _ hd he, fun k hk => by simp [hn k hk, hn' k hk]⟩`. Consider the case `smul a x _ hx`. Take `⟨d, hd, hn⟩` from `hx`. Conclude with `⟨smulS (W.lev i ζ a) d, isExp_smulA W T i ζ hd a, fun k hk => LB_smulS hn _ k hk⟩`.
-/
theorem pullJ_exp (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (h4 : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W) (C : CmpTie W E ιdR p1 tS zS)
    {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (h4W : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n) {ζ : LL} (hζ : IsPrimitiveRoot ζ PD.p) :
    ∀ x ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T (i - 1) 1, ∃ d : ℤ → T.V ⊗[Qp] BdR,
      Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ x d ∧ ∀ k : ℤ, k < 0 → d k = 0 := by
  have hs : W.s = 1 := hA.2.1
  obtain ⟨hN, hAg⟩ := gam_of_tie W hs C
  obtain ⟨-, -, hAdd, -, -, -, -⟩ := expRules_of W h4 hN hAg hA T hT i ζ hζ
  intro x hx
  unfold Formalism.MainNotions.CrystallineLiftingInputs.pullJ at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, ⟨hy, hyD⟩, rfl⟩ := hx
    rw [pow_one]
    obtain ⟨d, hd, hn, -⟩ := phi_exp W hs C h4W T hT i hζ y hy hyD.1
    exact ⟨d, hd, hn⟩
  | zero => exact ⟨fun _ => 0, isExp_zero W T i ζ, fun _ _ => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨d, hd, hn⟩ := hx
    obtain ⟨e, he, hn'⟩ := hy
    exact ⟨d + e, hAdd _ _ _ _ hd he, fun k hk => by simp [hn k hk, hn' k hk]⟩
  | smul a x _ hx =>
    obtain ⟨d, hd, hn⟩ := hx
    exact ⟨smulS (W.lev i ζ a) d, isExp_smulA W T i ζ hd a, fun k hk => LB_smulS hn _ k hk⟩

/- English proof (translation)
Use `haveI := hdom`. Use `haveI : Nontrivial O := (algebraMap O LL).domain_nontrivial`. Establish `hsum : ∑ m, c m • W.cmp T ⟨e m, (he.1 m).1⟩ = 0`. Apply `φVB_inj PD (LL := LL) (V := T.V)` to reduce the goal to its premises. Apply `Formalism.MainNotions.UnusedSlot80.LevR.ιV_inj (PD := PD) (LL := LL) (V := T.V)` to reduce the goal to its premises.

Rewrite using `[map_zero, map_zero, map_sum, map_sum]`. Simplify `hc` using `[map_smul]`. Take `⟨⟨dd, hdd⟩, hint⟩` from `IsLocalization.exist_integer_multiples (nonZeroDivisors O) (Finset.univ : Finset (Fin r)) c`. Use `choose o ho using fun m => hint m (Finset.mem_univ m)`. Establish `hdne : algebraMap O LL dd ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hdd`.

Use `set z : W.DD T := ∑ m, o m • e m with hz`. Establish `hzN : z ∈ W.N T` using `Submodule.sum_mem _ fun m _ => by`. Rewrite using `[← algebraMap_smul (LetA O n) (o m) (e m)]`. Conclude with `(W.N T).smul_mem _ (he.1 m).1`. Establish `hzD : Formalism.MainNotions.CrystallineLiftingInputs.DL W T i z`.

Use `⟨?_, fun δ hδ => ?_⟩` and prove the remaining obligations. Rewrite using `[hz, Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun m _ => by rw [smul_comm, (he.1 m).2.1]`. Rewrite using `[hz, map_sum]`. Conclude with `Finset.sum_congr rfl fun m _ => by rw [map_smul, (he.1 m).2.2 δ hδ]`.

Establish `hcz : W.cmp T ⟨z, hzN⟩ = 0`. Establish `e1 : (⟨z, hzN⟩ : ↥(W.N T)) = ∑ m, o m • (⟨e m, (he.1 m).1⟩ : ↥(W.N T))` using `Subtype.ext (by simp [hz, Submodule.coe_sum])`. Rewrite using `[e1, map_sum]`. Simplify using `only [W.cmp_smul]`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[ho m, Algebra.smul_def, mul_smul]`. Use `_ = 0 := by rw [← Finset.smul_sum, hsum, smul_zero]`. Establish `hPN` using `ker_NDl W T i h3 hmod hR (x := z) ⟨hzN, hzD⟩ (by unfold Formalism.MainNotions.ArcLiftingSetup.cmpD; rw [dif_pos hzN]; exact hcz)`. Take `⟨y, hy, hyΔ, hzy⟩` from `hPN`.

Rewrite `hzy` using `[pow_one]`. Establish `hyl : (letE i : LetA O n) • y = y`. Apply `RL.pi0_pow_smul_injective W T hR.2.2.1 1` to reduce the goal to its premises. Rewrite using `[pow_one, smul_comm, ← hzy, hzD.1]`. Take `⟨b, hb, -⟩` from `he.2 y hy ⟨hyl, hyΔ⟩`.

Establish `rep1 : z = ∑ m, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (PowerSeries.C (o m)) • e m`. Rewrite using `[hz]`. Conclude with `Finset.sum_congr rfl fun m _ => by rw [evalZero_C, algebraMap_smul]`. Establish `rep2 : z = ∑ m, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (PowerSeries.X * b m) • e m`. Rewrite using `[hzy, hb, Finset.smul_sum]`.

Conclude with `Finset.sum_congr rfl fun m _ => by rw [smul_smul, evalZero_mul W hR, evalZero_X_eq_pi0 W hR]`. Establish `heq` using `(he.2 z hzN hzD).unique rep1 rep2`. Use function extensionality and compare the values at `m`. Establish `h0 : o m = 0`. Use `congrArg (fun f => PowerSeries.constantCoeff (f m)) heq` as an intermediate fact.

Simplify using `using this`. Establish `: algebraMap O LL dd * c m = 0`. Rewrite using `[← Algebra.smul_def, ← ho m, h0, map_zero]`. Conclude with `(mul_eq_zero.1 this).resolve_left hdne`.
-/
theorem indep_phi_cmp (hdom : IsDomain O) (hFr : IsFractionRing O LL)
    (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (T : LocLat G Qp LL O) (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T)
    (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (i : ZMod n) {r : ℕ} (e : Fin r → W.DD T)
    (he : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsBas W T i e) (c : Fin r → LL)
    (hc : ∑ m, c m • ιV PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V)
      (W.cmp T ⟨e m, (he.1 m).1⟩)) = 0) : c = 0 := by
  haveI := hdom
  haveI : Nontrivial O := (algebraMap O LL).domain_nontrivial
  have hsum : ∑ m, c m • W.cmp T ⟨e m, (he.1 m).1⟩ = 0 := by
    apply φVB_inj PD (LL := LL) (V := T.V)
    apply Formalism.MainNotions.UnusedSlot80.LevR.ιV_inj (PD := PD) (LL := LL) (V := T.V)
    rw [map_zero, map_zero, map_sum, map_sum]
    simpa [map_smul] using hc
  obtain ⟨⟨dd, hdd⟩, hint⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O)
    (Finset.univ : Finset (Fin r)) c
  choose o ho using fun m => hint m (Finset.mem_univ m)
  have hdne : algebraMap O LL dd ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hdd
  set z : W.DD T := ∑ m, o m • e m with hz
  have hzN : z ∈ W.N T := Submodule.sum_mem _ fun m _ => by
    rw [← algebraMap_smul (LetA O n) (o m) (e m)]; exact (W.N T).smul_mem _ (he.1 m).1
  have hzD : Formalism.MainNotions.CrystallineLiftingInputs.DL W T i z := by
    refine ⟨?_, fun δ hδ => ?_⟩
    · rw [hz, Finset.smul_sum]
      exact Finset.sum_congr rfl fun m _ => by rw [smul_comm, (he.1 m).2.1]
    · rw [hz, map_sum]
      exact Finset.sum_congr rfl fun m _ => by rw [map_smul, (he.1 m).2.2 δ hδ]
  have hcz : W.cmp T ⟨z, hzN⟩ = 0 := by
    have e1 : (⟨z, hzN⟩ : ↥(W.N T)) = ∑ m, o m • (⟨e m, (he.1 m).1⟩ : ↥(W.N T)) :=
      Subtype.ext (by simp [hz, Submodule.coe_sum])
    rw [e1, map_sum]
    simp only [W.cmp_smul]
    calc ∑ m, algebraMap O LL (o m) • W.cmp T ⟨e m, (he.1 m).1⟩
        = ∑ m, algebraMap O LL dd • (c m • W.cmp T ⟨e m, (he.1 m).1⟩) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [ho m, Algebra.smul_def, mul_smul]
      _ = 0 := by rw [← Finset.smul_sum, hsum, smul_zero]
  have hPN := ker_NDl W T i h3 hmod hR (x := z) ⟨hzN, hzD⟩
    (by unfold Formalism.MainNotions.ArcLiftingSetup.cmpD; rw [dif_pos hzN]; exact hcz)
  obtain ⟨y, hy, hyΔ, hzy⟩ := hPN
  rw [pow_one] at hzy
  have hyl : (letE i : LetA O n) • y = y := by
    apply RL.pi0_pow_smul_injective W T hR.2.2.1 1
    rw [pow_one, smul_comm, ← hzy, hzD.1]
  obtain ⟨b, hb, -⟩ := he.2 y hy ⟨hyl, hyΔ⟩
  have rep1 : z = ∑ m, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (PowerSeries.C (o m)) • e m := by
    rw [hz]
    exact Finset.sum_congr rfl fun m _ => by rw [evalZero_C, algebraMap_smul]
  have rep2 : z = ∑ m, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (PowerSeries.X * b m) • e m := by
    rw [hzy, hb, Finset.smul_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [smul_smul, evalZero_mul W hR, evalZero_X_eq_pi0 W hR]
  have heq := (he.2 z hzN hzD).unique rep1 rep2
  funext m
  have h0 : o m = 0 := by
    have := congrArg (fun f => PowerSeries.constantCoeff (f m)) heq
    simpa using this
  have : algebraMap O LL dd * c m = 0 := by
    rw [← Algebra.smul_def, ← ho m, h0, map_zero]
  exact (mul_eq_zero.1 this).resolve_left hdne

end CritB2

end Formalism.MainNotions.N.Pv.LocalLengthBound
