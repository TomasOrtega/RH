import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.AboveWeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WStmtxx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocCompC
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WinConv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAboveW
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EqOneOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSatLoc

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Win UpperTheory.GalN.V
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
/- English proof (translation)
Establish `h0 : (x ^ a) ^ b = (y ^ a * c ^ a) ^ b`. Rewrite using `[pow_right_comm, h, pow_right_comm, mul_pow y c a]`. Rewrite `h0` using `[hx, hy]`. Simplify using `only [← zpow_natCast, ← zpow_mul, ← zpow_add] at h0`. Establish `h1 : c ^ (p * a * b - (q * a + a) * b) = 1`.

Rewrite using `[zpow_sub, h0, mul_inv_cancel]`. Establish `hne : p * a * b - (q * a + a) * b ≠ 0`. Establish `e : p * a * b - (q * a + a) * b = (p - (q + 1)) * a * b` using `by ring`. Rewrite using `[e]`. Establish `h2 : p - (q + 1) ≠ 0` using `sub_ne_zero.2 hpq`.

Establish `h3 : (a : ℤ) ≠ 0` using `by exact_mod_cast ha.ne'`. Establish `h4 : (b : ℤ) ≠ 0` using `by exact_mod_cast hb.ne'`. Conclude with `mul_ne_zero (mul_ne_zero h2 h3) h4`. Conclude with `hinf _ (Int.natAbs_ne_zero.2 hne) (pow_natAbs_eq_one.2 h1)`.
-/
private theorem flag_exp {U : Type} [CommGroup U] (x y c : U) (a b : ℕ) (p q : ℤ) (ha : 0 < a) (hb : 0 < b)
    (hpq : p ≠ q + 1) (hinf : ∀ k : ℕ, k ≠ 0 → c ^ k ≠ 1)
    (hx : x ^ a = (c ^ p) ^ a) (hy : y ^ a = (c ^ q) ^ a) (h : x ^ b = (y * c) ^ b) : False := by
  have h0 : (x ^ a) ^ b = (y ^ a * c ^ a) ^ b := by
    rw [pow_right_comm, h, pow_right_comm, mul_pow y c a]
  rw [hx, hy] at h0
  simp only [← zpow_natCast, ← zpow_mul, ← zpow_add] at h0
  have h1 : c ^ (p * a * b - (q * a + a) * b) = 1 := by
    rw [zpow_sub, h0, mul_inv_cancel]
  have hne : p * a * b - (q * a + a) * b ≠ 0 := by
    have e : p * a * b - (q * a + a) * b = (p - (q + 1)) * a * b := by ring
    rw [e]
    have h2 : p - (q + 1) ≠ 0 := sub_ne_zero.2 hpq
    have h3 : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
    have h4 : (b : ℤ) ≠ 0 := by exact_mod_cast hb.ne'
    exact mul_ne_zero (mul_ne_zero h2 h3) h4
  exact hinf _ (Int.natAbs_ne_zero.2 hne) (pow_natAbs_eq_one.2 h1)
/- English proof (translation)
Establish `key : ∀ i j : ℕ, i < j → (∀ x : F, (σ ^ i) (algebraMap F Ω x) = (σ ^ j) (algebraMap F Ω x)) → ∃ n : ℕ, 0 < n ∧ ∀ x : F, (σ ^ n) (algebraMap F Ω x) = algebraMap F Ω x`. Introduce `i j hij h`. Use `⟨j - i, by omega, fun x => (σ ^ i).injective ?_⟩` and prove the remaining obligations. Establish `e : σ ^ j = σ ^ i * σ ^ (j - i)` using `by rw [← pow_add]; congr 1; omega`. Rewrite using `[h x, e]`.

Both sides reduce to the same expression. Set `e : F →ₐ[ℚ] Ω` to `IsScalarTower.toAlgHom ℚ F Ω`. Set `f : ℕ → (F →ₐ[ℚ] Ω)` to `fun k => ((σ ^ k : G ℚ Ω) : Ω →ₐ[ℚ] Ω).comp e`. Take `⟨i, j, hij, hf⟩` from `Finite.exists_ne_map_eq_of_infinite f`. Break down `lt_or_gt_of_ne hij with h | h` into its components or cases.

Conclude with `key i j h fun x => DFunLike.congr_fun hf x`. Conclude with `key j i h fun x => (DFunLike.congr_fun hf x).symm`.
-/
private theorem pow_fix {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [Algebra ℚ Ω] [IsScalarTower ℚ F Ω]
    (σ : G ℚ Ω) : ∃ n : ℕ, 0 < n ∧ ∀ x : F, (σ ^ n) (algebraMap F Ω x) = algebraMap F Ω x := by
  have key : ∀ i j : ℕ, i < j → (∀ x : F, (σ ^ i) (algebraMap F Ω x) = (σ ^ j) (algebraMap F Ω x)) →
      ∃ n : ℕ, 0 < n ∧ ∀ x : F, (σ ^ n) (algebraMap F Ω x) = algebraMap F Ω x := by
    intro i j hij h
    refine ⟨j - i, by omega, fun x => (σ ^ i).injective ?_⟩
    have e : σ ^ j = σ ^ i * σ ^ (j - i) := by rw [← pow_add]; congr 1; omega
    rw [h x, e]
    rfl
  let e : F →ₐ[ℚ] Ω := IsScalarTower.toAlgHom ℚ F Ω
  let f : ℕ → (F →ₐ[ℚ] Ω) := fun k => ((σ ^ k : G ℚ Ω) : Ω →ₐ[ℚ] Ω).comp e
  obtain ⟨i, j, hij, hf⟩ := Finite.exists_ne_map_eq_of_infinite f
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h fun x => DFunLike.congr_fun hf x
  · exact key j i h fun x => (DFunLike.congr_fun hf x).symm
/- English proof (translation)
Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective`. Use `haveI : IsAlgClosure ℚ Ω := ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.trans ℚ F Ω⟩`. Establish `hu : IsUnit ((l + 1 : ℕ) : ℤ_[l])`. Rewrite using `[PadicInt.isUnit_iff]`. Conclude with `PadicInt.norm_natCast_eq_one_iff.2 (by simp)`.

Take `⟨σ, hσ, he⟩` from `GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA hu.unit`. Take `⟨n, hn, hfix⟩` from `pow_fix (F := F) σ`. Set `τ : G F Ω` to `AlgEquiv.ofRingEquiv (f := (σ ^ n).toRingEquiv) hfix`. Establish `hτ : τ.restrictScalars ℚ = σ ^ n` using `by ext x; rfl`. Establish `hmem : τ ∈ Ine (F` using `F) A := by`.

Establish `h1 : τ.restrictScalars ℚ ∈ Ine (F` using `ℚ) A := by rw [hτ]; exact pow_mem hσ n`. Conclude with `h1`. Establish `hz : cycZ F Ω l τ = hu.unit ^ n`. Establish `h1 : cycZ ℚ Ω l (τ.restrictScalars ℚ) = cycZ F Ω l τ` using `rfl`. Rewrite using `[← h1, hτ, map_pow, he]`.

Use `⟨τ, hmem, fun k hk h => ?_⟩` and prove the remaining obligations. Establish `h2 : ((cycBar F Ω l τ : (Qbar l)ˣ) : Qbar l) = ((l + 1 : ℕ) : Qbar l) ^ n`. Express the relevant statement in the definitionally equal form `algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ F Ω l τ : ℤ_[l]ˣ) : ℤ_[l])) = _`. Rewrite using `[hz, Units.val_pow_eq_pow_val, hu.unit_spec, map_pow, map_pow, map_natCast, map_natCast]`. Establish `h3` using `congrArg Units.val h`.

Rewrite `h3` using `[Units.val_pow_eq_pow_val, h2, Units.val_one, ← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_eq_one, Nat.pow_eq_one]`. Use `hl.out.pos` as an intermediate fact. Break down `h3 with h3 | h3` into its components or cases. Rewrite `h3` using `[Nat.pow_eq_one]`. Use linear arithmetic over natural numbers and integers.

Use linear arithmetic over natural numbers and integers.
-/
private theorem cyc_inf_over (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [hl : Fact l.Prime] (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) :
    ∃ s ∈ Ine (F := F) A, ∀ k : ℕ, k ≠ 0 → cycBar F Ω l s ^ k ≠ 1 := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsAlgClosure ℚ Ω := ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.trans ℚ F Ω⟩
  have hu : IsUnit ((l + 1 : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    exact PadicInt.norm_natCast_eq_one_iff.2 (by simp)
  obtain ⟨σ, hσ, he⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA hu.unit
  obtain ⟨n, hn, hfix⟩ := pow_fix (F := F) σ
  let τ : G F Ω := AlgEquiv.ofRingEquiv (f := (σ ^ n).toRingEquiv) hfix
  have hτ : τ.restrictScalars ℚ = σ ^ n := by ext x; rfl
  have hmem : τ ∈ Ine (F := F) A := by
    have h1 : τ.restrictScalars ℚ ∈ Ine (F := ℚ) A := by rw [hτ]; exact pow_mem hσ n
    exact h1
  have hz : cycZ F Ω l τ = hu.unit ^ n := by
    have h1 : cycZ ℚ Ω l (τ.restrictScalars ℚ) = cycZ F Ω l τ := rfl
    rw [← h1, hτ, map_pow, he]
  refine ⟨τ, hmem, fun k hk h => ?_⟩
  have h2 : ((cycBar F Ω l τ : (Qbar l)ˣ) : Qbar l) = ((l + 1 : ℕ) : Qbar l) ^ n := by
    change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ F Ω l τ : ℤ_[l]ˣ) : ℤ_[l])) = _
    rw [hz, Units.val_pow_eq_pow_val, hu.unit_spec, map_pow, map_pow, map_natCast, map_natCast]
  have h3 := congrArg Units.val h
  rw [Units.val_pow_eq_pow_val, h2, Units.val_one, ← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_eq_one, Nat.pow_eq_one] at h3
  have := hl.out.pos
  rcases h3 with h3 | h3
  · rw [Nat.pow_eq_one] at h3
    omega
  · omega
/- English proof (translation)
Introduce `A hA`. Establish `hAl : A.valuation (l : Ω) < 1`. Establish `h1` using `(hA ((l : ℕ) : 𝓞 L)).2 hw`. Simplify using `using h1`. Take `⟨b, k, κ, hk, hflag, hκ⟩` from `H A hAl`.

Use `⟨κ, hflag, fun i j c hc h => ?_⟩` and prove the remaining obligations. Take `⟨s, hs, hinf⟩` from `cyc_inf_over L Ω l A hAl`. Set `t : ↥(Dec (F` to `L) A) := ⟨s, Ine_le_Dec A hs⟩`. Establish `h1 : κ i t ^ c = (κ j t * cycBar L Ω l s) ^ c` using `DFunLike.congr_fun h t`. Take `⟨h2, h3⟩` from `hκ t hs`.

Establish `he : ∀ i : Fin 2, κ i t ^ k = (cycBar L Ω l s ^ (![b + m, b] i)) ^ k` using `fun i => by fin_cases i`. Conclude with `h2`. Conclude with `h3`. Apply the tactic sequence `have hne : ∀ i j : Fin 2, ![b + (m : ℤ), b] i ≠ ![b + (m : ℤ), b] j + 1 := fun i j => by fin_cases i <;> fin_cases j <;> simp <;> omega`. Conclude with `flag_exp (κ i t) (κ j t) (cycBar L Ω l s) k c _ _ hk hc (hne i j) hinf (he i) (he j) h1`.
-/
private theorem pot_of_above {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {r : G L Ω →* GL (Fin 2) (Qbar l)} {m : ℕ} (hm : 2 ≤ m) {w : Plc L} (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal)
    (H : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 →
      ∃ (b : ℤ) (k : ℕ) (κ : Fin 2 → ↥(Dec (F := L) A) →* (Qbar l)ˣ), 0 < k ∧ IsFlagOn r (Dec (F := L) A) κ ∧
        ∀ s : ↥(Dec (F := L) A), (s : G L Ω) ∈ Ine (F := L) A →
          κ 0 s ^ k = (cycBar L Ω l s ^ (b + m)) ^ k ∧ κ 1 s ^ k = (cycBar L Ω l s ^ b) ^ k) : PotUnl r w := by
  intro A hA
  have hAl : A.valuation (l : Ω) < 1 := by
    have h1 := (hA ((l : ℕ) : 𝓞 L)).2 hw
    simpa using h1
  obtain ⟨b, k, κ, hk, hflag, hκ⟩ := H A hAl
  refine ⟨κ, hflag, fun i j c hc h => ?_⟩
  obtain ⟨s, hs, hinf⟩ := cyc_inf_over L Ω l A hAl
  let t : ↥(Dec (F := L) A) := ⟨s, Ine_le_Dec A hs⟩
  have h1 : κ i t ^ c = (κ j t * cycBar L Ω l s) ^ c := DFunLike.congr_fun h t
  obtain ⟨h2, h3⟩ := hκ t hs
  have he : ∀ i : Fin 2, κ i t ^ k = (cycBar L Ω l s ^ (![b + m, b] i)) ^ k := fun i => by
    fin_cases i
    · exact h2
    · exact h3
  have hne : ∀ i j : Fin 2, ![b + (m : ℤ), b] i ≠ ![b + (m : ℤ), b] j + 1 := fun i j => by
    fin_cases i <;> fin_cases j <;> simp <;> omega
  exact flag_exp (κ i t) (κ j t) (cycBar L Ω l s) k c _ _ hk hc (hne i j) hinf (he i) (he j) h1
/- English proof (translation)
Take `⟨e, he⟩` from `GlobalTheory.locU_equiv_GL L n w hs`. Take `⟨hi, f, f0, fm, fe⟩` from `hτ`. Take `⟨z, hz, hfix⟩` from `hf`. Use `⟨f z, fm z, fun h0 => ?_, fun x hx hk => ?_⟩` and prove the remaining obligations. Set `K : Subrepresentation τ.ρ` to `⟨LinearMap.ker f, fun g v hv => by`.

Take `⟨x, rfl⟩ : ∃ x : locU n w, cLoc w (x : UA L n) = g` from `⟨e.symm g, (he _).symm.trans (e.apply_symm_apply g)⟩`. Rewrite `hv`, the goal using `[LinearMap.mem_ker]`. Conclude with `(fe x v).trans (by rw [hv, map_zero])⟩`. Break down `hi.eq_bot_or_eq_top K with hK | hK` into its components or cases. Establish `h1 : z ∈ K.toSubmodule` using `h0`.

Rewrite `h1` using `[hK]`. Conclude with `hz h1`. Use `f0 (LinearMap.ext fun v => ?_)` and prove the remaining obligations. Establish `h1 : v ∈ K.toSubmodule` using `by rw [hK]; trivial`. Conclude with `h1`.

Rewrite using `[← fe ⟨x, hx⟩ z]`. Conclude with `congrArg f (hfix _ hk)`.
-/
private theorem unr_of_comp {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w : Plc L}
    {σ : Submodule ℂ (UA L n → ℂ)} {τ : SmIrr (GL (Fin n) (Kw w))} (hs : IsSplitAt w) (hτ : Comp σ w τ)
    (hf : Af.HasFixed τ.ρ (GlobalTheory.LFun.KGL w n)) : IsUnramU σ w := by
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL L n w hs
  obtain ⟨hi, f, f0, fm, fe⟩ := hτ
  obtain ⟨z, hz, hfix⟩ := hf
  refine ⟨f z, fm z, fun h0 => ?_, fun x hx hk => ?_⟩
  · let K : Subrepresentation τ.ρ := ⟨LinearMap.ker f, fun g v hv => by
      obtain ⟨x, rfl⟩ : ∃ x : locU n w, cLoc w (x : UA L n) = g := ⟨e.symm g, (he _).symm.trans (e.apply_symm_apply g)⟩
      rw [LinearMap.mem_ker] at hv ⊢
      exact (fe x v).trans (by rw [hv, map_zero])⟩
    rcases hi.eq_bot_or_eq_top K with hK | hK
    · have h1 : z ∈ K.toSubmodule := h0
      rw [hK] at h1
      exact hz h1
    · refine f0 (LinearMap.ext fun v => ?_)
      have h1 : v ∈ K.toSubmodule := by rw [hK]; trivial
      exact h1
  · rw [← fe ⟨x, hx⟩ z]
    exact congrArg f (hfix _ hk)
/- English proof (translation)
Introduce `P L Ω _ _ _ _ _ _ l _ ι hl M m hM hlM hU r hr`. Establish `PA` using `P.af`. Establish `hc` using `hr.cont`. Take `⟨π, hreg, hd, hatt⟩` from `hr.aut`. Establish `hpol : ∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ`.

Use `⟨quadChar L ^ 2, fun v => ?_, ?_⟩` and prove the remaining obligations. Establish `e : (quadChar L ^ 2).locInf v (-1) = (quadChar L).locInf v (-1) ^ 2` using `rfl`. Rewrite using `[e, quadChar_locInf]`. Rewrite using `[map_pow, compNorm_quadChar, one_pow]`. Conclude with `(GlobalTheory.ContraPair.dualIsConjBy_one π).2 hd`.

Take `⟨HT, hwt, hLG⟩` from `P.compat L Ω l ι 2 one_le_two r π hc hreg hpol hatt`. Establish `hg : ∀ (w : Plc L) (A : ValuationSubring Ω) (hA : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion L) → WD hA), UpperTheory.Zero.LLC.IsRecT hA rc → ∀ τ, π.IsLocComp w τ → GlobalTheory.RoadU.PlainTor (IrrGL.of τ.ρ τ.smooth τ.irred) ∧ UpperTheory.GalStar.Tor (rc (algNorm τ)) ∧ (rc (a …` using `fun w A hA rc hrc τ hτ => guard_of P.plain hreg hatt hr.wit (by`. Distinguish the cases in `e : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal`. Conclude with `Or.inr (Or.inr (pot_of_above hr.gap e hr.above))`. Conclude with `Or.inl e) hrc hτ`.

Establish `hex : ∀ w : Plc L, ∃ τ, π.IsLocComp w τ` using `fun w => (_root_.UpperTheory.V.Af.local_comp_complex_of_printed_results PA L 2 π w).1`. Establish `hpt : ∀ (w : Plc L) τ, π.IsLocComp w τ → UpperTheory.V.Z.Sym.W.PT τ` using `fun w τ hτ => by`. Take `⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w` from `exists_isPlaceOver Ω w`. Take `⟨rc, hrc⟩` from `_root_.UpperTheory.V.Z.Win.exRec'_alt PA.litN hA`. Conclude with `(hg w A hA rc hrc τ hτ).1`.

Establish `hb : ∀ φ : L →+* Qbar l, ∃ b : ℤ, HT φ = {b, b + m}` using `fun φ => by`. Establish `hw : ((l : ℕ) : 𝓞 L) ∈ (GlobalTheory.EvExtend.placeOf φ).asIdeal`. Rewrite using `[GlobalTheory.EvExtend.mem_placeOf]`. Simplify using `using GlobalTheory.EvExtend.norm_natCast_lt_one (l := l)`. Take `⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A (GlobalTheory.EvExtend.placeOf φ)` from `exists_isPlaceOver Ω _`.

Establish `hAl : A.valuation (l : Ω) < 1` using `by simpa using (hA _).2 hw`. Take `⟨τ, hτ⟩` from `hex (GlobalTheory.EvExtend.placeOf φ)`. Take `⟨-, b, hb⟩` from `_root_.UpperTheory.V.Z.Sym.W.above_w_statement PA L Ω l ι hl r hc m hr.gap _ hw HT ((hLG _ _ hτ).2 (hpt _ _ hτ)) A hA (hr.above A hAl) τ (hLG _ _ hτ).1 (hpt _ _ hτ)`. Take `⟨j, hj, hx, -⟩` from `GlobalTheory.EvExtend.exists_ext φ`. Use `⟨b, ?_⟩` and prove the remaining obligations.

Use `hb ⟨j, hj⟩` as an intermediate fact. Rewrite `this` using `[show (j.comp (algebraMap L _)) = φ from RingHom.ext hx]`. Then use the resulting hypothesis. Establish `hrw : Z.Desc.RegWt π` using `fun u => by`. Take `⟨b, h2⟩` from `hb (ι.symm.toRingHom.comp u.embedding)`. Establish `h3` using `hwt (ι.symm.toRingHom.comp u.embedding)`.

Establish `e : ι.toRingHom.comp (ι.symm.toRingHom.comp u.embedding) = u.embedding` using `RingHom.ext fun x => by simp`. Rewrite `h3` using `[e, h2]`. Establish `hm : (2 : ℤ) ≤ m` using `by exact_mod_cast hr.gap`. Establish `hs : StrictAnti ![-b, 1 - b - m]`. Introduce `i j hij`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp at hij ⊢`. Use linear arithmetic over natural numbers and integers. Use `⟨u.embedding, ⟨![-b, 1 - b - m], hs.antitone⟩, u.mk_embedding, hs, ?_⟩` and prove the remaining obligations. Establish `h4` using `GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk π) u.embedding`. Establish `h5 : (CG.mk π).infChar u.embedding = infOfWeight ⟨![-b, 1 - b - m], hs.antitone⟩`.

Use `Multiset.map_injective (sub_right_injective (b := (((2 : ℕ) : ℂ) - 1) / 2)) (h3.symm.trans ?_)` and prove the remaining obligations. Rewrite using `[infOfWeight, Multiset.map_map, show (Finset.univ : Finset (Fin 2)).val = {0, 1} from rfl]`. Simplify using `only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Function.comp_apply]`. Use `congr 1`. Simplify using the standard rewrite rules.

Use `congr 1`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite `h4` using `[h5]`. Conclude with `h4`.

Establish `hk : ∀ (k : ℕ) (w : Plc L), (k : 𝓞 L) ∈ w.asIdeal ↔ (k : 𝓞 (Lp L)) ∈ (w.under (𝓞 (Lp L))).asIdeal` using `fun k w => by`. Rewrite using `[← map_natCast (algebraMap (𝓞 (Lp L)) (𝓞 L))]`. Both sides reduce to the same expression. Establish `hlm : ∀ w : Plc L, ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → (M : 𝓞 L) ∈ w.asIdeal` using `fun w hw => by`. Take `⟨c, rfl⟩` from `hlM`.

Rewrite using `[Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ hw`. Establish `hfin : {v : HeightOneSpectrum (𝓞 (Lp L)) | (M : 𝓞 (Lp L)) ∈ v.asIdeal}.Finite`. Establish `h0 : Ideal.span {(M : 𝓞 (Lp L))} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`.

Conclude with `hM` after adjusting the coercions. Conclude with `(Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr hv`. Establish `hfix : ∀ w : Plc L, (M : 𝓞 L) ∉ w.asIdeal → ∀ τ, π.IsLocComp w τ → Af.HasFixed τ.ρ (GlobalTheory.LFun.KGL w 2)` using `fun w hw τ hτ => by`. Take `⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w` from `exists_isPlaceOver Ω w`. Take `⟨rc, hrc⟩` from `_root_.UpperTheory.V.Z.Win.exRec'_alt PA.litN hA`.

Establish `hl'` using `mt (hlm w) hw`. Establish `hq` using `hg w A hA rc hrc τ hτ`. Conclude with `_root_.UpperTheory.V.Z.Desc.W.sphT_alt PA.litN L Ω l ι 2 r hc w hl' A hA (hr.unr A fun h => hw ((hA _).1 (by simpa using h))) rc hrc τ hq.1 ((((hLG w τ hτ).1 A hA rc hrc).1 hl').isWDOf hq.2)`. Take `⟨σ, hσ, hunr, hsat⟩` from `P.desc L hU.unr l Fact.out _ hfin (fun w hw => hU.split w ((hk M w).2 hw)) (fun w hw => (hk M w).1 (hlm w hw)) 2 le_rfl (by norm_num) π hreg hrw hd fun w hw => by`. Establish `hw' : (M : 𝓞 L) ∉ w.asIdeal` using `mt (hk M w).1 hw`.

Take `⟨⟨τ, hτ⟩, hi⟩` from `_root_.UpperTheory.V.Af.local_comp_complex_of_printed_results PA L 2 π w`. Take `⟨b, hb⟩` from `(_root_.UpperTheory.V.Af.satake_local_of_printed_results PA L 2 w τ).1 (hfix w hw' τ hτ)`. Conclude with `⟨b, ((_root_.UpperTheory.V.Af.satake_local_of_printed_results PA L 2 w τ).2 _ π.finPart (hi τ hτ) b).2 hb⟩`. Take `⟨hloc, hinf⟩` from `P.same L Ω hU.unr l ι 2 one_le_two π r hc hatt σ hσ hsat`. Use `choose τ₀ hτ₀ using hex`.

Establish `hcl : ∀ w, IsSplitAt w → ∀ τ, Comp σ w τ → IrrGL.of τ.ρ τ.smooth τ.irred = IrrGL.of (τ₀ w).ρ (τ₀ w).smooth (τ₀ w).irred` using `fun w hw τ hτ => IrrGL.of_eq_of.2 (UpperTheory.building_component_uniqueness L 2 σ hσ w hw _ _ _ _ hτ (hloc w hw _ (hτ₀ w)))`. Use `⟨σ, HT, hσ, ⟨hc, fun w hs => ⟨τ₀ w, hloc w hs _ (hτ₀ w)⟩, fun w hs τ hτ A hA rc hrc => ?_, hr.pair⟩, fun w hs τ hτ => ⟨?_, (hLG w _ (hτ₀ w)).2 (hpt w _ (hτ₀ w))⟩, fun w hw => ?_, fun v => ?_⟩` and prove the remaining obligations. Establish `e : algNorm τ = algNorm (τ₀ w)`. Unfold `algNorm`. Rewrite using `[hcl w hs τ hτ]`.

Rewrite using `[e]`. Conclude with `(hLG w _ (hτ₀ w)).1 A hA rc hrc`. Establish `h` using `hpt w _ (hτ₀ w)`. Unfold `UpperTheory.V.Z.Sym.W.PT at h ⊢`. Rewrite using `[hcl w hs τ hτ]`.

Conclude with `h`. Distinguish the cases in `hs : IsSplitAt w`. Conclude with `unr_of_comp hs (hloc w hs _ (hτ₀ w)) (hfix w hw _ (hτ₀ w))`. Conclude with `hunr w hs`. Take `⟨lam, h1, h2⟩` from `hinf v.embedding`.

Establish `e : ι.toRingHom.comp (ι.symm.toRingHom.comp v.embedding) = v.embedding` using `RingHom.ext fun x => by simp`. Take `⟨b, h3⟩` from `hb (ι.symm.toRingHom.comp v.embedding)`. Establish `h4` using `hwt (ι.symm.toRingHom.comp v.embedding)`. Rewrite `h4` using `[e, h3, CG.HasInfChar.infChar_eq (π := CG.mk π) h2]`. Establish `h5` using `Ga.wtOf m b lam h4`.

Use `hr.gap` as an intermediate fact. Conclude with `⟨lam, h1, by omega⟩`.
-/
theorem UpperTheory.V.Z.Sym.W.aboveWeight : _root_.UpperTheory.V.Z.Sym.W.AboveWeightAlt := by
  intro P L Ω _ _ _ _ _ _ l _ ι hl M m hM hlM hU r hr
  have PA := P.af
  have hc := hr.cont
  obtain ⟨π, hreg, hd, hatt⟩ := hr.aut
  have hpol : ∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ := by
    refine ⟨quadChar L ^ 2, fun v => ?_, ?_⟩
    · have e : (quadChar L ^ 2).locInf v (-1) = (quadChar L).locInf v (-1) ^ 2 := rfl
      rw [e, quadChar_locInf]
    · rw [map_pow, compNorm_quadChar, one_pow]
      exact (GlobalTheory.ContraPair.dualIsConjBy_one π).2 hd
  obtain ⟨HT, hwt, hLG⟩ := P.compat L Ω l ι 2 one_le_two r π hc hreg hpol hatt
  have hg : ∀ (w : Plc L) (A : ValuationSubring Ω) (hA : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion L) → WD hA), UpperTheory.Zero.LLC.IsRecT hA rc →
      ∀ τ, π.IsLocComp w τ → GlobalTheory.RoadU.PlainTor (IrrGL.of τ.ρ τ.smooth τ.irred) ∧ UpperTheory.GalStar.Tor (rc (algNorm τ)) ∧ (rc (algNorm τ)).mono0 :=
    fun w A hA rc hrc τ hτ => guard_of P.plain hreg hatt hr.wit (by
      by_cases e : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal
      · exact Or.inr (Or.inr (pot_of_above hr.gap e hr.above))
      · exact Or.inl e) hrc hτ
  have hex : ∀ w : Plc L, ∃ τ, π.IsLocComp w τ := fun w => (_root_.UpperTheory.V.Af.local_comp_complex_of_printed_results PA L 2 π w).1
  have hpt : ∀ (w : Plc L) τ, π.IsLocComp w τ → UpperTheory.V.Z.Sym.W.PT τ := fun w τ hτ => by
    obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
    obtain ⟨rc, hrc⟩ := _root_.UpperTheory.V.Z.Win.exRec'_alt PA.litN hA
    exact (hg w A hA rc hrc τ hτ).1
  have hb : ∀ φ : L →+* Qbar l, ∃ b : ℤ, HT φ = {b, b + m} := fun φ => by
    have hw : ((l : ℕ) : 𝓞 L) ∈ (GlobalTheory.EvExtend.placeOf φ).asIdeal := by
      rw [GlobalTheory.EvExtend.mem_placeOf]
      simpa using GlobalTheory.EvExtend.norm_natCast_lt_one (l := l)
    obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A (GlobalTheory.EvExtend.placeOf φ) := exists_isPlaceOver Ω _
    have hAl : A.valuation (l : Ω) < 1 := by simpa using (hA _).2 hw
    obtain ⟨τ, hτ⟩ := hex (GlobalTheory.EvExtend.placeOf φ)
    obtain ⟨-, b, hb⟩ := _root_.UpperTheory.V.Z.Sym.W.above_w_statement PA L Ω l ι hl r hc m hr.gap _ hw HT ((hLG _ _ hτ).2 (hpt _ _ hτ)) A hA
      (hr.above A hAl) τ (hLG _ _ hτ).1 (hpt _ _ hτ)
    obtain ⟨j, hj, hx, -⟩ := GlobalTheory.EvExtend.exists_ext φ
    refine ⟨b, ?_⟩
    have := hb ⟨j, hj⟩
    rwa [show (j.comp (algebraMap L _)) = φ from RingHom.ext hx] at this
  have hrw : Z.Desc.RegWt π := fun u => by
    obtain ⟨b, h2⟩ := hb (ι.symm.toRingHom.comp u.embedding)
    have h3 := hwt (ι.symm.toRingHom.comp u.embedding)
    have e : ι.toRingHom.comp (ι.symm.toRingHom.comp u.embedding) = u.embedding := RingHom.ext fun x => by simp
    rw [e, h2] at h3
    have hm : (2 : ℤ) ≤ m := by exact_mod_cast hr.gap
    have hs : StrictAnti ![-b, 1 - b - m] := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
      omega
    refine ⟨u.embedding, ⟨![-b, 1 - b - m], hs.antitone⟩, u.mk_embedding, hs, ?_⟩
    have h4 := GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk π) u.embedding
    have h5 : (CG.mk π).infChar u.embedding = infOfWeight ⟨![-b, 1 - b - m], hs.antitone⟩ := by
      refine Multiset.map_injective (sub_right_injective (b := (((2 : ℕ) : ℂ) - 1) / 2)) (h3.symm.trans ?_)
      rw [infOfWeight, Multiset.map_map, show (Finset.univ : Finset (Fin 2)).val = {0, 1} from rfl]
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Function.comp_apply]
      congr 1
      · simp
      · congr 1
        simp
        ring
    rw [h5] at h4
    exact h4
  have hk : ∀ (k : ℕ) (w : Plc L), (k : 𝓞 L) ∈ w.asIdeal ↔ (k : 𝓞 (Lp L)) ∈ (w.under (𝓞 (Lp L))).asIdeal := fun k w => by
    rw [← map_natCast (algebraMap (𝓞 (Lp L)) (𝓞 L))]
    rfl
  have hlm : ∀ w : Plc L, ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → (M : 𝓞 L) ∈ w.asIdeal := fun w hw => by
    obtain ⟨c, rfl⟩ := hlM
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hw
  have hfin : {v : HeightOneSpectrum (𝓞 (Lp L)) | (M : 𝓞 (Lp L)) ∈ v.asIdeal}.Finite := by
    have h0 : Ideal.span {(M : 𝓞 (Lp L))} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast hM
    exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr hv
  have hfix : ∀ w : Plc L, (M : 𝓞 L) ∉ w.asIdeal → ∀ τ, π.IsLocComp w τ → Af.HasFixed τ.ρ (GlobalTheory.LFun.KGL w 2) := fun w hw τ hτ => by
    obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
    obtain ⟨rc, hrc⟩ := _root_.UpperTheory.V.Z.Win.exRec'_alt PA.litN hA
    have hl' := mt (hlm w) hw
    have hq := hg w A hA rc hrc τ hτ
    exact _root_.UpperTheory.V.Z.Desc.W.sphT_alt PA.litN L Ω l ι 2 r hc w hl' A hA (hr.unr A fun h => hw ((hA _).1 (by simpa using h))) rc hrc τ hq.1
      ((((hLG w τ hτ).1 A hA rc hrc).1 hl').isWDOf hq.2)
  obtain ⟨σ, hσ, hunr, hsat⟩ := P.desc L hU.unr l Fact.out _ hfin (fun w hw => hU.split w ((hk M w).2 hw))
    (fun w hw => (hk M w).1 (hlm w hw)) 2 le_rfl (by norm_num) π hreg hrw hd
    fun w hw => by
      have hw' : (M : 𝓞 L) ∉ w.asIdeal := mt (hk M w).1 hw
      obtain ⟨⟨τ, hτ⟩, hi⟩ := _root_.UpperTheory.V.Af.local_comp_complex_of_printed_results PA L 2 π w
      obtain ⟨b, hb⟩ := (_root_.UpperTheory.V.Af.satake_local_of_printed_results PA L 2 w τ).1 (hfix w hw' τ hτ)
      exact ⟨b, ((_root_.UpperTheory.V.Af.satake_local_of_printed_results PA L 2 w τ).2 _ π.finPart (hi τ hτ) b).2 hb⟩
  obtain ⟨hloc, hinf⟩ := P.same L Ω hU.unr l ι 2 one_le_two π r hc hatt σ hσ hsat
  choose τ₀ hτ₀ using hex
  have hcl : ∀ w, IsSplitAt w → ∀ τ, Comp σ w τ → IrrGL.of τ.ρ τ.smooth τ.irred = IrrGL.of (τ₀ w).ρ (τ₀ w).smooth (τ₀ w).irred :=
    fun w hw τ hτ => IrrGL.of_eq_of.2 (UpperTheory.building_component_uniqueness L 2 σ hσ w hw _ _ _ _ hτ (hloc w hw _ (hτ₀ w)))
  refine ⟨σ, HT, hσ, ⟨hc, fun w hs => ⟨τ₀ w, hloc w hs _ (hτ₀ w)⟩, fun w hs τ hτ A hA rc hrc => ?_, hr.pair⟩,
    fun w hs τ hτ => ⟨?_, (hLG w _ (hτ₀ w)).2 (hpt w _ (hτ₀ w))⟩, fun w hw => ?_, fun v => ?_⟩
  · have e : algNorm τ = algNorm (τ₀ w) := by
      unfold algNorm
      rw [hcl w hs τ hτ]
    rw [e]
    exact (hLG w _ (hτ₀ w)).1 A hA rc hrc
  · have h := hpt w _ (hτ₀ w)
    unfold UpperTheory.V.Z.Sym.W.PT at h ⊢
    rw [hcl w hs τ hτ]
    exact h
  · by_cases hs : IsSplitAt w
    · exact unr_of_comp hs (hloc w hs _ (hτ₀ w)) (hfix w hw _ (hτ₀ w))
    · exact hunr w hs
  · obtain ⟨lam, h1, h2⟩ := hinf v.embedding
    have e : ι.toRingHom.comp (ι.symm.toRingHom.comp v.embedding) = v.embedding := RingHom.ext fun x => by simp
    obtain ⟨b, h3⟩ := hb (ι.symm.toRingHom.comp v.embedding)
    have h4 := hwt (ι.symm.toRingHom.comp v.embedding)
    rw [e, h3, CG.HasInfChar.infChar_eq (π := CG.mk π) h2] at h4
    have h5 := Ga.wtOf m b lam h4
    have := hr.gap
    exact ⟨lam, h1, by omega⟩
end
end
