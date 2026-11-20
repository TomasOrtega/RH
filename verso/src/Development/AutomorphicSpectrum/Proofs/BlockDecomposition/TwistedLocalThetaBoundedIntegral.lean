import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LFunctionEquationGlobal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitInducedRepresentationHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilInducedRepresentationHypothesisStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitWeilActionTorusEquivariantStatement
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.ThetaBound

open Filter Topology ValuativeRel

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/- English proof (translation)
Take `⟨p, hp⟩` from `CharP.exists 𝓀[F]`. Establish `hp0 : p ≠ 0` using `CharP.char_ne_zero_of_finite 𝓀[F] p`. Use `⟨p, hp0, ?_⟩` and prove the remaining obligations. Establish `h0 : IsLocalRing.residue 𝒪[F] (p : 𝒪[F]) = 0`. Rewrite using `[map_natCast]`.

Conclude with `(CharP.cast_eq_zero_iff 𝓀[F] p p).2 dvd_rfl`. Establish `h1 : ¬ IsUnit (p : 𝒪[F])`. Use `(IsLocalRing.residue_eq_zero_iff (R := 𝒪[F]) (p : 𝒪[F])).1 h0` as an intermediate fact. Conclude with `(IsLocalRing.mem_maximalIdeal _).1 this`. Establish `hv` using `Valuation.integer.integers (valuation F)`.

Establish `h2` using `lt_of_le_of_ne (hv.map_le_one (p : 𝒪[F])) fun h => h1 (hv.isUnit_iff_valuation_eq_one.2 h)`. Simplify using `using h2`.
-/
theorem exists_nat_val_lt_one [CharZero F] : ∃ p : ℕ, p ≠ 0 ∧ valuation F (p : F) < 1 := by
  obtain ⟨p, hp⟩ := CharP.exists 𝓀[F]
  have hp0 : p ≠ 0 := CharP.char_ne_zero_of_finite 𝓀[F] p
  refine ⟨p, hp0, ?_⟩
  have h0 : IsLocalRing.residue 𝒪[F] (p : 𝒪[F]) = 0 := by
    rw [map_natCast]
    exact (CharP.cast_eq_zero_iff 𝓀[F] p p).2 dvd_rfl
  have h1 : ¬ IsUnit (p : 𝒪[F]) := by
    have := (IsLocalRing.residue_eq_zero_iff (R := 𝒪[F]) (p : 𝒪[F])).1 h0
    exact (IsLocalRing.mem_maximalIdeal _).1 this
  have hv := Valuation.integer.integers (valuation F)
  have h2 := lt_of_le_of_ne (hv.map_le_one (p : 𝒪[F])) fun h => h1 (hv.isUnit_iff_valuation_eq_one.2 h)
  simpa using h2

/- English proof (translation)
Rewrite using `[(IsValuativeTopology.hasBasis_nhds_zero' F).tendsto_right_iff]`. Introduce `γ hγ`. Establish `: MulArchimedean (ValueGroupWithZero F)` using `ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance`. Take `⟨n, hn⟩` from `exists_pow_lt₀ h (Units.mk0 γ hγ)`. Use `filter_upwards [eventually_ge_atTop n] with m hm`.

Rewrite using `[map_pow]`. Conclude with `lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn`.
-/
theorem tendsto_pow_zero {x : F} (h : valuation F x < 1) : Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero' F).tendsto_right_iff]
  intro γ hγ
  have : MulArchimedean (ValueGroupWithZero F) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 γ hγ)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

/- English proof (translation)
Establish `hset : ({x : F | x ∈ 𝒪[F]} : Set F) = (valBall F 0 : Set F)`. Rewrite using `[coe_valBall_zero]`. Both sides reduce to the same expression. Rewrite using `[hset]`. Conclude with `isOpen_valBall 0`.
-/
theorem isOpen_integers : IsOpen ({x : F | x ∈ 𝒪[F]} : Set F) := by
  have hset : ({x : F | x ∈ 𝒪[F]} : Set F) = (valBall F 0 : Set F) := by
    rw [coe_valBall_zero]; rfl
  rw [hset]
  exact isOpen_valBall 0

/- English proof (translation)
Take `⟨p, hp0, hp⟩` from `exists_nat_val_lt_one (F := F)`. Establish `hO` using `isOpen_integers (F := F)`. Set `U : ℕ → Set F` to `fun k => {x | (p : F) ^ k * x ∈ 𝒪[F]}`. Establish `hUo : ∀ k, IsOpen (U k)` using `fun k => hO.preimage (continuous_const.mul continuous_id)`. Establish `hmono : Monotone U`.

Use `monotone_nat_of_le_succ fun k x hx => ?_` and prove the remaining obligations. Establish `hx' : (p : F) ^ k * x ∈ 𝒪[F]` using `hx`. Express the relevant statement in the definitionally equal form `(p : F) ^ (k + 1) * x ∈ 𝒪[F]`. Establish `e : (p : F) ^ (k + 1) * x = (p : F) * ((p : F) ^ k * x)` using `by ring`. Rewrite using `[e]`.

Conclude with `mul_mem (natCast_mem _ p) hx'`. Establish `hcov : S ⊆ ⋃ k, U k`. Introduce `x _`. Establish `ht : Tendsto (fun k : ℕ => (p : F) ^ k * x) atTop (𝓝 0)`. Simplify using `using (tendsto_pow_zero hp).mul_const x`.

Establish `h0 : ({x : F | x ∈ 𝒪[F]} : Set F) ∈ 𝓝 (0 : F)` using `hO.mem_nhds (zero_mem 𝒪[F])`. Take `⟨k, hk⟩` from `(ht.eventually h0).exists`. Conclude with `Set.mem_iUnion.2 ⟨k, hk⟩`. Take `⟨k, hk⟩` from `hS.elim_directed_cover U hUo hcov hmono.directed_le`. Use `⟨p ^ k, pow_ne_zero _ hp0, fun x hx => ?_⟩` and prove the remaining obligations.

Use `hk hx` as an intermediate fact. Simplify `this` using `[U]`.
-/
theorem exists_nat_mul_mem [CharZero F] {S : Set F} (hS : IsCompact S) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ x ∈ S, (N : F) * x ∈ 𝒪[F] := by
  obtain ⟨p, hp0, hp⟩ := exists_nat_val_lt_one (F := F)
  have hO := isOpen_integers (F := F)
  let U : ℕ → Set F := fun k => {x | (p : F) ^ k * x ∈ 𝒪[F]}
  have hUo : ∀ k, IsOpen (U k) := fun k => hO.preimage (continuous_const.mul continuous_id)
  have hmono : Monotone U := by
    refine monotone_nat_of_le_succ fun k x hx => ?_
    have hx' : (p : F) ^ k * x ∈ 𝒪[F] := hx
    change (p : F) ^ (k + 1) * x ∈ 𝒪[F]
    have e : (p : F) ^ (k + 1) * x = (p : F) * ((p : F) ^ k * x) := by ring
    rw [e]
    exact mul_mem (natCast_mem _ p) hx'
  have hcov : S ⊆ ⋃ k, U k := by
    intro x _
    have ht : Tendsto (fun k : ℕ => (p : F) ^ k * x) atTop (𝓝 0) := by
      simpa using (tendsto_pow_zero hp).mul_const x
    have h0 : ({x : F | x ∈ 𝒪[F]} : Set F) ∈ 𝓝 (0 : F) := hO.mem_nhds (zero_mem 𝒪[F])
    obtain ⟨k, hk⟩ := (ht.eventually h0).exists
    exact Set.mem_iUnion.2 ⟨k, hk⟩
  obtain ⟨k, hk⟩ := hS.elim_directed_cover U hUo hcov hmono.directed_le
  refine ⟨p ^ k, pow_ne_zero _ hp0, fun x hx => ?_⟩
  have := hk hx
  simpa [U] using this

end Loc

section Places

open GroundTheory.Global.AdicLiesOver

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
The claim follows from `Function.invFun_eq ((GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.algebraMap_bijective v w h1).2 _)`.
-/
theorem algebraMap_degreeOneEmbedding (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal]
    (h1 : Module.finrank (Qv v) (Kv K w) = 1) (ξ : K) :
    algebraMap (Qv v) (Kv K w) (dg1 v w ξ) = algebraMap K (Kv K w) ξ :=
  Function.invFun_eq ((GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.algebraMap_bijective v w h1).2 _)

/- English proof (translation)
Rewrite using `[map_mul, map_natCast]`. Conclude with `h`.
-/
theorem mul_mem_of_mem (w : PlK K) {N : ℕ} {ξ : K}
    (h : (N : Kv K w) * algebraMap K (Kv K w) ξ ∈ 𝒪[Kv K w]) :
    algebraMap K (Kv K w) ((N : K) * ξ) ∈ 𝒪[Kv K w] := by
  rw [map_mul, map_natCast]
  exact h

end Places

section Main

open GroundTheory.Global.AdicLiesOver

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Take `⟨hall, d1, d2⟩` from `GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.places_split h2 v w₁ w₂ hne`. Establish `hstd : IsStd (GP.psiF v)` using `GlobalTheory.CompanionTheory.RankinQ.isStd_local v`. Establish `hχc` using `GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.continuous_charInv (GP.psiF v) hstd.1`. Establish `hχ1 : (GP.psiF v)⁻¹ ≠ 1` using `inv_ne_one.2 hstd.2.1`. Establish `hf` using `(GlobalTheory.CompanionTheory.SplitPi.sPiRep (Qv v) (GP.psiF v)⁻¹ hχc hχ1 (cAt c v w₁) (cAt c v w₂) (GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.isUnit1_cAt c v w₁) (GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.isUnit1_cAt c v w₂) Φ ⟨hl, hc⟩ 1 g₀).2`.

Use `set f := GL2LocalData.piS (GP.psiF v)⁻¹ (cAt c v w₁) g₀ Φ with hfdef`. Take `⟨B, hB⟩` from `hf.1.continuous.bounded_above_of_compact_support hf.2`. Establish `hC : IsCompact (tsupport f)` using `hf.2`. Set `m : (Qv v)ˣ × (Qv v × Qv v) → Qv v × Qv v` to `fun q => q.2 * (((q.1⁻¹ : (Qv v)ˣ) : Qv v), (q.1 : Qv v))`. Establish `hm : Continuous m`.

Use `continuous_snd.mul (Continuous.prodMk ?_ ?_)` and prove the remaining obligations. Conclude with `Units.continuous_val.comp (continuous_inv.comp continuous_fst)`. Conclude with `Units.continuous_val.comp continuous_fst`. Establish `hC' : IsCompact (m '' (T ×ˢ tsupport f))` using `(hT.prod hC).image hm`. Establish `hA₁ : IsCompact (algebraMap (Qv v) (Kv K w₁) '' (Prod.fst '' (m '' (T ×ˢ tsupport f))))` using `(hC'.image continuous_fst).image (_root_.continuous_algebraMap (Qv v) (Kv K w₁))`.

Establish `hA₂ : IsCompact (algebraMap (Qv v) (Kv K w₂) '' (Prod.snd '' (m '' (T ×ˢ tsupport f))))` using `(hC'.image continuous_snd).image (_root_.continuous_algebraMap (Qv v) (Kv K w₂))`. Take `⟨N₁, hN₁, H₁⟩` from `exists_nat_mul_mem hA₁`. Take `⟨N₂, hN₂, H₂⟩` from `exists_nat_mul_mem hA₂`. Use `⟨B, N₁ * N₂, mul_ne_zero hN₁ hN₂, fun τ hτ ξ => ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.T.split_weil_action_torus_equivariant (Qv v) (GP.psiF v)⁻¹ hχc hχ1 (cAt c v w₁) g₀ Φ τ]`.

Use `⟨hB _, fun hz w hw => ?_⟩` and prove the remaining obligations. Establish `hs : ((dg1 v w₁ ξ, dg1 v w₂ ξ) : Qv v × Qv v) ∈ m '' (T ×ˢ tsupport f)`. Use `⟨(τ, (dg1 v w₁ ξ, dg1 v w₂ ξ) * ((τ : Qv v), ((τ⁻¹ : (Qv v)ˣ) : Qv v))), ⟨hτ, subset_tsupport f hz⟩, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [m, mul_assoc]`. Establish `e₁ : algebraMap K (Kv K w₁) ξ ∈ algebraMap (Qv v) (Kv K w₁) '' (Prod.fst '' (m '' (T ×ˢ tsupport f)))` using `⟨dg1 v w₁ ξ, ⟨_, hs, rfl⟩, algebraMap_degreeOneEmbedding v w₁ d1 ξ⟩`.

Establish `e₂ : algebraMap K (Kv K w₂) ξ ∈ algebraMap (Qv v) (Kv K w₂) '' (Prod.snd '' (m '' (T ×ˢ tsupport f)))` using `⟨dg1 v w₂ ξ, ⟨_, hs, rfl⟩, algebraMap_degreeOneEmbedding v w₂ d2 ξ⟩`. Break down `hall w hw with rfl | rfl` into its components or cases. Use `mul_mem_of_mem w ?_` and prove the remaining obligations. Establish `e : ((N₁ * N₂ : ℕ) : Kv K w) * algebraMap K (Kv K w) ξ = (N₂ : Kv K w) * ((N₁ : Kv K w) * algebraMap K (Kv K w) ξ)` using `by push_cast; ring`. Rewrite using `[e]`.

Conclude with `mul_mem (natCast_mem _ N₂) (H₁ _ e₁)`. Use `mul_mem_of_mem w ?_` and prove the remaining obligations. Establish `e : ((N₁ * N₂ : ℕ) : Kv K w) * algebraMap K (Kv K w) ξ = (N₁ : Kv K w) * ((N₂ : Kv K w) * algebraMap K (Kv K w) ξ)` using `by push_cast; ring`. Rewrite using `[e]`. Conclude with `mul_mem (natCast_mem _ N₁) (H₂ _ e₂)`.
-/
theorem bound_sp (h2 : Module.finrank ℚ K = 2) (c : HeckeCharacter K) (v : Pl) (w₁ w₂ : PlK K)
    [h₁ : w₁.asIdeal.LiesOver v.asIdeal] [h₂ : w₂.asIdeal.LiesOver v.asIdeal] (Φ : Qv v × Qv v → ℂ)
    (hne : w₁ ≠ w₂) (hl : IsLocallyConstant Φ) (hc : HasCompactSupport Φ) (g₀ : GL (Fin 2) (Qv v))
    (T : Set (Qv v)ˣ) (hT : IsCompact T) : ∃ (B : ℝ) (N : ℕ), N ≠ 0 ∧
      ∀ τ ∈ T, ∀ ξ : K,
        ‖GL2LocalData.piS (GP.psiF v)⁻¹ (cAt c v w₁) g₀ (fun x => Φ (x * ((τ : Qv v), ((τ⁻¹ : (Qv v)ˣ) : Qv v))))
                     (dg1 v w₁ ξ, dg1 v w₂ ξ)‖ ≤ B ∧
        (GL2LocalData.piS (GP.psiF v)⁻¹ (cAt c v w₁) g₀ (fun x => Φ (x * ((τ : Qv v), ((τ⁻¹ : (Qv v)ˣ) : Qv v))))
                     (dg1 v w₁ ξ, dg1 v w₂ ξ) ≠ 0 →
          ∀ w : PlK K, w.asIdeal.LiesOver v.asIdeal → algebraMap K (Kv K w) ((N : K) * ξ) ∈ 𝒪[Kv K w]) := by
  obtain ⟨hall, d1, d2⟩ := GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.places_split h2 v w₁ w₂ hne
  have hstd : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.RankinQ.isStd_local v
  have hχc := GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.continuous_charInv (GP.psiF v) hstd.1
  have hχ1 : (GP.psiF v)⁻¹ ≠ 1 := inv_ne_one.2 hstd.2.1
  have hf := (GlobalTheory.CompanionTheory.SplitPi.sPiRep (Qv v) (GP.psiF v)⁻¹ hχc hχ1 (cAt c v w₁) (cAt c v w₂)
    (GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.isUnit1_cAt c v w₁) (GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.isUnit1_cAt c v w₂) Φ ⟨hl, hc⟩ 1 g₀).2
  set f := GL2LocalData.piS (GP.psiF v)⁻¹ (cAt c v w₁) g₀ Φ with hfdef
  obtain ⟨B, hB⟩ := hf.1.continuous.bounded_above_of_compact_support hf.2
  have hC : IsCompact (tsupport f) := hf.2
  let m : (Qv v)ˣ × (Qv v × Qv v) → Qv v × Qv v :=
    fun q => q.2 * (((q.1⁻¹ : (Qv v)ˣ) : Qv v), (q.1 : Qv v))
  have hm : Continuous m := by
    refine continuous_snd.mul (Continuous.prodMk ?_ ?_)
    · exact Units.continuous_val.comp (continuous_inv.comp continuous_fst)
    · exact Units.continuous_val.comp continuous_fst
  have hC' : IsCompact (m '' (T ×ˢ tsupport f)) := (hT.prod hC).image hm
  have hA₁ : IsCompact (algebraMap (Qv v) (Kv K w₁) '' (Prod.fst '' (m '' (T ×ˢ tsupport f)))) :=
    (hC'.image continuous_fst).image (_root_.continuous_algebraMap (Qv v) (Kv K w₁))
  have hA₂ : IsCompact (algebraMap (Qv v) (Kv K w₂) '' (Prod.snd '' (m '' (T ×ˢ tsupport f)))) :=
    (hC'.image continuous_snd).image (_root_.continuous_algebraMap (Qv v) (Kv K w₂))
  obtain ⟨N₁, hN₁, H₁⟩ := exists_nat_mul_mem hA₁
  obtain ⟨N₂, hN₂, H₂⟩ := exists_nat_mul_mem hA₂
  refine ⟨B, N₁ * N₂, mul_ne_zero hN₁ hN₂, fun τ hτ ξ => ?_⟩
  rw [GlobalTheory.T.split_weil_action_torus_equivariant (Qv v) (GP.psiF v)⁻¹ hχc hχ1 (cAt c v w₁) g₀ Φ τ]
  refine ⟨hB _, fun hz w hw => ?_⟩
  have hs : ((dg1 v w₁ ξ, dg1 v w₂ ξ) : Qv v × Qv v) ∈ m '' (T ×ˢ tsupport f) := by
    refine ⟨(τ, (dg1 v w₁ ξ, dg1 v w₂ ξ) * ((τ : Qv v), ((τ⁻¹ : (Qv v)ˣ) : Qv v))),
      ⟨hτ, subset_tsupport f hz⟩, ?_⟩
    ext <;> simp [m, mul_assoc]
  have e₁ : algebraMap K (Kv K w₁) ξ ∈ algebraMap (Qv v) (Kv K w₁) '' (Prod.fst '' (m '' (T ×ˢ tsupport f))) :=
    ⟨dg1 v w₁ ξ, ⟨_, hs, rfl⟩, algebraMap_degreeOneEmbedding v w₁ d1 ξ⟩
  have e₂ : algebraMap K (Kv K w₂) ξ ∈ algebraMap (Qv v) (Kv K w₂) '' (Prod.snd '' (m '' (T ×ˢ tsupport f))) :=
    ⟨dg1 v w₂ ξ, ⟨_, hs, rfl⟩, algebraMap_degreeOneEmbedding v w₂ d2 ξ⟩
  rcases hall w hw with rfl | rfl
  · refine mul_mem_of_mem w ?_
    have e : ((N₁ * N₂ : ℕ) : Kv K w) * algebraMap K (Kv K w) ξ =
        (N₂ : Kv K w) * ((N₁ : Kv K w) * algebraMap K (Kv K w) ξ) := by push_cast; ring
    rw [e]
    exact mul_mem (natCast_mem _ N₂) (H₁ _ e₁)
  · refine mul_mem_of_mem w ?_
    have e : ((N₁ * N₂ : ℕ) : Kv K w) * algebraMap K (Kv K w) ξ =
        (N₁ : Kv K w) * ((N₂ : Kv K w) * algebraMap K (Kv K w) ξ) := by push_cast; ring
    rw [e]
    exact mul_mem (natCast_mem _ N₁) (H₂ _ e₂)

/- English proof (translation)
Establish `d2` using `GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.places_nonsplit h2 v w hu`. Establish `hstd : IsStd (GP.psiF v)` using `GlobalTheory.CompanionTheory.RankinQ.isStd_local v`. Establish `hχc` using `GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.continuous_charInv (GP.psiF v) hstd.1`. Establish `hχ1 : (GP.psiF v)⁻¹ ≠ 1` using `inv_ne_one.2 hstd.2.1`. Establish `hf` using `(GlobalTheory.T.weil_induced_representation_hypothesis (Qv v) (GP.psiF v)⁻¹ hχc hχ1 (Kv K w) d2 (_root_.continuous_algebraMap (Qv v) (Kv K w)) σ hσ η hη (localChar c w) Φ hΦ 1 g₀ hp).2`.

Use `set f := GL2LocalData.piG (GP.psiF v)⁻¹ σ (selfDualMeasure (GL2LocalData.chE (Kv K w) (GP.psiF v)⁻¹)) (GL2LocalData.lamE (Kv K w) (GP.psiF v)⁻¹ η) (localChar c w) g₀ Φ with hfdef`. Establish `hl : IsLocallyConstant f` using `hf.1`. Establish `hc : HasCompactSupport f` using `hf.2.1`. Take `⟨B, hB⟩` from `hl.continuous.bounded_above_of_compact_support hc`. Take `⟨N, hN, H⟩` from `exists_nat_mul_mem (show IsCompact (tsupport f) from hc)`.

Use `⟨B, N, hN, fun ξ => ⟨hB _, fun hz w' hw' => ?_⟩⟩` and prove the remaining obligations. Take `rfl` from `hu w' hw'`. Conclude with `mul_mem_of_mem w' (H _ (subset_tsupport f hz))`.
-/
theorem bound_ns (h2 : Module.finrank ℚ K = 2) (c : HeckeCharacter K) (v : Pl) (w : PlK K)
    [h : w.asIdeal.LiesOver v.asIdeal] (σ : Kv K w ≃ₐ[Qv v] Kv K w) (η : (Qv v)ˣ →* ℂˣ) (Φ : Kv K w → ℂ)
    (hu : ∀ w' : PlK K, w'.asIdeal.LiesOver v.asIdeal → w' = w) (hσ : σ ≠ AlgEquiv.refl)
    (hη : ∀ a, ((η a : ℂˣ) : ℂ) = GL2LocalData.nsg (Kv K w) (a : Qv v))
    (hΦ : Φ ∈ GL2LocalData.SBc (Qv v) (Kv K w) (localChar c w)) (g₀ : GL (Fin 2) (Qv v))
    (hp : ∃ t : (Kv K w)ˣ, Algebra.norm (Qv v) (t : Kv K w) = (g₀.val).det) :
    ∃ (B : ℝ) (N : ℕ), N ≠ 0 ∧ ∀ ξ : K,
      ‖GL2LocalData.piG (GP.psiF v)⁻¹ σ (selfDualMeasure (GL2LocalData.chE (Kv K w) (GP.psiF v)⁻¹))
                   (GL2LocalData.lamE (Kv K w) (GP.psiF v)⁻¹ η) (localChar c w) g₀ Φ (algebraMap K (Kv K w) ξ)‖ ≤ B ∧
      (GL2LocalData.piG (GP.psiF v)⁻¹ σ (selfDualMeasure (GL2LocalData.chE (Kv K w) (GP.psiF v)⁻¹))
                   (GL2LocalData.lamE (Kv K w) (GP.psiF v)⁻¹ η) (localChar c w) g₀ Φ (algebraMap K (Kv K w) ξ) ≠ 0 →
        ∀ w' : PlK K, w'.asIdeal.LiesOver v.asIdeal → algebraMap K (Kv K w') ((N : K) * ξ) ∈ 𝒪[Kv K w']) := by
  have d2 := GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.places_nonsplit h2 v w hu
  have hstd : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.RankinQ.isStd_local v
  have hχc := GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.continuous_charInv (GP.psiF v) hstd.1
  have hχ1 : (GP.psiF v)⁻¹ ≠ 1 := inv_ne_one.2 hstd.2.1
  have hf := (GlobalTheory.T.weil_induced_representation_hypothesis (Qv v) (GP.psiF v)⁻¹ hχc hχ1 (Kv K w) d2
    (_root_.continuous_algebraMap (Qv v) (Kv K w)) σ hσ η hη (localChar c w) Φ hΦ 1 g₀ hp).2
  set f := GL2LocalData.piG (GP.psiF v)⁻¹ σ (selfDualMeasure (GL2LocalData.chE (Kv K w) (GP.psiF v)⁻¹))
    (GL2LocalData.lamE (Kv K w) (GP.psiF v)⁻¹ η) (localChar c w) g₀ Φ with hfdef
  have hl : IsLocallyConstant f := hf.1
  have hc : HasCompactSupport f := hf.2.1
  obtain ⟨B, hB⟩ := hl.continuous.bounded_above_of_compact_support hc
  obtain ⟨N, hN, H⟩ := exists_nat_mul_mem (show IsCompact (tsupport f) from hc)
  refine ⟨B, N, hN, fun ξ => ⟨hB _, fun hz w' hw' => ?_⟩⟩
  obtain rfl := hu w' hw'
  exact mul_mem_of_mem w' (H _ (subset_tsupport f hz))

/- English proof (translation)
Introduce `K _ _ h2 c v L hok g₀ hp T hT`. Consider the cases of `L with`. Consider the case `@sp w₁ w₂ h₁ h₂ Φ`. Take `⟨hne, hl, hc⟩` from `hok`. Conclude with `bound_sp h2 c v w₁ w₂ Φ hne hl hc g₀ T hT`.

Consider the case `@ns w h σ η Φ`. Take `⟨hu, hσ, hη, hΦ⟩` from `hok`. Take `⟨B, N, hN, H⟩` from `bound_ns h2 c v w σ η Φ hu hσ hη hΦ g₀ hp`. Conclude with `⟨B, N, hN, fun _ _ ξ => H ξ⟩`.
-/
theorem bound : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → ∀ g₀ : GL (Fin 2) (Qv v), L.plus g₀ → ∀ T : Set (Qv v)ˣ, IsCompact T → ∃ (B : ℝ) (N : ℕ), N ≠ 0 ∧
    ∀ τ ∈ T, ∀ ξ : K, ‖(L.tw τ).val g₀ ξ‖ ≤ B ∧ ((L.tw τ).val g₀ ξ ≠ 0 →
      ∀ w : PlK K, w.asIdeal.LiesOver v.asIdeal → algebraMap K (Kv K w) ((N : K) * ξ) ∈ 𝒪[Kv K w]) := by
  intro K _ _ h2 c v L hok g₀ hp T hT
  cases L with
  | @sp w₁ w₂ h₁ h₂ Φ =>
    obtain ⟨hne, hl, hc⟩ := hok
    exact bound_sp h2 c v w₁ w₂ Φ hne hl hc g₀ T hT
  | @ns w h σ η Φ =>
    obtain ⟨hu, hσ, hη, hΦ⟩ := hok
    obtain ⟨B, N, hN, H⟩ := bound_ns h2 c v w σ η Φ hu hσ hη hΦ g₀ hp
    exact ⟨B, N, hN, fun _ _ ξ => H ξ⟩

end Main

end GlobalTheory.CompanionTheory.ThetaBound
