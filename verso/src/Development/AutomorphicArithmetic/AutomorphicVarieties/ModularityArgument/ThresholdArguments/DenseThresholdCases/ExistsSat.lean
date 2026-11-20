import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfHRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocCompR
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSatLoc

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Polynomial UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd Matrix
open GlobalTheory.CuspRep (SmIrr Af invT finId pFin locGL finGL GA chiDet)
namespace UpperTheory.Esk.HeckeRepresentationSatake
section Proj
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ}
/- English proof (translation)
Take `⟨⟨σ, hσ⟩, h2⟩` from `_root_.UpperTheory.V.Af.local_comp_real_of_printed_results P F a π w`. Establish `hi` using `h2 σ hσ`. Take `⟨h3, h4⟩` from `_root_.UpperTheory.V.Af.satake_local_of_printed_results P F a w σ`. Take `⟨x, hx0, hx⟩` from `h`. Take `⟨B, hB⟩` from `h3 (GlobalTheory.CuspRep.LocSph.exists_fixed_of_mem_iSup (π.locRep w) σ.ρ σ.irred (fun f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.finPart (locGL F a w g) (f v)} => f.1) (fun f => f.2) (GlobalTheory.LFun.KGL w a : Set _) x hx0 hx (hi.2 ▸ Submodule.mem_top))`.

Conclude with `⟨B, (h4 _ _ hi B).2 hB⟩`.
-/
theorem exists_sat_alt (P : _root_.UpperTheory.V.Af.Hypotheses') (π : TR.CuspSub F a) (w : HeightOneSpectrum (𝓞 F))
    (h : HasFixed (π.locRep w) (GlobalTheory.LFun.KGL w a)) : ∃ B, π.HasSat w B := by
  obtain ⟨⟨σ, hσ⟩, h2⟩ := _root_.UpperTheory.V.Af.local_comp_real_of_printed_results P F a π w
  have hi := h2 σ hσ
  obtain ⟨h3, h4⟩ := _root_.UpperTheory.V.Af.satake_local_of_printed_results P F a w σ
  obtain ⟨x, hx0, hx⟩ := h
  obtain ⟨B, hB⟩ := h3 (GlobalTheory.CuspRep.LocSph.exists_fixed_of_mem_iSup (π.locRep w) σ.ρ σ.irred
    (fun f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.finPart (locGL F a w g) (f v)} => f.1) (fun f => f.2)
    (GlobalTheory.LFun.KGL w a : Set _) x hx0 hx (hi.2 ▸ Submodule.mem_top))
  exact ⟨B, (h4 _ _ hi B).2 hB⟩
end Proj
section Loc
open GlobalTheory.LFun Formalism.UG
variable {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))
end Loc
section Inf
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
open GlobalTheory.HeckeGal.Model GlobalTheory.Mem.Chr.CharModel
end Inf
section Sign
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
end Sign
/- English proof (translation)
Introduce `P hC`. Unfold `UpperTheory.Esk.HCap at hC`. Unfold `UpperTheory.Esk.HRep`. Introduce `F _ _ _ k hk t c ω hω φ lam hφ hne heig hcusp`. Take `⟨h1, hcap⟩` from `hC F (fun v => k + 2 * t v) c ω hω φ hφ`.

Take `⟨π₀, ψ, hψ, h0, hz⟩` from `proj hne (P.ssR F 2 φ hcusp ⟨0, by rw [h1, zero_smul]⟩)`. Use `set ν := GlobalTheory.HeckeGal.Model.absPow F (1 - (k : ℝ) / 2) with hν`. Take `⟨hν1, hν2, -⟩` from `GlobalTheory.HeckeGal.Model.absPow_isAbsPow F (1 - (k : ℝ) / 2)`. Rewrite `hν1`, `hν2` using `[← hν]`. Establish `hq : ∀ w : Pl F, (0 : ℝ) < normV w` using `fun w => Nat.cast_pos.2 (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm w))`.

Establish `hν3 : ∀ w, ((ν.val w : ℂˣ) : ℂ) = (((normV w : ℝ) ^ ((k : ℝ) / 2 - 1) : ℝ) : ℂ)` using `fun w => by`. Rewrite using `[hν2, Complex.ofReal_cpow (hq w).le, ← Complex.ofReal_neg, neg_sub]`. Both sides reduce to the same expression. Use `set π := π₀.twist ν`. Use `set x₀ : π₀.V := ⟨ψ, hψ⟩`.

Use `set T := π₀.toTwist ν`. Establish `hx0 : T x₀ ≠ 0` using `(map_ne_zero_iff _ T.injective).2 fun e => h0 (congrArg Subtype.val e)`. Establish `hact : ∀ w g y, π.locRep w g (T y) = ((ν.loc w (GeneralLinearGroup.det g) : ℂˣ) : ℂ) • T (π₀.locRep w g y)` using `fun w g y => (TR.CuspSub.finPart_toTwist ν _ y).trans (by rw [TR.CuspSub.chiDet_locGL]; rfl)`. Establish `hloc : ∀ w g (a : ℂ), locSm F w g φ = a • φ → π₀.locRep w g x₀ = a • x₀` using `fun w g a h => Subtype.ext (hz _ (fun V hV => hV (.fin (locGL F 2 w g))) a h)`. Establish `hfix₀ : ∀ w, x₀ ∈ Hi.fixd (π₀.locRep w) (K1 w (c w))` using `fun w u hu => (hloc w u 1 ((hφ.level w u hu).trans (one_smul _ _).symm)).trans (one_smul _ _)`.

Establish `hfix : ∀ w, T x₀ ∈ Hi.fixd (π.locRep w) (K1 w (c w))` using `fun w u hu => by`. Rewrite using `[hact, hν1 w _ (unit_det w hu), hfix₀ w u hu, Units.val_one, one_smul]`. Establish `hU : ∀ w, Uop w (π.locRep w) (c w) (T x₀) = lam w • T x₀` using `fun w => by`. Establish `h2` using `hz (Sd.hk k w (c w)) (fun V hV y hy => V.smul_mem _ (finsum_induction (fun z : Module.End ℂ (TR.Sm F 2) => z y ∈ V) V.zero_mem (fun _ _ => V.add_mem) fun q => hV (.fin _) y hy)) _ (heig w)`. Establish `h3` using `uop_map w (ρ' := locSm F w) π₀.V.subtype 1 (fun g y => (one_smul _ _).symm) (c w) x₀ (hfix₀ w) fun u hu => congrArg Subtype.val (hfix₀ w u hu)`.

Use `(uop_map w T.toLinearMap (ν.loc w) (hact w) (c w) x₀ (hfix₀ w) (hfix w)).trans ?_` and prove the remaining obligations. Rewrite using `[LinearEquiv.coe_coe, ← map_smul T, ← map_smul T]`. Use `congrArg T (Subtype.ext ?_)` and prove the remaining obligations. Use `Eq.trans ?_ h2` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((ν.val w : ℂˣ) : ℂ) • π₀.V.subtype (Uop w (π₀.locRep w) (c w) x₀) = (((normV w : ℝ) ^ ((k : ℝ) / 2 - 1) : ℝ) : ℂ) • Uop w (locSm F w) (c w) (π₀.V.subtype x₀)`.

Rewrite using `[h3, hν3]`. Conclude with `congrArg _ (one_smul _ _).symm`. Establish `hZ : ∀ w, π.locRep w (GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))) (T x₀) = (((ω * ν * ν).val w : ℂˣ) : ℂ) • T x₀` using `fun w => by`. Rewrite using `[hact, hloc w _ (ω.val w : ℂˣ) (Subtype.ext (funext fun g => by`. Express the relevant statement in the definitionally equal form `φ.1 (g * finGL F 2 (locGL F 2 w _)) = _`.

Rewrite using `[fin_scalar, ← GlobalTheory.CuspRep.scalar_comm, hφ.cent]`. Use the proof step `rfl)), map_smul, smul_smul,`. Use `show GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))) = atFin w (unif w) * atFin w (unif w) from Units.ext (by simp [sq]), map_mul, mul_comm, ← Units.val_mul, ← mul_assoc]`. Both sides reduce to the same expression. Establish `hsat : ∀ w, (∀ u ∈ GlobalTheory.LFun.KGL w 2, π.locRep w u (T x₀) = T x₀) → ∃ α β : ℂˣ, π.HasSat w {α, β} ∧ Uop w (π.locRep w) 0 (T x₀) = ((((normV w : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (α + β)) • T x₀ ∧ α * β = (ω * ν * ν).val w` using `fun w h => by`.

Take `⟨B, hB⟩` from `_root_.UpperTheory.Esk.HeckeRepresentationSatake.exists_sat_alt P.toClassicalTheorems π w ⟨_, hx0, h⟩`. Take `⟨α, β, rfl, h2, h3⟩` from `sat_two w (hB.2 _ (GlobalTheory.LGrp.mem_fixed.2 h) hx0)`. Conclude with `⟨α, β, hB, h2, Units.ext (smul_left_injective ℂ hx0 (h3.symm.trans (hZ w)))⟩`. Establish `hinf : ∀ v, π.HasInfChar v (infOf ![(t v : ℤ), 1 - (k : ℤ) - t v])` using `fun v => by`. Establish `h2 : π₀.HasInfChar v {(((k + 2 * t v : ℕ) : ℂ) - 1) / 2, -((((k + 2 * t v : ℕ) : ℂ) - 1) / 2)}` using `⟨rfl, fun u => cap_all π₀ hψ h0 v u _ (by`.

Rewrite using `[hz _ (fun V hV => TR.Zalg_stable (fun X => hV (.lie X)) (Algebra.subset_adjoin ⟨v, u, rfl⟩)) _ (hcap v u)]`. Simplify using `[sub_eq_add_neg])⟩`. Use `h2.twist ν using 1` and compare the differences between its conclusion and the goal. Rewrite using `[hν, expo_abs]`. Simplify using `only [infOf, Fin.univ_val_map, List.ofFn_succ, List.ofFn_zero, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]`.

Express the relevant statement in the definitionally equal form `_ ::ₘ ({_} : Multiset ℂ) = _`. Apply the tactic sequence `refine congrArg₂ _ ?_ (congrArg _ ?_) <;> simp <;> ring`. Use `⟨π, fun v => ⟨_, hinf v, ?_, fun z hz => ?_⟩, ⟨ω * ν * ν, fun v v' => ?_, ?_⟩, hinf, fun w => ⟨_, hx0, hfix w, hU w⟩, fun w hw => ?_⟩` and prove the remaining obligations. Use `Multiset.Nodup.map (fun i j e => ?_) Finset.univ.nodup` and prove the remaining obligations. Establish `e' : ![(t v : ℤ), 1 - (k : ℤ) - t v] i = ![(t v : ℤ), 1 - (k : ℤ) - t v] j` using `by exact_mod_cast add_left_cancel e`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp at e' ⊢ <;> omega`. Take `⟨i, -, rfl⟩` from `Multiset.mem_map.1 hz`. Conclude with `⟨_, add_comm _ _⟩`. Simplify using `only [HChar.locInf_mul, hν, sign_abs, mul_one]`. Conclude with `Units.ext ((sign_hol hφ hne v).trans ((sign_eq k (t v)).trans ((sign_eq k (t v')).symm.trans (sign_hol hφ hne v').symm)))`.

Take `⟨B, hl, hr, hf, hc, hX⟩` from `P.gkR F 2 π`. Use `TR.CuspSub.isSelfDualBy_of_iso B hl hr hf hc hX (P.smoR F 2 one_le_two _ _ ?_)` and prove the remaining obligations. Use `filter_upwards [GlobalTheory.CuspRep.LocSph.eventually_mem ((π.isSmooth_finPart (T x₀)).mem_nhds (show π.finPart 1 (T x₀) = T x₀ by rw [map_one]; rfl)), Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified (ω * ν * ν))] with w hw hu`. Take `⟨α, β, h2, -, h3⟩` from `hsat w (by rintro _ ⟨g, rfl⟩; exact hw g)`. Establish `e : (({α, β} : Multiset ℂˣ).map (·⁻¹)).map (· * (ω * ν * ν).val w) = {α, β}`.

Rewrite using `[← h3, Multiset.pair_comm α β]`. Simplify using `only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, inv_mul_cancel_left]`. Rewrite using `[mul_comm α β, inv_mul_cancel_left]`. Conclude with `Multiset.pair_comm α β`. Conclude with `⟨_, h2, e ▸ h2.dual.twist hu⟩`.

Take `⟨α, β, h2, h3, h4⟩` from `hsat w (by have := hfix w; rwa [hw, iwahori_level_zero_eq] at this)`. Use `⟨_, h2, ?_⟩` and prove the remaining obligations. Establish `h5` using `hU w`. Rewrite `h5` using `[hw]`. Establish `h6` using `smul_left_injective ℂ hx0 (h5.symm.trans h3)`.

Establish `h7 : (α : ℂ) * β = (ω.val w : ℂˣ) * (ν.val w : ℂˣ) * (ν.val w : ℂˣ)` using `congrArg Units.val h4`. Use `set r : ℂ := (((normV w : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) with hr`. Establish `h8 : r * r * ((ν.val w : ℂˣ) * (ν.val w : ℂˣ)) = (normV w : ℂ) ^ (k - 1)`. Rewrite using `[hν3, hr, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.rpow_add (hq w), ← Real.rpow_add (hq w), ← Real.rpow_add (hq w), show (1 / 2 + 1 / 2 + ((k : ℝ) / 2 - 1 + (k / 2 - 1))) = ((k - 1 : ℕ) : ℝ) by`. Rewrite using `[Nat.cast_sub (by omega)]; push_cast; ring, Real.rpow_natCast]`.

Simplify using the standard rewrite rules. Establish `h9 : algSat 2 (normV w) {α, β} = {r * α, r * β}`. Simplify using `only [algSat, hr, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]`. Evaluate the numerical expressions. Rewrite using `[h9, h6, ← h8, show (ω.val w : ℂˣ) * (r * r * (((ν.val w : ℂˣ) : ℂ) * (ν.val w : ℂˣ))) = r * α * (r * β) by`.

Take the linear combination `(-(r * r)) * h7]`. Simplify using `only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton, map_mul, map_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem _root_.UpperTheory.Esk.pf_HRep_alt : _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.Esk.HCap → UpperTheory.Esk.HRep := by
  intro P hC
  unfold UpperTheory.Esk.HCap at hC
  unfold UpperTheory.Esk.HRep
  intro F _ _ _ k hk t c ω hω φ lam hφ hne heig hcusp
  obtain ⟨h1, hcap⟩ := hC F (fun v => k + 2 * t v) c ω hω φ hφ
  obtain ⟨π₀, ψ, hψ, h0, hz⟩ := proj hne (P.ssR F 2 φ hcusp ⟨0, by rw [h1, zero_smul]⟩)
  set ν := GlobalTheory.HeckeGal.Model.absPow F (1 - (k : ℝ) / 2) with hν
  obtain ⟨hν1, hν2, -⟩ := GlobalTheory.HeckeGal.Model.absPow_isAbsPow F (1 - (k : ℝ) / 2)
  rw [← hν] at hν1 hν2
  have hq : ∀ w : Pl F, (0 : ℝ) < normV w := fun w =>
    Nat.cast_pos.2 (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm w))
  have hν3 : ∀ w, ((ν.val w : ℂˣ) : ℂ) = (((normV w : ℝ) ^ ((k : ℝ) / 2 - 1) : ℝ) : ℂ) := fun w => by
    rw [hν2, Complex.ofReal_cpow (hq w).le, ← Complex.ofReal_neg, neg_sub]
    rfl
  set π := π₀.twist ν
  set x₀ : π₀.V := ⟨ψ, hψ⟩
  set T := π₀.toTwist ν
  have hx0 : T x₀ ≠ 0 := (map_ne_zero_iff _ T.injective).2 fun e => h0 (congrArg Subtype.val e)
  have hact : ∀ w g y, π.locRep w g (T y) = ((ν.loc w (GeneralLinearGroup.det g) : ℂˣ) : ℂ) • T (π₀.locRep w g y) :=
    fun w g y => (TR.CuspSub.finPart_toTwist ν _ y).trans (by rw [TR.CuspSub.chiDet_locGL]; rfl)
  have hloc : ∀ w g (a : ℂ), locSm F w g φ = a • φ → π₀.locRep w g x₀ = a • x₀ := fun w g a h =>
    Subtype.ext (hz _ (fun V hV => hV (.fin (locGL F 2 w g))) a h)
  have hfix₀ : ∀ w, x₀ ∈ Hi.fixd (π₀.locRep w) (K1 w (c w)) := fun w u hu =>
    (hloc w u 1 ((hφ.level w u hu).trans (one_smul _ _).symm)).trans (one_smul _ _)
  have hfix : ∀ w, T x₀ ∈ Hi.fixd (π.locRep w) (K1 w (c w)) := fun w u hu => by
    rw [hact, hν1 w _ (unit_det w hu), hfix₀ w u hu, Units.val_one, one_smul]
  have hU : ∀ w, Uop w (π.locRep w) (c w) (T x₀) = lam w • T x₀ := fun w => by
    have h2 := hz (Sd.hk k w (c w)) (fun V hV y hy => V.smul_mem _
      (finsum_induction (fun z : Module.End ℂ (TR.Sm F 2) => z y ∈ V) V.zero_mem (fun _ _ => V.add_mem)
        fun q => hV (.fin _) y hy)) _ (heig w)
    have h3 := uop_map w (ρ' := locSm F w) π₀.V.subtype 1 (fun g y => (one_smul _ _).symm) (c w) x₀ (hfix₀ w)
      fun u hu => congrArg Subtype.val (hfix₀ w u hu)
    refine (uop_map w T.toLinearMap (ν.loc w) (hact w) (c w) x₀ (hfix₀ w) (hfix w)).trans ?_
    rw [LinearEquiv.coe_coe, ← map_smul T, ← map_smul T]
    refine congrArg T (Subtype.ext ?_)
    refine Eq.trans ?_ h2
    change ((ν.val w : ℂˣ) : ℂ) • π₀.V.subtype (Uop w (π₀.locRep w) (c w) x₀) =
      (((normV w : ℝ) ^ ((k : ℝ) / 2 - 1) : ℝ) : ℂ) • Uop w (locSm F w) (c w) (π₀.V.subtype x₀)
    rw [h3, hν3]
    exact congrArg _ (one_smul _ _).symm
  have hZ : ∀ w, π.locRep w (GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))) (T x₀) =
      (((ω * ν * ν).val w : ℂˣ) : ℂ) • T x₀ := fun w => by
    rw [hact, hloc w _ (ω.val w : ℂˣ) (Subtype.ext (funext fun g => by
      change φ.1 (g * finGL F 2 (locGL F 2 w _)) = _
      rw [fin_scalar, ← GlobalTheory.CuspRep.scalar_comm, hφ.cent]
      rfl)), map_smul, smul_smul,
      show GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))) =
        atFin w (unif w) * atFin w (unif w) from Units.ext (by simp [sq]), map_mul, mul_comm, ← Units.val_mul, ← mul_assoc]
    rfl
  have hsat : ∀ w, (∀ u ∈ GlobalTheory.LFun.KGL w 2, π.locRep w u (T x₀) = T x₀) → ∃ α β : ℂˣ, π.HasSat w {α, β} ∧
      Uop w (π.locRep w) 0 (T x₀) = ((((normV w : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (α + β)) • T x₀ ∧
      α * β = (ω * ν * ν).val w := fun w h => by
    obtain ⟨B, hB⟩ := _root_.UpperTheory.Esk.HeckeRepresentationSatake.exists_sat_alt P.toClassicalTheorems π w ⟨_, hx0, h⟩
    obtain ⟨α, β, rfl, h2, h3⟩ := sat_two w (hB.2 _ (GlobalTheory.LGrp.mem_fixed.2 h) hx0)
    exact ⟨α, β, hB, h2, Units.ext (smul_left_injective ℂ hx0 (h3.symm.trans (hZ w)))⟩
  have hinf : ∀ v, π.HasInfChar v (infOf ![(t v : ℤ), 1 - (k : ℤ) - t v]) := fun v => by
    have h2 : π₀.HasInfChar v {(((k + 2 * t v : ℕ) : ℂ) - 1) / 2, -((((k + 2 * t v : ℕ) : ℂ) - 1) / 2)} :=
      ⟨rfl, fun u => cap_all π₀ hψ h0 v u _ (by
        rw [hz _ (fun V hV => TR.Zalg_stable (fun X => hV (.lie X)) (Algebra.subset_adjoin ⟨v, u, rfl⟩)) _ (hcap v u)]
        simp [sub_eq_add_neg])⟩
    convert h2.twist ν using 1
    rw [hν, expo_abs]
    simp only [infOf, Fin.univ_val_map, List.ofFn_succ, List.ofFn_zero, Multiset.insert_eq_cons, Multiset.map_cons,
      Multiset.map_singleton]
    change _ ::ₘ ({_} : Multiset ℂ) = _
    refine congrArg₂ _ ?_ (congrArg _ ?_) <;> simp <;> ring
  refine ⟨π, fun v => ⟨_, hinf v, ?_, fun z hz => ?_⟩, ⟨ω * ν * ν, fun v v' => ?_, ?_⟩, hinf,
    fun w => ⟨_, hx0, hfix w, hU w⟩, fun w hw => ?_⟩
  · refine Multiset.Nodup.map (fun i j e => ?_) Finset.univ.nodup
    have e' : ![(t v : ℤ), 1 - (k : ℤ) - t v] i = ![(t v : ℤ), 1 - (k : ℤ) - t v] j := by exact_mod_cast add_left_cancel e
    fin_cases i <;> fin_cases j <;> simp at e' ⊢ <;> omega
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
    exact ⟨_, add_comm _ _⟩
  · simp only [HChar.locInf_mul, hν, sign_abs, mul_one]
    exact Units.ext ((sign_hol hφ hne v).trans ((sign_eq k (t v)).trans ((sign_eq k (t v')).symm.trans (sign_hol hφ hne v').symm)))
  · obtain ⟨B, hl, hr, hf, hc, hX⟩ := P.gkR F 2 π
    refine TR.CuspSub.isSelfDualBy_of_iso B hl hr hf hc hX (P.smoR F 2 one_le_two _ _ ?_)
    filter_upwards [GlobalTheory.CuspRep.LocSph.eventually_mem ((π.isSmooth_finPart (T x₀)).mem_nhds
        (show π.finPart 1 (T x₀) = T x₀ by rw [map_one]; rfl)),
      Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified (ω * ν * ν))] with w hw hu
    obtain ⟨α, β, h2, -, h3⟩ := hsat w (by rintro _ ⟨g, rfl⟩; exact hw g)
    have e : (({α, β} : Multiset ℂˣ).map (·⁻¹)).map (· * (ω * ν * ν).val w) = {α, β} := by
      rw [← h3, Multiset.pair_comm α β]
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, inv_mul_cancel_left]
      rw [mul_comm α β, inv_mul_cancel_left]
      exact Multiset.pair_comm α β
    exact ⟨_, h2, e ▸ h2.dual.twist hu⟩
  · obtain ⟨α, β, h2, h3, h4⟩ := hsat w (by have := hfix w; rwa [hw, iwahori_level_zero_eq] at this)
    refine ⟨_, h2, ?_⟩
    have h5 := hU w
    rw [hw] at h5
    have h6 := smul_left_injective ℂ hx0 (h5.symm.trans h3)
    have h7 : (α : ℂ) * β = (ω.val w : ℂˣ) * (ν.val w : ℂˣ) * (ν.val w : ℂˣ) := congrArg Units.val h4
    set r : ℂ := (((normV w : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) with hr
    have h8 : r * r * ((ν.val w : ℂˣ) * (ν.val w : ℂˣ)) = (normV w : ℂ) ^ (k - 1) := by
      rw [hν3, hr, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.rpow_add (hq w),
        ← Real.rpow_add (hq w), ← Real.rpow_add (hq w),
        show (1 / 2 + 1 / 2 + ((k : ℝ) / 2 - 1 + (k / 2 - 1))) = ((k - 1 : ℕ) : ℝ) by
          rw [Nat.cast_sub (by omega)]; push_cast; ring, Real.rpow_natCast]
      simp
    have h9 : algSat 2 (normV w) {α, β} = {r * α, r * β} := by
      simp only [algSat, hr, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
      norm_num
    rw [h9, h6, ← h8, show (ω.val w : ℂˣ) * (r * r * (((ν.val w : ℂˣ) : ℂ) * (ν.val w : ℂˣ))) = r * α * (r * β) by
      linear_combination (-(r * r)) * h7]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
      Multiset.prod_singleton, map_mul, map_add]
    ring
end UpperTheory.Esk.HeckeRepresentationSatake
end
end
