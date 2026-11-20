import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinResidueLine

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ResLine

/- English proof (translation)
Use `h.1` as an intermediate fact. Set `e` to `fun w : InfinitePlace F => InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)`. Set `ρ : ℝ →* AF F` to `{ toFun := fun x => ((fun w => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm x : Ainf F), (1 : Af F)) map_one' := Prod.ext (funext fun w => map_one _) rfl map_mul' := fun x y => Prod.ext (funext fun w => map_mul _ _ _) (mul_one _).symm }`. Establish `hρ : Continuous ρ` using `(continuous_pi fun w => (e w).symm.continuous).prodMk continuous_const`. Establish `hn : ∀ w x, ‖evInf F w (ρ x)‖ = ‖x‖` using `fun w x => (e w).symm.isometry.norm_map_of_map_zero (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm) x`.

Set `ι : AF F →* AF F ⊗[F] E` to `(algebraMap (AF F) (AF F ⊗[F] E)).toMonoidHom`. Establish `hι : Continuous ι` using `by haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩ haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)`. Conclude with `IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AF F ⊗[F] E))`. Set `d : ℕ` to `Fintype.card (InfinitePlace F)`. Establish `hd : (d : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`.

Set `u : ℝ → ℝˣ` to `fun t => Units.mk0 (Real.exp (t / (2 * d))) (Real.exp_ne_zero _)`. Establish `hu : Continuous u` using `Units.continuous_iff.2 ⟨show Continuous fun t : ℝ => Real.exp (t / (2 * d)) by fun_prop, show Continuous fun t : ℝ => (Real.exp (t / (2 * d)))⁻¹ from Continuous.inv₀ (by fun_prop) fun _ => Real.exp_ne_zero _⟩`. Use `⟨fun t => Units.map (ι.comp ρ) (u t), (Continuous.units_map (ι.comp ρ) (show Continuous (ι ∘ ρ) from hι.comp hρ)).comp hu, fun s t => ?_, fun t => congrArg (ρ (u t) ⊗ₜ[F] ·) (map_one σ), fun t => ?_⟩` and prove the remaining obligations. Rewrite using `[← map_mul]`. Conclude with `congrArg _ (Units.ext (show Real.exp _ = Real.exp _ * Real.exp _ by rw [← Real.exp_add, add_div]))`.

Establish `h1 : Algebra.norm (AF F) (Units.map (ι.comp ρ) (u t)).1 = ρ (u t) ^ 2`. Express the relevant statement in the definitionally equal form `Algebra.norm (AF F) (algebraMap (AF F) (AF F ⊗[F] E) (ρ (u t))) = _`. Use `haveI : Nontrivial (AF F) := (evInf F (Classical.arbitrary _)).toRingHom.domain_nontrivial`. Rewrite using `[Algebra.norm_algebraMap, Module.finrank_baseChange, h.2.2.1]`. Establish `h2 : ∀ v, evFin F v (ρ (u t)) = 1` using `fun v => rfl`.

Establish `h3 : ∀ w : InfinitePlace F, w.mult = 1` using `fun w => if_pos (IsTotallyReal.isReal w)`. Simplify using `only [GlobalTheory.Doubling.absE_apply, GlobalTheory.Doubling.absEv_unitFin, GlobalTheory.Doubling.absEw_unitInf, h1, map_pow, h2, h3, one_pow, nnnorm_one, finprod_one, mul_one, pow_one, NNReal.coe_prod, coe_nnnorm, norm_pow, hn, Finset.prod_const, Finset.card_univ]`. Express the relevant statement in the definitionally equal form `(‖Real.exp (t / (2 * d))‖ ^ 2) ^ d = _`. Rewrite using `[Real.norm_of_nonneg (Real.exp_pos _).le, ← pow_mul, ← Real.exp_nat_mul]`. Use `congr 1`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_real_idele_flow (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) :
    ∃ l : ℝ → (AF F ⊗[F] E)ˣ, Continuous l ∧ (∀ s t, l (s + t) = l s * l t) ∧
      (∀ t, sigR (AF F) σ (l t).1 = (l t).1) ∧ ∀ t, (absE F E (l t) : ℝ) = Real.exp t := by
  have := h.1
  let e := fun w : InfinitePlace F => InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)
  let ρ : ℝ →* AF F :=
    { toFun := fun x => ((fun w => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm x :
        Ainf F), (1 : Af F))
      map_one' := Prod.ext (funext fun w => map_one _) rfl
      map_mul' := fun x y => Prod.ext (funext fun w => map_mul _ _ _) (mul_one _).symm }
  have hρ : Continuous ρ := (continuous_pi fun w => (e w).symm.continuous).prodMk continuous_const
  have hn : ∀ w x, ‖evInf F w (ρ x)‖ = ‖x‖ := fun w x =>
    (e w).symm.isometry.norm_map_of_map_zero
      (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm) x
  let ι : AF F →* AF F ⊗[F] E := (algebraMap (AF F) (AF F ⊗[F] E)).toMonoidHom
  have hι : Continuous ι := by
    haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
    haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
    exact IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AF F ⊗[F] E))
  let d : ℕ := Fintype.card (InfinitePlace F)
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  let u : ℝ → ℝˣ := fun t => Units.mk0 (Real.exp (t / (2 * d))) (Real.exp_ne_zero _)
  have hu : Continuous u := Units.continuous_iff.2
    ⟨show Continuous fun t : ℝ => Real.exp (t / (2 * d)) by fun_prop,
      show Continuous fun t : ℝ => (Real.exp (t / (2 * d)))⁻¹ from
        Continuous.inv₀ (by fun_prop) fun _ => Real.exp_ne_zero _⟩
  refine ⟨fun t => Units.map (ι.comp ρ) (u t), (Continuous.units_map (ι.comp ρ) (show Continuous (ι ∘ ρ) from hι.comp hρ)).comp hu, fun s t => ?_,
    fun t => congrArg (ρ (u t) ⊗ₜ[F] ·) (map_one σ), fun t => ?_⟩
  · rw [← map_mul]
    exact congrArg _ (Units.ext (show Real.exp _ = Real.exp _ * Real.exp _ by rw [← Real.exp_add, add_div]))
  · have h1 : Algebra.norm (AF F) (Units.map (ι.comp ρ) (u t)).1 = ρ (u t) ^ 2 := by
      change Algebra.norm (AF F) (algebraMap (AF F) (AF F ⊗[F] E) (ρ (u t))) = _
      haveI : Nontrivial (AF F) := (evInf F (Classical.arbitrary _)).toRingHom.domain_nontrivial
      rw [Algebra.norm_algebraMap, Module.finrank_baseChange, h.2.2.1]
    have h2 : ∀ v, evFin F v (ρ (u t)) = 1 := fun v => rfl
    have h3 : ∀ w : InfinitePlace F, w.mult = 1 := fun w => if_pos (IsTotallyReal.isReal w)
    simp only [GlobalTheory.Doubling.absE_apply, GlobalTheory.Doubling.absEv_unitFin, GlobalTheory.Doubling.absEw_unitInf, h1, map_pow, h2, h3,
      one_pow, nnnorm_one, finprod_one, mul_one, pow_one, NNReal.coe_prod, coe_nnnorm, norm_pow, hn,
      Finset.prod_const, Finset.card_univ]
    change (‖Real.exp (t / (2 * d))‖ ^ 2) ^ d = _
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← pow_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp

end GlobalTheory.ResLine
