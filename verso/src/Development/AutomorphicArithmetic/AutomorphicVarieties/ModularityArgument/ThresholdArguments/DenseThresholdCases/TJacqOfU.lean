import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.JacqOfU
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
namespace UpperTheory.V.Sd
/- English proof (translation)
Set `ε : MonoidAlgebra ℂ A →ₐ[ℂ] ℂ` to `MonoidAlgebra.lift ℂ ℂ A 1`. Establish `hε : ∀ r, ν.asAlgebraHom r x = ε r • x`. Introduce `r`. Proceed by induction on `r using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`.

Consider the case `add a b ha hb => simp [ha, hb, add_smul]`. Consider the case `single a c => simp [ε, hf]`. Establish `key : ∀ z ∈ Submodule.span ℂ {z | ∃ a y, z = ν a y - y}, ∃ r, ε r ≠ 0 ∧ ν.asAlgebraHom r z = 0`. Introduce `z hz`. Proceed by induction on `hz using Submodule.span_induction with`.

Consider the case `mem z hz`. Take `⟨a, y, rfl⟩` from `hz`. Take `⟨n, hn, e⟩` from `h a y`. Use `⟨∑ i ∈ Finset.range n, MonoidAlgebra.of ℂ A a ^ i, ?_, ?_⟩` and prove the remaining obligations. Simplify using `[ε, hn]`.

Establish `e1 : ν a y - y = ν.asAlgebraHom (MonoidAlgebra.of ℂ A a - 1) y` using `by simp`. Rewrite using `[e1, ← Module.End.mul_apply, ← map_mul, geom_sum_mul, ← map_pow]`. Rewrite using `[map_sub, map_one, MonoidAlgebra.of_apply, Representation.asAlgebraHom_single_one, LinearMap.sub_apply, e]`. Simplify using the standard rewrite rules. Consider the case `zero => exact ⟨1, by simp, by simp⟩`.

Consider the case `add a b _ _ ha hb`. Take `⟨r, hr, e⟩` from `ha`. Take `⟨s, hs, e'⟩` from `hb`. Use `⟨r * s, by simp [hr, hs], ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_mul, Module.End.mul_apply, Module.End.mul_apply, e', map_zero, add_zero, ← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply, e, map_zero]`.

Consider the case `smul c a _ ha`. Take `⟨r, hr, e⟩` from `ha`. Conclude with `⟨r, hr, by rw [map_smul, e, smul_zero]⟩`. Take `⟨r, hr, e⟩` from `key x hx`. Rewrite `e` using `[hε]`.

Conclude with `(smul_eq_zero.1 e).resolve_left hr`.
-/
private theorem fixed_coinv {A V : Type} [CommGroup A] [AddCommGroup V] [Module ℂ V] (ν : Representation ℂ A V)
    (h : ∀ a y, ∃ n : ℕ, n ≠ 0 ∧ ν (a ^ n) y = y) (x : V)
    (hx : x ∈ Submodule.span ℂ {z | ∃ a y, z = ν a y - y}) (hf : ∀ a, ν a x = x) : x = 0 := by
  let ε : MonoidAlgebra ℂ A →ₐ[ℂ] ℂ := MonoidAlgebra.lift ℂ ℂ A 1
  have hε : ∀ r, ν.asAlgebraHom r x = ε r • x := by
    intro r
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp [ha, hb, add_smul]
    | single a c => simp [ε, hf]
  have key : ∀ z ∈ Submodule.span ℂ {z | ∃ a y, z = ν a y - y}, ∃ r, ε r ≠ 0 ∧ ν.asAlgebraHom r z = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, y, rfl⟩ := hz
      obtain ⟨n, hn, e⟩ := h a y
      refine ⟨∑ i ∈ Finset.range n, MonoidAlgebra.of ℂ A a ^ i, ?_, ?_⟩
      · simp [ε, hn]
      · have e1 : ν a y - y = ν.asAlgebraHom (MonoidAlgebra.of ℂ A a - 1) y := by simp
        rw [e1, ← Module.End.mul_apply, ← map_mul, geom_sum_mul, ← map_pow]
        rw [map_sub, map_one, MonoidAlgebra.of_apply, Representation.asAlgebraHom_single_one, LinearMap.sub_apply, e]
        simp
    | zero => exact ⟨1, by simp, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨r, hr, e⟩ := ha
      obtain ⟨s, hs, e'⟩ := hb
      refine ⟨r * s, by simp [hr, hs], ?_⟩
      rw [map_add, map_mul, Module.End.mul_apply, Module.End.mul_apply, e', map_zero, add_zero, ← Module.End.mul_apply,
        ← map_mul, mul_comm, map_mul, Module.End.mul_apply, e, map_zero]
    | smul c a _ ha =>
      obtain ⟨r, hr, e⟩ := ha
      exact ⟨r, hr, by rw [map_smul, e, smul_zero]⟩
  obtain ⟨r, hr, e⟩ := key x hx
  rw [hε] at e
  exact (smul_eq_zero.1 e).resolve_left hr
/- English proof (translation)
Set `ε : MonoidAlgebra ℂ T →ₐ[ℂ] ℂ` to `MonoidAlgebra.lift ℂ ℂ T ((Units.coeHom ℂ).comp χ)`. Establish `hε : ∀ r, τ.asAlgebraHom r y = ε r • y`. Introduce `r`. Proceed by induction on `r using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`.

Consider the case `add a b ha hb => simp [ha, hb, add_smul]`. Consider the case `single a c => simp [ε, he, smul_smul]`. Set `W : Submodule ℂ J` to `Submodule.span ℂ {z | ∃ t x, z = τ t x - (χ t : ℂ) • x}`. Establish `hW : W ≠ ⊤`. Introduce `hW`.

Use `letI : Module (MonoidAlgebra ℂ T) J := Module.compHom J τ.asAlgebraHom.toRingHom`. Establish `hsm : ∀ (r : MonoidAlgebra ℂ T) (x : J), r • x = τ.asAlgebraHom r x` using `fun _ _ => rfl`. Establish `hc : ∀ (c : ℂ) (x : J), c • x = (algebraMap ℂ (MonoidAlgebra ℂ T) c) • x` using `fun c x => by`. Rewrite using `[hsm, AlgHom.commutes]`. Both sides reduce to the same expression.

Establish `hfg : (⊤ : Submodule (MonoidAlgebra ℂ T) J).FG`. Use `Submodule.fg_def.2 ⟨S, hS, eq_top_iff.2 fun x _ => ?_⟩` and prove the remaining obligations. Establish `hx : x ∈ Submodule.span ℂ {z | ∃ t, ∃ s ∈ S, z = τ t s}` using `hgen ▸ Submodule.mem_top`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem z hz`.

Take `⟨t, s, hs, rfl⟩` from `hz`. Establish `: τ t s = MonoidAlgebra.of ℂ T t • s` using `by rw [hsm]; simp`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hs)`. Consider the case `zero => exact zero_mem _`.

Consider the case `add a b _ _ ha hb => exact add_mem (ha trivial) (hb trivial)`. Consider the case `smul c a _ ha => rw [hc]`. Conclude with `Submodule.smul_mem _ _ (ha trivial)`. Establish `hle : (⊤ : Submodule (MonoidAlgebra ℂ T) J) ≤ RingHom.ker ε • ⊤`. Introduce `x _`.

Establish `hx : x ∈ W` using `hW ▸ Submodule.mem_top`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨t, s, rfl⟩` from `hz`. Establish `: τ t s - (χ t : ℂ) • s = (MonoidAlgebra.of ℂ T t - algebraMap ℂ _ (χ t : ℂ)) • s`.

Rewrite using `[sub_smul, ← hc, hsm]`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Use `Submodule.smul_mem_smul ?_ trivial` and prove the remaining obligations. Rewrite using `[RingHom.mem_ker, map_sub, AlgHom.commutes]`.

Simplify using `[ε]`. Consider the case `zero => exact zero_mem _`. Consider the case `add a b _ _ ha hb => exact add_mem (ha trivial) (hb trivial)`. Consider the case `smul c a _ ha => rw [hc]`. Conclude with `Submodule.smul_mem _ _ (ha trivial)`.

Take `⟨r, hr, e⟩` from `Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul _ _ hfg hle`. Establish `e1` using `e y trivial`. Rewrite `hr` using `[RingHom.mem_ker, map_sub, map_one, sub_eq_zero]`. Rewrite `e1` using `[hsm, hε, hr, one_smul]`. Conclude with `hy e1`.

Take `⟨L, hL, hk⟩` from `Submodule.exists_le_ker_of_lt_top W (lt_top_iff_ne_top.2 hW)`. Use `⟨L, hL, fun t x => ?_⟩` and prove the remaining obligations. Use `hk (Submodule.subset_span ⟨t, x, rfl⟩)` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero, smul_eq_mul]`. Then use the resulting hypothesis.
-/
private theorem quot_of_sub {T J : Type} [CommGroup T] [AddCommGroup J] [Module ℂ J] (τ : Representation ℂ T J)
    (S : Set J) (hS : S.Finite) (hgen : Submodule.span ℂ {z | ∃ t, ∃ s ∈ S, z = τ t s} = ⊤) (χ : T →* ℂˣ) (y : J) (hy : y ≠ 0)
    (he : ∀ t, τ t y = (χ t : ℂ) • y) : ∃ L : J →ₗ[ℂ] ℂ, L ≠ 0 ∧ ∀ t x, L (τ t x) = (χ t : ℂ) * L x := by
  let ε : MonoidAlgebra ℂ T →ₐ[ℂ] ℂ := MonoidAlgebra.lift ℂ ℂ T ((Units.coeHom ℂ).comp χ)
  have hε : ∀ r, τ.asAlgebraHom r y = ε r • y := by
    intro r
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp [ha, hb, add_smul]
    | single a c => simp [ε, he, smul_smul]
  let W : Submodule ℂ J := Submodule.span ℂ {z | ∃ t x, z = τ t x - (χ t : ℂ) • x}
  have hW : W ≠ ⊤ := by
    intro hW
    letI : Module (MonoidAlgebra ℂ T) J := Module.compHom J τ.asAlgebraHom.toRingHom
    have hsm : ∀ (r : MonoidAlgebra ℂ T) (x : J), r • x = τ.asAlgebraHom r x := fun _ _ => rfl
    have hc : ∀ (c : ℂ) (x : J), c • x = (algebraMap ℂ (MonoidAlgebra ℂ T) c) • x := fun c x => by
      rw [hsm, AlgHom.commutes]; rfl
    have hfg : (⊤ : Submodule (MonoidAlgebra ℂ T) J).FG := by
      refine Submodule.fg_def.2 ⟨S, hS, eq_top_iff.2 fun x _ => ?_⟩
      have hx : x ∈ Submodule.span ℂ {z | ∃ t, ∃ s ∈ S, z = τ t s} := hgen ▸ Submodule.mem_top
      induction hx using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨t, s, hs, rfl⟩ := hz
        have : τ t s = MonoidAlgebra.of ℂ T t • s := by rw [hsm]; simp
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span hs)
      | zero => exact zero_mem _
      | add a b _ _ ha hb => exact add_mem (ha trivial) (hb trivial)
      | smul c a _ ha => rw [hc]; exact Submodule.smul_mem _ _ (ha trivial)
    have hle : (⊤ : Submodule (MonoidAlgebra ℂ T) J) ≤ RingHom.ker ε • ⊤ := by
      intro x _
      have hx : x ∈ W := hW ▸ Submodule.mem_top
      induction hx using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨t, s, rfl⟩ := hz
        have : τ t s - (χ t : ℂ) • s = (MonoidAlgebra.of ℂ T t - algebraMap ℂ _ (χ t : ℂ)) • s := by
          rw [sub_smul, ← hc, hsm]; simp
        rw [this]
        refine Submodule.smul_mem_smul ?_ trivial
        rw [RingHom.mem_ker, map_sub, AlgHom.commutes]
        simp [ε]
      | zero => exact zero_mem _
      | add a b _ _ ha hb => exact add_mem (ha trivial) (hb trivial)
      | smul c a _ ha => rw [hc]; exact Submodule.smul_mem _ _ (ha trivial)
    obtain ⟨r, hr, e⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul _ _ hfg hle
    have e1 := e y trivial
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hr
    rw [hsm, hε, hr, one_smul] at e1
    exact hy e1
  obtain ⟨L, hL, hk⟩ := Submodule.exists_le_ker_of_lt_top W (lt_top_iff_ne_top.2 hW)
  refine ⟨L, hL, fun t x => ?_⟩
  have := hk (Submodule.subset_span ⟨t, x, rfl⟩)
  rwa [LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero, smul_eq_mul] at this
section Gen
variable {K : Type} [Field K]
/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_two, add_comm]`.
-/
private theorem aff_mul (y y' : Kˣ) (x x' : K) : aff y x * aff y' x' = aff (y * y') (x + y * x') := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_two, add_comm]
/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [aff]`.
-/
private theorem aff_one : aff (1 : Kˣ) (0 : K) = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff]
private def tor : Kˣ →* GL (Fin 2) K where
  toFun a := aff a 0
  map_one' := aff_one
  map_mul' a b := by simp [aff_mul]
private def uni (O : Subring K) : Multiplicative O →* GL (Fin 2) K where
  toFun a := aff 1 ((a.toAdd : O) : K)
  map_one' := aff_one
  map_mul' a b := by simp [aff_mul]
private def sw : GL (Fin 2) K where
  val := !![0, 1; 1, 0]
  inv := !![0, 1; 1, 0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
/- English proof (translation)
Establish `hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 ≠ 0`. Use `(Matrix.GeneralLinearGroup.det g).ne_zero` as an intermediate fact. Rewrite `this` using `[Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]`. Then use the resulting hypothesis. Distinguish the cases in `h : g 1 0 ≠ 0 ∧ g 1 1 / g 1 0 ∈ O`. Take `⟨h0, h1⟩` from `h`.

Use `⟨Units.mk0 _ h0, Units.mk0 (-(g 0 0 * g 1 1 - g 0 1 * g 1 0) / g 1 0 ^ 2) (div_ne_zero (neg_ne_zero.2 hdet) (pow_ne_zero _ h0)), g 0 0 / g 1 0, ⟨_, h1⟩, Or.inl ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [aff, sw, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply] <;> field_simp <;> ring`. Establish `h0 : g 1 1 ≠ 0`.

Introduce `h0`. Apply `h` to reduce the goal to its premises. Use `⟨fun h1 => hdet (by simp [h0, h1]), by simp [h0]⟩` and prove the remaining obligations. Establish `h1 : g 1 0 / g 1 1 ∈ O`. Distinguish the cases in `h2 : g 1 0 = 0`.

Simplify using `[h2]`. Use `(hO (g 1 1 / g 1 0)).resolve_left fun h3 => h ⟨h2, h3⟩` as an intermediate fact. Rewrite `this` using `[inv_div]`. Then use the resulting hypothesis. Use `⟨Units.mk0 _ h0, Units.mk0 ((g 0 0 * g 1 1 - g 0 1 * g 1 0) / g 1 1 ^ 2) (div_ne_zero hdet (pow_ne_zero _ h0)), g 0 1 / g 1 1, ⟨_, h1⟩, Or.inr ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises.

Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [aff, sw, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply] <;> field_simp <;> ring`.
-/
private theorem iwasawa (O : Subring K) (hO : ∀ x : K, x ∈ O ∨ x⁻¹ ∈ O) (g : GL (Fin 2) K) :
    ∃ (d a : Kˣ) (x : K) (u : O), g = Matrix.GeneralLinearGroup.scalar (Fin 2) d * (aff a x * (sw * aff 1 (u : K))) ∨
      g = Matrix.GeneralLinearGroup.scalar (Fin 2) d * (aff a x * (sw * (aff 1 (u : K) * sw))) := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det g).ne_zero
    rwa [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] at this
  by_cases h : g 1 0 ≠ 0 ∧ g 1 1 / g 1 0 ∈ O
  · obtain ⟨h0, h1⟩ := h
    refine ⟨Units.mk0 _ h0, Units.mk0 (-(g 0 0 * g 1 1 - g 0 1 * g 1 0) / g 1 0 ^ 2)
      (div_ne_zero (neg_ne_zero.2 hdet) (pow_ne_zero _ h0)), g 0 0 / g 1 0, ⟨_, h1⟩, Or.inl ?_⟩
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [aff, sw, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply] <;> field_simp <;> ring
  · have h0 : g 1 1 ≠ 0 := by
      intro h0
      apply h
      refine ⟨fun h1 => hdet (by simp [h0, h1]), by simp [h0]⟩
    have h1 : g 1 0 / g 1 1 ∈ O := by
      by_cases h2 : g 1 0 = 0
      · simp [h2]
      · have := (hO (g 1 1 / g 1 0)).resolve_left fun h3 => h ⟨h2, h3⟩
        rwa [inv_div] at this
    refine ⟨Units.mk0 _ h0, Units.mk0 ((g 0 0 * g 1 1 - g 0 1 * g 1 0) / g 1 1 ^ 2)
      (div_ne_zero hdet (pow_ne_zero _ h0)), g 0 1 / g 1 1, ⟨_, h1⟩, Or.inr ?_⟩
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [aff, sw, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply] <;> field_simp <;> ring
variable {V : Type} [AddCommGroup V] [Module ℂ V]
/- English proof (translation)
Simplify using `only [← Module.End.mul_apply, ← map_mul, aff_mul]`. Simplify using the standard rewrite rules.
-/
private theorem act_tor_uni (ρ : Representation ℂ (GL (Fin 2) K) V) (a : Kˣ) (x : K) (y : V) :
    ρ (aff a 0) (ρ (aff 1 x) y) = ρ (aff 1 (a * x)) (ρ (aff a 0) y) := by
  simp only [← Module.End.mul_apply, ← map_mul, aff_mul]
  simp
/- English proof (translation)
Simplify using `only [← Module.End.mul_apply, ← map_mul, aff_mul]`. Simplify using the standard rewrite rules.
-/
private theorem act_aff (ρ : Representation ℂ (GL (Fin 2) K) V) (a : Kˣ) (x : K) (y : V) :
    ρ (aff a x) y = ρ (aff 1 x) (ρ (aff a 0) y) := by
  simp only [← Module.End.mul_apply, ← map_mul, aff_mul]
  simp
/- English proof (translation)
Introduce `hmem`. Set `ν : Representation ℂ (Multiplicative O) V` to `ρ.comp (uni O)`. Set `W : Submodule ℂ V` to `Submodule.span ℂ {z | ∃ a y, z = ν a y - y}`. Establish `hW : ∀ x ∈ O, ∀ y, ρ (aff 1 x) y - y ∈ W` using `fun x hx y => Submodule.subset_span ⟨Multiplicative.ofAdd ⟨x, hx⟩, y, rfl⟩`. Establish `h1 : ∀ z ∈ Submodule.span ℂ {z | ∃ x y, z = ρ (aff 1 x) y - y}, ∀ᶠ m : ℕ in Filter.atTop, ρ (aff (π ^ m) 0) z ∈ W`.

Introduce `z hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨x, y, rfl⟩` from `hz`. Take `⟨m, hm⟩` from `hπ' x`.

Use `filter_upwards [Filter.eventually_ge_atTop m] with j hj`. Rewrite using `[map_sub, act_tor_uni]`. Use `hW _ ?_ _` and prove the remaining obligations. Take `⟨i, rfl⟩` from `Nat.exists_eq_add_of_le' hj`. Rewrite using `[Units.val_pow_eq_pow_val, pow_add, mul_assoc]`.

Conclude with `mul_mem (pow_mem hπ _) hm`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => filter_upwards [ha, hb] with j h h'`. Rewrite using `[map_add]`. Conclude with `add_mem h h'`.

Consider the case `smul c a _ ha => filter_upwards [ha] with j h`. Rewrite using `[map_smul]`. Conclude with `W.smul_mem _ h`. Establish `h2 : ∀ m : ℕ, ρ (aff (π ^ m) 0) v ∈ W → v ∈ W`. Introduce `m`.

Proceed by induction on `m with`. Consider the case `zero => simp [aff_one]`. Consider the case `succ j ih`. Introduce `h`. Apply `ih` to reduce the goal to its premises.

Rewrite using `[← W.smul_mem_iff lam.ne_zero, ← map_smul, ← hU, map_sum]`. Use `sum_mem fun u _ => ?_` and prove the remaining obligations. Establish `e : ρ (aff (π ^ j) 0) (ρ (aff π (u : K)) v) = ρ (aff 1 ((π : K) ^ j * u)) (ρ (aff (π ^ (j + 1)) 0) v)`. Simplify using `only [← Module.End.mul_apply, ← map_mul, aff_mul]`. Simplify using `[pow_succ]`.

Rewrite using `[e]`. Simplify using `using add_mem (hW _ (mul_mem (pow_mem hπ j) u.2) (ρ (aff (π ^ (j + 1)) 0) v)) h`. Take `⟨m, hm⟩` from `(h1 v hmem).exists`. Use `hv (fixed_coinv ν (fun a y => ?_) v (h2 m hm) fun a => hf _ a.toAdd.2)` and prove the remaining obligations. Take `⟨n, hn, e⟩` from `htor (a.toAdd : O) y`.

Use `⟨n, hn, ?_⟩` and prove the remaining obligations. Rewrite using `[← e]`. Simplify using `[ν, uni, e]`.
-/
private theorem not_mem_ker (O : Subring K) (π : Kˣ) (hπ : (π : K) ∈ O) (hπ' : ∀ x : K, ∃ m : ℕ, (π : K) ^ m * x ∈ O)
    (ρ : Representation ℂ (GL (Fin 2) K) V) (htor : ∀ (a : K) y, ∃ n : ℕ, n ≠ 0 ∧ ρ (aff 1 (n * a)) y = y)
    (v : V) (hv : v ≠ 0) (hf : ∀ x ∈ O, ρ (aff 1 x) v = v) (S : Finset O) (lam : ℂˣ)
    (hU : ∑ u ∈ S, ρ (aff π (u : K)) v = (lam : ℂ) • v) :
    v ∉ Submodule.span ℂ {z | ∃ x y, z = ρ (aff 1 x) y - y} := by
  intro hmem
  let ν : Representation ℂ (Multiplicative O) V := ρ.comp (uni O)
  let W : Submodule ℂ V := Submodule.span ℂ {z | ∃ a y, z = ν a y - y}
  have hW : ∀ x ∈ O, ∀ y, ρ (aff 1 x) y - y ∈ W := fun x hx y =>
    Submodule.subset_span ⟨Multiplicative.ofAdd ⟨x, hx⟩, y, rfl⟩
  have h1 : ∀ z ∈ Submodule.span ℂ {z | ∃ x y, z = ρ (aff 1 x) y - y},
      ∀ᶠ m : ℕ in Filter.atTop, ρ (aff (π ^ m) 0) z ∈ W := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, y, rfl⟩ := hz
      obtain ⟨m, hm⟩ := hπ' x
      filter_upwards [Filter.eventually_ge_atTop m] with j hj
      rw [map_sub, act_tor_uni]
      refine hW _ ?_ _
      obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' hj
      rw [Units.val_pow_eq_pow_val, pow_add, mul_assoc]
      exact mul_mem (pow_mem hπ _) hm
    | zero => simp
    | add a b _ _ ha hb =>
      filter_upwards [ha, hb] with j h h'
      rw [map_add]
      exact add_mem h h'
    | smul c a _ ha =>
      filter_upwards [ha] with j h
      rw [map_smul]
      exact W.smul_mem _ h
  have h2 : ∀ m : ℕ, ρ (aff (π ^ m) 0) v ∈ W → v ∈ W := by
    intro m
    induction m with
    | zero => simp [aff_one]
    | succ j ih =>
      intro h
      apply ih
      rw [← W.smul_mem_iff lam.ne_zero, ← map_smul, ← hU, map_sum]
      refine sum_mem fun u _ => ?_
      have e : ρ (aff (π ^ j) 0) (ρ (aff π (u : K)) v) = ρ (aff 1 ((π : K) ^ j * u)) (ρ (aff (π ^ (j + 1)) 0) v) := by
        simp only [← Module.End.mul_apply, ← map_mul, aff_mul]
        simp [pow_succ]
      rw [e]
      simpa using add_mem (hW _ (mul_mem (pow_mem hπ j) u.2) (ρ (aff (π ^ (j + 1)) 0) v)) h
  obtain ⟨m, hm⟩ := (h1 v hmem).exists
  refine hv (fixed_coinv ν (fun a y => ?_) v (h2 m hm) fun a => hf _ a.toAdd.2)
  obtain ⟨n, hn, e⟩ := htor (a.toAdd : O) y
  refine ⟨n, hn, ?_⟩
  rw [← e]
  simp [ν, uni, e]
/- English proof (translation)
Set `N : Submodule ℂ V` to `Submodule.span ℂ {z | ∃ x y, z = ρ (aff 1 x) y - y}`. Establish `hN : ∀ a : Kˣ, N ≤ N.comap ((ρ.comp tor) a)`. Introduce `a`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, y, rfl⟩`.

Express the relevant statement in the definitionally equal form `ρ (aff a 0) _ ∈ N`. Rewrite using `[map_sub, act_tor_uni]`. Conclude with `Submodule.subset_span ⟨_, _, rfl⟩`. Set `τ : Representation ℂ Kˣ (V ⧸ N)` to `Representation.quotient (ρ.comp tor) N hN`. Establish `hτ : ∀ a y, τ a (N.mkQ y) = N.mkQ (ρ (aff a 0) y)` using `fun _ _ => rfl`.

Establish `hq : ∀ a x y, N.mkQ (ρ (aff a x) y) = τ a (N.mkQ y)`. Introduce `a x y`. Rewrite using `[hτ, act_aff]`. Conclude with `(Submodule.Quotient.eq N).2 (Submodule.subset_span ⟨_, _, rfl⟩)`. Establish `hy : N.mkQ v ≠ 0` using `fun h => not_mem_ker O π hπ hπ' ρ htor v hv hf S lam hU ((Submodule.Quotient.mk_eq_zero N).1 h)`.

Establish `he : (S.card : ℂ) • τ π (N.mkQ v) = (lam : ℂ) • N.mkQ v`. Rewrite using `[← map_smul N.mkQ, ← hU, map_sum]`. Simplify using `only [hq, Finset.sum_const, Nat.cast_smul_eq_nsmul]`. Establish `hS : (S.card : ℂ) ≠ 0`. Introduce `h`.

Rewrite `he` using `[h, zero_smul]`. Conclude with `smul_ne_zero lam.ne_zero hy he.symm`. Set `H : Subgroup Kˣ` to `{ carrier := {a | ∃ c : ℂˣ, τ a (N.mkQ v) = (c : ℂ) • N.mkQ v} one_mem' := ⟨1, by simp⟩ mul_mem' := by`. Introduce and unpack `a b ⟨c, hc⟩ ⟨d, hd⟩`. Conclude with `⟨d * c, by rw [map_mul, Module.End.mul_apply, hd, map_smul, hc, smul_smul, Units.val_mul]⟩`.

Use the proof step `inv_mem' := by`. Introduce and unpack `a ⟨c, hc⟩`. Use `⟨c⁻¹, ?_⟩` and prove the remaining obligations. Use `congrArg (τ a⁻¹) hc` as an intermediate fact. Rewrite `this` using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, map_smul]`.

Use `conv_rhs => rw [this, smul_smul]`. Simplify using `}`. Establish `hπH : π ∈ H` using `⟨lam * (Units.mk0 _ hS)⁻¹, by`. Apply `smul_right_injective _ hS` to reduce the goal to its premises. Simplify using `only [he, smul_smul]`.

Use `congr 1`. Simplify using `only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]`. Use the proof step `field_simp⟩`. Establish `hH : ∀ a, a ∈ H`. Introduce `a`.

Take `⟨n, u, h1, rfl⟩` from `hdec a`. Conclude with `mul_mem ⟨1, by rw [hτ, hu u h1]; simp⟩ (zpow_mem hπH n)`. Use `choose c hc using (show ∀ a, ∃ c : ℂˣ, τ a (N.mkQ v) = (c : ℂ) • N.mkQ v from hH)`. Set `μ : Kˣ →* ℂˣ` to `MonoidHom.mk' c fun a b => Units.ext (smul_left_injective ℂ hy (by`. Simplify using `only [← hc]`.

Rewrite using `[Units.val_mul, mul_comm (c a : ℂ), mul_smul, ← hc, ← map_smul, ← hc, map_mul, Module.End.mul_apply]))`. Set `S₀ : Set V` to `(Set.range fun x : O => ρ (aff 1 (x : K)) v) ∪ Set.range fun x : O => ρ (aff 1 (x : K)) (ρ sw v)`. Establish `hgen : Submodule.span ℂ {z | ∃ t, ∃ s ∈ (fun y => N.mkQ (ρ sw y)) '' S₀, z = τ t s} = ⊤`. Take `⟨-, hi⟩` from `(isIrreducible_iff ρ).1 hirr`. Establish `ht : Submodule.span ℂ (Set.range fun g => ρ g v) = ⊤`.

Use `(hi _ fun g => ?_).resolve_left fun h => hv ?_` and prove the remaining obligations. Establish `: Submodule.span ℂ (Set.range fun g => ρ g v) ≤ (Submodule.span ℂ (Set.range fun g => ρ g v)).comap (ρ g)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨h, rfl⟩`. Conclude with `Submodule.subset_span ⟨g * h, by simp⟩`.

Conclude with `this`. Rewrite using `[← Submodule.mem_bot ℂ, ← h]`. Conclude with `Submodule.subset_span ⟨1, by simp⟩`. Establish `hle : Submodule.span ℂ (Set.range fun g => ρ g v) ≤ (Submodule.span ℂ {z | ∃ t, ∃ s ∈ (fun y => N.mkQ (ρ sw y)) '' S₀, z = τ t s}).comap N.mkQ`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨g, rfl⟩`. Express the relevant statement in the definitionally equal form `N.mkQ (ρ g v) ∈ Submodule.span ℂ _`. Take `⟨d, a, x, u, rfl | rfl⟩` from `iwasawa O hO g`. Simplify using `only [map_mul, Module.End.mul_apply, hω, map_smul, hq]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, _, ⟨_, Or.inl ⟨u, rfl⟩, rfl⟩, rfl⟩)`.

Simplify using `only [map_mul, Module.End.mul_apply, hω, map_smul, hq]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, _, ⟨_, Or.inr ⟨u, rfl⟩, rfl⟩, rfl⟩)`. Use `eq_top_iff.2 fun z _ => ?_` and prove the remaining obligations. Take `⟨y, rfl⟩` from `N.mkQ_surjective z`. Conclude with `hle (ht ▸ Submodule.mem_top)`.

Take `⟨L, hL, hL'⟩` from `quot_of_sub τ _ (((hfin v).union (hfin _)).image _) hgen μ _ hy hc`. Use `⟨μ, ω / μ, L ∘ₗ N.mkQ, fun h => hL ?_, fun x hx => ?_, ?_, fun a d x y => ?_⟩` and prove the remaining obligations. Conclude with `LinearMap.ext fun z => by`. Take `⟨y, rfl⟩` from `N.mkQ_surjective z`. Conclude with `LinearMap.congr_fun h y`.

Use `Units.ext (smul_left_injective ℂ hy ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(c x : ℂ) • _ = _`. Simplify using `only [← hc, hτ, hu x hx]`. Simplify using the standard rewrite rules. Use `smul_left_injective ℂ hy ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `((S.card : ℂ) * (c π : ℂ)) • _ = _`. Simplify using `only [mul_smul, ← hc, he]`. Simplify using `only [map_mul, Module.End.mul_apply, hω, map_smul, LinearMap.comp_apply, hq, hL', _root_.map_div, MonoidHom.div_apply, smul_eq_mul, Units.val_mul, Units.val_div_eq_div_val]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem gen (O : Subring K) (hO : ∀ x : K, x ∈ O ∨ x⁻¹ ∈ O) (π : Kˣ) (hπ : (π : K) ∈ O)
    (hπ' : ∀ x : K, ∃ m : ℕ, (π : K) ^ m * x ∈ O) (U : Kˣ → Prop) (hdec : ∀ a : Kˣ, ∃ (n : ℤ) (u : Kˣ), U u ∧ a = u * π ^ n)
    (ρ : Representation ℂ (GL (Fin 2) K) V) (hirr : ρ.IsIrreducible)
    (htor : ∀ (a : K) y, ∃ n : ℕ, n ≠ 0 ∧ ρ (aff 1 (n * a)) y = y)
    (hfin : ∀ y, (Set.range fun x : O => ρ (aff 1 (x : K)) y).Finite)
    (ω : Kˣ →* ℂˣ) (hω : ∀ z y, ρ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) y = (ω z : ℂ) • y)
    (v : V) (hv : v ≠ 0) (hf : ∀ x ∈ O, ρ (aff 1 x) v = v) (hu : ∀ u, U u → ρ (aff u 0) v = v) (S : Finset O) (lam : ℂˣ)
    (hU : ∑ u ∈ S, ρ (aff π (u : K)) v = (lam : ℂ) • v) :
    ∃ (μ₁ μ₂ : Kˣ →* ℂˣ) (L : V →ₗ[ℂ] ℂ), L ≠ 0 ∧ (∀ x, U x → μ₁ x = 1) ∧
      (S.card : ℂ) * (μ₁ π : ℂ) = lam ∧ ∀ (a d : Kˣ) (x : K) y,
        L (ρ (Matrix.GeneralLinearGroup.scalar (Fin 2) d * aff (a / d) x) y) = ((μ₁ a * μ₂ d : ℂˣ) : ℂ) * L y := by
  let N : Submodule ℂ V := Submodule.span ℂ {z | ∃ x y, z = ρ (aff 1 x) y - y}
  have hN : ∀ a : Kˣ, N ≤ N.comap ((ρ.comp tor) a) := by
    intro a
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, y, rfl⟩
    change ρ (aff a 0) _ ∈ N
    rw [map_sub, act_tor_uni]
    exact Submodule.subset_span ⟨_, _, rfl⟩
  let τ : Representation ℂ Kˣ (V ⧸ N) := Representation.quotient (ρ.comp tor) N hN
  have hτ : ∀ a y, τ a (N.mkQ y) = N.mkQ (ρ (aff a 0) y) := fun _ _ => rfl
  have hq : ∀ a x y, N.mkQ (ρ (aff a x) y) = τ a (N.mkQ y) := by
    intro a x y
    rw [hτ, act_aff]
    exact (Submodule.Quotient.eq N).2 (Submodule.subset_span ⟨_, _, rfl⟩)
  have hy : N.mkQ v ≠ 0 := fun h =>
    not_mem_ker O π hπ hπ' ρ htor v hv hf S lam hU ((Submodule.Quotient.mk_eq_zero N).1 h)
  have he : (S.card : ℂ) • τ π (N.mkQ v) = (lam : ℂ) • N.mkQ v := by
    rw [← map_smul N.mkQ, ← hU, map_sum]
    simp only [hq, Finset.sum_const, Nat.cast_smul_eq_nsmul]
  have hS : (S.card : ℂ) ≠ 0 := by
    intro h
    rw [h, zero_smul] at he
    exact smul_ne_zero lam.ne_zero hy he.symm
  let H : Subgroup Kˣ :=
    { carrier := {a | ∃ c : ℂˣ, τ a (N.mkQ v) = (c : ℂ) • N.mkQ v}
      one_mem' := ⟨1, by simp⟩
      mul_mem' := by
        rintro a b ⟨c, hc⟩ ⟨d, hd⟩
        exact ⟨d * c, by rw [map_mul, Module.End.mul_apply, hd, map_smul, hc, smul_smul, Units.val_mul]⟩
      inv_mem' := by
        rintro a ⟨c, hc⟩
        refine ⟨c⁻¹, ?_⟩
        have := congrArg (τ a⁻¹) hc
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, map_smul] at this
        conv_rhs => rw [this, smul_smul]
        simp }
  have hπH : π ∈ H := ⟨lam * (Units.mk0 _ hS)⁻¹, by
    apply smul_right_injective _ hS
    simp only [he, smul_smul]
    congr 1
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp⟩
  have hH : ∀ a, a ∈ H := by
    intro a
    obtain ⟨n, u, h1, rfl⟩ := hdec a
    exact mul_mem ⟨1, by rw [hτ, hu u h1]; simp⟩ (zpow_mem hπH n)
  choose c hc using (show ∀ a, ∃ c : ℂˣ, τ a (N.mkQ v) = (c : ℂ) • N.mkQ v from hH)
  let μ : Kˣ →* ℂˣ := MonoidHom.mk' c fun a b => Units.ext (smul_left_injective ℂ hy (by
    simp only [← hc]
    rw [Units.val_mul, mul_comm (c a : ℂ), mul_smul, ← hc, ← map_smul, ← hc, map_mul, Module.End.mul_apply]))
  let S₀ : Set V := (Set.range fun x : O => ρ (aff 1 (x : K)) v) ∪ Set.range fun x : O => ρ (aff 1 (x : K)) (ρ sw v)
  have hgen : Submodule.span ℂ {z | ∃ t, ∃ s ∈ (fun y => N.mkQ (ρ sw y)) '' S₀, z = τ t s} = ⊤ := by
    obtain ⟨-, hi⟩ := (isIrreducible_iff ρ).1 hirr
    have ht : Submodule.span ℂ (Set.range fun g => ρ g v) = ⊤ := by
      refine (hi _ fun g => ?_).resolve_left fun h => hv ?_
      · have : Submodule.span ℂ (Set.range fun g => ρ g v) ≤ (Submodule.span ℂ (Set.range fun g => ρ g v)).comap (ρ g) := by
          refine Submodule.span_le.2 ?_
          rintro _ ⟨h, rfl⟩
          exact Submodule.subset_span ⟨g * h, by simp⟩
        exact this
      · rw [← Submodule.mem_bot ℂ, ← h]
        exact Submodule.subset_span ⟨1, by simp⟩
    have hle : Submodule.span ℂ (Set.range fun g => ρ g v) ≤
        (Submodule.span ℂ {z | ∃ t, ∃ s ∈ (fun y => N.mkQ (ρ sw y)) '' S₀, z = τ t s}).comap N.mkQ := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, rfl⟩
      change N.mkQ (ρ g v) ∈ Submodule.span ℂ _
      obtain ⟨d, a, x, u, rfl | rfl⟩ := iwasawa O hO g
      · simp only [map_mul, Module.End.mul_apply, hω, map_smul, hq]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, _, ⟨_, Or.inl ⟨u, rfl⟩, rfl⟩, rfl⟩)
      · simp only [map_mul, Module.End.mul_apply, hω, map_smul, hq]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, _, ⟨_, Or.inr ⟨u, rfl⟩, rfl⟩, rfl⟩)
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨y, rfl⟩ := N.mkQ_surjective z
    exact hle (ht ▸ Submodule.mem_top)
  obtain ⟨L, hL, hL'⟩ := quot_of_sub τ _ (((hfin v).union (hfin _)).image _) hgen μ _ hy hc
  refine ⟨μ, ω / μ, L ∘ₗ N.mkQ, fun h => hL ?_, fun x hx => ?_, ?_, fun a d x y => ?_⟩
  · exact LinearMap.ext fun z => by
      obtain ⟨y, rfl⟩ := N.mkQ_surjective z
      exact LinearMap.congr_fun h y
  · refine Units.ext (smul_left_injective ℂ hy ?_)
    change (c x : ℂ) • _ = _
    simp only [← hc, hτ, hu x hx]
    simp
  · refine smul_left_injective ℂ hy ?_
    change ((S.card : ℂ) * (c π : ℂ)) • _ = _
    simp only [mul_smul, ← hc, he]
  · simp only [map_mul, Module.End.mul_apply, hω, map_smul, LinearMap.comp_apply, hq, hL', _root_.map_div, MonoidHom.div_apply,
      smul_eq_mul, Units.val_mul, Units.val_div_eq_div_val]
    ring
end Gen
/- English proof (translation)
Use `⟨aff u x, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Matrix.vecMul ![0, 1] ((aff u x : Matrix (Fin 2) (Fin 2) _).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c))) = ![0, 1]`. Use extensionality with `i`. Apply the tactic sequence `fin_cases i <;> simp [aff, Matrix.vecMul, dotProduct, Fin.sum_univ_two]`. Apply `Units.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `(aff u x : Matrix (Fin 2) (Fin 2) _).map (w.adicCompletionIntegers F).subtype = _`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [aff]`.
-/
private theorem affine_mem_iwahori_level {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (c : ℕ)
    (u : (w.adicCompletionIntegers F)ˣ) (x : w.adicCompletionIntegers F) :
    aff (Units.map (w.adicCompletionIntegers F).subtype.toMonoidHom u) (x : w.adicCompletion F) ∈ K1 w c := by
  refine ⟨aff u x, ?_, ?_⟩
  · change Matrix.vecMul ![0, 1] ((aff u x : Matrix (Fin 2) (Fin 2) _).map
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c))) = ![0, 1]
    ext i
    fin_cases i <;> simp [aff, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  · apply Units.ext
    change (aff u x : Matrix (Fin 2) (Fin 2) _).map (w.adicCompletionIntegers F).subtype = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [aff]
/- English proof (translation)
Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `refine continuous_matrix fun i j => ?_ fin_cases i <;> fin_cases j <;> simp [aff] <;> fun_prop`. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Continuous fun x : K => (aff (1 : Kˣ) x).inv i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [aff] <;> fun_prop`.
-/
private theorem cont_uni {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K] :
    Continuous fun x : K => aff (1 : Kˣ) x := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    change Continuous fun x : K => (aff (1 : Kˣ) x).inv i j
    fin_cases i <;> fin_cases j <;> simp [aff] <;> fun_prop
section Loc
variable {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))
/- English proof (translation)
Use `letI := GlobalTheory.LocalData.complRel w`. Use `haveI := GlobalTheory.LocalData.isLocalField w`. Take `⟨ω, -, hω⟩` from `GlobalTheory.LocGL.exists_smooth_hasCentralChar σ.smooth σ.irred`. Conclude with `⟨ω, hω⟩`.
-/
private theorem cent (σ : SmIrr (GL (Fin 2) (w.adicCompletion F))) : ∃ ω : (w.adicCompletion F)ˣ →* ℂˣ,
    ∀ z y, σ.ρ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) y = (ω z : ℂ) • y := by
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  obtain ⟨ω, -, hω⟩ := GlobalTheory.LocGL.exists_smooth_hasCentralChar σ.smooth σ.irred
  exact ⟨ω, hω⟩
/- English proof (translation)
Use `haveI := Formalism.UG.P.glint_finite_residueField w`. Use `letI := Fintype.ofFinite (IsLocalRing.ResidueField (w.adicCompletionIntegers F))`. Use `choose s hs using (IsLocalRing.residue_surjective (R := w.adicCompletionIntegers F))`. Establish `hsi : Function.Injective s` using `Function.RightInverse.injective hs`. Use `⟨Finset.univ.image s, ⟨fun _ _ => trivial, ?_, fun r _ => ⟨s r, by simp, hs r⟩⟩, ?_⟩` and prove the remaining obligations.

Introduce `a ha b hb h`. Take `⟨a, -, rfl⟩` from `Finset.mem_image.1 ha`. Take `⟨b, -, rfl⟩` from `Finset.mem_image.1 hb`. Rewrite `h` using `[hs, hs]`. Rewrite using `[h]`.

Rewrite using `[Finset.card_image_of_injective _ hsi, Finset.card_univ, ← Nat.card_eq_fintype_card, Formalism.UG.P.tjcosets_card_residue]`. Simplify using `[normV, Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]`.
-/
private theorem reps : ∃ S : Finset (w.adicCompletionIntegers F),
    Set.BijOn (IsLocalRing.residue _) (S : Set (w.adicCompletionIntegers F)) Set.univ ∧ S.card = normV w := by
  classical
  haveI := Formalism.UG.P.glint_finite_residueField w
  letI := Fintype.ofFinite (IsLocalRing.ResidueField (w.adicCompletionIntegers F))
  choose s hs using (IsLocalRing.residue_surjective (R := w.adicCompletionIntegers F))
  have hsi : Function.Injective s := Function.RightInverse.injective hs
  refine ⟨Finset.univ.image s, ⟨fun _ _ => trivial, ?_, fun r _ => ⟨s r, by simp, hs r⟩⟩, ?_⟩
  · intro a ha b hb h
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hb
    rw [hs, hs] at h
    rw [h]
  · rw [Finset.card_image_of_injective _ hsi, Finset.card_univ, ← Nat.card_eq_fintype_card, Formalism.UG.P.tjcosets_card_residue]
    simp [normV, Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
variable {w}
/- English proof (translation)
Rewrite using `[ValuationSubring.mem_toSubring, HeightOneSpectrum.mem_adicCompletionIntegers, hπ, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem pi_mem {π : w.adicCompletion F} (hπ : Valued.v π = WithZero.exp (-1 : ℤ)) :
    π ∈ (w.adicCompletionIntegers F).toSubring := by
  rw [ValuationSubring.mem_toSubring, HeightOneSpectrum.mem_adicCompletionIntegers, hπ, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega
/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Conclude with `⟨0, by simp [hx]⟩`. Establish `h0 : Valued.v x ≠ 0` using `(Valuation.ne_zero_iff _).2 hx`. Take `⟨n, hn⟩ : ∃ n : ℤ, Valued.v x = WithZero.exp n` from `⟨_, (WithZero.exp_log h0).symm⟩`. Use `⟨n.toNat, ?_⟩` and prove the remaining obligations.

Rewrite using `[ValuationSubring.mem_toSubring, HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_pow, hπ, ← WithZero.exp_nsmul, hn, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Simplify using `only [smul_neg, nsmul_eq_mul, mul_one]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem pi_pow {π : w.adicCompletion F} (hπ : Valued.v π = WithZero.exp (-1 : ℤ)) (x : w.adicCompletion F) :
    ∃ m : ℕ, π ^ m * x ∈ (w.adicCompletionIntegers F).toSubring := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  have h0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v x = WithZero.exp n := ⟨_, (WithZero.exp_log h0).symm⟩
  refine ⟨n.toNat, ?_⟩
  rw [ValuationSubring.mem_toSubring, HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_pow, hπ, ← WithZero.exp_nsmul,
    hn, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
  simp only [smul_neg, nsmul_eq_mul, mul_one]
  omega
/- English proof (translation)
Establish `h0 : Valued.v (a : w.adicCompletion F) ≠ 0` using `(Valuation.ne_zero_iff _).2 a.ne_zero`. Take `⟨n, hn⟩ : ∃ n : ℤ, Valued.v (a : w.adicCompletion F) = WithZero.exp n` from `⟨_, (WithZero.exp_log h0).symm⟩`. Use `⟨-n, a * π ^ n, ?_, by simp⟩` and prove the remaining obligations. Rewrite using `[IsUnitAt, Units.val_mul, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hπ, hn, ← WithZero.exp_zsmul, ← WithZero.exp_add]`. Simplify using the standard rewrite rules.
-/
private theorem pi_dec {π : (w.adicCompletion F)ˣ} (hπ : Valued.v (π : w.adicCompletion F) = WithZero.exp (-1 : ℤ))
    (a : (w.adicCompletion F)ˣ) : ∃ (n : ℤ) (u : (w.adicCompletion F)ˣ), IsUnitAt w u ∧ a = u * π ^ n := by
  have h0 : Valued.v (a : w.adicCompletion F) ≠ 0 := (Valuation.ne_zero_iff _).2 a.ne_zero
  obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v (a : w.adicCompletion F) = WithZero.exp n := ⟨_, (WithZero.exp_log h0).symm⟩
  refine ⟨-n, a * π ^ n, ?_, by simp⟩
  rw [IsUnitAt, Units.val_mul, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hπ, hn, ← WithZero.exp_zsmul, ← WithZero.exp_add]
  simp
/- English proof (translation)
The claim follows from `(σ.smooth y).preimage cont_uni`.
-/
private theorem open_stab (σ : SmIrr (GL (Fin 2) (w.adicCompletion F))) (y : σ.V) :
    IsOpen {x : w.adicCompletion F | σ.ρ (aff 1 x) y = y} := (σ.smooth y).preimage cont_uni
/- English proof (translation)
Establish `ht` using `(tendsto_pow_atTop_nhds_zero_of_norm_lt_one (GlobalTheory.LocalData.norm_resChar_lt_one w)).mul_const a`. Rewrite `ht` using `[zero_mul]`. Take `⟨m, hm⟩` from `(ht.eventually ((open_stab σ y).mem_nhds (by simp [aff_one]))).exists`. Conclude with `⟨_ ^ m, pow_ne_zero _ (GlobalTheory.LocalData.resChar_prime w).ne_zero, by rw [Nat.cast_pow]; exact hm⟩`.
-/
private theorem tors (σ : SmIrr (GL (Fin 2) (w.adicCompletion F))) (a : w.adicCompletion F) (y : σ.V) :
    ∃ n : ℕ, n ≠ 0 ∧ σ.ρ (aff 1 (n * a)) y = y := by
  have ht := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (GlobalTheory.LocalData.norm_resChar_lt_one w)).mul_const a
  rw [zero_mul] at ht
  obtain ⟨m, hm⟩ := (ht.eventually ((open_stab σ y).mem_nhds (by simp [aff_one]))).exists
  exact ⟨_ ^ m, pow_ne_zero _ (GlobalTheory.LocalData.resChar_prime w).ne_zero, by rw [Nat.cast_pow]; exact hm⟩
/- English proof (translation)
Use `haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F w`. Use `IsLocallyConstant.range_finite ((IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_)` and prove the remaining obligations. Establish `h1 : Continuous fun z : w.adicCompletionIntegers F => (z : w.adicCompletion F) - x` using `by fun_prop`. Use `filter_upwards [((open_stab σ y).preimage h1).mem_nhds (x := x) (by simp [aff_one])] with z hz`. Establish `hz' : σ.ρ (aff 1 ((z : w.adicCompletion F) - x)) y = y` using `hz`.

Use `conv_rhs => rw [← hz', ← Module.End.mul_apply, ← map_mul, aff_mul]`. Simplify using the standard rewrite rules.
-/
private theorem fin_orb (σ : SmIrr (GL (Fin 2) (w.adicCompletion F))) (y : σ.V) :
    (Set.range fun x : w.adicCompletionIntegers F => σ.ρ (aff 1 (x : w.adicCompletion F)) y).Finite := by
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F w
  refine IsLocallyConstant.range_finite ((IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_)
  have h1 : Continuous fun z : w.adicCompletionIntegers F => (z : w.adicCompletion F) - x := by fun_prop
  filter_upwards [((open_stab σ y).preimage h1).mem_nhds (x := x) (by simp [aff_one])] with z hz
  have hz' : σ.ρ (aff 1 ((z : w.adicCompletion F) - x)) y = y := hz
  conv_rhs => rw [← hz', ← Module.End.mul_apply, ← map_mul, aff_mul]
  simp
/- English proof (translation)
Establish `hu1 : Valued.v (u : w.adicCompletion F) = 1` using `hu`. Establish `h1 : (u : w.adicCompletion F) ∈ w.adicCompletionIntegers F`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, hu1]`. Establish `h2 : ((u⁻¹ : (w.adicCompletion F)ˣ) : w.adicCompletion F) ∈ w.adicCompletionIntegers F`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀, hu1, inv_one]`.

Set `u' : (w.adicCompletionIntegers F)ˣ` to `⟨⟨_, h1⟩, ⟨_, h2⟩, Subtype.ext u.mul_inv, Subtype.ext u.inv_mul⟩`. Establish `e : Units.map (w.adicCompletionIntegers F).subtype.toMonoidHom u' = u` using `Units.ext rfl`. Use `affine_mem_iwahori_level w c u' 0` as an intermediate fact. Rewrite `this` using `[e]`. Then use the resulting hypothesis.
-/
private theorem unit_mem (c : ℕ) (u : (w.adicCompletion F)ˣ) (hu : IsUnitAt w u) : aff u 0 ∈ K1 w c := by
  have hu1 : Valued.v (u : w.adicCompletion F) = 1 := hu
  have h1 : (u : w.adicCompletion F) ∈ w.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hu1]
  have h2 : ((u⁻¹ : (w.adicCompletion F)ˣ) : w.adicCompletion F) ∈ w.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀, hu1, inv_one]
  let u' : (w.adicCompletionIntegers F)ˣ := ⟨⟨_, h1⟩, ⟨_, h2⟩, Subtype.ext u.mul_inv, Subtype.ext u.inv_mul⟩
  have e : Units.map (w.adicCompletionIntegers F).subtype.toMonoidHom u' = u := Units.ext rfl
  have := affine_mem_iwahori_level w c u' 0
  rwa [e] at this
end Loc
end UpperTheory.V.Sd
open UpperTheory.V.Sd in
/- English proof (translation)
Introduce `_ F _ _ w σ c lam hc ⟨v, hv, hfix, hU⟩`. Take `⟨ω, hω⟩` from `cent w σ`. Take `⟨S, hS, hcard⟩` from `reps w`. Establish `hsum` using `(uopSum F w σ.V σ.ρ c v hfix).2 _ hS`. Rewrite `hsum` using `[if_neg hc, add_zero, hU]`.

Establish `hπ : Valued.v ((atFin w (unif w) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = WithZero.exp (-1 : ℤ)` using `unif_spec w`. Rewrite using `[← hcard]`. Use `gen (w.adicCompletionIntegers F).toSubring (w.adicCompletionIntegers F).mem_or_inv_mem (atFin w (unif w)) (pi_mem hπ) (pi_pow hπ) (IsUnitAt w) (pi_dec hπ) σ.ρ σ.irred (tors σ) (fin_orb σ) ω hω v hv (fun x hx => ?_) (fun u hu => hfix _ (unit_mem c u hu)) S lam hsum.symm` and prove the remaining obligations. Simplify using `using hfix _ (affine_mem_iwahori_level w c 1 ⟨x, hx⟩)`.
-/
theorem UpperTheory.V.Sd.jacqOfU_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Sd.JacqOfU := by
  intro _ F _ _ w σ c lam hc ⟨v, hv, hfix, hU⟩
  obtain ⟨ω, hω⟩ := cent w σ
  obtain ⟨S, hS, hcard⟩ := reps w
  have hsum := (uopSum F w σ.V σ.ρ c v hfix).2 _ hS
  rw [if_neg hc, add_zero, hU] at hsum
  have hπ : Valued.v ((atFin w (unif w) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = WithZero.exp (-1 : ℤ) :=
    unif_spec w
  rw [← hcard]
  refine gen (w.adicCompletionIntegers F).toSubring (w.adicCompletionIntegers F).mem_or_inv_mem (atFin w (unif w)) (pi_mem hπ)
    (pi_pow hπ) (IsUnitAt w) (pi_dec hπ) σ.ρ σ.irred (tors σ) (fin_orb σ) ω hω v hv (fun x hx => ?_)
    (fun u hu => hfix _ (unit_mem c u hu)) S lam hsum.symm
  simpa using hfix _ (affine_mem_iwahori_level w c 1 ⟨x, hx⟩)
end
end
