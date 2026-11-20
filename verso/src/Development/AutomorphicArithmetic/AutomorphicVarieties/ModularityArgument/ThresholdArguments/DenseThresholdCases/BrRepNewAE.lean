import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RepNewAE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SVRCharEq

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Polynomial GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd UpperTheory.V.Af UpperTheory.V.Af.Nf
/- English proof (translation)
The claim follows from `Function.Injective.tendsto_cofinite fun w w' e => HeightOneSpectrum.ext <| by rw [(places w).2.1, (places w').2.1] exact congrArg (fun n : ℕ => Ideal.span {(n : 𝓞 ℚ)}) e`.
-/
private theorem tend : Filter.Tendsto (fun w : Pl ℚ => normV w) Filter.cofinite Filter.cofinite :=
  Function.Injective.tendsto_cofinite fun w w' e => HeightOneSpectrum.ext <| by
    rw [(places w).2.1, (places w').2.1]
    exact congrArg (fun n : ℕ => Ideal.span {(n : 𝓞 ℚ)}) e
/- English proof (translation)
Introduce `hP hR k hk j π hπ`. Establish `hk1 : 1 ≤ k` using `by omega`. Use `set s : ℝ := 1 - (k : ℝ) / 2 + j with hs`. Set `χ` to `GlobalTheory.HeckeGal.Model.absPow ℚ (-s)`. Establish `hE` using `GlobalTheory.HeckeGal.Model.absPow_isAbsPow ℚ (-s)`.

Establish `hi : ∀ v, (π.twist χ).HasInfChar v {((k : ℂ) - 1) / 2, -(((k : ℂ) - 1) / 2)}` using `fun v => by`. Use `(hπ v).twist χ` as an intermediate fact. Rewrite `this` using `[absExpo ℚ (-s) v]`. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, hs]`.

Conclude with `congrArg₂ (fun a b : ℂ => a ::ₘ {b}) (by push_cast; ring) (by push_cast; ring)`. Take `⟨N, _, ψ, g, hg⟩` from `hR k hk _ hi`. Take `⟨f, _, h, hf, ha⟩` from `UpperTheory.V.Br.minNew N k hk1 ψ g`. Establish `hc` using `_root_.UpperTheory.V.Br.charEq_sv_alt hP k N f.M (by omega) ψ f.χ g h ha`. Use `⟨f, ?_⟩` and prove the remaining obligations.

Use `filter_upwards [hg, tend.eventually ha, tend.eventually hc] with w ⟨α, β, hsat, hsum, hprod⟩ h1 h2`. Establish `hp` using `(places w).1`. Establish `hq` using `(places w).2.2.1`. Establish `hu : (χ⁻¹).UnrAt w` using `fun u hu => by`. Use `hE.1 w u hu` as an intermediate fact.

Conclude with `inv_eq_one.2 this`. Establish `h3` using `hsat.twist hu`. Rewrite `h3` using `[← TR.CuspSub.twist_mul, mul_inv_cancel, TR.CuspSub.twist_one]`. Use `⟨_, h3, ?_⟩` and prove the remaining obligations. Establish `hq0 : (0 : ℝ) < normV w` using `by exact_mod_cast hp.pos`.

Establish `hval0 : ((χ.val w : ℂˣ) : ℂ) = (((normV w : ℝ) ^ (-(-s)) : ℝ) : ℂ)`. Rewrite using `[hE.2.1 w, hq, Complex.ofReal_cpow hq0.le]`. Simplify using the standard rewrite rules. Establish `hval : (((χ⁻¹).val w : ℂˣ) : ℂ) = (((normV w : ℝ) ^ (-s) : ℝ) : ℂ)`. Establish `e : (χ⁻¹).val w = (χ.val w)⁻¹` using `rfl`.

Rewrite using `[e, Units.val_inv_eq_inv_val, hval0, ← Complex.ofReal_inv, ← Real.rpow_neg hq0.le, neg_neg]`. Use `set r : ℂ := (((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) with hr`. Establish `key : ∀ a : ℂˣ, (normV w : ℂ) ^ j * ((((normV w : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ) * ((a * (χ⁻¹).val w : ℂˣ) : ℂ)) = r * a` using `fun a => by`. Establish `: ((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) = (normV w : ℝ) ^ j * ((normV w : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) * (normV w : ℝ) ^ (-s))`. Rewrite using `[← Real.rpow_intCast, ← Real.rpow_add hq0, ← Real.rpow_add hq0]`.

Use `congr 1`. Rewrite using `[hs]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hr, this, Units.val_mul, hval]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hrr : r * r = (normV w : ℂ) ^ (k - 1)`. Rewrite using `[hr, ← Complex.ofReal_mul, ← Real.rpow_add hq0, add_halves, ← Nat.cast_pred hk1, Real.rpow_natCast]`. Use `push_cast`.

Both sides reduce to the same expression. Establish `hfa : f.a (normV w) = r * ((α : ℂ) + β)`. Rewrite using `[← hsum, ← h1 hp, Newform.a, Eigenform.a, hf]`. Simplify using `only [algSat, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton, Multiset.pure_def, Multiset.bind_def, Multiset.cons_bind, Multiset.singleton_bind, Multiset.singleton_add, key]`. Rewrite using `[Newform.heckePoly, hfa, ← h2 hp, ← hprod, ← hrr]`.

Simplify using `only [Units.val_mul, C_mul, C_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.Br.repNewAE_of_printsH_of_repEig :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Br.RepEig → UpperTheory.V.Br.RepNewAE := by
  intro hP hR k hk j π hπ
  have hk1 : 1 ≤ k := by omega
  set s : ℝ := 1 - (k : ℝ) / 2 + j with hs
  let χ := GlobalTheory.HeckeGal.Model.absPow ℚ (-s)
  have hE := GlobalTheory.HeckeGal.Model.absPow_isAbsPow ℚ (-s)
  have hi : ∀ v, (π.twist χ).HasInfChar v {((k : ℂ) - 1) / 2, -(((k : ℂ) - 1) / 2)} := fun v => by
    have := (hπ v).twist χ
    rw [absExpo ℚ (-s) v] at this
    convert this using 1
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, hs]
    exact congrArg₂ (fun a b : ℂ => a ::ₘ {b}) (by push_cast; ring) (by push_cast; ring)
  obtain ⟨N, _, ψ, g, hg⟩ := hR k hk _ hi
  obtain ⟨f, _, h, hf, ha⟩ := UpperTheory.V.Br.minNew N k hk1 ψ g
  have hc := _root_.UpperTheory.V.Br.charEq_sv_alt hP k N f.M (by omega) ψ f.χ g h ha
  refine ⟨f, ?_⟩
  filter_upwards [hg, tend.eventually ha, tend.eventually hc] with w ⟨α, β, hsat, hsum, hprod⟩ h1 h2
  have hp := (places w).1
  have hq := (places w).2.2.1
  have hu : (χ⁻¹).UnrAt w := fun u hu => by
    have := hE.1 w u hu
    exact inv_eq_one.2 this
  have h3 := hsat.twist hu
  rw [← TR.CuspSub.twist_mul, mul_inv_cancel, TR.CuspSub.twist_one] at h3
  refine ⟨_, h3, ?_⟩
  have hq0 : (0 : ℝ) < normV w := by exact_mod_cast hp.pos
  have hval0 : ((χ.val w : ℂˣ) : ℂ) = (((normV w : ℝ) ^ (-(-s)) : ℝ) : ℂ) := by
    rw [hE.2.1 w, hq, Complex.ofReal_cpow hq0.le]; simp
  have hval : (((χ⁻¹).val w : ℂˣ) : ℂ) = (((normV w : ℝ) ^ (-s) : ℝ) : ℂ) := by
    have e : (χ⁻¹).val w = (χ.val w)⁻¹ := rfl
    rw [e, Units.val_inv_eq_inv_val, hval0, ← Complex.ofReal_inv, ← Real.rpow_neg hq0.le, neg_neg]
  set r : ℂ := (((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) with hr
  have key : ∀ a : ℂˣ, (normV w : ℂ) ^ j * ((((normV w : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ) * ((a * (χ⁻¹).val w : ℂˣ) : ℂ)) =
      r * a := fun a => by
    have : ((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) =
        (normV w : ℝ) ^ j * ((normV w : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) * (normV w : ℝ) ^ (-s)) := by
      rw [← Real.rpow_intCast, ← Real.rpow_add hq0, ← Real.rpow_add hq0]
      congr 1
      rw [hs]; push_cast; ring
    rw [hr, this, Units.val_mul, hval]; push_cast; ring
  have hrr : r * r = (normV w : ℂ) ^ (k - 1) := by
    rw [hr, ← Complex.ofReal_mul, ← Real.rpow_add hq0, add_halves, ← Nat.cast_pred hk1, Real.rpow_natCast]
    push_cast; rfl
  have hfa : f.a (normV w) = r * ((α : ℂ) + β) := by
    rw [← hsum, ← h1 hp, Newform.a, Eigenform.a, hf]
  simp only [algSat, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, Multiset.pure_def, Multiset.bind_def, Multiset.cons_bind, Multiset.singleton_bind,
    Multiset.singleton_add, key]
  rw [Newform.heckePoly, hfa, ← h2 hp, ← hprod, ← hrr]
  simp only [Units.val_mul, C_mul, C_add]
  ring
end
