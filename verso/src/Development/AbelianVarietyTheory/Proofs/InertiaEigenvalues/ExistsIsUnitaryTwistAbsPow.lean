import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.NormOneCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExtensionEmbeddingMixedSymmOfIsComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GroundTheory.Global

namespace GlobalTheory.AbsTwist

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Take `⟨D, hD, -, hxD⟩` from `IdeleGroup.exists_isCompact_normOneSubgroup F`. Take `⟨C, hC⟩` from `hD.exists_bound_of_continuousOn hc.continuousOn`. Establish `h1 : f 1 = 0`. Use `hm 1 1` as an intermediate fact. Rewrite `this` using `[mul_one]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hp : ∀ n : ℕ, f (x ^ n) = n * f x` using `fun n => by`. Proceed by induction on `n with`. Consider the case `zero => simpa using h1`. Consider the case `succ n ih => rw [pow_succ, hm, ih]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hb : ∀ n : ℕ, (n : ℝ) * |f x| ≤ C` using `fun n => by`. Take `⟨k, hk'⟩` from `hxD _ (pow_mem hx n)`. Use `hC _ hk'` as an intermediate fact.

Rewrite `this` using `[hm, hk, zero_add, hp, Real.norm_eq_abs, abs_mul, Nat.abs_cast]`. Then use the resulting hypothesis. Assume the negation of the conclusion as `h`. Take `⟨n, hn⟩` from `exists_nat_gt (C / |f x|)`. Rewrite `hn` using `[div_lt_iff₀ (abs_pos.2 h)]`. Conclude with `absurd (hb n) (not_le.2 hn)`.
-/
theorem eq_zero_of_normOne (f : IdeleGroup F → ℝ) (hc : Continuous f) (hm : ∀ x y, f (x * y) = f x + f y)
    (hk : ∀ k, f (IdeleGroup.diagonal F k) = 0) (x : IdeleGroup F) (hx : x ∈ IdeleGroup.normOneSubgroup F) :
    f x = 0 := by
  obtain ⟨D, hD, -, hxD⟩ := IdeleGroup.exists_isCompact_normOneSubgroup F
  obtain ⟨C, hC⟩ := hD.exists_bound_of_continuousOn hc.continuousOn
  have h1 : f 1 = 0 := by
    have := hm 1 1
    rw [mul_one] at this
    linarith
  have hp : ∀ n : ℕ, f (x ^ n) = n * f x := fun n => by
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ, hm, ih]; push_cast; ring
  have hb : ∀ n : ℕ, (n : ℝ) * |f x| ≤ C := fun n => by
    obtain ⟨k, hk'⟩ := hxD _ (pow_mem hx n)
    have := hC _ hk'
    rwa [hm, hk, zero_add, hp, Real.norm_eq_abs, abs_mul, Nat.abs_cast] at this
  by_contra h
  obtain ⟨n, hn⟩ := exists_nat_gt (C / |f x|)
  rw [div_lt_iff₀ (abs_pos.2 h)] at hn
  exact absurd (hb n) (not_le.2 hn)

/- English proof (translation)
The claim follows from `GlobalTheory.HeckeOne.ideleNorm_expScalar F t`.
-/
theorem module_expScalar (t : ℝ) :
    (IdeleGroup.ideleModule F (GlobalTheory.HeckeOne.mixedIdele F (GlobalTheory.HeckeOne.expScalar F t)) : ℝ) =
      Real.exp ((Module.finrank ℚ F : ℝ) * t) :=
  GlobalTheory.HeckeOne.ideleNorm_expScalar F t

/- English proof (translation)
Set `e : ℝ → IdeleGroup F` to `fun t => GlobalTheory.HeckeOne.mixedIdele F (GlobalTheory.HeckeOne.expScalar F t)`. Establish `hadd : ∀ s t, f (e (s + t)) = f (e s) + f (e t)` using `fun s t => by`. Simplify using `only [e]`. Rewrite using `[GlobalTheory.HeckeOne.expScalar_add, map_mul, hm]`. Establish `hcont : Continuous fun t => f (e t)` using `hc.comp ((GlobalTheory.HeckeOne.continuous_mixedIdele F).comp (GlobalTheory.HeckeOne.continuous_expScalar F))`.

Establish `hn : (Module.finrank ℚ F : ℝ) ≠ 0` using `by exact_mod_cast Module.finrank_pos.ne'`. Use `⟨f (e 1) / Module.finrank ℚ F, fun x => ?_⟩` and prove the remaining obligations. Use `set t : ℝ := Real.log (IdeleGroup.ideleModule F x : ℝ) / Module.finrank ℚ F with ht`. Establish `h1` using `map_real_smul (AddMonoidHom.mk' (fun t => f (e t)) hadd) hcont t 1`. Simplify using `only [smul_eq_mul, mul_one, AddMonoidHom.mk'_apply] at h1`.

Establish `h2 : IdeleGroup.ideleModule F (e t) = IdeleGroup.ideleModule F x` using `Subtype.ext (by`. Establish `h3` using `module_expScalar (F := F) t`. Rewrite `h3` using `[ht, mul_div_cancel₀ _ hn, Real.exp_log (IdeleGroup.ideleModule F x).2]`. Conclude with `h3)`. Establish `h4 : (e t)⁻¹ * x ∈ IdeleGroup.normOneSubgroup F`.

Rewrite using `[IdeleGroup.normOneSubgroup, MonoidHom.mem_ker, map_mul, map_inv, h2, inv_mul_cancel]`. Establish `h5` using `hm (e t) ((e t)⁻¹ * x)`. Rewrite `h5` using `[mul_inv_cancel_left, eq_zero_of_normOne f hc hm hk _ h4, add_zero, h1, ht]`. Rewrite using `[h5]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_eq_mul_log_module (f : IdeleGroup F → ℝ) (hc : Continuous f) (hm : ∀ x y, f (x * y) = f x + f y)
    (hk : ∀ k, f (IdeleGroup.diagonal F k) = 0) :
    ∃ a : ℝ, ∀ x, f x = a * Real.log (IdeleGroup.ideleModule F x : ℝ) := by
  let e : ℝ → IdeleGroup F := fun t => GlobalTheory.HeckeOne.mixedIdele F (GlobalTheory.HeckeOne.expScalar F t)
  have hadd : ∀ s t, f (e (s + t)) = f (e s) + f (e t) := fun s t => by
    simp only [e]
    rw [GlobalTheory.HeckeOne.expScalar_add, map_mul, hm]
  have hcont : Continuous fun t => f (e t) :=
    hc.comp ((GlobalTheory.HeckeOne.continuous_mixedIdele F).comp (GlobalTheory.HeckeOne.continuous_expScalar F))
  have hn : (Module.finrank ℚ F : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  refine ⟨f (e 1) / Module.finrank ℚ F, fun x => ?_⟩
  set t : ℝ := Real.log (IdeleGroup.ideleModule F x : ℝ) / Module.finrank ℚ F with ht
  have h1 := map_real_smul (AddMonoidHom.mk' (fun t => f (e t)) hadd) hcont t 1
  simp only [smul_eq_mul, mul_one, AddMonoidHom.mk'_apply] at h1
  have h2 : IdeleGroup.ideleModule F (e t) = IdeleGroup.ideleModule F x := Subtype.ext (by
    have h3 := module_expScalar (F := F) t
    rw [ht, mul_div_cancel₀ _ hn, Real.exp_log (IdeleGroup.ideleModule F x).2] at h3
    exact h3)
  have h4 : (e t)⁻¹ * x ∈ IdeleGroup.normOneSubgroup F := by
    rw [IdeleGroup.normOneSubgroup, MonoidHom.mem_ker, map_mul, map_inv, h2, inv_mul_cancel]
  have h5 := hm (e t) ((e t)⁻¹ * x)
  rw [mul_inv_cancel_left, eq_zero_of_normOne f hc hm hk _ h4, add_zero, h1, ht] at h5
  rw [h5]; ring

open GlobalTheory.Mem.Chr.CharModel in

/- English proof (translation)
Establish `h0 : ∀ x, ‖((ω.1 x : ℂˣ) : ℂ)‖ ≠ 0` using `fun x => norm_ne_zero_iff.2 (Units.ne_zero _)`. Take `⟨a, ha⟩` from `exists_eq_mul_log_module (F := F) (fun x => Real.log ‖((ω.1 x : ℂˣ) : ℂ)‖) ((Units.continuous_val.comp ω.2.1).norm.log h0) (fun x y => by rw [map_mul, Units.val_mul, norm_mul, Real.log_mul (h0 x) (h0 y)]) (fun k => by`. Establish `: ω.1 (IdeleGroup.diagonal F k) = 1` using `ω.2.2 k`. Rewrite using `[this]`. Use the proof step `simp)`.

Take `⟨b, hb⟩` from `exists_eq_mul_log_module (F := F) (logNorm F) (continuous_logNorm F) (logNorm_mul F) (logNorm_principal F)`. Establish `hb0 : b ≠ 0`. Introduce and unpack `rfl`. Use `absChar_not_unitary (F := F) fun x => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `‖Complex.exp (1 * logNorm F x)‖ = 1`.

Rewrite using `[hb]`. Simplify using the standard rewrite rules. Use `⟨a / b, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[← Real.exp_log (norm_pos_iff.2 (Units.ne_zero (ω.1 x))), ha x, hb x]`. Use `congr 1`.

Clear the denominators using the available nonvanishing facts.
-/
theorem exists_norm_eq_exp (ω : HChar F) :
    ∃ c : ℝ, ∀ x, ‖((ω.1 x : ℂˣ) : ℂ)‖ = Real.exp (c * logNorm F x) := by
  have h0 : ∀ x, ‖((ω.1 x : ℂˣ) : ℂ)‖ ≠ 0 := fun x => norm_ne_zero_iff.2 (Units.ne_zero _)
  obtain ⟨a, ha⟩ := exists_eq_mul_log_module (F := F) (fun x => Real.log ‖((ω.1 x : ℂˣ) : ℂ)‖)
    ((Units.continuous_val.comp ω.2.1).norm.log h0)
    (fun x y => by rw [map_mul, Units.val_mul, norm_mul, Real.log_mul (h0 x) (h0 y)])
    (fun k => by
      have : ω.1 (IdeleGroup.diagonal F k) = 1 := ω.2.2 k
      rw [this]; simp)
  obtain ⟨b, hb⟩ := exists_eq_mul_log_module (F := F) (logNorm F) (continuous_logNorm F) (logNorm_mul F)
    (logNorm_principal F)
  have hb0 : b ≠ 0 := by
    rintro rfl
    refine absChar_not_unitary (F := F) fun x => ?_
    change ‖Complex.exp (1 * logNorm F x)‖ = 1
    rw [hb]; simp
  refine ⟨a / b, fun x => ?_⟩
  rw [← Real.exp_log (norm_pos_iff.2 (Units.ne_zero (ω.1 x))), ha x, hb x]
  congr 1
  field_simp

end GlobalTheory.AbsTwist

namespace GlobalTheory.CuspRep.CG

open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.Mem.Chr.CharModel GlobalTheory.HeckeGal.Model

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [IsTotallyComplex E] in

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem absPow_val_apply (t : ℝ) (x : Ideles E) :
    (((absPow E t).1 x : ℂˣ) : ℂ) = Complex.exp ((t : ℂ) * logNorm E x) := rfl

omit [IsTotallyComplex E] in

/- English proof (translation)
Use `Subtype.ext (MonoidHom.ext fun x => Units.ext ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(((absPow E (-t)).1 x : ℂˣ) : ℂ) * (((absPow E t).1 x : ℂˣ) : ℂ) = 1`. Rewrite using `[absPow_val_apply, absPow_val_apply, ← Complex.exp_add]`. Use `push_cast`. Put the polynomial expressions in normal form.

Conclude with `Complex.exp_zero`.
-/
theorem absPow_neg_mul (t : ℝ) : absPow E (-t) * absPow E t = 1 := by
  refine Subtype.ext (MonoidHom.ext fun x => Units.ext ?_)
  change (((absPow E (-t)).1 x : ℂˣ) : ℂ) * (((absPow E t).1 x : ℂˣ) : ℂ) = 1
  rw [absPow_val_apply, absPow_val_apply, ← Complex.exp_add]
  push_cast
  ring_nf
  exact Complex.exp_zero

/- English proof (translation)
Take `⟨ω, hω⟩` from `GlobalTheory.CuspRep.Central.exists_hasCentChar π`. Take `⟨c, hc⟩` from `GlobalTheory.AbsTwist.exists_norm_eq_exp ω`. Establish `ha' : (a : ℝ) ≠ 0` using `by exact_mod_cast (show a ≠ 0 by omega)`. Use `⟨π.twist (absPow E (-(c / a))), c / a, ⟨_, fun x => ?_, hω.twist _⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `‖((ω.1 x : ℂˣ) : ℂ) * ((((absPow E (-(c / a))).1 x) ^ a : ℂˣ) : ℂ)‖ = 1`.

Rewrite using `[Units.val_pow_eq_pow_val, absPow_val_apply, norm_mul, norm_pow, hc x, show ((-(c / a) : ℝ) : ℂ) * (logNorm E x : ℂ) = ((-(c / a) * logNorm E x : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal, ← Real.exp_nat_mul, ← Real.exp_add]`. Rewrite using `[Real.exp_eq_one_iff]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← twist_mul, absPow_neg_mul, twist_one]`.
-/
theorem exists_isUnitary_twist_absPow (π : CG E a) (ha : 1 ≤ a) :
    ∃ (π₀ : CG E a) (t : ℝ), π₀.IsUnitary ∧ π = π₀.twist (absPow E t) := by
  obtain ⟨ω, hω⟩ := GlobalTheory.CuspRep.Central.exists_hasCentChar π
  obtain ⟨c, hc⟩ := GlobalTheory.AbsTwist.exists_norm_eq_exp ω
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  refine ⟨π.twist (absPow E (-(c / a))), c / a, ⟨_, fun x => ?_, hω.twist _⟩, ?_⟩
  · change ‖((ω.1 x : ℂˣ) : ℂ) * ((((absPow E (-(c / a))).1 x) ^ a : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_pow_eq_pow_val, absPow_val_apply, norm_mul, norm_pow, hc x,
      show ((-(c / a) : ℝ) : ℂ) * (logNorm E x : ℂ) = ((-(c / a) * logNorm E x : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_exp_ofReal, ← Real.exp_nat_mul, ← Real.exp_add]
    rw [Real.exp_eq_one_iff]
    field_simp
    ring
  · rw [← twist_mul, absPow_neg_mul, twist_one]

/- English proof (translation)
Proceed by induction on `π using Quotient.inductionOn`. Conclude with `GlobalTheory.SphGal.hasSatGL_twist _ _ _ ν w B hν h`.
-/
theorem HasSat.twist {π : CG E a} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ} (h : π.HasSat w B)
    {ν : HChar E} (hν : ν.UnrAt w) : (π.twist ν).HasSat w (B.map (· * ν.val w)) := by
  induction π using Quotient.inductionOn
  exact GlobalTheory.SphGal.hasSatGL_twist _ _ _ ν w B hν h

omit [IsTotallyComplex E] in

/- English proof (translation)
Establish `hq : 1 < Ideal.absNorm w.asIdeal` using `NumberField.HeightOneSpectrum.one_lt_absNorm w`. Rewrite using `[(absPow_isAbsPow E t).2.1 w, Complex.norm_natCast_cpow_of_pos (zero_lt_one.trans hq), Complex.neg_re, Complex.ofReal_re]`.
-/
theorem norm_val_absPow (t : ℝ) (w : HeightOneSpectrum (𝓞 E)) :
    ‖(((absPow E t).val w : ℂˣ) : ℂ)‖ = (Ideal.absNorm w.asIdeal : ℝ) ^ (-t) := by
  have hq : 1 < Ideal.absNorm w.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm w
  rw [(absPow_isAbsPow E t).2.1 w, Complex.norm_natCast_cpow_of_pos (zero_lt_one.trans hq), Complex.neg_re,
    Complex.ofReal_re]

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.twist ((absPow_isAbsPow E t).1 w), norm_val_absPow t w⟩`.
-/
theorem HasSat.twist_absPow {π : CG E a} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ} (h : π.HasSat w B)
    (t : ℝ) : (π.twist (absPow E t)).HasSat w (B.map (· * (absPow E t).val w)) ∧
      ‖(((absPow E t).val w : ℂˣ) : ℂ)‖ = (Ideal.absNorm w.asIdeal : ℝ) ^ (-t) :=
  ⟨h.twist ((absPow_isAbsPow E t).1 w), norm_val_absPow t w⟩

end GlobalTheory.CuspRep.CG
