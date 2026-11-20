import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Places

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf CongruenceSubgroup GlobalTheory.CuspRep Neutral.B1 Formalism.L2.Host
open scoped Matrix Manifold UpperHalfPlane

namespace GlobalTheory.NewLevel

/- English proof (translation)
Establish `h0 : Ideal.span {(a : 𝓞 ℚ)} ≠ 0` using `by simpa using h`. Use `Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun w hw => ?_)` and prove the remaining obligations. Take `⟨c, rfl⟩` from `not_not.1 hw`. Use `Ideal.dvd_span_singleton.2 ?_` and prove the remaining obligations. Rewrite using `[Nat.cast_mul, (places w).2.1]`.

Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`.
-/
private theorem ev_not_dvd_norm {a : ℕ} (h : a ≠ 0) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ¬ normV w ∣ a := by
  have h0 : Ideal.span {(a : 𝓞 ℚ)} ≠ 0 := by simpa using h
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun w hw => ?_)
  obtain ⟨c, rfl⟩ := not_not.1 hw
  refine Ideal.dvd_span_singleton.2 ?_
  rw [Nat.cast_mul, (places w).2.1]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

/- English proof (translation)
Establish `e : ∀ D : Multiset ℂˣ, (D.map fun b : ℂˣ => Polynomial.X - Polynomial.C (c * (b : ℂ))).prod.roots = D.map fun b : ℂˣ => c * (b : ℂ)` using `fun D => by`. Rewrite using `[← Polynomial.roots_multiset_prod_X_sub_C (D.map fun b : ℂˣ => c * (b : ℂ)), Multiset.map_map]`. Both sides reduce to the same expression. Establish `h1` using `(e B).symm.trans ((congrArg Polynomial.roots h).trans (e B'))`. Conclude with `Multiset.map_injective (fun a b hab => Units.ext (mul_left_cancel₀ hc hab)) h1`.
-/
private theorem multiset_eq_of_prod_eq {c : ℂ} (hc : c ≠ 0) {B B' : Multiset ℂˣ}
    (h : (B.map fun b : ℂˣ => Polynomial.X - Polynomial.C (c * (b : ℂ))).prod =
      (B'.map fun b : ℂˣ => Polynomial.X - Polynomial.C (c * (b : ℂ))).prod) : B = B' := by
  have e : ∀ D : Multiset ℂˣ, (D.map fun b : ℂˣ => Polynomial.X - Polynomial.C (c * (b : ℂ))).prod.roots =
      D.map fun b : ℂˣ => c * (b : ℂ) := fun D => by
    rw [← Polynomial.roots_multiset_prod_X_sub_C (D.map fun b : ℂˣ => c * (b : ℂ)), Multiset.map_map]
    rfl
  have h1 := (e B).symm.trans ((congrArg Polynomial.roots h).trans (e B'))
  exact Multiset.map_injective (fun a b hab => Units.ext (mul_left_cancel₀ hc hab)) h1

/- English proof (translation)
Proceed by induction on `B using Multiset.induction_on with`. Consider the case `empty => simp [algSat]`. Consider the case `cons a B ih`. Simplify using `only [algSat, Multiset.map_cons, Multiset.prod_cons, Multiset.pure_def, Multiset.bind_def, Multiset.cons_bind, Multiset.singleton_add] at ih ⊢`. Rewrite using `[ih, mul_assoc]`.
-/
private theorem algSat_prod (q : ℕ) (t : ℂ) (B : Multiset ℂˣ) :
    ((algSat 2 q B).map fun b => Polynomial.X - Polynomial.C (t * b)).prod =
      (B.map fun b : ℂˣ => Polynomial.X -
        Polynomial.C ((t * (((q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ)) * (b : ℂ))).prod := by
  induction B using Multiset.induction_on with
  | empty => simp [algSat]
  | cons a B ih =>
    simp only [algSat, Multiset.map_cons, Multiset.prod_cons, Multiset.pure_def, Multiset.bind_def,
      Multiset.cons_bind, Multiset.singleton_add] at ih ⊢
    rw [ih, mul_assoc]

/- English proof (translation)
Introduce `hS k hk g j π π₀ hπ hπ₀ w Bs hBs`. Establish `hk1 : 1 ≤ k` using `by omega`. Use `set s : ℝ := 1 - (k : ℝ) / 2 + j with hs`. Set `χ` to `GlobalTheory.HeckeGal.Model.absPow ℚ s`. Establish `hE` using `GlobalTheory.HeckeGal.Model.absPow_isAbsPow ℚ s`.

Establish `hM : g.M ≠ 0` using `by have : 1 ≤ g.M := g.pos; omega`. Establish `hiso : π.Iso (π₀.twist χ)`. Use `hS ℚ 2 one_le_two π _ ?_` and prove the remaining obligations. Use `filter_upwards [hπ, ev_not_dvd_norm hM] with q hq hd`. Take `⟨B, hB, hpoly⟩` from `hq`.

Take `⟨α, β, hv, hsum, hprod⟩` from `hπ₀ q hd`. Establish `htw` using `hv.twist (χ := χ) (hE.1 q)`. Use `⟨B, hB, ?_⟩` and prove the remaining obligations. Establish `hq : Ideal.absNorm q.asIdeal = normV q` using `(places q).2.2.1`. Establish `hq0 : (0 : ℝ) < normV q` using `by exact_mod_cast (places q).1.pos`.

Establish `hval : ((χ.val q : ℂˣ) : ℂ) = (((normV q : ℝ) ^ (-s) : ℝ) : ℂ)`. Rewrite using `[hE.2.1 q, hq, Complex.ofReal_cpow hq0.le]`. Simplify using the standard rewrite rules. Use `set r : ℂ := (((normV q : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) with hr`. Establish `key : ∀ a : ℂˣ, ((normV q : ℂ) ^ j * (((normV q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ)) * ((a * χ.val q : ℂˣ) : ℂ) = r * a` using `fun a => by`.

Establish `: ((normV q : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) = (normV q : ℝ) ^ j * ((normV q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) * (normV q : ℝ) ^ (-s))`. Rewrite using `[← Real.rpow_intCast, ← Real.rpow_add hq0, ← Real.rpow_add hq0]`. Use `congr 1`. Rewrite using `[hs]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hr, this, Units.val_mul, hval]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hrr : r * r = (normV q : ℂ) ^ (k - 1)`.

Rewrite using `[hr, ← Complex.ofReal_mul, ← Real.rpow_add hq0, add_halves, ← Nat.cast_pred hk1, Real.rpow_natCast]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hc : ((normV q : ℂ) ^ j * (((normV q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ)) ≠ 0` using `mul_ne_zero (zpow_ne_zero _ (by exact_mod_cast hq0.ne')) (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hq0 _).ne')`. Rewrite `hpoly` using `[algSat_prod]`.

Establish `hBeq : B = Multiset.map (fun x => x * χ.val q) {α, β}`. Use `multiset_eq_of_prod_eq hc ?_` and prove the remaining obligations. Rewrite using `[hpoly, Newform.heckePoly]`. Simplify using `only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton, key]`. Rewrite using `[← hsum, ← hprod, ← hrr]`.

Simplify using `only [Units.val_mul, Polynomial.C_mul, Polynomial.C_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hBeq]`. Conclude with `htw`. Establish `h1` using `(hiso.hasSat hBs).twist (χ := χ⁻¹) (HChar.UnrAt.inv (hE.1 w))`.

Rewrite `h1` using `[← TR.CuspSub.twist_mul, mul_inv_cancel, TR.CuspSub.twist_one]`. Conclude with `⟨_, h1⟩`.
-/
theorem spherical_of_normTwist : Published.StrongMultOneReal → ∀ (k : ℕ), 2 ≤ k → ∀ (g : Newform k) (j : ℤ) (π π₀ : TR.CuspSub ℚ 2), (∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ∃ Bs, π.HasSat w Bs ∧ ((algSat 2 (normV w) Bs).map fun b => Polynomial.X - Polynomial.C ((normV w : ℂ) ^ j * b)).prod = g.heckePoly (normV w)) → (∀ q : HeightOneSpectrum (𝓞 ℚ), ¬ normV q ∣ g.M → ∃ α β : ℂˣ, π₀.HasSat q {α, β} ∧ (((normV q : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) * ((α : ℂ) + β) = g.a (normV q) ∧ ((α * β : ℂˣ) : ℂ) = g.χ (normV q : ZMod g.M)) → ∀ (w : HeightOneSpectrum (𝓞 ℚ)) (Bs : Multiset ℂˣ), π.HasSat w Bs → ∃ B, π₀.HasSat w B := by
  intro hS k hk g j π π₀ hπ hπ₀ w Bs hBs
  have hk1 : 1 ≤ k := by omega
  set s : ℝ := 1 - (k : ℝ) / 2 + j with hs
  let χ := GlobalTheory.HeckeGal.Model.absPow ℚ s
  have hE := GlobalTheory.HeckeGal.Model.absPow_isAbsPow ℚ s
  have hM : g.M ≠ 0 := by have : 1 ≤ g.M := g.pos; omega
  have hiso : π.Iso (π₀.twist χ) := by
    refine hS ℚ 2 one_le_two π _ ?_
    filter_upwards [hπ, ev_not_dvd_norm hM] with q hq hd
    obtain ⟨B, hB, hpoly⟩ := hq
    obtain ⟨α, β, hv, hsum, hprod⟩ := hπ₀ q hd
    have htw := hv.twist (χ := χ) (hE.1 q)
    refine ⟨B, hB, ?_⟩
    have hq : Ideal.absNorm q.asIdeal = normV q := (places q).2.2.1
    have hq0 : (0 : ℝ) < normV q := by exact_mod_cast (places q).1.pos
    have hval : ((χ.val q : ℂˣ) : ℂ) = (((normV q : ℝ) ^ (-s) : ℝ) : ℂ) := by
      rw [hE.2.1 q, hq, Complex.ofReal_cpow hq0.le]; simp
    set r : ℂ := (((normV q : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) with hr
    have key : ∀ a : ℂˣ, ((normV q : ℂ) ^ j * (((normV q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ)) *
        ((a * χ.val q : ℂˣ) : ℂ) = r * a := fun a => by
      have : ((normV q : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) =
          (normV q : ℝ) ^ j * ((normV q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) * (normV q : ℝ) ^ (-s)) := by
        rw [← Real.rpow_intCast, ← Real.rpow_add hq0, ← Real.rpow_add hq0]
        congr 1
        rw [hs]; push_cast; ring
      rw [hr, this, Units.val_mul, hval]; push_cast; ring
    have hrr : r * r = (normV q : ℂ) ^ (k - 1) := by
      rw [hr, ← Complex.ofReal_mul, ← Real.rpow_add hq0, add_halves, ← Nat.cast_pred hk1, Real.rpow_natCast]
      push_cast; rfl
    have hc : ((normV q : ℂ) ^ j * (((normV q : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ)) ≠ 0 :=
      mul_ne_zero (zpow_ne_zero _ (by exact_mod_cast hq0.ne'))
        (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hq0 _).ne')
    rw [algSat_prod] at hpoly
    have hBeq : B = Multiset.map (fun x => x * χ.val q) {α, β} := by
      refine multiset_eq_of_prod_eq hc ?_
      rw [hpoly, Newform.heckePoly]
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
        Multiset.prod_singleton, key]
      rw [← hsum, ← hprod, ← hrr]
      simp only [Units.val_mul, Polynomial.C_mul, Polynomial.C_add]
      ring
    rw [hBeq]
    exact htw
  have h1 := (hiso.hasSat hBs).twist (χ := χ⁻¹) (HChar.UnrAt.inv (hE.1 w))
  rw [← TR.CuspSub.twist_mul, mul_inv_cancel, TR.CuspSub.twist_one] at h1
  exact ⟨_, h1⟩

end GlobalTheory.NewLevel

end
