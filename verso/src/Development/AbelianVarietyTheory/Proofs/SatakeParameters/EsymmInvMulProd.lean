import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ConjSep

namespace GlobalTheory.ElementarySymmetricInverse

/- English proof (translation)
Simplify using `[Multiset.esymm]`.
-/
theorem esymm_deg_zero (s : Multiset ℂ) : s.esymm 0 = 1 := by
  simp [Multiset.esymm]

/- English proof (translation)
Simplify using `only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add, Multiset.map_map, Function.comp_def, Multiset.prod_cons, Multiset.sum_map_mul_left]`.
-/
theorem esymm_cons_succ (x : ℂ) (s : Multiset ℂ) (k : ℕ) :
    (x ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + x * s.esymm k := by
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Function.comp_def, Multiset.prod_cons, Multiset.sum_map_mul_left]

/- English proof (translation)
Substitute `hk` using the available equality. Simplify using `[Multiset.esymm]`.
-/
theorem esymm_top (s : Multiset ℂ) (k : ℕ) (hk : Multiset.card s = k) : s.esymm k = s.prod := by
  subst hk
  simp [Multiset.esymm]

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty`. Introduce `i j h`. Establish `hi : i = 0` using `by simp at h; exact h.1`. Establish `hj : j = 0` using `by simp at h; exact h.2`.

Substitute `hi hj` using the available equality. Simplify using `[esymm_deg_zero]`. Consider the case `cons x s ih`. Introduce `i j h`. Establish `hx : x ≠ 0` using `hs x (Multiset.mem_cons_self x s)`.

Establish `ih'` using `ih (fun y hy => hs y (Multiset.mem_cons_of_mem hy))`. Break down `i with _ | i` into its components or cases. Rewrite using `[esymm_deg_zero, one_mul, esymm_top _ j (by omega)]`. Break down `j with _ | j` into its components or cases. Rewrite using `[esymm_deg_zero, esymm_top _ (i + 1) (by rw [Multiset.card_map]; omega), Multiset.prod_map_inv']`.

Conclude with `inv_mul_cancel₀ (Multiset.prod_ne_zero (fun h0 => hs 0 h0 rfl))`. Rewrite `h` using `[Multiset.card_cons]`. Rewrite using `[Multiset.map_cons, Multiset.prod_cons, esymm_cons_succ, esymm_cons_succ, ← ih' (i + 1) j (by omega), ← ih' i (j + 1) (by omega)]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem esymm_inv_mul_prod (s : Multiset ℂ) (hs : ∀ x ∈ s, x ≠ 0) :
    ∀ i j : ℕ, i + j = Multiset.card s →
      (s.map fun x => x⁻¹).esymm i * s.prod = s.esymm j := by
  induction s using Multiset.induction_on with
  | empty =>
    intro i j h
    have hi : i = 0 := by simp at h; exact h.1
    have hj : j = 0 := by simp at h; exact h.2
    subst hi hj
    simp [esymm_deg_zero]
  | cons x s ih =>
    intro i j h
    have hx : x ≠ 0 := hs x (Multiset.mem_cons_self x s)
    have ih' := ih (fun y hy => hs y (Multiset.mem_cons_of_mem hy))
    rcases i with _ | i
    · rw [esymm_deg_zero, one_mul, esymm_top _ j (by omega)]
    rcases j with _ | j
    · rw [esymm_deg_zero, esymm_top _ (i + 1) (by rw [Multiset.card_map]; omega),
        Multiset.prod_map_inv']
      exact inv_mul_cancel₀ (Multiset.prod_ne_zero (fun h0 => hs 0 h0 rfl))
    rw [Multiset.card_cons] at h
    rw [Multiset.map_cons, Multiset.prod_cons, esymm_cons_succ, esymm_cons_succ,
      ← ih' (i + 1) j (by omega), ← ih' i (j + 1) (by omega)]
    field_simp
    ring

/- English proof (translation)
Establish `h : ((q : ℝ) ^ (((a : ℝ) - 1) / 2)) ^ a = (q : ℝ) ^ Nat.choose a 2`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q), ← Real.rpow_natCast, Nat.cast_choose_two]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Conclude with `congrArg (fun r : ℝ => (r : ℂ)) h` after adjusting the coercions.
-/
theorem half_pow (q a : ℕ) :
    (((q : ℝ) ^ (((a : ℝ) - 1) / 2) : ℝ) : ℂ) ^ a = (q : ℂ) ^ Nat.choose a 2 := by
  have h : ((q : ℝ) ^ (((a : ℝ) - 1) / 2)) ^ a = (q : ℝ) ^ Nat.choose a 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q), ← Real.rpow_natCast,
      Nat.cast_choose_two]
    congr 1
    ring
  exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) h

/- English proof (translation)
Unfold `UpperTheory.V.Af.algSat`. Simplify using `only [Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton, Multiset.map_map, Function.comp_def]`.
-/
theorem algSat_eq (a q : ℕ) (B : Multiset ℂˣ) :
    UpperTheory.V.Af.algSat a q B =
      B.map fun b : ℂˣ => (((q : ℝ) ^ (((a : ℝ) - 1) / 2) : ℝ) : ℂ) * (b : ℂ) := by
  unfold UpperTheory.V.Af.algSat
  simp only [Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton, Multiset.map_map,
    Function.comp_def]

/- English proof (translation)
Introduce `q hq a B hB j hj hne`. Establish `hsat : GlobalTheory.LFun.satEig q a B a = (B.map fun b : ℂˣ => (b : ℂ)).prod`. Unfold `GlobalTheory.LFun.satEig`. Rewrite using `[esymm_top _ a (by rw [Multiset.card_map, hB])]`. Simplify using the standard rewrite rules.

Establish `hcard : Multiset.card (UpperTheory.V.Af.algSat a q B) = a`. Rewrite using `[algSat_eq, Multiset.card_map, hB]`. Establish `hprod : (UpperTheory.V.Af.algSat a q B).prod = (q : ℂ) ^ Nat.choose a 2 * GlobalTheory.LFun.satEig q a B a`. Rewrite using `[hsat, ← half_pow, algSat_eq, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hB]`. Establish `hq' : (q : ℂ) ^ Nat.choose a 2 ≠ 0` using `pow_ne_zero _ (Nat.cast_ne_zero.mpr hq)`.

Establish `hP : (UpperTheory.V.Af.algSat a q B).prod ≠ 0`. Rewrite using `[hprod]`. Conclude with `mul_ne_zero hq' hne`. Establish `hall : ∀ x ∈ UpperTheory.V.Af.algSat a q B, x ≠ 0`. Introduce and unpack `x hx rfl`.

Conclude with `hP (Multiset.prod_eq_zero hx)`. Rewrite using `[← esymm_inv_mul_prod _ hall j (a - j) (by omega), hprod]`. Clear the denominators using the available nonvanishing facts.
-/
theorem esymm_inv_algSat : ∀ {q : ℕ}, q ≠ (0 : ℕ) → ∀ {a : ℕ} {B : Multiset ℂˣ},
    Multiset.card B = a → ∀ {j : ℕ}, j ≤ a → GlobalTheory.LFun.satEig q a B a ≠ (0 : ℂ) →
    Multiset.esymm (Multiset.map (fun (x : ℂ) ↦ x⁻¹) (UpperTheory.V.Af.algSat a q B)) j =
      Multiset.esymm (UpperTheory.V.Af.algSat a q B) (a - j) *
        (((↑q : ℂ) ^ Nat.choose a (2 : ℕ))⁻¹ * (GlobalTheory.LFun.satEig q a B a)⁻¹) := by
  intro q hq a B hB j hj hne
  have hsat : GlobalTheory.LFun.satEig q a B a = (B.map fun b : ℂˣ => (b : ℂ)).prod := by
    unfold GlobalTheory.LFun.satEig
    rw [esymm_top _ a (by rw [Multiset.card_map, hB])]
    simp
  have hcard : Multiset.card (UpperTheory.V.Af.algSat a q B) = a := by
    rw [algSat_eq, Multiset.card_map, hB]
  have hprod : (UpperTheory.V.Af.algSat a q B).prod =
      (q : ℂ) ^ Nat.choose a 2 * GlobalTheory.LFun.satEig q a B a := by
    rw [hsat, ← half_pow, algSat_eq, Multiset.prod_map_mul,
      Multiset.map_const', Multiset.prod_replicate, hB]
  have hq' : (q : ℂ) ^ Nat.choose a 2 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hq)
  have hP : (UpperTheory.V.Af.algSat a q B).prod ≠ 0 := by
    rw [hprod]
    exact mul_ne_zero hq' hne
  have hall : ∀ x ∈ UpperTheory.V.Af.algSat a q B, x ≠ 0 := by
    rintro x hx rfl
    exact hP (Multiset.prod_eq_zero hx)
  rw [← esymm_inv_mul_prod _ hall j (a - j) (by omega), hprod]
  field_simp

end GlobalTheory.ElementarySymmetricInverse
