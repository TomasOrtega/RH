import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterTrivialOfNonzeroSumStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationVectorHomomorphismStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteNormOneUnitsTrivialValuationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicRealPartPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedStandardValuesAtIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIntegralUnitShift
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralUnitTranslateValuation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnramifiedCharCompUnitsMap
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.FexTheta.Orth

open GlobalTheory.CompanionTheory.FexTheta.ProdSum GlobalTheory.CompanionTheory.ThetaUnits

variable {K : Type} [Field K] [NumberField K] {c : HeckeCharacter K} {v : Pl}

def ctH : LM c v → (Qv v)ˣ →* ℂˣ
  | LM.sp w₁ w₂ _ => cAt c v w₁ * (cAt c v w₂)⁻¹
  | LM.ns .. => 1

/- English proof (translation)
Apply the tactic sequence `cases L <;> rfl`.
-/
theorem ctH_coe (L : LM c v) (x : (Qv v)ˣ) : ((ctH L x : ℂˣ) : ℂ) = L.ct x := by
  cases L <;> rfl

/- English proof (translation)
Rewrite using `[← ctH_coe, map_one]`. Both sides reduce to the same expression.
-/
theorem ct_one (L : LM c v) : L.ct 1 = 1 := by
  rw [← ctH_coe, map_one]; rfl

/- English proof (translation)
Simplify using `only [← ctH_coe, map_mul, Units.val_mul]`.
-/
theorem ct_mul (L : LM c v) (x y : (Qv v)ˣ) : L.ct (x * y) = L.ct x * L.ct y := by
  simp only [← ctH_coe, map_mul, Units.val_mul]

/- English proof (translation)
Introduce `e he`. Establish `h1` using `(measurePreserving_mulLeft_unQ v e he).integral_comp' (fun x => L.ct x)`. Establish `h2 : ∀ x, L.ct (MeasurableEquiv.mulLeft e x) = L.ct e * L.ct x` using `fun x => ct_mul L e x`. Rewrite `h1` using `[h2]`. Rewrite `h1` using `[integral_const_mul]`.

Conclude with `mul_right_cancel₀ h (by rw [h1, one_mul])`.
-/
theorem ct_unit_of_integral_ne (L : LM c v) (h : ∫ x in unQ v, L.ct x ∂multHaar (Qv v) ≠ 0) :
    ∀ e ∈ unQ v, L.ct e = 1 := by
  intro e he
  have h1 := (measurePreserving_mulLeft_unQ v e he).integral_comp' (fun x => L.ct x)
  have h2 : ∀ x, L.ct (MeasurableEquiv.mulLeft e x) = L.ct e * L.ct x := fun x => ct_mul L e x
  simp_rw [h2] at h1
  rw [integral_const_mul] at h1
  exact mul_right_cancel₀ h (by rw [h1, one_mul])

/- English proof (translation)
Introduce `e he`. Consider the cases of `L with`. Consider the case `ns w σ η Φ => rfl`. Consider the case `sp w₁ w₂ Φ`. Break down `h with h | hU` into its components or cases.

Conclude with `absurd trivial h`. Establish `r₁ : IsUnramifiedChar (cAt c v w₁)` using `GlobalTheory.CompanionTheory.SphTheta.isUnramifiedChar_comp_unitsMap (Qv v) (Kv K w₁) (localChar c w₁) (hU w₁).1`. Establish `r₂ : IsUnramifiedChar (cAt c v w₂)` using `GlobalTheory.CompanionTheory.SphTheta.isUnramifiedChar_comp_unitsMap (Qv v) (Kv K w₂) (localChar c w₂) (hU w₂).1`. Establish `hmem : e ∈ unitFiltrationUnits (Qv v) 0`. Use `he` as an intermediate fact.

Rewrite `this` using `[unQ_eq_ordShell, ordShell_zero]`. Conclude with `this`. Establish `he₁ : cAt c v w₁ e = 1` using `MonoidHom.mem_ker.1 (r₁ hmem)`. Establish `he₂ : cAt c v w₂ e = 1` using `MonoidHom.mem_ker.1 (r₂ hmem)`. Simplify using `[LM.ct, he₁, he₂]`.
-/
theorem ct_unit_of_unr (L : LM c v) (h : ¬ L.IsSp ∨ Unr c v) : ∀ e ∈ unQ v, L.ct e = 1 := by
  intro e he
  cases L with
  | ns w σ η Φ => rfl
  | sp w₁ w₂ Φ =>
    rcases h with h | hU
    · exact absurd trivial h
    have r₁ : IsUnramifiedChar (cAt c v w₁) :=
      GlobalTheory.CompanionTheory.SphTheta.isUnramifiedChar_comp_unitsMap (Qv v) (Kv K w₁) (localChar c w₁) (hU w₁).1
    have r₂ : IsUnramifiedChar (cAt c v w₂) :=
      GlobalTheory.CompanionTheory.SphTheta.isUnramifiedChar_comp_unitsMap (Qv v) (Kv K w₂) (localChar c w₂) (hU w₂).1
    have hmem : e ∈ unitFiltrationUnits (Qv v) 0 := by
      have := he
      rw [unQ_eq_ordShell, ordShell_zero] at this
      exact this
    have he₁ : cAt c v w₁ e = 1 := MonoidHom.mem_ker.1 (r₁ hmem)
    have he₂ : cAt c v w₂ e = 1 := MonoidHom.mem_ker.1 (r₂ hmem)
    simp [LM.ct, he₁, he₂]

/- English proof (translation)
Establish `hu : unifUnit (Qv v) ^ (-ord (x : Qv v)) * x ∈ unQ v`. Rewrite using `[mem_unQ_iff_ord_eq_zero, ord_units_mul, ord_unifUnit_zpow]`. Use linear arithmetic over natural numbers and integers. Establish `hx : x = unifUnit (Qv v) ^ ord (x : Qv v) * (unifUnit (Qv v) ^ (-ord (x : Qv v)) * x)`. Rewrite using `[← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]`.

Use `conv_rhs => rw [hx]`. Rewrite using `[ct_mul, hU _ hu, mul_one]`.
-/
theorem ct_eq_zpow_ord (L : LM c v) (hU : ∀ e ∈ unQ v, L.ct e = 1) (x : (Qv v)ˣ) :
    L.ct (unifUnit (Qv v) ^ ord (x : Qv v)) = L.ct x := by
  have hu : unifUnit (Qv v) ^ (-ord (x : Qv v)) * x ∈ unQ v := by
    rw [mem_unQ_iff_ord_eq_zero, ord_units_mul, ord_unifUnit_zpow]
    omega
  have hx : x = unifUnit (Qv v) ^ ord (x : Qv v) * (unifUnit (Qv v) ^ (-ord (x : Qv v)) * x) := by
    rw [← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
  conv_rhs => rw [hx]
  rw [ct_mul, hU _ hu, mul_one]

open Classical in

/- English proof (translation)
Establish `h1 : ctM M Sv m u = ∏ v ∈ m.support ∪ Sv, ((M v).ct (unifUnit (Qv v) ^ (m v)) * (M v).ct (if h : v ∈ Sv then u ⟨v, h⟩ else 1))` using `Finset.prod_congr rfl fun v _ => ct_mul _ _ _`. Rewrite using `[h1, Finset.prod_mul_distrib]`. Use `congr 1`. Establish `h2 : ∏ v ∈ m.support ∪ Sv, (M v).ct (if h : v ∈ Sv then u ⟨v, h⟩ else 1) = ∏ v ∈ Sv, (M v).ct (if h : v ∈ Sv then u ⟨v, h⟩ else 1)`. Use `symm`.

Use `Finset.prod_subset Finset.subset_union_right fun v _ hv => ?_` and prove the remaining obligations. Rewrite using `[dif_neg hv, ct_one]`. Rewrite using `[h2, ← Finset.prod_coe_sort]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[dif_pos v.2]`.
-/
theorem ctM_eq (M : ∀ v : Pl, LM c v) (Sv : Finset Pl) (m : Pl →₀ ℤ) (u : ∀ v : Sv, (Qv v.1)ˣ) :
    ctM M Sv m u = (∏ v ∈ m.support ∪ Sv, (M v).ct (unifUnit (Qv v) ^ (m v))) *
      ∏ v : Sv, (M v.1).ct (u v) := by
  have h1 : ctM M Sv m u = ∏ v ∈ m.support ∪ Sv, ((M v).ct (unifUnit (Qv v) ^ (m v)) *
      (M v).ct (if h : v ∈ Sv then u ⟨v, h⟩ else 1)) :=
    Finset.prod_congr rfl fun v _ => ct_mul _ _ _
  rw [h1, Finset.prod_mul_distrib]
  congr 1
  have h2 : ∏ v ∈ m.support ∪ Sv, (M v).ct (if h : v ∈ Sv then u ⟨v, h⟩ else 1) =
      ∏ v ∈ Sv, (M v).ct (if h : v ∈ Sv then u ⟨v, h⟩ else 1) := by
    symm
    refine Finset.prod_subset Finset.subset_union_right fun v _ hv => ?_
    rw [dif_neg hv, ct_one]
  rw [h2, ← Finset.prod_coe_sort]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [dif_pos v.2]

instance finiteU (v : Pl) : IsFiniteMeasure ((multHaar (Qv v)).restrict (unQ v)) :=
  ⟨by rw [Measure.restrict_apply_univ, multHaar_unQ]; simp⟩

def chi (M : ∀ v : Pl, LM c v) (m : Pl →₀ ℤ) : ℂ := ∏ᶠ v, (M v).ct (unifUnit (Qv v) ^ (m v))

/- English proof (translation)
Introduce `v hv`. Assume the negation of the conclusion as `h`. Establish `h0 : m v = 0` using `by simpa using h`. Conclude with `hv (by simp only [h0, zpow_zero, ct_one])`.
-/
theorem chi_support (M : ∀ v : Pl, LM c v) (m : Pl →₀ ℤ) :
    (Function.mulSupport fun v => (M v).ct (unifUnit (Qv v) ^ (m v))) ⊆ (m.support : Set Pl) := by
  intro v hv
  by_contra h
  have h0 : m v = 0 := by simpa using h
  exact hv (by simp only [h0, zpow_zero, ct_one])

open Classical in
/- English proof (translation)
The claim follows from `finprod_eq_prod_of_mulSupport_subset _ (by refine (chi_support M m).trans ?_ intro v hv simp only [Finset.coe_union, Set.mem_union] exact Or.inl hv)`.
-/
theorem chi_eq (M : ∀ v : Pl, LM c v) (Sv : Finset Pl) (m : Pl →₀ ℤ) :
    chi M m = ∏ v ∈ m.support ∪ Sv, (M v).ct (unifUnit (Qv v) ^ (m v)) :=
  finprod_eq_prod_of_mulSupport_subset _
    (by
      refine (chi_support M m).trans ?_
      intro v hv
      simp only [Finset.coe_union, Set.mem_union]
      exact Or.inl hv)

/- English proof (translation)
Unfold `chi`. Rewrite using `[← finprod_mul_distrib ((a.support.finite_toSet).subset (chi_support M a)) ((b.support.finite_toSet).subset (chi_support M b))]`. Use `finprod_congr fun v => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.add_apply, zpow_add, ct_mul]`.
-/
theorem chi_add (M : ∀ v : Pl, LM c v) (a b : Pl →₀ ℤ) : chi M (a + b) = chi M a * chi M b := by
  unfold chi
  rw [← finprod_mul_distrib ((a.support.finite_toSet).subset (chi_support M a))
    ((b.support.finite_toSet).subset (chi_support M b))]
  refine finprod_congr fun v => ?_
  rw [Finsupp.add_apply, zpow_add, ct_mul]

/- English proof (translation)
Repeatedly rewrite using `[ctM_eq, ← chi_eq]`. Rewrite using `[integral_const_mul]`. Use `congr 1`. Conclude with `integral_fintype_prod_eq_prod (𝕜 := ℂ) (fun (v : Sv) (x : (Qv v.1)ˣ) => (M v.1).ct x)`.
-/
theorem integral_ctM (M : ∀ v : Pl, LM c v) (Sv : Finset Pl) (m : Pl →₀ ℤ) :
    ∫ u, ctM M Sv m u ∂muU Sv =
      chi M m * ∏ v : Sv, ∫ x in unQ v.1, (M v.1).ct x ∂multHaar (Qv v.1) := by
  classical
  simp_rw [ctM_eq, ← chi_eq]
  rw [integral_const_mul]
  congr 1
  exact integral_fintype_prod_eq_prod (𝕜 := ℂ) (fun (v : Sv) (x : (Qv v.1)ˣ) => (M v.1).ct x)

def LgK (K : Type) [Field K] [NumberField K] {c : HeckeCharacter K} (M : ∀ v : Pl, LM c v)
    (hadd : ∀ a b : Kˣ, vK M (a * b) = vK M a + vK M b) : AddSubgroup (Pl →₀ ℤ) where
  carrier := {l | ∃ κ ∈ K1 K, l = vK M κ}
  zero_mem' := by
    refine ⟨1, one_mem _, ?_⟩
    have h := hadd 1 1
    rw [mul_one] at h
    exact (left_eq_add.mp h).symm
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, mul_mem ha hb, (hadd a b).symm⟩
  neg_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨a⁻¹, inv_mem ha, ?_⟩
    have h1 := hadd 1 1
    rw [mul_one] at h1
    have h0 : vK M (1 : Kˣ) = 0 := left_eq_add.mp h1
    have h := hadd a a⁻¹
    rw [mul_inv_cancel, h0] at h
    exact neg_eq_of_add_eq_zero_right h.symm

/- English proof (translation)
Introduce `K _ _ h2 _ c M hM R hR Sv hS hk hsum v x`. Take `⟨hord, hmem, hadd⟩` from `GlobalTheory.T.valuation_vector_homomorphism K h2 c M hM`. Rewrite `hsum` using `[integral_ctM]`. Rewrite `hsum` using `[← Finset.sum_mul]`. Establish `hχ : ∑ r ∈ R, chi M r ≠ 0` using `left_ne_zero_of_mul hsum`.

Establish `hP` using `right_ne_zero_of_mul hsum`. Establish `hU : ∀ v, ∀ e ∈ unQ v, (M v).ct e = 1`. Introduce `v`. Distinguish the cases in `hv : v ∈ Sv`. Conclude with `ct_unit_of_integral_ne _ (Finset.prod_ne_zero_iff.mp hP ⟨v, hv⟩ (Finset.mem_univ _))`.

Use `ct_unit_of_unr _ ?_` and prove the remaining obligations. Distinguish the cases in `hs : (M v).IsSp`. Conclude with `Or.inr (hS.2 v hv hs).1`. Conclude with `Or.inl hs`. Establish `hone : ∀ m ∈ Tm M, chi M m = 1`.

Use `GlobalTheory.T.character_trivial_of_nonzero_sum (Tm M) (LgK K M hadd) R (chi M) (fun a _ b _ => chi_add M a b) ?_ hR.1 ?_ hχ` and prove the remaining obligations. Introduce and unpack `_ ⟨κ, hκ, rfl⟩`. Use `⟨hmem κ, ?_⟩` and prove the remaining obligations. Rewrite using `[← hk κ hκ]`. Use `finprod_congr fun v => ?_` and prove the remaining obligations.

Rewrite using `[hord κ v]`. Conclude with `ct_eq_zpow_ord _ (hU v) _`. Introduce `m hm`. Take `⟨r, ⟨hr, κ, hκ, e⟩, huniq⟩` from `hR.2 m hm`. Use `⟨r, ⟨hr, vK M κ, ⟨κ, hκ, rfl⟩, e⟩, ?_⟩` and prove the remaining obligations.

Introduce and unpack `r' ⟨hr', _, ⟨κ', hκ', rfl⟩, e'⟩`. Conclude with `huniq r' ⟨hr', κ', hκ', e'⟩`. Establish `hpi : (M v).ct (unifUnit (Qv v)) = 1`. Distinguish the cases in `hs : (M v).IsSp`. Establish `hm : Finsupp.single v (1 : ℤ) ∈ Tm M`.

Introduce `w hw`. Distinguish the cases in `hwv : w = v`. Conclude with `hwv ▸ hs`. Conclude with `absurd (Finsupp.single_eq_of_ne hwv) hw`. Establish `h` using `hone _ hm`.

Unfold `chi at h`. Rewrite `h` using `[finprod_eq_single _ v ?_]`. Simplify using `using h`. Introduce `w hw`. Rewrite using `[Finsupp.single_eq_of_ne hw, zpow_zero, ct_one]`.

Use `revert hs`. Consider the cases of `M v with`. Consider the case `sp w₁ w₂ Φ => intro hs`. Conclude with `absurd trivial hs`. Consider the case `ns w σ η Φ => intro _`.

Both sides reduce to the same expression. Rewrite using `[← ct_eq_zpow_ord _ (hU v) x, ← ctH_coe, map_zpow]`. Establish `: ctH (M v) (unifUnit (Qv v)) = 1` using `Units.ext (by rw [ctH_coe, hpi]; rfl)`. Rewrite using `[this, one_zpow]`. Both sides reduce to the same expression.
-/
theorem weights_trivial : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ (c : HeckeCharacter K)
  (M : ∀ v : Pl, LM c v), AdmM M → ∀ R : Finset (Pl →₀ ℤ), IsReps M R → ∀ Sv : Finset Pl, GoodSv M Sv →
  (∀ κ ∈ K1 K, ∏ᶠ v, (M v).ct (k1 (M v) κ) = 1) → (∑ m ∈ R, ∫ u, ctM M Sv m u ∂muU Sv) ≠ 0 →
  ∀ (v : Pl) (x : (Qv v)ˣ), (M v).ct x = 1 := by
  intro K _ _ h2 _ c M hM R hR Sv hS hk hsum v x
  obtain ⟨hord, hmem, hadd⟩ := GlobalTheory.T.valuation_vector_homomorphism K h2 c M hM
  simp_rw [integral_ctM] at hsum
  rw [← Finset.sum_mul] at hsum
  have hχ : ∑ r ∈ R, chi M r ≠ 0 := left_ne_zero_of_mul hsum
  have hP := right_ne_zero_of_mul hsum
  have hU : ∀ v, ∀ e ∈ unQ v, (M v).ct e = 1 := by
    intro v
    by_cases hv : v ∈ Sv
    · exact ct_unit_of_integral_ne _ (Finset.prod_ne_zero_iff.mp hP ⟨v, hv⟩ (Finset.mem_univ _))
    · refine ct_unit_of_unr _ ?_
      by_cases hs : (M v).IsSp
      · exact Or.inr (hS.2 v hv hs).1
      · exact Or.inl hs
  have hone : ∀ m ∈ Tm M, chi M m = 1 := by
    refine GlobalTheory.T.character_trivial_of_nonzero_sum (Tm M) (LgK K M hadd) R (chi M) (fun a _ b _ => chi_add M a b) ?_ hR.1 ?_ hχ
    · rintro _ ⟨κ, hκ, rfl⟩
      refine ⟨hmem κ, ?_⟩
      rw [← hk κ hκ]
      refine finprod_congr fun v => ?_
      rw [hord κ v]
      exact ct_eq_zpow_ord _ (hU v) _
    · intro m hm
      obtain ⟨r, ⟨hr, κ, hκ, e⟩, huniq⟩ := hR.2 m hm
      refine ⟨r, ⟨hr, vK M κ, ⟨κ, hκ, rfl⟩, e⟩, ?_⟩
      rintro r' ⟨hr', _, ⟨κ', hκ', rfl⟩, e'⟩
      exact huniq r' ⟨hr', κ', hκ', e'⟩
  have hpi : (M v).ct (unifUnit (Qv v)) = 1 := by
    by_cases hs : (M v).IsSp
    · have hm : Finsupp.single v (1 : ℤ) ∈ Tm M := by
        intro w hw
        by_cases hwv : w = v
        · exact hwv ▸ hs
        · exact absurd (Finsupp.single_eq_of_ne hwv) hw
      have h := hone _ hm
      unfold chi at h
      rw [finprod_eq_single _ v ?_] at h
      · simpa using h
      · intro w hw
        rw [Finsupp.single_eq_of_ne hw, zpow_zero, ct_one]
    · revert hs
      cases M v with
      | sp w₁ w₂ Φ => intro hs; exact absurd trivial hs
      | ns w σ η Φ => intro _; rfl
  rw [← ct_eq_zpow_ord _ (hU v) x, ← ctH_coe, map_zpow]
  have : ctH (M v) (unifUnit (Qv v)) = 1 := Units.ext (by rw [ctH_coe, hpi]; rfl)
  rw [this, one_zpow]; rfl

end GlobalTheory.CompanionTheory.FexTheta.Orth
