import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingNumberFieldTwist
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsSncChartStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SncChartDivisorEquationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncChartKltCriterion

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

noncomputable def DivOver.ordHom {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (E : DivOver p) : X.functionFieldˣ →* Multiplicative ℤ where
  toFun f := Multiplicative.ofAdd (E.ord f)
  map_one' := by simp
  map_mul' f g := by simp [E.ord_mul]

/- English proof (translation)
Establish `h` using `congrArg Multiplicative.toAdd (map_prod E.ordHom (fun j => f j ^ e j) s)`. Rewrite `h` using `[toAdd_prod]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[map_zpow, toAdd_zpow, smul_eq_mul]`.

Both sides reduce to the same expression.
-/
theorem DivOver.ord_prod_zpow {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (E : DivOver p) {ι : Type} (s : Finset ι) (f : ι → X.functionFieldˣ) (e : ι → ℤ) :
    E.ord (∏ j ∈ s, f j ^ e j) = ∑ j ∈ s, e j * E.ord (f j) := by
  have h := congrArg Multiplicative.toAdd (map_prod E.ordHom (fun j => f j ^ e j) s)
  rw [toAdd_prod] at h
  calc E.ord (∏ j ∈ s, f j ^ e j) = Multiplicative.toAdd (E.ordHom (∏ j ∈ s, f j ^ e j)) := rfl
    _ = ∑ j ∈ s, Multiplicative.toAdd (E.ordHom (f j ^ e j)) := h
    _ = ∑ j ∈ s, e j * E.ord (f j) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_zpow, toAdd_zpow, smul_eq_mul]
      rfl

/- English proof (translation)
Take `⟨a, ha, hav⟩` from `hv`. Establish `h1 : (v : X.functionField) ∈ E.ring` using `hE _ ⟨a, hav⟩`. Establish `hinv : algebraMap (X.presheaf.stalk x) X.functionField (↑(ha.unit⁻¹)) = ((v⁻¹ : X.functionFieldˣ) : X.functionField)`. Rewrite using `[Units.val_inv_eq_inv_val]`. Use `eq_inv_of_mul_eq_one_right ?_` and prove the remaining obligations.

Rewrite using `[← hav, ← map_mul, IsUnit.mul_val_inv, map_one]`. Establish `h2 : ((v⁻¹ : X.functionFieldˣ) : X.functionField) ∈ E.ring` using `hE _ ⟨_, hinv⟩`. Establish `e1` using `(E.ord_nonneg_iff v).mpr h1`. Establish `e2` using `(E.ord_nonneg_iff v⁻¹).mpr h2`. Rewrite `e2` using `[E.ord_inv]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem DivOver.ord_eq_zero_of_unitAt {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} {E : DivOver p} {x : X} (hE : E.Through x) (v : X.functionFieldˣ)
    (hv : UnitAt x (v : X.functionField)) : E.ord v = 0 := by
  obtain ⟨a, ha, hav⟩ := hv
  have h1 : (v : X.functionField) ∈ E.ring := hE _ ⟨a, hav⟩
  have hinv : algebraMap (X.presheaf.stalk x) X.functionField (↑(ha.unit⁻¹)) =
      ((v⁻¹ : X.functionFieldˣ) : X.functionField) := by
    rw [Units.val_inv_eq_inv_val]
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← hav, ← map_mul, IsUnit.mul_val_inv, map_one]
  have h2 : ((v⁻¹ : X.functionFieldˣ) : X.functionField) ∈ E.ring := hE _ ⟨_, hinv⟩
  have e1 := (E.ord_nonneg_iff v).mpr h1
  have e2 := (E.ord_nonneg_iff v⁻¹).mpr h2
  rw [E.ord_inv] at e2
  omega

/- English proof (translation)
Introduce `k _ _ Y _ _ q n _ η hη K G m B hm hK hsnc hsupp y g hG E hE`. Use `haveI : Smooth q := SmoothOfRelativeDimension.smooth n q`. Establish `hdim : topologicalKrullDim Y = n` using `HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth q n inferInstance`. Take `⟨U, hy, z, J, w, u, hc⟩` from `exists_isSncChart k Y q n B hsnc y`. Establish `hgen : genericPoint Y ∈ U` using `((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr ⟨y, trivial, hy⟩`.

Establish `hfg` using `isFreeGen_formOf hgen hc.frame`. Establish `hω0 : formOf U hgen (dOn q z) ≠ 0`. Introduce `h0`. Use `hfg.1 (a₁ := 0) (a₂ := 1) (by simp only [h0, smul_zero])` as an intermediate fact. Conclude with `zero_ne_one this`.

Establish `hr : hfg.repr η ≠ 0`. Introduce `h0`. Apply `hη` to reduce the goal to its premises. Rewrite using `[← hfg.repr_smul η, h0, zero_smul]`. Establish `hηh : η = ((Units.mk0 _ hr : Y.functionFieldˣ) : Y.functionField) • formOf U hgen (dOn q z)` using `(hfg.repr_smul η).symm`.

Use `set h : Y.functionFieldˣ := Units.mk0 _ hr with hdef`. Establish `hKy : K.IsEqn y h` using `hK U (dOn q z) hc.frame y hy h hηh`. Establish `hD1 : (G - m • K).IsEqn y (g / h ^ m)` using `hG.sub (hKy.nsmul m)`. Establish `hD2` using `IsSncChart.isEqn_monomial k Y q n B y U hy z J w u hc (G - m • K) hsupp`. Establish `hunit` using `(hD1.iff_unitAt).mp hD2`.

Establish `hzero` using `DivOver.ord_eq_zero_of_unitAt hE ((∏ j ∈ J, u j ^ (G - m • K).mult (w j)) / (g / h ^ m)) (by simpa using hunit)`. Rewrite `hzero` using `[div_eq_mul_inv, E.ord_mul, E.ord_inv, div_eq_mul_inv, E.ord_mul, E.ord_inv, DivOver.ord_prod_zpow, E.ord_pow]`. Establish `hform : E.formOrd η = E.ord h + E.formOrd (formOf U hgen (dOn q z))`. Rewrite using `[hηh]`. Conclude with `E.formOrd_smul hdim hω0 h`.

Establish `hF0 : 0 ≤ E.formOrd (formOf U hgen (dOn q z))` using `E.formOrd_formOf_nonneg hdim hy hE (dOn q z) hω0`. Establish `hF1` using `E.sum_ord_sub_one_le_formOrd_dOn hdim hy hE z hω0 (J := ↥J) (fun j => j.1) Subtype.val_injective (fun j => u j.1) (fun j => hc.val j.1 j.2)`. Rewrite `hF1` using `[Finset.sum_coe_sort J (fun j => E.ord (u j))]`. Establish `hnn : ∀ j ∈ J, 0 ≤ E.ord (u j)` using `fun j hj => (E.ord_nonneg_iff _).mpr (hE _ (by rw [hc.val j hj]; exact regAt_fnOf hy _ _))`. Use `set F := E.formOrd (formOf U hgen (dOn q z)) with hFdef`.

Use `set S := ∑ j ∈ J, E.ord (u j) with hSdef`. Use `set T := ∑ j ∈ J, (G - m • K).mult (w j) * E.ord (u j) with hTdef`. Establish `hm' : (0 : ℚ) < m` using `by exact_mod_cast hm`. Establish `hdisc : discrep E η m g = ((m * F - T : ℤ) : ℚ) / m`. Establish `hg' : E.ord g = m * E.ord h + T` using `by linarith`.

Unfold `discrep`. Rewrite using `[hform, hg']`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hdisc]`. Prove the components needed by the constructor for the conclusion. Introduce `hlt`. Establish `hT : T ≤ (m - 1) * S`. Rewrite using `[hSdef, hTdef, Finset.mul_sum]`.

Use `Finset.sum_le_sum (fun j hj => ?_)` and prove the remaining obligations. Use `hlt (w j) (hc.spec j hj)` as an intermediate fact. Conclude with `mul_le_mul_of_nonneg_right (by omega) (hnn j hj)`. Establish `hS0 : 0 ≤ S` using `Finset.sum_nonneg hnn`. Establish `key : -(m : ℤ) < m * F - T`.

Break down `eq_or_lt_of_le hS0 with hS | hS` into its components or cases. Rewrite `hT` using `[← hS]`. Establish `: (m : ℤ) * F ≥ 0` using `mul_nonneg (by exact_mod_cast hm.le) hF0`. Establish `hm0 : (0 : ℤ) < m` using `by exact_mod_cast hm`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `: (m : ℤ) * (S - 1) ≤ m * F` using `mul_le_mul_of_nonneg_left (by linarith) (by exact_mod_cast hm.le)`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[lt_div_iff₀ hm']`. Establish `: ((-(m : ℤ) : ℤ) : ℚ) < ((m * F - T : ℤ) : ℚ)` using `by exact_mod_cast key`. Move the coercions through the operations in `at this ⊢`.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce `hle`. Establish `hT : T ≤ m * S`. Rewrite using `[hSdef, hTdef, Finset.mul_sum]`. Use `Finset.sum_le_sum (fun j hj => ?_)` and prove the remaining obligations.

Conclude with `mul_le_mul_of_nonneg_right (hle (w j) (hc.spec j hj)) (hnn j hj)`. Establish `key : -(m : ℤ) ≤ m * F - T`. Establish `: (m : ℤ) * (S - 1) ≤ m * F` using `mul_le_mul_of_nonneg_left (by linarith) (by exact_mod_cast hm.le)`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[le_div_iff₀ hm']`.

Establish `: ((-(m : ℤ) : ℤ) : ℚ) ≤ ((m * F - T : ℤ) : ℚ)` using `by exact_mod_cast key`. Move the coercions through the operations in `at this ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem coeff_criterion_snc : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (η : RatForms q n), η ≠ 0 → ∀ (K G : CartierDiv Y) (m : ℕ) (B : Closeds Y), 0 < m → IsDivOfForm K η → FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) → (G - m • K).supp ≤ B → ∀ (y : Y) (g : Y.functionFieldˣ), G.IsEqn y g → ∀ E : DivOver q, E.Through y → ((∀ w, w ⤳ y → (G - m • K).mult w < m) → -1 < discrep E η m g) ∧ ((∀ w, w ⤳ y → (G - m • K).mult w ≤ m) → -1 ≤ discrep E η m g) := by
  intro k _ _ Y _ _ q n _ η hη K G m B hm hK hsnc hsupp y g hG E hE
  haveI : Smooth q := SmoothOfRelativeDimension.smooth n q
  have hdim : topologicalKrullDim Y = n :=
    HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth q n inferInstance
  obtain ⟨U, hy, z, J, w, u, hc⟩ := exists_isSncChart k Y q n B hsnc y
  have hgen : genericPoint Y ∈ U :=
    ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr ⟨y, trivial, hy⟩
  have hfg := isFreeGen_formOf hgen hc.frame
  have hω0 : formOf U hgen (dOn q z) ≠ 0 := by
    intro h0
    have := hfg.1 (a₁ := 0) (a₂ := 1) (by simp only [h0, smul_zero])
    exact zero_ne_one this
  have hr : hfg.repr η ≠ 0 := by
    intro h0
    apply hη
    rw [← hfg.repr_smul η, h0, zero_smul]
  have hηh : η = ((Units.mk0 _ hr : Y.functionFieldˣ) : Y.functionField) • formOf U hgen (dOn q z) :=
    (hfg.repr_smul η).symm
  set h : Y.functionFieldˣ := Units.mk0 _ hr with hdef
  have hKy : K.IsEqn y h := hK U (dOn q z) hc.frame y hy h hηh
  have hD1 : (G - m • K).IsEqn y (g / h ^ m) := hG.sub (hKy.nsmul m)
  have hD2 := IsSncChart.isEqn_monomial k Y q n B y U hy z J w u hc (G - m • K) hsupp
  have hunit := (hD1.iff_unitAt).mp hD2
  have hzero := DivOver.ord_eq_zero_of_unitAt hE
    ((∏ j ∈ J, u j ^ (G - m • K).mult (w j)) / (g / h ^ m)) (by simpa using hunit)
  rw [div_eq_mul_inv, E.ord_mul, E.ord_inv, div_eq_mul_inv, E.ord_mul, E.ord_inv,
    DivOver.ord_prod_zpow, E.ord_pow] at hzero
  have hform : E.formOrd η = E.ord h + E.formOrd (formOf U hgen (dOn q z)) := by
    rw [hηh]
    exact E.formOrd_smul hdim hω0 h
  have hF0 : 0 ≤ E.formOrd (formOf U hgen (dOn q z)) :=
    E.formOrd_formOf_nonneg hdim hy hE (dOn q z) hω0
  have hF1 := E.sum_ord_sub_one_le_formOrd_dOn hdim hy hE z hω0 (J := ↥J) (fun j => j.1)
    Subtype.val_injective (fun j => u j.1) (fun j => hc.val j.1 j.2)
  rw [Finset.sum_coe_sort J (fun j => E.ord (u j))] at hF1
  have hnn : ∀ j ∈ J, 0 ≤ E.ord (u j) := fun j hj =>
    (E.ord_nonneg_iff _).mpr (hE _ (by rw [hc.val j hj]; exact regAt_fnOf hy _ _))
  set F := E.formOrd (formOf U hgen (dOn q z)) with hFdef
  set S := ∑ j ∈ J, E.ord (u j) with hSdef
  set T := ∑ j ∈ J, (G - m • K).mult (w j) * E.ord (u j) with hTdef
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  have hdisc : discrep E η m g = ((m * F - T : ℤ) : ℚ) / m := by
    have hg' : E.ord g = m * E.ord h + T := by linarith
    unfold discrep
    rw [hform, hg']
    push_cast
    field_simp
    ring
  rw [hdisc]
  constructor
  · intro hlt
    have hT : T ≤ (m - 1) * S := by
      rw [hSdef, hTdef, Finset.mul_sum]
      refine Finset.sum_le_sum (fun j hj => ?_)
      have := hlt (w j) (hc.spec j hj)
      exact mul_le_mul_of_nonneg_right (by omega) (hnn j hj)
    have hS0 : 0 ≤ S := Finset.sum_nonneg hnn
    have key : -(m : ℤ) < m * F - T := by
      rcases eq_or_lt_of_le hS0 with hS | hS
      · rw [← hS] at hT
        have : (m : ℤ) * F ≥ 0 := mul_nonneg (by exact_mod_cast hm.le) hF0
        have hm0 : (0 : ℤ) < m := by exact_mod_cast hm
        linarith
      · have : (m : ℤ) * (S - 1) ≤ m * F :=
          mul_le_mul_of_nonneg_left (by linarith) (by exact_mod_cast hm.le)
        nlinarith
    rw [lt_div_iff₀ hm']
    have : ((-(m : ℤ) : ℤ) : ℚ) < ((m * F - T : ℤ) : ℚ) := by exact_mod_cast key
    push_cast at this ⊢
    linarith
  · intro hle
    have hT : T ≤ m * S := by
      rw [hSdef, hTdef, Finset.mul_sum]
      refine Finset.sum_le_sum (fun j hj => ?_)
      exact mul_le_mul_of_nonneg_right (hle (w j) (hc.spec j hj)) (hnn j hj)
    have key : -(m : ℤ) ≤ m * F - T := by
      have : (m : ℤ) * (S - 1) ≤ m * F :=
        mul_le_mul_of_nonneg_left (by linarith) (by exact_mod_cast hm.le)
      nlinarith
    rw [le_div_iff₀ hm']
    have : ((-(m : ℤ) : ℤ) : ℚ) ≤ ((m * F - T : ℤ) : ℚ) := by exact_mod_cast key
    push_cast at this ⊢
    linarith

end GlobalTheory.Discrepancy
