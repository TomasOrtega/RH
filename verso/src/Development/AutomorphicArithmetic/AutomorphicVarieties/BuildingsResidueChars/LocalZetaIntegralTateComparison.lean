import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LaurentBlockInduction.LdDefs
import GroundTheory.AutomorphicForms.GL2.GJFEBlockConv
import GroundTheory.AutomorphicForms.GL2.GJUnramified

noncomputable section

open MeasureTheory Polynomial GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Parabolic
open GroundTheory.Automorphic.GodementJacquet
open scoped NNReal Classical ValuativeRel

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Conclude with `ordDet_nonneg_of_integral`. Introduce `h i j`. Rewrite using `[Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]`. Establish `hne : (g : Matrix (Fin 1) (Fin 1) F) 0 0 ≠ 0`.

Simplify `det_ne_zero g` using `[Matrix.det_unique]`. Rewrite using `[← GroundTheory.LocalField.mem_valBall_zero_iff, GroundTheory.LocalField.mem_valBall_iff_le_ord hne]`. Simplify `h` using `[ordDet, Matrix.det_unique]`.
-/
private theorem integral_iff_one (g : GL (Fin 1) F) :
    (∀ i j, (g : Matrix (Fin 1) (Fin 1) F) i j ∈ 𝒪[F]) ↔ 0 ≤ ordDet g := by
  constructor
  · exact ordDet_nonneg_of_integral
  · intro h i j
    rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
    have hne : (g : Matrix (Fin 1) (Fin 1) F) 0 0 ≠ 0 := by
      simpa [Matrix.det_unique] using det_ne_zero g
    rw [← GroundTheory.LocalField.mem_valBall_zero_iff, GroundTheory.LocalField.mem_valBall_iff_le_ord hne]
    simpa [ordDet, Matrix.det_unique] using h

/- English proof (translation)
Simplify using `only [tile, Set.mem_ofPred_eq]`. Use `push_cast`. Use linear arithmetic over natural numbers and integers.
-/
private theorem mem_tile_one (g : GL (Fin 1) F) : g ∈ tile F 1 0 ↔ ordDet g = 0 := by
  simp only [tile, Set.mem_ofPred_eq]
  push_cast
  omega

/- English proof (translation)
Establish `h0` using `(mem_tile_one g).1 hg`. Rewrite using `[mem_integralGL_iff]`. Use `⟨(integral_iff_one g).2 (by omega), (integral_iff_one g⁻¹).2 ?_⟩` and prove the remaining obligations. Rewrite using `[ordDet_inv]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem int_of_tile {g : GL (Fin 1) F} (hg : g ∈ tile F 1 0) : g ∈ integralGL F 1 := by
  have h0 := (mem_tile_one g).1 hg
  rw [mem_integralGL_iff]
  refine ⟨(integral_iff_one g).2 (by omega), (integral_iff_one g⁻¹).2 ?_⟩
  rw [ordDet_inv]
  omega

/- English proof (translation)
Establish `h` using `isCompact_shell F 1 0 0`. Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `g`. Simplify using `only [Set.mem_ofPred_eq, pow_zero, one_mul, mem_tile_one]`. Conclude with `⟨fun h0 => ⟨(integral_iff_one g).2 h0.ge, h0⟩, fun h => h.2⟩`.
-/
private theorem isCompact_tile_one : IsCompact (tile F 1 0) := by
  have h := isCompact_shell F 1 0 0
  convert h using 1
  ext g
  simp only [Set.mem_ofPred_eq, pow_zero, one_mul, mem_tile_one]
  exact ⟨fun h0 => ⟨(integral_iff_one g).2 h0.ge, h0⟩, fun h => h.2⟩

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `F _ _ _ _ _ _ μ _`. Use `⟨integralIndicator F 1, isSchwartzBruhat_integralIndicator, ((μ.real (tile F 1 0) : ℝ) : ℂ), ?_, ?_⟩` and prove the remaining obligations. Establish `hpos : 0 < μ (tile F 1 0)` using `(isOpen_tile 0).measure_pos μ ⟨1, (mem_tile_one 1).2 ordDet_one⟩`. Establish `hfin : μ (tile F 1 0) < ⊤` using `isCompact_tile_one.measure_lt_top`. Use `show (((μ (tile F 1 0)).toReal : ℝ) : ℂ) ≠ 0`.

Conclude with `(ENNReal.toReal_pos hpos.ne' hfin.ne).ne'` after adjusting the coercions. Introduce `α c hc hcK s hs`. Establish `hs1 : ‖α * qs F s‖ < 1` using `by simpa using hs`. Establish `hint` using `hc.integrable_zeta μ (isSchwartzBruhat_integralIndicator (F := F) (n := 1)) hs`. Establish `h1` using `hasSum_integral_tile μ hint`.

Establish `hterm : ∀ j : ℤ, (∫ g in tile F 1 0, integralIndicator F 1 ↑(centralUnif F 1 ^ j * g) * detPow (centralUnif F 1 ^ j * g) s * c (centralUnif F 1 ^ j * g) ∂μ) = if 0 ≤ j then (α * qs F s) ^ j * c 1 * ((μ.real (tile F 1 0) : ℝ) : ℂ) else 0`. Introduce `j`. Establish `hEq : Set.EqOn (fun g => integralIndicator F 1 ↑(centralUnif F 1 ^ j * g) * detPow (centralUnif F 1 ^ j * g) s * c (centralUnif F 1 ^ j * g)) (fun _ => if 0 ≤ j then (α * qs F s) ^ j * c 1 else 0) (tile F 1 0)`. Introduce `g hg`. Establish `hgK` using `int_of_tile hg`.

Establish `h0` using `(mem_tile_one g).1 hg`. Establish `hiff : ((↑(centralUnif F 1 ^ j * g) : Matrix (Fin 1) (Fin 1) F) ∈ integralMatrixSet F 1) ↔ 0 ≤ j`. Rewrite using `[mem_integralMatrixSet, integral_iff_one, ordDet_centralUnif_zpow_mul, h0]`. Use `push_cast`. Use linear arithmetic over natural numbers and integers.

Establish `hind : integralIndicator F 1 ↑(centralUnif F 1 ^ j * g) = if 0 ≤ j then 1 else 0`. Unfold `integralIndicator`. Distinguish the cases in `hj : 0 ≤ j`. Rewrite using `[Set.indicator_of_mem (hiff.2 hj), if_pos hj]`. Both sides reduce to the same expression.

Rewrite using `[Set.indicator_of_notMem (fun h => hj (hiff.1 h)), if_neg hj]`. Simplify using `only`. Rewrite using `[hind, detPow_centralUnif_zpow_mul, detPow_of_mem_integralGL hgK, hc.zpow_mul, hcK g hgK]`. Use `split_ifs`. Use `push_cast`.

Rewrite using `[mul_one, mul_zpow]`. Put the polynomial expressions in normal form. Simplify using the standard rewrite rules. Rewrite using `[setIntegral_congr_fun (measurableSet_tile 0) hEq, setIntegral_const, Complex.real_smul]`. Apply the tactic sequence `split_ifs <;> ring`.

Establish `h2` using `h1`. Simplify using `only [hterm] at h2`. Establish `hgeo : HasSum (fun j : ℤ => if 0 ≤ j then (α * qs F s) ^ j * c 1 * ((μ.real (tile F 1 0) : ℝ) : ℂ) else 0) ((1 - α * qs F s)⁻¹ * (c 1 * ((μ.real (tile F 1 0) : ℝ) : ℂ)))`. Establish `hn` using `(hasSum_geometric_of_norm_lt_one hs1).mul_right (c 1 * ((μ.real (tile F 1 0) : ℝ) : ℂ))`. Rewrite using `[← Nat.cast_injective.hasSum_iff]`.

Simplify `hn` using `[Function.comp_def, zpow_natCast, mul_assoc]`. Introduce `j hj`. Establish `hn' : ¬ 0 ≤ j` using `fun h => hj ⟨j.toNat, Int.toNat_of_nonneg h⟩`. Simplify using `[hn']`. Rewrite using `[h2.unique hgeo, div_eq_mul_inv]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.local_zeta_integral_tate_comparison :
    UpperTheory.V.Z.Gam.LdTate := by
  intro F _ _ _ _ _ _ μ _
  refine ⟨integralIndicator F 1, isSchwartzBruhat_integralIndicator, ((μ.real (tile F 1 0) : ℝ) : ℂ), ?_, ?_⟩
  · have hpos : 0 < μ (tile F 1 0) := (isOpen_tile 0).measure_pos μ ⟨1, (mem_tile_one 1).2 ordDet_one⟩
    have hfin : μ (tile F 1 0) < ⊤ := isCompact_tile_one.measure_lt_top
    show (((μ (tile F 1 0)).toReal : ℝ) : ℂ) ≠ 0
    exact_mod_cast (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
  · intro α c hc hcK s hs
    have hs1 : ‖α * qs F s‖ < 1 := by simpa using hs
    have hint := hc.integrable_zeta μ (isSchwartzBruhat_integralIndicator (F := F) (n := 1)) hs
    have h1 := hasSum_integral_tile μ hint
    have hterm : ∀ j : ℤ, (∫ g in tile F 1 0, integralIndicator F 1 ↑(centralUnif F 1 ^ j * g) *
        detPow (centralUnif F 1 ^ j * g) s * c (centralUnif F 1 ^ j * g) ∂μ) =
        if 0 ≤ j then (α * qs F s) ^ j * c 1 * ((μ.real (tile F 1 0) : ℝ) : ℂ) else 0 := by
      intro j
      have hEq : Set.EqOn (fun g => integralIndicator F 1 ↑(centralUnif F 1 ^ j * g) *
          detPow (centralUnif F 1 ^ j * g) s * c (centralUnif F 1 ^ j * g))
          (fun _ => if 0 ≤ j then (α * qs F s) ^ j * c 1 else 0) (tile F 1 0) := by
        intro g hg
        have hgK := int_of_tile hg
        have h0 := (mem_tile_one g).1 hg
        have hiff : ((↑(centralUnif F 1 ^ j * g) : Matrix (Fin 1) (Fin 1) F) ∈ integralMatrixSet F 1) ↔ 0 ≤ j := by
          rw [mem_integralMatrixSet, integral_iff_one, ordDet_centralUnif_zpow_mul, h0]
          push_cast
          omega
        have hind : integralIndicator F 1 ↑(centralUnif F 1 ^ j * g) = if 0 ≤ j then 1 else 0 := by
          unfold integralIndicator
          by_cases hj : 0 ≤ j
          · rw [Set.indicator_of_mem (hiff.2 hj), if_pos hj]
            rfl
          · rw [Set.indicator_of_notMem (fun h => hj (hiff.1 h)), if_neg hj]
        simp only
        rw [hind, detPow_centralUnif_zpow_mul, detPow_of_mem_integralGL hgK, hc.zpow_mul, hcK g hgK]
        split_ifs
        · push_cast
          rw [mul_one, mul_zpow]
          ring_nf
        · simp
      rw [setIntegral_congr_fun (measurableSet_tile 0) hEq, setIntegral_const, Complex.real_smul]
      split_ifs <;> ring
    have h2 := h1
    simp only [hterm] at h2
    have hgeo : HasSum (fun j : ℤ => if 0 ≤ j then (α * qs F s) ^ j * c 1 * ((μ.real (tile F 1 0) : ℝ) : ℂ) else 0)
        ((1 - α * qs F s)⁻¹ * (c 1 * ((μ.real (tile F 1 0) : ℝ) : ℂ))) := by
      have hn := (hasSum_geometric_of_norm_lt_one hs1).mul_right (c 1 * ((μ.real (tile F 1 0) : ℝ) : ℂ))
      rw [← Nat.cast_injective.hasSum_iff]
      · simpa [Function.comp_def, zpow_natCast, mul_assoc] using hn
      · intro j hj
        have hn' : ¬ 0 ≤ j := fun h => hj ⟨j.toNat, Int.toNat_of_nonneg h⟩
        simp [hn']
    rw [h2.unique hgeo, div_eq_mul_inv]
    ring
