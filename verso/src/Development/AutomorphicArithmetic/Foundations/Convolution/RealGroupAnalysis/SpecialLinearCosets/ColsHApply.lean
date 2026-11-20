import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.CosetSum
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.CosetSpan
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.IsCompactBoxSet

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

/- English proof (translation)
Take `⟨h1, h2⟩` from `GroundTheory.LocalField.mem_schwartzBruhat.1 ha`. Conclude with `GroundTheory.LocalField.mem_schwartzBruhat.2 ⟨h1.comp_continuous (continuous_id.mul continuous_const), h2.comp_homeomorph (Homeomorph.mulRight y)⟩`.
-/
private theorem tr_mem {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] {a : G → ℂ}
    (ha : a ∈ SB G) (y : G) : (fun x => a (x * y)) ∈ SB G := by
  obtain ⟨h1, h2⟩ := GroundTheory.LocalField.mem_schwartzBruhat.1 ha
  exact GroundTheory.LocalField.mem_schwartzBruhat.2
    ⟨h1.comp_continuous (continuous_id.mul continuous_const), h2.comp_homeomorph (Homeomorph.mulRight y)⟩

/- English proof (translation)
Use `GroundTheory.LocalField.mem_schwartzBruhat.2 ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Distinguish the cases in `hx : x ∈ U`. Use `filter_upwards [hUo.mem_nhds hx] with y hy`.

Establish `hy' : y ∈ U` using `hy`. Simplify using `[ind, hx, hy']`. Use `filter_upwards [(U.isClosed_of_isOpen hUo).isOpen_compl.mem_nhds hx] with y hy`. Establish `hy' : y ∉ U` using `hy`. Simplify using `[ind, hx, hy']`.

Conclude with `HasCompactSupport.intro hUc fun x hx => by simp [ind, hx]`.
-/
private theorem ind_mem {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G)
    (hUo : IsOpen (U : Set G)) (hUc : IsCompact (U : Set G)) : ind U ∈ SB G := by
  refine GroundTheory.LocalField.mem_schwartzBruhat.2 ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ U
    · filter_upwards [hUo.mem_nhds hx] with y hy
      have hy' : y ∈ U := hy
      simp [ind, hx, hy']
    · filter_upwards [(U.isClosed_of_isOpen hUo).isOpen_compl.mem_nhds hx] with y hy
      have hy' : y ∉ U := hy
      simp [ind, hx, hy']
  · exact HasCompactSupport.intro hUc fun x hx => by simp [ind, hx]

/- English proof (translation)
Establish `e : a = ∑ g ∈ s, cf g • (⟨_, tr_mem a'.2 g⁻¹⟩ : SB G)`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`. Rewrite using `[h x, Submodule.coe_sum, Finset.sum_apply]`. Both sides reduce to the same expression.

Rewrite using `[e, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul, hL g⁻¹ a' _ fun _ => rfl]`.
-/
private theorem ifnSum {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    (L : SB G →ₗ[ℂ] ℂ) (hL : ∀ (y : G) (a a' : SB G), (∀ m, a'.1 m = a.1 (m * y)) → L a' = L a)
    (a a' : SB G) (s : Finset G) (cf : G → ℂ) (h : ∀ x, a.1 x = ∑ g ∈ s, cf g * a'.1 (x * g⁻¹)) :
    L a = (∑ g ∈ s, cf g) * L a' := by
  have e : a = ∑ g ∈ s, cf g • (⟨_, tr_mem a'.2 g⁻¹⟩ : SB G) := by
    apply Subtype.ext
    funext x
    rw [h x, Submodule.coe_sum, Finset.sum_apply]
    rfl
  rw [e, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smul, smul_eq_mul, hL g⁻¹ a' _ fun _ => rfl]

/- English proof (translation)
Establish `ratio : ∀ (U U' : Subgroup G) (hUo : IsOpen (U : Set G)) (hUc : IsCompact (U : Set G)) (hUo' : IsOpen (U' : Set G)) (hUc' : IsCompact (U' : Set G)), U' ≤ U → l ⟨_, ind_mem U hUo hUc⟩ * I ⟨_, ind_mem U' hUo' hUc'⟩ = l ⟨_, ind_mem U' hUo' hUc'⟩ * I ⟨_, ind_mem U hUo hUc⟩`. Introduce `U U' hUo hUc hUo' hUc' hle`. Take `⟨s, -, -, hs⟩` from `cosetSum G U U' hle hUc hUo'`. Establish `h : ∀ x, (⟨_, ind_mem U hUo hUc⟩ : SB G).1 x = ∑ g ∈ s, (fun _ => (1 : ℂ)) g * (⟨_, ind_mem U' hUo' hUc'⟩ : SB G).1 (x * g⁻¹)`. Introduce `x`.

Simplify using `using hs x`. Rewrite using `[ifnSum l hl _ _ s _ h, ifnSum I hI _ _ s _ h]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨U₀, hU₀o, hU₀c, -⟩` from `hG Set.univ Filter.univ_mem`. Use `⟨l ⟨_, ind_mem U₀ hU₀o hU₀c⟩ / I ⟨_, ind_mem U₀ hU₀o hU₀c⟩, ?_⟩` and prove the remaining obligations.

Establish `h0 : I ⟨_, ind_mem U₀ hU₀o hU₀c⟩ ≠ 0` using `hne U₀ _ hU₀o hU₀c rfl`. Introduce `a`. Take `⟨U, s, cf, hUo, hUc, -, hs⟩` from `cosetSpan G hG a.1 a.2 Set.univ Filter.univ_mem`. Establish `hWo : IsOpen ((U ⊓ U₀ : Subgroup G) : Set G)`. Rewrite using `[Subgroup.coe_inf]`.

Conclude with `hUo.inter hU₀o`. Establish `hWc : IsCompact ((U ⊓ U₀ : Subgroup G) : Set G)`. Rewrite using `[Subgroup.coe_inf]`. Conclude with `hUc.inter_right (U₀.isClosed_of_isOpen hU₀o)`. Establish `hW : I ⟨_, ind_mem _ hWo hWc⟩ ≠ 0` using `hne _ _ hWo hWc rfl`.

Establish `e1` using `ratio U _ hUo hUc hWo hWc inf_le_left`. Establish `e2` using `ratio U₀ _ hU₀o hU₀c hWo hWc inf_le_right`. Establish `h : ∀ x, a.1 x = ∑ g ∈ s, cf g * (⟨_, ind_mem U hUo hUc⟩ : SB G).1 (x * g⁻¹)`. Introduce `x`. Rewrite using `[hs x]`.

Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm g⁻¹ x]`. Rewrite using `[ifnSum l hl _ _ s _ h, ifnSum I hI _ _ s _ h]`. Establish `key : l ⟨_, ind_mem U hUo hUc⟩ = l ⟨_, ind_mem U₀ hU₀o hU₀c⟩ / I ⟨_, ind_mem U₀ hU₀o hU₀c⟩ * I ⟨_, ind_mem U hUo hUc⟩`. Rewrite using `[div_mul_eq_mul_div, eq_div_iff h0]`.

Apply `mul_right_cancel₀ hW` to reduce the goal to its premises. Take the linear combination `(I ⟨_, ind_mem U₀ hU₀o hU₀c⟩) * e1 - (I ⟨_, ind_mem U hUo hUc⟩) * e2`. Rewrite using `[key]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem ifnAbs {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (hG : Lgrp G) (l I : SB G →ₗ[ℂ] ℂ)
    (hl : ∀ (y : G) (a a' : SB G), (∀ m, a'.1 m = a.1 (m * y)) → l a' = l a)
    (hI : ∀ (y : G) (a a' : SB G), (∀ m, a'.1 m = a.1 (m * y)) → I a' = I a)
    (hne : ∀ (U : Subgroup G) (a : SB G), IsOpen (U : Set G) → IsCompact (U : Set G) → a.1 = ind U → I a ≠ 0) :
    ∃ c : ℂ, ∀ a : SB G, l a = c * I a := by
  have ratio : ∀ (U U' : Subgroup G) (hUo : IsOpen (U : Set G)) (hUc : IsCompact (U : Set G))
      (hUo' : IsOpen (U' : Set G)) (hUc' : IsCompact (U' : Set G)), U' ≤ U →
      l ⟨_, ind_mem U hUo hUc⟩ * I ⟨_, ind_mem U' hUo' hUc'⟩ =
        l ⟨_, ind_mem U' hUo' hUc'⟩ * I ⟨_, ind_mem U hUo hUc⟩ := by
    intro U U' hUo hUc hUo' hUc' hle
    obtain ⟨s, -, -, hs⟩ := cosetSum G U U' hle hUc hUo'
    have h : ∀ x, (⟨_, ind_mem U hUo hUc⟩ : SB G).1 x =
        ∑ g ∈ s, (fun _ => (1 : ℂ)) g * (⟨_, ind_mem U' hUo' hUc'⟩ : SB G).1 (x * g⁻¹) := by
      intro x
      simpa using hs x
    rw [ifnSum l hl _ _ s _ h, ifnSum I hI _ _ s _ h]
    ring
  obtain ⟨U₀, hU₀o, hU₀c, -⟩ := hG Set.univ Filter.univ_mem
  refine ⟨l ⟨_, ind_mem U₀ hU₀o hU₀c⟩ / I ⟨_, ind_mem U₀ hU₀o hU₀c⟩, ?_⟩
  have h0 : I ⟨_, ind_mem U₀ hU₀o hU₀c⟩ ≠ 0 := hne U₀ _ hU₀o hU₀c rfl
  intro a
  obtain ⟨U, s, cf, hUo, hUc, -, hs⟩ := cosetSpan G hG a.1 a.2 Set.univ Filter.univ_mem
  have hWo : IsOpen ((U ⊓ U₀ : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]
    exact hUo.inter hU₀o
  have hWc : IsCompact ((U ⊓ U₀ : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]
    exact hUc.inter_right (U₀.isClosed_of_isOpen hU₀o)
  have hW : I ⟨_, ind_mem _ hWo hWc⟩ ≠ 0 := hne _ _ hWo hWc rfl
  have e1 := ratio U _ hUo hUc hWo hWc inf_le_left
  have e2 := ratio U₀ _ hU₀o hU₀c hWo hWc inf_le_right
  have h : ∀ x, a.1 x = ∑ g ∈ s, cf g * (⟨_, ind_mem U hUo hUc⟩ : SB G).1 (x * g⁻¹) := by
    intro x
    rw [hs x]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [mul_comm g⁻¹ x]
  rw [ifnSum l hl _ _ s _ h, ifnSum I hI _ _ s _ h]
  have key : l ⟨_, ind_mem U hUo hUc⟩ = l ⟨_, ind_mem U₀ hU₀o hU₀c⟩ / I ⟨_, ind_mem U₀ hU₀o hU₀c⟩ * I ⟨_, ind_mem U hUo hUc⟩ := by
    rw [div_mul_eq_mul_div, eq_div_iff h0]
    apply mul_right_cancel₀ hW
    linear_combination (I ⟨_, ind_mem U₀ hU₀o hU₀c⟩) * e1 - (I ⟨_, ind_mem U hUo hUc⟩) * e2
  rw [key]
  ring

section Meas
variable {F : Type} [Field F] [NumberField F] {v : P F}

private def colsH : ((Fin 2 → Kv v) × (Fin 2 → Kv v)) ≃ₜ M2 v where
  toFun p := cols p.1 p.2
  invFun X := (fun i => X i 0, fun i => X i 1)
  left_inv p := by
    ext i <;> fin_cases i <;> simp [cols]
  right_inv X := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cols]
  continuous_toFun := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp only [cols] <;> simp <;> fun_prop
  continuous_invFun := by
    refine Continuous.prodMk ?_ ?_ <;> refine continuous_pi fun i => ?_ <;> fun_prop

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem colsH_apply (p : (Fin 2 → Kv v) × (Fin 2 → Kv v)) : colsH p = cols p.1 p.2 := rfl

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [cols]`.
-/
private theorem cols_add (p q : (Fin 2 → Kv v) × (Fin 2 → Kv v)) :
    cols (p + q).1 (p + q).2 = cols p.1 p.2 + cols q.1 q.2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cols]

/- English proof (translation)
Take `⟨h1, h2⟩` from `GroundTheory.LocalField.mem_schwartzBruhat.1 ha`. Use `haveI : (μ2 v).IsAddHaarMeasure := by unfold μ2; infer_instance`. Conclude with `(h1.continuous.comp colsH.continuous).integrable_of_hasCompactSupport (h2.comp_homeomorph colsH)`.
-/
private theorem int_sb {a : M2 v → ℂ} (ha : a ∈ SB (M2 v)) :
    Integrable (fun p : (Fin 2 → Kv v) × (Fin 2 → Kv v) => a (cols p.1 p.2)) ((μ2 v).prod (μ2 v)) := by
  obtain ⟨h1, h2⟩ := GroundTheory.LocalField.mem_schwartzBruhat.1 ha
  haveI : (μ2 v).IsAddHaarMeasure := by unfold μ2; infer_instance
  exact (h1.continuous.comp colsH.continuous).integrable_of_hasCompactSupport (h2.comp_homeomorph colsH)

private noncomputable def IMl : SB (M2 v) →ₗ[ℂ] ℂ where
  toFun a := IM a.1
  map_add' a b := by
    simp only [IM]
    exact integral_add (int_sb a.2) (int_sb b.2)
  map_smul' c a := by
    simp only [IM, RingHom.id_apply, smul_eq_mul]
    exact integral_const_mul c _

end Meas

/- English proof (translation)
Introduce `F _ _ v ℓ hℓ`. Use `haveI : (μ2 v).IsAddHaarMeasure := by unfold μ2; infer_instance`. Establish `hI : ∀ (y : M2 v) (a a' : SB (M2 v)), (∀ m, a'.1 m = a.1 (m + y)) → IM a'.1 = IM a.1`. Introduce `y a a' h`. Establish `e : (fun p : (Fin 2 → Kv v) × (Fin 2 → Kv v) => a'.1 (cols p.1 p.2)) = fun p => (fun p : (Fin 2 → Kv v) × (Fin 2 → Kv v) => a.1 (cols p.1 p.2)) (p + colsH.symm y)`.

Use function extensionality and compare the values at `p`. Establish `hy : cols (colsH.symm y).1 (colsH.symm y).2 = y` using `colsH.apply_symm_apply y`. Simplify using `only [cols_add, hy]`. Conclude with `h _`. Simplify using `only [IM]`.

Rewrite using `[e]`. Conclude with `integral_add_right_eq_self (μ := (μ2 v).prod (μ2 v)) (fun p : (Fin 2 → Kv v) × (Fin 2 → Kv v) => a.1 (cols p.1 p.2)) (colsH.symm y)`. Establish `hne : ∀ (U : Subgroup (Multiplicative (M2 v))) (a : SB (M2 v)), IsOpen (U : Set (Multiplicative (M2 v))) → IsCompact (U : Set (Multiplicative (M2 v))) → a.1 = ind U → IM a.1 ≠ 0`. Introduce `U a hUo hUc ha`. Set `S : Set ((Fin 2 → Kv v) × (Fin 2 → Kv v))` to `colsH ⁻¹' {X : M2 v | Multiplicative.ofAdd X ∈ U}`.

Establish `hSo : IsOpen S` using `IsOpen.preimage colsH.continuous hUo`. Establish `hSc : IsCompact S` using `colsH.isCompact_preimage.2 hUc`. Establish `hSn : S.Nonempty` using `⟨colsH.symm (0 : M2 v), by show colsH (colsH.symm (0 : M2 v)) ∈ {X : M2 v | Multiplicative.ofAdd X ∈ U}`. Rewrite using `[colsH.apply_symm_apply]`. Conclude with `U.one_mem⟩`.

Establish `e : (fun p : (Fin 2 → Kv v) × (Fin 2 → Kv v) => a.1 (cols p.1 p.2)) = S.indicator fun _ => (1 : ℂ)`. Use function extensionality and compare the values at `p`. Rewrite using `[ha]`. Distinguish the cases in `hp : p ∈ S`. Rewrite using `[Set.indicator_of_mem hp]`.

Conclude with `Set.indicator_of_mem (s := (U : Set (Multiplicative (M2 v)))) hp _`. Rewrite using `[Set.indicator_of_notMem hp]`. Conclude with `Set.indicator_of_notMem (s := (U : Set (Multiplicative (M2 v)))) hp _`. Simplify using `only [IM]`. Rewrite using `[e, integral_indicator_const _ hSo.measurableSet]`.

Establish `hpos : ((μ2 v).prod (μ2 v)) S ≠ 0` using `(hSo.measure_pos _ hSn).ne'`. Establish `hfin : ((μ2 v).prod (μ2 v)) S ≠ ⊤` using `hSc.measure_lt_top.ne`. Establish `: ((μ2 v).prod (μ2 v)).real S ≠ 0` using `ENNReal.toReal_ne_zero.2 ⟨hpos, hfin⟩`. Simplify using `using this`. Use `haveI : T2Space (Multiplicative (M2 v)) := inferInstanceAs (T2Space (M2 v))`.

Take `⟨c, hc⟩` from `ifnAbs (G := Multiplicative (M2 v)) (lgrp F v).2 ℓ IMl (fun y a a' h => hℓ (Multiplicative.toAdd y) a a' h) (fun y a a' h => hI (Multiplicative.toAdd y) a a' h) (fun U a hUo hUc ha => hne U a hUo hUc ha)`. Conclude with `⟨c, hc⟩`.
-/
theorem UpperTheory.ConvolutionTheory.R2.I.invFn :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F) (ℓ : SB (M2 v) →ₗ[ℂ] ℂ), (∀ (y : M2 v) (a a' : SB (M2 v)), (∀ m, a'.1 m = a.1 (m + y)) → ℓ a' = ℓ a) →
      ∃ c : ℂ, ∀ a : SB (M2 v), ℓ a = c * IM a.1 := by
  intro F _ _ v ℓ hℓ
  haveI : (μ2 v).IsAddHaarMeasure := by unfold μ2; infer_instance
  have hI : ∀ (y : M2 v) (a a' : SB (M2 v)), (∀ m, a'.1 m = a.1 (m + y)) → IM a'.1 = IM a.1 := by
    intro y a a' h
    have e : (fun p : (Fin 2 → Kv v) × (Fin 2 → Kv v) => a'.1 (cols p.1 p.2)) =
        fun p => (fun p : (Fin 2 → Kv v) × (Fin 2 → Kv v) => a.1 (cols p.1 p.2)) (p + colsH.symm y) := by
      funext p
      have hy : cols (colsH.symm y).1 (colsH.symm y).2 = y := colsH.apply_symm_apply y
      simp only [cols_add, hy]
      exact h _
    simp only [IM]
    rw [e]
    exact integral_add_right_eq_self (μ := (μ2 v).prod (μ2 v)) (fun p : (Fin 2 → Kv v) × (Fin 2 → Kv v) => a.1 (cols p.1 p.2)) (colsH.symm y)
  have hne : ∀ (U : Subgroup (Multiplicative (M2 v))) (a : SB (M2 v)), IsOpen (U : Set (Multiplicative (M2 v))) →
      IsCompact (U : Set (Multiplicative (M2 v))) → a.1 = ind U → IM a.1 ≠ 0 := by
    intro U a hUo hUc ha
    let S : Set ((Fin 2 → Kv v) × (Fin 2 → Kv v)) := colsH ⁻¹' {X : M2 v | Multiplicative.ofAdd X ∈ U}
    have hSo : IsOpen S := IsOpen.preimage colsH.continuous hUo
    have hSc : IsCompact S := colsH.isCompact_preimage.2 hUc
    have hSn : S.Nonempty := ⟨colsH.symm (0 : M2 v), by
      show colsH (colsH.symm (0 : M2 v)) ∈ {X : M2 v | Multiplicative.ofAdd X ∈ U}
      rw [colsH.apply_symm_apply]
      exact U.one_mem⟩
    have e : (fun p : (Fin 2 → Kv v) × (Fin 2 → Kv v) => a.1 (cols p.1 p.2)) = S.indicator fun _ => (1 : ℂ) := by
      funext p
      rw [ha]
      by_cases hp : p ∈ S
      · rw [Set.indicator_of_mem hp]
        exact Set.indicator_of_mem (s := (U : Set (Multiplicative (M2 v)))) hp _
      · rw [Set.indicator_of_notMem hp]
        exact Set.indicator_of_notMem (s := (U : Set (Multiplicative (M2 v)))) hp _
    simp only [IM]
    rw [e, integral_indicator_const _ hSo.measurableSet]
    have hpos : ((μ2 v).prod (μ2 v)) S ≠ 0 := (hSo.measure_pos _ hSn).ne'
    have hfin : ((μ2 v).prod (μ2 v)) S ≠ ⊤ := hSc.measure_lt_top.ne
    have : ((μ2 v).prod (μ2 v)).real S ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hpos, hfin⟩
    simpa using this
  haveI : T2Space (Multiplicative (M2 v)) := inferInstanceAs (T2Space (M2 v))
  obtain ⟨c, hc⟩ := ifnAbs (G := Multiplicative (M2 v)) (lgrp F v).2 ℓ IMl
    (fun y a a' h => hℓ (Multiplicative.toAdd y) a a' h)
    (fun y a a' h => hI (Multiplicative.toAdd y) a a' h)
    (fun U a hUo hUc ha => hne U a hUo hUc ha)
  exact ⟨c, hc⟩
