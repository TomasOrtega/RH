import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

/- English proof (translation)
Use `Continuous.units_map _ ?_` and prove the remaining obligations. Establish `hs : Continuous (sInf E : Cinf E → Ad E)` using `(GlobalTheory.CuspRep.continuous_infEq E).prodMk continuous_const`. Conclude with `continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)`.
-/
private theorem inf_cont (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) :
    Continuous (infGL E a) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sInf E : Cinf E → Ad E) := (GlobalTheory.CuspRep.continuous_infEq E).prodMk continuous_const
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨hu, ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.coe_units_inv]`. Use `continuous_iff_continuousAt.2 fun x => ?_` and prove the remaining obligations. Take `⟨d, hd⟩` from `(Matrix.isUnit_iff_isUnit_det _).1 (u x).isUnit`. Use `ContinuousAt.comp (f := fun x => (u x).val) (continuousAt_matrix_inv _ ?_) hu.continuousAt` and prove the remaining obligations.

Rewrite using `[← hd]`. Conclude with `NormedRing.inverse_continuousAt d`.
-/
private theorem unit_cont (E : Type) [Field E] [NumberField E] (a : ℕ) {X : Type} [TopologicalSpace X]
    (u : X → GL (Fin a) (Cinf E)) (hu : Continuous fun x => (u x).val) : Continuous u := by
  refine Units.continuous_iff.2 ⟨hu, ?_⟩
  simp only [Matrix.coe_units_inv]
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨d, hd⟩ := (Matrix.isUnit_iff_isUnit_det _).1 (u x).isUnit
  refine ContinuousAt.comp (f := fun x => (u x).val) (continuousAt_matrix_inv _ ?_) hu.continuousAt
  rw [← hd]
  exact NormedRing.inverse_continuousAt d

/- English proof (translation)
Introduce `E _ _ _ a φ u w`. Use `⟨fun g => ?_, fun Z hZ h0 hw g x hx => ?_⟩` and prove the remaining obligations. Use `((φ.2 g).mul (u.2 g)).congr fun x hx => ?_` and prove the remaining obligations. Establish `h : IsUnit (Matrix.of x)` using `hx`. Simplify using `only [chart, dif_pos h]`.

Establish `h : IsUnit (Matrix.of x)` using `hx`. Establish `e : ∀ y ∈ invSet E a, chart (fun g => φ.1 g / w.1 g) g y = chart φ.1 g y * (chart w.1 g y)⁻¹`. Introduce `y hy`. Establish `h' : IsUnit (Matrix.of y)` using `hy`. Simplify using `only [chart, dif_pos h', div_eq_mul_inv]`.

Distinguish the cases in `hz : g * infGL E a h.unit ∈ Z`. Establish `hne : chart w.1 g x ≠ 0`. Rewrite using `[chart, dif_pos h]`. Conclude with `hw _ hz`. Conclude with `((φ.2 g x hx).mul ((w.2 g x hx).inv hne)).congr e (e x hx)`.

Set `v : invSet E a → GL (Fin a) (Cinf E)` to `fun y => (show IsUnit (Matrix.of y.1) from y.2).unit`. Establish `hv : Continuous v` using `unit_cont E a v continuous_subtype_val`. Establish `hc : Continuous fun y : invSet E a => g * infGL E a (v y)` using `continuous_const.mul ((inf_cont E a).comp hv)`. Establish `ho : IsOpen {y : invSet E a | g * infGL E a (v y) ∉ Z}` using `hZ.isOpen_compl.preimage hc`. Establish `hn : ∀ᶠ y : invSet E a in 𝓝 ⟨x, hx⟩, g * infGL E a (v y) ∉ Z` using `ho.mem_nhds hz`.

Establish `hv : ∀ᶠ y in 𝓝[invSet E a] x, chart (fun g => φ.1 g / w.1 g) g y = 0`. Rewrite using `[nhdsWithin_eq_map_subtype_coe hx, eventually_map]`. Use `filter_upwards [hn] with y hy`. Establish `h' : IsUnit (Matrix.of y.1)` using `y.2`. Rewrite using `[chart, dif_pos h', h0 _ hy, zero_div]`.

Conclude with `(contDiffWithinAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hv (hv.self_of_nhdsWithin hx)`.
-/
theorem UpperTheory.V.Cj.H.smDiv :
    UpperTheory.V.Cj.H.SmDiv := by
  intro E _ _ _ a φ u w
  refine ⟨fun g => ?_, fun Z hZ h0 hw g x hx => ?_⟩
  · refine ((φ.2 g).mul (u.2 g)).congr fun x hx => ?_
    have h : IsUnit (Matrix.of x) := hx
    simp only [chart, dif_pos h]
  · have h : IsUnit (Matrix.of x) := hx
    have e : ∀ y ∈ invSet E a, chart (fun g => φ.1 g / w.1 g) g y = chart φ.1 g y * (chart w.1 g y)⁻¹ := by
      intro y hy
      have h' : IsUnit (Matrix.of y) := hy
      simp only [chart, dif_pos h', div_eq_mul_inv]
    by_cases hz : g * infGL E a h.unit ∈ Z
    · have hne : chart w.1 g x ≠ 0 := by
        rw [chart, dif_pos h]
        exact hw _ hz
      exact ((φ.2 g x hx).mul ((w.2 g x hx).inv hne)).congr e (e x hx)
    · let v : invSet E a → GL (Fin a) (Cinf E) := fun y => (show IsUnit (Matrix.of y.1) from y.2).unit
      have hv : Continuous v := unit_cont E a v continuous_subtype_val
      have hc : Continuous fun y : invSet E a => g * infGL E a (v y) :=
        continuous_const.mul ((inf_cont E a).comp hv)
      have ho : IsOpen {y : invSet E a | g * infGL E a (v y) ∉ Z} := hZ.isOpen_compl.preimage hc
      have hn : ∀ᶠ y : invSet E a in 𝓝 ⟨x, hx⟩, g * infGL E a (v y) ∉ Z := ho.mem_nhds hz
      have hv : ∀ᶠ y in 𝓝[invSet E a] x, chart (fun g => φ.1 g / w.1 g) g y = 0 := by
        rw [nhdsWithin_eq_map_subtype_coe hx, eventually_map]
        filter_upwards [hn] with y hy
        have h' : IsUnit (Matrix.of y.1) := y.2
        rw [chart, dif_pos h', h0 _ hy, zero_div]
      exact (contDiffWithinAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hv (hv.self_of_nhdsWithin hx)
