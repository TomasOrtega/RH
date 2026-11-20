import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetVolSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SCompact
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NinfConjIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SigmaFiniteOfFcG

noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

open scoped Classical ENNReal
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full

/- English proof (translation)
Introduce `D X u h hh Ω hΩ`. Take `⟨h1, hmul, hinvN⟩` from `Formalism.L2.SG.Pf.psiInfChar_holds D X u`. Set `N : Subgroup X.B.I.Ginf` to `Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarCore.subOf (X.NinfU u) h1 (fun x hx y hy => (hmul x hx y hy).1) hinvN`. Establish `hNc : IsClosed (N : Set X.B.I.Ginf)` using `Formalism.L2.SG.Pf.Vanish2.ninf_closed X.B.I X.eR (X.zR u)`. Establish `hH : IsHaarOnSet X.B.I (N : Set X.B.I.Ginf) (X.muN u)` using `X.muN_haar u`.

Establish `hHa` using `Formalism.L2.SG.Pf.haarOnSet_isHaar_inst X.B.I N hNc (X.muN u) hH`. Take `⟨_, h0, hc, hl⟩` from `hH`. Establish `hfin : IsFiniteMeasureOnCompacts (X.muN u)` using `⟨hHa.2.1⟩`. Establish `hconj : ∀ g ∈ Hinf X u, ∀ n ∈ X.NinfU u, g * n * g⁻¹ ∈ X.NinfU u` using `fun g hg n hn => by`. Establish `hi : g⁻¹ ∈ Hinf X u` using `(Hinf X u).inv_mem hg`.

Establish `hfix : ∀ v, ∀ x ∈ fixSet X u, (uMat (g⁻¹ v)).mulVec (rv X.B.I v x) = rv X.B.I v x` using `hi`. Use `Formalism.L2.SG.CovariantRepresentation.ninf_conj X u g⁻¹ (fun v a => hfix v _ (Or.inl (Or.inl ⟨a, rfl⟩))) (fun v => hfix v _ (Or.inr rfl)) hn` as an intermediate fact. Simplify using `using this`. Establish `hcont : ∀ g : X.B.I.Ginf, Continuous fun s : X.B.I.Ginf => g * s * g⁻¹` using `fun g => (continuous_const.mul continuous_id).mul continuous_const`. Take `⟨K0, hK0c, hK0n⟩` from `exists_compact_mem_nhds (1 : X.B.I.Ginf)`.

Establish `hK0pos : 0 < X.muN u K0`. Establish `hpos` using `hHa.2.2 (interior K0) isOpen_interior ⟨1, mem_interior_iff_mem_nhds.2 hK0n, h1⟩`. Conclude with `lt_of_lt_of_le hpos (measure_mono interior_subset)`. Set `K : Set X.B.I.Ginf` to `(fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2 * p.1⁻¹) '' ((Hinf X u : Set X.B.I.Ginf) ×ˢ K0)`. Establish `hKc : IsCompact K` using `((Formalism.L2.SG.Pf.hinf_compact X u).prod hK0c).image ((continuous_fst.mul continuous_snd).mul continuous_fst.inv)`.

Establish `hK0K : K0 ⊆ K` using `fun k hk => ⟨(1, k), ⟨(Hinf X u).one_mem, hk⟩, by simp⟩`. Establish `hKpos : 0 < X.muN u K` using `lt_of_lt_of_le hK0pos (measure_mono hK0K)`. Establish `hKfin : X.muN u K ≠ ⊤` using `hKc.measure_lt_top.ne`. Establish `hKinv : ∀ g ∈ Hinf X u, (fun s => g * s * g⁻¹) ⁻¹' K = K`. Introduce `g hg`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨a, k⟩, ⟨ha, hk⟩, hx⟩`. Use `⟨(g⁻¹ * a, k), ⟨(Hinf X u).mul_mem ((Hinf X u).inv_mem hg) ha, hk⟩, ?_⟩` and prove the remaining obligations. Establish `hx' : a * k * a⁻¹ = g * x * g⁻¹` using `hx`.

Use `show g⁻¹ * a * k * (g⁻¹ * a)⁻¹ = x`. Combine the equalities or inequalities in the displayed calculation. Introduce and unpack `⟨⟨a, k⟩, ⟨ha, hk⟩, hx⟩`. Use `⟨(g * a, k), ⟨(Hinf X u).mul_mem hg ha, hk⟩, ?_⟩` and prove the remaining obligations. Establish `hx' : a * k * a⁻¹ = x` using `hx`.

Use `show g * a * k * (g * a)⁻¹ = g * x * g⁻¹`. Combine the equalities or inequalities in the displayed calculation. Establish `key : ∀ g ∈ Hinf X u, (X.muN u).map (fun s => g * s * g⁻¹) = X.muN u`. Introduce `g hg`. Establish `hm : Measurable fun s : X.B.I.Ginf => g * s * g⁻¹` using `(hcont g).measurable`.

Establish `hpre : ∀ S : Set X.B.I.Ginf, (fun s => g * s * g⁻¹) ⁻¹' S = (fun s => g⁻¹ * s * g⁻¹⁻¹) '' S`. Introduce `S`. Conclude with `(congrFun (Set.image_eq_preimage_of_inverse (f := fun s => g⁻¹ * s * g⁻¹⁻¹) (g := fun s => g * s * g⁻¹) (fun s => by show g * (g⁻¹ * s * g⁻¹⁻¹) * g⁻¹ = s; group) (fun s => by show g⁻¹ * (g * s * g⁻¹) * g⁻¹⁻¹ = s; group)) S).symm`. Establish `hν0 : (X.muN u).map (fun s => g * s * g⁻¹) ≠ 0`. Introduce `hz`.

Apply `h0` to reduce the goal to its premises. Use `congrArg (fun m : Measure X.B.I.Ginf => m Set.univ) hz` as an intermediate fact. Simplify using `only [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ, Measure.coe_zero, Pi.zero_apply] at this`. Conclude with `Measure.measure_univ_eq_zero.1 this`. Establish `hνc : (X.muN u).map (fun s => g * s * g⁻¹) (N : Set X.B.I.Ginf)ᶜ = 0`.

Rewrite using `[Measure.map_apply hm hNc.measurableSet.compl]`. Conclude with `measure_mono_null (fun s hs hsN => hs (hconj g hg s hsN)) hc`. Establish `hνi : ∀ t ∈ N, ((X.muN u).map (fun s => g * s * g⁻¹)).map (fun x => t * x) = (X.muN u).map (fun s => g * s * g⁻¹)`. Introduce `t ht`. Establish `ht' : g⁻¹ * t * g⁻¹⁻¹ ∈ X.NinfU u` using `hconj g⁻¹ ((Hinf X u).inv_mem hg) t ht`.

Rewrite using `[Measure.map_map (measurable_const_mul t) hm]`. Establish `e : (fun x => t * x) ∘ (fun s => g * s * g⁻¹) = (fun s => g * s * g⁻¹) ∘ (fun x => (g⁻¹ * t * g⁻¹⁻¹) * x)`. Use function extensionality and compare the values at `s`. Use `show t * (g * s * g⁻¹) = g * (g⁻¹ * t * g⁻¹⁻¹ * s) * g⁻¹`. Use `group`.

Rewrite using `[e, ← Measure.map_map hm (measurable_const_mul _), hl _ ht']`. Establish `hνf : IsFiniteMeasureOnCompacts ((X.muN u).map (fun s => g * s * g⁻¹))` using `⟨fun C hC => by`. Rewrite using `[Measure.map_apply hm hC.isClosed.measurableSet, hpre]`. Conclude with `(hC.image (hcont _)).measure_lt_top⟩`. Take `⟨c, _, hceq⟩` from `Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarCore.haar_unique N hNc (X.muN u) ((X.muN u).map (fun s => g * s * g⁻¹)) h0 hc hl hfin hνc hνi hνf`.

Establish `hK' : (X.muN u).map (fun s => g * s * g⁻¹) K = X.muN u K`. Rewrite using `[Measure.map_apply hm hKc.isClosed.measurableSet, hKinv g hg]`. Rewrite `hK'` using `[hceq, Measure.smul_apply, smul_eq_mul]`. Establish `hc1 : c = 1` using `(ENNReal.mul_left_inj hKpos.ne' hKfin).1 (hK'.trans (one_mul _).symm)`. Rewrite using `[hceq, hc1, one_smul]`.

Establish `hinv' : h⁻¹ ∈ Hinf X u` using `(Hinf X u).inv_mem hh`. Establish `e : (fun s => h * s * h⁻¹) '' Ω = (fun s => h⁻¹ * s * h⁻¹⁻¹) ⁻¹' Ω` using `congrFun (Set.image_eq_preimage_of_inverse (f := fun s => h * s * h⁻¹) (g := fun s => h⁻¹ * s * h⁻¹⁻¹) (fun s => by show h⁻¹ * (h * s * h⁻¹) * h⁻¹⁻¹ = s; group) (fun s => by show h * (h⁻¹ * s * h⁻¹⁻¹) * h⁻¹ = s; group)) Ω`. Rewrite using `[e, ← Measure.map_apply (hcont _).measurable hΩ, key _ hinv']`.
-/
theorem hinfConjC_holds : HinfConjC := by
  intro D X u h hh Ω hΩ
  obtain ⟨h1, hmul, hinvN⟩ := Formalism.L2.SG.Pf.psiInfChar_holds D X u
  let N : Subgroup X.B.I.Ginf :=
    Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarCore.subOf (X.NinfU u) h1 (fun x hx y hy => (hmul x hx y hy).1) hinvN
  have hNc : IsClosed (N : Set X.B.I.Ginf) := Formalism.L2.SG.Pf.Vanish2.ninf_closed X.B.I X.eR (X.zR u)
  have hH : IsHaarOnSet X.B.I (N : Set X.B.I.Ginf) (X.muN u) := X.muN_haar u
  have hHa := Formalism.L2.SG.Pf.haarOnSet_isHaar_inst X.B.I N hNc (X.muN u) hH
  obtain ⟨_, h0, hc, hl⟩ := hH
  have hfin : IsFiniteMeasureOnCompacts (X.muN u) := ⟨hHa.2.1⟩
  have hconj : ∀ g ∈ Hinf X u, ∀ n ∈ X.NinfU u, g * n * g⁻¹ ∈ X.NinfU u := fun g hg n hn => by
    have hi : g⁻¹ ∈ Hinf X u := (Hinf X u).inv_mem hg
    have hfix : ∀ v, ∀ x ∈ fixSet X u, (uMat (g⁻¹ v)).mulVec (rv X.B.I v x) = rv X.B.I v x := hi
    have := Formalism.L2.SG.CovariantRepresentation.ninf_conj X u g⁻¹ (fun v a => hfix v _ (Or.inl (Or.inl ⟨a, rfl⟩)))
      (fun v => hfix v _ (Or.inr rfl)) hn
    simpa using this
  have hcont : ∀ g : X.B.I.Ginf, Continuous fun s : X.B.I.Ginf => g * s * g⁻¹ := fun g =>
    (continuous_const.mul continuous_id).mul continuous_const

  obtain ⟨K0, hK0c, hK0n⟩ := exists_compact_mem_nhds (1 : X.B.I.Ginf)
  have hK0pos : 0 < X.muN u K0 := by
    have hpos := hHa.2.2 (interior K0) isOpen_interior ⟨1, mem_interior_iff_mem_nhds.2 hK0n, h1⟩
    exact lt_of_lt_of_le hpos (measure_mono interior_subset)
  let K : Set X.B.I.Ginf :=
    (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2 * p.1⁻¹) '' ((Hinf X u : Set X.B.I.Ginf) ×ˢ K0)
  have hKc : IsCompact K :=
    ((Formalism.L2.SG.Pf.hinf_compact X u).prod hK0c).image
      ((continuous_fst.mul continuous_snd).mul continuous_fst.inv)
  have hK0K : K0 ⊆ K := fun k hk => ⟨(1, k), ⟨(Hinf X u).one_mem, hk⟩, by simp⟩
  have hKpos : 0 < X.muN u K := lt_of_lt_of_le hK0pos (measure_mono hK0K)
  have hKfin : X.muN u K ≠ ⊤ := hKc.measure_lt_top.ne
  have hKinv : ∀ g ∈ Hinf X u, (fun s => g * s * g⁻¹) ⁻¹' K = K := by
    intro g hg
    ext x
    constructor
    · rintro ⟨⟨a, k⟩, ⟨ha, hk⟩, hx⟩
      refine ⟨(g⁻¹ * a, k), ⟨(Hinf X u).mul_mem ((Hinf X u).inv_mem hg) ha, hk⟩, ?_⟩
      have hx' : a * k * a⁻¹ = g * x * g⁻¹ := hx
      show g⁻¹ * a * k * (g⁻¹ * a)⁻¹ = x
      calc g⁻¹ * a * k * (g⁻¹ * a)⁻¹ = g⁻¹ * (a * k * a⁻¹) * g := by group
        _ = x := by rw [hx']; group
    · rintro ⟨⟨a, k⟩, ⟨ha, hk⟩, hx⟩
      refine ⟨(g * a, k), ⟨(Hinf X u).mul_mem hg ha, hk⟩, ?_⟩
      have hx' : a * k * a⁻¹ = x := hx
      show g * a * k * (g * a)⁻¹ = g * x * g⁻¹
      calc g * a * k * (g * a)⁻¹ = g * (a * k * a⁻¹) * g⁻¹ := by group
        _ = g * x * g⁻¹ := by rw [hx']

  have key : ∀ g ∈ Hinf X u, (X.muN u).map (fun s => g * s * g⁻¹) = X.muN u := by
    intro g hg
    have hm : Measurable fun s : X.B.I.Ginf => g * s * g⁻¹ := (hcont g).measurable
    have hpre : ∀ S : Set X.B.I.Ginf, (fun s => g * s * g⁻¹) ⁻¹' S = (fun s => g⁻¹ * s * g⁻¹⁻¹) '' S := by
      intro S
      exact (congrFun (Set.image_eq_preimage_of_inverse (f := fun s => g⁻¹ * s * g⁻¹⁻¹)
        (g := fun s => g * s * g⁻¹) (fun s => by show g * (g⁻¹ * s * g⁻¹⁻¹) * g⁻¹ = s; group)
        (fun s => by show g⁻¹ * (g * s * g⁻¹) * g⁻¹⁻¹ = s; group)) S).symm
    have hν0 : (X.muN u).map (fun s => g * s * g⁻¹) ≠ 0 := by
      intro hz
      apply h0
      have := congrArg (fun m : Measure X.B.I.Ginf => m Set.univ) hz
      simp only [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ, Measure.coe_zero, Pi.zero_apply] at this
      exact Measure.measure_univ_eq_zero.1 this
    have hνc : (X.muN u).map (fun s => g * s * g⁻¹) (N : Set X.B.I.Ginf)ᶜ = 0 := by
      rw [Measure.map_apply hm hNc.measurableSet.compl]
      exact measure_mono_null (fun s hs hsN => hs (hconj g hg s hsN)) hc
    have hνi : ∀ t ∈ N, ((X.muN u).map (fun s => g * s * g⁻¹)).map (fun x => t * x) =
        (X.muN u).map (fun s => g * s * g⁻¹) := by
      intro t ht
      have ht' : g⁻¹ * t * g⁻¹⁻¹ ∈ X.NinfU u := hconj g⁻¹ ((Hinf X u).inv_mem hg) t ht
      rw [Measure.map_map (measurable_const_mul t) hm]
      have e : (fun x => t * x) ∘ (fun s => g * s * g⁻¹) =
          (fun s => g * s * g⁻¹) ∘ (fun x => (g⁻¹ * t * g⁻¹⁻¹) * x) := by
        funext s
        show t * (g * s * g⁻¹) = g * (g⁻¹ * t * g⁻¹⁻¹ * s) * g⁻¹
        group
      rw [e, ← Measure.map_map hm (measurable_const_mul _), hl _ ht']
    have hνf : IsFiniteMeasureOnCompacts ((X.muN u).map (fun s => g * s * g⁻¹)) := ⟨fun C hC => by
      rw [Measure.map_apply hm hC.isClosed.measurableSet, hpre]
      exact (hC.image (hcont _)).measure_lt_top⟩
    obtain ⟨c, _, hceq⟩ := Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarCore.haar_unique N hNc (X.muN u)
      ((X.muN u).map (fun s => g * s * g⁻¹)) h0 hc hl hfin hνc hνi hνf
    have hK' : (X.muN u).map (fun s => g * s * g⁻¹) K = X.muN u K := by
      rw [Measure.map_apply hm hKc.isClosed.measurableSet, hKinv g hg]
    rw [hceq, Measure.smul_apply, smul_eq_mul] at hK'
    have hc1 : c = 1 := (ENNReal.mul_left_inj hKpos.ne' hKfin).1 (hK'.trans (one_mul _).symm)
    rw [hceq, hc1, one_smul]
  have hinv' : h⁻¹ ∈ Hinf X u := (Hinf X u).inv_mem hh
  have e : (fun s => h * s * h⁻¹) '' Ω = (fun s => h⁻¹ * s * h⁻¹⁻¹) ⁻¹' Ω :=
    congrFun (Set.image_eq_preimage_of_inverse (f := fun s => h * s * h⁻¹) (g := fun s => h⁻¹ * s * h⁻¹⁻¹)
      (fun s => by show h⁻¹ * (h * s * h⁻¹) * h⁻¹⁻¹ = s; group)
      (fun s => by show h * (h⁻¹ * s * h⁻¹⁻¹) * h⁻¹ = s; group)) Ω
  rw [e, ← Measure.map_apply (hcont _).measurable hΩ, key _ hinv']

end Formalism.L2.SG.Pf.IdMeet
