import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitIdelesOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyCompFinMemIntLocAdele

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting

/- English proof (translation)
The claim follows from `GlobalTheory.ThK.ConeEuler.eventually_compFin_mem_intLoc_adele a`.
-/
theorem eventually_cv_mem_intLoc {D : D7} (a : AE D) :
    ∀ᶠ v : Pl D in cofinite, cv D v a ∈ intLoc D.host.F D.host.E v :=
  GlobalTheory.ThK.ConeEuler.eventually_compFin_mem_intLoc_adele a

/- English proof (translation)
The claim follows from `GlobalTheory.ThK.ConeEuler.UnitsOpen.isOpen_integral_everywhere`.
-/
theorem isOpen_intAll (D : D7) : IsOpen {z : AE D | ∀ v : Pl D, cv D v z ∈ intLoc D.host.F D.host.E v} :=
  GlobalTheory.ThK.ConeEuler.UnitsOpen.isOpen_integral_everywhere

/- English proof (translation)
The claim follows from `eventually_all.2 fun i => eventually_all.2 fun j => eventually_cv_mem_intLoc (x i j)`.
-/
theorem exists_intOff {D : D7} {a b : ℕ} (x : Mx D a b) :
    ∀ᶠ v : Pl D in cofinite, ∀ i j, cv D v (x i j) ∈ intLoc D.host.F D.host.E v :=
  eventually_all.2 fun i => eventually_all.2 fun j => eventually_cv_mem_intLoc (x i j)

/- English proof (translation)
Use `isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)` as an intermediate fact. Establish `h : {y : Mx D a b | ∀ i j, ∀ v : Pl D, cv D v (y i j - x i j) ∈ intLoc D.host.F D.host.E v} = ⋂ i, ⋂ j, (fun y : Mx D a b => y i j - x i j) ⁻¹' {z : AE D | ∀ v : Pl D, cv D v z ∈ intLoc D.host.F D.host.E v}`. Use extensionality with `y`. Simplify using `only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]`. Rewrite using `[h]`.

Establish `hT` using `(top_mx (D := D) a b).1`. Use `haveI hS : ContinuousSub (Mx D a b) := @IsTopologicalAddGroup.to_continuousSub _ _ _ hT`. Establish `hc : Continuous fun y : Mx D a b => y - x` using `continuous_id.sub continuous_const`. Conclude with `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (isOpen_intAll D).preimage (hc.matrix_elem i j)`.
-/
theorem isOpen_nearInt {D : D7} {a b : ℕ} (x : Mx D a b) :
    IsOpen {y : Mx D a b | ∀ i j, ∀ v : Pl D, cv D v (y i j - x i j) ∈ intLoc D.host.F D.host.E v} := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have h : {y : Mx D a b | ∀ i j, ∀ v : Pl D, cv D v (y i j - x i j) ∈ intLoc D.host.F D.host.E v} =
      ⋂ i, ⋂ j, (fun y : Mx D a b => y i j - x i j) ⁻¹' {z : AE D | ∀ v : Pl D, cv D v z ∈ intLoc D.host.F D.host.E v} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [h]
  have hT := (top_mx (D := D) a b).1
  haveI hS : ContinuousSub (Mx D a b) := @IsTopologicalAddGroup.to_continuousSub _ _ _ hT
  have hc : Continuous fun y : Mx D a b => y - x := continuous_id.sub continuous_const
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (isOpen_intAll D).preimage (hc.matrix_elem i j)

/- English proof (translation)
Introduce `D n t B W d hn I μ hμ x₀`. Use `isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)` as an intermediate fact. Set `π : I.l.K × Par D n t W → Mx D B.rank W.rank × Mx D B.rank t` to `fun p => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)`. Set `p₀ : I.l.K × Par D n t W` to `(1, (1, (0, 0)))`. Establish `hbad : {v : Pl D | ¬ ((∀ i j, cv D v ((π p₀).1 i j) ∈ intLoc D.host.F D.host.E v) ∧ ∀ i j, cv D v ((π p₀).2 i j) ∈ intLoc D.host.F D.host.E v)}.Finite` using `((exists_intOff (π p₀).1).and (exists_intOff (π p₀).2))`.

Use `⟨hbad.toFinset, fun S hS => ?_⟩` and prove the remaining obligations. Establish `hπ : Continuous π`. Take `⟨-, k2, -, -, k5, -⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B`. Conclude with `(continuous_ac B).comp (((continuous_subtype_val.comp continuous_fst).inv).prodMk ((continuous_zp d hn x₀).comp continuous_snd))`. Set `N : Set (Mx D B.rank W.rank × Mx D B.rank t)` to `{z | (∀ i j, ∀ v : Pl D, cv D v (z.1 i j - (π p₀).1 i j) ∈ intLoc D.host.F D.host.E v) ∧ ∀ i j, ∀ v : Pl D, cv D v (z.2 i j - (π p₀).2 i j) ∈ intLoc D.host.F D.host.E v}`.

Establish `hNo : IsOpen N` using `((isOpen_nearInt (π p₀).1).preimage continuous_fst).inter ((isOpen_nearInt (π p₀).2).preimage continuous_snd)`. Establish `hN0 : π p₀ ∈ N`. Apply the tactic sequence `constructor <;> intro i j v <;> simp only [sub_self, map_zero, zero_mem]`. Establish `hNO : N ⊆ {z | IntOff S z.1 ∧ IntOff S z.2}`. Introduce `z hz`.

Establish `key : ∀ v, v ∉ S → (∀ i j, cv D v ((π p₀).1 i j) ∈ intLoc D.host.F D.host.E v) ∧ ∀ i j, cv D v ((π p₀).2 i j) ∈ intLoc D.host.F D.host.E v` using `fun v hv => by`. Assume the negation of the conclusion as `hc`. Conclude with `hv (hS (hbad.mem_toFinset.2 hc))`. Use `⟨fun v hv i j => ?_, fun v hv i j => ?_⟩` and prove the remaining obligations. Use `add_mem (hz.1 i j v) ((key v hv).1 i j)` as an intermediate fact.

Rewrite `this` using `[← RingHom.map_add, sub_add_cancel]`. Then use the resulting hypothesis. Use `add_mem (hz.2 i j v) ((key v hv).2 i j)` as an intermediate fact. Rewrite `this` using `[← RingHom.map_add, sub_add_cancel]`. Then use the resulting hypothesis. Take `⟨-, i2, i3, i4, i5⟩` from `top_mx (D := D) t n`. Take `⟨-, j2, j3, j4, j5⟩` from `top_mx (D := D) W.rank t`.

Take `⟨-, g2, g3, -, -, -⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W`. Establish `hGB : BorelSpace (GA D W)` using `⟨rfl⟩`. Take `⟨hc, 𝓕, hf⟩` from `I.cov₁`. Use `hf.1` as an intermediate fact. Use `I.haar` as an intermediate fact.

Use `I.haarK` as an intermediate fact. Establish `hs1 : SigmaFinite (I.μ₁.prod μ)` using `inferInstance`. Establish `hs2 : SigmaFinite (Q0 I μ)` using `sigmaFinite_parameter_product_measure I μ hμ`. Establish `p1 : (I.μ₁.prod μ).IsOpenPosMeasure` using `Measure.prod.instIsOpenPosMeasure`. Establish `p2 : (Q0 I μ).IsOpenPosMeasure` using `Measure.prod.instIsOpenPosMeasure`.

Establish `hpos : (I.νK.prod (Q0 I μ)).IsOpenPosMeasure` using `Measure.prod.instIsOpenPosMeasure`. Establish `hopen : IsOpen (π ⁻¹' N)` using `hNo.preimage hπ`. Establish `hne : (I.νK.prod (Q0 I μ)) (π ⁻¹' N) ≠ 0` using `hopen.measure_ne_zero _ ⟨p₀, hN0⟩`. Introduce `h0`. Apply `hne` to reduce the goal to its premises.

Establish `hle : (I.νK.prod (Q0 I μ)) (π ⁻¹' {z | IntOff S z.1 ∧ IntOff S z.2}) ≤ nuT hn I μ x₀ {z | IntOff S z.1 ∧ IntOff S z.2}` using `Measure.le_map_apply (measurable_pi hn I x₀).aemeasurable _`. Conclude with `le_antisymm (((measure_mono (Set.preimage_mono hNO)).trans hle).trans h0.le) bot_le`.
-/
theorem nuT_intOff_ne_zero : ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n)
    (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ x₀, ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S →
      nuT hn I μ x₀ {z | IntOff S z.1 ∧ IntOff S z.2} ≠ 0 := by
  intro D n t B W d hn I μ hμ x₀
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  let π : I.l.K × Par D n t W → Mx D B.rank W.rank × Mx D B.rank t :=
    fun p => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)
  let p₀ : I.l.K × Par D n t W := (1, (1, (0, 0)))
  have hbad : {v : Pl D | ¬ ((∀ i j, cv D v ((π p₀).1 i j) ∈ intLoc D.host.F D.host.E v) ∧
      ∀ i j, cv D v ((π p₀).2 i j) ∈ intLoc D.host.F D.host.E v)}.Finite :=
    ((exists_intOff (π p₀).1).and (exists_intOff (π p₀).2))
  refine ⟨hbad.toFinset, fun S hS => ?_⟩
  have hπ : Continuous π := by
    obtain ⟨-, k2, -, -, k5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
    exact (continuous_ac B).comp (((continuous_subtype_val.comp continuous_fst).inv).prodMk
      ((continuous_zp d hn x₀).comp continuous_snd))
  let N : Set (Mx D B.rank W.rank × Mx D B.rank t) :=
    {z | (∀ i j, ∀ v : Pl D, cv D v (z.1 i j - (π p₀).1 i j) ∈ intLoc D.host.F D.host.E v) ∧
      ∀ i j, ∀ v : Pl D, cv D v (z.2 i j - (π p₀).2 i j) ∈ intLoc D.host.F D.host.E v}
  have hNo : IsOpen N := ((isOpen_nearInt (π p₀).1).preimage continuous_fst).inter
    ((isOpen_nearInt (π p₀).2).preimage continuous_snd)
  have hN0 : π p₀ ∈ N := by
    constructor <;> intro i j v <;> simp only [sub_self, map_zero, zero_mem]
  have hNO : N ⊆ {z | IntOff S z.1 ∧ IntOff S z.2} := by
    intro z hz
    have key : ∀ v, v ∉ S → (∀ i j, cv D v ((π p₀).1 i j) ∈ intLoc D.host.F D.host.E v) ∧
        ∀ i j, cv D v ((π p₀).2 i j) ∈ intLoc D.host.F D.host.E v := fun v hv => by
      by_contra hc
      exact hv (hS (hbad.mem_toFinset.2 hc))
    refine ⟨fun v hv i j => ?_, fun v hv i j => ?_⟩
    · have := add_mem (hz.1 i j v) ((key v hv).1 i j)
      rwa [← RingHom.map_add, sub_add_cancel] at this
    · have := add_mem (hz.2 i j v) ((key v hv).2 i j)
      rwa [← RingHom.map_add, sub_add_cancel] at this
  obtain ⟨-, i2, i3, i4, i5⟩ := top_mx (D := D) t n
  obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) W.rank t
  obtain ⟨-, g2, g3, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have hGB : BorelSpace (GA D W) := ⟨rfl⟩
  obtain ⟨hc, 𝓕, hf⟩ := I.cov₁
  have := hf.1
  have := I.haar
  have := I.haarK
  have hs1 : SigmaFinite (I.μ₁.prod μ) := inferInstance
  have hs2 : SigmaFinite (Q0 I μ) := sigmaFinite_parameter_product_measure I μ hμ
  have p1 : (I.μ₁.prod μ).IsOpenPosMeasure := Measure.prod.instIsOpenPosMeasure
  have p2 : (Q0 I μ).IsOpenPosMeasure := Measure.prod.instIsOpenPosMeasure
  have hpos : (I.νK.prod (Q0 I μ)).IsOpenPosMeasure := Measure.prod.instIsOpenPosMeasure
  have hopen : IsOpen (π ⁻¹' N) := hNo.preimage hπ
  have hne : (I.νK.prod (Q0 I μ)) (π ⁻¹' N) ≠ 0 := hopen.measure_ne_zero _ ⟨p₀, hN0⟩
  intro h0
  apply hne
  have hle : (I.νK.prod (Q0 I μ)) (π ⁻¹' {z | IntOff S z.1 ∧ IntOff S z.2}) ≤ nuT hn I μ x₀ {z | IntOff S z.1 ∧ IntOff S z.2} :=
    Measure.le_map_apply (measurable_pi hn I x₀).aemeasurable _
  exact le_antisymm (((measure_mono (Set.preimage_mono hNO)).trans hle).trans h0.le) bot_le

end GlobalTheory.CompanionTheory.ColumnSplitting

end
