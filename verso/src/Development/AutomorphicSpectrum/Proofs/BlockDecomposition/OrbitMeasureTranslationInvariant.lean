import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure

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
Introduce `D n t B W d hn I μ hμ x₀ y`. Establish `hring` using `isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)`. Take `⟨i1, i2, i3, i4, i5⟩` from `top_mx (D := D) W.rank t`. Take `⟨-, j2, j3, j4, j5⟩` from `top_mx (D := D) t n`. Take `⟨k1, -, -, -, -⟩` from `top_mx (D := D) B.rank t`.

Take `⟨-, g2, g3, -, -, -⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W`. Establish `: BorelSpace (GA D W)` using `⟨rfl⟩`. Take `⟨hc, 𝓕, hf⟩` from `I.cov₁`. Use `hf.1` as an intermediate fact. Use `I.haar` as an intermediate fact.

Use `I.probK` as an intermediate fact. Establish `hQ` using `sigmaFinite_parameter_product_measure I μ hμ`. Take `⟨p1, p2⟩` from `top_pair (D := D) B.rank W.rank t`. Establish `o1 : OpensMeasurableSpace (Mx D B.rank W.rank × Mx D B.rank t)` using `p1.opensMeasurable`. Establish `hS : Measurable fun z : Mx D B.rank W.rank × Mx D B.rank t => (z.1, z.2 + mm z.1 y)` using `(continuous_fst.prodMk (continuous_snd.add (continuous_fst.matrix_mul continuous_const))).measurable`.

Establish `hτ : MeasurePreserving (fun p : I.l.K × Par D n t W => (p.1, p.2.1, p.2.2.1, p.2.2.2 + y)) (I.νK.prod (Q0 I μ)) (I.νK.prod (Q0 I μ))`. Unfold `Q0`. Conclude with `(MeasurePreserving.id _).prod ((MeasurePreserving.id _).prod ((MeasurePreserving.id _).prod (measurePreserving_add_right μ y)))`. Establish `hπ` using `measurable_pi (d := d) hn I x₀`. Establish `hcomp : (fun z : Mx D B.rank W.rank × Mx D B.rank t => (z.1, z.2 + mm z.1 y)) ∘ (fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)) = (fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)) ∘ (fun p : I.l.K × Par D n t W => (p.1, p.2.1, p.2 …`.

Use function extensionality and compare the values at `p`. Use `Prod.ext rfl ?_` and prove the remaining obligations. Establish `key : ∀ {a b c : ℕ} (g : Mx D a a) (ξ : Mx D a b) (u : Mx D a c) (y' y : Mx D b c), mm g (mm ξ y' + u) + mm (mm g ξ) y = mm g (mm ξ (y' + y) + u)`. Introduce `a b c g ξ u y' y`. Simplify using `only [mm, Matrix.mul_add, Matrix.mul_assoc]`.

Normalize the expressions using the abelian group laws. Conclude with `key _ _ _ _ _`. Unfold `nuT`. Rewrite using `[Measure.map_map hS hπ, hcomp, ← Measure.map_map hπ hτ.measurable, hτ.map_eq]`.
-/
theorem nuT_shear_invariant : ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n)
    (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ x₀ (y : Mx D W.rank t),
    (nuT hn I μ x₀).map (fun z => (z.1, z.2 + mm z.1 y)) = nuT hn I μ x₀ := by
  intro D n t B W d hn I μ hμ x₀ y
  have hring := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨i1, i2, i3, i4, i5⟩ := top_mx (D := D) W.rank t
  obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) t n
  obtain ⟨k1, -, -, -, -⟩ := top_mx (D := D) B.rank t
  obtain ⟨-, g2, g3, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have : BorelSpace (GA D W) := ⟨rfl⟩
  obtain ⟨hc, 𝓕, hf⟩ := I.cov₁
  have := hf.1
  have := I.haar
  have := I.probK
  have hQ := sigmaFinite_parameter_product_measure I μ hμ
  obtain ⟨p1, p2⟩ := top_pair (D := D) B.rank W.rank t
  have o1 : OpensMeasurableSpace (Mx D B.rank W.rank × Mx D B.rank t) := p1.opensMeasurable
  have hS : Measurable fun z : Mx D B.rank W.rank × Mx D B.rank t => (z.1, z.2 + mm z.1 y) :=
    (continuous_fst.prodMk (continuous_snd.add (continuous_fst.matrix_mul continuous_const))).measurable
  have hτ : MeasurePreserving (fun p : I.l.K × Par D n t W => (p.1, p.2.1, p.2.2.1, p.2.2.2 + y))
      (I.νK.prod (Q0 I μ)) (I.νK.prod (Q0 I μ)) := by
    unfold Q0
    exact (MeasurePreserving.id _).prod ((MeasurePreserving.id _).prod
      ((MeasurePreserving.id _).prod (measurePreserving_add_right μ y)))
  have hπ := measurable_pi (d := d) hn I x₀
  have hcomp : (fun z : Mx D B.rank W.rank × Mx D B.rank t => (z.1, z.2 + mm z.1 y)) ∘
        (fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)) =
      (fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)) ∘
        (fun p : I.l.K × Par D n t W => (p.1, p.2.1, p.2.2.1, p.2.2.2 + y)) := by
    funext p
    refine Prod.ext rfl ?_
    have key : ∀ {a b c : ℕ} (g : Mx D a a) (ξ : Mx D a b) (u : Mx D a c) (y' y : Mx D b c),
        mm g (mm ξ y' + u) + mm (mm g ξ) y = mm g (mm ξ (y' + y) + u) := by
      intro a b c g ξ u y' y
      simp only [mm, Matrix.mul_add, Matrix.mul_assoc]
      abel
    exact key _ _ _ _ _
  unfold nuT
  rw [Measure.map_map hS hπ, hcomp, ← Measure.map_map hπ hτ.measurable, hτ.map_eq]

end GlobalTheory.CompanionTheory.ColumnSplitting

end
