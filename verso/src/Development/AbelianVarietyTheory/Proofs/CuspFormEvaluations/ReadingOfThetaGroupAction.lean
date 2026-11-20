import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ReadingTwistedPullbackStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

/- English proof (translation)
Take `⟨hcov, -, -⟩` from `hL`. Establish `hmem : ∀ y : X, ∃ i, y ∈ L.U i`. Introduce `y`. Establish `hy : y ∈ (⨆ i, L.U i)` using `by rw [hcov]; trivial`. Conclude with `(TopologicalSpace.Opens.mem_iSup).1 hy`.

Establish `hsub : Subsingleton (Sp ℂ)`. Express the relevant statement in the definitionally equal form `Subsingleton (PrimeSpectrum ℂ)`. Use `infer_instance`. Establish `p0 : Sp ℂ`. Express the relevant statement in the definitionally equal form `PrimeSpectrum ℂ`.

Conclude with `default`. Use `choose j hj using fun k => hmem (φ k (q p0))`. Use `⟨j, fun y _ => ?_⟩` and prove the remaining obligations. Rewrite using `[Subsingleton.elim y p0]`. Use `show q p0 ∈ L.wchart φ j`.

Unfold `LB.wchart`. Conclude with `Set.mem_iInter.2 fun k => hj k`.
-/
theorem exists_wchart_complexPt {X Z : Scheme.{0}} (L : LB X) (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Z ⟶ X)) (q : Sp ℂ ⟶ Z) : ∃ j : K → L.ι, ⊤ ≤ q ⁻¹ᵁ LB.wchart L φ j := by
  obtain ⟨hcov, -, -⟩ := hL
  have hmem : ∀ y : X, ∃ i, y ∈ L.U i := by
    intro y
    have hy : y ∈ (⨆ i, L.U i) := by rw [hcov]; trivial
    exact (TopologicalSpace.Opens.mem_iSup).1 hy
  have hsub : Subsingleton (Sp ℂ) := by
    change Subsingleton (PrimeSpectrum ℂ)
    infer_instance
  have p0 : Sp ℂ := by
    change PrimeSpectrum ℂ
    exact default
  choose j hj using fun k => hmem (φ k (q p0))
  refine ⟨j, fun y _ => ?_⟩
  rw [Subsingleton.elim y p0]
  show q p0 ∈ L.wchart φ j
  unfold LB.wchart
  exact Set.mem_iInter.2 fun k => hj k

/- English proof (translation)
Introduce `S A _ _ L x0 g Φ k U x c s s' θ hc ha hr`. Take `⟨-, hz⟩` from `hc`. Establish `hfst : translT A U.pt ≫ fst (Over.mk x0) A = fst (Over.mk x0) A`. Unfold `translT`. Conclude with `lift_fst _ _`.

Establish `hsnd : translT A U.pt ≫ snd (Over.mk x0) A = translPt A U.pt`. Unfold `translT`. Conclude with `lift_snd _ _`. Establish `htw : IsTwistPull A L.L (translT A U.pt) (translPt A U.pt) hsnd k k U.φ s s'`. Unfold `IsActOf at ha`.

Conclude with `ha`. Establish `hcond : ∀ z, (ptSecT A (Φ.e z)).left ≫ (translPt A U.pt).left = (Φ.e (x + z)).left ∧ ∃ j : Fin 2 → L.L.ι, ⊤ ≤ (ptSecT A (Φ.e z)).left ⁻¹ᵁ LB.wchart L.L ![(snd (Over.mk x0) A).left, (translPt A U.pt).left] j ∧ valAt' (ptSecT A (Φ.e z)).left (LB.wchart L.L ![(snd (Over.mk x0) A).le …`. Introduce `z`. Take `⟨hmaps, hval⟩` from `hz z`. Use `⟨by simpa using hmaps 1, ?_⟩` and prove the remaining obligations.

Take `⟨j, hj⟩` from `exists_wchart_complexPt L.L L.isLB ![(snd (Over.mk x0) A).left, (translPt A U.pt).left] (ptSecT A (Φ.e z)).left`. Use `⟨j, hj, ?_⟩` and prove the remaining obligations. Rewrite using `[hval j hj, Fin.prod_univ_two]`. Simplify using the standard rewrite rules. Establish `key` using `GlobalTheory.T.reading_twisted_pullback S A L x0 g Φ (translT A U.pt) (translPt A U.pt) hsnd k k U.φ s s' θ (fun z => x + z) (fun z => c * fock Φ.Hm k x (fun _ => 1) z) hfst htw hr hcond`.

Establish `hfun : (fun z => c * fock Φ.Hm k x (fun _ => 1) z * θ (x + z)) = fun z => c * fock Φ.Hm k x θ z`. Use function extensionality and compare the values at `z`. Simplify using `only [fock]`. Rewrite using `[add_comm x z]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← hfun]`. Conclude with `key`.
-/
theorem AnFr.rd_of_isActOf : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (k : ℤ) (U : ThetaGrp A L.L k (Over.mk x0)) (x : Fin g → ℂ) (c : ℂ) (s s' : LB.Sec (LPow A L.L k (Over.mk x0))) (θ : (Fin g → ℂ) → ℂ), Φ.ThConst k U x c → IsActOf A L.L k U s s' → Φ.Rd k s θ → Φ.Rd k s' (fun z => c * fock Φ.Hm k x θ z) := by
  intro S A _ _ L x0 g Φ k U x c s s' θ hc ha hr
  obtain ⟨-, hz⟩ := hc
  have hfst : translT A U.pt ≫ fst (Over.mk x0) A = fst (Over.mk x0) A := by
    unfold translT
    exact lift_fst _ _
  have hsnd : translT A U.pt ≫ snd (Over.mk x0) A = translPt A U.pt := by
    unfold translT
    exact lift_snd _ _
  have htw : IsTwistPull A L.L (translT A U.pt) (translPt A U.pt) hsnd k k U.φ s s' := by
    unfold IsActOf at ha
    exact ha
  have hcond : ∀ z, (ptSecT A (Φ.e z)).left ≫ (translPt A U.pt).left = (Φ.e (x + z)).left ∧
      ∃ j : Fin 2 → L.L.ι, ⊤ ≤ (ptSecT A (Φ.e z)).left ⁻¹ᵁ
          LB.wchart L.L ![(snd (Over.mk x0) A).left, (translPt A U.pt).left] j ∧
        valAt' (ptSecT A (Φ.e z)).left
            (LB.wchart L.L ![(snd (Over.mk x0) A).left, (translPt A U.pt).left] j) (U.φ.s j).val =
          c * fock Φ.Hm k x (fun _ => 1) z * (Φ.fr (j 0) z ^ k * Φ.fr (j 1) (x + z) ^ (-k)) := by
    intro z
    obtain ⟨hmaps, hval⟩ := hz z
    refine ⟨by simpa using hmaps 1, ?_⟩
    obtain ⟨j, hj⟩ := exists_wchart_complexPt L.L L.isLB
      ![(snd (Over.mk x0) A).left, (translPt A U.pt).left] (ptSecT A (Φ.e z)).left
    refine ⟨j, hj, ?_⟩
    rw [hval j hj, Fin.prod_univ_two]
    simp
  have key := GlobalTheory.T.reading_twisted_pullback S A L x0 g Φ (translT A U.pt) (translPt A U.pt) hsnd k k U.φ s s' θ
    (fun z => x + z) (fun z => c * fock Φ.Hm k x (fun _ => 1) z) hfst htw hr hcond
  have hfun : (fun z => c * fock Φ.Hm k x (fun _ => 1) z * θ (x + z)) = fun z => c * fock Φ.Hm k x θ z := by
    funext z
    simp only [fock]
    rw [add_comm x z]
    ring
  rw [← hfun]
  exact key

end GlobalTheory.AnVal
