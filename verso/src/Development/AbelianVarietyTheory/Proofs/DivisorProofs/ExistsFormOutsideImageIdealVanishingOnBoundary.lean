import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfRingKrullDimConeIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogeneousFormsQuotientBirationalSystemStatement
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

namespace GlobalTheory.BoundaryForm

/- English proof (translation)
Take `⟨_, ⟨W, hW, rfl⟩, hy, -⟩` from `Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ`. Establish `hne : ((Z : Set Y)ᶜ).Nonempty` using `Set.nonempty_compl.2 fun h => hZ (SetLike.coe_injective h)`. Take `⟨z, hzW, hzZ⟩` from `nonempty_preirreducible_inter W.isOpen Z.isClosed.isOpen_compl ⟨y, hy⟩ hne`. Take `⟨a, ha, hz⟩` from `IsAffineOpen.exists_basicOpen_le hW (V := Z.compl) ⟨z, hzZ⟩ hzW`. Use `⟨W, a, hy, ?_, fun w hw => ha hw⟩` and prove the remaining obligations.

Introduce and unpack `rfl`. Rewrite `hz` using `[Scheme.basicOpen_zero]`. Conclude with `hz`.
-/
theorem exists_local_fun {Y : Scheme.{0}} [IrreducibleSpace Y] (Z : TopologicalSpace.Closeds Y) (hZ : Z ≠ ⊤) (y : Y) :
    ∃ (W : Y.Opens) (a : Γ(Y, W)), y ∈ W ∧ a ≠ 0 ∧ ∀ z ∈ Y.basicOpen a, z ∉ Z := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hy, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hne : ((Z : Set Y)ᶜ).Nonempty := Set.nonempty_compl.2 fun h => hZ (SetLike.coe_injective h)
  obtain ⟨z, hzW, hzZ⟩ := nonempty_preirreducible_inter W.isOpen Z.isClosed.isOpen_compl ⟨y, hy⟩ hne
  obtain ⟨a, ha, hz⟩ := IsAffineOpen.exists_basicOpen_le hW (V := Z.compl) ⟨z, hzZ⟩ hzW
  refine ⟨W, a, hy, ?_, fun w hw => ha hw⟩
  rintro rfl
  rw [Scheme.basicOpen_zero] at hz
  exact hz

/- English proof (translation)
Introduce `F _ _ T hG hB`. Establish `hV` using `hG.alg.variety`. Use `HeightExists.isIntegral hV` as an intermediate fact. Use `isNoetherian_of_isProjOver hV.proj` as an intermediate fact. Establish `hp` using `HeightExists.isPrime_imageIdeal hV`.

Use `choose W a hy ha hz using exists_local_fun T.bd hG.bd_ne`. Use `choose d P Q hP _ _ hPn hval using fun y => GlobalTheory.T.exists_homogeneous_forms_quotient_birational_system F T.toLinSys hV hG.alg.bpf hB (W y) (a y)`. Take `⟨s, hs⟩` from `isCompact_univ.elim_finite_subcover (fun y => (W y : Set T.Y)) (fun y => (W y).isOpen) fun y _ => Set.mem_iUnion.2 ⟨y, hy y⟩`. Use `⟨∑ y ∈ s, d y, ∏ y ∈ s, P y, IsHomogeneous.prod s P d fun y _ => hP y, fun h => ?_, fun K _ _ x hx => ?_⟩` and prove the remaining obligations. Take `⟨y, -, h⟩` from `Ideal.IsPrime.prod_mem_iff.1 h`.

Conclude with `hPn y (ha y) h`. Take `⟨y, hys, hxy⟩` from `Set.mem_iUnion₂.1 (hs (Set.mem_univ (ptOf x.1)))`. Rewrite using `[map_prod]`. Use `Finset.prod_eq_zero hys ?_` and prove the remaining obligations. Establish `h0 : valR x.1 (W y) (a y) = 0`.

Assume the negation of the conclusion as `h`. Conclude with `hz y _ ((valR_ne_zero_iff x.1 hxy _).1 h) hx`. Rewrite using `[← hval y K x hxy, h0, zero_mul]`.
-/
theorem exists_form_vanishing : ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F), T.IsGeometric → T.Birational →
    ∃ (d : ℕ) (g : MvPolynomial (Fin T.N) F), g.IsHomogeneous d ∧ g ∉ T.imageIdeal ∧
      ∀ (K : Type) [Field K] [Algebra F K] (x : T.Pt K), ptOf x.1 ∈ T.bd → aeval (T.coords x.1) g = 0 := by
  intro F _ _ T hG hB
  have hV := hG.alg.variety
  have := HeightExists.isIntegral hV
  have := isNoetherian_of_isProjOver hV.proj
  have hp := HeightExists.isPrime_imageIdeal hV
  choose W a hy ha hz using exists_local_fun T.bd hG.bd_ne
  choose d P Q hP _ _ hPn hval using fun y => GlobalTheory.T.exists_homogeneous_forms_quotient_birational_system F T.toLinSys hV hG.alg.bpf hB (W y) (a y)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun y => (W y : Set T.Y)) (fun y => (W y).isOpen)
    fun y _ => Set.mem_iUnion.2 ⟨y, hy y⟩
  refine ⟨∑ y ∈ s, d y, ∏ y ∈ s, P y, IsHomogeneous.prod s P d fun y _ => hP y, fun h => ?_, fun K _ _ x hx => ?_⟩
  · obtain ⟨y, -, h⟩ := Ideal.IsPrime.prod_mem_iff.1 h
    exact hPn y (ha y) h
  · obtain ⟨y, hys, hxy⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ (ptOf x.1)))
    rw [map_prod]
    refine Finset.prod_eq_zero hys ?_
    have h0 : valR x.1 (W y) (a y) = 0 := by
      by_contra h
      exact hz y _ ((valR_ne_zero_iff x.1 hxy _).1 h) hx
    rw [← hval y K x hxy, h0, zero_mul]

end GlobalTheory.BoundaryForm
