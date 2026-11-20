import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EmbBar
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

namespace GlobalTheory.CompanionTheory.IntegerCount

/- English proof (translation)
Introduce `E _ _`. Set `ι` to `Module.Free.ChooseBasisIndex ℤ (𝓞 E)`. Set `b : Module.Basis ι ℤ (𝓞 E)` to `RingOfIntegers.basis E`. Set `B` to `canonicalEmbedding.latticeBasis E`. Set `L : ι → (((E →+* ℂ) → ℂ) →L[ℂ] ℂ)` to `fun i => LinearMap.toContinuousLinearMap (B.coord i)`.

Set `C₀ : ℝ` to `∑ i, ‖L i‖`. Establish `hC₀ : 0 ≤ C₀` using `Finset.sum_nonneg fun _ _ => norm_nonneg _`. Establish `hcoord : ∀ (β : 𝓞 E) (i : ι), L i (canonicalEmbedding E (β : E)) = ((b.repr β i : ℤ) : ℂ)`. Introduce `β i`. Establish `hx : canonicalEmbedding E (β : E) = ∑ j, ((b.repr β j : ℤ) : ℂ) • B j`.

Establish `h0 : (β : E) = ∑ j, ((b.repr β j : ℤ) : E) * ((b j : 𝓞 E) : E)` using `by conv_lhs => rw [← b.sum_repr β]`. Simplify using `[map_sum, zsmul_eq_mul]`. Rewrite using `[h0, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use extensionality with `τ`.

Simplify using `[B, b, canonicalEmbedding.latticeBasis_apply, integralBasis_apply]`. Express the relevant statement in the definitionally equal form `B.coord i _ = _`. Rewrite using `[hx, map_sum]`. Simplify using `[Module.Basis.coord_apply, Finsupp.single_apply]`. Establish `hbound : ∀ (R : ℝ), 1 ≤ R → ∀ β : 𝓞 E, (∀ τ : E →+* ℂ, ‖τ (β : E)‖ ≤ R) → ∀ i, |((b.repr β i : ℤ) : ℝ)| ≤ C₀ * R`.

Introduce `R hR β hβ i`. Establish `hx : ‖canonicalEmbedding E (β : E)‖ ≤ R` using `(pi_norm_le_iff_of_nonneg (by linarith)).2 fun τ => by simpa using hβ τ`. Establish `h1 : ‖L i (canonicalEmbedding E (β : E))‖ ≤ ‖L i‖ * R` using `((L i).le_opNorm _).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))`. Rewrite `h1` using `[hcoord, Complex.norm_intCast]`. Use `h1.trans (mul_le_mul_of_nonneg_right ?_ (by linarith))` and prove the remaining obligations.

Conclude with `Finset.single_le_sum (f := fun i => ‖L i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)`. Establish `hcard : Fintype.card ι = Module.finrank ℚ E`. Rewrite using `[← RingOfIntegers.rank E]`. Conclude with `(Module.finrank_eq_card_chooseBasisIndex ℤ (𝓞 E)).symm`. Use `⟨(2 * C₀ + 1) ^ Module.finrank ℚ E, by positivity, fun R hR => ?_⟩` and prove the remaining obligations.

Use `set S : Set (𝓞 E) := {β : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (β : E)‖ ≤ R} with hS`. Set `N : ℤ` to `⌊C₀ * R⌋`. Establish `hN0 : 0 ≤ N` using `Int.floor_nonneg.2 (by nlinarith)`. Set `box : Finset (ι → ℤ)` to `Fintype.piFinset fun _ => Finset.Icc (-N) N`. Set `f : 𝓞 E → (ι → ℤ)` to `fun β i => b.repr β i`.

Establish `hf : Function.Injective f`. Introduce `x y hxy`. Apply `b.repr.injective` to reduce the goal to its premises. Use extensionality with `i`. Conclude with `congrFun hxy i`.

Establish `hmaps : Set.MapsTo f S (box : Set (ι → ℤ))`. Introduce `β hβ`. Simplify using `only [box, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]`. Introduce `i`. Establish `h` using `abs_le.1 (hbound R hR β hβ i)`.

Prove the components needed by the constructor for the conclusion. Establish `h2 : -(b.repr β i) ≤ N` using `Int.le_floor.2 (by push_cast; linarith [h.1])`. Express the relevant statement in the definitionally equal form `-N ≤ b.repr β i`. Use linear arithmetic over natural numbers and integers. Conclude with `Int.le_floor.2 h.2`.

Establish `hfin : S.Finite` using `Set.Finite.of_injOn hmaps hf.injOn box.finite_toSet`. Use `⟨hfin, ?_⟩` and prove the remaining obligations. Establish `hle : S.ncard ≤ box.card`. Establish `h` using `Set.ncard_le_ncard_of_injOn f hmaps hf.injOn box.finite_toSet`. Rewrite `h` using `[Set.ncard_coe_finset]`. Then use the resulting hypothesis.

Establish `hboxcard : (box.card : ℝ) = (2 * (N : ℝ) + 1) ^ Module.finrank ℚ E`. Establish `h1 : ((Finset.Icc (-N) N).card : ℤ) = 2 * N + 1`. Rewrite using `[Int.card_Icc]`. Use linear arithmetic over natural numbers and integers. Establish `h2 : ((Finset.Icc (-N) N).card : ℝ) = 2 * (N : ℝ) + 1`.

Conclude with `h1` after adjusting the coercions. Simplify using `only [box, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, hcard]`. Use `push_cast`. Rewrite using `[h2]`. Establish `hNle : (N : ℝ) ≤ C₀ * R` using `Int.floor_le _`.

Combine the equalities or inequalities in the displayed calculation. Establish `hN0' : (0 : ℝ) ≤ N` using `by exact_mod_cast hN0`. Conclude with `pow_le_pow_left₀ (by positivity) (by nlinarith) _`. Use `_ = (2 * C₀ + 1) ^ Module.finrank ℚ E * R ^ Module.finrank ℚ E := mul_pow _ _ _`.
-/
theorem card_bounded_conjugates_le :
    ∀ (E : Type) [Field E] [NumberField E], ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
    {β : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (β : E)‖ ≤ R}.Finite ∧
    (Set.ncard {β : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (β : E)‖ ≤ R} : ℝ) ≤ C * R ^ Module.finrank ℚ E := by
  intro E _ _
  classical
  let ι := Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  let b : Module.Basis ι ℤ (𝓞 E) := RingOfIntegers.basis E
  let B := canonicalEmbedding.latticeBasis E

  let L : ι → (((E →+* ℂ) → ℂ) →L[ℂ] ℂ) := fun i => LinearMap.toContinuousLinearMap (B.coord i)
  let C₀ : ℝ := ∑ i, ‖L i‖
  have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcoord : ∀ (β : 𝓞 E) (i : ι), L i (canonicalEmbedding E (β : E)) = ((b.repr β i : ℤ) : ℂ) := by
    intro β i
    have hx : canonicalEmbedding E (β : E) = ∑ j, ((b.repr β j : ℤ) : ℂ) • B j := by
      have h0 : (β : E) = ∑ j, ((b.repr β j : ℤ) : E) * ((b j : 𝓞 E) : E) := by
        conv_lhs => rw [← b.sum_repr β]
        simp [map_sum, zsmul_eq_mul]
      rw [h0, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ext τ
      simp [B, b, canonicalEmbedding.latticeBasis_apply, integralBasis_apply]
    change B.coord i _ = _
    rw [hx, map_sum]
    simp [Module.Basis.coord_apply, Finsupp.single_apply]
  have hbound : ∀ (R : ℝ), 1 ≤ R → ∀ β : 𝓞 E, (∀ τ : E →+* ℂ, ‖τ (β : E)‖ ≤ R) →
      ∀ i, |((b.repr β i : ℤ) : ℝ)| ≤ C₀ * R := by
    intro R hR β hβ i
    have hx : ‖canonicalEmbedding E (β : E)‖ ≤ R :=
      (pi_norm_le_iff_of_nonneg (by linarith)).2 fun τ => by simpa using hβ τ
    have h1 : ‖L i (canonicalEmbedding E (β : E))‖ ≤ ‖L i‖ * R :=
      ((L i).le_opNorm _).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
    rw [hcoord, Complex.norm_intCast] at h1
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (by linarith))
    exact Finset.single_le_sum (f := fun i => ‖L i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  have hcard : Fintype.card ι = Module.finrank ℚ E := by
    rw [← RingOfIntegers.rank E]
    exact (Module.finrank_eq_card_chooseBasisIndex ℤ (𝓞 E)).symm
  refine ⟨(2 * C₀ + 1) ^ Module.finrank ℚ E, by positivity, fun R hR => ?_⟩
  set S : Set (𝓞 E) := {β : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (β : E)‖ ≤ R} with hS
  let N : ℤ := ⌊C₀ * R⌋
  have hN0 : 0 ≤ N := Int.floor_nonneg.2 (by nlinarith)
  let box : Finset (ι → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-N) N
  let f : 𝓞 E → (ι → ℤ) := fun β i => b.repr β i
  have hf : Function.Injective f := by
    intro x y hxy
    apply b.repr.injective
    ext i
    exact congrFun hxy i
  have hmaps : Set.MapsTo f S (box : Set (ι → ℤ)) := by
    intro β hβ
    simp only [box, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    have h := abs_le.1 (hbound R hR β hβ i)
    constructor
    · have h2 : -(b.repr β i) ≤ N := Int.le_floor.2 (by push_cast; linarith [h.1])
      change -N ≤ b.repr β i
      omega
    · exact Int.le_floor.2 h.2
  have hfin : S.Finite := Set.Finite.of_injOn hmaps hf.injOn box.finite_toSet
  refine ⟨hfin, ?_⟩
  have hle : S.ncard ≤ box.card := by
    have h := Set.ncard_le_ncard_of_injOn f hmaps hf.injOn box.finite_toSet
    rwa [Set.ncard_coe_finset] at h
  have hboxcard : (box.card : ℝ) = (2 * (N : ℝ) + 1) ^ Module.finrank ℚ E := by
    have h1 : ((Finset.Icc (-N) N).card : ℤ) = 2 * N + 1 := by
      rw [Int.card_Icc]
      omega
    have h2 : ((Finset.Icc (-N) N).card : ℝ) = 2 * (N : ℝ) + 1 := by
      exact_mod_cast h1
    simp only [box, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, hcard]
    push_cast
    rw [h2]
  have hNle : (N : ℝ) ≤ C₀ * R := Int.floor_le _
  calc (S.ncard : ℝ) ≤ box.card := by exact_mod_cast hle
    _ = (2 * (N : ℝ) + 1) ^ Module.finrank ℚ E := hboxcard
    _ ≤ ((2 * C₀ + 1) * R) ^ Module.finrank ℚ E := by
        have hN0' : (0 : ℝ) ≤ N := by exact_mod_cast hN0
        exact pow_le_pow_left₀ (by positivity) (by nlinarith) _
    _ = (2 * C₀ + 1) ^ Module.finrank ℚ E * R ^ Module.finrank ℚ E := mul_pow _ _ _

end GlobalTheory.CompanionTheory.IntegerCount
