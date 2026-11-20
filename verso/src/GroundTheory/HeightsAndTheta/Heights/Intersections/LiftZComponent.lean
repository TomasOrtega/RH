import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreLast
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiProjPrimeImageZ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

attribute [local instance] MvPolynomial.weightedGradedAlgebra

namespace FibreMultiHomogeneous

variable {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}

/- English proof (translation)
Use extensionality with `m`. Simplify using `only [coeff_weightedHomogeneousComponent, coeff_map]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem component_map {σ R S : Type*} [CommSemiring R] [CommSemiring S] (g : R →+* S) (w : σ → ℕ) (n : ℕ)
    (F : MvPolynomial σ R) :
    weightedHomogeneousComponent w n (map g F) = map g (weightedHomogeneousComponent w n F) := by
  ext m
  simp only [coeff_weightedHomogeneousComponent, coeff_map]
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[← PointVertical.mem_map_red_iff p hp, PointVertical.red, ← component_map]`. Conclude with `weightedHomogeneousComponent_mem_of_mem _ _ (cyc_isHomogeneous_of_isMultiHomogIdeal hW k) ((PointVertical.mem_map_red_iff p hp g).2 hg) n`.
-/
theorem component_mem [Fintype K'] [∀ k, Fintype (ι' k)] {p : ℕ} {W' : Ideal (MRing ι')} (hp : ((p : ℕ) : MRing ι') ∈ W')
    (hW : IsMultiHomogIdeal (W'.map (MvPolynomial.map (Int.castRingHom (ZMod p))))) [DecidableEq K'] (k : K')
    (n : ℕ) {g : MRing ι'} (hg : g ∈ W') : weightedHomogeneousComponent (cycBlockWt k) n g ∈ W' := by
  rw [← PointVertical.mem_map_red_iff p hp, PointVertical.red, ← component_map]
  exact weightedHomogeneousComponent_mem_of_mem _ _ (cyc_isHomogeneous_of_isMultiHomogIdeal hW k)
    ((PointVertical.mem_map_red_iff p hp g).2 hg) n

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on' with`. Consider the case `monomial m c`. Take `⟨a, b, hb, rfl⟩` from `G.gen c`. Use `⟨b, hb, monomial m a, ?_⟩` and prove the remaining obligations. Rewrite using `[map_monomial, C_mul_monomial]`.

Use `congr 1`. Simplify using `only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]`. Clear the denominators using the available nonvanishing facts. Consider the case `add f g hf hg`. Take `⟨b₁, hb₁, F₁, e₁⟩` from `hf`.

Take `⟨b₂, hb₂, F₂, e₂⟩` from `hg`. Use `⟨b₁ * b₂, by rw [map_mul]; exact mul_ne_zero hb₁ hb₂, C b₂ * F₁ + C b₁ * F₂, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_mul, map_mul, map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_C, ← e₁, ← e₂]`. Simplify using `only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_clear [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] {v : (Σ k, ι k) → (Σ k', ι' k')} {W' : Ideal (MRing ι')} (G : GenFibre v W') {τ : Type*}
    (f : MvPolynomial τ G.Φ) : ∃ b : MRing ι, aeval G.x b ≠ 0 ∧
      ∃ F : MvPolynomial τ (MRing ι), C (aeval G.x b) * f = map (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom F := by
  induction f using MvPolynomial.induction_on' with
  | monomial m c =>
    obtain ⟨a, b, hb, rfl⟩ := G.gen c
    refine ⟨b, hb, monomial m a, ?_⟩
    rw [map_monomial, C_mul_monomial]
    congr 1
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    field_simp
  | add f g hf hg =>
    obtain ⟨b₁, hb₁, F₁, e₁⟩ := hf
    obtain ⟨b₂, hb₂, F₂, e₂⟩ := hg
    refine ⟨b₁ * b₂, by rw [map_mul]; exact mul_ne_zero hb₁ hb₂, C b₂ * F₁ + C b₁ * F₂, ?_⟩
    rw [map_add, map_mul, map_mul, map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_C, ← e₁, ← e₂]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    ring

def liftZ (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) :
    MvPolynomial (Σ k : FibreBlock κ, ι' k.1) (MRing ι) →+* MRing ι' :=
  eval₂Hom (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom fun q => X ⟨q.1.1, q.2⟩

/- English proof (translation)
Establish `h : (aeval G.x' : MRing ι' →ₐ[ℤ] G.Φ').toRingHom.comp (liftZ κ v) = (aeval (fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩)).toRingHom.comp (map (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom)`. Use `MvPolynomial.ringHom_ext (fun a => ?_) (fun q => ?_)` and prove the remaining obligations. Establish `e : G.x' ∘ v = algebraMap G.Φ G.Φ' ∘ G.x` using `funext G.compat`. Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, liftZ, coe_eval₂Hom, eval₂_C, MvPolynomial.map_C, aeval_C]`. Rewrite using `[aeval_rename, e, aeval_algebraMap_apply]`.

Simplify using `[liftZ]`. Conclude with `DFunLike.congr_fun h F`.
-/
theorem aeval_liftZ [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {W' : Ideal (MRing ι')} (G : GenFibre v W')
    (F : MvPolynomial (Σ k : FibreBlock κ, ι' k.1) (MRing ι)) :
    aeval G.x' (liftZ κ v F) = aeval (fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩)
      (map (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom F) := by
  have h : (aeval G.x' : MRing ι' →ₐ[ℤ] G.Φ').toRingHom.comp (liftZ κ v) =
      (aeval (fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩)).toRingHom.comp
        (map (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun q => ?_)
    · have e : G.x' ∘ v = algebraMap G.Φ G.Φ' ∘ G.x := funext G.compat
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, liftZ, coe_eval₂Hom, eval₂_C,
        MvPolynomial.map_C, aeval_C]
      rw [aeval_rename, e, aeval_algebraMap_apply]
    · simp [liftZ]
  exact DFunLike.congr_fun h F

/- English proof (translation)
Proceed by induction on `F using MvPolynomial.induction_on' with`. Consider the case `add F G hF hG => simp only [map_add, hF, hG]`. Consider the case `monomial m a`. Establish `hj : ∀ q : Σ k : FibreBlock κ, ι' k.1, cycBlockWt (ι` using `ι') k.1 ⟨q.1.1, q.2⟩ = cycBlockWt (ι := fun k : FibreBlock κ => ι' k.1) k q := by`. Introduce `q`.

Simplify using `only [cycBlockWt, Subtype.ext_iff]`. Establish `h0 : IsWeightedHomogeneous (cycBlockWt (ι` using `ι') k.1) (rename v a) 0 := by`. Introduce `d hd`. Take `⟨u, rfl, -⟩ : ∃ u, u.mapDomain v = d ∧ coeff u a ≠ 0` from `by by_contra! h`. Conclude with `hd (coeff_rename_eq_zero _ _ _ h)`.

Rewrite using `[Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_mul])]`. Use `Finset.sum_eq_zero fun q _ => ?_` and prove the remaining obligations. Establish `: (v q).1 ≠ k.1` using `fun h => k.2 ⟨q.1, by rw [← hv.2.2.1 q, h]⟩`. Simplify using `[cycBlockWt, this]`. Establish `h1 : IsWeightedHomogeneous (cycBlockWt (ι` using `ι') k.1) (m.prod fun q e => (X ⟨q.1.1, q.2⟩ : MRing ι') ^ e) (Finsupp.weight (cycBlockWt k) m) := by`.

Rewrite using `[Finsupp.weight_apply, Finsupp.prod, Finsupp.sum]`. Use `IsWeightedHomogeneous.prod m.support (fun q => (X ⟨q.1.1, q.2⟩ : MRing ι') ^ m q) (fun q => m q • cycBlockWt (ι := ι') k.1 ⟨q.1.1, q.2⟩) (fun q _ => (isWeightedHomogeneous_X ℤ _ _).pow (m q)) using 1` and compare the differences between its conclusion and the goal. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[hj]`. Establish `hw : IsWeightedHomogeneous (cycBlockWt (ι` using `ι') k.1) (liftZ κ v (monomial m a)) (Finsupp.weight (cycBlockWt k) m) := by`.

Use `h0.mul h1` as an intermediate fact. Rewrite `this` using `[zero_add]`. Simplify `this` using `[liftZ, eval₂_monomial]`. Distinguish the cases in `h : Finsupp.weight (cycBlockWt k) m = n`. Substitute `h` using the available equality.

Rewrite using `[hw.weightedHomogeneousComponent_same, (isWeightedHomogeneous_monomial _ _ _ rfl).weightedHomogeneousComponent_same]`. Rewrite using `[hw.weightedHomogeneousComponent_ne _ (Ne.symm h), (isWeightedHomogeneous_monomial _ _ _ rfl).weightedHomogeneousComponent_ne _ (Ne.symm h), map_zero]`.
-/
theorem liftZ_component [Fintype K'] [∀ k, Fintype (ι' k)] [DecidableEq K'] {κ : K → K'} [DecidableEq (FibreBlock κ)] {v : (Σ k, ι k) → (Σ k', ι' k')}
    (hv : IsBlockMap κ v) (k : FibreBlock κ) (n : ℕ) (F : MvPolynomial (Σ k : FibreBlock κ, ι' k.1) (MRing ι)) :
    weightedHomogeneousComponent (cycBlockWt k.1) n (liftZ κ v F) =
      liftZ κ v (weightedHomogeneousComponent (cycBlockWt k) n F) := by
  induction F using MvPolynomial.induction_on' with
  | add F G hF hG => simp only [map_add, hF, hG]
  | monomial m a =>
    have hj : ∀ q : Σ k : FibreBlock κ, ι' k.1,
        cycBlockWt (ι := ι') k.1 ⟨q.1.1, q.2⟩ = cycBlockWt (ι := fun k : FibreBlock κ => ι' k.1) k q := by
      intro q
      simp only [cycBlockWt, Subtype.ext_iff]
    have h0 : IsWeightedHomogeneous (cycBlockWt (ι := ι') k.1) (rename v a) 0 := by
      intro d hd
      obtain ⟨u, rfl, -⟩ : ∃ u, u.mapDomain v = d ∧ coeff u a ≠ 0 := by
        by_contra! h
        exact hd (coeff_rename_eq_zero _ _ _ h)
      rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_mul])]
      refine Finset.sum_eq_zero fun q _ => ?_
      have : (v q).1 ≠ k.1 := fun h => k.2 ⟨q.1, by rw [← hv.2.2.1 q, h]⟩
      simp [cycBlockWt, this]
    have h1 : IsWeightedHomogeneous (cycBlockWt (ι := ι') k.1)
        (m.prod fun q e => (X ⟨q.1.1, q.2⟩ : MRing ι') ^ e) (Finsupp.weight (cycBlockWt k) m) := by
      rw [Finsupp.weight_apply, Finsupp.prod, Finsupp.sum]
      convert IsWeightedHomogeneous.prod m.support (fun q => (X ⟨q.1.1, q.2⟩ : MRing ι') ^ m q)
        (fun q => m q • cycBlockWt (ι := ι') k.1 ⟨q.1.1, q.2⟩)
        (fun q _ => (isWeightedHomogeneous_X ℤ _ _).pow (m q)) using 1
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hj]
    have hw : IsWeightedHomogeneous (cycBlockWt (ι := ι') k.1) (liftZ κ v (monomial m a))
        (Finsupp.weight (cycBlockWt k) m) := by
      have := h0.mul h1
      rw [zero_add] at this
      simpa [liftZ, eval₂_monomial] using this
    by_cases h : Finsupp.weight (cycBlockWt k) m = n
    · subst h
      rw [hw.weightedHomogeneousComponent_same,
        (isWeightedHomogeneous_monomial _ _ _ rfl).weightedHomogeneousComponent_same]
    · rw [hw.weightedHomogeneousComponent_ne _ (Ne.symm h),
        (isWeightedHomogeneous_monomial _ _ _ rfl).weightedHomogeneousComponent_ne _ (Ne.symm h), map_zero]

end FibreMultiHomogeneous

open FibreMultiHomogeneous in

/- English proof (translation)
Introduce `K _ ι _ K' _ ι' _ κ v p _ W' hv hp hW G'`. Use `cyc_isMultiHomogIdeal_of_isHomogeneous fun k n f hf => ?_` and prove the remaining obligations. Rewrite using `[show (DirectSum.decompose (weightedHomogeneousSubmodule G'.Φ (cycBlockWt k)) f n : MvPolynomial _ G'.Φ) = weightedHomogeneousComponent (cycBlockWt k) n f from MvPolynomial.decompose'_apply _ _ f n]`. Take `⟨b, hb, F, e⟩` from `exists_clear G' f`. Rewrite `hf`, the goal using `[fibreIdeal, RingHom.mem_ker]`.

Establish `hF : liftZ κ v F ∈ W'`. Rewrite using `[← G'.genericFibre_ker_target, RingHom.mem_ker, aeval_liftZ, ← e, map_mul, aeval_C]`. Simplify using `[hf]`. Establish `hc` using `component_mem hp hW k.1 n hF`. Rewrite `hc` using `[liftZ_component hv, ← G'.genericFibre_ker_target, RingHom.mem_ker, aeval_liftZ, ← component_map, ← e, weightedHomogeneousComponent_C_mul, map_mul, aeval_C]`.

Conclude with `(mul_eq_zero.1 hc).resolve_left ((map_ne_zero _).2 hb)`.
-/
theorem ArithmeticIntersectionFibreMultiHomogeneous.proof : ArithmeticIntersectionFibreMultiHomogeneous.Statement := by
  intro K _ ι _ K' _ ι' _ κ v p _ W' hv hp hW G'
  classical
  refine cyc_isMultiHomogIdeal_of_isHomogeneous fun k n f hf => ?_
  rw [show (DirectSum.decompose (weightedHomogeneousSubmodule G'.Φ (cycBlockWt k)) f n : MvPolynomial _ G'.Φ) =
    weightedHomogeneousComponent (cycBlockWt k) n f from MvPolynomial.decompose'_apply _ _ f n]
  obtain ⟨b, hb, F, e⟩ := exists_clear G' f
  rw [fibreIdeal, RingHom.mem_ker] at hf ⊢
  have hF : liftZ κ v F ∈ W' := by
    rw [← G'.genericFibre_ker_target, RingHom.mem_ker, aeval_liftZ, ← e, map_mul, aeval_C]
    simp [hf]
  have hc := component_mem hp hW k.1 n hF
  rw [liftZ_component hv, ← G'.genericFibre_ker_target, RingHom.mem_ker, aeval_liftZ, ← component_map, ← e,
    weightedHomogeneousComponent_C_mul, map_mul, aeval_C] at hc
  exact (mul_eq_zero.1 hc).resolve_left ((map_ne_zero _).2 hb)

end GroundTheory.Heights₂.Heights.Inter
