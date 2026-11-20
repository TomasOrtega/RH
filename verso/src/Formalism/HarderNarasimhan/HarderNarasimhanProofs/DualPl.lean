import Formalism.HarderNarasimhan.QuotRealize
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeMu
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PlaceSplit
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Duality
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.MuChar
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SatBasic
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.ExistsSmulMemOfFinrankEq
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.ShiftInvariance
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DegSupermodZ

open Module NumberField

noncomputable section

namespace Formalism.HN.DualPolygon

section Defs

variable {K V ι : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]

def cE : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) →ₗ[ℝ]
    EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) :=
  (WithLp.linearEquiv 2 ℝ (InfinitePlace K × ι × Fin 2 → ℝ)).symm.toLinearMap ∘ₗ
    (LinearMap.pi (fun p : InfinitePlace K × ι × Fin 2 =>
      (if p.2.2 = 0 then (1 : ℝ) else -1) • LinearMap.proj p)) ∘ₗ
    (WithLp.linearEquiv 2 ℝ (InfinitePlace K × ι × Fin 2 → ℝ)).toLinearMap

/- English proof (translation)
Simplify using `only [cE, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]`. Apply the tactic sequence `split_ifs with h <;> simp [h]`.
-/
theorem cE_apply (w : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))
    (p : InfinitePlace K × ι × Fin 2) :
    cE w p = (if p.2.2 = 0 then (1 : ℝ) else -1) * w p := by
  simp only [cE, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  split_ifs with h <;> simp [h]

def tdualLat (A : Submodule (𝓞 K) V) : Submodule (𝓞 K) (Module.Dual K V) where
  carrier := {f | ∀ x ∈ A, ∃ z : ℤ, Algebra.trace ℚ K (f x) = z}
  zero_mem' := fun x _ => ⟨0, by simp⟩
  add_mem' := by
    rintro f g hf hg x hx
    obtain ⟨a, ha⟩ := hf x hx
    obtain ⟨c, hc⟩ := hg x hx
    exact ⟨a + c, by simp [ha, hc]⟩
  smul_mem' := by
    rintro r f hf x hx
    obtain ⟨a, ha⟩ := hf (r • x) (A.smul_mem r hx)
    have e : (r • f) x = f (r • x) := by
      rw [LinearMap.smul_apply, ← algebraMap_smul K r x, map_smul, algebraMap_smul]
    exact ⟨a, e ▸ ha⟩

def annO (N : Submodule (𝓞 K) V) : Submodule (𝓞 K) (Module.Dual K V) where
  carrier := {f | ∀ x ∈ N, f x = 0}
  zero_mem' := fun x _ => by simp
  add_mem' := by
    rintro f g hf hg x hx
    simp [hf x hx, hg x hx]
  smul_mem' := by
    rintro r f hf x hx
    simp [hf x hx]

end Defs

end Formalism.HN.DualPolygon

namespace Formalism.HN.DualPolygon

open Formalism.HN

/- English proof (translation)
Establish `h` using `trace_eq_sum_embeddings (K := ℚ) (L := K) ℂ (x := a)`. Rewrite `h` using `[← Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ => φ a) (fun σ => σ a) (fun _ => by simp [RingHom.equivRatAlgHom_apply])]`. Rewrite `h` using `[← Finset.sum_fiberwise Finset.univ InfinitePlace.mk (fun φ => φ a)]`. Establish `h2` using `congrArg Complex.re h`. Rewrite `h2` using `[Complex.re_sum]`.

Establish `hq : (algebraMap ℚ ℂ (Algebra.trace ℚ K a)).re = ((Algebra.trace ℚ K a : ℚ) : ℝ)`. Simplify using the standard rewrite rules. Rewrite `h2` using `[hq]`. Rewrite using `[h2]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations.

Rewrite using `[Complex.re_sum]`. Establish `hfib : ∀ φ ∈ (Finset.univ.filter fun φ : K →+* ℂ => InfinitePlace.mk φ = w), (φ a).re = (w.embedding a).re`. Introduce `φ hφ`. Establish `hm` using `(Finset.mem_filter.mp hφ).2`. Rewrite `hm` using `[← InfinitePlace.mk_embedding w, InfinitePlace.mk_eq_iff]`.

Break down `hm with rfl | hc` into its components or cases. Both sides reduce to the same expression. Rewrite using `[← hc, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]`. Rewrite using `[Finset.sum_congr rfl hfib, Finset.sum_const, InfinitePlace.card_filter_mk_eq, (IsTotallyComplex.isComplex w).mult_eq_two]`. Simplify using the standard rewrite rules.
-/
theorem ident_trace_eq {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (a : K) :
    ((Algebra.trace ℚ K a : ℚ) : ℝ) = ∑ v : InfinitePlace K, 2 * (v.embedding a).re := by
  classical
  have h := trace_eq_sum_embeddings (K := ℚ) (L := K) ℂ (x := a)
  rw [← Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ => φ a)
      (fun σ => σ a) (fun _ => by simp [RingHom.equivRatAlgHom_apply])] at h
  rw [← Finset.sum_fiberwise Finset.univ InfinitePlace.mk (fun φ => φ a)] at h
  have h2 := congrArg Complex.re h
  rw [Complex.re_sum] at h2
  have hq : (algebraMap ℚ ℂ (Algebra.trace ℚ K a)).re = ((Algebra.trace ℚ K a : ℚ) : ℝ) := by
    simp
  rw [hq] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Complex.re_sum]
  have hfib : ∀ φ ∈ (Finset.univ.filter fun φ : K →+* ℂ => InfinitePlace.mk φ = w),
      (φ a).re = (w.embedding a).re := by
    intro φ hφ
    have hm := (Finset.mem_filter.mp hφ).2
    rw [← InfinitePlace.mk_embedding w, InfinitePlace.mk_eq_iff] at hm
    rcases hm with rfl | hc
    · rfl
    · rw [← hc, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, InfinitePlace.card_filter_mk_eq,
    (IsTotallyComplex.isComplex w).mult_eq_two]
  simp

section Assumptions

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Use extensionality with `p`. Rewrite using `[cE_apply, cE_apply]`. Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem cE_cE (w : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) : cE (cE w) = w := by
  ext p
  rw [cE_apply, cE_apply]
  split_ifs <;> ring

/- English proof (translation)
Rewrite using `[PiLp.inner_apply, PiLp.inner_apply]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Simplify using `only [cE_apply, RCLike.inner_apply, conj_trivial]`. Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem inner_cE (w w' : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) :
    inner ℝ (cE w) (cE w') = inner ℝ w w' := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [cE_apply, RCLike.inner_apply, conj_trivial]
  split_ifs <;> ring

/- English proof (translation)
Establish `hT : IsUnit (X v).transpose.det` using `by rw [Matrix.det_transpose]; exact hX v`. Establish `hv : Formalism.HermitianLatticesTheory.vecAt b.dualBasis v f = fun i => v.embedding (f (b i))`. Use function extensionality and compare the values at `i`. Simplify using `[Formalism.HermitianLatticesTheory.vecAt, Basis.dualBasis_repr]`. Simplify using `only [Formalism.HermitianLatticesTheory.fcoord, dualFrame, hv, Matrix.nonsing_inv_nonsing_inv _ hT]`.
-/
theorem ident_fcoord_dual (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K) (f : Module.Dual K V) :
    Formalism.HermitianLatticesTheory.fcoord b.dualBasis (dualFrame X) v f =
      (X v).transpose.mulVec (fun i => v.embedding (f (b i))) := by
  have hT : IsUnit (X v).transpose.det := by rw [Matrix.det_transpose]; exact hX v
  have hv : Formalism.HermitianLatticesTheory.vecAt b.dualBasis v f = fun i => v.embedding (f (b i)) := by
    funext i; simp [Formalism.HermitianLatticesTheory.vecAt, Basis.dualBasis_repr]
  simp only [Formalism.HermitianLatticesTheory.fcoord, dualFrame, hv, Matrix.nonsing_inv_nonsing_inv _ hT]

/- English proof (translation)
Rewrite using `[ident_fcoord_dual b X hX]`. Express the relevant statement in the definitionally equal form `((X v).transpose.mulVec _) ⬝ᵥ ((X v)⁻¹.mulVec (Formalism.HermitianLatticesTheory.vecAt b v x)) = _`. Rewrite using `[Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hX v), Matrix.one_mulVec]`. Use `conv_rhs => rw [← b.sum_repr x]`. Simplify using `only [map_sum, map_smul, smul_eq_mul, map_mul, dotProduct, Formalism.HermitianLatticesTheory.vecAt]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ident_sum_fcoord (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K) (f : Module.Dual K V) (x : V) :
    ∑ i, Formalism.HermitianLatticesTheory.fcoord b.dualBasis (dualFrame X) v f i * Formalism.HermitianLatticesTheory.fcoord b X v x i =
      v.embedding (f x) := by
  rw [ident_fcoord_dual b X hX]
  change ((X v).transpose.mulVec _) ⬝ᵥ ((X v)⁻¹.mulVec (Formalism.HermitianLatticesTheory.vecAt b v x)) = _
  rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (hX v), Matrix.one_mulVec]
  conv_rhs => rw [← b.sum_repr x]
  simp only [map_sum, map_smul, smul_eq_mul, map_mul, dotProduct, Formalism.HermitianLatticesTheory.vecAt]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/- English proof (translation)
Rewrite using `[ident_trace_eq, PiLp.inner_apply]`. Simplify using `only [Fintype.sum_prod_type, Fin.sum_univ_two, PiLp.smul_apply, cE_apply, PlaceLattice.realize_apply0, PlaceLattice.realize_apply1, RCLike.inner_apply, conj_trivial, smul_eq_mul]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[← ident_sum_fcoord b X hX v f x, Complex.re_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Simplify using `only [Complex.mul_re, if_true, show ¬ ((1 : Fin 2) = 0) from by decide, if_false]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem inner_realize_alt [IsTotallyComplex K] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (x : V) (f : Module.Dual K V) :
    inner ℝ (Formalism.HermitianLatticesTheory.realize b X x) ((2 : ℝ) • cE (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X) f)) =
      ((Algebra.trace ℚ K (f x) : ℚ) : ℝ) := by
  rw [ident_trace_eq, PiLp.inner_apply]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, PiLp.smul_apply, cE_apply,
    PlaceLattice.realize_apply0, PlaceLattice.realize_apply1, RCLike.inner_apply, conj_trivial,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← ident_sum_fcoord b X hX v f x, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Complex.mul_re, if_true, show ¬ ((1 : Fin 2) = 0) from by decide, if_false]
  ring

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem ident_mem_zl {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (ρ : V →+ E)
    (N : Submodule (𝓞 K) V) (w : E) : w ∈ zl ρ N ↔ ∃ x ∈ N, ρ x = w :=
  Iff.rfl

/- English proof (translation)
Take `⟨hlat, hrk, -⟩` from `place_lattice_structure K V ι b X hX N hN`. Establish `: DiscreteTopology (zl (Formalism.HermitianLatticesTheory.realize b X) N)` using `hlat.2`. Set `bz` to `Module.finBasis ℤ (zl (Formalism.HermitianLatticesTheory.realize b X) N)`. Establish `hv` using `Formalism.F.linearIndependent_coe_basis''' _ bz`. Establish `hspZ` using `Formalism.F.span_range_coe_basis' _ bz`.

Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Rewrite using `[← hspZ, Submodule.span_span_of_tower, finrank_span_eq_card hv, Fintype.card_fin, finrank_euclideanSpace]`. Establish `h1 : Module.finrank ℤ (zl (Formalism.HermitianLatticesTheory.realize b X) N) = rk (Formalism.HermitianLatticesTheory.realize b X) N` using `rfl`. Establish `h2 : rkK N = Fintype.card ι`. Unfold `rkK`.

Rewrite using `[hsp, finrank_top, finrank_eq_card_basis b]`. Rewrite using `[h1, hrk, h2, sizeMu_finrank_eq, nPl]`. Simplify using `only [Fintype.card_prod, Fintype.card_fin]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem span_zl_top [IsTotallyComplex K] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (N : Submodule (𝓞 K) V) (hN : N.FG)
    (hsp : Submodule.span K (N : Set V) = ⊤) :
    Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) N :
      Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) = ⊤ := by
  obtain ⟨hlat, hrk, -⟩ := place_lattice_structure K V ι b X hX N hN
  have : DiscreteTopology (zl (Formalism.HermitianLatticesTheory.realize b X) N) := hlat.2
  let bz := Module.finBasis ℤ (zl (Formalism.HermitianLatticesTheory.realize b X) N)
  have hv := Formalism.F.linearIndependent_coe_basis''' _ bz
  have hspZ := Formalism.F.span_range_coe_basis' _ bz
  apply Submodule.eq_top_of_finrank_eq
  rw [← hspZ, Submodule.span_span_of_tower, finrank_span_eq_card hv, Fintype.card_fin,
    finrank_euclideanSpace]
  have h1 : Module.finrank ℤ (zl (Formalism.HermitianLatticesTheory.realize b X) N) = rk (Formalism.HermitianLatticesTheory.realize b X) N := rfl
  have h2 : rkK N = Fintype.card ι := by
    unfold rkK; rw [hsp, finrank_top, finrank_eq_card_basis b]
  rw [h1, hrk, h2, sizeMu_finrank_eq, nPl]
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring

/- English proof (translation)
Introduce `u hu`. Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem u hu => exact h u hu`. Consider the case `zero => simp`. Consider the case `add u w _ _ hu hw => rw [inner_add_left, hu, hw, add_zero]`.

Consider the case `smul c u _ hu => rw [real_inner_smul_left, hu, mul_zero]`.
-/
theorem ident_inner_span_eq_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : Set E) (z : E) (h : ∀ u ∈ S, inner ℝ u z = 0) :
    ∀ u ∈ Submodule.span ℝ S, inner ℝ u z = 0 := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem u hu => exact h u hu
  | zero => simp
  | add u w _ _ hu hw => rw [inner_add_left, hu, hw, add_zero]
  | smul c u _ hu => rw [real_inner_smul_left, hu, mul_zero]

/- English proof (translation)
Introduce `u hu`. Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem u hu => exact h u hu`. Consider the case `zero => simp`. Consider the case `add u w _ _ hu hw => rw [inner_add_left, hu, hw, add_zero]`.

Consider the case `smul c u _ hu`. Rewrite using `[show (c • u : E) = (c : ℝ) • u from (Int.cast_smul_eq_zsmul ℝ c u).symm, real_inner_smul_left, hu, mul_zero]`.
-/
theorem ident_inner_spanZ_eq_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : Set E) (z : E) (h : ∀ u ∈ S, inner ℝ u z = 0) :
    ∀ u ∈ Submodule.span ℤ S, inner ℝ u z = 0 := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem u hu => exact h u hu
  | zero => simp
  | add u w _ _ hu hw => rw [inner_add_left, hu, hw, add_zero]
  | smul c u _ hu =>
    rw [show (c • u : E) = (c : ℝ) • u from (Int.cast_smul_eq_zsmul ℝ c u).symm,
      real_inner_smul_left, hu, mul_zero]

/- English proof (translation)
Use `set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ`. Use `set ρ' := Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X) with hρ'`. Use `set T : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) →ₗ[ℝ] _ := (2 : ℝ) • cE with hTdef`. Establish `hT : ∀ (x : V) (f : Module.Dual K V), inner ℝ (ρ x) (T (ρ' f)) = ((Algebra.trace ℚ K (f x) : ℚ) : ℝ)`. Introduce `x f`.

Rewrite using `[hTdef, LinearMap.smul_apply]`. Conclude with `inner_realize_alt b X hX x f`. Establish `hspanA` using `span_zl_top b X hX A hA hsp`. Use extensionality with `y`. Simplify using `only [Submodule.mem_inf, Submodule.restrictScalars_mem, Submodule.mem_map, LinearMap.restrictScalars_apply]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hy1, hy2⟩`. Rewrite `hy1` using `[duality_mem_dualZ]`. Take `⟨-, hy1⟩` from `hy1`. Take `⟨s, hsA, hspan, hli⟩` from `exists_linearIndependent K (A : Set V)`.

Establish `: FiniteDimensional K V` using `Module.Finite.of_basis b`. Set `_ : Fintype s` to `hli.setFinite.fintype`. Set `e : s → V` to `Subtype.val`. Establish `he : ∀ j : s, (j : V) ∈ A` using `fun j => hsA j.2`. Establish `hmemA : ∀ (k : Free.ChooseBasisIndex ℤ (𝓞 K)) (j : s), integralBasis K k • (j : V) ∈ A`.

Introduce `k j`. Rewrite using `[integralBasis_apply, algebraMap_smul]`. Conclude with `A.smul_mem _ (he j)`. Establish `hex : ∀ (j : s) (k : Free.ChooseBasisIndex ℤ (𝓞 K)), ∃ n : ℤ, (n : ℝ) = inner ℝ (ρ (integralBasis K k • (j : V))) y` using `fun j k => hy1 _ ⟨_, hmemA k j, rfl⟩`. Use `choose t ht using hex`.

Set `ω'` to `(Algebra.traceForm ℚ K).dualBasis (traceForm_nondegenerate ℚ K) (integralBasis K)`. Establish `hω : ∀ k l, Algebra.trace ℚ K (integralBasis K l * ω' k) = if l = k then 1 else 0`. Introduce `k l`. Rewrite using `[mul_comm, ← Algebra.traceForm_apply]`. Conclude with `LinearMap.BilinForm.apply_dualBasis_left _ _ k l`.

Set `c : s → K` to `fun j => ∑ k, ((t j k : ℚ)) • ω' k`. Establish `hc : ∀ j l, Algebra.trace ℚ K (integralBasis K l * c j) = (t j l : ℚ)`. Introduce `j l`. Simplify using `only [c, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, hω, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Establish `hsp' : ⊤ ≤ Submodule.span K (Set.range e)`.

Rewrite using `[show Set.range e = s from Subtype.range_coe, hspan, hsp]`. Set `eB : Basis s K V` to `Basis.mk hli hsp'`. Set `f : Module.Dual K V` to `∑ j, c j • eB.coord j`. Establish `hfe : ∀ j : s, f (j : V) = c j`. Introduce `j`.

Establish `: (j : V) = eB j` using `by simp [eB]`. Rewrite using `[this]`. Simplify using `[f, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]`. Establish `hTy : T (ρ' f) = y` using `by set z := T (ρ' f) - y`. Establish `hgen : ∀ u ∈ Set.range (fun p : Free.ChooseBasisIndex ℤ (𝓞 K) × s => ρ (integralBasis K p.1 • e p.2)), inner ℝ u z = 0`.

Introduce and unpack `u ⟨⟨k, j⟩, rfl⟩`. Simplify using `only [z, inner_sub_right, hT, map_smul, smul_eq_mul, e, hfe, hc, ← ht]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hM : Submodule.span K ((Submodule.span (𝓞 K) (Set.range e) : Submodule (𝓞 K) V) : Set V) = ⊤`.

Rewrite using `[Submodule.span_span_of_tower]`. Conclude with `top_le_iff.mp hsp'`. Establish `hsM` using `span_zl_top b X hX _ (Submodule.fg_span (Set.finite_range e)) hM`. Establish `hzl` using `PlaceLattice.zl_span_eq (K := K) ρ e`. Establish `h1 : ∀ u ∈ (zl ρ (Submodule.span (𝓞 K) (Set.range e)) : Set _), inner ℝ u z = 0`.

Introduce `u hu`. Rewrite `hu` using `[hzl]`. Conclude with `ident_inner_spanZ_eq_zero _ z hgen u hu`. Establish `h2` using `ident_inner_span_eq_zero _ z h1 z (by rw [hsM]; trivial)`. Establish `: z = 0` using `inner_self_eq_zero.mp h2`.

Conclude with `sub_eq_zero.mp this`. Use `⟨ρ' f, ⟨f, Submodule.mem_inf.mpr ⟨?_, ?_⟩, rfl⟩, hTy⟩` and prove the remaining obligations. Introduce `x hx`. Take `⟨n, hn⟩` from `hy1 (ρ x) ⟨x, hx, rfl⟩`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Establish `h3` using `hT x f`. Rewrite `h3` using `[hTy, ← hn]`. Conclude with `h3.symm` after adjusting the coercions. Introduce `x hx`. Establish `h0 : ∀ r : 𝓞 K, Algebra.trace ℚ K ((r : K) * f x) = 0`.

Introduce `r`. Establish `hm : ρ (r • x) ∈ Submodule.span ℝ (zl ρ N : Set _)` using `Submodule.subset_span ⟨r • x, N.smul_mem r hx, rfl⟩`. Establish `h1` using `Submodule.inner_right_of_mem_orthogonal hm hy2`. Rewrite `h1` using `[← hTy, hT]`. Establish `h4 : f (r • x) = (r : K) * f x`.

Rewrite using `[← algebraMap_smul K r x, map_smul, smul_eq_mul]`. Rewrite `h1` using `[h4]`. Conclude with `h1` after adjusting the coercions. Establish `hz : Algebra.traceForm ℚ K (f x) = 0` using `(integralBasis K).ext (fun k => by`. Rewrite using `[LinearMap.zero_apply, Algebra.traceForm_apply, integralBasis_apply, mul_comm]`.

Conclude with `h0 _)`. Conclude with `(traceForm_nondegenerate ℚ K).1 (f x) (fun n => by rw [hz]; rfl)`. Introduce and unpack `⟨w, hw, rfl⟩`. Take `⟨f, hf, rfl⟩` from `(ident_mem_zl _ _ _).1 hw`. Establish `hf'` using `Submodule.mem_inf.mp hf`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[duality_mem_dualZ]`. Use `⟨by rw [hspanA]; trivial, ?_⟩` and prove the remaining obligations. Introduce `z hz`. Take `⟨x, hx, rfl⟩` from `(ident_mem_zl _ _ _).1 hz`.

Take `⟨n, hn⟩` from `hf'.1 x hx`. Conclude with `⟨n, by rw [hT, hn]; simp⟩`. Rewrite using `[Submodule.mem_orthogonal]`. Introduce `u hu`. Use `ident_inner_span_eq_zero _ _ (fun u hu => ?_) u hu` and prove the remaining obligations.

Take `⟨x, hx, rfl⟩` from `(ident_mem_zl _ _ _).1 hu`. Rewrite using `[hT, hf'.2 x hx]`. Simplify using the standard rewrite rules.
-/
theorem dualZ_zl_eq [IsTotallyComplex K] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) (N : Submodule (𝓞 K) V) :
    dualZ (zl (Formalism.HermitianLatticesTheory.realize b X) A) ⊓
        ((Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) N :
          Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))))ᗮ).restrictScalars ℤ =
      (zl (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (tdualLat A ⊓ annO N)).map
        (((2 : ℝ) • (cE : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) →ₗ[ℝ] _)).restrictScalars ℤ) := by
  classical
  set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ
  set ρ' := Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X) with hρ'
  set T : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) →ₗ[ℝ] _ := (2 : ℝ) • cE with hTdef
  have hT : ∀ (x : V) (f : Module.Dual K V), inner ℝ (ρ x) (T (ρ' f)) =
      ((Algebra.trace ℚ K (f x) : ℚ) : ℝ) := by
    intro x f
    rw [hTdef, LinearMap.smul_apply]
    exact inner_realize_alt b X hX x f
  have hspanA := span_zl_top b X hX A hA hsp
  ext y
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, Submodule.mem_map,
    LinearMap.restrictScalars_apply]
  constructor
  · rintro ⟨hy1, hy2⟩
    rw [duality_mem_dualZ] at hy1
    obtain ⟨-, hy1⟩ := hy1
    obtain ⟨s, hsA, hspan, hli⟩ := exists_linearIndependent K (A : Set V)
    have : FiniteDimensional K V := Module.Finite.of_basis b
    let _ : Fintype s := hli.setFinite.fintype
    let e : s → V := Subtype.val
    have he : ∀ j : s, (j : V) ∈ A := fun j => hsA j.2
    have hmemA : ∀ (k : Free.ChooseBasisIndex ℤ (𝓞 K)) (j : s), integralBasis K k • (j : V) ∈ A := by
      intro k j
      rw [integralBasis_apply, algebraMap_smul]
      exact A.smul_mem _ (he j)
    have hex : ∀ (j : s) (k : Free.ChooseBasisIndex ℤ (𝓞 K)),
        ∃ n : ℤ, (n : ℝ) = inner ℝ (ρ (integralBasis K k • (j : V))) y :=
      fun j k => hy1 _ ⟨_, hmemA k j, rfl⟩
    choose t ht using hex
    let ω' := (Algebra.traceForm ℚ K).dualBasis (traceForm_nondegenerate ℚ K) (integralBasis K)
    have hω : ∀ k l, Algebra.trace ℚ K (integralBasis K l * ω' k) = if l = k then 1 else 0 := by
      intro k l
      rw [mul_comm, ← Algebra.traceForm_apply]
      exact LinearMap.BilinForm.apply_dualBasis_left _ _ k l
    let c : s → K := fun j => ∑ k, ((t j k : ℚ)) • ω' k
    have hc : ∀ j l, Algebra.trace ℚ K (integralBasis K l * c j) = (t j l : ℚ) := by
      intro j l
      simp only [c, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, hω, smul_eq_mul, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hsp' : ⊤ ≤ Submodule.span K (Set.range e) := by
      rw [show Set.range e = s from Subtype.range_coe, hspan, hsp]
    let eB : Basis s K V := Basis.mk hli hsp'
    let f : Module.Dual K V := ∑ j, c j • eB.coord j
    have hfe : ∀ j : s, f (j : V) = c j := by
      intro j
      have : (j : V) = eB j := by simp [eB]
      rw [this]
      simp [f, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
    have hTy : T (ρ' f) = y := by
      set z := T (ρ' f) - y
      have hgen : ∀ u ∈ Set.range (fun p : Free.ChooseBasisIndex ℤ (𝓞 K) × s =>
          ρ (integralBasis K p.1 • e p.2)), inner ℝ u z = 0 := by
        rintro u ⟨⟨k, j⟩, rfl⟩
        simp only [z, inner_sub_right, hT, map_smul, smul_eq_mul, e, hfe, hc, ← ht]
        push_cast; ring
      have hM : Submodule.span K ((Submodule.span (𝓞 K) (Set.range e) : Submodule (𝓞 K) V) :
          Set V) = ⊤ := by
        rw [Submodule.span_span_of_tower]; exact top_le_iff.mp hsp'
      have hsM := span_zl_top b X hX _ (Submodule.fg_span (Set.finite_range e)) hM
      have hzl := PlaceLattice.zl_span_eq (K := K) ρ e
      have h1 : ∀ u ∈ (zl ρ (Submodule.span (𝓞 K) (Set.range e)) : Set _), inner ℝ u z = 0 := by
        intro u hu
        rw [hzl] at hu
        exact ident_inner_spanZ_eq_zero _ z hgen u hu
      have h2 := ident_inner_span_eq_zero _ z h1 z (by rw [hsM]; trivial)
      have : z = 0 := inner_self_eq_zero.mp h2
      exact sub_eq_zero.mp this
    refine ⟨ρ' f, ⟨f, Submodule.mem_inf.mpr ⟨?_, ?_⟩, rfl⟩, hTy⟩
    · intro x hx
      obtain ⟨n, hn⟩ := hy1 (ρ x) ⟨x, hx, rfl⟩
      refine ⟨n, ?_⟩
      have h3 := hT x f
      rw [hTy, ← hn] at h3
      exact_mod_cast h3.symm
    · intro x hx
      have h0 : ∀ r : 𝓞 K, Algebra.trace ℚ K ((r : K) * f x) = 0 := by
        intro r
        have hm : ρ (r • x) ∈ Submodule.span ℝ (zl ρ N : Set _) :=
          Submodule.subset_span ⟨r • x, N.smul_mem r hx, rfl⟩
        have h1 := Submodule.inner_right_of_mem_orthogonal hm hy2
        rw [← hTy, hT] at h1
        have h4 : f (r • x) = (r : K) * f x := by
          rw [← algebraMap_smul K r x, map_smul, smul_eq_mul]
        rw [h4] at h1
        exact_mod_cast h1
      have hz : Algebra.traceForm ℚ K (f x) = 0 :=
        (integralBasis K).ext (fun k => by
          rw [LinearMap.zero_apply, Algebra.traceForm_apply, integralBasis_apply, mul_comm]
          exact h0 _)
      exact (traceForm_nondegenerate ℚ K).1 (f x) (fun n => by rw [hz]; rfl)
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨f, hf, rfl⟩ := (ident_mem_zl _ _ _).1 hw
    have hf' := Submodule.mem_inf.mp hf
    refine ⟨?_, ?_⟩
    · rw [duality_mem_dualZ]
      refine ⟨by rw [hspanA]; trivial, ?_⟩
      intro z hz
      obtain ⟨x, hx, rfl⟩ := (ident_mem_zl _ _ _).1 hz
      obtain ⟨n, hn⟩ := hf'.1 x hx
      exact ⟨n, by rw [hT, hn]; simp⟩
    · rw [Submodule.mem_orthogonal]
      intro u hu
      refine ident_inner_span_eq_zero _ _ (fun u hu => ?_) u hu
      obtain ⟨x, hx, rfl⟩ := (ident_mem_zl _ _ _).1 hu
      rw [hT, hf'.2 x hx]
      simp

end Assumptions

end Formalism.HN.DualPolygon

namespace Formalism.HN.DualPolygon

open Formalism.HN

section Zlat

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- English proof (translation)
Use `set W := Submodule.span ℝ (S : Set E) with hW`. Establish `hQW : Submodule.span ℝ (Formalism.F.quot L S : Set E) ≤ Wᗮ`. Rewrite using `[Submodule.span_le]`. Introduce `z hz`. Take `⟨x, -, rfl⟩` from `Submodule.mem_map.1 hz`.

Conclude with `Wᗮ.starProjection_apply_mem x`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `y ⟨hyD, hyO⟩`. Establish `hyO' : y ∈ Wᗮ` using `hyO`. Establish `hyD : y ∈ dualZ L` using `hyD`.

Rewrite `hyD`, the goal using `[duality_mem_dualZ]`. Take `⟨hyL, hint⟩` from `hyD`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hPy : Wᗮ.starProjection y = y` using `Submodule.starProjection_eq_self_iff.2 hyO'`. Establish `hspan : Submodule.span ℝ (Formalism.F.quot L S : Set E) = (Submodule.span ℝ (L : Set E)).map (Wᗮ.starProjection : E →L[ℝ] E).toLinearMap`.

Rewrite using `[← Submodule.span_image]`. Use `congr 1`. Rewrite using `[hspan, ← hPy]`. Conclude with `Submodule.mem_map_of_mem hyL`. Introduce `z hz`.

Take `⟨x, hx, rfl⟩` from `Submodule.mem_map.1 hz`. Take `⟨n, hn⟩` from `hint x hx`. Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[hn]`. Establish `h0 : inner ℝ (W.starProjection x) y = 0` using `Submodule.inner_right_of_mem_orthogonal (W.starProjection_apply_mem x) hyO'`.

Use `show inner ℝ x y = inner ℝ (Wᗮ.starProjection x) y`. Rewrite using `[Submodule.starProjection_orthogonal_val, inner_sub_left, h0, sub_zero]`. Introduce `y hy`. Use `⟨duality_dualZ_quot_le L S hS hy, ?_⟩` and prove the remaining obligations. Use `((duality_mem_dualZ _ y).1 hy).1` as an intermediate fact.

Conclude with `hQW this`.
-/
theorem dualZ_inf_orth (L S : Submodule ℤ E) (hS : S ≤ L) :
    dualZ L ⊓ ((Submodule.span ℝ (S : Set E))ᗮ).restrictScalars ℤ = dualZ (Formalism.F.quot L S) := by
  set W := Submodule.span ℝ (S : Set E) with hW
  have hQW : Submodule.span ℝ (Formalism.F.quot L S : Set E) ≤ Wᗮ := by
    rw [Submodule.span_le]
    intro z hz
    obtain ⟨x, -, rfl⟩ := Submodule.mem_map.1 hz
    exact Wᗮ.starProjection_apply_mem x
  apply le_antisymm
  · rintro y ⟨hyD, hyO⟩
    have hyO' : y ∈ Wᗮ := hyO
    have hyD : y ∈ dualZ L := hyD
    rw [duality_mem_dualZ] at hyD ⊢
    obtain ⟨hyL, hint⟩ := hyD
    refine ⟨?_, ?_⟩
    · have hPy : Wᗮ.starProjection y = y := Submodule.starProjection_eq_self_iff.2 hyO'
      have hspan : Submodule.span ℝ (Formalism.F.quot L S : Set E) =
          (Submodule.span ℝ (L : Set E)).map (Wᗮ.starProjection : E →L[ℝ] E).toLinearMap := by
        rw [← Submodule.span_image]
        congr 1
      rw [hspan, ← hPy]
      exact Submodule.mem_map_of_mem hyL
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hz
      obtain ⟨n, hn⟩ := hint x hx
      refine ⟨n, ?_⟩
      rw [hn]
      have h0 : inner ℝ (W.starProjection x) y = 0 :=
        Submodule.inner_right_of_mem_orthogonal (W.starProjection_apply_mem x) hyO'
      show inner ℝ x y = inner ℝ (Wᗮ.starProjection x) y
      rw [Submodule.starProjection_orthogonal_val, inner_sub_left, h0, sub_zero]
  · intro y hy
    refine ⟨duality_dualZ_quot_le L S hS hy, ?_⟩
    have := ((duality_mem_dualZ _ y).1 hy).1
    exact hQW this

/- English proof (translation)
Establish `hinj : Function.Injective φ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `x hx`. Establish `h1` using `hφ x x`. Rewrite `h1` using `[hx, inner_zero_left]`.

Establish `h2 : inner ℝ x x = (0 : ℝ)`. Establish `hc2 : c ^ 2 ≠ 0` using `pow_ne_zero _ hc.ne'`. Conclude with `(mul_eq_zero.1 h1.symm).resolve_left hc2`. Conclude with `inner_self_eq_zero.1 h2`. Establish `hinjZ : Function.Injective (φ.restrictScalars ℤ)` using `hinj`.

Use `set M' := M.map (φ.restrictScalars ℤ) with hM'`. Set `e : M ≃ₗ[ℤ] M'` to `Submodule.equivMapOfInjective (φ.restrictScalars ℤ) hinjZ M`. Set `φe : E ≃ₗ[ℝ] E` to `LinearEquiv.ofInjectiveEndo φ hinj`. Establish `hdisc : DiscreteTopology M'`. Set `g : M' → M` to `fun y => ⟨φe.symm (y : E), by`.

Take `⟨x, hx, hxy⟩` from `Submodule.mem_map.1 y.2`. Establish `: φe.symm (y : E) = x`. Rewrite using `[← hxy]`. Use `show φe.symm (φe x) = x`. Conclude with `φe.symm_apply_apply x`.

Rewrite using `[this]`. Conclude with `hx⟩`. Use `DiscreteTopology.of_continuous_injective (f := g) ?_ ?_` and prove the remaining obligations. Establish `hc' : Continuous (φe.symm : E → E)` using `LinearMap.continuous_of_finiteDimensional (φe.symm : E →ₗ[ℝ] E)`. Conclude with `Continuous.subtype_mk (hc'.comp continuous_subtype_val) _`.

Introduce `y y' h`. Establish `h' : φe.symm (y : E) = φe.symm (y' : E)` using `congrArg Subtype.val h`. Conclude with `Subtype.ext (φe.symm.injective h')`. Establish `hrk : Formalism.F.rk M' = Formalism.F.rk M`. Unfold `Formalism.F.rk`.

Conclude with `e.finrank_eq.symm`. Use `⟨hdisc, hrk, ?_⟩` and prove the remaining obligations. Set `b` to `Module.finBasis ℤ M`. Set `b' : Basis (Fin (finrank ℤ M)) ℤ M'` to `b.map e`. Rewrite using `[Formalism.F.covolEqGram E M' _ b', Formalism.F.covolEqGram E M _ b]`.

Establish `hb' : ∀ i, (b' i : E) = φ (b i : E)`. Introduce `i`. Rewrite using `[Basis.map_apply]`. Both sides reduce to the same expression. Establish `hG : Matrix.gram ℝ (fun i => (b' i : E)) = (c ^ 2) • Matrix.gram ℝ (fun i => (b i : E))`.

Use extensionality with `i j`. Simplify using `only [Matrix.gram, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, hb']`. Rewrite using `[hφ]`. Rewrite using `[hG, Matrix.det_smul, Fintype.card_fin]`. Establish `hnn : 0 ≤ (c ^ 2) ^ finrank ℤ M` using `by positivity`.

Rewrite using `[Real.sqrt_mul hnn, ← pow_mul, mul_comm 2, pow_mul, Real.sqrt_sq (by positivity)]`. Both sides reduce to the same expression.
-/
theorem covol_map_scaled (φ : E →ₗ[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hφ : ∀ x y, inner ℝ (φ x) (φ y) = c ^ 2 * inner ℝ x y) (M : Submodule ℤ E)
    [DiscreteTopology M] :
    DiscreteTopology (M.map (φ.restrictScalars ℤ)) ∧
      Formalism.F.rk (M.map (φ.restrictScalars ℤ)) = Formalism.F.rk M ∧
      Formalism.F.covol (M.map (φ.restrictScalars ℤ)) = c ^ Formalism.F.rk M * Formalism.F.covol M := by
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 := hφ x x
    rw [hx, inner_zero_left] at h1
    have h2 : inner ℝ x x = (0 : ℝ) := by
      have hc2 : c ^ 2 ≠ 0 := pow_ne_zero _ hc.ne'
      exact (mul_eq_zero.1 h1.symm).resolve_left hc2
    exact inner_self_eq_zero.1 h2
  have hinjZ : Function.Injective (φ.restrictScalars ℤ) := hinj
  set M' := M.map (φ.restrictScalars ℤ) with hM'
  let e : M ≃ₗ[ℤ] M' := Submodule.equivMapOfInjective (φ.restrictScalars ℤ) hinjZ M
  let φe : E ≃ₗ[ℝ] E := LinearEquiv.ofInjectiveEndo φ hinj
  have hdisc : DiscreteTopology M' := by
    let g : M' → M := fun y => ⟨φe.symm (y : E), by
      obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.1 y.2
      have : φe.symm (y : E) = x := by
        rw [← hxy]
        show φe.symm (φe x) = x
        exact φe.symm_apply_apply x
      rw [this]; exact hx⟩
    refine DiscreteTopology.of_continuous_injective (f := g) ?_ ?_
    · have hc' : Continuous (φe.symm : E → E) :=
        LinearMap.continuous_of_finiteDimensional (φe.symm : E →ₗ[ℝ] E)
      exact Continuous.subtype_mk (hc'.comp continuous_subtype_val) _
    · intro y y' h
      have h' : φe.symm (y : E) = φe.symm (y' : E) := congrArg Subtype.val h
      exact Subtype.ext (φe.symm.injective h')
  have hrk : Formalism.F.rk M' = Formalism.F.rk M := by
    unfold Formalism.F.rk
    exact e.finrank_eq.symm
  refine ⟨hdisc, hrk, ?_⟩
  let b := Module.finBasis ℤ M
  let b' : Basis (Fin (finrank ℤ M)) ℤ M' := b.map e
  rw [Formalism.F.covolEqGram E M' _ b', Formalism.F.covolEqGram E M _ b]
  have hb' : ∀ i, (b' i : E) = φ (b i : E) := by
    intro i
    rw [Basis.map_apply]
    rfl
  have hG : Matrix.gram ℝ (fun i => (b' i : E)) = (c ^ 2) • Matrix.gram ℝ (fun i => (b i : E)) := by
    ext i j
    simp only [Matrix.gram, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, hb']
    rw [hφ]
  rw [hG, Matrix.det_smul, Fintype.card_fin]
  have hnn : 0 ≤ (c ^ 2) ^ finrank ℤ M := by positivity
  rw [Real.sqrt_mul hnn, ← pow_mul, mul_comm 2, pow_mul, Real.sqrt_sq (by positivity)]
  rfl

end Zlat

section Diff

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

open nonZeroDivisors

/- English proof (translation)
Establish `h1 : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0` using `one_ne_zero`. Rewrite using `[FractionalIdeal.mem_dual h1]`. Prove the components needed by the constructor for the conclusion. Introduce `h s`. Take `⟨z, hz⟩` from `h (s : K) ((FractionalIdeal.mem_one_iff _).2 ⟨s, rfl⟩)`.

Conclude with `⟨z, by simpa [Algebra.traceForm_apply] using hz.symm⟩`. Introduce `h a ha`. Take `⟨s, rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 ha`. Take `⟨z, hz⟩` from `h s`. Conclude with `⟨z, by simpa [Algebra.traceForm_apply] using hz.symm⟩`.
-/
theorem misc_mem_dual_one (t : K) :
    t ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) ↔
      ∀ s : 𝓞 K, ∃ z : ℤ, Algebra.trace ℚ K (t * (s : K)) = z := by
  have h1 : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := one_ne_zero
  rw [FractionalIdeal.mem_dual h1]
  constructor
  · intro h s
    obtain ⟨z, hz⟩ := h (s : K) ((FractionalIdeal.mem_one_iff _).2 ⟨s, rfl⟩)
    exact ⟨z, by simpa [Algebra.traceForm_apply] using hz.symm⟩
  · intro h a ha
    obtain ⟨s, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨z, hz⟩ := h s
    exact ⟨z, by simpa [Algebra.traceForm_apply] using hz.symm⟩

/- English proof (translation)
Rewrite using `[coeIdeal_differentIdeal ℤ ℚ K (𝓞 K)]`. Conclude with `inv_mul_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero)`.
-/
theorem misc_diff_mul :
    ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) = 1 := by
  rw [coeIdeal_differentIdeal ℤ ℚ K (𝓞 K)]
  exact inv_mul_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero)

/- English proof (translation)
Use `set D1 := FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)`. Use `set 𝔡 := differentIdeal ℤ (𝓞 K)`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `f ⟨hfA, hfN⟩`. Establish `key : ∀ t ∈ ((𝔡 : FractionalIdeal (𝓞 K)⁰ K) * D1 : FractionalIdeal (𝓞 K)⁰ K), t • f ∈ 𝔡 • (tdualLat A ⊓ annO N)`.

Introduce `t ht`. Rewrite `ht` using `[← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul]`. Use `Submodule.mul_induction_on ht ?_ ?_` and prove the remaining obligations. Introduce `r hr η hη`. Take `⟨r₀, hr₀, rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).1 hr`.

Establish `hηf : η • f ∈ tdualLat A ⊓ annO N`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Take `⟨s, hs⟩` from `hfA x hx`. Establish `hη'` using `(misc_mem_dual_one η).1 hη s`.

Take `⟨z, hz⟩` from `hη'`. Use `⟨z, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.smul_apply, smul_eq_mul]`. Rewrite using `[← hs]`. Conclude with `hz`.

Introduce `x hx`. Simplify using `[hfN x hx]`. Establish `: (algebraMap (𝓞 K) K r₀ * η) • f = r₀ • (η • f)`. Rewrite using `[mul_smul, algebraMap_smul]`. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem_smul hr₀ hηf`. Introduce `t₁ t₂ h₁ h₂`. Rewrite using `[add_smul]`. Conclude with `add_mem h₁ h₂`. Establish `h1 : (1 : K) ∈ ((𝔡 : FractionalIdeal (𝓞 K)⁰ K) * D1 : FractionalIdeal (𝓞 K)⁰ K)`.

Rewrite using `[misc_diff_mul]`. Conclude with `(FractionalIdeal.mem_one_iff _).2 ⟨1, by simp⟩`. Simplify using `using key 1 h1`. Rewrite using `[Submodule.smul_le]`. Introduce and unpack `r hr g ⟨hgA, hgN⟩`.

Use `⟨?_, (annO N).smul_mem r hgN⟩` and prove the remaining obligations. Introduce `x hx`. Establish `hgx : g x ∈ D1`. Rewrite using `[misc_mem_dual_one]`. Introduce `s`.

Take `⟨z, hz⟩` from `hgA (s • x) (A.smul_mem s hx)`. Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[← hz, ← algebraMap_smul K s x, map_smul, smul_eq_mul, mul_comm]`. Establish `hr' : (algebraMap (𝓞 K) K r) ∈ ((𝔡 : FractionalIdeal (𝓞 K)⁰ K))` using `(FractionalIdeal.mem_coeIdeal _).2 ⟨r, hr, rfl⟩`. Establish `hm` using `FractionalIdeal.mul_mem_mul hr' hgx`.

Rewrite `hm` using `[misc_diff_mul]`. Take `⟨s, hs⟩` from `(FractionalIdeal.mem_one_iff _).1 hm`. Use `⟨s, ?_⟩` and prove the remaining obligations. Rewrite using `[hs, LinearMap.smul_apply, ← algebraMap_smul K r (g x), smul_eq_mul]`.
-/
theorem dual_inf_ann_eq (A N : Submodule (𝓞 K) V) :
    dualLat A ⊓ annO N = (differentIdeal ℤ (𝓞 K)) • (tdualLat A ⊓ annO N) := by
  set D1 := FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)
  set 𝔡 := differentIdeal ℤ (𝓞 K)
  apply le_antisymm
  · rintro f ⟨hfA, hfN⟩

    have key : ∀ t ∈ ((𝔡 : FractionalIdeal (𝓞 K)⁰ K) * D1 : FractionalIdeal (𝓞 K)⁰ K),
        t • f ∈ 𝔡 • (tdualLat A ⊓ annO N) := by
      intro t ht
      rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul] at ht
      refine Submodule.mul_induction_on ht ?_ ?_
      · intro r hr η hη
        obtain ⟨r₀, hr₀, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hr
        have hηf : η • f ∈ tdualLat A ⊓ annO N := by
          refine ⟨?_, ?_⟩
          · intro x hx
            obtain ⟨s, hs⟩ := hfA x hx
            have hη' := (misc_mem_dual_one η).1 hη s
            obtain ⟨z, hz⟩ := hη'
            refine ⟨z, ?_⟩
            simp only [LinearMap.smul_apply, smul_eq_mul]
            rw [← hs]
            exact hz
          · intro x hx
            simp [hfN x hx]
        have : (algebraMap (𝓞 K) K r₀ * η) • f = r₀ • (η • f) := by
          rw [mul_smul, algebraMap_smul]
        rw [this]
        exact Submodule.smul_mem_smul hr₀ hηf
      · intro t₁ t₂ h₁ h₂
        rw [add_smul]
        exact add_mem h₁ h₂
    have h1 : (1 : K) ∈ ((𝔡 : FractionalIdeal (𝓞 K)⁰ K) * D1 : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [misc_diff_mul]
      exact (FractionalIdeal.mem_one_iff _).2 ⟨1, by simp⟩
    simpa using key 1 h1
  · rw [Submodule.smul_le]
    rintro r hr g ⟨hgA, hgN⟩
    refine ⟨?_, (annO N).smul_mem r hgN⟩
    intro x hx
    have hgx : g x ∈ D1 := by
      rw [misc_mem_dual_one]
      intro s
      obtain ⟨z, hz⟩ := hgA (s • x) (A.smul_mem s hx)
      refine ⟨z, ?_⟩
      rw [← hz, ← algebraMap_smul K s x, map_smul, smul_eq_mul, mul_comm]
    have hr' : (algebraMap (𝓞 K) K r) ∈ ((𝔡 : FractionalIdeal (𝓞 K)⁰ K)) :=
      (FractionalIdeal.mem_coeIdeal _).2 ⟨r, hr, rfl⟩
    have hm := FractionalIdeal.mul_mem_mul hr' hgx
    rw [misc_diff_mul] at hm
    obtain ⟨s, hs⟩ := (FractionalIdeal.mem_one_iff _).1 hm
    refine ⟨s, ?_⟩
    rw [hs, LinearMap.smul_apply, ← algebraMap_smul K r (g x), smul_eq_mul]

end Diff

end Formalism.HN.DualPolygon

namespace Formalism.HN.DualPolygon

open Formalism.HN

section Twist

attribute [local instance] Ideal.Quotient.field

variable {K W : Type} [Field K] [NumberField K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [FiniteDimensional K W]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Conclude with `Submodule.span_mono (Submodule.smul_le_right)`. Rewrite using `[Submodule.span_le]`. Introduce `x hx`. Take `⟨α, hα, hα0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot h`.

Establish `hmem : α • x ∈ 𝔞 • X` using `Submodule.smul_mem_smul hα hx`. Establish `hK : (algebraMap (𝓞 K) K α) ≠ 0`. Introduce `h0`. Conclude with `hα0 (FaithfulSMul.algebraMap_injective (𝓞 K) K (by simpa using h0))`. Establish `hx' : x = (algebraMap (𝓞 K) K α)⁻¹ • (α • x)`.

Rewrite using `[← algebraMap_smul K α x, smul_smul, inv_mul_cancel₀ hK, one_smul]`. Rewrite using `[SetLike.mem_coe, hx']`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hmem)`.
-/
theorem twist_span_smul (X : Submodule (𝓞 K) W) (𝔞 : Ideal (𝓞 K)) (h : 𝔞 ≠ ⊥) :
    Submodule.span K ((𝔞 • X : Submodule (𝓞 K) W) : Set W) = Submodule.span K (X : Set W) := by
  apply le_antisymm
  · exact Submodule.span_mono (Submodule.smul_le_right)
  · rw [Submodule.span_le]
    intro x hx
    obtain ⟨α, hα, hα0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    have hmem : α • x ∈ 𝔞 • X := Submodule.smul_mem_smul hα hx
    have hK : (algebraMap (𝓞 K) K α) ≠ 0 := by
      intro h0
      exact hα0 (FaithfulSMul.algebraMap_injective (𝓞 K) K (by simpa using h0))
    have hx' : x = (algebraMap (𝓞 K) K α)⁻¹ • (α • x) := by
      rw [← algebraMap_smul K α x, smul_smul, inv_mul_cancel₀ hK, one_smul]
    rw [SetLike.mem_coe, hx']
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Nat.card (X ⧸ (𝔭 • X).comap X.subtype) ≤ _`. Set `e : (X ⧸ (𝔭 • X).comap X.subtype) ≃ₗ[𝓞 K] (X ⧸ (𝔭 • (⊤ : Submodule (𝓞 K) X)))` to `Submodule.quotEquivOfEq _ _ (Submodule.map_injective_of_injective X.injective_subtype (by simp [Submodule.smul_le_right]))`. Rewrite using `[Nat.card_congr e.toEquiv]`. Establish `: Module.Finite (𝓞 K) X` using `Module.Finite.iff_fg.mpr hX`. Establish `: Finite (𝓞 K ⧸ 𝔭)` using `(Ideal.absNorm_ne_zero_iff 𝔭).1 (fun h => h0 (Ideal.absNorm_eq_zero_iff.1 h))`.

Establish `: Module.Finite (𝓞 K ⧸ 𝔭) (X ⧸ (𝔭 • (⊤ : Submodule (𝓞 K) X)))` using `Module.Finite.of_restrictScalars_finite (𝓞 K) _ _`. Establish `: Finite (X ⧸ (𝔭 • (⊤ : Submodule (𝓞 K) X)))` using `Module.finite_of_finite (𝓞 K ⧸ 𝔭)`. Establish `hcard : Nat.card (X ⧸ (𝔭 • (⊤ : Submodule (𝓞 K) X))) = Nat.card (𝓞 K ⧸ 𝔭) ^ finrank (𝓞 K ⧸ 𝔭) (X ⧸ (𝔭 • (⊤ : Submodule (𝓞 K) X)))` using `by haveI := Fintype.ofFinite (X ⧸ (𝔭 • (⊤ : Submodule (𝓞 K) X))) haveI := Fintype.ofFinite (𝓞 K ⧸ 𝔭)`. Rewrite using `[Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]`. Conclude with `Module.card_eq_pow_finrank`.

Establish `hN : Nat.card (𝓞 K ⧸ 𝔭) = Ideal.absNorm 𝔭`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Rewrite using `[hcard, hN]`. Apply `Nat.pow_le_pow_right (Nat.pos_of_ne_zero (fun h => h0 (Ideal.absNorm_eq_zero_iff.1 h)))` to reduce the goal to its premises. Set `B` to `Module.finBasis (𝓞 K ⧸ 𝔭) (X ⧸ (𝔭 • (⊤ : Submodule (𝓞 K) X)))`.

Establish `hsurj` using `Submodule.mkQ_surjective (𝔭 • (⊤ : Submodule (𝓞 K) X))`. Use `choose b' hb' using fun i => hsurj (B i)`. Establish `hli : LinearIndependent (𝓞 K ⧸ 𝔭) ((Submodule.mkQ (𝔭 • (⊤ : Submodule (𝓞 K) X))) ∘ b')`. Establish `: (Submodule.mkQ (𝔭 • (⊤ : Submodule (𝓞 K) X))) ∘ b' = B` using `funext hb'`. Rewrite using `[this]`.

Conclude with `B.linearIndependent`. Establish `hRS : RingHom.ker (algebraMap (𝓞 K) (𝓞 K ⧸ 𝔭)) ≠ ⊤`. Rewrite using `[Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]`. Conclude with `h𝔭.ne_top`. Establish `hli2` using `Ideal.FinrankQuotientMap.linearIndependent_of_nontrivial K hRS X.subtype X.injective_subtype (Submodule.mkQ _) hli`.

Set `g : Fin _ → Submodule.span K (X : Set W)` to `fun i => ⟨(b' i : W), Submodule.subset_span (b' i).2⟩`. Establish `hg : LinearIndependent K g`. Apply `LinearIndependent.of_comp (Submodule.span K (X : Set W)).subtype` to reduce the goal to its premises. Conclude with `hli2`. Simplify using `using hg.fintype_card_le_finrank`.
-/
theorem twist_prime_le (X : Submodule (𝓞 K) W) (hX : X.FG) (𝔭 : Ideal (𝓞 K))
    [h𝔭 : 𝔭.IsMaximal] (h0 : 𝔭 ≠ ⊥) :
    (𝔭 • X).toAddSubgroup.relIndex X.toAddSubgroup ≤
      Ideal.absNorm 𝔭 ^ finrank K (Submodule.span K (X : Set W)) := by
  change Nat.card (X ⧸ (𝔭 • X).comap X.subtype) ≤ _
  let e : (X ⧸ (𝔭 • X).comap X.subtype) ≃ₗ[𝓞 K] (X ⧸ (𝔭 • (⊤ : Submodule (𝓞 K) X))) :=
    Submodule.quotEquivOfEq _ _ (Submodule.map_injective_of_injective X.injective_subtype
      (by simp [Submodule.smul_le_right]))
  rw [Nat.card_congr e.toEquiv]
  have : Module.Finite (𝓞 K) X := Module.Finite.iff_fg.mpr hX
  have : Finite (𝓞 K ⧸ 𝔭) := (Ideal.absNorm_ne_zero_iff 𝔭).1
    (fun h => h0 (Ideal.absNorm_eq_zero_iff.1 h))
  have : Module.Finite (𝓞 K ⧸ 𝔭) (X ⧸ (𝔭 • (⊤ : Submodule (𝓞 K) X))) :=
    Module.Finite.of_restrictScalars_finite (𝓞 K) _ _
  have : Finite (X ⧸ (𝔭 • (⊤ : Submodule (𝓞 K) X))) := Module.finite_of_finite (𝓞 K ⧸ 𝔭)
  have hcard : Nat.card (X ⧸ (𝔭 • (⊤ : Submodule (𝓞 K) X))) =
      Nat.card (𝓞 K ⧸ 𝔭) ^ finrank (𝓞 K ⧸ 𝔭) (X ⧸ (𝔭 • (⊤ : Submodule (𝓞 K) X))) := by
    haveI := Fintype.ofFinite (X ⧸ (𝔭 • (⊤ : Submodule (𝓞 K) X)))
    haveI := Fintype.ofFinite (𝓞 K ⧸ 𝔭)
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Module.card_eq_pow_finrank
  have hN : Nat.card (𝓞 K ⧸ 𝔭) = Ideal.absNorm 𝔭 := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hcard, hN]
  apply Nat.pow_le_pow_right (Nat.pos_of_ne_zero (fun h => h0 (Ideal.absNorm_eq_zero_iff.1 h)))
  let B := Module.finBasis (𝓞 K ⧸ 𝔭) (X ⧸ (𝔭 • (⊤ : Submodule (𝓞 K) X)))
  have hsurj := Submodule.mkQ_surjective (𝔭 • (⊤ : Submodule (𝓞 K) X))
  choose b' hb' using fun i => hsurj (B i)
  have hli : LinearIndependent (𝓞 K ⧸ 𝔭)
      ((Submodule.mkQ (𝔭 • (⊤ : Submodule (𝓞 K) X))) ∘ b') := by
    have : (Submodule.mkQ (𝔭 • (⊤ : Submodule (𝓞 K) X))) ∘ b' = B := funext hb'
    rw [this]; exact B.linearIndependent
  have hRS : RingHom.ker (algebraMap (𝓞 K) (𝓞 K ⧸ 𝔭)) ≠ ⊤ := by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
    exact h𝔭.ne_top
  have hli2 := Ideal.FinrankQuotientMap.linearIndependent_of_nontrivial K hRS X.subtype
    X.injective_subtype (Submodule.mkQ _) hli
  let g : Fin _ → Submodule.span K (X : Set W) :=
    fun i => ⟨(b' i : W), Submodule.subset_span (b' i).2⟩
  have hg : LinearIndependent K g := by
    apply LinearIndependent.of_comp (Submodule.span K (X : Set W)).subtype
    exact hli2
  simpa using hg.fintype_card_le_finrank

/- English proof (translation)
Use `revert h𝔟`. Use `UniqueFactorizationMonoid.induction_on_prime 𝔟 ?_ ?_ ?_` and prove the remaining obligations. Introduce `h`. Conclude with `absurd Submodule.zero_eq_bot h`. Introduce `x hx _ X _`.

Rewrite using `[Ideal.isUnit_iff.1 hx, Submodule.top_smul, Ideal.absNorm_top, one_pow, AddSubgroup.relIndex_self]`. Introduce `a p ha hp ih _ X hX`. Establish `hpb : p ≠ ⊥` using `hp.ne_zero`. Establish `hab : a ≠ ⊥` using `ha`. Use `haveI : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hpb`.

Rewrite using `[Submodule.mul_smul, ← AddSubgroup.relIndex_mul_relIndex (p • a • X).toAddSubgroup (a • X).toAddSubgroup X.toAddSubgroup ((Submodule.toAddSubgroup_le _ _).2 Submodule.smul_le_right) ((Submodule.toAddSubgroup_le _ _).2 Submodule.smul_le_right)]`. Establish `h1` using `twist_prime_le (a • X) (Submodule.FG.smul (IsNoetherian.noetherian a) hX) p hpb`. Rewrite `h1` using `[twist_span_smul X a hab]`. Establish `h2` using `ih hab X hX`. Rewrite using `[map_mul, mul_pow]`.

Conclude with `Nat.mul_le_mul h1 h2`.
-/
theorem twist_le (𝔟 : Ideal (𝓞 K)) (h𝔟 : 𝔟 ≠ ⊥) : ∀ (X : Submodule (𝓞 K) W), X.FG →
    (𝔟 • X).toAddSubgroup.relIndex X.toAddSubgroup ≤
      Ideal.absNorm 𝔟 ^ finrank K (Submodule.span K (X : Set W)) := by
  revert h𝔟
  refine UniqueFactorizationMonoid.induction_on_prime 𝔟 ?_ ?_ ?_
  · intro h
    exact absurd Submodule.zero_eq_bot h
  · intro x hx _ X _
    rw [Ideal.isUnit_iff.1 hx, Submodule.top_smul, Ideal.absNorm_top, one_pow,
      AddSubgroup.relIndex_self]
  · intro a p ha hp ih _ X hX
    have hpb : p ≠ ⊥ := hp.ne_zero
    have hab : a ≠ ⊥ := ha
    haveI : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hpb
    rw [Submodule.mul_smul, ← AddSubgroup.relIndex_mul_relIndex (p • a • X).toAddSubgroup
      (a • X).toAddSubgroup X.toAddSubgroup ((Submodule.toAddSubgroup_le _ _).2 Submodule.smul_le_right)
      ((Submodule.toAddSubgroup_le _ _).2 Submodule.smul_le_right)]
    have h1 := twist_prime_le (a • X) (Submodule.FG.smul (IsNoetherian.noetherian a) hX) p hpb
    rw [twist_span_smul X a hab] at h1
    have h2 := ih hab X hX
    rw [map_mul, mul_pow]
    exact Nat.mul_le_mul h1 h2

omit [FiniteDimensional K W] in
include K in
/- English proof (translation)
Assemble the required witnesses or components as `⟨fun n hn a c h => by have h' : (n : K) • a = (n : K) • c := by simpa [Nat.cast_smul_eq_nsmul] using h exact smul_right_injective W (Nat.cast_ne_zero.2 hn) h'⟩`.
-/
theorem twist_torsionFree : IsAddTorsionFree W := ⟨fun n hn a c h => by
  have h' : (n : K) • a = (n : K) • c := by simpa [Nat.cast_smul_eq_nsmul] using h
  exact smul_right_injective W (Nat.cast_ne_zero.2 hn) h'⟩

/- English proof (translation)
Use `twist_torsionFree (K := K) (W := W)` as an intermediate fact. Use `infer_instance`.
-/
example (X : Submodule (𝓞 K) W) : Module.IsTorsionFree ℤ X := by
  have := twist_torsionFree (K := K) (W := W)
  infer_instance
/- English proof (translation)
Establish `: Module.Finite (𝓞 K) X` using `Module.Finite.iff_fg.mpr hX`. Conclude with `Module.Finite.trans (𝓞 K) X`.
-/
example (X : Submodule (𝓞 K) W) (hX : X.FG) : Module.Finite ℤ X := by
  have : Module.Finite (𝓞 K) X := Module.Finite.iff_fg.mpr hX
  exact Module.Finite.trans (𝓞 K) X

end Twist

section TwistInt

open scoped Pointwise

variable {K W : Type} [Field K] [NumberField K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [FiniteDimensional K W]

/- English proof (translation)
Set `b` to `Module.finBasis K W`. Set `Xf : InfinitePlace K → Matrix (Fin (finrank K W)) (Fin (finrank K W)) ℂ` to `fun _ => 1`. Establish `hXf : ∀ v, IsUnit (Xf v).det` using `fun v => by simp [Xf]`. Take `⟨-, hrk, -⟩` from `place_lattice_structure K W (Fin (finrank K W)) b Xf hXf X hX`. Establish `hinj` using `Formalism.HN.PlaceLattice.realize_injective b Xf hXf`.

Set `e : X.toAddSubgroup ≃+ (X.toAddSubgroup.map (Formalism.HermitianLatticesTheory.realize b Xf))` to `AddSubgroup.equivMapOfInjective _ _ hinj`. Establish `h1 : finrank ℤ X = finrank ℤ (zl (Formalism.HermitianLatticesTheory.realize b Xf) X)` using `e.toIntLinearEquiv.finrank_eq`. Rewrite using `[h1]`. Conclude with `hrk`.
-/
theorem twist_finrank_int [StarRing K] (X : Submodule (𝓞 K) W) (hX : X.FG) :
    finrank ℤ X = finrank ℚ K * finrank K (Submodule.span K (X : Set W)) := by
  let b := Module.finBasis K W
  let Xf : InfinitePlace K → Matrix (Fin (finrank K W)) (Fin (finrank K W)) ℂ := fun _ => 1
  have hXf : ∀ v, IsUnit (Xf v).det := fun v => by simp [Xf]
  obtain ⟨-, hrk, -⟩ := place_lattice_structure K W (Fin (finrank K W)) b Xf hXf X hX
  have hinj := Formalism.HN.PlaceLattice.realize_injective b Xf hXf
  let e : X.toAddSubgroup ≃+ (X.toAddSubgroup.map (Formalism.HermitianLatticesTheory.realize b Xf)) :=
    AddSubgroup.equivMapOfInjective _ _ hinj
  have h1 : finrank ℤ X = finrank ℤ (zl (Formalism.HermitianLatticesTheory.realize b Xf) X) :=
    e.toIntLinearEquiv.finrank_eq
  rw [h1]
  exact hrk

/- English proof (translation)
Establish `htf` using `twist_torsionFree (K := K) (W := W)`. Establish `: Module.Finite (𝓞 K) X` using `Module.Finite.iff_fg.mpr hX`. Establish `: Module.Finite ℤ X` using `Module.Finite.trans (𝓞 K) X`. Rewrite using `[Submodule.ideal_span_singleton_smul]`. Use `set H := ((m : 𝓞 K) • X).toAddSubgroup.addSubgroupOf X.toAddSubgroup with hH`.

Establish `hcoe : ∀ x : X, ((m • x : X) : W) = (m : 𝓞 K) • (x : W)`. Introduce `x`. Rewrite using `[Submodule.coe_smul_of_tower, ← Nat.cast_smul_eq_nsmul (𝓞 K)]`. Establish `hmem : ∀ x : X, m • x ∈ H.toIntSubmodule`. Introduce `x`.

Use `show m • x ∈ H`. Rewrite using `[hH, AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup, hcoe]`. Conclude with `Submodule.smul_mem_pointwise_smul _ _ _ x.2`. Set `f : X →+ H.toIntSubmodule` to `{ toFun := fun x => ⟨m • x, hmem x⟩ map_zero' := by ext; simp map_add' := fun x y => by ext; simp [smul_add] }`. Establish `hf : Function.Bijective f`.

Prove the components needed by the constructor for the conclusion. Introduce `x y hxy`. Establish `h1 : ((m • x : X) : W) = ((m • y : X) : W)`. Use `congrArg (fun z : H.toIntSubmodule => ((z : X) : W)) hxy` as an intermediate fact. Simplify `this` using `[f]`.

Rewrite `h1` using `[Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower]`. Conclude with `Subtype.ext (htf.nsmul_right_injective hm h1)`. Introduce and unpack `⟨z, hz⟩`. Establish `hz' : (z : W) ∈ (m : 𝓞 K) • X`. Establish `: z ∈ H` using `hz`.

Rewrite `this` using `[hH, AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup]`. Then use the resulting hypothesis. Take `⟨x, hx, hxz⟩` from `Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.1 hz'`. Use `⟨⟨x, hx⟩, ?_⟩` and prove the remaining obligations. Use `ext`. Simplify using `only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk]`.

Rewrite using `[hcoe]`. Conclude with `hxz`. Set `e` to `AddEquiv.ofBijective f hf`. Establish `key` using `Submodule.natAbs_det_equiv H.toIntSubmodule e`. Establish `hlin : H.toIntSubmodule.subtype ∘ₗ AddMonoidHom.toIntLinearMap (e : X →+ H.toIntSubmodule) = (m : ℤ) • LinearMap.id`.

Use extensionality with `x`. Simplify using `[e, f]`. Rewrite `key` using `[hlin, LinearMap.det_smul, LinearMap.det_id, mul_one]`. Express the relevant statement in the definitionally equal form `H.index = _`. Rewrite `key` using `[Int.natAbs_pow, Int.natAbs_natCast]`.

Conclude with `key.symm`.
-/
theorem twist_int (X : Submodule (𝓞 K) W) (hX : X.FG) (m : ℕ) (hm : m ≠ 0) :
    ((Ideal.span {(m : 𝓞 K)}) • X).toAddSubgroup.relIndex X.toAddSubgroup =
      m ^ finrank ℤ X := by
  have htf := twist_torsionFree (K := K) (W := W)
  have : Module.Finite (𝓞 K) X := Module.Finite.iff_fg.mpr hX
  have : Module.Finite ℤ X := Module.Finite.trans (𝓞 K) X
  rw [Submodule.ideal_span_singleton_smul]
  set H := ((m : 𝓞 K) • X).toAddSubgroup.addSubgroupOf X.toAddSubgroup with hH
  have hcoe : ∀ x : X, ((m • x : X) : W) = (m : 𝓞 K) • (x : W) := by
    intro x
    rw [Submodule.coe_smul_of_tower, ← Nat.cast_smul_eq_nsmul (𝓞 K)]
  have hmem : ∀ x : X, m • x ∈ H.toIntSubmodule := by
    intro x
    show m • x ∈ H
    rw [hH, AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup, hcoe]
    exact Submodule.smul_mem_pointwise_smul _ _ _ x.2
  let f : X →+ H.toIntSubmodule :=
    { toFun := fun x => ⟨m • x, hmem x⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp [smul_add] }
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have h1 : ((m • x : X) : W) = ((m • y : X) : W) := by
        have := congrArg (fun z : H.toIntSubmodule => ((z : X) : W)) hxy
        simpa [f] using this
      rw [Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower] at h1
      exact Subtype.ext (htf.nsmul_right_injective hm h1)
    · rintro ⟨z, hz⟩
      have hz' : (z : W) ∈ (m : 𝓞 K) • X := by
        have : z ∈ H := hz
        rwa [hH, AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup] at this
      obtain ⟨x, hx, hxz⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.1 hz'
      refine ⟨⟨x, hx⟩, ?_⟩
      ext
      simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [hcoe]
      exact hxz
  let e := AddEquiv.ofBijective f hf
  have key := Submodule.natAbs_det_equiv H.toIntSubmodule e
  have hlin : H.toIntSubmodule.subtype ∘ₗ AddMonoidHom.toIntLinearMap (e : X →+ H.toIntSubmodule) =
      (m : ℤ) • LinearMap.id := by
    ext x
    simp [e, f]
  rw [hlin, LinearMap.det_smul, LinearMap.det_id, mul_one] at key
  change H.index = _
  rw [Int.natAbs_pow, Int.natAbs_natCast] at key
  exact key.symm

/- English proof (translation)
Rewrite using `[Ideal.absNorm_span_singleton]`. Establish `: (m : 𝓞 K) = algebraMap ℤ (𝓞 K) (m : ℤ)` using `by simp`. Rewrite using `[this, Algebra.norm_algebraMap, RingOfIntegers.rank, Int.natAbs_pow, Int.natAbs_natCast]`.
-/
theorem twist_absNorm_nat (m : ℕ) :
    Ideal.absNorm (Ideal.span {(m : 𝓞 K)}) = m ^ finrank ℚ K := by
  rw [Ideal.absNorm_span_singleton]
  have : (m : 𝓞 K) = algebraMap ℤ (𝓞 K) (m : ℤ) := by simp
  rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank, Int.natAbs_pow, Int.natAbs_natCast]

/- English proof (translation)
Use `set m := Ideal.absNorm 𝔟 with hmdef`. Establish `hm : m ≠ 0` using `fun h => h𝔟 (Ideal.absNorm_eq_zero_iff.1 h)`. Establish `hmem : (m : 𝓞 K) ∈ 𝔟` using `Ideal.absNorm_mem 𝔟`. Take `⟨𝔠, h𝔠⟩ : 𝔟 ∣ Ideal.span {(m : 𝓞 K)}` from `Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hmem)`. Establish `hspan0 : Ideal.span {(m : 𝓞 K)} ≠ ⊥`.

Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hm` after adjusting the coercions. Establish `h𝔠0 : 𝔠 ≠ ⊥`. Introduce and unpack `rfl`. Rewrite `h𝔠` using `[Ideal.mul_bot]`.

Conclude with `hspan0 h𝔠`. Use `set r := finrank K (Submodule.span K (X : Set W)) with hr`. Establish `hall` using `twist_int X hX m hm`. Rewrite `hall` using `[twist_finrank_int X hX, h𝔠, mul_comm, Submodule.mul_smul, ← AddSubgroup.relIndex_mul_relIndex (𝔠 • 𝔟 • X).toAddSubgroup (𝔟 • X).toAddSubgroup X.toAddSubgroup ((Submodule.toAddSubgroup_le _ _).2 Submodule.smul_le_right) ((Submodule.toAddSubgroup_le _ _).2 Submodule.smul_le_right) …`. Establish `ha` using `twist_le 𝔟 h𝔟 X hX`.

Establish `hb` using `twist_le 𝔠 h𝔠0 (𝔟 • X) (Submodule.FG.smul (IsNoetherian.noetherian 𝔟) hX)`. Rewrite `hb` using `[twist_span_smul X 𝔟 h𝔟]`. Establish `hnorm : Ideal.absNorm 𝔠 * m = m ^ finrank ℚ K`. Rewrite using `[hmdef, ← map_mul, mul_comm, ← h𝔠, twist_absNorm_nat]`. Establish `hB : 0 < Ideal.absNorm 𝔠 ^ r` using `pow_pos (Nat.pos_of_ne_zero (fun h => h𝔠0 (Ideal.absNorm_eq_zero_iff.1 h))) _`.

Establish `htot : Ideal.absNorm 𝔠 ^ r * m ^ r = m ^ (finrank ℚ K * r)`. Rewrite using `[← mul_pow, hnorm, ← pow_mul]`. Assume the negation of the conclusion as `hne`. Establish `hlt` using `lt_of_le_of_ne ha hne`. Establish `h1 : (𝔠 • 𝔟 • X).toAddSubgroup.relIndex (𝔟 • X).toAddSubgroup * (𝔟 • X).toAddSubgroup.relIndex X.toAddSubgroup < Ideal.absNorm 𝔠 ^ r * m ^ r` using `lt_of_le_of_lt (Nat.mul_le_mul_right _ hb) (Nat.mul_lt_mul_of_pos_left hlt hB)`.

Rewrite `h1` using `[hall, htot]`. Conclude with `lt_irrefl _ h1`.
-/
theorem twist_index {K W : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [FiniteDimensional K W] (X : Submodule (𝓞 K) W) (hX : X.FG) (𝔟 : Ideal (𝓞 K))
    (h𝔟 : 𝔟 ≠ ⊥) :
    (𝔟 • X).toAddSubgroup.relIndex X.toAddSubgroup =
      Ideal.absNorm 𝔟 ^ finrank K (Submodule.span K (X : Set W)) := by
  set m := Ideal.absNorm 𝔟 with hmdef
  have hm : m ≠ 0 := fun h => h𝔟 (Ideal.absNorm_eq_zero_iff.1 h)
  have hmem : (m : 𝓞 K) ∈ 𝔟 := Ideal.absNorm_mem 𝔟
  obtain ⟨𝔠, h𝔠⟩ : 𝔟 ∣ Ideal.span {(m : 𝓞 K)} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hmem)
  have hspan0 : Ideal.span {(m : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hm
  have h𝔠0 : 𝔠 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot] at h𝔠
    exact hspan0 h𝔠
  set r := finrank K (Submodule.span K (X : Set W)) with hr
  have hall := twist_int X hX m hm
  rw [twist_finrank_int X hX, h𝔠, mul_comm, Submodule.mul_smul,
    ← AddSubgroup.relIndex_mul_relIndex (𝔠 • 𝔟 • X).toAddSubgroup
      (𝔟 • X).toAddSubgroup X.toAddSubgroup ((Submodule.toAddSubgroup_le _ _).2 Submodule.smul_le_right)
      ((Submodule.toAddSubgroup_le _ _).2 Submodule.smul_le_right)] at hall
  have ha := twist_le 𝔟 h𝔟 X hX
  have hb := twist_le 𝔠 h𝔠0 (𝔟 • X) (Submodule.FG.smul (IsNoetherian.noetherian 𝔟) hX)
  rw [twist_span_smul X 𝔟 h𝔟] at hb
  have hnorm : Ideal.absNorm 𝔠 * m = m ^ finrank ℚ K := by
    rw [hmdef, ← map_mul, mul_comm, ← h𝔠, twist_absNorm_nat]
  have hB : 0 < Ideal.absNorm 𝔠 ^ r :=
    pow_pos (Nat.pos_of_ne_zero (fun h => h𝔠0 (Ideal.absNorm_eq_zero_iff.1 h))) _
  have htot : Ideal.absNorm 𝔠 ^ r * m ^ r = m ^ (finrank ℚ K * r) := by
    rw [← mul_pow, hnorm, ← pow_mul]
  by_contra hne
  have hlt := lt_of_le_of_ne ha hne
  have h1 : (𝔠 • 𝔟 • X).toAddSubgroup.relIndex (𝔟 • X).toAddSubgroup *
      (𝔟 • X).toAddSubgroup.relIndex X.toAddSubgroup < Ideal.absNorm 𝔠 ^ r * m ^ r :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ hb) (Nat.mul_lt_mul_of_pos_left hlt hB)
  rw [hall, htot] at h1
  exact lt_irrefl _ h1

end TwistInt

end Formalism.HN.DualPolygon

namespace Formalism.HN.DualPolygon

open Formalism.HN

section Main

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Introduce `v` and use `by unfold dualFrame exact Matrix.isUnit_nonsing_inv_det _ (by rw [Matrix.det_transpose]; exact hX v)`.
-/
theorem dualFrame_unit (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) :
    ∀ v, IsUnit (dualFrame X v).det := fun v => by
  unfold dualFrame
  exact Matrix.isUnit_nonsing_inv_det _ (by rw [Matrix.det_transpose]; exact hX v)

/- English proof (translation)
Use function extensionality and compare the values at `v`. Unfold `dualFrame`. Rewrite using `[Matrix.transpose_nonsing_inv, Matrix.transpose_transpose, Matrix.nonsing_inv_nonsing_inv _ (hX v)]`.
-/
theorem dualFrame_dualFrame (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) :
    dualFrame (dualFrame X) = X := by
  funext v
  unfold dualFrame
  rw [Matrix.transpose_nonsing_inv, Matrix.transpose_transpose, Matrix.nonsing_inv_nonsing_inv _ (hX v)]

omit [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Take `⟨s, hsA, hspan, hli⟩` from `exists_linearIndependent K (A : Set V)`. Establish `hfin : s.Finite` using `hli.setFinite`. Use `haveI : Fintype s := hfin.fintype`. Set `e0 : Basis s K V` to `Basis.mk hli (by rw [Subtype.range_coe, hspan, hsp])`. Use `⟨Fintype.card s, e0.reindex (Fintype.equivFin s), fun i => ?_⟩` and prove the remaining obligations.

Rewrite using `[Basis.reindex_apply, Basis.mk_apply]`. Conclude with `hsA (Subtype.mem _)`.
-/
theorem exists_basis_in (A : Submodule (𝓞 K) V) [FiniteDimensional K V]
    (hsp : Submodule.span K (A : Set V) = ⊤) :
    ∃ (n : ℕ) (e : Basis (Fin n) K V), ∀ i, e i ∈ A := by
  obtain ⟨s, hsA, hspan, hli⟩ := exists_linearIndependent K (A : Set V)
  have hfin : s.Finite := hli.setFinite
  haveI : Fintype s := hfin.fintype
  let e0 : Basis s K V := Basis.mk hli (by rw [Subtype.range_coe, hspan, hsp])
  refine ⟨Fintype.card s, e0.reindex (Fintype.equivFin s), fun i => ?_⟩
  rw [Basis.reindex_apply, Basis.mk_apply]
  exact hsA (Subtype.mem _)

omit [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Take `⟨y, hy, hint⟩` from `exists_integral_multiples ℤ ℚ (Finset.univ.image fun i => e.repr w i)`. Use `⟨y, hy, ?_⟩` and prove the remaining obligations. Rewrite using `[← e.sum_repr w, Finset.smul_sum]`. Apply `Submodule.sum_mem` to reduce the goal to its premises. Introduce `i _`.

Establish `hi : IsIntegral ℤ (y • e.repr w i)` using `hint _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)`. Set `r : 𝓞 K` to `⟨y • e.repr w i, hi⟩`. Establish `hr : ((y : K)) • (e.repr w i • e i) = r • e i`. Rewrite using `[← algebraMap_smul K r, smul_smul]`. Use `congr 1`.

Use `show (y : K) * e.repr w i = y • e.repr w i`. Rewrite using `[zsmul_eq_mul]`. Rewrite using `[hr]`. Conclude with `Submodule.smul_mem _ _ (he i)`.
-/
theorem exists_int_smul_mem {n : ℕ} (A : Submodule (𝓞 K) V) (e : Basis (Fin n) K V)
    (he : ∀ i, e i ∈ A) (w : V) : ∃ c : ℤ, c ≠ 0 ∧ ((c : K)) • w ∈ A := by
  classical
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image fun i => e.repr w i)
  refine ⟨y, hy, ?_⟩
  rw [← e.sum_repr w, Finset.smul_sum]
  apply Submodule.sum_mem
  intro i _
  have hi : IsIntegral ℤ (y • e.repr w i) :=
    hint _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
  let r : 𝓞 K := ⟨y • e.repr w i, hi⟩
  have hr : ((y : K)) • (e.repr w i • e i) = r • e i := by
    rw [← algebraMap_smul K r, smul_smul]
    congr 1
    show (y : K) * e.repr w i = y • e.repr w i
    rw [zsmul_eq_mul]
  rw [hr]
  exact Submodule.smul_mem _ _ (he i)

omit [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Introduce `f hf`. Establish `h : ∀ i, ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = f (e i)` using `fun i => hf (e i) (he i)`. Use `choose a ha using h`. Establish `hf' : f = ∑ i, a i • e.dualBasis i` using `by conv_lhs => rw [← e.dualBasis.sum_repr f]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Basis.dualBasis_repr, ← ha i, algebraMap_smul]`. Rewrite using `[hf']`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem dualLat_le_span {n : ℕ} (A : Submodule (𝓞 K) V) (e : Basis (Fin n) K V)
    (he : ∀ i, e i ∈ A) : dualLat A ≤ Submodule.span (𝓞 K) (Set.range e.dualBasis) := by
  intro f hf
  have h : ∀ i, ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = f (e i) := fun i => hf (e i) (he i)
  choose a ha using h
  have hf' : f = ∑ i, a i • e.dualBasis i := by
    conv_lhs => rw [← e.dualBasis.sum_repr f]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Basis.dualBasis_repr, ← ha i, algebraMap_smul]
  rw [hf']
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

omit [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Take `⟨n, e, he⟩` from `exists_basis_in A hsp`. Conclude with `Submodule.FG.of_le (Submodule.fg_span (Set.finite_range _)) (dualLat_le_span A e he)`.
-/
theorem dualLat_fg [FiniteDimensional K V] (A : Submodule (𝓞 K) V)
    (hsp : Submodule.span K (A : Set V) = ⊤) : (dualLat A).FG := by
  obtain ⟨n, e, he⟩ := exists_basis_in A hsp
  exact Submodule.FG.of_le (Submodule.fg_span (Set.finite_range _)) (dualLat_le_span A e he)

omit [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Take `⟨n, e, he⟩` from `exists_basis_in A hsp`. Take `⟨y, hy, hAy⟩` from `Formalism.HN.PlaceLattice.exists_denom e A hA (fun x _ => by rw [e.span_eq]; trivial)`. Establish `hyK : (y : K) ≠ 0` using `Int.cast_ne_zero.2 hy`. Establish `hmem : ∀ i, ((y : K)) • e.dualBasis i ∈ dualLat A`. Introduce `i`.

It suffices to establish `H : ∀ x ∈ Submodule.span (𝓞 K) (Set.range fun a => ((y : K)⁻¹) • e a), (((y : K)) • e.dualBasis i) x ∈ Set.range (algebraMap (𝓞 K) K) from fun x hx => H x (hAy hx)`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨a, rfl⟩` from `hz`.

Distinguish the cases in `h : a = i`. Use `⟨1, ?_⟩` and prove the remaining obligations. Simplify using `[LinearMap.smul_apply, map_smul, Basis.dualBasis_apply_self, h, hyK]`. Use `⟨0, ?_⟩` and prove the remaining obligations. Simplify using `[LinearMap.smul_apply, map_smul, Basis.dualBasis_apply_self, h]`.

Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add z w _ _ hz hw`. Take `⟨a, ha⟩` from `hz`. Take `⟨c, hc⟩` from `hw`. Conclude with `⟨a + c, by rw [map_add, map_add, ha, hc]⟩`.

Consider the case `smul r z _ hz`. Take `⟨a, ha⟩` from `hz`. Use `⟨r * a, ?_⟩` and prove the remaining obligations. Rewrite using `[← algebraMap_smul K r z, map_smul, map_mul, ha, smul_eq_mul]`. Rewrite using `[eq_top_iff, ← e.dualBasis.span_eq, Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Establish `: e.dualBasis i = ((y : K))⁻¹ • (((y : K)) • e.dualBasis i)`. Rewrite using `[smul_smul, inv_mul_cancel₀ hyK, one_smul]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span (hmem i))`.
-/
theorem dualLat_span [FiniteDimensional K V] (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) :
    Submodule.span K (dualLat A : Set (Module.Dual K V)) = ⊤ := by
  classical
  obtain ⟨n, e, he⟩ := exists_basis_in A hsp
  obtain ⟨y, hy, hAy⟩ := Formalism.HN.PlaceLattice.exists_denom e A hA
    (fun x _ => by rw [e.span_eq]; trivial)
  have hyK : (y : K) ≠ 0 := Int.cast_ne_zero.2 hy
  have hmem : ∀ i, ((y : K)) • e.dualBasis i ∈ dualLat A := by
    intro i
    suffices H : ∀ x ∈ Submodule.span (𝓞 K) (Set.range fun a => ((y : K)⁻¹) • e a),
        (((y : K)) • e.dualBasis i) x ∈ Set.range (algebraMap (𝓞 K) K) from
      fun x hx => H x (hAy hx)
    intro x hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, rfl⟩ := hz
      by_cases h : a = i
      · refine ⟨1, ?_⟩
        simp [LinearMap.smul_apply, map_smul, Basis.dualBasis_apply_self, h, hyK]
      · refine ⟨0, ?_⟩
        simp [LinearMap.smul_apply, map_smul, Basis.dualBasis_apply_self, h]
    | zero => exact ⟨0, by simp⟩
    | add z w _ _ hz hw =>
      obtain ⟨a, ha⟩ := hz
      obtain ⟨c, hc⟩ := hw
      exact ⟨a + c, by rw [map_add, map_add, ha, hc]⟩
    | smul r z _ hz =>
      obtain ⟨a, ha⟩ := hz
      refine ⟨r * a, ?_⟩
      rw [← algebraMap_smul K r z, map_smul, map_mul, ha, smul_eq_mul]
  rw [eq_top_iff, ← e.dualBasis.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have : e.dualBasis i = ((y : K))⁻¹ • (((y : K)) • e.dualBasis i) := by
    rw [smul_smul, inv_mul_cancel₀ hyK, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (hmem i))

end Main

end Formalism.HN.DualPolygon

namespace Formalism.HN.DualPolygon

open Formalism.HN

/- English proof (translation)
Rewrite `h` using `[← Real.log_mul hb.ne' hc.ne']`. Conclude with `Real.log_injOn_pos (Set.mem_Ioi.2 ha) (Set.mem_Ioi.2 (mul_pos hb hc)) h`.
-/
theorem eq_mul_of_log_eq_add {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : Real.log a = Real.log b + Real.log c) : a = b * c := by
  rw [← Real.log_mul hb.ne' hc.ne'] at h
  exact Real.log_injOn_pos (Set.mem_Ioi.2 ha) (Set.mem_Ioi.2 (mul_pos hb hc)) h

section Key

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]

/- English proof (translation)
The claim follows from `|(NumberField.discr K : ℝ)| ^ rkK (dualLat A ⊓ annO N) * Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) N) := by classical have hfd : FiniteDimensional K V := Module.Finite.of_basis b have hX' := dualFrame_unit X hX set ρ := Formalism.HermitianLatticesTheor …`.
-/
theorem key_lemma (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) (N : Submodule (𝓞 K) V)
    (hN : IsSat (Formalism.HermitianLatticesTheory.realize b X) A N) :
    rkK (dualLat A ⊓ annO N) + rkK N = finrank K V ∧
    Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N)) *
              Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) A) *
              2 ^ (finrank ℚ K * rkK (dualLat A ⊓ annO N)) =
      |(NumberField.discr K : ℝ)| ^ rkK (dualLat A ⊓ annO N) *
        Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) N) := by
  classical
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hX' := dualFrame_unit X hX
  set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ
  set ρ' := Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X) with hρ'
  set Rp := tdualLat A ⊓ annO N with hRp
  set R := dualLat A ⊓ annO N with hR
  set 𝔡 := differentIdeal ℤ (𝓞 K) with h𝔡
  have h𝔡0 : 𝔡 ≠ ⊥ := differentIdeal_ne_bot
  have hRdR : R = 𝔡 • Rp := dual_inf_ann_eq A N
  have hNA : N ≤ A := hN.1
  have hNfg : N.FG := Submodule.FG.of_le hA hNA
  have hdfg : (dualLat A).FG := dualLat_fg A hsp
  have hRfg : R.FG := Submodule.FG.of_le hdfg inf_le_left
  have hRpfg : Rp.FG := by
    set m : ℕ := Ideal.absNorm 𝔡 with hm
    have hm0 : m ≠ 0 := fun h => h𝔡0 (Ideal.absNorm_eq_zero_iff.1 h)
    have hmK : (m : K) ≠ 0 := Nat.cast_ne_zero.2 hm0
    have hmem : (m : 𝓞 K) ∈ 𝔡 := Ideal.absNorm_mem 𝔡
    let ψ : Module.Dual K V →ₗ[𝓞 K] Module.Dual K V :=
      (((m : K)⁻¹) • (LinearMap.id : Module.Dual K V →ₗ[K] Module.Dual K V)).restrictScalars (𝓞 K)
    refine Submodule.FG.of_le (hdfg.map ψ) ?_
    intro g hg
    refine ⟨(m : 𝓞 K) • g, ?_, ?_⟩
    · have : (m : 𝓞 K) • g ∈ R := by rw [hRdR]; exact Submodule.smul_mem_smul hmem hg
      exact this.1
    · show ((m : K)⁻¹) • ((m : 𝓞 K) • g) = g
      rw [← algebraMap_smul K ((m : 𝓞 K)) g, map_natCast, smul_smul, inv_mul_cancel₀ hmK, one_smul]
  have hspR : Submodule.span K (R : Set (Module.Dual K V)) = Submodule.span K (Rp : Set _) := by
    rw [hRdR]; exact twist_span_smul Rp 𝔡 h𝔡0
  have hrkR : rkK R = rkK Rp := by unfold rkK; rw [hspR]
  obtain ⟨hlatA, hrkA, -⟩ := place_lattice_structure K V ι b X hX A hA
  obtain ⟨hlatN, hrkN, -⟩ := place_lattice_structure K V ι b X hX N hNfg
  obtain ⟨hlatR, hrkR', -⟩ := place_lattice_structure K (Module.Dual K V) ι b.dualBasis (dualFrame X) hX' R hRfg
  obtain ⟨hlatRp, hrkRp', -⟩ :=
    place_lattice_structure K (Module.Dual K V) ι b.dualBasis (dualFrame X) hX' Rp hRpfg
  have hrkAd : rkK A = finrank K V := by unfold rkK; rw [hsp, finrank_top]
  set L := zl ρ A with hL
  set S := zl ρ N with hS
  haveI hLd : DiscreteTopology L := hlatA.2
  have hSsat : Formalism.F.IsSaturated L S := hN.2
  obtain ⟨hQd, hrkQ, hdegQ⟩ := Formalism.F.degQuot _ L S hLd hSsat
  haveI := hQd
  obtain ⟨hDd, hrkD, hdegD, -⟩ := duality_basic (Formalism.F.quot L S)
  haveI := hDd
  have hSL : S ≤ L := hSsat.1
  have hE1 := dualZ_inf_orth L S hSL
  have hE2 := dualZ_zl_eq b X hX A hA hsp N
  set M' := zl ρ' Rp with hM'def
  set φ2 : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) →ₗ[ℝ] _ := (2 : ℝ) • cE with hφ2
  set φh : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) →ₗ[ℝ] _ := ((1 : ℝ) / 2) • cE with hφh
  have hcomp : φh.restrictScalars ℤ ∘ₗ φ2.restrictScalars ℤ = LinearMap.id := by
    ext w
    simp only [hφh, hφ2, LinearMap.coe_comp, Function.comp_apply, LinearMap.restrictScalars_apply,
      LinearMap.smul_apply, map_smul, cE_cE, smul_smul, LinearMap.id_apply]
    norm_num
  have hM' : M' = (dualZ (Formalism.F.quot L S)).map (φh.restrictScalars ℤ) := by
    rw [← hE1, hE2, ← Submodule.map_comp, hcomp, Submodule.map_id]
  have hφhi : ∀ x y, inner ℝ (φh x) (φh y) = ((1 : ℝ) / 2) ^ 2 * inner ℝ x y := by
    intro x y
    simp only [hφh, LinearMap.smul_apply, real_inner_smul_left, real_inner_smul_right, inner_cE]
    ring
  obtain ⟨hM'd, hrkM', hcovM'⟩ :=
    covol_map_scaled φh ((1 : ℝ) / 2) (by norm_num) hφhi (dualZ (Formalism.F.quot L S))
  rw [← hM'] at hM'd hrkM' hcovM'
  haveI := hM'd
  have hRRp : R ≤ Rp := by rw [hRdR]; exact Submodule.smul_le_right
  have hzlle : zl ρ' R ≤ M' := shiftInv_zl_mono ρ' hRRp
  have hn0 : 0 < finrank ℚ K := Module.finrank_pos
  have hrkeq : Formalism.F.rk (zl ρ' R) = Formalism.F.rk M' := by
    have h1 : Formalism.HN.rk ρ' R = Formalism.HN.rk ρ' Rp := by rw [hrkR', hrkRp', hrkR]
    exact h1
  have hcov := Formalism.RankSupermodularCovolume.covol_eq_relIndex_mul_covol (zl ρ' R) M' hzlle hrkeq
  have hρ'inj := Formalism.HN.PlaceLattice.realize_injective b.dualBasis (dualFrame X) hX'
  have hidx : (zl ρ' R).toAddSubgroup.relIndex M'.toAddSubgroup =
      R.toAddSubgroup.relIndex Rp.toAddSubgroup := by
    simp only [hM'def, zl, AddSubgroup.toIntSubmodule_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hρ'inj
  have htw : R.toAddSubgroup.relIndex Rp.toAddSubgroup = Ideal.absNorm 𝔡 ^ rkK Rp := by
    rw [hRdR]; exact twist_index Rp hRpfg 𝔡 h𝔡0
  have hnorm : (Ideal.absNorm 𝔡 : ℝ) = |(NumberField.discr K : ℝ)| := by
    rw [h𝔡, NumberField.absNorm_differentIdeal K (𝓞 K), Nat.cast_natAbs, Int.cast_abs]

  have hSd : DiscreteTopology S := Formalism.F.discreteTopology_of_le hSL
  have hcL := Formalism.F.covolPos _ L hLd
  have hcS := Formalism.F.covolPos _ S hSd
  have hcQ := Formalism.F.covolPos _ _ hQd
  have hcD := Formalism.F.covolPos _ _ hDd
  have hLSQ : Formalism.F.covol L = Formalism.F.covol S * Formalism.F.covol (Formalism.F.quot L S) := by
    apply eq_mul_of_log_eq_add hcL hcS hcQ
    unfold Formalism.F.deg at hdegQ
    linarith
  have hDQ : Formalism.F.covol (dualZ (Formalism.F.quot L S)) * Formalism.F.covol (Formalism.F.quot L S) = 1 := by
    have h1 : Real.log (Formalism.F.covol (dualZ (Formalism.F.quot L S)) * Formalism.F.covol (Formalism.F.quot L S)) = 0 := by
      rw [Real.log_mul hcD.ne' hcQ.ne']
      unfold Formalism.F.deg at hdegD
      linarith
    have h2 := Real.eq_one_of_pos_of_log_eq_zero (mul_pos hcD hcQ) h1
    exact h2

  have hrkL : Formalism.F.rk L = finrank ℚ K * finrank K V := by
    have : Formalism.HN.rk ρ A = _ := hrkA
    rw [hrkAd] at this
    exact this
  have hrkS : Formalism.F.rk S = finrank ℚ K * rkK N := hrkN
  have hrkM'2 : Formalism.F.rk M' = finrank ℚ K * rkK Rp := hrkRp'
  have hrkQ' : Formalism.F.rk (Formalism.F.quot L S) = finrank ℚ K * rkK Rp := by
    rw [← hrkM'2, hrkM', hrkD]
  have hdim : rkK Rp + rkK N = finrank K V := by
    have h1 : finrank ℚ K * finrank K V = finrank ℚ K * rkK N + finrank ℚ K * rkK Rp := by
      rw [← hrkL, ← hrkS, ← hrkQ', hrkQ]
    have h2 : finrank ℚ K * finrank K V = finrank ℚ K * (rkK Rp + rkK N) := by rw [h1]; ring
    exact (Nat.eq_of_mul_eq_mul_left hn0 h2).symm
  refine ⟨by rw [hrkR]; exact hdim, ?_⟩
  rw [hcov, hidx, htw, hrkR, hcovM', hrkD, hrkQ', Nat.cast_pow, hnorm, hLSQ]
  have h2 : ((1 : ℝ) / 2) ^ (finrank ℚ K * rkK Rp) * 2 ^ (finrank ℚ K * rkK Rp) = 1 := by
    rw [← mul_pow]; norm_num
  calc |(NumberField.discr K : ℝ)| ^ rkK Rp *
          (((1 : ℝ) / 2) ^ (finrank ℚ K * rkK Rp) * Formalism.F.covol (dualZ (Formalism.F.quot L S))) *
          (Formalism.F.covol S * Formalism.F.covol (Formalism.F.quot L S)) * 2 ^ (finrank ℚ K * rkK Rp)
        = |(NumberField.discr K : ℝ)| ^ rkK Rp * Formalism.F.covol S *
          (Formalism.F.covol (dualZ (Formalism.F.quot L S)) * Formalism.F.covol (Formalism.F.quot L S)) *
          (((1 : ℝ) / 2) ^ (finrank ℚ K * rkK Rp) * 2 ^ (finrank ℚ K * rkK Rp)) := by ring
    _ = _ := by rw [hDQ, h2]; ring

end Key

end Formalism.HN.DualPolygon

namespace Formalism.HN.DualPolygon

open Formalism.HN

/- English proof (translation)
Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hD.le]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rpow_neg_half_nat_pow {D : ℝ} (hD : 0 < D) (k : ℕ) :
    D ^ (-(k : ℝ) / 2) = (D ^ (-(1 : ℝ) / 2)) ^ k := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hD.le]
  congr 1
  ring

/- English proof (translation)
Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hD.le]`. Evaluate the numerical expressions. Rewrite using `[Real.rpow_neg_one, inv_mul_cancel₀ hD.ne']`.
-/
theorem rpow_neg_half_sq_mul {D : ℝ} (hD : 0 < D) : (D ^ (-(1 : ℝ) / 2)) ^ 2 * D = 1 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hD.le]
  norm_num
  rw [Real.rpow_neg_one, inv_mul_cancel₀ hD.ne']

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem ht_alg (f r j : ℕ) (D u cR cL cS : ℝ) (hu : u ^ 2 * D = 1)
    (h : cR * cL * 2 ^ (2 * f * r) = D ^ r * cS) :
    2 ^ (f * r) * u ^ r * cR * (2 ^ (f * (r + j)) * u ^ (r + j) * cL) =
      2 ^ (f * j) * u ^ j * cS := by
  calc 2 ^ (f * r) * u ^ r * cR * (2 ^ (f * (r + j)) * u ^ (r + j) * cL)
      = 2 ^ (f * j) * u ^ j * (u ^ 2) ^ r * (cR * cL * 2 ^ (2 * f * r)) := by ring
    _ = 2 ^ (f * j) * u ^ j * (u ^ 2 * D) ^ r * cS := by rw [h]; ring
    _ = _ := by rw [hu, one_pow, mul_one]

section HtDual

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]

/- English proof (translation)
Take `⟨hdim, hcov⟩` from `key_lemma b X hX A hA hsp N hN`. Establish `hrkAd : rkK A = finrank K V` using `by unfold rkK; rw [hsp, finrank_top]`. Establish `hD : 0 < |(NumberField.discr K : ℝ)|` using `abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))`. Establish `hn : finrank ℚ K = 2 * nPl K` using `sizeMu_finrank_eq K`. Unfold `ht`.

Rewrite using `[hrkAd, ← hdim, rpow_neg_half_nat_pow hD, rpow_neg_half_nat_pow hD, rpow_neg_half_nat_pow hD]`. Rewrite `hcov` using `[hn]`. Use `push_cast`. Conclude with `ht_alg (nPl K) _ _ _ _ _ _ _ (rpow_neg_half_sq_mul hD) hcov`.
-/
theorem ht_dual_ann (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) (N : Submodule (𝓞 K) V)
    (hN : IsSat (Formalism.HermitianLatticesTheory.realize b X) A N) :
    ht b.dualBasis (dualFrame X) (dualLat A ⊓ annO N) * ht b X A = ht b X N := by
  obtain ⟨hdim, hcov⟩ := key_lemma b X hX A hA hsp N hN
  have hrkAd : rkK A = finrank K V := by unfold rkK; rw [hsp, finrank_top]
  have hD : 0 < |(NumberField.discr K : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))
  have hn : finrank ℚ K = 2 * nPl K := sizeMu_finrank_eq K
  unfold ht
  rw [hrkAd, ← hdim, rpow_neg_half_nat_pow hD, rpow_neg_half_nat_pow hD, rpow_neg_half_nat_pow hD]
  rw [hn] at hcov
  push_cast
  exact ht_alg (nPl K) _ _ _ _ _ _ _ (rpow_neg_half_sq_mul hD) hcov

/- English proof (translation)
Establish `h1 : rkK (⊥ : Submodule (𝓞 K) V) = 0`. Unfold `rkK`. Simplify using the standard rewrite rules. Establish `h2 : zl (Formalism.HermitianLatticesTheory.realize b X) (⊥ : Submodule (𝓞 K) V) = ⊥` using `satBasic_zl_bot _`. Unfold `ht`.

Rewrite using `[h1, h2, (Formalism.F.covolBasic _).1]`. Simplify using the standard rewrite rules.
-/
theorem ht_bot (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) :
    ht b X (⊥ : Submodule (𝓞 K) V) = 1 := by
  have h1 : rkK (⊥ : Submodule (𝓞 K) V) = 0 := by
    unfold rkK; simp
  have h2 : zl (Formalism.HermitianLatticesTheory.realize b X) (⊥ : Submodule (𝓞 K) V) = ⊥ := satBasic_zl_bot _
  unfold ht
  rw [h1, h2, (Formalism.F.covolBasic _).1]
  simp

omit [StarRing K] [IsTotallyComplex K] [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Use extensionality with `f`. Simplify using `only [Submodule.mem_top, iff_true]`. Introduce `x hx`. Rewrite `hx` using `[Submodule.mem_bot]`. Simplify using `[hx]`.
-/
theorem annO_bot : annO (⊥ : Submodule (𝓞 K) V) = ⊤ := by
  ext f
  simp only [Submodule.mem_top, iff_true]
  intro x hx
  rw [Submodule.mem_bot] at hx
  simp [hx]

/- English proof (translation)
Take `⟨hlat, -, -⟩` from `place_lattice_structure K V ι b X hX A hA`. Establish `hsat : IsSat (Formalism.HermitianLatticesTheory.realize b X) A ⊥` using `(saturation_basic_properties (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) A hlat).2.2.2.2.2.1`. Use `ht_dual_ann b X hX A hA hsp ⊥ hsat` as an intermediate fact. Rewrite `this` using `[annO_bot, inf_top_eq, ht_bot]`. Then use the resulting hypothesis.
-/
theorem ht_dual (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) :
    ht b.dualBasis (dualFrame X) (dualLat A) * ht b X A = 1 := by
  obtain ⟨hlat, -, -⟩ := place_lattice_structure K V ι b X hX A hA
  have hsat : IsSat (Formalism.HermitianLatticesTheory.realize b X) A ⊥ :=
    (saturation_basic_properties (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) A hlat).2.2.2.2.2.1
  have := ht_dual_ann b X hX A hA hsp ⊥ hsat
  rwa [annO_bot, inf_top_eq, ht_bot] at this

/- English proof (translation)
Establish `hfd : FiniteDimensional K V` using `Module.Finite.of_basis b`. Unfold `rkK`. Rewrite using `[dualLat_span A hA hsp, finrank_top, Subspace.dual_finrank_eq]`.
-/
theorem rkK_dualLat (b : Basis ι K V) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) : rkK (dualLat A) = finrank K V := by
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  unfold rkK
  rw [dualLat_span A hA hsp, finrank_top, Subspace.dual_finrank_eq]

end HtDual

end Formalism.HN.DualPolygon

namespace Formalism.HN.DualPolygon

open Formalism.HN

section DD

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]

/- English proof (translation)
Rewrite using `[dualFrame_dualFrame X hX]`. Establish `hvec : ∀ v, Formalism.HermitianLatticesTheory.vecAt b.dualBasis.dualBasis v (Module.Dual.eval K V x) = Formalism.HermitianLatticesTheory.vecAt b v x`. Introduce `v`. Use function extensionality and compare the values at `i`. Simplify using `[Formalism.HermitianLatticesTheory.vecAt, Basis.dualBasis_repr, Basis.dualBasis_apply]`.

Establish `hf : ∀ v, Formalism.HermitianLatticesTheory.fcoord b.dualBasis.dualBasis X v (Module.Dual.eval K V x) = Formalism.HermitianLatticesTheory.fcoord b X v x`. Introduce `v`. Simplify using `only [Formalism.HermitianLatticesTheory.fcoord, hvec]`. Use extensionality with `p`. Simplify using `[Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw, hf]`.
-/
theorem realize_eval (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (x : V) :
    Formalism.HermitianLatticesTheory.realize b.dualBasis.dualBasis (dualFrame (dualFrame X)) (Module.Dual.eval K V x) =
      Formalism.HermitianLatticesTheory.realize b X x := by
  rw [dualFrame_dualFrame X hX]
  have hvec : ∀ v, Formalism.HermitianLatticesTheory.vecAt b.dualBasis.dualBasis v (Module.Dual.eval K V x) =
      Formalism.HermitianLatticesTheory.vecAt b v x := by
    intro v
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt, Basis.dualBasis_repr, Basis.dualBasis_apply]
  have hf : ∀ v, Formalism.HermitianLatticesTheory.fcoord b.dualBasis.dualBasis X v (Module.Dual.eval K V x) =
      Formalism.HermitianLatticesTheory.fcoord b X v x := by
    intro v
    simp only [Formalism.HermitianLatticesTheory.fcoord, hvec]
  ext p
  simp [Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw, hf]

/- English proof (translation)
Establish `hfd : FiniteDimensional K V` using `Module.Finite.of_basis b`. Establish `hX'` using `dualFrame_unit X hX`. Use `set A2 := (dualLat (dualLat A)).comap ((Module.Dual.eval K V).restrictScalars (𝓞 K)) with hA2`. Use `set e := Module.evalEquiv K V with he`. Establish `hee : ∀ x, e x = Module.Dual.eval K V x` using `fun x => rfl`.

Establish `hAA2 : A ≤ A2`. Introduce `x hx f hf`. Conclude with `hf x hx`. Establish `hdfg` using `dualLat_fg A hsp`. Establish `hdsp` using `dualLat_span A hA hsp`.

Establish `hddfg : (dualLat (dualLat A)).FG` using `dualLat_fg (dualLat A) hdsp`. Establish `hddsp` using `dualLat_span (dualLat A) hdfg hdsp`. Establish `hmap : A2.map (e.toLinearMap.restrictScalars (𝓞 K)) = dualLat (dualLat A)`. Apply `Submodule.map_comap_eq_of_surjective` to reduce the goal to its premises. Conclude with `e.surjective`.

Establish `hA2fg : A2.FG`. Establish `: A2 = (dualLat (dualLat A)).map (e.symm.toLinearMap.restrictScalars (𝓞 K))`. Use extensionality with `x`. Simplify using `only [hA2, Submodule.mem_comap, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Conclude with `⟨e x, hx, e.symm_apply_apply x⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Rewrite using `[← hee, e.apply_symm_apply]`. Conclude with `hy`.

Rewrite using `[this]`. Conclude with `hddfg.map _`. Establish `hA2sp : Submodule.span K (A2 : Set V) = ⊤` using `eq_top_iff.2 (hsp ▸ Submodule.span_mono hAA2)`. Establish `hht1` using `ht_dual b X hX A hA hsp`. Establish `hht2` using `ht_dual b.dualBasis (dualFrame X) hX' (dualLat A) hdfg hdsp`.

Establish `hzl : zl (Formalism.HermitianLatticesTheory.realize b.dualBasis.dualBasis (dualFrame (dualFrame X))) (dualLat (dualLat A)) = zl (Formalism.HermitianLatticesTheory.realize b X) A2`. Rewrite using `[← hmap]`. Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, ⟨x, hx, rfl⟩, rfl⟩`.

Conclude with `⟨x, hx, (realize_eval b X hX x).symm⟩`. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨e x, ⟨x, hx, rfl⟩, realize_eval b X hX x⟩`. Establish `hrk1 : rkK (dualLat (dualLat A)) = finrank K V`. Unfold `rkK`.

Rewrite using `[hddsp, finrank_top, Subspace.dual_finrank_eq, Subspace.dual_finrank_eq]`. Establish `hrk2 : rkK A2 = finrank K V` using `by unfold rkK; rw [hA2sp, finrank_top]`. Establish `hrkA : rkK A = finrank K V` using `by unfold rkK; rw [hsp, finrank_top]`. Establish `hhtA2 : ht b X A2 = ht b X A`. Establish `h3 : ht b.dualBasis.dualBasis (dualFrame (dualFrame X)) (dualLat (dualLat A)) = ht b X A2`.

Unfold `ht`. Rewrite using `[hzl, hrk1, hrk2]`. Rewrite using `[← h3]`. Establish `hpos : 0 < ht b.dualBasis (dualFrame X) (dualLat A)` using `(place_lattice_structure K _ ι b.dualBasis (dualFrame X) hX' (dualLat A) hdfg).2.2`. Clear denominators, using `at hht1 hht2 ⊢` for the nonvanishing conditions.

Use polynomial arithmetic with `[hht1, hht2, hpos]`. Establish `hD : 0 < |(NumberField.discr K : ℝ)|` using `abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))`. Establish `hcovEq : Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) A2) = Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) A)`. Unfold `ht at hhtA2`. Rewrite `hhtA2` using `[hrk2, hrkA]`.

Establish `hc : (0 : ℝ) < (2 : ℝ) ^ (nPl K * finrank K V) * |(NumberField.discr K : ℝ)| ^ (-(finrank K V : ℝ) / 2)` using `by positivity`. Conclude with `mul_left_cancel₀ hc.ne' hhtA2`. Take `⟨hlat2, hrkz2, -⟩` from `place_lattice_structure K V ι b X hX A2 hA2fg`. Take `⟨hlat1, hrkz1, -⟩` from `place_lattice_structure K V ι b X hX A hA`. Use `haveI := hlat2.2`.

Establish `hrkeq : Formalism.F.rk (zl (Formalism.HermitianLatticesTheory.realize b X) A) = Formalism.F.rk (zl (Formalism.HermitianLatticesTheory.realize b X) A2)`. Establish `h : Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) A = Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) A2`. Rewrite using `[hrkz1, hrkz2, hrkA, hrk2]`. Conclude with `h`. Establish `hcov` using `Formalism.RankSupermodularCovolume.covol_eq_relIndex_mul_covol _ _ (shiftInv_zl_mono (Formalism.HermitianLatticesTheory.realize b X) hAA2) hrkeq`.

Establish `hpos` using `Formalism.F.covolPos _ _ hlat2.2`. Rewrite `hcov` using `[hcovEq]`. Establish `hidx1 : ((zl (Formalism.HermitianLatticesTheory.realize b X) A).toAddSubgroup.relIndex (zl (Formalism.HermitianLatticesTheory.realize b X) A2).toAddSubgroup : ℝ) = 1`. Establish `hp1 : 0 < Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) A)` using `by rw [← hcovEq]; exact hpos`. Clear denominators, using `at hcov` for the nonvanishing conditions.

Use polynomial arithmetic with `[hcov, hp1]`. Establish `hinj` using `Formalism.HN.PlaceLattice.realize_injective b X hX`. Establish `hidx : A.toAddSubgroup.relIndex A2.toAddSubgroup = 1`. Establish `h : (zl (Formalism.HermitianLatticesTheory.realize b X) A).toAddSubgroup.relIndex (zl (Formalism.HermitianLatticesTheory.realize b X) A2).toAddSubgroup = A.toAddSubgroup.relIndex A2.toAddSubgroup`. Simplify using `only [zl, AddSubgroup.toIntSubmodule_toAddSubgroup]`.

Conclude with `AddSubgroup.relIndex_map_map_of_injective _ _ hinj`. Rewrite using `[← h]`. Conclude with `hidx1` after adjusting the coercions. Establish `hle : A2.toAddSubgroup ≤ A.toAddSubgroup` using `AddSubgroup.relIndex_eq_one.1 hidx`. Conclude with `le_antisymm (fun x hx => hle hx) hAA2`.
-/
theorem dual_dual (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) :
    (dualLat (dualLat A)).comap ((Module.Dual.eval K V).restrictScalars (𝓞 K)) = A := by
  classical
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hX' := dualFrame_unit X hX
  set A2 := (dualLat (dualLat A)).comap ((Module.Dual.eval K V).restrictScalars (𝓞 K)) with hA2
  set e := Module.evalEquiv K V with he
  have hee : ∀ x, e x = Module.Dual.eval K V x := fun x => rfl
  have hAA2 : A ≤ A2 := by
    intro x hx f hf
    exact hf x hx
  have hdfg := dualLat_fg A hsp
  have hdsp := dualLat_span A hA hsp
  have hddfg : (dualLat (dualLat A)).FG := dualLat_fg (dualLat A) hdsp
  have hddsp := dualLat_span (dualLat A) hdfg hdsp
  have hmap : A2.map (e.toLinearMap.restrictScalars (𝓞 K)) = dualLat (dualLat A) := by
    apply Submodule.map_comap_eq_of_surjective
    exact e.surjective
  have hA2fg : A2.FG := by
    have : A2 = (dualLat (dualLat A)).map (e.symm.toLinearMap.restrictScalars (𝓞 K)) := by
      ext x
      simp only [hA2, Submodule.mem_comap, Submodule.mem_map, LinearMap.restrictScalars_apply,
        LinearEquiv.coe_coe]
      constructor
      · intro hx
        exact ⟨e x, hx, e.symm_apply_apply x⟩
      · rintro ⟨y, hy, rfl⟩
        rw [← hee, e.apply_symm_apply]
        exact hy
    rw [this]
    exact hddfg.map _
  have hA2sp : Submodule.span K (A2 : Set V) = ⊤ :=
    eq_top_iff.2 (hsp ▸ Submodule.span_mono hAA2)

  have hht1 := ht_dual b X hX A hA hsp
  have hht2 := ht_dual b.dualBasis (dualFrame X) hX' (dualLat A) hdfg hdsp
  have hzl : zl (Formalism.HermitianLatticesTheory.realize b.dualBasis.dualBasis (dualFrame (dualFrame X)))
      (dualLat (dualLat A)) = zl (Formalism.HermitianLatticesTheory.realize b X) A2 := by
    rw [← hmap]
    ext w
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (realize_eval b X hX x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨e x, ⟨x, hx, rfl⟩, realize_eval b X hX x⟩
  have hrk1 : rkK (dualLat (dualLat A)) = finrank K V := by
    unfold rkK
    rw [hddsp, finrank_top, Subspace.dual_finrank_eq, Subspace.dual_finrank_eq]
  have hrk2 : rkK A2 = finrank K V := by unfold rkK; rw [hA2sp, finrank_top]
  have hrkA : rkK A = finrank K V := by unfold rkK; rw [hsp, finrank_top]
  have hhtA2 : ht b X A2 = ht b X A := by
    have h3 : ht b.dualBasis.dualBasis (dualFrame (dualFrame X)) (dualLat (dualLat A)) =
        ht b X A2 := by
      unfold ht; rw [hzl, hrk1, hrk2]
    rw [← h3]
    have hpos : 0 < ht b.dualBasis (dualFrame X) (dualLat A) :=
      (place_lattice_structure K _ ι b.dualBasis (dualFrame X) hX' (dualLat A) hdfg).2.2
    field_simp at hht1 hht2 ⊢
    nlinarith [hht1, hht2, hpos]

  have hD : 0 < |(NumberField.discr K : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))
  have hcovEq : Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) A2) =
      Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) A) := by
    unfold ht at hhtA2
    rw [hrk2, hrkA] at hhtA2
    have hc : (0 : ℝ) < (2 : ℝ) ^ (nPl K * finrank K V) *
        |(NumberField.discr K : ℝ)| ^ (-(finrank K V : ℝ) / 2) := by positivity
    exact mul_left_cancel₀ hc.ne' hhtA2
  obtain ⟨hlat2, hrkz2, -⟩ := place_lattice_structure K V ι b X hX A2 hA2fg
  obtain ⟨hlat1, hrkz1, -⟩ := place_lattice_structure K V ι b X hX A hA
  haveI := hlat2.2
  have hrkeq : Formalism.F.rk (zl (Formalism.HermitianLatticesTheory.realize b X) A) = Formalism.F.rk (zl (Formalism.HermitianLatticesTheory.realize b X) A2) := by
    have h : Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) A = Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) A2 := by
      rw [hrkz1, hrkz2, hrkA, hrk2]
    exact h
  have hcov := Formalism.RankSupermodularCovolume.covol_eq_relIndex_mul_covol _ _
    (shiftInv_zl_mono (Formalism.HermitianLatticesTheory.realize b X) hAA2) hrkeq
  have hpos := Formalism.F.covolPos _ _ hlat2.2
  rw [hcovEq] at hcov
  have hidx1 : ((zl (Formalism.HermitianLatticesTheory.realize b X) A).toAddSubgroup.relIndex
      (zl (Formalism.HermitianLatticesTheory.realize b X) A2).toAddSubgroup : ℝ) = 1 := by
    have hp1 : 0 < Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) A) := by rw [← hcovEq]; exact hpos
    field_simp at hcov
    nlinarith [hcov, hp1]
  have hinj := Formalism.HN.PlaceLattice.realize_injective b X hX
  have hidx : A.toAddSubgroup.relIndex A2.toAddSubgroup = 1 := by
    have h : (zl (Formalism.HermitianLatticesTheory.realize b X) A).toAddSubgroup.relIndex
        (zl (Formalism.HermitianLatticesTheory.realize b X) A2).toAddSubgroup = A.toAddSubgroup.relIndex A2.toAddSubgroup := by
      simp only [zl, AddSubgroup.toIntSubmodule_toAddSubgroup]
      exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj
    rw [← h]
    exact_mod_cast hidx1
  have hle : A2.toAddSubgroup ≤ A.toAddSubgroup := AddSubgroup.relIndex_eq_one.1 hidx
  exact le_antisymm (fun x hx => hle hx) hAA2

end DD

end Formalism.HN.DualPolygon

namespace Formalism.HN.DualPolygon

open Formalism.HN

section HNDual

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]

/- English proof (translation)
Take `⟨hlat, -, -⟩` from `place_lattice_structure K V ι b X hX A hA`. Take `⟨N', h1, h2, h3⟩` from `real_saturation_property (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) A N hlat hNA`. Take `⟨s1, -, s3⟩` from `Formalism.F.saturProps _ (zl (Formalism.HermitianLatticesTheory.realize b X) A) (zl (Formalism.HermitianLatticesTheory.realize b X) N) hlat.2 (shiftInv_zl_mono (Formalism.HermitianLatticesTheory.realize b X) hNA)`. Establish `hrk : Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N' = Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N`. Unfold `Formalism.HN.rk`.

Rewrite using `[h3]`. Conclude with `s3`. Establish `hSB` using `saturation_basic_properties (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) A hlat`. Conclude with `⟨N', h1, ⟨h2, by rw [h3]; exact s1⟩, hrk, (hSB.2.1 N N' h1 h2).2 hrk.symm⟩`.
-/
theorem sat_exists (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG) (N : Submodule (𝓞 K) V)
    (hNA : N ≤ A) :
    ∃ N', N ≤ N' ∧ IsSat (Formalism.HermitianLatticesTheory.realize b X) A N' ∧
      Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N' = Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N ∧
      deg (Formalism.HermitianLatticesTheory.realize b X) N ≤ deg (Formalism.HermitianLatticesTheory.realize b X) N' := by
  obtain ⟨hlat, -, -⟩ := place_lattice_structure K V ι b X hX A hA
  obtain ⟨N', h1, h2, h3⟩ := real_saturation_property (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) A N hlat hNA
  obtain ⟨s1, -, s3⟩ := Formalism.F.saturProps _ (zl (Formalism.HermitianLatticesTheory.realize b X) A)
    (zl (Formalism.HermitianLatticesTheory.realize b X) N) hlat.2 (shiftInv_zl_mono (Formalism.HermitianLatticesTheory.realize b X) hNA)
  have hrk : Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N' = Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N := by
    unfold Formalism.HN.rk; rw [h3]; exact s3
  have hSB := saturation_basic_properties (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) A hlat
  exact ⟨N', h1, ⟨h2, by rw [h3]; exact s1⟩, hrk, (hSB.2.1 N N' h1 h2).2 hrk.symm⟩

/- English proof (translation)
Establish `hfd : FiniteDimensional K V` using `Module.Finite.of_basis b`. Take `⟨n, e, he⟩` from `exists_basis_in A hsp`. Use `set W : Submodule K V := (Submodule.span K (R : Set (Module.Dual K V))).dualCoannihilator with hW`. Use `set N : Submodule (𝓞 K) V := A ⊓ W.restrictScalars (𝓞 K) with hN`. Establish `hNA : N ≤ A` using `inf_le_left`.

Establish `hspN : Submodule.span K (N : Set V) = W`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce `x hx`. Conclude with `hx.2`.

Introduce `w hw`. Take `⟨c, hc, hcw⟩` from `exists_int_smul_mem A e he w`. Establish `hcK : (c : K) ≠ 0` using `Int.cast_ne_zero.2 hc`. Establish `hmem : (c : K) • w ∈ N` using `⟨hcw, W.smul_mem _ hw⟩`. Establish `: w = ((c : K))⁻¹ • ((c : K) • w)` using `by rw [smul_smul, inv_mul_cancel₀ hcK, one_smul]`.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hmem)`. Establish `hdim : rkK R + rkK N = finrank K V`. Unfold `rkK`. Rewrite using `[hspN]`.

Conclude with `Subspace.finrank_add_finrank_dualCoannihilator_eq _`. Take `⟨hlat, -, -⟩` from `place_lattice_structure K V ι b X hX A hA`. Establish `hsat : IsSat (Formalism.HermitianLatticesTheory.realize b X) A N`. Rewrite using `[shiftInv_isSat_iff (Formalism.HermitianLatticesTheory.realize b X) hlat N]`. Use `⟨hNA, fun N'' h1 h2 h3 => ?_⟩` and prove the remaining obligations.

Establish `hfg'' : N''.FG` using `Submodule.FG.of_le hA h2`. Establish `hNfg : N.FG` using `Submodule.FG.of_le hA hNA`. Take `⟨-, hr1, -⟩` from `place_lattice_structure K V ι b X hX N'' hfg''`. Take `⟨-, hr2, -⟩` from `place_lattice_structure K V ι b X hX N hNfg`. Establish `hn0 : 0 < finrank ℚ K` using `Module.finrank_pos`.

Establish `hrkK : rkK N'' = rkK N`. Rewrite `h3` using `[hr1, hr2]`. Conclude with `Nat.eq_of_mul_eq_mul_left hn0 h3`. Establish `hsp_eq : Submodule.span K (N : Set V) = Submodule.span K (N'' : Set V)` using `Submodule.eq_of_le_of_finrank_eq (Submodule.span_mono h1) hrkK.symm`. Apply `le_antisymm _ h1` to reduce the goal to its premises.

Introduce `x hx`. Use `⟨h2 hx, ?_⟩` and prove the remaining obligations. Use `show x ∈ W`. Rewrite using `[← hspN, hsp_eq]`. Conclude with `Submodule.subset_span hx`.

Use `⟨N, hsat, fun f hf => ⟨hR hf, fun x hx => ?_⟩, hdim⟩` and prove the remaining obligations. Establish `hxW : x ∈ W` using `hx.2`. Conclude with `(Submodule.mem_dualCoannihilator x).1 hxW f (Submodule.subset_span hf)`.
-/
theorem sat_of_ann (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) (R : Submodule (𝓞 K) (Module.Dual K V))
    (hR : R ≤ dualLat A) :
    ∃ N, IsSat (Formalism.HermitianLatticesTheory.realize b X) A N ∧ R ≤ dualLat A ⊓ annO N ∧
      rkK R + rkK N = finrank K V := by
  classical
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  obtain ⟨n, e, he⟩ := exists_basis_in A hsp
  set W : Submodule K V := (Submodule.span K (R : Set (Module.Dual K V))).dualCoannihilator with hW
  set N : Submodule (𝓞 K) V := A ⊓ W.restrictScalars (𝓞 K) with hN
  have hNA : N ≤ A := inf_le_left
  have hspN : Submodule.span K (N : Set V) = W := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      exact hx.2
    · intro w hw
      obtain ⟨c, hc, hcw⟩ := exists_int_smul_mem A e he w
      have hcK : (c : K) ≠ 0 := Int.cast_ne_zero.2 hc
      have hmem : (c : K) • w ∈ N := ⟨hcw, W.smul_mem _ hw⟩
      have : w = ((c : K))⁻¹ • ((c : K) • w) := by rw [smul_smul, inv_mul_cancel₀ hcK, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  have hdim : rkK R + rkK N = finrank K V := by
    unfold rkK
    rw [hspN]
    exact Subspace.finrank_add_finrank_dualCoannihilator_eq _
  obtain ⟨hlat, -, -⟩ := place_lattice_structure K V ι b X hX A hA
  have hsat : IsSat (Formalism.HermitianLatticesTheory.realize b X) A N := by
    rw [shiftInv_isSat_iff (Formalism.HermitianLatticesTheory.realize b X) hlat N]
    refine ⟨hNA, fun N'' h1 h2 h3 => ?_⟩
    have hfg'' : N''.FG := Submodule.FG.of_le hA h2
    have hNfg : N.FG := Submodule.FG.of_le hA hNA
    obtain ⟨-, hr1, -⟩ := place_lattice_structure K V ι b X hX N'' hfg''
    obtain ⟨-, hr2, -⟩ := place_lattice_structure K V ι b X hX N hNfg
    have hn0 : 0 < finrank ℚ K := Module.finrank_pos
    have hrkK : rkK N'' = rkK N := by
      rw [hr1, hr2] at h3
      exact Nat.eq_of_mul_eq_mul_left hn0 h3
    have hsp_eq : Submodule.span K (N : Set V) = Submodule.span K (N'' : Set V) :=
      Submodule.eq_of_le_of_finrank_eq (Submodule.span_mono h1) hrkK.symm
    apply le_antisymm _ h1
    intro x hx
    refine ⟨h2 hx, ?_⟩
    show x ∈ W
    rw [← hspN, hsp_eq]
    exact Submodule.subset_span hx
  refine ⟨N, hsat, fun f hf => ⟨hR hf, fun x hx => ?_⟩, hdim⟩
  have hxW : x ∈ W := hx.2
  exact (Submodule.mem_dualCoannihilator x).1 hxW f (Submodule.subset_span hf)

/- English proof (translation)
Establish `hX'` using `dualFrame_unit X hX`. Take `⟨hdim, hcov⟩` from `key_lemma b X hX A hA hsp N hN`. Establish `hNfg : N.FG` using `Submodule.FG.of_le hA hN.1`. Establish `hfd : FiniteDimensional K V` using `Module.Finite.of_basis b`. Establish `hdfg` using `dualLat_fg A hsp`.

Establish `hRfg : (dualLat A ⊓ annO N).FG` using `Submodule.FG.of_le hdfg inf_le_left`. Take `⟨hlatA, hrkA, -⟩` from `place_lattice_structure K V ι b X hX A hA`. Take `⟨hlatN, hrkN, -⟩` from `place_lattice_structure K V ι b X hX N hNfg`. Take `⟨hlatR, hrkR, -⟩` from `place_lattice_structure K _ ι b.dualBasis (dualFrame X) hX' (dualLat A ⊓ annO N) hRfg`. Establish `hrkAd : rkK A = finrank K V` using `by unfold rkK; rw [hsp, finrank_top]`.

Establish `hD : 0 < |(NumberField.discr K : ℝ)|` using `abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))`. Establish `hn0 : (0 : ℝ) < finrank ℚ K` using `by exact_mod_cast Module.finrank_pos`. Establish `hcR` using `Formalism.F.covolPos _ _ hlatR.2`. Establish `hcA` using `Formalism.F.covolPos _ _ hlatA.2`. Establish `hcN` using `Formalism.F.covolPos _ _ hlatN.2`.

Establish `hlog` using `congrArg Real.log hcov`. Rewrite `hlog` using `[Real.log_mul (mul_pos hcR hcA).ne' (by positivity), Real.log_mul hcR.ne' hcA.ne', Real.log_mul (by positivity) hcN.ne', Real.log_pow, Real.log_pow]`. Use `set r := rkK (dualLat A ⊓ annO N) with hr`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `deg Formalism.F.deg`.

Rewrite using `[hrkR]`. Establish `h1 : (Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ)) * ((finrank ℚ K * r : ℕ) : ℝ) = ((finrank ℚ K * r : ℕ) : ℝ) * Real.log 2 - (r : ℝ) * Real.log |(NumberField.discr K : ℝ)|`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[h1]`.

Move the coercions through the operations in `at hlog ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hrkR, hrkA, hrkN, hrkAd, ← hdim]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem deg_R (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) (N : Submodule (𝓞 K) V)
    (hN : IsSat (Formalism.HermitianLatticesTheory.realize b X) A N) :
    deg (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N) =
        deg (Formalism.HermitianLatticesTheory.realize b X) N - deg (Formalism.HermitianLatticesTheory.realize b X) A +
          (Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ)) *
            (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N) : ℝ) ∧
      (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N) : ℝ) =
        (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) A : ℝ) - Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N := by
  have hX' := dualFrame_unit X hX
  obtain ⟨hdim, hcov⟩ := key_lemma b X hX A hA hsp N hN
  have hNfg : N.FG := Submodule.FG.of_le hA hN.1
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hdfg := dualLat_fg A hsp
  have hRfg : (dualLat A ⊓ annO N).FG := Submodule.FG.of_le hdfg inf_le_left
  obtain ⟨hlatA, hrkA, -⟩ := place_lattice_structure K V ι b X hX A hA
  obtain ⟨hlatN, hrkN, -⟩ := place_lattice_structure K V ι b X hX N hNfg
  obtain ⟨hlatR, hrkR, -⟩ :=
    place_lattice_structure K _ ι b.dualBasis (dualFrame X) hX' (dualLat A ⊓ annO N) hRfg
  have hrkAd : rkK A = finrank K V := by unfold rkK; rw [hsp, finrank_top]
  have hD : 0 < |(NumberField.discr K : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))
  have hn0 : (0 : ℝ) < finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hcR := Formalism.F.covolPos _ _ hlatR.2
  have hcA := Formalism.F.covolPos _ _ hlatA.2
  have hcN := Formalism.F.covolPos _ _ hlatN.2
  have hlog := congrArg Real.log hcov
  rw [Real.log_mul (mul_pos hcR hcA).ne' (by positivity), Real.log_mul hcR.ne' hcA.ne',
    Real.log_mul (by positivity) hcN.ne', Real.log_pow, Real.log_pow] at hlog
  set r := rkK (dualLat A ⊓ annO N) with hr
  refine ⟨?_, ?_⟩
  · unfold deg Formalism.F.deg
    rw [hrkR]
    have h1 : (Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ)) *
        ((finrank ℚ K * r : ℕ) : ℝ) = ((finrank ℚ K * r : ℕ) : ℝ) * Real.log 2 -
          (r : ℝ) * Real.log |(NumberField.discr K : ℝ)| := by
      push_cast
      field_simp
    rw [h1]
    push_cast at hlog ⊢
    linarith
  · rw [hrkR, hrkA, hrkN, hrkAd, ← hdim]
    push_cast
    ring

/- English proof (translation)
Establish `hfd : FiniteDimensional K V` using `Module.Finite.of_basis b`. Establish `hX'` using `dualFrame_unit X hX`. Establish `hdfg` using `dualLat_fg A hsp`. Take `⟨hlat', -, -⟩` from `place_lattice_structure K _ ι b.dualBasis (dualFrame X) hX' (dualLat A) hdfg`. Establish `hSB'` using `saturation_basic_properties (𝓞 K) (Module.Dual K V) _ _ (dualLat A) hlat'`.

Take `⟨N, hN, hRN, hdim⟩` from `sat_of_ann b X hX A hA hsp R hR`. Take `⟨hdimN, -⟩` from `key_lemma b X hX A hA hsp N hN`. Establish `hRfg : R.FG` using `Submodule.FG.of_le hdfg hR`. Establish `hRNfg : (dualLat A ⊓ annO N).FG` using `Submodule.FG.of_le hdfg inf_le_left`. Take `⟨-, r1, -⟩` from `place_lattice_structure K _ ι b.dualBasis (dualFrame X) hX' R hRfg`.

Take `⟨-, r2, -⟩` from `place_lattice_structure K _ ι b.dualBasis (dualFrame X) hX' _ hRNfg`. Establish `hrk : Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) R = Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N)`. Combine the equalities or inequalities in the displayed calculation. Conclude with `⟨N, hN, hrk, (hSB'.2.1 R _ hRN inf_le_left).2 hrk⟩`.
-/
theorem corr_R (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) (R : Submodule (𝓞 K) (Module.Dual K V))
    (hR : R ≤ dualLat A) : ∃ N, IsSat (Formalism.HermitianLatticesTheory.realize b X) A N ∧
      Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) R =
        Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N) ∧
      deg (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) R ≤
        deg (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N) := by
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hX' := dualFrame_unit X hX
  have hdfg := dualLat_fg A hsp
  obtain ⟨hlat', -, -⟩ := place_lattice_structure K _ ι b.dualBasis (dualFrame X) hX' (dualLat A) hdfg
  have hSB' := saturation_basic_properties (𝓞 K) (Module.Dual K V) _ _ (dualLat A) hlat'
  obtain ⟨N, hN, hRN, hdim⟩ := sat_of_ann b X hX A hA hsp R hR
  obtain ⟨hdimN, -⟩ := key_lemma b X hX A hA hsp N hN
  have hRfg : R.FG := Submodule.FG.of_le hdfg hR
  have hRNfg : (dualLat A ⊓ annO N).FG := Submodule.FG.of_le hdfg inf_le_left
  obtain ⟨-, r1, -⟩ := place_lattice_structure K _ ι b.dualBasis (dualFrame X) hX' R hRfg
  obtain ⟨-, r2, -⟩ := place_lattice_structure K _ ι b.dualBasis (dualFrame X) hX' _ hRNfg
  have hrk : Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) R =
      Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N) := by
    calc _ = finrank ℚ K * rkK R := r1
      _ = finrank ℚ K * rkK (dualLat A ⊓ annO N) := by congr 1; omega
      _ = _ := r2.symm
  exact ⟨N, hN, hrk, (hSB'.2.1 R _ hRN inf_le_left).2 hrk⟩

/- English proof (translation)
Establish `hfd : FiniteDimensional K V` using `Module.Finite.of_basis b`. Introduce `h`. Establish `h1` using `rkK_dualLat b A hA hsp`. Rewrite `h1` using `[h]`. Establish `h2 : rkK (⊥ : Submodule (𝓞 K) (Module.Dual K V)) = 0` using `by unfold rkK; simp`.

Establish `hpos : 0 < finrank K V`. Take `⟨x, -, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hA0`. Use `haveI : Nontrivial V := ⟨⟨x, 0, hx0⟩⟩`. Conclude with `Module.finrank_pos`. Use linear arithmetic over natural numbers and integers.
-/
theorem dual_ne_bot (b : Basis ι K V) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) (hA0 : A ≠ ⊥) : dualLat A ≠ ⊥ := by
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  intro h
  have h1 := rkK_dualLat b A hA hsp
  rw [h] at h1
  have h2 : rkK (⊥ : Submodule (𝓞 K) (Module.Dual K V)) = 0 := by unfold rkK; simp
  have hpos : 0 < finrank K V := by
    obtain ⟨x, -, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA0
    haveI : Nontrivial V := ⟨⟨x, 0, hx0⟩⟩
    exact Module.finrank_pos
  omega

/- English proof (translation)
Take `⟨hlat, -, -⟩` from `place_lattice_structure K V ι b X hX A hA`. Establish `hSB` using `saturation_basic_properties (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) A hlat`. Establish `hsat0 : IsSat (Formalism.HermitianLatticesTheory.realize b X) A ⊥` using `hSB.2.2.2.2.2.1`. Take `⟨hdeg0, hrk0⟩` from `deg_R b X hX A hA hsp ⊥ hsat0`. Rewrite `hdeg0`, `hrk0` using `[annO_bot, inf_top_eq]`.

Establish `hdegbot : deg (Formalism.HermitianLatticesTheory.realize b X) (⊥ : Submodule (𝓞 K) V) = 0` using `hSB.2.2.2.2.1`. Establish `hrkbot : Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) (⊥ : Submodule (𝓞 K) V) = 0` using `(hSB.2.2.2.1 ⊥ bot_le).2 rfl`. Establish `hb : (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) (⊥ : Submodule (𝓞 K) V) : ℝ) = 0`. Conclude with `hrkbot` after adjusting the coercions. Establish `hP : (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) : ℝ) = (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) A : ℝ)` using `by linarith`.

Use `⟨?_, hP⟩` and prove the remaining obligations. Establish `e0` using `congrArg (fun t => (Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ)) * t) hP`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem deg_dual (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) :
    deg (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) =
        - deg (Formalism.HermitianLatticesTheory.realize b X) A +
          (Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ)) *
            (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) A : ℝ) ∧
      (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) : ℝ) =
        (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) A : ℝ) := by
  obtain ⟨hlat, -, -⟩ := place_lattice_structure K V ι b X hX A hA
  have hSB := saturation_basic_properties (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) A hlat
  have hsat0 : IsSat (Formalism.HermitianLatticesTheory.realize b X) A ⊥ := hSB.2.2.2.2.2.1
  obtain ⟨hdeg0, hrk0⟩ := deg_R b X hX A hA hsp ⊥ hsat0
  rw [annO_bot, inf_top_eq] at hdeg0 hrk0
  have hdegbot : deg (Formalism.HermitianLatticesTheory.realize b X) (⊥ : Submodule (𝓞 K) V) = 0 := hSB.2.2.2.2.1
  have hrkbot : Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) (⊥ : Submodule (𝓞 K) V) = 0 :=
    (hSB.2.2.2.1 ⊥ bot_le).2 rfl
  have hb : (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) (⊥ : Submodule (𝓞 K) V) : ℝ) = 0 := by
    exact_mod_cast hrkbot
  have hP : (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) : ℝ) =
      (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) A : ℝ) := by linarith
  refine ⟨?_, hP⟩
  have e0 := congrArg (fun t => (Real.log 2 - Real.log |(NumberField.discr K : ℝ)| /
    (finrank ℚ K : ℝ)) * t) hP
  linarith

/- English proof (translation)
Use `set c2 := Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ) with hc2`. Prove the components needed by the constructor for the conclusion. Introduce `H N hN`. Take `⟨N', -, hN', hrk, hdeg⟩` from `sat_exists b X hX A hA N hN`. Take `⟨hd, hr⟩` from `deg_R b X hX A hA hsp N' hN'`.

Establish `h3` using `H (dualLat A ⊓ annO N') inf_le_left`. Establish `hc : (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N' : ℝ) = Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N` using `congrArg Nat.cast hrk`. Establish `e1` using `congrArg (fun t => (c2 - θ) * t) (show (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) A : ℝ) - Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N = Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ …`. Use polynomial arithmetic with `[e1, hd, h3, hdeg]`. Introduce `H R hR`.

Take `⟨N, hN, hrk, hdeg⟩` from `corr_R b X hX A hA hsp R hR`. Take `⟨hd, hr⟩` from `deg_R b X hX A hA hsp N hN`. Establish `h3` using `H N hN.1`. Establish `hx : (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) R : ℝ) = Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N)` using `congrArg Nat.cast hrk`. Establish `e1` using `congrArg (fun t => (c2 - θ) * t) (show (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) A : ℝ) - Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N = Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ …`.

Establish `e2` using `congrArg (fun t => θ * t) hx`. Use polynomial arithmetic with `[e1, e2, hd, h3, hdeg]`.
-/
theorem key_one (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) (θ : ℝ) :
    (∀ R : Submodule (𝓞 K) (Module.Dual K V), R ≤ dualLat A →
        deg (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) R ≤
          θ * Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) R) ↔
      ∀ N : Submodule (𝓞 K) V, N ≤ A →
        ((Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ)) - θ) *
            ((Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) A : ℝ) - Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N) ≤
          deg (Formalism.HermitianLatticesTheory.realize b X) A - deg (Formalism.HermitianLatticesTheory.realize b X) N := by
  set c2 := Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ) with hc2
  constructor
  · intro H N hN
    obtain ⟨N', -, hN', hrk, hdeg⟩ := sat_exists b X hX A hA N hN
    obtain ⟨hd, hr⟩ := deg_R b X hX A hA hsp N' hN'
    have h3 := H (dualLat A ⊓ annO N') inf_le_left
    have hc : (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N' : ℝ) = Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N :=
      congrArg Nat.cast hrk
    have e1 := congrArg (fun t => (c2 - θ) * t)
      (show (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) A : ℝ) - Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N =
        Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N') by
          linarith)
    nlinarith [e1, hd, h3, hdeg]
  · intro H R hR
    obtain ⟨N, hN, hrk, hdeg⟩ := corr_R b X hX A hA hsp R hR
    obtain ⟨hd, hr⟩ := deg_R b X hX A hA hsp N hN
    have h3 := H N hN.1
    have hx : (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) R : ℝ) =
        Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N) :=
      congrArg Nat.cast hrk
    have e1 := congrArg (fun t => (c2 - θ) * t)
      (show (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) A : ℝ) - Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N =
        Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N) by
          linarith)
    have e2 := congrArg (fun t => θ * t) hx
    nlinarith [e1, e2, hd, h3, hdeg]

/- English proof (translation)
Use `set c2 := Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ) with hc2`. Take `⟨hdeg0, hrk0⟩` from `deg_dual b X hX A hA hsp`. Establish `e0` using `congrArg (fun t => c2 * t) hrk0`. Prove the components needed by the constructor for the conclusion. Introduce `H N hN`.

Take `⟨N', -, hN', hrk, hdeg⟩` from `sat_exists b X hX A hA N hN`. Take `⟨hd, hr⟩` from `deg_R b X hX A hA hsp N' hN'`. Establish `h3` using `H (dualLat A ⊓ annO N') inf_le_left`. Establish `hc : (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N' : ℝ) = Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N` using `congrArg Nat.cast hrk`. Establish `e1` using `congrArg (fun t => (c2 - θ) * t) (show (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) : ℝ) - Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N') = Formalism.HN.rk (Formalis …`.

Establish `e2` using `congrArg (fun t => c2 * t) hr`. Establish `e3` using `congrArg (fun t => θ * t) hc`. Use polynomial arithmetic with `[e0, e1, e2, e3, hd, h3, hdeg, hdeg0]`. Introduce `H R hR`. Take `⟨N, hN, hrk, hdeg⟩` from `corr_R b X hX A hA hsp R hR`.

Take `⟨hd, hr⟩` from `deg_R b X hX A hA hsp N hN`. Establish `h3` using `H N hN.1`. Establish `hx : (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) R : ℝ) = Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N)` using `congrArg Nat.cast hrk`. Establish `e1` using `congrArg (fun t => (c2 - θ) * t) (show (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) : ℝ) - Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) R = Formalism.HN.rk (Formalism.HermitianLatticesT …`. Establish `e2` using `congrArg (fun t => c2 * t) hr`.

Use polynomial arithmetic with `[e0, e1, e2, hd, h3, hdeg, hdeg0]`.
-/
theorem key_two (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) (θ : ℝ) :
    (∀ R : Submodule (𝓞 K) (Module.Dual K V), R ≤ dualLat A →
        ((Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ)) - θ) *
            ((Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) : ℝ) -
              Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) R) ≤
          deg (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) -
            deg (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) R) ↔
      ∀ N : Submodule (𝓞 K) V, N ≤ A →
        deg (Formalism.HermitianLatticesTheory.realize b X) N ≤ θ * Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N := by
  set c2 := Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ) with hc2
  obtain ⟨hdeg0, hrk0⟩ := deg_dual b X hX A hA hsp
  have e0 := congrArg (fun t => c2 * t) hrk0
  constructor
  · intro H N hN
    obtain ⟨N', -, hN', hrk, hdeg⟩ := sat_exists b X hX A hA N hN
    obtain ⟨hd, hr⟩ := deg_R b X hX A hA hsp N' hN'
    have h3 := H (dualLat A ⊓ annO N') inf_le_left
    have hc : (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N' : ℝ) = Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N :=
      congrArg Nat.cast hrk
    have e1 := congrArg (fun t => (c2 - θ) * t)
      (show (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) : ℝ) -
          Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N') =
        Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N by linarith)
    have e2 := congrArg (fun t => c2 * t) hr
    have e3 := congrArg (fun t => θ * t) hc
    nlinarith [e0, e1, e2, e3, hd, h3, hdeg, hdeg0]
  · intro H R hR
    obtain ⟨N, hN, hrk, hdeg⟩ := corr_R b X hX A hA hsp R hR
    obtain ⟨hd, hr⟩ := deg_R b X hX A hA hsp N hN
    have h3 := H N hN.1
    have hx : (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) R : ℝ) =
        Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N) :=
      congrArg Nat.cast hrk
    have e1 := congrArg (fun t => (c2 - θ) * t)
      (show (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) : ℝ) -
          Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) R =
        Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N by linarith)
    have e2 := congrArg (fun t => c2 * t) hr
    nlinarith [e0, e1, e2, hd, h3, hdeg, hdeg0]

/- English proof (translation)
Establish `hfd : FiniteDimensional K V` using `Module.Finite.of_basis b`. Establish `hX'` using `dualFrame_unit X hX`. Use `set c2 := Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ) with hc2`. Take `⟨hlat, -, -⟩` from `place_lattice_structure K V ι b X hX A hA`. Establish `hdfg` using `dualLat_fg A hsp`.

Take `⟨hlat', -, -⟩` from `place_lattice_structure K _ ι b.dualBasis (dualFrame X) hX' (dualLat A) hdfg`. Establish `hd0` using `dual_ne_bot b A hA hsp hA0`. Establish `m1` using `slope_characterization (𝓞 K) (Module.Dual K V) _ _ (dualLat A) hlat' hd0`. Establish `m2` using `slope_characterization (𝓞 K) V _ _ A hlat hA0`. Establish `key1 : ∀ θ : ℝ, muMax (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) ≤ θ ↔ c2 - θ ≤ muMin (Formalism.HermitianLatticesTheory.realize b X) A` using `fun θ => (m1.1 θ).trans ((key_one b X hX A hA hsp θ).trans (m2.2.1 (c2 - θ)).symm)`.

Establish `key2 : ∀ θ : ℝ, c2 - θ ≤ muMin (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) ↔ muMax (Formalism.HermitianLatticesTheory.realize b X) A ≤ θ` using `fun θ => (m1.2.1 (c2 - θ)).trans ((key_two b X hX A hA hsp θ).trans (m2.1 θ).symm)`. Use `⟨le_antisymm ((key1 _).2 (by linarith)) ?_, le_antisymm ?_ ((key2 _).2 le_rfl)⟩` and prove the remaining obligations. Use `(key1 (muMax (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A))).1 le_rfl` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `(key2 (c2 - muMin (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A))).1 (by linarith)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem mu_dual (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) (hA0 : A ≠ ⊥) :
    muMax (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) =
        (Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ)) -
          muMin (Formalism.HermitianLatticesTheory.realize b X) A ∧
      muMin (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) =
        (Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ)) -
          muMax (Formalism.HermitianLatticesTheory.realize b X) A := by
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hX' := dualFrame_unit X hX
  set c2 := Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ) with hc2
  obtain ⟨hlat, -, -⟩ := place_lattice_structure K V ι b X hX A hA
  have hdfg := dualLat_fg A hsp
  obtain ⟨hlat', -, -⟩ := place_lattice_structure K _ ι b.dualBasis (dualFrame X) hX' (dualLat A) hdfg
  have hd0 := dual_ne_bot b A hA hsp hA0
  have m1 := slope_characterization (𝓞 K) (Module.Dual K V) _ _ (dualLat A) hlat' hd0
  have m2 := slope_characterization (𝓞 K) V _ _ A hlat hA0
  have key1 : ∀ θ : ℝ, muMax (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) ≤ θ ↔
      c2 - θ ≤ muMin (Formalism.HermitianLatticesTheory.realize b X) A := fun θ =>
    (m1.1 θ).trans ((key_one b X hX A hA hsp θ).trans (m2.2.1 (c2 - θ)).symm)
  have key2 : ∀ θ : ℝ, c2 - θ ≤ muMin (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) ↔
      muMax (Formalism.HermitianLatticesTheory.realize b X) A ≤ θ := fun θ =>
    (m1.2.1 (c2 - θ)).trans ((key_two b X hX A hA hsp θ).trans (m2.1 θ).symm)
  refine ⟨le_antisymm ((key1 _).2 (by linarith)) ?_, le_antisymm ?_ ((key2 _).2 le_rfl)⟩
  · have := (key1 (muMax (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A))).1 le_rfl
    linarith
  · have := (key2 (c2 - muMin (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A))).1
      (by linarith)
    linarith

end HNDual

end Formalism.HN.DualPolygon

namespace Formalism.HN

open DualPolygon

/- English proof (translation)
Introduce `K V ι _ _ _ _ _ _ _ _ _ _ b X hX A hA hsp`. Establish `hfd : FiniteDimensional K V` using `Module.Finite.of_basis b`. Establish `hX'` using `dualFrame_unit X hX`. Establish `hht` using `ht_dual b X hX A hA hsp`. Establish `hpos` using `(place_lattice_structure K V ι b X hX A hA).2.2`.

Establish `hhtinv : ht b.dualBasis (dualFrame X) (dualLat A) = (ht b X A)⁻¹` using `eq_inv_of_mul_eq_one_left hht`. Establish `hrkA : rkK A = finrank K V` using `by unfold rkK; rw [hsp, finrank_top]`. Establish `hrkD` using `rkK_dualLat b A hA hsp`. Establish `hdfg` using `dualLat_fg A hsp`. Establish `hc2 : ∀ m : ℝ, (Real.log 2 / 2 - logDisc K / (2 * (finrank ℚ K : ℝ))) - ((Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ)) - m) = -((Real.log 2 / 2 - logDisc K / (2 * (finrank ℚ K : ℝ))) - m)`.

Introduce `m`. Unfold `logDisc`. Expand and normalize the polynomial expressions, which then agree. Use `⟨hdfg, dualLat_span A hA hsp, hhtinv, ?_, ?_, ?_, dual_dual b X hX A hA hsp⟩` and prove the remaining obligations. Unfold `size`.

Rewrite using `[hhtinv, hrkD, hrkA]`. Conclude with `Real.inv_rpow hpos.le _`. Distinguish the cases in `hA0 : A = ⊥`. Establish `hsub : ∀ x : V, x = 0`. Introduce `x`.

Establish `: x ∈ Submodule.span K (A : Set V)` using `hsp ▸ Submodule.mem_top`. Rewrite `this` using `[hA0]`. Simplify using `using this`. Establish `hdual : ∀ f : Module.Dual K V, f = 0` using `fun f => LinearMap.ext fun x => by rw [hsub x]; simp`. Establish `h1 : leastSize b.dualBasis (dualFrame X) (dualLat A) = 0`.

Unfold `leastSize`. Use `Real.sInf_empty` and compare the differences between its conclusion and the goal. Use extensionality with `t`. Simplify using `only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]`. Introduce and unpack `⟨R, -, hR0, -⟩`.

Conclude with `hR0 (eq_bot_iff.2 fun f _ => (Submodule.mem_bot _).2 (hdual f))`. Establish `h2 : largestSize b X A = 0`. Unfold `largestSize`. Use `Real.sSup_empty` and compare the differences between its conclusion and the goal. Use extensionality with `t`.

Simplify using `only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]`. Introduce and unpack `⟨S, hS, hSA, -⟩`. Conclude with `hSA (le_antisymm hS.1 (by rw [hA0]; exact bot_le))`. Rewrite using `[h1, h2, inv_zero]`. Take `⟨-, -, -, -, hg, -⟩` from `size_maximal_slope K V ι b X hX A hA hA0`.

Take `⟨-, -, -, hl', -, -⟩` from `size_maximal_slope K _ ι b.dualBasis (dualFrame X) hX' (dualLat A) hdfg (dual_ne_bot b A hA hsp hA0)`. Rewrite using `[hl', hg, (mu_dual b X hX A hA hsp hA0).1, ← Real.exp_neg, hc2]`. Distinguish the cases in `hA0 : A = ⊥`. Establish `hsub : ∀ x : V, x = 0`. Introduce `x`.

Establish `: x ∈ Submodule.span K (A : Set V)` using `hsp ▸ Submodule.mem_top`. Rewrite `this` using `[hA0]`. Simplify using `using this`. Establish `hdual : ∀ f : Module.Dual K V, f = 0` using `fun f => LinearMap.ext fun x => by rw [hsub x]; simp`. Establish `hbot : ∀ R : Submodule (𝓞 K) (Module.Dual K V), R = ⊥` using `fun R => eq_bot_iff.2 fun f _ => (Submodule.mem_bot _).2 (hdual f)`.

Establish `h1 : largestSize b.dualBasis (dualFrame X) (dualLat A) = 0`. Unfold `largestSize`. Use `Real.sSup_empty` and compare the differences between its conclusion and the goal. Use extensionality with `t`. Simplify using `only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]`.

Introduce and unpack `⟨S, -, hSA, -⟩`. Conclude with `hSA (by rw [hbot S, hbot (dualLat A)])`. Establish `h2 : leastSize b X A = 0`. Unfold `leastSize`. Use `Real.sInf_empty` and compare the differences between its conclusion and the goal.

Use extensionality with `t`. Simplify using `only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]`. Introduce and unpack `⟨R, hR, hR0, -⟩`. Conclude with `hR0 (le_antisymm (by rw [← hA0]; exact hR) bot_le)`. Rewrite using `[h1, h2, inv_zero]`.

Take `⟨-, -, -, hl, -, -⟩` from `size_maximal_slope K V ι b X hX A hA hA0`. Take `⟨-, -, -, -, hg', -⟩` from `size_maximal_slope K _ ι b.dualBasis (dualFrame X) hX' (dualLat A) hdfg (dual_ne_bot b A hA hsp hA0)`. Rewrite using `[hg', hl, (mu_dual b X hX A hA hsp hA0).2, ← Real.exp_neg, hc2]`.
-/
theorem dual_polygon_identity : DualPl := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX A hA hsp
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hX' := dualFrame_unit X hX
  have hht := ht_dual b X hX A hA hsp
  have hpos := (place_lattice_structure K V ι b X hX A hA).2.2
  have hhtinv : ht b.dualBasis (dualFrame X) (dualLat A) = (ht b X A)⁻¹ :=
    eq_inv_of_mul_eq_one_left hht
  have hrkA : rkK A = finrank K V := by unfold rkK; rw [hsp, finrank_top]
  have hrkD := rkK_dualLat b A hA hsp
  have hdfg := dualLat_fg A hsp
  have hc2 : ∀ m : ℝ, (Real.log 2 / 2 - logDisc K / (2 * (finrank ℚ K : ℝ))) -
      ((Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ)) - m) =
      -((Real.log 2 / 2 - logDisc K / (2 * (finrank ℚ K : ℝ))) - m) := by
    intro m
    unfold logDisc
    ring
  refine ⟨hdfg, dualLat_span A hA hsp, hhtinv, ?_, ?_, ?_, dual_dual b X hX A hA hsp⟩
  · unfold size
    rw [hhtinv, hrkD, hrkA]
    exact Real.inv_rpow hpos.le _
  · by_cases hA0 : A = ⊥
    · have hsub : ∀ x : V, x = 0 := by
        intro x
        have : x ∈ Submodule.span K (A : Set V) := hsp ▸ Submodule.mem_top
        rw [hA0] at this
        simpa using this
      have hdual : ∀ f : Module.Dual K V, f = 0 := fun f =>
        LinearMap.ext fun x => by rw [hsub x]; simp
      have h1 : leastSize b.dualBasis (dualFrame X) (dualLat A) = 0 := by
        unfold leastSize
        convert Real.sInf_empty
        ext t
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨R, -, hR0, -⟩
        exact hR0 (eq_bot_iff.2 fun f _ => (Submodule.mem_bot _).2 (hdual f))
      have h2 : largestSize b X A = 0 := by
        unfold largestSize
        convert Real.sSup_empty
        ext t
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨S, hS, hSA, -⟩
        exact hSA (le_antisymm hS.1 (by rw [hA0]; exact bot_le))
      rw [h1, h2, inv_zero]
    · obtain ⟨-, -, -, -, hg, -⟩ := size_maximal_slope K V ι b X hX A hA hA0
      obtain ⟨-, -, -, hl', -, -⟩ := size_maximal_slope K _ ι b.dualBasis (dualFrame X) hX'
        (dualLat A) hdfg (dual_ne_bot b A hA hsp hA0)
      rw [hl', hg, (mu_dual b X hX A hA hsp hA0).1, ← Real.exp_neg, hc2]
  · by_cases hA0 : A = ⊥
    · have hsub : ∀ x : V, x = 0 := by
        intro x
        have : x ∈ Submodule.span K (A : Set V) := hsp ▸ Submodule.mem_top
        rw [hA0] at this
        simpa using this
      have hdual : ∀ f : Module.Dual K V, f = 0 := fun f =>
        LinearMap.ext fun x => by rw [hsub x]; simp
      have hbot : ∀ R : Submodule (𝓞 K) (Module.Dual K V), R = ⊥ := fun R =>
        eq_bot_iff.2 fun f _ => (Submodule.mem_bot _).2 (hdual f)
      have h1 : largestSize b.dualBasis (dualFrame X) (dualLat A) = 0 := by
        unfold largestSize
        convert Real.sSup_empty
        ext t
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨S, -, hSA, -⟩
        exact hSA (by rw [hbot S, hbot (dualLat A)])
      have h2 : leastSize b X A = 0 := by
        unfold leastSize
        convert Real.sInf_empty
        ext t
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨R, hR, hR0, -⟩
        exact hR0 (le_antisymm (by rw [← hA0]; exact hR) bot_le)
      rw [h1, h2, inv_zero]
    · obtain ⟨-, -, -, hl, -, -⟩ := size_maximal_slope K V ι b X hX A hA hA0
      obtain ⟨-, -, -, -, hg', -⟩ := size_maximal_slope K _ ι b.dualBasis (dualFrame X) hX'
        (dualLat A) hdfg (dual_ne_bot b A hA hsp hA0)
      rw [hg', hl, (mu_dual b X hX A hA hsp hA0).2, ← Real.exp_neg, hc2]

end Formalism.HN
