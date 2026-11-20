import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueFieldMapPtCoordSndM
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiprojectivePrimeEqPointIdeal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageInverse
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointIdealMultiprojectivePrime

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog geoNum charOf mCoordIdeal mConeMap)
open GlobalTheory.CompanionTheory.MPDict

namespace GlobalTheory.CompanionTheory.MixZ.PtLenProof

section Top

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hne' : closure ({z} : Set Y) ≠ {z}` using `fun e => hne (e ▸ isClosed_closure)`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy, hyz⟩ : ∃ y ∈ closure ({z} : Set Y), y ≠ z := by`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`.

Conclude with `hne' (Set.Subset.antisymm (fun y hy => hall y hy) subset_closure)`. Set `T` to `closure ({z} : Set Y)`. Set `z' : T` to `⟨z, subset_closure rfl⟩`. Set `y' : T` to `⟨y, hy⟩`. Establish `hzy : z' ⤳ y'` using `(subtype_specializes_iff _ _).2 (specializes_iff_mem_closure.2 hy)`.

Set `A : IrreducibleCloseds T` to `⟨closure {y'}, isIrreducible_singleton.closure, isClosed_closure⟩`. Set `B : IrreducibleCloseds T` to `⟨closure {z'}, isIrreducible_singleton.closure, isClosed_closure⟩`. Establish `hAB : A < B`. Use `lt_of_le_of_ne (fun w hw => ?_) fun e => hyz ?_` and prove the remaining obligations. Conclude with `closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hzy)) isClosed_closure hw`.

Establish `h1 : z' ∈ closure ({y'} : Set T)`. Establish `: (B : Set T) = A` using `congrArg (fun C : IrreducibleCloseds T => (C : Set T)) e.symm`. Establish `h2 : z' ∈ (B : Set T)` using `subset_closure rfl`. Rewrite `h2` using `[this]`. Then use the resulting hypothesis. Establish `h3 : y' ⤳ z'` using `specializes_iff_mem_closure.2 h1`.

Conclude with `congrArg Subtype.val (h3.antisymm hzy).eq`. Establish `h0 : Order.krullDim (IrreducibleCloseds T) ≤ 0`. Establish `: topologicalKrullDim T = Order.krullDim (IrreducibleCloseds T)` using `rfl`. Rewrite using `[← this, h]`. Both sides reduce to the same expression.

Conclude with `(Order.krullDim_nonpos_iff_forall_isMax.1 h0 A).not_lt hAB`.
-/
theorem isClosed_singleton_of_dim_closure {Y : Type*} [TopologicalSpace Y] [T0Space Y] (z : Y)
    (h : topologicalKrullDim (closure ({z} : Set Y)) = (0 : ℕ)) : IsClosed ({z} : Set Y) := by
  by_contra hne
  have hne' : closure ({z} : Set Y) ≠ {z} := fun e => hne (e ▸ isClosed_closure)
  obtain ⟨y, hy, hyz⟩ : ∃ y ∈ closure ({z} : Set Y), y ≠ z := by
    by_contra hall
    push_neg at hall
    exact hne' (Set.Subset.antisymm (fun y hy => hall y hy) subset_closure)
  let T := closure ({z} : Set Y)
  let z' : T := ⟨z, subset_closure rfl⟩
  let y' : T := ⟨y, hy⟩
  have hzy : z' ⤳ y' := (subtype_specializes_iff _ _).2 (specializes_iff_mem_closure.2 hy)
  let A : IrreducibleCloseds T := ⟨closure {y'}, isIrreducible_singleton.closure, isClosed_closure⟩
  let B : IrreducibleCloseds T := ⟨closure {z'}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hAB : A < B := by
    refine lt_of_le_of_ne (fun w hw => ?_) fun e => hyz ?_
    · exact closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hzy)) isClosed_closure hw
    · have h1 : z' ∈ closure ({y'} : Set T) := by
        have : (B : Set T) = A := congrArg (fun C : IrreducibleCloseds T => (C : Set T)) e.symm
        have h2 : z' ∈ (B : Set T) := subset_closure rfl
        rwa [this] at h2
      have h3 : y' ⤳ z' := specializes_iff_mem_closure.2 h1
      exact congrArg Subtype.val (h3.antisymm hzy).eq
  have h0 : Order.krullDim (IrreducibleCloseds T) ≤ 0 := by
    have : topologicalKrullDim T = Order.krullDim (IrreducibleCloseds T) := rfl
    rw [← this, h]
    rfl
  exact (Order.krullDim_nonpos_iff_forall_isMax.1 h0 A).not_lt hAB

end Top

section Homog

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Introduce `m hm` and use `by classical rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h exacts [hf m h, hg m h]`.
-/
theorem isMultiHomog_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := fun m hm => by
  classical
  rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
  exacts [hf m h, hg m h]

/- English proof (translation)
Introduce `m hm k` and use `by classical obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul f g hm) simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf u hu k, hg v hv k]`.
-/
theorem isMultiHomog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := fun m hm k => by
  classical
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf u hu k, hg v hv k]

/- English proof (translation)
Introduce `m hm k` and use `by classical have hm0 : m = 0 := by by_contra h exact (MvPolynomial.mem_support_iff.1 hm) (by rw [coeff_C, if_neg (Ne.symm h)]) simp [hm0]`.
-/
theorem isMultiHomog_C (c : ℤ) : IsMultiHomog (C c : MRing ι) 0 := fun m hm k => by
  classical
  have hm0 : m = 0 := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.1 hm) (by rw [coeff_C, if_neg (Ne.symm h)])
  simp [hm0]

open Classical in
/- English proof (translation)
Introduce `m hm k` and use `by classical rw [X, support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hm subst hm obtain ⟨l, i⟩ := p by_cases hk : k = l · subst hk simp [Finsupp.single_apply] · have : ∀ j : ι k, (Finsupp.single (⟨l, i⟩ : Σ k, ι k) 1) ⟨k, j⟩ = 0 := fun j => by rw [Finsupp.single_app …`.
-/
theorem isMultiHomog_X (p : Σ k, ι k) : IsMultiHomog (X p : MRing ι) (Pi.single p.1 1) := fun m hm k => by
  classical
  rw [X, support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hm
  subst hm
  obtain ⟨l, i⟩ := p
  by_cases hk : k = l
  · subst hk
    simp [Finsupp.single_apply]
  · have : ∀ j : ι k, (Finsupp.single (⟨l, i⟩ : Σ k, ι k) 1) ⟨k, j⟩ = 0 := fun j => by
      rw [Finsupp.single_apply, if_neg]
      intro e
      exact hk (congrArg Sigma.fst e).symm
    simp [this, Pi.single_apply, hk]

/- English proof (translation)
Proceed by induction on `e with`. Consider the case `zero => simpa using isMultiHomog_C (ι := ι) 1`. Consider the case `succ e ih`. Rewrite using `[pow_succ, succ_nsmul]`. Conclude with `isMultiHomog_mul ih hf`.
-/
theorem isMultiHomog_pow {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (e : ℕ) :
    IsMultiHomog (f ^ e) (e • a) := by
  induction e with
  | zero => simpa using isMultiHomog_C (ι := ι) 1
  | succ e ih =>
    rw [pow_succ, succ_nsmul]
    exact isMultiHomog_mul ih hf

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using isMultiHomog_C (ι := ι) 1`. Consider the case `insert o s ho ih`. Rewrite using `[Finset.prod_insert ho, Finset.sum_insert ho]`. Conclude with `isMultiHomog_mul (h o (Finset.mem_insert_self o s)) (ih fun o' ho' => h o' (Finset.mem_insert_of_mem ho'))`.
-/
theorem isMultiHomog_prod {α : Type} (s : Finset α) (f : α → MRing ι) (a : α → K → ℕ)
    (h : ∀ o ∈ s, IsMultiHomog (f o) (a o)) : IsMultiHomog (∏ o ∈ s, f o) (∑ o ∈ s, a o) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isMultiHomog_C (ι := ι) 1
  | insert o s ho ih =>
    rw [Finset.prod_insert ho, Finset.sum_insert ho]
    exact isMultiHomog_mul (h o (Finset.mem_insert_self o s))
      (ih fun o' ho' => h o' (Finset.mem_insert_of_mem ho'))

abbrev chartI (c : ∀ k, ι k) : Ideal (MRing ι) := Ideal.span (Set.range fun k => (X ⟨k, c k⟩ : MRing ι) - 1)

/- English proof (translation)
The claim follows from `Ideal.subset_span ⟨k, rfl⟩`.
-/
theorem sub_one_mem_chartI (c : ∀ k, ι k) (k : K) : (X ⟨k, c k⟩ : MRing ι) - 1 ∈ chartI c :=
  Ideal.subset_span ⟨k, rfl⟩

/- English proof (translation)
Rewrite using `[← Ideal.Quotient.eq, map_prod, map_one]`. Use `Finset.prod_eq_one fun k _ => ?_` and prove the remaining obligations. Establish `: Ideal.Quotient.mk (chartI c) (X ⟨k, c k⟩) = 1`. Rewrite using `[← map_one (Ideal.Quotient.mk (chartI c)), Ideal.Quotient.eq]`. Conclude with `sub_one_mem_chartI c k`.

Rewrite using `[map_pow, this, one_pow]`.
-/
theorem mono_sub_one_mem (c : ∀ k, ι k) (E : K → ℕ) : (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ E k) - 1 ∈ chartI c := by
  rw [← Ideal.Quotient.eq, map_prod, map_one]
  refine Finset.prod_eq_one fun k _ => ?_
  have : Ideal.Quotient.mk (chartI c) (X ⟨k, c k⟩) = 1 := by
    rw [← map_one (Ideal.Quotient.mk (chartI c)), Ideal.Quotient.eq]
    exact sub_one_mem_chartI c k
  rw [map_pow, this, one_pow]

/- English proof (translation)
Establish `h` using `isMultiHomog_prod (ι := ι) Finset.univ (fun k => (X ⟨k, c k⟩ : MRing ι) ^ E k) (fun k => E k • Pi.single k 1) fun k _ => isMultiHomog_pow (isMultiHomog_X ⟨k, c k⟩) (E k)`. Establish `e : (∑ k, E k • (Pi.single k 1 : K → ℕ)) = E`. Use function extensionality and compare the values at `l`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Rewrite `h` using `[e]`. Then use the resulting hypothesis.
-/
theorem isMultiHomog_mono (c : ∀ k, ι k) (E : K → ℕ) : IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ E k) E := by
  classical
  have h := isMultiHomog_prod (ι := ι) Finset.univ (fun k => (X ⟨k, c k⟩ : MRing ι) ^ E k)
    (fun k => E k • Pi.single k 1) fun k _ => isMultiHomog_pow (isMultiHomog_X ⟨k, c k⟩) (E k)
  have e : (∑ k, E k • (Pi.single k 1 : K → ℕ)) = E := by
    funext l
    simp [Finset.sum_apply, Pi.single_apply]
  rwa [e] at h

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a`. Use `⟨0, fun E _ => ⟨C a * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ E k, ?_, ?_⟩⟩` and prove the remaining obligations. Simplify using `using isMultiHomog_mul (isMultiHomog_C a) (isMultiHomog_mono c E)`. Establish `: (C a : MRing ι) - C a * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ E k = -(C a * ((∏ k, (X ⟨k, c k⟩ : MRing ι) ^ E k) - 1))` using `by ring`.

Rewrite using `[this]`. Conclude with `neg_mem (Ideal.mul_mem_left _ _ (mono_sub_one_mem c E))`. Consider the case `add f g hf hg`. Take `⟨D₁, h₁⟩` from `hf`. Take `⟨D₂, h₂⟩` from `hg`.

Use `⟨D₁ ⊔ D₂, fun E hE => ?_⟩` and prove the remaining obligations. Take `⟨u, hu, hu'⟩` from `h₁ E (le_sup_left.trans hE)`. Take `⟨v, hv, hv'⟩` from `h₂ E (le_sup_right.trans hE)`. Use `⟨u + v, isMultiHomog_add hu hv, ?_⟩` and prove the remaining obligations. Establish `: f + g - (u + v) = (f - u) + (g - v)` using `by ring`.

Rewrite using `[this]`. Conclude with `add_mem hu' hv'`. Consider the case `mul_X f p hf`. Take `⟨D, h⟩` from `hf`. Use `⟨D + Pi.single p.1 1, fun E hE => ?_⟩` and prove the remaining obligations.

Establish `hle : D ≤ E - Pi.single p.1 1` using `fun k => by`. Use `hE k` as an intermediate fact. Simplify using `only [Pi.add_apply, Pi.sub_apply] at this ⊢`. Use linear arithmetic over natural numbers and integers. Take `⟨u, hu, hu'⟩` from `h _ hle`.

Establish `hE' : E - Pi.single p.1 1 + Pi.single p.1 1 = E`. Use function extensionality and compare the values at `k`. Use `hE k` as an intermediate fact. Simplify using `only [Pi.add_apply, Pi.sub_apply] at this ⊢`. Use linear arithmetic over natural numbers and integers.

Use `⟨u * X p, ?_, ?_⟩` and prove the remaining obligations. Use `isMultiHomog_mul hu (isMultiHomog_X p)` as an intermediate fact. Rewrite `this` using `[hE']`. Then use the resulting hypothesis. Establish `: f * X p - u * X p = (f - u) * X p` using `by ring`. Rewrite using `[this]`.

Conclude with `Ideal.mul_mem_right _ _ hu'`.
-/
theorem exists_homog (c : ∀ k, ι k) (f : MRing ι) :
    ∃ D : K → ℕ, ∀ E : K → ℕ, D ≤ E → ∃ g, IsMultiHomog g E ∧ f - g ∈ chartI c := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, fun E _ => ⟨C a * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ E k, ?_, ?_⟩⟩
    · simpa using isMultiHomog_mul (isMultiHomog_C a) (isMultiHomog_mono c E)
    · have : (C a : MRing ι) - C a * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ E k =
          -(C a * ((∏ k, (X ⟨k, c k⟩ : MRing ι) ^ E k) - 1)) := by ring
      rw [this]
      exact neg_mem (Ideal.mul_mem_left _ _ (mono_sub_one_mem c E))
  | add f g hf hg =>
    obtain ⟨D₁, h₁⟩ := hf
    obtain ⟨D₂, h₂⟩ := hg
    refine ⟨D₁ ⊔ D₂, fun E hE => ?_⟩
    obtain ⟨u, hu, hu'⟩ := h₁ E (le_sup_left.trans hE)
    obtain ⟨v, hv, hv'⟩ := h₂ E (le_sup_right.trans hE)
    refine ⟨u + v, isMultiHomog_add hu hv, ?_⟩
    have : f + g - (u + v) = (f - u) + (g - v) := by ring
    rw [this]
    exact add_mem hu' hv'
  | mul_X f p hf =>
    obtain ⟨D, h⟩ := hf
    refine ⟨D + Pi.single p.1 1, fun E hE => ?_⟩
    have hle : D ≤ E - Pi.single p.1 1 := fun k => by
      have := hE k
      simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
      omega
    obtain ⟨u, hu, hu'⟩ := h _ hle
    have hE' : E - Pi.single p.1 1 + Pi.single p.1 1 = E := by
      funext k
      have := hE k
      simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
      omega
    refine ⟨u * X p, ?_, ?_⟩
    · have := isMultiHomog_mul hu (isMultiHomog_X p)
      rwa [hE'] at this
    · have : f * X p - u * X p = (f - u) * X p := by ring
      rw [this]
      exact Ideal.mul_mem_right _ _ hu'

end Homog

section Chart

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

abbrev ratioCoord (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : (Σ k, ι k) → Ω := fun p => (y ⟨p.1, c p.1⟩)⁻¹ * y p

abbrev chartMap (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : MRing ι →ₐ[ℤ] Ω := aeval (ratioCoord y c)

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.MPDict.Onto.mCoordIdeal_blockScale (fun k => (y ⟨k, c k⟩)⁻¹) (fun k => inv_ne_zero (hc k)) y`.
-/
theorem mCoordIdeal_ratioCoord (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    mCoordIdeal (ratioCoord y c) = mCoordIdeal y :=
  GlobalTheory.CompanionTheory.MPDict.Onto.mCoordIdeal_blockScale (fun k => (y ⟨k, c k⟩)⁻¹) (fun k => inv_ne_zero (hc k)) y

/- English proof (translation)
Introduce `f hf`. Establish `hf' : mConeMap w f = 0` using `hf`. Establish `key : (aeval (fun _ : K => (1 : Ω)) : MvPolynomial K Ω →ₐ[Ω] Ω).toRingHom.comp (mConeMap w).toRingHom = (aeval w : MRing ι →ₐ[ℤ] Ω).toRingHom`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`.

Simplify using the standard rewrite rules. Introduce `p`. Simplify using `[mConeMap]`. Use `congrArg (fun φ : MRing ι →+* Ω => φ f) key` as an intermediate fact. Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hf', map_zero] at this`.

Conclude with `this.symm`.
-/
theorem mCoordIdeal_le_ker (w : (Σ k, ι k) → Ω) :
    mCoordIdeal w ≤ RingHom.ker (aeval w : MRing ι →ₐ[ℤ] Ω) := by
  intro f hf
  have hf' : mConeMap w f = 0 := hf
  have key : (aeval (fun _ : K => (1 : Ω)) : MvPolynomial K Ω →ₐ[Ω] Ω).toRingHom.comp (mConeMap w).toRingHom =
      (aeval w : MRing ι →ₐ[ℤ] Ω).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro p
      simp [mConeMap]
  have := congrArg (fun φ : MRing ι →+* Ω => φ f) key
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hf', map_zero] at this
  exact this.symm

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `f hf`. Take `⟨D, hD⟩` from `exists_homog c f`. Take `⟨g, hg, hfg⟩` from `hD D le_rfl`. Establish `hJ : chartI c ≤ RingHom.ker (chartMap y c)`.

Use `Ideal.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Simplify using `[RingHom.mem_ker, inv_mul_cancel₀ (hc k)]`. Establish `hg0 : aeval (ratioCoord y c) g = 0`. Establish `h1 : chartMap y c (f - g) = 0` using `hJ hfg`.

Establish `h2 : chartMap y c f = 0` using `hf`. Rewrite `h1` using `[map_sub, h2, zero_sub, neg_eq_zero]`. Conclude with `h1`. Establish `hgW : g ∈ mCoordIdeal y`. Rewrite using `[← mCoordIdeal_ratioCoord y c hc]`.

Conclude with `(GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageInverse.mem_mCoordIdeal_iff _ hg).2 hg0`. Establish `: f = g + (f - g)` using `by ring`. Rewrite using `[this]`. Conclude with `add_mem (Ideal.mem_sup_left hgW) (Ideal.mem_sup_right hfg)`. Use `sup_le ?_ ?_` and prove the remaining obligations.

Rewrite using `[← mCoordIdeal_ratioCoord y c hc]`. Conclude with `mCoordIdeal_le_ker _`. Use `Ideal.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Simplify using `[RingHom.mem_ker, inv_mul_cancel₀ (hc k)]`.
-/
theorem ker_chartMap (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    RingHom.ker (chartMap y c) = mCoordIdeal y ⊔ chartI c := by
  apply le_antisymm
  · intro f hf
    obtain ⟨D, hD⟩ := exists_homog c f
    obtain ⟨g, hg, hfg⟩ := hD D le_rfl
    have hJ : chartI c ≤ RingHom.ker (chartMap y c) := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      simp [RingHom.mem_ker, inv_mul_cancel₀ (hc k)]
    have hg0 : aeval (ratioCoord y c) g = 0 := by
      have h1 : chartMap y c (f - g) = 0 := hJ hfg
      have h2 : chartMap y c f = 0 := hf
      rw [map_sub, h2, zero_sub, neg_eq_zero] at h1
      exact h1
    have hgW : g ∈ mCoordIdeal y := by
      rw [← mCoordIdeal_ratioCoord y c hc]
      exact (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageInverse.mem_mCoordIdeal_iff _ hg).2 hg0
    have : f = g + (f - g) := by ring
    rw [this]
    exact add_mem (Ideal.mem_sup_left hgW) (Ideal.mem_sup_right hfg)
  · refine sup_le ?_ ?_
    · rw [← mCoordIdeal_ratioCoord y c hc]
      exact mCoordIdeal_le_ker _
    · refine Ideal.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      simp [RingHom.mem_ker, inv_mul_cancel₀ (hc k)]

/- English proof (translation)
Set `S : Subring Ω` to `(chartMap y c).range.toSubring`. Establish `hinv : ∀ x ∈ S, x⁻¹ ∈ S`. Introduce `x hx`. Distinguish the cases in `h0 : x = 0`. Simplify `S.zero_mem` using `[h0]`.

Establish `hu` using `pow_card_eq_one' (x := Units.mk0 x h0)`. Establish `hN : 0 < Nat.card Ωˣ` using `Nat.card_pos`. Establish `e : x * x ^ (Nat.card Ωˣ - 1) = 1`. Rewrite using `[← pow_succ', Nat.sub_add_cancel hN]`. Establish `hu' : ((Units.mk0 x h0 ^ Nat.card Ωˣ : Ωˣ) : Ω) = 1` using `by rw [hu]; rfl`.

Rewrite `hu'` using `[Units.val_pow_eq_pow_val]`. Conclude with `hu'`. Rewrite using `[inv_eq_of_mul_eq_one_right e]`. Conclude with `S.pow_mem hx _`. Set `F : Subfield Ω` to `{ S with inv_mem' := hinv }`.

Establish `hmem : ∀ p, ratioCoord y c p ∈ F` using `fun p => ⟨X p, by simp⟩`. Establish `hyF : ∀ p, y p ∈ F`. Introduce `p`. Establish `e : y p = ratioCoord y c p * (ratioCoord y c ⟨p.1, c₀ p.1⟩)⁻¹`. Simplify using `only [ratioCoord, h₁, mul_one, mul_inv, inv_inv]`.

Clear denominators, using `[hc p.1]` for the nonvanishing conditions. Rewrite using `[e]`. Conclude with `F.mul_mem (hmem p) (F.inv_mem (hmem _))`. Establish `hF : F = ⊤`. Rewrite using `[eq_top_iff, ← hy]`.

Conclude with `Subfield.closure_le.2 (by rintro _ ⟨p, rfl⟩; exact hyF p)`. Introduce `a`. Establish `: a ∈ F` using `hF ▸ Subfield.mem_top a`. Conclude with `this`.
-/
theorem chartMap_surjective [Finite Ω] (y : (Σ k, ι k) → Ω) (c c₀ : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (h₁ : ∀ k, y ⟨k, c₀ k⟩ = 1) (hy : Subfield.closure (Set.range y) = ⊤) :
    Function.Surjective (chartMap y c) := by
  let S : Subring Ω := (chartMap y c).range.toSubring
  have hinv : ∀ x ∈ S, x⁻¹ ∈ S := by
    intro x hx
    by_cases h0 : x = 0
    · simpa [h0] using S.zero_mem
    · have hu := pow_card_eq_one' (x := Units.mk0 x h0)
      have hN : 0 < Nat.card Ωˣ := Nat.card_pos
      have e : x * x ^ (Nat.card Ωˣ - 1) = 1 := by
        rw [← pow_succ', Nat.sub_add_cancel hN]
        have hu' : ((Units.mk0 x h0 ^ Nat.card Ωˣ : Ωˣ) : Ω) = 1 := by rw [hu]; rfl
        rw [Units.val_pow_eq_pow_val] at hu'
        exact hu'
      rw [inv_eq_of_mul_eq_one_right e]
      exact S.pow_mem hx _
  let F : Subfield Ω := { S with inv_mem' := hinv }
  have hmem : ∀ p, ratioCoord y c p ∈ F := fun p => ⟨X p, by simp⟩
  have hyF : ∀ p, y p ∈ F := by
    intro p
    have e : y p = ratioCoord y c p * (ratioCoord y c ⟨p.1, c₀ p.1⟩)⁻¹ := by
      simp only [ratioCoord, h₁, mul_one, mul_inv, inv_inv]
      field_simp [hc p.1]
    rw [e]
    exact F.mul_mem (hmem p) (F.inv_mem (hmem _))
  have hF : F = ⊤ := by
    rw [eq_top_iff, ← hy]
    exact Subfield.closure_le.2 (by rintro _ ⟨p, rfl⟩; exact hyF p)
  intro a
  have : a ∈ F := hF ▸ Subfield.mem_top a
  exact this

/- English proof (translation)
Set `E : (MRing ι ⧸ (mCoordIdeal y ⊔ chartI c)) ≃+* Ω` to `(Ideal.quotEquivOfEq (ker_chartMap y c hc).symm).trans (RingHom.quotientKerEquivOfSurjective (f := (chartMap y c).toRingHom) (chartMap_surjective y c c₀ hc h₁ hy))`. Use `letI := ZMod.algebra Ω p`. Establish `hZ : Function.Surjective (algebraMap ℤ (ZMod p))`. Rewrite using `[algebraMap_int_eq]`. Conclude with `ZMod.ringHom_surjective _`.

Use `haveI : Module.Finite (ZMod p) Ω := Module.Finite.of_finite`. Rewrite using `[E.toIntAlgEquiv.toLinearEquiv.length_eq, Module.length_eq_of_surjective hZ, Module.length_eq_rank, Cardinal.toNat_toENat]`. Establish `hcard : Nat.card Ω = p ^ Module.finrank (ZMod p) Ω`. Rewrite using `[Module.natCard_eq_pow_finrank (K := ZMod p) (V := Ω), Nat.card_zmod]`. Rewrite using `[hcard]`.

Use `push_cast`. Rewrite using `[Real.log_pow]`. Both sides reduce to the same expression.
-/
theorem length_mul_log [Finite Ω] (y : (Σ k, ι k) → Ω) (c c₀ : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (h₁ : ∀ k, y ⟨k, c₀ k⟩ = 1) (hy : Subfield.closure (Set.range y) = ⊤) (p : ℕ) [hp : Fact p.Prime] [CharP Ω p] :
    (((Module.length ℤ (MRing ι ⧸ (mCoordIdeal y ⊔ chartI c))).toNat : ℤ) : ℝ) * Real.log p =
      Real.log (Nat.card Ω) := by
  let E : (MRing ι ⧸ (mCoordIdeal y ⊔ chartI c)) ≃+* Ω :=
    (Ideal.quotEquivOfEq (ker_chartMap y c hc).symm).trans
      (RingHom.quotientKerEquivOfSurjective (f := (chartMap y c).toRingHom) (chartMap_surjective y c c₀ hc h₁ hy))
  letI := ZMod.algebra Ω p
  have hZ : Function.Surjective (algebraMap ℤ (ZMod p)) := by
    rw [algebraMap_int_eq]
    exact ZMod.ringHom_surjective _
  haveI : Module.Finite (ZMod p) Ω := Module.Finite.of_finite
  rw [E.toIntAlgEquiv.toLinearEquiv.length_eq, Module.length_eq_of_surjective hZ, Module.length_eq_rank,
    Cardinal.toNat_toENat]
  have hcard : Nat.card Ω = p ^ Module.finrank (ZMod p) Ω := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := Ω), Nat.card_zmod]
  rw [hcard]
  push_cast
  rw [Real.log_pow]
  rfl

end Chart

/- English proof (translation)
Establish `hc : (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = Ideal.span {(p : ℤ)}`. Use extensionality with `a`. Rewrite using `[Ideal.mem_comap, Ideal.mem_span_singleton, ← CharP.intCast_eq_zero_iff Ω p]`. Express the relevant statement in the definitionally equal form `mConeMap y (C a) = 0 ↔ _`. Establish `: mConeMap y (C a) = C (a : Ω)`.

Simplify using `[mConeMap, MvPolynomial.algebraMap_eq]`. Rewrite using `[this, MvPolynomial.C_eq_zero]`. Use `Submodule.IsPrincipal.span_singleton_generator ((mCoordIdeal y).comap (C : ℤ →+* MRing ι))` as an intermediate fact. Rewrite using `[charOf]`. Establish `h2 : Ideal.span {Submodule.IsPrincipal.generator ((mCoordIdeal y).comap (C : ℤ →+* MRing ι))} = Ideal.span {(p : ℤ)}` using `this.trans hc`.

Establish `h3` using `Ideal.span_singleton_eq_span_singleton.1 h2`. Conclude with `(Int.associated_iff_natAbs.1 h3).trans (by simp)`.
-/
theorem charOf_mCoordIdeal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) (p : ℕ) [CharP Ω p] : charOf (mCoordIdeal y) = p := by
  have hc : (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = Ideal.span {(p : ℤ)} := by
    ext a
    rw [Ideal.mem_comap, Ideal.mem_span_singleton, ← CharP.intCast_eq_zero_iff Ω p]
    change mConeMap y (C a) = 0 ↔ _
    have : mConeMap y (C a) = C (a : Ω) := by
      simp [mConeMap, MvPolynomial.algebraMap_eq]
    rw [this, MvPolynomial.C_eq_zero]
  have := Submodule.IsPrincipal.span_singleton_generator ((mCoordIdeal y).comap (C : ℤ →+* MRing ι))
  rw [charOf]
  have h2 : Ideal.span {Submodule.IsPrincipal.generator ((mCoordIdeal y).comap (C : ℤ →+* MRing ι))} =
      Ideal.span {(p : ℤ)} := this.trans hc
  have h3 := Ideal.span_singleton_eq_span_singleton.1 h2
  exact (Int.associated_iff_natAbs.1 h3).trans (by simp)

/- English proof (translation)
Introduce `m n X i _ z hz a`. Establish `hzc : IsClosed ({z} : Set X)` using `isClosed_singleton_of_dim_closure z hz`. Establish `hxc : IsClosed ({i z} : Set (MP ℤ m n))`. Use `i.isClosedEmbedding.isClosedMap _ hzc` as an intermediate fact. Simplify using `using this`.

Use `haveI : Finite ((MP ℤ m n).residueField (i z)) := GlobalTheory.finite_residueField_of_isClosed_of_locallyOfFiniteType_int (mpStr ℤ m n) (i z) hxc`. Establish `hcard : Nat.card (X.residueField z) = Nat.card ((MP ℤ m n).residueField (i z))`. Establish `hs : Function.Surjective (i.residueFieldMap z).hom`. Introduce `b`. Take `⟨b', rfl⟩` from `IsLocalRing.residue_surjective b`.

Take `⟨c, rfl⟩` from `i.stalkMap_surjective z b'`. Conclude with `⟨IsLocalRing.residue _ c, rfl⟩`. Conclude with `(Nat.card_congr (Equiv.ofBijective _ ⟨(i.residueFieldMap z).hom.injective, hs⟩)).symm`. Take `⟨p, hp⟩` from `CharP.exists ((MP ℤ m n).residueField (i z))`. Use `haveI : Fact p.Prime := ⟨CharP.char_is_prime ((MP ℤ m n).residueField (i z)) p⟩`.

Establish `hrel` using `(isMultiProjPrime_ptIdeal m n (i z)).2.2`. Establish `hy0 : ∀ k, ptCoord (i z) ⟨k, (hrel k).choose⟩ ≠ 0`. Introduce `k h0`. Use `(hrel k).choose_spec ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `mConeMap _ _ = 0`.

Simplify using `[mConeMap, h0]`. Rewrite using `[hcard, show charOf (ptIdeal (i z)) = p from charOf_mCoordIdeal (ptCoord (i z)) p, geoNum, dif_pos hrel]`. Conclude with `length_mul_log (ptCoord (i z)) (fun k => (hrel k).choose) (ptChart (i z)) hy0 (ptCoord_ptChart (i z)) (GlobalTheory.CompanionTheory.MPDict.FnDeg.closure_ptCoord m n (i z)) p`.
-/
theorem ptLen : GlobalTheory.CompanionTheory.MixZ.PtLen := by
  intro m n X i _ z hz a
  have hzc : IsClosed ({z} : Set X) := isClosed_singleton_of_dim_closure z hz
  have hxc : IsClosed ({i z} : Set (MP ℤ m n)) := by
    have := i.isClosedEmbedding.isClosedMap _ hzc
    simpa using this
  haveI : Finite ((MP ℤ m n).residueField (i z)) :=
    GlobalTheory.finite_residueField_of_isClosed_of_locallyOfFiniteType_int (mpStr ℤ m n) (i z) hxc
  have hcard : Nat.card (X.residueField z) = Nat.card ((MP ℤ m n).residueField (i z)) := by
    have hs : Function.Surjective (i.residueFieldMap z).hom := by
      intro b
      obtain ⟨b', rfl⟩ := IsLocalRing.residue_surjective b
      obtain ⟨c, rfl⟩ := i.stalkMap_surjective z b'
      exact ⟨IsLocalRing.residue _ c, rfl⟩
    exact (Nat.card_congr (Equiv.ofBijective _ ⟨(i.residueFieldMap z).hom.injective, hs⟩)).symm
  obtain ⟨p, hp⟩ := CharP.exists ((MP ℤ m n).residueField (i z))
  haveI : Fact p.Prime := ⟨CharP.char_is_prime ((MP ℤ m n).residueField (i z)) p⟩
  have hrel := (isMultiProjPrime_ptIdeal m n (i z)).2.2
  have hy0 : ∀ k, ptCoord (i z) ⟨k, (hrel k).choose⟩ ≠ 0 := by
    intro k h0
    refine (hrel k).choose_spec ?_
    change mConeMap _ _ = 0
    simp [mConeMap, h0]
  rw [hcard, show charOf (ptIdeal (i z)) = p from charOf_mCoordIdeal (ptCoord (i z)) p, geoNum, dif_pos hrel]
  exact length_mul_log (ptCoord (i z)) (fun k => (hrel k).choose) (ptChart (i z)) hy0
    (ptCoord_ptChart (i z)) (GlobalTheory.CompanionTheory.MPDict.FnDeg.closure_ptCoord m n (i z)) p

end GlobalTheory.CompanionTheory.MixZ.PtLenProof
