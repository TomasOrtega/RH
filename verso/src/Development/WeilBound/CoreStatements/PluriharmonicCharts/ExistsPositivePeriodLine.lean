import Mathlib
import Development.WeilBound.CoreStatements.PluriharmonicCharts.IsBlockMapInitialVertex
import GroundTheory.HeightsAndTheta.Heights.Intersections.PProjBundleFibre
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Classical

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.Xgp.W

local instance (priority := 2000) intAlg4 {Φ : Type} [Field Φ] : Algebra ℤ (RatFunc Φ) := Ring.toIntAlgebra _

open GlobalTheory.CompanionTheory.Ar.PB.CovGraph.GenIdeal GlobalTheory.CompanionTheory.Ar.PB.WSq

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {L : Type} [Field L]

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

/- English proof (translation)
Use `letI : Algebra (A ⧸ RingHom.ker a) F := (RingHom.kerLift a).toAlgebra`. Use `haveI : FaithfulSMul (A ⧸ RingHom.ker a) F := (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective a)`. Use `haveI : IsFractionRing (A ⧸ RingHom.ker a) F := IsFractionRing.of_field _ _ fun c => by`. Take `⟨f, g, e⟩` from `gen c`. Conclude with `⟨Ideal.Quotient.mk _ f, Ideal.Quotient.mk _ g, e⟩`.

Set `b' : A ⧸ RingHom.ker a →+* E` to `Ideal.Quotient.lift _ b fun f hf => by rwa [hk] at hf`. Establish `hb' : Function.Injective b'` using `RingHom.lift_injective_of_ker_le_ideal _ _ hk.ge`. Conclude with `⟨IsFractionRing.lift hb', fun f => IsFractionRing.lift_algebraMap hb' (Ideal.Quotient.mk _ f)⟩`.
-/
theorem exists_lift_gen {A F E : Type} [CommRing A] [Field F] [Field E] (a : A →+* F) (b : A →+* E)
    (hk : RingHom.ker a = RingHom.ker b) (gen : ∀ c, ∃ f g, c = a f / a g) : ∃ ψ : F →+* E, ∀ f, ψ (a f) = b f := by
  letI : Algebra (A ⧸ RingHom.ker a) F := (RingHom.kerLift a).toAlgebra
  haveI : FaithfulSMul (A ⧸ RingHom.ker a) F :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective a)
  haveI : IsFractionRing (A ⧸ RingHom.ker a) F := IsFractionRing.of_field _ _ fun c => by
    obtain ⟨f, g, e⟩ := gen c
    exact ⟨Ideal.Quotient.mk _ f, Ideal.Quotient.mk _ g, e⟩
  let b' : A ⧸ RingHom.ker a →+* E := Ideal.Quotient.lift _ b fun f hf => by rwa [hk] at hf
  have hb' : Function.Injective b' := RingHom.lift_injective_of_ker_le_ideal _ _ hk.ge
  exact ⟨IsFractionRing.lift hb', fun f => IsFractionRing.lift_algebraMap hb' (Ideal.Quotient.mk _ f)⟩

def fibEquiv (ι : K → Type) (k₀ : K) :
    (Σ k : FibreBlock (some : K → Option K), fibreIdx (iW ι k₀) some k) ≃ ι k₀ where
  toFun
    | ⟨⟨some k, h⟩, _⟩ => absurd ⟨k, rfl⟩ h
    | ⟨⟨none, _⟩, m⟩ => m
  invFun m := ⟨⟨none, by rintro ⟨k, hk⟩; cases hk⟩, m⟩
  left_inv := by
    rintro ⟨⟨_ | k, h⟩, m⟩
    · rfl
    · exact absurd ⟨k, rfl⟩ h
  right_inv _ := rfl

/- English proof (translation)
Break down `k with ⟨_ | k, hk⟩` into its components or cases. Break down `k' with ⟨_ | k', hk'⟩` into its components or cases. Both sides reduce to the same expression. Conclude with `absurd ⟨k', rfl⟩ hk'`. Conclude with `absurd ⟨k, rfl⟩ hk`.
-/
theorem fibreBlock_subsingleton (k k' : FibreBlock (some : K → Option K)) : k = k' := by
  rcases k with ⟨_ | k, hk⟩
  · rcases k' with ⟨_ | k', hk'⟩
    · rfl
    · exact absurd ⟨k', rfl⟩ hk'
  · exact absurd ⟨k, rfl⟩ hk

/- English proof (translation)
Introduce `s hs k`. Take `⟨q, -, hq⟩` from `Finset.mem_biUnion.1 (support_sum hs)`. Rewrite `hq` using `[C_mul_X_eq_monomial]`. Establish `hs'` using `support_monomial_subset hq`. Rewrite `hs'` using `[Finset.mem_singleton]`.

Substitute `hs'` using the available equality. Take `⟨qk, qi⟩` from `q`. Take `rfl : qk = k` from `fibreBlock_subsingleton _ _`. Simplify using `[Finsupp.single_apply]`.
-/
theorem isMultiHomog_lin {F : Type} [Field F] (k₀ : K)
    (μ : (Σ k : FibreBlock (some : K → Option K), fibreIdx (iW ι k₀) some k) → F) :
    IsMultiHomog (∑ q, C (μ q) * X q : MRingOver F (fibreIdx (iW ι k₀) some)) fun _ => 1 := by
  intro s hs k
  obtain ⟨q, -, hq⟩ := Finset.mem_biUnion.1 (support_sum hs)
  rw [C_mul_X_eq_monomial] at hq
  have hs' := support_monomial_subset hq
  rw [Finset.mem_singleton] at hs'
  subst hs'
  obtain ⟨qk, qi⟩ := q
  obtain rfl : qk = k := fibreBlock_subsingleton _ _
  simp [Finsupp.single_apply]

variable {y : (Σ k, ι k) → Φ} {k₀ : K} {B : ι k₀ → Φ}

/- English proof (translation)
Establish `e : i₀.comp (mConeMap y).toRingHom = (aeval (fun p : Σ k, ι k => i₀ (X p.1) * ((i₀.comp C) ∘ y) p) : MRing ι →ₐ[ℤ] E).toRingHom` using `MvPolynomial.ringHom_ext (fun r => by simp) fun p => by simp [mConeMap, mul_comm]`. Use `RingHom.congr_fun e g` as an intermediate fact. Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this`. Rewrite using `[this, aeval_scale' (fun k => i₀ (X k)) _ hg, CPts.aeval_comp_ringHom]`. Both sides reduce to the same expression.
-/
theorem cone_homog {E : Type} [Field E] (i₀ : MvPolynomial K Φ →+* E) {g : MRing ι} {d : K → ℕ}
    (hg : IsMultiHomog g d) : i₀ (mConeMap y g) = (∏ k, i₀ (X k) ^ d k) * i₀ (C (aeval y g)) := by
  have e : i₀.comp (mConeMap y).toRingHom =
      (aeval (fun p : Σ k, ι k => i₀ (X p.1) * ((i₀.comp C) ∘ y) p) : MRing ι →ₐ[ℤ] E).toRingHom :=
    MvPolynomial.ringHom_ext (fun r => by simp) fun p => by simp [mConeMap, mul_comm]
  have := RingHom.congr_fun e g
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
  rw [this, aeval_scale' (fun k => i₀ (X k)) _ hg, CPts.aeval_comp_ringHom]
  rfl

/- English proof (translation)
Set `a : MRing ι →+* G.Φ` to `(aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom`. Establish `hka : RingHom.ker a = mCoordIdeal y` using `G.ker_x.trans (image_pen _ _ _ _ _)`. Take `⟨ψ, hψ⟩` from `exists_lift_gen a (i₀.comp (mConeMap y).toRingHom) (by rw [hka, RingHom.ker_comp_of_injective _ hi]; rfl) (fun c => by obtain ⟨f, g, -, e⟩ := G.gen c; exact ⟨f, g, e⟩)`. Establish `lift : ∀ s v, HasVal y y s v → ∃ s', ψ s' = i₀ (C s)`. Introduce and unpack `s v ⟨d, g, h, hg, hh, h0, e, -⟩`.

Use `⟨a g / a h, ?_⟩` and prove the remaining obligations. Rewrite using `[map_div₀, hψ, hψ]`. Use `show i₀ (mConeMap y g) / i₀ (mConeMap y h) = _`. Establish `hp : (∏ k, i₀ (X k) ^ d k) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ ((map_ne_zero_iff _ hi).2 (X_ne_zero _))`. Establish `h1 : i₀ (C (aeval y h)) ≠ 0` using `(map_ne_zero_iff _ hi).2 (by rwa [Ne, C_eq_zero])`.

Rewrite using `[cone_homog i₀ hg, cone_homog i₀ hh, mul_div_mul_left _ _ hp, e, map_mul, map_mul, mul_div_cancel_right₀ _ h1]`. Use `choose p hp using fun m => lift _ _ (Fr.hp m)`. Use `choose r hr using fun m => lift _ _ (Fr.hr m)`. Use `choose α hα using fun m => lift _ _ (Fr.hα m)`. Use `choose β hβ using fun m => lift _ _ (Fr.hβ m)`.

Set `eF` to `fibEquiv ι k₀`. Set `ℓ : (Σ k : FibreBlock (some : K → Option K), fibreIdx (iW ι k₀) some k) → Fin 2 → G.Φ` to `fun q => ![p (eF q), r (eF q)]`. Establish `hν : ∀ a b : Fin 2, ∑ q, ![fun q => α (eF q), fun q => β (eF q)] a q * ℓ q b = if a = b then 1 else 0`. Establish `key : ∀ (u w : ι k₀ → G.Φ) (u' w' : ι k₀ → Φ) (s : G.Φ) (s' : Φ), (∀ m, ψ (u m) = i₀ (C (u' m))) → (∀ m, ψ (w m) = i₀ (C (w' m))) → ψ s = i₀ (C s') → ∑ m, u' m * w' m = s' → ∑ q, u (eF q) * w (eF q) = s` using `fun u w u' w' s s' hu hw hs h => by`. Rewrite using `[Equiv.sum_comp eF fun m => u m * w m]`.

Apply `ψ.injective` to reduce the goal to its premises. Rewrite using `[hs, ← h]`. Simplify using `only [map_sum, map_mul, hu, hw]`. Introduce `a b`. Apply the tactic sequence `fin_cases a <;> fin_cases b`.

Conclude with `key α p _ _ 1 1 hα hp (by simp) Fr.αp`. Conclude with `key α r _ _ 0 0 hα hr (by simp) Fr.αr`. Conclude with `key β p _ _ 0 0 hβ hp (by simp) Fr.βp`. Conclude with `key β r _ _ 1 1 hβ hr (by simp) Fr.βr`. Use `⟨linKerForms ℓ, ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `f ⟨μ, -, rfl⟩`. Conclude with `isMultiHomog_lin k₀ μ`. Rewrite using `[← ker_linSubst ℓ _ hν]`. Set `W' : MRing (iW ι k₀) →+* MvPolynomial (Fin 2) E` to `(MvPolynomial.map i₀).comp (planeMap y k₀ Fr.p Fr.r)`. Set `x' : MRing (iW ι k₀) →+* G.Φ'` to `(aeval G.x' : MRing (iW ι k₀) →ₐ[ℤ] G.Φ').toRingHom`.

Establish `hker : RingHom.ker x' = RingHom.ker W'`. Rewrite using `[RingHom.ker_comp_of_injective _ (MvPolynomial.map_injective _ hi), ← Fr.ker_eq, ← ideal_pen_plane]`. Conclude with `G.genericFibre_ker_target`. Establish `r1 : ∀ f, x' (rename (v₀ k₀) f) = algebraMap G.Φ G.Φ' (a f)` using `fun f => by`. Establish `e : x'.comp (rename (v₀ k₀) : MRing ι →ₐ[ℤ] MRing (iW ι k₀)).toRingHom = (algebraMap G.Φ G.Φ').comp a` using `MvPolynomial.ringHom_ext (fun r => by simp) fun q => by simpa [x', a] using G.compat q`.

Conclude with `RingHom.congr_fun e f`. Establish `r2 : ∀ f, W' (rename (v₀ k₀) f) = C (ψ (a f))` using `fun f => by`. Rewrite using `[hψ]`. Establish `e : W'.comp (rename (v₀ k₀) : MRing ι →ₐ[ℤ] MRing (iW ι k₀)).toRingHom = (C : E →+* _).comp (i₀.comp (mConeMap y).toRingHom)` using `MvPolynomial.ringHom_ext (fun r => by simp) fun q => by simp [W', planeMap, ext2, v₀, mConeMap]`. Conclude with `RingHom.congr_fun e f`.

Establish `main : ∀ f : MRingOver G.Φ (fibreIdx (iW ι k₀) (some : K → Option K)), ∃ (Dn : MRing ι) (f' : MRing (iW ι k₀)), a Dn ≠ 0 ∧ x' f' = algebraMap G.Φ G.Φ' (a Dn) * aeval (fun q : Σ k : FibreBlock (some : K → Option K), iW ι k₀ k.1 => G.x' ⟨q.1.1, q.2⟩) f ∧ W' f' = C (ψ (a Dn)) * MvPo …`. Introduce `f`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C s`. Take `⟨f, g, hg, e⟩` from `G.gen s`.

Establish `e' : a f = a g * s` using `by rw [e]; exact (mul_div_cancel₀ _ hg).symm`. Use `⟨g, rename (v₀ k₀) f, hg, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[r1, e', map_mul, aeval_C]`. Rewrite using `[r2, e', map_mul, map_mul, algHom_C, algebraMap_eq, map_C]`. Consider the case `add f g hf hg`.

Take `⟨D₁, f₁, h₁, a₁, b₁⟩` from `hf`. Take `⟨D₂, f₂, h₂, a₂, b₂⟩` from `hg`. Use `⟨D₁ * D₂, f₁ * rename (v₀ k₀) D₂ + f₂ * rename (v₀ k₀) D₁, by rw [map_mul]; exact mul_ne_zero h₁ h₂, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, map_mul, r1, a₁, a₂]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [map_add, map_mul, r2, b₁, b₂]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul_X f q hf`. Take `⟨D₁, f₁, h₁, a₁, b₁⟩` from `hf`. Use `⟨D₁, f₁ * X ⟨q.1.1, q.2⟩, h₁, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, map_mul, a₁, aeval_X, mul_assoc]`. Use `congr 2`. Conclude with `aeval_X _ _`. Rewrite using `[map_mul, map_mul, map_mul, b₁, mul_assoc]`. Use `congr 2`.

Take `⟨m, rfl⟩` from `eF.symm.surjective q`. Establish `: W' (X ⟨none, m⟩) = C (i₀ (C (Fr.p m))) * X 0 + C (i₀ (C (Fr.r m))) * X 1`. Simplify using `[W', planeMap, ext2]`. Use `this.trans ?_` and prove the remaining obligations. Simplify using `[linSubst, ℓ, Fin.sum_univ_two, hp, hr]`.

Use extensionality with `f`. Take `⟨Dn, f', h0, h1, h2⟩` from `main f`. Establish `h3 : x' f' = 0 ↔ W' f' = 0` using `SetLike.ext_iff.1 hker f'`. Rewrite `h3` using `[h1, h2, mul_eq_zero, mul_eq_zero, or_iff_right ((map_ne_zero _).2 h0), or_iff_right (by rw [C_eq_zero]; exact (map_ne_zero _).2 h0), map_eq_zero_iff _ (MvPolynomial.map_injective _ ψ.injective)]`. Conclude with `h3`.
-/
theorem exists_positive_period_line {E : Type} [Field E] (i₀ : MvPolynomial K Φ →+* E) (hi : Function.Injective i₀)
    {cf : Φ} {e : K → ℤ} {c : ∀ k, ι k} (Fr : PenFrame y k₀ B cf e y c)
    (G : GenFibre (v₀ k₀) (mCoordIdeal (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X))) :
    ∃ T : Set (MRingOver G.Φ (fibreIdx (iW ι k₀) (some : K → Option K))),
      (∀ f ∈ T, IsMultiHomog f fun _ => 1) ∧ fibreIdeal (some : K → Option K) G = Ideal.span T := by
  let a : MRing ι →+* G.Φ := (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom
  have hka : RingHom.ker a = mCoordIdeal y := G.ker_x.trans (image_pen _ _ _ _ _)
  obtain ⟨ψ, hψ⟩ := exists_lift_gen a (i₀.comp (mConeMap y).toRingHom)
    (by rw [hka, RingHom.ker_comp_of_injective _ hi]; rfl)
    (fun c => by obtain ⟨f, g, -, e⟩ := G.gen c; exact ⟨f, g, e⟩)
  have lift : ∀ s v, HasVal y y s v → ∃ s', ψ s' = i₀ (C s) := by
    rintro s v ⟨d, g, h, hg, hh, h0, e, -⟩
    refine ⟨a g / a h, ?_⟩
    rw [map_div₀, hψ, hψ]
    show i₀ (mConeMap y g) / i₀ (mConeMap y h) = _
    have hp : (∏ k, i₀ (X k) ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ =>
      pow_ne_zero _ ((map_ne_zero_iff _ hi).2 (X_ne_zero _))
    have h1 : i₀ (C (aeval y h)) ≠ 0 := (map_ne_zero_iff _ hi).2 (by rwa [Ne, C_eq_zero])
    rw [cone_homog i₀ hg, cone_homog i₀ hh, mul_div_mul_left _ _ hp, e, map_mul, map_mul,
      mul_div_cancel_right₀ _ h1]
  choose p hp using fun m => lift _ _ (Fr.hp m)
  choose r hr using fun m => lift _ _ (Fr.hr m)
  choose α hα using fun m => lift _ _ (Fr.hα m)
  choose β hβ using fun m => lift _ _ (Fr.hβ m)
  let eF := fibEquiv ι k₀
  let ℓ : (Σ k : FibreBlock (some : K → Option K), fibreIdx (iW ι k₀) some k) → Fin 2 → G.Φ :=
    fun q => ![p (eF q), r (eF q)]
  have hν : ∀ a b : Fin 2, ∑ q, ![fun q => α (eF q), fun q => β (eF q)] a q * ℓ q b = if a = b then 1 else 0 := by
    have key : ∀ (u w : ι k₀ → G.Φ) (u' w' : ι k₀ → Φ) (s : G.Φ) (s' : Φ), (∀ m, ψ (u m) = i₀ (C (u' m))) →
        (∀ m, ψ (w m) = i₀ (C (w' m))) → ψ s = i₀ (C s') → ∑ m, u' m * w' m = s' →
        ∑ q, u (eF q) * w (eF q) = s := fun u w u' w' s s' hu hw hs h => by
      rw [Equiv.sum_comp eF fun m => u m * w m]
      apply ψ.injective
      rw [hs, ← h]
      simp only [map_sum, map_mul, hu, hw]
    intro a b
    fin_cases a <;> fin_cases b
    · exact key α p _ _ 1 1 hα hp (by simp) Fr.αp
    · exact key α r _ _ 0 0 hα hr (by simp) Fr.αr
    · exact key β p _ _ 0 0 hβ hp (by simp) Fr.βp
    · exact key β r _ _ 1 1 hβ hr (by simp) Fr.βr
  refine ⟨linKerForms ℓ, ?_, ?_⟩
  · rintro f ⟨μ, -, rfl⟩
    exact isMultiHomog_lin k₀ μ
  rw [← ker_linSubst ℓ _ hν]
  let W' : MRing (iW ι k₀) →+* MvPolynomial (Fin 2) E := (MvPolynomial.map i₀).comp (planeMap y k₀ Fr.p Fr.r)
  let x' : MRing (iW ι k₀) →+* G.Φ' := (aeval G.x' : MRing (iW ι k₀) →ₐ[ℤ] G.Φ').toRingHom
  have hker : RingHom.ker x' = RingHom.ker W' := by
    rw [RingHom.ker_comp_of_injective _ (MvPolynomial.map_injective _ hi), ← Fr.ker_eq, ← ideal_pen_plane]
    exact G.genericFibre_ker_target
  have r1 : ∀ f, x' (rename (v₀ k₀) f) = algebraMap G.Φ G.Φ' (a f) := fun f => by
    have e : x'.comp (rename (v₀ k₀) : MRing ι →ₐ[ℤ] MRing (iW ι k₀)).toRingHom = (algebraMap G.Φ G.Φ').comp a :=
      MvPolynomial.ringHom_ext (fun r => by simp) fun q => by simpa [x', a] using G.compat q
    exact RingHom.congr_fun e f
  have r2 : ∀ f, W' (rename (v₀ k₀) f) = C (ψ (a f)) := fun f => by
    rw [hψ]
    have e : W'.comp (rename (v₀ k₀) : MRing ι →ₐ[ℤ] MRing (iW ι k₀)).toRingHom =
        (C : E →+* _).comp (i₀.comp (mConeMap y).toRingHom) :=
      MvPolynomial.ringHom_ext (fun r => by simp) fun q => by simp [W', planeMap, ext2, v₀, mConeMap]
    exact RingHom.congr_fun e f
  have main : ∀ f : MRingOver G.Φ (fibreIdx (iW ι k₀) (some : K → Option K)), ∃ (Dn : MRing ι) (f' : MRing (iW ι k₀)),
      a Dn ≠ 0 ∧ x' f' = algebraMap G.Φ G.Φ' (a Dn) *
        aeval (fun q : Σ k : FibreBlock (some : K → Option K), iW ι k₀ k.1 => G.x' ⟨q.1.1, q.2⟩) f ∧
      W' f' = C (ψ (a Dn)) * MvPolynomial.map ψ (linSubst ℓ f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C s =>
      obtain ⟨f, g, hg, e⟩ := G.gen s
      have e' : a f = a g * s := by rw [e]; exact (mul_div_cancel₀ _ hg).symm
      refine ⟨g, rename (v₀ k₀) f, hg, ?_, ?_⟩
      · rw [r1, e', map_mul, aeval_C]
      · rw [r2, e', map_mul, map_mul, algHom_C, algebraMap_eq, map_C]
    | add f g hf hg =>
      obtain ⟨D₁, f₁, h₁, a₁, b₁⟩ := hf
      obtain ⟨D₂, f₂, h₂, a₂, b₂⟩ := hg
      refine ⟨D₁ * D₂, f₁ * rename (v₀ k₀) D₂ + f₂ * rename (v₀ k₀) D₁, by rw [map_mul]; exact mul_ne_zero h₁ h₂,
        ?_, ?_⟩
      · simp only [map_add, map_mul, r1, a₁, a₂]; ring
      · simp only [map_add, map_mul, r2, b₁, b₂]; ring
    | mul_X f q hf =>
      obtain ⟨D₁, f₁, h₁, a₁, b₁⟩ := hf
      refine ⟨D₁, f₁ * X ⟨q.1.1, q.2⟩, h₁, ?_, ?_⟩
      · rw [map_mul, map_mul, a₁, aeval_X, mul_assoc]
        congr 2
        exact aeval_X _ _
      · rw [map_mul, map_mul, map_mul, b₁, mul_assoc]
        congr 2
        obtain ⟨m, rfl⟩ := eF.symm.surjective q
        have : W' (X ⟨none, m⟩) = C (i₀ (C (Fr.p m))) * X 0 + C (i₀ (C (Fr.r m))) * X 1 := by
          simp [W', planeMap, ext2]
        refine this.trans ?_
        simp [linSubst, ℓ, Fin.sum_univ_two, hp, hr]
  ext f
  obtain ⟨Dn, f', h0, h1, h2⟩ := main f
  have h3 : x' f' = 0 ↔ W' f' = 0 := SetLike.ext_iff.1 hker f'
  rw [h1, h2, mul_eq_zero, mul_eq_zero, or_iff_right ((map_ne_zero _).2 h0),
    or_iff_right (by rw [C_eq_zero]; exact (map_ne_zero _).2 h0),
    map_eq_zero_iff _ (MvPolynomial.map_injective _ ψ.injective)] at h3
  exact h3

/- English proof (translation)
The claim follows from `exists_positive_period_line (algebraMap _ (FractionRing (MvPolynomial K Φ))) (IsFractionRing.injective _ _) Fr G`.
-/
theorem line_pen {cf : Φ} {e : K → ℤ} {c : ∀ k, ι k} (Fr : PenFrame y k₀ B cf e y c)
    (G : GenFibre (v₀ k₀) (mCoordIdeal (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X))) :
    ∃ T : Set (MRingOver G.Φ (fibreIdx (iW ι k₀) (some : K → Option K))),
      (∀ f ∈ T, IsMultiHomog f fun _ => 1) ∧ fibreIdeal (some : K → Option K) G = Ideal.span T :=
  exists_positive_period_line (algebraMap _ (FractionRing (MvPolynomial K Φ))) (IsFractionRing.injective _ _) Fr G

end PositivityTheory.Xgp.W
