import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.TsgPolyVolPolyCoeffEven
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace PositivityTheory.Xgp.birat

variable {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Introduce `m hm k`. Take `⟨m₁, h₁, m₂, h₂, rfl⟩` from `Finset.mem_add.1 (support_mul f g hm)`. Simplify using `only [Finsupp.add_apply, Finset.sum_add_distrib, hf m₁ h₁ k, hg m₂ h₂ k, Pi.add_apply]`.
-/
theorem hom_mul {f g : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι} {a b : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a)
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g b) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.1 (support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, hf m₁ h₁ k, hg m₂ h₂ k, Pi.add_apply]

/- English proof (translation)
Introduce `m hm k`. Break down `Finset.mem_union.1 (support_add hm) with h | h` into its components or cases. Conclude with `hf m h k`. Conclude with `hg m h k`.
-/
theorem hom_add {f g : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι} {a : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a)
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.1 (support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

/- English proof (translation)
Introduce `m hm k`. Rewrite `hm` using `[support_neg]`. Conclude with `hf m hm k`.
-/
theorem hom_neg {f : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι} {a : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (-f) a := by
  intro m hm k
  rw [support_neg] at hm
  exact hf m hm k

/- English proof (translation)
Introduce `m hm k`. Establish `: m = 0`. Assume the negation of the conclusion as `h`. Rewrite `hm` using `[mem_support_iff, coeff_one, if_neg (Ne.symm h)]`. Conclude with `hm rfl`.

Substitute `this` using the available equality. Simplify using the standard rewrite rules.
-/
theorem hom_one : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (1 : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) 0 := by
  classical
  intro m hm k
  have : m = 0 := by
    by_contra h
    rw [mem_support_iff, coeff_one, if_neg (Ne.symm h)] at hm
    exact hm rfl
  subst this
  simp

/- English proof (translation)
Establish `key : ∀ i : ι k, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (X ⟨k, i⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) (fun k' => if k = k' then 1 else 0)`. Introduce `i m hm k'`. Rewrite `hm` using `[support_X, Finset.mem_singleton]`. Substitute `hm` using the available equality. Distinguish the cases in `h : k = k'`.

Substitute `h` using the available equality. Simplify using `[Finsupp.single_apply]`. Simplify using `[Finsupp.single_apply, h]`. Conclude with `⟨_, key i, key j⟩`.
-/
theorem hom_X (k : K) (i j : ι k) : ∃ a, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (X ⟨k, i⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) a ∧
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (X ⟨k, j⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) a := by
  classical
  have key : ∀ i : ι k, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (X ⟨k, i⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)
      (fun k' => if k = k' then 1 else 0) := by
    intro i m hm k'
    rw [support_X, Finset.mem_singleton] at hm
    subst hm
    by_cases h : k = k'
    · subst h
      simp [Finsupp.single_apply]
    · simp [Finsupp.single_apply, h]
  exact ⟨_, key i, key j⟩

/- English proof (translation)
Proceed by induction on `hs using Subfield.closure_induction with`. Consider the case `mem x hx`. Take `⟨⟨k, i⟩, rfl⟩` from `hx`. Take `⟨a, h1, h2⟩` from `hom_X k i (c k)`. Conclude with `⟨a, _, _, h1, h2, by simp [hc], by simp [hc]⟩`.

Consider the case `one => exact ⟨0, 1, 1, hom_one, hom_one, by simp, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨d, g, h, a1, a2, a3, a4⟩` from `hx`. Take `⟨d', g', h', b1, b2, b3, b4⟩` from `hy`. Use `⟨d + d', g * h' + h * g', h * h', hom_add (hom_mul a1 b2) (hom_mul a2 b1), hom_mul a2 b2, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul]`. Conclude with `mul_ne_zero a3 b3`. Rewrite using `[map_add, map_mul, map_mul, map_mul, a4, b4]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `neg x _ hx`.

Take `⟨d, g, h, a1, a2, a3, a4⟩` from `hx`. Conclude with `⟨d, -g, h, hom_neg a1, a2, a3, by rw [map_neg, a4]; ring⟩`. Consider the case `inv x _ hx`. Take `⟨d, g, h, a1, a2, a3, a4⟩` from `hx`. Distinguish the cases in `h0 : x = 0`.

Conclude with `⟨d, g, h, a1, a2, a3, by rw [a4, h0, inv_zero]⟩`. Conclude with `⟨d, h, g, a2, a1, by rw [a4]; exact mul_ne_zero h0 a3, by rw [a4, inv_mul_cancel_left₀ h0]⟩`. Consider the case `mul x y _ _ hx hy`. Take `⟨d, g, h, a1, a2, a3, a4⟩` from `hx`. Take `⟨d', g', h', b1, b2, b3, b4⟩` from `hy`.

Use `⟨d + d', g * g', h * h', hom_mul a1 b1, hom_mul a2 b2, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `mul_ne_zero a3 b3`. Rewrite using `[map_mul, map_mul, a4, b4]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ratio {Ω : Type} [Field Ω] (r : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, r ⟨k, c k⟩ = 1) (s : Ω)
    (hs : s ∈ Subfield.closure (Set.range r)) :
    ∃ (d : K → ℕ) (g h : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d ∧
      ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog h d ∧ aeval r h ≠ 0 ∧ aeval r g = s * aeval r h := by
  induction hs using Subfield.closure_induction with
  | mem x hx =>
    obtain ⟨⟨k, i⟩, rfl⟩ := hx
    obtain ⟨a, h1, h2⟩ := hom_X k i (c k)
    exact ⟨a, _, _, h1, h2, by simp [hc], by simp [hc]⟩
  | one => exact ⟨0, 1, 1, hom_one, hom_one, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d, g, h, a1, a2, a3, a4⟩ := hx
    obtain ⟨d', g', h', b1, b2, b3, b4⟩ := hy
    refine ⟨d + d', g * h' + h * g', h * h', hom_add (hom_mul a1 b2) (hom_mul a2 b1), hom_mul a2 b2, ?_, ?_⟩
    · rw [map_mul]; exact mul_ne_zero a3 b3
    · rw [map_add, map_mul, map_mul, map_mul, a4, b4]; ring
  | neg x _ hx =>
    obtain ⟨d, g, h, a1, a2, a3, a4⟩ := hx
    exact ⟨d, -g, h, hom_neg a1, a2, a3, by rw [map_neg, a4]; ring⟩
  | inv x _ hx =>
    obtain ⟨d, g, h, a1, a2, a3, a4⟩ := hx
    by_cases h0 : x = 0
    · exact ⟨d, g, h, a1, a2, a3, by rw [a4, h0, inv_zero]⟩
    · exact ⟨d, h, g, a2, a1, by rw [a4]; exact mul_ne_zero h0 a3, by rw [a4, inv_mul_cancel_left₀ h0]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨d, g, h, a1, a2, a3, a4⟩ := hx
    obtain ⟨d', g', h', b1, b2, b3, b4⟩ := hy
    refine ⟨d + d', g * g', h * h', hom_mul a1 b1, hom_mul a2 b2, ?_, ?_⟩
    · rw [map_mul]; exact mul_ne_zero a3 b3
    · rw [map_mul, map_mul, a4, b4]; ring

end PositivityTheory.Xgp.birat

open PositivityTheory.Xgp.birat in
/- English proof (translation)
Introduce `K _ ι _ Ω _ y hy`. Use `choose c hc using hy`. Set `r : (Σ k, ι k) → Ω` to `fun p => y p / y ⟨p.1, c p.1⟩`. Set `F : Subfield Ω` to `Subfield.closure (Set.range r)`. Set `y' : (Σ k, ι k) → F` to `fun p => ⟨r p, Subfield.subset_closure ⟨p, rfl⟩⟩`.

Establish `hev : ∀ g : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι, ((aeval y' g : F) : Ω) = aeval r g` using `fun g => by`. Establish `: (F.subtype.toIntAlgHom).comp (aeval y') = aeval r`. Use extensionality with `p`. Simplify using `[y']`. Conclude with `AlgHom.congr_fun this g`.

Use `⟨F, inferInstance, y', ?_, fun s => ?_⟩` and prove the remaining obligations. Set `θ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω` to `aeval fun k => C (y ⟨k, c k⟩) * X k`. Set `θ' : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω` to `aeval fun k => C (y ⟨k, c k⟩)⁻¹ * X k`. Establish `hθ : θ'.comp θ = AlgHom.id Ω _`. Use `MvPolynomial.algHom_ext fun k => ?_` and prove the remaining obligations.

Simplify using `only [θ, θ', AlgHom.comp_apply, aeval_X, map_mul, aeval_C, algebraMap_eq, AlgHom.id_apply]`. Rewrite using `[← mul_assoc, ← C_mul, mul_inv_cancel₀ (hc k), C_1, one_mul]`. Establish `hθi : Function.Injective θ` using `Function.LeftInverse.injective (g := θ') (AlgHom.congr_fun hθ)`. Set `ψ : MvPolynomial K F →+* MvPolynomial K Ω` to `θ.toRingHom.comp (MvPolynomial.map F.subtype)`. Establish `hψ : Function.Injective ψ` using `hθi.comp (MvPolynomial.map_injective _ F.subtype.injective)`.

Establish `e : ψ.comp (mConeMap y').toRingHom = (mConeMap y).toRingHom`. Use `MvPolynomial.ringHom_ext (fun n => by simp) fun p => ?_` and prove the remaining obligations. Establish `e1 : mConeMap y' (X p) = C (y' p) * X p.1` using `aeval_X _ p`. Establish `e2 : mConeMap y (X p) = C (y p) * X p.1` using `aeval_X _ p`. Use `show θ (MvPolynomial.map F.subtype (mConeMap y' (X p))) = mConeMap y (X p)`.

Rewrite using `[e1, e2]`. Simplify using `only [θ, map_mul, map_C, map_X, aeval_X, aeval_C, algebraMap_eq]`. Rewrite using `[← mul_assoc, ← C_mul]`. Use `congr 2`. Conclude with `div_mul_cancel₀ _ (hc _)`.

Use extensionality with `g`. Use `show mConeMap y' g = 0 ↔ mConeMap y g = 0`. Rewrite using `[show mConeMap y g = ψ (mConeMap y' g) from (RingHom.congr_fun e g).symm]`. Conclude with `(map_eq_zero_iff ψ hψ).symm`. Take `⟨d, g, h, a1, a2, a3, a4⟩` from `ratio r c (fun k => div_self (hc k)) s.1 s.2`.

Use `⟨d, g, h, a1, a2, fun h0 => a3 (by rw [← hev, h0]; rfl), Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[Subfield.coe_mul, hev, hev, a4]`.
-/
theorem PositivityTheory.Xgp.t_birat : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω), (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → ∃ (Ω' : Type) (_ : Field Ω') (y' : (Σ k, ι k) → Ω'), mCoordIdeal y' = mCoordIdeal y ∧ Birational y' := by
  intro K _ ι _ Ω _ y hy
  choose c hc using hy
  let r : (Σ k, ι k) → Ω := fun p => y p / y ⟨p.1, c p.1⟩
  let F : Subfield Ω := Subfield.closure (Set.range r)
  let y' : (Σ k, ι k) → F := fun p => ⟨r p, Subfield.subset_closure ⟨p, rfl⟩⟩
  have hev : ∀ g : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι, ((aeval y' g : F) : Ω) = aeval r g := fun g => by
    have : (F.subtype.toIntAlgHom).comp (aeval y') = aeval r := by
      ext p
      simp [y']
    exact AlgHom.congr_fun this g
  refine ⟨F, inferInstance, y', ?_, fun s => ?_⟩
  · let θ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k => C (y ⟨k, c k⟩) * X k
    let θ' : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := aeval fun k => C (y ⟨k, c k⟩)⁻¹ * X k
    have hθ : θ'.comp θ = AlgHom.id Ω _ := by
      refine MvPolynomial.algHom_ext fun k => ?_
      simp only [θ, θ', AlgHom.comp_apply, aeval_X, map_mul, aeval_C, algebraMap_eq, AlgHom.id_apply]
      rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ (hc k), C_1, one_mul]
    have hθi : Function.Injective θ := Function.LeftInverse.injective (g := θ') (AlgHom.congr_fun hθ)
    let ψ : MvPolynomial K F →+* MvPolynomial K Ω := θ.toRingHom.comp (MvPolynomial.map F.subtype)
    have hψ : Function.Injective ψ := hθi.comp (MvPolynomial.map_injective _ F.subtype.injective)
    have e : ψ.comp (mConeMap y').toRingHom = (mConeMap y).toRingHom := by
      refine MvPolynomial.ringHom_ext (fun n => by simp) fun p => ?_
      have e1 : mConeMap y' (X p) = C (y' p) * X p.1 := aeval_X _ p
      have e2 : mConeMap y (X p) = C (y p) * X p.1 := aeval_X _ p
      show θ (MvPolynomial.map F.subtype (mConeMap y' (X p))) = mConeMap y (X p)
      rw [e1, e2]
      simp only [θ, map_mul, map_C, map_X, aeval_X, aeval_C, algebraMap_eq]
      rw [← mul_assoc, ← C_mul]
      congr 2
      exact div_mul_cancel₀ _ (hc _)
    ext g
    show mConeMap y' g = 0 ↔ mConeMap y g = 0
    rw [show mConeMap y g = ψ (mConeMap y' g) from (RingHom.congr_fun e g).symm]
    exact (map_eq_zero_iff ψ hψ).symm
  · obtain ⟨d, g, h, a1, a2, a3, a4⟩ := ratio r c (fun k => div_self (hc k)) s.1 s.2
    refine ⟨d, g, h, a1, a2, fun h0 => a3 (by rw [← hev, h0]; rfl), Subtype.ext ?_⟩
    rw [Subfield.coe_mul, hev, hev, a4]
