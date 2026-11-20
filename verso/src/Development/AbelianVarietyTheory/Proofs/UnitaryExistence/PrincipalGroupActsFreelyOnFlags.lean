import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEqNsmulOfDvdPairing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOfFinOrderOfBounded
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsInvariantNatLengthLattice

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.PrincFree

/- English proof (translation)
Establish `hE : (H.rt : E) ^ 2 = -(H.d : E)`. Use `congrArg (algebraMap (𝓞 E) E) H.rt_sq` as an intermediate fact. Simplify using `using this`. Establish `hsq : τ (H.rt : E) ^ 2 = -(H.d : ℂ)` using `by rw [← map_pow, hE]; simp`. Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`.

Establish `hconj : ∀ z : ℂ, z ^ 2 = -(H.d : ℂ) → starRingEnd ℂ z = -z`. Introduce `z hz`. Establish `h1` using `congrArg Complex.re hz`. Establish `h2` using `congrArg Complex.im hz`. Simplify using `only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re, Complex.natCast_im, neg_zero] at h1 h2`.

Establish `h3 : z.re = 0`. Assume the negation of the conclusion as `h`. Establish `h4 : z.im = 0`. Establish `: z.re * z.im = 0` using `by linarith`. Conclude with `(mul_eq_zero.1 this).resolve_left h`.

Rewrite `h1` using `[h4]`. Use polynomial arithmetic with `[mul_self_nonneg z.re]`. Apply the tactic sequence `apply Complex.ext <;> simp [h3]`. Establish `hne : H.rt0 ≠ 0`. Introduce `h`.

Establish `h1` using `H.sqrt_neg_disc_sq`. Rewrite `h1` using `[h]`. Establish `h2 : (H.d : ℂ) = 0` using `by simpa using h1`. Conclude with `H.d_prime.ne_zero (by exact_mod_cast h2)`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq, hconj _ hsq]`.

Prove the components needed by the constructor for the conclusion. Introduce `h h'`. Rewrite `h'` using `[h]`. Conclude with `hne (by linear_combination (-1 / 2 : ℂ) * h')`. Introduce `h`.

Establish `h1 : τ (H.rt : E) ^ 2 = H.rt0 ^ 2` using `by rw [hsq, H.sqrt_neg_disc_sq]`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h2 | h2` into its components or cases. Conclude with `h2`. Conclude with `absurd (by rw [h2, neg_neg]) h`.
-/
theorem cmType_of_rt {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (τ : E →+* ℂ) :
    τ (H.rt : E) = H.rt0 ↔ ¬ (ComplexEmbedding.conjugate τ) (H.rt : E) = H.rt0 := by
  have hE : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have hsq : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by rw [← map_pow, hE]; simp
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hconj : ∀ z : ℂ, z ^ 2 = -(H.d : ℂ) → starRingEnd ℂ z = -z := by
    intro z hz
    have h1 := congrArg Complex.re hz
    have h2 := congrArg Complex.im hz
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
      Complex.natCast_im, neg_zero] at h1 h2
    have h3 : z.re = 0 := by
      by_contra h
      have h4 : z.im = 0 := by
        have : z.re * z.im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left h
      rw [h4] at h1
      nlinarith [mul_self_nonneg z.re]
    apply Complex.ext <;> simp [h3]
  have hne : H.rt0 ≠ 0 := by
    intro h
    have h1 := H.sqrt_neg_disc_sq
    rw [h] at h1
    have h2 : (H.d : ℂ) = 0 := by simpa using h1
    exact H.d_prime.ne_zero (by exact_mod_cast h2)
  rw [ComplexEmbedding.conjugate_coe_eq, hconj _ hsq]
  constructor
  · intro h h'
    rw [h] at h'
    exact hne (by linear_combination (-1 / 2 : ℂ) * h')
  · intro h
    have h1 : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by rw [hsq, H.sqrt_neg_disc_sq]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h2 | h2
    · exact h2
    · exact absurd (by rw [h2, neg_neg]) h

/- English proof (translation)
Use `choose f hf using fun a : L => (hγ (φ a)).1 (LinearMap.mem_range_self φ a)`. Set `g : L →ₗ[𝓞 E] L` to `{ toFun := f map_add' := fun a b => hφ (by rw [map_add, hf, hf, hf, map_add, Matrix.mulVec_add]) map_smul' := fun c a => hφ (by`. Rewrite using `[RingHom.id_apply, map_smul, hf, hf, map_smul, Matrix.mulVec_smul]) }`. Establish `hri : ∀ v, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v` using `fun v => by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Establish `hli : ∀ v, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = v` using `fun v => by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]`.

Use `⟨LinearEquiv.ofBijective g ⟨fun a b hab => hφ ?_, fun b => ?_⟩, hf⟩` and prove the remaining obligations. Establish `h : f a = f b` using `hab`. Rewrite using `[← hli (φ a), ← hli (φ b), ← hf, ← hf, h]`. Take `⟨a, ha⟩` from `(hγ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ φ b)).2 (by rw [hri]; exact LinearMap.mem_range_self φ b)`. Conclude with `⟨a, hφ (by rw [← hri (φ b), ← ha]; exact hf a)⟩`.
-/
theorem exists_equiv_of_stab {E : Type} [Field E] [NumberField E] {L : Type} [AddCommGroup L] [Module (𝓞 E) L]
    {r : ℕ} (φ : L →ₗ[𝓞 E] (Fin r → E)) (hφ : Function.Injective φ) (γ : GL (Fin r) E)
    (hγ : ∀ v, v ∈ LinearMap.range φ ↔ (γ : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ LinearMap.range φ) :
    ∃ g : L ≃ₗ[𝓞 E] L, ∀ a, φ (g a) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ a := by
  choose f hf using fun a : L => (hγ (φ a)).1 (LinearMap.mem_range_self φ a)
  let g : L →ₗ[𝓞 E] L :=
    { toFun := f
      map_add' := fun a b => hφ (by rw [map_add, hf, hf, hf, map_add, Matrix.mulVec_add])
      map_smul' := fun c a => hφ (by
        rw [RingHom.id_apply, map_smul, hf, hf, map_smul, Matrix.mulVec_smul]) }
  have hri : ∀ v, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hli : ∀ v, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  refine ⟨LinearEquiv.ofBijective g ⟨fun a b hab => hφ ?_, fun b => ?_⟩, hf⟩
  · have h : f a = f b := hab
    rw [← hli (φ a), ← hli (φ b), ← hf, ← hf, h]
  · obtain ⟨a, ha⟩ := (hγ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ φ b)).2
      (by rw [hri]; exact LinearMap.mem_range_self φ b)
    exact ⟨a, hφ (by rw [← hri (φ b), ← ha]; exact hf a)⟩

/- English proof (translation)
Introduce `E _ _ _ H l Di r ξ₀ Gm φ0 _ ⟨hinj, hsp, hG, _, hEF⟩ Ψ q hΨ γ hγ x hx b hb hxb`. Take `⟨hU, hhalf, -⟩` from `hγ`. Take `⟨g, hg⟩` from `exists_equiv_of_stab φ0 hinj γ hU.2`. Establish `hiso : ∀ a a', Di.EF (g a) (g a') = Di.EF a a'`. Introduce `a a'`.

Establish `: ((Di.EF (g a) (g a') : ℤ) : ℚ) = ((Di.EF a a' : ℤ) : ℚ)`. Rewrite using `[hEF, hEF, hg, hg, hU.1]`. Conclude with `this` after adjusting the coercions. Establish `hfull` using `GlobalTheory.LevelHalf.trivial_mod_of_trivial_on_half E H Di l g hiso (fun a ha => by`. Take `⟨e, he⟩` from `hhalf a ha`.

Conclude with `⟨e, hinj (by rw [hg, he, map_add, map_nsmul])⟩)`. Establish `hfin` using `Di.fin`. Use `GlobalTheory.GamFree.gam_free GlobalTheory.latMinkowski E r q l.M Ψ Gm (LinearMap.range φ0) γ (fun τ => ?_) hG ?_ ?_ l.three_le hU ?_ x hx b hb hxb` and prove the remaining obligations. Rewrite using `[hΨ, hΨ]`. Conclude with `cmType_of_rt H τ`.

Rewrite using `[LinearMap.range_eq_map]`. Conclude with `Module.Finite.fg_top.map φ0`. Rewrite using `[LinearMap.coe_range]`. Conclude with `hsp`. Introduce and unpack `_ ⟨a, rfl⟩`.

Take `⟨e, he⟩` from `hfull a`. Conclude with `⟨φ0 e, LinearMap.mem_range_self φ0 e, by rw [← hg, he, map_add, map_nsmul]⟩`.
-/
theorem princ_free : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Di : Datum H) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ0 : Di.La →ₗ[𝓞 E] (Fin r → E)), cc ξ₀ = -ξ₀ → (Function.Injective φ0 ∧ Submodule.span E (Set.range φ0) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Di.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ0 x) (φ0 y))) → ∀ (Ψ : Finset (E →+* ℂ)) (q : ℕ), (∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) → ∀ γ ∈ princ l Gm Di φ0, ∀ x ∈ GG Ψ Gm q, ∀ b ∈ Bor Ψ r, lact γ x = rmul x b → γ = 1 := by
  intro E _ _ _ H l Di r ξ₀ Gm φ0 _ ⟨hinj, hsp, hG, _, hEF⟩ Ψ q hΨ γ hγ x hx b hb hxb
  obtain ⟨hU, hhalf, -⟩ := hγ
  obtain ⟨g, hg⟩ := exists_equiv_of_stab φ0 hinj γ hU.2
  have hiso : ∀ a a', Di.EF (g a) (g a') = Di.EF a a' := by
    intro a a'
    have : ((Di.EF (g a) (g a') : ℤ) : ℚ) = ((Di.EF a a' : ℤ) : ℚ) := by
      rw [hEF, hEF, hg, hg, hU.1]
    exact_mod_cast this
  have hfull := GlobalTheory.LevelHalf.trivial_mod_of_trivial_on_half E H Di l g hiso (fun a ha => by
    obtain ⟨e, he⟩ := hhalf a ha
    exact ⟨e, hinj (by rw [hg, he, map_add, map_nsmul])⟩)
  have hfin := Di.fin
  refine GlobalTheory.GamFree.gam_free GlobalTheory.latMinkowski E r q l.M Ψ Gm (LinearMap.range φ0) γ
    (fun τ => ?_) hG ?_ ?_ l.three_le hU ?_ x hx b hb hxb
  · rw [hΨ, hΨ]; exact cmType_of_rt H τ
  · rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map φ0
  · rw [LinearMap.coe_range]; exact hsp
  · rintro _ ⟨a, rfl⟩
    obtain ⟨e, he⟩ := hfull a
    exact ⟨φ0 e, LinearMap.mem_range_self φ0 e, by rw [← hg, he, map_add, map_nsmul]⟩

end GlobalTheory.PrincFree
