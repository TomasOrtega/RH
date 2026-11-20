import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

/- English proof (translation)
Use `haveI : (RingHom.ker Φ).IsPrime := RingHom.ker_isPrime Φ`. Set `Q` to `P ⧸ RingHom.ker Φ`. Set `f1 : Q →+* L` to `RingHom.kerLift Φ`. Establish `hf1 : Function.Injective f1` using `RingHom.kerLift_injective Φ`. Set `f2 : Q →+* M` to `Ideal.Quotient.lift _ Ψ (fun a ha => by`.

Rewrite `ha` using `[h]`. Conclude with `ha)`. Establish `hf2 : Function.Injective f2` using `RingHom.lift_injective_of_ker_le_ideal _ _ h.ge`. Set `i1 : FractionRing Q →+* L` to `IsFractionRing.lift hf1`. Set `i2 : FractionRing Q →+* M` to `IsFractionRing.lift hf2`.

Establish `h1 : ∀ p, i1 (algebraMap Q _ (Ideal.Quotient.mk _ p)) = Φ p` using `fun p => by`. Simplify using `only [i1, IsFractionRing.lift_algebraMap]`. Conclude with `RingHom.kerLift_mk Φ p`. Establish `h2 : ∀ p, i2 (algebraMap Q _ (Ideal.Quotient.mk _ p)) = Ψ p` using `fun p => by`. Simplify using `only [i2, IsFractionRing.lift_algebraMap]`.

Both sides reduce to the same expression. Use `⟨i1.fieldRange, i2.comp i1.rangeRestrictFieldEquiv.symm.toRingHom, fun p => ⟨_, h1 p⟩, fun p => ?_⟩` and prove the remaining obligations. Establish `: i1.rangeRestrictFieldEquiv.symm ⟨Φ p, ⟨_, h1 p⟩⟩ = algebraMap Q _ (Ideal.Quotient.mk _ p)`. Rewrite using `[RingEquiv.symm_apply_eq]`. Conclude with `Subtype.ext (h1 p).symm`.

Rewrite using `[← h2 p, ← this]`. Both sides reduce to the same expression.
-/
theorem exists_hom_of_ker_eq {P L M : Type} [CommRing P] [Field L] [Field M]
    (Φ : P →+* L) (Ψ : P →+* M) (h : RingHom.ker Φ = RingHom.ker Ψ) :
    ∃ (S : Subfield L) (e : S →+* M), ∃ hS : ∀ p, Φ p ∈ S, ∀ p, e ⟨Φ p, hS p⟩ = Ψ p := by
  haveI : (RingHom.ker Φ).IsPrime := RingHom.ker_isPrime Φ
  let Q := P ⧸ RingHom.ker Φ
  let f1 : Q →+* L := RingHom.kerLift Φ
  have hf1 : Function.Injective f1 := RingHom.kerLift_injective Φ
  let f2 : Q →+* M := Ideal.Quotient.lift _ Ψ (fun a ha => by
    rw [h] at ha; exact ha)
  have hf2 : Function.Injective f2 :=
    RingHom.lift_injective_of_ker_le_ideal _ _ h.ge
  let i1 : FractionRing Q →+* L := IsFractionRing.lift hf1
  let i2 : FractionRing Q →+* M := IsFractionRing.lift hf2
  have h1 : ∀ p, i1 (algebraMap Q _ (Ideal.Quotient.mk _ p)) = Φ p := fun p => by
    simp only [i1, IsFractionRing.lift_algebraMap]
    exact RingHom.kerLift_mk Φ p
  have h2 : ∀ p, i2 (algebraMap Q _ (Ideal.Quotient.mk _ p)) = Ψ p := fun p => by
    simp only [i2, IsFractionRing.lift_algebraMap]
    rfl
  refine ⟨i1.fieldRange, i2.comp i1.rangeRestrictFieldEquiv.symm.toRingHom,
    fun p => ⟨_, h1 p⟩, fun p => ?_⟩
  have : i1.rangeRestrictFieldEquiv.symm ⟨Φ p, ⟨_, h1 p⟩⟩
      = algebraMap Q _ (Ideal.Quotient.mk _ p) := by
    rw [RingEquiv.symm_apply_eq]
    exact Subtype.ext (h1 p).symm
  rw [← h2 p, ← this]
  rfl

/- English proof (translation)
Introduce `o K σ _ _ β em u w a₀ hu hcl hker`. Set `i0 : Polynomial K →+* RatFunc K` to `algebraMap _ _`. Establish `hi0 : Function.Injective i0` using `IsFractionRing.injective _ _`. Use `set Φ₀ := MvPolynomial.eval₂Hom ((Polynomial.C : K →+* Polynomial K).comp β) (fun a => Polynomial.C (u a) * Polynomial.X) with hΦ₀`. Establish `hk : RingHom.ker (i0.comp Φ₀) = RingHom.ker (MvPolynomial.eval₂Hom em w)`.

Rewrite using `[← hker]`. Use extensionality with `p`. Simplify using `only [RingHom.mem_ker, RingHom.comp_apply, map_eq_zero_iff i0 hi0]`. Take `⟨S, e, hS, he⟩` from `exists_hom_of_ker_eq _ _ hk`. Set `j : K →+* RatFunc K` to `i0.comp Polynomial.C`.

Establish `hC : ∀ r, (i0.comp Φ₀) (MvPolynomial.C r) = j (β r)` using `fun r => by`. Simplify using `[hΦ₀, j]`. Establish `hX : ∀ a, (i0.comp Φ₀) (MvPolynomial.X a) = j (u a) * i0 Polynomial.X` using `fun a => by`. Simplify using `[hΦ₀, j]`. Establish `hT : i0 Polynomial.X ≠ 0` using `(map_ne_zero_iff i0 hi0).2 Polynomial.X_ne_zero`.

Establish `hdiv : ∀ a, j (u a / u a₀) = (i0.comp Φ₀) (MvPolynomial.X a) / (i0.comp Φ₀) (MvPolynomial.X a₀)` using `fun a => by`. Rewrite using `[hX, hX, map_div₀, mul_div_mul_right _ _ hT]`. Establish `hj : ∀ x, j x ∈ S`. Establish `: (⊤ : Subfield K) ≤ S.comap j`. Rewrite using `[← hcl, Subfield.closure_le]`.

Introduce and unpack `x (⟨r, rfl⟩ | ⟨a, rfl⟩)`. Use `show j (β r) ∈ S`. Rewrite using `[← hC]`. Conclude with `hS _`. Use `show j (u a / u a₀) ∈ S`.

Rewrite using `[hdiv]`. Conclude with `S.div_mem (hS _) (hS _)`. Conclude with `fun x => this (Subfield.mem_top x)`. Set `e' : K →+* ℂ` to `e.comp (j.codRestrict S hj)`. Establish `hw : w a₀ ≠ 0`.

Introduce `h0`. Establish `: MvPolynomial.X a₀ ∈ RingHom.ker (i0.comp Φ₀)`. Rewrite using `[hk, RingHom.mem_ker]`. Simplify using `using h0`. Rewrite `this` using `[RingHom.mem_ker, hX]`.

Conclude with `mul_ne_zero ((map_ne_zero j).2 hu) hT this`. Establish `hr : ∀ a, e' (u a / u a₀) = w a / w a₀` using `fun a => by`. Establish `h1` using `he (MvPolynomial.X a)`. Establish `h2` using `he (MvPolynomial.X a₀)`. Rewrite `h1`, `h2` using `[MvPolynomial.eval₂Hom_X']`.

Rewrite using `[← h1, ← h2, ← map_div₀]`. Conclude with `congrArg e (Subtype.ext (hdiv a))`. Establish `he0 : e' (u a₀) ≠ 0` using `(map_ne_zero e').2 hu`. Use `⟨e', e' (u a₀) / w a₀, div_ne_zero he0 hw, ?_, fun a => ?_⟩` and prove the remaining obligations. Use extensionality with `r`.

Establish `h1` using `he (MvPolynomial.C r)`. Rewrite `h1` using `[MvPolynomial.eval₂Hom_C]`. Rewrite using `[← h1]`. Conclude with `congrArg e (Subtype.ext (hC r).symm)`. Establish `h` using `hr a`.

Rewrite `h` using `[map_div₀, div_eq_iff he0]`. Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_embedding_of_homogeneous_ker_eq :
    ∀ (o K σ : Type) [CommRing o] [Field K] (β : o →+* K) (em : o →+* ℂ) (u : σ → K) (w : σ → ℂ) (a₀ : σ), u a₀ ≠ 0 → Subfield.closure (Set.range β ∪ Set.range (fun a => u a / u a₀)) = ⊤ → RingHom.ker (MvPolynomial.eval₂Hom ((Polynomial.C : K →+* Polynomial K).comp β) (fun a => Polynomial.C (u a) * Polynomial.X)) = RingHom.ker (MvPolynomial.eval₂Hom em w) → ∃ (e : K →+* ℂ) (c : ℂ), c ≠ 0 ∧ e.comp β = em ∧ ∀ a, e (u a) = c * w a := by
  intro o K σ _ _ β em u w a₀ hu hcl hker
  let i0 : Polynomial K →+* RatFunc K := algebraMap _ _
  have hi0 : Function.Injective i0 := IsFractionRing.injective _ _
  set Φ₀ := MvPolynomial.eval₂Hom ((Polynomial.C : K →+* Polynomial K).comp β)
    (fun a => Polynomial.C (u a) * Polynomial.X) with hΦ₀
  have hk : RingHom.ker (i0.comp Φ₀) = RingHom.ker (MvPolynomial.eval₂Hom em w) := by
    rw [← hker]
    ext p
    simp only [RingHom.mem_ker, RingHom.comp_apply, map_eq_zero_iff i0 hi0]
  obtain ⟨S, e, hS, he⟩ := exists_hom_of_ker_eq _ _ hk
  let j : K →+* RatFunc K := i0.comp Polynomial.C
  have hC : ∀ r, (i0.comp Φ₀) (MvPolynomial.C r) = j (β r) := fun r => by
    simp [hΦ₀, j]
  have hX : ∀ a, (i0.comp Φ₀) (MvPolynomial.X a) = j (u a) * i0 Polynomial.X := fun a => by
    simp [hΦ₀, j]
  have hT : i0 Polynomial.X ≠ 0 := (map_ne_zero_iff i0 hi0).2 Polynomial.X_ne_zero
  have hdiv : ∀ a, j (u a / u a₀)
      = (i0.comp Φ₀) (MvPolynomial.X a) / (i0.comp Φ₀) (MvPolynomial.X a₀) := fun a => by
    rw [hX, hX, map_div₀, mul_div_mul_right _ _ hT]
  have hj : ∀ x, j x ∈ S := by
    have : (⊤ : Subfield K) ≤ S.comap j := by
      rw [← hcl, Subfield.closure_le]
      rintro x (⟨r, rfl⟩ | ⟨a, rfl⟩)
      · show j (β r) ∈ S
        rw [← hC]; exact hS _
      · show j (u a / u a₀) ∈ S
        rw [hdiv]; exact S.div_mem (hS _) (hS _)
    exact fun x => this (Subfield.mem_top x)
  let e' : K →+* ℂ := e.comp (j.codRestrict S hj)
  have hw : w a₀ ≠ 0 := by
    intro h0
    have : MvPolynomial.X a₀ ∈ RingHom.ker (i0.comp Φ₀) := by
      rw [hk, RingHom.mem_ker]; simpa using h0
    rw [RingHom.mem_ker, hX] at this
    exact mul_ne_zero ((map_ne_zero j).2 hu) hT this
  have hr : ∀ a, e' (u a / u a₀) = w a / w a₀ := fun a => by
    have h1 := he (MvPolynomial.X a)
    have h2 := he (MvPolynomial.X a₀)
    rw [MvPolynomial.eval₂Hom_X'] at h1 h2
    rw [← h1, ← h2, ← map_div₀]
    exact congrArg e (Subtype.ext (hdiv a))
  have he0 : e' (u a₀) ≠ 0 := (map_ne_zero e').2 hu
  refine ⟨e', e' (u a₀) / w a₀, div_ne_zero he0 hw, ?_, fun a => ?_⟩
  · ext r
    have h1 := he (MvPolynomial.C r)
    rw [MvPolynomial.eval₂Hom_C] at h1
    rw [← h1]
    exact congrArg e (Subtype.ext (hC r).symm)
  · have h := hr a
    rw [map_div₀, div_eq_iff he0] at h
    rw [h]; ring

end GlobalTheory
