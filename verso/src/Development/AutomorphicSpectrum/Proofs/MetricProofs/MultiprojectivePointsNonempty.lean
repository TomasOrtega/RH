import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TransPtBase
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

/- English proof (translation)
Take `⟨M, hM⟩` from `Ideal.exists_maximal A`. Set `_ : Field (A ⧸ M)` to `Ideal.Quotient.field M`. Establish `: Module.Finite ℚ (A ⧸ M)` using `finite_of_finite_type_of_isJacobsonRing ℚ (A ⧸ M)`. Set `κ : (A ⧸ M) →ₐ[ℚ] ℂ` to `IsAlgClosed.lift`. Conclude with `⟨κ.comp (Ideal.Quotient.mkₐ ℚ M)⟩`.
-/
theorem exists_ratAlgHom_complex (A : Type) [CommRing A] [Nontrivial A] [Algebra ℚ A] [Algebra.FiniteType ℚ A] :
    Nonempty (A →ₐ[ℚ] ℂ) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  let _ : Field (A ⧸ M) := Ideal.Quotient.field M
  have : Module.Finite ℚ (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing ℚ (A ⧸ M)
  let κ : (A ⧸ M) →ₐ[ℚ] ℂ := IsAlgClosed.lift
  exact ⟨κ.comp (Ideal.Quotient.mkₐ ℚ M)⟩

/- English proof (translation)
Establish `h0 : mConeMap x f = 0` using `hf`. Establish `e : ((MvPolynomial.eval fun _ : K => (1 : Ω)).comp (mConeMap x).toRingHom) = (aeval x : MRing ι →ₐ[ℤ] Ω).toRingHom`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using the standard rewrite rules.

Introduce `p`. Simplify using `[mConeMap]`. Use `congrArg (fun g => g f) e` as an intermediate fact. Simplify using `only [RingHom.comp_apply] at this`. Establish `h1 : (aeval x : MRing ι →ₐ[ℤ] Ω) f = (MvPolynomial.eval fun _ : K => (1 : Ω)) ((mConeMap x) f)` using `this.symm`.

Rewrite using `[h1, h0, map_zero]`.
-/
theorem aeval_eq_zero_of_mem_mCoordIdeal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] {x : (Σ k, ι k) → Ω} {f : MRing ι} (hf : f ∈ mCoordIdeal x) : aeval x f = 0 := by
  have h0 : mConeMap x f = 0 := hf
  have e : ((MvPolynomial.eval fun _ : K => (1 : Ω)).comp (mConeMap x).toRingHom) =
      (aeval x : MRing ι →ₐ[ℤ] Ω).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro p
      simp [mConeMap]
  have := congrArg (fun g => g f) e
  simp only [RingHom.comp_apply] at this
  have h1 : (aeval x : MRing ι →ₐ[ℤ] Ω) f = (MvPolynomial.eval fun _ : K => (1 : Ω)) ((mConeMap x) f) := this.symm
  rw [h1, h0, map_zero]

/- English proof (translation)
Use `choose c hc using hx`. Use `set u : Ω := ∏ k, x ⟨k, c k⟩ with hu`. Establish `hu0 : u ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => hc k`. Set `S : Set Ω` to `Set.range x ∪ {u⁻¹}`. Establish `hS : S.Finite` using `(Set.finite_range x).union (Set.finite_singleton _)`.

Set `A : Subalgebra ℚ Ω` to `Algebra.adjoin ℚ S`. Establish `: Algebra.FiniteType ℚ A` using `Algebra.FiniteType.adjoin_of_finite hS`. Take `⟨ρ⟩` from `exists_ratAlgHom_complex A`. Set `xA : (Σ k, ι k) → A` to `fun p => ⟨x p, Algebra.subset_adjoin (Or.inl ⟨p, rfl⟩)⟩`. Set `v : A` to `⟨u⁻¹, Algebra.subset_adjoin (Or.inr rfl)⟩`.

Establish `huv : (∏ k, xA ⟨k, c k⟩) * v = 1`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `: ((∏ k, xA ⟨k, c k⟩ : A) : Ω) = u`. Rewrite using `[hu]`. Conclude with `map_prod A.val _ _`.

Use `show ((∏ k, xA ⟨k, c k⟩ : A) : Ω) * u⁻¹ = 1`. Rewrite using `[this, mul_inv_cancel₀ hu0]`. Establish `hz : (∏ k, ρ (xA ⟨k, c k⟩)) * ρ v = 1`. Rewrite using `[← map_prod, ← map_mul, huv, map_one]`. Use `⟨fun p => ρ (xA p), fun k => ⟨c k, fun h0 => ?_⟩, fun f hf => ?_⟩` and prove the remaining obligations.

Establish `: ∏ k, ρ (xA ⟨k, c k⟩) = 0` using `Finset.prod_eq_zero (Finset.mem_univ k) h0`. Rewrite `hz` using `[this, zero_mul]`. Conclude with `zero_ne_one hz`. Establish `h1 : aeval xA f = 0`. Apply `Subtype.ext` to reduce the goal to its premises.

Establish `e : (A.val.toRingHom.comp (aeval xA : MRing ι →ₐ[ℤ] A).toRingHom) = (aeval x : MRing ι →ₐ[ℤ] Ω).toRingHom`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using the standard rewrite rules. Introduce `p`.

Simplify using `[xA]`. Use `congrArg (fun g => g f) e` as an intermediate fact. Simplify using `only [RingHom.comp_apply] at this`. Conclude with `this.trans (aeval_eq_zero_of_mem_mCoordIdeal hf)`. Establish `e : ((MvPolynomial.eval fun p => ρ (xA p)).comp (MvPolynomial.map (Int.castRingHom ℂ))) = ρ.toRingHom.comp (aeval xA : MRing ι →ₐ[ℤ] A).toRingHom`.

Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using the standard rewrite rules. Introduce `p`. Simplify using the standard rewrite rules.

Use `congrArg (fun g => g f) e` as an intermediate fact. Simplify using `only [RingHom.comp_apply] at this`. Use `this.trans ?_` and prove the remaining obligations. Use `show ρ ((aeval xA : MRing ι →ₐ[ℤ] A) f) = 0`. Rewrite using `[h1, map_zero]`.
-/
theorem mcPts_mCoordIdeal_nonempty (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (x : (Σ k, ι k) → Ω) (hx : ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0) : (mcPts (mCoordIdeal x)).Nonempty := by
  choose c hc using hx
  set u : Ω := ∏ k, x ⟨k, c k⟩ with hu
  have hu0 : u ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
  let S : Set Ω := Set.range x ∪ {u⁻¹}
  have hS : S.Finite := (Set.finite_range x).union (Set.finite_singleton _)
  let A : Subalgebra ℚ Ω := Algebra.adjoin ℚ S
  have : Algebra.FiniteType ℚ A := Algebra.FiniteType.adjoin_of_finite hS
  obtain ⟨ρ⟩ := exists_ratAlgHom_complex A
  let xA : (Σ k, ι k) → A := fun p => ⟨x p, Algebra.subset_adjoin (Or.inl ⟨p, rfl⟩)⟩
  let v : A := ⟨u⁻¹, Algebra.subset_adjoin (Or.inr rfl)⟩
  have huv : (∏ k, xA ⟨k, c k⟩) * v = 1 := by
    apply Subtype.ext
    have : ((∏ k, xA ⟨k, c k⟩ : A) : Ω) = u := by
      rw [hu]
      exact map_prod A.val _ _
    show ((∏ k, xA ⟨k, c k⟩ : A) : Ω) * u⁻¹ = 1
    rw [this, mul_inv_cancel₀ hu0]
  have hz : (∏ k, ρ (xA ⟨k, c k⟩)) * ρ v = 1 := by
    rw [← map_prod, ← map_mul, huv, map_one]
  refine ⟨fun p => ρ (xA p), fun k => ⟨c k, fun h0 => ?_⟩, fun f hf => ?_⟩
  · have : ∏ k, ρ (xA ⟨k, c k⟩) = 0 := Finset.prod_eq_zero (Finset.mem_univ k) h0
    rw [this, zero_mul] at hz
    exact zero_ne_one hz
  · have h1 : aeval xA f = 0 := by
      apply Subtype.ext
      have e : (A.val.toRingHom.comp (aeval xA : MRing ι →ₐ[ℤ] A).toRingHom) =
          (aeval x : MRing ι →ₐ[ℤ] Ω).toRingHom := by
        apply MvPolynomial.ringHom_ext
        · intro r
          simp
        · intro p
          simp [xA]
      have := congrArg (fun g => g f) e
      simp only [RingHom.comp_apply] at this
      exact this.trans (aeval_eq_zero_of_mem_mCoordIdeal hf)
    have e : ((MvPolynomial.eval fun p => ρ (xA p)).comp (MvPolynomial.map (Int.castRingHom ℂ))) =
        ρ.toRingHom.comp (aeval xA : MRing ι →ₐ[ℤ] A).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp
      · intro p
        simp
    have := congrArg (fun g => g f) e
    simp only [RingHom.comp_apply] at this
    refine this.trans ?_
    show ρ ((aeval xA : MRing ι →ₐ[ℤ] A) f) = 0
    rw [h1, map_zero]

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
