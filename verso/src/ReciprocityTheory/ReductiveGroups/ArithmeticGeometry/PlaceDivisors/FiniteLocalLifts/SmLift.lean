import Mathlib

set_option autoImplicit false
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms

variable {R : Type} [CommRing R] {A W K : Type} [CommRing A] [CommRing W] [CommRing K]
  [Algebra R A] [Algebra R W] [Algebra R K]

/- English proof (translation)
Take `⟨n, f, hf, hfg⟩ : ∃ (n : ℕ) (f : MvPolynomial (Fin n) R →ₐ[R] A), Function.Surjective f ∧ (RingHom.ker f.toRingHom).FG` from `by first`. Consider the case `exact Algebra.FinitePresentation.out`. Consider the case `(obtain ⟨n, f, hf, hfg⟩ := Algebra.FinitePresentation.out (R := R) (A := A)`. Conclude with `⟨n, f, hf, hfg⟩)`. Use `choose w hw using fun i : Fin n => hsurj (φ (f (MvPolynomial.X i)))`.

Set `Φ : MvPolynomial (Fin n) R →ₐ[R] W` to `MvPolynomial.aeval w`. Establish `hΦ : ρ.comp Φ = φ.comp f`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `i`. Simplify using `[Φ, hw]`.

Take `⟨s, hs⟩` from `hfg`. Set `J : Ideal W` to `Ideal.span (Φ '' (s : Set (MvPolynomial (Fin n) R)))`. Establish `hker : RingHom.ker f.toRingHom ≤ J.comap Φ`. Rewrite using `[← hs, Ideal.span_le]`. Introduce `p hp`.

Conclude with `Ideal.mem_comap.mpr (Ideal.subset_span ⟨p, hp, rfl⟩)`. Establish `hJker : J ≤ RingHom.ker ρ`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨p, hp, rfl⟩`. Establish `hpk : p ∈ RingHom.ker f.toRingHom` using `hs ▸ Ideal.subset_span hp`.

Rewrite `hpk` using `[RingHom.mem_ker]`. Rewrite using `[SetLike.mem_coe, RingHom.mem_ker]`. Establish `h1` using `congrArg (fun g => g p) hΦ`. Simplify using `only [AlgHom.comp_apply] at h1`. Rewrite using `[h1]`.

Establish `h2 : f p = 0` using `hpk`. Rewrite using `[h2, map_zero]`. Establish `hJnil : IsNilpotent J`. Rewrite using `[Ideal.FG.isNilpotent_iff_le_nilradical ⟨s.image Φ, by rw [Finset.coe_image]⟩]`. Introduce `a ha`.

Conclude with `mem_nilradical.mpr (hnil a (hJker ha))`. Establish `hcond : ∀ a ∈ RingHom.ker f, ((Ideal.Quotient.mkₐ R J).comp Φ) a = 0`. Introduce `a ha`. Rewrite using `[AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hker ha`.

Set `g : A →ₐ[R] W ⧸ J` to `(Ideal.Quotient.liftₐ (RingHom.ker f) ((Ideal.Quotient.mkₐ R J).comp Φ) hcond).comp (Ideal.quotientKerAlgEquivOfSurjective hf).symm.toAlgHom`. Use `⟨Algebra.FormallySmooth.lift J hJnil g, ?_⟩` and prove the remaining obligations. Apply `AlgHom.ext` to reduce the goal to its premises. Introduce `a`. Take `⟨p, rfl⟩` from `hf a`.

Establish `hmk` using `Algebra.FormallySmooth.mk_lift J hJnil g (f p)`. Establish `e2 : g (f p) = Ideal.Quotient.mk J (Φ p)`. Establish `e0 : (Ideal.quotientKerAlgEquivOfSurjective hf).symm (f p) = Ideal.Quotient.mk (RingHom.ker f) p`. Rewrite using `[AlgEquiv.symm_apply_eq]`. Use `first`.

Consider the case `rfl`. Consider the case `simp`. Use `show (Ideal.Quotient.liftₐ (RingHom.ker f) ((Ideal.Quotient.mkₐ R J).comp Φ) hcond) ((Ideal.quotientKerAlgEquivOfSurjective hf).symm (f p)) = _`. Rewrite using `[e0]`. Both sides reduce to the same expression.

Establish `e3 : ρ (Algebra.FormallySmooth.lift J hJnil g (f p)) = ρ (Φ p)`. Establish `h4 : Ideal.Quotient.mk J (Algebra.FormallySmooth.lift J hJnil g (f p)) = Ideal.Quotient.mk J (Φ p)` using `hmk.trans e2`. Rewrite `h4` using `[Ideal.Quotient.eq]`. Establish `h5` using `hJker h4`. Rewrite `h5` using `[RingHom.mem_ker, map_sub, sub_eq_zero]`.

Conclude with `h5`. Rewrite using `[AlgHom.comp_apply, e3]`. Conclude with `congrArg (fun g' => g' p) hΦ`.
-/
theorem exists_lift_nil [Algebra.FormallySmooth R A] [Algebra.FinitePresentation R A]
    (ρ : W →ₐ[R] K) (hsurj : Function.Surjective ρ) (hnil : ∀ a ∈ RingHom.ker ρ, IsNilpotent a)
    (φ : A →ₐ[R] K) : ∃ ψ : A →ₐ[R] W, ρ.comp ψ = φ := by
  classical
  obtain ⟨n, f, hf, hfg⟩ : ∃ (n : ℕ) (f : MvPolynomial (Fin n) R →ₐ[R] A), Function.Surjective f ∧
      (RingHom.ker f.toRingHom).FG := by
    first
    | exact Algebra.FinitePresentation.out
    | (obtain ⟨n, f, hf, hfg⟩ := Algebra.FinitePresentation.out (R := R) (A := A)
       exact ⟨n, f, hf, hfg⟩)
  choose w hw using fun i : Fin n => hsurj (φ (f (MvPolynomial.X i)))
  let Φ : MvPolynomial (Fin n) R →ₐ[R] W := MvPolynomial.aeval w
  have hΦ : ρ.comp Φ = φ.comp f := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [Φ, hw]
  obtain ⟨s, hs⟩ := hfg
  let J : Ideal W := Ideal.span (Φ '' (s : Set (MvPolynomial (Fin n) R)))
  have hker : RingHom.ker f.toRingHom ≤ J.comap Φ := by
    rw [← hs, Ideal.span_le]
    intro p hp
    exact Ideal.mem_comap.mpr (Ideal.subset_span ⟨p, hp, rfl⟩)
  have hJker : J ≤ RingHom.ker ρ := by
    rw [Ideal.span_le]
    rintro _ ⟨p, hp, rfl⟩
    have hpk : p ∈ RingHom.ker f.toRingHom := hs ▸ Ideal.subset_span hp
    rw [RingHom.mem_ker] at hpk
    rw [SetLike.mem_coe, RingHom.mem_ker]
    have h1 := congrArg (fun g => g p) hΦ
    simp only [AlgHom.comp_apply] at h1
    rw [h1]
    have h2 : f p = 0 := hpk
    rw [h2, map_zero]
  have hJnil : IsNilpotent J := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical ⟨s.image Φ, by rw [Finset.coe_image]⟩]
    intro a ha
    exact mem_nilradical.mpr (hnil a (hJker ha))
  have hcond : ∀ a ∈ RingHom.ker f, ((Ideal.Quotient.mkₐ R J).comp Φ) a = 0 := by
    intro a ha
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hker ha
  let g : A →ₐ[R] W ⧸ J := (Ideal.Quotient.liftₐ (RingHom.ker f) ((Ideal.Quotient.mkₐ R J).comp Φ)
    hcond).comp (Ideal.quotientKerAlgEquivOfSurjective hf).symm.toAlgHom
  refine ⟨Algebra.FormallySmooth.lift J hJnil g, ?_⟩
  apply AlgHom.ext
  intro a
  obtain ⟨p, rfl⟩ := hf a
  have hmk := Algebra.FormallySmooth.mk_lift J hJnil g (f p)
  have e2 : g (f p) = Ideal.Quotient.mk J (Φ p) := by
    have e0 : (Ideal.quotientKerAlgEquivOfSurjective hf).symm (f p) = Ideal.Quotient.mk (RingHom.ker f) p := by
      rw [AlgEquiv.symm_apply_eq]
      first
      | rfl
      | simp
    show (Ideal.Quotient.liftₐ (RingHom.ker f) ((Ideal.Quotient.mkₐ R J).comp Φ) hcond)
      ((Ideal.quotientKerAlgEquivOfSurjective hf).symm (f p)) = _
    rw [e0]
    rfl
  have e3 : ρ (Algebra.FormallySmooth.lift J hJnil g (f p)) = ρ (Φ p) := by
    have h4 : Ideal.Quotient.mk J (Algebra.FormallySmooth.lift J hJnil g (f p)) = Ideal.Quotient.mk J (Φ p) :=
      hmk.trans e2
    rw [Ideal.Quotient.eq] at h4
    have h5 := hJker h4
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h5
    exact h5
  rw [AlgHom.comp_apply, e3]
  exact congrArg (fun g' => g' p) hΦ

end ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms
