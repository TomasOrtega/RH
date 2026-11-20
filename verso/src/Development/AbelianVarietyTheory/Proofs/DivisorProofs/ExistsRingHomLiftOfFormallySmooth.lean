import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DI

/- English proof (translation)
Use `letI := φ.toAlgebra`. Use `letI := ψ.toAlgebra`. Use `haveI : Algebra.FormallySmooth R A := hφ`. Set `g' : A →ₐ[R] C ⧸ I` to `{ g with commutes' := fun r => by`. Use `congrArg (· r) hg` as an intermediate fact.

Conclude with `this }`. Use `⟨(Algebra.FormallySmooth.lift I hI g').toRingHom, fun x => ?_, fun r => ?_⟩` and prove the remaining obligations. Conclude with `Algebra.FormallySmooth.mk_lift I hI g' x`. Use `(Algebra.FormallySmooth.lift I hI g').commutes r` as an intermediate fact. Simplify `this` using `[RingHom.algebraMap_toAlgebra]`.
-/
theorem exists_ringHom_lift_of_formallySmooth {R A C : Type} [CommRing R] [CommRing A] [CommRing C]
    (φ : R →+* A) (hφ : φ.FormallySmooth) (ψ : R →+* C) (I : Ideal C) (hI : IsNilpotent I)
    (g : A →+* C ⧸ I) (hg : g.comp φ = (Ideal.Quotient.mk I).comp ψ) :
    ∃ F : A →+* C, (∀ x, Ideal.Quotient.mk I (F x) = g x) ∧ ∀ r, F (φ r) = ψ r := by
  letI := φ.toAlgebra
  letI := ψ.toAlgebra
  haveI : Algebra.FormallySmooth R A := hφ
  let g' : A →ₐ[R] C ⧸ I :=
    { g with
      commutes' := fun r => by
        have := congrArg (· r) hg
        exact this }
  refine ⟨(Algebra.FormallySmooth.lift I hI g').toRingHom, fun x => ?_, fun r => ?_⟩
  · exact Algebra.FormallySmooth.mk_lift I hI g' x
  · have := (Algebra.FormallySmooth.lift I hI g').commutes r
    simpa [RingHom.algebraMap_toAlgebra] using this

def powModP (p : ℕ) (hp : p.Prime) (B : Type) [CommRing B] :
    B →+* B ⧸ Ideal.span {(p : B)} where
  toFun z := Ideal.Quotient.mk _ (z ^ p)
  map_one' := by simp
  map_mul' x y := by simp [mul_pow]
  map_zero' := by simp [zero_pow hp.ne_zero]
  map_add' x y := by
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp x y
    rw [hr, map_add, map_add]
    have : Ideal.Quotient.mk (Ideal.span {(p : B)}) ((p : B) * x * y * r) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, mul_assoc, mul_assoc]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    rw [this, add_zero]

/- English proof (translation)
Introduce `p hpf n B _ φ hφ`. Establish `hp : p.Prime` using `hpf.out`. Use `set I : Ideal B := Ideal.span {(p : B)} with hIdef`. Establish `hp2 : ((p : B)) ^ 2 = 0`. Establish `: ((p ^ 2 : ℕ) : MvPolynomial (Fin n) (ZMod (p ^ 2))) = 0`.

Rewrite using `[← map_natCast (MvPolynomial.C (σ := Fin n)), ZMod.natCast_self, map_zero]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_natCast]`. Use `push_cast`. Both sides reduce to the same expression.

Use `_ = 0 := by rw [this, map_zero]`. Establish `hI : IsNilpotent I`. Use `⟨2, ?_⟩` and prove the remaining obligations. Rewrite using `[hIdef, Ideal.span_singleton_pow, hp2, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.zero_eq_bot]`. Establish `hsm : φ.FormallySmooth`.

Use `letI := φ.toAlgebra`. Use `haveI : Algebra.Etale _ B := hφ`. Use `show Algebra.FormallySmooth _ B`. Use `infer_instance`. Set `ψ : MvPolynomial (Fin n) (ZMod (p ^ 2)) →+* B` to `φ.comp (MvPolynomial.expand p).toRingHom`.

Establish `hg : (powModP p hp B).comp φ = (Ideal.Quotient.mk I).comp ψ`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Conclude with `congrArg (· r) (Subsingleton.elim ((((powModP p hp B).comp φ)).comp MvPolynomial.C) (((Ideal.Quotient.mk I).comp ψ).comp MvPolynomial.C))`. Introduce `i`.

Simplify using `[ψ, powModP, I]`. Take `⟨F, hF1, hF2⟩` from `exists_ringHom_lift_of_formallySmooth φ hsm ψ I hI (powModP p hp B) hg`. Use `⟨F, fun z => ?_, fun l => ?_⟩` and prove the remaining obligations. Establish `h1` using `hF1 z`. Establish `: F z - z ^ p ∈ I`.

Rewrite using `[← Ideal.Quotient.eq]`. Conclude with `h1`. Take `⟨w, hw⟩` from `Ideal.mem_span_singleton'.mp this`. Conclude with `⟨w, by rw [mul_comm]; linear_combination -hw⟩`. Rewrite using `[hF2]`.

Simplify using `[ψ]`.
-/
theorem frob_lift_etale_chart :
    ∀ (p : ℕ) [Fact p.Prime] {n : ℕ} {B : Type} [CommRing B]
      (φ : MvPolynomial (Fin n) (ZMod (p ^ 2)) →+* B), φ.Etale →
      ∃ F : B →+* B, (∀ z, ∃ w, F z = z ^ p + p * w) ∧
        ∀ l, F (φ (MvPolynomial.X l)) = φ (MvPolynomial.X l) ^ p := by
  intro p hpf n B _ φ hφ
  have hp : p.Prime := hpf.out
  set I : Ideal B := Ideal.span {(p : B)} with hIdef
  have hp2 : ((p : B)) ^ 2 = 0 := by
    have : ((p ^ 2 : ℕ) : MvPolynomial (Fin n) (ZMod (p ^ 2))) = 0 := by
      rw [← map_natCast (MvPolynomial.C (σ := Fin n)), ZMod.natCast_self, map_zero]
    calc ((p : B)) ^ 2 = φ ((p ^ 2 : ℕ) : MvPolynomial (Fin n) (ZMod (p ^ 2))) := by
          rw [map_natCast]; push_cast; rfl
      _ = 0 := by rw [this, map_zero]
  have hI : IsNilpotent I := by
    refine ⟨2, ?_⟩
    rw [hIdef, Ideal.span_singleton_pow, hp2, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.zero_eq_bot]
  have hsm : φ.FormallySmooth := by
    letI := φ.toAlgebra
    haveI : Algebra.Etale _ B := hφ
    show Algebra.FormallySmooth _ B
    infer_instance
  let ψ : MvPolynomial (Fin n) (ZMod (p ^ 2)) →+* B :=
    φ.comp (MvPolynomial.expand p).toRingHom
  have hg : (powModP p hp B).comp φ = (Ideal.Quotient.mk I).comp ψ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact congrArg (· r) (Subsingleton.elim ((((powModP p hp B).comp φ)).comp MvPolynomial.C)
        (((Ideal.Quotient.mk I).comp ψ).comp MvPolynomial.C))
    · intro i
      simp [ψ, powModP, I]
  obtain ⟨F, hF1, hF2⟩ := exists_ringHom_lift_of_formallySmooth φ hsm ψ I hI (powModP p hp B) hg
  refine ⟨F, fun z => ?_, fun l => ?_⟩
  · have h1 := hF1 z
    have : F z - z ^ p ∈ I := by
      rw [← Ideal.Quotient.eq]
      exact h1
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp this
    exact ⟨w, by rw [mul_comm]; linear_combination -hw⟩
  · rw [hF2]
    simp [ψ]

end GlobalTheory.DI
