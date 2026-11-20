import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents

noncomputable section

namespace GlobalTheory.FrobeniusPower

open Polynomial

/- English proof (translation)
Use `letI : Algebra (ZMod p) F := ZMod.algebra F p`. Set `ψ : F →ₐ[ZMod p] F` to `{ φ with commutes' := fun r => RingHom.congr_fun (RingHom.ext_zmod (φ.comp (algebraMap (ZMod p) F)) (algebraMap (ZMod p) F)) r }`. Establish `hinj : Function.Injective ψ` using `ψ.toRingHom.injective`. Set `σ : F ≃ₐ[ZMod p] F` to `AlgEquiv.ofBijective ψ ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩`. Take `⟨n, hn⟩` from `(FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) F).2 σ`.

Use `⟨n, fun x => ?_⟩` and prove the remaining obligations. Establish `h1 : σ x = φ x` using `rfl`. Rewrite using `[← h1, ← hn, AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card]`.
-/
theorem ringHom_eq_pow_frob (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Finite F] [CharP F p]
    (φ : F →+* F) : ∃ m : ℕ, ∀ x : F, φ x = x ^ p ^ m := by
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  let ψ : F →ₐ[ZMod p] F :=
    { φ with
      commutes' := fun r =>
        RingHom.congr_fun (RingHom.ext_zmod (φ.comp (algebraMap (ZMod p) F)) (algebraMap (ZMod p) F)) r }
  have hinj : Function.Injective ψ := ψ.toRingHom.injective
  let σ : F ≃ₐ[ZMod p] F := AlgEquiv.ofBijective ψ ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) F).2 σ
  refine ⟨n, fun x => ?_⟩
  have h1 : σ x = φ x := rfl
  rw [← h1, ← hn, AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card]

/- English proof (translation)
Establish `hq : 1 < l ^ a` using `Nat.one_lt_pow (NeZero.ne a) hl.out.one_lt`. Establish `hp : (X ^ (l ^ a) - X : (Formalism.BasicNotions.Loc.OCb l)[X]) ≠ 0`. Introduce `h`. Establish `h2` using `congrArg (fun f => Polynomial.coeff f (l ^ a)) h`. Simplify using `only [coeff_sub, coeff_X_pow, coeff_X, if_true, coeff_zero, if_neg hq.ne] at h2`.

Simplify using `at h2`. Establish `hsub : ((GlobalTheory.BKReal.resSub l a : Subring (Formalism.BasicNotions.Loc.OCb l)) : Set (Formalism.BasicNotions.Loc.OCb l)) ⊆ {x | (X ^ (l ^ a) - X : (Formalism.BasicNotions.Loc.OCb l)[X]).IsRoot x}`. Introduce `x hx`. Establish `hx' : iterateFrobenius (Formalism.BasicNotions.Loc.OCb l) l a x = x` using `hx`. Rewrite `hx'` using `[iterateFrobenius_def]`.

Use `show Polynomial.eval x (X ^ (l ^ a) - X) = 0`. Rewrite using `[eval_sub, eval_pow, eval_X, hx', sub_self]`. Establish `h : Finite ↥(GlobalTheory.BKReal.resSub l a)` using `((Polynomial.finite_setOf_isRoot hp).subset hsub).to_subtype`. Conclude with `h`.
-/
theorem finite_Fq (l : ℕ) [hl : Fact (Nat.Prime l)] (a : ℕ) [NeZero a] : Finite (GlobalTheory.BKReal.Fq l a) := by
  have hq : 1 < l ^ a := Nat.one_lt_pow (NeZero.ne a) hl.out.one_lt
  have hp : (X ^ (l ^ a) - X : (Formalism.BasicNotions.Loc.OCb l)[X]) ≠ 0 := by
    intro h
    have h2 := congrArg (fun f => Polynomial.coeff f (l ^ a)) h
    simp only [coeff_sub, coeff_X_pow, coeff_X, if_true, coeff_zero, if_neg hq.ne] at h2
    simp at h2
  have hsub : ((GlobalTheory.BKReal.resSub l a : Subring (Formalism.BasicNotions.Loc.OCb l)) : Set (Formalism.BasicNotions.Loc.OCb l)) ⊆
      {x | (X ^ (l ^ a) - X : (Formalism.BasicNotions.Loc.OCb l)[X]).IsRoot x} := by
    intro x hx
    have hx' : iterateFrobenius (Formalism.BasicNotions.Loc.OCb l) l a x = x := hx
    rw [iterateFrobenius_def] at hx'
    show Polynomial.eval x (X ^ (l ^ a) - X) = 0
    rw [eval_sub, eval_pow, eval_X, hx', sub_self]
  have h : Finite ↥(GlobalTheory.BKReal.resSub l a) := ((Polynomial.finite_setOf_isRoot hp).subset hsub).to_subtype
  exact h

/- English proof (translation)
Introduce `l hl a _ φ`. Use `haveI := finite_Fq l a`. Use `haveI : IsDomain (GlobalTheory.BKReal.Fq l a) := inferInstanceAs (IsDomain ↥(GlobalTheory.BKReal.resSub l a))`. Use `haveI : CharP (GlobalTheory.BKReal.Fq l a) l := inferInstanceAs (CharP ↥(GlobalTheory.BKReal.resSub l a) l)`. Use `letI : Field (GlobalTheory.BKReal.Fq l a) := (Finite.isDomain_to_isField _).toField`.

Conclude with `ringHom_eq_pow_frob l (GlobalTheory.BKReal.Fq l a) φ`.
-/
theorem main : ∀ (l : ℕ) [hl : Fact (Nat.Prime l)] (a : ℕ) [inst : NeZero a]
    (φ : GlobalTheory.BKReal.Fq l a →+* GlobalTheory.BKReal.Fq l a), ∃ (m : ℕ), ∀ (x : GlobalTheory.BKReal.Fq l a),
      (φ : GlobalTheory.BKReal.Fq l a → GlobalTheory.BKReal.Fq l a) x = x ^ l ^ m := by
  intro l hl a _ φ
  haveI := finite_Fq l a
  haveI : IsDomain (GlobalTheory.BKReal.Fq l a) := inferInstanceAs (IsDomain ↥(GlobalTheory.BKReal.resSub l a))
  haveI : CharP (GlobalTheory.BKReal.Fq l a) l :=
    inferInstanceAs (CharP ↥(GlobalTheory.BKReal.resSub l a) l)
  letI : Field (GlobalTheory.BKReal.Fq l a) := (Finite.isDomain_to_isField _).toField
  exact ringHom_eq_pow_frob l (GlobalTheory.BKReal.Fq l a) φ

end GlobalTheory.FrobeniusPower
