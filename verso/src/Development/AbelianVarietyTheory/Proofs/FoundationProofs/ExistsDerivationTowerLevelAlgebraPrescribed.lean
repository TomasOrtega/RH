import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerEmbeddingInjectiveStatement
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

noncomputable section
namespace GlobalTheory.AlmostEt.LevDer
open Polynomial TrivSqZeroExt

section Gen
variable {A S M : Type} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M]
  [Module Sᵐᵒᵖ M] [IsCentralScalar S M]

def sqEv (z q : S) (μ ν : M) : Polynomial (Polynomial A) →+* TrivSqZeroExt S M :=
  eval₂RingHom (eval₂RingHom ((inlHom S M).comp (algebraMap A S)) (inl z + inr μ)) (inl q + inr ν)

def ev2 (z q : S) : Polynomial (Polynomial A) →+* S :=
  eval₂RingHom (eval₂RingHom (algebraMap A S) z) q

/- English proof (translation)
Rewrite using `[pow_two, inr_mul_inr]`.
-/
theorem sq_inr (m : M) : (inr m : TrivSqZeroExt S M) ^ 2 = 0 := by
  rw [pow_two, inr_mul_inr]

/- English proof (translation)
Simplify using `only [sqEv, coe_eval₂RingHom, eval₂_C]`. Rewrite using `[eval₂_eq_eval_map, eval_add_of_sq_eq_zero _ _ _ (sq_inr μ), derivative_map, ← eval₂_eq_eval_map, ← eval₂_eq_eval_map]`. Rewrite using `[show (inl z : TrivSqZeroExt S M) = inlHom S M z from rfl, ← hom_eval₂, ← hom_eval₂, inlHom_apply, inlHom_apply, inl_mul_inr]`.
-/
theorem sqEv_C (z q : S) (μ ν : M) (g : Polynomial A) :
    sqEv z q μ ν (C g) = inl (eval₂ (algebraMap A S) z g) +
      inr (eval₂ (algebraMap A S) z (derivative g) • μ) := by
  simp only [sqEv, coe_eval₂RingHom, eval₂_C]
  rw [eval₂_eq_eval_map, eval_add_of_sq_eq_zero _ _ _ (sq_inr μ), derivative_map,
    ← eval₂_eq_eval_map, ← eval₂_eq_eval_map]
  rw [show (inl z : TrivSqZeroExt S M) = inlHom S M z from rfl, ← hom_eval₂, ← hom_eval₂,
    inlHom_apply, inlHom_apply, inl_mul_inr]

/- English proof (translation)
Simplify using `[sqEv]`.
-/
theorem sqEv_X (z q : S) (μ ν : M) : sqEv (A := A) z q μ ν X = inl q + inr ν := by
  simp [sqEv]

/- English proof (translation)
Establish `: (fstHom S S M).toRingHom.comp (sqEv z q μ ν) = ev2 (A` using `A) z q := by`. Apply `Polynomial.ringHom_ext` to reduce the goal to its premises. Introduce `g`. Simplify using `[sqEv_C, ev2]`. Simplify using `[sqEv_X, ev2]`.

Conclude with `congrArg (fun φ => φ f) this`.
-/
theorem fst_sqEv (z q : S) (μ ν : M) (f : Polynomial (Polynomial A)) :
    (sqEv z q μ ν f).fst = ev2 z q f := by
  have : (fstHom S S M).toRingHom.comp (sqEv z q μ ν) = ev2 (A := A) z q := by
    apply Polynomial.ringHom_ext
    · intro g
      simp [sqEv_C, ev2]
    · simp [sqEv_X, ev2]
  exact congrArg (fun φ => φ f) this

/- English proof (translation)
Use `eval_add_of_sq_eq_zero (X ^ N : Polynomial (TrivSqZeroExt S M)) (inl a) (inr m) (sq_inr m)` as an intermediate fact. Simplify using `only [eval_pow, eval_X, derivative_X_pow, eval_mul, eval_natCast] at this`. Rewrite using `[this, eval_C, inl_pow, inl_pow, ← inl_natCast, ← inl_mul, inl_mul_inr]`.
-/
theorem pow_inl_add_inr (a : S) (m : M) (N : ℕ) :
    (inl a + inr m : TrivSqZeroExt S M) ^ N = inl (a ^ N) + inr (((N : S) * a ^ (N - 1)) • m) := by
  have := eval_add_of_sq_eq_zero (X ^ N : Polynomial (TrivSqZeroExt S M)) (inl a) (inr m) (sq_inr m)
  simp only [eval_pow, eval_X, derivative_X_pow, eval_mul, eval_natCast] at this
  rw [this, eval_C, inl_pow, inl_pow, ← inl_natCast, ← inl_mul, inl_mul_inr]

end Gen
end LevDer
end GlobalTheory.AlmostEt

noncomputable section
namespace GlobalTheory.AlmostEt.LevDer
open Polynomial TrivSqZeroExt

section Gen2
variable {A S M : Type} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M]
  [Module Sᵐᵒᵖ M] [IsCentralScalar S M]

/- English proof (translation)
Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Break down `hx with rfl | rfl` into its components or cases. Conclude with `⟨C X, by simp [ev2]⟩`. Conclude with `⟨X, by simp [ev2]⟩`.

Consider the case `algebraMap a => exact ⟨C (C a), by simp [ev2]⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨f, rfl⟩` from `hx`. Take `⟨g, rfl⟩` from `hy`. Conclude with `⟨f + g, map_add _ _ _⟩`.

Consider the case `mul x y _ _ hx hy`. Take `⟨f, rfl⟩` from `hx`. Take `⟨g, rfl⟩` from `hy`. Conclude with `⟨f * g, map_mul _ _ _⟩`.
-/
theorem exists_evalBivariatePolynomialAt_of_mem_adjoin (z q : S) {x : S} (hx : x ∈ Algebra.adjoin A {z, q}) :
    ∃ f : Polynomial (Polynomial A), ev2 z q f = x := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨C X, by simp [ev2]⟩
    · exact ⟨X, by simp [ev2]⟩
  | algebraMap a => exact ⟨C (C a), by simp [ev2]⟩
  | add x y _ _ hx hy =>
    obtain ⟨f, rfl⟩ := hx
    obtain ⟨g, rfl⟩ := hy
    exact ⟨f + g, map_add _ _ _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨f, rfl⟩ := hx
    obtain ⟨g, rfl⟩ := hy
    exact ⟨f * g, map_mul _ _ _⟩

/- English proof (translation)
Set `D : S → M` to `fun x => (sqEv z q μ ν (Function.invFun (ev2 (A := A) z q) x)).snd`. Establish `key : ∀ f : Polynomial (Polynomial A), D (ev2 z q f) = (sqEv z q μ ν f).snd`. Introduce `f`. Establish `h1 : ev2 z q (Function.invFun (ev2 (A` using `A) z q) (ev2 z q f)) = ev2 z q f := Function.invFun_eq ⟨f, rfl⟩`. Establish `h2` using `hwd (Function.invFun (ev2 (A := A) z q) (ev2 z q f) - f) (by rw [map_sub, h1, sub_self])`.

Rewrite `h2` using `[map_sub, sub_eq_zero]`. Use `show (sqEv z q μ ν (Function.invFun (ev2 (A := A) z q) (ev2 z q f))).snd = _`. Rewrite using `[h2]`. Use `⟨D, ⟨?_, ?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx y hy`.

Take `⟨f, rfl⟩` from `exists_evalBivariatePolynomialAt_of_mem_adjoin z q hx`. Take `⟨g, rfl⟩` from `exists_evalBivariatePolynomialAt_of_mem_adjoin z q hy`. Rewrite using `[← map_add, key, key, key, map_add, snd_add]`. Introduce `x hx y hy`. Take `⟨f, rfl⟩` from `exists_evalBivariatePolynomialAt_of_mem_adjoin z q hx`.

Take `⟨g, rfl⟩` from `exists_evalBivariatePolynomialAt_of_mem_adjoin z q hy`. Rewrite using `[← map_mul, key, key, key, map_mul, snd_mul, op_smul_eq_smul, fst_sqEv, fst_sqEv]`. Introduce `a`. Establish `: algebraMap A S a = ev2 z q (C (C a))` using `by simp [ev2]`. Rewrite using `[this, key, sqEv_C]`.

Simplify using the standard rewrite rules. Establish `: z = ev2 (A` using `A) z q (C X) := by simp [ev2]`. Rewrite using `[this, key, sqEv_C]`. Simplify using the standard rewrite rules. Establish `: q = ev2 (A` using `A) z q X := by simp [ev2]`.

Rewrite using `[this, key, sqEv_X]`. Simplify using the standard rewrite rules.
-/
theorem exists_der_gen (z q : S) (μ ν : M)
    (hwd : ∀ f : Polynomial (Polynomial A), ev2 z q f = 0 → sqEv z q μ ν f = 0) :
    ∃ D : S → M, IsDerOn (Algebra.adjoin A {z, q}) D ∧ D z = μ ∧ D q = ν := by
  classical
  let D : S → M := fun x => (sqEv z q μ ν (Function.invFun (ev2 (A := A) z q) x)).snd
  have key : ∀ f : Polynomial (Polynomial A), D (ev2 z q f) = (sqEv z q μ ν f).snd := by
    intro f
    have h1 : ev2 z q (Function.invFun (ev2 (A := A) z q) (ev2 z q f)) = ev2 z q f :=
      Function.invFun_eq ⟨f, rfl⟩
    have h2 := hwd (Function.invFun (ev2 (A := A) z q) (ev2 z q f) - f) (by rw [map_sub, h1, sub_self])
    rw [map_sub, sub_eq_zero] at h2
    show (sqEv z q μ ν (Function.invFun (ev2 (A := A) z q) (ev2 z q f))).snd = _
    rw [h2]
  refine ⟨D, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨f, rfl⟩ := exists_evalBivariatePolynomialAt_of_mem_adjoin z q hx
    obtain ⟨g, rfl⟩ := exists_evalBivariatePolynomialAt_of_mem_adjoin z q hy
    rw [← map_add, key, key, key, map_add, snd_add]
  · intro x hx y hy
    obtain ⟨f, rfl⟩ := exists_evalBivariatePolynomialAt_of_mem_adjoin z q hx
    obtain ⟨g, rfl⟩ := exists_evalBivariatePolynomialAt_of_mem_adjoin z q hy
    rw [← map_mul, key, key, key, map_mul, snd_mul, op_smul_eq_smul, fst_sqEv, fst_sqEv]
  · intro a
    have : algebraMap A S a = ev2 z q (C (C a)) := by simp [ev2]
    rw [this, key, sqEv_C]
    simp
  · have : z = ev2 (A := A) z q (C X) := by simp [ev2]
    rw [this, key, sqEv_C]
    simp
  · have : q = ev2 (A := A) z q X := by simp [ev2]
    rw [this, key, sqEv_X]
    simp

end Gen2
end LevDer
end GlobalTheory.AlmostEt

noncomputable section
namespace GlobalTheory.AlmostEt.LevDer
open Polynomial TrivSqZeroExt

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

abbrev ev (T : Tower p Ω) (n : ℕ) :
    Polynomial (Polynomial (O0 p)) →+* integralClosure (O0 p) Ω :=
  ev2 (zS T n) (qS T n)

/- English proof (translation)
The claim follows from `IsPrimitiveRoot.of_map_of_injective (f := (integralClosure (O0 p) Ω).val.toRingHom) (T.prim n) Subtype.val_injective`.
-/
theorem zS_prim (T : Tower p Ω) (n : ℕ) : IsPrimitiveRoot (zS T n) (p ^ n) :=
  IsPrimitiveRoot.of_map_of_injective (f := (integralClosure (O0 p) Ω).val.toRingHom)
    (T.prim n) Subtype.val_injective

/- English proof (translation)
The claim follows from `Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact GlobalTheory.AlmostEt.qq_pow T n)`.
-/
theorem qS_pow (T : Tower p Ω) (n : ℕ) :
    qS T n ^ p ^ n = algebraMap (O0 p) (integralClosure (O0 p) Ω) (qO p) :=
  Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact GlobalTheory.AlmostEt.qq_pow T n)

/- English proof (translation)
Establish `hpos : 0 < p ^ n` using `pow_pos (Fact.out : p.Prime).pos n`. Use `(zS_prim T n).isRoot_cyclotomic hpos` as an intermediate fact. Rewrite using `[eval₂_eq_eval_map, map_cyclotomic]`. Conclude with `this`.
-/
theorem aeval_cyc (T : Tower p Ω) (n : ℕ) :
    eval₂ (algebraMap (O0 p) (integralClosure (O0 p) Ω)) (zS T n) (cyclotomic (p ^ n) (O0 p)) = 0 := by
  have hpos : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  have := (zS_prim T n).isRoot_cyclotomic hpos
  rw [eval₂_eq_eval_map, map_cyclotomic]
  exact this

/- English proof (translation)
Rewrite using `[towerIdeal, Ideal.span_le]`. Introduce and unpack `b (rfl | rfl)`. Simplify using `only [SetLike.mem_coe, RingHom.mem_ker, ev, ev2, coe_eval₂RingHom, eval₂_C]`. Conclude with `aeval_cyc T n`. Simplify using `only [SetLike.mem_coe, RingHom.mem_ker, ev, ev2, coe_eval₂RingHom, eval₂_sub, eval₂_X_pow, eval₂_C, qS_pow, sub_self]`.
-/
theorem le_ker_ev (T : Tower p Ω) (n : ℕ) : towerIdeal p n ≤ RingHom.ker (ev T n) := by
  rw [towerIdeal, Ideal.span_le]
  rintro b (rfl | rfl)
  · simp only [SetLike.mem_coe, RingHom.mem_ker, ev, ev2, coe_eval₂RingHom, eval₂_C]
    exact aeval_cyc T n
  · simp only [SetLike.mem_coe, RingHom.mem_ker, ev, ev2, coe_eval₂RingHom, eval₂_sub, eval₂_X_pow,
      eval₂_C, qS_pow, sub_self]

def kap (T : Tower p Ω) (n : ℕ) : On p n →+* integralClosure (O0 p) Ω :=
  Ideal.Quotient.lift _ (ev T n) (le_ker_ev T n)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem kap_mk (T : Tower p Ω) (n : ℕ) (f : Polynomial (Polynomial (O0 p))) :
    kap T n (Ideal.Quotient.mk _ f) = ev T n f := rfl

/- English proof (translation)
Take `⟨f, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Establish `h1 : ∀ c, ι (Ideal.Quotient.mk (towerIdeal p n) (C (C c))) = algebraMap (O0 p) Ω c` using `fun c => ι.commutes c`. Establish `h2 : ι (Ideal.Quotient.mk (towerIdeal p n) (C X)) = T.ζ n` using `hι.1`. Establish `h3 : ι (Ideal.Quotient.mk (towerIdeal p n) X) = T.qq n` using `hι.2`. Establish `: ((integralClosure (O0 p) Ω).val.toRingHom.comp (ev T n)) = (ι.toRingHom.comp (Ideal.Quotient.mk (towerIdeal p n)))`.

Apply `Polynomial.ringHom_ext` to reduce the goal to its premises. Introduce `g`. Proceed by induction on `g using Polynomial.induction_on' with`. Consider the case `add g h hg hh => rw [C_add, map_add, map_add, hg, hh]`. Consider the case `monomial k c`.

Rewrite using `[← C_mul_X_pow_eq_monomial, C_mul, C_pow]`. Simplify using `only [RingHom.coe_comp, Function.comp_apply, map_mul, map_pow, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h1, h2]`. Simplify using `only [ev, ev2, coe_eval₂RingHom, eval₂_C, eval₂_X, Subalgebra.coe_val, AlgHom.coe_toRingHom]`. Both sides reduce to the same expression. Simplify using `only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h3]`.

Simplify using `only [ev, ev2, coe_eval₂RingHom, eval₂_X, Subalgebra.coe_val, AlgHom.coe_toRingHom]`. Both sides reduce to the same expression. Conclude with `congrArg (fun φ => φ f) this`.
-/
theorem kap_eq (T : Tower p Ω) (n : ℕ) (ι : On p n →ₐ[O0 p] Ω) (hι : IsEmb T n ι) (a : On p n) :
    (kap T n a : Ω) = ι a := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  have h1 : ∀ c, ι (Ideal.Quotient.mk (towerIdeal p n) (C (C c))) = algebraMap (O0 p) Ω c :=
    fun c => ι.commutes c
  have h2 : ι (Ideal.Quotient.mk (towerIdeal p n) (C X)) = T.ζ n := hι.1
  have h3 : ι (Ideal.Quotient.mk (towerIdeal p n) X) = T.qq n := hι.2
  have : ((integralClosure (O0 p) Ω).val.toRingHom.comp (ev T n)) =
      (ι.toRingHom.comp (Ideal.Quotient.mk (towerIdeal p n))) := by
    apply Polynomial.ringHom_ext
    · intro g
      induction g using Polynomial.induction_on' with
      | add g h hg hh => rw [C_add, map_add, map_add, hg, hh]
      | monomial k c =>
        rw [← C_mul_X_pow_eq_monomial, C_mul, C_pow]
        simp only [RingHom.coe_comp, Function.comp_apply, map_mul, map_pow, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe, h1, h2]
        simp only [ev, ev2, coe_eval₂RingHom, eval₂_C, eval₂_X, Subalgebra.coe_val, AlgHom.coe_toRingHom]
        rfl
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h3]
      simp only [ev, ev2, coe_eval₂RingHom, eval₂_X, Subalgebra.coe_val, AlgHom.coe_toRingHom]
      rfl
  exact congrArg (fun φ => φ f) this

set_option synthInstance.maxHeartbeats 400000 in
/- English proof (translation)
Rewrite using `[towerIdeal, Ideal.span_le]`. Introduce and unpack `b (rfl | rfl)`. Rewrite using `[SetLike.mem_coe, RingHom.mem_ker, sqEv_C, aeval_cyc, ← aeval_def, hμ, inl_zero, inr_zero, add_zero]`. Rewrite using `[SetLike.mem_coe, RingHom.mem_ker, map_sub, map_pow, sqEv_X, sqEv_C, pow_inl_add_inr, Nat.cast_pow, hν, qS_pow]`. Simplify using the standard rewrite rules.
-/
theorem le_ker_sqEv (T : Tower p Ω) (n : ℕ) {M : Type} [AddCommGroup M]
    [Module (integralClosure (O0 p) Ω) M] [Module (integralClosure (O0 p) Ω)ᵐᵒᵖ M]
    [IsCentralScalar (integralClosure (O0 p) Ω) M] (μ ν : M)
    (hμ : (Polynomial.aeval (zS T n) (Polynomial.derivative (Polynomial.cyclotomic (p ^ n) (O0 p)))) • μ = 0)
    (hν : ((p : (integralClosure (O0 p) Ω)) ^ n * qS T n ^ (p ^ n - 1)) • ν = 0) :
    towerIdeal p n ≤ RingHom.ker (sqEv (A := O0 p) (zS T n) (qS T n) μ ν) := by
  rw [towerIdeal, Ideal.span_le]
  rintro b (rfl | rfl)
  · rw [SetLike.mem_coe, RingHom.mem_ker, sqEv_C, aeval_cyc, ← aeval_def, hμ, inl_zero, inr_zero,
      add_zero]
  · rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_pow, sqEv_X, sqEv_C, pow_inl_add_inr,
      Nat.cast_pow, hν, qS_pow]
    simp

end LevDer
end GlobalTheory.AlmostEt

namespace GlobalTheory.AlmostEt.LevDer
open Polynomial TrivSqZeroExt

/- English proof (translation)
Introduce `p _ Ω _ _ hc T n hn M _ _ μ ν hμ hν`. Use `letI : Module (integralClosure (O0 p) Ω)ᵐᵒᵖ M := Module.compHom _ ((RingHom.id _).fromOpposite fun _ _ => mul_comm _ _)`. Use `haveI : IsCentralScalar (integralClosure (O0 p) Ω) M := ⟨fun _ _ => rfl⟩`. Take `⟨ι, hι⟩` from `GlobalTheory.K5.Basic.exists_isEmb T n`. Establish `hinj` using `GlobalTheory.T.tower_embedding_injective p Ω hc T n hn ι hι`.

Establish `hk : Function.Injective (kap T n)`. Introduce `a b hab`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[← kap_eq T n ι hι, ← kap_eq T n ι hι, hab]`. Use `exists_der_gen (A := O0 p) (zS T n) (qS T n) μ ν fun f hf => ?_` and prove the remaining obligations.

Establish `h0 : Ideal.Quotient.mk (towerIdeal p n) f = 0` using `hk (by rw [kap_mk, map_zero]; exact hf)`. Rewrite `h0` using `[Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `le_ker_sqEv T n μ ν hμ hν h0`.
-/
theorem exists_derOn_levelAlg : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ), 1 ≤ n → ∀ (M : Type) [AddCommGroup M] [Module (integralClosure (O0 p) Ω) M] (μ ν : M), (Polynomial.aeval (zS T n) (Polynomial.derivative (Polynomial.cyclotomic (p ^ n) (O0 p)))) • μ = 0 → ((p : (integralClosure (O0 p) Ω)) ^ n * qS T n ^ (p ^ n - 1)) • ν = 0 → ∃ D : (integralClosure (O0 p) Ω) → M, IsDerOn (levelAlg T n) D ∧ D (zS T n) = μ ∧ D (qS T n) = ν := by
  intro p _ Ω _ _ hc T n hn M _ _ μ ν hμ hν
  letI : Module (integralClosure (O0 p) Ω)ᵐᵒᵖ M :=
    Module.compHom _ ((RingHom.id _).fromOpposite fun _ _ => mul_comm _ _)
  haveI : IsCentralScalar (integralClosure (O0 p) Ω) M := ⟨fun _ _ => rfl⟩
  obtain ⟨ι, hι⟩ := GlobalTheory.K5.Basic.exists_isEmb T n
  have hinj := GlobalTheory.T.tower_embedding_injective p Ω hc T n hn ι hι
  have hk : Function.Injective (kap T n) := by
    intro a b hab
    apply hinj
    rw [← kap_eq T n ι hι, ← kap_eq T n ι hι, hab]
  refine exists_der_gen (A := O0 p) (zS T n) (qS T n) μ ν fun f hf => ?_
  have h0 : Ideal.Quotient.mk (towerIdeal p n) f = 0 := hk (by rw [kap_mk, map_zero]; exact hf)
  rw [Ideal.Quotient.eq_zero_iff_mem] at h0
  exact le_ker_sqEv T n μ ν hμ hν h0

end LevDer
end GlobalTheory.AlmostEt
