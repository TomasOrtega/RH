import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFontaineThetaOnAinf

noncomputable section

namespace GlobalTheory.Cyc.Decomp

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `hl : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Establish `hn : ‖((l : ℕ) : PadicComplex l)‖ = (l : ℝ)⁻¹`. Establish `h` using `norm_zC ((l : ℕ) : ℤ_[l])`. Rewrite `h` using `[PadicInt.norm_p]`. Rewrite using `[← h]`.

Simplify using `[zC]`. Establish `key : ∀ k : ℕ, ‖((f x - g x : OC l) : PadicComplex l)‖ ≤ ((l : ℝ)⁻¹) ^ k`. Introduce `k`. Take `⟨y, hy⟩` from `Ideal.mem_span_singleton'.1 (PadicInt.appr_spec k x)`. Establish `hx : x = (x.appr k : ℤ_[l]) + y * (l : ℤ_[l]) ^ k` using `by rw [hy]; ring`.

Establish `h1 : f x - g x = (f y - g y) * ((l : ℕ) : OC l) ^ k` using `by conv_lhs => rw [hx]`. Simplify using `only [map_add, map_mul, map_pow, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : ((f x - g x : OC l) : PadicComplex l) = ((f y - g y : OC l) : PadicComplex l) * ((l : ℕ) : PadicComplex l) ^ k`. Rewrite using `[h1]`.

Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[h2, norm_mul, norm_pow, hn]`. Conclude with `mul_le_of_le_one_left (by positivity) ((mem_OC _).1 (f y - g y).2)`. Establish `h0 : ‖((f x - g x : OC l) : PadicComplex l)‖ ≤ 0` using `ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hl)) key`.

Establish `h3 : f x - g x = 0` using `Subtype.ext (norm_le_zero_iff.1 h0)`. Conclude with `sub_eq_zero.1 h3`.
-/
theorem ringHom_padicInt_OC_ext (f g : ℤ_[l] →+* OC l) (x : ℤ_[l]) : f x = g x := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hn : ‖((l : ℕ) : PadicComplex l)‖ = (l : ℝ)⁻¹ := by
    have h := norm_zC ((l : ℕ) : ℤ_[l])
    rw [PadicInt.norm_p] at h
    rw [← h]
    simp [zC]
  have key : ∀ k : ℕ, ‖((f x - g x : OC l) : PadicComplex l)‖ ≤ ((l : ℝ)⁻¹) ^ k := by
    intro k
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec k x)
    have hx : x = (x.appr k : ℤ_[l]) + y * (l : ℤ_[l]) ^ k := by rw [hy]; ring
    have h1 : f x - g x = (f y - g y) * ((l : ℕ) : OC l) ^ k := by
      conv_lhs => rw [hx]
      simp only [map_add, map_mul, map_pow, map_natCast]
      ring
    have h2 : ((f x - g x : OC l) : PadicComplex l) =
        ((f y - g y : OC l) : PadicComplex l) * ((l : ℕ) : PadicComplex l) ^ k := by
      rw [h1]; push_cast; rfl
    rw [h2, norm_mul, norm_pow, hn]
    exact mul_le_of_le_one_left (by positivity) ((mem_OC _).1 (f y - g y).2)
  have h0 : ‖((f x - g x : OC l) : PadicComplex l)‖ ≤ 0 :=
    ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      (inv_lt_one_of_one_lt₀ hl)) key
  have h3 : f x - g x = 0 := Subtype.ext (norm_le_zero_iff.1 h0)
  exact sub_eq_zero.1 h3

/- English proof (translation)
Apply `(frobeniusEquiv (OCb l) l).injective` to reduce the goal to its premises. Rewrite using `[RingEquiv.apply_symm_apply, frobeniusEquiv_apply, frobenius_def, ← map_pow, frobeniusEquiv_symm_pow_p]`.
-/
theorem map_frobeniusEquiv_symm_OCb (e : OCb l →+* OCb l) (x : OCb l) :
    e ((frobeniusEquiv (OCb l) l).symm x) = (frobeniusEquiv (OCb l) l).symm (e x) := by
  apply (frobeniusEquiv (OCb l) l).injective
  rw [RingEquiv.apply_symm_apply, frobeniusEquiv_apply, frobenius_def, ← map_pow,
    frobeniusEquiv_symm_pow_p]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Take `⟨θ, -, -, h1, -, h2⟩` from `exists_isTheta l P AI`. Conclude with `⟨θ, h1, h2⟩`. Consider the case `succ n ih`.

Take `⟨θ, h1, h2⟩` from `ih`. Use `⟨θ.comp (WittVector.map (frobeniusEquiv (OCb l) l).symm.toRingHom), fun g a => ?_, fun j => ?_⟩` and prove the remaining obligations. Establish `e : WittVector.map (frobeniusEquiv (OCb l) l).symm.toRingHom (AI.actW g a) = AI.actW g (WittVector.map (frobeniusEquiv (OCb l) l).symm.toRingHom a)` using `WittVector.ext fun k => (map_frobeniusEquiv_symm_OCb (AI.actT g).toRingHom (a.coeff k)).symm`. Rewrite using `[RingHom.comp_apply, RingHom.comp_apply, e, h1]`. Establish `e : (frobeniusEquiv (OCb l) l).symm.toRingHom (AI.εroot j) = AI.εroot (j + 1)`.

Rewrite using `[LocAinf.εroot, LocAinf.εroot, Function.iterate_succ_apply']`. Both sides reduce to the same expression. Rewrite using `[RingHom.comp_apply, WittVector.map_teichmuller, e, h2, add_assoc, add_comm 1 n]`.
-/
theorem exists_thetaShift_ringHom {P : LocPrime l} (AI : LocAinf l P) (n : ℕ) :
    ∃ θ : Ainf l →+* OC l,
      (∀ (g : GQ l) (a : Ainf l), ((θ (AI.actW g a) : OC l) : PadicComplex l) =
        AI.actC g ((θ a : OC l) : PadicComplex l)) ∧
      ∀ j : ℕ, θ (WittVector.teichmuller l (AI.εroot j)) = AI.ζ (j + n) := by
  induction n with
  | zero =>
    obtain ⟨θ, -, -, h1, -, h2⟩ := exists_isTheta l P AI
    exact ⟨θ, h1, h2⟩
  | succ n ih =>
    obtain ⟨θ, h1, h2⟩ := ih
    refine ⟨θ.comp (WittVector.map (frobeniusEquiv (OCb l) l).symm.toRingHom), fun g a => ?_,
      fun j => ?_⟩
    · have e : WittVector.map (frobeniusEquiv (OCb l) l).symm.toRingHom (AI.actW g a) =
          AI.actW g (WittVector.map (frobeniusEquiv (OCb l) l).symm.toRingHom a) :=
        WittVector.ext fun k =>
          (map_frobeniusEquiv_symm_OCb (AI.actT g).toRingHom (a.coeff k)).symm
      rw [RingHom.comp_apply, RingHom.comp_apply, e, h1]
    · have e : (frobeniusEquiv (OCb l) l).symm.toRingHom (AI.εroot j) = AI.εroot (j + 1) := by
        rw [LocAinf.εroot, LocAinf.εroot, Function.iterate_succ_apply']
        rfl
      rw [RingHom.comp_apply, WittVector.map_teichmuller, e, h2, add_assoc, add_comm 1 n]

/- English proof (translation)
Introduce `l _ P AI n`. Take `⟨θ, h1, h2⟩` from `exists_thetaShift_ringHom AI n`. Conclude with `⟨{ toRingHom := θ commutes' := fun x => ringHom_padicInt_OC_ext (θ.comp (algebraMap ℤ_[l] (Ainf l))) (algebraMap ℤ_[l] (OC l)) x }, fun g a => h1 g a, h2⟩`.
-/
theorem exists_isThetaShift : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (n : ℕ),
    ∃ θ : Ainf l →ₐ[ℤ_[l]] OC l, IsThetaShift AI n θ := by
  intro l _ P AI n
  obtain ⟨θ, h1, h2⟩ := exists_thetaShift_ringHom AI n
  exact ⟨{ toRingHom := θ
           commutes' := fun x => ringHom_padicInt_OC_ext (θ.comp (algebraMap ℤ_[l] (Ainf l)))
             (algebraMap ℤ_[l] (OC l)) x }, fun g a => h1 g a, h2⟩

end GlobalTheory.Cyc.Decomp
