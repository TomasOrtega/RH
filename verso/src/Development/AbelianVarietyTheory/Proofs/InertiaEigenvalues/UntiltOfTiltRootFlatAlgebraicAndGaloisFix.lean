import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.MemLoc

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Proceed by induction on `n generalizing e with`. Consider the case `zero => simp [rootT]`. Consider the case `succ n ih`. Establish `h : rootT e (n + 1) = rootT ((frobeniusEquiv (Per.Fl l) l).symm e) n`. Rewrite using `[rootT, rootT, Function.iterate_succ_apply]`.

Rewrite using `[h, pow_succ, pow_mul, ih, ← map_pow, frobeniusEquiv_symm_pow_p]`.
-/
theorem rootT_pow_eq_untilt (e : Per.Fl l) (n : ℕ) : rootT e n ^ (l ^ n) = e.untilt := by
  induction n generalizing e with
  | zero => simp [rootT]
  | succ n ih =>
    have h : rootT e (n + 1) = rootT ((frobeniusEquiv (Per.Fl l) l).symm e) n := by
      rw [rootT, rootT, Function.iterate_succ_apply]
    rw [h, pow_succ, pow_mul, ih, ← map_pow, frobeniusEquiv_symm_pow_p]

end GlobalTheory.MemLoc

namespace GlobalTheory.BSP

/- English proof (translation)
Introduce `l _ K bk`. Use `⟨fun n => ?_, fun g y hy => ?_⟩` and prove the remaining obligations. Use `set r : ↥(OL K) := bk.str.symm (Ideal.Quotient.mk _ X) with hr`. Establish `h1 : (GlobalTheory.MemLoc.rootT bk.flat n) ^ (l ^ n) = intToOC K r`. Rewrite using `[GlobalTheory.MemLoc.rootT_pow_eq_untilt, ← WittVector.fontaineTheta_teichmuller, ← bk.ev_X]`.

Conclude with `bk.θ_ev r X (by rw [hr, RingEquiv.apply_symm_apply])`. Use `set a : Om l := ((r : ↥K.1) : Om l)`. Establish `hf : (Polynomial.X ^ (l ^ n) - Polynomial.C a : Polynomial (Om l)) ≠ 0` using `Polynomial.X_pow_sub_C_ne_zero (pow_pos (Fact.out : l.Prime).pos n) a`. Establish `hroot : ((Polynomial.X ^ (l ^ n) - Polynomial.C a : Polynomial (Om l)).map (algebraMap (Om l) ℂ_[l])).IsRoot ((GlobalTheory.MemLoc.rootT bk.flat n : OC l) : ℂ_[l])`. Establish `h2` using `congrArg (fun x : OC l => (x : ℂ_[l])) h1`.

Rewrite `h2` using `[SubmonoidClass.coe_pow]`. Rewrite `h2` using `[coe_intToOC]`. Simplify using `only [Polynomial.IsRoot, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]`. Rewrite using `[h2]`. Conclude with `sub_self _`.

Take `⟨z, hz⟩` from `(IsAlgClosed.splits _).mem_range_of_isRoot hf hroot`. Conclude with `⟨z, hz.symm⟩`. Use `Perfection.ext fun n => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `PreTilt.coeff n (Per.σF g bk.flat) = PreTilt.coeff n y`. Establish `hit : ∀ k : ℕ, ((frobeniusEquiv (Per.Fl l) l).symm)^[k] (Per.σF g bk.flat) = Per.σF g (((frobeniusEquiv (Per.Fl l) l).symm)^[k] bk.flat)`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => exact Eq.refl (Per.σF g bk.flat)`. Consider the case `succ k ih`. Rewrite using `[Function.iterate_succ_apply', Function.iterate_succ_apply', ih, RingHom.map_frobeniusEquiv_symm]`.

Establish `hsig : GlobalTheory.MemLoc.rootT (Per.σF g bk.flat) n = Per.σO g (GlobalTheory.MemLoc.rootT bk.flat n)`. Rewrite using `[GlobalTheory.MemLoc.rootT, GlobalTheory.MemLoc.rootT, hit, GlobalTheory.RingBasics.untilt_σF]`. Rewrite using `[GlobalTheory.MemLoc.coeff_eq_mk_rootT, GlobalTheory.MemLoc.coeff_eq_mk_rootT, hsig, hy n]`.
-/
theorem rootT_flat_alg_and_fix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ n : ℕ, ∃ z : Om l, ((GlobalTheory.MemLoc.rootT bk.flat n : OC l) : ℂ_[l]) = (z : ℂ_[l])) ∧ ∀ (g : GQ l) (y : OCb l), (∀ n : ℕ, Per.σO g (GlobalTheory.MemLoc.rootT bk.flat n) = GlobalTheory.MemLoc.rootT y n) → Per.σF g bk.flat = y := by
  intro l _ K bk
  refine ⟨fun n => ?_, fun g y hy => ?_⟩
  · set r : ↥(OL K) := bk.str.symm (Ideal.Quotient.mk _ X) with hr
    have h1 : (GlobalTheory.MemLoc.rootT bk.flat n) ^ (l ^ n) = intToOC K r := by
      rw [GlobalTheory.MemLoc.rootT_pow_eq_untilt, ← WittVector.fontaineTheta_teichmuller, ← bk.ev_X]
      exact bk.θ_ev r X (by rw [hr, RingEquiv.apply_symm_apply])
    set a : Om l := ((r : ↥K.1) : Om l)
    have hf : (Polynomial.X ^ (l ^ n) - Polynomial.C a : Polynomial (Om l)) ≠ 0 :=
      Polynomial.X_pow_sub_C_ne_zero (pow_pos (Fact.out : l.Prime).pos n) a
    have hroot : ((Polynomial.X ^ (l ^ n) - Polynomial.C a : Polynomial (Om l)).map (algebraMap (Om l) ℂ_[l])).IsRoot
        ((GlobalTheory.MemLoc.rootT bk.flat n : OC l) : ℂ_[l]) := by
      have h2 := congrArg (fun x : OC l => (x : ℂ_[l])) h1
      rw [SubmonoidClass.coe_pow] at h2
      rw [coe_intToOC] at h2
      simp only [Polynomial.IsRoot, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
      rw [h2]
      exact sub_self _
    obtain ⟨z, hz⟩ := (IsAlgClosed.splits _).mem_range_of_isRoot hf hroot
    exact ⟨z, hz.symm⟩
  · refine Perfection.ext fun n => ?_
    change PreTilt.coeff n (Per.σF g bk.flat) = PreTilt.coeff n y
    have hit : ∀ k : ℕ, ((frobeniusEquiv (Per.Fl l) l).symm)^[k] (Per.σF g bk.flat) =
        Per.σF g (((frobeniusEquiv (Per.Fl l) l).symm)^[k] bk.flat) := by
      intro k
      induction k with
      | zero => exact Eq.refl (Per.σF g bk.flat)
      | succ k ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, RingHom.map_frobeniusEquiv_symm]
    have hsig : GlobalTheory.MemLoc.rootT (Per.σF g bk.flat) n = Per.σO g (GlobalTheory.MemLoc.rootT bk.flat n) := by
      rw [GlobalTheory.MemLoc.rootT, GlobalTheory.MemLoc.rootT, hit, GlobalTheory.RingBasics.untilt_σF]
    rw [GlobalTheory.MemLoc.coeff_eq_mk_rootT, GlobalTheory.MemLoc.coeff_eq_mk_rootT, hsig, hy n]

end GlobalTheory.BSP
