import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisLoc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.TiedMu

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [pow_succ', pow_mul, Nat.add_right_comm, AI.ζ_succ, ih]`.
-/
theorem zeta_pow (AI : LocAinf l P) (k n : ℕ) : AI.ζ (n + k) ^ l ^ n = AI.ζ k := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, Nat.add_right_comm, AI.ζ_succ, ih]

/- English proof (translation)
Use `Perfection.teichmuller_spec (I := Ideal.span {(l : Per.OC l)}) fun n => ?_` and prove the remaining obligations. Use `⟨AI.ζ n, (AI.ε_coeff n).symm, ?_⟩` and prove the remaining obligations. Establish `h` using `zeta_pow AI 0 n`. Rewrite `h` using `[add_zero, AI.ζ_zero]`. Rewrite using `[h]`.
-/
theorem untilt_eps (AI : LocAinf l P) : AI.ε.untilt = 1 := by
  refine Perfection.teichmuller_spec (I := Ideal.span {(l : Per.OC l)}) fun n => ?_
  refine ⟨AI.ζ n, (AI.ε_coeff n).symm, ?_⟩
  have h := zeta_pow AI 0 n
  rw [add_zero, AI.ζ_zero] at h
  rw [h]

/- English proof (translation)
Use `Perfection.teichmuller_spec (I := Ideal.span {(l : Per.OC l)}) fun n => ?_` and prove the remaining obligations. Use `⟨AI.ζ (n + 1), ?_, ?_⟩` and prove the remaining obligations. Use `(AI.ε_coeff (n + 1)).symm.trans ?_` and prove the remaining obligations. Establish `h : AI.ε = AI.ε1 ^ l` using `by rw [LocAinf.ε1, frobeniusEquiv_symm_pow_p]`. Rewrite using `[h]`.

Conclude with `Perfection.coeff_pow_p _ _`. Rewrite using `[zeta_pow AI 1 n]`.
-/
theorem locAinf_untilt_epsOne_eq_zeta (AI : LocAinf l P) : AI.ε1.untilt = AI.ζ 1 := by
  refine Perfection.teichmuller_spec (I := Ideal.span {(l : Per.OC l)}) fun n => ?_
  refine ⟨AI.ζ (n + 1), ?_, ?_⟩
  · refine (AI.ε_coeff (n + 1)).symm.trans ?_
    have h : AI.ε = AI.ε1 ^ l := by rw [LocAinf.ε1, frobeniusEquiv_symm_pow_p]
    rw [h]
    exact Perfection.coeff_pow_p _ _
  · rw [zeta_pow AI 1 n]

/- English proof (translation)
Introduce `h`. Apply `AI.ζ_one` to reduce the goal to its premises. Rewrite using `[← locAinf_untilt_epsOne_eq_zeta, LocAinf.ε1, h, map_one, map_one]`.
-/
theorem eps_ne_one (AI : LocAinf l P) : AI.ε ≠ 1 := by
  intro h
  apply AI.ζ_one
  rw [← locAinf_untilt_epsOne_eq_zeta, LocAinf.ε1, h, map_one, map_one]

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => simpa using eps_ne_one AI`. Consider the case `succ j ih`. Introduce `h`. Apply `ih` to reduce the goal to its premises.

Apply `(frobeniusEquiv (OCb l) l).injective` to reduce the goal to its premises. Rewrite using `[frobeniusEquiv_apply, frobeniusEquiv_apply, frobenius_def, frobenius_def, ← pow_mul, ← pow_succ, h, one_pow]`.
-/
theorem eps_pow_ne_one (AI : LocAinf l P) (j : ℕ) : AI.ε ^ l ^ j ≠ 1 := by
  induction j with
  | zero => simpa using eps_ne_one AI
  | succ j ih =>
    intro h
    apply ih
    apply (frobeniusEquiv (OCb l) l).injective
    rw [frobeniusEquiv_apply, frobeniusEquiv_apply, frobenius_def, frobenius_def, ← pow_mul,
      ← pow_succ, h, one_pow]

/- English proof (translation)
Proceed by induction on `s with`. Consider the case `zero => simp [LocAinf.εroot]`. Consider the case `succ s ih`. Rewrite using `[LocAinf.εroot, Function.iterate_succ_apply', pow_succ', pow_mul, frobeniusEquiv_symm_pow_p]`. Conclude with `ih`.
-/
theorem eps_root_pow (AI : LocAinf l P) (s : ℕ) : AI.εroot s ^ l ^ s = AI.ε := by
  induction s with
  | zero => simp [LocAinf.εroot]
  | succ s ih =>
    rw [LocAinf.εroot, Function.iterate_succ_apply', pow_succ', pow_mul, frobeniusEquiv_symm_pow_p]
    exact ih

/- English proof (translation)
The claim follows from `GlobalTheory.CrisLoc.unit_of_root_aB l e he hne`.
-/
theorem isUnit_aB (e : Per.Fl l) (he : e.untilt = 1) (hne : e ≠ 1) :
    IsUnit (Per.aB l (Per.tm e - 1)) :=
  GlobalTheory.CrisLoc.unit_of_root_aB l e he hne

/- English proof (translation)
Rewrite `h` using `[← T.ιA]`. Establish `h'` using `h.map T.eB.symm`. Rewrite `h'` using `[RingEquiv.symm_apply_apply]`. Then use the resulting hypothesis.
-/
theorem isUnit_of_aB {AI : LocAinf l P} (T : LocTied l P AI) (a : Ainf l) (h : IsUnit (Per.aB l a)) :
    IsUnit (AI.ιA a) := by
  rw [← T.ιA] at h
  have h' := h.map T.eB.symm
  rwa [RingEquiv.symm_apply_apply] at h'

/- English proof (translation)
Introduce `l _ P AI T`. Establish `hj : ∀ j : ℕ, IsUnit (AI.ιA (WittVector.teichmuller l (AI.ε ^ l ^ j) - 1))` using `fun j => isUnit_of_aB T _ (isUnit_aB (AI.ε ^ l ^ j) (by rw [map_pow, untilt_eps, one_pow]) (eps_pow_ne_one AI j))`. Establish `hμ : IsUnit (AI.ιA AI.μ)` using `by simpa [LocAinf.μ] using hj 0`. Use `⟨fun s => ?_, hj, ?_, fun z => ?_⟩` and prove the remaining obligations. Establish `h` using `geom_sum_mul (WittVector.teichmuller l (AI.εroot s)) (l ^ s)`.

Rewrite `h` using `[← map_pow, eps_root_pow]`. Rewrite `hμ` using `[LocAinf.μ, ← h, map_mul]`. Conclude with `isUnit_of_mul_isUnit_right hμ`. Rewrite `hμ` using `[AI.μ_eq, map_mul]`. Conclude with `isUnit_of_mul_isUnit_right hμ`.

Apply `T.eB.injective` to reduce the goal to its premises. Rewrite using `[T.ιA, T.zB]`. Conclude with `GlobalTheory.RingIface.aB_algebraMap_padicInt l z`.
-/
theorem tied_mu_units : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → (∀ s : ℕ, IsUnit (AI.ιA (WittVector.teichmuller l (AI.εroot s) - 1))) ∧ (∀ j : ℕ, IsUnit (AI.ιA (WittVector.teichmuller l (AI.ε ^ l ^ j) - 1))) ∧ IsUnit (AI.ιA AI.ξ) ∧ ∀ z : ℤ_[l], AI.ιA (algebraMap ℤ_[l] (Ainf l) z) = algebraMap ℚ_[l] P.R.B (z : ℚ_[l]) := by
  intro l _ P AI T
  have hj : ∀ j : ℕ, IsUnit (AI.ιA (WittVector.teichmuller l (AI.ε ^ l ^ j) - 1)) := fun j =>
    isUnit_of_aB T _ (isUnit_aB (AI.ε ^ l ^ j)
      (by rw [map_pow, untilt_eps, one_pow]) (eps_pow_ne_one AI j))
  have hμ : IsUnit (AI.ιA AI.μ) := by simpa [LocAinf.μ] using hj 0
  refine ⟨fun s => ?_, hj, ?_, fun z => ?_⟩
  · have h := geom_sum_mul (WittVector.teichmuller l (AI.εroot s)) (l ^ s)
    rw [← map_pow, eps_root_pow] at h
    rw [LocAinf.μ, ← h, map_mul] at hμ
    exact isUnit_of_mul_isUnit_right hμ
  · rw [AI.μ_eq, map_mul] at hμ
    exact isUnit_of_mul_isUnit_right hμ
  · apply T.eB.injective
    rw [T.ιA, T.zB]
    exact GlobalTheory.RingIface.aB_algebraMap_padicInt l z

end GlobalTheory.TiedMu
