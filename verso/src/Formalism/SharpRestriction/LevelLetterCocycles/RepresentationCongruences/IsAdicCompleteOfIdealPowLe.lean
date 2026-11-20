import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsGaloisExtendingAlgHom

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

/- English proof (translation)
Establish `mono : ∀ {A B : Ideal R}, A ≤ B → ∀ n : ℕ, A ^ n ≤ B ^ n`. Introduce `A B h n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ k ih`.

Rewrite using `[pow_succ, pow_succ]`. Conclude with `Ideal.mul_mono ih h`. Establish `hIJn : ∀ n : ℕ, I ^ (e * n) ≤ J ^ n` using `fun n => by`. Rewrite using `[pow_mul]`. Conclude with `mono hIJ n`.

Establish `hJIn : ∀ n : ℕ, J ^ n ≤ I ^ n` using `fun n => mono hJI n`. Establish `hle : ∀ n : ℕ, n ≤ e * n` using `fun n => by nlinarith`. Use `{ haus' := ?_, prec' := ?_ }` and prove the remaining obligations. Introduce `x hx`. Conclude with `hJ.haus' x fun n => (hx (e * n)).mono (Submodule.smul_mono_left (hIJn n))`.

Introduce `f hf`. Take `⟨L, hL⟩` from `hJ.prec' (fun k => f (e * k)) (fun {m n} hmn => (hf (Nat.mul_le_mul le_rfl hmn)).mono (Submodule.smul_mono_left (hIJn m)))`. Use `⟨L, fun n => ?_⟩` and prove the remaining obligations. Conclude with `(hf (hle n)).trans ((hL n).mono (Submodule.smul_mono_left (hJIn n)))`.
-/
theorem isAdicComplete_of_ideal_pow_le {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I J : Ideal R) [hJ : IsAdicComplete J M] (e : ℕ) (he : 1 ≤ e) (hJI : J ≤ I) (hIJ : I ^ e ≤ J) :
    IsAdicComplete I M := by
  have mono : ∀ {A B : Ideal R}, A ≤ B → ∀ n : ℕ, A ^ n ≤ B ^ n := by
    intro A B h n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_succ]
      exact Ideal.mul_mono ih h
  have hIJn : ∀ n : ℕ, I ^ (e * n) ≤ J ^ n := fun n => by
    rw [pow_mul]
    exact mono hIJ n
  have hJIn : ∀ n : ℕ, J ^ n ≤ I ^ n := fun n => mono hJI n
  have hle : ∀ n : ℕ, n ≤ e * n := fun n => by nlinarith
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    exact hJ.haus' x fun n => (hx (e * n)).mono (Submodule.smul_mono_left (hIJn n))
  · intro f hf
    obtain ⟨L, hL⟩ := hJ.prec' (fun k => f (e * k)) (fun {m n} hmn =>
      (hf (Nat.mul_le_mul le_rfl hmn)).mono (Submodule.smul_mono_left (hIJn m)))
    refine ⟨L, fun n => ?_⟩
    exact (hf (hle n)).trans ((hL n).mono (Submodule.smul_mono_left (hJIn n)))

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17 in
/- English proof (translation)
Introduce `l _ LL`. Establish `hc : IsAdicComplete (Ideal.span {((l : ℕ) : ↥(OL LL))}) ↥(OL LL)` using `Formalism.MainNotions.LiftingTheory.phib_OL_complete LL`. Establish `hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0`. Introduce `h`. Establish `h'` using `congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h`.

Simplify using `only [map_natCast, ZeroMemClass.coe_zero] at h'`. Establish `hp : (l : ℕ) ≠ 0` using `(Fact.out : l.Prime).ne_zero`. Conclude with `hp (by exact_mod_cast h')`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible ↥(OL LL)`. Take `⟨k, u, hk⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ`.

Establish `hmax : IsLocalRing.maximalIdeal ↥(OL LL) = Ideal.span {ϖ}` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ`. Establish `hspan : Ideal.span {((l : ℕ) : ↥(OL LL))} = IsLocalRing.maximalIdeal ↥(OL LL) ^ k`. Rewrite using `[hmax, Ideal.span_singleton_pow, hk, Ideal.span_singleton_mul_left_unit u.isUnit]`. Establish `hk1 : 1 ≤ k`. Assume the negation of the conclusion as `hlt`.

Establish `hk0 : k = 0` using `by omega`. Establish `htop : Ideal.span {((l : ℕ) : ↥(OL LL))} = ⊤`. Rewrite using `[hspan, hk0, pow_zero, Ideal.one_eq_top]`. Establish `h10 : (1 : ↥(OL LL)) = 0`. Apply `hc.haus' 1` to reduce the goal to its premises.

Introduce `m`. Rewrite using `[SModEq.sub_mem, htop, Ideal.top_pow, Submodule.top_smul]`. Conclude with `Submodule.mem_top`. Conclude with `one_ne_zero h10`. Use `isAdicComplete_of_ideal_pow_le (IsLocalRing.maximalIdeal ↥(OL LL)) (Ideal.span {((l : ℕ) : ↥(OL LL))}) k hk1 ?_ ?_` and prove the remaining obligations.

Rewrite using `[hspan]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hspan]`.
-/
theorem isAdicComplete_integers_local : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l),
    IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := by
  intro l _ LL
  have hc : IsAdicComplete (Ideal.span {((l : ℕ) : ↥(OL LL))}) ↥(OL LL) :=
    Formalism.MainNotions.LiftingTheory.phib_OL_complete LL

  have hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
    intro h
    have h' := congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h
    simp only [map_natCast, ZeroMemClass.coe_zero] at h'
    have hp : (l : ℕ) ≠ 0 := (Fact.out : l.Prime).ne_zero
    exact hp (by exact_mod_cast h')
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(OL LL)
  obtain ⟨k, u, hk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  have hmax : IsLocalRing.maximalIdeal ↥(OL LL) = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hspan : Ideal.span {((l : ℕ) : ↥(OL LL))} = IsLocalRing.maximalIdeal ↥(OL LL) ^ k := by
    rw [hmax, Ideal.span_singleton_pow, hk, Ideal.span_singleton_mul_left_unit u.isUnit]

  have hk1 : 1 ≤ k := by
    by_contra hlt
    have hk0 : k = 0 := by omega
    have htop : Ideal.span {((l : ℕ) : ↥(OL LL))} = ⊤ := by
      rw [hspan, hk0, pow_zero, Ideal.one_eq_top]
    have h10 : (1 : ↥(OL LL)) = 0 := by
      apply hc.haus' 1
      intro m
      rw [SModEq.sub_mem, htop, Ideal.top_pow, Submodule.top_smul]
      exact Submodule.mem_top
    exact one_ne_zero h10
  refine isAdicComplete_of_ideal_pow_le (IsLocalRing.maximalIdeal ↥(OL LL))
    (Ideal.span {((l : ℕ) : ↥(OL LL))}) k hk1 ?_ ?_
  · rw [hspan]
    calc IsLocalRing.maximalIdeal ↥(OL LL) ^ k ≤ IsLocalRing.maximalIdeal ↥(OL LL) ^ 1 :=
          Ideal.pow_le_pow_right hk1
      _ = IsLocalRing.maximalIdeal ↥(OL LL) := pow_one _
  · rw [hspan]

end Formalism.MainNotions.N.Ln17
