import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.CoreStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMTraceSurjective.IsTrMulConjOfMem

open NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace PI.SRW

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def CStab (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Prop := ∀ x ∈ I, star x ∈ I

/- English proof (translation)
Assemble the required witnesses or components as `⟨PI.CMT.conj o, PI.CMT.coe_conj o⟩`.
-/
theorem star_int (o : 𝓞 E) : ∃ o' : 𝓞 E, (o' : E) = star (o : E) :=
  ⟨PI.CMT.conj o, PI.CMT.coe_conj o⟩

/- English proof (translation)
Introduce `x hx`. Take `⟨o, rfl⟩` from `(FractionalIdeal.mem_one_iff _).mp hx`. Take `⟨o', ho'⟩` from `star_int o`. Conclude with `(FractionalIdeal.mem_one_iff _).mpr ⟨o', ho'⟩`.
-/
theorem cstab_one : CStab (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
  intro x hx
  obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hx
  obtain ⟨o', ho'⟩ := star_int o
  exact (FractionalIdeal.mem_one_iff _).mpr ⟨o', ho'⟩

/- English proof (translation)
Introduce `x hx`. Use `FractionalIdeal.mul_induction_on (C := fun y => star y ∈ I * J) hx ?_ ?_` and prove the remaining obligations. Introduce `i hi j hj`. Rewrite using `[star_mul']`. Conclude with `FractionalIdeal.mul_mem_mul (hI i hi) (hJ j hj)`.

Introduce `y z hy hz`. Rewrite using `[star_add]`. Conclude with `Submodule.add_mem _ hy hz`.
-/
theorem cstab_mul {I J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E} (hI : CStab I) (hJ : CStab J) :
    CStab (I * J) := by
  intro x hx
  refine FractionalIdeal.mul_induction_on (C := fun y => star y ∈ I * J) hx ?_ ?_
  · intro i hi j hj
    rw [star_mul']
    exact FractionalIdeal.mul_mem_mul (hI i hi) (hJ j hj)
  · intro y z hy hz
    rw [star_add]
    exact Submodule.add_mem _ hy hz

/- English proof (translation)
Introduce `x hx`. Distinguish the cases in `h0 : I = 0`. Rewrite `hx`, the goal using `[h0, inv_zero]`. Rewrite using `[(FractionalIdeal.mem_zero_iff _).mp hx, star_zero]`. Conclude with `(FractionalIdeal.mem_zero_iff _).mpr rfl`.

Rewrite `hx`, the goal using `[FractionalIdeal.mem_inv_iff h0]`. Introduce `y hy`. Establish `h1` using `cstab_one _ (hx (star y) (hI y hy))`. Rewrite `h1` using `[star_mul', star_star]`. Then use the resulting hypothesis.
-/
theorem cstab_inv {I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E} (hI : CStab I) : CStab I⁻¹ := by
  intro x hx
  by_cases h0 : I = 0
  · rw [h0, inv_zero] at hx ⊢
    rw [(FractionalIdeal.mem_zero_iff _).mp hx, star_zero]
    exact (FractionalIdeal.mem_zero_iff _).mpr rfl
  · rw [FractionalIdeal.mem_inv_iff h0] at hx ⊢
    intro y hy
    have h1 := cstab_one _ (hx (star y) (hI y hy))
    rwa [star_mul', star_star] at h1

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using cstab_one`. Consider the case `succ n ih`. Rewrite using `[pow_succ]`. Conclude with `cstab_mul ih hI`.
-/
theorem cstab_pow {I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E} (hI : CStab I) (n : ℕ) :
    CStab (I ^ n) := by
  induction n with
  | zero => simpa using cstab_one
  | succ n ih =>
    rw [pow_succ]
    exact cstab_mul ih hI

/- English proof (translation)
Consider the cases of `n with`. Consider the case `ofNat n`. Rewrite using `[Int.ofNat_eq_natCast, zpow_natCast]`. Conclude with `cstab_pow hI n`. Consider the case `negSucc n`.

Rewrite using `[zpow_negSucc]`. Conclude with `cstab_inv (cstab_pow hI _)`.
-/
theorem cstab_zpow {I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E} (hI : CStab I) (n : ℤ) :
    CStab (I ^ n) := by
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact cstab_pow hI n
  | negSucc n =>
    rw [zpow_negSucc]
    exact cstab_inv (cstab_pow hI _)

end Gen

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Both sides reduce to the same expression.
-/
example (D : D7) (a : 𝓞 D.host.F) :
    ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) = ((a : D.host.F) : D.host.E) := rfl

/- English proof (translation)
The claim follows from `D.sp.cm.fixed a`.
-/
example (D : D7) (a : D.host.E) : star a = a ↔ a ∈ (algebraMap D.host.F D.host.E).range := D.sp.cm.fixed a

/- English proof (translation)
Introduce `D`. Take `⟨x, y, hy, hxy⟩` from `PI.CMT.main D.host.E D.sp.cm.cmUnram 1 (by simp)`. Use `⟨x, ?_⟩` and prove the remaining obligations. Rewrite using `[← hy]`. Conclude with `hxy` after adjusting the coercions.
-/
theorem trace_reduction : TrStep := by
  intro D
  obtain ⟨x, y, hy, hxy⟩ := PI.CMT.main D.host.E D.sp.cm.cmUnram 1 (by simp)
  refine ⟨x, ?_⟩
  rw [← hy]
  exact_mod_cast hxy

/- English proof (translation)
Introduce `a b h`. Establish `h'` using `congrArg ((↑) : 𝓞 D.host.E → D.host.E) h`. Use `ext`. Simplify using `using h'`.
-/
theorem alg_inj (D : D7) : Function.Injective (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
  intro a b h
  have h' := congrArg ((↑) : 𝓞 D.host.E → D.host.E) h
  ext
  simpa using h'

/- English proof (translation)
Rewrite using `[ddS, Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.map_eq_bot_iff_of_injective (alg_inj D)]`. Conclude with `differentIdeal_ne_bot`.
-/
theorem ddS_ne (D : D7) : ddS D ≠ 0 := by
  rw [ddS, Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.map_eq_bot_iff_of_injective (alg_inj D)]
  exact differentIdeal_ne_bot

/- English proof (translation)
Establish `hfix : PI.CMT.conj.comp (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E)`. Use extensionality with `a`. Rewrite using `[RingHom.comp_apply, PI.CMT.coe_conj]`. Use `(D.sp.cm.fixed _).2 ⟨(a : D.host.F), ?_⟩` and prove the remaining obligations. Both sides reduce to the same expression.

Introduce `x hx`. Rewrite `hx`, the goal using `[ddS]`. Take `⟨y, hy, rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).mp hx`. Use `(FractionalIdeal.mem_coeIdeal _).mpr ⟨PI.CMT.conj y, ?_, PI.CMT.coe_conj y⟩` and prove the remaining obligations. Rewrite using `[← hfix, ← Ideal.map_map]`.

Conclude with `Ideal.mem_map_of_mem _ hy`.
-/
theorem ddS_cstab (D : D7) : CStab (ddS D) := by
  have hfix : PI.CMT.conj.comp (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) =
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) := by
    ext a
    rw [RingHom.comp_apply, PI.CMT.coe_conj]
    refine (D.sp.cm.fixed _).2 ⟨(a : D.host.F), ?_⟩
    rfl
  intro x hx
  rw [ddS] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hx
  refine (FractionalIdeal.mem_coeIdeal _).mpr ⟨PI.CMT.conj y, ?_, PI.CMT.coe_conj y⟩
  rw [← hfix, ← Ideal.map_map]
  exact Ideal.mem_map_of_mem _ hy

/- English proof (translation)
Introduce `D a`. Conclude with `⟨zpow_ne_zero _ (ddS_ne D), cstab_zpow (ddS_cstab D) _⟩`.
-/
theorem adjoint_action_reduction : AaStep := by
  intro D a
  exact ⟨zpow_ne_zero _ (ddS_ne D), cstab_zpow (ddS_cstab D) _⟩

end D7

end PI.SRW
