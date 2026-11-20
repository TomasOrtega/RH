import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComapInlMemStLat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralClosureFgDvrOfSeparableCharpolyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqSubmoduleMulLeftImageIntegralClosureOfSeparablStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAevalEqOfMulLeftCharpolySeparableStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCommonDenominatorAevalOfFgStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSubmodulesBetweenSmulAndSelfStatement

open Polynomial

namespace GlobalTheory.UnitLemma

/- English proof (translation)
Proceed by induction on `p using Polynomial.induction_on with`. Consider the case `C a => simpa [Algebra.smul_def] using M.smul_mem a hm`. Consider the case `add p q hp hq => simpa [add_mul] using M.add_mem hp hq`. Consider the case `monomial n a ih`. Use `hM _ ih` as an intermediate fact.

Establish `e : aeval g (Polynomial.C a * X ^ (n + 1)) * m = g * (aeval g (Polynomial.C a * X ^ n) * m)`. Simplify using `only [map_mul, aeval_C, aeval_X, map_pow, pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `this`.
-/
theorem aeval_mul_mem_of_stable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {g : A} {M : Submodule O A}
    (hM : ∀ y ∈ M, g * y ∈ M) (p : O[X]) {m : A} (hm : m ∈ M) : aeval g p * m ∈ M := by
  induction p using Polynomial.induction_on with
  | C a => simpa [Algebra.smul_def] using M.smul_mem a hm
  | add p q hp hq => simpa [add_mul] using M.add_mem hp hq
  | monomial n a ih =>
    have := hM _ ih
    have e : aeval g (Polynomial.C a * X ^ (n + 1)) * m = g * (aeval g (Polynomial.C a * X ^ n) * m) := by
      simp only [map_mul, aeval_C, aeval_X, map_pow, pow_succ]; ring
    rw [e]; exact this

/- English proof (translation)
Introduce `O E A _ _ _ _ _ _ _ _ _ _ _ _ g hsep`. Use `set C : Submodule O A := Subalgebra.toSubmodule (integralClosure O A) with hCdef`. Establish `hCfg : C.FG` using `GlobalTheory.T.integralClosure_fg_dvr_of_separable_charpoly O E A g hsep`. Take `⟨c, hc0, hc⟩` from `GlobalTheory.T.exists_common_denominator_aeval_of_fg' O E A g (GlobalTheory.T.exists_aeval_eq_of_mulLeft_charpoly_separable E A g hsep) C hCfg`. Establish `hfin` using `GlobalTheory.T.finite_setOf_submodule_between_smul_and_fg O A C hCfg c hc0`.

Establish `key : ∀ M : stLat O E g, ∃ t : Aˣ, mulLat O ((t⁻¹ : Aˣ) : A) (M : Submodule O A) ∈ {N : Submodule O A | N ≤ C ∧ ∀ x ∈ C, c • x ∈ N}`. Introduce `M`. Take `⟨hML, hMg⟩` from `M.2`. Use `set N : Submodule O A := C * (M : Submodule O A) with hN`. Establish `hMN : (M : Submodule O A) ≤ N`.

Introduce `m hm`. Use `Submodule.mul_mem_mul (show (1 : A) ∈ C from (integralClosure O A).one_mem) hm` as an intermediate fact. Simplify using `using this`. Establish `hNlat : IsLat O E N`. Use `⟨Submodule.FG.mul hCfg hML.1, ?_⟩` and prove the remaining obligations.

Rewrite using `[eq_top_iff, ← hML.2]`. Conclude with `Submodule.span_mono hMN`. Establish `hNC : ∀ x ∈ integralClosure O A, ∀ y ∈ N, x * y ∈ N`. Introduce `x hx y hy`. Use `Submodule.mul_induction_on hy ?_ ?_` and prove the remaining obligations.

Introduce `a ha m hm`. Rewrite using `[← mul_assoc]`. Conclude with `Submodule.mul_mem_mul ((integralClosure O A).mul_mem hx ha) hm`. Introduce `u v hu hv`. Rewrite using `[mul_add]`.

Conclude with `N.add_mem hu hv`. Take `⟨t, ht⟩` from `GlobalTheory.T.eq_submoduleMulLeftImage_integralClosure_of_separable O E A g hsep N hNlat hNC`. Establish `hcN : ∀ y ∈ N, c • y ∈ (M : Submodule O A)`. Introduce `y hy`. Use `Submodule.mul_induction_on hy ?_ ?_` and prove the remaining obligations.

Introduce `a ha m hm`. Take `⟨p, hp⟩` from `hc a ha`. Rewrite using `[← smul_mul_assoc, ← hp]`. Conclude with `aeval_mul_mem_of_stable hMg p hm`. Introduce `u v hu hv`.

Rewrite using `[smul_add]`. Conclude with `Submodule.add_mem _ hu hv`. Use `⟨t, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx` using `[mem_mulLat_iff, inv_inv]`.

Establish `h1 : (t : A) * x ∈ N` using `hMN hx`. Rewrite `h1` using `[ht, mem_mulLat_iff]`. Rewrite using `[hCdef, Subalgebra.mem_toSubmodule]`. Rewrite `h1` using `[Subalgebra.mem_toSubmodule]`. Simplify `h1` using `[← mul_assoc]`.

Introduce `y hy`. Rewrite using `[mem_mulLat_iff, inv_inv]`. Establish `h1 : (t : A) * y ∈ N`. Rewrite using `[ht, mem_mulLat_iff, Subalgebra.mem_toSubmodule]`. Rewrite `hy` using `[hCdef, Subalgebra.mem_toSubmodule]`.

Simplify `hy` using `[← mul_assoc]`. Simplify `hcN _ h1` using `[mul_smul_comm]`. Use `choose t ht using key`. Set `F : MulAction.orbitRel.Quotient Aˣ (stLat O E g) → {N : Submodule O A // N ∈ {N : Submodule O A | N ≤ C ∧ ∀ x ∈ C, c • x ∈ N}}` to `fun q => ⟨_, ht q.out⟩`. Use `haveI : Finite {N : Submodule O A // N ∈ {N : Submodule O A | N ≤ C ∧ ∀ x ∈ C, c • x ∈ N}} := hfin.to_subtype`.

Use `Finite.of_injective F ?_` and prove the remaining obligations. Introduce `q₁ q₂ h`. Establish `h' : mulLat O (((t q₁.out)⁻¹ : Aˣ) : A) (q₁.out : Submodule O A) = mulLat O (((t q₂.out)⁻¹ : Aˣ) : A) (q₂.out : Submodule O A)` using `congrArg Subtype.val h`. Rewrite using `[← q₁.out_eq, ← q₂.out_eq]`. Apply `Quotient.sound` to reduce the goal to its premises.

Use `⟨t q₁.out * (t q₂.out)⁻¹, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[stLat_smul_val, Units.val_mul, mulLat_mul, ← h', ← mulLat_mul]`. Simplify using `[mulLat_one]`.
-/
theorem finite_orbits_stLat_of_separable : ∀ (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → Finite (MulAction.orbitRel.Quotient Aˣ (stLat O E g)) := by
  intro O E A _ _ _ _ _ _ _ _ _ _ _ _ g hsep
  set C : Submodule O A := Subalgebra.toSubmodule (integralClosure O A) with hCdef
  have hCfg : C.FG := GlobalTheory.T.integralClosure_fg_dvr_of_separable_charpoly O E A g hsep
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.T.exists_common_denominator_aeval_of_fg' O E A g (GlobalTheory.T.exists_aeval_eq_of_mulLeft_charpoly_separable E A g hsep) C hCfg
  have hfin := GlobalTheory.T.finite_setOf_submodule_between_smul_and_fg O A C hCfg c hc0

  have key : ∀ M : stLat O E g, ∃ t : Aˣ, mulLat O ((t⁻¹ : Aˣ) : A) (M : Submodule O A) ∈
      {N : Submodule O A | N ≤ C ∧ ∀ x ∈ C, c • x ∈ N} := by
    intro M
    obtain ⟨hML, hMg⟩ := M.2
    set N : Submodule O A := C * (M : Submodule O A) with hN
    have hMN : (M : Submodule O A) ≤ N := by
      intro m hm
      have := Submodule.mul_mem_mul (show (1 : A) ∈ C from (integralClosure O A).one_mem) hm
      simpa using this
    have hNlat : IsLat O E N := by
      refine ⟨Submodule.FG.mul hCfg hML.1, ?_⟩
      rw [eq_top_iff, ← hML.2]
      exact Submodule.span_mono hMN
    have hNC : ∀ x ∈ integralClosure O A, ∀ y ∈ N, x * y ∈ N := by
      intro x hx y hy
      refine Submodule.mul_induction_on hy ?_ ?_
      · intro a ha m hm
        rw [← mul_assoc]
        exact Submodule.mul_mem_mul ((integralClosure O A).mul_mem hx ha) hm
      · intro u v hu hv
        rw [mul_add]; exact N.add_mem hu hv
    obtain ⟨t, ht⟩ := GlobalTheory.T.eq_submoduleMulLeftImage_integralClosure_of_separable O E A g hsep N hNlat hNC
    have hcN : ∀ y ∈ N, c • y ∈ (M : Submodule O A) := by
      intro y hy
      refine Submodule.mul_induction_on hy ?_ ?_
      · intro a ha m hm
        obtain ⟨p, hp⟩ := hc a ha
        rw [← smul_mul_assoc, ← hp]
        exact aeval_mul_mem_of_stable hMg p hm
      · intro u v hu hv
        rw [smul_add]; exact Submodule.add_mem _ hu hv
    refine ⟨t, ?_, ?_⟩
    · intro x hx
      rw [mem_mulLat_iff, inv_inv] at hx
      have h1 : (t : A) * x ∈ N := hMN hx
      rw [ht, mem_mulLat_iff] at h1
      rw [hCdef, Subalgebra.mem_toSubmodule]
      rw [Subalgebra.mem_toSubmodule] at h1
      simpa [← mul_assoc] using h1
    · intro y hy
      rw [mem_mulLat_iff, inv_inv]
      have h1 : (t : A) * y ∈ N := by
        rw [ht, mem_mulLat_iff, Subalgebra.mem_toSubmodule]
        rw [hCdef, Subalgebra.mem_toSubmodule] at hy
        simpa [← mul_assoc] using hy
      simpa [mul_smul_comm] using hcN _ h1
  choose t ht using key
  let F : MulAction.orbitRel.Quotient Aˣ (stLat O E g) → {N : Submodule O A // N ∈ {N : Submodule O A | N ≤ C ∧ ∀ x ∈ C, c • x ∈ N}} :=
    fun q => ⟨_, ht q.out⟩
  haveI : Finite {N : Submodule O A // N ∈ {N : Submodule O A | N ≤ C ∧ ∀ x ∈ C, c • x ∈ N}} := hfin.to_subtype
  refine Finite.of_injective F ?_
  intro q₁ q₂ h
  have h' : mulLat O (((t q₁.out)⁻¹ : Aˣ) : A) (q₁.out : Submodule O A) = mulLat O (((t q₂.out)⁻¹ : Aˣ) : A) (q₂.out : Submodule O A) :=
    congrArg Subtype.val h
  rw [← q₁.out_eq, ← q₂.out_eq]
  apply Quotient.sound
  refine ⟨t q₁.out * (t q₂.out)⁻¹, ?_⟩
  apply Subtype.ext
  rw [stLat_smul_val, Units.val_mul, mulLat_mul, ← h', ← mulLat_mul]
  simp [mulLat_one]

end GlobalTheory.UnitLemma
