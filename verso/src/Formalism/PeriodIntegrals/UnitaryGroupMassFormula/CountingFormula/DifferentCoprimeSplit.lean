import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.UnimodOneGenus
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TypedLoc
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemInvCoe

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev ddI (D : D7) : Ideal (𝓞 D.host.E) :=
  Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))

def DdOffG : Prop :=
  ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ¬ ddI D ≤ P.asIdeal

section LocLemmas

variable {E : Type} [Field E] [NumberField E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

/- English proof (translation)
Conclude with `Iff.rfl`.
-/
theorem mem_localization_iff' (p : Ideal (𝓞 E)) [p.IsPrime] (L : Submodule (𝓞 E) V) (x : V) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ p L ↔ ∃ s : 𝓞 E, s ∉ p ∧ s • x ∈ L := by
  exact Iff.rfl

/- English proof (translation)
Introduce `x hx`. Rewrite `hx`, the goal using `[mem_localization_iff']`. Take `⟨s, hs, hsx⟩` from `hx`. Take `⟨t, ht, htx⟩` from `(mem_localization_iff' p L' _).1 (h hsx)`. Use `⟨t * s, fun hm => (Ideal.IsPrime.mem_or_mem ‹_› hm).elim ht hs, ?_⟩` and prove the remaining obligations.

Rewrite using `[mul_smul]` and apply the resulting hypothesis.
-/
theorem localization_le_of_le_localization' (p : Ideal (𝓞 E)) [p.IsPrime] {L L' : Submodule (𝓞 E) V} (h : L ≤ Formalism.HermitianLatticesTheory.localization₂ p L') :
    Formalism.HermitianLatticesTheory.localization₂ p L ≤ Formalism.HermitianLatticesTheory.localization₂ p L' := by
  intro x hx
  rw [mem_localization_iff'] at hx ⊢
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨t, ht, htx⟩ := (mem_localization_iff' p L' _).1 (h hsx)
  refine ⟨t * s, fun hm => (Ideal.IsPrime.mem_or_mem ‹_› hm).elim ht hs, ?_⟩
  rwa [mul_smul]

/- English proof (translation)
Establish `hP : P.asIdeal ≠ ⊤` using `P.isPrime.ne_top`. Establish `hlt : J * P.asIdeal < J`. Use `lt_of_le_of_ne (Ideal.mul_le_inf.trans inf_le_left) ?_` and prove the remaining obligations. Introduce `h`. Apply `hP` to reduce the goal to its premises.

Establish `h2 : J * P.asIdeal = J * ⊤` using `by rw [h, Ideal.mul_top]`. Conclude with `mul_left_cancel₀ hJ h2`. Take `⟨d, hdJ, hdP⟩` from `SetLike.exists_of_lt hlt`. Establish `hd0 : d ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hdP (zero_mem _)`. Take `⟨I, hI⟩` from `Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem J).mpr hdJ)`. Establish `hIP : ¬ I ≤ P.asIdeal`. Introduce `hle`. Apply `hdP` to reduce the goal to its premises.

Establish `h3 : Ideal.span {d} ≤ J * P.asIdeal`. Rewrite using `[hI]`. Conclude with `Ideal.mul_mono_right hle`. Conclude with `h3 (Ideal.mem_span_singleton_self d)`. Take `⟨t, htI, htP⟩` from `SetLike.not_le_iff_exists.mp hIP`.

Use `⟨d, hdJ, hd0, t, htP, fun y hy => ?_⟩` and prove the remaining obligations. Establish `h4 : y * t ∈ J * I` using `Ideal.mul_mem_mul hy htI`. Rewrite `h4` using `[← hI, Ideal.mem_span_singleton']`. Take `⟨o, ho⟩` from `h4`. Conclude with `⟨o, by rw [mul_comm t y, ← ho, mul_comm]⟩`.
-/
theorem locGen_ideal (J : Ideal (𝓞 E)) (hJ : J ≠ ⊥) (P : HeightOneSpectrum (𝓞 E)) :
    ∃ d ∈ J, d ≠ 0 ∧ ∃ t : 𝓞 E, t ∉ P.asIdeal ∧ ∀ y ∈ J, ∃ o : 𝓞 E, t * y = d * o := by
  have hP : P.asIdeal ≠ ⊤ := P.isPrime.ne_top
  have hlt : J * P.asIdeal < J := by
    refine lt_of_le_of_ne (Ideal.mul_le_inf.trans inf_le_left) ?_
    intro h
    apply hP
    have h2 : J * P.asIdeal = J * ⊤ := by rw [h, Ideal.mul_top]
    exact mul_left_cancel₀ hJ h2
  obtain ⟨d, hdJ, hdP⟩ := SetLike.exists_of_lt hlt
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hdP (zero_mem _)
  obtain ⟨I, hI⟩ := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem J).mpr hdJ)
  have hIP : ¬ I ≤ P.asIdeal := by
    intro hle
    apply hdP
    have h3 : Ideal.span {d} ≤ J * P.asIdeal := by
      rw [hI]
      exact Ideal.mul_mono_right hle
    exact h3 (Ideal.mem_span_singleton_self d)
  obtain ⟨t, htI, htP⟩ := SetLike.not_le_iff_exists.mp hIP
  refine ⟨d, hdJ, hd0, t, htP, fun y hy => ?_⟩
  have h4 : y * t ∈ J * I := Ideal.mul_mem_mul hy htI
  rw [← hI, Ideal.mem_span_singleton'] at h4
  obtain ⟨o, ho⟩ := h4
  exact ⟨o, by rw [mul_comm t y, ← ho, mul_comm]⟩

end LocLemmas

section XS

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

/- English proof (translation)
Unfold `aaI`. Establish `h : ((D.R.rS : ℤ) - (a : ℕ)) = ((D.R.rS - (a : ℕ) : ℕ) : ℤ)`. Use `a.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[h, zpow_neg, zpow_natCast, FractionalIdeal.coeIdeal_pow]`.

Apply the tactic sequence `try rfl`.
-/
theorem aaI_eq (a : Fin D.R.rS) :
    aaI D a = (((ddI D ^ (D.R.rS - (a : ℕ)) : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))⁻¹ := by
  unfold aaI
  have h : ((D.R.rS : ℤ) - (a : ℕ)) = ((D.R.rS - (a : ℕ) : ℕ) : ℤ) := by
    have := a.isLt
    omega
  rw [h, zpow_neg, zpow_natCast, FractionalIdeal.coeIdeal_pow]
  try rfl

/- English proof (translation)
Rewrite using `[ne_eq, Ideal.map_eq_bot_iff_of_injective]`. Conclude with `differentIdeal_ne_bot`. Use `first`. Consider the case `exact FaithfulSMul.algebraMap_injective _ _`. Consider the case `exact NoZeroSMulDivisors.algebraMap_injective _ _`.
-/
theorem ddI_ne_bot : ddI D ≠ ⊥ := by
  rw [ne_eq, Ideal.map_eq_bot_iff_of_injective]
  · exact differentIdeal_ne_bot
  · first
    | exact FaithfulSMul.algebraMap_injective _ _
    | exact NoZeroSMulDivisors.algebraMap_injective _ _

/- English proof (translation)
Establish `hJ' : (J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0`. Rewrite using `[ne_eq, FractionalIdeal.coeIdeal_eq_zero]` and apply the resulting hypothesis. Rewrite using `[FractionalIdeal.mem_inv_iff hJ']`. Prove the components needed by the constructor for the conclusion. Introduce `h y hy`.

Establish `h2` using `h _ (by rw [FractionalIdeal.mem_coeIdeal]; exact ⟨y, hy, rfl⟩)`. Rewrite `h2` using `[FractionalIdeal.mem_one_iff]`. Take `⟨o, ho⟩` from `h2`. Conclude with `⟨o, ho⟩`. Introduce `h y hy`.

Rewrite `hy` using `[FractionalIdeal.mem_coeIdeal]`. Take `⟨y', hy', rfl⟩` from `hy`. Take `⟨o, ho⟩` from `h y' hy'`. Rewrite using `[FractionalIdeal.mem_one_iff]`. Conclude with `⟨o, ho⟩`.
-/
theorem mem_inv_coe {J : Ideal (𝓞 D.host.E)} (hJ : J ≠ ⊥) (x : D.host.E) :
    x ∈ ((J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))⁻¹ ↔
      ∀ y ∈ J, ∃ o : 𝓞 D.host.E, (o : D.host.E) = x * (y : D.host.E) := by
  have hJ' : (J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := by
    rwa [ne_eq, FractionalIdeal.coeIdeal_eq_zero]
  rw [FractionalIdeal.mem_inv_iff hJ']
  constructor
  · intro h y hy
    have h2 := h _ (by rw [FractionalIdeal.mem_coeIdeal]; exact ⟨y, hy, rfl⟩)
    rw [FractionalIdeal.mem_one_iff] at h2
    obtain ⟨o, ho⟩ := h2
    exact ⟨o, ho⟩
  · intro h y hy
    rw [FractionalIdeal.mem_coeIdeal] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    obtain ⟨o, ho⟩ := h y' hy'
    rw [FractionalIdeal.mem_one_iff]
    exact ⟨o, ho⟩

/- English proof (translation)
Establish `hgen_le : XS D F0 ≤ Formalism.HermitianLatticesTheory.localization₂ P (Submodule.span (𝓞 D.host.E) (Set.range fun a => c a • F0.e a))`. Unfold `XS`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `y ⟨a, x, hx, rfl⟩`. Take `⟨s, hs, o, ho⟩` from `h1 a x hx`.

Use `(mem_localization_iff' P _ _).mpr ⟨s, hs, ?_⟩` and prove the remaining obligations. Establish `e1 : s • (x • F0.e a) = o • (c a • F0.e a)`. Rewrite using `[← smul_assoc, ← smul_assoc]`. Use `congr 1`. Rewrite using `[Algebra.smul_def, Algebra.smul_def, mul_comm (algebraMap _ _ o)]`.

Conclude with `ho`. Rewrite using `[e1]`. Conclude with `Submodule.smul_mem _ o (Submodule.subset_span ⟨a, rfl⟩)`. Establish `hgen_ge : Submodule.span (𝓞 D.host.E) (Set.range fun a => c a • F0.e a) ≤ Formalism.HermitianLatticesTheory.localization₂ P (XS D F0)`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `y ⟨a, rfl⟩`. Take `⟨s, hs, hsc⟩` from `h2 a`. Use `(mem_localization_iff' P _ _).mpr ⟨s, hs, ?_⟩` and prove the remaining obligations. Rewrite using `[← smul_assoc]`. Unfold `XS`.

Apply `Submodule.subset_span` to reduce the goal to its premises. Conclude with `⟨a, s • c a, by rw [Algebra.smul_def]; exact hsc, rfl⟩`. Conclude with `le_antisymm (localization_le_of_le_localization' P hgen_le) (localization_le_of_le_localization' P hgen_ge)`.
-/
theorem localization_eq_localization_span (P : Ideal (𝓞 D.host.E)) [P.IsPrime] (c : Fin D.R.rS → D.host.E)
    (h1 : ∀ a, ∀ x ∈ aaI D a, ∃ s : 𝓞 D.host.E, s ∉ P ∧ ∃ o : 𝓞 D.host.E, (s : D.host.E) * x = c a * o)
    (h2 : ∀ a, ∃ s : 𝓞 D.host.E, s ∉ P ∧ (s : D.host.E) * c a ∈ aaI D a) :
    Formalism.HermitianLatticesTheory.localization₂ P (XS D F0) =
      Formalism.HermitianLatticesTheory.localization₂ P (Submodule.span (𝓞 D.host.E) (Set.range fun a => c a • F0.e a)) := by
  have hgen_le : XS D F0 ≤ Formalism.HermitianLatticesTheory.localization₂ P (Submodule.span (𝓞 D.host.E) (Set.range fun a => c a • F0.e a)) := by
    unfold XS
    rw [Submodule.span_le]
    rintro y ⟨a, x, hx, rfl⟩
    obtain ⟨s, hs, o, ho⟩ := h1 a x hx
    refine (mem_localization_iff' P _ _).mpr ⟨s, hs, ?_⟩
    have e1 : s • (x • F0.e a) = o • (c a • F0.e a) := by
      rw [← smul_assoc, ← smul_assoc]
      congr 1
      rw [Algebra.smul_def, Algebra.smul_def, mul_comm (algebraMap _ _ o)]
      exact ho
    rw [e1]
    exact Submodule.smul_mem _ o (Submodule.subset_span ⟨a, rfl⟩)
  have hgen_ge : Submodule.span (𝓞 D.host.E) (Set.range fun a => c a • F0.e a) ≤ Formalism.HermitianLatticesTheory.localization₂ P (XS D F0) := by
    rw [Submodule.span_le]
    rintro y ⟨a, rfl⟩
    obtain ⟨s, hs, hsc⟩ := h2 a
    refine (mem_localization_iff' P _ _).mpr ⟨s, hs, ?_⟩
    rw [← smul_assoc]
    unfold XS
    apply Submodule.subset_span
    exact ⟨a, s • c a, by rw [Algebra.smul_def]; exact hsc, rfl⟩
  exact le_antisymm (localization_le_of_le_localization' P hgen_le) (localization_le_of_le_localization' P hgen_ge)

end XS

/- English proof (translation)
Introduce `D u F0 P`. Use `haveI := P.isPrime`. Establish `hJ : ∀ a : Fin D.R.rS, (ddI D ^ (D.R.rS - (a : ℕ))) ≠ ⊥` using `fun a => pow_ne_zero _ (ddI_ne_bot D)`. Establish `h1P : (1 : 𝓞 D.host.E) ∉ P.asIdeal` using `(Ideal.ne_top_iff_one _).mp P.isPrime.ne_top`. Distinguish the cases in `hg : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal`.

Take `⟨t, htd, htP⟩` from `SetLike.not_le_iff_exists.mp (hD D P hg)`. Use `⟨fun _ => 1, fun _ => one_ne_zero, fun _ _ => rfl, localization_eq_localization_span D F0 P.asIdeal _ ?_ ?_⟩` and prove the remaining obligations. Introduce `a x hx`. Rewrite `hx` using `[aaI_eq, mem_inv_coe D (hJ a)]`. Take `⟨o, ho⟩` from `hx (t ^ (D.R.rS - (a : ℕ))) (Ideal.pow_mem_pow htd _)`.

Use `⟨t ^ (D.R.rS - (a : ℕ)), fun h => htP (P.isPrime.mem_of_pow_mem _ h), o, ?_⟩` and prove the remaining obligations. Rewrite using `[one_mul, ho, mul_comm]`. Introduce `a`. Use `⟨1, h1P, ?_⟩` and prove the remaining obligations. Rewrite using `[aaI_eq, mem_inv_coe D (hJ a)]`.

Introduce `y _`. Conclude with `⟨y, by simp⟩`. Use `choose d hdJ hd0 t htP ht using fun a : Fin D.R.rS => locGen_ideal (ddI D ^ (D.R.rS - (a : ℕ))) (hJ a) P`. Establish `hdE : ∀ a, ((d a : 𝓞 D.host.E) : D.host.E) ≠ 0` using `fun a h => hd0 a (NumberField.RingOfIntegers.coe_eq_zero_iff.mp h)`. Use `⟨fun a => ((d a : 𝓞 D.host.E) : D.host.E)⁻¹, fun a => inv_ne_zero (hdE a), fun h => absurd h hg, localization_eq_localization_span D F0 P.asIdeal _ ?_ ?_⟩` and prove the remaining obligations.

Introduce `a x hx`. Rewrite `hx` using `[aaI_eq, mem_inv_coe D (hJ a)]`. Take `⟨o, ho⟩` from `hx (d a) (hdJ a)`. Use `⟨1, h1P, o, ?_⟩` and prove the remaining obligations. Rewrite using `[ho]`.

Use `hdE a` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try simp`. Apply the tactic sequence `try ring`. Introduce `a`.

Use `⟨t a, htP a, ?_⟩` and prove the remaining obligations. Rewrite using `[aaI_eq, mem_inv_coe D (hJ a)]`. Introduce `y hy`. Take `⟨o, ho⟩` from `ht a y hy`. Use `⟨o, ?_⟩` and prove the remaining obligations.

Establish `hoE : ((t a : 𝓞 D.host.E) : D.host.E) * (y : D.host.E) = ((d a : 𝓞 D.host.E) : D.host.E) * (o : D.host.E)`. Use `congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) ho` as an intermediate fact. Simplify using `using this`. Rewrite using `[eq_comm, mul_comm ((t a : 𝓞 D.host.E) : D.host.E) _, mul_assoc, hoE, ← mul_assoc, inv_mul_cancel₀ (hdE a), one_mul]`.
-/
theorem locGenXS_of (hD : DdOffG) : LocGenXS := by
  intro D u F0 P
  haveI := P.isPrime
  have hJ : ∀ a : Fin D.R.rS, (ddI D ^ (D.R.rS - (a : ℕ))) ≠ ⊥ := fun a => pow_ne_zero _ (ddI_ne_bot D)
  have h1P : (1 : 𝓞 D.host.E) ∉ P.asIdeal := (Ideal.ne_top_iff_one _).mp P.isPrime.ne_top
  by_cases hg : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
  · obtain ⟨t, htd, htP⟩ := SetLike.not_le_iff_exists.mp (hD D P hg)
    refine ⟨fun _ => 1, fun _ => one_ne_zero, fun _ _ => rfl, localization_eq_localization_span D F0 P.asIdeal _ ?_ ?_⟩
    · intro a x hx
      rw [aaI_eq, mem_inv_coe D (hJ a)] at hx
      obtain ⟨o, ho⟩ := hx (t ^ (D.R.rS - (a : ℕ))) (Ideal.pow_mem_pow htd _)
      refine ⟨t ^ (D.R.rS - (a : ℕ)), fun h => htP (P.isPrime.mem_of_pow_mem _ h), o, ?_⟩
      rw [one_mul, ho, mul_comm]
    · intro a
      refine ⟨1, h1P, ?_⟩
      rw [aaI_eq, mem_inv_coe D (hJ a)]
      intro y _
      exact ⟨y, by simp⟩
  · choose d hdJ hd0 t htP ht using fun a : Fin D.R.rS => locGen_ideal (ddI D ^ (D.R.rS - (a : ℕ))) (hJ a) P
    have hdE : ∀ a, ((d a : 𝓞 D.host.E) : D.host.E) ≠ 0 := fun a h =>
      hd0 a (NumberField.RingOfIntegers.coe_eq_zero_iff.mp h)
    refine ⟨fun a => ((d a : 𝓞 D.host.E) : D.host.E)⁻¹, fun a => inv_ne_zero (hdE a), fun h => absurd h hg,
      localization_eq_localization_span D F0 P.asIdeal _ ?_ ?_⟩
    · intro a x hx
      rw [aaI_eq, mem_inv_coe D (hJ a)] at hx
      obtain ⟨o, ho⟩ := hx (d a) (hdJ a)
      refine ⟨1, h1P, o, ?_⟩
      rw [ho]
      have := hdE a
      field_simp
      try simp
      try ring
    · intro a
      refine ⟨t a, htP a, ?_⟩
      rw [aaI_eq, mem_inv_coe D (hJ a)]
      intro y hy
      obtain ⟨o, ho⟩ := ht a y hy
      refine ⟨o, ?_⟩
      have hoE : ((t a : 𝓞 D.host.E) : D.host.E) * (y : D.host.E) = ((d a : 𝓞 D.host.E) : D.host.E) * (o : D.host.E) := by
        have := congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) ho
        simpa using this
      rw [eq_comm, mul_comm ((t a : 𝓞 D.host.E) : D.host.E) _, mul_assoc, hoE, ← mul_assoc, inv_mul_cancel₀ (hdE a),
        one_mul]

/- English proof (translation)
Introduce `D P hg hle`. Establish `hg' : ∃ i, ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal`. Establish `e : ((gS D : ℕ) : 𝓞 D.host.E) = ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E)`. Simplify using `[gS, Nat.cast_mul]`. Rewrite `hg` using `[e]`.

Break down `P.isPrime.mem_or_mem hg with h | h` into its components or cases. Conclude with `⟨0, h⟩`. Conclude with `⟨1, h⟩`. Take `⟨i, hi⟩` from `hg'`. Establish `hp : (D.host.g i).Prime` using `D.host.g_prime i`.

Establish `hvp : (P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))).IsPrime` using `Ideal.IsPrime.comap _`. Establish `hpv : ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))`. Rewrite using `[Ideal.mem_comap, map_natCast]`. Conclude with `hi`. Establish `hvb : P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≠ ⊥`.

Introduce `h0`. Rewrite `hpv` using `[h0, Ideal.mem_bot]`. Conclude with `hp.ne_zero (by exact_mod_cast hpv)`. Set `v : HeightOneSpectrum (𝓞 D.host.F)` to `⟨_, hvp, hvb⟩`. Establish `hv : ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal` using `hpv`.

Establish `hef` using `Formalism.L2.SG.Pf.TypedLoc.tower_ef D.host.F D.host.E hp (D.nd.g_split i) v hv`. Establish `hq0` using `Formalism.L2.SG.Pf.TypedLoc.span_p_ne_bot hp`. Establish `hmap : Ideal.map (algebraMap ℤ (𝓞 D.host.F)) (Ideal.span {((D.host.g i : ℕ) : ℤ)}) ≠ ⊥` using `Ideal.map_ne_bot_of_ne_bot hq0`. Establish `hcount` using `Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmap v.isPrime v.ne_bot`. Rewrite `hcount` using `[hef.1]`.

Establish `: v.asIdeal.IsMaximal` using `v.isMaximal`. Take `⟨Q, hQ1, hQ2⟩` from `Ideal.eq_prime_pow_mul_coprime hmap v.asIdeal`. Rewrite `hQ2` using `[← hcount, pow_one]`. Use `haveI := Formalism.L2.SG.Pf.TypedLoc.span_p_maximal hp`. Use `haveI : NeZero (D.host.g i) := ⟨hp.ne_zero⟩`.

Use `haveI : Finite (ℤ ⧸ Ideal.span {((D.host.g i : ℕ) : ℤ)}) := Finite.of_equiv _ (Int.quotientSpanNatEquivZMod (D.host.g i)).symm.toEquiv`. Establish `hnd` using `not_dvd_differentIdeal_of_isCoprime ℤ v.asIdeal Q (Ideal.isCoprime_iff_sup_eq.mpr hQ1) hQ2.symm`. Apply `hnd` to reduce the goal to its premises. Rewrite using `[Ideal.dvd_iff_le]`. Conclude with `Ideal.map_le_iff_le_comap.mp hle`.
-/
theorem different_coprime_split : DdOffG := by
  intro D P hg hle
  have hg' : ∃ i, ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    have e : ((gS D : ℕ) : 𝓞 D.host.E) = ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E) := by
      simp [gS, Nat.cast_mul]
    rw [e] at hg
    rcases P.isPrime.mem_or_mem hg with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨i, hi⟩ := hg'
  have hp : (D.host.g i).Prime := D.host.g_prime i
  have hvp : (P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))).IsPrime := Ideal.IsPrime.comap _
  have hpv : ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
    rw [Ideal.mem_comap, map_natCast]; exact hi
  have hvb : P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hpv
    exact hp.ne_zero (by exact_mod_cast hpv)
  let v : HeightOneSpectrum (𝓞 D.host.F) := ⟨_, hvp, hvb⟩
  have hv : ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := hpv
  have hef := Formalism.L2.SG.Pf.TypedLoc.tower_ef D.host.F D.host.E hp (D.nd.g_split i) v hv
  have hq0 := Formalism.L2.SG.Pf.TypedLoc.span_p_ne_bot hp
  have hmap : Ideal.map (algebraMap ℤ (𝓞 D.host.F)) (Ideal.span {((D.host.g i : ℕ) : ℤ)}) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hq0
  have hcount := Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmap v.isPrime v.ne_bot
  rw [hef.1] at hcount
  have : v.asIdeal.IsMaximal := v.isMaximal
  obtain ⟨Q, hQ1, hQ2⟩ := Ideal.eq_prime_pow_mul_coprime hmap v.asIdeal
  rw [← hcount, pow_one] at hQ2
  haveI := Formalism.L2.SG.Pf.TypedLoc.span_p_maximal hp
  haveI : NeZero (D.host.g i) := ⟨hp.ne_zero⟩
  haveI : Finite (ℤ ⧸ Ideal.span {((D.host.g i : ℕ) : ℤ)}) :=
    Finite.of_equiv _ (Int.quotientSpanNatEquivZMod (D.host.g i)).symm.toEquiv
  have hnd := not_dvd_differentIdeal_of_isCoprime ℤ v.asIdeal Q (Ideal.isCoprime_iff_sup_eq.mpr hQ1) hQ2.symm
  apply hnd
  rw [Ideal.dvd_iff_le]
  exact Ideal.map_le_iff_le_comap.mp hle

/- English proof (translation)
The claim follows from `locGenXS_of different_coprime_split`.
-/
theorem local_genus_exists : LocGenXS := locGenXS_of different_coprime_split

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
