import Formalism.LocalRingCardinality.SpanPowerMembership.TwCore
import Formalism.LocalRingCardinality.SpanPowerMembership.UrPkgNonempty
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocH

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc LB

/- English proof (translation)
Use `haveI := v.isMaximal`. Take `⟨q, n, -, hqP, hq, hN⟩` from `Ideal.exists_prime_and_absNorm_eq_pow v.asIdeal`. Establish `hpP : ((p : ℕ) : 𝓞 E) ∈ v.asIdeal` using `hv`. Establish `hqp : q = p`. Assume the negation of the conclusion as `hne`.

Take `⟨a, b, hab⟩` from `Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr (Ne.symm hne))`. Establish `h1` using `congrArg (Int.cast : ℤ → 𝓞 E) hab`. Move the coercions through the operations in `at h1`. Establish `hmem : (1 : 𝓞 E) ∈ v.asIdeal`. Rewrite using `[← h1]`.

Conclude with `v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hpP) (v.asIdeal.mul_mem_left _ hqP)`. Conclude with `v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hmem)`. Rewrite using `[hN, hqp, Nat.pow_mod, h15, one_pow]`. Apply the tactic sequence `all_goals norm_num`.
-/
theorem absNorm_mod_fifteen (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (h15 : p % 15 = 1)
    {v : HeightOneSpectrum (𝓞 E)} (hv : v ∈ placesOver E p) : Ideal.absNorm v.asIdeal % 15 = 1 := by
  haveI := v.isMaximal
  obtain ⟨q, n, -, hqP, hq, hN⟩ := Ideal.exists_prime_and_absNorm_eq_pow v.asIdeal
  have hpP : ((p : ℕ) : 𝓞 E) ∈ v.asIdeal := hv
  have hqp : q = p := by
    by_contra hne
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr (Ne.symm hne))
    have h1 := congrArg (Int.cast : ℤ → 𝓞 E) hab
    push_cast at h1
    have hmem : (1 : 𝓞 E) ∈ v.asIdeal := by
      rw [← h1]
      exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hpP) (v.asIdeal.mul_mem_left _ hqP)
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hmem)
  rw [hN, hqp, Nat.pow_mod, h15, one_pow]
  all_goals norm_num

namespace TwB

section Settings

variable (F : Type) [Field F] [NumberField F]

abbrev TwT : Type :=
  Σ l : Nat.Primes, {w : HeightOneSpectrum (𝓞 F) // (((l : ℕ) : ℕ) : 𝓞 F) ∈ w.asIdeal}

instance (i : TwT F) : Fact ((i.1 : ℕ)).Prime := ⟨i.1.2⟩

def phi (i : TwT F) : F →+* PadicAlgCl (i.1 : ℕ) := (exists_embAt i.2.1 i.2.2).choose

/- English proof (translation)
Conclude with `(exists_embAt i.2.1 i.2.2).choose_spec x`.
-/
theorem phi_spec (i : TwT F) (x : 𝓞 F) : x ∈ i.2.1.asIdeal ↔ ‖phi F i (x : F)‖ < 1 := by
  exact (exists_embAt i.2.1 i.2.2).choose_spec x

end Settings

section OneLL

variable {l : ℕ} [hl : Fact l.Prime] {F : Type} [Field F] (LL : FinExt l) (φ : F →+* PadicAlgCl l)
  (hφ : ∀ x, φ x ∈ LL.1)

def phiL : F →+* ↥LL.1 := φ.codRestrict LL.1.toSubfield hφ

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem phiL_coe (x : F) : ((phiL LL φ hφ x : ↥LL.1) : PadicAlgCl l) = φ x := rfl

def embF : F →+* FractionRing ↥(OL LL) := (toFrac LL).comp (phiL LL φ hφ)

/- English proof (translation)
Establish `key : ∀ y : ↥(OL LL), algebraMap ↥(OL LL) (FractionRing ↥(OL LL)) y = embF LL φ hφ x ↔ (y : ↥LL.1) = phiL LL φ hφ x`. Introduce `y`. Use `show algebraMap ↥(OL LL) (FractionRing ↥(OL LL)) y = (FractionRing.algEquiv ↥(OL LL) ↥LL.1).symm (phiL LL φ hφ x) ↔ _`. Rewrite using `[AlgEquiv.eq_symm_apply, AlgEquiv.commutes]`. Both sides reduce to the same expression.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hmem : phiL LL φ hφ x ∈ OL LL`. Rewrite using `[mem_OL, phiL_coe]`. Conclude with `h.le`.

Use `⟨⟨phiL LL φ hφ x, hmem⟩, ?_, (key _).mpr rfl⟩` and prove the remaining obligations. Rewrite using `[mem_max]`. Use `show ‖((phiL LL φ hφ x : ↥LL.1) : PadicAlgCl l)‖ < 1`. Rewrite using `[phiL_coe]`. Conclude with `h`.

Introduce and unpack `⟨y, hy, hyx⟩`. Rewrite `hy` using `[mem_max]`. Use `(key y).mp hyx` as an intermediate fact. Rewrite using `[← phiL_coe LL φ hφ, ← this]`. Conclude with `hy`.
-/
theorem embF_lt_iff (x : F) : ‖φ x‖ < 1 ↔ ∃ y ∈ maximalIdeal ↥(OL LL),
    algebraMap ↥(OL LL) (FractionRing ↥(OL LL)) y = embF LL φ hφ x := by
  have key : ∀ y : ↥(OL LL), algebraMap ↥(OL LL) (FractionRing ↥(OL LL)) y = embF LL φ hφ x ↔
      (y : ↥LL.1) = phiL LL φ hφ x := by
    intro y
    show algebraMap ↥(OL LL) (FractionRing ↥(OL LL)) y =
        (FractionRing.algEquiv ↥(OL LL) ↥LL.1).symm (phiL LL φ hφ x) ↔ _
    rw [AlgEquiv.eq_symm_apply, AlgEquiv.commutes]
    rfl
  constructor
  · intro h
    have hmem : phiL LL φ hφ x ∈ OL LL := by
      rw [mem_OL, phiL_coe]
      exact h.le
    refine ⟨⟨phiL LL φ hφ x, hmem⟩, ?_, (key _).mpr rfl⟩
    rw [mem_max]
    show ‖((phiL LL φ hφ x : ↥LL.1) : PadicAlgCl l)‖ < 1
    rw [phiL_coe]
    exact h
  · rintro ⟨y, hy, hyx⟩
    rw [mem_max] at hy
    have := (key y).mp hyx
    rw [← phiL_coe LL φ hφ, ← this]
    exact hy

def pkg : UrPkg l ↥(OL LL) :=
  (urPkg_nonempty l ↥(OL LL) (toC LL) (toC_injective LL)
    (fun x => (norm_toC LL x).le.trans (nrm_le LL x))
    (fun x hx => by rw [norm_toC]; exact (mem_max LL x).mp hx)).some

end OneLL

end TwB

end Formalism.BasicNotions.Examples₂
