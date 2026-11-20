import Mathlib
import Formalism.FrobeniusOrbits.HostThickExists
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Galois
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.FrobMulInertia
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Decomp
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK

open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

namespace OrdUnimod

variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

/- English proof (translation)
Rewrite using `[FractionalIdeal.mem_one_iff, IsIntegralClosure.isIntegral_iff (A := 𝓞 (hostE ζ a b))]`.
-/
theorem mem_one_iff' (t : hostE ζ a b) :
    t ∈ (1 : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) ↔ IsIntegral ℤ t := by
  rw [FractionalIdeal.mem_one_iff, IsIntegralClosure.isIntegral_iff (A := 𝓞 (hostE ζ a b))]

/- English proof (translation)
Use `first`. Consider the case `exact isIntegral_algEquiv (σ.restrictScalars ℤ)`. Consider the case `exact ⟨fun h => by simpa using h.map (σ.symm.toAlgHom.restrictScalars ℤ), fun h => h.map (σ.toAlgHom.restrictScalars ℤ)⟩`.
-/
theorem integ_iff (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (t : hostE ζ a b) :
    IsIntegral ℤ (σ t) ↔ IsIntegral ℤ t := by
  first
  | exact isIntegral_algEquiv (σ.restrictScalars ℤ)
  | exact ⟨fun h => by simpa using h.map (σ.symm.toAlgHom.restrictScalars ℤ),
      fun h => h.map (σ.toAlgHom.restrictScalars ℤ)⟩

/- English proof (translation)
Introduce `h`. Apply `hB` to reduce the goal to its premises. Establish `h' : σ⁻¹ • σ • B = σ⁻¹ • (⊥ : Ideal (𝓞 (hostE ζ a b)))` using `by rw [h]`. Rewrite `h'` using `[inv_smul_smul]`. Rewrite using `[h']`.

Use `first`. Consider the case `exact smul_bot _`. Consider the case `exact Ideal.map_bot`. Consider the case `(rw [Ideal.pointwise_smul_def]; exact Ideal.map_bot)`. Consider the case `simp`.
-/
theorem smul_ne_bot (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (B : Ideal (𝓞 (hostE ζ a b)))
    (hB : B ≠ ⊥) : σ • B ≠ ⊥ := by
  intro h
  apply hB
  have h' : σ⁻¹ • σ • B = σ⁻¹ • (⊥ : Ideal (𝓞 (hostE ζ a b))) := by rw [h]
  rw [inv_smul_smul] at h'
  rw [h']
  first
  | exact smul_bot _
  | exact Ideal.map_bot
  | (rw [Ideal.pointwise_smul_def]; exact Ideal.map_bot)
  | simp

/- English proof (translation)
Establish `hc : ∀ z : 𝓞 (hostE ζ a b), algebraMap (𝓞 (hostE ζ a b)) (hostE ζ a b) (σ • z) = σ (algebraMap (𝓞 (hostE ζ a b)) (hostE ζ a b) z)`. Introduce `z`. Use `first`. Consider the case `rfl`. Consider the case `simp`.

Consider the case `exact NumberField.RingOfIntegers.coe_smul _ _`. Establish `h1 : ((σ • B : Ideal (𝓞 (hostE ζ a b))) : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.mpr (smul_ne_bot σ B hB)`. Establish `h2 : ((B : Ideal (𝓞 (hostE ζ a b))) : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.mpr hB`. Rewrite using `[FractionalIdeal.mem_inv_iff h1, FractionalIdeal.mem_inv_iff h2]`. Prove the components needed by the constructor for the conclusion.

Introduce `h z hz`. Rewrite `hz` using `[FractionalIdeal.mem_coeIdeal]`. Take `⟨z', hz', rfl⟩` from `hz`. Establish `hm : σ • z' ∈ σ • B` using `by first`. Consider the case `exact Ideal.smul_mem_pointwise_smul σ z' B hz'`.

Consider the case `exact Submodule.smul_mem_pointwise_smul z' σ B hz'`. Consider the case `exact Set.smul_mem_smul_set hz'`. Use `h (algebraMap _ _ (σ • z')) (by` as an intermediate fact. Rewrite using `[FractionalIdeal.mem_coeIdeal]`. Conclude with `⟨σ • z', hm, rfl⟩)`.

Rewrite `this`, the goal using `[mem_one_iff']`. Rewrite `this` using `[hc, ← map_mul, integ_iff]`. Then use the resulting hypothesis. Introduce `h w hw`. Rewrite `hw` using `[FractionalIdeal.mem_coeIdeal]`. Take `⟨w', hw', rfl⟩` from `hw`.

Establish `hv : σ⁻¹ • w' ∈ B` using `by first`. Consider the case `exact (Ideal.mem_pointwise_smul_iff_inv_smul_mem).mp hw'`. Consider the case `exact Ideal.mem_pointwise_smul_iff_inv_smul_mem.mp hw'`. Consider the case `(obtain ⟨v, hv, rfl⟩ := hw'; simpa using hv)`. Use `h (algebraMap _ _ (σ⁻¹ • w')) (by` as an intermediate fact.

Rewrite using `[FractionalIdeal.mem_coeIdeal]`. Conclude with `⟨σ⁻¹ • w', hv, rfl⟩)`. Rewrite `this`, the goal using `[mem_one_iff']`. Establish `hw2 : w' = σ • (σ⁻¹ • w')` using `(smul_inv_smul σ w').symm`. Rewrite using `[hw2, hc, ← map_mul, integ_iff]`.

Conclude with `this`.
-/
theorem mem_inv_smul (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (B : Ideal (𝓞 (hostE ζ a b)))
    (hB : B ≠ ⊥) (y : hostE ζ a b) :
    σ y ∈ ((σ • B : Ideal (𝓞 (hostE ζ a b))) :
        FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b))⁻¹ ↔
      y ∈ ((B : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)))⁻¹ := by
  have hc : ∀ z : 𝓞 (hostE ζ a b),
      algebraMap (𝓞 (hostE ζ a b)) (hostE ζ a b) (σ • z) =
        σ (algebraMap (𝓞 (hostE ζ a b)) (hostE ζ a b) z) := by
    intro z
    first
    | rfl
    | simp
    | exact NumberField.RingOfIntegers.coe_smul _ _
  have h1 : ((σ • B : Ideal (𝓞 (hostE ζ a b))) :
      FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (smul_ne_bot σ B hB)
  have h2 : ((B : Ideal (𝓞 (hostE ζ a b))) :
      FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hB
  rw [FractionalIdeal.mem_inv_iff h1, FractionalIdeal.mem_inv_iff h2]
  constructor
  · intro h z hz
    rw [FractionalIdeal.mem_coeIdeal] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    have hm : σ • z' ∈ σ • B := by
      first
      | exact Ideal.smul_mem_pointwise_smul σ z' B hz'
      | exact Submodule.smul_mem_pointwise_smul z' σ B hz'
      | exact Set.smul_mem_smul_set hz'
    have := h (algebraMap _ _ (σ • z')) (by
      rw [FractionalIdeal.mem_coeIdeal]
      exact ⟨σ • z', hm, rfl⟩)
    rw [mem_one_iff'] at this ⊢
    rwa [hc, ← map_mul, integ_iff] at this
  · intro h w hw
    rw [FractionalIdeal.mem_coeIdeal] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    have hv : σ⁻¹ • w' ∈ B := by
      first
      | exact (Ideal.mem_pointwise_smul_iff_inv_smul_mem).mp hw'
      | exact Ideal.mem_pointwise_smul_iff_inv_smul_mem.mp hw'
      | (obtain ⟨v, hv, rfl⟩ := hw'; simpa using hv)
    have := h (algebraMap _ _ (σ⁻¹ • w')) (by
      rw [FractionalIdeal.mem_coeIdeal]
      exact ⟨σ⁻¹ • w', hv, rfl⟩)
    rw [mem_one_iff'] at this ⊢
    have hw2 : w' = σ • (σ⁻¹ • w') := (smul_inv_smul σ w').symm
    rw [hw2, hc, ← map_mul, integ_iff]
    exact this

end OrdUnimod

open OrdUnimod

/- English proof (translation)
Establish `hc` using `h.comap_eq`. Establish `key : ∀ y : 𝓞 (hostE ζ a b), y ∈ P ↔ σ • y ∈ P`. Introduce `y`. Use `congrArg (fun I : Ideal (𝓞 (hostE ζ a b)) => y ∈ I) hc` as an intermediate fact. Simplify using `only [Ideal.mem_comap] at this`.

Rewrite using `[← this]`. Use `first`. Consider the case `rfl`. Consider the case `exact Iff.rfl`. Consider the case `simp`.

Rewrite using `[MulAction.mem_stabilizer_iff]`. Use extensionality with `x`. Rewrite using `[Ideal.mem_pointwise_smul_iff_inv_smul_mem]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Use `(key _).mp hx` as an intermediate fact. Rewrite `this` using `[smul_inv_smul]`. Then use the resulting hypothesis. Introduce `hx`. Conclude with `(key _).mpr (by rw [smul_inv_smul]; exact hx)`.
-/
private theorem mem_stabilizer_of_isArithFrobAt {L : Type} [Field L] [NumberField L] {ζ a b : L}
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime]
    (h : IsArithFrobAt ℤ σ P) :
    σ ∈ MulAction.stabilizer (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) P := by
  have hc := h.comap_eq
  have key : ∀ y : 𝓞 (hostE ζ a b), y ∈ P ↔ σ • y ∈ P := by
    intro y
    have := congrArg (fun I : Ideal (𝓞 (hostE ζ a b)) => y ∈ I) hc
    simp only [Ideal.mem_comap] at this
    rw [← this]
    first
    | rfl
    | exact Iff.rfl
    | simp
  rw [MulAction.mem_stabilizer_iff]
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  constructor
  · intro hx
    have := (key _).mp hx
    rwa [smul_inv_smul] at this
  · intro hx
    exact (key _).mpr (by rw [smul_inv_smul]; exact hx)

/- English proof (translation)
Establish `hodd' : q.Prime ∧ d.Prime ∧ q ≠ d ∧ q ≠ 2 ∧ d ≠ 2` using `hodd`. Establish `hL' : IsPrimitiveRoot ζ (2 ^ (e + 2)) ∧ a ^ 2 = -(q : L) ∧ b ^ 2 = -(d : L) ∧ IntermediateField.adjoin ℚ {ζ, a, b} = ⊤` using `hL`. Establish `hp : p.Prime` using `hpF.out`. Establish `hspec` using `(hostGalSpec e q d hodd L ζ a b hL τ).2.1`. Assume the negation of the conclusion as `hs`.

Establish `hs' : (galE e ζ a b τ).1.2 = -1` using `(Int.units_eq_one_or _).resolve_left hs`. Establish `hτb : τ (bE ζ a b) = -(bE ζ a b)`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hspec, hs']`. Use `first`.

Consider the case `simp [bE]`. Consider the case `(simp; rfl)`. Establish `hb2 : (bE ζ a b) ^ 2 = algebraMap ℤ (hostE ζ a b) (-(d : ℤ))`. Apply `Subtype.ext` to reduce the goal to its premises. Use `first`.

Consider the case `simp [bE, hL'.2.2.1]`. Consider the case `(simp [bE]; exact hL'.2.2.1)`. Establish `hbI : IsIntegral ℤ (bE ζ a b)`. Establish `h` using `isIntegral_algebraMap (R := ℤ) (A := hostE ζ a b) (x := -(d : ℤ))`. Rewrite `h` using `[← hb2]`.

Conclude with `IsIntegral.of_pow two_pos h`. Take `⟨β, hβ⟩` from `(IsIntegralClosure.isIntegral_iff (A := 𝓞 (hostE ζ a b))).mp hbI`. Establish `hinj : Function.Injective (algebraMap (𝓞 (hostE ζ a b)) (hostE ζ a b))` using `by first`. Consider the case `exact IsIntegralClosure.algebraMap_injective (𝓞 (hostE ζ a b)) ℤ (hostE ζ a b)`. Consider the case `exact FaithfulSMul.algebraMap_injective _ _`.

Consider the case `exact NoZeroSMulDivisors.algebraMap_injective _ _`. Consider the case `exact IsFractionRing.injective _ _`. Establish `hcomm : ∀ z : 𝓞 (hostE ζ a b), algebraMap (𝓞 (hostE ζ a b)) (hostE ζ a b) (τ • z) = τ (algebraMap (𝓞 (hostE ζ a b)) (hostE ζ a b) z)`. Introduce `z`. Use `first`.

Consider the case `rfl`. Consider the case `simp`. Consider the case `exact NumberField.RingOfIntegers.coe_smul _ _`. Establish `hβ2 : β ^ 2 = -(d : 𝓞 (hostE ζ a b))`. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[map_pow, hβ, hb2]`. Simplify using the standard rewrite rules. Establish `hZ : ∀ x : ℤ, (x : 𝓞 (hostE ζ a b)) ∈ P ↔ (p : ℤ) ∣ x`. Introduce `x`. Rewrite using `[← eq_intCast (algebraMap ℤ (𝓞 (hostE ζ a b))) x, ← Ideal.mem_span_singleton]`.

Use `first`. Consider the case `exact (Ideal.mem_of_liesOver P (span {(p : ℤ)}) x).symm`. Consider the case `(rw [Ideal.over_def P (span {(p : ℤ)})]; rfl)`. Consider the case `(rw [Ideal.LiesOver.over (P := P) (p := span {(p : ℤ)})]; rfl)`. Consider the case `(rw [Ideal.over_def P (span {(p : ℤ)})]; simp [Ideal.under])`.

Establish `hsq : IsSquare (((-(d : ℤ)) : ℤ) : ZMod p)`. Establish `hl : legendreSym p (-(d : ℤ)) = 1` using `by first`. Consider the case `(rw [jacobiSym.legendreSym.to_jacobiSym]; exact hj)`. Consider the case `(rw [← jacobiSym.legendreSym.to_jacobiSym] at hj; exact hj)`. Consider the case `(simp [jacobiSym, Nat.primeFactorsList_prime hp] at hj; exact hj)`.

Establish `h0 : (((-(d : ℤ)) : ℤ) : ZMod p) ≠ 0`. Introduce `h0`. Use `(legendreSym.eq_zero_iff p (-(d : ℤ))).mpr h0` as an intermediate fact. Rewrite `this` using `[hl]`. Conclude with `one_ne_zero this`.

Conclude with `(legendreSym.eq_one_iff p h0).mp hl`. Take `⟨c, hc⟩` from `hsq`. Take `⟨r, hr⟩ : ∃ r : ℤ, (r : ZMod p) = c` from `⟨c.val, by first`. Consider the case `simp`. Consider the case `exact_mod_cast ZMod.natCast_zmod_val c⟩`.

Establish `hdiv : (p : ℤ) ∣ r * r + d`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Use `push_cast`. Rewrite using `[hr, ← hc]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hstab : τ • P = P` using `MulAction.mem_stabilizer_iff.mp hτ`. Establish `key : ∀ s : ℤ, β - (s : 𝓞 (hostE ζ a b)) ∈ P → False`. Introduce `s hs`. Establish `h1 : τ • (β - (s : 𝓞 (hostE ζ a b))) ∈ P`.

Establish `hm : τ • (β - (s : 𝓞 (hostE ζ a b))) ∈ τ • P` using `by first`. Consider the case `exact Ideal.smul_mem_pointwise_smul τ _ P hs`. Consider the case `exact Submodule.smul_mem_pointwise_smul _ τ P hs`. Consider the case `exact Set.smul_mem_smul_set hs`. Rewrite `hm` using `[hstab]`. Then use the resulting hypothesis.

Establish `h2 : τ • (β - (s : 𝓞 (hostE ζ a b))) = -β - (s : 𝓞 (hostE ζ a b))`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[hcomm]`. Simplify using `[hβ, hτb]`. Rewrite `h1` using `[h2]`.

Establish `e3 : ((4 * (d : ℤ) : ℤ) : 𝓞 (hostE ζ a b)) = -(((β - s) - (-β - s)) * ((β - s) - (-β - s)))`. Use `push_cast`. Take the linear combination `4 * hβ2`. Establish `h3 : ((4 * (d : ℤ) : ℤ) : 𝓞 (hostE ζ a b)) ∈ P`. Rewrite using `[e3]`.

Conclude with `neg_mem (Ideal.mul_mem_left _ _ (sub_mem hs h1))`. Establish `h4 : p ∣ 4 * d`. Use `(hZ _).mp h3` as an intermediate fact. Conclude with `this` after adjusting the coercions. Break down `(Nat.Prime.dvd_mul hp).mp h4 with h5 | h5` into its components or cases.

Conclude with `hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h5)))`. Conclude with `hpd ((Nat.prime_dvd_prime_iff_eq hp hodd'.2.1).mp h5)`. Establish `hm : (β - (r : 𝓞 (hostE ζ a b))) * (β - ((-r : ℤ) : 𝓞 (hostE ζ a b))) ∈ P`. Establish `e4 : (β - (r : 𝓞 (hostE ζ a b))) * (β - ((-r : ℤ) : 𝓞 (hostE ζ a b))) = (((-(r * r + d)) : ℤ) : 𝓞 (hostE ζ a b))`. Use `push_cast`.

Take the linear combination `hβ2`. Rewrite using `[e4, hZ]`. Conclude with `dvd_neg.mpr hdiv`. Break down `hPp.mem_or_mem hm with h | h` into its components or cases. Conclude with `key r h`.

Conclude with `key (-r) h`.
-/
private theorem galE_fst_snd_eq_one_of_mem_stabilizer_of_jacobiSym_eq_one {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
    (hodd : HypOdd q d) (hL : IsLayer (e + 2) q d ζ a b)
    (p : ℕ) [hpF : Fact p.Prime] (hp2 : p ≠ 2) (hpd : p ≠ d)
    (P : Ideal (𝓞 (hostE ζ a b))) [hPp : P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
    (hj : jacobiSym (-(d : ℤ)) p = 1)
    (τ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b)
    (hτ : τ ∈ MulAction.stabilizer (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) P) :
    (galE e ζ a b τ).1.2 = 1 := by
  have hodd' : q.Prime ∧ d.Prime ∧ q ≠ d ∧ q ≠ 2 ∧ d ≠ 2 := hodd
  have hL' : IsPrimitiveRoot ζ (2 ^ (e + 2)) ∧ a ^ 2 = -(q : L) ∧ b ^ 2 = -(d : L) ∧
      IntermediateField.adjoin ℚ {ζ, a, b} = ⊤ := hL
  have hp : p.Prime := hpF.out
  have hspec := (hostGalSpec e q d hodd L ζ a b hL τ).2.1
  by_contra hs
  have hs' : (galE e ζ a b τ).1.2 = -1 := (Int.units_eq_one_or _).resolve_left hs
  have hτb : τ (bE ζ a b) = -(bE ζ a b) := by
    apply Subtype.ext
    rw [hspec, hs']
    first
    | simp [bE]
    | (simp; rfl)
  have hb2 : (bE ζ a b) ^ 2 = algebraMap ℤ (hostE ζ a b) (-(d : ℤ)) := by
    apply Subtype.ext
    first
    | simp [bE, hL'.2.2.1]
    | (simp [bE]; exact hL'.2.2.1)
  have hbI : IsIntegral ℤ (bE ζ a b) := by
    have h := isIntegral_algebraMap (R := ℤ) (A := hostE ζ a b) (x := -(d : ℤ))
    rw [← hb2] at h
    exact IsIntegral.of_pow two_pos h
  obtain ⟨β, hβ⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 (hostE ζ a b))).mp hbI
  have hinj : Function.Injective (algebraMap (𝓞 (hostE ζ a b)) (hostE ζ a b)) := by
    first
    | exact IsIntegralClosure.algebraMap_injective (𝓞 (hostE ζ a b)) ℤ (hostE ζ a b)
    | exact FaithfulSMul.algebraMap_injective _ _
    | exact NoZeroSMulDivisors.algebraMap_injective _ _
    | exact IsFractionRing.injective _ _
  have hcomm : ∀ z : 𝓞 (hostE ζ a b),
      algebraMap (𝓞 (hostE ζ a b)) (hostE ζ a b) (τ • z) =
        τ (algebraMap (𝓞 (hostE ζ a b)) (hostE ζ a b) z) := by
    intro z
    first
    | rfl
    | simp
    | exact NumberField.RingOfIntegers.coe_smul _ _
  have hβ2 : β ^ 2 = -(d : 𝓞 (hostE ζ a b)) := by
    apply hinj
    rw [map_pow, hβ, hb2]
    simp
  have hZ : ∀ x : ℤ, (x : 𝓞 (hostE ζ a b)) ∈ P ↔ (p : ℤ) ∣ x := by
    intro x
    rw [← eq_intCast (algebraMap ℤ (𝓞 (hostE ζ a b))) x, ← Ideal.mem_span_singleton]
    first
    | exact (Ideal.mem_of_liesOver P (span {(p : ℤ)}) x).symm
    | (rw [Ideal.over_def P (span {(p : ℤ)})]; rfl)
    | (rw [Ideal.LiesOver.over (P := P) (p := span {(p : ℤ)})]; rfl)
    | (rw [Ideal.over_def P (span {(p : ℤ)})]; simp [Ideal.under])
  have hsq : IsSquare (((-(d : ℤ)) : ℤ) : ZMod p) := by
    have hl : legendreSym p (-(d : ℤ)) = 1 := by
      first
      | (rw [jacobiSym.legendreSym.to_jacobiSym]; exact hj)
      | (rw [← jacobiSym.legendreSym.to_jacobiSym] at hj; exact hj)
      | (simp [jacobiSym, Nat.primeFactorsList_prime hp] at hj; exact hj)
    have h0 : (((-(d : ℤ)) : ℤ) : ZMod p) ≠ 0 := by
      intro h0
      have := (legendreSym.eq_zero_iff p (-(d : ℤ))).mpr h0
      rw [hl] at this
      exact one_ne_zero this
    exact (legendreSym.eq_one_iff p h0).mp hl
  obtain ⟨c, hc⟩ := hsq
  obtain ⟨r, hr⟩ : ∃ r : ℤ, (r : ZMod p) = c := ⟨c.val, by
    first
    | simp
    | exact_mod_cast ZMod.natCast_zmod_val c⟩
  have hdiv : (p : ℤ) ∣ r * r + d := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hr, ← hc]
    push_cast
    ring
  have hstab : τ • P = P := MulAction.mem_stabilizer_iff.mp hτ
  have key : ∀ s : ℤ, β - (s : 𝓞 (hostE ζ a b)) ∈ P → False := by
    intro s hs
    have h1 : τ • (β - (s : 𝓞 (hostE ζ a b))) ∈ P := by
      have hm : τ • (β - (s : 𝓞 (hostE ζ a b))) ∈ τ • P := by
        first
        | exact Ideal.smul_mem_pointwise_smul τ _ P hs
        | exact Submodule.smul_mem_pointwise_smul _ τ P hs
        | exact Set.smul_mem_smul_set hs
      rwa [hstab] at hm
    have h2 : τ • (β - (s : 𝓞 (hostE ζ a b))) = -β - (s : 𝓞 (hostE ζ a b)) := by
      apply hinj
      rw [hcomm]
      simp [hβ, hτb]
    rw [h2] at h1
    have e3 : ((4 * (d : ℤ) : ℤ) : 𝓞 (hostE ζ a b)) =
        -(((β - s) - (-β - s)) * ((β - s) - (-β - s))) := by
      push_cast
      linear_combination 4 * hβ2
    have h3 : ((4 * (d : ℤ) : ℤ) : 𝓞 (hostE ζ a b)) ∈ P := by
      rw [e3]
      exact neg_mem (Ideal.mul_mem_left _ _ (sub_mem hs h1))
    have h4 : p ∣ 4 * d := by
      have := (hZ _).mp h3
      exact_mod_cast this
    rcases (Nat.Prime.dvd_mul hp).mp h4 with h5 | h5
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h5)))
    · exact hpd ((Nat.prime_dvd_prime_iff_eq hp hodd'.2.1).mp h5)
  have hm : (β - (r : 𝓞 (hostE ζ a b))) * (β - ((-r : ℤ) : 𝓞 (hostE ζ a b))) ∈ P := by
    have e4 : (β - (r : 𝓞 (hostE ζ a b))) * (β - ((-r : ℤ) : 𝓞 (hostE ζ a b))) =
        (((-(r * r + d)) : ℤ) : 𝓞 (hostE ζ a b)) := by
      push_cast
      linear_combination hβ2
    rw [e4, hZ]
    exact dvd_neg.mpr hdiv
  rcases hPp.mem_or_mem hm with h | h
  · exact key r h
  · exact key (-r) h

/- English proof (translation)
Introduce `e q d hH L _ _ ζ a b hL p _ P _ _`. Establish `hH' : q.Prime ∧ d.Prime ∧ q % 8 = 3 ∧ d % 16 = 7 ∧ jacobiSym (-(d : ℤ)) q = 1` using `hH`. Take `⟨hq, hd, hq8, hd16, -⟩` from `hH'`. Establish `hq2 : q ≠ 2` using `by omega`. Establish `hd2 : d ≠ 2` using `by omega`.

Establish `hodd : HypOdd q d` using `show q.Prime ∧ d.Prime ∧ q ≠ d ∧ q ≠ 2 ∧ d ≠ 2 from ⟨hq, hd, by omega, hq2, hd2⟩`. Establish `hG` using `hostGalois e q d hodd L ζ a b hL`. Establish `hmul` using `hG.2.2.1`. Establish `hbij` using `hG.2.2.2`. Establish `hg1 : galE e ζ a b 1 = 1` using `by first`.

Consider the case `exact map_one (MonoidHom.mk' (galE e ζ a b) hmul)`. Consider the case `(have h11 := hmul 1 1; rw [one_mul] at h11; exact (mul_eq_left.mp h11.symm))`. Establish `hPsi : ∀ g : GG e, g ∈ Psi e ↔ g.1.2 = 1`. Introduce `g`. Use `first`.

Consider the case `exact Iff.rfl`. Consider the case `(rw [Psi, MonoidHom.mem_ker]; rfl)`. Consider the case `simp [Psi, chD]`. Establish `hS` using `hostSplitK_of (hostFrob_of hostGalois hostGalSpec) e q d hH L ζ a b hL`. Establish `hF` using `hostFrob_of hostGalois hostGalSpec e q d hodd L ζ a b hL`.

Establish `hcq : Nat.Coprime q (2 ^ (e + 2))` using `Nat.Coprime.pow_right _ ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)`. Establish `hcd : Nat.Coprime d (2 ^ (e + 2))` using `Nat.Coprime.pow_right _ ((Nat.coprime_primes hd Nat.prime_two).mpr hd2)`. Establish `hD` using `hostDecomp e q d hH L ζ a b hL (ZMod.unitOfCoprime q hcq) (ZMod.unitOfCoprime d hcd) (ZMod.coe_unitOfCoprime _ _) (ZMod.coe_unitOfCoprime _ _)`. Establish `key : (∀ σ τ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, τ ∈ MulAction.stabilizer _ P → (galE e ζ a b (σ * τ) ∈ Psi e ↔ galE e ζ a b σ ∈ Psi e)) ↔ ∀ τ ∈ MulAction.stabilizer (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) P, galE e ζ a b τ ∈ Psi e`. Prove the components needed by the constructor for the conclusion.

Introduce `h τ hτ`. Establish `h1` using `h 1 τ hτ`. Rewrite `h1` using `[one_mul]`. Conclude with `h1.mpr (by rw [hg1]; exact (Psi e).one_mem)`. Introduce `h σ τ hτ`.

Rewrite using `[hmul]`. Conclude with `Subgroup.mul_mem_cancel_right _ (h τ hτ)`. Rewrite using `[key]`. Distinguish the cases in `hp2 : p = 2`. Substitute `hp2 haveI : P.LiesOver (span {(2 : ℤ)}) := by` using the available equality.

Simplify using `using (inferInstance : P.LiesOver (span {((2 : ℕ) : ℤ)}))`. Conclude with `iff_of_true (fun τ hτ => ((hD τ).1 P).mp hτ) ((hS.1 2 Nat.prime_two).mpr (Or.inl rfl))`. Distinguish the cases in `hpq : p = q`. Substitute `hpq` using the available equality. Use `iff_of_true (fun τ hτ => ?_) hS.2.2.1` and prove the remaining obligations.

Rewrite using `[hPsi]`. Conclude with `(((hD τ).2.1 P).mp hτ).1`. Distinguish the cases in `hpd : p = d`. Substitute `hpd` using the available equality. Use `iff_of_false (fun h => ?_) (by rw [hS.2.1]; decide)` and prove the remaining obligations.

Take `⟨σ0, hσ0⟩` from `hbij.2 (((-1 : ℤˣ), (-1 : ℤˣ)), hcl e (ZMod.unitOfCoprime p hcd))`. Establish `hst : σ0 ∈ MulAction.stabilizer _ P` using `((hD σ0).2.2 P).mpr ⟨1, by rw [hσ0, pow_one], by rw [hσ0, pow_one]⟩`. Establish `h1` using `(hPsi _).mp (h σ0 hst)`. Rewrite `h1` using `[hσ0]`. Conclude with `absurd (congrArg Units.val h1) (by norm_num)`.

Take `⟨φ, hφ⟩` from `(hF p hp2 hpq hpd P).1`. Rewrite using `[← hS.2.2.2 p hp2 hpq hpd P φ hφ]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `h φ (mem_stabilizer_of_isArithFrobAt φ P hφ)`.

Introduce `hφΨ τ hτ`. Rewrite using `[hPsi]`. Establish `hj : jacobiSym (-(d : ℤ)) p = 1`. Establish `h2` using `(hS.2.2.2 p hp2 hpq hpd P φ hφ).mp hφΨ`. Break down `(hS.1 p (Fact.out)).mp h2 with h | ⟨-, h⟩` into its components or cases.

Conclude with `absurd h hp2`. Conclude with `h`. Conclude with `galE_fst_snd_eq_one_of_mem_stabilizer_of_jacobiSym_eq_one hodd hL p hp2 hpd P hj τ hτ`.
-/
theorem hostOrdinary : HostOrdinary := by
  intro e q d hH L _ _ ζ a b hL p _ P _ _
  have hH' : q.Prime ∧ d.Prime ∧ q % 8 = 3 ∧ d % 16 = 7 ∧ jacobiSym (-(d : ℤ)) q = 1 := hH
  obtain ⟨hq, hd, hq8, hd16, -⟩ := hH'
  have hq2 : q ≠ 2 := by omega
  have hd2 : d ≠ 2 := by omega
  have hodd : HypOdd q d := show q.Prime ∧ d.Prime ∧ q ≠ d ∧ q ≠ 2 ∧ d ≠ 2 from
    ⟨hq, hd, by omega, hq2, hd2⟩
  have hG := hostGalois e q d hodd L ζ a b hL
  have hmul := hG.2.2.1
  have hbij := hG.2.2.2
  have hg1 : galE e ζ a b 1 = 1 := by
    first
    | exact map_one (MonoidHom.mk' (galE e ζ a b) hmul)
    | (have h11 := hmul 1 1; rw [one_mul] at h11; exact (mul_eq_left.mp h11.symm))
  have hPsi : ∀ g : GG e, g ∈ Psi e ↔ g.1.2 = 1 := by
    intro g
    first
    | exact Iff.rfl
    | (rw [Psi, MonoidHom.mem_ker]; rfl)
    | simp [Psi, chD]
  have hS := hostSplitK_of (hostFrob_of hostGalois hostGalSpec) e q d hH L ζ a b hL
  have hF := hostFrob_of hostGalois hostGalSpec e q d hodd L ζ a b hL
  have hcq : Nat.Coprime q (2 ^ (e + 2)) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)
  have hcd : Nat.Coprime d (2 ^ (e + 2)) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hd Nat.prime_two).mpr hd2)
  have hD := hostDecomp e q d hH L ζ a b hL (ZMod.unitOfCoprime q hcq) (ZMod.unitOfCoprime d hcd)
    (ZMod.coe_unitOfCoprime _ _) (ZMod.coe_unitOfCoprime _ _)
  have key : (∀ σ τ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, τ ∈ MulAction.stabilizer _ P →
      (galE e ζ a b (σ * τ) ∈ Psi e ↔ galE e ζ a b σ ∈ Psi e)) ↔
      ∀ τ ∈ MulAction.stabilizer (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) P, galE e ζ a b τ ∈ Psi e := by
    constructor
    · intro h τ hτ
      have h1 := h 1 τ hτ
      rw [one_mul] at h1
      exact h1.mpr (by rw [hg1]; exact (Psi e).one_mem)
    · intro h σ τ hτ
      rw [hmul]
      exact Subgroup.mul_mem_cancel_right _ (h τ hτ)
  rw [key]
  by_cases hp2 : p = 2
  · subst hp2
    haveI : P.LiesOver (span {(2 : ℤ)}) := by
      simpa using (inferInstance : P.LiesOver (span {((2 : ℕ) : ℤ)}))
    exact iff_of_true (fun τ hτ => ((hD τ).1 P).mp hτ) ((hS.1 2 Nat.prime_two).mpr (Or.inl rfl))
  by_cases hpq : p = q
  · subst hpq
    refine iff_of_true (fun τ hτ => ?_) hS.2.2.1
    rw [hPsi]
    exact (((hD τ).2.1 P).mp hτ).1
  by_cases hpd : p = d
  · subst hpd
    refine iff_of_false (fun h => ?_) (by rw [hS.2.1]; decide)
    obtain ⟨σ0, hσ0⟩ := hbij.2 (((-1 : ℤˣ), (-1 : ℤˣ)), hcl e (ZMod.unitOfCoprime p hcd))
    have hst : σ0 ∈ MulAction.stabilizer _ P :=
      ((hD σ0).2.2 P).mpr ⟨1, by rw [hσ0, pow_one], by rw [hσ0, pow_one]⟩
    have h1 := (hPsi _).mp (h σ0 hst)
    rw [hσ0] at h1
    exact absurd (congrArg Units.val h1) (by norm_num)
  obtain ⟨φ, hφ⟩ := (hF p hp2 hpq hpd P).1
  rw [← hS.2.2.2 p hp2 hpq hpd P φ hφ]
  constructor
  · intro h
    exact h φ (mem_stabilizer_of_isArithFrobAt φ P hφ)
  · intro hφΨ τ hτ
    rw [hPsi]
    have hj : jacobiSym (-(d : ℤ)) p = 1 := by
      have h2 := (hS.2.2.2 p hp2 hpq hpd P φ hφ).mp hφΨ
      rcases (hS.1 p (Fact.out)).mp h2 with h | ⟨-, h⟩
      · exact absurd h hp2
      · exact h
    exact galE_fst_snd_eq_one_of_mem_stabilizer_of_jacobiSym_eq_one hodd hL p hp2 hpd P hj τ hτ

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/- English proof (translation)
Introduce `e q d _ L _ _ ζ a b _ σ _ 𝔟 h x`. Establish `hd1 : FractionalIdeal.dual (𝓞 (KinE ζ a b)) (KinE ζ a b) (1 : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) ≠ 0` using `by first`. Consider the case `exact FractionalIdeal.dual_ne_zero _ _ one_ne_zero`. Consider the case `exact FractionalIdeal.dual_ne_zero one_ne_zero`. Consider the case `exact FractionalIdeal.dual_ne_zero (𝓞 (KinE ζ a b)) (KinE ζ a b) one_ne_zero`.

Establish `hprod : ((𝔟 : Ideal (𝓞 (hostE ζ a b))) : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) * ((σ • 𝔟 : Ideal (𝓞 (hostE ζ a b))) : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) = (FractionalIdeal.dual (𝓞 (KinE ζ a b)) (KinE ζ a b) (1 : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE …`. Rewrite using `[← FractionalIdeal.coeIdeal_mul, ← h]`. Use `first`. Consider the case `exact coeIdeal_differentIdeal _ _ _ _`. Consider the case `exact coeIdeal_differentIdeal (𝓞 (KinE ζ a b)) (KinE ζ a b) (hostE ζ a b) (𝓞 (hostE ζ a b))`.

Consider the case `exact coeIdeal_differentIdeal (A := 𝓞 (KinE ζ a b)) (K := KinE ζ a b) (L := hostE ζ a b) (B := 𝓞 (hostE ζ a b))`. Establish `hne : ((𝔟 : Ideal (𝓞 (hostE ζ a b))) : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) * ((σ • 𝔟 : Ideal (𝓞 (hostE ζ a b))) : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) ≠ 0`. Rewrite using `[hprod]`. Conclude with `inv_ne_zero hd1`. Establish `hb` using `left_ne_zero_of_mul hne`.

Establish `hsb` using `right_ne_zero_of_mul hne`. Establish `hb0 : 𝔟 ≠ ⊥` using `FractionalIdeal.coeIdeal_ne_zero.mp hb`. Establish `hd : FractionalIdeal.dual (𝓞 (KinE ζ a b)) (KinE ζ a b) (1 : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) = (((𝔟 : Ideal (𝓞 (hostE ζ a b))) : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) * ((σ • 𝔟 : Ideal (𝓞 (hostE ζ a b))) : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ …`. Rewrite using `[hprod, inv_inv]`. Establish `hJ : FractionalIdeal.dual (𝓞 (KinE ζ a b)) (KinE ζ a b) (((σ • 𝔟 : Ideal (𝓞 (hostE ζ a b))) : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)))⁻¹ = ((𝔟 : Ideal (𝓞 (hostE ζ a b))) : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b))⁻¹`.

Rewrite using `[FractionalIdeal.dual_eq_mul_inv, hd, inv_inv, mul_inv, mul_assoc, inv_mul_cancel₀ hsb, mul_one]`. Establish `hx : ∀ z : hostE ζ a b, z ∈ ((𝔟 : Ideal (𝓞 (hostE ζ a b))) : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b))⁻¹ ↔ ∀ w ∈ (((σ • 𝔟 : Ideal (𝓞 (hostE ζ a b))) : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)))⁻¹, Algebra.trace (KinE ζ a b) (hostE ζ a b) (z * w) ∈ (algebraMap (𝓞 ( …`. Introduce `z`. Rewrite using `[← hJ, FractionalIdeal.mem_dual (inv_ne_zero hsb)]`. Simplify using `only [Algebra.traceForm_apply]`.

Rewrite using `[hx x]`. Prove the components needed by the constructor for the conclusion. Introduce `hw y hy`. Conclude with `hw _ ((mem_inv_smul σ 𝔟 hb0 y).mpr hy)`. Introduce `hy w hw`.

Establish `hw' : σ (σ.symm w) ∈ (((σ • 𝔟 : Ideal (𝓞 (hostE ζ a b))) : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)))⁻¹`. Rewrite using `[AlgEquiv.apply_symm_apply]`. Conclude with `hw`. Use `hy (σ.symm w) ((mem_inv_smul σ 𝔟 hb0 _).mp hw')` as an intermediate fact. Rewrite `this` using `[AlgEquiv.apply_symm_apply]`. Then use the resulting hypothesis.
-/
theorem hostUnimodular : HostUnimodular := by
  intro e q d _ L _ _ ζ a b _ σ _ 𝔟 h x
  have hd1 : FractionalIdeal.dual (𝓞 (KinE ζ a b)) (KinE ζ a b)
      (1 : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) ≠ 0 := by
    first
    | exact FractionalIdeal.dual_ne_zero _ _ one_ne_zero
    | exact FractionalIdeal.dual_ne_zero one_ne_zero
    | exact FractionalIdeal.dual_ne_zero (𝓞 (KinE ζ a b)) (KinE ζ a b) one_ne_zero
  have hprod : ((𝔟 : Ideal (𝓞 (hostE ζ a b))) :
      FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) *
      ((σ • 𝔟 : Ideal (𝓞 (hostE ζ a b))) :
        FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) =
      (FractionalIdeal.dual (𝓞 (KinE ζ a b)) (KinE ζ a b)
        (1 : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)))⁻¹ := by
    rw [← FractionalIdeal.coeIdeal_mul, ← h]
    first
    | exact coeIdeal_differentIdeal _ _ _ _
    | exact coeIdeal_differentIdeal (𝓞 (KinE ζ a b)) (KinE ζ a b) (hostE ζ a b) (𝓞 (hostE ζ a b))
    | exact coeIdeal_differentIdeal (A := 𝓞 (KinE ζ a b)) (K := KinE ζ a b) (L := hostE ζ a b)
        (B := 𝓞 (hostE ζ a b))
  have hne : ((𝔟 : Ideal (𝓞 (hostE ζ a b))) :
      FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) *
      ((σ • 𝔟 : Ideal (𝓞 (hostE ζ a b))) :
        FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) ≠ 0 := by
    rw [hprod]; exact inv_ne_zero hd1
  have hb := left_ne_zero_of_mul hne
  have hsb := right_ne_zero_of_mul hne
  have hb0 : 𝔟 ≠ ⊥ := FractionalIdeal.coeIdeal_ne_zero.mp hb
  have hd : FractionalIdeal.dual (𝓞 (KinE ζ a b)) (KinE ζ a b)
      (1 : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) =
      (((𝔟 : Ideal (𝓞 (hostE ζ a b))) :
        FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) *
      ((σ • 𝔟 : Ideal (𝓞 (hostE ζ a b))) :
        FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)))⁻¹ := by
    rw [hprod, inv_inv]
  have hJ : FractionalIdeal.dual (𝓞 (KinE ζ a b)) (KinE ζ a b)
      (((σ • 𝔟 : Ideal (𝓞 (hostE ζ a b))) :
        FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)))⁻¹ =
      ((𝔟 : Ideal (𝓞 (hostE ζ a b))) :
        FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b))⁻¹ := by
    rw [FractionalIdeal.dual_eq_mul_inv, hd, inv_inv, mul_inv, mul_assoc, inv_mul_cancel₀ hsb,
      mul_one]
  have hx : ∀ z : hostE ζ a b, z ∈ ((𝔟 : Ideal (𝓞 (hostE ζ a b))) :
        FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b))⁻¹ ↔
      ∀ w ∈ (((σ • 𝔟 : Ideal (𝓞 (hostE ζ a b))) :
        FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)))⁻¹,
        Algebra.trace (KinE ζ a b) (hostE ζ a b) (z * w) ∈
          (algebraMap (𝓞 (KinE ζ a b)) (KinE ζ a b)).range := by
    intro z
    rw [← hJ, FractionalIdeal.mem_dual (inv_ne_zero hsb)]
    simp only [Algebra.traceForm_apply]
  rw [hx x]
  constructor
  · intro hw y hy
    exact hw _ ((mem_inv_smul σ 𝔟 hb0 y).mpr hy)
  · intro hy w hw
    have hw' : σ (σ.symm w) ∈ (((σ • 𝔟 : Ideal (𝓞 (hostE ζ a b))) :
        FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)))⁻¹ := by
      rw [AlgEquiv.apply_symm_apply]; exact hw
    have := hy (σ.symm w) ((mem_inv_smul σ 𝔟 hb0 _).mp hw')
    rwa [AlgEquiv.apply_symm_apply] at this

end Formalism.FrobeniusOrbits
