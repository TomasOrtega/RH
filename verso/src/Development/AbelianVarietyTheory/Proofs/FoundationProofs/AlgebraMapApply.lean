import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitaryClassRepTrivialAtCm
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.ClassSet
import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic

open NumberField IsDedekindDomain Formalism.UG Formalism.UG.P
open scoped TensorProduct Matrix

namespace GlobalTheory.LocDict

section Adele

variable {F : Type} [Field F] [NumberField F]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem algebraMap_apply' (a : 𝓞 F) (w : HeightOneSpectrum (𝓞 F)) :
    algebraMap (𝓞 F) 𝔸 a w = algebraMap (𝓞 F) (w.adicCompletion F) a := rfl

/- English proof (translation)
Establish `hval : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) a) = 1`. Rewrite using `[csApprox_val_int]`. Conclude with `HeightOneSpectrum.intValuation_eq_one_iff.2 ha`. Establish `hne : algebraMap (𝓞 F) (v.adicCompletion F) a ≠ 0`. Introduce `h`.

Rewrite `hval` using `[h, map_zero]`. Conclude with `zero_ne_one hval`. Establish `heval` using `afsplitI_eval v (algebraMap (𝓞 F) 𝔸 a)`. Rewrite `heval` using `[GlobalTheory.LocDict.algebraMap_apply']`. Use `⟨afsplitI v (algebraMap (𝓞 F) (v.adicCompletion F) a)⁻¹, afsplitI_mem_intAd v _ ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hval, inv_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, ← afsplitI_mul, mul_one]`. Use `_ = afsplitI v 1 := by rw [← heval, ← afsplitI_mul, inv_mul_cancel₀ hne]`.
-/
theorem exists_inv (v : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F) (ha : a ∉ v.asIdeal) :
    ∃ u ∈ intAd F, u * algebraMap (𝓞 F) 𝔸 a = afsplitI v 1 := by
  have hval : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) a) = 1 := by
    rw [csApprox_val_int]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 ha
  have hne : algebraMap (𝓞 F) (v.adicCompletion F) a ≠ 0 := by
    intro h
    rw [h, map_zero] at hval
    exact zero_ne_one hval
  have heval := afsplitI_eval v (algebraMap (𝓞 F) 𝔸 a)
  rw [GlobalTheory.LocDict.algebraMap_apply'] at heval
  refine ⟨afsplitI v (algebraMap (𝓞 F) (v.adicCompletion F) a)⁻¹, afsplitI_mem_intAd v _ ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hval, inv_one]
  · calc afsplitI v (algebraMap (𝓞 F) (v.adicCompletion F) a)⁻¹ * algebraMap (𝓞 F) 𝔸 a
        = afsplitI v (algebraMap (𝓞 F) (v.adicCompletion F) a)⁻¹ *
            (afsplitI v 1 * algebraMap (𝓞 F) 𝔸 a) := by
          rw [← mul_assoc, ← afsplitI_mul, mul_one]
      _ = afsplitI v 1 := by rw [← heval, ← afsplitI_mul, inv_mul_cancel₀ hne]

/- English proof (translation)
Take `⟨k, hk0⟩ : ∃ k : ℕ, v.intValuation d = WithZero.exp (-(k : ℤ))` from `⟨_, v.intValuation_if_neg hd⟩`. Establish `hk : v.asIdeal ^ k ∣ Ideal.span {d}`. Rewrite using `[← HeightOneSpectrum.intValuation_le_pow_iff_dvd, hk0]`. Establish `hk1 : ¬ v.asIdeal ^ (k + 1) ∣ Ideal.span {d}`. Rewrite using `[← HeightOneSpectrum.intValuation_le_pow_iff_dvd, hk0, WithZero.exp_le_exp]`.

Use `push_cast`. Use linear arithmetic over natural numbers and integers. Take `⟨J, hJ⟩` from `hk`. Establish `hJP : ¬ J ≤ v.asIdeal`. Introduce `hle`.

Apply `hk1` to reduce the goal to its premises. Rewrite using `[hJ, pow_succ]`. Conclude with `mul_dvd_mul_left _ (Ideal.dvd_iff_le.2 hle)`. Take `⟨t, htJ, htP⟩` from `SetLike.not_le_iff_exists.1 hJP`. Establish `hb : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → ∃ b ∈ v.asIdeal ^ k, b ∉ w.asIdeal`.

Introduce `w hw`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `hle : v.asIdeal ≤ w.asIdeal` using `Ideal.IsPrime.le_of_pow_le (fun b hb' => h b hb')`. Conclude with `hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hle).symm)`.

Establish `hval : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → w.intValuation t ≤ w.intValuation d`. Introduce `w hw`. Take `⟨b, hbk, hbw⟩` from `hb w hw`. Establish `hmem : t * b ∈ Ideal.span {d}`. Rewrite using `[hJ, mul_comm t b]`.

Conclude with `Ideal.mul_mem_mul hbk htJ`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 hmem`. Establish `h1 : w.intValuation b = 1` using `HeightOneSpectrum.intValuation_eq_one_iff.2 hbw`. Combine the equalities or inequalities in the displayed calculation. Establish `hdF : algebraMap (𝓞 F) F d ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hd`.

Use `⟨t, htP, algebraMap F 𝔸 (algebraMap (𝓞 F) F t / algebraMap (𝓞 F) F d) * (1 - afsplitI v 1), ?_, ?_⟩` and prove the remaining obligations. Use `show ∀ w, _`. Introduce `w`. Rewrite using `[afsplit_mul_apply, afsplit_sub_apply, afsplit_one_apply]`. Distinguish the cases in `hw : w = v`.

Substitute `hw` using the available equality. Rewrite using `[afsplitI_self, sub_self, mul_zero]`. Conclude with `zero_mem _`. Rewrite using `[afsplitI_ne v w hw, sub_zero, mul_one, HeightOneSpectrum.mem_adicCompletionIntegers]`. Establish `hc : ∀ c : F, (algebraMap F 𝔸 c) w = algebraMap F (w.adicCompletion F) c` using `fun c => rfl`.

Rewrite using `[hc, levelaf_valued_algebraMap, map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, div_le_one₀ (zero_lt_iff.2 (w.intValuation_ne_zero d hd))]`. Conclude with `hval w hw`. Rewrite using `[IsScalarTower.algebraMap_apply (𝓞 F) F 𝔸 t, IsScalarTower.algebraMap_apply (𝓞 F) F 𝔸 d]`. Establish `hq : algebraMap F 𝔸 (algebraMap (𝓞 F) F t / algebraMap (𝓞 F) F d) * algebraMap F 𝔸 (algebraMap (𝓞 F) F d) = algebraMap F 𝔸 (algebraMap (𝓞 F) F t)`. Rewrite using `[← map_mul, div_mul_cancel₀ _ hdF]`.

Take the linear combination `(-(1 - afsplitI v 1)) * hq`.
-/
theorem exists_approx (v : HeightOneSpectrum (𝓞 F)) (d : 𝓞 F) (hd : d ≠ 0) :
    ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ ∃ y ∈ intAd F,
      algebraMap (𝓞 F) 𝔸 t = algebraMap (𝓞 F) 𝔸 t * afsplitI v 1 + y * algebraMap (𝓞 F) 𝔸 d := by
  classical
  obtain ⟨k, hk0⟩ : ∃ k : ℕ, v.intValuation d = WithZero.exp (-(k : ℤ)) :=
    ⟨_, v.intValuation_if_neg hd⟩
  have hk : v.asIdeal ^ k ∣ Ideal.span {d} := by
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_dvd, hk0]
  have hk1 : ¬ v.asIdeal ^ (k + 1) ∣ Ideal.span {d} := by
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_dvd, hk0, WithZero.exp_le_exp]
    push_cast
    omega
  obtain ⟨J, hJ⟩ := hk
  have hJP : ¬ J ≤ v.asIdeal := by
    intro hle
    apply hk1
    rw [hJ, pow_succ]
    exact mul_dvd_mul_left _ (Ideal.dvd_iff_le.2 hle)
  obtain ⟨t, htJ, htP⟩ := SetLike.not_le_iff_exists.1 hJP
  have hb : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → ∃ b ∈ v.asIdeal ^ k, b ∉ w.asIdeal := by
    intro w hw
    by_contra h
    push_neg at h
    have hle : v.asIdeal ≤ w.asIdeal := Ideal.IsPrime.le_of_pow_le (fun b hb' => h b hb')
    exact hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hle).symm)
  have hval : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → w.intValuation t ≤ w.intValuation d := by
    intro w hw
    obtain ⟨b, hbk, hbw⟩ := hb w hw
    have hmem : t * b ∈ Ideal.span {d} := by
      rw [hJ, mul_comm t b]
      exact Ideal.mul_mem_mul hbk htJ
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
    have h1 : w.intValuation b = 1 := HeightOneSpectrum.intValuation_eq_one_iff.2 hbw
    calc w.intValuation t = w.intValuation (t * b) := by rw [map_mul, h1, mul_one]
      _ = w.intValuation c * w.intValuation d := by rw [← hc, map_mul]
      _ ≤ 1 * w.intValuation d := by gcongr; exact w.intValuation_le_one c
      _ = w.intValuation d := one_mul _
  have hdF : algebraMap (𝓞 F) F d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hd
  refine ⟨t, htP, algebraMap F 𝔸 (algebraMap (𝓞 F) F t / algebraMap (𝓞 F) F d) * (1 - afsplitI v 1),
    ?_, ?_⟩
  · show ∀ w, _
    intro w
    rw [afsplit_mul_apply, afsplit_sub_apply, afsplit_one_apply]
    by_cases hw : w = v
    · subst hw
      rw [afsplitI_self, sub_self, mul_zero]
      exact zero_mem _
    · rw [afsplitI_ne v w hw, sub_zero, mul_one, HeightOneSpectrum.mem_adicCompletionIntegers]
      have hc : ∀ c : F, (algebraMap F 𝔸 c) w = algebraMap F (w.adicCompletion F) c := fun c => rfl
      rw [hc, levelaf_valued_algebraMap, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.valuation_of_algebraMap,
        div_le_one₀ (zero_lt_iff.2 (w.intValuation_ne_zero d hd))]
      exact hval w hw
  · rw [IsScalarTower.algebraMap_apply (𝓞 F) F 𝔸 t, IsScalarTower.algebraMap_apply (𝓞 F) F 𝔸 d]
    have hq : algebraMap F 𝔸 (algebraMap (𝓞 F) F t / algebraMap (𝓞 F) F d) *
        algebraMap F 𝔸 (algebraMap (𝓞 F) F d) = algebraMap F 𝔸 (algebraMap (𝓞 F) F t) := by
      rw [← map_mul, div_mul_cancel₀ _ hdF]
    linear_combination (-(1 - afsplitI v 1)) * hq

end Adele

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem eps_eq (v : HeightOneSpectrum (𝓞 F)) :
    afsplitEps E v = (1 : E) ⊗ₜ[F] afsplitI v 1 := rfl

/- English proof (translation)
Establish `h` using `levelaf_tmul_mem (F := F) (E := E) 1 hy`. Rewrite `h` using `[map_one]`. Then use the resulting hypothesis.
-/
theorem one_tmul_mem {y : 𝔸} (hy : y ∈ intAd F) : (1 : E) ⊗ₜ[F] y ∈ 𝒮 := by
  have h := levelaf_tmul_mem (F := F) (E := E) 1 hy
  rwa [map_one] at h

/- English proof (translation)
Take `⟨m, hm, hsingle⟩` from `csGlob_single Λ hspan`. Take `⟨m', hm', hint⟩` from `adelstabL_den x`. Use `⟨m * m', mul_ne_zero hm hm', ?_⟩` and prove the remaining obligations. Establish `hmk : ∀ (a : E) (h : IsIntegral ℤ a), algebraMap (𝓞 E) E ⟨a, h⟩ = a` using `fun _ _ => rfl`. Establish `key : ((m * m' : ℤ) : 𝓞 E) • x = ∑ k : Fin n, (⟨(m' : E) * x k, hint k⟩ : 𝓞 E) • (Pi.single k (m : E) : Fin n → E)`.

Use function extensionality and compare the values at `i`. Rewrite using `[Finset.sum_apply, Pi.smul_apply]`. Simplify using `only [Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Simplify using `only [Algebra.smul_def, map_intCast, hmk]`. Use `push_cast`.

Use `show (m : E) * (m' : E) * x i = ((m' : E) * x i) * (m : E)`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hsingle k)`.
-/
theorem exists_den {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hspan : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ d : ℤ, d ≠ 0 ∧ (d : 𝓞 E) • x ∈ Λ := by
  obtain ⟨m, hm, hsingle⟩ := csGlob_single Λ hspan
  obtain ⟨m', hm', hint⟩ := adelstabL_den x
  refine ⟨m * m', mul_ne_zero hm hm', ?_⟩
  have hmk : ∀ (a : E) (h : IsIntegral ℤ a), algebraMap (𝓞 E) E ⟨a, h⟩ = a := fun _ _ => rfl
  have key : ((m * m' : ℤ) : 𝓞 E) • x =
      ∑ k : Fin n, (⟨(m' : E) * x k, hint k⟩ : 𝓞 E) • (Pi.single k (m : E) : Fin n → E) := by
    funext i
    rw [Finset.sum_apply, Pi.smul_apply]
    simp only [Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [Algebra.smul_def, map_intCast, hmk]
    push_cast
    show (m : E) * (m' : E) * x i = ((m' : E) * x i) * (m : E)
    ring
  rw [key]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hsingle k)

/- English proof (translation)
Use `set s' := algebraMap (𝓞 E) E s with hs'`. Establish `hsint : IsIntegral ℤ s'` using `RingOfIntegers.isIntegral_coe s`. Establish `hσint : IsIntegral ℤ ((σ : E →+* E) s')` using `hsint.map (σ : E →+* E).toIntAlgHom`. Take `⟨sb, hsb⟩ : ∃ sb : 𝓞 E, algebraMap (𝓞 E) E sb = (σ : E →+* E) s'` from `⟨⟨_, hσint⟩, rfl⟩`. Establish `hsbp : sb ∉ p` using `h2 sb hsb`.

Establish `hfixN : σ ((σ : E →+* E) s' * s') = (σ : E →+* E) s' * s'` using `by show (σ : E →+* E) ((σ : E →+* E) s' * s') = (σ : E →+* E) s' * s'`. Rewrite using `[map_mul, hs, mul_comm]`. Take `⟨a, ha⟩` from `hfix _ hfixN`. Establish `haint : IsIntegral ℤ a`. Rewrite using `[← isIntegral_algHom_iff (algebraMap F E).toIntAlgHom (algebraMap F E).injective]`.

Use `show IsIntegral ℤ (algebraMap F E a)`. Rewrite using `[ha]`. Conclude with `hσint.mul hsint`. Take `⟨aO, haO'⟩ : ∃ aO : 𝓞 F, algebraMap (𝓞 F) F aO = a` from `⟨⟨a, haint⟩, rfl⟩`. Establish `haO : algebraMap (𝓞 F) E aO = (σ : E →+* E) s' * s'`.

Rewrite using `[IsScalarTower.algebraMap_apply (𝓞 F) F E, haO', ha]`. Establish `haOv : aO ∉ v.asIdeal`. Rewrite using `[← hpv, Ideal.mem_comap]`. Introduce `hmem`. Establish `heq : algebraMap (𝓞 F) (𝓞 E) aO = sb * s`.

Apply `IsFractionRing.injective (𝓞 E) E` to reduce the goal to its premises. Rewrite using `[← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, haO, map_mul, hsb]`. Rewrite `hmem` using `[heq]`. Break down `hp.mem_or_mem hmem with h | h` into its components or cases. Conclude with `hsbp h`.

Conclude with `h1 h`. Take `⟨u0, hu0, hu0e⟩` from `GlobalTheory.LocDict.exists_inv v aO haOv`. Establish `key : (1 : E) ⊗ₜ[F] (u0 * algebraMap (𝓞 F) 𝔸 aO) = ((1 : E) ⊗ₜ[F] u0) * ι (algebraMap (𝓞 F) E aO)`. Rewrite using `[← mul_one (algebraMap (𝓞 F) E aO), ← csGlob_tmul_int, Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Use `⟨ι ((σ : E →+* E) s') * ((1 : E) ⊗ₜ[F] u0), mul_mem ?_ (GlobalTheory.LocDict.one_tmul_mem hu0), ?_⟩` and prove the remaining obligations.

Rewrite using `[← hsb]`. Conclude with `adelstab_incl_int sb`. Rewrite using `[GlobalTheory.LocDict.eps_eq, ← hu0e, key, haO, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_inv_gen (σ : E →ₐ[F] E) (hs : ∀ e, (σ : E →+* E) ((σ : E →+* E) e) = e)
    (hfix : ∀ e : E, σ e = e → ∃ a : F, algebraMap F E a = e)
    (v : HeightOneSpectrum (𝓞 F)) (p : Ideal (𝓞 E)) (hp : p.IsPrime)
    (hpv : p.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal) (s : 𝓞 E) (h1 : s ∉ p)
    (h2 : ∀ t : 𝓞 E, algebraMap (𝓞 E) E t = (σ : E →+* E) (algebraMap (𝓞 E) E s) → t ∉ p) :
    ∃ u ∈ 𝒮, u * ι (algebraMap (𝓞 E) E s) = afsplitEps E v := by
  set s' := algebraMap (𝓞 E) E s with hs'
  have hsint : IsIntegral ℤ s' := RingOfIntegers.isIntegral_coe s
  have hσint : IsIntegral ℤ ((σ : E →+* E) s') := hsint.map (σ : E →+* E).toIntAlgHom
  obtain ⟨sb, hsb⟩ : ∃ sb : 𝓞 E, algebraMap (𝓞 E) E sb = (σ : E →+* E) s' := ⟨⟨_, hσint⟩, rfl⟩
  have hsbp : sb ∉ p := h2 sb hsb
  have hfixN : σ ((σ : E →+* E) s' * s') = (σ : E →+* E) s' * s' := by
    show (σ : E →+* E) ((σ : E →+* E) s' * s') = (σ : E →+* E) s' * s'
    rw [map_mul, hs, mul_comm]
  obtain ⟨a, ha⟩ := hfix _ hfixN
  have haint : IsIntegral ℤ a := by
    rw [← isIntegral_algHom_iff (algebraMap F E).toIntAlgHom (algebraMap F E).injective]
    show IsIntegral ℤ (algebraMap F E a)
    rw [ha]
    exact hσint.mul hsint
  obtain ⟨aO, haO'⟩ : ∃ aO : 𝓞 F, algebraMap (𝓞 F) F aO = a := ⟨⟨a, haint⟩, rfl⟩
  have haO : algebraMap (𝓞 F) E aO = (σ : E →+* E) s' * s' := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F E, haO', ha]
  have haOv : aO ∉ v.asIdeal := by
    rw [← hpv, Ideal.mem_comap]
    intro hmem
    have heq : algebraMap (𝓞 F) (𝓞 E) aO = sb * s := by
      apply IsFractionRing.injective (𝓞 E) E
      rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, haO, map_mul, hsb]
    rw [heq] at hmem
    rcases hp.mem_or_mem hmem with h | h
    · exact hsbp h
    · exact h1 h
  obtain ⟨u0, hu0, hu0e⟩ := GlobalTheory.LocDict.exists_inv v aO haOv
  have key : (1 : E) ⊗ₜ[F] (u0 * algebraMap (𝓞 F) 𝔸 aO) =
      ((1 : E) ⊗ₜ[F] u0) * ι (algebraMap (𝓞 F) E aO) := by
    rw [← mul_one (algebraMap (𝓞 F) E aO), ← csGlob_tmul_int, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul]
  refine ⟨ι ((σ : E →+* E) s') * ((1 : E) ⊗ₜ[F] u0), mul_mem ?_ (GlobalTheory.LocDict.one_tmul_mem hu0), ?_⟩
  · rw [← hsb]
    exact adelstab_incl_int sb
  · rw [GlobalTheory.LocDict.eps_eq, ← hu0e, key, haO, map_mul]
    ring

/- English proof (translation)
Rewrite using `[GlobalTheory.LocDict.eps_eq]`. Conclude with `GlobalTheory.LocDict.one_tmul_mem (afsplitI_mem_intAd v 1 (one_mem _))`.
-/
private theorem eps_mem_intAd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) :
    afsplitEps E v ∈ tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F) := by
  rw [GlobalTheory.LocDict.eps_eq]
  exact GlobalTheory.LocDict.one_tmul_mem (afsplitI_mem_intAd v 1 (one_mem _))

/- English proof (translation)
Rewrite using `[← csGlob_tmul_int]`. Use `show z ⊗ₜ[F] _ = _ * (z ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F))`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]`.
-/
private theorem inclE_tmul' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (ρ : 𝓞 F) (z : E) :
    inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) E ρ * z) =
      ((1 : E) ⊗ₜ[F] algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) ρ) *
        inclE (F := F) (FiniteAdeleRing (𝓞 F) F) z := by
  rw [← csGlob_tmul_int]
  show z ⊗ₜ[F] _ = _ * (z ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F))
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

/- English proof (translation)
Rewrite using `[inclE_tmul', inclE_tmul', GlobalTheory.LocDict.eps_eq]`. Establish `h1 : (1 : E) ⊗ₜ[F] (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) t * afsplitI v 1) = ((1 : E) ⊗ₜ[F] algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) t) * ((1 : E) ⊗ₜ[F] afsplitI v 1)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Establish `h2 : (1 : E) ⊗ₜ[F] (y * algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) d) = ((1 : E) ⊗ₜ[F] y) * ((1 : E) ⊗ₜ[F] algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) d)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul]`.

Use `conv_lhs => rw [hty]`. Rewrite using `[TensorProduct.tmul_add, h1, h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem split_lemma_3 {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (t d : 𝓞 F) (y : FiniteAdeleRing (𝓞 F) F)
    (hty : algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) t =
      algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) t * afsplitI v 1 +
        y * algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) d) (z : E) :
    inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) E t * z) =
      ((1 : E) ⊗ₜ[F] algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) t) *
          (afsplitEps E v * inclE (F := F) (FiniteAdeleRing (𝓞 F) F) z) +
        ((1 : E) ⊗ₜ[F] y) *
          inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) E d * z) := by
  rw [inclE_tmul', inclE_tmul', GlobalTheory.LocDict.eps_eq]
  have h1 : (1 : E) ⊗ₜ[F] (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) t * afsplitI v 1) =
      ((1 : E) ⊗ₜ[F] algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) t) * ((1 : E) ⊗ₜ[F] afsplitI v 1) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have h2 : (1 : E) ⊗ₜ[F] (y * algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) d) =
      ((1 : E) ⊗ₜ[F] y) * ((1 : E) ⊗ₜ[F] algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) d) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  conv_lhs => rw [hty]
  rw [TensorProduct.tmul_add, h1, h2]
  ring

end Main

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hs hfix n Λ hfin hspan v p hp hpv x`. Use `letI := Formalism.UG.CS.starOfInv (σ : E →+* E) hs`. Use `show x ∈ Formalism.HermitianLatticesTheory.locS (Formalism.HermitianLatticesTheory.hcompl (K := E) p) Λ ↔ _`. Rewrite using `[Formalism.HermitianLatticesTheory.locBasic_mem_locS]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨s, hsS, hsx⟩`. Establish `hgood : ∀ s₁ ∈ Formalism.HermitianLatticesTheory.hcompl (K` using `E) p, ∃ u ∈ tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F), u * inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E s₁) = afsplitEps E v := by`. Introduce `s₁ hs₁`. Express the relevant statement in the definitionally equal form `s₁ ∈ Submonoid.closure _ at hs₁`. Proceed by induction on `hs₁ using Submonoid.closure_induction with`.

Consider the case `mem s₀ hs₀ => exact GlobalTheory.LocDict.exists_inv_gen σ hs hfix v p hp hpv s₀ hs₀.1 hs₀.2`. Consider the case `one => exact ⟨afsplitEps E v, eps_mem_intAd v, by rw [map_one, map_one, mul_one]⟩`. Consider the case `mul a b _ _ ha hb`. Take `⟨u₁, hu₁, e₁⟩` from `ha`. Take `⟨u₂, hu₂, e₂⟩` from `hb`.

Use `⟨u₁ * u₂, mul_mem hu₁ hu₂, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, mul_mul_mul_comm, e₁, e₂, afsplit_eps_idem]`. Take `⟨u, hu, hue⟩` from `hgood s hsS`. Establish `heq : (afsplitEps E v • fun i => inclE (F` using `F) (FiniteAdeleRing (𝓞 F) F) (x i)) = (⟨u, hu⟩ : tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) • fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((s • x) i) := by`. Use function extensionality and compare the values at `i`.

Use `show afsplitEps E v * inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i) = u * inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E s * x i)`. Rewrite using `[map_mul, ← hue]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[heq]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨s • x, hsx, rfl⟩)`.

Introduce `h`. Take `⟨dz, hdz, hdx⟩` from `GlobalTheory.LocDict.exists_den Λ hspan x`. Establish `hd0 : (dz : 𝓞 F) ≠ 0` using `Int.cast_ne_zero.2 hdz`. Take `⟨t, htv, y, hy, hty⟩` from `GlobalTheory.LocDict.exists_approx v (dz : 𝓞 F) hd0`. Establish `hmem : (fun i => inclE (F` using `F) (FiniteAdeleRing (𝓞 F) F) ((algebraMap (𝓞 F) (𝓞 E) t • x) i)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ := by`.

Establish `heq : (fun i => inclE (F` using `F) (FiniteAdeleRing (𝓞 F) F) ((algebraMap (𝓞 F) (𝓞 E) t • x) i)) = (⟨_, GlobalTheory.LocDict.one_tmul_mem (levelaf_int_mem t)⟩ : tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) • (afsplitEps E v • fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) + (⟨_, Glo …`. Use function extensionality and compare the values at `i`. Establish `hx1 : algebraMap (𝓞 F) (𝓞 E) t • x i = algebraMap (𝓞 F) E t * x i`. Rewrite using `[Algebra.smul_def, ← IsScalarTower.algebraMap_apply]`. Establish `hx2 : (dz : 𝓞 E) • x i = algebraMap (𝓞 F) E (dz : 𝓞 F) * x i`.

Rewrite using `[Algebra.smul_def, map_intCast, map_intCast]`. Use `show inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) (𝓞 E) t • x i) = ((1 : E) ⊗ₜ[F] algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) t) * (afsplitEps E v * inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) + ((1 : E) ⊗ₜ[F] y) * inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((dz : …`. Rewrite using `[hx1, hx2]`. Conclude with `split_lemma_3 v t (dz : 𝓞 F) y hty (x i)`. Rewrite using `[heq]`.

Conclude with `add_mem (Submodule.smul_mem _ _ h) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hdx, rfl⟩))`. Establish `hx' : algebraMap (𝓞 F) (𝓞 E) t • x ∈ Λ`. Rewrite using `[← csGlob_one (F := F) integral_adele_approximation_holds Λ hfin hspan, csGlob_eq, adelstab_mem_iff]`. Simplify using `using hmem`. Establish `hnot : algebraMap (𝓞 F) (𝓞 E) t ∉ p`.

Introduce `hm`. Apply `htv` to reduce the goal to its premises. Rewrite using `[← hpv]`. Conclude with `hm`. Use `⟨algebraMap (𝓞 F) (𝓞 E) t, Submonoid.subset_closure ⟨hnot, ?_⟩, hx'⟩` and prove the remaining obligations.

Introduce `t' ht'`. Establish `ht'' : t' = algebraMap (𝓞 F) (𝓞 E) t`. Apply `IsFractionRing.injective (𝓞 E) E` to reduce the goal to its premises. Rewrite using `[ht']`. Use `show (σ : E →+* E) (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) t)) = _`.

Rewrite using `[← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E]`. Simplify using the standard rewrite rules. Rewrite using `[ht'']`. Conclude with `hnot`.
-/
theorem mem_loc_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hs : ∀ e, (σ : E →+* E) ((σ : E →+* E) e) = e), (∀ e : E, σ e = e → ∃ a : F, algebraMap F E a = e) → ∀ (n : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)), Module.Finite (𝓞 E) Λ → Submodule.span E (Λ : Set (Fin n → E)) = ⊤ → ∀ (v : HeightOneSpectrum (𝓞 F)) (p : Ideal (𝓞 E)), p.IsPrime → p.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal → ∀ x : Fin n → E, (letI := Formalism.UG.CS.starOfInv (σ : E →+* E) hs; x ∈ Formalism.HermitianLatticesTheory.loc (K := E) p Λ) ↔ (afsplitEps E v • fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ := by
  intro F E _ _ _ _ _ σ hs hfix n Λ hfin hspan v p hp hpv x
  letI := Formalism.UG.CS.starOfInv (σ : E →+* E) hs
  show x ∈ Formalism.HermitianLatticesTheory.locS (Formalism.HermitianLatticesTheory.hcompl (K := E) p) Λ ↔ _
  rw [Formalism.HermitianLatticesTheory.locBasic_mem_locS]
  constructor
  · rintro ⟨s, hsS, hsx⟩
    have hgood : ∀ s₁ ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) p,
        ∃ u ∈ tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F),
        u * inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E s₁) = afsplitEps E v := by
      intro s₁ hs₁
      change s₁ ∈ Submonoid.closure _ at hs₁
      induction hs₁ using Submonoid.closure_induction with
      | mem s₀ hs₀ => exact GlobalTheory.LocDict.exists_inv_gen σ hs hfix v p hp hpv s₀ hs₀.1 hs₀.2
      | one => exact ⟨afsplitEps E v, eps_mem_intAd v, by rw [map_one, map_one, mul_one]⟩
      | mul a b _ _ ha hb =>
        obtain ⟨u₁, hu₁, e₁⟩ := ha
        obtain ⟨u₂, hu₂, e₂⟩ := hb
        refine ⟨u₁ * u₂, mul_mem hu₁ hu₂, ?_⟩
        rw [map_mul, map_mul, mul_mul_mul_comm, e₁, e₂, afsplit_eps_idem]
    obtain ⟨u, hu, hue⟩ := hgood s hsS
    have heq : (afsplitEps E v • fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) =
        (⟨u, hu⟩ : tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) •
          fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((s • x) i) := by
      funext i
      show afsplitEps E v * inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i) =
        u * inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E s * x i)
      rw [map_mul, ← hue]
      ring
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s • x, hsx, rfl⟩)
  · intro h
    obtain ⟨dz, hdz, hdx⟩ := GlobalTheory.LocDict.exists_den Λ hspan x
    have hd0 : (dz : 𝓞 F) ≠ 0 := Int.cast_ne_zero.2 hdz
    obtain ⟨t, htv, y, hy, hty⟩ := GlobalTheory.LocDict.exists_approx v (dz : 𝓞 F) hd0
    have hmem : (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F)
        ((algebraMap (𝓞 F) (𝓞 E) t • x) i)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
          (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ := by
      have heq : (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F)
          ((algebraMap (𝓞 F) (𝓞 E) t • x) i)) =
          (⟨_, GlobalTheory.LocDict.one_tmul_mem (levelaf_int_mem t)⟩ :
              tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) •
            (afsplitEps E v • fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) +
          (⟨_, GlobalTheory.LocDict.one_tmul_mem hy⟩ :
              tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) •
            (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (((dz : 𝓞 E) • x) i)) := by
        funext i
        have hx1 : algebraMap (𝓞 F) (𝓞 E) t • x i = algebraMap (𝓞 F) E t * x i := by
          rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
        have hx2 : (dz : 𝓞 E) • x i = algebraMap (𝓞 F) E (dz : 𝓞 F) * x i := by
          rw [Algebra.smul_def, map_intCast, map_intCast]
        show inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) (𝓞 E) t • x i) =
          ((1 : E) ⊗ₜ[F] algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) t) *
              (afsplitEps E v * inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) +
            ((1 : E) ⊗ₜ[F] y) * inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((dz : 𝓞 E) • x i)
        rw [hx1, hx2]
        exact split_lemma_3 v t (dz : 𝓞 F) y hty (x i)
      rw [heq]
      exact add_mem (Submodule.smul_mem _ _ h)
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hdx, rfl⟩))
    have hx' : algebraMap (𝓞 F) (𝓞 E) t • x ∈ Λ := by
      rw [← csGlob_one (F := F) integral_adele_approximation_holds Λ hfin hspan, csGlob_eq, adelstab_mem_iff]
      simpa using hmem
    have hnot : algebraMap (𝓞 F) (𝓞 E) t ∉ p := by
      intro hm
      apply htv
      rw [← hpv]
      exact hm
    refine ⟨algebraMap (𝓞 F) (𝓞 E) t, Submonoid.subset_closure ⟨hnot, ?_⟩, hx'⟩
    intro t' ht'
    have ht'' : t' = algebraMap (𝓞 F) (𝓞 E) t := by
      apply IsFractionRing.injective (𝓞 E) E
      rw [ht']
      show (σ : E →+* E) (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) t)) = _
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E]
      simp
    rw [ht'']
    exact hnot

end GlobalTheory.LocDict
