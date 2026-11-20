import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsLocalCoeffRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

/- English proof (translation)
Rewrite using `[Module.length_eq_coheight, Module.length_eq_coheight]`. Use `Ideal.coheight_comap_of_surjective (e : S →+* T) e.surjective ⊥` as an intermediate fact. Establish `hb : Ideal.comap (e : S →+* T) ⊥ = ⊥` using `Ideal.comap_bot_of_injective _ e.injective`. Rewrite `this` using `[hb]`. Conclude with `this`.
-/
private theorem length_self_eq_of_ringEquiv {S T : Type*} [CommRing S] [CommRing T] (e : S ≃+* T) :
    Module.length S S = Module.length T T := by
  rw [Module.length_eq_coheight, Module.length_eq_coheight]
  have := Ideal.coheight_comap_of_surjective (e : S →+* T) e.surjective ⊥
  have hb : Ideal.comap (e : S →+* T) ⊥ = ⊥ := Ideal.comap_bot_of_injective _ e.injective
  rw [hb] at this
  exact this

/- English proof (translation)
Set `S` to `Localization.AtPrime W`. Establish `hJ : (J : Submodule R R).localized' S W.primeCompl (Algebra.linearMap R S) = J.map (algebraMap R S)`. Rewrite using `[Submodule.localized'_eq_span, Ideal.map]`. Both sides reduce to the same expression. Set `e` to `(IsLocalizedModule.linearEquiv W.primeCompl ((J : Submodule R R).toLocalizedQuotient' S W.primeCompl (Algebra.linearMap R S)) (LocalizedModule.mkLinearMap W.primeCompl (R ⧸ J))).extendScalarsOfIsLocalization W.primeCompl S`.

Rewrite using `[← e.length_eq, (Submodule.quotEquivOfEq _ _ hJ).length_eq]`. Conclude with `Module.length_eq_of_surjective Ideal.Quotient.mk_surjective`.
-/
private theorem length_localizedModule_quot {R : Type*} [CommRing R] (J W : Ideal R) [W.IsPrime] :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J)) =
      Module.length (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))
        (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) := by
  let S := Localization.AtPrime W
  have hJ : (J : Submodule R R).localized' S W.primeCompl (Algebra.linearMap R S) =
      J.map (algebraMap R S) := by
    rw [Submodule.localized'_eq_span, Ideal.map]
    rfl
  let e := (IsLocalizedModule.linearEquiv W.primeCompl
    ((J : Submodule R R).toLocalizedQuotient' S W.primeCompl (Algebra.linearMap R S))
    (LocalizedModule.mkLinearMap W.primeCompl (R ⧸ J))).extendScalarsOfIsLocalization W.primeCompl S
  rw [← e.length_eq, (Submodule.quotEquivOfEq _ _ hJ).length_eq]
  exact Module.length_eq_of_surjective Ideal.Quotient.mk_surjective

/- English proof (translation)
Introduce `R _ P U _ J W hPJ hW hPW hWU`. Take `⟨hup, hdown⟩` from `h₂ R P U (hPW.trans hWU)`. Take `⟨hpW, hcW⟩` from `hup W hW hPW hWU`. Establish `hmin : W ∈ J.minimalPrimes ↔ W.map (localQuotMap P U) ∈ (J.map (localQuotMap P U)).minimalPrimes`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨-, hJW⟩, hm⟩`. Use `⟨⟨hpW, Ideal.map_mono hJW⟩, fun q hq hqW => ?_⟩` and prove the remaining obligations. Use `hq.1` as an intermediate fact. Take `⟨hPq, hqU, hqe⟩` from `hdown q hq.1`. Establish `h` using `hm ⟨Ideal.comap_isPrime _ q, Ideal.le_comap_map.trans (Ideal.comap_mono hq.2)⟩ ((Ideal.comap_mono hqW).trans hcW.le)`.

Rewrite using `[← hqe]`. Conclude with `Ideal.map_mono h`. Introduce and unpack `⟨⟨-, hJW⟩, hm⟩`. Use `⟨⟨hW, Ideal.le_comap_map.trans ((Ideal.comap_mono hJW).trans hcW.le)⟩, fun Q hQ hQW => ?_⟩` and prove the remaining obligations. Take `⟨hQp, hQc⟩` from `hup Q hQ.1 (hPJ.trans hQ.2) (hQW.trans hWU)`.

Establish `h` using `hm ⟨hQp, Ideal.map_mono hQ.2⟩ (Ideal.map_mono hQW)`. Rewrite using `[← hcW, ← hQc]`. Conclude with `Ideal.comap_mono h`. Unfold `locCycle`. Distinguish the cases in `h : W ∈ J.minimalPrimes`.

Use `swap`. Rewrite using `[dif_neg h, dif_neg (mt hmin.2 h)]`. Rewrite using `[dif_pos h, dif_pos (hmin.1 h)]`. Use `hW` as an intermediate fact. Use `hpW` as an intermediate fact.

Use `set φ := localQuotMap P U with hφ`. Take `⟨p, hp⟩ : ∃ p, W.map φ = p` from `⟨_, rfl⟩`. Rewrite `hpW`, `hcW` using `[hp]`. Use `hpW` as an intermediate fact. Establish `hφp : ∀ x : R, φ x ∈ p ↔ x ∈ W` using `fun x => by rw [← Ideal.mem_comap, hcW]`.

Establish `hrep : ∀ a : localQuot P U, ∃ r u : R, u ∉ U ∧ a * φ u = φ r`. Introduce `a`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Take `⟨⟨r, u⟩, rfl⟩` from `IsLocalization.mk'_surjective U.primeCompl b`. Use `⟨r, u, u.2, ?_⟩` and prove the remaining obligations.

Simplify using `only [hφ, localQuotMap, RingHom.comp_apply, ← map_mul, IsLocalization.mk'_spec]`. Establish `hnum : ∀ (t : localQuot P U) (r' u' : R), t ∉ p → u' ∉ U → t * φ u' = φ r' → r' ∉ W`. Introduce `t r' u' ht hu' hr' hmem`. Rewrite `hmem` using `[← hφp, ← hr']`. Break down `hpW.mem_or_mem hmem with h | h` into its components or cases.

Conclude with `ht h`. Conclude with `hu' (hWU ((hφp u').1 h))`. Set `ψ : (Localization.AtPrime W) →+* (Localization.AtPrime p)` to `Localization.localRingHom W p φ hcW.symm`. Establish `hψ : Function.Surjective ψ`. Introduce `z`.

Take `⟨⟨a, t⟩, rfl⟩` from `IsLocalization.mk'_surjective p.primeCompl z`. Take `⟨r, u, hu, hr⟩` from `hrep a`. Take `⟨r', u', hu', hr'⟩` from `hrep t`. Establish `hs : r' * u ∈ W.primeCompl` using `W.primeCompl.mul_mem (hnum t r' u' t.2 hu' hr') fun h => hu (hWU h)`. Use `⟨IsLocalization.mk' _ (r * u') ⟨r' * u, hs⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[Localization.localRingHom_mk', IsLocalization.mk'_eq_iff_eq]`. Use `congr 1`. Simplify using `only [map_mul]`. Take the linear combination `(φ r) * hr' - (φ r') * hr`. Establish `hker : Ideal.comap ψ ⊥ ≤ J.map (algebraMap R (Localization.AtPrime W))`.

Introduce `x hx`. Rewrite `hx` using `[Ideal.mem_comap, Ideal.mem_bot]`. Take `⟨⟨r, s⟩, rfl⟩` from `IsLocalization.mk'_surjective W.primeCompl x`. Rewrite `hx` using `[Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff]`. Take `⟨⟨t, ht⟩, htr⟩` from `hx`.

Take `⟨r', u', hu', hr'⟩` from `hrep t`. Establish `hr'W` using `hnum t r' u' ht hu' hr'`. Establish `h0 : φ (r' * r) = 0`. Rewrite using `[map_mul, ← hr', mul_right_comm, htr, zero_mul]`. Rewrite `h0` using `[hφ, localQuotMap, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, IsLocalization.mem_map_algebraMap_iff U.primeCompl]`.

Take `⟨⟨⟨i, hi⟩, v⟩, hv⟩` from `h0`. Rewrite `hv` using `[← map_mul, IsLocalization.eq_iff_exists U.primeCompl]`. Take `⟨c, hc⟩` from `hv`. Establish `hcW : (c : R) * r' * v ∈ W.primeCompl` using `W.primeCompl.mul_mem (W.primeCompl.mul_mem (fun h => c.2 (hWU h)) hr'W) fun h => v.2 (hWU h)`. Establish `hmemP : (c : R) * r' * v * r ∈ P`.

Establish `: (c : R) * (r' * r * v) = c * r' * v * r` using `by ring`. Rewrite using `[← this, hc]`. Conclude with `P.mul_mem_left _ hi`. Establish `hrJ : algebraMap R (Localization.AtPrime W) r ∈ J.map (algebraMap R (Localization.AtPrime W))`. Rewrite using `[← Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units (Localization.AtPrime W) ⟨_, hcW⟩), ← map_mul]`.

Conclude with `Ideal.mem_map_of_mem _ (hPJ hmemP)`. Use `show IsLocalization.mk' (Localization.AtPrime W) r s ∈ _`. Rewrite using `[IsLocalization.mk'_eq_mul_mk'_one]`. Conclude with `Ideal.mul_mem_right _ _ hrJ`. Set `: CommRing (Localization.AtPrime p)` to `inferInstance`.

Establish `hcomp : ψ.comp (algebraMap R (Localization.AtPrime W)) = (algebraMap (localQuot P U) (Localization.AtPrime p)).comp φ` using `RingHom.ext fun x => Localization.localRingHom_to_map W p φ hcW.symm x`. Establish `hI : (J.map φ).map (algebraMap (localQuot P U) (Localization.AtPrime p)) = (J.map (algebraMap R (Localization.AtPrime W))).map ψ`. Rewrite using `[Ideal.map_map, Ideal.map_map, hcomp]`. Set `g` to `(Ideal.Quotient.mk ((J.map φ).map (algebraMap (localQuot P U) (Localization.AtPrime p)))).comp ψ`. Establish `hg : Function.Surjective g` using `Ideal.Quotient.mk_surjective.comp hψ`.

Establish `hgk : J.map (algebraMap R (Localization.AtPrime W)) = RingHom.ker g`. Rewrite using `[← RingHom.comap_ker, Ideal.mk_ker, hI, Ideal.comap_map_of_surjective _ hψ, sup_eq_left.mpr hker]`. Establish `key` using `length_self_eq_of_ringEquiv ((Ideal.quotEquivOfEq hgk).trans (RingHom.quotientKerEquivOfSurjective hg))`. Rewrite `key` using `[← length_localizedModule_quot, ← length_localizedModule_quot]`. Substitute `hp` using the available equality.

Conclude with `congrArg (fun n : ℕ∞ => ((n.toNat : ℕ) : ℤ)) key`.
-/
theorem LocCycleLocalQuot.proof (h₂ : LocalQuotPrimes.Statement.{u}) : LocCycleLocalQuot.Statement.{u} := by
  intro R _ P U _ J W hPJ hW hPW hWU
  obtain ⟨hup, hdown⟩ := h₂ R P U (hPW.trans hWU)
  obtain ⟨hpW, hcW⟩ := hup W hW hPW hWU

  have hmin : W ∈ J.minimalPrimes ↔ W.map (localQuotMap P U) ∈ (J.map (localQuotMap P U)).minimalPrimes := by
    constructor
    · rintro ⟨⟨-, hJW⟩, hm⟩
      refine ⟨⟨hpW, Ideal.map_mono hJW⟩, fun q hq hqW => ?_⟩
      have := hq.1
      obtain ⟨hPq, hqU, hqe⟩ := hdown q hq.1
      have h := hm ⟨Ideal.comap_isPrime _ q, Ideal.le_comap_map.trans (Ideal.comap_mono hq.2)⟩
        ((Ideal.comap_mono hqW).trans hcW.le)
      rw [← hqe]
      exact Ideal.map_mono h
    · rintro ⟨⟨-, hJW⟩, hm⟩
      refine ⟨⟨hW, Ideal.le_comap_map.trans ((Ideal.comap_mono hJW).trans hcW.le)⟩, fun Q hQ hQW => ?_⟩
      obtain ⟨hQp, hQc⟩ := hup Q hQ.1 (hPJ.trans hQ.2) (hQW.trans hWU)
      have h := hm ⟨hQp, Ideal.map_mono hQ.2⟩ (Ideal.map_mono hQW)
      rw [← hcW, ← hQc]
      exact Ideal.comap_mono h
  unfold locCycle
  by_cases h : W ∈ J.minimalPrimes
  swap
  · rw [dif_neg h, dif_neg (mt hmin.2 h)]
  rw [dif_pos h, dif_pos (hmin.1 h)]
  have := hW
  have := hpW
  set φ := localQuotMap P U with hφ
  obtain ⟨p, hp⟩ : ∃ p, W.map φ = p := ⟨_, rfl⟩
  rw [hp] at hpW hcW
  have := hpW
  have hφp : ∀ x : R, φ x ∈ p ↔ x ∈ W := fun x => by rw [← Ideal.mem_comap, hcW]

  have hrep : ∀ a : localQuot P U, ∃ r u : R, u ∉ U ∧ a * φ u = φ r := by
    intro a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨⟨r, u⟩, rfl⟩ := IsLocalization.mk'_surjective U.primeCompl b
    refine ⟨r, u, u.2, ?_⟩
    simp only [hφ, localQuotMap, RingHom.comp_apply, ← map_mul, IsLocalization.mk'_spec]
  have hnum : ∀ (t : localQuot P U) (r' u' : R), t ∉ p → u' ∉ U → t * φ u' = φ r' → r' ∉ W := by
    intro t r' u' ht hu' hr' hmem
    rw [← hφp, ← hr'] at hmem
    rcases hpW.mem_or_mem hmem with h | h
    · exact ht h
    · exact hu' (hWU ((hφp u').1 h))
  let ψ : (Localization.AtPrime W) →+* (Localization.AtPrime p) := Localization.localRingHom W p φ hcW.symm
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
    obtain ⟨r, u, hu, hr⟩ := hrep a
    obtain ⟨r', u', hu', hr'⟩ := hrep t
    have hs : r' * u ∈ W.primeCompl :=
      W.primeCompl.mul_mem (hnum t r' u' t.2 hu' hr') fun h => hu (hWU h)
    refine ⟨IsLocalization.mk' _ (r * u') ⟨r' * u, hs⟩, ?_⟩
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_iff_eq]
    congr 1
    simp only [map_mul]
    linear_combination (φ r) * hr' - (φ r') * hr

  have hker : Ideal.comap ψ ⊥ ≤ J.map (algebraMap R (Localization.AtPrime W)) := by
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot] at hx
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective W.primeCompl x
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨⟨t, ht⟩, htr⟩ := hx
    obtain ⟨r', u', hu', hr'⟩ := hrep t
    have hr'W := hnum t r' u' ht hu' hr'
    have h0 : φ (r' * r) = 0 := by
      rw [map_mul, ← hr', mul_right_comm, htr, zero_mul]
    rw [hφ, localQuotMap, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
      IsLocalization.mem_map_algebraMap_iff U.primeCompl] at h0
    obtain ⟨⟨⟨i, hi⟩, v⟩, hv⟩ := h0
    rw [← map_mul, IsLocalization.eq_iff_exists U.primeCompl] at hv
    obtain ⟨c, hc⟩ := hv
    have hcW : (c : R) * r' * v ∈ W.primeCompl :=
      W.primeCompl.mul_mem (W.primeCompl.mul_mem (fun h => c.2 (hWU h)) hr'W) fun h => v.2 (hWU h)
    have hmemP : (c : R) * r' * v * r ∈ P := by
      have : (c : R) * (r' * r * v) = c * r' * v * r := by ring
      rw [← this, hc]
      exact P.mul_mem_left _ hi
    have hrJ : algebraMap R (Localization.AtPrime W) r ∈ J.map (algebraMap R (Localization.AtPrime W)) := by
      rw [← Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units (Localization.AtPrime W) ⟨_, hcW⟩), ← map_mul]
      exact Ideal.mem_map_of_mem _ (hPJ hmemP)
    show IsLocalization.mk' (Localization.AtPrime W) r s ∈ _
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ hrJ

  let : CommRing (Localization.AtPrime p) := inferInstance
  have hcomp : ψ.comp (algebraMap R (Localization.AtPrime W)) = (algebraMap (localQuot P U) (Localization.AtPrime p)).comp φ :=
    RingHom.ext fun x => Localization.localRingHom_to_map W p φ hcW.symm x
  have hI : (J.map φ).map (algebraMap (localQuot P U) (Localization.AtPrime p)) = (J.map (algebraMap R (Localization.AtPrime W))).map ψ := by
    rw [Ideal.map_map, Ideal.map_map, hcomp]
  let g := (Ideal.Quotient.mk ((J.map φ).map (algebraMap (localQuot P U) (Localization.AtPrime p)))).comp ψ
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hψ
  have hgk : J.map (algebraMap R (Localization.AtPrime W)) = RingHom.ker g := by
    rw [← RingHom.comap_ker, Ideal.mk_ker, hI, Ideal.comap_map_of_surjective _ hψ, sup_eq_left.mpr hker]
  have key := length_self_eq_of_ringEquiv ((Ideal.quotEquivOfEq hgk).trans (RingHom.quotientKerEquivOfSurjective hg))
  rw [← length_localizedModule_quot, ← length_localizedModule_quot] at key
  subst hp
  exact congrArg (fun n : ℕ∞ => ((n.toNat : ℕ) : ℤ)) key

end GroundTheory.Heights₂.Heights.NumbersDVR
