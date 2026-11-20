import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.SatakeDualWeyl.StatementC
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramLoc
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ModuliIntegralCharts

noncomputable section

open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf

namespace TypedLoc

open Formalism.MainNotions.S

section Split

open NumberField IsDedekindDomain

variable (L : Type) [Field L] [NumberField L]

/- English proof (translation)
The claim follows from `PrincipalIdealRing.isMaximal_of_irreducible (Int.prime_iff_natAbs_prime.2 (by simpa using hp)).irreducible`.
-/
theorem span_p_maximal {p : ℕ} (hp : p.Prime) : (Ideal.span {(p : ℤ)}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible (Int.prime_iff_natAbs_prime.2 (by simpa using hp)).irreducible

/- English proof (translation)
Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hp.ne_zero` after adjusting the coercions.
-/
theorem span_p_ne_bot {p : ℕ} (hp : p.Prime) : Ideal.span {(p : ℤ)} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero

/- English proof (translation)
Use `span_p_maximal hp` as an intermediate fact. Use extensionality with `P`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hP, hlo⟩`. Establish `hPb : P ≠ ⊥`.

Introduce `h0`. Use `hlo.over` as an intermediate fact. Rewrite `this` using `[h0]`. Apply `span_p_ne_bot hp` to reduce the goal to its premises. Rewrite using `[this]`.

Use extensionality with `x`. Simplify using `[Ideal.under, Ideal.mem_comap]`. Use `⟨⟨P, hP, hPb⟩, ?_, rfl⟩` and prove the remaining obligations. Use `show ((p : ℕ) : 𝓞 L) ∈ P`. Establish `h1 : (p : ℤ) ∈ Ideal.under ℤ P`.

Rewrite using `[← hlo.over]`. Conclude with `Ideal.subset_span rfl`. Simplify `h1` using `[Ideal.under, Ideal.mem_comap]`. Introduce and unpack `⟨v, hv, rfl⟩`. Use `⟨v.isPrime, ⟨?_⟩⟩` and prove the remaining obligations.

Establish `hle : Ideal.span {(p : ℤ)} ≤ Ideal.under ℤ v.asIdeal`. Rewrite using `[Ideal.span_le]`. Introduce `x hx`. Rewrite `hx` using `[Set.mem_singleton_iff]`. Substitute `hx` using the available equality.

Simplify `hv` using `[Ideal.under, Ideal.mem_comap]`. Conclude with `(Ideal.IsMaximal.eq_of_le this (Ideal.IsPrime.ne_top (Ideal.comap_isPrime _ _)) hle)`.
-/
theorem primesOver_eq {p : ℕ} (hp : p.Prime) :
    (Ideal.span {(p : ℤ)}).primesOver (𝓞 L) =
      (fun v : HeightOneSpectrum (𝓞 L) => v.asIdeal) '' {v | ((p : ℕ) : 𝓞 L) ∈ v.asIdeal} := by
  have := span_p_maximal hp
  ext P
  constructor
  · rintro ⟨hP, hlo⟩
    have hPb : P ≠ ⊥ := by
      intro h0
      have := hlo.over
      rw [h0] at this
      apply span_p_ne_bot hp
      rw [this]
      ext x; simp [Ideal.under, Ideal.mem_comap]
    refine ⟨⟨P, hP, hPb⟩, ?_, rfl⟩
    show ((p : ℕ) : 𝓞 L) ∈ P
    have h1 : (p : ℤ) ∈ Ideal.under ℤ P := by
      rw [← hlo.over]; exact Ideal.subset_span rfl
    simpa [Ideal.under, Ideal.mem_comap] using h1
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v.isPrime, ⟨?_⟩⟩
    have hle : Ideal.span {(p : ℤ)} ≤ Ideal.under ℤ v.asIdeal := by
      rw [Ideal.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      simpa [Ideal.under, Ideal.mem_comap] using hv
    exact (Ideal.IsMaximal.eq_of_le this (Ideal.IsPrime.ne_top (Ideal.comap_isPrime _ _)) hle)

/- English proof (translation)
Use `span_p_maximal hp` as an intermediate fact. Establish `hq0` using `span_p_ne_bot hp`. Establish `hsum` using `Ideal.sum_ramification_inertia (𝓞 L) ℚ L hq0`. Establish `hcard : (IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 L)).card = Module.finrank ℚ L`. Rewrite using `[← h, ← Set.ncard_coe_finset, IsDedekindDomain.coe_primesOverFinset hq0, primesOver_eq L hp]`.

Conclude with `Set.ncard_image_of_injective _ (fun v w hvw => HeightOneSpectrum.ext hvw)`. Establish `hpos : ∀ Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 L), 1 ≤ (Ideal.span {(p : ℤ)}).ramificationIdx' Q * (Ideal.span {(p : ℤ)}).inertiaDeg' Q`. Introduce `Q hQ`. Rewrite `hQ` using `[IsDedekindDomain.mem_primesOverFinset_iff hq0]`. Take `⟨hQp, hQl⟩` from `hQ`.

Establish `he : (Ideal.span {(p : ℤ)}).ramificationIdx' Q ≠ 0`. Use `Ideal.IsDedekindDomain.ramificationIdx'_ne_zero ?_ hQp ?_` and prove the remaining obligations. Conclude with `Ideal.map_ne_bot_of_ne_bot hq0`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Conclude with `le_of_eq hQl.over`.

Establish `hf` using `Ideal.inertiaDeg'_pos (Ideal.span {(p : ℤ)}) Q`. Conclude with `Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero he hf.ne')`. Establish `hall : ∀ Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 L), (Ideal.span {(p : ℤ)}).ramificationIdx' Q * (Ideal.span {(p : ℤ)}).inertiaDeg' Q = 1`. Establish `h2 : ∑ Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 L), ((Ideal.span {(p : ℤ)}).ramificationIdx' Q * (Ideal.span {(p : ℤ)}).inertiaDeg' Q - 1) = 0`. Establish `h3` using `Finset.sum_tsub_distrib (s := IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 L)) (f := fun Q => (Ideal.span {(p : ℤ)}).ramificationIdx' Q * (Ideal.span {(p : ℤ)}).inertiaDeg' Q) (g := fun _ => 1) hpos`.

Rewrite using `[h3, hsum, Finset.sum_const, smul_eq_mul, mul_one, hcard, Nat.sub_self]`. Introduce `Q hQ`. Use `(Finset.sum_eq_zero_iff.1 h2) Q hQ` as an intermediate fact. Use `hpos Q hQ` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hP' : P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 L)` using `(IsDedekindDomain.mem_primesOverFinset_iff hq0 _).2 hPp`. Use `hall P hP'` as an intermediate fact. Conclude with `⟨Nat.eq_one_of_mul_eq_one_right this, Nat.eq_one_of_mul_eq_one_left this⟩`.
-/
theorem split_ef {p : ℕ} (hp : p.Prime)
    (h : ({v : HeightOneSpectrum (𝓞 L) | ((p : ℕ) : 𝓞 L) ∈ v.asIdeal}).ncard = Module.finrank ℚ L)
    (P : Ideal (𝓞 L)) (hPp : P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 L)) :
    (Ideal.span {(p : ℤ)}).ramificationIdx' P = 1 ∧ (Ideal.span {(p : ℤ)}).inertiaDeg' P = 1 := by
  classical
  have := span_p_maximal hp
  have hq0 := span_p_ne_bot hp
  have hsum := Ideal.sum_ramification_inertia (𝓞 L) ℚ L hq0
  have hcard : (IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 L)).card = Module.finrank ℚ L := by
    rw [← h, ← Set.ncard_coe_finset, IsDedekindDomain.coe_primesOverFinset hq0, primesOver_eq L hp]
    exact Set.ncard_image_of_injective _ (fun v w hvw => HeightOneSpectrum.ext hvw)
  have hpos : ∀ Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 L),
      1 ≤ (Ideal.span {(p : ℤ)}).ramificationIdx' Q * (Ideal.span {(p : ℤ)}).inertiaDeg' Q := by
    intro Q hQ
    rw [IsDedekindDomain.mem_primesOverFinset_iff hq0] at hQ
    obtain ⟨hQp, hQl⟩ := hQ
    have he : (Ideal.span {(p : ℤ)}).ramificationIdx' Q ≠ 0 := by
      refine Ideal.IsDedekindDomain.ramificationIdx'_ne_zero ?_ hQp ?_
      · exact Ideal.map_ne_bot_of_ne_bot hq0
      · rw [Ideal.map_le_iff_le_comap]; exact le_of_eq hQl.over
    have hf := Ideal.inertiaDeg'_pos (Ideal.span {(p : ℤ)}) Q
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero he hf.ne')
  have hall : ∀ Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 L),
      (Ideal.span {(p : ℤ)}).ramificationIdx' Q * (Ideal.span {(p : ℤ)}).inertiaDeg' Q = 1 := by
    have h2 : ∑ Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 L),
        ((Ideal.span {(p : ℤ)}).ramificationIdx' Q * (Ideal.span {(p : ℤ)}).inertiaDeg' Q - 1) = 0 := by
      have h3 := Finset.sum_tsub_distrib (s := IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 L))
        (f := fun Q => (Ideal.span {(p : ℤ)}).ramificationIdx' Q * (Ideal.span {(p : ℤ)}).inertiaDeg' Q)
        (g := fun _ => 1) hpos
      rw [h3, hsum, Finset.sum_const, smul_eq_mul, mul_one, hcard, Nat.sub_self]
    intro Q hQ
    have := (Finset.sum_eq_zero_iff.1 h2) Q hQ
    have := hpos Q hQ
    omega
  have hP' : P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 L) := (IsDedekindDomain.mem_primesOverFinset_iff hq0 _).2 hPp
  have := hall P hP'
  exact ⟨Nat.eq_one_of_mul_eq_one_right this, Nat.eq_one_of_mul_eq_one_left this⟩

end Split

section Tower

open NumberField IsDedekindDomain

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/- English proof (translation)
The claim follows from `inferInstance`.
-/
theorem int_tower : IsScalarTower ℤ (𝓞 K) (𝓞 L) := inferInstance

/- English proof (translation)
Use `span_p_maximal hp` as an intermediate fact. Establish `hq0` using `span_p_ne_bot hp`. Establish `hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 L))` using `FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L)`. Take `⟨Q, -, hQp, hQv⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 L) v.asIdeal ⊥ (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)`. Establish `hvq : v.asIdeal ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K)`.

Rewrite using `[primesOver_eq K hp]`. Conclude with `⟨v, hv, rfl⟩`. Establish `hvlo : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)})` using `hvq.2`. Establish `hQlo' : Q.LiesOver v.asIdeal` using `⟨hQv.symm⟩`. Establish `hQq : Q ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 L)`.

Use `⟨hQp, ⟨?_⟩⟩` and prove the remaining obligations. Rewrite using `[hvlo.over]`. Use `show Ideal.comap (algebraMap ℤ (𝓞 K)) v.asIdeal = Ideal.comap (algebraMap ℤ (𝓞 L)) Q`. Rewrite using `[← hQv, Ideal.comap_comap]`. Use `congr 1`.

Conclude with `RingHom.ext_int _ _`. Take `⟨he, hf⟩` from `split_ef L hp h Q hQq`. Use `hvq.1` as an intermediate fact. Establish `hvmax : v.asIdeal.IsMaximal` using `v.isMaximal`. Establish `hQlo : Q.LiesOver (Ideal.span {(p : ℤ)})` using `hQq.2`.

Establish `hf'` using `Ideal.inertiaDeg'_algebra_tower (Ideal.span {(p : ℤ)}) v.asIdeal Q`. Rewrite `hf'` using `[hf]`. Establish `hQb : Q ≠ ⊥`. Introduce `h0`. Apply `v.ne_bot` to reduce the goal to its premises.

Rewrite using `[← hQv, h0, Ideal.comap_bot_of_injective _ hinj]`. Establish `hmap1 : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) v.asIdeal ≠ ⊥` using `Ideal.map_ne_bot_of_ne_bot v.ne_bot`. Establish `hmap2 : Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {(p : ℤ)}) ≠ ⊥` using `Ideal.map_ne_bot_of_ne_bot hq0`. Establish `hle : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) v.asIdeal ≤ Q`. Rewrite using `[Ideal.map_le_iff_le_comap, hQv]`.

Establish `he'` using `Ideal.ramificationIdx'_algebra_tower (p := Ideal.span {(p : ℤ)}) hmap1 hmap2 hle`. Rewrite `he'` using `[he]`. Conclude with `⟨Nat.eq_one_of_mul_eq_one_right he'.symm, Nat.eq_one_of_mul_eq_one_right hf'.symm⟩`.
-/
theorem tower_ef {p : ℕ} (hp : p.Prime)
    (h : ({v : HeightOneSpectrum (𝓞 L) | ((p : ℕ) : 𝓞 L) ∈ v.asIdeal}).ncard = Module.finrank ℚ L)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    (Ideal.span {(p : ℤ)}).ramificationIdx' v.asIdeal = 1 ∧ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal = 1 := by
  have := span_p_maximal hp
  have hq0 := span_p_ne_bot hp
  have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 L)) := FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L)
  obtain ⟨Q, -, hQp, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 L) v.asIdeal ⊥
    (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
  have hvq : v.asIdeal ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) := by
    rw [primesOver_eq K hp]; exact ⟨v, hv, rfl⟩
  have hvlo : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := hvq.2
  have hQlo' : Q.LiesOver v.asIdeal := ⟨hQv.symm⟩
  have hQq : Q ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 L) := by
    refine ⟨hQp, ⟨?_⟩⟩
    rw [hvlo.over]
    show Ideal.comap (algebraMap ℤ (𝓞 K)) v.asIdeal = Ideal.comap (algebraMap ℤ (𝓞 L)) Q
    rw [← hQv, Ideal.comap_comap]
    congr 1
    exact RingHom.ext_int _ _
  obtain ⟨he, hf⟩ := split_ef L hp h Q hQq
  have := hvq.1
  have hvmax : v.asIdeal.IsMaximal := v.isMaximal
  have hQlo : Q.LiesOver (Ideal.span {(p : ℤ)}) := hQq.2
  have hf' := Ideal.inertiaDeg'_algebra_tower (Ideal.span {(p : ℤ)}) v.asIdeal Q
  rw [hf] at hf'
  have hQb : Q ≠ ⊥ := by
    intro h0; apply v.ne_bot; rw [← hQv, h0, Ideal.comap_bot_of_injective _ hinj]
  have hmap1 : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) v.asIdeal ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot v.ne_bot
  have hmap2 : Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {(p : ℤ)}) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hq0
  have hle : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) v.asIdeal ≤ Q := by
    rw [Ideal.map_le_iff_le_comap, hQv]
  have he' := Ideal.ramificationIdx'_algebra_tower (p := Ideal.span {(p : ℤ)}) hmap1 hmap2 hle
  rw [he] at he'
  exact ⟨Nat.eq_one_of_mul_eq_one_right he'.symm, Nat.eq_one_of_mul_eq_one_right hf'.symm⟩

/- English proof (translation)
Establish `hvq : v.asIdeal ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K)`. Rewrite using `[primesOver_eq K hp]`. Conclude with `⟨v, hv, rfl⟩`. Establish `hvlo : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)})` using `hvq.2`. Establish `h1` using `Ideal.absNorm_eq_pow_inertiaDeg (R := 𝓞 K) (p := (p : ℤ)) v.asIdeal (Nat.prime_iff_prime_int.1 hp)`.

Rewrite `h1` using `[(tower_ef K L hp h v hv).2, pow_one, Int.natAbs_natCast, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Conclude with `h1`.
-/
theorem tower_card {p : ℕ} (hp : p.Prime)
    (h : ({v : HeightOneSpectrum (𝓞 L) | ((p : ℕ) : 𝓞 L) ∈ v.asIdeal}).ncard = Module.finrank ℚ L)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    Nat.card (𝓞 K ⧸ v.asIdeal) = p := by
  have hvq : v.asIdeal ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) := by
    rw [primesOver_eq K hp]; exact ⟨v, hv, rfl⟩
  have hvlo : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := hvq.2
  have h1 := Ideal.absNorm_eq_pow_inertiaDeg (R := 𝓞 K) (p := (p : ℤ)) v.asIdeal (Nat.prime_iff_prime_int.1 hp)
  rw [(tower_ef K L hp h v hv).2, pow_one, Int.natAbs_natCast, Ideal.absNorm_apply, Submodule.cardQuot_apply] at h1
  exact h1

/- English proof (translation)
Establish `he` using `(tower_ef K L hp h v hv).1`. Establish `hq0` using `span_p_ne_bot hp`. Establish `hmap : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) ≠ ⊥` using `Ideal.map_ne_bot_of_ne_bot hq0`. Establish `hcount` using `Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmap v.isPrime v.ne_bot`. Rewrite `hcount` using `[he]`.

Establish `hp0 : ((p : ℕ) : 𝓞 K) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Establish `hnot2 : ((p : ℕ) : 𝓞 K) ∉ v.asIdeal ^ 2`. Introduce `h2`. Establish `hle : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) ≤ v.asIdeal ^ 2`. Rewrite using `[Ideal.map_span, Ideal.span_le]`.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite `hx` using `[Set.mem_singleton_iff]`. Substitute `hx` using the available equality. Simplify using `using h2`. Take `⟨J, hJ⟩` from `Ideal.dvd_iff_le.2 hle`.

Establish `hJ0 : J ≠ ⊥` using `by rintro rfl; rw [Ideal.mul_bot] at hJ; exact hmap hJ`. Establish `hv2 : v.asIdeal ^ 2 ≠ ⊥` using `pow_ne_zero _ v.ne_bot`. Rewrite `hcount` using `[hJ, UniqueFactorizationMonoid.normalizedFactors_mul hv2 hJ0, UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.count_add, Multiset.count_nsmul, UniqueFactorizationMonoid.normalizedFactors_irreducible (Ideal.prime_of_isPrime v.ne_bot v.isPrime).irreducible, normalize_eq, …`. Use linear arithmetic over natural numbers and integers. Establish `h1 : v.intValuation ((p : ℕ) : 𝓞 K) ≤ WithZero.exp (-((1 : ℕ) : ℤ))` using `(HeightOneSpectrum.intValuation_le_pow_iff_mem v _ 1).2 (by simpa using hv)`.

Establish `h2 : ¬ v.intValuation ((p : ℕ) : 𝓞 K) ≤ WithZero.exp (-((2 : ℕ) : ℤ))` using `fun hh => hnot2 ((HeightOneSpectrum.intValuation_le_pow_iff_mem v _ 2).1 hh)`. Establish `hne` using `HeightOneSpectrum.intValuation_ne_zero v _ hp0`. Take `⟨k, hk⟩ : ∃ k : ℤ, v.intValuation ((p : ℕ) : 𝓞 K) = WithZero.exp k` from `⟨WithZero.log (v.intValuation ((p : ℕ) : 𝓞 K)), (WithZero.exp_log hne).symm⟩`. Rewrite `h1`, `h2` using `[hk, WithZero.exp_le_exp]`. Rewrite using `[hk]`.

Use `congr 1`. Move the coercions through the operations in `at h1 h2`. Use linear arithmetic over natural numbers and integers.
-/
theorem tower_val {p : ℕ} (hp : p.Prime)
    (h : ({v : HeightOneSpectrum (𝓞 L) | ((p : ℕ) : 𝓞 L) ∈ v.asIdeal}).ncard = Module.finrank ℚ L)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    v.intValuation ((p : ℕ) : 𝓞 K) = WithZero.exp (-1 : ℤ) := by
  classical
  have he := (tower_ef K L hp h v hv).1
  have hq0 := span_p_ne_bot hp
  have hmap : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hq0
  have hcount := Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmap v.isPrime v.ne_bot
  rw [he] at hcount
  have hp0 : ((p : ℕ) : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hnot2 : ((p : ℕ) : 𝓞 K) ∉ v.asIdeal ^ 2 := by
    intro h2
    have hle : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) ≤ v.asIdeal ^ 2 := by
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨x, hx, rfl⟩
      rw [Set.mem_singleton_iff] at hx; subst hx
      simpa using h2
    obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle
    have hJ0 : J ≠ ⊥ := by rintro rfl; rw [Ideal.mul_bot] at hJ; exact hmap hJ
    have hv2 : v.asIdeal ^ 2 ≠ ⊥ := pow_ne_zero _ v.ne_bot
    rw [hJ, UniqueFactorizationMonoid.normalizedFactors_mul hv2 hJ0,
      UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.count_add, Multiset.count_nsmul,
      UniqueFactorizationMonoid.normalizedFactors_irreducible (Ideal.prime_of_isPrime v.ne_bot v.isPrime).irreducible,
      normalize_eq, Multiset.count_singleton_self] at hcount
    omega
  have h1 : v.intValuation ((p : ℕ) : 𝓞 K) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) :=
    (HeightOneSpectrum.intValuation_le_pow_iff_mem v _ 1).2 (by simpa using hv)
  have h2 : ¬ v.intValuation ((p : ℕ) : 𝓞 K) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    fun hh => hnot2 ((HeightOneSpectrum.intValuation_le_pow_iff_mem v _ 2).1 hh)
  have hne := HeightOneSpectrum.intValuation_ne_zero v _ hp0
  obtain ⟨k, hk⟩ : ∃ k : ℤ, v.intValuation ((p : ℕ) : 𝓞 K) = WithZero.exp k :=
    ⟨WithZero.log (v.intValuation ((p : ℕ) : 𝓞 K)), (WithZero.exp_log hne).symm⟩
  rw [hk, WithZero.exp_le_exp] at h1 h2
  rw [hk]
  congr 1
  push_cast at h1 h2
  omega

end Tower

section GiVal

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Formalism.BasicNotions

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

/- English proof (translation)
Use `letI : Algebra X.B.I.F D.host.E := (X.ιE.toRingHom.comp (algebraMap X.B.I.F X.B.I.E)).toAlgebra`. Conclude with `tower_val X.B.I.F D.host.E (D.host.g_prime i) (D.nd.g_split i) v hv`.
-/
theorem gi_val (v : HeightOneSpectrum (𝓞 X.B.I.F)) (i : Fin 2) (hv : ((D.host.g i : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal) :
    v.intValuation ((D.host.g i : ℕ) : 𝓞 X.B.I.F) = WithZero.exp (-1 : ℤ) := by
  letI : Algebra X.B.I.F D.host.E := (X.ιE.toRingHom.comp (algebraMap X.B.I.F X.B.I.E)).toAlgebra
  exact tower_val X.B.I.F D.host.E (D.host.g_prime i) (D.nd.g_split i) v hv

end GiVal

section Local

open Formalism.MainNotions.S NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Formalism.BasicNotions Formalism.L2.SG.HidaSetting
open scoped TensorProduct

variable (I : AutInst)

/- English proof (translation)
The claim follows from `(I.cm.fixed (y + star y)).1 (by rw [star_add, star_star, add_comm])`.
-/
theorem star_add_self_mem (y : I.E) : ∃ c : I.F, algebraMap I.F I.E c = y + star y :=
  (I.cm.fixed (y + star y)).1 (by rw [star_add, star_star, add_comm])

def tlin : I.E →ₗ[I.F] I.F where
  toFun y := (star_add_self_mem I y).choose
  map_add' x y := by
    apply (algebraMap I.F I.E).injective
    rw [map_add, (star_add_self_mem I (x + y)).choose_spec, (star_add_self_mem I x).choose_spec,
      (star_add_self_mem I y).choose_spec, star_add]; ring
  map_smul' c y := by
    apply (algebraMap I.F I.E).injective
    rw [RingHom.id_apply, smul_eq_mul, map_mul, (star_add_self_mem I (c • y)).choose_spec,
      (star_add_self_mem I y).choose_spec, Algebra.smul_def, star_mul]
    have hc : star (algebraMap I.F I.E c) = algebraMap I.F I.E c := (I.cm.fixed _).2 ⟨c, rfl⟩
    rw [hc]; ring

/- English proof (translation)
The claim follows from `(star_add_self_mem I y).choose_spec`.
-/
theorem tlin_spec (y : I.E) : algebraMap I.F I.E (tlin I y) = y + star y := (star_add_self_mem I y).choose_spec

/- English proof (translation)
Apply `(algebraMap I.F I.E).injective` to reduce the goal to its premises. Rewrite using `[tlin_spec, star_one, map_ofNat]`. Evaluate the numerical expressions.
-/
theorem tlin_one : tlin I 1 = 2 := by
  apply (algebraMap I.F I.E).injective
  rw [tlin_spec, star_one, map_ofNat]; norm_num

/- English proof (translation)
Establish `h1 : IsIntegral ℤ ((o : I.E) + star (o : I.E))`. Use `(RingOfIntegers.isIntegral_coe o).add ?_` and prove the remaining obligations. Establish `: star (o : I.E) = I.cm.sig (o : I.E)` using `rfl`. Rewrite using `[this]`. Conclude with `(RingOfIntegers.isIntegral_coe o).map (I.cm.sig.restrictScalars ℤ)`.

Rewrite `h1` using `[← tlin_spec]`. Establish `h2 : IsIntegral ℤ (tlin I (o : I.E))` using `(isIntegral_algebraMap_iff (algebraMap I.F I.E).injective).1 h1`. Conclude with `⟨⟨_, h2⟩, rfl⟩`.
-/
theorem tlin_int (o : 𝓞 I.E) : tlin I (o : I.E) ∈ (algebraMap (𝓞 I.F) I.F).range := by
  have h1 : IsIntegral ℤ ((o : I.E) + star (o : I.E)) := by
    refine (RingOfIntegers.isIntegral_coe o).add ?_
    have : star (o : I.E) = I.cm.sig (o : I.E) := rfl
    rw [this]
    exact (RingOfIntegers.isIntegral_coe o).map (I.cm.sig.restrictScalars ℤ)
  rw [← tlin_spec] at h1
  have h2 : IsIntegral ℤ (tlin I (o : I.E)) :=
    (isIntegral_algebraMap_iff (algebraMap I.F I.E).injective).1 h1
  exact ⟨⟨_, h2⟩, rfl⟩

variable (v : HeightOneSpectrum (𝓞 I.F))

def trV : I.E ⊗[I.F] v.adicCompletion I.F →ₗ[I.F] v.adicCompletion I.F :=
  TensorProduct.lift ((LinearMap.lsmul I.F (v.adicCompletion I.F)).comp (tlin I))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem trV_tmul (y : I.E) (c : v.adicCompletion I.F) : trV I v (y ⊗ₜ c) = tlin I y • c := rfl

abbrev sigV : I.E ⊗[I.F] v.adicCompletion I.F →+* I.E ⊗[I.F] v.adicCompletion I.F :=
  Formalism.UG.sigR I.cm.sig (v.adicCompletion I.F)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sigV_tmul (y : I.E) (c : v.adicCompletion I.F) : sigV I v (y ⊗ₜ c) = star y ⊗ₜ c := rfl

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul y c`. Rewrite using `[sigV_tmul, trV_tmul, ← TensorProduct.add_tmul, ← tlin_spec, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`. Consider the case `add a b ha hb`.

Rewrite using `[map_add, map_add, TensorProduct.tmul_add, ← ha, ← hb]`. Normalize the expressions using the abelian group laws.
-/
theorem add_sig (z : I.E ⊗[I.F] v.adicCompletion I.F) :
    z + sigV I v z = (1 : I.E) ⊗ₜ[I.F] trV I v z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul y c =>
    rw [sigV_tmul, trV_tmul, ← TensorProduct.add_tmul, ← tlin_spec, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul]
  | add a b ha hb =>
    rw [map_add, map_add, TensorProduct.tmul_add, ← ha, ← hb]; abel

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul y d`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, trV_tmul, trV_tmul, mul_smul_comm]`. Consider the case `add a b ha hb => rw [mul_add, map_add, map_add, ha, hb, mul_add]`.
-/
theorem trV_mul_tmul (c : v.adicCompletion I.F) (z : I.E ⊗[I.F] v.adicCompletion I.F) :
    trV I v (((1 : I.E) ⊗ₜ[I.F] c) * z) = c * trV I v z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul y d =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, trV_tmul, trV_tmul, mul_smul_comm]
  | add a b ha hb => rw [mul_add, map_add, map_add, ha, hb, mul_add]

/- English proof (translation)
Rewrite using `[trV_tmul, tlin_one, two_smul, two_mul]`.
-/
theorem trV_one_tmul (c : v.adicCompletion I.F) : trV I v ((1 : I.E) ⊗ₜ[I.F] c) = 2 * c := by
  rw [trV_tmul, tlin_one, two_smul, two_mul]

/- English proof (translation)
Use `congrArg (trV I v) h` as an intermediate fact. Rewrite `this` using `[trV_one_tmul, trV_one_tmul]`. Establish `h2 : (2 : v.adicCompletion I.F) ≠ 0`. Introduce `h`. Apply `(two_ne_zero : (2 : I.F) ≠ 0)` to reduce the goal to its premises.

Apply `(algebraMap I.F (v.adicCompletion I.F)).injective` to reduce the goal to its premises. Rewrite using `[map_ofNat, h, map_zero]`. Conclude with `mul_left_cancel₀ h2 this`.
-/
theorem one_tmul_inj {c d : v.adicCompletion I.F} (h : (1 : I.E) ⊗ₜ[I.F] c = (1 : I.E) ⊗ₜ[I.F] d) : c = d := by
  have := congrArg (trV I v) h
  rw [trV_one_tmul, trV_one_tmul] at this
  have h2 : (2 : v.adicCompletion I.F) ≠ 0 := by
    intro h
    apply (two_ne_zero : (2 : I.F) ≠ 0)
    apply (algebraMap I.F (v.adicCompletion I.F)).injective
    rw [map_ofNat, h, map_zero]
  exact mul_left_cancel₀ h2 this

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul y a => rfl`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb, ← map_add, ← map_add]`.
-/
theorem prV_sigA (x : I.E ⊗[I.F] Af I.F) :
    Formalism.UG.prV (E := I.E) v (sigA I x) = sigV I v (Formalism.UG.prV (E := I.E) v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul y a => rfl
  | add a b ha hb => rw [map_add, map_add, ha, hb, ← map_add, ← map_add]

end Local

section Red

open Formalism.MainNotions.S NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Formalism.BasicNotions Formalism.L2.SG.HidaSetting
open scoped TensorProduct

variable (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))

def phiV : 𝓞 I.E ⊗[ℤ] v.adicCompletionIntegers I.F →ₐ[ℤ] I.E ⊗[I.F] v.adicCompletion I.F :=
  Algebra.TensorProduct.productMap
    { (Algebra.TensorProduct.includeLeftRingHom.comp (algebraMap (𝓞 I.E) I.E)) with
      commutes' := fun z => by simp }
    { (Algebra.TensorProduct.includeRight.toRingHom.comp (v.adicCompletionIntegers I.F).subtype) with
      commutes' := fun z => by simp }

/- English proof (translation)
Rewrite using `[phiV, Algebra.TensorProduct.productMap_apply_tmul]`. Use `show (o : I.E) ⊗ₜ[I.F] (1 : v.adicCompletion I.F) * ((1 : I.E) ⊗ₜ[I.F] (r : v.adicCompletion I.F)) = _`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`.
-/
theorem phiV_tmul (o : 𝓞 I.E) (r : v.adicCompletionIntegers I.F) :
    phiV I v (o ⊗ₜ r) = (o : I.E) ⊗ₜ[I.F] (r : v.adicCompletion I.F) := by
  rw [phiV, Algebra.TensorProduct.productMap_apply_tmul]
  show (o : I.E) ⊗ₜ[I.F] (1 : v.adicCompletion I.F) * ((1 : I.E) ⊗ₜ[I.F] (r : v.adicCompletion I.F)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/- English proof (translation)
Establish `hle : Formalism.UG.tensInt (F` using `I.F) (v.adicCompletion I.F) (Formalism.UG.intOE I.E) (v.adicCompletionIntegers I.F).toSubring ≤ (phiV I v).range.toSubring := by`. Use `Subring.closure_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ (⟨⟨x, hx⟩, rfl⟩ | ⟨y, rfl⟩)`. Take `⟨o, rfl⟩` from `hx`. Use `⟨o ⊗ₜ 1, ?_⟩` and prove the remaining obligations.

Use `show phiV I v (o ⊗ₜ 1) = _`. Rewrite using `[phiV_tmul]`. Both sides reduce to the same expression. Use `⟨1 ⊗ₜ y, ?_⟩ show phiV I v (1 ⊗ₜ y) = _` and prove the remaining obligations. Rewrite using `[phiV_tmul]`.

Simplify using the standard rewrite rules. Take `⟨t, rfl⟩` from `hle hx`. Use `clear hx hle`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul o r => show trV I v (phiV I v (o ⊗ₜ r)) ∈ _`. Rewrite using `[phiV_tmul, trV_tmul]`. Take `⟨s, hs⟩` from `tlin_int I o`. Rewrite using `[← hs, Algebra.smul_def]`. Use `mul_mem ?_ r.2` and prove the remaining obligations.

Rewrite using `[show algebraMap I.F (v.adicCompletion I.F) ((algebraMap (𝓞 I.F) I.F) s) = ((s : I.F) : v.adicCompletion I.F) from rfl]`. Conclude with `coe_mem_adicCompletionIntegers v s`. Consider the case `add a b ha hb => show trV I v (phiV I v (a + b)) ∈ _`. Rewrite using `[map_add, map_add]`. Conclude with `add_mem ha hb`.
-/
theorem trV_intV {x : I.E ⊗[I.F] v.adicCompletion I.F}
    (hx : x ∈ Formalism.UG.tensInt (F := I.F) (v.adicCompletion I.F) (Formalism.UG.intOE I.E) (v.adicCompletionIntegers I.F).toSubring) :
    trV I v x ∈ v.adicCompletionIntegers I.F := by
  have hle : Formalism.UG.tensInt (F := I.F) (v.adicCompletion I.F) (Formalism.UG.intOE I.E) (v.adicCompletionIntegers I.F).toSubring ≤
      (phiV I v).range.toSubring := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨y, rfl⟩)
    · obtain ⟨o, rfl⟩ := hx
      refine ⟨o ⊗ₜ 1, ?_⟩
      show phiV I v (o ⊗ₜ 1) = _
      rw [phiV_tmul]; rfl
    · refine ⟨1 ⊗ₜ y, ?_⟩
      show phiV I v (1 ⊗ₜ y) = _
      rw [phiV_tmul]; simp
  obtain ⟨t, rfl⟩ := hle hx
  clear hx hle
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul o r =>
    show trV I v (phiV I v (o ⊗ₜ r)) ∈ _
    rw [phiV_tmul, trV_tmul]
    obtain ⟨s, hs⟩ := tlin_int I o
    rw [← hs, Algebra.smul_def]
    refine mul_mem ?_ r.2
    rw [show algebraMap I.F (v.adicCompletion I.F) ((algebraMap (𝓞 I.F) I.F) s) = ((s : I.F) : v.adicCompletion I.F) from rfl]
    exact coe_mem_adicCompletionIntegers v s
  | add a b ha hb =>
    show trV I v (phiV I v (a + b)) ∈ _
    rw [map_add, map_add]; exact add_mem ha hb

/- English proof (translation)
Assume the negation of the conclusion as `hδ0`. Take `⟨d, rfl⟩` from `WithZero.ne_zero_iff_exists.1 hδ0`. Break down `eq_or_ne γ 0 with hγ | hγ` into its components or cases. Use `hδ 1` as an intermediate fact. Rewrite `this` using `[hγ, pow_one]`.

Conclude with `WithZero.coe_ne_zero (le_antisymm this zero_le)`. Take `⟨t, rfl⟩` from `WithZero.ne_zero_iff_exists.1 hγ`. Establish `ht : Multiplicative.toAdd t < 0`. Establish `h1 : t < 1` using `by exact_mod_cast h`. Conclude with `h1`.

Establish `hk` using `hδ ((-(Multiplicative.toAdd d)).toNat + 1)`. Rewrite `hk` using `[← WithZero.coe_pow, WithZero.coe_le_coe]`. Establish `h2 : Multiplicative.toAdd d ≤ (((-(Multiplicative.toAdd d)).toNat + 1 : ℕ) : ℤ) * Multiplicative.toAdd t`. Use `Multiplicative.toAdd_le.2 hk` as an intermediate fact. Rewrite `this` using `[toAdd_pow, nsmul_eq_mul]`. Then use the resulting hypothesis.

Establish `h3 : (0 : ℤ) ≤ ((-(Multiplicative.toAdd d)).toNat : ℤ)` using `Nat.cast_nonneg _`. Establish `h4 : -(Multiplicative.toAdd d) ≤ ((-(Multiplicative.toAdd d)).toNat : ℤ)` using `Int.self_le_toNat _`. Move the coercions through the operations in `at h2`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem wz (γ δ : WithZero (Multiplicative ℤ)) (h : γ < 1) (hδ : ∀ k : ℕ, δ ≤ γ ^ k) : δ = 0 := by
  by_contra hδ0
  obtain ⟨d, rfl⟩ := WithZero.ne_zero_iff_exists.1 hδ0
  rcases eq_or_ne γ 0 with hγ | hγ
  · have := hδ 1
    rw [hγ, pow_one] at this
    exact WithZero.coe_ne_zero (le_antisymm this zero_le)
  obtain ⟨t, rfl⟩ := WithZero.ne_zero_iff_exists.1 hγ
  have ht : Multiplicative.toAdd t < 0 := by
    have h1 : t < 1 := by exact_mod_cast h
    exact h1
  have hk := hδ ((-(Multiplicative.toAdd d)).toNat + 1)
  rw [← WithZero.coe_pow, WithZero.coe_le_coe] at hk
  have h2 : Multiplicative.toAdd d ≤ (((-(Multiplicative.toAdd d)).toNat + 1 : ℕ) : ℤ) * Multiplicative.toAdd t := by
    have := Multiplicative.toAdd_le.2 hk
    rwa [toAdd_pow, nsmul_eq_mul] at this
  have h3 : (0 : ℤ) ≤ ((-(Multiplicative.toAdd d)).toNat : ℤ) := Nat.cast_nonneg _
  have h4 : -(Multiplicative.toAdd d) ≤ ((-(Multiplicative.toAdd d)).toNat : ℤ) := Int.self_le_toNat _
  push_cast at h2
  nlinarith

/- English proof (translation)
Establish `hγ : Valued.v π < 1`. Rewrite using `[hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]`. Evaluate the numerical expressions. Use `(Valued.v.zero_iff).1 (wz _ _ hγ fun k => ?_)` and prove the remaining obligations. Take `⟨u, hu, rfl⟩` from `h k`.

Rewrite using `[Valued.v.map_mul, Valued.v.map_pow]`. Conclude with `mul_le_of_le_one_right' ((mem_adicCompletionIntegers _ _ _).1 hu)`.
-/
theorem vdiv_zero {π c : v.adicCompletion I.F} (hπ : Valued.v π = WithZero.exp (-1 : ℤ))
    (h : ∀ k : ℕ, ∃ u ∈ v.adicCompletionIntegers I.F, c = π ^ k * u) : c = 0 := by
  have hγ : Valued.v π < 1 := by
    rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  refine (Valued.v.zero_iff).1 (wz _ _ hγ fun k => ?_)
  obtain ⟨u, hu, rfl⟩ := h k
  rw [Valued.v.map_mul, Valued.v.map_pow]
  exact mul_le_of_le_one_right' ((mem_adicCompletionIntegers _ _ _).1 hu)

end Red

end TypedLoc

open TypedLoc Formalism.MainNotions.S

section TypedPlaces

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Formalism.BasicNotions

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

/- English proof (translation)
Introduce `v i hv`. Use `letI : Algebra X.B.I.F D.host.E := (X.ιE.toRingHom.comp (algebraMap X.B.I.F X.B.I.E)).toAlgebra`. Conclude with `tower_card X.B.I.F D.host.E (D.host.g_prime i) (D.nd.g_split i) v hv`.
-/
theorem gResCard_holds : ∀ (v : HeightOneSpectrum (𝓞 X.B.I.F)) (i : Fin 2), ((D.host.g i : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
    Nat.card (𝓞 X.B.I.F ⧸ v.asIdeal) = D.host.g i := by
  intro v i hv
  letI : Algebra X.B.I.F D.host.E := (X.ιE.toRingHom.comp (algebraMap X.B.I.F X.B.I.E)).toAlgebra
  exact tower_card X.B.I.F D.host.E (D.host.g_prime i) (D.nd.g_split i) v hv

/- English proof (translation)
Introduce `v hv`. Establish `hv' : ((D.host.g 0 : ℕ) : 𝓞 X.B.I.F) * ((D.host.g 1 : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal`. Rewrite using `[← Nat.cast_mul, ← X.g_eq]`. Conclude with `hv`. Establish `hcop : IsCoprime ((D.host.g 0 : ℕ) : 𝓞 X.B.I.F) ((D.host.g 1 : ℕ) : 𝓞 X.B.I.F)`.

Establish `h : IsCoprime ((D.host.g 0 : ℕ) : ℤ) ((D.host.g 1 : ℕ) : ℤ)` using `Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)`. Simplify using `using h.map (Int.castRingHom (𝓞 X.B.I.F))`. Establish `hnot : ∀ i j : Fin 2, ((D.host.g i : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal → ((D.host.g j : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal → ((D.host.g 0 : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal ∧ ((D.host.g 1 : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal → False`. Introduce `_ _ _ _ ⟨h0, h1⟩`. Take `⟨a, b, hab⟩` from `hcop`.

Use `v.asIdeal.add_mem (v.asIdeal.mul_mem_left a h0) (v.asIdeal.mul_mem_left b h1)` as an intermediate fact. Rewrite `this` using `[hab]`. Conclude with `v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)`. Establish `e : ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) = (((X.B.g : ℕ) : X.B.I.F) : v.adicCompletion X.B.I.F)`. Rewrite using `[← map_natCast (algebraMap X.B.I.F (v.adicCompletion X.B.I.F))]`.

Both sides reduce to the same expression. Rewrite using `[e, valuedAdicCompletion_eq_valuation']`. Establish `e2 : ((X.B.g : ℕ) : X.B.I.F) = algebraMap (𝓞 X.B.I.F) X.B.I.F (((D.host.g 0 : ℕ) : 𝓞 X.B.I.F) * ((D.host.g 1 : ℕ) : 𝓞 X.B.I.F))`. Rewrite using `[X.g_eq]`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite using `[e2, valuation_of_algebraMap, map_mul]`. Break down `v.isPrime.mem_or_mem hv' with h0 | h1` into its components or cases. Establish `h1 : ((D.host.g 1 : ℕ) : 𝓞 X.B.I.F) ∉ v.asIdeal` using `fun h1 => hnot 0 1 h0 h1 ⟨h0, h1⟩`. Rewrite using `[gi_val X v 0 h0, intValuation_eq_one_iff.2 h1, mul_one]`.

Establish `h0 : ((D.host.g 0 : ℕ) : 𝓞 X.B.I.F) ∉ v.asIdeal` using `fun h0 => hnot 0 1 h0 h1 ⟨h0, h1⟩`. Rewrite using `[gi_val X v 1 h1, intValuation_eq_one_iff.2 h0, one_mul]`.
-/
theorem gUnif_holds : ∀ v : HeightOneSpectrum (𝓞 X.B.I.F), ((X.B.g : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
    Valued.v ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) = WithZero.exp (-1 : ℤ) := by
  intro v hv
  have hv' : ((D.host.g 0 : ℕ) : 𝓞 X.B.I.F) * ((D.host.g 1 : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal := by
    rw [← Nat.cast_mul, ← X.g_eq]; exact hv
  have hcop : IsCoprime ((D.host.g 0 : ℕ) : 𝓞 X.B.I.F) ((D.host.g 1 : ℕ) : 𝓞 X.B.I.F) := by
    have h : IsCoprime ((D.host.g 0 : ℕ) : ℤ) ((D.host.g 1 : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)
    simpa using h.map (Int.castRingHom (𝓞 X.B.I.F))
  have hnot : ∀ i j : Fin 2, ((D.host.g i : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal → ((D.host.g j : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      ((D.host.g 0 : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal ∧ ((D.host.g 1 : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal → False := by
    intro _ _ _ _ ⟨h0, h1⟩
    obtain ⟨a, b, hab⟩ := hcop
    have := v.asIdeal.add_mem (v.asIdeal.mul_mem_left a h0) (v.asIdeal.mul_mem_left b h1)
    rw [hab] at this
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)
  have e : ((X.B.g : ℕ) : v.adicCompletion X.B.I.F) =
      (((X.B.g : ℕ) : X.B.I.F) : v.adicCompletion X.B.I.F) := by
    rw [← map_natCast (algebraMap X.B.I.F (v.adicCompletion X.B.I.F))]; rfl
  rw [e, valuedAdicCompletion_eq_valuation']
  have e2 : ((X.B.g : ℕ) : X.B.I.F) = algebraMap (𝓞 X.B.I.F) X.B.I.F
      (((D.host.g 0 : ℕ) : 𝓞 X.B.I.F) * ((D.host.g 1 : ℕ) : 𝓞 X.B.I.F)) := by
    rw [X.g_eq]; push_cast; rfl
  rw [e2, valuation_of_algebraMap, map_mul]
  rcases v.isPrime.mem_or_mem hv' with h0 | h1
  · have h1 : ((D.host.g 1 : ℕ) : 𝓞 X.B.I.F) ∉ v.asIdeal := fun h1 => hnot 0 1 h0 h1 ⟨h0, h1⟩
    rw [gi_val X v 0 h0, intValuation_eq_one_iff.2 h1, mul_one]
  · have h0 : ((D.host.g 0 : ℕ) : 𝓞 X.B.I.F) ∉ v.asIdeal := fun h0 => hnot 0 1 h0 h1 ⟨h0, h1⟩
    rw [gi_val X v 1 h1, intValuation_eq_one_iff.2 h0, one_mul]

end TypedPlaces

def PsiCondAll : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers X.B.I.F)),
    ((X.B.g : ℕ) : NumberField.RingOfIntegers X.B.I.F) ∈ v.asIdeal →
      ∃ o ∈ v.adicCompletionIntegers X.B.I.F,
        X.psiEf (Formalism.L2.SG.HidaSetting.divN X.B.I X.B.g (X.ew * ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] Formalism.UG.P.afsplitI v o))) ≠ 1

namespace TypedLoc

section Key

open Formalism.MainNotions.S NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Formalism.BasicNotions Formalism.L2.SG.HidaSetting
open scoped TensorProduct

variable (I : AutInst)

/- English proof (translation)
Establish `h1 : IsAlgebraic ℚ x` using `Algebra.IsAlgebraic.isAlgebraic x`. Establish `h2 : IsAlgebraic ℤ x` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ I.E).2 h1`. Take `⟨y, hy, hi⟩` from `h2.exists_integral_multiple`. Conclude with `⟨y, hy, by rwa [zsmul_eq_mul] at hi⟩`.
-/
theorem int_mul_of (x : I.E) : ∃ m : ℤ, m ≠ 0 ∧ IsIntegral ℤ ((m : I.E) * x) := by
  have h1 : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
  have h2 : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ I.E).2 h1
  obtain ⟨y, hy, hi⟩ := h2.exists_integral_multiple
  exact ⟨y, hy, by rwa [zsmul_eq_mul] at hi⟩

/- English proof (translation)
Set `b0` to `Module.finBasis I.F I.E`. Use `choose n hn0 hnI using fun i => int_mul_of I (b0 i)`. Use `⟨b0.isUnitSMul (w := fun i => ((n i : ℤ) : I.F)) (fun i => (Int.cast_ne_zero.2 (hn0 i)).isUnit), fun i => ?_⟩` and prove the remaining obligations. Establish `: b0.isUnitSMul (w` using `fun i => ((n i : ℤ) : I.F)) (fun i => (Int.cast_ne_zero.2 (hn0 i)).isUnit) i = ((n i : ℤ) : I.E) * b0 i := by`. Simplify using `only [Module.Basis.isUnitSMul_apply, Algebra.smul_def, map_intCast]`.

Rewrite using `[this]`. Conclude with `hnI i`.
-/
theorem intBasis : ∃ b : Module.Basis (Fin (Module.finrank I.F I.E)) I.F I.E, ∀ i, IsIntegral ℤ (b i) := by
  classical
  let b0 := Module.finBasis I.F I.E
  choose n hn0 hnI using fun i => int_mul_of I (b0 i)
  refine ⟨b0.isUnitSMul (w := fun i => ((n i : ℤ) : I.F)) (fun i => (Int.cast_ne_zero.2 (hn0 i)).isUnit), fun i => ?_⟩
  have : b0.isUnitSMul (w := fun i => ((n i : ℤ) : I.F)) (fun i => (Int.cast_ne_zero.2 (hn0 i)).isUnit) i =
      ((n i : ℤ) : I.E) * b0 i := by
    simp only [Module.Basis.isUnitSMul_apply, Algebra.smul_def, map_intCast]
  rw [this]; exact hnI i

def tForm : LinearMap.BilinForm I.F I.E := (LinearMap.mul I.F I.E).compr₂ (tlin I)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tForm_apply (y y' : I.E) : tForm I y y' = tlin I (y * y') := rfl

/- English proof (translation)
Apply `(algebraMap I.F I.E).injective` to reduce the goal to its premises. Establish `hc : star (algebraMap I.F I.E c) = algebraMap I.F I.E c` using `(I.cm.fixed _).2 ⟨c, rfl⟩`. Rewrite using `[tlin_spec, hc, map_mul, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tlin_alg (c : I.F) : tlin I (algebraMap I.F I.E c) = 2 * c := by
  apply (algebraMap I.F I.E).injective
  have hc : star (algebraMap I.F I.E c) = algebraMap I.F I.E c := (I.cm.fixed _).2 ⟨c, rfl⟩
  rw [tlin_spec, hc, map_mul, map_ofNat]; ring

/- English proof (translation)
Establish `h` using `hy (star y)`. Rewrite `h` using `[tForm_apply]`. Take `⟨c, hc⟩` from `(I.cm.fixed (y * star y)).1 (by rw [star_mul, star_star])`. Rewrite `h` using `[← hc, tlin_alg]`. Establish `hc0 : c = 0`.

Break down `mul_eq_zero.1 h with h2 | h2` into its components or cases. Conclude with `absurd h2 two_ne_zero`. Conclude with `h2`. Rewrite `hc` using `[hc0, map_zero]`. Break down `mul_eq_zero.1 hc.symm with h3 | h3` into its components or cases.

Conclude with `h3`. Conclude with `star_eq_zero.1 h3`.
-/
theorem tForm_sepL (y : I.E) (hy : ∀ y', tForm I y y' = 0) : y = 0 := by
  have h := hy (star y)
  rw [tForm_apply] at h
  obtain ⟨c, hc⟩ := (I.cm.fixed (y * star y)).1 (by rw [star_mul, star_star])
  rw [← hc, tlin_alg] at h
  have hc0 : c = 0 := by
    rcases mul_eq_zero.1 h with h2 | h2
    · exact absurd h2 two_ne_zero
    · exact h2
  rw [hc0, map_zero] at hc
  rcases mul_eq_zero.1 hc.symm with h3 | h3
  · exact h3
  · exact star_eq_zero.1 h3

/- English proof (translation)
Use `⟨fun y hy => tForm_sepL I y hy, fun y hy => tForm_sepL I y fun y' => ?_⟩` and prove the remaining obligations. Rewrite using `[tForm_apply, mul_comm, ← tForm_apply]`. Conclude with `hy y'`.
-/
theorem tForm_nondeg : (tForm I).Nondegenerate := by
  refine ⟨fun y hy => tForm_sepL I y hy, fun y hy => tForm_sepL I y fun y' => ?_⟩
  rw [tForm_apply, mul_comm, ← tForm_apply]; exact hy y'

variable (v : HeightOneSpectrum (𝓞 I.F))

/- English proof (translation)
Take `⟨b, hbI⟩` from `intBasis I`. Establish `hB` using `tForm_nondeg I`. Set `d` to `(tForm I).dualBasis hB b`. Establish `hrep : ∀ w : I.E ⊗[I.F] v.adicCompletion I.F, ∃ a : Fin (Module.finrank I.F I.E) → v.adicCompletion I.F, w = ∑ j, d j ⊗ₜ[I.F] a j`. Introduce `w`.

Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `tmul e a`. Use `⟨fun j => d.repr e j • a, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← d.sum_repr e]`.

Rewrite using `[TensorProduct.sum_tmul]`. Conclude with `Finset.sum_congr rfl fun j _ => TensorProduct.smul_tmul _ _ _`. Consider the case `add x y hx hy`. Take `⟨a, rfl⟩` from `hx`. Take `⟨a', rfl⟩` from `hy`.

Conclude with `⟨a + a', by simp [TensorProduct.tmul_add, Finset.sum_add_distrib]⟩`. Take `⟨a, rfl⟩` from `hrep z`. Establish `ha : ∀ i, a i = 0`. Introduce `i`. Set `bi : 𝓞 I.E` to `⟨b i, hbI i⟩`.

Establish `hbi : (bi : I.E) = b i` using `rfl`. Establish `h1` using `h bi`. Rewrite `h1` using `[Finset.mul_sum, map_sum]`. Simplify using `only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, trV_tmul, hbi] at h1`. Establish `e : ∀ j, tlin I (b i * d j) = if i = j then 1 else 0`.

Introduce `j`. Use `LinearMap.BilinForm.apply_dualBasis_left hB b j i` as an intermediate fact. Rewrite `this` using `[tForm_apply, mul_comm]`. Conclude with `this`. Simplify using `only [e, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h1`.

Conclude with `h1`. Simplify using `[ha]`.
-/
theorem trV_nondeg (z : I.E ⊗[I.F] v.adicCompletion I.F)
    (h : ∀ x : 𝓞 I.E, trV I v (((x : I.E) ⊗ₜ[I.F] (1 : v.adicCompletion I.F)) * z) = 0) : z = 0 := by
  classical
  obtain ⟨b, hbI⟩ := intBasis I
  have hB := tForm_nondeg I
  let d := (tForm I).dualBasis hB b
  have hrep : ∀ w : I.E ⊗[I.F] v.adicCompletion I.F,
      ∃ a : Fin (Module.finrank I.F I.E) → v.adicCompletion I.F, w = ∑ j, d j ⊗ₜ[I.F] a j := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul e a =>
      refine ⟨fun j => d.repr e j • a, ?_⟩
      conv_lhs => rw [← d.sum_repr e]
      rw [TensorProduct.sum_tmul]
      exact Finset.sum_congr rfl fun j _ => TensorProduct.smul_tmul _ _ _
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨a', rfl⟩ := hy
      exact ⟨a + a', by simp [TensorProduct.tmul_add, Finset.sum_add_distrib]⟩
  obtain ⟨a, rfl⟩ := hrep z
  have ha : ∀ i, a i = 0 := by
    intro i
    let bi : 𝓞 I.E := ⟨b i, hbI i⟩
    have hbi : (bi : I.E) = b i := rfl
    have h1 := h bi
    rw [Finset.mul_sum, map_sum] at h1
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, trV_tmul, hbi] at h1
    have e : ∀ j, tlin I (b i * d j) = if i = j then 1 else 0 := by
      intro j
      have := LinearMap.BilinForm.apply_dualBasis_left hB b j i
      rw [tForm_apply, mul_comm] at this
      exact this
    simp only [e, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h1
    exact h1
  simp [ha]

end Key

end TypedLoc

namespace TypedLoc

section Lat

open Formalism.MainNotions.S NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Formalism.BasicNotions Formalism.L2.SG.HidaSetting
open scoped TensorProduct

variable (I : AutInst)

/- English proof (translation)
Take `⟨s, hs⟩` from `I.L_fg`. Use `choose m hm0 hmI using fun (g : Fin I.n → I.E) (i : Fin I.n) => int_mul_of I (g i)`. Use `⟨∏ g ∈ s, ∏ i, m g i, Finset.prod_ne_zero_iff.2 fun g _ => Finset.prod_ne_zero_iff.2 fun i _ => hm0 g i, fun l hl => ?_⟩` and prove the remaining obligations. Rewrite `hl` using `[← hs]`. Proceed by induction on `hl using Submodule.span_induction with`.

Consider the case `mem g hg`. Introduce `i`. Establish `e : ((∏ g ∈ s, ∏ i, m g i : ℤ) : I.E) * g i = (((∏ g' ∈ s.erase g, ∏ i, m g' i) * ∏ j ∈ Finset.univ.erase i, m g j : ℤ) : I.E) * ((m g i : I.E) * g i)`. Rewrite using `[← Finset.mul_prod_erase _ _ hg, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `isIntegral_algebraMap.mul (hmI g i)`. Consider the case `zero => intro i`. Simplify using `using isIntegral_zero`.

Consider the case `add x y _ _ hx hy => intro i`. Rewrite using `[Pi.add_apply, mul_add]`. Conclude with `(hx i).add (hy i)`. Consider the case `smul o x _ hx`. Introduce `i`.

Establish `e : ((∏ g ∈ s, ∏ i, m g i : ℤ) : I.E) * (o • x) i = (o : I.E) * (((∏ g ∈ s, ∏ i, m g i : ℤ) : I.E) * x i)`. Rewrite using `[Pi.smul_apply, Algebra.smul_def]`. Express the relevant statement in the definitionally equal form `_ * ((o : I.E) * x i) = _`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `(RingOfIntegers.isIntegral_coe o).mul (hx i)`.
-/
theorem L_denom : ∃ c : ℤ, c ≠ 0 ∧ ∀ l ∈ I.L, ∀ i, IsIntegral ℤ ((c : I.E) * l i) := by
  classical
  obtain ⟨s, hs⟩ := I.L_fg
  choose m hm0 hmI using fun (g : Fin I.n → I.E) (i : Fin I.n) => int_mul_of I (g i)
  refine ⟨∏ g ∈ s, ∏ i, m g i, Finset.prod_ne_zero_iff.2 fun g _ => Finset.prod_ne_zero_iff.2 fun i _ => hm0 g i,
    fun l hl => ?_⟩
  rw [← hs] at hl
  induction hl using Submodule.span_induction with
  | mem g hg =>
    intro i
    have e : ((∏ g ∈ s, ∏ i, m g i : ℤ) : I.E) * g i =
        (((∏ g' ∈ s.erase g, ∏ i, m g' i) * ∏ j ∈ Finset.univ.erase i, m g j : ℤ) : I.E) * ((m g i : I.E) * g i) := by
      rw [← Finset.mul_prod_erase _ _ hg, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      push_cast; ring
    rw [e]
    exact isIntegral_algebraMap.mul (hmI g i)
  | zero => intro i; simpa using isIntegral_zero
  | add x y _ _ hx hy => intro i; rw [Pi.add_apply, mul_add]; exact (hx i).add (hy i)
  | smul o x _ hx =>
    intro i
    have e : ((∏ g ∈ s, ∏ i, m g i : ℤ) : I.E) * (o • x) i = (o : I.E) * (((∏ g ∈ s, ∏ i, m g i : ℤ) : I.E) * x i) := by
      rw [Pi.smul_apply, Algebra.smul_def]
      change _ * ((o : I.E) * x i) = _
      ring
    rw [e]
    exact (RingOfIntegers.isIntegral_coe o).mul (hx i)

/- English proof (translation)
Take `⟨c1, hc1, h1⟩` from `L_denom I`. Use `⟨c1, hc1, fun w hw => ?_⟩` and prove the remaining obligations. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem g hg`. Take `⟨⟨l, hl⟩, rfl⟩` from `hg`.

Introduce `i`. Rewrite using `[← map_mul]`. Conclude with `Subring.subset_closure (Or.inl ⟨⟨_, ⟨⟨_, h1 l hl i⟩, rfl⟩⟩, rfl⟩)`. Consider the case `zero => intro i`. Simplify using the standard rewrite rules.

Consider the case `add x y _ _ hx hy => intro i`. Rewrite using `[Pi.add_apply, mul_add]`. Conclude with `add_mem (hx i) (hy i)`. Consider the case `smul r x _ hx`. Introduce `i`.

Establish `e : Formalism.UG.inclE (F` using `I.F) (Af I.F) (c1 : I.E) * (r • x) i = (r : I.E ⊗[I.F] Af I.F) * (Formalism.UG.inclE (F := I.F) (Af I.F) (c1 : I.E) * x i) := by`. Rewrite using `[Pi.smul_apply, Subring.smul_def, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `mul_mem r.2 (hx i)`.
-/
theorem Lf_int : ∃ c : ℤ, c ≠ 0 ∧ ∀ w ∈ I.Lf, ∀ i,
    Formalism.UG.inclE (F := I.F) (Af I.F) (c : I.E) * w i ∈ IntAf I.F I.E := by
  obtain ⟨c1, hc1, h1⟩ := L_denom I
  refine ⟨c1, hc1, fun w hw => ?_⟩
  induction hw using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨⟨l, hl⟩, rfl⟩ := hg
    intro i
    rw [← map_mul]
    exact Subring.subset_closure (Or.inl ⟨⟨_, ⟨⟨_, h1 l hl i⟩, rfl⟩⟩, rfl⟩)
  | zero => intro i; simp
  | add x y _ _ hx hy => intro i; rw [Pi.add_apply, mul_add]; exact add_mem (hx i) (hy i)
  | smul r x _ hx =>
    intro i
    have e : Formalism.UG.inclE (F := I.F) (Af I.F) (c1 : I.E) * (r • x) i =
        (r : I.E ⊗[I.F] Af I.F) * (Formalism.UG.inclE (F := I.F) (Af I.F) (c1 : I.E) * x i) := by
      rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul]; ring
    rw [e]
    exact mul_mem r.2 (hx i)

/- English proof (translation)
Apply the tactic sequence `apply _root_.UpperTheory.Reformulated.B.ModuliIntegralCharts.single_mem <;> assumption`.
-/
theorem single_mem (i : Fin I.n) : ∃ N : ℤ, N ≠ 0 ∧ (Pi.single i (N : I.E) : Fin I.n → I.E) ∈ I.L :=
  by apply _root_.UpperTheory.Reformulated.B.ModuliIntegralCharts.single_mem <;> assumption

end Lat

end TypedLoc

namespace TypedLoc

section Key2

open Formalism.MainNotions.S NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Formalism.BasicNotions Formalism.L2.SG.HidaSetting
open scoped TensorProduct

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (v : HeightOneSpectrum (𝓞 X.B.I.F))

/- English proof (translation)
Establish `h1` using `X.n_eq`. Establish `h2` using `Formalism.BasicNotions.Ranks.r_eq (R := D.R)`. Establish `h3` using `D.R.two_le_m`. Use linear arithmetic over natural numbers and integers.
-/
theorem n_pos' : 1 ≤ X.B.I.n := by
  have h1 := X.n_eq
  have h2 := Formalism.BasicNotions.Ranks.r_eq (R := D.R)
  have h3 := D.R.two_le_m
  omega

abbrev eV : X.B.I.E ⊗[X.B.I.F] v.adicCompletion X.B.I.F := Formalism.UG.prV (E := X.B.I.E) v X.ew

/- English proof (translation)
Rewrite using `[← map_mul, X.ew_idem]`.
-/
theorem eV_idem : eV X v * eV X v = eV X v := by rw [← map_mul, X.ew_idem]

/- English proof (translation)
Rewrite using `[← prV_sigA, ← map_mul, X.ew_orth, map_zero]`.
-/
theorem eV_orth : eV X v * sigV X.B.I v (eV X v) = 0 := by
  rw [← prV_sigA, ← map_mul, X.ew_orth, map_zero]

/- English proof (translation)
Rewrite using `[← map_mul, eV_idem]`.
-/
theorem sV_idem : sigV X.B.I v (eV X v) * sigV X.B.I v (eV X v) = sigV X.B.I v (eV X v) := by
  rw [← map_mul, eV_idem]

/- English proof (translation)
Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem y hy => exact hy`. Consider the case `zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩`. Consider the case `add a b _ _ ha hb`. Take `⟨x, hx, rfl⟩` from `ha`.

Take `⟨x', hx', rfl⟩` from `hb`. Conclude with `⟨x + x', add_mem hx hx', (smul_add _ _ _).symm⟩`. Consider the case `smul r a _ ha`. Take `⟨x, hx, rfl⟩` from `ha`. Use `⟨r • x, X.B.I.Lf.smul_mem r hx, ?_⟩` and prove the remaining obligations.

Rewrite using `[Subring.smul_def, Subring.smul_def, smul_smul, smul_smul, mul_comm]`.
-/
theorem mL_smul {w : VA X.B.I} (hw : w ∈ mL X.B.I X.B.g) :
    ∃ x ∈ X.B.I.Lf, w = ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x := by
  induction hw using Submodule.span_induction with
  | mem y hy => exact hy
  | zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩
  | add a b _ _ ha hb =>
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨x', hx', rfl⟩ := hb
    exact ⟨x + x', add_mem hx hx', (smul_add _ _ _).symm⟩
  | smul r a _ ha =>
    obtain ⟨x, hx, rfl⟩ := ha
    refine ⟨r • x, X.B.I.Lf.smul_mem r hx, ?_⟩
    rw [Subring.smul_def, Subring.smul_def, smul_smul, smul_smul, mul_comm]

abbrev Wg : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F := 1 - X.ew - sigA X.B.I X.ew

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => exact ⟨y, hy, by simp⟩`. Consider the case `succ k ih`. Take `⟨x, hx, hxk⟩` from `ih`. Take `⟨x', hx', hx'e⟩` from `mL_smul X (X.ew_full x hx)`.

Use `⟨x', hx', ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ', mul_smul, hxk, smul_smul, mul_comm, ← smul_smul, hx'e, smul_smul, ← pow_succ]`.
-/
theorem W_pow {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) (k : ℕ) :
    ∃ x ∈ X.B.I.Lf, (Wg X ^ k) • y = ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ^ k • x := by
  induction k with
  | zero => exact ⟨y, hy, by simp⟩
  | succ k ih =>
    obtain ⟨x, hx, hxk⟩ := ih
    obtain ⟨x', hx', hx'e⟩ := mL_smul X (X.ew_full x hx)
    refine ⟨x', hx', ?_⟩
    rw [pow_succ', mul_smul, hxk, smul_smul, mul_comm, ← smul_smul, hx'e, smul_smul, ← pow_succ]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem prV_inclE (a : X.B.I.E) :
    Formalism.UG.prV (E := X.B.I.E) v (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) a) = a ⊗ₜ[X.B.I.F] (1 : v.adicCompletion X.B.I.F) := rfl

/- English proof (translation)
Rewrite using `[← map_natCast (Algebra.TensorProduct.includeRight (R := X.B.I.F) (A := X.B.I.E) (B := v.adicCompletion X.B.I.F))]`. Both sides reduce to the same expression.
-/
theorem natCast_A (m : ℕ) : ((m : ℕ) : X.B.I.E ⊗[X.B.I.F] v.adicCompletion X.B.I.F) =
    (1 : X.B.I.E) ⊗ₜ[X.B.I.F] ((m : ℕ) : v.adicCompletion X.B.I.F) := by
  rw [← map_natCast (Algebra.TensorProduct.includeRight (R := X.B.I.F) (A := X.B.I.E)
    (B := v.adicCompletion X.B.I.F))]
  rfl

abbrev fV : X.B.I.E ⊗[X.B.I.F] v.adicCompletion X.B.I.F := 1 - eV X v - sigV X.B.I v (eV X v)

/- English proof (translation)
Rewrite using `[map_sub, map_sub, map_one, prV_sigA]`.
-/
theorem projection_w_eq_local_f : Formalism.UG.prV (E := X.B.I.E) v (Wg X) = fV X v := by
  rw [map_sub, map_sub, map_one, prV_sigA]

/- English proof (translation)
Establish `h1` using `eV_idem X v`. Establish `h2` using `sV_idem X v`. Establish `h3` using `eV_orth X v`. Take the linear combination `h1 + h2 + 2 * h3`.
-/
theorem fV_idem : fV X v * fV X v = fV X v := by
  have h1 := eV_idem X v
  have h2 := sV_idem X v
  have h3 := eV_orth X v
  linear_combination h1 + h2 + 2 * h3

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rw [zero_add, pow_one]`. Consider the case `succ k ih => rw [pow_succ, ih, fV_idem]`.
-/
theorem fV_pow (k : ℕ) : fV X v ^ (k + 1) = fV X v := by
  induction k with
  | zero => rw [zero_add, pow_one]
  | succ k ih => rw [pow_succ, ih, fV_idem]

/- English proof (translation)
Take `⟨c1, hc1, hLf⟩` from `Lf_int X.B.I`. Set `i0 : Fin X.B.I.n` to `⟨0, n_pos' X⟩`. Take `⟨N, hN, hNL⟩` from `single_mem X.B.I i0`. Establish `hy0 : incl X.B.I (Pi.single i0 (N : X.B.I.E)) ∈ X.B.I.Lf` using `Submodule.subset_span ⟨⟨_, hNL⟩, rfl⟩`. Establish `hπ` using `gUnif_holds X v hv`.

Set `π : v.adicCompletion X.B.I.F` to `((X.B.g : ℕ) : v.adicCompletion X.B.I.F)`. Establish `hπO : π ∈ v.adicCompletionIntegers X.B.I.F`. Rewrite using `[mem_adicCompletionIntegers, hπ, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Evaluate the numerical expressions. Set `z : X.B.I.E ⊗[X.B.I.F] v.adicCompletion X.B.I.F` to `(((c1 * N : ℤ) : X.B.I.E) ⊗ₜ[X.B.I.F] (1 : v.adicCompletion X.B.I.F)) * fV X v`.

Establish `hzk : ∀ k : ℕ, ∃ t ∈ Formalism.UG.tensInt (F` using `X.B.I.F) (v.adicCompletion X.B.I.F) (Formalism.UG.intOE X.B.I.E) (v.adicCompletionIntegers X.B.I.F).toSubring, z = ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] v.adicCompletion X.B.I.F) ^ (k + 1) * t := by`. Introduce `k`. Take `⟨x, hx, hxe⟩` from `W_pow X hy0 (k + 1)`. Establish `hi` using `congrFun hxe i0`. Simplify using `only [Pi.smul_apply, smul_eq_mul, incl, Pi.single_eq_same] at hi`.

Use `⟨Formalism.UG.prV (E := X.B.I.E) v (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (c1 : X.B.I.E) * x i0), Formalism.UG.P.afsplit_prV_int v _ (hLf x hx i0), ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg (Formalism.UG.prV (E := X.B.I.E) v) (congrArg (fun w => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (c1 : X.B.I.E) * w) hi)`. Simplify using `only [map_mul, map_pow, map_natCast, projection_w_eq_local_f] at h2`. Rewrite `h2` using `[fV_pow]`. Use `show (((c1 * N : ℤ) : X.B.I.E) ⊗ₜ[X.B.I.F] (1 : v.adicCompletion X.B.I.F)) * fV X v = _`.

Rewrite `h2` using `[prV_inclE, prV_inclE]`. Establish `e1 : (((c1 * N : ℤ) : X.B.I.E) ⊗ₜ[X.B.I.F] (1 : v.adicCompletion X.B.I.F)) = ((c1 : X.B.I.E) ⊗ₜ[X.B.I.F] (1 : v.adicCompletion X.B.I.F)) * ((N : X.B.I.E) ⊗ₜ[X.B.I.F] (1 : v.adicCompletion X.B.I.F))`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one]`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite using `[e1, map_mul, prV_inclE]`. Take the linear combination `h2`. Establish `hz0 : z = 0`. Use `trV_nondeg X.B.I v z fun x => ?_` and prove the remaining obligations. Use `vdiv_zero X.B.I v hπ fun k => ?_` and prove the remaining obligations.

Take `⟨t, ht, hzt⟩` from `hzk k`. Establish `hxt : ((x : X.B.I.E) ⊗ₜ[X.B.I.F] (1 : v.adicCompletion X.B.I.F)) * t ∈ Formalism.UG.tensInt (F` using `X.B.I.F) (v.adicCompletion X.B.I.F) (Formalism.UG.intOE X.B.I.E) (v.adicCompletionIntegers X.B.I.F).toSubring := mul_mem (Subring.subset_closure (Or.inl ⟨⟨_, ⟨x, rfl⟩⟩, rfl⟩)) ht`. Use `⟨π * trV X.B.I v (((x : X.B.I.E) ⊗ₜ[X.B.I.F] (1 : v.adicCompletion X.B.I.F)) * t), mul_mem hπO (trV_intV X.B.I v hxt), ?_⟩` and prove the remaining obligations. Rewrite using `[hzt, natCast_A, Algebra.TensorProduct.tmul_pow, one_pow, mul_left_comm, trV_mul_tmul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hu : (((c1 * N : ℤ) : X.B.I.E)⁻¹ ⊗ₜ[X.B.I.F] (1 : v.adicCompletion X.B.I.F)) * (((c1 * N : ℤ) : X.B.I.E) ⊗ₜ[X.B.I.F] (1 : v.adicCompletion X.B.I.F)) = 1`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ (Int.cast_ne_zero.2 (mul_ne_zero hc1 hN)), mul_one]`. Both sides reduce to the same expression. Establish `hf0 : fV X v = 0`. Use `congrArg (fun w => (((c1 * N : ℤ) : X.B.I.E)⁻¹ ⊗ₜ[X.B.I.F] (1 : v.adicCompletion X.B.I.F)) * w) hz0` as an intermediate fact.

Simplify using `only [z, ← mul_assoc, hu, one_mul, mul_zero] at this`. Conclude with `this`. Establish `: (1 : X.B.I.E ⊗[X.B.I.F] v.adicCompletion X.B.I.F) - eV X v - sigV X.B.I v (eV X v) = 0` using `hf0`. Take the linear combination `-this`.
-/
theorem eV_add (hv : ((X.B.g : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal) :
    eV X v + sigV X.B.I v (eV X v) = 1 := by
  classical
  obtain ⟨c1, hc1, hLf⟩ := Lf_int X.B.I
  let i0 : Fin X.B.I.n := ⟨0, n_pos' X⟩
  obtain ⟨N, hN, hNL⟩ := single_mem X.B.I i0
  have hy0 : incl X.B.I (Pi.single i0 (N : X.B.I.E)) ∈ X.B.I.Lf := Submodule.subset_span ⟨⟨_, hNL⟩, rfl⟩
  have hπ := gUnif_holds X v hv
  let π : v.adicCompletion X.B.I.F := ((X.B.g : ℕ) : v.adicCompletion X.B.I.F)
  have hπO : π ∈ v.adicCompletionIntegers X.B.I.F := by
    rw [mem_adicCompletionIntegers, hπ, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
  let z : X.B.I.E ⊗[X.B.I.F] v.adicCompletion X.B.I.F :=
    (((c1 * N : ℤ) : X.B.I.E) ⊗ₜ[X.B.I.F] (1 : v.adicCompletion X.B.I.F)) * fV X v
  have hzk : ∀ k : ℕ, ∃ t ∈ Formalism.UG.tensInt (F := X.B.I.F) (v.adicCompletion X.B.I.F) (Formalism.UG.intOE X.B.I.E)
      (v.adicCompletionIntegers X.B.I.F).toSubring, z = ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] v.adicCompletion X.B.I.F) ^ (k + 1) * t := by
    intro k
    obtain ⟨x, hx, hxe⟩ := W_pow X hy0 (k + 1)
    have hi := congrFun hxe i0
    simp only [Pi.smul_apply, smul_eq_mul, incl, Pi.single_eq_same] at hi
    refine ⟨Formalism.UG.prV (E := X.B.I.E) v (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (c1 : X.B.I.E) * x i0),
      Formalism.UG.P.afsplit_prV_int v _ (hLf x hx i0), ?_⟩
    have h2 := congrArg (Formalism.UG.prV (E := X.B.I.E) v) (congrArg (fun w => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (c1 : X.B.I.E) * w) hi)
    simp only [map_mul, map_pow, map_natCast, projection_w_eq_local_f] at h2
    rw [fV_pow] at h2
    show (((c1 * N : ℤ) : X.B.I.E) ⊗ₜ[X.B.I.F] (1 : v.adicCompletion X.B.I.F)) * fV X v = _
    rw [prV_inclE, prV_inclE] at h2
    have e1 : (((c1 * N : ℤ) : X.B.I.E) ⊗ₜ[X.B.I.F] (1 : v.adicCompletion X.B.I.F)) =
        ((c1 : X.B.I.E) ⊗ₜ[X.B.I.F] (1 : v.adicCompletion X.B.I.F)) * ((N : X.B.I.E) ⊗ₜ[X.B.I.F] (1 : v.adicCompletion X.B.I.F)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]; push_cast; rfl
    rw [e1, map_mul, prV_inclE]
    linear_combination h2
  have hz0 : z = 0 := by
    refine trV_nondeg X.B.I v z fun x => ?_
    refine vdiv_zero X.B.I v hπ fun k => ?_
    obtain ⟨t, ht, hzt⟩ := hzk k
    have hxt : ((x : X.B.I.E) ⊗ₜ[X.B.I.F] (1 : v.adicCompletion X.B.I.F)) * t ∈
        Formalism.UG.tensInt (F := X.B.I.F) (v.adicCompletion X.B.I.F) (Formalism.UG.intOE X.B.I.E)
          (v.adicCompletionIntegers X.B.I.F).toSubring :=
      mul_mem (Subring.subset_closure (Or.inl ⟨⟨_, ⟨x, rfl⟩⟩, rfl⟩)) ht
    refine ⟨π * trV X.B.I v (((x : X.B.I.E) ⊗ₜ[X.B.I.F] (1 : v.adicCompletion X.B.I.F)) * t),
      mul_mem hπO (trV_intV X.B.I v hxt), ?_⟩
    rw [hzt, natCast_A, Algebra.TensorProduct.tmul_pow, one_pow, mul_left_comm, trV_mul_tmul]
    ring
  have hu : (((c1 * N : ℤ) : X.B.I.E)⁻¹ ⊗ₜ[X.B.I.F] (1 : v.adicCompletion X.B.I.F)) *
      (((c1 * N : ℤ) : X.B.I.E) ⊗ₜ[X.B.I.F] (1 : v.adicCompletion X.B.I.F)) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ (Int.cast_ne_zero.2 (mul_ne_zero hc1 hN)), mul_one]
    rfl
  have hf0 : fV X v = 0 := by
    have := congrArg (fun w => (((c1 * N : ℤ) : X.B.I.E)⁻¹ ⊗ₜ[X.B.I.F] (1 : v.adicCompletion X.B.I.F)) * w) hz0
    simp only [z, ← mul_assoc, hu, one_mul, mul_zero] at this
    exact this
  have : (1 : X.B.I.E ⊗[X.B.I.F] v.adicCompletion X.B.I.F) - eV X v - sigV X.B.I v (eV X v) = 0 := hf0
  linear_combination -this

end Key2

end TypedLoc

section Finals

open Formalism.MainNotions.S NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Formalism.BasicNotions Formalism.L2.SG.HidaSetting TypedLoc
open scoped TensorProduct

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

/- English proof (translation)
The claim follows from `eV_add X v hv`.
-/
theorem ew_split_holds (v : HeightOneSpectrum (𝓞 X.B.I.F)) (hv : ((X.B.g : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal) :
    Formalism.UG.prV (E := X.B.I.E) v X.ew + Formalism.UG.sigR X.B.I.cm.sig (v.adicCompletion X.B.I.F) (Formalism.UG.prV (E := X.B.I.E) v X.ew) = 1 :=
  eV_add X v hv

namespace TypedLoc

variable (v : HeightOneSpectrum (𝓞 X.B.I.F)) (hv : ((X.B.g : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal)

include hv

/- English proof (translation)
Establish `h1` using `add_sig X.B.I v (eV X v)`. Rewrite `h1` using `[eV_add X v hv, Algebra.TensorProduct.one_def]`. Conclude with `(one_tmul_inj X.B.I v h1).symm`.
-/
theorem trV_eV : trV X.B.I v (eV X v) = 1 := by
  have h1 := add_sig X.B.I v (eV X v)
  rw [eV_add X v hv, Algebra.TensorProduct.one_def] at h1
  exact (one_tmul_inj X.B.I v h1).symm

/- English proof (translation)
Establish `h1` using `add_sig X.B.I v (eV X v * x)`. Establish `h2` using `congrArg (fun w => eV X v * w) h1`. Simplify using `only [mul_add] at h2`. Establish `h3 : eV X v * sigV X.B.I v (eV X v * x) = 0`. Rewrite using `[map_mul, ← mul_assoc, eV_orth, zero_mul]`.

Rewrite `h2` using `[h3, add_zero, ← mul_assoc, eV_idem, mul_comm (eV X v) ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] _)]`. Conclude with `h2`.
-/
theorem eV_mul (x : X.B.I.E ⊗[X.B.I.F] v.adicCompletion X.B.I.F) :
    eV X v * x = ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] trV X.B.I v (eV X v * x)) * eV X v := by
  have h1 := add_sig X.B.I v (eV X v * x)
  have h2 := congrArg (fun w => eV X v * w) h1
  simp only [mul_add] at h2
  have h3 : eV X v * sigV X.B.I v (eV X v * x) = 0 := by
    rw [map_mul, ← mul_assoc, eV_orth, zero_mul]
  rw [h3, add_zero, ← mul_assoc, eV_idem, mul_comm (eV X v) ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] _)] at h2
  exact h2

def redV : X.B.I.E ⊗[X.B.I.F] v.adicCompletion X.B.I.F →+* v.adicCompletion X.B.I.F where
  toFun x := trV X.B.I v (eV X v * x)
  map_one' := by rw [mul_one]; exact trV_eV X v hv
  map_mul' x y := by
    show trV X.B.I v (eV X v * (x * y)) = trV X.B.I v (eV X v * x) * trV X.B.I v (eV X v * y)
    set t := trV X.B.I v (eV X v * x) with ht
    have h : eV X v * x = ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] t) * eV X v := eV_mul X v hv x
    rw [← mul_assoc, h, mul_assoc, trV_mul_tmul]
  map_zero' := by simp
  map_add' x y := by simp [mul_add]

end TypedLoc

/- English proof (translation)
Introduce `v hv`. Use `⟨TypedLoc.redV X v hv, ?_, fun c => ?_, fun x hx => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Use `show trV X.B.I v (eV X v * eV X v) = 1`. Rewrite using `[eV_idem]`. Conclude with `trV_eV X v hv`.

Use `show trV X.B.I v (eV X v * ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] c)) = c`. Rewrite using `[mul_comm, trV_mul_tmul, trV_eV X v hv, mul_one]`. Use `show trV X.B.I v (eV X v * x) ∈ _`. Conclude with `trV_intV X.B.I v (mul_mem (Formalism.UG.P.afsplit_prV_int v X.ew X.ew_int) hx)`. Conclude with `hx.symm.trans (eV_mul X v hv x)`.
-/
theorem redExists_holds : ∀ v : HeightOneSpectrum (𝓞 X.B.I.F), ((X.B.g : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
    ∃ r : X.B.I.E ⊗[X.B.I.F] v.adicCompletion X.B.I.F →+* v.adicCompletion X.B.I.F,
      r (Formalism.UG.prV (E := X.B.I.E) v X.ew) = 1 ∧
      (∀ c : v.adicCompletion X.B.I.F, r ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] c) = c) ∧
      (∀ x ∈ Formalism.UG.tensInt (F := X.B.I.F) (v.adicCompletion X.B.I.F) (Formalism.UG.intOE X.B.I.E)
          (v.adicCompletionIntegers X.B.I.F).toSubring, r x ∈ v.adicCompletionIntegers X.B.I.F) ∧
      ∀ x, Formalism.UG.prV (E := X.B.I.E) v X.ew * x = x →
        x = ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] r x) * Formalism.UG.prV (E := X.B.I.E) v X.ew := by
  intro v hv
  refine ⟨TypedLoc.redV X v hv, ?_, fun c => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · show trV X.B.I v (eV X v * eV X v) = 1
    rw [eV_idem]; exact trV_eV X v hv
  · show trV X.B.I v (eV X v * ((1 : X.B.I.E) ⊗ₜ[X.B.I.F] c)) = c
    rw [mul_comm, trV_mul_tmul, trV_eV X v hv, mul_one]
  · show trV X.B.I v (eV X v * x) ∈ _
    exact trV_intV X.B.I v (mul_mem (Formalism.UG.P.afsplit_prV_int v X.ew X.ew_int) hx)
  · exact hx.symm.trans (eV_mul X v hv x)

/- English proof (translation)
Introduce `v hv`. Set `c` to `Algebra.TensorProduct.comm X.B.I.F X.B.I.E (v.adicCompletion X.B.I.F)`. Establish `hnt : (1 : X.B.I.E ⊗[X.B.I.F] v.adicCompletion X.B.I.F) ≠ 0`. Introduce `h`. Use `congrArg (trV X.B.I v) h` as an intermediate fact.

Rewrite `this` using `[Algebra.TensorProduct.one_def, trV_one_tmul, mul_one, map_zero]`. Establish `h2 : (2 : v.adicCompletion X.B.I.F) ≠ 0`. Introduce `h`. Apply `(two_ne_zero : (2 : X.B.I.F) ≠ 0)` to reduce the goal to its premises. Apply `(algebraMap X.B.I.F (v.adicCompletion X.B.I.F)).injective` to reduce the goal to its premises.

Rewrite using `[map_ofNat, h, map_zero]`. Conclude with `h2 this`. Use `⟨c (eV X v), by rw [← map_mul, eV_idem], fun h0 => ?_, fun h1 => ?_⟩` and prove the remaining obligations. Establish `he : eV X v = 0`. Use `congrArg c.symm h0` as an intermediate fact.

Simplify using `using this`. Use `eV_add X v hv` as an intermediate fact. Rewrite `this` using `[he, map_zero, add_zero]`. Conclude with `hnt this.symm`. Establish `he : eV X v = 1`.

Use `congrArg c.symm h1` as an intermediate fact. Simplify using `using this`. Use `eV_orth X v` as an intermediate fact. Rewrite `this` using `[he, map_one, mul_one]`. Conclude with `hnt this`.
-/
theorem split_at_g : ∀ v : HeightOneSpectrum (𝓞 X.B.I.F), ((X.B.g : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
    ∃ x : v.adicCompletion X.B.I.F ⊗[X.B.I.F] X.B.I.E, x * x = x ∧ x ≠ 0 ∧ x ≠ 1 := by
  intro v hv
  let c := Algebra.TensorProduct.comm X.B.I.F X.B.I.E (v.adicCompletion X.B.I.F)
  have hnt : (1 : X.B.I.E ⊗[X.B.I.F] v.adicCompletion X.B.I.F) ≠ 0 := by
    intro h
    have := congrArg (trV X.B.I v) h
    rw [Algebra.TensorProduct.one_def, trV_one_tmul, mul_one, map_zero] at this
    have h2 : (2 : v.adicCompletion X.B.I.F) ≠ 0 := by
      intro h
      apply (two_ne_zero : (2 : X.B.I.F) ≠ 0)
      apply (algebraMap X.B.I.F (v.adicCompletion X.B.I.F)).injective
      rw [map_ofNat, h, map_zero]
    exact h2 this
  refine ⟨c (eV X v), by rw [← map_mul, eV_idem], fun h0 => ?_, fun h1 => ?_⟩
  · have he : eV X v = 0 := by
      have := congrArg c.symm h0
      simpa using this
    have := eV_add X v hv
    rw [he, map_zero, add_zero] at this
    exact hnt this.symm
  · have he : eV X v = 1 := by
      have := congrArg c.symm h1
      simpa using this
    have := eV_orth X v
    rw [he, map_one, mul_one] at this
    exact hnt this

end Finals

/- English proof (translation)
Introduce `F E _ _ _ _ _ p hp h`. Use `⟨fun v hv => ⟨TypedLoc.tower_card F E hp h v hv, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `e : ((p : ℕ) : v.adicCompletion F) = (((p : ℕ) : F) : v.adicCompletion F)`. Rewrite using `[← map_natCast (algebraMap F (v.adicCompletion F))]`. Both sides reduce to the same expression.

Rewrite using `[e, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`. Establish `e2 : ((p : ℕ) : F) = algebraMap (NumberField.RingOfIntegers F) F ((p : ℕ) : NumberField.RingOfIntegers F)`. Rewrite using `[map_natCast]`. Rewrite using `[e2, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `TypedLoc.tower_val F E hp h v hv`.

Use `TypedLoc.span_p_maximal hp` as an intermediate fact. Establish `hq0` using `TypedLoc.span_p_ne_bot hp`. Establish `hsum` using `Ideal.sum_ramification_inertia (NumberField.RingOfIntegers F) ℚ F hq0`. Establish `hone : ∀ P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (NumberField.RingOfIntegers F), (Ideal.span {(p : ℤ)}).ramificationIdx' P * (Ideal.span {(p : ℤ)}).inertiaDeg' P = 1`. Introduce `P hP`.

Rewrite `hP` using `[IsDedekindDomain.mem_primesOverFinset_iff hq0, TypedLoc.primesOver_eq F hp]`. Take `⟨v, hv, rfl⟩` from `hP`. Take `⟨h1, h2⟩` from `TypedLoc.tower_ef F E hp h v hv`. Rewrite using `[h1, h2]`. Rewrite `hsum` using `[Finset.sum_congr rfl hone, Finset.sum_const, smul_eq_mul, mul_one]`.

Rewrite using `[← hsum, ← Set.ncard_coe_finset, IsDedekindDomain.coe_primesOverFinset hq0, TypedLoc.primesOver_eq F hp]`. Conclude with `(Set.ncard_image_of_injective _ (fun v w hvw => IsDedekindDomain.HeightOneSpectrum.ext hvw)).symm`.
-/
theorem splitPrimeLoc_holds : Formalism.L2.SG.Pf.SatGramLoc.SplitPrimeLoc := by
  intro F E _ _ _ _ _ p hp h
  refine ⟨fun v hv => ⟨TypedLoc.tower_card F E hp h v hv, ?_⟩, ?_⟩
  · have e : ((p : ℕ) : v.adicCompletion F) = (((p : ℕ) : F) : v.adicCompletion F) := by
      rw [← map_natCast (algebraMap F (v.adicCompletion F))]; rfl
    rw [e, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    have e2 : ((p : ℕ) : F) = algebraMap (NumberField.RingOfIntegers F) F ((p : ℕ) : NumberField.RingOfIntegers F) := by
      rw [map_natCast]
    rw [e2, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact TypedLoc.tower_val F E hp h v hv
  · classical
    have := TypedLoc.span_p_maximal hp
    have hq0 := TypedLoc.span_p_ne_bot hp
    have hsum := Ideal.sum_ramification_inertia (NumberField.RingOfIntegers F) ℚ F hq0
    have hone : ∀ P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (NumberField.RingOfIntegers F),
        (Ideal.span {(p : ℤ)}).ramificationIdx' P * (Ideal.span {(p : ℤ)}).inertiaDeg' P = 1 := by
      intro P hP
      rw [IsDedekindDomain.mem_primesOverFinset_iff hq0, TypedLoc.primesOver_eq F hp] at hP
      obtain ⟨v, hv, rfl⟩ := hP
      obtain ⟨h1, h2⟩ := TypedLoc.tower_ef F E hp h v hv
      rw [h1, h2]
    rw [Finset.sum_congr rfl hone, Finset.sum_const, smul_eq_mul, mul_one] at hsum
    rw [← hsum, ← Set.ncard_coe_finset, IsDedekindDomain.coe_primesOverFinset hq0, TypedLoc.primesOver_eq F hp]
    exact (Set.ncard_image_of_injective _ (fun v w hvw => IsDedekindDomain.HeightOneSpectrum.ext hvw)).symm

end Formalism.L2.SG.Pf
