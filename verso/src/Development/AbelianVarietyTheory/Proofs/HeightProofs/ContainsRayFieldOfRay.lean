import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RayFieldTheta

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldSize.RayNorm

open NumberField IsDedekindDomain GlobalTheory.NT
open scoped Pointwise

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/- English proof (translation)
Unfold `heckeIdeal`. Rewrite using `[finprod_eq_single _ 𝔮]`. Rewrite using `[Associates.mk_pow, Associates.count_pow (Associates.mk_ne_zero.mpr 𝔮.ne_bot) (HeightOneSpectrum.associates_irreducible 𝔮), Associates.count_self (HeightOneSpectrum.associates_irreducible 𝔮), mul_one]`. Introduce `𝔭 h𝔭`. Establish `hne : Associates.mk 𝔭.asIdeal ≠ Associates.mk 𝔮.asIdeal`.

Introduce `h`. Apply `h𝔭` to reduce the goal to its premises. Rewrite `h` using `[Associates.mk_eq_mk_iff_associated, associated_iff_eq]`. Conclude with `HeightOneSpectrum.ext h`. Rewrite using `[Associates.mk_pow, Associates.count_pow (Associates.mk_ne_zero.mpr 𝔮.ne_bot) (HeightOneSpectrum.associates_irreducible 𝔭), Associates.count_eq_zero_of_ne (HeightOneSpectrum.associates_irreducible 𝔭) (HeightOneSpectrum.associates_irreducible 𝔮) hne, mul_zero, pow_zero]`.
-/
theorem heckeIdeal_prime_pow (χ : (L ≃ₐ[K] L) →* ℂˣ) (𝔮 : HeightOneSpectrum (𝓞 K)) (f : ℕ) :
    heckeIdeal L χ (𝔮.asIdeal ^ f) = heckeVal L χ 𝔮 ^ f := by
  unfold heckeIdeal
  rw [finprod_eq_single _ 𝔮]
  · rw [Associates.mk_pow, Associates.count_pow (Associates.mk_ne_zero.mpr 𝔮.ne_bot)
      (HeightOneSpectrum.associates_irreducible 𝔮), Associates.count_self
      (HeightOneSpectrum.associates_irreducible 𝔮), mul_one]
  · intro 𝔭 h𝔭
    have hne : Associates.mk 𝔭.asIdeal ≠ Associates.mk 𝔮.asIdeal := by
      intro h
      apply h𝔭
      rw [Associates.mk_eq_mk_iff_associated, associated_iff_eq] at h
      exact HeightOneSpectrum.ext h
    rw [Associates.mk_pow, Associates.count_pow (Associates.mk_ne_zero.mpr 𝔮.ne_bot)
      (HeightOneSpectrum.associates_irreducible 𝔭), Associates.count_eq_zero_of_ne
      (HeightOneSpectrum.associates_irreducible 𝔭) (HeightOneSpectrum.associates_irreducible 𝔮) hne,
      mul_zero, pow_zero]

omit [NumberField K] [NumberField L] in

/- English proof (translation)
Establish `h' : ∀ y : 𝓞 L, Ideal.Quotient.mk P (σ • y) = Ideal.Quotient.mk P y ^ q` using `fun y => by`. Rewrite using `[← map_pow, Ideal.Quotient.eq]`. Conclude with `h y`. Proceed by induction on `k with`. Consider the case `zero => simp`.

Consider the case `succ k ih`. Rewrite `ih`, the goal using `[← Ideal.Quotient.eq]`. Rewrite using `[pow_succ' σ k, mul_smul, h', ih, ← map_pow, ← pow_mul, ← pow_succ]`.
-/
theorem pow_smul_sub_mem (P : Ideal (𝓞 L)) {σ : L ≃ₐ[K] L} {q : ℕ} (h : ∀ x : 𝓞 L, σ • x - x ^ q ∈ P) (k : ℕ)
    (x : 𝓞 L) : σ ^ k • x - x ^ q ^ k ∈ P := by
  have h' : ∀ y : 𝓞 L, Ideal.Quotient.mk P (σ • y) = Ideal.Quotient.mk P y ^ q := fun y => by
    rw [← map_pow, Ideal.Quotient.eq]
    exact h y
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Ideal.Quotient.eq] at ih ⊢
    rw [pow_succ' σ k, mul_smul, h', ih, ← map_pow, ← pow_mul, ← pow_succ]

/- English proof (translation)
Unfold `UnramIn at hu`. Establish `hq : Nat.card (𝓞 K ⧸ P.asIdeal.under (𝓞 K)) = Ideal.absNorm 𝔭.asIdeal`. Rewrite using `[← hPo.over, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Establish `hfin : Finite (𝓞 L ⧸ P.asIdeal)` using `(Ideal.absNorm_ne_zero_iff _).mp (fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0))`. Take `⟨σ, hσ⟩` from `IsArithFrobAt.exists_of_isInvariant (𝓞 K) (L ≃ₐ[K] L) P.asIdeal`.

Establish `hσ' : ∀ x : 𝓞 L, σ • x - x ^ Ideal.absNorm 𝔭.asIdeal ∈ P.asIdeal` using `fun x => by`. Establish `h1` using `hσ x`. Rewrite `h1` using `[hq]`. Conclude with `h1`. Use `⟨σ, ⟨P.asIdeal, P.isPrime, hPo, hσ'⟩, ?_⟩` and prove the remaining obligations.

Establish `hfix : ∀ x : 𝓞 L, σ ^ f • x - x ∈ P.asIdeal` using `fun x => by`. Establish `h1` using `pow_smul_sub_mem P.asIdeal hσ' f x`. Establish `h2 : x ^ Ideal.absNorm 𝔭.asIdeal ^ f - x ∈ P.asIdeal`. Set `_` to `Ideal.Quotient.field P.asIdeal`. Establish `_` using `Fintype.ofFinite (𝓞 L ⧸ P.asIdeal)`.

Rewrite using `[← hf, ← Ideal.Quotient.eq, map_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, FiniteField.pow_card]`. Establish `h3` using `P.asIdeal.add_mem h1 h2`. Rewrite `h3` using `[sub_add_sub_cancel]`. Conclude with `h3`. Apply `hu` to reduce the goal to its premises.

Conclude with `⟨P.asIdeal, P.isPrime, hPo, hfix⟩`.
-/
theorem exists_frob_pow_eq_one [IsGalois K L] (𝔭 : HeightOneSpectrum (𝓞 K)) (hu : UnramIn L 𝔭)
    (P : HeightOneSpectrum (𝓞 L)) [hPo : P.asIdeal.LiesOver 𝔭.asIdeal] {f : ℕ}
    (hf : Ideal.absNorm P.asIdeal = Ideal.absNorm 𝔭.asIdeal ^ f) :
    ∃ σ : L ≃ₐ[K] L, IsFrob L 𝔭 σ ∧ σ ^ f = 1 := by
  unfold UnramIn at hu
  have hq : Nat.card (𝓞 K ⧸ P.asIdeal.under (𝓞 K)) = Ideal.absNorm 𝔭.asIdeal := by
    rw [← hPo.over, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hfin : Finite (𝓞 L ⧸ P.asIdeal) :=
    (Ideal.absNorm_ne_zero_iff _).mp (fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0))
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 K) (L ≃ₐ[K] L) P.asIdeal
  have hσ' : ∀ x : 𝓞 L, σ • x - x ^ Ideal.absNorm 𝔭.asIdeal ∈ P.asIdeal := fun x => by
    have h1 := hσ x
    rw [hq] at h1
    exact h1
  refine ⟨σ, ⟨P.asIdeal, P.isPrime, hPo, hσ'⟩, ?_⟩
  have hfix : ∀ x : 𝓞 L, σ ^ f • x - x ∈ P.asIdeal := fun x => by
    have h1 := pow_smul_sub_mem P.asIdeal hσ' f x
    have h2 : x ^ Ideal.absNorm 𝔭.asIdeal ^ f - x ∈ P.asIdeal := by
      let _ := Ideal.Quotient.field P.asIdeal
      have _ := Fintype.ofFinite (𝓞 L ⧸ P.asIdeal)
      rw [← hf, ← Ideal.Quotient.eq, map_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply,
        Nat.card_eq_fintype_card, FiniteField.pow_card]
    have h3 := P.asIdeal.add_mem h1 h2
    rw [sub_add_sub_cancel] at h3
    exact h3
  apply hu
  exact ⟨P.asIdeal, P.isPrime, hPo, hfix⟩

/- English proof (translation)
Take `⟨α, β, hr, hI⟩` from `h`. Unfold `RayPair at hr`. Take `⟨-, hβ, -, hβc, hαβ, -⟩` from `hr`. Establish `hα : α ∈ I * Ideal.span {β}`. Rewrite using `[hI]`.

Conclude with `Ideal.mem_span_singleton_self α`. Take `⟨π, -, hπ⟩` from `Submodule.mem_mul_span_singleton.mp hα`. Establish `hb0 : Ideal.span {β} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hβ`.

Use `⟨π, ?_, ?_⟩` and prove the remaining obligations. Apply `mul_right_cancel₀ hb0` to reduce the goal to its premises. Rewrite using `[hI, Ideal.span_singleton_mul_span_singleton, hπ]`. Establish `hq : β * (π - 1) ∈ 𝔮`. Establish `e : β * (π - 1) = α - β`.

Rewrite using `[← hπ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `hαβ`. Establish `h1 : (1 : 𝓞 K) ∈ Ideal.span {β} ⊔ 𝔮`.

Rewrite using `[Ideal.isCoprime_iff_sup_eq.mp hβc]`. Conclude with `Submodule.mem_top`. Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.mp h1`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.mp hy`. Establish `e2 : π - 1 = c * (β * (π - 1)) + (π - 1) * z`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e2]`. Conclude with `𝔮.add_mem (𝔮.mul_mem_left c hq) (𝔮.mul_mem_left (π - 1) hz)`.
-/
theorem exists_gen_of_ray {𝔮 I : Ideal (𝓞 K)}
    (h : ∃ α β : 𝓞 K, RayPair 𝔮 α β ∧ I * Ideal.span {β} = Ideal.span {α}) :
    ∃ π : 𝓞 K, I = Ideal.span {π} ∧ π - 1 ∈ 𝔮 := by
  obtain ⟨α, β, hr, hI⟩ := h
  unfold RayPair at hr
  obtain ⟨-, hβ, -, hβc, hαβ, -⟩ := hr
  have hα : α ∈ I * Ideal.span {β} := by
    rw [hI]
    exact Ideal.mem_span_singleton_self α
  obtain ⟨π, -, hπ⟩ := Submodule.mem_mul_span_singleton.mp hα
  have hb0 : Ideal.span {β} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hβ
  refine ⟨π, ?_, ?_⟩
  · apply mul_right_cancel₀ hb0
    rw [hI, Ideal.span_singleton_mul_span_singleton, hπ]
  · have hq : β * (π - 1) ∈ 𝔮 := by
      have e : β * (π - 1) = α - β := by
        rw [← hπ]
        ring
      rw [e]
      exact hαβ
    have h1 : (1 : 𝓞 K) ∈ Ideal.span {β} ⊔ 𝔮 := by
      rw [Ideal.isCoprime_iff_sup_eq.mp hβc]
      exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h1
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    have e2 : π - 1 = c * (β * (π - 1)) + (π - 1) * z := by
      calc π - 1 = (π - 1) * (c * β + z) := by rw [hyz, mul_one]
        _ = c * (β * (π - 1)) + (π - 1) * z := by ring
    rw [e2]
    exact 𝔮.add_mem (𝔮.mul_mem_left c hq) (𝔮.mul_mem_left (π - 1) hz)

/- English proof (translation)
Unfold `UnramIn at hu`. Establish `hN0 : Ideal.absNorm Q ≠ 0`. Rewrite using `[hQf]`. Conclude with `pow_ne_zero f (fun h0 => 𝔭.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0))`. Establish `hQ0 : Q ≠ ⊥` using `fun h0 => hN0 (Ideal.absNorm_eq_zero_iff.mpr h0)`.

Establish `hfin : Finite (𝓞 L ⧸ Q)` using `(Ideal.absNorm_ne_zero_iff _).mp hN0`. Use `haveI : Q.IsMaximal := hQ.isMaximal hQ0`. Establish `hfix : ∀ x : 𝓞 L, τ ^ f • x - x ∈ Q` using `fun x => by`. Establish `h1` using `pow_smul_sub_mem Q hτ f x`. Establish `h2 : x ^ Ideal.absNorm 𝔭.asIdeal ^ f - x ∈ Q`.

Set `_` to `Ideal.Quotient.field Q`. Establish `_` using `Fintype.ofFinite (𝓞 L ⧸ Q)`. Rewrite using `[← hQf, ← Ideal.Quotient.eq, map_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, FiniteField.pow_card]`. Establish `h3` using `Q.add_mem h1 h2`. Rewrite `h3` using `[sub_add_sub_cancel]`.

Conclude with `h3`. Conclude with `hu _ ⟨Q, hQ, hQo, hfix⟩`.
-/
private theorem pow_residue_degree_eq_one_of_isFrobenius [IsGalois K L] (𝔭 : HeightOneSpectrum (𝓞 K)) (hu : UnramIn L 𝔭)
    (Q : Ideal (𝓞 L)) [hQ : Q.IsPrime] [hQo : Q.LiesOver 𝔭.asIdeal] {f : ℕ}
    (hQf : Ideal.absNorm Q = Ideal.absNorm 𝔭.asIdeal ^ f) (τ : L ≃ₐ[K] L)
    (hτ : ∀ x : 𝓞 L, τ • x - x ^ Ideal.absNorm 𝔭.asIdeal ∈ Q) : τ ^ f = 1 := by
  unfold UnramIn at hu
  have hN0 : Ideal.absNorm Q ≠ 0 := by
    rw [hQf]
    exact pow_ne_zero f (fun h0 => 𝔭.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0))
  have hQ0 : Q ≠ ⊥ := fun h0 => hN0 (Ideal.absNorm_eq_zero_iff.mpr h0)
  have hfin : Finite (𝓞 L ⧸ Q) := (Ideal.absNorm_ne_zero_iff _).mp hN0
  haveI : Q.IsMaximal := hQ.isMaximal hQ0
  have hfix : ∀ x : 𝓞 L, τ ^ f • x - x ∈ Q := fun x => by
    have h1 := pow_smul_sub_mem Q hτ f x
    have h2 : x ^ Ideal.absNorm 𝔭.asIdeal ^ f - x ∈ Q := by
      let _ := Ideal.Quotient.field Q
      have _ := Fintype.ofFinite (𝓞 L ⧸ Q)
      rw [← hQf, ← Ideal.Quotient.eq, map_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply,
        Nat.card_eq_fintype_card, FiniteField.pow_card]
    have h3 := Q.add_mem h1 h2
    rw [sub_add_sub_cancel] at h3
    exact h3
  exact hu _ ⟨Q, hQ, hQo, hfix⟩

/- English proof (translation)
Introduce `𝔓 h𝔓`. Use `haveI := 𝔓.isPrime`. Establish `hN : ((Ideal.absNorm 𝔓.asIdeal : ℕ) : 𝓞 K) ∈ 𝔓.asIdeal.comap (RingOfIntegers.mapRingHom (algebraMap K L))`. Rewrite using `[Ideal.mem_comap, map_natCast]`. Conclude with `Ideal.absNorm_mem _`.

Establish `hne : 𝔓.asIdeal.comap (RingOfIntegers.mapRingHom (algebraMap K L)) ≠ ⊥`. Introduce `h0`. Rewrite `hN` using `[h0, Ideal.mem_bot]`. Establish `h2` using `congrArg (algebraMap (𝓞 K) K) hN`. Rewrite `h2` using `[map_natCast, map_zero, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff]`.

Conclude with `𝔓.ne_bot h2`. Set `𝔭 : HeightOneSpectrum (𝓞 K)` to `⟨_, inferInstance, hne⟩`. Use `haveI : 𝔓.asIdeal.LiesOver 𝔭.asIdeal := ⟨rfl⟩`. Take `⟨f, hfdef⟩ : ∃ f, f = 𝔓.asIdeal.inertiaDeg (𝓞 K)` from `⟨_, rfl⟩`. Establish `hf : Ideal.absNorm 𝔓.asIdeal = Ideal.absNorm 𝔭.asIdeal ^ f`.

Rewrite using `[hfdef, Ideal.absNorm_pow_inertiaDeg]`. Establish `hn𝔭 : ((n : ℕ) : 𝓞 K) ∉ 𝔭.asIdeal`. Introduce `h`. Apply `h𝔓` to reduce the goal to its premises. Establish `h' : (RingOfIntegers.mapRingHom (algebraMap K L)) (n : 𝓞 K) ∈ 𝔓.asIdeal` using `h`.

Rewrite `h'` using `[map_natCast]`. Then use the resulting hypothesis. Establish `hu : UnramIn L 𝔭` using `hun 𝔭 (fun h => hn𝔭 (Ideal.dvd_span_singleton.mp h))`. Establish `hcop1 : IsCoprime 𝔭.asIdeal (Ideal.span {(n : 𝓞 K)})`. Rewrite using `[Ideal.isCoprime_iff_sup_eq]`. Assume the negation of the conclusion as `hne2`.

Establish `e` using `(𝔭.isMaximal).eq_of_le hne2 le_sup_left`. Establish `h2 : (n : 𝓞 K) ∈ 𝔭.asIdeal ⊔ Ideal.span {(n : 𝓞 K)}` using `Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)`. Rewrite `h2` using `[← e]`. Conclude with `hn𝔭 h2`. Establish `hI0 : 𝔭.asIdeal ^ f ≠ ⊥` using `pow_ne_zero f 𝔭.ne_bot`.

Establish `hχ : ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ (𝔭.asIdeal ^ f) = 1`. Introduce `χ`. Rewrite using `[heckeIdeal_prime_pow]`. Take `⟨σ0, hσ0, -⟩` from `exists_frob_pow_eq_one 𝔭 hu 𝔓 hf`. Establish `hc : (∀ σ : L ≃ₐ[K] L, InInertia L 𝔭 σ → χ σ = 1) ∧ ∃ σ, IsFrob L 𝔭 σ` using `⟨fun σ hσ => by rw [hu σ hσ, map_one], ⟨σ0, hσ0⟩⟩`.

Unfold `heckeVal`. Rewrite using `[dif_pos hc]`. Take `⟨Q, hQp, hQo, hQ⟩` from `hc.2.choose_spec`. Establish `hQf : Ideal.absNorm Q = Ideal.absNorm 𝔭.asIdeal ^ f`. Rewrite using `[hfdef, Ideal.inertiaDeg_eq_of_isGaloisGroup 𝔭.asIdeal 𝔓.asIdeal Q (L ≃ₐ[K] L), Ideal.absNorm_pow_inertiaDeg]`.

Establish `hτ` using `pow_residue_degree_eq_one_of_isFrobenius 𝔭 hu Q hQf _ hQ`. Establish `hχτ : χ hc.2.choose ^ f = 1` using `by rw [← map_pow, hτ, map_one]`. Rewrite using `[← Units.val_pow_eq_pow_val, hχτ, Units.val_one]`. Take `⟨α, β, hr, hI⟩` from `hart (𝔭.asIdeal ^ f) hI0 hcop1.pow_left hχ`. Take `⟨π, hπ, hπ1⟩` from `exists_gen_of_ray ⟨α, β, hr, hI⟩`.

Conclude with `⟨f, π, hf, hπ, Ideal.mem_span_singleton.mp hπ1⟩`.
-/
theorem containsRayField_of_ray [IsGalois K L] (n : ℕ)
    (hun : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ Ideal.span {(n : 𝓞 K)} → UnramIn L 𝔭)
    (hart : ∀ I : Ideal (𝓞 K), I ≠ ⊥ → IsCoprime I (Ideal.span {(n : 𝓞 K)}) →
      (∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ I = 1) →
        ∃ α β : 𝓞 K, RayPair (Ideal.span {(n : 𝓞 K)}) α β ∧ I * Ideal.span {β} = Ideal.span {α}) :
    GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (algebraMap K L) n := by
  intro 𝔓 h𝔓
  haveI := 𝔓.isPrime
  have hN : ((Ideal.absNorm 𝔓.asIdeal : ℕ) : 𝓞 K) ∈
      𝔓.asIdeal.comap (RingOfIntegers.mapRingHom (algebraMap K L)) := by
    rw [Ideal.mem_comap, map_natCast]
    exact Ideal.absNorm_mem _
  have hne : 𝔓.asIdeal.comap (RingOfIntegers.mapRingHom (algebraMap K L)) ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hN
    have h2 := congrArg (algebraMap (𝓞 K) K) hN
    rw [map_natCast, map_zero, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff] at h2
    exact 𝔓.ne_bot h2
  let 𝔭 : HeightOneSpectrum (𝓞 K) := ⟨_, inferInstance, hne⟩
  haveI : 𝔓.asIdeal.LiesOver 𝔭.asIdeal := ⟨rfl⟩
  obtain ⟨f, hfdef⟩ : ∃ f, f = 𝔓.asIdeal.inertiaDeg (𝓞 K) := ⟨_, rfl⟩
  have hf : Ideal.absNorm 𝔓.asIdeal = Ideal.absNorm 𝔭.asIdeal ^ f := by
    rw [hfdef, Ideal.absNorm_pow_inertiaDeg]
  have hn𝔭 : ((n : ℕ) : 𝓞 K) ∉ 𝔭.asIdeal := by
    intro h
    apply h𝔓
    have h' : (RingOfIntegers.mapRingHom (algebraMap K L)) (n : 𝓞 K) ∈ 𝔓.asIdeal := h
    rwa [map_natCast] at h'
  have hu : UnramIn L 𝔭 := hun 𝔭 (fun h => hn𝔭 (Ideal.dvd_span_singleton.mp h))
  have hcop1 : IsCoprime 𝔭.asIdeal (Ideal.span {(n : 𝓞 K)}) := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne2
    have e := (𝔭.isMaximal).eq_of_le hne2 le_sup_left
    have h2 : (n : 𝓞 K) ∈ 𝔭.asIdeal ⊔ Ideal.span {(n : 𝓞 K)} :=
      Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    rw [← e] at h2
    exact hn𝔭 h2
  have hI0 : 𝔭.asIdeal ^ f ≠ ⊥ := pow_ne_zero f 𝔭.ne_bot
  have hχ : ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ (𝔭.asIdeal ^ f) = 1 := by
    intro χ
    rw [heckeIdeal_prime_pow]
    obtain ⟨σ0, hσ0, -⟩ := exists_frob_pow_eq_one 𝔭 hu 𝔓 hf
    have hc : (∀ σ : L ≃ₐ[K] L, InInertia L 𝔭 σ → χ σ = 1) ∧ ∃ σ, IsFrob L 𝔭 σ :=
      ⟨fun σ hσ => by rw [hu σ hσ, map_one], ⟨σ0, hσ0⟩⟩
    unfold heckeVal
    rw [dif_pos hc]
    obtain ⟨Q, hQp, hQo, hQ⟩ := hc.2.choose_spec
    have hQf : Ideal.absNorm Q = Ideal.absNorm 𝔭.asIdeal ^ f := by
      rw [hfdef, Ideal.inertiaDeg_eq_of_isGaloisGroup 𝔭.asIdeal 𝔓.asIdeal Q (L ≃ₐ[K] L),
        Ideal.absNorm_pow_inertiaDeg]
    have hτ := pow_residue_degree_eq_one_of_isFrobenius 𝔭 hu Q hQf _ hQ
    have hχτ : χ hc.2.choose ^ f = 1 := by rw [← map_pow, hτ, map_one]
    rw [← Units.val_pow_eq_pow_val, hχτ, Units.val_one]
  obtain ⟨α, β, hr, hI⟩ := hart (𝔭.asIdeal ^ f) hI0 hcop1.pow_left hχ
  obtain ⟨π, hπ, hπ1⟩ := exists_gen_of_ray ⟨α, β, hr, hI⟩
  exact ⟨f, π, hf, hπ, Ideal.mem_span_singleton.mp hπ1⟩

end GlobalTheory.FieldSize.RayNorm

end
