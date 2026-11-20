import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowDescentCyclotomicStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteGaloisContainsRootsOfUnitsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFrobFixesRootOfOneModPlaceStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.ChevalleyUnitsProof

/- English proof (translation)
Establish `hN : normV v = Ideal.absNorm v.asIdeal`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Both sides reduce to the same expression. Establish `hne : v.asIdeal ≠ ⊥` using `v.ne_bot`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hN]; exact Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hne)`. Rewrite using `[hN]`. Conclude with `Ideal.absNorm_mem _`. Use `haveI : v.asIdeal.IsMaximal := v.isMaximal`. Use `letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _`.

Use `haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ hne`. Use `letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _`. Take `⟨p, hp⟩` from `CharP.exists (𝓞 F ⧸ v.asIdeal)`. Use `haveI := hp`. Use `haveI : Fact p.Prime := ⟨CharP.char_is_prime (𝓞 F ⧸ v.asIdeal) p⟩`.

Take `⟨n, hp', hcard⟩` from `FiniteField.card (𝓞 F ⧸ v.asIdeal) p`. Establish `hNv : normV v = p ^ (n : ℕ)`. Unfold `normV`. Rewrite using `[Nat.card_eq_fintype_card, hcard]`. Apply `Nat.coprime_of_dvd` to reduce the goal to its premises.

Introduce `q hq hqN hqb`. Rewrite `hqN` using `[hNv]`. Establish `hqp : q = p` using `(Nat.prime_dvd_prime_iff_eq hq hp').1 (hq.dvd_of_dvd_pow hqN)`. Substitute `hqp` using the available equality. Apply `hb` to reduce the goal to its premises.

Take `⟨e, rfl⟩` from `hqb`. Rewrite using `[Nat.cast_mul]`. Apply `Ideal.mul_mem_right` to reduce the goal to its premises. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`. Conclude with `CharP.cast_eq_zero _ _`.
-/
theorem normFacts (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (b : ℕ)
    (hb : ((b : ℕ) : 𝓞 F) ∉ v.asIdeal) :
    0 < normV v ∧ ((normV v : ℕ) : 𝓞 F) ∈ v.asIdeal ∧ (normV v).Coprime b := by
  classical
  have hN : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hne : v.asIdeal ≠ ⊥ := v.ne_bot
  refine ⟨?_, ?_, ?_⟩
  · rw [hN]; exact Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hne)
  · rw [hN]; exact Ideal.absNorm_mem _
  · haveI : v.asIdeal.IsMaximal := v.isMaximal
    letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
    haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
    letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
    obtain ⟨p, hp⟩ := CharP.exists (𝓞 F ⧸ v.asIdeal)
    haveI := hp
    haveI : Fact p.Prime := ⟨CharP.char_is_prime (𝓞 F ⧸ v.asIdeal) p⟩
    obtain ⟨n, hp', hcard⟩ := FiniteField.card (𝓞 F ⧸ v.asIdeal) p
    have hNv : normV v = p ^ (n : ℕ) := by
      unfold normV; rw [Nat.card_eq_fintype_card, hcard]
    apply Nat.coprime_of_dvd
    intro q hq hqN hqb
    rw [hNv] at hqN
    have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq hp').1 (hq.dvd_of_dvd_pow hqN)
    subst hqp
    apply hb
    obtain ⟨e, rfl⟩ := hqb
    rw [Nat.cast_mul]
    apply Ideal.mul_mem_right
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ _

/- English proof (translation)
Establish `hm : 0 < l ^ r` using `pow_pos hl.pos r`. Use `set m := l ^ r with hmdef`. Take `⟨M, hM0, hmM, hD⟩` from `GlobalTheory.T.exists_pow_descent_cyclotomic' E l r hl`. Set `Ω` to `AlgebraicClosure E`. Use `haveI : NeZero (M : Ω) := ⟨by exact_mod_cast hM0.ne'⟩`.

Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω M`. Set `K : IntermediateField E Ω` to `IntermediateField.adjoin E {ζ}`. Use `haveI : FiniteDimensional E K := IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)`. Use `haveI : NumberField K := NumberField.of_module_finite E K`. Use `haveI : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.tower_top (K := E) K`.

Use `haveI : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩`. Set `ζK : K` to `⟨ζ, IntermediateField.mem_adjoin_simple_self E ζ⟩`. Establish `hζK : IsPrimitiveRoot ζK M` using `(show IsPrimitiveRoot (algebraMap K Ω ζK) M from hζ).of_map_of_injective (algebraMap K Ω).injective`. Take `⟨L, hLfin, hLgal, hLroots⟩` from `GlobalTheory.T.exists_finite_galois_contains_roots_of_units E K Ω M hM0 ⟨ζK, hζK⟩`. Set `S : Set (HeightOneSpectrum (𝓞 K))` to `{v | ((M * b : ℕ) : 𝓞 K) ∈ v.asIdeal}`.

Establish `hS : S.Finite`. Establish `hne : Ideal.span {((M * b : ℕ) : 𝓞 K)} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `(Nat.mul_pos hM0 hb).ne'` after adjusting the coercions. Use `(Ideal.finite_factors hne).subset ?_` and prove the remaining obligations.

Introduce `v hv`. Conclude with `Ideal.dvd_span_singleton.2 hv`. Establish `hchoice : ∀ g : L ≃ₐ[K] L, ∃ v : HeightOneSpectrum (𝓞 K), v ∉ S ∧ ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ ∃ σ : G K Ω, IsFrob B (normV v) σ ∧ AlgEquiv.restrictNormalHom L σ = g`. Introduce `g`. Take `⟨v, hv, -, B, hB, -, σ, hσ, hg⟩` from `GlobalTheory.Published.chebotarevDegreeOne' K Ω L g S hS`.

Conclude with `⟨v, hv, B, hB, σ, hσ, hg⟩`. Use `choose v hvS B hB σ hσ hg using hchoice`. Establish `hvb : ∀ g, ((b : ℕ) : 𝓞 K) ∉ (v g).asIdeal` using `fun g h => hvS g (by simp only [S, Set.mem_setOf_eq, Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h)`. Establish `hvM : ∀ g, ((M : ℕ) : 𝓞 K) ∉ (v g).asIdeal` using `fun g h => hvS g (by simp only [S, Set.mem_setOf_eq, Nat.cast_mul]; exact Ideal.mul_mem_right _ _ h)`. Establish `hnf` using `fun g => normFacts K (v g) b (hvb g)`.

Set `a : ℕ` to `∏ g : L ≃ₐ[K] L, normV (v g)`. Use `⟨a, Finset.prod_pos fun g _ => (hnf g).1, Nat.Coprime.prod_left fun g _ => (hnf g).2.2, ?_⟩` and prove the remaining obligations. Introduce `u hu`. Take `⟨c, hc⟩` from `hu`. Take `⟨w, hw⟩` from `IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω ((u : 𝓞 E) : E)) hM0`.

Establish `hwL` using `hLroots u w hw`. Set `x : 𝓞 K` to `⟨algebraMap E K ((u : 𝓞 E) : E), ((u : 𝓞 E).2).map (IsScalarTower.toAlgHom ℤ E K)⟩`. Set `c' : 𝓞 K` to `⟨algebraMap E K (c : E), (c.2).map (IsScalarTower.toAlgHom ℤ E K)⟩`. Establish `hx1 : ∀ g, x - 1 ∈ (v g).asIdeal`. Introduce `g`.

Establish `hxc : x - 1 = ((a : ℕ) : 𝓞 K) * c'`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `algebraMap E K ((u : 𝓞 E) : E) - 1 = ((a : ℕ) : K) * algebraMap E K ((c : 𝓞 E) : E)`. Establish `h2` using `congrArg (fun t : 𝓞 E => algebraMap E K (t : E)) hc`. Simplify using `using h2`.

Rewrite using `[hxc]`. Apply `Ideal.mul_mem_right` to reduce the goal to its premises. Establish `hdvd : normV (v g) ∣ a` using `Finset.dvd_prod_of_mem _ (Finset.mem_univ g)`. Take `⟨e, he⟩` from `hdvd`. Rewrite using `[he, Nat.cast_mul]`.

Conclude with `Ideal.mul_mem_right _ _ (hnf g).2.1`. Establish `hwx : w ^ M = algebraMap K Ω (x : K)`. Rewrite using `[hw]`. Both sides reduce to the same expression. Establish `hfix : ∀ g : L ≃ₐ[K] L, g ⟨w, hwL⟩ = ⟨w, hwL⟩`.

Introduce `g`. Establish `h1` using `GlobalTheory.T.isFrob_fixes_root_of_one_mod_place K Ω M ζK hζK (v g) (hvM g) (B g) (hB g) (σ g) (hσ g) x (hx1 g) w hwx`. Rewrite using `[← hg g]`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[AlgEquiv.restrictNormalHom_apply]`.

Conclude with `h1`. Establish `hwK : (⟨w, hwL⟩ : L) ∈ (⊥ : IntermediateField K L)` using `(IsGalois.mem_bot_iff_fixed _).2 hfix`. Take `⟨k, hk⟩` from `IntermediateField.mem_bot.1 hwK`. Establish `hwK' : w ∈ K`. Establish `: algebraMap K Ω k = w` using `congrArg Subtype.val hk`.

Rewrite using `[← this]`. Conclude with `k.2`. Take `⟨y, hy⟩` from `hD Ω ζ hζ _ w hwK' hw`. Establish `hu0 : ((u : 𝓞 E) : E) ≠ 0`. Introduce `h0`.

Establish `: ((u : 𝓞 E)) = 0` using `RingOfIntegers.ext (by simpa using h0)`. Conclude with `u.ne_zero this`. Establish `hy0 : y ≠ 0`. Introduce and unpack `rfl; exact hu0 (by rw [← hy, zero_pow hm.ne'])`. Establish `hyi : IsIntegral ℤ y` using `IsIntegral.of_pow hm (by rw [hy]; exact (u : 𝓞 E).2)`.

Establish `hyi' : IsIntegral ℤ y⁻¹` using `IsIntegral.of_pow hm (by`. Rewrite using `[inv_pow, hy]`. Establish `: (((u⁻¹ : (𝓞 E)ˣ) : 𝓞 E) : E) = ((u : 𝓞 E) : E)⁻¹`. Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises. Establish `h3` using `congrArg (fun t : 𝓞 E => (t : E)) u.inv_mul`.

Simplify using `using h3`. Rewrite using `[← this]`. Conclude with `((u⁻¹ : (𝓞 E)ˣ) : 𝓞 E).2)`. Use `⟨⟨⟨y, hyi⟩, ⟨y⁻¹, hyi'⟩, RingOfIntegers.ext (by change y * y⁻¹ = 1; exact mul_inv_cancel₀ hy0), RingOfIntegers.ext (by change y⁻¹ * y = 1; exact inv_mul_cancel₀ hy0)⟩, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises.

Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[Units.val_pow_eq_pow_val]`. Express the relevant statement in the definitionally equal form `((u : 𝓞 E) : E) = y ^ m`. Rewrite using `[hy]`.
-/
theorem core (E : Type) [Field E] [NumberField E] (l r b : ℕ) (hl : l.Prime) (hb : 0 < b) :
    ∃ a : ℕ, 0 < a ∧ a.Coprime b ∧ ∀ u : (𝓞 E)ˣ, (a : 𝓞 E) ∣ (u : 𝓞 E) - 1 → ∃ v : (𝓞 E)ˣ, u = v ^ (l ^ r) := by
  classical
  have hm : 0 < l ^ r := pow_pos hl.pos r
  set m := l ^ r with hmdef
  obtain ⟨M, hM0, hmM, hD⟩ := GlobalTheory.T.exists_pow_descent_cyclotomic' E l r hl
  let Ω := AlgebraicClosure E
  haveI : NeZero (M : Ω) := ⟨by exact_mod_cast hM0.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  let K : IntermediateField E Ω := IntermediateField.adjoin E {ζ}
  haveI : FiniteDimensional E K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  haveI : NumberField K := NumberField.of_module_finite E K
  haveI : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.tower_top (K := E) K
  haveI : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  let ζK : K := ⟨ζ, IntermediateField.mem_adjoin_simple_self E ζ⟩
  have hζK : IsPrimitiveRoot ζK M :=
    (show IsPrimitiveRoot (algebraMap K Ω ζK) M from hζ).of_map_of_injective (algebraMap K Ω).injective
  obtain ⟨L, hLfin, hLgal, hLroots⟩ := GlobalTheory.T.exists_finite_galois_contains_roots_of_units E K Ω M hM0 ⟨ζK, hζK⟩
  let S : Set (HeightOneSpectrum (𝓞 K)) := {v | ((M * b : ℕ) : 𝓞 K) ∈ v.asIdeal}
  have hS : S.Finite := by
    have hne : Ideal.span {((M * b : ℕ) : 𝓞 K)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Nat.mul_pos hM0 hb).ne'
    refine (Ideal.finite_factors hne).subset ?_
    intro v hv
    exact Ideal.dvd_span_singleton.2 hv
  have hchoice : ∀ g : L ≃ₐ[K] L, ∃ v : HeightOneSpectrum (𝓞 K), v ∉ S ∧ ∃ B : ValuationSubring Ω,
      IsPlaceOver B v ∧ ∃ σ : G K Ω, IsFrob B (normV v) σ ∧ AlgEquiv.restrictNormalHom L σ = g := by
    intro g
    obtain ⟨v, hv, -, B, hB, -, σ, hσ, hg⟩ := GlobalTheory.Published.chebotarevDegreeOne' K Ω L g S hS
    exact ⟨v, hv, B, hB, σ, hσ, hg⟩
  choose v hvS B hB σ hσ hg using hchoice
  have hvb : ∀ g, ((b : ℕ) : 𝓞 K) ∉ (v g).asIdeal := fun g h =>
    hvS g (by simp only [S, Set.mem_setOf_eq, Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h)
  have hvM : ∀ g, ((M : ℕ) : 𝓞 K) ∉ (v g).asIdeal := fun g h =>
    hvS g (by simp only [S, Set.mem_setOf_eq, Nat.cast_mul]; exact Ideal.mul_mem_right _ _ h)
  have hnf := fun g => normFacts K (v g) b (hvb g)
  let a : ℕ := ∏ g : L ≃ₐ[K] L, normV (v g)
  refine ⟨a, Finset.prod_pos fun g _ => (hnf g).1, Nat.Coprime.prod_left fun g _ => (hnf g).2.2, ?_⟩
  intro u hu
  obtain ⟨c, hc⟩ := hu
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω ((u : 𝓞 E) : E)) hM0
  have hwL := hLroots u w hw
  let x : 𝓞 K := ⟨algebraMap E K ((u : 𝓞 E) : E), ((u : 𝓞 E).2).map (IsScalarTower.toAlgHom ℤ E K)⟩
  let c' : 𝓞 K := ⟨algebraMap E K (c : E), (c.2).map (IsScalarTower.toAlgHom ℤ E K)⟩
  have hx1 : ∀ g, x - 1 ∈ (v g).asIdeal := by
    intro g
    have hxc : x - 1 = ((a : ℕ) : 𝓞 K) * c' := by
      apply RingOfIntegers.ext
      change algebraMap E K ((u : 𝓞 E) : E) - 1 = ((a : ℕ) : K) * algebraMap E K ((c : 𝓞 E) : E)
      have h2 := congrArg (fun t : 𝓞 E => algebraMap E K (t : E)) hc
      simpa using h2
    rw [hxc]
    apply Ideal.mul_mem_right
    have hdvd : normV (v g) ∣ a := Finset.dvd_prod_of_mem _ (Finset.mem_univ g)
    obtain ⟨e, he⟩ := hdvd
    rw [he, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (hnf g).2.1
  have hwx : w ^ M = algebraMap K Ω (x : K) := by
    rw [hw]; rfl
  have hfix : ∀ g : L ≃ₐ[K] L, g ⟨w, hwL⟩ = ⟨w, hwL⟩ := by
    intro g
    have h1 := GlobalTheory.T.isFrob_fixes_root_of_one_mod_place K Ω M ζK hζK (v g) (hvM g) (B g) (hB g) (σ g) (hσ g) x (hx1 g) w hwx
    rw [← hg g]
    apply Subtype.ext
    rw [AlgEquiv.restrictNormalHom_apply]
    exact h1
  have hwK : (⟨w, hwL⟩ : L) ∈ (⊥ : IntermediateField K L) := (IsGalois.mem_bot_iff_fixed _).2 hfix
  obtain ⟨k, hk⟩ := IntermediateField.mem_bot.1 hwK
  have hwK' : w ∈ K := by
    have : algebraMap K Ω k = w := congrArg Subtype.val hk
    rw [← this]; exact k.2
  obtain ⟨y, hy⟩ := hD Ω ζ hζ _ w hwK' hw
  have hu0 : ((u : 𝓞 E) : E) ≠ 0 := by
    intro h0
    have : ((u : 𝓞 E)) = 0 := RingOfIntegers.ext (by simpa using h0)
    exact u.ne_zero this
  have hy0 : y ≠ 0 := by
    rintro rfl; exact hu0 (by rw [← hy, zero_pow hm.ne'])
  have hyi : IsIntegral ℤ y := IsIntegral.of_pow hm (by rw [hy]; exact (u : 𝓞 E).2)
  have hyi' : IsIntegral ℤ y⁻¹ := IsIntegral.of_pow hm (by
    rw [inv_pow, hy]
    have : (((u⁻¹ : (𝓞 E)ˣ) : 𝓞 E) : E) = ((u : 𝓞 E) : E)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      have h3 := congrArg (fun t : 𝓞 E => (t : E)) u.inv_mul
      simpa using h3
    rw [← this]; exact ((u⁻¹ : (𝓞 E)ˣ) : 𝓞 E).2)
  refine ⟨⟨⟨y, hyi⟩, ⟨y⁻¹, hyi'⟩, RingOfIntegers.ext (by change y * y⁻¹ = 1; exact mul_inv_cancel₀ hy0), RingOfIntegers.ext (by change y⁻¹ * y = 1; exact inv_mul_cancel₀ hy0)⟩, ?_⟩
  apply Units.ext
  apply RingOfIntegers.ext
  rw [Units.val_pow_eq_pow_val]
  change ((u : 𝓞 E) : E) = y ^ m
  rw [hy]

/- English proof (translation)
Take `⟨a₁, ha₁, hc₁, hu₁⟩` from `h₁`. Take `⟨a₂, ha₂, hc₂, hu₂⟩` from `h₂`. Use `⟨a₁ * a₂, Nat.mul_pos ha₁ ha₂, Nat.Coprime.mul hc₁ hc₂, ?_⟩` and prove the remaining obligations. Introduce `u hu`. Establish `hd₁ : (a₁ : 𝓞 E) ∣ (u : 𝓞 E) - 1` using `dvd_trans ⟨(a₂ : 𝓞 E), by push_cast; ring⟩ hu`.

Establish `hd₂ : (a₂ : 𝓞 E) ∣ (u : 𝓞 E) - 1` using `dvd_trans ⟨(a₁ : 𝓞 E), by push_cast; ring⟩ hu`. Take `⟨v₁, hv₁⟩` from `hu₁ u hd₁`. Take `⟨v₂, hv₂⟩` from `hu₂ u hd₂`. Use `set s := Nat.gcdA m₁ m₂`. Use `set t := Nat.gcdB m₁ m₂`.

Establish `hg : ((1 : ℕ) : ℤ) = (m₁ : ℤ) * s + (m₂ : ℤ) * t`. Rewrite using `[← hcop.gcd_eq_one]`. Conclude with `Nat.gcd_eq_gcd_ab m₁ m₂`. Establish `key : u = u ^ ((m₁ : ℤ) * s + (m₂ : ℤ) * t)`. Rewrite using `[← hg]`.

Simplify using the standard rewrite rules. Establish `e1 : u ^ ((m₁ : ℤ) * s) = v₂ ^ (s * ((m₁ * m₂ : ℕ) : ℤ))` using `by conv_lhs => rw [hv₂]`. Rewrite using `[← zpow_natCast, ← zpow_mul]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `e2 : u ^ ((m₂ : ℤ) * t) = v₁ ^ (t * ((m₁ * m₂ : ℕ) : ℤ))` using `by conv_lhs => rw [hv₁]`. Rewrite using `[← zpow_natCast, ← zpow_mul]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨v₂ ^ s * v₁ ^ t, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e1, e2, zpow_mul, zpow_mul, ← mul_zpow, zpow_natCast]`.
-/
theorem combine (E : Type) [Field E] [NumberField E] (b m₁ m₂ : ℕ) (hcop : m₁.Coprime m₂)
    (h₁ : ∃ a : ℕ, 0 < a ∧ a.Coprime b ∧ ∀ u : (𝓞 E)ˣ, (a : 𝓞 E) ∣ (u : 𝓞 E) - 1 → ∃ v : (𝓞 E)ˣ, u = v ^ m₁)
    (h₂ : ∃ a : ℕ, 0 < a ∧ a.Coprime b ∧ ∀ u : (𝓞 E)ˣ, (a : 𝓞 E) ∣ (u : 𝓞 E) - 1 → ∃ v : (𝓞 E)ˣ, u = v ^ m₂) :
    ∃ a : ℕ, 0 < a ∧ a.Coprime b ∧ ∀ u : (𝓞 E)ˣ, (a : 𝓞 E) ∣ (u : 𝓞 E) - 1 →
      ∃ v : (𝓞 E)ˣ, u = v ^ (m₁ * m₂) := by
  obtain ⟨a₁, ha₁, hc₁, hu₁⟩ := h₁
  obtain ⟨a₂, ha₂, hc₂, hu₂⟩ := h₂
  refine ⟨a₁ * a₂, Nat.mul_pos ha₁ ha₂, Nat.Coprime.mul hc₁ hc₂, ?_⟩
  intro u hu
  have hd₁ : (a₁ : 𝓞 E) ∣ (u : 𝓞 E) - 1 := dvd_trans ⟨(a₂ : 𝓞 E), by push_cast; ring⟩ hu
  have hd₂ : (a₂ : 𝓞 E) ∣ (u : 𝓞 E) - 1 := dvd_trans ⟨(a₁ : 𝓞 E), by push_cast; ring⟩ hu
  obtain ⟨v₁, hv₁⟩ := hu₁ u hd₁
  obtain ⟨v₂, hv₂⟩ := hu₂ u hd₂
  set s := Nat.gcdA m₁ m₂
  set t := Nat.gcdB m₁ m₂
  have hg : ((1 : ℕ) : ℤ) = (m₁ : ℤ) * s + (m₂ : ℤ) * t := by
    rw [← hcop.gcd_eq_one]; exact Nat.gcd_eq_gcd_ab m₁ m₂
  have key : u = u ^ ((m₁ : ℤ) * s + (m₂ : ℤ) * t) := by
    rw [← hg]; simp
  have e1 : u ^ ((m₁ : ℤ) * s) = v₂ ^ (s * ((m₁ * m₂ : ℕ) : ℤ)) := by
    conv_lhs => rw [hv₂]
    rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
  have e2 : u ^ ((m₂ : ℤ) * t) = v₁ ^ (t * ((m₁ * m₂ : ℕ) : ℤ)) := by
    conv_lhs => rw [hv₁]
    rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
  refine ⟨v₂ ^ s * v₁ ^ t, ?_⟩
  calc u = u ^ ((m₁ : ℤ) * s + (m₂ : ℤ) * t) := key
    _ = u ^ ((m₁ : ℤ) * s) * u ^ ((m₂ : ℤ) * t) := zpow_add _ _ _
    _ = (v₂ ^ s * v₁ ^ t) ^ (m₁ * m₂) := by
      rw [e1, e2, zpow_mul, zpow_mul, ← mul_zpow, zpow_natCast]

end GlobalTheory.ChevalleyUnitsProof

/- English proof (translation)
Introduce `E _ _ m b hm hb`. Proceed by induction on `m using Nat.recOnPosPrimePosCoprime with`. Consider the case `prime_pow p n hp hn => exact GlobalTheory.ChevalleyUnitsProof.core E p n b hp hb`. Consider the case `zero => exact absurd hm (lt_irrefl 0)`. Consider the case `one => exact ⟨1, one_pos, Nat.coprime_one_left b, fun u _ => ⟨u, (pow_one u).symm⟩⟩`.

Consider the case `coprime a b' ha hb' hab iha ihb => exact GlobalTheory.ChevalleyUnitsProof.combine E b a b' hab (iha (by omega)) (ihb (by omega))`.
-/
theorem GlobalTheory.Published.chevalleyUnits' : GlobalTheory.Published.ChevalleyUnits := by
  intro E _ _ m b hm hb
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn => exact GlobalTheory.ChevalleyUnitsProof.core E p n b hp hb
  | zero => exact absurd hm (lt_irrefl 0)
  | one => exact ⟨1, one_pos, Nat.coprime_one_left b, fun u _ => ⟨u, (pow_one u).symm⟩⟩
  | coprime a b' ha hb' hab iha ihb => exact GlobalTheory.ChevalleyUnitsProof.combine E b a b' hab (iha (by omega)) (ihb (by omega))

end
