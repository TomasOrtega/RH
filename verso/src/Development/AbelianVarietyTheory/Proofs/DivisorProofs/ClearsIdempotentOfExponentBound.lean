import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

namespace GlobalTheory.Proof.clears_idempotent_of_exponent_bound

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Use `set e := multiplicity v.asIdeal 𝔣 with he`. Take `⟨𝔤, h𝔤⟩` from `pow_multiplicity_dvd v.asIdeal 𝔣`. Establish `hnu : ¬ IsUnit v.asIdeal`. Rewrite using `[Ideal.isUnit_iff]`. Conclude with `v.isPrime.ne_top`.

Establish `hfin : FiniteMultiplicity v.asIdeal 𝔣` using `FiniteMultiplicity.of_not_isUnit hnu h𝔣`. Establish `hndvd : ¬ v.asIdeal ∣ 𝔤`. Introduce and unpack `⟨𝔥, rfl⟩`. Apply `hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self e)` to reduce the goal to its premises. Conclude with `⟨𝔥, by rw [h𝔤, pow_succ, mul_assoc]⟩`.

Rewrite `hndvd` using `[Ideal.dvd_iff_le, SetLike.not_le_iff_exists]`. Take `⟨x, hx𝔤, hxv⟩` from `hndvd`. Use `⟨x, hxv, ?_⟩` and prove the remaining obligations. Rewrite using `[h𝔤, mul_comm x]`. Use `Ideal.mul_mem_mul ?_ hx𝔤` and prove the remaining obligations.

Conclude with `Ideal.pow_le_pow_right hk (Ideal.pow_mem_pow hc k)`.
-/
theorem exists_not_mem_mul_pow_mem {𝔣 : Ideal (OF E)} (h𝔣 : 𝔣 ≠ ⊥) (v : HeightOneSpectrum (OF E)) {c : OF E}
    (hc : c ∈ v.asIdeal) {k : ℕ} (hk : expIn 𝔣 v ≤ k) : ∃ x : OF E, x ∉ v.asIdeal ∧ x * c ^ k ∈ 𝔣 := by
  set e := multiplicity v.asIdeal 𝔣 with he
  obtain ⟨𝔤, h𝔤⟩ := pow_multiplicity_dvd v.asIdeal 𝔣
  have hnu : ¬ IsUnit v.asIdeal := by
    rw [Ideal.isUnit_iff]; exact v.isPrime.ne_top
  have hfin : FiniteMultiplicity v.asIdeal 𝔣 := FiniteMultiplicity.of_not_isUnit hnu h𝔣
  have hndvd : ¬ v.asIdeal ∣ 𝔤 := by
    rintro ⟨𝔥, rfl⟩
    apply hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self e)
    exact ⟨𝔥, by rw [h𝔤, pow_succ, mul_assoc]⟩
  rw [Ideal.dvd_iff_le, SetLike.not_le_iff_exists] at hndvd
  obtain ⟨x, hx𝔤, hxv⟩ := hndvd
  refine ⟨x, hxv, ?_⟩
  rw [h𝔤, mul_comm x]
  refine Ideal.mul_mem_mul ?_ hx𝔤
  exact Ideal.pow_le_pow_right hk (Ideal.pow_mem_pow hc k)

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨M, hM, hle⟩` from `Ideal.exists_le_maximal _ hne`. Establish `hMb : M ≠ ⊥` using `Ideal.IsMaximal.ne_bot_of_isIntegral_int M`. Set `v : HeightOneSpectrum (OF E)` to `⟨M, hM.isPrime, hMb⟩`. Establish `hlv : (l : OF E) ∈ v.asIdeal` using `hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))`.

Take `⟨x, hxv, hx⟩` from `exists_not_mem_mul_pow_mem h𝔣 v hlv (hk v hlv)`. Apply `hxv` to reduce the goal to its premises. Apply `hle` to reduce the goal to its premises. Apply `Ideal.mem_sup_left` to reduce the goal to its premises. Rewrite using `[Submodule.mem_colon_singleton, smul_eq_mul]`.

Conclude with `hx`.
-/
theorem colon_sup_eq_top {𝔣 : Ideal (OF E)} (h𝔣 : 𝔣 ≠ ⊥) {l : ℕ} (hl : l ≠ 0) {k : ℕ}
    (hk : ∀ v : HeightOneSpectrum (OF E), (l : OF E) ∈ v.asIdeal → expIn 𝔣 v ≤ k) :
    𝔣.colon {((l : OF E) ^ k)} ⊔ Ideal.span {(l : OF E)} = ⊤ := by
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hMb : M ≠ ⊥ := Ideal.IsMaximal.ne_bot_of_isIntegral_int M
  let v : HeightOneSpectrum (OF E) := ⟨M, hM.isPrime, hMb⟩
  have hlv : (l : OF E) ∈ v.asIdeal := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  obtain ⟨x, hxv, hx⟩ := exists_not_mem_mul_pow_mem h𝔣 v hlv (hk v hlv)
  apply hxv
  apply hle
  apply Ideal.mem_sup_left
  rw [Submodule.mem_colon_singleton, smul_eq_mul]
  exact hx

end GlobalTheory.Proof.clears_idempotent_of_exponent_bound

namespace GlobalTheory.Proof.clears_idempotent_of_exponent_bound

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Use `set J := 𝔣.colon {((l : OF E) ^ k)} with hJ`. Establish `hmemJ : ∀ r : OF E, r ∈ J ↔ r * (l : OF E) ^ k ∈ 𝔣` using `fun r => by`. Rewrite using `[hJ, Submodule.mem_colon_singleton, smul_eq_mul]`. Establish `hfJ : 𝔣 ≤ J` using `fun r hr => (hmemJ r).2 (Ideal.mul_mem_right _ _ hr)`. Establish `hJb : J ≠ ⊥` using `fun h => h𝔣 (le_bot_iff.1 (h ▸ hfJ))`.

Establish `htop` using `colon_sup_eq_top h𝔣 hl.ne_zero hk`. Rewrite `htop` using `[← hJ]`. Use `⟨Ideal.absNorm J, ?_, (hmemJ _).1 (Ideal.absNorm_mem J)⟩` and prove the remaining obligations. Rewrite using `[Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hl]`. Introduce `hdvd`.

Establish `hcard : Nat.card (OF E ⧸ J) = Ideal.absNorm J`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Establish `hne : Nat.card (OF E ⧸ J) ≠ 0`. Rewrite using `[hcard]`. Conclude with `fun h => hJb (Ideal.absNorm_eq_zero_iff.1 h)`.

Use `haveI : Finite (OF E ⧸ J) := Nat.finite_of_card_ne_zero hne`. Use `haveI : Fact l.Prime := ⟨hl⟩`. Take `⟨x, hx⟩` from `exists_prime_addOrderOf_dvd_card' (G := OF E ⧸ J) l (hcard ▸ hdvd)`. Establish `h1 : (1 : OF E) ∈ J ⊔ Ideal.span {(l : OF E)}` using `htop ▸ Submodule.mem_top`. Take `⟨j, hj, y, hy, hjy⟩` from `Submodule.mem_sup.1 h1`.

Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.1 hy`. Establish `hu : (Ideal.Quotient.mk J a) * (l : OF E ⧸ J) = 1`. Establish `: Ideal.Quotient.mk J (j + a * l) = 1` using `by rw [hjy, map_one]`. Rewrite `this` using `[map_add, Ideal.Quotient.eq_zero_iff_mem.2 hj, zero_add, map_mul, map_natCast]`. Conclude with `this`.

Establish `hlx : (l : OF E ⧸ J) * x = 0`. Rewrite using `[← nsmul_eq_mul, ← hx]`. Conclude with `addOrderOf_nsmul_eq_zero x`. Establish `hx0 : x = 0`. Combine the equalities or inequalities in the displayed calculation.

Rewrite `hx` using `[hx0, addOrderOf_zero]`. Conclude with `hl.one_lt.ne hx`.
-/
theorem exists_coprime_mul_pow_mem {𝔣 : Ideal (OF E)} (h𝔣 : 𝔣 ≠ ⊥) {l : ℕ} (hl : l.Prime) {k : ℕ}
    (hk : ∀ v : HeightOneSpectrum (OF E), (l : OF E) ∈ v.asIdeal → expIn 𝔣 v ≤ k) :
    ∃ m : ℕ, m.Coprime l ∧ ((m : OF E) * (l : OF E) ^ k) ∈ 𝔣 := by
  set J := 𝔣.colon {((l : OF E) ^ k)} with hJ
  have hmemJ : ∀ r : OF E, r ∈ J ↔ r * (l : OF E) ^ k ∈ 𝔣 := fun r => by
    rw [hJ, Submodule.mem_colon_singleton, smul_eq_mul]
  have hfJ : 𝔣 ≤ J := fun r hr => (hmemJ r).2 (Ideal.mul_mem_right _ _ hr)
  have hJb : J ≠ ⊥ := fun h => h𝔣 (le_bot_iff.1 (h ▸ hfJ))
  have htop := colon_sup_eq_top h𝔣 hl.ne_zero hk
  rw [← hJ] at htop
  refine ⟨Ideal.absNorm J, ?_, (hmemJ _).1 (Ideal.absNorm_mem J)⟩
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hl]
  intro hdvd
  have hcard : Nat.card (OF E ⧸ J) = Ideal.absNorm J := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hne : Nat.card (OF E ⧸ J) ≠ 0 := by
    rw [hcard]; exact fun h => hJb (Ideal.absNorm_eq_zero_iff.1 h)
  haveI : Finite (OF E ⧸ J) := Nat.finite_of_card_ne_zero hne
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := OF E ⧸ J) l (hcard ▸ hdvd)
  have h1 : (1 : OF E) ∈ J ⊔ Ideal.span {(l : OF E)} := htop ▸ Submodule.mem_top
  obtain ⟨j, hj, y, hy, hjy⟩ := Submodule.mem_sup.1 h1
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  have hu : (Ideal.Quotient.mk J a) * (l : OF E ⧸ J) = 1 := by
    have : Ideal.Quotient.mk J (j + a * l) = 1 := by rw [hjy, map_one]
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.2 hj, zero_add, map_mul, map_natCast] at this
    exact this
  have hlx : (l : OF E ⧸ J) * x = 0 := by
    rw [← nsmul_eq_mul, ← hx]; exact addOrderOf_nsmul_eq_zero x
  have hx0 : x = 0 := by
    calc x = (Ideal.Quotient.mk J a * (l : OF E ⧸ J)) * x := by rw [hu, one_mul]
      _ = 0 := by rw [mul_assoc, hlx, mul_zero]
  rw [hx0, addOrderOf_zero] at hx
  exact hl.one_lt.ne hx

/- English proof (translation)
Establish `hc : IsCoprime (m : O) (l : O)`. Use `(Nat.isCoprime_iff_coprime.2 h).map (Int.castRingHom O)` as an intermediate fact. Simplify using `using this`. Assume the negation of the conclusion as `hm`. Take `⟨u, w, huw⟩` from `hc`.

Establish `hm' : (m : O) ∈ IsLocalRing.maximalIdeal O` using `(IsLocalRing.mem_maximalIdeal _).2 hm`. Establish `: (1 : O) ∈ IsLocalRing.maximalIdeal O`. Rewrite using `[← huw]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm') (Ideal.mul_mem_left _ _ hl)`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 this)`.
-/
theorem isUnit_natCast_of_coprime {O : Type} [CommRing O] [IsLocalRing O] {m l : ℕ} (h : m.Coprime l)
    (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) : IsUnit (m : O) := by
  have hc : IsCoprime (m : O) (l : O) := by
    have := (Nat.isCoprime_iff_coprime.2 h).map (Int.castRingHom O)
    simpa using this
  by_contra hm
  obtain ⟨u, w, huw⟩ := hc
  have hm' : (m : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hm
  have : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [← huw]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm') (Ideal.mul_mem_left _ _ hl)
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 this)

end GlobalTheory.Proof.clears_idempotent_of_exponent_bound

namespace GlobalTheory.Proof.clears_idempotent_of_exponent_bound

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Take `⟨a, b, -, rfl⟩` from `mem_orderC.1 hx`. Use `mem_orderC.2 ⟨c * a, algebraMap (OF E) (𝓞 E) c * b, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hc), ?_⟩` and prove the remaining obligations. Establish `hc' : ∀ a : OF E, algebraMap (OF E) E a = algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) a)` using `fun a => rfl`. Rewrite using `[mul_add, map_mul, map_mul, ← hc' c]`.
-/
theorem mul_mem_orderC {𝔣 : Ideal (OF E)} {c : OF E} (hc : c ∈ 𝔣) {x : E} (hx : x ∈ orderC (⊤ : Ideal (OF E))) :
    algebraMap (OF E) E c * x ∈ orderC 𝔣 := by
  obtain ⟨a, b, -, rfl⟩ := mem_orderC.1 hx
  refine mem_orderC.2 ⟨c * a, algebraMap (OF E) (𝓞 E) c * b,
    Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hc), ?_⟩
  have hc' : ∀ a : OF E, algebraMap (OF E) E a = algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) a) := fun a => rfl
  rw [mul_add, map_mul, map_mul, ← hc' c]

def mulMap {𝔣 : Ideal (OF E)} {c : OF E} (hc : c ∈ 𝔣) : orderC (⊤ : Ideal (OF E)) →ₗ[ℤ] orderC 𝔣 where
  toFun x := ⟨algebraMap (OF E) E c * x, mul_mem_orderC hc x.2⟩
  map_add' x y := Subtype.ext (by simp [mul_add])
  map_smul' n x := Subtype.ext (by simp [mul_left_comm])

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y`. Simplify using `only [TensorProduct.map_tmul, LinearMap.mulLeft_apply]`. Express the relevant statement in the definitionally equal form `σ (algebraMap (OF E) E c * x) * algebraMap O K (w * y) = _ * (σ x * algebraMap O K y)`.

Rewrite using `[map_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `add s t hs ht => rw [map_add, map_add, hs, ht, map_add, mul_add]`.
-/
theorem coordAt_map {𝔣 : Ideal (OF E)} {c : OF E} (hc : c ∈ 𝔣) {O : Type} [CommRing O] {K : Type} [Field K]
    [Algebra O K] (w : O) (σ : E →+* K) (t : orderC (⊤ : Ideal (OF E)) ⊗[ℤ] O) :
    coordAt O 𝔣 σ (TensorProduct.map (mulMap hc) (LinearMap.mulLeft ℤ w) t) =
      σ (algebraMap (OF E) E c) * algebraMap O K w * coordAt O ⊤ σ t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [TensorProduct.map_tmul, LinearMap.mulLeft_apply]
    change σ (algebraMap (OF E) E c * x) * algebraMap O K (w * y) = _ * (σ x * algebraMap O K y)
    rw [map_mul, map_mul]; ring
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, mul_add]

end GlobalTheory.Proof.clears_idempotent_of_exponent_bound

open GlobalTheory.Proof.clears_idempotent_of_exponent_bound in
/- English proof (translation)
Introduce `E _ _ _ 𝔣 h𝔣 l hl k hk O _ _ _ _ K _ _ _ hlO D hD σ`. Take `⟨m, hm, hmem⟩` from `exists_coprime_mul_pow_mem h𝔣 hl hk`. Take `⟨u, hu⟩` from `isUnit_natCast_of_coprime (O := O) hm hlO`. Take `⟨t, ht⟩` from `hD σ`. Use `⟨TensorProduct.map (mulMap hmem) (LinearMap.mulLeft ℤ ((u⁻¹ : Oˣ) : O)) t, fun σ' => ?_⟩` and prove the remaining obligations.

Rewrite using `[coordAt_map, ht]`. Establish `hw : algebraMap O K (m : O) * algebraMap O K ((u⁻¹ : Oˣ) : O) = 1`. Rewrite using `[← map_mul, ← hu, Units.mul_inv, map_one]`. Simplify using `only [map_mul, map_pow, map_natCast] at hw ⊢`. Use `split_ifs`.

Take the linear combination `((l : K) ^ k * algebraMap O K D) * hw`. Simplify using the standard rewrite rules.
-/
theorem GlobalTheory.Proof.clears_idempotent_of_exponent_bound.clearsIdem_condC :
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 : Ideal (OF E)), 𝔣 ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ k : ℕ, (∀ v : HeightOneSpectrum (OF E), (l : OF E) ∈ v.asIdeal → expIn 𝔣 v ≤ k) → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ D : O, ClearsIdem K (⊤ : Ideal (OF E)) D → ClearsIdem K 𝔣 ((l : O) ^ k * D) := by
  intro E _ _ _ 𝔣 h𝔣 l hl k hk O _ _ _ _ K _ _ _ hlO D hD σ
  obtain ⟨m, hm, hmem⟩ := exists_coprime_mul_pow_mem h𝔣 hl hk
  obtain ⟨u, hu⟩ := isUnit_natCast_of_coprime (O := O) hm hlO
  obtain ⟨t, ht⟩ := hD σ
  refine ⟨TensorProduct.map (mulMap hmem) (LinearMap.mulLeft ℤ ((u⁻¹ : Oˣ) : O)) t, fun σ' => ?_⟩
  rw [coordAt_map, ht]
  have hw : algebraMap O K (m : O) * algebraMap O K ((u⁻¹ : Oˣ) : O) = 1 := by
    rw [← map_mul, ← hu, Units.mul_inv, map_one]
  simp only [map_mul, map_pow, map_natCast] at hw ⊢
  split_ifs
  · linear_combination ((l : K) ^ k * algebraMap O K D) * hw
  · simp
