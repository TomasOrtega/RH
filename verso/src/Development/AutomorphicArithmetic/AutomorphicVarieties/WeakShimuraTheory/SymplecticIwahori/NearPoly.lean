import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.AdjMulSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.NilPoly
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Pp

/- English proof (translation)
Take `⟨q, hq⟩` from `Ideal.exists_maximal S`. Take `⟨e, he, H⟩` from `GlobalTheory.exists_idempotent_notMem_iff_of_henselian B q`. Use `.of_unique_max_ideal ⟨q, hq, fun n hn => (H n hn).1 ?_⟩` and prove the remaining obligations. Break down `IsIdempotentElem.iff_eq_zero_or_one.1 he with h | h` into its components or cases. Conclude with `absurd (h ▸ q.zero_mem) ((H q hq).2 rfl)`.

Rewrite using `[h]`. Conclude with `(Ideal.ne_top_iff_one _).1 hn.ne_top`.
-/
private theorem nearPoly_local (B S : Type) [CommRing B] [HenselianLocalRing B] [CommRing S] [IsDomain S]
    [Algebra B S] [Module.Finite B S] : IsLocalRing S := by
  obtain ⟨q, hq⟩ := Ideal.exists_maximal S
  obtain ⟨e, he, H⟩ := GlobalTheory.exists_idempotent_notMem_iff_of_henselian B q
  refine .of_unique_max_ideal ⟨q, hq, fun n hn => (H n hn).1 ?_⟩
  rcases IsIdempotentElem.iff_eq_zero_or_one.1 he with h | h
  · exact absurd (h ▸ q.zero_mem) ((H q hq).2 rfl)
  · rw [h]
    exact (Ideal.ne_top_iff_one _).1 hn.ne_top

/- English proof (translation)
Introduce `O B _ _ _ _ _ _ x d t v hd ht hv h`. Set `S` to `Algebra.adjoin B ({v} : Set (FractionRing B))`. Use `haveI : Module.Finite B S := Module.Finite.iff_fg.2 hv.fg_adjoin_singleton`. Use `haveI : IsLocalRing S := nearPoly_local B S`. Set `w : S` to `⟨v, Algebra.self_mem_adjoin_singleton B v⟩`.

Establish `hw : w ∈ maximalIdeal S`. Introduce `hu`. Take `⟨u, hu⟩` from `hu.exists_right_inv`. Establish `h1 : algebraMap B S (algebraMap O B d) * w = algebraMap B S t` using `Subtype.ext h`. Establish `h2 : algebraMap B S (algebraMap O B d) = algebraMap B S t * u`.

Rewrite using `[← h1, mul_assoc, hu, mul_one]`. Use `haveI : (RingHom.ker x).IsPrime := RingHom.ker_isPrime x`. Establish `hinj : Function.Injective (algebraMap B S)` using `fun a b e => IsFractionRing.injective B (FractionRing B) (congrArg Subtype.val e)`. Take `⟨Q, _, hQ⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := S) (RingHom.ker x) (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)`. Establish `h3 : t ∈ Q.comap (algebraMap B S)` using `by rw [hQ]; exact ht`.

Establish `h4 : algebraMap O B d ∈ Q.comap (algebraMap B S)`. Rewrite using `[Ideal.mem_comap, h2]`. Conclude with `Q.mul_mem_right _ h3`. Rewrite `h4` using `[hQ, RingHom.mem_ker, x.commutes]`. Conclude with `hd h4`.

Take `⟨p, hp, h0⟩` from `nilPoly (B := B) w hw`. Use `⟨p, hp, ?_⟩` and prove the remaining obligations. Use `aeval_algHom_apply S.val w p` as an intermediate fact. Rewrite `this` using `[h0, map_zero]`. Conclude with `this`.
-/
theorem UpperTheory.V.Ws.Pp.nearPoly :
    ∀ {O B : Type} [CommRing O] [IsDomain O] [CommRing B] [IsDomain B] [HenselianLocalRing B] [Algebra O B] (x : B →ₐ[O] O) (d : O) (t : B) (v : FractionRing B), d ≠ 0 → x t = 0 → IsIntegral B v → algebraMap B (FractionRing B) (algebraMap O B d) * v = algebraMap B (FractionRing B) t → ∃ p : B[X], Dist (maximalIdeal B) p ∧ aeval v p = 0 := by
  intro O B _ _ _ _ _ _ x d t v hd ht hv h
  let S := Algebra.adjoin B ({v} : Set (FractionRing B))
  haveI : Module.Finite B S := Module.Finite.iff_fg.2 hv.fg_adjoin_singleton
  haveI : IsLocalRing S := nearPoly_local B S
  let w : S := ⟨v, Algebra.self_mem_adjoin_singleton B v⟩
  have hw : w ∈ maximalIdeal S := by
    intro hu
    obtain ⟨u, hu⟩ := hu.exists_right_inv
    have h1 : algebraMap B S (algebraMap O B d) * w = algebraMap B S t := Subtype.ext h
    have h2 : algebraMap B S (algebraMap O B d) = algebraMap B S t * u := by
      rw [← h1, mul_assoc, hu, mul_one]
    haveI : (RingHom.ker x).IsPrime := RingHom.ker_isPrime x
    have hinj : Function.Injective (algebraMap B S) := fun a b e =>
      IsFractionRing.injective B (FractionRing B) (congrArg Subtype.val e)
    obtain ⟨Q, _, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := S) (RingHom.ker x)
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)
    have h3 : t ∈ Q.comap (algebraMap B S) := by rw [hQ]; exact ht
    have h4 : algebraMap O B d ∈ Q.comap (algebraMap B S) := by
      rw [Ideal.mem_comap, h2]
      exact Q.mul_mem_right _ h3
    rw [hQ, RingHom.mem_ker, x.commutes] at h4
    exact hd h4
  obtain ⟨p, hp, h0⟩ := nilPoly (B := B) w hw
  refine ⟨p, hp, ?_⟩
  have := aeval_algHom_apply S.val w p
  rw [h0, map_zero] at this
  exact this
