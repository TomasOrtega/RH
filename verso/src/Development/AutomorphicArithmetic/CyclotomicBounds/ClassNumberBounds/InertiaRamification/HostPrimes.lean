import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.HostDegree
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Places
import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.ResDeg

namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ} [NeZero N] {n d q₁ : ℕ} {ch ps χ : DirichletCharacter ℂ N}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h ψ hψ`. Conclude with `(MonoidHom.mem_ker).2 ((localPart_eq_one_iff l ψ).2.2 (h ψ hψ))`. Introduce `h ψ hψ`. Conclude with `(localPart_eq_one_iff l ψ).2.1 ((MonoidHom.mem_ker).1 (h hψ))`.
-/
private theorem hp_unr_iff (l : ℕ) [Fact l.Prime] (X : Subgroup (DirichletCharacter ℂ N)) :
    (∀ ψ ∈ X, ¬ l ∣ ψ.conductor) ↔ X ≤ (localPart N l).ker := by
  constructor
  · intro h ψ hψ
    exact (MonoidHom.mem_ker).2 ((localPart_eq_one_iff l ψ).2.2 (h ψ hψ))
  · intro h ψ hψ
    exact (localPart_eq_one_iff l ψ).2.1 ((MonoidHom.mem_ker).1 (h hψ))

/- English proof (translation)
The claim follows from `(hp_unr_iff l _).2 (sup_le ((hp_unr_iff l _).1 hX) ((hp_unr_iff l _).1 hY))`.
-/
private theorem hp_unr_sup (l : ℕ) [Fact l.Prime] {X Y : Subgroup (DirichletCharacter ℂ N)}
    (hX : ∀ ψ ∈ X, ¬ l ∣ ψ.conductor) (hY : ∀ ψ ∈ Y, ¬ l ∣ ψ.conductor) :
    ∀ ψ ∈ X ⊔ Y, ¬ l ∣ ψ.conductor :=
  (hp_unr_iff l _).2 (sup_le ((hp_unr_iff l _).1 hX) ((hp_unr_iff l _).1 hY))

/- English proof (translation)
The claim follows from `(hp_unr_iff l _).2 ((Subgroup.zpowers_le).2 ((MonoidHom.mem_ker).2 ((localPart_eq_one_iff l φ).2.2 h)))`.
-/
private theorem hp_unr_zpowers (l : ℕ) [Fact l.Prime] {φ : DirichletCharacter ℂ N}
    (h : ¬ l ∣ φ.conductor) : ∀ ψ ∈ Subgroup.zpowers φ, ¬ l ∣ ψ.conductor :=
  (hp_unr_iff l _).2 ((Subgroup.zpowers_le).2
    ((MonoidHom.mem_ker).2 ((localPart_eq_one_iff l φ).2.2 h)))

omit [NeZero N] in
/- English proof (translation)
Rewrite using `[Set.insert_eq, Subgroup.closure_union, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure]`.
-/
private theorem hp_closure_pair (ch ps : DirichletCharacter ℂ N) :
    Subgroup.closure ({ch, ps} : Set (DirichletCharacter ℂ N)) =
      Subgroup.zpowers ch ⊔ Subgroup.zpowers ps := by
  rw [Set.insert_eq, Subgroup.closure_union, Subgroup.zpowers_eq_closure,
    Subgroup.zpowers_eq_closure]

omit [NeZero N] in
/- English proof (translation)
Rewrite using `[h.2.2]`. Conclude with `fun h' => hne ((Nat.prime_dvd_prime_iff_eq hl hd).1 h')`.
-/
private theorem hp_not_dvd {l d : ℕ} (hl : l.Prime) (hd : d.Prime) (hne : l ≠ d)
    {ch : DirichletCharacter ℂ N} (h : IsImagQuad ch d) : ¬ l ∣ ch.conductor := by
  rw [h.2.2]
  exact fun h' => hne ((Nat.prime_dvd_prime_iff_eq hl hd).1 h')

omit [NeZero N] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨Subgroup.mem_sup_left (Subgroup.subset_closure (by simp)), Subgroup.mem_sup_left (Subgroup.subset_closure (by simp)), le_sup_of_le_right le_sup_left⟩`.
-/
private theorem hp_mem (n : ℕ) (ch ps χ : DirichletCharacter ℂ N) :
    ch ∈ hostChars n ch ps χ ∧ ps ∈ hostChars n ch ps χ ∧
      evenPart (condDvd N (4 * n)) ≤ hostChars n ch ps χ :=
  ⟨Subgroup.mem_sup_left (Subgroup.subset_closure (by simp)),
    Subgroup.mem_sup_left (Subgroup.subset_closure (by simp)),
    le_sup_of_le_right le_sup_left⟩

/- English proof (translation)
Apply `Nat.eq_of_mul_eq_mul_left hn` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem hp_arith1 {n f g r : ℕ} (hn : 0 < n) (h : n * f * g = 4 * n * r) :
    g * f = 4 * r := by
  apply Nat.eq_of_mul_eq_mul_left hn
  linarith

/- English proof (translation)
Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem hp_arith2 {f g r : ℕ} (h : 2 * g * f = 4 * r) : g * f = 2 * r := by
  linarith

/- English proof (translation)
Take `⟨s, o, -, hs, ho, hc, -, -⟩` from `h.card`. Take `⟨⟨e, he, rfl⟩, hN, hd, hd16, hq, hq8, hch, hps, hdχ, hqχ⟩` from `h`. Take `⟨m1, m2, m3⟩` from `hp_mem (2 ^ e) ch ps χ`. Establish `h4 : 4 * 2 ^ e = 2 ^ (e + 2)` using `by ring`. Establish `hF` using `(fieldCond_evenPart_condDvd_two_pow (N := N) (k := e + 2) (h4 ▸ hN) (by omega)).2`.

Rewrite `hF` using `[← h4, Nat.add_sub_cancel]`. Use `⟨?_, fun hχ => ?_⟩` and prove the remaining obligations. Establish `hdv : ramIdx 2 (evenPart (condDvd N (4 * 2 ^ e))) ∣ ramIdx 2 (hostChars (2 ^ e) ch ps χ)` using `Subgroup.card_dvd_of_le (Subgroup.map_mono m3)`. Rewrite `hdv` using `[hF.1]`. Then use the resulting hypothesis. Establish `u1` using `hp_not_dvd Nat.prime_two hd (by omega) hch`.

Establish `u2` using `hp_not_dvd Nat.prime_two hq (by omega) hps`. Establish `uE` using `hp_unr_sup 2 (hp_unr_zpowers 2 u1) (hp_unr_zpowers 2 u2)`. Establish `uS` using `hp_unr_sup 2 uE (hp_unr_zpowers 2 hχ)`. Establish `e1 : hostChars (2 ^ e) ch ps χ = (Subgroup.zpowers ch ⊔ Subgroup.zpowers ps ⊔ Subgroup.zpowers χ) ⊔ evenPart (condDvd N (4 * 2 ^ e))`. Rewrite using `[hostChars, hp_closure_pair]`.

The two sides agree by associativity and commutativity. Take `⟨v1, v2, -⟩` from `IsImagQuad.values hd hq (by omega) hq8 hch hps`. Establish `hr : ramIdx 2 (hostChars (2 ^ e) ch ps χ) = 2 ^ e`. Rewrite using `[e1, (resDeg_sup 2 _ _ uS).2.1, hF.1]`. Establish `hneg : orderOf (-1 : ℂ) = 2`.

Apply `orderOf_eq_prime` to reduce the goal to its premises. Evaluate the numerical expressions. Evaluate the numerical expressions. Establish `hf : resDeg 2 (hostChars (2 ^ e) ch ps χ) = Nat.lcm 2 (orderOf (χ.primitiveCharacter ((2 : ℕ) : ZMod χ.conductor)))`. Rewrite using `[e1, (resDeg_sup 2 _ _ uS).1, hF.2, Nat.lcm_one_right, (resDeg_sup 2 _ _ uE).1, (resDeg_sup 2 _ _ (hp_unr_zpowers 2 u1)).1, resDeg_zpowers 2 ch u1, resDeg_zpowers 2 ps u2, resDeg_zpowers 2 χ hχ, show ch.primitiveCharacter ((2 : ℕ) : ZMod ch.conductor) = 1 from v1, orderOf_one, Na …`.

Establish `hc0 : condExp 2 χ = 0` using `Nat.factorization_eq_zero_of_not_dvd hχ`. Establish `hs0 : s = 0` using `by omega`. Rewrite `ho` using `[hs0, pow_zero, one_mul]`. Establish `hp` using `ramIdx_mul_resDeg_mul_numPlaces 2 (hostChars (2 ^ e) ch ps χ)`. Rewrite `hp` using `[hr, hf, hc, ← ho]`.

Establish `hg : numPlaces 2 (hostChars (2 ^ e) ch ps χ) * Nat.lcm 2 (orderOf (χ.primitiveCharacter ((2 : ℕ) : ZMod χ.conductor))) = 4 * orderOf χ`. Conclude with `hp_arith1 (Nat.two_pow_pos e) hp`. Use `⟨hr, hf, hg, ?_⟩` and prove the remaining obligations. Rewrite `hg` using `[(split_of_splitsFor 2 _ m1 hch.2.1 v1).2.2.1]`. Conclude with `hp_arith2 hg`.
-/
theorem HostData.at_two (h : HostData n d q₁ ch ps χ) :
    n ∣ ramIdx 2 (hostChars n ch ps χ) ∧
      (¬ 2 ∣ χ.conductor →
        ramIdx 2 (hostChars n ch ps χ) = n ∧
        resDeg 2 (hostChars n ch ps χ) =
          Nat.lcm 2 (orderOf (χ.primitiveCharacter ((2 : ℕ) : ZMod χ.conductor))) ∧
        numPlaces 2 (hostChars n ch ps χ) *
          Nat.lcm 2 (orderOf (χ.primitiveCharacter ((2 : ℕ) : ZMod χ.conductor))) =
            4 * orderOf χ ∧
        numPlaces 2 (evenPart (hostChars n ch ps χ)) *
          Nat.lcm 2 (orderOf (χ.primitiveCharacter ((2 : ℕ) : ZMod χ.conductor))) =
            2 * orderOf χ) := by
  obtain ⟨s, o, -, hs, ho, hc, -, -⟩ := h.card
  obtain ⟨⟨e, he, rfl⟩, hN, hd, hd16, hq, hq8, hch, hps, hdχ, hqχ⟩ := h
  obtain ⟨m1, m2, m3⟩ := hp_mem (2 ^ e) ch ps χ
  have h4 : 4 * 2 ^ e = 2 ^ (e + 2) := by ring
  have hF := (fieldCond_evenPart_condDvd_two_pow (N := N) (k := e + 2) (h4 ▸ hN) (by omega)).2
  rw [← h4, Nat.add_sub_cancel] at hF
  refine ⟨?_, fun hχ => ?_⟩
  · have hdv : ramIdx 2 (evenPart (condDvd N (4 * 2 ^ e))) ∣
        ramIdx 2 (hostChars (2 ^ e) ch ps χ) :=
      Subgroup.card_dvd_of_le (Subgroup.map_mono m3)
    rwa [hF.1] at hdv
  have u1 := hp_not_dvd Nat.prime_two hd (by omega) hch
  have u2 := hp_not_dvd Nat.prime_two hq (by omega) hps
  have uE := hp_unr_sup 2 (hp_unr_zpowers 2 u1) (hp_unr_zpowers 2 u2)
  have uS := hp_unr_sup 2 uE (hp_unr_zpowers 2 hχ)
  have e1 : hostChars (2 ^ e) ch ps χ =
      (Subgroup.zpowers ch ⊔ Subgroup.zpowers ps ⊔ Subgroup.zpowers χ) ⊔
        evenPart (condDvd N (4 * 2 ^ e)) := by
    rw [hostChars, hp_closure_pair]; ac_rfl
  obtain ⟨v1, v2, -⟩ := IsImagQuad.values hd hq (by omega) hq8 hch hps
  have hr : ramIdx 2 (hostChars (2 ^ e) ch ps χ) = 2 ^ e := by
    rw [e1, (resDeg_sup 2 _ _ uS).2.1, hF.1]
  have hneg : orderOf (-1 : ℂ) = 2 := by
    apply orderOf_eq_prime
    · norm_num
    · norm_num
  have hf : resDeg 2 (hostChars (2 ^ e) ch ps χ) =
      Nat.lcm 2 (orderOf (χ.primitiveCharacter ((2 : ℕ) : ZMod χ.conductor))) := by
    rw [e1, (resDeg_sup 2 _ _ uS).1, hF.2, Nat.lcm_one_right, (resDeg_sup 2 _ _ uE).1,
      (resDeg_sup 2 _ _ (hp_unr_zpowers 2 u1)).1, resDeg_zpowers 2 ch u1, resDeg_zpowers 2 ps u2,
      resDeg_zpowers 2 χ hχ,
      show ch.primitiveCharacter ((2 : ℕ) : ZMod ch.conductor) = 1 from v1, orderOf_one,
      Nat.lcm_one_left, v2, hneg]
  have hc0 : condExp 2 χ = 0 := Nat.factorization_eq_zero_of_not_dvd hχ
  have hs0 : s = 0 := by omega
  rw [hs0, pow_zero, one_mul] at ho
  have hp := ramIdx_mul_resDeg_mul_numPlaces 2 (hostChars (2 ^ e) ch ps χ)
  rw [hr, hf, hc, ← ho] at hp
  have hg : numPlaces 2 (hostChars (2 ^ e) ch ps χ) *
      Nat.lcm 2 (orderOf (χ.primitiveCharacter ((2 : ℕ) : ZMod χ.conductor))) =
        4 * orderOf χ := by
    exact hp_arith1 (Nat.two_pow_pos e) hp
  refine ⟨hr, hf, hg, ?_⟩
  rw [(split_of_splitsFor 2 _ m1 hch.2.1 v1).2.2.1] at hg
  exact hp_arith2 hg

end KStar.Ram
