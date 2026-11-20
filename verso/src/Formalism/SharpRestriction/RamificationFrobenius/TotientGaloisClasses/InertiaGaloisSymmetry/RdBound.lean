import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.RdArith

open ArithmeticFunction Finset

noncomputable section

namespace Formalism.HC.Der.Rd

variable {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ)

def SS : ℝ := ∑ m ∈ N.divisors, vonMangoldt m * rho U (N / m)

/- English proof (translation)
Establish `h1 : (s : Set G) ⊆ (H : Set G)` using `fun x hx => hs x hx`. Establish `h2` using `Set.ncard_le_ncard h1 (Set.toFinite _)`. Rewrite `h2` using `[Set.ncard_coe_finset]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem card_le_natCard_subgroup_of_forall_mem {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (s : Finset G) (hs : ∀ x ∈ s, x ∈ H) : s.card ≤ Nat.card H := by
  have h1 : (s : Set G) ⊆ (H : Set G) := fun x hx => hs x hx
  have h2 := Set.ncard_le_ncard h1 (Set.toFinite _)
  rw [Set.ncard_coe_finset] at h2
  calc s.card ≤ (H : Set G).ncard := h2
    _ = Nat.card H := (Nat.card_coe_set_eq (H : Set G)).symm

/- English proof (translation)
Establish `h` using `mem_KK.mp hu`. Establish `h' : ((u : ZMod N).val : ZMod N) = ((1 : ℕ) : ZMod N)`. Rewrite using `[ZMod.natCast_eq_natCast_iff]`. Conclude with `h`. Rewrite `h'` using `[ZMod.natCast_zmod_val, Nat.cast_one]`.

Conclude with `Units.ext h'`.
-/
private theorem eq_one_of_mem_KK_self {u : (ZMod N)ˣ}
    (hu : u ∈ KK N N) : u = 1 := by
  have h := mem_KK.mp hu
  have h' : ((u : ZMod N).val : ZMod N) = ((1 : ℕ) : ZMod N) := by
    rw [ZMod.natCast_eq_natCast_iff]; exact h
  rw [ZMod.natCast_zmod_val, Nat.cast_one] at h'
  exact Units.ext h'

/- English proof (translation)
Establish `hN0 : N ≠ 0` using `NeZero.ne N`. Establish `hex : ∃ f, f ∣ N ∧ ∀ u ∈ KK N f, u ∈ U` using `⟨N, dvd_rfl, fun u hu => by rw [eq_one_of_mem_KK_self hu]; exact U.one_mem⟩`. Take `⟨c, hc, hcmin⟩ : ∃ c, (c ∣ N ∧ ∀ u ∈ KK N c, u ∈ U) ∧ ∀ f, (f ∣ N ∧ ∀ u ∈ KK N f, u ∈ U) → c ≤ f` from `⟨Nat.find hex, Nat.find_spec hex, fun f hf => Nat.find_min' hex hf⟩`. Establish `hcpos : 0 < c` using `Nat.pos_of_dvd_of_pos hc.1 (Nat.pos_of_ne_zero hN0)`. Establish `hcdvd : ∀ f, f ∣ N → (∀ u ∈ KK N f, u ∈ U) → c ∣ f`.

Introduce `f hf hfU`. Establish `hle : c ≤ Nat.gcd c f` using `hcmin _ ⟨(Nat.gcd_dvd_left c f).trans hc.1, KK_gcd U hc.1 hf hc.2 hfU⟩`. Establish `heq : Nat.gcd c f = c` using `le_antisymm (Nat.le_of_dvd hcpos (Nat.gcd_dvd_left c f)) hle`. Rewrite using `[← heq]`. Conclude with `Nat.gcd_dvd_right c f`.

Take `⟨k, hk⟩` from `hc.1`. Establish `hk0 : k ≠ 0` using `by intro h0; apply hN0; rw [hk, h0, mul_zero]`. Establish `hKpos : 0 < (KK N c).card` using `Finset.card_pos.mpr ⟨1, one_mem_KK hc.1⟩`. Establish `hKc` using `card_KK (N := N) hc.1`. Establish `hKU : (KK N c).card ≤ Nat.card U` using `card_le_natCard_subgroup_of_forall_mem U _ (fun u hu => hc.2 u hu)`.

Establish `hGU : Nat.card U * U.index = N.totient`. Rewrite using `[Subgroup.card_mul_index, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]`. Establish `hidx : U.index ≤ c.totient`. Establish `h1 : U.index * (KK N c).card ≤ c.totient * (KK N c).card`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `Nat.le_of_mul_le_mul_right h1 hKpos`. Establish `hidx0 : 0 < U.index` using `Nat.pos_of_ne_zero (fun h => by`. Rewrite `hGU` using `[h, mul_zero]`. Conclude with `(Nat.totient_pos.mpr (Nat.pos_of_ne_zero hN0)).ne' hGU.symm)`. Establish `hlog1 : Real.log U.index ≤ Real.log c`.

Apply `Real.log_le_log (by exact_mod_cast hidx0)` to reduce the goal to its premises. Conclude with `hidx.trans (Nat.totient_le c)` after adjusting the coercions. Establish `hfilt : N.divisors.filter (fun m => c ∣ N / m) = k.divisors`. Use extensionality with `m`. Simplify using `only [Finset.mem_filter, Nat.mem_divisors]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨hm, -⟩, hcm⟩`. Use `⟨?_, hk0⟩` and prove the remaining obligations. Take `⟨j, hj⟩` from `hcm`. Establish `h1 : N = m * (c * j)` using `by rw [← hj, Nat.mul_div_cancel' hm]`.

Establish `h2 : c * k = c * (m * j)` using `by rw [← hk, h1]; ring`. Conclude with `⟨j, Nat.eq_of_mul_eq_mul_left hcpos h2⟩`. Introduce and unpack `⟨⟨j, hj⟩, -⟩`. Establish `hm0 : 0 < m` using `Nat.pos_of_dvd_of_pos ⟨j, hj⟩ (Nat.pos_of_ne_zero hk0)`. Use `⟨⟨?_, hN0⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[hk, hj]; exact ⟨c * j, by ring⟩`. Establish `h1 : N / m = c * j`. Rewrite using `[hk, hj, show c * (m * j) = m * (c * j) by ring, Nat.mul_div_cancel_left _ hm0]`. Rewrite using `[h1]`. Conclude with `dvd_mul_right c j`.

Establish `hsplit : Real.log k + ∑ m ∈ N.divisors.filter (fun m => ¬ c ∣ N / m), vonMangoldt m = Real.log N`. Rewrite using `[← vonMangoldt_sum (n := k), ← hfilt, Finset.sum_filter_add_sum_filter_not, vonMangoldt_sum]`. Establish `hlogN : Real.log (N : ℝ) = Real.log c + Real.log k`. Rewrite using `[hk, Nat.cast_mul, Real.log_mul (by exact_mod_cast hcpos.ne') (by exact_mod_cast hk0)]`. Establish `hbound : ∑ m ∈ N.divisors.filter (fun m => ¬ c ∣ N / m), vonMangoldt m ≤ ∑ m ∈ N.divisors, 2 * (vonMangoldt m * rho U (N / m))`.

Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `m hm`. Rewrite `hm` using `[Finset.mem_filter, Nat.mem_divisors]`. Establish `hmN : N / m ∣ N` using `Nat.div_dvd_of_dvd hm.1.1`.

Establish `hex' : ∃ u ∈ KK N (N / m), u ∉ U`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hm.2 (hcdvd _ hmN hcon)`. Establish `h12` using `half_le_rho U hmN hex'`.

Establish `hΛ : 0 ≤ vonMangoldt m` using `vonMangoldt_nonneg`. Use the polynomial consequences of the given equalities and inequalities. Use `_ ≤ _ := by`. Apply `Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)` to reduce the goal to its premises. Introduce `m _ _`.

Conclude with `mul_nonneg zero_le_two (mul_nonneg vonMangoldt_nonneg (rho_nonneg U _))`. Unfold `SS`. Rewrite using `[Finset.mul_sum]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem log_index_le : Real.log U.index ≤ 2 * SS U := by
  classical
  have hN0 : N ≠ 0 := NeZero.ne N
  have hex : ∃ f, f ∣ N ∧ ∀ u ∈ KK N f, u ∈ U :=
    ⟨N, dvd_rfl, fun u hu => by rw [eq_one_of_mem_KK_self hu]; exact U.one_mem⟩
  obtain ⟨c, hc, hcmin⟩ : ∃ c, (c ∣ N ∧ ∀ u ∈ KK N c, u ∈ U) ∧
      ∀ f, (f ∣ N ∧ ∀ u ∈ KK N f, u ∈ U) → c ≤ f :=
    ⟨Nat.find hex, Nat.find_spec hex, fun f hf => Nat.find_min' hex hf⟩
  have hcpos : 0 < c := Nat.pos_of_dvd_of_pos hc.1 (Nat.pos_of_ne_zero hN0)
  have hcdvd : ∀ f, f ∣ N → (∀ u ∈ KK N f, u ∈ U) → c ∣ f := by
    intro f hf hfU
    have hle : c ≤ Nat.gcd c f :=
      hcmin _ ⟨(Nat.gcd_dvd_left c f).trans hc.1, KK_gcd U hc.1 hf hc.2 hfU⟩
    have heq : Nat.gcd c f = c := le_antisymm (Nat.le_of_dvd hcpos (Nat.gcd_dvd_left c f)) hle
    rw [← heq]; exact Nat.gcd_dvd_right c f
  obtain ⟨k, hk⟩ := hc.1
  have hk0 : k ≠ 0 := by intro h0; apply hN0; rw [hk, h0, mul_zero]
  have hKpos : 0 < (KK N c).card :=
    Finset.card_pos.mpr ⟨1, one_mem_KK hc.1⟩
  have hKc := card_KK (N := N) hc.1
  have hKU : (KK N c).card ≤ Nat.card U :=
    card_le_natCard_subgroup_of_forall_mem U _ (fun u hu => hc.2 u hu)
  have hGU : Nat.card U * U.index = N.totient := by
    rw [Subgroup.card_mul_index, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hidx : U.index ≤ c.totient := by
    have h1 : U.index * (KK N c).card ≤ c.totient * (KK N c).card := by
      calc U.index * (KK N c).card ≤ U.index * Nat.card U := Nat.mul_le_mul_left _ hKU
        _ = N.totient := by rw [mul_comm, hGU]
        _ = c.totient * (KK N c).card := by rw [← hKc, mul_comm]
    exact Nat.le_of_mul_le_mul_right h1 hKpos
  have hidx0 : 0 < U.index := Nat.pos_of_ne_zero (fun h => by
    rw [h, mul_zero] at hGU
    exact (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hN0)).ne' hGU.symm)
  have hlog1 : Real.log U.index ≤ Real.log c := by
    apply Real.log_le_log (by exact_mod_cast hidx0)
    exact_mod_cast hidx.trans (Nat.totient_le c)
  have hfilt : N.divisors.filter (fun m => c ∣ N / m) = k.divisors := by
    ext m
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hm, -⟩, hcm⟩
      refine ⟨?_, hk0⟩
      obtain ⟨j, hj⟩ := hcm
      have h1 : N = m * (c * j) := by rw [← hj, Nat.mul_div_cancel' hm]
      have h2 : c * k = c * (m * j) := by rw [← hk, h1]; ring
      exact ⟨j, Nat.eq_of_mul_eq_mul_left hcpos h2⟩
    · rintro ⟨⟨j, hj⟩, -⟩
      have hm0 : 0 < m := Nat.pos_of_dvd_of_pos ⟨j, hj⟩ (Nat.pos_of_ne_zero hk0)
      refine ⟨⟨?_, hN0⟩, ?_⟩
      · rw [hk, hj]; exact ⟨c * j, by ring⟩
      · have h1 : N / m = c * j := by
          rw [hk, hj, show c * (m * j) = m * (c * j) by ring, Nat.mul_div_cancel_left _ hm0]
        rw [h1]; exact dvd_mul_right c j
  have hsplit : Real.log k + ∑ m ∈ N.divisors.filter (fun m => ¬ c ∣ N / m), vonMangoldt m
      = Real.log N := by
    rw [← vonMangoldt_sum (n := k), ← hfilt, Finset.sum_filter_add_sum_filter_not, vonMangoldt_sum]
  have hlogN : Real.log (N : ℝ) = Real.log c + Real.log k := by
    rw [hk, Nat.cast_mul, Real.log_mul (by exact_mod_cast hcpos.ne') (by exact_mod_cast hk0)]
  have hbound : ∑ m ∈ N.divisors.filter (fun m => ¬ c ∣ N / m), vonMangoldt m
      ≤ ∑ m ∈ N.divisors, 2 * (vonMangoldt m * rho U (N / m)) := by
    calc _ ≤ ∑ m ∈ N.divisors.filter (fun m => ¬ c ∣ N / m),
          2 * (vonMangoldt m * rho U (N / m)) := by
          apply Finset.sum_le_sum
          intro m hm
          rw [Finset.mem_filter, Nat.mem_divisors] at hm
          have hmN : N / m ∣ N := Nat.div_dvd_of_dvd hm.1.1
          have hex' : ∃ u ∈ KK N (N / m), u ∉ U := by
            by_contra hcon
            push_neg at hcon
            exact hm.2 (hcdvd _ hmN hcon)
          have h12 := half_le_rho U hmN hex'
          have hΛ : 0 ≤ vonMangoldt m := vonMangoldt_nonneg
          nlinarith
      _ ≤ _ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro m _ _
          exact mul_nonneg zero_le_two
            (mul_nonneg vonMangoldt_nonneg (rho_nonneg U _))
  unfold SS
  rw [Finset.mul_sum]
  linarith

/- English proof (translation)
Establish `hN0 : N ≠ 0` using `NeZero.ne N`. Establish `hT : (0 : ℝ) < N.totient` using `by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hN0)`. Establish `hqD : q ∈ N.divisors` using `Nat.mem_divisors.mpr ⟨hqN, hN0⟩`. Establish `hdD : d ∈ N.divisors.erase q` using `Finset.mem_erase.mpr ⟨hqd.symm, Nat.mem_divisors.mpr ⟨hdN, hN0⟩⟩`. Establish `hRsub : ∀ m ∈ (N.divisors.erase q).erase d, m ∣ N` using `fun m hm => Nat.dvd_of_mem_divisors (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hm))`.

Establish `hterm : ∀ m ∈ (N.divisors.erase q).erase d, vonMangoldt m * rho U (N / m) ≤ vonMangoldt m - vonMangoldt m * ((N / m).totient : ℝ) / N.totient`. Introduce `m hm`. Establish `h1` using `mul_le_mul_of_nonneg_left (rho_le U (Nat.div_dvd_of_dvd (hRsub m hm))) (vonMangoldt_nonneg (n := m))`. Combine the equalities or inequalities in the displayed calculation. Establish `h2sub : N.divisors.filter (fun m => 2 ∣ m) ⊆ (N.divisors.erase q).erase d`.

Introduce `m hm`. Rewrite `hm` using `[Finset.mem_filter]`. Rewrite using `[Finset.mem_erase, Finset.mem_erase]`. Conclude with `⟨fun h => hd2 (h ▸ hm.2), fun h => hq2 (h ▸ hm.2), hm.1⟩`. Establish `h2val : ∑ m ∈ N.divisors.filter (fun m => 2 ∣ m), vonMangoldt m * ((N / m).totient : ℝ) / N.totient = Real.log 2`.

Establish `h` using `weight_sum hN0 h2 (by norm_num : (2 : ℕ) ≠ 1)`. Rewrite `h` using `[vonMangoldt_apply_prime Nat.prime_two, Nat.totient_two, Nat.cast_one, div_one, Nat.cast_ofNat]`. Rewrite using `[← Finset.sum_div, h, div_eq_iff hT.ne']`. Expand and normalize the polynomial expressions, which then agree. Establish `hgR : Real.log 2 ≤ ∑ m ∈ (N.divisors.erase q).erase d, vonMangoldt m * ((N / m).totient : ℝ) / N.totient`.

Rewrite using `[← h2val]`. Apply `Finset.sum_le_sum_of_subset_of_nonneg h2sub` to reduce the goal to its premises. Introduce `m _ _`. Conclude with `div_nonneg (mul_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)) (Nat.cast_nonneg _)`. Establish `hRsum : ∑ m ∈ (N.divisors.erase q).erase d, vonMangoldt m * rho U (N / m) ≤ ∑ m ∈ (N.divisors.erase q).erase d, vonMangoldt m - ∑ m ∈ (N.divisors.erase q).erase d, vonMangoldt m * ((N / m).totient : ℝ) / N.totient`.

Rewrite using `[← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_le_sum hterm`. Establish `hΛsum : Real.log N = vonMangoldt q + (vonMangoldt d + ∑ m ∈ (N.divisors.erase q).erase d, vonMangoldt m)`. Rewrite using `[← vonMangoldt_sum, ← Finset.add_sum_erase _ _ hqD, ← Finset.add_sum_erase _ _ hdD]`. Establish `hwsplit : SS U = vonMangoldt q * rho U (N / q) + (vonMangoldt d * rho U (N / d) + ∑ m ∈ (N.divisors.erase q).erase d, vonMangoldt m * rho U (N / m))`.

Unfold `SS`. Rewrite using `[← Finset.add_sum_erase _ _ hqD, ← Finset.add_sum_erase _ _ hdD]`. Establish `hqt : vonMangoldt q * rho U (N / q) ≤ vonMangoldt q * (1 / 2)` using `mul_le_mul_of_nonneg_left rq vonMangoldt_nonneg`. Establish `hdt : vonMangoldt d * rho U (N / d) ≤ vonMangoldt d * (1 / 2)` using `mul_le_mul_of_nonneg_left rd vonMangoldt_nonneg`. Establish `hΛq : vonMangoldt q = Real.log q` using `vonMangoldt_apply_prime hq`.

Establish `hΛd : vonMangoldt d = Real.log d` using `vonMangoldt_apply_prime hd`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem SS_le {q d : ℕ} (h2 : 2 ∣ N) (hq : q.Prime) (hd : d.Prime) (hqN : q ∣ N) (hdN : d ∣ N) (hq2 : ¬ 2 ∣ q)
    (hd2 : ¬ 2 ∣ d) (hqd : q ≠ d) (rq : rho U (N / q) ≤ 1 / 2) (rd : rho U (N / d) ≤ 1 / 2) :
    SS U ≤ Real.log N - Real.log 2 - Real.log q / 2 - Real.log d / 2 := by
  classical
  have hN0 : N ≠ 0 := NeZero.ne N
  have hT : (0 : ℝ) < N.totient := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hN0)
  have hqD : q ∈ N.divisors := Nat.mem_divisors.mpr ⟨hqN, hN0⟩
  have hdD : d ∈ N.divisors.erase q :=
    Finset.mem_erase.mpr ⟨hqd.symm, Nat.mem_divisors.mpr ⟨hdN, hN0⟩⟩
  have hRsub : ∀ m ∈ (N.divisors.erase q).erase d, m ∣ N := fun m hm =>
    Nat.dvd_of_mem_divisors (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hm))
  have hterm : ∀ m ∈ (N.divisors.erase q).erase d,
      vonMangoldt m * rho U (N / m)
        ≤ vonMangoldt m - vonMangoldt m * ((N / m).totient : ℝ) / N.totient := by
    intro m hm
    have h1 := mul_le_mul_of_nonneg_left
      (rho_le U (Nat.div_dvd_of_dvd (hRsub m hm))) (vonMangoldt_nonneg (n := m))
    calc _ ≤ _ := h1
      _ = _ := by ring
  have h2sub : N.divisors.filter (fun m => 2 ∣ m) ⊆ (N.divisors.erase q).erase d := by
    intro m hm
    rw [Finset.mem_filter] at hm
    rw [Finset.mem_erase, Finset.mem_erase]
    exact ⟨fun h => hd2 (h ▸ hm.2), fun h => hq2 (h ▸ hm.2), hm.1⟩
  have h2val : ∑ m ∈ N.divisors.filter (fun m => 2 ∣ m),
      vonMangoldt m * ((N / m).totient : ℝ) / N.totient = Real.log 2 := by
    have h := weight_sum hN0 h2 (by norm_num : (2 : ℕ) ≠ 1)
    rw [vonMangoldt_apply_prime Nat.prime_two, Nat.totient_two, Nat.cast_one, div_one,
      Nat.cast_ofNat] at h
    rw [← Finset.sum_div, h, div_eq_iff hT.ne']
    ring
  have hgR : Real.log 2 ≤ ∑ m ∈ (N.divisors.erase q).erase d,
      vonMangoldt m * ((N / m).totient : ℝ) / N.totient := by
    rw [← h2val]
    apply Finset.sum_le_sum_of_subset_of_nonneg h2sub
    intro m _ _
    exact div_nonneg (mul_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hRsum : ∑ m ∈ (N.divisors.erase q).erase d, vonMangoldt m * rho U (N / m)
      ≤ ∑ m ∈ (N.divisors.erase q).erase d, vonMangoldt m
        - ∑ m ∈ (N.divisors.erase q).erase d, vonMangoldt m * ((N / m).totient : ℝ) / N.totient := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_le_sum hterm
  have hΛsum : Real.log N
      = vonMangoldt q + (vonMangoldt d + ∑ m ∈ (N.divisors.erase q).erase d, vonMangoldt m) := by
    rw [← vonMangoldt_sum, ← Finset.add_sum_erase _ _ hqD, ← Finset.add_sum_erase _ _ hdD]
  have hwsplit : SS U
      = vonMangoldt q * rho U (N / q) + (vonMangoldt d * rho U (N / d)
        + ∑ m ∈ (N.divisors.erase q).erase d, vonMangoldt m * rho U (N / m)) := by
    unfold SS
    rw [← Finset.add_sum_erase _ _ hqD, ← Finset.add_sum_erase _ _ hdD]
  have hqt : vonMangoldt q * rho U (N / q) ≤ vonMangoldt q * (1 / 2) :=
    mul_le_mul_of_nonneg_left rq vonMangoldt_nonneg
  have hdt : vonMangoldt d * rho U (N / d) ≤ vonMangoldt d * (1 / 2) :=
    mul_le_mul_of_nonneg_left rd vonMangoldt_nonneg
  have hΛq : vonMangoldt q = Real.log q := vonMangoldt_apply_prime hq
  have hΛd : vonMangoldt d = Real.log d := vonMangoldt_apply_prime hd
  linarith

/- English proof (translation)
Rewrite using `[← ZMod.cast_eq_val]`. Both sides reduce to the same expression.
-/
private theorem coe_unitsMap_eq_cast_val_of_dvd_neZero {m n : ℕ} [NeZero m] (h : n ∣ m) (u : (ZMod m)ˣ) :
    ((ZMod.unitsMap h u : (ZMod n)ˣ) : ZMod n) = ((u : ZMod m).val : ZMod n) := by
  rw [← ZMod.cast_eq_val]; rfl

/- English proof (translation)
Use `open Classical in`. Establish `card_filter_mem_le_lemma_6 {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ) {e M i : ℕ} (hM : Nat.Coprime 2 M) (hN : 2 ^ (e + 2) * M ∣ N) (hi : i ≤ e + 2) (hU : ∀ u ∈ U, ZMod.unitsMap ((dvd_mul_right _ M).trans hN) u = 1 ∨ ZMod.unitsMap ((dvd_mul_right _ M).trans hN) u = -1) : ((KK N …`. Establish `h2 : 2 ^ (e + 2) ∣ N` using `(dvd_mul_right _ M).trans hN`. Establish `hMN : M ∣ N` using `(dvd_mul_left M _).trans hN`. Establish `hcop : Nat.Coprime (2 ^ (e + 2)) M` using `Nat.Coprime.pow_left _ hM`.

Establish `hA : ∀ v : (ZMod N)ˣ, v ∈ (ZMod.unitsMap hMN).ker → ZMod.unitsMap h2 v = 1 → v ∈ KK N (2 ^ (e + 2) * M)`. Introduce `v hv1 hv2`. Rewrite using `[mem_KK]`. Rewrite `hv1` using `[mem_ker_iff]`. Establish `hv2'` using `(mem_ker_iff h2 v).mp (MonoidHom.mem_ker.mpr hv2)`.

Conclude with `(Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hv2', hv1⟩`. Establish `hKM : ∀ u ∈ KK N (2 ^ i * M), u ∈ (ZMod.unitsMap hMN).ker`. Introduce `u hu`. Rewrite using `[mem_ker_iff]`. Conclude with `Nat.ModEq.of_mul_left (2 ^ i) (mem_KK.mp hu)`.

Establish `hneg : 2 ≤ i → ∀ u ∈ KK N (2 ^ i * M), ZMod.unitsMap h2 u ≠ -1`. Introduce `hi2 u hu hneg1`. Establish `hval` using `congrArg Units.val hneg1`. Rewrite `hval` using `[coe_unitsMap_eq_cast_val_of_dvd_neZero, Units.val_neg, Units.val_one]`. Establish `h1 : (((u : ZMod N).val + 1 : ℕ) : ZMod (2 ^ (e + 2))) = 0` using `by push_cast; rw [hval]; ring`.

Rewrite `h1` using `[CharP.cast_eq_zero_iff (ZMod (2 ^ (e + 2))) (2 ^ (e + 2))]`. Establish `h4 : 4 ∣ (u : ZMod N).val + 1`. Establish `h5` using `(pow_dvd_pow 2 (by omega : 2 ≤ e + 2)).trans h1`. Simplify using `using h5`. Establish `h4' : (u : ZMod N).val ≡ 1 [MOD 4]`.

Establish `h6` using `Nat.ModEq.of_dvd ((pow_dvd_pow 2 hi2).trans (dvd_mul_right _ M)) (mem_KK.mp hu)`. Simplify using `using h6`. Unfold `Nat.ModEq at h4'`. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `hi2 : i < 2`.

Rewrite using `[if_pos hi2]`. Distinguish the cases in `hw : ∃ w ∈ (KK N (2 ^ i * M)).filter (fun u => u ∈ U), ZMod.unitsMap h2 w = -1`. Take `⟨w, hwH, hw1⟩` from `hw`. Rewrite `hwH` using `[Finset.mem_filter]`. Establish `hsub : (KK N (2 ^ i * M)).filter (fun u => u ∈ U) ⊆ KK N (2 ^ (e + 2) * M) ∪ (KK N (2 ^ (e + 2) * M)).image (fun x => w * x)`.

Introduce `u hu`. Rewrite `hu` using `[Finset.mem_filter]`. Break down `hU u hu.2 with h1 | h1` into its components or cases. Conclude with `Finset.mem_union_left _ (hA u (hKM u hu.1) h1)`. Apply `Finset.mem_union_right` to reduce the goal to its premises.

Rewrite using `[Finset.mem_image]`. Use `⟨w⁻¹ * u, hA _ ?_ ?_, mul_inv_cancel_left w u⟩` and prove the remaining obligations. Conclude with `Subgroup.mul_mem _ (Subgroup.inv_mem _ (hKM w hwH.1)) (hKM u hu.1)`. Rewrite using `[map_mul, map_inv, hw1, h1, inv_mul_cancel]`. Combine the equalities or inequalities in the displayed calculation.

Use `push_neg at hw`. Combine the equalities or inequalities in the displayed calculation. Rewrite `hu` using `[Finset.mem_filter]`. Break down `hU u hu.2 with h1 | h1` into its components or cases. Conclude with `hA u (hKM u hu.1) h1`.

Conclude with `absurd h1 (hw u (Finset.mem_filter.mpr hu)))`. Use `_ ≤ 2 * _ := by omega`. Rewrite using `[if_neg hi2]`. Combine the equalities or inequalities in the displayed calculation. Rewrite `hu` using `[Finset.mem_filter]`.

Break down `hU u hu.2 with h1 | h1` into its components or cases. Conclude with `hA u (hKM u hu.1) h1`. Conclude with `absurd h1 (hneg (by omega) u hu.1))`. Use `_ = 1 * _ := (one_mul _).symm`. Establish `hf : 2 ^ i * M ∣ N` using `(Nat.mul_dvd_mul_right (pow_dvd_pow 2 hi) M).trans hN`.

Establish `hcard` using `card_filter_mem_le_lemma_6 U hM hN hi hU`. Establish `hA` using `card_KK (N := N) hN`. Establish `hApos : 0 < (KK N (2 ^ (e + 2) * M)).card` using `Finset.card_pos.mpr ⟨1, one_mem_KK hN⟩`. Establish `hφf : (2 ^ i * M).totient = (2 ^ i).totient * M.totient` using `Nat.totient_mul (Nat.Coprime.pow_left _ hM)`. Establish `hφL : (2 ^ (e + 2) * M).totient = 2 ^ (e + 1) * M.totient`.

Rewrite using `[Nat.totient_mul (Nat.Coprime.pow_left _ hM), show e + 2 = e + 1 + 1 from rfl, Nat.totient_prime_pow_succ Nat.prime_two]`. Evaluate the numerical expressions. Establish `hMpos : 0 < M.totient` using `Nat.totient_pos.mpr (Nat.pos_of_dvd_of_pos ((dvd_mul_left M _).trans hN) (Nat.pos_of_ne_zero (NeZero.ne N)))`. Establish `hT : (N.totient : ℝ) = (KK N (2 ^ (e + 2) * M)).card * (2 ^ (e + 1) * M.totient)`. Rewrite using `[← hA, hφL]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hkey : (((KK N (2 ^ i * M)).filter fun u => u ∈ U).card : ℝ) * (2 ^ i).totient ≤ (((2 ^ i).totient : ℝ) + if i < 2 then 1 else 0) * (KK N (2 ^ (e + 2) * M)).card`. Distinguish the cases in `hi2 : i < 2`. Rewrite `hcard`, the goal using `[if_pos hi2]`.

Apply the tactic sequence `have ht : (2 ^ i).totient = 1 := by interval_cases i <;> simp`. Rewrite using `[ht]`. Establish `: (((KK N (2 ^ i * M)).filter fun u => u ∈ U).card : ℝ) ≤ 2 * (KK N (2 ^ (e + 2) * M)).card` using `by exact_mod_cast hcard`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite `hcard`, the goal using `[if_neg hi2]`. Establish `: (((KK N (2 ^ i * M)).filter fun u => u ∈ U).card : ℝ) ≤ (KK N (2 ^ (e + 2) * M)).card`. Use `hcard` as an intermediate fact. Rewrite `this` using `[one_mul]`. Conclude with `this` after adjusting the coercions.

Establish `ht0 : (0 : ℝ) ≤ (2 ^ i).totient` using `Nat.cast_nonneg _`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right this ht0]`. Rewrite using `[rho_eq U hf, hφf, hT]`. Use `push_cast`. Establish `ha : (0 : ℝ) < (KK N (2 ^ (e + 2) * M)).card` using `by exact_mod_cast hApos`.

Establish `hs : (0 : ℝ) < M.totient` using `by exact_mod_cast hMpos`. Establish `hp : (0 : ℝ) < 2 ^ (e + 1)` using `by positivity`. It suffices to establish `h : (((KK N (2 ^ i * M)).filter fun u => u ∈ U).card : ℝ) * (((2 ^ i).totient : ℝ) * M.totient) / ((KK N (2 ^ (e + 2) * M)).card * (2 ^ (e + 1) * M.totient)) ≤ (((2 ^ i).totient : ℝ) + if i < 2 then 1 else 0) / 2 ^ (e + 1) by linarith`. Rewrite using `[div_le_div_iff₀ (mul_pos ha (mul_pos hp hs)) hp]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hkey (le_of_lt (mul_pos hs hp))]`.
-/
theorem rho_two {e M i : ℕ} (hM : Nat.Coprime 2 M) (hN : 2 ^ (e + 2) * M ∣ N) (hi : i ≤ e + 2)
    (hU : ∀ u ∈ U, ZMod.unitsMap ((dvd_mul_right _ M).trans hN) u = 1 ∨ ZMod.unitsMap ((dvd_mul_right _ M).trans hN) u = -1) :
    1 - (((2 ^ i).totient : ℝ) + if i < 2 then 1 else 0) / 2 ^ (e + 1) ≤ rho U (2 ^ i * M) := by
  open Classical in
  have card_filter_mem_le_lemma_6 {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ) {e M i : ℕ} (hM : Nat.Coprime 2 M) (hN : 2 ^ (e + 2) * M ∣ N)
      (hi : i ≤ e + 2)
      (hU : ∀ u ∈ U, ZMod.unitsMap ((dvd_mul_right _ M).trans hN) u = 1 ∨
        ZMod.unitsMap ((dvd_mul_right _ M).trans hN) u = -1) :
      ((KK N (2 ^ i * M)).filter fun u => u ∈ U).card
        ≤ (if i < 2 then 2 else 1) * (KK N (2 ^ (e + 2) * M)).card := by
    have h2 : 2 ^ (e + 2) ∣ N := (dvd_mul_right _ M).trans hN
    have hMN : M ∣ N := (dvd_mul_left M _).trans hN
    have hcop : Nat.Coprime (2 ^ (e + 2)) M := Nat.Coprime.pow_left _ hM
    have hA : ∀ v : (ZMod N)ˣ, v ∈ (ZMod.unitsMap hMN).ker → ZMod.unitsMap h2 v = 1 →
        v ∈ KK N (2 ^ (e + 2) * M) := by
      intro v hv1 hv2
      rw [mem_KK]
      rw [mem_ker_iff] at hv1
      have hv2' := (mem_ker_iff h2 v).mp (MonoidHom.mem_ker.mpr hv2)
      exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hv2', hv1⟩
    have hKM : ∀ u ∈ KK N (2 ^ i * M), u ∈ (ZMod.unitsMap hMN).ker := by
      intro u hu
      rw [mem_ker_iff]
      exact Nat.ModEq.of_mul_left (2 ^ i) (mem_KK.mp hu)
    have hneg : 2 ≤ i → ∀ u ∈ KK N (2 ^ i * M), ZMod.unitsMap h2 u ≠ -1 := by
      intro hi2 u hu hneg1
      have hval := congrArg Units.val hneg1
      rw [coe_unitsMap_eq_cast_val_of_dvd_neZero, Units.val_neg, Units.val_one] at hval
      have h1 : (((u : ZMod N).val + 1 : ℕ) : ZMod (2 ^ (e + 2))) = 0 := by
        push_cast; rw [hval]; ring
      rw [CharP.cast_eq_zero_iff (ZMod (2 ^ (e + 2))) (2 ^ (e + 2))] at h1
      have h4 : 4 ∣ (u : ZMod N).val + 1 := by
        have h5 := (pow_dvd_pow 2 (by omega : 2 ≤ e + 2)).trans h1
        simpa using h5
      have h4' : (u : ZMod N).val ≡ 1 [MOD 4] := by
        have h6 := Nat.ModEq.of_dvd ((pow_dvd_pow 2 hi2).trans (dvd_mul_right _ M))
          (mem_KK.mp hu)
        simpa using h6
      unfold Nat.ModEq at h4'
      omega
    by_cases hi2 : i < 2
    · rw [if_pos hi2]
      by_cases hw : ∃ w ∈ (KK N (2 ^ i * M)).filter (fun u => u ∈ U),
          ZMod.unitsMap h2 w = -1
      · obtain ⟨w, hwH, hw1⟩ := hw
        rw [Finset.mem_filter] at hwH
        have hsub : (KK N (2 ^ i * M)).filter (fun u => u ∈ U) ⊆
            KK N (2 ^ (e + 2) * M) ∪
              (KK N (2 ^ (e + 2) * M)).image (fun x => w * x) := by
          intro u hu
          rw [Finset.mem_filter] at hu
          rcases hU u hu.2 with h1 | h1
          · exact Finset.mem_union_left _ (hA u (hKM u hu.1) h1)
          · apply Finset.mem_union_right
            rw [Finset.mem_image]
            refine ⟨w⁻¹ * u, hA _ ?_ ?_, mul_inv_cancel_left w u⟩
            · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hKM w hwH.1)) (hKM u hu.1)
            · rw [map_mul, map_inv, hw1, h1, inv_mul_cancel]
        calc _ ≤ _ := Finset.card_le_card hsub
          _ ≤ _ := Finset.card_union_le _ _
          _ ≤ _ := Nat.add_le_add_left Finset.card_image_le _
          _ = 2 * (KK N (2 ^ (e + 2) * M)).card := by ring
      · push_neg at hw
        calc _ ≤ (KK N (2 ^ (e + 2) * M)).card := Finset.card_le_card (fun u hu => by
              rw [Finset.mem_filter] at hu
              rcases hU u hu.2 with h1 | h1
              · exact hA u (hKM u hu.1) h1
              · exact absurd h1 (hw u (Finset.mem_filter.mpr hu)))
          _ ≤ 2 * _ := by omega
    · rw [if_neg hi2]
      calc _ ≤ (KK N (2 ^ (e + 2) * M)).card := Finset.card_le_card (fun u hu => by
            rw [Finset.mem_filter] at hu
            rcases hU u hu.2 with h1 | h1
            · exact hA u (hKM u hu.1) h1
            · exact absurd h1 (hneg (by omega) u hu.1))
        _ = 1 * _ := (one_mul _).symm
  classical
  have hf : 2 ^ i * M ∣ N := (Nat.mul_dvd_mul_right (pow_dvd_pow 2 hi) M).trans hN
  have hcard := card_filter_mem_le_lemma_6 U hM hN hi hU
  have hA := card_KK (N := N) hN
  have hApos : 0 < (KK N (2 ^ (e + 2) * M)).card :=
    Finset.card_pos.mpr ⟨1, one_mem_KK hN⟩
  have hφf : (2 ^ i * M).totient = (2 ^ i).totient * M.totient :=
    Nat.totient_mul (Nat.Coprime.pow_left _ hM)
  have hφL : (2 ^ (e + 2) * M).totient = 2 ^ (e + 1) * M.totient := by
    rw [Nat.totient_mul (Nat.Coprime.pow_left _ hM), show e + 2 = e + 1 + 1 from rfl,
      Nat.totient_prime_pow_succ Nat.prime_two]
    norm_num
  have hMpos : 0 < M.totient := Nat.totient_pos.mpr
    (Nat.pos_of_dvd_of_pos ((dvd_mul_left M _).trans hN) (Nat.pos_of_ne_zero (NeZero.ne N)))
  have hT : (N.totient : ℝ) = (KK N (2 ^ (e + 2) * M)).card * (2 ^ (e + 1) * M.totient) := by
    rw [← hA, hφL]; push_cast; ring
  have hkey : (((KK N (2 ^ i * M)).filter fun u => u ∈ U).card : ℝ) * (2 ^ i).totient
      ≤ (((2 ^ i).totient : ℝ) + if i < 2 then 1 else 0) * (KK N (2 ^ (e + 2) * M)).card := by
    by_cases hi2 : i < 2
    · rw [if_pos hi2] at hcard ⊢
      have ht : (2 ^ i).totient = 1 := by interval_cases i <;> simp
      rw [ht]
      have : (((KK N (2 ^ i * M)).filter fun u => u ∈ U).card : ℝ)
          ≤ 2 * (KK N (2 ^ (e + 2) * M)).card := by exact_mod_cast hcard
      push_cast
      linarith
    · rw [if_neg hi2] at hcard ⊢
      have : (((KK N (2 ^ i * M)).filter fun u => u ∈ U).card : ℝ)
          ≤ (KK N (2 ^ (e + 2) * M)).card := by
        have := hcard; rw [one_mul] at this; exact_mod_cast this
      have ht0 : (0 : ℝ) ≤ (2 ^ i).totient := Nat.cast_nonneg _
      nlinarith [mul_le_mul_of_nonneg_right this ht0]
  rw [rho_eq U hf, hφf, hT]
  push_cast
  have ha : (0 : ℝ) < (KK N (2 ^ (e + 2) * M)).card := by exact_mod_cast hApos
  have hs : (0 : ℝ) < M.totient := by exact_mod_cast hMpos
  have hp : (0 : ℝ) < 2 ^ (e + 1) := by positivity
  suffices h : (((KK N (2 ^ i * M)).filter fun u => u ∈ U).card : ℝ)
      * (((2 ^ i).totient : ℝ) * M.totient)
      / ((KK N (2 ^ (e + 2) * M)).card * (2 ^ (e + 1) * M.totient))
      ≤ (((2 ^ i).totient : ℝ) + if i < 2 then 1 else 0) / 2 ^ (e + 1) by linarith
  rw [div_le_div_iff₀ (mul_pos ha (mul_pos hp hs)) hp]
  nlinarith [mul_le_mul_of_nonneg_right hkey (le_of_lt (mul_pos hs hp))]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => intro n h1 h2`. Conclude with `absurd (Nat.le_zero.mp h1) h2`. Consider the case `succ k ih`. Introduce `n h1 h2`.

Distinguish the cases in `h : 2 ∣ n`. Take `⟨j, rfl⟩` from `h`. Take `⟨v, M, hM, hj⟩` from `ih j (by omega) (by omega)`. Conclude with `⟨v + 1, M, hM, by rw [hj, pow_succ]; ring⟩`. Conclude with `⟨0, n, h, by simp⟩`.
-/
private theorem exists_two_pow_mul_odd_of_le_of_ne_zero (k : ℕ) :
    ∀ n : ℕ, n ≤ k → n ≠ 0 → ∃ v M : ℕ, ¬ 2 ∣ M ∧ n = 2 ^ v * M := by
  induction k with
  | zero => intro n h1 h2; exact absurd (Nat.le_zero.mp h1) h2
  | succ k ih =>
    intro n h1 h2
    by_cases h : 2 ∣ n
    · obtain ⟨j, rfl⟩ := h
      obtain ⟨v, M, hM, hj⟩ := ih j (by omega) (by omega)
      exact ⟨v + 1, M, hM, by rw [hj, pow_succ]; ring⟩
    · exact ⟨0, n, h, by simp⟩

/- English proof (translation)
Proceed by induction on `e with`. Consider the case `zero => show ∑ i ∈ range 2, (if i < 2 then (1 : ℝ) else 0) = 2`. Rewrite using `[Finset.sum_range_succ, Finset.sum_range_one]`. Evaluate the numerical expressions. Consider the case `succ k ih`.

Rewrite using `[show k + 1 + 2 = k + 2 + 1 from rfl, Finset.sum_range_succ, ih, if_neg (by omega), add_zero]`.
-/
private theorem sum_range_ite_lt_two_eq_two (e : ℕ) :
    ∑ i ∈ range (e + 2), (if i < 2 then (1 : ℝ) else 0) = 2 := by
  induction e with
  | zero =>
    show ∑ i ∈ range 2, (if i < 2 then (1 : ℝ) else 0) = 2
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    norm_num
  | succ k ih =>
    rw [show k + 1 + 2 = k + 2 + 1 from rfl, Finset.sum_range_succ, ih, if_neg (by omega), add_zero]

/- English proof (translation)
Establish `hN0 : N ≠ 0` using `NeZero.ne N`. Take `⟨v, M, hModd, hNvM⟩` from `exists_two_pow_mul_odd_of_le_of_ne_zero N N le_rfl hN0`. Establish `hM : Nat.Coprime 2 M` using `(Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hModd`. Establish `hv : e + 2 ≤ v`. Establish `h1 : 2 ^ (e + 2) ∣ 2 ^ v * M` using `by rw [← hNvM]; exact h2`.

Establish `h3 : 2 ^ (e + 2) ∣ 2 ^ v` using `(Nat.Coprime.pow_left (e + 2) hM).dvd_of_dvd_mul_right h1`. Conclude with `(Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h3`. Establish `hN' : 2 ^ (e + 2) * M ∣ N`. Rewrite using `[hNvM]`. Conclude with `Nat.mul_dvd_mul_right (pow_dvd_pow 2 hv) M`.

Establish `hU' : ∀ u ∈ U, ZMod.unitsMap ((dvd_mul_right _ M).trans hN') u = 1 ∨ ZMod.unitsMap ((dvd_mul_right _ M).trans hN') u = -1` using `hU`. Establish `hdiv : ∀ i ∈ range (e + 2), N / 2 ^ (v - i) = 2 ^ i * M`. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_range]`. Establish `h1 : N = 2 ^ (v - i) * (2 ^ i * M)`.

Rewrite using `[hNvM, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (by omega)]`. Rewrite using `[h1, Nat.mul_div_cancel_left _ (by positivity)]`. Establish `hΛ2 : ∀ i ∈ range (e + 2), vonMangoldt (2 ^ (v - i)) = Real.log 2`. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_range]`.

Simplify using `[vonMangoldt_apply_pow (show v - i ≠ 0 by omega), vonMangoldt_apply_prime Nat.prime_two]`. Establish `hSsub : insert d ((range (e + 2)).image (fun i => 2 ^ (v - i))) ⊆ N.divisors`. Introduce `x hx`. Rewrite `hx` using `[Finset.mem_insert, Finset.mem_image]`. Rewrite using `[Nat.mem_divisors]`.

Use `⟨?_, hN0⟩` and prove the remaining obligations. Break down `hx with rfl | ⟨i, _, rfl⟩` into its components or cases. Conclude with `hdN`. Rewrite using `[hNvM]`. Conclude with `(pow_dvd_pow 2 (Nat.sub_le v i)).trans (dvd_mul_right _ M)`.

Establish `hdS : d ∉ (range (e + 2)).image (fun i => 2 ^ (v - i))`. Rewrite using `[Finset.mem_image]`. Introduce and unpack `⟨i, hi, hid⟩`. Rewrite `hi` using `[Finset.mem_range]`. Apply `hd2` to reduce the goal to its premises.

Rewrite using `[← hid]`. Conclude with `dvd_pow_self 2 (by omega)`. Establish `hinj : ∀ x ∈ range (e + 2), ∀ y ∈ range (e + 2), 2 ^ (v - x) = 2 ^ (v - y) → x = y`. Introduce `x hx y hy hxy`. Rewrite `hx`, `hy` using `[Finset.mem_range]`.

Use `Nat.pow_right_injective (le_refl 2) hxy` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `h1 : ∑ i ∈ range (e + 2), Real.log 2 * (1 - (((2 ^ i).totient : ℝ) + if i < 2 then 1 else 0) / 2 ^ (e + 1)) ≤ ∑ i ∈ range (e + 2), vonMangoldt (2 ^ (v - i)) * rho U (N / 2 ^ (v - i))`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `i hi`.

Rewrite using `[hΛ2 i hi, hdiv i hi]`. Establish `hie : i ≤ e + 2` using `by rw [Finset.mem_range] at hi; omega`. Conclude with `mul_le_mul_of_nonneg_left (rho_two U hM hN' hie hU') (Real.log_nonneg one_le_two)`. Establish `h2' : ∑ i ∈ range (e + 2), vonMangoldt (2 ^ (v - i)) * rho U (N / 2 ^ (v - i)) = ∑ m ∈ (range (e + 2)).image (fun i => 2 ^ (v - i)), vonMangoldt m * rho U (N / m)` using `(Finset.sum_image (f := fun m => vonMangoldt m * rho U (N / m)) hinj).symm`. Establish `h3 : ∑ m ∈ insert d ((range (e + 2)).image (fun i => 2 ^ (v - i))), vonMangoldt m * rho U (N / m) ≤ ∑ m ∈ N.divisors, vonMangoldt m * rho U (N / m)` using `Finset.sum_le_sum_of_subset_of_nonneg hSsub (fun m _ _ => mul_nonneg vonMangoldt_nonneg (rho_nonneg U _))`.

Rewrite `h3` using `[Finset.sum_insert hdS, vonMangoldt_apply_prime hd]`. Establish `hφ : ∑ i ∈ range (e + 2), (((2 ^ i).totient : ℕ) : ℝ) = 2 ^ (e + 1)`. Establish `h` using `sum_totient_pow Nat.prime_two (e + 1)`. Rewrite `h` using `[show e + 1 + 1 = e + 2 from rfl]`. Conclude with `h` after adjusting the coercions.

Establish `hsum : ∑ i ∈ range (e + 2), Real.log 2 * (1 - (((2 ^ i).totient : ℝ) + if i < 2 then 1 else 0) / 2 ^ (e + 1)) = ((e : ℝ) + 1 - 1 / 2 ^ e) * Real.log 2`. Rewrite using `[← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib, sum_range_ite_lt_two_eq_two e, hφ]`. Simplify using `only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `hd' : Real.log d / 2 ≤ Real.log d * rho U (N / d)`. Use `mul_le_mul_of_nonneg_left rd (Real.log_nonneg (show (1 : ℝ) ≤ d by exact_mod_cast hd.one_lt.le))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Unfold `SS`.

Combine the linear relations using `[h1, h2', h3, hsum, hd']`.
-/
theorem le_SS {e d : ℕ} (h2 : 2 ^ (e + 2) ∣ N) (hd : d.Prime) (hdN : d ∣ N) (hd2 : ¬ 2 ∣ d)
    (hU : ∀ u ∈ U, ZMod.unitsMap h2 u = 1 ∨ ZMod.unitsMap h2 u = -1) (rd : 1 / 2 ≤ rho U (N / d)) :
    ((e : ℝ) + 1 - 1 / 2 ^ e) * Real.log 2 + Real.log d / 2 ≤ SS U := by
  classical
  have hN0 : N ≠ 0 := NeZero.ne N
  obtain ⟨v, M, hModd, hNvM⟩ := exists_two_pow_mul_odd_of_le_of_ne_zero N N le_rfl hN0
  have hM : Nat.Coprime 2 M := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hModd
  have hv : e + 2 ≤ v := by
    have h1 : 2 ^ (e + 2) ∣ 2 ^ v * M := by rw [← hNvM]; exact h2
    have h3 : 2 ^ (e + 2) ∣ 2 ^ v := (Nat.Coprime.pow_left (e + 2) hM).dvd_of_dvd_mul_right h1
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h3
  have hN' : 2 ^ (e + 2) * M ∣ N := by
    rw [hNvM]; exact Nat.mul_dvd_mul_right (pow_dvd_pow 2 hv) M
  have hU' : ∀ u ∈ U, ZMod.unitsMap ((dvd_mul_right _ M).trans hN') u = 1 ∨
      ZMod.unitsMap ((dvd_mul_right _ M).trans hN') u = -1 := hU
  have hdiv : ∀ i ∈ range (e + 2), N / 2 ^ (v - i) = 2 ^ i * M := by
    intro i hi
    rw [Finset.mem_range] at hi
    have h1 : N = 2 ^ (v - i) * (2 ^ i * M) := by
      rw [hNvM, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (by omega)]
    rw [h1, Nat.mul_div_cancel_left _ (by positivity)]
  have hΛ2 : ∀ i ∈ range (e + 2), vonMangoldt (2 ^ (v - i)) = Real.log 2 := by
    intro i hi
    rw [Finset.mem_range] at hi
    simp [vonMangoldt_apply_pow (show v - i ≠ 0 by omega), vonMangoldt_apply_prime Nat.prime_two]
  have hSsub : insert d ((range (e + 2)).image (fun i => 2 ^ (v - i))) ⊆ N.divisors := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_image] at hx
    rw [Nat.mem_divisors]
    refine ⟨?_, hN0⟩
    rcases hx with rfl | ⟨i, _, rfl⟩
    · exact hdN
    · rw [hNvM]; exact (pow_dvd_pow 2 (Nat.sub_le v i)).trans (dvd_mul_right _ M)
  have hdS : d ∉ (range (e + 2)).image (fun i => 2 ^ (v - i)) := by
    rw [Finset.mem_image]
    rintro ⟨i, hi, hid⟩
    rw [Finset.mem_range] at hi
    apply hd2
    rw [← hid]
    exact dvd_pow_self 2 (by omega)
  have hinj : ∀ x ∈ range (e + 2), ∀ y ∈ range (e + 2), 2 ^ (v - x) = 2 ^ (v - y) → x = y := by
    intro x hx y hy hxy
    rw [Finset.mem_range] at hx hy
    have := Nat.pow_right_injective (le_refl 2) hxy
    omega
  have h1 : ∑ i ∈ range (e + 2), Real.log 2 * (1 - (((2 ^ i).totient : ℝ) + if i < 2 then 1 else 0) / 2 ^ (e + 1))
      ≤ ∑ i ∈ range (e + 2), vonMangoldt (2 ^ (v - i)) * rho U (N / 2 ^ (v - i)) := by
    apply Finset.sum_le_sum
    intro i hi
    rw [hΛ2 i hi, hdiv i hi]
    have hie : i ≤ e + 2 := by rw [Finset.mem_range] at hi; omega
    exact mul_le_mul_of_nonneg_left (rho_two U hM hN' hie hU')
      (Real.log_nonneg one_le_two)
  have h2' : ∑ i ∈ range (e + 2), vonMangoldt (2 ^ (v - i)) * rho U (N / 2 ^ (v - i))
      = ∑ m ∈ (range (e + 2)).image (fun i => 2 ^ (v - i)),
          vonMangoldt m * rho U (N / m) :=
    (Finset.sum_image (f := fun m => vonMangoldt m * rho U (N / m)) hinj).symm
  have h3 : ∑ m ∈ insert d ((range (e + 2)).image (fun i => 2 ^ (v - i))),
        vonMangoldt m * rho U (N / m)
      ≤ ∑ m ∈ N.divisors, vonMangoldt m * rho U (N / m) :=
    Finset.sum_le_sum_of_subset_of_nonneg hSsub
      (fun m _ _ => mul_nonneg vonMangoldt_nonneg (rho_nonneg U _))
  rw [Finset.sum_insert hdS, vonMangoldt_apply_prime hd] at h3
  have hφ : ∑ i ∈ range (e + 2), (((2 ^ i).totient : ℕ) : ℝ) = 2 ^ (e + 1) := by
    have h := sum_totient_pow Nat.prime_two (e + 1)
    rw [show e + 1 + 1 = e + 2 from rfl] at h
    exact_mod_cast h
  have hsum : ∑ i ∈ range (e + 2), Real.log 2 * (1 - (((2 ^ i).totient : ℝ) + if i < 2 then 1 else 0) / 2 ^ (e + 1))
      = ((e : ℝ) + 1 - 1 / 2 ^ e) * Real.log 2 := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib,
      sum_range_ite_lt_two_eq_two e, hφ]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast
    field_simp
    ring
  have hd' : Real.log d / 2 ≤ Real.log d * rho U (N / d) := by
    have := mul_le_mul_of_nonneg_left rd (Real.log_nonneg (show (1 : ℝ) ≤ d by exact_mod_cast hd.one_lt.le))
    linarith
  unfold SS
  linarith [h1, h2', h3, hsum, hd']

end Formalism.HC.Der.Rd

end
