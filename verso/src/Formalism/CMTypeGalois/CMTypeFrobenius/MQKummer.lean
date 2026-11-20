import Mathlib
import Formalism.CMTypeGalois.StatementField

open Polynomial

noncomputable section

namespace Formalism.Q3

section KummerAux

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]

/- English proof (translation)
Establish `hint : IsIntegral K β`. Use `⟨X ^ 2 - C ⟨b, hb⟩, monic_X_pow_sub_C _ two_ne_zero, ?_⟩` and prove the remaining obligations. Simplify using `[hβ]`. Establish `hy' : y ∈ Algebra.adjoin K {β}`. Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]`.

Conclude with `hy`. Use `clear hy`. Proceed by induction on `hy' using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Rewrite `hx` using `[Set.mem_singleton_iff]`.

Conclude with `⟨0, K.zero_mem, 1, K.one_mem, by simp [hx]⟩`. Consider the case `algebraMap r`. Conclude with `⟨r, r.2, 0, K.zero_mem, by simp⟩`. Consider the case `add x z _ _ hx hz`. Take `⟨u, hu, v, hv, rfl⟩` from `hx`.

Take `⟨u', hu', v', hv', rfl⟩` from `hz`. Conclude with `⟨u + u', K.add_mem hu hu', v + v', K.add_mem hv hv', by ring⟩`. Consider the case `mul x z _ _ hx hz`. Take `⟨u, hu, v, hv, rfl⟩` from `hx`. Take `⟨u', hu', v', hv', rfl⟩` from `hz`.

Use `⟨u * u' + v * v' * b, K.add_mem (K.mul_mem hu hu') (K.mul_mem (K.mul_mem hv hv') hb), u * v' + v * u', K.add_mem (K.mul_mem hu hv') (K.mul_mem hv hu'), ?_⟩` and prove the remaining obligations. Rewrite using `[← hβ]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma mqk_mem_adjoin_form (K : IntermediateField F E) (β b : E) (hb : b ∈ K) (hβ : β ^ 2 = b)
    {y : E} (hy : y ∈ IntermediateField.adjoin K {β}) :
    ∃ u ∈ K, ∃ v ∈ K, y = u + v * β := by
  have hint : IsIntegral K β := by
    refine ⟨X ^ 2 - C ⟨b, hb⟩, monic_X_pow_sub_C _ two_ne_zero, ?_⟩
    simp [hβ]
  have hy' : y ∈ Algebra.adjoin K {β} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hy
  clear hy
  induction hy' using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, K.zero_mem, 1, K.one_mem, by simp [hx]⟩
  | algebraMap r =>
    exact ⟨r, r.2, 0, K.zero_mem, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨u, hu, v, hv, rfl⟩ := hx
    obtain ⟨u', hu', v', hv', rfl⟩ := hz
    exact ⟨u + u', K.add_mem hu hu', v + v', K.add_mem hv hv', by ring⟩
  | mul x z _ _ hx hz =>
    obtain ⟨u, hu, v, hv, rfl⟩ := hx
    obtain ⟨u', hu', v', hv', rfl⟩ := hz
    refine ⟨u * u' + v * v' * b, K.add_mem (K.mul_mem hu hu') (K.mul_mem (K.mul_mem hv hv') hb),
      u * v' + v * u', K.add_mem (K.mul_mem hu hv') (K.mul_mem hv hu'), ?_⟩
    rw [← hβ]
    ring

/- English proof (translation)
Take `⟨u, hu, v, hv, rfl⟩` from `mqk_mem_adjoin_form K β b hb hβ hy`. Establish `key : (u + v * β) ^ 2 = u ^ 2 + v ^ 2 * b + 2 * u * v * β` using `by rw [← hβ]; ring`. Distinguish the cases in `huv : u * v = 0`. Break down `mul_eq_zero.1 huv with h | h` into its components or cases. Use `right`.

Use `⟨v * b, K.mul_mem hv hb, ?_⟩` and prove the remaining obligations. Rewrite using `[← hyd, h, ← hβ]`. Expand and normalize the polynomial expressions, which then agree. Use `left`. Use `⟨u, hu, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hyd, h]`. Expand and normalize the polynomial expressions, which then agree. It suffices to derive a contradiction. Apply `hβK` to reduce the goal to its premises. Establish `h2 : (2 : E) * u * v ≠ 0`.

Rewrite using `[mul_assoc]`. Conclude with `mul_ne_zero two_ne_zero huv`. Establish `hβeq : β = (d - u ^ 2 - v ^ 2 * b) / (2 * u * v)`. Rewrite using `[eq_div_iff h2, ← hyd, key]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h2K : (2 : E) ∈ K`. Use `K.add_mem K.one_mem K.one_mem` as an intermediate fact. Rewrite `this` using `[one_add_one_eq_two]`. Conclude with `this`. Rewrite using `[hβeq]`.

Conclude with `K.div_mem (K.sub_mem (K.sub_mem hd (_root_.pow_mem hu 2)) (K.mul_mem (_root_.pow_mem hv 2) hb)) (K.mul_mem (K.mul_mem h2K hu) hv)`.
-/
lemma mqk_sq_step [CharZero E] (K : IntermediateField F E) (β b d : E) (hb : b ∈ K) (hd : d ∈ K)
    (hβ : β ^ 2 = b) (hβK : β ∉ K) {y : E} (hy : y ∈ IntermediateField.adjoin K {β})
    (hyd : y ^ 2 = d) :
    (∃ z ∈ K, z ^ 2 = d) ∨ (∃ z ∈ K, z ^ 2 = d * b) := by
  obtain ⟨u, hu, v, hv, rfl⟩ := mqk_mem_adjoin_form K β b hb hβ hy
  have key : (u + v * β) ^ 2 = u ^ 2 + v ^ 2 * b + 2 * u * v * β := by rw [← hβ]; ring
  by_cases huv : u * v = 0
  · rcases mul_eq_zero.1 huv with h | h
    · right
      refine ⟨v * b, K.mul_mem hv hb, ?_⟩
      rw [← hyd, h, ← hβ]
      ring
    · left
      refine ⟨u, hu, ?_⟩
      rw [← hyd, h]
      ring
  · exfalso
    apply hβK
    have h2 : (2 : E) * u * v ≠ 0 := by
      rw [mul_assoc]
      exact mul_ne_zero two_ne_zero huv
    have hβeq : β = (d - u ^ 2 - v ^ 2 * b) / (2 * u * v) := by
      rw [eq_div_iff h2, ← hyd, key]
      ring
    have h2K : (2 : E) ∈ K := by
      have := K.add_mem K.one_mem K.one_mem
      rw [one_add_one_eq_two] at this
      exact this
    rw [hβeq]
    exact K.div_mem (K.sub_mem (K.sub_mem hd (_root_.pow_mem hu 2)) (K.mul_mem (_root_.pow_mem hv 2) hb))
      (K.mul_mem (K.mul_mem h2K hu) hv)

/- English proof (translation)
Use `set b' : K := ⟨b, hb⟩ with hb'`. Establish `hmon : (X ^ 2 - C b' : K[X]).Monic` using `monic_X_pow_sub_C _ two_ne_zero`. Establish `hev : aeval β (X ^ 2 - C b' : K[X]) = 0` using `by simp [b', hβ]`. Establish `hint : IsIntegral K β` using `⟨X ^ 2 - C b', hmon, by simpa [aeval_def] using hev⟩`. Establish `hirr : Irreducible (X ^ 2 - C b' : K[X])` using `X_pow_sub_C_irreducible_of_prime Nat.prime_two fun z hz => hns z z.2 (by simpa [b'] using congrArg Subtype.val hz)`.

Establish `hmin : minpoly K β = X ^ 2 - C b'` using `(minpoly.eq_of_irreducible_of_monic hirr hev hmon).symm`. Rewrite using `[IntermediateField.adjoin.finrank hint, hmin, natDegree_X_pow_sub_C]`.
-/
lemma mqk_finrank_two (K : IntermediateField F E) (β b : E) (hb : b ∈ K) (hβ : β ^ 2 = b)
    (hns : ∀ z ∈ K, z ^ 2 ≠ b) :
    Module.finrank K (IntermediateField.adjoin K {β}) = 2 := by
  set b' : K := ⟨b, hb⟩ with hb'
  have hmon : (X ^ 2 - C b' : K[X]).Monic := monic_X_pow_sub_C _ two_ne_zero
  have hev : aeval β (X ^ 2 - C b' : K[X]) = 0 := by simp [b', hβ]
  have hint : IsIntegral K β := ⟨X ^ 2 - C b', hmon, by simpa [aeval_def] using hev⟩
  have hirr : Irreducible (X ^ 2 - C b' : K[X]) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two fun z hz =>
      hns z z.2 (by simpa [b'] using congrArg Subtype.val hz)
  have hmin : minpoly K β = X ^ 2 - C b' := (minpoly.eq_of_irreducible_of_monic hirr hev hmon).symm
  rw [IntermediateField.adjoin.finrank hint, hmin, natDegree_X_pow_sub_C]

end KummerAux

section KummerInd

variable {E : Type*} [Field E] [CharZero E]

def mqkField (F : Type*) [Field F] [Algebra F E] {k : ℕ} (α : Fin k → E) (T : Finset (Fin k)) : IntermediateField F E :=
  IntermediateField.adjoin F (α '' (T : Set (Fin k)))

omit [CharZero E] in
/- English proof (translation)
Establish `h` using `IntermediateField.adjoin_adjoin_left F (α '' (T : Set (Fin k))) {α j}`. Use `Eq.trans ?_ h.symm` and prove the remaining obligations. Unfold `mqkField`. Rewrite using `[Set.union_singleton, Finset.coe_insert, Set.image_insert_eq]`.
-/
lemma mqk_insert (F : Type*) [Field F] [Algebra F E] {k : ℕ} (α : Fin k → E) (T : Finset (Fin k)) (j : Fin k) :
    mqkField F α (insert j T) =
      (IntermediateField.adjoin (mqkField F α T) {α j}).restrictScalars F := by
  have h := IntermediateField.adjoin_adjoin_left F (α '' (T : Set (Fin k))) {α j}
  refine Eq.trans ?_ h.symm
  unfold mqkField
  rw [Set.union_singleton, Finset.coe_insert, Set.image_insert_eq]

/- English proof (translation)
Introduce `T`. Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty`. Establish `hbot : mqkField F α ∅ = ⊥`. Simplify using `only [mqkField, Finset.coe_empty, Set.image_empty]`.

Conclude with `IntermediateField.adjoin_empty F E`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hbot, IntermediateField.finrank_bot]`. Simplify using the standard rewrite rules. Introduce `d y hy hyd`.

Rewrite `hy` using `[hbot, IntermediateField.mem_bot]`. Take `⟨z, rfl⟩` from `hy`. Use `⟨∅, Finset.empty_subset _, ?_⟩` and prove the remaining obligations. Establish `hz : z ^ 2 = d` using `(algebraMap F E).injective (by rw [map_pow]; exact hyd)`. Conclude with `⟨z, by rw [Finset.prod_empty, mul_one, ← hz, sq]⟩`.

Consider the case `@insert j T hj ih`. Take `⟨ihr, ihs⟩` from `ih`. Use `set K := mqkField F α T with hK`. Establish `hb : (a j : E) ∈ K`. Use `K.algebraMap_mem ((a j : ℤ) : F)` as an intermediate fact.

Simplify using `using this`. Establish `hsq_a : ∀ z ∈ K, z ^ 2 ≠ (a j : E)`. Introduce `z hz hz2`. Take `⟨S, hS, hsq⟩` from `ihs ((a j : ℤ) : F) z hz (by simpa using hz2)`. Establish `hjS : j ∉ S` using `fun h => hj (hS h)`.

Apply `hns (insert j S) (Finset.insert_nonempty j S)` to reduce the goal to its premises. Rewrite using `[Finset.prod_insert hjS]`. Conclude with `hsq`. Establish `hβK : α j ∉ K` using `fun h => hsq_a (α j) h (hα j)`. Establish `hfr` using `mqk_finrank_two K (α j) (a j : E) hb (hα j) hsq_a`.

Establish `hcard : (insert j T).card = T.card + 1` using `by first`. Consider the case `exact Finset.card_insert_of_not_mem hj`. Consider the case `exact Finset.card_insert_of_notMem hj`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mqk_insert, hcard, pow_succ, ← ihr, ← hfr]`.

Conclude with `(Module.finrank_mul_finrank F K (IntermediateField.adjoin K {α j})).symm`. Introduce `d y hy hyd`. Rewrite `hy` using `[mqk_insert]`. Establish `hdK : algebraMap F E d ∈ K` using `K.algebraMap_mem d`. Break down `mqk_sq_step K (α j) (a j : E) (algebraMap F E d) hb hdK (hα j) hβK hy hyd with ⟨z, hz, hz2⟩ | ⟨z, hz, hz2⟩` into its components or cases.

Take `⟨S, hS, hsq⟩` from `ihs d z hz hz2`. Conclude with `⟨S, hS.trans (Finset.subset_insert j T), hsq⟩`. Take `⟨S, hS, hsq⟩` from `ihs (d * ((a j : ℤ) : F)) z hz (by rw [hz2]; simp)`. Establish `hjS : j ∉ S` using `fun h => hj (hS h)`. Use `⟨insert j S, Finset.insert_subset_insert j hS, ?_⟩` and prove the remaining obligations.

Rewrite using `[Finset.prod_insert hjS, ← mul_assoc]`. Conclude with `hsq`.
-/
lemma mqk_induction (F : Type*) [Field F] [Algebra F E] {k : ℕ} (a : Fin k → ℤ) (α : Fin k → E) (hα : ∀ i, α i ^ 2 = (a i : E))
    (hns : ∀ S : Finset (Fin k), S.Nonempty → ¬ IsSquare (∏ i ∈ S, (a i : F))) :
    ∀ T : Finset (Fin k), Module.finrank F (mqkField F α T) = 2 ^ T.card ∧
      ∀ d : F, ∀ y ∈ mqkField F α T, y ^ 2 = algebraMap F E d →
        ∃ S ⊆ T, IsSquare (d * ∏ i ∈ S, (a i : F)) := by
  intro T
  classical
  induction T using Finset.induction_on with
  | empty =>
    have hbot : mqkField F α ∅ = ⊥ := by
      simp only [mqkField, Finset.coe_empty, Set.image_empty]
      exact IntermediateField.adjoin_empty F E
    refine ⟨?_, ?_⟩
    · rw [hbot, IntermediateField.finrank_bot]
      simp
    · intro d y hy hyd
      rw [hbot, IntermediateField.mem_bot] at hy
      obtain ⟨z, rfl⟩ := hy
      refine ⟨∅, Finset.empty_subset _, ?_⟩
      have hz : z ^ 2 = d := (algebraMap F E).injective (by rw [map_pow]; exact hyd)
      exact ⟨z, by rw [Finset.prod_empty, mul_one, ← hz, sq]⟩
  | @insert j T hj ih =>
    obtain ⟨ihr, ihs⟩ := ih
    set K := mqkField F α T with hK
    have hb : (a j : E) ∈ K := by
      have := K.algebraMap_mem ((a j : ℤ) : F)
      simpa using this
    have hsq_a : ∀ z ∈ K, z ^ 2 ≠ (a j : E) := by
      intro z hz hz2
      obtain ⟨S, hS, hsq⟩ := ihs ((a j : ℤ) : F) z hz (by simpa using hz2)
      have hjS : j ∉ S := fun h => hj (hS h)
      apply hns (insert j S) (Finset.insert_nonempty j S)
      rw [Finset.prod_insert hjS]
      exact hsq
    have hβK : α j ∉ K := fun h => hsq_a (α j) h (hα j)
    have hfr := mqk_finrank_two K (α j) (a j : E) hb (hα j) hsq_a
    have hcard : (insert j T).card = T.card + 1 := by
      first
      | exact Finset.card_insert_of_not_mem hj
      | exact Finset.card_insert_of_notMem hj
    refine ⟨?_, ?_⟩
    · rw [mqk_insert, hcard, pow_succ, ← ihr, ← hfr]
      exact (Module.finrank_mul_finrank F K (IntermediateField.adjoin K {α j})).symm
    · intro d y hy hyd
      rw [mqk_insert] at hy
      have hdK : algebraMap F E d ∈ K := K.algebraMap_mem d
      rcases mqk_sq_step K (α j) (a j : E) (algebraMap F E d) hb hdK (hα j) hβK hy hyd with
        ⟨z, hz, hz2⟩ | ⟨z, hz, hz2⟩
      · obtain ⟨S, hS, hsq⟩ := ihs d z hz hz2
        exact ⟨S, hS.trans (Finset.subset_insert j T), hsq⟩
      · obtain ⟨S, hS, hsq⟩ := ihs (d * ((a j : ℤ) : F)) z hz (by rw [hz2]; simp)
        have hjS : j ∉ S := fun h => hj (hS h)
        refine ⟨insert j S, Finset.insert_subset_insert j hS, ?_⟩
        rw [Finset.prod_insert hjS, ← mul_assoc]
        exact hsq

end KummerInd

/- English proof (translation)
Take `⟨hp, hinj⟩` from `hq`. Take `⟨j, hj⟩` from `hS`. Introduce `hsq`. Rewrite `hsq` using `[← Int.cast_prod, Rat.isSquare_intCast_iff]`. Take `⟨t, ht⟩` from `hsq`.

Establish `hpj : Prime (q j : ℤ)` using `Nat.prime_iff_prime_int.mp (hp j).1`. Establish `hdiv : (q j : ℤ) ∣ t * t`. Rewrite using `[← ht]`. Conclude with `(dvd_neg.2 (dvd_refl _)).trans (Finset.dvd_prod_of_mem (fun i => -(q i : ℤ)) hj)`. Establish `ht' : (q j : ℤ) ∣ t` using `(hpj.dvd_or_dvd hdiv).elim id id`.

Establish `hsq2 : (q j : ℤ) * q j ∣ ∏ i ∈ S, (-(q i : ℤ))`. Rewrite using `[ht]`. Conclude with `mul_dvd_mul ht' ht'`. Rewrite `hsq2` using `[← Finset.mul_prod_erase S _ hj]`. Establish `hrest : (q j : ℤ) ∣ ∏ i ∈ S.erase j, (-(q i : ℤ))`.

Establish `e : -(q j : ℤ) * ∏ i ∈ S.erase j, (-(q i : ℤ)) = (q j : ℤ) * (-(∏ i ∈ S.erase j, (-(q i : ℤ))))` using `by ring`. Rewrite `hsq2` using `[e]`. Conclude with `dvd_neg.1 ((mul_dvd_mul_iff_left hpj.ne_zero).1 hsq2)`. Take `⟨i, hi, hdi⟩` from `(Prime.dvd_finsetProd_iff hpj _).1 hrest`. Establish `hij : i ≠ j` using `Finset.ne_of_mem_erase hi`.

Establish `hdi' : q j ∣ q i` using `Int.natCast_dvd_natCast.1 (dvd_neg.1 hdi)`. Establish `heq` using `(Nat.prime_dvd_prime_iff_eq (hp j).1 (hp i).1).1 hdi'`. Conclude with `hij (hinj heq.symm)`.
-/
lemma host_not_sq (q : Fin 3 → ℕ) (hq : Hyp3 q) (S : Finset (Fin 3)) (hS : S.Nonempty) :
    ¬ IsSquare (∏ i ∈ S, (((-(q i : ℤ)) : ℤ) : ℚ)) := by
  obtain ⟨hp, hinj⟩ := hq
  obtain ⟨j, hj⟩ := hS
  intro hsq
  rw [← Int.cast_prod, Rat.isSquare_intCast_iff] at hsq
  obtain ⟨t, ht⟩ := hsq
  have hpj : Prime (q j : ℤ) := Nat.prime_iff_prime_int.mp (hp j).1
  have hdiv : (q j : ℤ) ∣ t * t := by
    rw [← ht]
    exact (dvd_neg.2 (dvd_refl _)).trans (Finset.dvd_prod_of_mem (fun i => -(q i : ℤ)) hj)
  have ht' : (q j : ℤ) ∣ t := (hpj.dvd_or_dvd hdiv).elim id id
  have hsq2 : (q j : ℤ) * q j ∣ ∏ i ∈ S, (-(q i : ℤ)) := by
    rw [ht]
    exact mul_dvd_mul ht' ht'
  rw [← Finset.mul_prod_erase S _ hj] at hsq2
  have hrest : (q j : ℤ) ∣ ∏ i ∈ S.erase j, (-(q i : ℤ)) := by
    have e : -(q j : ℤ) * ∏ i ∈ S.erase j, (-(q i : ℤ)) =
        (q j : ℤ) * (-(∏ i ∈ S.erase j, (-(q i : ℤ)))) := by ring
    rw [e] at hsq2
    exact dvd_neg.1 ((mul_dvd_mul_iff_left hpj.ne_zero).1 hsq2)
  obtain ⟨i, hi, hdi⟩ := (Prime.dvd_finsetProd_iff hpj _).1 hrest
  have hij : i ≠ j := Finset.ne_of_mem_erase hi
  have hdi' : q j ∣ q i := Int.natCast_dvd_natCast.1 (dvd_neg.1 hdi)
  have heq := (Nat.prime_dvd_prime_iff_eq (hp j).1 (hp i).1).1 hdi'
  exact hij (hinj heq.symm)

/- English proof (translation)
Unfold `MQGalois at hG`. Unfold `MQKummer`. Introduce `k E _ _ a α hα hns`. Establish `hα'` using `hα`. Take `⟨hsq, htop⟩` from `hα`.

Establish `hne : ∀ i, a i ≠ 0`. Introduce `i h0`. Apply `hns {i} (Finset.singleton_nonempty i)` to reduce the goal to its premises. Rewrite using `[Finset.prod_singleton, h0]`. Conclude with `⟨0, by simp⟩`.

Take `⟨hgal, -, -, hinj⟩` from `hG k E a α hα' hne`. Take `⟨hfr0, hsqs⟩` from `mqk_induction ℚ a α hsq hns Finset.univ`. Establish `huniv : mqkField ℚ α Finset.univ = ⊤`. Rewrite using `[← htop]`. Simplify using `only [mqkField, Finset.coe_univ, Set.image_univ]`.

Establish `hfr : Module.finrank ℚ E = 2 ^ k`. Rewrite `hfr0` using `[huniv, IntermediateField.finrank_top']`. Simplify using `using hfr0`. Use `⟨hfr, ?_, ?_⟩` and prove the remaining obligations. Use `(Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, ?_⟩` and prove the remaining obligations.

Establish `h1 : Fintype.card Gal(E/ℚ) = 2 ^ k`. Rewrite using `[← hfr]`. Use `first`. Consider the case `(rw [← Nat.card_eq_fintype_card]; exact IsGalois.card_aut_eq_finrank (F := ℚ) (E := E))`. Consider the case `(convert IsGalois.card_aut_eq_finrank (F := ℚ) (E := E) using 1)`.

Rewrite using `[h1]`. Simplify using `[Fintype.card_units_int]`. Introduce `d`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, hr⟩`.

Establish `hr2 : r ^ 2 = algebraMap ℚ E d` using `by rw [hr, sq]`. Take `⟨S, -, hS⟩` from `hsqs d r (by rw [huniv]; exact IntermediateField.mem_top) hr2`. Conclude with `⟨S, hS⟩`. Introduce and unpack `⟨S, t, ht⟩`. Establish `hαne : ∀ i, α i ≠ 0`.

Introduce `i h`. Establish `h2` using `hsq i`. Rewrite `h2` using `[h, zero_pow two_ne_zero]`. Conclude with `hne i (by exact_mod_cast h2.symm)`. Use `set P := ∏ i ∈ S, α i with hP`.

Establish `hPne : P ≠ 0` using `Finset.prod_ne_zero_iff.2 fun i _ => hαne i`. Establish `hcast : algebraMap ℚ E d * P ^ 2 = algebraMap ℚ E t * algebraMap ℚ E t`. Establish `h1` using `congrArg (algebraMap ℚ E) ht`. Rewrite `h1` using `[map_mul, map_mul, map_prod]`. Rewrite using `[← h1, hP, ← Finset.prod_pow]`.

Use `congr 1`. Conclude with `Finset.prod_congr rfl fun i _ => by rw [hsq i]; simp`. Use `⟨algebraMap ℚ E t / P, ?_⟩` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Take the linear combination `hcast`.
-/
theorem mqKummer_of (hG : MQGalois) : MQKummer := by
  unfold MQGalois at hG
  unfold MQKummer
  intro k E _ _ a α hα hns
  have hα' := hα
  obtain ⟨hsq, htop⟩ := hα
  have hne : ∀ i, a i ≠ 0 := by
    intro i h0
    apply hns {i} (Finset.singleton_nonempty i)
    rw [Finset.prod_singleton, h0]
    exact ⟨0, by simp⟩
  obtain ⟨hgal, -, -, hinj⟩ := hG k E a α hα' hne
  obtain ⟨hfr0, hsqs⟩ := mqk_induction ℚ a α hsq hns Finset.univ
  have huniv : mqkField ℚ α Finset.univ = ⊤ := by
    rw [← htop]
    simp only [mqkField, Finset.coe_univ, Set.image_univ]
  have hfr : Module.finrank ℚ E = 2 ^ k := by
    rw [huniv, IntermediateField.finrank_top'] at hfr0
    simpa using hfr0
  refine ⟨hfr, ?_, ?_⟩
  · refine (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, ?_⟩
    have h1 : Fintype.card Gal(E/ℚ) = 2 ^ k := by
      rw [← hfr]
      first
      | (rw [← Nat.card_eq_fintype_card]; exact IsGalois.card_aut_eq_finrank (F := ℚ) (E := E))
      | (convert IsGalois.card_aut_eq_finrank (F := ℚ) (E := E) using 1)
    rw [h1]
    simp [Fintype.card_units_int]
  · intro d
    constructor
    · rintro ⟨r, hr⟩
      have hr2 : r ^ 2 = algebraMap ℚ E d := by rw [hr, sq]
      obtain ⟨S, -, hS⟩ := hsqs d r (by rw [huniv]; exact IntermediateField.mem_top) hr2
      exact ⟨S, hS⟩
    · rintro ⟨S, t, ht⟩
      have hαne : ∀ i, α i ≠ 0 := by
        intro i h
        have h2 := hsq i
        rw [h, zero_pow two_ne_zero] at h2
        exact hne i (by exact_mod_cast h2.symm)
      set P := ∏ i ∈ S, α i with hP
      have hPne : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hαne i
      have hcast : algebraMap ℚ E d * P ^ 2 = algebraMap ℚ E t * algebraMap ℚ E t := by
        have h1 := congrArg (algebraMap ℚ E) ht
        rw [map_mul, map_mul, map_prod] at h1
        rw [← h1, hP, ← Finset.prod_pow]
        congr 1
        exact Finset.prod_congr rfl fun i _ => by rw [hsq i]; simp
      refine ⟨algebraMap ℚ E t / P, ?_⟩
      field_simp
      linear_combination hcast

/- English proof (translation)
Unfold `MQGalois at hG`. Unfold `MQKummer at hK`. Unfold `HostGalois`. Introduce `q hq E _ _ α hα`. Establish `hα' : IsMQ (fun i => -(q i : ℤ)) α` using `hα`.

Establish `hne : ∀ i, (fun i => -(q i : ℤ)) i ≠ 0`. Introduce `i`. Use `(hq.1 i).1.pos` as an intermediate fact. Use `show -(q i : ℤ) ≠ 0`. Use linear arithmetic over natural numbers and integers.

Take `⟨hgal, -, hmul, -⟩` from `hG 3 E (fun i => -(q i : ℤ)) α hα' hne`. Take `⟨hfr, hbij, -⟩` from `hK 3 E (fun i => -(q i : ℤ)) α hα' (fun S hS => host_not_sq q hq S hS)`. Conclude with `⟨hgal, by rw [hfr]; norm_num, hbij, hmul⟩`.
-/
theorem hostGalois_of (hG : MQGalois) (hK : MQKummer) : HostGalois := by
  unfold MQGalois at hG
  unfold MQKummer at hK
  unfold HostGalois
  intro q hq E _ _ α hα
  have hα' : IsMQ (fun i => -(q i : ℤ)) α := hα
  have hne : ∀ i, (fun i => -(q i : ℤ)) i ≠ 0 := by
    intro i
    have := (hq.1 i).1.pos
    show -(q i : ℤ) ≠ 0
    omega
  obtain ⟨hgal, -, hmul, -⟩ := hG 3 E (fun i => -(q i : ℤ)) α hα' hne
  obtain ⟨hfr, hbij, -⟩ := hK 3 E (fun i => -(q i : ℤ)) α hα' (fun S hS => host_not_sq q hq S hS)
  exact ⟨hgal, by rw [hfr]; norm_num, hbij, hmul⟩

end Formalism.Q3
