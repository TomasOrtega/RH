import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorFormsSpanOfSetsMulSmulMonoStatement

set_option autoImplicit false

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

/- English proof (translation)
Take `⟨hone, hmul, hsmul, -, -⟩` from `GlobalTheory.T.exteriorFormsSpanOfSets_mul_smul_mono A L`. Introduce `vs`. Proceed by induction on `vs with`. Consider the case `nil`. Introduce `_ t`.

Simplify using `only [prodL, List.foldr_nil, oneC, List.length_nil]`. Use `⟨fun _ q hq => ?_, fun ht => ?_⟩` and prove the remaining obligations. Use `split_ifs with h1t`. Establish `hq0 : q = 0` using `by omega`. Substitute `hq0` using the available equality.

Conclude with `hone`. Conclude with `zero_mem _`. Rewrite using `[if_neg (by omega)]`. Consider the case `cons w vs ih`. Introduce `hvs t`.

Establish `hw : w ∈ L` using `hvs w (List.mem_cons_self ..)`. Establish `hvs' : ∀ u ∈ vs, u ∈ L` using `fun u hu => hvs u (List.mem_cons_of_mem _ hu)`. Establish `key : prodL f h (w :: vs) t = Lop f h w (prodL f h vs) t` using `rfl`. Rewrite using `[key, List.length_cons]`. Use `⟨fun hts q hq => ?_, fun hlt => ?_⟩` and prove the remaining obligations.

Simplify using `only [Lop]`. Distinguish the cases in `ht : t.Nonempty`. Rewrite using `[dif_pos ht]`. Establish `hm : t.min' ht ∈ s` using `hts (t.min'_mem ht)`. Use `add_mem ?_ ?_` and prove the remaining obligations.

Use `zsmul_mem ?_ _` and prove the remaining obligations. Break down `q with _ | q` into its components or cases. Rewrite using `[(ih hvs' t).2 (by omega), mul_zero]`. Conclude with `zero_mem _`. Conclude with `hmul q _ _ (hf _ hm w hw) ((ih hvs' t).1 hts q (by omega))`.

Use `split_ifs with h2`. Establish `hm' : (t.erase (t.min' ht)).min' h2 ∈ s` using `hts (Finset.mem_of_mem_erase ((t.erase _).min'_mem h2))`. Establish `hcard : (t.erase (t.min' ht)).card = t.card - 1` using `Finset.card_erase_of_mem (t.min'_mem ht)`. Establish `hpos : 0 < t.card` using `ht.card_pos`. Conclude with `hsmul q _ _ (hh _ hm _ hm' w hw) ((ih hvs' _).1 ((Finset.erase_subset _ _).trans hts) q (by omega))`.

Conclude with `zero_mem _`. Rewrite using `[dif_neg ht]`. Conclude with `zero_mem _`. Simplify using `only [Lop]`. Distinguish the cases in `ht : t.Nonempty`.

Rewrite using `[dif_pos ht]`. Establish `hcard : (t.erase (t.min' ht)).card = t.card - 1` using `Finset.card_erase_of_mem (t.min'_mem ht)`. Rewrite using `[(ih hvs' t).2 (by omega), mul_zero, smul_zero, zero_add]`. Use `split_ifs with h2`. Rewrite using `[(ih hvs' _).2 (by omega), smul_zero]`.

Both sides reduce to the same expression. Rewrite using `[dif_neg ht]`.
-/
theorem prodL_mem_forms_and_vanish {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]
    {ι : Type} [LinearOrder ι]
    (f : ι → V →+ V) (h : ι → ι → V →+ K) (A : Subring K) (L : Set V) (s : Finset ι)
    (hf : ∀ i ∈ s, ∀ v ∈ L, ExteriorAlgebra.ι K (f i v) ∈ forms (A : Set K) L 1)
    (hh : ∀ i ∈ s, ∀ j ∈ s, ∀ v ∈ L, h i j v ∈ A) :
    ∀ (vs : List V), (∀ w ∈ vs, w ∈ L) → ∀ t : Finset ι,
      (t ⊆ s → ∀ q, q + t.card = vs.length + 1 → prodL f h vs t ∈ forms (A : Set K) L q) ∧
      (vs.length + 1 < t.card → prodL f h vs t = 0) := by
  obtain ⟨hone, hmul, hsmul, -, -⟩ := GlobalTheory.T.exteriorFormsSpanOfSets_mul_smul_mono A L
  intro vs
  induction vs with
  | nil =>
    intro _ t
    simp only [prodL, List.foldr_nil, oneC, List.length_nil]
    refine ⟨fun _ q hq => ?_, fun ht => ?_⟩
    · split_ifs with h1t
      · have hq0 : q = 0 := by omega
        subst hq0
        exact hone
      · exact zero_mem _
    · rw [if_neg (by omega)]
  | cons w vs ih =>
    intro hvs t
    have hw : w ∈ L := hvs w (List.mem_cons_self ..)
    have hvs' : ∀ u ∈ vs, u ∈ L := fun u hu => hvs u (List.mem_cons_of_mem _ hu)
    have key : prodL f h (w :: vs) t = Lop f h w (prodL f h vs) t := rfl
    rw [key, List.length_cons]
    refine ⟨fun hts q hq => ?_, fun hlt => ?_⟩
    · simp only [Lop]
      by_cases ht : t.Nonempty
      · rw [dif_pos ht]
        have hm : t.min' ht ∈ s := hts (t.min'_mem ht)
        refine add_mem ?_ ?_
        · refine zsmul_mem ?_ _
          rcases q with _ | q
          · rw [(ih hvs' t).2 (by omega), mul_zero]
            exact zero_mem _
          · exact hmul q _ _ (hf _ hm w hw) ((ih hvs' t).1 hts q (by omega))
        · split_ifs with h2
          · have hm' : (t.erase (t.min' ht)).min' h2 ∈ s :=
              hts (Finset.mem_of_mem_erase ((t.erase _).min'_mem h2))
            have hcard : (t.erase (t.min' ht)).card = t.card - 1 :=
              Finset.card_erase_of_mem (t.min'_mem ht)
            have hpos : 0 < t.card := ht.card_pos
            exact hsmul q _ _ (hh _ hm _ hm' w hw)
              ((ih hvs' _).1 ((Finset.erase_subset _ _).trans hts) q (by omega))
          · exact zero_mem _
      · rw [dif_neg ht]
        exact zero_mem _
    · simp only [Lop]
      by_cases ht : t.Nonempty
      · rw [dif_pos ht]
        have hcard : (t.erase (t.min' ht)).card = t.card - 1 :=
          Finset.card_erase_of_mem (t.min'_mem ht)
        rw [(ih hvs' t).2 (by omega), mul_zero, smul_zero, zero_add]
        split_ifs with h2
        · rw [(ih hvs' _).2 (by omega), smul_zero]
        · rfl
      · rw [dif_neg ht]

/- English proof (translation)
Introduce `K _ V _ _ ι _ f h A L s hf hh a v t hv hts q hq`. Rewrite using `[alt, Finset.sum_apply]`. Use `AddSubgroup.sum_mem _ fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply]`. Use `zsmul_mem ?_ _` and prove the remaining obligations.

Use `(prodL_mem_forms_and_vanish f h A L s hf hh _ ?_ t).1 hts q (by rw [List.length_ofFn]; exact hq)` and prove the remaining obligations. Introduce `w hw`. Take `⟨k, rfl⟩` from `List.mem_ofFn.mp hw`. Conclude with `hv _`.
-/
theorem alt_mem_forms : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type}
    [LinearOrder ι] (f : ι → V →+ V) (h : ι → ι → V →+ K) (A : Subring K) (L : Set V) (s : Finset ι),
    (∀ i ∈ s, ∀ v ∈ L, ExteriorAlgebra.ι K (f i v) ∈ forms (A : Set K) L 1) →
    (∀ i ∈ s, ∀ j ∈ s, ∀ v ∈ L, h i j v ∈ A) →
    ∀ (a : ℕ) (v : Fin a → V) (t : Finset ι), (∀ k, v k ∈ L) → t ⊆ s →
      ∀ q, q + t.card = a + 1 → alt f h a v t ∈ forms (A : Set K) L q := by
  intro K _ V _ _ ι _ f h A L s hf hh a v t hv hts q hq
  rw [alt, Finset.sum_apply]
  refine AddSubgroup.sum_mem _ fun σ _ => ?_
  rw [Pi.smul_apply]
  refine zsmul_mem ?_ _
  refine (prodL_mem_forms_and_vanish f h A L s hf hh _ ?_ t).1 hts q (by rw [List.length_ofFn]; exact hq)
  intro w hw
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hw
  exact hv _

end GlobalTheory.DI
