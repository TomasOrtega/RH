import Formalism.CharacterColumnKernels.StatementNG
import Formalism.CharacterColumnKernels.IdempotentNormalForms.GlobalConcreteOf
import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthQuotSmulRangeFree

open Finset

noncomputable section

namespace Formalism.NG

/- English proof (translation)
Break down `t with _ | n` into its components or cases. Simplify using the standard rewrite rules. Establish `hs : Ioo 0 (n + 1) = (range n).map ⟨(· + 1), add_left_injective 1⟩`. Use extensionality with `e`. Simplify using `only [mem_Ioo, mem_map, mem_range, Function.Embedding.coeFn_mk]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨e - 1, by omega, by omega⟩`. Introduce and unpack `⟨i, hi, rfl⟩`. Conclude with `⟨by omega, by omega⟩`.

Rewrite using `[hs, Finset.sum_map, Finset.sum_range_succ', add_comm]`. Use `add_le_add (le_of_eq (if_pos rfl)) (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))` and prove the remaining obligations. Use `show (if i + 1 + 1 = 1 then vhE else Sha (i + 1 + 1 - 1)) = Sha (i + 1)`. Conclude with `(if_neg (by omega)).trans (congrArg Sha (by omega))`.
-/
lemma sum_ite_le (t : ℕ) (vhE : ℕ∞) (Sha : ℕ → ℕ∞) :
    ∑ i ∈ range t, (if i + 1 = 1 then vhE else Sha (i + 1 - 1)) ≤
      vhE + ∑ e ∈ Ioo 0 t, Sha e := by
  rcases t with _ | n
  · simp
  · have hs : Ioo 0 (n + 1) = (range n).map ⟨(· + 1), add_left_injective 1⟩ := by
      ext e
      simp only [mem_Ioo, mem_map, mem_range, Function.Embedding.coeFn_mk]
      constructor
      · intro h
        exact ⟨e - 1, by omega, by omega⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨by omega, by omega⟩
    rw [hs, Finset.sum_map, Finset.sum_range_succ', add_comm]
    refine add_le_add (le_of_eq (if_pos rfl)) (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    show (if i + 1 + 1 = 1 then vhE else Sha (i + 1 + 1 - 1)) = Sha (i + 1)
    exact (if_neg (by omega)).trans (congrArg Sha (by omega))

/- English proof (translation)
Introduce `O _ _ _ X X' T T' Z p q b hT hZ d _ _ R' m g _ _ _ P hdet hφ π' ρπ hρπ t bl hbl ρk hsurj hblk hcard ℓ what₂ cols Q lenRow e' j vδ h0 s Sha vhE cB deg H0 vζ eO h0b hcb`. Establish `hG` using `globalConcrete O X X' T T' Z p q b hT hZ d R' m g P hdet hφ π' ρπ hρπ (Fin (t + 1)) bl hbl ρk hsurj hblk hcard`. Use `hG.trans ((Finset.sum_le_sum_of_subset (Finset.subset_univ _)).trans ?_)` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_succ]`. Establish `hsucc : ∑ c : Fin t, Module.length O (LinearMap.ker (relMap O (KO O) (bigRect (ρk c.succ) P))) ≤ ∑ c : Fin t, ((if (c : ℕ) + 1 = 1 then vhE + ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ) else Sha ((c : ℕ) + 1 - 1)) + (eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) + 4 * ((cols.card …`.

Use `Finset.sum_le_sum fun c _ => ?_` and prove the remaining obligations. Establish `h` using `hcb c.succ (Fin.succ_ne_zero c)`. Rewrite `h` using `[Fin.val_succ]`. Use `h.trans (le_of_eq ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Establish `hite : ∑ c : Fin t, (if (c : ℕ) + 1 = 1 then vhE + ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ) else Sha ((c : ℕ) + 1 - 1)) ≤ (vhE + ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ)) + ∑ e ∈ Ioo 0 t, Sha e` using `(Fin.sum_univ_eq_sum_range (fun i => if i + 1 = 1 then vhE + ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ) else Sha (i + 1 - 1)) t).le.trans (sum_ite_le t _ Sha)`. Rewrite `hsucc` using `[Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Use `(add_le_add h0b (hsucc.trans (add_le_add hite le_rfl))).trans (le_of_eq ?_)` and prove the remaining obligations. Simplify using `only [Finset.sum_add_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem nGlobal : StatNGlobal := by
  intro O _ _ _ X X' T T' Z p q b hT hZ d _ _ R' m g _ _ _ P hdet hφ π' ρπ hρπ t bl hbl ρk hsurj
    hblk hcard ℓ what₂ cols Q lenRow e' j vδ h0 s Sha vhE cB deg H0 vζ eO h0b hcb
  classical
  have hG := globalConcrete O X X' T T' Z p q b hT hZ d R' m g P hdet hφ π' ρπ hρπ (Fin (t + 1)) bl
    hbl ρk hsurj hblk hcard
  refine hG.trans ((Finset.sum_le_sum_of_subset (Finset.subset_univ _)).trans ?_)
  rw [Fin.sum_univ_succ]
  have hsucc : ∑ c : Fin t, Module.length O (LinearMap.ker (relMap O (KO O) (bigRect (ρk c.succ) P))) ≤
      ∑ c : Fin t, ((if (c : ℕ) + 1 = 1 then vhE + ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ)
          else Sha ((c : ℕ) + 1 - 1)) +
        (eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) + 4 * ((cols.card : ℕ∞) + 1) * vδ +
          (cols.card : ℕ∞) * H0 + ∑ z ∈ Q, vζ z)) := by
    refine Finset.sum_le_sum fun c _ => ?_
    have h := hcb c.succ (Fin.succ_ne_zero c)
    rw [Fin.val_succ] at h
    refine h.trans (le_of_eq ?_)
    ring
  have hite : ∑ c : Fin t, (if (c : ℕ) + 1 = 1 then vhE + ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ)
      else Sha ((c : ℕ) + 1 - 1)) ≤
      (vhE + ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ)) + ∑ e ∈ Ioo 0 t, Sha e :=
    (Fin.sum_univ_eq_sum_range (fun i => if i + 1 = 1 then vhE + ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ)
      else Sha (i + 1 - 1)) t).le.trans (sum_ite_le t _ Sha)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    at hsucc
  refine (add_le_add h0b (hsucc.trans (add_le_add hite le_rfl))).trans (le_of_eq ?_)
  simp only [Finset.sum_add_distrib]
  ring

/- English proof (translation)
Introduce `O _ _ _ X _ T _ hsep V _ _ _ _ _ act hsum L hL hspan hLT Z Zg hZg a A haL hacomm haG haB B hB`. Use `(congBoundGood O X T hsep V act hsum L hL hspan hLT Z Zg hZg a A haL hacomm haG haB).trans ?_` and prove the remaining obligations. Use `sum_le_sum fun x hx => ?_` and prove the remaining obligations. Use `gcongr`. Conclude with `hB x hx`.
-/
theorem etaBound : LocalSubalgebraEtaBound := by
  intro O _ _ _ X _ T _ hsep V _ _ _ _ _ act hsum L hL hspan hLT Z Zg hZg a A haL hacomm haG haB
    B hB
  refine (congBoundGood O X T hsep V act hsum L hL hspan hLT Z Zg hZg a A haL hacomm haG
    haB).trans ?_
  refine sum_le_sum fun x hx => ?_
  gcongr
  exact hB x hx

end Formalism.NG
