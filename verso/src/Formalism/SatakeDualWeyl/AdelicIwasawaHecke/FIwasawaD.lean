import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawaC

open Formalism.UG Matrix

namespace Formalism.UG.P

section FIwasawaStep

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {n : ℕ}

/- English proof (translation)
Use `set W : Finset (Fin n) := Finset.univ.filter (fun i => ρ ≤ i ∧ i ≤ Fin.rev ρ) with hW`. Establish `hmem : ∀ i, ρ ≤ i → i ≤ Fin.rev ρ → i ∈ W` using `fun i h1 h2 => Finset.mem_filter.2 ⟨Finset.mem_univ _, h1, h2⟩`. Establish `hout : ∀ i, i ∉ W → i < ρ ∨ Fin.rev ρ < i`. Introduce `i hi`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hi (hmem i h.1 h.2)`. Establish `hρW : ρ ∈ W` using `hmem ρ le_rfl hρ.le`. Establish `hcz` using `fIwasawa_col_zero σ M hM r hT ρ hρr hρ`. Establish `hex : ∃ j ∈ W, M j ρ ≠ 0`.

Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hgram` using `fIwasawa_gram_un σ M hM (Fin.rev ρ) ρ`. Rewrite `hgram` using `[if_pos (Fin.rev_rev ρ).symm]`. Establish `h0 : ∑ j, σ (M (Fin.rev j) (Fin.rev ρ)) * M j ρ = 0`.

Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hj1 : j < ρ`. Establish `hjr : j.val < r` using `by rw [← hρr]; exact hj1`. Rewrite using `[(fIwasawa_rows σ M hM r hT j hjr).2 (Fin.rev ρ) (Fin.rev_lt_rev.2 hj1), map_zero, zero_mul]`. Distinguish the cases in `hj2 : Fin.rev ρ < j`.

Rewrite using `[hcz j hj2, mul_zero]`. Rewrite using `[hcon j (hmem j (not_lt.1 hj1) (not_lt.1 hj2)), mul_zero]`. Rewrite `hgram` using `[h0]`. Conclude with `zero_ne_one hgram`. Take `⟨j₀, hj₀W, hj₀⟩` from `hex`.

Take `⟨a₀, ha₀W, ha₀max⟩` from `Finset.exists_max_image W (fun i => Valued.v (M i ρ)) ⟨ρ, hρW⟩`. Establish `hnz : ∀ a ∈ W, (∀ i ∈ W, Valued.v (M i ρ) ≤ Valued.v (M a ρ)) → Valued.v (M a ρ) ≠ 0`. Introduce `a _ hamax h0`. Establish `h1` using `hamax j₀ hj₀W`. Rewrite `h1` using `[h0]`.

Conclude with `hj₀ ((Valuation.zero_iff _).1 (le_antisymm h1 zero_le'))`. Establish `hV` using `hnz a₀ ha₀W ha₀max`. Establish `hWrev : ∀ j ∈ W, Fin.rev j ∈ W`. Introduce `j hj`. Take `⟨_, h1, h2⟩` from `Finset.mem_filter.1 hj`.

Conclude with `hmem _ (by simpa using Fin.rev_le_rev.2 h2) (Fin.rev_le_rev.2 h1)`. Choose the witnesses or unpack the hypotheses as in `⟨a, haW, hamax, hne⟩ : ∃ a ∈ W, (∀ i ∈ W, Valued.v (M i ρ) ≤ Valued.v (M a ρ)) ∧ a ≠ Fin.rev a := by`. Distinguish the cases in `h₀ : a₀ = Fin.rev a₀`. Assume the negation of the conclusion as `hcon push_neg at hcon`. Establish `hlt : ∀ i ∈ W, i ≠ a₀ → Valued.v (M i ρ) < Valued.v (M a₀ ρ)`.

Introduce `i hi hia`. Use `lt_of_le_of_ne (ha₀max i hi) fun heq => ?_` and prove the remaining obligations. Establish `hii : i = Fin.rev i` using `hcon i hi fun k hk => (ha₀max k hk).trans_eq heq.symm`. Apply `hia` to reduce the goal to its premises. Establish `e1` using `congrArg Fin.val hii`.

Establish `e2` using `congrArg Fin.val h₀`. Rewrite `e1`, `e2` using `[Fin.val_rev]`. Conclude with `Fin.ext (by omega)`. Establish `hiso` using `fIwasawa_iso σ M hM ρ hρ`. Rewrite `hiso` using `[← Finset.add_sum_erase _ _ (Finset.mem_univ a₀)]`.

Establish `hbig : Valued.v (σ (M (Fin.rev a₀) ρ) * M a₀ ρ) = Valued.v (M a₀ ρ) * Valued.v (M a₀ ρ)`. Rewrite using `[← h₀, map_mul, hσv]`. Establish `hpos : (0 : WithZero (Multiplicative ℤ)) < Valued.v (M a₀ ρ) * Valued.v (M a₀ ρ)` using `zero_lt_iff.2 (mul_ne_zero hV hV)`. Establish `hsmall : Valued.v (∑ j ∈ Finset.univ.erase a₀, σ (M (Fin.rev j) ρ) * M j ρ) < Valued.v (M a₀ ρ) * Valued.v (M a₀ ρ)`. Apply `Valuation.map_sum_lt _ (mul_ne_zero hV hV)` to reduce the goal to its premises.

Introduce `j hj`. Establish `hja` using `Finset.ne_of_mem_erase hj`. Rewrite using `[map_mul, hσv]`. Distinguish the cases in `hjW : j ∈ W`. Establish `hra : Fin.rev j ≠ a₀`.

Introduce `h`. Apply `hja` to reduce the goal to its premises. Rewrite using `[← Fin.rev_rev j, h, ← h₀]`. Conclude with `mul_lt_mul_of_le_of_lt_of_nonneg_of_pos (ha₀max _ (hWrev j hjW)) (hlt j hjW hja) zero_le' (zero_lt_iff.2 hV)`. Break down `hout j hjW with h | h` into its components or cases.

Rewrite using `[hcz (Fin.rev j) (Fin.rev_lt_rev.2 h), map_zero, zero_mul]`. Conclude with `hpos`. Rewrite using `[hcz j h, map_zero, mul_zero]`. Conclude with `hpos`. Establish `h3 : σ (M (Fin.rev a₀) ρ) * M a₀ ρ = -∑ j ∈ Finset.univ.erase a₀, σ (M (Fin.rev j) ρ) * M j ρ` using `eq_neg_of_add_eq_zero_left hiso`.

Rewrite `hbig` using `[h3, Valuation.map_neg]`. Rewrite `hsmall` using `[hbig]`. Conclude with `lt_irrefl _ hsmall`. Conclude with `⟨a₀, ha₀W, ha₀max, h₀⟩`. Establish `haW'` using `Finset.mem_filter.1 haW`.

Take `⟨π, hπa, hπrev, hπfix⟩` from `fIwasawa_perm ρ a hρ haW'.2.1 haW'.2.2 hne`. Establish `hπW : ∀ i ∈ W, π i ∈ W`. Introduce `i hi`. Assume the negation of the conclusion as `hni`. Establish `hii : π i = i` using `π.injective (hπfix (π i) (hout _ hni))`.

Rewrite `hni` using `[hii]`. Conclude with `hni hi`. Establish `hInt : fIwasawaInt (fIwasawaP (L` using `L) π) := by`. Introduce `i j`. Simplify using `only [fIwasawaP, Matrix.of_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Use `⟨fIwasawaP π, ⟨permMatrix_isUnitary_of_commute_rev σ π hπrev, hInt⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j hj hji`. Rewrite using `[permMatrix_mul_apply₂]`. Distinguish the cases in `hiW : i ∈ W`.

Establish `hπi` using `Finset.mem_filter.1 (hπW i hiW)`. Establish `hjρ : j < ρ` using `by rw [Fin.lt_iff_val_lt_val, hρr]; exact hj`. Conclude with `hT (π i) j hj (lt_of_lt_of_le hjρ hπi.2.1)`. Rewrite using `[hπfix i (hout i hiW)]`. Conclude with `hT i j hj hji`.

Rewrite using `[permMatrix_mul_apply₂, hπa]`. Introduce `h0`. Conclude with `hnz a haW hamax (by rw [h0, map_zero])`. Introduce `i h1 h2`. Rewrite using `[permMatrix_mul_apply₂, permMatrix_mul_apply₂, hπa]`.

Conclude with `hamax (π i) (hπW i (hmem i h1 h2))`.
-/
theorem fIwasawa_exists_max_pivot (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (M : Matrix (Fin n) (Fin n) L)
    (hM : fIwasawaUn σ M) (r : ℕ) (hT : fIwasawaTri r M) (ρ : Fin n) (hρr : ρ.val = r)
    (hρ : ρ < Fin.rev ρ) :
    ∃ k, fIwasawaKm σ k ∧ fIwasawaTri r (k * M) ∧ (k * M) ρ ρ ≠ 0 ∧
      ∀ i, ρ ≤ i → i ≤ Fin.rev ρ → Valued.v ((k * M) i ρ) ≤ Valued.v ((k * M) ρ ρ) := by
  classical
  set W : Finset (Fin n) := Finset.univ.filter (fun i => ρ ≤ i ∧ i ≤ Fin.rev ρ) with hW
  have hmem : ∀ i, ρ ≤ i → i ≤ Fin.rev ρ → i ∈ W := fun i h1 h2 =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, h1, h2⟩
  have hout : ∀ i, i ∉ W → i < ρ ∨ Fin.rev ρ < i := by
    intro i hi
    by_contra h
    push_neg at h
    exact hi (hmem i h.1 h.2)
  have hρW : ρ ∈ W := hmem ρ le_rfl hρ.le
  have hcz := fIwasawa_col_zero σ M hM r hT ρ hρr hρ

  have hex : ∃ j ∈ W, M j ρ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hgram := fIwasawa_gram_un σ M hM (Fin.rev ρ) ρ
    rw [if_pos (Fin.rev_rev ρ).symm] at hgram
    have h0 : ∑ j, σ (M (Fin.rev j) (Fin.rev ρ)) * M j ρ = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj1 : j < ρ
      · have hjr : j.val < r := by rw [← hρr]; exact hj1
        rw [(fIwasawa_rows σ M hM r hT j hjr).2 (Fin.rev ρ) (Fin.rev_lt_rev.2 hj1), map_zero, zero_mul]
      · by_cases hj2 : Fin.rev ρ < j
        · rw [hcz j hj2, mul_zero]
        · rw [hcon j (hmem j (not_lt.1 hj1) (not_lt.1 hj2)), mul_zero]
    rw [h0] at hgram
    exact zero_ne_one hgram
  obtain ⟨j₀, hj₀W, hj₀⟩ := hex
  obtain ⟨a₀, ha₀W, ha₀max⟩ := Finset.exists_max_image W (fun i => Valued.v (M i ρ)) ⟨ρ, hρW⟩
  have hnz : ∀ a ∈ W, (∀ i ∈ W, Valued.v (M i ρ) ≤ Valued.v (M a ρ)) → Valued.v (M a ρ) ≠ 0 := by
    intro a _ hamax h0
    have h1 := hamax j₀ hj₀W
    rw [h0] at h1
    exact hj₀ ((Valuation.zero_iff _).1 (le_antisymm h1 zero_le'))
  have hV := hnz a₀ ha₀W ha₀max
  have hWrev : ∀ j ∈ W, Fin.rev j ∈ W := by
    intro j hj
    obtain ⟨_, h1, h2⟩ := Finset.mem_filter.1 hj
    exact hmem _ (by simpa using Fin.rev_le_rev.2 h2) (Fin.rev_le_rev.2 h1)

  obtain ⟨a, haW, hamax, hne⟩ : ∃ a ∈ W, (∀ i ∈ W, Valued.v (M i ρ) ≤ Valued.v (M a ρ)) ∧
      a ≠ Fin.rev a := by
    by_cases h₀ : a₀ = Fin.rev a₀
    · by_contra hcon
      push_neg at hcon
      have hlt : ∀ i ∈ W, i ≠ a₀ → Valued.v (M i ρ) < Valued.v (M a₀ ρ) := by
        intro i hi hia
        refine lt_of_le_of_ne (ha₀max i hi) fun heq => ?_
        have hii : i = Fin.rev i := hcon i hi fun k hk => (ha₀max k hk).trans_eq heq.symm
        apply hia
        have e1 := congrArg Fin.val hii
        have e2 := congrArg Fin.val h₀
        rw [Fin.val_rev] at e1 e2
        exact Fin.ext (by omega)
      have hiso := fIwasawa_iso σ M hM ρ hρ
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a₀)] at hiso
      have hbig : Valued.v (σ (M (Fin.rev a₀) ρ) * M a₀ ρ) = Valued.v (M a₀ ρ) * Valued.v (M a₀ ρ) := by
        rw [← h₀, map_mul, hσv]
      have hpos : (0 : WithZero (Multiplicative ℤ)) < Valued.v (M a₀ ρ) * Valued.v (M a₀ ρ) :=
        zero_lt_iff.2 (mul_ne_zero hV hV)
      have hsmall : Valued.v (∑ j ∈ Finset.univ.erase a₀, σ (M (Fin.rev j) ρ) * M j ρ)
          < Valued.v (M a₀ ρ) * Valued.v (M a₀ ρ) := by
        apply Valuation.map_sum_lt _ (mul_ne_zero hV hV)
        intro j hj
        have hja := Finset.ne_of_mem_erase hj
        rw [map_mul, hσv]
        by_cases hjW : j ∈ W
        · have hra : Fin.rev j ≠ a₀ := by
            intro h; apply hja; rw [← Fin.rev_rev j, h, ← h₀]
          exact mul_lt_mul_of_le_of_lt_of_nonneg_of_pos (ha₀max _ (hWrev j hjW)) (hlt j hjW hja)
            zero_le' (zero_lt_iff.2 hV)
        · rcases hout j hjW with h | h
          · rw [hcz (Fin.rev j) (Fin.rev_lt_rev.2 h), map_zero, zero_mul]; exact hpos
          · rw [hcz j h, map_zero, mul_zero]; exact hpos
      have h3 : σ (M (Fin.rev a₀) ρ) * M a₀ ρ = -∑ j ∈ Finset.univ.erase a₀, σ (M (Fin.rev j) ρ) * M j ρ :=
        eq_neg_of_add_eq_zero_left hiso
      rw [h3, Valuation.map_neg] at hbig
      rw [hbig] at hsmall
      exact lt_irrefl _ hsmall
    · exact ⟨a₀, ha₀W, ha₀max, h₀⟩
  have haW' := Finset.mem_filter.1 haW
  obtain ⟨π, hπa, hπrev, hπfix⟩ := fIwasawa_perm ρ a hρ haW'.2.1 haW'.2.2 hne
  have hπW : ∀ i ∈ W, π i ∈ W := by
    intro i hi
    by_contra hni
    have hii : π i = i := π.injective (hπfix (π i) (hout _ hni))
    rw [hii] at hni
    exact hni hi
  have hInt : fIwasawaInt (fIwasawaP (L := L) π) := by
    intro i j
    simp only [fIwasawaP, Matrix.of_apply]
    split_ifs <;> simp
  refine ⟨fIwasawaP π, ⟨permMatrix_isUnitary_of_commute_rev σ π hπrev, hInt⟩, ?_, ?_, ?_⟩
  · intro i j hj hji
    rw [permMatrix_mul_apply₂]
    by_cases hiW : i ∈ W
    · have hπi := Finset.mem_filter.1 (hπW i hiW)
      have hjρ : j < ρ := by rw [Fin.lt_iff_val_lt_val, hρr]; exact hj
      exact hT (π i) j hj (lt_of_lt_of_le hjρ hπi.2.1)
    · rw [hπfix i (hout i hiW)]
      exact hT i j hj hji
  · rw [permMatrix_mul_apply₂, hπa]
    intro h0
    exact hnz a haW hamax (by rw [h0, map_zero])
  · intro i h1 h2
    rw [permMatrix_mul_apply₂, permMatrix_mul_apply₂, hπa]
    exact hamax (π i) (hπW i (hmem i h1 h2))

/- English proof (translation)
Establish `h1 : fIwasawaH σ (Pi.single (Fin.rev ρ) 1) w = 0`. Unfold `fIwasawaH`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hj : j = ρ`. Substitute `hj` using the available equality.

Rewrite using `[hwρ, mul_zero]`. Rewrite using `[Pi.single_eq_of_ne (by rwa [Ne, Fin.rev_inj]), map_zero, zero_mul]`. Establish `h2 : fIwasawaH σ z w = 0`. Unfold `fIwasawaH`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hzj : z (Fin.rev j) = 0`. Rewrite using `[hzj, map_zero, zero_mul]`. Take `⟨ha, hb⟩` from `hz _ hzj`. Establish `hj1 : ρ < j` using `by simpa using Fin.rev_lt_rev.1 hb`. Establish `hj2 : j < Fin.rev ρ` using `by simpa using Fin.rev_lt_rev.2 ha`.

Rewrite using `[hw j hj1 hj2, mul_zero]`. Rewrite using `[fIwasawa_E_mulVec, h1, h2]`. Simplify using the standard rewrite rules.
-/
theorem fIwasawa_E_fix (ρ : Fin n) (z : Fin n → L) (c : L)
    (hz : ∀ t, z t ≠ 0 → ρ < t ∧ t < Fin.rev ρ) (w : Fin n → L) (hwρ : w ρ = 0)
    (hw : ∀ t, ρ < t → t < Fin.rev ρ → w t = 0) :
    fIwasawaE σ (Pi.single (Fin.rev ρ) 1) z c *ᵥ w = w := by
  have h1 : fIwasawaH σ (Pi.single (Fin.rev ρ) 1) w = 0 := by
    unfold fIwasawaH
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j = ρ
    · subst hj; rw [hwρ, mul_zero]
    · rw [Pi.single_eq_of_ne (by rwa [Ne, Fin.rev_inj]), map_zero, zero_mul]
  have h2 : fIwasawaH σ z w = 0 := by
    unfold fIwasawaH
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hzj : z (Fin.rev j) = 0
    · rw [hzj, map_zero, zero_mul]
    · obtain ⟨ha, hb⟩ := hz _ hzj
      have hj1 : ρ < j := by simpa using Fin.rev_lt_rev.1 hb
      have hj2 : j < Fin.rev ρ := by simpa using Fin.rev_lt_rev.2 ha
      rw [hw j hj1 hj2, mul_zero]
  rw [fIwasawa_E_mulVec, h1, h2]
  simp

end FIwasawaStep

end Formalism.UG.P
