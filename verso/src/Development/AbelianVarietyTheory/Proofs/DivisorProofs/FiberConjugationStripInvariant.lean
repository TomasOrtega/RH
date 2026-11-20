import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtMapApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtMapCompStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtMapOneStatement
open Matrix MeasureTheory Set GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped ContDiff

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorsionForm.StrNConj

/- English proof (translation)
Establish `hi : i ∉ T` using `fun h' => lt_irrefl _ (h i h')`. Unfold `genProd`. Rewrite using `[Finset.sort_insert (· ≤ ·) (fun b hb => (h b hb).le) hi]`. Both sides reduce to the same expression.
-/
theorem genProd_insert {m : ℕ} (φ : Matrix (Fin m) (Fin m) ℂ) (i : Fin m) (T : Finset (Fin m))
    (h : ∀ x ∈ T, i < x) : genProd φ (insert i T) = ∑ k, φ i k • wedge k (genProd φ T) := by
  have hi : i ∉ T := fun h' => lt_irrefl _ (h i h')
  unfold genProd
  rw [Finset.sort_insert (· ≤ ·) (fun b hb => (h b hb).le) hi]
  rfl

/- English proof (translation)
Simplify using `[genProd]`.
-/
theorem genProd_empty {m : ℕ} (φ : Matrix (Fin m) (Fin m) ℂ) : genProd φ ∅ = Pi.single ∅ 1 := by
  simp [genProd]

/- English proof (translation)
Unfold `wedge at h`. Use `split_ifs at h with hk`. Conclude with `⟨hk, fun h0 => h (by rw [h0, mul_zero])⟩`. Conclude with `absurd rfl h`.
-/
theorem wedge_ne_zero {m : ℕ} {k : Fin m} {w : Ext m} {T : Finset (Fin m)} (h : wedge k w T ≠ 0) :
    k ∈ T ∧ w (T.erase k) ≠ 0 := by
  unfold wedge at h
  split_ifs at h with hk
  · exact ⟨hk, fun h0 => h (by rw [h0, mul_zero])⟩
  · exact absurd rfl h

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on_min with`. Consider the case `empty`. Introduce `T' h`. Rewrite `h` using `[genProd_empty]`. Assume the negation of the conclusion as `hc`.

Establish `: T' ≠ ∅` using `by rintro rfl; simp at hc`. Conclude with `h (by simp [Pi.single_apply, this])`. Consider the case `insert i T hi ih`. Introduce `T' h`. Establish `hiT : i ∉ T` using `fun h' => lt_irrefl _ (hi i h')`.

Rewrite `h` using `[genProd_insert φ i T hi, Finset.sum_apply]`. Take `⟨k, -, hk⟩` from `Finset.exists_ne_zero_of_sum_ne_zero h`. Simplify using `only [Pi.smul_apply, smul_eq_mul] at hk`. Establish `hw` using `wedge_ne_zero (right_ne_zero_of_mul hk)`. Establish `h1` using `ih _ hw.2`.

Rewrite `h1` using `[Finset.card_erase_of_mem hw.1]`. Establish `: 0 < T'.card` using `Finset.card_pos.mpr ⟨k, hw.1⟩`. Rewrite using `[Finset.card_insert_of_notMem hiT]`. Use linear arithmetic over natural numbers and integers.
-/
theorem genProd_card {m : ℕ} (φ : Matrix (Fin m) (Fin m) ℂ) (T : Finset (Fin m)) :
    ∀ T' : Finset (Fin m), genProd φ T T' ≠ 0 → T'.card = T.card := by
  induction T using Finset.induction_on_min with
  | empty =>
    intro T' h
    rw [genProd_empty] at h
    by_contra hc
    have : T' ≠ ∅ := by rintro rfl; simp at hc
    exact h (by simp [Pi.single_apply, this])
  | insert i T hi ih =>
    intro T' h
    have hiT : i ∉ T := fun h' => lt_irrefl _ (hi i h')
    rw [genProd_insert φ i T hi, Finset.sum_apply] at h
    obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    simp only [Pi.smul_apply, smul_eq_mul] at hk
    have hw := wedge_ne_zero (right_ne_zero_of_mul hk)
    have h1 := ih _ hw.2
    rw [Finset.card_erase_of_mem hw.1] at h1
    have : 0 < T'.card := Finset.card_pos.mpr ⟨k, hw.1⟩
    rw [Finset.card_insert_of_notMem hiT]
    omega

section Join
variable {m g : ℕ}

/- English proof (translation)
Simplify using `[join, eq_comm]`.
-/
theorem mem_join (S : Finset (Fin m)) (I : Finset (Fin g)) (x : Fin (m + g)) :
    x ∈ join S I ↔ (∃ s ∈ S, x = Fin.castAdd g s) ∨ (∃ j ∈ I, x = Fin.natAdd m j) := by
  simp [join, eq_comm]

/- English proof (translation)
Simplify using `[join, Fin.ext_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(⟨a, ha, e⟩ | ⟨a, ha, e⟩)`. Rewrite `ha` using `[show a = s from Fin.ext e]`. Then use the resulting hypothesis. Use linear arithmetic over natural numbers and integers.

Introduce `h`. Conclude with `Or.inl ⟨s, h, rfl⟩`.
-/
theorem castAdd_mem_join (S : Finset (Fin m)) (I : Finset (Fin g)) (s : Fin m) :
    Fin.castAdd g s ∈ join S I ↔ s ∈ S := by
  simp [join, Fin.ext_iff]
  constructor
  · rintro (⟨a, ha, e⟩ | ⟨a, ha, e⟩)
    · rwa [show a = s from Fin.ext e] at ha
    · omega
  · intro h; exact Or.inl ⟨s, h, rfl⟩

/- English proof (translation)
Simplify using `[join, Fin.ext_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(⟨a, ha, e⟩ | ⟨a, ha, e⟩)`. Use linear arithmetic over natural numbers and integers. Rewrite `ha` using `[show a = j from Fin.ext (by omega)]`. Then use the resulting hypothesis.

Introduce `h`. Conclude with `Or.inr ⟨j, h, rfl⟩`.
-/
theorem natAdd_mem_join (S : Finset (Fin m)) (I : Finset (Fin g)) (j : Fin g) :
    Fin.natAdd m j ∈ join S I ↔ j ∈ I := by
  simp [join, Fin.ext_iff]
  constructor
  · rintro (⟨a, ha, e⟩ | ⟨a, ha, e⟩)
    · omega
    · rwa [show a = j from Fin.ext (by omega)] at ha
  · intro h; exact Or.inr ⟨j, h, rfl⟩

end Join
end GlobalTheory.TorsionForm.StrNConj

namespace GlobalTheory.TorsionForm.StrNConj
section Join2
variable {m g : ℕ}

/- English proof (translation)
Introduce and unpack `⟨S, I⟩ ⟨S', I'⟩ h`. Simplify using `only at h`. Establish `h1 : S = S'`. Use extensionality with `s`. Rewrite using `[← castAdd_mem_join S I, ← castAdd_mem_join S' I', h]`.

Establish `h2 : I = I'`. Use extensionality with `j`. Rewrite using `[← natAdd_mem_join S I, ← natAdd_mem_join S' I', h]`. Rewrite using `[h1, h2]`.
-/
theorem join_injective : Function.Injective (fun p : Finset (Fin m) × Finset (Fin g) => join p.1 p.2) := by
  rintro ⟨S, I⟩ ⟨S', I'⟩ h
  simp only at h
  have h1 : S = S' := by
    ext s; rw [← castAdd_mem_join S I, ← castAdd_mem_join S' I', h]
  have h2 : I = I' := by
    ext j; rw [← natAdd_mem_join S I, ← natAdd_mem_join S' I', h]
  rw [h1, h2]

/- English proof (translation)
Introduce `T`. Use `⟨(Finset.univ.filter (fun s => Fin.castAdd g s ∈ T), Finset.univ.filter (fun j => Fin.natAdd m j ∈ T)), ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Proceed by induction on `x using Fin.addCases with`. Consider the case `left s => simp only [castAdd_mem_join]`.

Simplify using the standard rewrite rules. Consider the case `right j => simp only [natAdd_mem_join]`. Simplify using the standard rewrite rules.
-/
theorem join_surjective : Function.Surjective (fun p : Finset (Fin m) × Finset (Fin g) => join p.1 p.2) := by
  intro T
  refine ⟨(Finset.univ.filter (fun s => Fin.castAdd g s ∈ T), Finset.univ.filter (fun j => Fin.natAdd m j ∈ T)), ?_⟩
  ext x
  induction x using Fin.addCases with
  | left s => simp only [castAdd_mem_join]; simp
  | right j => simp only [natAdd_mem_join]; simp

/- English proof (translation)
Rewrite using `[← Fintype.sum_prod_type']`. Conclude with `(Fintype.sum_bijective _ ⟨join_injective, join_surjective⟩ _ _ (fun _ => rfl)).symm`.
-/
theorem sum_join (f : Finset (Fin (m + g)) → ℂ) : ∑ T, f T = ∑ S, ∑ I, f (join S I) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_bijective _ ⟨join_injective, join_surjective⟩ _ _ (fun _ => rfl)).symm

/- English proof (translation)
Simplify using `[join]`.
-/
theorem card_join_empty (I : Finset (Fin g)) : (join (∅ : Finset (Fin m)) I).card = I.card := by
  simp [join]

/- English proof (translation)
Simplify using `[join, Finset.map_insert, Finset.insert_union]`.
-/
theorem join_insert_left (s : Fin m) (S : Finset (Fin m)) (I : Finset (Fin g)) :
    join (insert s S) I = insert (Fin.castAdd g s) (join S I) := by
  simp [join, Finset.map_insert, Finset.insert_union]

/- English proof (translation)
Simplify using `[join, Finset.map_insert]`.
-/
theorem join_insert_right (j : Fin g) (I : Finset (Fin g)) :
    join (∅ : Finset (Fin m)) (insert j I) = insert (Fin.natAdd m j) (join ∅ I) := by
  simp [join, Finset.map_insert]

/- English proof (translation)
Use extensionality with `x`. Proceed by induction on `x using Fin.addCases with`. Consider the case `left t`. Rewrite using `[Finset.mem_erase, castAdd_mem_join, castAdd_mem_join, Finset.mem_erase]`. Simplify using `[Fin.ext_iff]`.

Consider the case `right j`. Rewrite using `[Finset.mem_erase, natAdd_mem_join, natAdd_mem_join]`. Simplify using `[Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers.
-/
theorem join_erase_left (s : Fin m) (S : Finset (Fin m)) (I : Finset (Fin g)) :
    (join S I).erase (Fin.castAdd g s) = join (S.erase s) I := by
  ext x
  induction x using Fin.addCases with
  | left t =>
    rw [Finset.mem_erase, castAdd_mem_join, castAdd_mem_join, Finset.mem_erase]
    simp [Fin.ext_iff]
  | right j =>
    rw [Finset.mem_erase, natAdd_mem_join, natAdd_mem_join]
    simp [Fin.ext_iff]
    omega

end Join2

section Fib
variable {n g : ℕ}

/- English proof (translation)
Proceed by induction on `k using Fin.addCases with`. Consider the case `left t => simp [fibMat, Matrix.one_apply, eq_comm]`. Consider the case `right j => simp [fibMat, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers.
-/
theorem fibMat_castAdd (a : Matrix (Fin g) (Fin g) ℂ) (s : Fin (n + n)) (k : Fin (n + n + g)) :
    fibMat n a (Fin.castAdd g s) k = if k = Fin.castAdd g s then 1 else 0 := by
  induction k using Fin.addCases with
  | left t => simp [fibMat, Matrix.one_apply, eq_comm]
  | right j => simp [fibMat, Fin.ext_iff]; omega

/- English proof (translation)
Simplify using `[fibMat]`.
-/
theorem fibMat_natAdd_castAdd (a : Matrix (Fin g) (Fin g) ℂ) (j : Fin g) (s : Fin (n + n)) :
    fibMat n a (Fin.natAdd (n + n) j) (Fin.castAdd g s) = 0 := by
  simp [fibMat]

end Fib
end GlobalTheory.TorsionForm.StrNConj

namespace GlobalTheory.TorsionForm.StrNConj
variable {n g : ℕ}

/- English proof (translation)
Introduce `x hx`. Rewrite `hx` using `[mem_join]`. Break down `hx with ⟨s, hs, -⟩ | ⟨l, hl, rfl⟩` into its components or cases. Simplify using `at hs`. Use `hj l hl` as an intermediate fact.

Rewrite `this`, the goal using `[Fin.lt_iff_val_lt_val]`. Simplify using `only [Fin.val_natAdd]`. Use linear arithmetic over natural numbers and integers.
-/
theorem natAdd_lt_of_mem_join (j : Fin g) (J : Finset (Fin g)) (hj : ∀ x ∈ J, j < x) :
    ∀ x ∈ join (∅ : Finset (Fin (n + n))) J, Fin.natAdd (n + n) j < x := by
  intro x hx
  rw [mem_join] at hx
  rcases hx with ⟨s, hs, -⟩ | ⟨l, hl, rfl⟩
  · simp at hs
  · have := hj l hl
    rw [Fin.lt_iff_val_lt_val] at this ⊢
    simp only [Fin.val_natAdd]
    omega

/- English proof (translation)
Proceed by induction on `J using Finset.induction_on_min with`. Consider the case `empty`. Introduce `T h s hs`. Establish `hT : T ≠ ∅` using `by rintro rfl; simp at hs`. Establish `: join (∅ : Finset (Fin (n + n))) (∅ : Finset (Fin g)) = ∅` using `by simp [join]`.

Rewrite `h` using `[this, genProd_empty]`. Conclude with `h (by simp [Pi.single_apply, hT])`. Consider the case `insert j J hj ih`. Introduce `T h s hs`. Rewrite `h` using `[join_insert_right, genProd_insert _ _ _ (natAdd_lt_of_mem_join j J hj), Finset.sum_apply]`.

Take `⟨k, -, hk⟩` from `Finset.exists_ne_zero_of_sum_ne_zero h`. Simplify using `only [Pi.smul_apply, smul_eq_mul] at hk`. Establish `hw` using `wedge_ne_zero (right_ne_zero_of_mul hk)`. Establish `hφ` using `left_ne_zero_of_mul hk`. Proceed by induction on `k using Fin.addCases with`.

Consider the case `left t => exact hφ (fibMat_natAdd_castAdd a j t)`. Consider the case `right l`. Use `ih _ hw.2 s ?_` and prove the remaining obligations. Rewrite using `[Finset.mem_erase]`. Use `⟨?_, hs⟩` and prove the remaining obligations.

Simplify using `[Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers.
-/
theorem genProd_fib_support (a : Matrix (Fin g) (Fin g) ℂ) (J : Finset (Fin g)) :
    ∀ T : Finset (Fin (n + n + g)), genProd (fibMat n a) (join ∅ J) T ≠ 0 →
      ∀ s : Fin (n + n), Fin.castAdd g s ∉ T := by
  induction J using Finset.induction_on_min with
  | empty =>
    intro T h s hs
    have hT : T ≠ ∅ := by rintro rfl; simp at hs
    have : join (∅ : Finset (Fin (n + n))) (∅ : Finset (Fin g)) = ∅ := by simp [join]
    rw [this, genProd_empty] at h
    exact h (by simp [Pi.single_apply, hT])
  | insert j J hj ih =>
    intro T h s hs
    rw [join_insert_right, genProd_insert _ _ _ (natAdd_lt_of_mem_join j J hj), Finset.sum_apply] at h
    obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    simp only [Pi.smul_apply, smul_eq_mul] at hk
    have hw := wedge_ne_zero (right_ne_zero_of_mul hk)
    have hφ := left_ne_zero_of_mul hk
    induction k using Fin.addCases with
    | left t => exact hφ (fibMat_natAdd_castAdd a j t)
    | right l =>
      refine ih _ hw.2 s ?_
      rw [Finset.mem_erase]
      refine ⟨?_, hs⟩
      simp [Fin.ext_iff]
      omega

end GlobalTheory.TorsionForm.StrNConj

namespace GlobalTheory.TorsionForm.StrNConj
variable {n g : ℕ}

/- English proof (translation)
Proceed by induction on `S' using Finset.induction_on_min with`. Consider the case `empty`. Introduce `S I`. Use `split_ifs with h`. Substitute `h` using the available equality.

Both sides reduce to the same expression. Assume the negation of the conclusion as `hne`. Take `⟨s, hs⟩` from `Finset.nonempty_iff_ne_empty.mpr (Ne.symm h)`. Conclude with `genProd_fib_support a J _ hne s ((castAdd_mem_join S I s).mpr hs)`. Consider the case `insert s S' hs ih`.

Introduce `S I`. Establish `hlt : ∀ x ∈ join S' J, Fin.castAdd g s < x`. Introduce `x hx`. Rewrite `hx` using `[mem_join]`. Break down `hx with ⟨t, ht, rfl⟩ | ⟨l, -, rfl⟩` into its components or cases.

Use `Fin.lt_iff_val_lt_val.mp (hs t ht)` as an intermediate fact. Rewrite using `[Fin.lt_iff_val_lt_val]`. Simplify using `only [Fin.val_castAdd]`. Use linear arithmetic over natural numbers and integers. Use `s.isLt` as an intermediate fact.

Rewrite using `[Fin.lt_iff_val_lt_val]`. Simplify using `only [Fin.val_castAdd, Fin.val_natAdd]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[join_insert_left, genProd_insert _ _ _ hlt]`. Establish `hsum : ∑ k, fibMat n a (Fin.castAdd g s) k • wedge k (genProd (fibMat n a) (join S' J)) = wedge (Fin.castAdd g s) (genProd (fibMat n a) (join S' J))`.

Simplify using `[fibMat_castAdd]`. Rewrite using `[hsum]`. Establish `hsS' : s ∉ S'` using `fun h => lt_irrefl _ (hs s h)`. Distinguish the cases in `hsS : s ∈ S`. Establish `hmem : Fin.castAdd g s ∈ join S I` using `(castAdd_mem_join _ _ _).mpr hsS`.

Simplify using `only [wedge, hmem, if_true]`. Rewrite using `[join_erase_left, ih]`. Establish `hiff : (insert s S' = S) ↔ (S' = S.erase s)` using `⟨fun h => h ▸ (Finset.erase_insert hsS').symm, fun h => h ▸ Finset.insert_erase hsS⟩`. Distinguish the cases in `he : S' = S.erase s`. Rewrite using `[if_pos he, if_pos (hiff.mpr he)]`.

Establish `hsg : sgn (Fin.castAdd g s) (join S I) = 1`. Unfold `sgn`. Establish `hf : (join S I).filter (· < Fin.castAdd g s) = ∅`. Use extensionality with `x`. Simplify using `only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and, not_lt]`.

Introduce `hx`. Rewrite `hx` using `[mem_join]`. Break down `hx with ⟨t, ht, rfl⟩ | ⟨l, -, rfl⟩` into its components or cases. Distinguish the cases in `hts : t = s`. Rewrite using `[hts]`.

Establish `htS' : t ∈ S'` using `by rw [he]; exact Finset.mem_erase.mpr ⟨hts, ht⟩`. Use `Fin.lt_iff_val_lt_val.mp (hs t htS')` as an intermediate fact. Rewrite using `[Fin.le_iff_val_le_val]`. Simplify using `only [Fin.val_castAdd]`. Use linear arithmetic over natural numbers and integers.

Use `s.isLt` as an intermediate fact. Rewrite using `[Fin.le_iff_val_le_val]`. Simplify using `only [Fin.val_castAdd, Fin.val_natAdd]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hf]`.

Simplify using the standard rewrite rules. Rewrite using `[hsg, one_mul]`. Rewrite using `[if_neg he, if_neg (fun h => he (hiff.mp h)), mul_zero]`. Establish `hmem : Fin.castAdd g s ∉ join S I` using `fun h => hsS ((castAdd_mem_join _ _ _).mp h)`. Simplify using `only [wedge, hmem, if_false]`.

Rewrite using `[if_neg]`. Introduce and unpack `rfl`. Conclude with `hsS (Finset.mem_insert_self _ _)`.
-/
theorem genProd_join (a : Matrix (Fin g) (Fin g) ℂ) (S' : Finset (Fin (n + n))) (J : Finset (Fin g)) :
    ∀ (S : Finset (Fin (n + n))) (I : Finset (Fin g)), genProd (fibMat n a) (join S' J) (join S I) =
      if S' = S then genProd (fibMat n a) (join ∅ J) (join ∅ I) else 0 := by
  induction S' using Finset.induction_on_min with
  | empty =>
    intro S I
    split_ifs with h
    · subst h; rfl
    · by_contra hne
      obtain ⟨s, hs⟩ := Finset.nonempty_iff_ne_empty.mpr (Ne.symm h)
      exact genProd_fib_support a J _ hne s ((castAdd_mem_join S I s).mpr hs)
  | insert s S' hs ih =>
    intro S I
    have hlt : ∀ x ∈ join S' J, Fin.castAdd g s < x := by
      intro x hx
      rw [mem_join] at hx
      rcases hx with ⟨t, ht, rfl⟩ | ⟨l, -, rfl⟩
      · have := Fin.lt_iff_val_lt_val.mp (hs t ht)
        rw [Fin.lt_iff_val_lt_val]; simp only [Fin.val_castAdd]; omega
      · have := s.isLt
        rw [Fin.lt_iff_val_lt_val]; simp only [Fin.val_castAdd, Fin.val_natAdd]; omega
    rw [join_insert_left, genProd_insert _ _ _ hlt]
    have hsum : ∑ k, fibMat n a (Fin.castAdd g s) k • wedge k (genProd (fibMat n a) (join S' J)) =
        wedge (Fin.castAdd g s) (genProd (fibMat n a) (join S' J)) := by
      simp [fibMat_castAdd]
    rw [hsum]
    have hsS' : s ∉ S' := fun h => lt_irrefl _ (hs s h)
    by_cases hsS : s ∈ S
    · have hmem : Fin.castAdd g s ∈ join S I := (castAdd_mem_join _ _ _).mpr hsS
      simp only [wedge, hmem, if_true]
      rw [join_erase_left, ih]
      have hiff : (insert s S' = S) ↔ (S' = S.erase s) :=
        ⟨fun h => h ▸ (Finset.erase_insert hsS').symm, fun h => h ▸ Finset.insert_erase hsS⟩
      by_cases he : S' = S.erase s
      · rw [if_pos he, if_pos (hiff.mpr he)]
        have hsg : sgn (Fin.castAdd g s) (join S I) = 1 := by
          unfold sgn
          have hf : (join S I).filter (· < Fin.castAdd g s) = ∅ := by
            ext x
            simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and, not_lt]
            intro hx
            rw [mem_join] at hx
            rcases hx with ⟨t, ht, rfl⟩ | ⟨l, -, rfl⟩
            · by_cases hts : t = s
              · rw [hts]
              · have htS' : t ∈ S' := by rw [he]; exact Finset.mem_erase.mpr ⟨hts, ht⟩
                have := Fin.lt_iff_val_lt_val.mp (hs t htS')
                rw [Fin.le_iff_val_le_val]; simp only [Fin.val_castAdd]; omega
            · have := s.isLt
              rw [Fin.le_iff_val_le_val]; simp only [Fin.val_castAdd, Fin.val_natAdd]; omega
          rw [hf]; simp
        rw [hsg, one_mul]
      · rw [if_neg he, if_neg (fun h => he (hiff.mp h)), mul_zero]
    · have hmem : Fin.castAdd g s ∉ join S I := fun h => hsS ((castAdd_mem_join _ _ _).mp h)
      simp only [wedge, hmem, if_false]
      rw [if_neg]
      rintro rfl
      exact hsS (Finset.mem_insert_self _ _)

end GlobalTheory.TorsionForm.StrNConj

namespace GlobalTheory.TorsionForm.StrNConj
variable {n g : ℕ}

/- English proof (translation)
Rewrite using `[extMap_apply, Finset.sum_eq_single T]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Pi.single_apply, hb]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ T) h`.
-/
theorem extMap_single {m : ℕ} (φ : Matrix (Fin m) (Fin m) ℂ) (T : Finset (Fin m)) :
    extMap φ (Pi.single T 1) = genProd φ T := by
  rw [extMap_apply, Finset.sum_eq_single T]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · intro h; exact absurd (Finset.mem_univ T) h

/- English proof (translation)
Rewrite using `[extMap_apply, Finset.sum_apply]`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Rewrite using `[sum_join]`. Repeatedly rewrite using `[genProd_join a _ _ S I]`. Rewrite using `[Finset.sum_eq_single S]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[hb]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ S) h`.
-/
theorem extMap_fibMat_join (a : Matrix (Fin g) (Fin g) ℂ) (v : Ext (n + n + g))
    (S : Finset (Fin (n + n))) (I : Finset (Fin g)) :
    extMap (fibMat n a) v (join S I) =
      ∑ J, v (join S J) * genProd (fibMat n a) (join ∅ J) (join ∅ I) := by
  rw [extMap_apply, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [sum_join]
  simp_rw [genProd_join a _ _ S I]
  rw [Finset.sum_eq_single S]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ S) h

/- English proof (translation)
Establish `hu : u = ∑ T, u T • (Pi.single T (1 : ℂ) : Ext N)`. Use extensionality with `T0`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Use `conv_lhs => rw [hu]`. Rewrite using `[map_sum, Finset.sum_apply]`.

Simplify using `[map_smul]`.
-/
theorem clm_apply_expand {N : ℕ} (K : Ext N →L[ℂ] Ext N) (u : Ext N) (T' : Finset (Fin N)) :
    K u T' = ∑ T, u T * K (Pi.single T 1) T' := by
  have hu : u = ∑ T, u T • (Pi.single T (1 : ℂ) : Ext N) := by
    ext T0; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hu]
  rw [map_sum, Finset.sum_apply]
  simp [map_smul]

/- English proof (translation)
Rewrite using `[clm_apply_expand, sum_join, Finset.sum_eq_single ∅]`. Introduce `b _ hb`. Conclude with `Finset.sum_eq_zero (fun J _ => by rw [genProd_join a ∅ I b J, if_neg (Ne.symm hb), zero_mul])`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem clm_apply_fib (a : Matrix (Fin g) (Fin g) ℂ) (K : Ext (n + n + g) →L[ℂ] Ext (n + n + g))
    (I : Finset (Fin g)) (T' : Finset (Fin (n + n + g))) :
    K (genProd (fibMat n a) (join ∅ I)) T' =
      ∑ J, genProd (fibMat n a) (join ∅ I) (join ∅ J) * K (Pi.single (join ∅ J) 1) T' := by
  rw [clm_apply_expand, sum_join, Finset.sum_eq_single ∅]
  · intro b _ hb
    exact Finset.sum_eq_zero (fun J _ => by rw [genProd_join a ∅ I b J, if_neg (Ne.symm hb), zero_mul])
  · intro h; exact absurd (Finset.mem_univ _) h

end GlobalTheory.TorsionForm.StrNConj

namespace GlobalTheory.TorsionForm.StrNConj

/- English proof (translation)
Establish `haa : a * a' = 1` using `mul_eq_one_comm.mp h`. Establish `hid : extMap (fibMat n a') ∘L extMap (fibMat n a) = ContinuousLinearMap.id ℂ (Ext (n + n + g))`. Rewrite using `[GlobalTheory.T.extMap_comp_extMap, fibMat_mul, haa, fibMat_one, GlobalTheory.T.extMap_one']`. Establish `orth : ∀ J J' : Finset (Fin g), ∑ I, genProd (fibMat n a) (join ∅ J') (join ∅ I) * genProd (fibMat n a') (join ∅ I) (join ∅ J) = if J' = J then 1 else 0`. Introduce `J J'`.

Establish `h1` using `congrArg (fun f : Ext (n + n + g) →L[ℂ] Ext (n + n + g) => f (Pi.single (join ∅ J') 1) (join ∅ J)) hid`. Simplify using `only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h1`. Rewrite `h1` using `[extMap_fibMat_join, extMap_single]`. Rewrite using `[h1, Pi.single_apply]`. Distinguish the cases in `hJ : J' = J`.

Substitute `hJ` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg hJ, if_neg]`. Introduce `he`. Use `join_injective (m := n + n) (g := g) (a₁ := (∅, J)) (a₂ := (∅, J')) he` as an intermediate fact.

Conclude with `hJ (Prod.ext_iff.mp this).2.symm`. Establish `hcard : ∀ I J : Finset (Fin g), genProd (fibMat n a') (join ∅ I) (join ∅ J) ≠ 0 → J.card = I.card`. Introduce `I J hne`. Use `genProd_card _ _ _ hne` as an intermediate fact. Rewrite `this` using `[card_join_empty, card_join_empty]`. Then use the resulting hypothesis.

Use function extensionality and compare the values at `S`. Simplify using `only [strN, ContinuousLinearMap.comp_apply]`. Repeatedly rewrite using `[extMap_fibMat_join a, extMap_single, clm_apply_fib a']`. Repeatedly rewrite using `[Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `conv_lhs => enter [2, J']`. Rewrite using `[Finset.sum_comm]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun J _ => ?_)` and prove the remaining obligations. Establish `key : ∀ J' I : Finset (Fin g), (-1) ^ I.card * (I.card : ℂ) * (genProd (fibMat n a') (join ∅ I) (join ∅ J) * K (Pi.single (join ∅ J) 1) (join S J') * genProd (fibMat n a) (join ∅ J') (join ∅ I)) = ((-1) ^ J.card * (J.card : ℂ) * K (Pi.single (join ∅ J) 1) (join S J')) * (genProd …`.

Introduce `J' I`. Distinguish the cases in `hc : genProd (fibMat n a') (join ∅ I) (join ∅ J) = 0`. Simplify using `[hc]`. Rewrite using `[hcard I J hc]`. Expand and normalize the polynomial expressions, which then agree.

Repeatedly rewrite using `[key, ← Finset.mul_sum, orth]`. Simplify using the standard rewrite rules.
-/
theorem strN_fibMat_conj {n g : ℕ} (a a' : Matrix (Fin g) (Fin g) ℂ) (h : a' * a = 1)
    (K : Ext (n + n + g) →L[ℂ] Ext (n + n + g)) :
    strN (m := n + n) (extMap (fibMat n a) ∘L K ∘L extMap (fibMat n a')) = strN (m := n + n) K := by
  have haa : a * a' = 1 := mul_eq_one_comm.mp h
  have hid : extMap (fibMat n a') ∘L extMap (fibMat n a) = ContinuousLinearMap.id ℂ (Ext (n + n + g)) := by
    rw [GlobalTheory.T.extMap_comp_extMap, fibMat_mul, haa, fibMat_one, GlobalTheory.T.extMap_one']
  have orth : ∀ J J' : Finset (Fin g), ∑ I, genProd (fibMat n a) (join ∅ J') (join ∅ I) *
      genProd (fibMat n a') (join ∅ I) (join ∅ J) = if J' = J then 1 else 0 := by
    intro J J'
    have h1 := congrArg (fun f : Ext (n + n + g) →L[ℂ] Ext (n + n + g) =>
      f (Pi.single (join ∅ J') 1) (join ∅ J)) hid
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h1
    rw [extMap_fibMat_join, extMap_single] at h1
    rw [h1, Pi.single_apply]
    by_cases hJ : J' = J
    · subst hJ; simp
    · rw [if_neg hJ, if_neg]
      intro he
      have := join_injective (m := n + n) (g := g) (a₁ := (∅, J)) (a₂ := (∅, J')) he
      exact hJ (Prod.ext_iff.mp this).2.symm
  have hcard : ∀ I J : Finset (Fin g), genProd (fibMat n a') (join ∅ I) (join ∅ J) ≠ 0 →
      J.card = I.card := by
    intro I J hne
    have := genProd_card _ _ _ hne
    rwa [card_join_empty, card_join_empty] at this
  funext S
  simp only [strN, ContinuousLinearMap.comp_apply]
  simp_rw [extMap_fibMat_join a, extMap_single, clm_apply_fib a']
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => enter [2, J']; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun J _ => ?_)
  have key : ∀ J' I : Finset (Fin g),
      (-1) ^ I.card * (I.card : ℂ) * (genProd (fibMat n a') (join ∅ I) (join ∅ J) *
        K (Pi.single (join ∅ J) 1) (join S J') * genProd (fibMat n a) (join ∅ J') (join ∅ I)) =
      ((-1) ^ J.card * (J.card : ℂ) * K (Pi.single (join ∅ J) 1) (join S J')) *
        (genProd (fibMat n a) (join ∅ J') (join ∅ I) * genProd (fibMat n a') (join ∅ I) (join ∅ J)) := by
    intro J' I
    by_cases hc : genProd (fibMat n a') (join ∅ I) (join ∅ J) = 0
    · simp [hc]
    · rw [hcard I J hc]; ring
  simp_rw [key, ← Finset.mul_sum, orth]
  simp

end GlobalTheory.TorsionForm.StrNConj

/- English proof (translation)
Introduce `a a' h K` and use `GlobalTheory.TorsionForm.StrNConj.strN_fibMat_conj a a' h K`.
-/
theorem GlobalTheory.TorsionForm.strN_frame_conj : ∀ {n g : ℕ} (a a' : Matrix (Fin g) (Fin g) ℂ), a' * a = 1 →
    ∀ K : Ext (n + n + g) →L[ℂ] Ext (n + n + g),
      strN (m := n + n) (extMap (fibMat n a) ∘L K ∘L extMap (fibMat n a')) = strN (m := n + n) K :=
  fun a a' h K => GlobalTheory.TorsionForm.StrNConj.strN_fibMat_conj a a' h K
