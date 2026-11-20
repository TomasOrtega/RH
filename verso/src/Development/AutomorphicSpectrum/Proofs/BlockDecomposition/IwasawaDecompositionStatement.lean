import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif

noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.Jp.Iw

section Ops

variable {O L ι : Type} [CommRing O] [Field L] [Algebra O L] [Fintype ι] [DecidableEq ι]

def admitted (O : Type) [CommRing O] [Algebra O L] (T : Finset ι) (k : GL ι L) : Prop :=
  (∃ κ : GL ι O, Matrix.GeneralLinearGroup.map (algebraMap O L) κ = k) ∧
    ∀ v : ι → L, (∀ i ∈ T, v i = 0) → v ᵥ* k.1 = v

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨1, map_one _⟩, fun v _ => by simp⟩`.
-/
lemma admitted.one (T : Finset ι) : admitted O T (1 : GL ι L) :=
  ⟨⟨1, map_one _⟩, fun v _ => by simp⟩

/- English proof (translation)
Take `⟨⟨κ, rfl⟩, f⟩` from `h`. Take `⟨⟨κ', rfl⟩, f'⟩` from `h'`. Use `⟨⟨κ * κ', map_mul _ _ _⟩, fun v hv => ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, ← Matrix.vecMul_vecMul, f v hv, f' v hv]`.
-/
lemma admitted.mul {T : Finset ι} {k k' : GL ι L} (h : admitted O T k) (h' : admitted O T k') : admitted O T (k * k') := by
  obtain ⟨⟨κ, rfl⟩, f⟩ := h
  obtain ⟨⟨κ', rfl⟩, f'⟩ := h'
  refine ⟨⟨κ * κ', map_mul _ _ _⟩, fun v hv => ?_⟩
  rw [Units.val_mul, ← Matrix.vecMul_vecMul, f v hv, f' v hv]

/- English proof (translation)
Set `κ : GL ι O` to `⟨transvection i j c, transvection i j (-c), by simp [transvection_mul_transvection_same, hij], by simp [transvection_mul_transvection_same, hij]⟩`. Establish `key : ∀ z : ι → L, z ᵥ* (Matrix.GeneralLinearGroup.map (algebraMap O L) κ).1 = z + Pi.single j (z i * algebraMap O L c)`. Introduce `z`. Establish `e : (Matrix.GeneralLinearGroup.map (algebraMap O L) κ).1 = 1 + Matrix.single i j (algebraMap O L c)`. Use extensionality with `a b`.

Simplify using `[κ, transvection, Matrix.one_apply, Matrix.single_apply, apply_ite (algebraMap O L)]`. Rewrite using `[e, Matrix.vecMul_add, Matrix.vecMul_one]`. Use `congr 1`. Use extensionality with `l`. Distinguish the cases in `h : l = j`.

Substitute `h` using the available equality. Simplify using `[Matrix.vecMul, dotProduct, Matrix.single_apply]`. Simplify using `[Matrix.vecMul, dotProduct, Matrix.single_apply, h, Ne.symm h]`. Conclude with `⟨_, ⟨⟨κ, rfl⟩, fun v hv => by rw [key, hv i hi]; simp⟩, key⟩`.
-/
lemma exists_transv {T : Finset ι} {i j : ι} (hi : i ∈ T) (hij : i ≠ j) (c : O) :
    ∃ k : GL ι L, admitted O T k ∧
      ∀ z : ι → L, z ᵥ* k.1 = z + Pi.single j (z i * algebraMap O L c) := by
  let κ : GL ι O := ⟨transvection i j c, transvection i j (-c),
    by simp [transvection_mul_transvection_same, hij], by simp [transvection_mul_transvection_same, hij]⟩
  have key : ∀ z : ι → L, z ᵥ* (Matrix.GeneralLinearGroup.map (algebraMap O L) κ).1 =
      z + Pi.single j (z i * algebraMap O L c) := by
    intro z
    have e : (Matrix.GeneralLinearGroup.map (algebraMap O L) κ).1 =
        1 + Matrix.single i j (algebraMap O L c) := by
      ext a b
      simp [κ, transvection, Matrix.one_apply, Matrix.single_apply, apply_ite (algebraMap O L)]
    rw [e, Matrix.vecMul_add, Matrix.vecMul_one]
    congr 1
    ext l
    by_cases h : l = j
    · subst h
      simp [Matrix.vecMul, dotProduct, Matrix.single_apply]
    · simp [Matrix.vecMul, dotProduct, Matrix.single_apply, h, Ne.symm h]
  exact ⟨_, ⟨⟨κ, rfl⟩, fun v hv => by rw [key, hv i hi]; simp⟩, key⟩

/- English proof (translation)
Distinguish the cases in `ha : a = 0`. Conclude with `Or.inr ⟨0, by simp [ha]⟩`. Distinguish the cases in `hb : b = 0`. Conclude with `Or.inl ⟨0, by simp [hb]⟩`. Break down `ValuationRing.isInteger_or_isInteger O (b / a) with ⟨c, hc⟩ | ⟨c, hc⟩` into its components or cases.

Use `Or.inl ⟨c, ?_⟩` and prove the remaining obligations. Establish `hc' : algebraMap O L c = b / a` using `hc`. Rewrite using `[hc']`. Clear the denominators using the available nonvanishing facts. Use `Or.inr ⟨c, ?_⟩` and prove the remaining obligations.

Establish `hc' : algebraMap O L c = (b / a)⁻¹` using `hc`. Rewrite using `[hc']`. Clear the denominators using the available nonvanishing facts.
-/
lemma exists_mul_or [IsDomain O] [ValuationRing O] [IsFractionRing O L] (a b : L) :
    (∃ c : O, b = algebraMap O L c * a) ∨ ∃ c : O, a = algebraMap O L c * b := by
  by_cases ha : a = 0
  · exact Or.inr ⟨0, by simp [ha]⟩
  by_cases hb : b = 0
  · exact Or.inl ⟨0, by simp [hb]⟩
  rcases ValuationRing.isInteger_or_isInteger O (b / a) with ⟨c, hc⟩ | ⟨c, hc⟩
  · refine Or.inl ⟨c, ?_⟩
    have hc' : algebraMap O L c = b / a := hc
    rw [hc']; field_simp
  · refine Or.inr ⟨c, ?_⟩
    have hc' : algebraMap O L c = (b / a)⁻¹ := hc
    rw [hc']; field_simp

/- English proof (translation)
Break down `exists_mul_or (O := O) (z j) (z p) with ⟨c, hc⟩ | ⟨c, hc⟩` into its components or cases. Take `⟨k₁, a₁, h₁⟩` from `exists_transv (O := O) (L := L) hj hjp (1 - c)`. Take `⟨k₂, a₂, h₂⟩` from `exists_transv (O := O) (L := L) hp hjp.symm (-1)`. Use `⟨k₁ * k₂, a₁.mul a₂, ?_, fun l hl hl' => ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, ← Matrix.vecMul_vecMul, h₂, h₁]`.

Simplify using `[Pi.single_apply, hjp, hjp.symm, hc]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Units.val_mul, ← Matrix.vecMul_vecMul, h₂, h₁]`. Simplify using `[Pi.single_apply, hl, hl']`. Take `⟨k, a, h⟩` from `exists_transv (O := O) (L := L) hp hjp.symm (-c)`.

Use `⟨k, a, ?_, fun l hl _ => ?_⟩` and prove the remaining obligations. Rewrite using `[h]`. Simplify using `[hc]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h]`.

Simplify using `[Pi.single_apply, hl]`.
-/
lemma exists_clear [IsDomain O] [ValuationRing O] [IsFractionRing O L] {T : Finset ι} {j p : ι}
    (hj : j ∈ T) (hp : p ∈ T) (hjp : j ≠ p) (z : ι → L) :
    ∃ k : GL ι L, admitted O T k ∧ (z ᵥ* k.1) j = 0 ∧ ∀ l, l ≠ j → l ≠ p → (z ᵥ* k.1) l = z l := by
  rcases exists_mul_or (O := O) (z j) (z p) with ⟨c, hc⟩ | ⟨c, hc⟩
  · obtain ⟨k₁, a₁, h₁⟩ := exists_transv (O := O) (L := L) hj hjp (1 - c)
    obtain ⟨k₂, a₂, h₂⟩ := exists_transv (O := O) (L := L) hp hjp.symm (-1)
    refine ⟨k₁ * k₂, a₁.mul a₂, ?_, fun l hl hl' => ?_⟩
    · rw [Units.val_mul, ← Matrix.vecMul_vecMul, h₂, h₁]
      simp [Pi.single_apply, hjp, hjp.symm, hc]
      ring
    · rw [Units.val_mul, ← Matrix.vecMul_vecMul, h₂, h₁]
      simp [Pi.single_apply, hl, hl']
  · obtain ⟨k, a, h⟩ := exists_transv (O := O) (L := L) hp hjp.symm (-c)
    refine ⟨k, a, ?_, fun l hl _ => ?_⟩
    · rw [h]
      simp [hc]
      ring
    · rw [h]
      simp [Pi.single_apply, hl]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨1, admitted.one T, by simp⟩`. Consider the case `insert a s ha ih`. Take `⟨k, hk, h⟩` from `ih ((Finset.subset_insert a s).trans hs) (fun hh => hps (Finset.mem_insert_of_mem hh))`. Establish `hap : a ≠ p` using `fun e => hps (e ▸ Finset.mem_insert_self a s)`.

Take `⟨k', hk', h0, h1⟩` from `exists_clear (O := O) (hs (Finset.mem_insert_self a s)) hp hap (z ᵥ* k.1)`. Use `⟨k * k', hk.mul hk', fun l hl => ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, ← Matrix.vecMul_vecMul]`. Break down `Finset.mem_insert.1 hl with rfl | hl` into its components or cases. Conclude with `h0`.

Rewrite using `[h1 l (fun e => ha (e ▸ hl)) (fun e => hps (e ▸ Finset.mem_insert_of_mem hl))]`. Conclude with `h l hl`.
-/
lemma exists_clear_set [IsDomain O] [ValuationRing O] [IsFractionRing O L] {T : Finset ι} {p : ι}
    (hp : p ∈ T) (z : ι → L) (s : Finset ι) (hs : s ⊆ T) (hps : p ∉ s) :
    ∃ k : GL ι L, admitted O T k ∧ ∀ l ∈ s, (z ᵥ* k.1) l = 0 := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, admitted.one T, by simp⟩
  | insert a s ha ih =>
    obtain ⟨k, hk, h⟩ := ih ((Finset.subset_insert a s).trans hs)
      (fun hh => hps (Finset.mem_insert_of_mem hh))
    have hap : a ≠ p := fun e => hps (e ▸ Finset.mem_insert_self a s)
    obtain ⟨k', hk', h0, h1⟩ := exists_clear (O := O) (hs (Finset.mem_insert_self a s)) hp hap (z ᵥ* k.1)
    refine ⟨k * k', hk.mul hk', fun l hl => ?_⟩
    rw [Units.val_mul, ← Matrix.vecMul_vecMul]
    rcases Finset.mem_insert.1 hl with rfl | hl
    · exact h0
    · rw [h1 l (fun e => ha (e ▸ hl)) (fun e => hps (e ▸ Finset.mem_insert_of_mem hl))]
      exact h l hl

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact ⟨1, by simp⟩`. Consider the case `insert a S ha ih`. Take `⟨κ, h⟩` from `ih`. Establish `hpT : f a ∈ (S.image f)ᶜ`.

Simplify using `only [Finset.mem_compl, Finset.mem_image, not_exists, not_and]`. Conclude with `fun x hx e => ha (hf e ▸ hx)`. Take `⟨k, ⟨⟨κ', rfl⟩, fix⟩, hk⟩` from `exists_clear_set (O := O) hpT ((g * (Matrix.GeneralLinearGroup.map (algebraMap O L) κ).1) (f a)) (((S.image f)ᶜ).erase (f a)) (Finset.erase_subset _ _) (Finset.notMem_erase _ _)`. Use `⟨κ * κ', fun i hi c hc => ?_⟩` and prove the remaining obligations. Establish `row : ∀ r, (g * (Matrix.GeneralLinearGroup.map (algebraMap O L) (κ * κ')).1) r = (g * (Matrix.GeneralLinearGroup.map (algebraMap O L) κ).1) r ᵥ* (Matrix.GeneralLinearGroup.map (algebraMap O L) κ').1`.

Introduce `r`. Rewrite using `[map_mul, Units.val_mul, ← Matrix.mul_assoc, Matrix.mul_apply_eq_vecMul]`. Establish `hcS : c ∉ S.image f` using `fun e => hc (by`. Rewrite using `[Finset.image_insert]`. Conclude with `Finset.mem_insert_of_mem e)`.

Establish `hca : c ≠ f a` using `fun e => hc (by`. Rewrite using `[Finset.image_insert, e]`. Conclude with `Finset.mem_insert_self _ _)`. Rewrite using `[row]`. Break down `Finset.mem_insert.1 hi with rfl | hi` into its components or cases.

Conclude with `hk c (Finset.mem_erase.2 ⟨hca, Finset.mem_compl.2 hcS⟩)`. Rewrite using `[fix _ (fun l hl => h i hi l (Finset.mem_compl.1 hl))]`. Conclude with `h i hi c hcS`.
-/
lemma exists_rows [IsDomain O] [ValuationRing O] [IsFractionRing O L] {ρ : Type} [DecidableEq ρ]
    (f : ρ → ι) (hf : Function.Injective f) (g : Matrix ι ι L) (S : Finset ρ) :
    ∃ κ : GL ι O, ∀ i ∈ S, ∀ c ∉ S.image f,
      (g * (Matrix.GeneralLinearGroup.map (algebraMap O L) κ).1) (f i) c = 0 := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | insert a S ha ih =>
    obtain ⟨κ, h⟩ := ih
    have hpT : f a ∈ (S.image f)ᶜ := by
      simp only [Finset.mem_compl, Finset.mem_image, not_exists, not_and]
      exact fun x hx e => ha (hf e ▸ hx)
    obtain ⟨k, ⟨⟨κ', rfl⟩, fix⟩, hk⟩ := exists_clear_set (O := O) hpT
      ((g * (Matrix.GeneralLinearGroup.map (algebraMap O L) κ).1) (f a)) (((S.image f)ᶜ).erase (f a))
      (Finset.erase_subset _ _) (Finset.notMem_erase _ _)
    refine ⟨κ * κ', fun i hi c hc => ?_⟩
    have row : ∀ r, (g * (Matrix.GeneralLinearGroup.map (algebraMap O L) (κ * κ')).1) r =
        (g * (Matrix.GeneralLinearGroup.map (algebraMap O L) κ).1) r ᵥ*
          (Matrix.GeneralLinearGroup.map (algebraMap O L) κ').1 := by
      intro r
      rw [map_mul, Units.val_mul, ← Matrix.mul_assoc, Matrix.mul_apply_eq_vecMul]
    have hcS : c ∉ S.image f := fun e => hc (by
      rw [Finset.image_insert]; exact Finset.mem_insert_of_mem e)
    have hca : c ≠ f a := fun e => hc (by
      rw [Finset.image_insert, e]; exact Finset.mem_insert_self _ _)
    rw [row]
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hk c (Finset.mem_erase.2 ⟨hca, Finset.mem_compl.2 hcS⟩)
    · rw [fix _ (fun l hl => h i hi l (Finset.mem_compl.1 hl))]
      exact h i hi c hcS

end Ops

/- English proof (translation)
Introduce `O L _ _ _ _ _ _ n g`. Take `⟨κ, h⟩` from `exists_rows (O := O) (L := L) (ι := Ix n) (Sum.inr : Fin n → Ix n) Sum.inr_injective g.1 Finset.univ`. Use `set k : GL (Ix n) L := inL κ with hk`. Use `set G : Matrix (Ix n) (Ix n) L := (g * k).1 with hG`. Establish `hC : G.toBlocks₂₁ = 0`.

Use extensionality with `i j`. Conclude with `h i (Finset.mem_univ _) (Sum.inl j) (by simp)`. Establish `hGb : G = fromBlocks G.toBlocks₁₁ G.toBlocks₁₂ 0 G.toBlocks₂₂`. Rewrite using `[← hC, Matrix.fromBlocks_toBlocks]`. Establish `hdet : G.toBlocks₁₁.det * G.toBlocks₂₂.det ≠ 0`.

Rewrite using `[← Matrix.det_fromBlocks_zero₂₁ G.toBlocks₁₁ G.toBlocks₁₂ G.toBlocks₂₂, ← hGb]`. Conclude with `(Matrix.isUnits_det_units (g * k)).ne_zero`. Use `⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ (left_ne_zero_of_mul hdet), Matrix.GeneralLinearGroup.mkOfDetNeZero _ (right_ne_zero_of_mul hdet), G.toBlocks₁₂, κ⁻¹, ?_⟩` and prove the remaining obligations. Establish `hp : pM (Matrix.GeneralLinearGroup.mkOfDetNeZero _ (left_ne_zero_of_mul hdet)) (Matrix.GeneralLinearGroup.mkOfDetNeZero _ (right_ne_zero_of_mul hdet)) G.toBlocks₁₂ = g * k`. Apply `Units.ext` to reduce the goal to its premises.

Conclude with `hGb.symm`. Rewrite using `[hp, map_inv, ← hk, mul_inv_cancel_right]`.
-/
theorem jpIw : JpIw := by
  intro O L _ _ _ _ _ _ n g
  obtain ⟨κ, h⟩ := exists_rows (O := O) (L := L) (ι := Ix n) (Sum.inr : Fin n → Ix n)
    Sum.inr_injective g.1 Finset.univ
  set k : GL (Ix n) L := inL κ with hk
  set G : Matrix (Ix n) (Ix n) L := (g * k).1 with hG
  have hC : G.toBlocks₂₁ = 0 := by
    ext i j
    exact h i (Finset.mem_univ _) (Sum.inl j) (by simp)
  have hGb : G = fromBlocks G.toBlocks₁₁ G.toBlocks₁₂ 0 G.toBlocks₂₂ := by
    rw [← hC, Matrix.fromBlocks_toBlocks]
  have hdet : G.toBlocks₁₁.det * G.toBlocks₂₂.det ≠ 0 := by
    rw [← Matrix.det_fromBlocks_zero₂₁ G.toBlocks₁₁ G.toBlocks₁₂ G.toBlocks₂₂, ← hGb]
    exact (Matrix.isUnits_det_units (g * k)).ne_zero
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ (left_ne_zero_of_mul hdet),
    Matrix.GeneralLinearGroup.mkOfDetNeZero _ (right_ne_zero_of_mul hdet), G.toBlocks₁₂, κ⁻¹, ?_⟩
  have hp : pM (Matrix.GeneralLinearGroup.mkOfDetNeZero _ (left_ne_zero_of_mul hdet))
      (Matrix.GeneralLinearGroup.mkOfDetNeZero _ (right_ne_zero_of_mul hdet)) G.toBlocks₁₂ = g * k := by
    apply Units.ext
    exact hGb.symm
  rw [hp, map_inv, ← hk, mul_inv_cancel_right]

end GlobalTheory.CompanionTheory.Jp.Iw

end
