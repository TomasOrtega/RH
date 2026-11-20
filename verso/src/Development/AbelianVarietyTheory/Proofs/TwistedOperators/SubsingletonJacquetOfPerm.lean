import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory

namespace GlobalTheory.SmGL.CuspMax

/- English proof (translation)
Establish `h1 : twKer π N 1 = ⊤` using `Submodule.Quotient.subsingleton_iff.1 hN`. Use `Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun v _ => ?_)` and prove the remaining obligations. Establish `h2 : twKer π N 1 ≤ (twKer π N' 1).comap (π g)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨u, w, rfl⟩`.

Use `Submodule.subset_span ⟨⟨_, h u u.2⟩, π g w, ?_⟩` and prove the remaining obligations. Simplify using `[← Module.End.mul_apply, ← map_mul]`. Establish `h3 : π g⁻¹ v ∈ twKer π N 1` using `h1 ▸ Submodule.mem_top`. Establish `h4 : π g (π g⁻¹ v) ∈ twKer π N' 1` using `h2 h3`. Simplify `h4` using `[← Module.End.mul_apply, ← map_mul]`.
-/
theorem subsingleton_jacquet_of_conj {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) {N N' : Subgroup G} (g : G) (h : ∀ u ∈ N, g * u * g⁻¹ ∈ N')
    (hN : Subsingleton (Jacquet π N)) : Subsingleton (Jacquet π N') := by
  have h1 : twKer π N 1 = ⊤ := Submodule.Quotient.subsingleton_iff.1 hN
  refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun v _ => ?_)
  have h2 : twKer π N 1 ≤ (twKer π N' 1).comap (π g) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, w, rfl⟩
    refine Submodule.subset_span ⟨⟨_, h u u.2⟩, π g w, ?_⟩
    simp [← Module.End.mul_apply, ← map_mul]
  have h3 : π g⁻¹ v ∈ twKer π N 1 := h1 ▸ Submodule.mem_top
  have h4 : π g (π g⁻¹ v) ∈ twKer π N' 1 := h2 h3
  simpa [← Module.End.mul_apply, ← map_mul] using h4

variable {R : Type} [CommRing R] {α β n : Type} {m : α → Type} {m' : β → Type}
  [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype β] [LinearOrder β] [∀ a, Fintype (m' a)] [∀ a, DecidableEq (m' a)]
  [Fintype n] [DecidableEq n]

/- English proof (translation)
Rewrite using `[mem_unipRad]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩ i j hij`. Break down `(not_lt.1 hij).lt_or_eq with h | h` into its components or cases. Rewrite using `[mem_parab.1 h1 i j h, Matrix.one_apply_ne]`.

Introduce and unpack `rfl`. Conclude with `lt_irrefl _ h`. Take `⟨⟨a, i⟩, rfl⟩` from `e.surjective i`. Take `⟨⟨b, j⟩, rfl⟩` from `e.surjective j`. Take `rfl : b = a` from `by simpa using h`.

Rewrite using `[h2]`. Simplify using `[Matrix.one_apply]`. Introduce `h`. Use `⟨mem_parab.2 fun i j hij => ?_, fun a i j => ?_⟩` and prove the remaining obligations. Rewrite using `[h i j hij.not_gt, Matrix.one_apply_ne]`.

Introduce and unpack `rfl`. Conclude with `lt_irrefl _ hij`. Rewrite using `[h _ _ (by simp)]`. Simplify using `[Matrix.one_apply]`.
-/
theorem mem_unipRad_iff_entries {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ unipRad R e ↔ ∀ i j, ¬ blk e i < blk e j → (g : Matrix n n R) i j = (1 : Matrix n n R) i j := by
  rw [mem_unipRad]
  constructor
  · rintro ⟨h1, h2⟩ i j hij
    rcases (not_lt.1 hij).lt_or_eq with h | h
    · rw [mem_parab.1 h1 i j h, Matrix.one_apply_ne]
      rintro rfl
      exact lt_irrefl _ h
    · obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
      obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
      obtain rfl : b = a := by simpa using h
      rw [h2]
      simp [Matrix.one_apply]
  · intro h
    refine ⟨mem_parab.2 fun i j hij => ?_, fun a i j => ?_⟩
    · rw [h i j hij.not_gt, Matrix.one_apply_ne]
      rintro rfl
      exact lt_irrefl _ hij
    · rw [h _ _ (by simp)]
      simp [Matrix.one_apply]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hc`. Use `h ((Subgroup.eq_bot_iff_forall _).2 fun u hu => ?_)` and prove the remaining obligations. Use extensionality with `i j`.

Conclude with `mem_unipRad_iff_entries.1 hu i j fun hij => hc ⟨i, j, hij⟩`. Introduce and unpack `⟨i, j, hij⟩ hb`. Establish `hne : i ≠ j`. Introduce and unpack `rfl`. Conclude with `lt_irrefl _ hij`.

Set `u : GL n R` to `⟨Matrix.transvection i j 1, Matrix.transvection i j (-1), by rw [Matrix.transvection_mul_transvection_same _ _ hne]; simp, by rw [Matrix.transvection_mul_transvection_same _ _ hne]; simp⟩`. Establish `hu : u ∈ unipRad R e` using `mem_unipRad_iff_entries.2 fun a b hab => by show Matrix.transvection i j (1 : R) a b = _`. Rewrite using `[Matrix.transvection, Matrix.add_apply, Matrix.single_apply_of_ne, add_zero]`. Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `hab hij`.

Rewrite `hu` using `[hb, Subgroup.mem_bot]`. Establish `: Matrix.transvection i j (1 : R) i j = (1 : Matrix n n R) i j` using `congrArg (fun g : GL n R => (g : Matrix n n R) i j) hu`. Simplify using `[Matrix.transvection] at this`.
-/
theorem unipRad_ne_bot_iff [Nontrivial R] {e : (Σ a, m a) ≃ n} :
    unipRad R e ≠ ⊥ ↔ ∃ i j, blk e i < blk e j := by
  constructor
  · intro h
    by_contra hc
    refine h ((Subgroup.eq_bot_iff_forall _).2 fun u hu => ?_)
    ext i j
    exact mem_unipRad_iff_entries.1 hu i j fun hij => hc ⟨i, j, hij⟩
  · rintro ⟨i, j, hij⟩ hb
    have hne : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hij
    let u : GL n R := ⟨Matrix.transvection i j 1, Matrix.transvection i j (-1),
      by rw [Matrix.transvection_mul_transvection_same _ _ hne]; simp,
      by rw [Matrix.transvection_mul_transvection_same _ _ hne]; simp⟩
    have hu : u ∈ unipRad R e := mem_unipRad_iff_entries.2 fun a b hab => by
      show Matrix.transvection i j (1 : R) a b = _
      rw [Matrix.transvection, Matrix.add_apply, Matrix.single_apply_of_ne, add_zero]
      rintro ⟨rfl, rfl⟩
      exact hab hij
    rw [hb, Subgroup.mem_bot] at hu
    have : Matrix.transvection i j (1 : R) i j = (1 : Matrix n n R) i j :=
      congrArg (fun g : GL n R => (g : Matrix n n R) i j) hu
    simp [Matrix.transvection] at this

/- English proof (translation)
Set `g : GL n R` to `⟨σ.toPEquiv.toMatrix, σ.symm.toPEquiv.toMatrix, by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp, by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp⟩`. Use `subsingleton_jacquet_of_conj π g (fun u hu => ?_) hN` and prove the remaining obligations. Use `mem_unipRad_iff_entries.2 fun i j hij => ?_` and prove the remaining obligations. Use `show (σ.toPEquiv.toMatrix * (u : Matrix n n R) * σ.symm.toPEquiv.toMatrix : Matrix n n R) i j = _`. Rewrite using `[PEquiv.mul_toMatrix_toPEquiv, PEquiv.toMatrix_toPEquiv_mul]`.

Simplify using `only [Matrix.submatrix_apply, id, Equiv.symm_symm]`. Rewrite using `[mem_unipRad_iff_entries.1 hu _ _ fun hh => hij (h i j hh)]`. Simplify using `[Matrix.one_apply]`.
-/
theorem subsingleton_jacquet_of_perm {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL n R) V) {e : (Σ a, m a) ≃ n} {e' : (Σ a, m' a) ≃ n} (σ : Equiv.Perm n)
    (h : ∀ i j, blk e (σ i) < blk e (σ j) → blk e' i < blk e' j)
    (hN : Subsingleton (Jacquet π (unipRad R e))) : Subsingleton (Jacquet π (unipRad R e')) := by
  let g : GL n R := ⟨σ.toPEquiv.toMatrix, σ.symm.toPEquiv.toMatrix,
    by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp,
    by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp⟩
  refine subsingleton_jacquet_of_conj π g (fun u hu => ?_) hN
  refine mem_unipRad_iff_entries.2 fun i j hij => ?_
  show (σ.toPEquiv.toMatrix * (u : Matrix n n R) * σ.symm.toPEquiv.toMatrix : Matrix n n R) i j = _
  rw [PEquiv.mul_toMatrix_toPEquiv, PEquiv.toMatrix_toPEquiv_mul]
  simp only [Matrix.submatrix_apply, id, Equiv.symm_symm]
  rw [mem_unipRad_iff_entries.1 hu _ _ fun hh => hij (h i j hh)]
  simp [Matrix.one_apply]

/- English proof (translation)
Use `and_congr_right fun _ => ⟨fun H r t h hr ht => ?_, fun H s d e he => ?_⟩` and prove the remaining obligations. Set `f : Fin N → Fin 2` to `fun i => if blk (two (stdSum h)) i then 1 else 0`. Set `e : (Σ a : Fin 2, Fin (Fintype.card {i // f i = a})) ≃ Fin N` to `(Equiv.sigmaCongrRight fun a => (Fintype.equivFin {i // f i = a}).symm).trans (Equiv.sigmaFiberEquiv f)`. Establish `hb : ∀ i, blk e i = f i` using `fun i => rfl`. Establish `hlt : ∀ i j, blk e i < blk e j ↔ blk (two (stdSum h)) i < blk (two (stdSum h)) j`.

Introduce `i j`. Rewrite using `[hb, hb]`. Simplify using `only [f]`. Apply the tactic sequence `cases blk (two (stdSum h)) i <;> cases blk (two (stdSum h)) j <;> decide`. Use `subsingleton_jacquet_of_perm π (e := e) 1 (fun i j hij => (hlt i j).1 hij) (H 2 _ e (unipRad_ne_bot_iff.2 ⟨two (stdSum h) ⟨false, ⟨0, hr⟩⟩, two (stdSum h) ⟨true, ⟨0, ht⟩⟩, (hlt _ _).2 ?_⟩))` and prove the remaining obligations.

Rewrite using `[blk_apply, blk_apply]`. Evaluate the decidable proposition. Take `⟨i₀, j₀, hij⟩` from `unipRad_ne_bot_iff.1 he`. Set `p : Fin N → Prop` to `fun i => blk e i ≤ blk e i₀`. Establish `hsum : Fintype.card {i // p i} + Fintype.card {i // ¬ p i} = N`.

Rewrite using `[← Fintype.card_sum, Fintype.card_congr (Equiv.sumCompl p), Fintype.card_fin]`. Set `τ : Fin (Fintype.card {i // p i}) ⊕ Fin (Fintype.card {i // ¬ p i}) ≃ Fin N` to `(Equiv.sumCongr (Fintype.equivFin _).symm (Fintype.equivFin _).symm).trans (Equiv.sumCompl p)`. Use `subsingleton_jacquet_of_perm π (τ.symm.trans (stdSum hsum)) (fun i j hh => ?_) (H _ _ hsum (Fintype.card_pos_iff.2 ⟨⟨i₀, le_rfl⟩⟩) (Fintype.card_pos_iff.2 ⟨⟨j₀, hij.not_ge⟩⟩))` and prove the remaining obligations. Take `⟨i, rfl⟩` from `τ.surjective i`. Take `⟨j, rfl⟩` from `τ.surjective j`.

Simplify using `only [Equiv.trans_apply, Equiv.symm_apply_apply] at hh`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j`. Rewrite `hh` using `[← two_false, ← two_false, blk_apply, blk_apply]`. Conclude with `absurd hh (by decide)`. Establish `h1 : p (τ (.inl i))` using `((Fintype.equivFin {i // p i}).symm i).2`.

Establish `h2 : ¬ p (τ (.inr j))` using `((Fintype.equivFin {i // ¬ p i}).symm j).2`. Conclude with `lt_of_le_of_lt h1 (not_le.1 h2)`. Rewrite `hh` using `[← two_false, ← two_true, blk_apply, blk_apply]`. Conclude with `absurd hh (by decide)`. Rewrite `hh` using `[← two_true, ← two_true, blk_apply, blk_apply]`.

Conclude with `absurd hh (by decide)`.
-/
theorem isCuspidal_iff_maximal (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) :
    IsCuspidal π ↔ IsSmooth π ∧ ∀ (r t : ℕ) (h : r + t = N), 0 < r → 0 < t →
      Subsingleton (Jacquet π (unipRad k (two (stdSum h)))) := by
  refine and_congr_right fun _ => ⟨fun H r t h hr ht => ?_, fun H s d e he => ?_⟩
  · let f : Fin N → Fin 2 := fun i => if blk (two (stdSum h)) i then 1 else 0
    let e : (Σ a : Fin 2, Fin (Fintype.card {i // f i = a})) ≃ Fin N :=
      (Equiv.sigmaCongrRight fun a => (Fintype.equivFin {i // f i = a}).symm).trans
        (Equiv.sigmaFiberEquiv f)
    have hb : ∀ i, blk e i = f i := fun i => rfl
    have hlt : ∀ i j, blk e i < blk e j ↔ blk (two (stdSum h)) i < blk (two (stdSum h)) j := by
      intro i j
      rw [hb, hb]
      simp only [f]
      cases blk (two (stdSum h)) i <;> cases blk (two (stdSum h)) j <;> decide
    refine subsingleton_jacquet_of_perm π (e := e) 1 (fun i j hij => (hlt i j).1 hij)
      (H 2 _ e (unipRad_ne_bot_iff.2 ⟨two (stdSum h) ⟨false, ⟨0, hr⟩⟩, two (stdSum h) ⟨true, ⟨0, ht⟩⟩,
        (hlt _ _).2 ?_⟩))
    rw [blk_apply, blk_apply]
    decide
  · obtain ⟨i₀, j₀, hij⟩ := unipRad_ne_bot_iff.1 he
    let p : Fin N → Prop := fun i => blk e i ≤ blk e i₀
    have hsum : Fintype.card {i // p i} + Fintype.card {i // ¬ p i} = N := by
      rw [← Fintype.card_sum, Fintype.card_congr (Equiv.sumCompl p), Fintype.card_fin]
    let τ : Fin (Fintype.card {i // p i}) ⊕ Fin (Fintype.card {i // ¬ p i}) ≃ Fin N :=
      (Equiv.sumCongr (Fintype.equivFin _).symm (Fintype.equivFin _).symm).trans (Equiv.sumCompl p)
    refine subsingleton_jacquet_of_perm π (τ.symm.trans (stdSum hsum)) (fun i j hh => ?_)
      (H _ _ hsum (Fintype.card_pos_iff.2 ⟨⟨i₀, le_rfl⟩⟩) (Fintype.card_pos_iff.2 ⟨⟨j₀, hij.not_ge⟩⟩))
    obtain ⟨i, rfl⟩ := τ.surjective i
    obtain ⟨j, rfl⟩ := τ.surjective j
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply] at hh
    rcases i with i | i <;> rcases j with j | j
    · rw [← two_false, ← two_false, blk_apply, blk_apply] at hh
      exact absurd hh (by decide)
    · have h1 : p (τ (.inl i)) := ((Fintype.equivFin {i // p i}).symm i).2
      have h2 : ¬ p (τ (.inr j)) := ((Fintype.equivFin {i // ¬ p i}).symm j).2
      exact lt_of_le_of_lt h1 (not_le.1 h2)
    · rw [← two_false, ← two_true, blk_apply, blk_apply] at hh
      exact absurd hh (by decide)
    · rw [← two_true, ← two_true, blk_apply, blk_apply] at hh
      exact absurd hh (by decide)

end GlobalTheory.SmGL.CuspMax
