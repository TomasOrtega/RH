import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
namespace FunctorialResolution.EmbeddedResolution

namespace MonomialCenter

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.
-/
private theorem sort_image_of_strictMono {α β : Type*} [LinearOrder α] [LinearOrder β]
    [DecidableEq β] (f : α → β) (hf : StrictMono f) (s : Finset α) :
    (s.image f).sort (· ≤ ·) = (s.sort (· ≤ ·)).map f := by
  have hlt' : List.Pairwise (· < ·) ((s.image f).sort (· ≤ ·)) :=
    (Finset.sortedLT_sort (s.image f)).pairwise
  have hmap : List.Pairwise (· < ·) ((s.sort (· ≤ ·)).map f) :=
    (Finset.sortedLT_sort s).pairwise.map f (fun _ _ hab => hf hab)
  refine List.Pairwise.eq_of_mem_iff hlt' hmap ?_
  intro b
  simp [Finset.mem_sort]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem sortedIndices_image_of_strictMono {n n' : ℕ} [DecidableEq (Fin n')]
    (φ : Fin n → Fin n') (hφ : StrictMono φ) (J : Finset (Fin n)) :
    sortedIndices (J.image φ) = (J.sort (· ≤ ·)).map (fun j => ((φ j : Fin n') : ℕ)) := by
  rw [sortedIndices_eq_map_sort, sort_image_of_strictMono φ hφ J, List.map_map]
  rfl

/- English proof (translation)
Proceed by induction. Treat this case separately. Split into cases according to the possible forms of the given data. Treat this case separately. Simplify using the standard rewrite rules.

Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately. Split into cases according to the possible forms of the given data. Treat this case separately.

Simplify using the standard rewrite rules. Treat this case separately. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Prove the first alternative. Prove the second alternative. Assume the hypotheses and unpack their components. Prove the first alternative. Prove the second alternative.

A detailed English derivation is pending.
-/
theorem lex_map_iff_of_strictMono {α β : Type*} [LinearOrder α] [LinearOrder β]
    (f : α → β) (hf : StrictMono f) (l l' : List α) :
    List.Lex (· < ·) (l.map f) (l'.map f) ↔ List.Lex (· < ·) l l' := by
  induction l generalizing l' with
  | nil =>
    cases l' with
    | nil =>
      simp only [List.map_nil]
      exact iff_of_false (by rintro ⟨⟩) (by rintro ⟨⟩)
    | cons b t =>
      simp only [List.map_nil, List.map_cons]
      exact iff_of_true List.Lex.nil List.Lex.nil
  | cons a s ih =>
    cases l' with
    | nil =>
      simp only [List.map_nil, List.map_cons]
      exact iff_of_false (by rintro ⟨⟩) (by rintro ⟨⟩)
    | cons b t =>
      simp only [List.map_cons, List.cons_lex_cons_iff]
      constructor
      · rintro (h | ⟨h, h2⟩)
        · exact Or.inl (hf.lt_iff_lt.mp h)
        · exact Or.inr ⟨hf.injective h, (ih t).mp h2⟩
      · rintro (h | ⟨rfl, h2⟩)
        · exact Or.inl (hf h)
        · exact Or.inr ⟨rfl, (ih t).mpr h2⟩

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem lex_sortedIndices_image_iff {n n' : ℕ} [DecidableEq (Fin n')]
    (φ : Fin n → Fin n') (hφ : StrictMono φ) (J J' : Finset (Fin n)) :
    List.Lex (· < ·) (sortedIndices (J.image φ)) (sortedIndices (J'.image φ)) ↔
      List.Lex (· < ·) (sortedIndices J) (sortedIndices J') := by
  have hg : StrictMono (fun j : Fin n => ((φ j : Fin n') : ℕ)) :=
    fun a b h => Fin.val_strictMono (hφ h)
  have h1 := lex_map_iff_of_strictMono _ hg (J.sort (· ≤ ·)) (J'.sort (· ≤ ·))
  have h2 := lex_map_iff_of_strictMono (Fin.val : Fin n → ℕ) Fin.val_strictMono
    (J.sort (· ≤ ·)) (J'.sort (· ≤ ·))
  rw [sortedIndices_image_of_strictMono φ hφ J, sortedIndices_image_of_strictMono φ hφ J',
    sortedIndices_eq_map_sort, sortedIndices_eq_map_sort]
  exact h1.trans h2.symm

def reversedIndex (n : ℕ) (j : Fin n) : ℕ := n - 1 - (j : ℕ)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.
-/
theorem reversedIndex_lt_reversedIndex_iff {n : ℕ} (j j' : Fin n) :
    reversedIndex n j < reversedIndex n j' ↔ j' < j := by
  have hj := j.isLt
  have hj' := j'.isLt
  simp only [reversedIndex, Fin.lt_def]
  omega

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem reversedIndex_injective {n : ℕ} : Function.Injective (reversedIndex n) := by
  intro a b h
  have ha := a.isLt
  have hb := b.isLt
  have h' : n - 1 - (a : ℕ) = n - 1 - (b : ℕ) := h
  exact Fin.val_injective (by omega)

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem binaryEncode_eq_sum_image {n : ℕ} (J : Finset (Fin n)) :
    _root_.FunctorialResolution.EmbeddedResolution.binaryEncode J = ∑ e ∈ J.image (reversedIndex n), 2 ^ e := by
  have hinj : ∀ a ∈ J, ∀ b ∈ J, reversedIndex n a = reversedIndex n b → a = b :=
    fun a _ b _ h => reversedIndex_injective h
  rw [Finset.sum_image hinj]
  rfl

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem binaryEncode_lt_iff {n : ℕ} (J J' : Finset (Fin n)) :
    _root_.FunctorialResolution.EmbeddedResolution.binaryEncode J' < _root_.FunctorialResolution.EmbeddedResolution.binaryEncode J ↔
      (∃ a ∈ J, a ∉ J' ∧ ∀ b ∈ J', b ∉ J → a < b) := by
  simp only [binaryEncode_eq_sum_image]
  rw [(Finset.geomSum_lt_geomSum_iff_toColex_lt_toColex (le_refl 2)).trans
    Finset.Colex.toColex_lt_toColex_iff_exists_forall_lt]
  constructor
  · rintro ⟨e, he, he', hmax⟩
    obtain ⟨a, haJ, rfl⟩ := Finset.mem_image.mp he
    refine ⟨a, haJ, ?_, ?_⟩
    · intro haJ'
      exact he' (Finset.mem_image_of_mem _ haJ')
    · intro b hb hbJ
      have hb1 : reversedIndex n b ∈ J'.image (reversedIndex n) := Finset.mem_image_of_mem _ hb
      have hb2 : reversedIndex n b ∉ J.image (reversedIndex n) := by
        intro hmem
        obtain ⟨c, hc, hceq⟩ := Finset.mem_image.mp hmem
        have hcb : c = b := reversedIndex_injective hceq
        rw [hcb] at hc
        exact hbJ hc
      exact (reversedIndex_lt_reversedIndex_iff b a).mp (hmax _ hb1 hb2)
  · rintro ⟨a, haJ, haJ', hmin⟩
    refine ⟨reversedIndex n a, Finset.mem_image_of_mem _ haJ, ?_, ?_⟩
    · intro hmem
      obtain ⟨c, hc, hceq⟩ := Finset.mem_image.mp hmem
      have hca : c = a := reversedIndex_injective hceq
      rw [hca] at hc
      exact haJ' hc
    · rintro f hf hfnot
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hf
      have hbJ : b ∉ J := by
        intro hbJ
        exact hfnot (Finset.mem_image_of_mem _ hbJ)
      exact (reversedIndex_lt_reversedIndex_iff b a).mpr (hmin b hb hbJ)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Split into cases according to the possible forms of the given data.

Treat this case separately. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Split into cases according to the possible forms of the given data. Assume the hypotheses and unpack their components.

Simplify using the standard rewrite rules. Treat this case separately. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Split into cases according to the possible forms of the given data.

Treat this case separately. Treat this case separately. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Separate the alternatives or extract the components of the hypothesis. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Separate the alternatives or extract the components of the hypothesis. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Prove the first alternative. Substitute using the available equality. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis.

Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Rewrite the indicated hypotheses using the stated equalities.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
private theorem lex_iff_exists_min_mem {α : Type*} [LinearOrder α] :
    ∀ (L L' : List α), L.length = L'.length → List.Pairwise (· < ·) L →
      List.Pairwise (· < ·) L' →
      (List.Lex (· < ·) L L' ↔ ∃ a ∈ L, a ∉ L' ∧ ∀ b ∈ L', b ∉ L → a < b) := by
  intro L
  induction L with
  | nil =>
    intro L' hlen _ _
    cases L' with
    | nil =>
      constructor
      · intro h
        cases h
      · rintro ⟨a, ha, -⟩
        simp at ha
    | cons b t => simp at hlen
  | cons a s ih =>
    intro L' hlen hs hL'
    cases L' with
    | nil => simp at hlen
    | cons b t =>
      rw [List.pairwise_cons] at hs hL'
      have hlen' : s.length = t.length := by simpa using hlen
      rw [List.cons_lex_cons_iff]
      rcases lt_trichotomy a b with hab | hab | hab
      · constructor
        · intro _
          refine ⟨a, by simp, ?_, ?_⟩
          · intro hmem
            rcases List.mem_cons.mp hmem with h | h
            · rw [h] at hab
              exact absurd hab (lt_irrefl b)
            · exact absurd (hL'.1 a h) (not_lt.mpr hab.le)
          · intro y hy _
            rcases List.mem_cons.mp hy with h | h
            · rw [h]
              exact hab
            · exact lt_trans hab (hL'.1 y h)
        · intro _
          exact Or.inl hab
      · subst hab
        have ihst := ih t hlen' hs.2 hL'.2
        constructor
        · rintro (h | ⟨-, h⟩)
          · exact absurd h (lt_irrefl _)
          · obtain ⟨x, hxs, hxt, hmin⟩ := ihst.mp h
            refine ⟨x, List.mem_cons.mpr (Or.inr hxs), ?_, ?_⟩
            · intro hx
              rcases List.mem_cons.mp hx with heq | hx
              · rw [heq] at hxs
                exact absurd (hs.1 _ hxs) (lt_irrefl _)
              · exact hxt hx
            · intro y hy hyn
              rcases List.mem_cons.mp hy with heq | hy
              · refine absurd ?_ hyn
                rw [heq]
                simp
              · exact hmin y hy (fun hys => hyn (List.mem_cons.mpr (Or.inr hys)))
        · rintro ⟨x, hx, hxn, hmin⟩
          refine Or.inr ⟨rfl, ihst.mpr ?_⟩
          have hxs : x ∈ s := by
            rcases List.mem_cons.mp hx with h | h
            · refine absurd ?_ hxn
              rw [h]
              simp
            · exact h
          refine ⟨x, hxs, ?_, ?_⟩
          · intro hxt
            exact hxn (List.mem_cons.mpr (Or.inr hxt))
          · intro y hy hys
            refine hmin y (List.mem_cons.mpr (Or.inr hy)) ?_
            intro hy'
            rcases List.mem_cons.mp hy' with h | h
            · rw [h] at hy
              exact absurd (hL'.1 _ hy) (lt_irrefl _)
            · exact hys h
      · constructor
        · rintro (h | ⟨h, -⟩)
          · exact absurd h (not_lt.mpr hab.le)
          · rw [h] at hab
            exact absurd hab (lt_irrefl b)
        · rintro ⟨x, hx, hxn, hmin⟩
          have hbs : b ∉ a :: s := by
            intro hb
            rcases List.mem_cons.mp hb with h | h
            · rw [h] at hab
              exact absurd hab (lt_irrefl a)
            · exact absurd (hs.1 b h) (not_lt.mpr hab.le)
          have hxb : x < b := hmin b (by simp) hbs
          have hax : a ≤ x := by
            rcases List.mem_cons.mp hx with h | h
            · exact le_of_eq h.symm
            · exact le_of_lt (hs.1 x h)
          exact absurd hxb (not_lt.mpr (le_trans hab.le hax))

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem binaryEncode_lt_iff_lex_of_card_eq {n : ℕ} (J J' : Finset (Fin n)) (hcard : J.card = J'.card) :
    _root_.FunctorialResolution.EmbeddedResolution.binaryEncode J' < _root_.FunctorialResolution.EmbeddedResolution.binaryEncode J ↔
      List.Lex (· < ·) (sortedIndices J) (sortedIndices J') := by
  have hlen : (J.sort (· ≤ ·)).length = (J'.sort (· ≤ ·)).length := by
    rw [Finset.length_sort, Finset.length_sort, hcard]
  have hsJ : List.Pairwise (· < ·) (J.sort (· ≤ ·)) := (Finset.sortedLT_sort J).pairwise
  have hsJ' : List.Pairwise (· < ·) (J'.sort (· ≤ ·)) := (Finset.sortedLT_sort J').pairwise
  have hmap := lex_map_iff_of_strictMono (Fin.val : Fin n → ℕ) Fin.val_strictMono
    (J.sort (· ≤ ·)) (J'.sort (· ≤ ·))
  have hA := lex_iff_exists_min_mem (J.sort (· ≤ ·)) (J'.sort (· ≤ ·)) hlen hsJ hsJ'
  have hfin : (∃ a ∈ J.sort (· ≤ ·), a ∉ J'.sort (· ≤ ·) ∧
      ∀ b ∈ J'.sort (· ≤ ·), b ∉ J.sort (· ≤ ·) → a < b) ↔
      (∃ a ∈ J, a ∉ J' ∧ ∀ b ∈ J', b ∉ J → a < b) := by
    simp only [Finset.mem_sort]
  rw [sortedIndices_eq_map_sort, sortedIndices_eq_map_sort]
  exact (binaryEncode_lt_iff J J').trans (hfin.symm.trans (hA.symm.trans hmap.symm))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem binaryEncode_injective {n : ℕ} :
    Function.Injective (fun J : Finset (Fin n) => _root_.FunctorialResolution.EmbeddedResolution.binaryEncode J) := by
  intro J J' h
  have hJ := binaryEncode_eq_sum_image J
  have hJ' := binaryEncode_eq_sum_image J'
  have h1 : (∑ e ∈ J.image (reversedIndex n), 2 ^ e) = (∑ e ∈ J'.image (reversedIndex n), 2 ^ e) := by
    rw [← hJ, ← hJ']
    exact h
  exact Finset.image_injective reversedIndex_injective (Finset.geomSum_injective (le_refl 2) h1)

end MonomialCenter

end FunctorialResolution.EmbeddedResolution
