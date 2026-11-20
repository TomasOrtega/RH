import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

open Formalism.L2.NTheta

namespace GlobalTheory.ArchRec.ParPair

section HC

variable {R : Ranks} (h : HCParam R)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

A detailed English derivation is pending.
-/
theorem lamAt_tail (n : ℕ) (c : Fin R.m) (hn : n + 1 = R.k + c) : lamAt h n = -h.b c := by
  have hk := R.m_add_three_le_k
  have hc := c.2
  unfold lamAt
  rw [dif_neg (by omega), dif_pos (by omega)]
  congr 2
  exact Fin.ext (by simp only; omega)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem lamAt_head (n : Fin (R.k - 1)) : lamAt h n = h.v n := by
  unfold lamAt
  rw [dif_pos n.2]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Move the embeddings inside the algebraic operations.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lamAt_lt_of_lt {a b : ℕ} (hab : a < b) (hb : b < R.r) : lamAt h b < lamAt h a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hab
  have := lamAt_add_add_le h (d + 1) a (by omega)
  rw [← add_assoc] at this
  have h0 : (0 : ℚ) ≤ d := by positivity
  push_cast at this
  linarith

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
theorem lamAt_le_of_le {a b : ℕ} (hab : a ≤ b) (hb : b < R.r) : lamAt h b ≤ lamAt h a := by
  rcases hab.eq_or_lt with rfl | hab
  · exact le_rfl
  · exact (lamAt_lt_of_lt h hab hb).le

variable (i : Fin R.m)

def al : List ℚ := (List.range (R.k + i)).map fun n => lamAt h n + h.e i

def de : List ℚ := (List.range (R.m - (i + 1))).map fun c => lamAt h (R.k + i + c) + h.e i

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem mem_al {x : ℚ} : x ∈ al h i ↔ ∃ n < R.k + i, lamAt h n + h.e i = x := by
  simp only [al, List.mem_map, List.mem_range]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem mem_de {x : ℚ} : x ∈ de h i ↔ ∃ c < R.m - (i + 1), lamAt h (R.k + i + c) + h.e i = x := by
  simp only [de, List.mem_map, List.mem_range]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem length_al : (al h i).length = R.k + i := by simp [al]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem length_de : (de h i).length = R.m - (i + 1) := by simp [de]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem le_of_mem_al {x : ℚ} (hx : x ∈ al h i) : h.e i - h.b i ≤ x := by
  obtain ⟨n, hn, rfl⟩ := (mem_al h i).1 hx
  have hk := R.m_add_three_le_k
  have hi := i.2
  have h1 := lamAt_tail h (R.k + i - 1) i (by omega)
  have h2 := lamAt_le_of_le h (a := n) (b := R.k + i - 1) (by omega) (by unfold Ranks.r; omega)
  linarith

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem le_of_mem_de {x : ℚ} (hx : x ∈ de h i) :
    ∃ hi : i.1 + 1 < R.m, x ≤ h.e i - h.b ⟨i.1 + 1, hi⟩ := by
  obtain ⟨c, hc, rfl⟩ := (mem_de h i).1 hx
  have hk := R.m_add_three_le_k
  have hi : i.1 + 1 < R.m := by omega
  refine ⟨hi, ?_⟩
  have h1 := lamAt_tail h (R.k + i) ⟨i.1 + 1, hi⟩ (by simp only; omega)
  have h2 := lamAt_le_of_le h (a := R.k + i) (b := R.k + i + c) (by omega) (by unfold Ranks.r; omega)
  linarith

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem al_far {x : ℚ} (hx : x ∈ al h i) : ((R.t : ℚ) + 3) / 2 ≤ x :=
  (h.gap_be i).trans (le_of_mem_al h i hx)

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem de_far {x : ℚ} (hx : x ∈ de h i) : ((R.t : ℚ) + 3) / 2 ≤ -x := by
  obtain ⟨hi, hx⟩ := le_of_mem_de h i hx
  have := h.gap_eb i hi
  linarith

/- English proof (translation)
Simplify using the standard rewrite rules. Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
theorem far {x : ℚ} (hx : x ∈ al h i ++ [] ++ [] ++ de h i) : ((R.t : ℚ) + 3) / 2 ≤ |x| := by
  simp only [List.append_nil, List.mem_append] at hx
  rcases hx with hx | hx
  · exact (al_far h i hx).trans (le_abs_self x)
  · exact (de_far h i hx).trans (neg_le_abs x)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem al_pairwise : (al h i).Pairwise (· > ·) := by
  have hk := R.m_add_three_le_k
  have hi := i.2
  unfold al
  rw [List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ List.pairwise_lt_range
  intro a b _ hb hab
  have := lamAt_lt_of_lt h hab (by have := List.mem_range.1 hb; unfold Ranks.r; omega)
  show lamAt h b + h.e i < lamAt h a + h.e i
  linarith

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem de_pairwise : (de h i).Pairwise (· > ·) := by
  have hk := R.m_add_three_le_k
  unfold de
  rw [List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ List.pairwise_lt_range
  intro a b _ hb hab
  have := lamAt_lt_of_lt h (a := R.k + i + a) (b := R.k + i + b) (by omega)
    (by have := List.mem_range.1 hb; unfold Ranks.r; omega)
  show lamAt h (R.k + i + b) + h.e i < lamAt h (R.k + i + a) + h.e i
  linarith

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Extract witnesses or component facts from the available result. Apply the first step, then apply the next step to every resulting obligation. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem hypA : HypA R.t (al h i) [] [] (de h i) := by
  have hk := R.m_add_three_le_k
  have ht : (0 : ℚ) < ((R.t : ℚ) + 3) / 2 := by positivity
  have hp : ∀ x ∈ al h i, 0 < x := fun x hx => ht.trans_le (al_far h i hx)
  have hn : ∀ x ∈ de h i, x < 0 := fun x hx => neg_pos.1 (ht.trans_le (de_far h i hx))
  refine ⟨R.t_odd.pos, by rw [length_al]; omega, al_pairwise h i, List.Pairwise.nil, List.Pairwise.nil,
    de_pairwise h i, ?_, ?_, ?_, ?_, fun x hx => le_trans (by linarith) (far h i hx)⟩
  · simp only [List.append_nil]
    exact List.nodup_append.2 ⟨(al_pairwise h i).imp ne_of_gt, (de_pairwise h i).imp ne_of_gt,
      fun a ha b hb => ((hn b hb).trans (hp a ha)).ne'⟩
  · simpa using hp
  · simpa using hn
  · intro x hx
    simp only [List.append_nil, List.mem_append, mem_al, mem_de] at hx
    obtain ⟨n, rfl⟩ : ∃ n, lamAt h n + h.e i = x := by
      rcases hx with ⟨n, -, hx⟩ | ⟨n, -, hx⟩ <;> exact ⟨_, hx⟩
    obtain ⟨z, hz⟩ := lamAt_int h n
    obtain ⟨e, he⟩ := h.e_int i
    obtain ⟨s, hs⟩ := R.t_odd
    refine ⟨z + e - s - 1, ?_⟩
    rw [hz, he, hs]
    push_cast
    ring

/- English proof (translation)
Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Chain the equalities or inequalities of the calculation.

A detailed English derivation is pending.
-/
theorem num_bound {n q m N : ℕ} (hn : n ≤ N) (hq : q ≤ m) (hN : 8 * m ≤ N) :
    120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 2 * (N : ℝ) ^ 3 := by
  have h1 : (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (q : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos q with rfl | hq0
    · simp
    · rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq0) (by norm_num)
  have hn' : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hq' : 8 * (q : ℝ) ≤ N := by exact_mod_cast (by omega : 8 * q ≤ N)
  have h2 : 60 * (q : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
    have : (8 * (q : ℝ)) ^ 2 ≤ (N : ℝ) ^ 2 := by gcongr
    nlinarith [sq_nonneg (q : ℝ)]
  calc 120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 120 * (N : ℝ) * (q : ℝ) ^ 2 := by gcongr
    _ = 2 * (N : ℝ) * (60 * (q : ℝ) ^ 2) := by ring
    _ ≤ 2 * (N : ℝ) * (N : ℝ) ^ 2 := by gcongr
    _ = 2 * (N : ℝ) ^ 3 := by ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem getD_mem (l : List ℚ) {n : ℕ} (hn : n < l.length) : l.getD n 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ hn]
  exact List.getElem_mem hn

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem gapGe {g : ℚ} (hg : ∀ hi : i.1 + 1 < R.m, g ≤ h.b ⟨i.1 + 1, hi⟩ - h.b i) :
    GapGe (lamA (al h i) [] [] (de h i)) (g : ℝ) := by
  have key : ∀ (a : Fin ((al h i).length + ([] : List ℚ).length)) (b : Fin (([] : List ℚ).length + (de h i).length)),
      g ≤ lamA (al h i) [] [] (de h i) (.inl a) - lamA (al h i) [] [] (de h i) (.inr b) := by
    intro a b
    have ha := le_of_mem_al h i (getD_mem (al h i) (n := a) (by simpa using a.2))
    obtain ⟨hi, hb⟩ := le_of_mem_de h i (getD_mem (de h i) (n := b) (by simpa using b.2))
    have := hg hi
    simp only [lamA, ofBlocks, List.append_nil, List.nil_append]
    linarith
  rintro (a | a) (b | b) hab
  · exact absurd (by simp [sameBlock]) hab
  · exact le_abs.2 (Or.inl (by exact_mod_cast key a b))
  · refine le_abs.2 (Or.inr ?_)
    rw [← Rat.cast_neg, neg_sub]
    exact_mod_cast key b a
  · exact absurd (by simp [sameBlock]) hab

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Replace the relevant objects with their definitions. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Move the embeddings inside the algebraic operations. Combine the linear equalities and inequalities to obtain the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Move the embeddings inside the algebraic operations. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem hypG {N : ℕ} (hN : R.rankX' + 1 ≤ N)
    (hg : ∀ hi : i.1 + 1 < R.m, (R.t : ℚ) + 2 * (N : ℚ) ^ 3 + 1 ≤ h.b ⟨i.1 + 1, hi⟩ - h.b i) :
    HypG R.t (al h i) [] [] (de h i) := by
  have G := gapGe h i hg
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  have hi := i.2
  have ht := R.rank_add_five_le
  unfold Ranks.rankX' Ranks.r at hN
  have h1 : 1 * R.t ≤ R.m * R.t := Nat.mul_le_mul_right _ (by omega)
  have h2 : R.m * 8 ≤ R.m * R.t := Nat.mul_le_mul_left _ (by omega)
  have ht0 : (0 : ℝ) ≤ R.t := by positivity
  have hN0 : (0 : ℝ) ≤ (N : ℝ) ^ 3 := by positivity
  have hl1 := length_al h i
  have hl2 := length_de h i
  refine ⟨fun a b hab => lt_of_lt_of_le ?_ (G a b hab), ?_, fun a b hab => le_trans ?_ (G a b hab)⟩
  · have : (((al h i).length + ([] : List ℚ).length + ([] : List ℚ).length + (de h i).length + R.t : ℕ) : ℝ) ≤ N := by
      exact_mod_cast (by simp only [List.length_nil]; omega)
    have h3 := pow_le_pow_left₀ (by positivity) this 3
    refine h3.trans_lt ?_
    push_cast
    linarith
  · rintro (a | a) (b | b) hab
    · exact absurd (by simp [sameBlock]) hab
    · exact absurd b.2 (by simp)
    · exact absurd a.2 (by simp)
    · exact absurd a.2 (by simp)
  · refine (num_bound (m := R.m) (N := N) (by simp only [List.length_nil]; omega)
      ((min_le_right _ _).trans (by simp only [List.length_nil]; omega)) (by omega)).trans ?_
    push_cast
    linarith

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Substitute using the available equality.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Prove the first alternative.

Prove the second alternative. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Supply the required witnesses or components.
-/
theorem holPar_eq {p q : ℕ} (hp : p = R.k + i) (hq : q = R.m - (i + 1)) :
    holPar p q (kapW h p q) = signed (al h i ++ []) ([] ++ de h i) (-h.e i) := by
  have hk := R.m_add_three_le_k
  have hi := i.2
  have ho : Odd (p + q) := by
    rw [show p + q = R.r by unfold Ranks.r; omega]; exact odd_r R
  subst hp hq
  ext ⟨x, s⟩
  simp only [holPar, holEnt_kapW h _ _ ho, signed, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union,
    List.mem_toFinset, List.mem_map, List.append_nil, List.nil_append, mem_al, mem_de, Prod.mk.injEq]
  constructor
  · rintro ⟨a | a, rfl, rfl⟩
    · exact Or.inl ⟨_, ⟨a, a.2, rfl⟩, by simp, rfl⟩
    · exact Or.inr ⟨_, ⟨a, a.2, rfl⟩, by simp, rfl⟩
  · rintro (⟨_, ⟨n, hn, rfl⟩, rfl, rfl⟩ | ⟨_, ⟨n, hn, rfl⟩, rfl, rfl⟩)
    · exact ⟨.inl ⟨n, hn⟩, by simp, rfl⟩
    · exact ⟨.inr ⟨n, hn⟩, by simp, rfl⟩

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Consider separately whether the proposition holds or fails. Prove the first alternative. Prove the second alternative. Prove the second alternative. Assume the hypotheses and unpack their components.

Prove the first alternative. Establish an intermediate fact. Consider separately whether the proposition holds or fails. Prove the first alternative. Prove the second alternative.
-/
theorem mem_al_or_de {x : ℚ} :
    (x ∈ al h i ∨ x ∈ de h i) ↔ (∃ a, h.v a + h.e i = x) ∨ ∃ l, -h.b l + h.e i = x := by
  have hk := R.m_add_three_le_k
  have hi := i.2
  rw [mem_al, mem_de]
  constructor
  · rintro (⟨n, hn, rfl⟩ | ⟨c, hc, rfl⟩)
    · by_cases h1 : n < R.k - 1
      · exact Or.inl ⟨⟨n, h1⟩, by rw [← lamAt_head]⟩
      · exact Or.inr ⟨⟨n + 1 - R.k, by omega⟩, by rw [← lamAt_tail h n _ (by simp only; omega)]⟩
    · exact Or.inr ⟨⟨i + c + 1, by omega⟩, by rw [← lamAt_tail h (R.k + i + c) _ (by simp only; omega)]⟩
  · rintro (⟨a, rfl⟩ | ⟨l, rfl⟩)
    · exact Or.inl ⟨a, by have := a.2; omega, by rw [lamAt_head]⟩
    · have hl := l.2
      by_cases h1 : l.1 ≤ i.1
      · exact Or.inl ⟨R.k + l - 1, by omega, by rw [lamAt_tail h _ l (by omega)]⟩
      · exact Or.inr ⟨l - i - 1, by omega, by rw [lamAt_tail h _ l (by omega)]⟩

end HC

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem mem_block {t : ℕ} {x : ℚ} : x ∈ block t ↔ ∃ a < t, ((t : ℚ) - 1) / 2 - (a : ℚ) = x := by
  simp [block]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Supply the required witnesses or components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Supply the required witnesses or components.

Supply the required witnesses or components.
-/
theorem parDef_eq (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) :
    parDef D i τ = signed (al (D.hc τ) i ++ block D.R.t ++ de (D.hc τ) i) ([] ++ []) (-(D.hc τ).e i - 1 / 2) := by
  ext ⟨x, s⟩
  simp only [parDef, signed, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union,
    List.mem_toFinset, List.mem_map, List.append_nil, List.mem_append, Prod.mk.injEq, List.map_nil, List.not_mem_nil,
    or_false, TPar.block, mem_block, Finset.mem_range, or_right_comm (c := _ ∈ de (D.hc τ) i), mem_al_or_de]
  constructor
  · rintro ⟨_, (⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨a, ha, rfl⟩, rfl, rfl⟩
    · exact ⟨_, Or.inl (Or.inl ⟨a, rfl⟩), by ring, rfl⟩
    · exact ⟨_, Or.inl (Or.inr ⟨a, rfl⟩), by ring, rfl⟩
    · exact ⟨_, Or.inr ⟨a, ha, rfl⟩, by ring, rfl⟩
  · rintro ⟨_, (⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨a, ha, rfl⟩, rfl, rfl⟩
    · exact ⟨_, Or.inl (Or.inl ⟨a, rfl⟩), by ring, rfl⟩
    · exact ⟨_, Or.inl (Or.inr ⟨a, rfl⟩), by ring, rfl⟩
    · exact ⟨_, Or.inr ⟨a, ha, rfl⟩, by ring, rfl⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem centred_pair : ∀ (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau), ∃ al de : List ℚ, Centred D al [] [] de ∧
    parHol D i τ = signed (al ++ []) ([] ++ de) (-(D.hc τ).e i) ∧
    parDef D i τ = signed (al ++ block D.R.t ++ de) ([] ++ []) (-(D.hc τ).e i - 1 / 2) := by
  intro D i τ
  refine ⟨al (D.hc τ) i, de (D.hc τ) i, ⟨hypA _ i, fun x hx => far _ i hx, ?_⟩, ?_, parDef_eq D i τ⟩
  · rintro ⟨N, hN, hg⟩
    exact hypG _ i hN (hg τ i)
  · have hs : (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) :=
      D.sp.W_sigval _ (Nat.le_add_left _ _) i.2 _
    exact holPar_eq (D.hc τ) i (by rw [hs]; simp [Ranks.sigW]) (by rw [hs]; rfl)

end GlobalTheory.ArchRec.ParPair
