import Formalism.GradedWeylDivisibility.FinalB
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.MinorExpLt
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.ColLexInitMinor
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.ColumnLexBideterminant
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.ColSums
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.SSYTPeel
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.SSYTExists
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.CompDeg
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LeadComp
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.PeelDecomp
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.PeelHomog
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.PeelLead
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.EvalDeg
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.PeelDegBound
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.TwoColumn
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LeadInterlaced
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.SMSAssembly
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.StandardMonomialSpanOf

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
The claim follows from `minorExponentLt`.
-/
theorem minorExpLt : MinorExpLt := minorExponentLt
/- English proof (translation)
The claim follows from `colLexInitMinor_of minorExpLt`.
-/
theorem colLexInitMinor : ColLexInitMinor := colLexInitMinor_of minorExpLt
/- English proof (translation)
The claim follows from `columnLexBideterminant_of_initialMinor colLexInitMinor`.
-/
theorem column_lex_bideterminant : ColumnLexBideterminant := columnLexBideterminant_of_initialMinor colLexInitMinor
/- English proof (translation)
The claim follows from `columnSums_holds`.
-/
theorem colSums : ColSums := columnSums_holds
/- English proof (translation)
The claim follows from `semistandardPeel`.
-/
theorem sSYTPeel : SSYTPeel := semistandardPeel
/- English proof (translation)
The claim follows from `sSYTExists_of sSYTPeel`.
-/
theorem sSYTExists : SSYTExists := sSYTExists_of sSYTPeel
/- English proof (translation)
The claim follows from `componentDegree`.
-/
theorem compDeg : CompDeg := componentDegree
/- English proof (translation)
The claim follows from `leadingComponent`.
-/
theorem leadComp : LeadComp := leadingComponent
/- English proof (translation)
The claim follows from `peelDecomposition`.
-/
theorem peelDecomp : PeelDecomp := peelDecomposition
/- English proof (translation)
The claim follows from `sliceHomogeneous`.
-/
theorem peelHomog : PeelHomog := sliceHomogeneous
/- English proof (translation)
The claim follows from `sliceLeading`.
-/
theorem peelLead : PeelLead := sliceLeading
/- English proof (translation)
The claim follows from `evalDegree`.
-/
theorem evalDeg : EvalDeg := evalDegree
/- English proof (translation)
The claim follows from `peelDegBound_of evalDeg`.
-/
theorem peelDegBound : PeelDegBound := peelDegBound_of evalDeg
/- English proof (translation)
The claim follows from `twoColumn_of peelDecomp peelHomog peelLead peelDegBound`.
-/
theorem twoColumn : TwoColumn := twoColumn_of peelDecomp peelHomog peelLead peelDegBound
/- English proof (translation)
The claim follows from `leadInterlaced_of compDeg leadComp twoColumn`.
-/
theorem leadInterlaced : LeadInterlaced := leadInterlaced_of compDeg leadComp twoColumn
/- English proof (translation)
The claim follows from `semistandard_module_assembly column_lex_bideterminant colSums sSYTExists leadInterlaced`.
-/
theorem standardMonomialSpanDomain : StandardMonomialSpanDomain :=
  semistandard_module_assembly column_lex_bideterminant colSums sSYTExists leadInterlaced

/- English proof (translation)
The claim follows from `standardMonomialSpanOf standardMonomialSpanDomain`.
-/
theorem standardMonomialSpan : StandardMonomialSpan :=
  standardMonomialSpanOf standardMonomialSpanDomain

/- English proof (translation)
Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `m hm`. Simplify using `only [Finset.prod_empty] at hm`.

Establish `hm0 : m = 0`. Assume the negation of the conclusion as `h`. Apply `(MvPolynomial.mem_support_iff.mp hm)` to reduce the goal to its premises. Rewrite using `[MvPolynomial.coeff_one, if_neg (Ne.symm h)]`. Substitute `hm0` using the available equality.

Simplify using `[rowPart_zero]`. Consider the case `@insert j s hj ih`. Introduce `m hm`. Rewrite `hm` using `[Finset.prod_insert hj]`. Take `⟨m1, hm1, m2, hm2, rfl⟩` from `Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)`.

Rewrite using `[rowPart_add, Finset.sum_insert hj]`. Conclude with `Nat.add_le_add ((initMinor_support (I j) (hsz j) m1 hm1).1 k) (ih m2 hm2)`.
-/
private theorem bidet_rowPart_lemma {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) (k : ℕ) :
    ∀ (s : Finset (Fin K)) (m : Fin r × Fin n →₀ ℕ),
      m ∈ (∏ j ∈ s, initMinor ℤ (I j) (hsz j)).support → rowPart k m ≤ ∑ j ∈ s, min k (sz j) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro m hm
    simp only [Finset.prod_empty] at hm
    have hm0 : m = 0 := by
      by_contra h
      apply (MvPolynomial.mem_support_iff.mp hm)
      rw [MvPolynomial.coeff_one, if_neg (Ne.symm h)]
    subst hm0
    simp [rowPart_zero]
  | @insert j s hj ih =>
    intro m hm
    rw [Finset.prod_insert hj] at hm
    obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
    rw [rowPart_add, Finset.sum_insert hj]
    exact Nat.add_le_add ((initMinor_support (I j) (hsz j) m1 hm1).1 k) (ih m2 hm2)

/- English proof (translation)
Establish `h1 : ∀ a : Fin r, rowNu (r` using `r) (shapeDeg (n := n) sz) a = ∑ j : Fin K, if a.val < sz j then 1 else 0 := by`. Introduce `a`. Unfold `rowNu`. Use `split_ifs with h`. Unfold `shapeDeg`.

Rewrite using `[Finset.card_filter]`. Use `symm`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `j _`. Use `hsz j` as an intermediate fact.

Conclude with `if_neg (by omega)`. Establish `h2 : ∀ j : Fin K, min k (sz j) = ∑ a : Fin r with a.val < k, if a.val < sz j then 1 else 0`. Introduce `j`. Establish `hj : sz j ≤ r` using `(hsz j).trans hnr`. Rewrite using `[← Finset.card_filter, Finset.filter_filter]`.

Establish `hset : (Finset.univ.filter fun a : Fin r => a.val < k ∧ a.val < sz j).map Fin.valEmbedding = Finset.range (min k (sz j))`. Use extensionality with `x`. Simplify using `only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply, Finset.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, rfl⟩`.

Use linear arithmetic over natural numbers and integers. Introduce `hx`. Conclude with `⟨⟨x, by omega⟩, by simp only; omega, rfl⟩`. Rewrite using `[← Finset.card_map Fin.valEmbedding, hset, Finset.card_range]`. Rewrite using `[Finset.sum_congr rfl (fun a _ => h1 a), Finset.sum_comm]`.

Conclude with `le_of_eq (Finset.sum_congr rfl (fun j _ => h2 j))`.
-/
private theorem sum_rowNu_lemma_2 {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ j, sz j ≤ n) (hnr : n ≤ r)
    (k : ℕ) :
    ∑ j : Fin K, min k (sz j) ≤ ∑ a : Fin r with a.val < k, rowNu (r := r) (shapeDeg (n := n) sz) a := by
  classical
  have h1 : ∀ a : Fin r, rowNu (r := r) (shapeDeg (n := n) sz) a =
      ∑ j : Fin K, if a.val < sz j then 1 else 0 := by
    intro a
    unfold rowNu
    split_ifs with h
    · unfold shapeDeg
      rw [Finset.card_filter]
    · symm
      apply Finset.sum_eq_zero
      intro j _
      have := hsz j
      exact if_neg (by omega)
  have h2 : ∀ j : Fin K, min k (sz j) = ∑ a : Fin r with a.val < k, if a.val < sz j then 1 else 0 := by
    intro j
    have hj : sz j ≤ r := (hsz j).trans hnr
    rw [← Finset.card_filter, Finset.filter_filter]
    have hset : (Finset.univ.filter fun a : Fin r => a.val < k ∧ a.val < sz j).map Fin.valEmbedding =
        Finset.range (min k (sz j)) := by
      ext x
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.valEmbedding_apply, Finset.mem_range]
      constructor
      · rintro ⟨a, ha, rfl⟩
        omega
      · intro hx
        exact ⟨⟨x, by omega⟩, by simp only; omega, rfl⟩
    rw [← Finset.card_map Fin.valEmbedding, hset, Finset.card_range]
  rw [Finset.sum_congr rfl (fun a _ => h1 a), Finset.sum_comm]
  exact le_of_eq (Finset.sum_congr rfl (fun j _ => h2 j))

/- English proof (translation)
Introduce `r n ν hnr hν f hf m hm`. Establish `hcol` using `colSums ℤ r n ν f hf m hm`. Use `⟨fun k => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[standardMonomialSpan r n ν hν] at hf clear hcol show rowPart k m ≤ _`. Proceed by induction on `hf using Submodule.span_induction generalizing m with`.

Consider the case `mem x hx`. Take `⟨K, sz, hsz, I, hν', rfl⟩` from `hx`. Substitute `hν'` using the available equality. Conclude with `(bidet_rowPart_lemma sz hsz I k Finset.univ m hm).trans (sum_rowNu_lemma_2 sz hsz hnr k)`. Consider the case `zero => simp at hm`.

Consider the case `add x y _ _ ihx ihy`. Break down `Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h` into its components or cases. Conclude with `ihx m h`. Conclude with `ihy m h`. Consider the case `smul a x _ ihx`.

Conclude with `ihx m (MvPolynomial.support_smul hm)`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hnr`. Establish `hL : ∑ a : Fin (n + d), rowDeg m a = ∑ s : Fin n, ν s`. Unfold `rowDeg`. Rewrite using `[Finset.sum_comm]`.

Conclude with `Finset.sum_congr rfl (fun s _ => hcol s)`. Rewrite using `[hL, Fin.sum_univ_add]`. Simplify using `[rowNu]`.
-/
theorem dualWeylDominanceZ :
    ∀ (r n : ℕ) (ν : Fin n → ℕ), n ≤ r → Antitone ν → ∀ f ∈ dualWeyl ℤ r n ν, ∀ m ∈ f.support,
      (∀ k : ℕ, (∑ a : Fin r with a.val < k, rowDeg m a) ≤ ∑ a : Fin r with a.val < k, rowNu (r := r) ν a) ∧
      ∑ a : Fin r, rowDeg m a = ∑ a : Fin r, rowNu (r := r) ν a := by
  intro r n ν hnr hν f hf m hm
  have hcol := colSums ℤ r n ν f hf m hm
  refine ⟨fun k => ?_, ?_⟩
  · rw [standardMonomialSpan r n ν hν] at hf
    clear hcol
    show rowPart k m ≤ _
    induction hf using Submodule.span_induction generalizing m with
    | mem x hx =>
      obtain ⟨K, sz, hsz, I, hν', rfl⟩ := hx
      subst hν'
      exact (bidet_rowPart_lemma sz hsz I k Finset.univ m hm).trans (sum_rowNu_lemma_2 sz hsz hnr k)
    | zero => simp at hm
    | add x y _ _ ihx ihy =>
      rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
      · exact ihx m h
      · exact ihy m h
    | smul a x _ ihx =>
      exact ihx m (MvPolynomial.support_smul hm)
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnr
    have hL : ∑ a : Fin (n + d), rowDeg m a = ∑ s : Fin n, ν s := by
      unfold rowDeg
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun s _ => hcol s)
    rw [hL, Fin.sum_univ_add]
    simp [rowNu]

end Formalism.GradedWeylDivisibility
