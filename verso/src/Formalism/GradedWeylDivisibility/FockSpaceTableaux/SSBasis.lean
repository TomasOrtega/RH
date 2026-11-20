import Formalism.GradedWeylDivisibility.StatementD
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDbasisLemmas

open MvPolynomial

namespace Formalism.GradedWeylDivisibility

open scoped MonomialOrder

/- English proof (translation)
Introduce `R _ _ k n ν`. Establish `hex : ∀ m : ssIdx k n ν, ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ i, sz i ≤ n) (I : ∀ i, Fin (sz i) → Fin k), shapeDeg sz = ν ∧ (∀ i, StrictMono (I i)) ∧ bidetExp sz hsz I = m.1` using `fun m => sSYTExists k n ν m.1 m.2.2 m.2.1`. Use `choose K sz hsz I hshape hmono hexp using hex`. Use `set b : ssIdx k n ν → MvPolynomial (Fin k × Fin n) R := fun m => bideterminant R (sz m) (hsz m) (I m) with hb`. Establish `hdeg : ∀ m, (colLex k n).degree (b m) = m.1` using `fun m => (column_lex_bideterminant R k n (K m) (sz m) (hsz m) (I m) (hmono m)).1.trans (hexp m)`.

Establish `hlc : ∀ m, (colLex k n).leadingCoeff (b m) = 1` using `fun m => (column_lex_bideterminant R k n (K m) (sz m) (hsz m) (I m) (hmono m)).2`. Establish `hmem : ∀ m, b m ∈ dualWeyl R k n ν` using `fun m => by`. Use `bidetMem R k n (K m) (sz m) (hsz m) (I m)` as an intermediate fact. Rewrite `this` using `[hshape m]`. Conclude with `this`.

Use `⟨b, ⟨?_, ?_, ?_⟩, fun m => ⟨hdeg m, hlc m, K m, sz m, hsz m, I m, hshape m, hmono m, rfl⟩⟩` and prove the remaining obligations. Use `ldbasis_linearIndependent (colLex k n) b ?_ hlc` and prove the remaining obligations. Introduce `m m' h`. Conclude with `Subtype.ext ((hdeg m).symm.trans (h.trans (hdeg m')))`. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨m, rfl⟩`. Conclude with `hmem m`. It suffices to establish `key : ∀ d : (colLex k n).syn, ∀ f ∈ dualWeyl R k n ν, (colLex k n).toSyn ((colLex k n).degree f) = d → f ∈ Submodule.span R (Set.range b) by`. Introduce `f hf`.

Conclude with `key _ f hf rfl`. Introduce `d`. Proceed by induction on `d using WellFoundedLT.induction with`. Consider the case `_ d ih`. Introduce `f hf hd`.

Distinguish the cases in `hf0 : f = 0`. Rewrite using `[hf0]`. Conclude with `Submodule.zero_mem _`. Use `set m := (colLex k n).degree f with hm`. Establish `hint : Interlaced m` using `leadInterlaced R k n ν f hf hf0`.

Establish `hcol : ∀ t : Fin n, ∑ a : Fin k, m (a, t) = ν t` using `colSums R k n ν f hf m (((colLex k n).degree_mem_support_iff f).mpr hf0)`. Use `set mi : ssIdx k n ν := ⟨m, hint, hcol⟩ with hmi`. Establish `hbS : b mi ∈ Submodule.span R (Set.range b)` using `Submodule.subset_span ⟨mi, rfl⟩`. Use `set f' := f - (colLex k n).leadingCoeff f • b mi with hf'`. Establish `hf'mem : f' ∈ dualWeyl R k n ν` using `Submodule.sub_mem _ hf (Submodule.smul_mem _ _ (hmem mi))`.

Establish `hdecomp : f = f' + (colLex k n).leadingCoeff f • b mi`. Rewrite using `[hf']`. Normalize the expressions using the abelian group laws. Rewrite using `[hdecomp]`. Use `Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ hbS)` and prove the remaining obligations.

Distinguish the cases in `h0 : f' = 0`. Rewrite using `[h0]`. Conclude with `Submodule.zero_mem _`. Establish `hlt` using `lcassem_sub_lt (colLex k n) (f := f) (g := b mi) (hdeg mi) (hlc mi) h0`. Conclude with `ih _ (hd ▸ hlt) f' hf'mem rfl`.

Introduce `m`. Use `show IsWeightedHomogeneous (rowW k n) (bideterminant R (sz m) (hsz m) (I m)) (rowWt m.1)`. Rewrite using `[← hexp m, ldbasis_rowWt_bidetExp]`. Conclude with `ldbasis_bidet_rowHom R (sz m) (hsz m) (I m)`.
-/
theorem semistandard_basis : SSBasis := by
  intro R _ _ k n ν
  have hex : ∀ m : ssIdx k n ν, ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ i, sz i ≤ n)
      (I : ∀ i, Fin (sz i) → Fin k),
      shapeDeg sz = ν ∧ (∀ i, StrictMono (I i)) ∧ bidetExp sz hsz I = m.1 := fun m =>
    sSYTExists k n ν m.1 m.2.2 m.2.1
  choose K sz hsz I hshape hmono hexp using hex
  set b : ssIdx k n ν → MvPolynomial (Fin k × Fin n) R := fun m => bideterminant R (sz m) (hsz m) (I m) with hb
  have hdeg : ∀ m, (colLex k n).degree (b m) = m.1 := fun m =>
    (column_lex_bideterminant R k n (K m) (sz m) (hsz m) (I m) (hmono m)).1.trans (hexp m)
  have hlc : ∀ m, (colLex k n).leadingCoeff (b m) = 1 := fun m =>
    (column_lex_bideterminant R k n (K m) (sz m) (hsz m) (I m) (hmono m)).2
  have hmem : ∀ m, b m ∈ dualWeyl R k n ν := fun m => by
    have := bidetMem R k n (K m) (sz m) (hsz m) (I m)
    rw [hshape m] at this
    exact this
  refine ⟨b, ⟨?_, ?_, ?_⟩, fun m => ⟨hdeg m, hlc m, K m, sz m, hsz m, I m, hshape m, hmono m, rfl⟩⟩
  ·
    refine ldbasis_linearIndependent (colLex k n) b ?_ hlc
    intro m m' h
    exact Subtype.ext ((hdeg m).symm.trans (h.trans (hdeg m')))
  ·
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨m, rfl⟩
      exact hmem m
    · suffices key : ∀ d : (colLex k n).syn, ∀ f ∈ dualWeyl R k n ν,
          (colLex k n).toSyn ((colLex k n).degree f) = d → f ∈ Submodule.span R (Set.range b) by
        intro f hf
        exact key _ f hf rfl
      intro d
      induction d using WellFoundedLT.induction with
      | _ d ih =>
        intro f hf hd
        by_cases hf0 : f = 0
        · rw [hf0]; exact Submodule.zero_mem _
        set m := (colLex k n).degree f with hm
        have hint : Interlaced m := leadInterlaced R k n ν f hf hf0
        have hcol : ∀ t : Fin n, ∑ a : Fin k, m (a, t) = ν t :=
          colSums R k n ν f hf m (((colLex k n).degree_mem_support_iff f).mpr hf0)
        set mi : ssIdx k n ν := ⟨m, hint, hcol⟩ with hmi
        have hbS : b mi ∈ Submodule.span R (Set.range b) := Submodule.subset_span ⟨mi, rfl⟩
        set f' := f - (colLex k n).leadingCoeff f • b mi with hf'
        have hf'mem : f' ∈ dualWeyl R k n ν :=
          Submodule.sub_mem _ hf (Submodule.smul_mem _ _ (hmem mi))
        have hdecomp : f = f' + (colLex k n).leadingCoeff f • b mi := by
          rw [hf']; abel
        rw [hdecomp]
        refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ hbS)
        by_cases h0 : f' = 0
        · rw [h0]; exact Submodule.zero_mem _
        have hlt := lcassem_sub_lt (colLex k n) (f := f) (g := b mi) (hdeg mi) (hlc mi) h0
        exact ih _ (hd ▸ hlt) f' hf'mem rfl
  ·
    intro m
    show IsWeightedHomogeneous (rowW k n) (bideterminant R (sz m) (hsz m) (I m)) (rowWt m.1)
    rw [← hexp m, ldbasis_rowWt_bidetExp]
    exact ldbasis_bidet_rowHom R (sz m) (hsz m) (I m)

end Formalism.GradedWeylDivisibility
