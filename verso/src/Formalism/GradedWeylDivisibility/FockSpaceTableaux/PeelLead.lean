import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LCpleadLemmas

open MvPolynomial
open scoped MonomialOrder

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Use `first`. Consider the case `exact Finsupp.lex_lt_iff.2 ⟨i, h1, h2⟩`. Consider the case `exact Finsupp.lex_def.2 ⟨i, h1, h2⟩`. Consider the case `exact ⟨i, h1, h2⟩`.
-/
private theorem toLex_lt_of_eq_of_lt_at {N : ℕ} {a b : Fin N →₀ ℕ} (i : Fin N)
    (h1 : ∀ i', i' < i → a i' = b i') (h2 : a i < b i) : toLex a < toLex b := by
  first
  | exact Finsupp.lex_lt_iff.2 ⟨i, h1, h2⟩
  | exact Finsupp.lex_def.2 ⟨i, h1, h2⟩
  | exact ⟨i, h1, h2⟩

/- English proof (translation)
Use `first`. Consider the case `(simp [Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply]; done)`. Consider the case `(simp [Finsupp.domCongr_apply]; done)`. Consider the case `rfl`.
-/
private theorem domCongr_cmIdx_apply_eq {r n : ℕ} (m : Fin r × Fin n →₀ ℕ)
    (x : Fin r × Fin n) :
    Finsupp.domCongr (cmIdx r n) m (cmIdx r n x) = m x := by
  first
  | (simp [Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply]; done)
  | (simp [Finsupp.domCongr_apply]; done)
  | rfl

/- English proof (translation)
Use `first`. Consider the case `exact M.le_degree hd`. Consider the case `(unfold MonomialOrder.degree; rw [AddEquiv.apply_symm_apply]; exact Finset.le_sup hd)`.
-/
private theorem toSyn_le_toSyn_degree_of_mem_support {σ R : Type*} [CommSemiring R] (M : MonomialOrder σ)
    {f : MvPolynomial σ R} {d : σ →₀ ℕ} (hd : d ∈ f.support) :
    M.toSyn d ≤ M.toSyn (M.degree f) := by
  first
  | exact M.le_degree hd
  | (unfold MonomialOrder.degree; rw [AddEquiv.apply_symm_apply]; exact Finset.le_sup hd)

/- English proof (translation)
Unfold `PeelLead`. Introduce `B _ _ r n l j hlj a0 ω g K hg hω hK htop`. Establish `hlj' : l ≠ j` using `ne_of_lt hlj`. Establish `hd : (colLex r n).degree (peel l j a0 K g) ∈ (peel l j a0 K g).support` using `(colLex r n).degree_mem_support hK`. Take `⟨m0, hm0, hm0K, hd_eq⟩` from `lcplead_mem_support_peel a0 K hd`.

Establish `hm0_eq` using `lcplead_recon hlj' a0 hg hm0`. Rewrite `hm0_eq` using `[hm0K, ← hd_eq]`. Rewrite using `[← hm0_eq]`. Establish `hg0 : g ≠ 0`. Introduce and unpack `rfl`.

Simplify using `at hm0`. Establish `hup : ∀ m ∈ g.support, (colLex r n).toSyn m ≤ (colLex r n).toSyn m0`. Introduce `m hm`. Break down `lt_trichotomy (m (a0, l)) K with hlt | heq | hgt` into its components or cases. Apply `le_of_lt` to reduce the goal to its premises.

Apply `colLex_lt_iff.2` to reduce the goal to its premises. Use `toLex_lt_of_eq_of_lt_at (cmIdx r n (a0, l)) ?_ ?_` and prove the remaining obligations. Introduce `i' hi'`. Take `⟨⟨b, t⟩, rfl⟩` from `(cmIdx r n).surjective i'`. Rewrite using `[domCongr_cmIdx_apply_eq, domCongr_cmIdx_apply_eq]`.

Break down `lcplead_cmIdx_lt hi' with ht | ⟨ht, hb⟩` into its components or cases. Establish `htl : t ≠ l` using `ne_of_lt ht`. Establish `htj : t ≠ j` using `ne_of_lt (lt_trans ht hlj)`. Rewrite using `[lcplead_hom_off hlj' hg hm b t htl htj, lcplead_hom_off hlj' hg hm0 b t htl htj]`. Rewrite using `[ht]`.

Establish `h1` using `lcplead_hom_row hlj' hg hm b`. Establish `h2` using `lcplead_hom_row hlj' hg hm0 b`. Establish `h3` using `hω b hb`. Use linear arithmetic over natural numbers and integers. Rewrite using `[domCongr_cmIdx_apply_eq, domCongr_cmIdx_apply_eq, hm0K]`.

Conclude with `hlt`. Establish `hc` using `lcplead_coeff_peel hlj' a0 hg hm`. Rewrite `hc` using `[heq]`. Establish `he : (m.erase (a0, l)).erase (a0, j) ∈ (peel l j a0 K g).support`. Rewrite using `[mem_support_iff, hc]`.

Conclude with `mem_support_iff.1 hm`. Establish `hle` using `toSyn_le_toSyn_degree_of_mem_support (colLex r n) he`. Establish `hm_eq` using `lcplead_recon hlj' a0 hg hm`. Rewrite `hm_eq` using `[heq]`. Rewrite using `[hm_eq, hm0_eq]`.

Simplify using `only [map_add]`. Use `first`. Consider the case `exact add_le_add le_rfl hle`. Consider the case `exact add_le_add_left hle _`. Consider the case `gcongr`.

It suffices to derive a contradiction. Establish `hc` using `lcplead_coeff_peel hlj' a0 hg hm`. Rewrite `hc` using `[htop _ hgt, coeff_zero]`. Conclude with `mem_support_iff.1 hm hc.symm`. Conclude with `(colLex r n).toSyn.injective (le_antisymm (hup _ ((colLex r n).degree_mem_support hg0)) (toSyn_le_toSyn_degree_of_mem_support (colLex r n) hm0))`.
-/
theorem sliceLeading : PeelLead := by
  unfold PeelLead
  intro B _ _ r n l j hlj a0 ω g K hg hω hK htop
  have hlj' : l ≠ j := ne_of_lt hlj
  have hd : (colLex r n).degree (peel l j a0 K g) ∈
      (peel l j a0 K g).support :=
    (colLex r n).degree_mem_support hK
  obtain ⟨m0, hm0, hm0K, hd_eq⟩ := lcplead_mem_support_peel a0 K hd
  have hm0_eq := lcplead_recon hlj' a0 hg hm0
  rw [hm0K, ← hd_eq] at hm0_eq
  rw [← hm0_eq]
  have hg0 : g ≠ 0 := by
    rintro rfl
    simp at hm0
  have hup : ∀ m ∈ g.support, (colLex r n).toSyn m ≤ (colLex r n).toSyn m0 := by
    intro m hm
    rcases lt_trichotomy (m (a0, l)) K with hlt | heq | hgt
    · apply le_of_lt
      apply colLex_lt_iff.2
      refine toLex_lt_of_eq_of_lt_at (cmIdx r n (a0, l)) ?_ ?_
      · intro i' hi'
        obtain ⟨⟨b, t⟩, rfl⟩ := (cmIdx r n).surjective i'
        rw [domCongr_cmIdx_apply_eq, domCongr_cmIdx_apply_eq]
        rcases lcplead_cmIdx_lt hi' with ht | ⟨ht, hb⟩
        · have htl : t ≠ l := ne_of_lt ht
          have htj : t ≠ j := ne_of_lt (lt_trans ht hlj)
          rw [lcplead_hom_off hlj' hg hm b t htl htj,
            lcplead_hom_off hlj' hg hm0 b t htl htj]
        · rw [ht]
          have h1 := lcplead_hom_row hlj' hg hm b
          have h2 := lcplead_hom_row hlj' hg hm0 b
          have h3 := hω b hb
          omega
      · rw [domCongr_cmIdx_apply_eq, domCongr_cmIdx_apply_eq, hm0K]
        exact hlt
    · have hc := lcplead_coeff_peel hlj' a0 hg hm
      rw [heq] at hc
      have he : (m.erase (a0, l)).erase (a0, j) ∈ (peel l j a0 K g).support := by
        rw [mem_support_iff, hc]
        exact mem_support_iff.1 hm
      have hle := toSyn_le_toSyn_degree_of_mem_support (colLex r n) he
      have hm_eq := lcplead_recon hlj' a0 hg hm
      rw [heq] at hm_eq
      rw [hm_eq, hm0_eq]
      simp only [map_add]
      first
      | exact add_le_add le_rfl hle
      | exact add_le_add_left hle _
      | gcongr
    · exfalso
      have hc := lcplead_coeff_peel hlj' a0 hg hm
      rw [htop _ hgt, coeff_zero] at hc
      exact mem_support_iff.1 hm hc.symm
  exact (colLex r n).toSyn.injective
    (le_antisymm (hup _ ((colLex r n).degree_mem_support hg0))
      (toSyn_le_toSyn_degree_of_mem_support (colLex r n) hm0))

end Formalism.GradedWeylDivisibility
