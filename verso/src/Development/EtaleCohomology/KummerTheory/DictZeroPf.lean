import Development.EtaleCohomology.KummerTheory.DictPf
import Development.EtaleCohomology.KummerTheory.CupAWCutEv
import Development.EtaleCohomology.TateTwists.EtaleChainCochainExistsOfEvalData
import Development.EtaleCohomology.TateTwists.EtaleSimplicialCochainExistsFromNaturalSections

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.DZ

/- English proof (translation)
Establish `e` using `LateralTheory.KummerTheory.AW.ev_add (0 : Cochain ((chains R).obj E) I n) 0 p s h U x`. Rewrite `e` using `[add_zero]`. Simplify using `using e.symm`.
-/
theorem ev_zero' (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} p s h U x :
    ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by
  have e := LateralTheory.KummerTheory.AW.ev_add (0 : Cochain ((chains R).obj E) I n) 0 p s h U x
  rw [add_zero] at e
  simpa using e.symm

end LateralTheory.KummerTheory.DZ

open LateralTheory.KummerTheory.DZ LateralTheory.EtaleFoundations in
/- English proof (translation)
Introduce `R _ I X n α hα`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← LateralTheory.KummerTheory.AW.ev_delta_zero (m := n + 1) rfl α.1 n (n + 1) (by simp) (by simp) X (𝟙 X), Cocycle.δ_eq_zero]`. Conclude with `ev_zero' R _ _ _ _ _`. Rewrite using `[CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff α (n - 1) (by omega)]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨β, hβ⟩`. Use `⟨ev β 0 (n - 1) (by simp) X (𝟙 X), ?_⟩` and prove the remaining obligations. Rewrite using `[← LateralTheory.KummerTheory.AW.ev_delta_zero (m := n) (by omega) β (n - 1) n (by simp) (by simp) X (𝟙 X), hβ]`. Introduce and unpack `⟨y, hy⟩`.

Take `⟨γ, hγ⟩` from `LateralTheory.EtaleFoundations.etale_chain_cochain_exists_of_eval_data R (a0 X I (n - 1) y) (etaleSimplicialCochain_scheme_section_extension_naturality X I (n - 1) y)`. Use `⟨γ, LateralTheory.KummerTheory.AW.ev_ext _ _ ?_⟩` and prove the remaining obligations. Introduce `p s h U x`. Consider the cases of `p with`. Consider the case `zero`.

Take `rfl : s = n` from `by omega`. Rewrite using `[LateralTheory.KummerTheory.AW.ev_delta_zero (m := s) (by omega) γ (s - 1) s (by simp) h U x, hγ, etaleSimplicialCochain_scheme_section_extension_degree_zero]`. Use `(map_res _ _ _).trans ?_` and prove the remaining obligations. Conclude with `(congrArg (Sec.res _) hy).trans (LateralTheory.KummerTheory.AW.ev_res α.1 0 s _ x (𝟙 X))`. Consider the case `succ p`.

Rewrite using `[hα p s h U x, LateralTheory.KummerTheory.AW.ev_delta_succ (m := n) (by omega) γ p (-((p + 1 : ℕ) : ℤ) + (n - 1)) s rfl h U x]`. Simplify using `only [hγ]`. Consider the cases of `p with`. Consider the case `zero`. Take `rfl : s = n - 1` from `by omega`.

Simplify using `[a0, Fin.sum_univ_two]`. Rewrite using `[show x.face 0 = x from rfl, show x.face 1 = x from rfl]`. Conclude with `add_neg_cancel _`. Consider the case `succ p => simp [a0]`.
-/
theorem LateralTheory.KummerTheory.DictZero_of : LateralTheory.KummerTheory.DictZero := by
  intro R _ I X n α hα
  refine ⟨?_, ?_⟩
  · rw [← LateralTheory.KummerTheory.AW.ev_delta_zero (m := n + 1) rfl α.1 n (n + 1) (by simp) (by simp) X (𝟙 X), Cocycle.δ_eq_zero]
    exact ev_zero' R _ _ _ _ _
  · rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff α (n - 1) (by omega)]
    constructor
    · rintro ⟨β, hβ⟩
      refine ⟨ev β 0 (n - 1) (by simp) X (𝟙 X), ?_⟩
      rw [← LateralTheory.KummerTheory.AW.ev_delta_zero (m := n) (by omega) β (n - 1) n (by simp) (by simp) X (𝟙 X), hβ]
    · rintro ⟨y, hy⟩
      obtain ⟨γ, hγ⟩ := LateralTheory.EtaleFoundations.etale_chain_cochain_exists_of_eval_data R (a0 X I (n - 1) y) (etaleSimplicialCochain_scheme_section_extension_naturality X I (n - 1) y)
      refine ⟨γ, LateralTheory.KummerTheory.AW.ev_ext _ _ ?_⟩
      intro p s h U x
      cases p with
      | zero =>
        obtain rfl : s = n := by omega
        rw [LateralTheory.KummerTheory.AW.ev_delta_zero (m := s) (by omega) γ (s - 1) s (by simp) h U x, hγ, etaleSimplicialCochain_scheme_section_extension_degree_zero]
        refine (map_res _ _ _).trans ?_
        exact (congrArg (Sec.res _) hy).trans (LateralTheory.KummerTheory.AW.ev_res α.1 0 s _ x (𝟙 X))
      | succ p =>
        rw [hα p s h U x, LateralTheory.KummerTheory.AW.ev_delta_succ (m := n) (by omega) γ p (-((p + 1 : ℕ) : ℤ) + (n - 1)) s rfl h U x]
        simp only [hγ]
        cases p with
        | zero =>
          obtain rfl : s = n - 1 := by omega
          simp [a0, Fin.sum_univ_two]
          rw [show x.face 0 = x from rfl, show x.face 1 = x from rfl]
          exact add_neg_cancel _
        | succ p => simp [a0]
