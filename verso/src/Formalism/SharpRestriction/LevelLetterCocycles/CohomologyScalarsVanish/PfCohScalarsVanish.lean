import Formalism.SharpRestriction.LevelLetterCocycles.CohomologyScalarsVanish.CohScalarsVanish

noncomputable section

namespace Formalism.MainNotions.N.CohomologyScalarsVanish

open ReciprocityTheory.Gal

/- English proof (translation)
Introduce `n k _ G _ _ M _ _ _ _ _ _ _ rho rho' hrr hyp`. Take `⟨h0, h1, h2⟩` from `hyp`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite `h0`, the goal using `[eq_bot_iff]`. Introduce `m hm`.

Establish `hm' : m ∈ H0 rho'` using `by show m ∈ rho'.invariants`. Rewrite using `[Representation.mem_invariants]`. Introduce `g`. Rewrite using `[hrr]`. Conclude with `(Representation.mem_invariants _ _).1 hm g`.

Conclude with `h0 hm'`. Rewrite `h1`, the goal using `[Submodule.Quotient.subsingleton_iff]`. Rewrite `h1`, the goal using `[eq_top_iff]`. Introduce and unpack `⟨f, hf⟩ -`. Establish `hf' : f ∈ Z1 rho'` using `⟨hf.1, fun g h => by rw [hrr]; exact hf.2 g h⟩`.

Take `⟨m, hm⟩` from `h1 (Submodule.mem_top (x := (⟨f, hf'⟩ : Z1 rho')))`. Use `⟨m, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`. Establish `h3` using `congrFun hm g`. Simplify using `only [d0, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply] at h3 ⊢`.

Rewrite using `[← hrr]`. Conclude with `h3`. Rewrite `h2`, the goal using `[Submodule.Quotient.subsingleton_iff]`. Rewrite `h2`, the goal using `[eq_top_iff]`. Introduce and unpack `⟨f, hf⟩ -`.

Establish `hf' : f ∈ Z2 rho'` using `⟨hf.1, fun g h l => by rw [hrr]; exact hf.2 g h l⟩`. Take `⟨c, hc, hcf⟩` from `h2 (Submodule.mem_top (x := (⟨f, hf'⟩ : Z2 rho')))`. Use `⟨c, hc, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `p`. Establish `h3` using `congrFun hcf p`.

Simplify using `only [d1, LinearMap.coe_mk, AddHom.coe_mk] at h3 ⊢`. Rewrite using `[← hrr]`. Conclude with `h3`.
-/
theorem cohScalarsVanish : CohScalarsVanish := by
  intro n k _ G _ _ M _ _ _ _ _ _ _ rho rho' hrr hyp
  obtain ⟨h0, h1, h2⟩ := hyp
  refine ⟨?_, ?_, ?_⟩
  · rw [eq_bot_iff] at h0 ⊢
    intro m hm
    have hm' : m ∈ H0 rho' := by
      show m ∈ rho'.invariants
      rw [Representation.mem_invariants]
      intro g
      rw [hrr]
      exact (Representation.mem_invariants _ _).1 hm g
    exact h0 hm'
  · rw [Submodule.Quotient.subsingleton_iff] at h1 ⊢
    rw [eq_top_iff] at h1 ⊢
    rintro ⟨f, hf⟩ -
    have hf' : f ∈ Z1 rho' := ⟨hf.1, fun g h => by rw [hrr]; exact hf.2 g h⟩
    obtain ⟨m, hm⟩ := h1 (Submodule.mem_top (x := (⟨f, hf'⟩ : Z1 rho')))
    refine ⟨m, ?_⟩
    funext g
    have h3 := congrFun hm g
    simp only [d0, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply] at h3 ⊢
    rw [← hrr]
    exact h3
  · rw [Submodule.Quotient.subsingleton_iff] at h2 ⊢
    rw [eq_top_iff] at h2 ⊢
    rintro ⟨f, hf⟩ -
    have hf' : f ∈ Z2 rho' := ⟨hf.1, fun g h l => by rw [hrr]; exact hf.2 g h l⟩
    obtain ⟨c, hc, hcf⟩ := h2 (Submodule.mem_top (x := (⟨f, hf'⟩ : Z2 rho')))
    refine ⟨c, hc, ?_⟩
    funext p
    have h3 := congrFun hcf p
    simp only [d1, LinearMap.coe_mk, AddHom.coe_mk] at h3 ⊢
    rw [← hrr]
    exact h3

end Formalism.MainNotions.N.CohomologyScalarsVanish
