import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GEquivIntL

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

namespace GlobalTheory.SatIso

/- English proof (translation)
Use `⟨hfin.toFinset, fun c => if hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x then Dv.hval h (Dv.loc hc.choose) else 0, fun c => if hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x then hc.choose else 1, fun W _ _ φ => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`. Unfold `heckeFunI`. Rewrite using `[finsum_eq_sum_of_support_subset (s := hfin.toFinset)]`. Rewrite using `[Finset.sum_apply]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Distinguish the cases in `hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x`. Simplify using `only [dif_pos hc]`. Both sides reduce to the same expression. Simplify using `only [dif_neg hc, zero_smul]`.

Both sides reduce to the same expression. Introduce `c hc0`. Rewrite `hc0` using `[Function.mem_support]`. Distinguish the cases in `hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x`. Rewrite `hc0` using `[dif_pos hc]`.

Rewrite using `[Set.Finite.coe_toFinset]`. Use `⟨hc.choose, hc.choose_spec.1, hc.choose_spec.2, fun h0 => hc0 ?_⟩` and prove the remaining obligations. Rewrite using `[h0, zero_smul]`. Conclude with `absurd (dif_neg hc) hc0`.
-/
theorem heckeFunI_eq_sum {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}
    (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)) (h : GU Dv.σw n → ℂ)
    (hfin : Set.Finite {c : GAf L n ⧸ U | ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x ∧
      Dv.hval h (Dv.loc x) ≠ 0}) :
    ∃ (C : Finset (GAf L n ⧸ U)) (a : GAf L n ⧸ U → ℂ) (x : GAf L n ⧸ U → GAf L n),
      ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (φ : GAf L n → W),
        heckeFunI L n U Dv h φ = ∑ c ∈ C, a c • NG.rt L n (x c) φ := by
  classical
  refine ⟨hfin.toFinset,
    fun c => if hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x then
      Dv.hval h (Dv.loc hc.choose) else 0,
    fun c => if hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x then
      hc.choose else 1, fun W _ _ φ => ?_⟩
  funext g
  unfold heckeFunI
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
  · rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x
    · simp only [dif_pos hc]
      rfl
    · simp only [dif_neg hc, zero_smul]
      rfl
  · intro c hc0
    rw [Function.mem_support] at hc0
    by_cases hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x
    · rw [dif_pos hc] at hc0
      rw [Set.Finite.coe_toFinset]
      refine ⟨hc.choose, hc.choose_spec.1, hc.choose_spec.2, fun h0 => hc0 ?_⟩
      rw [h0, zero_smul]
    · exact absurd (dif_neg hc) hc0

/- English proof (translation)
Take `⟨f, hfS, hf0, U, hU, hUv, hH⟩` from `hs`. Take `⟨T, hT⟩` from `hiso.2`. Use `⟨(T ⟨f, hfS⟩ : π'.S), (T ⟨f, hfS⟩).2, ?_, U, ?_, hUv, ?_⟩` and prove the remaining obligations. Introduce `h0`. Establish `h1 : T ⟨f, hfS⟩ = 0` using `Subtype.ext h0`.

Establish `h2 : (⟨f, hfS⟩ : π.S) = 0` using `T.map_eq_zero_iff.mp h1`. Conclude with `hf0 (congrArg Subtype.val h2)`. Introduce `κ hκ`. Conclude with `(hT κ ⟨f, hfS⟩ ⟨f, hfS⟩ (hU κ hκ).symm).symm`. Introduce `h hh`.

Take `⟨C, a, x, hC⟩` from `heckeFunI_eq_sum Dv U h (hfin U hUv h hh)`. Establish `e` using `hH h hh`. Rewrite `e` using `[hC]`. Rewrite using `[hC]`. Establish `e1 : (∑ c ∈ C, a c • (⟨NG.rt L n (x c) f, π.irrS.1.stable _ _ hfS⟩ : π.S)) = SatU Dv.ϖ (qV (maximalRealSubfield L) v) h α • (⟨f, hfS⟩ : π.S)`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Submodule.coe_sum]`. Conclude with `e`. Establish `e2` using `congrArg (fun y => ((T y : π'.S) : GAf L n → π'.W)) e1`. Simplify using `only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul] at e2`.

Rewrite using `[← e2]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[hT (x c) ⟨f, hfS⟩ ⟨NG.rt L n (x c) f, π.irrS.1.stable _ _ hfS⟩ rfl]`.
-/
theorem satAt_of_iso (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π π' : NG.AutRep L n)
    (hiso : π.Iso π') (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ)
    (hfin : ∀ (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) →
      ∀ h ∈ Hecke ℂ (KU Dv.σw n), Set.Finite {c : GAf L n ⧸ U | ∃ x : GAf L n,
        (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x ∧ Dv.hval h (Dv.loc x) ≠ 0})
    (hs : NG.SatAt π Dv α) : NG.SatAt π' Dv α := by
  obtain ⟨f, hfS, hf0, U, hU, hUv, hH⟩ := hs
  obtain ⟨T, hT⟩ := hiso.2
  refine ⟨(T ⟨f, hfS⟩ : π'.S), (T ⟨f, hfS⟩).2, ?_, U, ?_, hUv, ?_⟩
  · intro h0
    have h1 : T ⟨f, hfS⟩ = 0 := Subtype.ext h0
    have h2 : (⟨f, hfS⟩ : π.S) = 0 := T.map_eq_zero_iff.mp h1
    exact hf0 (congrArg Subtype.val h2)
  · intro κ hκ
    exact (hT κ ⟨f, hfS⟩ ⟨f, hfS⟩ (hU κ hκ).symm).symm
  · intro h hh
    obtain ⟨C, a, x, hC⟩ := heckeFunI_eq_sum Dv U h (hfin U hUv h hh)
    have e := hH h hh
    rw [hC] at e
    rw [hC]
    have e1 : (∑ c ∈ C, a c • (⟨NG.rt L n (x c) f, π.irrS.1.stable _ _ hfS⟩ : π.S)) =
        SatU Dv.ϖ (qV (maximalRealSubfield L) v) h α • (⟨f, hfS⟩ : π.S) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      exact e
    have e2 := congrArg (fun y => ((T y : π'.S) : GAf L n → π'.W)) e1
    simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul] at e2
    rw [← e2]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hT (x c) ⟨f, hfS⟩ ⟨NG.rt L n (x c) f, π.irrS.1.stable _ _ hfS⟩ rfl]

end GlobalTheory.SatIso
