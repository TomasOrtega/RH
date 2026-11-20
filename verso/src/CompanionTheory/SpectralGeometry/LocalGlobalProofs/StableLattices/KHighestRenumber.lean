import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ScalarCharacterOfL2Embedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KTypesAboveOfDsClass

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.LowestData

open Formalism.REAL (KHighest)
open GlobalTheory.LowestKTypeDetermines (rhoC_perm lowK_add strictAnti_add_rho nsq_add_cone eq_zero_of_nsq nsq_comp)

variable {n : ℕ}

/- English proof (translation)
Take `⟨h1, h2⟩` from `h`. Use `⟨fun a => ?_, fun a b hab he => ?_⟩` and prove the remaining obligations. Use `h1 (s'.symm (s a))` as an intermediate fact. Simplify using `using this`. Establish `hlt` using `hs a b hab he`.

Establish `key : s'.symm (s a) < s'.symm (s b)`. Assume the negation of the conclusion as `hn`. Establish `hle` using `not_lt.1 hn`. Break down `hle.lt_or_eq with hl | he'` into its components or cases. Use `hs' _ _ hl (by simpa using he.symm)` as an intermediate fact.

Simplify using `only [Equiv.apply_symm_apply] at this`. Conclude with `absurd this (not_lt.2 hlt.le)`. Use `s'.symm.injective he'` as an intermediate fact. Conclude with `absurd this hlt.ne'`. Use `h2 _ _ key (by simpa using he)` as an intermediate fact.

Simplify using `using this`.
-/
theorem kHighest_renumber {V : Type} [AddCommGroup V] [Module ℂ V] (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) {s s' : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b)
    (hs' : ∀ a b, a < b → ε (s' a) = ε (s' b) → s' a < s' b) {Λ : Fin n → ℝ} {v : V}
    (h : KHighest (ε ∘ s') (fun a b => E (s' a) (s' b)) Λ v) :
    KHighest (ε ∘ s) (fun a b => E (s a) (s b)) (Λ ∘ s'.symm ∘ s) v := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · have := h1 (s'.symm (s a))
    simpa using this
  · have hlt := hs a b hab he
    have key : s'.symm (s a) < s'.symm (s b) := by
      by_contra hn
      have hle := not_lt.1 hn
      rcases hle.lt_or_eq with hl | he'
      · have := hs' _ _ hl (by simpa using he.symm)
        simp only [Equiv.apply_symm_apply] at this
        exact absurd this (not_lt.2 hlt.le)
      · have := s'.symm.injective he'
        exact absurd this hlt.ne'
    have := h2 _ _ key (by simpa using he)
    simpa using this

/- English proof (translation)
Introduce `n ε X s s' mu mu' h hc h'`. Take `⟨hl, hs, -, v, hv0, hv⟩` from `h`. Take `⟨hl', hs', hmin', v', hv0', hv'⟩` from `h'`. Establish `add : ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ), PI.UpqRep.lowK ε lam + (2 : ℝ) • Formalism.REAL.rhoC ε = lam + Formalism.QuantumDeterminants.rhoStd n` using `fun ε lam => lowK_add ε lam`. Establish `k1` using `kHighest_renumber ε X.E hs hs' hv'`.

Establish `k2` using `kHighest_renumber ε X.E hs' hs hv`. Take `⟨c, hc1, e⟩` from `hc _ v' hv0' k1`. Establish `m2` using `hmin' _ v hv0 k2`. Use `set x := mu + Formalism.QuantumDeterminants.rhoStd n with hx`. Use `set x' := mu' + Formalism.QuantumDeterminants.rhoStd n with hx'`.

Use `set Q : Fin n → ℝ := ∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b with hQ`. Establish `hsx : StrictAnti x` using `strictAnti_add_rho hl.1`. Establish `hsx' : StrictAnti x'` using `strictAnti_add_rho hl'.1`. Establish `r1 : x' ∘ s'.symm ∘ s = x + Q`. Establish `e1 : x = PI.UpqRep.lowK (ε ∘ s) mu + (2 : ℝ) • Formalism.REAL.rhoC (ε ∘ s)` using `(add _ _).symm`.

Establish `e2 : x' = PI.UpqRep.lowK (ε ∘ s') mu' + (2 : ℝ) • Formalism.REAL.rhoC (ε ∘ s')` using `(add _ _).symm`. Use function extensionality and compare the values at `a`. Establish `ea` using `congrFun e a`. Rewrite using `[e1, e2, rhoC_perm s hs, rhoC_perm s' hs']`. Simplify using `only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, Equiv.apply_symm_apply] at ea ⊢`.

Rewrite using `[ea]`. Expand and normalize the polynomial expressions, which then agree. Establish `r2 : x ∘ s.symm ∘ s' = PI.UpqRep.lowK (ε ∘ s) mu ∘ s.symm ∘ s' + (2 : ℝ) • Formalism.REAL.rhoC (ε ∘ s')`. Establish `e1 : x = PI.UpqRep.lowK (ε ∘ s) mu + (2 : ℝ) • Formalism.REAL.rhoC (ε ∘ s)` using `(add _ _).symm`. Rewrite using `[e1, rhoC_perm s hs, rhoC_perm s' hs']`.

Use function extensionality and compare the values at `a`. Simplify using the standard rewrite rules. Establish `m3 : Formalism.REAL.nsq x' ≤ Formalism.REAL.nsq x`. Establish `a1 : Formalism.REAL.nsq x' = PI.UpqRep.vNormSq (ε ∘ s') (PI.UpqRep.lowK (ε ∘ s') mu')`. Rewrite using `[hx', ← add]`.

Both sides reduce to the same expression. Establish `a2 : Formalism.REAL.nsq x = PI.UpqRep.vNormSq (ε ∘ s') (PI.UpqRep.lowK (ε ∘ s) mu ∘ s.symm ∘ s')`. Use `nsq_comp (s.symm * s') x` as an intermediate fact. Establish `e3 : x ∘ ⇑(s.symm * s') = x ∘ s.symm ∘ s'` using `rfl`. Rewrite `this` using `[e3, r2]`.

Rewrite using `[← this]`. Both sides reduce to the same expression. Rewrite using `[a1, a2]`. Conclude with `m2`. Establish `m4 : Formalism.REAL.nsq (x + Q) = Formalism.REAL.nsq x'`.

Rewrite using `[← r1]`. Conclude with `nsq_comp (s'.symm * s) x'`. Establish `h4` using `nsq_add_cone hsx.antitone hc1`. Establish `hQ0 : Q = 0` using `eq_zero_of_nsq (by linarith)`. Rewrite `r1` using `[hQ0, add_zero]`.

Establish `hm : StrictMono (s'.symm * s)` using `fun a b hab => by`. Establish `h5` using `hsx hab`. Rewrite `h5` using `[← r1]`. Conclude with `hsx'.lt_iff_gt.1 h5`. Establish `h6 : s'.symm * s = 1`.

Use `Subsingleton.elim (hm.orderIsoOfSurjective _ (s'.symm * s).surjective) (OrderIso.refl _)` as an intermediate fact. Conclude with `Equiv.ext fun a => DFunLike.congr_fun this a`. Establish `h7 : s = s'`. Use `Equiv.ext fun a => ?_` and prove the remaining obligations. Use `congrArg (fun t : Equiv.Perm (Fin n) => s' (t a)) h6` as an intermediate fact.

Simplify using `using this`. Substitute `h7` using the available equality. Use `⟨rfl, ?_⟩` and prove the remaining obligations. Establish `h8 : x' = x`. Simplify using `using r1`.

Conclude with `(add_right_cancel h8).symm`.
-/
theorem dataUniq : CompanionTheory.RgExh.Fin.DataUniq := by
  intro n ε X s s' mu mu' h hc h'
  obtain ⟨hl, hs, -, v, hv0, hv⟩ := h
  obtain ⟨hl', hs', hmin', v', hv0', hv'⟩ := h'
  have add : ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ),
      PI.UpqRep.lowK ε lam + (2 : ℝ) • Formalism.REAL.rhoC ε = lam + Formalism.QuantumDeterminants.rhoStd n := fun ε lam => lowK_add ε lam
  have k1 := kHighest_renumber ε X.E hs hs' hv'
  have k2 := kHighest_renumber ε X.E hs' hs hv
  obtain ⟨c, hc1, e⟩ := hc _ v' hv0' k1
  have m2 := hmin' _ v hv0 k2
  set x := mu + Formalism.QuantumDeterminants.rhoStd n with hx
  set x' := mu' + Formalism.QuantumDeterminants.rhoStd n with hx'
  set Q : Fin n → ℝ := ∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b with hQ
  have hsx : StrictAnti x := strictAnti_add_rho hl.1
  have hsx' : StrictAnti x' := strictAnti_add_rho hl'.1
  have r1 : x' ∘ s'.symm ∘ s = x + Q := by
    have e1 : x = PI.UpqRep.lowK (ε ∘ s) mu + (2 : ℝ) • Formalism.REAL.rhoC (ε ∘ s) := (add _ _).symm
    have e2 : x' = PI.UpqRep.lowK (ε ∘ s') mu' + (2 : ℝ) • Formalism.REAL.rhoC (ε ∘ s') := (add _ _).symm
    funext a
    have ea := congrFun e a
    rw [e1, e2, rhoC_perm s hs, rhoC_perm s' hs']
    simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, Equiv.apply_symm_apply] at ea ⊢
    rw [ea]; ring
  have r2 : x ∘ s.symm ∘ s' =
      PI.UpqRep.lowK (ε ∘ s) mu ∘ s.symm ∘ s' + (2 : ℝ) • Formalism.REAL.rhoC (ε ∘ s') := by
    have e1 : x = PI.UpqRep.lowK (ε ∘ s) mu + (2 : ℝ) • Formalism.REAL.rhoC (ε ∘ s) := (add _ _).symm
    rw [e1, rhoC_perm s hs, rhoC_perm s' hs']
    funext a
    simp
  have m3 : Formalism.REAL.nsq x' ≤ Formalism.REAL.nsq x := by
    have a1 : Formalism.REAL.nsq x' =
        PI.UpqRep.vNormSq (ε ∘ s') (PI.UpqRep.lowK (ε ∘ s') mu') := by
      rw [hx', ← add]; rfl
    have a2 : Formalism.REAL.nsq x = PI.UpqRep.vNormSq (ε ∘ s')
        (PI.UpqRep.lowK (ε ∘ s) mu ∘ s.symm ∘ s') := by
      have := nsq_comp (s.symm * s') x
      have e3 : x ∘ ⇑(s.symm * s') = x ∘ s.symm ∘ s' := rfl
      rw [e3, r2] at this
      rw [← this]; rfl
    rw [a1, a2]; exact m2
  have m4 : Formalism.REAL.nsq (x + Q) = Formalism.REAL.nsq x' := by
    rw [← r1]
    exact nsq_comp (s'.symm * s) x'
  have h4 := nsq_add_cone hsx.antitone hc1
  have hQ0 : Q = 0 := eq_zero_of_nsq (by linarith)
  rw [hQ0, add_zero] at r1
  have hm : StrictMono (s'.symm * s) := fun a b hab => by
    have h5 := hsx hab
    rw [← r1] at h5
    exact hsx'.lt_iff_gt.1 h5
  have h6 : s'.symm * s = 1 := by
    have := Subsingleton.elim (hm.orderIsoOfSurjective _ (s'.symm * s).surjective) (OrderIso.refl _)
    exact Equiv.ext fun a => DFunLike.congr_fun this a
  have h7 : s = s' := by
    refine Equiv.ext fun a => ?_
    have := congrArg (fun t : Equiv.Perm (Fin n) => s' (t a)) h6
    simpa using this
  subst h7
  refine ⟨rfl, ?_⟩
  have h8 : x' = x := by
    simpa using r1
  exact (add_right_cancel h8).symm

end GlobalTheory.CompanionTheory.LowestData
