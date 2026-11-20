import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary

noncomputable section

namespace GlobalTheory.JumpDictRec

open GlobalTheory.JumpDictionaryFoundation

/- English proof (translation)
Introduce `D hW hB hG hC i τ ρ b hτ`. Establish `hs` using `shift_embOver D ρ b`. Use `⟨shift D (embOver D ρ b), ?_, fun w hw => ?_⟩` and prove the remaining obligations. Apply `Multiset.map_injective (f := fun q : ℚ => (q : ℂ)) Rat.cast_injective` to reduce the goal to its premises. Rewrite using `[Multiset.map_map, Multiset.map_map]`.

Establish `e0` using `D.naut.locAut_hodgeTateWeightsLevelZero_def i τ`. Rewrite `e0` using `[hτ]`. Establish `e1 : (D.naut.locAutHodgeTateWeightsLevelZero i τ).map ((fun q : ℚ => (q : ℂ)) ∘ fun n : ℤ => (n : ℚ)) = (D.naut.locAutHodgeTateWeightsLevelZero i τ).map (fun n : ℤ => (n : ℂ))` using `Multiset.map_congr rfl fun n _ => by simp`. Rewrite using `[e1, e0]`. Consider the cases of `b`.

Rewrite using `[(hW i ρ).1, Multiset.map_map]`. Use `Multiset.map_congr rfl fun p _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp, sgnOf, hs]`. Use `push_cast`. Evaluate the numerical expressions.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[(hW i ρ).2, Multiset.map_map]`. Use `Multiset.map_congr rfl fun p _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp, sgnOf, hs]`. Use `push_cast`.

Evaluate the numerical expressions. Expand and normalize the polynomial expressions, which then agree. Establish `ht : 1 ≤ D.R.t`. Take `⟨u, v, -, hv, -⟩` from `exists_halves D.R`. Use linear arithmetic over natural numbers and integers.

Establish `hz : ∀ φ, ∃ z : ℤ, (D.naut.infG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) φ).map (· + (blockExp D 1 : ℂ)) = {(z : ℂ)}`. Introduce `φ`. Take `⟨ρ', b', rfl⟩` from `exists_embOver D φ`. Take `⟨a, ha⟩` from `firstJump_int D i ρ' b'`. Use `⟨-a, ?_⟩` and prove the remaining obligations.

Rewrite using `[inf_block D hB, ha]`. Use `push_cast`. Simplify using the standard rewrite rules. Use `choose z hz using hz`. Take `⟨r, hrc, hrf, hrd, hrj⟩` from `hG i _ _ z hz`.

Establish `hr : r = mapRep (iotaOQ D.nd D.naut i) (chiGL D i 1)`. Establish `h` using `eq_of_frob D.nd hC i (a := fun g => ((r g : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0) (b := fun g => iotaOQ D.nd D.naut i ((D.nd.chi i 1 g : (D.nd.O i)ˣ) : D.nd.O i)) ((continuous_apply 0).comp ((continuous_apply 0).comp hrc)) ((continuous_iot …`. Establish `e1` using `hrf v hv.2.1 (D.naut.chi_mu i v hv).1 B σ hB' hσ`. Rewrite `e1` using `[chi_frob D i 1 le_rfl ht v hv B σ hB' hσ, Multiset.singleton_inj]`. Conclude with `((D.naut.iotaQC i).injective e1).symm`.

Use extensionality with `g a c`. Take `rfl : a = 0` from `Subsingleton.elim _ _`. Take `rfl : c = 0` from `Subsingleton.elim _ _`. Use `(congrFun h g).trans ?_` and prove the remaining obligations. Rewrite using `[← chiGL_apply D i 1 g 0 0]`.

Both sides reduce to the same expression. Substitute `hr` using the available equality. Use `⟨hrd w hw, ?_⟩` and prove the remaining obligations. Establish `hq : firstJump D i ρ b + (((1 : ℕ) : ℚ) - 1) = ((-z (embOver D ρ b) : ℤ) : ℚ)`. Establish `e` using `(inf_block D hB i 1 ρ b).symm.trans (hz _)`.

Rewrite `e` using `[Multiset.singleton_inj]`. Establish `e' : -(firstJump D i ρ b + (((1 : ℕ) : ℚ) - 1)) = (z (embOver D ρ b) : ℚ)` using `by exact_mod_cast e`. Rewrite using `[Int.cast_neg, ← e', neg_neg]`. Rewrite using `[hrj, hτ, Multiset.map_singleton, ← hq, hs]`. Use `congr 1`.

Consider the cases of `b`. Simplify using `only [firstJump, sgnOf, Ranks.nV]`. Use `push_cast`. Evaluate the numerical expressions. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [firstJump, sgnOf, Ranks.nV]`. Use `push_cast`. Evaluate the numerical expressions. Expand and normalize the polynomial expressions, which then agree.
-/
theorem main : ∀ D : D7, WeightParam D → BlockCharParam D → GlobalTheory.JumpDictionaryFoundation.AlgebraicCharacter_at D →
    GlobalTheory.TwSys.Cheb → ∀ (i : D.nd.Loc) (τ : D.host.E →+* Qbar (D.nd.l i)) (ρ : D.what₂.Tau) (b : Bool),
    (D.naut.iotaQC i).toRingHom.comp τ = embOver D ρ b → ∃ cτ : ℤ,
      (D.naut.locAutHodgeTateWeightsLevelZero i τ).map (fun n : ℤ => (n : ℚ)) = (PP D i ρ).map (fun p => sgnOf true b * p + cτ) ∧
      ∀ w ∈ placesOver D.host.E (D.nd.l i),
        D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) (chiGL D i 1)) w ∧
        (D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) (chiGL D i 1)) τ).map (fun n : ℤ => (n : ℚ)) =
          {sgnOf true b * (-(D.hc ρ).e (liftIdx D i)) - ((D.R.t : ℚ) - 1) / 2 + cτ} := by
  intro D hW hB hG hC i τ ρ b hτ
  have hs := shift_embOver D ρ b
  refine ⟨shift D (embOver D ρ b), ?_, fun w hw => ?_⟩
  · apply Multiset.map_injective (f := fun q : ℚ => (q : ℂ)) Rat.cast_injective
    rw [Multiset.map_map, Multiset.map_map]
    have e0 := D.naut.locAut_hodgeTateWeightsLevelZero_def i τ
    rw [hτ] at e0
    have e1 : (D.naut.locAutHodgeTateWeightsLevelZero i τ).map ((fun q : ℚ => (q : ℂ)) ∘ fun n : ℤ => (n : ℚ)) =
        (D.naut.locAutHodgeTateWeightsLevelZero i τ).map (fun n : ℤ => (n : ℂ)) :=
      Multiset.map_congr rfl fun n _ => by simp
    rw [e1, e0]
    cases b
    · rw [(hW i ρ).1, Multiset.map_map]
      refine Multiset.map_congr rfl fun p _ => ?_
      simp only [Function.comp, sgnOf, hs]
      push_cast
      norm_num
      ring
    · rw [(hW i ρ).2, Multiset.map_map]
      refine Multiset.map_congr rfl fun p _ => ?_
      simp only [Function.comp, sgnOf, hs]
      push_cast
      norm_num
      ring
  · have ht : 1 ≤ D.R.t := by
      obtain ⟨u, v, -, hv, -⟩ := exists_halves D.R
      omega
    have hz : ∀ φ, ∃ z : ℤ, (D.naut.infG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) φ).map
        (· + (blockExp D 1 : ℂ)) = {(z : ℂ)} := by
      intro φ
      obtain ⟨ρ', b', rfl⟩ := exists_embOver D φ
      obtain ⟨a, ha⟩ := firstJump_int D i ρ' b'
      refine ⟨-a, ?_⟩
      rw [inf_block D hB, ha]
      push_cast
      simp
    choose z hz using hz
    obtain ⟨r, hrc, hrf, hrd, hrj⟩ := hG i _ _ z hz
    have hr : r = mapRep (iotaOQ D.nd D.naut i) (chiGL D i 1) := by
      have h := eq_of_frob D.nd hC i
        (a := fun g => ((r g : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0)
        (b := fun g => iotaOQ D.nd D.naut i ((D.nd.chi i 1 g : (D.nd.O i)ˣ) : D.nd.O i))
        ((continuous_apply 0).comp ((continuous_apply 0).comp hrc))
        ((continuous_iotaOQ D i w hw).comp (D.nd.chi_cont i 1)) fun v hv B σ hB' hσ => by
          have e1 := hrf v hv.2.1 (D.naut.chi_mu i v hv).1 B σ hB' hσ
          rw [chi_frob D i 1 le_rfl ht v hv B σ hB' hσ, Multiset.singleton_inj] at e1
          exact ((D.naut.iotaQC i).injective e1).symm
      ext g a c
      obtain rfl : a = 0 := Subsingleton.elim _ _
      obtain rfl : c = 0 := Subsingleton.elim _ _
      refine (congrFun h g).trans ?_
      rw [← chiGL_apply D i 1 g 0 0]
      rfl
    subst hr
    refine ⟨hrd w hw, ?_⟩
    have hq : firstJump D i ρ b + (((1 : ℕ) : ℚ) - 1) = ((-z (embOver D ρ b) : ℤ) : ℚ) := by
      have e := (inf_block D hB i 1 ρ b).symm.trans (hz _)
      rw [Multiset.singleton_inj] at e
      have e' : -(firstJump D i ρ b + (((1 : ℕ) : ℚ) - 1)) = (z (embOver D ρ b) : ℚ) := by exact_mod_cast e
      rw [Int.cast_neg, ← e', neg_neg]
    rw [hrj, hτ, Multiset.map_singleton, ← hq, hs]
    congr 1
    cases b
    · simp only [firstJump, sgnOf, Ranks.nV]
      push_cast
      norm_num
      ring
    · simp only [firstJump, sgnOf, Ranks.nV]
      push_cast
      norm_num
      ring

end GlobalTheory.JumpDictRec

end
