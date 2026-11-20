import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementF
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.FinalA

noncomputable section
open scoped BigOperators
open NumberField

namespace Formalism.L2.Th1.GD

open Formalism.L2.Th1.H (cmL CmOK matH stdH stdLat blk4 pow4 imgLat relIdx IsIsom)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

/- English proof (translation)
Introduce `p _ E _ _ φ y`. Take `⟨P, hP, hPx⟩` from `RingOfIntegers.isIntegral_coe y`. Establish `hx' : IsIntegral (NormedField.valuation (K` using `ℂ_[p])).integer (φ (y : E)) := by`. Use `⟨P.map (Int.castRingHom _), hP.map _, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_map]`.

Establish `h` using `congrArg φ hPx`. Rewrite `h` using `[Polynomial.hom_eval₂, map_zero]`. Rewrite using `[← h]`. Use `congr 1`. Conclude with `Subsingleton.elim _ _`.

Establish `h` using `(Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))).mem_of_integral hx'`. Rewrite `h` using `[Valuation.mem_integer_iff, NormedField.valuation_apply]`. Conclude with `h` after adjusting the coercions.
-/
theorem IntNorm_proof : IntNorm := by
  intro p _ E _ _ φ y
  obtain ⟨P, hP, hPx⟩ := RingOfIntegers.isIntegral_coe y
  have hx' : IsIntegral (NormedField.valuation (K := ℂ_[p])).integer (φ (y : E)) := by
    refine ⟨P.map (Int.castRingHom _), hP.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have h := congrArg φ hPx
    rw [Polynomial.hom_eval₂, map_zero] at h
    rw [← h]
    congr 1
    exact Subsingleton.elim _ _
  have h := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))).mem_of_integral hx'
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

/- English proof (translation)
Introduce `a b c d ha hd lam hlam hcm n _ _ h Λ g hg p _ ι hidx J _ v hv H _ _ N0 N1 A u hA Xo T T' chi chi' hadj hpres hchi' hT hT' hsep hnorm`. Establish `hth0 : ι (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) ≠ 0`. Establish `h1 : Complex.I * ((Real.sqrt d : ℝ) : ℂ) ≠ 0`. Use `mul_ne_zero Complex.I_ne_zero ?_` and prove the remaining obligations. Establish `h2 : (0 : ℝ) < Real.sqrt d` using `Real.sqrt_pos.2 (by exact_mod_cast hd)`.

Conclude with `h2.ne'` after adjusting the coercions. Conclude with `(map_ne_zero_iff ι ι.injective).2 h1`. Generalize the expression as in `hth : ι (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) = th at hth0 hnorm ⊢`. Establish `hBx` using `fun x y => hB a b c d ha hd lam hlam hcm n h Λ g hg p ι hidx J v hv (fun j => A j x) (fun j => A j y) (fun j => hA j x) (fun j => hA j y)`. Rewrite `hBx` using `[hth]`.

Take `⟨BB, hBB⟩ : ∃ BB : ((Bool × H) × Fin N0 × Fin N1) → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p], ∀ x y, BB x y = ∑ j, ∑ k, A j x * ι (hOK (cmL a b d ha hd lam hlam) h (v j) (v k)) * A k y` from `⟨_, fun _ _ => rfl⟩`. Simplify using `only [← hBB] at hBx hnorm`. Establish `hcomp : ∀ e x y, ‖(chi e x.1 - chi' e y.1) * BB x y‖ ≤ ‖th‖`. Introduce `e x y`. Take `⟨ε, hε, heq⟩` from `hC a b c d ha hd lam hlam hcm n h Λ g hg p ι hidx J v hv (T e) (T' e) (hadj e) (hpres e) (fun j => A j x) (fun j => A j y) (chi e x.1) (chi' e y.1) (fun j => hA j x) (fun j => hA j y) (hchi' e y.1) (hT e x) (hT' e y)`.

Rewrite using `[hBB, heq, hth, norm_mul]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) hε`. Take `⟨q1, hq1, hsplit⟩` from `Formalism.L2.Th1.G.eigenSplit ℂ_[p] ((Bool × H) × Fin N0 × Fin N1) (Bool × H) Xo (fun x => x.1) (fun τ => (!τ.1, τ.2)) BB th chi chi' hth0 (fun x y => (hBx x y).1) hcomp hsep`. Establish `main : ∀ x y, ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ BB x y = (if x.1.2 = y.1.2 ∧ x.2 = y.2 ∧ x.1.1 ≠ y.1.1 then u x.1.2 else 0) + th * e`. Introduce `x y`.

Distinguish the cases in `hxy : y.1 = (!x.1.1, x.1.2)`. Take `⟨⟨bx, t⟩, ab⟩` from `x`. Take `⟨⟨by', t'⟩, ab'⟩` from `y`. Simplify using `only [Prod.mk.injEq] at hxy`. Take `⟨rfl, rfl⟩` from `hxy`.

Consider the cases of `bx`. Take `⟨e, he, heq⟩` from `hnorm t' ab ab'`. Use `⟨e, he, ?_⟩` and prove the remaining obligations. Simplify using `only [Bool.not_false]`. Rewrite using `[heq]`.

Simplify using the standard rewrite rules. Take `⟨e, he, heq⟩` from `hnorm t' ab' ab`. Take `⟨e2, he2, hsym⟩` from `(hBx ((true, t'), ab) ((false, t'), ab')).2.1`. Use `⟨e + e2, (IsUltrametricDist.norm_add_le_max _ _).trans (max_le he he2), ?_⟩` and prove the remaining obligations. Simplify using `only [Bool.not_true]`.

Rewrite using `[sub_eq_iff_eq_add.1 hsym, heq]`. Simplify using `only [eq_comm (a := ab') (b := ab)]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `hsplit x y`.

Simplify using `only [if_neg hxy, zero_add] at h1`. Use `⟨q1 x y, hq1 x y, ?_⟩` and prove the remaining obligations. Rewrite using `[if_neg, zero_add]`. Conclude with `h1`. Introduce and unpack `⟨h2, _, h3⟩`.

Apply `hxy` to reduce the goal to its premises. Use `Prod.ext ?_ h2.symm` and prove the remaining obligations. Simplify using `only`. Use `revert h3`. Apply the tactic sequence `cases x.1.1 <;> cases y.1.1 <;> simp`.

Use `choose q hq hqe using main`. Use `⟨q, hv, hA, hq, ?_⟩` and prove the remaining obligations. Introduce `x y`. Conclude with `(hBB x y).symm.trans (hqe x y)`.
-/
theorem EigenFrame_of (hB : GramBasic) (hC : EigenCompat) : EigenFrame := by
  intro a b c d ha hd lam hlam hcm n _ _ h Λ g hg p _ ι hidx J _ v hv H _ _ N0 N1 A u hA Xo T T' chi chi'
    hadj hpres hchi' hT hT' hsep hnorm
  have hth0 : ι (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) ≠ 0 := by
    have h1 : Complex.I * ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by
      refine mul_ne_zero Complex.I_ne_zero ?_
      have h2 : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
      exact_mod_cast h2.ne'
    exact (map_ne_zero_iff ι ι.injective).2 h1
  generalize hth : ι (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) = th at hth0 hnorm ⊢
  have hBx := fun x y => hB a b c d ha hd lam hlam hcm n h Λ g hg p ι hidx J v hv
    (fun j => A j x) (fun j => A j y) (fun j => hA j x) (fun j => hA j y)
  rw [hth] at hBx
  obtain ⟨BB, hBB⟩ : ∃ BB : ((Bool × H) × Fin N0 × Fin N1) → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p],
      ∀ x y, BB x y = ∑ j, ∑ k, A j x * ι (hOK (cmL a b d ha hd lam hlam) h (v j) (v k)) * A k y :=
    ⟨_, fun _ _ => rfl⟩
  simp only [← hBB] at hBx hnorm
  have hcomp : ∀ e x y, ‖(chi e x.1 - chi' e y.1) * BB x y‖ ≤ ‖th‖ := by
    intro e x y
    obtain ⟨ε, hε, heq⟩ := hC a b c d ha hd lam hlam hcm n h Λ g hg p ι hidx J v hv (T e) (T' e) (hadj e)
      (hpres e) (fun j => A j x) (fun j => A j y) (chi e x.1) (chi' e y.1) (fun j => hA j x)
      (fun j => hA j y) (hchi' e y.1) (hT e x) (hT' e y)
    rw [hBB, heq, hth, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hε
  obtain ⟨q1, hq1, hsplit⟩ := Formalism.L2.Th1.G.eigenSplit ℂ_[p] ((Bool × H) × Fin N0 × Fin N1) (Bool × H) Xo
    (fun x => x.1) (fun τ => (!τ.1, τ.2)) BB th chi chi' hth0 (fun x y => (hBx x y).1) hcomp hsep
  have main : ∀ x y, ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧
      BB x y = (if x.1.2 = y.1.2 ∧ x.2 = y.2 ∧ x.1.1 ≠ y.1.1 then u x.1.2 else 0) + th * e := by
    intro x y
    by_cases hxy : y.1 = (!x.1.1, x.1.2)
    · obtain ⟨⟨bx, t⟩, ab⟩ := x
      obtain ⟨⟨by', t'⟩, ab'⟩ := y
      simp only [Prod.mk.injEq] at hxy
      obtain ⟨rfl, rfl⟩ := hxy
      cases bx
      · obtain ⟨e, he, heq⟩ := hnorm t' ab ab'
        refine ⟨e, he, ?_⟩
        simp only [Bool.not_false]
        rw [heq]
        simp
      · obtain ⟨e, he, heq⟩ := hnorm t' ab' ab
        obtain ⟨e2, he2, hsym⟩ := (hBx ((true, t'), ab) ((false, t'), ab')).2.1
        refine ⟨e + e2, (IsUltrametricDist.norm_add_le_max _ _).trans (max_le he he2), ?_⟩
        simp only [Bool.not_true]
        rw [sub_eq_iff_eq_add.1 hsym, heq]
        simp only [eq_comm (a := ab') (b := ab)]
        simp
        ring
    · have h1 := hsplit x y
      simp only [if_neg hxy, zero_add] at h1
      refine ⟨q1 x y, hq1 x y, ?_⟩
      rw [if_neg, zero_add]
      · exact h1
      · rintro ⟨h2, _, h3⟩
        apply hxy
        refine Prod.ext ?_ h2.symm
        simp only
        revert h3
        cases x.1.1 <;> cases y.1.1 <;> simp
  choose q hq hqe using main
  refine ⟨q, hv, hA, hq, ?_⟩
  intro x y
  exact (hBB x y).symm.trans (hqe x y)

/- English proof (translation)
Introduce `a b c d ha hd lam hlam hcm n _ _ h Λ g hg p _ ι hidx J _ v hv hpd E _ _ _ cE s δ hδ hcδ hsδ hcc hss hsc H _ _ emb hinj hembδ hembt hKur act hadj hpres N0 N1 A u hA heig hnorm`. Establish `hp2 : p ≠ 2`. Take `⟨_, _, h8, _⟩` from `hcm`. Use linear arithmetic over natural numbers and integers. Use `hF a b c d ha hd lam hlam hcm n h Λ g hg p ι hidx J v hv H N0 N1 A u hA {ee : 𝓞 E × 𝓞 E // (ee.2 : E) = cE (ee.1 : E)} (fun ee => act ee.1.1) (fun ee => act ee.1.2) (fun ee τ => emb τ (ee.1.1 : E)) (fun ee τ => emb τ (ee.1.2 : E)) ?_ ?_ ?_ ?_ ?_ ?_ hnorm` and prove the remaining obligations.

Introduce `ee x y`. Conclude with `hadj ee.1.1 ee.1.2 ee.2 x y`. Introduce `ee`. Conclude with `hpres ee.1.2`. Introduce `ee τ`.

Conclude with `hN p E (emb τ) ee.1.2`. Introduce `ee x i`. Conclude with `heig ee.1.1 x i`. Introduce `ee x i`. Conclude with `heig ee.1.2 x i`.

Introduce `τ ρ hρ`. Take `⟨e, he⟩` from `hS p hp2 E cE s δ hδ hcδ hsδ hcc hss hsc H emb hinj hembδ hembt hKur τ ρ hρ`. Establish `hint : IsIntegral ℤ (cE (e : E))` using `map_isIntegral_int cE (RingOfIntegers.isIntegral_coe e)`. Conclude with `⟨⟨(e, ⟨cE (e : E), hint⟩), rfl⟩, he⟩`.
-/
theorem EigenFrameE_of (hF : EigenFrame) (hS : SepPairs) (hN : IntNorm) : EigenFrameE := by
  intro a b c d ha hd lam hlam hcm n _ _ h Λ g hg p _ ι hidx J _ v hv hpd E _ _ _ cE s δ hδ hcδ hsδ hcc hss
    hsc H _ _ emb hinj hembδ hembt hKur act hadj hpres N0 N1 A u hA heig hnorm
  have hp2 : p ≠ 2 := by
    obtain ⟨_, _, h8, _⟩ := hcm
    omega
  refine hF a b c d ha hd lam hlam hcm n h Λ g hg p ι hidx J v hv H N0 N1 A u hA
    {ee : 𝓞 E × 𝓞 E // (ee.2 : E) = cE (ee.1 : E)} (fun ee => act ee.1.1) (fun ee => act ee.1.2)
    (fun ee τ => emb τ (ee.1.1 : E)) (fun ee τ => emb τ (ee.1.2 : E)) ?_ ?_ ?_ ?_ ?_ ?_ hnorm
  · intro ee x y
    exact hadj ee.1.1 ee.1.2 ee.2 x y
  · intro ee
    exact hpres ee.1.2
  · intro ee τ
    exact hN p E (emb τ) ee.1.2
  · intro ee x i
    exact heig ee.1.1 x i
  · intro ee x i
    exact heig ee.1.2 x i
  · intro τ ρ hρ
    obtain ⟨e, he⟩ := hS p hp2 E cE s δ hδ hcδ hsδ hcc hss hsc H emb hinj hembδ hembt hKur τ ρ hρ
    have hint : IsIntegral ℤ (cE (e : E)) := map_isIntegral_int cE (RingOfIntegers.isIntegral_coe e)
    exact ⟨⟨(e, ⟨cE (e : E), hint⟩), rfl⟩, he⟩

/- English proof (translation)
Introduce `O L L' _ _ _ _ _ hL' N0 N1 e es e' es' h0l h0r hdual Eab Es hE1 hE2 hS1 hS2 x y`. Take `⟨a, b⟩` from `x`. Take `⟨a', b'⟩` from `y`. Simplify using `only [hE1, hE2, hS1, hS2, h0l, Finset.sum_const_zero, add_zero]`. Rewrite using `[Finset.sum_eq_single a]`.

Rewrite using `[if_pos rfl]`. Distinguish the cases in `h : a' = a`. Substitute `h` using the available equality. Rewrite using `[if_pos rfl, hdual]`. Simplify using the standard rewrite rules.

Rewrite using `[if_neg h, h0r, if_neg]`. Introduce `h2`. Conclude with `h (Prod.ext_iff.1 h2).1.symm`. Introduce `c _ hc`. Rewrite using `[if_neg (Ne.symm hc), h0l]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ a) h`.
-/
theorem HomGram_proof : HomGram := by
  intro O L L' _ _ _ _ _ hL' N0 N1 e es e' es' h0l h0r hdual Eab Es hE1 hE2 hS1 hS2 x y
  obtain ⟨a, b⟩ := x
  obtain ⟨a', b'⟩ := y
  simp only [hE1, hE2, hS1, hS2, h0l, Finset.sum_const_zero, add_zero]
  rw [Finset.sum_eq_single a]
  · rw [if_pos rfl]
    by_cases h : a' = a
    · subst h
      rw [if_pos rfl, hdual]
      simp
    · rw [if_neg h, h0r, if_neg]
      intro h2
      exact h (Prod.ext_iff.1 h2).1.symm
  · intro c _ hc
    rw [if_neg (Ne.symm hc), h0l]
  · intro h
    exact absurd (Finset.mem_univ a) h

end Formalism.L2.Th1.GD
