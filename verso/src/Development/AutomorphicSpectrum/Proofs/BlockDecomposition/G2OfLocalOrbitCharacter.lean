import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.GlobalComplexCoefficients
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.WeylSplitting.WeylSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterLaplaceFactorisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResultantFactorsProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaConstantMulOfCoprimeEllipticPolynomials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportOfStTw2NeZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemProdOfMemTsupport

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.resultantFactorHypotheses

/- English proof (translation)
Establish `hR0 : resultant P₁ P₂ ≠ 0` using `GlobalTheory.ProdForm.resNe E P₁ P₂ h₁.1 h₂.1 hc`. Use `set R := resultant P₁ P₂ with hR`. Use `set c := IsCMField.complexConj E with hcdef`. Establish `hcR0 : c R ≠ 0` using `(map_ne_zero c).2 hR0`. Set `k : Eˣ` to `Units.mk0 R hR0`.

Set `kc : Eˣ` to `Units.map (MonoidHomClass.toMonoidHom c) k`. Use `set d : E := ((-1) ^ a * P₁.coeff 0) ^ b * ((-1) ^ b * P₂.coeff 0) ^ a with hd`. Establish `hH : c R * d = (-1) ^ (a * b) * R` using `GlobalTheory.T.conj_resultant_of_ell_polys E a b P₁ P₂ h₁ h₂`. Establish `hsq : ((-1 : E) ^ (a * b)) * (-1) ^ (a * b) = 1`. Rewrite using `[← mul_pow, neg_one_mul, neg_neg, one_pow]`.

Establish `hd1 : (-1) ^ (a * b) * d = R * (c R)⁻¹`. Rewrite using `[eq_mul_inv_iff_mul_eq₀ hcR0]`. Take the linear combination `(-1 : E) ^ (a * b) * hH + R * hsq`. Establish `hd0 : d ≠ 0`. Introduce `h0`.

Rewrite `hH` using `[h0, mul_zero]`. Conclude with `hR0 (by simpa using hH.symm)`. Establish `hd2 : R ^ 2 / d = (-1) ^ (a * b) * (R * c R)`. Rewrite using `[div_eq_iff hd0]`. Take the linear combination `(-(-1 : E) ^ (a * b) * R) * hH - R ^ 2 * hsq`.

Set `f : Pl E → ℂ` to `fun w => ((μ.locK w k : ℂˣ) : ℂ) * absHalf w (algebraMap E (w.adicCompletion E) R)`. Take `⟨hfin1, hprod1⟩` from `GlobalTheory.T.heckeChar_finprod_locK_mul_inf_eq_one E μ k`. Take `⟨hfin2, hprod2⟩` from `GlobalTheory.T.prodFormula_sqrt_normalizedAbsValues_CMField E R hR0`. Establish `hfin1' : (Function.mulSupport fun w : Pl E => ((μ.locK w k : ℂˣ) : ℂ)).Finite`. Use `hfin1.subset fun w hw => ?_` and prove the remaining obligations.

Introduce `h1`. Apply `hw` to reduce the goal to its premises. Simplify using `[h1]`. Establish `hfin : (Function.mulSupport f).Finite` using `(hfin1'.union hfin2).subset (Function.mulSupport_mul _ _)`. Establish `hloc : ∀ w ∈ S, delta w (μ.loc w) (atPl w P₁) (atPl w P₂) = ∏ᶠ x ∈ {x : Pl E | x.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))}, f x`.

Introduce `w _`. Establish `hn₁ : (atPl w P₁).natDegree = a`. Rewrite using `[atPl, Polynomial.natDegree_map_eq_of_injective (algebraMap E _).injective]`. Conclude with `h₁.2.1`. Establish `hn₂ : (atPl w P₂).natDegree = b`.

Rewrite using `[atPl, Polynomial.natDegree_map_eq_of_injective (algebraMap E _).injective]`. Conclude with `h₂.2.1`. Establish `hres : resultant (atPl w P₁) (atPl w P₂) = algebraMap E (w.adicCompletion E) R` using `GlobalTheory.ProdForm.resMap _ _ _ _ _`. Establish `hdl : ((-1) ^ a * (atPl w P₁).coeff 0) ^ b * ((-1) ^ b * (atPl w P₂).coeff 0) ^ a = algebraMap E (w.adicCompletion E) d`. Simplify using `[atPl, Polynomial.coeff_map, hd]`.

Take `⟨hAm, hAn⟩` from `GlobalTheory.T.absHalf_mul_and_absHalf_neg_one E w`. Establish `hA0 : ∀ x : E, x ≠ 0 → algebraMap E (w.adicCompletion E) x ≠ 0` using `fun x hx => (_root_.map_ne_zero _).2 hx`. Distinguish the cases in `hsp : IsSplitAt w`. Take `⟨u, hu, huw⟩` from `hsp`. Establish `hfib : {x : Pl E | x.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))} = {w, u}`.

Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion. Conclude with `fun hx => GlobalTheory.T.eq_or_eq_of_under_maximalRealSubfield_eq_CMField E w u x hu huw hx`. Introduce and unpack `(rfl | rfl)`.

Both sides reduce to the same expression. Conclude with `huw`. Rewrite using `[hfib, finprod_mem_pair (Ne.symm hu)]`. Establish `hdelta : delta w (μ.loc w) (atPl w P₁) (atPl w P₂) = (if h : (-1) ^ (a * b) * algebraMap E (w.adicCompletion E) d ≠ 0 then (μ.loc w (Units.mk0 _ h) : ℂ) else 0) * absHalf w (algebraMap E (w.adicCompletion E) R ^ 2 / algebraMap E (w.adicCompletion E) d)`. Unfold `delta`.

Rewrite using `[hres]`. Simplify using `only [hn₁, hn₂, hdl]`. Rewrite using `[if_pos ⟨u, hu, huw⟩]`. Establish `hne : (-1) ^ (a * b) * algebraMap E (w.adicCompletion E) d ≠ 0` using `mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (hA0 d hd0)`. Rewrite using `[hdelta, dif_pos hne]`.

Establish `hunit : (Units.mk0 _ hne : (w.adicCompletion E)ˣ) = atFin w (k * kc⁻¹)`. Apply `Units.ext` to reduce the goal to its premises. Establish `e1 : ((atFin w (k * kc⁻¹) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = algebraMap E (w.adicCompletion E) (R * (c R)⁻¹)`. Simplify using `[atFin, kc, k, map_inv₀]`. Rewrite using `[e1, ← hd1, Units.val_mk0]`.

Simplify using `[map_mul, map_pow]`. Establish `hchar : ((μ.loc w (Units.mk0 _ hne) : ℂˣ) : ℂ) = ((μ.locK w k : ℂˣ) : ℂ) * ((μ.locK u k : ℂˣ) : ℂ)`. Rewrite using `[hunit]`. Establish `h1` using `GlobalTheory.T.unitaryHeckeCharCM_splitPlace_mul_conjPlace_eq_one E μ e hμ w u hu huw k`. Establish `h2 : μ.locK w kc = (μ.locK u k)⁻¹` using `eq_inv_of_mul_eq_one_right h1`.

Express the relevant statement in the definitionally equal form `((μ.locK w (k * kc⁻¹) : ℂˣ) : ℂ) = _`. Rewrite using `[map_mul, map_inv, h2, inv_inv, Units.val_mul]`. Establish `habs : absHalf w (algebraMap E (w.adicCompletion E) R ^ 2 / algebraMap E (w.adicCompletion E) d) = absHalf w (algebraMap E (w.adicCompletion E) R) * absHalf u (algebraMap E (u.adicCompletion E) R)`. Rewrite using `[← map_pow, ← map_div₀, hd2, map_mul, map_mul, map_pow, map_neg, map_one, hAm _ _ (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (mul_ne_zero (hA0 R hR0) (hA0 _ hcR0)), hAm _ _ (hA0 R hR0) (hA0 _ hcR0), GlobalTheory.T.absHalf_conjugatePlace_eq E w u hu huw R]`. Establish `hpow : ∀ n : ℕ, absHalf w ((-1 : w.adicCompletion E) ^ n) = 1`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Establish `h` using `hAm (-1) (-1) (neg_ne_zero.2 one_ne_zero) (neg_ne_zero.2 one_ne_zero)`. Rewrite `h` using `[neg_one_mul, neg_neg, hAn, one_mul]`.

Rewrite using `[pow_zero, h]`. Consider the case `succ n ih`. Rewrite using `[pow_succ, hAm _ _ (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (neg_ne_zero.2 one_ne_zero), ih, hAn, one_mul]`. Rewrite using `[hpow, one_mul]`. Rewrite using `[hchar, habs]`.

Simplify using `only [f]`. Expand and normalize the polynomial expressions, which then agree. Establish `hfib : {x : Pl E | x.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))} = {w}`. Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq, Set.mem_singleton_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Assume the negation of the conclusion as `hxw`. Conclude with `hsp ⟨x, hxw, hx⟩`. Introduce and unpack `rfl`.

Both sides reduce to the same expression. Rewrite using `[hfib, finprod_mem_singleton]`. Unfold `delta`. Rewrite using `[hres]`. Simplify using `only [hn₁, hn₂, hdl]`.

Rewrite using `[if_neg hsp]`. Simplify using `only [f]`. Rewrite using `[GlobalTheory.T.unitaryHeckeCharCM_locK_nonsplit_eq_neg_one_pow E μ e hμ w hsp k]`. Both sides reduce to the same expression. Establish `hS' : ∀ x : Pl E, ∃! s, s ∈ S ∧ s.under (𝓞 (maximalRealSubfield E)) = x.under (𝓞 (maximalRealSubfield E))` using `hS`.

Establish `hfib` using `GlobalTheory.T.finprod_eq_finprod_mem_fibres_of_section' (fun x : Pl E => x.under (𝓞 (maximalRealSubfield E))) S f hS' hfin`. Rewrite using `[finprod_mem_congr rfl hloc, ← hfib]`. Establish `hinf : ∀ v : InfinitePlace E, resultant (P₁.map v.embedding) (P₂.map v.embedding) = v.embedding R` using `fun v => GlobalTheory.ProdForm.resMap _ _ _ _ _`. Simplify using `only [hinf]`. Establish `hi` using `GlobalTheory.T.unitaryHeckeCharCM_infinityComponent_globalUnit E μ e hμ k`.

Simplify using `only [k, Units.val_mk0] at hi`. Rewrite using `[Finset.prod_mul_distrib, ← hi]`. Establish `hsplitf : ∏ᶠ x, f x = (∏ᶠ w, ((μ.locK w k : ℂˣ) : ℂ)) * ∏ᶠ w, absHalf w (algebraMap E (w.adicCompletion E) R)` using `finprod_mul_distrib hfin1' hfin2`. Establish `hc1 : (∏ᶠ w, ((μ.locK w k : ℂˣ) : ℂ)) * ((μ.inf k : ℂˣ) : ℂ) = 1`. Use `congrArg (fun z : ℂˣ => (z : ℂ)) hprod1` as an intermediate fact.

Simplify using `only [Units.val_mul, Units.val_one] at this`. Rewrite using `[← this]`. Use `congr 1`. Conclude with `(MonoidHom.map_finprod (Units.coeHom ℂ) hfin1).symm`. Rewrite using `[hsplitf]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem resultant_factors_prod_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (μ : HChar E)
    (e : InfinitePlace E → ℤ) (hμ : IsMu μ e) (S : Set (Pl E)) (hS : IsSection S) (a b : ℕ) (P₁ P₂ : E[X])
    (h₁ : P₁ ∈ Ell E a) (h₂ : P₂ ∈ Ell E b) (hc : IsCoprime P₁ P₂) :
    (∏ᶠ w ∈ S, GlobalTheory.BCT.delta w (μ.loc w) (atPl w P₁) (atPl w P₂)) * ∏ v : InfinitePlace E, ((resultant (P₁.map v.embedding) (P₂.map v.embedding) / (‖resultant (P₁.map v.embedding) (P₂.map v.embedding)‖ : ℂ)) ^ e v * ‖resultant (P₁.map v.embedding) (P₂.map v.embedding)‖) = 1 := by
  have hR0 : resultant P₁ P₂ ≠ 0 := GlobalTheory.ProdForm.resNe E P₁ P₂ h₁.1 h₂.1 hc
  set R := resultant P₁ P₂ with hR
  set c := IsCMField.complexConj E with hcdef
  have hcR0 : c R ≠ 0 := (map_ne_zero c).2 hR0
  let k : Eˣ := Units.mk0 R hR0
  let kc : Eˣ := Units.map (MonoidHomClass.toMonoidHom c) k
  set d : E := ((-1) ^ a * P₁.coeff 0) ^ b * ((-1) ^ b * P₂.coeff 0) ^ a with hd
  have hH : c R * d = (-1) ^ (a * b) * R := GlobalTheory.T.conj_resultant_of_ell_polys E a b P₁ P₂ h₁ h₂
  have hsq : ((-1 : E) ^ (a * b)) * (-1) ^ (a * b) = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  have hd1 : (-1) ^ (a * b) * d = R * (c R)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hcR0]
    linear_combination (-1 : E) ^ (a * b) * hH + R * hsq
  have hd0 : d ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hH
    exact hR0 (by simpa using hH.symm)
  have hd2 : R ^ 2 / d = (-1) ^ (a * b) * (R * c R) := by
    rw [div_eq_iff hd0]
    linear_combination (-(-1 : E) ^ (a * b) * R) * hH - R ^ 2 * hsq

  let f : Pl E → ℂ := fun w => ((μ.locK w k : ℂˣ) : ℂ) * absHalf w (algebraMap E (w.adicCompletion E) R)
  obtain ⟨hfin1, hprod1⟩ := GlobalTheory.T.heckeChar_finprod_locK_mul_inf_eq_one E μ k
  obtain ⟨hfin2, hprod2⟩ := GlobalTheory.T.prodFormula_sqrt_normalizedAbsValues_CMField E R hR0
  have hfin1' : (Function.mulSupport fun w : Pl E => ((μ.locK w k : ℂˣ) : ℂ)).Finite := by
    refine hfin1.subset fun w hw => ?_
    intro h1; apply hw; simp [h1]
  have hfin : (Function.mulSupport f).Finite :=
    (hfin1'.union hfin2).subset (Function.mulSupport_mul _ _)

  have hloc : ∀ w ∈ S, delta w (μ.loc w) (atPl w P₁) (atPl w P₂) =
      ∏ᶠ x ∈ {x : Pl E | x.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))}, f x := by
    intro w _
    have hn₁ : (atPl w P₁).natDegree = a := by
      rw [atPl, Polynomial.natDegree_map_eq_of_injective (algebraMap E _).injective]; exact h₁.2.1
    have hn₂ : (atPl w P₂).natDegree = b := by
      rw [atPl, Polynomial.natDegree_map_eq_of_injective (algebraMap E _).injective]; exact h₂.2.1
    have hres : resultant (atPl w P₁) (atPl w P₂) = algebraMap E (w.adicCompletion E) R := GlobalTheory.ProdForm.resMap _ _ _ _ _
    have hdl : ((-1) ^ a * (atPl w P₁).coeff 0) ^ b * ((-1) ^ b * (atPl w P₂).coeff 0) ^ a =
        algebraMap E (w.adicCompletion E) d := by
      simp [atPl, Polynomial.coeff_map, hd]
    obtain ⟨hAm, hAn⟩ := GlobalTheory.T.absHalf_mul_and_absHalf_neg_one E w
    have hA0 : ∀ x : E, x ≠ 0 → algebraMap E (w.adicCompletion E) x ≠ 0 := fun x hx => (_root_.map_ne_zero _).2 hx
    by_cases hsp : IsSplitAt w
    · obtain ⟨u, hu, huw⟩ := hsp
      have hfib : {x : Pl E | x.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))} = {w, u} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · exact fun hx => GlobalTheory.T.eq_or_eq_of_under_maximalRealSubfield_eq_CMField E w u x hu huw hx
        · rintro (rfl | rfl)
          · rfl
          · exact huw
      rw [hfib, finprod_mem_pair (Ne.symm hu)]
      have hdelta : delta w (μ.loc w) (atPl w P₁) (atPl w P₂) =
          (if h : (-1) ^ (a * b) * algebraMap E (w.adicCompletion E) d ≠ 0 then (μ.loc w (Units.mk0 _ h) : ℂ) else 0) *
            absHalf w (algebraMap E (w.adicCompletion E) R ^ 2 / algebraMap E (w.adicCompletion E) d) := by
        unfold delta
        rw [hres]
        simp only [hn₁, hn₂, hdl]
        rw [if_pos ⟨u, hu, huw⟩]
      have hne : (-1) ^ (a * b) * algebraMap E (w.adicCompletion E) d ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (hA0 d hd0)
      rw [hdelta, dif_pos hne]
      have hunit : (Units.mk0 _ hne : (w.adicCompletion E)ˣ) = atFin w (k * kc⁻¹) := by
        apply Units.ext
        have e1 : ((atFin w (k * kc⁻¹) : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
            algebraMap E (w.adicCompletion E) (R * (c R)⁻¹) := by
          simp [atFin, kc, k, map_inv₀]
        rw [e1, ← hd1, Units.val_mk0]
        simp [map_mul, map_pow]
      have hchar : ((μ.loc w (Units.mk0 _ hne) : ℂˣ) : ℂ) = ((μ.locK w k : ℂˣ) : ℂ) * ((μ.locK u k : ℂˣ) : ℂ) := by
        rw [hunit]
        have h1 := GlobalTheory.T.unitaryHeckeCharCM_splitPlace_mul_conjPlace_eq_one E μ e hμ w u hu huw k
        have h2 : μ.locK w kc = (μ.locK u k)⁻¹ := eq_inv_of_mul_eq_one_right h1
        change ((μ.locK w (k * kc⁻¹) : ℂˣ) : ℂ) = _
        rw [map_mul, map_inv, h2, inv_inv, Units.val_mul]
      have habs : absHalf w (algebraMap E (w.adicCompletion E) R ^ 2 / algebraMap E (w.adicCompletion E) d) =
          absHalf w (algebraMap E (w.adicCompletion E) R) * absHalf u (algebraMap E (u.adicCompletion E) R) := by
        rw [← map_pow, ← map_div₀, hd2, map_mul, map_mul, map_pow, map_neg, map_one,
          hAm _ _ (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (mul_ne_zero (hA0 R hR0) (hA0 _ hcR0)),
          hAm _ _ (hA0 R hR0) (hA0 _ hcR0), GlobalTheory.T.absHalf_conjugatePlace_eq E w u hu huw R]
        have hpow : ∀ n : ℕ, absHalf w ((-1 : w.adicCompletion E) ^ n) = 1 := by
          intro n
          induction n with
          | zero =>
            have h := hAm (-1) (-1) (neg_ne_zero.2 one_ne_zero) (neg_ne_zero.2 one_ne_zero)
            rw [neg_one_mul, neg_neg, hAn, one_mul] at h
            rw [pow_zero, h]
          | succ n ih =>
            rw [pow_succ, hAm _ _ (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (neg_ne_zero.2 one_ne_zero), ih, hAn, one_mul]
        rw [hpow, one_mul]
      rw [hchar, habs]
      simp only [f]
      ring
    · have hfib : {x : Pl E | x.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))} = {w} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · intro hx
          by_contra hxw
          exact hsp ⟨x, hxw, hx⟩
        · rintro rfl; rfl
      rw [hfib, finprod_mem_singleton]
      unfold delta
      rw [hres]
      simp only [hn₁, hn₂, hdl]
      rw [if_neg hsp]
      simp only [f]
      rw [GlobalTheory.T.unitaryHeckeCharCM_locK_nonsplit_eq_neg_one_pow E μ e hμ w hsp k]
      rfl
  have hS' : ∀ x : Pl E, ∃! s, s ∈ S ∧ s.under (𝓞 (maximalRealSubfield E)) = x.under (𝓞 (maximalRealSubfield E)) := hS
  have hfib := GlobalTheory.T.finprod_eq_finprod_mem_fibres_of_section' (fun x : Pl E => x.under (𝓞 (maximalRealSubfield E))) S f hS' hfin
  rw [finprod_mem_congr rfl hloc, ← hfib]

  have hinf : ∀ v : InfinitePlace E, resultant (P₁.map v.embedding) (P₂.map v.embedding) = v.embedding R :=
    fun v => GlobalTheory.ProdForm.resMap _ _ _ _ _
  simp only [hinf]
  have hi := GlobalTheory.T.unitaryHeckeCharCM_infinityComponent_globalUnit E μ e hμ k
  simp only [k, Units.val_mk0] at hi
  rw [Finset.prod_mul_distrib, ← hi]
  have hsplitf : ∏ᶠ x, f x = (∏ᶠ w, ((μ.locK w k : ℂˣ) : ℂ)) * ∏ᶠ w, absHalf w (algebraMap E (w.adicCompletion E) R) :=
    finprod_mul_distrib hfin1' hfin2
  have hc1 : (∏ᶠ w, ((μ.locK w k : ℂˣ) : ℂ)) * ((μ.inf k : ℂˣ) : ℂ) = 1 := by
    have := congrArg (fun z : ℂˣ => (z : ℂ)) hprod1
    simp only [Units.val_mul, Units.val_one] at this
    rw [← this]
    congr 1
    exact (MonoidHom.map_finprod (Units.coeHom ℂ) hfin1).symm
  rw [hsplitf]
  calc (∏ᶠ w, ((μ.locK w k : ℂˣ) : ℂ)) * (∏ᶠ w, absHalf w (algebraMap E (w.adicCompletion E) R)) *
        (((μ.inf k : ℂˣ) : ℂ) * ∏ v : InfinitePlace E, (‖v.embedding R‖ : ℂ))
      = ((∏ᶠ w, ((μ.locK w k : ℂˣ) : ℂ)) * ((μ.inf k : ℂˣ) : ℂ)) *
        ((∏ᶠ w, absHalf w (algebraMap E (w.adicCompletion E) R)) * ∏ v : InfinitePlace E, (‖v.embedding R‖ : ℂ)) := by ring
    _ = 1 := by rw [hc1, hprod2, one_mul]

/- English proof (translation)
Establish `hR0 : resultant P₁ P₂ ≠ 0` using `GlobalTheory.ProdForm.resNe E P₁ P₂ h₁.1 h₂.1 hc`. Use `set R := resultant P₁ P₂ with hR`. Use `set d : E := ((-1) ^ a * P₁.coeff 0) ^ b * ((-1) ^ b * P₂.coeff 0) ^ a with hd`. Establish `hH : IsCMField.complexConj E R * d = (-1) ^ (a * b) * R` using `GlobalTheory.T.conj_resultant_of_ell_polys E a b P₁ P₂ h₁ h₂`. Establish `hd0 : d ≠ 0`.

Introduce `h0`. Rewrite `hH` using `[h0, mul_zero]`. Conclude with `hR0 (by simpa using hH.symm)`. Establish `hu0 : (-1 : E) ^ (a * b) * d ≠ 0` using `mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hd0`. Set `k : Eˣ` to `Units.mk0 R hR0`.

Set `u : Eˣ` to `Units.mk0 _ hu0`. Establish `e1 : ∀ᶠ w in (cofinite : Filter (Pl E)), μ.locK w k = 1` using `Filter.eventually_cofinite.2 (GlobalTheory.T.heckeChar_finprod_locK_mul_inf_eq_one E μ k).1`. Establish `e2 : ∀ᶠ w in (cofinite : Filter (Pl E)), μ.locK w u = 1` using `Filter.eventually_cofinite.2 (GlobalTheory.T.heckeChar_finprod_locK_mul_inf_eq_one E μ u).1`. Establish `e3 : ∀ᶠ w in (cofinite : Filter (Pl E)), absHalf w (algebraMap E (w.adicCompletion E) R) = 1` using `Filter.eventually_cofinite.2 (GlobalTheory.T.prodFormula_sqrt_normalizedAbsValues_CMField E R hR0).1`. Establish `e4 : ∀ᶠ w in (cofinite : Filter (Pl E)), absHalf w (algebraMap E (w.adicCompletion E) (R ^ 2 / d)) = 1` using `Filter.eventually_cofinite.2 (GlobalTheory.T.prodFormula_sqrt_normalizedAbsValues_CMField E (R ^ 2 / d) (div_ne_zero (pow_ne_zero _ hR0) hd0)).1`.

Use `filter_upwards [e1, e2, e3, e4] with w h1 h2 h3 h4`. Establish `hn₁ : (atPl w P₁).natDegree = a`. Rewrite using `[atPl, Polynomial.natDegree_map_eq_of_injective (algebraMap E _).injective]`. Conclude with `h₁.2.1`. Establish `hn₂ : (atPl w P₂).natDegree = b`.

Rewrite using `[atPl, Polynomial.natDegree_map_eq_of_injective (algebraMap E _).injective]`. Conclude with `h₂.2.1`. Establish `hres : resultant (atPl w P₁) (atPl w P₂) = algebraMap E (w.adicCompletion E) R` using `GlobalTheory.ProdForm.resMap _ _ _ _ _`. Establish `hdl : ((-1) ^ a * (atPl w P₁).coeff 0) ^ b * ((-1) ^ b * (atPl w P₂).coeff 0) ^ a = algebraMap E (w.adicCompletion E) d`. Simplify using `[atPl, Polynomial.coeff_map, hd]`.

Distinguish the cases in `hsp : IsSplitAt w`. Establish `hne : (-1) ^ (a * b) * algebraMap E (w.adicCompletion E) d ≠ 0` using `mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) ((_root_.map_ne_zero _).2 hd0)`. Establish `hdelta : GlobalTheory.BCT.delta w (μ.loc w) (atPl w P₁) (atPl w P₂) = (if h : (-1) ^ (a * b) * algebraMap E (w.adicCompletion E) d ≠ 0 then (μ.loc w (Units.mk0 _ h) : ℂ) else 0) * absHalf w (algebraMap E (w.adicCompletion E) R ^ 2 / algebraMap E (w.adicCompletion E) d)`. Unfold `GlobalTheory.BCT.delta`. Rewrite using `[hres]`.

Simplify using `only [hn₁, hn₂, hdl]`. Rewrite using `[if_pos hsp]`. Rewrite using `[hdelta, dif_pos hne]`. Establish `hunit : (Units.mk0 _ hne : (w.adicCompletion E)ˣ) = atFin w u`. Apply `Units.ext` to reduce the goal to its premises.

Simplify using `[atFin, u, map_mul, map_pow]`. Establish `hchar : ((μ.loc w (Units.mk0 _ hne) : ℂˣ) : ℂ) = 1`. Rewrite using `[hunit]`. Express the relevant statement in the definitionally equal form `((μ.locK w u : ℂˣ) : ℂ) = 1`. Rewrite using `[h2, Units.val_one]`.

Rewrite using `[hchar, one_mul, ← map_pow, ← map_div₀, h4]`. Unfold `GlobalTheory.BCT.delta`. Rewrite using `[hres]`. Simplify using `only [hn₁, hn₂, hdl]`. Rewrite using `[if_neg hsp, h3, mul_one]`.

Use `GlobalTheory.T.unitaryHeckeCharCM_locK_nonsplit_eq_neg_one_pow E μ e hμ w hsp k` as an intermediate fact. Rewrite `this` using `[h1]`. Simplify `this.symm` using `[k]`.
-/
theorem delta_eventually_one {E : Type} [Field E] [NumberField E] [IsCMField E] (μ : HChar E)
    (e : InfinitePlace E → ℤ) (hμ : IsMu μ e) (a b : ℕ) (P₁ P₂ : E[X])
    (h₁ : P₁ ∈ Ell E a) (h₂ : P₂ ∈ Ell E b) (hc : IsCoprime P₁ P₂) :
    ∀ᶠ w in (cofinite : Filter (Pl E)), GlobalTheory.BCT.delta w (μ.loc w) (atPl w P₁) (atPl w P₂) = 1 := by
  have hR0 : resultant P₁ P₂ ≠ 0 := GlobalTheory.ProdForm.resNe E P₁ P₂ h₁.1 h₂.1 hc
  set R := resultant P₁ P₂ with hR
  set d : E := ((-1) ^ a * P₁.coeff 0) ^ b * ((-1) ^ b * P₂.coeff 0) ^ a with hd
  have hH : IsCMField.complexConj E R * d = (-1) ^ (a * b) * R := GlobalTheory.T.conj_resultant_of_ell_polys E a b P₁ P₂ h₁ h₂
  have hd0 : d ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hH
    exact hR0 (by simpa using hH.symm)
  have hu0 : (-1 : E) ^ (a * b) * d ≠ 0 := mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hd0
  let k : Eˣ := Units.mk0 R hR0
  let u : Eˣ := Units.mk0 _ hu0
  have e1 : ∀ᶠ w in (cofinite : Filter (Pl E)), μ.locK w k = 1 :=
    Filter.eventually_cofinite.2 (GlobalTheory.T.heckeChar_finprod_locK_mul_inf_eq_one E μ k).1
  have e2 : ∀ᶠ w in (cofinite : Filter (Pl E)), μ.locK w u = 1 :=
    Filter.eventually_cofinite.2 (GlobalTheory.T.heckeChar_finprod_locK_mul_inf_eq_one E μ u).1
  have e3 : ∀ᶠ w in (cofinite : Filter (Pl E)), absHalf w (algebraMap E (w.adicCompletion E) R) = 1 :=
    Filter.eventually_cofinite.2 (GlobalTheory.T.prodFormula_sqrt_normalizedAbsValues_CMField E R hR0).1
  have e4 : ∀ᶠ w in (cofinite : Filter (Pl E)), absHalf w (algebraMap E (w.adicCompletion E) (R ^ 2 / d)) = 1 :=
    Filter.eventually_cofinite.2 (GlobalTheory.T.prodFormula_sqrt_normalizedAbsValues_CMField E (R ^ 2 / d) (div_ne_zero (pow_ne_zero _ hR0) hd0)).1
  filter_upwards [e1, e2, e3, e4] with w h1 h2 h3 h4
  have hn₁ : (atPl w P₁).natDegree = a := by
    rw [atPl, Polynomial.natDegree_map_eq_of_injective (algebraMap E _).injective]; exact h₁.2.1
  have hn₂ : (atPl w P₂).natDegree = b := by
    rw [atPl, Polynomial.natDegree_map_eq_of_injective (algebraMap E _).injective]; exact h₂.2.1
  have hres : resultant (atPl w P₁) (atPl w P₂) = algebraMap E (w.adicCompletion E) R := GlobalTheory.ProdForm.resMap _ _ _ _ _
  have hdl : ((-1) ^ a * (atPl w P₁).coeff 0) ^ b * ((-1) ^ b * (atPl w P₂).coeff 0) ^ a =
      algebraMap E (w.adicCompletion E) d := by
    simp [atPl, Polynomial.coeff_map, hd]
  by_cases hsp : IsSplitAt w
  · have hne : (-1) ^ (a * b) * algebraMap E (w.adicCompletion E) d ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) ((_root_.map_ne_zero _).2 hd0)
    have hdelta : GlobalTheory.BCT.delta w (μ.loc w) (atPl w P₁) (atPl w P₂) =
        (if h : (-1) ^ (a * b) * algebraMap E (w.adicCompletion E) d ≠ 0 then (μ.loc w (Units.mk0 _ h) : ℂ) else 0) *
          absHalf w (algebraMap E (w.adicCompletion E) R ^ 2 / algebraMap E (w.adicCompletion E) d) := by
      unfold GlobalTheory.BCT.delta
      rw [hres]
      simp only [hn₁, hn₂, hdl]
      rw [if_pos hsp]
    rw [hdelta, dif_pos hne]
    have hunit : (Units.mk0 _ hne : (w.adicCompletion E)ˣ) = atFin w u := by
      apply Units.ext
      simp [atFin, u, map_mul, map_pow]
    have hchar : ((μ.loc w (Units.mk0 _ hne) : ℂˣ) : ℂ) = 1 := by
      rw [hunit]
      change ((μ.locK w u : ℂˣ) : ℂ) = 1
      rw [h2, Units.val_one]
    rw [hchar, one_mul, ← map_pow, ← map_div₀, h4]
  · unfold GlobalTheory.BCT.delta
    rw [hres]
    simp only [hn₁, hn₂, hdl]
    rw [if_neg hsp, h3, mul_one]
    have := GlobalTheory.T.unitaryHeckeCharCM_locK_nonsplit_eq_neg_one_pow E μ e hμ w hsp k
    rw [h1] at this
    simpa [k] using this.symm

open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.G2

/- English proof (translation)
Establish `key : ∀ (b : ℕ) (_ : a + b = n) (lam : DomWeight n), ∃ (ι : Type) (_ : Fintype ι) (l₁ : ι → DomWeight a) (l₂ : ι → DomWeight b) (ε : ι → ℂ), (∀ j, (infOfWeight (l₁ j)).map (· + (b : ℂ) * (e : ℂ) / 2) + (infOfWeight (l₂ j)).map (· + (a : ℂ) * (e : ℂ) / 2) = infOfWeight lam) ∧ ∀ Q₁ …`. Introduce `b hb lam`. Substitute `hb` using the available equality. Conclude with `GlobalTheory.character_laplace_factorisation a b lam e he`. Conclude with `key (n - a) (Nat.add_sub_cancel' ha) lam`.
-/
theorem laplace_cast (n a : ℕ) (ha : a ≤ n) (lam : DomWeight n) (e : ℤ) (he : Odd e) :
    ∃ (ι : Type) (_ : Fintype ι) (l₁ : ι → DomWeight a) (l₂ : ι → DomWeight (n - a)) (ε : ι → ℂ),
      (∀ j, (infOfWeight (l₁ j)).map (· + ((n - a : ℕ) : ℂ) * (e : ℂ) / 2) +
        (infOfWeight (l₂ j)).map (· + (a : ℂ) * (e : ℂ) / 2) = infOfWeight lam) ∧
      ∀ Q₁ Q₂ : ℂ[X], Q₁.Monic → Q₂.Monic → Q₁.natDegree = a → Q₂.natDegree = n - a → (Q₁ * Q₂).Separable →
        (∀ z ∈ (Q₁ * Q₂).roots, ‖z‖ = 1) →
        ((resultant Q₁ Q₂ / (‖resultant Q₁ Q₂‖ : ℂ)) ^ e * ‖resultant Q₁ Q₂‖) * (starRingEnd ℂ) (chAt lam (Q₁ * Q₂)) =
          ∑ j, ε j * (starRingEnd ℂ) (chAt (l₁ j) Q₁) * (starRingEnd ℂ) (chAt (l₂ j) Q₂) := by
  have key : ∀ (b : ℕ) (_ : a + b = n) (lam : DomWeight n),
      ∃ (ι : Type) (_ : Fintype ι) (l₁ : ι → DomWeight a) (l₂ : ι → DomWeight b) (ε : ι → ℂ),
      (∀ j, (infOfWeight (l₁ j)).map (· + (b : ℂ) * (e : ℂ) / 2) +
        (infOfWeight (l₂ j)).map (· + (a : ℂ) * (e : ℂ) / 2) = infOfWeight lam) ∧
      ∀ Q₁ Q₂ : ℂ[X], Q₁.Monic → Q₂.Monic → Q₁.natDegree = a → Q₂.natDegree = b → (Q₁ * Q₂).Separable →
        (∀ z ∈ (Q₁ * Q₂).roots, ‖z‖ = 1) →
        ((resultant Q₁ Q₂ / (‖resultant Q₁ Q₂‖ : ℂ)) ^ e * ‖resultant Q₁ Q₂‖) * (starRingEnd ℂ) (chAt lam (Q₁ * Q₂)) =
          ∑ j, ε j * (starRingEnd ℂ) (chAt (l₁ j) Q₁) * (starRingEnd ℂ) (chAt (l₂ j) Q₂) := by
    intro b hb lam
    subst hb
    exact GlobalTheory.character_laplace_factorisation a b lam e he
  exact key (n - a) (Nat.add_sub_cancel' ha) lam

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Introduce `w hw`. Take `⟨m₁, m₂, d₁, d₂, sp, c₁, c₂⟩` from `hEL E a (n - a) p₁ p₂ h₁ h₂ hc w`. Conclude with `hM w hw _ _ m₁ m₂ d₁ d₂ sp c₁ c₂`.
-/
theorem match_at (hEL : EllLocal) {n a : ℕ} {μ : HChar E} {S : Set (Pl E)} {f : ∀ w : Pl E, UL n w → ℂ}
    {φ : ∀ w : Pl E, GLw a w × GLw (n - a) w → ℂ}
    (hM : ∀ w ∈ S, GlobalTheory.BCT.Match n a (n - a) w (μ.loc w) (f w) (φ w)) {p₁ p₂ : E[X]}
    (h₁ : p₁ ∈ Ell E a) (h₂ : p₂ ∈ Ell E (n - a)) (hc : IsCoprime p₁ p₂) :
    ∀ w ∈ S, stTw2 a (n - a) w (atPl w p₁) (atPl w p₂) (φ w) =
      GlobalTheory.BCT.delta w (μ.loc w) (atPl w p₁) (atPl w p₂) * kapOrb n w (atPl w p₁) (atPl w p₂) (f w) := by
  intro w hw
  obtain ⟨m₁, m₂, d₁, d₂, sp, c₁, c₂⟩ := hEL E a (n - a) p₁ p₂ h₁ h₂ hc w
  exact hM w hw _ _ m₁ m₂ d₁ d₂ sp c₁ c₂

/- English proof (translation)
The claim follows from `hKO E hU n K' f hf p₁ p₂ (by rw [h₁.2.1]; exact h₁) (by rw [h₂.2.1]; exact h₂) hc (by rw [h₁.2.1, h₂.2.1]; omega)`.
-/
theorem kapOrb_finite (hKO : KapOrbAE) (hU : Unr E) {n a : ℕ} (ha : a ≤ n) {K' : ∀ w : Pl E, Subgroup (UL n w)}
    {f : ∀ w : Pl E, UL n w → ℂ} (hf : GlobalTheory.BCT.IsTest (KL n) K' f) {p₁ p₂ : E[X]}
    (h₁ : p₁ ∈ Ell E a) (h₂ : p₂ ∈ Ell E (n - a)) (hc : IsCoprime p₁ p₂) :
    (Function.mulSupport fun w : Pl E => kapOrb n w (atPl w p₁) (atPl w p₂) (f w)).Finite :=
  hKO E hU n K' f hf p₁ p₂ (by rw [h₁.2.1]; exact h₁) (by rw [h₂.2.1]; exact h₂) hc
    (by rw [h₁.2.1, h₂.2.1]; omega)

/- English proof (translation)
The claim follows from `Filter.eventually_cofinite.1 (delta_eventually_one μ e hμ a b p₁ p₂ h₁ h₂ hc)`.
-/
theorem delta_finite {μ : HChar E} {e : InfinitePlace E → ℤ} (hμ : IsMu μ e) {a b : ℕ} {p₁ p₂ : E[X]}
    (h₁ : p₁ ∈ Ell E a) (h₂ : p₂ ∈ Ell E b) (hc : IsCoprime p₁ p₂) :
    (Function.mulSupport fun w : Pl E => GlobalTheory.BCT.delta w (μ.loc w) (atPl w p₁) (atPl w p₂)).Finite :=
  Filter.eventually_cofinite.1 (delta_eventually_one μ e hμ a b p₁ p₂ h₁ h₂ hc)

/- English proof (translation)
Rewrite using `[finprod_mem_congr rfl (match_at hEL hM h₁ h₂ hc)]`. Conclude with `finprod_mem_mul_distrib' ((delta_finite hμ h₁ h₂ hc).inter_of_right _) ((kapOrb_finite hKO hU ha hf h₁ h₂ hc).inter_of_right _)`.
-/
theorem prod_stTw2 (hEL : EllLocal) (hKO : KapOrbAE) (hU : Unr E) {n a : ℕ} (ha : a ≤ n) {μ : HChar E}
    {e : InfinitePlace E → ℤ} (hμ : IsMu μ e) {S : Set (Pl E)} {K' : ∀ w : Pl E, Subgroup (UL n w)}
    {f : ∀ w : Pl E, UL n w → ℂ} (hf : GlobalTheory.BCT.IsTest (KL n) K' f)
    {φ : ∀ w : Pl E, GLw a w × GLw (n - a) w → ℂ}
    (hM : ∀ w ∈ S, GlobalTheory.BCT.Match n a (n - a) w (μ.loc w) (f w) (φ w)) {p₁ p₂ : E[X]}
    (h₁ : p₁ ∈ Ell E a) (h₂ : p₂ ∈ Ell E (n - a)) (hc : IsCoprime p₁ p₂) :
    ∏ᶠ w ∈ S, stTw2 a (n - a) w (atPl w p₁) (atPl w p₂) (φ w) =
      (∏ᶠ w ∈ S, GlobalTheory.BCT.delta w (μ.loc w) (atPl w p₁) (atPl w p₂)) *
        ∏ᶠ w ∈ S, kapOrb n w (atPl w p₁) (atPl w p₂) (f w) := by
  rw [finprod_mem_congr rfl (match_at hEL hM h₁ h₂ hc)]
  exact finprod_mem_mul_distrib' ((delta_finite hμ h₁ h₂ hc).inter_of_right _)
    ((kapOrb_finite hKO hU ha hf h₁ h₂ hc).inter_of_right _)

/- English proof (translation)
Introduce `w hw`. Establish `hm` using `match_at hEL hM h₁ h₂ hc`. Rewrite `h` using `[finprod_mem_congr rfl hm]`. Establish `hfin : (Function.mulSupport fun w : Pl E => GlobalTheory.BCT.delta w (μ.loc w) (atPl w p₁) (atPl w p₂) * kapOrb n w (atPl w p₁) (atPl w p₂) (f w)).Finite` using `((delta_finite hμ h₁ h₂ hc).union (kapOrb_finite hKO hU ha hf h₁ h₂ hc)).subset (Function.mulSupport_mul _ _)`. Establish `h0` using `GlobalTheory.BCT.GeoFin.ne_zero_of_finprod_mem_ne_zero _ S hfin h w hw`.

Rewrite `h0` using `[← hm w hw]`. Conclude with `GlobalTheory.BCT.GeoFin.exists_support_of_stTw2_ne_zero a (n - a) w _ _ _ h0`.
-/
theorem exists_support (hEL : EllLocal) (hKO : KapOrbAE) (hU : Unr E) {n a : ℕ} (ha : a ≤ n) {μ : HChar E}
    {e : InfinitePlace E → ℤ} (hμ : IsMu μ e) {S : Set (Pl E)} {K' : ∀ w : Pl E, Subgroup (UL n w)}
    {f : ∀ w : Pl E, UL n w → ℂ} (hf : GlobalTheory.BCT.IsTest (KL n) K' f)
    {φ : ∀ w : Pl E, GLw a w × GLw (n - a) w → ℂ}
    (hM : ∀ w ∈ S, GlobalTheory.BCT.Match n a (n - a) w (μ.loc w) (f w) (φ w)) {p₁ p₂ : E[X]}
    (h₁ : p₁ ∈ Ell E a) (h₂ : p₂ ∈ Ell E (n - a)) (hc : IsCoprime p₁ p₂)
    (h : ∏ᶠ w ∈ S, stTw2 a (n - a) w (atPl w p₁) (atPl w p₂) (φ w) ≠ 0) :
    ∀ w ∈ S, ∃ y : GLw a w × GLw (n - a) w, φ w y ≠ 0 ∧ (nrmL a w y.1).val.charpoly = atPl w p₁ ∧
      (nrmL (n - a) w y.2).val.charpoly = atPl w p₂ := by
  intro w hw
  have hm := match_at hEL hM h₁ h₂ hc
  rw [finprod_mem_congr rfl hm] at h
  have hfin : (Function.mulSupport fun w : Pl E => GlobalTheory.BCT.delta w (μ.loc w) (atPl w p₁) (atPl w p₂) *
      kapOrb n w (atPl w p₁) (atPl w p₂) (f w)).Finite :=
    ((delta_finite hμ h₁ h₂ hc).union (kapOrb_finite hKO hU ha hf h₁ h₂ hc)).subset (Function.mulSupport_mul _ _)
  have h0 := GlobalTheory.BCT.GeoFin.ne_zero_of_finprod_mem_ne_zero _ S hfin h w hw
  rw [← hm w hw] at h0
  exact GlobalTheory.BCT.GeoFin.exists_support_of_stTw2_ne_zero a (n - a) w _ _ _ h0

/- English proof (translation)
Establish `hP` using `(GlobalTheory.BCT.KapMul.kap_mul E hU a (n - a) p₁ p₂ h₁ h₂ hc).2.2`. Establish `hv : ∀ v : InfinitePlace E, ((resultant (p₁.map v.embedding) (p₂.map v.embedding) / (‖resultant (p₁.map v.embedding) (p₂.map v.embedding)‖ : ℂ)) ^ e v * ‖resultant (p₁.map v.embedding) (p₂.map v.embedding)‖) * (starRingEnd ℂ) (chAt (lam v) ((p₁ * p₂).map v.embedding)) = ∑ j, ε v …`. Introduce `v`. Rewrite using `[Polynomial.map_mul]`. Use `hL v _ _ (h₁.1.map _) (h₂.1.map _) ?_ ?_ ?_ ?_` and prove the remaining obligations.

Rewrite using `[Polynomial.natDegree_map]`. Conclude with `h₁.2.1`. Rewrite using `[Polynomial.natDegree_map]`. Conclude with `h₂.2.1`. Rewrite using `[← Polynomial.map_mul]`.

Conclude with `hP.2.2.1.map`. Introduce `z hz`. Rewrite `hz` using `[← Polynomial.map_mul]`. Conclude with `hP.2.2.2 _ z hz`. Simplify using `only [chW]`.

Rewrite using `[← Finset.prod_mul_distrib, Finset.prod_congr rfl (fun v _ => hv v), Finset.prod_univ_sum, Fintype.piFinset_univ]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Simplify using `only [Finset.prod_mul_distrib]`.
-/
theorem chW_expand (hU : Unr E) {n a : ℕ} (e : InfinitePlace E → ℤ) (lam : InfinitePlace E → DomWeight n)
    (κ : InfinitePlace E → Type) [∀ v, Fintype (κ v)] (l₁ : ∀ v, κ v → DomWeight a)
    (l₂ : ∀ v, κ v → DomWeight (n - a)) (ε : ∀ v, κ v → ℂ)
    (hL : ∀ v, ∀ Q₁ Q₂ : ℂ[X], Q₁.Monic → Q₂.Monic → Q₁.natDegree = a → Q₂.natDegree = n - a → (Q₁ * Q₂).Separable →
      (∀ z ∈ (Q₁ * Q₂).roots, ‖z‖ = 1) →
      ((resultant Q₁ Q₂ / (‖resultant Q₁ Q₂‖ : ℂ)) ^ e v * ‖resultant Q₁ Q₂‖) * (starRingEnd ℂ) (chAt (lam v) (Q₁ * Q₂)) =
        ∑ j, ε v j * (starRingEnd ℂ) (chAt (l₁ v j) Q₁) * (starRingEnd ℂ) (chAt (l₂ v j) Q₂))
    {p₁ p₂ : E[X]} (h₁ : p₁ ∈ Ell E a) (h₂ : p₂ ∈ Ell E (n - a)) (hc : IsCoprime p₁ p₂) :
    (∏ v : InfinitePlace E, ((resultant (p₁.map v.embedding) (p₂.map v.embedding) /
        (‖resultant (p₁.map v.embedding) (p₂.map v.embedding)‖ : ℂ)) ^ e v *
          ‖resultant (p₁.map v.embedding) (p₂.map v.embedding)‖)) * chW lam (p₁ * p₂) =
      ∑ s : ∀ v, κ v, (∏ v, ε v (s v)) * chW (fun v => l₁ v (s v)) p₁ * chW (fun v => l₂ v (s v)) p₂ := by
  have hP := (GlobalTheory.BCT.KapMul.kap_mul E hU a (n - a) p₁ p₂ h₁ h₂ hc).2.2
  have hv : ∀ v : InfinitePlace E, ((resultant (p₁.map v.embedding) (p₂.map v.embedding) /
        (‖resultant (p₁.map v.embedding) (p₂.map v.embedding)‖ : ℂ)) ^ e v *
          ‖resultant (p₁.map v.embedding) (p₂.map v.embedding)‖) *
        (starRingEnd ℂ) (chAt (lam v) ((p₁ * p₂).map v.embedding)) =
      ∑ j, ε v j * (starRingEnd ℂ) (chAt (l₁ v j) (p₁.map v.embedding)) *
        (starRingEnd ℂ) (chAt (l₂ v j) (p₂.map v.embedding)) := by
    intro v
    rw [Polynomial.map_mul]
    refine hL v _ _ (h₁.1.map _) (h₂.1.map _) ?_ ?_ ?_ ?_
    · rw [Polynomial.natDegree_map]; exact h₁.2.1
    · rw [Polynomial.natDegree_map]; exact h₂.2.1
    · rw [← Polynomial.map_mul]; exact hP.2.2.1.map
    · intro z hz
      rw [← Polynomial.map_mul] at hz
      exact hP.2.2.2 _ z hz
  simp only [chW]
  rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl (fun v _ => hv v), Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Finset.prod_mul_distrib]

/- English proof (translation)
Establish `hDA` using `resultant_factors_prod_eq_one μ e hμ S hS a (n - a) p₁ p₂ h₁ h₂ hc`. Establish `hA` using `chW_expand hU e lam κ l₁ l₂ ε hL h₁ h₂ hc`. Rewrite using `[prod_stTw2 hEL hKO hU ha hμ hf hM h₁ h₂ hc, (GlobalTheory.BCT.KapMul.kap_mul E hU a (n - a) p₁ p₂ h₁ h₂ hc).1]`. Use `set D := ∏ᶠ w ∈ S, GlobalTheory.BCT.delta w (μ.loc w) (atPl w p₁) (atPl w p₂)`. Use `set O := ∏ᶠ w ∈ S, kapOrb n w (atPl w p₁) (atPl w p₂) (f w)`.

Use `set A := ∏ v : InfinitePlace E, ((resultant (p₁.map v.embedding) (p₂.map v.embedding) / (‖resultant (p₁.map v.embedding) (p₂.map v.embedding)‖ : ℂ)) ^ e v * ‖resultant (p₁.map v.embedding) (p₂.map v.embedding)‖)`. Establish `e1 : ∑ s : ∀ v, κ v, (∏ v, ε v (s v)) * (kap p₁ * kap p₂ * chW (fun v => l₁ v (s v)) p₁ * chW (fun v => l₂ v (s v)) p₂ * (D * O)) = (kap p₁ * kap p₂ * (D * O)) * ∑ s : ∀ v, κ v, (∏ v, ε v (s v)) * chW (fun v => l₁ v (s v)) p₁ * chW (fun v => l₂ v (s v)) p₂`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun s _ => by ring`. Rewrite using `[e1, ← hA]`.

Take the linear combination `(-(kap p₁ * kap p₂ * O * chW lam (p₁ * p₂))) * hDA`.
-/
theorem term_identity (hEL : EllLocal) (hKO : KapOrbAE) (hU : Unr E) {n a : ℕ} (ha : a ≤ n) {μ : HChar E}
    {e : InfinitePlace E → ℤ} (hμ : IsMu μ e) {S : Set (Pl E)} (hS : IsSection S)
    (lam : InfinitePlace E → DomWeight n)
    (κ : InfinitePlace E → Type) [∀ v, Fintype (κ v)] (l₁ : ∀ v, κ v → DomWeight a)
    (l₂ : ∀ v, κ v → DomWeight (n - a)) (ε : ∀ v, κ v → ℂ)
    (hL : ∀ v, ∀ Q₁ Q₂ : ℂ[X], Q₁.Monic → Q₂.Monic → Q₁.natDegree = a → Q₂.natDegree = n - a → (Q₁ * Q₂).Separable →
      (∀ z ∈ (Q₁ * Q₂).roots, ‖z‖ = 1) →
      ((resultant Q₁ Q₂ / (‖resultant Q₁ Q₂‖ : ℂ)) ^ e v * ‖resultant Q₁ Q₂‖) * (starRingEnd ℂ) (chAt (lam v) (Q₁ * Q₂)) =
        ∑ j, ε v j * (starRingEnd ℂ) (chAt (l₁ v j) Q₁) * (starRingEnd ℂ) (chAt (l₂ v j) Q₂))
    {K' : ∀ w : Pl E, Subgroup (UL n w)} {f : ∀ w : Pl E, UL n w → ℂ} (hf : GlobalTheory.BCT.IsTest (KL n) K' f)
    {φ : ∀ w : Pl E, GLw a w × GLw (n - a) w → ℂ}
    (hM : ∀ w ∈ S, GlobalTheory.BCT.Match n a (n - a) w (μ.loc w) (f w) (φ w)) {p₁ p₂ : E[X]}
    (h₁ : p₁ ∈ Ell E a) (h₂ : p₂ ∈ Ell E (n - a)) (hc : IsCoprime p₁ p₂) :
    kap (p₁ * p₂) * chW lam (p₁ * p₂) * ∏ᶠ w ∈ S, kapOrb n w (atPl w p₁) (atPl w p₂) (f w) =
      ∑ s : ∀ v, κ v, (∏ v, ε v (s v)) * (kap p₁ * kap p₂ * chW (fun v => l₁ v (s v)) p₁ *
        chW (fun v => l₂ v (s v)) p₂ * ∏ᶠ w ∈ S, stTw2 a (n - a) w (atPl w p₁) (atPl w p₂) (φ w)) := by
  have hDA := resultant_factors_prod_eq_one μ e hμ S hS a (n - a) p₁ p₂ h₁ h₂ hc
  have hA := chW_expand hU e lam κ l₁ l₂ ε hL h₁ h₂ hc
  rw [prod_stTw2 hEL hKO hU ha hμ hf hM h₁ h₂ hc, (GlobalTheory.BCT.KapMul.kap_mul E hU a (n - a) p₁ p₂ h₁ h₂ hc).1]
  set D := ∏ᶠ w ∈ S, GlobalTheory.BCT.delta w (μ.loc w) (atPl w p₁) (atPl w p₂)
  set O := ∏ᶠ w ∈ S, kapOrb n w (atPl w p₁) (atPl w p₂) (f w)
  set A := ∏ v : InfinitePlace E, ((resultant (p₁.map v.embedding) (p₂.map v.embedding) /
        (‖resultant (p₁.map v.embedding) (p₂.map v.embedding)‖ : ℂ)) ^ e v *
          ‖resultant (p₁.map v.embedding) (p₂.map v.embedding)‖)
  have e1 : ∑ s : ∀ v, κ v, (∏ v, ε v (s v)) * (kap p₁ * kap p₂ * chW (fun v => l₁ v (s v)) p₁ *
        chW (fun v => l₂ v (s v)) p₂ * (D * O)) =
      (kap p₁ * kap p₂ * (D * O)) * ∑ s : ∀ v, κ v, (∏ v, ε v (s v)) * chW (fun v => l₁ v (s v)) p₁ *
        chW (fun v => l₂ v (s v)) p₂ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e1, ← hA]
  linear_combination (-(kap p₁ * kap p₂ * O * chW lam (p₁ * p₂))) * hDA

/- English proof (translation)
Use `finsum_mem_eq_sum_of_inter_support_eq g ?_` and prove the remaining obligations. Use extensionality with `p`. Simplify using `only [Set.mem_inter_iff, Function.mem_support, Finset.mem_coe]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hp, h0⟩`.

Conclude with `⟨h p hp h0, h0⟩`. Introduce and unpack `⟨hp, h0⟩`. Conclude with `⟨((hF p).1 hp).1, h0⟩`.
-/
theorem finsum_mem_eq_sum_of_subset {β : Type} {t : Set β} {F : Finset β} (hF : ∀ p, p ∈ F ↔ p ∈ t ∧ p ∈ (F : Set β))
    (g : β → ℂ) (h : ∀ p ∈ t, g p ≠ 0 → p ∈ F) : ∑ᶠ p ∈ t, g p = ∑ p ∈ F, g p := by
  refine finsum_mem_eq_sum_of_inter_support_eq g ?_
  ext p
  simp only [Set.mem_inter_iff, Function.mem_support, Finset.mem_coe]
  constructor
  · rintro ⟨hp, h0⟩
    exact ⟨h p hp h0, h0⟩
  · rintro ⟨hp, h0⟩
    exact ⟨((hF p).1 hp).1, h0⟩

/- English proof (translation)
Take `⟨K₁, K₂, -, -, hφ⟩` from `hT`. Establish `hfin` using `GlobalTheory.CompanionTheory.FinPol.finite_pairs E hU a (n - a) S hS φ (fun w => (hφ.1 w).1) hφ.2`. Use `set t : Set (E[X] × E[X]) := {p | p.1 ∈ Ell E a ∧ p.2 ∈ Ell E (n - a) ∧ IsCoprime p.1 p.2} with ht`. Use `set B := {p : E[X] × E[X] | p.1 ∈ Ell E a ∧ p.2 ∈ Ell E (n - a) ∧ ∀ w ∈ S, ∃ y : GLw a w × GLw (n - a) w, φ w y ≠ 0 ∧ (nrmL a w y.1).val.charpoly = atPl w p.1 ∧ (nrmL (n - a) w y.2).val.charpoly = atPl w p.2} with hB`. Establish `hfin' : (t ∩ B).Finite` using `hfin.inter_of_right _`.

Use `set F := hfin'.toFinset with hFdef`. Establish `hF : ∀ p, p ∈ F ↔ p ∈ t ∧ p ∈ (F : Set (E[X] × E[X]))` using `fun p => by`. Prove the components needed by the constructor for the conclusion. Introduce `hp`. Conclude with `⟨((hfin'.mem_toFinset).1 hp).1, hp⟩`.

Conclude with `fun hp => hp.2`. Set `T : (∀ v, κ v) → E[X] × E[X] → ℂ` to `fun s p => kap p.1 * kap p.2 * chW (fun v => l₁ v (s v)) p.1 * chW (fun v => l₂ v (s v)) p.2 * ∏ᶠ w ∈ S, stTw2 a (n - a) w (atPl w p.1) (atPl w p.2) (φ w)`. Establish `hsupp : ∀ s, ∀ p ∈ t, T s p ≠ 0 → p ∈ F`. Introduce `s p hp h0`. Use `(hfin'.mem_toFinset).2 ⟨hp, hp.1, hp.2.1, ?_⟩` and prove the remaining obligations.

Conclude with `exists_support hEL hKO hU ha hμ hf hM hp.1 hp.2.1 hp.2.2 (right_ne_zero_of_mul h0)`. Establish `hterm : ∀ p ∈ t, kap (p.1 * p.2) * chW lam (p.1 * p.2) * ∏ᶠ w ∈ S, kapOrb n w (atPl w p.1) (atPl w p.2) (f w) = ∑ s : ∀ v, κ v, (∏ v, ε v (s v)) * T s p` using `fun p hp => term_identity hEL hKO hU ha hμ hS lam κ l₁ l₂ ε hL hf hM hp.1 hp.2.1 hp.2.2`. Establish `hR : ∀ s, geomSt2 S (fun v => l₁ v (s v)) (fun v => l₂ v (s v)) φ = ∑ p ∈ F, T s p` using `fun s => finsum_mem_eq_sum_of_subset hF (T s) (hsupp s)`. Rewrite using `[finsum_mem_eq_sum_of_subset hF _ ?_]`. Simplify using `only [hR, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Rewrite using `[hterm p ((hF p).1 hp).1]`. Introduce `p hp h0`. Rewrite `h0` using `[hterm p hp]`.

Take `⟨s, -, hs⟩` from `Finset.exists_ne_zero_of_sum_ne_zero h0`. Conclude with `hsupp s p hp (right_ne_zero_of_mul hs)`.
-/
theorem sum_identity (hEL : EllLocal) (hKO : KapOrbAE) (hU : Unr E) {n a : ℕ} (ha : a ≤ n) {μ : HChar E}
    {e : InfinitePlace E → ℤ} (hμ : IsMu μ e) {S : Set (Pl E)} (hS : IsSection S)
    (lam : InfinitePlace E → DomWeight n)
    (κ : InfinitePlace E → Type) [∀ v, Fintype (κ v)] (l₁ : ∀ v, κ v → DomWeight a)
    (l₂ : ∀ v, κ v → DomWeight (n - a)) (ε : ∀ v, κ v → ℂ)
    (hL : ∀ v, ∀ Q₁ Q₂ : ℂ[X], Q₁.Monic → Q₂.Monic → Q₁.natDegree = a → Q₂.natDegree = n - a → (Q₁ * Q₂).Separable →
      (∀ z ∈ (Q₁ * Q₂).roots, ‖z‖ = 1) →
      ((resultant Q₁ Q₂ / (‖resultant Q₁ Q₂‖ : ℂ)) ^ e v * ‖resultant Q₁ Q₂‖) * (starRingEnd ℂ) (chAt (lam v) (Q₁ * Q₂)) =
        ∑ j, ε v j * (starRingEnd ℂ) (chAt (l₁ v j) Q₁) * (starRingEnd ℂ) (chAt (l₂ v j) Q₂))
    {K' : ∀ w : Pl E, Subgroup (UL n w)} {f : ∀ w : Pl E, UL n w → ℂ} (hf : GlobalTheory.BCT.IsTest (KL n) K' f)
    {φ : ∀ w : Pl E, GLw a w × GLw (n - a) w → ℂ} (hT : IsTestP φ)
    (hM : ∀ w ∈ S, GlobalTheory.BCT.Match n a (n - a) w (μ.loc w) (f w) (φ w)) :
    ∑ᶠ p ∈ {p : E[X] × E[X] | p.1 ∈ Ell E a ∧ p.2 ∈ Ell E (n - a) ∧ IsCoprime p.1 p.2},
        kap (p.1 * p.2) * chW lam (p.1 * p.2) * ∏ᶠ w ∈ S, kapOrb n w (atPl w p.1) (atPl w p.2) (f w) =
      ∑ s : ∀ v, κ v, (∏ v, ε v (s v)) * geomSt2 S (fun v => l₁ v (s v)) (fun v => l₂ v (s v)) φ := by
  obtain ⟨K₁, K₂, -, -, hφ⟩ := hT
  have hfin := GlobalTheory.CompanionTheory.FinPol.finite_pairs E hU a (n - a) S hS φ (fun w => (hφ.1 w).1) hφ.2
  set t : Set (E[X] × E[X]) := {p | p.1 ∈ Ell E a ∧ p.2 ∈ Ell E (n - a) ∧ IsCoprime p.1 p.2} with ht
  set B := {p : E[X] × E[X] | p.1 ∈ Ell E a ∧ p.2 ∈ Ell E (n - a) ∧ ∀ w ∈ S, ∃ y : GLw a w × GLw (n - a) w, φ w y ≠ 0 ∧
    (nrmL a w y.1).val.charpoly = atPl w p.1 ∧ (nrmL (n - a) w y.2).val.charpoly = atPl w p.2} with hB
  have hfin' : (t ∩ B).Finite := hfin.inter_of_right _
  set F := hfin'.toFinset with hFdef
  have hF : ∀ p, p ∈ F ↔ p ∈ t ∧ p ∈ (F : Set (E[X] × E[X])) := fun p => by
    constructor
    · intro hp
      exact ⟨((hfin'.mem_toFinset).1 hp).1, hp⟩
    · exact fun hp => hp.2
  let T : (∀ v, κ v) → E[X] × E[X] → ℂ := fun s p => kap p.1 * kap p.2 * chW (fun v => l₁ v (s v)) p.1 *
    chW (fun v => l₂ v (s v)) p.2 * ∏ᶠ w ∈ S, stTw2 a (n - a) w (atPl w p.1) (atPl w p.2) (φ w)
  have hsupp : ∀ s, ∀ p ∈ t, T s p ≠ 0 → p ∈ F := by
    intro s p hp h0
    refine (hfin'.mem_toFinset).2 ⟨hp, hp.1, hp.2.1, ?_⟩
    exact exists_support hEL hKO hU ha hμ hf hM hp.1 hp.2.1 hp.2.2 (right_ne_zero_of_mul h0)
  have hterm : ∀ p ∈ t, kap (p.1 * p.2) * chW lam (p.1 * p.2) * ∏ᶠ w ∈ S, kapOrb n w (atPl w p.1) (atPl w p.2) (f w) =
      ∑ s : ∀ v, κ v, (∏ v, ε v (s v)) * T s p := fun p hp =>
    term_identity hEL hKO hU ha hμ hS lam κ l₁ l₂ ε hL hf hM hp.1 hp.2.1 hp.2.2
  have hR : ∀ s, geomSt2 S (fun v => l₁ v (s v)) (fun v => l₂ v (s v)) φ = ∑ p ∈ F, T s p := fun s =>
    finsum_mem_eq_sum_of_subset hF (T s) (hsupp s)
  rw [finsum_mem_eq_sum_of_subset hF _ ?_]
  · simp only [hR, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hterm p ((hF p).1 hp).1]
  · intro p hp h0
    rw [hterm p hp] at h0
    obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0
    exact hsupp s p hp (right_ne_zero_of_mul hs)

/- English proof (translation)
Introduce `hEL hKO _ E _ _ _ hU n _ μ e hμ lam`. Establish `hl : ∀ (a : Fin (n + 1)) (v : InfinitePlace E), _` using `fun a v => laplace_cast n a (Nat.lt_succ_iff.1 a.2) (lam v) (e v) (hμ.2.2.2.1 v)`. Use `choose κ inst l₁ l₂ ε hinf hL using hl`. Use `letI : ∀ a v, Fintype (κ a v) := inst`. Set `J : Type` to `Σ a : Fin (n + 1), ∀ v, κ a v`.

Set `c₀ : J → ℂ` to `fun j => ∏ v, ε j.1 v (j.2 v)`. Use `⟨{j : J // c₀ j ≠ 0}, inferInstance, fun i => i.1.1, fun i v => l₁ i.1.1 v (i.1.2 v), fun i v => l₂ i.1.1 v (i.1.2 v), fun i => c₀ i.1, fun i => ⟨i.2, Nat.lt_succ_iff.1 i.1.1.2, fun v => hinf _ _ _⟩, ?_⟩` and prove the remaining obligations. Introduce `S hS K' f φ _ hf hφ`. Establish `hsum : ∀ a : Fin (n + 1), (∑ᶠ p ∈ {p : E[X] × E[X] | p.1 ∈ Ell E a ∧ p.2 ∈ Ell E (n - a) ∧ IsCoprime p.1 p.2}, kap (p.1 * p.2) * chW lam (p.1 * p.2) * ∏ᶠ w ∈ S, kapOrb n w (atPl w p.1) (atPl w p.2) (f w)) = ∑ s : ∀ v, κ a v, (∏ v, ε a v (s v)) * geomSt2 S (fun v => l₁ a v (s v)) …` using `fun a => sum_identity hEL hKO hU (Nat.lt_succ_iff.1 a.2) hμ hS lam (κ a) (l₁ a) (l₂ a) (ε a) (hL a) hf (hφ a (Nat.lt_succ_iff.1 a.2)).1 (hφ a (Nat.lt_succ_iff.1 a.2)).2`. Unfold `geomU`.

Rewrite using `[← Fin.sum_univ_eq_sum_range (fun a => ∑ᶠ p ∈ {p : E[X] × E[X] | p.1 ∈ Ell E a ∧ p.2 ∈ Ell E (n - a) ∧ IsCoprime p.1 p.2}, kap (p.1 * p.2) * chW lam (p.1 * p.2) * ∏ᶠ w ∈ S, kapOrb n w (atPl w p.1) (atPl w p.2) (f w)) (n + 1), Finset.sum_congr rfl fun a _ => hsum a]`. Set `G : J → ℂ` to `fun j => c₀ j * geomSt2 S (fun v => l₁ j.1 v (j.2 v)) (fun v => l₂ j.1 v (j.2 v)) (φ j.1)`. Establish `h1 : (∑ a : Fin (n + 1), ∑ s : ∀ v, κ a v, (∏ v, ε a v (s v)) * geomSt2 S (fun v => l₁ a v (s v)) (fun v => l₂ a v (s v)) (φ a)) = ∑ j : J, G j` using `(Fintype.sum_sigma (fun j : J => G j)).symm`. Rewrite using `[h1]`. Establish `h2 : ∑ j : J, G j = ∑ i : {j : J // c₀ j ≠ 0}, G i.1`.

Rewrite using `[← Finset.sum_subtype (Finset.univ.filter fun j => c₀ j ≠ 0) (by simp) G, Finset.sum_filter_of_ne]`. Introduce `j _ h`. Conclude with `left_ne_zero_of_mul h`. Conclude with `h2`.
-/
theorem g2c : EllLocal → KapOrbAE → ChWMap → GlobalComplexCoefficients := by
  intro hEL hKO _ E _ _ _ hU n _ μ e hμ lam
  have hl : ∀ (a : Fin (n + 1)) (v : InfinitePlace E), _ := fun a v =>
    laplace_cast n a (Nat.lt_succ_iff.1 a.2) (lam v) (e v) (hμ.2.2.2.1 v)
  choose κ inst l₁ l₂ ε hinf hL using hl
  letI : ∀ a v, Fintype (κ a v) := inst
  let J : Type := Σ a : Fin (n + 1), ∀ v, κ a v
  let c₀ : J → ℂ := fun j => ∏ v, ε j.1 v (j.2 v)
  refine ⟨{j : J // c₀ j ≠ 0}, inferInstance, fun i => i.1.1, fun i v => l₁ i.1.1 v (i.1.2 v),
    fun i v => l₂ i.1.1 v (i.1.2 v), fun i => c₀ i.1, fun i => ⟨i.2, Nat.lt_succ_iff.1 i.1.1.2, fun v => hinf _ _ _⟩, ?_⟩
  intro S hS K' f φ _ hf hφ
  have hsum : ∀ a : Fin (n + 1), (∑ᶠ p ∈ {p : E[X] × E[X] | p.1 ∈ Ell E a ∧ p.2 ∈ Ell E (n - a) ∧ IsCoprime p.1 p.2},
        kap (p.1 * p.2) * chW lam (p.1 * p.2) * ∏ᶠ w ∈ S, kapOrb n w (atPl w p.1) (atPl w p.2) (f w)) =
      ∑ s : ∀ v, κ a v, (∏ v, ε a v (s v)) * geomSt2 S (fun v => l₁ a v (s v)) (fun v => l₂ a v (s v)) (φ a) := fun a =>
    sum_identity hEL hKO hU (Nat.lt_succ_iff.1 a.2) hμ hS lam (κ a) (l₁ a) (l₂ a) (ε a) (hL a) hf
      (hφ a (Nat.lt_succ_iff.1 a.2)).1 (hφ a (Nat.lt_succ_iff.1 a.2)).2
  unfold geomU
  rw [← Fin.sum_univ_eq_sum_range (fun a => ∑ᶠ p ∈ {p : E[X] × E[X] | p.1 ∈ Ell E a ∧ p.2 ∈ Ell E (n - a) ∧ IsCoprime p.1 p.2},
        kap (p.1 * p.2) * chW lam (p.1 * p.2) * ∏ᶠ w ∈ S, kapOrb n w (atPl w p.1) (atPl w p.2) (f w)) (n + 1),
    Finset.sum_congr rfl fun a _ => hsum a]
  let G : J → ℂ := fun j => c₀ j * geomSt2 S (fun v => l₁ j.1 v (j.2 v)) (fun v => l₂ j.1 v (j.2 v)) (φ j.1)
  have h1 : (∑ a : Fin (n + 1), ∑ s : ∀ v, κ a v, (∏ v, ε a v (s v)) *
      geomSt2 S (fun v => l₁ a v (s v)) (fun v => l₂ a v (s v)) (φ a)) = ∑ j : J, G j :=
    (Fintype.sum_sigma (fun j : J => G j)).symm
  rw [h1]
  have h2 : ∑ j : J, G j = ∑ i : {j : J // c₀ j ≠ 0}, G i.1 := by
    rw [← Finset.sum_subtype (Finset.univ.filter fun j => c₀ j ≠ 0) (by simp) G, Finset.sum_filter_of_ne]
    intro j _ h
    exact left_ne_zero_of_mul h
  exact h2

end GlobalTheory.CompanionTheory.resultantFactorHypotheses

end
