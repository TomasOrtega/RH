import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.DeltaProdAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.EllCsr
import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.DeltaProd
import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.LpolTwist

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Use `⟨hs.inter_of_right _, ?_⟩` and prove the remaining obligations. Establish `hk : (S ∩ Function.mulSupport k).Finite`. Use `(hs.union hd).subset ?_` and prove the remaining obligations. Introduce and unpack `w ⟨hw, hkw⟩`. Assume the negation of the conclusion as `hn`.

Simplify using `only [Set.mem_union, Function.mem_mulSupport, not_or, not_not] at hn`. Use `h w hw` as an intermediate fact. Rewrite `this` using `[hn.1, hn.2, one_mul]`. Conclude with `hkw this.symm`. Rewrite using `[finprod_mem_congr rfl h, finprod_mem_mul_distrib' (hd.inter_of_right _) hk, ← mul_assoc, mul_comm c, hc, one_mul]`.
-/
private theorem finprod_termIdentity {ι : Type} (S : Set ι) (s d k : ι → ℂ) (c : ℂ) (hs : (Function.mulSupport s).Finite)
    (hd : (Function.mulSupport d).Finite) (h : ∀ w ∈ S, s w = d w * k w) (hc : (∏ᶠ w ∈ S, d w) * c = 1) :
    (S ∩ Function.mulSupport s).Finite ∧ ∏ᶠ w ∈ S, k w = c * ∏ᶠ w ∈ S, s w := by
  refine ⟨hs.inter_of_right _, ?_⟩
  have hk : (S ∩ Function.mulSupport k).Finite := by
    refine (hs.union hd).subset ?_
    rintro w ⟨hw, hkw⟩
    by_contra hn
    simp only [Set.mem_union, Function.mem_mulSupport, not_or, not_not] at hn
    have := h w hw
    rw [hn.1, hn.2, one_mul] at this
    exact hkw this.symm
  rw [finprod_mem_congr rfl h, finprod_mem_mul_distrib' (hd.inter_of_right _) hk, ← mul_assoc, mul_comm c, hc, one_mul]

/- English proof (translation)
Introduce `E _ _ _ hE μ e hμ S hS n a b f φ hφ hM P₁ P₂ h₁ h₂ hco`. Take `⟨hd, hc⟩` from `UpperTheory.ConvolutionTheory.G2.deltaProd E hE μ e hμ S hS a b P₁ P₂ h₁ h₂ hco`. Establish `hst` using `UpperTheory.ConvolutionTheory.G2.stAA E hE a b P₁ P₂ h₁ h₂`. Establish `hc₁` using `(UpperTheory.ConvolutionTheory.G2.ellCsr E hE a P₁ h₁).2.2`. Establish `hc₂` using `(UpperTheory.ConvolutionTheory.G2.ellCsr E hE b P₂ h₂).2.2`.

Use `finprod_termIdentity S _ _ _ _ ?_ hd ?_ hc` and prove the remaining obligations. Establish `: ∀ᶠ w : Pl E in cofinite, stTw2 a b w (atPl w P₁) (atPl w P₂) (φ w) = 1` using `by filter_upwards [hφ, hst] with w h1 h2`. Rewrite using `[h1, h2]`. Conclude with `Filter.eventually_cofinite.1 this`. Introduce `w hw`.

Use `hM w hw _ _ (h₁.1.map _) (h₂.1.map _) ?_ ?_ ?_ (hc₁ w) (hc₂ w)` and prove the remaining obligations. Rewrite using `[h₁.1.natDegree_map, h₁.2.1]`. Rewrite using `[h₂.1.natDegree_map, h₂.2.1]`. Rewrite using `[← Polynomial.map_mul]`. Conclude with `(h₁.2.2.1.mul h₂.2.2.1 hco).map`.
-/
theorem UpperTheory.ConvolutionTheory.G2.termId :
    UpperTheory.ConvolutionTheory.G2.TermId := by
  intro E _ _ _ hE μ e hμ S hS n a b f φ hφ hM P₁ P₂ h₁ h₂ hco
  obtain ⟨hd, hc⟩ := UpperTheory.ConvolutionTheory.G2.deltaProd E hE μ e hμ S hS a b P₁ P₂ h₁ h₂ hco
  have hst := UpperTheory.ConvolutionTheory.G2.stAA E hE a b P₁ P₂ h₁ h₂
  have hc₁ := (UpperTheory.ConvolutionTheory.G2.ellCsr E hE a P₁ h₁).2.2
  have hc₂ := (UpperTheory.ConvolutionTheory.G2.ellCsr E hE b P₂ h₂).2.2
  refine finprod_termIdentity S _ _ _ _ ?_ hd ?_ hc
  · have : ∀ᶠ w : Pl E in cofinite, stTw2 a b w (atPl w P₁) (atPl w P₂) (φ w) = 1 := by
      filter_upwards [hφ, hst] with w h1 h2
      rw [h1, h2]
    exact Filter.eventually_cofinite.1 this
  · intro w hw
    refine hM w hw _ _ (h₁.1.map _) (h₂.1.map _) ?_ ?_ ?_ (hc₁ w) (hc₂ w)
    · rw [h₁.1.natDegree_map, h₁.2.1]
    · rw [h₂.1.natDegree_map, h₂.2.1]
    · rw [← Polynomial.map_mul]
      exact (h₁.2.2.1.mul h₂.2.2.1 hco).map
