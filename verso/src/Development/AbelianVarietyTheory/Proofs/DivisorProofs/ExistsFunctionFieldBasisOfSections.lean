import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingLocusAmpleSectionIsAffineModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionQuotientsTranscendenceBasisBasepointFreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyPowMulMemHermPairSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionAmpleTwistNonvanishingFiniteSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionsMulMemNormMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentedBundleSectionsRationalFunctionsDict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairWithSectionsRepresentsTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundlePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianRepresentativeIntegerCombination
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.FBasis

/- English proof (translation)
Take `⟨M, hM⟩` from `Pair.exists_rep k X p P a b`. Establish `hLe : IsAmpleLB (P.L.pow e).B` using `(isAmpleLB_pow_iff hL.isLB he).2 hL`. Take `⟨c, -, u, hu⟩` from `exists_sec_finite_subset_nonzeroLocus k X p D hX M (P.L.pow e) hLe {genericPoint X} (Set.finite_singleton _)`. Establish `h1` using `(Pair.rep_base k X p P).1`. Establish `h2` using `Pair.rep_pow k X p P 1 0 P.L e h1`.

Establish `h3` using `Pair.rep_pow k X p P _ _ _ c h2`. Establish `hN` using `Pair.rep_tens k X p P a b _ _ M _ hM h3`. Establish `e1 : a + (c : ℤ) * ((e : ℤ) * 1) = (e : ℤ) * c + a` using `by ring`. Establish `e2 : b + (c : ℤ) * ((e : ℤ) * 0) = b` using `by ring`. Rewrite `hN` using `[e1, e2]`.

Take `⟨f, -, hrange, -, hloc⟩` from `RepDict.rep_dict k X p P _ _ _ hN`. Establish `hmem : f u ∈ P.H ((e : ℤ) * c + a) b`. Establish `: f u ∈ Set.range f` using `Set.mem_range_self u`. Rewrite `this` using `[hrange]`. Conclude with `this`.

Take `⟨i, hi⟩ : ∃ i, genericPoint X ∈ P.L.B.U i` from `Opens.mem_iSup.1 (P.L.isLB.cover.ge (Opens.mem_top _))`. Take `⟨j, hj⟩ : ∃ j, genericPoint X ∈ P.A.B.U j` from `Opens.mem_iSup.1 (P.A.isLB.cover.ge (Opens.mem_top _))`. Establish `hU` using `(hloc u (genericPoint X) i j hi hj).1 (hu rfl)`. Use `⟨c, f u, fun h0 => ?_, hmem⟩` and prove the remaining obligations. Rewrite `hU` using `[h0]`.

Establish `z : P.loc ((e : ℤ) * c + a) b 0 i j = 0` using `by simp [Pair.loc]`. Rewrite `hU` using `[z]`. Establish `hz : ∀ x : X, ¬ UnitAt x (0 : X.functionField)`. Introduce and unpack `x ⟨w, hw, h⟩`. Conclude with `(hw.map (algebraMap _ X.functionField)).ne_zero h`.

Conclude with `hz _ hU`.
-/
theorem exists_ne_zero_mem_H (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ)
    (hX : IsArithVar p D) (P : Pair p) (hL : IsAmpleLB P.L.B) (e : ℕ) (he : 0 < e) (a b : ℤ) :
    ∃ (c : ℕ) (γ : X.functionField), γ ≠ 0 ∧ γ ∈ P.H ((e : ℤ) * c + a) b := by
  obtain ⟨M, hM⟩ := Pair.exists_rep k X p P a b
  have hLe : IsAmpleLB (P.L.pow e).B := (isAmpleLB_pow_iff hL.isLB he).2 hL
  obtain ⟨c, -, u, hu⟩ := exists_sec_finite_subset_nonzeroLocus k X p D hX M (P.L.pow e) hLe {genericPoint X}
    (Set.finite_singleton _)
  have h1 := (Pair.rep_base k X p P).1
  have h2 := Pair.rep_pow k X p P 1 0 P.L e h1
  have h3 := Pair.rep_pow k X p P _ _ _ c h2
  have hN := Pair.rep_tens k X p P a b _ _ M _ hM h3
  have e1 : a + (c : ℤ) * ((e : ℤ) * 1) = (e : ℤ) * c + a := by ring
  have e2 : b + (c : ℤ) * ((e : ℤ) * 0) = b := by ring
  rw [e1, e2] at hN
  obtain ⟨f, -, hrange, -, hloc⟩ := RepDict.rep_dict k X p P _ _ _ hN
  have hmem : f u ∈ P.H ((e : ℤ) * c + a) b := by
    have : f u ∈ Set.range f := Set.mem_range_self u
    rw [hrange] at this
    exact this
  obtain ⟨i, hi⟩ : ∃ i, genericPoint X ∈ P.L.B.U i :=
    Opens.mem_iSup.1 (P.L.isLB.cover.ge (Opens.mem_top _))
  obtain ⟨j, hj⟩ : ∃ j, genericPoint X ∈ P.A.B.U j :=
    Opens.mem_iSup.1 (P.A.isLB.cover.ge (Opens.mem_top _))
  have hU := (hloc u (genericPoint X) i j hi hj).1 (hu rfl)
  refine ⟨c, f u, fun h0 => ?_, hmem⟩
  rw [h0] at hU
  have z : P.loc ((e : ℤ) * c + a) b 0 i j = 0 := by simp [Pair.loc]
  rw [z] at hU
  have hz : ∀ x : X, ¬ UnitAt x (0 : X.functionField) := by
    rintro x ⟨w, hw, h⟩
    exact (hw.map (algebraMap _ X.functionField)).ne_zero h
  exact hz _ hU

/- English proof (translation)
Establish `hS : Algebra.adjoin F (R : Set K) = ⊤`. Use `eq_top_iff.2 fun w _ => ?_` and prove the remaining obligations. Take `⟨a, ha, b, hb, hb0, rfl⟩` from `hR w`. Establish `hbS : b ∈ Algebra.adjoin F (R : Set K)` using `Algebra.subset_adjoin hb`. Establish `hinv : b⁻¹ ∈ Algebra.adjoin F (R : Set K)` using `(Algebra.adjoin F (R : Set K)).inv_mem_of_algebraic (x := ⟨b, hbS⟩) (Algebra.IsAlgebraic.isAlgebraic (b : K))`.

Rewrite using `[div_eq_mul_inv]`. Conclude with `mul_mem (Algebra.subset_adjoin ha) hinv`. Establish `hspan : Submodule.span F (R : Set K) = ⊤`. Use `congrArg Subalgebra.toSubmodule hS` as an intermediate fact. Rewrite `this` using `[Algebra.adjoin_eq_span, Algebra.top_toSubmodule]`.

Establish `hc : (Submonoid.closure (R : Set K) : Set K) = (R : Set K)`. Conclude with `congrArg (fun s : Submonoid K => (s : Set K)) (Submonoid.closure_eq R.toSubmonoid)`. Rewrite `this` using `[hc]`. Conclude with `this`. Take `⟨s, hsR, hsspan, hli⟩` from `exists_linearIndependent F (R : Set K)`.

Rewrite `hsspan` using `[hspan]`. Set `B : Module.Basis s F K` to `Module.Basis.mk hli (by rw [Subtype.range_coe, hsspan])`. Set `E : s ≃ Fin (Module.finrank F K)` to `B.indexEquiv (Module.finBasis F K)`. Use `⟨fun i => (E.symm i : K), fun i => hsR (E.symm i).2, ?_⟩` and prove the remaining obligations. Conclude with `hli.comp _ E.symm.injective`.
-/
theorem exists_linearIndependent_of_frac {K : Type} [Field K] (F : Subfield K) [FiniteDimensional F K] (R : Subring K)
    (hR : ∀ w : K, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ w = a / b) :
    ∃ β : Fin (Module.finrank F K) → K, (∀ i, β i ∈ R) ∧ LinearIndependent F β := by
  have hS : Algebra.adjoin F (R : Set K) = ⊤ := by
    refine eq_top_iff.2 fun w _ => ?_
    obtain ⟨a, ha, b, hb, hb0, rfl⟩ := hR w
    have hbS : b ∈ Algebra.adjoin F (R : Set K) := Algebra.subset_adjoin hb
    have hinv : b⁻¹ ∈ Algebra.adjoin F (R : Set K) :=
      (Algebra.adjoin F (R : Set K)).inv_mem_of_algebraic (x := ⟨b, hbS⟩) (Algebra.IsAlgebraic.isAlgebraic (b : K))
    rw [div_eq_mul_inv]
    exact mul_mem (Algebra.subset_adjoin ha) hinv
  have hspan : Submodule.span F (R : Set K) = ⊤ := by
    have := congrArg Subalgebra.toSubmodule hS
    rw [Algebra.adjoin_eq_span, Algebra.top_toSubmodule] at this
    have hc : (Submonoid.closure (R : Set K) : Set K) = (R : Set K) := by
      exact congrArg (fun s : Submonoid K => (s : Set K)) (Submonoid.closure_eq R.toSubmonoid)
    rw [hc] at this
    exact this
  obtain ⟨s, hsR, hsspan, hli⟩ := exists_linearIndependent F (R : Set K)
  rw [hspan] at hsspan
  let B : Module.Basis s F K := Module.Basis.mk hli (by rw [Subtype.range_coe, hsspan])
  let E : s ≃ Fin (Module.finrank F K) := B.indexEquiv (Module.finBasis F K)
  refine ⟨fun i => (E.symm i : K), fun i => hsR (E.symm i).2, ?_⟩
  exact hli.comp _ E.symm.injective

end GlobalTheory.HSAmp.FBasis

namespace GlobalTheory.HSAmp

/- English proof (translation)
Introduce `k _ X _ p D hX P hL e x hx a b`. Take `⟨hne, -, hfin⟩` from `GlobalTheory.T.sectionQuotients_transcendenceBasis_basepointFree k X p D hX P hL e x hx`. Take `⟨U, hU, hUe, -, hreg, -, hfrac, -⟩` from `GlobalTheory.T.nonvanishingLocus_ample_section_isAffine_model k X p D hX P hL e (x 0) hx.pos (hx.mem 0) (hne 0)`. Take `⟨β, hβR, hβ⟩` from `FBasis.exists_linearIndependent_of_frac (ratF x) (fnOf U hU).range hfrac`. Take `⟨c₁, γ, hγ0, hγ⟩` from `FBasis.exists_ne_zero_mem_H k X p D hX P hL e hx.pos a b`.

Establish `hext : ∀ i, ∀ᶠ c : ℕ in atTop, x 0 ^ c * β i ∈ P.H ((e : ℤ) * c + 0) 0`. Introduce `i`. Use `GlobalTheory.T.eventually_pow_mul_mem_hermPairSections k X p D hX P e 0 0 (x 0) (β i) (hx.mem 0) (hne 0) fun z hz i' j _ _ => ?_` and prove the remaining obligations. Establish `e0 : P.loc 0 0 (β i) i' j = β i` using `by simp [Pair.loc]`. Rewrite using `[e0]`.

Use `(hreg (β i)).2 (hβR i) z ?_` and prove the remaining obligations. Rewrite using `[← SetLike.mem_coe, hUe]`. Conclude with `hz`. Take `⟨c₂, hc₂⟩` from `(Filter.eventually_all.2 hext).exists`. Use `⟨c₁ + c₂, fun i => γ * x 0 ^ c₂ * β i, fun i => ?_, ?_⟩` and prove the remaining obligations.

Establish `h` using `(NuMul.mul_mem_H_and_nu_mul k X p P _ _ _ _ γ (x 0 ^ c₂ * β i) hγ (hc₂ i)).1`. Establish `e1 : (e : ℤ) * c₁ + a + ((e : ℤ) * c₂ + 0) = (e : ℤ) * ((c₁ + c₂ : ℕ) : ℤ) + a` using `by push_cast; ring`. Rewrite `h` using `[e1, add_zero, ← mul_assoc]`. Conclude with `h`. Establish `ht : γ * x 0 ^ c₂ ≠ 0` using `mul_ne_zero hγ0 (pow_ne_zero _ (hne 0))`.

Conclude with `hβ.map' (LinearMap.mulLeft (ratF x) (γ * x 0 ^ c₂)) (LinearMap.ker_eq_bot.2 (mul_right_injective₀ ht))`.
-/
theorem exists_linearIndependent_mem_H : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField),
    Gens P D e x → ∀ a b : ℤ, ∃ (c : ℕ) (g : Fin (Module.finrank (ratF x) X.functionField) → X.functionField),
    (∀ i, g i ∈ P.H (e * c + a) b) ∧ LinearIndependent (ratF x) g := by
  intro k _ X _ p D hX P hL e x hx a b
  obtain ⟨hne, -, hfin⟩ := GlobalTheory.T.sectionQuotients_transcendenceBasis_basepointFree k X p D hX P hL e x hx
  obtain ⟨U, hU, hUe, -, hreg, -, hfrac, -⟩ :=
    GlobalTheory.T.nonvanishingLocus_ample_section_isAffine_model k X p D hX P hL e (x 0) hx.pos (hx.mem 0) (hne 0)
  obtain ⟨β, hβR, hβ⟩ := FBasis.exists_linearIndependent_of_frac (ratF x) (fnOf U hU).range hfrac
  obtain ⟨c₁, γ, hγ0, hγ⟩ := FBasis.exists_ne_zero_mem_H k X p D hX P hL e hx.pos a b
  have hext : ∀ i, ∀ᶠ c : ℕ in atTop, x 0 ^ c * β i ∈ P.H ((e : ℤ) * c + 0) 0 := by
    intro i
    refine GlobalTheory.T.eventually_pow_mul_mem_hermPairSections k X p D hX P e 0 0 (x 0) (β i) (hx.mem 0) (hne 0) fun z hz i' j _ _ => ?_
    have e0 : P.loc 0 0 (β i) i' j = β i := by simp [Pair.loc]
    rw [e0]
    refine (hreg (β i)).2 (hβR i) z ?_
    rw [← SetLike.mem_coe, hUe]
    exact hz
  obtain ⟨c₂, hc₂⟩ := (Filter.eventually_all.2 hext).exists
  refine ⟨c₁ + c₂, fun i => γ * x 0 ^ c₂ * β i, fun i => ?_, ?_⟩
  · have h := (NuMul.mul_mem_H_and_nu_mul k X p P _ _ _ _ γ (x 0 ^ c₂ * β i) hγ (hc₂ i)).1
    have e1 : (e : ℤ) * c₁ + a + ((e : ℤ) * c₂ + 0) = (e : ℤ) * ((c₁ + c₂ : ℕ) : ℤ) + a := by
      push_cast; ring
    rw [e1, add_zero, ← mul_assoc] at h
    exact h
  · have ht : γ * x 0 ^ c₂ ≠ 0 := mul_ne_zero hγ0 (pow_ne_zero _ (hne 0))
    exact hβ.map' (LinearMap.mulLeft (ratF x) (γ * x 0 ^ c₂))
      (LinearMap.ker_eq_bot.2 (mul_right_injective₀ ht))

end GlobalTheory.HSAmp
