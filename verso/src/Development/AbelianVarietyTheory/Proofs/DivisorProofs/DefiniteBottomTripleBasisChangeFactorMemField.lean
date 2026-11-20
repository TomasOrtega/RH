import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdLatEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqProdLocalComponentsApproximating
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIdeleExistsLocalApprox
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharInvCentralFlipIdeleEqProdLocalComponents
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotFrames

open Formalism.L2.JoinChr

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

/- English proof (translation)
Take `⟨ι, h1, h2, h3⟩` from `GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D`. Take `⟨N, hN, hprod⟩` from `GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2 (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc`. Take `⟨⟨es, hes, rfl⟩, -⟩` from `he`. Establish `heT : ∀ P, ι (finPart D (∑ PP ∈ S, es PP)) P = if P ∈ S then 1 else 0`. Introduce `P`.

Rewrite using `[map_sum, map_sum, GlobalTheory.FlipCharFormula.fa_sum, Finset.sum_congr rfl (fun PP hPP => GlobalTheory.FlipCharFormula.comp_of_isIdemAt ι h1 h2 (hes PP hPP) P)]`. Conclude with `Finset.sum_ite_eq S P (fun _ => (1 : HeightOneSpectrum.adicCompletion D.host.E P))`. Establish `hinfT : infPart D (∑ PP ∈ S, es PP) = 0`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_eq_zero (fun PP hPP => GlobalTheory.FlipCharFormula.infPart_of_isIdemAt (hes PP hPP))`.

Establish `hinf : infPart D (x : AE D) = 1`. Rewrite using `[hx, map_add, map_mul, map_sub, hinfT, map_one, zero_mul, zero_add, sub_zero]`. Establish `hout : ∀ P, P ∉ S → ι (finPart D (x : AE D)) P = 1`. Introduce `P hP`. Rewrite using `[hx, map_add, map_mul, map_sub, map_one, map_add, map_mul, map_sub, map_one, GlobalTheory.FlipCharFormula.fa_add, GlobalTheory.FlipCharFormula.fa_mul, GlobalTheory.FlipCharFormula.fa_sub, GlobalTheory.FlipCharFormula.fa_one, heT, if_neg hP]`.

Simplify using the standard rewrite rules. Establish `hne : ∀ P, ι (finPart D (x : AE D)) P ≠ 0`. Introduce `P h0`. Establish `h` using `congrArg (fun z => ι (finPart D z) P) (Units.mul_inv x)`. Simplify using `only [map_mul, map_one, GlobalTheory.FlipCharFormula.fa_mul, GlobalTheory.FlipCharFormula.fa_one, h0, zero_mul] at h`.

Conclude with `zero_ne_one h`. Establish `hk : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ k : D.host.Eˣ, Valued.v (ι (finPart D (x : AE D)) P) = P.valuation D.host.E (k : D.host.E) ∧ Valued.v (ι (finPart D (x : AE D)) P - algebraMap D.host.E _ (k : D.host.E)) ≤ P.valuation D.host.E (N : D.host.E) * P.valuation D.host.E (k : …` using `fun P => by`. Take `⟨k, a, b, -⟩` from `GlobalTheory.adicCompletion_exists_unit_approx D.host.E N hN P _ (hne P)`. Conclude with `⟨k, a, b⟩`. Use `choose k hk1 hk2 using hk`.

Establish `hI : Ideal.span {((N : ℕ) : 𝓞 D.host.E)} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hN.ne'` after adjusting the coercions. Establish `key` using `hprod x hinf (S ∪ (Ideal.finite_factors hI).toFinset) k (fun P _ => ⟨hk1 P, hk2 P⟩) (fun P hP => by`. Establish `hPS : P ∉ S` using `fun h => hP (Finset.mem_union_left _ h)`.

Use `⟨by rw [hout P hPS, map_one], fun hNP => hP (Finset.mem_union_right _ ?_)⟩` and prove the remaining obligations. Rewrite using `[Set.Finite.mem_toFinset]`. Conclude with `Ideal.dvd_span_singleton.mpr hNP)`. Rewrite using `[key]`. Use `Subfield.prod_mem _ fun P _ => ?_` and prove the remaining obligations.

Rewrite using `[← SetLike.mem_coe, RingHom.coe_fieldRange]`. Conclude with `hχ P _`.
-/
theorem chr_mem_of_idemSum {K : Type} [Field K] {σ : K →+* ℂ} {D : D7} {c : (AE D)ˣ →* Circle}
    {χ : Formalism.L2.Host.HChar D.host.E} (hc : ChrEq c χ) (hχ : LocIn σ χ) {e : AE D}
    {S : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e S) (x : (AE D)ˣ) (d : AE D)
    (hx : (x : AE D) = e * d + (1 - e)) : ((c x : Circle) : ℂ) ∈ σ.fieldRange := by
  classical
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2
    (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  have heT : ∀ P, ι (finPart D (∑ PP ∈ S, es PP)) P = if P ∈ S then 1 else 0 := by
    intro P
    rw [map_sum, map_sum, GlobalTheory.FlipCharFormula.fa_sum,
      Finset.sum_congr rfl (fun PP hPP => GlobalTheory.FlipCharFormula.comp_of_isIdemAt ι h1 h2 (hes PP hPP) P)]
    exact Finset.sum_ite_eq S P (fun _ => (1 : HeightOneSpectrum.adicCompletion D.host.E P))
  have hinfT : infPart D (∑ PP ∈ S, es PP) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero (fun PP hPP => GlobalTheory.FlipCharFormula.infPart_of_isIdemAt (hes PP hPP))
  have hinf : infPart D (x : AE D) = 1 := by
    rw [hx, map_add, map_mul, map_sub, hinfT, map_one, zero_mul, zero_add, sub_zero]
  have hout : ∀ P, P ∉ S → ι (finPart D (x : AE D)) P = 1 := by
    intro P hP
    rw [hx, map_add, map_mul, map_sub, map_one, map_add, map_mul, map_sub, map_one, GlobalTheory.FlipCharFormula.fa_add,
      GlobalTheory.FlipCharFormula.fa_mul, GlobalTheory.FlipCharFormula.fa_sub, GlobalTheory.FlipCharFormula.fa_one, heT, if_neg hP]
    simp
  have hne : ∀ P, ι (finPart D (x : AE D)) P ≠ 0 := by
    intro P h0
    have h := congrArg (fun z => ι (finPart D z) P) (Units.mul_inv x)
    simp only [map_mul, map_one, GlobalTheory.FlipCharFormula.fa_mul, GlobalTheory.FlipCharFormula.fa_one, h0, zero_mul] at h
    exact zero_ne_one h
  have hk : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ k : D.host.Eˣ,
      Valued.v (ι (finPart D (x : AE D)) P) = P.valuation D.host.E (k : D.host.E) ∧
      Valued.v (ι (finPart D (x : AE D)) P - algebraMap D.host.E _ (k : D.host.E)) ≤
        P.valuation D.host.E (N : D.host.E) * P.valuation D.host.E (k : D.host.E) := fun P => by
    obtain ⟨k, a, b, -⟩ := GlobalTheory.adicCompletion_exists_unit_approx D.host.E N hN P _ (hne P)
    exact ⟨k, a, b⟩
  choose k hk1 hk2 using hk
  have hI : Ideal.span {((N : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  have key := hprod x hinf (S ∪ (Ideal.finite_factors hI).toFinset) k (fun P _ => ⟨hk1 P, hk2 P⟩)
    (fun P hP => by
      have hPS : P ∉ S := fun h => hP (Finset.mem_union_left _ h)
      refine ⟨by rw [hout P hPS, map_one], fun hNP => hP (Finset.mem_union_right _ ?_)⟩
      rw [Set.Finite.mem_toFinset]
      exact Ideal.dvd_span_singleton.mpr hNP)
  rw [key]
  refine Subfield.prod_mem _ fun P _ => ?_
  rw [← SetLike.mem_coe, RingHom.coe_fieldRange]
  exact hχ P _

set_option maxHeartbeats 800000 in

/- English proof (translation)
Introduce `D T L sc G W S μ₀ hL hN i j A A' WW Y hY t g g' h x x' y _ _ hx _ _ hx' _ _ hy`. Establish `he` using `hY.is.idem t`. Establish `hm : 1 ≤ D.R.m - (i : ℕ) ∧ D.R.m - (i : ℕ) ≤ D.R.m` using `⟨by omega, by omega⟩`. Establish `mem : ∀ (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → LocIn D.what₂.embLL χ → ∀ (u : (AE D)ˣ) (d : AE D), (u : AE D) = Y.e t * d + (1 - Y.e t) → ((c u : Circle) : ℂ) ∈ D.what₂.embLL.fieldRange` using `fun c χ hc hχ u d hu => chr_mem_of_idemSum hc hχ he u d hu`. Establish `m1` using `mem _ _ (hL.mu0 j) (hN.chars.mu0 j)`.

Establish `m2` using `mem _ _ (hL.xi t) (hN.chars.xi t)`. Establish `m3` using `mem _ _ (G.ch.chi_eq _ hm.1 hm.2) (hN.chars.chi _ hm.1 hm.2)`. Use `set a := L.mu0 ((j : ℕ) + 1)`. Use `set b := L.xi t`. Use `set c := G.ch.chi (D.R.m - (i : ℕ))`.

Use `set η := L.eta ^ (rankV D i j % 2)`. Establish `hv : ((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) x' y : Circle) : ℂ) / ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botA …`. Establish `e1 : GlobalTheory.BotFrames.botAlpha L i j t = a * b * η` using `rfl`. Establish `e2 : GlobalTheory.BotFrames.botBeta G i j = c * η` using `rfl`. Rewrite using `[e1, e2]`.

Simplify using `only [splitFacO, MonoidHom.div_apply, MonoidHom.mul_apply, Circle.coe_mul, Circle.coe_inv, Circle.coe_div]`. Establish `n1` using `Circle.coe_ne_zero (a x')`. Establish `n2` using `Circle.coe_ne_zero (b x')`. Establish `n3` using `Circle.coe_ne_zero (c x')`. Establish `n4` using `Circle.coe_ne_zero (η x')`.

Establish `n5` using `Circle.coe_ne_zero (a x)`. Establish `n6` using `Circle.coe_ne_zero (b x)`. Establish `n7` using `Circle.coe_ne_zero (c x)`. Establish `n8` using `Circle.coe_ne_zero (η x)`. Establish `n9` using `Circle.coe_ne_zero (a y)`.

Establish `n10` using `Circle.coe_ne_zero (b y)`. Establish `n11` using `Circle.coe_ne_zero (c y)`. Establish `n12` using `Circle.coe_ne_zero (η y)`. Clear the denominators using the available nonvanishing facts. Establish `hmem : (((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) x' y : Circle) : ℂ) / ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.b …`.

Rewrite using `[hv]`. Use `mul_mem (mul_mem (mul_mem (inv_mem (mul_mem (m1 _ _ hx') (m2 _ _ hx'))) (m3 _ _ hx')) (mul_mem (inv_mem (mul_mem (m1 _ _ hx) (m2 _ _ hx))) (m3 _ _ hx))) (mul_mem (mul_mem (m1 _ _ hy) (m2 _ _ hy)) (inv_mem (m3 _ _ hy)))` and prove the remaining obligations. Take `⟨z, hz⟩` from `hmem`. Establish `hne : ((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) x' y : Circle) : ℂ) / ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.bot …` using `div_ne_zero (Circle.coe_ne_zero _) (Circle.coe_ne_zero _)`. Establish `hz0 : z ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hz` using `[map_zero]`. Conclude with `hne hz.symm`. Conclude with `⟨Units.mk0 z hz0, hz⟩`.
-/
theorem factor_mem_field : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (S : GridChoice W Set.univ)
    (μ₀ : T), L.Is μ₀ → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D) (Y : Tri T A A' WW),
    IsBottomTri W i j Y → ∀ (t : T) (g : GA D A) (g' : GA D A') (h : GA D WW) (x x' y : (AE D)ˣ),
    Formalism.L2.Theta.SuppAt (Y.e t) A g → Formalism.IndefR.Lev.finE A g ∈ Formalism.L2.DIV.St Y.rA.β → Formalism.L2.Theta.IsDetAt (Y.e t) A g x →
    Formalism.L2.Theta.SuppAt (Y.e t) A' g' → Formalism.IndefR.Lev.finE A' g' ∈ Formalism.L2.DIV.St Y.rA'.β →
    Formalism.L2.Theta.IsDetAt (Y.e t) A' g' x' →
    Formalism.L2.Theta.SuppAt (Y.e t) WW h → Formalism.IndefR.Lev.finE WW h ∈ Formalism.L2.DIV.St Y.rW.β → Formalism.L2.Theta.IsDetAt (Y.e t) WW h y →
    ∃ z : D.what₂.LLˣ, D.what₂.embLL z =
      ((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) x' y : Circle)
        : ℂ) /
      ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) := by
  intro D T L sc G W S μ₀ hL hN i j A A' WW Y hY t g g' h x x' y _ _ hx _ _ hx' _ _ hy
  have he := hY.is.idem t
  have hm : 1 ≤ D.R.m - (i : ℕ) ∧ D.R.m - (i : ℕ) ≤ D.R.m := ⟨by omega, by omega⟩
  have mem : ∀ (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → LocIn D.what₂.embLL χ →
      ∀ (u : (AE D)ˣ) (d : AE D), (u : AE D) = Y.e t * d + (1 - Y.e t) → ((c u : Circle) : ℂ) ∈ D.what₂.embLL.fieldRange :=
    fun c χ hc hχ u d hu => chr_mem_of_idemSum hc hχ he u d hu
  have m1 := mem _ _ (hL.mu0 j) (hN.chars.mu0 j)
  have m2 := mem _ _ (hL.xi t) (hN.chars.xi t)
  have m3 := mem _ _ (G.ch.chi_eq _ hm.1 hm.2) (hN.chars.chi _ hm.1 hm.2)
  set a := L.mu0 ((j : ℕ) + 1)
  set b := L.xi t
  set c := G.ch.chi (D.R.m - (i : ℕ))
  set η := L.eta ^ (rankV D i j % 2)
  have hv : ((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) x' y : Circle)
        : ℂ) /
      ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) =
      ((a x' : ℂ) * b x')⁻¹ * c x' * (((a x : ℂ) * b x)⁻¹ * c x) * ((a y : ℂ) * b y * (c y : ℂ)⁻¹) := by
    have e1 : GlobalTheory.BotFrames.botAlpha L i j t = a * b * η := rfl
    have e2 : GlobalTheory.BotFrames.botBeta G i j = c * η := rfl
    rw [e1, e2]
    simp only [splitFacO, MonoidHom.div_apply, MonoidHom.mul_apply, Circle.coe_mul, Circle.coe_inv, Circle.coe_div]
    have n1 := Circle.coe_ne_zero (a x'); have n2 := Circle.coe_ne_zero (b x'); have n3 := Circle.coe_ne_zero (c x')
    have n4 := Circle.coe_ne_zero (η x'); have n5 := Circle.coe_ne_zero (a x); have n6 := Circle.coe_ne_zero (b x)
    have n7 := Circle.coe_ne_zero (c x); have n8 := Circle.coe_ne_zero (η x); have n9 := Circle.coe_ne_zero (a y)
    have n10 := Circle.coe_ne_zero (b y); have n11 := Circle.coe_ne_zero (c y); have n12 := Circle.coe_ne_zero (η y)
    field_simp
  have hmem : (((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) x' y : Circle)
        : ℂ) /
      ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ)) ∈
      D.what₂.embLL.fieldRange := by
    rw [hv]
    refine mul_mem (mul_mem (mul_mem (inv_mem (mul_mem (m1 _ _ hx') (m2 _ _ hx'))) (m3 _ _ hx'))
      (mul_mem (inv_mem (mul_mem (m1 _ _ hx) (m2 _ _ hx))) (m3 _ _ hx)))
      (mul_mem (mul_mem (m1 _ _ hy) (m2 _ _ hy)) (inv_mem (m3 _ _ hy)))
  obtain ⟨z, hz⟩ := hmem
  have hne : ((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) x' y : Circle)
        : ℂ) /
      ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) ≠ 0 :=
    div_ne_zero (Circle.coe_ne_zero _) (Circle.coe_ne_zero _)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [map_zero] at hz
    exact hne hz.symm
  exact ⟨Units.mk0 z hz0, hz⟩

end GlobalTheory.BotFrames

end
