import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionRows.AsmBound

noncomputable section

namespace PI.DvRows

open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv Formalism.LFunctionChainParameters.LLcv

def Adapted : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K] [IsGalois ℚ K]
    (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K), Hyp K A e n h →
    ∀ U : Submodule K A.V, U ≤ LinearMap.range e →
    ∃ (k d : ℕ) (u : Fin k → A.V) (z : Fin d → A.V) (y : Fin d → A.V),
      LinearIndependent K (Fin.append u z) ∧
      Submodule.span K (Set.range (Fin.append u z)) = LinearMap.range e ∧
      Submodule.span K (Set.range u) = U ∧
      (∀ i, Fin.append u z i ∈ cutE A e A.L) ∧
      LinearIndependent K y ∧ (∀ i, y i ∈ lamSub A e h U) ∧
      Submodule.span K (lamSub A e h U : Set A.V) = Submodule.span K (Set.range y) ∧
      (cutE A e A.L).FG ∧ (cutE A e A.L ⊓ U.restrictScalars (𝓞 K)).FG ∧
      Submodule.span K (cutE A e A.L : Set A.V) = Submodule.span K (Set.range (Fin.append u z)) ∧
      Submodule.span K ((cutE A e A.L ⊓ U.restrictScalars (𝓞 K) : Submodule (𝓞 K) A.V) : Set A.V) =
        Submodule.span K (Set.range u)

/- English proof (translation)
Establish `: u = Fin.append u z ∘ Fin.castAdd d` using `by funext i; simp`. Rewrite using `[this]`. Conclude with `h.comp _ (Fin.castAdd_injective k d)`.
-/
lemma linInd_left {K V : Type} [Field K] [AddCommGroup V] [Module K V] {k d : ℕ} (u : Fin k → V)
    (z : Fin d → V) (h : LinearIndependent K (Fin.append u z)) : LinearIndependent K u := by
  have : u = Fin.append u z ∘ Fin.castAdd d := by funext i; simp
  rw [this]
  exact h.comp _ (Fin.castAdd_injective k d)

/- English proof (translation)
Introduce `K _ _ _ _ _ A e n h hS hP hH hC U hU`. Establish `hyp : Hyp K A e n h` using `⟨hS, hP, hH, hC⟩`. Take `⟨k, d, u, z, y, hlin, hspz, hspu, hzM, hy, hyM, hspy, hMfg, hSfg, hspM, hspS⟩` from `hAd K A e n h hyp U hU`. Establish `hfg` using `hFG K A e n h hyp U hU`. Establish `hu : LinearIndependent K u` using `linInd_left u z hlin`.

Use `set M := cutE A e A.L with hM`. Use `set S := cutE A e A.L ⊓ U.restrictScalars (𝓞 K) with hS'`. Use `set Λ := lamSub A e h U with hΛ`. Rewrite using `[degL_eq_neg_lcv A hP.1 S hSfg u hu hspS, degL_eq_neg_lcv A hP.1 M hMfg _ hlin hspM, degL_eq_neg_lcv A hP.1 Λ hfg y hy hspy]`. Establish `hyU : ∀ i, ∀ x ∈ U, h (y i) x = 0` using `fun i => (hyM i).2.1`.

Establish `hye : ∀ i, y i ∈ LinearMap.range e` using `fun i => (hyM i).1`. Establish `harch` using `hAI K A e n h hyp U hU k d u z y hlin hspz hspu hy hye hyU`. Take `⟨c, hcinv, hc⟩` from `hCP K`. Establish `hlwc : ∀ w, lw K (c w) = lw K w` using `fun w => by unfold lw; rw [(hc w).2]`. Use `set D := (Matrix.of fun i j => h (y i) (z j)).det with hD`.

Use `set zf := Fin.append u z with hzf`. Use `set Ly := Submodule.span (𝓞 K) (Set.range y)`. Use `set Lz := Submodule.span (𝓞 K) (Set.range zf)`. Use `set Lu := Submodule.span (𝓞 K) (Set.range u)`. Establish `hloc : ∀ w, (vAdd w D : ℝ) + (Formalism.HermitianLatticesTheory.lidx (c w).asIdeal Ly Λ : ℝ) + (Formalism.HermitianLatticesTheory.lidx w.asIdeal Lz M : ℝ) - (Formalism.HermitianLatticesTheory.lidx w.asIdeal Lu S : ℝ) = 0`.

Introduce `w`. Use `hLP K A e n h hyp U hU k d u z y hlin hspz hspu hzM hy hyM hspy w (c w) (hc w).1` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `fV` using `vAdd_support_finite (K := K) D`. Establish `fY` using `lidx_support_finite A hP.1 Λ hfg y hy hspy`.

Establish `fZ` using `lidx_support_finite A hP.1 M hMfg zf hlin hspM`. Establish `fU` using `lidx_support_finite A hP.1 S hSfg u hu hspS`. Use `set a : HeightOneSpectrum (𝓞 K) → ℝ := fun w => lw K w * (vAdd w D : ℝ)`. Use `set gy : HeightOneSpectrum (𝓞 K) → ℝ := fun w => lw K w * (Formalism.HermitianLatticesTheory.lidx w.asIdeal Ly Λ : ℝ)`. Use `set gz : HeightOneSpectrum (𝓞 K) → ℝ := fun w => lw K w * (Formalism.HermitianLatticesTheory.lidx w.asIdeal Lz M : ℝ)`.

Use `set gu : HeightOneSpectrum (𝓞 K) → ℝ := fun w => lw K w * (Formalism.HermitianLatticesTheory.lidx w.asIdeal Lu S : ℝ)`. Establish `sub : ∀ {x : HeightOneSpectrum (𝓞 K) → ℤ}, (Function.support x).Finite → (Function.support fun w => lw K w * (x w : ℝ)).Finite` using `fun hx => hx.subset (fun w hw => by`. Simplify using `only [Function.mem_support] at hw ⊢`. Introduce `h0`. Apply `hw` to reduce the goal to its premises.

Rewrite using `[h0]`. Use the proof step `simp)`. Establish `fa : (Function.support a).Finite` using `sub fV`. Establish `fgy : (Function.support gy).Finite` using `sub fY`. Establish `fgz : (Function.support gz).Finite` using `sub fZ`.

Establish `fgu : (Function.support gu).Finite` using `sub fU`. Establish `fgyc : (Function.support fun w => gy (c w)).Finite` using `(fgy.preimage (hcinv.injective.injOn)).subset (fun w hw => hw)`. Establish `hsum0 : (∑ᶠ w, (a w + gy (c w) + gz w - gu w)) = 0`. Establish `: (fun w => a w + gy (c w) + gz w - gu w) = fun _ => (0 : ℝ)`. Use function extensionality and compare the values at `w`.

Simplify using `only [a, gy, gz, gu]`. Rewrite using `[hlwc w]`. Use `hloc w` as an intermediate fact. Take the linear combination `lw K w * this`. Rewrite using `[this, finsum_zero]`.

Establish `hsym : (∑ᶠ w, gy (c w)) = ∑ᶠ w, gy w`. Establish `: (fun w => gy (c w)) = fun w => gy (Function.Involutive.toPerm c hcinv w)`. Use function extensionality and compare the values at `w`. Simplify using the standard rewrite rules. Rewrite using `[this]`.

Conclude with `finsum_comp_equiv (Function.Involutive.toPerm c hcinv)`. Establish `hsplit : (∑ᶠ w, (a w + gy (c w) + gz w - gu w)) = (∑ᶠ w, a w) + (∑ᶠ w, gy (c w)) + (∑ᶠ w, gz w) - ∑ᶠ w, gu w`. Rewrite using `[finsum_sub_distrib ((fa.union fgyc).union fgz |>.subset ?_) fgu, finsum_add_distrib ((fa.union fgyc).subset (Function.support_add _ _)) fgz, finsum_add_distrib fa fgyc]`. Introduce `w hw`. Simplify using `only [Function.mem_support] at hw`.

Assume the negation of the conclusion as `hn`. Simplify using `only [Set.mem_union, Function.mem_support, not_or, not_not] at hn`. Apply `hw` to reduce the goal to its premises. Rewrite using `[hn.1.1, hn.1.2, hn.2]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `hsum0` using `[hsplit, hsym]`. Establish `hnorm : Real.log |((Algebra.norm ℚ D : ℚ) : ℝ)| / (Module.finrank ℚ K : ℝ) = ∑ᶠ w, a w`. Distinguish the cases in `hD0 : D = 0`. Simplify using `only [a]`. Rewrite using `[hD0]`.

Simplify using `[vAdd]`. Conclude with `(hNF K D hD0).symm`. Unfold `lcv lcvInf`. Rewrite using `[lcvFin_eq A u, lcvFin_eq A zf, lcvFin_eq A y]`. Establish `hk` using `finrank_eq_two_nPl (K := K)`.

Establish `hnpos : (0 : ℝ) < Formalism.HN.nPl K`. Unfold `Formalism.HN.nPl`. Conclude with `Fintype.card_pos` after adjusting the coercions. Rewrite `hnorm` using `[hk]`. Establish `e1 : (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v zf).det.re - (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v u).det.re = 2 * (∑ᶠ w, a w) - (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HN.gramPl A.b A.X …`.

Rewrite using `[← hnorm, ← harch]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Express the relevant statement in the definitionally equal form `-((1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v u).det.re + 2 * ∑ᶠ w, gu w) - -((1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v zf).det.re + 2 * ∑ᶠ w, gz w) = -((1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism …`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem degDual_of (hFG : LamFG) (hAd : Adapted) (hAI : ArchIdentity) (hLP : LocalPairing)
    (hCP : ConjPrime) (hNF : NormFinsum) : DegDual := by
  intro K _ _ _ _ _ A e n h hS hP hH hC U hU
  have hyp : Hyp K A e n h := ⟨hS, hP, hH, hC⟩
  obtain ⟨k, d, u, z, y, hlin, hspz, hspu, hzM, hy, hyM, hspy, hMfg, hSfg, hspM, hspS⟩ :=
    hAd K A e n h hyp U hU
  have hfg := hFG K A e n h hyp U hU
  have hu : LinearIndependent K u := linInd_left u z hlin
  set M := cutE A e A.L with hM
  set S := cutE A e A.L ⊓ U.restrictScalars (𝓞 K) with hS'
  set Λ := lamSub A e h U with hΛ
  rw [degL_eq_neg_lcv A hP.1 S hSfg u hu hspS, degL_eq_neg_lcv A hP.1 M hMfg _ hlin hspM,
    degL_eq_neg_lcv A hP.1 Λ hfg y hy hspy]
  have hyU : ∀ i, ∀ x ∈ U, h (y i) x = 0 := fun i => (hyM i).2.1
  have hye : ∀ i, y i ∈ LinearMap.range e := fun i => (hyM i).1
  have harch := hAI K A e n h hyp U hU k d u z y hlin hspz hspu hy hye hyU
  obtain ⟨c, hcinv, hc⟩ := hCP K
  have hlwc : ∀ w, lw K (c w) = lw K w := fun w => by unfold lw; rw [(hc w).2]
  set D := (Matrix.of fun i j => h (y i) (z j)).det with hD
  set zf := Fin.append u z with hzf
  set Ly := Submodule.span (𝓞 K) (Set.range y)
  set Lz := Submodule.span (𝓞 K) (Set.range zf)
  set Lu := Submodule.span (𝓞 K) (Set.range u)
  have hloc : ∀ w, (vAdd w D : ℝ) + (Formalism.HermitianLatticesTheory.lidx (c w).asIdeal Ly Λ : ℝ) +
      (Formalism.HermitianLatticesTheory.lidx w.asIdeal Lz M : ℝ) - (Formalism.HermitianLatticesTheory.lidx w.asIdeal Lu S : ℝ) = 0 := by
    intro w
    have := hLP K A e n h hyp U hU k d u z y hlin hspz hspu hzM hy hyM hspy w (c w) (hc w).1
    exact_mod_cast this

  have fV := vAdd_support_finite (K := K) D
  have fY := lidx_support_finite A hP.1 Λ hfg y hy hspy
  have fZ := lidx_support_finite A hP.1 M hMfg zf hlin hspM
  have fU := lidx_support_finite A hP.1 S hSfg u hu hspS
  set a : HeightOneSpectrum (𝓞 K) → ℝ := fun w => lw K w * (vAdd w D : ℝ)
  set gy : HeightOneSpectrum (𝓞 K) → ℝ := fun w => lw K w * (Formalism.HermitianLatticesTheory.lidx w.asIdeal Ly Λ : ℝ)
  set gz : HeightOneSpectrum (𝓞 K) → ℝ := fun w => lw K w * (Formalism.HermitianLatticesTheory.lidx w.asIdeal Lz M : ℝ)
  set gu : HeightOneSpectrum (𝓞 K) → ℝ := fun w => lw K w * (Formalism.HermitianLatticesTheory.lidx w.asIdeal Lu S : ℝ)
  have sub : ∀ {x : HeightOneSpectrum (𝓞 K) → ℤ}, (Function.support x).Finite →
      (Function.support fun w => lw K w * (x w : ℝ)).Finite := fun hx =>
    hx.subset (fun w hw => by
      simp only [Function.mem_support] at hw ⊢
      intro h0; apply hw; rw [h0]; simp)
  have fa : (Function.support a).Finite := sub fV
  have fgy : (Function.support gy).Finite := sub fY
  have fgz : (Function.support gz).Finite := sub fZ
  have fgu : (Function.support gu).Finite := sub fU
  have fgyc : (Function.support fun w => gy (c w)).Finite :=
    (fgy.preimage (hcinv.injective.injOn)).subset (fun w hw => hw)
  have hsum0 : (∑ᶠ w, (a w + gy (c w) + gz w - gu w)) = 0 := by
    have : (fun w => a w + gy (c w) + gz w - gu w) = fun _ => (0 : ℝ) := by
      funext w
      simp only [a, gy, gz, gu]
      rw [hlwc w]
      have := hloc w
      linear_combination lw K w * this
    rw [this, finsum_zero]
  have hsym : (∑ᶠ w, gy (c w)) = ∑ᶠ w, gy w := by
    have : (fun w => gy (c w)) = fun w => gy (Function.Involutive.toPerm c hcinv w) := by
      funext w; simp
    rw [this]
    exact finsum_comp_equiv (Function.Involutive.toPerm c hcinv)
  have hsplit : (∑ᶠ w, (a w + gy (c w) + gz w - gu w)) =
      (∑ᶠ w, a w) + (∑ᶠ w, gy (c w)) + (∑ᶠ w, gz w) - ∑ᶠ w, gu w := by
    rw [finsum_sub_distrib ((fa.union fgyc).union fgz |>.subset ?_) fgu,
      finsum_add_distrib ((fa.union fgyc).subset (Function.support_add _ _)) fgz,
      finsum_add_distrib fa fgyc]
    intro w hw
    simp only [Function.mem_support] at hw
    by_contra hn
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hn
    apply hw
    rw [hn.1.1, hn.1.2, hn.2]; ring
  rw [hsplit, hsym] at hsum0

  have hnorm : Real.log |((Algebra.norm ℚ D : ℚ) : ℝ)| / (Module.finrank ℚ K : ℝ) = ∑ᶠ w, a w := by
    by_cases hD0 : D = 0
    · simp only [a]
      rw [hD0]
      simp [vAdd]
    · exact (hNF K D hD0).symm
  unfold lcv lcvInf
  rw [lcvFin_eq A u, lcvFin_eq A zf, lcvFin_eq A y]
  have hk := finrank_eq_two_nPl (K := K)
  have hnpos : (0 : ℝ) < Formalism.HN.nPl K := by
    unfold Formalism.HN.nPl
    exact_mod_cast Fintype.card_pos
  rw [hk] at hnorm
  have e1 : (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v zf).det.re -
      (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v u).det.re =
      2 * (∑ᶠ w, a w) - (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v y).det.re := by
    rw [← hnorm, ← harch]
    field_simp
    ring
  change -((1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v u).det.re + 2 * ∑ᶠ w, gu w) -
      -((1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v zf).det.re + 2 * ∑ᶠ w, gz w) =
      -((1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v y).det.re + 2 * ∑ᶠ w, gy w)
  linarith

/- English proof (translation)
The claim follows from `partB_of (degDual_of hFG hAd hAI hLP hCP hNF) (degDualBound_of hFG hCS hLG hCP hNF)`.
-/
theorem partB_of_pieces (hFG : LamFG) (hAd : Adapted) (hCS : GramCS) (hAI : ArchIdentity)
    (hLG : LocalGamma) (hLP : LocalPairing) (hCP : ConjPrime) (hNF : NormFinsum) : PartB :=
  partB_of (degDual_of hFG hAd hAI hLP hCP hNF) (degDualBound_of hFG hCS hLG hCP hNF)

/- English proof (translation)
The claim follows from `dvProjRows_of (partB_of_pieces hFG hAd hCS hAI hLG hLP hCP hNF)`.
-/
theorem dvProjRows_of_pieces (hFG : LamFG) (hAd : Adapted) (hCS : GramCS) (hAI : ArchIdentity)
    (hLG : LocalGamma) (hLP : LocalPairing) (hCP : ConjPrime) (hNF : NormFinsum) : PI.Dv.division_rows_base_level :=
  dvProjRows_of (partB_of_pieces hFG hAd hCS hAI hLG hLP hCP hNF)

end PI.DvRows
