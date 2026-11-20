import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionRows.Pieces

noncomputable section

namespace PI.DvRows

open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv Formalism.LFunctionChainParameters.LLcv

section Gen

variable {K : Type} [Field K] [NumberField K]

def hosEquiv : HeightOneSpectrum (𝓞 K) ≃ {p : Ideal (𝓞 K) // p.IsMaximal} where
  toFun w := ⟨w.asIdeal, w.isMaximal⟩
  invFun p := ⟨p.1, p.2.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField p.2 (RingOfIntegers.not_isField K)⟩
  left_inv w := by cases w; rfl
  right_inv p := rfl

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Simplify using `[vAdd, hx]`. Use `((IsDedekindDomain.HeightOneSpectrum.Support.finite (𝓞 K) x).union (IsDedekindDomain.HeightOneSpectrum.Support.finite (𝓞 K) x⁻¹)).subset ?_` and prove the remaining obligations. Introduce `w hw`. Rewrite `hw` using `[Function.mem_support]`.

Establish `hne : w.valuation K x ≠ 0` using `(Valuation.ne_zero_iff _).mpr hx`. Break down `lt_trichotomy (w.valuation K x) 1 with hlt | heq | hgt` into its components or cases. Use `right show 1 < w.valuation K x⁻¹`. Rewrite using `[map_inv₀]`. Conclude with `(one_lt_inv₀ (zero_lt_iff.mpr hne)).mpr hlt`.

Conclude with `absurd (by simp [vAdd, heq]) hw`. Use `left`. Conclude with `hgt`.
-/
lemma vAdd_support_finite (x : K) :
    (Function.support fun w : HeightOneSpectrum (𝓞 K) => vAdd w x).Finite := by
  by_cases hx : x = 0
  · simp [vAdd, hx]
  · refine ((IsDedekindDomain.HeightOneSpectrum.Support.finite (𝓞 K) x).union
        (IsDedekindDomain.HeightOneSpectrum.Support.finite (𝓞 K) x⁻¹)).subset ?_
    intro w hw
    rw [Function.mem_support] at hw
    have hne : w.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
    rcases lt_trichotomy (w.valuation K x) 1 with hlt | heq | hgt
    · right
      show 1 < w.valuation K x⁻¹
      rw [map_inv₀]
      exact (one_lt_inv₀ (zero_lt_iff.mpr hne)).mpr hlt
    · exact absurd (by simp [vAdd, heq]) hw
    · left
      exact hgt

/- English proof (translation)
Unfold `Formalism.HN.nPl`. Establish `h1` using `NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K`. Establish `h2` using `NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K`. Establish `h3` using `NumberField.IsTotallyComplex.nrRealPlaces_eq_zero K`. Rewrite using `[← h1, h2, h3]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma finrank_eq_two_nPl [NumberField.IsTotallyComplex K] :
    (Module.finrank ℚ K : ℝ) = 2 * (Formalism.HN.nPl K : ℝ) := by
  unfold Formalism.HN.nPl
  have h1 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  have h2 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
  have h3 := NumberField.IsTotallyComplex.nrRealPlaces_eq_zero K
  rw [← h1, h2, h3]
  push_cast
  ring

end Gen

section Deg

variable {K : Type} [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]

/- English proof (translation)
Unfold `degL`. Distinguish the cases in `h0 : M = ⊥`. Substitute `h0` using the available equality. Establish `hj : j = 0`. Assume the negation of the conclusion as `hj`.

Establish `hmem : y ⟨0, by omega⟩ ∈ Submodule.span K (Set.range y)` using `Submodule.subset_span ⟨_, rfl⟩`. Rewrite `hmem` using `[← hsp]`. Simplify using `at hmem`. Conclude with `hy.ne_zero _ hmem`. Substitute `hj` using the available equality.

Simplify using `[Formalism.HN.rkK, lcv, lcvInf, lcvFin, Formalism.HermitianLatticesTheory.lidx]`. Take `⟨hrk, hj, -, -, hmu⟩` from `log_covolume_slope_mu K A.V A.ι A.b A.X hG.1 j y M hy hM h0 hsp`. Rewrite using `[hmu]`. Establish `hne : (Formalism.HN.rkK M : ℝ) ≠ 0`. Rewrite using `[hrk]`.

Conclude with `hj.ne'` after adjusting the coercions. Clear the denominators using the available nonvanishing facts.
-/
lemma degL_eq_neg_lcv (A : HLat K) (hG : A.Good) (M : Submodule (𝓞 K) A.V) (hM : M.FG) {j : ℕ}
    (y : Fin j → A.V) (hy : LinearIndependent K y)
    (hsp : Submodule.span K (M : Set A.V) = Submodule.span K (Set.range y)) :
    degL A M = -lcv A.b A.X y M := by
  unfold degL
  by_cases h0 : M = ⊥
  · subst h0
    have hj : j = 0 := by
      by_contra hj
      have hmem : y ⟨0, by omega⟩ ∈ Submodule.span K (Set.range y) := Submodule.subset_span ⟨_, rfl⟩
      rw [← hsp] at hmem
      simp at hmem
      exact hy.ne_zero _ hmem
    subst hj
    simp [Formalism.HN.rkK, lcv, lcvInf, lcvFin, Formalism.HermitianLatticesTheory.lidx]
  · obtain ⟨hrk, hj, -, -, hmu⟩ := log_covolume_slope_mu K A.V A.ι A.b A.X hG.1 j y M hy hM h0 hsp
    rw [hmu]
    have hne : (Formalism.HN.rkK M : ℝ) ≠ 0 := by
      rw [hrk]
      exact_mod_cast hj.ne'
    field_simp

/- English proof (translation)
Distinguish the cases in `h0 : M = ⊥`. Substitute `h0` using the available equality. Establish `hj : j = 0`. Assume the negation of the conclusion as `hj`. Establish `hmem : y ⟨0, by omega⟩ ∈ Submodule.span K (Set.range y)` using `Submodule.subset_span ⟨_, rfl⟩`.

Rewrite `hmem` using `[← hsp]`. Simplify using `at hmem`. Conclude with `hy.ne_zero _ hmem`. Substitute `hj` using the available equality. Simplify using `[Formalism.HermitianLatticesTheory.lidx]`.

Take `⟨-, -, -, hfin, -⟩` from `log_covolume_slope_mu K A.V A.ι A.b A.X hG.1 j y M hy hM h0 hsp`. Use `(hfin.preimage (hosEquiv (K := K)).injective.injOn).subset ?_` and prove the remaining obligations. Introduce `w hw`. Conclude with `hw`.
-/
lemma lidx_support_finite (A : HLat K) (hG : A.Good) (M : Submodule (𝓞 K) A.V) (hM : M.FG) {j : ℕ}
    (y : Fin j → A.V) (hy : LinearIndependent K y)
    (hsp : Submodule.span K (M : Set A.V) = Submodule.span K (Set.range y)) :
    (Function.support fun w : HeightOneSpectrum (𝓞 K) =>
      Formalism.HermitianLatticesTheory.lidx w.asIdeal (Submodule.span (𝓞 K) (Set.range y)) M).Finite := by
  by_cases h0 : M = ⊥
  · subst h0
    have hj : j = 0 := by
      by_contra hj
      have hmem : y ⟨0, by omega⟩ ∈ Submodule.span K (Set.range y) := Submodule.subset_span ⟨_, rfl⟩
      rw [← hsp] at hmem
      simp at hmem
      exact hy.ne_zero _ hmem
    subst hj
    simp [Formalism.HermitianLatticesTheory.lidx]
  · obtain ⟨-, -, -, hfin, -⟩ := log_covolume_slope_mu K A.V A.ι A.b A.X hG.1 j y M hy hM h0 hsp
    refine (hfin.preimage (hosEquiv (K := K)).injective.injOn).subset ?_
    intro w hw
    exact hw

/- English proof (translation)
Unfold `lcvFin`. Use `congr 1`. Rewrite using `[← finsum_comp_equiv (hosEquiv (K := K))]`. Both sides reduce to the same expression.
-/
lemma lcvFin_eq (A : HLat K) {j : ℕ} (y : Fin j → A.V) (M : Submodule (𝓞 K) A.V) :
    lcvFin y M = 2 * ∑ᶠ w : HeightOneSpectrum (𝓞 K),
      lw K w * (Formalism.HermitianLatticesTheory.lidx w.asIdeal (Submodule.span (𝓞 K) (Set.range y)) M : ℝ) := by
  unfold lcvFin
  congr 1
  rw [← finsum_comp_equiv (hosEquiv (K := K))]
  rfl

end Deg

/- English proof (translation)
Introduce `K _ _ _ _ _ A e n h hS hP hH hC U hU γ hγ`. Establish `hyp : Hyp K A e n h` using `⟨hS, hP, hH, hC⟩`. Use `haveI : FiniteDimensional K A.V := Module.Finite.of_basis A.b`. Take `⟨d, y, hy, hyM, hsp⟩` from `covolume_exists K A.V (lamSub A e h U)`. Establish `hfg` using `hFG K A e n h hyp U hU`.

Rewrite using `[degL_eq_neg_lcv A hP.1 _ hfg y hy hsp]`. Take `⟨c, hcinv, hc⟩` from `hCP K`. Use `set D := (Matrix.of fun i j => h (y i) (y j)).det with hD`. Use `set L := Submodule.span (𝓞 K) (Set.range y) with hL`. Establish `hγw : ∀ w, (γ w : ℝ) = -(vAdd w D : ℝ) - (Formalism.HermitianLatticesTheory.lidx w.asIdeal L (lamSub A e h U) : ℝ) - (Formalism.HermitianLatticesTheory.lidx (c w).asIdeal L (lamSub A e h U) : ℝ)`.

Introduce `w`. Use `hLG K A e n h hyp U hU d y hy hyM hsp w (γ w) (hγ w) (c w) (hc w).1` as an intermediate fact. Rewrite using `[this]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨hD0, hcs⟩` from `hCS K A e n h hyp d y hy`. Establish `hfinV` using `vAdd_support_finite (K := K) D`. Establish `hfinL` using `lidx_support_finite A hP.1 _ hfg y hy hsp`. Use `set f : HeightOneSpectrum (𝓞 K) → ℝ := fun w => lw K w * (Formalism.HermitianLatticesTheory.lidx w.asIdeal L (lamSub A e h U) : ℝ) with hf`. Establish `hfinf : (Function.support f).Finite` using `hfinL.subset (fun w hw => by`.

Simplify using `only [Function.mem_support, hf] at hw ⊢`. Introduce `h0`. Apply `hw` to reduce the goal to its premises. Rewrite using `[h0]`. Use the proof step `simp)`.

Establish `hfinv : (Function.support fun w => lw K w * (vAdd w D : ℝ)).Finite` using `hfinV.subset (fun w hw => by`. Simplify using `only [Function.mem_support] at hw ⊢`. Introduce `h0`. Apply `hw` to reduce the goal to its premises. Rewrite using `[h0]`.

Use the proof step `simp)`. Establish `hcf : (Function.support fun w => f (c w)).Finite`. Use `(hfinf.preimage (hcinv.injective.injOn)).subset (fun w hw => hw)` and prove the remaining obligations. Establish `hsym : ∑ᶠ w, lw K w * (Formalism.HermitianLatticesTheory.lidx (c w).asIdeal L (lamSub A e h U) : ℝ) = ∑ᶠ w, f w`. Establish `h1 : (fun w => lw K w * (Formalism.HermitianLatticesTheory.lidx (c w).asIdeal L (lamSub A e h U) : ℝ)) = fun w => f (Function.Involutive.toPerm c hcinv w)`.

Use function extensionality and compare the values at `w`. Simplify using `only [hf, Function.Involutive.coe_toPerm]`. Use `congr 1`. Unfold `lw`. Rewrite using `[(hc w).2]`.

Rewrite using `[h1]`. Conclude with `finsum_comp_equiv (Function.Involutive.toPerm c hcinv)`. Establish `hsplit : ∑ᶠ w, lw K w * (γ w : ℝ) = -(∑ᶠ w, lw K w * (vAdd w D : ℝ)) - ∑ᶠ w, f w - ∑ᶠ w, lw K w * (Formalism.HermitianLatticesTheory.lidx (c w).asIdeal L (lamSub A e h U) : ℝ)`. Establish `hlwc : ∀ w, lw K (c w) = lw K w` using `fun w => by unfold lw; rw [(hc w).2]`. Establish `h1 : (fun w => lw K w * (γ w : ℝ)) = fun w => (-(lw K w * (vAdd w D : ℝ)) + -f w) + -(f (c w))`.

Use function extensionality and compare the values at `w`. Rewrite using `[hγw w]`. Simplify using `only [hf]`. Rewrite using `[hlwc w]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hA : (Function.support fun w => -(lw K w * (vAdd w D : ℝ))).Finite` using `hfinv.subset (fun w hw => by simpa using hw)`. Establish `hB : (Function.support fun w => -f w).Finite` using `hfinf.subset (fun w hw => by simpa using hw)`. Establish `hC' : (Function.support fun w => -(f (c w))).Finite` using `hcf.subset (fun w hw => by simpa using hw)`. Establish `hAB : (Function.support fun w => -(lw K w * (vAdd w D : ℝ)) + -f w).Finite` using `(hA.union hB).subset (Function.support_add _ _)`. Rewrite using `[h1, finsum_add_distrib hAB hC', finsum_add_distrib hA hB]`.

Simplify using `only [finsum_neg_distrib]`. Establish `h2 : (∑ᶠ w, f (c w)) = ∑ᶠ w, lw K w * (Formalism.HermitianLatticesTheory.lidx (c w).asIdeal L (lamSub A e h U) : ℝ)`. Use `congr 1`. Use function extensionality and compare the values at `w`. Simplify using `only [hf]`.

Rewrite using `[hlwc w]`. Rewrite using `[h2]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsplit, hsym, hNF K D hD0]`. Establish `hlcv : lcvFin y (lamSub A e h U) = 2 * ∑ᶠ w, f w` using `lcvFin_eq A y _`.

Unfold `lcv`. Rewrite using `[hlcv]`. Unfold `lcvInf`. Establish `hk` using `finrank_eq_two_nPl (K := K)`. Establish `hnpos : (0 : ℝ) < Formalism.HN.nPl K`.

Unfold `Formalism.HN.nPl`. Conclude with `Fintype.card_pos` after adjusting the coercions. Rewrite using `[hk]`. Establish `: Real.log |((Algebra.norm ℚ D : ℚ) : ℝ)| / (2 * (Formalism.HN.nPl K : ℝ)) ≤ 1 / (Formalism.HN.nPl K : ℝ) * ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v y).det.re`. Rewrite using `[div_le_iff₀ (by positivity)]`.

Use `hcs` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem degDualBound_of (hFG : LamFG) (hCS : GramCS) (hLG : LocalGamma) (hCP : ConjPrime) (hNF : NormFinsum) :
    DegDualBound := by
  intro K _ _ _ _ _ A e n h hS hP hH hC U hU γ hγ
  have hyp : Hyp K A e n h := ⟨hS, hP, hH, hC⟩
  haveI : FiniteDimensional K A.V := Module.Finite.of_basis A.b
  obtain ⟨d, y, hy, hyM, hsp⟩ := covolume_exists K A.V (lamSub A e h U)
  have hfg := hFG K A e n h hyp U hU
  rw [degL_eq_neg_lcv A hP.1 _ hfg y hy hsp]
  obtain ⟨c, hcinv, hc⟩ := hCP K
  set D := (Matrix.of fun i j => h (y i) (y j)).det with hD
  set L := Submodule.span (𝓞 K) (Set.range y) with hL
  have hγw : ∀ w, (γ w : ℝ) = -(vAdd w D : ℝ) - (Formalism.HermitianLatticesTheory.lidx w.asIdeal L (lamSub A e h U) : ℝ) -
      (Formalism.HermitianLatticesTheory.lidx (c w).asIdeal L (lamSub A e h U) : ℝ) := by
    intro w
    have := hLG K A e n h hyp U hU d y hy hyM hsp w (γ w) (hγ w) (c w) (hc w).1
    rw [this]; push_cast; ring
  obtain ⟨hD0, hcs⟩ := hCS K A e n h hyp d y hy
  have hfinV := vAdd_support_finite (K := K) D
  have hfinL := lidx_support_finite A hP.1 _ hfg y hy hsp
  set f : HeightOneSpectrum (𝓞 K) → ℝ := fun w =>
    lw K w * (Formalism.HermitianLatticesTheory.lidx w.asIdeal L (lamSub A e h U) : ℝ) with hf
  have hfinf : (Function.support f).Finite :=
    hfinL.subset (fun w hw => by
      simp only [Function.mem_support, hf] at hw ⊢
      intro h0; apply hw; rw [h0]; simp)
  have hfinv : (Function.support fun w => lw K w * (vAdd w D : ℝ)).Finite :=
    hfinV.subset (fun w hw => by
      simp only [Function.mem_support] at hw ⊢
      intro h0; apply hw; rw [h0]; simp)
  have hcf : (Function.support fun w => f (c w)).Finite := by
    refine (hfinf.preimage (hcinv.injective.injOn)).subset (fun w hw => hw)
  have hsym : ∑ᶠ w, lw K w * (Formalism.HermitianLatticesTheory.lidx (c w).asIdeal L (lamSub A e h U) : ℝ) = ∑ᶠ w, f w := by
    have h1 : (fun w => lw K w * (Formalism.HermitianLatticesTheory.lidx (c w).asIdeal L (lamSub A e h U) : ℝ)) =
        fun w => f (Function.Involutive.toPerm c hcinv w) := by
      funext w
      simp only [hf, Function.Involutive.coe_toPerm]
      congr 1
      unfold lw
      rw [(hc w).2]
    rw [h1]
    exact finsum_comp_equiv (Function.Involutive.toPerm c hcinv)
  have hsplit : ∑ᶠ w, lw K w * (γ w : ℝ) =
      -(∑ᶠ w, lw K w * (vAdd w D : ℝ)) - ∑ᶠ w, f w -
        ∑ᶠ w, lw K w * (Formalism.HermitianLatticesTheory.lidx (c w).asIdeal L (lamSub A e h U) : ℝ) := by
    have hlwc : ∀ w, lw K (c w) = lw K w := fun w => by unfold lw; rw [(hc w).2]
    have h1 : (fun w => lw K w * (γ w : ℝ)) = fun w =>
        (-(lw K w * (vAdd w D : ℝ)) + -f w) + -(f (c w)) := by
      funext w
      rw [hγw w]
      simp only [hf]
      rw [hlwc w]; ring
    have hA : (Function.support fun w => -(lw K w * (vAdd w D : ℝ))).Finite :=
      hfinv.subset (fun w hw => by simpa using hw)
    have hB : (Function.support fun w => -f w).Finite :=
      hfinf.subset (fun w hw => by simpa using hw)
    have hC' : (Function.support fun w => -(f (c w))).Finite :=
      hcf.subset (fun w hw => by simpa using hw)
    have hAB : (Function.support fun w => -(lw K w * (vAdd w D : ℝ)) + -f w).Finite :=
      (hA.union hB).subset (Function.support_add _ _)
    rw [h1, finsum_add_distrib hAB hC', finsum_add_distrib hA hB]
    simp only [finsum_neg_distrib]
    have h2 : (∑ᶠ w, f (c w)) = ∑ᶠ w, lw K w * (Formalism.HermitianLatticesTheory.lidx (c w).asIdeal L (lamSub A e h U) : ℝ) := by
      congr 1; funext w; simp only [hf]; rw [hlwc w]
    rw [h2]; ring
  rw [hsplit, hsym, hNF K D hD0]
  have hlcv : lcvFin y (lamSub A e h U) = 2 * ∑ᶠ w, f w := lcvFin_eq A y _
  unfold lcv
  rw [hlcv]
  unfold lcvInf
  have hk := finrank_eq_two_nPl (K := K)
  have hnpos : (0 : ℝ) < Formalism.HN.nPl K := by
    unfold Formalism.HN.nPl
    exact_mod_cast Fintype.card_pos
  rw [hk]
  have : Real.log |((Algebra.norm ℚ D : ℚ) : ℝ)| / (2 * (Formalism.HN.nPl K : ℝ)) ≤
      1 / (Formalism.HN.nPl K : ℝ) * ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v y).det.re := by
    rw [div_le_iff₀ (by positivity)]
    have := hcs
    field_simp
    nlinarith
  linarith

end PI.DvRows
