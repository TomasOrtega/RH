import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.GeneratedCechTieSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.DegreeOneCellEqChartUpdate
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (Cell cellMon CechC cechD locPart cechCc cechZc mIdealOver chartRingOver quotPart
  secOver GeneratedV)

noncomputable section

namespace GeneratedCechTie

open HZeroRowPlaceData

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)] {Ω : Type} [Field Ω] [Algebra S Ω] {y : (Σ k, ι k) → Ω}

/- English proof (translation)
Proceed by induction on `x using LocalizedModule.induction_on with`. Consider the case `h m t`. Proceed by induction on `x' using LocalizedModule.induction_on with`. Consider the case `h m' t'`. Take `⟨g, rfl⟩` from `Ideal.Quotient.mk_surjective m`.

Take `⟨g', rfl⟩` from `Ideal.Quotient.mk_surjective m'`. Rewrite using `[LocalizedModule.mk_mul_mk, ← map_mul, evMap_mk y hI, evMap_mk y hI, evMap_mk y hI, Submonoid.coe_mul, map_mul, map_mul, mul_div_mul_comm]`.
-/
theorem evMap_mul {I : ∀ k, Finset (ι k)} (hI : Good y I)
    (x x' : LocalizedModule (cellMon S I) (MRingOver S ι ⧸ mIdealOver S y)) :
    evMap y I (x * x') = evMap y I x * evMap y I x' := by
  induction x using LocalizedModule.induction_on with
  | h m t =>
    induction x' using LocalizedModule.induction_on with
    | h m' t' =>
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective m
      obtain ⟨g', rfl⟩ := Ideal.Quotient.mk_surjective m'
      rw [LocalizedModule.mk_mul_mk, ← map_mul, evMap_mk y hI, evMap_mk y hI, evMap_mk y hI,
        Submonoid.coe_mul, map_mul, map_mul, mul_div_mul_comm]

/- English proof (translation)
Establish `h1 : (1 : LocalizedModule (cellMon S I) (MRingOver S ι ⧸ mIdealOver S y)) = LocalizedModule.mk (Ideal.Quotient.mk (mIdealOver S y) 1) 1`. Rewrite using `[map_one, ← pow_zero (LocalizedModule.mk (1 : MRingOver S ι ⧸ mIdealOver S y) (1 : cellMon S I)), LocalizedModule.mk_pow, one_pow, one_pow]`. Rewrite using `[h1, evMap_mk y hI]`. Simplify using the standard rewrite rules.
-/
theorem evMap_one {I : ∀ k, Finset (ι k)} (hI : Good y I) :
    evMap y I (1 : LocalizedModule (cellMon S I) (MRingOver S ι ⧸ mIdealOver S y)) = 1 := by
  have h1 : (1 : LocalizedModule (cellMon S I) (MRingOver S ι ⧸ mIdealOver S y)) =
      LocalizedModule.mk (Ideal.Quotient.mk (mIdealOver S y) 1) 1 := by
    rw [map_one, ← pow_zero (LocalizedModule.mk (1 : MRingOver S ι ⧸ mIdealOver S y) (1 : cellMon S I)),
      LocalizedModule.mk_pow, one_pow, one_pow]
  rw [h1, evMap_mk y hI]
  simp

/- English proof (translation)
Establish `h1 : (1 : LocalizedModule T (MRingOver S ι ⧸ mIdealOver S y)) = LocalizedModule.mk (Ideal.Quotient.mk (mIdealOver S y) 1) 1`. Rewrite using `[map_one, ← pow_zero (LocalizedModule.mk (1 : MRingOver S ι ⧸ mIdealOver S y) (1 : T)), LocalizedModule.mk_pow, one_pow, one_pow]`. Rewrite using `[h1]`. Use `GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.mk_mem_locPart _ 1 0 (GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.isMultiHomog_one _ fun _ => rfl) ?_` and prove the remaining obligations. Use `Submodule.subset_span ⟨1, ⟨fun k => by simp, ?_⟩, rfl⟩` and prove the remaining obligations.

Conclude with `GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.isMultiHomog_one _ fun k => by simp`.
-/
theorem one_mem_locPart (T : Submonoid (MRingOver S ι)) :
    (1 : LocalizedModule T (MRingOver S ι ⧸ mIdealOver S y)) ∈
      locPart ι (quotPart S (mIdealOver S y)) T 0 := by
  have h1 : (1 : LocalizedModule T (MRingOver S ι ⧸ mIdealOver S y)) =
      LocalizedModule.mk (Ideal.Quotient.mk (mIdealOver S y) 1) 1 := by
    rw [map_one, ← pow_zero (LocalizedModule.mk (1 : MRingOver S ι ⧸ mIdealOver S y) (1 : T)),
      LocalizedModule.mk_pow, one_pow, one_pow]
  rw [h1]
  refine GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.mk_mem_locPart _ 1 0
    (GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.isMultiHomog_one _ fun _ => rfl) ?_
  refine Submodule.subset_span ⟨1, ⟨fun k => by simp, ?_⟩, rfl⟩
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.isMultiHomog_one _ fun k => by simp

/- English proof (translation)
Establish `hs' : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → s * ∏ k, y ⟨k, c k⟩ ^ (-n k) ∈ chartRingOver S y c`. Introduce `c hc`. Conclude with `(Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hs c) hc`. Establish `hlift : ∀ I : Cell K ι 0, Good y I.1 → ∃ w ∈ locPart ι (quotPart S (mIdealOver S y)) (cellMon S I.1) n, evMap y I.1 w = s` using `fun I hI => exists_lift hI (fun k => Finset.min'_mem _ (I.2.1 k)) n (hs' _ fun k => hI k _ (Finset.min'_mem _ (I.2.1 k)))`. Set `z : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) 0` to `fun I => if hI : Good y I.1 then (hlift I hI).choose else 0`.

Establish `hzC : ∀ I : Cell K ι 0, z I ∈ locPart ι (quotPart S (mIdealOver S y)) (cellMon S I.1) n`. Introduce `I`. Distinguish the cases in `hI : Good y I.1`. Simplify using `only [z, dif_pos hI]`. Conclude with `(hlift I hI).choose_spec.1`.

Simplify using `only [z, dif_neg hI]`. Conclude with `Submodule.zero_mem _`. Establish `hzv : ∀ I : Cell K ι 0, Good y I.1 → evMap y I.1 (z I) = s`. Introduce `I hI`. Simplify using `only [z, dif_pos hI]`.

Conclude with `(hlift I hI).choose_spec.2`. Establish `hzCc : z ∈ cechCc ι (quotPart S (mIdealOver S y)) n 0` using `Submodule.mem_pi.mpr fun I _ => hzC I`. Establish `hzD : cechD S ι _ 0 z = 0`. Use function extensionality and compare the values at `J`. Distinguish the cases in `hJ : Good y J.1`.

Use `evMap_injOn y hJ n (cechD_mem_locPart n 0 hzCc J) (Submodule.zero_mem _) ?_` and prove the remaining obligations. Establish `hconst : constD K ι Ω 0 (fun I => evMap y I.1 (z I)) J = constD K ι Ω 0 (fun _ => s) J` using `CechPointVanish.constD_congr J.1 0 (fun I hIJ => hzv I fun k i hi => hJ k i (hIJ k hi)) J fun k => subset_refl _`. Rewrite using `[evMap_cechD z J hJ, hconst, constD_const, Pi.zero_apply, map_zero]`. Unfold `Good at hJ push Not at hJ`. Take `⟨k, i, hi, hy0⟩` from `hJ`.

Use `subsingleton_of_bad (S := S) hi hy0` as an intermediate fact. Conclude with `@Subsingleton.elim _ this _ _`. Conclude with `⟨z, Submodule.mem_inf.mpr ⟨hzCc, hzD⟩, fun c hc => hzv (cell0 c) (good_chart hc)⟩`.
-/
theorem exists_cocycle {n : K → ℤ} {s : Ω} (hs : s ∈ secOver S y n) :
    ∃ z ∈ cechZc ι (quotPart S (mIdealOver S y)) n 0,
      ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → evMap y (chart c) (z (cell0 c)) = s := by
  have hs' : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      s * ∏ k, y ⟨k, c k⟩ ^ (-n k) ∈ chartRingOver S y c := by
    intro c hc
    exact (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hs c) hc
  have hlift : ∀ I : Cell K ι 0, Good y I.1 → ∃ w ∈ locPart ι (quotPart S (mIdealOver S y)) (cellMon S I.1) n,
      evMap y I.1 w = s := fun I hI =>
    exists_lift hI (fun k => Finset.min'_mem _ (I.2.1 k)) n
      (hs' _ fun k => hI k _ (Finset.min'_mem _ (I.2.1 k)))
  classical
  let z : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) 0 := fun I =>
    if hI : Good y I.1 then (hlift I hI).choose else 0
  have hzC : ∀ I : Cell K ι 0, z I ∈ locPart ι (quotPart S (mIdealOver S y)) (cellMon S I.1) n := by
    intro I
    by_cases hI : Good y I.1
    · simp only [z, dif_pos hI]; exact (hlift I hI).choose_spec.1
    · simp only [z, dif_neg hI]; exact Submodule.zero_mem _
  have hzv : ∀ I : Cell K ι 0, Good y I.1 → evMap y I.1 (z I) = s := by
    intro I hI
    simp only [z, dif_pos hI]
    exact (hlift I hI).choose_spec.2
  have hzCc : z ∈ cechCc ι (quotPart S (mIdealOver S y)) n 0 :=
    Submodule.mem_pi.mpr fun I _ => hzC I
  have hzD : cechD S ι _ 0 z = 0 := by
    funext J
    by_cases hJ : Good y J.1
    · refine evMap_injOn y hJ n (cechD_mem_locPart n 0 hzCc J) (Submodule.zero_mem _) ?_
      have hconst : constD K ι Ω 0 (fun I => evMap y I.1 (z I)) J = constD K ι Ω 0 (fun _ => s) J :=
        CechPointVanish.constD_congr J.1 0 (fun I hIJ => hzv I fun k i hi => hJ k i (hIJ k hi)) J
          fun k => subset_refl _
      rw [evMap_cechD z J hJ, hconst, constD_const, Pi.zero_apply, map_zero]
    · unfold Good at hJ
      push Not at hJ
      obtain ⟨k, i, hi, hy0⟩ := hJ
      have := subsingleton_of_bad (S := S) hi hy0
      exact @Subsingleton.elim _ this _ _
  exact ⟨z, Submodule.mem_inf.mpr ⟨hzCc, hzD⟩, fun c hc => hzv (cell0 c) (good_chart hc)⟩

end GeneratedCechTie

open GeneratedCechTie HZeroRowPlaceData in

/- English proof (translation)
Introduce `S _ K _ _ ι _ _ Ω _ _ y β _ hgen I`. Take `⟨n, s, hs, hgen⟩` from `hgen`. Take `⟨c, rfl⟩` from `degree_zero_cell_eq_chart I`. Distinguish the cases in `hc : ∀ k, y ⟨k, c k⟩ ≠ 0`. Use `choose z hz hzv using fun j => exists_cocycle (hs j)`.

Take `⟨u, hu, hsum⟩` from `hgen c hc`. Establish `hcI : ∀ k, c k ∈ chart c k` using `fun k => Finset.mem_singleton_self _`. Establish `hval : ∀ j, u j * (∏ k, y ⟨k, c k⟩ ^ (-β k)) * ∏ k, y ⟨k, c k⟩ ^ (-(-β) k) = u j`. Introduce `j`. Rewrite using `[mul_assoc, ← Finset.prod_mul_distrib]`.

Simplify using `only [Pi.neg_apply, neg_neg]`. Rewrite using `[Finset.prod_congr rfl fun k _ => zpow_neg_mul_zpow_self (β k) (hc k), Finset.prod_const_one, mul_one]`. Use `choose U hU hUv using fun j => exists_lift (good_chart hc) hcI (-β) (s := u j * ∏ k, y ⟨k, c k⟩ ^ (-β k)) (by rw [hval j]; exact hu j)`. Use `⟨n, z, U, hz, hU, ?_⟩` and prove the remaining obligations. Set `Z : Fin n → LocalizedModule (cellMon S (chart c)) (MRingOver S ι ⧸ mIdealOver S y)` to `fun j => z j (cell0 c)`.

Use `show ∑ j, U j * Z j = 1`. Establish `hmem : ∑ j, U j * Z j ∈ locPart ι (quotPart S (mIdealOver S y)) (cellMon S (chart c)) 0`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Establish `h` using `GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.locPart_mul (hU j) (Submodule.mem_pi.mp (Submodule.mem_inf.mp (hz j)).1 (cell0 c) (Set.mem_univ _))`. Rewrite `h` using `[neg_add_cancel]`. Then use the resulting hypothesis.

Use `evMap_injOn y (good_chart hc) 0 hmem (one_mem_locPart _) ?_` and prove the remaining obligations. Rewrite using `[evMap_one (good_chart hc), map_sum, ← hsum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[evMap_mul (good_chart hc), hUv j, show evMap y (chart c) (Z j) = s j from hzv j c hc]`. Expand and normalize the polynomial expressions, which then agree.

Use `push Not at hc`. Take `⟨k, hk⟩` from `hc`. Use `subsingleton_of_bad (S := S) (I := chart c) (Finset.mem_singleton_self (c k)) hk` as an intermediate fact. Conclude with `⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, @Subsingleton.elim _ this _ _⟩`.
-/
theorem GeneratedCechTie.proof : GeneratedCechTie.Statement := by
  intro S _ K _ _ ι _ _ Ω _ _ y β _ hgen I
  obtain ⟨n, s, hs, hgen⟩ := hgen
  obtain ⟨c, rfl⟩ := degree_zero_cell_eq_chart I
  by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
  · choose z hz hzv using fun j => exists_cocycle (hs j)
    obtain ⟨u, hu, hsum⟩ := hgen c hc
    have hcI : ∀ k, c k ∈ chart c k := fun k => Finset.mem_singleton_self _
    have hval : ∀ j, u j * (∏ k, y ⟨k, c k⟩ ^ (-β k)) * ∏ k, y ⟨k, c k⟩ ^ (-(-β) k) = u j := by
      intro j
      rw [mul_assoc, ← Finset.prod_mul_distrib]
      simp only [Pi.neg_apply, neg_neg]
      rw [Finset.prod_congr rfl fun k _ => zpow_neg_mul_zpow_self (β k) (hc k), Finset.prod_const_one,
        mul_one]
    choose U hU hUv using fun j => exists_lift (good_chart hc) hcI (-β)
      (s := u j * ∏ k, y ⟨k, c k⟩ ^ (-β k)) (by rw [hval j]; exact hu j)
    refine ⟨n, z, U, hz, hU, ?_⟩
    let Z : Fin n → LocalizedModule (cellMon S (chart c)) (MRingOver S ι ⧸ mIdealOver S y) := fun j => z j (cell0 c)
    show ∑ j, U j * Z j = 1
    have hmem : ∑ j, U j * Z j ∈ locPart ι (quotPart S (mIdealOver S y)) (cellMon S (chart c)) 0 := by
      refine Submodule.sum_mem _ fun j _ => ?_
      have h := GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.locPart_mul (hU j)
        (Submodule.mem_pi.mp (Submodule.mem_inf.mp (hz j)).1 (cell0 c) (Set.mem_univ _))
      rwa [neg_add_cancel] at h
    refine evMap_injOn y (good_chart hc) 0 hmem (one_mem_locPart _) ?_
    rw [evMap_one (good_chart hc), map_sum, ← hsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [evMap_mul (good_chart hc), hUv j, show evMap y (chart c) (Z j) = s j from hzv j c hc]
    ring
  · push Not at hc
    obtain ⟨k, hk⟩ := hc
    have := subsingleton_of_bad (S := S) (I := chart c) (Finset.mem_singleton_self (c k)) hk
    exact ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, @Subsingleton.elim _ this _ _⟩

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
