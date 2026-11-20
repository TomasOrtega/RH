import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBlockNFZeroOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOfMulUnimodular
import Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableOfRapidDecay
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.FundamentalContinuity.AdelicIsomorphismStatement
import Formalism.LocalToGlobal.Columns.RecLevelTop
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.AdelicBump

open NumberField IsDedekindDomain Topology
open scoped Classical

/- English proof (translation)
Rewrite `hB` using `[nhds_pi, Filter.mem_pi]`. Take `⟨I, -, t, ht, hsub⟩` from `hB`. Establish `hO : (⋂ i, (fun a => w₀ i + a) ⁻¹' t i) ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F)` using `Filter.iInter_mem.mpr fun i => (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using ht i)`. Take `⟨N, hN, hNO⟩` from `GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hO`. Establish `hNF : ((N : ℕ) : F) ≠ 0` using `Nat.cast_ne_zero.2 hN.ne'`.

Set `c : FiniteAdeleRing (𝓞 F) F` to `algebraMap F _ ((N : F)⁻¹)`. Establish `hcN : (N : FiniteAdeleRing (𝓞 F) F) * c = 1`. Rewrite using `[← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) N, ← map_mul, mul_inv_cancel₀ hNF, map_one]`. Establish `hNc : c * (N : FiniteAdeleRing (𝓞 F) F) = 1` using `by rw [mul_comm]; exact hcN`. Set `h : FiniteAdeleRing (𝓞 F) F ≃ₜ FiniteAdeleRing (𝓞 F) F` to `{ toFun := fun u => c * u invFun := fun u => (N : FiniteAdeleRing (𝓞 F) F) * u left_inv := fun u => by show (N : FiniteAdeleRing (𝓞 F) F) * (c * u) = u`.

Rewrite using `[← mul_assoc, hcN, one_mul]`. Use `right_inv := fun u => by show c * ((N : FiniteAdeleRing (𝓞 F) F) * u) = u`. Rewrite using `[← mul_assoc, hNc, one_mul]`. Use `continuous_toFun := continuous_const.mul continuous_id`. Use `continuous_invFun := continuous_const.mul continuous_id }`.

Establish `hint_c : IsCompact (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F))` using `Formalism.L2.Col.rlt_isCompact_intAd`. Establish `hint_o : IsOpen (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F))` using `Formalism.L2.SG.Pf.top_isOpen_intAd F`. Set `D : κ → Set (FiniteAdeleRing (𝓞 F) F)` to `fun i => (Homeomorph.subRight (w₀ i)) ⁻¹' (h ⁻¹' (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)))`. Establish `hDc : ∀ i, IsCompact (D i)` using `fun i => (Homeomorph.subRight (w₀ i)).isCompact_preimage.2 (h.isCompact_preimage.2 hint_c)`. Establish `hDo : ∀ i, IsOpen (D i)` using `fun i => (hint_o.preimage h.continuous).preimage (Homeomorph.subRight (w₀ i)).continuous`.

Establish `hint_l : IsClosed (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F))` using `(Formalism.UG.intAd F).toAddSubgroup.isClosed_of_isOpen hint_o`. Establish `hDl : ∀ i, IsClosed (D i)` using `fun i => (hint_l.preimage h.continuous).preimage (Homeomorph.subRight (w₀ i)).continuous`. Use `⟨Set.univ.pi D, isOpen_set_pi Set.finite_univ fun i _ => hDo i, isCompact_univ_pi hDc, isClosed_set_pi fun i _ => hDl i, fun i _ => ?_, fun u hu => hsub fun i _ => ?_⟩` and prove the remaining obligations. Use `show c * (w₀ i - w₀ i) ∈ (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F))`. Rewrite using `[sub_self, mul_zero]`.

Conclude with `zero_mem (Formalism.UG.intAd F)`. Establish `hi : c * (u i - w₀ i) ∈ Formalism.UG.intAd F` using `hu i (Set.mem_univ i)`. Establish `h1` using `Set.mem_iInter.mp (hNO _ hi) i`. Rewrite `h1` using `[nsmul_eq_mul, ← mul_assoc, hcN, one_mul]`. Simplify using `using h1`.
-/
theorem exists_compact_open_nhds (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {w₀ : κ → FiniteAdeleRing (𝓞 F) F} {B : Set (κ → FiniteAdeleRing (𝓞 F) F)} (hB : B ∈ 𝓝 w₀) :
    ∃ C : Set (κ → FiniteAdeleRing (𝓞 F) F), IsOpen C ∧ IsCompact C ∧ IsClosed C ∧ w₀ ∈ C ∧ C ⊆ B := by
  rw [nhds_pi, Filter.mem_pi] at hB
  obtain ⟨I, -, t, ht, hsub⟩ := hB
  have hO : (⋂ i, (fun a => w₀ i + a) ⁻¹' t i) ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) :=
    Filter.iInter_mem.mpr fun i =>
      (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using ht i)
  obtain ⟨N, hN, hNO⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hO
  have hNF : ((N : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  let c : FiniteAdeleRing (𝓞 F) F := algebraMap F _ ((N : F)⁻¹)
  have hcN : (N : FiniteAdeleRing (𝓞 F) F) * c = 1 := by
    rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) N, ← map_mul, mul_inv_cancel₀ hNF, map_one]
  have hNc : c * (N : FiniteAdeleRing (𝓞 F) F) = 1 := by rw [mul_comm]; exact hcN
  let h : FiniteAdeleRing (𝓞 F) F ≃ₜ FiniteAdeleRing (𝓞 F) F :=
    { toFun := fun u => c * u
      invFun := fun u => (N : FiniteAdeleRing (𝓞 F) F) * u
      left_inv := fun u => by
        show (N : FiniteAdeleRing (𝓞 F) F) * (c * u) = u
        rw [← mul_assoc, hcN, one_mul]
      right_inv := fun u => by
        show c * ((N : FiniteAdeleRing (𝓞 F) F) * u) = u
        rw [← mul_assoc, hNc, one_mul]
      continuous_toFun := continuous_const.mul continuous_id
      continuous_invFun := continuous_const.mul continuous_id }
  have hint_c : IsCompact (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := Formalism.L2.Col.rlt_isCompact_intAd
  have hint_o : IsOpen (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := Formalism.L2.SG.Pf.top_isOpen_intAd F
  let D : κ → Set (FiniteAdeleRing (𝓞 F) F) := fun i =>
    (Homeomorph.subRight (w₀ i)) ⁻¹' (h ⁻¹' (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)))
  have hDc : ∀ i, IsCompact (D i) := fun i =>
    (Homeomorph.subRight (w₀ i)).isCompact_preimage.2 (h.isCompact_preimage.2 hint_c)
  have hDo : ∀ i, IsOpen (D i) := fun i =>
    (hint_o.preimage h.continuous).preimage (Homeomorph.subRight (w₀ i)).continuous
  have hint_l : IsClosed (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) :=
    (Formalism.UG.intAd F).toAddSubgroup.isClosed_of_isOpen hint_o
  have hDl : ∀ i, IsClosed (D i) := fun i =>
    (hint_l.preimage h.continuous).preimage (Homeomorph.subRight (w₀ i)).continuous
  refine ⟨Set.univ.pi D, isOpen_set_pi Set.finite_univ fun i _ => hDo i, isCompact_univ_pi hDc,
    isClosed_set_pi fun i _ => hDl i, fun i _ => ?_, fun u hu => hsub fun i _ => ?_⟩
  · show c * (w₀ i - w₀ i) ∈ (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F))
    rw [sub_self, mul_zero]
    exact zero_mem (Formalism.UG.intAd F)
  · have hi : c * (u i - w₀ i) ∈ Formalism.UG.intAd F := hu i (Set.mem_univ i)
    have h1 := Set.mem_iInter.mp (hNO _ hi) i
    rw [nsmul_eq_mul, ← mul_assoc, hcN, one_mul] at h1
    simpa using h1

/- English proof (translation)
Introduce `F _ _ κ _ N hN z₀ hz₀`. Set `P : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) → (κ → AdeleRing (𝓞 F) F)` to `fun p i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i)`. Establish `hP : Continuous P` using `continuous_pi fun i => Continuous.prodMk ((GlobalTheory.Core.Rk.RapidInt.continuous_ofMixed F).comp ((continuous_apply i).comp continuous_fst)) ((continuous_apply i).comp continuous_snd)`. Set `y₀ : κ → mixedEmbedding.mixedSpace F` to `fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z₀ i).1`. Set `w₀ : κ → FiniteAdeleRing (𝓞 F) F` to `fun i => (z₀ i).2`.

Establish `hPz : ∀ z : κ → AdeleRing (𝓞 F) F, P (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1, fun i => (z i).2) = z` using `fun z =>`. Use function extensionality and compare the values at `fun i => Prod.ext (RingEquiv.symm_apply_apply _ _) rfl`. Establish `hmem : P ⁻¹' N ∈ 𝓝 (y₀, w₀)` using `(hN.preimage hP).mem_nhds (by show P (y₀, w₀) ∈ N; rw [hPz z₀]; exact hz₀)`. Take `⟨A, hA, B, hB, hAB⟩` from `mem_nhds_prod_iff.mp hmem`. Take `⟨φ, hφs, hφc, hφd, hφr, hφ1⟩` from `exists_contDiff_tsupport_subset (E := κ → mixedEmbedding.mixedSpace F) (n := ⊤) hA`.

Take `⟨C, hCo, hCc, hCcl, hwC, hCB⟩` from `exists_compact_open_nhds F hB`. Establish `hc : HasCompactSupport fun y => ((φ y : ℝ) : ℂ)` using `hφc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)`. Set `f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ` to `hc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hφd)`. Establish `hf : ∀ y, f y = ((φ y : ℝ) : ℂ)` using `fun y => rfl`. Set `g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ` to `Set.indicator C fun _ => 1`.

Establish `hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)`. Use `⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, HasCompactSupport.intro hCc fun x hx => Set.indicator_of_notMem hx _⟩` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ C`. Conclude with `⟨C, hCo, hx, fun x' hx' => by simp only [g, Set.indicator_of_mem hx, Set.indicator_of_mem hx']⟩`. Conclude with `⟨Cᶜ, hCcl.isOpen_compl, hx, fun x' hx' => by`.

Simplify using `only [g, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']⟩`. Establish `hval : ∀ z, GlobalTheory.WeilM.pureA F f g z = ((φ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1) : ℝ) : ℂ) * g (fun i => (z i).2)` using `fun z => rfl`. Establish `hgval : ∀ w, g w = ((Set.indicator C (fun _ => (1 : ℝ)) w : ℝ) : ℂ)` using `fun w => by`. Apply the tactic sequence `by_cases hw : w ∈ C <;> simp [g, hw]`. Establish `hnn : ∀ y, 0 ≤ φ y` using `fun y => (hφr ⟨y, rfl⟩).1`.

Use `⟨GlobalTheory.WeilM.pureA F f g, Submodule.subset_span ⟨f, g, hg, rfl⟩, fun z => ?_, fun z hz => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hval, hgval, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.ofReal_im]`. Conclude with `⟨mul_nonneg (hnn _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _), rfl⟩`. Rewrite using `[hval]`. Assume the negation of the conclusion as `hne`.

Establish `h1` using `left_ne_zero_of_mul hne`. Establish `h2` using `right_ne_zero_of_mul hne`. Establish `h1' : φ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1) ≠ 0` using `fun h => h1 (by rw [h]; simp)`. Establish `h2' : (fun i => (z i).2) ∈ C`. Assume the negation of the conclusion as `h`.

Conclude with `h2 (Set.indicator_of_notMem h _)`. Establish `h3` using `hAB (Set.mk_mem_prod (hφs (subset_tsupport _ h1')) (hCB h2'))`. Apply `hz` to reduce the goal to its premises. Establish `h4 : P (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1, fun i => (z i).2) ∈ N` using `h3`. Rewrite `h4` using `[hPz z]`. Then use the resulting hypothesis.

Rewrite using `[hval]`. Establish `e1 : g (fun i => (z₀ i).2) = 1` using `Set.indicator_of_mem (show w₀ ∈ C from hwC) _`. Establish `e2 : φ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z₀ i).1) = 1` using `hφ1`. Rewrite using `[e1, e2]`. Simplify using the standard rewrite rules.
-/
theorem exists_bump : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (N : Set (κ → AF F)), IsOpen N → ∀ z₀ ∈ N, ∃ Φ ∈ GlobalTheory.WeilM.schA F κ, (∀ z, 0 ≤ (Φ z).re ∧ (Φ z).im = 0) ∧ (∀ z, z ∉ N → Φ z = 0) ∧ 0 < (Φ z₀).re := by
  intro F _ _ κ _ N hN z₀ hz₀
  let P : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) → (κ → AdeleRing (𝓞 F) F) :=
    fun p i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i)
  have hP : Continuous P := continuous_pi fun i =>
    Continuous.prodMk ((GlobalTheory.Core.Rk.RapidInt.continuous_ofMixed F).comp ((continuous_apply i).comp continuous_fst))
      ((continuous_apply i).comp continuous_snd)
  let y₀ : κ → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z₀ i).1
  let w₀ : κ → FiniteAdeleRing (𝓞 F) F := fun i => (z₀ i).2
  have hPz : ∀ z : κ → AdeleRing (𝓞 F) F,
      P (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1, fun i => (z i).2) = z := fun z =>
    funext fun i => Prod.ext (RingEquiv.symm_apply_apply _ _) rfl
  have hmem : P ⁻¹' N ∈ 𝓝 (y₀, w₀) :=
    (hN.preimage hP).mem_nhds (by show P (y₀, w₀) ∈ N; rw [hPz z₀]; exact hz₀)
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hmem
  obtain ⟨φ, hφs, hφc, hφd, hφr, hφ1⟩ := exists_contDiff_tsupport_subset (E := κ → mixedEmbedding.mixedSpace F) (n := ⊤) hA
  obtain ⟨C, hCo, hCc, hCcl, hwC, hCB⟩ := exists_compact_open_nhds F hB
  have hc : HasCompactSupport fun y => ((φ y : ℝ) : ℂ) :=
    hφc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  let f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ :=
    hc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hφd)
  have hf : ∀ y, f y = ((φ y : ℝ) : ℂ) := fun y => rfl
  let g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := Set.indicator C fun _ => 1
  have hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) := by
    refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, HasCompactSupport.intro hCc fun x hx => Set.indicator_of_notMem hx _⟩
    by_cases hx : x ∈ C
    · exact ⟨C, hCo, hx, fun x' hx' => by simp only [g, Set.indicator_of_mem hx, Set.indicator_of_mem hx']⟩
    · exact ⟨Cᶜ, hCcl.isOpen_compl, hx, fun x' hx' => by
        simp only [g, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']⟩
  have hval : ∀ z, GlobalTheory.WeilM.pureA F f g z = ((φ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1) : ℝ) : ℂ) *
      g (fun i => (z i).2) := fun z => rfl
  have hgval : ∀ w, g w = ((Set.indicator C (fun _ => (1 : ℝ)) w : ℝ) : ℂ) := fun w => by
    by_cases hw : w ∈ C <;> simp [g, hw]
  have hnn : ∀ y, 0 ≤ φ y := fun y => (hφr ⟨y, rfl⟩).1
  refine ⟨GlobalTheory.WeilM.pureA F f g, Submodule.subset_span ⟨f, g, hg, rfl⟩, fun z => ?_, fun z hz => ?_, ?_⟩
  · rw [hval, hgval, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨mul_nonneg (hnn _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _), rfl⟩
  · rw [hval]
    by_contra hne
    have h1 := left_ne_zero_of_mul hne
    have h2 := right_ne_zero_of_mul hne
    have h1' : φ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1) ≠ 0 := fun h => h1 (by rw [h]; simp)
    have h2' : (fun i => (z i).2) ∈ C := by
      by_contra h
      exact h2 (Set.indicator_of_notMem h _)
    have h3 := hAB (Set.mk_mem_prod (hφs (subset_tsupport _ h1')) (hCB h2'))
    apply hz
    have h4 : P (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1, fun i => (z i).2) ∈ N := h3
    rwa [hPz z] at h4
  · rw [hval]
    have e1 : g (fun i => (z₀ i).2) = 1 := Set.indicator_of_mem (show w₀ ∈ C from hwC) _
    have e2 : φ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z₀ i).1) = 1 := hφ1
    rw [e1, e2]
    simp

end GlobalTheory.CompanionTheory.AdelicBump

end
