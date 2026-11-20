import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IkedaPartialFourierIntegralMemAdelicSchwartz
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNonnegativeSchwartzBump

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LRowTotal

open GlobalTheory.RegSch.IkSchwartz (AEf)

/- English proof (translation)
Establish `: Module.Finite D.host.F D.host.E` using `Module.Finite.of_restrictScalars_finite ℚ _ _`. Take `⟨e0⟩` from `GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Af D.host.F)`. Set `H : (Fin a → Fin b → AEf D) ≃ₜ (Fin a × Fin b × Fin (Module.finrank D.host.F D.host.E) → Af D.host.F)` to `{ toFun := fun w k => e0 (w k.1 k.2.1) k.2.2 invFun := fun z i j => e0.symm fun l => z (i, j, l) left_inv := fun w => funext fun i => funext fun j => by simp right_inv := fun z => funext fun k => by simp continuous_toFun := continuous_pi fun k => (continuous_apply k.2.2).comp (e0 …`. Take `⟨C, hCo, hCc, hCl, hwC, hCB⟩` from `GlobalTheory.CompanionTheory.AdelicBump.exists_compact_open_nhds D.host.F (H.isOpenMap.image_mem_nhds hB)`. Conclude with `⟨H ⁻¹' C, hCo.preimage H.continuous, H.isCompact_preimage.2 hCc, hCl.preimage H.continuous, hwC, fun w hw => H.injective.mem_set_image.1 (hCB hw)⟩`.
-/
theorem finBump (D : D7) {a b : ℕ} {w₀ : Fin a → Fin b → AEf D} {B : Set (Fin a → Fin b → AEf D)} (hB : B ∈ 𝓝 w₀) :
    ∃ C : Set (Fin a → Fin b → AEf D), IsOpen C ∧ IsCompact C ∧ IsClosed C ∧ w₀ ∈ C ∧ C ⊆ B := by
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Af D.host.F)
  let H : (Fin a → Fin b → AEf D) ≃ₜ (Fin a × Fin b × Fin (Module.finrank D.host.F D.host.E) → Af D.host.F) :=
    { toFun := fun w k => e0 (w k.1 k.2.1) k.2.2
      invFun := fun z i j => e0.symm fun l => z (i, j, l)
      left_inv := fun w => funext fun i => funext fun j => by simp
      right_inv := fun z => funext fun k => by simp
      continuous_toFun := continuous_pi fun k => (continuous_apply k.2.2).comp
        (e0.continuous.comp ((continuous_apply k.2.1).comp (continuous_apply k.1)))
      continuous_invFun := continuous_pi fun i => continuous_pi fun j =>
        e0.symm.continuous.comp (continuous_pi fun l => continuous_apply (i, j, l)) }
  obtain ⟨C, hCo, hCc, hCl, hwC, hCB⟩ :=
    GlobalTheory.CompanionTheory.AdelicBump.exists_compact_open_nhds D.host.F (H.isOpenMap.image_mem_nhds hB)
  exact ⟨H ⁻¹' C, hCo.preimage H.continuous, H.isCompact_preimage.2 hCc, hCl.preimage H.continuous, hwC,
    fun w hw => H.injective.mem_set_image.1 (hCB hw)⟩

/- English proof (translation)
Take `⟨e, he⟩` from `GlobalTheory.RegSch.IkSchwartz.exists_split hθ 1 p`. Set `E'` to `e.toHomeomorph`. Establish `hE : ∀ x, E' x = e x` using `fun x => rfl`. Establish `hN' : E'.symm ⁻¹' N ∈ 𝓝 (E' y₁)` using `E'.symm.continuous.continuousAt.preimage_mem_nhds (by rw [E'.symm_apply_apply]; exact hN)`. Take `⟨A, hA, B, hB, hAB⟩` from `mem_nhds_prod_iff.mp hN'`.

Take `⟨φ, hφs, hφc, hφd, hφr, hφ1⟩` from `exists_contDiff_tsupport_subset (n := ⊤) hA`. Take `⟨C, hCo, hCc, hCcl, hwC, hCB⟩` from `finBump D hB`. Establish `hc : HasCompactSupport fun y => ((φ y : ℝ) : ℂ)` using `hφc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)`. Set `f : SchwartzMap (D.what₂.Tau → Fin 1 → Fin p → ℂ) ℂ` to `hc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hφd)`. Establish `hf : ∀ y, f y = ((φ y : ℝ) : ℂ)` using `fun y => rfl`.

Set `g : (Fin 1 → Fin p → AEf D) → ℂ` to `Set.indicator C fun _ => 1`. Establish `hgl : IsLocallyConstant g`. Use `(IsLocallyConstant.iff_exists_open _).2 fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ C`. Conclude with `⟨C, hCo, hx, fun x' hx' => by simp only [g, Set.indicator_of_mem hx, Set.indicator_of_mem hx']⟩`.

Conclude with `⟨Cᶜ, hCcl.isOpen_compl, hx, fun x' hx' => by`. Simplify using `only [g, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']⟩`. Establish `hg : g ∈ GlobalTheory.WeilM.SB (Fin 1 → Fin p → AEf D)` using `⟨hgl, HasCompactSupport.intro' hCc hCcl fun x hx => Set.indicator_of_notMem hx _⟩`. Establish `hgval : ∀ w, g w = ((Set.indicator C (fun _ => (1 : ℝ)) w : ℝ) : ℂ)` using `fun w => by`. Apply the tactic sequence `by_cases hw : w ∈ C <;> simp [g, hw]`.

Set `η : Mx D 1 p → ℂ` to `fun x => f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))`. Establish `hη : ∀ x, η x = ((φ (E' x).1 * Set.indicator C (fun _ => (1 : ℝ)) (E' x).2 : ℝ) : ℂ)` using `fun x => by`. Rewrite using `[Complex.ofReal_mul, ← hgval, ← hf, hE, he]`. Establish `hnn : ∀ y, 0 ≤ φ y` using `fun y => (hφr ⟨y, rfl⟩).1`. Establish `hK : IsCompact (E' ⁻¹' (tsupport φ ×ˢ C))` using `E'.isCompact_preimage.2 (hφc.prod hCc)`.

Establish `hKl : IsClosed (E' ⁻¹' (tsupport φ ×ˢ C))` using `((isClosed_tsupport _).prod hCcl).preimage E'.continuous`. Establish `hout : ∀ x, x ∉ E' ⁻¹' (tsupport φ ×ˢ C) → η x = 0`. Introduce `x hx`. Rewrite using `[hη]`. Simplify using `only [Set.mem_preimage, Set.mem_prod, not_and_or] at hx`.

Break down `hx with hx | hx` into its components or cases. Rewrite using `[image_eq_zero_of_notMem_tsupport hx]`. Simplify using the standard rewrite rules. Rewrite using `[Set.indicator_of_notMem hx]`. Simplify using the standard rewrite rules.

Use `⟨η, Submodule.subset_span ⟨f, g, hg, rfl⟩, ?_, HasCompactSupport.intro' hK hKl hout, fun y => ?_, fun y hy => ?_, ?_⟩` and prove the remaining obligations. Establish `: η = fun x => f (E' x).1 * g (E' x).2` using `funext fun x => by rw [hE, he]`. Rewrite using `[this]`. Conclude with `(f.continuous.comp (continuous_fst.comp E'.continuous)).mul (hgl.continuous.comp (continuous_snd.comp E'.continuous))`. Rewrite using `[hη, Complex.ofReal_re, Complex.ofReal_im]`.

Conclude with `⟨mul_nonneg (hnn _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _), rfl⟩`. Assume the negation of the conclusion as `hne`. Apply `hy` to reduce the goal to its premises. Establish `h1 : (E' y) ∈ tsupport φ ×ˢ C`. Assume the negation of the conclusion as `h`.

Conclude with `hne (hout y h)`. Establish `h2 : E' y ∈ E'.symm ⁻¹' N` using `hAB ⟨hφs h1.1, hCB h1.2⟩`. Simplify using `using h2`. Rewrite using `[hη, Complex.ofReal_re, Set.indicator_of_mem (show (E' y₁).2 ∈ C from hwC), show φ (E' y₁).1 = 1 from hφ1]`. Evaluate the numerical expressions.
-/
theorem bump1 {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (p : ℕ) (y₁ : Mx D 1 p) {N : Set (Mx D 1 p)}
    (hN : N ∈ 𝓝 y₁) : ∃ η ∈ schwartzA θ 1 p, Continuous η ∧ HasCompactSupport η ∧
      (∀ y, 0 ≤ (η y).re ∧ (η y).im = 0) ∧ (∀ y, y ∉ N → η y = 0) ∧ 0 < (η y₁).re := by
  obtain ⟨e, he⟩ := GlobalTheory.RegSch.IkSchwartz.exists_split hθ 1 p
  let E' := e.toHomeomorph
  have hE : ∀ x, E' x = e x := fun x => rfl
  have hN' : E'.symm ⁻¹' N ∈ 𝓝 (E' y₁) :=
    E'.symm.continuous.continuousAt.preimage_mem_nhds (by rw [E'.symm_apply_apply]; exact hN)
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hN'
  obtain ⟨φ, hφs, hφc, hφd, hφr, hφ1⟩ := exists_contDiff_tsupport_subset (n := ⊤) hA
  obtain ⟨C, hCo, hCc, hCcl, hwC, hCB⟩ := finBump D hB
  have hc : HasCompactSupport fun y => ((φ y : ℝ) : ℂ) := hφc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  let f : SchwartzMap (D.what₂.Tau → Fin 1 → Fin p → ℂ) ℂ :=
    hc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hφd)
  have hf : ∀ y, f y = ((φ y : ℝ) : ℂ) := fun y => rfl
  let g : (Fin 1 → Fin p → AEf D) → ℂ := Set.indicator C fun _ => 1
  have hgl : IsLocallyConstant g := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
    by_cases hx : x ∈ C
    · exact ⟨C, hCo, hx, fun x' hx' => by simp only [g, Set.indicator_of_mem hx, Set.indicator_of_mem hx']⟩
    · exact ⟨Cᶜ, hCcl.isOpen_compl, hx, fun x' hx' => by
        simp only [g, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']⟩
  have hg : g ∈ GlobalTheory.WeilM.SB (Fin 1 → Fin p → AEf D) :=
    ⟨hgl, HasCompactSupport.intro' hCc hCcl fun x hx => Set.indicator_of_notMem hx _⟩
  have hgval : ∀ w, g w = ((Set.indicator C (fun _ => (1 : ℝ)) w : ℝ) : ℂ) := fun w => by
    by_cases hw : w ∈ C <;> simp [g, hw]
  let η : Mx D 1 p → ℂ := fun x => f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))
  have hη : ∀ x, η x = ((φ (E' x).1 * Set.indicator C (fun _ => (1 : ℝ)) (E' x).2 : ℝ) : ℂ) := fun x => by
    rw [Complex.ofReal_mul, ← hgval, ← hf, hE, he]
  have hnn : ∀ y, 0 ≤ φ y := fun y => (hφr ⟨y, rfl⟩).1
  have hK : IsCompact (E' ⁻¹' (tsupport φ ×ˢ C)) := E'.isCompact_preimage.2 (hφc.prod hCc)
  have hKl : IsClosed (E' ⁻¹' (tsupport φ ×ˢ C)) := ((isClosed_tsupport _).prod hCcl).preimage E'.continuous
  have hout : ∀ x, x ∉ E' ⁻¹' (tsupport φ ×ˢ C) → η x = 0 := by
    intro x hx
    rw [hη]
    simp only [Set.mem_preimage, Set.mem_prod, not_and_or] at hx
    rcases hx with hx | hx
    · rw [image_eq_zero_of_notMem_tsupport hx]; simp
    · rw [Set.indicator_of_notMem hx]; simp
  refine ⟨η, Submodule.subset_span ⟨f, g, hg, rfl⟩, ?_, HasCompactSupport.intro' hK hKl hout, fun y => ?_, fun y hy => ?_, ?_⟩
  · have : η = fun x => f (E' x).1 * g (E' x).2 := funext fun x => by rw [hE, he]
    rw [this]
    exact (f.continuous.comp (continuous_fst.comp E'.continuous)).mul (hgl.continuous.comp (continuous_snd.comp E'.continuous))
  · rw [hη, Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨mul_nonneg (hnn _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _), rfl⟩
  · by_contra hne
    apply hy
    have h1 : (E' y) ∈ tsupport φ ×ˢ C := by
      by_contra h; exact hne (hout y h)
    have h2 : E' y ∈ E'.symm ⁻¹' N := hAB ⟨hφs h1.1, hCB h1.2⟩
    simpa using h2
  · rw [hη, Complex.ofReal_re, Set.indicator_of_mem (show (E' y₁).2 ∈ C from hwC),
      show φ (E' y₁).1 = 1 from hφ1]
    norm_num

def rowsH (D : D7) (ρ p : ℕ) : Mx D ρ p ≃ₜ (Fin ρ → Mx D 1 p) where
  toFun y i := y.submatrix (fun _ => i) id
  invFun z := fun i j => z i 0 j
  left_inv y := rfl
  right_inv z := by
    funext i a j
    fin_cases a
    rfl
  continuous_toFun := continuous_pi fun i => continuous_id.matrix_submatrix _ _
  continuous_invFun := continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply j).comp ((continuous_apply (0 : Fin 1)).comp (continuous_apply i))

/- English proof (translation)
The claim follows from `Complex.ext (by simp) (by simp [h])`.
-/
theorem real_eq {z : ℂ} (h : z.im = 0) : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [h])

end PositivityTheory.Rg.Rsw.L.LRowTotal

open PositivityTheory.Rg.Rsw.L.LRowTotal in

/- English proof (translation)
Introduce `_ _ D θ hθ ρ p μ hμ u hu horth`. Assume the negation of the conclusion as `hne`. Take `⟨y₀, hy₀⟩` from `Function.ne_iff.mp hne`. Establish `: BorelSpace (Mx D ρ p)` using `⟨rfl⟩`. Use `set c := u y₀ with hc`.

Set `U : Set (Mx D ρ p)` to `{y | 0 < (u y * conj c).re}`. Establish `hUo : IsOpen U` using `isOpen_lt continuous_const (Complex.continuous_re.comp (hu.mul continuous_const))`. Establish `hy₀U : y₀ ∈ U` using `by show 0 < (u y₀ * conj (u y₀)).re`. Rewrite using `[Complex.mul_conj, Complex.ofReal_re]`. Conclude with `Complex.normSq_pos.2 hy₀`.

Set `R` to `rowsH D ρ p`. Establish `hR : R.symm ⁻¹' U ∈ 𝓝 (R y₀)` using `R.symm.continuous.continuousAt.preimage_mem_nhds (by rw [R.symm_apply_apply]; exact hUo.mem_nhds hy₀U)`. Rewrite `hR` using `[nhds_pi, Filter.mem_pi]`. Take `⟨I, -, t, ht, hsub⟩` from `hR`. Use `choose η hηS hηc hηK hηpos hηN hηy using fun i => bump1 hθ p (R y₀ i) (ht i)`.

Establish `h0` using `horth η fun i => ⟨hηS i, hηK i⟩`. Establish `hRy : ∀ y i, y.submatrix (fun _ => i) id = R y i` using `fun y i => rfl`. Set `Pr : Mx D ρ p → ℝ` to `fun y => ∏ i, (η i (R y i)).re`. Establish `hP : ∀ y, conj (∏ i, η i (y.submatrix (fun _ => i) id)) = (Pr y : ℂ)`. Introduce `y`.

Establish `: (∏ i, η i (y.submatrix (fun _ => i) id)) = (Pr y : ℂ)`. Simplify using `only [Pr, Complex.ofReal_prod, hRy]`. Conclude with `Finset.prod_congr rfl fun i _ => real_eq (hηpos i _).2`. Rewrite using `[this, Complex.conj_ofReal]`. Set `G : Mx D ρ p → ℂ` to `fun y => conj c * (u y * conj (∏ i, η i (y.submatrix (fun _ => i) id)))`.

Establish `hG0 : ∫ y, G y ∂μ = 0`. Simplify using `only [G]`. Rewrite using `[integral_const_mul, h0, mul_zero]`. Establish `hGre : ∀ y, (G y).re = (u y * conj c).re * Pr y`. Introduce `y`.

Simplify using `only [G]`. Rewrite using `[hP, show conj c * (u y * (Pr y : ℂ)) = (u y * conj c) * (Pr y : ℂ) by ring, Complex.re_mul_ofReal]`. Establish `hGc : Continuous G`. Use `continuous_const.mul (hu.mul ?_)` and prove the remaining obligations. Use `Complex.continuous_conj.comp (continuous_finsetProd _ fun i _ => ?_)` and prove the remaining obligations.

Conclude with `(hηc i).comp ((continuous_apply i).comp R.continuous)`. Set `K : Set (Mx D ρ p)` to `R ⁻¹' Set.univ.pi fun i => tsupport (η i)`. Establish `hKc : IsCompact K` using `R.isCompact_preimage.2 (isCompact_univ_pi fun i => hηK i)`. Establish `hKl : IsClosed K` using `(isClosed_set_pi fun i _ => isClosed_tsupport _).preimage R.continuous`. Establish `hGK : HasCompactSupport G`.

Use `HasCompactSupport.intro' hKc hKl fun y hy => ?_` and prove the remaining obligations. Simplify using `only [K, Set.mem_preimage, Set.mem_univ_pi, not_forall] at hy`. Take `⟨i, hi⟩` from `hy`. Establish `: ∏ i, η i (y.submatrix (fun _ => i) id) = 0` using `Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hRy]; exact image_eq_zero_of_notMem_tsupport hi)`. Simplify using `only [G, this, map_zero, mul_zero]`.

Establish `hGi : Integrable G μ` using `hGc.integrable_of_hasCompactSupport hGK`. Establish `hpos : 0 < ∫ y, (G y).re ∂μ`. Use `(Complex.continuous_re.comp hGc).integral_pos_of_hasCompactSupport_nonneg_nonzero (hGK.comp_left Complex.zero_re) (fun y => ?_) (x := y₀) ?_` and prove the remaining obligations. Use `show 0 ≤ (G y).re`. Rewrite using `[hGre]`.

Distinguish the cases in `hPr : Pr y = 0`. Rewrite using `[hPr, mul_zero]`. Establish `hall : ∀ i, R y i ∈ t i`. Introduce `i`. Assume the negation of the conclusion as `hn`.

Apply `hPr` to reduce the goal to its premises. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hηN i _ hn, Complex.zero_re])`. Establish `hyU : y ∈ U`. Use `hsub (fun i _ => hall i)` as an intermediate fact. Simplify using `using this`.

Conclude with `mul_nonneg hyU.le (Finset.prod_nonneg fun i _ => (hηpos i _).1)`. Use `show (G y₀).re ≠ 0`. Rewrite using `[hGre]`. Conclude with `(mul_pos hy₀U (Finset.prod_pos fun i _ => hηy i)).ne'`. Use `integral_re hGi` as an intermediate fact.

Simplify using `only [RCLike.re_to_complex] at this`. Rewrite `hpos` using `[this, hG0, Complex.zero_re]`. Conclude with `lt_irrefl _ hpos`.
-/
theorem PositivityTheory.Rg.Rsw.L.rowTotal : IdemEx → BumpEx → RowTotal := by
  intro _ _ D θ hθ ρ p μ hμ u hu horth
  by_contra hne
  obtain ⟨y₀, hy₀⟩ := Function.ne_iff.mp hne
  have : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  set c := u y₀ with hc
  let U : Set (Mx D ρ p) := {y | 0 < (u y * conj c).re}
  have hUo : IsOpen U := isOpen_lt continuous_const (Complex.continuous_re.comp (hu.mul continuous_const))
  have hy₀U : y₀ ∈ U := by
    show 0 < (u y₀ * conj (u y₀)).re
    rw [Complex.mul_conj, Complex.ofReal_re]
    exact Complex.normSq_pos.2 hy₀
  let R := rowsH D ρ p
  have hR : R.symm ⁻¹' U ∈ 𝓝 (R y₀) :=
    R.symm.continuous.continuousAt.preimage_mem_nhds (by rw [R.symm_apply_apply]; exact hUo.mem_nhds hy₀U)
  rw [nhds_pi, Filter.mem_pi] at hR
  obtain ⟨I, -, t, ht, hsub⟩ := hR
  choose η hηS hηc hηK hηpos hηN hηy using fun i => bump1 hθ p (R y₀ i) (ht i)
  have h0 := horth η fun i => ⟨hηS i, hηK i⟩
  have hRy : ∀ y i, y.submatrix (fun _ => i) id = R y i := fun y i => rfl
  let Pr : Mx D ρ p → ℝ := fun y => ∏ i, (η i (R y i)).re
  have hP : ∀ y, conj (∏ i, η i (y.submatrix (fun _ => i) id)) = (Pr y : ℂ) := by
    intro y
    have : (∏ i, η i (y.submatrix (fun _ => i) id)) = (Pr y : ℂ) := by
      simp only [Pr, Complex.ofReal_prod, hRy]
      exact Finset.prod_congr rfl fun i _ => real_eq (hηpos i _).2
    rw [this, Complex.conj_ofReal]
  let G : Mx D ρ p → ℂ := fun y => conj c * (u y * conj (∏ i, η i (y.submatrix (fun _ => i) id)))
  have hG0 : ∫ y, G y ∂μ = 0 := by
    simp only [G]
    rw [integral_const_mul, h0, mul_zero]
  have hGre : ∀ y, (G y).re = (u y * conj c).re * Pr y := by
    intro y
    simp only [G]
    rw [hP, show conj c * (u y * (Pr y : ℂ)) = (u y * conj c) * (Pr y : ℂ) by ring, Complex.re_mul_ofReal]
  have hGc : Continuous G := by
    refine continuous_const.mul (hu.mul ?_)
    refine Complex.continuous_conj.comp (continuous_finsetProd _ fun i _ => ?_)
    exact (hηc i).comp ((continuous_apply i).comp R.continuous)
  let K : Set (Mx D ρ p) := R ⁻¹' Set.univ.pi fun i => tsupport (η i)
  have hKc : IsCompact K := R.isCompact_preimage.2 (isCompact_univ_pi fun i => hηK i)
  have hKl : IsClosed K := (isClosed_set_pi fun i _ => isClosed_tsupport _).preimage R.continuous
  have hGK : HasCompactSupport G := by
    refine HasCompactSupport.intro' hKc hKl fun y hy => ?_
    simp only [K, Set.mem_preimage, Set.mem_univ_pi, not_forall] at hy
    obtain ⟨i, hi⟩ := hy
    have : ∏ i, η i (y.submatrix (fun _ => i) id) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hRy]; exact image_eq_zero_of_notMem_tsupport hi)
    simp only [G, this, map_zero, mul_zero]
  have hGi : Integrable G μ := hGc.integrable_of_hasCompactSupport hGK
  have hpos : 0 < ∫ y, (G y).re ∂μ := by
    refine (Complex.continuous_re.comp hGc).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (hGK.comp_left Complex.zero_re) (fun y => ?_) (x := y₀) ?_
    · show 0 ≤ (G y).re
      rw [hGre]
      by_cases hPr : Pr y = 0
      · rw [hPr, mul_zero]
      · have hall : ∀ i, R y i ∈ t i := by
          intro i
          by_contra hn
          apply hPr
          exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hηN i _ hn, Complex.zero_re])
        have hyU : y ∈ U := by
          have := hsub (fun i _ => hall i)
          simpa using this
        exact mul_nonneg hyU.le (Finset.prod_nonneg fun i _ => (hηpos i _).1)
    · show (G y₀).re ≠ 0
      rw [hGre]
      exact (mul_pos hy₀U (Finset.prod_pos fun i _ => hηy i)).ne'
  have := integral_re hGi
  simp only [RCLike.re_to_complex] at this
  rw [this, hG0, Complex.zero_re] at hpos
  exact lt_irrefl _ hpos

end
