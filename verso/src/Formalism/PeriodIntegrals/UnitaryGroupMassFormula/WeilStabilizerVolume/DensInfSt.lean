import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.FibOfTens
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TensTop

noncomputable section

namespace PI.VolStabW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Topology
open scoped TensorProduct

def SubmDens : Prop :=
  ∀ (n m : ℕ) (μ : Measure (Fin n → ℝ)) (ν : Measure (Fin m → ℝ)), μ.IsAddHaarMeasure →
    ν.IsAddHaarMeasure → ∀ (f : (Fin n → ℝ) → (Fin m → ℝ)), ContDiff ℝ 1 f →
      DensAll μ f id ν {x | Function.Surjective (fderiv ℝ f x)}

def SubmLocal : Prop :=
  ∀ (n m : ℕ) (μ : Measure (Fin n → ℝ)) (ν : Measure (Fin m → ℝ)), μ.IsAddHaarMeasure →
    ν.IsAddHaarMeasure → ∀ (f : (Fin n → ℝ) → (Fin m → ℝ)), ContDiff ℝ 1 f →
      ∀ x0, Function.Surjective (fderiv ℝ f x0) → ∃ N, IsOpen N ∧ x0 ∈ N ∧ DensAll μ f id ν N

def CoordInf : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∃ (n m : ℕ) (eV : (Fin a → Fin M → Ainf F ⊗[F] E) ≃ₜ (Fin n → ℝ))
    (eH : HermR (Ainf F) σ a ≃ₜ (Fin m → ℝ)) (f' : (Fin n → ℝ) → (Fin m → ℝ)),
    (∀ x y, eV (x + y) = eV x + eV y) ∧ (∀ x y, eH (x + y) = eH x + eH y) ∧ ContDiff ℝ 1 f' ∧
    (∀ X, ((eH.symm (f' (eV X)) : HermR (Ainf F) σ a) : Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) =
      gramR (Ainf F) σ J X) ∧
    ∀ X, LinearIndependent (Ainf F ⊗[F] E) X → Function.Surjective (fderiv ℝ f' (eV X))

section Transport

variable {V X Y V' X' : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace V'] [MeasurableSpace V']
  [BorelSpace V'] [TopologicalSpace X'] [MeasurableSpace X'] [BorelSpace X']

/- English proof (translation)
Introduce `φ hc hs hU`. Establish `hc' : Continuous (φ ∘ eV.symm)` using `hc.comp eV.symm.continuous`. Establish `hs' : HasCompactSupport (φ ∘ eV.symm)` using `hs.comp_homeomorph eV.symm`. Establish `hU' : tsupport (φ ∘ eV.symm) ⊆ eV '' U`. Introduce `y hy`.

Establish `: eV.symm y ∈ tsupport φ`. Establish `e : tsupport (φ ∘ eV.symm) = eV.symm ⁻¹' tsupport φ`. Simplify using `using (tsupport_comp_eq_preimage φ eV.symm)`. Rewrite `hy` using `[e]`. Conclude with `hy`.

Conclude with `⟨eV.symm y, hU this, by simp⟩`. Take `⟨g', hg'c, hg'⟩` from `h _ hc' hs' hU'`. Use `⟨g' ∘ eX, hg'c.comp eX.continuous, fun S hS => ?_⟩` and prove the remaining obligations. Establish `e1` using `hg' (eX '' S) (hS.image eX.continuous)`. Rewrite `e1` using `[show ((μ.map eV)) = μ.map eV.toMeasurableEquiv from rfl, show ((ν.map eX)) = ν.map eX.toMeasurableEquiv from rfl, setIntegral_map_equiv, setIntegral_map_equiv]`.

Establish `p1 : (eV.toMeasurableEquiv : V → V') ⁻¹' (f' ⁻¹' (id '' (eX '' S))) = f ⁻¹' (ι '' S)`. Use extensionality with `v`. Simplify using `only [Set.mem_preimage, Set.image_id, Set.mem_image, Homeomorph.toMeasurableEquiv_coe]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, hxe⟩`.

Use `⟨x, hx, ?_⟩` and prove the remaining obligations. Rewrite using `[← hf v, ← hxe]`. Simplify using the standard rewrite rules. Introduce and unpack `⟨x, hx, hxe⟩`. Use `⟨x, hx, ?_⟩` and prove the remaining obligations.

Rewrite `hxe` using `[← hf v]`. Use `hι hxe` as an intermediate fact. Rewrite using `[this]`. Simplify using the standard rewrite rules. Establish `p2 : (eX.toMeasurableEquiv : X → X') ⁻¹' (eX '' S) = S`.

Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite `e1` using `[p1, p2]`. Simplify `e1` using `[Homeomorph.toMeasurableEquiv_coe]`.
-/
theorem densAll_transport (μ : Measure V) (ν : Measure X) (f : V → Y) (ι : X → Y) (U : Set V)
    (eV : V ≃ₜ V') (eX : X ≃ₜ X') (f' : V' → X') (hι : Function.Injective ι)
    (hf : ∀ v, ι (eX.symm (f' (eV v))) = f v)
    (h : DensAll (μ.map eV) f' id (ν.map eX) (eV '' U)) : DensAll μ f ι ν U := by
  intro φ hc hs hU
  have hc' : Continuous (φ ∘ eV.symm) := hc.comp eV.symm.continuous
  have hs' : HasCompactSupport (φ ∘ eV.symm) := hs.comp_homeomorph eV.symm
  have hU' : tsupport (φ ∘ eV.symm) ⊆ eV '' U := by
    intro y hy
    have : eV.symm y ∈ tsupport φ := by
      have e : tsupport (φ ∘ eV.symm) = eV.symm ⁻¹' tsupport φ := by
        simpa using (tsupport_comp_eq_preimage φ eV.symm)
      rw [e] at hy; exact hy
    exact ⟨eV.symm y, hU this, by simp⟩
  obtain ⟨g', hg'c, hg'⟩ := h _ hc' hs' hU'
  refine ⟨g' ∘ eX, hg'c.comp eX.continuous, fun S hS => ?_⟩
  have e1 := hg' (eX '' S) (hS.image eX.continuous)
  rw [show ((μ.map eV)) = μ.map eV.toMeasurableEquiv from rfl,
    show ((ν.map eX)) = ν.map eX.toMeasurableEquiv from rfl,
    setIntegral_map_equiv, setIntegral_map_equiv] at e1
  have p1 : (eV.toMeasurableEquiv : V → V') ⁻¹' (f' ⁻¹' (id '' (eX '' S))) = f ⁻¹' (ι '' S) := by
    ext v
    simp only [Set.mem_preimage, Set.image_id, Set.mem_image, Homeomorph.toMeasurableEquiv_coe]
    constructor
    · rintro ⟨x, hx, hxe⟩
      refine ⟨x, hx, ?_⟩
      rw [← hf v, ← hxe]; simp
    · rintro ⟨x, hx, hxe⟩
      refine ⟨x, hx, ?_⟩
      rw [← hf v] at hxe
      have := hι hxe
      rw [this]; simp
  have p2 : (eX.toMeasurableEquiv : X → X') ⁻¹' (eX '' S) = S := by
    ext x; simp
  rw [p1, p2] at e1
  simpa [Homeomorph.toMeasurableEquiv_coe] using e1

end Transport

section Local

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X]
  [MeasurableSpace X]

/- English proof (translation)
Introduce `φ hc hs hφ`. Conclude with `h φ hc hs (hφ.trans hU)`.
-/
theorem densAll_mono {μ : Measure V} {f : V → Y} {ι : X → Y} {ν : Measure X} {U U' : Set V}
    (h : DensAll μ f ι ν U') (hU : U ⊆ U') : DensAll μ f ι ν U := by
  intro φ hc hs hφ
  exact h φ hc hs (hφ.trans hU)

/- English proof (translation)
Introduce `φ hc hs hU`. Use `choose N hNo hNx hND using h`. Set `K` to `tsupport φ`. Establish `hK : IsCompact K` using `hs`. Take `⟨t, ht⟩` from `hK.elim_finite_subcover (fun x : K => N x.1 (hU x.2)) (fun x => hNo _ _) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hNx _ _⟩)`.

Set `n` to `t.card`. Set `N' : K → Set V` to `fun x => N x.1 (hU x.2)`. Set `s : Fin n → Set V` to `fun i => N' (t.equivFin.symm i).1`. Establish `hso : ∀ i, IsOpen (s i)` using `fun i => hNo _ _`. Establish `hcov : K ⊆ ⋃ i, s i`.

Introduce `x hx`. Take `⟨j, hj, hxj⟩` from `Set.mem_iUnion₂.1 (ht hx)`. Use `Set.mem_iUnion.2 ⟨t.equivFin ⟨j, hj⟩, ?_⟩` and prove the remaining obligations. Establish `e : s (t.equivFin ⟨j, hj⟩) = N' j` using `by simp only [s, Equiv.symm_apply_apply]`. Rewrite using `[e]`.

Conclude with `hxj`. Take `⟨ρ, hρs, hρ1, -, hρc⟩` from `exists_continuous_sum_one_of_isOpen_isCompact hso hK hcov`. Establish `hsum : ∀ x, φ x = ∑ i, φ x * ρ i x`. Introduce `x`. Distinguish the cases in `hx : x ∈ K`.

Use `hρ1 hx` as an intermediate fact. Simplify using `only [Finset.sum_apply, Pi.one_apply] at this`. Rewrite using `[← Finset.mul_sum, this, mul_one]`. Establish `: φ x = 0` using `image_eq_zero_of_notMem_tsupport hx`. Simplify using `[this]`.

Establish `hi : ∀ i, ∃ g : X → ℝ, Continuous g ∧ ∀ S : Set X, IsCompact S → ∫ v in f ⁻¹' (ι '' S), φ v * ρ i v ∂μ = ∫ b in S, g b ∂ν`. Introduce `i`. Conclude with `hND _ _ (fun v => φ v * ρ i v) (hc.mul (ρ i).continuous) (hs.mul_right) ((tsupport_mul_subset_right).trans (hρs i))`. Use `choose g hgc hg using hi`. Use `⟨fun b => ∑ i, g i b, continuous_finsetSum _ fun i _ => hgc i, fun S hS => ?_⟩` and prove the remaining obligations.

Establish `e1 : ∫ v in f ⁻¹' (ι '' S), φ v ∂μ = ∑ i, ∫ v in f ⁻¹' (ι '' S), φ v * ρ i v ∂μ`. Rewrite using `[← integral_finsetSum]`. Conclude with `integral_congr_ae (Filter.Eventually.of_forall fun x => hsum x)`. Introduce `i _`. Conclude with `((hc.mul (ρ i).continuous).integrable_of_hasCompactSupport hs.mul_right).integrableOn`.

Rewrite using `[e1, integral_finsetSum]`. Conclude with `Finset.sum_congr rfl fun i _ => hg i S hS`. Introduce `i _`. Conclude with `(hgc i).continuousOn.integrableOn_compact hS`.
-/
theorem densAll_of_local [T2Space V] [LocallyCompactSpace V] [OpensMeasurableSpace V]
    [OpensMeasurableSpace X] [T2Space X] {μ : Measure V} [IsFiniteMeasureOnCompacts μ] {ν : Measure X}
    [IsFiniteMeasureOnCompacts ν] {f : V → Y} {ι : X → Y} {U : Set V}
    (h : ∀ x ∈ U, ∃ N, IsOpen N ∧ x ∈ N ∧ DensAll μ f ι ν N) : DensAll μ f ι ν U := by
  intro φ hc hs hU
  choose N hNo hNx hND using h
  let K := tsupport φ
  have hK : IsCompact K := hs
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => N x.1 (hU x.2))
    (fun x => hNo _ _) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hNx _ _⟩)
  let n := t.card
  let N' : K → Set V := fun x => N x.1 (hU x.2)
  let s : Fin n → Set V := fun i => N' (t.equivFin.symm i).1
  have hso : ∀ i, IsOpen (s i) := fun i => hNo _ _
  have hcov : K ⊆ ⋃ i, s i := by
    intro x hx
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.1 (ht hx)
    refine Set.mem_iUnion.2 ⟨t.equivFin ⟨j, hj⟩, ?_⟩
    have e : s (t.equivFin ⟨j, hj⟩) = N' j := by simp only [s, Equiv.symm_apply_apply]
    rw [e]; exact hxj
  obtain ⟨ρ, hρs, hρ1, -, hρc⟩ := exists_continuous_sum_one_of_isOpen_isCompact hso hK hcov
  have hsum : ∀ x, φ x = ∑ i, φ x * ρ i x := by
    intro x
    by_cases hx : x ∈ K
    · have := hρ1 hx
      simp only [Finset.sum_apply, Pi.one_apply] at this
      rw [← Finset.mul_sum, this, mul_one]
    · have : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [this]
  have hi : ∀ i, ∃ g : X → ℝ, Continuous g ∧ ∀ S : Set X, IsCompact S →
      ∫ v in f ⁻¹' (ι '' S), φ v * ρ i v ∂μ = ∫ b in S, g b ∂ν := by
    intro i
    exact hND _ _ (fun v => φ v * ρ i v) (hc.mul (ρ i).continuous) (hs.mul_right)
      ((tsupport_mul_subset_right).trans (hρs i))
  choose g hgc hg using hi
  refine ⟨fun b => ∑ i, g i b, continuous_finsetSum _ fun i _ => hgc i, fun S hS => ?_⟩
  have e1 : ∫ v in f ⁻¹' (ι '' S), φ v ∂μ = ∑ i, ∫ v in f ⁻¹' (ι '' S), φ v * ρ i v ∂μ := by
    rw [← integral_finsetSum]
    · exact integral_congr_ae (Filter.Eventually.of_forall fun x => hsum x)
    · intro i _
      exact ((hc.mul (ρ i).continuous).integrable_of_hasCompactSupport hs.mul_right).integrableOn
  rw [e1, integral_finsetSum]
  · exact Finset.sum_congr rfl fun i _ => hg i S hS
  · intro i _
    exact (hgc i).continuousOn.integrableOn_compact hS

end Local

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet ψ hψ μinf hμ νinf hν`. Take `⟨n, m, eV, eH, f', hV, hH, hC, hG, hS⟩` from `hCo F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet`. Use `hμ.1` as an intermediate fact. Use `hν.1` as an intermediate fact. Establish `: ContinuousAdd (Fin a → Fin M → Ainf F ⊗[F] E)` using `⟨by`.

Establish `e : (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) × (Fin a → Fin M → Ainf F ⊗[F] E) => p.1 + p.2) = fun p => eV.symm (eV p.1 + eV p.2)`. Use function extensionality and compare the values at `p`. Rewrite using `[← hV, Homeomorph.symm_apply_apply]`. Rewrite using `[e]`. Use the proof step `fun_prop⟩`.

Establish `: ContinuousAdd (HermR (Ainf F) σ a)` using `⟨by`. Establish `e : (fun p : HermR (Ainf F) σ a × HermR (Ainf F) σ a => p.1 + p.2) = fun p => eH.symm (eH p.1 + eH p.2)`. Use function extensionality and compare the values at `p`. Rewrite using `[← hH, Homeomorph.symm_apply_apply]`. Rewrite using `[e]`.

Use the proof step `fun_prop⟩`. Establish `hμ' : (μinf.map eV).IsAddHaarMeasure` using `Measure.isAddHaarMeasure_map μinf (AddMonoidHom.mk' eV hV) eV.continuous eV.surjective (eV.map_cocompact).le`. Establish `hν' : (νinf.map eH).IsAddHaarMeasure` using `Measure.isAddHaarMeasure_map νinf (AddMonoidHom.mk' eH hH) eH.continuous eH.surjective (eH.map_cocompact).le`. Establish `hD` using `hSub n m _ _ hμ' hν' f' hC`. Use `densAll_transport μinf νinf (gramR (Ainf F) σ J) Subtype.val _ eV eH f' Subtype.val_injective (fun X => hG X) (densAll_mono hD ?_)` and prove the remaining obligations.

Introduce and unpack `y ⟨X, hX, rfl⟩`. Conclude with `hS X hX`.
-/
theorem densInf_of (hSub : SubmDens) (hCo : CoordInf) : DensInf := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet ψ hψ μinf hμ νinf hν
  obtain ⟨n, m, eV, eH, f', hV, hH, hC, hG, hS⟩ :=
    hCo F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet
  have := hμ.1
  have := hν.1
  have : ContinuousAdd (Fin a → Fin M → Ainf F ⊗[F] E) := ⟨by
    have e : (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) × (Fin a → Fin M → Ainf F ⊗[F] E) =>
        p.1 + p.2) = fun p => eV.symm (eV p.1 + eV p.2) := by
      funext p; rw [← hV, Homeomorph.symm_apply_apply]
    rw [e]; fun_prop⟩
  have : ContinuousAdd (HermR (Ainf F) σ a) := ⟨by
    have e : (fun p : HermR (Ainf F) σ a × HermR (Ainf F) σ a => p.1 + p.2) =
        fun p => eH.symm (eH p.1 + eH p.2) := by
      funext p; rw [← hH, Homeomorph.symm_apply_apply]
    rw [e]; fun_prop⟩
  have hμ' : (μinf.map eV).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map μinf (AddMonoidHom.mk' eV hV) eV.continuous eV.surjective
      (eV.map_cocompact).le
  have hν' : (νinf.map eH).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map νinf (AddMonoidHom.mk' eH hH) eH.continuous eH.surjective
      (eH.map_cocompact).le
  have hD := hSub n m _ _ hμ' hν' f' hC
  refine densAll_transport μinf νinf (gramR (Ainf F) σ J) Subtype.val _ eV eH f'
    Subtype.val_injective (fun X => hG X) (densAll_mono hD ?_)
  rintro y ⟨X, hX, rfl⟩
  exact hS X hX

end PI.VolStabW
