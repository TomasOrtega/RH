import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OfinProd
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.EigAdm

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM UpperTheory.ConvolutionTheory.C
open scoped Classical

/- English proof (translation)
Introduce `K _ _ n hn μ _ ν _ V a x r w hV hx hw U hCO`. Set `U' : ∀ v : Pl K, Subgroup (Gw n v)` to `fun v => if h : ∃ i, w i = v then h.choose_spec ▸ U h.choose else ⊥`. Establish `hU' : ∀ i, U' (w i) = U i`. Introduce `i`. Establish `h : ∃ j, w j = w i` using `⟨i, rfl⟩`.

Establish `key : ∀ (j : Fin r) (e : w j = w i), (e ▸ U j : Subgroup (Gw n (w i))) = U i`. Introduce `j e`. Take `rfl` from `hw e`. Both sides reduce to the same expression. Simplify using `only [U', dif_pos h]`.

Conclude with `key _ _`. Establish `hCO' : ∀ v ∈ Finset.univ.image w, CO (U' v)`. Introduce `v hv`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 hv`. Rewrite using `[hU']`.

Conclude with `hCO i`. Establish `hfin` using `UpperTheory.ConvolutionTheory.C.eigAdm K n hn μ ν a x hx (Finset.univ.image w) U' hCO'`. Establish `hVc : V ≤ cuspidalL2 μ` using `hV.le`. Establish `hle : (eigIn V (Oinf μ ν a) x ⊓ sphOff μ (Finset.univ.image w)) ⊓ ⨅ i, fixL μ (w i) (U i) ≤ eigIn (cuspidalL2 μ) (Oinf μ ν a) x ⊓ sphOff μ (Finset.univ.image w) ⊓ ⨅ v ∈ Finset.univ.image w, fixL μ v (U' v)`. Introduce `u hu`.

Take `⟨⟨he, hs⟩, hf⟩` from `hu`. Use `⟨⟨?_, hs⟩, ?_⟩` and prove the remaining obligations. Establish `hmem : ∀ (W : Submodule ℂ (LL μ)) (y : LL μ), y ∈ eigIn W (Oinf μ ν a) x ↔ y ∈ W ∧ Oinf μ ν a y = (x : ℂ) • y`. Introduce `W y`. Simplify using `[eigIn, Module.End.mem_eigenspace_iff]`.

Establish `he'` using `(hmem V u).1 he`. Conclude with `(hmem _ u).2 ⟨hVc he'.1, he'.2⟩`. Establish `hf' : u ∈ ⨅ i, fixL μ (w i) (U i)` using `hf`. Rewrite `hf'` using `[Submodule.mem_iInf]`. Express the relevant statement in the definitionally equal form `u ∈ ⨅ v ∈ Finset.univ.image w, fixL μ v (U' v)`.

Simplify using `only [Submodule.mem_iInf]`. Introduce `v hv`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 hv`. Rewrite using `[hU']`. Conclude with `hf' i`.

Use `haveI := hfin`. Conclude with `Submodule.finiteDimensional_of_le hle`.
-/
theorem UpperTheory.finiteDimensional_eigenspace_inf_fixed_compactOpen :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]
        (V : Submodule ℂ (LL μ)) (a : TI K n) (x : ℝ) (r : ℕ) (w : Fin r → Pl K), IsSummand μ V → x ≠ 0 → Function.Injective w →
        ∀ U : ∀ i, Subgroup (Gw n (w i)), (∀ i, CO (U i)) →
          FiniteDimensional ℂ ↥((eigIn V (Oinf μ ν a) x ⊓ sphOff μ (Finset.univ.image w)) ⊓ ⨅ i, fixL μ (w i) (U i)) := by
  intro K _ _ n hn μ _ ν _ V a x r w hV hx hw U hCO
  let U' : ∀ v : Pl K, Subgroup (Gw n v) := fun v =>
    if h : ∃ i, w i = v then h.choose_spec ▸ U h.choose else ⊥
  have hU' : ∀ i, U' (w i) = U i := by
    intro i
    have h : ∃ j, w j = w i := ⟨i, rfl⟩
    have key : ∀ (j : Fin r) (e : w j = w i), (e ▸ U j : Subgroup (Gw n (w i))) = U i := by
      intro j e
      obtain rfl := hw e
      rfl
    simp only [U', dif_pos h]
    exact key _ _
  have hCO' : ∀ v ∈ Finset.univ.image w, CO (U' v) := by
    intro v hv
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
    rw [hU']
    exact hCO i
  have hfin := UpperTheory.ConvolutionTheory.C.eigAdm K n hn μ ν a x hx (Finset.univ.image w) U' hCO'
  have hVc : V ≤ cuspidalL2 μ := hV.le
  have hle : (eigIn V (Oinf μ ν a) x ⊓ sphOff μ (Finset.univ.image w)) ⊓ ⨅ i, fixL μ (w i) (U i) ≤
      eigIn (cuspidalL2 μ) (Oinf μ ν a) x ⊓ sphOff μ (Finset.univ.image w) ⊓
        ⨅ v ∈ Finset.univ.image w, fixL μ v (U' v) := by
    intro u hu
    obtain ⟨⟨he, hs⟩, hf⟩ := hu
    refine ⟨⟨?_, hs⟩, ?_⟩
    · have hmem : ∀ (W : Submodule ℂ (LL μ)) (y : LL μ), y ∈ eigIn W (Oinf μ ν a) x ↔ y ∈ W ∧ Oinf μ ν a y = (x : ℂ) • y := by
        intro W y
        simp [eigIn, Module.End.mem_eigenspace_iff]
      have he' := (hmem V u).1 he
      exact (hmem _ u).2 ⟨hVc he'.1, he'.2⟩
    · have hf' : u ∈ ⨅ i, fixL μ (w i) (U i) := hf
      rw [Submodule.mem_iInf] at hf'
      change u ∈ ⨅ v ∈ Finset.univ.image w, fixL μ v (U' v)
      simp only [Submodule.mem_iInf]
      intro v hv
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
      rw [hU']
      exact hf' i
  haveI := hfin
  exact Submodule.finiteDimensional_of_le hle
