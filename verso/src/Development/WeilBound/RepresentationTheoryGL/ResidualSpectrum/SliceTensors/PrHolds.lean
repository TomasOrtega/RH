import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PPrIrr
import GroundTheory.PAdicHodge.NormalizedTrace

noncomputable section

open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CapOrth
  GlobalTheory.LevelTypeProj GlobalTheory.PRep GlobalTheory.CuspRep.LocEx PositivityTheory.Rg.Rs.PrAdm

namespace PositivityTheory.Rg.Rs

/- English proof (translation)
Introduce `E _ _ _ N`. Establish `hF` using `PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL`. Establish `hW : IsStable (A2 E N)` using `PrSt.isStable_square_integrable_forms hF`. Use `⟨hW, fun ψ hψ hψ0 => ?_⟩` and prove the remaining obligations. Set `μ : Measure (GA E N)` to `Measure.haar`.

Establish `: μ.IsMulRightInvariant` using `GlobalTheory.CovolGL.isMulRightInvariant E N μ`. Establish `hA : ∀ φ ∈ A2 E N, IsAutForm φ` using `fun φ hφ => (PrSt.mem_square_integrable_forms hφ).1`. Establish `h : ∀ φ ∈ A2 E N, MemL2Quotient (latticeGL E N) μ φ.1` using `fun φ hφ => memL2_of_isAutForm (PrSt.mem_square_integrable_forms hφ).1 (PrSt.mem_square_integrable_forms hφ).2`. Establish `hF2` using `toL2ₗ_injective h fun φ hφ => ContAut.continuous_of_isOpen_stab E N φ (hA φ hφ).level`. Establish `hinj : ∀ x ∈ A2 E N, cls h x = 0 → x = 0` using `fun x hx e => by`.

Rewrite `e` using `[cls_mk h hx]`. Conclude with `congrArg Subtype.val (hF2 (e.trans (map_zero _).symm))`. Establish `hadj` using `fun o => PrSt.exists_adj h hW hA o`. Take `⟨V, hVst, hVA, hV0, hirr, v, hvV, hvψ⟩` from `PrIrr.exists_irr h hW hA hinj hadj hψ hψ0`. Establish `hVW : V ≤ A2 E N` using `hVA.trans (admissible_span_le _ ψ)`.

Establish `hexist : ∀ χ ∈ A2 E N, ∃ v ∈ V, ∀ w ∈ V, inner ℂ (cls h (χ - v)) (cls h w) = 0`. Introduce `χ hχ`. Take `⟨L, hLo, hLc, hχT⟩` from `exists_type (hA χ hχ)`. Establish `: FiniteDimensional ℂ (orbSpan χ)` using `(hA χ hχ).kfin`. Establish `hρ` using `isContRep_sub (orbSpan χ) (orbSpan_stable χ)`.

Establish `: FiniteDimensional ℂ (V ⊓ typePart L (sub (cptRep E N) (orbSpan χ) (orbSpan_stable χ)) : Submodule ℂ (Sm E N))`. Use `finiteDimensional_admissible_isotypic hA (hA ψ hψ) hLo _ hρ` as an intermediate fact. Use the proof step `Submodule.finiteDimensional_of_le (inf_le_inf_right _ hVA)`. Take `⟨v, hv, hv'⟩` from `exists_orth h hW hA hinj hVst hVW hχ hLo hLc _ hρ hχT`. Conclude with `⟨v, hv.1, hv'⟩`.

Use `choose! P hPV hP using hexist`. Set `pW : A2 E N →ₗ[ℂ] Sm E N` to `{ toFun := fun χ => P χ.1 map_add' := fun x y => by`. Use `orth_unique h hinj hVW ((A2 E N).add_mem x.2 y.2) (hPV _ ((A2 E N).add_mem x.2 y.2)) (V.add_mem (hPV _ x.2) (hPV _ y.2)) (hP _ ((A2 E N).add_mem x.2 y.2)) fun w hw => ?_` and prove the remaining obligations. Establish `e : x.1 + y.1 - (P x.1 + P y.1) = (x.1 - P x.1) + (y.1 - P y.1)` using `by abel`. Express the relevant statement in the definitionally equal form `inner ℂ (cls h (x.1 + y.1 - (P x.1 + P y.1))) (cls h w) = 0`.

Rewrite using `[e, cls_add h ((A2 E N).sub_mem x.2 (hVW (hPV _ x.2))) ((A2 E N).sub_mem y.2 (hVW (hPV _ y.2))), inner_add_left, hP _ x.2 w hw, hP _ y.2 w hw, add_zero]`. Use the proof step `map_smul' := fun c x => by`. Use `orth_unique h hinj hVW ((A2 E N).smul_mem c x.2) (hPV _ ((A2 E N).smul_mem c x.2)) (V.smul_mem c (hPV _ x.2)) (hP _ ((A2 E N).smul_mem c x.2)) fun w hw => ?_` and prove the remaining obligations. Establish `e : c • x.1 - c • P x.1 = c • (x.1 - P x.1)` using `(smul_sub c _ _).symm`. Express the relevant statement in the definitionally equal form `inner ℂ (cls h (c • x.1 - (RingHom.id ℂ) c • P x.1)) (cls h w) = 0`.

Rewrite using `[RingHom.id_apply, e, cls_smul h c ((A2 E N).sub_mem x.2 (hVW (hPV _ x.2))), inner_smul_left, hP _ x.2 w hw, mul_zero] }`. Take `⟨p, hp⟩` from `LinearMap.exists_extend pW`. Establish `hpW : ∀ χ ∈ A2 E N, p χ = P χ` using `fun χ hχ => LinearMap.congr_fun hp ⟨χ, hχ⟩`. Use `⟨V, p, ⟨fun φ hφ => hA φ (hVW hφ), fun φ hφ => (PrSt.mem_square_integrable_forms (hVW hφ)).2, hVst, hV0, hirr⟩, fun χ hχ => by rw [hpW χ hχ]; exact hPV χ hχ, fun o χ hχ => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hpW _ (hW o χ hχ), hpW χ hχ]`.

Use `orth_unique h hinj hVW (hW o χ hχ) (hPV _ (hW o χ hχ)) (hVst o _ (hPV χ hχ)) (hP _ (hW o χ hχ)) fun w hw => ?_` and prove the remaining obligations. Take `⟨B, hB, hadjB⟩` from `hadj o`. Rewrite using `[← map_sub, hadjB _ ((A2 E N).sub_mem hχ (hVW (hPV χ hχ))) w (hVW hw)]`. Conclude with `hP χ hχ _ (hB V hVst w hw)`. Rewrite using `[hpW ψ hψ]`.

Introduce `e`. Use `hP ψ hψ v hvV` as an intermediate fact. Rewrite `this` using `[e, sub_zero]`. Conclude with `hvψ this`.
-/
theorem pr_holds : Pr := by
  intro E _ _ _ N
  have hF := PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL
  have hW : IsStable (A2 E N) := PrSt.isStable_square_integrable_forms hF
  refine ⟨hW, fun ψ hψ hψ0 => ?_⟩
  let μ : Measure (GA E N) := Measure.haar
  have : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E N μ
  have hA : ∀ φ ∈ A2 E N, IsAutForm φ := fun φ hφ => (PrSt.mem_square_integrable_forms hφ).1
  have h : ∀ φ ∈ A2 E N, MemL2Quotient (latticeGL E N) μ φ.1 := fun φ hφ =>
    memL2_of_isAutForm (PrSt.mem_square_integrable_forms hφ).1 (PrSt.mem_square_integrable_forms hφ).2
  have hF2 := toL2ₗ_injective h fun φ hφ => ContAut.continuous_of_isOpen_stab E N φ (hA φ hφ).level
  have hinj : ∀ x ∈ A2 E N, cls h x = 0 → x = 0 := fun x hx e => by
    rw [cls_mk h hx] at e
    exact congrArg Subtype.val (hF2 (e.trans (map_zero _).symm))
  have hadj := fun o => PrSt.exists_adj h hW hA o
  obtain ⟨V, hVst, hVA, hV0, hirr, v, hvV, hvψ⟩ := PrIrr.exists_irr h hW hA hinj hadj hψ hψ0
  have hVW : V ≤ A2 E N := hVA.trans (admissible_span_le _ ψ)
  have hexist : ∀ χ ∈ A2 E N, ∃ v ∈ V, ∀ w ∈ V, inner ℂ (cls h (χ - v)) (cls h w) = 0 := by
    intro χ hχ
    obtain ⟨L, hLo, hLc, hχT⟩ := exists_type (hA χ hχ)
    have : FiniteDimensional ℂ (orbSpan χ) := (hA χ hχ).kfin
    have hρ := isContRep_sub (orbSpan χ) (orbSpan_stable χ)
    have : FiniteDimensional ℂ (V ⊓ typePart L (sub (cptRep E N) (orbSpan χ) (orbSpan_stable χ)) :
        Submodule ℂ (Sm E N)) :=
      have := finiteDimensional_admissible_isotypic hA (hA ψ hψ) hLo _ hρ
      Submodule.finiteDimensional_of_le (inf_le_inf_right _ hVA)
    obtain ⟨v, hv, hv'⟩ := exists_orth h hW hA hinj hVst hVW hχ hLo hLc _ hρ hχT
    exact ⟨v, hv.1, hv'⟩
  choose! P hPV hP using hexist
  let pW : A2 E N →ₗ[ℂ] Sm E N :=
    { toFun := fun χ => P χ.1
      map_add' := fun x y => by
        refine orth_unique h hinj hVW ((A2 E N).add_mem x.2 y.2) (hPV _ ((A2 E N).add_mem x.2 y.2))
          (V.add_mem (hPV _ x.2) (hPV _ y.2)) (hP _ ((A2 E N).add_mem x.2 y.2)) fun w hw => ?_
        have e : x.1 + y.1 - (P x.1 + P y.1) = (x.1 - P x.1) + (y.1 - P y.1) := by abel
        change inner ℂ (cls h (x.1 + y.1 - (P x.1 + P y.1))) (cls h w) = 0
        rw [e, cls_add h ((A2 E N).sub_mem x.2 (hVW (hPV _ x.2))) ((A2 E N).sub_mem y.2 (hVW (hPV _ y.2))),
          inner_add_left, hP _ x.2 w hw, hP _ y.2 w hw, add_zero]
      map_smul' := fun c x => by
        refine orth_unique h hinj hVW ((A2 E N).smul_mem c x.2) (hPV _ ((A2 E N).smul_mem c x.2))
          (V.smul_mem c (hPV _ x.2)) (hP _ ((A2 E N).smul_mem c x.2)) fun w hw => ?_
        have e : c • x.1 - c • P x.1 = c • (x.1 - P x.1) := (smul_sub c _ _).symm
        change inner ℂ (cls h (c • x.1 - (RingHom.id ℂ) c • P x.1)) (cls h w) = 0
        rw [RingHom.id_apply, e, cls_smul h c ((A2 E N).sub_mem x.2 (hVW (hPV _ x.2))), inner_smul_left,
          hP _ x.2 w hw, mul_zero] }
  obtain ⟨p, hp⟩ := LinearMap.exists_extend pW
  have hpW : ∀ χ ∈ A2 E N, p χ = P χ := fun χ hχ => LinearMap.congr_fun hp ⟨χ, hχ⟩
  refine ⟨V, p, ⟨fun φ hφ => hA φ (hVW hφ), fun φ hφ => (PrSt.mem_square_integrable_forms (hVW hφ)).2, hVst, hV0, hirr⟩,
    fun χ hχ => by rw [hpW χ hχ]; exact hPV χ hχ, fun o χ hχ => ?_, ?_⟩
  · rw [hpW _ (hW o χ hχ), hpW χ hχ]
    refine orth_unique h hinj hVW (hW o χ hχ) (hPV _ (hW o χ hχ)) (hVst o _ (hPV χ hχ)) (hP _ (hW o χ hχ))
      fun w hw => ?_
    obtain ⟨B, hB, hadjB⟩ := hadj o
    rw [← map_sub, hadjB _ ((A2 E N).sub_mem hχ (hVW (hPV χ hχ))) w (hVW hw)]
    exact hP χ hχ _ (hB V hVst w hw)
  · rw [hpW ψ hψ]
    intro e
    have := hP ψ hψ v hvV
    rw [e, sub_zero] at this
    exact hvψ this

end PositivityTheory.Rg.Rs

end
