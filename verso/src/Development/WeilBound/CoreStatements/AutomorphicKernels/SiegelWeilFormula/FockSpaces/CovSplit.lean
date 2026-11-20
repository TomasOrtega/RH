import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.ExistsInsW
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.VolumeIsAddHaar
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.IntSch

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFock

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Use `haveI := hν.1`. Use `⟨fun f hf => int_schM d ν hν.1 hf, ?_⟩` and prove the remaining obligations. Take `⟨i1, i2, i3, i4⟩` from `(PositivityTheory.ThKCT.ideleTop F E).1`. Use `haveI : BorelSpace (AE F E) := ⟨rfl⟩`. Use `haveI : IsTopologicalAddGroup (Mx F E d.m d.n) := inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))`.

Use `haveI : LocallyCompactSpace (Mx F E d.m d.n) := inferInstanceAs (LocallyCompactSpace (Fin d.m → Fin d.n → AE F E))`. Use `haveI : SecondCountableTopology (Mx F E d.m d.n) := inferInstanceAs (SecondCountableTopology (Fin d.m → Fin d.n → AE F E))`. Use `haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))`. Establish `hcl : IsClosed ((d.restW w : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n))` using `isClosed_eq (Place.continuous_cw d w) continuous_const`. Use `haveI : LocallyCompactSpace (d.restW w) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace`.

Use `haveI : SecondCountableTopology (d.restW w) := TopologicalSpace.Subtype.secondCountableTopology ((d.restW w : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n))`. Use `haveI : BorelSpace (d.restW w) := Subtype.borelSpace ((d.restW w : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n))`. Use `haveI := volume_isAddHaar d.m d.n`. Take `⟨s, hsc, hs1, hs2, hsa, -⟩` from `Place.exists_sec d.cm d.B.emb`. Set `sW : (Fin d.m → Fin d.n → ℂ) → Mx F E d.m d.n` to `fun u i j => s fun w' => if w' = w then u i j else 0`.

Establish `cw_sW : ∀ u, d.cw w (sW u) = Matrix.of u` using `fun u => by`. Use extensionality with `i j`. Use `show piInf (d.B.emb w) (s _) = u i j`. Rewrite using `[hs1, if_pos rfl]`. Establish `cw_sW' : ∀ u w', w' ≠ w → d.cw w' (sW u) = 0` using `fun u w' h => by`.

Use extensionality with `i j`. Use `show piInf (d.B.emb w') (s _) = 0`. Rewrite using `[hs1, if_neg h]`. Establish `fin_sW : ∀ u, finOne F • sW u = 0` using `fun u => by`. Use extensionality with `i j`.

Use `show finOne F • s _ = 0`. Conclude with `hs2 _`. Establish `ins_eq : ∀ u, ins (Matrix.of u) = sW u` using `fun u => by`. Take `⟨h1, h2, h3⟩` from `hins (Matrix.of u)`. Use `Place.cw_ext d (fun w' => ?_) (by rw [h3, fin_sW])` and prove the remaining obligations.

Distinguish the cases in `h : w' = w`. Substitute `h` using the available equality. Rewrite using `[h1, cw_sW]`. Rewrite using `[h2 w' h, cw_sW' u w' h]`. Establish `sW_add : ∀ u v, sW (u + v) = sW u + sW v` using `fun u v => by`.

Use extensionality with `i j`. Use `show s _ = s _ + s _`. Rewrite using `[← hsa]`. Use `congr 1`. Use function extensionality and compare the values at `w'`.

Use `show _ = (if w' = w then u i j else 0) + (if w' = w then v i j else 0)`. Distinguish the cases in `h : w' = w`. Rewrite using `[if_pos h, if_pos h, if_pos h]`. Both sides reduce to the same expression. Rewrite using `[if_neg h, if_neg h, if_neg h, add_zero]`.

Establish `hsW : Continuous sW`. Use `continuous_pi fun i => continuous_pi fun j => hsc.comp (continuous_pi fun w' => ?_)` and prove the remaining obligations. Use `split_ifs`. Conclude with `(continuous_apply j).comp (continuous_apply i)`. Conclude with `continuous_const`.

Establish `cw_sub : ∀ X Z : Mx F E d.m d.n, d.cw w (X - Z) = d.cw w X - d.cw w Z` using `fun X Z => Matrix.map_sub _ (map_sub _) X Z`. Establish `cw_add : ∀ X Z : Mx F E d.m d.n, d.cw w (X + Z) = d.cw w X + d.cw w Z` using `fun X Z => Matrix.map_add _ (map_add _) X Z`. Set `cwf : Mx F E d.m d.n → Fin d.m → Fin d.n → ℂ` to `fun X i j => d.cw w X i j`. Establish `hcwf : ∀ X, Matrix.of (cwf X) = d.cw w X` using `fun X => rfl`. Establish `hccwf : Continuous cwf` using `Place.continuous_cw d w`.

Establish `mem : ∀ X, X - sW (cwf X) ∈ d.restW w` using `fun X => by show d.cw w (X - sW (cwf X)) = 0`. Rewrite using `[cw_sub, cw_sW, hcwf]`. Conclude with `sub_self _`. Set `Φ : (Fin d.m → Fin d.n → ℂ) × d.restW w ≃ₜ+ Mx F E d.m d.n` to `{ toFun := fun p => sW p.1 + p.2.1 invFun := fun X => (cwf X, ⟨X - sW (cwf X), mem X⟩) left_inv := fun p => by`. Take `⟨u, b, hb⟩` from `p`.

Establish `hb' : d.cw w b = 0` using `hb`. Establish `e1 : cwf (sW u + b) = u` using `by show Matrix.of.symm (d.cw w (sW u + b)) = u`. Rewrite using `[cw_add, cw_sW, hb', add_zero]`. Both sides reduce to the same expression. Use `Prod.ext e1 (Subtype.ext ?_)` and prove the remaining obligations.

Use `show sW u + b - sW (cwf (sW u + b)) = b`. Rewrite using `[e1]`. Conclude with `add_sub_cancel_left _ _`. Use `right_inv := fun X => by show sW (cwf X) + (X - sW (cwf X)) = X`. Rewrite using `[add_sub_cancel]`.

Use the proof step `map_add' := fun p q => by show sW (p.1 + q.1) + (p.2.1 + q.2.1) = sW p.1 + p.2.1 + (sW q.1 + q.2.1)`. Rewrite using `[sW_add]`. Normalize the expressions using the abelian group laws. Use `continuous_toFun := (hsW.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)`. Use `continuous_invFun := hccwf.prodMk ((continuous_id.sub (hsW.comp hccwf)).subtype_mk _) }`.

Take `⟨c, hc, hνc⟩` from `measure_split ν (volume : Measure (Fin d.m → Fin d.n → ℂ)) (Measure.addHaar : Measure (d.restW w)) Φ`. Use `⟨c, Measure.addHaar, NNReal.coe_pos.mpr hc, fun G hG => ?_⟩` and prove the remaining obligations. Set `e : (Fin d.m → Fin d.n → ℂ) × d.restW w ≃ᵐ Mx F E d.m d.n` to `Φ.toHomeomorph.toMeasurableEquiv`. Establish `hme : Measure.map Φ ((volume : Measure (Fin d.m → Fin d.n → ℂ)).prod (Measure.addHaar : Measure (d.restW w))) = Measure.map e ((volume : Measure (Fin d.m → Fin d.n → ℂ)).prod (Measure.addHaar : Measure (d.restW w)))` using `rfl`. Rewrite `hG` using `[hνc, hme]`.

Establish `hG1` using `(integrable_smul_measure (ENNReal.coe_ne_zero.mpr hc.ne') ENNReal.coe_ne_top).1 hG`. Establish `hG2` using `(integrable_map_equiv e G).1 hG1`. Rewrite using `[hνc, hme, integral_smul_nnreal_measure, integral_map_equiv]`. Use `show c • ∫ x, (G ∘ e) x ∂_ = _`. Rewrite using `[integral_prod _ hG2, NNReal.smul_def, Complex.real_smul]`.

Use `congr 1`. Use `integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)` and prove the remaining obligations. Use `integral_congr_ae (Filter.Eventually.of_forall fun Z => ?_)` and prove the remaining obligations. Use `show G (sW v + Z.1) = G (ins (Matrix.of v) + Z.1)`. Rewrite using `[ins_eq]`.
-/
theorem cov_split (d : SD σ) (w : InfinitePlace F) (ins : Matrix (Fin d.m) (Fin d.n) ℂ → Mx F E d.m d.n)
    (hins : ∀ M, d.cw w (ins M) = M ∧ (∀ w', w' ≠ w → d.cw w' (ins M) = 0) ∧ finOne F • ins M = 0)
    (ν : Measure (Mx F E d.m d.n)) (hν : d.IsCov ν) :
    (∀ f ∈ d.schM, Integrable f ν) ∧ ∃ (c : ℝ) (ν₀ : Measure (d.restW w)), 0 < c ∧
      ∀ G : Mx F E d.m d.n → ℂ, Integrable G ν →
        ∫ X, G X ∂ν = c * ∫ v : Fin d.m → Fin d.n → ℂ, ∫ Z : d.restW w, G (ins (Matrix.of v) + Z.1) ∂ν₀ := by
  haveI := hν.1
  refine ⟨fun f hf => int_schM d ν hν.1 hf, ?_⟩
  obtain ⟨i1, i2, i3, i4⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (Mx F E d.m d.n) := inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))
  haveI : LocallyCompactSpace (Mx F E d.m d.n) := inferInstanceAs (LocallyCompactSpace (Fin d.m → Fin d.n → AE F E))
  haveI : SecondCountableTopology (Mx F E d.m d.n) :=
    inferInstanceAs (SecondCountableTopology (Fin d.m → Fin d.n → AE F E))
  haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))
  have hcl : IsClosed ((d.restW w : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n)) :=
    isClosed_eq (Place.continuous_cw d w) continuous_const
  haveI : LocallyCompactSpace (d.restW w) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (d.restW w) :=
    TopologicalSpace.Subtype.secondCountableTopology ((d.restW w : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n))
  haveI : BorelSpace (d.restW w) := Subtype.borelSpace ((d.restW w : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n))
  haveI := volume_isAddHaar d.m d.n
  obtain ⟨s, hsc, hs1, hs2, hsa, -⟩ := Place.exists_sec d.cm d.B.emb
  let sW : (Fin d.m → Fin d.n → ℂ) → Mx F E d.m d.n := fun u i j => s fun w' => if w' = w then u i j else 0
  have cw_sW : ∀ u, d.cw w (sW u) = Matrix.of u := fun u => by
    ext i j
    show piInf (d.B.emb w) (s _) = u i j
    rw [hs1, if_pos rfl]
  have cw_sW' : ∀ u w', w' ≠ w → d.cw w' (sW u) = 0 := fun u w' h => by
    ext i j
    show piInf (d.B.emb w') (s _) = 0
    rw [hs1, if_neg h]
  have fin_sW : ∀ u, finOne F • sW u = 0 := fun u => by
    ext i j
    show finOne F • s _ = 0
    exact hs2 _
  have ins_eq : ∀ u, ins (Matrix.of u) = sW u := fun u => by
    obtain ⟨h1, h2, h3⟩ := hins (Matrix.of u)
    refine Place.cw_ext d (fun w' => ?_) (by rw [h3, fin_sW])
    by_cases h : w' = w
    · subst h; rw [h1, cw_sW]
    · rw [h2 w' h, cw_sW' u w' h]
  have sW_add : ∀ u v, sW (u + v) = sW u + sW v := fun u v => by
    ext i j
    show s _ = s _ + s _
    rw [← hsa]
    congr 1
    funext w'
    show _ = (if w' = w then u i j else 0) + (if w' = w then v i j else 0)
    by_cases h : w' = w
    · rw [if_pos h, if_pos h, if_pos h]; rfl
    · rw [if_neg h, if_neg h, if_neg h, add_zero]
  have hsW : Continuous sW := by
    refine continuous_pi fun i => continuous_pi fun j => hsc.comp (continuous_pi fun w' => ?_)
    split_ifs
    · exact (continuous_apply j).comp (continuous_apply i)
    · exact continuous_const
  have cw_sub : ∀ X Z : Mx F E d.m d.n, d.cw w (X - Z) = d.cw w X - d.cw w Z := fun X Z =>
    Matrix.map_sub _ (map_sub _) X Z
  have cw_add : ∀ X Z : Mx F E d.m d.n, d.cw w (X + Z) = d.cw w X + d.cw w Z := fun X Z =>
    Matrix.map_add _ (map_add _) X Z
  let cwf : Mx F E d.m d.n → Fin d.m → Fin d.n → ℂ := fun X i j => d.cw w X i j
  have hcwf : ∀ X, Matrix.of (cwf X) = d.cw w X := fun X => rfl
  have hccwf : Continuous cwf := Place.continuous_cw d w
  have mem : ∀ X, X - sW (cwf X) ∈ d.restW w := fun X => by
    show d.cw w (X - sW (cwf X)) = 0
    rw [cw_sub, cw_sW, hcwf]
    exact sub_self _
  let Φ : (Fin d.m → Fin d.n → ℂ) × d.restW w ≃ₜ+ Mx F E d.m d.n :=
    { toFun := fun p => sW p.1 + p.2.1
      invFun := fun X => (cwf X, ⟨X - sW (cwf X), mem X⟩)
      left_inv := fun p => by
        obtain ⟨u, b, hb⟩ := p
        have hb' : d.cw w b = 0 := hb
        have e1 : cwf (sW u + b) = u := by
          show Matrix.of.symm (d.cw w (sW u + b)) = u
          rw [cw_add, cw_sW, hb', add_zero]; rfl
        refine Prod.ext e1 (Subtype.ext ?_)
        show sW u + b - sW (cwf (sW u + b)) = b
        rw [e1]
        exact add_sub_cancel_left _ _
      right_inv := fun X => by
        show sW (cwf X) + (X - sW (cwf X)) = X
        rw [add_sub_cancel]
      map_add' := fun p q => by
        show sW (p.1 + q.1) + (p.2.1 + q.2.1) = sW p.1 + p.2.1 + (sW q.1 + q.2.1)
        rw [sW_add]; abel
      continuous_toFun := (hsW.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)
      continuous_invFun := hccwf.prodMk ((continuous_id.sub (hsW.comp hccwf)).subtype_mk _) }
  obtain ⟨c, hc, hνc⟩ := measure_split ν (volume : Measure (Fin d.m → Fin d.n → ℂ)) (Measure.addHaar : Measure (d.restW w)) Φ
  refine ⟨c, Measure.addHaar, NNReal.coe_pos.mpr hc, fun G hG => ?_⟩
  let e : (Fin d.m → Fin d.n → ℂ) × d.restW w ≃ᵐ Mx F E d.m d.n := Φ.toHomeomorph.toMeasurableEquiv
  have hme : Measure.map Φ ((volume : Measure (Fin d.m → Fin d.n → ℂ)).prod (Measure.addHaar : Measure (d.restW w))) =
      Measure.map e ((volume : Measure (Fin d.m → Fin d.n → ℂ)).prod (Measure.addHaar : Measure (d.restW w))) := rfl
  rw [hνc, hme] at hG
  have hG1 := (integrable_smul_measure (ENNReal.coe_ne_zero.mpr hc.ne') ENNReal.coe_ne_top).1 hG
  have hG2 := (integrable_map_equiv e G).1 hG1
  rw [hνc, hme, integral_smul_nnreal_measure, integral_map_equiv]
  show c • ∫ x, (G ∘ e) x ∂_ = _
  rw [integral_prod _ hG2, NNReal.smul_def, Complex.real_smul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun Z => ?_)
  show G (sW v + Z.1) = G (ins (Matrix.of v) + Z.1)
  rw [ins_eq]

end PositivityTheory.SiegelWeilFormula.KFock

end
