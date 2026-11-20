import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.OneVanish

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc

namespace PositivityTheory.Rg.BcB.CV.Glob1Aux

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

/- English proof (translation)
The claim follows from `IsCMField.complexEmbedding_complexConj E v.embedding x`.
-/
theorem emb_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (v : InfinitePlace E) (x : E) :
    v.embedding (conjE E x) = starRingEnd ℂ (v.embedding x) :=
  IsCMField.complexEmbedding_complexConj E v.embedding x

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Establish `h1 : (locGL v (thetaE E n d)).val = ((thetaR (conjE E) n d).val).map v.embedding` using `rfl`. Establish `h2 : (locGL v d⁻¹).val = (d⁻¹ : GL (Fin n) E).val.map v.embedding` using `rfl`. Rewrite using `[h1, thetaR_val, thetaR_val, ← map_inv, h2]`. Use extensionality with `i j`.

Simplify using `[emb_conj]`.
-/
theorem locGL_theta {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (v : InfinitePlace E)
    (d : GL (Fin n) E) : locGL v (thetaE E n d) = thC n (locGL v d) := by
  apply Units.ext
  have h1 : (locGL v (thetaE E n d)).val = ((thetaR (conjE E) n d).val).map v.embedding := rfl
  have h2 : (locGL v d⁻¹).val = (d⁻¹ : GL (Fin n) E).val.map v.embedding := rfl
  rw [h1, thetaR_val, thetaR_val, ← map_inv, h2]
  ext i j
  simp [emb_conj]

/- English proof (translation)
Rewrite using `[nrm, map_mul, locGL_theta]`.
-/
theorem locGL_nrm {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (v : InfinitePlace E)
    (d : GL (Fin n) E) : locGL v (nrm d) = locGL v d * thC n (locGL v d) := by
  rw [nrm, map_mul, locGL_theta]

/- English proof (translation)
Rewrite using `[← locGL_nrm]`. Establish `: (locGL v (nrm d)).val = (nrm d).val.map v.embedding` using `rfl`. Rewrite using `[this, Matrix.charpoly_map]`. Conclude with `hd.map`.
-/
theorem sep {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (v : InfinitePlace E)
    (d : GL (Fin n) E) (hd : IsRegD d) : (locGL v d * thC n (locGL v d)).val.charpoly.Separable := by
  rw [← locGL_nrm]
  have : (locGL v (nrm d)).val = (nrm d).val.map v.embedding := rfl
  rw [this, Matrix.charpoly_map]
  exact hd.map

/- English proof (translation)
Establish `h1 : ∀ t : T, e t ∈ T'` using `fun t => by`. Rewrite using `[← hT]`. Conclude with `Subgroup.mem_map_of_mem _ t.2`. Establish `h2 : ∀ s : T', e.symm s ∈ T` using `fun s => by`. Establish `hs : (s : H) ∈ T.map e.toMonoidHom` using `by rw [hT]; exact s.2`.

Take `⟨t, ht, hts⟩` from `Subgroup.mem_map.1 hs`. Rewrite using `[← hts]`. Use `show e.symm (e t) ∈ T`. Rewrite using `[e.symm_apply_apply]`. Conclude with `ht`.

Set `f : T ≃ₜ* T'` to `{ toFun := fun t => ⟨e t, h1 t⟩ invFun := fun s => ⟨e.symm s, h2 s⟩ left_inv := fun t => Subtype.ext (e.symm_apply_apply t) right_inv := fun s => Subtype.ext (e.apply_symm_apply s) map_mul' := fun a b => Subtype.ext (map_mul e (a : G) (b : G)) continuous_toFun := (e.continuous.co …`. Use `⟨ν.map f, inferInstance, ⟨?_⟩⟩` and prove the remaining obligations. Establish `hf : Measurable f` using `f.continuous.measurable`. Establish `hinv : Measurable (fun t : T => t⁻¹)` using `continuous_inv.measurable`. Establish `hν : Measure.map (fun t : T => t⁻¹) ν = ν` using `Measure.IsInvInvariant.inv_eq_self`.

Use `show Measure.map (fun s : T' => s⁻¹) (Measure.map f ν) = Measure.map f ν`. Rewrite using `[Measure.map_map continuous_inv.measurable hf]`. Use `conv_rhs => rw [← hν, Measure.map_map hf hinv]`. Use `congr 1`. Use function extensionality and compare the values at `t`.

Conclude with `(map_inv f t).symm`.
-/
theorem exists_measure {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
    (e : G ≃ₜ* H) (T : Subgroup G) (T' : Subgroup H) (hT : T.map e.toMonoidHom = T') (ν : Measure T)
    [ν.IsHaarMeasure] [ν.IsInvInvariant] : ∃ ν' : Measure T', ν'.IsHaarMeasure ∧ ν'.IsInvInvariant := by
  have h1 : ∀ t : T, e t ∈ T' := fun t => by
    rw [← hT]; exact Subgroup.mem_map_of_mem _ t.2
  have h2 : ∀ s : T', e.symm s ∈ T := fun s => by
    have hs : (s : H) ∈ T.map e.toMonoidHom := by rw [hT]; exact s.2
    obtain ⟨t, ht, hts⟩ := Subgroup.mem_map.1 hs
    rw [← hts]
    show e.symm (e t) ∈ T
    rw [e.symm_apply_apply]
    exact ht
  let f : T ≃ₜ* T' :=
    { toFun := fun t => ⟨e t, h1 t⟩
      invFun := fun s => ⟨e.symm s, h2 s⟩
      left_inv := fun t => Subtype.ext (e.symm_apply_apply t)
      right_inv := fun s => Subtype.ext (e.apply_symm_apply s)
      map_mul' := fun a b => Subtype.ext (map_mul e (a : G) (b : G))
      continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _ }
  refine ⟨ν.map f, inferInstance, ⟨?_⟩⟩
  have hf : Measurable f := f.continuous.measurable
  have hinv : Measurable (fun t : T => t⁻¹) := continuous_inv.measurable
  have hν : Measure.map (fun t : T => t⁻¹) ν = ν := Measure.IsInvInvariant.inv_eq_self
  show Measure.map (fun s : T' => s⁻¹) (Measure.map f ν) = Measure.map f ν
  rw [Measure.map_map continuous_inv.measurable hf]
  conv_rhs => rw [← hν, Measure.map_map hf hinv]
  congr 1
  funext t
  exact (map_inv f t).symm

end PositivityTheory.Rg.BcB.CV.Glob1Aux

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.BcB.CV.Glob1Aux in
/- English proof (translation)
Introduce `hSA hNEF hLV hLT hQM hQP hPl hAT E _ _ _ n _ _ μ _ d ν _ _ φ hreg hne hcomm hcl hφ hvc`. Take `⟨v, W₁, W₂, hW0, hW12, hp1, hp2⟩` from `hNEF E n d hreg hne`. Take `⟨G', _, _, _, _, _, _, _, _, _, e, μ₁, μ₂, θ', hμ₁, hμ₂, -, he1, hemb, hθ, hcent⟩` from `hSA E n v μ`. Establish `hsep` using `sep v d hreg`. Take `⟨hT1c, hT1m, -, hLC, hSC⟩` from `hLT n (locGL v d) hsep`.

Take `⟨hLCA, hT2A, hSCA, hθA, -, -⟩` from `hAT E n`. Use `hLC` as an intermediate fact. Use `hSC` as an intermediate fact. Use `hLCA` as an intermediate fact. Use `hT2A` as an intermediate fact.

Use `hSCA` as an intermediate fact. Use `hμ₁` as an intermediate fact. Use `hμ₂` as an intermediate fact. Establish `: T2Space (GL (Fin n) ℂ × G')` using `e.symm.toHomeomorph.isEmbedding.t2Space`. Establish `: T2Space (GL (Fin n) ℂ)` using `T2Space.of_injective_continuous (f := fun g : GL (Fin n) ℂ => (g, (1 : G'))) (fun a b h => (Prod.ext_iff.1 h).1) (continuous_id.prodMk continuous_const)`.

Establish `: T2Space G'` using `T2Space.of_injective_continuous (f := fun b : G' => ((1 : GL (Fin n) ℂ), b)) (fun a b h => (Prod.ext_iff.1 h).2) (continuous_const.prodMk continuous_id)`. Establish `he1' : (e (ratGL E n d)).1 = locGL v d`. Rewrite using `[he1]`. Conclude with `(hPl E n v ⊥).2.2.2.2.2.2.1 d`. Establish `hmem : ∀ p, p ∈ (twCent (thC n) (locGL v d)).prod (twCent θ' (e (ratGL E n d)).2) ↔ p ∈ e '' (adCent d : Set (GA E n))`.

Introduce `p`. Rewrite using `[← hcent d]`. Conclude with `Iff.rfl`. Establish `hT2c : IsClosed (twCent θ' (e (ratGL E n d)).2 : Set G')`. Establish `hc : IsClosed (e '' (adCent d : Set (GA E n)))` using `e.toHomeomorph.isClosedMap _ hcl`.

Establish `: (twCent θ' (e (ratGL E n d)).2 : Set G') = (fun b => ((1 : GL (Fin n) ℂ), b)) ⁻¹' (e '' (adCent d : Set (GA E n)))`. Use extensionality with `b`. Rewrite using `[Set.mem_preimage, ← hmem, Subgroup.mem_prod]`. Conclude with `⟨fun h => ⟨Subgroup.one_mem _, h⟩, fun h => h.2⟩`. Rewrite using `[this]`.

Conclude with `hc.preimage (continuous_const.prodMk continuous_id)`. Establish `hT2m : ∀ s ∈ twCent θ' (e (ratGL E n d)).2, ∀ t ∈ twCent θ' (e (ratGL E n d)).2, s * t = t * s`. Introduce `s hs t ht`. Take `⟨x, hx, hxs⟩` from `(hmem (1, s)).1 (Subgroup.mem_prod.2 ⟨Subgroup.one_mem _, hs⟩)`. Take `⟨y, hy, hyt⟩` from `(hmem (1, t)).1 (Subgroup.mem_prod.2 ⟨Subgroup.one_mem _, ht⟩)`.

Establish `h` using `congrArg (fun p => (e p).2) (hcomm x hx y hy)`. Simplify using `only [map_mul, Prod.snd_mul, hxs, hyt] at h`. Conclude with `h`. Take `⟨ν', hν'1, hν'2⟩` from `exists_measure e (adCent d) _ (hcent d) ν`. Use `hν'1` as an intermediate fact.

Use `hν'2` as an intermediate fact. Establish `hFc : Continuous fun x : GA E n => φ (twConj (thetaA E n) x (ratGL E n d))` using `hφ.cont.comp ((continuous_inv.mul continuous_const).mul hθA)`. Use `hQM (GA E n) (GL (Fin n) ℂ × G') e μ (μ₁.prod μ₂) (adCent d) _ ν ν' _ hcl (hcent d) hFc.measurable (fun t ht x => congrArg φ (twConj_mul_left (thetaA E n) (ratGL E n d) ht x)) ?_` and prove the remaining obligations. Use `hQP (GL (Fin n) ℂ) G' μ₁ μ₂ _ _ ν' _ hT1c hT2c hT1m hT2m (hFc.comp e.symm.continuous).measurable ?_ (Or.inl ?_)` and prove the remaining obligations. Introduce `t ht x`.

Take `⟨s, hs, rfl⟩` from `(hmem t).1 ht`. Use `show φ (twConj (thetaA E n) (e.symm (e s * x)) (ratGL E n d)) = φ (twConj (thetaA E n) (e.symm x) (ratGL E n d))`. Rewrite using `[map_mul, e.symm_apply_apply]`. Conclude with `congrArg φ (twConj_mul_left (thetaA E n) (ratGL E n d) hs _)`. Introduce `ν₁ _ _ x₂`.

Establish `key : ∀ x₁ : GL (Fin n) ℂ, twConj (thetaA E n) (e.symm (x₁, x₂)) (ratGL E n d) = e.symm (twConj (thC n) x₁ (locGL v d), twConj θ' x₂ (e (ratGL E n d)).2)`. Introduce `x₁`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[e.apply_symm_apply]`. Simplify using `only [twConj, map_mul, map_inv, hθ, e.apply_symm_apply]`.

Use `Prod.ext ?_ ?_` and prove the remaining obligations. Simplify using `[he1']`. Simplify using the standard rewrite rules. Establish `hf : VeryCusp fun g => φ (e.symm (g, twConj θ' x₂ (e (ratGL E n d)).2))`. Establish `h` using `hvc v (e.symm (1, twConj θ' x₂ (e (ratGL E n d)).2)) (by rw [← he1, e.apply_symm_apply])`.

Establish `: (fun g => φ (e.symm (g, twConj θ' x₂ (e (ratGL E n d)).2))) = fun g => φ (embInf n v g * e.symm (1, twConj θ' x₂ (e (ratGL E n d)).2))`. Use function extensionality and compare the values at `g`. Establish `hg : embInf n v g = e.symm (g, 1)` using `by rw [← hemb g, e.symm_apply_apply]`. Rewrite using `[hg, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]`. Rewrite using `[this]`.

Conclude with `h`. Establish `hfc : Continuous fun g => φ (e.symm (g, twConj θ' x₂ (e (ratGL E n d)).2))` using `hφ.cont.comp (e.symm.continuous.comp (continuous_id.prodMk continuous_const))`. Establish `hfs : HasCompactSupport fun g => φ (e.symm (g, twConj θ' x₂ (e (ratGL E n d)).2))`. Establish `hK : IsCompact (e '' tsupport φ)` using `hφ.supp.image e.continuous`. Use `IsCompact.of_isClosed_subset (hK.image continuous_fst) (isClosed_tsupport _) ?_` and prove the remaining obligations.

Establish `hcl' : IsClosed {g : GL (Fin n) ℂ | (g, twConj θ' x₂ (e (ratGL E n d)).2) ∈ e '' tsupport φ}` using `hK.isClosed.preimage (continuous_id.prodMk continuous_const)`. Use `(closure_minimal ?_ hcl').trans ?_` and prove the remaining obligations. Introduce `g hg`. Conclude with `⟨_, subset_tsupport _ hg, e.apply_symm_apply _⟩`. Introduce `g hg`.

Conclude with `⟨_, hg, rfl⟩`. Establish `hLV'` using `hLV n μ₁ _ (fun _ => 1) (locGL v d) ν₁ W₁ W₂ hfc hfs hf hsep hW0 hW12 hp1 hp2 measurable_const (fun _ _ => ⟨1, fun _ _ => by simp⟩) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)`. Use `Eq.trans ?_ hLV'` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `x₁`.

Use `show φ (twConj (thetaA E n) (e.symm (x₁, x₂)) (ratGL E n d)) = _`. Rewrite using `[key, mul_one]`.
-/
theorem PositivityTheory.Rg.BcB.CV.pf_Glob1 : PositivityTheory.Rg.BcB.D4.SplitAt → PositivityTheory.Rg.BcB.D4.NonEllFlag → PositivityTheory.Rg.BcB.LocVanish → PositivityTheory.Rg.BcB.CV.LocTor → PositivityTheory.Rg.BcB.CV.QMap → PositivityTheory.Rg.BcB.CV.QProd → PositivityTheory.Rg.BcB.CV.Ploc → PositivityTheory.Rg.BcB.CV.AdTop → PositivityTheory.Rg.BcB.CV.Glob1 := by
  intro hSA hNEF hLV hLT hQM hQP hPl hAT E _ _ _ n _ _ μ _ d ν _ _ φ hreg hne hcomm hcl hφ hvc
  obtain ⟨v, W₁, W₂, hW0, hW12, hp1, hp2⟩ := hNEF E n d hreg hne
  obtain ⟨G', _, _, _, _, _, _, _, _, _, e, μ₁, μ₂, θ', hμ₁, hμ₂, -, he1, hemb, hθ, hcent⟩ := hSA E n v μ
  have hsep := sep v d hreg
  obtain ⟨hT1c, hT1m, -, hLC, hSC⟩ := hLT n (locGL v d) hsep
  obtain ⟨hLCA, hT2A, hSCA, hθA, -, -⟩ := hAT E n
  have := hLC; have := hSC; have := hLCA; have := hT2A; have := hSCA; have := hμ₁; have := hμ₂
  have : T2Space (GL (Fin n) ℂ × G') := e.symm.toHomeomorph.isEmbedding.t2Space
  have : T2Space (GL (Fin n) ℂ) :=
    T2Space.of_injective_continuous (f := fun g : GL (Fin n) ℂ => (g, (1 : G')))
      (fun a b h => (Prod.ext_iff.1 h).1) (continuous_id.prodMk continuous_const)
  have : T2Space G' :=
    T2Space.of_injective_continuous (f := fun b : G' => ((1 : GL (Fin n) ℂ), b))
      (fun a b h => (Prod.ext_iff.1 h).2) (continuous_const.prodMk continuous_id)
  have he1' : (e (ratGL E n d)).1 = locGL v d := by
    rw [he1]; exact (hPl E n v ⊥).2.2.2.2.2.2.1 d
  have hmem : ∀ p, p ∈ (twCent (thC n) (locGL v d)).prod (twCent θ' (e (ratGL E n d)).2) ↔
      p ∈ e '' (adCent d : Set (GA E n)) := by
    intro p; rw [← hcent d]; exact Iff.rfl
  have hT2c : IsClosed (twCent θ' (e (ratGL E n d)).2 : Set G') := by
    have hc : IsClosed (e '' (adCent d : Set (GA E n))) := e.toHomeomorph.isClosedMap _ hcl
    have : (twCent θ' (e (ratGL E n d)).2 : Set G') =
        (fun b => ((1 : GL (Fin n) ℂ), b)) ⁻¹' (e '' (adCent d : Set (GA E n))) := by
      ext b
      rw [Set.mem_preimage, ← hmem, Subgroup.mem_prod]
      exact ⟨fun h => ⟨Subgroup.one_mem _, h⟩, fun h => h.2⟩
    rw [this]
    exact hc.preimage (continuous_const.prodMk continuous_id)
  have hT2m : ∀ s ∈ twCent θ' (e (ratGL E n d)).2, ∀ t ∈ twCent θ' (e (ratGL E n d)).2, s * t = t * s := by
    intro s hs t ht
    obtain ⟨x, hx, hxs⟩ := (hmem (1, s)).1 (Subgroup.mem_prod.2 ⟨Subgroup.one_mem _, hs⟩)
    obtain ⟨y, hy, hyt⟩ := (hmem (1, t)).1 (Subgroup.mem_prod.2 ⟨Subgroup.one_mem _, ht⟩)
    have h := congrArg (fun p => (e p).2) (hcomm x hx y hy)
    simp only [map_mul, Prod.snd_mul, hxs, hyt] at h
    exact h
  obtain ⟨ν', hν'1, hν'2⟩ := exists_measure e (adCent d) _ (hcent d) ν
  have := hν'1; have := hν'2
  have hFc : Continuous fun x : GA E n => φ (twConj (thetaA E n) x (ratGL E n d)) :=
    hφ.cont.comp ((continuous_inv.mul continuous_const).mul hθA)
  refine hQM (GA E n) (GL (Fin n) ℂ × G') e μ (μ₁.prod μ₂) (adCent d) _ ν ν' _ hcl (hcent d) hFc.measurable
    (fun t ht x => congrArg φ (twConj_mul_left (thetaA E n) (ratGL E n d) ht x)) ?_
  refine hQP (GL (Fin n) ℂ) G' μ₁ μ₂ _ _ ν' _ hT1c hT2c hT1m hT2m (hFc.comp e.symm.continuous).measurable ?_ (Or.inl ?_)
  · intro t ht x
    obtain ⟨s, hs, rfl⟩ := (hmem t).1 ht
    show φ (twConj (thetaA E n) (e.symm (e s * x)) (ratGL E n d)) = φ (twConj (thetaA E n) (e.symm x) (ratGL E n d))
    rw [map_mul, e.symm_apply_apply]
    exact congrArg φ (twConj_mul_left (thetaA E n) (ratGL E n d) hs _)
  · intro ν₁ _ _ x₂
    have key : ∀ x₁ : GL (Fin n) ℂ, twConj (thetaA E n) (e.symm (x₁, x₂)) (ratGL E n d) =
        e.symm (twConj (thC n) x₁ (locGL v d), twConj θ' x₂ (e (ratGL E n d)).2) := by
      intro x₁
      apply e.injective
      rw [e.apply_symm_apply]
      simp only [twConj, map_mul, map_inv, hθ, e.apply_symm_apply]
      refine Prod.ext ?_ ?_
      · simp [he1']
      · simp
    have hf : VeryCusp fun g => φ (e.symm (g, twConj θ' x₂ (e (ratGL E n d)).2)) := by
      have h := hvc v (e.symm (1, twConj θ' x₂ (e (ratGL E n d)).2)) (by rw [← he1, e.apply_symm_apply])
      have : (fun g => φ (e.symm (g, twConj θ' x₂ (e (ratGL E n d)).2))) =
          fun g => φ (embInf n v g * e.symm (1, twConj θ' x₂ (e (ratGL E n d)).2)) := by
        funext g
        have hg : embInf n v g = e.symm (g, 1) := by rw [← hemb g, e.symm_apply_apply]
        rw [hg, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
      rw [this]; exact h
    have hfc : Continuous fun g => φ (e.symm (g, twConj θ' x₂ (e (ratGL E n d)).2)) :=
      hφ.cont.comp (e.symm.continuous.comp (continuous_id.prodMk continuous_const))
    have hfs : HasCompactSupport fun g => φ (e.symm (g, twConj θ' x₂ (e (ratGL E n d)).2)) := by
      have hK : IsCompact (e '' tsupport φ) := hφ.supp.image e.continuous
      refine IsCompact.of_isClosed_subset (hK.image continuous_fst) (isClosed_tsupport _) ?_
      have hcl' : IsClosed {g : GL (Fin n) ℂ | (g, twConj θ' x₂ (e (ratGL E n d)).2) ∈ e '' tsupport φ} :=
        hK.isClosed.preimage (continuous_id.prodMk continuous_const)
      refine (closure_minimal ?_ hcl').trans ?_
      · intro g hg
        exact ⟨_, subset_tsupport _ hg, e.apply_symm_apply _⟩
      · intro g hg
        exact ⟨_, hg, rfl⟩
    have hLV' := hLV n μ₁ _ (fun _ => 1) (locGL v d) ν₁ W₁ W₂ hfc hfs hf hsep hW0 hW12 hp1 hp2 measurable_const
      (fun _ _ => ⟨1, fun _ _ => by simp⟩) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    refine Eq.trans ?_ hLV'
    congr 1
    funext x₁
    show φ (twConj (thetaA E n) (e.symm (x₁, x₂)) (ratGL E n d)) = _
    rw [key, mul_one]
