import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmRes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR

open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N ReciprocityTheory.Gal UpperTheory.V.Loc UpperTheory.V.Af UpperTheory.V.Af.Bc NumberField

/- English proof (translation)
Set `K : FinExt l` to `⟨IntermediateField.adjoin ℚ_[l] (Set.range fun x : E => j (algebraMap E Ω x)), GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap E Ω))⟩`. Use `K.2` as an intermediate fact. Take `⟨e, he, he', hec⟩` from `GlobalTheory.PlaceBridge.exists_mulEquiv (E := E) hj K rfl`. Conclude with `⟨⟨IntermediateField.normalClosure ℚ_[l] K.1 (PadicAlgCl l), inferInstance⟩, { Kw := K j := j j_E := fun x => IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩ j_dense := GlobalTheory.PlaceBridge.adjoin_range_subset_closure (j.comp (algebraMap E Ω)) e := e e_cont := he e_symm_cont := h …`.
-/
private theorem ex_bridge {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} (j : Ω →+* Om l) (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) :
    ∃ (L : FinExt l) (Bw : LocBridge l E Ω (Dec (F := E) A) ↥(OL L)), Bw.j = j := by
  let K : FinExt l := ⟨IntermediateField.adjoin ℚ_[l] (Set.range fun x : E => j (algebraMap E Ω x)),
    GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap E Ω))⟩
  have := K.2
  obtain ⟨e, he, he', hec⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := E) hj K rfl
  exact ⟨⟨IntermediateField.normalClosure ℚ_[l] K.1 (PadicAlgCl l), inferInstance⟩,
    { Kw := K
      j := j
      j_E := fun x => IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩
      j_dense := GlobalTheory.PlaceBridge.adjoin_range_subset_closure (j.comp (algebraMap E Ω))
      e := e
      e_cont := he
      e_symm_cont := he'
      e_comm := hec
      LL := ⟨IntermediateField.normalClosure ℚ_[l] K.1 (PadicAlgCl l), inferInstance⟩
      LL_split := fun τ x => AlgHom.fieldRange_le_normalClosure τ ⟨x, rfl⟩
      eO := RingEquiv.refl _
      eO_alg := fun _ => rfl
      eO_cont := continuous_id
      eO_symm_cont := continuous_id }, rfl⟩

/- English proof (translation)
Introduce `F K Ω _ _ _ _ _ _ _ _ _ _ _ l _ n r A hr`. Take `⟨O, i1, i2, i3, Bw, hj, hp⟩` from `hr`. Take `⟨L, Bw', hBj⟩` from `ex_bridge (E := K) (A := A) Bw.j hj`. Use `⟨↥(OL L), inferInstance, inferInstance, inferInstance, Bw', fun x => by rw [hBj]; exact hj x, ?_⟩` and prove the remaining obligations. Take `⟨L₀, r₀, hm₀, -⟩` from `id hp`.

Establish `hm₁` using `hm₀.enlarge (L₂ := GlobalTheory.Pst.supExt L₀ Bw'.LL) le_sup_left`. Establish `hL : Bw'.LL.1 ≤ (GlobalTheory.Pst.supExt L₀ Bw'.LL).1` using `le_sup_right`. Take `⟨r₁, hm, hc⟩ : ∃ r₁, GlobalTheory.Pst.IsModel Bw (r.comp (Dec (F` from `F) A).subtype) (GlobalTheory.Pst.supExt L₀ Bw'.LL) r₁ ∧ Bw.IsPotCrysE (PP l) _ r₁ := ⟨_, hm₁, (hm₁.isPotCrysAt_iff (PP l)).1 hp⟩`. Use `clear hm₁`. Generalize the expression as in `GlobalTheory.Pst.supExt L₀ Bw'.LL = L₁ at hL r₁ hm hc`.

Take `⟨K₁, h₁, hc⟩` from `hc`. Establish `hmem : ∀ σ : G K Ω, σ ∈ Dec (F` using `K) A ↔ res F Ω K σ ∈ Dec (F := F) A := fun σ => by`. Rewrite using `[mem_Dec, mem_Dec]`. Conclude with `Iff.rfl`. Set `f : ↥(Dec (F` to `K) A) →* ↥(Dec (F := F) A) := ((res F Ω K).comp (Dec (F := K) A).subtype).codRestrict _ fun σ => (hmem σ).1 σ.2`.

Use `⟨L₁, r₁.comp f, ⟨hL, MonoidHom.ext fun g => DFunLike.congr_fun hm.2 (f g)⟩, ?_⟩` and prove the remaining obligations. Establish `h₂ : K₁.1 ≤ (GlobalTheory.Pst.supExt K₁ Bw'.Kw).1` using `le_sup_left`. Establish `h₃ : Bw'.Kw.1 ≤ (GlobalTheory.Pst.supExt K₁ Bw'.Kw).1` using `le_sup_right`. Use `⟨_, h₃, ?_⟩` and prove the remaining obligations. Take `⟨T⟩` from `tiedP l`.

Establish `hres` using `(GlobalTheory.Per.TiedRestrict.restrict_crys_deRham l (PP l) (AIP l) T K₁ _ L₁ h₂ _ _).1 hc`. Use `hres using 1` and compare the differences between its conclusion and the goal. Use `MonoidHom.ext fun g => ?_` and prove the remaining obligations. Establish `hg : f (Bw'.e.symm (Subgroup.inclusion (GK_le h₃) g)) = Bw.e.symm (Subgroup.inclusion (GK_le h₁) (Subgroup.inclusion (GK_le h₂) g))`. Use `Subtype.ext (AlgEquiv.ext fun x => Bw.j.injective ?_)` and prove the remaining obligations.

Establish `a1` using `Bw'.e_comm (Bw'.e.symm (Subgroup.inclusion (GK_le h₃) g)) x`. Establish `a2` using `Bw.e_comm (Bw.e.symm (Subgroup.inclusion (GK_le h₁) (Subgroup.inclusion (GK_le h₂) g))) x`. Rewrite `a1`, `a2` using `[MulEquiv.apply_symm_apply]`. Rewrite `a1` using `[hBj]`. Conclude with `a1.symm.trans a2`.

Conclude with `congrArg (fun s => Matrix.toLinAlgEquiv' (r₁ s : Matrix (Fin n) (Fin n) ↥L₁.1)) hg`.
-/
theorem UpperTheory.V.Br.potRes :
    UpperTheory.V.Br.PotRes := by
  intro F K Ω _ _ _ _ _ _ _ _ _ _ _ l _ n r A hr
  obtain ⟨O, i1, i2, i3, Bw, hj, hp⟩ := hr
  obtain ⟨L, Bw', hBj⟩ := ex_bridge (E := K) (A := A) Bw.j hj
  refine ⟨↥(OL L), inferInstance, inferInstance, inferInstance, Bw', fun x => by rw [hBj]; exact hj x, ?_⟩
  obtain ⟨L₀, r₀, hm₀, -⟩ := id hp
  have hm₁ := hm₀.enlarge (L₂ := GlobalTheory.Pst.supExt L₀ Bw'.LL) le_sup_left
  have hL : Bw'.LL.1 ≤ (GlobalTheory.Pst.supExt L₀ Bw'.LL).1 := le_sup_right
  obtain ⟨r₁, hm, hc⟩ : ∃ r₁, GlobalTheory.Pst.IsModel Bw (r.comp (Dec (F := F) A).subtype) (GlobalTheory.Pst.supExt L₀ Bw'.LL) r₁ ∧
      Bw.IsPotCrysE (PP l) _ r₁ := ⟨_, hm₁, (hm₁.isPotCrysAt_iff (PP l)).1 hp⟩
  clear hm₁
  generalize GlobalTheory.Pst.supExt L₀ Bw'.LL = L₁ at hL r₁ hm hc
  obtain ⟨K₁, h₁, hc⟩ := hc
  have hmem : ∀ σ : G K Ω, σ ∈ Dec (F := K) A ↔ res F Ω K σ ∈ Dec (F := F) A := fun σ => by
    rw [mem_Dec, mem_Dec]
    exact Iff.rfl
  let f : ↥(Dec (F := K) A) →* ↥(Dec (F := F) A) :=
    ((res F Ω K).comp (Dec (F := K) A).subtype).codRestrict _ fun σ => (hmem σ).1 σ.2
  refine ⟨L₁, r₁.comp f, ⟨hL, MonoidHom.ext fun g => DFunLike.congr_fun hm.2 (f g)⟩, ?_⟩
  have h₂ : K₁.1 ≤ (GlobalTheory.Pst.supExt K₁ Bw'.Kw).1 := le_sup_left
  have h₃ : Bw'.Kw.1 ≤ (GlobalTheory.Pst.supExt K₁ Bw'.Kw).1 := le_sup_right
  refine ⟨_, h₃, ?_⟩
  obtain ⟨T⟩ := tiedP l
  have hres := (GlobalTheory.Per.TiedRestrict.restrict_crys_deRham l (PP l) (AIP l) T K₁ _ L₁ h₂ _ _).1 hc
  convert hres using 1
  refine MonoidHom.ext fun g => ?_
  have hg : f (Bw'.e.symm (Subgroup.inclusion (GK_le h₃) g)) =
      Bw.e.symm (Subgroup.inclusion (GK_le h₁) (Subgroup.inclusion (GK_le h₂) g)) := by
    refine Subtype.ext (AlgEquiv.ext fun x => Bw.j.injective ?_)
    have a1 := Bw'.e_comm (Bw'.e.symm (Subgroup.inclusion (GK_le h₃) g)) x
    have a2 := Bw.e_comm (Bw.e.symm (Subgroup.inclusion (GK_le h₁) (Subgroup.inclusion (GK_le h₂) g))) x
    rw [MulEquiv.apply_symm_apply] at a1 a2
    rw [hBj] at a1
    exact a1.symm.trans a2
  exact congrArg (fun s => Matrix.toLinAlgEquiv' (r₁ s : Matrix (Fin n) (Fin n) ↥L₁.1)) hg
