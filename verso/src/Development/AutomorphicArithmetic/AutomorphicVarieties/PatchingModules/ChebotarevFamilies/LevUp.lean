import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.TaylorWilesObstructionBound

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

/- English proof (translation)
Introduce `l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ n r Q hQ hQs`. Establish `hsub : (⋃ v ∈ (V0.S' ∪ Q)ᶜ, ⋃ A ∈ {A : ValuationSubring Ω | IsPlaceOver A v}, Inertia (F` using `Lp L) A) ⊆ ⋃ v ∈ V0.S'ᶜ, ⋃ A ∈ {A : ValuationSubring Ω | IsPlaceOver A v}, Inertia (F := Lp L) A := Set.biUnion_subset_biUnion_left (Set.compl_subset_compl.mpr Set.subset_union_left)`. Establish `hNS : NS Ω (V0.S' ∪ Q) ≤ NS Ω V0.S'` using `Subgroup.topologicalClosure_minimal _ ((Subgroup.normalClosure_mono hsub).trans (Subgroup.le_topologicalClosure _)) (Subgroup.isClosed_topologicalClosure _)`. Set `π : GS Ω (V0.S' ∪ Q) →* GS Ω V0.S'` to `QuotientGroup.map _ _ (MonoidHom.id _) (fun x hx => hNS hx)`. Establish `hπ : ∀ g, π (toGS Ω (V0.S' ∪ Q) g) = toGS Ω V0.S' g` using `fun g => rfl`.

Establish `hπc : Continuous π`. Use `(QuotientGroup.isQuotientMap_mk (NS Ω (V0.S' ∪ Q))).continuous_iff.mpr ?_` and prove the remaining obligations. Conclude with `continuous_toGS Ω V0.S'`. Establish `hπs : Function.Surjective π`. Introduce `y`.

Take `⟨g, rfl⟩` from `QuotientGroup.mk'_surjective (NS Ω V0.S') y`. Conclude with `⟨toGS Ω (V0.S' ∪ Q) g, rfl⟩`. Establish `hconj : ∀ σ h, h ∈ (resP L Ω).range → σ * h * σ⁻¹ ∈ (resP L Ω).range`. Introduce `σ h hh`. Rewrite `hh`, the goal using `[← V0.hη]`.

Simplify using `[hh]`. Use `⟨{ S' := V0.S' ∪ Q fin := V0.fin.union hQ sub := V0.sub.trans Set.subset_union_left split := ?_ η := V0.η.comp π hη := fun g => by simpa only [MonoidHom.comp_apply, hπ] using V0.hη g η_open := V0.η_open.preimage hπc η_c := by simpa only [MonoidHom.comp_apply, hπ] using V0.η_c ε : …` and prove the remaining obligations. Use extensionality with `g`. Conclude with `congrArg (fun u : ℤ_[l]ˣ => (u : ℤ_[l])) (DFunLike.congr_fun V0.hε g)`. Use `ε_cont := V0.ε_cont.comp hπc }, rfl, ?_⟩`.

Introduce `v hv`. Break down `hv with hv | hv` into its components or cases. Conclude with `V0.split v hv`. Take `⟨B, hB, hdec⟩` from `hQs v hv`. Take `⟨σ, hσ⟩` from `exists_smul_eq_of_isPlaceOver hB (s.hA v)`.

Introduce `τ hτ`. Establish `hτ' : σ⁻¹ * τ * σ ∈ Dec (F` using `Lp L) B := by open Pointwise in`. Rewrite using `[mem_Dec, mul_smul, mul_smul, hσ, mem_Dec.mp hτ, ← hσ, inv_smul_smul]`. Use `hconj σ _ (hdec hτ')` as an intermediate fact. Simplify `this` using `[mul_assoc]`.

Conclude with `⟨⟨π, hπc, hπs, fun _ => rfl, rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩, fun _ => rfl⟩`.
-/
theorem UpperTheory.V.Pa.levUp :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (Q : Set (Plc (Lp L))), Q.Finite → (∀ v ∈ Q, ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ Dec (F := Lp L) B ≤ (resP L Ω).range) → ∃ V : s.Lev, V.S' = V0.S' ∪ Q ∧ ∃ h : (globOf r V).Hom (globOf r V0), ∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g := by
  intro l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ n r Q hQ hQs
  have hsub : (⋃ v ∈ (V0.S' ∪ Q)ᶜ, ⋃ A ∈ {A : ValuationSubring Ω | IsPlaceOver A v}, Inertia (F := Lp L) A) ⊆
      ⋃ v ∈ V0.S'ᶜ, ⋃ A ∈ {A : ValuationSubring Ω | IsPlaceOver A v}, Inertia (F := Lp L) A :=
    Set.biUnion_subset_biUnion_left (Set.compl_subset_compl.mpr Set.subset_union_left)
  have hNS : NS Ω (V0.S' ∪ Q) ≤ NS Ω V0.S' :=
    Subgroup.topologicalClosure_minimal _
      ((Subgroup.normalClosure_mono hsub).trans (Subgroup.le_topologicalClosure _))
      (Subgroup.isClosed_topologicalClosure _)
  let π : GS Ω (V0.S' ∪ Q) →* GS Ω V0.S' :=
    QuotientGroup.map _ _ (MonoidHom.id _) (fun x hx => hNS hx)
  have hπ : ∀ g, π (toGS Ω (V0.S' ∪ Q) g) = toGS Ω V0.S' g := fun g => rfl
  have hπc : Continuous π := by
    refine (QuotientGroup.isQuotientMap_mk (NS Ω (V0.S' ∪ Q))).continuous_iff.mpr ?_
    exact continuous_toGS Ω V0.S'
  have hπs : Function.Surjective π := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (NS Ω V0.S') y
    exact ⟨toGS Ω (V0.S' ∪ Q) g, rfl⟩
  have hconj : ∀ σ h, h ∈ (resP L Ω).range → σ * h * σ⁻¹ ∈ (resP L Ω).range := by
    intro σ h hh
    rw [← V0.hη] at hh ⊢
    simp [hh]
  refine ⟨{ S' := V0.S' ∪ Q
            fin := V0.fin.union hQ
            sub := V0.sub.trans Set.subset_union_left
            split := ?_
            η := V0.η.comp π
            hη := fun g => by simpa only [MonoidHom.comp_apply, hπ] using V0.hη g
            η_open := V0.η_open.preimage hπc
            η_c := by simpa only [MonoidHom.comp_apply, hπ] using V0.η_c
            ε := V0.ε.comp π
            hε := by
              ext g
              exact congrArg (fun u : ℤ_[l]ˣ => (u : ℤ_[l])) (DFunLike.congr_fun V0.hε g)
            ε_cont := V0.ε_cont.comp hπc }, rfl, ?_⟩
  · intro v hv
    rcases hv with hv | hv
    · exact V0.split v hv
    · obtain ⟨B, hB, hdec⟩ := hQs v hv
      obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hB (s.hA v)
      intro τ hτ
      have hτ' : σ⁻¹ * τ * σ ∈ Dec (F := Lp L) B := by
        open Pointwise in
        rw [mem_Dec, mul_smul, mul_smul, hσ, mem_Dec.mp hτ, ← hσ, inv_smul_smul]
      have := hconj σ _ (hdec hτ')
      simpa [mul_assoc] using this
  · exact ⟨⟨π, hπc, hπs, fun _ => rfl, rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩, fun _ => rfl⟩
