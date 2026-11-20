import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocRho

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Use extensionality with `z`. Take `⟨a, ha⟩` from `IsCO.res_surj (O := O') z`. Establish `h1 : (res O' C) z = (res O' C) (algebraMap O' C a)`. Rewrite using `[← sub_eq_zero, ← map_sub, res_eq_zero_iff]`. Conclude with `ha`.

Establish `h2 : IsLocalRing.residue C z = IsLocalRing.residue C (algebraMap O' C a)`. Rewrite using `[← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]`. Conclude with `ha`. Rewrite using `[RingHom.comp_apply, RingHom.coe_coe, h1, h2, AlgHom.commutes]`. Conclude with `(IsLocalRing.ResidueField.map_residue _ a).symm`.
-/
private theorem residue_eq_map_algebraMap_comp_res_of_isCO {O' C : Type} [CommRing O'] [IsLocalRing O'] [CommRing C] [Algebra O' C]
    [IsCO O' C] [IsLocalHom (algebraMap O' C)] :
    IsLocalRing.residue C =
      (IsLocalRing.ResidueField.map (algebraMap O' C)).comp (res O' C : C →+* ResidueField O') := by
  ext z
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O') z
  have h1 : (res O' C) z = (res O' C) (algebraMap O' C a) := by
    rw [← sub_eq_zero, ← map_sub, res_eq_zero_iff]
    exact ha
  have h2 : IsLocalRing.residue C z = IsLocalRing.residue C (algebraMap O' C a) := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact ha
  rw [RingHom.comp_apply, RingHom.coe_coe, h1, h2, AlgHom.commutes]
  exact (IsLocalRing.ResidueField.map_residue _ a).symm

/- English proof (translation)
Unfold `NRep.IsBar at h ⊢`. Conclude with `⟨fun g i => j.injective (h.1 g i), fun v i g => j.injective (h.2 v i g)⟩`.
-/
private theorem nRep_isBar_of_isBar_comp_map {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ}
    {K K' : Type} [Field K] [CommRing K'] [Nontrivial K'] (f : k →+* K) (j : K →+* K')
    (σ : NRep F n K) (h : NRep.IsBar (j.comp f) (NRep.map j σ)) : NRep.IsBar f σ := by
  unfold NRep.IsBar at h ⊢
  exact ⟨fun g i => j.injective (h.1 g i), fun v i g => j.injective (h.2 v i g)⟩

/- English proof (translation)
Introduce `l _ O _ _ _ _ F C₀ n hF hn S x L`. Establish `hOloc : IsLocalHom (algebraMap O L.O')`. Use `⟨fun a ha => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Establish `hm : algebraMap O L.O' a ∈ maximalIdeal L.O'`.

Rewrite using `[← L.unr]`. Conclude with `Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal a).mpr h)`. Conclude with `(IsLocalRing.mem_maximalIdeal _).mp hm ha`. Use `haveI : IsLocalHom (algebraMap L.O' L.R) := IsCO.isLocalHom`. Set `f0 : ResidueField O →+* ResidueField L.O'` to `IsLocalRing.ResidueField.map (algebraMap O L.O')`.

Set `jR : ResidueField L.O' →+* ResidueField L.R` to `IsLocalRing.ResidueField.map (algebraMap L.O' L.R)`. Establish `hloc` using `loc_rho hF hn S x L`. Use `⟨⟨f0, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `hfR : IsResMap O L.R (jR.comp f0)`. Introduce `a`.

Use `show jR (f0 (IsLocalRing.residue O a)) = _`. Rewrite using `[IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue, IsScalarTower.algebraMap_apply O L.O' L.R a]`. Establish `hbR` using `hloc.2.1 _ hfR`. Rewrite `hbR` using `[residue_eq_map_algebraMap_comp_res_of_isCO (O' := L.O') (C := L.R)]`. Conclude with `nRep_isBar_of_isBar_comp_map f0 jR _ hbR`.

Distinguish the cases in `hP : S.u.triP ≤ x`. Use `left`. Establish `hle : L.ρ.triP ≤ maximalIdeal L.R`. Rewrite using `[(hloc.2.2.1 (maximalIdeal L.R)).1]`. Use `show S.u.triP ≤ Ideal.comap (L.ι : S.A →+* L.R) (maximalIdeal L.R)`.

Rewrite using `[L.lies]`. Conclude with `hP`. Introduce `g i j hji`. Establish `hm : L.ρ.r g i j ∈ maximalIdeal L.R`. Use `hle ?_` and prove the remaining obligations.

Unfold `NRep.triP`. Conclude with `Ideal.subset_span ⟨g, i, j, hji, rfl⟩`. Use `show res L.O' L.R (L.ρ.r g i j) = 0`. Conclude with `(res_eq_zero_iff _ _ _).mpr hm`. Use `right`.

Establish `hle` using `(hloc.2.2.2 hP).2`. Introduce `g i j hji`. Establish `hm : L.ρ.r g j i ∈ maximalIdeal L.R`. Use `hle ?_` and prove the remaining obligations. Unfold `NRep.triM`.

Conclude with `Ideal.subset_span ⟨g, j, i, hji, rfl⟩`. Use `show res L.O' L.R (L.ρ.r g j i) = 0`. Conclude with `(res_eq_zero_iff _ _ _).mpr hm`.
-/
theorem UpperTheory.V.Fr.pr_res :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (x : Ideal S.A) (L : S.Loc x), (∃ φ : ResidueField O →+* ResidueField L.O', (L.ρ.bar L.O').IsBar φ) ∧ ((∀ g, UpT ((L.ρ.bar L.O').r g)) ∨ ∀ g, UpT ((L.ρ.bar L.O').r g)ᵀ) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S x L
  have hOloc : IsLocalHom (algebraMap O L.O') := by
    refine ⟨fun a ha => ?_⟩
    by_contra h
    have hm : algebraMap O L.O' a ∈ maximalIdeal L.O' := by
      rw [← L.unr]
      exact Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal a).mpr h)
    exact (IsLocalRing.mem_maximalIdeal _).mp hm ha
  haveI : IsLocalHom (algebraMap L.O' L.R) := IsCO.isLocalHom
  let f0 : ResidueField O →+* ResidueField L.O' := IsLocalRing.ResidueField.map (algebraMap O L.O')
  let jR : ResidueField L.O' →+* ResidueField L.R :=
    IsLocalRing.ResidueField.map (algebraMap L.O' L.R)
  have hloc := loc_rho hF hn S x L
  refine ⟨⟨f0, ?_⟩, ?_⟩
  · have hfR : IsResMap O L.R (jR.comp f0) := by
      intro a
      show jR (f0 (IsLocalRing.residue O a)) = _
      rw [IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue,
        IsScalarTower.algebraMap_apply O L.O' L.R a]
    have hbR := hloc.2.1 _ hfR
    rw [residue_eq_map_algebraMap_comp_res_of_isCO (O' := L.O') (C := L.R)] at hbR
    exact nRep_isBar_of_isBar_comp_map f0 jR _ hbR
  · by_cases hP : S.u.triP ≤ x
    · left
      have hle : L.ρ.triP ≤ maximalIdeal L.R := by
        rw [(hloc.2.2.1 (maximalIdeal L.R)).1]
        show S.u.triP ≤ Ideal.comap (L.ι : S.A →+* L.R) (maximalIdeal L.R)
        rw [L.lies]
        exact hP
      intro g i j hji
      have hm : L.ρ.r g i j ∈ maximalIdeal L.R := by
        refine hle ?_
        unfold NRep.triP
        exact Ideal.subset_span ⟨g, i, j, hji, rfl⟩
      show res L.O' L.R (L.ρ.r g i j) = 0
      exact (res_eq_zero_iff _ _ _).mpr hm
    · right
      have hle := (hloc.2.2.2 hP).2
      intro g i j hji
      have hm : L.ρ.r g j i ∈ maximalIdeal L.R := by
        refine hle ?_
        unfold NRep.triM
        exact Ideal.subset_span ⟨g, j, i, hji, rfl⟩
      show res L.O' L.R (L.ρ.r g j i) = 0
      exact (res_eq_zero_iff _ _ _).mpr hm
