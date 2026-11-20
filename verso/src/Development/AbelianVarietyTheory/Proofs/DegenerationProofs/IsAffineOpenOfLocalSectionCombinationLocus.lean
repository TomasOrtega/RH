import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOpenNonzeroLocusOfUniversallyClosed
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out

noncomputable section
namespace GlobalTheory.ZH.CombLocus

def secComb {X : Scheme.{0}} {H : LB X} {J : Type} [Fintype J] (a : J → Γ(X, ⊤)) (s : J → H.Sec) : H.Sec where
  f l := ∑ k, resG X le_top (a k) * (s k).f l
  compat i j := by
    rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e : ∀ (U V : X.Opens) (h : V ≤ U),
        (X.presheaf.map (homOfLE h).op).hom (resG X (le_top : U ≤ ⊤) (a k)) = resG X (le_top : V ≤ ⊤) (a k) := by
      intro U V h
      change (X.presheaf.map (homOfLE _).op ≫ X.presheaf.map (homOfLE h).op).hom (a k) = _
      rw [← Functor.map_comp]
      rfl
    rw [map_mul, map_mul, (s k).compat i j, e, e, mul_left_comm]

/- English proof (translation)
Establish `h₀ : (y ≫ h) (IsLocalRing.closedPoint K) ∈ ⨆ k, nonzeroLocus (σ k)` using `by rw [hcov]; trivial`. Take `⟨k₀, hk₀⟩` from `TopologicalSpace.Opens.mem_iSup.1 h₀`. Take `⟨l, hl⟩` from `exists_chart_of_mem_nonzeroLocus hk₀`. Establish `h₁ : ⊤ ≤ (y ≫ h) ⁻¹ᵁ H.U l` using `(CrdCalc.top_le_iff _ _).2 hl`. Establish `h₂ : ⊤ ≤ y ⁻¹ᵁ (H.pull h).U (fun _ => l)` using `fun p hp => Set.mem_iInter.2 fun _ => h₁ hp`.

Use `⟨fun k => valR (y ≫ h) (H.U l) ((σ k).f l), ⟨l, 1, h₁, fun k => by simp⟩, ?_⟩` and prove the remaining obligations. Establish `h₃ : Crd (H.pull h) (fun _ : Unit => secComb a fun k => GlobalTheory.secPull (σ k) h) y (fun _ => ∑ k, valR y ⊤ (a k) * valR (y ≫ h) (H.U l) ((σ k).f l))`. Use `⟨fun _ => l, 1, h₂, fun _ => ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_one, one_mul, CrdCalc.valR_eq y _ h₂]`. Use `Eq.symm ((map_sum _ _ _).trans (Finset.sum_congr rfl fun k _ => ?_))` and prove the remaining obligations.

Rewrite using `[map_mul, ← CrdCalc.valR_eq, ← CrdCalc.valR_eq, CrdCalc.valR_res y _ h₂]`. Conclude with `congrArg _ (GlobalTheory.Points.valR_appLE y h _ h₂ _)`. Conclude with `(CrdCalc.crd_isUnit_iff () h₃).symm.trans isUnit_iff_ne_zero`.
-/
theorem exists_crd_secComb {X Y : Scheme.{0}} (h : X ⟶ Y) {H : LB Y} {J : Type} [Fintype J] (σ : J → H.Sec)
    (hcov : ⨆ k, nonzeroLocus (σ k) = ⊤) (a : J → Γ(X, ⊤)) {K : Type} [Field K] (y : Sp K ⟶ X) :
    ∃ w, Crd H σ (y ≫ h) w ∧ (⊤ ≤ y ⁻¹ᵁ nonzeroLocus (secComb a fun k => GlobalTheory.secPull (σ k) h) ↔
      ∑ k, valR y ⊤ (a k) * w k ≠ 0) := by
  have h₀ : (y ≫ h) (IsLocalRing.closedPoint K) ∈ ⨆ k, nonzeroLocus (σ k) := by rw [hcov]; trivial
  obtain ⟨k₀, hk₀⟩ := TopologicalSpace.Opens.mem_iSup.1 h₀
  obtain ⟨l, hl⟩ := exists_chart_of_mem_nonzeroLocus hk₀
  have h₁ : ⊤ ≤ (y ≫ h) ⁻¹ᵁ H.U l := (CrdCalc.top_le_iff _ _).2 hl
  have h₂ : ⊤ ≤ y ⁻¹ᵁ (H.pull h).U (fun _ => l) := fun p hp => Set.mem_iInter.2 fun _ => h₁ hp
  refine ⟨fun k => valR (y ≫ h) (H.U l) ((σ k).f l), ⟨l, 1, h₁, fun k => by simp⟩, ?_⟩
  have h₃ : Crd (H.pull h) (fun _ : Unit => secComb a fun k => GlobalTheory.secPull (σ k) h) y
      (fun _ => ∑ k, valR y ⊤ (a k) * valR (y ≫ h) (H.U l) ((σ k).f l)) := by
    refine ⟨fun _ => l, 1, h₂, fun _ => ?_⟩
    rw [Units.val_one, one_mul, CrdCalc.valR_eq y _ h₂]
    refine Eq.symm ((map_sum _ _ _).trans (Finset.sum_congr rfl fun k _ => ?_))
    rw [map_mul, ← CrdCalc.valR_eq, ← CrdCalc.valR_eq, CrdCalc.valR_res y _ h₂]
    exact congrArg _ (GlobalTheory.Points.valR_appLE y h _ h₂ _)
  exact (CrdCalc.crd_isUnit_iff () h₃).symm.trans isUnit_iff_ne_zero

/- English proof (translation)
Establish `e : ∀ (p : X) (O : X.Opens), ⊤ ≤ X.fromSpecResidueField p ⁻¹ᵁ O ↔ p ∈ O` using `fun p O => ⟨fun H => by`. Use `H (Set.mem_univ (IsLocalRing.closedPoint (X.residueField p)))` as an intermediate fact. Establish `h' : X.fromSpecResidueField p (IsLocalRing.closedPoint (X.residueField p)) ∈ O` using `this`. Conclude with `(Scheme.fromSpecResidueField_apply p (IsLocalRing.closedPoint (X.residueField p))) ▸ h',`. Use `fun H s _ => by`.

Express the relevant statement in the definitionally equal form `X.fromSpecResidueField p s ∈ O`. Rewrite using `[Scheme.fromSpecResidueField_apply]⟩` and apply the resulting hypothesis. Use extensionality with `p`. Conclude with `(e p U).symm.trans ((h _ (X.fromSpecResidueField p)).trans (e p V))`.
-/
theorem opens_eq_of_field_points {X : Scheme.{0}} {U V : X.Opens}
    (h : ∀ (K : Type) [Field K] (y : Sp K ⟶ X), ⊤ ≤ y ⁻¹ᵁ U ↔ ⊤ ≤ y ⁻¹ᵁ V) : U = V := by
  have e : ∀ (p : X) (O : X.Opens), ⊤ ≤ X.fromSpecResidueField p ⁻¹ᵁ O ↔ p ∈ O := fun p O =>
    ⟨fun H => by
      have := H (Set.mem_univ (IsLocalRing.closedPoint (X.residueField p)))
      have h' : X.fromSpecResidueField p (IsLocalRing.closedPoint (X.residueField p)) ∈ O := this
      exact (Scheme.fromSpecResidueField_apply p (IsLocalRing.closedPoint (X.residueField p))) ▸ h',
    fun H s _ => by
      change X.fromSpecResidueField p s ∈ O
      rwa [Scheme.fromSpecResidueField_apply]⟩
  ext p
  exact (e p U).symm.trans ((h _ (X.fromSpecResidueField p)).trans (e p V))

/- English proof (translation)
Establish `: IsAffine V` using `hV`. Establish `: IsAffine W` using `hW`. Establish `sq : IsPullback (P.homOfLE (π.preimage_mono e)) (π ∣_ V) (π ∣_ W) (Z.homOfLE e)`. Use `IsPullback.of_right (h₁₂ := (π ⁻¹ᵁ W).ι) (h₂₂ := W.ι) (v₁₃ := π) ?_ ?_ (isPullback_morphismRestrict π W).flip` and prove the remaining obligations. Rewrite using `[Scheme.homOfLE_ι, Scheme.homOfLE_ι]`.

Conclude with `(isPullback_morphismRestrict π V).flip`. Rewrite using `[← cancel_mono W.ι]`. Simplify using the standard rewrite rules. Conclude with `MorphismProperty.of_isPullback (P := @IsAffineHom) sq.flip (inferInstance : IsAffineHom (Z.homOfLE e))`.
-/
theorem isAffineHom_homOfLE {P Z : Scheme.{0}} (π : P ⟶ Z) {V W : Z.Opens} (e : V ≤ W) (hV : IsAffineOpen V)
    (hW : IsAffineOpen W) : IsAffineHom (P.homOfLE (π.preimage_mono e)) := by
  have : IsAffine V := hV
  have : IsAffine W := hW
  have sq : IsPullback (P.homOfLE (π.preimage_mono e)) (π ∣_ V) (π ∣_ W) (Z.homOfLE e) := by
    refine IsPullback.of_right (h₁₂ := (π ⁻¹ᵁ W).ι) (h₂₂ := W.ι) (v₁₃ := π) ?_ ?_ (isPullback_morphismRestrict π W).flip
    · rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι]
      exact (isPullback_morphismRestrict π V).flip
    · rw [← cancel_mono W.ι]
      simp
  exact MorphismProperty.of_isPullback (P := @IsAffineHom) sq.flip (inferInstance : IsAffineHom (Z.homOfLE e))

/- English proof (translation)
Introduce `P Z π _ J _ D W hW hD H`. Establish `: IsAffine W` using `hW`. Establish `: IsAffineHom (π.resLE W D hD)`. Use `isAffineHom_of_forall_exists_isAffineOpen _ fun z => ?_` and prove the remaining obligations. Take `⟨W', H, σ, m, hz, hW', hcov, haff, hiff⟩` from `H z.1 z.2`.

Take `⟨V, hV, hzV, hle⟩` from `exists_isAffineOpen_mem_and_subset (X := Z) (x := z.1) (U := W ⊓ W') ⟨z.2, hz⟩`. Establish `hle' : V ≤ W ⊓ W'` using `hle`. Establish `: IsAffine V` using `hV`. Use `⟨W.ι ⁻¹ᵁ V, hzV, hV.preimage_of_isOpenImmersion _ (by simpa using hle'.trans inf_le_left), ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_preimage, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_preimage, ← D.ι.isAffineOpen_iff_of_isOpenImmersion, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]`.

Establish `e : V ≤ W'` using `hle'.trans inf_le_right`. Use `isAffineHom_homOfLE π e hV hW'` as an intermediate fact. Use `set h := P.homOfLE (π.preimage_mono e) with hh`. Establish `hι : h ≫ (π ⁻¹ᵁ W').ι = (π ⁻¹ᵁ V).ι` using `Scheme.homOfLE_ι _ _`. Establish `ha : ⊤ ≤ ((π ⁻¹ᵁ V).ι ≫ π) ⁻¹ᵁ (W ⊓ W')` using `fun p _ => hle' p.2`.

Set `a : J → Γ((π ⁻¹ᵁ V).toScheme, ⊤)` to `fun k => (((π ⁻¹ᵁ V).ι ≫ π).appLE (W ⊓ W') ⊤ ha).hom (m k)`. Establish `ht` using `isAffineOpen_nonzeroLocus_of_universallyClosed (π ∣_ V) (fun k => GlobalTheory.secPull (σ k) h) (by simp only [GlobalTheory.nonzeroLocus_secPull]; rw [← Scheme.Hom.preimage_iSup, hcov]; rfl) (fun k => by rw [GlobalTheory.nonzeroLocus_secPull]; exact (haff k).preimage h) (secComb …`. Establish `hE : nonzeroLocus (secComb a fun k => GlobalTheory.secPull (σ k) h) = (π ⁻¹ᵁ V).ι ⁻¹ᵁ D`. Establish `key : ∀ (K : Type) [Field K] (y : Sp K ⟶ (π ⁻¹ᵁ V).toScheme), ⊤ ≤ y ⁻¹ᵁ nonzeroLocus (secComb a fun k => GlobalTheory.secPull (σ k) h) ↔ ⊤ ≤ y ⁻¹ᵁ ((π ⁻¹ᵁ V).ι ⁻¹ᵁ D)`. Introduce `K _ y`.

Take `⟨w, hw, hiff'⟩` from `exists_crd_secComb h σ hcov a y`. Establish `e₁ : (y ≫ h) ≫ (π ⁻¹ᵁ W').ι = y ≫ (π ⁻¹ᵁ V).ι` using `by rw [Category.assoc, hι]`. Establish `e₂ : (y ≫ h) ≫ (π ⁻¹ᵁ W').ι ≫ π = y ≫ (π ⁻¹ᵁ V).ι ≫ π`. Rewrite using `[← Category.assoc, e₁, Category.assoc]`. Establish `h₄` using `hiff K (y ≫ h) w (by rw [e₂]; exact fun p _ => (hle' (y p).2).1) hw`.

Rewrite `h₄` using `[e₁, e₂]`. Use `hiff'.trans (Iff.trans ?_ h₄.symm)` and prove the remaining obligations. Establish `e₃ : ∀ k, valR y ⊤ (a k) = valR (y ≫ (π ⁻¹ᵁ V).ι ≫ π) (W ⊓ W') (m k)` using `fun k => GlobalTheory.Points.valR_appLE y _ ha le_top _`. Simplify using `only [e₃]`. Conclude with `opens_eq_of_field_points key`.

Rewrite `ht` using `[hE]`. Establish `h₆` using `ht.image_of_isOpenImmersion (π ⁻¹ᵁ V).ι`. Rewrite `h₆` using `[Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]`. Then use the resulting hypothesis. Conclude with `isAffine_of_isAffineHom (π.resLE W D hD)`.
-/
theorem isAffineOpen_of_comb : ∀ (P Z : Scheme.{0}) (π : P ⟶ Z) [IsProper π] (J : Type) [Fintype J] (D : P.Opens) (W : Z.Opens), IsAffineOpen W → D ≤ π ⁻¹ᵁ W → (∀ z ∈ W, ∃ (W' : Z.Opens) (H : LB (π ⁻¹ᵁ W').toScheme) (σ : J → H.Sec) (m : J → Γ(Z, W ⊓ W')), z ∈ W' ∧ IsAffineOpen W' ∧ ⨆ k, nonzeroLocus (σ k) = ⊤ ∧ (∀ k, IsAffineOpen (nonzeroLocus (σ k))) ∧ ∀ (K : Type) [Field K] (y : Sp K ⟶ (π ⁻¹ᵁ W').toScheme) (w : J → K), ⊤ ≤ (y ≫ (π ⁻¹ᵁ W').ι ≫ π) ⁻¹ᵁ W → Crd H σ y w → (⊤ ≤ (y ≫ (π ⁻¹ᵁ W').ι) ⁻¹ᵁ D ↔ ∑ k, valR (y ≫ (π ⁻¹ᵁ W').ι ≫ π) (W ⊓ W') (m k) * w k ≠ 0)) → IsAffineOpen D := by
  intro P Z π _ J _ D W hW hD H
  have : IsAffine W := hW
  have : IsAffineHom (π.resLE W D hD) := by
    refine isAffineHom_of_forall_exists_isAffineOpen _ fun z => ?_
    obtain ⟨W', H, σ, m, hz, hW', hcov, haff, hiff⟩ := H z.1 z.2
    obtain ⟨V, hV, hzV, hle⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (x := z.1) (U := W ⊓ W') ⟨z.2, hz⟩
    have hle' : V ≤ W ⊓ W' := hle
    have : IsAffine V := hV
    refine ⟨W.ι ⁻¹ᵁ V, hzV, hV.preimage_of_isOpenImmersion _ (by simpa using hle'.trans inf_le_left), ?_⟩
    rw [← Scheme.Hom.comp_preimage, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_preimage,
      ← D.ι.isAffineOpen_iff_of_isOpenImmersion, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι]
    have e : V ≤ W' := hle'.trans inf_le_right
    have := isAffineHom_homOfLE π e hV hW'
    set h := P.homOfLE (π.preimage_mono e) with hh
    have hι : h ≫ (π ⁻¹ᵁ W').ι = (π ⁻¹ᵁ V).ι := Scheme.homOfLE_ι _ _
    have ha : ⊤ ≤ ((π ⁻¹ᵁ V).ι ≫ π) ⁻¹ᵁ (W ⊓ W') := fun p _ => hle' p.2
    let a : J → Γ((π ⁻¹ᵁ V).toScheme, ⊤) := fun k => (((π ⁻¹ᵁ V).ι ≫ π).appLE (W ⊓ W') ⊤ ha).hom (m k)
    have ht := isAffineOpen_nonzeroLocus_of_universallyClosed (π ∣_ V) (fun k => GlobalTheory.secPull (σ k) h)
      (by simp only [GlobalTheory.nonzeroLocus_secPull]; rw [← Scheme.Hom.preimage_iSup, hcov]; rfl)
      (fun k => by rw [GlobalTheory.nonzeroLocus_secPull]; exact (haff k).preimage h)
      (secComb a fun k => GlobalTheory.secPull (σ k) h)
    have hE : nonzeroLocus (secComb a fun k => GlobalTheory.secPull (σ k) h) = (π ⁻¹ᵁ V).ι ⁻¹ᵁ D := by
      have key : ∀ (K : Type) [Field K] (y : Sp K ⟶ (π ⁻¹ᵁ V).toScheme),
          ⊤ ≤ y ⁻¹ᵁ nonzeroLocus (secComb a fun k => GlobalTheory.secPull (σ k) h) ↔ ⊤ ≤ y ⁻¹ᵁ ((π ⁻¹ᵁ V).ι ⁻¹ᵁ D) := by
        intro K _ y
        obtain ⟨w, hw, hiff'⟩ := exists_crd_secComb h σ hcov a y
        have e₁ : (y ≫ h) ≫ (π ⁻¹ᵁ W').ι = y ≫ (π ⁻¹ᵁ V).ι := by rw [Category.assoc, hι]
        have e₂ : (y ≫ h) ≫ (π ⁻¹ᵁ W').ι ≫ π = y ≫ (π ⁻¹ᵁ V).ι ≫ π := by
          rw [← Category.assoc, e₁, Category.assoc]
        have h₄ := hiff K (y ≫ h) w (by rw [e₂]; exact fun p _ => (hle' (y p).2).1) hw
        rw [e₁, e₂] at h₄
        refine hiff'.trans (Iff.trans ?_ h₄.symm)
        have e₃ : ∀ k, valR y ⊤ (a k) = valR (y ≫ (π ⁻¹ᵁ V).ι ≫ π) (W ⊓ W') (m k) := fun k =>
          GlobalTheory.Points.valR_appLE y _ ha le_top _
        simp only [e₃]
      exact opens_eq_of_field_points key
    rw [hE] at ht
    have h₆ := ht.image_of_isOpenImmersion (π ⁻¹ᵁ V).ι
    rwa [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm] at h₆
  exact isAffine_of_isAffineHom (π.resLE W D hD)

end GlobalTheory.ZH.CombLocus
end
