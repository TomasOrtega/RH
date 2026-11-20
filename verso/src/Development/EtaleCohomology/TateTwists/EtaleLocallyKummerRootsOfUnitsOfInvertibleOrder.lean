import Development.EtaleCohomology.TateTwists.EtaleLocallyExistsPrimitiveRootOfUnityOfInvertib

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.EtaleFoundations.PrimLocKumPf

noncomputable abbrev kpol {A : Type} [CommRing A] (q : ℕ) (u : A) : A[X] := X ^ q - C u

/- English proof (translation)
The claim follows from `monic_X_pow_sub_C u (NeZero.ne q)`.
-/
theorem kpol_monic {A : Type} [CommRing A] (q : ℕ) [NeZero q] (u : A) : (kpol q u).Monic :=
  monic_X_pow_sub_C u (NeZero.ne q)

/- English proof (translation)
The claim follows from `natDegree_X_pow_sub_C`.
-/
theorem kpol_natDegree {A : Type} [CommRing A] [Nontrivial A] (q : ℕ) [NeZero q] (u : A) :
    (kpol q u).natDegree = q :=
  natDegree_X_pow_sub_C

/- English proof (translation)
Establish `h` using `AdjoinRoot.eval₂_root (kpol q u)`. Simplify using `only [eval₂_sub, eval₂_X_pow, eval₂_C] at h`. Rewrite `h` using `[← AdjoinRoot.algebraMap_eq]`. Conclude with `sub_eq_zero.mp h`.
-/
theorem root_pow {A : Type} [CommRing A] (q : ℕ) (u : A) :
    AdjoinRoot.root (kpol q u) ^ q = algebraMap A (AdjoinRoot (kpol q u)) u := by
  have h := AdjoinRoot.eval₂_root (kpol q u)
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  rw [← AdjoinRoot.algebraMap_eq] at h
  exact sub_eq_zero.mp h

/- English proof (translation)
Establish `h : IsUnit (AdjoinRoot.root (kpol q (u : A)) ^ q)`. Rewrite using `[root_pow]`. Conclude with `u.isUnit.map _`. Conclude with `(isUnit_pow_iff (NeZero.ne q)).mp h`.
-/
theorem root_isUnit {A : Type} [CommRing A] (q : ℕ) [NeZero q] (u : Aˣ) :
    IsUnit (AdjoinRoot.root (kpol q (u : A))) := by
  have h : IsUnit (AdjoinRoot.root (kpol q (u : A)) ^ q) := by
    rw [root_pow]; exact u.isUnit.map _
  exact (isUnit_pow_iff (NeZero.ne q)).mp h

/- English proof (translation)
Establish `hd : derivative (kpol q (u : A)) = C (q : A) * X ^ (q - 1)`. Simplify using `[kpol, derivative_X_pow]`. Rewrite using `[hd, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C]`. Use `IsUnit.mul (hq.map _) ?_` and prove the remaining obligations. Conclude with `(root_isUnit q u).pow _`.
-/
theorem deriv_isUnit {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) (u : Aˣ) :
    IsUnit (AdjoinRoot.mk (kpol q (u : A)) (derivative (kpol q (u : A)))) := by
  have hd : derivative (kpol q (u : A)) = C (q : A) * X ^ (q - 1) := by
    simp [kpol, derivative_X_pow]
  rw [hd, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
  refine IsUnit.mul (hq.map _) ?_
  exact (root_isUnit q u).pow _

/- English proof (translation)
The claim follows from `let P : StandardEtalePair A := ⟨kpol q (u : A), kpol_monic q _, derivative (kpol q (u : A)), 1, 0, 1, by simp⟩ .of_equiv (P.equivAwayAdjoinRoot.trans ((IsLocalization.atUnit _ (Localization.Away (AdjoinRoot.mk P.f (derivative (kpol q (u : A))))) _ (deriv_isUnit q hq u)).symm.rest …`.
-/
theorem etale_kum {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) (u : Aˣ) :
    Algebra.Etale A (AdjoinRoot (kpol q (u : A))) :=
  let P : StandardEtalePair A := ⟨kpol q (u : A), kpol_monic q _, derivative (kpol q (u : A)), 1, 0, 1, by simp⟩
  .of_equiv (P.equivAwayAdjoinRoot.trans
    ((IsLocalization.atUnit _ (Localization.Away (AdjoinRoot.mk P.f (derivative (kpol q (u : A))))) _
      (deriv_isUnit q hq u)).symm.restrictScalars A))

/- English proof (translation)
Establish `hf` using `kpol_monic q u`. Establish `: Module.Free A (AdjoinRoot (kpol q u))` using `hf.free_adjoinRoot`. Establish `: Module.Finite A (AdjoinRoot (kpol q u))` using `hf.finite_adjoinRoot`. Establish `hr : Module.finrank A (AdjoinRoot (kpol q u)) = q`. Rewrite using `[Module.finrank_eq_card_basis (AdjoinRoot.powerBasis' hf).basis, Fintype.card_fin]`.

Conclude with `kpol_natDegree q u`. Establish `: Nontrivial (AdjoinRoot (kpol q u))` using `Module.nontrivial_of_finrank_pos (R := A) (by rw [hr]; exact Nat.pos_of_neZero q)`. Use `infer_instance`.
-/
theorem ff_kum {A : Type} [CommRing A] [Nontrivial A] (q : ℕ) [NeZero q] (u : A) :
    Module.FaithfullyFlat A (AdjoinRoot (kpol q u)) := by
  have hf := kpol_monic q u
  have : Module.Free A (AdjoinRoot (kpol q u)) := hf.free_adjoinRoot
  have : Module.Finite A (AdjoinRoot (kpol q u)) := hf.finite_adjoinRoot
  have hr : Module.finrank A (AdjoinRoot (kpol q u)) = q := by
    rw [Module.finrank_eq_card_basis (AdjoinRoot.powerBasis' hf).basis, Fintype.card_fin]
    exact kpol_natDegree q u
  have : Nontrivial (AdjoinRoot (kpol q u)) :=
    Module.nontrivial_of_finrank_pos (R := A) (by rw [hr]; exact Nat.pos_of_neZero q)
  infer_instance

/- English proof (translation)
Introduce and unpack `V W g k ⟨v, hv⟩`. Use `⟨Units.map k.appTop.hom.toMonoidHom v, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_pow, hv]`. Use `ext`. Apply the tactic sequence `simp <;> rfl`.
-/
theorem mono_kum (q : ℕ) {U : Scheme.{0}} (u : (Γ(U, ⊤))ˣ) :
    ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V),
    (∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u) →
    ∃ v : (Γ(W, ⊤))ˣ, v ^ q = Units.map (k ≫ g).appTop.hom.toMonoidHom u := by
  rintro V W g k ⟨v, hv⟩
  refine ⟨Units.map k.appTop.hom.toMonoidHom v, ?_⟩
  rw [← map_pow, hv]
  ext
  simp <;> rfl

/- English proof (translation)
Take `⟨W, hW, hyW, -⟩ : ∃ W : U.Opens, IsAffineOpen W ∧ y ∈ W ∧ W ≤ ⊤` from `(TopologicalSpace.Opens.isBasis_iff_nbhd.mp U.isBasis_affineOpens) (Set.mem_univ y)`. Take `⟨z, hz⟩ : y ∈ Set.range hW.fromSpec` from `by rw [hW.range_fromSpec]; exact hyW`. Set `A : CommRingCat.{0}` to `Γ(U, W)`. Establish `: Nontrivial A`. Use `z.asIdeal.ne_top_iff_one.mp z.isPrime.ne_top` as an intermediate fact.

Conclude with `⟨⟨1, 0, fun h => this (h ▸ z.asIdeal.zero_mem)⟩⟩`. Set `ρ : Γ(U, ⊤) →+* A` to `(Scheme.ΓSpecIso A).hom.hom.comp hW.fromSpec.appTop.hom`. Set `u₁ : Aˣ` to `Units.map ρ.toMonoidHom u`. Establish `hqA : IsUnit (q : A)` using `by simpa using hq.map ρ`. Set `B : CommRingCat.{0}` to `CommRingCat.of (AdjoinRoot (kpol q (u₁ : A)))`.

Set `φ : A ⟶ B` to `CommRingCat.ofHom (algebraMap A (AdjoinRoot (kpol q (u₁ : A))))`. Establish `he : Algebra.Etale A (AdjoinRoot (kpol q (u₁ : A)))` using `etale_kum q hqA u₁`. Establish `hff : Module.FaithfullyFlat A (AdjoinRoot (kpol q (u₁ : A)))` using `ff_kum q _`. Establish `hE : Etale (Spec.map φ)`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @Etale)]`.

Conclude with `RingHom.etale_algebraMap.mpr he`. Establish `hS : Surjective (Spec.map φ)` using `((flat_and_surjective_SpecMap_iff φ).mpr (RingHom.faithfullyFlat_algebraMap_iff.mpr hff)).2`. Use `⟨Spec B, Spec.map φ ≫ hW.fromSpec, inferInstance, inferInstance, ?_, ?_⟩` and prove the remaining obligations. Take `⟨w, hw⟩` from `hS.surj z`. Conclude with `⟨w, by simp [hw, hz]⟩`.

Take `⟨r, hr⟩` from `root_isUnit q u₁`. Use `⟨Units.map (Scheme.ΓSpecIso B).inv.hom.toMonoidHom r, ?_⟩` and prove the remaining obligations. Use `ext`. Use `set w : Γ(Spec A, ⊤) := hW.fromSpec.appTop.hom (u : Γ(U, ⊤)) with hw`. Establish `hnat : (Scheme.ΓSpecIso B).hom.hom ((Spec.map φ).appTop.hom w) = φ.hom ((Scheme.ΓSpecIso A).hom.hom w)`.

Rewrite using `[← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply]`. Simplify using `only [Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe]`. Rewrite using `[Scheme.Hom.comp_appTop, CommRingCat.hom_comp]`. Use `show ((Scheme.ΓSpecIso B).inv.hom (r : AdjoinRoot (kpol q (u₁ : A)))) ^ q = (Spec.map φ).appTop.hom w`. Rewrite using `[← map_pow, hr, root_pow]`.

Express the relevant statement in the definitionally equal form `(Scheme.ΓSpecIso B).inv.hom (φ.hom ((Scheme.ΓSpecIso A).hom.hom w)) = _`. Rewrite using `[← hnat, ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]`.
-/
theorem pt (q : ℕ) [NeZero q] (U : Scheme.{0}) (hq : IsUnit (q : Γ(U, ⊤))) (u : (Γ(U, ⊤))ˣ)
    (y : U) : ∃ (V : Scheme.{0}) (g : V ⟶ U), IsAffine V ∧ Etale g ∧ y ∈ Set.range g ∧
      ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u := by
  obtain ⟨W, hW, hyW, -⟩ : ∃ W : U.Opens, IsAffineOpen W ∧ y ∈ W ∧ W ≤ ⊤ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp U.isBasis_affineOpens) (Set.mem_univ y)
  obtain ⟨z, hz⟩ : y ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact hyW
  let A : CommRingCat.{0} := Γ(U, W)
  have : Nontrivial A := by
    have := z.asIdeal.ne_top_iff_one.mp z.isPrime.ne_top
    exact ⟨⟨1, 0, fun h => this (h ▸ z.asIdeal.zero_mem)⟩⟩
  let ρ : Γ(U, ⊤) →+* A := (Scheme.ΓSpecIso A).hom.hom.comp hW.fromSpec.appTop.hom
  let u₁ : Aˣ := Units.map ρ.toMonoidHom u
  have hqA : IsUnit (q : A) := by simpa using hq.map ρ
  let B : CommRingCat.{0} := CommRingCat.of (AdjoinRoot (kpol q (u₁ : A)))
  let φ : A ⟶ B := CommRingCat.ofHom (algebraMap A (AdjoinRoot (kpol q (u₁ : A))))
  have he : Algebra.Etale A (AdjoinRoot (kpol q (u₁ : A))) := etale_kum q hqA u₁
  have hff : Module.FaithfullyFlat A (AdjoinRoot (kpol q (u₁ : A))) := ff_kum q _
  have hE : Etale (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr he
  have hS : Surjective (Spec.map φ) :=
    ((flat_and_surjective_SpecMap_iff φ).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr hff)).2
  refine ⟨Spec B, Spec.map φ ≫ hW.fromSpec, inferInstance, inferInstance, ?_, ?_⟩
  · obtain ⟨w, hw⟩ := hS.surj z
    exact ⟨w, by simp [hw, hz]⟩
  · obtain ⟨r, hr⟩ := root_isUnit q u₁
    refine ⟨Units.map (Scheme.ΓSpecIso B).inv.hom.toMonoidHom r, ?_⟩
    ext
    set w : Γ(Spec A, ⊤) := hW.fromSpec.appTop.hom (u : Γ(U, ⊤)) with hw
    have hnat : (Scheme.ΓSpecIso B).hom.hom ((Spec.map φ).appTop.hom w) =
        φ.hom ((Scheme.ΓSpecIso A).hom.hom w) := by
      rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply]
    simp only [Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe]
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
    show ((Scheme.ΓSpecIso B).inv.hom (r : AdjoinRoot (kpol q (u₁ : A)))) ^ q =
      (Spec.map φ).appTop.hom w
    rw [← map_pow, hr, root_pow]
    change (Scheme.ΓSpecIso B).inv.hom (φ.hom ((Scheme.ΓSpecIso A).hom.hom w)) = _
    rw [← hnat, ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]

end LateralTheory.EtaleFoundations.PrimLocKumPf

/- English proof (translation)
Introduce `q _ U hq u`. Rewrite using `[LateralTheory.EtaleFoundations.etale_sheaf_section_locally_iff_of_presheaf_facts U _ (LateralTheory.EtaleFoundations.PrimLocKumPf.mono_kum q u)]`. Conclude with `LateralTheory.EtaleFoundations.PrimLocKumPf.pt q U hq u`.
-/
theorem LateralTheory.EtaleFoundations.etale_locally_kummer_roots_of_units_of_invertible_order : LateralTheory.EtaleFoundations.EtaleLocallyKummerRootsOfUnits := by
  intro q _ U hq u
  rw [LateralTheory.EtaleFoundations.etale_sheaf_section_locally_iff_of_presheaf_facts U _ (LateralTheory.EtaleFoundations.PrimLocKumPf.mono_kum q u)]
  exact LateralTheory.EtaleFoundations.PrimLocKumPf.pt q U hq u
