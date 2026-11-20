import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KisinCrTrivial
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RestrictionToDecompositionGroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ConstOfChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.UniversalDiagonalOfTriangularPoints
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FrameClassOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostOk
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IrrOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPtOfIsPtHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.GaussianFieldRangeEqKerQuarticChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MatIrr

open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete
  UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom

/- English proof (translation)
Rewrite using `[totallyDisconnectedSpace_iff_connectedComponent_one]`. Use `Set.eq_singleton_iff_unique_mem.2 ⟨mem_connectedComponent, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `QuotientGroup.mk_surjective y`. Assume the negation of the conclusion as `hx`. Establish `hx' : x ∉ N` using `fun h => hx ((QuotientGroup.eq_one_iff x).2 h)`.

Establish `ho : IsOpen {g : G | g * x ∉ N}` using `hN.isOpen_compl.preimage (continuous_mul_const x)`. Take `⟨U, hU⟩` from `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho (by simpa using hx')`. Set `V : Subgroup (G ⧸ N)` to `U.toSubgroup.map (QuotientGroup.mk' N)`. Establish `hVo : IsOpen (V : Set (G ⧸ N))` using `QuotientGroup.isOpenMap_coe _ U.isOpen'`. Establish `hV : IsClopen (V : Set (G ⧸ N))` using `⟨V.isClosed_of_isOpen hVo, hVo⟩`.

Take `⟨u, hu, hux⟩` from `hV.connectedComponent_subset V.one_mem hy`. Conclude with `hU (U.toSubgroup.inv_mem hu) (QuotientGroup.eq.1 hux)`.
-/
private theorem totDisc_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_one]
  refine Set.eq_singleton_iff_unique_mem.2 ⟨mem_connectedComponent, fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  by_contra hx
  have hx' : x ∉ N := fun h => hx ((QuotientGroup.eq_one_iff x).2 h)
  have ho : IsOpen {g : G | g * x ∉ N} := hN.isOpen_compl.preimage (continuous_mul_const x)
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho (by simpa using hx')
  let V : Subgroup (G ⧸ N) := U.toSubgroup.map (QuotientGroup.mk' N)
  have hVo : IsOpen (V : Set (G ⧸ N)) := QuotientGroup.isOpenMap_coe _ U.isOpen'
  have hV : IsClopen (V : Set (G ⧸ N)) := ⟨V.isClosed_of_isOpen hVo, hVo⟩
  obtain ⟨u, hu, hux⟩ := hV.connectedComponent_subset V.one_mem hy
  exact hU (U.toSubgroup.inv_mem hu) (QuotientGroup.eq.1 hux)

open Matrix Formalism.MainNotions.N in
/- English proof (translation)
Set `e : (Fin n → k) ≃ₗ[k] (Fin n → k)` to `Matrix.toLin'OfInv (M := (h : Matrix (Fin n) (Fin n) k)) (M' := ((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (Units.mul_inv h) (Units.inv_mul h)`. Establish `he : ∀ v, e v = ((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ v` using `fun v => rfl`. Establish `key : ∀ g v, e ((ρ' g : Matrix (Fin n) (Fin n) k) *ᵥ v) = (ρ g : Matrix (Fin n) (Fin n) k) *ᵥ e v`. Introduce `g v`. Rewrite using `[he, he, hh, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]`.

Use `congr 2`. Use `group`. Introduce `W hW`. Take `⟨W', hW', hc⟩` from `hρ (W.map (e : (Fin n → k) →ₗ[k] (Fin n → k))) (by`. Introduce and unpack `g _ ⟨v, hv, rfl⟩`.

Conclude with `⟨_, hW g v hv, key g v⟩)`. Use `⟨W'.comap (e : (Fin n → k) →ₗ[k] (Fin n → k)), fun g v hv => ?_, ?_⟩` and prove the remaining obligations. Use `show e _ ∈ W'`. Rewrite using `[key]`. Conclude with `hW' g _ hv`.

Use `(Submodule.orderIsoMapComap e).symm.isCompl hc` as an intermediate fact. Establish `h2 : IsCompl ((W.map (e : (Fin n → k) →ₗ[k] (Fin n → k))).comap (e : (Fin n → k) →ₗ[k] (Fin n → k))) (W'.comap (e : (Fin n → k) →ₗ[k] (Fin n → k)))` using `this`. Rewrite `h2` using `[Submodule.comap_map_eq_of_injective e.injective]`. Then use the resulting hypothesis.
-/
private theorem ss_conj {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {ρ ρ' : Γ →* GL (Fin n) k} (h : GL (Fin n) k)
    (hh : ∀ g, ρ' g = h * ρ g * h⁻¹) (hρ : IsSSRep ρ) : IsSSRep ρ' := by
  let e : (Fin n → k) ≃ₗ[k] (Fin n → k) := Matrix.toLin'OfInv (M := (h : Matrix (Fin n) (Fin n) k))
    (M' := ((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (Units.mul_inv h) (Units.inv_mul h)
  have he : ∀ v, e v = ((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ v := fun v => rfl
  have key : ∀ g v, e ((ρ' g : Matrix (Fin n) (Fin n) k) *ᵥ v) = (ρ g : Matrix (Fin n) (Fin n) k) *ᵥ e v := by
    intro g v
    rw [he, he, hh, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  intro W hW
  obtain ⟨W', hW', hc⟩ := hρ (W.map (e : (Fin n → k) →ₗ[k] (Fin n → k))) (by
    rintro g _ ⟨v, hv, rfl⟩
    exact ⟨_, hW g v hv, key g v⟩)
  refine ⟨W'.comap (e : (Fin n → k) →ₗ[k] (Fin n → k)), fun g v hv => ?_, ?_⟩
  · show e _ ∈ W'
    rw [key]
    exact hW' g _ hv
  · have := (Submodule.orderIsoMapComap e).symm.isCompl hc
    have h2 : IsCompl ((W.map (e : (Fin n → k) →ₗ[k] (Fin n → k))).comap (e : (Fin n → k) →ₗ[k] (Fin n → k)))
      (W'.comap (e : (Fin n → k) →ₗ[k] (Fin n → k))) := this
    rwa [Submodule.comap_map_eq_of_injective e.injective] at h2

/- English proof (translation)
Take `⟨π, h1, h2, h3, h4⟩` from `H`. Use `⟨π, h1, h2, ss_conj h.choose h.choose_spec h3, h4.mono fun w ⟨B, hB, hB'⟩ => ⟨B, hB, hB'.of_iso h⟩⟩` and prove the remaining obligations.
-/
private theorem autCsd_iso {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] {l : ℕ}
    [Fact l.Prime] {n : ℕ} {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} (h : Af.RepIso r r')
    (H : Af.IsAutCsd ι r) : Af.IsAutCsd ι r' := by
  obtain ⟨π, h1, h2, h3, h4⟩ := H
  refine ⟨π, h1, h2, ss_conj h.choose h.choose_spec h3, h4.mono fun w ⟨B, hB, hB'⟩ => ⟨B, hB, hB'.of_iso h⟩⟩

/- English proof (translation)
Take `⟨g, hg⟩` from `h`. Use `⟨g, fun s => Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, Units.val_mul, Af.tw_val, Af.tw_val, hg, Units.val_mul, Units.val_mul, Matrix.mul_smul, Matrix.smul_mul]`.
-/
private theorem tw_iso {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k} (χ : Γ →* kˣ)
    (h : Af.RepIso r r') : Af.RepIso (Af.tw r χ) (Af.tw r' χ) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun s => Units.ext ?_⟩
  rw [Units.val_mul, Units.val_mul, Af.tw_val, Af.tw_val, hg, Units.val_mul, Units.val_mul, Matrix.mul_smul,
    Matrix.smul_mul]

/- English proof (translation)
Establish `e : conjBy h r g = GG.ofGL h * r g * GG.ofGL h⁻¹`. Rewrite using `[map_inv]`. Both sides reduce to the same expression. Rewrite using `[e, SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.left_inl, SemidirectProduct.right_inl, sgnAct_one, SemidirectProduct.mul_right, SemidirectProduct.right_inl, hg, mul_one, sgnAct_one]`.
-/
private theorem conj_left {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) (h : GL (Fin 3) R) (g : G)
    (hg : (r g).right = 1) : (conjBy h r g).left = h * (r g).left * h⁻¹ := by
  have e : conjBy h r g = GG.ofGL h * r g * GG.ofGL h⁻¹ := by
    rw [map_inv]; rfl
  rw [e, SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.left_inl,
    SemidirectProduct.left_inl, SemidirectProduct.right_inl, sgnAct_one, SemidirectProduct.mul_right,
    SemidirectProduct.right_inl, hg, mul_one, sgnAct_one]

open Matrix in
/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qf5.matIrr_conj h e H`.
-/
private theorem matIrr_conj {G R : Type} [Group G] [CommRing R] {m : ℕ} {U : Subgroup G}
    {a a' : G → Matrix (Fin m) (Fin m) R} (h : GL (Fin m) R)
    (e : ∀ g ∈ U, a g = ((h⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) * a' g * h) (H : MatIrr U a) :
    MatIrr U a' :=
  _root_.UpperTheory.Reformulated.B.Qf5.matIrr_conj h e H

/- English proof (translation)
Use `letI : Algebra (ResidueField O) A := (Ideal.Quotient.lift _ (algebraMap O A) h0).toAlgebra`. Set `Φ : G →* (ResidueField O)ˣ` to `(Units.map (residue O).toMonoidHom).comp Ψ`. Establish `e : ∀ g, ((r0 η Φ g).mat).map (algebraMap (ResidueField O) A) = ((r0 η Ψ g).mat).map (algebraMap O A)`. Introduce `g`. Rewrite using `[GG.mat, GG.mat, unitaryThreeReflection_left, unitaryThreeReflection_left, tor_val, tor_val, Matrix.diagonal_map (map_zero _), Matrix.diagonal_map (map_zero _)]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[show Φ g ^ wt1 i = Units.map (residue O).toMonoidHom (Ψ g ^ wt1 i) from (map_zpow (Units.map (residue O).toMonoidHom) (Ψ g) _).symm]`. Both sides reduce to the same expression. Use `(constOfChar G (ResidueField O) A ?_ η Φ c g₁ ⟨hM.csq, hM.ηc, ?_, hM.ηg, ?_⟩ r hr.mult (fun g => ?_) hN U hU fun g hg hη => ?_).1` and prove the remaining obligations.

Simplify `(h2.map (residue O)).ne_zero` using `[map_ofNat]`. Use `show Units.map _ (Ψ c) = 1`. Rewrite using `[hM.Ψc, map_one]`. Use `hM.Ψg.map (residue O)` as an intermediate fact. Rewrite `this` using `[map_sub, map_pow, map_one]`. Then use the resulting hypothesis.

Rewrite using `[e]`. Conclude with `hr.red g`. Rewrite using `[e]`. Conclude with `hch g hg hη`.
-/
private theorem tri_of_char {O G A : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [Group G]
    [CommRing A] [IsDomain A] [IsLocalRing A] [Algebra O A] (h2 : IsUnit (2 : O))
    (h0 : ∀ a ∈ maximalIdeal O, algebraMap O A a = 0) {η : G →* ℤˣ} {Ψ : G →* Oˣ} {c g₁ : G} (hM : Marks η Ψ c g₁)
    {r : G →* GG 3 A} (hr : UnitaryThreeInertia.Red η Ψ r) (hN : Normalised c g₁ r) (U : Subgroup G) (hU : U.FiniteIndex)
    (hch : ∀ g ∈ U, η g = 1 → (r g).mat.charpoly = (((r0 η Ψ g).mat).map (algebraMap O A)).charpoly) :
    Upper η r ∨ Lower η r := by
  letI : Algebra (ResidueField O) A := (Ideal.Quotient.lift _ (algebraMap O A) h0).toAlgebra
  let Φ : G →* (ResidueField O)ˣ := (Units.map (residue O).toMonoidHom).comp Ψ
  have e : ∀ g, ((r0 η Φ g).mat).map (algebraMap (ResidueField O) A) = ((r0 η Ψ g).mat).map (algebraMap O A) := by
    intro g
    rw [GG.mat, GG.mat, unitaryThreeReflection_left, unitaryThreeReflection_left, tor_val, tor_val, Matrix.diagonal_map (map_zero _),
      Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    rw [show Φ g ^ wt1 i = Units.map (residue O).toMonoidHom (Ψ g ^ wt1 i) from
      (map_zpow (Units.map (residue O).toMonoidHom) (Ψ g) _).symm]
    rfl
  refine (constOfChar G (ResidueField O) A ?_ η Φ c g₁ ⟨hM.csq, hM.ηc, ?_, hM.ηg, ?_⟩ r hr.mult
    (fun g => ?_) hN U hU fun g hg hη => ?_).1
  · simpa [map_ofNat] using (h2.map (residue O)).ne_zero
  · show Units.map _ (Ψ c) = 1
    rw [hM.Ψc, map_one]
  · have := hM.Ψg.map (residue O)
    rwa [map_sub, map_pow, map_one] at this
  · rw [e]; exact hr.red g
  · rw [e]; exact hch g hg hη

/- English proof (translation)
Introduce `H K _ _ _ hK Ω _ _ _ l _ ι c N _ e ψ o₁ hd S A F hF`. Take `⟨σ, hσ, hc⟩` from `hF.cc`. Establish `hv : (A F.vl).valuation (l : Ω) < 1` using `by simpa using (hF.isOver F.vl (l : 𝓞 ℚ)).2 hF.vl`. Take `⟨g₁, hM, ⟨U, hU, hfin⟩, haut⟩` from `H K hK Ω l ι c N e ψ o₁ hd σ hσ (A F.vl) hv`. Establish `hη : ∀ g, F.η (toGS Ω _ g) = UnitaryThreeInertia.eta4 Ω g` using `fun g => by rw [← hF.η, hF.π]; rfl`.

Establish `hΨ : ∀ g, F.Ψ (toGS Ω _ g) = Chr.Psi l e (Chr.dirG ℚ Ω ψ) g` using `fun g => by rw [← hF.Ψ, hF.π]; rfl`. Rewrite `hc` using `[hF.π]`. Establish `hg : F.Marked (toGS Ω _ g₁)` using `⟨(hη g₁).trans hM.ηg, by rw [hΨ]; exact hM.Ψg⟩`. Use `haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω`. Use `haveI hcl := isClosed_NS Ω (S : Set UnitaryThreeInertia.Pl)`.

Use `haveI : CompactSpace (UnitaryThreeInertia.Gam Ω S) := inferInstance`. Use `haveI : T2Space (UnitaryThreeInertia.Gam Ω S) := inferInstance`. Use `haveI : TotallyDisconnectedSpace (UnitaryThreeInertia.Gam Ω S) := totDisc_quot _ hcl`. Establish `hOk` using `UnitaryThreeInertia.hostFrame_ok Ω c e ψ o₁ hd S A F hF`. Establish `hsurj : ∀ x : UnitaryThreeInertia.Gam Ω S, ∃ s, toGS Ω _ s = x` using `fun x => QuotientGroup.mk_surjective x`.

Use `⟨_, hg, fun R _ _ _ u hu => ?_⟩` and prove the remaining obligations. Establish `hM2 : Module.Finite c.O (UnitaryThreeInertia.wpart c.O u 0)`. Use `UnitaryThreeInertia.universal_diagonal_of_triangular_points F hOk (UnitaryThreeInertia.frame_class_one Ω c e ψ o₁ hd S A F hF) _ hg u hu fun B _ _ hB h0 r hr => ?_` and prove the remaining obligations. Use `haveI := hB.toIsDomain`. Use `haveI := hB.toIsDiscreteValuationRing`.

Establish `ho` using `ordPt_of_isPt Ω c e ψ o₁ hd S A F hF σ g₁ hc r hr`. Use `(tri_of_char hOk.two h0 hM ho.red ho.norm U hU (hfin B h0 _ ho)).imp (fun h g hg => ?_) fun h g hg => ?_` and prove the remaining obligations. Take `⟨s, rfl⟩` from `hsurj g`. Conclude with `h s ((hη s).symm.trans hg)`. Take `⟨s, rfl⟩` from `hsurj g`.

Conclude with `h s ((hη s).symm.trans hg)`. Use `⟨hM2, fun ξ r h1 h2 => ?_⟩` and prove the remaining obligations. Establish `hz : F.IsCharZeroPt _ r` using `UnitaryThreeInertia.isCharZeroPt_of_isPtHom (l := l) F hOk _ hg u hu hM2 ξ r h1`. Establish `hirr` using `UnitaryThreeInertia.matIrr_open Ω c e ψ o₁ hd S A F hF _ hg r hz h2`. Take `⟨B, _, _, t, r', hr', ht⟩` from `hz`.

Establish `ho` using `ordPt_of_isPt Ω c e ψ o₁ hd S A F hF σ g₁ hc r' hr'`. Establish `hm : ∀ s, (r (toGS Ω _ s)).right = UnitaryThreeInertia.eta4 Ω s` using `fun s => ((h1 _).1.trans (hu.pt.mult _)).trans (hη s)`. Establish `hl : ∀ s ∈ (UnitaryThreeInertia.eta4 Ω).ker, (UnitaryThreeInertia.push B.val (r'.comp (toGS Ω _)) s).left = tor _ t * (r (toGS Ω _ s)).left * (tor _ t)⁻¹` using `fun s hs => by`. Rewrite using `[← conj_left r _ _ ((hm s).trans hs), ← ht]`. Both sides reduce to the same expression.

Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `letI : Algebra K Ω := (IsAlgClosed.lift : K →ₐ[ℚ] Ω).toRingHom.toAlgebra`. Establish `hker : ∀ s : G K Ω, Base.galEmb ℚ K Ω s ∈ (UnitaryThreeInertia.eta4 Ω).ker` using `fun s => by`. Rewrite using `[← (UnitaryThreeInertia.gaussian_field_range_eq_ker_quartic_char.2 Ω K hK).1]`. Conclude with `⟨s, rfl⟩`.

Set `j : G K Ω →* (UnitaryThreeInertia.eta4 Ω).ker` to `(Base.galEmb ℚ K Ω).codRestrict _ hker`. Set `ρ : G K Ω →* GL (Fin 3) (Qbar l)` to `(glPart (UnitaryThreeInertia.eta4 Ω) (r.comp (toGS Ω _)) hm).comp j`. Set `ρ' : G K Ω →* GL (Fin 3) (Qbar l)` to `(glPart (UnitaryThreeInertia.eta4 Ω) (UnitaryThreeInertia.push B.val (r'.comp (toGS Ω _))) ho.red.mult).comp j`. Establish `hiso : Af.RepIso ρ ρ'` using `⟨tor _ t, fun s => hl _ (hker s)⟩`. Establish `key` using `haut B _ ho (fun V hV hVη => matIrr_conj (tor _ t) (fun s hs => by`.

Rewrite using `[mats, GG.mat, GG.mat, hl s (hVη hs), ← Units.val_mul, ← Units.val_mul]`. Use `congr 1`. Use the proof step `group) (hirr V hV hVη)) ρ' fun s => rfl`. Use `⟨inferInstance, inferInstance, ρ, fun s => rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[zpow_neg_one]`.

Conclude with `autCsd_iso (tw_iso _ hiso.symm') key`.
-/
theorem UpperTheory.V.Pr.symmetric_cube_theorem_of_endomorphisms :
    HostEnd → AutomorphyClauseStatement := by
  intro H K _ _ _ hK Ω _ _ _ l _ ι c N _ e ψ o₁ hd S A F hF
  obtain ⟨σ, hσ, hc⟩ := hF.cc
  have hv : (A F.vl).valuation (l : Ω) < 1 := by simpa using (hF.isOver F.vl (l : 𝓞 ℚ)).2 hF.vl
  obtain ⟨g₁, hM, ⟨U, hU, hfin⟩, haut⟩ := H K hK Ω l ι c N e ψ o₁ hd σ hσ (A F.vl) hv
  have hη : ∀ g, F.η (toGS Ω _ g) = UnitaryThreeInertia.eta4 Ω g := fun g => by rw [← hF.η, hF.π]; rfl
  have hΨ : ∀ g, F.Ψ (toGS Ω _ g) = Chr.Psi l e (Chr.dirG ℚ Ω ψ) g := fun g => by rw [← hF.Ψ, hF.π]; rfl
  rw [hF.π] at hc
  have hg : F.Marked (toGS Ω _ g₁) := ⟨(hη g₁).trans hM.ηg, by rw [hΨ]; exact hM.Ψg⟩
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI hcl := isClosed_NS Ω (S : Set UnitaryThreeInertia.Pl)
  haveI : CompactSpace (UnitaryThreeInertia.Gam Ω S) := inferInstance
  haveI : T2Space (UnitaryThreeInertia.Gam Ω S) := inferInstance
  haveI : TotallyDisconnectedSpace (UnitaryThreeInertia.Gam Ω S) := totDisc_quot _ hcl
  have hOk := UnitaryThreeInertia.hostFrame_ok Ω c e ψ o₁ hd S A F hF
  have hsurj : ∀ x : UnitaryThreeInertia.Gam Ω S, ∃ s, toGS Ω _ s = x := fun x => QuotientGroup.mk_surjective x
  refine ⟨_, hg, fun R _ _ _ u hu => ?_⟩
  have hM2 : Module.Finite c.O (UnitaryThreeInertia.wpart c.O u 0) := by
    refine UnitaryThreeInertia.universal_diagonal_of_triangular_points F hOk (UnitaryThreeInertia.frame_class_one Ω c e ψ o₁ hd S A F hF) _ hg u hu fun B _ _ hB h0 r hr => ?_
    haveI := hB.toIsDomain
    haveI := hB.toIsDiscreteValuationRing
    have ho := ordPt_of_isPt Ω c e ψ o₁ hd S A F hF σ g₁ hc r hr
    refine (tri_of_char hOk.two h0 hM ho.red ho.norm U hU (hfin B h0 _ ho)).imp (fun h g hg => ?_) fun h g hg => ?_
    · obtain ⟨s, rfl⟩ := hsurj g
      exact h s ((hη s).symm.trans hg)
    · obtain ⟨s, rfl⟩ := hsurj g
      exact h s ((hη s).symm.trans hg)
  refine ⟨hM2, fun ξ r h1 h2 => ?_⟩
  have hz : F.IsCharZeroPt _ r := UnitaryThreeInertia.isCharZeroPt_of_isPtHom (l := l) F hOk _ hg u hu hM2 ξ r h1
  have hirr := UnitaryThreeInertia.matIrr_open Ω c e ψ o₁ hd S A F hF _ hg r hz h2
  obtain ⟨B, _, _, t, r', hr', ht⟩ := hz
  have ho := ordPt_of_isPt Ω c e ψ o₁ hd S A F hF σ g₁ hc r' hr'
  have hm : ∀ s, (r (toGS Ω _ s)).right = UnitaryThreeInertia.eta4 Ω s := fun s =>
    ((h1 _).1.trans (hu.pt.mult _)).trans (hη s)
  have hl : ∀ s ∈ (UnitaryThreeInertia.eta4 Ω).ker, (UnitaryThreeInertia.push B.val (r'.comp (toGS Ω _)) s).left =
      tor _ t * (r (toGS Ω _ s)).left * (tor _ t)⁻¹ := fun s hs => by
    rw [← conj_left r _ _ ((hm s).trans hs), ← ht]
    rfl
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  letI : Algebra K Ω := (IsAlgClosed.lift : K →ₐ[ℚ] Ω).toRingHom.toAlgebra
  have hker : ∀ s : G K Ω, Base.galEmb ℚ K Ω s ∈ (UnitaryThreeInertia.eta4 Ω).ker := fun s => by
    rw [← (UnitaryThreeInertia.gaussian_field_range_eq_ker_quartic_char.2 Ω K hK).1]
    exact ⟨s, rfl⟩
  let j : G K Ω →* (UnitaryThreeInertia.eta4 Ω).ker := (Base.galEmb ℚ K Ω).codRestrict _ hker
  let ρ : G K Ω →* GL (Fin 3) (Qbar l) := (glPart (UnitaryThreeInertia.eta4 Ω) (r.comp (toGS Ω _)) hm).comp j
  let ρ' : G K Ω →* GL (Fin 3) (Qbar l) :=
    (glPart (UnitaryThreeInertia.eta4 Ω) (UnitaryThreeInertia.push B.val (r'.comp (toGS Ω _))) ho.red.mult).comp j
  have hiso : Af.RepIso ρ ρ' := ⟨tor _ t, fun s => hl _ (hker s)⟩
  have key := haut B _ ho (fun V hV hVη => matIrr_conj (tor _ t) (fun s hs => by
    rw [mats, GG.mat, GG.mat, hl s (hVη hs), ← Units.val_mul, ← Units.val_mul]
    congr 1
    group) (hirr V hV hVη)) ρ' fun s => rfl
  refine ⟨inferInstance, inferInstance, ρ, fun s => rfl, ?_⟩
  rw [zpow_neg_one]
  exact autCsd_iso (tw_iso _ hiso.symm') key
