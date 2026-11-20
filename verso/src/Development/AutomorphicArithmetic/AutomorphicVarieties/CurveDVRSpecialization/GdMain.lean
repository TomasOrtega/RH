import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KisinCrTrivial
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.GfResZpow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.MatIrrOpenGd
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.WeightZeroAlgebraLeEntryAlgebra
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ConjTor
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MatIrr

open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

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
Take `⟨g, hg⟩` from `h`. Use `⟨ss_conj g hg H.1, H.2.mono fun w hw A hA => ⟨fun s hs => ?_, fun σ hσ => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hg, (hw A hA).1 s hs, mul_one, mul_inv_cancel]`. Rewrite using `[← (hw A hA).2 σ hσ, hg, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]`.
-/
private theorem att_iso {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {k : ℕ} {ι : Qbar l ≃+* ℂ}
    {f : Af.Newform k} {r r' : G ℚ Ω →* GL (Fin 2) (Qbar l)} (h : Af.RepIso r r') (H : f.Att ι r) : f.Att ι r' := by
  obtain ⟨g, hg⟩ := h
  refine ⟨ss_conj g hg H.1, H.2.mono fun w hw A hA => ⟨fun s hs => ?_, fun σ hσ => ?_⟩⟩
  · rw [hg, (hw A hA).1 s hs, mul_one, mul_inv_cancel]
  · rw [← (hw A hA).2 σ hσ, hg, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

private def dg {R : Type} [CommRing R] (t : Rˣ) : GL (Fin 2) R where
  val := Matrix.diagonal ![(t : R), ((t⁻¹ : Rˣ) : R)]
  inv := Matrix.diagonal ![((t⁻¹ : Rˣ) : R), (t : R)]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; fin_cases i <;> simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; fin_cases i <;> simp

/- English proof (translation)
Use extensionality with `a b`. Use `show _ = (Matrix.diagonal ![(t : R), ((t⁻¹ : Rˣ) : R)] * corner (r g).mat * Matrix.diagonal ![((t⁻¹ : Rˣ) : R), (t : R)] : Matrix (Fin 2) (Fin 2) R) a b`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul, corner, corner, Matrix.submatrix_apply, Matrix.submatrix_apply, (conjBy_tor r t).1, wt, zpow_sub, Units.val_mul, mul_right_comm]`. Use `congr 1`. Apply the tactic sequence `congr 1 fin_cases a <;> simp [wt1]`.

Apply the tactic sequence `fin_cases b <;> simp [wt1]`.
-/
private theorem corner_conj {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) (t : Rˣ) (g : G) :
    corner (conjBy (tor R t) r g).mat =
      (dg t : Matrix (Fin 2) (Fin 2) R) * corner (r g).mat * (((dg t)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) := by
  ext a b
  show _ = (Matrix.diagonal ![(t : R), ((t⁻¹ : Rˣ) : R)] * corner (r g).mat *
    Matrix.diagonal ![((t⁻¹ : Rˣ) : R), (t : R)] : Matrix (Fin 2) (Fin 2) R) a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, corner, corner, Matrix.submatrix_apply, Matrix.submatrix_apply,
    (conjBy_tor r t).1, wt, zpow_sub, Units.val_mul, mul_right_comm]
  congr 1
  · congr 1
    fin_cases a <;> simp [wt1]
  · fin_cases b <;> simp [wt1]

/- English proof (translation)
Introduce `hL H Ω _ _ _ K _ _ _ _ l _ c N _ e ψ D _ ι`. Take `⟨B, hB, -, -, -, hmem, -⟩` from `dat_loc D`. Take `⟨g₁, hM, hfin, h3, h2⟩` from `H Ω K l c N e ψ D ι B hB`. Establish `hA : FinA D g₁` using `finA_of_end hL D g₁ hM B hmem hfin`. Use `⟨g₁, hM, hA, fun U S ξ r hr hp hI => ?_, fun U S ξ r hp hII h11 W hW => ?_⟩` and prove the remaining obligations.

Take `⟨A, _, _, t, r', ho, ht⟩` from `exists_ordPt_of_point hL D g₁ hM U S hA B hmem ξ r hp`. Establish `hl : ∀ s ∈ D.η.ker, (UnitaryThreeInertia.push A.val r' s).left = tor _ t * (r s).left * (tor _ t)⁻¹` using `fun s hs => by`. Rewrite using `[ht, conj_left r _ _ ((hr s).trans hs)]`. Establish `hI' : TypeI D.η (UnitaryThreeInertia.push A.val r')` using `matIrr_conj (tor _ t) (fun s hs => by`. Rewrite using `[mats, mats, GG.mat, GG.mat, hl s hs, ← Units.val_mul, ← Units.val_mul]`.

Use `congr 1`. Use the proof step `group) hI`. Establish `hm : HasMult D.η (UnitaryThreeInertia.push A.val r')` using `ho.red.mult`. Establish `hiso : Af.RepIso (D.rhoK r hr) (D.rhoK _ hm)` using `⟨tor _ t, fun s => hl _ (D.η_ker.ge (Base.galEmb_mem ℚ K Ω s))⟩`. Establish `key` using `h3 A r' ho (matIrr_open_gd D g₁ hM B hB A r' ho hI') (D.rhoK _ hm) fun s => rfl`.

Conclude with `autCsd_iso (tw_iso _ hiso.symm') key`. Take `⟨A, _, _, t, r', ho, ht⟩` from `exists_ordPt_of_point hL D g₁ hM U S hA B hmem ξ r hp`. Set `W' : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l)` to `(MulAut.conj (dg t)).toMonoidHom.comp W`. Establish `hW' : ∀ s, W' s = dg t * W s * (dg t)⁻¹` using `fun s => rfl`. Establish `hII' : TypeII D.η (UnitaryThreeInertia.push A.val r')`.

Rewrite using `[ht]`. Use `⟨fun g hg a b hab => ?_, matIrr_conj (dg t) (fun s _ => ?_) hII.2⟩` and prove the remaining obligations. Rewrite using `[(conjBy_tor r t).1, hII.1 g hg a b hab, mul_zero]`. Rewrite using `[corner_conj]`. Simplify using `only [← Matrix.mul_assoc]`.

Rewrite using `[Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]`. Take `⟨f, hf⟩` from `h2 A r' ho hII' (fun g hg => by`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (UnitaryThreeInertia.push A.val r' g).mat 1 1 = 1`. Rewrite using `[ht, (conjBy_tor r t).1, h11 g hg]`.

Simplify using `[wt]) W' (fun g hg => by`. Rewrite using `[ht, corner_conj, hW', Units.val_mul, Units.val_mul, hW.1 g hg]) (by`. Rewrite using `[hW', Units.val_mul, Units.val_mul, Matrix.trace_units_conj, hW.2])`. Conclude with `⟨f, att_iso (tw_iso _ (Af.RepIso.symm' ⟨dg t, hW'⟩)) hf⟩`.
-/
theorem UpperTheory.V.Pr.automorphy_rank_three_of_endomorphisms :
    Loc.LocalPublishedTheorems → GdEnd → AutomorphyUnramifiedCoefficients := by
  intro hL H Ω _ _ _ K _ _ _ _ l _ c N _ e ψ D _ ι
  obtain ⟨B, hB, -, -, -, hmem, -⟩ := dat_loc D
  obtain ⟨g₁, hM, hfin, h3, h2⟩ := H Ω K l c N e ψ D ι B hB
  have hA : FinA D g₁ := finA_of_end hL D g₁ hM B hmem hfin
  refine ⟨g₁, hM, hA, fun U S ξ r hr hp hI => ?_, fun U S ξ r hp hII h11 W hW => ?_⟩
  · obtain ⟨A, _, _, t, r', ho, ht⟩ := exists_ordPt_of_point hL D g₁ hM U S hA B hmem ξ r hp
    have hl : ∀ s ∈ D.η.ker, (UnitaryThreeInertia.push A.val r' s).left = tor _ t * (r s).left * (tor _ t)⁻¹ := fun s hs => by
      rw [ht, conj_left r _ _ ((hr s).trans hs)]
    have hI' : TypeI D.η (UnitaryThreeInertia.push A.val r') := matIrr_conj (tor _ t) (fun s hs => by
      rw [mats, mats, GG.mat, GG.mat, hl s hs, ← Units.val_mul, ← Units.val_mul]
      congr 1
      group) hI
    have hm : HasMult D.η (UnitaryThreeInertia.push A.val r') := ho.red.mult
    have hiso : Af.RepIso (D.rhoK r hr) (D.rhoK _ hm) :=
      ⟨tor _ t, fun s => hl _ (D.η_ker.ge (Base.galEmb_mem ℚ K Ω s))⟩
    have key := h3 A r' ho (matIrr_open_gd D g₁ hM B hB A r' ho hI') (D.rhoK _ hm) fun s => rfl
    exact autCsd_iso (tw_iso _ hiso.symm') key
  · obtain ⟨A, _, _, t, r', ho, ht⟩ := exists_ordPt_of_point hL D g₁ hM U S hA B hmem ξ r hp
    let W' : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l) := (MulAut.conj (dg t)).toMonoidHom.comp W
    have hW' : ∀ s, W' s = dg t * W s * (dg t)⁻¹ := fun s => rfl
    have hII' : TypeII D.η (UnitaryThreeInertia.push A.val r') := by
      rw [ht]
      refine ⟨fun g hg a b hab => ?_, matIrr_conj (dg t) (fun s _ => ?_) hII.2⟩
      · rw [(conjBy_tor r t).1, hII.1 g hg a b hab, mul_zero]
      · rw [corner_conj]
        simp only [← Matrix.mul_assoc]
        rw [Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    obtain ⟨f, hf⟩ := h2 A r' ho hII' (fun g hg => by
      apply Subtype.ext
      show (UnitaryThreeInertia.push A.val r' g).mat 1 1 = 1
      rw [ht, (conjBy_tor r t).1, h11 g hg]
      simp [wt]) W' (fun g hg => by
      rw [ht, corner_conj, hW', Units.val_mul, Units.val_mul, hW.1 g hg]) (by
      rw [hW', Units.val_mul, Units.val_mul, Matrix.trace_units_conj, hW.2])
    exact ⟨f, att_iso (tw_iso _ (Af.RepIso.symm' ⟨dg t, hW'⟩)) hf⟩
