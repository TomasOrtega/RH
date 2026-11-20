import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.UnitaryThreeTestFunctionHeckeRelations
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.LocalLevelOutsideSigma
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.IsIntegralLf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.FactJ

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Local

open Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use `ext`. Simplify using `[dg, val_diagT, Matrix.det_diagonal, Fin.prod_univ_two]`.
-/
private theorem det_dg (d : Fin 2 → kˣ) : GeneralLinearGroup.det (dg d) = d 0 * d 1 := by
  ext
  simp [dg, val_diagT, Matrix.det_diagonal, Fin.prod_univ_two]

/- English proof (translation)
Take `⟨a, ha, s, hs, b, hb, rfl⟩` from `(factJ k V 2).1 g hg`. Take `⟨t, ht, rfl⟩` from `Subgroup.mem_map.1 hs`. Establish `hau : a ∈ unipB k (Fin 2)` using `(glIwa k 2).N_le ha`. Establish `hb0 : b ∈ Subgroup.comap (GlobalTheory.CuspRep.invT 2 k) (unipB k (Fin 2)) ⊓ Kc k 2 (V.c + 1)` using `hb`. Establish `hbl` using `GlAx.mem_low.1 (Subgroup.mem_inf.1 hb0).1`.

Establish `hal` using `(mem_unipB k).1 hau`. Establish `da : GeneralLinearGroup.det a = 1`. Use `ext`. Simplify using `only [GeneralLinearGroup.val_det_apply, Units.val_one]`. Rewrite using `[Matrix.det_of_upperTriangular (fun i j hij => hal.1 i j hij)]`.

Simplify using `[hal.2]`. Establish `db : GeneralLinearGroup.det b = 1`. Use `ext`. Simplify using `only [GeneralLinearGroup.val_det_apply, Units.val_one]`. Rewrite using `[Matrix.det_of_lowerTriangular _ (fun i j hij => hbl.1 i j hij)]`.

Simplify using `[hbl.2]`. Rewrite using `[map_mul, map_mul, da, db, one_mul, mul_one]`. Establish `ht' : ∀ i, t i ∈ V.H` using `fun i => ht i (Set.mem_univ i)`. Rewrite using `[show diagT k (Fin 2) t = dg t from rfl, det_dg]`. Conclude with `V.H.mul_mem (ht' 0) (ht' 1)`.
-/
private theorem det_mem (V : Lev k) (g : GL (Fin 2) k) (hg : g ∈ V.J 2) : GeneralLinearGroup.det g ∈ V.H := by
  obtain ⟨a, ha, s, hs, b, hb, rfl⟩ := (factJ k V 2).1 g hg
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hs
  have hau : a ∈ unipB k (Fin 2) := (glIwa k 2).N_le ha
  have hb0 : b ∈ Subgroup.comap (GlobalTheory.CuspRep.invT 2 k) (unipB k (Fin 2)) ⊓ Kc k 2 (V.c + 1) := hb
  have hbl := GlAx.mem_low.1 (Subgroup.mem_inf.1 hb0).1
  have hal := (mem_unipB k).1 hau
  have da : GeneralLinearGroup.det a = 1 := by
    ext
    simp only [GeneralLinearGroup.val_det_apply, Units.val_one]
    rw [Matrix.det_of_upperTriangular (fun i j hij => hal.1 i j hij)]
    simp [hal.2]
  have db : GeneralLinearGroup.det b = 1 := by
    ext
    simp only [GeneralLinearGroup.val_det_apply, Units.val_one]
    rw [Matrix.det_of_lowerTriangular _ (fun i j hij => hbl.1 i j hij)]
    simp [hbl.2]
  rw [map_mul, map_mul, da, db, one_mul, mul_one]
  have ht' : ∀ i, t i ∈ V.H := fun i => ht i (Set.mem_univ i)
  rw [show diagT k (Fin 2) t = dg t from rfl, det_dg]
  exact V.H.mul_mem (ht' 0) (ht' 1)

/- English proof (translation)
Take `⟨hbij, -, -, -, hdet, -⟩` from `eD_facts k O hO h2 Δ s hs hs0`. Take `⟨c, hc⟩` from `hbij.2 (dg ![GeneralLinearGroup.det (eD hs u), 1])`. Establish `hxH : GeneralLinearGroup.det (eD hs u) ∈ V.H` using `det_mem V _ hu`. Establish `hcJ : eD hs c ∈ V.J 2`. Rewrite using `[hc]`.

Apply `V.dg_mem` to reduce the goal to its premises. Introduce `i`. Use `fin_cases i`. Simplify using `using hxH`. Simplify using `using V.H.one_mem`.

Establish `hdet1 : ∀ w : DX Δ, GeneralLinearGroup.det (eD hs w) = 1 → w ∈ SU Δ`. Introduce `w hw`. Use `show GeneralLinearGroup.det ((DX Δ).subtype w) = 1`. Apply `Units.ext` to reduce the goal to its premises. Establish `h0` using `(hdet w).1`.

Simplify using `only [GeneralLinearGroup.val_det_apply, Units.val_one, Subgroup.coe_subtype]`. Rewrite using `[h0, ← GeneralLinearGroup.val_det_apply, hw]`. Simplify using the standard rewrite rules. Establish `hec : GeneralLinearGroup.det (eD hs c) = GeneralLinearGroup.det (eD hs u)`. Rewrite using `[hc, det_dg]`.

Simplify using the standard rewrite rules. Use `⟨c, hcJ, hdet1 _ ?_, hdet1 _ ?_, _, hc⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_inv, map_mul, map_inv, hec, mul_inv_cancel]`. Rewrite using `[map_mul, map_inv, map_mul, map_inv, hec, inv_mul_cancel]`.
-/
private theorem loc {O : Type} [CommRing O] [Algebra O k] (hO : IsInts k O) (h2 : (2 : k) ≠ 0) {Δ s : k} (hs : s * s = Δ)
    (hs0 : s ≠ 0) (V : Lev k) (u : DX Δ) (hu : eD hs u ∈ V.J 2) :
    ∃ c : DX Δ, eD hs c ∈ V.J 2 ∧ u * c⁻¹ ∈ SU Δ ∧ c⁻¹ * u ∈ SU Δ ∧ ∃ x : kˣ, eD hs c = dg ![x, 1] := by
  obtain ⟨hbij, -, -, -, hdet, -⟩ := eD_facts k O hO h2 Δ s hs hs0
  obtain ⟨c, hc⟩ := hbij.2 (dg ![GeneralLinearGroup.det (eD hs u), 1])
  have hxH : GeneralLinearGroup.det (eD hs u) ∈ V.H := det_mem V _ hu
  have hcJ : eD hs c ∈ V.J 2 := by
    rw [hc]
    apply V.dg_mem
    intro i
    fin_cases i
    · simpa using hxH
    · simpa using V.H.one_mem
  have hdet1 : ∀ w : DX Δ, GeneralLinearGroup.det (eD hs w) = 1 → w ∈ SU Δ := by
    intro w hw
    show GeneralLinearGroup.det ((DX Δ).subtype w) = 1
    apply Units.ext
    have h0 := (hdet w).1
    simp only [GeneralLinearGroup.val_det_apply, Units.val_one, Subgroup.coe_subtype]
    rw [h0, ← GeneralLinearGroup.val_det_apply, hw]
    simp
  have hec : GeneralLinearGroup.det (eD hs c) = GeneralLinearGroup.det (eD hs u) := by
    rw [hc, det_dg]
    simp
  refine ⟨c, hcJ, hdet1 _ ?_, hdet1 _ ?_, _, hc⟩
  · rw [map_mul, map_inv, map_mul, map_inv, hec, mul_inv_cancel]
  · rw [map_mul, map_inv, map_mul, map_inv, hec, inv_mul_cancel]

end Local

/- English proof (translation)
Introduce `F _ _ Δ A hA u hu`. Take `⟨-, -, hloc, -, hU2⟩` from `datOk F Δ A hA`. Take `⟨huJ, huK⟩` from `(hU2 u).1 hu`. Establish `hex : ∀ v (h : v ∈ A.Sg), ∃ c : DX ((cv v) Δ), eD (A.hs v h) c ∈ (A.V v).J 2 ∧ u.1 v * c⁻¹ ∈ SU ((cv v) Δ) ∧ c⁻¹ * u.1 v ∈ SU ((cv v) Δ) ∧ ∃ x : (Kv v)ˣ, eD (A.hs v h) c = dg ![x, 1]`. Introduce `v h`.

Take `⟨hO, h2, hs0, -, -⟩` from `hloc v h`. Conclude with `loc hO h2 (A.hs v h) hs0 (A.V v) _ (huJ v h)`. Set `cf : (v : Pl F) → DX ((cv v) Δ)` to `fun v => if h : v ∈ A.Sg then Classical.choose (hex v h) else u.1 v`. Establish `cf_in : ∀ v (h : v ∈ A.Sg), cf v = Classical.choose (hex v h)` using `fun v h => dif_pos h`. Establish `cf_out : ∀ v, v ∉ A.Sg → cf v = u.1 v` using `fun v h => dif_neg h`.

Establish `hcRP : cf ∈ RP (fun v => DX ((cv v) Δ)) (fun v => KD ((cv v) Δ) (Ov v))` using `by show ∀ᶠ v in Filter.cofinite, cf v ∈ KD ((cv v) Δ) (Ov v)`. Rewrite using `[Filter.eventually_cofinite]`. Use `A.Sg.finite_toSet.subset (fun v hv => ?_)` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Conclude with `hv (by rw [cf_out v h]; exact huK v h)`.

Set `c : DA Δ` to `⟨cf, hcRP⟩`. Establish `hSA : ∀ w : DA Δ, (∀ v, w.1 v ∈ SU ((cv v) Δ)) → w ∈ SA Δ`. Introduce `w hw`. Conclude with `Subgroup.mem_iInf.2 (fun v => hw v)`. Use `⟨c, (hU2 c).2 ⟨fun v h => ?_, fun v h => ?_⟩, hSA _ (fun v => ?_), hSA _ (fun v => ?_), fun g d hgd => ?_⟩` and prove the remaining obligations.

Use `show eD _ (cf v) ∈ _`. Rewrite using `[cf_in v h]`. Conclude with `(Classical.choose_spec (hex v h)).1`. Use `show cf v ∈ _`. Rewrite using `[cf_out v h]`.

Conclude with `huK v h`. Use `show u.1 v * (cf v)⁻¹ ∈ SU ((cv v) Δ)`. Distinguish the cases in `h : v ∈ A.Sg`. Rewrite using `[cf_in v h]`. Conclude with `(Classical.choose_spec (hex v h)).2.1`.

Rewrite using `[cf_out v h, mul_inv_cancel]`. Conclude with `one_mem _`. Use `show (cf v)⁻¹ * u.1 v ∈ SU ((cv v) Δ)`. Distinguish the cases in `h : v ∈ A.Sg`. Rewrite using `[cf_in v h]`.

Conclude with `(Classical.choose_spec (hex v h)).2.2.1`. Rewrite using `[cf_out v h, inv_mul_cancel]`. Conclude with `one_mem _`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `v`.

Use `show cf v * g.1 v = g.1 v * cf v`. Distinguish the cases in `h : v ∈ A.Sg`. Rewrite using `[cf_in v h]`. Take `⟨hO, h2, hs0, -, -⟩` from `hloc v h`. Establish `hinj` using `(eD_facts (Kv v) (Ov v) hO h2 _ _ (A.hs v h) hs0).1.1`.

Take `⟨-, -, -, x, hx⟩` from `Classical.choose_spec (hex v h)`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, hx, hgd.1 v h]`. Use `show diagT _ (Fin 2) ![x, 1] * diagT _ (Fin 2) (d v) = diagT _ (Fin 2) (d v) * diagT _ (Fin 2) ![x, 1]`. Rewrite using `[← map_mul, ← map_mul, mul_comm]`.

Rewrite using `[hgd.2 v h, mul_one, one_mul]`.
-/
theorem UpperTheory.V.Z.Sym.So.torPart :
    UpperTheory.V.Z.Sym.So.TorPart := by
  classical
  intro F _ _ Δ A hA u hu
  obtain ⟨-, -, hloc, -, hU2⟩ := datOk F Δ A hA
  obtain ⟨huJ, huK⟩ := (hU2 u).1 hu
  have hex : ∀ v (h : v ∈ A.Sg), ∃ c : DX ((cv v) Δ), eD (A.hs v h) c ∈ (A.V v).J 2 ∧
      u.1 v * c⁻¹ ∈ SU ((cv v) Δ) ∧ c⁻¹ * u.1 v ∈ SU ((cv v) Δ) ∧
      ∃ x : (Kv v)ˣ, eD (A.hs v h) c = dg ![x, 1] := by
    intro v h
    obtain ⟨hO, h2, hs0, -, -⟩ := hloc v h
    exact loc hO h2 (A.hs v h) hs0 (A.V v) _ (huJ v h)
  let cf : (v : Pl F) → DX ((cv v) Δ) := fun v =>
    if h : v ∈ A.Sg then Classical.choose (hex v h) else u.1 v
  have cf_in : ∀ v (h : v ∈ A.Sg), cf v = Classical.choose (hex v h) := fun v h => dif_pos h
  have cf_out : ∀ v, v ∉ A.Sg → cf v = u.1 v := fun v h => dif_neg h
  have hcRP : cf ∈ RP (fun v => DX ((cv v) Δ)) (fun v => KD ((cv v) Δ) (Ov v)) := by
    show ∀ᶠ v in Filter.cofinite, cf v ∈ KD ((cv v) Δ) (Ov v)
    rw [Filter.eventually_cofinite]
    refine A.Sg.finite_toSet.subset (fun v hv => ?_)
    by_contra h
    exact hv (by rw [cf_out v h]; exact huK v h)
  let c : DA Δ := ⟨cf, hcRP⟩
  have hSA : ∀ w : DA Δ, (∀ v, w.1 v ∈ SU ((cv v) Δ)) → w ∈ SA Δ := by
    intro w hw
    exact Subgroup.mem_iInf.2 (fun v => hw v)
  refine ⟨c, (hU2 c).2 ⟨fun v h => ?_, fun v h => ?_⟩, hSA _ (fun v => ?_), hSA _ (fun v => ?_),
    fun g d hgd => ?_⟩
  · show eD _ (cf v) ∈ _
    rw [cf_in v h]
    exact (Classical.choose_spec (hex v h)).1
  · show cf v ∈ _
    rw [cf_out v h]
    exact huK v h
  · show u.1 v * (cf v)⁻¹ ∈ SU ((cv v) Δ)
    by_cases h : v ∈ A.Sg
    · rw [cf_in v h]
      exact (Classical.choose_spec (hex v h)).2.1
    · rw [cf_out v h, mul_inv_cancel]
      exact one_mem _
  · show (cf v)⁻¹ * u.1 v ∈ SU ((cv v) Δ)
    by_cases h : v ∈ A.Sg
    · rw [cf_in v h]
      exact (Classical.choose_spec (hex v h)).2.2.1
    · rw [cf_out v h, inv_mul_cancel]
      exact one_mem _
  · apply Subtype.ext
    funext v
    show cf v * g.1 v = g.1 v * cf v
    by_cases h : v ∈ A.Sg
    · rw [cf_in v h]
      obtain ⟨hO, h2, hs0, -, -⟩ := hloc v h
      have hinj := (eD_facts (Kv v) (Ov v) hO h2 _ _ (A.hs v h) hs0).1.1
      obtain ⟨-, -, -, x, hx⟩ := Classical.choose_spec (hex v h)
      apply hinj
      rw [map_mul, map_mul, hx, hgd.1 v h]
      show diagT _ (Fin 2) ![x, 1] * diagT _ (Fin 2) (d v) = diagT _ (Fin 2) (d v) * diagT _ (Fin 2) ![x, 1]
      rw [← map_mul, ← map_mul, mul_comm]
    · rw [hgd.2 v h, mul_one, one_mul]

end
