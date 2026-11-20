import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.NotIsTemperedGLDetRepTwo
import GroundTheory.AutomorphicForms.TensorProductTheorem.CuspidalRep

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

section

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Introduce and unpack `o _ ⟨φ, hφ, rfl⟩`. Conclude with `⟨_, add_mem (U.smul_mem _ (h o φ hφ)) (U.smul_mem _ hφ), (act_mulChi χ o φ).symm⟩`.
-/
private theorem stable_twist (χ : HChar E) {U : Submodule ℂ (Sm E a)} (h : IsStable U) :
    IsStable (U.map (mulChi a χ).toLinearMap) := by
  rintro o _ ⟨φ, hφ, rfl⟩
  exact ⟨_, add_mem (U.smul_mem _ (h o φ hφ)) (U.smul_mem _ hφ), (act_mulChi χ o φ).symm⟩

/- English proof (translation)
Rewrite using `[← Submodule.map_comp]`. Establish `: (mulChi a χ⁻¹).toLinearMap ∘ₗ (mulChi a χ).toLinearMap = LinearMap.id` using `LinearMap.ext fun φ => by`. Express the relevant statement in the definitionally equal form `mulChi a χ⁻¹ (mulChi a χ φ) = φ`. Rewrite using `[← mulChi_mul, mul_inv_cancel, mulChi_one]`. Rewrite using `[this, Submodule.map_id]`.
-/
private theorem map_twist_inv (χ : HChar E) (U : Submodule ℂ (Sm E a)) :
    (U.map (mulChi a χ).toLinearMap).map (mulChi a χ⁻¹).toLinearMap = U := by
  rw [← Submodule.map_comp]
  have : (mulChi a χ⁻¹).toLinearMap ∘ₗ (mulChi a χ).toLinearMap = LinearMap.id := LinearMap.ext fun φ => by
    change mulChi a χ⁻¹ (mulChi a χ φ) = φ
    rw [← mulChi_mul, mul_inv_cancel, mulChi_one]
  rw [this, Submodule.map_id]

/- English proof (translation)
Establish `hn : (Fintype.card (InfinitePlace E) : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`. Establish `ha' : (a : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`. Use `⟨Model.absC E (-c / (a * (2 * Fintype.card (InfinitePlace E)))), ?_⟩` and prove the remaining obligations. Establish `e : (Matrix.of (oneL E a)).trace = a • (1 : Cinf E)`. Express the relevant statement in the definitionally equal form `Matrix.trace (1 : Matrix (Fin a) (Fin a) (Cinf E)) = _`.

Simplify using the standard rewrite rules. Rewrite using `[e, map_nsmul, GlobalTheory.GKCoh.Tests.dchi_absC_one, nsmul_eq_mul]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
private theorem exists_twist (ha : 1 ≤ a) (c : ℂ) :
    ∃ χ : HChar E, dchi χ (Matrix.of (oneL E a)).trace = -c := by
  have hn : (Fintype.card (InfinitePlace E) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have ha' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  refine ⟨Model.absC E (-c / (a * (2 * Fintype.card (InfinitePlace E)))), ?_⟩
  have e : (Matrix.of (oneL E a)).trace = a • (1 : Cinf E) := by
    change Matrix.trace (1 : Matrix (Fin a) (Fin a) (Cinf E)) = _
    simp
  rw [e, map_nsmul, GlobalTheory.GKCoh.Tests.dchi_absC_one, nsmul_eq_mul]
  push_cast
  field_simp

/- English proof (translation)
Establish `hr : C ≤ LinearMap.range (UpperTheory.V.Cm.ofCusp E a)` using `fun φ h => UpperTheory.V.Cm.mem_range_ofCusp.2 (hc φ h)`. Establish `hz : C.comap (UpperTheory.V.Cm.ofCusp E a) ≤ GroundTheory.Automorphic.AutomorphicForm.centralCuspForms E a` using `fun ψ h => UpperTheory.V.Cm.mem_centralCuspForms_of (h0 _ h)`. Establish `st` using `UpperTheory.V.Cm.stab_comap hsU`. Take `⟨D, -, d2, d3, d4, d5, d6⟩` from `GroundTheory.Automorphic.AutomorphicForm.exists_compl_centralCuspForms (U.comap (UpperTheory.V.Cm.ofCusp E a)) ((Submodule.comap_mono hU).trans hz) st.ρ st.σ st.τ`. Establish `hUe : (U.comap (UpperTheory.V.Cm.ofCusp E a)).map (UpperTheory.V.Cm.ofCusp E a) = U` using `Submodule.map_comap_eq_self (hU.trans hr)`.

Establish `hD : IsStable (D.map (UpperTheory.V.Cm.ofCusp E a))` using `UpperTheory.V.Cm.isStable_map ⟨d2, d3, d4⟩`. Use `⟨D.map (UpperTheory.V.Cm.ofCusp E a) ⊓ C, inf_le_right, fun o φ h => ⟨hD o φ h.1, hs o φ h.2⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← inf_assoc, ← hUe, ← Submodule.map_inf _ UpperTheory.V.Cm.ofCusp_injective, d5, Submodule.map_bot, bot_inf_eq]`. Rewrite using `[← sup_inf_assoc_of_le _ hU, inf_eq_right, ← hUe, ← Submodule.map_sup, d6]`. Conclude with `(Submodule.map_comap_eq_self hr).ge.trans (Submodule.map_mono hz)`.
-/
private theorem compl_zero {C : Submodule ℂ (Sm E a)} (hc : ∀ φ ∈ C, IsCuspForm φ)
    (h0 : ∀ φ ∈ C, lie E a (oneL E a) φ = 0) (hs : IsStable C) {U : Submodule ℂ (Sm E a)} (hU : U ≤ C)
    (hsU : IsStable U) : ∃ D ≤ C, IsStable D ∧ U ⊓ D = ⊥ ∧ U ⊔ D = C := by
  have hr : C ≤ LinearMap.range (UpperTheory.V.Cm.ofCusp E a) := fun φ h => UpperTheory.V.Cm.mem_range_ofCusp.2 (hc φ h)
  have hz : C.comap (UpperTheory.V.Cm.ofCusp E a) ≤ GroundTheory.Automorphic.AutomorphicForm.centralCuspForms E a :=
    fun ψ h => UpperTheory.V.Cm.mem_centralCuspForms_of (h0 _ h)
  have st := UpperTheory.V.Cm.stab_comap hsU
  obtain ⟨D, -, d2, d3, d4, d5, d6⟩ := GroundTheory.Automorphic.AutomorphicForm.exists_compl_centralCuspForms
    (U.comap (UpperTheory.V.Cm.ofCusp E a)) ((Submodule.comap_mono hU).trans hz) st.ρ st.σ st.τ
  have hUe : (U.comap (UpperTheory.V.Cm.ofCusp E a)).map (UpperTheory.V.Cm.ofCusp E a) = U :=
    Submodule.map_comap_eq_self (hU.trans hr)
  have hD : IsStable (D.map (UpperTheory.V.Cm.ofCusp E a)) := UpperTheory.V.Cm.isStable_map ⟨d2, d3, d4⟩
  refine ⟨D.map (UpperTheory.V.Cm.ofCusp E a) ⊓ C, inf_le_right, fun o φ h => ⟨hD o φ h.1, hs o φ h.2⟩, ?_, ?_⟩
  · rw [← inf_assoc, ← hUe, ← Submodule.map_inf _ UpperTheory.V.Cm.ofCusp_injective, d5, Submodule.map_bot, bot_inf_eq]
  · rw [← sup_inf_assoc_of_le _ hU, inf_eq_right, ← hUe, ← Submodule.map_sup, d6]
    exact (Submodule.map_comap_eq_self hr).ge.trans (Submodule.map_mono hz)

end

/- English proof (translation)
Introduce `hb E _ _ _ a ha m U hU hsU`. Take `⟨hs, c, hc⟩` from `hb E a m`. Take `⟨χ, hχ⟩` from `exists_twist (E := E) ha c`. Take `⟨D, d1, d2, d3, d4⟩` from `compl_zero (C := (CI a m).map (mulChi a χ).toLinearMap) (by rintro _ ⟨φ, h, rfl⟩; exact (mem_CI.1 h).1.mulChi χ) (by`. Introduce and unpack `_ ⟨φ, h, rfl⟩`.

Rewrite using `[LinearEquiv.coe_coe, lie_mulChi, hc φ h, hχ, neg_smul, add_neg_cancel, map_zero])`. Use the proof step `(stable_twist χ hs) (Submodule.map_mono hU) (stable_twist χ hsU)`. Use `⟨D.map (mulChi a χ⁻¹).toLinearMap, (Submodule.map_mono d1).trans (map_twist_inv χ _).le, stable_twist _ d2, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_twist_inv χ U, ← Submodule.map_inf _ (mulChi a χ⁻¹).injective, d3, Submodule.map_bot]`. Rewrite using `[← map_twist_inv χ U, ← Submodule.map_sup, d4, map_twist_inv]`.
-/
theorem UpperTheory.V.Cj.S.ciCompl :
    UpperTheory.V.Cj.S.CiBasic → UpperTheory.V.Cj.S.CiCompl := by
  intro hb E _ _ _ a ha m U hU hsU
  obtain ⟨hs, c, hc⟩ := hb E a m
  obtain ⟨χ, hχ⟩ := exists_twist (E := E) ha c
  obtain ⟨D, d1, d2, d3, d4⟩ := compl_zero (C := (CI a m).map (mulChi a χ).toLinearMap)
    (by rintro _ ⟨φ, h, rfl⟩; exact (mem_CI.1 h).1.mulChi χ)
    (by
      rintro _ ⟨φ, h, rfl⟩
      rw [LinearEquiv.coe_coe, lie_mulChi, hc φ h, hχ, neg_smul, add_neg_cancel, map_zero])
    (stable_twist χ hs) (Submodule.map_mono hU) (stable_twist χ hsU)
  refine ⟨D.map (mulChi a χ⁻¹).toLinearMap, (Submodule.map_mono d1).trans (map_twist_inv χ _).le,
    stable_twist _ d2, ?_, ?_⟩
  · rw [← map_twist_inv χ U, ← Submodule.map_inf _ (mulChi a χ⁻¹).injective, d3, Submodule.map_bot]
  · rw [← map_twist_inv χ U, ← Submodule.map_sup, d4, map_twist_inv]
