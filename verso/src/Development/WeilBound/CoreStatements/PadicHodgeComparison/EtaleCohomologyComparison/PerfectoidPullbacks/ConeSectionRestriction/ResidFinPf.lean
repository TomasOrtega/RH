import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.RaTpowSinglePow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.Pb

variable {K : Type} [Field K] {R : Type} [CommRing R] [IsDomain R] [Algebra K R] {n : ℕ}

/- English proof (translation)
Establish `h : algebraMap R (FractionRing R) (tpow t m) = (((Units.map (algebraMap R (FractionRing R)).toMonoidHom) (∏ k, t k ^ m k) : (FractionRing R)ˣ) : FractionRing R)` using `rfl`. Rewrite using `[h, map_prod, Units.coe_prod]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_zpow, Units.val_zpow_eq_zpow_val]`. Both sides reduce to the same expression.
-/
theorem fldF_findim_pf_tpow (t : Fin (n + 1) → Rˣ) (m : Fin (n + 1) → ℤ) :
    algebraMap R (FractionRing R) (tpow t m) = ∏ k, (algebraMap R (FractionRing R) (t k : R)) ^ (m k) := by
  have h : algebraMap R (FractionRing R) (tpow t m) =
      (((Units.map (algebraMap R (FractionRing R)).toMonoidHom) (∏ k, t k ^ m k) : (FractionRing R)ˣ) :
        FractionRing R) := rfl
  rw [h, map_prod, Units.coe_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow, Units.val_zpow_eq_zpow_val]
  rfl

/- English proof (translation)
Introduce `r hr`. Establish `hle : torusS K t Finset.univ ≤ (fldF K t).toSubalgebra.comap (IsScalarTower.toAlgHom K R (FractionRing R))`. Unfold `torusS`. Rewrite using `[Algebra.adjoin_le_iff]`. Introduce and unpack `_ ⟨m, -, rfl⟩`.

Rewrite using `[SetLike.mem_coe, Subalgebra.mem_comap, IsScalarTower.coe_toAlgHom', IntermediateField.mem_toSubalgebra, fldF_findim_pf_tpow]`. Conclude with `prod_mem fun k _ => zpow_mem (IntermediateField.subset_adjoin K (Set.range fun k => algebraMap R (FractionRing R) (t k : R)) ⟨k, rfl⟩ : algebraMap R (FractionRing R) (t k : R) ∈ fldF K t) _`. Use `hle hr` as an intermediate fact. Rewrite `this` using `[Subalgebra.mem_comap, IsScalarTower.coe_toAlgHom', IntermediateField.mem_toSubalgebra]`. Then use the resulting hypothesis.
-/
theorem fldF_findim_pf_mem (t : Fin (n + 1) → Rˣ) :
    ∀ r ∈ torusS K t Finset.univ, algebraMap R (FractionRing R) r ∈ fldF K t := by
  intro r hr
  have hle : torusS K t Finset.univ ≤
      (fldF K t).toSubalgebra.comap (IsScalarTower.toAlgHom K R (FractionRing R)) := by
    unfold torusS
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨m, -, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_comap, IsScalarTower.coe_toAlgHom', IntermediateField.mem_toSubalgebra,
      fldF_findim_pf_tpow]
    exact prod_mem fun k _ => zpow_mem
      (IntermediateField.subset_adjoin K (Set.range fun k => algebraMap R (FractionRing R) (t k : R)) ⟨k, rfl⟩ :
        algebraMap R (FractionRing R) (t k : R) ∈ fldF K t) _
  have := hle hr
  rwa [Subalgebra.mem_comap, IsScalarTower.coe_toAlgHom', IntermediateField.mem_toSubalgebra] at this

/- English proof (translation)
Take `⟨s, hs⟩` from `hFG`. Set `ψ : torusS K t Finset.univ →+* fldF K t` to `((algebraMap R (FractionRing R)).comp (torusS K t Finset.univ).val.toRingHom).codRestrict (fldF K t) (fun x => fldF_findim_pf_mem t x x.2)`. Establish `hcomp : (algebraMap (fldF K t) (FractionRing R)).comp ψ = (algebraMap R (FractionRing R)).comp (algebraMap (torusS K t Finset.univ) R)`. Use extensionality with `x`. Both sides reduce to the same expression.

Establish `hint : ∀ x ∈ (s : Set R), IsIntegral (fldF K t) (algebraMap R (FractionRing R) x)` using `fun x hx => IsIntegral.map_of_comp_eq ψ (algebraMap R (FractionRing R)) hcomp (hInt x (hs ▸ Algebra.subset_adjoin hx))`. Set `E` to `IntermediateField.adjoin (fldF K t) (algebraMap R (FractionRing R) '' (s : Set R))`. Establish `: Finite (algebraMap R (FractionRing R) '' (s : Set R))` using `(s.finite_toSet.image _).to_subtype`. Establish `hE : FiniteDimensional (fldF K t) E` using `IntermediateField.finiteDimensional_adjoin (by`. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Conclude with `hint x hx)`. Establish `hBu : Bu ≤ ((E.restrictScalars K).toSubalgebra).comap (IsScalarTower.toAlgHom K R (FractionRing R))`. Rewrite using `[← hs, Algebra.adjoin_le_iff]`. Introduce `x hx`. Rewrite using `[SetLike.mem_coe, Subalgebra.mem_comap, IsScalarTower.coe_toAlgHom', IntermediateField.mem_toSubalgebra, IntermediateField.mem_restrictScalars]`.

Conclude with `IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩`. Establish `hmemB : ∀ b ∈ Bu, algebraMap R (FractionRing R) b ∈ E` using `fun b hb => by`. Use `hBu hb` as an intermediate fact. Rewrite `this` using `[Subalgebra.mem_comap, IsScalarTower.coe_toAlgHom', IntermediateField.mem_toSubalgebra, IntermediateField.mem_restrictScalars]`. Then use the resulting hypothesis. Establish `hmemR : ∀ r : R, algebraMap R (FractionRing R) r ∈ E` using `fun r => by`.

Take `⟨b, hb, b', hb', hb0, hrb⟩` from `hFrac r`. Establish `hne : algebraMap R (FractionRing R) b' ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr hb0`. Establish `heq : algebraMap R (FractionRing R) r = algebraMap R (FractionRing R) b / algebraMap R (FractionRing R) b'` using `eq_div_of_mul_eq hne (by rw [← map_mul, hrb])`. Rewrite using `[heq]`. Conclude with `div_mem (hmemB b hb) (hmemB b' hb')`.

Establish `htop : E = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `y _`. Take `⟨r, r', -, rfl⟩` from `IsFractionRing.div_surjective (A := R) y`. Conclude with `div_mem (hmemR r) (hmemR r')`.

Establish `e : E ≃ₗ[fldF K t] FractionRing R` using `((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv).toLinearEquiv`. Conclude with `e.finiteDimensional`.
-/
theorem fldF_findim_pf (t : Fin (n + 1) → Rˣ) (Bu : Subalgebra K R) (hTB : torusS K t Finset.univ ≤ Bu) (hFG : Bu.FG)
    (hInt : ∀ b ∈ Bu, IsIntegral (torusS K t Finset.univ) b)
    (hFrac : ∀ r : R, ∃ b ∈ Bu, ∃ b' ∈ Bu, b' ≠ 0 ∧ r * b' = b) :
    FiniteDimensional (fldF K t) (FractionRing R) := by
  classical
  obtain ⟨s, hs⟩ := hFG

  let ψ : torusS K t Finset.univ →+* fldF K t :=
    ((algebraMap R (FractionRing R)).comp (torusS K t Finset.univ).val.toRingHom).codRestrict (fldF K t)
      (fun x => fldF_findim_pf_mem t x x.2)
  have hcomp : (algebraMap (fldF K t) (FractionRing R)).comp ψ =
      (algebraMap R (FractionRing R)).comp (algebraMap (torusS K t Finset.univ) R) := by
    ext x
    rfl

  have hint : ∀ x ∈ (s : Set R), IsIntegral (fldF K t) (algebraMap R (FractionRing R) x) := fun x hx =>
    IsIntegral.map_of_comp_eq ψ (algebraMap R (FractionRing R)) hcomp
      (hInt x (hs ▸ Algebra.subset_adjoin hx))
  let E := IntermediateField.adjoin (fldF K t) (algebraMap R (FractionRing R) '' (s : Set R))
  have : Finite (algebraMap R (FractionRing R) '' (s : Set R)) := (s.finite_toSet.image _).to_subtype
  have hE : FiniteDimensional (fldF K t) E := IntermediateField.finiteDimensional_adjoin (by
    rintro _ ⟨x, hx, rfl⟩
    exact hint x hx)

  have hBu : Bu ≤ ((E.restrictScalars K).toSubalgebra).comap (IsScalarTower.toAlgHom K R (FractionRing R)) := by
    rw [← hs, Algebra.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, Subalgebra.mem_comap, IsScalarTower.coe_toAlgHom', IntermediateField.mem_toSubalgebra,
      IntermediateField.mem_restrictScalars]
    exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
  have hmemB : ∀ b ∈ Bu, algebraMap R (FractionRing R) b ∈ E := fun b hb => by
    have := hBu hb
    rwa [Subalgebra.mem_comap, IsScalarTower.coe_toAlgHom', IntermediateField.mem_toSubalgebra,
      IntermediateField.mem_restrictScalars] at this

  have hmemR : ∀ r : R, algebraMap R (FractionRing R) r ∈ E := fun r => by
    obtain ⟨b, hb, b', hb', hb0, hrb⟩ := hFrac r
    have hne : algebraMap R (FractionRing R) b' ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr hb0
    have heq : algebraMap R (FractionRing R) r = algebraMap R (FractionRing R) b / algebraMap R (FractionRing R) b' :=
      eq_div_of_mul_eq hne (by rw [← map_mul, hrb])
    rw [heq]
    exact div_mem (hmemB b hb) (hmemB b' hb')
  have htop : E = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨r, r', -, rfl⟩ := IsFractionRing.div_surjective (A := R) y
    exact div_mem (hmemR r) (hmemR r')
  have e : E ≃ₗ[fldF K t] FractionRing R :=
    ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv).toLinearEquiv
  exact e.finiteDimensional

end CrystallineSemistableComparison.Pb
