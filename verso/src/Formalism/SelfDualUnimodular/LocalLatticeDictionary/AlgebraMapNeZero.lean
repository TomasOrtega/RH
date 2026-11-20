import Mathlib
import Formalism.SelfDualUnimodular.LocalLatticeDictionary.UnimodOfSelfDual

noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.LatDictZ.Z0.BR

open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA PIW.AdelClassFin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hv`. Use `⟨g.symm v, (hm _).2 (by rw [LinearEquiv.apply_symm_apply]; exact hv), ?_⟩` and prove the remaining obligations. Rewrite using `[hγg, LinearEquiv.apply_symm_apply]`. Introduce and unpack `⟨w, hw, rfl⟩`.

Rewrite using `[hγg]`. Conclude with `(hm w).1 hw`.
-/
theorem loc_iff_of_isom (g : (Fin n → E) ≃ₗ[E] (Fin n → E))
    {L M : Submodule (𝓞 E) (Fin n → E)} {p : Ideal (𝓞 E)}
    (hm : ∀ x, x ∈ Formalism.HermitianLatticesTheory.loc (K := E) p L ↔ g x ∈ Formalism.HermitianLatticesTheory.loc (K := E) p M)
    (γ : GL (Fin n) E) (hγg : ∀ w, (γ : Matrix (Fin n) (Fin n) E) *ᵥ w = g w) (v : Fin n → E) :
    v ∈ Formalism.HermitianLatticesTheory.loc (K := E) p M ↔ ∃ w ∈ Formalism.HermitianLatticesTheory.loc (K := E) p L, (γ : Matrix (Fin n) (Fin n) E) *ᵥ w = v := by
  constructor
  · intro hv
    refine ⟨g.symm v, (hm _).2 (by rw [LinearEquiv.apply_symm_apply]; exact hv), ?_⟩
    rw [hγg, LinearEquiv.apply_symm_apply]
  · rintro ⟨w, hw, rfl⟩
    rw [hγg]; exact (hm w).1 hw

/- English proof (translation)
Introduce `E _ _ _ n J hK hJh hdet L M hLfg hMfg hLsp hMsp hLd hMd p hp`. Take `⟨g, hg, hm⟩` from `hG E (Fin n → E) (hJ J) hK (hJ_symm hJh) (hJ_nondeg hdet) p hp (Formalism.HermitianLatticesTheory.loc (K := E) p L).toAddSubgroup (Formalism.HermitianLatticesTheory.loc (K := E) p M).toAddSubgroup (selfDualMod_loc hJh hLfg hLsp hLd hp) (selfDualMod_loc hJh hMfg hMsp hMd hp)`. Take `⟨γ, hγ, hγg⟩` from `gl_of_isom g hg`. Conclude with `⟨γ, hγ, loc_iff_of_isom g hm γ hγg⟩`.
-/
theorem semiGenus_of (hG : SemiGenusLoc) : SemiGenus := by
  intro E _ _ _ n J hK hJh hdet L M hLfg hMfg hLsp hMsp hLd hMd p hp
  obtain ⟨g, hg, hm⟩ := hG E (Fin n → E) (hJ J) hK (hJ_symm hJh) (hJ_nondeg hdet) p hp
    (Formalism.HermitianLatticesTheory.loc (K := E) p L).toAddSubgroup (Formalism.HermitianLatticesTheory.loc (K := E) p M).toAddSubgroup
    (selfDualMod_loc hJh hLfg hLsp hLd hp) (selfDualMod_loc hJh hMfg hMsp hMd hp)
  obtain ⟨γ, hγ, hγg⟩ := gl_of_isom g hg
  exact ⟨γ, hγ, loc_iff_of_isom g hm γ hγg⟩

/- English proof (translation)
The claim follows from `algebraMap_ne_zero_of_mem_hcompl hp ht`.
-/
theorem algebraMap_ne_zero' {p : Ideal (𝓞 E)} (hp : p.IsPrime) {t : 𝓞 E}
    (ht : t ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) p) : algebraMap (𝓞 E) E t ≠ 0 :=
  algebraMap_ne_zero_of_mem_hcompl hp ht

/- English proof (translation)
Rewrite using `[algebraMap_smul]`.
-/
theorem smul_eq_alg (t : 𝓞 E) (v : Fin n → E) : t • v = (algebraMap (𝓞 E) E t) • v := by
  rw [algebraMap_smul]

/- English proof (translation)
Introduce `E _ _ _ n J hK hJh hdet r s z L M hLfg hMfg hLsp hMsp hLd hMd hsz hU hSL hSM hzL hzM hPL hPM p hp`. Establish `hpP` using `hp.isPrime`. Establish `hU' : ∀ w ∈ Submodule.span E (Set.range s), w ∈ (Formalism.HermitianLatticesTheory.loc (K` using `E) p L).toAddSubgroup ↔ w ∈ (Formalism.HermitianLatticesTheory.loc (K := E) p M).toAddSubgroup := by`. Introduce `w hw`. Express the relevant statement in the definitionally equal form `w ∈ Formalism.HermitianLatticesTheory.loc (K := E) p L ↔ w ∈ Formalism.HermitianLatticesTheory.loc (K := E) p M`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht, htw⟩`. Use `⟨t, ht, (hU _ ?_).1 htw⟩` and prove the remaining obligations. Rewrite using `[smul_eq_alg]`. Conclude with `Submodule.smul_mem _ _ hw`.

Introduce and unpack `⟨t, ht, htw⟩`. Use `⟨t, ht, (hU _ ?_).2 htw⟩` and prove the remaining obligations. Rewrite using `[smul_eq_alg]`. Conclude with `Submodule.smul_mem _ _ hw`. Establish `hsplit : ∀ N : Submodule (𝓞 E) (Fin n → E), (∀ w ∈ N, ∃ w₁ ∈ N, w₁ ∈ Submodule.span E (Set.range s) ∧ ∀ a, Formalism.UG.hform (starRingEnd E) J (s a) (w - w₁) = 0) → ∀ w ∈ (Formalism.HermitianLatticesTheory.loc (K` using `E) p N).toAddSubgroup, ∃ w₁ ∈ (Formalism.HermitianLatticesTheory.loc (K := E) p N).toAddSubgroup, w₁ ∈ Submodule.span E (Set.range s) ∧ ∀ a, hJ J (s a) (w - w₁) = 0 := by`.

Introduce `N hN w hw`. Take `⟨t, ht, htw⟩` from `hw`. Take `⟨u, huN, hus, hu0⟩` from `hN _ htw`. Establish `ht0` using `algebraMap_ne_zero' hpP ht`. Use `⟨(algebraMap (𝓞 E) E t)⁻¹ • u, ⟨t, ht, ?_⟩, Submodule.smul_mem _ _ hus, fun a => ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_eq_alg, smul_smul, mul_inv_cancel₀ ht0, one_smul]`. Conclude with `huN`. Establish `e : w - (algebraMap (𝓞 E) E t)⁻¹ • u = (algebraMap (𝓞 E) E t)⁻¹ • (t • w - u)`. Rewrite using `[smul_eq_alg, smul_sub, smul_smul, inv_mul_cancel₀ ht0, one_smul]`. Rewrite using `[e, map_smul, smul_eq_mul, hJ_apply, hu0 a, mul_zero]`.

Establish `hprim : ∀ N : Submodule (𝓞 E) (Fin n → E), (∀ c : E, c • z ∈ N → c ∈ (algebraMap (𝓞 E) E).range) → ∀ c : E, c • z ∈ (Formalism.HermitianLatticesTheory.loc (K` using `E) p N).toAddSubgroup → c ∈ locRing p := by`. Introduce `N hN c hc`. Take `⟨t, ht, htc⟩` from `hc`. Rewrite `htc` using `[smul_eq_alg, smul_smul]`. Take `⟨r, hr⟩` from `hN _ htc`.

Establish `ht0` using `algebraMap_ne_zero' hpP ht`. Rewrite using `[mem_locRing, mem_locR_iff hpP]`. Use `⟨r, t, ht, ?_⟩` and prove the remaining obligations. Rewrite using `[hr]`. Clear the denominators using the available nonvanishing facts.

Establish `hzloc : ∀ N : Submodule (𝓞 E) (Fin n → E), z ∈ N → z ∈ (Formalism.HermitianLatticesTheory.loc (K` using `E) p N).toAddSubgroup := fun N hz => ⟨1, one_mem _, by rw [one_smul]; exact hz⟩`. Take `⟨g, hg, hgs, hgz, hm⟩` from `hZ E (Fin n → E) (hJ J) hK (hJ_symm hJh) (hJ_nondeg hdet) p hp s z (Formalism.HermitianLatticesTheory.loc (K := E) p L).toAddSubgroup (Formalism.HermitianLatticesTheory.loc (K := E) p M).toAddSubgroup (selfDualMod_loc hJh hLfg hLsp hLd hp) (selfDualMod_loc hJh hMfg hMsp hMd hp) h …`. Take `⟨γ, hγ, hγg⟩` from `gl_of_isom g hg`. Use `⟨γ, hγ, fun a => by rw [hγg, hgs a], by rw [hγg, hgz], loc_iff_of_isom g hm γ hγg⟩` and prove the remaining obligations.
-/
theorem semiGenusZ_of (hZ : SemiGenusZLoc) : SemiGenusZ := by
  intro E _ _ _ n J hK hJh hdet r s z L M hLfg hMfg hLsp hMsp hLd hMd hsz hU hSL hSM hzL hzM hPL hPM p hp
  have hpP := hp.isPrime

  have hU' : ∀ w ∈ Submodule.span E (Set.range s),
      w ∈ (Formalism.HermitianLatticesTheory.loc (K := E) p L).toAddSubgroup ↔ w ∈ (Formalism.HermitianLatticesTheory.loc (K := E) p M).toAddSubgroup := by
    intro w hw
    change w ∈ Formalism.HermitianLatticesTheory.loc (K := E) p L ↔ w ∈ Formalism.HermitianLatticesTheory.loc (K := E) p M
    constructor
    · rintro ⟨t, ht, htw⟩
      refine ⟨t, ht, (hU _ ?_).1 htw⟩
      rw [smul_eq_alg]; exact Submodule.smul_mem _ _ hw
    · rintro ⟨t, ht, htw⟩
      refine ⟨t, ht, (hU _ ?_).2 htw⟩
      rw [smul_eq_alg]; exact Submodule.smul_mem _ _ hw
  have hsplit : ∀ N : Submodule (𝓞 E) (Fin n → E),
      (∀ w ∈ N, ∃ w₁ ∈ N, w₁ ∈ Submodule.span E (Set.range s) ∧
        ∀ a, Formalism.UG.hform (starRingEnd E) J (s a) (w - w₁) = 0) →
      ∀ w ∈ (Formalism.HermitianLatticesTheory.loc (K := E) p N).toAddSubgroup, ∃ w₁ ∈ (Formalism.HermitianLatticesTheory.loc (K := E) p N).toAddSubgroup,
        w₁ ∈ Submodule.span E (Set.range s) ∧ ∀ a, hJ J (s a) (w - w₁) = 0 := by
    intro N hN w hw
    obtain ⟨t, ht, htw⟩ := hw
    obtain ⟨u, huN, hus, hu0⟩ := hN _ htw
    have ht0 := algebraMap_ne_zero' hpP ht
    refine ⟨(algebraMap (𝓞 E) E t)⁻¹ • u, ⟨t, ht, ?_⟩, Submodule.smul_mem _ _ hus, fun a => ?_⟩
    · rw [smul_eq_alg, smul_smul, mul_inv_cancel₀ ht0, one_smul]; exact huN
    · have e : w - (algebraMap (𝓞 E) E t)⁻¹ • u = (algebraMap (𝓞 E) E t)⁻¹ • (t • w - u) := by
        rw [smul_eq_alg, smul_sub, smul_smul, inv_mul_cancel₀ ht0, one_smul]
      rw [e, map_smul, smul_eq_mul, hJ_apply, hu0 a, mul_zero]
  have hprim : ∀ N : Submodule (𝓞 E) (Fin n → E),
      (∀ c : E, c • z ∈ N → c ∈ (algebraMap (𝓞 E) E).range) →
      ∀ c : E, c • z ∈ (Formalism.HermitianLatticesTheory.loc (K := E) p N).toAddSubgroup → c ∈ locRing p := by
    intro N hN c hc
    obtain ⟨t, ht, htc⟩ := hc
    rw [smul_eq_alg, smul_smul] at htc
    obtain ⟨r, hr⟩ := hN _ htc
    have ht0 := algebraMap_ne_zero' hpP ht
    rw [mem_locRing, mem_locR_iff hpP]
    refine ⟨r, t, ht, ?_⟩
    rw [hr]; field_simp
  have hzloc : ∀ N : Submodule (𝓞 E) (Fin n → E), z ∈ N → z ∈ (Formalism.HermitianLatticesTheory.loc (K := E) p N).toAddSubgroup :=
    fun N hz => ⟨1, one_mem _, by rw [one_smul]; exact hz⟩
  obtain ⟨g, hg, hgs, hgz, hm⟩ := hZ E (Fin n → E) (hJ J) hK (hJ_symm hJh) (hJ_nondeg hdet) p hp s z
    (Formalism.HermitianLatticesTheory.loc (K := E) p L).toAddSubgroup (Formalism.HermitianLatticesTheory.loc (K := E) p M).toAddSubgroup
    (selfDualMod_loc hJh hLfg hLsp hLd hp) (selfDualMod_loc hJh hMfg hMsp hMd hp)
    hsz hU' (hsplit L hSL) (hsplit M hSM) (hzloc L hzL) (hzloc M hzM) (hprim L hPL) (hprim M hPM)
  obtain ⟨γ, hγ, hγg⟩ := gl_of_isom g hg
  refine ⟨γ, hγ, fun a => by rw [hγg, hgs a], by rw [hγg, hgz], loc_iff_of_isom g hm γ hγg⟩

end Formalism.L2.SG.Pf.LatDictZ.Z0.BR
