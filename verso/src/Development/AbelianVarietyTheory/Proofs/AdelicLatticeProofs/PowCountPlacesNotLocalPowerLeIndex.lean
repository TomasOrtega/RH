import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowCardLeIndexIInfOfPrimeStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitsMappingToPowersLeUnitsLocalKummerNormsStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsApproxModPowersStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitNotLocalKummerNormOfNotPowStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitsLocalPowersAtPlacesIndexLeStatement
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

/- English proof (translation)
Rewrite using `[mem_kNorm, mem_kNorm]`. Conclude with `Iff.rfl`.
-/
theorem mem_kNorm_iff_map_mem_id (p : ℕ) {F L : Type} [Field F] [Field L] (φ : F →+* L) (δ : F)
    (x : Fˣ) :
    x ∈ kNorm p φ δ ↔ Units.map (φ : F →* L) x ∈ kNorm p (RingHom.id L) (φ δ) := by
  rw [mem_kNorm, mem_kNorm]
  exact Iff.rfl

/- English proof (translation)
Introduce `p F _ _ _ ζ δ S hp hζ`. Establish `hpow` using `(GlobalTheory.T.unitsMappingToPowers_le_unitsLocalKummerNorms p hp.pos).1`. Establish `hPN : finPow p F S ≤ finNorm p F δ S`. Unfold `finPow finNorm`. Conclude with `iInf_mono fun v => iInf_mono fun _ => hpow _ _ _ _`.

Establish `h0 : (finNorm p F δ S).index ≠ 0` using `ne_zero_of_dvd_ne_zero (GlobalTheory.T.unitsLocalPowersAtPlaces_index_le p F S hp.pos).1 (Subgroup.index_dvd_of_le hPN)`. Use `⟨h0, ?_⟩` and prove the remaining obligations. Use `set A : Set (HeightOneSpectrum (𝓞 F)) := {v | v ∈ S ∧ ∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) δ} with hA`. Establish `hAf : A.Finite` using `S.finite_toSet.subset fun v hv => hv.1`. Use `letI : Fintype A := hAf.fintype`.

Set `K : A → Subgroup Fˣ` to `fun v => kNorm p (algebraMap F (v.1.adicCompletion F)) δ`. Establish `hle : finNorm p F δ S ≤ ⨅ i, K i` using `le_iInf fun v => iInf₂_le v.1 v.2.1`. Establish `hdvd` using `Subgroup.index_dvd_of_le hle`. Establish `hcard : Fintype.card A = tNon p F δ S`. Rewrite using `[← Nat.card_eq_fintype_card]`.

Both sides reduce to the same expression. Rewrite using `[← hcard]`. Use `le_trans (GlobalTheory.T.pow_card_le_index_iInf_of_prime' p Fˣ A K hp ?_ ?_ (ne_zero_of_dvd_ne_zero h0 hdvd)) (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd)` and prove the remaining obligations. Introduce `v x`. Conclude with `hpow _ _ _ _ ⟨algebraMap F _ (x : F), by simp⟩`.

Introduce `v`. Take `⟨c, hc⟩` from `GlobalTheory.T.exists_unit_not_localKummerNorm_of_not_pow p F ζ δ v.1 hp hζ v.2.2`. Take `⟨x, hx0, hxv⟩` from `GlobalTheory.T.exists_approx_mod_powers' p F S (Function.update (fun w : HeightOneSpectrum (𝓞 F) => (1 : w.adicCompletion F)) v.1 (c : v.1.adicCompletion F)) hp.pos (by`. Introduce `w`. Distinguish the cases in `hw : w = v.1`.

Substitute `hw` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne hw])`. Use `⟨Units.mk0 x hx0, ?_, ?_⟩` and prove the remaining obligations. Introduce `hm`.

Take `⟨r, hr⟩` from `hxv v.1 v.2.1`. Rewrite `hr` using `[Function.update_self]`. Establish `hr0 : r ≠ 0`. Introduce and unpack `rfl`. Rewrite `hr` using `[zero_pow hp.ne_zero, mul_zero]`.

Conclude with `hx0 (by simpa using hr)`. Establish `hm'` using `(mem_kNorm_iff_map_mem_id p _ δ _).1 hm`. Establish `hrm : (Units.mk0 r hr0) ^ p ∈ kNorm p (RingHom.id (v.1.adicCompletion F)) (algebraMap F (v.1.adicCompletion F) δ)` using `hpow _ _ _ _ ⟨r, by simp⟩`. Apply `hc` to reduce the goal to its premises. Establish `hq` using `Subgroup.div_mem _ hm' hrm`.

Use `hq using 1` and compare the differences between its conclusion and the goal. Rewrite using `[eq_div_iff_mul_eq']`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `using hr.symm`. Introduce `w hj`.

Establish `hw : w.1 ≠ v.1` using `fun h => hj (Subtype.ext h)`. Take `⟨r, hr⟩` from `hxv w.1 w.2.1`. Rewrite `hr` using `[Function.update_of_ne hw, one_mul]`. Conclude with `hpow _ _ _ _ ⟨r, hr.symm⟩`.
-/
theorem pow_tNon_le_index_finNorm :
    ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (ζ δ : F)
      (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p →
      (finNorm p F δ S).index ≠ 0 ∧ p ^ tNon p F δ S ≤ (finNorm p F δ S).index := by
  intro p F _ _ _ ζ δ S hp hζ
  classical
  have hpow := (GlobalTheory.T.unitsMappingToPowers_le_unitsLocalKummerNorms p hp.pos).1
  have hPN : finPow p F S ≤ finNorm p F δ S := by
    unfold finPow finNorm
    exact iInf_mono fun v => iInf_mono fun _ => hpow _ _ _ _
  have h0 : (finNorm p F δ S).index ≠ 0 :=
    ne_zero_of_dvd_ne_zero (GlobalTheory.T.unitsLocalPowersAtPlaces_index_le p F S hp.pos).1 (Subgroup.index_dvd_of_le hPN)
  refine ⟨h0, ?_⟩
  set A : Set (HeightOneSpectrum (𝓞 F)) :=
    {v | v ∈ S ∧ ∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) δ} with hA
  have hAf : A.Finite := S.finite_toSet.subset fun v hv => hv.1
  letI : Fintype A := hAf.fintype
  let K : A → Subgroup Fˣ := fun v => kNorm p (algebraMap F (v.1.adicCompletion F)) δ
  have hle : finNorm p F δ S ≤ ⨅ i, K i := le_iInf fun v => iInf₂_le v.1 v.2.1
  have hdvd := Subgroup.index_dvd_of_le hle
  have hcard : Fintype.card A = tNon p F δ S := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  rw [← hcard]
  refine le_trans (GlobalTheory.T.pow_card_le_index_iInf_of_prime' p Fˣ A K hp ?_ ?_ (ne_zero_of_dvd_ne_zero h0 hdvd))
    (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd)
  · intro v x
    exact hpow _ _ _ _ ⟨algebraMap F _ (x : F), by simp⟩
  · intro v
    obtain ⟨c, hc⟩ := GlobalTheory.T.exists_unit_not_localKummerNorm_of_not_pow p F ζ δ v.1 hp hζ v.2.2
    obtain ⟨x, hx0, hxv⟩ := GlobalTheory.T.exists_approx_mod_powers' p F S
      (Function.update (fun w : HeightOneSpectrum (𝓞 F) => (1 : w.adicCompletion F)) v.1
        (c : v.1.adicCompletion F)) hp.pos (by
        intro w
        by_cases hw : w = v.1
        · subst hw; simp
        · simp [Function.update_of_ne hw])
    refine ⟨Units.mk0 x hx0, ?_, ?_⟩
    · intro hm
      obtain ⟨r, hr⟩ := hxv v.1 v.2.1
      rw [Function.update_self] at hr
      have hr0 : r ≠ 0 := by
        rintro rfl
        rw [zero_pow hp.ne_zero, mul_zero] at hr
        exact hx0 (by simpa using hr)
      have hm' := (mem_kNorm_iff_map_mem_id p _ δ _).1 hm
      have hrm : (Units.mk0 r hr0) ^ p ∈ kNorm p (RingHom.id (v.1.adicCompletion F))
          (algebraMap F (v.1.adicCompletion F) δ) := hpow _ _ _ _ ⟨r, by simp⟩
      apply hc
      have hq := Subgroup.div_mem _ hm' hrm
      convert hq using 1
      rw [eq_div_iff_mul_eq']
      apply Units.ext
      simpa using hr.symm
    · intro w hj
      have hw : w.1 ≠ v.1 := fun h => hj (Subtype.ext h)
      obtain ⟨r, hr⟩ := hxv w.1 w.2.1
      rw [Function.update_of_ne hw, one_mul] at hr
      exact hpow _ _ _ _ ⟨r, hr.symm⟩

end GlobalTheory.CNorm
