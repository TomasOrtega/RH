import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.BoundedOnFramesIffIntegralOnFrames
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyPadicIntRingHomOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAlgebraMapEqOfValVLeOne

noncomputable section

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FreeQuotientRank Formalism.L2.Pj Formalism.L2.Pj.QAt

section Norm

variable {V F C : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F]
  [Algebra V F] [IsFractionRing V F] [NormedField C] (f : F →+* C)
  (hf : ∀ v : V, ‖f (algebraMap V F v)‖ ≤ 1)

include hf

omit [IsDomain V] [IsDiscreteValuationRing V] [IsFractionRing V F] in
/- English proof (translation)
Establish `h : ‖f (algebraMap V F u)‖ * ‖f (algebraMap V F (u⁻¹ : Vˣ))‖ = 1`. Rewrite using `[← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]`. Conclude with `le_antisymm (hf _) (h.ge.trans (mul_le_of_le_one_right (norm_nonneg _) (hf _)))`.
-/
theorem norm_map_unit_eq_one (u : Vˣ) : ‖f (algebraMap V F u)‖ = 1 := by
  have h : ‖f (algebraMap V F u)‖ * ‖f (algebraMap V F (u⁻¹ : Vˣ))‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
  exact le_antisymm (hf _) (h.ge.trans (mul_le_of_le_one_right (norm_nonneg _) (hf _)))

/- English proof (translation)
Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ hx`. Establish `hv : vV V (u • algebraMap V F π ^ n) = n`. Rewrite using `[vV, Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀, PlaceCompletion.valV_algebraMap_of_isUnit u.isUnit, PlaceCompletion.valV_algebraMap_of_irreducible hπ, one_mul, ← WithZero.exp_zsmul, WithZero.log_exp]`. Simplify using the standard rewrite rules. Rewrite using `[hv, Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀, norm_mul, norm_zpow, norm_map_unit_eq_one f hf, one_mul]`.
-/
theorem norm_map_eq_zpow_vV {π : V} (hπ : Irreducible π) {x : F} (hx : x ≠ 0) :
    ‖f x‖ = ‖f (algebraMap V F π)‖ ^ vV V x := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ hx
  have hv : vV V (u • algebraMap V F π ^ n) = n := by
    rw [vV, Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀,
      PlaceCompletion.valV_algebraMap_of_isUnit u.isUnit,
      PlaceCompletion.valV_algebraMap_of_irreducible hπ, one_mul, ← WithZero.exp_zsmul,
      WithZero.log_exp]
    simp
  rw [hv, Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀, norm_mul, norm_zpow,
    norm_map_unit_eq_one f hf, one_mul]

/- English proof (translation)
Use `⟨fun h => ?_, by rintro ⟨v, rfl⟩; exact hf v⟩` and prove the remaining obligations. Distinguish the cases in `hx : x = 0`. Conclude with `⟨0, by simp [hx]⟩`. Establish `h0 : 0 < ‖f (algebraMap V F π)‖` using `norm_pos_iff.2 ((map_ne_zero f).2 ((map_ne_zero_iff _ (IsFractionRing.injective V F)).2 hπ.ne_zero))`. Rewrite `h` using `[norm_map_eq_zpow_vV f hf hπ hx, zpow_le_one_iff_right_of_lt_one₀ h0 h1]`.

Use `PlaceCompletion.exists_algebraMap_eq_of_valV_le_one ?_` and prove the remaining obligations. Rewrite using `[← WithZero.exp_log (valV_ne_zero (V := V) hx), ← WithZero.exp_zero, WithZero.exp_le_exp]`. Rewrite `h` using `[vV]`. Use linear arithmetic over natural numbers and integers.
-/
theorem norm_map_le_one_iff {π : V} (hπ : Irreducible π) (h1 : ‖f (algebraMap V F π)‖ < 1) (x : F) :
    ‖f x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V F) := by
  refine ⟨fun h => ?_, by rintro ⟨v, rfl⟩; exact hf v⟩
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  have h0 : 0 < ‖f (algebraMap V F π)‖ := norm_pos_iff.2 ((map_ne_zero f).2
    ((map_ne_zero_iff _ (IsFractionRing.injective V F)).2 hπ.ne_zero))
  rw [norm_map_eq_zpow_vV f hf hπ hx, zpow_le_one_iff_right_of_lt_one₀ h0 h1] at h
  refine PlaceCompletion.exists_algebraMap_eq_of_valV_le_one ?_
  rw [← WithZero.exp_log (valV_ne_zero (V := V) hx), ← WithZero.exp_zero, WithZero.exp_le_exp]
  rw [vV] at h
  omega

end Norm

open DiscEval in

/- English proof (translation)
Introduce `K₁ _ _ w`. Use `⟨?_, fun Tv io e hfin ho => ?_⟩` and prove the remaining obligations. Take `⟨T, io, h1, h2, -⟩` from `PlaceCompletion.exists_initial_completion K₁ w`. Conclude with `⟨T, io, h2, h1⟩`. Use `haveI : Finite (IsLocalRing.ResidueField Tv.V) := hfin`.

Take `⟨p, _, _, _⟩` from `exists_padicInt_algebra_finite Tv.V`. Take `⟨i, hinj, hi⟩` from `exists_injective_norm_le_one (p := p) Tv.V (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)`. Set `ιT : Tv.Fr →+* ℂ_[p]` to `IsFractionRing.lift hinj`. Establish `hι : ∀ v, ιT (algebraMap Tv.V Tv.Fr v) = i v` using `fun v => IsFractionRing.lift_algebraMap hinj v`. Establish `hf : ∀ v, ‖ιT (algebraMap Tv.V Tv.Fr v)‖ ≤ 1` using `fun v => by rw [hι]; exact hi v`.

Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible Tv.V`. Establish `h0 : 0 < ‖i π‖` using `norm_pos_iff.2 ((map_ne_zero_iff i hinj).2 hπ.ne_zero)`. Establish `h1 : ‖i π‖ < 1` using `(hi π).lt_of_ne fun h => hπ.not_isUnit ((norm_map_eq_one_iff i hi hinj π).1 h)`. Set `Z : FinSite K₁ w` to `{ K := ℂ_[p] ι := ιT.comp io r := ‖i π‖ ^ e r_pos := pow_pos h0 e r_lt := pow_lt_one₀ h0.le h1 ho.1.ne' norm_ι := fun x hx => by`. Rewrite using `[RingHom.comp_apply, norm_map_eq_zpow_vV ιT hf hπ ((map_ne_zero io).2 hx), hι, ho.2 x, zpow_mul, zpow_natCast]`.

Both sides reduce to the same expression. Use `K₀ := algField p`. Use `res := residueFieldInfiniteOn_algField p`. Use `S := algDisc p`. Use `S_disc := fun _ ht => ht.2`.

Use `S_dense := algDisc_dense p`. Use `S_units := mul_mem_algDisc p }`. Use `⟨Z, ιT, rfl, norm_map_le_one_iff ιT hf hπ (by rw [hι]; exact h1), ?_⟩` and prove the remaining obligations. Introduce `(s : Finset ℂ_[p]) hs`. Establish `hsK : (s : Set ℂ_[p]) ⊆ algField p` using `fun x hx => (hs x hx).1.elim id fun h => h.1`.

Use `haveI := finiteDimensional_genField i hi s.finite_toSet`. Use `set L := genField i (s : Set ℂ_[p])`. Use `haveI : CharZero (integralClosure ℤ_[p] L) := RingHom.charZero (intEmb L)`. Set `T' : CDVR` to `{ V := integralClosure ℤ_[p] L, cpl := isAdicComplete_integralClosure L }`. Take `⟨j, hj⟩` from `exists_comp_eq_of_mem_range _ (intEmb_injective L) i fun a => (mem_range_intEmb_iff _ _).2 ⟨map_mem_genField i hi hsK a, hi a⟩`.

Set `i' : FractionRing (integralClosure ℤ_[p] L) →+* ℂ_[p]` to `IsFractionRing.lift (intEmb_injective L)`. Establish `hi' : ∀ v, i' (algebraMap _ _ v) = intEmb L v` using `fun v => IsFractionRing.lift_algebraMap (intEmb_injective L) v`. Take `⟨π', hπ'⟩` from `IsDiscreteValuationRing.exists_irreducible (integralClosure ℤ_[p] L)`. Use `⟨T', j, i', finite_residueField_integralClosure L, isLocalHom_of_intEmb_eq i hi L hinj hj, fun v => (hi' _).trans ((hj v).trans (hι v).symm), norm_map_le_one_iff i' (fun v => by rw [hi']; exact norm_intEmb_le_one L v) hπ' (by` and prove the remaining obligations. Rewrite using `[hi', ← mem_maximalIdeal_iff_norm]`.

Conclude with `hπ'.not_isUnit), fun x hx => ?_⟩`. Take `⟨v, hv⟩` from `(mem_range_intEmb_iff L x).2 ⟨mem_genField_of_mem i hi hsK hx, (hs x hx).2⟩`. Conclude with `⟨v, (hi' v).trans hv⟩`.
-/
theorem exists_finSite_siteAlg :
    ∀ (K₁ : Type) [Field K₁] [NumberField K₁] (w : HeightOneSpectrum (𝓞 K₁)),
      (∃ (Tv : CDVR) (io : K₁ →+* Tv.Fr), Tv.FinRes ∧ OverLa w Tv.V io 1) ∧
      ∀ (Tv : CDVR) (io : K₁ →+* Tv.Fr) (e : ℕ), Tv.FinRes → OverLa w Tv.V io e →
        ∃ (Z : FinSite K₁ w) (ιT : Tv.Fr →+* Z.K), ιT.comp io = Z.ι ∧
          (∀ x : Tv.Fr, ‖ιT x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap Tv.V Tv.Fr)) ∧ SiteAlg Z Tv ιT := by
  intro K₁ _ _ w
  refine ⟨?_, fun Tv io e hfin ho => ?_⟩
  · obtain ⟨T, io, h1, h2, -⟩ := PlaceCompletion.exists_initial_completion K₁ w
    exact ⟨T, io, h2, h1⟩
  haveI : Finite (IsLocalRing.ResidueField Tv.V) := hfin
  obtain ⟨p, _, _, _⟩ := exists_padicInt_algebra_finite Tv.V
  obtain ⟨i, hinj, hi⟩ := exists_injective_norm_le_one (p := p) Tv.V
    (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  let ιT : Tv.Fr →+* ℂ_[p] := IsFractionRing.lift hinj
  have hι : ∀ v, ιT (algebraMap Tv.V Tv.Fr v) = i v := fun v => IsFractionRing.lift_algebraMap hinj v
  have hf : ∀ v, ‖ιT (algebraMap Tv.V Tv.Fr v)‖ ≤ 1 := fun v => by rw [hι]; exact hi v
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible Tv.V
  have h0 : 0 < ‖i π‖ := norm_pos_iff.2 ((map_ne_zero_iff i hinj).2 hπ.ne_zero)
  have h1 : ‖i π‖ < 1 :=
    (hi π).lt_of_ne fun h => hπ.not_isUnit ((norm_map_eq_one_iff i hi hinj π).1 h)
  let Z : FinSite K₁ w :=
    { K := ℂ_[p]
      ι := ιT.comp io
      r := ‖i π‖ ^ e
      r_pos := pow_pos h0 e
      r_lt := pow_lt_one₀ h0.le h1 ho.1.ne'
      norm_ι := fun x hx => by
        rw [RingHom.comp_apply, norm_map_eq_zpow_vV ιT hf hπ ((map_ne_zero io).2 hx), hι, ho.2 x,
          zpow_mul, zpow_natCast]
        rfl
      K₀ := algField p
      res := residueFieldInfiniteOn_algField p
      S := algDisc p
      S_disc := fun _ ht => ht.2
      S_dense := algDisc_dense p
      S_units := mul_mem_algDisc p }
  refine ⟨Z, ιT, rfl, norm_map_le_one_iff ιT hf hπ (by rw [hι]; exact h1), ?_⟩
  intro (s : Finset ℂ_[p]) hs
  have hsK : (s : Set ℂ_[p]) ⊆ algField p := fun x hx => (hs x hx).1.elim id fun h => h.1
  haveI := finiteDimensional_genField i hi s.finite_toSet
  set L := genField i (s : Set ℂ_[p])
  haveI : CharZero (integralClosure ℤ_[p] L) := RingHom.charZero (intEmb L)
  let T' : CDVR := { V := integralClosure ℤ_[p] L, cpl := isAdicComplete_integralClosure L }
  obtain ⟨j, hj⟩ := exists_comp_eq_of_mem_range _ (intEmb_injective L) i fun a =>
    (mem_range_intEmb_iff _ _).2 ⟨map_mem_genField i hi hsK a, hi a⟩
  let i' : FractionRing (integralClosure ℤ_[p] L) →+* ℂ_[p] := IsFractionRing.lift (intEmb_injective L)
  have hi' : ∀ v, i' (algebraMap _ _ v) = intEmb L v := fun v =>
    IsFractionRing.lift_algebraMap (intEmb_injective L) v
  obtain ⟨π', hπ'⟩ := IsDiscreteValuationRing.exists_irreducible (integralClosure ℤ_[p] L)
  refine ⟨T', j, i', finite_residueField_integralClosure L, isLocalHom_of_intEmb_eq i hi L hinj hj,
    fun v => (hi' _).trans ((hj v).trans (hι v).symm),
    norm_map_le_one_iff i' (fun v => by rw [hi']; exact norm_intEmb_le_one L v) hπ' (by
      rw [hi', ← mem_maximalIdeal_iff_norm]
      exact hπ'.not_isUnit), fun x hx => ?_⟩
  obtain ⟨v, hv⟩ := (mem_range_intEmb_iff L x).2 ⟨mem_genField_of_mem i hi hsK hx, (hs x hx).2⟩
  exact ⟨v, (hi' v).trans hv⟩

end GlobalTheory.ArcQ
