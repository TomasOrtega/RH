import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LtSeries
import GroundTheory.LocalFields.LubinTateLimitGalois
import GroundTheory.LocalFields.LubinTateUnramified
import GroundTheory.LocalFields.KroneckerWeber

noncomputable section

open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup IntermediateField

namespace GlobalTheory.PZ.LTExists

section General

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {Ω : Type} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra F Ω] [ValuativeExtension F Ω] [Algebra.IsAlgebraic F Ω]

/- English proof (translation)
Use `set M := E ⊓ maximalUnramifiedExtension F Ω with hM`. Establish `hME : M ≤ E` using `inf_le_left`. Use `haveI : FiniteDimensional F M := Module.Finite.of_injective (IntermediateField.inclusion hME).toLinearMap (IntermediateField.inclusion_injective hME)`. Apply `le_antisymm` to reduce the goal to its premises. Take `⟨x, hx⟩` from `Field.exists_primitive_element F M`.

Establish `hxM : F⟮(x : Ω)⟯ = M`. Use `congrArg (IntermediateField.map M.val) hx` as an intermediate fact. Rewrite `this` using `[adjoin_map, Set.image_singleton, ← AlgHom.fieldRange_eq_map, fieldRange_val]`. Then use the resulting hypothesis. Take `⟨U, hU, hxU⟩` from `mem_maximalUnramifiedExtension_iff.mp x.2.2`. Use `hU.1` as an intermediate fact.

Establish `hMU : M ≤ U` using `hxM ▸ adjoin_simple_le_iff.mpr hxU`. Establish `he : ramificationIndex F M = 1`. Establish `h` using `ramificationIndex_dvd_of_le hMU`. Rewrite `h` using `[hU.ramificationIndex_eq_one]`. Conclude with `Nat.dvd_one.mp h`.

Rewrite using `[← ramificationIndex_mul_residueDegree F M, he, one_mul]`. Conclude with `Nat.le_of_dvd (residueDegree_pos F E) (residueDegree_dvd_of_le hME)`. Take `⟨ξ, hξ⟩` from `exists_isPrimitiveRoot_card_residueField_sub_one (L := E)`. Establish `hξ' : IsPrimitiveRoot ((ξ : E) : Ω) (Nat.card 𝓀[F] ^ residueDegree F E - 1)`. Rewrite using `[← card_residueField_eq_pow_residueDegree F E]`.

Conclude with `(hξ.map_of_injective (f := (𝒪[E]).subtype) Subtype.val_injective).map_of_injective (f := E.val) Subtype.val_injective`. Establish `hf0 : residueDegree F E ≠ 0` using `(residueDegree_pos F E).ne'`. Rewrite using `[← (isUnramifiedSubextension_adjoin hf0 hξ').2]`. Conclude with `IntermediateField.finrank_le_of_le_right (le_inf (adjoin_simple_le_iff.mpr (ξ : E).2) (adjoin_le_maximalUnramifiedExtension hf0 hξ'))`.
-/
theorem finrank_inf_maximalUnramified [IsSepClosed Ω] [CharZero F] (E : IntermediateField F Ω)
    [FiniteDimensional F E] :
    Module.finrank F ↥(E ⊓ maximalUnramifiedExtension F Ω) = residueDegree F E := by
  set M := E ⊓ maximalUnramifiedExtension F Ω with hM
  have hME : M ≤ E := inf_le_left
  haveI : FiniteDimensional F M :=
    Module.Finite.of_injective (IntermediateField.inclusion hME).toLinearMap
      (IntermediateField.inclusion_injective hME)
  apply le_antisymm
  · obtain ⟨x, hx⟩ := Field.exists_primitive_element F M
    have hxM : F⟮(x : Ω)⟯ = M := by
      have := congrArg (IntermediateField.map M.val) hx
      rwa [adjoin_map, Set.image_singleton, ← AlgHom.fieldRange_eq_map, fieldRange_val] at this
    obtain ⟨U, hU, hxU⟩ := mem_maximalUnramifiedExtension_iff.mp x.2.2
    have := hU.1
    have hMU : M ≤ U := hxM ▸ adjoin_simple_le_iff.mpr hxU
    have he : ramificationIndex F M = 1 := by
      have h := ramificationIndex_dvd_of_le hMU
      rw [hU.ramificationIndex_eq_one] at h
      exact Nat.dvd_one.mp h
    rw [← ramificationIndex_mul_residueDegree F M, he, one_mul]
    exact Nat.le_of_dvd (residueDegree_pos F E) (residueDegree_dvd_of_le hME)
  · obtain ⟨ξ, hξ⟩ := exists_isPrimitiveRoot_card_residueField_sub_one (L := E)
    have hξ' : IsPrimitiveRoot ((ξ : E) : Ω) (Nat.card 𝓀[F] ^ residueDegree F E - 1) := by
      rw [← card_residueField_eq_pow_residueDegree F E]
      exact (hξ.map_of_injective (f := (𝒪[E]).subtype) Subtype.val_injective).map_of_injective
        (f := E.val) Subtype.val_injective
    have hf0 : residueDegree F E ≠ 0 := (residueDegree_pos F E).ne'
    rw [← (isUnramifiedSubextension_adjoin hf0 hξ').2]
    exact IntermediateField.finrank_le_of_le_right
      (le_inf (adjoin_simple_le_iff.mpr (ξ : E).2) (adjoin_le_maximalUnramifiedExtension hf0 hξ'))

/- English proof (translation)
Establish `hq` using `one_lt_card_residueField' F`. Establish `hf` using `isLubinTateSeries_ltPoly π`. Use `set p := (ltPoly π).map (algebraMap 𝒪[F] F) with hp`. Establish `hsurj : ∀ y : Ω, ∃ x : Ω, Polynomial.aeval x p = y`. Introduce `y`.

Establish `hd : (p.map (algebraMap F Ω)).natDegree ≠ 0`. Rewrite using `[hp, Polynomial.map_map, (ltPoly_monic π).natDegree_map, natDegree_ltPoly]`. Use linear arithmetic over natural numbers and integers. Take `⟨x, hx⟩` from `IsAlgClosed.eval_surjective hd y`. Conclude with `⟨x, (Polynomial.eval_map_algebraMap p x).symm.trans hx⟩`.

Use `choose r hr using hsurj`. Establish `hπ0 : algebraMap F Ω (π : F) ≠ 0`. Rewrite using `[ne_eq, map_eq_zero_iff _ (algebraMap F Ω).injective]`. Conclude with `fun h => hπ.ne_zero (Subtype.ext h)`. Take `⟨w, hw⟩` from `IsAlgClosed.exists_pow_nat_eq (-algebraMap F Ω (π : F)) (n := Nat.card 𝓀[F] - 1) (by omega)`.

Establish `hw0 : w ≠ 0`. Introduce and unpack `rfl`. Rewrite `hw` using `[zero_pow (by omega), zero_eq_neg]`. Conclude with `hπ0 hw`. Set `z : ℕ → Ω` to `fun n => Nat.casesOn n 0 fun m => r^[m] w`.

Establish `hz : ∀ n, Polynomial.aeval (z (n + 1)) p = z n`. Introduce and unpack `(_ | n)`. Use `show Polynomial.aeval w p = 0`. Rewrite using `[hp, aeval_ltPoly, ← Nat.sub_add_cancel hq.le, pow_succ, hw]`. Expand and normalize the polynomial expressions, which then agree.

Use `show Polynomial.aeval (r^[n + 1] w) p = r^[n] w`. Rewrite using `[Function.iterate_succ_apply', hr]`. Establish `hiter : ∀ k n, Polynomial.aeval (z (n + k)) ((ltPolyIter π k).map (algebraMap 𝒪[F] F)) = z n`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => intro n`. Simplify using `[ltPolyIter_zero]`. Consider the case `succ k ih`. Introduce `n`. Rewrite using `[ltPolyIter_succ, Polynomial.map_comp, Polynomial.aeval_comp, ← hz n, show n + (k + 1) = n + 1 + k by ring, ih]`.

Establish `h0 : ∀ n, Polynomial.aeval (z n) ((ltPolyIter π n).map (algebraMap 𝒪[F] F)) = 0`. Introduce `n`. Establish `h` using `hiter n 0`. Rewrite `h` using `[zero_add]`. Then use the resulting hypothesis. Establish `hv : ∀ n, valuation Ω (z n) < 1` using `fun n => valuation_lt_one_of_aeval_ltPolyIter_eq_zero hπ n (h0 n)`.

Set `e` to `lubinTateLimitGalEquiv (Ω := Ω) hπ hf`. Use `⟨e.symm.toMulEquiv.toMonoidHom.comp (AlgEquiv.restrictNormalHom (lubinTateLimit Ω hπ)), z, rfl, hw0, fun n => by rw [← hz n, hp, aeval_ltPoly], fun g => ?_⟩` and prove the remaining obligations. Use `set u : 𝒪[F]ˣ := e.symm (AlgEquiv.restrictNormalHom (lubinTateLimit Ω hπ) g) with hu`. Establish `hφ0` using `(lubinTateHom hπ hf hf (u : 𝒪[F])).constantCoeff_eq_zero`. Use `⟨(lubinTateHom hπ hf hf (u : 𝒪[F])).toPowerSeries, hφ0, coeff_one_lubinTateHom hπ hf hf _, ?_, fun n => ?_⟩` and prove the remaining obligations.

Establish `h` using `subst_lubinTateHom hπ hf hf (u : 𝒪[F])`. Establish `hc : ((ltPoly π : Polynomial 𝒪[F]) : PowerSeries 𝒪[F]) = PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ Nat.card 𝓀[F]`. Simplify using `[ltPoly]`. Generalize the expression as in `(lubinTateHom hπ hf hf (u : 𝒪[F])).toPowerSeries = φ at h hφ0`. Rewrite `h` using `[hc]`.

Rewrite using `[← h]`. Establish `hs : PowerSeries.HasSubst φ` using `PowerSeries.HasSubst.of_constantCoeff_zero' hφ0`. Rewrite using `[← PowerSeries.coe_substAlgHom hs, map_add, map_mul, map_pow, PowerSeries.substAlgHom_X]`. Use `congr 2`. Conclude with `((PowerSeries.substAlgHom hs).commutes π).symm`.

Set `x : IdealPoint Ω (lubinTateFormalGroup hπ hf)` to `IdealPoint.mk (z n) (hv n)`. Establish `hx : x ∈ lubinTateTorsion Ω hf n` using `(mem_lubinTateTorsion_ltPoly_iff n x).mpr (h0 n)`. Establish `h1` using `lubinTateLimitGalEquiv_apply hπ hf u hx`. Establish `h2 : lubinTateLimitGalEquiv (Ω` using `Ω) hπ hf u = AlgEquiv.restrictNormalHom (lubinTateLimit Ω hπ) g := e.apply_symm_apply _`. Rewrite `h1` using `[h2, AlgEquiv.restrictNormalHom_apply, lubinTate_smul_val]`.

Establish `h3` using `hasSum_psEval' (lubinTateHom hπ hf hf (u : 𝒪[F])).toPowerSeries (fun _ : Unit => z n) fun _ => hv n`. Express the relevant statement in the definitionally equal form `g (z n) = psEval _ (fun _ => z n) at h1`. Rewrite `h3` using `[← (Finsupp.uniqueEquiv ()).symm.hasSum_iff, ← h1]`. Use `h3 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`.

Simplify using `[psTerm, PowerSeries.coeff, Finsupp.uniqueEquiv]`.
-/
theorem exists_data [IsAlgClosed Ω] [Normal F Ω] {π : 𝒪[F]} (hπ : Irreducible π) :
    ∃ (χ : (Ω ≃ₐ[F] Ω) →* 𝒪[F]ˣ) (z : ℕ → Ω), z 0 = 0 ∧ z 1 ≠ 0 ∧
      (∀ n, algebraMap F Ω (π : F) * z (n + 1) + z (n + 1) ^ Nat.card 𝓀[F] = z n) ∧
      ∀ g, ∃ φ : PowerSeries 𝒪[F], PowerSeries.constantCoeff φ = 0 ∧
        PowerSeries.coeff 1 φ = χ g ∧
        PowerSeries.C π * φ + φ ^ Nat.card 𝓀[F] =
          PowerSeries.subst (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ Nat.card 𝓀[F]) φ ∧
        ∀ n, HasSum (fun k => algebraMap F Ω ((PowerSeries.coeff k φ : 𝒪[F]) : F) * z n ^ k)
          (g (z n)) := by
  have hq := one_lt_card_residueField' F
  have hf := isLubinTateSeries_ltPoly π
  set p := (ltPoly π).map (algebraMap 𝒪[F] F) with hp

  have hsurj : ∀ y : Ω, ∃ x : Ω, Polynomial.aeval x p = y := by
    intro y
    have hd : (p.map (algebraMap F Ω)).natDegree ≠ 0 := by
      rw [hp, Polynomial.map_map, (ltPoly_monic π).natDegree_map, natDegree_ltPoly]
      omega
    obtain ⟨x, hx⟩ := IsAlgClosed.eval_surjective hd y
    exact ⟨x, (Polynomial.eval_map_algebraMap p x).symm.trans hx⟩
  choose r hr using hsurj
  have hπ0 : algebraMap F Ω (π : F) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (algebraMap F Ω).injective]
    exact fun h => hπ.ne_zero (Subtype.ext h)
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (-algebraMap F Ω (π : F)) (n := Nat.card 𝓀[F] - 1) (by omega)
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega), zero_eq_neg] at hw
    exact hπ0 hw
  let z : ℕ → Ω := fun n => Nat.casesOn n 0 fun m => r^[m] w
  have hz : ∀ n, Polynomial.aeval (z (n + 1)) p = z n := by
    rintro (_ | n)
    · show Polynomial.aeval w p = 0
      rw [hp, aeval_ltPoly, ← Nat.sub_add_cancel hq.le, pow_succ, hw]
      ring
    · show Polynomial.aeval (r^[n + 1] w) p = r^[n] w
      rw [Function.iterate_succ_apply', hr]
  have hiter : ∀ k n, Polynomial.aeval (z (n + k)) ((ltPolyIter π k).map (algebraMap 𝒪[F] F)) = z n := by
    intro k
    induction k with
    | zero => intro n; simp [ltPolyIter_zero]
    | succ k ih =>
      intro n
      rw [ltPolyIter_succ, Polynomial.map_comp, Polynomial.aeval_comp, ← hz n,
        show n + (k + 1) = n + 1 + k by ring, ih]
  have h0 : ∀ n, Polynomial.aeval (z n) ((ltPolyIter π n).map (algebraMap 𝒪[F] F)) = 0 := by
    intro n
    have h := hiter n 0
    rwa [zero_add] at h
  have hv : ∀ n, valuation Ω (z n) < 1 := fun n =>
    valuation_lt_one_of_aeval_ltPolyIter_eq_zero hπ n (h0 n)
  let e := lubinTateLimitGalEquiv (Ω := Ω) hπ hf
  refine ⟨e.symm.toMulEquiv.toMonoidHom.comp (AlgEquiv.restrictNormalHom (lubinTateLimit Ω hπ)), z, rfl, hw0,
    fun n => by rw [← hz n, hp, aeval_ltPoly], fun g => ?_⟩
  set u : 𝒪[F]ˣ := e.symm (AlgEquiv.restrictNormalHom (lubinTateLimit Ω hπ) g) with hu
  have hφ0 := (lubinTateHom hπ hf hf (u : 𝒪[F])).constantCoeff_eq_zero
  refine ⟨(lubinTateHom hπ hf hf (u : 𝒪[F])).toPowerSeries, hφ0, coeff_one_lubinTateHom hπ hf hf _, ?_, fun n => ?_⟩
  · have h := subst_lubinTateHom hπ hf hf (u : 𝒪[F])
    have hc : ((ltPoly π : Polynomial 𝒪[F]) : PowerSeries 𝒪[F]) =
        PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ Nat.card 𝓀[F] := by
      simp [ltPoly]
    generalize (lubinTateHom hπ hf hf (u : 𝒪[F])).toPowerSeries = φ at h hφ0
    rw [hc] at h
    rw [← h]
    have hs : PowerSeries.HasSubst φ := PowerSeries.HasSubst.of_constantCoeff_zero' hφ0
    rw [← PowerSeries.coe_substAlgHom hs, map_add, map_mul, map_pow, PowerSeries.substAlgHom_X]
    congr 2
    exact ((PowerSeries.substAlgHom hs).commutes π).symm
  · let x : IdealPoint Ω (lubinTateFormalGroup hπ hf) := IdealPoint.mk (z n) (hv n)
    have hx : x ∈ lubinTateTorsion Ω hf n := (mem_lubinTateTorsion_ltPoly_iff n x).mpr (h0 n)
    have h1 := lubinTateLimitGalEquiv_apply hπ hf u hx
    have h2 : lubinTateLimitGalEquiv (Ω := Ω) hπ hf u = AlgEquiv.restrictNormalHom (lubinTateLimit Ω hπ) g :=
      e.apply_symm_apply _
    rw [h2, AlgEquiv.restrictNormalHom_apply, lubinTate_smul_val] at h1
    have h3 := hasSum_psEval' (lubinTateHom hπ hf hf (u : 𝒪[F])).toPowerSeries (fun _ : Unit => z n) fun _ => hv n
    change g (z n) = psEval _ (fun _ => z n) at h1
    rw [← (Finsupp.uniqueEquiv ()).symm.hasSum_iff, ← h1] at h3
    convert h3 using 1
    funext k
    simp [psTerm, PowerSeries.coeff, Finsupp.uniqueEquiv]

/- English proof (translation)
Establish `hsub : PowerSeries.HasSubst (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q : PowerSeries A)` using `PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hq])`. Establish `h2` using `PowerSeries.map_subst hsub (h := h) φ`. Rewrite `h2` using `[← hc]`. Express the relevant statement in the definitionally equal form `PowerSeries.map h _ = PowerSeries.subst (PowerSeries.map h _) _ at h2`. Simplify `h2` using `only [map_add, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X]`.
-/
theorem map_commute {A B : Type} [CommRing A] [CommRing B] (h : A →+* B) (π : A) {q : ℕ} (hq : q ≠ 0)
    (φ : PowerSeries A) (hc : PowerSeries.C π * φ + φ ^ q =
      PowerSeries.subst (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q) φ) :
    PowerSeries.C (h π) * PowerSeries.map h φ + PowerSeries.map h φ ^ q =
      PowerSeries.subst (PowerSeries.C (h π) * PowerSeries.X + PowerSeries.X ^ q)
        (PowerSeries.map h φ) := by
  have hsub : PowerSeries.HasSubst
      (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q : PowerSeries A) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hq])
  have h2 := PowerSeries.map_subst hsub (h := h) φ
  rw [← hc] at h2
  change PowerSeries.map h _ = PowerSeries.subst (PowerSeries.map h _) _ at h2
  simpa only [map_add, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X] using h2

end General

open Formalism.BasicNotions Formalism.BasicNotions.Loc

variable (l : ℕ) [Fact l.Prime]

@[instance_reducible]
def omRel : ValuativeRel (Om l) := ValuativeRel.ofValuation (NormedField.valuation (K := Om l))

attribute [local instance] omRel

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem om_vle_iff (x y : Om l) : x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ := Iff.rfl

/- English proof (translation)
Establish `hc : (NormedField.valuation (K` using `Om l)).Compatible := Valuation.Compatible.ofValuation _`. Conclude with `IsValuativeTopology.of_mem_nhds_zero_iff_vle (NormedField.valuation (K := Om l)) (fun {s} ↦ (NormedField.toValued (K := Om l)).is_topological_valuation s)`.
-/
theorem omTop : IsValuativeTopology (Om l) := by
  have hc : (NormedField.valuation (K := Om l)).Compatible := Valuation.Compatible.ofValuation _
  exact IsValuativeTopology.of_mem_nhds_zero_iff_vle (NormedField.valuation (K := Om l))
    (fun {s} ↦ (NormedField.toValued (K := Om l)).is_topological_valuation s)

/- English proof (translation)
Break down `eq_or_ne b 0 with rfl | hb` into its components or cases. Rewrite using `[(valuation ℚ_[l]).vle_iff_le]`. Simplify using the standard rewrite rules. Rewrite using `[(valuation ℚ_[l]).vle_iff_le, ← div_le_one (norm_pos_iff.mpr hb), ← norm_div, ← PadicRank.mem_integer_padic_iff, Valuation.mem_integer_iff, map_div₀, div_le_one₀ (zero_lt_iff.mpr ((valuation ℚ_[l]).ne_zero_iff.mpr hb))]`.
-/
theorem padic_vle_iff (a b : ℚ_[l]) : a ≤ᵥ b ↔ ‖a‖ ≤ ‖b‖ := by
  rcases eq_or_ne b 0 with rfl | hb
  · rw [(valuation ℚ_[l]).vle_iff_le]
    simp
  · rw [(valuation ℚ_[l]).vle_iff_le, ← div_le_one (norm_pos_iff.mpr hb), ← norm_div,
      ← PadicRank.mem_integer_padic_iff, Valuation.mem_integer_iff, map_div₀,
      div_le_one₀ (zero_lt_iff.mpr ((valuation ℚ_[l]).ne_zero_iff.mpr hb))]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun a b => by rw [om_vle_iff, padic_vle_iff, norm_algebraMap', norm_algebraMap']⟩`.
-/
theorem omExt : ValuativeExtension ℚ_[l] (Om l) :=
  ⟨fun a b => by rw [om_vle_iff, padic_vle_iff, norm_algebraMap', norm_algebraMap']⟩

attribute [local instance] omTop omExt

variable {l}

/- English proof (translation)
Use `haveI := K.2`. Rewrite using `[Valuation.mem_integer_iff, ← isIntegral_iff ℚ_[l] ↥K.1 x]`. Conclude with `(RingEquiv.isIntegral_iff (PadicRank.padicIntEquivInteger l) (RingHom.ext fun _ => rfl) x)`.
-/
theorem mem_OL_iff (K : FinExt l) (x : ↥K.1) : x ∈ OL K ↔ x ∈ 𝒪[↥K.1] := by
  haveI := K.2
  rw [Valuation.mem_integer_iff, ← isIntegral_iff ℚ_[l] ↥K.1 x]
  exact (RingEquiv.isIntegral_iff (PadicRank.padicIntEquivInteger l) (RingHom.ext fun _ => rfl) x)

def intEquiv (K : FinExt l) : 𝒪[↥K.1] ≃+* ↥(OL K) where
  toFun x := ⟨x.1, (mem_OL_iff K _).2 x.2⟩
  invFun x := ⟨x.1, (mem_OL_iff K _).1 x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Use `haveI : CharP 𝓀[ℚ_[l]] l := by`. Rewrite using `[CharP.charP_iff_prime_eq_zero hl, ← map_natCast (IsLocalRing.residue 𝒪[ℚ_[l]]), IsLocalRing.residue_eq_zero_iff]`. Conclude with `(GroundTheory.LocalField.Padic.irreducible_natCast_integer l).not_isUnit`. Rewrite using `[maximalUnramifiedExtension_eq_adjoin, MaximalUnramifiedExtension]`.

Use `congr 1`. Use extensionality with `x`. Rewrite using `[mem_unramifiedRoots_iff]`. Use `exists_congr fun m => ?_` and prove the remaining obligations. Rewrite using `[Ne, CharP.cast_eq_zero_iff _ l]`.

Conclude with `⟨fun h => h.2, fun h => ⟨Nat.pos_of_ne_zero (by rintro rfl; exact h.1 (dvd_zero l)), h⟩⟩`.
-/
theorem kur_eq : MaximalUnramifiedExtension l = maximalUnramifiedExtension ℚ_[l] (Om l) := by
  have hl : l.Prime := Fact.out
  haveI : CharP 𝓀[ℚ_[l]] l := by
    rw [CharP.charP_iff_prime_eq_zero hl, ← map_natCast (IsLocalRing.residue 𝒪[ℚ_[l]]),
      IsLocalRing.residue_eq_zero_iff]
    exact (GroundTheory.LocalField.Padic.irreducible_natCast_integer l).not_isUnit
  rw [maximalUnramifiedExtension_eq_adjoin, MaximalUnramifiedExtension]
  congr 1
  ext x
  rw [mem_unramifiedRoots_iff]
  refine exists_congr fun m => ?_
  rw [Ne, CharP.cast_eq_zero_iff _ l]
  exact ⟨fun h => h.2, fun h => ⟨Nat.pos_of_ne_zero (by rintro rfl; exact h.1 (dvd_zero l)), h⟩⟩

/- English proof (translation)
The claim follows from `K.2; resCard K = Nat.card 𝓀[↥K.1] := by haveI := K.2 rw [card_residueField_eq_pow_residueDegree ℚ_[l] ↥K.1, GroundTheory.LocalField.Padic.card_residueField, resCard, K0, kur_eq, finrank_inf_maximalUnramified]`.
-/
theorem resCard_eq (K : FinExt l) : haveI := K.2; resCard K = Nat.card 𝓀[↥K.1] := by
  haveI := K.2
  rw [card_residueField_eq_pow_residueDegree ℚ_[l] ↥K.1, GroundTheory.LocalField.Padic.card_residueField,
    resCard, K0, kur_eq, finrank_inf_maximalUnramified]

end GlobalTheory.PZ.LTExists

namespace GlobalTheory.PZ

open Formalism.BasicNotions Formalism.BasicNotions.Loc LTExists

attribute [local instance] omRel omTop omExt

/- English proof (translation)
Use `haveI := K.2`. Take `⟨π, rfl⟩` from `(intEquiv K).surjective π`. Establish `hπ' : Irreducible π` using `(MulEquiv.irreducible_iff (intEquiv K).toMulEquiv).1 hπ`. Take `⟨χ, z, h0, h1, hz, H⟩` from `exists_data (Ω := Om l) hπ'`. Use `⟨(Units.map (𝒪[↥K.1]).subtype.toMonoidHom).comp (χ.comp (IntermediateField.fixingSubgroupEquiv K.1).toMonoidHom), z, hπ, h0, h1, fun n => by rw [resCard_eq]; exact hz n, fun g => ?_⟩` and prove the remaining obligations.

Take `⟨φ, c0, c1, hc, hs⟩` from `H (IntermediateField.fixingSubgroupEquiv K.1 g)`. Use `⟨intEquiv K (χ (IntermediateField.fixingSubgroupEquiv K.1 g)), rfl, PowerSeries.map (intEquiv K).toRingHom φ, ⟨?_, ?_, ?_⟩, fun n => hs n⟩` and prove the remaining obligations. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, c0, map_zero]`. Rewrite using `[PowerSeries.coeff_map, c1]`. Both sides reduce to the same expression.

Establish `hq` using `one_lt_card_residueField' ↥K.1`. Establish `hr : Nat.card 𝓀[↥K.1] = resCard K` using `(resCard_eq K).symm`. Rewrite `hc`, `hq` using `[hr]`. Conclude with `map_commute (intEquiv K).toRingHom π (by omega) φ hc`.
-/
theorem exists_ltData_of_irreducible (l : ℕ) [Fact l.Prime] (K : FinExt l) (π : ↥(OL K))
    (hπ : Irreducible π) :
    ∃ (χ : ↥(GK K) →* (↥K.1)ˣ) (z : ℕ → Om l), LTData K χ π z := by
  haveI := K.2
  obtain ⟨π, rfl⟩ := (intEquiv K).surjective π
  have hπ' : Irreducible π := (MulEquiv.irreducible_iff (intEquiv K).toMulEquiv).1 hπ
  obtain ⟨χ, z, h0, h1, hz, H⟩ := exists_data (Ω := Om l) hπ'
  refine ⟨(Units.map (𝒪[↥K.1]).subtype.toMonoidHom).comp
    (χ.comp (IntermediateField.fixingSubgroupEquiv K.1).toMonoidHom), z, hπ, h0, h1,
    fun n => by rw [resCard_eq]; exact hz n, fun g => ?_⟩
  obtain ⟨φ, c0, c1, hc, hs⟩ := H (IntermediateField.fixingSubgroupEquiv K.1 g)
  refine ⟨intEquiv K (χ (IntermediateField.fixingSubgroupEquiv K.1 g)), rfl,
    PowerSeries.map (intEquiv K).toRingHom φ, ⟨?_, ?_, ?_⟩, fun n => hs n⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, c0, map_zero]
  · rw [PowerSeries.coeff_map, c1]
    rfl
  · have hq := one_lt_card_residueField' ↥K.1
    have hr : Nat.card 𝓀[↥K.1] = resCard K := (resCard_eq K).symm
    rw [hr] at hc hq
    exact map_commute (intEquiv K).toRingHom π (by omega) φ hc

end GlobalTheory.PZ

end
