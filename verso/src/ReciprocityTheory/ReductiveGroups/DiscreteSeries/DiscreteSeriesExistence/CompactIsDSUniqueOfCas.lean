import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Arbitrary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Compact
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.VNormSqLowKSubRootLt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.VogDrop
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBasic
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.SmulOneMemUnitary

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

/- English proof (translation)
Simplify using `only [casimir, LinearMap.sum_apply, Module.End.mul_apply, sum_inner, inner_sum]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[hU a b, hU b a]`. Unfold `adjSign`. Distinguish the cases in `h : ε a = ε b`.

Simplify using `[h]`. Simplify using `[h, Ne.symm h]`.
-/
theorem cf_inner_casimir {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ M} (hU : IsInfUnitary ε E) (x y : M) :
    inner ℂ (casimir E x) y = inner ℂ x (casimir E y) := by
  simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hU a b, hU b a]
  unfold adjSign
  by_cases h : ε a = ε b
  · simp [h]
  · simp [h, Ne.symm h]

/- English proof (translation)
Break down `hpq with h | h` into its components or cases. Unfold `pOf at h`. Rewrite `h` using `[Finset.card_eq_zero, Finset.filter_eq_empty_iff]`. Establish `ha` using `h (Finset.mem_univ a)`. Establish `hb` using `h (Finset.mem_univ b)`.

Use `clear h`. Apply the tactic sequence `cases h1 : ε a <;> cases h2 : ε b <;> simp_all`. Unfold `qOf at h`. Rewrite `h` using `[Finset.card_eq_zero, Finset.filter_eq_empty_iff]`. Establish `ha` using `h (Finset.mem_univ a)`.

Establish `hb` using `h (Finset.mem_univ b)`. Use `clear h`. Apply the tactic sequence `cases h1 : ε a <;> cases h2 : ε b <;> simp_all`.
-/
theorem cf_eps_eq_of_pq {ε : Fin n → Bool} (hpq : pOf ε = 0 ∨ qOf ε = 0) (a b : Fin n) : ε a = ε b := by
  rcases hpq with h | h
  · unfold pOf at h
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
    have ha := h (Finset.mem_univ a)
    have hb := h (Finset.mem_univ b)
    clear h
    cases h1 : ε a <;> cases h2 : ε b <;> simp_all
  · unfold qOf at h
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
    have ha := h (Finset.mem_univ a)
    have hb := h (Finset.mem_univ b)
    clear h
    cases h1 : ε a <;> cases h2 : ε b <;> simp_all

/- English proof (translation)
Use `⟨hmono, 2, fun a b hab => absurd (cf_eps_eq_of_pq hpq a b) hab, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rcases hpq with h | h <;> rw [h] <;> norm_num`.
-/
theorem cf_stdGap_of_pq {ε : Fin n → Bool} {lam : Fin n → ℝ} (hpq : pOf ε = 0 ∨ qOf ε = 0)
    (hmono : StrictAnti lam) : StdGap ε lam := by
  refine ⟨hmono, 2, fun a b hab => absurd (cf_eps_eq_of_pq hpq a b) hab, ?_⟩
  rcases hpq with h | h <;> rw [h] <;> norm_num

/- English proof (translation)
Establish `h1 : gᴴ * g = 1` using `Matrix.mem_unitaryGroup_iff'.1 hg.1`. Use `show gᴴ * Jm ε * g = Jm ε`. Rewrite using `[Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]`.
-/
theorem cf_kset_sub {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) : g ∈ UJset ε := by
  have h1 : gᴴ * g = 1 := Matrix.mem_unitaryGroup_iff'.1 hg.1
  show gᴴ * Jm ε * g = Jm ε
  rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]

section Datum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}

/- English proof (translation)
Introduce `a b hab hne w hw hkhw`. Assume the negation of the conclusion as `hw0`. Establish `hE` using `hD.glRep`. Establish `hU` using `isInfUnitary_of_isDerivedOn hσ hD`. Establish `hSf : FiniteDimensional ℂ (layer ε E V 1)` using `finiteDimensional_layer hV.1 1`.

Establish `hSk : IsKStableSub ε E (layer ε E V 1)` using `layer_kStable hE hV.2.1 1`. Take `⟨S', -, -, hS'⟩` from `exists_irr_sub_of_khw hE hU _ hSf hSk hw hw0 hkhw`. Establish `hK'` using `kStable_of_isKStableSub hσ hD S' hS'.1 hS'.2.1`. Establish `hKT` using `isKTypeOf_of_isKIrrHW hσ hD hS' hK' (fun μ x hx hx0 hμ => weights_le_of_irr_hw hE hU hS' hx hx0 hμ)`. Establish `h1` using `hvog _ _ hKT`.

Establish `h2` using `vNormSq_lowK_sub_root_lt hgap.1 hab hne`. Rewrite `h1`, `h2` using `[mir_lowK_eq]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cfa_no_of_vogan (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hvog : ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), Formalism.MainNotions.S.IsKTypeOf ε σ μ S →
      Formalism.MainNotions.S.vNormSq ε (Formalism.QuantumDeterminants.lowK ε lam) ≤ Formalism.MainNotions.S.vNormSq ε μ) :
    ∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ w ∈ layer ε E V 1,
      IsKHWVec ε E (lowK ε lam - root a b) w → w = 0 := by
  intro a b hab hne w hw hkhw
  by_contra hw0
  have hE := hD.glRep
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  have hSf : FiniteDimensional ℂ (layer ε E V 1) := finiteDimensional_layer hV.1 1
  have hSk : IsKStableSub ε E (layer ε E V 1) := layer_kStable hE hV.2.1 1
  obtain ⟨S', -, -, hS'⟩ := exists_irr_sub_of_khw hE hU _ hSf hSk hw hw0 hkhw
  have hK' := kStable_of_isKStableSub hσ hD S' hS'.1 hS'.2.1
  have hKT := isKTypeOf_of_isKIrrHW hσ hD hS' hK'
    (fun μ x hx hx0 hμ => weights_le_of_irr_hw hE hU hS' hx hx0 hμ)
  have h1 := hvog _ _ hKT
  have h2 := vNormSq_lowK_sub_root_lt hgap.1 hab hne
  rw [mir_lowK_eq] at h1 h2
  linarith

end Datum

section Arbitrary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

variable (ε lam) in

def CasOnCopies (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ V : Submodule ℂ (smD ε σ), IsKIrrHW ε (smE ε σ) (lowK ε lam) V →
    (∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) →
    ∀ v ∈ V, casimir (smE ε σ) v = (casVal lam : ℂ) • v

/- English proof (translation)
Establish `hσ : IsURepOn (UJset ε) σ` using `hDS.2.2.1`. Take `⟨S, hS⟩` from `hDS.2.2.2.2.2.1`. Take `⟨V, hV, hV0, hVK, -⟩` from `exists_datum_of_isKTypeOf hσ hS`. Establish `hV' : IsKIrrHW ε (smE ε σ) (lowK ε lam) V` using `hV`. Establish `hD` using `isDerivedOn_smE hσ`.

Establish `hc` using `hcV V hV' hVK`. Conclude with `⟨V, hV', hV0, hVK, hc, data_closGen_eq_top hgap hσ hD hV' hc hVK hDS.2.2.2.1 hV0⟩`.
-/
theorem cf_datum_of_copies (hDS : Formalism.MainNotions.S.IsDS ε lam σ) (hgap : StdGap ε lam) (hcV : CasOnCopies ε lam σ) :
    ∃ V : Submodule ℂ (smD ε σ), IsKIrrHW ε (smE ε σ) (lowK ε lam) V ∧ V ≠ ⊥ ∧
      (∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) ∧
      (∀ v ∈ V, casimir (smE ε σ) v = (casVal lam : ℂ) • v) ∧ closGen (smE ε σ) V = ⊤ := by
  have hσ : IsURepOn (UJset ε) σ := hDS.2.2.1
  obtain ⟨S, hS⟩ := hDS.2.2.2.2.2.1
  obtain ⟨V, hV, hV0, hVK, -⟩ := exists_datum_of_isKTypeOf hσ hS
  have hV' : IsKIrrHW ε (smE ε σ) (lowK ε lam) V := hV
  have hD := isDerivedOn_smE hσ
  have hc := hcV V hV' hVK
  exact ⟨V, hV', hV0, hVK, hc, data_closGen_eq_top hgap hσ hD hV' hc hVK hDS.2.2.2.1 hV0⟩

/- English proof (translation)
Establish `htop` using `data_closGen_eq_top hgap hσ (isDerivedOn_smE hσ) hV hc hVK hirr hV0`. Establish `hD` using `isDerivedOn_smE hσ`. Establish `hU` using `isInfUnitary_of_isDerivedOn hσ hD`. Introduce `v hv`. Set `v' : smD ε σ` to `⟨v, (mem_smD_iff ε σ v).2 hv⟩`.

Establish `hvv : (v' : H) = v` using `rfl`. Rewrite using `[← hvv, casU_eq_casimir hD v', ← sub_eq_zero]`. Establish `hperp : ((casimir (smE ε σ) v' : smD ε σ) : H) - ((casVal lam : ℝ) : ℂ) • (v' : H) ∈ ((genSub (smE ε σ) V).map (smD ε σ).subtype)ᗮ`. Rewrite using `[Submodule.mem_orthogonal]`. Introduce `u hu`.

Take `⟨x, hx, rfl⟩` from `Submodule.mem_map.1 hu`. Establish `hcx : ((casimir (smE ε σ) x : smD ε σ) : H) = ((casVal lam : ℝ) : ℂ) • (x : H)`. Rewrite using `[← casU_eq_casimir hD x]`. Conclude with `data_casU hgap hσ hD hV hc hVK x hx`. Establish `hsym` using `cf_inner_casimir hU x v'`.

Rewrite `hsym` using `[Submodule.coe_inner, Submodule.coe_inner, hcx]`. Rewrite using `[Submodule.subtype_apply, inner_sub_right, ← hsym, inner_smul_left, inner_smul_right, Complex.conj_ofReal, sub_self]`. Establish `htop' : ((genSub (smE ε σ) V).map (smD ε σ).subtype).topologicalClosure = ⊤` using `htop`. Rewrite `hperp` using `[Submodule.topologicalClosure_eq_top_iff.1 htop']`. Conclude with `(Submodule.mem_bot ℂ).1 hperp`.
-/
theorem casOnSmooth_of_datum (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (UJset ε) σ) {V : Submodule ℂ (smD ε σ)}
    (hV : IsKIrrHW ε (smE ε σ) (lowK ε lam) V) (hV0 : V ≠ ⊥)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hc : ∀ v ∈ V, casimir (smE ε σ) v = (casVal lam : ℂ) • v) : CasOnSmooth ε lam σ := by
  have htop := data_closGen_eq_top hgap hσ (isDerivedOn_smE hσ) hV hc hVK hirr hV0
  have hD := isDerivedOn_smE hσ
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  intro v hv
  let v' : smD ε σ := ⟨v, (mem_smD_iff ε σ v).2 hv⟩
  have hvv : (v' : H) = v := rfl
  rw [← hvv, casU_eq_casimir hD v', ← sub_eq_zero]
  have hperp : ((casimir (smE ε σ) v' : smD ε σ) : H) - ((casVal lam : ℝ) : ℂ) • (v' : H) ∈
      ((genSub (smE ε σ) V).map (smD ε σ).subtype)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hu
    have hcx : ((casimir (smE ε σ) x : smD ε σ) : H) = ((casVal lam : ℝ) : ℂ) • (x : H) := by
      rw [← casU_eq_casimir hD x]
      exact data_casU hgap hσ hD hV hc hVK x hx
    have hsym := cf_inner_casimir hU x v'
    rw [Submodule.coe_inner, Submodule.coe_inner, hcx] at hsym
    rw [Submodule.subtype_apply, inner_sub_right, ← hsym, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal, sub_self]
  have htop' : ((genSub (smE ε σ) V).map (smD ε σ).subtype).topologicalClosure = ⊤ := htop
  rw [Submodule.topologicalClosure_eq_top_iff.1 htop'] at hperp
  exact (Submodule.mem_bot ℂ).1 hperp

/- English proof (translation)
Take `⟨V, hV, hV0, hVK, hc, -⟩` from `cf_datum_of_copies hDS hgap hcV`. Conclude with `casOnSmooth_of_datum hgap hDS.2.2.1 hDS.2.2.2.1 hV hV0 hVK hc`.
-/
theorem casOnSmooth_of_copies (hDS : Formalism.MainNotions.S.IsDS ε lam σ) (hgap : StdGap ε lam) (hcV : CasOnCopies ε lam σ) :
    CasOnSmooth ε lam σ := by
  obtain ⟨V, hV, hV0, hVK, hc, -⟩ := cf_datum_of_copies hDS hgap hcV
  exact casOnSmooth_of_datum hgap hDS.2.2.1 hDS.2.2.2.1 hV hV0 hVK hc

/- English proof (translation)
Establish `hgap` using `cf_stdGap_of_pq hpq (lam := lam) hlam.1`. Take `⟨σ₀, hDS₀, hcas₀, hσ₀K⟩` from `isDS_compact hpq hlam T`. Take `⟨U, hU⟩` from `dsUnique_of_cas hgap hDS₀ hcas₀ hDS hcas`. Establish `hUK : ∀ (k : S7.KG ε) (v : T.V), U (T.op k v) = σ (S7.toMK k) (U v)`. Introduce `k v`.

Rewrite using `[← hσ₀K k]`. Conclude with `hU _ (cf_kset_sub (S7.toMK_mem ε k)) v`. Use `⟨fun S hS => ?_, U, hUK⟩` and prove the remaining obligations. Take `⟨-, hSK, -, ⟨v, hvS, hv0, -⟩, -⟩` from `hS`. Set `W : Submodule ℂ T.V` to `S.comap (U.toLinearEquiv : T.V →ₗ[ℂ] H)`.

Establish `hmemW : ∀ x : T.V, x ∈ W ↔ U x ∈ S` using `fun x => Iff.rfl`. Establish `hW : ∀ k : S7.KG ε, ∀ x ∈ W, ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) x ∈ W`. Introduce `k x hx`. Rewrite `hx`, the goal using `[hmemW]`. Establish `h` using `hUK k x`.

Simplify using `only [S7.KType.op] at h`. Rewrite using `[h]`. Conclude with `hSK _ (S7.toMK_mem ε k) _ hx`. Break down `T.irred W hW with h | h` into its components or cases. It suffices to derive a contradiction.

Apply `hv0` to reduce the goal to its premises. Establish `hvW : U.symm v ∈ W`. Rewrite using `[hmemW, LinearIsometryEquiv.apply_symm_apply]`. Conclude with `hvS`. Rewrite `hvW` using `[h, Submodule.mem_bot]`.

Use `congrArg U hvW` as an intermediate fact. Rewrite `this` using `[LinearIsometryEquiv.apply_symm_apply, map_zero]`. Then use the resulting hypothesis. Use `eq_top_iff.2 fun y _ => ?_` and prove the remaining obligations. Establish `hyW : U.symm y ∈ W` using `by rw [h]; exact Submodule.mem_top`. Rewrite `hyW` using `[hmemW, LinearIsometryEquiv.apply_symm_apply]`.

Conclude with `hyW`.
-/
theorem compact_isDS_unique_of_cas (hpq : pOf ε = 0 ∨ qOf ε = 0) (hlam : S7.IsHCParam lam)
    (hDS : Formalism.MainNotions.S.IsDS ε lam σ) (hcas : CasOnSmooth ε lam σ) (T : S7.KType ε (lowK ε lam)) :
    (∀ S : Submodule ℂ H, Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S → S = ⊤) ∧
      ∃ U : T.V ≃ₗᵢ[ℂ] H, ∀ k : S7.KG ε, ∀ v : T.V, U (T.op k v) = σ (S7.toMK k) (U v) := by
  have hgap := cf_stdGap_of_pq hpq (lam := lam) hlam.1
  obtain ⟨σ₀, hDS₀, hcas₀, hσ₀K⟩ := isDS_compact hpq hlam T
  obtain ⟨U, hU⟩ := dsUnique_of_cas hgap hDS₀ hcas₀ hDS hcas
  have hUK : ∀ (k : S7.KG ε) (v : T.V), U (T.op k v) = σ (S7.toMK k) (U v) := by
    intro k v
    rw [← hσ₀K k]
    exact hU _ (cf_kset_sub (S7.toMK_mem ε k)) v
  refine ⟨fun S hS => ?_, U, hUK⟩
  obtain ⟨-, hSK, -, ⟨v, hvS, hv0, -⟩, -⟩ := hS
  let W : Submodule ℂ T.V := S.comap (U.toLinearEquiv : T.V →ₗ[ℂ] H)
  have hmemW : ∀ x : T.V, x ∈ W ↔ U x ∈ S := fun x => Iff.rfl
  have hW : ∀ k : S7.KG ε, ∀ x ∈ W, ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) x ∈ W := by
    intro k x hx
    rw [hmemW] at hx ⊢
    have h := hUK k x
    simp only [S7.KType.op] at h
    rw [h]
    exact hSK _ (S7.toMK_mem ε k) _ hx
  rcases T.irred W hW with h | h
  · exfalso
    apply hv0
    have hvW : U.symm v ∈ W := by
      rw [hmemW, LinearIsometryEquiv.apply_symm_apply]; exact hvS
    rw [h, Submodule.mem_bot] at hvW
    have := congrArg U hvW
    rwa [LinearIsometryEquiv.apply_symm_apply, map_zero] at this
  · refine eq_top_iff.2 fun y _ => ?_
    have hyW : U.symm y ∈ W := by rw [h]; exact Submodule.mem_top
    rw [hmemW, LinearIsometryEquiv.apply_symm_apply] at hyW
    exact hyW

end Arbitrary

/- English proof (translation)
Establish `hgap : StdGap ε lam` using `⟨hlam.1, h, hh, hbig⟩`. Establish `hcas` using `casOnSmooth_of_copies hDS hgap (hall H σ hDS)`. Establish `hσ : IsURepOn (UJset ε) σ` using `hDS.2.2.1`. Take `⟨V, hV, -, hVK, hc, htop⟩` from `cf_datum_of_copies hDS hgap (hall H σ hDS)`. Establish `hD` using `isDerivedOn_smE hσ`.

Use `⟨hcas, fun S S' hS hS' => lowKMultOne_of_cas hDS hgap hcas S S' hS hS', fun μ => ?_, fun S hSf hSK v hv => ?_, fun H' _ _ _ σ' hDS' => ?_⟩` and prove the remaining obligations. Establish `hadm` using `data_admissible hgap hσ hD hV hc hVK μ`. Rewrite `hadm` using `[htop]`. Establish `hset : {S : Submodule ℂ H | S ≤ ⊤ ∧ Formalism.MainNotions.S.IsKTypeOf ε σ μ S} = {S : Submodule ℂ H | Formalism.MainNotions.S.IsKTypeOf ε σ μ S}`. Use extensionality with `S`.

Simplify using the standard rewrite rules. Rewrite `hadm` using `[hset]`. Conclude with `hadm`. Establish `hle : S ≤ closGen (smE ε σ) V` using `by rw [htop]; exact le_top`. Establish `hmem` using `data_kfin_le hgap hσ hD hV hc hVK S hle hSf hSK hv`.

Take `⟨x, -, rfl⟩` from `Submodule.mem_map.1 hmem`. Conclude with `(mem_smD_iff ε σ _).1 x.2`. Conclude with `dsUnique_of_cas hgap hDS hcas hDS' (casOnSmooth_of_copies hDS' hgap (hall H' σ' hDS'))`.
-/
theorem isDS_props_of_copies {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Formalism.QuantumDeterminants.IsHCParam lam) {h : ℝ}
    (hh : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h)
    (hall : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ → CasOnCopies ε lam σ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hDS : Formalism.MainNotions.S.IsDS ε lam σ) :
    CasOnSmooth ε lam σ ∧
      (∀ S S' : Submodule ℂ H, Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S →
        Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S' → S = S') ∧
      (∀ μ : Fin n → ℝ, FiniteDimensional ℂ (sSup {S : Submodule ℂ H | Formalism.MainNotions.S.IsKTypeOf ε σ μ S} :
        Submodule ℂ H)) ∧
      (∀ S : Submodule ℂ H, FiniteDimensional ℂ S → Formalism.MainNotions.S.IsKStableOn ε σ S →
        ∀ v ∈ S, IsSmoothVecU ε σ v) ∧
      ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
        (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDS ε lam σ' →
        ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ x : H, U (σ g x) = σ' g (U x) := by
  have hgap : StdGap ε lam := ⟨hlam.1, h, hh, hbig⟩
  have hcas := casOnSmooth_of_copies hDS hgap (hall H σ hDS)
  have hσ : IsURepOn (UJset ε) σ := hDS.2.2.1
  obtain ⟨V, hV, -, hVK, hc, htop⟩ := cf_datum_of_copies hDS hgap (hall H σ hDS)
  have hD := isDerivedOn_smE hσ
  refine ⟨hcas, fun S S' hS hS' => lowKMultOne_of_cas hDS hgap hcas S S' hS hS', fun μ => ?_,
    fun S hSf hSK v hv => ?_, fun H' _ _ _ σ' hDS' => ?_⟩
  · have hadm := data_admissible hgap hσ hD hV hc hVK μ
    rw [htop] at hadm
    have hset : {S : Submodule ℂ H | S ≤ ⊤ ∧ Formalism.MainNotions.S.IsKTypeOf ε σ μ S} =
        {S : Submodule ℂ H | Formalism.MainNotions.S.IsKTypeOf ε σ μ S} := by
      ext S
      simp
    rw [hset] at hadm
    exact hadm
  · have hle : S ≤ closGen (smE ε σ) V := by rw [htop]; exact le_top
    have hmem := data_kfin_le hgap hσ hD hV hc hVK S hle hSf hSK hv
    obtain ⟨x, -, rfl⟩ := Submodule.mem_map.1 hmem
    exact (mem_smD_iff ε σ _).1 x.2
  · exact dsUnique_of_cas hgap hDS hcas hDS' (casOnSmooth_of_copies hDS' hgap (hall H' σ' hDS'))

end ReciprocityTheory.ChartRestriction.DS
