import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.ContinuousHRRight

noncomputable section

namespace LocMassOrdSC

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol MeasureTheory
  NumberField IsDedekindDomain LocMassOrdW
open scoped TensorProduct Classical

def MeasConjK : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (P : Frame E n r) (Λ : Set (Fin n → E))
    (μG : Measure (HA (Fv F v) σ J)) (μS : Measure (Ssub (Fv F v) σ J P))
    (μS0 : Measure (S0 (Fv F v) σ J P)) (y : HA (Fv F v) σ J),
    FrameHyp σ J ψ v P Λ μG μS μS0 y →
    MeasurableSet {g : HA (Fv F v) σ J | y * g * y⁻¹ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v}

def MeasUO : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (r : ℕ), MeasurableSet (UO (E := E) v r)

def UnipExists : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (P : Frame E n r) (Λ : Set (Fin n → E))
    (μG : Measure (HA (Fv F v) σ J)) (μS : Measure (Ssub (Fv F v) σ J P))
    (μS0 : Measure (S0 (Fv F v) σ J P)) (y : HA (Fv F v) σ J),
    FrameHyp σ J ψ v P Λ μG μS μS0 y → ∀ x : UIdx r → Fv F v ⊗[F] E,
    ∃ g : HA (Fv F v) σ J, ∀ b, lin (Fv F v) σ J g (ratV (F := F) (Fv F v) (F0 P b)) =
      ∑ a, uMat v x a b • ratV (F := F) (Fv F v) (F0 P a)

def KUnip : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (P : Frame E n r) (Λ : Set (Fin n → E))
    (μG : Measure (HA (Fv F v) σ J)) (μS : Measure (Ssub (Fv F v) σ J P))
    (μS0 : Measure (S0 (Fv F v) σ J P)) (y : HA (Fv F v) σ J),
    FrameHyp σ J ψ v P Λ μG μS μS0 y → ∀ x ∈ UO (E := E) v r,
    ∃ g : HA (Fv F v) σ J, (∀ b, lin (Fv F v) σ J g (ratV (F := F) (Fv F v) (F0 P b)) =
      ∑ a, uMat v x a b • ratV (F := F) (Fv F v) (F0 P a)) ∧
      y * g * y⁻¹ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v

section Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kvc_mul {a b : HA (Fv F v) σ J} (ha : a ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v)
    (hb : b ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v) : a * b ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v :=
  (Kloc (E := E) v Λ).mul_mem ha hb

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kvc_inv {a : HA (Fv F v) σ J} (ha : a ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v) :
    a⁻¹ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v :=
  (Kloc (E := E) v Λ).inv_mem ha

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kvc_mem_lat {k : HA (Fv F v) σ J} (hk : k ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v)
    {z : Fin n → Fv F v ⊗[F] E} (hz : z ∈ latLoc (E := E) v Λ) :
    lin (Fv F v) σ J k z ∈ latLoc (E := E) v Λ :=
  (hk z).1 hz

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem sc_mul (a b : Fv F v) : sc (E := E) v a * sc (E := E) v b = sc (E := E) v (a * b) := by
  simp [sc, Algebra.TensorProduct.tmul_mul_tmul]

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem dV_ne : dV v ≠ 0 := by
  unfold dV
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_ne_zero

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem alp_ne (r : ℕ) (a : Fin (r + 1)) : alp v r a ≠ 0 := by
  unfold alp
  split_ifs
  · exact pow_ne_zero _ (inv_ne_zero (dV_ne v))
  · exact one_ne_zero

end Alg

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
  (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (P : Frame E n r) (Λ : Set (Fin n → E))

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Introduce a local definition for the expression.

Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Clear the denominators using the available nonvanishing facts. Chain the equalities or inequalities of the calculation. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem uo_of_mem {y : HA (Fv F v) σ J}
    (hy : IsPrim v Λ (locF v (y • ratTup (Fv F v) (F0 P))))
    (s0 : S0 (Fv F v) σ J P) (g : HA (Fv F v) σ J) (x : UIdx r → Fv F v ⊗[F] E)
    (hg : ∀ b, lin (Fv F v) σ J g (ratV (F := F) (Fv F v) (F0 P b)) =
      ∑ a, uMat v x a b • ratV (F := F) (Fv F v) (F0 P a))
    (hk : y * ((s0 : HA (Fv F v) σ J) * g) * y⁻¹ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v) :
    x ∈ UO (E := E) v r := by
  set X : TupV (E := E) v n (r + 1) := y • ratTup (Fv F v) (F0 P) with hX
  have hXa : ∀ a, X a = lin (Fv F v) σ J y (ratV (F := F) (Fv F v) (F0 P a)) := fun a => rfl
  have hs0 : ∀ a, lin (Fv F v) σ J (s0 : HA (Fv F v) σ J) (ratV (F := F) (Fv F v) (F0 P a)) =
      ratV (F := F) (Fv F v) (F0 P a) := fun a =>
    congrFun (s0.2 : (s0 : HA (Fv F v) σ J) • ratTup (Fv F v) (F0 P) = ratTup (Fv F v) (F0 P)) a
  have hkX : ∀ b, lin (Fv F v) σ J (y * ((s0 : HA (Fv F v) σ J) * g) * y⁻¹) (X b) =
      ∑ a, uMat v x a b • X a := by
    intro b
    rw [hXa, lin_mul, lin_inv_lin, lin_mul, lin_mul, hg, map_sum, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, hs0, map_smul, hXa]
  intro p
  obtain ⟨⟨a, b⟩, hab⟩ := p
  let c : Fin (r + 1) → Fv F v ⊗[F] E := fun a =>
    sc (E := E) v ((alp v r a)⁻¹ * alp v r b) * uMat v x a b
  have key : ∑ a, c a • locF v X a =
      lin (Fv F v) σ J (y * ((s0 : HA (Fv F v) σ J) * g) * y⁻¹) (locF v X b) := by
    simp only [locF, map_smul, hkX, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    have e1 : sc (E := E) v ((alp v r a)⁻¹ * alp v r b) * sc (E := E) v (alp v r a) =
        sc (E := E) v (alp v r b) := by
      rw [sc_mul]
      congr 1
      field_simp [alp_ne v r a]
    calc c a * sc (E := E) v (alp v r a)
        = uMat v x a b * (sc (E := E) v ((alp v r a)⁻¹ * alp v r b) *
            sc (E := E) v (alp v r a)) := by simp only [c]; ring
      _ = sc (E := E) v (alp v r b) * uMat v x a b := by rw [e1, mul_comm]
  have hmem : ∑ a, c a • locF v X a ∈ latLoc (E := E) v Λ := by
    rw [key]
    exact kvc_mem_lat σ J v Λ hk (hy.1 b)
  have := hy.2 c hmem a
  simp only [c, uMat, if_neg hab.ne, dif_pos hab] at this
  exact this

end Main

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Apply an available result and prove the equalities needed to match it to the conclusion.

Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem stepC_at {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (P : Frame E n r) (Λ : Set (Fin n → E))
    (μG : Measure (HA (Fv F v) σ J)) (μS : Measure (Ssub (Fv F v) σ J P))
    (μS0 : Measure (S0 (Fv F v) σ J P)) (y : HA (Fv F v) σ J)
    (h : FrameHyp σ J ψ v P Λ μG μS μS0 y)
    (hC0 : MeasurableSet {g : HA (Fv F v) σ J | y * g * y⁻¹ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v})
    (hU0 : MeasurableSet (UO (E := E) v r))
    (hE0 : ∀ x : UIdx r → Fv F v ⊗[F] E, ∃ g : HA (Fv F v) σ J,
      ∀ b, lin (Fv F v) σ J g (ratV (F := F) (Fv F v) (F0 P b)) =
        ∑ a, uMat v x a b • ratV (F := F) (Fv F v) (F0 P a))
    (hK0 : ∀ x ∈ UO (E := E) v r, ∃ g : HA (Fv F v) σ J,
      (∀ b, lin (Fv F v) σ J g (ratV (F := F) (Fv F v) (F0 P b)) =
        ∑ a, uMat v x a b • ratV (F := F) (Fv F v) (F0 P a)) ∧
      y * g * y⁻¹ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v) :
    μS (KSvT σ J v P Λ y) = μS0 (stabilizerConjugateCompact σ J v P Λ y) * sdE (E := E) ψ v (UIdx r) (UO v r) := by
  obtain ⟨_, _, _, _, _, _, _, _, hpu, hy⟩ := id h
  have hC := hC0
  set C := {g : HA (Fv F v) σ J | y * g * y⁻¹ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v} with hCdef
  let t : (UIdx r → Fv F v ⊗[F] E) → HA (Fv F v) σ J := fun x =>
    if hx : x ∈ UO (E := E) v r then (hK0 x hx).choose
    else (hE0 x).choose
  have ht : ∀ x b, lin (Fv F v) σ J (t x) (ratV (F := F) (Fv F v) (F0 P b)) =
      ∑ a, uMat v x a b • ratV (F := F) (Fv F v) (F0 P a) := by
    intro x b
    by_cases hx : x ∈ UO (E := E) v r
    · simp only [t, dif_pos hx]
      exact (hK0 x hx).choose_spec.1 b
    · simp only [t, dif_neg hx]
      exact (hE0 x).choose_spec b
  have htK : ∀ x ∈ UO (E := E) v r, y * t x * y⁻¹ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v := by
    intro x hx
    simp only [t, dif_pos hx]
    exact (hK0 x hx).choose_spec.2
  have hiff : ∀ x (s0 : S0 (Fv F v) σ J P), (s0 : HA (Fv F v) σ J) * t x ∈ C ↔
      x ∈ UO (E := E) v r ∧ s0 ∈ stabilizerConjugateCompact σ J v P Λ y := by
    intro x s0
    constructor
    · intro hk
      have hx := uo_of_mem σ J v P Λ hy s0 (t x) x (ht x) hk
      refine ⟨hx, ?_⟩
      have := kvc_mul σ J v Λ hk (kvc_inv σ J v Λ (htK x hx))
      change y * (s0 : HA (Fv F v) σ J) * y⁻¹ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v
      convert this using 1
      group
    · rintro ⟨hx, hs⟩
      have := kvc_mul σ J v Λ hs (htK x hx)
      rw [hCdef, Set.mem_ofPred_eq]
      convert this using 1
      group
  have hL : μS (KSvT σ J v P Λ y) = ∫⁻ g, C.indicator 1 g ∂(amb μS) := by
    rw [lintegral_indicator_one hC, Measure.map_apply measurable_subtype_coe hC]
    rfl
  rw [hL, hpu (C.indicator 1) (measurable_one.indicator hC) t ht]
  have hs0m : MeasurableSet (stabilizerConjugateCompact σ J v P Λ y) := measurable_subtype_coe hC
  have hpt : ∀ x, ∫⁻ s0, C.indicator 1 ((s0 : HA (Fv F v) σ J) * t x) ∂μS0 =
      (UO (E := E) v r).indicator 1 x * μS0 (stabilizerConjugateCompact σ J v P Λ y) := by
    intro x
    have hq : ∀ s0 : S0 (Fv F v) σ J P,
        C.indicator (1 : HA (Fv F v) σ J → ENNReal) ((s0 : HA (Fv F v) σ J) * t x) =
          (UO (E := E) v r).indicator 1 x * (stabilizerConjugateCompact σ J v P Λ y).indicator 1 s0 := by
      intro s0
      by_cases h1 : (s0 : HA (Fv F v) σ J) * t x ∈ C
      · obtain ⟨a1, a2⟩ := (hiff x s0).1 h1
        rw [Set.indicator_of_mem h1, Set.indicator_of_mem a1, Set.indicator_of_mem a2]
        simp
      · rw [Set.indicator_of_notMem h1]
        by_cases a1 : x ∈ UO (E := E) v r
        · have a2 : s0 ∉ stabilizerConjugateCompact σ J v P Λ y := fun a2 => h1 ((hiff x s0).2 ⟨a1, a2⟩)
          rw [Set.indicator_of_notMem a2, mul_zero]
        · rw [Set.indicator_of_notMem a1, zero_mul]
    simp_rw [hq]
    rw [lintegral_const_mul _ (measurable_one.indicator hs0m), lintegral_indicator_one hs0m]
  simp_rw [hpt]
  rw [lintegral_mul_const _ (measurable_one.indicator hU0), lintegral_indicator_one hU0,
    mul_comm]

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem measConj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (Λ : Set (Fin n → E)) (hSD : IsSDLoc σ J v Λ) (y : HA (Fv F v) σ J) :
    MeasurableSet {g : HA (Fv F v) σ J | y * g * y⁻¹ ∈ Formalism.L2.SG.TypedSets.Kv σ J Λ v} := by
  have hc : Continuous fun g : HA (Fv F v) σ J => y * g * y⁻¹ :=
    (continuous_const.mul continuous_id).mul continuous_const
  exact hc.measurable (LocMassOrdKv.kv_measurableSet σ J v Λ hSD)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem measurable_conjugate_compact : MeasConjK := by
  intro F E _ _ _ _ _ σ n J ψ v r P Λ μG μS μS0 y h
  exact measConj σ J v Λ h.2.2.1 y

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem measurable_unipotent_orbit : MeasUO := by
  intro F E _ _ _ _ _ v r
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have hset : UO (E := E) v r = ⋂ p : UIdx r, (fun x : UIdx r → Fv F v ⊗[F] E => x p) ⁻¹'
      ((fun z : Fv F v ⊗[F] E => sc (E := E) v ((alp v r p.1.1)⁻¹ * alp v r p.1.2) * z) ⁻¹'
        OEv (E := E) v) := by
    ext x
    simp [UO]
  rw [hset]
  refine MeasurableSet.iInter fun p => measurable_pi_apply p ?_
  exact ((LocMassOrdKv.isClosed_oev v).preimage
    (continuous_const.mul continuous_id)).measurableSet

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem stepC_of (hE : UnipExists) (hK : KUnip) : StepC := by
  intro F E _ _ _ _ _ σ n J ψ v r P Λ μG μS μS0 y h
  exact stepC_at σ J ψ v P Λ μG μS μS0 y h (measConj σ J v Λ h.2.2.1 y) (measurable_unipotent_orbit v r)
    (hE σ J ψ v P Λ μG μS μS0 y h) (hK σ J ψ v P Λ μG μS μS0 y h)

end LocMassOrdSC
