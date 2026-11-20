import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.UnitaryLocalMassIdentity
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.ContinuousHRRight

noncomputable section

namespace PI.LocMassTypM

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol MeasureTheory NumberField IsDedekindDomain
  Topology Filter
open scoped TensorProduct
open PI.LocMassTypW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Inst

variable (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
The claim follows from `inferInstance`.
-/
theorem t2Space_fv : T2Space (Fv F v) := inferInstance

/- English proof (translation)
Use `haveI := t2Space_fv (F := F) v`. Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Conclude with `LocMassOrdSF.t2_tensor_product (F := F) (E := E) (R := Fv F v)`.
-/
theorem t2Space_fv_tensorProduct : T2Space (Fv F v ⊗[F] E) := by
  haveI := t2Space_fv (F := F) v
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact LocMassOrdSF.t2_tensor_product (F := F) (E := E) (R := Fv F v)

/- English proof (translation)
Use `haveI := LocMassOrdSF.secondCountable_Fv (F := F) (v := v)`. Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Conclude with `LocMassOrdSF.sc_tens (F := F) (E := E) (R := Fv F v)`.
-/
theorem sc_tensV : SecondCountableTopology (Fv F v ⊗[F] E) := by
  haveI := LocMassOrdSF.secondCountable_Fv (F := F) (v := v)
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact LocMassOrdSF.sc_tens (F := F) (E := E) (R := Fv F v)

/- English proof (translation)
Use `haveI := t2Space_fv (F := F) v`. Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI := LocMassOrdSF.locallyCompact_Fv (F := F) (v := v)`. Conclude with `LocMassOrdSF.lc_tens (F := F) (E := E) (R := Fv F v)`.
-/
theorem lc_tensV : LocallyCompactSpace (Fv F v ⊗[F] E) := by
  haveI := t2Space_fv (F := F) v
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := LocMassOrdSF.locallyCompact_Fv (F := F) (v := v)
  exact LocMassOrdSF.lc_tens (F := F) (E := E) (R := Fv F v)

/- English proof (translation)
Assemble the required witnesses or components as `⟨rfl⟩`.
-/
theorem borel_tensV : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩

end Inst

attribute [local instance] t2Space_fv_tensorProduct sc_tensV lc_tensV borel_tensV

section HATop

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI := LocMassOrdSF.isModTop_tens (F := F) (E := E) (R := Fv F v)`. Set `f : (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fv F v ⊗[F] E)` to `TensorProduct.AlgebraTensorModule.map LinearMap.id σ.toLinearMap`. Establish `hf : Continuous f` using `IsModuleTopology.continuous_of_linearMap f`. Establish `heq : (sigR (Fv F v) σ : Fv F v ⊗[F] E → Fv F v ⊗[F] E) = f`.

Use function extensionality and compare the values at `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [f, sigR]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.

Rewrite using `[heq]`. Conclude with `hf`.
-/
theorem continuous_sigR : Continuous (sigR (Fv F v) σ) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := LocMassOrdSF.isModTop_tens (F := F) (E := E) (R := Fv F v)
  let f : (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fv F v ⊗[F] E) :=
    TensorProduct.AlgebraTensorModule.map LinearMap.id σ.toLinearMap
  have hf : Continuous f := IsModuleTopology.continuous_of_linearMap f
  have heq : (sigR (Fv F v) σ : Fv F v ⊗[F] E → Fv F v ⊗[F] E) = f := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [f, sigR]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [heq]
  exact hf

/- English proof (translation)
Establish `hv : Continuous fun g : GL (Fin n) (Fv F v ⊗[F] E) => (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))` using `Units.continuous_val`. Establish `hm : Continuous fun g : GL (Fin n) (Fv F v ⊗[F] E) => Formalism.UG.cT (sigR (Fv F v) σ) (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))`. Unfold `Formalism.UG.cT`. Conclude with `(hv.matrix_map (continuous_sigR σ v)).matrix_transpose`. Conclude with `isClosed_eq ((hm.matrix_mul continuous_const).matrix_mul hv) continuous_const`.
-/
theorem isClosed_HR : IsClosed (HR (Fv F v) σ J : Set (GL (Fin n) (Fv F v ⊗[F] E))) := by
  have hv : Continuous fun g : GL (Fin n) (Fv F v ⊗[F] E) => (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :=
    Units.continuous_val
  have hm : Continuous fun g : GL (Fin n) (Fv F v ⊗[F] E) =>
      Formalism.UG.cT (sigR (Fv F v) σ) (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) := by
    unfold Formalism.UG.cT
    exact (hv.matrix_map (continuous_sigR σ v)).matrix_transpose
  exact isClosed_eq ((hm.matrix_mul continuous_const).matrix_mul hv) continuous_const

/- English proof (translation)
Use `haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) := (inferInstance : LocallyCompactSpace (Fin n → Fin n → Fv F v ⊗[F] E))`. Use `haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))ᵐᵒᵖ := (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))).symm.isClosedEmbedding.locallyCompactSpace`. Use `haveI : LocallyCompactSpace (GL (Fin n) (Fv F v ⊗[F] E)) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace`. Conclude with `(isClosed_HR σ J v).isClosedEmbedding_subtypeVal.locallyCompactSpace`.
-/
theorem lc_HA : LocallyCompactSpace (HA (Fv F v) σ J) := by
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :=
    (inferInstance : LocallyCompactSpace (Fin n → Fin n → Fv F v ⊗[F] E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))).symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (GL (Fin n) (Fv F v ⊗[F] E)) :=
    Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  exact (isClosed_HR σ J v).isClosedEmbedding_subtypeVal.locallyCompactSpace

/- English proof (translation)
Use `haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) := (inferInstance : SecondCountableTopology (Fin n → Fin n → Fv F v ⊗[F] E))`. Use `haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))ᵐᵒᵖ := (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))).symm.isInducing.secondCountableTopology`. Use `haveI : SecondCountableTopology (GL (Fin n) (Fv F v ⊗[F] E)) := Units.isEmbedding_embedProduct.isInducing.secondCountableTopology`. Conclude with `(isClosed_HR σ J v).isClosedEmbedding_subtypeVal.isInducing.secondCountableTopology`.
-/
theorem sc_HA : SecondCountableTopology (HA (Fv F v) σ J) := by
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :=
    (inferInstance : SecondCountableTopology (Fin n → Fin n → Fv F v ⊗[F] E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))).symm.isInducing.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin n) (Fv F v ⊗[F] E)) :=
    Units.isEmbedding_embedProduct.isInducing.secondCountableTopology
  exact (isClosed_HR σ J v).isClosedEmbedding_subtypeVal.isInducing.secondCountableTopology

/- English proof (translation)
Use `continuous_pi fun i => ?_` and prove the remaining obligations. Conclude with `LocMassOrdKv.continuous_act (σ := σ) (J := J) (v := v) (X i)`.
-/
theorem continuous_smulTup {a : ℕ} (X : TupV (E := E) v n a) :
    Continuous (fun c : HA (Fv F v) σ J => c • X) := by
  refine continuous_pi fun i => ?_
  exact LocMassOrdKv.continuous_act (σ := σ) (J := J) (v := v) (X i)

/- English proof (translation)
Use `haveI := lc_HA σ J v`. Use `haveI := sc_HA σ J v`. Take `⟨K, hK, hKU⟩` from `IsSigmaCompact.image (continuous_smulTup σ J v X) (isSigmaCompact_univ.of_isClosed_subset hC (Set.subset_univ _))`. Rewrite using `[← hKU]`. Conclude with `MeasurableSet.iUnion fun i => (hK i).measurableSet`.
-/
theorem measurableSet_image_closed {a : ℕ} {C : Set (HA (Fv F v) σ J)} (hC : IsClosed C)
    (X : TupV (E := E) v n a) : MeasurableSet ((fun c : HA (Fv F v) σ J => c • X) '' C) := by
  haveI := lc_HA σ J v
  haveI := sc_HA σ J v
  obtain ⟨K, hK, hKU⟩ := IsSigmaCompact.image (continuous_smulTup σ J v X)
    (isSigmaCompact_univ.of_isClosed_subset hC (Set.subset_univ _))
  rw [← hKU]
  exact MeasurableSet.iUnion fun i => (hK i).measurableSet

end HATop

section Lat

variable {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sc_one : sc (E := E) v 1 = 1 := rfl

/- English proof (translation)
Establish `h1 : sc (E` using `E) v x⁻¹ * sc (E := E) v x = 1 := by`. Unfold `sc`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ hx, one_mul]`. Both sides reduce to the same expression. Establish `h2 : sc (E` using `E) v x * sc (E := E) v x⁻¹ = 1 := by`.

Rewrite using `[mul_comm, h1]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Rewrite using `[smul_smul, h1, one_smul]` and apply the resulting hypothesis. Introduce `hw`.

Conclude with `⟨_, hw, by rw [smul_smul, h2, one_smul]⟩`.
-/
theorem mem_gLat_iff {x : Fv F v} (hx : x ≠ 0) (w : Fin n → Fv F v ⊗[F] E) :
    (∃ y ∈ latLoc (E := E) v Λ, w = sc (E := E) v x • y) ↔
      sc (E := E) v x⁻¹ • w ∈ latLoc (E := E) v Λ := by
  have h1 : sc (E := E) v x⁻¹ * sc (E := E) v x = 1 := by
    unfold sc
    rw [Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ hx, one_mul]
    rfl
  have h2 : sc (E := E) v x * sc (E := E) v x⁻¹ = 1 := by
    rw [mul_comm, h1]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [smul_smul, h1, one_smul]
  · intro hw
    exact ⟨_, hw, by rw [smul_smul, h2, one_smul]⟩

/- English proof (translation)
Unfold `locF`. Conclude with `(continuous_const : Continuous fun _ : TupV (E := E) v n (r + 1) => sc (E := E) v (alp v r a)).smul (continuous_apply a : Continuous fun X : TupV (E := E) v n (r + 1) => X a)`.
-/
theorem continuous_locF {r : ℕ} (a : Fin (r + 1)) :
    Continuous (fun X : TupV (E := E) v n (r + 1) => locF v X a) := by
  unfold locF
  exact (continuous_const : Continuous fun _ : TupV (E := E) v n (r + 1) => sc (E := E) v (alp v r a)).smul
    (continuous_apply a : Continuous fun X : TupV (E := E) v n (r + 1) => X a)

/- English proof (translation)
Establish `h` using `IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (g : 𝓞 F)`. Establish `h2` using `(IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (g : 𝓞 F)).mpr hgv`. Rewrite `h2` using `[← h]`. Use `h2 using 2` and compare the differences between its conclusion and the goal. Simplify using the standard rewrite rules.
-/
theorem v_natCast_lt_one {g : ℕ} (hgv : (g : 𝓞 F) ∈ v.asIdeal) : Valued.v (g : Fv F v) < 1 := by
  have h := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (g : 𝓞 F)
  have h2 := (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (g : 𝓞 F)).mpr hgv
  rw [← h] at h2
  convert h2 using 2
  simp

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI := LocMassOrdSF.isModTop_tens (F := F) (E := E) (R := Fv F v)`. Establish `ht` using `Valued.tendsto_zero_pow_of_v_lt_one (v_natCast_lt_one v hgv)`. Establish `hev : ∀ i, ∀ᶠ N in atTop, (g : Fv F v) ^ N • c i ∈ OEv (E` using `E) v := fun i => by`. Establish `h2 : Tendsto (fun N : ℕ => (g : Fv F v) ^ N • c i) atTop (𝓝 ((0 : Fv F v) • c i))` using `ht.smul_const (c i)`.

Rewrite `h2` using `[zero_smul]`. Conclude with `h2 ((PI.LocMassTypU.isOpen_oev (E := E) (v := v)).mem_nhds (PI.LocMassTypU.oev_zero (E := E) (v := v)))`. Conclude with `(Filter.eventually_all.mpr hev).exists`.
-/
theorem eventually_pow_smul_mem {g : ℕ} (hgv : (g : 𝓞 F) ∈ v.asIdeal) {a : ℕ}
    (c : Fin a → Fv F v ⊗[F] E) : ∃ N : ℕ, ∀ i, (g : Fv F v) ^ N • c i ∈ OEv (E := E) v := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := LocMassOrdSF.isModTop_tens (F := F) (E := E) (R := Fv F v)
  have ht := Valued.tendsto_zero_pow_of_v_lt_one (v_natCast_lt_one v hgv)
  have hev : ∀ i, ∀ᶠ N in atTop, (g : Fv F v) ^ N • c i ∈ OEv (E := E) v := fun i => by
    have h2 : Tendsto (fun N : ℕ => (g : Fv F v) ^ N • c i) atTop (𝓝 ((0 : Fv F v) • c i)) :=
      ht.smul_const (c i)
    rw [zero_smul] at h2
    exact h2 ((PI.LocMassTypU.isOpen_oev (E := E) (v := v)).mem_nhds (PI.LocMassTypU.oev_zero (E := E) (v := v)))
  exact (Filter.eventually_all.mpr hev).exists

def P2 (a : ℕ) : Set (Fin a → Fin n → Fv F v ⊗[F] E) :=
  {X | ∀ c : Fin a → Fv F v ⊗[F] E, (∑ i, c i • X i) ∈ latLoc (E := E) v Λ →
    ∀ i, c i ∈ OEv (E := E) v}

def Sg (g a : ℕ) : Set (Fin a → Fv F v ⊗[F] E) :=
  (Set.univ.pi fun _ => (fun x : Fv F v ⊗[F] E => (g : Fv F v) • x) ⁻¹' OEv (E := E) v) ∩
    {c | ∃ i, c i ∉ OEv (E := E) v}

/- English proof (translation)
Use extensionality with `X`. Prove the components needed by the constructor for the conclusion. Introduce `hX`. Simplify using `only [Set.mem_compl_iff, P2, Set.mem_setOf_eq, not_forall, exists_prop] at hX`. Take `⟨c, hs, i0, hi0⟩` from `hX`.

Establish `hex : ∃ N : ℕ, ∀ i, (g : Fv F v) ^ N • c i ∈ OEv (E` using `E) v := eventually_pow_smul_mem v hgv c`. Establish `hN` using `Nat.find_spec hex`. Establish `hmin : ∀ m < Nat.find hex, ¬ ∀ i, (g : Fv F v) ^ m • c i ∈ OEv (E` using `E) v := fun m hm => Nat.find_min hex hm`. Establish `hN0 : Nat.find hex ≠ 0`. Introduce `h0`.

Apply `hi0` to reduce the goal to its premises. Use `hN i0` as an intermediate fact. Rewrite `this` using `[h0, pow_zero, one_smul]`. Then use the resulting hypothesis. Establish `hint : (g : Fv F v) ^ (Nat.find hex - 1) ∈ v.adicCompletionIntegers F` using `pow_mem (natCast_mem (v.adicCompletionIntegers F) g) _`. Use `⟨fun i => (g : Fv F v) ^ (Nat.find hex - 1) • c i, ⟨fun i _ => ?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Use `show (g : Fv F v) • ((g : Fv F v) ^ (Nat.find hex - 1) • c i) ∈ OEv (E := E) v`. Rewrite using `[smul_smul, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hN0)]`. Conclude with `hN i`. Assume the negation of the conclusion as `h`. Apply `hmin (Nat.find hex - 1) (Nat.sub_lt (Nat.pos_of_ne_zero hN0) one_pos)` to reduce the goal to its premises.

Introduce `i`. Assume the negation of the conclusion as `hi`. Conclude with `h ⟨i, hi⟩`. Use `show (∑ i, ((g : Fv F v) ^ (Nat.find hex - 1) • c i) • X i) ∈ latLoc (E := E) v Λ`. Repeatedly rewrite using `[smul_assoc, ← Finset.smul_sum]`.

Conclude with `(latLoc (E := E) v Λ).smul_mem (⟨_, hint⟩ : v.adicCompletionIntegers F) hs`. Introduce and unpack `⟨c, ⟨-, ⟨i, hi⟩⟩, hs⟩ hP`. Conclude with `hi (hP c hs i)`.
-/
theorem compl_congruence_tuples {g : ℕ} (hgv : (g : 𝓞 F) ∈ v.asIdeal) (a : ℕ) :
    (P2 v Λ a)ᶜ = {X | ∃ c ∈ Sg (E := E) v g a, (∑ i, c i • X i) ∈ latLoc (E := E) v Λ} := by
  classical
  ext X
  constructor
  · intro hX
    simp only [Set.mem_compl_iff, P2, Set.mem_setOf_eq, not_forall, exists_prop] at hX
    obtain ⟨c, hs, i0, hi0⟩ := hX
    have hex : ∃ N : ℕ, ∀ i, (g : Fv F v) ^ N • c i ∈ OEv (E := E) v := eventually_pow_smul_mem v hgv c
    have hN := Nat.find_spec hex
    have hmin : ∀ m < Nat.find hex, ¬ ∀ i, (g : Fv F v) ^ m • c i ∈ OEv (E := E) v :=
      fun m hm => Nat.find_min hex hm
    have hN0 : Nat.find hex ≠ 0 := by
      intro h0
      apply hi0
      have := hN i0
      rwa [h0, pow_zero, one_smul] at this
    have hint : (g : Fv F v) ^ (Nat.find hex - 1) ∈ v.adicCompletionIntegers F :=
      pow_mem (natCast_mem (v.adicCompletionIntegers F) g) _
    refine ⟨fun i => (g : Fv F v) ^ (Nat.find hex - 1) • c i, ⟨fun i _ => ?_, ?_⟩, ?_⟩
    · show (g : Fv F v) • ((g : Fv F v) ^ (Nat.find hex - 1) • c i) ∈ OEv (E := E) v
      rw [smul_smul, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hN0)]
      exact hN i
    · by_contra h
      apply hmin (Nat.find hex - 1) (Nat.sub_lt (Nat.pos_of_ne_zero hN0) one_pos)
      intro i
      by_contra hi
      exact h ⟨i, hi⟩
    · show (∑ i, ((g : Fv F v) ^ (Nat.find hex - 1) • c i) • X i) ∈ latLoc (E := E) v Λ
      simp_rw [smul_assoc, ← Finset.smul_sum]
      exact (latLoc (E := E) v Λ).smul_mem (⟨_, hint⟩ : v.adicCompletionIntegers F) hs
  · rintro ⟨c, ⟨-, ⟨i, hi⟩⟩, hs⟩ hP
    exact hi (hP c hs i)

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI := LocMassOrdSF.isModTop_tens (F := F) (E := E) (R := Fv F v)`. Establish `hg0 : (g : Fv F v) ≠ 0`. Rewrite using `[← map_natCast (algebraMap F (Fv F v)) g]`. Conclude with `(map_ne_zero _).mpr (by exact_mod_cast hg.ne_zero)`.

Establish `h1 : IsCompact ((fun x : Fv F v ⊗[F] E => (g : Fv F v) • x) ⁻¹' OEv (E` using `E) v) := (Homeomorph.isCompact_preimage (Homeomorph.smulOfNeZero (g : Fv F v) hg0)).mpr (LocMassOrdKv.isCompact_oev (v := v))`. Establish `h2 : IsClosed {c : Fin a → Fv F v ⊗[F] E | ∃ i, c i ∉ OEv (E` using `E) v} := by`. Establish `heq : {c : Fin a → Fv F v ⊗[F] E | ∃ i, c i ∉ OEv (E` using `E) v} = ⋃ i, (fun c : Fin a → Fv F v ⊗[F] E => c i) ⁻¹' (OEv (E := E) v)ᶜ := by`. Use extensionality with `c`. Simplify using the standard rewrite rules.

Rewrite using `[heq]`. Conclude with `isClosed_iUnion_of_finite fun i => (PI.LocMassTypU.isOpen_oev (v := v)).isClosed_compl.preimage (continuous_apply i)`. Conclude with `(isCompact_univ_pi fun _ => h1).inter_right h2`.
-/
theorem isCompact_Sg {g : ℕ} (hg : g.Prime) (a : ℕ) : IsCompact (Sg (E := E) v g a) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := LocMassOrdSF.isModTop_tens (F := F) (E := E) (R := Fv F v)
  have hg0 : (g : Fv F v) ≠ 0 := by
    rw [← map_natCast (algebraMap F (Fv F v)) g]
    exact (map_ne_zero _).mpr (by exact_mod_cast hg.ne_zero)
  have h1 : IsCompact ((fun x : Fv F v ⊗[F] E => (g : Fv F v) • x) ⁻¹' OEv (E := E) v) :=
    (Homeomorph.isCompact_preimage (Homeomorph.smulOfNeZero (g : Fv F v) hg0)).mpr
      (LocMassOrdKv.isCompact_oev (v := v))
  have h2 : IsClosed {c : Fin a → Fv F v ⊗[F] E | ∃ i, c i ∉ OEv (E := E) v} := by
    have heq : {c : Fin a → Fv F v ⊗[F] E | ∃ i, c i ∉ OEv (E := E) v} =
        ⋃ i, (fun c : Fin a → Fv F v ⊗[F] E => c i) ⁻¹' (OEv (E := E) v)ᶜ := by
      ext c
      simp
    rw [heq]
    exact isClosed_iUnion_of_finite fun i =>
      (PI.LocMassTypU.isOpen_oev (v := v)).isClosed_compl.preimage (continuous_apply i)
  exact (isCompact_univ_pi fun _ => h1).inter_right h2

/- English proof (translation)
Use `haveI : CompactSpace (Sg (E := E) v g a) := isCompact_iff_compactSpace.mp (isCompact_Sg v hg a)`. Establish `hC : IsClosed {p : Sg (E` using `E) v g a × (Fin a → Fin n → Fv F v ⊗[F] E) | (∑ i, (p.1 : Fin a → Fv F v ⊗[F] E) i • p.2 i) ∈ latLoc (E := E) v Λ} := by`. Use `(LocMassOrdKv.isClosed_latLoc (σ := σ) (J := J) (v := v) Λ hSD).preimage ?_` and prove the remaining obligations. Conclude with `continuous_finset_sum _ fun i _ => ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).smul ((continuous_apply i).comp continuous_snd)`. Establish `himg : (P2 v Λ a)ᶜ = Prod.snd '' {p : Sg (E` using `E) v g a × (Fin a → Fin n → Fv F v ⊗[F] E) | (∑ i, (p.1 : Fin a → Fv F v ⊗[F] E) i • p.2 i) ∈ latLoc (E := E) v Λ} := by`.

Rewrite using `[compl_congruence_tuples v Λ hgv a]`. Use extensionality with `X`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc, hs⟩`. Conclude with `⟨(⟨c, hc⟩, X), hs, rfl⟩`.

Introduce and unpack `⟨⟨c, X'⟩, hs, rfl⟩`. Conclude with `⟨c.1, c.2, hs⟩`. Rewrite using `[← isClosed_compl_iff, himg]`. Conclude with `isClosedMap_snd_of_compactSpace _ hC`.
-/
theorem isOpen_congruence_tuples (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (hSD : IsSDLoc σ J v Λ)
    {g : ℕ} (hg : g.Prime) (hgv : (g : 𝓞 F) ∈ v.asIdeal) (a : ℕ) : IsOpen (P2 v Λ a) := by
  haveI : CompactSpace (Sg (E := E) v g a) := isCompact_iff_compactSpace.mp (isCompact_Sg v hg a)
  have hC : IsClosed {p : Sg (E := E) v g a × (Fin a → Fin n → Fv F v ⊗[F] E) |
      (∑ i, (p.1 : Fin a → Fv F v ⊗[F] E) i • p.2 i) ∈ latLoc (E := E) v Λ} := by
    refine (LocMassOrdKv.isClosed_latLoc (σ := σ) (J := J) (v := v) Λ hSD).preimage ?_
    exact continuous_finset_sum _ fun i _ =>
      ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).smul
        ((continuous_apply i).comp continuous_snd)
  have himg : (P2 v Λ a)ᶜ = Prod.snd '' {p : Sg (E := E) v g a × (Fin a → Fin n → Fv F v ⊗[F] E) |
      (∑ i, (p.1 : Fin a → Fv F v ⊗[F] E) i • p.2 i) ∈ latLoc (E := E) v Λ} := by
    rw [compl_congruence_tuples v Λ hgv a]
    ext X
    constructor
    · rintro ⟨c, hc, hs⟩
      exact ⟨(⟨c, hc⟩, X), hs, rfl⟩
    · rintro ⟨⟨c, X'⟩, hs, rfl⟩
      exact ⟨c.1, c.2, hs⟩
  rw [← isClosed_compl_iff, himg]
  exact isClosedMap_snd_of_compactSpace _ hC

/- English proof (translation)
Establish `heq : {X : Fin a → Fin n → Fv F v ⊗[F] E | ∀ i, X i ∈ latLoc (E` using `E) v Λ} = ⋂ i, (fun X : Fin a → Fin n → Fv F v ⊗[F] E => X i) ⁻¹' (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by`. Use extensionality with `X`. Simplify using the standard rewrite rules. Rewrite using `[heq]`. Conclude with `isClosed_iInter fun i => (LocMassOrdKv.isClosed_latLoc (σ := σ) (J := J) (v := v) Λ hSD).preimage (continuous_apply i)`.
-/
theorem isClosed_lattice_tuples (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (hSD : IsSDLoc σ J v Λ) (a : ℕ) :
    IsClosed {X : Fin a → Fin n → Fv F v ⊗[F] E | ∀ i, X i ∈ latLoc (E := E) v Λ} := by
  have heq : {X : Fin a → Fin n → Fv F v ⊗[F] E | ∀ i, X i ∈ latLoc (E := E) v Λ} =
      ⋂ i, (fun X : Fin a → Fin n → Fv F v ⊗[F] E => X i) ⁻¹'
        (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
    ext X
    simp
  rw [heq]
  exact isClosed_iInter fun i =>
    (LocMassOrdKv.isClosed_latLoc (σ := σ) (J := J) (v := v) Λ hSD).preimage (continuous_apply i)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem isPrim_eq (a : ℕ) :
    {X : Fin a → Fin n → Fv F v ⊗[F] E | IsPrim v Λ X} =
      {X | ∀ i, X i ∈ latLoc (E := E) v Λ} ∩ P2 v Λ a := rfl

/- English proof (translation)
Rewrite using `[isPrim_eq]`. Conclude with `(isClosed_lattice_tuples v Λ σ J hSD a).measurableSet.inter (isOpen_congruence_tuples v Λ σ J hSD hg hgv a).measurableSet`.
-/
theorem measurableSet_prim (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (hSD : IsSDLoc σ J v Λ)
    {g : ℕ} (hg : g.Prime) (hgv : (g : 𝓞 F) ∈ v.asIdeal) (a : ℕ) :
    MeasurableSet {X : Fin a → Fin n → Fv F v ⊗[F] E | IsPrim v Λ X} := by
  rw [isPrim_eq]
  exact (isClosed_lattice_tuples v Λ σ J hSD a).measurableSet.inter (isOpen_congruence_tuples v Λ σ J hSD hg hgv a).measurableSet

/- English proof (translation)
Establish `hg0 : (g : Fv F v) ≠ 0`. Rewrite using `[← map_natCast (algebraMap F (Fv F v)) g]`. Conclude with `(map_ne_zero _).mpr (by exact_mod_cast hg.ne_zero)`. Establish `heq : {z | ∀ a, ∃ y ∈ latLoc (E` using `E) v Λ, locF v (f2 z) a - locF v (f1 z) a = sc (E := E) v (g : Fv F v) • y} = ⋂ a, (fun z => sc (E := E) v (g : Fv F v)⁻¹ • (locF v (f2 z) a - locF v (f1 z) a)) ⁻¹' (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by`. Use extensionality with `z`.

Simplify using `only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]`. Conclude with `forall_congr' fun a => mem_gLat_iff v Λ hg0 _`. Rewrite using `[heq]`. Use `isClosed_iInter fun a => (LocMassOrdKv.isClosed_latLoc (σ := σ) (J := J) (v := v) Λ hSD).preimage ?_` and prove the remaining obligations. Conclude with `(continuous_const : Continuous fun _ : Z => sc (E := E) v (g : Fv F v)⁻¹).smul (((continuous_locF v a).comp h2).sub ((continuous_locF v a).comp h1))`.
-/
theorem isClosed_cong (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (hSD : IsSDLoc σ J v Λ)
    {g : ℕ} (hg : g.Prime) {r : ℕ} {Z : Type} [TopologicalSpace Z]
    (f1 f2 : Z → TupV (E := E) v n (r + 1)) (h1 : Continuous f1) (h2 : Continuous f2) :
    IsClosed {z | ∀ a, ∃ y ∈ latLoc (E := E) v Λ,
      locF v (f2 z) a - locF v (f1 z) a = sc (E := E) v (g : Fv F v) • y} := by
  have hg0 : (g : Fv F v) ≠ 0 := by
    rw [← map_natCast (algebraMap F (Fv F v)) g]
    exact (map_ne_zero _).mpr (by exact_mod_cast hg.ne_zero)
  have heq : {z | ∀ a, ∃ y ∈ latLoc (E := E) v Λ,
      locF v (f2 z) a - locF v (f1 z) a = sc (E := E) v (g : Fv F v) • y} =
      ⋂ a, (fun z => sc (E := E) v (g : Fv F v)⁻¹ • (locF v (f2 z) a - locF v (f1 z) a)) ⁻¹'
        (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    exact forall_congr' fun a => mem_gLat_iff v Λ hg0 _
  rw [heq]
  refine isClosed_iInter fun a => (LocMassOrdKv.isClosed_latLoc (σ := σ) (J := J) (v := v) Λ hSD).preimage ?_
  exact (continuous_const : Continuous fun _ : Z => sc (E := E) v (g : Fv F v)⁻¹).smul
    (((continuous_locF v a).comp h2).sub ((continuous_locF v a).comp h1))

/- English proof (translation)
Establish `hc1 : Continuous fun p : TupV (E` using `E) v n (r + 1) × TupV (E := E) v n (r + 1) => locF v p.1 := continuous_pi fun a => (continuous_locF v a).comp continuous_fst`. Establish `hc2 : Continuous fun p : TupV (E` using `E) v n (r + 1) × TupV (E := E) v n (r + 1) => locF v p.2 := continuous_pi fun a => (continuous_locF v a).comp continuous_snd`. Establish `h1` using `(measurableSet_prim v Λ σ J hSD hg hgv (r + 1)).preimage hc1.measurable`. Establish `h2` using `(measurableSet_prim v Λ σ J hSD hg hgv (r + 1)).preimage hc2.measurable`. Establish `h3` using `(isClosed_cong v Λ σ J hSD hg (r := r) (Z := TupV (E := E) v n (r + 1) × TupV (E := E) v n (r + 1)) Prod.fst Prod.snd continuous_fst continuous_snd).measurableSet`.

Conclude with `h1.inter (h2.inter h3)`.
-/
theorem measurableSet_omTyp (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (hSD : IsSDLoc σ J v Λ)
    {g : ℕ} (hg : g.Prime) (hgv : (g : 𝓞 F) ∈ v.asIdeal) (r : ℕ) :
    MeasurableSet (OmTyp v Λ g r) := by
  have hc1 : Continuous fun p : TupV (E := E) v n (r + 1) × TupV (E := E) v n (r + 1) => locF v p.1 :=
    continuous_pi fun a => (continuous_locF v a).comp continuous_fst
  have hc2 : Continuous fun p : TupV (E := E) v n (r + 1) × TupV (E := E) v n (r + 1) => locF v p.2 :=
    continuous_pi fun a => (continuous_locF v a).comp continuous_snd
  have h1 := (measurableSet_prim v Λ σ J hSD hg hgv (r + 1)).preimage hc1.measurable
  have h2 := (measurableSet_prim v Λ σ J hSD hg hgv (r + 1)).preimage hc2.measurable
  have h3 := (isClosed_cong v Λ σ J hSD hg (r := r)
    (Z := TupV (E := E) v n (r + 1) × TupV (E := E) v n (r + 1)) Prod.fst Prod.snd continuous_fst continuous_snd).measurableSet
  exact h1.inter (h2.inter h3)

end Lat

section K1

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
  (Λ : Set (Fin n → E))

/- English proof (translation)
Conclude with `(LocMassOrdKv.isClosed_Kv (σ := σ) (J := J) (v := v) Λ hSD).inter (isClosed_cong v Λ σ J hSD hg (Z := HA (Fv F v) σ J) (fun _ => ratTup (Fv F v) (F0 P)) (fun k => k • ratTup (Fv F v) (F0 P)) continuous_const (continuous_smulTup σ J v _))`.
-/
theorem isClosed_congruence_subgroup (hSD : IsSDLoc σ J v Λ) {g : ℕ} (hg : g.Prime) {r : ℕ} (P : Frame E n r) :
    IsClosed (K1 σ J v Λ g P) := by
  exact (LocMassOrdKv.isClosed_Kv (σ := σ) (J := J) (v := v) Λ hSD).inter
    (isClosed_cong v Λ σ J hSD hg (Z := HA (Fv F v) σ J) (fun _ => ratTup (Fv F v) (F0 P))
      (fun k => k • ratTup (Fv F v) (F0 P)) continuous_const (continuous_smulTup σ J v _))

end K1

end PI.LocMassTypM
