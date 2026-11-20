import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import GroundTheory.LocalFields.LocalZetaShell
open NumberField IsDedekindDomain MeasureTheory Topology GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LocalTestVectors

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Use `haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) F) := show SecondCountableTopology (Fin 2 → Fin 2 → F) from inferInstance`. Use `haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) F)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology`. Conclude with `Units.isEmbedding_embedProduct.secondCountableTopology`.
-/
theorem secondCountable_GL2 : SecondCountableTopology (GL (Fin 2) F) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) F) :=
    show SecondCountableTopology (Fin 2 → Fin 2 → F) from inferInstance
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

omit [MeasurableSpace F] [BorelSpace F] in

/- English proof (translation)
Establish `a : ValuativeRel.valuation F (x : F) ≤ 1` using `h1`. Establish `b : ValuativeRel.valuation F ((x⁻¹ : Fˣ) : F) ≤ 1` using `h2`. Establish `c : ValuativeRel.valuation F (x : F) = 1`. Use `le_antisymm a ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Conclude with `modulus_eq_one_iff.2 ⟨x.ne_zero, mem_unitFiltrationUnits_zero_iff_ord.1 (mem_unitFiltrationUnits_zero_iff.2 c)⟩`.
-/
theorem modulus_eq_one_of_integral {x : Fˣ} (h1 : (x : F) ∈ 𝒪[F]) (h2 : ((x⁻¹ : Fˣ) : F) ∈ 𝒪[F]) :
    modulus (x : F) = 1 := by
  have a : ValuativeRel.valuation F (x : F) ≤ 1 := h1
  have b : ValuativeRel.valuation F ((x⁻¹ : Fˣ) : F) ≤ 1 := h2
  have c : ValuativeRel.valuation F (x : F) = 1 := by
    refine le_antisymm a ?_
    calc (1 : ValuativeRel.ValueGroupWithZero F)
        = ValuativeRel.valuation F ((x : F) * ((x⁻¹ : Fˣ) : F)) := by simp
      _ = ValuativeRel.valuation F (x : F) * ValuativeRel.valuation F ((x⁻¹ : Fˣ) : F) := map_mul _ _ _
      _ ≤ ValuativeRel.valuation F (x : F) := mul_le_of_le_one_right' b
  exact modulus_eq_one_iff.2 ⟨x.ne_zero,
    mem_unitFiltrationUnits_zero_iff_ord.1 (mem_unitFiltrationUnits_zero_iff.2 c)⟩

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [uni2, Matrix.mul_apply, Fin.sum_univ_two]`.
-/
theorem unipotent_neg_mul (x : F) : uni2 (-x) * uni2 x = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uni2, Matrix.mul_apply, Fin.sum_univ_two]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]`.
-/
theorem diag_inv_mul_alt (c b : Fˣ) : dg2 c⁻¹ b⁻¹ * dg2 c b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]

omit [MeasurableSpace F] [BorelSpace F] in

/- English proof (translation)
Establish `hm : u * k⁻¹ = uni2 (-x) * dg2 c b`. Combine the equalities or inequalities in the displayed calculation. Establish `hm' : k * u⁻¹ = dg2 c⁻¹ b⁻¹ * uni2 x`. Combine the equalities or inequalities in the displayed calculation. Establish `i1` using `((GLnLocal.mem_integralGL_iff F 2).1 ((GLnLocal.integralGL F 2).mul_mem hu ((GLnLocal.integralGL F 2).inv_mem hk))).1`.

Establish `i2` using `((GLnLocal.mem_integralGL_iff F 2).1 ((GLnLocal.integralGL F 2).mul_mem hk ((GLnLocal.integralGL F 2).inv_mem hu))).1`. Rewrite `i1` using `[hm]`. Rewrite `i2` using `[hm']`. Establish `a1` using `i1 0 0`. Establish `a2` using `i1 1 1`.

Establish `b1` using `i2 0 0`. Establish `b2` using `i2 1 1`. Simplify using `[uni2, dg2, Matrix.mul_apply, Fin.sum_univ_two] at a1 a2 b1 b2`. Conclude with `⟨modulus_eq_one_of_integral a1 (by simpa using b1), modulus_eq_one_of_integral a2 (by simpa using b2)⟩`.
-/
theorem modulus_of_decomp {c b : Fˣ} {k u : GL (Fin 2) F} {x : F}
    (hk : k ∈ GLnLocal.integralGL F 2) (hu : u ∈ GLnLocal.integralGL F 2)
    (h : dg2 c b * k = uni2 x * u) : modulus (c : F) = 1 ∧ modulus (b : F) = 1 := by
  have hm : u * k⁻¹ = uni2 (-x) * dg2 c b := by
    calc u * k⁻¹ = uni2 (-x) * (uni2 x * u) * k⁻¹ := by rw [← mul_assoc, unipotent_neg_mul, one_mul]
      _ = uni2 (-x) * dg2 c b := by rw [← h]; group
  have hm' : k * u⁻¹ = dg2 c⁻¹ b⁻¹ * uni2 x := by
    calc k * u⁻¹ = dg2 c⁻¹ b⁻¹ * (dg2 c b * k) * u⁻¹ := by rw [← mul_assoc, diag_inv_mul_alt, one_mul]
      _ = dg2 c⁻¹ b⁻¹ * uni2 x := by rw [h]; group
  have i1 := ((GLnLocal.mem_integralGL_iff F 2).1
    ((GLnLocal.integralGL F 2).mul_mem hu ((GLnLocal.integralGL F 2).inv_mem hk))).1
  have i2 := ((GLnLocal.mem_integralGL_iff F 2).1
    ((GLnLocal.integralGL F 2).mul_mem hk ((GLnLocal.integralGL F 2).inv_mem hu))).1
  rw [hm] at i1
  rw [hm'] at i2
  have a1 := i1 0 0
  have a2 := i1 1 1
  have b1 := i2 0 0
  have b2 := i2 1 1
  simp [uni2, dg2, Matrix.mul_apply, Fin.sum_univ_two] at a1 a2 b1 b2
  exact ⟨modulus_eq_one_of_integral a1 (by simpa using b1),
    modulus_eq_one_of_integral a2 (by simpa using b2)⟩

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `refine continuous_matrix fun i j => ?_ fin_cases i <;> fin_cases j <;> simp [dg2] <;> fun_prop`. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Establish `h1 : Continuous fun p : Fˣ × Fˣ => ((p.1⁻¹ : Fˣ) : F)` using `Units.continuous_val.comp (continuous_inv.comp continuous_fst)`. Establish `h2 : Continuous fun p : Fˣ × Fˣ => ((p.2⁻¹ : Fˣ) : F)` using `Units.continuous_val.comp (continuous_inv.comp continuous_snd)`.

Apply the tactic sequence `fin_cases i <;> fin_cases j`. Conclude with `h1`. Conclude with `continuous_const`. Conclude with `continuous_const`. Conclude with `h2`.
-/
theorem continuous_diagGL2 :
    Continuous (fun p : Fˣ × Fˣ => (dg2 p.1 p.2 : GL (Fin 2) F)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [dg2] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    have h1 : Continuous fun p : Fˣ × Fˣ => ((p.1⁻¹ : Fˣ) : F) :=
      Units.continuous_val.comp (continuous_inv.comp continuous_fst)
    have h2 : Continuous fun p : Fˣ × Fˣ => ((p.2⁻¹ : Fˣ) : F) :=
      Units.continuous_val.comp (continuous_inv.comp continuous_snd)
    fin_cases i <;> fin_cases j
    · exact h1
    · exact continuous_const
    · exact continuous_const
    · exact h2

def iwPt (p : Fˣ × Fˣ × GL (Fin 2) F) : GL (Fin 2) F := dg2 (p.1 * p.2.1) p.2.1 * p.2.2

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Unfold `iwPt`. Establish `h` using `(continuous_diagGL2 (F := F)).comp (((continuous_fst.mul (continuous_fst.comp continuous_snd)).prodMk (continuous_fst.comp continuous_snd)) : Continuous fun p : Fˣ × Fˣ × GL (Fin 2) F => (p.1 * p.2.1, p.2.1))`. Conclude with `h.mul (continuous_snd.comp continuous_snd)`.
-/
theorem continuous_iwPt : Continuous (iwPt (F := F)) := by
  unfold iwPt
  have h := (continuous_diagGL2 (F := F)).comp
    (((continuous_fst.mul (continuous_fst.comp continuous_snd)).prodMk
      (continuous_fst.comp continuous_snd)) :
      Continuous fun p : Fˣ × Fˣ × GL (Fin 2) F => (p.1 * p.2.1, p.2.1))
  exact h.mul (continuous_snd.comp continuous_snd)

def nS (S : Set (GL (Fin 2) F)) : Set (GL (Fin 2) F) := {h | ∃ x, ∃ u ∈ S, h = uni2 x * u}

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Establish `: nS S = ⋃ x : F, (fun h => uni2 (-x) * h) ⁻¹' S`. Use extensionality with `h`. Simplify using `only [nS, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, u, hu, rfl⟩`.

Conclude with `⟨x, by rwa [← mul_assoc, unipotent_neg_mul, one_mul]⟩`. Introduce and unpack `⟨x, hx⟩`. Use `⟨x, _, hx, ?_⟩` and prove the remaining obligations. Establish `e : uni2 x * uni2 (-x) = 1` using `by simpa using unipotent_neg_mul (-x)`. Rewrite using `[← mul_assoc, e, one_mul]`.

Rewrite using `[this]`. Conclude with `isOpen_iUnion fun x => hS.preimage (continuous_const.mul continuous_id)`.
-/
theorem isOpen_nS {S : Set (GL (Fin 2) F)} (hS : IsOpen S) : IsOpen (nS S) := by
  have : nS S = ⋃ x : F, (fun h => uni2 (-x) * h) ⁻¹' S := by
    ext h
    simp only [nS, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨x, u, hu, rfl⟩
      exact ⟨x, by rwa [← mul_assoc, unipotent_neg_mul, one_mul]⟩
    · rintro ⟨x, hx⟩
      refine ⟨x, _, hx, ?_⟩
      have e : uni2 x * uni2 (-x) = 1 := by simpa using unipotent_neg_mul (-x)
      rw [← mul_assoc, e, one_mul]
  rw [this]
  exact isOpen_iUnion fun x => hS.preimage (continuous_const.mul continuous_id)

def tSet (S : Set (GL (Fin 2) F)) : Set (Fˣ × Fˣ × GL (Fin 2) F) :=
  {p | p.2.2 ∈ GL2LocalData.K2 F ∧ iwPt p ∈ nS S}

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
The claim follows from `((GLnLocal.isOpen_integralGL F 2).preimage (continuous_snd.comp continuous_snd)).inter ((isOpen_nS hS).preimage continuous_iwPt)`.
-/
theorem isOpen_tSet {S : Set (GL (Fin 2) F)} (hS : IsOpen S) : IsOpen (tSet S) :=
  ((GLnLocal.isOpen_integralGL F 2).preimage (continuous_snd.comp continuous_snd)).inter
    ((isOpen_nS hS).preimage continuous_iwPt)

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Take `⟨hk, x, u, hu, h⟩` from `hp`. Take `⟨h1, h2⟩` from `modulus_of_decomp hk (hSK hu) h`. Use `⟨?_, h2⟩` and prove the remaining obligations. Rewrite `h1` using `[Units.val_mul, modulus_mul, h2, mul_one]`. Conclude with `h1`.
-/
theorem modulus_of_mem_tSet {S : Set (GL (Fin 2) F)} (hSK : S ⊆ GL2LocalData.K2 F) {p} (hp : p ∈ tSet S) :
    modulus (p.1 : F) = 1 ∧ modulus (p.2.1 : F) = 1 := by
  obtain ⟨hk, x, u, hu, h⟩ := hp
  obtain ⟨h1, h2⟩ := modulus_of_decomp hk (hSK hu) h
  refine ⟨?_, h2⟩
  rw [Units.val_mul, modulus_mul, h2, mul_one] at h1
  exact h1

/- English proof (translation)
Use `haveI : (LFS.hG ψ).IsHaarMeasure := by unfold LFS.hG; infer_instance`. Establish `hKc : IsCompact (GL2LocalData.K2 F)` using `GLnLocal.isCompact_integralGL F 2`. Establish `hKo : IsOpen (GL2LocalData.K2 F)` using `GLnLocal.isOpen_integralGL F 2`. Use `haveI : IsFiniteMeasure ((LFS.hG ψ).restrict (GL2LocalData.K2 F)) := ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩`. Prove the components needed by the constructor for the conclusion.

Establish `hone : ((1 : Fˣ), ((1 : Fˣ), (1 : GL (Fin 2) F))) ∈ tSet S`. Use `⟨(GLnLocal.integralGL F 2).one_mem, 0, 1, h1, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [iwPt, uni2, dg2]`. Take `⟨U₁, V, hU₁, hV, h1U, h1V, hsub⟩` from `isOpen_prod_iff.1 (isOpen_tSet hS) _ _ hone`.

Take `⟨U₂, S', hU₂, hS', h2U, h1S, hsub'⟩` from `isOpen_prod_iff.1 hV _ _ h1V`. Establish `hbox : U₁ ×ˢ (U₂ ×ˢ S') ⊆ tSet S` using `(Set.prod_mono_right hsub').trans hsub`. Introduce `h0`. Establish `hz` using `measure_mono_null hbox h0`. Unfold `GL2LocalData.mIw at hz`.

Rewrite `hz` using `[Measure.prod_prod, Measure.prod_prod, Measure.restrict_apply hS'.measurableSet]`. Establish `p1 : multHaar F U₁ ≠ 0` using `(hU₁.measure_pos _ ⟨1, h1U⟩).ne'`. Establish `p2 : multHaar F U₂ ≠ 0` using `(hU₂.measure_pos _ ⟨1, h2U⟩).ne'`. Establish `p3 : LFS.hG ψ (S' ∩ GL2LocalData.K2 F) ≠ 0` using `((hS'.inter hKo).measure_pos _ ⟨1, h1S, (GLnLocal.integralGL F 2).one_mem⟩).ne'`. Simplify using `[p1, p2, p3] at hz`.

Establish `hbox : tSet S ⊆ (unitFiltrationUnits F 0 : Set Fˣ) ×ˢ ((unitFiltrationUnits F 0 : Set Fˣ) ×ˢ (GL2LocalData.K2 F))`. Introduce `p hp`. Take `⟨m1, m2⟩` from `modulus_of_mem_tSet hSK hp`. Conclude with `⟨mem_unitFiltrationUnits_zero_iff_ord.2 (modulus_eq_one_iff.1 m1).2, mem_unitFiltrationUnits_zero_iff_ord.2 (modulus_eq_one_iff.1 m2).2, hp.1⟩`. Use `ne_top_of_le_ne_top ?_ (measure_mono hbox)` and prove the remaining obligations.

Unfold `GL2LocalData.mIw`. Rewrite using `[Measure.prod_prod, Measure.prod_prod, multHaar_unitFiltrationUnits_zero, one_mul, one_mul]`. Conclude with `measure_ne_top _ _`.
-/
theorem mIw_tSet_pos_finite (ψ : AddChar F Circle) {S : Set (GL (Fin 2) F)} (hS : IsOpen S)
    (h1 : (1 : GL (Fin 2) F) ∈ S) (hSK : S ⊆ GL2LocalData.K2 F) :
    GL2LocalData.mIw ψ (tSet S) ≠ 0 ∧ GL2LocalData.mIw ψ (tSet S) ≠ ⊤ := by
  haveI : (LFS.hG ψ).IsHaarMeasure := by unfold LFS.hG; infer_instance
  have hKc : IsCompact (GL2LocalData.K2 F) := GLnLocal.isCompact_integralGL F 2
  have hKo : IsOpen (GL2LocalData.K2 F) := GLnLocal.isOpen_integralGL F 2
  haveI : IsFiniteMeasure ((LFS.hG ψ).restrict (GL2LocalData.K2 F)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
  constructor
  · have hone : ((1 : Fˣ), ((1 : Fˣ), (1 : GL (Fin 2) F))) ∈ tSet S := by
      refine ⟨(GLnLocal.integralGL F 2).one_mem, 0, 1, h1, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [iwPt, uni2, dg2]
    obtain ⟨U₁, V, hU₁, hV, h1U, h1V, hsub⟩ := isOpen_prod_iff.1 (isOpen_tSet hS) _ _ hone
    obtain ⟨U₂, S', hU₂, hS', h2U, h1S, hsub'⟩ := isOpen_prod_iff.1 hV _ _ h1V
    have hbox : U₁ ×ˢ (U₂ ×ˢ S') ⊆ tSet S :=
      (Set.prod_mono_right hsub').trans hsub
    intro h0
    have hz := measure_mono_null hbox h0
    unfold GL2LocalData.mIw at hz
    rw [Measure.prod_prod, Measure.prod_prod, Measure.restrict_apply hS'.measurableSet] at hz
    have p1 : multHaar F U₁ ≠ 0 := (hU₁.measure_pos _ ⟨1, h1U⟩).ne'
    have p2 : multHaar F U₂ ≠ 0 := (hU₂.measure_pos _ ⟨1, h2U⟩).ne'
    have p3 : LFS.hG ψ (S' ∩ GL2LocalData.K2 F) ≠ 0 :=
      ((hS'.inter hKo).measure_pos _ ⟨1, h1S, (GLnLocal.integralGL F 2).one_mem⟩).ne'
    simp [p1, p2, p3] at hz
  · have hbox : tSet S ⊆ (unitFiltrationUnits F 0 : Set Fˣ) ×ˢ
        ((unitFiltrationUnits F 0 : Set Fˣ) ×ˢ (GL2LocalData.K2 F)) := by
      intro p hp
      obtain ⟨m1, m2⟩ := modulus_of_mem_tSet hSK hp
      exact ⟨mem_unitFiltrationUnits_zero_iff_ord.2 (modulus_eq_one_iff.1 m1).2,
        mem_unitFiltrationUnits_zero_iff_ord.2 (modulus_eq_one_iff.1 m2).2, hp.1⟩
    refine ne_top_of_le_ne_top ?_ (measure_mono hbox)
    unfold GL2LocalData.mIw
    rw [Measure.prod_prod, Measure.prod_prod, multHaar_unitFiltrationUnits_zero, one_mul, one_mul]
    exact measure_ne_top _ _

/- English proof (translation)
Use `haveI : (LFS.hG ψ).IsHaarMeasure := by unfold LFS.hG; infer_instance`. Establish `hKc : IsCompact (GL2LocalData.K2 F)` using `GLnLocal.isCompact_integralGL F 2`. Establish `hKo : IsOpen (GL2LocalData.K2 F)` using `GLnLocal.isOpen_integralGL F 2`. Use `haveI : IsFiniteMeasure ((LFS.hG ψ).restrict (GL2LocalData.K2 F)) := ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩`. Rewrite using `[ae_iff]`.

Establish `e : {p : Fˣ × Fˣ × GL (Fin 2) F | ¬ p.2.2 ∈ GL2LocalData.K2 F} = Set.univ ×ˢ (Set.univ ×ˢ (GL2LocalData.K2 F)ᶜ)`. Use extensionality with `p`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Unfold `GL2LocalData.mIw`.

Rewrite using `[Measure.prod_prod, Measure.prod_prod, Measure.restrict_apply hKo.measurableSet.compl]`. Simplify using the standard rewrite rules.
-/
theorem ae_mem_maximal_compact (ψ : AddChar F Circle) : ∀ᵐ p ∂GL2LocalData.mIw ψ, p.2.2 ∈ GL2LocalData.K2 F := by
  haveI : (LFS.hG ψ).IsHaarMeasure := by unfold LFS.hG; infer_instance
  have hKc : IsCompact (GL2LocalData.K2 F) := GLnLocal.isCompact_integralGL F 2
  have hKo : IsOpen (GL2LocalData.K2 F) := GLnLocal.isOpen_integralGL F 2
  haveI : IsFiniteMeasure ((LFS.hG ψ).restrict (GL2LocalData.K2 F)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hKc.measure_lt_top⟩
  rw [ae_iff]
  have e : {p : Fˣ × Fˣ × GL (Fin 2) F | ¬ p.2.2 ∈ GL2LocalData.K2 F} =
      Set.univ ×ˢ (Set.univ ×ˢ (GL2LocalData.K2 F)ᶜ) := by
    ext p; simp
  rw [e]
  unfold GL2LocalData.mIw
  rw [Measure.prod_prod, Measure.prod_prod,
    Measure.restrict_apply hKo.measurableSet.compl]
  simp

end GlobalTheory.CompanionTheory.LocalTestVectors

open GlobalTheory.CompanionTheory.LocalTestVectors in
/- English proof (translation)
Introduce `F _ _ _ _ _ _ ψ W Wt S C₁ C₂ hS h1 hSK hC₁ hC₂ hsup hW hWt`. Use `haveI : SecondCountableTopology (GL (Fin 2) F) := secondCountable_GL2`. Establish `hTm : MeasurableSet (tSet S)` using `(isOpen_tSet hS).measurableSet`. Take `⟨hT0, hTt⟩` from `mIw_tSet_pos_finite ψ hS h1 hSK`. Establish `hreal : (GL2LocalData.mIw ψ).real (tSet S) ≠ 0` using `(ENNReal.toReal_pos hT0 hTt).ne'`.

Use `⟨((GL2LocalData.mIw ψ).real (tSet S) : ℂ) * (C₁ * C₂), ?_, fun s => ?_⟩` and prove the remaining obligations. Conclude with `mul_ne_zero (by exact_mod_cast hreal) (mul_ne_zero hC₁ hC₂)`. Establish `key : ∀ p : Fˣ × Fˣ × GL (Fin 2) F, p.2.2 ∈ GL2LocalData.K2 F → GL2LocalData.iw W Wt s p = (tSet S).indicator (fun _ => C₁ * C₂) p`. Introduce `p hk`. Distinguish the cases in `hp : p ∈ tSet S`.

Rewrite using `[Set.indicator_of_mem hp]`. Take `⟨m1, m2⟩` from `modulus_of_mem_tSet hSK hp`. Take `⟨-, x, u, hu, h⟩` from `hp`. Establish `h' : dg2 (p.1 * p.2.1) p.2.1 * p.2.2 = uni2 x * u` using `h`. Establish `hψ : (ψ x : ℂ) * ((ψ⁻¹ x : Circle) : ℂ) = 1`.

Rewrite using `[AddChar.inv_apply', Circle.coe_inv]`. Conclude with `mul_inv_cancel₀ (Circle.coe_ne_zero _)`. Unfold `GL2LocalData.iw`. Rewrite using `[h', hW x u hu, hWt x u hu]`. Simplify using `only [mp, m1, m2, NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow, mul_one]`.

Take the linear combination `(C₁ * C₂) * hψ`. Rewrite using `[Set.indicator_of_notMem hp]`. Establish `h0 : W (GL2LocalData.em (iwPt p)) = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hp ⟨hk, hsup _ hne⟩`.

Establish `h0' : W (GL2LocalData.em (dg2 (p.1 * p.2.1) p.2.1 * p.2.2)) = 0` using `h0`. Unfold `GL2LocalData.iw`. Rewrite using `[h0']`. Simplify using the standard rewrite rules. Unfold `GL2LocalData.zetaGL3GL2`.

Rewrite using `[integral_congr_ae ((ae_mem_maximal_compact ψ).mono key), integral_indicator_const _ hTm, Complex.real_smul]`.
-/
theorem GlobalTheory.CompanionTheory.LocalTestVectors.main : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
  (ψ : AddChar F Circle) (W : GL (Fin 3) F → ℂ) (Wt : GL (Fin 2) F → ℂ) (S : Set (GL (Fin 2) F)) (C₁ C₂ : ℂ),
  IsOpen S → (1 : GL (Fin 2) F) ∈ S → S ⊆ GL2LocalData.K2 F → C₁ ≠ 0 → C₂ ≠ 0 →
  (∀ h, W (GL2LocalData.em h) ≠ 0 → ∃ x, ∃ u ∈ S, h = uni2 x * u) →
  (∀ x, ∀ u ∈ S, W (GL2LocalData.em (uni2 x * u)) = (ψ x : ℂ) * C₁) →
  (∀ x, ∀ u ∈ S, Wt (uni2 x * u) = ((ψ⁻¹ x : Circle) : ℂ) * C₂) →
  ∃ κ : ℂ, κ ≠ 0 ∧ ∀ s : ℂ, GL2LocalData.zetaGL3GL2 ψ W Wt s = κ := by
  intro F _ _ _ _ _ _ ψ W Wt S C₁ C₂ hS h1 hSK hC₁ hC₂ hsup hW hWt
  haveI : SecondCountableTopology (GL (Fin 2) F) := secondCountable_GL2
  have hTm : MeasurableSet (tSet S) := (isOpen_tSet hS).measurableSet
  obtain ⟨hT0, hTt⟩ := mIw_tSet_pos_finite ψ hS h1 hSK
  have hreal : (GL2LocalData.mIw ψ).real (tSet S) ≠ 0 := (ENNReal.toReal_pos hT0 hTt).ne'
  refine ⟨((GL2LocalData.mIw ψ).real (tSet S) : ℂ) * (C₁ * C₂), ?_, fun s => ?_⟩
  · exact mul_ne_zero (by exact_mod_cast hreal) (mul_ne_zero hC₁ hC₂)
  have key : ∀ p : Fˣ × Fˣ × GL (Fin 2) F, p.2.2 ∈ GL2LocalData.K2 F →
      GL2LocalData.iw W Wt s p = (tSet S).indicator (fun _ => C₁ * C₂) p := by
    intro p hk
    by_cases hp : p ∈ tSet S
    · rw [Set.indicator_of_mem hp]
      obtain ⟨m1, m2⟩ := modulus_of_mem_tSet hSK hp
      obtain ⟨-, x, u, hu, h⟩ := hp
      have h' : dg2 (p.1 * p.2.1) p.2.1 * p.2.2 = uni2 x * u := h
      have hψ : (ψ x : ℂ) * ((ψ⁻¹ x : Circle) : ℂ) = 1 := by
        rw [AddChar.inv_apply', Circle.coe_inv]
        exact mul_inv_cancel₀ (Circle.coe_ne_zero _)
      unfold GL2LocalData.iw
      rw [h', hW x u hu, hWt x u hu]
      simp only [mp, m1, m2, NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow, mul_one]
      linear_combination (C₁ * C₂) * hψ
    · rw [Set.indicator_of_notMem hp]
      have h0 : W (GL2LocalData.em (iwPt p)) = 0 := by
        by_contra hne
        exact hp ⟨hk, hsup _ hne⟩
      have h0' : W (GL2LocalData.em (dg2 (p.1 * p.2.1) p.2.1 * p.2.2)) = 0 := h0
      unfold GL2LocalData.iw
      rw [h0']
      simp
  unfold GL2LocalData.zetaGL3GL2
  rw [integral_congr_ae ((ae_mem_maximal_compact ψ).mono key), integral_indicator_const _ hTm, Complex.real_smul]
