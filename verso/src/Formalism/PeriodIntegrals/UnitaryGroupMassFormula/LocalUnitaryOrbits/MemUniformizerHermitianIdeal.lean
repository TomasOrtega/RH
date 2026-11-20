import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.UnifExHolds

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory Topology
  Filter
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

/- English proof (translation)
Rewrite using `[Algebra.smul_def]`. Both sides reduce to the same expression.
-/
theorem smul_eq_sc (r : Fv F v) (x : Fv F v ⊗[F] E) : r • x = sc (E := E) v r * x := by
  rw [Algebra.smul_def]
  rfl

/- English proof (translation)
Unfold `sc`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul]`.
-/
theorem sc_mul (r s : Fv F v) : sc (E := E) v r * sc (E := E) v s = sc (E := E) v (r * s) := by
  unfold sc
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sc_one : sc (E := E) v (1 : Fv F v) = 1 := rfl

/- English proof (translation)
Unfold `hN`. Rewrite using `[PI.VolStabSW.mem_smulSub]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, hp, rfl⟩ i j`. Use `⟨(p : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j, hp i j, ?_⟩` and prove the remaining obligations.

Rewrite using `[PI.VolStabSW.coe_hermSMul, Matrix.smul_apply, pow_one, smul_eq_sc]`. Introduce `hz`. Use `⟨ϖ⁻¹ • z, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j`. Take `⟨c, hc, e⟩` from `hz i j`.

Use `show ((ϖ⁻¹ • z : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j ∈ OEv (E := E) v`. Rewrite using `[PI.VolStabSW.coe_hermSMul, Matrix.smul_apply, e, smul_eq_sc, ← mul_assoc, sc_mul, inv_mul_cancel₀ h0, sc_one, one_mul]`. Conclude with `hc`. Rewrite using `[pow_one, smul_smul, mul_inv_cancel₀ h0, one_smul]`.
-/
theorem mem_uniformizer_hermitian_ideal (ϖ : Fv F v) (h0 : ϖ ≠ 0) (a : ℕ) (z : HermR (Fv F v) σ a) :
    z ∈ hN σ v ϖ a 0 ↔ ∀ i j, (z : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j ∈ PO (E := E) v ϖ := by
  unfold hN
  rw [PI.VolStabSW.mem_smulSub]
  constructor
  · rintro ⟨p, hp, rfl⟩ i j
    refine ⟨(p : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j, hp i j, ?_⟩
    rw [PI.VolStabSW.coe_hermSMul, Matrix.smul_apply, pow_one, smul_eq_sc]
  · intro hz
    refine ⟨ϖ⁻¹ • z, ?_, ?_⟩
    · intro i j
      obtain ⟨c, hc, e⟩ := hz i j
      show ((ϖ⁻¹ • z : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j ∈ OEv (E := E) v
      rw [PI.VolStabSW.coe_hermSMul, Matrix.smul_apply, e, smul_eq_sc, ← mul_assoc, sc_mul,
        inv_mul_cancel₀ h0, sc_one, one_mul]
      exact hc
    · rw [pow_one, smul_smul, mul_inv_cancel₀ h0, one_smul]

/- English proof (translation)
The claim follows from `(latLoc (E := E) v Λ).smul_mem ⟨r, hr⟩ hx`.
-/
theorem latLoc_smul {r : Fv F v} (hr : r ∈ v.adicCompletionIntegers F) {x : Fin n → Fv F v ⊗[F] E}
    (hx : x ∈ latLoc (E := E) v Λ) : r • x ∈ latLoc (E := E) v Λ :=
  (latLoc (E := E) v Λ).smul_mem ⟨r, hr⟩ hx

/- English proof (translation)
Introduce `i` and use `latLoc_smul v Λ hr (hx i)`.
-/
theorem lamS_smul {a : ℕ} {r : Fv F v} (hr : r ∈ v.adicCompletionIntegers F) {x : TupV (E := E) v n a}
    (hx : x ∈ lamS v Λ a) : r • x ∈ lamS v Λ a :=
  fun i => latLoc_smul v Λ hr (hx i)

/- English proof (translation)
Introduce `hG hW hH hfib ϖ hϖ`. Establish `hG'` using `hG`. Take `⟨hS, hL, hSD, hUn, ha, hP, hdet⟩` from `hG`. Establish `hσ : ∀ x, σ (σ x) = x` using `PI.VolStabSW.sigma_invol σ hS.1.2.2.2`. Establish `hJ : ∀ i j, σ (J j i) = J i j` using `hS.2.1.1`.

Take `⟨h0, hπ, hint⟩` from `unif_spec v ϖ hϖ`. Take `⟨hLo, hLc⟩` from `h1 hL`. Take `⟨hHo', hHc'⟩` from `h2`. Use `PI.VolStabSW.secondCountable_Fv F v` as an intermediate fact. Use `PI.VolStabSW.locallyCompact_Fv F v` as an intermediate fact.

Establish `: SecondCountableTopology (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))` using `inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Fv F v ⊗[F] E))`. Establish `: T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))` using `inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))`. Establish `: LocallyCompactSpace (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))` using `inferInstanceAs (LocallyCompactSpace (Fin a → Fin a → Fv F v ⊗[F] E))`. Establish `: SecondCountableTopology (HermR (Fv F v) σ a)` using `TopologicalSpace.Subtype.secondCountableTopology _`. Establish `hμ : SdW F E σ n J (Fv F v) (psiV F ψ v) a (dX σ J ψ v a)`.

Unfold `dX`. Rewrite using `[dif_pos hW]`. Conclude with `hW.choose_spec`. Establish `hν : SdHerm F E σ (Fv F v) (psiV F ψ v) a (dT σ ψ v a)`. Unfold `dT`.

Rewrite using `[dif_pos hH]`. Conclude with `hH.choose_spec`. Use `hμ.1` as an intermediate fact. Use `hν.1` as an intermediate fact. Establish `hfibC : IsOm σ J ψ v a (omFam σ J ψ v a)`.

Unfold `omFam`. Rewrite using `[dif_pos hfib]`. Conclude with `hfib.choose_spec`. Establish `hTm` using `PI.VolStabSW.gramR_mem (Fv F v) σ hσ J hJ Y`. Establish `hom : omAt σ J ψ v (gramR (Fv F v) σ J Y) = omFam σ J ψ v a (PI.VolStabSW.gramH (Fv F v) σ hσ J hJ Y)`.

Unfold `omAt`. Rewrite using `[dif_pos hTm]`. Both sides reduce to the same expression. Rewrite using `[hom]`. Use `set G := PI.VolStabSW.gramH (n := a) (Fv F v) σ hσ J hJ with hGdef`.

Use `set T := G Y with hTdef`. Use `set fb := omFam σ J ψ v a with hfb`. Establish `hΛL : lamN v Λ ϖ a 0 ≤ lamS v Λ a`. Introduce `x hx`. Take `⟨p, hp, rfl⟩` from `(PI.VolStabSW.mem_smulSub _ _ _).1 hx`.

Conclude with `lamS_smul v Λ (pow_mem hint _) hp`. Establish `hΛo : ∀ k, IsOpen (lamN v Λ ϖ a k : Set (TupV (E` using `E) v n a)) := fun k => PI.VolStabSW.isOpen_smulSub _ (pow_ne_zero _ h0) _ hLo`. Establish `hΛc : ∀ k, IsCompact (lamN v Λ ϖ a k : Set (TupV (E` using `E) v n a)) := fun k => PI.VolStabSW.isCompact_smulSub _ _ hLc`. Establish `hΛa : Antitone (lamN v Λ ϖ a)`. Introduce `m k hmk x hx`.

Simplify using `only [lamN, PI.VolStabSW.mem_smulSub] at hx ⊢`. Take `⟨p, hp, rfl⟩` from `hx`. Use `⟨ϖ ^ (k - m) • p, lamS_smul v Λ (pow_mem hint _) hp, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_smul, ← pow_add]`. Use `congr 2`.

Use linear arithmetic over natural numbers and integers. Establish `hHo : ∀ k, IsOpen (hN σ v ϖ a k : Set (HermR (Fv F v) σ a))` using `fun k => PI.VolStabSW.isOpen_smulSub _ (pow_ne_zero _ h0) _ hHo'`. Establish `hHc : ∀ k, IsCompact (hN σ v ϖ a k : Set (HermR (Fv F v) σ a))` using `fun k => PI.VolStabSW.isCompact_smulSub _ _ hHc'`. Establish `hHb : ∀ N' ∈ 𝓝 (0 : HermR (Fv F v) σ a), ∃ k, (hN σ v ϖ a k : Set (HermR (Fv F v) σ a)) ⊆ N'`. Introduce `N hN'`.

Take `⟨k, hk⟩` from `PI.VolStabSW.eventually_smul_sub (hermOE σ v a : Set (HermR (Fv F v) σ a)) hHc' (fun k => ϖ ^ (k + 1)) (hπ.comp (tendsto_add_atTop_nat 1)) N hN'`. Use `⟨k, ?_⟩` and prove the remaining obligations. Simplify using `only [hN, PI.VolStabSW.coe_smulSub]`. Introduce and unpack `_ ⟨p, hp, rfl⟩`. Conclude with `hk p hp`.

Use `set Nb : Set (HermR (Fv F v) σ a) := {S | IsUnit (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)).det} with hNbdef`. Establish `hTu : T ∈ Nb`. Take `⟨w, -, -, hw⟩` from `hdet`. Conclude with `IsUnit.of_mul_eq_one _ hw`. Establish `hNb : Nb ∈ 𝓝 T` using `(PI.VolStabSW.isOpen_unitHerm (Fv F v) (PI.VolStabSW.isOpen_units_Fv F v) σ a).mem_nhds hTu`.

Establish `hNbU : ∀ x ∈ LamT v Λ a, G x ∈ Nb → x ∈ IndepV (E` using `E) (n := n) v a := fun x _ hx => PI.VolStabSW.linIndep_of_isUnit_det (Fv F v) σ J x hx`. Establish `hLcl : IsClosed (LamT v Λ a)` using `AddSubgroup.isClosed_of_isOpen (lamS v Λ a) hLo`. Establish `e` using `PI.VolStabSW.fibLatGen_holds _ _ _ (dX σ J ψ v a) (dT σ ψ v a) hμ.1 hν.1 (gramR (Fv F v) σ J) Subtype.val Subtype.val_injective G (PI.VolStabSW.continuous_gramH (Fv F v) σ hσ J hJ) (fun _ => rfl) (IndepV (E := E) (n := n) v a) Set.univ fb hfibC T Filter.univ_mem (lamS v Λ a) hLo …`. Establish `hA : LamT v Λ a ∩ G ⁻¹' {z | z - T ∈ hN σ v ϖ a 0} = LamT v Λ a ∩ NearT v σ J ϖ (gramR (Fv F v) σ J Y)`. Use extensionality with `x`.

Simplify using `only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]`. Rewrite using `[mem_uniformizer_hermitian_ideal σ v ϖ h0]`. Both sides reduce to the same expression. Establish `hHP : (hN σ v ϖ a 0 : Set (HermR (Fv F v) σ a)) = HermP v σ a ϖ`. Use extensionality with `z`.

Conclude with `mem_uniformizer_hermitian_ideal σ v ϖ h0 a z`. Rewrite `e` using `[hA, hHP]`. Establish `hLm : MeasurableSet (LamT v Λ a)` using `hLo.measurableSet`. Establish `hind : (LamT v Λ a).indicator (1 : TupV (E` using `E) v n a → ℂ) = fun x => (((LamT v Λ a).indicator (1 : TupV (E := E) v n a → ℝ) x : ℝ) : ℂ) := by`. Use function extensionality and compare the values at `x`.

Apply the tactic sequence `by_cases hx : x ∈ LamT v Λ a <;> simp [Set.indicator, hx]`. Rewrite `e` using `[hind, integral_complex_ofReal, integral_indicator_one hLm]`. Establish `e'` using `Complex.ofReal_injective e`. Establish `hGc : Continuous G` using `PI.VolStabSW.continuous_gramH (Fv F v) σ hσ J hJ`. Take `⟨k, hk⟩` from `hHb _ ((continuous_const.add continuous_id : Continuous fun w : HermR (Fv F v) σ a => T + w).continuousAt.preimage_mem_nhds (by simpa using hNb))`.

Use `set Q := LamT v Λ a ∩ G ⁻¹' {z | z - T ∈ hN σ v ϖ a k} with hQdef`. Establish `hQo : IsOpen Q` using `hLo.inter (((hHo k).preimage (continuous_id.sub continuous_const)).preimage hGc)`. Establish `hQcl : IsClosed Q` using `hLcl.inter (((AddSubgroup.isClosed_of_isOpen _ (hHo k)).preimage (continuous_id.sub continuous_const)).preimage hGc)`. Establish `hQc : IsCompact Q` using `hLc.of_isClosed_subset hQcl Set.inter_subset_left`. Establish `hQU : Q ⊆ IndepV (E` using `E) (n := n) v a := by`.

Introduce and unpack `x ⟨hx, hxk⟩`. Use `hNbU x hx ?_` and prove the remaining obligations. Use `hk hxk` as an intermediate fact. Establish `e2 : G x = T + (G x - T)` using `by abel`. Rewrite using `[e2]`.

Conclude with `this`. Use `set φ : TupV (E := E) v n a → ℝ := Q.indicator (fun _ => (1 : ℝ)) with hφdef`. Establish `hφc : Continuous φ` using `(LocallyConstant.indicator (LocallyConstant.const _ (1 : ℝ)) ⟨hQcl, hQo⟩).isLocallyConstant.continuous`. Establish `hφs : HasCompactSupport φ` using `HasCompactSupport.intro' hQc hQcl fun x hx => Set.indicator_of_notMem hx _`. Establish `hφU : tsupport φ ⊆ IndepV (E` using `E) (n := n) v a := (closure_minimal Set.support_indicator_subset hQcl).trans hQU`.

Take `⟨hint', -⟩` from `hfibC.2.2 φ hφc hφs hφU`. Establish `hQm : MeasurableSet Q` using `hQo.measurableSet`. Establish `hfinQ : fb T Q ≠ ⊤`. Establish `h` using `hint' T (Set.mem_univ _)`. Rewrite `h` using `[hφdef, integrable_indicator_iff hQm]`.

Conclude with `((integrableOn_const_iff (C := (1 : ℝ))).1 h).resolve_left (by simp) |>.ne`. Establish `hsub : LamT v Λ a ⊆ Q ∪ (gramR (Fv F v) σ J ⁻¹' {(T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))} ∩ IndepV (E` using `E) (n := n) v a)ᶜ := by`. Introduce `x hx`. Distinguish the cases in `h : x ∈ gramR (Fv F v) σ J ⁻¹' {(T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))} ∩ IndepV (E := E) (n := n) v a`. Use `left`.

Use `⟨hx, ?_⟩` and prove the remaining obligations. Establish `hGx : G x = T` using `Subtype.ext h.1`. Use `show G x - T ∈ hN σ v ϖ a k`. Rewrite using `[hGx, sub_self]`. Conclude with `zero_mem _`.

Use `right`. Conclude with `h`. Establish `hz` using `hfibC.1 T`. Establish `hfin : fb T (LamT v Λ a) ≠ ⊤`. Use `((measure_mono hsub).trans_lt (lt_of_le_of_lt (measure_union_le _ _) ?_)).ne` and prove the remaining obligations.

Rewrite using `[hz, add_zero]`. Conclude with `hfinQ.lt_top`. Establish `hR : dX σ J ψ v a (LamT v Λ a ∩ NearT v σ J ϖ (gramR (Fv F v) σ J Y)) / dT σ ψ v a (HermP v σ a ϖ) ≠ ⊤`. Use `(ENNReal.div_lt_top ?_ ?_).ne` and prove the remaining obligations. Conclude with `((measure_mono Set.inter_subset_left).trans_lt hLc.measure_lt_top).ne`.

Rewrite using `[← hHP]`. Conclude with `((hHo 0).measure_pos _ ⟨0, (hN σ v ϖ a 0).zero_mem⟩).ne'`. Rewrite `e'` using `[measureReal_def]`. Conclude with `(ENNReal.toReal_eq_toReal_iff' hfin hR).1 e'`.
-/
theorem fibU'_of (a : ℕ) (Y : TupV (E := E) v n a) (h1 : LamOC v Λ a) (h2 : HermOC σ v a)
    (h3 : FibHens σ J ψ v Λ a Y) : FibU' σ J ψ v Λ a Y := by
  intro hG hW hH hfib ϖ hϖ
  have hG' := hG
  obtain ⟨hS, hL, hSD, hUn, ha, hP, hdet⟩ := hG
  have hσ : ∀ x, σ (σ x) = x := PI.VolStabSW.sigma_invol σ hS.1.2.2.2
  have hJ : ∀ i j, σ (J j i) = J i j := hS.2.1.1
  obtain ⟨h0, hπ, hint⟩ := unif_spec v ϖ hϖ
  obtain ⟨hLo, hLc⟩ := h1 hL
  obtain ⟨hHo', hHc'⟩ := h2
  have := PI.VolStabSW.secondCountable_Fv F v
  have := PI.VolStabSW.locallyCompact_Fv F v
  have : SecondCountableTopology (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Fv F v ⊗[F] E))
  have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  have : LocallyCompactSpace (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin a → Fv F v ⊗[F] E))
  have : SecondCountableTopology (HermR (Fv F v) σ a) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have hμ : SdW F E σ n J (Fv F v) (psiV F ψ v) a (dX σ J ψ v a) := by
    unfold dX; rw [dif_pos hW]; exact hW.choose_spec
  have hν : SdHerm F E σ (Fv F v) (psiV F ψ v) a (dT σ ψ v a) := by
    unfold dT; rw [dif_pos hH]; exact hH.choose_spec
  have := hμ.1
  have := hν.1
  have hfibC : IsOm σ J ψ v a (omFam σ J ψ v a) := by
    unfold omFam; rw [dif_pos hfib]; exact hfib.choose_spec
  have hTm := PI.VolStabSW.gramR_mem (Fv F v) σ hσ J hJ Y
  have hom : omAt σ J ψ v (gramR (Fv F v) σ J Y) =
      omFam σ J ψ v a (PI.VolStabSW.gramH (Fv F v) σ hσ J hJ Y) := by
    unfold omAt; rw [dif_pos hTm]; rfl
  rw [hom]
  set G := PI.VolStabSW.gramH (n := a) (Fv F v) σ hσ J hJ with hGdef
  set T := G Y with hTdef
  set fb := omFam σ J ψ v a with hfb

  have hΛL : lamN v Λ ϖ a 0 ≤ lamS v Λ a := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := (PI.VolStabSW.mem_smulSub _ _ _).1 hx
    exact lamS_smul v Λ (pow_mem hint _) hp
  have hΛo : ∀ k, IsOpen (lamN v Λ ϖ a k : Set (TupV (E := E) v n a)) := fun k =>
    PI.VolStabSW.isOpen_smulSub _ (pow_ne_zero _ h0) _ hLo
  have hΛc : ∀ k, IsCompact (lamN v Λ ϖ a k : Set (TupV (E := E) v n a)) := fun k =>
    PI.VolStabSW.isCompact_smulSub _ _ hLc
  have hΛa : Antitone (lamN v Λ ϖ a) := by
    intro m k hmk x hx
    simp only [lamN, PI.VolStabSW.mem_smulSub] at hx ⊢
    obtain ⟨p, hp, rfl⟩ := hx
    refine ⟨ϖ ^ (k - m) • p, lamS_smul v Λ (pow_mem hint _) hp, ?_⟩
    rw [smul_smul, ← pow_add]
    congr 2
    omega
  have hHo : ∀ k, IsOpen (hN σ v ϖ a k : Set (HermR (Fv F v) σ a)) := fun k =>
    PI.VolStabSW.isOpen_smulSub _ (pow_ne_zero _ h0) _ hHo'
  have hHc : ∀ k, IsCompact (hN σ v ϖ a k : Set (HermR (Fv F v) σ a)) := fun k =>
    PI.VolStabSW.isCompact_smulSub _ _ hHc'
  have hHb : ∀ N' ∈ 𝓝 (0 : HermR (Fv F v) σ a), ∃ k, (hN σ v ϖ a k : Set (HermR (Fv F v) σ a)) ⊆ N' := by
    intro N hN'
    obtain ⟨k, hk⟩ := PI.VolStabSW.eventually_smul_sub (hermOE σ v a : Set (HermR (Fv F v) σ a))
      hHc' (fun k => ϖ ^ (k + 1)) (hπ.comp (tendsto_add_atTop_nat 1)) N hN'
    refine ⟨k, ?_⟩
    simp only [hN, PI.VolStabSW.coe_smulSub]
    rintro _ ⟨p, hp, rfl⟩
    exact hk p hp

  set Nb : Set (HermR (Fv F v) σ a) := {S | IsUnit (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)).det}
    with hNbdef
  have hTu : T ∈ Nb := by
    obtain ⟨w, -, -, hw⟩ := hdet
    exact IsUnit.of_mul_eq_one _ hw
  have hNb : Nb ∈ 𝓝 T :=
    (PI.VolStabSW.isOpen_unitHerm (Fv F v) (PI.VolStabSW.isOpen_units_Fv F v) σ a).mem_nhds hTu
  have hNbU : ∀ x ∈ LamT v Λ a, G x ∈ Nb → x ∈ IndepV (E := E) (n := n) v a := fun x _ hx =>
    PI.VolStabSW.linIndep_of_isUnit_det (Fv F v) σ J x hx
  have hLcl : IsClosed (LamT v Λ a) := AddSubgroup.isClosed_of_isOpen (lamS v Λ a) hLo
  have e := PI.VolStabSW.fibLatGen_holds _ _ _ (dX σ J ψ v a) (dT σ ψ v a) hμ.1 hν.1
    (gramR (Fv F v) σ J) Subtype.val Subtype.val_injective G
    (PI.VolStabSW.continuous_gramH (Fv F v) σ hσ J hJ) (fun _ => rfl) (IndepV (E := E) (n := n) v a)
    Set.univ fb hfibC T Filter.univ_mem (lamS v Λ a) hLo hLc (lamN v Λ ϖ a) (hN σ v ϖ a) hΛL hΛo hΛc
    hΛa hHo hHc hHb (LamT v Λ a) subset_rfl (fun y hy Z hZ => (lamS v Λ a).add_mem hy (hΛL hZ))
    hLo hLcl Nb hNb hNbU (fun y hy hyT => h3 hG' ϖ hϖ hσ hJ y hy hyT)
  have hA : LamT v Λ a ∩ G ⁻¹' {z | z - T ∈ hN σ v ϖ a 0} =
      LamT v Λ a ∩ NearT v σ J ϖ (gramR (Fv F v) σ J Y) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
    rw [mem_uniformizer_hermitian_ideal σ v ϖ h0]
    rfl
  have hHP : (hN σ v ϖ a 0 : Set (HermR (Fv F v) σ a)) = HermP v σ a ϖ := by
    ext z
    exact mem_uniformizer_hermitian_ideal σ v ϖ h0 a z
  rw [hA, hHP] at e
  have hLm : MeasurableSet (LamT v Λ a) := hLo.measurableSet
  have hind : (LamT v Λ a).indicator (1 : TupV (E := E) v n a → ℂ) =
      fun x => (((LamT v Λ a).indicator (1 : TupV (E := E) v n a → ℝ) x : ℝ) : ℂ) := by
    funext x
    by_cases hx : x ∈ LamT v Λ a <;> simp [Set.indicator, hx]
  rw [hind, integral_complex_ofReal, integral_indicator_one hLm] at e
  have e' := Complex.ofReal_injective e

  have hGc : Continuous G := PI.VolStabSW.continuous_gramH (Fv F v) σ hσ J hJ
  obtain ⟨k, hk⟩ := hHb _ ((continuous_const.add continuous_id :
    Continuous fun w : HermR (Fv F v) σ a => T + w).continuousAt.preimage_mem_nhds
      (by simpa using hNb))
  set Q := LamT v Λ a ∩ G ⁻¹' {z | z - T ∈ hN σ v ϖ a k} with hQdef
  have hQo : IsOpen Q :=
    hLo.inter (((hHo k).preimage (continuous_id.sub continuous_const)).preimage hGc)
  have hQcl : IsClosed Q :=
    hLcl.inter (((AddSubgroup.isClosed_of_isOpen _ (hHo k)).preimage
      (continuous_id.sub continuous_const)).preimage hGc)
  have hQc : IsCompact Q := hLc.of_isClosed_subset hQcl Set.inter_subset_left
  have hQU : Q ⊆ IndepV (E := E) (n := n) v a := by
    rintro x ⟨hx, hxk⟩
    refine hNbU x hx ?_
    have := hk hxk
    have e2 : G x = T + (G x - T) := by abel
    rw [e2]
    exact this
  set φ : TupV (E := E) v n a → ℝ := Q.indicator (fun _ => (1 : ℝ)) with hφdef
  have hφc : Continuous φ :=
    (LocallyConstant.indicator (LocallyConstant.const _ (1 : ℝ)) ⟨hQcl, hQo⟩).isLocallyConstant.continuous
  have hφs : HasCompactSupport φ :=
    HasCompactSupport.intro' hQc hQcl fun x hx => Set.indicator_of_notMem hx _
  have hφU : tsupport φ ⊆ IndepV (E := E) (n := n) v a :=
    (closure_minimal Set.support_indicator_subset hQcl).trans hQU
  obtain ⟨hint', -⟩ := hfibC.2.2 φ hφc hφs hφU
  have hQm : MeasurableSet Q := hQo.measurableSet
  have hfinQ : fb T Q ≠ ⊤ := by
    have h := hint' T (Set.mem_univ _)
    rw [hφdef, integrable_indicator_iff hQm] at h
    exact ((integrableOn_const_iff (C := (1 : ℝ))).1 h).resolve_left (by simp) |>.ne
  have hsub : LamT v Λ a ⊆ Q ∪ (gramR (Fv F v) σ J ⁻¹' {(T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))} ∩
      IndepV (E := E) (n := n) v a)ᶜ := by
    intro x hx
    by_cases h : x ∈ gramR (Fv F v) σ J ⁻¹' {(T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))} ∩
      IndepV (E := E) (n := n) v a
    · left
      refine ⟨hx, ?_⟩
      have hGx : G x = T := Subtype.ext h.1
      show G x - T ∈ hN σ v ϖ a k
      rw [hGx, sub_self]
      exact zero_mem _
    · right
      exact h
  have hz := hfibC.1 T
  have hfin : fb T (LamT v Λ a) ≠ ⊤ := by
    refine ((measure_mono hsub).trans_lt (lt_of_le_of_lt (measure_union_le _ _) ?_)).ne
    rw [hz, add_zero]
    exact hfinQ.lt_top
  have hR : dX σ J ψ v a (LamT v Λ a ∩ NearT v σ J ϖ (gramR (Fv F v) σ J Y)) /
      dT σ ψ v a (HermP v σ a ϖ) ≠ ⊤ := by
    refine (ENNReal.div_lt_top ?_ ?_).ne
    · exact ((measure_mono Set.inter_subset_left).trans_lt hLc.measure_lt_top).ne
    · rw [← hHP]
      exact ((hHo 0).measure_pos _ ⟨0, (hN σ v ϖ a 0).zero_mem⟩).ne'
  rw [measureReal_def] at e'
  exact (ENNReal.toReal_eq_toReal_iff' hfin hR).1 e'

end PI.OmLocU
