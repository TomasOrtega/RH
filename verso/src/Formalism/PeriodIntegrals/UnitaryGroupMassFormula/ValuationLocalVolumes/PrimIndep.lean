import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CrossMSmulRight

noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory Topology Filter
  PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

/- English proof (translation)
Use `show LinearIndependent (Fv F v ⊗[F] E) X`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc i`. Take `⟨ϖ, hϖ⟩` from `unifEx_holds v`. Take `⟨h0, hπ, -⟩` from `unif_spec v ϖ hϖ`.

Establish `hm : ∀ m : ℕ, sc (E` using `E) v (ϖ ^ m)⁻¹ * c i ∈ OEv (E := E) v := by`. Introduce `m`. Use `hX.2 (fun j => sc (E := E) v (ϖ ^ m)⁻¹ * c j) ?_ i` and prove the remaining obligations. Establish `e : (∑ j, (sc (E` using `E) v (ϖ ^ m)⁻¹ * c j) • X j) = sc (E := E) v (ϖ ^ m)⁻¹ • ∑ j, c j • X j := by`. Rewrite using `[Finset.smul_sum]`.

Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[mul_smul]`. Rewrite using `[e, hc, smul_zero]`. Conclude with `(latLoc (E := E) v Λ).zero_mem`. Assume the negation of the conclusion as `hne`.

Establish `hN : {x : Fv F v ⊗[F] E | x ≠ c i} ∈ 𝓝 (0 : Fv F v ⊗[F] E)` using `isOpen_ne.mem_nhds (Ne.symm hne)`. Take `⟨k, hk⟩` from `PI.VolStabSW.eventually_smul_sub (OEv (E := E) v) (isCompact_oEv v) (fun k => ϖ ^ k) hπ _ hN`. Apply `hk _ (hm k)` to reduce the goal to its premises. Use `show ϖ ^ k • (sc (E := E) v (ϖ ^ k)⁻¹ * c i) = c i`. Rewrite using `[smul_eq_sc, ← mul_assoc, sc_mul, mul_inv_cancel₀ (pow_ne_zero _ h0), sc_one, one_mul]`.
-/
theorem prim_indep {a : ℕ} (X : TupV (E := E) v n a) (hX : IsPrim v Λ X) :
    X ∈ IndepV (E := E) (n := n) v a := by
  show LinearIndependent (Fv F v ⊗[F] E) X
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  obtain ⟨ϖ, hϖ⟩ := unifEx_holds v
  obtain ⟨h0, hπ, -⟩ := unif_spec v ϖ hϖ
  have hm : ∀ m : ℕ, sc (E := E) v (ϖ ^ m)⁻¹ * c i ∈ OEv (E := E) v := by
    intro m
    refine hX.2 (fun j => sc (E := E) v (ϖ ^ m)⁻¹ * c j) ?_ i
    have e : (∑ j, (sc (E := E) v (ϖ ^ m)⁻¹ * c j) • X j) = sc (E := E) v (ϖ ^ m)⁻¹ • ∑ j, c j • X j := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [mul_smul]
    rw [e, hc, smul_zero]
    exact (latLoc (E := E) v Λ).zero_mem
  by_contra hne
  have hN : {x : Fv F v ⊗[F] E | x ≠ c i} ∈ 𝓝 (0 : Fv F v ⊗[F] E) := isOpen_ne.mem_nhds (Ne.symm hne)
  obtain ⟨k, hk⟩ := PI.VolStabSW.eventually_smul_sub (OEv (E := E) v) (isCompact_oEv v) (fun k => ϖ ^ k) hπ _ hN
  apply hk _ (hm k)
  show ϖ ^ k • (sc (E := E) v (ϖ ^ k)⁻¹ * c i) = c i
  rw [smul_eq_sc, ← mul_assoc, sc_mul, mul_inv_cancel₀ (pow_ne_zero _ h0), sc_one, one_mul]

def FibHensP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ → ∀ (hσ : ∀ x, σ (σ x) = x)
    (hJ : ∀ i j, σ (J j i) = J i j),
    ∀ y ∈ PrimT v Λ a, PI.VolStabSW.gramH (Fv F v) σ hσ J hJ y -
        PI.VolStabSW.gramH (Fv F v) σ hσ J hJ Y ∈ hN σ v ϖ a 0 →
      ∃ D : TupV (E := E) v n a →+ HermR (Fv F v) σ a,
        (∀ k, (lamN v Λ ϖ a k).map D = hN σ v ϖ a k) ∧
        ∀ k, ∀ Z ∈ lamN v Λ ϖ a 0, ∀ W ∈ lamN v Λ ϖ a k,
          PI.VolStabSW.gramH (Fv F v) σ hσ J hJ (y + Z + W) -
            PI.VolStabSW.gramH (Fv F v) σ hσ J hJ (y + Z) - D W ∈ hN σ v ϖ a (k + 1)

/- English proof (translation)
Introduce `hG hW hH hfib ϖ hϖ`. Establish `hG'` using `hG`. Take `⟨hS, hL, hSD, hUn, ha, hP⟩` from `hG`. Establish `hσ : ∀ x, σ (σ x) = x` using `PI.VolStabSW.sigma_invol σ hS.1.2.2.2`. Establish `hJ : ∀ i j, σ (J j i) = J i j` using `hS.2.1.1`.

Take `⟨h0, hπ, hint⟩` from `unif_spec v ϖ hϖ`. Take `⟨hLo, hLc⟩` from `lamOC_holds v Λ a hL`. Take `⟨hHo', hHc'⟩` from `hermOC_holds v σ a`. Use `PI.VolStabSW.secondCountable_Fv F v` as an intermediate fact. Use `PI.VolStabSW.locallyCompact_Fv F v` as an intermediate fact.

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

Establish `hPcos : ∀ y ∈ PrimT v Λ a, ∀ Z ∈ lamN v Λ ϖ a 0, y + Z ∈ PrimT v Λ a` using `hC hS hL hSD hUn ϖ hϖ`. Establish `hPsub : PrimT v Λ a ⊆ LamT v Λ a` using `fun x hx => hx.1`. Establish `hPo : IsOpen (PrimT v Λ a)`. Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `y hy`.

Use `Filter.mem_of_superset (((hΛo 0).preimage (continuous_id.sub continuous_const)).mem_nhds (show y - y ∈ (lamN v Λ ϖ a 0 : Set (TupV (E := E) v n a)) by rw [sub_self]; exact zero_mem _)) ?_` and prove the remaining obligations. Introduce `x hx`. Use `hPcos y hy (x - y) hx` as an intermediate fact. Rewrite `this` using `[show y + (x - y) = x by abel]`. Then use the resulting hypothesis. Establish `hPcl : IsClosed (PrimT v Λ a)`.

Rewrite using `[← isOpen_compl_iff, isOpen_iff_mem_nhds]`. Introduce `y hy`. Use `Filter.mem_of_superset (((hΛo 0).preimage (continuous_id.sub continuous_const)).mem_nhds (show y - y ∈ (lamN v Λ ϖ a 0 : Set (TupV (E := E) v n a)) by rw [sub_self]; exact zero_mem _)) ?_` and prove the remaining obligations. Introduce `x hx hxP`. Apply `hy` to reduce the goal to its premises.

Use `hPcos x hxP (-(x - y)) (neg_mem hx)` as an intermediate fact. Rewrite `this` using `[show x + -(x - y) = y by abel]`. Then use the resulting hypothesis. Establish `hPc : IsCompact (PrimT v Λ a)` using `hLc.of_isClosed_subset hPcl hPsub`. Establish `hPU : PrimT v Λ a ⊆ IndepV (E` using `E) (n := n) v a := fun x hx => prim_indep v Λ x hx`. Establish `e` using `PI.VolStabSW.fibLatGen_holds _ _ _ (dX σ J ψ v a) (dT σ ψ v a) hμ.1 hν.1 (gramR (Fv F v) σ J) Subtype.val Subtype.val_injective G (PI.VolStabSW.continuous_gramH (Fv F v) σ hσ J hJ) (fun _ => rfl) (IndepV (E := E) (n := n) v a) Set.univ fb hfibC T Filter.univ_mem (lamS v Λ a) hLo …`.

Establish `hA : PrimT v Λ a ∩ G ⁻¹' {z | z - T ∈ hN σ v ϖ a 0} = PrimT v Λ a ∩ NearT v σ J ϖ (gramR (Fv F v) σ J Y)`. Use extensionality with `x`. Simplify using `only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]`. Rewrite using `[mem_uniformizer_hermitian_ideal σ v ϖ h0]`. Both sides reduce to the same expression.

Establish `hHP : (hN σ v ϖ a 0 : Set (HermR (Fv F v) σ a)) = HermP v σ a ϖ`. Use extensionality with `z`. Conclude with `mem_uniformizer_hermitian_ideal σ v ϖ h0 a z`. Rewrite `e` using `[hA, hHP]`. Establish `hPm : MeasurableSet (PrimT v Λ a)` using `hPo.measurableSet`.

Establish `hind : (PrimT v Λ a).indicator (1 : TupV (E` using `E) v n a → ℂ) = fun x => (((PrimT v Λ a).indicator (1 : TupV (E := E) v n a → ℝ) x : ℝ) : ℂ) := by`. Use function extensionality and compare the values at `x`. Apply the tactic sequence `by_cases hx : x ∈ PrimT v Λ a <;> simp [Set.indicator, hx]`. Rewrite `e` using `[hind, integral_complex_ofReal, integral_indicator_one hPm]`. Establish `e'` using `Complex.ofReal_injective e`.

Use `set φ : TupV (E := E) v n a → ℝ := (PrimT v Λ a).indicator (fun _ => (1 : ℝ)) with hφdef`. Establish `hφc : Continuous φ` using `(LocallyConstant.indicator (LocallyConstant.const _ (1 : ℝ)) ⟨hPcl, hPo⟩).isLocallyConstant.continuous`. Establish `hφs : HasCompactSupport φ` using `HasCompactSupport.intro' hPc hPcl fun x hx => Set.indicator_of_notMem hx _`. Establish `hφU : tsupport φ ⊆ IndepV (E` using `E) (n := n) v a := (closure_minimal Set.support_indicator_subset hPcl).trans hPU`. Take `⟨hint', -⟩` from `hfibC.2.2 φ hφc hφs hφU`.

Establish `hfin : fb T (PrimT v Λ a) ≠ ⊤`. Establish `h` using `hint' T (Set.mem_univ _)`. Rewrite `h` using `[hφdef, integrable_indicator_iff hPm]`. Conclude with `((integrableOn_const_iff (C := (1 : ℝ))).1 h).resolve_left (by simp) |>.ne`. Establish `hR : dX σ J ψ v a (PrimT v Λ a ∩ NearT v σ J ϖ (gramR (Fv F v) σ J Y)) / dT σ ψ v a (HermP v σ a ϖ) ≠ ⊤`.

Use `(ENNReal.div_lt_top ?_ ?_).ne` and prove the remaining obligations. Conclude with `((measure_mono Set.inter_subset_left).trans_lt hPc.measure_lt_top).ne`. Rewrite using `[← hHP]`. Conclude with `((hHo 0).measure_pos _ ⟨0, (hN σ v ϖ a 0).zero_mem⟩).ne'`. Rewrite `e'` using `[measureReal_def]`.

Conclude with `(ENNReal.toReal_eq_toReal_iff' hfin hR).1 e'`.
-/
theorem fibP_of (a : ℕ) (Y : TupV (E := E) v n a) (hC : PrimCos σ J ψ v Λ a) (h3 : FibHensP σ J ψ v Λ a Y) :
    FibP σ J ψ v Λ a Y := by
  intro hG hW hH hfib ϖ hϖ
  have hG' := hG
  obtain ⟨hS, hL, hSD, hUn, ha, hP⟩ := hG
  have hσ : ∀ x, σ (σ x) = x := PI.VolStabSW.sigma_invol σ hS.1.2.2.2
  have hJ : ∀ i j, σ (J j i) = J i j := hS.2.1.1
  obtain ⟨h0, hπ, hint⟩ := unif_spec v ϖ hϖ
  obtain ⟨hLo, hLc⟩ := lamOC_holds v Λ a hL
  obtain ⟨hHo', hHc'⟩ := hermOC_holds v σ a
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

  have hPcos : ∀ y ∈ PrimT v Λ a, ∀ Z ∈ lamN v Λ ϖ a 0, y + Z ∈ PrimT v Λ a := hC hS hL hSD hUn ϖ hϖ
  have hPsub : PrimT v Λ a ⊆ LamT v Λ a := fun x hx => hx.1
  have hPo : IsOpen (PrimT v Λ a) := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    refine Filter.mem_of_superset (((hΛo 0).preimage (continuous_id.sub continuous_const)).mem_nhds
      (show y - y ∈ (lamN v Λ ϖ a 0 : Set (TupV (E := E) v n a)) by rw [sub_self]; exact zero_mem _)) ?_
    intro x hx
    have := hPcos y hy (x - y) hx
    rwa [show y + (x - y) = x by abel] at this
  have hPcl : IsClosed (PrimT v Λ a) := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y hy
    refine Filter.mem_of_superset (((hΛo 0).preimage (continuous_id.sub continuous_const)).mem_nhds
      (show y - y ∈ (lamN v Λ ϖ a 0 : Set (TupV (E := E) v n a)) by rw [sub_self]; exact zero_mem _)) ?_
    intro x hx hxP
    apply hy
    have := hPcos x hxP (-(x - y)) (neg_mem hx)
    rwa [show x + -(x - y) = y by abel] at this
  have hPc : IsCompact (PrimT v Λ a) := hLc.of_isClosed_subset hPcl hPsub
  have hPU : PrimT v Λ a ⊆ IndepV (E := E) (n := n) v a := fun x hx => prim_indep v Λ x hx
  have e := PI.VolStabSW.fibLatGen_holds _ _ _ (dX σ J ψ v a) (dT σ ψ v a) hμ.1 hν.1
    (gramR (Fv F v) σ J) Subtype.val Subtype.val_injective G
    (PI.VolStabSW.continuous_gramH (Fv F v) σ hσ J hJ) (fun _ => rfl) (IndepV (E := E) (n := n) v a)
    Set.univ fb hfibC T Filter.univ_mem (lamS v Λ a) hLo hLc (lamN v Λ ϖ a) (hN σ v ϖ a) hΛL hΛo hΛc
    hΛa hHo hHc hHb (PrimT v Λ a) hPsub hPcos
    hPo hPcl Set.univ Filter.univ_mem (fun x hx _ => hPU hx) (fun y hy hyT => h3 hG' ϖ hϖ hσ hJ y hy hyT)
  have hA : PrimT v Λ a ∩ G ⁻¹' {z | z - T ∈ hN σ v ϖ a 0} =
      PrimT v Λ a ∩ NearT v σ J ϖ (gramR (Fv F v) σ J Y) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
    rw [mem_uniformizer_hermitian_ideal σ v ϖ h0]
    rfl
  have hHP : (hN σ v ϖ a 0 : Set (HermR (Fv F v) σ a)) = HermP v σ a ϖ := by
    ext z
    exact mem_uniformizer_hermitian_ideal σ v ϖ h0 a z
  rw [hA, hHP] at e
  have hPm : MeasurableSet (PrimT v Λ a) := hPo.measurableSet
  have hind : (PrimT v Λ a).indicator (1 : TupV (E := E) v n a → ℂ) =
      fun x => (((PrimT v Λ a).indicator (1 : TupV (E := E) v n a → ℝ) x : ℝ) : ℂ) := by
    funext x
    by_cases hx : x ∈ PrimT v Λ a <;> simp [Set.indicator, hx]
  rw [hind, integral_complex_ofReal, integral_indicator_one hPm] at e
  have e' := Complex.ofReal_injective e
  set φ : TupV (E := E) v n a → ℝ := (PrimT v Λ a).indicator (fun _ => (1 : ℝ)) with hφdef
  have hφc : Continuous φ :=
    (LocallyConstant.indicator (LocallyConstant.const _ (1 : ℝ)) ⟨hPcl, hPo⟩).isLocallyConstant.continuous
  have hφs : HasCompactSupport φ :=
    HasCompactSupport.intro' hPc hPcl fun x hx => Set.indicator_of_notMem hx _
  have hφU : tsupport φ ⊆ IndepV (E := E) (n := n) v a :=
    (closure_minimal Set.support_indicator_subset hPcl).trans hPU
  obtain ⟨hint', -⟩ := hfibC.2.2 φ hφc hφs hφU
  have hfin : fb T (PrimT v Λ a) ≠ ⊤ := by
    have h := hint' T (Set.mem_univ _)
    rw [hφdef, integrable_indicator_iff hPm] at h
    exact ((integrableOn_const_iff (C := (1 : ℝ))).1 h).resolve_left (by simp) |>.ne
  have hR : dX σ J ψ v a (PrimT v Λ a ∩ NearT v σ J ϖ (gramR (Fv F v) σ J Y)) /
      dT σ ψ v a (HermP v σ a ϖ) ≠ ⊤ := by
    refine (ENNReal.div_lt_top ?_ ?_).ne
    · exact ((measure_mono Set.inter_subset_left).trans_lt hPc.measure_lt_top).ne
    · rw [← hHP]
      exact ((hHo 0).measure_pos _ ⟨0, (hN σ v ϖ a 0).zero_mem⟩).ne'
  rw [measureReal_def] at e'
  exact (ENNReal.toReal_eq_toReal_iff' hfin hR).1 e'

end PI.OmVd
