import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsLAdicCharOfUnique
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsLocCompTrivIff

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.TheRec
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AboveL.Model

section Tower

variable {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
  [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] {A : ValuationSubring Ω}
  {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)} {h : IsPlaceOver A v} {h' : IsPlaceOver A v'}

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun ⟨n, a, b, h1, h2, h3, h4⟩ => ⟨n, a, b, h1, h2, h3.symm, fun σ σ' e => (h4 σ σ' e).symm⟩, fun ⟨n, a, b, h1, h2, h3, h4⟩ => ⟨n, a, b, h1, h2, h3.symm, fun σ σ' e => (h4 σ σ' e).symm⟩⟩`.
-/
theorem restricts_iff_wdRel (x : WD h) (x' : WD h') : Restricts x x' ↔ WDRel (RingEquiv.refl Ω) x x' :=
  ⟨fun ⟨n, a, b, h1, h2, h3, h4⟩ => ⟨n, a, b, h1, h2, h3.symm, fun σ σ' e => (h4 σ σ' e).symm⟩,
    fun ⟨n, a, b, h1, h2, h3, h4⟩ => ⟨n, a, b, h1, h2, h3.symm, fun σ σ' e => (h4 σ σ' e).symm⟩⟩

/- English proof (translation)
Introduce `⟨n, a, b, h1, h2, h3, h4⟩` and use `⟨n, b, a, h2, h1, h3.symm, fun σ σ' e => (h4 σ' σ fun z => (e z).symm).symm⟩`.
-/
theorem restricts_symm {x : WD h} {x' : WD h'} : Restricts x x' → Restricts x' x :=
  fun ⟨n, a, b, h1, h2, h3, h4⟩ => ⟨n, b, a, h2, h1, h3.symm, fun σ σ' e => (h4 σ' σ fun z => (e z).symm).symm⟩

/- English proof (translation)
Take `⟨n, a, b, rfl, rfl, -⟩` from `H`. Simplify using the standard rewrite rules.
-/
theorem lpDim_eq {x : WD h} {x' : WD h'} (H : Restricts x x') : x'.lpDim = x.lpDim := by
  obtain ⟨n, a, b, rfl, rfl, -⟩ := H
  simp

/- English proof (translation)
Take `⟨n, a, b, rfl, rfl, e, -⟩` from `H`. Simplify using `[e]`.
-/
theorem monodromyZero_iff_restricts {x : WD h} {x' : WD h'} (H : Restricts x x') : x'.mono0 ↔ x.mono0 := by
  obtain ⟨n, a, b, rfl, rfl, e, -⟩ := H
  simp [e]

/- English proof (translation)
Introduce `H` and use `WD.not_mono0_lpSp le_rfl ((monodromyZero_iff_restricts H).1 (by simp))`.
-/
theorem not_restricts_sp (c : Fin 2 → ℂˣ) : ¬ Restricts (WD.lpSp h 2) (WD.mk (WDRep.diag h' c)) := fun H =>
  WD.not_mono0_lpSp le_rfl ((monodromyZero_iff_restricts H).1 (by simp))

/- English proof (translation)
Use `forall_congr' fun τ => ?_` and prove the remaining obligations. Rewrite using `[WD.charPol_mk, WD.lpDim_mk]`. Use `⟨fun e => ?_, fun e => by rw [e, LinearMap.charpoly_one]⟩` and prove the remaining obligations. Establish `h1` using `LinearMap.aeval_self_charpoly (a.ρ (ineIncl h τ))`. Rewrite `h1` using `[e, map_pow, map_sub, Polynomial.aeval_X, map_one]`.

Establish `h2 : Module.End.IsSemisimple (a.ρ (ineIncl h τ) - 1)`. Use `(Module.End.isSemisimple_sub_algebraMap_iff (f := a.ρ (ineIncl h τ)) (μ := (1 : ℂ))).2 (a.semisimple _)` as an intermediate fact. Simplify using `using this`. Conclude with `sub_eq_zero.1 (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨_, h1⟩ h2)`.
-/
theorem ineTriv_mk {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V) :
    IneTriv (WD.mk a) ↔ ∀ τ : Ine (F := K) A, a.ρ (ineIncl h τ) = 1 := by
  refine forall_congr' fun τ => ?_
  rw [WD.charPol_mk, WD.lpDim_mk]
  refine ⟨fun e => ?_, fun e => by rw [e, LinearMap.charpoly_one]⟩
  have h1 := LinearMap.aeval_self_charpoly (a.ρ (ineIncl h τ))
  rw [e, map_pow, map_sub, Polynomial.aeval_X, map_one] at h1
  have h2 : Module.End.IsSemisimple (a.ρ (ineIncl h τ) - 1) := by
    have := (Module.End.isSemisimple_sub_algebraMap_iff (f := a.ρ (ineIncl h τ)) (μ := (1 : ℂ))).2 (a.semisimple _)
    simpa using this
  exact sub_eq_zero.1 (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨_, h1⟩ h2)

/- English proof (translation)
Take `⟨n, a, rfl⟩` from `WD.exists_rep x`. Rewrite using `[WD.unr_mk, WD.monodromyZero_ofWeilDeligneRepClass_iff, ineTriv_mk]`. Both sides reduce to the same expression.
-/
theorem unr_iff (x : WD h) : x.unr ↔ x.mono0 ∧ IneTriv x := by
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  rw [WD.unr_mk, WD.monodromyZero_ofWeilDeligneRepClass_iff, ineTriv_mk]; rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨(ineTriv_mk _).2 (WDRep.unr_diag (h := h) (WDRep.spEig v 2)).2, (sp_two_spec h).2.2.2⟩`.
-/
theorem ineTriv_sp : IneTriv (WD.lpSp h 2) ∧ ¬ (WD.lpSp h 2).unr :=
  ⟨(ineTriv_mk _).2 (WDRep.unr_diag (h := h) (WDRep.spEig v 2)).2, (sp_two_spec h).2.2.2⟩

/- English proof (translation)
Rewrite using `[WD.lpOfChar, ineTriv_mk]`. Use `forall_congr' fun τ => ⟨fun e => ?_, fun e => ?_⟩` and prove the remaining obligations. Use `congrFun (LinearMap.congr_fun e fun _ => 1) 0` as an intermediate fact. Simplify using `using this`. Use `ext`.

Simplify using `[e]`.
-/
theorem ineTriv_ofChar (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) :
    IneTriv (WD.lpOfChar h χ hχ) ↔ ∀ τ : Ine (F := K) A, χ (ineIncl h τ) = 1 := by
  rw [WD.lpOfChar, ineTriv_mk]
  refine forall_congr' fun τ => ⟨fun e => ?_, fun e => ?_⟩
  · have := congrFun (LinearMap.congr_fun e fun _ => 1) 0
    simpa using this
  · ext; simp [e]

variable [Algebra K L] [IsScalarTower K L Ω]

omit [NumberField K] [NumberField L] [IsAlgClosure K Ω] [IsAlgClosure L Ω] in

/- English proof (translation)
Apply `continuous_of_continuousAt_one` to reduce the goal to its premises. Rewrite using `[ContinuousAt, map_one]`. Introduce `s hs`. Rewrite `hs` using `[krullTopology_mem_nhds_one_iff]`. Take `⟨M, hM, hMs⟩` from `hs`.

Set `b` to `Module.finBasis K M`. Establish `hint : ∀ i, IsIntegral L ((b i : M) : Ω)` using `fun i => ((IsIntegral.of_finite K (b i)).map (IsScalarTower.toAlgHom K M Ω)).tower_top`. Establish `hN : ⋂ i, ((IntermediateField.adjoin L {((b i : M) : Ω)}).fixingSubgroup : Set (Ω ≃ₐ[L] Ω)) ∈ nhds (1 : Ω ≃ₐ[L] Ω)` using `Filter.iInter_mem.mpr fun i => by haveI := IntermediateField.adjoin.finiteDimensional (hint i)`. Conclude with `(IntermediateField.fixingSubgroup_isOpen _).mem_nhds (Subgroup.one_mem _)`. Rewrite using `[Filter.mem_map]`.

Use `Filter.mem_of_superset hN ?_` and prove the remaining obligations. Introduce `σ hσ`. Apply `hMs` to reduce the goal to its premises. Simplify using `only [Set.mem_iInter, SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ`. Rewrite using `[SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]`.

Introduce `x hx`. Establish `hb : ∀ i, σ ((b i : M) : Ω) = ((b i : M) : Ω)` using `fun i => hσ i _ (IntermediateField.mem_adjoin_simple_self L _)`. Take `⟨y, rfl⟩ : ∃ y : M, (y : Ω) = x` from `⟨⟨x, hx⟩, rfl⟩`. Rewrite using `[← b.sum_repr y]`. Express the relevant statement in the definitionally equal form `(AlgEquiv.restrictScalars K σ) _ = _`.

Simplify using `only [IntermediateField.coe_sum, IntermediateField.coe_smul, map_sum, map_smul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[AlgEquiv.restrictScalars_apply, hb]`.
-/
theorem continuous_restr : Continuous (AlgEquiv.restrictScalarsHom K : G L Ω →* G K Ω) := by
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, map_one]
  intro s hs
  rw [krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨M, hM, hMs⟩ := hs
  let b := Module.finBasis K M
  have hint : ∀ i, IsIntegral L ((b i : M) : Ω) := fun i =>
    ((IsIntegral.of_finite K (b i)).map (IsScalarTower.toAlgHom K M Ω)).tower_top
  have hN : ⋂ i, ((IntermediateField.adjoin L {((b i : M) : Ω)}).fixingSubgroup : Set (Ω ≃ₐ[L] Ω))
      ∈ nhds (1 : Ω ≃ₐ[L] Ω) := Filter.iInter_mem.mpr fun i => by
    haveI := IntermediateField.adjoin.finiteDimensional (hint i)
    exact (IntermediateField.fixingSubgroup_isOpen _).mem_nhds (Subgroup.one_mem _)
  rw [Filter.mem_map]
  refine Filter.mem_of_superset hN ?_
  intro σ hσ
  apply hMs
  simp only [Set.mem_iInter, SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hb : ∀ i, σ ((b i : M) : Ω) = ((b i : M) : Ω) := fun i =>
    hσ i _ (IntermediateField.mem_adjoin_simple_self L _)
  obtain ⟨y, rfl⟩ : ∃ y : M, (y : Ω) = x := ⟨⟨x, hx⟩, rfl⟩
  rw [← b.sum_repr y]
  change (AlgEquiv.restrictScalars K σ) _ = _
  simp only [IntermediateField.coe_sum, IntermediateField.coe_smul, map_sum, map_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [AlgEquiv.restrictScalars_apply, hb]

omit [IsAlgClosure K Ω] [IsAlgClosure L Ω] in
include h h' in

/- English proof (translation)
Establish `e : v = v'.under (𝓞 K)` using `HeightOneSpectrum.ext (Ideal.ext fun x => by`. Rewrite using `[← h x]`. Express the relevant statement in the definitionally equal form `_ ↔ algebraMap (𝓞 K) (𝓞 L) x ∈ v'.asIdeal`. Rewrite using `[← h', IsScalarTower.algebraMap_apply K L Ω]`. Use the proof step `rfl)`.

Substitute `e` using the available equality. Establish `: v'.asIdeal.LiesOver (v'.under (𝓞 K)).asIdeal` using `⟨rfl⟩`. Use `v'.isMaximal` as an intermediate fact. Use `(v'.under (𝓞 K)).isMaximal` as an intermediate fact. Use `show Ideal.absNorm v'.asIdeal = Ideal.absNorm (v'.under (𝓞 K)).asIdeal ^ v'.asIdeal.inertiaDeg (𝓞 K)`.

Rewrite using `[← Ideal.absNorm_relNorm (𝓞 K) (𝓞 L) v'.asIdeal, Ideal.relNorm_eq_pow_of_isMaximal v'.asIdeal (v'.under (𝓞 K)).asIdeal, map_pow]`.
-/
theorem normV_pow : normV v' = normV v ^ v'.asIdeal.inertiaDeg (𝓞 K) := by
  have e : v = v'.under (𝓞 K) := HeightOneSpectrum.ext (Ideal.ext fun x => by
    rw [← h x]
    change _ ↔ algebraMap (𝓞 K) (𝓞 L) x ∈ v'.asIdeal
    rw [← h', IsScalarTower.algebraMap_apply K L Ω]
    rfl)
  subst e
  have : v'.asIdeal.LiesOver (v'.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := v'.isMaximal
  have := (v'.under (𝓞 K)).isMaximal
  show Ideal.absNorm v'.asIdeal = Ideal.absNorm (v'.under (𝓞 K)).asIdeal ^ v'.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 L) v'.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal v'.asIdeal (v'.under (𝓞 K)).asIdeal, map_pow]

omit [IsAlgClosure K Ω] [IsAlgClosure L Ω] in
include h h' in

/- English proof (translation)
Use `⟨H.1, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[pow_mul, pow_mul, ← normV_pow (h := h) (h' := h')]`. Conclude with `H.2 x hx`.
-/
theorem actsAs_restr {σ : G L Ω} {a b : ℕ} (H : ActsAs A (normV v') σ a b) :
    ActsAs A (normV v) (σ.restrictScalars K : G K Ω) (v'.asIdeal.inertiaDeg (𝓞 K) * a) (v'.asIdeal.inertiaDeg (𝓞 K) * b) := by
  refine ⟨H.1, fun x hx => ?_⟩
  rw [pow_mul, pow_mul, ← normV_pow (h := h) (h' := h')]
  exact H.2 x hx

variable (h h') in

def weilRes : Weil h' →* Weil h :=
  ((AlgEquiv.restrictScalarsHom K : G L Ω →* G K Ω).comp (Weil h').subtype).codRestrict _ fun σ =>
    let ⟨_, _, H⟩ := σ.2; ⟨_, _, actsAs_restr (h := h) (h' := h') H⟩

/- English proof (translation)
Take `⟨a, b, H⟩` from `σ.2`. Rewrite using `[deg_eq H, deg_eq (σ := weilRes h h' σ) (actsAs_restr (h := h) (h' := h') H)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem deg_weilRes (σ : Weil h') : deg (weilRes h h' σ) = v'.asIdeal.inertiaDeg (𝓞 K) * deg σ := by
  obtain ⟨a, b, H⟩ := σ.2
  rw [deg_eq H, deg_eq (σ := weilRes h h' σ) (actsAs_restr (h := h) (h' := h') H)]
  push_cast; ring

variable (h') in

def repRes {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V) : WDRep h' V where
  ρ := a.ρ.comp (weilRes h h')
  N := a.N
  smooth := by
    let i : Ine (F := L) A → Ine (F := K) A := fun τ => ⟨AlgEquiv.restrictScalarsHom K τ.1, τ.2⟩
    have hi : Continuous i := (continuous_restr.comp continuous_subtype_val).subtype_mk _
    exact a.smooth.preimage hi
  semisimple σ := a.semisimple _
  nilpotent := a.nilpotent
  comm σ := by
    have := a.comm (weilRes h h' σ)
    rw [deg_weilRes, zpow_mul, zpow_natCast, ← Nat.cast_pow, ← normV_pow (h := h) (h' := h')] at this
    exact this

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, a₁, b, h1, rfl, h3, h4⟩`. Take `⟨e, e1, e2⟩` from `WD.mk_eq_mk.1 h1`. Use `WD.sound ⟨e, fun σ u => ?_, fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[h4 (weilRes h h' σ) σ fun _ => rfl]`.

Conclude with `e1 _ u`. Rewrite using `[h3]`. Conclude with `e2 u`. Introduce and unpack `rfl`. Set `e` to `(Module.finBasis ℂ V).equivFun`.

Use `⟨_, a.transport e, (repRes h' a).transport e, WD.sound (a.iso_transport e).symm, WD.sound ((repRes h' a).iso_transport e).symm, rfl, fun σ σ' hσ => ?_⟩` and prove the remaining obligations. Rewrite using `[show σ = weilRes h h' σ' from Subtype.ext (AlgEquiv.ext hσ)]`. Both sides reduce to the same expression.
-/
theorem restricts_mk_iff {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V) (x' : WD h') :
    Restricts (WD.mk a) x' ↔ x' = WD.mk (repRes h' a) := by
  constructor
  · rintro ⟨n, a₁, b, h1, rfl, h3, h4⟩
    obtain ⟨e, e1, e2⟩ := WD.mk_eq_mk.1 h1
    refine WD.sound ⟨e, fun σ u => ?_, fun u => ?_⟩
    · rw [h4 (weilRes h h' σ) σ fun _ => rfl]; exact e1 _ u
    · rw [h3]; exact e2 u
  · rintro rfl
    let e := (Module.finBasis ℂ V).equivFun
    refine ⟨_, a.transport e, (repRes h' a).transport e, WD.sound (a.iso_transport e).symm,
      WD.sound ((repRes h' a).iso_transport e).symm, rfl, fun σ σ' hσ => ?_⟩
    rw [show σ = weilRes h h' σ' from Subtype.ext (AlgEquiv.ext hσ)]
    rfl

variable (h') in

/- English proof (translation)
Take `⟨n, a, rfl⟩` from `WD.exists_rep x`. Simplify using `only [restricts_mk_iff]`. Conclude with `existsUnique_eq`.
-/
theorem existsUnique_restricts (x : WD h) : ∃! x' : WD h', Restricts x x' := by
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  simp only [restricts_mk_iff]
  exact existsUnique_eq

/- English proof (translation)
Use `(restricts_mk_iff _ _).2 (WD.sound ⟨.refl _ _, fun σ u => ?_, fun u => rfl⟩)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = (WDRep.diag h c).ρ (weilRes h h' σ) u`. Rewrite using `[WDRep.diag_ρ, WDRep.diag_ρ, deg_weilRes]`. Simplify using `[zpow_mul]`.
-/
theorem restricts_diag {n : ℕ} (c : Fin n → ℂˣ) :
    Restricts (WD.mk (WDRep.diag h c)) (WD.mk (WDRep.diag h' fun i => c i ^ v'.asIdeal.inertiaDeg (𝓞 K))) := by
  refine (restricts_mk_iff _ _).2 (WD.sound ⟨.refl _ _, fun σ u => ?_, fun u => rfl⟩)
  change _ = (WDRep.diag h c).ρ (weilRes h h' σ) u
  rw [WDRep.diag_ρ, WDRep.diag_ρ, deg_weilRes]
  simp [zpow_mul]

/- English proof (translation)
Use `(restricts_mk_iff _ _).2 (WD.sound ⟨.refl _ _, fun σ u => ?_, fun u => rfl⟩)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = (WDRep.sp h n).ρ (weilRes h h' σ) u`. Rewrite using `[WDRep.sp_ρ, WDRep.sp_ρ, deg_weilRes]`. Establish `e : ∀ s : ℝ, (qPow v' s : ℂ) = (qPow v s : ℂ) ^ v'.asIdeal.inertiaDeg (𝓞 K)` using `fun s => by`. Rewrite using `[coe_qPow, coe_qPow, normV_pow (h := h) (h' := h'), ← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (by positivity), ← Complex.ofReal_cpow (by positivity), ← Complex.ofReal_pow, Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by …`.

Simplify using `only [LinearEquiv.refl_apply, WDRep.spEig, e, zpow_mul, zpow_natCast]`.
-/
theorem restricts_sp (n : ℕ) : Restricts (WD.lpSp h n) (WD.lpSp h' n) := by
  refine (restricts_mk_iff _ _).2 (WD.sound ⟨.refl _ _, fun σ u => ?_, fun u => rfl⟩)
  change _ = (WDRep.sp h n).ρ (weilRes h h' σ) u
  rw [WDRep.sp_ρ, WDRep.sp_ρ, deg_weilRes]
  have e : ∀ s : ℝ, (qPow v' s : ℂ) = (qPow v s : ℂ) ^ v'.asIdeal.inertiaDeg (𝓞 K) := fun s => by
    rw [coe_qPow, coe_qPow, normV_pow (h := h) (h' := h'), ← Complex.ofReal_natCast, ← Complex.ofReal_natCast,
      ← Complex.ofReal_cpow (by positivity), ← Complex.ofReal_cpow (by positivity), ← Complex.ofReal_pow, Nat.cast_pow,
      ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity), mul_comm]
  simp only [LinearEquiv.refl_apply, WDRep.spEig, e, zpow_mul, zpow_natCast]

/- English proof (translation)
Take `⟨n, a, rfl⟩` from `WD.exists_rep x`. Rewrite using `[(restricts_mk_iff _ _).1 H, ineTriv_mk]`. Conclude with `fun τ => (ineTriv_mk a).1 hx ⟨AlgEquiv.restrictScalarsHom K τ.1, τ.2⟩`.
-/
theorem IneTriv.restricts {x : WD h} {x' : WD h'} (H : Restricts x x') (hx : IneTriv x) : IneTriv x' := by
  obtain ⟨n, a, rfl⟩ := WD.exists_rep x
  rw [(restricts_mk_iff _ _).1 H, ineTriv_mk]
  exact fun τ => (ineTriv_mk a).1 hx ⟨AlgEquiv.restrictScalarsHom K τ.1, τ.2⟩

end Tower

/- English proof (translation)
Use extensionality with `g`. Both sides reduce to the same expression.
-/
theorem resTo_resTo {K L M Ω : Type} [Field K] [Field L] [Field M] [Field Ω] [Algebra K Ω] [Algebra L Ω] [Algebra M Ω]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L Ω] [IsScalarTower L M Ω] [IsScalarTower K M Ω]
    {X : Type} [Monoid X] (r : G K Ω →* X) : resTo M (resTo L r) = resTo M r := by
  ext g; rfl

/- English proof (translation)
Use `⟨le_rfl, fun W _ => ?_⟩` and prove the remaining obligations. Use `haveI : IsSimpleModule k (Fin 1 → k) := isSimpleModule_iff_finrank_eq_one.2 (by simp)`. Conclude with `eq_bot_or_eq_top W`.
-/
theorem irr_one {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 1) k) : Irr r := by
  refine ⟨le_rfl, fun W _ => ?_⟩
  haveI : IsSimpleModule k (Fin 1 → k) := isSimpleModule_iff_finrank_eq_one.2 (by simp)
  exact eq_bot_or_eq_top W

/- English proof (translation)
Introduce `H` and use `by rcases H.2 (LinearMap.ker (LinearMap.proj 0 : (Fin 2 → k) →ₗ[k] k)) (fun g u hu => by simpa using hu) with e | e · have : (Pi.single 1 1 : Fin 2 → k) ∈ LinearMap.ker (LinearMap.proj 0 : (Fin 2 → k) →ₗ[k] k) := by simp rw [e, Submodule.mem_bot] at this simpa using congrFun this …`.
-/
theorem not_irr_two {Γ k : Type} [Group Γ] [Field k] : ¬ Irr (1 : Γ →* GL (Fin 2) k) := fun H => by
  rcases H.2 (LinearMap.ker (LinearMap.proj 0 : (Fin 2 → k) →ₗ[k] k)) (fun g u hu => by simpa using hu) with e | e
  · have : (Pi.single 1 1 : Fin 2 → k) ∈ LinearMap.ker (LinearMap.proj 0 : (Fin 2 → k) →ₗ[k] k) := by simp
    rw [e, Submodule.mem_bot] at this
    simpa using congrFun this 1
  · have : (Pi.single 0 1 : Fin 2 → k) ∈ LinearMap.ker (LinearMap.proj 0 : (Fin 2 → k) →ₗ[k] k) := by
      rw [e]; trivial
    simp at this

/- English proof (translation)
Use `⟨by norm_num, fun W hW => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Take `⟨u, hu, h0⟩` from `(Submodule.ne_bot_iff W).1 hc.1`. Set `s : GL (Fin 2) k` to `Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0] (by simp [Matrix.det_fin_two])`.

Set `t : GL (Fin 2) k` to `Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 1; 0, 1] (by simp [Matrix.det_fin_two])`. Establish `hs : ∀ w ∈ W, ![w 1, w 0] ∈ W` using `fun w hw => by`. Use `hW s w hw using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `ext i; fin_cases i <;> simp [s, Matrix.mulVec, dotProduct]`. Establish `ht : ∀ w ∈ W, ![w 1, 0] ∈ W` using `fun w hw => by`.

Use `W.sub_mem (hW t w hw) hw using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `ext i; fin_cases i <;> simp [t, Matrix.mulVec, dotProduct]`. Establish `h1 : (![1, 0] : Fin 2 → k) ∈ W`. Distinguish the cases in `e : u 1 = 0`. Apply the tactic sequence `have e0 : u 0 ≠ 0 := fun e0 => h0 (by ext i; fin_cases i <;> simp [e, e0])`.

Use `W.smul_mem (u 0)⁻¹ (ht _ (hs _ hu)) using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `ext i; fin_cases i <;> simp [e0]`. Use `W.smul_mem (u 1)⁻¹ (ht _ hu) using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `ext i; fin_cases i <;> simp [e]`. Use `hc.2 (eq_top_iff.2 fun w _ => ?_)` and prove the remaining obligations.

Use `W.add_mem (W.smul_mem (w 0) h1) (W.smul_mem (w 1) (hs _ h1)) using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `ext i; fin_cases i <;> simp`.
-/
theorem irr_std {k : Type} [Field k] : Irr (MonoidHom.id (GL (Fin 2) k)) := by
  refine ⟨by norm_num, fun W hW => ?_⟩
  by_contra hc
  push Not at hc
  obtain ⟨u, hu, h0⟩ := (Submodule.ne_bot_iff W).1 hc.1
  let s : GL (Fin 2) k := Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0] (by simp [Matrix.det_fin_two])
  let t : GL (Fin 2) k := Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 1; 0, 1] (by simp [Matrix.det_fin_two])
  have hs : ∀ w ∈ W, ![w 1, w 0] ∈ W := fun w hw => by
    convert hW s w hw using 1
    ext i; fin_cases i <;> simp [s, Matrix.mulVec, dotProduct]
  have ht : ∀ w ∈ W, ![w 1, 0] ∈ W := fun w hw => by
    convert W.sub_mem (hW t w hw) hw using 1
    ext i; fin_cases i <;> simp [t, Matrix.mulVec, dotProduct]
  have h1 : (![1, 0] : Fin 2 → k) ∈ W := by
    by_cases e : u 1 = 0
    · have e0 : u 0 ≠ 0 := fun e0 => h0 (by ext i; fin_cases i <;> simp [e, e0])
      convert W.smul_mem (u 0)⁻¹ (ht _ (hs _ hu)) using 1
      ext i; fin_cases i <;> simp [e0]
    · convert W.smul_mem (u 1)⁻¹ (ht _ hu) using 1
      ext i; fin_cases i <;> simp [e]
  refine hc.2 (eq_top_iff.2 fun w _ => ?_)
  convert W.add_mem (W.smul_mem (w 0) h1) (W.smul_mem (w 1) (hs _ h1)) using 1
  ext i; fin_cases i <;> simp

section Aut

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {l : ℕ} [Fact l.Prime] {a : ℕ}

/- English proof (translation)
Use `GlobalTheory.Published.PolarizedPairModel.hyp_triv (L := E)` as an intermediate fact. Rewrite `this` using `[GlobalTheory.Published.PolarizedPairModel.line, CuspSub.twist_one]`. Conclude with `⟨this.1, _, this.2⟩`.
-/
theorem regPol_triv : RegPol (CuspSub.triv E (le_refl 1)) := by
  have := GlobalTheory.Published.PolarizedPairModel.hyp_triv (L := E)
  rw [GlobalTheory.Published.PolarizedPairModel.line, CuspSub.twist_one] at this
  exact ⟨this.1, _, this.2⟩

/- English proof (translation)
The claim follows from `let ⟨h1, χ, _, _, h2, _⟩ := H; ⟨h1, χ, h2⟩`.
-/
theorem RepOf.regPol {π : CuspSub E a} {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin a) (Qbar l)} (H : RepOf π ι r) : RegPol π :=
  let ⟨h1, χ, _, _, h2, _⟩ := H; ⟨h1, χ, h2⟩

/- English proof (translation)
The claim follows from `let ⟨h1, χ, h2⟩ := hπ let ⟨r, wt, HT, K⟩ := H E Ω l ι a ha π χ h1 h2 ⟨r, h1, χ, wt, HT, h2, K⟩`.
-/
theorem exists_repOf (H : GlobalTheory.Published.PolarizedGaloisRepPublished) (ha : 1 ≤ a) {π : CuspSub E a} (hπ : RegPol π)
    (ι : Qbar l ≃+* ℂ) : ∃ r : G E Ω →* GL (Fin a) (Qbar l), RepOf π ι r :=
  let ⟨h1, χ, h2⟩ := hπ
  let ⟨r, wt, HT, K⟩ := H E Ω l ι a ha π χ h1 h2
  ⟨r, h1, χ, wt, HT, h2, K⟩

/- English proof (translation)
The claim follows from `let ⟨r, h⟩ := exists_repOf (Ω := Ω) H le_rfl (regPol_triv (E := E)) ι; ⟨r, _, h⟩`.
-/
theorem exists_isAut (H : GlobalTheory.Published.PolarizedGaloisRepPublished) (ι : Qbar l ≃+* ℂ) :
    ∃ r : G E Ω →* GL (Fin 1) (Qbar l), IsAut ι r :=
  let ⟨r, h⟩ := exists_repOf (Ω := Ω) H le_rfl (regPol_triv (E := E)) ι; ⟨r, _, h⟩

/- English proof (translation)
Introduce and unpack `⟨-, χ, wt, HT, -, H⟩`. Use `GlobalTheory.CarHyp.Model.not_isAssoc_cyc Ω ι hl h hrc ⟨H.cont, H.ss, fun w hl A h rc hrc σ σ' hσ _ e => ?_⟩` and prove the remaining obligations. Conclude with `H.away w hl A h rc hrc σ' (GlobalTheory.CarHyp.Model.isLocComp_contra hσ e)`.
-/
theorem not_repOf_cyc (ι : Qbar l ≃+* ℂ) {w : HeightOneSpectrum (𝓞 E)} (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal)
    {A : ValuationSubring Ω} (h : IsPlaceOver A w) {rc} (hrc : IsTheRec h rc) :
    ¬ RepOf (CuspSub.triv E (le_refl 1)) ι ((Matrix.GeneralLinearGroup.scalar (Fin 1)).comp (cyc E Ω l)) := by
  rintro ⟨-, χ, wt, HT, -, H⟩
  refine GlobalTheory.CarHyp.Model.not_isAssoc_cyc Ω ι hl h hrc ⟨H.cont, H.ss, fun w hl A h rc hrc σ σ' hσ _ e => ?_⟩
  exact H.away w hl A h rc hrc σ' (GlobalTheory.CarHyp.Model.isLocComp_contra hσ e)

end Aut

end GlobalTheory.AboveL.Model

end
