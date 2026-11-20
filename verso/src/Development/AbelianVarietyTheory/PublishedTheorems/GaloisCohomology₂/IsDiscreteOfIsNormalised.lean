import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompactLatticeGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOneOfInfOfVal

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host MeasureTheory Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.IdeleCovolume

namespace GlobalTheory.DiscSpec.Model

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

omit [IsTotallyComplex E] in

/- English proof (translation)
The claim follows from `GlobalTheory.HeckeUnrTrivial.eq_one_of_inf_of_val E ν (fun k => Units.ext (by simpa using h.2.2 k)) fun v _ => Units.ext (by simpa using h.2.1 v)`.
-/
theorem eq_one_of_isAbsPow {ν : HChar E} (h : ν.IsAbsPow 0) : ν = 1 :=
  GlobalTheory.HeckeUnrTrivial.eq_one_of_inf_of_val E ν (fun k => Units.ext (by simpa using h.2.2 k)) fun v _ => Units.ext (by simpa using h.2.1 v)

/- English proof (translation)
Take `⟨χ, rfl⟩` from `RankOne.exists_eq_twist π`. Take `⟨χ', rfl⟩` from `RankOne.exists_eq_twist π'`. Rewrite using `[CG.ofChar_injective (Quotient.sound h)]`.
-/
theorem eq_of_iso {π π' : CuspSub E 1} (h : π.Iso π') : π = π' := by
  obtain ⟨χ, rfl⟩ := RankOne.exists_eq_twist π
  obtain ⟨χ', rfl⟩ := RankOne.exists_eq_twist π'
  rw [CG.ofChar_injective (Quotient.sound h)]

/- English proof (translation)
Take `⟨f, hf, hc⟩` from `h`. Establish `hm : ∀ φ ∈ π.V, f φ ∈ π'.V` using `fun φ hφ => hf ▸ Submodule.mem_map_of_mem hφ`. Establish `hk : π.V ⊓ LinearMap.ker f = ⊥`. Use `(π.irred _ inf_le_left fun o φ hφ => ⟨π.stable o φ hφ.1, ?_⟩).resolve_right fun e => π'.ne_bot ?_` and prove the remaining obligations. Establish `h0 : f φ = 0` using `hφ.2`.

Express the relevant statement in the definitionally equal form `f _ = 0`. Rewrite using `[hc o φ hφ.1, h0, map_zero]`. Rewrite using `[← hf, eq_bot_iff]`. Introduce and unpack `_ ⟨φ, hφ, rfl⟩`. Conclude with `(e.ge hφ).2`.

Use `⟨LinearEquiv.ofBijective (f.restrict hm) ⟨?_, ?_⟩, fun o φ => Subtype.ext (hc o φ.1 φ.2)⟩` and prove the remaining obligations. Use `(injective_iff_map_eq_zero _).2 fun φ h0 => Subtype.ext ?_` and prove the remaining obligations. Establish `: φ.1 ∈ π.V ⊓ LinearMap.ker f` using `⟨φ.2, congrArg Subtype.val h0⟩`. Rewrite `this` using `[hk]`. Then use the resulting hypothesis. Introduce and unpack `⟨ψ, hψ⟩`.

Take `⟨φ, hφ, rfl⟩` from `hf.ge hψ`. Conclude with `⟨⟨φ, hφ⟩, rfl⟩`.
-/
theorem iso_of_isQuotOf {a : ℕ} {π π' : CuspSub E a} (h : IsQuotOf π'.V π.V) : π.Iso π' := by
  obtain ⟨f, hf, hc⟩ := h
  have hm : ∀ φ ∈ π.V, f φ ∈ π'.V := fun φ hφ => hf ▸ Submodule.mem_map_of_mem hφ
  have hk : π.V ⊓ LinearMap.ker f = ⊥ := by
    refine (π.irred _ inf_le_left fun o φ hφ => ⟨π.stable o φ hφ.1, ?_⟩).resolve_right fun e => π'.ne_bot ?_
    · have h0 : f φ = 0 := hφ.2
      change f _ = 0
      rw [hc o φ hφ.1, h0, map_zero]
    · rw [← hf, eq_bot_iff]
      rintro _ ⟨φ, hφ, rfl⟩
      exact (e.ge hφ).2
  refine ⟨LinearEquiv.ofBijective (f.restrict hm) ⟨?_, ?_⟩, fun o φ => Subtype.ext (hc o φ.1 φ.2)⟩
  · refine (injective_iff_map_eq_zero _).2 fun φ h0 => Subtype.ext ?_
    have : φ.1 ∈ π.V ⊓ LinearMap.ker f := ⟨φ.2, congrArg Subtype.val h0⟩
    rwa [hk] at this
  · rintro ⟨ψ, hψ⟩
    obtain ⟨φ, hφ, rfl⟩ := hf.ge hψ
    exact ⟨⟨φ, hφ⟩, rfl⟩

def toCusp {V : Submodule ℂ (Sm E 1)} (h : IsDiscrete V) : CuspSub E 1 :=
  ⟨V, fun φ hφ => ⟨h.aut φ hφ, fun r h0 h1 => by omega⟩, h.stable, h.ne_bot, h.irred⟩

/- English proof (translation)
Take `⟨h, ν, hν, hq⟩` from `h`. Take `rfl : ν = fun _ => 1` from `funext fun i => eq_one_of_isAbsPow (by simpa [spehExp] using hν i)`. Simplify using `only [CuspSub.twist_one] at hq`. Rewrite `hq` using `[indForms_one h π]`. Conclude with `iso_of_isQuotOf hq`.
-/
theorem iso_of_isSpehOf_one {a : ℕ} {π π' : CuspSub E a} (h : IsSpehOf π'.V π 1) : π.Iso π' := by
  obtain ⟨h, ν, hν, hq⟩ := h
  obtain rfl : ν = fun _ => 1 := funext fun i => eq_one_of_isAbsPow (by simpa [spehExp] using hν i)
  simp only [CuspSub.twist_one] at hq
  rw [indForms_one h π] at hq
  exact iso_of_isQuotOf hq

/- English proof (translation)
Set `S : Subgroup (GA E a)` to `{ carrier := {γ | ∀ g, φ.1 (γ * g) = φ.1 g} one_mem' := fun g => by rw [one_mul] mul_mem' := fun {x y} hx hy g => by rw [mul_assoc, hx, hy] inv_mem' := fun {x} hx g => by rw [← hx, mul_inv_cancel_left] }`. Establish `: latticeGL E a ≤ S` using `sup_le (by rintro _ ⟨γ, rfl⟩; exact (π.cusp φ hφ).1.left γ) (Subgroup.zpowers_le.2 (h φ hφ 1))`. Conclude with `this`.
-/
theorem left_lattice {a : ℕ} {π : CuspSub E a} (h : IsNormalised π) {φ : Sm E a} (hφ : φ ∈ π.V) :
    ∀ γ ∈ latticeGL E a, ∀ g, φ.1 (γ * g) = φ.1 g := by
  let S : Subgroup (GA E a) :=
    { carrier := {γ | ∀ g, φ.1 (γ * g) = φ.1 g}
      one_mem' := fun g => by rw [one_mul]
      mul_mem' := fun {x y} hx hy g => by rw [mul_assoc, hx, hy]
      inv_mem' := fun {x} hx g => by rw [← hx, mul_inv_cancel_left] }
  have : latticeGL E a ≤ S := sup_le (by rintro _ ⟨γ, rfl⟩; exact (π.cusp φ hφ).1.left γ)
    (Subgroup.zpowers_le.2 (h φ hφ 1))
  exact this

/- English proof (translation)
Take `⟨ω, h⟩` from `RankOne.exists_char π`. Establish `e : φ.1 = fun g => ((ω g : ℂˣ) : ℂ) * φ.1 1` using `funext fun g => by`. Establish `h1 : φ.1 (1 * g) = ((ω g : ℂˣ) : ℂ) * φ.1 1` using `congrFun (congrArg Subtype.val (h g φ hφ)) 1`. Rewrite `h1` using `[one_mul]`. Then use the resulting hypothesis. Rewrite using `[e]`.

Conclude with `(Units.continuous_val.comp (RankOne.continuous_char π ω h)).mul continuous_const`.
-/
theorem continuous_form (π : CuspSub E 1) {φ : Sm E 1} (hφ : φ ∈ π.V) : Continuous φ.1 := by
  obtain ⟨ω, h⟩ := RankOne.exists_char π
  have e : φ.1 = fun g => ((ω g : ℂˣ) : ℂ) * φ.1 1 := funext fun g => by
    have h1 : φ.1 (1 * g) = ((ω g : ℂˣ) : ℂ) * φ.1 1 := congrFun (congrArg Subtype.val (h g φ hφ)) 1
    rwa [one_mul] at h1
  rw [e]
  exact (Units.continuous_val.comp (RankOne.continuous_char π ω h)).mul continuous_const

/- English proof (translation)
Use `⟨fun φ hφ => (π.cusp φ hφ).1, fun φ hφ => ⟨h φ hφ, ?_⟩, π.stable, π.ne_bot, π.irred⟩` and prove the remaining obligations. Take `⟨-, μ, 𝓕, hμ, hF, -⟩` from `isSqInt_const E 1`. Use `⟨μ, 𝓕, hμ, hF, ?_⟩` and prove the remaining obligations. Use `letI : MeasurableSpace (GA E 1) := borel _`. Use `haveI : BorelSpace (GA E 1) := ⟨rfl⟩`.

Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E`. Use `haveI : SecondCountableTopology (Matrix (Fin 1) (Fin 1) (Ad E)) := inferInstanceAs (SecondCountableTopology (Fin 1 → Fin 1 → Ad E))`. Use `haveI : SecondCountableTopology (Matrix (Fin 1) (Fin 1) (Ad E))ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology`. Use `haveI : SecondCountableTopology (GA E 1) := Units.isEmbedding_embedProduct.secondCountableTopology`. Use `haveI := discrete_latticeGL E`.

Use `haveI : Countable (latticeGL E 1) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance`. Take `⟨K, hK, hcov⟩` from `exists_compact_latticeGL E`. Establish `h2` using `GlobalTheory.integrableOn_fundamentalDomain_of_cocompact _ (latticeGL E 1) K hK hcov μ hμ 𝓕 hF (fun g => φ.1 g ^ 2) ((continuous_form π hφ).pow 2) fun γ hγ g => by rw [left_lattice h hφ γ hγ]`. Simplify `h2.2` using `only [HasFiniteIntegral, enorm_pow]`.
-/
theorem isDiscrete_of_isNormalised {π : CuspSub E 1} (h : IsNormalised π) : IsDiscrete π.V := by
  refine ⟨fun φ hφ => (π.cusp φ hφ).1, fun φ hφ => ⟨h φ hφ, ?_⟩, π.stable, π.ne_bot, π.irred⟩
  obtain ⟨-, μ, 𝓕, hμ, hF, -⟩ := isSqInt_const E 1
  refine ⟨μ, 𝓕, hμ, hF, ?_⟩
  letI : MeasurableSpace (GA E 1) := borel _
  haveI : BorelSpace (GA E 1) := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI : SecondCountableTopology (Matrix (Fin 1) (Fin 1) (Ad E)) :=
    inferInstanceAs (SecondCountableTopology (Fin 1 → Fin 1 → Ad E))
  haveI : SecondCountableTopology (Matrix (Fin 1) (Fin 1) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GA E 1) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI := discrete_latticeGL E
  haveI : Countable (latticeGL E 1) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨K, hK, hcov⟩ := exists_compact_latticeGL E
  have h2 := GlobalTheory.integrableOn_fundamentalDomain_of_cocompact _ (latticeGL E 1) K hK hcov μ hμ 𝓕 hF
    (fun g => φ.1 g ^ 2) ((continuous_form π hφ).pow 2) fun γ hγ g => by rw [left_lattice h hφ γ hγ]
  simpa only [HasFiniteIntegral, enorm_pow] using h2.2

/- English proof (translation)
Take `⟨χ, rfl⟩` from `RankOne.exists_eq_twist π`. Use `(CG.isUnitary_mk _).1 ((CG.isUnitary_ofChar_iff χ).2 ?_)` and prove the remaining obligations. Establish `hφ : mulChi 1 χ (oneFn E 1) ∈ ((CuspSub.triv E le_rfl).twist χ).V` using `⟨_, Submodule.mem_span_singleton_self _, rfl⟩`. Take `⟨K, hK, hcov⟩` from `exists_compact_latticeGL E`. Take `⟨C, hC⟩` from `hK.exists_bound_of_continuousOn (continuous_form _ hφ).continuousOn`.

Establish `hb : ∀ x, ‖((χ.1 x : ℂˣ) : ℂ)‖ ≤ C` using `fun x => by`. Take `⟨γ, hγ, hk⟩` from `hcov (CG.oneByOne x)`. Establish `h1` using `hC _ hk`. Rewrite `h1` using `[left_lattice h hφ γ hγ, mulChi_apply]`. Express the relevant statement in the definitionally equal form `‖1 * ((χ.1 (GeneralLinearGroup.det (CG.oneByOne x)) : ℂˣ) : ℂ)‖ ≤ C at h1`.

Rewrite `h1` using `[CG.det_oneByOne, one_mul]`. Then use the resulting hypothesis. Establish `hle : ∀ x, ‖((χ.1 x : ℂˣ) : ℂ)‖ ≤ 1` using `fun x => by`. Assume the negation of the conclusion as `hc`. Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt C (not_le.1 hc)`. Use `hb (x ^ n)` as an intermediate fact.

Rewrite `this` using `[map_pow, Units.val_pow_eq_pow_val, norm_pow]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `x`. Use `le_antisymm (hle x) ?_` and prove the remaining obligations. Use `hle x⁻¹` as an intermediate fact.

Rewrite `this` using `[map_inv, Units.val_inv_eq_inv_val, norm_inv]`. Conclude with `(inv_le_one₀ (norm_pos_iff.2 (Units.ne_zero _))).1 this`.
-/
theorem isUnitary_of_isNormalised {π : CuspSub E 1} (h : IsNormalised π) : π.IsUnitary := by
  obtain ⟨χ, rfl⟩ := RankOne.exists_eq_twist π
  refine (CG.isUnitary_mk _).1 ((CG.isUnitary_ofChar_iff χ).2 ?_)
  have hφ : mulChi 1 χ (oneFn E 1) ∈ ((CuspSub.triv E le_rfl).twist χ).V :=
    ⟨_, Submodule.mem_span_singleton_self _, rfl⟩
  obtain ⟨K, hK, hcov⟩ := exists_compact_latticeGL E
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (continuous_form _ hφ).continuousOn
  have hb : ∀ x, ‖((χ.1 x : ℂˣ) : ℂ)‖ ≤ C := fun x => by
    obtain ⟨γ, hγ, hk⟩ := hcov (CG.oneByOne x)
    have h1 := hC _ hk
    rw [left_lattice h hφ γ hγ, mulChi_apply] at h1
    change ‖1 * ((χ.1 (GeneralLinearGroup.det (CG.oneByOne x)) : ℂˣ) : ℂ)‖ ≤ C at h1
    rwa [CG.det_oneByOne, one_mul] at h1
  have hle : ∀ x, ‖((χ.1 x : ℂˣ) : ℂ)‖ ≤ 1 := fun x => by
    by_contra hc
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (not_le.1 hc)
    have := hb (x ^ n)
    rw [map_pow, Units.val_pow_eq_pow_val, norm_pow] at this
    linarith
  intro x
  refine le_antisymm (hle x) ?_
  have := hle x⁻¹
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at this
  exact (inv_le_one₀ (norm_pos_iff.2 (Units.ne_zero _))).1 this

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨f, h0, h1, h2⟩`. Conclude with `⟨f.codRestrict _ h1, fun e => h0 (LinearMap.ext fun v => congrArg Subtype.val (LinearMap.congr_fun e v)), fun g v => Subtype.ext (h2 g v)⟩`. Introduce and unpack `⟨f, h0, h1⟩`. Conclude with `⟨P.V.subtype.comp f, fun e => h0 (LinearMap.ext fun v => Subtype.ext (LinearMap.congr_fun e v)), fun v => (f v).2, fun g v => congrArg Subtype.val (h1 g v)⟩`.
-/
theorem isLocCompGL_iff {a : ℕ} (P : CuspSub E a) (w σ) : IsLocCompGL P.V w σ ↔ P.IsLocComp w σ := by
  constructor
  · rintro ⟨f, h0, h1, h2⟩
    exact ⟨f.codRestrict _ h1, fun e => h0 (LinearMap.ext fun v => congrArg Subtype.val (LinearMap.congr_fun e v)),
      fun g v => Subtype.ext (h2 g v)⟩
  · rintro ⟨f, h0, h1⟩
    exact ⟨P.V.subtype.comp f, fun e => h0 (LinearMap.ext fun v => Subtype.ext (LinearMap.congr_fun e v)),
      fun v => (f v).2, fun g v => congrArg Subtype.val (h1 g v)⟩

/- English proof (translation)
Take `⟨χ, rfl⟩` from `RankOne.exists_eq_twist π`. Use `⟨fun w => ⟨_, _, CG.isLoc_ofChar χ w, (isLocCompGL_iff _ _ _).2 (CG.isLoc_ofChar χ w)⟩, fun w σ σ' h h' => ?_, fun τ => ⟨_, CG.hasInfChar_ofChar χ τ, by rw [GlobalTheory.SphGal.spehInf_one]; exact CG.hasInfChar_ofChar χ τ⟩⟩` and prove the remaining obligations. Set `_` to `GlobalTheory.LocalData.complRel w`. Use `GlobalTheory.LocalData.isLocalField w` as an intermediate fact. Take `⟨e⟩` from `LocUniq.isLocComp_unique _ w σ σ' h ((isLocCompGL_iff _ w σ').1 h')`.

Take `⟨hd, hc⟩` from `GlobalTheory.LocGL.isSpeh_one (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred)`. Conclude with `⟨hd, hc.of_equiv ((GlobalTheory.LocGL.IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm.trans e) (.refl _)⟩`.
-/
theorem hasSpehComp_rank_one (π : CuspSub E 1) : HasSpehComp π.V π 1 := by
  obtain ⟨χ, rfl⟩ := RankOne.exists_eq_twist π
  refine ⟨fun w => ⟨_, _, CG.isLoc_ofChar χ w, (isLocCompGL_iff _ _ _).2 (CG.isLoc_ofChar χ w)⟩, fun w σ σ' h h' => ?_,
    fun τ => ⟨_, CG.hasInfChar_ofChar χ τ, by rw [GlobalTheory.SphGal.spehInf_one]; exact CG.hasInfChar_ofChar χ τ⟩⟩
  let _ := GlobalTheory.LocalData.complRel w
  have := GlobalTheory.LocalData.isLocalField w
  obtain ⟨e⟩ := LocUniq.isLocComp_unique _ w σ σ' h ((isLocCompGL_iff _ w σ').1 h')
  obtain ⟨hd, hc⟩ := GlobalTheory.LocGL.isSpeh_one (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred)
  exact ⟨hd, hc.of_equiv ((GlobalTheory.LocGL.IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm.trans e) (.refl _)⟩

/- English proof (translation)
Establish `key : ∀ {V : Submodule ℂ (Sm E 1)} (hV : IsDiscrete V) {π : CuspSub E 1}, IsSpehOf V π 1 → π = toCusp hV` using `fun hV π h => eq_of_iso (iso_of_isSpehOf_one (π' := toCusp hV) h)`. Use `⟨fun V hV => ?_, fun a d π h hn => ?_, fun V hV a d a' d' π π' _ _ e e' => ?_, fun V V' hV hV' h => ?_, fun V hV a d π _ e => ?_⟩` and prove the remaining obligations. Establish `hn : IsNormalised (toCusp hV)` using `isNormalised_of_isDiscrete hV`. Conclude with `⟨1, 1, toCusp hV, isUnitary_of_isNormalised hn, hn, isSpehOf_one (toCusp hV)⟩`. Take `⟨rfl, rfl⟩` from `mul_eq_one.1 h`.

Conclude with `⟨π.V, ⟨isDiscrete_of_isNormalised hn, isSpehOf_one π⟩, fun V hV => by rw [key hV.1 hV.2]; rfl⟩`. Take `⟨rfl, rfl⟩` from `mul_eq_one.1 e.mul_eq`. Take `⟨rfl, rfl⟩` from `mul_eq_one.1 e'.mul_eq`. Rewrite using `[key hV e, key hV e']`. Conclude with `⟨rfl, rfl⟩`.

Conclude with `congrArg CuspSub.V (eq_of_iso ((isIsoGL_iff (toCusp hV) (toCusp hV')).1 h))`. Take `⟨rfl, rfl⟩` from `mul_eq_one.1 e.mul_eq`. Rewrite using `[key hV e]`. Conclude with `hasSpehComp_rank_one (toCusp hV)`.
-/
theorem discreteSpectrum_one :
    (∀ V : Submodule ℂ (Sm E 1), IsDiscrete V →
      ∃ (a d : ℕ) (π : CuspSub E a), π.IsUnitary ∧ IsNormalised π ∧ IsSpehOf V π d) ∧
    (∀ (a d : ℕ) (π : CuspSub E a), d * a = 1 → IsNormalised π →
      ∃! V : Submodule ℂ (Sm E 1), IsDiscrete V ∧ IsSpehOf V π d) ∧
    (∀ V : Submodule ℂ (Sm E 1), IsDiscrete V → ∀ (a d a' d' : ℕ) (π : CuspSub E a) (π' : CuspSub E a'),
      IsNormalised π → IsNormalised π' → IsSpehOf V π d → IsSpehOf V π' d' →
        d = d' ∧ (⟨a, CG.mk π⟩ : Σ b, CG E b) = ⟨a', CG.mk π'⟩) ∧
    (∀ V V' : Submodule ℂ (Sm E 1), IsDiscrete V → IsDiscrete V' → IsIsoGL V V' → V = V') ∧
    ∀ V : Submodule ℂ (Sm E 1), IsDiscrete V → ∀ (a d : ℕ) (π : CuspSub E a),
      IsNormalised π → IsSpehOf V π d → HasSpehComp V π d := by
  have key : ∀ {V : Submodule ℂ (Sm E 1)} (hV : IsDiscrete V) {π : CuspSub E 1}, IsSpehOf V π 1 → π = toCusp hV :=
    fun hV π h => eq_of_iso (iso_of_isSpehOf_one (π' := toCusp hV) h)
  refine ⟨fun V hV => ?_, fun a d π h hn => ?_, fun V hV a d a' d' π π' _ _ e e' => ?_, fun V V' hV hV' h => ?_,
    fun V hV a d π _ e => ?_⟩
  · have hn : IsNormalised (toCusp hV) := isNormalised_of_isDiscrete hV
    exact ⟨1, 1, toCusp hV, isUnitary_of_isNormalised hn, hn, isSpehOf_one (toCusp hV)⟩
  · obtain ⟨rfl, rfl⟩ := mul_eq_one.1 h
    exact ⟨π.V, ⟨isDiscrete_of_isNormalised hn, isSpehOf_one π⟩, fun V hV => by rw [key hV.1 hV.2]; rfl⟩
  · obtain ⟨rfl, rfl⟩ := mul_eq_one.1 e.mul_eq
    obtain ⟨rfl, rfl⟩ := mul_eq_one.1 e'.mul_eq
    rw [key hV e, key hV e']
    exact ⟨rfl, rfl⟩
  · exact congrArg CuspSub.V (eq_of_iso ((isIsoGL_iff (toCusp hV) (toCusp hV')).1 h))
  · obtain ⟨rfl, rfl⟩ := mul_eq_one.1 e.mul_eq
    rw [key hV e]
    exact hasSpehComp_rank_one (toCusp hV)

/- English proof (translation)
Assemble the required witnesses or components as `⟨_, _, isDiscrete_of_isNormalised (isNormalised_triv le_rfl), isNormalised_triv le_rfl, isSpehOf_one _⟩`.
-/
theorem exists_discrete_speh : ∃ (V : Submodule ℂ (Sm E 1)) (π : CuspSub E 1),
    IsDiscrete V ∧ IsNormalised π ∧ IsSpehOf V π 1 :=
  ⟨_, _, isDiscrete_of_isNormalised (isNormalised_triv le_rfl), isNormalised_triv le_rfl, isSpehOf_one _⟩

/- English proof (translation)
Take `⟨σ, hσ⟩` from `exists_not_isUnitary (E := E)`. Proceed by induction on `σ using Quotient.inductionOn with`. Consider the case `h π => exact ⟨π, fun h => hσ ((CG.isUnitary_mk π).2 (isUnitary_of_isNormalised h))⟩`.
-/
theorem exists_not_isNormalised : ∃ π : CuspSub E 1, ¬ IsNormalised π := by
  obtain ⟨σ, hσ⟩ := exists_not_isUnitary (E := E)
  induction σ using Quotient.inductionOn with
  | h π => exact ⟨π, fun h => hσ ((CG.isUnitary_mk π).2 (isUnitary_of_isNormalised h))⟩

/- English proof (translation)
Evaluate the numerical expressions using `[spehExp]`.
-/
theorem exponents_two : spehExp 2 0 + (1 : ℕ) * spehExp 2 0 = 1 ∧ spehExp 2 1 + (1 : ℕ) * spehExp 2 1 = -1 := by
  norm_num [spehExp]

end GlobalTheory.DiscSpec.Model

end
