import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.CountPOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.NearTIff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.IsCompactSpanRange
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CrossMSmulRight

noncomputable section

namespace PI.OmVg

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.OmLocU.Red
  Topology Filter
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

/- English proof (translation)
Take `⟨-, hπ, -⟩` from `unif_spec v ϖ hϖ`. Establish `hN : OEv (E` using `E) v ∈ 𝓝 (0 : Fv F v ⊗[F] E) := (isOpen_oEv v).mem_nhds (Orb.oev_zero v)`. Take `⟨m, hm⟩` from `PI.VolStabSW.eventually_smul_sub (Set.range c) (Set.finite_range c).isCompact (fun k => ϖ ^ k) hπ _ hN`. Conclude with `⟨m, fun i => by rw [← smul_eq_sc]; exact hm _ ⟨i, rfl⟩⟩`.
-/
theorem exists_pow_mem {ϖ : Fv F v} (hϖ : IsUnif v ϖ) {a : ℕ} (c : Fin a → Fv F v ⊗[F] E) :
    ∃ m : ℕ, ∀ i, sc (E := E) v (ϖ ^ m) * c i ∈ OEv (E := E) v := by
  obtain ⟨-, hπ, -⟩ := unif_spec v ϖ hϖ
  have hN : OEv (E := E) v ∈ 𝓝 (0 : Fv F v ⊗[F] E) := (isOpen_oEv v).mem_nhds (Orb.oev_zero v)
  obtain ⟨m, hm⟩ := PI.VolStabSW.eventually_smul_sub (Set.range c) (Set.finite_range c).isCompact
    (fun k => ϖ ^ k) hπ _ hN
  exact ⟨m, fun i => by rw [← smul_eq_sc]; exact hm _ ⟨i, rfl⟩⟩

variable (hSD : IsSDLoc σ J v Λ) {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e)
  (he1 : gramR (Fv F v) σ J e = 1)

/- English proof (translation)
Establish `e1 : (⟨_, hw⟩ : OR (E` using `E) v) = ∑ i, d i * cf σ J v Λ hSD he x i p := by`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [AddSubmonoidClass.coe_finsetSum, Subring.coe_mul, cf_coe]`. Rewrite using `[Orb.hR_sum_right σ J v]`. Rewrite using `[e1, map_sum]`.

Simplify using `only [map_mul, phi_apply]`.
-/
theorem coord_comb {K : Type} [CommRing K] (π : OR (E := E) v →+* K) {a : ℕ} (x : lamA v Λ a)
    (d : Fin a → OR (E := E) v) (p : Fin n)
    (hw : hR (Fv F v) σ J (e p) (∑ i, (d i : Fv F v ⊗[F] E) • (x : TupV (E := E) v n a) i) ∈ OR (E := E) v) :
    π ⟨_, hw⟩ = ∑ i, π (d i) * phi σ J v Λ hSD he π a x i p := by
  have e1 : (⟨_, hw⟩ : OR (E := E) v) = ∑ i, d i * cf σ J v Λ hSD he x i p := by
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum, Subring.coe_mul, cf_coe]
    rw [Orb.hR_sum_right σ J v]
  rw [e1, map_sum]
  simp only [map_mul, phi_apply]

include he1 in

/- English proof (translation)
Establish `hP : ∀ p, ∃ d ∈ OEv (E` using `E) v, hR (Fv F v) σ J (e p) w = sc (E := E) v ϖ * d := fun p => (hπ.2.1 _).1 (h0 p)`. Use `choose d hd hde using hP`. Use `⟨∑ p, d p • e p, (he _).2 ⟨d, hd, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[expand σ J v Λ he he1 hw, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations.

Rewrite using `[hde, smul_smul]`.
-/
theorem ker_vec {ϖ : Fv F v} {K : Type} [CommRing K] {τ : K →+* K} {π : OR (E := E) v →+* K}
    (hπ : IsRes σ v ϖ τ π) {w : Fin n → Fv F v ⊗[F] E} (hw : w ∈ latLoc (E := E) v Λ)
    (h0 : ∀ p, π ⟨hR (Fv F v) σ J (e p) w, (hSD _).1 hw _ (bas_mem v Λ he p)⟩ = 0) :
    ∃ w' ∈ latLoc (E := E) v Λ, w = sc (E := E) v ϖ • w' := by
  have hP : ∀ p, ∃ d ∈ OEv (E := E) v, hR (Fv F v) σ J (e p) w = sc (E := E) v ϖ * d :=
    fun p => (hπ.2.1 _).1 (h0 p)
  choose d hd hde using hP
  refine ⟨∑ p, d p • e p, (he _).2 ⟨d, hd, rfl⟩, ?_⟩
  rw [expand σ J v Λ he he1 hw, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hde, smul_smul]

end PI.OmVg
