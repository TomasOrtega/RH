import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel
open GlobalTheory.TwistDet GlobalTheory.AntiRamConj
open scoped Pointwise

namespace GlobalTheory.ResUnr

/- English proof (translation)
Establish `e1` using `x.2.2 (h * σ * h⁻¹) h`. Establish `e2` using `x.2.2 h σ`. Rewrite `e1` using `[inv_mul_cancel_right, e2, hσ, map_zero, add_zero]`. Rewrite using `[map_neg, sub_neg_eq_add, eq_neg_add_iff_add_eq, add_comm]`. Conclude with `e1.symm`.
-/
theorem cocycle_conj {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (rho : Representation R G M) (x : Z1 rho)
    (h σ : G) (hσ : x.1 σ = 0) : x.1 (h * σ * h⁻¹) = rho (h * σ * h⁻¹) (-x.1 h) - (-x.1 h) := by
  have e1 := x.2.2 (h * σ * h⁻¹) h
  have e2 := x.2.2 h σ
  rw [inv_mul_cancel_right, e2, hσ, map_zero, add_zero] at e1
  rw [map_neg, sub_neg_eq_add, eq_neg_add_iff_add_eq, add_comm]
  exact e1.symm

/- English proof (translation)
Unfold `Formalism.GaloisCohomology.unrAt H1ur`. Rewrite using `[LinearMap.mem_ker]`. Unfold `ReciprocityTheory.Gal.resH1`. Rewrite using `[Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `(mem_coboundaries1 _ _).2 ⟨m, fun g => hm g.1.1 (Subgroup.mem_subgroupOf.1 g.2)⟩`.
-/
theorem res_mem_unrAt {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (rho : Representation R (G F Ω) M) (x : Z1 rho)
    (A : ValuationSubring Ω) (m : M) (hm : ∀ σ ∈ Ine (F := F) A, x.1 σ = rho σ m - m) :
    ReciprocityTheory.Gal.resH1 rho (Dec (F := F) A).subtype continuous_subtype_val (Submodule.Quotient.mk x) ∈ Formalism.GaloisCohomology.unrAt rho A := by
  unfold Formalism.GaloisCohomology.unrAt H1ur
  rw [LinearMap.mem_ker]
  unfold ReciprocityTheory.Gal.resH1
  rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
  exact (mem_coboundaries1 _ _).2 ⟨m, fun g => hm g.1.1 (Subgroup.mem_subgroupOf.1 g.2)⟩

/- English proof (translation)
Rewrite using `[Subsingleton.elim y 0]`. Conclude with `S.zero_mem`.
-/
theorem mem_of_subsingleton {R M : Type} [Ring R] [AddCommGroup M] [Module R M] (h : Subsingleton M) (S : Submodule R M) (y : M) :
    y ∈ S := by
  rw [Subsingleton.elim y 0]
  exact S.zero_mem

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨h.1, fun x hx => by rw [pow_one]; exact h.2 x hx⟩`. Introduce `h`. Conclude with `⟨h.1, fun x hx => by have := h.2 x hx; rwa [pow_one] at this⟩`.
-/
theorem mem_ine_iff_isFrob {B : ValuationSubring N.Om} {σ : GE N} : σ ∈ Ine (F := D.host.E) B ↔ IsFrob B 1 σ := by
  constructor
  · intro h
    exact ⟨h.1, fun x hx => by rw [pow_one]; exact h.2 x hx⟩
  · intro h
    exact ⟨h.1, fun x hx => by have := h.2 x hx; rwa [pow_one] at this⟩

/- English proof (translation)
The claim follows from `mem_ine_iff_isFrob.2 (isFrob_smul (mem_ine_iff_isFrob.1 hσ) g)`.
-/
theorem ine_smul {B : ValuationSubring N.Om} {σ : GE N} (hσ : σ ∈ Ine (F := D.host.E) B) (g : GE N) :
    g * σ * g⁻¹ ∈ Ine (F := D.host.E) (g • B) :=
  mem_ine_iff_isFrob.2 (isFrob_smul (mem_ine_iff_isFrob.1 hσ) g)

/- English proof (translation)
Establish `h2` using `isPlaceOver_moveVal_cc X (isConjPl_symm h) (N.plOm.2 P')`. Take `⟨g, hg⟩` from `exists_smul_eq_of_isPlaceOver (F := D.host.E) h2 (N.plOm.2 P)`. Use `⟨(cConj X g)⁻¹, fun σ hσ => ?_⟩` and prove the remaining obligations. Establish `h3` using `ine_smul (cConj_mem_ine X hσ) g`. Rewrite `h3` using `[hg]`.

Use `⟨_, h3, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, map_inv, cConj_cConj]`. Use `group`.
-/
theorem exists_ine_of_conj (X : NTw D.R D.host D.what₂ D.LL0 N) {P P' : PlE D.host} (h : IsConjPl D.host P P') :
    ∃ k : GE N, ∀ σ ∈ Ine (F := D.host.E) (N.plOm.1 P'), ∃ σ₀ ∈ Ine (F := D.host.E) (N.plOm.1 P),
      σ = k * cConj X σ₀ * k⁻¹ := by
  have h2 := isPlaceOver_moveVal_cc X (isConjPl_symm h) (N.plOm.2 P')
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := D.host.E) h2 (N.plOm.2 P)
  refine ⟨(cConj X g)⁻¹, fun σ hσ => ?_⟩
  have h3 := ine_smul (cConj_mem_ine X hσ) g
  rw [hg] at h3
  refine ⟨_, h3, ?_⟩
  rw [map_mul, map_mul, map_inv, cConj_cConj]
  group

/- English proof (translation)
Take `⟨k, hk⟩` from `exists_ine_of_conj X h`. Use `res_mem_unrAt rho x (N.plOm.1 P') (-x.1 k) fun σ hσ => ?_` and prove the remaining obligations. Take `⟨σ₀, h3, rfl⟩` from `hk σ hσ`. Conclude with `cocycle_conj rho x k _ (hz _ h3)`.
-/
theorem res_mem_unrAt_of_conj (X : NTw D.R D.host D.what₂ D.LL0 N) {P P' : PlE D.host} (h : IsConjPl D.host P P')
    {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (rho : Representation R (GE N) M) (x : Z1 rho)
    (hz : ∀ σ ∈ Ine (F := D.host.E) (N.plOm.1 P), x.1 (cConj X σ) = 0) :
    ReciprocityTheory.Gal.resH1 rho (Dec (F := D.host.E) (N.plOm.1 P')).subtype continuous_subtype_val (Submodule.Quotient.mk x) ∈
      Formalism.GaloisCohomology.unrAt rho (N.plOm.1 P') := by
  obtain ⟨k, hk⟩ := exists_ine_of_conj X h
  refine res_mem_unrAt rho x (N.plOm.1 P') (-x.1 k) fun σ hσ => ?_
  obtain ⟨σ₀, h3, rfl⟩ := hk σ hσ
  exact cocycle_conj rho x k _ (hz _ h3)

set_option maxHeartbeats 800000 in

/- English proof (translation)
Introduce `D N X bkP i s hF K _ _ _ _ hK M R P d φ φ' Q hM hpos hQ x hx hz`. Unfold `selOn Formalism.GaloisCohomology.SelAll at hx ⊢`. Use `(mem_Sel _ _ _ _ _).2 fun v => ?_` and prove the remaining obligations. Establish `hv` using `(mem_Sel _ _ _ _ _).1 hx v`. Unfold `Formalism.GaloisCohomology.bkCond at hv ⊢`.

Distinguish the cases in `h1 : ((X.l i : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal`. Rewrite `hv`, the goal using `[if_pos h1]`. Conclude with `hv`. Rewrite `hv`, the goal using `[if_neg h1]`. Distinguish the cases in `h2 : v ∈ Spl i`.

Rewrite using `[if_pos (Set.mem_union_left _ h2)]`. Conclude with `Submodule.mem_top`. Rewrite using `[if_neg (by simpa using h2)]`. Distinguish the cases in `h3 : v ∈ Q`. Use `swap`.

Rewrite `hv` using `[if_neg (by simp [h2, h3])]`. Conclude with `hv`. Take `⟨q, hq⟩` from `(hQ v).1 h3`. Break down `q with a | a` into its components or cases. Use `haveI : IsLocalHom (algebraMap (X.O0 i) K) := ⟨fun y hy => by`.

Assume the negation of the conclusion as `hn`. Conclude with `hy.ne_zero (hK y ((IsLocalRing.mem_maximalIdeal y).2 hn))⟩`. Establish `hT : Tors K K` using `fun b => ⟨1, fun y hy => by`. Rewrite `hy` using `[pow_one, IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot]`. Rewrite using `[hy, zero_smul]⟩`.

Establish `hs` using `(hF M R P d φ φ' hM hpos K (1 : GE N →* Kˣ) (by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ) (fun g => ⟨0, by simp⟩) K hT (Tgl i s) (Or.inl rfl) a v hq).2.1`. Conclude with `mem_of_subsingleton hs _ _`. Break down `hq with rfl | hq` into its components or cases. Use `res_mem_unrAt (red i K (Tgl i s)) x (N.plOm.1 (P (.inr a))) 0 fun σ hσ => ?_` and prove the remaining obligations. Rewrite using `[(hz a σ hσ).1, map_zero, sub_zero]`.

Conclude with `res_mem_unrAt_of_conj X hq (red i K (Tgl i s)) x fun σ hσ => (hz a σ hσ).2`.
-/
theorem unrelax : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), FirstHalf i s → ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → ∀ (M R : ℕ) (P : Fin R ⊕ Fin R → PlE D.host) d φ φ' (Q : Finset (PlE D.host)), 1 ≤ M → Position i s M P d φ φ' → IsQ P Q → ∀ x : Z1 (red i K (Tgl i s)), cl x ∈ selOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K Q → (∀ a, ∀ σ ∈ Ine (F := D.host.E) (N.plOm.1 (P (.inr a))), x.1 σ = 0 ∧ x.1 (GlobalTheory.TwistDet.cConj X σ) = 0) → cl x ∈ selOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K ∅ := by
  intro D N X bkP i s hF K _ _ _ _ hK M R P d φ φ' Q hM hpos hQ x hx hz
  unfold selOn Formalism.GaloisCohomology.SelAll at hx ⊢
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hx v
  unfold Formalism.GaloisCohomology.bkCond at hv ⊢
  by_cases h1 : ((X.l i : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal
  · rw [if_pos h1] at hv ⊢
    exact hv
  rw [if_neg h1] at hv ⊢
  by_cases h2 : v ∈ Spl i
  · rw [if_pos (Set.mem_union_left _ h2)]
    exact Submodule.mem_top
  rw [if_neg (by simpa using h2)]
  by_cases h3 : v ∈ Q
  swap
  · rw [if_neg (by simp [h2, h3])] at hv
    exact hv
  obtain ⟨q, hq⟩ := (hQ v).1 h3
  rcases q with a | a
  · haveI : IsLocalHom (algebraMap (X.O0 i) K) := ⟨fun y hy => by
      by_contra hn
      exact hy.ne_zero (hK y ((IsLocalRing.mem_maximalIdeal y).2 hn))⟩
    have hT : Tors K K := fun b => ⟨1, fun y hy => by
      rw [pow_one, IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at hy
      rw [hy, zero_smul]⟩
    have hs := (hF M R P d φ φ' hM hpos K (1 : GE N →* Kˣ) (by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ) (fun g => ⟨0, by simp⟩) K hT (Tgl i s) (Or.inl rfl)
      a v hq).2.1
    exact mem_of_subsingleton hs _ _
  · rcases hq with rfl | hq
    · refine res_mem_unrAt (red i K (Tgl i s)) x (N.plOm.1 (P (.inr a))) 0 fun σ hσ => ?_
      rw [(hz a σ hσ).1, map_zero, sub_zero]
    · exact res_mem_unrAt_of_conj X hq (red i K (Tgl i s)) x fun σ hσ => (hz a σ hσ).2

end GlobalTheory.ResUnr

end
