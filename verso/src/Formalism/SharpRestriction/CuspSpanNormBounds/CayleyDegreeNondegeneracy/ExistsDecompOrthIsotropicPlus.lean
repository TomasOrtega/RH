import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.LiftsConjugateUnderStabilizer

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence.LatticeLiftIndependence

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cl

variable (D : D7) (u : D.what₂.Word) (hT : Tu D u ≠ 0) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
  (he : F0.e = D.sp.hypE) (hz : F0.z = D.zmOf u)

include he in
/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Rewrite using `[he]`. Express the relevant statement in the definitionally equal form `D.sp.hypE a ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0))`. Rewrite using `[Formalism.MainNotions.mem_orth_iff]`.

Introduce and unpack `_ ⟨w, rfl⟩`. Conclude with `(D.sp.hyp_orthX a w).1`.
-/
theorem isotropic_le_orth_range : F0.X ≤ orth (hS D) (LinearMap.range (D.sp.iXY 0)) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, rfl⟩
  rw [he]
  change D.sp.hypE a ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0))
  rw [Formalism.MainNotions.mem_orth_iff]
  rintro _ ⟨w, rfl⟩
  exact (D.sp.hyp_orthX a w).1

include hz in
/- English proof (translation)
Rewrite using `[Formalism.MainNotions.mem_orth_iff]`. Introduce and unpack `_ ⟨w, rfl⟩`. Rewrite using `[hz]`. Conclude with `Formalism.MainNotions.hT_swap_zero (z_orth_embedding D u w)`.
-/
theorem z_mem_orth_range : F0.z ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0)) := by
  rw [Formalism.MainNotions.mem_orth_iff]
  rintro _ ⟨w, rfl⟩
  rw [hz]
  exact Formalism.MainNotions.hT_swap_zero (z_orth_embedding D u w)

include hT he hz in

/- English proof (translation)
Establish `hW` using `(Formalism.MainNotions.WHyp_Wsp D u hT (lf D F0) he hz).1`. Establish `hx' : x ∈ Wsp D ⊔ Xsp (lf D F0)` using `by rw [hW]; exact hx`. Take `⟨a, ⟨w, rfl⟩, ξ, hξ, rfl⟩` from `Submodule.mem_sup.1 hx'`. Conclude with `⟨w, by simpa using hξ⟩`.
-/
theorem exists_decomp_orth_isotropic_plus (x : (VS D).V) (hx : x ∈ orth (hS D) F0.Xplus) :
    ∃ w, x - D.sp.iXY 0 w ∈ F0.X := by
  have hW := (Formalism.MainNotions.WHyp_Wsp D u hT (lf D F0) he hz).1
  have hx' : x ∈ Wsp D ⊔ Xsp (lf D F0) := by rw [hW]; exact hx
  obtain ⟨a, ⟨w, rfl⟩, ξ, hξ, rfl⟩ := Submodule.mem_sup.1 hx'
  exact ⟨w, by simpa using hξ⟩

include hT he hz in

/- English proof (translation)
Establish `hT' : ((Tu D u : ℕ) : D.host.E) ≠ 0` using `Nat.cast_ne_zero.2 hT`. Establish `hx'` using `(Formalism.MainNotions.mem_orth_iff _ _).1 hx`. Take `⟨w, hw⟩` from `exists_decomp_orth_isotropic_plus D u hT F0 he hz (x - (-((VS D).hT F0.z x) / ((Tu D u : ℕ) : D.host.E)) • F0.z) (by`. Rewrite using `[Formalism.MainNotions.mem_orth_iff]`. Use `Formalism.MainNotions.hT_zero_of_mem_Xplus F0 (fun a => ?_) ?_` and prove the remaining obligations.

Rewrite using `[map_sub, map_smul, F0.z_orth a, smul_zero, sub_zero]`. Conclude with `hx' _ (Submodule.subset_span ⟨a, rfl⟩)`. Rewrite using `[map_sub, map_smul, F0.z_norm, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Use the proof step `ring)`.

Use `⟨w, -((VS D).hT F0.z x) / ((Tu D u : ℕ) : D.host.E), ?_⟩` and prove the remaining obligations. Rewrite using `[add_comm, ← sub_sub]`. Conclude with `hw`.
-/
theorem exists_decomp_orth_isotropic (x : (VS D).V) (hx : x ∈ orth (hS D) F0.X) :
    ∃ (w : (D.sp.X 0).V) (c : D.host.E), x - (D.sp.iXY 0 w + c • F0.z) ∈ F0.X := by
  have hT' : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hT
  have hx' := (Formalism.MainNotions.mem_orth_iff _ _).1 hx
  obtain ⟨w, hw⟩ := exists_decomp_orth_isotropic_plus D u hT F0 he hz
    (x - (-((VS D).hT F0.z x) / ((Tu D u : ℕ) : D.host.E)) • F0.z) (by
      rw [Formalism.MainNotions.mem_orth_iff]
      refine Formalism.MainNotions.hT_zero_of_mem_Xplus F0 (fun a => ?_) ?_
      · rw [map_sub, map_smul, F0.z_orth a, smul_zero, sub_zero]
        exact hx' _ (Submodule.subset_span ⟨a, rfl⟩)
      · rw [map_sub, map_smul, F0.z_norm, smul_eq_mul]
        field_simp
        ring)
  refine ⟨w, -((VS D).hT F0.z x) / ((Tu D u : ℕ) : D.host.E), ?_⟩
  rw [add_comm, ← sub_sub]
  exact hw

include hT he hz in

/- English proof (translation)
Establish `key : ∀ Λ : LatV D, ∀ x, x ∈ Lsub Λ (lf D F0) ↔ x ∈ orth (hS D) F0.X ∧ ∀ (w : (D.sp.X 0).V) (c : D.host.E), x - (D.sp.iXY 0 w + c • F0.z) ∈ F0.X → (w, c) ∈ latticeWithZ D F0 Λ`. Introduce `Λ x`. Establish `hj : ∀ (w : (D.sp.X 0).V) (c : D.host.E), (w, c) ∈ latticeWithZ D F0 Λ ↔ D.sp.iXY 0 w + c • F0.z ∈ Lsub Λ (lf D F0)`. Introduce `w c`. Unfold `latticeWithZ`.

Rewrite using `[Submodule.mem_comap]`. Simplify using `[embedWithZ]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `⟨hx.2, fun w c hξ => ?_⟩` and prove the remaining obligations.

Rewrite using `[hj]`. Use `(Lsub Λ (lf D F0)).sub_mem hx (isotropic_le_Lsub F0 Λ hξ)` as an intermediate fact. Simplify using `using this`. Introduce and unpack `⟨hxO, hall⟩`. Take `⟨w, c, hξ⟩` from `exists_decomp_orth_isotropic D u hT F0 he hz x hxO`.

Establish `h1` using `(hj w c).1 (hall w c hξ)`. Use `(Lsub Λ (lf D F0)).add_mem h1 (isotropic_le_Lsub F0 Λ hξ)` as an intermediate fact. Simplify using `using this`. Use extensionality with `x`. Rewrite using `[key Λ₁, key Λ₂, h]`.
-/
theorem Lsub_eq_of_latticeWithZ_eq (Λ₁ Λ₂ : LatV D) (h : latticeWithZ D F0 Λ₁ = latticeWithZ D F0 Λ₂) :
    Lsub Λ₁ (lf D F0) = Lsub Λ₂ (lf D F0) := by
  have key : ∀ Λ : LatV D, ∀ x, x ∈ Lsub Λ (lf D F0) ↔
      x ∈ orth (hS D) F0.X ∧ ∀ (w : (D.sp.X 0).V) (c : D.host.E),
        x - (D.sp.iXY 0 w + c • F0.z) ∈ F0.X → (w, c) ∈ latticeWithZ D F0 Λ := by
    intro Λ x
    have hj : ∀ (w : (D.sp.X 0).V) (c : D.host.E), (w, c) ∈ latticeWithZ D F0 Λ ↔ D.sp.iXY 0 w + c • F0.z ∈ Lsub Λ (lf D F0) := by
      intro w c
      unfold latticeWithZ
      rw [Submodule.mem_comap]
      simp [embedWithZ]
    constructor
    · intro hx
      refine ⟨hx.2, fun w c hξ => ?_⟩
      rw [hj]
      have := (Lsub Λ (lf D F0)).sub_mem hx (isotropic_le_Lsub F0 Λ hξ)
      simpa using this
    · rintro ⟨hxO, hall⟩
      obtain ⟨w, c, hξ⟩ := exists_decomp_orth_isotropic D u hT F0 he hz x hxO
      have h1 := (hj w c).1 (hall w c hξ)
      have := (Lsub Λ (lf D F0)).add_mem h1 (isotropic_le_Lsub F0 Λ hξ)
      simpa using this
  ext x
  rw [key Λ₁, key Λ₂, h]

def projWAlt : (VS D).V →ₗ[D.host.E] (D.sp.X 0).V :=
  (LinearEquiv.ofInjective (D.sp.iXY 0) (embedding_W_injective D)).symm.toLinearMap ∘ₗ LinearMap.fst D.host.E _ _ ∘ₗ
    (Submodule.prodEquivOfIsCompl _ _ (isCompl_range_orth_range D)).symm.toLinearMap

/- English proof (translation)
Establish `e : D.sp.iXY 0 w + b = Submodule.prodEquivOfIsCompl _ _ (isCompl_range_orth_range D) (LinearEquiv.ofInjective (D.sp.iXY 0) (embedding_W_injective D) w, ⟨b, hb⟩)`. Rewrite using `[Submodule.coe_prodEquivOfIsCompl']`. Both sides reduce to the same expression. Rewrite using `[e]`. Unfold `projWAlt`.

Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearMap.fst_apply]`.
-/
theorem projW_apply (w : (D.sp.X 0).V) (b : (VS D).V) (hb : b ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0))) :
    projWAlt D (D.sp.iXY 0 w + b) = w := by
  have e : D.sp.iXY 0 w + b = Submodule.prodEquivOfIsCompl _ _ (isCompl_range_orth_range D)
      (LinearEquiv.ofInjective (D.sp.iXY 0) (embedding_W_injective D) w, ⟨b, hb⟩) := by
    rw [Submodule.coe_prodEquivOfIsCompl']
    rfl
  rw [e]
  unfold projWAlt
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearMap.fst_apply]

include hT he hz in

/- English proof (translation)
Establish `hσ' : ∀ x y, (VS D).hT (σ x) (σ y) = (VS D).hT x y` using `hσ.1`. Establish `hX : F0.X.map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) = F0.X`. Use `hσ.2.1 D.R.rS` as an intermediate fact. Rewrite `this` using `[partial_isotropic_top]`. Then use the resulting hypothesis. Establish `hXp : F0.Xplus.map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) = F0.Xplus`.

Unfold `FlagG.Xplus`. Rewrite using `[Submodule.map_sup, hX, Submodule.map_span, Set.image_singleton]`. Use `congr 3`. Conclude with `hσ.2.2`. Establish `hWO : ∀ w, D.sp.iXY 0 w ∈ orth (hS D) F0.Xplus`.

Introduce `w`. Establish `hW` using `(Formalism.MainNotions.WHyp_Wsp D u hT (lf D F0) he hz).1`. Establish `: D.sp.iXY 0 w ∈ Wsp D ⊔ Xsp (lf D F0)` using `Submodule.mem_sup_left ⟨w, rfl⟩`. Rewrite `this` using `[hW]`. Conclude with `this`.

Establish `hdec : ∀ w, ∃ w', σ (D.sp.iXY 0 w) - D.sp.iXY 0 w' ∈ F0.X`. Introduce `w`. Use `exists_decomp_orth_isotropic_plus D u hT F0 he hz _ ?_` and prove the remaining obligations. Rewrite using `[Formalism.MainNotions.mem_orth_iff]`. Introduce `x hx`.

Rewrite `hx` using `[← hXp]`. Take `⟨x', hx', rfl⟩` from `hx`. Express the relevant statement in the definitionally equal form `(VS D).hT (σ x') (σ (D.sp.iXY 0 w)) = 0`. Rewrite using `[hσ']`. Conclude with `(Formalism.MainNotions.mem_orth_iff _ _).1 (hWO w) x' hx'`.

Set `γ0 : (D.sp.X 0).V →ₗ[D.host.E] (D.sp.X 0).V` to `projWAlt D ∘ₗ (σ : (VS D).V →ₗ[D.host.E] (VS D).V) ∘ₗ D.sp.iXY 0`. Establish `hγ0 : ∀ w, σ (D.sp.iXY 0 w) - D.sp.iXY 0 (γ0 w) ∈ F0.X`. Introduce `w`. Take `⟨w', hw'⟩` from `hdec w`. Establish `e : γ0 w = w'`.

Express the relevant statement in the definitionally equal form `projWAlt D (σ (D.sp.iXY 0 w)) = w'`. Establish `: σ (D.sp.iXY 0 w) = D.sp.iXY 0 w' + (σ (D.sp.iXY 0 w) - D.sp.iXY 0 w')` using `by abel`. Rewrite using `[this]`. Conclude with `projW_apply D w' _ (isotropic_le_orth_range D u F0 he hw')`. Rewrite using `[e]`.

Conclude with `hw'`. Establish `hiso : ∀ w w', (D.sp.X 0).hT (γ0 w) (γ0 w') = (D.sp.X 0).hT w w'`. Introduce `w w'`. Establish `e1 : σ (D.sp.iXY 0 w) = D.sp.iXY 0 (γ0 w) + (σ (D.sp.iXY 0 w) - D.sp.iXY 0 (γ0 w))` using `by abel`. Establish `e2 : σ (D.sp.iXY 0 w') = D.sp.iXY 0 (γ0 w') + (σ (D.sp.iXY 0 w') - D.sp.iXY 0 (γ0 w'))` using `by abel`.

Establish `h1` using `hσ' (D.sp.iXY 0 w) (D.sp.iXY 0 w')`. Rewrite `h1` using `[e1, e2, inner_decomp_orth_range D _ _ _ _ (isotropic_le_orth_range D u F0 he (hγ0 w)) (isotropic_le_orth_range D u F0 he (hγ0 w')), embedding_isometry_W, (Formalism.MainNotions.mem_orth_iff _ _).1 (isotropic_le_orth_isotropic F0 (hγ0 w')) _ (hγ0 w), add_zero]`. Conclude with `h1`. Establish `hinj : Function.Injective γ0`. Rewrite using `[← LinearMap.ker_eq_bot, eq_bot_iff]`.

Introduce `x hx`. Rewrite `hx` using `[LinearMap.mem_ker]`. Use `(Submodule.mem_bot _).2 ((D.sp.X 0).nondeg.2 x (fun y => ?_))` and prove the remaining obligations. Rewrite using `[← hiso y x, hx, map_zero]`. Use `⟨LinearEquiv.ofInjectiveEndo γ0 hinj, fun w w' => ?_, fun w => ?_⟩` and prove the remaining obligations.

Simplify using `using hiso w w'`. Simplify using `using hγ0 w`.
-/
theorem exists_induced_isometry_W (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hσ : σ ∈ stabF D F0) :
    ∃ γ ∈ isom (D.sp.X 0).hT, ∀ w, σ (D.sp.iXY 0 w) - D.sp.iXY 0 (γ w) ∈ F0.X := by
  have hσ' : ∀ x y, (VS D).hT (σ x) (σ y) = (VS D).hT x y := hσ.1
  have hX : F0.X.map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) = F0.X := by
    have := hσ.2.1 D.R.rS
    rwa [partial_isotropic_top] at this
  have hXp : F0.Xplus.map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) = F0.Xplus := by
    unfold FlagG.Xplus
    rw [Submodule.map_sup, hX, Submodule.map_span, Set.image_singleton]
    congr 3
    exact hσ.2.2
  have hWO : ∀ w, D.sp.iXY 0 w ∈ orth (hS D) F0.Xplus := by
    intro w
    have hW := (Formalism.MainNotions.WHyp_Wsp D u hT (lf D F0) he hz).1
    have : D.sp.iXY 0 w ∈ Wsp D ⊔ Xsp (lf D F0) := Submodule.mem_sup_left ⟨w, rfl⟩
    rw [hW] at this
    exact this
  have hdec : ∀ w, ∃ w', σ (D.sp.iXY 0 w) - D.sp.iXY 0 w' ∈ F0.X := by
    intro w
    refine exists_decomp_orth_isotropic_plus D u hT F0 he hz _ ?_
    rw [Formalism.MainNotions.mem_orth_iff]
    intro x hx
    rw [← hXp] at hx
    obtain ⟨x', hx', rfl⟩ := hx
    change (VS D).hT (σ x') (σ (D.sp.iXY 0 w)) = 0
    rw [hσ']
    exact (Formalism.MainNotions.mem_orth_iff _ _).1 (hWO w) x' hx'
  let γ0 : (D.sp.X 0).V →ₗ[D.host.E] (D.sp.X 0).V :=
    projWAlt D ∘ₗ (σ : (VS D).V →ₗ[D.host.E] (VS D).V) ∘ₗ D.sp.iXY 0
  have hγ0 : ∀ w, σ (D.sp.iXY 0 w) - D.sp.iXY 0 (γ0 w) ∈ F0.X := by
    intro w
    obtain ⟨w', hw'⟩ := hdec w
    have e : γ0 w = w' := by
      change projWAlt D (σ (D.sp.iXY 0 w)) = w'
      have : σ (D.sp.iXY 0 w) = D.sp.iXY 0 w' + (σ (D.sp.iXY 0 w) - D.sp.iXY 0 w') := by abel
      rw [this]
      exact projW_apply D w' _ (isotropic_le_orth_range D u F0 he hw')
    rw [e]
    exact hw'
  have hiso : ∀ w w', (D.sp.X 0).hT (γ0 w) (γ0 w') = (D.sp.X 0).hT w w' := by
    intro w w'
    have e1 : σ (D.sp.iXY 0 w) = D.sp.iXY 0 (γ0 w) + (σ (D.sp.iXY 0 w) - D.sp.iXY 0 (γ0 w)) := by abel
    have e2 : σ (D.sp.iXY 0 w') = D.sp.iXY 0 (γ0 w') + (σ (D.sp.iXY 0 w') - D.sp.iXY 0 (γ0 w')) := by abel
    have h1 := hσ' (D.sp.iXY 0 w) (D.sp.iXY 0 w')
    rw [e1, e2, inner_decomp_orth_range D _ _ _ _ (isotropic_le_orth_range D u F0 he (hγ0 w))
      (isotropic_le_orth_range D u F0 he (hγ0 w')), embedding_isometry_W,
      (Formalism.MainNotions.mem_orth_iff _ _).1 (isotropic_le_orth_isotropic F0 (hγ0 w')) _ (hγ0 w), add_zero] at h1
    exact h1
  have hinj : Function.Injective γ0 := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    refine (Submodule.mem_bot _).2 ((D.sp.X 0).nondeg.2 x (fun y => ?_))
    rw [← hiso y x, hx, map_zero]
  refine ⟨LinearEquiv.ofInjectiveEndo γ0 hinj, fun w w' => ?_, fun w => ?_⟩
  · simpa using hiso w w'
  · simpa using hγ0 w

end Cl

end Formalism.MainNotions.BridgeLemma₂

end
