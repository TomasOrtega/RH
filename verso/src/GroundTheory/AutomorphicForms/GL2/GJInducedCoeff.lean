import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJZetaDefs
import GroundTheory.AutomorphicForms.HaarCosets
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal Parabolic Iwasawa MeasureTheory

section Extension

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  {U : Type*} [AddCommGroup U] [Module ℂ U] {τ : Representation ℂ G U}

/- English proof (translation)
Take `⟨r, hr⟩` from `LinearMap.exists_leftInverse_of_injective (fixedMap ρ ι K) (LinearMap.ker_eq_bot.2 (fixedMap_injective ρ hι))`. Use `⟨ℓ ∘ₗ (fixedVectors ρ K).subtype ∘ₗ r ∘ₗ fixedProj τ hτ hKc hKo, fun k hk x => ?_, fun v => ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.coe_comp, Function.comp_apply]`. Rewrite using `[fixedProj_apply_act hτ hKc hKo hk]`. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]`.

Rewrite using `[fixedProj_map hKc hKo hρ hτ ι v]`. Establish `h1 : r (fixedMap ρ ι K (fixedProj ρ hρ hKc hKo v)) = fixedProj ρ hρ hKc hKo v`. Rewrite using `[← LinearMap.comp_apply, hr, LinearMap.id_apply]`. Rewrite using `[h1]`. Establish `hker : ∀ y ∈ coinvariantsKer ρ K, ℓ y = 0`.

Introduce `y hy`. Use `Submodule.span_induction ?_ (by simp) (fun a b _ _ ha hb => by rw [map_add, ha, hb, add_zero]) (fun c a _ ha => by rw [map_smul, ha, smul_zero]) hy` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Simplify using `[hℓ k.1.1 k.1.2 k.2]`. Use `hker _ (sub_fixedProj_mem hρ hKc hKo v)` as an intermediate fact.

Rewrite `this` using `[map_sub, sub_eq_zero]`. Conclude with `this.symm`.
-/
theorem exists_extend_dual (hρ : IsSmooth ρ) (hτ : IsSmooth τ)
    (ι : Representation.IntertwiningMap ρ τ) (hι : Function.Injective ι) {K : Subgroup G}
    (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) {ℓ : Module.Dual ℂ V}
    (hℓ : ∀ k ∈ K, ∀ v, ℓ (ρ k v) = ℓ v) :
    ∃ lam : Module.Dual ℂ U, (∀ k ∈ K, ∀ x, lam (τ k x) = lam x) ∧ ∀ v, lam (ι v) = ℓ v := by
  classical
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (fixedMap ρ ι K)
    (LinearMap.ker_eq_bot.2 (fixedMap_injective ρ hι))
  refine ⟨ℓ ∘ₗ (fixedVectors ρ K).subtype ∘ₗ r ∘ₗ fixedProj τ hτ hKc hKo, fun k hk x => ?_,
    fun v => ?_⟩
  · simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [fixedProj_apply_act hτ hKc hKo hk]
  · simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
    rw [fixedProj_map hKc hKo hρ hτ ι v]
    have h1 : r (fixedMap ρ ι K (fixedProj ρ hρ hKc hKo v)) = fixedProj ρ hρ hKc hKo v := by
      rw [← LinearMap.comp_apply, hr, LinearMap.id_apply]
    rw [h1]

    have hker : ∀ y ∈ coinvariantsKer ρ K, ℓ y = 0 := by
      intro y hy
      refine Submodule.span_induction ?_ (by simp) (fun a b _ _ ha hb => by rw [map_add, ha, hb, add_zero])
        (fun c a _ ha => by rw [map_smul, ha, smul_zero]) hy
      rintro _ ⟨k, rfl⟩
      simp [hℓ k.1.1 k.1.2 k.2]
    have := hker _ (sub_fixedProj_mem hρ hKc hKo v)
    rw [map_sub, sub_eq_zero] at this
    exact this.symm

end Extension

section Decomposition

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}

variable (F n) in

/- English proof (translation)
Use `set K₀ := integralGL F n`. Use `set K := congruenceSubgroup F n m`. Establish `: CompactSpace K₀` using `isCompact_iff_compactSpace.1 (isCompact_integralGL F n)`. Establish `hQ : Finite (K₀ ⧸ K.subgroupOf K₀)`. Use `Subgroup.quotient_finite_of_isOpen _ ?_` and prove the remaining obligations.

Rewrite using `[Subgroup.coe_subgroupOf]`. Conclude with `(isOpen_congruenceSubgroup F n m).preimage continuous_subtype_val`. Use `Fintype.ofFinite (K₀ ⧸ K.subgroupOf K₀)` as an intermediate fact. Use `⟨Finset.univ.image fun q : K₀ ⧸ K.subgroupOf K₀ => ((Quotient.out q : K₀) : GL (Fin n) F), ?_, fun k hk => ?_⟩` and prove the remaining obligations. Introduce `x hx`.

Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 hx`. Conclude with `(Quotient.out q).2`. Use `⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (QuotientGroup.mk (⟨k, hk⟩ : K₀))), ?_⟩` and prove the remaining obligations. Establish `h` using `QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk (⟨k, hk⟩ : K₀) : K₀ ⧸ K.subgroupOf K₀))`. Conclude with `Subgroup.mem_subgroupOf.1 h`.
-/
theorem exists_reps_congruenceSubgroup (m : ℕ) :
    ∃ R : Finset (GL (Fin n) F), (∀ x ∈ R, x ∈ integralGL F n) ∧
      ∀ k ∈ integralGL F n, ∃ x ∈ R, x⁻¹ * k ∈ congruenceSubgroup F n m := by
  classical
  set K₀ := integralGL F n
  set K := congruenceSubgroup F n m
  have : CompactSpace K₀ := isCompact_iff_compactSpace.1 (isCompact_integralGL F n)
  have hQ : Finite (K₀ ⧸ K.subgroupOf K₀) := by
    refine Subgroup.quotient_finite_of_isOpen _ ?_
    rw [Subgroup.coe_subgroupOf]
    exact (isOpen_congruenceSubgroup F n m).preimage continuous_subtype_val
  have := Fintype.ofFinite (K₀ ⧸ K.subgroupOf K₀)
  refine ⟨Finset.univ.image fun q : K₀ ⧸ K.subgroupOf K₀ => ((Quotient.out q : K₀) : GL (Fin n) F),
    ?_, fun k hk => ?_⟩
  · intro x hx
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hx
    exact (Quotient.out q).2
  · refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (QuotientGroup.mk (⟨k, hk⟩ : K₀))), ?_⟩
    have h := QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk (⟨k, hk⟩ : K₀) :
      K₀ ⧸ K.subgroupOf K₀))
    exact Subgroup.mem_subgroupOf.1 h

/- English proof (translation)
Establish `: LocallyCompactSpace (levi F n β)` using `isClosed_levi.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `set K := congruenceSubgroup F n m`. Use `set KM : Subgroup (levi F n β) := K.subgroupOf (levi F n β)`. Establish `hKMc : IsCompact (KM : Set (levi F n β))` using `isCompact_subgroupOf_levi (isCompact_congruenceSubgroup F n m)`. Establish `hKMo : IsOpen (KM : Set (levi F n β))` using `isOpen_subgroupOf_levi (isOpen_congruenceSubgroup F n m)`.

Use `set e := fixedProj σ hσ hKMc hKMo`. Set `E : fixedVectors (parabolicInd F n β σ) K →ₗ[ℂ] (R → W)` to `LinearMap.pi fun x : R => (LinearMap.proj (R := ℂ) (φ := fun _ : GL (Fin n) F => W) (x : GL (Fin n) F)) ∘ₗ (parabolicIndSpace F n β σ).subtype ∘ₗ (fixedVectors (parabolicInd F n β σ) K).subtype`. Establish `hE : ∀ ψ, E ψ = 0 → ψ = 0`. Introduce `ψ hψ`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Take `⟨p, hp, k, hk, rfl⟩` from `exists_blockUpper_mul_integralGL' (β := β) g`. Take `⟨x, hxR, hxk⟩` from `hR k hk`. Establish `h0 : ((ψ : parabolicIndSpace F n β σ) : GL (Fin n) F → W) x = 0`.

Use `congrFun hψ ⟨x, hxR⟩` as an intermediate fact. Simplify `this` using `[E]`. Establish `hfix` using `ψ.2 (x⁻¹ * k) hxk`. Establish `h1 : ((ψ : parabolicIndSpace F n β σ) : GL (Fin n) F → W) (p * k) = ((ψ : parabolicIndSpace F n β σ) : GL (Fin n) F → W) (p * x)`. Use `congrArg (fun f : parabolicIndSpace F n β σ => (f : GL (Fin n) F → W) (p * x)) hfix` as an intermediate fact.

Simplify using `only [coe_indRep_apply] at this`. Rewrite using `[← this, mul_assoc, mul_inv_cancel_left]`. Rewrite using `[h1, ((ψ : parabolicIndSpace F n β σ).2.1 ⟨p, hp⟩ x), h0]`. Simplify using the standard rewrite rules. Establish `hker : LinearMap.ker E = ⊥` using `LinearMap.ker_eq_bot'.2 hE`.

Take `⟨E', hE'⟩` from `LinearMap.exists_leftInverse_of_injective (K := ℂ) (V := fixedVectors (parabolicInd F n β σ) K) (V' := R → W) E hker`. Set `L` to `lam ∘ₗ (fixedVectors (parabolicInd F n β σ) K).subtype ∘ₗ E'`. Use `⟨fun x => if hx : x ∈ R then L ∘ₗ LinearMap.single ℂ (fun _ : R => W) ⟨x, hx⟩ ∘ₗ (fixedVectors σ KM).subtype ∘ₗ e else 0, fun x => ?_, fun ψ hψ => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ R`. Simplify using `only`.

Rewrite using `[dif_pos hx, mem_fixedVectors_dual]`. Introduce `k hk w`. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]`. Rewrite using `[fixedProj_apply_act hσ hKMc hKMo hk]`. Simplify using `only`.

Rewrite using `[dif_neg hx]`. Conclude with `zero_mem _`. Establish `hval : ∀ x ∈ R, ((fixedProj σ hσ hKMc hKMo ((ψ : GL (Fin n) F → W) x) : fixedVectors σ KM) : W) = (ψ : GL (Fin n) F → W) x` using `fun x hx => fixedProj_apply_of_mem hσ hKMc hKMo (apply_mem_fixedVectors (f := ⟨ψ, hψ⟩) (hR₀ x hx))`. Establish `hEψ : E ⟨ψ, hψ⟩ = ∑ x : R, LinearMap.single ℂ (fun _ : R => W) x ((ψ : GL (Fin n) F → W) x)`. Use function extensionality and compare the values at `y`.

Simplify using `[E, Finset.sum_apply, Pi.single_apply]`. Establish `hlam : lam ψ = L (E ⟨ψ, hψ⟩)`. Simplify using `only [L, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]`. Rewrite using `[← LinearMap.comp_apply E' E, hE', LinearMap.id_apply]`. Rewrite using `[hlam, hEψ, map_sum, ← Finset.sum_coe_sort R]`.

Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[dif_pos x.2]`. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]`. Rewrite using `[hval x x.2]`.
-/
theorem exists_eval_decomposition (hσ : IsSmooth σ) {m : ℕ} {R : Finset (GL (Fin n) F)}
    (hR₀ : ∀ x ∈ R, x ∈ integralGL F n)
    (hR : ∀ k ∈ integralGL F n, ∃ x ∈ R, x⁻¹ * k ∈ congruenceSubgroup F n m)
    (lam : Module.Dual ℂ (parabolicIndSpace F n β σ)) :
    ∃ ℓ : GL (Fin n) F → Module.Dual ℂ W,
      (∀ x, ℓ x ∈ fixedVectors (Representation.dual σ)
        ((congruenceSubgroup F n m).subgroupOf (levi F n β))) ∧
      ∀ ψ ∈ fixedVectors (parabolicInd F n β σ) (congruenceSubgroup F n m),
        lam ψ = ∑ x ∈ R, ℓ x ((ψ : GL (Fin n) F → W) x) := by
  classical
  have : LocallyCompactSpace (levi F n β) :=
    isClosed_levi.isClosedEmbedding_subtypeVal.locallyCompactSpace
  set K := congruenceSubgroup F n m
  set KM : Subgroup (levi F n β) := K.subgroupOf (levi F n β)
  have hKMc : IsCompact (KM : Set (levi F n β)) :=
    isCompact_subgroupOf_levi (isCompact_congruenceSubgroup F n m)
  have hKMo : IsOpen (KM : Set (levi F n β)) :=
    isOpen_subgroupOf_levi (isOpen_congruenceSubgroup F n m)
  set e := fixedProj σ hσ hKMc hKMo

  let E : fixedVectors (parabolicInd F n β σ) K →ₗ[ℂ] (R → W) :=
    LinearMap.pi fun x : R =>
      (LinearMap.proj (R := ℂ) (φ := fun _ : GL (Fin n) F => W) (x : GL (Fin n) F)) ∘ₗ
        (parabolicIndSpace F n β σ).subtype ∘ₗ (fixedVectors (parabolicInd F n β σ) K).subtype
  have hE : ∀ ψ, E ψ = 0 → ψ = 0 := by
    intro ψ hψ
    apply Subtype.ext
    apply Subtype.ext
    funext g
    obtain ⟨p, hp, k, hk, rfl⟩ := exists_blockUpper_mul_integralGL' (β := β) g
    obtain ⟨x, hxR, hxk⟩ := hR k hk
    have h0 : ((ψ : parabolicIndSpace F n β σ) : GL (Fin n) F → W) x = 0 := by
      have := congrFun hψ ⟨x, hxR⟩
      simpa [E] using this
    have hfix := ψ.2 (x⁻¹ * k) hxk
    have h1 : ((ψ : parabolicIndSpace F n β σ) : GL (Fin n) F → W) (p * k) =
        ((ψ : parabolicIndSpace F n β σ) : GL (Fin n) F → W) (p * x) := by
      have := congrArg (fun f : parabolicIndSpace F n β σ => (f : GL (Fin n) F → W) (p * x)) hfix
      simp only [coe_indRep_apply] at this
      rw [← this, mul_assoc, mul_inv_cancel_left]
    rw [h1, ((ψ : parabolicIndSpace F n β σ).2.1 ⟨p, hp⟩ x), h0]
    simp
  have hker : LinearMap.ker E = ⊥ := LinearMap.ker_eq_bot'.2 hE
  obtain ⟨E', hE'⟩ := LinearMap.exists_leftInverse_of_injective (K := ℂ)
    (V := fixedVectors (parabolicInd F n β σ) K) (V' := R → W) E hker
  let L := lam ∘ₗ (fixedVectors (parabolicInd F n β σ) K).subtype ∘ₗ E'
  refine ⟨fun x => if hx : x ∈ R then
      L ∘ₗ LinearMap.single ℂ (fun _ : R => W) ⟨x, hx⟩ ∘ₗ (fixedVectors σ KM).subtype ∘ₗ e
    else 0, fun x => ?_, fun ψ hψ => ?_⟩
  · by_cases hx : x ∈ R
    · dsimp only
      rw [dif_pos hx, mem_fixedVectors_dual]
      intro k hk w
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
      rw [fixedProj_apply_act hσ hKMc hKMo hk]
    · dsimp only
      rw [dif_neg hx]
      exact zero_mem _
  · have hval : ∀ x ∈ R, ((fixedProj σ hσ hKMc hKMo ((ψ : GL (Fin n) F → W) x) :
        fixedVectors σ KM) : W) = (ψ : GL (Fin n) F → W) x := fun x hx =>
      fixedProj_apply_of_mem hσ hKMc hKMo
        (apply_mem_fixedVectors (f := ⟨ψ, hψ⟩) (hR₀ x hx))
    have hEψ : E ⟨ψ, hψ⟩ = ∑ x : R, LinearMap.single ℂ (fun _ : R => W) x
        ((ψ : GL (Fin n) F → W) x) := by
      funext y
      simp [E, Finset.sum_apply, Pi.single_apply]
    have hlam : lam ψ = L (E ⟨ψ, hψ⟩) := by
      simp only [L, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
      rw [← LinearMap.comp_apply E' E, hE', LinearMap.id_apply]
    rw [hlam, hEψ, map_sum, ← Finset.sum_coe_sort R]
    refine Finset.sum_congr rfl fun x _ => ?_
    dsimp only
    rw [dif_pos x.2]
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
    rw [hval x x.2]

end Decomposition

section Integral

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}
  [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]

/- English proof (translation)
Set `Ko : OpenSubgroup (GL (Fin n) F)` to `⟨K, hKo⟩`. Establish `hφk : ∀ k ∈ K, parabolicInd F n β σ k φ = φ` using `fun k hk => hφ k hk`. Establish `hfin : (QuotientGroup.mk '' tsupport h : Set (GL (Fin n) F ⧸ K)).Finite` using `finite_image_mk_tsupport Ko hh`. Establish `hL : ∫ g, h g * lam (parabolicInd F n β σ g φ) ∂μ = μ.real (K : Set (GL (Fin n) F)) • ∑ᶠ c : GL (Fin n) F ⧸ K, h c.out * lam (parabolicInd F n β σ c.out φ)`. Use `integral_eq_smul_finsum_coset μ Ko hKc (hh.mul_right) fun g k hk => ?_` and prove the remaining obligations.

Use `show h (g * k) * lam (parabolicInd F n β σ (g * k) φ) = h g * lam (parabolicInd F n β σ g φ)`. Rewrite using `[hhr k hk, map_mul, Module.End.mul_apply, hφk k hk]`. Establish `hR : ∀ x ∈ R, ∫ g, h g * ℓ x ((φ : GL (Fin n) F → W) (x * g)) ∂μ = μ.real (K : Set (GL (Fin n) F)) • ∑ᶠ c : GL (Fin n) F ⧸ K, h c.out * ℓ x ((φ : GL (Fin n) F → W) (x * c.out))`. Introduce `x _`. Use `integral_eq_smul_finsum_coset μ Ko hKc (hh.mul_right) fun g k hk => ?_` and prove the remaining obligations.

Use `show h (g * k) * ℓ x ((φ : GL (Fin n) F → W) (x * (g * k))) = h g * ℓ x ((φ : GL (Fin n) F → W) (x * g))`. Use `congrArg (fun f : parabolicIndSpace F n β σ => (f : GL (Fin n) F → W) (x * g)) (hφk k hk)` as an intermediate fact. Simplify using `only [coe_indRep_apply] at this`. Rewrite using `[hhr k hk, ← mul_assoc, this]`. Use `set ψ : parabolicIndSpace F n β σ := ∑ᶠ c : GL (Fin n) F ⧸ K, h c.out • parabolicInd F n β σ c.out φ with hψdef`.

Establish `hψsupp : (Function.support fun c : GL (Fin n) F ⧸ K => h c.out • parabolicInd F n β σ c.out φ).Finite` using `hfin.subset fun c hc => ⟨c.out, subset_tsupport h fun h0 => hc (by simp [h0]), QuotientGroup.out_eq' c⟩`. Establish `hψK : ψ ∈ fixedVectors (parabolicInd F n β σ) K`. Introduce `k hk`. Rewrite using `[hψdef, map_finsum (parabolicInd F n β σ k) hψsupp]`. Establish `hterm : ∀ c : GL (Fin n) F ⧸ K, parabolicInd F n β σ k (h c.out • parabolicInd F n β σ c.out φ) = (fun c : GL (Fin n) F ⧸ K => h c.out • parabolicInd F n β σ c.out φ) (MulAction.toPerm k c)`.

Introduce `c`. Establish `hmk : (QuotientGroup.mk (k * c.out) : GL (Fin n) F ⧸ K) = MulAction.toPerm k c` using `by show QuotientGroup.mk (k * c.out) = k • c conv_rhs => rw [← QuotientGroup.out_eq' c]`. Both sides reduce to the same expression. Choose the witnesses or unpack the hypotheses as in `⟨j, hj, hjeq⟩ : ∃ j ∈ K, k * c.out = (MulAction.toPerm k c).out * j := by`. Use `⟨((MulAction.toPerm k c).out)⁻¹ * (k * c.out), ?_, by group⟩` and prove the remaining obligations.

Use `QuotientGroup.eq.1 ((QuotientGroup.out_eq' (MulAction.toPerm k c)).trans hmk.symm)` as an intermediate fact. Simplify using `using this`. Establish `hhc : h c.out = h (MulAction.toPerm k c).out`. Rewrite using `[← hhl k hk c.out, hjeq, hhr j hj]`. Simplify using `only`.

Rewrite using `[map_smul, ← Module.End.mul_apply, ← map_mul, hjeq, map_mul, Module.End.mul_apply, hφk j hj, hhc]`. Rewrite using `[finsum_congr hterm]`. Conclude with `finsum_comp_equiv (MulAction.toPerm k) (f := fun c : GL (Fin n) F ⧸ K => h c.out • parabolicInd F n β σ c.out φ)`. Establish `h1 : lam ψ = ∑ᶠ c : GL (Fin n) F ⧸ K, h c.out * lam (parabolicInd F n β σ c.out φ)`. Rewrite using `[hψdef, map_finsum lam hψsupp]`.

Simplify using `only [map_smul, smul_eq_mul]`. Establish `h2 : ∀ x ∈ R, ℓ x ((ψ : GL (Fin n) F → W) x) = ∑ᶠ c : GL (Fin n) F ⧸ K, h c.out * ℓ x ((φ : GL (Fin n) F → W) (x * c.out))`. Introduce `x _`. Set `ev : parabolicIndSpace F n β σ →ₗ[ℂ] W` to `LinearMap.proj (R := ℂ) (φ := fun _ : GL (Fin n) F => W) x ∘ₗ (parabolicIndSpace F n β σ).subtype`. Establish `hev : (ψ : GL (Fin n) F → W) x = ev ψ` using `rfl`.

Rewrite using `[hev, hψdef, map_finsum ev hψsupp, map_finsum (ℓ x)]`. Use `finsum_congr fun c => ?_` and prove the remaining obligations. Simplify using `[ev, coe_indRep_apply]`. Conclude with `hfin.subset fun c hc => ⟨c.out, subset_tsupport h fun h0 => hc (by simp [h0]), QuotientGroup.out_eq' c⟩`. Rewrite using `[hL, ← h1, hdec ψ hψK, Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun x hx => ?_` and prove the remaining obligations. Rewrite using `[hR x hx, h2 x hx]`.
-/
theorem integral_mul_coeff_eq (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure]
    {K : Subgroup (GL (Fin n) F)} (hKc : IsCompact (K : Set (GL (Fin n) F)))
    (hKo : IsOpen (K : Set (GL (Fin n) F)))
    {lam : Module.Dual ℂ (parabolicIndSpace F n β σ)}
    {φ : parabolicIndSpace F n β σ} (hφ : φ ∈ fixedVectors (parabolicInd F n β σ) K)
    {R : Finset (GL (Fin n) F)} {ℓ : GL (Fin n) F → Module.Dual ℂ W}
    (hdec : ∀ ψ ∈ fixedVectors (parabolicInd F n β σ) K,
      lam ψ = ∑ x ∈ R, ℓ x ((ψ : GL (Fin n) F → W) x))
    {h : GL (Fin n) F → ℂ} (hh : HasCompactSupport h) (hhl : ∀ k ∈ K, ∀ g, h (k * g) = h g)
    (hhr : ∀ k ∈ K, ∀ g, h (g * k) = h g) :
    ∫ g, h g * lam (parabolicInd F n β σ g φ) ∂μ =
      ∑ x ∈ R, ∫ g, h g * ℓ x ((φ : GL (Fin n) F → W) (x * g)) ∂μ := by
  classical
  let Ko : OpenSubgroup (GL (Fin n) F) := ⟨K, hKo⟩
  have hφk : ∀ k ∈ K, parabolicInd F n β σ k φ = φ := fun k hk => hφ k hk

  have hfin : (QuotientGroup.mk '' tsupport h : Set (GL (Fin n) F ⧸ K)).Finite :=
    finite_image_mk_tsupport Ko hh

  have hL : ∫ g, h g * lam (parabolicInd F n β σ g φ) ∂μ = μ.real (K : Set (GL (Fin n) F)) •
      ∑ᶠ c : GL (Fin n) F ⧸ K, h c.out * lam (parabolicInd F n β σ c.out φ) := by
    refine integral_eq_smul_finsum_coset μ Ko hKc (hh.mul_right) fun g k hk => ?_
    show h (g * k) * lam (parabolicInd F n β σ (g * k) φ) = h g * lam (parabolicInd F n β σ g φ)
    rw [hhr k hk, map_mul, Module.End.mul_apply, hφk k hk]
  have hR : ∀ x ∈ R, ∫ g, h g * ℓ x ((φ : GL (Fin n) F → W) (x * g)) ∂μ = μ.real (K : Set (GL (Fin n) F)) •
      ∑ᶠ c : GL (Fin n) F ⧸ K, h c.out * ℓ x ((φ : GL (Fin n) F → W) (x * c.out)) := by
    intro x _
    refine integral_eq_smul_finsum_coset μ Ko hKc (hh.mul_right) fun g k hk => ?_
    show h (g * k) * ℓ x ((φ : GL (Fin n) F → W) (x * (g * k))) = h g * ℓ x ((φ : GL (Fin n) F → W) (x * g))
    have := congrArg (fun f : parabolicIndSpace F n β σ => (f : GL (Fin n) F → W) (x * g)) (hφk k hk)
    simp only [coe_indRep_apply] at this
    rw [hhr k hk, ← mul_assoc, this]

  set ψ : parabolicIndSpace F n β σ := ∑ᶠ c : GL (Fin n) F ⧸ K, h c.out • parabolicInd F n β σ c.out φ
    with hψdef
  have hψsupp : (Function.support fun c : GL (Fin n) F ⧸ K =>
      h c.out • parabolicInd F n β σ c.out φ).Finite :=
    hfin.subset fun c hc => ⟨c.out, subset_tsupport h fun h0 => hc (by simp [h0]),
      QuotientGroup.out_eq' c⟩
  have hψK : ψ ∈ fixedVectors (parabolicInd F n β σ) K := by
    intro k hk
    rw [hψdef, map_finsum (parabolicInd F n β σ k) hψsupp]
    have hterm : ∀ c : GL (Fin n) F ⧸ K,
        parabolicInd F n β σ k (h c.out • parabolicInd F n β σ c.out φ) =
        (fun c : GL (Fin n) F ⧸ K => h c.out • parabolicInd F n β σ c.out φ)
          (MulAction.toPerm k c) := by
      intro c
      have hmk : (QuotientGroup.mk (k * c.out) : GL (Fin n) F ⧸ K) = MulAction.toPerm k c := by
        show QuotientGroup.mk (k * c.out) = k • c
        conv_rhs => rw [← QuotientGroup.out_eq' c]
        rfl
      obtain ⟨j, hj, hjeq⟩ : ∃ j ∈ K, k * c.out = (MulAction.toPerm k c).out * j := by
        refine ⟨((MulAction.toPerm k c).out)⁻¹ * (k * c.out), ?_, by group⟩
        have := QuotientGroup.eq.1 ((QuotientGroup.out_eq' (MulAction.toPerm k c)).trans hmk.symm)
        simpa using this
      have hhc : h c.out = h (MulAction.toPerm k c).out := by
        rw [← hhl k hk c.out, hjeq, hhr j hj]
      dsimp only
      rw [map_smul, ← Module.End.mul_apply, ← map_mul, hjeq, map_mul, Module.End.mul_apply,
        hφk j hj, hhc]
    rw [finsum_congr hterm]
    exact finsum_comp_equiv (MulAction.toPerm k) (f := fun c : GL (Fin n) F ⧸ K =>
      h c.out • parabolicInd F n β σ c.out φ)

  have h1 : lam ψ = ∑ᶠ c : GL (Fin n) F ⧸ K, h c.out * lam (parabolicInd F n β σ c.out φ) := by
    rw [hψdef, map_finsum lam hψsupp]
    simp only [map_smul, smul_eq_mul]
  have h2 : ∀ x ∈ R, ℓ x ((ψ : GL (Fin n) F → W) x) =
      ∑ᶠ c : GL (Fin n) F ⧸ K, h c.out * ℓ x ((φ : GL (Fin n) F → W) (x * c.out)) := by
    intro x _
    let ev : parabolicIndSpace F n β σ →ₗ[ℂ] W :=
      LinearMap.proj (R := ℂ) (φ := fun _ : GL (Fin n) F => W) x ∘ₗ
        (parabolicIndSpace F n β σ).subtype
    have hev : (ψ : GL (Fin n) F → W) x = ev ψ := rfl
    rw [hev, hψdef, map_finsum ev hψsupp, map_finsum (ℓ x)]
    · refine finsum_congr fun c => ?_
      simp [ev, coe_indRep_apply]
    · exact hfin.subset fun c hc => ⟨c.out, subset_tsupport h fun h0 => hc (by simp [h0]),
        QuotientGroup.out_eq' c⟩
  rw [hL, ← h1, hdec ψ hψK, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [hR x hx, h2 x hx]

end Integral

end GodementJacquet

end GroundTheory.Automorphic
