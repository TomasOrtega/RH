import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosure
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaFreeFiniteBijectiveOfSmooth
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulEqZeroOfToCompletion

set_option autoImplicit false

noncomputable section

open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj

namespace GlobalTheory.HodgeTateEigenRank

section Algebra

variable {O C : Type} [CommRing O] [IsDomain O] [Field C] [Algebra O C] [IsFractionRing O C]
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by rwa [one_smul]⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha, hx⟩` from `hx`.

Take `⟨b, hb, hy⟩` from `hy`. Use `⟨a * b, mul_ne_zero ha hb, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `Submodule.add_mem _ ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`.

Conclude with `Submodule.smul_mem _ _ hx`. Rewrite using `[mul_smul]`. Conclude with `Submodule.smul_mem _ _ hy`. Consider the case `smul c x _ hx`. Take `⟨r, hr, hx⟩` from `hx`.

Take `⟨⟨a, b⟩, hab⟩` from `IsLocalization.surj (nonZeroDivisors O) c`. Use `⟨b * r, mul_ne_zero (nonZeroDivisors.coe_ne_zero b) hr, ?_⟩` and prove the remaining obligations. Establish `h1 : (b : O) • c • x = a • x`. Rewrite using `[← algebraMap_smul C (b : O), smul_smul, mul_comm, hab, algebraMap_smul]`. Rewrite using `[mul_comm, mul_smul, h1, smul_comm]`.

Conclude with `N.smul_mem _ hx`.
-/
theorem exists_smul_mem_of_mem_span (N : Submodule O V) {x : V}
    (hx : x ∈ Submodule.span C (N : Set V)) : ∃ s : O, s ≠ 0 ∧ s • x ∈ N := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rwa [one_smul]⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine Submodule.add_mem _ ?_ ?_
    · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hx
    · rw [mul_smul]; exact Submodule.smul_mem _ _ hy
  | smul c x _ hx =>
    obtain ⟨r, hr, hx⟩ := hx
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors O) c
    refine ⟨b * r, mul_ne_zero (nonZeroDivisors.coe_ne_zero b) hr, ?_⟩
    have h1 : (b : O) • c • x = a • x := by
      rw [← algebraMap_smul C (b : O), smul_smul, mul_comm, hab, algebraMap_smul]
    rw [mul_comm, mul_smul, h1, smul_comm]
    exact N.smul_mem _ hx

/- English proof (translation)
Set `b` to `Module.finBasis O M`. Establish `h1 : LinearIndependent O (B ∘ b)` using `b.linearIndependent.map' B (LinearMap.ker_eq_bot.2 hB)`. Establish `h2 : LinearIndependent C (B ∘ b)` using `(LinearIndependent.iff_fractionRing O C).1 h1`. Establish `h3 : Submodule.span C (Set.range B) = Submodule.span C (Set.range (B ∘ b))`. Rewrite using `[← Submodule.span_span_of_tower O C (Set.range (B ∘ b)), Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_top, LinearMap.coe_range]`.

Rewrite using `[h3, finrank_span_eq_card h2, Fintype.card_fin]`.
-/
theorem finrank_span_range {M : Type} [AddCommGroup M] [Module O M] [Module.Free O M]
    [Module.Finite O M] (B : M →ₗ[O] V) (hB : Function.Injective B) :
    Module.finrank C (Submodule.span C (Set.range B)) = Module.finrank O M := by
  let b := Module.finBasis O M
  have h1 : LinearIndependent O (B ∘ b) :=
    b.linearIndependent.map' B (LinearMap.ker_eq_bot.2 hB)
  have h2 : LinearIndependent C (B ∘ b) := (LinearIndependent.iff_fractionRing O C).1 h1
  have h3 : Submodule.span C (Set.range B) = Submodule.span C (Set.range (B ∘ b)) := by
    rw [← Submodule.span_span_of_tower O C (Set.range (B ∘ b)), Set.range_comp,
      Submodule.span_image, b.span_eq, Submodule.map_top, LinearMap.coe_range]
  rw [h3, finrank_span_eq_card h2, Fintype.card_fin]

end Algebra

open GlobalTheory.HodgeTateCompare GlobalTheory.EigenLieCompare GlobalTheory.EigenSplit AlgebraicGeometry in

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P hcok hW τ`. Use `haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)`. Use `haveI : ValuationRing O := ValuationRing.of_integers v P.integers`. Use `haveI : IsFractionRing O C := P.integers.isFractionRing`. Use `haveI := (GlobalTheory.UnitRigidity.smooth_geometricallyConnected_of_isGt _ _ ⟨P.D⟩).1`.

Take `⟨-, -, hb⟩` from `Point.omega_free_finite_bijective p C v O Λ P`. Establish `hp : algebraMap O C ((p : O) ^ 2) ≠ 0`. Rewrite using `[map_pow, map_natCast]`. Conclude with `pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)`. Establish `hinj : Function.Injective P.bLie`.

Introduce `x y hxy`. Establish `h0 : ∀ t, (P.al₀ t).1 x = (P.al₀ t).1 y` using `fun t => P.integers.hom_inj (by`. Rewrite using `[← P.pairV_bLie, ← P.pairV_bLie, hxy])`. Establish `h1 : ∀ z, (P.al z).1 x = (P.al z).1 y` using `fun z => by`. Proceed by induction on `z using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add z z' hz hz' => simp only [map_add, Submodule.coe_add, Pi.add_apply, hz, hz']`. Consider the case `tmul c t => simp only [Point.al_tmul, Submodule.coe_smul, Pi.smul_apply, h0]`. Use `hb.1 (LinearMap.ext fun f => ?_)` and prove the remaining obligations. Take `⟨z, hz⟩` from `hcok f`.

Establish `h2` using `h1 z`. Rewrite `h2` using `[hz]`. Conclude with `mul_left_cancel₀ (fun h => hp (by rw [h, map_zero])) h2`. Take `⟨h₁, h₂⟩` from `finite_free_eigSub P.oGt τ`. Set `B : eigSub P.oGt τ →ₗ[O] P.V` to `{ toFun := fun x => P.bLie (lieEquiv P.Gt x.1) map_add' := fun x y => by`.

Rewrite using `[← P.bLie_add]`. Conclude with `congrArg P.bLie (Subtype.ext (lieEquiv_add x.1 y.1))`. Use the proof step `map_smul' := fun c x => by`. Rewrite using `[RingHom.id_apply, ← P.bLie_scale]`. Conclude with `congrArg P.bLie (Subtype.ext (lieEquiv_smul c x.1)) }`.

Establish `hBi : Function.Injective B` using `fun x y h => Subtype.ext ((lieEquiv P.Gt).injective (hinj h))`. Establish `hr : Set.range B = P.wRec τ`. Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩`.

Conclude with `⟨(eigEquiv P.oGt τ).symm (subEquiv P.oGt τ x), rfl⟩`. Introduce and unpack `⟨x, rfl⟩`. Use `⟨(subEquiv P.oGt τ).symm (eigEquiv P.oGt τ x), congrArg P.bLie ?_⟩` and prove the remaining obligations. Conclude with `(subEquiv_val P.oGt τ _).symm.trans (congrArg Subtype.val ((subEquiv P.oGt τ).apply_symm_apply _))`. Establish `hE : P.eigW τ = Submodule.span C (Set.range B)`.

Rewrite using `[hr]`. Use `le_antisymm ?_ (Submodule.span_le.2 fun w hw => ?_)` and prove the remaining obligations. Introduce and unpack `w ⟨hw, hwτ⟩`. Rewrite `hw` using `[hW]`. Take `⟨s, hs, x, hx⟩` from `exists_smul_mem_of_mem_span (C := C) P.latLie hw`.

Establish `hs' : algebraMap O C s ≠ 0` using `fun h => hs (P.integers.hom_inj (by rw [h, map_zero]))`. Establish `hxτ : P.bLie x ∈ P.eigV τ`. Rewrite using `[hx, ← algebraMap_smul C s]`. Conclude with `Submodule.smul_mem _ _ hwτ`. Establish `hx' : AvDefs.IsEig P.Gt P.oGt τ x` using `fun a => hinj (by`.

Rewrite using `[P.bLie_act, P.bLie_scale, mem_eigenSub.1 hxτ a, RingHom.comp_apply, algebraMap_smul])`. Establish `: w = (algebraMap O C s)⁻¹ • P.bLie x`. Rewrite using `[hx, ← algebraMap_smul C s, smul_smul, inv_mul_cancel₀ hs', one_smul]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨x, hx'⟩, rfl⟩)`.

Establish `h` using `P.wRec_le τ hw`. Use `⟨?_, h.2⟩` and prove the remaining obligations. Rewrite using `[hW]`. Conclude with `Submodule.subset_span h.1`. Rewrite using `[hE, finrank_span_range B hBi, rTau_eq, eigRank_eq, Module.finrank_linearMap_self]`.
-/
theorem finrank_eigW : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), CokernelBound P → P.W = Submodule.span C (Set.range P.bLie) → ∀ τ : Λ →+* O, Module.finrank C (P.eigW τ) = AvDefs.rTau P.Gt P.oGt τ := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P hcok hW τ
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  haveI : ValuationRing O := ValuationRing.of_integers v P.integers
  haveI : IsFractionRing O C := P.integers.isFractionRing
  haveI := (GlobalTheory.UnitRigidity.smooth_geometricallyConnected_of_isGt _ _ ⟨P.D⟩).1
  obtain ⟨-, -, hb⟩ := Point.omega_free_finite_bijective p C v O Λ P
  have hp : algebraMap O C ((p : O) ^ 2) ≠ 0 := by
    rw [map_pow, map_natCast]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hinj : Function.Injective P.bLie := by
    intro x y hxy
    have h0 : ∀ t, (P.al₀ t).1 x = (P.al₀ t).1 y := fun t => P.integers.hom_inj (by
      rw [← P.pairV_bLie, ← P.pairV_bLie, hxy])
    have h1 : ∀ z, (P.al z).1 x = (P.al z).1 y := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z z' hz hz' => simp only [map_add, Submodule.coe_add, Pi.add_apply, hz, hz']
      | tmul c t => simp only [Point.al_tmul, Submodule.coe_smul, Pi.smul_apply, h0]
    refine hb.1 (LinearMap.ext fun f => ?_)
    obtain ⟨z, hz⟩ := hcok f
    have h2 := h1 z
    rw [hz] at h2
    exact mul_left_cancel₀ (fun h => hp (by rw [h, map_zero])) h2
  obtain ⟨h₁, h₂⟩ := finite_free_eigSub P.oGt τ
  let B : eigSub P.oGt τ →ₗ[O] P.V :=
    { toFun := fun x => P.bLie (lieEquiv P.Gt x.1)
      map_add' := fun x y => by
        rw [← P.bLie_add]
        exact congrArg P.bLie (Subtype.ext (lieEquiv_add x.1 y.1))
      map_smul' := fun c x => by
        rw [RingHom.id_apply, ← P.bLie_scale]
        exact congrArg P.bLie (Subtype.ext (lieEquiv_smul c x.1)) }
  have hBi : Function.Injective B := fun x y h =>
    Subtype.ext ((lieEquiv P.Gt).injective (hinj h))
  have hr : Set.range B = P.wRec τ := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(eigEquiv P.oGt τ).symm (subEquiv P.oGt τ x), rfl⟩
    · rintro ⟨x, rfl⟩
      refine ⟨(subEquiv P.oGt τ).symm (eigEquiv P.oGt τ x), congrArg P.bLie ?_⟩
      exact (subEquiv_val P.oGt τ _).symm.trans
        (congrArg Subtype.val ((subEquiv P.oGt τ).apply_symm_apply _))
  have hE : P.eigW τ = Submodule.span C (Set.range B) := by
    rw [hr]
    refine le_antisymm ?_ (Submodule.span_le.2 fun w hw => ?_)
    · rintro w ⟨hw, hwτ⟩
      rw [hW] at hw
      obtain ⟨s, hs, x, hx⟩ := exists_smul_mem_of_mem_span (C := C) P.latLie hw
      have hs' : algebraMap O C s ≠ 0 := fun h => hs (P.integers.hom_inj (by rw [h, map_zero]))
      have hxτ : P.bLie x ∈ P.eigV τ := by
        rw [hx, ← algebraMap_smul C s]
        exact Submodule.smul_mem _ _ hwτ
      have hx' : AvDefs.IsEig P.Gt P.oGt τ x := fun a => hinj (by
        rw [P.bLie_act, P.bLie_scale, mem_eigenSub.1 hxτ a, RingHom.comp_apply, algebraMap_smul])
      have : w = (algebraMap O C s)⁻¹ • P.bLie x := by
        rw [hx, ← algebraMap_smul C s, smul_smul, inv_mul_cancel₀ hs', one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨x, hx'⟩, rfl⟩)
    · have h := P.wRec_le τ hw
      refine ⟨?_, h.2⟩
      rw [hW]
      exact Submodule.subset_span h.1
  rw [hE, finrank_span_range B hBi, rTau_eq, eigRank_eq, Module.finrank_linearMap_self]

end GlobalTheory.HodgeTateEigenRank
