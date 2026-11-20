import Mathlib
import ReciprocityTheory.NeutralLocalFields.Duality
import ReciprocityTheory.GroupCohomology.LengthKerEqCoker

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.InflationOneCocycles

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

noncomputable section

variable {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (N : Subgroup G) [N.Normal] {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  (rho : Representation R G M)

def qRho (hN : ∀ σ ∈ N, ∀ m, rho σ m = m) : Representation R (G ⧸ N) M :=
  QuotientGroup.lift N rho (fun σ hσ => LinearMap.ext (hN σ hσ))

abbrev qT (hrho : ContAction rho) (hN : ∀ σ ∈ N, ∀ m, rho σ m = m) : TRep R (G ⧸ N) where
  V := M
  rho := qRho N rho hN
  cont := by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    rw [← QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff]
    exact hrho.comp (continuous_id.prodMk continuous_const)

scoped instance (hrho : ContAction rho) (hN : ∀ σ ∈ N, ∀ m, rho σ m = m) : DiscreteTopology (qT N rho hrho hN).V :=
  inferInstanceAs (DiscreteTopology M)

variable {N rho}

/- English proof (translation)
Establish `hw : ∀ a b : G, QuotientGroup.leftRel N a b → c a = c b`. Introduce `a b hab`. Establish `h1 : a⁻¹ * b ∈ N` using `QuotientGroup.leftRel_apply.1 hab`. Establish `h2` using `hc.2 a (a⁻¹ * b)`. Rewrite `h2` using `[mul_inv_cancel_left, h0 _ h1, map_zero, add_zero]`.

Conclude with `h2.symm`. Use `⟨fun q => Quotient.liftOn' q c hw, ⟨?_, ?_⟩, fun g => rfl⟩` and prove the remaining obligations. Conclude with `hc.1.quotient_liftOn' hw`. Introduce `a b`. Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective a`.

Take `⟨h, rfl⟩` from `QuotientGroup.mk_surjective b`. Conclude with `hc.2 g h`.
-/
theorem exists_desc1 (hN : ∀ σ ∈ N, ∀ m, rho σ m = m) (c : G → M) (hc : c ∈ Z1 rho) (h0 : ∀ σ ∈ N, c σ = 0) :
    ∃ c' : G ⧸ N → M, c' ∈ ReciprocityTheory.Gal.Z1 (qRho N rho hN) ∧ ∀ g, c' (QuotientGroup.mk g) = c g := by
  have hw : ∀ a b : G, QuotientGroup.leftRel N a b → c a = c b := by
    intro a b hab
    have h1 : a⁻¹ * b ∈ N := QuotientGroup.leftRel_apply.1 hab
    have h2 := hc.2 a (a⁻¹ * b)
    rw [mul_inv_cancel_left, h0 _ h1, map_zero, add_zero] at h2
    exact h2.symm
  refine ⟨fun q => Quotient.liftOn' q c hw, ⟨?_, ?_⟩, fun g => rfl⟩
  · exact hc.1.quotient_liftOn' hw
  · intro a b
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective b
    exact hc.2 g h

/- English proof (translation)
Assemble the required witnesses or components as `⟨hc.1.comp QuotientGroup.continuous_mk, fun g h => hc.2 (QuotientGroup.mk g) (QuotientGroup.mk h)⟩`.
-/
theorem inflation_mem_one_cocycles (hN : ∀ σ ∈ N, ∀ m, rho σ m = m) (c' : G ⧸ N → M) (hc : c' ∈ ReciprocityTheory.Gal.Z1 (qRho N rho hN)) :
    (fun g : G => c' (QuotientGroup.mk g)) ∈ Z1 rho :=
  ⟨hc.1.comp QuotientGroup.continuous_mk, fun g h => hc.2 (QuotientGroup.mk g) (QuotientGroup.mk h)⟩

/- English proof (translation)
Establish `h1 : (Submodule.Quotient.mk (restrictCocycles1 rho N.subtype continuous_subtype_val c) : H1 (rho.comp N.subtype)) = 0` using `hc`. Rewrite `h1` using `[Submodule.Quotient.mk_eq_zero]`. Take `⟨m, hm⟩` from `(mem_contCoboundaries1 _ _).1 h1`. Establish `h3 : c.1 σ = rho σ m - m` using `hm ⟨σ, hσ⟩`. Rewrite using `[h3, hN σ hσ, sub_self]`.
-/
theorem apply_eq_zero_of_mem_H1ur (hN : ∀ σ ∈ N, ∀ m, rho σ m = m) (c : Z1 rho)
    (hc : (Submodule.Quotient.mk c : H1 rho) ∈ H1ur rho N) (σ : G) (hσ : σ ∈ N) : c.1 σ = 0 := by
  have h1 : (Submodule.Quotient.mk (restrictCocycles1 rho N.subtype continuous_subtype_val c) : H1 (rho.comp N.subtype)) = 0 := hc
  rw [Submodule.Quotient.mk_eq_zero] at h1
  obtain ⟨m, hm⟩ := (mem_contCoboundaries1 _ _).1 h1
  have h3 : c.1 σ = rho σ m - m := hm ⟨σ, hσ⟩
  rw [h3, hN σ hσ, sub_self]

/- English proof (translation)
Assemble the required witnesses or components as `⟨Nat.card M, Nat.card_pos, card_nsmul_eq_zero'⟩`.
-/
theorem torsion_of_finite [Finite M] (m : M) : ∃ k : ℕ, 0 < k ∧ k • m = 0 :=
  ⟨Nat.card M, Nat.card_pos, card_nsmul_eq_zero'⟩

variable [CompactSpace (G ⧸ N)] [T2Space (G ⧸ N)] [TotallyDisconnectedSpace (G ⧸ N)] [Finite M]

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero, mem_riemannRochSpace_iff_regularAt_everywhere]`. Use `⟨fun h g => ?_, fun h => h s⟩` and prove the remaining obligations. Use `set W := ProcyclicCohomology.stab (qT N rho hrho hN) m with hW`. Establish `hWo : IsOpen (W : Set (G ⧸ N))` using `ProcyclicCohomology.stab_isOpen (qT N rho hrho hN) m`.

Establish `hWc : IsClosed (W : Set (G ⧸ N))` using `W.isClosed_of_isOpen hWo`. Establish `hsW : (QuotientGroup.mk s : G ⧸ N) ∈ W` using `h`. Establish `hz : (Subgroup.zpowers (QuotientGroup.mk s : G ⧸ N) : Set (G ⧸ N)) ⊆ W` using `(Subgroup.zpowers_le.2 hsW)`. Establish `htop : (W : Set (G ⧸ N)) = Set.univ`. Rewrite using `[← hWc.closure_eq, ← Set.univ_subset_iff, ← hs.1.closure_eq]`.

Conclude with `closure_mono hz`. Establish `: (QuotientGroup.mk g : G ⧸ N) ∈ (W : Set (G ⧸ N))` using `by rw [htop]; trivial`. Conclude with `this`.
-/
theorem ker_frobenius_sub_id_eq_invariants (hrho : ContAction rho) (hN : ∀ σ ∈ N, ∀ m, rho σ m = m) {s : G}
    (hs : IsZHat (G ⧸ N) (QuotientGroup.mk s)) : LinearMap.ker (rho s - LinearMap.id) = H0 rho := by
  ext m
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero, mem_riemannRochSpace_iff_regularAt_everywhere]
  refine ⟨fun h g => ?_, fun h => h s⟩
  set W := ProcyclicCohomology.stab (qT N rho hrho hN) m with hW
  have hWo : IsOpen (W : Set (G ⧸ N)) := ProcyclicCohomology.stab_isOpen (qT N rho hrho hN) m
  have hWc : IsClosed (W : Set (G ⧸ N)) := W.isClosed_of_isOpen hWo
  have hsW : (QuotientGroup.mk s : G ⧸ N) ∈ W := h
  have hz : (Subgroup.zpowers (QuotientGroup.mk s : G ⧸ N) : Set (G ⧸ N)) ⊆ W :=
    (Subgroup.zpowers_le.2 hsW)
  have htop : (W : Set (G ⧸ N)) = Set.univ := by
    rw [← hWc.closure_eq, ← Set.univ_subset_iff, ← hs.1.closure_eq]
    exact closure_mono hz
  have : (QuotientGroup.mk g : G ⧸ N) ∈ (W : Set (G ⧸ N)) := by rw [htop]; trivial
  exact this

/- English proof (translation)
Establish `h1` using `Submodule.card_eq_card_quotient_mul_card (LinearMap.range u)`. Establish `h2` using `Submodule.card_eq_card_quotient_mul_card (LinearMap.ker u)`. Rewrite `h2` using `[Nat.card_congr u.quotKerEquivRange.toEquiv]`. Establish `h3 : 0 < Nat.card (LinearMap.range u)` using `Nat.card_pos`. Rewrite `h1` using `[h2, mul_comm]`.

Conclude with `(Nat.eq_of_mul_eq_mul_left h3 h1).symm`.
-/
theorem card_quot_range (u : M →ₗ[R] M) : Nat.card (M ⧸ LinearMap.range u) = Nat.card (LinearMap.ker u) := by
  have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range u)
  have h2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker u)
  rw [Nat.card_congr u.quotKerEquivRange.toEquiv] at h2
  have h3 : 0 < Nat.card (LinearMap.range u) := Nat.card_pos
  rw [h2, mul_comm] at h1
  exact (Nat.eq_of_mul_eq_mul_left h3 h1).symm

/- English proof (translation)
Use `set P : Submodule R M := LinearMap.range (rho s - LinearMap.id) with hP`. Set `f : Z1 rho →ₗ[R] M ⧸ P` to `P.mkQ ∘ₗ ((LinearMap.proj s) ∘ₗ (Z1 rho).subtype)`. Establish `hker : (Bd1 rho).comap (Z1 rho).subtype ≤ LinearMap.ker f`. Introduce `c hc'`. Take `⟨m, hm⟩` from `(mem_contCoboundaries1 _ _).1 hc'`.

Rewrite using `[LinearMap.mem_ker]`. Express the relevant statement in the definitionally equal form `(Submodule.Quotient.mk (c.1 s) : M ⧸ P) = 0`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Conclude with `⟨m, by simpa using (hm s).symm⟩`. Set `φ : H1 rho →ₗ[R] M ⧸ P` to `((Bd1 rho).comap (Z1 rho).subtype).liftQ f hker`.

Establish `hφ : ∀ c : Z1 rho, φ (Submodule.Quotient.mk c) = Submodule.Quotient.mk (c.1 s)` using `fun c => rfl`. Establish `hinj0 : ∀ z ∈ H1ur rho N, φ z = 0 → z = 0`. Introduce `z hz hz0`. Take `⟨c, rfl⟩` from `Submodule.Quotient.mk_surjective _ z`. Take `⟨c', hc', hcc⟩` from `exists_desc1 hN c.1 c.2 (apply_eq_zero_of_mem_H1ur hN c hz)`.

Rewrite `hz0` using `[hφ, Submodule.Quotient.mk_eq_zero]`. Take `⟨m, hm⟩` from `hz0`. Establish `h1 : c' (QuotientGroup.mk s) = rho s m - m` using `by rw [hcc, ← hm]; rfl`. Establish `h2` using `ProcyclicCohomology.cocycle_eq_of_apply (qT N rho hrho hN) hs.1 c' hc' m h1`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`.

Use `(mem_contCoboundaries1 _ _).2 ⟨m, fun g => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `c.1 g = _`. Rewrite using `[← hcc]`. Conclude with `h2 (QuotientGroup.mk g)`. Establish `hbij : Bijective (fun x : H1ur rho N => φ x.1)`.

Prove the components needed by the constructor for the conclusion. Introduce `x y hxy`. Establish `h1 : φ (x.1 - y.1) = 0` using `by rw [map_sub]; exact sub_eq_zero.2 hxy`. Conclude with `Subtype.ext (sub_eq_zero.1 (hinj0 _ ((H1ur rho N).sub_mem x.2 y.2) h1))`. Introduce `y`.

Take `⟨m, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Take `⟨c', hc', hcs⟩` from `ProcyclicCohomology.exists_cocycle (qT N rho hrho hN) (ProcyclicCohomology.comm_of_dense hs.1) hs.1 hs.2 m (torsion_of_finite (M := M) m)`. Establish `hZ` using `inflation_mem_one_cocycles hN c' hc'`. Use `⟨⟨Submodule.Quotient.mk ⟨_, hZ⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(Submodule.Quotient.mk (restrictCocycles1 rho N.subtype continuous_subtype_val ⟨_, hZ⟩) : H1 (rho.comp N.subtype)) = 0`.

Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Use `(mem_contCoboundaries1 _ _).2 ⟨0, fun σ => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `c' (QuotientGroup.mk σ.1) = _`. Rewrite using `[(QuotientGroup.eq_one_iff σ.1).2 σ.2, map_zero, sub_zero]`. Establish `h1 : c' (1 * 1) = c' 1 + qRho N rho hN 1 (c' 1)` using `hc'.2 1 1`.

Rewrite `h1` using `[mul_one, map_one, Module.End.one_apply]`. Conclude with `left_eq_add.1 h1`. Express the relevant statement in the definitionally equal form `φ (Submodule.Quotient.mk _) = _`. Rewrite using `[hφ]`. Conclude with `congrArg _ hcs`.

Rewrite using `[Nat.card_eq_of_bijective _ hbij, hP, card_quot_range, ker_frobenius_sub_id_eq_invariants hrho hN hs]`.
-/
theorem card_H1ur (hrho : ContAction rho) (hN : ∀ σ ∈ N, ∀ m, rho σ m = m) {s : G}
    (hs : IsZHat (G ⧸ N) (QuotientGroup.mk s)) : Nat.card (H1ur rho N) = Nat.card (H0 rho) := by
  set P : Submodule R M := LinearMap.range (rho s - LinearMap.id) with hP
  let f : Z1 rho →ₗ[R] M ⧸ P := P.mkQ ∘ₗ ((LinearMap.proj s) ∘ₗ (Z1 rho).subtype)
  have hker : (Bd1 rho).comap (Z1 rho).subtype ≤ LinearMap.ker f := by
    intro c hc'
    obtain ⟨m, hm⟩ := (mem_contCoboundaries1 _ _).1 hc'
    rw [LinearMap.mem_ker]
    change (Submodule.Quotient.mk (c.1 s) : M ⧸ P) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨m, by simpa using (hm s).symm⟩
  let φ : H1 rho →ₗ[R] M ⧸ P := ((Bd1 rho).comap (Z1 rho).subtype).liftQ f hker
  have hφ : ∀ c : Z1 rho, φ (Submodule.Quotient.mk c) = Submodule.Quotient.mk (c.1 s) := fun c => rfl
  have hinj0 : ∀ z ∈ H1ur rho N, φ z = 0 → z = 0 := by
    intro z hz hz0
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    obtain ⟨c', hc', hcc⟩ := exists_desc1 hN c.1 c.2 (apply_eq_zero_of_mem_H1ur hN c hz)
    rw [hφ, Submodule.Quotient.mk_eq_zero] at hz0
    obtain ⟨m, hm⟩ := hz0
    have h1 : c' (QuotientGroup.mk s) = rho s m - m := by rw [hcc, ← hm]; rfl
    have h2 := ProcyclicCohomology.cocycle_eq_of_apply (qT N rho hrho hN) hs.1 c' hc' m h1
    rw [Submodule.Quotient.mk_eq_zero]
    refine (mem_contCoboundaries1 _ _).2 ⟨m, fun g => ?_⟩
    change c.1 g = _
    rw [← hcc]
    exact h2 (QuotientGroup.mk g)
  have hbij : Bijective (fun x : H1ur rho N => φ x.1) := by
    constructor
    · intro x y hxy
      have h1 : φ (x.1 - y.1) = 0 := by rw [map_sub]; exact sub_eq_zero.2 hxy
      exact Subtype.ext (sub_eq_zero.1 (hinj0 _ ((H1ur rho N).sub_mem x.2 y.2) h1))
    · intro y
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨c', hc', hcs⟩ := ProcyclicCohomology.exists_cocycle (qT N rho hrho hN) (ProcyclicCohomology.comm_of_dense hs.1) hs.1 hs.2 m
        (torsion_of_finite (M := M) m)
      have hZ := inflation_mem_one_cocycles hN c' hc'
      refine ⟨⟨Submodule.Quotient.mk ⟨_, hZ⟩, ?_⟩, ?_⟩
      · change (Submodule.Quotient.mk (restrictCocycles1 rho N.subtype continuous_subtype_val ⟨_, hZ⟩) :
          H1 (rho.comp N.subtype)) = 0
        rw [Submodule.Quotient.mk_eq_zero]
        refine (mem_contCoboundaries1 _ _).2 ⟨0, fun σ => ?_⟩
        change c' (QuotientGroup.mk σ.1) = _
        rw [(QuotientGroup.eq_one_iff σ.1).2 σ.2, map_zero, sub_zero]
        have h1 : c' (1 * 1) = c' 1 + qRho N rho hN 1 (c' 1) := hc'.2 1 1
        rw [mul_one, map_one, Module.End.one_apply] at h1
        exact left_eq_add.1 h1
      · change φ (Submodule.Quotient.mk _) = _
        rw [hφ]
        exact congrArg _ hcs
  rw [Nat.card_eq_of_bijective _ hbij, hP, card_quot_range, ker_frobenius_sub_id_eq_invariants hrho hN hs]

end

end ReciprocityTheory.DiscreteGroups.LocalClassField.InflationOneCocycles
