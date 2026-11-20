import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsMulEqUnifPow
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulSpanIff

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Rewrite using `[Subgroup.relIndex, AddSubgroup.relIndex, Subgroup.index, AddSubgroup.index]`. Establish `hrel : ∀ a b : G', (a⁻¹ * b ∈ H.subgroupOf G') ↔ (-(⟨φ a, h1 a a.2⟩ : P) + ⟨φ b, h1 b b.2⟩ ∈ N.addSubgroupOf P)`. Introduce `a b`. Rewrite using `[Subgroup.mem_subgroupOf, AddSubgroup.mem_addSubgroupOf]`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv, AddSubgroup.coe_add, AddSubgroup.coe_neg, neg_add_eq_sub]`.

Conclude with `h3 a a.2 b b.2`. Set `f : G' ⧸ H.subgroupOf G' → P ⧸ N.addSubgroupOf P` to `Quotient.map' (fun x : G' => (⟨φ x, h1 x x.2⟩ : P)) (fun a b hab => by`. Rewrite `hab` using `[QuotientGroup.leftRel_apply]`. Rewrite using `[QuotientAddGroup.leftRel_apply]`. Conclude with `(hrel a b).1 hab)`.

Use `Nat.card_congr (Equiv.ofBijective f ⟨fun a b hab => ?_, fun p => ?_⟩)` and prove the remaining obligations. Proceed by induction on `a using QuotientGroup.induction_on with`. Consider the case `H a`. Proceed by induction on `b using QuotientGroup.induction_on with`. Consider the case `H b`.

Establish `hab' : ((⟨φ a, h1 a a.2⟩ : P) : P ⧸ N.addSubgroupOf P) = ((⟨φ b, h1 b b.2⟩ : P) : _)` using `hab`. Rewrite `hab'` using `[QuotientAddGroup.eq]`. Conclude with `QuotientGroup.eq.2 ((hrel a b).2 hab')`. Proceed by induction on `p using QuotientAddGroup.induction_on with`. Consider the case `H p`.

Take `⟨x, hx, hφ⟩` from `h2 p p.2`. Use `⟨((⟨x, hx⟩ : G') : G' ⧸ H.subgroupOf G'), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((⟨φ x, h1 x hx⟩ : P) : P ⧸ N.addSubgroupOf P) = (p : _)`. Use `congr 1`. Conclude with `Subtype.ext hφ`.
-/
theorem relIndex_eq_of_map {G M : Type*} [Group G] [AddCommGroup M] (H G' : Subgroup G)
    (N P : AddSubgroup M) (φ : G → M) (h1 : ∀ x ∈ G', φ x ∈ P) (h2 : ∀ p ∈ P, ∃ x ∈ G', φ x = p)
    (h3 : ∀ x ∈ G', ∀ y ∈ G', x⁻¹ * y ∈ H ↔ φ y - φ x ∈ N) : H.relIndex G' = N.relIndex P := by
  classical
  rw [Subgroup.relIndex, AddSubgroup.relIndex, Subgroup.index, AddSubgroup.index]

  have hrel : ∀ a b : G', (a⁻¹ * b ∈ H.subgroupOf G') ↔
      (-(⟨φ a, h1 a a.2⟩ : P) + ⟨φ b, h1 b b.2⟩ ∈ N.addSubgroupOf P) := by
    intro a b
    rw [Subgroup.mem_subgroupOf, AddSubgroup.mem_addSubgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, AddSubgroup.coe_add, AddSubgroup.coe_neg, neg_add_eq_sub]
    exact h3 a a.2 b b.2
  let f : G' ⧸ H.subgroupOf G' → P ⧸ N.addSubgroupOf P :=
    Quotient.map' (fun x : G' => (⟨φ x, h1 x x.2⟩ : P)) (fun a b hab => by
      rw [QuotientGroup.leftRel_apply] at hab
      rw [QuotientAddGroup.leftRel_apply]
      exact (hrel a b).1 hab)
  refine Nat.card_congr (Equiv.ofBijective f ⟨fun a b hab => ?_, fun p => ?_⟩)
  · induction a using QuotientGroup.induction_on with
    | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
    have hab' : ((⟨φ a, h1 a a.2⟩ : P) : P ⧸ N.addSubgroupOf P) = ((⟨φ b, h1 b b.2⟩ : P) : _) := hab
    rw [QuotientAddGroup.eq] at hab'
    exact QuotientGroup.eq.2 ((hrel a b).2 hab')
  · induction p using QuotientAddGroup.induction_on with
    | H p =>
    obtain ⟨x, hx, hφ⟩ := h2 p p.2
    refine ⟨((⟨x, hx⟩ : G') : G' ⧸ H.subgroupOf G'), ?_⟩
    change ((⟨φ x, h1 x hx⟩ : P) : P ⧸ N.addSubgroupOf P) = (p : _)
    congr 1
    exact Subtype.ext hφ

/- English proof (translation)
Take `⟨r, hr⟩` from `exists_endL_le hB₀ hA₀ h𝔭`. Take `⟨k₁, hk₁⟩` from `nSub_le_glSub hA₀ hB₀ h𝔭`. Use `⟨r, fun c hc => ⟨max k₁ 1, fun k hk => ?_⟩⟩` and prove the remaining obligations. Establish `hk1 : 1 ≤ k` using `le_trans (le_max_right _ _) hk`. Establish `hle : endL (locF 𝔭 B₀) (extP K 𝔭 ^ (k + c) • locF 𝔭 B₀) ≤ endL (locF 𝔭 A₀) (extP K 𝔭 ^ k • locF 𝔭 A₀)`.

Introduce `D hD`. Use `hr k ?_` and prove the remaining obligations. Introduce `x hx`. Conclude with `smul_anti 𝔭 _ (by omega) (hD x hx)`. Establish `hlift : ∀ D ∈ endL (locF 𝔭 A₀) (extP K 𝔭 ^ k • locF 𝔭 A₀), ∃ X ∈ nSub (locF 𝔭 A₀) 𝔭 k, (X : V →ₗ[K] V) - LinearMap.id = D`.

Introduce `D hD`. Establish `hD1 : D ∈ endL (locF 𝔭 A₀) (extP K 𝔭 • locF 𝔭 A₀)`. Introduce `x hx`. Use `smul_anti 𝔭 (locF 𝔭 A₀) hk1 (hD x hx)` as an intermediate fact. Rewrite `this` using `[pow_one]`. Then use the resulting hypothesis.

Take `⟨X, hX, hXg⟩` from `exists_equiv_of_mem_endL hA₀ h𝔭 hD1`. Use `⟨X, mem_nSub.2 ⟨hXg, fun x hx => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hX, add_sub_cancel_left]`. Conclude with `hD x hx`. Use extensionality with `v`.

Simplify using `[hX]`. Establish `hnsub : nSub (locF 𝔭 B₀) 𝔭 (k + c) ≤ nSub (locF 𝔭 A₀) 𝔭 k`. Introduce `X hXm`. Take `⟨hXB, hX⟩` from `mem_nSub.1 hXm`. Establish `hD : (X : V →ₗ[K] V) - LinearMap.id ∈ endL (locF 𝔭 B₀) (extP K 𝔭 ^ (k + c) • locF 𝔭 B₀)`.

Introduce `x hx`. Simplify using `using hX x hx`. Take `⟨X', hX'm, hX'⟩` from `hlift _ (hle hD)`. Establish `hXX : X' = X`. Use extensionality with `v`.

Use `LinearMap.congr_fun hX' v` as an intermediate fact. Simplify using `using this`. Rewrite using `[← hXX]`. Conclude with `hX'm`. Use `⟨hnsub, hle, ?_⟩` and prove the remaining obligations.

Use `relIndex_eq_of_map _ _ _ _ (fun X => (X : V →ₗ[K] V) - LinearMap.id) (fun X hX => ?_) (fun D hD => ?_) (fun x hx y hy => ?_)` and prove the remaining obligations. Introduce `v hv`. Simplify using `using (mem_nSub.1 hX).2 v hv`. Take `⟨X, hXm, hX⟩` from `hlift D hD`. Conclude with `⟨X, hXm, hX⟩`.

Establish `hxB : x ∈ glSub (locF 𝔭 B₀)` using `hk₁ k (le_trans (le_max_left _ _) hk) hx`. Establish `hyB : y ∈ glSub (locF 𝔭 B₀)` using `hk₁ k (le_trans (le_max_left _ _) hk) hy`. Establish `hxyB : x⁻¹ * y ∈ glSub (locF 𝔭 B₀)` using `mul_mem (inv_mem hxB) hyB`. Establish `e1 : ∀ v : V, x (x⁻¹ v) = v` using `fun v => by`. Rewrite using `[← LinearEquiv.mul_apply, mul_inv_cancel]`.

Both sides reduce to the same expression. Rewrite using `[mem_nSub]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, h⟩ v hv`. Establish `h'` using `apply_mem_smul hxB _ (h v hv)`.

Establish `e2 : x ((x⁻¹ * y) v - v) = y v - x v`. Rewrite using `[map_sub, LinearEquiv.mul_apply, e1]`. Rewrite `h'` using `[e2]`. Simplify using `using h'`. Introduce `h`.

Use `⟨hxyB, fun v hv => ?_⟩` and prove the remaining obligations. Establish `h'` using `apply_mem_smul (inv_mem hxB) _ (h v hv)`. Establish `e2 : x⁻¹ ((((y : V →ₗ[K] V) - LinearMap.id) - ((x : V →ₗ[K] V) - LinearMap.id) : V →ₗ[K] V) v) = (x⁻¹ * y) v - v`. Simplify using `only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, sub_sub_sub_cancel_right, map_sub, LinearEquiv.mul_apply]`. Rewrite using `[← LinearEquiv.mul_apply x⁻¹ x, inv_mul_cancel]`.

Both sides reduce to the same expression. Rewrite `h'` using `[e2]`. Conclude with `h'`.
-/
theorem relIndex_nSub_eq {A₀ B₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hB₀ : Submodule.IsLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ c₀ : ℕ, ∀ c ≥ c₀, ∃ k₀ : ℕ, ∀ k ≥ k₀, nSub (locF 𝔭 B₀) 𝔭 (k + c) ≤ nSub (locF 𝔭 A₀) 𝔭 k ∧
      endL (locF 𝔭 B₀) (extP K 𝔭 ^ (k + c) • locF 𝔭 B₀) ≤ endL (locF 𝔭 A₀) (extP K 𝔭 ^ k • locF 𝔭 A₀) ∧
      (nSub (locF 𝔭 B₀) 𝔭 (k + c)).relIndex (nSub (locF 𝔭 A₀) 𝔭 k) =
        (endL (locF 𝔭 B₀) (extP K 𝔭 ^ (k + c) • locF 𝔭 B₀)).relIndex
          (endL (locF 𝔭 A₀) (extP K 𝔭 ^ k • locF 𝔭 A₀)) := by
  obtain ⟨r, hr⟩ := exists_endL_le hB₀ hA₀ h𝔭
  obtain ⟨k₁, hk₁⟩ := nSub_le_glSub hA₀ hB₀ h𝔭
  refine ⟨r, fun c hc => ⟨max k₁ 1, fun k hk => ?_⟩⟩
  have hk1 : 1 ≤ k := le_trans (le_max_right _ _) hk

  have hle : endL (locF 𝔭 B₀) (extP K 𝔭 ^ (k + c) • locF 𝔭 B₀) ≤
      endL (locF 𝔭 A₀) (extP K 𝔭 ^ k • locF 𝔭 A₀) := by
    intro D hD
    refine hr k ?_
    intro x hx
    exact smul_anti 𝔭 _ (by omega) (hD x hx)

  have hlift : ∀ D ∈ endL (locF 𝔭 A₀) (extP K 𝔭 ^ k • locF 𝔭 A₀),
      ∃ X ∈ nSub (locF 𝔭 A₀) 𝔭 k, (X : V →ₗ[K] V) - LinearMap.id = D := by
    intro D hD
    have hD1 : D ∈ endL (locF 𝔭 A₀) (extP K 𝔭 • locF 𝔭 A₀) := by
      intro x hx
      have := smul_anti 𝔭 (locF 𝔭 A₀) hk1 (hD x hx)
      rwa [pow_one] at this
    obtain ⟨X, hX, hXg⟩ := exists_equiv_of_mem_endL hA₀ h𝔭 hD1
    refine ⟨X, mem_nSub.2 ⟨hXg, fun x hx => ?_⟩, ?_⟩
    · rw [hX, add_sub_cancel_left]
      exact hD x hx
    · ext v
      simp [hX]
  have hnsub : nSub (locF 𝔭 B₀) 𝔭 (k + c) ≤ nSub (locF 𝔭 A₀) 𝔭 k := by
    intro X hXm
    obtain ⟨hXB, hX⟩ := mem_nSub.1 hXm
    have hD : (X : V →ₗ[K] V) - LinearMap.id ∈ endL (locF 𝔭 B₀) (extP K 𝔭 ^ (k + c) • locF 𝔭 B₀) := by
      intro x hx
      simpa using hX x hx
    obtain ⟨X', hX'm, hX'⟩ := hlift _ (hle hD)
    have hXX : X' = X := by
      ext v
      have := LinearMap.congr_fun hX' v
      simpa using this
    rw [← hXX]
    exact hX'm
  refine ⟨hnsub, hle, ?_⟩
  refine relIndex_eq_of_map _ _ _ _ (fun X => (X : V →ₗ[K] V) - LinearMap.id) (fun X hX => ?_)
    (fun D hD => ?_) (fun x hx y hy => ?_)
  · intro v hv
    simpa using (mem_nSub.1 hX).2 v hv
  · obtain ⟨X, hXm, hX⟩ := hlift D hD
    exact ⟨X, hXm, hX⟩
  · have hxB : x ∈ glSub (locF 𝔭 B₀) := hk₁ k (le_trans (le_max_left _ _) hk) hx
    have hyB : y ∈ glSub (locF 𝔭 B₀) := hk₁ k (le_trans (le_max_left _ _) hk) hy
    have hxyB : x⁻¹ * y ∈ glSub (locF 𝔭 B₀) := mul_mem (inv_mem hxB) hyB
    have e1 : ∀ v : V, x (x⁻¹ v) = v := fun v => by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]
      rfl
    rw [mem_nSub]
    constructor
    · rintro ⟨_, h⟩ v hv
      have h' := apply_mem_smul hxB _ (h v hv)
      have e2 : x ((x⁻¹ * y) v - v) = y v - x v := by
        rw [map_sub, LinearEquiv.mul_apply, e1]
      rw [e2] at h'
      simpa using h'
    · intro h
      refine ⟨hxyB, fun v hv => ?_⟩
      have h' := apply_mem_smul (inv_mem hxB) _ (h v hv)
      have e2 : x⁻¹ ((((y : V →ₗ[K] V) - LinearMap.id) - ((x : V →ₗ[K] V) - LinearMap.id) :
          V →ₗ[K] V) v) =
          (x⁻¹ * y) v - v := by
        simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, sub_sub_sub_cancel_right,
          map_sub, LinearEquiv.mul_apply]
        rw [← LinearEquiv.mul_apply x⁻¹ x, inv_mul_cancel]
        rfl
      rw [e2] at h'
      exact h'

/- English proof (translation)
Take `⟨a, b, e, c0, hc0, he, hA, hB, hbe⟩` from `exists_smith hA₀ hB₀ h𝔭`. Establish `hinj` using `IsFractionRing.injective (𝓞 K) K`. Use `set eK : Fin (finrank K V) → K := fun i => algebraMap (𝓞 K) K (e i) with heKdef`. Use `set c0K : K := algebraMap (𝓞 K) K c0 with hc0Kdef`. Establish `heK : ∀ i, eK i ≠ 0` using `fun i => (map_ne_zero_iff _ hinj).2 (he i)`.

Establish `hc0K : c0K ≠ 0` using `(map_ne_zero_iff _ hinj).2 hc0`. Establish `hbeK : ∀ i, c0K • b i = eK i • a i` using `fun i => by`. Simplify using `only [c0K, eK, algebraMap_smul]`. Conclude with `hbe i`. Establish `hab : ∀ l, a l = (c0K / eK l) • b l` using `fun l => by`.

Rewrite using `[div_eq_mul_inv, mul_comm, ← smul_smul, hbeK l, smul_smul, inv_mul_cancel₀ (heK l), one_smul]`. Establish `hba : ∀ j, b j = (eK j / c0K) • a j` using `fun j => by`. Rewrite using `[div_eq_mul_inv, mul_comm, ← smul_smul, ← hbeK j, smul_smul, inv_mul_cancel₀ hc0K, one_smul]`. Establish `key : ∀ (D : V →ₗ[K] V) i j, LinearMap.toMatrix b b D i j * eK i = eK j * LinearMap.toMatrix a a D i j`. Introduce `D i j`.

Establish `h2 : D (a j) = ∑ l, (LinearMap.toMatrix a a D l j * (c0K / eK l)) • b l` using `by conv_lhs => rw [← a.sum_repr (D (a j))]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.toMatrix_apply, ← smul_smul, ← hab l]`. Rewrite using `[LinearMap.toMatrix_apply b b, hba j, map_smul, h2, map_smul, Finsupp.smul_apply, map_sum, Finsupp.finset_sum_apply]`. Simplify using `only [map_smul, Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Clear denominators, using `[heK i, hc0K]` for the nonvanishing conditions. Set `φA : (V →ₗ[K] V) →+ Matrix (Fin (finrank K V)) (Fin (finrank K V)) K` to `(LinearMap.toMatrix a a).toLinearMap.toAddMonoidHom`. Establish `hφA : Function.Surjective φA` using `(LinearMap.toMatrix a a).surjective`. Establish `hEA : endL (locF 𝔭 A₀) (extP K 𝔭 ^ k • locF 𝔭 A₀) = (matL 𝔭 k (fun _ _ => (1 : K)) (fun _ _ => 1)).comap φA`. Use extensionality with `D`.

Rewrite using `[AddSubgroup.mem_comap, ← hA, mem_endL_iff a h𝔭]`. Prove the components needed by the constructor for the conclusion. Introduce `h i j`. Conclude with `⟨_, h i j, by simp [φA]⟩`. Introduce `h i j`.

Take `⟨w, hw, hw'⟩` from `h i j`. Simplify using `only [one_mul, φA] at hw'`. Rewrite using `[show LinearMap.toMatrix a a D i j = w from hw']`. Conclude with `hw`. Establish `hEB : endL (locF 𝔭 B₀) (extP K 𝔭 ^ (k + c) • locF 𝔭 B₀) = (matL 𝔭 (k + c) (fun _ j => eK j) (fun i _ => eK i)).comap φA`.

Use extensionality with `D`. Rewrite using `[AddSubgroup.mem_comap, ← hB, mem_endL_iff b h𝔭]`. Prove the components needed by the constructor for the conclusion. Introduce `h i j`. Use `⟨_, h i j, ?_⟩` and prove the remaining obligations.

Simplify using `only [φA, LinearEquiv.coe_toLinearMap, LinearMap.toAddMonoidHom_coe]`. Rewrite using `[← key, mul_comm]`. Introduce `h i j`. Take `⟨w, hw, hw'⟩` from `h i j`. Simplify using `only [φA, LinearEquiv.coe_toLinearMap, LinearMap.toAddMonoidHom_coe] at hw'`.

Rewrite `hw'` using `[← key, mul_comm]`. Rewrite using `[mul_left_cancel₀ (heK i) hw']`. Conclude with `hw`. Rewrite `hle`, the goal using `[hEA, hEB]`. Establish `hle' : matL 𝔭 (k + c) (fun _ j => eK j) (fun i _ => eK i) ≤ matL 𝔭 k (fun _ _ => (1 : K)) (fun _ _ => 1)`.

Introduce `M hM`. Take `⟨D, rfl⟩` from `hφA M`. Conclude with `hle hM`. Rewrite using `[AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hφA]`. Establish `hmat` using `relIndex_matL hK hF h𝔭 (fun _ j => eK j) (fun i _ => eK i) (fun _ j => ⟨algebraMap_mem_pK 𝔭 _, heK j⟩) (fun i _ => ⟨algebraMap_mem_pK 𝔭 _, heK i⟩) k c hle'`.

Rewrite `hmat` using `[Finset.prod_comm]`. Establish `hP : (∏ i : Fin (finrank K V), ∏ _j : Fin (finrank K V), nO 𝔭 (eK i)) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun _ _ => nO_ne_zero hK hF h𝔭 (algebraMap_mem_pK 𝔭 _) (heK i)`. Rewrite `hmat` using `[mul_comm _ (Ideal.absNorm 𝔭 ^ _)]`. Simplify `Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hP) hmat` using `[Fintype.card_fin]`.
-/
theorem relIndex_endL (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {A₀ B₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hB₀ : Submodule.IsLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k c : ℕ}
    (hle : endL (locF 𝔭 B₀) (extP K 𝔭 ^ (k + c) • locF 𝔭 B₀) ≤
      endL (locF 𝔭 A₀) (extP K 𝔭 ^ k • locF 𝔭 A₀)) :
    (endL (locF 𝔭 B₀) (extP K 𝔭 ^ (k + c) • locF 𝔭 B₀)).relIndex
        (endL (locF 𝔭 A₀) (extP K 𝔭 ^ k • locF 𝔭 A₀)) =
      Ideal.absNorm 𝔭 ^ (2 * finrank K V ^ 2 * c) := by
  classical
  obtain ⟨a, b, e, c0, hc0, he, hA, hB, hbe⟩ := exists_smith hA₀ hB₀ h𝔭
  have hinj := IsFractionRing.injective (𝓞 K) K
  set eK : Fin (finrank K V) → K := fun i => algebraMap (𝓞 K) K (e i) with heKdef
  set c0K : K := algebraMap (𝓞 K) K c0 with hc0Kdef
  have heK : ∀ i, eK i ≠ 0 := fun i => (map_ne_zero_iff _ hinj).2 (he i)
  have hc0K : c0K ≠ 0 := (map_ne_zero_iff _ hinj).2 hc0
  have hbeK : ∀ i, c0K • b i = eK i • a i := fun i => by
    simp only [c0K, eK, algebraMap_smul]
    exact hbe i
  have hab : ∀ l, a l = (c0K / eK l) • b l := fun l => by
    rw [div_eq_mul_inv, mul_comm, ← smul_smul, hbeK l, smul_smul, inv_mul_cancel₀ (heK l), one_smul]
  have hba : ∀ j, b j = (eK j / c0K) • a j := fun j => by
    rw [div_eq_mul_inv, mul_comm, ← smul_smul, ← hbeK j, smul_smul, inv_mul_cancel₀ hc0K, one_smul]

  have key : ∀ (D : V →ₗ[K] V) i j, LinearMap.toMatrix b b D i j * eK i =
      eK j * LinearMap.toMatrix a a D i j := by
    intro D i j
    have h2 : D (a j) = ∑ l, (LinearMap.toMatrix a a D l j * (c0K / eK l)) • b l := by
      conv_lhs => rw [← a.sum_repr (D (a j))]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [LinearMap.toMatrix_apply, ← smul_smul, ← hab l]
    rw [LinearMap.toMatrix_apply b b, hba j, map_smul, h2, map_smul, Finsupp.smul_apply, map_sum,
      Finsupp.finset_sum_apply]
    simp only [map_smul, Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    field_simp [heK i, hc0K]
  let φA : (V →ₗ[K] V) →+ Matrix (Fin (finrank K V)) (Fin (finrank K V)) K :=
    (LinearMap.toMatrix a a).toLinearMap.toAddMonoidHom
  have hφA : Function.Surjective φA := (LinearMap.toMatrix a a).surjective
  have hEA : endL (locF 𝔭 A₀) (extP K 𝔭 ^ k • locF 𝔭 A₀) =
      (matL 𝔭 k (fun _ _ => (1 : K)) (fun _ _ => 1)).comap φA := by
    ext D
    rw [AddSubgroup.mem_comap, ← hA, mem_endL_iff a h𝔭]
    constructor
    · intro h i j
      exact ⟨_, h i j, by simp [φA]⟩
    · intro h i j
      obtain ⟨w, hw, hw'⟩ := h i j
      simp only [one_mul, φA] at hw'
      rw [show LinearMap.toMatrix a a D i j = w from hw']
      exact hw
  have hEB : endL (locF 𝔭 B₀) (extP K 𝔭 ^ (k + c) • locF 𝔭 B₀) =
      (matL 𝔭 (k + c) (fun _ j => eK j) (fun i _ => eK i)).comap φA := by
    ext D
    rw [AddSubgroup.mem_comap, ← hB, mem_endL_iff b h𝔭]
    constructor
    · intro h i j
      refine ⟨_, h i j, ?_⟩
      simp only [φA, LinearEquiv.coe_toLinearMap, LinearMap.toAddMonoidHom_coe]
      rw [← key, mul_comm]
    · intro h i j
      obtain ⟨w, hw, hw'⟩ := h i j
      simp only [φA, LinearEquiv.coe_toLinearMap, LinearMap.toAddMonoidHom_coe] at hw'
      rw [← key, mul_comm] at hw'
      rw [mul_left_cancel₀ (heK i) hw']
      exact hw
  rw [hEA, hEB] at hle ⊢
  have hle' : matL 𝔭 (k + c) (fun _ j => eK j) (fun i _ => eK i) ≤
      matL 𝔭 k (fun _ _ => (1 : K)) (fun _ _ => 1) := by
    intro M hM
    obtain ⟨D, rfl⟩ := hφA M
    exact hle hM
  rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hφA]
  have hmat := relIndex_matL hK hF h𝔭 (fun _ j => eK j) (fun i _ => eK i)
    (fun _ j => ⟨algebraMap_mem_pK 𝔭 _, heK j⟩) (fun i _ => ⟨algebraMap_mem_pK 𝔭 _, heK i⟩) k c hle'
  rw [Finset.prod_comm] at hmat
  have hP : (∏ i : Fin (finrank K V), ∏ _j : Fin (finrank K V), nO 𝔭 (eK i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun _ _ =>
      nO_ne_zero hK hF h𝔭 (algebraMap_mem_pK 𝔭 _) (heK i)
  rw [mul_comm _ (Ideal.absNorm 𝔭 ^ _)] at hmat
  simpa [Fintype.card_fin] using Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hP) hmat

/- English proof (translation)
Take `⟨c₀, hc₀⟩` from `relIndex_nSub_eq hA₀ hB₀ h𝔭`. Use `⟨c₀, fun c hc => ?_⟩` and prove the remaining obligations. Take `⟨k₀, hk₀⟩` from `hc₀ c hc`. Use `⟨k₀, fun k hk => ?_⟩` and prove the remaining obligations. Take `⟨h1, h2, h3⟩` from `hk₀ k hk`.

Conclude with `⟨h1, h3.trans (relIndex_endL hK hF hA₀ hB₀ h𝔭 h2)⟩`.
-/
theorem relIndex_nSub (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {A₀ B₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hB₀ : Submodule.IsLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ c₀ : ℕ, ∀ c ≥ c₀, ∃ k₀ : ℕ, ∀ k ≥ k₀, nSub (locF 𝔭 B₀) 𝔭 (k + c) ≤ nSub (locF 𝔭 A₀) 𝔭 k ∧
      (nSub (locF 𝔭 B₀) 𝔭 (k + c)).relIndex (nSub (locF 𝔭 A₀) 𝔭 k) =
        Ideal.absNorm 𝔭 ^ (2 * finrank K V ^ 2 * c) := by
  obtain ⟨c₀, hc₀⟩ := relIndex_nSub_eq hA₀ hB₀ h𝔭
  refine ⟨c₀, fun c hc => ?_⟩
  obtain ⟨k₀, hk₀⟩ := hc₀ c hc
  refine ⟨k₀, fun k hk => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hk₀ k hk
  exact ⟨h1, h3.trans (relIndex_endL hK hF hA₀ hB₀ h𝔭 h2)⟩

end Formalism.HermitianLattices.Ext.L3.D2
