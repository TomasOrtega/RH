import Mathlib

open Matrix

namespace UpperTheory.V

private def transl (R : Type) [CommRing R] {G : Type} [Group G] (g : G) : (G → R) →ₗ[R] (G → R) where
  toFun x := fun h => x (g⁻¹ * h)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end UpperTheory.V

/- English proof (translation)
Establish `hπ : ∀ (a b : G) (y : N), π a (π b y) = π (a * b) y` using `fun a b y => by`. Rewrite using `[map_mul]`. Both sides reduce to the same expression. Combine the equalities or inequalities in the displayed calculation. Repeatedly rewrite using `[map_sum, map_smul, hπ, Finset.smul_sum, smul_smul]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun h _ => ?_)` and prove the remaining obligations. Rewrite using `[← Finset.sum_smul, hR]`. Use `_ = _ := Equiv.sum_comp (Equiv.mulLeft g) (fun h => u i h • π h v)`.
-/
private theorem UpperTheory.sum_B_smul_pi_sum_smul_eq_sum_smul {G N : Type} [Group G] [Fintype G] [AddCommGroup N] [Module ℂ N]
    (π : Representation ℂ G N) {m : ℕ} (u : Fin m → G → ℂ) (B : G → Matrix (Fin m) (Fin m) ℂ)
    (hR : ∀ g i h, u i (g * h) = ∑ j, B g j i * u j h) (v : N) (g : G) (i : Fin m) :
    ∑ j, B g j i • π g (∑ h, u j h • π h v) = ∑ h, u i h • π h v := by
  have hπ : ∀ (a b : G) (y : N), π a (π b y) = π (a * b) y := fun a b y => by
    rw [map_mul]
    rfl
  calc _ = ∑ h, u i (g * h) • π (g * h) v := by
        simp_rw [map_sum, map_smul, hπ, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun h _ => ?_)
        rw [← Finset.sum_smul, hR]
    _ = _ := Equiv.sum_comp (Equiv.mulLeft g) (fun h => u i h • π h v)

/- English proof (translation)
Establish `hπ : ∀ (a b : G) (y : N), π a (π b y) = π (a * b) y` using `fun a b y => by`. Rewrite using `[map_mul]`. Both sides reduce to the same expression. Establish `hinner : ∀ g k, ∑ h, u i h * c k (g⁻¹ * h) = B g k i`. Introduce `g k`.

Rewrite using `[← Equiv.sum_comp (Equiv.mulLeft g)]`. Simplify using `only [Equiv.coe_mulLeft, inv_mul_cancel_left]`. Repeatedly rewrite using `[hR, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Repeatedly rewrite using `[mul_assoc, ← Finset.mul_sum]`.

Establish `hc' : ∀ j, ∑ h, u j h * c k h = if k = j then 1 else 0` using `fun j => by`. Rewrite using `[← hc k j]`. Conclude with `Finset.sum_congr rfl (fun h _ => mul_comm _ _)`. Simplify using `[hc']`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_congr rfl (fun h _ => ?_)` and prove the remaining obligations. Rewrite using `[← Equiv.sum_comp (Equiv.mulLeft h⁻¹)]`. Simplify using `only [Equiv.coe_mulLeft, map_sum, map_smul, hπ, Finset.smul_sum, smul_smul, _root_.mul_inv_rev, inv_inv, mul_inv_cancel_left]`. Use `_ = ∑ g, ∑ k, (∑ h, u i h * c k (g⁻¹ * h)) • π g (F k) := by`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl (fun g _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Repeatedly rewrite using `[Finset.sum_smul]`. Use `_ = (Fintype.card G : ℂ) • F i := by`. Repeatedly rewrite using `[hinner, hF]`.

Rewrite using `[Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]`.
-/
private theorem UpperTheory.sum_smul_pi_average_eq_card_smul_of_dual {G N : Type} [Group G] [Fintype G] [AddCommGroup N] [Module ℂ N]
    (π : Representation ℂ G N) {m : ℕ} (u : Fin m → G → ℂ) (B : G → Matrix (Fin m) (Fin m) ℂ)
    (hR : ∀ g i h, u i (g * h) = ∑ j, B g j i * u j h) (c : Fin m → G → ℂ)
    (hc : ∀ k j, ∑ h, c k h * u j h = if k = j then 1 else 0) (F : Fin m → N)
    (hF : ∀ g i, ∑ j, B g j i • π g (F j) = F i) (i : Fin m) :
    ∑ h, u i h • π h (∑ g, ∑ k, c k g⁻¹ • π g (F k)) = (Fintype.card G : ℂ) • F i := by
  have hπ : ∀ (a b : G) (y : N), π a (π b y) = π (a * b) y := fun a b y => by
    rw [map_mul]
    rfl
  have hinner : ∀ g k, ∑ h, u i h * c k (g⁻¹ * h) = B g k i := by
    intro g k
    rw [← Equiv.sum_comp (Equiv.mulLeft g)]
    simp only [Equiv.coe_mulLeft, inv_mul_cancel_left]
    simp_rw [hR, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    have hc' : ∀ j, ∑ h, u j h * c k h = if k = j then 1 else 0 := fun j => by
      rw [← hc k j]
      exact Finset.sum_congr rfl (fun h _ => mul_comm _ _)
    simp [hc']
  calc ∑ h, u i h • π h (∑ g, ∑ k, c k g⁻¹ • π g (F k))
      = ∑ h, ∑ g, ∑ k, (u i h * c k (g⁻¹ * h)) • π g (F k) := by
        refine Finset.sum_congr rfl (fun h _ => ?_)
        rw [← Equiv.sum_comp (Equiv.mulLeft h⁻¹)]
        simp only [Equiv.coe_mulLeft, map_sum, map_smul, hπ, Finset.smul_sum, smul_smul,
          _root_.mul_inv_rev, inv_inv, mul_inv_cancel_left]
    _ = ∑ g, ∑ k, (∑ h, u i h * c k (g⁻¹ * h)) • π g (F k) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun g _ => ?_)
        rw [Finset.sum_comm]
        simp_rw [Finset.sum_smul]
    _ = (Fintype.card G : ℂ) • F i := by
        simp_rw [hinner, hF]
        rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]

/- English proof (translation)
Use `letI : Algebra (FractionRing O) ℂ := FractionRing.liftAlgebra O ℂ`. Use `haveI : IsScalarTower O (FractionRing O) ℂ := FractionRing.isScalarTower_liftAlgebra O ℂ`. Set `w : Fin m → G → FractionRing O` to `fun j h => algebraMap O (FractionRing O) (u j h)`. Establish `hw : LinearIndependent (FractionRing O) w`. Rewrite using `[← LinearIndependent.iff_fractionRing O (FractionRing O)]`.

Establish `hinj : Function.Injective (LinearMap.compLeft (Algebra.linearMap O (FractionRing O)) G)`. Introduce `x y hxy`. Use function extensionality and compare the values at `h`. Conclude with `IsFractionRing.injective O (FractionRing O) (congrFun hxy h)`. Conclude with `hu.map' _ (LinearMap.ker_eq_bot.2 hinj)`.

Set `f : (Fin m → FractionRing O) →ₗ[FractionRing O] (G → FractionRing O)` to `{ toFun := fun x => ∑ j, x j • w j map_add' := by intros; simp [add_smul, Finset.sum_add_distrib] map_smul' := by intros; simp [Finset.smul_sum, smul_smul] }`. Establish `hf : LinearMap.ker f = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `x hx`. Use function extensionality and compare the values at `j`.

Conclude with `Fintype.linearIndependent_iff.1 hw x hx j`. Take `⟨P, hP⟩` from `LinearMap.exists_leftInverse_of_injective f hf`. Establish `hPw : ∀ j, P (w j) = fun k => if j = k then 1 else 0`. Introduce `j`. Establish `h1 : f (fun k => if j = k then 1 else 0) = w j`.

Simplify using `[f, ite_smul, Finset.sum_ite_eq]`. Rewrite using `[← h1, ← LinearMap.comp_apply, hP, LinearMap.id_apply]`. Use `⟨fun k h => algebraMap (FractionRing O) ℂ (P (fun h' => if h = h' then 1 else 0) k), ?_⟩` and prove the remaining obligations. Introduce `k j`. Establish `hsum : ∑ h, w j h • (fun h' => if h = h' then (1 : FractionRing O) else 0) = w j` using `(pi_eq_sum_univ (w j)).symm`.

Establish `h2 : ∑ h, P (fun h' => if h = h' then 1 else 0) k * w j h = if k = j then 1 else 0`. Use `congrFun (congrArg P hsum) k` as an intermediate fact. Rewrite `this` using `[map_sum, hPw]`. Simplify using `only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this`. Rewrite `this` using `[eq_comm]`.

Simplify using `only [mul_comm]`. Rewrite using `[← this]`. Simplify using `[eq_comm]`. Simplify using `only [IsScalarTower.algebraMap_apply O (FractionRing O) ℂ, ← map_mul, ← map_sum]`. Rewrite using `[show (∑ h, P (fun h' => if h = h' then 1 else 0) k * algebraMap O (FractionRing O) (u j h)) = if k = j then 1 else 0 from h2]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem UpperTheory.exists_dual_family_of_linearIndependent' (O : Type) [CommRing O] [IsDomain O] [Algebra O ℂ] [FaithfulSMul O ℂ]
    {G : Type} [Fintype G] {m : ℕ} (u : Fin m → G → O) (hu : LinearIndependent O u) :
    ∃ c : Fin m → G → ℂ, ∀ k j, ∑ h, c k h * algebraMap O ℂ (u j h) = if k = j then 1 else 0 := by
  classical
  letI : Algebra (FractionRing O) ℂ := FractionRing.liftAlgebra O ℂ
  haveI : IsScalarTower O (FractionRing O) ℂ := FractionRing.isScalarTower_liftAlgebra O ℂ
  let w : Fin m → G → FractionRing O := fun j h => algebraMap O (FractionRing O) (u j h)
  have hw : LinearIndependent (FractionRing O) w := by
    rw [← LinearIndependent.iff_fractionRing O (FractionRing O)]
    have hinj : Function.Injective
        (LinearMap.compLeft (Algebra.linearMap O (FractionRing O)) G) := by
      intro x y hxy
      funext h
      exact IsFractionRing.injective O (FractionRing O) (congrFun hxy h)
    exact hu.map' _ (LinearMap.ker_eq_bot.2 hinj)
  let f : (Fin m → FractionRing O) →ₗ[FractionRing O] (G → FractionRing O) :=
    { toFun := fun x => ∑ j, x j • w j
      map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intros; simp [Finset.smul_sum, smul_smul] }
  have hf : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    funext j
    exact Fintype.linearIndependent_iff.1 hw x hx j
  obtain ⟨P, hP⟩ := LinearMap.exists_leftInverse_of_injective f hf
  have hPw : ∀ j, P (w j) = fun k => if j = k then 1 else 0 := by
    intro j
    have h1 : f (fun k => if j = k then 1 else 0) = w j := by
      simp [f, ite_smul, Finset.sum_ite_eq]
    rw [← h1, ← LinearMap.comp_apply, hP, LinearMap.id_apply]
  refine ⟨fun k h => algebraMap (FractionRing O) ℂ (P (fun h' => if h = h' then 1 else 0) k), ?_⟩
  intro k j
  have hsum : ∑ h, w j h • (fun h' => if h = h' then (1 : FractionRing O) else 0) = w j :=
    (pi_eq_sum_univ (w j)).symm
  have h2 : ∑ h, P (fun h' => if h = h' then 1 else 0) k * w j h = if k = j then 1 else 0 := by
    have := congrFun (congrArg P hsum) k
    rw [map_sum, hPw] at this
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [eq_comm] at this
    simp only [mul_comm]
    rw [← this]
    simp [eq_comm]
  simp only [IsScalarTower.algebraMap_apply O (FractionRing O) ℂ, ← map_mul, ← map_sum]
  rw [show (∑ h, P (fun h' => if h = h' then 1 else 0) k * algebraMap O (FractionRing O) (u j h))
    = if k = j then 1 else 0 from h2]
  split_ifs <;> simp

/- English proof (translation)
Introduce `O _ _ _ _ _ G _ _ I hI hspan`. Set `ι : (G → O) →ₗ[O] (G → ℂ)` to `LinearMap.compLeft (Algebra.linearMap O ℂ) G`. Set `Λ : Submodule O (G → O)` to `(I.restrictScalars O).comap ι`. Take `⟨m, b⟩` from `Submodule.basisOfPid (Pi.basisFun O G) Λ`. Set `T : G → (G → O) →ₗ[O] (G → O)` to `fun g => LinearMap.funLeft O O (fun h => g⁻¹ * h)`.

Establish `hT : ∀ g, ∀ y ∈ Λ, T g y ∈ Λ`. Introduce `g y hy`. Conclude with `hI g _ hy`. Set `A : G → Matrix (Fin m) (Fin m) O` to `fun g => LinearMap.toMatrix b b ((T g).restrict (hT g))`. Establish `hA1 : A 1 = 1`.

Establish `e : (T 1).restrict (hT 1) = LinearMap.id`. Use `LinearMap.ext fun y => Subtype.ext (funext fun h => ?_)` and prove the remaining obligations. Simplify using `[T, LinearMap.funLeft_apply, LinearMap.restrict_apply]`. Simplify using `only [A, e, LinearMap.toMatrix_id]`. Establish `hAmul : ∀ g g', A (g * g') = A g * A g'`.

Introduce `g g'`. Establish `e : (T (g * g')).restrict (hT _) = ((T g).restrict (hT g)).comp ((T g').restrict (hT g'))`. Use `LinearMap.ext fun y => Subtype.ext (funext fun h => ?_)` and prove the remaining obligations. Simplify using `[T, LinearMap.funLeft_apply, LinearMap.restrict_apply, _root_.mul_inv_rev, mul_assoc]`. Simplify using `only [A, e]`.

Conclude with `LinearMap.toMatrix_comp b b b _ _`. Set `τ0 : G →* Matrix (Fin m) (Fin m) O` to `{ toFun := fun g => (A g⁻¹)ᵀ map_one' := by simp [hA1] map_mul' := by`. Introduce `g g'`. Simplify using `only [_root_.mul_inv_rev, hAmul, Matrix.transpose_mul] }`. Establish `hRO : ∀ g i h, (b i : G → O) (g * h) = ∑ j, A g⁻¹ j i * (b j : G → O) h`.

Introduce `g i h`. Establish `e` using `b.sum_repr ((T g⁻¹).restrict (hT g⁻¹) (b i))`. Establish `e2` using `congrArg (fun z : Λ => (z : G → O) h) e`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at e2`. Establish `e3 : (((T g⁻¹).restrict (hT g⁻¹) (b i) : Λ) : G → O) h = (b i : G → O) (g * h)`.

Simplify using `[T, LinearMap.funLeft_apply, LinearMap.restrict_apply]`. Rewrite using `[← e3, ← e2]`. Simplify using `only [A, LinearMap.toMatrix_apply]`. Set `u' : Fin m → G → ℂ` to `fun j h => algebraMap O ℂ ((b j : G → O) h)`. Set `B : G → Matrix (Fin m) (Fin m) ℂ` to `fun g j i => algebraMap O ℂ (A g⁻¹ j i)`.

Establish `hR : ∀ g i h, u' i (g * h) = ∑ j, B g j i * u' j h`. Introduce `g i h`. Simplify using `only [u', B, hRO, map_sum, map_mul]`. Establish `hsp : I ≤ Submodule.span ℂ (Set.range u')`. Use `hspan.trans (Submodule.span_le.2 ?_)` and prove the remaining obligations.

Introduce and unpack `x ⟨hxI, hxO⟩`. Simplify using `only [RingHom.mem_range] at hxO`. Use `choose y hy using hxO`. Establish `hyΛ : y ∈ Λ` using `by show ι y ∈ I`. Use `hxI using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `g`. Conclude with `hy g`. Establish `e` using `b.sum_repr ⟨y, hyΛ⟩`. Establish `hx : x = ∑ j, algebraMap O ℂ (b.repr ⟨y, hyΛ⟩ j) • u' j`. Use function extensionality and compare the values at `g`.

Establish `e2` using `congrArg (fun z : Λ => (z : G → O) g) e`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at e2`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, u']`. Rewrite using `[← hy g, ← e2, map_sum]`. Simplify using `[map_mul]`.

Rewrite using `[hx]`. Conclude with `Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))`. Establish `hli : LinearIndependent O (fun j => (b j : G → O))` using `b.linearIndependent.map' Λ.subtype (Submodule.ker_subtype _)`. Take `⟨c, hc⟩` from `UpperTheory.exists_dual_family_of_linearIndependent' O (fun j => (b j : G → O)) hli`. Use `⟨m, τ0.toHomUnits, ?_⟩` and prove the remaining obligations.

Introduce `N _ _ π`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨F, hF0, hF⟩`. Take `⟨k, hk⟩` from `Function.ne_iff.1 hF0`. Use `⟨u' k, (b k).2, ∑ g, ∑ k, c k g⁻¹ • π g (F k), ?_⟩` and prove the remaining obligations.

Rewrite using `[UpperTheory.sum_smul_pi_average_eq_card_smul_of_dual π u' B hR c hc F (fun g i => hF g i) k]`. Conclude with `smul_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero) hk`. Introduce and unpack `⟨x, hx, v, hv⟩`. Use `⟨fun j => ∑ h, u' j h • π h v, ?_, fun g i => UpperTheory.sum_B_smul_pi_sum_smul_eq_sum_smul π u' B hR v g i⟩` and prove the remaining obligations. Introduce `hF0`.

Apply `hv` to reduce the goal to its premises. Set `Φ : (G → ℂ) →ₗ[ℂ] N` to `{ toFun := fun y => ∑ g, y g • π g v map_add' := by intros; simp [add_smul, Finset.sum_add_distrib] map_smul' := by intros; simp [Finset.smul_sum, smul_smul] }`. Establish `hker : Submodule.span ℂ (Set.range u') ≤ LinearMap.ker Φ`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`.

Use `show Φ (u' j) = 0`. Conclude with `congrFun hF0 j`. Conclude with `hker (hsp hx)`.
-/
theorem UpperTheory.exists_integral_rep_detecting_invariant_subspace :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O ℂ] [FaithfulSMul O ℂ] (G : Type) [Group G] [Fintype G] (I : Submodule ℂ (G → ℂ)), (∀ g, ∀ x ∈ I, (fun h => x (g⁻¹ * h)) ∈ I) → I ≤ Submodule.span ℂ {x | x ∈ I ∧ ∀ g, x g ∈ (algebraMap O ℂ).range} → ∃ (m : ℕ) (τ : G →* GL (Fin m) O), ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (π : Representation ℂ G N), (∃ F : Fin m → N, F ≠ 0 ∧ ∀ g i, ∑ j, algebraMap O ℂ (τ g i j) • π g (F j) = F i) ↔ ∃ x ∈ I, ∃ v, ∑ g, x g • π g v ≠ 0 := by
  intro O _ _ _ _ _ G _ _ I hI hspan
  classical
  let ι : (G → O) →ₗ[O] (G → ℂ) := LinearMap.compLeft (Algebra.linearMap O ℂ) G
  let Λ : Submodule O (G → O) := (I.restrictScalars O).comap ι
  obtain ⟨m, b⟩ := Submodule.basisOfPid (Pi.basisFun O G) Λ
  let T : G → (G → O) →ₗ[O] (G → O) := fun g => LinearMap.funLeft O O (fun h => g⁻¹ * h)
  have hT : ∀ g, ∀ y ∈ Λ, T g y ∈ Λ := by
    intro g y hy
    exact hI g _ hy
  let A : G → Matrix (Fin m) (Fin m) O := fun g => LinearMap.toMatrix b b ((T g).restrict (hT g))
  have hA1 : A 1 = 1 := by
    have e : (T 1).restrict (hT 1) = LinearMap.id := by
      refine LinearMap.ext fun y => Subtype.ext (funext fun h => ?_)
      simp [T, LinearMap.funLeft_apply, LinearMap.restrict_apply]
    simp only [A, e, LinearMap.toMatrix_id]
  have hAmul : ∀ g g', A (g * g') = A g * A g' := by
    intro g g'
    have e : (T (g * g')).restrict (hT _) = ((T g).restrict (hT g)).comp ((T g').restrict (hT g')) := by
      refine LinearMap.ext fun y => Subtype.ext (funext fun h => ?_)
      simp [T, LinearMap.funLeft_apply, LinearMap.restrict_apply, _root_.mul_inv_rev, mul_assoc]
    simp only [A, e]
    exact LinearMap.toMatrix_comp b b b _ _
  let τ0 : G →* Matrix (Fin m) (Fin m) O :=
    { toFun := fun g => (A g⁻¹)ᵀ
      map_one' := by simp [hA1]
      map_mul' := by
        intro g g'
        simp only [_root_.mul_inv_rev, hAmul, Matrix.transpose_mul] }
  have hRO : ∀ g i h, (b i : G → O) (g * h) = ∑ j, A g⁻¹ j i * (b j : G → O) h := by
    intro g i h
    have e := b.sum_repr ((T g⁻¹).restrict (hT g⁻¹) (b i))
    have e2 := congrArg (fun z : Λ => (z : G → O) h) e
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at e2
    have e3 : (((T g⁻¹).restrict (hT g⁻¹) (b i) : Λ) : G → O) h = (b i : G → O) (g * h) := by
      simp [T, LinearMap.funLeft_apply, LinearMap.restrict_apply]
    rw [← e3, ← e2]
    simp only [A, LinearMap.toMatrix_apply]
  let u' : Fin m → G → ℂ := fun j h => algebraMap O ℂ ((b j : G → O) h)
  let B : G → Matrix (Fin m) (Fin m) ℂ := fun g j i => algebraMap O ℂ (A g⁻¹ j i)
  have hR : ∀ g i h, u' i (g * h) = ∑ j, B g j i * u' j h := by
    intro g i h
    simp only [u', B, hRO, map_sum, map_mul]
  have hsp : I ≤ Submodule.span ℂ (Set.range u') := by
    refine hspan.trans (Submodule.span_le.2 ?_)
    rintro x ⟨hxI, hxO⟩
    simp only [RingHom.mem_range] at hxO
    choose y hy using hxO
    have hyΛ : y ∈ Λ := by
      show ι y ∈ I
      convert hxI using 1
      funext g
      exact hy g
    have e := b.sum_repr ⟨y, hyΛ⟩
    have hx : x = ∑ j, algebraMap O ℂ (b.repr ⟨y, hyΛ⟩ j) • u' j := by
      funext g
      have e2 := congrArg (fun z : Λ => (z : G → O) g) e
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] at e2
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, u']
      rw [← hy g, ← e2, map_sum]
      simp [map_mul]
    rw [hx]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  have hli : LinearIndependent O (fun j => (b j : G → O)) :=
    b.linearIndependent.map' Λ.subtype (Submodule.ker_subtype _)
  obtain ⟨c, hc⟩ := UpperTheory.exists_dual_family_of_linearIndependent' O (fun j => (b j : G → O)) hli
  refine ⟨m, τ0.toHomUnits, ?_⟩
  intro N _ _ π
  constructor
  · rintro ⟨F, hF0, hF⟩
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hF0
    refine ⟨u' k, (b k).2, ∑ g, ∑ k, c k g⁻¹ • π g (F k), ?_⟩
    rw [UpperTheory.sum_smul_pi_average_eq_card_smul_of_dual π u' B hR c hc F (fun g i => hF g i) k]
    exact smul_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero) hk
  · rintro ⟨x, hx, v, hv⟩
    refine ⟨fun j => ∑ h, u' j h • π h v, ?_, fun g i => UpperTheory.sum_B_smul_pi_sum_smul_eq_sum_smul π u' B hR v g i⟩
    intro hF0
    apply hv
    let Φ : (G → ℂ) →ₗ[ℂ] N :=
      { toFun := fun y => ∑ g, y g • π g v
        map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
        map_smul' := by intros; simp [Finset.smul_sum, smul_smul] }
    have hker : Submodule.span ℂ (Set.range u') ≤ LinearMap.ker Φ := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      show Φ (u' j) = 0
      exact congrFun hF0 j
    exact hker (hsp hx)
