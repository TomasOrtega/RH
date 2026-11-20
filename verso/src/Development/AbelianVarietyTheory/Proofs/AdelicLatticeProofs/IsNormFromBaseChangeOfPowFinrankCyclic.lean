import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AlgebraMapNormTensorEqProdConjugatesStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TensorExistsOfGaloisFixedStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Hilbert90BaseChangeStatement
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm.LocStep

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => simp [Function.iterate_succ_apply', ih, map_prod]`.
-/
theorem iter_prod {A ι : Type} [CommMonoid A] (T : A →* A) (n : ℕ) (s : Finset ι) (f : ι → A) :
    T^[n] (∏ i ∈ s, f i) = ∏ i ∈ s, T^[n] (f i) := by
  induction n with
  | zero => simp
  | succ n ih => simp [Function.iterate_succ_apply', ih, map_prod]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[Nat.mul_succ, Finset.prod_range_add, ih, Finset.prod_range_succ, ← Function.iterate_mul, iter_prod]`. Use `congr 1`.

Conclude with `Finset.prod_congr rfl fun j _ => Function.iterate_add_apply _ _ _ _`.
-/
theorem prod_range_mul_iter {A : Type} [CommMonoid A] (T : A →* A) (d m : ℕ) (x : A) :
    ∏ i ∈ Finset.range (d * m), T^[i] x
      = ∏ k ∈ Finset.range m, (T^[d])^[k] (∏ j ∈ Finset.range d, T^[j] x) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Finset.prod_range_add, ih, Finset.prod_range_succ, ← Function.iterate_mul,
      iter_prod]
    congr 1
    exact Finset.prod_congr rfl fun j _ => Function.iterate_add_apply _ _ _ _

/- English proof (translation)
Establish `ho : orderOf σ = Nat.card G` using `orderOf_eq_card_of_forall_mem_zpowers h`. Use `symm`. Use `Finset.prod_bij (fun i _ => σ ^ i) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)` and prove the remaining obligations. Introduce `i hi j hj hij`. Rewrite `hi`, `hj` using `[← ho]`.

Conclude with `pow_injOn_Iio_orderOf (by simpa using hi) (by simpa using hj) hij`. Introduce `g _`. Use `(mem_zpowers_iff_mem_range_orderOf).1 (h g)` as an intermediate fact. Rewrite `this` using `[Finset.mem_image]`. Take `⟨i, hi, e⟩` from `this`.

Conclude with `⟨i, ho ▸ hi, e⟩`.
-/
theorem prod_cyc {G A : Type} [Group G] [Fintype G] [CommMonoid A] (σ : G)
    (h : ∀ g, g ∈ Subgroup.zpowers σ) (f : G → A) :
    ∏ g, f g = ∏ i ∈ Finset.range (Nat.card G), f (σ ^ i) := by
  classical
  have ho : orderOf σ = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers h
  symm
  refine Finset.prod_bij (fun i _ => σ ^ i) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · intro i hi j hj hij
    rw [← ho] at hi hj
    exact pow_injOn_Iio_orderOf (by simpa using hi) (by simpa using hj) hij
  · intro g _
    have := (mem_zpowers_iff_mem_range_orderOf).1 (h g)
    rw [Finset.mem_image] at this
    obtain ⟨i, hi, e⟩ := this
    exact ⟨i, ho ▸ hi, e⟩

/- English proof (translation)
Rewrite using `[← Finset.prod_range_succ, Finset.prod_range_succ']`. Both sides reduce to the same expression.
-/
theorem telescope {A : Type} [CommMonoid A] (T : A →* A) (d : ℕ) (z : A) :
    (∏ j ∈ Finset.range d, T^[j] (T z)) * z = (∏ j ∈ Finset.range d, T^[j] z) * T^[d] z := by
  rw [← Finset.prod_range_succ, Finset.prod_range_succ']
  rfl

/- English proof (translation)
Use `set P : A → A := fun u => ∏ j ∈ Finset.range d, T^[j] u with hP`. Establish `Pmul : ∀ u v, P (u * v) = P u * P v` using `fun u v => by`. Simplify using `only [hP, iterate_map_mul, Finset.prod_mul_distrib]`. Establish `Pone : P 1 = 1` using `by simp only [hP, iterate_map_one, Finset.prod_const_one]`. Establish `hbk : ∀ k, T^[k] b = b` using `fun k => Function.IsFixedPt.iterate hb k`.

Take `⟨z, hz⟩` from `h90 (P x * b) (by`. Rewrite `hx` using `[prod_range_mul_iter]`. Establish `: ∀ k, (T^[d])^[k] (P x * b) = (T^[d])^[k] (P x) * b` using `fun k => by`. Rewrite using `[← Function.iterate_mul, iterate_map_mul, hbk]`. Simplify using `only [this, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]`.

Rewrite using `[hx, ← mul_pow, hab, one_pow])`. Establish `hzz : P z * P (z⁻¹ : Aˣ) = 1` using `by rw [← Pmul, Units.mul_inv, Pone]`. Establish `ht : ∀ u, P (T u) * u = P u * T^[d] u` using `fun u => telescope T d u`. Establish `h1 : P (x * T z * (z⁻¹ : Aˣ)) = a`. Rewrite using `[← Units.mul_left_inj z, Pmul, Pmul]`.

Combine the equalities or inequalities in the displayed calculation. Use `⟨_, ?_, h1⟩` and prove the remaining obligations. Generalize the expression as in `x * T z * (z⁻¹ : Aˣ) = w at h1`. Establish `h2 : P (T w) = a`. Rewrite using `[← ha, ← h1]`.

Simplify using `only [hP, map_prod]`. Conclude with `Finset.prod_congr rfl fun j _ => Function.iterate_succ_apply' _ _ _`. Establish `h3` using `ht w`. Rewrite `h3` using `[h1, h2]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem core {A : Type} [CommMonoid A] (T : A →* A) (d m : ℕ) (x a b : A) (hab : a * b = 1)
    (hb : T b = b) (ha : T a = a) (hx : ∏ i ∈ Finset.range (d * m), T^[i] x = a ^ m)
    (h90 : ∀ u : A, ∏ k ∈ Finset.range m, (T^[d])^[k] u = 1 → ∃ z : Aˣ, u * T^[d] z = z) :
    ∃ x' : A, T^[d] x' = x' ∧ ∏ j ∈ Finset.range d, T^[j] x' = a := by
  set P : A → A := fun u => ∏ j ∈ Finset.range d, T^[j] u with hP
  have Pmul : ∀ u v, P (u * v) = P u * P v := fun u v => by
    simp only [hP, iterate_map_mul, Finset.prod_mul_distrib]
  have Pone : P 1 = 1 := by simp only [hP, iterate_map_one, Finset.prod_const_one]
  have hbk : ∀ k, T^[k] b = b := fun k => Function.IsFixedPt.iterate hb k
  obtain ⟨z, hz⟩ := h90 (P x * b) (by
    rw [prod_range_mul_iter] at hx
    have : ∀ k, (T^[d])^[k] (P x * b) = (T^[d])^[k] (P x) * b := fun k => by
      rw [← Function.iterate_mul, iterate_map_mul, hbk]
    simp only [this, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    rw [hx, ← mul_pow, hab, one_pow])
  have hzz : P z * P (z⁻¹ : Aˣ) = 1 := by rw [← Pmul, Units.mul_inv, Pone]
  have ht : ∀ u, P (T u) * u = P u * T^[d] u := fun u => telescope T d u
  have h1 : P (x * T z * (z⁻¹ : Aˣ)) = a := by
    rw [← Units.mul_left_inj z, Pmul, Pmul]
    calc P x * P (T z) * P (z⁻¹ : Aˣ) * z = P x * (P (T z) * z) * P (z⁻¹ : Aˣ) := by ac_rfl
      _ = P x * T^[d] z * (P z * P (z⁻¹ : Aˣ)) * (a * b) := by rw [ht, hab, mul_one]; ac_rfl
      _ = a * (P x * b * T^[d] z) := by rw [hzz, mul_one]; ac_rfl
      _ = a * z := by rw [hz]
  refine ⟨_, ?_, h1⟩
  generalize x * T z * (z⁻¹ : Aˣ) = w at h1
  have h2 : P (T w) = a := by
    rw [← ha, ← h1]
    simp only [hP, map_prod]
    exact Finset.prod_congr rfl fun j _ => Function.iterate_succ_apply' _ _ _
  have h3 := ht w
  rw [h1, h2] at h3
  calc T^[d] w = b * (a * T^[d] w) := by rw [← mul_assoc, mul_comm b, hab, one_mul]
    _ = w := by rw [← h3, ← mul_assoc, mul_comm b, hab, one_mul]

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul k e => simp`.

Consider the case `add u v hu hv => rw [map_add, hu, hv]`. Both sides reduce to the same expression. Consider the case `succ i ih`. Rewrite using `[Function.iterate_succ_apply', ← ih]`. Use `clear ih`.

Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul k e => simp [pow_succ']`. Consider the case `add u v hu hv => simp only [map_add, hu, hv]`.
-/
theorem map_pow_iter {F E K : Type} [Field F] [Field E] [Algebra F E] [CommRing K] [Algebra F K]
    (σ : E ≃ₐ[F] E) (i : ℕ) (y : K ⊗[F] E) :
    Algebra.TensorProduct.map (AlgHom.id K K) ((σ ^ i : E ≃ₐ[F] E) : E →ₐ[F] E) y
      = (Algebra.TensorProduct.map (AlgHom.id K K) (σ : E →ₐ[F] E))^[i] y := by
  induction i with
  | zero =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul k e => simp
    | add u v hu hv => rw [map_add, hu, hv]; rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ← ih]
    clear ih
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul k e => simp [pow_succ']
    | add u v hu hv => simp only [map_add, hu, hv]

/- English proof (translation)
Take `⟨n, rfl⟩` from `(Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 (h g))`. Rewrite `hg` using `[← pow_mul, ← orderOf_dvd_iff_pow_eq_one, ho]`. Take `⟨k, rfl⟩` from `Nat.dvd_of_mul_dvd_mul_right (Nat.pos_of_ne_zero hm) hg`. Conclude with `⟨k, rfl⟩`.
-/
theorem exists_pow_of_pow_eq_one {G : Type} [Group G] [Finite G] (σ : G) (d m : ℕ) (hm : m ≠ 0)
    (h : ∀ g, g ∈ Subgroup.zpowers σ) (ho : orderOf σ = d * m) (g : G) (hg : g ^ m = 1) :
    ∃ k : ℕ, g = σ ^ (d * k) := by
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 (h g))
  rw [← pow_mul, ← orderOf_dvd_iff_pow_eq_one, ho] at hg
  obtain ⟨k, rfl⟩ := Nat.dvd_of_mul_dvd_mul_right (Nat.pos_of_ne_zero hm) hg
  exact ⟨k, rfl⟩

end GlobalTheory.CNorm.LocStep

namespace GlobalTheory.CNorm
open LocStep

/- English proof (translation)
Introduce `F M E K _ _ _ _ _ _ _ _ _ _ _ _ hc a ha ⟨x, hx⟩`. Use `haveI : IsAbelianGalois F E := IsAbelianGalois.of_isCyclic F E`. Use `haveI : IsGalois F M := (IsAbelianGalois.tower_bot F M E).toIsGalois`. Use `haveI : IsGalois M E := IsGalois.tower_top_of_isGalois F M E`. Use `haveI : FiniteDimensional M E := Module.Finite.of_restrictScalars_finite F M E`.

Use `haveI : FiniteDimensional F M := FiniteDimensional.left F M E`. Take `⟨σ, hσ⟩` from `IsCyclic.exists_generator (α := E ≃ₐ[F] E)`. Use `set d := Module.finrank F M with hd`. Use `set m := Module.finrank M E with hm`. Establish `hd0 : d ≠ 0` using `Module.finrank_pos.ne'`.

Establish `hm0 : m ≠ 0` using `Module.finrank_pos.ne'`. Establish `hcard : Nat.card (E ≃ₐ[F] E) = d * m`. Rewrite using `[IsGalois.card_aut_eq_finrank, Module.finrank_mul_finrank]`. Establish `ho : orderOf σ = d * m` using `(orderOf_eq_card_of_forall_mem_zpowers hσ).trans hcard`. Establish `hτ : orderOf (σ ^ d) = m`.

Rewrite using `[orderOf_pow_of_dvd hd0 (ho ▸ dvd_mul_right d m), ho, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]`. Use `set S := Algebra.TensorProduct.map (AlgHom.id K K) (σ : E →ₐ[F] E) with hS`. Set `T : K ⊗[F] E →* K ⊗[F] E` to `S`. Establish `hT : (T : K ⊗[F] E → K ⊗[F] E) = S` using `rfl`. Establish `hSd : (Algebra.TensorProduct.map (AlgHom.id K K) ((σ ^ d : E ≃ₐ[F] E) : E →ₐ[F] E) : K ⊗[F] E → K ⊗[F] E) = S^[d]` using `funext fun y => map_pow_iter σ d y`.

Establish `haK : algebraMap F K a ≠ 0` using `(_root_.map_ne_zero _).2 ha`. Take `⟨w, hw, hw'⟩` from `core T d m x (algebraMap K _ (algebraMap F K a)) (algebraMap K _ (algebraMap F K a)⁻¹) (by rw [← map_mul, mul_inv_cancel₀ haK, map_one]) (S.commutes _) (S.commutes _) (by`. Use `GlobalTheory.T.algebraMap_norm_tensor_eq_prod_galois_conjugates F E K x` as an intermediate fact. Rewrite `this` using `[hx, prod_cyc σ hσ, hcard, map_pow, map_pow]`. Rewrite using `[this]`.

Conclude with `Finset.prod_congr rfl fun i _ => (map_pow_iter σ i x).symm)`. Use the proof step `(by`. Introduce `u hu`. Use `GlobalTheory.T.hilbert90_baseChange' F E K (σ ^ d) m hτ u (by rw [hSd]; exact hu)` as an intermediate fact. Rewrite `this` using `[hSd]`.

Conclude with `this)`. Take `⟨z, rfl⟩` from `GlobalTheory.T.exists_tensor_eq_of_fixed_by_algEquiv F M E K w (by`. Introduce `h`. Take `⟨k, hk⟩` from `exists_pow_of_pow_eq_one σ d m hm0 hσ ho (h.restrictScalars F) (by`. Establish `h1 : h ^ m = 1`.

Rewrite using `[hm, ← IsGalois.card_aut_eq_finrank]`. Conclude with `pow_card_eq_one'`. Use `map_pow (AlgEquiv.restrictScalarsHom F (S := M) (A := E)) h m` as an intermediate fact. Rewrite `this` using `[h1, map_one]`. Conclude with `this.symm)`.

Rewrite using `[hk, map_pow_iter, Function.iterate_mul]`. Conclude with `Function.IsFixedPt.iterate hw k)`. Use `set ι := Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom F M E) with hι`. Establish `hinj : Function.Injective ι` using `Module.Flat.lTensor_preserves_injective_linearMap (M := K) (IsScalarTower.toAlgHom F M E).toLinearMap (algebraMap M E).injective`. Set `σ' : M ≃ₐ[F] M` to `AlgEquiv.restrictNormalHom M σ`.

Establish `hσ' : ∀ g, g ∈ Subgroup.zpowers σ'`. Introduce `g`. Take `⟨g', rfl⟩` from `AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := M) E g`. Take `⟨k, rfl⟩` from `hσ g'`. Conclude with `⟨k, (map_zpow _ _ _).symm⟩`.

Establish `hcomm : ∀ u : K ⊗[F] M, ι (Algebra.TensorProduct.map (AlgHom.id K K) (σ' : M →ₐ[F] M) u) = S (ι u)`. Introduce `u`. Proceed by induction on `u using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul k e`.

Establish `: algebraMap M E (σ' e) = σ (algebraMap M E e)` using `AlgEquiv.restrictNormal_commutes σ M e`. Simplify using `[hι, hS, this]`. Consider the case `add u v hu hv => simp only [map_add, hu, hv]`. Use `⟨z, ?_⟩` and prove the remaining obligations. Apply `(algebraMap K (K ⊗[F] M)).injective` to reduce the goal to its premises.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[GlobalTheory.T.algebraMap_norm_tensor_eq_prod_galois_conjugates F M K z, prod_cyc σ' hσ', IsGalois.card_aut_eq_finrank, ι.commutes, ← hw', map_prod]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow_iter]`. Conclude with `Function.Semiconj.iterate_right hcomm i z`.
-/
theorem tnorm_of_tnorm_pow : ∀ (F M E K : Type) [Field F] [CharZero F] [Field M] [Field E] [Algebra F M] [Algebra M E] [Algebra F E] [IsScalarTower F M E] [FiniteDimensional F E] [IsGalois F E] [Field K] [Algebra F K], IsCyclic (E ≃ₐ[F] E) → ∀ a : F, a ≠ 0 → TNorm F E K (a ^ Module.finrank M E) → TNorm F M K a := by
  intro F M E K _ _ _ _ _ _ _ _ _ _ _ _ hc a ha ⟨x, hx⟩
  haveI : IsAbelianGalois F E := IsAbelianGalois.of_isCyclic F E
  haveI : IsGalois F M := (IsAbelianGalois.tower_bot F M E).toIsGalois
  haveI : IsGalois M E := IsGalois.tower_top_of_isGalois F M E
  haveI : FiniteDimensional M E := Module.Finite.of_restrictScalars_finite F M E
  haveI : FiniteDimensional F M := FiniteDimensional.left F M E
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := E ≃ₐ[F] E)
  set d := Module.finrank F M with hd
  set m := Module.finrank M E with hm
  have hd0 : d ≠ 0 := Module.finrank_pos.ne'
  have hm0 : m ≠ 0 := Module.finrank_pos.ne'
  have hcard : Nat.card (E ≃ₐ[F] E) = d * m := by
    rw [IsGalois.card_aut_eq_finrank, Module.finrank_mul_finrank]
  have ho : orderOf σ = d * m := (orderOf_eq_card_of_forall_mem_zpowers hσ).trans hcard
  have hτ : orderOf (σ ^ d) = m := by
    rw [orderOf_pow_of_dvd hd0 (ho ▸ dvd_mul_right d m), ho,
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]
  set S := Algebra.TensorProduct.map (AlgHom.id K K) (σ : E →ₐ[F] E) with hS
  let T : K ⊗[F] E →* K ⊗[F] E := S
  have hT : (T : K ⊗[F] E → K ⊗[F] E) = S := rfl
  have hSd : (Algebra.TensorProduct.map (AlgHom.id K K) ((σ ^ d : E ≃ₐ[F] E) : E →ₐ[F] E) :
      K ⊗[F] E → K ⊗[F] E) = S^[d] := funext fun y => map_pow_iter σ d y
  have haK : algebraMap F K a ≠ 0 := (_root_.map_ne_zero _).2 ha
  obtain ⟨w, hw, hw'⟩ := core T d m x (algebraMap K _ (algebraMap F K a))
    (algebraMap K _ (algebraMap F K a)⁻¹) (by rw [← map_mul, mul_inv_cancel₀ haK, map_one])
    (S.commutes _) (S.commutes _)
    (by
      have := GlobalTheory.T.algebraMap_norm_tensor_eq_prod_galois_conjugates F E K x
      rw [hx, prod_cyc σ hσ, hcard, map_pow, map_pow] at this
      rw [this]
      exact Finset.prod_congr rfl fun i _ => (map_pow_iter σ i x).symm)
    (by
      intro u hu
      have := GlobalTheory.T.hilbert90_baseChange' F E K (σ ^ d) m hτ u (by rw [hSd]; exact hu)
      rw [hSd] at this
      exact this)
  obtain ⟨z, rfl⟩ := GlobalTheory.T.exists_tensor_eq_of_fixed_by_algEquiv F M E K w (by
    intro h
    obtain ⟨k, hk⟩ := exists_pow_of_pow_eq_one σ d m hm0 hσ ho (h.restrictScalars F) (by
      have h1 : h ^ m = 1 := by
        rw [hm, ← IsGalois.card_aut_eq_finrank]; exact pow_card_eq_one'
      have := map_pow (AlgEquiv.restrictScalarsHom F (S := M) (A := E)) h m
      rw [h1, map_one] at this
      exact this.symm)
    rw [hk, map_pow_iter, Function.iterate_mul]
    exact Function.IsFixedPt.iterate hw k)
  set ι := Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom F M E) with hι
  have hinj : Function.Injective ι :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := K)
      (IsScalarTower.toAlgHom F M E).toLinearMap (algebraMap M E).injective
  let σ' : M ≃ₐ[F] M := AlgEquiv.restrictNormalHom M σ
  have hσ' : ∀ g, g ∈ Subgroup.zpowers σ' := by
    intro g
    obtain ⟨g', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := M) E g
    obtain ⟨k, rfl⟩ := hσ g'
    exact ⟨k, (map_zpow _ _ _).symm⟩
  have hcomm : ∀ u : K ⊗[F] M,
      ι (Algebra.TensorProduct.map (AlgHom.id K K) (σ' : M →ₐ[F] M) u) = S (ι u) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul k e =>
      have : algebraMap M E (σ' e) = σ (algebraMap M E e) :=
        AlgEquiv.restrictNormal_commutes σ M e
      simp [hι, hS, this]
    | add u v hu hv => simp only [map_add, hu, hv]
  refine ⟨z, ?_⟩
  apply (algebraMap K (K ⊗[F] M)).injective
  apply hinj
  rw [GlobalTheory.T.algebraMap_norm_tensor_eq_prod_galois_conjugates F M K z, prod_cyc σ' hσ', IsGalois.card_aut_eq_finrank, ι.commutes, ← hw',
    map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_pow_iter]
  exact Function.Semiconj.iterate_right hcomm i z

end GlobalTheory.CNorm
