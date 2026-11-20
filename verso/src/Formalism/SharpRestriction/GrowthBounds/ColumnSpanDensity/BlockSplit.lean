import Mathlib

namespace Formalism.MainNotions.flipOneThree.Pf.KP

def BlockSplit : Prop :=
  ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {J : Type} [Fintype J] (n : ℕ) (z : O), z ≠ 0 →
    ∀ (A : J → Matrix (Fin n) (Fin n) O), ∑ j, A j = z • (1 : Matrix (Fin n) (Fin n) O) →
    ∃ ν : J → ℕ, n ≤ ∑ j, ν j ∧ ∀ j, ∃ (P : Matrix (Fin (ν j)) (Fin n) O) (Q : Matrix (Fin n) (Fin (ν j)) O),
      P * A j * Q = z • (1 : Matrix (Fin (ν j)) (Fin (ν j)) O)

open Module

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

private noncomputable def bspZ (n : ℕ) (z : O) : Submodule O (Fin n → O) :=
  LinearMap.range (z • (LinearMap.id : (Fin n → O) →ₗ[O] (Fin n → O)))

/- English proof (translation)
Use `haveI : ValuationRing O := ((IsDiscreteValuationRing.TFAE O (IsDiscreteValuationRing.not_isField O)).out 0 1).mp (inferInstance : IsDiscreteValuationRing O)`. Take `⟨m, S⟩` from `Submodule.smithNormalForm (Pi.basisFun O (Fin n)) (LinearMap.range (Matrix.mulVecLin A))`. Set `T : Finset (Fin m)` to `Finset.univ.filter (fun k => S.a k ∣ z)`. Set `e : Fin T.card ≃ T` to `T.equivFin.symm`. Use `choose x hx using fun k : Fin m => (S.bN k).2`.

Establish `hc : ∀ t : T, ∃ c, z = S.a t.1 * c` using `fun t => (Finset.mem_filter.mp t.2).2`. Use `choose c hc' using hc`. Set `w : Fin T.card → (Fin n → O)` to `fun i => c (e i) • x (e i).1`. Establish `hAw : ∀ i, Matrix.mulVec A (w i) = z • S.bM (S.f (e i).1)`. Introduce `i`.

Establish `h1` using `hx (e i).1`. Rewrite `h1` using `[Matrix.mulVecLin_apply]`. Use `show Matrix.mulVec A (c (e i) • x (e i).1) = _`. Rewrite using `[Matrix.mulVec_smul, h1, S.snf, smul_smul, hc' (e i), mul_comm]`. Use `⟨T.card, fun i => S.bM (S.f (e i).1), ?_, ?_⟩` and prove the remaining obligations.

Introduce `y hy`. Establish `e2` using `congrArg Subtype.val (S.bN.sum_repr ⟨y, hy⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at e2`. Rewrite using `[← e2]`. Use `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations.

Rewrite using `[S.snf]`. Distinguish the cases in `hk : S.a k ∣ z`. Apply `Submodule.mem_sup_left` to reduce the goal to its premises. Apply `Submodule.smul_mem` to reduce the goal to its premises. Apply `Submodule.subset_span` to reduce the goal to its premises.

Conclude with `⟨e.symm ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩, by simp⟩`. Apply `Submodule.mem_sup_right` to reduce the goal to its premises. Take `⟨d, hd⟩` from `(ValuationRing.dvd_total (S.a k) z).resolve_left hk`. Establish `hdm : d ∈ IsLocalRing.maximalIdeal O`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`.

Introduce `hu`. Conclude with `hk ⟨↑hu.unit⁻¹, by rw [hd, mul_assoc, IsUnit.mul_val_inv, mul_one]⟩`. Rewrite using `[hd, mul_comm, ← smul_smul]`. Conclude with `Submodule.smul_mem_smul hdm ⟨S.bM (S.f k), rfl⟩`. Use `⟨Matrix.of fun i r => S.bM.coord (S.f (e i).1) (fun j => if r = j then 1 else 0), Matrix.of fun r i => w i r, ?_⟩` and prove the remaining obligations.

Use extensionality with `i i'`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_apply]`. Establish `hcol : ∀ r, (A * Matrix.of fun r i => w i r) r i' = (z • S.bM (S.f (e i').1)) r`. Introduce `r`. Rewrite using `[← hAw i']`.

Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Simplify using `only [hcol, Matrix.of_apply]`. Establish `hφ : ∑ r, S.bM.coord (S.f (e i).1) (fun j => if r = j then 1 else 0) * (z • S.bM (S.f (e i').1)) r = S.bM.coord (S.f (e i).1) (z • S.bM (S.f (e i').1))`. Rewrite using `[LinearMap.pi_apply_eq_sum_univ (S.bM.coord (S.f (e i).1)) (z • S.bM (S.f (e i').1))]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_eq_mul, mul_comm]`. Rewrite using `[hφ, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, smul_eq_mul]`. Distinguish the cases in `hii : i = i'`. Substitute `hii` using the available equality. Simplify using the standard rewrite rules.

Establish `hne : S.f (e i).1 ≠ S.f (e i').1` using `fun h => hii (e.injective (Subtype.ext (S.f.injective h)))`. Simplify using `[Finsupp.single_apply, hne, hii]`.
-/
private theorem bsp_one (n : ℕ) (z : O) (A : Matrix (Fin n) (Fin n) O) :
    ∃ (ν : ℕ) (v : Fin ν → (Fin n → O)),
      LinearMap.range (Matrix.mulVecLin A) ≤
        Submodule.span O (Set.range v) ⊔ IsLocalRing.maximalIdeal O • bspZ n z ∧
      ∃ (P : Matrix (Fin ν) (Fin n) O) (Q : Matrix (Fin n) (Fin ν) O),
        P * A * Q = z • (1 : Matrix (Fin ν) (Fin ν) O) := by
  classical
  haveI : ValuationRing O :=
    ((IsDiscreteValuationRing.TFAE O (IsDiscreteValuationRing.not_isField O)).out 0 1).mp
      (inferInstance : IsDiscreteValuationRing O)
  obtain ⟨m, S⟩ := Submodule.smithNormalForm (Pi.basisFun O (Fin n))
    (LinearMap.range (Matrix.mulVecLin A))
  let T : Finset (Fin m) := Finset.univ.filter (fun k => S.a k ∣ z)
  let e : Fin T.card ≃ T := T.equivFin.symm
  choose x hx using fun k : Fin m => (S.bN k).2
  have hc : ∀ t : T, ∃ c, z = S.a t.1 * c := fun t => (Finset.mem_filter.mp t.2).2
  choose c hc' using hc
  let w : Fin T.card → (Fin n → O) := fun i => c (e i) • x (e i).1
  have hAw : ∀ i, Matrix.mulVec A (w i) = z • S.bM (S.f (e i).1) := by
    intro i
    have h1 := hx (e i).1
    rw [Matrix.mulVecLin_apply] at h1
    show Matrix.mulVec A (c (e i) • x (e i).1) = _
    rw [Matrix.mulVec_smul, h1, S.snf, smul_smul, hc' (e i), mul_comm]
  refine ⟨T.card, fun i => S.bM (S.f (e i).1), ?_, ?_⟩
  · intro y hy
    have e2 := congrArg Subtype.val (S.bN.sum_repr ⟨y, hy⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at e2
    rw [← e2]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    rw [S.snf]
    by_cases hk : S.a k ∣ z
    · apply Submodule.mem_sup_left
      apply Submodule.smul_mem
      apply Submodule.subset_span
      exact ⟨e.symm ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩, by simp⟩
    · apply Submodule.mem_sup_right
      obtain ⟨d, hd⟩ := (ValuationRing.dvd_total (S.a k) z).resolve_left hk
      have hdm : d ∈ IsLocalRing.maximalIdeal O := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        exact hk ⟨↑hu.unit⁻¹, by rw [hd, mul_assoc, IsUnit.mul_val_inv, mul_one]⟩
      rw [hd, mul_comm, ← smul_smul]
      exact Submodule.smul_mem_smul hdm ⟨S.bM (S.f k), rfl⟩
  · refine ⟨Matrix.of fun i r => S.bM.coord (S.f (e i).1) (fun j => if r = j then 1 else 0),
      Matrix.of fun r i => w i r, ?_⟩
    ext i i'
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    have hcol : ∀ r, (A * Matrix.of fun r i => w i r) r i' = (z • S.bM (S.f (e i').1)) r := by
      intro r
      rw [← hAw i']
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    simp only [hcol, Matrix.of_apply]
    have hφ : ∑ r, S.bM.coord (S.f (e i).1) (fun j => if r = j then 1 else 0) *
        (z • S.bM (S.f (e i').1)) r = S.bM.coord (S.f (e i).1) (z • S.bM (S.f (e i').1)) := by
      rw [LinearMap.pi_apply_eq_sum_univ (S.bM.coord (S.f (e i).1)) (z • S.bM (S.f (e i').1))]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [smul_eq_mul, mul_comm]
    rw [hφ, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, smul_eq_mul]
    by_cases hii : i = i'
    · subst hii
      simp
    · have hne : S.f (e i).1 ≠ S.f (e i').1 := fun h =>
        hii (e.injective (Subtype.ext (S.f.injective h)))
      simp [Finsupp.single_apply, hne, hii]

/- English proof (translation)
Use `choose ν v hv P Q hPQ using fun j => bsp_one n z (A j)`. Use `⟨ν, ?_, fun j => ⟨P j, Q j, hPQ j⟩⟩` and prove the remaining obligations. Set `V : (Σ j, Fin (ν j)) → (Fin n → O)` to `fun jk => v jk.1 jk.2`. Set `W : Submodule O (Fin n → O)` to `Submodule.span O (Set.range V)`. Establish `hvW : ∀ j, Submodule.span O (Set.range (v j)) ≤ W`.

Introduce `j`. Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `⟨⟨j, k⟩, rfl⟩`. Establish `hsum : ∀ (s : Finset J) (x : Fin n → O), Matrix.mulVec (∑ j ∈ s, A j) x = ∑ j ∈ s, Matrix.mulVec (A j) x`.

Introduce `s x`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, Matrix.add_mulVec, ih]`. Establish `hZ : bspZ n z ≤ W ⊔ IsLocalRing.maximalIdeal O • bspZ n z`.

Introduce and unpack `_ ⟨x, rfl⟩`. Establish `hx : (z • (LinearMap.id : (Fin n → O) →ₗ[O] (Fin n → O))) x = ∑ j, Matrix.mulVec (A j) x`. Rewrite using `[LinearMap.smul_apply, LinearMap.id_apply, ← hsum, h, Matrix.smul_mulVec, Matrix.one_mulVec]`. Rewrite using `[hx]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations.

Conclude with `sup_le_sup_right (hvW j) _ (hv j ⟨x, rfl⟩)`. Establish `hfg : (bspZ n z).FG`. Unfold `bspZ`. Rewrite using `[LinearMap.range_eq_map]`. Conclude with `Module.Finite.fg_top.map _`.

Establish `hjac : IsLocalRing.maximalIdeal O ≤ Ideal.jacobson ⊥`. Rewrite using `[IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]`. Establish `hZW : bspZ n z ≤ W` using `Submodule.le_of_le_smul_of_le_jacobson_bot hfg hjac hZ`. Set `f` to `z • (LinearMap.id : (Fin n → O) →ₗ[O] (Fin n → O))`. Establish `hinj : LinearMap.ker f = ⊥`.

Rewrite using `[LinearMap.ker_eq_bot]`. Introduce `x y hxy`. Conclude with `smul_right_injective _ hz hxy`. Establish `hli : LinearIndependent O (fun i : Fin n => f (Pi.basisFun O (Fin n) i))` using `(Pi.basisFun O (Fin n)).linearIndependent.map' f hinj`. Establish `hle` using `linearIndependent_le_span' _ hli (Set.range V) (by`.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hZW ⟨_, rfl⟩)`. Combine the equalities or inequalities in the displayed calculation. Rewrite `hle` using `[Cardinal.mk_fintype]`. Conclude with `hle` after adjusting the coercions.

Use `_ ≤ Fintype.card (Σ j, Fin (ν j)) := Fintype.card_range_le V`. Use `_ = ∑ j, ν j := by simp [Fintype.card_sigma]`.
-/
theorem blockSplit {J : Type} [Fintype J] (n : ℕ) (z : O) (hz : z ≠ 0)
    (A : J → Matrix (Fin n) (Fin n) O) (h : ∑ j, A j = z • (1 : Matrix (Fin n) (Fin n) O)) :
    ∃ ν : J → ℕ, n ≤ ∑ j, ν j ∧ ∀ j, ∃ (P : Matrix (Fin (ν j)) (Fin n) O)
      (Q : Matrix (Fin n) (Fin (ν j)) O), P * A j * Q = z • (1 : Matrix _ _ O) := by
  classical
  choose ν v hv P Q hPQ using fun j => bsp_one n z (A j)
  refine ⟨ν, ?_, fun j => ⟨P j, Q j, hPQ j⟩⟩
  let V : (Σ j, Fin (ν j)) → (Fin n → O) := fun jk => v jk.1 jk.2
  let W : Submodule O (Fin n → O) := Submodule.span O (Set.range V)
  have hvW : ∀ j, Submodule.span O (Set.range (v j)) ≤ W := by
    intro j
    apply Submodule.span_mono
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨j, k⟩, rfl⟩
  have hsum : ∀ (s : Finset J) (x : Fin n → O), Matrix.mulVec (∑ j ∈ s, A j) x = ∑ j ∈ s, Matrix.mulVec (A j) x := by
    intro s x
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, Matrix.add_mulVec, ih]
  have hZ : bspZ n z ≤ W ⊔ IsLocalRing.maximalIdeal O • bspZ n z := by
    rintro _ ⟨x, rfl⟩
    have hx : (z • (LinearMap.id : (Fin n → O) →ₗ[O] (Fin n → O))) x = ∑ j, Matrix.mulVec (A j) x := by
      rw [LinearMap.smul_apply, LinearMap.id_apply, ← hsum, h, Matrix.smul_mulVec,
        Matrix.one_mulVec]
    rw [hx]
    refine Submodule.sum_mem _ fun j _ => ?_
    exact sup_le_sup_right (hvW j) _ (hv j ⟨x, rfl⟩)
  have hfg : (bspZ n z).FG := by
    unfold bspZ
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  have hjac : IsLocalRing.maximalIdeal O ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have hZW : bspZ n z ≤ W := Submodule.le_of_le_smul_of_le_jacobson_bot hfg hjac hZ
  let f := z • (LinearMap.id : (Fin n → O) →ₗ[O] (Fin n → O))
  have hinj : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    exact smul_right_injective _ hz hxy
  have hli : LinearIndependent O (fun i : Fin n => f (Pi.basisFun O (Fin n) i)) :=
    (Pi.basisFun O (Fin n)).linearIndependent.map' f hinj
  have hle := linearIndependent_le_span' _ hli (Set.range V) (by
    rintro _ ⟨i, rfl⟩
    exact hZW ⟨_, rfl⟩)
  calc n = Fintype.card (Fin n) := (Fintype.card_fin n).symm
    _ ≤ Fintype.card (Set.range V) := by
        rw [Cardinal.mk_fintype] at hle
        exact_mod_cast hle
    _ ≤ Fintype.card (Σ j, Fin (ν j)) := Fintype.card_range_le V
    _ = ∑ j, ν j := by simp [Fintype.card_sigma]

/- English proof (translation)
Introduce `O _ _ _ J _ n z hz A h`. Conclude with `blockSplit n z hz A h`.
-/
theorem blockSplitting_holds : BlockSplit := by
  intro O _ _ _ J _ n z hz A h
  exact blockSplit n z hz A h

end Formalism.MainNotions.flipOneThree.Pf.KP
