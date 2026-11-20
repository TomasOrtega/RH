import Mathlib

open Polynomial

namespace UpperTheory.V.Lib.FinChar

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {n : ℕ}

/- English proof (translation)
Establish `hmk : ((m : ℕ) : k) ≠ 0` using `Nat.cast_ne_zero.mpr hm.ne'`. Establish `hsep : (X ^ m - C (1 : k)).Separable` using `separable_X_pow_sub_C 1 hmk one_ne_zero`. Establish `hss : f.IsSemisimple` using `Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree (by simp [hfm])`. Establish `hint : DirectSum.IsInternal f.eigenspace` using `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top f.eigenspaces_iSupIndep hss.iSup_eigenspace_eq_top`. Set `v` to `fun μ => Module.Basis.ofVectorSpace k (f.eigenspace μ)`.

Set `B` to `hint.collectedBasis v`. Set `e` to `B.indexEquiv (Pi.basisFun k (Fin n))`. Use `⟨B.reindex e, fun i => (e.symm i).1, fun i => ?_⟩` and prove the remaining obligations. Establish `hmem` using `hint.collectedBasis_mem v (e.symm i)`. Rewrite `hmem` using `[Module.End.mem_eigenspace_iff]`.

Simplify `hmem` using `[Module.Basis.reindex_apply, B]`.
-/
theorem exists_eigenbasis (f : Module.End k (Fin n → k)) {m : ℕ} (hm : 0 < m) (hfm : f ^ m = 1) :
    ∃ (b : Module.Basis (Fin n) k (Fin n → k)) (d : Fin n → k), ∀ i, f (b i) = d i • b i := by
  classical
  have hmk : ((m : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hsep : (X ^ m - C (1 : k)).Separable := separable_X_pow_sub_C 1 hmk one_ne_zero
  have hss : f.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree (by simp [hfm])
  have hint : DirectSum.IsInternal f.eigenspace :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top f.eigenspaces_iSupIndep
      hss.iSup_eigenspace_eq_top
  let v := fun μ => Module.Basis.ofVectorSpace k (f.eigenspace μ)
  let B := hint.collectedBasis v
  let e := B.indexEquiv (Pi.basisFun k (Fin n))
  refine ⟨B.reindex e, fun i => (e.symm i).1, fun i => ?_⟩
  have hmem := hint.collectedBasis_mem v (e.symm i)
  rw [Module.End.mem_eigenspace_iff] at hmem
  simpa [Module.Basis.reindex_apply, B] using hmem

/- English proof (translation)
Take `⟨b, d, hb⟩` from `exists_eigenbasis (Matrix.toLinAlgEquiv' T.val) hm (by rw [← map_pow, ← Units.val_pow_eq_pow_val, hT, Units.val_one, map_one])`. Use `letI := (Pi.basisFun k (Fin n)).invertibleToMatrix b`. Use `⟨unitOfInvertible ((Pi.basisFun k (Fin n)).toMatrix b), d, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Rewrite using `[Matrix.mul_diagonal]`.

Establish `hj` using `congrFun (hb j) i`. Simplify using `only [Matrix.toLinAlgEquiv'_apply, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hj`. Simplify using `[Matrix.mul_apply, Module.Basis.toMatrix_apply, hj, mul_comm]`.
-/
theorem exists_eigenframe (T : (Matrix (Fin n) (Fin n) k)ˣ) {m : ℕ} (hm : 0 < m) (hT : T ^ m = 1) :
    ∃ (u : (Matrix (Fin n) (Fin n) k)ˣ) (d : Fin n → k), T.val * u.val = u.val * Matrix.diagonal d := by
  classical
  obtain ⟨b, d, hb⟩ := exists_eigenbasis (Matrix.toLinAlgEquiv' T.val) hm
    (by rw [← map_pow, ← Units.val_pow_eq_pow_val, hT, Units.val_one, map_one])
  letI := (Pi.basisFun k (Fin n)).invertibleToMatrix b
  refine ⟨unitOfInvertible ((Pi.basisFun k (Fin n)).toMatrix b), d, ?_⟩
  ext i j
  rw [Matrix.mul_diagonal]
  have hj := congrFun (hb j) i
  simp only [Matrix.toLinAlgEquiv'_apply, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hj
  simp [Matrix.mul_apply, Module.Basis.toMatrix_apply, hj, mul_comm]

/- English proof (translation)
Take `⟨u, d, hu⟩` from `exists_eigenframe T hm hT`. Establish `hc : ∀ a : ℕ, T.val ^ a * u.val = u.val * Matrix.diagonal d ^ a`. Introduce `a`. Proceed by induction on `a with`. Consider the case `zero => simp`.

Consider the case `succ a ih => rw [pow_succ', mul_assoc, ih, ← mul_assoc, hu, mul_assoc, ← pow_succ']`. Use `⟨d, fun i => ?_, fun a => ?_⟩` and prove the remaining obligations. Establish `h1 : u.val * Matrix.diagonal (d ^ m) = u.val * 1`. Rewrite using `[← Matrix.diagonal_pow, ← hc m, ← Units.val_pow_eq_pow_val, hT, Units.val_one, one_mul, mul_one]`. Establish `h2` using `(Units.mul_right_inj u).mp h1`.

Establish `h3` using `congrFun (congrFun h2 i) i`. Simplify using `using h3`. Establish `hdet : IsUnit u.val.det` using `(Matrix.isUnit_iff_isUnit_det _).mp u.isUnit`. Establish `h1 : (T ^ a).val = u.val * Matrix.diagonal d ^ a * (u.val)⁻¹`. Rewrite using `[Units.val_pow_eq_pow_val, ← hc a, mul_assoc, Matrix.mul_nonsing_inv _ hdet, mul_one]`.

Rewrite using `[h1, Matrix.charpoly_units_conj, Matrix.diagonal_pow, Matrix.charpoly_diagonal]`. Simplify using `[Pi.pow_apply]`.
-/
theorem charpoly_powers (T : (Matrix (Fin n) (Fin n) k)ˣ) {m : ℕ} (hm : 0 < m) (hT : T ^ m = 1) :
    ∃ d : Fin n → k, (∀ i, d i ^ m = 1) ∧ ∀ a : ℕ, (T ^ a).val.charpoly = ∏ i, (X - C (d i ^ a)) := by
  classical
  obtain ⟨u, d, hu⟩ := exists_eigenframe T hm hT
  have hc : ∀ a : ℕ, T.val ^ a * u.val = u.val * Matrix.diagonal d ^ a := by
    intro a
    induction a with
    | zero => simp
    | succ a ih => rw [pow_succ', mul_assoc, ih, ← mul_assoc, hu, mul_assoc, ← pow_succ']
  refine ⟨d, fun i => ?_, fun a => ?_⟩
  · have h1 : u.val * Matrix.diagonal (d ^ m) = u.val * 1 := by
      rw [← Matrix.diagonal_pow, ← hc m, ← Units.val_pow_eq_pow_val, hT, Units.val_one, one_mul,
        mul_one]
    have h2 := (Units.mul_right_inj u).mp h1
    have h3 := congrFun (congrFun h2 i) i
    simpa using h3
  · have hdet : IsUnit u.val.det := (Matrix.isUnit_iff_isUnit_det _).mp u.isUnit
    have h1 : (T ^ a).val = u.val * Matrix.diagonal d ^ a * (u.val)⁻¹ := by
      rw [Units.val_pow_eq_pow_val, ← hc a, mul_assoc, Matrix.mul_nonsing_inv _ hdet, mul_one]
    rw [h1, Matrix.charpoly_units_conj, Matrix.diagonal_pow, Matrix.charpoly_diagonal]
    simp [Pi.pow_apply]

/- English proof (translation)
Use `set S : Subgroup kˣ := I.map χ with hS`. Establish `hSf : (S : Set kˣ).Finite` using `by rw [hS, Subgroup.coe_map]; exact hf`. Use `haveI : Finite S := hSf.to_subtype`. Take `⟨x, hx⟩` from `IsCyclic.exists_monoid_generator (α := S)`. Take `⟨g0, hg0I, hg0⟩` from `Subgroup.mem_map.mp x.2`.

Use `set N := orderOf x with hN`. Establish `hNpos : 0 < N` using `orderOf_pos x`. Establish `hxN : (x : kˣ) ^ N = 1`. Establish `h` using `congrArg Subtype.val (pow_orderOf_eq_one x)`. Conclude with `h` after adjusting the coercions.

Establish `hrN : r g0 ^ N = 1`. Rewrite using `[← map_pow]`. Apply `hk _ (I.pow_mem hg0I N)` to reduce the goal to its premises. Rewrite using `[map_pow, hg0, hxN]`. Take `⟨d, hd, hchar⟩` from `charpoly_powers (r g0) hNpos hrN`.

Establish `hprim : IsPrimitiveRoot ((x : kˣ) : k) N`. Rewrite using `[IsPrimitiveRoot.coe_units_iff, hN, ← Subgroup.orderOf_coe]`. Conclude with `IsPrimitiveRoot.orderOf _`. Use `haveI : NeZero N := ⟨hNpos.ne'⟩`. Establish `hj : ∀ i, ∃ j, ((x : kˣ) : k) ^ j = d i` using `fun i =>`.

Set `⟨j, _, h⟩` to `hprim.eq_pow_of_pow_eq_one (hd i)`. Use the proof step `⟨j, h⟩`. Use `choose j hj using hj`. Use `⟨j, fun g hg => ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `(Submonoid.mem_powers_iff _ _).mp (hx ⟨χ g, Subgroup.mem_map_of_mem χ hg⟩)`.

Establish `hχa : χ g = (x : kˣ) ^ a`. Rewrite using `[← SubgroupClass.coe_pow, ha]`. Establish `hrg : r g = r g0 ^ a`. Establish `h1 : χ (g * (g0 ^ a)⁻¹) = 1`. Rewrite using `[map_mul, map_inv, map_pow, hg0, hχa, mul_inv_cancel]`.

Establish `h2` using `hk _ (I.mul_mem hg (I.inv_mem (I.pow_mem hg0I a))) h1`. Rewrite `h2` using `[map_mul, map_inv, map_pow, mul_inv_eq_one]`. Conclude with `h2`. Rewrite using `[hrg, hchar a]`. Use `Finset.prod_congr rfl (fun i _ => ?_)` and prove the remaining obligations.

Rewrite using `[← hj i, hχa, Units.val_pow_eq_pow_val, ← pow_mul, ← pow_mul, Nat.mul_comm]`.
-/
theorem charpoly_of_ker {Γ : Type} [Group Γ] (r : Γ →* (Matrix (Fin n) (Fin n) k)ˣ) (χ : Γ →* kˣ) (I : Subgroup Γ)
    (hf : (χ '' (I : Set Γ)).Finite) (hk : ∀ g ∈ I, χ g = 1 → r g = 1) :
    ∃ j : Fin n → ℕ, ∀ g ∈ I, (r g).val.charpoly = ∏ i, (X - C ((χ g : k) ^ j i)) := by
  classical
  set S : Subgroup kˣ := I.map χ with hS
  have hSf : (S : Set kˣ).Finite := by rw [hS, Subgroup.coe_map]; exact hf
  haveI : Finite S := hSf.to_subtype
  obtain ⟨x, hx⟩ := IsCyclic.exists_monoid_generator (α := S)
  obtain ⟨g0, hg0I, hg0⟩ := Subgroup.mem_map.mp x.2
  set N := orderOf x with hN
  have hNpos : 0 < N := orderOf_pos x
  have hxN : (x : kˣ) ^ N = 1 := by
    have h := congrArg Subtype.val (pow_orderOf_eq_one x)
    exact_mod_cast h
  have hrN : r g0 ^ N = 1 := by
    rw [← map_pow]
    apply hk _ (I.pow_mem hg0I N)
    rw [map_pow, hg0, hxN]
  obtain ⟨d, hd, hchar⟩ := charpoly_powers (r g0) hNpos hrN
  have hprim : IsPrimitiveRoot ((x : kˣ) : k) N := by
    rw [IsPrimitiveRoot.coe_units_iff, hN, ← Subgroup.orderOf_coe]
    exact IsPrimitiveRoot.orderOf _
  haveI : NeZero N := ⟨hNpos.ne'⟩
  have hj : ∀ i, ∃ j, ((x : kˣ) : k) ^ j = d i := fun i =>
    let ⟨j, _, h⟩ := hprim.eq_pow_of_pow_eq_one (hd i); ⟨j, h⟩
  choose j hj using hj
  refine ⟨j, fun g hg => ?_⟩
  obtain ⟨a, ha⟩ := (Submonoid.mem_powers_iff _ _).mp (hx ⟨χ g, Subgroup.mem_map_of_mem χ hg⟩)
  have hχa : χ g = (x : kˣ) ^ a := by
    rw [← SubgroupClass.coe_pow, ha]
  have hrg : r g = r g0 ^ a := by
    have h1 : χ (g * (g0 ^ a)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_pow, hg0, hχa, mul_inv_cancel]
    have h2 := hk _ (I.mul_mem hg (I.inv_mem (I.pow_mem hg0I a))) h1
    rw [map_mul, map_inv, map_pow, mul_inv_eq_one] at h2
    exact h2
  rw [hrg, hchar a]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [← hj i, hχa, Units.val_pow_eq_pow_val, ← pow_mul, ← pow_mul, Nat.mul_comm]

end UpperTheory.V.Lib.FinChar
