import Mathlib
open scoped NNReal

namespace GlobalTheory

open Matrix

/- English proof (translation)
Use `set N : Submodule C (Fin d → C) := LinearMap.ker (Matrix.toLin' Y) with hN`. Set `e : Fin d → (Fin d → C)` to `fun k => Pi.single k 1`. Establish `hsupp : ∀ (S : Set (Fin d)) (v : Fin d → C), (∀ i, i ∉ S → v i = 0) → v ∈ Submodule.span C (e '' S)`. Introduce `S v hv`. Rewrite using `[show v = ∑ k, Pi.single k (v k) from (Finset.univ_sum_single v).symm]`.

Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : k ∈ S`. Establish `: Pi.single k (v k) = v k • e k`. Use extensionality with `i`. Simplify using `[e, Pi.single_apply]`.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)`. Rewrite using `[hv k hk, Pi.single_zero]`. Conclude with `Submodule.zero_mem _`. Establish `hspan : Submodule.span C (Set.range (N.mkQ ∘ e)) = ⊤`.

Rewrite using `[Set.range_comp, ← Submodule.map_span]`. Establish `: Submodule.span C (Set.range e) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `v _`. Use `hsupp Set.univ v (fun i hi => absurd (Set.mem_univ i) hi)` as an intermediate fact.

Rewrite `this` using `[Set.image_univ]`. Then use the resulting hypothesis. Rewrite using `[this, Submodule.map_top, Submodule.range_mkQ]`. Take `⟨κ, a, ha, hsp, hli⟩` from `exists_linearIndependent' C (N.mkQ ∘ e)`. Establish `: Finite κ` using `Finite.of_injective a ha`. Use `Fintype.ofFinite κ` as an intermediate fact.

Use `set W : Submodule C (Fin d → C) := Submodule.span C (e '' Set.range a) with hW`. Establish `hWeq : W = Submodule.span C (Set.range (e ∘ a))` using `by rw [hW, Set.range_comp]`. Establish `hWcoord : ∀ w ∈ W, ∀ i, i ∉ Set.range a → w i = 0`. Introduce `w hw i hi`. Use `Submodule.span_induction (p := fun w _ => w i = 0) ?_ ?_ ?_ ?_ hw` and prove the remaining obligations.

Introduce and unpack `_ ⟨k, ⟨m, rfl⟩, rfl⟩`. Establish `: i ≠ a m` using `fun h => hi ⟨m, h.symm⟩`. Simplify using `[e, Pi.single_apply, this]`. Simplify using the standard rewrite rules. Introduce `x y _ _ hx hy`.

Simplify using `[hx, hy]`. Introduce `c x _ hx`. Simplify using `[hx]`. Establish `hc : IsCompl N W`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[disjoint_iff, eq_bot_iff]`. Introduce `y ⟨hyN, hyW⟩`. Rewrite `hyW` using `[hWeq]`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun C).mp hyW`. Establish `h0 : ∑ j, c j • (N.mkQ ∘ e ∘ a) j = 0`.

Simplify using `only [Function.comp_apply, ← map_smul, ← map_sum]`. Conclude with `(Submodule.Quotient.mk_eq_zero N).mpr hyN`. Establish `hc0` using `Fintype.linearIndependent_iff.mp hli c h0`. Simplify using `[hc0]`. Rewrite using `[codisjoint_iff, ← Submodule.map_mkQ_eq_top, hWeq, Submodule.map_span, ← Set.range_comp]`.

Conclude with `hsp.trans hspan`. Use `set P := N.projection W hc with hP`. Use `set Q : Matrix (Fin d) (Fin d) C := LinearMap.toMatrix' P with hQ`. Establish `hQv : ∀ v, Q *ᵥ v = P v` using `fun v => by`. Rewrite using `[← Matrix.toLin'_apply, hQ, Matrix.toLin'_toMatrix']`.

Establish `hPN : ∀ v, P v ∈ N` using `fun v => Submodule.projection_apply_mem hc v`. Establish `hmemN : ∀ v, v ∈ N ↔ Y *ᵥ v = 0` using `fun v => by`. Rewrite using `[hN, LinearMap.mem_ker, Matrix.toLin'_apply]`. Establish `key : ∀ X Z : Matrix (Fin d) (Fin d) C, (∀ v, X *ᵥ v = Z *ᵥ v) → X = Z` using `fun X Z h => Matrix.toLin'.injective (LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using h v)`. Establish `hYQ : Y * Q = 0` using `key _ _ fun v => by`.

Rewrite using `[← Matrix.mulVec_mulVec, hQv, Matrix.zero_mulVec]`. Conclude with `(hmemN _).mp (hPN v)`. Use `set I : Finset (Fin d) := Finset.univ.filter (fun i => i ∉ Set.range a) with hI`. Establish `hmemI : ∀ i, i ∈ I ↔ i ∉ Set.range a` using `fun i => by simp [hI]`. Establish `hrow : ∀ i ∈ I, ∀ j, Q i j = if i = j then 1 else 0`.

Introduce `i hi j`. Rewrite using `[hQ, LinearMap.toMatrix'_apply]`. Establish `h1` using `hWcoord _ (Submodule.sub_projection_mem hc (Pi.single j (1 : C))) i ((hmemI i).mp hi)`. Rewrite `h1` using `[Pi.sub_apply, sub_eq_zero, Pi.single_apply]`. Rewrite `h1` using `[← hP]`.

Conclude with `h1.symm`. Establish `hcol : ∀ i, ∀ j ∉ I, Q i j = 0`. Introduce `i j hj`. Rewrite `hj` using `[hmemI, not_not]`. Rewrite using `[hQ, LinearMap.toMatrix'_apply]`.

Establish `: Pi.single j (1 : C) ∈ W` using `Submodule.subset_span ⟨j, hj, rfl⟩`. Rewrite using `[Submodule.projection_apply_of_mem_right hc this]`. Both sides reduce to the same expression. Use `set M : Matrix (Fin d) (Fin d) C := A * Q.map (frobenius C l) with hM`. Establish `hYM : Y * M = 0`.

Rewrite using `[hM, ← mul_assoc, ← hY, ← Matrix.map_mul, hYQ, Matrix.map_zero _ (map_zero _)]`. Establish `hrangeN : LinearMap.range (Matrix.toLin' M) ≤ N`. Introduce and unpack `_ ⟨v, rfl⟩`. Rewrite using `[hmemN, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hYM, Matrix.zero_mulVec]`. Establish `hkerW : LinearMap.ker (Matrix.toLin' M) ≤ W`.

Introduce `v hv`. Rewrite `hv` using `[LinearMap.mem_ker, Matrix.toLin'_apply, hM, ← Matrix.mulVec_mulVec]`. Establish `hAu : IsUnit A.det` using `isUnit_iff_ne_zero.mpr hA`. Establish `h0 : Q.map (frobenius C l) *ᵥ v = 0`. Use `congrArg (fun x => A⁻¹ *ᵥ x) hv` as an intermediate fact.

Simplify using `only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this`. Rewrite `this` using `[← mul_assoc, Matrix.nonsing_inv_mul A hAu, one_mul]`. Then use the resulting hypothesis. Use `hsupp (Set.range a) v (fun i hi => by` as an intermediate fact. Establish `hi' : i ∈ I` using `(hmemI i).mpr hi`. Establish `h2` using `congrFun h0 i`.

Simplify using `only [Matrix.mulVec, dotProduct, Matrix.map_apply, hrow i hi', Pi.zero_apply] at h2`. Simplify `h2)` using `[apply_ite]`. Rewrite `this` using `[← hW]`. Then use the resulting hypothesis. Establish `hrange : LinearMap.range (Matrix.toLin' M) = N`. Use `Submodule.eq_of_le_of_finrank_le hrangeN ?_` and prove the remaining obligations.

Establish `h1` using `LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' M)`. Establish `h2` using `Submodule.finrank_add_eq_of_isCompl hc`. Establish `h3` using `Submodule.finrank_mono hkerW`. Use linear arithmetic over natural numbers and integers. Establish `hex : ∀ j, ∃ w, Matrix.toLin' M w = P (Pi.single j 1)` using `fun j => by`.

Establish `: P (Pi.single j 1) ∈ LinearMap.range (Matrix.toLin' M)` using `hrange ▸ hPN _`. Conclude with `this`. Use `choose lam hlam using hex`. Use `⟨I, Q, Matrix.of fun k j => lam j k, hYQ, fun v hv => ?_, hrow, hcol, ?_⟩` and prove the remaining obligations. Rewrite using `[hQv]`.

Conclude with `Submodule.projection_apply_of_mem_left hc ((hmemN v).mpr hv)`. Use extensionality with `i j`. Rewrite using `[← hM, Matrix.mul_apply]`. Use `congrFun (hlam j) i` as an intermediate fact. Rewrite `this` using `[Matrix.toLin'_apply]`.

Rewrite using `[hQ, LinearMap.toMatrix'_apply, ← this]`. Simplify using `[Matrix.mulVec, dotProduct]`.
-/
theorem echelon_projector_frobenius (l : ℕ) [Fact l.Prime] (C : Type) [Field C] [CharP C l]
    (d : ℕ) (Y A : Matrix (Fin d) (Fin d) C) (hA : A.det ≠ 0)
    (hY : Y.map (frobenius C l) = Y * A) :
    ∃ (I : Finset (Fin d)) (Q Λ : Matrix (Fin d) (Fin d) C), Y * Q = 0 ∧
      (∀ v, Y.mulVec v = 0 → Q.mulVec v = v) ∧
      (∀ i ∈ I, ∀ j, Q i j = if i = j then 1 else 0) ∧ (∀ i, ∀ j ∉ I, Q i j = 0) ∧
      Q = A * Q.map (frobenius C l) * Λ := by
  classical
  set N : Submodule C (Fin d → C) := LinearMap.ker (Matrix.toLin' Y) with hN
  let e : Fin d → (Fin d → C) := fun k => Pi.single k 1

  have hsupp : ∀ (S : Set (Fin d)) (v : Fin d → C), (∀ i, i ∉ S → v i = 0) →
      v ∈ Submodule.span C (e '' S) := by
    intro S v hv
    rw [show v = ∑ k, Pi.single k (v k) from (Finset.univ_sum_single v).symm]
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : k ∈ S
    · have : Pi.single k (v k) = v k • e k := by
        ext i; simp [e, Pi.single_apply]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)
    · rw [hv k hk, Pi.single_zero]; exact Submodule.zero_mem _
  have hspan : Submodule.span C (Set.range (N.mkQ ∘ e)) = ⊤ := by
    rw [Set.range_comp, ← Submodule.map_span]
    have : Submodule.span C (Set.range e) = ⊤ := by
      rw [eq_top_iff]; intro v _
      have := hsupp Set.univ v (fun i hi => absurd (Set.mem_univ i) hi)
      rwa [Set.image_univ] at this
    rw [this, Submodule.map_top, Submodule.range_mkQ]
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' C (N.mkQ ∘ e)
  have : Finite κ := Finite.of_injective a ha
  have := Fintype.ofFinite κ
  set W : Submodule C (Fin d → C) := Submodule.span C (e '' Set.range a) with hW
  have hWeq : W = Submodule.span C (Set.range (e ∘ a)) := by rw [hW, Set.range_comp]
  have hWcoord : ∀ w ∈ W, ∀ i, i ∉ Set.range a → w i = 0 := by
    intro w hw i hi
    refine Submodule.span_induction (p := fun w _ => w i = 0) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨k, ⟨m, rfl⟩, rfl⟩
      have : i ≠ a m := fun h => hi ⟨m, h.symm⟩
      simp [e, Pi.single_apply, this]
    · simp
    · intro x y _ _ hx hy; simp [hx, hy]
    · intro c x _ hx; simp [hx]
  have hc : IsCompl N W := by
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      intro y ⟨hyN, hyW⟩
      rw [hWeq] at hyW
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun C).mp hyW
      have h0 : ∑ j, c j • (N.mkQ ∘ e ∘ a) j = 0 := by
        simp only [Function.comp_apply, ← map_smul, ← map_sum]
        exact (Submodule.Quotient.mk_eq_zero N).mpr hyN
      have hc0 := Fintype.linearIndependent_iff.mp hli c h0
      simp [hc0]
    · rw [codisjoint_iff, ← Submodule.map_mkQ_eq_top, hWeq, Submodule.map_span, ← Set.range_comp]
      exact hsp.trans hspan
  set P := N.projection W hc with hP
  set Q : Matrix (Fin d) (Fin d) C := LinearMap.toMatrix' P with hQ
  have hQv : ∀ v, Q *ᵥ v = P v := fun v => by
    rw [← Matrix.toLin'_apply, hQ, Matrix.toLin'_toMatrix']
  have hPN : ∀ v, P v ∈ N := fun v => Submodule.projection_apply_mem hc v
  have hmemN : ∀ v, v ∈ N ↔ Y *ᵥ v = 0 := fun v => by
    rw [hN, LinearMap.mem_ker, Matrix.toLin'_apply]
  have key : ∀ X Z : Matrix (Fin d) (Fin d) C, (∀ v, X *ᵥ v = Z *ᵥ v) → X = Z :=
    fun X Z h => Matrix.toLin'.injective (LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using h v)
  have hYQ : Y * Q = 0 := key _ _ fun v => by
    rw [← Matrix.mulVec_mulVec, hQv, Matrix.zero_mulVec]; exact (hmemN _).mp (hPN v)
  set I : Finset (Fin d) := Finset.univ.filter (fun i => i ∉ Set.range a) with hI
  have hmemI : ∀ i, i ∈ I ↔ i ∉ Set.range a := fun i => by simp [hI]
  have hrow : ∀ i ∈ I, ∀ j, Q i j = if i = j then 1 else 0 := by
    intro i hi j
    rw [hQ, LinearMap.toMatrix'_apply]
    have h1 := hWcoord _ (Submodule.sub_projection_mem hc (Pi.single j (1 : C))) i ((hmemI i).mp hi)
    rw [Pi.sub_apply, sub_eq_zero, Pi.single_apply] at h1
    rw [← hP] at h1
    exact h1.symm
  have hcol : ∀ i, ∀ j ∉ I, Q i j = 0 := by
    intro i j hj
    rw [hmemI, not_not] at hj
    rw [hQ, LinearMap.toMatrix'_apply]
    have : Pi.single j (1 : C) ∈ W := Submodule.subset_span ⟨j, hj, rfl⟩
    rw [Submodule.projection_apply_of_mem_right hc this]; rfl

  set M : Matrix (Fin d) (Fin d) C := A * Q.map (frobenius C l) with hM
  have hYM : Y * M = 0 := by
    rw [hM, ← mul_assoc, ← hY, ← Matrix.map_mul, hYQ, Matrix.map_zero _ (map_zero _)]
  have hrangeN : LinearMap.range (Matrix.toLin' M) ≤ N := by
    rintro _ ⟨v, rfl⟩
    rw [hmemN, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hYM, Matrix.zero_mulVec]
  have hkerW : LinearMap.ker (Matrix.toLin' M) ≤ W := by
    intro v hv
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, hM, ← Matrix.mulVec_mulVec] at hv
    have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
    have h0 : Q.map (frobenius C l) *ᵥ v = 0 := by
      have := congrArg (fun x => A⁻¹ *ᵥ x) hv
      simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this
      rwa [← mul_assoc, Matrix.nonsing_inv_mul A hAu, one_mul] at this
    have := hsupp (Set.range a) v (fun i hi => by
      have hi' : i ∈ I := (hmemI i).mpr hi
      have h2 := congrFun h0 i
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hrow i hi', Pi.zero_apply] at h2
      simpa [apply_ite] using h2)
    rwa [← hW] at this
  have hrange : LinearMap.range (Matrix.toLin' M) = N := by
    refine Submodule.eq_of_le_of_finrank_le hrangeN ?_
    have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' M)
    have h2 := Submodule.finrank_add_eq_of_isCompl hc
    have h3 := Submodule.finrank_mono hkerW
    omega
  have hex : ∀ j, ∃ w, Matrix.toLin' M w = P (Pi.single j 1) := fun j => by
    have : P (Pi.single j 1) ∈ LinearMap.range (Matrix.toLin' M) := hrange ▸ hPN _
    exact this
  choose lam hlam using hex
  refine ⟨I, Q, Matrix.of fun k j => lam j k, hYQ, fun v hv => ?_, hrow, hcol, ?_⟩
  · rw [hQv]; exact Submodule.projection_apply_of_mem_left hc ((hmemN v).mpr hv)
  · ext i j
    rw [← hM, Matrix.mul_apply]
    have := congrFun (hlam j) i
    rw [Matrix.toLin'_apply] at this
    rw [hQ, LinearMap.toMatrix'_apply, ← this]
    simp [Matrix.mulVec, dotProduct]

end GlobalTheory
