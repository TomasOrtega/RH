import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open Matrix Module ReciprocityTheory.ChartRestriction.G.Geo

variable {D : ℕ}

/- English proof (translation)
Rewrite using `[← Finset.powerset_univ, ← Finset.insert_erase (Finset.mem_univ a), Finset.sum_powerset_insert (Finset.notMem_erase a _), ← Finset.sum_add_distrib]`. Use `Finset.sum_eq_zero fun T hT => ?_` and prove the remaining obligations. Establish `haT : a ∉ T` using `fun h => Finset.notMem_erase a _ (Finset.mem_powerset.mp hT h)`. Establish `hlt : T.card < D`. Use `Finset.card_le_card (Finset.mem_powerset.mp hT)` as an intermediate fact.

Rewrite `this` using `[Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]`. Establish `: 0 < D` using `Fin.pos a`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Finset.card_insert_of_notMem haT]`. Establish `hD : D - T.card = (D - (T.card + 1)) + 1` using `by omega`.

Distinguish the cases in `h : p T`. Rewrite using `[if_pos h, if_pos ((hp T).mpr h), hD, pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg h, if_neg fun h' => h ((hp T).mp h')]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_neg_one_pow_superset_eq_zero (p : Finset (Fin D) → Prop) [DecidablePred p] (a : Fin D)
    (hp : ∀ T, p (insert a T) ↔ p T) (X : ℂ) :
    ∑ T : Finset (Fin D), (-1 : ℂ) ^ (D - T.card) * (if p T then X else 0) = 0 := by
  rw [← Finset.powerset_univ, ← Finset.insert_erase (Finset.mem_univ a),
    Finset.sum_powerset_insert (Finset.notMem_erase a _), ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun T hT => ?_
  have haT : a ∉ T := fun h => Finset.notMem_erase a _ (Finset.mem_powerset.mp hT h)
  have hlt : T.card < D := by
    have := Finset.card_le_card (Finset.mem_powerset.mp hT)
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin] at this
    have : 0 < D := Fin.pos a
    omega
  rw [Finset.card_insert_of_notMem haT]
  have hD : D - T.card = (D - (T.card + 1)) + 1 := by omega
  by_cases h : p T
  · rw [if_pos h, if_pos ((hp T).mpr h), hD, pow_succ]
    ring
  · rw [if_neg h, if_neg fun h' => h ((hp T).mp h')]
    ring

/- English proof (translation)
Unfold `mixedDisc`. Use `mul_eq_zero_of_right _ ?_` and prove the remaining obligations. Establish `hdet : ∀ T : Finset (Fin D), (∑ k ∈ T, B k).det = ∑ σ : Equiv.Perm (Fin D), ∑ f : Fin D → Fin D, (if ∀ i, f i ∈ T then (Equiv.Perm.sign σ : ℂ) * ∏ i, B (f i) (σ i) i else 0)`. Introduce `T`. Rewrite using `[Matrix.det_apply]`.

Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.sum_apply]`. Rewrite using `[Finset.prod_univ_sum, Units.smul_def, zsmul_eq_mul, Finset.mul_sum]`. Establish `hpi : Fintype.piFinset (fun _ : Fin D => T) = Finset.univ.filter (fun f : Fin D → Fin D => ∀ i, f i ∈ T)`. Use extensionality with `f`.

Simplify using `[Fintype.mem_piFinset]`. Rewrite using `[hpi, Finset.sum_filter]`. Repeatedly rewrite using `[hdet, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_eq_zero fun σ _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_eq_zero fun f _ => ?_` and prove the remaining obligations. Distinguish the cases in `hf : Function.Surjective f`. Establish `hbij : Function.Bijective f` using `⟨Finite.injective_iff_surjective.mpr hf, hf⟩`. Establish `hpre : (S.preimage f hbij.1.injOn).card = S.card`.

Rewrite using `[Finset.card_preimage]`. Use `congr 1`. Conclude with `Finset.filter_true_of_mem fun x _ => hf x`. Take `⟨i, hi⟩` from `Finset.inter_nonempty_of_card_lt_card_add_card (Finset.subset_univ C) (Finset.subset_univ (S.preimage f hbij.1.injOn)) (by rw [hpre, Finset.card_univ, Fintype.card_fin]; exact hcard)`. Rewrite `hi` using `[Finset.mem_inter, Finset.mem_preimage]`.

Establish `h0 : ∏ i, B (f i) (σ i) i = 0` using `Finset.prod_eq_zero (Finset.mem_univ i) (hB _ hi.2 _ hi.1 _)`. Use `Finset.sum_eq_zero fun T _ => ?_` and prove the remaining obligations. Simplify using `[h0]`. Take `⟨a, ha⟩` from `not_forall.mp hf push Not at ha`. Use `sum_neg_one_pow_superset_eq_zero (fun T => ∀ i, f i ∈ T) a (fun T => ⟨fun h i => (Finset.mem_insert.mp (h i)).resolve_left (ha i), fun h i => Finset.mem_insert_of_mem (h i)⟩) ((Equiv.Perm.sign σ : ℂ) * ∏ i, B (f i) (σ i) i)` as an intermediate fact.

Conclude with `this`.
-/
theorem mixedDisc_eq_zero_of_cols (B : Fin D → Matrix (Fin D) (Fin D) ℂ) (S C : Finset (Fin D))
    (hcard : D < C.card + S.card) (hB : ∀ k ∈ S, ∀ j ∈ C, ∀ i, B k i j = 0) : mixedDisc B = 0 := by
  classical
  unfold mixedDisc
  refine mul_eq_zero_of_right _ ?_
  have hdet : ∀ T : Finset (Fin D), (∑ k ∈ T, B k).det = ∑ σ : Equiv.Perm (Fin D), ∑ f : Fin D → Fin D,
      (if ∀ i, f i ∈ T then (Equiv.Perm.sign σ : ℂ) * ∏ i, B (f i) (σ i) i else 0) := by
    intro T
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Matrix.sum_apply]
    rw [Finset.prod_univ_sum, Units.smul_def, zsmul_eq_mul, Finset.mul_sum]
    have hpi : Fintype.piFinset (fun _ : Fin D => T) = Finset.univ.filter (fun f : Fin D → Fin D => ∀ i, f i ∈ T) := by
      ext f; simp [Fintype.mem_piFinset]
    rw [hpi, Finset.sum_filter]
  simp_rw [hdet, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun σ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun f _ => ?_
  by_cases hf : Function.Surjective f
  · have hbij : Function.Bijective f := ⟨Finite.injective_iff_surjective.mpr hf, hf⟩
    have hpre : (S.preimage f hbij.1.injOn).card = S.card := by
      rw [Finset.card_preimage]
      congr 1
      exact Finset.filter_true_of_mem fun x _ => hf x
    obtain ⟨i, hi⟩ := Finset.inter_nonempty_of_card_lt_card_add_card (Finset.subset_univ C)
      (Finset.subset_univ (S.preimage f hbij.1.injOn)) (by rw [hpre, Finset.card_univ, Fintype.card_fin]; exact hcard)
    rw [Finset.mem_inter, Finset.mem_preimage] at hi
    have h0 : ∏ i, B (f i) (σ i) i = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (hB _ hi.2 _ hi.1 _)
    refine Finset.sum_eq_zero fun T _ => ?_
    simp [h0]
  · obtain ⟨a, ha⟩ := not_forall.mp hf
    push Not at ha
    have := sum_neg_one_pow_superset_eq_zero (fun T => ∀ i, f i ∈ T) a
      (fun T => ⟨fun h i => (Finset.mem_insert.mp (h i)).resolve_left (ha i), fun h i => Finset.mem_insert_of_mem (h i)⟩)
      ((Equiv.Perm.sign σ : ℂ) * ∏ i, B (f i) (σ i) i)
    exact this

/- English proof (translation)
Unfold `mixedDisc`. Repeatedly rewrite using `[← Finset.sum_mul, Matrix.det_mul, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun T _ => by ring` and prove the remaining obligations.
-/
theorem mixedDisc_mul_right (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (P : Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (fun k => A k * P) = mixedDisc A * P.det := by
  unfold mixedDisc
  simp_rw [← Finset.sum_mul, Matrix.det_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun T _ => by ring

/- English proof (translation)
Unfold `mixedDisc`. Rewrite using `[map_mul, map_sum]`. Use `congr 1`. Simplify using the standard rewrite rules. Use `Finset.sum_congr rfl fun T _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, map_pow, map_neg, map_one, RingHom.map_det]`. Use `congr 2`. Use extensionality with `i j`. Simplify using `[Matrix.sum_apply]`.
-/
theorem mixedDisc_map_star (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (fun k => (A k).map (starRingEnd ℂ)) = starRingEnd ℂ (mixedDisc A) := by
  unfold mixedDisc
  rw [map_mul, map_sum]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun T _ => ?_
    rw [map_mul, map_pow, map_neg, map_one, RingHom.map_det]
    congr 2
    ext i j
    simp [Matrix.sum_apply]

/- English proof (translation)
Take `⟨U, hU⟩` from `Submodule.exists_isCompl V`. Use `set b0 := ((Module.finBasis ℂ V).prod (Module.finBasis ℂ U)).map (Submodule.prodEquivOfIsCompl V U hU) with hb0`. Establish `hcardι : Fintype.card (Fin (Module.finrank ℂ V) ⊕ Fin (Module.finrank ℂ U)) = D`. Rewrite using `[← Module.finrank_eq_card_basis b0, Module.finrank_fin_fun]`. Use `set e := Fintype.equivFinOfCardEq hcardι`.

Use `set b := b0.reindex e`. Establish `hbV : ∀ i, b (e (Sum.inl i)) ∈ V`. Introduce `i`. Simplify using `[b, hb0, Basis.reindex_apply, Basis.map_apply, Basis.prod_apply]`. Use `set P : Matrix (Fin D) (Fin D) ℂ := (Pi.basisFun ℂ (Fin D)).toMatrix b`.

Establish `hP : IsUnit P.det`. Rewrite using `[← Basis.det_apply]`. Conclude with `(Pi.basisFun ℂ (Fin D)).isUnit_det b`. Use `set C := Finset.univ.image fun i => e (Sum.inl i)`. Establish `hC : C.card = Module.finrank ℂ V`.

Rewrite using `[Finset.card_image_of_injective (f := fun i => e (Sum.inl i)) _ (fun x y h => Sum.inl_injective (e.injective h)), Finset.card_univ, Fintype.card_fin]`. Establish `hcol : ∀ k ∈ S, ∀ j ∈ C, ∀ i, (A k * P) i j = 0`. Introduce `k hk j hj i`. Take `⟨l, -, rfl⟩` from `Finset.mem_image.mp hj`. Establish `h` using `congrFun (hA k hk _ (hbV l)) i`.

Simplify `h` using `[P, Matrix.mul_apply, Matrix.mulVec, dotProduct, Basis.toMatrix_apply]`. Establish `h` using `mixedDisc_eq_zero_of_cols (fun k => A k * P) S C (by rw [hC]; exact hdim) hcol`. Rewrite `h` using `[mixedDisc_mul_right]`. Conclude with `(mul_eq_zero.mp h).resolve_right hP.ne_zero`.
-/
theorem mixedDisc_eq_zero_of_ker (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (V : Submodule ℂ (Fin D → ℂ))
    (S : Finset (Fin D)) (hdim : D < Module.finrank ℂ V + S.card) (hA : ∀ k ∈ S, ∀ x ∈ V, A k *ᵥ x = 0) :
    mixedDisc A = 0 := by
  classical
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl V
  set b0 := ((Module.finBasis ℂ V).prod (Module.finBasis ℂ U)).map (Submodule.prodEquivOfIsCompl V U hU) with hb0
  have hcardι : Fintype.card (Fin (Module.finrank ℂ V) ⊕ Fin (Module.finrank ℂ U)) = D := by
    rw [← Module.finrank_eq_card_basis b0, Module.finrank_fin_fun]
  set e := Fintype.equivFinOfCardEq hcardι
  set b := b0.reindex e
  have hbV : ∀ i, b (e (Sum.inl i)) ∈ V := by
    intro i
    simp [b, hb0, Basis.reindex_apply, Basis.map_apply, Basis.prod_apply]
  set P : Matrix (Fin D) (Fin D) ℂ := (Pi.basisFun ℂ (Fin D)).toMatrix b
  have hP : IsUnit P.det := by
    rw [← Basis.det_apply]
    exact (Pi.basisFun ℂ (Fin D)).isUnit_det b
  set C := Finset.univ.image fun i => e (Sum.inl i)
  have hC : C.card = Module.finrank ℂ V := by
    rw [Finset.card_image_of_injective (f := fun i => e (Sum.inl i)) _
      (fun x y h => Sum.inl_injective (e.injective h)), Finset.card_univ, Fintype.card_fin]
  have hcol : ∀ k ∈ S, ∀ j ∈ C, ∀ i, (A k * P) i j = 0 := by
    intro k hk j hj i
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hj
    have h := congrFun (hA k hk _ (hbV l)) i
    simpa [P, Matrix.mul_apply, Matrix.mulVec, dotProduct, Basis.toMatrix_apply] using h
  have h := mixedDisc_eq_zero_of_cols (fun k => A k * P) S C (by rw [hC]; exact hdim) hcol
  rw [mixedDisc_mul_right] at h
  exact (mul_eq_zero.mp h).resolve_right hP.ne_zero

end GroundTheory.Heights₂.Heights.Inter
