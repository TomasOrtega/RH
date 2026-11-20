import Mathlib
open Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `l _ F ζ hζ`. Use `set ι := algebraMap (PadicAlgCl l) ℂ_[l] with hι`. Set `F0 : Subfield ℂ_[l]` to `(F.toSubfield.map ι).topologicalClosure`. Establish `hF0 : (F0 : Set ℂ_[l]) = closure (ι '' (F : Set (PadicAlgCl l)))` using `rfl`. Establish `hmemF : ∀ y ∈ F, ι y ∈ F0` using `fun y hy => Subfield.le_topologicalClosure _ ⟨y, hy, rfl⟩`.

Take `⟨r, hr⟩` from `NontriviallyNormedField.non_trivial (α := ℚ_[l])`. Establish `hrmem : ι (algebraMap ℚ_[l] (PadicAlgCl l) r) ∈ F0` using `hmemF _ (F.algebraMap_mem r)`. Establish `hrnorm : ‖ι (algebraMap ℚ_[l] (PadicAlgCl l) r)‖ = ‖r‖`. Rewrite using `[← PadicComplex.coe_eq, PadicComplex.norm_extends]`. Conclude with `PadicAlgCl.norm_extends l r`.

Use `letI : NontriviallyNormedField F0 := { SubfieldClass.toNormedField F0 with non_trivial := ⟨⟨_, hrmem⟩, by show 1 < ‖ι (algebraMap ℚ_[l] (PadicAlgCl l) r)‖`. Rewrite using `[hrnorm]`. Conclude with `hr⟩ }`. Use `haveI : CompleteSpace F0 := (Subfield.isClosed_topologicalClosure _).completeSpace_coe`. Use `letI : NormedSpace F0 ℂ_[l] := { norm_smul_le := fun a b => by show ‖(a : ℂ_[l]) * b‖ ≤ ‖(a : ℂ_[l])‖ * ‖b‖`.

Conclude with `(norm_mul _ _).le }`. Use `set z := ι ζ with hz`. Use `set q := minpoly ℚ_[l] ζ with hq`. Use `set n := q.natDegree with hn`. Set `g : ℚ_[l] →+* F0` to `(ι.comp (algebraMap ℚ_[l] (PadicAlgCl l))).codRestrict F0 (fun r => hmemF _ (F.algebraMap_mem r))`.

Set `Q : F0[X]` to `q.map g`. Establish `hQmonic : Q.Monic` using `(minpoly.monic hζ).map g`. Establish `hQdeg : Q.natDegree = n` using `(minpoly.monic hζ).natDegree_map g`. Establish `hQroot : aeval z Q = 0`. Establish `h1 : (algebraMap F0 ℂ_[l]).comp g = ι.comp (algebraMap ℚ_[l] (PadicAlgCl l))` using `by ext; rfl`.

Rewrite using `[aeval_def, eval₂_map, h1, ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]`. Establish `hQ1 : Q ≠ 1`. Introduce `h`. Use `congrArg natDegree h` as an intermediate fact. Rewrite `this` using `[hQdeg, natDegree_one]`.

Conclude with `(minpoly.natDegree_pos hζ).ne' this`. Set `φ : (Fin n → F0) →ₗ[F0] ℂ_[l]` to `Fintype.linearCombination F0 (fun i : Fin n => z ^ (i : ℕ))`. Establish `hpoly : ∀ p : F0[X], aeval z p ∈ LinearMap.range φ`. Introduce `p`. Rewrite using `[← aeval_modByMonic_eq_self_of_root (p := p) hQroot]`.

Establish `hd : (p %ₘ Q).natDegree < n` using `hQdeg ▸ natDegree_modByMonic_lt p hQmonic hQ1`. Rewrite using `[aeval_eq_sum_range' hd, ← Fin.sum_univ_eq_sum_range (fun i => (p %ₘ Q).coeff i • z ^ i)]`. Conclude with `⟨fun i => (p %ₘ Q).coeff i, by rw [Fintype.linearCombination_apply]⟩`. Establish `hadj : ∀ y ∈ Algebra.adjoin F0 {z}, y ∈ LinearMap.range φ`. Introduce `y hy`.

Rewrite `hy` using `[Algebra.adjoin_singleton_eq_range_aeval]`. Take `⟨p, rfl⟩` from `hy`. Conclude with `hpoly p`. Set `B : Subalgebra ℚ_[l] (PadicAlgCl l)` to `{ (Algebra.adjoin F0 {z}).toSubsemiring.comap ι with algebraMap_mem' := fun r => by show ι (algebraMap ℚ_[l] _ r) ∈ Algebra.adjoin F0 {z}`. Conclude with `(Algebra.adjoin F0 {z}).algebraMap_mem (⟨_, hmemF _ (F.algebraMap_mem r)⟩ : F0) }`.

Establish `hsub : ∀ y ∈ (F ⊔ IntermediateField.adjoin ℚ_[l] {ζ} : IntermediateField ℚ_[l] (PadicAlgCl l)), ι y ∈ Algebra.adjoin F0 {z}`. Introduce `y hy`. Establish `hle : (F ⊔ IntermediateField.adjoin ℚ_[l] {ζ}).toSubalgebra ≤ B`. Rewrite using `[IntermediateField.sup_toSubalgebra_of_isAlgebraic_right]`. Use `sup_le ?_ ?_` and prove the remaining obligations.

Introduce `w hw`. Conclude with `(Algebra.adjoin F0 {z}).algebraMap_mem (⟨_, hmemF w hw⟩ : F0)`. Rewrite using `[IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hζ.isAlgebraic]`. Use `Algebra.adjoin_le (Set.singleton_subset_iff.2 ?_)` and prove the remaining obligations. Conclude with `Algebra.subset_adjoin rfl`.

Conclude with `hle hy`. Establish `hclosed : IsClosed ((LinearMap.range φ : Submodule F0 ℂ_[l]) : Set ℂ_[l])` using `Submodule.closed_of_finiteDimensional _`. Establish `hcl : closure (ι '' ((F ⊔ IntermediateField.adjoin ℚ_[l] {ζ} : IntermediateField ℚ_[l] (PadicAlgCl l)) : Set (PadicAlgCl l))) ⊆ LinearMap.range φ` using `closure_minimal (by rintro _ ⟨y, hy, rfl⟩; exact hadj _ (hsub y hy)) hclosed`. Take `⟨W, hW⟩` from `Submodule.exists_isCompl (LinearMap.ker φ)`. Establish `hψker : LinearMap.ker (φ.domRestrict W) = ⊥`.

Use `LinearMap.ker_eq_bot'.2 fun w hw => ?_` and prove the remaining obligations. Conclude with `Subtype.ext (Submodule.disjoint_def.1 hW.disjoint _ hw w.2)`. Take `⟨C0, -, hC0⟩` from `(φ.domRestrict W).exists_antilipschitzWith hψker`. Use `⟨n, C0, fun x hx hx1 => ?_⟩` and prove the remaining obligations. Take `⟨v, hv⟩` from `hcl hx`.

Take `⟨k, hk, w, hw, hkw⟩` from `Submodule.mem_sup.1 (hW.sup_eq_top ▸ Submodule.mem_top (x := v))`. Establish `hφw : φ w = x`. Rewrite using `[← hv, ← hkw, map_add, LinearMap.mem_ker.1 hk, zero_add]`. Establish `hwn : ‖w‖ ≤ C0`. Establish `h` using `hC0.le_mul_dist ⟨w, hw⟩ 0`.

Rewrite `h` using `[map_zero, dist_zero_right, dist_zero_right]`. Establish `h2 : ‖(φ.domRestrict W) ⟨w, hw⟩‖ = ‖x‖`. Rewrite using `[LinearMap.domRestrict_apply, hφw]`. Rewrite `h` using `[h2]`. Combine the equalities or inequalities in the displayed calculation.

Use `⟨fun i => (w i : ℂ_[l]), fun i => ⟨(w i).2, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `(norm_le_pi_norm w i).trans hwn`. Rewrite using `[← hφw, Fintype.linearCombination_apply]`. Both sides reduce to the same expression.
-/
theorem closure_adjoin_unitBall_coeff_bound : ∀ (l : ℕ) [Fact l.Prime] (F : IntermediateField ℚ_[l] (PadicAlgCl l)) (ζ : PadicAlgCl l), IsIntegral ℚ_[l] ζ → ∃ (n : ℕ) (C : ℝ), ∀ x ∈ closure (algebraMap (PadicAlgCl l) ℂ_[l] '' ((F ⊔ IntermediateField.adjoin ℚ_[l] {ζ} : IntermediateField ℚ_[l] (PadicAlgCl l)) : Set (PadicAlgCl l))), ‖x‖ ≤ 1 → ∃ c : Fin n → ℂ_[l], (∀ i, c i ∈ closure (algebraMap (PadicAlgCl l) ℂ_[l] '' (F : Set (PadicAlgCl l))) ∧ ‖c i‖ ≤ C) ∧ x = ∑ i, c i * (algebraMap (PadicAlgCl l) ℂ_[l] ζ) ^ (i : ℕ) := by
  intro l _ F ζ hζ
  set ι := algebraMap (PadicAlgCl l) ℂ_[l] with hι
  let F0 : Subfield ℂ_[l] := (F.toSubfield.map ι).topologicalClosure
  have hF0 : (F0 : Set ℂ_[l]) = closure (ι '' (F : Set (PadicAlgCl l))) := rfl
  have hmemF : ∀ y ∈ F, ι y ∈ F0 := fun y hy =>
    Subfield.le_topologicalClosure _ ⟨y, hy, rfl⟩
  obtain ⟨r, hr⟩ := NontriviallyNormedField.non_trivial (α := ℚ_[l])
  have hrmem : ι (algebraMap ℚ_[l] (PadicAlgCl l) r) ∈ F0 := hmemF _ (F.algebraMap_mem r)
  have hrnorm : ‖ι (algebraMap ℚ_[l] (PadicAlgCl l) r)‖ = ‖r‖ := by
    rw [← PadicComplex.coe_eq, PadicComplex.norm_extends]
    exact PadicAlgCl.norm_extends l r
  letI : NontriviallyNormedField F0 :=
    { SubfieldClass.toNormedField F0 with
      non_trivial := ⟨⟨_, hrmem⟩, by
        show 1 < ‖ι (algebraMap ℚ_[l] (PadicAlgCl l) r)‖
        rw [hrnorm]; exact hr⟩ }
  haveI : CompleteSpace F0 := (Subfield.isClosed_topologicalClosure _).completeSpace_coe
  letI : NormedSpace F0 ℂ_[l] :=
    { norm_smul_le := fun a b => by
        show ‖(a : ℂ_[l]) * b‖ ≤ ‖(a : ℂ_[l])‖ * ‖b‖
        exact (norm_mul _ _).le }
  set z := ι ζ with hz
  set q := minpoly ℚ_[l] ζ with hq
  set n := q.natDegree with hn
  let g : ℚ_[l] →+* F0 := (ι.comp (algebraMap ℚ_[l] (PadicAlgCl l))).codRestrict F0
    (fun r => hmemF _ (F.algebraMap_mem r))
  let Q : F0[X] := q.map g
  have hQmonic : Q.Monic := (minpoly.monic hζ).map g
  have hQdeg : Q.natDegree = n := (minpoly.monic hζ).natDegree_map g
  have hQroot : aeval z Q = 0 := by
    have h1 : (algebraMap F0 ℂ_[l]).comp g = ι.comp (algebraMap ℚ_[l] (PadicAlgCl l)) := by
      ext; rfl
    rw [aeval_def, eval₂_map, h1, ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]
  have hQ1 : Q ≠ 1 := by
    intro h
    have := congrArg natDegree h
    rw [hQdeg, natDegree_one] at this
    exact (minpoly.natDegree_pos hζ).ne' this
  let φ : (Fin n → F0) →ₗ[F0] ℂ_[l] := Fintype.linearCombination F0 (fun i : Fin n => z ^ (i : ℕ))
  have hpoly : ∀ p : F0[X], aeval z p ∈ LinearMap.range φ := by
    intro p
    rw [← aeval_modByMonic_eq_self_of_root (p := p) hQroot]
    have hd : (p %ₘ Q).natDegree < n := hQdeg ▸ natDegree_modByMonic_lt p hQmonic hQ1
    rw [aeval_eq_sum_range' hd, ← Fin.sum_univ_eq_sum_range (fun i => (p %ₘ Q).coeff i • z ^ i)]
    exact ⟨fun i => (p %ₘ Q).coeff i, by rw [Fintype.linearCombination_apply]⟩
  have hadj : ∀ y ∈ Algebra.adjoin F0 {z}, y ∈ LinearMap.range φ := by
    intro y hy
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨p, rfl⟩ := hy
    exact hpoly p
  let B : Subalgebra ℚ_[l] (PadicAlgCl l) :=
    { (Algebra.adjoin F0 {z}).toSubsemiring.comap ι with
      algebraMap_mem' := fun r => by
        show ι (algebraMap ℚ_[l] _ r) ∈ Algebra.adjoin F0 {z}
        exact (Algebra.adjoin F0 {z}).algebraMap_mem (⟨_, hmemF _ (F.algebraMap_mem r)⟩ : F0) }
  have hsub : ∀ y ∈ (F ⊔ IntermediateField.adjoin ℚ_[l] {ζ} : IntermediateField ℚ_[l] (PadicAlgCl l)),
      ι y ∈ Algebra.adjoin F0 {z} := by
    intro y hy
    have hle : (F ⊔ IntermediateField.adjoin ℚ_[l] {ζ}).toSubalgebra ≤ B := by
      rw [IntermediateField.sup_toSubalgebra_of_isAlgebraic_right]
      refine sup_le ?_ ?_
      · intro w hw
        exact (Algebra.adjoin F0 {z}).algebraMap_mem (⟨_, hmemF w hw⟩ : F0)
      · rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hζ.isAlgebraic]
        refine Algebra.adjoin_le (Set.singleton_subset_iff.2 ?_)
        exact Algebra.subset_adjoin rfl
    exact hle hy
  have hclosed : IsClosed ((LinearMap.range φ : Submodule F0 ℂ_[l]) : Set ℂ_[l]) :=
    Submodule.closed_of_finiteDimensional _
  have hcl : closure (ι '' ((F ⊔ IntermediateField.adjoin ℚ_[l] {ζ} :
      IntermediateField ℚ_[l] (PadicAlgCl l)) : Set (PadicAlgCl l))) ⊆ LinearMap.range φ :=
    closure_minimal (by rintro _ ⟨y, hy, rfl⟩; exact hadj _ (hsub y hy)) hclosed
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.ker φ)
  have hψker : LinearMap.ker (φ.domRestrict W) = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun w hw => ?_
    exact Subtype.ext (Submodule.disjoint_def.1 hW.disjoint _ hw w.2)
  obtain ⟨C0, -, hC0⟩ := (φ.domRestrict W).exists_antilipschitzWith hψker
  refine ⟨n, C0, fun x hx hx1 => ?_⟩
  obtain ⟨v, hv⟩ := hcl hx
  obtain ⟨k, hk, w, hw, hkw⟩ := Submodule.mem_sup.1 (hW.sup_eq_top ▸ Submodule.mem_top (x := v))
  have hφw : φ w = x := by
    rw [← hv, ← hkw, map_add, LinearMap.mem_ker.1 hk, zero_add]
  have hwn : ‖w‖ ≤ C0 := by
    have h := hC0.le_mul_dist ⟨w, hw⟩ 0
    rw [map_zero, dist_zero_right, dist_zero_right] at h
    have h2 : ‖(φ.domRestrict W) ⟨w, hw⟩‖ = ‖x‖ := by
      rw [LinearMap.domRestrict_apply, hφw]
    rw [h2] at h
    calc ‖w‖ = ‖(⟨w, hw⟩ : W)‖ := rfl
      _ ≤ C0 * ‖x‖ := h
      _ ≤ C0 * 1 := mul_le_mul_of_nonneg_left hx1 C0.2
      _ = C0 := mul_one _
  refine ⟨fun i => (w i : ℂ_[l]), fun i => ⟨(w i).2, ?_⟩, ?_⟩
  · exact (norm_le_pi_norm w i).trans hwn
  · rw [← hφw, Fintype.linearCombination_apply]
    rfl

end GlobalTheory
