import Mathlib

open scoped BigOperators

namespace GlobalTheory

open Matrix in

/- English proof (translation)
Introduce `hdet`. Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hdet`. Establish `hall : ∀ X : Matrix (Fin r) (Fin r) k, ∃ Y, Y * B = B * X`. Introduce `X`. Establish `hle : Submodule.span k (Set.range M) ≤ (LinearMap.range (LinearMap.mulRight k B)).comap (LinearMap.mulLeft k B)`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨g, rfl⟩`. Rewrite using `[SetLike.mem_coe, Submodule.mem_comap, LinearMap.mem_range]`. Conclude with `⟨N g, by simp [h g]⟩`. Establish `hX` using `hle (hM ▸ Submodule.mem_top : X ∈ Submodule.span k (Set.range M))`.

Rewrite `hX` using `[Submodule.mem_comap, LinearMap.mem_range]`. Take `⟨Y, hY⟩` from `hX`. Conclude with `⟨Y, by simpa using hY⟩`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c, v c ≠ 0 := by`. Assume the negation of the conclusion as `hne`.

Use `push Not at hne`. Conclude with `hv0 (funext hne)`. Set `X : Matrix (Fin r) (Fin r) k` to `Matrix.of fun a b => if a = j then (if b = c then (v c)⁻¹ else 0) else 0`. Establish `hXv : X *ᵥ v = Pi.single j 1`. Use extensionality with `a`.

Distinguish the cases in `ha : a = j`. Substitute `ha` using the available equality. Simplify using `[X, Matrix.mulVec, dotProduct, hc]`. Simplify using `[X, Matrix.mulVec, dotProduct, ha]`. Take `⟨Y, hY⟩` from `hall X`.

Establish `key : B *ᵥ (X *ᵥ v) = 0`. Rewrite using `[Matrix.mulVec_mulVec, ← hY, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]`. Establish `hi` using `congrFun key i`. Rewrite `hi` using `[hXv]`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply] at hi`.

Conclude with `hB hi`.
-/
theorem det_ne_zero_of_intertwines_of_span_eq_top {k : Type} [Field k] {G : Type} {r : ℕ}
    (M N : G → Matrix (Fin r) (Fin r) k) (hM : Submodule.span k (Set.range M) = ⊤)
    (B : Matrix (Fin r) (Fin r) k) (i j : Fin r) (hB : B i j ≠ 0)
    (h : ∀ g, N g * B = B * M g) : B.det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hall : ∀ X : Matrix (Fin r) (Fin r) k, ∃ Y, Y * B = B * X := by
    intro X
    have hle : Submodule.span k (Set.range M) ≤
        (LinearMap.range (LinearMap.mulRight k B)).comap (LinearMap.mulLeft k B) := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mem_range]
      exact ⟨N g, by simp [h g]⟩
    have hX := hle (hM ▸ Submodule.mem_top : X ∈ Submodule.span k (Set.range M))
    rw [Submodule.mem_comap, LinearMap.mem_range] at hX
    obtain ⟨Y, hY⟩ := hX
    exact ⟨Y, by simpa using hY⟩
  obtain ⟨c, hc⟩ : ∃ c, v c ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hv0 (funext hne)
  let X : Matrix (Fin r) (Fin r) k :=
    Matrix.of fun a b => if a = j then (if b = c then (v c)⁻¹ else 0) else 0
  have hXv : X *ᵥ v = Pi.single j 1 := by
    ext a
    by_cases ha : a = j
    · subst ha
      simp [X, Matrix.mulVec, dotProduct, hc]
    · simp [X, Matrix.mulVec, dotProduct, ha]
  obtain ⟨Y, hY⟩ := hall X
  have key : B *ᵥ (X *ᵥ v) = 0 := by
    rw [Matrix.mulVec_mulVec, ← hY, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  have hi := congrFun key i
  rw [hXv] at hi
  simp [Matrix.mulVec, dotProduct, Pi.single_apply] at hi
  exact hB hi

/- English proof (translation)
Introduce `O _ _ _ G _ r ρ ρ' hspan ⟨A, hdet, hA⟩`. Distinguish the cases in `hr : r = 0`. Substitute `hr` using the available equality. Conclude with `⟨1, fun g => Units.ext (Matrix.ext fun a _ => a.elim0)⟩`. Establish `: Nonempty (Fin r)` using `⟨⟨0, Nat.pos_of_ne_zero hr⟩⟩`.

Take `⟨p, -, hp⟩` from `Finset.exists_min_image Finset.univ (fun q : Fin r × Fin r => IsDiscreteValuationRing.addVal O (A q.1 q.2)) Finset.univ_nonempty`. Establish `hdvd : ∀ x y, A p.1 p.2 ∣ A x y` using `fun x y => IsDiscreteValuationRing.addVal_le_iff_dvd.mp (hp (x, y) (Finset.mem_univ _))`. Establish `hd : A p.1 p.2 ≠ 0`. Introduce `h0`. Apply `hdet` to reduce the goal to its premises.

Establish `hA0 : A = 0`. Use extensionality with `x y`. Establish `hxy` using `hdvd x y`. Rewrite `hxy` using `[h0, zero_dvd_iff]`. Simplify using `using hxy`.

Rewrite using `[hA0, Matrix.det_zero]`. Use `choose C hC using hdvd`. Generalize the expression as in `hdd : A p.1 p.2 = d at hC hd`. Establish `hC1 : C p.1 p.2 = 1` using `mul_left_cancel₀ hd (((hC p.1 p.2).symm.trans hdd).trans (mul_one d).symm)`. Establish `hAeq : A = d • Matrix.of C`.

Use extensionality with `x y`. Rewrite using `[Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← hC]`. Establish `hint : ∀ g, (ρ' g : Matrix (Fin r) (Fin r) O) * Matrix.of C = Matrix.of C * (ρ g : Matrix (Fin r) (Fin r) O)`. Introduce `g`. Establish `h1` using `hA g`.

Rewrite `h1` using `[hAeq, Matrix.mul_smul, Matrix.smul_mul]`. Use extensionality with `x y`. Establish `hxy` using `congrFun (congrFun h1 x) y`. Rewrite `hxy` using `[Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]`. Conclude with `mul_left_cancel₀ hd hxy`.

Establish `hB : (Matrix.of C).map (IsLocalRing.residue O) p.1 p.2 ≠ 0`. Rewrite using `[Matrix.map_apply, Matrix.of_apply, hC1, map_one]`. Conclude with `one_ne_zero`. Establish `hdet'` using `det_ne_zero_of_intertwines_of_span_eq_top (fun g => (ρ g : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O)) (fun g => (ρ' g : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O)) hspan ((Matrix.of C).map (IsLocalRing.residue O)) p.1 p.2 hB (fun g => by rw [← Matrix.map_mu …`. Establish `hunit : IsUnit (Matrix.of C).det`.

Assume the negation of the conclusion as `hu`. Apply `hdet'` to reduce the goal to its premises. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `(IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hu)`. Use `⟨((Matrix.isUnit_iff_isUnit_det _).mpr hunit).unit, fun g => ?_⟩` and prove the remaining obligations.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, Units.val_mul, IsUnit.unit_spec, hint g]`.
-/
theorem exists_gl_intertwiner_of_residual_span_eq_top :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (G : Type) [Group G] (r : ℕ) (ρ ρ' : G →* Matrix.GeneralLinearGroup (Fin r) O), Submodule.span (IsLocalRing.ResidueField O) (Set.range fun g => (ρ g : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O)) = ⊤ → (∃ A : Matrix (Fin r) (Fin r) O, A.det ≠ 0 ∧ ∀ g, (ρ' g : Matrix (Fin r) (Fin r) O) * A = A * ρ g) → ∃ U : Matrix.GeneralLinearGroup (Fin r) O, ∀ g, ρ' g * U = U * ρ g := by
  classical
  intro O _ _ _ G _ r ρ ρ' hspan ⟨A, hdet, hA⟩
  by_cases hr : r = 0
  · subst hr
    exact ⟨1, fun g => Units.ext (Matrix.ext fun a _ => a.elim0)⟩
  have : Nonempty (Fin r) := ⟨⟨0, Nat.pos_of_ne_zero hr⟩⟩
  obtain ⟨p, -, hp⟩ := Finset.exists_min_image Finset.univ
    (fun q : Fin r × Fin r => IsDiscreteValuationRing.addVal O (A q.1 q.2)) Finset.univ_nonempty
  have hdvd : ∀ x y, A p.1 p.2 ∣ A x y := fun x y =>
    IsDiscreteValuationRing.addVal_le_iff_dvd.mp (hp (x, y) (Finset.mem_univ _))
  have hd : A p.1 p.2 ≠ 0 := by
    intro h0
    apply hdet
    have hA0 : A = 0 := by
      ext x y
      have hxy := hdvd x y
      rw [h0, zero_dvd_iff] at hxy
      simpa using hxy
    rw [hA0, Matrix.det_zero]
  choose C hC using hdvd
  generalize hdd : A p.1 p.2 = d at hC hd
  have hC1 : C p.1 p.2 = 1 :=
    mul_left_cancel₀ hd (((hC p.1 p.2).symm.trans hdd).trans (mul_one d).symm)
  have hAeq : A = d • Matrix.of C := by
    ext x y
    rw [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← hC]
  have hint : ∀ g, (ρ' g : Matrix (Fin r) (Fin r) O) * Matrix.of C =
      Matrix.of C * (ρ g : Matrix (Fin r) (Fin r) O) := by
    intro g
    have h1 := hA g
    rw [hAeq, Matrix.mul_smul, Matrix.smul_mul] at h1
    ext x y
    have hxy := congrFun (congrFun h1 x) y
    rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul] at hxy
    exact mul_left_cancel₀ hd hxy
  have hB : (Matrix.of C).map (IsLocalRing.residue O) p.1 p.2 ≠ 0 := by
    rw [Matrix.map_apply, Matrix.of_apply, hC1, map_one]
    exact one_ne_zero
  have hdet' := det_ne_zero_of_intertwines_of_span_eq_top
    (fun g => (ρ g : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O))
    (fun g => (ρ' g : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O)) hspan
    ((Matrix.of C).map (IsLocalRing.residue O)) p.1 p.2 hB
    (fun g => by rw [← Matrix.map_mul, ← Matrix.map_mul, hint g])
  have hunit : IsUnit (Matrix.of C).det := by
    by_contra hu
    apply hdet'
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hu)
  refine ⟨((Matrix.isUnit_iff_isUnit_det _).mpr hunit).unit, fun g => ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, IsUnit.unit_spec, hint g]

end GlobalTheory
