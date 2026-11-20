import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.EdgeIndep

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.LatticeSystems Formalism.GradedWeylDivisibility MvPolynomial

section Pos

variable {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {m : ℕ}

/- English proof (translation)
Unfold `colSpan`. Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Use `congr 1`.
-/
theorem fu_colSpan_map {k : ℕ} (γ : GL (Fin k) Kf) (h : Matrix (Fin k) (Fin k) Kf) :
    (colSpan O h).map (nt_phi O γ) = colSpan O ((γ : Matrix (Fin k) (Fin k) Kf) * h) := by
  unfold colSpan
  rw [Submodule.map_span, ← Set.range_comp]
  congr 1

def fuT (γ : GL (Fin (m + 1)) Kf) (lam : Fin (m + 1) → ℤ) (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) :
    MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf :=
  ((γ : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf).det ^ (-(lam (Fin.last m)))) •
    rowAct Kf ((γ⁻¹ : GL (Fin (m + 1)) Kf) : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) F

/- English proof (translation)
Take `⟨G, hG, rfl⟩` from `hF`. Establish `hcomp : (rowAct Kf ((γ : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) * h)) ((rowAct Kf ((γ⁻¹ : GL (Fin (m + 1)) Kf) : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf)) G) = (rowAct Kf h) G`. Establish `h1` using `congrArg (fun φ => φ G) (rowActMul Kf (m + 1) (m + 1) ((γ : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) * h) ((γ⁻¹ : GL (Fin (m + 1)) Kf) : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf))`. Simplify using `only [AlgHom.comp_apply] at h1`. Rewrite using `[h1, ← mul_assoc, Units.inv_mul, one_mul]`.

Use `⟨rowAct Kf ((γ⁻¹ : GL (Fin (m + 1)) Kf) : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) G, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [nablaL] at hG ⊢`. Rewrite `hG`, the goal using `[SetLike.mem_coe, Submodule.mem_comap]`. Simplify `hG` using `only [LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply, hcomp]`. Simplify using `only [fuT, LinearMap.coe_restrictScalars, LinearMap.lsmul_apply, map_smul, smul_smul, Matrix.det_mul, mul_zpow]`.
-/
theorem fu_nablaLTw (γ : GL (Fin (m + 1)) Kf) (lam : Fin (m + 1) → ℤ) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf)
    (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) (hF : F ∈ nablaLTw O Kf m lam h) :
    fuT γ lam F ∈ nablaLTw O Kf m lam ((γ : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) * h) := by
  obtain ⟨G, hG, rfl⟩ := hF
  have hcomp : (rowAct Kf ((γ : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) * h))
      ((rowAct Kf ((γ⁻¹ : GL (Fin (m + 1)) Kf) : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf)) G) = (rowAct Kf h) G := by
    have h1 := congrArg (fun φ => φ G) (rowActMul Kf (m + 1) (m + 1)
      ((γ : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) * h)
      ((γ⁻¹ : GL (Fin (m + 1)) Kf) : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf))
    simp only [AlgHom.comp_apply] at h1
    rw [h1, ← mul_assoc, Units.inv_mul, one_mul]
  refine ⟨rowAct Kf ((γ⁻¹ : GL (Fin (m + 1)) Kf) : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) G, ?_, ?_⟩
  · simp only [nablaL] at hG ⊢
    rw [SetLike.mem_coe, Submodule.mem_comap] at hG ⊢
    simpa only [LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply, hcomp] using hG
  · simp only [fuT, LinearMap.coe_restrictScalars, LinearMap.lsmul_apply, map_smul, smul_smul,
      Matrix.det_mul, mul_zpow]

/- English proof (translation)
Unfold `H0 at hF ⊢`. Rewrite `hF`, the goal using `[if_pos hlam]`. Simplify using `only [Submodule.mem_iInf] at hF ⊢`. Introduce `g hg`. Establish `hid : (nt_phi O ((γ⁻¹ : GL (Fin (m + 1)) Kf))).comp (nt_phi O γ) = LinearMap.id`.

Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Use `show Matrix.mulVec ((γ⁻¹ : GL (Fin (m + 1)) Kf) : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (Matrix.mulVec (γ : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) x) = x`. Rewrite using `[Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]`. Establish `hback : (Λ.map (nt_phi O γ)).map (nt_phi O ((γ⁻¹ : GL (Fin (m + 1)) Kf))) = Λ`. Rewrite using `[← Submodule.map_comp, hid, Submodule.map_id]`.

Establish `hΛ' : Λ = colSpan O (((γ⁻¹ : GL (Fin (m + 1)) Kf) : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) * g)` using `hback.symm.trans (by rw [hg.2, fu_colSpan_map])`. Establish `hdet : IsUnit (((γ⁻¹ : GL (Fin (m + 1)) Kf) : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) * g).det`. Rewrite using `[Matrix.det_mul]`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)).mul hg.1`. Establish `key` using `fu_nablaLTw (O := O) γ lam _ F (hF _ ⟨hdet, hΛ'⟩)`.

Rewrite `key` using `[← mul_assoc, Units.mul_inv, one_mul]`. Then use the resulting hypothesis.
-/
theorem invariant_sections_transport_GL (γ : GL (Fin (m + 1)) Kf) (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam)
    (Λ : Submodule O (Fin (m + 1) → Kf)) (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf)
    (hF : F ∈ H0 O m lam Λ) : fuT γ lam F ∈ H0 O m lam (Λ.map (nt_phi O γ)) := by
  unfold H0 at hF ⊢
  rw [if_pos hlam] at hF ⊢
  simp only [Submodule.mem_iInf] at hF ⊢
  intro g hg
  have hid : (nt_phi O ((γ⁻¹ : GL (Fin (m + 1)) Kf))).comp (nt_phi O γ) = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    show Matrix.mulVec ((γ⁻¹ : GL (Fin (m + 1)) Kf) : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf)
      (Matrix.mulVec (γ : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) x) = x
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hback : (Λ.map (nt_phi O γ)).map (nt_phi O ((γ⁻¹ : GL (Fin (m + 1)) Kf))) = Λ := by
    rw [← Submodule.map_comp, hid, Submodule.map_id]
  have hΛ' : Λ = colSpan O (((γ⁻¹ : GL (Fin (m + 1)) Kf) : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) * g) :=
    hback.symm.trans (by rw [hg.2, fu_colSpan_map])
  have hdet : IsUnit (((γ⁻¹ : GL (Fin (m + 1)) Kf) : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) * g).det := by
    rw [Matrix.det_mul]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)).mul hg.1
  have key := fu_nablaLTw (O := O) γ lam _ F (hF _ ⟨hdet, hΛ'⟩)
  rwa [← mul_assoc, Units.mul_inv, one_mul] at key

end Pos

section Tw

variable {W Qq O Kf : Type} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [Field Kf] [Algebra O Kf] {k : ℕ}

def fuF (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (s : ℕ) : Qq →+* Kf := ι.comp ((σ ^ s : Qq ≃+* Qq) : Qq →+* Qq)

def fuG (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (s : ℕ) (g : GL (Fin k) Qq) : GL (Fin k) Kf :=
  Matrix.GeneralLinearGroup.map (fuF ι σ s) g

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[twistVec, nt_phi, fuG, fuF, Matrix.mulVec, dotProduct, map_sum]`.
-/
theorem fu_twist (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (s : ℕ) (g : GL (Fin k) Qq) (x : Fin k → Qq) :
    twistVec ι σ s (nt_phi W g x) = nt_phi O (fuG ι σ s g) (twistVec ι σ s x) := by
  funext i
  simp [twistVec, nt_phi, fuG, fuF, Matrix.mulVec, dotProduct, map_sum]

/- English proof (translation)
Unfold `extO`. Rewrite using `[Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]`. Use `congr 1`. Conclude with `Set.image_congr fun x _ => fu_twist ι σ s g x`.
-/
theorem fu_extO (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (s : ℕ) (g : GL (Fin k) Qq) (L : Submodule W (Fin k → Qq)) :
    extO O ι σ s (L.map (nt_phi W g)) = (extO O ι σ s L).map (nt_phi O (fuG ι σ s g)) := by
  unfold extO
  rw [Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
  congr 1
  exact Set.image_congr fun x _ => fu_twist ι σ s g x

/- English proof (translation)
Rewrite using `[LeAt, LeAt, Submodule.map_sup, ← fu_extO]`. Use `congr 1`. Rewrite using `[Submodule.map_span]`. Simplify using `only [mapE, Submodule.map_coe, Set.image_image]`. Use `congr 1`.

Use `Set.image_congr fun x _ => ?_` and prove the remaining obligations. Establish `key` using `fun y => fu_twist (W := W) (O := O) ι σ s g y`. Simplify using `only [nt_phi, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] at key ⊢`. Rewrite using `[← Matrix.mulVec_smul (g : Matrix (Fin k) (Fin k) Qq), key, Matrix.mulVec_smul]`.
-/
theorem fu_LeAt (p : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) (s : ℕ) (g : GL (Fin k) Qq) (e : Edge W Qq k) :
    LeAt p ι σ w s (mapE g e) = (LeAt p ι σ w s e).map (nt_phi O (fuG ι σ s g)) := by
  rw [LeAt, LeAt, Submodule.map_sup, ← fu_extO]
  congr 1
  rw [Submodule.map_span]
  simp only [mapE, Submodule.map_coe, Set.image_image]
  congr 1
  refine Set.image_congr fun x _ => ?_
  have key := fun y => fu_twist (W := W) (O := O) ι σ s g y
  simp only [nt_phi, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] at key ⊢
  rw [← Matrix.mulVec_smul (g : Matrix (Fin k) (Fin k) Qq), key, Matrix.mulVec_smul]

end Tw

section Ten

variable {Kf : Type} [Field Kf] {n' m : ℕ}

def fuTT (lam0 : Fin n' → Fin (m + 1) → ℤ) (γ : Fin n' → GL (Fin (m + 1)) Kf) :
    MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf →ₗ[Kf]
      MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf :=
  (∏ s, ((γ s : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf).det ^ (-(lamAt lam0 s (Fin.last m))))) •
    (blockAct Kf (n := m + 1) fun s => (((γ s)⁻¹ : GL (Fin (m + 1)) Kf) : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf)).toLinearMap

/- English proof (translation)
Establish `hle : tensorLat A Kf M ≤ (tensorLat A Kf M').comap ((fuTT lam0 γ).restrictScalars A)`. Unfold `tensorLat`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `Q ⟨F, hF, rfl⟩`. Use `Submodule.subset_span ⟨fun s => fuT (γ s) (lamAt lam0 s) (F s), fun s => h s _ (hF s), ?_⟩` and prove the remaining obligations.

Simplify using `only [LinearMap.coe_restrictScalars, fuTT, fuT, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_prod, ldtensor_blockAct_blockEmb, map_smul]`. Simplify using `only [MvPolynomial.smul_eq_C_mul, Finset.prod_mul_distrib, map_prod]`. Conclude with `hle hP`.
-/
theorem fu_tensor {A : Type} [CommRing A] [Algebra A Kf] (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (γ : Fin n' → GL (Fin (m + 1)) Kf) (M M' : Fin n' → Submodule A (MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf))
    (h : ∀ s F, F ∈ M s → fuT (γ s) (lamAt lam0 s) F ∈ M' s)
    (P : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) (hP : P ∈ tensorLat A Kf M) :
    fuTT lam0 γ P ∈ tensorLat A Kf M' := by
  have hle : tensorLat A Kf M ≤ (tensorLat A Kf M').comap ((fuTT lam0 γ).restrictScalars A) := by
    unfold tensorLat
    rw [Submodule.span_le]
    rintro Q ⟨F, hF, rfl⟩
    refine Submodule.subset_span ⟨fun s => fuT (γ s) (lamAt lam0 s) (F s), fun s => h s _ (hF s), ?_⟩
    simp only [LinearMap.coe_restrictScalars, fuTT, fuT, LinearMap.smul_apply, AlgHom.toLinearMap_apply,
      map_prod, ldtensor_blockAct_blockEmb, map_smul]
    simp only [MvPolynomial.smul_eq_C_mul, Finset.prod_mul_distrib, map_prod]
  exact hle hP

/- English proof (translation)
Establish `hc : (blockAct Kf A).comp (blockAct Kf B) = AlgHom.id Kf (MvPolynomial (Fin n' × Fin k × Fin n) Kf)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨s, a, j⟩`. Simplify using `only [AlgHom.comp_apply, AlgHom.id_apply, blockAct, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Repeatedly rewrite using `[← mul_assoc, ← MvPolynomial.C_mul, ← Finset.sum_mul, ← map_sum, ← Matrix.mul_apply, h s, Matrix.one_apply]`. Simplify using the standard rewrite rules. Conclude with `congrArg (fun φ => φ P) hc`.
-/
theorem fu_block_inv {k n : ℕ} (A B : Fin n' → Matrix (Fin k) (Fin k) Kf) (h : ∀ s, B s * A s = 1)
    (P : MvPolynomial (Fin n' × (Fin k × Fin n)) Kf) : blockAct Kf A (blockAct Kf B P) = P := by
  have hc : (blockAct Kf A).comp (blockAct Kf B) = AlgHom.id Kf (MvPolynomial (Fin n' × Fin k × Fin n) Kf) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨s, a, j⟩
    simp only [AlgHom.comp_apply, AlgHom.id_apply, blockAct, MvPolynomial.aeval_X, map_sum, map_mul,
      MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← MvPolynomial.C_mul, ← Finset.sum_mul, ← map_sum, ← Matrix.mul_apply, h s,
      Matrix.one_apply]
    simp
  exact congrArg (fun φ => φ P) hc

/- English proof (translation)
Simplify using `only [fuTT, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul, smul_smul, inv_inv]`. Rewrite using `[fu_block_inv (fun s => ((γ s : GL (Fin (m + 1)) Kf) : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf)) (fun s => (((γ s)⁻¹ : GL (Fin (m + 1)) Kf) : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf)) (fun s => Units.inv_mul (γ s)), ← Finset.prod_mul_distrib, Finset.prod_eq_one, one_smul]`. Introduce `s _`. Rewrite using `[← mul_zpow, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, one_zpow]`.
-/
theorem fuTT_inv (lam0 : Fin n' → Fin (m + 1) → ℤ) (γ : Fin n' → GL (Fin (m + 1)) Kf)
    (P : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) :
    fuTT lam0 (fun s => (γ s)⁻¹) (fuTT lam0 γ P) = P := by
  simp only [fuTT, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul, smul_smul, inv_inv]
  rw [fu_block_inv (fun s => ((γ s : GL (Fin (m + 1)) Kf) : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf))
    (fun s => (((γ s)⁻¹ : GL (Fin (m + 1)) Kf) : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf))
    (fun s => Units.inv_mul (γ s)), ← Finset.prod_mul_distrib, Finset.prod_eq_one, one_smul]
  intro s _
  rw [← mul_zpow, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, one_zpow]

end Ten

/- English proof (translation)
Establish `hant : ∀ s, Antitone (lamAt lam0 s)`. Introduce `s i j hij`. Unfold `lamAt`. Use `split_ifs`. Conclude with `hDom s hij`.

Simplify using `only [neg_le_neg_iff]`. Conclude with `hDom s (Fin.rev_le_rev.mpr hij)`. Unfold `Hten`. Prove the components needed by the constructor for the conclusion. Introduce `hP`.

Use `fu_tensor lam0 γ _ _ (fun s F hF => ?_) P hP` and prove the remaining obligations. Use `beta_reduce at hF ⊢`. Rewrite using `[hΛ s]`. Conclude with `invariant_sections_transport_GL (γ s) _ (hant s) (Λ s) F hF`. Introduce `hP`.

Establish `hback : ∀ s, (Λ' s).map (nt_phi O (((γ s)⁻¹ : GL (Fin (m + 1)) Kf))) = Λ s`. Introduce `s`. Rewrite using `[hΛ s, ← Submodule.map_comp]`. Use `Submodule.map_id (Λ s)` and compare the differences between its conclusion and the goal. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations.

Use `show Matrix.mulVec (((γ s)⁻¹ : GL (Fin (m + 1)) Kf) : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (Matrix.mulVec (γ s : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) x) = x`. Rewrite using `[Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]`. Establish `key` using `fu_tensor lam0 (fun s => (γ s)⁻¹) (fun s => H0 O m (lamAt lam0 s) (Λ' s)) (fun s => H0 O m (lamAt lam0 s) (Λ s)) (fun s F hF => ?_) _ hP`. Rewrite `key` using `[fuTT_inv]`. Then use the resulting hypothesis. Use `beta_reduce at hF ⊢`.

Rewrite using `[← hback s]`. Conclude with `invariant_sections_transport_GL ((γ s)⁻¹) _ (hant s) (Λ' s) F hF`.
-/
theorem fu_Hten {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (hDom : IsDominant lam0) (γ : Fin n' → GL (Fin (m + 1)) Kf) (Λ Λ' : Fin n' → Submodule O (Fin (m + 1) → Kf))
    (hΛ : ∀ s, Λ' s = (Λ s).map (nt_phi O (γ s))) (P : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) :
    P ∈ Hten O lam0 Λ ↔ fuTT lam0 γ P ∈ Hten O lam0 Λ' := by
  have hant : ∀ s, Antitone (lamAt lam0 s) := by
    intro s i j hij
    unfold lamAt
    split_ifs
    · exact hDom s hij
    · simp only [neg_le_neg_iff]
      exact hDom s (Fin.rev_le_rev.mpr hij)
  unfold Hten
  constructor
  · intro hP
    refine fu_tensor lam0 γ _ _ (fun s F hF => ?_) P hP
    beta_reduce at hF ⊢
    rw [hΛ s]
    exact invariant_sections_transport_GL (γ s) _ (hant s) (Λ s) F hF
  · intro hP
    have hback : ∀ s, (Λ' s).map (nt_phi O (((γ s)⁻¹ : GL (Fin (m + 1)) Kf))) = Λ s := by
      intro s
      rw [hΛ s, ← Submodule.map_comp]
      convert Submodule.map_id (Λ s)
      refine LinearMap.ext fun x => ?_
      show Matrix.mulVec (((γ s)⁻¹ : GL (Fin (m + 1)) Kf) : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf)
        (Matrix.mulVec (γ s : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) x) = x
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    have key := fu_tensor lam0 (fun s => (γ s)⁻¹) (fun s => H0 O m (lamAt lam0 s) (Λ' s))
      (fun s => H0 O m (lamAt lam0 s) (Λ s)) (fun s F hF => ?_) _ hP
    · rwa [fuTT_inv] at key
    · beta_reduce at hF ⊢
      rw [← hback s]
      exact invariant_sections_transport_GL ((γ s)⁻¹) _ (hant s) (Λ' s) F hF

/- English proof (translation)
Introduce `p n' R m lam0 hDom g`. Establish `hanti` using `kp_lamAt_antitone lam0 hDom`. Establish `hV : ∀ (γ : Fin n' → GL (Fin (m + 1)) R.Kf), ∀ P ∈ Vsp R.Kf lam0, fuTT lam0 γ P ∈ Vsp R.Kf lam0`. Introduce `γ P hP`. Use `fu_tensor lam0 γ _ _ (fun s F hF => ?_) P hP` and prove the remaining obligations.

Rewrite `hF`, the goal using `[if_pos (hanti s)]`. Conclude with `Submodule.smul_mem _ _ (dualWeylRowStable R.Kf _ _ _ _ F hF)`. Set `γ : Fin n' → GL (Fin (m + 1)) R.Kf` to `fun s => fuG R.ι R.σ s.val g`. Set `T : Vsp R.Kf lam0 ≃ₗ[R.Kf] Vsp R.Kf lam0` to `LinearEquiv.ofLinearMap ((fuTT lam0 γ).restrict (hV γ)) ((fuTT lam0 fun s => (γ s)⁻¹).restrict (hV _)) (by`. Use extensionality with `x`.

Use `fuTT_inv lam0 (fun s => (γ s)⁻¹) (x : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R.Kf)` as an intermediate fact. Simplify using `only [inv_inv] at this`. Conclude with `congrArg _ this)`. Use the proof step `(by`. Use extensionality with `x`.

Conclude with `congrArg _ (fuTT_inv lam0 γ (x : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R.Kf)))`. Use `⟨T, fun L _ x => ?_, fun e _ x => ?_⟩` and prove the remaining obligations. Conclude with `fu_Hten lam0 hDom γ _ _ (fun s => fu_extO R.ι R.σ s.val g L) _`. Conclude with `fu_Hten lam0 hDom γ _ _ (fun s => fu_LeAt p R.ι R.σ R.w s.val g e) _`.
-/
theorem restFunct : RestFunct := by
  intro p n' R m lam0 hDom g
  have hanti := kp_lamAt_antitone lam0 hDom
  have hV : ∀ (γ : Fin n' → GL (Fin (m + 1)) R.Kf), ∀ P ∈ Vsp R.Kf lam0, fuTT lam0 γ P ∈ Vsp R.Kf lam0 := by
    intro γ P hP
    refine fu_tensor lam0 γ _ _ (fun s F hF => ?_) P hP
    rw [if_pos (hanti s)] at hF ⊢
    exact Submodule.smul_mem _ _ (dualWeylRowStable R.Kf _ _ _ _ F hF)
  let γ : Fin n' → GL (Fin (m + 1)) R.Kf := fun s => fuG R.ι R.σ s.val g
  let T : Vsp R.Kf lam0 ≃ₗ[R.Kf] Vsp R.Kf lam0 :=
    LinearEquiv.ofLinearMap ((fuTT lam0 γ).restrict (hV γ)) ((fuTT lam0 fun s => (γ s)⁻¹).restrict (hV _))
      (by
        ext x
        have := fuTT_inv lam0 (fun s => (γ s)⁻¹) (x : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R.Kf)
        simp only [inv_inv] at this
        exact congrArg _ this)
      (by
        ext x
        exact congrArg _ (fuTT_inv lam0 γ (x : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R.Kf)))
  refine ⟨T, fun L _ x => ?_, fun e _ x => ?_⟩
  · exact fu_Hten lam0 hDom γ _ _ (fun s => fu_extO R.ι R.σ s.val g L) _
  · exact fu_Hten lam0 hDom γ _ _ (fun s => fu_LeAt p R.ι R.σ R.w s.val g e) _

end Formalism.MainNotions.flipOneThree.Pf

end
