import ReciprocityTheory.DualLattices.ProdPowUnitVectorVal

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up.UnitVectorPowers

open ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}

section Res

variable [IsLocalRing R] [CharP (IsLocalRing.ResidueField R) p]

def Lk (D : Lifts H U X) : Matrix (Ix g) (Ix g) (IsLocalRing.ResidueField R) :=
  D.Λ.map (IsLocalRing.residue R)

def Mk (D : Lifts H U X) : Matrix (Ix g) (Ix g) (IsLocalRing.ResidueField R) :=
  (Lk D).map (fun a => a ^ p) * (Lk D)⁻¹

/- English proof (translation)
Unfold `Lk`. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `D.Λ_det.map _`.
-/
theorem Lk_det (D : Lifts H U X) : IsUnit (Lk D).det := by
  unfold Lk
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact D.Λ_det.map _

/- English proof (translation)
Establish `hinv : (Lk D)⁻¹ * Lk D = 1` using `Matrix.nonsing_inv_mul _ (Lk_det D)`. Establish `hxc : ∀ i, (xc (IsLocalRing.ResidueField R) i y) ^ p = xc (IsLocalRing.ResidueField R) i y`. Introduce `i`. Simplify using `only [xc]`. Rewrite using `[← map_pow, ZMod.pow_card]`.

Establish `hR : ∑ l, Mk D j l * lam (Lk D) l y = ((Mk D * Lk D) *ᵥ fun i => xc (IsLocalRing.ResidueField R) i y) j`. Rewrite using `[← Matrix.mulVec_mulVec]`. Simplify using `[Matrix.mulVec, dotProduct, lam]`. Rewrite using `[hR]`. Unfold `Mk`.

Rewrite using `[Matrix.mul_assoc, hinv, Matrix.mul_one]`. Simplify using `only [lam, Matrix.mulVec, dotProduct, Matrix.map_apply]`. Rewrite using `[sum_pow_char]`. Simplify using `only [mul_pow, hxc]`.
-/
theorem lam_p (D : Lifts H U X) (j : Ix g) (y : Nb p g) :
    lam (Lk D) j y ^ p = ∑ l, Mk D j l * lam (Lk D) l y := by
  have hinv : (Lk D)⁻¹ * Lk D = 1 := Matrix.nonsing_inv_mul _ (Lk_det D)
  have hxc : ∀ i, (xc (IsLocalRing.ResidueField R) i y) ^ p = xc (IsLocalRing.ResidueField R) i y := by
    intro i
    simp only [xc]
    rw [← map_pow, ZMod.pow_card]
  have hR : ∑ l, Mk D j l * lam (Lk D) l y =
      ((Mk D * Lk D) *ᵥ fun i => xc (IsLocalRing.ResidueField R) i y) j := by
    rw [← Matrix.mulVec_mulVec]
    simp [Matrix.mulVec, dotProduct, lam]
  rw [hR]
  unfold Mk
  rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
  simp only [lam, Matrix.mulVec, dotProduct, Matrix.map_apply]
  rw [sum_pow_char]
  simp only [mul_pow, hxc]

/- English proof (translation)
Simplify using `only [monF, e1]`. Rewrite using `[Finset.prod_eq_single l]`. Simplify using `[ZMod.val_one]`. Introduce `b _ hb`. Simplify using `[Pi.single_apply, hb]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ l) h`.
-/
theorem formMonomial_unitVector (D : Lifts H U X) (l : Ix g) (y : Nb p g) :
    monF (Lk D) (e1 l) y = lam (Lk D) l y := by
  simp only [monF, e1]
  rw [Finset.prod_eq_single l]
  · simp [ZMod.val_one]
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ l) h

/- English proof (translation)
Use extensionality with `y α`. Simplify using `[MuR, monF, Lk, residue_uR hv]`.
-/
theorem MuR_map (hv : v.Integers R) (D : Lifts H U X) :
    (MuR hv D).map (IsLocalRing.residue R) = Matrix.of fun (y α : Nb p g) => monF (Lk D) α y := by
  ext y α
  simp [MuR, monF, Lk, residue_uR hv]

/- English proof (translation)
Establish `hMu` using `MuR_mulVec_bR hv hp1 D j`. Establish `hdet : IsUnit ((MuR hv D).map (IsLocalRing.residue R)).det`. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `(isUnit_det_MuR hv hp1 D).map _`. Set `c : Nb p g → IsLocalRing.ResidueField R` to `fun α => ∑ l', if α = e1 l' then Mk D j l' else 0`.

Establish `hvecres : ((MuR hv D).map (IsLocalRing.residue R)) *ᵥ (fun α => IsLocalRing.residue R (bR hv D j α)) = ((MuR hv D).map (IsLocalRing.residue R)) *ᵥ c`. Use function extensionality and compare the values at `y`. Establish `h1 : ((MuR hv D).map (IsLocalRing.residue R) *ᵥ fun α => IsLocalRing.residue R (bR hv D j α)) y = IsLocalRing.residue R (hvec hv D j y)`. Rewrite using `[← hMu, RingHom.map_mulVec]`. Both sides reduce to the same expression.

Rewrite using `[h1, hvec, map_pow, residue_uR hv]`. Express the relevant statement in the definitionally equal form `lam (Lk D) j y ^ p = _`. Rewrite using `[lam_p, MuR_map hv D]`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.of_apply, c, Finset.mul_sum, mul_ite, mul_zero]`. Rewrite using `[Finset.sum_comm]`.

Simplify using `only [Finset.sum_ite_eq', Finset.mem_univ, if_true, formMonomial_unitVector]`. Conclude with `Finset.sum_congr rfl fun _ _ => mul_comm _ _`. Establish `hinv` using `Matrix.nonsing_inv_mul _ hdet`. Establish `hinj : (fun α => IsLocalRing.residue R (bR hv D j α)) = c`. Combine the equalities or inequalities in the displayed calculation.

Establish `hc : IsLocalRing.residue R (bR hv D j (e1 l)) = c (e1 l)` using `congrFun hinj (e1 l)`. Rewrite using `[hc]`. Simplify using `only [c]`. Rewrite using `[Finset.sum_eq_single l]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Rewrite using `[if_neg]`. Introduce `h`. Establish `h2` using `congrFun h l`. Simplify using `[e1, Pi.single_apply, Ne.symm hb] at h2`.

Simplify using the standard rewrite rules.
-/
theorem res_bR (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1) (D : Lifts H U X)
    (j l : Ix g) : IsLocalRing.residue R (bR hv D j (e1 l)) = Mk D j l := by
  classical
  have hMu := MuR_mulVec_bR hv hp1 D j
  have hdet : IsUnit ((MuR hv D).map (IsLocalRing.residue R)).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (isUnit_det_MuR hv hp1 D).map _
  let c : Nb p g → IsLocalRing.ResidueField R := fun α => ∑ l', if α = e1 l' then Mk D j l' else 0
  have hvecres : ((MuR hv D).map (IsLocalRing.residue R)) *ᵥ
      (fun α => IsLocalRing.residue R (bR hv D j α)) = ((MuR hv D).map (IsLocalRing.residue R)) *ᵥ c := by
    funext y
    have h1 : ((MuR hv D).map (IsLocalRing.residue R) *ᵥ fun α => IsLocalRing.residue R (bR hv D j α)) y =
        IsLocalRing.residue R (hvec hv D j y) := by
      rw [← hMu, RingHom.map_mulVec]
      rfl
    rw [h1, hvec, map_pow, residue_uR hv]
    change lam (Lk D) j y ^ p = _
    rw [lam_p, MuR_map hv D]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, c, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, formMonomial_unitVector]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hinv := Matrix.nonsing_inv_mul _ hdet
  have hinj : (fun α => IsLocalRing.residue R (bR hv D j α)) = c := by
    calc (fun α => IsLocalRing.residue R (bR hv D j α))
        = (((MuR hv D).map (IsLocalRing.residue R))⁻¹ * (MuR hv D).map (IsLocalRing.residue R)) *ᵥ
            (fun α => IsLocalRing.residue R (bR hv D j α)) := by rw [hinv, Matrix.one_mulVec]
      _ = c := by rw [← Matrix.mulVec_mulVec, hvecres, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hc : IsLocalRing.residue R (bR hv D j (e1 l)) = c (e1 l) := congrFun hinj (e1 l)
  rw [hc]
  simp only [c]
  rw [Finset.sum_eq_single l]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    have h2 := congrFun h l
    simp [e1, Pi.single_apply, Ne.symm hb] at h2
  · simp

/- English proof (translation)
Establish `h0` using `(Lk_det D).ne_zero`. Establish `hfrob : (Lk D).map (fun a => a ^ p) = (frobenius (IsLocalRing.ResidueField R) p).mapMatrix (Lk D)`. Use extensionality with `a b`. Simplify using `[frobenius_def]`. Establish `hdet : ((Lk D).map (fun a => a ^ p)).det = (Lk D).det ^ p`.

Rewrite using `[hfrob, ← RingHom.map_det, frobenius_def]`. Unfold `Mk`. Rewrite using `[Matrix.det_mul, hdet, Matrix.det_nonsing_inv]`. Conclude with `mul_ne_zero (pow_ne_zero _ h0) (by simpa [Ring.inverse_eq_inv] using h0)`.
-/
theorem Mk_det (D : Lifts H U X) : (Mk D).det ≠ 0 := by
  have h0 := (Lk_det D).ne_zero
  have hfrob : (Lk D).map (fun a => a ^ p) =
      (frobenius (IsLocalRing.ResidueField R) p).mapMatrix (Lk D) := by
    ext a b
    simp [frobenius_def]
  have hdet : ((Lk D).map (fun a => a ^ p)).det = (Lk D).det ^ p := by
    rw [hfrob, ← RingHom.map_det, frobenius_def]
  unfold Mk
  rw [Matrix.det_mul, hdet, Matrix.det_nonsing_inv]
  exact mul_ne_zero (pow_ne_zero _ h0) (by simpa [Ring.inverse_eq_inv] using h0)

/- English proof (translation)
Rewrite using `[← res_bR hv hp1 D j l, bR_off hv hp1 D j l hl, map_zero]`.
-/
theorem Mk_off (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1) (D : Lifts H U X)
    (j l : Ix g) (hl : D.κ l ≠ U.φ (D.κ j)) : Mk D j l = 0 := by
  rw [← res_bR hv hp1 D j l, bR_off hv hp1 D j l hl, map_zero]

/- English proof (translation)
Introduce `h0`. Take `⟨w, hw0, hw⟩` from `Matrix.exists_vecMul_eq_zero_iff.mpr h0`. Set `W : Ix g → IsLocalRing.ResidueField R` to `fun j => if hj : D.κ j = i then w ⟨j, hj⟩ else 0`. Apply `Mk_det D` to reduce the goal to its premises. Rewrite using `[← Matrix.exists_vecMul_eq_zero_iff]`.

Use `⟨W, ?_, ?_⟩` and prove the remaining obligations. Introduce `hW`. Apply `hw0` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Establish `h1` using `congrFun hW j.1`.

Simplify `h1` using `[W, j.2]`. Use function extensionality and compare the values at `l`. Simplify using `only [Matrix.vecMul, dotProduct, Pi.zero_apply]`. Distinguish the cases in `hl : D.κ l = U.φ i`. Establish `h1` using `congrFun hw (e.symm ⟨l, hl⟩)`.

Simplify using `only [Matrix.vecMul, dotProduct, Matrix.of_apply, Equiv.apply_symm_apply, Pi.zero_apply] at h1`. Rewrite using `[← Fintype.sum_subtype_add_sum_subtype (fun j => D.κ j = i)]`. Establish `h2 : ∑ j : {j // ¬ D.κ j = i}, W j.1 * Mk D j.1 l = 0` using `Finset.sum_eq_zero fun j _ => by simp [W, j.2]`. Establish `h3 : ∑ j : {j // D.κ j = i}, W j.1 * Mk D j.1 l = ∑ j, w j * Mk D j.1 l` using `Finset.sum_congr rfl fun j _ => by simp [W, j.2]`. Rewrite using `[h2, h3, add_zero]`.

Conclude with `h1`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hj : D.κ j = i`. Rewrite using `[Mk_off hv hp1 D j l (by rw [hj]; exact hl), mul_zero]`. Simplify using `[W, hj]`.
-/
theorem block_det_ne (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1) (D : Lifts H U X)
    (i : Fin U.m) (e : {j // D.κ j = i} ≃ {l // D.κ l = U.φ i}) :
    (Matrix.of fun j l : {j // D.κ j = i} => Mk D j.1 (e l).1).det ≠ 0 := by
  classical
  intro h0
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
  let W : Ix g → IsLocalRing.ResidueField R := fun j => if hj : D.κ j = i then w ⟨j, hj⟩ else 0
  apply Mk_det D
  rw [← Matrix.exists_vecMul_eq_zero_iff]
  refine ⟨W, ?_, ?_⟩
  · intro hW
    apply hw0
    funext j
    have h1 := congrFun hW j.1
    simpa [W, j.2] using h1
  · funext l
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
    by_cases hl : D.κ l = U.φ i
    · have h1 := congrFun hw (e.symm ⟨l, hl⟩)
      simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Equiv.apply_symm_apply,
        Pi.zero_apply] at h1
      rw [← Fintype.sum_subtype_add_sum_subtype (fun j => D.κ j = i)]
      have h2 : ∑ j : {j // ¬ D.κ j = i}, W j.1 * Mk D j.1 l = 0 :=
        Finset.sum_eq_zero fun j _ => by simp [W, j.2]
      have h3 : ∑ j : {j // D.κ j = i}, W j.1 * Mk D j.1 l = ∑ j, w j * Mk D j.1 l :=
        Finset.sum_congr rfl fun j _ => by simp [W, j.2]
      rw [h2, h3, add_zero]
      exact h1
    · refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : D.κ j = i
      · rw [Mk_off hv hp1 D j l (by rw [hj]; exact hl), mul_zero]
      · simp [W, hj]

end Res

end ReciprocityTheory.PGsh.Up.UnitVectorPowers
