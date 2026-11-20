import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentBlockCharPolyEqCharpolyImage

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing Polynomial

namespace GlobalTheory.RootFactor

/- English proof (translation)
Establish `hCH : aeval D (X - C r) * aeval D q = 0`. Rewrite using `[← map_mul, ← h, Matrix.aeval_self_charpoly]`. Take `⟨s, hs⟩ : ∃ s : K[X], q = s * (X - C r) + C (q.eval r)` from `⟨q /ₘ (X - C r), by`. Establish `hmd` using `Polynomial.modByMonic_add_div q (X - C r)`. Rewrite `hmd` using `[Polynomial.modByMonic_X_sub_C_eq_C_eval]`.

Rewrite using `[mul_comm, add_comm]`. Conclude with `hmd.symm⟩`. Use `conv_lhs => arg 1`. Rewrite using `[hs]`. Rewrite using `[map_add, map_mul, aeval_C, add_mul, Matrix.mul_assoc, hCH, Matrix.mul_zero, zero_add, Algebra.smul_def]`.
-/
theorem aeval_sq {K : Type} [Field K] {t : ℕ} (D : Matrix (Fin t) (Fin t) K) (r : K) (q : K[X])
    (h : D.charpoly = (X - C r) * q) : aeval D q * aeval D q = q.eval r • aeval D q := by
  have hCH : aeval D (X - C r) * aeval D q = 0 := by
    rw [← map_mul, ← h, Matrix.aeval_self_charpoly]
  obtain ⟨s, hs⟩ : ∃ s : K[X], q = s * (X - C r) + C (q.eval r) :=
    ⟨q /ₘ (X - C r), by
      have hmd := Polynomial.modByMonic_add_div q (X - C r)
      rw [Polynomial.modByMonic_X_sub_C_eq_C_eval] at hmd
      rw [mul_comm, add_comm]
      exact hmd.symm⟩
  conv_lhs => arg 1; rw [hs]
  rw [map_add, map_mul, aeval_C, add_mul, Matrix.mul_assoc, hCH, Matrix.mul_zero, zero_add,
    Algebra.smul_def]

/- English proof (translation)
Establish `hCH : aeval D (X - C r) * aeval D q = 0`. Rewrite using `[← map_mul, ← h, Matrix.aeval_self_charpoly]`. Establish `hDP : D * aeval D q = r • aeval D q`. Rewrite `hCH` using `[map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.sub_mul, sub_eq_zero, Matrix.smul_mul, Matrix.one_mul]`. Conclude with `hCH`.

Establish `hchar : LinearMap.charpoly (Matrix.toLinAlgEquiv' D) = (X - C r) * q`. Rewrite using `[← h]`. Conclude with `Matrix.charpoly_toLin' D`. Establish `hmult : (LinearMap.charpoly (Matrix.toLinAlgEquiv' D)).rootMultiplicity r = 1`. Rewrite using `[hchar, Polynomial.rootMultiplicity_mul, Polynomial.rootMultiplicity_X_sub_C_self, Polynomial.rootMultiplicity_eq_zero (by simpa [Polynomial.IsRoot] using hq)]`.

Rewrite using `[← h]`. Conclude with `(Matrix.charpoly_monic D).ne_zero`. Establish `hle : LinearMap.range (aeval D q).mulVecLin ≤ Module.End.eigenspace (Matrix.toLinAlgEquiv' D) r`. Introduce and unpack `_ ⟨v, rfl⟩`. Rewrite using `[Module.End.mem_eigenspace_iff, Matrix.toLinAlgEquiv'_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hDP, Matrix.smul_mulVec]`.

Establish `hEig : Module.End.HasEigenvalue (Matrix.toLinAlgEquiv' D) r`. Rewrite using `[Module.End.hasEigenvalue_iff_isRoot_charpoly, hchar]`. Simplify using `[Polynomial.IsRoot]`. Take `⟨v, hv⟩` from `hEig.exists_hasEigenvector`. Establish `hPv : Matrix.mulVec (aeval D q) v = q.eval r • v`.

Rewrite using `[← Matrix.toLinAlgEquiv'_apply, ← Polynomial.aeval_algHom_apply]`. Conclude with `Module.End.aeval_apply_of_hasEigenvector hv`. Use `show Module.finrank K (LinearMap.range (aeval D q).mulVecLin) = 1`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `(Submodule.finrank_mono hle).trans (hmult ▸ LinearMap.finrank_eigenspace_le _ r)`.

Rewrite using `[Nat.one_le_iff_ne_zero]`. Introduce `h0`. Rewrite `h0` using `[Submodule.finrank_eq_zero]`. Establish `hmem : Matrix.mulVec (aeval D q) v ∈ LinearMap.range (aeval D q).mulVecLin` using `⟨v, rfl⟩`. Rewrite `hmem` using `[h0, Submodule.mem_bot, hPv]`.

Conclude with `smul_ne_zero hq hv.2 hmem`.
-/
theorem aeval_rank {K : Type} [Field K] {t : ℕ} (D : Matrix (Fin t) (Fin t) K) (r : K) (q : K[X])
    (h : D.charpoly = (X - C r) * q) (hq : q.eval r ≠ 0) : (aeval D q).rank = 1 := by
  have hCH : aeval D (X - C r) * aeval D q = 0 := by
    rw [← map_mul, ← h, Matrix.aeval_self_charpoly]
  have hDP : D * aeval D q = r • aeval D q := by
    rw [map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.sub_mul,
      sub_eq_zero, Matrix.smul_mul, Matrix.one_mul] at hCH
    exact hCH
  have hchar : LinearMap.charpoly (Matrix.toLinAlgEquiv' D) = (X - C r) * q := by
    rw [← h]; exact Matrix.charpoly_toLin' D
  have hmult : (LinearMap.charpoly (Matrix.toLinAlgEquiv' D)).rootMultiplicity r = 1 := by
    rw [hchar, Polynomial.rootMultiplicity_mul, Polynomial.rootMultiplicity_X_sub_C_self,
      Polynomial.rootMultiplicity_eq_zero (by simpa [Polynomial.IsRoot] using hq)]
    rw [← h]; exact (Matrix.charpoly_monic D).ne_zero
  have hle : LinearMap.range (aeval D q).mulVecLin ≤
      Module.End.eigenspace (Matrix.toLinAlgEquiv' D) r := by
    rintro _ ⟨v, rfl⟩
    rw [Module.End.mem_eigenspace_iff, Matrix.toLinAlgEquiv'_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec, hDP, Matrix.smul_mulVec]
  have hEig : Module.End.HasEigenvalue (Matrix.toLinAlgEquiv' D) r := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, hchar]
    simp [Polynomial.IsRoot]
  obtain ⟨v, hv⟩ := hEig.exists_hasEigenvector
  have hPv : Matrix.mulVec (aeval D q) v = q.eval r • v := by
    rw [← Matrix.toLinAlgEquiv'_apply, ← Polynomial.aeval_algHom_apply]
    exact Module.End.aeval_apply_of_hasEigenvector hv
  show Module.finrank K (LinearMap.range (aeval D q).mulVecLin) = 1
  apply le_antisymm
  · exact (Submodule.finrank_mono hle).trans (hmult ▸ LinearMap.finrank_eigenspace_le _ r)
  · rw [Nat.one_le_iff_ne_zero]
    intro h0
    rw [Submodule.finrank_eq_zero] at h0
    have hmem : Matrix.mulVec (aeval D q) v ∈ LinearMap.range (aeval D q).mulVecLin := ⟨v, rfl⟩
    rw [h0, Submodule.mem_bot, hPv] at hmem
    exact smul_ne_zero hq hv.2 hmem

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons c l ih`. Establish `key : b * (a * D * b - ρ c • (a * b)) = (D - ρ c • 1) * b`. Simplify using `only [Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc, hba, Matrix.one_mul, Matrix.sub_mul, Matrix.smul_mul]`.

Rewrite using `[List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, map_mul, ← Matrix.mul_assoc, key, Matrix.mul_assoc, ih, ← Matrix.mul_assoc]`. Use `congr 2`. Simplify using `[Algebra.algebraMap_eq_smul_one]`.
-/
private theorem aeval_list_prod_X_sub_C_mul_comm {K : Type} [Field K] {n t : ℕ} (a : Matrix (Fin n) (Fin t) K)
    (b : Matrix (Fin t) (Fin n) K) (hba : b * a = 1) (D : Matrix (Fin t) (Fin t) K) (ρ : ℕ → K)
    (l : List ℕ) :
    b * (l.map fun c => a * D * b - ρ c • (a * b)).prod =
      aeval D (l.map fun c => X - C (ρ c)).prod * b := by
  induction l with
  | nil => simp
  | cons c l ih =>
    have key : b * (a * D * b - ρ c • (a * b)) = (D - ρ c • 1) * b := by
      simp only [Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc, hba, Matrix.one_mul,
        Matrix.sub_mul, Matrix.smul_mul]
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, map_mul, ← Matrix.mul_assoc,
      key, Matrix.mul_assoc, ih, ← Matrix.mul_assoc]
    congr 2
    simp [Algebra.algebraMap_eq_smul_one]

/- English proof (translation)
Rewrite using `[Matrix.mul_assoc, aeval_list_prod_X_sub_C_mul_comm a b hba D ρ l, ← Matrix.mul_assoc]`.
-/
theorem prod_eq {K : Type} [Field K] {n t : ℕ} (a : Matrix (Fin n) (Fin t) K) (b : Matrix (Fin t) (Fin n) K)
    (hba : b * a = 1) (D : Matrix (Fin t) (Fin t) K) (ρ : ℕ → K) (l : List ℕ) :
    (a * b) * (l.map fun c => a * D * b - ρ c • (a * b)).prod =
      a * aeval D (l.map fun c => X - C (ρ c)).prod * b := by
  rw [Matrix.mul_assoc, aeval_list_prod_X_sub_C_mul_comm a b hba D ρ l, ← Matrix.mul_assoc]

/- English proof (translation)
Rewrite using `[Finset.prod_eq_multiset_prod]`. Both sides reduce to the same expression.
-/
private theorem prod_Ioc_one_eq_list_range'_prod {M : Type} [CommMonoid M] (f : ℕ → M) (t : ℕ) :
    ∏ c ∈ Finset.Ioc 1 t, f c = ((List.range' 2 (t - 1)).map f).prod := by
  rw [Finset.prod_eq_multiset_prod]
  rfl

/- English proof (translation)
Take `⟨a, b, hba, hab, hM⟩` from `GlobalTheory.BlockCharpoly.blockPol_eq_charpoly e he rfl`. Establish `hX : e * X₀ * e = X₀` using `by rw [h1, h2]`. Establish `hX' : a * (b * X₀ * a) * b = X₀` using `by conv_rhs => rw [← hX, ← hab]`. Simplify using `only [Matrix.mul_assoc]`. Establish `hcp : (b * X₀ * a).charpoly = (X - C (ρ 1)) * ((List.range' 2 (t - 1)).map fun c => X - C (ρ c)).prod`.

Rewrite using `[← hM, hX, ← hP, Finset.Icc_eq_cons_Ioc (by omega : 1 ≤ t), Finset.prod_cons, prod_Ioc_one_eq_list_range'_prod]`. Establish `hev : (((List.range' 2 (t - 1)).map fun c => X - C (ρ c)).prod).eval (ρ 1) = ∏ c ∈ Finset.Ioc 1 t, (ρ 1 - ρ c)`. Rewrite using `[prod_Ioc_one_eq_list_range'_prod, Polynomial.eval_list_prod, List.map_map]`. Use `congr 1`. Apply `List.map_congr_left` to reduce the goal to its premises.

Introduce `c _`. Simplify using the standard rewrite rules. Establish `hne : (((List.range' 2 (t - 1)).map fun c => X - C (ρ c)).prod).eval (ρ 1) ≠ 0`. Rewrite using `[hev, Finset.prod_ne_zero_iff]`. Introduce `c hc hzero`.

Rewrite `hc` using `[Finset.mem_Ioc]`. Use `hρ (by simp only [Finset.coe_Icc, Set.mem_Icc]; omega) (by simp only [Finset.coe_Icc, Set.mem_Icc]; omega) (sub_eq_zero.mp hzero)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `heE : e * ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod = ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod`. Take `⟨k, hk⟩ : ∃ k, t - 1 = k + 1` from `⟨t - 2, by omega⟩`.

Rewrite using `[hk, List.range'_succ, List.map_cons, List.prod_cons, ← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_smul, h1, he]`. Establish `hE : ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod = a * aeval (b * X₀ * a) ((List.range' 2 (t - 1)).map fun c => X - C (ρ c)).prod * b`. Rewrite using `[← heE, ← prod_eq a b hba (b * X₀ * a) ρ, hab]`. Use `congr 2`. Apply `List.map_congr_left` to reduce the goal to its premises.

Introduce `c _`. Rewrite using `[hX']`. Establish `hsq` using `aeval_sq (b * X₀ * a) (ρ 1) _ hcp`. Establish `hrk` using `aeval_rank (b * X₀ * a) (ρ 1) _ hcp hne`. Rewrite using `[hE, ← hev]`.

Generalize the expression as in `aeval (b * X₀ * a) ((List.range' 2 (t - 1)).map fun c => X - C (ρ c)).prod = R at hsq hrk`. Prove the components needed by the constructor for the conclusion. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)).trans hrk.le`. Establish `hR : R = b * (a * R * b) * a`.

Simplify using `only [← Matrix.mul_assoc, hba, Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc, hba, Matrix.mul_one]`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[← Matrix.mul_assoc b a, hba, Matrix.one_mul]`. Use `_ = _ := by rw [hsq, Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem field_case {K : Type} [Field K] (n t : ℕ) (e X₀ : Matrix (Fin n) (Fin n) K) (ρ : ℕ → K) (ht : 2 ≤ t)
    (he : e * e = e) (h1 : e * X₀ = X₀) (h2 : X₀ * e = X₀) (hρ : Set.InjOn ρ (Finset.Icc 1 t : Set ℕ))
    (hP : ∏ c ∈ Finset.Icc 1 t, (X - C (ρ c)) = blockPol e X₀) :
    (((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod).rank = 1 ∧
    ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod *
      ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod =
      (∏ c ∈ Finset.Ioc 1 t, (ρ 1 - ρ c)) • ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod := by
  obtain ⟨a, b, hba, hab, hM⟩ := GlobalTheory.BlockCharpoly.blockPol_eq_charpoly e he rfl
  have hX : e * X₀ * e = X₀ := by rw [h1, h2]
  have hX' : a * (b * X₀ * a) * b = X₀ := by
    conv_rhs => rw [← hX, ← hab]
    simp only [Matrix.mul_assoc]
  have hcp : (b * X₀ * a).charpoly =
      (X - C (ρ 1)) * ((List.range' 2 (t - 1)).map fun c => X - C (ρ c)).prod := by
    rw [← hM, hX, ← hP, Finset.Icc_eq_cons_Ioc (by omega : 1 ≤ t), Finset.prod_cons,
      prod_Ioc_one_eq_list_range'_prod]
  have hev : (((List.range' 2 (t - 1)).map fun c => X - C (ρ c)).prod).eval (ρ 1) =
      ∏ c ∈ Finset.Ioc 1 t, (ρ 1 - ρ c) := by
    rw [prod_Ioc_one_eq_list_range'_prod, Polynomial.eval_list_prod, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c _
    simp
  have hne : (((List.range' 2 (t - 1)).map fun c => X - C (ρ c)).prod).eval (ρ 1) ≠ 0 := by
    rw [hev, Finset.prod_ne_zero_iff]
    intro c hc hzero
    rw [Finset.mem_Ioc] at hc
    have := hρ (by simp only [Finset.coe_Icc, Set.mem_Icc]; omega)
      (by simp only [Finset.coe_Icc, Set.mem_Icc]; omega) (sub_eq_zero.mp hzero)
    omega
  have heE : e * ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod =
      ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod := by
    obtain ⟨k, hk⟩ : ∃ k, t - 1 = k + 1 := ⟨t - 2, by omega⟩
    rw [hk, List.range'_succ, List.map_cons, List.prod_cons, ← Matrix.mul_assoc, Matrix.mul_sub,
      Matrix.mul_smul, h1, he]
  have hE : ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod =
      a * aeval (b * X₀ * a) ((List.range' 2 (t - 1)).map fun c => X - C (ρ c)).prod * b := by
    rw [← heE, ← prod_eq a b hba (b * X₀ * a) ρ, hab]
    congr 2
    apply List.map_congr_left
    intro c _
    rw [hX']
  have hsq := aeval_sq (b * X₀ * a) (ρ 1) _ hcp
  have hrk := aeval_rank (b * X₀ * a) (ρ 1) _ hcp hne
  rw [hE, ← hev]
  generalize aeval (b * X₀ * a) ((List.range' 2 (t - 1)).map fun c => X - C (ρ c)).prod = R at hsq hrk
  constructor
  · apply le_antisymm
    · exact ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)).trans hrk.le
    · have hR : R = b * (a * R * b) * a := by
        simp only [← Matrix.mul_assoc, hba, Matrix.one_mul]
        rw [Matrix.mul_assoc, hba, Matrix.mul_one]
      calc 1 = R.rank := hrk.symm
        _ = (b * (a * R * b) * a).rank := by rw [← hR]
        _ ≤ (b * (a * R * b)).rank := Matrix.rank_mul_le_left _ _
        _ ≤ (a * R * b).rank := Matrix.rank_mul_le_right _ _
  · calc a * R * b * (a * R * b) = a * (R * R) * b := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc b a, hba, Matrix.one_mul]
      _ = _ := by rw [hsq, Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Unfold `blockPol`. Rewrite using `[← Polynomial.coe_mapRingHom, RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`. Apply the tactic sequence `by_cases hij : i = j <;> simp [hij]`.
-/
theorem blockPol_map {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B)
    (e M : Matrix (Fin n) (Fin n) A) : (blockPol e M).map f = blockPol (e.map f) (M.map f) := by
  unfold blockPol
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases hij : i = j <;> simp [hij]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons c l ih`. Rewrite using `[List.map_cons, List.prod_cons, Matrix.map_mul, ih, List.map_cons, List.prod_cons]`. Use `congr 1`.

Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
private theorem map_list_prod' {O K : Type} [CommRing O] [CommRing K] (f : O →+* K) {n : ℕ}
    (e X₀ : Matrix (Fin n) (Fin n) O) (ρ : ℕ → O) (l : List ℕ) :
    ((l.map fun c => X₀ - ρ c • e).prod).map f = (l.map fun c => X₀.map f - f (ρ c) • e.map f).prod := by
  induction l with
  | nil => simp
  | cons c l ih =>
    rw [List.map_cons, List.prod_cons, Matrix.map_mul, ih, List.map_cons, List.prod_cons]
    congr 1
    ext i j
    simp

/- English proof (translation)
Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
private theorem map_smul_eq_smul_map {O K : Type} [CommRing O] [CommRing K] (f : O →+* K) {n : ℕ}
    (s : O) (M : Matrix (Fin n) (Fin n) O) : (s • M).map f = f s • M.map f := by
  ext i j
  simp

/- English proof (translation)
Establish `hinj : Function.Injective (toFr O)` using `IsFractionRing.injective O (FractionRing O)`. Take `⟨hr, hsq⟩` from `field_case (K := FractionRing O) n t (e.map (toFr O)) (X₀.map (toFr O)) (fun c => toFr O (ρ c)) ht (by rw [← Matrix.map_mul, he]) (by rw [← Matrix.map_mul, h1]) (by rw [← Matrix.map_mul, h2]) (fun x hx y hy hxy => hρ hx hy (hinj hxy)) (by rw [← blockPol_map, ← hP, Polynomial.map_ …`. Use `⟨by rw [map_list_prod']; exact hr, ?_⟩` and prove the remaining obligations. Establish `hmap : (((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod * ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod).map (toFr O) = ((∏ c ∈ Finset.Ioc 1 t, (ρ 1 - ρ c)) • ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod).map (toFr O)`. Rewrite using `[Matrix.map_mul, map_smul_eq_smul_map, map_list_prod', hsq, map_prod]`.

Simplify using `[map_sub]`. Use extensionality with `i j`. Conclude with `hinj (congrFun (congrFun hmap i) j)`.
-/
theorem rank_one_and_sq {O : Type} [CommRing O] [IsDomain O] (n t : ℕ) (e X₀ : Matrix (Fin n) (Fin n) O)
    (ρ : ℕ → O) (ht : 2 ≤ t)
    (he : e * e = e) (h1 : e * X₀ = X₀) (h2 : X₀ * e = X₀) (hρ : Set.InjOn ρ (Finset.Icc 1 t : Set ℕ))
    (hP : ∏ c ∈ Finset.Icc 1 t, (X - C (ρ c)) = blockPol e X₀) :
    ((((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod).map (toFr O)).rank = 1 ∧
    ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod *
      ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod =
      (∏ c ∈ Finset.Ioc 1 t, (ρ 1 - ρ c)) • ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod := by
  have hinj : Function.Injective (toFr O) := IsFractionRing.injective O (FractionRing O)
  obtain ⟨hr, hsq⟩ := field_case (K := FractionRing O) n t (e.map (toFr O)) (X₀.map (toFr O))
    (fun c => toFr O (ρ c)) ht (by rw [← Matrix.map_mul, he]) (by rw [← Matrix.map_mul, h1])
    (by rw [← Matrix.map_mul, h2]) (fun x hx y hy hxy => hρ hx hy (hinj hxy))
    (by rw [← blockPol_map, ← hP, Polynomial.map_prod]; simp)
  refine ⟨by rw [map_list_prod']; exact hr, ?_⟩
  have hmap : (((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod *
      ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod).map (toFr O) =
      ((∏ c ∈ Finset.Ioc 1 t, (ρ 1 - ρ c)) •
        ((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • e).prod).map (toFr O) := by
    rw [Matrix.map_mul, map_smul_eq_smul_map, map_list_prod', hsq, map_prod]
    simp [map_sub]
  ext i j
  exact hinj (congrFun (congrFun hmap i) j)

end GlobalTheory.RootFactor
