import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.TestEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.TrConst
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.ClosureIdeal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.TestVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.PrVr
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.PrAdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.OddDiag
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.HomBasic
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EigEx
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => exact ⟨fun i j hij => by simp [Matrix.one_apply_ne hij.ne'], fun i => by simp⟩`. Consider the case `cons A L ih`. Take `⟨h1, h2⟩` from `ih fun M hM => h M (by simp [hM])`. Establish `hA` using `h A (by simp)`.

Use `⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[List.prod_cons, Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Break down `lt_or_ge k i with hk | hk` into its components or cases. Rewrite using `[hA i k hk, zero_mul]`.

Rewrite using `[h1 k j (hij.trans_le hk), mul_zero]`. Rewrite using `[List.prod_cons, Matrix.mul_apply, List.map_cons, List.prod_cons, ← h2]`. Use `Finset.sum_eq_single i ?_ (by simp)` and prove the remaining obligations. Introduce `k _ hk`. Break down `lt_or_gt_of_ne hk with h3 | h3` into its components or cases.

Rewrite using `[hA i k h3, zero_mul]`. Rewrite using `[h1 k i h3, mul_zero]`.
-/
private theorem tri_prod {R : Type} [CommRing R] {n : ℕ} (L : List (Matrix (Fin n) (Fin n) R))
    (h : ∀ M ∈ L, ∀ i j, j < i → M i j = 0) :
    (∀ i j, j < i → L.prod i j = 0) ∧ ∀ i, L.prod i i = (L.map fun M => M i i).prod := by
  induction L with
  | nil => exact ⟨fun i j hij => by simp [Matrix.one_apply_ne hij.ne'], fun i => by simp⟩
  | cons A L ih =>
    obtain ⟨h1, h2⟩ := ih fun M hM => h M (by simp [hM])
    have hA := h A (by simp)
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [List.prod_cons, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      rcases lt_or_ge k i with hk | hk
      · rw [hA i k hk, zero_mul]
      · rw [h1 k j (hij.trans_le hk), mul_zero]
    · rw [List.prod_cons, Matrix.mul_apply, List.map_cons, List.prod_cons, ← h2]
      refine Finset.sum_eq_single i ?_ (by simp)
      intro k _ hk
      rcases lt_or_gt_of_ne hk with h3 | h3
      · rw [hA i k h3, zero_mul]
      · rw [h1 k i h3, mul_zero]

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro M c _`. Simplify using the standard rewrite rules. Consider the case `succ m ih`.

Introduce `M c h`. Rewrite using `[List.ofFn_succ, List.prod_cons, ← Matrix.mulVec_mulVec, ih _ (fun k => c k.succ) (fun k => h _), Matrix.mulVec_smul, h, Fin.prod_univ_succ, smul_smul, mul_comm]`.
-/
private theorem eig_prod {R : Type} [CommRing R] {n : ℕ} (v : Fin n → R) :
    ∀ {m : ℕ} (M : Fin m → Matrix (Fin n) (Fin n) R) (c : Fin m → R), (∀ k, M k *ᵥ v = c k • v) →
      (List.ofFn M).prod *ᵥ v = (∏ k, c k) • v := by
  intro m
  induction m with
  | zero => intro M c _; simp
  | succ m ih =>
    intro M c h
    rw [List.ofFn_succ, List.prod_cons, ← Matrix.mulVec_mulVec, ih _ (fun k => c k.succ) (fun k => h _),
      Matrix.mulVec_smul, h, Fin.prod_univ_succ, smul_smul, mul_comm]

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qi37.eig_ex P a hP i`.
-/
private theorem eig_ex {k : Type} [Field k] {n : ℕ} (P : Matrix (Fin n) (Fin n) k) (a : Fin n → k)
    (hP : P.charpoly = ∏ i, (Polynomial.X - Polynomial.C (a i))) (i : Fin n) :
    ∃ v : Fin n → k, v ≠ 0 ∧ P *ᵥ v = a i • v :=
  _root_.UpperTheory.Reformulated.B.Qi37.eig_ex P a hP i

/- English proof (translation)
Rewrite `h` using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]`. Conclude with `(IsUnit.mul_left_eq_zero (IsUnit.prod_iff.2 fun j hj => hu j (Finset.ne_of_mem_erase hj))).1 h`.
-/
private theorem one_zero {R : Type} [CommRing R] {n : ℕ} (c : Fin n → R) (i : Fin n)
    (hu : ∀ j, j ≠ i → IsUnit (c j)) (h : ∏ j, c j = 0) : c i = 0 := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)] at h
  exact (IsUnit.mul_left_eq_zero (IsUnit.prod_iff.2 fun j hj => hu j (Finset.ne_of_mem_erase hj))).1 h

/- English proof (translation)
Take `⟨j, hj⟩` from `Function.ne_iff.1 hv`. Use `congrFun h j` as an intermediate fact. Conclude with `(IsUnit.mul_left_eq_zero ((IsUnit.mk0 _ hj).map (algebraMap k R))).1 this`.
-/
private theorem eig_zero {k R : Type} [Field k] [CommRing R] [Algebra k R] {n : ℕ} (v : Fin n → k) (hv : v ≠ 0)
    (c : R) (h : c • (fun j => algebraMap k R (v j)) = 0) : c = 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hv
  have := congrFun h j
  exact (IsUnit.mul_left_eq_zero ((IsUnit.mk0 _ hj).map (algebraMap k R))).1 this

/- English proof (translation)
Rewrite using `[Matrix.sub_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec, sub_smul]`. Use `congr 1`. Use extensionality with `i`. Use `RingHom.map_mulVec (algebraMap k R) P v i` as an intermediate fact. Rewrite `this` using `[h]`.

Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul] at this ⊢`. Conclude with `this.symm`.
-/
private theorem eig_map {k R : Type} [Field k] [CommRing R] [Algebra k R] {n : ℕ} (P : Matrix (Fin n) (Fin n) k)
    (a : k) (v : Fin n → k) (h : P *ᵥ v = a • v) (c : R) :
    (P.map (algebraMap k R) - algebraMap R (Matrix (Fin n) (Fin n) R) c) *ᵥ (fun j => algebraMap k R (v j)) =
      (algebraMap k R a - c) • fun j => algebraMap k R (v j) := by
  rw [Matrix.sub_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec, sub_smul]
  congr 1
  ext i
  have := RingHom.map_mulVec (algebraMap k R) P v i
  rw [h] at this
  simp only [Pi.smul_apply, smul_eq_mul, map_mul] at this ⊢
  exact this.symm

/- English proof (translation)
Take `⟨N, hN⟩` from `hn`. Establish `h1 : x - algebraMap k R (e x) ∈ RingHom.ker e` using `by simp [RingHom.mem_ker]`. Establish `h2 : IsNilpotent (x - algebraMap k R (e x))` using `⟨N, by`. Use `Ideal.pow_mem_pow h1 N` as an intermediate fact. Rewrite using `[hN, Ideal.mem_bot] at this⟩` and apply the resulting hypothesis.

Use `h2.isUnit_add_left_of_commute ((IsUnit.mk0 _ hx).map (algebraMap k R)) (Commute.all _ _)` as an intermediate fact. Simplify using `using this`.
-/
private theorem unit_of {k R : Type} [Field k] [CommRing R] [Algebra k R] (e : R →ₐ[k] k)
    (hn : ∃ N : ℕ, RingHom.ker e ^ N = ⊥) (x : R) (hx : e x ≠ 0) : IsUnit x := by
  obtain ⟨N, hN⟩ := hn
  have h1 : x - algebraMap k R (e x) ∈ RingHom.ker e := by simp [RingHom.mem_ker]
  have h2 : IsNilpotent (x - algebraMap k R (e x)) := ⟨N, by
    have := Ideal.pow_mem_pow h1 N
    rwa [hN, Ideal.mem_bot] at this⟩
  have := h2.isUnit_add_left_of_commute ((IsUnit.mk0 _ hx).map (algebraMap k R)) (Commute.all _ _)
  simpa using this

/- English proof (translation)
Assemble the required witnesses or components as `⟨{ toFun := fun Z => T * Z * T' map_one' := by rw [mul_one, h] map_mul' := fun X Y => by calc T * (X * Y) * T' = T * X * (T' * T) * Y * T' := by rw [h']; simp only [mul_one, mul_assoc] _ = _ := by simp only [mul_assoc] map_zero' := by simp map_add' := fun X Y => by rw [mul_add, a …`.
-/
private theorem conj_ex {R : Type} [CommRing R] {n : ℕ} (T T' : Matrix (Fin n) (Fin n) R) (h : T * T' = 1)
    (h' : T' * T = 1) : ∃ φ : Matrix (Fin n) (Fin n) R →ₐ[R] Matrix (Fin n) (Fin n) R, ∀ Z, φ Z = T * Z * T' :=
  ⟨{ toFun := fun Z => T * Z * T'
     map_one' := by rw [mul_one, h]
     map_mul' := fun X Y => by
       calc T * (X * Y) * T' = T * X * (T' * T) * Y * T' := by rw [h']; simp only [mul_one, mul_assoc]
         _ = _ := by simp only [mul_assoc]
     map_zero' := by simp
     map_add' := fun X Y => by rw [mul_add, add_mul]
     commutes' := fun c => by rw [← Algebra.commutes, mul_assoc, h, mul_one] }, fun _ => rfl⟩

/- English proof (translation)
Use `choose s hs using hsep i`. Set `g' : Fin n → Γ` to `fun j => if h : j ≠ i then s j h else g`. Establish `h2` using `(tri_prod (List.ofFn fun i => (M (g' i)).map (algebraMap k R) - algebraMap R (Matrix (Fin n) (Fin n) R) (c i (g' i))) (by`. Introduce `Z hZ a b hab`. Take `⟨j, rfl⟩` from `List.mem_ofFn.1 hZ`.

Simplify using `[Matrix.algebraMap_matrix_apply, hab.ne', htri _ a b hab])).2 i`. Rewrite `h2` using `[hrel, List.map_ofFn, List.prod_ofFn]`. Establish `h3` using `one_zero _ i (fun j hj => unit_of e hn _ (by`. Establish `hg : g' j = s j hj` using `dif_pos hj`. Simplify using `only [Function.comp_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply, if_true, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, hc, hg]`.

Conclude with `sub_ne_zero.2 (hs j hj))) h2.symm`. Establish `hg : g' i = g` using `dif_neg (by simp)`. Simplify using `only [Function.comp_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply, if_true, Algebra.algebraMap_self, RingHom.id_apply, hg] at h3`. Conclude with `(sub_eq_zero.1 h3).symm`.
-/
private theorem psi_lem {k R Γ : Type} [Field k] [CommRing R] [Algebra k R] {n : ℕ} (e : R →ₐ[k] k)
    (hn : ∃ N : ℕ, RingHom.ker e ^ N = ⊥) (M : Γ → Matrix (Fin n) (Fin n) k) (c : Fin n → Γ → R)
    (htri : ∀ g i j, j < i → M g i j = 0) (hc : ∀ i g, e (c i g) = M g i i)
    (hsep : ∀ i j, j ≠ i → ∃ g, M g i i ≠ M g j j)
    (hrel : ∀ g : Fin n → Γ, (List.ofFn fun i => (M (g i)).map (algebraMap k R) -
      algebraMap R (Matrix (Fin n) (Fin n) R) (c i (g i))).prod = 0) (i : Fin n) (g : Γ) :
    c i g = algebraMap k R (M g i i) := by
  classical
  choose s hs using hsep i
  let g' : Fin n → Γ := fun j => if h : j ≠ i then s j h else g
  have h2 := (tri_prod (List.ofFn fun i => (M (g' i)).map (algebraMap k R) -
      algebraMap R (Matrix (Fin n) (Fin n) R) (c i (g' i))) (by
    intro Z hZ a b hab
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hZ
    simp [Matrix.algebraMap_matrix_apply, hab.ne', htri _ a b hab])).2 i
  rw [hrel, List.map_ofFn, List.prod_ofFn] at h2
  have h3 := one_zero _ i (fun j hj => unit_of e hn _ (by
    have hg : g' j = s j hj := dif_pos hj
    simp only [Function.comp_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply, if_true,
      map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, hc, hg]
    exact sub_ne_zero.2 (hs j hj))) h2.symm
  have hg : g' i = g := dif_neg (by simp)
  simp only [Function.comp_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply, if_true,
    Algebra.algebraMap_self, RingHom.id_apply, hg] at h3
  exact (sub_eq_zero.1 h3).symm

/- English proof (translation)
Take `⟨v, hv0, hv⟩` from `eig_ex P _ hP i`. Establish `hu : ∀ j, j ≠ i → IsUnit (algebraMap k R (e (c i)) - c j)` using `fun j hj => unit_of e hn _ (by`. Rewrite using `[map_sub, AlgHom.commutes]`. Conclude with `sub_ne_zero.2 fun h => hj (hinj h).symm)`. Use `⟨fun h => ?_, fun y h => ?_⟩` and prove the remaining obligations.

Establish `h1` using `eig_prod _ _ _ fun j => eig_map P _ v hv (c j)`. Rewrite `h1` using `[h, Matrix.zero_mulVec]`. Conclude with `(sub_eq_zero.1 (one_zero _ i hu (eig_zero v hv0 _ h1.symm))).symm`. Establish `h1` using `eig_prod (fun j => algebraMap k R (v j)) (fun j => if j = i then 1 else P.map (algebraMap k R) - algebraMap R (Matrix (Fin n) (Fin n) R) (c j)) (fun j => if j = i then 1 else algebraMap k R (e (c i)) - c j) (fun j => by`. Distinguish the cases in `hj : j = i`.

Simplify using `[hj]`. Simplify using `only [hj, if_false]`. Conclude with `eig_map P _ v hv (c j))`. Establish `h2` using `congrArg (fun Z => Z *ᵥ fun j => algebraMap k R (v j)) h`. Simplify using `only [sub_self, zero_sub, Matrix.zero_mulVec] at h2`.

Rewrite `h2` using `[← Matrix.mulVec_mulVec, Matrix.neg_mulVec, Algebra.algebraMap_eq_smul_one y, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_neg, Matrix.mulVec_smul, h1, smul_smul, neg_eq_zero]`. Use `(IsUnit.mul_left_eq_zero (IsUnit.prod_iff.2 fun j _ => ?_)).1 (eig_zero v hv0 _ h2)` and prove the remaining obligations. Distinguish the cases in `hj : j = i`. Simplify using `[hj]`. Simplify using `only [hj, if_false]`.

Conclude with `hu j hj`.
-/
private theorem u_lem {k R : Type} [Field k] [CommRing R] [Algebra k R] {n : ℕ} (e : R →ₐ[k] k)
    (hn : ∃ N : ℕ, RingHom.ker e ^ N = ⊥) (P : Matrix (Fin n) (Fin n) k) (c : Fin n → R)
    (hP : P.charpoly = ∏ i, (Polynomial.X - Polynomial.C (e (c i)))) (hinj : Function.Injective fun i => e (c i))
    (i : Fin n) :
    ((List.ofFn fun i => P.map (algebraMap k R) - algebraMap R (Matrix (Fin n) (Fin n) R) (c i)).prod = 0 →
      c i = algebraMap k R (e (c i))) ∧
    ∀ y : R, (List.ofFn fun j => if j = i then 1 else P.map (algebraMap k R) -
      algebraMap R (Matrix (Fin n) (Fin n) R) (c j)).prod * (1 - 1 - algebraMap R (Matrix (Fin n) (Fin n) R) y) = 0 →
      y = 0 := by
  obtain ⟨v, hv0, hv⟩ := eig_ex P _ hP i
  have hu : ∀ j, j ≠ i → IsUnit (algebraMap k R (e (c i)) - c j) := fun j hj => unit_of e hn _ (by
    rw [map_sub, AlgHom.commutes]
    exact sub_ne_zero.2 fun h => hj (hinj h).symm)
  refine ⟨fun h => ?_, fun y h => ?_⟩
  · have h1 := eig_prod _ _ _ fun j => eig_map P _ v hv (c j)
    rw [h, Matrix.zero_mulVec] at h1
    exact (sub_eq_zero.1 (one_zero _ i hu (eig_zero v hv0 _ h1.symm))).symm
  · have h1 := eig_prod (fun j => algebraMap k R (v j)) (fun j => if j = i then 1 else P.map (algebraMap k R) -
      algebraMap R (Matrix (Fin n) (Fin n) R) (c j)) (fun j => if j = i then 1 else algebraMap k R (e (c i)) - c j)
      (fun j => by
        by_cases hj : j = i
        · simp [hj]
        · simp only [hj, if_false]; exact eig_map P _ v hv (c j))
    have h2 := congrArg (fun Z => Z *ᵥ fun j => algebraMap k R (v j)) h
    simp only [sub_self, zero_sub, Matrix.zero_mulVec] at h2
    rw [← Matrix.mulVec_mulVec, Matrix.neg_mulVec, Algebra.algebraMap_eq_smul_one y, Matrix.smul_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_neg, Matrix.mulVec_smul, h1, smul_smul, neg_eq_zero] at h2
    refine (IsUnit.mul_left_eq_zero (IsUnit.prod_iff.2 fun j _ => ?_)).1 (eig_zero v hv0 _ h2)
    by_cases hj : j = i
    · simp [hj]
    · simp only [hj, if_false]; exact hu j hj

/- English proof (translation)
Take `⟨r1, -, r3, r4, r5⟩` from `vrRel l S`. Take `⟨-, -, t3, t4, -⟩` from `testVal l S R e θ hθ`. Establish `he : ∀ b : S.B, e (θ (algebraMap S.B S.U.AA b)) = algebraMap S.x.A S.F (S.P.f b)`. Introduce `b`. Use `((prAdd l S).2.1 (algebraMap S.B S.Bh b) 0).1` as an intermediate fact.

Rewrite `this` using `[Submodule.coe_zero, add_zero]`. Rewrite using `[hθ.res, IsScalarTower.algebraMap_apply S.B S.Bh S.U.AA, this, S.rF_f]`. Establish `key : ∀ (b : S.B) (c : S.F), θ (algebraMap S.B S.U.AA b) = algebraMap S.F R c → θ (algebraMap S.B S.U.AA b) = algebraMap S.F R (algebraMap S.x.A S.F (S.P.f b))`. Introduce `b c hb`. Rewrite using `[← he, hb, AlgHom.commutes]`.

Both sides reduce to the same expression. Take `⟨φ0, hφ0⟩` from `conj_ex T T' h h'`. Choose the witnesses or unpack the hypotheses as in `⟨φ, hφ1, hφ2⟩ : ∃ φ : Matrix (Fin S.n) (Fin S.n) S.U.AA →+* Matrix (Fin S.n) (Fin S.n) R, (∀ g, φ (S.U.vr g) = (S.ρ S.F g).map (algebraMap S.F R)) ∧ ∀ a, φ (algebraMap S.U.AA _ a) = algebraMap R _ (θ a) := by`. Use `⟨φ0.toRingHom.comp θ.mapMatrix, fun g => (hφ0 _).trans (hc g), fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[← φ0.commutes]`.

Use `congrArg φ0 ?_` and prove the remaining obligations. Use extensionality with `x y`. Apply the tactic sequence `by_cases hxy : x = y <;> simp [Matrix.algebraMap_matrix_apply, hxy]`. Establish `hU : ∀ j i, _` using `fun j i => u_lem e hθ.nil (S.ρ S.F (S.P.ph j)) (fun i => θ (algebraMap S.B S.U.AA (S.P.U j i))) (by`. Simplify using `only [he]`.

Rewrite using `[Ctx.ρ, NP.ρX, Matrix.charpoly_map, S.P.eig, Polynomial.map_prod]`. Use the proof step `simp)`. Use the proof step `(by`. Simplify using `only [he]`. Conclude with `(IsFractionRing.injective S.x.A S.F).comp (S.P.f_U j)) i`.

Use `trConst l S R e θ hθ ?_ b` and prove the remaining obligations. Introduce and unpack `b (((⟨i, g, rfl⟩ | ⟨v, i, g, rfl⟩) | ⟨j, i, rfl | rfl⟩) | rfl)`. Use `key _ ((-1) ^ i * (S.ρ S.F g).charpoly.coeff (S.n - i)) ?_` and prove the remaining obligations. Establish `h1 : ((S.U.vr g).map θ).charpoly = ((S.ρ S.F g).map (algebraMap S.F R)).charpoly`. Rewrite using `[← hc, Matrix.charpoly_mul_comm, ← mul_assoc, h', one_mul]`.

Rewrite `h1` using `[Matrix.charpoly_map, Matrix.charpoly_map]`. Rewrite using `[r5, map_mul, map_mul, ← Polynomial.coeff_map, ← Polynomial.coeff_map, h1]`. Simplify using the standard rewrite rules. Take `⟨o1, o2, -, o4, -⟩` from `oddDiag l S.L S.G S.G0 S.h S.n S.x S.F v`. Establish `hp` using `(homBasic l S.L S.G S.G0 S.h).2.2.2.1 v`.

Take `⟨φ1, hφ3⟩` from `conj_ex ((S.x.wiX S.F v).map (algebraMap S.F R)) ((S.x.wX S.F v).map (algebraMap S.F R)) (by rw [← Matrix.map_mul, o2]; simp) (by rw [← Matrix.map_mul, o1]; simp)`. Use `key _ _ (psi_lem e hθ.nil (fun g => S.x.wiX S.F v * S.x.ρX S.F (S.G0.φ v g) * S.x.wX S.F v) (fun i g => θ (algebraMap S.B S.U.AA (S.u.ψ v i g))) (fun g => (o4 g).1) (fun i g => (t4 v i g).trans ((o4 g).2 i).symm) (fun i j hij => ?_) (fun g => ?_) i g)` and prove the remaining obligations. Assume the negation of the conclusion as `hne push Not at hne`. Use `(S.x.N1 v).1 i j hij.symm (MonoidHom.ext fun g => Units.ext (IsFractionRing.injective S.x.A S.F ?_))` and prove the remaining obligations. Rewrite using `[← (o4 g).2, ← (o4 g).2, hne g]`.

Establish `h1` using `congrArg (φ1.toRingHom.comp φ) (r1 v g)`. Rewrite `h1` using `[map_list_prod, map_zero, List.map_ofFn]`. Rewrite using `[← h1]`. Use `congr 2`. Use function extensionality and compare the values at `i`.

Simplify using `only [Function.comp_apply, RingHom.comp_apply, map_sub, hφ1, hφ2, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]`. Rewrite using `[hφ3, Matrix.map_mul, Matrix.map_mul, Ctx.ρ, hp]`. Use `key _ _ ((hU j i).1 ?_)` and prove the remaining obligations. Establish `h1` using `congrArg φ (r3 j)`. Rewrite `h1` using `[map_list_prod, map_zero, List.map_ofFn]`.

Rewrite using `[← h1]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Simplify using `only [Function.comp_apply, map_sub, hφ1, hφ2]`. Use `key _ 0 (((hU j i).2 _ ?_).trans (map_zero _).symm)` and prove the remaining obligations.

Establish `h1` using `congrArg φ (r4 j i)`. Establish `h2 : S.ρ S.F (S.P.ta j) = 1`. Rewrite using `[Ctx.ρ, S.P.p_ta, NP.ρX]`. Simplify using `[mat]`. Rewrite `h1` using `[map_mul, map_list_prod, map_zero, List.map_ofFn, map_sub, map_sub, hφ1, hφ2, h2, map_one, Matrix.map_one _ (map_zero _) (map_one _)]`.

Rewrite using `[← h1]`. Use `congr 3`. Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = i`. Simplify using `[hk]`.

Simplify using `only [Function.comp_apply, hk, if_false, map_sub, hφ1, hφ2]`. Conclude with `key _ _ t3`.
-/
private theorem conj_const {l : ℕ} [Fact l.Prime] (S : Ctx l) (R : Type) [CommRing R] [Algebra S.F R]
    (e : R →ₐ[S.F] S.F) (θ : S.U.AA →+* R) (hθ : S.Test R e θ) (T T' : Matrix (Fin S.n) (Fin S.n) R)
    (h : T * T' = 1) (h' : T' * T = 1)
    (hc : ∀ g, T * (S.U.vr g).map θ * T' = (S.ρ S.F g).map (algebraMap S.F R)) (b : S.Bh) :
    θ (algebraMap S.Bh S.U.AA b) = algebraMap S.F R (S.rF b) := by
  obtain ⟨r1, -, r3, r4, r5⟩ := vrRel l S
  obtain ⟨-, -, t3, t4, -⟩ := testVal l S R e θ hθ
  have he : ∀ b : S.B, e (θ (algebraMap S.B S.U.AA b)) = algebraMap S.x.A S.F (S.P.f b) := by
    intro b
    have := ((prAdd l S).2.1 (algebraMap S.B S.Bh b) 0).1
    rw [Submodule.coe_zero, add_zero] at this
    rw [hθ.res, IsScalarTower.algebraMap_apply S.B S.Bh S.U.AA, this, S.rF_f]
  have key : ∀ (b : S.B) (c : S.F), θ (algebraMap S.B S.U.AA b) = algebraMap S.F R c →
      θ (algebraMap S.B S.U.AA b) = algebraMap S.F R (algebraMap S.x.A S.F (S.P.f b)) := by
    intro b c hb
    rw [← he, hb, AlgHom.commutes]; rfl
  obtain ⟨φ0, hφ0⟩ := conj_ex T T' h h'
  obtain ⟨φ, hφ1, hφ2⟩ : ∃ φ : Matrix (Fin S.n) (Fin S.n) S.U.AA →+* Matrix (Fin S.n) (Fin S.n) R,
      (∀ g, φ (S.U.vr g) = (S.ρ S.F g).map (algebraMap S.F R)) ∧
      ∀ a, φ (algebraMap S.U.AA _ a) = algebraMap R _ (θ a) := by
    refine ⟨φ0.toRingHom.comp θ.mapMatrix, fun g => (hφ0 _).trans (hc g), fun a => ?_⟩
    rw [← φ0.commutes]
    refine congrArg φ0 ?_
    ext x y
    by_cases hxy : x = y <;> simp [Matrix.algebraMap_matrix_apply, hxy]
  have hU : ∀ j i, _ := fun j i => u_lem e hθ.nil (S.ρ S.F (S.P.ph j)) (fun i => θ (algebraMap S.B S.U.AA (S.P.U j i)))
    (by
      simp only [he]
      rw [Ctx.ρ, NP.ρX, Matrix.charpoly_map, S.P.eig, Polynomial.map_prod]
      simp)
    (by
      simp only [he]
      exact (IsFractionRing.injective S.x.A S.F).comp (S.P.f_U j)) i
  refine trConst l S R e θ hθ ?_ b
  rintro b (((⟨i, g, rfl⟩ | ⟨v, i, g, rfl⟩) | ⟨j, i, rfl | rfl⟩) | rfl)
  · refine key _ ((-1) ^ i * (S.ρ S.F g).charpoly.coeff (S.n - i)) ?_
    have h1 : ((S.U.vr g).map θ).charpoly = ((S.ρ S.F g).map (algebraMap S.F R)).charpoly := by
      rw [← hc, Matrix.charpoly_mul_comm, ← mul_assoc, h', one_mul]
    rw [Matrix.charpoly_map, Matrix.charpoly_map] at h1
    rw [r5, map_mul, map_mul, ← Polynomial.coeff_map, ← Polynomial.coeff_map, h1]
    simp
  · obtain ⟨o1, o2, -, o4, -⟩ := oddDiag l S.L S.G S.G0 S.h S.n S.x S.F v
    have hp := (homBasic l S.L S.G S.G0 S.h).2.2.2.1 v
    obtain ⟨φ1, hφ3⟩ := conj_ex ((S.x.wiX S.F v).map (algebraMap S.F R)) ((S.x.wX S.F v).map (algebraMap S.F R))
      (by rw [← Matrix.map_mul, o2]; simp) (by rw [← Matrix.map_mul, o1]; simp)
    refine key _ _ (psi_lem e hθ.nil (fun g => S.x.wiX S.F v * S.x.ρX S.F (S.G0.φ v g) * S.x.wX S.F v)
      (fun i g => θ (algebraMap S.B S.U.AA (S.u.ψ v i g))) (fun g => (o4 g).1)
      (fun i g => (t4 v i g).trans ((o4 g).2 i).symm) (fun i j hij => ?_) (fun g => ?_) i g)
    · by_contra hne
      push Not at hne
      refine (S.x.N1 v).1 i j hij.symm (MonoidHom.ext fun g => Units.ext (IsFractionRing.injective S.x.A S.F ?_))
      rw [← (o4 g).2, ← (o4 g).2, hne g]
    · have h1 := congrArg (φ1.toRingHom.comp φ) (r1 v g)
      rw [map_list_prod, map_zero, List.map_ofFn] at h1
      rw [← h1]
      congr 2
      funext i
      simp only [Function.comp_apply, RingHom.comp_apply, map_sub, hφ1, hφ2, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, AlgHom.commutes]
      rw [hφ3, Matrix.map_mul, Matrix.map_mul, Ctx.ρ, hp]
  · refine key _ _ ((hU j i).1 ?_)
    have h1 := congrArg φ (r3 j)
    rw [map_list_prod, map_zero, List.map_ofFn] at h1
    rw [← h1]
    congr 2
    funext i
    simp only [Function.comp_apply, map_sub, hφ1, hφ2]
  · refine key _ 0 (((hU j i).2 _ ?_).trans (map_zero _).symm)
    have h1 := congrArg φ (r4 j i)
    have h2 : S.ρ S.F (S.P.ta j) = 1 := by
      rw [Ctx.ρ, S.P.p_ta, NP.ρX]; simp [mat]
    rw [map_mul, map_list_prod, map_zero, List.map_ofFn, map_sub, map_sub, hφ1, hφ2, h2, map_one,
      Matrix.map_one _ (map_zero _) (map_one _)] at h1
    rw [← h1]
    congr 3
    funext k
    by_cases hk : k = i
    · simp [hk]
    · simp only [Function.comp_apply, hk, if_false, map_sub, hφ1, hφ2]
  · exact key _ _ t3

/- English proof (translation)
Introduce and unpack `l _ S α hα ⟨Y, -, -, hY⟩`. Take `⟨θ, hθ, hv⟩` from `testEx l S 1 (fun _ => α) (fun _ => 0) 0 (fun _ => hα) (fun _ => S.La.zero_mem) (by simp)`. Establish `hm : ∀ g, S.ρ S.F g⁻¹ * S.ρ S.F g = 1`. Introduce `g`. Simplify using `only [Ctx.ρ, NP.ρX]`.

Rewrite using `[← Matrix.map_mul]`. Simplify using `[mat]`. Establish `hA : ∀ g, (S.U.vr g).map (fun a => α (S.pr0 a)) = S.ρ S.F g * Y - Y * S.ρ S.F g`. Introduce `g`. Establish `h1` using `congrArg (· * S.ρ S.F g) (congrFun hY g)`.

Simplify using `only [Ctx.alC, dY] at h1`. Rewrite `h1` using `[mul_assoc, hm, mul_one, sub_mul, mul_assoc, hm, mul_one]`. Conclude with `h1`. Set `E : Matrix (Fin S.n) (Fin S.n) S.F → Matrix (Fin S.n) (Fin S.n) (DD S.F 1)` to `fun Z => Z.map fun a => ⟨0, 0, fun _ => a, 0⟩`. Establish `hEE : ∀ Z Z', E Z * E Z' = 0`.

Introduce `Z Z'`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [E]`.

Establish `hE : ∀ Z : Matrix (Fin S.n) (Fin S.n) S.F, ∃ ε : DD S.F 1, ∀ Z, E Z = ε • Z.map (algebraMap S.F (DD S.F 1))`. Introduce `_`. Use `⟨⟨0, 0, fun _ => 1, 0⟩, fun Z => Matrix.ext fun i j => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = (⟨0, 0, fun _ => 1, 0⟩ : DD S.F 1) * DD.C (Z i j)`. Apply the tactic sequence `ext <;> simp [E]`.

Take `⟨ε, hε⟩` from `hE 0`. Establish `hu : ∀ g, (S.U.vr g).map θ = (S.ρ S.F g).map (algebraMap S.F (DD S.F 1)) + E (S.ρ S.F g * Y - Y * S.ρ S.F g)`. Introduce `g`. Rewrite using `[← hA]`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `_ = (DD.C (S.ρ S.F g i j) : DD S.F 1) + E _ i j`. Rewrite using `[Matrix.map_apply, hv, (prVr l S g i j).1]`. Apply the tactic sequence `ext <;> simp [E]`. Establish `h0` using `conj_const S (DD S.F 1) (DD.aug S.F 1) θ hθ (1 + E Y) (1 - E Y) (by rw [mul_sub, mul_one, add_mul, one_mul, hEE, add_zero, add_sub_cancel_right]) (by rw [mul_add, mul_one, sub_mul, one_mul, hEE, sub_zero, sub_add_cancel]) (fun g => by`. Establish `a1 : E (S.ρ S.F g * Y - Y * S.ρ S.F g) = (S.ρ S.F g).map (algebraMap S.F (DD S.F 1)) * E Y - E Y * (S.ρ S.F g).map (algebraMap S.F (DD S.F 1))`.

Rewrite using `[hε, hε, Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_sub _ (map_sub _)]`. Establish `a2 : E Y * (S.ρ S.F g).map (algebraMap S.F (DD S.F 1)) * E Y = 0`. Use `hEE (Y * S.ρ S.F g) Y` as an intermediate fact. Rewrite `this` using `[hε (Y * _), Matrix.map_mul, ← Matrix.smul_mul, ← hε]`. Then use the resulting hypothesis. Establish `a3` using `hEE Y Y`.

Rewrite using `[hu, a1]`. Generalize the expression as in `(S.ρ S.F g).map (algebraMap S.F (DD S.F 1)) = r at a2 ⊢`. Generalize the expression as in `E Y = y at a2 a3 ⊢`. Establish `: (1 + y) * (r + (r * y - y * r)) * (1 - y) = r - r * (y * y) + y * r * y - y * r * y * y - y * y * r + y * y * r * y` using `by noncomm_ring`. Rewrite using `[this, a2, a3]`.

Use the proof step `simp)`. Use extensionality with `b`. Establish `h1` using `congrArg (fun u => DD.ep' u 0) ((hv _).symm.trans (h0 b))`. Establish `h2` using `((prAdd l S).2.1 b 0).1`. Rewrite `h2` using `[Submodule.coe_zero, add_zero]`.

Simplify using `only [h2] at h1`. Conclude with `h1`.
-/
theorem UpperTheory.V.Pa.alInj :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ α ∈ S.Tp, S.alC α ∈ BdP S.h S.x S.F → α = 0 := by
  rintro l _ S α hα ⟨Y, -, -, hY⟩
  obtain ⟨θ, hθ, hv⟩ := testEx l S 1 (fun _ => α) (fun _ => 0) 0 (fun _ => hα) (fun _ => S.La.zero_mem) (by simp)
  have hm : ∀ g, S.ρ S.F g⁻¹ * S.ρ S.F g = 1 := by
    intro g
    simp only [Ctx.ρ, NP.ρX]
    rw [← Matrix.map_mul]
    simp [mat]
  have hA : ∀ g, (S.U.vr g).map (fun a => α (S.pr0 a)) = S.ρ S.F g * Y - Y * S.ρ S.F g := by
    intro g
    have h1 := congrArg (· * S.ρ S.F g) (congrFun hY g)
    simp only [Ctx.alC, dY] at h1
    rw [mul_assoc, hm, mul_one, sub_mul, mul_assoc, hm, mul_one] at h1
    exact h1
  let E : Matrix (Fin S.n) (Fin S.n) S.F → Matrix (Fin S.n) (Fin S.n) (DD S.F 1) :=
    fun Z => Z.map fun a => ⟨0, 0, fun _ => a, 0⟩
  have hEE : ∀ Z Z', E Z * E Z' = 0 := by
    intro Z Z'
    refine Matrix.ext fun i j => ?_
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    ext <;> simp [E]
  have hE : ∀ Z : Matrix (Fin S.n) (Fin S.n) S.F, ∃ ε : DD S.F 1, ∀ Z, E Z = ε • Z.map (algebraMap S.F (DD S.F 1)) := by
    intro _
    refine ⟨⟨0, 0, fun _ => 1, 0⟩, fun Z => Matrix.ext fun i j => ?_⟩
    change _ = (⟨0, 0, fun _ => 1, 0⟩ : DD S.F 1) * DD.C (Z i j)
    ext <;> simp [E]
  obtain ⟨ε, hε⟩ := hE 0
  have hu : ∀ g, (S.U.vr g).map θ = (S.ρ S.F g).map (algebraMap S.F (DD S.F 1)) + E (S.ρ S.F g * Y - Y * S.ρ S.F g) := by
    intro g
    rw [← hA]
    refine Matrix.ext fun i j => ?_
    change _ = (DD.C (S.ρ S.F g i j) : DD S.F 1) + E _ i j
    rw [Matrix.map_apply, hv, (prVr l S g i j).1]
    ext <;> simp [E]
  have h0 := conj_const S (DD S.F 1) (DD.aug S.F 1) θ hθ (1 + E Y) (1 - E Y)
    (by rw [mul_sub, mul_one, add_mul, one_mul, hEE, add_zero, add_sub_cancel_right])
    (by rw [mul_add, mul_one, sub_mul, one_mul, hEE, sub_zero, sub_add_cancel])
    (fun g => by
      have a1 : E (S.ρ S.F g * Y - Y * S.ρ S.F g) = (S.ρ S.F g).map (algebraMap S.F (DD S.F 1)) * E Y -
          E Y * (S.ρ S.F g).map (algebraMap S.F (DD S.F 1)) := by
        rw [hε, hε, Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, ← Matrix.map_mul, ← Matrix.map_mul,
          Matrix.map_sub _ (map_sub _)]
      have a2 : E Y * (S.ρ S.F g).map (algebraMap S.F (DD S.F 1)) * E Y = 0 := by
        have := hEE (Y * S.ρ S.F g) Y
        rwa [hε (Y * _), Matrix.map_mul, ← Matrix.smul_mul, ← hε] at this
      have a3 := hEE Y Y
      rw [hu, a1]
      generalize (S.ρ S.F g).map (algebraMap S.F (DD S.F 1)) = r at a2 ⊢
      generalize E Y = y at a2 a3 ⊢
      have : (1 + y) * (r + (r * y - y * r)) * (1 - y) =
          r - r * (y * y) + y * r * y - y * r * y * y - y * y * r + y * y * r * y := by noncomm_ring
      rw [this, a2, a3]
      simp)
  ext b
  have h1 := congrArg (fun u => DD.ep' u 0) ((hv _).symm.trans (h0 b))
  have h2 := ((prAdd l S).2.1 b 0).1
  rw [Submodule.coe_zero, add_zero] at h2
  simp only [h2] at h1
  exact h1
