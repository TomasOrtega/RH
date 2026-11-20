import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsHaveFiniteDimensionInvarianceIsomorphism
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalPolarisationVolumeFormSymmetricAmpleStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsCountSqEqDetFormOnTorsionStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SqIsPowGrp

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.AdditionGraph

open GlobalTheory.CechPic
open scoped Kronecker

section Algebra

variable {G H σ κ : Type} [CommGroup G] [CommGroup H] [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in

/- English proof (translation)
Rewrite using `[map_prod, Finset.prod_apply, Fintype.prod_prod_type, Finset.prod_eq_single b]`. Simplify using the standard rewrite rules. Introduce `c _ hc`. Simplify using `[Pi.mulSingle_eq_of_ne' hc]`. Simplify using the standard rewrite rules.
-/
theorem apply_prod_single (Φ : H ≃* (σ → G)) (pt : κ → G) (a : σ × κ → ℕ) (b : σ) :
    Φ (∏ x : σ × κ, Φ.symm (Pi.mulSingle x.1 (pt x.2)) ^ a x) b = ∏ j, pt j ^ a (b, j) := by
  rw [map_prod, Finset.prod_apply, Fintype.prod_prod_type, Finset.prod_eq_single b]
  · simp
  · intro c _ hc
    simp [Pi.mulSingle_eq_of_ne' hc]
  · simp

omit [DecidableEq κ] in

/- English proof (translation)
Establish `hb : ∀ b, Φ y b ^ k = 1` using `fun b => by`. Rewrite using `[← Pi.pow_apply, ← map_pow, hy, map_one, Pi.one_apply]`. Use `choose c hc hu using fun b => h _ (hb b)`. Use `⟨fun x => c x.1 x.2, Φ.injective (funext fun b => ?_), fun c' hc' => funext fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[apply_prod_single]`.

Conclude with `hc b`. Use `congrFun (hu x.1 (fun j => c' (x.1, j)) ?_) x.2` and prove the remaining obligations. Rewrite using `[← hc', apply_prod_single]`.
-/
theorem existsUnique_prod_single (Φ : H ≃* (σ → G)) {k : ℕ} (pt : κ → G)
    (h : ∀ y : G, y ^ k = 1 → ∃! c : κ → ZMod k, ∏ j, pt j ^ (c j).val = y) (y : H) (hy : y ^ k = 1) :
    ∃! c : σ × κ → ZMod k, ∏ x : σ × κ, Φ.symm (Pi.mulSingle x.1 (pt x.2)) ^ (c x).val = y := by
  have hb : ∀ b, Φ y b ^ k = 1 := fun b => by
    rw [← Pi.pow_apply, ← map_pow, hy, map_one, Pi.one_apply]
  choose c hc hu using fun b => h _ (hb b)
  refine ⟨fun x => c x.1 x.2, Φ.injective (funext fun b => ?_), fun c' hc' => funext fun x => ?_⟩
  · rw [apply_prod_single]
    exact hc b
  · refine congrFun (hu x.1 (fun j => c' (x.1, j)) ?_) x.2
    rw [← hc', apply_prod_single]

/- English proof (translation)
Use `Φ.injective (funext fun b => ?_)` and prove the remaining obligations. Rewrite using `[apply_prod_single, hs, Finset.prod_eq_single x.1, Finset.prod_eq_single x.2]`. Simplify using `[ZMod.val_natCast, ← pow_eq_pow_mod _ (h _)]`. Introduce `j _ hj`. Simplify using `[Matrix.one_apply_ne hj]`.

Simplify using the standard rewrite rules. Introduce `a _ ha`. Simplify using `[Pi.mulSingle_eq_of_ne ha]`. Simplify using the standard rewrite rules.
-/
theorem act_prod_single (Φ : H ≃* (σ → G)) {k : ℕ} (pt : κ → G) (h : ∀ j, pt j ^ k = 1) (C : Matrix σ σ ℕ)
    (s : H → H) (hs : ∀ y b, Φ (s y) b = ∏ a, Φ y a ^ C b a) (x : σ × κ) :
    s (Φ.symm (Pi.mulSingle x.1 (pt x.2))) = ∏ x' : σ × κ, Φ.symm (Pi.mulSingle x'.1 (pt x'.2)) ^
      ((C.map (Nat.cast : ℕ → ZMod k) ⊗ₖ (1 : Matrix κ κ (ZMod k))) x' x).val := by
  refine Φ.injective (funext fun b => ?_)
  rw [apply_prod_single, hs, Finset.prod_eq_single x.1, Finset.prod_eq_single x.2]
  · simp [ZMod.val_natCast, ← pow_eq_pow_mod _ (h _)]
  · intro j _ hj
    simp [Matrix.one_apply_ne hj]
  · simp
  · intro a _ ha
    simp [Pi.mulSingle_eq_of_ne ha]
  · simp

/- English proof (translation)
Establish `hlt : a + b < l ^ (a + b)` using `Nat.lt_pow_self hl.one_lt`. Conclude with `Nat.ModEq.eq_of_lt_of_lt ((ZMod.natCast_eq_natCast_iff _ _ _).1 (h (a + b))) (by omega) (by omega)`.
-/
theorem eq_of_forall_zmod {l a b : ℕ} (hl : l.Prime) (h : ∀ j, (a : ZMod (l ^ j)) = b) : a = b := by
  have hlt : a + b < l ^ (a + b) := Nat.lt_pow_self hl.one_lt
  exact Nat.ModEq.eq_of_lt_of_lt ((ZMod.natCast_eq_natCast_iff _ _ _).1 (h (a + b))) (by omega) (by omega)

end Algebra

section Geometry

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

/- English proof (translation)
Rewrite using `[Out.linComb, List.prod_ofFn]`. Conclude with `ε.prod_comp fun x => y x ^ a x`.
-/
theorem linComb_equiv {T : Over S} {n : ℕ} {σ : Type} [Fintype σ] (ε : Fin n ≃ σ) (y : σ → (T ⟶ B)) (a : σ → ℕ) :
    Out.linComb (fun i => y (ε i)) (fun i => a (ε i)) = ∏ x, y x ^ a x := by
  rw [Out.linComb, List.prod_ofFn]
  exact ε.prod_comp fun x => y x ^ a x

def pointsEquiv (e : B ≅ A ⊗ A) [IsMonHom (e.hom ≫ fst A A)] [IsMonHom (e.hom ≫ snd A A)] (T : Over S) :
    (T ⟶ B) ≃* (Fin 2 → (T ⟶ A)) where
  toFun x := ![x ≫ e.hom ≫ fst A A, x ≫ e.hom ≫ snd A A]
  invFun y := lift (y 0) (y 1) ≫ e.inv
  left_inv x := by
    rw [← cancel_mono e.hom]
    ext <;> simp
  right_inv y := by
    funext i
    fin_cases i <;> simp
  map_mul' x y := by
    funext i
    fin_cases i
    · exact MonObj.mul_comp x y (e.hom ≫ fst A A)
    · exact MonObj.mul_comp x y (e.hom ≫ snd A A)

omit [IsCommMonObj B] in

/- English proof (translation)
Rewrite using `[MonObj.comp_mul, IsMonHom.one_hom, IsMonHom.one_hom]`. Establish `e₁ : (η[A] : 𝟙_ _ ⟶ A) = 1` using `by rw [Hom.one_def]; simp`. Rewrite using `[e₁, _root_.mul_one]`. Use `mul_hom := by`. Establish `e₁ : μ[B] = fst B B * snd B B` using `by simp [Hom.mul_def]`.

Establish `e₂ : ((p * q) ⊗ₘ (p * q)) ≫ μ[A] = (fst B B ≫ (p * q)) * (snd B B ≫ (p * q))`. Rewrite using `[Hom.mul_def (fst B B ≫ (p * q))]`. Use `congr 1`. Rewrite using `[e₂, e₁]`. Simplify using `only [MonObj.comp_mul, MonObj.mul_comp]`.

Conclude with `mul_mul_mul_comm _ _ _ _`.
-/
theorem isMonHom_mul (p q : B ⟶ A) [IsMonHom p] [IsMonHom q] : IsMonHom (p * q) where
  one_hom := by
    rw [MonObj.comp_mul, IsMonHom.one_hom, IsMonHom.one_hom]
    have e₁ : (η[A] : 𝟙_ _ ⟶ A) = 1 := by rw [Hom.one_def]; simp
    rw [e₁, _root_.mul_one]
  mul_hom := by
    have e₁ : μ[B] = fst B B * snd B B := by simp [Hom.mul_def]
    have e₂ : ((p * q) ⊗ₘ (p * q)) ≫ μ[A] = (fst B B ≫ (p * q)) * (snd B B ≫ (p * q)) := by
      rw [Hom.mul_def (fst B B ≫ (p * q))]
      congr 1
    rw [e₂, e₁]
    simp only [MonObj.comp_mul, MonObj.mul_comp]
    exact mul_mul_mul_comm _ _ _ _

omit [IsCommMonObj A] [IsCommMonObj B] in
/- English proof (translation)
Simplify using `only [lam, map_add]`. Normalize the expressions using the abelian group laws.
-/
theorem lam_add {T : Over S} (c d : Pic B.left) (x y : T ⟶ B) : lam (c + d) x y = lam c x y + lam d x y := by
  simp only [lam, map_add]
  abel

end Geometry

end GlobalTheory.AdditionGraph

namespace GlobalTheory

open GlobalTheory.CechPic GlobalTheory.AdditionGraph
open scoped Kronecker

/- English proof (translation)
Introduce `laws laws₂ K _ _ P N hN e he`. Take `⟨Q, φ, hp, hq, hg, hQ⟩` from `SquarePol.exists_square K P`. Use `P.isAb.comm` as an intermediate fact. Use `Q.isAb.comm` as an intermediate fact. Use `P.isAb.proper` as an intermediate fact.

Use `Q.isAb.proper` as an intermediate fact. Establish `hL` using `P.isLB`. Take `⟨rig, hrig⟩` from `P.rigid`. Take `⟨cub⟩` from `(laws.cube _ P ⟨P.L, rig, hL, hrig⟩ rfl).1`. Establish `hΘ : ∃ t : LB.Gen (Theta P.A P.L), t.IsGen` using `⟨cub.t, cub.isGen⟩`.

Take `⟨-, -, hsym, -, -, htor⟩` from `GlobalTheory.T.principalPolarisation_volume_form_symmetric_ample laws laws₂ K P`. Set `Φ` to `pointsEquiv φ`. Use `set p := φ.hom ≫ fst P.A P.A with hpd`. Use `set q := φ.hom ≫ snd P.A P.A with hqd`. Establish `hpq` using `isMonHom_mul p q`.

Use `set c := cls P.L hL with hc`. Set `M : LB Q.A.left` to `LB.LinComb P.L (K := Fin 3) ![p.left, q.left, (p * q).left] ![(N : ℤ), (N : ℤ), (N : ℤ)]`. Establish `hM : M.IsLB` using `LB.isLB_linComb hL _ _`. Establish `cM : cls M hM = N • (pull p.left c + pull q.left c + pull (p * q).left c)`. Rewrite using `[cls_linComb hL, Fin.sum_univ_three]`.

Simplify using `[← hc]`. Establish `cQ : cls Q.L Q.isLB = pull p.left c + pull q.left c`. Rewrite using `[(cls_eq_iff Q.isLB (LB.isLB_linComb hL _ _)).2 hQ, cls_linComb hL, Fin.sum_univ_two]`. Simplify using `[← hc]`. Establish `hamp : Out.RelAmple Q.A M`.

Take `⟨n, hn, hgen⟩` from `((relAmple_iff_isAmpleLB_of_isAffine P.A hL).1 P.ample).exists_isGenerated_pow`. Establish `a₁` using `(isAmpleLB_pow_iff Q.isLB (k := n * N) (Nat.mul_pos hn hN)).2 ((relAmple_iff_isAmpleLB_of_isAffine Q.A Q.isLB).1 Q.ample)`. Establish `a₂` using `(hgen.pow N).pull (p * q).left`. Establish `hMn : (lbPow M n).IsLB` using `LB.isLB_linComb hM _ _`. Use `(relAmple_iff_isAmpleLB_of_isAffine Q.A hM).2 ((isAmpleLB_pow_iff hM hn).1 (a₁.tensor_isGenerated a₂ hMn ((cls_eq_zero_iff (LB.isLB_div (LB.isLB_div hMn a₁.isLB) a₂.isLB)).1 ?_)))` and prove the remaining obligations.

Rewrite using `[cls_div (LB.isLB_div hMn a₁.isLB) a₂.isLB, cls_div hMn a₁.isLB, cls_pull (hgen.pow N).isLB, cls_lbPow hgen.isLB, cls_lbPow hL, cls_lbPow hM, cls_lbPow Q.isLB, cM, cQ, map_nsmul, map_nsmul, ← hc]`. Use `module`. Establish `hsymM : SymB M`. Establish `e₁ : pull (GrpObj.inv : P.A ⟶ P.A).left c = c` using `((cls_eq_iff hL (pull_isLB hL _)).2 hsym).symm`. Establish `e₂ : ∀ (r : Q.A ⟶ P.A) [IsMonHom r], pull (GrpObj.inv : Q.A ⟶ Q.A).left (pull r.left c) = pull r.left c` using `fun r _ => by`.

Rewrite using `[← pull_comp, ← Over.comp_left, GrpObj.inv_hom, Over.comp_left, pull_comp, e₁]`. Use `(cls_eq_iff hM (pull_isLB hM _)).1 ?_` and prove the remaining obligations. Rewrite using `[cls_pull hM, cM, map_nsmul, map_add, map_add, e₂, e₂, e₂]`. Set `C : Matrix (Fin 2) (Fin 2) ℕ` to `!![2 * N, N; N, 2 * N]`. Set `s : Q.A ⟶ Q.A` to `(Φ Q.A).symm ![p ^ (2 * N) * q ^ N, p ^ N * q ^ (2 * N)]`.

Establish `sp : s ≫ p = p ^ (2 * N) * q ^ N` using `congrFun ((Φ Q.A).apply_symm_apply _) 0`. Establish `sq : s ≫ q = p ^ N * q ^ (2 * N)` using `congrFun ((Φ Q.A).apply_symm_apply _) 1`. Establish `hs : ∀ {T : Over (Sp K)} (y : T ⟶ Q.A) (b : Fin 2), Φ T (y ≫ s) b = ∏ a, Φ T y a ^ C b a`. Introduce `T y b`. Rewrite using `[Fin.prod_univ_two]`.

Use `fin_cases b`. Express the relevant statement in the definitionally equal form `(y ≫ s) ≫ p = (y ≫ p) ^ (2 * N) * (y ≫ q) ^ N`. Rewrite using `[Category.assoc, sp, MonObj.comp_mul, MonObj.comp_pow, MonObj.comp_pow]`. Express the relevant statement in the definitionally equal form `(y ≫ s) ≫ q = (y ≫ p) ^ N * (y ≫ q) ^ (2 * N)`. Rewrite using `[Category.assoc, sq, MonObj.comp_mul, MonObj.comp_pow, MonObj.comp_pow]`.

Establish `hform : FormIs Q M s`. Use `⟨laws.rigidity _ _ _ Q.isAb Q.isAb _ ?_, ?_⟩` and prove the remaining obligations. Establish `e₁ : (η[Q.A] : 𝟙_ _ ⟶ Q.A) = 1` using `by rw [Hom.one_def]; simp`. Rewrite using `[e₁]`. Use `(Φ _).injective (funext fun b => ?_)` and prove the remaining obligations.

Rewrite using `[hs, map_one]`. Simplify using the standard rewrite rules. Establish `mr : ∀ {T : Over (Sp K)} (x y z : T ⟶ P.A), lam c x (y * z) = lam c x y + lam c x z` using `fun x y z => by`. Rewrite using `[lam_comm, lam_mul_left hL hΘ, lam_comm _ y, lam_comm _ z]`. Use `(cls_eq_iff (LB.isLB_linComb hM _ _) (LB.isLB_linComb Q.isLB _ _)).1 ?_` and prove the remaining obligations.

Use `(cls_cube_two hM _ _ _).trans (Eq.trans ?_ (cls_cube_two Q.isLB _ _ _).symm)` and prove the remaining obligations. Rewrite using `[cM, cQ, lam_nsmul]`. Simplify using `only [lam_add, lam_pull, Category.assoc, sp, sq, MonObj.comp_mul, MonObj.comp_pow, mr]`. Simplify using `only [hc, lam_mul_left hL hΘ, lam_pow_right hL hΘ]`. Use `module`.

Choose the witnesses or unpack the hypotheses as in `⟨l, hl, hlK⟩ : ∃ l : ℕ, l.Prime ∧ (l : K) ≠ 0 := by`. Distinguish the cases in `h : ((2 : ℕ) : K) = 0`. Use `⟨3, Nat.prime_three, fun h' => one_ne_zero (α := K) ?_⟩` and prove the remaining obligations. Move the coercions through the operations in `at h h'`. Take the linear combination `h' - h`.

Conclude with `⟨2, Nat.prime_two, h⟩`. Take `⟨δ, -, hδ, hdet⟩` from `GlobalTheory.T.sections_count_sq_eq_det_form_on_torsion laws laws₂ K Q M s l hl hlK hM hamp hsymM hform`. Establish `hsq : δ ^ 2 = ((3 * N ^ 2) ^ P.g) ^ 2`. Use `eq_of_forall_zmod hl fun j => ?_` and prove the remaining obligations. Take `⟨pt, ⟨h₀, h₁, h₂⟩, -⟩` from `htor (l ^ j) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hlK)`.

Set `ε : Fin (2 * Q.g) ≃ Fin 2 × Fin (2 * P.g)` to `(finCongr (by rw [hg])).trans finProdFinEquiv.symm`. Set `z : Fin 2 × Fin (2 * P.g) → (Out.baseOver (Sp K) ⟶ Q.A)` to `fun x => (Φ _).symm (Pi.mulSingle x.1 (pt x.2))`. Set `D` to `C.map (Nat.cast : ℕ → ZMod (l ^ j)) ⊗ₖ (1 : Matrix (Fin (2 * P.g)) (Fin (2 * P.g)) (ZMod (l ^ j)))`. Establish `h₃` using `hdet j (fun i => z (ε i)) (D.submatrix ε ε) ⟨h₀, fun i => ?_, fun y hy => ?_⟩ ⟨h₀, fun i => ?_⟩`. Establish `hC : (C.map (Nat.cast : ℕ → ZMod (l ^ j))).det = 3 * (N : ZMod (l ^ j)) ^ 2`.

Simplify using `[C, Matrix.det_fin_two]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h₃` using `[Matrix.det_submatrix_equiv_self, Matrix.det_kronecker, hC, Matrix.det_one, one_pow, _root_.mul_one, Fintype.card_fin]`. Use `push_cast`. Rewrite using `[h₃, ← pow_mul, _root_.mul_comm P.g]`.

Rewrite using `[← map_pow, ← Pi.mulSingle_pow, h₁, Pi.mulSingle_one, map_one]`. Establish `h₄` using `existsUnique_prod_single (Φ _) pt (fun y hy => by`. Simplify `h₂ y hy) y hy` using `only [Out.linComb, List.prod_ofFn]`. Use `((Equiv.arrowCongr ε.symm (Equiv.refl _)).existsUnique_congr fun a => ?_).1 h₄` and prove the remaining obligations. Rewrite using `[← linComb_equiv ε z fun x => (a x).val]`.

Both sides reduce to the same expression. Conclude with `(act_prod_single (Φ _) pt h₁ C (· ≫ s) hs (ε i)).trans (linComb_equiv ε z fun x => (D x (ε i)).val).symm`. Establish `hδ' : δ = (3 * N ^ 2) ^ P.g` using `Nat.pow_left_injective two_ne_zero hsq`. Establish `H` using `hδ e he`. Rewrite `H` using `[show δ * e ^ Q.g = 3 ^ P.g * (N * e) ^ (2 * P.g) by rw [hδ', hg]; ring]`.

Set `M'` to `LB.LinComb P.L (K := Fin 3) ![(fst P.A P.A).left, (snd P.A P.A).left, (fst P.A P.A * snd P.A P.A).left] ![(N : ℤ), (N : ℤ), (N : ℤ)]`. Establish `hM' : M'.IsLB` using `LB.isLB_linComb hL _ _`. Establish `hMe : (lbPow M e).IsLB` using `LB.isLB_linComb hM _ _`. Establish `hMe' : (lbPow M' e).IsLB` using `LB.isLB_linComb hM' _ _`. Use `((SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K _ (P.A ⊗ P.A).hom _ hMe').2.2.2.2.2 _ ((Over.forget _).mapIso φ) _).2 ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `SectionsHaveFiniteDimension (φ.hom.left ≫ (P.A ⊗ P.A).hom) ((lbPow M' e).pull φ.hom.left) _`. Rewrite using `[Over.w]`. Use `((SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K _ Q.A.hom _ hMe).2.1 _ (pull_isLB hMe' _) ?_).1 _ H` and prove the remaining obligations. Use `(cls_eq_iff hMe (pull_isLB hMe' _)).1 ?_` and prove the remaining obligations. Rewrite using `[cls_pull hMe', cls_lbPow hM, cls_lbPow hM', cM, cls_linComb hL, Fin.sum_univ_three]`.

Establish `e₁ : ∀ r : P.A ⊗ P.A ⟶ P.A, pull φ.hom.left (pull r.left c) = pull (φ.hom ≫ r).left c` using `fun r => by`. Rewrite using `[Over.comp_left, pull_comp]`. Simplify using `only [← hc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, map_nsmul, map_add, map_zsmul, e₁, MonObj.comp_mul, ← hpd, ← hqd]`. Use `module`.
-/
theorem sectionsDim_additionGraph_principalPolarisation : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : ℕ), 1 ≤ N → ∀ e ≥ 1, SectionsHaveFiniteDimension (P.A ⊗ P.A).hom (lbPow (LB.LinComb P.L (K := Fin 3) ![(fst P.A P.A).left, (snd P.A P.A).left, (fst P.A P.A * snd P.A P.A).left] ![(N : ℤ), (N : ℤ), (N : ℤ)]) e) (3 ^ P.g * (N * e) ^ (2 * P.g)) := by
  intro laws laws₂ K _ _ P N hN e he
  obtain ⟨Q, φ, hp, hq, hg, hQ⟩ := SquarePol.exists_square K P
  have := P.isAb.comm
  have := Q.isAb.comm
  have := P.isAb.proper
  have := Q.isAb.proper
  have hL := P.isLB
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨cub⟩ := (laws.cube _ P ⟨P.L, rig, hL, hrig⟩ rfl).1
  have hΘ : ∃ t : LB.Gen (Theta P.A P.L), t.IsGen := ⟨cub.t, cub.isGen⟩
  obtain ⟨-, -, hsym, -, -, htor⟩ := GlobalTheory.T.principalPolarisation_volume_form_symmetric_ample laws laws₂ K P
  let Φ := pointsEquiv φ
  set p := φ.hom ≫ fst P.A P.A with hpd
  set q := φ.hom ≫ snd P.A P.A with hqd
  have hpq := isMonHom_mul p q
  set c := cls P.L hL with hc

  let M : LB Q.A.left := LB.LinComb P.L (K := Fin 3) ![p.left, q.left, (p * q).left] ![(N : ℤ), (N : ℤ), (N : ℤ)]
  have hM : M.IsLB := LB.isLB_linComb hL _ _
  have cM : cls M hM = N • (pull p.left c + pull q.left c + pull (p * q).left c) := by
    rw [cls_linComb hL, Fin.sum_univ_three]
    simp [← hc]
  have cQ : cls Q.L Q.isLB = pull p.left c + pull q.left c := by
    rw [(cls_eq_iff Q.isLB (LB.isLB_linComb hL _ _)).2 hQ, cls_linComb hL, Fin.sum_univ_two]
    simp [← hc]

  have hamp : Out.RelAmple Q.A M := by
    obtain ⟨n, hn, hgen⟩ := ((relAmple_iff_isAmpleLB_of_isAffine P.A hL).1 P.ample).exists_isGenerated_pow
    have a₁ := (isAmpleLB_pow_iff Q.isLB (k := n * N) (Nat.mul_pos hn hN)).2
      ((relAmple_iff_isAmpleLB_of_isAffine Q.A Q.isLB).1 Q.ample)
    have a₂ := (hgen.pow N).pull (p * q).left
    have hMn : (lbPow M n).IsLB := LB.isLB_linComb hM _ _
    refine (relAmple_iff_isAmpleLB_of_isAffine Q.A hM).2 ((isAmpleLB_pow_iff hM hn).1
      (a₁.tensor_isGenerated a₂ hMn ((cls_eq_zero_iff (LB.isLB_div (LB.isLB_div hMn a₁.isLB) a₂.isLB)).1 ?_)))
    rw [cls_div (LB.isLB_div hMn a₁.isLB) a₂.isLB, cls_div hMn a₁.isLB, cls_pull (hgen.pow N).isLB,
      cls_lbPow hgen.isLB, cls_lbPow hL, cls_lbPow hM, cls_lbPow Q.isLB, cM, cQ, map_nsmul, map_nsmul, ← hc]
    module

  have hsymM : SymB M := by
    have e₁ : pull (GrpObj.inv : P.A ⟶ P.A).left c = c :=
      ((cls_eq_iff hL (pull_isLB hL _)).2 hsym).symm
    have e₂ : ∀ (r : Q.A ⟶ P.A) [IsMonHom r],
        pull (GrpObj.inv : Q.A ⟶ Q.A).left (pull r.left c) = pull r.left c := fun r _ => by
      rw [← pull_comp, ← Over.comp_left, GrpObj.inv_hom, Over.comp_left, pull_comp, e₁]
    refine (cls_eq_iff hM (pull_isLB hM _)).1 ?_
    rw [cls_pull hM, cM, map_nsmul, map_add, map_add, e₂, e₂, e₂]

  let C : Matrix (Fin 2) (Fin 2) ℕ := !![2 * N, N; N, 2 * N]
  let s : Q.A ⟶ Q.A := (Φ Q.A).symm ![p ^ (2 * N) * q ^ N, p ^ N * q ^ (2 * N)]
  have sp : s ≫ p = p ^ (2 * N) * q ^ N := congrFun ((Φ Q.A).apply_symm_apply _) 0
  have sq : s ≫ q = p ^ N * q ^ (2 * N) := congrFun ((Φ Q.A).apply_symm_apply _) 1
  have hs : ∀ {T : Over (Sp K)} (y : T ⟶ Q.A) (b : Fin 2), Φ T (y ≫ s) b = ∏ a, Φ T y a ^ C b a := by
    intro T y b
    rw [Fin.prod_univ_two]
    fin_cases b
    · change (y ≫ s) ≫ p = (y ≫ p) ^ (2 * N) * (y ≫ q) ^ N
      rw [Category.assoc, sp, MonObj.comp_mul, MonObj.comp_pow, MonObj.comp_pow]
    · change (y ≫ s) ≫ q = (y ≫ p) ^ N * (y ≫ q) ^ (2 * N)
      rw [Category.assoc, sq, MonObj.comp_mul, MonObj.comp_pow, MonObj.comp_pow]
  have hform : FormIs Q M s := by
    refine ⟨laws.rigidity _ _ _ Q.isAb Q.isAb _ ?_, ?_⟩
    · have e₁ : (η[Q.A] : 𝟙_ _ ⟶ Q.A) = 1 := by rw [Hom.one_def]; simp
      rw [e₁]
      refine (Φ _).injective (funext fun b => ?_)
      rw [hs, map_one]
      simp
    · have mr : ∀ {T : Over (Sp K)} (x y z : T ⟶ P.A), lam c x (y * z) = lam c x y + lam c x z := fun x y z => by
        rw [lam_comm, lam_mul_left hL hΘ, lam_comm _ y, lam_comm _ z]
      refine (cls_eq_iff (LB.isLB_linComb hM _ _) (LB.isLB_linComb Q.isLB _ _)).1 ?_
      refine (cls_cube_two hM _ _ _).trans (Eq.trans ?_ (cls_cube_two Q.isLB _ _ _).symm)
      rw [cM, cQ, lam_nsmul]
      simp only [lam_add, lam_pull, Category.assoc, sp, sq, MonObj.comp_mul, MonObj.comp_pow, mr]
      simp only [hc, lam_mul_left hL hΘ, lam_pow_right hL hΘ]
      module

  obtain ⟨l, hl, hlK⟩ : ∃ l : ℕ, l.Prime ∧ (l : K) ≠ 0 := by
    by_cases h : ((2 : ℕ) : K) = 0
    · refine ⟨3, Nat.prime_three, fun h' => one_ne_zero (α := K) ?_⟩
      push_cast at h h'
      linear_combination h' - h
    · exact ⟨2, Nat.prime_two, h⟩
  obtain ⟨δ, -, hδ, hdet⟩ := GlobalTheory.T.sections_count_sq_eq_det_form_on_torsion laws laws₂ K Q M s l hl hlK hM hamp hsymM hform
  have hsq : δ ^ 2 = ((3 * N ^ 2) ^ P.g) ^ 2 := by
    refine eq_of_forall_zmod hl fun j => ?_
    obtain ⟨pt, ⟨h₀, h₁, h₂⟩, -⟩ := htor (l ^ j) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hlK)
    let ε : Fin (2 * Q.g) ≃ Fin 2 × Fin (2 * P.g) := (finCongr (by rw [hg])).trans finProdFinEquiv.symm
    let z : Fin 2 × Fin (2 * P.g) → (Out.baseOver (Sp K) ⟶ Q.A) := fun x => (Φ _).symm (Pi.mulSingle x.1 (pt x.2))
    let D := C.map (Nat.cast : ℕ → ZMod (l ^ j)) ⊗ₖ (1 : Matrix (Fin (2 * P.g)) (Fin (2 * P.g)) (ZMod (l ^ j)))
    have h₃ := hdet j (fun i => z (ε i)) (D.submatrix ε ε) ⟨h₀, fun i => ?_, fun y hy => ?_⟩
      ⟨h₀, fun i => ?_⟩
    · have hC : (C.map (Nat.cast : ℕ → ZMod (l ^ j))).det = 3 * (N : ZMod (l ^ j)) ^ 2 := by
        simp [C, Matrix.det_fin_two]
        ring
      rw [Matrix.det_submatrix_equiv_self, Matrix.det_kronecker, hC, Matrix.det_one, one_pow, _root_.mul_one,
        Fintype.card_fin] at h₃
      push_cast
      rw [h₃, ← pow_mul, _root_.mul_comm P.g]
    · rw [← map_pow, ← Pi.mulSingle_pow, h₁, Pi.mulSingle_one, map_one]
    · have h₄ := existsUnique_prod_single (Φ _) pt (fun y hy => by
        simpa only [Out.linComb, List.prod_ofFn] using h₂ y hy) y hy
      refine ((Equiv.arrowCongr ε.symm (Equiv.refl _)).existsUnique_congr fun a => ?_).1 h₄
      rw [← linComb_equiv ε z fun x => (a x).val]
      rfl
    · exact (act_prod_single (Φ _) pt h₁ C (· ≫ s) hs (ε i)).trans
        (linComb_equiv ε z fun x => (D x (ε i)).val).symm
  have hδ' : δ = (3 * N ^ 2) ^ P.g := Nat.pow_left_injective two_ne_zero hsq
  have H := hδ e he
  rw [show δ * e ^ Q.g = 3 ^ P.g * (N * e) ^ (2 * P.g) by rw [hδ', hg]; ring] at H

  let M' := LB.LinComb P.L (K := Fin 3)
    ![(fst P.A P.A).left, (snd P.A P.A).left, (fst P.A P.A * snd P.A P.A).left] ![(N : ℤ), (N : ℤ), (N : ℤ)]
  have hM' : M'.IsLB := LB.isLB_linComb hL _ _
  have hMe : (lbPow M e).IsLB := LB.isLB_linComb hM _ _
  have hMe' : (lbPow M' e).IsLB := LB.isLB_linComb hM' _ _
  refine ((SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K _ (P.A ⊗ P.A).hom _ hMe').2.2.2.2.2 _ ((Over.forget _).mapIso φ) _).2 ?_
  change SectionsHaveFiniteDimension (φ.hom.left ≫ (P.A ⊗ P.A).hom) ((lbPow M' e).pull φ.hom.left) _
  rw [Over.w]
  refine ((SecDim.lbPow_mul_and_pull_and_sectionsFiniteDim_iso_invariant K _ Q.A.hom _ hMe).2.1 _ (pull_isLB hMe' _) ?_).1 _ H
  refine (cls_eq_iff hMe (pull_isLB hMe' _)).1 ?_
  rw [cls_pull hMe', cls_lbPow hM, cls_lbPow hM', cM, cls_linComb hL, Fin.sum_univ_three]
  have e₁ : ∀ r : P.A ⊗ P.A ⟶ P.A, pull φ.hom.left (pull r.left c) = pull (φ.hom ≫ r).left c := fun r => by
    rw [Over.comp_left, pull_comp]
  simp only [← hc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, map_nsmul, map_add, map_zsmul, e₁,
    MonObj.comp_mul, ← hpd, ← hqd]
  module

end GlobalTheory
