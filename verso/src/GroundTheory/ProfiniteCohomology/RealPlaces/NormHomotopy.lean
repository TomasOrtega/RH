import Mathlib
import GroundTheory.ProfiniteCohomology.RealPlaces.ConeDefs
import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.CupLeibniz
import GroundTheory.ProfiniteCohomology.CoinducedModules.Acyclic
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory groupCohomology

universe u

section Tuple

variable {α : Type*}

def consTuple {s m : ℕ} (h : s = m + 1) (a : α) (g : Fin m → α) : Fin s → α :=
  fun i => if hi : (i : ℕ) = 0 then a else g ⟨i - 1, by omega⟩

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `[consTuple]`. Simplify using `only [consTuple, Fin.val_succ, Nat.add_one_ne_zero, dite_false, Fin.cons_succ]`. Use `congr 1`.
-/
theorem consTuple_rfl {m : ℕ} (a : α) (g : Fin m → α) :
    consTuple (rfl : m + 1 = m + 1) a g = Fin.cons a g := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [consTuple]
  · simp only [consTuple, Fin.val_succ, Nat.add_one_ne_zero, dite_false, Fin.cons_succ]
    congr 1

/- English proof (translation)
Use `continuous_pi fun i => ?_` and prove the remaining obligations. Unfold `consTuple`. Use `split_ifs`. Conclude with `continuous_const`. Conclude with `continuous_apply _`.
-/
theorem continuous_consTuple [TopologicalSpace α] {s m : ℕ} (h : s = m + 1) (a : α) :
    Continuous (consTuple h a) := by
  refine continuous_pi fun i => ?_
  unfold consTuple
  split_ifs
  · exact continuous_const
  · exact continuous_apply _

end Tuple

section Homotopy

variable {k F : Type u} [CommRing k] [Group F] [Fintype F] {X Y Z : Rep.{u} k F}
  (μ : X ⊗ Y ⟶ Z)

noncomputable def normHomotopyFun {s m : ℕ} (h : s = m + 1) (e : X) (y : (Fin s → F) → Y) : (Fin m → F) → Z :=
  fun g => ∑ a : F, Z.ρ a (μ.hom ((e ⊗ₜ[k] y (consTuple h a⁻¹ g) : (X ⊗ Y : Rep k F))))

/- English proof (translation)
Use function extensionality and compare the values at `g`. Simplify using `only [normHomotopyFun, Pi.add_apply, TensorProduct.add_tmul, map_add, Finset.sum_add_distrib]`.
-/
theorem normHomotopyFun_add_left {s m : ℕ} (h : s = m + 1) (e e' : X) (y : (Fin s → F) → Y) :
    normHomotopyFun μ h (e + e') y = normHomotopyFun μ h e y + normHomotopyFun μ h e' y := by
  funext g
  simp only [normHomotopyFun, Pi.add_apply, TensorProduct.add_tmul, map_add,
    Finset.sum_add_distrib]

/- English proof (translation)
Use function extensionality and compare the values at `g`. Simplify using `only [normHomotopyFun, Pi.smul_apply, ← TensorProduct.smul_tmul', map_smul, Finset.smul_sum]`.
-/
theorem normHomotopyFun_smul_left {s m : ℕ} (h : s = m + 1) (c : k) (e : X) (y : (Fin s → F) → Y) :
    normHomotopyFun μ h (c • e) y = c • normHomotopyFun μ h e y := by
  funext g
  simp only [normHomotopyFun, Pi.smul_apply, ← TensorProduct.smul_tmul', map_smul, Finset.smul_sum]

/- English proof (translation)
Use function extensionality and compare the values at `g`. Simplify using `only [normHomotopyFun, Pi.add_apply, TensorProduct.tmul_add, map_add, Finset.sum_add_distrib]`.
-/
theorem normHomotopyFun_add_right {s m : ℕ} (h : s = m + 1) (e : X) (y y' : (Fin s → F) → Y) :
    normHomotopyFun μ h e (y + y') = normHomotopyFun μ h e y + normHomotopyFun μ h e y' := by
  funext g
  simp only [normHomotopyFun, Pi.add_apply, TensorProduct.tmul_add, map_add,
    Finset.sum_add_distrib]

/- English proof (translation)
Use function extensionality and compare the values at `g`. Simplify using `only [normHomotopyFun, Pi.smul_apply, TensorProduct.tmul_smul, map_smul, Finset.smul_sum]`.
-/
theorem normHomotopyFun_smul_right {s m : ℕ} (h : s = m + 1) (c : k) (e : X)
    (y : (Fin s → F) → Y) :
    normHomotopyFun μ h e (c • y) = c • normHomotopyFun μ h e y := by
  funext g
  simp only [normHomotopyFun, Pi.smul_apply, TensorProduct.tmul_smul, map_smul, Finset.smul_sum]

/- English proof (translation)
Establish `h1 : ∀ a : F, Z.ρ a (μ.hom ((e ⊗ₜ[k] Y.ρ a⁻¹ b : (X ⊗ Y : Rep k F)))) = μ.hom ((X.ρ a e ⊗ₜ[k] b : (X ⊗ Y : Rep k F)))` using `fun a => by`. Establish `h2 : ((X ⊗ Y).ρ a) ((e ⊗ₜ[k] Y.ρ a⁻¹ b : (X ⊗ Y : Rep k F))) = ((X.ρ a e ⊗ₜ[k] b : (X ⊗ Y : Rep k F)))`. Express the relevant statement in the definitionally equal form `TensorProduct.map (X.ρ a) (Y.ρ a) (e ⊗ₜ[k] Y.ρ a⁻¹ b) = _`. Rewrite using `[TensorProduct.map_tmul, Representation.self_inv_apply]`. Conclude with `(Rep.hom_comm_apply μ a _).symm.trans (congrArg _ h2)`.

Rewrite using `[Finset.sum_congr rfl fun a _ => h1 a, ← map_sum, ← TensorProduct.sum_tmul]`. Use `congr 2`. Simplify using `[Representation.norm]`.
-/
theorem sum_ρ_μ_tmul_ρ_inv (e : X) (b : Y) :
    ∑ a : F, Z.ρ a (μ.hom ((e ⊗ₜ[k] Y.ρ a⁻¹ b : (X ⊗ Y : Rep k F)))) =
      μ.hom ((X.ρ.norm e ⊗ₜ[k] b : (X ⊗ Y : Rep k F))) := by
  have h1 : ∀ a : F, Z.ρ a (μ.hom ((e ⊗ₜ[k] Y.ρ a⁻¹ b : (X ⊗ Y : Rep k F)))) =
      μ.hom ((X.ρ a e ⊗ₜ[k] b : (X ⊗ Y : Rep k F))) := fun a => by
    have h2 : ((X ⊗ Y).ρ a) ((e ⊗ₜ[k] Y.ρ a⁻¹ b : (X ⊗ Y : Rep k F))) =
        ((X.ρ a e ⊗ₜ[k] b : (X ⊗ Y : Rep k F))) := by
      change TensorProduct.map (X.ρ a) (Y.ρ a) (e ⊗ₜ[k] Y.ρ a⁻¹ b) = _
      rw [TensorProduct.map_tmul, Representation.self_inv_apply]
    exact (Rep.hom_comm_apply μ a _).symm.trans (congrArg _ h2)
  rw [Finset.sum_congr rfl fun a _ => h1 a, ← map_sum, ← TensorProduct.sum_tmul]
  congr 2
  simp [Representation.norm]

/- English proof (translation)
Use function extensionality and compare the values at `g`. Establish `hdy : ∀ a : F, (inhomogeneousCochains.d Y (m + 1)).hom y (Fin.cons a⁻¹ g) = Y.ρ a⁻¹ (y g) - y (Fin.cons (a⁻¹ * g 0) fun i => g i.succ) + ∑ j : Fin (m + 1), (-1 : k) ^ ((j : ℕ) + 2) • y (Fin.cons a⁻¹ (Fin.contractNth j (· * ·) g))`. Introduce `a`. Rewrite using `[inhomogeneousCochains.d_hom_apply, Fin.sum_univ_succ (n := m + 1)]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ, contractNth_zero_cons, contractNth_succ_cons, Fin.val_zero, Fin.val_succ, zero_add, pow_one, neg_one_smul]`.

Establish `e2 : ∀ j : Fin (m + 1), (j : ℕ) + 1 + 1 = (j : ℕ) + 2` using `fun _ => rfl`. Simplify using `only [e2]`. Normalize the expressions using the abelian group laws. Establish `hsplit : normHomotopyFun μ rfl e ((inhomogeneousCochains.d Y (m + 1)).hom y) g = μ.hom ((X.ρ.norm e ⊗ₜ[k] y g : (X ⊗ Y : Rep k F))) - Z.ρ (g 0) (normHomotopyFun μ rfl e y fun i => g i.succ) + ∑ j : Fin (m + 1), (-1 : k) ^ ((j : ℕ) + 2) • normHomotopyFun μ rfl e y (Fin.contractNth …`. Simplify using `only [normHomotopyFun, consTuple_rfl]`.

Simplify using `only [hdy, TensorProduct.tmul_add, TensorProduct.tmul_sub, TensorProduct.tmul_sum, TensorProduct.tmul_smul, map_add, map_sub, map_sum, map_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib]`. Rewrite using `[sum_ρ_μ_tmul_ρ_inv μ e (y g), Finset.sum_comm (β := Z.V)]`. Use `congr 2`. Use `(Fintype.sum_equiv (Equiv.mulLeft (g 0)) _ _ fun a => ?_).symm` and prove the remaining obligations. Simplify using `only [Equiv.coe_mulLeft, mul_inv_rev, inv_mul_cancel_right, map_mul, Module.End.mul_apply]`.

Use function extensionality and compare the values at `j`. Rewrite using `[Finset.smul_sum]`. Rewrite using `[Pi.add_apply, inhomogeneousCochains.d_hom_apply, hsplit]`. Establish `hpow : ∀ j : Fin (m + 1), (-1 : k) ^ ((j : ℕ) + 2) = -(-1 : k) ^ ((j : ℕ) + 1)` using `fun j => by rw [pow_succ, mul_neg_one]`. Simplify using `only [hpow, neg_smul, Finset.sum_neg_distrib]`.

Normalize the expressions using the abelian group laws.
-/
theorem normHomotopyFun_d_add {m : ℕ} (e : X) (y : (Fin (m + 1) → F) → Y) :
    (inhomogeneousCochains.d Z m).hom (normHomotopyFun μ rfl e y) +
        normHomotopyFun μ rfl e ((inhomogeneousCochains.d Y (m + 1)).hom y) =
      fun g => μ.hom ((X.ρ.norm e ⊗ₜ[k] y g : (X ⊗ Y : Rep k F))) := by
  funext g
  have hdy : ∀ a : F, (inhomogeneousCochains.d Y (m + 1)).hom y (Fin.cons a⁻¹ g) =
      Y.ρ a⁻¹ (y g) - y (Fin.cons (a⁻¹ * g 0) fun i => g i.succ) +
        ∑ j : Fin (m + 1), (-1 : k) ^ ((j : ℕ) + 2) •
          y (Fin.cons a⁻¹ (Fin.contractNth j (· * ·) g)) := by
    intro a
    rw [inhomogeneousCochains.d_hom_apply, Fin.sum_univ_succ (n := m + 1)]
    simp only [Fin.cons_zero, Fin.cons_succ, contractNth_zero_cons, contractNth_succ_cons,
      Fin.val_zero, Fin.val_succ, zero_add, pow_one, neg_one_smul]
    have e2 : ∀ j : Fin (m + 1), (j : ℕ) + 1 + 1 = (j : ℕ) + 2 := fun _ => rfl
    simp only [e2]
    abel
  have hsplit : normHomotopyFun μ rfl e ((inhomogeneousCochains.d Y (m + 1)).hom y) g =
      μ.hom ((X.ρ.norm e ⊗ₜ[k] y g : (X ⊗ Y : Rep k F))) -
        Z.ρ (g 0) (normHomotopyFun μ rfl e y fun i => g i.succ) +
        ∑ j : Fin (m + 1), (-1 : k) ^ ((j : ℕ) + 2) •
          normHomotopyFun μ rfl e y (Fin.contractNth j (· * ·) g) := by
    simp only [normHomotopyFun, consTuple_rfl]
    simp only [hdy, TensorProduct.tmul_add, TensorProduct.tmul_sub, TensorProduct.tmul_sum,
      TensorProduct.tmul_smul, map_add, map_sub, map_sum, map_smul, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    rw [sum_ρ_μ_tmul_ρ_inv μ e (y g), Finset.sum_comm (β := Z.V)]
    congr 2
    · refine (Fintype.sum_equiv (Equiv.mulLeft (g 0)) _ _ fun a => ?_).symm
      simp only [Equiv.coe_mulLeft, mul_inv_rev, inv_mul_cancel_right, map_mul,
        Module.End.mul_apply]
    · funext j
      rw [Finset.smul_sum]
  rw [Pi.add_apply, inhomogeneousCochains.d_hom_apply, hsplit]
  have hpow : ∀ j : Fin (m + 1), (-1 : k) ^ ((j : ℕ) + 2) = -(-1 : k) ^ ((j : ℕ) + 1) :=
    fun j => by rw [pow_succ, mul_neg_one]
  simp only [hpow, neg_smul, Finset.sum_neg_distrib]
  abel

/- English proof (translation)
Use function extensionality and compare the values at `g`. Use `set b := z g with hb`. Establish `hzc : z = fun _ => b` using `funext fun g' => congrArg z (Subsingleton.elim g' g)`. Rewrite using `[hzc]`. Simplify using `only [normHomotopyFun, inhomogeneousCochains.d_hom_apply, consTuple_rfl, Fin.cons_zero, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, zero_add, pow_one, neg_one_smul, ← sub_eq_add_neg, TensorProduct.tmul_sub, map_sub, Finset.sum_sub_distrib]`.

Rewrite using `[sum_ρ_μ_tmul_ρ_inv]`. Use `congr 1`. Simplify using `[Representation.norm]`.
-/
theorem normHomotopyFun_d_zero (e : X) (z : (Fin 0 → F) → Y) :
    normHomotopyFun μ rfl e ((inhomogeneousCochains.d Y 0).hom z) =
      fun g => μ.hom ((X.ρ.norm e ⊗ₜ[k] z g : (X ⊗ Y : Rep k F))) -
        Z.ρ.norm (μ.hom ((e ⊗ₜ[k] z g : (X ⊗ Y : Rep k F)))) := by
  funext g
  set b := z g with hb
  have hzc : z = fun _ => b := funext fun g' => congrArg z (Subsingleton.elim g' g)
  rw [hzc]
  simp only [normHomotopyFun, inhomogeneousCochains.d_hom_apply, consTuple_rfl, Fin.cons_zero,
    Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, zero_add, pow_one,
    neg_one_smul, ← sub_eq_add_neg,
    TensorProduct.tmul_sub, map_sub, Finset.sum_sub_distrib]
  rw [sum_ρ_μ_tmul_ρ_inv]
  congr 1
  simp [Representation.norm]

end Homotopy

section LocallyConstant

variable {k F : Type u} [CommRing k] [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
  [Fintype F] {X Y Z : Rep.{u} k F} [IsDiscreteRep X] [IsDiscreteRep Y] [IsDiscreteRep Z]
  (μ : X ⊗ Y ⟶ Z)

omit [IsTopologicalGroup F] [IsDiscreteRep X] [IsDiscreteRep Y] [IsDiscreteRep Z] in
/- English proof (translation)
Establish `e1 : normHomotopyFun μ h e y = ∑ a : F, fun g => Z.ρ a (μ.hom ((e ⊗ₜ[k] y (consTuple h a⁻¹ g) : (X ⊗ Y : Rep k F))))`. Use function extensionality and compare the values at `g`. Simplify using `[normHomotopyFun, Finset.sum_apply]`. Rewrite using `[e1]`. Conclude with `Finset.sum_induction _ IsLocallyConstant (fun _ _ ha hb => ha.add hb) (IsLocallyConstant.const 0) fun a _ => (hy.comp_continuous (continuous_consTuple h a⁻¹)).comp (fun b : Y => Z.ρ a (μ.hom ((e ⊗ₜ[k] b : (X ⊗ Y : Rep k F)))))`.
-/
theorem isLocallyConstant_normHomotopyFun {s m : ℕ} (h : s = m + 1) (e : X)
    {y : (Fin s → F) → Y} (hy : IsLocallyConstant y) :
    IsLocallyConstant (normHomotopyFun μ h e y) := by
  have e1 : normHomotopyFun μ h e y = ∑ a : F, fun g =>
      Z.ρ a (μ.hom ((e ⊗ₜ[k] y (consTuple h a⁻¹ g) : (X ⊗ Y : Rep k F)))) := by
    funext g
    simp [normHomotopyFun, Finset.sum_apply]
  rw [e1]
  exact Finset.sum_induction _ IsLocallyConstant (fun _ _ ha hb => ha.add hb)
    (IsLocallyConstant.const 0) fun a _ =>
      (hy.comp_continuous (continuous_consTuple h a⁻¹)).comp
        (fun b : Y => Z.ρ a (μ.hom ((e ⊗ₜ[k] b : (X ⊗ Y : Rep k F)))))

noncomputable def normHomotopy {s m : ℕ} (h : s = m + 1) :
    X →ₗ[k] (cochainsComplex Y).X s →ₗ[k] (cochainsComplex Z).X m :=
  LinearMap.mk₂ k (fun e y => mkCochain Z (normHomotopyFun μ h e (cochainOf Y y))
      (isLocallyConstant_normHomotopyFun μ h e (isLocallyConstant_cochainOf y)))
    (fun e e' _ => cochainOf_injective (normHomotopyFun_add_left μ h e e' _))
    (fun c e _ => cochainOf_injective (normHomotopyFun_smul_left μ h c e _))
    (fun e _ _ => cochainOf_injective (normHomotopyFun_add_right μ h e _ _))
    (fun c e _ => cochainOf_injective (normHomotopyFun_smul_right μ h c e _))

omit [IsDiscreteRep X] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cochainOf_normHomotopy {s m : ℕ} (h : s = m + 1) (e : X) (y : (cochainsComplex Y).X s) :
    cochainOf Z (normHomotopy μ h e y) = normHomotopyFun μ h e (cochainOf Y y) :=
  rfl

omit [Fintype F] in

/- English proof (translation)
Rewrite using `[cochainOf_cupPairingCochains]`. Express the relevant statement in the definitionally equal form `μ.hom (GroupCoh.cupCochain _ _ _ g) = _`. Rewrite using `[GroupCoh.cupCochain_apply]`. Use `congr 2`. Establish `hp : Fin.partialProd g ⟨0, by omega⟩ = 1` using `Fin.partialProd_zero g`.

Rewrite using `[hp, map_one, Module.End.one_apply]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Use `congr 1`. Conclude with `Fin.ext (zero_add _)`.
-/
theorem cochainOf_cupPairingCochains_zeroCochain {n : ℕ} (x : X) (y : (cochainsComplex Y).X n)
    (g : Fin n → F) :
    cochainOf Z (cupPairingCochains μ (zero_add n) (zeroCochain X x) y) g =
      μ.hom ((x ⊗ₜ[k] cochainOf Y y g : (X ⊗ Y : Rep k F))) := by
  rw [cochainOf_cupPairingCochains]
  change μ.hom (GroupCoh.cupCochain _ _ _ g) = _
  rw [GroupCoh.cupCochain_apply]
  congr 2
  have hp : Fin.partialProd g ⟨0, by omega⟩ = 1 := Fin.partialProd_zero g
  rw [hp, map_one, Module.End.one_apply]
  congr 1
  funext j
  congr 1
  exact Fin.ext (zero_add _)

/- English proof (translation)
Apply `cochainOf_injective` to reduce the goal to its premises. Rewrite using `[cochainOf_add, cochainOf_d, cochainOf_normHomotopy, cochainOf_normHomotopy, cochainOf_d, normHomotopyFun_d_add]`. Use function extensionality and compare the values at `g`. Rewrite using `[cochainOf_cupPairingCochains_zeroCochain]`.
-/
theorem d_normHomotopy_add {m : ℕ} (e : X) (y : (cochainsComplex Y).X (m + 1)) :
    ((cochainsComplex Z).d m (m + 1)).hom (normHomotopy μ rfl e y) +
        normHomotopy μ rfl e (((cochainsComplex Y).d (m + 1) (m + 1 + 1)).hom y) =
      cupPairingCochains μ (zero_add (m + 1)) (zeroCochain X (X.ρ.norm e)) y := by
  apply cochainOf_injective
  rw [cochainOf_add, cochainOf_d, cochainOf_normHomotopy, cochainOf_normHomotopy, cochainOf_d,
    normHomotopyFun_d_add]
  funext g
  rw [cochainOf_cupPairingCochains_zeroCochain]

/- English proof (translation)
Apply `cochainOf_injective` to reduce the goal to its premises. Rewrite using `[cochainOf_normHomotopy, cochainOf_d, normHomotopyFun_d_zero]`. Use function extensionality and compare the values at `g`. Establish `hg : g = fun i => i.elim0` using `Subsingleton.elim _ _`. Substitute `hg` using the available equality.

Rewrite using `[show ∀ a b : (cochainsComplex Z).X 0, cochainOf Z (a - b) = cochainOf Z a - cochainOf Z b from fun _ _ => rfl, Pi.sub_apply, cochainOf_cupPairingCochains_zeroCochain]`. Both sides reduce to the same expression.
-/
theorem normHomotopy_d_zero (e : X) (z : (cochainsComplex Y).X 0) :
    normHomotopy μ rfl e (((cochainsComplex Y).d 0 1).hom z) =
      cupPairingCochains μ (zero_add 0) (zeroCochain X (X.ρ.norm e)) z -
        zeroCochain Z (Z.ρ.norm (μ.hom ((e ⊗ₜ[k] cochainOf Y z (fun i => i.elim0) :
          (X ⊗ Y : Rep k F))))) := by
  apply cochainOf_injective
  rw [cochainOf_normHomotopy, cochainOf_d, normHomotopyFun_d_zero]
  funext g
  have hg : g = fun i => i.elim0 := Subsingleton.elim _ _
  subst hg
  rw [show ∀ a b : (cochainsComplex Z).X 0, cochainOf Z (a - b) = cochainOf Z a - cochainOf Z b
    from fun _ _ => rfl, Pi.sub_apply, cochainOf_cupPairingCochains_zeroCochain]
  rfl

end LocallyConstant

end GroundTheory.ProfCoh
