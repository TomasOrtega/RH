import Mathlib
import GroundTheory.TateCohomology.DimensionShift
set_option maxSynthPendingDepth 1

noncomputable section

universe u

open CategoryTheory Limits groupCohomology

namespace GroundTheory.GroupCoh

section Signs

def triangle : ℕ → ℕ
  | 0 => 0
  | n + 1 => triangle n + (n + 1)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem triangle_zero : triangle 0 = 0 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem triangle_succ (n : ℕ) : triangle (n + 1) = triangle n + (n + 1) := rfl

/- English proof (translation)
Proceed by induction on `q with`. Consider the case `zero => simp [triangle_zero]`. Consider the case `succ q ih`. Rewrite using `[← add_assoc, triangle_succ, ih, triangle_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem triangle_add (p q : ℕ) : triangle (p + q) = triangle p + triangle q + p * q := by
  induction q with
  | zero => simp [triangle_zero]
  | succ q ih =>
    rw [← add_assoc, triangle_succ, ih, triangle_succ]
    ring

/- English proof (translation)
Rewrite using `[← Nat.mod_add_div a 2, ← Nat.mod_add_div b 2, pow_add, pow_add, pow_mul, pow_mul, neg_one_sq, one_pow, one_pow, h]`.
-/
theorem neg_one_pow_eq_of_mod_two {R : Type*} [Monoid R] [HasDistribNeg R] {a b : ℕ}
    (h : a % 2 = b % 2) : (-1 : R) ^ a = (-1 : R) ^ b := by
  rw [← Nat.mod_add_div a 2, ← Nat.mod_add_div b 2, pow_add, pow_add, pow_mul, pow_mul,
    neg_one_sq, one_pow, one_pow, h]

end Signs

section Tuples

variable {G : Type*} [Group G] {n : ℕ}

def revInv (x : Fin n → G) : Fin n → G := fun i => (x i.rev)⁻¹

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem revInv_apply (x : Fin n → G) (i : Fin n) : revInv x i = (x i.rev)⁻¹ := rfl

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [show Fin.last 0 = 0 from rfl]`. Consider the case `succ n ih`. Establish `h1` using `Fin.partialProd_succ (revInv x) (Fin.last n)`. Establish `h2` using `Fin.partialProd_succ' x (Fin.last n)`.

Rewrite `h1`, `h2` using `[Fin.succ_last]`. Rewrite using `[h1, h2, ← Fin.partialProd_init]`. Establish `: Fin.init (revInv x) = revInv (Fin.tail x)`. Use function extensionality and compare the values at `i`. Simplify using `only [Fin.init, Fin.tail, revInv_apply]`.

Use `congr 2`. Use `ext`. Simplify using `only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[this, ih, revInv_apply, mul_inv_rev, Fin.rev_last]`.
-/
theorem partialProd_last_revInv (x : Fin n → G) :
    Fin.partialProd (revInv x) (Fin.last n) = (Fin.partialProd x (Fin.last n))⁻¹ := by
  induction n with
  | zero => simp [show Fin.last 0 = 0 from rfl]
  | succ n ih =>
    have h1 := Fin.partialProd_succ (revInv x) (Fin.last n)
    have h2 := Fin.partialProd_succ' x (Fin.last n)
    rw [Fin.succ_last] at h1 h2
    rw [h1, h2, ← Fin.partialProd_init]
    have : Fin.init (revInv x) = revInv (Fin.tail x) := by
      funext i
      simp only [Fin.init, Fin.tail, revInv_apply]
      congr 2
      ext
      simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]
      omega
    rw [this, ih, revInv_apply, mul_inv_rev, Fin.rev_last]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [Fin.init, Fin.tail, revInv_apply]`. Use `congr 2`. Use `ext`. Simplify using `only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem tail_revInv (x : Fin (n + 1) → G) : Fin.tail (revInv x) = revInv (Fin.init x) := by
  funext i
  simp only [Fin.init, Fin.tail, revInv_apply]
  congr 2
  ext
  simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]
  omega

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [Fin.init, Fin.tail, revInv_apply]`. Use `congr 2`. Use `ext`. Simplify using `only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem init_revInv (x : Fin (n + 1) → G) : Fin.init (revInv x) = revInv (Fin.tail x) := by
  funext i
  simp only [Fin.init, Fin.tail, revInv_apply]
  congr 2
  ext
  simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]
  omega

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [Fin.contractNth, revInv_apply, Fin.val_castSucc, Fin.val_rev]`. Apply the tactic sequence `split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;> first`. Consider the case `omega`. Consider the case `(exact congrArg (fun t => (x t)⁻¹) (Fin.ext (by simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]; omega)))`.

Consider the case `(rw [mul_inv_rev]`. Conclude with `congrArg₂ (fun s t => (x s)⁻¹ * (x t)⁻¹) (Fin.ext (by simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]; omega)) (Fin.ext (by simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]; omega)))`.
-/
theorem contractNth_revInv (x : Fin (n + 1) → G) (j : Fin n) :
    Fin.contractNth (Fin.castSucc j) (· * ·) (revInv x) =
      revInv (Fin.contractNth (Fin.castSucc j.rev) (· * ·) x) := by
  funext i
  simp only [Fin.contractNth, revInv_apply, Fin.val_castSucc, Fin.val_rev]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;>
    first
    | omega
    | (exact congrArg (fun t => (x t)⁻¹)
        (Fin.ext (by simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]; omega)))
    | (rw [mul_inv_rev]
       exact congrArg₂ (fun s t => (x s)⁻¹ * (x t)⁻¹)
        (Fin.ext (by simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]; omega))
        (Fin.ext (by simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]; omega)))

/- English proof (translation)
Rewrite using `[Fin.partialProd_contractNth]`. Simplify using `only [Function.comp_apply]`. Use `congr 1`. Rewrite using `[Fin.succAbove_of_le_castSucc]`. Both sides reduce to the same expression.

Simplify using `[Fin.le_def]`.
-/
theorem partialProd_last_contractNth (x : Fin (n + 1) → G) (j : Fin n) :
    Fin.partialProd (Fin.contractNth (Fin.castSucc j) (· * ·) x) (Fin.last n) =
      Fin.partialProd x (Fin.last (n + 1)) := by
  rw [Fin.partialProd_contractNth]
  simp only [Function.comp_apply]
  congr 1
  rw [Fin.succAbove_of_le_castSucc]
  · rfl
  · simp [Fin.le_def]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[Fin.contractNth_apply_of_lt _ _ _ _ (by simp)]`. Both sides reduce to the same expression.
-/
theorem contractNth_last (x : Fin (n + 1) → G) :
    Fin.contractNth (Fin.last n) (· * ·) x = Fin.init x := by
  funext i
  rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp)]
  rfl

/- English proof (translation)
The claim follows from `tail_revInv x`.
-/
theorem tail_revInv' (x : Fin (n + 1) → G) :
    (fun i : Fin n => revInv x i.succ) = revInv (Fin.init x) :=
  tail_revInv x

/- English proof (translation)
The claim follows from `init_revInv x`.
-/
theorem init_revInv' (x : Fin (n + 1) → G) :
    Fin.init (revInv x) = revInv (fun i : Fin n => x i.succ) :=
  init_revInv x

end Tuples

/- English proof (translation)
Substitute `h₁ h₂ h₃` using the available equality. Normalize the expressions using the abelian group laws.
-/
theorem add_add_eq_add_add {M : Type*} [AddCommMonoid M] {a s c b t d : M} (h₁ : a = d)
    (h₂ : c = b) (h₃ : s = t) : a + (s + c) = b + (t + d) := by
  subst h₁ h₂ h₃
  abel

section Cochains

variable {k G : Type u} [CommRing k] [Group G]

def revCochain {A : Rep k G} (n : ℕ) (f : (Fin n → G) → A) : (Fin n → G) → A :=
  fun x => (-1 : k) ^ triangle n • A.ρ (Fin.partialProd x (Fin.last n)) (f (revInv x))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem revCochain_apply {A : Rep k G} (n : ℕ) (f : (Fin n → G) → A) (x : Fin n → G) :
    revCochain n f x =
      (-1 : k) ^ triangle n • A.ρ (Fin.partialProd x (Fin.last n)) (f (revInv x)) :=
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `x`. Establish `hP : Fin.partialProd x (Fin.last (n + 1)) = x 0 * Fin.partialProd (fun i : Fin n => x i.succ) (Fin.last n)`. Rewrite using `[← Fin.succ_last, Fin.partialProd_succ']`. Both sides reduce to the same expression. Establish `hP' : Fin.partialProd x (Fin.last (n + 1)) = Fin.partialProd (Fin.init x) (Fin.last n) * x (Fin.last n)`.

Rewrite using `[← Fin.succ_last, Fin.partialProd_succ, Fin.partialProd_init]`. Simplify using `only [inhomogeneousCochains.d_hom_apply, revCochain_apply, Fin.sum_univ_castSucc, Fin.val_last, Fin.val_castSucc, contractNth_last, contractNth_revInv, partialProd_last_contractNth, tail_revInv', init_revInv', map_add, map_sum, map_smul, smul_add, Finset.smul_sum]`. Use `add_add_eq_add_add ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[← Module.End.mul_apply, ← map_mul, ← hP, smul_smul, ← pow_add]`. Use `congr 1`.

Use `neg_one_pow_eq_of_mod_two ?_` and prove the remaining obligations. Rewrite using `[triangle_succ]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[revInv_apply, Fin.rev_zero, ← Module.End.mul_apply, ← map_mul, hP', mul_inv_cancel_right, smul_smul, ← pow_add]`. Use `congr 1`.

Use `neg_one_pow_eq_of_mod_two ?_` and prove the remaining obligations. Rewrite using `[triangle_succ]`. Use linear arithmetic over natural numbers and integers. Use `Fintype.sum_equiv Fin.revPerm _ _ fun j => ?_` and prove the remaining obligations. Simplify using `only [Fin.revPerm_apply, Fin.rev_rev, smul_smul, ← pow_add]`.

Use `congr 1`. Use `neg_one_pow_eq_of_mod_two ?_` and prove the remaining obligations. Rewrite using `[triangle_succ, Fin.val_rev]`. Use `j.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem d_revCochain {A : Rep k G} (n : ℕ) (f : (Fin n → G) → A) :
    (inhomogeneousCochains.d A n).hom (revCochain n f) =
      revCochain (n + 1) ((inhomogeneousCochains.d A n).hom f) := by
  funext x
  have hP : Fin.partialProd x (Fin.last (n + 1)) =
      x 0 * Fin.partialProd (fun i : Fin n => x i.succ) (Fin.last n) := by
    rw [← Fin.succ_last, Fin.partialProd_succ']
    rfl
  have hP' : Fin.partialProd x (Fin.last (n + 1)) =
      Fin.partialProd (Fin.init x) (Fin.last n) * x (Fin.last n) := by
    rw [← Fin.succ_last, Fin.partialProd_succ, Fin.partialProd_init]
  simp only [inhomogeneousCochains.d_hom_apply, revCochain_apply, Fin.sum_univ_castSucc,
    Fin.val_last, Fin.val_castSucc, contractNth_last, contractNth_revInv,
    partialProd_last_contractNth, tail_revInv', init_revInv', map_add, map_sum, map_smul,
    smul_add, Finset.smul_sum]
  refine add_add_eq_add_add ?_ ?_ ?_
  · rw [← Module.End.mul_apply, ← map_mul, ← hP, smul_smul, ← pow_add]
    congr 1
    refine neg_one_pow_eq_of_mod_two ?_
    rw [triangle_succ]
    omega
  · rw [revInv_apply, Fin.rev_zero, ← Module.End.mul_apply, ← map_mul, hP', mul_inv_cancel_right,
      smul_smul, ← pow_add]
    congr 1
    refine neg_one_pow_eq_of_mod_two ?_
    rw [triangle_succ]
    omega
  · refine Fintype.sum_equiv Fin.revPerm _ _ fun j => ?_
    simp only [Fin.revPerm_apply, Fin.rev_rev, smul_smul, ← pow_add]
    congr 1
    refine neg_one_pow_eq_of_mod_two ?_
    rw [triangle_succ, Fin.val_rev]
    have := j.isLt
    omega

variable (A : Rep k G)

def revₗ (n : ℕ) : ((Fin n → G) → A) →ₗ[k] ((Fin n → G) → A) where
  toFun := revCochain n
  map_add' f g := by
    funext x
    simp only [revCochain_apply, Pi.add_apply, map_add, smul_add]
  map_smul' c f := by
    funext x
    simp only [revCochain_apply, Pi.smul_apply, map_smul, RingHom.id_apply]
    exact smul_comm _ _ _

def revHom : inhomogeneousCochains A ⟶ inhomogeneousCochains A where
  f n := ModuleCat.ofHom (revₗ A n)
  comm' i j (hij : i + 1 = j) := by
    subst hij
    rw [inhomogeneousCochains.d_def]
    exact ModuleCat.hom_ext (LinearMap.ext fun f => d_revCochain i f)

variable {A}

/- English proof (translation)
Use `HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext (LinearMap.ext fun f => funext fun x => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `φ.hom (revCochain n f x) = revCochain n (fun y => φ.hom (f y)) x`. Rewrite using `[revCochain_apply, revCochain_apply, map_smul, Rep.hom_comm_apply]`.
-/
theorem revHom_naturality {B : Rep k G} (φ : A ⟶ B) :
    revHom A ≫ cochainsMap (MonoidHom.id G) φ = cochainsMap (MonoidHom.id G) φ ≫ revHom B := by
  refine HomologicalComplex.hom_ext _ _ fun n =>
    ModuleCat.hom_ext (LinearMap.ext fun f => funext fun x => ?_)
  change φ.hom (revCochain n f x) = revCochain n (fun y => φ.hom (f y)) x
  rw [revCochain_apply, revCochain_apply, map_smul, Rep.hom_comm_apply]

/- English proof (translation)
Use `ModuleCat.hom_ext (LinearMap.ext fun f => funext fun x => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `revCochain 0 f x = f x`. Rewrite using `[revCochain_apply, triangle_zero, pow_zero, one_smul, show Fin.last 0 = 0 from rfl, Fin.partialProd_zero, map_one, Module.End.one_apply]`. Conclude with `congrArg f (Subsingleton.elim _ _)`.
-/
theorem revHom_f_zero : (revHom A).f 0 = 𝟙 _ := by
  refine ModuleCat.hom_ext (LinearMap.ext fun f => funext fun x => ?_)
  change revCochain 0 f x = f x
  rw [revCochain_apply, triangle_zero, pow_zero, one_smul, show Fin.last 0 = 0 from rfl,
    Fin.partialProd_zero, map_one, Module.End.one_apply]
  exact congrArg f (Subsingleton.elim _ _)

end Cochains

/- English proof (translation)
Establish `hc : HomologicalComplex.cyclesMap φ i = 𝟙 _`. Rewrite using `[← cancel_mono (K.iCycles i), HomologicalComplex.cyclesMap_i, h, Category.comp_id, Category.id_comp]`. Rewrite using `[← cancel_epi (K.homologyπ i), HomologicalComplex.homologyπ_naturality, hc, Category.id_comp, Category.comp_id]`.
-/
theorem homologyMap_eq_id_of_f_eq_id {ι V : Type*} [Category V] [HasZeroMorphisms V]
    {c : ComplexShape ι} {K : HomologicalComplex V c} (φ : K ⟶ K) (i : ι) [K.HasHomology i]
    (h : φ.f i = 𝟙 _) : HomologicalComplex.homologyMap φ i = 𝟙 _ := by
  have hc : HomologicalComplex.cyclesMap φ i = 𝟙 _ := by
    rw [← cancel_mono (K.iCycles i), HomologicalComplex.cyclesMap_i, h, Category.comp_id,
      Category.id_comp]
  rw [← cancel_epi (K.homologyπ i), HomologicalComplex.homologyπ_naturality, hc, Category.id_comp,
    Category.comp_id]

section Cohomology

variable {k G : Type u} [CommRing k] [Group G]

/- English proof (translation)
Proceed by induction on `n generalizing A with`. Consider the case `zero => exact homologyMap_eq_id_of_f_eq_id _ 0 revHom_f_zero`. Consider the case `succ n ih`. Establish `hS` using `coindSES_shortExact A`. Establish `hz : IsZero (groupCohomology (coindSES.obj A).X₂ (n + 1))` using `(isZero_groupCohomology_succ_of_subsingleton _ n).of_iso (coindIso _ (n + 1))`.

Use `epi_δ_of_isZero hS n hz` as an intermediate fact. Set `Φ : (coindSES.obj A).map (cochainsFunctor k G) ⟶ (coindSES.obj A).map (cochainsFunctor k G)` to `{ τ₁ := revHom _ τ₂ := revHom _ τ₃ := revHom _ comm₁₂ := revHom_naturality _ comm₂₃ := revHom_naturality _ }`. Establish `key` using `HomologicalComplex.HomologySequence.δ_naturality Φ (map_cochainsFunctor_shortExact hS) (map_cochainsFunctor_shortExact hS) n (n + 1) rfl`. Establish `h3 : HomologicalComplex.homologyMap Φ.τ₃ n = 𝟙 _` using `ih _`. Rewrite `key` using `[h3, Category.id_comp]`.

Use `(cancel_epi (δ hS n (n + 1) rfl)).1 ?_` and prove the remaining obligations. Conclude with `key.trans (Category.comp_id _).symm`.
-/
theorem homologyMap_revHom (n : ℕ) (A : Rep k G) :
    HomologicalComplex.homologyMap (revHom A) n = 𝟙 _ := by
  induction n generalizing A with
  | zero => exact homologyMap_eq_id_of_f_eq_id _ 0 revHom_f_zero
  | succ n ih =>
    have hS := coindSES_shortExact A
    have hz : IsZero (groupCohomology (coindSES.obj A).X₂ (n + 1)) :=
      (isZero_groupCohomology_succ_of_subsingleton _ n).of_iso (coindIso _ (n + 1))
    have := epi_δ_of_isZero hS n hz
    let Φ : (coindSES.obj A).map (cochainsFunctor k G) ⟶
        (coindSES.obj A).map (cochainsFunctor k G) :=
      { τ₁ := revHom _
        τ₂ := revHom _
        τ₃ := revHom _
        comm₁₂ := revHom_naturality _
        comm₂₃ := revHom_naturality _ }
    have key := HomologicalComplex.HomologySequence.δ_naturality Φ
      (map_cochainsFunctor_shortExact hS) (map_cochainsFunctor_shortExact hS) n (n + 1) rfl
    have h3 : HomologicalComplex.homologyMap Φ.τ₃ n = 𝟙 _ := ih _
    rw [h3, Category.id_comp] at key
    refine (cancel_epi (δ hS n (n + 1) rfl)).1 ?_
    exact key.trans (Category.comp_id _).symm

variable {A : Rep k G} {n : ℕ}

/- English proof (translation)
The claim follows from `congr(($(HomologicalComplex.cyclesMap_i (revHom A) n)).hom z)`.
-/
theorem iCocycles_cyclesMap_revHom (z : cocycles A n) :
    iCocycles A n (HomologicalComplex.cyclesMap (revHom A) n z) = revCochain n (iCocycles A n z) :=
  congr(($(HomologicalComplex.cyclesMap_i (revHom A) n)).hom z)

/- English proof (translation)
Establish `h` using `congr(($(HomologicalComplex.homologyπ_naturality (revHom A) n)).hom z)`. Rewrite `h` using `[homologyMap_revHom, Category.comp_id]`. Conclude with `h.symm`.
-/
theorem π_cyclesMap_revHom (z : cocycles A n) :
    π A n (HomologicalComplex.cyclesMap (revHom A) n z) = π A n z := by
  have h := congr(($(HomologicalComplex.homologyπ_naturality (revHom A) n)).hom z)
  rw [homologyMap_revHom, Category.comp_id] at h
  exact h.symm

end Cohomology

end GroundTheory.GroupCoh
