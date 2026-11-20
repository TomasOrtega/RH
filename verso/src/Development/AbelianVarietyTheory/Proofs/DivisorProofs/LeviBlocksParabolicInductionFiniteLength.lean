import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix

namespace GlobalTheory.BlockReorder

variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

abbrev NonemptyBlockIndex (m : α → Type) [∀ a, Fintype (m a)] : Type := {a : α // 0 < Fintype.card (m a)}

abbrev numBlocks (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] : ℕ := Fintype.card (NonemptyBlockIndex m)

def neOrder (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] : Fin (numBlocks m) ≃o NonemptyBlockIndex m :=
  monoEquivOfFin (NonemptyBlockIndex m) rfl

def blockSize (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] (i : Fin (numBlocks m)) : ℕ :=
  Fintype.card (m (neOrder m i).1)

/- English proof (translation)
The claim follows from `(neOrder m i).2`.
-/
theorem blockSize_pos (i : Fin (numBlocks m)) : 0 < blockSize m i := (neOrder m i).2

def blockNum (i : Fin (numBlocks m)) : Fin (blockSize m i) ≃ m (neOrder m i).1 := (Fintype.equivFin _).symm

def stdSigma (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] :
    (Σ i, Fin (blockSize m i)) ≃ (Σ a, m a) :=
  ((Equiv.sigmaCongrRight blockNum).trans (Equiv.sigmaCongrLeft (β := fun b : NonemptyBlockIndex m => m b.1) (neOrder m).toEquiv)).trans
    (Equiv.sigmaSubtypeEquivOfSubset m (fun a => 0 < Fintype.card (m a))
      fun _ x => Fintype.card_pos_iff.2 ⟨x⟩)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem stdSigma_apply (i : Fin (numBlocks m)) (u : Fin (blockSize m i)) :
    stdSigma m ⟨i, u⟩ = ⟨(neOrder m i).1, blockNum i u⟩ := rfl

def stdIdx (e : (Σ a, m a) ≃ n) : Fin (∑ i, blockSize m i) ≃ n :=
  finSigmaFinEquiv.symm.trans ((stdSigma m).trans e)

/- English proof (translation)
Rewrite using `[Equiv.symm_apply_eq, stdIdx]`. Simplify using the standard rewrite rules.
-/
@[simp] theorem stdIdx_symm_apply (e : (Σ a, m a) ≃ n) (i : Fin (numBlocks m)) (u : Fin (blockSize m i)) :
    (stdIdx e).symm (e ⟨(neOrder m i).1, blockNum i u⟩) = finSigmaFinEquiv ⟨i, u⟩ := by
  rw [Equiv.symm_apply_eq, stdIdx]
  simp

variable (R : Type) [CommRing R]

def glIso (e : (Σ a, m a) ≃ n) : GL (Fin (∑ i, blockSize m i)) R ≃* GL n R :=
  Units.mapEquiv (reindexAlgEquiv R R (stdIdx e)).toMulEquiv

variable {R}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem val_glIso (e : (Σ a, m a) ≃ n) (g : GL (Fin (∑ i, blockSize m i)) R) (x y : n) :
    (glIso R e g : Matrix n n R) x y = (g : Matrix _ _ R) ((stdIdx e).symm x) ((stdIdx e).symm y) := rfl

variable (R)

/- English proof (translation)
Use `mem_parab.2 fun x y hxy => ?_` and prove the remaining obligations. Take `⟨⟨i, u⟩, rfl⟩` from `((stdSigma m).trans e).surjective x`. Take `⟨⟨j, v⟩, rfl⟩` from `((stdSigma m).trans e).surjective y`. Simplify using `only [Equiv.trans_apply, stdSigma_apply, blk_apply] at hxy`. Establish `hji : j < i` using `(neOrder m).lt_iff_lt.1 (Subtype.coe_lt_coe.1 hxy)`.

Simplify using `only [Equiv.trans_apply, stdSigma_apply, val_glIso, stdIdx_symm_apply]`. Conclude with `mem_parab_iff.1 hg i j u v hji`.
-/
theorem glIso_mem_parab (e : (Σ a, m a) ≃ n) {g : GL (Fin (∑ i, blockSize m i)) R}
    (hg : g ∈ parab R (finSigmaFinEquiv : (Σ i, Fin (blockSize m i)) ≃ _)) : glIso R e g ∈ parab R e := by
  refine mem_parab.2 fun x y hxy => ?_
  obtain ⟨⟨i, u⟩, rfl⟩ := ((stdSigma m).trans e).surjective x
  obtain ⟨⟨j, v⟩, rfl⟩ := ((stdSigma m).trans e).surjective y
  simp only [Equiv.trans_apply, stdSigma_apply, blk_apply] at hxy
  have hji : j < i := (neOrder m).lt_iff_lt.1 (Subtype.coe_lt_coe.1 hxy)
  simp only [Equiv.trans_apply, stdSigma_apply, val_glIso, stdIdx_symm_apply]
  exact mem_parab_iff.1 hg i j u v hji

def leviMap (e : (Σ a, m a) ≃ n) : Levi R (fun i => Fin (blockSize m i)) →* Levi R m :=
  (leviProj R e).comp (((glIso R e).toMonoidHom.comp (leviEmb R finSigmaFinEquiv)).codRestrict (parab R e)
    fun g => glIso_mem_parab R e (leviEmb_mem_parab R _ g))

variable {R}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem leviMap_apply (e : (Σ a, m a) ≃ n) (g : Levi R (fun i => Fin (blockSize m i))) (a : α) (x y : m a) :
    (leviMap R e g a : Matrix (m a) (m a) R) x y =
      (leviEmb R finSigmaFinEquiv g : Matrix _ _ R) ((stdIdx e).symm (e ⟨a, x⟩)) ((stdIdx e).symm (e ⟨a, y⟩)) :=
  rfl

/- English proof (translation)
Rewrite using `[leviMap_apply, stdIdx_symm_apply, stdIdx_symm_apply, leviEmb_apply_same]`.
-/
@[simp] theorem leviMap_apply_num (e : (Σ a, m a) ≃ n) (g : Levi R (fun i => Fin (blockSize m i))) (i : Fin (numBlocks m))
    (u v : Fin (blockSize m i)) :
    (leviMap R e g (neOrder m i).1 : Matrix _ _ R) (blockNum i u) (blockNum i v) = (g i : Matrix _ _ R) u v := by
  rw [leviMap_apply, stdIdx_symm_apply, stdIdx_symm_apply, leviEmb_apply_same]

/- English proof (translation)
Use function extensionality and compare the values at `a`. Use `Units.ext (Matrix.ext fun x y => ?_)` and prove the remaining obligations. Take `⟨i, hi⟩` from `(neOrder m).surjective ⟨a, Fintype.card_pos_iff.2 ⟨x⟩⟩`. Establish `ha : (neOrder m i).1 = a` using `congrArg Subtype.val hi`. Substitute `ha` using the available equality.

Take `⟨u, rfl⟩` from `(blockNum i).surjective x`. Take `⟨v, rfl⟩` from `(blockNum i).surjective y`. Conclude with `H i u v`.
-/
theorem levi_ext {g h : Levi R m}
    (H : ∀ (i : Fin (numBlocks m)) (u v : Fin (blockSize m i)),
      (g (neOrder m i).1 : Matrix _ _ R) (blockNum i u) (blockNum i v) = (h (neOrder m i).1 : Matrix _ _ R) (blockNum i u) (blockNum i v)) :
    g = h := by
  funext a
  refine Units.ext (Matrix.ext fun x y => ?_)
  obtain ⟨i, hi⟩ := (neOrder m).surjective ⟨a, Fintype.card_pos_iff.2 ⟨x⟩⟩
  have ha : (neOrder m i).1 = a := congrArg Subtype.val hi
  subst ha
  obtain ⟨u, rfl⟩ := (blockNum i).surjective x
  obtain ⟨v, rfl⟩ := (blockNum i).surjective y
  exact H i u v

/- English proof (translation)
Use `levi_ext fun i u v => ?_` and prove the remaining obligations. Rewrite using `[leviMap_apply_num, leviProj_apply, leviProj_apply]`. Simplify using `only [val_glIso, stdIdx_symm_apply]`.
-/
theorem leviProj_glIso (e : (Σ a, m a) ≃ n)
    (p : parab R (finSigmaFinEquiv : (Σ i, Fin (blockSize m i)) ≃ _)) :
    leviProj R e ⟨glIso R e p, glIso_mem_parab R e p.2⟩ =
      leviMap R e (leviProj R finSigmaFinEquiv p) := by
  refine levi_ext fun i u v => ?_
  rw [leviMap_apply_num, leviProj_apply, leviProj_apply]
  simp only [val_glIso, stdIdx_symm_apply]

/- English proof (translation)
Introduce `h`. Use `⟨fun i => Units.map (reindexAlgEquiv R R (blockNum i).symm).toRingEquiv.toMonoidHom (h (neOrder m i).1), levi_ext fun i u v => ?_⟩` and prove the remaining obligations. Rewrite using `[leviMap_apply_num]`. Simplify using `[reindexAlgEquiv_apply]`.
-/
theorem leviMap_surjective (e : (Σ a, m a) ≃ n) : Function.Surjective (leviMap R e) := by
  intro h
  refine ⟨fun i => Units.map (reindexAlgEquiv R R (blockNum i).symm).toRingEquiv.toMonoidHom (h (neOrder m i).1),
    levi_ext fun i u v => ?_⟩
  rw [leviMap_apply_num]
  simp [reindexAlgEquiv_apply]

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨continuous_matrix fun x y => ?_, continuous_matrix fun x y => ?_⟩` and prove the remaining obligations. Conclude with `Units.continuous_val.matrix_elem _ _`. Establish `: ∀ g : GL (Fin (∑ i, blockSize m i)) R, (((glIso R e g)⁻¹ : GL n R) : Matrix n n R) x y = ((g⁻¹ : GL _ R) : Matrix _ _ R) ((stdIdx e).symm x) ((stdIdx e).symm y)` using `fun g => by`. Rewrite using `[← map_inv]`. Both sides reduce to the same expression.

Simplify using `only [this]`. Conclude with `Units.continuous_coe_inv.matrix_elem _ _`.
-/
theorem continuous_glIso [TopologicalSpace R] (e : (Σ a, m a) ≃ n) : Continuous (glIso R e) := by
  refine Units.continuous_iff.2 ⟨continuous_matrix fun x y => ?_, continuous_matrix fun x y => ?_⟩
  · exact Units.continuous_val.matrix_elem _ _
  · have : ∀ g : GL (Fin (∑ i, blockSize m i)) R, (((glIso R e g)⁻¹ : GL n R) : Matrix n n R) x y =
        ((g⁻¹ : GL _ R) : Matrix _ _ R) ((stdIdx e).symm x) ((stdIdx e).symm y) := fun g => by
      rw [← map_inv]; rfl
    simp only [this]
    exact Units.continuous_coe_inv.matrix_elem _ _

/- English proof (translation)
Use `continuous_pi fun a => Units.continuous_iff.2 ⟨continuous_matrix fun x y => ?_, continuous_matrix fun x y => ?_⟩` and prove the remaining obligations. Conclude with `(Units.continuous_val.comp (continuous_leviEmb R _)).matrix_elem _ _`. Establish `: ∀ g : Levi R (fun i => Fin (blockSize m i)), (((leviMap R e g a)⁻¹ : GL (m a) R) : Matrix _ _ R) x y = (((leviEmb R finSigmaFinEquiv g)⁻¹ : GL _ R) : Matrix _ _ R) ((stdIdx e).symm (e ⟨a, x⟩)) ((stdIdx e).symm (e ⟨a, y⟩))` using `fun g => by`. Rewrite using `[← Pi.inv_apply, ← map_inv, leviMap_apply, map_inv]`. Simplify using `only [this]`.

Conclude with `(Units.continuous_coe_inv.comp (continuous_leviEmb R _)).matrix_elem _ _`.
-/
theorem continuous_leviMap [TopologicalSpace R] [IsTopologicalRing R] (e : (Σ a, m a) ≃ n) :
    Continuous (leviMap R e) := by
  refine continuous_pi fun a => Units.continuous_iff.2 ⟨continuous_matrix fun x y => ?_,
    continuous_matrix fun x y => ?_⟩
  · exact (Units.continuous_val.comp (continuous_leviEmb R _)).matrix_elem _ _
  · have : ∀ g : Levi R (fun i => Fin (blockSize m i)), (((leviMap R e g a)⁻¹ : GL (m a) R) : Matrix _ _ R) x y =
        (((leviEmb R finSigmaFinEquiv g)⁻¹ : GL _ R) : Matrix _ _ R) ((stdIdx e).symm (e ⟨a, x⟩))
          ((stdIdx e).symm (e ⟨a, y⟩)) := fun g => by
      rw [← Pi.inv_apply, ← map_inv, leviMap_apply, map_inv]
    simp only [this]
    exact (Units.continuous_coe_inv.comp (continuous_leviEmb R _)).matrix_elem _ _

end GlobalTheory.BlockReorder

namespace GlobalTheory.BlockReorder

variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

/- English proof (translation)
Rewrite using `[← Finset.prod_filter_of_ne (p := fun a => 0 < Fintype.card (m a)) (fun a _ h => Nat.pos_of_ne_zero fun h0 => h (hF a h0)), ← Finset.prod_subtype_eq_prod_filter, Finset.subtype_univ]`. Conclude with `((neOrder m).toEquiv.prod_comp (fun b : NonemptyBlockIndex m => F b.1)).symm`.
-/
theorem prod_neOrder {M : Type} [CommMonoid M] (F : α → M) (hF : ∀ a, Fintype.card (m a) = 0 → F a = 1) :
    ∏ a, F a = ∏ i : Fin (numBlocks m), F (neOrder m i).1 := by
  rw [← Finset.prod_filter_of_ne (p := fun a => 0 < Fintype.card (m a))
    (fun a _ h => Nat.pos_of_ne_zero fun h0 => h (hF a h0)),
    ← Finset.prod_subtype_eq_prod_filter, Finset.subtype_univ]
  exact ((neOrder m).toEquiv.prod_comp (fun b : NonemptyBlockIndex m => F b.1)).symm

/- English proof (translation)
Rewrite using `[← Finset.sum_filter_of_ne (p := fun a => 0 < Fintype.card (m a)) (fun a _ h => Nat.pos_of_ne_zero fun h0 => h (hF a h0)), ← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]`. Conclude with `((neOrder m).toEquiv.sum_comp (fun b : NonemptyBlockIndex m => F b.1)).symm`.
-/
theorem sum_neOrder {M : Type} [AddCommMonoid M] (F : α → M) (hF : ∀ a, Fintype.card (m a) = 0 → F a = 0) :
    ∑ a, F a = ∑ i : Fin (numBlocks m), F (neOrder m i).1 := by
  rw [← Finset.sum_filter_of_ne (p := fun a => 0 < Fintype.card (m a))
    (fun a _ h => Nat.pos_of_ne_zero fun h0 => h (hF a h0)),
    ← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]
  exact ((neOrder m).toEquiv.sum_comp (fun b : NonemptyBlockIndex m => F b.1)).symm

/- English proof (translation)
Unfold `modExp`. Simplify using `only [Finset.sum_filter]`. Rewrite using `[sum_neOrder (m := m) (fun b => if (neOrder m i).1 < b then (Fintype.card (m b) : ℤ) else 0) (fun b hb => by simp [hb]), sum_neOrder (m := m) (fun b => if b < (neOrder m i).1 then (Fintype.card (m b) : ℤ) else 0) (fun b hb => by simp [hb])]`. Establish `hc : ∀ j : Fin (numBlocks m), (Fintype.card (Fin (blockSize m j)) : ℤ) = Fintype.card (m (neOrder m j).1)` using `fun j => by rw [Fintype.card_fin]; rfl`. Simplify using `only [hc, OrderIso.lt_iff_lt, Subtype.coe_lt_coe]`.
-/
theorem modExp_neOrder (i : Fin (numBlocks m)) : modExp m (neOrder m i).1 = modExp (fun j => Fin (blockSize m j)) i := by
  unfold modExp
  simp only [Finset.sum_filter]
  rw [sum_neOrder (m := m) (fun b => if (neOrder m i).1 < b then (Fintype.card (m b) : ℤ) else 0)
      (fun b hb => by simp [hb]),
    sum_neOrder (m := m) (fun b => if b < (neOrder m i).1 then (Fintype.card (m b) : ℤ) else 0)
      (fun b hb => by simp [hb])]
  have hc : ∀ j : Fin (numBlocks m), (Fintype.card (Fin (blockSize m j)) : ℤ) = Fintype.card (m (neOrder m j).1) :=
    fun j => by rw [Fintype.card_fin]; rfl
  simp only [hc, OrderIso.lt_iff_lt, Subtype.coe_lt_coe]

variable {R : Type} [CommRing R]

/- English proof (translation)
Use `haveI : IsEmpty (m a) := Fintype.card_eq_zero_iff.1 h`. Use `ext`. Simplify using `[Matrix.det_isEmpty]`.
-/
theorem det_eq_one_of_card_eq_zero {a : α} (h : Fintype.card (m a) = 0) (g : GL (m a) R) :
    Matrix.GeneralLinearGroup.det g = 1 := by
  haveI : IsEmpty (m a) := Fintype.card_eq_zero_iff.1 h
  ext
  simp [Matrix.det_isEmpty]

/- English proof (translation)
Use `ext`. Simplify using `only [Matrix.GeneralLinearGroup.val_det_apply]`. Establish `: (leviMap R e g (neOrder m i).1 : Matrix _ _ R) = (g i : Matrix _ _ R).submatrix (blockNum i).symm (blockNum i).symm`. Use extensionality with `x y`. Take `⟨u, rfl⟩` from `(blockNum i).surjective x`.

Take `⟨v, rfl⟩` from `(blockNum i).surjective y`. Simplify using the standard rewrite rules. Rewrite using `[this, Matrix.det_submatrix_equiv_self]`.
-/
theorem det_leviMap (e : (Σ a, m a) ≃ n) (g : Levi R (fun i => Fin (blockSize m i))) (i : Fin (numBlocks m)) :
    Matrix.GeneralLinearGroup.det (leviMap R e g (neOrder m i).1) = Matrix.GeneralLinearGroup.det (g i) := by
  ext
  simp only [Matrix.GeneralLinearGroup.val_det_apply]
  have : (leviMap R e g (neOrder m i).1 : Matrix _ _ R) =
      (g i : Matrix _ _ R).submatrix (blockNum i).symm (blockNum i).symm := by
    ext x y
    obtain ⟨u, rfl⟩ := (blockNum i).surjective x
    obtain ⟨v, rfl⟩ := (blockNum i).surjective y
    simp
  rw [this, Matrix.det_submatrix_equiv_self]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Rewrite using `[deltaHalf_apply, deltaHalf_apply, prod_neOrder (m := m) _ fun a ha => by`. Rewrite using `[det_eq_one_of_card_eq_zero ha, map_one]]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[det_leviMap, modExp_neOrder]`.
-/
theorem deltaHalf_leviMap (e : (Σ a, m a) ≃ n) (g : Levi k (fun i => Fin (blockSize m i))) :
    deltaHalf k m (leviMap k e g) = deltaHalf k (fun i => Fin (blockSize m i)) g := by
  rw [deltaHalf_apply, deltaHalf_apply, prod_neOrder (m := m) _ fun a ha => by
    rw [det_eq_one_of_card_eq_zero ha, map_one]]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [det_leviMap, modExp_neOrder]

end GlobalTheory.BlockReorder

namespace GlobalTheory.BlockReorder

variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def pullInd (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) :
    IndSp e ρ →ₗ[ℂ] IndSp (finSigmaFinEquiv : (Σ i, Fin (blockSize m i)) ≃ _) (ρ.comp (leviMap k e)) where
  toFun f := ⟨⟨fun g => f.1.1 (glIso k e g), fun p g => by
      show f.1.1 (glIso k e ((p : GL _ k) * g)) =
        (deltaHalf k (fun i => Fin (blockSize m i)) (leviProj k finSigmaFinEquiv p) : ℂ) •
          ρ (leviMap k e (leviProj k finSigmaFinEquiv p)) (f.1.1 (glIso k e g))
      rw [map_mul, ← deltaHalf_leviMap e, ← leviProj_glIso]
      exact parInd_law e ρ f ⟨glIso k e p, glIso_mem_parab k e p.2⟩ (glIso k e g)⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset
      ((continuous_glIso e).continuousAt.preimage_mem_nhds
        (by rw [map_one]; exact IsOpen.mem_nhds f.2 (by simp))) fun g hg => by
      have hg' : ind (parab k e) ((twist ρ (deltaHalf k m)).comp (leviProj k e)) (glIso k e g) f.1 = f.1 := hg
      apply Subtype.ext
      funext x
      show f.1.1 (glIso k e (x * g)) = f.1.1 (glIso k e x)
      rw [map_mul]
      exact congrFun (congrArg Subtype.val hg') (glIso k e x))⟩
  map_add' f f' := rfl
  map_smul' c f := rfl

def pullMap (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) :
    Representation.IntertwiningMap ((parInd e ρ).comp (glIso k e).toMonoidHom)
      (parInd (finSigmaFinEquiv : (Σ i, Fin (blockSize m i)) ≃ _) (ρ.comp (leviMap k e))) where
  toLinearMap := pullInd e ρ
  isIntertwining' g := by
    refine LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => ?_))
    show f.1.1 (glIso k e x * glIso k e g) = f.1.1 (glIso k e (x * g))
    rw [map_mul]

/- English proof (translation)
Introduce `f f' h`. Use `Subtype.ext (Subtype.ext (funext fun x => ?_))` and prove the remaining obligations. Take `⟨y, rfl⟩` from `(glIso k e).surjective x`. Conclude with `congrFun (congrArg (fun F : IndSp _ _ => F.1.1) h) y`.
-/
theorem pullInd_injective (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) :
    Function.Injective (pullInd e ρ) := by
  intro f f' h
  refine Subtype.ext (Subtype.ext (funext fun x => ?_))
  obtain ⟨y, rfl⟩ := (glIso k e).surjective x
  exact congrFun (congrArg (fun F : IndSp _ _ => F.1.1) h) y

/- English proof (translation)
Establish `h1 : HasFiniteLength ((parInd e ρ).comp (glIso k e).toMonoidHom)` using `IsFiniteLength.of_injective h (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ (pullMap e ρ)) (fun x y hxy => pullInd_injective e ρ hxy)`. Conclude with `(hasFiniteLength_comp_iff _ _ (glIso k e).surjective).1 h1`.
-/
theorem hasFiniteLength_parInd (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W)
    (h : HasFiniteLength (parInd (finSigmaFinEquiv : (Σ i, Fin (blockSize m i)) ≃ _) (ρ.comp (leviMap k e)))) :
    HasFiniteLength (parInd e ρ) := by
  have h1 : HasFiniteLength ((parInd e ρ).comp (glIso k e).toMonoidHom) :=
    IsFiniteLength.of_injective h
      (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ (pullMap e ρ))
      (fun x y hxy => pullInd_injective e ρ hxy)
  exact (hasFiniteLength_comp_iff _ _ (glIso k e).surjective).1 h1

end GlobalTheory.BlockReorder

namespace GlobalTheory

open BlockReorder in

/- English proof (translation)
Introduce `hP k _ _ _ _ α n m _ _ _ _ _ _ e W _ _ ρ hρ hl`. Use `hasFiniteLength_parInd e ρ ((hP k (numBlocks m) (blockSize m) blockSize_pos).2 W (ρ.comp (leviMap k e)) (isSmooth_comp hρ _ (continuous_leviMap e)) ((hasFiniteLength_comp_iff _ _ (leviMap_surjective e)).2 hl))` and prove the remaining obligations.
-/
theorem inductionFiniteLength_of_standard : GlobalTheory.Published.StandardFunctorsFiniteLength →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      GlobalTheory.SmGL.InductionFiniteLength k := by
  intro hP k _ _ _ _ α n m _ _ _ _ _ _ e W _ _ ρ hρ hl
  refine hasFiniteLength_parInd e ρ ((hP k (numBlocks m) (blockSize m) blockSize_pos).2 W (ρ.comp (leviMap k e))
    (isSmooth_comp hρ _ (continuous_leviMap e)) ((hasFiniteLength_comp_iff _ _ (leviMap_surjective e)).2 hl))

end GlobalTheory
