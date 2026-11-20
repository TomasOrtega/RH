import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralEqClosedSubgroupConjAverage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerBlockLeParabolic
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviDesc.CptLevi

open Topology

section Gen

variable {G M : Type} [Group G] [Group M] [TopologicalSpace G] [TopologicalSpace M]

/- English proof (translation)
Unfold `cptPart`. Rewrite using `[MonoidHom.map_closure]`. Use `congr 1`. Establish `hc : ∀ x : M, IsCompact (closure (Subgroup.zpowers (j x) : Set G)) ↔ IsCompact (closure (Subgroup.zpowers x : Set M))`. Introduce `x`.

Rewrite using `[← MonoidHom.map_zpowers, Subgroup.coe_map, hj.closure_image_eq, ← hj.isInducing.isCompact_iff]`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨x, hx, rfl⟩, hy⟩`. Conclude with `⟨x, ⟨hx, (hc x).1 hy⟩, rfl⟩`.

Introduce and unpack `⟨x, ⟨hx, hx'⟩, rfl⟩`. Conclude with `⟨⟨x, hx, rfl⟩, (hc x).2 hx'⟩`.
-/
theorem cptPart_map (j : M →* G) (hj : IsClosedEmbedding j) (T : Subgroup M) :
    cptPart (T.map j) = (cptPart T).map j := by
  unfold cptPart
  rw [MonoidHom.map_closure]
  congr 1
  have hc : ∀ x : M, IsCompact (closure (Subgroup.zpowers (j x) : Set G)) ↔
      IsCompact (closure (Subgroup.zpowers x : Set M)) := by
    intro x
    rw [← MonoidHom.map_zpowers, Subgroup.coe_map, hj.closure_image_eq, ← hj.isInducing.isCompact_iff]
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hy⟩
    exact ⟨x, ⟨hx, (hc x).1 hy⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hx'⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, (hc x).2 hx'⟩

/- English proof (translation)
Use `IsClosedEmbedding.of_comp (Units.isEmbedding_embedProduct (M := B)) ?_` and prove the remaining obligations. Conclude with `(hf.prodMap ((MulOpposite.opHomeomorph.isClosedEmbedding.comp hf).comp MulOpposite.opHomeomorph.symm.isClosedEmbedding)).comp Units.isClosedEmbedding_embedProduct`.
-/
theorem isClosedEmbedding_unitsMap {A B : Type} [Monoid A] [Monoid B] [TopologicalSpace A] [TopologicalSpace B]
    [T1Space A] [ContinuousMul A] (f : A →* B) (hf : IsClosedEmbedding f) :
    IsClosedEmbedding (Units.map f) := by
  refine IsClosedEmbedding.of_comp (Units.isEmbedding_embedProduct (M := B)) ?_
  exact (hf.prodMap ((MulOpposite.opHomeomorph.isClosedEmbedding.comp hf).comp
    MulOpposite.opHomeomorph.symm.isClosedEmbedding)).comp Units.isClosedEmbedding_embedProduct

end Gen

section Mat

variable {R : Type} [CommRing R] {n a b : ℕ} (h : a + b = n)

def dHom : Matrix (Fin a) (Fin a) R × Matrix (Fin b) (Fin b) R →* Matrix (Fin n) (Fin n) R where
  toFun p := reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h)) (fromBlocks p.1 0 0 p.2)
  map_one' := by
    simp only [Prod.fst_one, Prod.snd_one, fromBlocks_one, reindex_apply]
    exact submatrix_one_equiv _
  map_mul' p q := by
    simp only [reindex_apply, submatrix_mul_equiv, fromBlocks_multiply, Prod.fst_mul, Prod.snd_mul]
    simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dHom_apply (p : Matrix (Fin a) (Fin a) R × Matrix (Fin b) (Fin b) R) :
    dHom h p = reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (fromBlocks p.1 0 0 p.2) := rfl

/- English proof (translation)
Simplify using `only [reindex_apply, submatrix_mul_equiv]`.
-/
theorem reindex_mul_reindex (e : Fin a ⊕ Fin b ≃ Fin n) (A B : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R) :
    reindex e e A * reindex e e B = reindex e e (A * B) := by
  simp only [reindex_apply, submatrix_mul_equiv]

/- English proof (translation)
Introduce `p` and use `by simp only [dHom_apply, ← reindex_symm, Equiv.symm_apply_apply, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₂]`.
-/
theorem dHom_leftInverse : Function.LeftInverse
    (fun z : Matrix (Fin n) (Fin n) R =>
      ((reindex (finSumFinEquiv.trans (finCongr h)).symm (finSumFinEquiv.trans (finCongr h)).symm z).toBlocks₁₁,
        (reindex (finSumFinEquiv.trans (finCongr h)).symm (finSumFinEquiv.trans (finCongr h)).symm z).toBlocks₂₂))
    (dHom h) := fun p => by
  simp only [dHom_apply, ← reindex_symm, Equiv.symm_apply_apply, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₂]

/- English proof (translation)
Use `(dHom_leftInverse h).isClosedEmbedding ?_ ?_` and prove the remaining obligations. Establish `: Continuous fun z : Matrix (Fin n) (Fin n) R => reindex (finSumFinEquiv.trans (finCongr h)).symm (finSumFinEquiv.trans (finCongr h)).symm z` using `continuous_id.matrix_reindex _ _`. Conclude with `(continuous_matrix fun i j => this.matrix_elem _ _).prodMk (continuous_matrix fun i j => this.matrix_elem _ _)`. Conclude with `(continuous_fst.matrix_fromBlocks continuous_const continuous_const continuous_snd).matrix_reindex _ _`.
-/
theorem isClosedEmbedding_dHom [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    IsClosedEmbedding (dHom (R := R) h) := by
  refine (dHom_leftInverse h).isClosedEmbedding ?_ ?_
  · have : Continuous fun z : Matrix (Fin n) (Fin n) R =>
        reindex (finSumFinEquiv.trans (finCongr h)).symm (finSumFinEquiv.trans (finCongr h)).symm z :=
      continuous_id.matrix_reindex _ _
    exact (continuous_matrix fun i j => this.matrix_elem _ _).prodMk (continuous_matrix fun i j => this.matrix_elem _ _)
  · exact (continuous_fst.matrix_fromBlocks continuous_const continuous_const continuous_snd).matrix_reindex _ _

def jHom : GL (Fin a) R × GL (Fin b) R →* GL (Fin n) R :=
  (Units.map (dHom h)).comp MulEquiv.prodUnits.symm.toMonoidHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem jHom_val (t : GL (Fin a) R × GL (Fin b) R) : (jHom h t).val = dHom h (t.1.val, t.2.val) := rfl

/- English proof (translation)
The claim follows from `(isClosedEmbedding_unitsMap _ (isClosedEmbedding_dHom h)).comp Homeomorph.prodUnits.symm.isClosedEmbedding`.
-/
theorem isClosedEmbedding_jHom [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    IsClosedEmbedding (jHom (R := R) h) :=
  (isClosedEmbedding_unitsMap _ (isClosedEmbedding_dHom h)).comp Homeomorph.prodUnits.symm.isClosedEmbedding

/- English proof (translation)
Use `set Q := reindex (finSumFinEquiv.trans (finCongr h)).symm (finSumFinEquiv.trans (finCongr h)).symm g.val with hQdef`. Establish `hQ : Q = fromBlocks Q.toBlocks₁₁ 0 0 Q.toBlocks₂₂`. Use `(fromBlocks_toBlocks Q).symm` as an intermediate fact. Rewrite `this` using `[h12, h21]`. Then use the resulting hypothesis. Establish `hdet : IsUnit Q.det`.

Rewrite using `[hQdef, det_reindex_self]`. Conclude with `(isUnit_iff_isUnit_det _).1 g.isUnit`. Rewrite `hdet` using `[hQ, det_fromBlocks_zero₁₂]`. Establish `u1 : IsUnit Q.toBlocks₁₁` using `(isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_left hdet)`. Establish `u2 : IsUnit Q.toBlocks₂₂` using `(isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right hdet)`.

Use `⟨(u1.unit, u2.unit), Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[jHom_val, dHom_apply]`. Simplify using `only [IsUnit.unit_spec]`. Rewrite using `[← hQ, hQdef, ← reindex_symm, Equiv.apply_symm_apply]`.
-/
theorem exists_jHom (g : GL (Fin n) R)
    (h12 : (reindex (finSumFinEquiv.trans (finCongr h)).symm (finSumFinEquiv.trans (finCongr h)).symm g.val).toBlocks₁₂ = 0)
    (h21 : (reindex (finSumFinEquiv.trans (finCongr h)).symm (finSumFinEquiv.trans (finCongr h)).symm g.val).toBlocks₂₁ = 0) :
    ∃ t, jHom h t = g := by
  set Q := reindex (finSumFinEquiv.trans (finCongr h)).symm (finSumFinEquiv.trans (finCongr h)).symm g.val with hQdef
  have hQ : Q = fromBlocks Q.toBlocks₁₁ 0 0 Q.toBlocks₂₂ := by
    have := (fromBlocks_toBlocks Q).symm
    rwa [h12, h21] at this
  have hdet : IsUnit Q.det := by
    rw [hQdef, det_reindex_self]
    exact (isUnit_iff_isUnit_det _).1 g.isUnit
  rw [hQ, det_fromBlocks_zero₁₂] at hdet
  have u1 : IsUnit Q.toBlocks₁₁ := (isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_left hdet)
  have u2 : IsUnit Q.toBlocks₂₂ := (isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right hdet)
  refine ⟨(u1.unit, u2.unit), Units.ext ?_⟩
  rw [jHom_val, dHom_apply]
  simp only [IsUnit.unit_spec]
  rw [← hQ, hQdef, ← reindex_symm, Equiv.apply_symm_apply]

end Mat

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Unfold `blk`. Simplify using `only [Matrix.mul_zero]`. Use `split_ifs with hM`. Conclude with `Units.ext (by rw [IsUnit.unit_spec]; rfl)`. Conclude with `absurd (jHom h t).isUnit hM`.
-/
theorem blk_eq_jHom {n a b : ℕ} (h : a + b = n) (w : Pl E) (t : GLw a w × GLw b w) : blk h w t 0 = jHom h t := by
  unfold blk
  simp only [Matrix.mul_zero]
  split_ifs with hM
  · exact Units.ext (by rw [IsUnit.unit_spec]; rfl)
  · exact absurd (jHom h t).isUnit hM

/- English proof (translation)
Establish `hcop` using `hsep.isCoprime`. Rewrite using `[blk_eq_jHom]`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce `hg`.

Establish `hc : g.val * (jHom h m).val = (jHom h m).val * g.val`. Use `congrArg Units.val (show g * jHom h m = jHom h m * MonoidHom.id _ g from hg)` as an intermediate fact. Simplify using `using this`. Use `set e := finSumFinEquiv.trans (finCongr h) with he`. Use `set Q := reindex e.symm e.symm g.val with hQdef`.

Establish `hgQ : g.val = reindex e e Q` using `by simp [hQdef]`. Rewrite `hc` using `[hgQ, jHom_val, dHom_apply, ← fromBlocks_toBlocks Q, reindex_mul_reindex, reindex_mul_reindex]`. Establish `hc2` using `(reindex e e).injective hc`. Simplify using `only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at hc2`. Rewrite `hc2` using `[Matrix.fromBlocks_inj]`.

Establish `h21` using `GlobalTheory.LeviDesc.intertwiner_eq_zero_of_isCoprime _ _ _ hcop hc2.2.2.1`. Establish `h12` using `GlobalTheory.LeviDesc.intertwiner_eq_zero_of_isCoprime _ _ _ hcop.symm hc2.2.1`. Take `⟨t, rfl⟩` from `exists_jHom h g h12 h21`. Use `⟨t, ?_, rfl⟩` and prove the remaining obligations. Use `show t * m = m * MonoidHom.id _ t`.

Apply `(isClosedEmbedding_jHom h).injective` to reduce the goal to its premises. Establish `: jHom h t * jHom h m = jHom h m * MonoidHom.id _ (jHom h t)` using `hg`. Simplify `this` using `[map_mul]`. Introduce and unpack `⟨t, ht, rfl⟩`. Establish `: t * m = m * t` using `ht`.

Use `show jHom h t * jHom h m = jHom h m * MonoidHom.id _ (jHom h t)`. Rewrite using `[MonoidHom.id_apply, ← map_mul, ← map_mul, this]`.
-/
theorem twCent_blk_eq {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (hsep : (m.1.val.charpoly * m.2.val.charpoly).Separable) :
    twCent (MonoidHom.id (GLw n w)) (blk h w m 0) = (twCent (MonoidHom.id _) m).map (jHom h) := by
  have hcop := hsep.isCoprime
  rw [blk_eq_jHom]
  ext g
  constructor
  · intro hg
    have hc : g.val * (jHom h m).val = (jHom h m).val * g.val := by
      have := congrArg Units.val (show g * jHom h m = jHom h m * MonoidHom.id _ g from hg)
      simpa using this
    set e := finSumFinEquiv.trans (finCongr h) with he
    set Q := reindex e.symm e.symm g.val with hQdef
    have hgQ : g.val = reindex e e Q := by simp [hQdef]
    rw [hgQ, jHom_val, dHom_apply, ← fromBlocks_toBlocks Q, reindex_mul_reindex, reindex_mul_reindex] at hc
    have hc2 := (reindex e e).injective hc
    simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at hc2
    rw [Matrix.fromBlocks_inj] at hc2
    have h21 := GlobalTheory.LeviDesc.intertwiner_eq_zero_of_isCoprime _ _ _ hcop hc2.2.2.1
    have h12 := GlobalTheory.LeviDesc.intertwiner_eq_zero_of_isCoprime _ _ _ hcop.symm hc2.2.1
    obtain ⟨t, rfl⟩ := exists_jHom h g h12 h21
    refine ⟨t, ?_, rfl⟩
    show t * m = m * MonoidHom.id _ t
    apply (isClosedEmbedding_jHom h).injective
    have : jHom h t * jHom h m = jHom h m * MonoidHom.id _ (jHom h t) := hg
    simpa [map_mul] using this
  · rintro ⟨t, ht, rfl⟩
    have : t * m = m * t := ht
    show jHom h t * jHom h m = jHom h m * MonoidHom.id _ (jHom h t)
    rw [MonoidHom.id_apply, ← map_mul, ← map_mul, this]

/- English proof (translation)
Establish `: (parP a n w : Set (GLw n w)) = ⋂ i : Fin n, ⋂ j : Fin n, {g : GLw n w | decide (a ≤ (j : ℕ)) < decide (a ≤ (i : ℕ)) → (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j = 0}`. Use extensionality with `g`. Simplify using `only [Set.mem_iInter]`. Both sides reduce to the same expression. Rewrite using `[this]`.

Use `isClosed_iInter fun i => isClosed_iInter fun j => ?_` and prove the remaining obligations. Distinguish the cases in `hij : decide (a ≤ (j : ℕ)) < decide (a ≤ (i : ℕ))`. Simplify using `only [hij, true_implies]`. Conclude with `isClosed_eq (Continuous.matrix_elem (Units.continuous_val (M := Matrix (Fin n) (Fin n) (w.adicCompletion E))) i j) continuous_const`. Simplify using `only [hij, false_implies, Set.ofPred_true]`.

Conclude with `isClosed_univ`.
-/
theorem isClosed_parP' (a n : ℕ) (w : Pl E) : IsClosed (GlobalTheory.LeviDesc.parP a n w : Set (GLw n w)) := by
  have : (parP a n w : Set (GLw n w)) = ⋂ i : Fin n, ⋂ j : Fin n,
      {g : GLw n w | decide (a ≤ (j : ℕ)) < decide (a ≤ (i : ℕ)) → (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j = 0} := by
    ext g
    simp only [Set.mem_iInter]
    rfl
  rw [this]
  refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
  by_cases hij : decide (a ≤ (j : ℕ)) < decide (a ≤ (i : ℕ))
  · simp only [hij, true_implies]
    exact isClosed_eq (Continuous.matrix_elem (Units.continuous_val (M := Matrix (Fin n) (Fin n) (w.adicCompletion E))) i j) continuous_const
  · simp only [hij, false_implies, Set.ofPred_true]
    exact isClosed_univ

/- English proof (translation)
Introduce `E _ _ n a b h w m hsep hγ p`. Establish `hT` using `GlobalTheory.LeviDesc.twCent_blk_le_parP E n a b h w m hsep`. Rewrite using `[← Subgroup.mem_map_iff_mem (f := (parP a n w).subtype) (parP a n w).subtype_injective, GlobalTheory.IwRed.cptPart_map_sub _ (isClosed_parP' a n w) _ hγ hT, twCent_blk_eq h w m hsep, cptPart_map _ (isClosedEmbedding_jHom h)]`. Simplify using `only [Subgroup.mem_map, blk_eq_jHom, Subgroup.coe_subtype]`.
-/
theorem mem_compactPart_parabolic_iff : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w), (m.1.val.charpoly * m.2.val.charpoly).Separable → ∀ (hγ : blk h w m 0 ∈ GlobalTheory.LeviDesc.parP a n w) (p : GlobalTheory.LeviDesc.parP a n w), p ∈ cptPart (twCent (MonoidHom.id _) (⟨blk h w m 0, hγ⟩ : GlobalTheory.LeviDesc.parP a n w)) ↔ ∃ t ∈ cptPart (twCent (MonoidHom.id _) m), blk h w t 0 = (p : GLw n w) := by
  intro E _ _ n a b h w m hsep hγ p
  have hT := GlobalTheory.LeviDesc.twCent_blk_le_parP E n a b h w m hsep
  rw [← Subgroup.mem_map_iff_mem (f := (parP a n w).subtype) (parP a n w).subtype_injective,
    GlobalTheory.IwRed.cptPart_map_sub _ (isClosed_parP' a n w) _ hγ hT, twCent_blk_eq h w m hsep,
    cptPart_map _ (isClosedEmbedding_jHom h)]
  simp only [Subgroup.mem_map, blk_eq_jHom, Subgroup.coe_subtype]

end GlobalTheory.LeviDesc.CptLevi
