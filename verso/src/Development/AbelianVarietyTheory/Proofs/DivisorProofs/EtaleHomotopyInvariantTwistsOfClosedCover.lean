import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLtTopOfEssFiniteType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfRingEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceCechDescentIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyProdRingProjectionsBijectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.ClosedCover

/- English proof (translation)
Simplify using `only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]`.
-/
theorem spMap_comp {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

/- English proof (translation)
Simplify using `only [spMap]`. Rewrite using `[show CommRingCat.ofHom (RingHom.id A) = 𝟙 (CommRingCat.of A) from rfl, Spec.map_id]`. Conclude with `sch.map_id _`.
-/
theorem spMap_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp only [spMap]
  rw [show CommRingCat.ofHom (RingHom.id A) = 𝟙 (CommRingCat.of A) from rfl, Spec.map_id]
  exact sch.map_id _

/- English proof (translation)
Establish `h1 : ∀ x, pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n (pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n x) = x`. Introduce `x`. Rewrite using `[← pull_comp, ← spMap_comp]`. Establish `: (e.symm : B →+* A).comp (e : A →+* B) = RingHom.id A` using `by ext; simp`. Rewrite using `[this, spMap_id, pull_id]`.

Establish `h2 : ∀ x, pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n (pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n x) = x`. Introduce `x`. Rewrite using `[← pull_comp, ← spMap_comp]`. Establish `: (e : A →+* B).comp (e.symm : B →+* A) = RingHom.id B` using `by ext; simp`. Rewrite using `[this, spMap_id, pull_id]`.

Conclude with `⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩`.
-/
theorem pull_spMap_bij {q : ℕ} {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (n i : ℤ) :
    Function.Bijective (pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n) := by
  have h1 : ∀ x, pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n (pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n x) = x := by
    intro x
    rw [← pull_comp, ← spMap_comp]
    have : (e.symm : B →+* A).comp (e : A →+* B) = RingHom.id A := by ext; simp
    rw [this, spMap_id, pull_id]
  have h2 : ∀ x, pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n (pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n x) = x := by
    intro x
    rw [← pull_comp, ← spMap_comp]
    have : (e : A →+* B).comp (e.symm : B →+* A) = RingHom.id B := by ext; simp
    rw [this, spMap_id, pull_id]
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `p hp`. Simplify using `only [RingHom.prod_apply, Prod.mk_eq_zero, Polynomial.coe_mapRingHom] at hp`. Use extensionality with `n`.

Simplify using `using congrArg (fun r => Polynomial.coeff r n) hp.1`. Simplify using `using congrArg (fun r => Polynomial.coeff r n) hp.2`. Introduce and unpack `⟨p, p'⟩`. Set `N` to `max p.natDegree p'.natDegree + 1`. Use `⟨∑ k ∈ Finset.range N, Polynomial.monomial k (p.coeff k, p'.coeff k), ?_⟩` and prove the remaining obligations.

Simplify using `only [RingHom.prod_apply, Polynomial.coe_mapRingHom, Polynomial.map_sum, Polynomial.map_monomial]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Conclude with `(Polynomial.as_sum_range' p N (by omega)).symm`. Conclude with `(Polynomial.as_sum_range' p' N (by omega)).symm`.
-/
theorem polyProd_bij (A B : Type) [CommRing A] [CommRing B] :
    Function.Bijective ((Polynomial.mapRingHom (RingHom.fst A B)).prod (Polynomial.mapRingHom (RingHom.snd A B))) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro p hp
    simp only [RingHom.prod_apply, Prod.mk_eq_zero, Polynomial.coe_mapRingHom] at hp
    ext n
    · simpa using congrArg (fun r => Polynomial.coeff r n) hp.1
    · simpa using congrArg (fun r => Polynomial.coeff r n) hp.2
  · rintro ⟨p, p'⟩
    let N := max p.natDegree p'.natDegree + 1
    refine ⟨∑ k ∈ Finset.range N, Polynomial.monomial k (p.coeff k, p'.coeff k), ?_⟩
    simp only [RingHom.prod_apply, Polynomial.coe_mapRingHom, Polynomial.map_sum, Polynomial.map_monomial]
    refine Prod.ext ?_ ?_
    · exact (Polynomial.as_sum_range' p N (by omega)).symm
    · exact (Polynomial.as_sum_range' p' N (by omega)).symm

/- English proof (translation)
Introduce `q _ A B _ _ hA hB i n`. Set `e : Polynomial (A × B) ≃+* Polynomial A × Polynomial B` to `RingEquiv.ofBijective _ (polyProd_bij A B)`. Set `g : A × B →+* Polynomial A × Polynomial B` to `RingHom.prodMap Polynomial.C Polynomial.C`. Establish `hg : e.toRingHom.comp Polynomial.C = g`. Apply the tactic sequence `ext x <;> simp [e, g]`.

Establish `hgb : Function.Bijective (pull (ZMod q) (spMap g) (tw q i) n)`. Establish `hP` using `GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q A B n i`. Establish `hD` using `GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q (Polynomial A) (Polynomial B) n i`. Establish `hsq : ∀ x : Ht q (sp (A × B)) n i, (pull _ (spMap (RingHom.fst (Polynomial A) (Polynomial B))) _ _ (pull _ (spMap g) _ n x), pull _ (spMap (RingHom.snd (Polynomial A) (Polynomial B))) _ _ (pull _ (spMap g) _ n x)) = Prod.map (pull _ (spMap (Polynomial.C : A →+* Polynomial A)) (tw …`. Introduce `x`.

Simplify using `only [Prod.map]`. Rewrite using `[← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, ← spMap_comp, ← spMap_comp, ← spMap_comp, ← spMap_comp]`. Both sides reduce to the same expression. Establish `hcomp : (fun x : Ht q (sp (Polynomial A × Polynomial B)) n i => (pull _ (spMap (RingHom.fst (Polynomial A) (Polynomial B))) _ _ x, pull _ (spMap (RingHom.snd (Polynomial A) (Polynomial B))) _ _ x)) ∘ (pull _ (spMap g) _ n) = Prod.map (pull _ (spMap (Polynomial.C : A →+* Polynomia …`. Use function extensionality and compare the values at `x`.

Conclude with `hsq x`. Establish `hR : Function.Bijective (Prod.map (pull _ (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i) n) (pull _ (spMap (Polynomial.C : B →+* Polynomial B)) (tw q i) n))` using `Function.Bijective.prodMap (hA i n) (hB i n)`. Use `(hR.comp hP)` as an intermediate fact. Rewrite `this` using `[← hcomp]`. Conclude with `(Function.Bijective.of_comp_iff' hD _).mp this`.

Establish `heq : ⇑(pull (ZMod q) (spMap g) (tw q i) n) = ⇑(pull (ZMod q) (spMap e.toRingHom) (tw q i) n) ∘ ⇑(pull (ZMod q) (spMap (Polynomial.C : A × B →+* Polynomial (A × B))) (tw q i) n)`. Use function extensionality and compare the values at `x`. Rewrite using `[Function.comp_apply, ← pull_comp, ← spMap_comp, hg]`. Rewrite `hgb` using `[heq]`. Conclude with `(Function.Bijective.of_comp_iff' (pull_spMap_bij e n i) _).mp hgb`.
-/
theorem prodL : ∀ (q : ℕ) [NeZero q] (A B : Type) [CommRing A] [CommRing B], HInv q A → HInv q B → HInv q (A × B) := by
  intro q _ A B _ _ hA hB i n
  let e : Polynomial (A × B) ≃+* Polynomial A × Polynomial B := RingEquiv.ofBijective _ (polyProd_bij A B)
  let g : A × B →+* Polynomial A × Polynomial B := RingHom.prodMap Polynomial.C Polynomial.C
  have hg : e.toRingHom.comp Polynomial.C = g := by
    ext x <;> simp [e, g]

  have hgb : Function.Bijective (pull (ZMod q) (spMap g) (tw q i) n) := by
    have hP := GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q A B n i
    have hD := GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q (Polynomial A) (Polynomial B) n i
    have hsq : ∀ x : Ht q (sp (A × B)) n i,
        (pull _ (spMap (RingHom.fst (Polynomial A) (Polynomial B))) _ _ (pull _ (spMap g) _ n x),
          pull _ (spMap (RingHom.snd (Polynomial A) (Polynomial B))) _ _ (pull _ (spMap g) _ n x)) =
        Prod.map (pull _ (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i) n)
          (pull _ (spMap (Polynomial.C : B →+* Polynomial B)) (tw q i) n)
          (pull _ (spMap (RingHom.fst A B)) _ _ x, pull _ (spMap (RingHom.snd A B)) _ _ x) := by
      intro x
      simp only [Prod.map]
      rw [← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, ← spMap_comp, ← spMap_comp, ← spMap_comp, ← spMap_comp]
      rfl
    have hcomp : (fun x : Ht q (sp (Polynomial A × Polynomial B)) n i =>
          (pull _ (spMap (RingHom.fst (Polynomial A) (Polynomial B))) _ _ x,
           pull _ (spMap (RingHom.snd (Polynomial A) (Polynomial B))) _ _ x)) ∘ (pull _ (spMap g) _ n) =
        Prod.map (pull _ (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i) n)
          (pull _ (spMap (Polynomial.C : B →+* Polynomial B)) (tw q i) n) ∘
          (fun x : Ht q (sp (A × B)) n i =>
            (pull _ (spMap (RingHom.fst A B)) _ _ x, pull _ (spMap (RingHom.snd A B)) _ _ x)) := by
      funext x; exact hsq x
    have hR : Function.Bijective (Prod.map (pull _ (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i) n)
          (pull _ (spMap (Polynomial.C : B →+* Polynomial B)) (tw q i) n)) :=
      Function.Bijective.prodMap (hA i n) (hB i n)
    have := (hR.comp hP)
    rw [← hcomp] at this
    exact (Function.Bijective.of_comp_iff' hD _).mp this
  have heq : ⇑(pull (ZMod q) (spMap g) (tw q i) n) =
      ⇑(pull (ZMod q) (spMap e.toRingHom) (tw q i) n) ∘ ⇑(pull (ZMod q) (spMap (Polynomial.C : A × B →+* Polynomial (A × B))) (tw q i) n) := by
    funext x
    rw [Function.comp_apply, ← pull_comp, ← spMap_comp, hg]
  rw [heq] at hgb
  exact (Function.Bijective.of_comp_iff' (pull_spMap_bij e n i) _).mp hgb

end GlobalTheory.EtC.ClosedCover

namespace GlobalTheory.EtC.ClosedCover
open PiTensorProduct

noncomputable def consLin (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (k : ℕ) :
    B ⊗[A] PiTensorProduct A (fun _ : Fin (k + 1) => B) ≃ₗ[A] PiTensorProduct A (fun _ : Fin (k + 2) => B) :=
  (TensorProduct.congr (subsingletonEquiv (R := A) (s := fun _ : Fin 1 => B) (0 : Fin 1)).symm (LinearEquiv.refl A _)).trans <|
    (tmulEquiv A B).trans (reindex A (fun _ => B) (finSumFinEquiv.trans (finCongr (by omega))))

/- English proof (translation)
Simplify using `[consLin, reindex_tprod]`.
-/
theorem consLin_tmul (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (k : ℕ) (b : B) (x : Fin (k + 1) → B) :
    consLin A B k (b ⊗ₜ PiTensorProduct.tprod A x) =
      PiTensorProduct.tprod A (fun i => Sum.elim (fun _ : Fin 1 => b) x ((finSumFinEquiv.trans (finCongr (by omega))).symm i)) := by
  simp [consLin, reindex_tprod]

/- English proof (translation)
Introduce `A B _ _ _ k`. Use `⟨(AlgEquiv.ofLinearEquiv (consLin A B k) ?_ ?_).symm⟩` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.one_def, PiTensorProduct.one_def, consLin_tmul, PiTensorProduct.one_def]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Apply the tactic sequence `rcases (finSumFinEquiv.trans (finCongr (by omega))).symm i with j | j <;> rfl`. Use `(LinearMap.map_mul_iff _).mpr ?_` and prove the remaining obligations. Use extensionality with `b x b' x'`. Simplify using `only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, Algebra.TensorProduct.tmul_mul_tmul, tprod_mul_tprod, consLin_tmul, TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply, LinearMap.compMulti …`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Simplify using `only [Pi.mul_apply]`. Apply the tactic sequence `rcases (finSumFinEquiv.trans (finCongr (by omega))).symm i with j | j <;> rfl`.
-/
theorem succL : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (k : ℕ), Nonempty (PiTensorProduct A (fun _ : Fin (k + 2) => B) ≃ₐ[A] B ⊗[A] PiTensorProduct A (fun _ : Fin (k + 1) => B)) := by
  intro A B _ _ _ k
  refine ⟨(AlgEquiv.ofLinearEquiv (consLin A B k) ?_ ?_).symm⟩
  · rw [Algebra.TensorProduct.one_def, PiTensorProduct.one_def, consLin_tmul, PiTensorProduct.one_def]
    congr 1
    funext i
    rcases (finSumFinEquiv.trans (finCongr (by omega))).symm i with j | j <;> rfl
  · refine (LinearMap.map_mul_iff _).mpr ?_
    ext b x b' x'
    simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.compl₂_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, Algebra.TensorProduct.tmul_mul_tmul, tprod_mul_tprod, consLin_tmul, TensorProduct.AlgebraTensorModule.curry_apply,
      TensorProduct.curry_apply, LinearMap.compMultilinearMap_apply, LinearMap.restrictScalars_apply]
    congr 1
    funext i
    simp only [Pi.mul_apply]
    rcases (finSumFinEquiv.trans (finCongr (by omega))).symm i with j | j <;> rfl
end GlobalTheory.EtC.ClosedCover

namespace GlobalTheory.EtC.ClosedCover

/- English proof (translation)
Introduce `A B _ _ _`. Set `f` to `PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin 1 => B) 0`. Set `g` to `PiTensorProduct.subsingletonEquiv (R := A) (s := fun _ : Fin 1 => B) (0 : Fin 1)`. Establish `hgf : ∀ a, g (f a) = a`. Introduce `a`.

Simplify using `[f, g, PiTensorProduct.subsingletonEquiv_apply_tprod]`. Establish `hf : Function.Bijective f`. Establish `: (f : B → _) = g.symm`. Use function extensionality and compare the values at `a`. Apply `g.injective` to reduce the goal to its premises.

Rewrite using `[hgf, LinearEquiv.apply_symm_apply]`. Rewrite using `[this]`. Conclude with `g.symm.bijective`. Conclude with `⟨(AlgEquiv.ofBijective f hf).symm⟩`.
-/
theorem oneL : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Nonempty (PiTensorProduct A (fun _ : Fin 1 => B) ≃ₐ[A] B) := by
  intro A B _ _ _
  classical
  let f := PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin 1 => B) 0
  let g := PiTensorProduct.subsingletonEquiv (R := A) (s := fun _ : Fin 1 => B) (0 : Fin 1)
  have hgf : ∀ a, g (f a) = a := by
    intro a
    simp [f, g, PiTensorProduct.subsingletonEquiv_apply_tprod]
  have hf : Function.Bijective f := by
    have : (f : B → _) = g.symm := by
      funext a
      apply g.injective
      rw [hgf, LinearEquiv.apply_symm_apply]
    rw [this]
    exact g.symm.bijective
  exact ⟨(AlgEquiv.ofBijective f hf).symm⟩
end GlobalTheory.EtC.ClosedCover

namespace GlobalTheory.EtC.ClosedCover

variable {A : Type} [CommRing A]

noncomputable def quotTensorQuot (L K : Ideal A) : (A ⧸ L) ⊗[A] (A ⧸ K) ≃ₐ[A] A ⧸ (L ⊔ K) :=
  ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A ⧸ L) K).restrictScalars A).symm.trans
    (DoubleQuot.quotQuotEquivQuotSupₐ A L K)

noncomputable def prodLeftAlg (X Y C : Type) [CommRing X] [CommRing Y] [CommRing C] [Algebra A X] [Algebra A Y]
    [Algebra A C] : (X × Y) ⊗[A] C ≃ₐ[A] (X ⊗[A] C) × (Y ⊗[A] C) :=
  (Algebra.TensorProduct.comm A (X × Y) C).trans <|
    (Algebra.TensorProduct.prodRight A A C X Y).trans <|
      AlgEquiv.prodCongr (Algebra.TensorProduct.comm A C X) (Algebra.TensorProduct.comm A C Y)

noncomputable def stepEquiv (L I J : Ideal A) (C : Type) [CommRing C] [Algebra A C] :
    (A ⧸ L) ⊗[A] (((A ⧸ I) × (A ⧸ J)) ⊗[A] C) ≃ₐ[A] ((A ⧸ (L ⊔ I)) ⊗[A] C) × ((A ⧸ (L ⊔ J)) ⊗[A] C) :=
  (Algebra.TensorProduct.assoc A A A (A ⧸ L) ((A ⧸ I) × (A ⧸ J)) C).symm.trans <|
    (Algebra.TensorProduct.congr ((Algebra.TensorProduct.prodRight A A (A ⧸ L) (A ⧸ I) (A ⧸ J)).trans
      (AlgEquiv.prodCongr (quotTensorQuot L I) (quotTensorQuot L J))) AlgEquiv.refl).trans <|
    prodLeftAlg _ _ C

end GlobalTheory.EtC.ClosedCover

namespace GlobalTheory.EtC.ClosedCover

variable {A : Type} [CommRing A]

/- English proof (translation)
The claim follows from `GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q X Y e.toRingEquiv h`.
-/
theorem hinv_of_algEquiv {q : ℕ} [NeZero q] {X Y : Type} [CommRing X] [CommRing Y] [Algebra A X] [Algebra A Y]
    (e : X ≃ₐ[A] Y) (h : HInv q X) : HInv q Y :=
  GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q X Y e.toRingEquiv h

def Good (I J L : Ideal A) : Prop := L = I ∨ L = J ∨ L = I ⊔ J

/- English proof (translation)
Break down `h with rfl | rfl | rfl` into its components or cases. Use `left`. Simplify using the standard rewrite rules. Use `right`. Use `right`.

Conclude with `sup_comm _ _`. Use `right`. Use `right`. Rewrite using `[sup_assoc, sup_comm J I, ← sup_assoc, sup_idem]`.
-/
theorem good_sup_left {I J L : Ideal A} (h : Good I J L) : Good I J (L ⊔ I) := by
  rcases h with rfl | rfl | rfl
  · left; simp
  · right; right; exact sup_comm _ _
  · right; right; rw [sup_assoc, sup_comm J I, ← sup_assoc, sup_idem]

/- English proof (translation)
Break down `h with rfl | rfl | rfl` into its components or cases. Use `right`. Use `right`. Both sides reduce to the same expression. Use `right`.

Use `left`. Simplify using the standard rewrite rules. Use `right`. Use `right`. Rewrite using `[sup_assoc, sup_idem]`.
-/
theorem good_sup_right {I J L : Ideal A} (h : Good I J L) : Good I J (L ⊔ J) := by
  rcases h with rfl | rfl | rfl
  · right; right; rfl
  · right; left; simp
  · right; right; rw [sup_assoc, sup_idem]

/- English proof (translation)
Introduce `L hL`. Conclude with `hinv_of_algEquiv (stepEquiv L I J C).symm (prodL q _ _ (hC _ (good_sup_left hL)) (hC _ (good_sup_right hL)))`.
-/
theorem main_step (q : ℕ) [NeZero q] (I J : Ideal A) (C : Type) [CommRing C] [Algebra A C]
    (hC : ∀ L, Good I J L → HInv q ((A ⧸ L) ⊗[A] C)) :
    ∀ L, Good I J L → HInv q ((A ⧸ L) ⊗[A] (((A ⧸ I) × (A ⧸ J)) ⊗[A] C)) := by
  intro L hL
  exact hinv_of_algEquiv (stepEquiv L I J C).symm
    (prodL q _ _ (hC _ (good_sup_left hL)) (hC _ (good_sup_right hL)))

/- English proof (translation)
The claim follows from `hinv_of_algEquiv (prodLeftAlg _ _ C).symm (prodL q _ _ (hC I (Or.inl rfl)) (hC J (Or.inr (Or.inl rfl))))`.
-/
theorem main_fin (q : ℕ) [NeZero q] (I J : Ideal A) (C : Type) [CommRing C] [Algebra A C]
    (hC : ∀ L, Good I J L → HInv q ((A ⧸ L) ⊗[A] C)) :
    HInv q (((A ⧸ I) × (A ⧸ J)) ⊗[A] C) :=
  hinv_of_algEquiv (prodLeftAlg _ _ C).symm (prodL q _ _ (hC I (Or.inl rfl)) (hC J (Or.inr (Or.inl rfl))))

/- English proof (translation)
Introduce `L hL` and use `hinv_of_algEquiv (Algebra.TensorProduct.congr (AlgEquiv.refl : (A ⧸ L) ≃ₐ[A] (A ⧸ L)) e) (hC L hL)`.
-/
theorem good_congr (q : ℕ) [NeZero q] (I J : Ideal A) {C D : Type} [CommRing C] [Algebra A C] [CommRing D] [Algebra A D]
    (e : C ≃ₐ[A] D) (hC : ∀ L, Good I J L → HInv q ((A ⧸ L) ⊗[A] C)) :
    ∀ L, Good I J L → HInv q ((A ⧸ L) ⊗[A] D) := fun L hL =>
  hinv_of_algEquiv (Algebra.TensorProduct.congr (AlgEquiv.refl : (A ⧸ L) ≃ₐ[A] (A ⧸ L)) e) (hC L hL)

/- English proof (translation)
Establish `h0 : ∀ L, Good I J L → HInv q ((A ⧸ L) ⊗[A] A)`. Introduce `L hL`. Use `hinv_of_algEquiv (Algebra.TensorProduct.rid A A (A ⧸ L)).symm ?_` and prove the remaining obligations. Break down `hL with rfl | rfl | rfl` into its components or cases. Use `exacts [hI, hJ, hIJ]`.

Proceed by induction on `k with`. Consider the case `zero`. Take `⟨e⟩` from `oneL A ((A ⧸ I) × (A ⧸ J))`. Set `e'` to `e.trans (Algebra.TensorProduct.rid A A ((A ⧸ I) × (A ⧸ J))).symm`. Conclude with `⟨good_congr q I J e'.symm (main_step q I J A h0), hinv_of_algEquiv e'.symm (main_fin q I J A h0)⟩`.

Consider the case `succ k ih`. Take `⟨e⟩` from `succL A ((A ⧸ I) × (A ⧸ J)) k`. Conclude with `⟨good_congr q I J e.symm (main_step q I J _ ih.1), hinv_of_algEquiv e.symm (main_fin q I J _ ih.1)⟩`.
-/
theorem tensorPow (q : ℕ) [NeZero q] (I J : Ideal A)
    (hI : HInv q (A ⧸ I)) (hJ : HInv q (A ⧸ J)) (hIJ : HInv q (A ⧸ (I ⊔ J))) (k : ℕ) :
    (∀ L, Good I J L → HInv q ((A ⧸ L) ⊗[A] PiTensorProduct A (fun _ : Fin (k + 1) => (A ⧸ I) × (A ⧸ J)))) ∧
    HInv q (PiTensorProduct A (fun _ : Fin (k + 1) => (A ⧸ I) × (A ⧸ J))) := by
  have h0 : ∀ L, Good I J L → HInv q ((A ⧸ L) ⊗[A] A) := by
    intro L hL
    refine hinv_of_algEquiv (Algebra.TensorProduct.rid A A (A ⧸ L)).symm ?_
    rcases hL with rfl | rfl | rfl
    exacts [hI, hJ, hIJ]
  induction k with
  | zero =>
    obtain ⟨e⟩ := oneL A ((A ⧸ I) × (A ⧸ J))
    let e' := e.trans (Algebra.TensorProduct.rid A A ((A ⧸ I) × (A ⧸ J))).symm
    exact ⟨good_congr q I J e'.symm (main_step q I J A h0),
      hinv_of_algEquiv e'.symm (main_fin q I J A h0)⟩
  | succ k ih =>
    obtain ⟨e⟩ := succL A ((A ⧸ I) × (A ⧸ J)) k
    exact ⟨good_congr q I J e.symm (main_step q I J _ ih.1),
      hinv_of_algEquiv e.symm (main_fin q I J _ ih.1)⟩

/- English proof (translation)
Introduce `q _ A _ I J hn hq hI hJ hIJ`. Use `GlobalTheory.T.etaleHomotopyInvariance_cechDescent_integral q A ((A ⧸ I) × (A ⧸ J)) inferInstance ?_ hq (fun k => (tensorPow q I J hI hJ hIJ k).2)` and prove the remaining obligations. Introduce `x hx`. Apply `hn` to reduce the goal to its premises. Rewrite `hx` using `[RingHom.mem_ker]`.

Establish `h1` using `congrArg Prod.fst hx`. Establish `h2` using `congrArg Prod.snd hx`. Simplify using `only [Prod.fst_zero, Prod.snd_zero] at h1 h2`. Conclude with `⟨Ideal.Quotient.eq_zero_iff_mem.mp h1, Ideal.Quotient.eq_zero_iff_mem.mp h2⟩`.
-/
theorem closedCover : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (I J : Ideal A), I ⊓ J ≤ nilradical A →
    IsUnit (q : A) → HInv q (A ⧸ I) → HInv q (A ⧸ J) → HInv q (A ⧸ (I ⊔ J)) → HInv q A := by
  intro q _ A _ I J hn hq hI hJ hIJ
  refine GlobalTheory.T.etaleHomotopyInvariance_cechDescent_integral q A ((A ⧸ I) × (A ⧸ J)) inferInstance ?_ hq (fun k => (tensorPow q I J hI hJ hIJ k).2)
  intro x hx
  apply hn
  rw [RingHom.mem_ker] at hx
  have h1 := congrArg Prod.fst hx
  have h2 := congrArg Prod.snd hx
  simp only [Prod.fst_zero, Prod.snd_zero] at h1 h2
  exact ⟨Ideal.Quotient.eq_zero_iff_mem.mp h1, Ideal.Quotient.eq_zero_iff_mem.mp h2⟩

end GlobalTheory.EtC.ClosedCover

namespace GlobalTheory.EtC.ClosedCover

end GlobalTheory.EtC.ClosedCover
