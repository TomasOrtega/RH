import Formalism.CharacterColumnKernels.StatementN
import Formalism.CharacterColumnKernels.IdempotentNormalForms.GenFin
import Formalism.CharacterColumnKernels.IdempotentNormalForms.DetTri
import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthKerOfDetEqZero
import Formalism.CharacterColumnKernels.IdempotentNormalForms.SingleEqSmul
import Formalism.CharacterColumnKernels.IdempotentNormalForms.VccSpan

open Finset

noncomputable section

namespace Formalism.NG

namespace GlobalDeterminantRelations

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X' : Type*}
  {d : Type} [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
  (x' : X')

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma evalSp_smul (r : R') (v : EvalSp O d R' x') (a : d) :
    (r • v : d → FractionRing O) a =
      ∑ b, (r : X' → Matrix d d (FractionRing O)) x' a b * (v : d → FractionRing O) b := rfl

instance : SMulCommClass R' (FractionRing O) (EvalSp O d R' x') where
  smul_comm r c v := by
    funext a
    change (∑ b, (r : X' → Matrix d d (FractionRing O)) x' a b * (c * (v : d → FractionRing O) b)) =
      c * ∑ b, (r : X' → Matrix d d (FractionRing O)) x' a b * (v : d → FractionRing O) b
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

instance : FiniteDimensional (FractionRing O) (EvalSp O d R' x') :=
  inferInstanceAs (FiniteDimensional (FractionRing O) (d → FractionRing O))

def curryE (g : Type) : (g × d → FractionRing O) ≃ₗ[FractionRing O] (g → EvalSp O d R' x') where
  toFun v i a := v (i, a)
  invFun w q := (w q.1 : d → FractionRing O) q.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/- English proof (translation)
Establish `hconj` using `LinearMap.det_conj (relMap (FractionRing O) (EvalSp O d R' x') Θ) (curryE R' x' g).symm`. Rewrite using `[← hconj, ← LinearMap.det_toLin']`. Use `congr 1`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`.

Use function extensionality and compare the values at `p`. Take `⟨i, a⟩` from `p`. Set `ev : EvalSp O d R' x' →+ FractionRing O` to `{ toFun := fun w => (w : d → FractionRing O) a map_zero' := rfl map_add' := fun _ _ => rfl }`. Use `show ev (∑ j, Θ i j • (curryE R' x' g v) j) = Matrix.mulVec (bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ) v (i, a)`. Rewrite using `[map_sum]`.

Establish `hev : ∀ j, ev (Θ i j • (curryE R' x' g v) j) = ∑ b, (Θ i j : X' → Matrix d d (FractionRing O)) x' a b * v (j, b)` using `fun j => evalSp_smul R' x' (Θ i j) ((curryE R' x' g v) j) a`. Rewrite using `[Finset.sum_congr rfl (fun j _ => hev j), Matrix.mulVec]`. Use `first`. Consider the case `(rw [dotProduct, Fintype.sum_prod_type]; rfl)`. Consider the case `(rw [Matrix.dotProduct, Fintype.sum_prod_type]; rfl)`.

Consider the case `(simp only [dotProduct, Fintype.sum_prod_type]; rfl)`.
-/
lemma det_relMap_eq (g : Type) [Fintype g] [DecidableEq g] (Θ : Matrix g g R') :
    LinearMap.det (relMap (FractionRing O) (EvalSp O d R' x') Θ) =
      (bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ).det := by
  have hconj := LinearMap.det_conj (relMap (FractionRing O) (EvalSp O d R' x') Θ) (curryE R' x' g).symm
  rw [← hconj, ← LinearMap.det_toLin']
  congr 1
  apply LinearMap.ext
  intro v
  funext p
  obtain ⟨i, a⟩ := p
  let ev : EvalSp O d R' x' →+ FractionRing O :=
    { toFun := fun w => (w : d → FractionRing O) a
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  show ev (∑ j, Θ i j • (curryE R' x' g v) j) =
    Matrix.mulVec (bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ) v (i, a)
  rw [map_sum]
  have hev : ∀ j, ev (Θ i j • (curryE R' x' g v) j) =
      ∑ b, (Θ i j : X' → Matrix d d (FractionRing O)) x' a b * v (j, b) := fun j =>
    evalSp_smul R' x' (Θ i j) ((curryE R' x' g v) j) a
  rw [Finset.sum_congr rfl (fun j _ => hev j), Matrix.mulVec]
  first
    | (rw [dotProduct, Fintype.sum_prod_type]; rfl)
    | (rw [Matrix.dotProduct, Fintype.sum_prod_type]; rfl)
    | (simp only [dotProduct, Fintype.sum_prod_type]; rfl)

end GlobalDeterminantRelations

universe u v w

open GlobalDeterminantRelations in
/- English proof (translation)
Introduce `O _ _ _ X X' T T' Z p q b hT hZ d _ _ R' m g _ _ _ P hdet hφ π' ρπ hρπ α _ _ bl hbl ρk hsurj hblk hcard`. Take `⟨C, hC⟩` from `genericFin R' O m g α (fun k => {a // bl a = k}) hcard ρk hsurj P`. Take `⟨f, hfT, hf⟩` from `hdet (C * P)`. Establish `hcomp : ∀ (x' : X') (v : g → EvalSp O d R' x'), relMap (FractionRing O) (EvalSp O d R' x') (C * P) v = relMap (FractionRing O) (EvalSp O d R' x') C (relMap (FractionRing O) (EvalSp O d R' x') P v)`. Introduce `x' v`.

Use function extensionality and compare the values at `i`. Use `show ∑ j, (C * P) i j • v j = ∑ l, C i l • ∑ j, P l j • v j`. Simplify using `only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]`. Conclude with `Finset.sum_comm`. Establish `hvanish : ∀ x', p x' ∉ Z → f x' = 0`.

Introduce `x' hx`. Take `⟨φ, hφ0⟩` from `hφ x' hx`. Set `e` to `(homEquiv P : (Coker P →ₗ[R'] EvalSp O d R' x') ≃ₗ[FractionRing O] LinearMap.ker (relMap (FractionRing O) (EvalSp O d R' x') P))`. Establish `hne : e φ ≠ 0` using `fun h => hφ0 (e.injective (h.trans (map_zero e).symm))`. Establish `hv0 : ((e φ : LinearMap.ker _) : g → EvalSp O d R' x') ≠ 0` using `fun h => hne (Subtype.ext h)`.

Establish `hvk` using `LinearMap.mem_ker.mp (e φ).2`. Establish `hnot : ¬ Function.Injective (relMap (FractionRing O) (EvalSp O d R' x') (C * P))`. Introduce `hinj`. Apply `hv0` to reduce the goal to its premises. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[hcomp, hvk, map_zero, map_zero]`. Establish `hdet0 : LinearMap.det (relMap (FractionRing O) (EvalSp O d R' x') (C * P)) = 0`. Assume the negation of the conclusion as `hne'`. Apply `hnot` to reduce the goal to its premises. Establish `hu : IsUnit (relMap (FractionRing O) (EvalSp O d R' x') (C * P))` using `(LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hne')`.

Conclude with `((Module.End.isUnit_iff _).mp hu).injective`. Rewrite `hdet0` using `[GlobalDeterminantRelations.det_relMap_eq]`. Apply `IsFractionRing.injective O (FractionRing O)` to reduce the goal to its premises. Rewrite using `[hf x', hdet0, map_zero]`. Establish `hspan` using `hD O X X' T T' Z p q b hT hZ f hfT hvanish π'`.

Use `(hV O X T Z (p π') (f π') hspan).trans (le_of_eq ?_)` and prove the remaining obligations. Establish `hfπ : f π' = (bigMat (fun r : R' => ρπ r) (C * P)).det`. Apply `IsFractionRing.injective O (FractionRing O)` to reduce the goal to its premises. Rewrite using `[hf π', RingHom.map_det]`. Use `congr 1`.

Use `Matrix.ext fun x y => ?_` and prove the remaining obligations. Simplify using `[bigMat, RingHom.mapMatrix_apply, ← hρπ]`. Break down `isEmpty_or_nonempty g with hg | hg` into its components or cases. Establish `h1 : f π' = 1`. Rewrite using `[hfπ]`.

Conclude with `Matrix.det_isEmpty`. Rewrite using `[h1, IsDiscreteValuationRing.addVal_one]`. Use `symm`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Module.length_eq_zero_iff]`.

Conclude with `⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩`. Establish `hBT : (bigMat (fun r : R' => ρπ r) (C * P)).BlockTriangular (fun x : g × d => bl x.2)`. Introduce `x y hxy`. Conclude with `hbl _ hxy`. Establish `himage : (Finset.univ.image fun x : g × d => bl x.2) = Finset.univ.image bl`.

Use extensionality with `k`. Simplify using `only [Finset.mem_image, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx⟩`. Conclude with `⟨x.2, hx⟩`.

Introduce and unpack `⟨a, ha⟩`. Conclude with `⟨(Classical.arbitrary g, a), ha⟩`. Establish `hprod : ∀ (s : Finset α) (F : α → O), IsDiscreteValuationRing.addVal O (∏ k ∈ s, F k) = ∑ k ∈ s, IsDiscreteValuationRing.addVal O (F k)`. Introduce `s F`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations.

Rewrite using `[Finset.prod_empty, Finset.sum_empty, IsDiscreteValuationRing.addVal_one]`. Introduce `a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha, IsDiscreteValuationRing.addVal_mul, ih]`. Establish `hblock : ∀ k, ((bigMat (fun r : R' => ρπ r) (C * P)).toSquareBlock (fun x : g × d => bl x.2) k).det = (bigMat (fun r : R' => ρk k r) (C * P)).det`. Introduce `k`.

Set `eK : g × {a // bl a = k} ≃ {x : g × d // bl x.2 = k}` to `{ toFun := fun y => ⟨(y.1, y.2.1), y.2.2⟩ invFun := fun x => (x.1.1, ⟨x.1.2, x.2⟩) left_inv := fun _ => rfl right_inv := fun _ => rfl }`. Rewrite using `[← Matrix.det_reindex_self eK.symm]`. Use `congr 1`. Use `Matrix.ext fun x y => ?_` and prove the remaining obligations. Take `⟨pp, i⟩` from `x`.

Take `⟨qq, j⟩` from `y`. Use `show _ = (ρk k) ((C * P) pp qq) i j`. Rewrite using `[← hblk]`. Both sides reduce to the same expression. Rewrite using `[hfπ, hBT.det, hprod, himage]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hblock k, ← (lenKer : StatLenKer) O _ (bigMat (fun r : R' => ρk k r) (C * P))]`. Conclude with `hC k`.
-/
theorem globalConcrete_of (hD : StatDescent.{u, v, w}) (hV : StatVccSpan.{u, v}) :
    CharacterColumnGlobal.{u, v, w} := by
  intro O _ _ _ X X' T T' Z p q b hT hZ d _ _ R' m g _ _ _ P hdet hφ π' ρπ hρπ α _ _ bl hbl ρk
    hsurj hblk hcard
  classical
  obtain ⟨C, hC⟩ := genericFin R' O m g α (fun k => {a // bl a = k}) hcard ρk hsurj P
  obtain ⟨f, hfT, hf⟩ := hdet (C * P)
  have hcomp : ∀ (x' : X') (v : g → EvalSp O d R' x'),
      relMap (FractionRing O) (EvalSp O d R' x') (C * P) v =
        relMap (FractionRing O) (EvalSp O d R' x') C (relMap (FractionRing O) (EvalSp O d R' x') P v) := by
    intro x' v
    funext i
    show ∑ j, (C * P) i j • v j = ∑ l, C i l • ∑ j, P l j • v j
    simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
    exact Finset.sum_comm
  have hvanish : ∀ x', p x' ∉ Z → f x' = 0 := by
    intro x' hx
    obtain ⟨φ, hφ0⟩ := hφ x' hx
    let e := (homEquiv P : (Coker P →ₗ[R'] EvalSp O d R' x') ≃ₗ[FractionRing O]
      LinearMap.ker (relMap (FractionRing O) (EvalSp O d R' x') P))
    have hne : e φ ≠ 0 := fun h => hφ0 (e.injective (h.trans (map_zero e).symm))
    have hv0 : ((e φ : LinearMap.ker _) : g → EvalSp O d R' x') ≠ 0 := fun h => hne (Subtype.ext h)
    have hvk := LinearMap.mem_ker.mp (e φ).2
    have hnot : ¬ Function.Injective (relMap (FractionRing O) (EvalSp O d R' x') (C * P)) := by
      intro hinj
      apply hv0
      apply hinj
      rw [hcomp, hvk, map_zero, map_zero]
    have hdet0 : LinearMap.det (relMap (FractionRing O) (EvalSp O d R' x') (C * P)) = 0 := by
      by_contra hne'
      apply hnot
      have hu : IsUnit (relMap (FractionRing O) (EvalSp O d R' x') (C * P)) :=
        (LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hne')
      exact ((Module.End.isUnit_iff _).mp hu).injective
    rw [GlobalDeterminantRelations.det_relMap_eq] at hdet0
    apply IsFractionRing.injective O (FractionRing O)
    rw [hf x', hdet0, map_zero]
  have hspan := hD O X X' T T' Z p q b hT hZ f hfT hvanish π'
  refine (hV O X T Z (p π') (f π') hspan).trans (le_of_eq ?_)
  have hfπ : f π' = (bigMat (fun r : R' => ρπ r) (C * P)).det := by
    apply IsFractionRing.injective O (FractionRing O)
    rw [hf π', RingHom.map_det]
    congr 1
    refine Matrix.ext fun x y => ?_
    simp [bigMat, RingHom.mapMatrix_apply, ← hρπ]
  rcases isEmpty_or_nonempty g with hg | hg
  · have h1 : f π' = 1 := by
      rw [hfπ]
      exact Matrix.det_isEmpty
    rw [h1, IsDiscreteValuationRing.addVal_one]
    symm
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Module.length_eq_zero_iff]
    exact ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  have hBT : (bigMat (fun r : R' => ρπ r) (C * P)).BlockTriangular (fun x : g × d => bl x.2) := by
    intro x y hxy
    exact hbl _ hxy
  have himage : (Finset.univ.image fun x : g × d => bl x.2) = Finset.univ.image bl := by
    ext k
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x.2, hx⟩
    · rintro ⟨a, ha⟩
      exact ⟨(Classical.arbitrary g, a), ha⟩
  have hprod : ∀ (s : Finset α) (F : α → O), IsDiscreteValuationRing.addVal O (∏ k ∈ s, F k) =
      ∑ k ∈ s, IsDiscreteValuationRing.addVal O (F k) := by
    intro s F
    refine Finset.induction_on s ?_ ?_
    · rw [Finset.prod_empty, Finset.sum_empty, IsDiscreteValuationRing.addVal_one]
    · intro a s ha ih
      rw [Finset.prod_insert ha, Finset.sum_insert ha, IsDiscreteValuationRing.addVal_mul, ih]
  have hblock : ∀ k, ((bigMat (fun r : R' => ρπ r) (C * P)).toSquareBlock
      (fun x : g × d => bl x.2) k).det = (bigMat (fun r : R' => ρk k r) (C * P)).det := by
    intro k
    let eK : g × {a // bl a = k} ≃ {x : g × d // bl x.2 = k} :=
      { toFun := fun y => ⟨(y.1, y.2.1), y.2.2⟩
        invFun := fun x => (x.1.1, ⟨x.1.2, x.2⟩)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← Matrix.det_reindex_self eK.symm]
    congr 1
    refine Matrix.ext fun x y => ?_
    obtain ⟨pp, i⟩ := x
    obtain ⟨qq, j⟩ := y
    show _ = (ρk k) ((C * P) pp qq) i j
    rw [← hblk]
    rfl
  rw [hfπ, hBT.det, hprod, himage]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hblock k, ← (lenKer : StatLenKer) O _ (bigMat (fun r : R' => ρk k r) (C * P))]
  exact hC k

/- English proof (translation)
The claim follows from `globalConcrete_of descent vccSpan`.
-/
theorem globalConcrete : CharacterColumnGlobal := globalConcrete_of descent vccSpan

end Formalism.NG
