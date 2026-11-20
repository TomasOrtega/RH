import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.CharpolyRevMap

open Module

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

section Normal

variable {O : Type*} [CommRing O] {r : Type} [Fintype r] [DecidableEq r]

/- English proof (translation)
Establish `hsurj : Function.Surjective (Submodule.linearProjOfIsCompl p q h)` using `fun x => ⟨(x : r → O), Submodule.linearProjOfIsCompl_apply_left h x⟩`. Establish `hfin : Module.Finite O p` using `Module.Finite.of_surjective _ hsurj`. Use `haveI : Module.Projective O p := Module.Projective.of_split p.subtype (Submodule.linearProjOfIsCompl p q h) (LinearMap.ext fun x => Submodule.linearProjOfIsCompl_apply_left h x)`. Use `haveI : Module.FinitePresentation O p := by first`. Consider the case `infer_instance`.

Consider the case `exact Module.finitePresentation_of_projective _ _`. Consider the case `exact Module.finitePresentation_of_projective`. Conclude with `⟨Module.free_of_flat_of_isLocalRing, hfin⟩`.
-/
theorem free_of_isCompl [IsLocalRing O] (p q : Submodule O (r → O)) (h : IsCompl p q) :
    Module.Free O p ∧ Module.Finite O p := by
  have hsurj : Function.Surjective (Submodule.linearProjOfIsCompl p q h) :=
    fun x => ⟨(x : r → O), Submodule.linearProjOfIsCompl_apply_left h x⟩
  have hfin : Module.Finite O p := Module.Finite.of_surjective _ hsurj
  haveI : Module.Projective O p :=
    Module.Projective.of_split p.subtype (Submodule.linearProjOfIsCompl p q h)
      (LinearMap.ext fun x => Submodule.linearProjOfIsCompl_apply_left h x)
  haveI : Module.FinitePresentation O p := by
    first
    | infer_instance
    | exact Module.finitePresentation_of_projective _ _
    | exact Module.finitePresentation_of_projective
  exact ⟨Module.free_of_flat_of_isLocalRing, hfin⟩

/- English proof (translation)
Set `E : (r → O) →ₗ[O] (r → O)` to `Matrix.toLin' e`. Establish `hE : IsIdempotentElem E`. Establish `h : E * E = E` using `by rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, he.eq]`. Conclude with `h`. Establish `hC : IsCompl (LinearMap.range E) (LinearMap.ker E)` using `LinearMap.IsIdempotentElem.isCompl hE`.

Take `⟨_, _⟩` from `free_of_isCompl _ _ hC`. Take `⟨_, _⟩` from `free_of_isCompl _ _ hC.symm`. Set `bR` to `Module.Free.chooseBasis O (LinearMap.range E)`. Set `bK` to `Module.Free.chooseBasis O (LinearMap.ker E)`. Set `B` to `(bR.prod bK).map (Submodule.prodEquivOfIsCompl _ _ hC)`.

Set `σ` to `B.indexEquiv (Pi.basisFun O r)`. Set `B'` to `B.reindex σ`. Establish `key : ∀ j, E (B' j) = (if (σ.symm j).isLeft then 1 else 0 : O) • B' j`. Introduce `j`. Simplify using `only [B', Module.Basis.reindex_apply]`.

Break down `σ.symm j with a | b` into its components or cases. Establish `hm : (B (Sum.inl a)) ∈ LinearMap.range E`. Simplify using `[B, Module.Basis.prod_apply]`. Simplify using `using ((LinearMap.IsIdempotentElem.mem_range_iff hE).mp hm)`. Establish `hm : (B (Sum.inr b)) ∈ LinearMap.ker E`.

Simplify using `[B, Module.Basis.prod_apply]`. Simplify using `using hm`. Apply the tactic sequence `refine ⟨(Pi.basisFun O r).toMatrix B', B'.toMatrix (Pi.basisFun O r), fun j => if (σ.symm j).isLeft then 1 else 0, fun j => by dsimp only; split_ifs <;> simp, Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _, ?_⟩`. Establish `hEP : e * (Pi.basisFun O r).toMatrix B' = (Pi.basisFun O r).toMatrix B' * Matrix.diagonal (fun j => if (σ.symm j).isLeft then 1 else 0)`. Use extensionality with `i j`.

Rewrite using `[Matrix.mul_diagonal]`. Use `congrFun (key j) i` as an intermediate fact. Simplify using `only [E, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this`. Simplify using `only [Matrix.mul_apply, Module.Basis.toMatrix_apply, Pi.basisFun_repr]`. Rewrite using `[this, mul_comm]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.mul_one]`. Use `_ = _ := by rw [← Matrix.mul_assoc, hEP]`.
-/
theorem idem_normal_form [IsLocalRing O] (e : Matrix r r O) (he : IsIdempotentElem e) :
    ∃ (P Q : Matrix r r O) (d : r → O), (∀ j, d j = 0 ∨ d j = 1) ∧ P * Q = 1 ∧ Q * P = 1 ∧
      e = P * Matrix.diagonal d * Q := by
  classical
  let E : (r → O) →ₗ[O] (r → O) := Matrix.toLin' e
  have hE : IsIdempotentElem E := by
    have h : E * E = E := by rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, he.eq]
    exact h
  have hC : IsCompl (LinearMap.range E) (LinearMap.ker E) := LinearMap.IsIdempotentElem.isCompl hE
  obtain ⟨_, _⟩ := free_of_isCompl _ _ hC
  obtain ⟨_, _⟩ := free_of_isCompl _ _ hC.symm
  let bR := Module.Free.chooseBasis O (LinearMap.range E)
  let bK := Module.Free.chooseBasis O (LinearMap.ker E)
  let B := (bR.prod bK).map (Submodule.prodEquivOfIsCompl _ _ hC)
  let σ := B.indexEquiv (Pi.basisFun O r)
  let B' := B.reindex σ
  have key : ∀ j, E (B' j) = (if (σ.symm j).isLeft then 1 else 0 : O) • B' j := by
    intro j
    simp only [B', Module.Basis.reindex_apply]
    rcases σ.symm j with a | b
    · have hm : (B (Sum.inl a)) ∈ LinearMap.range E := by
        simp [B, Module.Basis.prod_apply]
      simpa using ((LinearMap.IsIdempotentElem.mem_range_iff hE).mp hm)
    · have hm : (B (Sum.inr b)) ∈ LinearMap.ker E := by
        simp [B, Module.Basis.prod_apply]
      simpa using hm
  refine ⟨(Pi.basisFun O r).toMatrix B', B'.toMatrix (Pi.basisFun O r),
    fun j => if (σ.symm j).isLeft then 1 else 0, fun j => by dsimp only; split_ifs <;> simp,
    Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _, ?_⟩
  have hEP : e * (Pi.basisFun O r).toMatrix B' = (Pi.basisFun O r).toMatrix B' *
      Matrix.diagonal (fun j => if (σ.symm j).isLeft then 1 else 0) := by
    ext i j
    rw [Matrix.mul_diagonal]
    have := congrFun (key j) i
    simp only [E, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Pi.smul_apply,
      smul_eq_mul] at this
    simp only [Matrix.mul_apply, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rw [this, mul_comm]
  calc e = e * ((Pi.basisFun O r).toMatrix B' * B'.toMatrix (Pi.basisFun O r)) := by
        rw [Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, hEP]

/- English proof (translation)
Use `haveI : Nontrivial O := f.domain_nontrivial`. Establish `hmap : (P * Matrix.diagonal d * Q).map f = P.map f * Matrix.diagonal (fun j => f (d j)) * Q.map f`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero f)]`. Establish `h1 : P.map f * Q.map f = 1`. Simplify `congrArg (fun M => M.map f) hPQ` using `[Matrix.map_mul]`.

Establish `h2 : Q.map f * P.map f = 1`. Simplify `congrArg (fun M => M.map f) hQP` using `[Matrix.map_mul]`. Establish `hPu : IsUnit (P.map f).det` using `Matrix.isUnit_det_of_right_inverse h1`. Establish `hQu : IsUnit (Q.map f).det` using `Matrix.isUnit_det_of_right_inverse h2`. Rewrite using `[hmap, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hQu, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hPu, Matrix.rank_diagonal, Nat.card_eq_fintype_card]`.

Apply `Fintype.card_congr` to reduce the goal to its premises. Apply the tactic sequence `exact Equiv.subtypeEquivRight fun j => by rcases hd j with h | h <;> simp [h]`.
-/
theorem rank_map_conj {F : Type*} [Field F] (f : O →+* F) (P Q : Matrix r r O) (d : r → O)
    (hd : ∀ j, d j = 0 ∨ d j = 1) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    ((P * Matrix.diagonal d * Q).map f).rank = Nat.card {j // d j = 1} := by
  classical
  haveI : Nontrivial O := f.domain_nontrivial
  have hmap : (P * Matrix.diagonal d * Q).map f = P.map f * Matrix.diagonal (fun j => f (d j)) * Q.map f := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero f)]
  have h1 : P.map f * Q.map f = 1 := by
    simpa [Matrix.map_mul] using congrArg (fun M => M.map f) hPQ
  have h2 : Q.map f * P.map f = 1 := by
    simpa [Matrix.map_mul] using congrArg (fun M => M.map f) hQP
  have hPu : IsUnit (P.map f).det := Matrix.isUnit_det_of_right_inverse h1
  have hQu : IsUnit (Q.map f).det := Matrix.isUnit_det_of_right_inverse h2
  rw [hmap, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hQu, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hPu,
    Matrix.rank_diagonal, Nat.card_eq_fintype_card]
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight fun j => by rcases hd j with h | h <;> simp [h]

open Polynomial in
/- English proof (translation)
Establish `hPQ' : P.map (Polynomial.C : O →+* Polynomial O) * Q.map Polynomial.C = 1`. Simplify `congrArg (fun M => M.map (Polynomial.C : O →+* Polynomial O)) hPQ` using `[Matrix.map_mul]`. Establish `hdiag : Matrix.diagonal (fun j => (1 : Polynomial O) - Polynomial.X * Polynomial.C (d j)) = 1 - (Polynomial.X : Polynomial O) • Matrix.diagonal (fun j => Polynomial.C (d j))`. Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i = j <;> simp [h, Matrix.diagonal_apply, Matrix.one_apply]`.

Establish `key : (1 : Matrix r r (Polynomial O)) - (Polynomial.X : Polynomial O) • (P * Matrix.diagonal d * Q).map Polynomial.C = P.map Polynomial.C * Matrix.diagonal (fun j => 1 - Polynomial.X * Polynomial.C (d j)) * Q.map Polynomial.C`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero _), hdiag, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPQ', Matrix.mul_smul, Matrix.smul_mul]`. Establish `hfac : ∀ j, ((1 : Polynomial O) - Polynomial.X * Polynomial.C (d j)) = if d j = 1 then 1 - Polynomial.X else 1` using `fun j => by`. Apply the tactic sequence `rcases hd j with h | h <;> simp [h]`. Unfold `Matrix.charpolyRev`.

Rewrite using `[key, Matrix.det_mul, Matrix.det_mul, mul_comm (Matrix.det (P.map Polynomial.C)), mul_assoc, ← Matrix.det_mul, hPQ', Matrix.det_one, mul_one, Matrix.det_diagonal]`. Repeatedly rewrite using `[hfac]`. Rewrite using `[Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]`. Use `congr 1`. Simplify using `[Nat.card_eq_fintype_card, Fintype.card_subtype]`.
-/
theorem charpolyRev_conj [Nontrivial O] (P Q : Matrix r r O) (d : r → O)
    (hd : ∀ j, d j = 0 ∨ d j = 1) (hPQ : P * Q = 1) :
    (P * Matrix.diagonal d * Q).charpolyRev = (1 - X) ^ (Nat.card {j // d j = 1}) := by
  classical
  have hPQ' : P.map (Polynomial.C : O →+* Polynomial O) * Q.map Polynomial.C = 1 := by
    simpa [Matrix.map_mul] using congrArg (fun M => M.map (Polynomial.C : O →+* Polynomial O)) hPQ
  have hdiag : Matrix.diagonal (fun j => (1 : Polynomial O) - Polynomial.X * Polynomial.C (d j)) =
      1 - (Polynomial.X : Polynomial O) • Matrix.diagonal (fun j => Polynomial.C (d j)) := by
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.diagonal_apply, Matrix.one_apply]
  have key : (1 : Matrix r r (Polynomial O)) - (Polynomial.X : Polynomial O) •
      (P * Matrix.diagonal d * Q).map Polynomial.C =
      P.map Polynomial.C * Matrix.diagonal (fun j => 1 - Polynomial.X * Polynomial.C (d j)) *
        Q.map Polynomial.C := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero _), hdiag, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one, hPQ', Matrix.mul_smul, Matrix.smul_mul]
  have hfac : ∀ j, ((1 : Polynomial O) - Polynomial.X * Polynomial.C (d j)) =
      if d j = 1 then 1 - Polynomial.X else 1 := fun j => by
    rcases hd j with h | h <;> simp [h]
  unfold Matrix.charpolyRev
  rw [key, Matrix.det_mul, Matrix.det_mul, mul_comm (Matrix.det (P.map Polynomial.C)), mul_assoc,
    ← Matrix.det_mul, hPQ', Matrix.det_one, mul_one, Matrix.det_diagonal]
  simp_rw [hfac]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  congr 1
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype]

end Normal

open Polynomial in
/- English proof (translation)
Unfold `StatRankConst`. Introduce `O _ _ _ X T d _ _ hT e he hcoef x y`. Establish `hid : ∀ z, IsIdempotentElem (e z)` using `fun z => congrFun he z`. Use `choose P Q dd hdd hPQ hQP heq using fun z => idem_normal_form (e z) (hid z)`. Establish `hrk : ∀ z, ((e z).map (algebraMap O (FractionRing O))).rank = Nat.card {j // dd z j = 1}`.

Introduce `z`. Rewrite using `[heq z]`. Conclude with `rank_map_conj _ (P z) (Q z) (dd z) (hdd z) (hPQ z) (hQP z)`. Establish `hcp : ∀ z, (e z).charpolyRev = (1 - Polynomial.X) ^ Nat.card {j // dd z j = 1}`. Introduce `z`.

Rewrite using `[heq z]`. Conclude with `charpolyRev_conj (P z) (Q z) (dd z) (hdd z) (hPQ z)`. Rewrite using `[hrk, hrk]`. Establish `hres : ∀ k, IsLocalRing.residue O (((1 - Polynomial.X : Polynomial O) ^ Nat.card {j // dd x j = 1}).coeff k) = IsLocalRing.residue O (((1 - Polynomial.X : Polynomial O) ^ Nat.card {j // dd y j = 1}).coeff k)`. Introduce `k`.

Use `resConst O X T hT _ (hcoef k) x y` as an intermediate fact. Simplify `this` using `only [hcp]`. Establish `hpoly : ((1 - Polynomial.X : Polynomial O) ^ Nat.card {j // dd x j = 1}).map (IsLocalRing.residue O) = ((1 - Polynomial.X : Polynomial O) ^ Nat.card {j // dd y j = 1}).map (IsLocalRing.residue O)`. Use extensionality with `k`. Simplify using `only [Polynomial.coeff_map]`.

Conclude with `hres k`. Establish `hdeg : ∀ m : ℕ, (((1 - Polynomial.X : Polynomial O) ^ m).map (IsLocalRing.residue O)).natDegree = m`. Introduce `m`. Apply the tactic sequence `rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X, Polynomial.natDegree_pow, Polynomial.natDegree_sub_eq_right_of_natDegree_lt] <;> simp`. Use `congrArg Polynomial.natDegree hpoly` as an intermediate fact.

Rewrite `this` using `[hdeg, hdeg]`. Then use the resulting hypothesis.
-/
theorem rankConst : StatRankConst := by
  unfold StatRankConst
  intro O _ _ _ X T d _ _ hT e he hcoef x y
  classical
  have hid : ∀ z, IsIdempotentElem (e z) := fun z => congrFun he z
  choose P Q dd hdd hPQ hQP heq using fun z => idem_normal_form (e z) (hid z)
  have hrk : ∀ z, ((e z).map (algebraMap O (FractionRing O))).rank = Nat.card {j // dd z j = 1} := by
    intro z
    rw [heq z]
    exact rank_map_conj _ (P z) (Q z) (dd z) (hdd z) (hPQ z) (hQP z)
  have hcp : ∀ z, (e z).charpolyRev = (1 - Polynomial.X) ^ Nat.card {j // dd z j = 1} := by
    intro z
    rw [heq z]
    exact charpolyRev_conj (P z) (Q z) (dd z) (hdd z) (hPQ z)
  rw [hrk, hrk]
  have hres : ∀ k, IsLocalRing.residue O
      (((1 - Polynomial.X : Polynomial O) ^ Nat.card {j // dd x j = 1}).coeff k) =
      IsLocalRing.residue O (((1 - Polynomial.X : Polynomial O) ^ Nat.card {j // dd y j = 1}).coeff k) := by
    intro k
    have := resConst O X T hT _ (hcoef k) x y
    simpa only [hcp] using this
  have hpoly : ((1 - Polynomial.X : Polynomial O) ^ Nat.card {j // dd x j = 1}).map (IsLocalRing.residue O) =
      ((1 - Polynomial.X : Polynomial O) ^ Nat.card {j // dd y j = 1}).map (IsLocalRing.residue O) := by
    ext k
    simp only [Polynomial.coeff_map]
    exact hres k
  have hdeg : ∀ m : ℕ, (((1 - Polynomial.X : Polynomial O) ^ m).map (IsLocalRing.residue O)).natDegree = m := by
    intro m
    rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X, Polynomial.natDegree_pow,
      Polynomial.natDegree_sub_eq_right_of_natDegree_lt] <;> simp
  have := congrArg Polynomial.natDegree hpoly
  rwa [hdeg, hdeg] at this

end Formalism.RepresentationBoundsCohomology.ringDataObjects
