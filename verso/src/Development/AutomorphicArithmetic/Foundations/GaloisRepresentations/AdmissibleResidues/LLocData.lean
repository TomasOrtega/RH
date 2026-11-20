import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RealAway
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CsdSsOfFull
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.WdChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ArtinEl
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.NuChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.PairRel
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwJqEmbed
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwTamePair

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep

open Polynomial in
/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using `[Matrix.trace]`. Use `haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩`. Rewrite using `[Matrix.trace_eq_neg_charpoly_coeff, h, Fintype.card_fin]`. Establish `hc` using `prod_X_sub_C_coeff_card_pred (Finset.univ : Finset (Fin n)) c (by simp [hn])`.

Rewrite `hc` using `[Finset.card_univ, Fintype.card_fin]`. Rewrite using `[hc, neg_neg]`.
-/
private theorem trace_of_charpoly {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → ℂ)
    (h : M.charpoly = ∏ i, (X - C (c i))) : M.trace = ∑ i, c i := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Matrix.trace]
  · haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    rw [Matrix.trace_eq_neg_charpoly_coeff, h, Fintype.card_fin]
    have hc := prod_X_sub_C_coeff_card_pred (Finset.univ : Finset (Fin n)) c (by simp [hn])
    rw [Finset.card_univ, Fintype.card_fin] at hc
    rw [hc, neg_neg]

/- English proof (translation)
Establish `hi : IsIdempotentElem (Matrix.toLinAlgEquiv' E)`. Rewrite using `[IsIdempotentElem, ← map_mul, hE]`. Establish `h0 : LinearMap.trace ℂ (Fin n → ℂ) (Matrix.toLinAlgEquiv' E) = 0` using `by show LinearMap.trace ℂ (Fin n → ℂ) (Matrix.toLin' E) = 0`. Rewrite using `[Matrix.trace_toLin'_eq]`. Conclude with `ht`.

Establish `h1` using `LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hi h0`. Conclude with `Matrix.toLinAlgEquiv'.injective (by rw [h1, map_zero])`.
-/
private theorem eq_zero_of_idempotent_trace_zero {n : ℕ} (E : Matrix (Fin n) (Fin n) ℂ) (hE : E * E = E) (ht : E.trace = 0) :
    E = 0 := by
  have hi : IsIdempotentElem (Matrix.toLinAlgEquiv' E) := by
    rw [IsIdempotentElem, ← map_mul, hE]
  have h0 : LinearMap.trace ℂ (Fin n → ℂ) (Matrix.toLinAlgEquiv' E) = 0 := by
    show LinearMap.trace ℂ (Fin n → ℂ) (Matrix.toLin' E) = 0
    rw [Matrix.trace_toLin'_eq]
    exact ht
  have h1 := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hi h0
  exact Matrix.toLinAlgEquiv'.injective (by rw [h1, map_zero])

/- English proof (translation)
Establish `e : ((List.ofFn c).map fun a => M - a • (1 : Matrix (Fin n) (Fin n) ℂ)) = (List.ofFn fun i => Polynomial.X - Polynomial.C (c i)).map (Polynomial.aeval M)`. Rewrite using `[List.map_ofFn, List.map_ofFn]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `[Algebra.algebraMap_eq_smul_one]`.

Rewrite using `[e, ← map_list_prod, List.prod_ofFn, ← h, Matrix.aeval_self_charpoly]`.
-/
private theorem wdb_ofReal_eq_conj_wd_ofReal {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → ℂ)
    (h : M.charpoly = ∏ i, (Polynomial.X - Polynomial.C (c i))) :
    ((List.ofFn c).map fun a => M - a • (1 : Matrix (Fin n) (Fin n) ℂ)).prod = 0 := by
  have e : ((List.ofFn c).map fun a => M - a • (1 : Matrix (Fin n) (Fin n) ℂ)) =
      (List.ofFn fun i => Polynomial.X - Polynomial.C (c i)).map (Polynomial.aeval M) := by
    rw [List.map_ofFn, List.map_ofFn]
    congr 1
    funext i
    simp [Algebra.algebraMap_eq_smul_one]
  rw [e, ← map_list_prod, List.prod_ofFn, ← h, Matrix.aeval_self_charpoly]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons b l ih`. Rewrite using `[List.map_cons, List.prod_cons, mul_assoc, ih, Matrix.mul_smul, sub_mul, h, smul_mul_assoc, one_mul, ← sub_smul, smul_smul, List.map_cons, List.prod_cons]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem list_prod_sub_smul_mul_eigenvector {n : ℕ} (D W : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (h : D * W = c • W)
    (l : List ℂ) :
    (l.map fun b => D - b • (1 : Matrix (Fin n) (Fin n) ℂ)).prod * W = (l.map fun b => c - b).prod • W := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [List.map_cons, List.prod_cons, mul_assoc, ih, Matrix.mul_smul, sub_mul, h, smul_mul_assoc,
      one_mul, ← sub_smul, smul_smul, List.map_cons, List.prod_cons]
    congr 1
    ring

/- English proof (translation)
Establish `hk : ∀ k : ℕ, D ^ k * W = c ^ k • W`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ihk => rw [pow_succ', mul_assoc, ihk, Matrix.mul_smul, h, smul_smul, pow_succ, mul_comm]`.

Use `Polynomial.induction_on p ?_ ?_ ?_` and prove the remaining obligations. Introduce `a`. Simplify using `[Algebra.algebraMap_eq_smul_one]`. Introduce `p r hp hr`. Simplify using `[add_mul, hp, hr, add_smul]`.

Introduce `k a _`. Simplify using `[Algebra.algebraMap_eq_smul_one, smul_mul_assoc, mul_assoc, hk, smul_smul]`.
-/
private theorem aeval_mul_eigenvector {n : ℕ} (D W : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (h : D * W = c • W)
    (p : Polynomial ℂ) : Polynomial.aeval D p * W = p.eval c • W := by
  have hk : ∀ k : ℕ, D ^ k * W = c ^ k • W := by
    intro k
    induction k with
    | zero => simp
    | succ k ihk => rw [pow_succ', mul_assoc, ihk, Matrix.mul_smul, h, smul_smul, pow_succ, mul_comm]
  refine Polynomial.induction_on p ?_ ?_ ?_
  · intro a
    simp [Algebra.algebraMap_eq_smul_one]
  · intro p r hp hr
    simp [add_mul, hp, hr, add_smul]
  · intro k a _
    simp [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, mul_assoc, hk, smul_smul]

/- English proof (translation)
Establish `K : ∀ l : List ℂ, L * (L * ((l.map fun a => D - a • (1 : Matrix (Fin n) (Fin n) ℂ)).prod * L ^ m)) = 0`. Introduce `l`. Proceed by induction on `l with`. Consider the case `nil`. Simplify using `only [List.map_nil, List.prod_nil, one_mul]`.

Rewrite using `[← pow_succ', ← pow_succ']`. Conclude with `hm`. Consider the case `cons a l ih`. Simplify using `only [List.map_cons, List.prod_cons, mul_assoc, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul]`. Simplify using `only [hLD, hLS, ih, mul_zero, smul_zero, sub_zero]`.

Establish `Y : ∀ l : List ℂ, L * ((l.map fun a => D - a • (1 : Matrix (Fin n) (Fin n) ℂ)).prod * L ^ m) = (l.map fun a => q • D - a • (1 : Matrix (Fin n) (Fin n) ℂ)).prod * L ^ (m + 1)`. Introduce `l`. Proceed by induction on `l with`. Consider the case `nil`. Simplify using `only [List.map_nil, List.prod_nil, one_mul]`.

Rewrite using `[pow_succ']`. Consider the case `cons a l ih`. Simplify using `only [List.map_cons, List.prod_cons, mul_assoc, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul]`. Simplify using `only [hLD, hS, mul_add, mul_smul_comm, hLH]`. Rewrite using `[K l]`.

Simplify using `only [mul_zero, add_zero, ih]`. Establish `h0` using `Y lam`. Rewrite `h0` using `[hD, zero_mul, mul_zero]`. Establish `peel : ∀ l' : List ℂ, (∀ a ∈ l', ∀ b ∈ lam, a ≠ q * b) → ∀ Z : Matrix (Fin n) (Fin n) ℂ, (l'.map fun a => q • D - a • (1 : Matrix (Fin n) (Fin n) ℂ)).prod * Z = 0 → Z = 0`. Introduce `l'`.

Proceed by induction on `l' with`. Consider the case `nil`. Introduce `_ Z hZ`. Simplify using `using hZ`. Consider the case `cons a l' ih`.

Introduce `hl Z hZ`. Rewrite `hZ` using `[List.map_cons, List.prod_cons, mul_assoc]`. Apply `ih (fun a' ha' => hl a' (List.mem_cons_of_mem _ ha')) Z` to reduce the goal to its premises. Use `set W := (l'.map fun a => q • D - a • (1 : Matrix (Fin n) (Fin n) ℂ)).prod * Z`. Establish `hqW : q • (D * W) = a • W`.

Rewrite `hZ` using `[sub_mul, sub_eq_zero, smul_mul_assoc, smul_mul_assoc, one_mul]`. Conclude with `hZ`. Establish `hW : D * W = (a / q) • W`. Combine the equalities or inequalities in the displayed calculation. Establish `e` using `list_prod_sub_smul_mul_eigenvector D W (a / q) hW lam`.

Rewrite `e` using `[hD, zero_mul]`. Establish `hne : (lam.map fun b => a / q - b).prod ≠ 0`. Introduce `hp`. Rewrite `hp` using `[List.prod_eq_zero_iff, List.mem_map]`. Take `⟨b, hb, hb0⟩` from `hp`.

Establish `hab : a / q = b` using `sub_eq_zero.1 hb0`. Rewrite `hab` using `[div_eq_iff hq]`. Conclude with `hl a (by simp) b hb (by rw [hab, mul_comm])`. Conclude with `(smul_eq_zero.1 e.symm).resolve_left hne`. Conclude with `peel lam hlam _ h0.symm`.
-/
private theorem nilpotent_index_drop_of_relations {n : ℕ} (D L S H : Matrix (Fin n) (Fin n) ℂ) (q : ℂ) (lam : List ℂ)
    (hD : (lam.map fun a => D - a • (1 : Matrix (Fin n) (Fin n) ℂ)).prod = 0)
    (hq : q ≠ 0) (hlam : ∀ a ∈ lam, ∀ b ∈ lam, a ≠ q * b)
    (hLD : ∀ X, L * (D * X) = D * (L * (S * X)))
    (hS : ∀ X, S * X = q • X + L * (H * X))
    (hLH : ∀ X, L * (H * X) = H * (L * X))
    (hLS : ∀ X, L * (S * X) = S * (L * X))
    (m : ℕ) (hm : L ^ (m + 2) = 0) : L ^ (m + 1) = 0 := by
  have K : ∀ l : List ℂ,
      L * (L * ((l.map fun a => D - a • (1 : Matrix (Fin n) (Fin n) ℂ)).prod * L ^ m)) = 0 := by
    intro l
    induction l with
    | nil =>
      simp only [List.map_nil, List.prod_nil, one_mul]
      rw [← pow_succ', ← pow_succ']
      exact hm
    | cons a l ih =>
      simp only [List.map_cons, List.prod_cons, mul_assoc, sub_mul, mul_sub, smul_mul_assoc,
        mul_smul_comm, one_mul]
      simp only [hLD, hLS, ih, mul_zero, smul_zero, sub_zero]
  have Y : ∀ l : List ℂ,
      L * ((l.map fun a => D - a • (1 : Matrix (Fin n) (Fin n) ℂ)).prod * L ^ m) =
        (l.map fun a => q • D - a • (1 : Matrix (Fin n) (Fin n) ℂ)).prod * L ^ (m + 1) := by
    intro l
    induction l with
    | nil =>
      simp only [List.map_nil, List.prod_nil, one_mul]
      rw [pow_succ']
    | cons a l ih =>
      simp only [List.map_cons, List.prod_cons, mul_assoc, sub_mul, mul_sub, smul_mul_assoc,
        mul_smul_comm, one_mul]
      simp only [hLD, hS, mul_add, mul_smul_comm, hLH]
      rw [K l]
      simp only [mul_zero, add_zero, ih]
  have h0 := Y lam
  rw [hD, zero_mul, mul_zero] at h0
  have peel : ∀ l' : List ℂ, (∀ a ∈ l', ∀ b ∈ lam, a ≠ q * b) → ∀ Z : Matrix (Fin n) (Fin n) ℂ,
      (l'.map fun a => q • D - a • (1 : Matrix (Fin n) (Fin n) ℂ)).prod * Z = 0 → Z = 0 := by
    intro l'
    induction l' with
    | nil =>
      intro _ Z hZ
      simpa using hZ
    | cons a l' ih =>
      intro hl Z hZ
      rw [List.map_cons, List.prod_cons, mul_assoc] at hZ
      apply ih (fun a' ha' => hl a' (List.mem_cons_of_mem _ ha')) Z
      set W := (l'.map fun a => q • D - a • (1 : Matrix (Fin n) (Fin n) ℂ)).prod * Z
      have hqW : q • (D * W) = a • W := by
        rw [sub_mul, sub_eq_zero, smul_mul_assoc, smul_mul_assoc, one_mul] at hZ
        exact hZ
      have hW : D * W = (a / q) • W := by
        calc D * W = q⁻¹ • (q • (D * W)) := by rw [smul_smul, inv_mul_cancel₀ hq, one_smul]
          _ = (a / q) • W := by rw [hqW, smul_smul, div_eq_inv_mul]
      have e := list_prod_sub_smul_mul_eigenvector D W (a / q) hW lam
      rw [hD, zero_mul] at e
      have hne : (lam.map fun b => a / q - b).prod ≠ 0 := by
        intro hp
        rw [List.prod_eq_zero_iff, List.mem_map] at hp
        obtain ⟨b, hb, hb0⟩ := hp
        have hab : a / q = b := sub_eq_zero.1 hb0
        rw [div_eq_iff hq] at hab
        exact hl a (by simp) b hb (by rw [hab, mul_comm])
      exact (smul_eq_zero.1 e.symm).resolve_left hne
  exact peel lam hlam _ h0.symm

/- English proof (translation)
Establish `hq0 : (q : ℂ) ≠ 0` using `by exact_mod_cast (show q ≠ 0 by omega)`. Establish `hpow : ∀ a : ℕ, N ^ a * D = D * N ^ (q * a)`. Introduce `a`. Proceed by induction on `a with`. Consider the case `zero => simp`.

Consider the case `succ a ih`. Rewrite using `[pow_succ, mul_assoc, hND, ← mul_assoc, ih, mul_assoc, ← pow_add, mul_add, mul_one]`. Take `⟨U, hUdef⟩ : ∃ U, U = N ^ (q - 1)` from `⟨_, rfl⟩`. Establish `hUD : U * D = D * U ^ q` using `by rw [hUdef, hpow, ← pow_mul, mul_comm]`. Rewrite `hU` using `[← hUdef]`.

Take `⟨S, hSdef⟩ : ∃ S : Matrix (Fin n) (Fin n) ℂ, S = ∑ s ∈ Finset.range q, U ^ s` from `⟨_, rfl⟩`. Take `⟨H, hHdef⟩ : ∃ H : Matrix (Fin n) (Fin n) ℂ, H = ∑ s ∈ Finset.range q, ∑ r ∈ Finset.range s, U ^ r` from `⟨_, rfl⟩`. Establish `hc : ∀ a : ℕ, Commute (U ^ a) (U - 1)` using `fun a => ((Commute.refl U).pow_left a).sub_right (Commute.one_right _)`. Establish `hSL : Commute S (U - 1)`. Rewrite using `[hSdef]`.

Conclude with `Commute.sum_left _ _ _ (fun s _ => hc s)`. Establish `hHL : Commute H (U - 1)`. Rewrite using `[hHdef]`. Conclude with `Commute.sum_left _ _ _ (fun s _ => Commute.sum_left _ _ _ (fun r _ => hc r))`. Establish `hLD0 : (U - 1) * D = D * ((U - 1) * S)`.

Combine the equalities or inequalities in the displayed calculation. Establish `hS0 : S = (q : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + (U - 1) * H`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hSdef]`. Conclude with `Finset.sum_congr rfl (fun s _ => by rw [geom_sum_mul, sub_add_cancel])`.

Use `_ = H * (U - 1) + (q : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by`. Rewrite using `[Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℂ, hHdef]`. Use `_ = (q : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + (U - 1) * H := by rw [add_comm, hHL.eq]`. Establish `hLD : ∀ X, (U - 1) * (D * X) = D * ((U - 1) * (S * X))` using `fun X => by`. Rewrite using `[← mul_assoc, hLD0, mul_assoc, mul_assoc]`.

Establish `hSX : ∀ X, S * X = (q : ℂ) • X + (U - 1) * (H * X)` using `fun X => by`. Rewrite using `[hS0, add_mul, smul_mul_assoc, one_mul, mul_assoc]`. Establish `hLH : ∀ X, (U - 1) * (H * X) = H * ((U - 1) * X)` using `fun X => by`. Rewrite using `[← mul_assoc, ← mul_assoc, hHL.eq]`. Establish `hLS : ∀ X, (U - 1) * (S * X) = S * ((U - 1) * X)` using `fun X => by`.

Rewrite using `[← mul_assoc, ← mul_assoc, hSL.eq]`. Establish `hlam' : ∀ a ∈ List.ofFn lam, ∀ b ∈ List.ofFn lam, a ≠ (q : ℂ) * b`. Introduce `a ha b hb`. Rewrite `ha`, `hb` using `[List.mem_ofFn]`. Take `⟨j, rfl⟩` from `ha`.

Take `⟨j', rfl⟩` from `hb`. Conclude with `hlam j j'`. Establish `hLall : ∀ m : ℕ, (U - 1) ^ (m + 1) = 0 → U - 1 = 0`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero`. Introduce `h`. Simplify using `using h`. Consider the case `succ m ih`. Introduce `hm`.

Conclude with `ih (nilpotent_index_drop_of_relations D (U - 1) S H (q : ℂ) (List.ofFn lam) hD hq0 hlam' hLD hSX hLH hLS m hm)`. Establish `hL0 : U - 1 = 0` using `hLall n (by rw [pow_succ, hU, zero_mul])`. Establish `hU1 : N ^ (q - 1) = 1`. Rewrite using `[← hUdef]`. Conclude with `sub_eq_zero.1 hL0`.

Establish `hNq : N ^ q = N`. Rewrite using `[show q = (q - 1) + 1 by omega, pow_succ, hU1, one_mul]`. Establish `hcomm : Commute N D` using `by show N * D = D * N`. Rewrite using `[hND, hNq]`. Take `⟨P, hPdef⟩ : ∃ P : Matrix (Fin n) (Fin n) ℂ, P = (List.ofFn fun i' => if i' = i then 1 else D - lam i' • (1 : Matrix (Fin n) (Fin n) ℂ)).prod` from `⟨_, rfl⟩`.

Rewrite using `[← hPdef]`. Take `⟨p, hpdef⟩ : ∃ p : Polynomial ℂ, p = (List.ofFn fun i' => if i' = i then (1 : Polynomial ℂ) else Polynomial.X - Polynomial.C (lam i')).prod` from `⟨_, rfl⟩`. Establish `hPp : P = Polynomial.aeval D p`. Rewrite using `[hPdef, hpdef, map_list_prod, List.map_ofFn]`. Use `congrArg List.prod (congrArg List.ofFn (funext fun i' => ?_))` and prove the remaining obligations.

Simplify using `only [Function.comp_apply]`. Apply the tactic sequence `split_ifs <;> simp [Algebra.algebraMap_eq_smul_one]`. Establish `hprodpoly : (Polynomial.X - Polynomial.C (lam i)) * p = ∏ j, (Polynomial.X - Polynomial.C (lam j))`. Rewrite using `[hpdef, List.prod_ofFn, ← Finset.mul_prod_erase Finset.univ (fun j => Polynomial.X - Polynomial.C (lam j)) (Finset.mem_univ i), ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), if_pos rfl, one_mul]`. Use `congr 1`.

Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `j hj`. Rewrite using `[if_neg (Finset.ne_of_mem_erase hj)]`. Establish `hCH : Polynomial.aeval D (∏ j, (Polynomial.X - Polynomial.C (lam j))) = 0`. Rewrite using `[← List.prod_ofFn, map_list_prod, ← hD, List.map_ofFn, List.map_ofFn]`.

Use `congrArg List.prod (congrArg List.ofFn (funext fun j => ?_))` and prove the remaining obligations. Simplify using `[Algebra.algebraMap_eq_smul_one]`. Establish `hDP : D * P = lam i • P`. Establish `h0 : Polynomial.aeval D ((Polynomial.X - Polynomial.C (lam i)) * p) = 0`. Rewrite using `[hprodpoly, hCH]`.

Rewrite `h0` using `[map_mul, ← hPp]`. Simplify using `only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, sub_mul, smul_mul_assoc, one_mul] at h0`. Conclude with `sub_eq_zero.1 h0`. Establish `hPP : P * P = p.eval (lam i) • P`. Establish `e` using `aeval_mul_eigenvector D P (lam i) hDP p`.

Rewrite `e` using `[← hPp]`. Conclude with `e`. Establish `hpe : ∀ x, p.eval x = ∏ i', (if i' = i then (1 : ℂ) else x - lam i')`. Introduce `x`. Rewrite using `[hpdef, Polynomial.eval_list_prod, List.map_ofFn, List.prod_ofFn]`.

Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `j _`. Simplify using `only [Function.comp_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hκ : p.eval (lam i) ≠ 0`.

Rewrite using `[hpe]`. Use `Finset.prod_ne_zero_iff.2 (fun j _ => ?_)` and prove the remaining obligations. Use `split_ifs with hj`. Conclude with `one_ne_zero`. Conclude with `sub_ne_zero.2 (hdist i j (Ne.symm hj))`.

Establish `hz : ∀ j, j ≠ i → p.eval (lam j) = 0`. Introduce `j hj`. Rewrite using `[hpe]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ j) (by rw [if_neg hj, sub_self])`. Establish `htrp : ∀ (r : Polynomial ℂ) (a : ℕ), (Polynomial.aeval D r * N ^ a).trace = ∑ j, r.eval (lam j) * mu j ^ a`.

Introduce `r a`. Use `Polynomial.induction_on r ?_ ?_ ?_` and prove the remaining obligations. Introduce `c`. Establish `e` using `htr 0 a`. Simplify using `only [pow_zero, one_mul] at e`.

Simplify using `[Algebra.algebraMap_eq_smul_one, Matrix.trace_smul, e, Finset.mul_sum]`. Introduce `r1 r2 h1 h2`. Simplify using `[add_mul, Matrix.trace_add, h1, h2, Finset.sum_add_distrib]`. Introduce `k c _`. Simplify using `[Algebra.algebraMap_eq_smul_one, smul_mul_assoc, Matrix.trace_smul, htr, Finset.mul_sum, mul_assoc]`.

Establish `hPN : ∀ s : ℕ, (P * N ^ s).trace = p.eval (lam i) * mu i ^ s`. Introduce `s`. Rewrite using `[hPp, htrp, Finset.sum_eq_single i (fun j _ hj => by rw [hz j hj, zero_mul]) (fun h => absurd (Finset.mem_univ i) h)]`. Establish `htP : P.trace = p.eval (lam i)`. Establish `e` using `hPN 0`.

Rewrite `e` using `[pow_zero, mul_one, pow_zero, mul_one]`. Conclude with `e`. Establish `hmu0 : mu i ≠ 0`. Introduce `h0`. Establish `e` using `hmu i`.

Rewrite `e` using `[h0, zero_pow (by omega)]`. Conclude with `zero_ne_one e`. Take `⟨V, hVdef⟩ : ∃ V : Matrix (Fin n) (Fin n) ℂ, V = (mu i)⁻¹ • N` from `⟨_, rfl⟩`. Establish `hV1 : V ^ (q - 1) = 1` using `by rw [hVdef, smul_pow, hU1, inv_pow, hmu i, inv_one, one_smul]`. Take `⟨T, hTdef⟩ : ∃ T : Matrix (Fin n) (Fin n) ℂ, T = ∑ s ∈ Finset.range (q - 1), V ^ s` from `⟨_, rfl⟩`.

Establish `hVT : V * T = T`. Establish `e1` using `Finset.sum_range_succ' (fun s => V ^ s) (q - 1)`. Establish `e2` using `Finset.sum_range_succ (fun s => V ^ s) (q - 1)`. Establish `e3` using `e1.symm.trans e2`. Simplify using `only [pow_zero, hV1] at e3`.

Rewrite using `[hTdef, Finset.mul_sum]`. Simplify using `only [← pow_succ']`. Conclude with `add_right_cancel e3`. Establish `hVsT : ∀ s : ℕ, V ^ s * T = T`. Introduce `s`.

Proceed by induction on `s with`. Consider the case `zero => simp`. Consider the case `succ s ih => rw [pow_succ, mul_assoc, hVT, ih]`. Establish `hTT : T * T = ((q - 1 : ℕ) : ℂ) • T`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[show T * T = (∑ s ∈ Finset.range (q - 1), V ^ s) * T by rw [← hTdef], Finset.sum_mul]`. Use `_ = ∑ s ∈ Finset.range (q - 1), T := Finset.sum_congr rfl (fun s _ => hVsT s)`. Use `_ = ((q - 1 : ℕ) : ℂ) • T := by rw [Finset.sum_const, Finset.card_range, Nat.cast_smul_eq_nsmul]`. Establish `hq1 : ((q - 1 : ℕ) : ℂ) ≠ 0` using `by exact_mod_cast (show q - 1 ≠ 0 by omega)`. Take `⟨F, hFdef⟩ : ∃ F : Matrix (Fin n) (Fin n) ℂ, F = ((q - 1 : ℕ) : ℂ)⁻¹ • T` from `⟨_, rfl⟩`.

Establish `hFF : F * F = F`. Rewrite using `[hFdef, smul_mul_assoc, mul_smul_comm, hTT, smul_smul, smul_smul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Establish `hNV : N = mu i • V` using `by rw [hVdef, smul_smul, mul_inv_cancel₀ hmu0, one_smul]`.

Establish `hNF : N * F = mu i • F`. Rewrite using `[hFdef, mul_smul_comm, hNV, smul_mul_assoc, hVT, smul_comm]`. Establish `hNP : Commute N P`. Rewrite using `[hPdef]`. Apply `Commute.list_prod_right` to reduce the goal to its premises.

Introduce `x hx`. Rewrite `hx` using `[List.mem_ofFn]`. Take `⟨j, rfl⟩` from `hx`. Use `split_ifs`. Conclude with `Commute.one_right N`.

Conclude with `hcomm.sub_right ((Commute.one_right N).smul_right _)`. Establish `hVc : Commute V P`. Rewrite using `[hVdef]`. Conclude with `hNP.smul_left _`. Establish `hFP : Commute F P`.

Rewrite using `[hFdef, hTdef]`. Conclude with `(Commute.sum_left _ _ _ (fun s _ => hVc.pow_left s)).smul_left _`. Establish `hVN : Commute V N`. Rewrite using `[hVdef]`. Conclude with `(Commute.refl N).smul_left _`.

Establish `hFN : Commute F N`. Rewrite using `[hFdef, hTdef]`. Conclude with `(Commute.sum_left _ _ _ (fun s _ => hVN.pow_left s)).smul_left _`. Establish `htPF : (P * F).trace = p.eval (lam i)`. Establish `hs : ∀ s : ℕ, (P * V ^ s).trace = p.eval (lam i)`.

Introduce `s`. Establish `hms` using `pow_ne_zero s hmu0`. Rewrite using `[hVdef, smul_pow, mul_smul_comm, Matrix.trace_smul, hPN, smul_eq_mul, inv_pow]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hFdef, mul_smul_comm, Matrix.trace_smul, hTdef, Finset.mul_sum, Matrix.trace_sum, Finset.sum_congr rfl (fun s _ => hs s), Finset.sum_const, Finset.card_range, smul_eq_mul, nsmul_eq_mul]`.

Clear the denominators using the available nonvanishing facts. Establish `h1F : (1 - F) * (1 - F) = 1 - F`. Simplify using `only [sub_mul, mul_sub, one_mul, mul_one, hFF]`. Normalize the expressions using the abelian group laws. Establish `hcomm1F : Commute (1 - F) P` using `(Commute.one_left P).sub_left hFP`.

Establish `hE : P * (1 - F) = 0`. Establish `e : P * (1 - F) * (P * (1 - F)) = p.eval (lam i) • (P * (1 - F))`. Rewrite using `[mul_assoc, ← mul_assoc (1 - F) P, hcomm1F.eq, mul_assoc, h1F, ← mul_assoc, hPP, smul_mul_assoc]`. Establish `hE2 : (p.eval (lam i))⁻¹ • (P * (1 - F)) * ((p.eval (lam i))⁻¹ • (P * (1 - F))) = (p.eval (lam i))⁻¹ • (P * (1 - F))`. Rewrite using `[smul_mul_assoc, mul_smul_comm, smul_smul, e, smul_smul]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Establish `ht : ((p.eval (lam i))⁻¹ • (P * (1 - F))).trace = 0`. Rewrite using `[Matrix.trace_smul, mul_sub, mul_one, Matrix.trace_sub, htP, htPF, sub_self, smul_zero]`. Establish `h0` using `eq_zero_of_idempotent_trace_zero _ hE2 ht`.

Conclude with `(smul_eq_zero.1 h0).resolve_left (inv_ne_zero hκ)`. Establish `hNF0 : (N - mu i • (1 : Matrix (Fin n) (Fin n) ℂ)) * F = 0`. Rewrite using `[sub_mul, hNF, smul_mul_assoc, one_mul, sub_self]`. Establish `hNF' : Commute (N - mu i • (1 : Matrix (Fin n) (Fin n) ℂ)) F` using `hFN.symm.sub_left ((Commute.one_left F).smul_left _)`. Establish `hc2 : Commute (N - mu i • (1 : Matrix (Fin n) (Fin n) ℂ)) (1 - F)` using `(Commute.one_right _).sub_right hNF'`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_add, add_sub_cancel, mul_one]`. Use `_ = P * (1 - F) * (N - mu i • 1) := by`. Rewrite using `[mul_assoc P _ F, hNF0, mul_zero, zero_add, mul_assoc, mul_assoc, hc2.eq]`. Use `_ = 0 := by rw [hE, zero_mul]`.
-/
private theorem prod_sub_lam_mul_sub_mu_eq_zero {n : ℕ} (D N : Matrix (Fin n) (Fin n) ℂ) (lam mu : Fin n → ℂ) (q : ℕ) (hq : 2 ≤ q)
    (hND : N * D = D * N ^ q)
    (hD : ((List.ofFn lam).map fun a => D - a • (1 : Matrix (Fin n) (Fin n) ℂ)).prod = 0)
    (hU : (N ^ (q - 1) - 1) ^ n = 0)
    (htr : ∀ b a : ℕ, (D ^ b * N ^ a).trace = ∑ j, lam j ^ b * mu j ^ a)
    (hmu : ∀ j, mu j ^ (q - 1) = 1)
    (hlam : ∀ j j', lam j ≠ (q : ℂ) * lam j')
    (hdist : ∀ j j', j ≠ j' → lam j ≠ lam j')
    (i : Fin n) :
    (List.ofFn fun i' => if i' = i then 1 else D - lam i' • (1 : Matrix (Fin n) (Fin n) ℂ)).prod *
      (N - mu i • (1 : Matrix (Fin n) (Fin n) ℂ)) = 0 := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hpow : ∀ a : ℕ, N ^ a * D = D * N ^ (q * a) := by
    intro a
    induction a with
    | zero => simp
    | succ a ih =>
      rw [pow_succ, mul_assoc, hND, ← mul_assoc, ih, mul_assoc, ← pow_add, mul_add, mul_one]
  obtain ⟨U, hUdef⟩ : ∃ U, U = N ^ (q - 1) := ⟨_, rfl⟩
  have hUD : U * D = D * U ^ q := by rw [hUdef, hpow, ← pow_mul, mul_comm]
  rw [← hUdef] at hU
  obtain ⟨S, hSdef⟩ : ∃ S : Matrix (Fin n) (Fin n) ℂ, S = ∑ s ∈ Finset.range q, U ^ s := ⟨_, rfl⟩
  obtain ⟨H, hHdef⟩ : ∃ H : Matrix (Fin n) (Fin n) ℂ,
      H = ∑ s ∈ Finset.range q, ∑ r ∈ Finset.range s, U ^ r := ⟨_, rfl⟩
  have hc : ∀ a : ℕ, Commute (U ^ a) (U - 1) := fun a =>
    ((Commute.refl U).pow_left a).sub_right (Commute.one_right _)
  have hSL : Commute S (U - 1) := by
    rw [hSdef]
    exact Commute.sum_left _ _ _ (fun s _ => hc s)
  have hHL : Commute H (U - 1) := by
    rw [hHdef]
    exact Commute.sum_left _ _ _ (fun s _ => Commute.sum_left _ _ _ (fun r _ => hc r))
  have hLD0 : (U - 1) * D = D * ((U - 1) * S) := by
    calc (U - 1) * D = D * U ^ q - D := by rw [sub_mul, one_mul, hUD]
      _ = D * (U ^ q - 1) := by rw [mul_sub, mul_one]
      _ = D * (S * (U - 1)) := by rw [hSdef, geom_sum_mul]
      _ = D * ((U - 1) * S) := by rw [hSL.eq]
  have hS0 : S = (q : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + (U - 1) * H := by
    calc S = ∑ s ∈ Finset.range q, ((∑ r ∈ Finset.range s, U ^ r) * (U - 1) + 1) := by
          rw [hSdef]
          exact Finset.sum_congr rfl (fun s _ => by rw [geom_sum_mul, sub_add_cancel])
      _ = H * (U - 1) + (q : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_range,
            ← Nat.cast_smul_eq_nsmul ℂ, hHdef]
      _ = (q : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + (U - 1) * H := by rw [add_comm, hHL.eq]
  have hLD : ∀ X, (U - 1) * (D * X) = D * ((U - 1) * (S * X)) := fun X => by
    rw [← mul_assoc, hLD0, mul_assoc, mul_assoc]
  have hSX : ∀ X, S * X = (q : ℂ) • X + (U - 1) * (H * X) := fun X => by
    rw [hS0, add_mul, smul_mul_assoc, one_mul, mul_assoc]
  have hLH : ∀ X, (U - 1) * (H * X) = H * ((U - 1) * X) := fun X => by
    rw [← mul_assoc, ← mul_assoc, hHL.eq]
  have hLS : ∀ X, (U - 1) * (S * X) = S * ((U - 1) * X) := fun X => by
    rw [← mul_assoc, ← mul_assoc, hSL.eq]
  have hlam' : ∀ a ∈ List.ofFn lam, ∀ b ∈ List.ofFn lam, a ≠ (q : ℂ) * b := by
    intro a ha b hb
    rw [List.mem_ofFn] at ha hb
    obtain ⟨j, rfl⟩ := ha
    obtain ⟨j', rfl⟩ := hb
    exact hlam j j'
  have hLall : ∀ m : ℕ, (U - 1) ^ (m + 1) = 0 → U - 1 = 0 := by
    intro m
    induction m with
    | zero =>
      intro h
      simpa using h
    | succ m ih =>
      intro hm
      exact ih (nilpotent_index_drop_of_relations D (U - 1) S H (q : ℂ) (List.ofFn lam) hD hq0 hlam' hLD hSX hLH hLS m hm)
  have hL0 : U - 1 = 0 := hLall n (by rw [pow_succ, hU, zero_mul])
  have hU1 : N ^ (q - 1) = 1 := by
    rw [← hUdef]
    exact sub_eq_zero.1 hL0
  have hNq : N ^ q = N := by
    rw [show q = (q - 1) + 1 by omega, pow_succ, hU1, one_mul]
  have hcomm : Commute N D := by
    show N * D = D * N
    rw [hND, hNq]
  obtain ⟨P, hPdef⟩ : ∃ P : Matrix (Fin n) (Fin n) ℂ, P = (List.ofFn fun i' =>
      if i' = i then 1 else D - lam i' • (1 : Matrix (Fin n) (Fin n) ℂ)).prod := ⟨_, rfl⟩
  rw [← hPdef]
  obtain ⟨p, hpdef⟩ : ∃ p : Polynomial ℂ, p = (List.ofFn fun i' =>
      if i' = i then (1 : Polynomial ℂ) else Polynomial.X - Polynomial.C (lam i')).prod := ⟨_, rfl⟩
  have hPp : P = Polynomial.aeval D p := by
    rw [hPdef, hpdef, map_list_prod, List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun i' => ?_))
    simp only [Function.comp_apply]
    split_ifs <;> simp [Algebra.algebraMap_eq_smul_one]
  have hprodpoly : (Polynomial.X - Polynomial.C (lam i)) * p =
      ∏ j, (Polynomial.X - Polynomial.C (lam j)) := by
    rw [hpdef, List.prod_ofFn,
      ← Finset.mul_prod_erase Finset.univ (fun j => Polynomial.X - Polynomial.C (lam j)) (Finset.mem_univ i),
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), if_pos rfl, one_mul]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [if_neg (Finset.ne_of_mem_erase hj)]
  have hCH : Polynomial.aeval D (∏ j, (Polynomial.X - Polynomial.C (lam j))) = 0 := by
    rw [← List.prod_ofFn, map_list_prod, ← hD, List.map_ofFn, List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun j => ?_))
    simp [Algebra.algebraMap_eq_smul_one]
  have hDP : D * P = lam i • P := by
    have h0 : Polynomial.aeval D ((Polynomial.X - Polynomial.C (lam i)) * p) = 0 := by
      rw [hprodpoly, hCH]
    rw [map_mul, ← hPp] at h0
    simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one,
      sub_mul, smul_mul_assoc, one_mul] at h0
    exact sub_eq_zero.1 h0
  have hPP : P * P = p.eval (lam i) • P := by
    have e := aeval_mul_eigenvector D P (lam i) hDP p
    rw [← hPp] at e
    exact e
  have hpe : ∀ x, p.eval x = ∏ i', (if i' = i then (1 : ℂ) else x - lam i') := by
    intro x
    rw [hpdef, Polynomial.eval_list_prod, List.map_ofFn, List.prod_ofFn]
    apply Finset.prod_congr rfl
    intro j _
    simp only [Function.comp_apply]
    split_ifs <;> simp
  have hκ : p.eval (lam i) ≠ 0 := by
    rw [hpe]
    refine Finset.prod_ne_zero_iff.2 (fun j _ => ?_)
    split_ifs with hj
    · exact one_ne_zero
    · exact sub_ne_zero.2 (hdist i j (Ne.symm hj))
  have hz : ∀ j, j ≠ i → p.eval (lam j) = 0 := by
    intro j hj
    rw [hpe]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [if_neg hj, sub_self])
  have htrp : ∀ (r : Polynomial ℂ) (a : ℕ),
      (Polynomial.aeval D r * N ^ a).trace = ∑ j, r.eval (lam j) * mu j ^ a := by
    intro r a
    refine Polynomial.induction_on r ?_ ?_ ?_
    · intro c
      have e := htr 0 a
      simp only [pow_zero, one_mul] at e
      simp [Algebra.algebraMap_eq_smul_one, Matrix.trace_smul, e, Finset.mul_sum]
    · intro r1 r2 h1 h2
      simp [add_mul, Matrix.trace_add, h1, h2, Finset.sum_add_distrib]
    · intro k c _
      simp [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, Matrix.trace_smul, htr, Finset.mul_sum,
        mul_assoc]
  have hPN : ∀ s : ℕ, (P * N ^ s).trace = p.eval (lam i) * mu i ^ s := by
    intro s
    rw [hPp, htrp, Finset.sum_eq_single i (fun j _ hj => by rw [hz j hj, zero_mul])
      (fun h => absurd (Finset.mem_univ i) h)]
  have htP : P.trace = p.eval (lam i) := by
    have e := hPN 0
    rw [pow_zero, mul_one, pow_zero, mul_one] at e
    exact e
  have hmu0 : mu i ≠ 0 := by
    intro h0
    have e := hmu i
    rw [h0, zero_pow (by omega)] at e
    exact zero_ne_one e
  obtain ⟨V, hVdef⟩ : ∃ V : Matrix (Fin n) (Fin n) ℂ, V = (mu i)⁻¹ • N := ⟨_, rfl⟩
  have hV1 : V ^ (q - 1) = 1 := by rw [hVdef, smul_pow, hU1, inv_pow, hmu i, inv_one, one_smul]
  obtain ⟨T, hTdef⟩ : ∃ T : Matrix (Fin n) (Fin n) ℂ, T = ∑ s ∈ Finset.range (q - 1), V ^ s :=
    ⟨_, rfl⟩
  have hVT : V * T = T := by
    have e1 := Finset.sum_range_succ' (fun s => V ^ s) (q - 1)
    have e2 := Finset.sum_range_succ (fun s => V ^ s) (q - 1)
    have e3 := e1.symm.trans e2
    simp only [pow_zero, hV1] at e3
    rw [hTdef, Finset.mul_sum]
    simp only [← pow_succ']
    exact add_right_cancel e3
  have hVsT : ∀ s : ℕ, V ^ s * T = T := by
    intro s
    induction s with
    | zero => simp
    | succ s ih => rw [pow_succ, mul_assoc, hVT, ih]
  have hTT : T * T = ((q - 1 : ℕ) : ℂ) • T := by
    calc T * T = ∑ s ∈ Finset.range (q - 1), V ^ s * T := by
          rw [show T * T = (∑ s ∈ Finset.range (q - 1), V ^ s) * T by rw [← hTdef], Finset.sum_mul]
      _ = ∑ s ∈ Finset.range (q - 1), T := Finset.sum_congr rfl (fun s _ => hVsT s)
      _ = ((q - 1 : ℕ) : ℂ) • T := by rw [Finset.sum_const, Finset.card_range, Nat.cast_smul_eq_nsmul]
  have hq1 : ((q - 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show q - 1 ≠ 0 by omega)
  obtain ⟨F, hFdef⟩ : ∃ F : Matrix (Fin n) (Fin n) ℂ, F = ((q - 1 : ℕ) : ℂ)⁻¹ • T := ⟨_, rfl⟩
  have hFF : F * F = F := by
    rw [hFdef, smul_mul_assoc, mul_smul_comm, hTT, smul_smul, smul_smul]
    congr 1
    field_simp
  have hNV : N = mu i • V := by rw [hVdef, smul_smul, mul_inv_cancel₀ hmu0, one_smul]
  have hNF : N * F = mu i • F := by
    rw [hFdef, mul_smul_comm, hNV, smul_mul_assoc, hVT, smul_comm]
  have hNP : Commute N P := by
    rw [hPdef]
    apply Commute.list_prod_right
    intro x hx
    rw [List.mem_ofFn] at hx
    obtain ⟨j, rfl⟩ := hx
    split_ifs
    · exact Commute.one_right N
    · exact hcomm.sub_right ((Commute.one_right N).smul_right _)
  have hVc : Commute V P := by
    rw [hVdef]
    exact hNP.smul_left _
  have hFP : Commute F P := by
    rw [hFdef, hTdef]
    exact (Commute.sum_left _ _ _ (fun s _ => hVc.pow_left s)).smul_left _
  have hVN : Commute V N := by
    rw [hVdef]
    exact (Commute.refl N).smul_left _
  have hFN : Commute F N := by
    rw [hFdef, hTdef]
    exact (Commute.sum_left _ _ _ (fun s _ => hVN.pow_left s)).smul_left _
  have htPF : (P * F).trace = p.eval (lam i) := by
    have hs : ∀ s : ℕ, (P * V ^ s).trace = p.eval (lam i) := by
      intro s
      have hms := pow_ne_zero s hmu0
      rw [hVdef, smul_pow, mul_smul_comm, Matrix.trace_smul, hPN, smul_eq_mul, inv_pow]
      field_simp
    rw [hFdef, mul_smul_comm, Matrix.trace_smul, hTdef, Finset.mul_sum, Matrix.trace_sum,
      Finset.sum_congr rfl (fun s _ => hs s), Finset.sum_const, Finset.card_range, smul_eq_mul,
      nsmul_eq_mul]
    field_simp
  have h1F : (1 - F) * (1 - F) = 1 - F := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hFF]
    abel
  have hcomm1F : Commute (1 - F) P := (Commute.one_left P).sub_left hFP
  have hE : P * (1 - F) = 0 := by
    have e : P * (1 - F) * (P * (1 - F)) = p.eval (lam i) • (P * (1 - F)) := by
      rw [mul_assoc, ← mul_assoc (1 - F) P, hcomm1F.eq, mul_assoc, h1F, ← mul_assoc, hPP,
        smul_mul_assoc]
    have hE2 : (p.eval (lam i))⁻¹ • (P * (1 - F)) * ((p.eval (lam i))⁻¹ • (P * (1 - F))) =
        (p.eval (lam i))⁻¹ • (P * (1 - F)) := by
      rw [smul_mul_assoc, mul_smul_comm, smul_smul, e, smul_smul]
      congr 1
      field_simp
    have ht : ((p.eval (lam i))⁻¹ • (P * (1 - F))).trace = 0 := by
      rw [Matrix.trace_smul, mul_sub, mul_one, Matrix.trace_sub, htP, htPF, sub_self, smul_zero]
    have h0 := eq_zero_of_idempotent_trace_zero _ hE2 ht
    exact (smul_eq_zero.1 h0).resolve_left (inv_ne_zero hκ)
  have hNF0 : (N - mu i • (1 : Matrix (Fin n) (Fin n) ℂ)) * F = 0 := by
    rw [sub_mul, hNF, smul_mul_assoc, one_mul, sub_self]
  have hNF' : Commute (N - mu i • (1 : Matrix (Fin n) (Fin n) ℂ)) F :=
    hFN.symm.sub_left ((Commute.one_left F).smul_left _)
  have hc2 : Commute (N - mu i • (1 : Matrix (Fin n) (Fin n) ℂ)) (1 - F) :=
    (Commute.one_right _).sub_right hNF'
  calc P * (N - mu i • (1 : Matrix (Fin n) (Fin n) ℂ))
      = P * (N - mu i • 1) * F + P * (N - mu i • 1) * (1 - F) := by
        rw [← mul_add, add_sub_cancel, mul_one]
    _ = P * (1 - F) * (N - mu i • 1) := by
        rw [mul_assoc P _ F, hNF0, mul_zero, zero_add, mul_assoc, mul_assoc, hc2.eq]
    _ = 0 := by rw [hE, zero_mul]

open Polynomial in
/- English proof (translation)
Establish `hcne : ∀ j g, c j g ≠ 0`. Introduce `j g h0`. Establish `e : c j g * c j g⁻¹ = 1` using `by rw [← map_mul, mul_inv_cancel, map_one]`. Rewrite `e` using `[h0, zero_mul]`. Conclude with `zero_ne_one e`.

Establish `hrel : R t * R f = R f * R t ^ q`. Establish `e1` using `h1`. Simplify using `only [map_mul, map_inv, map_pow] at e1`. Rewrite `e1` using `[inv_mul_eq_one]`. Rewrite using `[e1]`.

Use `group`. Establish `hND : (R t : Matrix (Fin n) (Fin n) ℂ) * (R f : Matrix (Fin n) (Fin n) ℂ) = (R f : Matrix (Fin n) (Fin n) ℂ) * (R t : Matrix (Fin n) (Fin n) ℂ) ^ q`. Establish `e` using `congrArg Units.val hrel`. Simplify `e` using `only [Units.val_mul, Units.val_pow_eq_pow_val]`. Establish `hD` using `wdb_ofReal_eq_conj_wd_ofReal _ _ (h f)`.

Establish `hmu : ∀ j, c j t ^ (q - 1) = 1`. Introduce `j`. Establish `e` using `h2 j`. Simplify using `only [map_mul, map_inv, map_pow] at e`. Establish `hf` using `hcne j f`.

Establish `ht` using `hcne j t`. Rewrite `e` using `[show (c j f)⁻¹ * c j t * c j f = c j t by field_simp]`. Establish `e' : c j t ^ q = c j t` using `(inv_mul_eq_one₀ (pow_ne_zero q ht)).1 e`. Rewrite `e'` using `[show q = (q - 1) + 1 by omega, pow_succ]`. Conclude with `mul_right_cancel₀ ht (e'.trans (one_mul _).symm)`.

Establish `hU : ((R t : Matrix (Fin n) (Fin n) ℂ) ^ (q - 1) - 1) ^ n = 0`. Establish `e` using `wdb_ofReal_eq_conj_wd_ofReal _ _ (h (t ^ (q - 1)))`. Establish `hv : ∀ j, c j (t ^ (q - 1)) = 1` using `fun j => by rw [map_pow, hmu j]`. Simplify `e` using `[hv, map_pow, Units.val_pow_eq_pow_val, List.map_replicate, List.prod_replicate]`. Establish `htr : ∀ b a : ℕ, ((R f : Matrix (Fin n) (Fin n) ℂ) ^ b * (R t : Matrix (Fin n) (Fin n) ℂ) ^ a).trace = ∑ j, c j f ^ b * c j t ^ a`.

Introduce `b a`. Establish `e` using `trace_of_charpoly _ _ (h (f ^ b * t ^ a))`. Simplify `e` using `[map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val]`. Establish `hlam : ∀ j j', c j f ≠ (q : ℂ) * c j' f`. Introduce `j j'`.

Distinguish the cases in `hjj : j = j'`. Substitute `hjj` using the available equality. Introduce `e`. Establish `hf` using `hcne j f`. Establish `e2 : ((q : ℂ) - 1) * c j f = 0` using `by linear_combination -e`.

Break down `mul_eq_zero.1 e2 with h0 | h0` into its components or cases. Establish `e3 : (q : ℂ) = 1` using `by linear_combination h0`. Normalize the coercions in `at e3`. Use linear arithmetic over natural numbers and integers. Conclude with `hf h0`.

Conclude with `(h3 j j' hjj).2`. Establish `hdist : ∀ j j', j ≠ j' → c j f ≠ c j' f` using `fun j j' hjj => (h3 j j' hjj).1`. Conclude with `prod_sub_lam_mul_sub_mu_eq_zero (R f : Matrix (Fin n) (Fin n) ℂ) (R t : Matrix (Fin n) (Fin n) ℂ) (fun j => c j f) (fun j => c j t) q hq hND hD hU htr hmu hlam hdist i`.
-/
private theorem rel_of_chars {W : Type} [Group W] {n q : ℕ} (hq : 2 ≤ q) (R : W →* GL (Fin n) ℂ) (c : Fin n → W →* ℂ)
    (h : ∀ g, (R g : Matrix (Fin n) (Fin n) ℂ).charpoly = ∏ i, (X - C (c i g))) (f t : W)
    (h1 : R ((t ^ q)⁻¹ * (f⁻¹ * t * f)) = 1) (h2 : ∀ i, c i ((t ^ q)⁻¹ * (f⁻¹ * t * f)) = 1)
    (h3 : ∀ i i', i ≠ i' → c i f ≠ c i' f ∧ c i f ≠ (q : ℂ) * c i' f) (i : Fin n) :
    (List.ofFn fun i' => if i' = i then 1 else (R f : Matrix (Fin n) (Fin n) ℂ) - c i' f • (1 : Matrix (Fin n) (Fin n) ℂ)).prod *
      ((R t : Matrix (Fin n) (Fin n) ℂ) - c i t • (1 : Matrix (Fin n) (Fin n) ℂ)) = 0 := by
  have hcne : ∀ j g, c j g ≠ 0 := by
    intro j g h0
    have e : c j g * c j g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [h0, zero_mul] at e
    exact zero_ne_one e
  have hrel : R t * R f = R f * R t ^ q := by
    have e1 := h1
    simp only [map_mul, map_inv, map_pow] at e1
    rw [inv_mul_eq_one] at e1
    rw [e1]
    group
  have hND : (R t : Matrix (Fin n) (Fin n) ℂ) * (R f : Matrix (Fin n) (Fin n) ℂ) =
      (R f : Matrix (Fin n) (Fin n) ℂ) * (R t : Matrix (Fin n) (Fin n) ℂ) ^ q := by
    have e := congrArg Units.val hrel
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using e
  have hD := wdb_ofReal_eq_conj_wd_ofReal _ _ (h f)
  have hmu : ∀ j, c j t ^ (q - 1) = 1 := by
    intro j
    have e := h2 j
    simp only [map_mul, map_inv, map_pow] at e
    have hf := hcne j f
    have ht := hcne j t
    rw [show (c j f)⁻¹ * c j t * c j f = c j t by field_simp] at e
    have e' : c j t ^ q = c j t := (inv_mul_eq_one₀ (pow_ne_zero q ht)).1 e
    rw [show q = (q - 1) + 1 by omega, pow_succ] at e'
    exact mul_right_cancel₀ ht (e'.trans (one_mul _).symm)
  have hU : ((R t : Matrix (Fin n) (Fin n) ℂ) ^ (q - 1) - 1) ^ n = 0 := by
    have e := wdb_ofReal_eq_conj_wd_ofReal _ _ (h (t ^ (q - 1)))
    have hv : ∀ j, c j (t ^ (q - 1)) = 1 := fun j => by rw [map_pow, hmu j]
    simpa [hv, map_pow, Units.val_pow_eq_pow_val, List.map_replicate, List.prod_replicate] using e
  have htr : ∀ b a : ℕ, ((R f : Matrix (Fin n) (Fin n) ℂ) ^ b * (R t : Matrix (Fin n) (Fin n) ℂ) ^ a).trace =
      ∑ j, c j f ^ b * c j t ^ a := by
    intro b a
    have e := trace_of_charpoly _ _ (h (f ^ b * t ^ a))
    simpa [map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val] using e
  have hlam : ∀ j j', c j f ≠ (q : ℂ) * c j' f := by
    intro j j'
    by_cases hjj : j = j'
    · subst hjj
      intro e
      have hf := hcne j f
      have e2 : ((q : ℂ) - 1) * c j f = 0 := by linear_combination -e
      rcases mul_eq_zero.1 e2 with h0 | h0
      · have e3 : (q : ℂ) = 1 := by linear_combination h0
        norm_cast at e3
        omega
      · exact hf h0
    · exact (h3 j j' hjj).2
  have hdist : ∀ j j', j ≠ j' → c j f ≠ c j' f := fun j j' hjj => (h3 j j' hjj).1
  exact prod_sub_lam_mul_sub_mu_eq_zero (R f : Matrix (Fin n) (Fin n) ℂ) (R t : Matrix (Fin n) (Fin n) ℂ)
    (fun j => c j f) (fun j => c j t) q hq hND hD hU htr hmu hlam hdist i

/- English proof (translation)
Establish `hd : (deltaHalf k fun _ : Fin n => Unit) ((leviTorus k (Fin n)) (Pi.mulSingle i u)) = 1`. Rewrite using `[deltaHalf_apply]`. Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `a _`. Establish `hdet : Matrix.GeneralLinearGroup.det ((leviTorus k (Fin n)) (Pi.mulSingle i u) a) = (Pi.mulSingle i u : Fin n → kˣ) a`.

Establish `hs` using `congrFun ((leviTorus k (Fin n)).symm_apply_apply (Pi.mulSingle i u)) a`. Conclude with `hs`. Rewrite using `[hdet]`. Distinguish the cases in `ha : a = i`. Substitute `ha` using the available equality.

Rewrite using `[Pi.mulSingle_eq_same]`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[val_absPow, GlobalTheory.LGrp.nabs_eq_zpow, hu]`. Simplify using the standard rewrite rules. Rewrite using `[Pi.mulSingle_eq_of_ne ha, map_one]`.

Establish `ht : torusChar ψ (Pi.mulSingle i u) = 1`. Rewrite using `[torusChar_apply]`. Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `j _`. Distinguish the cases in `hj : j = i`.

Substitute `hj` using the available equality. Rewrite using `[Pi.mulSingle_eq_same, h1]`. Rewrite using `[Pi.mulSingle_eq_of_ne hj, map_one]`. Establish `e` using `congrArg (fun φ : (Fin n → kˣ) →* ℂˣ => φ (Pi.mulSingle i u)) hχ`. Rewrite `e` using `[MonoidHom.mul_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ht, hd, mul_one]`.

Conclude with `e.symm`.
-/
private theorem chi_unit {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (ψ : Fin n → kˣ →* ℂˣ) (χ : (Fin n → kˣ) →* ℂˣ)
    (hχ : torusChar ψ = χ * ((deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom))
    (i : Fin n) (u : kˣ) (hu : ord k u = 0) (h1 : ψ i u = 1) : χ (Pi.mulSingle i u) = 1 := by
  have hd : (deltaHalf k fun _ : Fin n => Unit) ((leviTorus k (Fin n)) (Pi.mulSingle i u)) = 1 := by
    rw [deltaHalf_apply]
    apply Finset.prod_eq_one
    intro a _
    have hdet : Matrix.GeneralLinearGroup.det ((leviTorus k (Fin n)) (Pi.mulSingle i u) a) =
        (Pi.mulSingle i u : Fin n → kˣ) a := by
      have hs := congrFun ((leviTorus k (Fin n)).symm_apply_apply (Pi.mulSingle i u)) a
      exact hs
    rw [hdet]
    by_cases ha : a = i
    · subst ha
      rw [Pi.mulSingle_eq_same]
      apply Units.ext
      rw [val_absPow, GlobalTheory.LGrp.nabs_eq_zpow, hu]
      simp
    · rw [Pi.mulSingle_eq_of_ne ha, map_one]
  have ht : torusChar ψ (Pi.mulSingle i u) = 1 := by
    rw [torusChar_apply]
    apply Finset.prod_eq_one
    intro j _
    by_cases hj : j = i
    · subst hj
      rw [Pi.mulSingle_eq_same, h1]
    · rw [Pi.mulSingle_eq_of_ne hj, map_one]
  have e := congrArg (fun φ : (Fin n → kˣ) →* ℂˣ => φ (Pi.mulSingle i u)) hχ
  rw [MonoidHom.mul_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ht, hd, mul_one] at e
  exact e.symm
