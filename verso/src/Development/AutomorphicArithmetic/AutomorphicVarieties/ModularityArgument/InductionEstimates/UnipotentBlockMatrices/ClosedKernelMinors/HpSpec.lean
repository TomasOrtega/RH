import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.UnipBlocks
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SubDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.AdMeas
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PkLaws

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.UnipotentUpperLower

section Ring

variable {R : Type} [CommRing R]

private def Low (M : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) : Prop :=
  ∀ i j : Fin 2, M (Fin.natAdd 2 i) (Fin.castAdd 2 j) = 0

private def ul (M : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) : Matrix (Fin 2) (Fin 2) R :=
  M.submatrix (Fin.castAdd 2) (Fin.castAdd 2)

/- English proof (translation)
Introduce `i j`. Rewrite using `[Matrix.mul_apply, Fin.sum_univ_add]`. Simplify using `only [hM _ _, hN _ _, zero_mul, mul_zero, Finset.sum_const_zero, add_zero]`.
-/
private theorem low_mul {M N : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R} (hM : Low M) (hN : Low N) : Low (M * N) := by
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_add]
  simp only [hM _ _, hN _ _, zero_mul, mul_zero, Finset.sum_const_zero, add_zero]

/- English proof (translation)
Introduce `i j`. Use `Matrix.one_apply_ne fun h => ?_` and prove the remaining obligations. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `only [Fin.val_natAdd, Fin.val_castAdd] at this`. Use linear arithmetic over natural numbers and integers.
-/
private theorem low_one : Low (1 : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) := by
  intro i j
  refine Matrix.one_apply_ne fun h => ?_
  have := congrArg Fin.val h
  simp only [Fin.val_natAdd, Fin.val_castAdd] at this
  omega

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [ul, Matrix.submatrix_apply]`. Rewrite using `[Matrix.mul_apply, Fin.sum_univ_add, Matrix.mul_apply]`. Simplify using `only [hN _ _, mul_zero, Finset.sum_const_zero, add_zero, Matrix.submatrix_apply]`.
-/
private theorem ul_mul (M : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) {N : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R} (hN : Low N) :
    ul (M * N) = ul M * ul N := by
  ext i j
  simp only [ul, Matrix.submatrix_apply]
  rw [Matrix.mul_apply, Fin.sum_univ_add, Matrix.mul_apply]
  simp only [hN _ _, mul_zero, Finset.sum_const_zero, add_zero, Matrix.submatrix_apply]

/- English proof (translation)
The claim follows from `Matrix.submatrix_one _ (Fin.castAdd_injective 2 2)`.
-/
private theorem ul_one : ul (1 : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) = 1 :=
  Matrix.submatrix_one _ (Fin.castAdd_injective 2 2)

variable (R) in
private def PS : Subgroup (GL (Fin (2 + 2)) R) where
  carrier := {g | Low g.val ∧ Low (g⁻¹).val}
  mul_mem' := fun {a b} ha hb => ⟨by rw [Units.val_mul]; exact low_mul ha.1 hb.1,
    by rw [mul_inv_rev, Units.val_mul]; exact low_mul hb.2 ha.2⟩
  one_mem' := ⟨low_one, by rw [inv_one]; exact low_one⟩
  inv_mem' := fun {a} ha => ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

private def top : PS R →* GL (Fin 2) R where
  toFun g := ⟨ul g.1.val, ul (g.1⁻¹).val,
    by rw [← ul_mul _ g.2.2, ← Units.val_mul, mul_inv_cancel, Units.val_one, ul_one],
    by rw [← ul_mul _ g.2.1, ← Units.val_mul, inv_mul_cancel, Units.val_one, ul_one]⟩
  map_one' := Units.ext ul_one
  map_mul' a b := Units.ext (ul_mul _ b.2.1)

/- English proof (translation)
Introduce `i j`. Rewrite using `[unipMatrix, Matrix.add_apply, low_one i j, blockEntry_apply, dif_neg, add_zero]`. Simplify using `only [Fin.val_natAdd, Fin.val_castAdd]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem low_unip (X : UPos (2 + 2) 2 → R) : Low (unipMatrix X) := by
  intro i j
  rw [unipMatrix, Matrix.add_apply, low_one i j, blockEntry_apply, dif_neg, add_zero]
  simp only [Fin.val_natAdd, Fin.val_castAdd]
  omega

/- English proof (translation)
Assemble the required witnesses or components as `⟨low_unip X, low_unip (-X)⟩`.
-/
private theorem unip_mem (X : UPos (2 + 2) 2 → R) : unipGL X ∈ PS R := ⟨low_unip X, low_unip (-X)⟩

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[Units.val_one, ← ul_one]`. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `unipMatrix X (Fin.castAdd 2 i) (Fin.castAdd 2 j) = (1 : Matrix _ _ R) (Fin.castAdd 2 i) (Fin.castAdd 2 j)`. Rewrite using `[unipMatrix, Matrix.add_apply, blockEntry_apply, dif_neg, add_zero]`.

Simplify using `only [Fin.val_castAdd]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem top_unip (X : UPos (2 + 2) 2 → R) : top ⟨unipGL X, unip_mem X⟩ = 1 := by
  refine Units.ext ?_
  rw [Units.val_one, ← ul_one]
  ext i j
  change unipMatrix X (Fin.castAdd 2 i) (Fin.castAdd 2 j) = (1 : Matrix _ _ R) (Fin.castAdd 2 i) (Fin.castAdd 2 j)
  rw [unipMatrix, Matrix.add_apply, blockEntry_apply, dif_neg, add_zero]
  simp only [Fin.val_castAdd]
  omega

/- English proof (translation)
Introduce `i j`. Simplify using `only [Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]`.
-/
private theorem low_blocks (a b : Matrix (Fin 2) (Fin 2) R) :
    Low (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks a 0 0 b)) := by
  intro i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd,
    finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]

/- English proof (translation)
Assemble the required witnesses or components as `⟨low_blocks _ _, low_blocks _ _⟩`.
-/
private theorem blk_mem (a b : GL (Fin 2) R) : blk a b ∈ PS R := ⟨low_blocks _ _, low_blocks _ _⟩

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks a.val 0 0 b.val) (Fin.castAdd 2 i) (Fin.castAdd 2 j) = _`. Simplify using `only [Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₁₁]`.
-/
private theorem top_blk (a b : GL (Fin 2) R) : top ⟨blk a b, blk_mem a b⟩ = a := by
  refine Units.ext ?_
  ext i j
  change Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks a.val 0 0 b.val)
    (Fin.castAdd 2 i) (Fin.castAdd 2 j) = _
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₁₁]

end Ring

variable {K : Type} [Field K] [NumberField K]

private noncomputable def hh (s : PS 𝔸[K]) : ℝ := Real.log (detModule K 2 (top s)).1

/- English proof (translation)
Unfold `hh`. Rewrite using `[map_mul, map_mul, Positive.val_mul, Real.log_mul (detModule K 2 _).2.ne' (detModule K 2 _).2.ne']`.
-/
private theorem hh_mul (s s' : PS 𝔸[K]) : hh (s * s') = hh s + hh s' := by
  unfold hh
  rw [map_mul, map_mul, Positive.val_mul, Real.log_mul (detModule K 2 _).2.ne' (detModule K 2 _).2.ne']

/- English proof (translation)
Use `hh_mul (1 : PS 𝔸[K]) 1` as an intermediate fact. Rewrite `this` using `[mul_one]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem hh_one : hh (1 : PS 𝔸[K]) = 0 := by
  have := hh_mul (1 : PS 𝔸[K]) 1
  rw [mul_one] at this
  linarith

/- English proof (translation)
The claim follows from `Real.log_nonpos (detModule K 2 _).2.le ((subDet (2 + 2) s.1 hs _ _ (Fin.castAdd_injective 2 2) (Fin.castAdd_injective 2 2)).2.2 (top s) rfl)`.
-/
private theorem hh_le (s : PS 𝔸[K]) (hs : s.1 ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K (2 + 2)))) : hh s ≤ 0 :=
  Real.log_nonpos (detModule K 2 _).2.le
    ((subDet (2 + 2) s.1 hs _ _ (Fin.castAdd_injective 2 2) (Fin.castAdd_injective 2 2)).2.2 (top s) rfl)

/- English proof (translation)
Establish `e : (s'⁻¹ * s).1 = k' * k⁻¹`. Rewrite using `[Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]`. Establish `h1` using `hh_le (s'⁻¹ * s) (e ▸ mul_mem hk' (inv_mem hk))`. Establish `h2` using `hh_mul s' (s'⁻¹ * s)`. Rewrite `h2` using `[mul_inv_cancel_left]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem hh_uniq (s s' : PS 𝔸[K]) {k k' : AdelicGLn.AdelicGL K (2 + 2)}
    (hk : k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K (2 + 2))))
    (hk' : k' ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K (2 + 2))))
    (h : s.1 * k = s'.1 * k') : hh s ≤ hh s' := by
  have e : (s'⁻¹ * s).1 = k' * k⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
  have h1 := hh_le (s'⁻¹ * s) (e ▸ mul_mem hk' (inv_mem hk))
  have h2 := hh_mul s' (s'⁻¹ * s)
  rw [mul_inv_cancel_left] at h2
  linarith

private noncomputable def ub (X : UPos (2 + 2) 2 → 𝔸[K]) (a b : AdelicGLn.AdelicGL K 2) : PS 𝔸[K] :=
  ⟨unipGL X, unip_mem X⟩ * ⟨blk a b, blk_mem a b⟩

/- English proof (translation)
Unfold `hh ub`. Rewrite using `[map_mul, top_unip, top_blk, one_mul]`.
-/
private theorem hh_ub (X : UPos (2 + 2) 2 → 𝔸[K]) (a b : AdelicGLn.AdelicGL K 2) :
    hh (ub X a b) = Real.log (detModule K 2 a).1 := by
  unfold hh ub
  rw [map_mul, top_unip, top_blk, one_mul]

/- English proof (translation)
Use `⟨ub X (m₁ * zt K t) (m₂ * zt K (-t)), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.coe_mul, blkLaws.1]`. Both sides reduce to the same expression. Rewrite using `[hh_ub, map_mul, mem_normOneGL_iff_detModule.1 m₁.2, one_mul, zt, detModule_centralSection two_pos]`. Conclude with `Real.log_exp t`.
-/
private theorem coord (X : UPos (2 + 2) 2 → 𝔸[K]) (m₁ m₂ : G1 K 2) (t : ℝ) :
    ∃ s : PS 𝔸[K], ((nn X * lv m₁ m₂ t : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) = s.1 ∧ hh s = t := by
  refine ⟨ub X (m₁ * zt K t) (m₂ * zt K (-t)), ?_, ?_⟩
  · rw [Subgroup.coe_mul, blkLaws.1]
    rfl
  · rw [hh_ub, map_mul, mem_normOneGL_iff_detModule.1 m₁.2, one_mul, zt, detModule_centralSection two_pos]
    exact Real.log_exp t

/- English proof (translation)
Establish `key : ∀ (X : UPos (2 + 2) 2 → 𝔸[K]) (a b : AdelicGLn.AdelicGL K 2) (k' : AdelicGLn.AdelicGL K (2 + 2)), k' ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K (2 + 2))) → (g : AdelicGLn.AdelicGL K (2 + 2)) = unipGL X * blk a b * k' → Real.log (detModule K 2 a).1 = hh s`. Introduce `X a b k' hk' e`. Rewrite using `[← hh_ub X a b]`. Establish `e' : (ub X a b).1 * k' = s.1 * k` using `e.symm.trans h`. Conclude with `le_antisymm (hh_uniq _ _ hk' hk e') (hh_uniq _ _ hk hk' e'.symm)`.

Unfold `HH HP`. Rewrite using `[← csInf_singleton (hh s)]`. Use `congr 1`. Use `Set.eq_singleton_iff_unique_mem.2 ⟨?_, ?_⟩` and prove the remaining obligations. Take `⟨X, m₁, m₂, t, k', hk', e⟩` from `iwa g`.

Establish `e' : (g : AdelicGLn.AdelicGL K (2 + 2)) = unipGL X * blk (m₁.1 * zt K t) (m₂.1 * zt K (-t)) * k'.1`. Rewrite using `[e, Subgroup.coe_mul, Subgroup.coe_mul, blkLaws.1]`. Both sides reduce to the same expression. Conclude with `⟨X, _, _, k'.1, hk', e', (key _ _ _ _ hk' e').symm⟩`. Introduce and unpack `_ ⟨X, a, b, k', hk', e, rfl⟩`.

Conclude with `key X a b k' hk' e`.
-/
private theorem hp_eq (g : G1 K (2 + 2)) (s : PS 𝔸[K]) {k : AdelicGLn.AdelicGL K (2 + 2)}
    (hk : k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K (2 + 2))))
    (h : (g : AdelicGLn.AdelicGL K (2 + 2)) = s.1 * k) : HH g = hh s := by
  have key : ∀ (X : UPos (2 + 2) 2 → 𝔸[K]) (a b : AdelicGLn.AdelicGL K 2) (k' : AdelicGLn.AdelicGL K (2 + 2)),
      k' ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K (2 + 2))) →
      (g : AdelicGLn.AdelicGL K (2 + 2)) = unipGL X * blk a b * k' → Real.log (detModule K 2 a).1 = hh s := by
    intro X a b k' hk' e
    rw [← hh_ub X a b]
    have e' : (ub X a b).1 * k' = s.1 * k := e.symm.trans h
    exact le_antisymm (hh_uniq _ _ hk' hk e') (hh_uniq _ _ hk hk' e'.symm)
  unfold HH HP
  rw [← csInf_singleton (hh s)]
  congr 1
  refine Set.eq_singleton_iff_unique_mem.2 ⟨?_, ?_⟩
  · obtain ⟨X, m₁, m₂, t, k', hk', e⟩ := iwa g
    have e' : (g : AdelicGLn.AdelicGL K (2 + 2)) = unipGL X * blk (m₁.1 * zt K t) (m₂.1 * zt K (-t)) * k'.1 := by
      rw [e, Subgroup.coe_mul, Subgroup.coe_mul, blkLaws.1]
      rfl
    exact ⟨X, _, _, k'.1, hk', e', (key _ _ _ _ hk' e').symm⟩
  · rintro _ ⟨X, a, b, k', hk', e, rfl⟩
    exact key X a b k' hk' e

/- English proof (translation)
Take `⟨X, m₁, m₂, t, k, hk, e⟩` from `iwa g`. Take `⟨s, hs, -⟩` from `coord X m₁ m₂ t`. Conclude with `⟨_, k, hk, hs ▸ s.2, e⟩`.
-/
private theorem dec (g : G1 K (2 + 2)) : ∃ s : G1 K (2 + 2), ∃ k ∈ KG K (2 + 2),
    (s : AdelicGLn.AdelicGL K (2 + 2)) ∈ PS 𝔸[K] ∧ g = s * k := by
  obtain ⟨X, m₁, m₂, t, k, hk, e⟩ := iwa g
  obtain ⟨s, hs, -⟩ := coord X m₁ m₂ t
  exact ⟨_, k, hk, hs ▸ s.2, e⟩

/- English proof (translation)
Take `⟨s', k, hk, hs', rfl⟩` from `dec g`. Rewrite using `[hp_eq (s' * k) ⟨_, hs'⟩ hk rfl, ← hh_mul]`. Use `hp_eq _ _ hk ?_` and prove the remaining obligations. Simplify using `only [Subgroup.coe_mul, h, mul_assoc, Subgroup.coe_subtype]`.
-/
private theorem hp_mul (p : G1 K (2 + 2)) (s : PS 𝔸[K]) (h : (p : AdelicGLn.AdelicGL K (2 + 2)) = s.1)
    (g : G1 K (2 + 2)) : HH (p * g) = hh s + HH g := by
  obtain ⟨s', k, hk, hs', rfl⟩ := dec g
  rw [hp_eq (s' * k) ⟨_, hs'⟩ hk rfl, ← hh_mul]
  refine hp_eq _ _ hk ?_
  simp only [Subgroup.coe_mul, h, mul_assoc, Subgroup.coe_subtype]

/- English proof (translation)
Set `S : Subgroup (G1 K (2 + 2))` to `(PS 𝔸[K]).comap (normOneGL K (2 + 2)).subtype`. Establish `c1 : Continuous fun g : G1 K (2 + 2) => (g : AdelicGLn.AdelicGL K (2 + 2)).val` using `Units.continuous_val.comp continuous_subtype_val`. Establish `c2 : Continuous fun g : G1 K (2 + 2) => ((g : AdelicGLn.AdelicGL K (2 + 2))⁻¹).val` using `Units.continuous_coe_inv.comp continuous_subtype_val`. Establish `hS : IsClosed (S : Set (G1 K (2 + 2)))`. Express the relevant statement in the definitionally equal form `IsClosed ({g : G1 K (2 + 2) | ∀ i j : Fin 2, (g : AdelicGLn.AdelicGL K (2 + 2)).val (Fin.natAdd 2 i) (Fin.castAdd 2 j) = 0} ∩ {g : G1 K (2 + 2) | ∀ i j : Fin 2, ((g : AdelicGLn.AdelicGL K (2 + 2))⁻¹).val (Fin.natAdd 2 i) (Fin.castAdd 2 j) = 0})`.

Simplify using `only [Set.setOf_forall]`. Conclude with `(isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (c1.matrix_elem _ _) continuous_const).inter (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (c2.matrix_elem _ _) continuous_const)`. Establish `hsurj : Function.Surjective (HaarSK.mulMap S (KG K (2 + 2)))` using `fun g => by`. Take `⟨s, k, hk, hs, e⟩` from `dec g`. Conclude with `⟨(⟨s, hs⟩, ⟨k, hk⟩), e.symm⟩`.

Establish `hq` using `HaarSK.isQuotientMap_mulMap hS (blkLaws.2.2.2.2.2.2.2.2.2.2.2 (2 + 2)).1 hsurj`. Rewrite using `[hq.continuous_iff]`. Establish `e : HH (K` using `K) ∘ HaarSK.mulMap S (KG K (2 + 2)) = fun p => hh ⟨p.1.1.1, p.1.2⟩ :=`. Use function extensionality and compare the values at `fun p => hp_eq _ ⟨p.1.1.1, p.1.2⟩ p.2.2 rfl`. Rewrite using `[e]`.

Establish `c3 : Continuous fun p : S × KG K (2 + 2) => (top ⟨p.1.1.1, p.1.2⟩ : AdelicGLn.AdelicGL K 2)` using `Units.continuous_iff.2 ⟨(c1.comp (continuous_subtype_val.comp continuous_fst)).matrix_submatrix _ _, (c2.comp (continuous_subtype_val.comp continuous_fst)).matrix_submatrix _ _⟩`. Conclude with `(continuous_subtype_val.comp (continuous_detModule.comp c3)).log fun p => (detModule K 2 _).2.ne'`.
-/
private theorem cont_hp : Continuous (HH (K := K)) := by
  let S : Subgroup (G1 K (2 + 2)) := (PS 𝔸[K]).comap (normOneGL K (2 + 2)).subtype
  have c1 : Continuous fun g : G1 K (2 + 2) => (g : AdelicGLn.AdelicGL K (2 + 2)).val :=
    Units.continuous_val.comp continuous_subtype_val
  have c2 : Continuous fun g : G1 K (2 + 2) => ((g : AdelicGLn.AdelicGL K (2 + 2))⁻¹).val :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  have hS : IsClosed (S : Set (G1 K (2 + 2))) := by
    change IsClosed ({g : G1 K (2 + 2) | ∀ i j : Fin 2,
      (g : AdelicGLn.AdelicGL K (2 + 2)).val (Fin.natAdd 2 i) (Fin.castAdd 2 j) = 0} ∩ {g : G1 K (2 + 2) | ∀ i j : Fin 2,
      ((g : AdelicGLn.AdelicGL K (2 + 2))⁻¹).val (Fin.natAdd 2 i) (Fin.castAdd 2 j) = 0})
    simp only [Set.setOf_forall]
    exact (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (c1.matrix_elem _ _) continuous_const).inter
      (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (c2.matrix_elem _ _) continuous_const)
  have hsurj : Function.Surjective (HaarSK.mulMap S (KG K (2 + 2))) := fun g => by
    obtain ⟨s, k, hk, hs, e⟩ := dec g
    exact ⟨(⟨s, hs⟩, ⟨k, hk⟩), e.symm⟩
  have hq := HaarSK.isQuotientMap_mulMap hS (blkLaws.2.2.2.2.2.2.2.2.2.2.2 (2 + 2)).1 hsurj
  rw [hq.continuous_iff]
  have e : HH (K := K) ∘ HaarSK.mulMap S (KG K (2 + 2)) = fun p => hh ⟨p.1.1.1, p.1.2⟩ :=
    funext fun p => hp_eq _ ⟨p.1.1.1, p.1.2⟩ p.2.2 rfl
  rw [e]
  have c3 : Continuous fun p : S × KG K (2 + 2) => (top ⟨p.1.1.1, p.1.2⟩ : AdelicGLn.AdelicGL K 2) :=
    Units.continuous_iff.2 ⟨(c1.comp (continuous_subtype_val.comp continuous_fst)).matrix_submatrix _ _,
      (c2.comp (continuous_subtype_val.comp continuous_fst)).matrix_submatrix _ _⟩
  exact (continuous_subtype_val.comp (continuous_detModule.comp c3)).log fun p => (detModule K 2 _).2.ne'

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.UnipotentUpperLower

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.UnipotentUpperLower in
/- English proof (translation)
Introduce `K _ _`. Establish `h1 : ∀ (X : UPos (2 + 2) 2 → 𝔸[K]) (m₁ m₂ : G1 K 2) (t : ℝ) (g : G1 K (2 + 2)), HH (nn X * lv m₁ m₂ t * g) = t + HH g` using `fun X m₁ m₂ t g => by`. Take `⟨s, hs, ht⟩` from `coord X m₁ m₂ t`. Rewrite using `[hp_mul _ s hs, ht]`. Establish `h2 : ∀ k ∈ KG K (2 + 2), HH k = 0` using `fun k hk => (hp_eq k 1 hk (one_mul _).symm).trans hh_one`.

Use `⟨h1, fun k hk => ⟨h2 k hk, fun g => ?_⟩, fun γ hγ g => ?_, cont_hp, fun C hC => ?_⟩` and prove the remaining obligations. Take `⟨X, m₁, m₂, t, k', hk', rfl⟩` from `iwa g`. Rewrite using `[mul_assoc _ k' k, h1, h1, h2 _ hk', h2 _ (mul_mem hk' hk)]`. Take `⟨ξ, γ₁, γ₂, rfl⟩` from `(pkLaws.2.1 γ).1 hγ`. Rewrite using `[h1, zero_add]`.

Establish `hc` using `(((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 (2 + 2)).1.mul hC).image (cont_hp (K := K)).abs`. Take `⟨R, hR⟩` from `hc.bddAbove`. Use `⟨R, fun g x hx => ?_⟩` and prove the remaining obligations. Take `⟨X, m₁, m₂, t, k, hk, rfl⟩` from `iwa g`. Rewrite using `[mul_assoc _ k x, h1, h1, h2 _ hk, add_zero, add_sub_cancel_left]`.

Conclude with `hR ⟨k * x, Set.mul_mem_mul hk hx, rfl⟩`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.hpSpec :
    ∀ {K : Type} [Field K] [NumberField K], (∀ (X : UPos (2 + 2) 2 → 𝔸[K]) (m₁ m₂ : G1 K 2) (t : ℝ) (g : G1 K (2 + 2)), HH (nn X * lv m₁ m₂ t * g) = t + HH g) ∧
      (∀ k ∈ KG K (2 + 2), HH k = 0 ∧ ∀ g : G1 K (2 + 2), HH (g * k) = HH g) ∧ (∀ γ ∈ PK K, ∀ g, HH (γ * g) = HH g) ∧ Continuous (HH (K := K)) ∧
      ∀ C : Set (G1 K (2 + 2)), IsCompact C → ∃ R : ℝ, ∀ g, ∀ x ∈ C, |HH (g * x) - HH g| ≤ R := by
  intro K _ _
  have h1 : ∀ (X : UPos (2 + 2) 2 → 𝔸[K]) (m₁ m₂ : G1 K 2) (t : ℝ) (g : G1 K (2 + 2)),
      HH (nn X * lv m₁ m₂ t * g) = t + HH g := fun X m₁ m₂ t g => by
    obtain ⟨s, hs, ht⟩ := coord X m₁ m₂ t
    rw [hp_mul _ s hs, ht]
  have h2 : ∀ k ∈ KG K (2 + 2), HH k = 0 := fun k hk =>
    (hp_eq k 1 hk (one_mul _).symm).trans hh_one
  refine ⟨h1, fun k hk => ⟨h2 k hk, fun g => ?_⟩, fun γ hγ g => ?_, cont_hp, fun C hC => ?_⟩
  · obtain ⟨X, m₁, m₂, t, k', hk', rfl⟩ := iwa g
    rw [mul_assoc _ k' k, h1, h1, h2 _ hk', h2 _ (mul_mem hk' hk)]
  · obtain ⟨ξ, γ₁, γ₂, rfl⟩ := (pkLaws.2.1 γ).1 hγ
    rw [h1, zero_add]
  · have hc := (((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 (2 + 2)).1.mul hC).image (cont_hp (K := K)).abs
    obtain ⟨R, hR⟩ := hc.bddAbove
    refine ⟨R, fun g x hx => ?_⟩
    obtain ⟨X, m₁, m₂, t, k, hk, rfl⟩ := iwa g
    rw [mul_assoc _ k x, h1, h1, h2 _ hk, add_zero, add_sub_cancel_left]
    exact hR ⟨k * x, Set.mul_mem_mul hk hx, rfl⟩
