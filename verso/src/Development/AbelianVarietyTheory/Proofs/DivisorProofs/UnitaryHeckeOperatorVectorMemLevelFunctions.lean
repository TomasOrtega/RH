import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.BCT.TrKer.HopStab

/- English proof (translation)
Unfold `toSub`. Distinguish the cases in `hy : y ∈ H`. Establish `h2 : y * (k : G) ∈ H` using `H.mul_mem hy k.2`. Rewrite using `[dif_pos h2, dif_pos hy]`. Conclude with `hu k hk ⟨y, hy⟩`.

Establish `h2 : y * (k : G) ∉ H` using `fun h => hy (by simpa using H.mul_mem h (H.inv_mem k.2))`. Rewrite using `[dif_neg h2, dif_neg hy]`.
-/
theorem toSub_mul_right {G : Type} [Group G] (H : Subgroup G) (K : Subgroup H) (u : H → ℂ)
    (hu : ∀ k ∈ K, ∀ x, u (x * k) = u x) (y : G) (k : H) (hk : k ∈ K) :
    u (toSub H (y * k)) = u (toSub H y) := by
  unfold toSub
  by_cases hy : y ∈ H
  · have h2 : y * (k : G) ∈ H := H.mul_mem hy k.2
    rw [dif_pos h2, dif_pos hy]
    exact hu k hk ⟨y, hy⟩
  · have h2 : y * (k : G) ∉ H := fun h => hy (by simpa using H.mul_mem h (H.inv_mem k.2))
    rw [dif_neg h2, dif_neg hy]

/- English proof (translation)
Unfold `toSub`. Distinguish the cases in `hy : y ∈ H`. Establish `h2 : (k : G) * y ∈ H` using `H.mul_mem k.2 hy`. Rewrite using `[dif_pos h2, dif_pos hy]`. Conclude with `hu k hk ⟨y, hy⟩`.

Establish `h2 : (k : G) * y ∉ H` using `fun h => hy (by simpa using H.mul_mem (H.inv_mem k.2) h)`. Rewrite using `[dif_neg h2, dif_neg hy]`.
-/
theorem toSub_mul_left {G : Type} [Group G] (H : Subgroup G) (K : Subgroup H) (u : H → ℂ)
    (hu : ∀ k ∈ K, ∀ x, u (k * x) = u x) (y : G) (k : H) (hk : k ∈ K) :
    u (toSub H (k * y)) = u (toSub H y) := by
  unfold toSub
  by_cases hy : y ∈ H
  · have h2 : (k : G) * y ∈ H := H.mul_mem k.2 hy
    rw [dif_pos h2, dif_pos hy]
    exact hu k hk ⟨y, hy⟩
  · have h2 : (k : G) * y ∉ H := fun h => hy (by simpa using H.mul_mem (H.inv_mem k.2) h)
    rw [dif_neg h2, dif_neg hy]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Unfold `globLev at hk`. Use `(Subgroup.mem_iInf.1 hk w)` as an intermediate fact. Use `Subgroup.mem_iInf.1 this hw` as an intermediate fact. Simplify using `using this`.
-/
theorem mem_loc {S : Set (Pl E)} {K' : ∀ w : Pl E, Subgroup (UL n w)} {k : finU E n} (hk : k ∈ globLev S K')
    {w : Pl E} (hw : w ∈ S) : ∃ k' : UL n w, k' ∈ K' w ∧ (k' : GLw n w) = cLoc w k.1 := by
  unfold globLev at hk
  have := (Subgroup.mem_iInf.1 hk w)
  have := Subgroup.mem_iInf.1 this hw
  simpa using this

/- English proof (translation)
Unfold `globFn`. Use `finprod_mem_congr rfl fun w hw => ?_` and prove the remaining obligations. Take `⟨k', hk', he⟩` from `mem_loc hk hw`. Rewrite using `[Subgroup.coe_mul, map_mul, ← he]`. Conclude with `toSub_mul_right _ (K' w) (f w) (fun k hk x => ((hf w).2 k hk x).2) _ k' hk'`.
-/
theorem globFn_mul_right {S : Set (Pl E)} {K' : ∀ w : Pl E, Subgroup (UL n w)} {f : ∀ w : Pl E, UL n w → ℂ}
    (hf : ∀ w, IsHecke (K' w) (f w)) {k : finU E n} (hk : k ∈ globLev S K') (x : finU E n) :
    globFn S f (x * k) = globFn S f x := by
  unfold globFn
  refine finprod_mem_congr rfl fun w hw => ?_
  obtain ⟨k', hk', he⟩ := mem_loc hk hw
  rw [Subgroup.coe_mul, map_mul, ← he]
  exact toSub_mul_right _ (K' w) (f w) (fun k hk x => ((hf w).2 k hk x).2) _ k' hk'

/- English proof (translation)
Unfold `globFn`. Use `finprod_mem_congr rfl fun w hw => ?_` and prove the remaining obligations. Take `⟨k', hk', he⟩` from `mem_loc hk hw`. Rewrite using `[Subgroup.coe_mul, map_mul, ← he]`. Conclude with `toSub_mul_left _ (K' w) (f w) (fun k hk x => ((hf w).2 k hk x).1) _ k' hk'`.
-/
theorem globFn_mul_left {S : Set (Pl E)} {K' : ∀ w : Pl E, Subgroup (UL n w)} {f : ∀ w : Pl E, UL n w → ℂ}
    (hf : ∀ w, IsHecke (K' w) (f w)) {k : finU E n} (hk : k ∈ globLev S K') (x : finU E n) :
    globFn S f (k * x) = globFn S f x := by
  unfold globFn
  refine finprod_mem_congr rfl fun w hw => ?_
  obtain ⟨k', hk', he⟩ := mem_loc hk hw
  rw [Subgroup.coe_mul, map_mul, ← he]
  exact toSub_mul_left _ (K' w) (f w) (fun k hk x => ((hf w).2 k hk x).1) _ k' hk'

end GlobalTheory.BCT.TrKer.HopStab

namespace GlobalTheory.BCT.TrKer.HopStab
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Establish `hsub : (Function.support fun q : finU E n ⧸ globLev S K' => globFn S f q.out • F (x * q.out)) ⊆ (hfin.toFinset : Set _)`. Introduce `q hq`. Simplify using `only [Set.Finite.coe_toFinset, Function.mem_support] at hq ⊢`. Introduce `h0`. Apply `hq` to reduce the goal to its premises.

Use `congrArg (fun L : (finU E n → Module.Dual ℂ (Wsp lam)) →ₗ[ℂ] (finU E n → Module.Dual ℂ (Wsp lam)) => L F x) h0` as an intermediate fact. Simplify `this` using `[rightReg, LinearMap.funLeft]`. Unfold `hopM levOp`. Rewrite using `[finsum_eq_sum _ hfin, finsum_eq_sum_of_support_subset _ hsub]`. Simplify using `[rightReg, LinearMap.funLeft, Finset.sum_apply, LinearMap.sum_apply]`.
-/
theorem hopM_apply {S : Set (Pl E)} {lam : InfinitePlace E → DomWeight n} {K' : ∀ w : Pl E, Subgroup (UL n w)}
    (f : ∀ w : Pl E, UL n w → ℂ) (F : finU E n → Module.Dual ℂ (Wsp lam))
    (hfin : (Function.support fun q : finU E n ⧸ globLev S K' =>
      globFn S f q.out • (rightReg ℂ (finU E n) (Module.Dual ℂ (Wsp lam)) q.out ∘ₗ LinearMap.id)).Finite)
    (x : finU E n) :
    hopM S lam K' f F x = (((globLev S K').relIndex (globLev S (KL n)) : ℕ) : ℂ)⁻¹ •
      ∑ᶠ q : finU E n ⧸ globLev S K', globFn S f q.out • F (x * q.out) := by
  have hsub : (Function.support fun q : finU E n ⧸ globLev S K' => globFn S f q.out • F (x * q.out)) ⊆
      (hfin.toFinset : Set _) := by
    intro q hq
    simp only [Set.Finite.coe_toFinset, Function.mem_support] at hq ⊢
    intro h0
    apply hq
    have := congrArg (fun L : (finU E n → Module.Dual ℂ (Wsp lam)) →ₗ[ℂ] (finU E n → Module.Dual ℂ (Wsp lam)) => L F x) h0
    simpa [rightReg, LinearMap.funLeft] using this
  unfold hopM levOp
  rw [finsum_eq_sum _ hfin, finsum_eq_sum_of_support_subset _ hsub]
  simp [rightReg, LinearMap.funLeft, Finset.sum_apply, LinearMap.sum_apply]

end GlobalTheory.BCT.TrKer.HopStab

namespace GlobalTheory.BCT.TrKer.HopStab

/- English proof (translation)
Introduce `E _ _ _ n S lam K' _ f hf F hF`. Distinguish the cases in `hfin : (Function.support fun q : finU E n ⧸ globLev S K' => globFn S f q.out • (rightReg ℂ (finU E n) (Module.Dual ℂ (Wsp lam)) q.out ∘ₗ LinearMap.id)).Finite`. Use `swap`. Establish `h0 : hopM S lam K' f = 0`. Unfold `hopM levOp`.

Rewrite using `[finsum_of_infinite_support hfin, smul_zero]`. Rewrite using `[h0]`. Conclude with `(vecM S lam K').zero_mem`. Establish `hsupp : ∀ y : finU E n, (Function.support fun q : finU E n ⧸ globLev S K' => globFn S f q.out • F (y * q.out)).Finite`. Introduce `y`.

Use `hfin.subset fun q hq => ?_` and prove the remaining obligations. Simplify using `only [Function.mem_support] at hq ⊢`. Introduce `h0`. Apply `hq` to reduce the goal to its premises. Use `congrArg (fun L : (finU E n → Module.Dual ℂ (Wsp lam)) →ₗ[ℂ] (finU E n → Module.Dual ℂ (Wsp lam)) => L F y) h0` as an intermediate fact.

Simplify `this` using `[rightReg, LinearMap.funLeft]`. Use `⟨fun γ x => ?_, fun k hk x => ?_⟩` and prove the remaining obligations. Rewrite using `[hopM_apply f F hfin, hopM_apply f F hfin, map_smul, map_finsum _ (hsupp x)]`. Use `congr 1`. Use `finsum_congr fun q => ?_` and prove the remaining obligations.

Rewrite using `[mul_assoc, hF.1 γ, map_smul]`. Rewrite using `[hopM_apply f F hfin, hopM_apply f F hfin]`. Use `congr 1`. Use `symm`. Rewrite using `[← finsum_comp_equiv (MulAction.toPerm k : Equiv.Perm (finU E n ⧸ globLev S K'))]`.

Use `finsum_congr fun q => ?_` and prove the remaining obligations. Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul (globLev S K') (k * q.out)`. Establish `hq : (MulAction.toPerm k : Equiv.Perm (finU E n ⧸ globLev S K')) q = ((k * q.out : finU E n) : finU E n ⧸ globLev S K')` using `by conv_lhs => rw [← QuotientGroup.out_eq' q]`. Both sides reduce to the same expression. Rewrite using `[hq, hh, globFn_mul_right hf.1 h.2, globFn_mul_left hf.1 hk, ← mul_assoc, ← mul_assoc, hF.2 h h.2]`.
-/
theorem hopM_mem_vecM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E))
    (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ,
    IsTest (KL n) K' f → ∀ F ∈ vecM S lam K', hopM S lam K' f F ∈ vecM S lam K' := by
  intro E _ _ _ n S lam K' _ f hf F hF
  by_cases hfin : (Function.support fun q : finU E n ⧸ globLev S K' =>
      globFn S f q.out • (rightReg ℂ (finU E n) (Module.Dual ℂ (Wsp lam)) q.out ∘ₗ LinearMap.id)).Finite
  swap
  · have h0 : hopM S lam K' f = 0 := by
      unfold hopM levOp
      rw [finsum_of_infinite_support hfin, smul_zero]
    rw [h0]
    exact (vecM S lam K').zero_mem
  have hsupp : ∀ y : finU E n, (Function.support fun q : finU E n ⧸ globLev S K' =>
      globFn S f q.out • F (y * q.out)).Finite := by
    intro y
    refine hfin.subset fun q hq => ?_
    simp only [Function.mem_support] at hq ⊢
    intro h0
    apply hq
    have := congrArg (fun L : (finU E n → Module.Dual ℂ (Wsp lam)) →ₗ[ℂ] (finU E n → Module.Dual ℂ (Wsp lam)) => L F y) h0
    simpa [rightReg, LinearMap.funLeft] using this
  refine ⟨fun γ x => ?_, fun k hk x => ?_⟩
  · rw [hopM_apply f F hfin, hopM_apply f F hfin, map_smul, map_finsum _ (hsupp x)]
    congr 1
    refine finsum_congr fun q => ?_
    rw [mul_assoc, hF.1 γ, map_smul]
  · rw [hopM_apply f F hfin, hopM_apply f F hfin]
    congr 1
    symm
    rw [← finsum_comp_equiv (MulAction.toPerm k : Equiv.Perm (finU E n ⧸ globLev S K'))]
    refine finsum_congr fun q => ?_
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (globLev S K') (k * q.out)
    have hq : (MulAction.toPerm k : Equiv.Perm (finU E n ⧸ globLev S K')) q =
        ((k * q.out : finU E n) : finU E n ⧸ globLev S K') := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [hq, hh, globFn_mul_right hf.1 h.2, globFn_mul_left hf.1 hk, ← mul_assoc, ← mul_assoc, hF.2 h h.2]

end GlobalTheory.BCT.TrKer.HopStab
