import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorRationalTranslateMemThetaFunctions
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPrincipalCongruenceLevelSubgroupIffIntegralCo
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.StdDatum.DetCong

variable {D : D7}

/- English proof (translation)
Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨c, hc, s, hs, rfl⟩` from `hx`. Use `AddSubgroup.subset_closure ⟨b * c, Ideal.mul_mem_mul hb hc, s, hs, ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← map_mul]`.

Both sides reduce to the same expression. Consider the case `zero => rw [mul_zero]`. Conclude with `zero_mem _`. Consider the case `add _ _ _ _ h1 h2 => rw [mul_add]`. Conclude with `add_mem h1 h2`.

Consider the case `neg _ _ h => rw [mul_neg]`. Conclude with `neg_mem h`.
-/
theorem inc_mul_mem_hatId {I J : Ideal (𝓞 D.host.E)} {b : 𝓞 D.host.E} (hb : b ∈ I) {y : AE D}
    (hy : y ∈ hatId D J) : inc D (b : D.host.E) * y ∈ hatId D (I * J) := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, s, hs, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨b * c, Ideal.mul_mem_mul hb hc, s, hs, ?_⟩
    rw [← mul_assoc, ← map_mul]; rfl
  | zero => rw [mul_zero]; exact zero_mem _
  | add _ _ _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg _ _ h => rw [mul_neg]; exact neg_mem h

/- English proof (translation)
Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨c, hc, s, hs, rfl⟩` from `hx`. Use `AddSubgroup.subset_closure ⟨D.host.conj • c, Ideal.smul_mem_pointwise_smul _ _ _ hc, sgA D s, VacMove.sgA_mem D hs, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, GlobalTheory.NormSum.PtsMem.sgA_inc]`.

Both sides reduce to the same expression. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add _ _ _ _ h1 h2 => rw [map_add]`. Conclude with `add_mem h1 h2`.

Consider the case `neg _ _ h => rw [map_neg]`. Conclude with `neg_mem h`.
-/
theorem sgA_mem_hatId {𝔪 : Ideal (𝓞 D.host.E)} {y : AE D} (hy : y ∈ hatId D 𝔪) :
    sgA D y ∈ hatId D (D.host.conj • 𝔪) := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, s, hs, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨D.host.conj • c, Ideal.smul_mem_pointwise_smul _ _ _ hc, sgA D s,
      VacMove.sgA_mem D hs, ?_⟩
    rw [map_mul, GlobalTheory.NormSum.PtsMem.sgA_inc]; rfl
  | zero => rw [map_zero]; exact zero_mem _
  | add _ _ _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
  | neg _ _ h => rw [map_neg]; exact neg_mem h

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp only [Finset.prod_empty, sub_self]`. Conclude with `zero_mem _`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.prod_insert ha]`.

Establish `e : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i = f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) + (f a - g a) * ∏ i ∈ s, g i` using `by ring`. Rewrite using `[e]`. Use `add_mem (mul_mem_hatId (hf a (Finset.mem_insert_self a s)) (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) (fun i hi => hg i (Finset.mem_insert_of_mem hi)) (fun i hi => h i (Finset.mem_insert_of_mem hi)))) (mem_hatId_mul (prod_mem fun i hi => hg i (Finset.mem_insert_of_mem h …` and prove the remaining obligations.
-/
theorem prod_sub_prod_mem {𝔪 : Ideal (𝓞 D.host.E)} {ι : Type*} (s : Finset ι) (f g : ι → AE D)
    (hf : ∀ i ∈ s, f i ∈ OhE D) (hg : ∀ i ∈ s, g i ∈ OhE D) (h : ∀ i ∈ s, f i - g i ∈ hatId D 𝔪) :
    (∏ i ∈ s, f i) - ∏ i ∈ s, g i ∈ hatId D 𝔪 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, sub_self]; exact zero_mem _
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have e : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i =
        f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) + (f a - g a) * ∏ i ∈ s, g i := by ring
    rw [e]
    refine add_mem (mul_mem_hatId (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) (fun i hi => hg i (Finset.mem_insert_of_mem hi))
        (fun i hi => h i (Finset.mem_insert_of_mem hi))))
      (mem_hatId_mul (prod_mem fun i hi => hg i (Finset.mem_insert_of_mem hi)) (h a (Finset.mem_insert_self a s)))

/- English proof (translation)
Establish `h1 : ∀ i j, (1 : Matrix (Fin a) (Fin a) (AE D)) i j ∈ OhE D` using `fun i j => by`. Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`.

Rewrite using `[← Matrix.det_one (R := AE D) (n := Fin a), Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib]`. Use `sum_mem fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[← smul_sub]`. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h]`. Rewrite using `[one_smul]`.

Conclude with `prod_sub_prod_mem _ _ _ (fun i _ => hM _ _) (fun i _ => h1 _ _) (fun i _ => hC _ _)`. Rewrite using `[Units.neg_smul, one_smul]`. Conclude with `neg_mem (prod_sub_prod_mem _ _ _ (fun i _ => hM _ _) (fun i _ => h1 _ _) (fun i _ => hC _ _))`.
-/
theorem det_sub_one_mem_hatId_of {𝔪 : Ideal (𝓞 D.host.E)} {a : ℕ} (M : Matrix (Fin a) (Fin a) (AE D))
    (hM : ∀ i j, M i j ∈ OhE D) (hC : ∀ i j, (M - 1) i j ∈ hatId D 𝔪) : M.det - 1 ∈ hatId D 𝔪 := by
  have h1 : ∀ i j, (1 : Matrix (Fin a) (Fin a) (AE D)) i j ∈ OhE D := fun i j => by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  rw [← Matrix.det_one (R := AE D) (n := Fin a), Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib]
  refine sum_mem fun σ _ => ?_
  rw [← smul_sub]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h]
  · rw [one_smul]
    exact prod_sub_prod_mem _ _ _ (fun i _ => hM _ _) (fun i _ => h1 _ _) (fun i _ => hC _ _)
  · rw [Units.neg_smul, one_smul]
    exact neg_mem (prod_sub_prod_mem _ _ _ (fun i _ => hM _ _) (fun i _ => h1 _ _) (fun i _ => hC _ _))

/- English proof (translation)
Introduce `D a 𝔪 hco k hk hc`. Use `set u : AE D := ((Matrix.GeneralLinearGroup.det (k : GL (Fin a) (AE D)) : (AE D)ˣ) : AE D) with hu`. Establish `hint` using `(mem_intG k).1 hk`. Establish `huO : u ∈ OhE D` using `VacMove.det_int D _ hint`. Establish `h1 : u - 1 ∈ hatId D 𝔪`.

Rewrite using `[hu, Matrix.GeneralLinearGroup.val_det_apply]`. Conclude with `det_sub_one_mem_hatId_of _ (fun i j => (hint i j).1) hc`. Establish `hn : u * sgA D u = 1` using `VacMove.det_norm D k`. Establish `h2 : u - 1 ∈ hatId D (D.host.conj • 𝔪)`. Establish `e : u - 1 = -(u * sgA D (u - 1))`.

Rewrite using `[map_sub, map_one, mul_sub, hn]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `neg_mem (mul_mem_hatId huO (sgA_mem_hatId h1))`. Establish `hsup : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤`.

Rewrite using `[← Ideal.add_eq_sup, Ideal.isCoprime_iff_add.1 hco, Ideal.one_eq_top]`. Establish `h1m : (1 : 𝓞 D.host.E) ∈ 𝔪 ⊔ D.host.conj • 𝔪` using `by rw [hsup]; exact Submodule.mem_top`. Take `⟨s, hs, t, ht, hst⟩` from `Submodule.mem_sup.1 h1m`. Establish `e : u - 1 = inc D (s : D.host.E) * (u - 1) + inc D (t : D.host.E) * (u - 1)`. Rewrite using `[← add_mul, ← map_add, show (s : D.host.E) + t = ((s + t : 𝓞 D.host.E) : D.host.E) from rfl, hst]`.

Simplify using the standard rewrite rules. Rewrite using `[e]`. Use `add_mem (inc_mul_mem_hatId hs h2) ?_` and prove the remaining obligations. Rewrite using `[mul_comm 𝔪]`. Conclude with `inc_mul_mem_hatId ht h1`.
-/
theorem det_sub_one_mem : ∀ (D : D7) {a : ℕ} (𝔪 : Ideal (𝓞 D.host.E)), IsCoprime 𝔪 (D.host.conj • 𝔪) →
    ∀ k : GA D a, k ∈ intG D a → CongOne D 𝔪 k →
      ((Matrix.GeneralLinearGroup.det (k : GL (Fin a) (AE D)) : (AE D)ˣ) : AE D) - 1 ∈
        hatId D (𝔪 * D.host.conj • 𝔪) := by
  intro D a 𝔪 hco k hk hc
  set u : AE D := ((Matrix.GeneralLinearGroup.det (k : GL (Fin a) (AE D)) : (AE D)ˣ) : AE D) with hu
  have hint := (mem_intG k).1 hk
  have huO : u ∈ OhE D := VacMove.det_int D _ hint
  have h1 : u - 1 ∈ hatId D 𝔪 := by
    rw [hu, Matrix.GeneralLinearGroup.val_det_apply]
    exact det_sub_one_mem_hatId_of _ (fun i j => (hint i j).1) hc
  have hn : u * sgA D u = 1 := VacMove.det_norm D k
  have h2 : u - 1 ∈ hatId D (D.host.conj • 𝔪) := by
    have e : u - 1 = -(u * sgA D (u - 1)) := by
      rw [map_sub, map_one, mul_sub, hn]; ring
    rw [e]
    exact neg_mem (mul_mem_hatId huO (sgA_mem_hatId h1))
  have hsup : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ := by
    rw [← Ideal.add_eq_sup, Ideal.isCoprime_iff_add.1 hco, Ideal.one_eq_top]
  have h1m : (1 : 𝓞 D.host.E) ∈ 𝔪 ⊔ D.host.conj • 𝔪 := by rw [hsup]; exact Submodule.mem_top
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 h1m
  have e : u - 1 = inc D (s : D.host.E) * (u - 1) + inc D (t : D.host.E) * (u - 1) := by
    rw [← add_mul, ← map_add, show (s : D.host.E) + t = ((s + t : 𝓞 D.host.E) : D.host.E) from rfl, hst]; simp
  rw [e]
  refine add_mem (inc_mul_mem_hatId hs h2) ?_
  rw [mul_comm 𝔪]
  exact inc_mul_mem_hatId ht h1

end GlobalTheory.FunObj.StdDatum.DetCong

end
