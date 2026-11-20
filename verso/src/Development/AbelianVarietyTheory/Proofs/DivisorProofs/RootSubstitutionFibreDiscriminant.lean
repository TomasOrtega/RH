import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSub
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdIoiSubEqAntisymmMonomial
open NumberField MvPolynomial
open Formalism.BasicNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RelabDR

/- English proof (translation)
Unfold `GlobalTheory.GoodMetric.antisymm`. Simplify using `only [map_sum, map_prod, map_zsmul, rename_rename]`. Rewrite using `[Finset.prod_univ_sum, Fintype.piFinset_univ]`. Use `Finset.sum_congr (by congr) fun w _ => ?_` and prove the remaining obligations. Simplify using `only [zsmul_eq_mul, Finset.prod_mul_distrib, Units.coe_prod, Int.cast_prod]`.

Both sides reduce to the same expression.
-/
theorem antisymm_prod_rename {ι : Type} [Fintype ι] (m : ι → ℕ) (P : ∀ a, MvPolynomial (Fin (m a)) ℝ) :
    GlobalTheory.GoodMetric.antisymm (∏ a, rename (fun i : Fin (m a) => (⟨a, i⟩ : GlobalTheory.GoodMetric.Root m)) (P a)) =
      ∏ a, rename (fun i : Fin (m a) => (⟨a, i⟩ : GlobalTheory.GoodMetric.Root m))
        (∑ v : Equiv.Perm (Fin (m a)), ((Equiv.Perm.sign v : ℤˣ) : ℤ) • rename v (P a)) := by
  classical
  unfold GlobalTheory.GoodMetric.antisymm
  simp only [map_sum, map_prod, map_zsmul, rename_rename]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr (by congr) fun w _ => ?_
  simp only [zsmul_eq_mul, Finset.prod_mul_distrib, Units.coe_prod, Int.cast_prod]
  rfl

/- English proof (translation)
Rewrite using `[← Matrix.det_vandermonde, Matrix.det_apply]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Units.smul_def, map_prod]`. Simplify using the standard rewrite rules.
-/
theorem sum_sign_rename_pow (n : ℕ) :
    (∑ v : Equiv.Perm (Fin n), ((Equiv.Perm.sign v : ℤˣ) : ℤ) •
        rename v (∏ i : Fin n, (X i : MvPolynomial (Fin n) ℝ) ^ (i : ℕ))) =
      ∏ i : Fin n, ∏ i' ∈ Finset.Ioi i, (X i' - X i) := by
  rw [← Matrix.det_vandermonde, Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, map_prod]
  simp

/- English proof (translation)
Rewrite using `[GlobalTheory.prod_Ioi_sub_eq_antisymm_monomial]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Int.cast_smul_eq_zsmul]`.
-/
theorem sum_sign_rename_neg_pow (n : ℕ) :
    (∑ v : Equiv.Perm (Fin n), ((Equiv.Perm.sign v : ℤˣ) : ℤ) •
        rename v (∏ i : Fin n, (-X i : MvPolynomial (Fin n) ℝ) ^ (n - 1 - (i : ℕ)))) =
      ∏ i : Fin n, ∏ i' ∈ Finset.Ioi i, (X i' - X i) := by
  rw [GlobalTheory.prod_Ioi_sub_eq_antisymm_monomial]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Int.cast_smul_eq_zsmul]

/- English proof (translation)
Establish `h : (∏ z : GlobalTheory.GoodMetric.Root m, if b z.1 then (-X z : MvPolynomial (GlobalTheory.GoodMetric.Root m) ℝ) ^ (m z.1 - 1 - (z.2 : ℕ)) else X z ^ (z.2 : ℕ)) = ∏ a, rename (fun i : Fin (m a) => (⟨a, i⟩ : GlobalTheory.GoodMetric.Root m)) (if b a then ∏ i : Fin (m a), (-X i : M …`. Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases hb : b a <;> simp [hb]`. Rewrite using `[h, antisymm_prod_rename]`.

Unfold `GlobalTheory.GoodMetric.rootDiscr`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Establish `e : (∑ v : Equiv.Perm (Fin (m a)), ((Equiv.Perm.sign v : ℤˣ) : ℤ) • rename v (if b a then ∏ i : Fin (m a), (-X i : MvPolynomial (Fin (m a)) ℝ) ^ (m a - 1 - (i : ℕ)) else ∏ i : Fin (m a), X i ^ (i : ℕ))) = ∏ i : Fin (m a), ∏ i' ∈ Finset.Ioi i, (X i' - X i)` using `by split_ifs`. Conclude with `sum_sign_rename_neg_pow _`. Conclude with `sum_sign_rename_pow _`.

Rewrite using `[e]`. Simplify using `only [map_prod, map_sub, rename_X]`. Conclude with `Finset.prod_comm' (fun j i => by simp [and_comm])`.
-/
theorem antisymm_mixed {ι : Type} [Fintype ι] (m : ι → ℕ) (b : ι → Prop) [DecidablePred b] :
    GlobalTheory.GoodMetric.antisymm (∏ z : GlobalTheory.GoodMetric.Root m,
      if b z.1 then (-X z : MvPolynomial (GlobalTheory.GoodMetric.Root m) ℝ) ^ (m z.1 - 1 - (z.2 : ℕ)) else X z ^ (z.2 : ℕ)) =
      GlobalTheory.GoodMetric.rootDiscr m := by
  have h : (∏ z : GlobalTheory.GoodMetric.Root m,
      if b z.1 then (-X z : MvPolynomial (GlobalTheory.GoodMetric.Root m) ℝ) ^ (m z.1 - 1 - (z.2 : ℕ)) else X z ^ (z.2 : ℕ)) =
      ∏ a, rename (fun i : Fin (m a) => (⟨a, i⟩ : GlobalTheory.GoodMetric.Root m))
        (if b a then ∏ i : Fin (m a), (-X i : MvPolynomial (Fin (m a)) ℝ) ^ (m a - 1 - (i : ℕ))
          else ∏ i : Fin (m a), X i ^ (i : ℕ)) := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun a _ => ?_
    by_cases hb : b a <;> simp [hb]
  rw [h, antisymm_prod_rename]
  unfold GlobalTheory.GoodMetric.rootDiscr
  refine Finset.prod_congr rfl fun a _ => ?_
  have e : (∑ v : Equiv.Perm (Fin (m a)), ((Equiv.Perm.sign v : ℤˣ) : ℤ) • rename v
      (if b a then ∏ i : Fin (m a), (-X i : MvPolynomial (Fin (m a)) ℝ) ^ (m a - 1 - (i : ℕ))
          else ∏ i : Fin (m a), X i ^ (i : ℕ))) = ∏ i : Fin (m a), ∏ i' ∈ Finset.Ioi i, (X i' - X i) := by
    split_ifs
    · exact sum_sign_rename_neg_pow _
    · exact sum_sign_rename_pow _
  rw [e]
  simp only [map_prod, map_sub, rename_X]
  exact Finset.prod_comm' (fun j i => by simp [and_comm])

/- English proof (translation)
Establish `h` using `LieGen.rootIdx_bijective O.S`. Conclude with `(Function.Bijective.of_comp_iff' ((finCongr (length_letters O.S)).bijective.comp (((GlobalTheory.Proof.LetterConjugation.nodup_letters O.S.Dw).getEquivOfForallMemList _ (GlobalTheory.Proof.LetterConjugation.mem_letters O.S.Dw)).symm.bijective)) _).1 h`.
-/
theorem rootL_bijective {D : D7} (O : Setup D) : Function.Bijective (rootL O) := by
  classical
  have h := LieGen.rootIdx_bijective O.S
  exact (Function.Bijective.of_comp_iff' ((finCongr (length_letters O.S)).bijective.comp
    (((GlobalTheory.Proof.LetterConjugation.nodup_letters O.S.Dw).getEquivOfForallMemList _
      (GlobalTheory.Proof.LetterConjugation.mem_letters O.S.Dw)).symm.bijective)) _).1 h

/- English proof (translation)
Introduce `D O`. Rewrite using `[← antisymm_mixed O.S.Dw.mult (fun σ => σ (O.A.H.rt : D.host.E) = O.A.H.rt0)]`. Use `congr 1`. Unfold `fibPt`. Rewrite using `[map_prod]`.

Use `Fintype.prod_bijective _ (rootL_bijective O) _ _ ?_` and prove the remaining obligations. Introduce and unpack `⟨t, i⟩`. Simplify using `only [map_pow, map_neg, aeval_X, rootSub, rootSg]`. Distinguish the cases in `hi : (i : ℕ) < O.j`. Establish `e : rootL O (t, i) = ⟨DV.tauEmb D t, ⟨i, by rw [LieGen.mult_tau O.S]; exact hi⟩⟩` using `dif_pos hi`.

Rewrite using `[e, if_pos hi, if_pos hi, if_pos (O.A.cm t)]`. Simplify using `[LieGen.mult_tau O.S]`. Establish `e : rootL O (t, i) = ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (DV.tauEmb D t), ⟨O.N - 1 - i, by rw [LieGen.mult_conj_tau O.S]; have` using `i.2; omega⟩⟩ := dif_neg hi`. Rewrite using `[e, if_neg hi, if_neg hi, if_neg (GlobalTheory.Proof.LetterConjugation.conj_ne (O.A.cm t))]`. Simplify using the standard rewrite rules.
-/
theorem antisymm_fibPt : ∀ (D : D7) (O : Setup D),
    GlobalTheory.GoodMetric.antisymm (aeval (GlobalTheory.RelabDR.rootSub O) (fibPt D.what₂.Tau O.N O.j)) =
      GlobalTheory.GoodMetric.rootDiscr O.S.Dw.mult := by
  intro D O
  classical
  rw [← antisymm_mixed O.S.Dw.mult (fun σ => σ (O.A.H.rt : D.host.E) = O.A.H.rt0)]
  congr 1
  unfold fibPt
  rw [map_prod]
  refine Fintype.prod_bijective _ (rootL_bijective O) _ _ ?_
  rintro ⟨t, i⟩
  simp only [map_pow, map_neg, aeval_X, rootSub, rootSg]
  by_cases hi : (i : ℕ) < O.j
  · have e : rootL O (t, i) = ⟨DV.tauEmb D t, ⟨i, by rw [LieGen.mult_tau O.S]; exact hi⟩⟩ := dif_pos hi
    rw [e, if_pos hi, if_pos hi, if_pos (O.A.cm t)]
    simp [LieGen.mult_tau O.S]
  · have e : rootL O (t, i) = ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (DV.tauEmb D t),
        ⟨O.N - 1 - i, by rw [LieGen.mult_conj_tau O.S]; have := i.2; omega⟩⟩ := dif_neg hi
    rw [e, if_neg hi, if_neg hi, if_neg (GlobalTheory.Proof.LetterConjugation.conj_ne (O.A.cm t))]
    simp

end GlobalTheory.RelabDR

end
