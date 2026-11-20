import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfHasSig
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SplitDictHerm

open GlobalTheory.EmbChart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, smul_add, hx, hy]`. Consider the case `tmul a x => show atPlace v (evFin F v a) ⊗ₜ[F] x = atPlace v 1 • (a ⊗ₜ[F] x)`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, atPlace_mul_right, one_mul]`.
-/
theorem tensAt_compFin (v : Pl F) (z : AE F E) : tensAt E v (compFin F E v z) = atPlace v 1 • z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul a x =>
    show atPlace v (evFin F v a) ⊗ₜ[F] x = atPlace v 1 • (a ⊗ₜ[F] x)
    rw [TensorProduct.smul_tmul', smul_eq_mul, atPlace_mul_right, one_mul]

/- English proof (translation)
Introduce `u hu` and use `by rw [smul_eq_mul, mul_comm, atPlace_mul_right, hu, mul_zero, map_zero]`.
-/
theorem at_atPlace (v : Pl F) (c : Fv F v) : At (evFin F v) (atPlace v c) := fun u hu => by
  rw [smul_eq_mul, mul_comm, atPlace_mul_right, hu, mul_zero, map_zero]

/- English proof (translation)
Introduce `u hu` and use `by induction y using TensorProduct.induction_on with | zero => simp | add x y hx hy => rw [map_add, smul_add, hx, hy, add_zero] | tmul a x => rw [tensAt_tmul, TensorProduct.smul_tmul', at_atPlace v a u hu, TensorProduct.zero_tmul]`.
-/
theorem at_tensAt (v : Pl F) (y : Fv F v ⊗[F] E) : At (evFin F v) (tensAt E v y) := fun u hu => by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, smul_add, hx, hy, add_zero]
  | tmul a x =>
    rw [tensAt_tmul, TensorProduct.smul_tmul', at_atPlace v a u hu, TensorProduct.zero_tmul]

/- English proof (translation)
Rewrite using `[tensAt_compFin]`. Establish `h1 : (1 - atPlace v 1) • z = 0` using `hz _ (by rw [map_sub, map_one, evFin_atPlace, sub_self])`. Rewrite `h1` using `[sub_smul, one_smul, sub_eq_zero]`. Conclude with `h1`.
-/
theorem eq_tensAt_of_at {v : Pl F} {z : AE F E} (hz : At (evFin F v) z) : z = tensAt E v (compFin F E v z) := by
  rw [tensAt_compFin]
  have h1 : (1 - atPlace v 1) • z = 0 := hz _ (by rw [map_sub, map_one, evFin_atPlace, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  exact h1

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul a x => rfl`.
-/
theorem compFin_cA (σ : E →ₐ[F] E) (v : Pl F) (z : AE F E) :
    compFin F E v (cA σ z) = sigR (Fv F v) σ (compFin F E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem piW_apply {v : Pl F} (τ : E →ₐ[F] Fv F v) (z : AE F E) : piW τ z = splitProj τ (compFin F E v z) := rfl

/- English proof (translation)
Use `show splitProj τ (evFin F v 1 ⊗ₜ[F] x) = τ x`. Rewrite using `[map_one, splitProj_tmul, one_mul]`.
-/
theorem piW_inclR {v : Pl F} (τ : E →ₐ[F] Fv F v) (x : E) : piW τ (inclR (AF F) x) = τ x := by
  show splitProj τ (evFin F v 1 ⊗ₜ[F] x) = τ x
  rw [map_one, splitProj_tmul, one_mul]

/- English proof (translation)
Use `show splitProj τ (evFin F v a ⊗ₜ[F] 1) = evFin F v a`. Rewrite using `[splitProj_tmul, map_one, mul_one]`.
-/
theorem piW_algebraMap {v : Pl F} (τ : E →ₐ[F] Fv F v) (a : AF F) :
    piW τ (algebraMap (AF F) (AE F E) a) = evFin F v a := by
  show splitProj τ (evFin F v a ⊗ₜ[F] 1) = evFin F v a
  rw [splitProj_tmul, map_one, mul_one]

/- English proof (translation)
Use `show compFin F E v (a • ((1 : AF F) ⊗ₜ[F] x)) = _`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Both sides reduce to the same expression.
-/
theorem compFin_smul_inclR (v : Pl F) (a : AF F) (x : E) :
    compFin F E v (a • inclR (AF F) x) = evFin F v a ⊗ₜ[F] x := by
  show compFin F E v (a • ((1 : AF F) ⊗ₜ[F] x)) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hz`. Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, hav, y, hy, rfl⟩` from `hz`.

Use `⟨fun u hu => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_smul, ← smul_eq_mul, ha u hu, zero_smul]`. Use `tmul_mem_latLoc hav hy using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`. Conclude with `compFin_smul_inclR v a (y j)`.

Consider the case `zero => exact ⟨fun u _ => smul_zero u, by convert zero_mem (latLoc F W.L v) using 1; funext j; simp⟩`. Consider the case `add x y _ _ hx hy`. Use `⟨fun u hu => by rw [smul_add, hx.1 u hu, hy.1 u hu, add_zero], ?_⟩` and prove the remaining obligations. Use `add_mem hx.2 hy.2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`.

Simplify using the standard rewrite rules. Consider the case `neg x _ hx`. Use `⟨fun u hu => by rw [smul_neg, hx.1 u hu, neg_zero], ?_⟩` and prove the remaining obligations. Use `neg_mem hx.2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`.

Simplify using the standard rewrite rules. Introduce and unpack `⟨hz, hl⟩`. Establish `e : z = fun j => tensAt E v (compFin F E v (z j))` using `funext fun j => eq_tensAt_of_at (fun u hu => by`. Use `congrFun (hz u hu) j` as an intermediate fact. Simplify using `using this)`.

Rewrite using `[e]`. Use `latLoc_induction (p := fun Y => (fun j => tensAt E v (Y j)) ∈ GlobalTheory.InertSph.latAt W v) (fun c hc x hx => ?_) (by convert zero_mem (GlobalTheory.InertSph.latAt W v) using 1; funext j; simp) (fun Y Y' hY hY' => ?_) (fun Y hY => ?_) hl` and prove the remaining obligations. Use `AddSubgroup.subset_closure ⟨atPlace v c, at_atPlace v c, by rwa [evFin_atPlace], x, hx, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `j`. Rewrite using `[tensAt_tmul]`.

Use `show _ = atPlace v c • ((1 : AF F) ⊗ₜ[F] x j)`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Use `add_mem hY hY' using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules.

Use `neg_mem hY using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules.
-/
theorem mem_latAt_iff {d : ℕ} (W : Spc F E d) (v : Pl F) (z : Fin d → AE F E) :
    z ∈ GlobalTheory.InertSph.latAt W v ↔ At (evFin F v) z ∧ (fun j => compFin F E v (z j)) ∈ latLoc F W.L v := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hav, y, hy, rfl⟩ := hz
      refine ⟨fun u hu => ?_, ?_⟩
      · rw [smul_smul, ← smul_eq_mul, ha u hu, zero_smul]
      · convert tmul_mem_latLoc hav hy using 1
        funext j
        exact compFin_smul_inclR v a (y j)
    | zero => exact ⟨fun u _ => smul_zero u, by convert zero_mem (latLoc F W.L v) using 1; funext j; simp⟩
    | add x y _ _ hx hy =>
      refine ⟨fun u hu => by rw [smul_add, hx.1 u hu, hy.1 u hu, add_zero], ?_⟩
      convert add_mem hx.2 hy.2 using 1
      funext j; simp
    | neg x _ hx =>
      refine ⟨fun u hu => by rw [smul_neg, hx.1 u hu, neg_zero], ?_⟩
      convert neg_mem hx.2 using 1
      funext j; simp
  · rintro ⟨hz, hl⟩
    have e : z = fun j => tensAt E v (compFin F E v (z j)) := funext fun j => eq_tensAt_of_at (fun u hu => by
      have := congrFun (hz u hu) j
      simpa using this)
    rw [e]
    refine latLoc_induction (p := fun Y => (fun j => tensAt E v (Y j)) ∈ GlobalTheory.InertSph.latAt W v)
      (fun c hc x hx => ?_) (by convert zero_mem (GlobalTheory.InertSph.latAt W v) using 1; funext j; simp) (fun Y Y' hY hY' => ?_)
      (fun Y hY => ?_) hl
    · refine AddSubgroup.subset_closure ⟨atPlace v c, at_atPlace v c, by rwa [evFin_atPlace], x, hx, ?_⟩
      funext j
      rw [tensAt_tmul]
      show _ = atPlace v c • ((1 : AF F) ⊗ₜ[F] x j)
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    · convert add_mem hY hY' using 1
      funext j; simp
    · convert neg_mem hY using 1
      funext j; simp

/- English proof (translation)
Establish `key : ∀ {ρ : E →ₐ[F] Fv F v} {b : GL (Fin d) (Fv F v)}, IsSplitBasis ρ W.L b → ∀ u : Fin d → Fv F v, (∀ i, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ u) i ∈ v.adicCompletionIntegers F) ↔ u ∈ splitLat ρ W.L`. Introduce `ρ b hb u`. Rewrite using `[hb, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`. Rewrite using `[mem_latAt_iff, mem_latLoc_iff_split τ h, key hb₁, key hb₂]`. Conclude with `Iff.rfl`.
-/
theorem mem_latAt_iff_bases {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {d : ℕ} (W : Spc F E d) {v : Pl F}
    (τ : E →ₐ[F] Fv F v) {b₁ b₂ : GL (Fin d) (Fv F v)} (hb₁ : IsSplitBasis τ W.L b₁)
    (hb₂ : IsSplitBasis (τ.comp σ) W.L b₂) (z : Fin d → AE F E) :
    z ∈ GlobalTheory.InertSph.latAt W v ↔ At (evFin F v) z ∧
      (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => piW τ (z j)) i ∈
          v.adicCompletionIntegers F) ∧
      (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => piW (τ.comp σ) (z j)) i ∈
          v.adicCompletionIntegers F) := by
  have key : ∀ {ρ : E →ₐ[F] Fv F v} {b : GL (Fin d) (Fv F v)}, IsSplitBasis ρ W.L b → ∀ u : Fin d → Fv F v,
      (∀ i, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ u) i ∈ v.adicCompletionIntegers F) ↔
        u ∈ splitLat ρ W.L := by
    intro ρ b hb u
    rw [hb, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  rw [mem_latAt_iff, mem_latLoc_iff_split τ h, key hb₁, key hb₂]
  exact Iff.rfl

/- English proof (translation)
Simplify using `only [hE, Formalism.UG.hform, form, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.transpose_apply]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => (by intro a b c; ring : ∀ a b c : E, a * b * c = c * (b * a)) _ _ _`.
-/
theorem hE_transpose (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hE σ Jᵀ x y = form σ J y x := by
  simp only [hE, Formalism.UG.hform, form, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    (by intro a b c; ring : ∀ a b c : E, a * b * c = c * (b * a)) _ _ _

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B d V r s hB hV v hv _`. Establish `h` using `hB.cm`. Take `⟨P, Q, hPQ, hP, hQ⟩` from `hv`. Take `⟨τ, -⟩` from `(existsUnique_splitPrime_eq h hPQ (HeightOneSpectrum.ext hP) (HeightOneSpectrum.ext hQ)).exists`. Use `haveI := hV.lat`.

Take `⟨b₁, hb₁⟩` from `exists_isSplitBasis τ V.L h`. Establish `hdet : V.J.det ≠ 0`. Introduce `h0`. Take `⟨u⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Apply `GlobalTheory.SigDet.det_ne_zero_of_hasSig _ _ _ _ (hV.sig u)` to reduce the goal to its premises.

Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]`. Establish `hdetT : V.Jᵀ.det ≠ 0` using `by rwa [Matrix.det_transpose]`. Establish `hJ : IsHermND σ V.Jᵀ` using `⟨fun i j => hV.herm j i, hdetT⟩`. Establish `hL : IsSelfDualAt σ V.Jᵀ V.L v`. Use `(SelfDual.forall_isSelfDualAt_iff hdetT hV.lat).2 (fun y => ?_) v` and prove the remaining obligations.

Rewrite using `[hV.dual y]`. Use `forall₂_congr fun x _ => ?_` and prove the remaining obligations. Rewrite using `[hE_transpose]`. Conclude with `⟨fun hi => ⟨⟨_, hi⟩, rfl⟩, fun ⟨c, hc⟩ => hc ▸ RingOfIntegers.isIntegral_coe c⟩`. Establish `hb₂` using `IsSplitBasis.dual h hJ hL hb₁`.

Use `⟨piW τ, piW (τ.comp σ), b₁, dualConj 1 (splitGram hJ τ * b₁), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, 1, by simp, ?_⟩` and prove the remaining obligations. Introduce `z`. Rewrite using `[piW_apply, piW_apply, compFin_cA, splitProj_comp]`. Introduce `z`. Rewrite using `[piW_apply, piW_apply, compFin_cA, splitProj_comp_sigR h]`.

Conclude with `piW_algebraMap τ`. Conclude with `piW_algebraMap _`. Introduce `z hz h1 h2`. Establish `e : compFin F E v z = 0` using `split_ext h τ (by rw [map_zero]; exact h1) (by rw [map_zero]; exact h2)`. Rewrite using `[eq_tensAt_of_at hz, e, map_zero]`.

Introduce `x₁ x₂`. Use `⟨tensAt E v ((splitAlgEquiv h τ).symm (x₁, x₂)), at_tensAt v _, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[piW_apply, compFin_tensAt, splitProj_symm]`. Rewrite using `[piW_apply, compFin_tensAt, splitProj_comp_symm]`. Conclude with `mem_latAt_iff_bases h V τ hb₁ hb₂`.

Establish `eJ : (incM F V.J).map (piW τ) = V.J.map τ`. Conclude with `Matrix.ext fun i j => piW_inclR τ (V.J i j)`. Establish `eT : V.J.map τ = ((splitGram hJ τ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v))ᵀ`. Conclude with `Matrix.ext fun i j => rfl`. Establish `eG : V.J.map τ * (((splitGram hJ τ)⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v))ᵀ = 1`.

Rewrite using `[eT, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]`. Rewrite using `[Matrix.map_one _ (by simp) (by simp), eJ, dualConj_one_val, mul_inv_rev, Units.val_mul, Matrix.transpose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc _ (V.J.map τ), eG, Matrix.mul_one, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]`.
-/
theorem split_dict_herm : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (V : Spc F E d) (r s : ℕ), B.IsGood σ → V.IsHerm σ B r s →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v →
    ∃ (π₁ π₂ : AE F E →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
      ((∀ z, π₁ (cA σ z) = π₂ z) ∧ (∀ z, π₂ (cA σ z) = π₁ z) ∧
      (∀ a : AF F, π₁ (algebraMap (AF F) (AE F E) a) = evFin F v a) ∧
      (∀ a : AF F, π₂ (algebraMap (AF F) (AE F E) a) = evFin F v a) ∧
      (∀ z : AE F E, At (evFin F v) z → π₁ z = 0 → π₂ z = 0 → z = 0) ∧
      (∀ x₁ x₂ : Fv F v, ∃ z : AE F E, At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) ∧
      (∀ z : Fin d → AE F E, z ∈ GlobalTheory.InertSph.latAt V v ↔ At (evFin F v) z ∧
        (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₁ (z j)) i ∈
          v.adicCompletionIntegers F) ∧
        (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₂ (z j)) i ∈
          v.adicCompletionIntegers F))) ∧
      ∃ S : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), IsUnit S.det ∧
        S.map (fun x => (x : Fv F v)) =
          (b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F V.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) := by
  intro F E _ _ _ _ _ σ B d V r s hB hV v hv _
  have h := hB.cm
  obtain ⟨P, Q, hPQ, hP, hQ⟩ := hv
  obtain ⟨τ, -⟩ := (existsUnique_splitPrime_eq h hPQ (HeightOneSpectrum.ext hP) (HeightOneSpectrum.ext hQ)).exists
  haveI := hV.lat
  obtain ⟨b₁, hb₁⟩ := exists_isSplitBasis τ V.L h
  have hdet : V.J.det ≠ 0 := by
    intro h0
    obtain ⟨u⟩ : Nonempty (InfinitePlace F) := inferInstance
    apply GlobalTheory.SigDet.det_ne_zero_of_hasSig _ _ _ _ (hV.sig u)
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  have hdetT : V.Jᵀ.det ≠ 0 := by rwa [Matrix.det_transpose]
  have hJ : IsHermND σ V.Jᵀ := ⟨fun i j => hV.herm j i, hdetT⟩
  have hL : IsSelfDualAt σ V.Jᵀ V.L v := by
    refine (SelfDual.forall_isSelfDualAt_iff hdetT hV.lat).2 (fun y => ?_) v
    rw [hV.dual y]
    refine forall₂_congr fun x _ => ?_
    rw [hE_transpose]
    exact ⟨fun hi => ⟨⟨_, hi⟩, rfl⟩, fun ⟨c, hc⟩ => hc ▸ RingOfIntegers.isIntegral_coe c⟩
  have hb₂ := IsSplitBasis.dual h hJ hL hb₁
  refine ⟨piW τ, piW (τ.comp σ), b₁, dualConj 1 (splitGram hJ τ * b₁), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, 1, by simp, ?_⟩
  · intro z; rw [piW_apply, piW_apply, compFin_cA, splitProj_comp]
  · intro z; rw [piW_apply, piW_apply, compFin_cA, splitProj_comp_sigR h]
  · exact piW_algebraMap τ
  · exact piW_algebraMap _
  · intro z hz h1 h2
    have e : compFin F E v z = 0 := split_ext h τ (by rw [map_zero]; exact h1) (by rw [map_zero]; exact h2)
    rw [eq_tensAt_of_at hz, e, map_zero]
  · intro x₁ x₂
    refine ⟨tensAt E v ((splitAlgEquiv h τ).symm (x₁, x₂)), at_tensAt v _, ?_, ?_⟩
    · rw [piW_apply, compFin_tensAt, splitProj_symm]
    · rw [piW_apply, compFin_tensAt, splitProj_comp_symm]
  · exact mem_latAt_iff_bases h V τ hb₁ hb₂
  · have eJ : (incM F V.J).map (piW τ) = V.J.map τ := by
      exact Matrix.ext fun i j => piW_inclR τ (V.J i j)
    have eT : V.J.map τ = ((splitGram hJ τ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v))ᵀ := by
      exact Matrix.ext fun i j => rfl
    have eG : V.J.map τ * (((splitGram hJ τ)⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v))ᵀ = 1 := by
      rw [eT, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]
    rw [Matrix.map_one _ (by simp) (by simp), eJ, dualConj_one_val, mul_inv_rev, Units.val_mul, Matrix.transpose_mul,
      ← Matrix.mul_assoc, Matrix.mul_assoc _ (V.J.map τ), eG, Matrix.mul_one, ← Matrix.transpose_mul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.transpose_one]

end GlobalTheory.SplitDictHerm
