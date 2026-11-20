import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.LeviHC.BlockTriLine

open NormedSpace in
/- English proof (translation)
Establish `hpow : ∀ k, ∀ i j, b j < b i + s → (W ^ (k + 1)) i j = 0`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simpa using hW`. Consider the case `succ k ih`.

Introduce `i j hij`. Rewrite using `[pow_succ, Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : b l < b i + s`. Rewrite using `[ih i l h, zero_mul]`.

Rewrite using `[hW l j (by omega), mul_zero]`. Introduce `i j hij`. Establish `hs : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • W ^ n) (exp W)` using `by open scoped Matrix.Norms.Operator in exact exp_series_hasSum_exp' (𝕂 := ℂ) W`. Establish `h1` using `hs.map (Matrix.entryAddMonoidHom ℂ i j) (continuous_id.matrix_elem i j)`. Establish `h2 : HasSum (⇑(Matrix.entryAddMonoidHom ℂ i j) ∘ fun n : ℕ => ((n.factorial : ℂ)⁻¹) • W ^ n) ((1 : Matrix (Fin m) (Fin m) ℂ) i j)`.

Use `hasSum_single (f := ⇑(Matrix.entryAddMonoidHom ℂ i j) ∘ fun n : ℕ => ((n.factorial : ℂ)⁻¹) • W ^ n) 0 _` and compare the differences between its conclusion and the goal. Use `show _ = ((((Nat.factorial 0 : ℕ) : ℂ))⁻¹ • W ^ 0) i j`. Simplify using the standard rewrite rules. Introduce `k hk`. Take `⟨k, rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hk`.

Use `show ((((k + 1).factorial : ℂ))⁻¹ • W ^ (k + 1)) i j = 0`. Rewrite using `[Matrix.smul_apply, hpow k i j hij, smul_zero]`. Rewrite using `[Matrix.sub_apply, sub_eq_zero]`. Conclude with `h1.unique h2`.
-/
theorem entry_exp_sub_one {m : ℕ} (b : Fin m → ℕ) (s : ℕ) (W : Matrix (Fin m) (Fin m) ℂ)
    (hW : ∀ i j, b j < b i + s → W i j = 0) : ∀ i j, b j < b i + s → (exp W - 1) i j = 0 := by
  have hpow : ∀ k, ∀ i j, b j < b i + s → (W ^ (k + 1)) i j = 0 := by
    intro k
    induction k with
    | zero => simpa using hW
    | succ k ih =>
      intro i j hij
      rw [pow_succ, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases h : b l < b i + s
      · rw [ih i l h, zero_mul]
      · rw [hW l j (by omega), mul_zero]
  intro i j hij
  have hs : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • W ^ n) (exp W) := by
    open scoped Matrix.Norms.Operator in exact exp_series_hasSum_exp' (𝕂 := ℂ) W
  have h1 := hs.map (Matrix.entryAddMonoidHom ℂ i j) (continuous_id.matrix_elem i j)
  have h2 : HasSum (⇑(Matrix.entryAddMonoidHom ℂ i j) ∘ fun n : ℕ => ((n.factorial : ℂ)⁻¹) • W ^ n)
      ((1 : Matrix (Fin m) (Fin m) ℂ) i j) := by
    convert hasSum_single (f := ⇑(Matrix.entryAddMonoidHom ℂ i j) ∘ fun n : ℕ => ((n.factorial : ℂ)⁻¹) • W ^ n) 0 _
    · show _ = ((((Nat.factorial 0 : ℕ) : ℂ))⁻¹ • W ^ 0) i j
      simp
    · intro k hk
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
      show ((((k + 1).factorial : ℂ))⁻¹ • W ^ (k + 1)) i j = 0
      rw [Matrix.smul_apply, hpow k i j hij, smul_zero]
  rw [Matrix.sub_apply, sub_eq_zero]
  exact h1.unique h2

open NormedSpace in

/- English proof (translation)
Set `L : Matrix (Fin n) (Fin n) ℂ →+* Matrix (Fin m) (Fin m) ℂ` to `{ toFun := fun A => R * A * Q map_one' := by simp [hRQ] map_mul' := fun A B => by`. Combine the equalities or inequalities in the displayed calculation. Use the proof step `map_zero' := by simp`. Use the proof step `map_add' := fun A B => by simp [Matrix.mul_add, Matrix.add_mul] }`. Establish `hc : Continuous L` using `(continuous_const.matrix_mul continuous_id).matrix_mul continuous_const`.

Use `open scoped Matrix.Norms.Operator in exact map_exp L hc X`.
-/
theorem conj_exp {n m : ℕ} (R : Matrix (Fin m) (Fin n) ℂ) (Q : Matrix (Fin n) (Fin m) ℂ) (hQR : Q * R = 1)
    (hRQ : R * Q = 1) (X : Matrix (Fin n) (Fin n) ℂ) : R * exp X * Q = exp (R * X * Q) := by
  let L : Matrix (Fin n) (Fin n) ℂ →+* Matrix (Fin m) (Fin m) ℂ :=
    { toFun := fun A => R * A * Q
      map_one' := by simp [hRQ]
      map_mul' := fun A B => by
        calc R * (A * B) * Q = R * A * (Q * R) * B * Q := by rw [hQR, Matrix.mul_one]; simp only [Matrix.mul_assoc]
          _ = _ := by simp only [Matrix.mul_assoc]
      map_zero' := by simp
      map_add' := fun A B => by simp [Matrix.mul_add, Matrix.add_mul] }
  have hc : Continuous L := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  open scoped Matrix.Norms.Operator in exact map_exp L hc X

open NormedSpace in

/- English proof (translation)
Establish `e : (R * (exp (t • Z) - 1) * Q : Matrix (Fin m) (Fin m) ℂ) = exp (t • (R * Z * Q)) - 1`. Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hRQ, conj_exp R Q hQR hRQ]`. Use `congr 2`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul]`. Rewrite using `[e]`.

Use `entry_exp_sub_one b s _ fun i j hij => ?_` and prove the remaining obligations. Rewrite using `[Matrix.smul_apply, hZ i j hij, smul_zero]`.
-/
theorem entry_conj_exp {n m : ℕ} (R : Matrix (Fin m) (Fin n) ℂ) (Q : Matrix (Fin n) (Fin m) ℂ) (hQR : Q * R = 1)
    (hRQ : R * Q = 1) (b : Fin m → ℕ) (s : ℕ) (Z : Matrix (Fin n) (Fin n) ℂ)
    (hZ : ∀ i j, b j < b i + s → (R * Z * Q) i j = 0) (t : ℝ) :
    ∀ i j, b j < b i + s → (R * (exp (t • Z) - 1) * Q : Matrix (Fin m) (Fin m) ℂ) i j = 0 := by
  have e : (R * (exp (t • Z) - 1) * Q : Matrix (Fin m) (Fin m) ℂ) = exp (t • (R * Z * Q)) - 1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hRQ, conj_exp R Q hQR hRQ]
    congr 2
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [e]
  refine entry_exp_sub_one b s _ fun i j hij => ?_
  rw [Matrix.smul_apply, hZ i j hij, smul_zero]

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {w : InfinitePlace F}

variable (F E) in

def placeToAdeles (w : InfinitePlace F) : w.Completion ⊗[F] E →ₙ+* AE F E :=
  (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (R' := AF F) (LinearMap.inl F (Ainf F) (Af F)) (fun _ _ => Prod.ext rfl (mul_zero _).symm)).comp
    (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (GlobalTheory.AutFunCompare.sgW w) (GlobalTheory.AutFunCompare.sgW_mul w))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem placeToAdeles_apply (x : w.Completion ⊗[F] E) :
    placeToAdeles F E w x = GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (R' := AF F) (LinearMap.inl F (Ainf F) (Af F))
      (fun _ _ => Prod.ext rfl (mul_zero _).symm)
      (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (GlobalTheory.AutFunCompare.sgW w) (GlobalTheory.AutFunCompare.sgW_mul w) x) := rfl

/- English proof (translation)
Use extensionality with `r s`. Rewrite using `[Matrix.sub_apply, Matrix.map_apply, Matrix.sub_apply]`. Establish `e1` using `GlobalTheory.AutFunCompare.mat_extH (R' := AF F) σ J (LinearMap.inl F (Ainf F) (Af F)) (fun _ _ => Prod.ext rfl (mul_zero _).symm) (embArchInf σ J w y) r s`. Establish `e2` using `GlobalTheory.AutFunCompare.mat_extH σ J (GlobalTheory.AutFunCompare.sgW w) (GlobalTheory.AutFunCompare.sgW_mul w) y r s`. Express the relevant statement in the definitionally equal form `(HA.mat _ σ J (ofInf σ J (embArchInf σ J w y))).1 r s - _ = placeToAdeles F E w ((HA.mat _ σ J y).1 r s - _)`.

Rewrite using `[ofInf, e1]`. Use `erw [e2]`. Rewrite using `[placeToAdeles_apply]`. Distinguish the cases in `h : r = s`. Substitute `h` using the available equality.

Simplify using `only [Matrix.one_apply_eq, mul_one, map_sub, map_add]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[Matrix.one_apply_ne h]`.
-/
theorem mat_embArch_sub_one (y : GArch σ J w) :
    (((embArch σ J w y).1 : GL (Fin n) (AE F E)).1 - 1 : Matrix (Fin n) (Fin n) (AE F E)) =
      ((y.1 : GL (Fin n) (w.Completion ⊗[F] E)).1 - 1 : Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E)).map
        (placeToAdeles F E w) := by
  ext r s
  rw [Matrix.sub_apply, Matrix.map_apply, Matrix.sub_apply]
  have e1 := GlobalTheory.AutFunCompare.mat_extH (R' := AF F) σ J (LinearMap.inl F (Ainf F) (Af F))
    (fun _ _ => Prod.ext rfl (mul_zero _).symm) (embArchInf σ J w y) r s
  have e2 := GlobalTheory.AutFunCompare.mat_extH σ J (GlobalTheory.AutFunCompare.sgW w) (GlobalTheory.AutFunCompare.sgW_mul w) y r s
  change (HA.mat _ σ J (ofInf σ J (embArchInf σ J w y))).1 r s - _ = placeToAdeles F E w ((HA.mat _ σ J y).1 r s - _)
  rw [ofInf, e1]
  erw [e2]
  rw [placeToAdeles_apply]
  by_cases h : r = s
  · subst h
    simp only [Matrix.one_apply_eq, mul_one, map_sub, map_add]
    ring
  · simp [Matrix.one_apply_ne h]

/- English proof (translation)
Establish `h1 : placeToAdeles F E w (inclR (F` using `F) w.Completion e) = inclR (F := F) (AF F) e * placeToAdeles F E w 1 := by show placeToAdeles F E w ((1 : w.Completion) ⊗ₜ[F] e) = ((1 : AF F) ⊗ₜ[F] e) * placeToAdeles F E w ((1 : w.Completion) ⊗ₜ[F] (1 : E))`. Rewrite using `[placeToAdeles_apply, placeToAdeles_apply]`. Simplify using `only [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul]`. Use `erw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul]`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]`.

Rewrite using `[map_mul, h1, mul_assoc, ← map_mul, one_mul]`.
-/
theorem placeToAdeles_inclR_mul (e : E) (x : w.Completion ⊗[F] E) :
    placeToAdeles F E w (inclR (F := F) w.Completion e * x) = inclR (F := F) (AF F) e * placeToAdeles F E w x := by
  have h1 : placeToAdeles F E w (inclR (F := F) w.Completion e) = inclR (F := F) (AF F) e * placeToAdeles F E w 1 := by
    show placeToAdeles F E w ((1 : w.Completion) ⊗ₜ[F] e) =
      ((1 : AF F) ⊗ₜ[F] e) * placeToAdeles F E w ((1 : w.Completion) ⊗ₜ[F] (1 : E))
    rw [placeToAdeles_apply, placeToAdeles_apply]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul]
    erw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul]
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rw [map_mul, h1, mul_assoc, ← map_mul, one_mul]

/- English proof (translation)
Establish `key : ∀ (a c : E) (x : w.Completion ⊗[F] E), inclR (F` using `F) (AF F) a * placeToAdeles F E w x * inclR (F := F) (AF F) c = placeToAdeles F E w (inclR (F := F) w.Completion a * x * inclR (F := F) w.Completion c) := by`. Introduce `a c x`. Establish `k : placeToAdeles F E w (inclR (F` using `F) w.Completion c * (inclR (F := F) w.Completion a * x)) = inclR (F := F) (AF F) c * (inclR (F := F) (AF F) a * placeToAdeles F E w x) := (placeToAdeles_inclR_mul c _).trans (congrArg (inclR (F := F) (AF F) c * ·) (placeToAdeles_inclR_mul a x))`. Combine the equalities or inequalities in the displayed calculation. Use extensionality with `i j`.

Simplify using `only [Matrix.mul_apply, Matrix.map_apply, incM, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Conclude with `key _ _ _`.
-/
theorem incM_mul_map_mul {m : ℕ} (R : Matrix (Fin m) (Fin n) E) (Q : Matrix (Fin n) (Fin m) E)
    (N : Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E)) :
    (incM F R * N.map (placeToAdeles F E w) * incM F Q : Matrix (Fin m) (Fin m) (AE F E)) =
      (R.map (inclR (F := F) w.Completion) * N * Q.map (inclR (F := F) w.Completion)).map (placeToAdeles F E w) := by
  have key : ∀ (a c : E) (x : w.Completion ⊗[F] E), inclR (F := F) (AF F) a * placeToAdeles F E w x *
      inclR (F := F) (AF F) c = placeToAdeles F E w (inclR (F := F) w.Completion a * x * inclR (F := F) w.Completion c) := by
    intro a c x
    have k : placeToAdeles F E w (inclR (F := F) w.Completion c * (inclR (F := F) w.Completion a * x)) =
        inclR (F := F) (AF F) c * (inclR (F := F) (AF F) a * placeToAdeles F E w x) :=
      (placeToAdeles_inclR_mul c _).trans (congrArg (inclR (F := F) (AF F) c * ·) (placeToAdeles_inclR_mul a x))
    calc _ = inclR (F := F) (AF F) c * (inclR (F := F) (AF F) a * placeToAdeles F E w x) := by ring
      _ = _ := k.symm
      _ = _ := congrArg _ (by ring)
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, incM, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  exact key _ _ _

end Adelic

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {w : InfinitePlace F}

/- English proof (translation)
Establish `hι : (infEmb τ ∘ inclR (F` using `F) w.Completion) = τ.1 := funext fun e => by show infEmb τ ((1 : w.Completion) ⊗ₜ[F] e) = τ.1 e`. Rewrite using `[infEmb_tmul, map_one, one_mul]`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, Matrix.map_map, Matrix.map_map, hι, GlobalTheory.Orb.archMat_apply]`. Use `congr 2`. Use extensionality with `r s`.

Simplify using `only [Matrix.map_apply, Matrix.sub_apply, map_sub, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp <;> rfl`.
-/
theorem map_infEmb_conj (τ : EmbOver E w) {m : ℕ} (R : Matrix (Fin m) (Fin n) E) (Q : Matrix (Fin n) (Fin m) E)
    (y : GArch σ J w) :
    (R.map (inclR (F := F) w.Completion) * ((y.1 : GL (Fin n) (w.Completion ⊗[F] E)).1 - 1) *
        Q.map (inclR (F := F) w.Completion)).map (infEmb τ) =
      R.map τ.1 * (GlobalTheory.Orb.archMat σ J τ y - 1) * Q.map τ.1 := by
  have hι : (infEmb τ ∘ inclR (F := F) w.Completion) = τ.1 := funext fun e => by
    show infEmb τ ((1 : w.Completion) ⊗ₜ[F] e) = τ.1 e
    rw [infEmb_tmul, map_one, one_mul]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_map, Matrix.map_map, hι, GlobalTheory.Orb.archMat_apply]
  congr 2
  ext r s
  simp only [Matrix.map_apply, Matrix.sub_apply, map_sub, Matrix.one_apply]
  split_ifs <;> simp <;> rfl

/- English proof (translation)
Introduce `i j hij`. Rewrite using `[mat_embArch_sub_one, incM_mul_map_mul, Matrix.map_apply]`. Establish `h0 : (R.map (inclR (F` using `F) w.Completion) * ((y.1 : GL (Fin n) (w.Completion ⊗[F] E)).1 - 1) * Q.map (inclR (F := F) w.Completion) : Matrix (Fin m) (Fin m) (w.Completion ⊗[F] E)) i j = 0 := by`. Apply `(infEmb_bijective h τ).1` to reduce the goal to its premises. Rewrite using `[map_zero, ← hy i j hij, ← map_infEmb_conj τ R Q y]`.

Both sides reduce to the same expression. Rewrite using `[h0, map_zero]`.
-/
theorem entry_embArch (h : IsCMExt F E σ) (τ : EmbOver E w) {m : ℕ} (R : Matrix (Fin m) (Fin n) E)
    (Q : Matrix (Fin n) (Fin m) E) (b : Fin m → ℕ) (s : ℕ) (y : GArch σ J w)
    (hy : ∀ i j, b j < b i + s → (R.map τ.1 * (GlobalTheory.Orb.archMat σ J τ y - 1) * Q.map τ.1 : Matrix (Fin m) (Fin m) ℂ) i j = 0) :
    ∀ i j, b j < b i + s →
      (incM F R * (((embArch σ J w y).1 : GL (Fin n) (AE F E)).1 - 1 : Matrix (Fin n) (Fin n) (AE F E)) * incM F Q :
        Matrix (Fin m) (Fin m) (AE F E)) i j = 0 := by
  intro i j hij
  rw [mat_embArch_sub_one, incM_mul_map_mul, Matrix.map_apply]
  have h0 : (R.map (inclR (F := F) w.Completion) * ((y.1 : GL (Fin n) (w.Completion ⊗[F] E)).1 - 1) *
      Q.map (inclR (F := F) w.Completion) : Matrix (Fin m) (Fin m) (w.Completion ⊗[F] E)) i j = 0 := by
    apply (infEmb_bijective h τ).1
    rw [map_zero, ← hy i j hij, ← map_infEmb_conj τ R Q y]
    rfl
  rw [h0, map_zero]

end Main

open NormedSpace in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ h n J _ m Q R hQR hRQ b s w τ Z γ hγ hZ t i j hij`. Establish `hQR' : Q.map τ.1 * R.map τ.1 = 1`. Rewrite using `[← Matrix.map_mul, hQR, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hRQ' : R.map τ.1 * Q.map τ.1 = 1`. Rewrite using `[← Matrix.map_mul, hRQ, Matrix.map_one _ (map_zero _) (map_one _)]`.

Take `⟨y, hy1, hy2⟩` from `hγ t`. Establish `hA : GlobalTheory.Orb.archMat σ J τ y⁻¹ = exp ((-t) • Z)`. Establish `e1 : GlobalTheory.Orb.archMat σ J τ y⁻¹ * GlobalTheory.Orb.archMat σ J τ y = 1`. Rewrite using `[← map_mul, inv_mul_cancel, map_one]`. Establish `e2 : exp (t • Z) * exp ((-t) • Z) = 1`.

Rewrite using `[← Matrix.exp_add_of_commute _ _ (((Commute.refl Z).smul_left t).smul_right (-t)), ← add_smul, add_neg_cancel, zero_smul, exp_zero]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e2, Matrix.mul_one]`. Use `_ = (GlobalTheory.Orb.archMat σ J τ y⁻¹ * GlobalTheory.Orb.archMat σ J τ y) * exp ((-t) • Z) := by`. Rewrite using `[hy2, Matrix.mul_assoc]`.

Use `_ = _ := by rw [e1, Matrix.one_mul]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hy1]`. Use `entry_embArch h τ R Q b s y (fun i j hij => ?_) i j hij` and prove the remaining obligations. Rewrite using `[hy2]`.

Conclude with `entry_conj_exp _ _ hQR' hRQ' b s Z hZ t i j hij`. Rewrite using `[hy1, ← map_inv]`. Use `entry_embArch h τ R Q b s y⁻¹ (fun i j hij => ?_) i j hij` and prove the remaining obligations. Rewrite using `[hA]`. Conclude with `entry_conj_exp _ _ hQR' hRQ' b s Z hZ (-t) i j hij`.
-/
theorem blockTri_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (m : ℕ) (Q : Matrix (Fin n) (Fin m) E) (R : Matrix (Fin m) (Fin n) E), Q * R = 1 → R * Q = 1 →
    ∀ (b : Fin m → ℕ) (s : ℕ) (w : InfinitePlace F) (τ : EmbOver E w) (Z : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → GAd σ J),
      IsLineOf σ J τ Z γ → (∀ i j, b j < b i + s → (R.map τ.1 * Z * Q.map τ.1) i j = 0) → ∀ t i j, b j < b i + s →
        (incM F R * (((γ t).1 : GL (Fin n) (AE F E)).1 - 1 : Matrix (Fin n) (Fin n) (AE F E)) * incM F Q : Matrix (Fin m) (Fin m) (AE F E)) i j = 0 ∧
        (incM F R * ((((γ t)⁻¹).1 : GL (Fin n) (AE F E)).1 - 1 : Matrix (Fin n) (Fin n) (AE F E)) * incM F Q : Matrix (Fin m) (Fin m) (AE F E)) i j = 0 := by
  intro F E _ _ _ _ _ σ h n J _ m Q R hQR hRQ b s w τ Z γ hγ hZ t i j hij
  have hQR' : Q.map τ.1 * R.map τ.1 = 1 := by
    rw [← Matrix.map_mul, hQR, Matrix.map_one _ (map_zero _) (map_one _)]
  have hRQ' : R.map τ.1 * Q.map τ.1 = 1 := by
    rw [← Matrix.map_mul, hRQ, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨y, hy1, hy2⟩ := hγ t
  have hA : GlobalTheory.Orb.archMat σ J τ y⁻¹ = exp ((-t) • Z) := by
    have e1 : GlobalTheory.Orb.archMat σ J τ y⁻¹ * GlobalTheory.Orb.archMat σ J τ y = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    have e2 : exp (t • Z) * exp ((-t) • Z) = 1 := by
      rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl Z).smul_left t).smul_right (-t)), ← add_smul,
        add_neg_cancel, zero_smul, exp_zero]
    calc GlobalTheory.Orb.archMat σ J τ y⁻¹ = GlobalTheory.Orb.archMat σ J τ y⁻¹ * (exp (t • Z) * exp ((-t) • Z)) := by
          rw [e2, Matrix.mul_one]
      _ = (GlobalTheory.Orb.archMat σ J τ y⁻¹ * GlobalTheory.Orb.archMat σ J τ y) * exp ((-t) • Z) := by
          rw [hy2, Matrix.mul_assoc]
      _ = _ := by rw [e1, Matrix.one_mul]
  refine ⟨?_, ?_⟩
  · rw [hy1]
    refine entry_embArch h τ R Q b s y (fun i j hij => ?_) i j hij
    rw [hy2]
    exact entry_conj_exp _ _ hQR' hRQ' b s Z hZ t i j hij
  · rw [hy1, ← map_inv]
    refine entry_embArch h τ R Q b s y⁻¹ (fun i j hij => ?_) i j hij
    rw [hA]
    exact entry_conj_exp _ _ hQR' hRQ' b s Z hZ (-t) i j hij

end GlobalTheory.LeviHC.BlockTriLine
