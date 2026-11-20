import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.FinMatchDefs
import Development.AutomorphicArithmetic.DivisorFrames.MemIntAfAndInIdIffSplitComponents
import Development.AutomorphicArithmetic.DivisorFrames.UnitCharIdempotentSumEqProdOverSplitPlaces

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Establish `h1 : (m⁻¹).1 = Wi.submatrix e e`. Establish `: Wi.submatrix e e * m.1 = 1`. Rewrite using `[hm, Matrix.submatrix_mul_equiv, hW]`. Conclude with `Matrix.submatrix_one_equiv e`. Combine the equalities or inequalities in the displayed calculation.

Establish `h2 : (G * B)ᵀ * ((X * Gi)ᵀ).submatrix id e = ((X * B)ᵀ).submatrix id e`. Establish `: (G * B)ᵀ * ((X * Gi)ᵀ).submatrix id e = ((G * B)ᵀ * (X * Gi)ᵀ).submatrix id e` using `rfl`. Rewrite using `[this, ← Matrix.transpose_mul, Matrix.mul_assoc X, ← Matrix.mul_assoc Gi, hG, Matrix.one_mul]`. Rewrite using `[h2, GlobalTheory.SplitFlip.invT_val, h1, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul, Matrix.mul_assoc]`.
-/
private theorem fmFst_mat {k : Type} [Field k] {a n d : ℕ} (e : Fin n ≃ Fin d) (B G Gi : Matrix (Fin a) (Fin a) k) (hG : Gi * G = 1)
    (W Wi : Matrix (Fin d) (Fin d) k) (hW : Wi * W = 1) (m : GL (Fin n) k) (hm : m.1 = W.submatrix e e)
    (X : Matrix (Fin d) (Fin a) k) :
    (G * B)ᵀ * ((X * Gi)ᵀ).submatrix id e * (GlobalTheory.SplitFlip.invT m).1 = ((Wi * X * B)ᵀ).submatrix id e := by
  have h1 : (m⁻¹).1 = Wi.submatrix e e := by
    have : Wi.submatrix e e * m.1 = 1 := by
      rw [hm, Matrix.submatrix_mul_equiv, hW]; exact Matrix.submatrix_one_equiv e
    calc (m⁻¹).1 = (Wi.submatrix e e * m.1) * (m⁻¹).1 := by rw [this, Matrix.one_mul]
      _ = Wi.submatrix e e := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have h2 : (G * B)ᵀ * ((X * Gi)ᵀ).submatrix id e = ((X * B)ᵀ).submatrix id e := by
    have : (G * B)ᵀ * ((X * Gi)ᵀ).submatrix id e = ((G * B)ᵀ * (X * Gi)ᵀ).submatrix id e := rfl
    rw [this, ← Matrix.transpose_mul, Matrix.mul_assoc X, ← Matrix.mul_assoc Gi, hG, Matrix.one_mul]
  rw [h2, GlobalTheory.SplitFlip.invT_val, h1, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul,
    Matrix.mul_assoc]

/- English proof (translation)
Substitute `hr` using the available equality. Establish `hb : GlobalTheory.StdPairCone.blk₁ ((Mᵀ).submatrix id (finCongr (rfl : a + a' = a + a'))) = (topL a M)ᵀ`. Use extensionality with `i j`. Establish `: j.1 < a + a' ∧ i.1 < a` using `⟨by omega, i.2⟩`. Simplify using `only [GlobalTheory.StdPairCone.blk₁, topL, Matrix.of_apply, Matrix.submatrix_apply, Matrix.transpose_apply, dif_pos this]`.

Both sides reduce to the same expression. Establish `hb2 : ∀ i j, GlobalTheory.StdPairCone.blk₂ ((Mᵀ).submatrix id (finCongr (rfl : a + a' = a + a'))) i j = M (Fin.natAdd a j) i` using `fun i j => rfl`. Establish `hb1 : ∀ i j, GlobalTheory.StdPairCone.blk₁ ((Mᵀ).submatrix id (finCongr (rfl : a + a' = a + a'))) i j = M (Fin.castAdd a' j) i` using `fun i j => rfl`. Establish `hd : (GlobalTheory.StdPairCone.blk₁ ((Mᵀ).submatrix id (finCongr (rfl : a + a' = a + a')))).det = (topL a M).det`. Rewrite using `[hb, Matrix.det_transpose]`.

Establish `hsub : ∀ x, x ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) → x ∈ (ValuativeRel.valuation k).integer`. Introduce `x hx`. Establish `h1 : ValuativeRel.valuation k x ≤ ValuativeRel.valuation k ((ϖ ^ c : kˣ) : k)` using `hx`. Establish `h2 : ((ϖ ^ c : kˣ) : k) ∈ (ValuativeRel.valuation k).integer`. Rewrite using `[Units.val_pow_eq_pow_val]`.

Conclude with `pow_mem hϖ.mem c`. Conclude with `(Valuation.mem_integer_iff _ _).2 (le_trans h1 ((Valuation.mem_integer_iff _ _).1 h2))`. Unfold `GlobalTheory.StdPairCone.stdA GlobalTheory.StdPairCone.unitInd GlobalTheory.StdPairCone.IsGLO`. Simplify using `only [hb1, hb2]`. Distinguish the cases in `h : (∀ i j, M i j ∈ (ValuativeRel.valuation k).integer) ∧ ∀ i j, a ≤ i.1 → M i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)`.

Rewrite using `[if_pos h]`. Distinguish the cases in `h' : (topL a M).det ≠ 0 ∧ ValuativeRel.valuation k (topL a M).det = 1`. Rewrite using `[dif_pos h', dif_pos ⟨hd ▸ h'.1, ⟨fun i j => h.1 _ _, hd ▸ h'.2⟩, fun i j => h.2 _ _ (by simp)⟩]`. Simplify using `only [hd]`. Rewrite using `[dif_neg h', dif_neg]`.

Introduce and unpack `⟨h1, ⟨-, h2⟩, -⟩`. Conclude with `h' ⟨hd ▸ h1, hd ▸ h2⟩`. Rewrite using `[if_neg h, dif_neg]`. Introduce and unpack `⟨-, ⟨h1, -⟩, h2⟩`. Use `h ⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations.

Proceed by induction on `i using Fin.addCases with`. Consider the case `left i => exact h1 j i`. Consider the case `right i => exact hsub _ (h2 j i)`. Proceed by induction on `i using Fin.addCases with`. Consider the case `left i => intro hi`.

Conclude with `absurd i.2 (not_lt.2 hi)`. Consider the case `right i => exact fun _ => h2 j i`.
-/
private theorem fmFst_loc {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ν : kˣ →* ℂˣ) (ϖ : kˣ) (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) (c a a' d : ℕ) (hr : a + a' = d) (M : Matrix (Fin d) (Fin a) k) :
    GlobalTheory.StdPairCone.stdA ν ϖ c a a' ((Mᵀ).submatrix id (finCongr hr)) =
      if (∀ i j, M i j ∈ (ValuativeRel.valuation k).integer) ∧ ∀ i j, a ≤ i.1 → M i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) then
        GlobalTheory.StdPairCone.unitInd ν (topL a M).det else 0 := by
  subst hr
  have hb : GlobalTheory.StdPairCone.blk₁ ((Mᵀ).submatrix id (finCongr (rfl : a + a' = a + a'))) = (topL a M)ᵀ := by
    ext i j
    have : j.1 < a + a' ∧ i.1 < a := ⟨by omega, i.2⟩
    simp only [GlobalTheory.StdPairCone.blk₁, topL, Matrix.of_apply, Matrix.submatrix_apply, Matrix.transpose_apply, dif_pos this]
    rfl
  have hb2 : ∀ i j, GlobalTheory.StdPairCone.blk₂ ((Mᵀ).submatrix id (finCongr (rfl : a + a' = a + a'))) i j = M (Fin.natAdd a j) i :=
    fun i j => rfl
  have hb1 : ∀ i j, GlobalTheory.StdPairCone.blk₁ ((Mᵀ).submatrix id (finCongr (rfl : a + a' = a + a'))) i j = M (Fin.castAdd a' j) i :=
    fun i j => rfl
  have hd : (GlobalTheory.StdPairCone.blk₁ ((Mᵀ).submatrix id (finCongr (rfl : a + a' = a + a')))).det = (topL a M).det := by
    rw [hb, Matrix.det_transpose]
  have hsub : ∀ x, x ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) → x ∈ (ValuativeRel.valuation k).integer := by
    intro x hx
    have h1 : ValuativeRel.valuation k x ≤ ValuativeRel.valuation k ((ϖ ^ c : kˣ) : k) := hx
    have h2 : ((ϖ ^ c : kˣ) : k) ∈ (ValuativeRel.valuation k).integer := by
      rw [Units.val_pow_eq_pow_val]; exact pow_mem hϖ.mem c
    exact (Valuation.mem_integer_iff _ _).2 (le_trans h1 ((Valuation.mem_integer_iff _ _).1 h2))
  unfold GlobalTheory.StdPairCone.stdA GlobalTheory.StdPairCone.unitInd GlobalTheory.StdPairCone.IsGLO
  simp only [hb1, hb2]
  by_cases h : (∀ i j, M i j ∈ (ValuativeRel.valuation k).integer) ∧ ∀ i j, a ≤ i.1 → M i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)
  · rw [if_pos h]
    by_cases h' : (topL a M).det ≠ 0 ∧ ValuativeRel.valuation k (topL a M).det = 1
    · rw [dif_pos h', dif_pos ⟨hd ▸ h'.1, ⟨fun i j => h.1 _ _, hd ▸ h'.2⟩, fun i j => h.2 _ _ (by simp)⟩]
      simp only [hd]
    · rw [dif_neg h', dif_neg]
      rintro ⟨h1, ⟨-, h2⟩, -⟩
      exact h' ⟨hd ▸ h1, hd ▸ h2⟩
  · rw [if_neg h, dif_neg]
    rintro ⟨-, ⟨h1, -⟩, h2⟩
    refine h ⟨fun i j => ?_, fun i j => ?_⟩
    · induction i using Fin.addCases with
      | left i => exact h1 j i
      | right i => exact hsub _ (h2 j i)
    · induction i using Fin.addCases with
      | left i => intro hi; exact absurd i.2 (not_lt.2 hi)
      | right i => exact fun _ => h2 j i

/- English proof (translation)
Introduce `D e₀ S hS P t hP ht ν c A WW a' hr βA βW m hm`. Take `⟨G, hG⟩ : ∃ G : Matrix (Fin A.rank) (Fin A.rank) D.host.E, G = (sgn true A).gram` from `⟨_, rfl⟩`. Establish `hdet : IsUnit G.det` using `by rw [hG]; exact (Formalism.L2.Theta.gram_det_ne (sgn true A)).isUnit`. Establish `hGi : ∀ v : P, (G⁻¹.map (incA D)).map (piW (t v)) * (G.map (incA D)).map (piW (t v)) = 1` using `fun v => by`. Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]`.

Establish `hu : ∀ v : P, IsUnit ((G.map (incA D)).map (piW (t v)) * βA.1.map (piF (t v)))ᵀ` using `fun v => by`. Rewrite using `[Matrix.isUnit_transpose]`. Use `IsUnit.mul (IsUnit.of_mul_eq_one_right _ (hGi v)) ?_` and prove the remaining obligations. Use `IsUnit.of_mul_eq_one ((βA⁻¹).1.map (piF (t v))) ?_` and prove the remaining obligations. Rewrite using `[← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]`.

Use `⟨fun v => (hu v).unit, fun x => ?_⟩` and prove the remaining obligations. Establish `key : ∀ v : P, ((hu v).unit).1 * (ptO (sgn true A).gram (finCongr hr) x).map (piW (t v)) * (GlobalTheory.SplitFlip.invT (m v)).1 = (((frMapO A WW βA βW x).map (piF (t v)))ᵀ).submatrix id (finCongr hr)` using `fun v => by`. Establish `e1 : (ptO G (finCongr hr) x).map (piW (t v)) = ((Matrix.map x (piW (t v)) * (G⁻¹.map (incA D)).map (piW (t v)))ᵀ).submatrix id (finCongr hr)`. Rewrite using `[← Matrix.map_mul]`. Both sides reduce to the same expression.

Establish `e2 : (frMapO A WW βA βW x).map (piF (t v)) = (βW⁻¹).1.map (piF (t v)) * Matrix.map x (piW (t v)) * βA.1.map (piF (t v))`. Unfold `frMapO`. Rewrite using `[Matrix.map_mul, Matrix.map_mul]`. Use `congr 2`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations.

Conclude with `piF_toEAf (t v) (x i j)`. Rewrite using `[← hG, IsUnit.unit_spec, e1, e2]`. Use `fmFst_mat (finCongr hr) _ _ _ (hGi v) (βW.1.map (piF (t v))) _ ?_ (m v) (hm v) _` and prove the remaining obligations. Rewrite using `[← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hϖ : ∀ v : P, GlobalTheory.SplitFlip.IsUnif (unifAt v.1)` using `fun v => (GlobalTheory.SplitFlip.exists_isUnif (k := Fv D.host.F v)).choose_spec`.

Simplify using `only [key, fmFst_loc _ _ (hϖ _)]`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst`. Distinguish the cases in `hx : IsHalf e₀ x`. Use `swap`. Rewrite using `[if_neg hx, if_neg fun h => hx h.1]`.

Rewrite using `[if_pos hx]`. Establish `hN : ∀ i j, toEAf D e₀ * frMapO A WW βA βW x i j = frMapO A WW βA βW x i j`. Establish `h1 : toEAf D e₀ • Matrix.map x (toEAf D) = Matrix.map x (toEAf D)`. Use extensionality with `i j`. Use `show toEAf D e₀ * toEAf D (x i j) = toEAf D (x i j)`.

Rewrite using `[← map_mul, hx i j]`. Establish `h2 : toEAf D e₀ • frMapO A WW βA βW x = frMapO A WW βA βW x`. Unfold `frMapO`. Rewrite using `[← Matrix.smul_mul, ← Matrix.mul_smul, h1]`. Conclude with `fun i j => congrFun (congrFun h2 i) j`.

Generalize the expression as in `frMapO A WW βA βW x = N at hN`. Establish `hI` using `fun i j => UpperTheory.mem_intAf_and_inId_iff_splitComponents D e₀ S hS P t hP ht c (N i j) (hN i j)`. Distinguish the cases in `h : IsIntM N ∧ ∀ i j, A.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (∏ w ∈ S, w.asIdeal ^ c w) (N i j)`. Rewrite using `[if_pos ⟨hx, h⟩, UpperTheory.unitChar_idempotentSum_eq_prod_over_splitPlaces D e₀ S hS P t hP ht ν _ (topL A.rank N)]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations.

Rewrite using `[if_pos ⟨fun i j => (hI i j).1.1 (h.1 i j) v, fun i j hi => (hI i j).2.1 (h.2 i j hi) v⟩]`. Use `congr 2`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [topL, Matrix.map_apply]`. Use `split_ifs`.

Both sides reduce to the same expression. Conclude with `map_zero _`. Introduce `i j`. Simplify using `only [topL]`. Use `split_ifs`.

Conclude with `h.1 _ _`. Conclude with `zero_mem _`. Rewrite using `[if_neg fun h' => h h'.2]`. Assume the negation of the conclusion as `hne`. Establish `hv` using `fun v : P => Finset.prod_ne_zero_iff.1 (Ne.symm hne) v (Finset.mem_univ v)`.

Establish `hv'` using `fun v : P => (ite_ne_right_iff.1 (hv v)).1`. Conclude with `h ⟨fun i j => (hI i j).1.2 fun v => (hv' v).1 i j, fun i j hi => (hI i j).2.2 fun v => (hv' v).2 i j hi⟩`.
-/
theorem UpperTheory.exists_gl_stdFst_eq_product_local :
    ∀ (D : D7) (e₀ : AE D) (S : Finset (HeightOneSpectrum (𝓞 D.host.E))), IsIdemSum e₀ S →
        ∀ (P : Finset (HeightOneSpectrum (𝓞 D.host.F))) (t : ∀ v : P, D.host.E →ₐ[D.host.F] Fv D.host.F v),
        (∀ v, v ∈ P ↔ ∃ w ∈ S, w.under (𝓞 D.host.F) = v) → (∀ v : P, splitPrime (t v) ∈ S) →
        ∀ (ν : (AE D)ˣ →* Circle) (c : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (A WW : HSp D) (a' : ℕ) (hr : A.rank + a' = WW.rank)
          (βA : GL (Fin A.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D)) (m : ∀ v : P, GL (Fin (A.rank + a')) (Fv D.host.F v)),
        (∀ v, (m v).1 = (βW.1.map (piF (t v))).submatrix (finCongr hr) (finCongr hr)) →
        ∃ g : ∀ v : P, GL (Fin A.rank) (Fv D.host.F v), ∀ x : WO A WW,
          GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e₀ (∏ w ∈ S, w.asIdeal ^ c w) A WW βA βW x =
            if IsHalf e₀ x then ∏ v : P, GlobalTheory.StdPairCone.stdA (chrW ν (t v)) (unifAt v.1) (c (splitPrime (t v))) A.rank a'
              ((g v).1 * (ptO (sgn true A).gram (finCongr hr) x).map (piW (t v)) * (GlobalTheory.SplitFlip.invT (m v)).1) else 0 := by
  intro D e₀ S hS P t hP ht ν c A WW a' hr βA βW m hm
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Fin A.rank) (Fin A.rank) D.host.E, G = (sgn true A).gram := ⟨_, rfl⟩
  have hdet : IsUnit G.det := by rw [hG]; exact (Formalism.L2.Theta.gram_det_ne (sgn true A)).isUnit
  have hGi : ∀ v : P, (G⁻¹.map (incA D)).map (piW (t v)) * (G.map (incA D)).map (piW (t v)) = 1 := fun v => by
    rw [← Matrix.map_mul, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hu : ∀ v : P, IsUnit ((G.map (incA D)).map (piW (t v)) * βA.1.map (piF (t v)))ᵀ := fun v => by
    rw [Matrix.isUnit_transpose]
    refine IsUnit.mul (IsUnit.of_mul_eq_one_right _ (hGi v)) ?_
    refine IsUnit.of_mul_eq_one ((βA⁻¹).1.map (piF (t v))) ?_
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨fun v => (hu v).unit, fun x => ?_⟩
  have key : ∀ v : P, ((hu v).unit).1 * (ptO (sgn true A).gram (finCongr hr) x).map (piW (t v)) * (GlobalTheory.SplitFlip.invT (m v)).1 =
      (((frMapO A WW βA βW x).map (piF (t v)))ᵀ).submatrix id (finCongr hr) := fun v => by
    have e1 : (ptO G (finCongr hr) x).map (piW (t v)) =
        ((Matrix.map x (piW (t v)) * (G⁻¹.map (incA D)).map (piW (t v)))ᵀ).submatrix id (finCongr hr) := by
      rw [← Matrix.map_mul]; rfl
    have e2 : (frMapO A WW βA βW x).map (piF (t v)) =
        (βW⁻¹).1.map (piF (t v)) * Matrix.map x (piW (t v)) * βA.1.map (piF (t v)) := by
      unfold frMapO
      rw [Matrix.map_mul, Matrix.map_mul]
      congr 2
      refine Matrix.ext fun i j => ?_
      exact piF_toEAf (t v) (x i j)
    rw [← hG, IsUnit.unit_spec, e1, e2]
    refine fmFst_mat (finCongr hr) _ _ _ (hGi v) (βW.1.map (piF (t v))) _ ?_ (m v) (hm v) _
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hϖ : ∀ v : P, GlobalTheory.SplitFlip.IsUnif (unifAt v.1) := fun v => (GlobalTheory.SplitFlip.exists_isUnif (k := Fv D.host.F v)).choose_spec
  simp only [key, fmFst_loc _ _ (hϖ _)]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst
  by_cases hx : IsHalf e₀ x
  swap
  · rw [if_neg hx, if_neg fun h => hx h.1]
  rw [if_pos hx]
  have hN : ∀ i j, toEAf D e₀ * frMapO A WW βA βW x i j = frMapO A WW βA βW x i j := by
    have h1 : toEAf D e₀ • Matrix.map x (toEAf D) = Matrix.map x (toEAf D) := by
      ext i j
      show toEAf D e₀ * toEAf D (x i j) = toEAf D (x i j)
      rw [← map_mul, hx i j]
    have h2 : toEAf D e₀ • frMapO A WW βA βW x = frMapO A WW βA βW x := by
      unfold frMapO
      rw [← Matrix.smul_mul, ← Matrix.mul_smul, h1]
    exact fun i j => congrFun (congrFun h2 i) j
  generalize frMapO A WW βA βW x = N at hN
  have hI := fun i j => UpperTheory.mem_intAf_and_inId_iff_splitComponents D e₀ S hS P t hP ht c (N i j) (hN i j)
  by_cases h : IsIntM N ∧ ∀ i j, A.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (∏ w ∈ S, w.asIdeal ^ c w) (N i j)
  · rw [if_pos ⟨hx, h⟩, UpperTheory.unitChar_idempotentSum_eq_prod_over_splitPlaces D e₀ S hS P t hP ht ν _ (topL A.rank N)]
    · refine Finset.prod_congr rfl fun v _ => ?_
      rw [if_pos ⟨fun i j => (hI i j).1.1 (h.1 i j) v, fun i j hi => (hI i j).2.1 (h.2 i j hi) v⟩]
      congr 2
      refine Matrix.ext fun i j => ?_
      simp only [topL, Matrix.map_apply]
      split_ifs
      · rfl
      · exact map_zero _
    · intro i j
      simp only [topL]
      split_ifs
      · exact h.1 _ _
      · exact zero_mem _
  · rw [if_neg fun h' => h h'.2]
    by_contra hne
    have hv := fun v : P => Finset.prod_ne_zero_iff.1 (Ne.symm hne) v (Finset.mem_univ v)
    have hv' := fun v : P => (ite_ne_right_iff.1 (hv v)).1
    exact h ⟨fun i j => (hI i j).1.2 fun v => (hv' v).1 i j, fun i j hi => (hI i j).2.2 fun v => (hv' v).2 i j hi⟩
