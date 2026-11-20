import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGenKE
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.MulVecInt

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Rg.Rsw.L.LGenK

open Matrix

section Blocks

variable {R : Type} [CommRing R] {n : ℕ}

/- English proof (translation)
Establish `h : (1 : Matrix (Fin (n + n)) (Fin (n + n)) R).submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks 1 0 0 1`. Rewrite using `[Matrix.submatrix_one_equiv, Matrix.fromBlocks_one]`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show ((1 : Matrix (Fin (n + n)) (Fin (n + n)) R).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁ = 1`. Rewrite using `[h, Matrix.toBlocks_fromBlocks₁₁]`.

Use `show ((1 : Matrix (Fin (n + n)) (Fin (n + n)) R).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂ = 0`. Rewrite using `[h, Matrix.toBlocks_fromBlocks₁₂]`. Use `show ((1 : Matrix (Fin (n + n)) (Fin (n + n)) R).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0`. Rewrite using `[h, Matrix.toBlocks_fromBlocks₂₁]`. Use `show ((1 : Matrix (Fin (n + n)) (Fin (n + n)) R).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂ = 1`.

Rewrite using `[h, Matrix.toBlocks_fromBlocks₂₂]`.
-/
theorem blocks_one : bA (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 1 ∧ bB (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 0 ∧
    bC (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 0 ∧ bD (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 1 := by
  have h : (1 : Matrix (Fin (n + n)) (Fin (n + n)) R).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks 1 0 0 1 := by
    rw [Matrix.submatrix_one_equiv, Matrix.fromBlocks_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ((1 : Matrix (Fin (n + n)) (Fin (n + n)) R).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁ = 1
    rw [h, Matrix.toBlocks_fromBlocks₁₁]
  · show ((1 : Matrix (Fin (n + n)) (Fin (n + n)) R).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂ = 0
    rw [h, Matrix.toBlocks_fromBlocks₁₂]
  · show ((1 : Matrix (Fin (n + n)) (Fin (n + n)) R).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0
    rw [h, Matrix.toBlocks_fromBlocks₂₁]
  · show ((1 : Matrix (Fin (n + n)) (Fin (n + n)) R).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂ = 1
    rw [h, Matrix.toBlocks_fromBlocks₂₂]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem bC_map {S : Type} [CommRing S] (f : R →+* S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : bC (M.map f) = (bC M).map f := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem bD_map {S : Type} [CommRing S] (f : R →+* S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : bD (M.map f) = (bD M).map f := rfl

/- English proof (translation)
Rewrite using `[block_matrix_map]`. Establish `h0 : (0 : Matrix (Fin n) (Fin n) R).map f = 0` using `Matrix.map_zero _ (map_zero f)`. Establish `h1 : (1 : Matrix (Fin n) (Fin n) R).map f = 1` using `Matrix.map_one _ (map_zero f) (map_one f)`. Establish `hn : (-1 : Matrix (Fin n) (Fin n) R).map f = -1`. Rewrite using `[Matrix.map_neg _ (fun a => map_neg f a), h1]`.

Rewrite using `[h0, h1, hn]`.
-/
theorem weyl_block_matrix_map {S : Type} [CommRing S] (f : R →+* S) :
    (blk4 (0 : Matrix (Fin n) (Fin n) R) 1 (-1) 0).map f = blk4 0 1 (-1) 0 := by
  rw [block_matrix_map]
  have h0 : (0 : Matrix (Fin n) (Fin n) R).map f = 0 := Matrix.map_zero _ (map_zero f)
  have h1 : (1 : Matrix (Fin n) (Fin n) R).map f = 1 := Matrix.map_one _ (map_zero f) (map_one f)
  have hn : (-1 : Matrix (Fin n) (Fin n) R).map f = -1 := by
    rw [Matrix.map_neg _ (fun a => map_neg f a), h1]
  rw [h0, h1, hn]

end Blocks

variable {D : D7} {n : ℕ}

/- English proof (translation)
Conclude with `star_star x`.
-/
theorem sig_invol (x : D.host.E) : D.sp.cm.sig (D.sp.cm.sig x) = x := by
  exact star_star x

/- English proof (translation)
Introduce `h`. Establish `h1 : ∀ a : D.host.E, star a = a` using `fun a => by`. Use `DFunLike.congr_fun h a` as an intermediate fact. Conclude with `this`. Establish `htop : (⊥ : Subalgebra D.host.F D.host.E) = ⊤`.

Use `eq_top_iff.mpr fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.mem_bot]`. Take `⟨r, hr⟩` from `(D.sp.cm.fixed a).mp (h1 a)`. Conclude with `⟨r, hr⟩`. Establish `h2` using `Subalgebra.bot_eq_top_iff_finrank_eq_one.mp htop`.

Rewrite `h2` using `[D.sp.cm.deg2]`. Conclude with `absurd h2 (by norm_num)`.
-/
theorem sig_ne : D.sp.cm.sig ≠ AlgHom.id D.host.F D.host.E := by
  intro h
  have h1 : ∀ a : D.host.E, star a = a := fun a => by
    have := DFunLike.congr_fun h a
    exact this
  have htop : (⊥ : Subalgebra D.host.F D.host.E) = ⊤ := by
    refine eq_top_iff.mpr fun a _ => ?_
    rw [Algebra.mem_bot]
    obtain ⟨r, hr⟩ := (D.sp.cm.fixed a).mp (h1 a)
    exact ⟨r, hr⟩
  have h2 := Subalgebra.bot_eq_top_iff_finrank_eq_one.mp htop
  rw [D.sp.cm.deg2] at h2
  exact absurd h2 (by norm_num)

/- English proof (translation)
Establish `key : ((Algebra.TensorProduct.map (GlobalTheory.AdelicU.evFin D.host.F v) (AlgHom.id D.host.F D.host.E)).comp (Algebra.TensorProduct.map (AlgHom.id D.host.F (AF D.host.F)) D.sp.cm.sig)) = (Algebra.TensorProduct.map (AlgHom.id D.host.F (Fv D.host.F v)) D.sp.cm.sig).comp (Algebra.T …`. Rewrite using `[← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp]`. Simplify using `only [AlgHom.id_comp, AlgHom.comp_id]`. Conclude with `DFunLike.congr_fun key x`.
-/
private theorem cv_cA_lemma (v : Pl D) (x : AE D) :
    cv D v (cA D x) = sigR (Fv D.host.F v) D.sp.cm.sig (cv D v x) := by
  have key : ((Algebra.TensorProduct.map (GlobalTheory.AdelicU.evFin D.host.F v) (AlgHom.id D.host.F D.host.E)).comp
      (Algebra.TensorProduct.map (AlgHom.id D.host.F (AF D.host.F)) D.sp.cm.sig)) =
      (Algebra.TensorProduct.map (AlgHom.id D.host.F (Fv D.host.F v)) D.sp.cm.sig).comp
        (Algebra.TensorProduct.map (GlobalTheory.AdelicU.evFin D.host.F v) (AlgHom.id D.host.F D.host.E)) := by
    rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp]
    simp only [AlgHom.id_comp, AlgHom.comp_id]
  exact DFunLike.congr_fun key x

/- English proof (translation)
Establish `hcj : (cj (cA D) (mat g)).map (cv D v) = cj (sigR (Fv D.host.F v) D.sp.cm.sig) ((mat g).map (cv D v))`. Use extensionality with `i j`. Conclude with `cv_cA_lemma v (mat g j i)`. Establish `hJ : (Jm D n).map (cv D v) = blk4 0 1 (-1) 0` using `weyl_block_matrix_map (cv D v)`. Establish `h2` using `congrArg (fun N => N.map (cv D v)) (mat_unit g)`.

Simplify using `only [Matrix.map_mul] at h2`. Rewrite `h2` using `[hcj, hJ]`. Apply `unit_fromBlocks` to reduce the goal to its premises. Rewrite using `[block_matrix_of_blocks]`. Conclude with `h2`.
-/
theorem unit_loc (v : Pl D) (g : G D n) :
    cj (sigR (Fv D.host.F v) D.sp.cm.sig) (fromBlocks (bA ((mat g).map (cv D v))) (bB ((mat g).map (cv D v)))
        (bC ((mat g).map (cv D v))) (bD ((mat g).map (cv D v)))) * fromBlocks 0 1 (-1) 0 *
      fromBlocks (bA ((mat g).map (cv D v))) (bB ((mat g).map (cv D v))) (bC ((mat g).map (cv D v)))
        (bD ((mat g).map (cv D v))) = fromBlocks 0 1 (-1) 0 := by
  have hcj : (cj (cA D) (mat g)).map (cv D v) =
      cj (sigR (Fv D.host.F v) D.sp.cm.sig) ((mat g).map (cv D v)) := by
    ext i j
    exact cv_cA_lemma v (mat g j i)
  have hJ : (Jm D n).map (cv D v) = blk4 0 1 (-1) 0 := weyl_block_matrix_map (cv D v)
  have h2 := congrArg (fun N => N.map (cv D v)) (mat_unit g)
  simp only [Matrix.map_mul] at h2
  rw [hcj, hJ] at h2
  apply unit_fromBlocks
  rw [block_matrix_of_blocks]
  exact h2

/- English proof (translation)
Rewrite using `[RingHom.map_det, RingHom.map_add, RingHom.map_mul, bD_map, bC_map]`. Both sides reduce to the same expression.
-/
theorem det_map_u {T : Type} [CommRing T] (f : AE D →+* T) (M : Mx D (n + n) (n + n)) (X : Mx D n n) :
    f (bD M + bC M * X).det = (bD (M.map f) + bC (M.map f) * X.map f).det := by
  rw [RingHom.map_det, RingHom.map_add, RingHom.map_mul, bD_map, bC_map]
  rfl

/- English proof (translation)
Take `⟨hinf, hSv, hint⟩` from `KOff_props hk`. Establish `hloc : ∀ v, v ∉ S → ∃ x : Matrix (Fin n) (Fin n) (Fv D.host.F v ⊗[D.host.F] D.host.E), (∀ i j, x i j ∈ intLoc D.host.F D.host.E v) ∧ cj (sigR (Fv D.host.F v) D.sp.cm.sig) x = x ∧ ∃ z ∈ intLoc D.host.F D.host.E v, (bD ((mat k).map (cv D v)) + bC ((mat k).map (cv D v)) * x).det * z …` using `fun v hv => local_choice v D.sp.cm.sig sig_invol sig_ne D.sp.cm.deg2 (hS2 v hv) _ _ _ _ (fun i j => hint v hv _ _) (fun i j => hint v hv _ _) (fun i j => hint v hv _ _) (fun i j => hint v hv _ _) (unit_loc v k)`. Use `choose x hx using hloc`. Set `b : ∀ v : Pl D, Matrix (Fin n) (Fin n) (Fv D.host.F v ⊗[D.host.F] D.host.E)` to `fun v => if hv : v ∈ S then 0 else x v hv`. Establish `hb : ∀ v i j, b v i j ∈ intLoc D.host.F D.host.E v`.

Introduce `v i j`. Distinguish the cases in `hv : v ∈ S`. Simplify using `only [b, dif_pos hv]`. Conclude with `zero_mem _`. Simplify using `only [b, dif_neg hv]`.

Conclude with `(hx v hv).1 i j`. Take `⟨X, hXc, hXi⟩` from `glue_mat D b hb`. Establish `hXv : ∀ v (hv : v ∉ S), X.map (cv D v) = x v hv`. Introduce `v hv`. Use extensionality with `i j`.

Rewrite using `[Matrix.map_apply, hXc]`. Simplify using `only [b, dif_neg hv]`. Establish `hXinf : X.map (infPart D) = 0` using `by ext i j; exact hXi i j`. Establish `hz : ∀ v, ∃ z ∈ intLoc D.host.F D.host.E v, cv D v (bD (mat k) + bC (mat k) * X).det * z = 1`. Introduce `v`.

Rewrite using `[det_map_u]`. Distinguish the cases in `hv : v ∈ S`. Use `⟨1, one_mem _, ?_⟩` and prove the remaining obligations. Rewrite using `[hSv v hv, blocks_one.2.2.1, blocks_one.2.2.2]`. Simplify using the standard rewrite rules.

Rewrite using `[hXv v hv]`. Conclude with `(hx v hv).2.2`. Use `⟨X, ?_, hXinf, fun v hv => ?_, fun v hv i j => ?_, hz, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Apply `ext_comp` to reduce the goal to its premises.

Introduce `v`. Rewrite using `[cj_apply, cv_cA, hXc, hXc]`. Distinguish the cases in `hv : v ∈ S`. Simplify using `only [b, dif_pos hv, Matrix.zero_apply, map_zero]`. Simplify using `only [b, dif_neg hv]`.

Use `congrFun (congrFun (hx v hv).2.1 i) j` as an intermediate fact. Rewrite `this` using `[cj_apply]`. Conclude with `this`. Rewrite using `[cj_apply, infPart_cA, hXi, hXi, map_zero]`. Use extensionality with `i j`.

Rewrite using `[Matrix.map_apply, hXc]`. Simplify using `only [b, dif_pos hv, Matrix.zero_apply]`. Rewrite using `[hXc]`. Conclude with `hb v i j`. Use `isUnit_of_comp D _ hz ?_` and prove the remaining obligations.

Rewrite using `[det_map_u, hinf, hXinf, blocks_one.2.2.1, blocks_one.2.2.2]`. Simplify using the standard rewrite rules.
-/
theorem exists_X {S : Finset (Pl D)} (hS2 : ∀ v ∉ S, (2 : 𝓞 D.host.F) ∉ v.asIdeal) {k : G D n} (hk : k ∈ KOff D n S) :
    ∃ X : Mx D n n, cj (cA D) X = X ∧ X.map (infPart D) = 0 ∧ (∀ v ∈ S, X.map (cv D v) = 0) ∧
      (∀ v ∉ S, ∀ i j, cv D v (X i j) ∈ intLoc D.host.F D.host.E v) ∧
      (∀ v, ∃ z ∈ intLoc D.host.F D.host.E v, cv D v (bD (mat k) + bC (mat k) * X).det * z = 1) ∧
      IsUnit (bD (mat k) + bC (mat k) * X).det := by
  classical
  obtain ⟨hinf, hSv, hint⟩ := KOff_props hk
  have hloc : ∀ v, v ∉ S → ∃ x : Matrix (Fin n) (Fin n) (Fv D.host.F v ⊗[D.host.F] D.host.E),
      (∀ i j, x i j ∈ intLoc D.host.F D.host.E v) ∧ cj (sigR (Fv D.host.F v) D.sp.cm.sig) x = x ∧
      ∃ z ∈ intLoc D.host.F D.host.E v,
        (bD ((mat k).map (cv D v)) + bC ((mat k).map (cv D v)) * x).det * z = 1 := fun v hv =>
    local_choice v D.sp.cm.sig sig_invol sig_ne D.sp.cm.deg2 (hS2 v hv) _ _ _ _
      (fun i j => hint v hv _ _) (fun i j => hint v hv _ _) (fun i j => hint v hv _ _) (fun i j => hint v hv _ _)
      (unit_loc v k)
  choose x hx using hloc
  let b : ∀ v : Pl D, Matrix (Fin n) (Fin n) (Fv D.host.F v ⊗[D.host.F] D.host.E) :=
    fun v => if hv : v ∈ S then 0 else x v hv
  have hb : ∀ v i j, b v i j ∈ intLoc D.host.F D.host.E v := by
    intro v i j
    by_cases hv : v ∈ S
    · simp only [b, dif_pos hv]; exact zero_mem _
    · simp only [b, dif_neg hv]; exact (hx v hv).1 i j
  obtain ⟨X, hXc, hXi⟩ := glue_mat D b hb
  have hXv : ∀ v (hv : v ∉ S), X.map (cv D v) = x v hv := by
    intro v hv; ext i j; rw [Matrix.map_apply, hXc]; simp only [b, dif_neg hv]
  have hXinf : X.map (infPart D) = 0 := by ext i j; exact hXi i j
  have hz : ∀ v, ∃ z ∈ intLoc D.host.F D.host.E v, cv D v (bD (mat k) + bC (mat k) * X).det * z = 1 := by
    intro v
    rw [det_map_u]
    by_cases hv : v ∈ S
    · refine ⟨1, one_mem _, ?_⟩
      rw [hSv v hv, blocks_one.2.2.1, blocks_one.2.2.2]; simp
    · rw [hXv v hv]; exact (hx v hv).2.2
  refine ⟨X, ?_, hXinf, fun v hv => ?_, fun v hv i j => ?_, hz, ?_⟩
  · ext i j
    apply ext_comp
    · intro v
      rw [cj_apply, cv_cA, hXc, hXc]
      by_cases hv : v ∈ S
      · simp only [b, dif_pos hv, Matrix.zero_apply, map_zero]
      · simp only [b, dif_neg hv]
        have := congrFun (congrFun (hx v hv).2.1 i) j
        rw [cj_apply] at this
        exact this
    · rw [cj_apply, infPart_cA, hXi, hXi, map_zero]
  · ext i j; rw [Matrix.map_apply, hXc]; simp only [b, dif_pos hv, Matrix.zero_apply]
  · rw [hXc]; exact hb v i j
  · refine isUnit_of_comp D _ hz ?_
    rw [det_map_u, hinf, hXinf, blocks_one.2.2.1, blocks_one.2.2.2]; simp

end PositivityTheory.Rg.Rsw.L.LGenK
