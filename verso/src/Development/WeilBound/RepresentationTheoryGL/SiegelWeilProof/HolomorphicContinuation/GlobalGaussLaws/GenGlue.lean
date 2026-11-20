import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenUnit
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenInf
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin

noncomputable section

open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.AdelicU GlobalTheory.StdUnn IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PositivityTheory.Rg.Sw.Glob.GenGlueH

variable {D : D7} {n : ℕ}

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul a e => rfl`.
-/
theorem compAt_sigR (v : GlobalTheory.FinPl.Pl D) (z : AE D) :
    GlobalTheory.FinPl.compAt D v (sigR (AF D.host.F) D.sp.cm.sig z) =
      sigR (Fv D.host.F v) D.sp.cm.sig (GlobalTheory.FinPl.compAt D v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e => rfl

/- English proof (translation)
Apply the tactic sequence `obtain ⟨s, -, hs⟩ := GenUnitH.glueEntry z hz`. Use `⟨Formalism.IndefR.Eqv.glueA D (Formalism.IndefR.Eqv.splitInv D f) (finPart D s), fun τ => Formalism.IndefR.Eqv.psiT_glueA D τ f _, fun v => ?_⟩` and prove the remaining obligations. Use `show GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v (finPart D _) = _`. Rewrite using `[Formalism.IndefR.Eqv.finPart_glueA]`. Conclude with `hs v`.
-/
theorem glueFull (f : D.what₂.Tau → ℂ) (z : ∀ v : GlobalTheory.FinPl.Pl D, Ev D v)
    (hz : ∀ v, z v ∈ intLoc D.host.F D.host.E v) :
    ∃ x : AE D, (∀ τ, Formalism.IndefR.Eqv.psiT D τ x = f τ) ∧ ∀ v, GlobalTheory.FinPl.compAt D v x = z v := by
  obtain ⟨s, -, hs⟩ := GenUnitH.glueEntry z hz
  refine ⟨Formalism.IndefR.Eqv.glueA D (Formalism.IndefR.Eqv.splitInv D f) (finPart D s),
    fun τ => Formalism.IndefR.Eqv.psiT_glueA D τ f _, fun v => ?_⟩
  show GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v (finPart D _) = _
  rw [Formalism.IndefR.Eqv.finPart_glueA]
  exact hs v

/- English proof (translation)
Use `symm`. Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[← Matrix.map_mul, Matrix.mul_nonsing_inv M h, Matrix.map_one _ (map_zero f) (map_one f)]`.
-/
theorem map_inv_of {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (M : Matrix (Fin n) (Fin n) R)
    (h : IsUnit M.det) : (M⁻¹).map f = (M.map f)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv M h, Matrix.map_one _ (map_zero f) (map_one f)]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [GlobalTheory.MixModel.adj, Matrix.map_apply, Matrix.transpose_apply]`. Conclude with `hf _`.
-/
theorem adj_map {S : Type} [CommRing S] (f : AE D →+* S) (σS : S →+* S)
    (hf : ∀ z, f (sigR (AF D.host.F) D.sp.cm.sig z) = σS (f z)) (x : Matrix (Fin n) (Fin n) (AE D)) :
    (GlobalTheory.MixModel.adj x).map f = ((x.map f).map σS)ᵀ := by
  ext i j
  simp only [GlobalTheory.MixModel.adj, Matrix.map_apply, Matrix.transpose_apply]
  exact hf _

/- English proof (translation)
Take `⟨-, z', -, hz⟩` from `h`. Conclude with `⟨⟨z, z', hz, by rw [mul_comm]; exact hz⟩, rfl⟩`.
-/
theorem isUnit_of_intUnit {v : GlobalTheory.FinPl.Pl D} {z : Ev D v} (h : IsIntUnit z) : IsUnit z := by
  obtain ⟨-, z', -, hz⟩ := h
  exact ⟨⟨z, z', hz, by rw [mul_comm]; exact hz⟩, rfl⟩

end PositivityTheory.Rg.Sw.Glob.GenGlueH

namespace PositivityTheory.Rg.Sw.Glob

open GenGlueH

/- English proof (translation)
Introduce `D n a hint hdet`. Establish `hE : ∀ i j, ∃ x : AE D, (∀ τ, Formalism.IndefR.Eqv.psiT D τ x = (1 : Matrix (Fin n) (Fin n) ℂ) i j) ∧ ∀ v, GlobalTheory.FinPl.compAt D v x = a v i j` using `fun i j => glueFull _ (fun v => a v i j) (fun v => hint v i j)`. Use `choose A hAτ hAv using hE`. Set `A' : Matrix (Fin n) (Fin n) (AE D)` to `Matrix.of A`. Establish `hτ : ∀ τ, A'.map (Formalism.IndefR.Eqv.psiT D τ) = 1` using `fun τ => by ext i j; exact hAτ i j τ`.

Establish `hv : ∀ v, A'.map (GlobalTheory.FinPl.compAt D v) = a v` using `fun v => by ext i j; exact hAv i j v`. Establish `hdetA : IsUnit A'.det`. Apply `unitAE D` to reduce the goal to its premises. Introduce `τ`. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, hτ τ, Matrix.det_one]`.

Conclude with `one_ne_zero`. Introduce `v`. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, hv v]`. Conclude with `hdet v`. Set `u : GL (Fin n) (AE D)` to `((Matrix.isUnit_iff_isUnit_det A').2 hdetA).unit`.

Establish `hu : (u : Matrix (Fin n) (Fin n) (AE D)) = A'` using `IsUnit.unit_spec _`. Establish `hui : ((u⁻¹ : GL (Fin n) (AE D)) : Matrix (Fin n) (Fin n) (AE D)) = A'⁻¹`. Rewrite using `[Matrix.coe_units_inv, hu]`. Take `⟨m, hm⟩` from `GlobalTheory.StdUnn.Model.exists_levi u`. Use `⟨m, Or.inr (Or.inl ⟨_, _, hm⟩), fun v => ?_, fun τ => ?_⟩` and prove the remaining obligations.

Rewrite using `[show cTv (a v) = ((a v).map (sigR (Fv D.host.F v) D.sp.cm.sig))ᵀ from rfl, hm, PlaceFactsH.block_matrix_map, hu, hv v, hui, adj_map (GlobalTheory.FinPl.compAt D v) (sigR (Fv D.host.F v) D.sp.cm.sig) (compAt_sigR v), map_inv_of (GlobalTheory.FinPl.compAt D v) A' hdetA, hv v, map_ …`. Rewrite using `[hm, PlaceFactsH.block_matrix_map, hu, hτ τ, hui, adj_map (Formalism.IndefR.Eqv.psiT D τ) (starRingEnd ℂ) (fun z => Formalism.IndefR.Eqv.psiT_sigR D τ z), map_inv_of (Formalism.IndefR.Eqv.psiT D τ) A' hdetA, hτ τ, inv_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpo …`.
-/
theorem glueLevi : GlueLevi := by
  intro D n a hint hdet
  have hE : ∀ i j, ∃ x : AE D, (∀ τ, Formalism.IndefR.Eqv.psiT D τ x = (1 : Matrix (Fin n) (Fin n) ℂ) i j) ∧
      ∀ v, GlobalTheory.FinPl.compAt D v x = a v i j := fun i j => glueFull _ (fun v => a v i j) (fun v => hint v i j)
  choose A hAτ hAv using hE
  let A' : Matrix (Fin n) (Fin n) (AE D) := Matrix.of A
  have hτ : ∀ τ, A'.map (Formalism.IndefR.Eqv.psiT D τ) = 1 := fun τ => by ext i j; exact hAτ i j τ
  have hv : ∀ v, A'.map (GlobalTheory.FinPl.compAt D v) = a v := fun v => by ext i j; exact hAv i j v
  have hdetA : IsUnit A'.det := by
    apply unitAE D
    · intro τ
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hτ τ, Matrix.det_one]
      exact one_ne_zero
    · intro v
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hv v]
      exact hdet v
  let u : GL (Fin n) (AE D) := ((Matrix.isUnit_iff_isUnit_det A').2 hdetA).unit
  have hu : (u : Matrix (Fin n) (Fin n) (AE D)) = A' := IsUnit.unit_spec _
  have hui : ((u⁻¹ : GL (Fin n) (AE D)) : Matrix (Fin n) (Fin n) (AE D)) = A'⁻¹ := by
    rw [Matrix.coe_units_inv, hu]
  obtain ⟨m, hm⟩ := GlobalTheory.StdUnn.Model.exists_levi u
  refine ⟨m, Or.inr (Or.inl ⟨_, _, hm⟩), fun v => ?_, fun τ => ?_⟩
  · rw [show cTv (a v) = ((a v).map (sigR (Fv D.host.F v) D.sp.cm.sig))ᵀ from rfl,
      hm, PlaceFactsH.block_matrix_map, hu, hv v, hui,
      adj_map (GlobalTheory.FinPl.compAt D v) (sigR (Fv D.host.F v) D.sp.cm.sig) (compAt_sigR v),
      map_inv_of (GlobalTheory.FinPl.compAt D v) A' hdetA, hv v,
      map_inv_of (sigR (Fv D.host.F v) D.sp.cm.sig) (a v) (isUnit_of_intUnit (hdet v)),
      Matrix.transpose_nonsing_inv, Matrix.map_zero _ (map_zero _)]
  · rw [hm, PlaceFactsH.block_matrix_map, hu, hτ τ, hui,
      adj_map (Formalism.IndefR.Eqv.psiT D τ) (starRingEnd ℂ) (fun z => Formalism.IndefR.Eqv.psiT_sigR D τ z),
      map_inv_of (Formalism.IndefR.Eqv.psiT D τ) A' hdetA, hτ τ, inv_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one,
      Matrix.map_zero _ (map_zero _), PlaceFactsH.block_matrix_one]

/- English proof (translation)
Introduce `D n I`. Establish `hE : ∀ i, ∃ x : AE D, (∀ τ, Formalism.IndefR.Eqv.psiT D τ x = 0) ∧ ∀ v, GlobalTheory.FinPl.compAt D v x = if i ∈ I v then 1 else 0` using `fun i => glueFull _ _ (fun v => by split_ifs; exacts [one_mem _, zero_mem _])`. Use `choose e heτ hev using hE`. Establish `hσe : ∀ i, sigR (AF D.host.F) D.sp.cm.sig (e i) = e i` using `fun i => by`. Apply `Formalism.IndefR.Eqv.ae_ext' D` to reduce the goal to its premises.

Introduce `τ`. Rewrite using `[Formalism.IndefR.Eqv.psiT_sigR, heτ, map_zero]`. Apply `GenUnitH.finExt` to reduce the goal to its premises. Introduce `v`. Use `show GlobalTheory.FinPl.compAt D v (sigR (AF D.host.F) D.sp.cm.sig (e i)) = GlobalTheory.FinPl.compAt D v (e i)`.

Rewrite using `[compAt_sigR, hev]`. Apply the tactic sequence `split_ifs <;> simp`. Set `B : Matrix (Fin n) (Fin n) (AE D)` to `Matrix.diagonal e`. Establish `hB : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) B = B`. Use extensionality with `i j`.

Simplify using `only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, B, Matrix.diagonal_apply]`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `[hσe]`. Simplify using `[h, Ne.symm h]`.

Establish `hB' : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (-B) = -B` using `by rw [GenInfH.cT_neg', hB]`. Establish `h1 : GenInfH.nEl B hB ∈ genSet D n` using `Or.inl ⟨B, GenInfH.mat_nEl B hB⟩`. Establish `h2 : GenInfH.nBarEl (-B) hB' ∈ genSet D n` using `Or.inr (Or.inr ⟨-B, GenInfH.mat_nBarEl _ _⟩)`. Use `⟨GenInfH.nEl B hB * GenInfH.nBarEl (-B) hB' * GenInfH.nEl B hB, Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure h1) (Subgroup.subset_closure h2)) (Subgroup.subset_closure h1), fun v => ?_, fun τ => ?_⟩` and prove the remaining obligations. Establish `hBv : B.map (GlobalTheory.FinPl.compAt D v) = eI (I v)`.

Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, B, Matrix.diagonal_apply, eI]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[hev]`.

Simplify using `[h]`. Use `show (blk4 1 B 0 1 * blk4 1 0 (-B) 1 * blk4 1 B 0 1).map (GlobalTheory.FinPl.compAt D v) = wIm (I v)`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, PlaceFactsH.block_matrix_map, PlaceFactsH.block_matrix_map, hBv, Matrix.map_neg _ (map_neg _), hBv, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _), GenInfH.weyl_idem _ (GenInfH.eI_mul_self _)]`. Both sides reduce to the same expression. Establish `hBτ : B.map (Formalism.IndefR.Eqv.psiT D τ) = 0`.

Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, B, Matrix.diagonal_apply, Matrix.zero_apply]`. Apply the tactic sequence `split_ifs <;> simp [heτ]`. Use `show (blk4 1 B 0 1 * blk4 1 0 (-B) 1 * blk4 1 B 0 1).map (Formalism.IndefR.Eqv.psiT D τ) = 1`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, PlaceFactsH.block_matrix_map, PlaceFactsH.block_matrix_map, hBτ, Matrix.map_neg _ (map_neg _), hBτ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _), neg_zero, PlaceFactsH.block_matrix_one, Matrix.one_mul, Matrix.one_mul]`.
-/
theorem glueW : GlueW := by
  intro D n I
  have hE : ∀ i, ∃ x : AE D, (∀ τ, Formalism.IndefR.Eqv.psiT D τ x = 0) ∧
      ∀ v, GlobalTheory.FinPl.compAt D v x = if i ∈ I v then 1 else 0 := fun i =>
    glueFull _ _ (fun v => by split_ifs; exacts [one_mem _, zero_mem _])
  choose e heτ hev using hE
  have hσe : ∀ i, sigR (AF D.host.F) D.sp.cm.sig (e i) = e i := fun i => by
    apply Formalism.IndefR.Eqv.ae_ext' D
    · intro τ
      rw [Formalism.IndefR.Eqv.psiT_sigR, heτ, map_zero]
    · apply GenUnitH.finExt
      intro v
      show GlobalTheory.FinPl.compAt D v (sigR (AF D.host.F) D.sp.cm.sig (e i)) = GlobalTheory.FinPl.compAt D v (e i)
      rw [compAt_sigR, hev]
      split_ifs <;> simp
  let B : Matrix (Fin n) (Fin n) (AE D) := Matrix.diagonal e
  have hB : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) B = B := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, B, Matrix.diagonal_apply]
    by_cases h : j = i
    · subst h; simp [hσe]
    · simp [h, Ne.symm h]
  have hB' : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (-B) = -B := by rw [GenInfH.cT_neg', hB]
  have h1 : GenInfH.nEl B hB ∈ genSet D n := Or.inl ⟨B, GenInfH.mat_nEl B hB⟩
  have h2 : GenInfH.nBarEl (-B) hB' ∈ genSet D n := Or.inr (Or.inr ⟨-B, GenInfH.mat_nBarEl _ _⟩)
  refine ⟨GenInfH.nEl B hB * GenInfH.nBarEl (-B) hB' * GenInfH.nEl B hB,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure h1) (Subgroup.subset_closure h2))
      (Subgroup.subset_closure h1), fun v => ?_, fun τ => ?_⟩
  · have hBv : B.map (GlobalTheory.FinPl.compAt D v) = eI (I v) := by
      ext i j
      simp only [Matrix.map_apply, B, Matrix.diagonal_apply, eI]
      by_cases h : i = j
      · subst h; simp [hev]
      · simp [h]
    show (blk4 1 B 0 1 * blk4 1 0 (-B) 1 * blk4 1 B 0 1).map (GlobalTheory.FinPl.compAt D v) = wIm (I v)
    rw [Matrix.map_mul, Matrix.map_mul, PlaceFactsH.block_matrix_map, PlaceFactsH.block_matrix_map, hBv,
      Matrix.map_neg _ (map_neg _), hBv, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _),
      GenInfH.weyl_idem _ (GenInfH.eI_mul_self _)]
    rfl
  · have hBτ : B.map (Formalism.IndefR.Eqv.psiT D τ) = 0 := by
      ext i j
      simp only [Matrix.map_apply, B, Matrix.diagonal_apply, Matrix.zero_apply]
      split_ifs <;> simp [heτ]
    show (blk4 1 B 0 1 * blk4 1 0 (-B) 1 * blk4 1 B 0 1).map (Formalism.IndefR.Eqv.psiT D τ) = 1
    rw [Matrix.map_mul, Matrix.map_mul, PlaceFactsH.block_matrix_map, PlaceFactsH.block_matrix_map, hBτ,
      Matrix.map_neg _ (map_neg _), hBτ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _),
      neg_zero, PlaceFactsH.block_matrix_one, Matrix.one_mul, Matrix.one_mul]

end PositivityTheory.Rg.Sw.Glob
