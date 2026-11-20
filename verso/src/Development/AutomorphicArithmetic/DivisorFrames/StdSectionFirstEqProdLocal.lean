import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ComplEquivEvW
import Development.AutomorphicArithmetic.DivisorFrames.MemIntAdelesAndIdealIffSplitEmbeddings
import Development.AutomorphicArithmetic.DivisorFrames.UnitCharIdempotentSumEqProdUnitInd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Rewrite using `[Matrix.det_apply']`. Conclude with `sum_mem fun σ _ => mul_mem (intCast_mem S _) (prod_mem fun i _ => h _ _)`.
-/
private theorem det_mem' {R : Type} [CommRing R] (S : Subring R) {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply']
  exact sum_mem fun σ _ => mul_mem (intCast_mem S _) (prod_mem fun i _ => h _ _)

open Classical in
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
private theorem botFst_loc {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
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
Introduce `D ε Pw hε ι _ pl τ hP hinj c ν A WW βA βW a' hk x hx`. Establish `hϖ : ∀ i, GlobalTheory.SplitFlip.IsUnif (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt (pl i))` using `fun i => (GlobalTheory.SplitFlip.exists_isUnif (k := Fv D.host.F (pl i))).choose_spec`. Simplify using `only [botFst_loc _ _ (hϖ _)]`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst`. Establish `hN : ∀ i j, toEAf D ε * frMapO A WW βA βW x i j = frMapO A WW βA βW x i j`.

Establish `h1 : toEAf D ε • Matrix.map x (toEAf D) = Matrix.map x (toEAf D)`. Use extensionality with `i j`. Use `show toEAf D ε * toEAf D (x i j) = toEAf D (x i j)`. Rewrite using `[← map_mul, hx i j]`. Establish `h2 : toEAf D ε • frMapO A WW βA βW x = frMapO A WW βA βW x`.

Unfold `frMapO`. Rewrite using `[← Matrix.smul_mul, ← Matrix.mul_smul, h1]`. Conclude with `fun i j => congrFun (congrFun h2 i) j`. Generalize the expression as in `frMapO A WW βA βW x = N at hN`. Establish `hI` using `fun i j => UpperTheory.mem_intAdeles_and_ideal_iff_splitEmbeddings D ε Pw hε ι pl τ hP hinj c (N i j) (hN i j)`.

Establish `htop : ∀ v, GlobalTheory.BotMatch.evW (τ v) (topL A.rank N).det = (topL A.rank (N.map (GlobalTheory.BotMatch.evW (τ v)))).det` using `fun v => by`. Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [topL, RingHom.mapMatrix_apply, Matrix.map_apply]`.

Use `split_ifs`. Both sides reduce to the same expression. Conclude with `map_zero _`. Distinguish the cases in `h : IsIntM N ∧ ∀ i j, A.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (∏ w ∈ Pw, w.asIdeal ^ c w) (N i j)`. Rewrite using `[if_pos ⟨hx, h⟩, UpperTheory.unitChar_idempotentSum_eq_prod_unitInd D ε Pw hε ι pl τ hP hinj ν _ (topL A.rank N)]`.

Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[if_pos ⟨fun i j => (hI i j).1.1 (h.1 i j) v, fun i j hi => (hI i j).2.1 (h.2 i j hi) v⟩, htop]`. Introduce `v`. Rewrite using `[htop]`. Use `det_mem' _ _ fun i j => ?_` and prove the remaining obligations.

Simplify using `only [topL]`. Use `split_ifs`. Conclude with `(hI _ _).1.1 (h.1 _ _) v`. Conclude with `zero_mem _`. Rewrite using `[if_neg fun h' => h h'.2]`.

Assume the negation of the conclusion as `hne`. Establish `hv` using `fun v : ι => Finset.prod_ne_zero_iff.1 (Ne.symm hne) v (Finset.mem_univ v)`. Establish `hv'` using `fun v : ι => (ite_ne_right_iff.1 (hv v)).1`. Conclude with `h ⟨fun i j => (hI i j).1.2 fun v => (hv' v).1 i j, fun i j hi => (hI i j).2.2 fun v => (hv' v).2 i j hi⟩`.
-/
theorem UpperTheory.stdSectionFirst_eq_prod_local :
    ∀ (D : D7) (ε : AE D) (Pw : Finset (Pl D.host.E)), IsIdemSum ε Pw → ∀ (ι : Type) [Fintype ι] (pl : ι → Pl D.host.F)
        (τ : ∀ i, D.host.E →ₐ[D.host.F] Fv D.host.F (pl i)), (∀ w, w ∈ Pw ↔ ∃ i, splitPrime (τ i) = w) →
        Function.Injective (fun i => splitPrime (τ i)) → ∀ (c : Pl D.host.E → ℕ) (ν : (AE D)ˣ →* Circle) (A WW : HSp D) (βA : GL (Fin A.rank) (Lev.EAf D))
          (βW : GL (Fin WW.rank) (Lev.EAf D)) (a' : ℕ) (hk : A.rank + a' = WW.rank) (x : WO A WW), IsHalf ε x →
          GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν ε (∏ w ∈ Pw, w.asIdeal ^ c w) A WW βA βW x =
            ∏ i, GlobalTheory.StdPairCone.stdA (chrW ν (τ i)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt (pl i)) (c (splitPrime (τ i))) A.rank a'
              ((((frMapO A WW βA βW x).map (GlobalTheory.BotMatch.evW (τ i)))ᵀ).submatrix id (finCongr hk)) := by
  intro D ε Pw hε ι _ pl τ hP hinj c ν A WW βA βW a' hk x hx
  classical
  have hϖ : ∀ i, GlobalTheory.SplitFlip.IsUnif (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt (pl i)) := fun i =>
    (GlobalTheory.SplitFlip.exists_isUnif (k := Fv D.host.F (pl i))).choose_spec
  simp only [botFst_loc _ _ (hϖ _)]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst
  have hN : ∀ i j, toEAf D ε * frMapO A WW βA βW x i j = frMapO A WW βA βW x i j := by
    have h1 : toEAf D ε • Matrix.map x (toEAf D) = Matrix.map x (toEAf D) := by
      ext i j
      show toEAf D ε * toEAf D (x i j) = toEAf D (x i j)
      rw [← map_mul, hx i j]
    have h2 : toEAf D ε • frMapO A WW βA βW x = frMapO A WW βA βW x := by
      unfold frMapO
      rw [← Matrix.smul_mul, ← Matrix.mul_smul, h1]
    exact fun i j => congrFun (congrFun h2 i) j
  generalize frMapO A WW βA βW x = N at hN
  have hI := fun i j => UpperTheory.mem_intAdeles_and_ideal_iff_splitEmbeddings D ε Pw hε ι pl τ hP hinj c (N i j) (hN i j)
  have htop : ∀ v, GlobalTheory.BotMatch.evW (τ v) (topL A.rank N).det = (topL A.rank (N.map (GlobalTheory.BotMatch.evW (τ v)))).det := fun v => by
    rw [RingHom.map_det]
    congr 1
    refine Matrix.ext fun i j => ?_
    simp only [topL, RingHom.mapMatrix_apply, Matrix.map_apply]
    split_ifs
    · rfl
    · exact map_zero _
  by_cases h : IsIntM N ∧ ∀ i j, A.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (∏ w ∈ Pw, w.asIdeal ^ c w) (N i j)
  · rw [if_pos ⟨hx, h⟩, UpperTheory.unitChar_idempotentSum_eq_prod_unitInd D ε Pw hε ι pl τ hP hinj ν _ (topL A.rank N)]
    · refine Finset.prod_congr rfl fun v _ => ?_
      rw [if_pos ⟨fun i j => (hI i j).1.1 (h.1 i j) v, fun i j hi => (hI i j).2.1 (h.2 i j hi) v⟩, htop]
    · intro v
      rw [htop]
      refine det_mem' _ _ fun i j => ?_
      simp only [topL]
      split_ifs
      · exact (hI _ _).1.1 (h.1 _ _) v
      · exact zero_mem _
  · rw [if_neg fun h' => h h'.2]
    by_contra hne
    have hv := fun v : ι => Finset.prod_ne_zero_iff.1 (Ne.symm hne) v (Finset.mem_univ v)
    have hv' := fun v : ι => (ite_ne_right_iff.1 (hv v)).1
    exact h ⟨fun i j => (hI i j).1.2 fun v => (hv' v).1 i j, fun i j hi => (hI i j).2.2 fun v => (hv' v).2 i j hi⟩
