import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PkLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.PiHomExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.LevLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical NumberField.AdeleRing

section Ring

variable {R : Type} [CommRing R]

private def topR (X : UPos (2 + 2) 2 → R) : Matrix (Fin 2) (Fin 2) R :=
  Matrix.of fun i j => X ⟨(Fin.castAdd 2 i, Fin.natAdd 2 j), i.2, Nat.le_add_right 2 j⟩

/- English proof (translation)
Rewrite using `[coe_unipGL]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [unipMatrix, blockEntry_apply, topR] <;> rfl`.
-/
private theorem unipGL_val (X : UPos (2 + 2) 2 → R) :
    (unipGL X : GL (Fin (2 + 2)) R).val =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 (topR X) 0 1) := by
  rw [coe_unipGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipMatrix, blockEntry_apply, topR] <;> rfl

/- English proof (translation)
Use `⟨fun p => B ⟨p.1.1, p.2.1⟩ ⟨p.1.2 - 2, by have := p.1.2.2; omega⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `[topR]`.
-/
private theorem topR_surj (B : Matrix (Fin 2) (Fin 2) R) : ∃ X : UPos (2 + 2) 2 → R, topR X = B := by
  refine ⟨fun p => B ⟨p.1.1, p.2.1⟩ ⟨p.1.2 - 2, by have := p.1.2.2; omega⟩, ?_⟩
  ext i j
  simp [topR]

/- English proof (translation)
Rewrite using `[Units.val_mul, unipGL_val]`. Simplify using `only [PositivityTheory.Rg.Tf.Adel.blk, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]`.
-/
private theorem unip_mul_blk (X : UPos (2 + 2) 2 → R) (a b : GL (Fin 2) R) :
    (unipGL X * blk a b : GL (Fin (2 + 2)) R).val =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks a.val (topR X * b.val) 0 b.val) := by
  rw [Units.val_mul, unipGL_val]
  simp only [PositivityTheory.Rg.Tf.Adel.blk, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.one_mul,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

/- English proof (translation)
Rewrite using `[Units.val_mul, unipGL_val]`. Simplify using `only [PositivityTheory.Rg.Tf.Adel.blk, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]`.
-/
private theorem blk_mul_unip (X : UPos (2 + 2) 2 → R) (a b : GL (Fin 2) R) :
    (blk a b * unipGL X : GL (Fin (2 + 2)) R).val =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks a.val (a.val * topR X) 0 b.val) := by
  rw [Units.val_mul, unipGL_val]
  simp only [PositivityTheory.Rg.Tf.Adel.blk, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.mul_one,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

/- English proof (translation)
Take `⟨X', h⟩` from `topR_surj (a.val * topR X * (b⁻¹).val)`. Use `⟨X', Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[blk_mul_unip, unip_mul_blk, h, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]`.
-/
private theorem conj_unip (X : UPos (2 + 2) 2 → R) (a b : GL (Fin 2) R) :
    ∃ X' : UPos (2 + 2) 2 → R, PositivityTheory.Rg.Tf.Adel.blk a b * unipGL X = unipGL X' * blk a b := by
  obtain ⟨X', h⟩ := topR_surj (a.val * topR X * (b⁻¹).val)
  refine ⟨X', Units.ext ?_⟩
  rw [blk_mul_unip, unip_mul_blk, h, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

/- English proof (translation)
Take `⟨X, hX⟩` from `topR_surj (Matrix.of (fun i j : Fin 2 => g.val (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j))) * (b⁻¹).val)`. Use `⟨X, Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[unip_mul_blk, hX, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]`. Use extensionality with `i j`. Take `⟨i, rfl⟩` from `(finSumFinEquiv (m := 2) (n := 2)).surjective i`.

Take `⟨j, rfl⟩` from `(finSumFinEquiv (m := 2) (n := 2)).surjective j`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;>`. Simplify using `[h₁, h₂, h₃, Matrix.reindex_apply, Matrix.submatrix_apply]`.
-/
private theorem eq_unip_blk (g : GL (Fin (2 + 2)) R) (a b : GL (Fin 2) R)
    (h₁ : ∀ i j : Fin 2, g.val (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) = a.val i j)
    (h₂ : ∀ i j : Fin 2, g.val (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)) = b.val i j)
    (h₃ : ∀ i j : Fin 2, g.val (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0) :
    ∃ X : UPos (2 + 2) 2 → R, g = unipGL X * blk a b := by
  obtain ⟨X, hX⟩ := topR_surj (Matrix.of (fun i j : Fin 2 => g.val (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j))) * (b⁻¹).val)
  refine ⟨X, Units.ext ?_⟩
  rw [unip_mul_blk, hX, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  ext i j
  obtain ⟨i, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [h₁, h₂, h₃, Matrix.reindex_apply, Matrix.submatrix_apply]

end Ring

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Take `⟨X', h⟩` from `conj_unip X ((m₁ : AdelicGLn.AdelicGL K 2) * zt K t) ((m₂ : AdelicGLn.AdelicGL K 2) * zt K (-t))`. Use `⟨X', Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.coe_mul, Subgroup.coe_mul, (blkLaws (K := K)).1, coe_unipOne, coe_unipOne, h]`.
-/
private theorem lv_nn (m₁ m₂ : G1 K 2) (t : ℝ) (X : UPos (2 + 2) 2 → 𝔸[K]) :
    ∃ X', lv (K := K) m₁ m₂ t * nn X = nn X' * lv m₁ m₂ t := by
  obtain ⟨X', h⟩ := conj_unip X ((m₁ : AdelicGLn.AdelicGL K 2) * zt K t) ((m₂ : AdelicGLn.AdelicGL K 2) * zt K (-t))
  refine ⟨X', Subtype.ext ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_mul, (blkLaws (K := K)).1, coe_unipOne, coe_unipOne, h]

/- English proof (translation)
Conclude with `Prod.ext (funext h₁) (Subtype.ext (funext h₂))`.
-/
private theorem ad_ext {x y : 𝔸[K]} (h₁ : ∀ w, infEval w x = infEval w y) (h₂ : ∀ v, finEval v x = finEval v y) : x = y := by
  exact Prod.ext (funext h₁) (Subtype.ext (funext h₂))

/- English proof (translation)
Use `show (AdelicGLn.infiniteEquiv K n (AdelicGLn.prodEquiv K n (finEmb K n x)).1) w = 1`. Rewrite using `[AutomorphicForm.prodEquiv_finEmb, map_one]`. Both sides reduce to the same expression.
-/
private theorem infAt_fin {n : ℕ} (w : InfinitePlace K) (x : AdelicGLn.FiniteAdelicGL K n) : infAt w (finEmb K n x) = 1 := by
  show (AdelicGLn.infiniteEquiv K n (AdelicGLn.prodEquiv K n (finEmb K n x)).1) w = 1
  rw [AutomorphicForm.prodEquiv_finEmb, map_one]
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem ent_inf {n : ℕ} (w : InfinitePlace K) (x : AdelicGLn.AdelicGL K n) (i j) :
    infEval w (x.val i j) = (infAt w x).val i j := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem ent_fin {n : ℕ} (v : Pl K) (x : AdelicGLn.AdelicGL K n) (i j) :
    finEval v (x.val i j) = (finAt v x).val i j := rfl

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem lev_fst (w : Pl K) (x : PW w) (i j : Fin 2) :
    (lev₂ w x).1.val i j = x.1.val (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem lev_snd (w : Pl K) (x : PW w) (i j : Fin 2) :
    (lev₂ w x).2.val i j = x.1.val (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)) := rfl

/- English proof (translation)
The claim follows from `mem_parab_iff.1 x.2 true false i j (by decide)`.
-/
private theorem par_low (w : Pl K) (x : PW w) (i j : Fin 2) :
    x.1.val (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0 :=
  mem_parab_iff.1 x.2 true false i j (by decide)

/- English proof (translation)
Take `⟨-, c₂, d₂, -⟩` from `(embEx 2 w hw).2 ι₂ h₂`. Take `⟨-, c₄, d₄, -⟩` from `(embEx (2 + 2) w hw).2 ι₄ h₄`. Establish `c₂' : ∀ (g : GS 2 w) i, finAt (w i) (finEmb K 2 (ι₂ g)) = g i` using `c₂`. Establish `d₂' : ∀ (g : GS 2 w) v, v ∉ im w → finAt v (finEmb K 2 (ι₂ g)) = 1` using `d₂`. Establish `c₄' : ∀ (g : GS (2 + 2) w) i, finAt (w i) (finEmb K (2 + 2) (ι₄ g)) = g i` using `c₄`.

Establish `d₄' : ∀ (g : GS (2 + 2) w) v, v ∉ im w → finAt v (finEmb K (2 + 2) (ι₄ g)) = 1` using `d₄`. Apply `eq_unip_blk` to reduce the goal to its premises. Introduce `i j`. Use `ad_ext (fun u => ?_) (fun v => ?_)` and prove the remaining obligations. Rewrite using `[ent_inf, ent_inf, infAt_fin, infAt_fin]`.

Simplify using `[Matrix.one_apply]`. Rewrite using `[ent_fin, ent_fin]`. Distinguish the cases in `hv : v ∈ im w`. Take `⟨i₀, -, rfl⟩` from `Finset.mem_image.1 hv`. Rewrite using `[c₄', c₂']`.

Conclude with `(lev_fst _ _ i j).symm`. Rewrite using `[d₄' _ _ hv, d₂' _ _ hv]`. Simplify using `[Matrix.one_apply]`. Introduce `i j`. Use `ad_ext (fun u => ?_) (fun v => ?_)` and prove the remaining obligations.

Rewrite using `[ent_inf, ent_inf, infAt_fin, infAt_fin]`. Simplify using `[Matrix.one_apply]`. Rewrite using `[ent_fin, ent_fin]`. Distinguish the cases in `hv : v ∈ im w`. Take `⟨i₀, -, rfl⟩` from `Finset.mem_image.1 hv`.

Rewrite using `[c₄', c₂']`. Conclude with `(lev_snd _ _ i j).symm`. Rewrite using `[d₄' _ _ hv, d₂' _ _ hv]`. Simplify using `[Matrix.one_apply]`. Introduce `i j`.

Use `ad_ext (fun u => ?_) (fun v => ?_)` and prove the remaining obligations. Rewrite using `[ent_inf, infAt_fin, map_zero]`. Simplify using `[Matrix.one_apply]`. Rewrite using `[ent_fin]`. Distinguish the cases in `hv : v ∈ im w`.

Take `⟨i₀, -, rfl⟩` from `Finset.mem_image.1 hv`. Rewrite using `[c₄', map_zero]`. Conclude with `par_low _ _ i j`. Rewrite using `[d₄' _ _ hv]`. Simplify using `[Matrix.one_apply]`.
-/
private theorem fin_dec {r : ℕ} (w : Fin r → Pl K) (ι₂ : GS 2 w →* FA K 2) (ι₄ : GS (2 + 2) w →* FA K (2 + 2))
    (hw : Function.Injective w) (h₂ : IsEmb w ι₂) (h₄ : IsEmb w ι₄) (p : ∀ i, PW (w i)) :
    ∃ X : UPos (2 + 2) 2 → 𝔸[K], finEmb K (2 + 2) (ι₄ (piIncl (fun i => PW (w i)) p)) =
      unipGL X * PositivityTheory.Rg.Tf.Adel.blk (finEmb K 2 (ι₂ fun i => (lev₂ (w i) (p i)).1)) (finEmb K 2 (ι₂ fun i => (lev₂ (w i) (p i)).2)) := by
  obtain ⟨-, c₂, d₂, -⟩ := (embEx 2 w hw).2 ι₂ h₂
  obtain ⟨-, c₄, d₄, -⟩ := (embEx (2 + 2) w hw).2 ι₄ h₄
  have c₂' : ∀ (g : GS 2 w) i, finAt (w i) (finEmb K 2 (ι₂ g)) = g i := c₂
  have d₂' : ∀ (g : GS 2 w) v, v ∉ im w → finAt v (finEmb K 2 (ι₂ g)) = 1 := d₂
  have c₄' : ∀ (g : GS (2 + 2) w) i, finAt (w i) (finEmb K (2 + 2) (ι₄ g)) = g i := c₄
  have d₄' : ∀ (g : GS (2 + 2) w) v, v ∉ im w → finAt v (finEmb K (2 + 2) (ι₄ g)) = 1 := d₄
  apply eq_unip_blk
  · intro i j
    refine ad_ext (fun u => ?_) (fun v => ?_)
    · rw [ent_inf, ent_inf, infAt_fin, infAt_fin]
      simp [Matrix.one_apply]
    · rw [ent_fin, ent_fin]
      by_cases hv : v ∈ im w
      · obtain ⟨i₀, -, rfl⟩ := Finset.mem_image.1 hv
        rw [c₄', c₂']
        exact (lev_fst _ _ i j).symm
      · rw [d₄' _ _ hv, d₂' _ _ hv]
        simp [Matrix.one_apply]
  · intro i j
    refine ad_ext (fun u => ?_) (fun v => ?_)
    · rw [ent_inf, ent_inf, infAt_fin, infAt_fin]
      simp [Matrix.one_apply]
    · rw [ent_fin, ent_fin]
      by_cases hv : v ∈ im w
      · obtain ⟨i₀, -, rfl⟩ := Finset.mem_image.1 hv
        rw [c₄', c₂']
        exact (lev_snd _ _ i j).symm
      · rw [d₄' _ _ hv, d₂' _ _ hv]
        simp [Matrix.one_apply]
  · intro i j
    refine ad_ext (fun u => ?_) (fun v => ?_)
    · rw [ent_inf, infAt_fin, map_zero]
      simp [Matrix.one_apply]
    · rw [ent_fin]
      by_cases hv : v ∈ im w
      · obtain ⟨i₀, -, rfl⟩ := Finset.mem_image.1 hv
        rw [c₄', map_zero]
        exact par_low _ _ i j
      · rw [d₄' _ _ hv]
        simp [Matrix.one_apply]

/- English proof (translation)
Take `⟨-, c, d, -⟩` from `(embEx n w hw).2 ι hι`. Establish `c' : ∀ i, finAt (w i) (finEmb K n (ι g)) = g i` using `c g`. Establish `d' : ∀ v, v ∉ im w → finAt v (finEmb K n (ι g)) = 1` using `d g`. Use `set x := finEmb K n (ι g) with hx`. Establish `hi : ∀ u : InfinitePlace K, ((AdelicGLn.det K n x : GroundTheory.Global.IdeleGroup K) : 𝔸[K]).1 u = 1` using `fun u => by`.

Establish `e : ((AdelicGLn.det K n x : GroundTheory.Global.IdeleGroup K) : 𝔸[K]).1 u = (infAt u x).val.det`. Rewrite using `[AdelicGLn.coe_det]`. Conclude with `RingHom.map_det (infEval u) _`. Rewrite using `[e, hx, infAt_fin]`. Simplify using the standard rewrite rules.

Establish `hf : ∀ v : Pl K, ((AdelicGLn.det K n x : GroundTheory.Global.IdeleGroup K) : 𝔸[K]).2 v = (finAt v x).val.det` using `fun v => by`. Rewrite using `[AdelicGLn.coe_det]`. Conclude with `RingHom.map_det (finEval v) _`. Establish `hs : Function.mulSupport (fun v : Pl K => ‖(finAt v x).val.det‖) ⊆ ((im w : Finset (Pl K)) : Set (Pl K))`. Introduce `v hv`.

Assume the negation of the conclusion as `hn`. Apply `hv` to reduce the goal to its premises. Simplify `hn)]` using `[d' v (by simpa`. Rewrite using `[detModule, MonoidHom.comp_apply, GroundTheory.Global.IdeleGroup.ideleModule_eq]`. Simplify using `only [hi, hf, norm_one, one_pow, Finset.prod_const_one, one_mul]`.

Rewrite using `[finprod_eq_prod_of_mulSupport_subset _ hs, Finset.prod_image fun a _ b _ h => hw h]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[c']`. Conclude with `((GlobalTheory.CompletionNorm.norm_nabs_valuation K (w i)).1 (Matrix.GeneralLinearGroup.det (g i))).1`.
-/
private theorem mod_S {n r : ℕ} (w : Fin r → Pl K) (ι : GS n w →* FA K n) (hw : Function.Injective w) (hι : IsEmb w ι) (g : GS n w) :
    (detModule K n (finEmb K n (ι g)) : ℝ) =
      ∏ i, GlobalTheory.SplitWeil.nabs ((w i).adicCompletion K) (Matrix.GeneralLinearGroup.det (g i)) := by
  obtain ⟨-, c, d, -⟩ := (embEx n w hw).2 ι hι
  have c' : ∀ i, finAt (w i) (finEmb K n (ι g)) = g i := c g
  have d' : ∀ v, v ∉ im w → finAt v (finEmb K n (ι g)) = 1 := d g
  set x := finEmb K n (ι g) with hx
  have hi : ∀ u : InfinitePlace K, ((AdelicGLn.det K n x : GroundTheory.Global.IdeleGroup K) : 𝔸[K]).1 u = 1 := fun u => by
    have e : ((AdelicGLn.det K n x : GroundTheory.Global.IdeleGroup K) : 𝔸[K]).1 u = (infAt u x).val.det := by
      rw [AdelicGLn.coe_det]
      exact RingHom.map_det (infEval u) _
    rw [e, hx, infAt_fin]
    simp
  have hf : ∀ v : Pl K, ((AdelicGLn.det K n x : GroundTheory.Global.IdeleGroup K) : 𝔸[K]).2 v = (finAt v x).val.det := fun v => by
    rw [AdelicGLn.coe_det]
    exact RingHom.map_det (finEval v) _
  have hs : Function.mulSupport (fun v : Pl K => ‖(finAt v x).val.det‖) ⊆ ((im w : Finset (Pl K)) : Set (Pl K)) := by
    intro v hv
    by_contra hn
    apply hv
    simp [d' v (by simpa using hn)]
  rw [detModule, MonoidHom.comp_apply, GroundTheory.Global.IdeleGroup.ideleModule_eq]
  simp only [hi, hf, norm_one, one_pow, Finset.prod_const_one, one_mul]
  rw [finprod_eq_prod_of_mulSupport_subset _ hs, Finset.prod_image fun a _ b _ h => hw h]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [c']
  exact ((GlobalTheory.CompletionNorm.norm_nabs_valuation K (w i)).1 (Matrix.GeneralLinearGroup.det (g i))).1

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Take `⟨i, rfl⟩` from `(finSumFinEquiv (m := 2) (n := 2)).surjective i`. Take `⟨j, rfl⟩` from `(finSumFinEquiv (m := 2) (n := 2)).surjective j`. Rewrite using `[scalarUnits_apply, scalarUnits_apply]`.

Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;>`. Simplify using `[PositivityTheory.Rg.Tf.Adel.blk, diagUnits, Matrix.diagonal_apply]`.
-/
private theorem scal_blk (u : GroundTheory.Global.IdeleGroup K) :
    scalarUnits K (2 + 2) u = PositivityTheory.Rg.Tf.Adel.blk (scalarUnits K 2 u) (scalarUnits K 2 u) := by
  apply Units.ext
  ext i j
  obtain ⟨i, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective j
  rw [scalarUnits_apply, scalarUnits_apply]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [PositivityTheory.Rg.Tf.Adel.blk, diagUnits, Matrix.diagonal_apply]

/- English proof (translation)
Establish `e : rpowHom (((2 + 2 : ℕ) * Module.finrank ℚ K : ℝ))⁻¹ (s * s) = rpowHom ((2 * Module.finrank ℚ K : ℝ))⁻¹ s`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `hd : (Module.finrank ℚ K : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 Module.finrank_pos.ne'`. Express the relevant statement in the definitionally equal form `(s.1 * s.1) ^ _ = s.1 ^ _`. Rewrite using `[Real.mul_rpow s.2.le s.2.le, ← Real.rpow_add s.2]`.

Use `congr 1`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Evaluate the numerical expressions. Simplify using `only [centralSection, MonoidHom.comp_apply]`.

Rewrite using `[e, scal_blk]`. Both sides reduce to the same expression.
-/
private theorem cen_blk (s : {r : ℝ // 0 < r}) :
    centralSection K (2 + 2) (s * s) = PositivityTheory.Rg.Tf.Adel.blk (centralSection K 2 s) (centralSection K 2 s) := by
  have e : rpowHom (((2 + 2 : ℕ) * Module.finrank ℚ K : ℝ))⁻¹ (s * s) = rpowHom ((2 * Module.finrank ℚ K : ℝ))⁻¹ s := by
    apply Subtype.ext
    have hd : (Module.finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
    change (s.1 * s.1) ^ _ = s.1 ^ _
    rw [Real.mul_rpow s.2.le s.2.le, ← Real.rpow_add s.2]
    congr 1
    push_cast
    field_simp
    norm_num
  simp only [centralSection, MonoidHom.comp_apply]
  rw [e, scal_blk]
  rfl

/- English proof (translation)
Establish `e : leviProj (w.adicCompletion K) (two (stdSum (rfl : 2 + 2 = 2 + 2))) x = leviTwo (w.adicCompletion K) (Fin 2) (Fin 2) (lev₂ w x)` using `((leviTwo (w.adicCompletion K) (Fin 2) (Fin 2)).apply_symm_apply _).symm`. Rewrite using `[dl, MonoidHom.comp_apply, e, deltaHalf_two, Units.val_mul, val_absPow, val_absPow]`. Establish `h₁ : (((Fintype.card (Fin 2) : ℕ) : ℂ) / 2) = 1` using `by simp`. Establish `h₂ : (-((Fintype.card (Fin 2) : ℕ) : ℂ) / 2) = -1` using `by simp`. Rewrite using `[h₁, h₂, Complex.cpow_one, Complex.cpow_neg_one, Complex.ofReal_div, div_eq_mul_inv]`.
-/
private theorem dl_val (w : Pl K) (x : PW w) :
    ((dl w x : ℂˣ) : ℂ) =
      ((GlobalTheory.SplitWeil.nabs (w.adicCompletion K) (Matrix.GeneralLinearGroup.det (lev₂ w x).1) /
        GlobalTheory.SplitWeil.nabs (w.adicCompletion K) (Matrix.GeneralLinearGroup.det (lev₂ w x).2) : ℝ) : ℂ) := by
  have e : leviProj (w.adicCompletion K) (two (stdSum (rfl : 2 + 2 = 2 + 2))) x =
      leviTwo (w.adicCompletion K) (Fin 2) (Fin 2) (lev₂ w x) :=
    ((leviTwo (w.adicCompletion K) (Fin 2) (Fin 2)).apply_symm_apply _).symm
  rw [dl, MonoidHom.comp_apply, e, deltaHalf_two, Units.val_mul, val_absPow, val_absPow]
  have h₁ : (((Fintype.card (Fin 2) : ℕ) : ℂ) / 2) = 1 := by simp
  have h₂ : (-((Fintype.card (Fin 2) : ℕ) : ℂ) / 2) = -1 := by simp
  rw [h₁, h₂, Complex.cpow_one, Complex.cpow_neg_one, Complex.ofReal_div, div_eq_mul_inv]

/- English proof (translation)
Introduce `K _ _ r w ι₂ ι₄ hw h₂ h₄`. Use `⟨lv_nn, fun p => ?_⟩` and prove the remaining obligations. Take `⟨X, hX⟩` from `fin_dec w ι₂ ι₄ hw h₂ h₄ p`. Establish `hmA` using `mod_S w ι₂ hw h₂ fun i => (lev₂ (w i) (p i)).1`. Establish `hmD` using `mod_S w ι₂ hw h₂ fun i => (lev₂ (w i) (p i)).2`.

Use `set a := ι₂ fun i => (lev₂ (w i) (p i)).1 with ha`. Use `set b := ι₂ fun i => (lev₂ (w i) (p i)).2 with hb`. Use `set A := finEmb K 2 a with hA`. Use `set D := finEmb K 2 b with hD`. Use `set α := detModule K 2 A with hα`.

Use `set δ := detModule K 2 D with hδ`. Use `set t : ℝ := (Real.log α.1 - Real.log δ.1) / 2 with ht`. Set `s : {r : ℝ // 0 < r}` to `⟨Real.exp ((Real.log α.1 + Real.log δ.1) / 2), Real.exp_pos _⟩`. Set `e : {r : ℝ // 0 < r}` to `⟨Real.exp t, Real.exp_pos _⟩`. Set `e' : {r : ℝ // 0 < r}` to `⟨Real.exp (-t), Real.exp_pos _⟩`.

Establish `hse : α = s * e` using `Subtype.ext (by`. Express the relevant statement in the definitionally equal form `α.1 = Real.exp _ * Real.exp _`. Rewrite using `[← Real.exp_add, ht, show (Real.log α.1 + Real.log δ.1) / 2 + (Real.log α.1 - Real.log δ.1) / 2 = Real.log α.1 by ring, Real.exp_log α.2])`. Establish `hse' : δ = s * e'` using `Subtype.ext (by`. Express the relevant statement in the definitionally equal form `δ.1 = Real.exp _ * Real.exp _`.

Rewrite using `[← Real.exp_add, ht, show (Real.log α.1 + Real.log δ.1) / 2 + -((Real.log α.1 - Real.log δ.1) / 2) = Real.log δ.1 by ring, Real.exp_log δ.2])`. Establish `hee : e * e' = 1` using `Subtype.ext (by`. Express the relevant statement in the definitionally equal form `Real.exp _ * Real.exp _ = 1`. Rewrite using `[← Real.exp_add, add_neg_cancel, Real.exp_zero])`. Establish `hdet : detModule K (2 + 2) (finEmb K (2 + 2) (ι₄ (piIncl (fun i => PW (w i)) p))) = s * s`.

Establish `hu : detModule K (2 + 2) (unipGL X) = 1`. Use `mem_normOneGL_iff_detModule.1 (unipOne K (2 + 2) 2 X).2` as an intermediate fact. Rewrite `this` using `[coe_unipOne]`. Then use the resulting hypothesis. Establish `hbl` using `(blkLaws (K := K)).2.2.2.2.1 A D`. Rewrite using `[hX, map_mul, hu, one_mul, hbl, ← hα, ← hδ, hse, hse']`.

Combine the equalities or inequalities in the displayed calculation. Use `⟨X, t, Subtype.ext ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : ((fin1 (ι₄ (piIncl (fun i => PW (w i)) p)) : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) = finEmb K (2 + 2) (ι₄ (piIncl (fun i => PW (w i)) p)) * (centralSection K (2 + 2) (s * s))⁻¹`. Rewrite using `[← hdet]`. Both sides reduce to the same expression.

Establish `hz : ∀ α' u e'' : {r : ℝ // 0 < r}, u * e'' = α' → (centralSection K 2 α')⁻¹ * centralSection K 2 e'' = centralSection K 2 u⁻¹`. Introduce `α' u e'' hu`. Rewrite using `[← map_inv, ← map_mul, ← hu, mul_inv, mul_assoc, inv_mul_cancel, mul_one]`. Establish `b₁ : (((blocks ι₂ p).1 : G1 K 2) : AdelicGLn.AdelicGL K 2) = A * (centralSection K 2 α)⁻¹` using `rfl`. Establish `b₂ : (((blocks ι₂ p).2 : G1 K 2) : AdelicGLn.AdelicGL K 2) = D * (centralSection K 2 δ)⁻¹` using `rfl`.

Establish `z₁ : zt K t = centralSection K 2 e` using `rfl`. Establish `z₂ : zt K (-t) = centralSection K 2 e'` using `rfl`. Rewrite using `[Subgroup.coe_mul, coe_unipOne, (blkLaws (K := K)).1, h1, hX, b₁, b₂, z₁, z₂, mul_assoc A, mul_assoc D, hz α s e hse.symm, hz δ s e' hse'.symm, ← map_inv, mul_inv, cen_blk, mul_assoc, (blkLaws (K := K)).2.2.2.2.2.1]`. Establish `hd : ((dS w p : ℂˣ) : ℂ) = ((α.1 / δ.1 : ℝ) : ℂ)`. Rewrite using `[dS, MonoidHom.finset_prod_apply, Units.coe_prod]`.

Simplify using `only [MonoidHom.comp_apply, Pi.evalMonoidHom_apply, dl_val]`. Rewrite using `[← Complex.ofReal_prod, Finset.prod_div_distrib, ← hmA, ← hmD]`. Rewrite using `[hd, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul, ← Complex.ofReal_exp]`. Use `congr 1`. Rewrite using `[ht, show (2 : ℝ) * ((Real.log α.1 - Real.log δ.1) / 2) = Real.log α.1 - Real.log δ.1 by ring, Real.exp_sub, Real.exp_log α.2, Real.exp_log δ.2]`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.parLaw :
    ∀ {K : Type} [Field K] [NumberField K] {r : ℕ} (w : Fin r → Pl K) (ι₂ : GS 2 w →* FA K 2) (ι₄ : GS (2 + 2) w →* FA K (2 + 2)), Function.Injective w → IsEmb w ι₂ → IsEmb w ι₄ →
      (∀ m₁ m₂ t X, ∃ X', lv (K := K) m₁ m₂ t * nn X = nn X' * lv m₁ m₂ t) ∧
      ∀ p : ∀ i, PW (w i), ∃ X t, fin1 (ι₄ (piIncl (fun i => PW (w i)) p)) = nn X * lv (blocks ι₂ p).1 (blocks ι₂ p).2 t ∧ Complex.exp (2 * (t : ℂ)) = (dS w p : ℂ) := by
  intro K _ _ r w ι₂ ι₄ hw h₂ h₄
  refine ⟨lv_nn, fun p => ?_⟩
  obtain ⟨X, hX⟩ := fin_dec w ι₂ ι₄ hw h₂ h₄ p
  have hmA := mod_S w ι₂ hw h₂ fun i => (lev₂ (w i) (p i)).1
  have hmD := mod_S w ι₂ hw h₂ fun i => (lev₂ (w i) (p i)).2
  set a := ι₂ fun i => (lev₂ (w i) (p i)).1 with ha
  set b := ι₂ fun i => (lev₂ (w i) (p i)).2 with hb
  set A := finEmb K 2 a with hA
  set D := finEmb K 2 b with hD
  set α := detModule K 2 A with hα
  set δ := detModule K 2 D with hδ
  set t : ℝ := (Real.log α.1 - Real.log δ.1) / 2 with ht
  let s : {r : ℝ // 0 < r} := ⟨Real.exp ((Real.log α.1 + Real.log δ.1) / 2), Real.exp_pos _⟩
  let e : {r : ℝ // 0 < r} := ⟨Real.exp t, Real.exp_pos _⟩
  let e' : {r : ℝ // 0 < r} := ⟨Real.exp (-t), Real.exp_pos _⟩
  have hse : α = s * e := Subtype.ext (by
    change α.1 = Real.exp _ * Real.exp _
    rw [← Real.exp_add, ht, show (Real.log α.1 + Real.log δ.1) / 2 + (Real.log α.1 - Real.log δ.1) / 2 = Real.log α.1 by ring,
      Real.exp_log α.2])
  have hse' : δ = s * e' := Subtype.ext (by
    change δ.1 = Real.exp _ * Real.exp _
    rw [← Real.exp_add, ht, show (Real.log α.1 + Real.log δ.1) / 2 + -((Real.log α.1 - Real.log δ.1) / 2) = Real.log δ.1 by ring,
      Real.exp_log δ.2])
  have hee : e * e' = 1 := Subtype.ext (by
    change Real.exp _ * Real.exp _ = 1
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero])
  have hdet : detModule K (2 + 2) (finEmb K (2 + 2) (ι₄ (piIncl (fun i => PW (w i)) p))) = s * s := by
    have hu : detModule K (2 + 2) (unipGL X) = 1 := by
      have := mem_normOneGL_iff_detModule.1 (unipOne K (2 + 2) 2 X).2
      rwa [coe_unipOne] at this
    have hbl := (blkLaws (K := K)).2.2.2.2.1 A D
    rw [hX, map_mul, hu, one_mul, hbl, ← hα, ← hδ, hse, hse']
    calc s * e * (s * e') = s * s * (e * e') := by ac_rfl
      _ = s * s := by rw [hee, mul_one]
  refine ⟨X, t, Subtype.ext ?_, ?_⟩
  · have h1 : ((fin1 (ι₄ (piIncl (fun i => PW (w i)) p)) : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) =
        finEmb K (2 + 2) (ι₄ (piIncl (fun i => PW (w i)) p)) * (centralSection K (2 + 2) (s * s))⁻¹ := by
      rw [← hdet]; rfl
    have hz : ∀ α' u e'' : {r : ℝ // 0 < r}, u * e'' = α' →
        (centralSection K 2 α')⁻¹ * centralSection K 2 e'' = centralSection K 2 u⁻¹ := by
      intro α' u e'' hu
      rw [← map_inv, ← map_mul, ← hu, mul_inv, mul_assoc, inv_mul_cancel, mul_one]
    have b₁ : (((blocks ι₂ p).1 : G1 K 2) : AdelicGLn.AdelicGL K 2) = A * (centralSection K 2 α)⁻¹ := rfl
    have b₂ : (((blocks ι₂ p).2 : G1 K 2) : AdelicGLn.AdelicGL K 2) = D * (centralSection K 2 δ)⁻¹ := rfl
    have z₁ : zt K t = centralSection K 2 e := rfl
    have z₂ : zt K (-t) = centralSection K 2 e' := rfl
    rw [Subgroup.coe_mul, coe_unipOne, (blkLaws (K := K)).1, h1, hX, b₁, b₂, z₁, z₂, mul_assoc A, mul_assoc D,
      hz α s e hse.symm, hz δ s e' hse'.symm, ← map_inv, mul_inv, cen_blk, mul_assoc,
      (blkLaws (K := K)).2.2.2.2.2.1]
  · have hd : ((dS w p : ℂˣ) : ℂ) = ((α.1 / δ.1 : ℝ) : ℂ) := by
      rw [dS, MonoidHom.finset_prod_apply, Units.coe_prod]
      simp only [MonoidHom.comp_apply, Pi.evalMonoidHom_apply, dl_val]
      rw [← Complex.ofReal_prod, Finset.prod_div_distrib, ← hmA, ← hmD]
    rw [hd, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul, ← Complex.ofReal_exp]
    congr 1
    rw [ht, show (2 : ℝ) * ((Real.log α.1 - Real.log δ.1) / 2) = Real.log α.1 - Real.log δ.1 by ring, Real.exp_sub,
      Real.exp_log α.2, Real.exp_log δ.2]
