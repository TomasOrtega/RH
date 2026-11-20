import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.JnArcFin
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
import GroundTheory.GlobalFields.Adele.IntegersLattice

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFPB

open PositivityTheory.SiegelWeilFormula.KFP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ}

/- English proof (translation)
Establish `h` using `Place.continuous_cw d w (p := Fin d.m) (q := Fin d.n)`. Unfold `RD.loc`. Use `continuous_pi fun a => continuous_pi fun j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.map_apply, Matrix.mul_apply]`. Conclude with `continuous_star.comp (continuous_finsetSum _ fun i _ => continuous_const.mul ((continuous_apply j).comp ((continuous_apply i).comp h)))`.
-/
theorem continuous_loc (R : RD d) (w : InfinitePlace F) : Continuous (fun X : Mx F E d.m d.n => R.loc w X) := by
  have h := Place.continuous_cw d w (p := Fin d.m) (q := Fin d.n)
  unfold RD.loc
  refine continuous_pi fun a => continuous_pi fun j => ?_
  simp only [Matrix.map_apply, Matrix.mul_apply]
  exact continuous_star.comp (continuous_finsetSum _ fun i _ =>
    continuous_const.mul ((continuous_apply j).comp ((continuous_apply i).comp h)))

/- English proof (translation)
Unfold `arc`. Use `(EuclideanSpace.equiv (Iw d) ℝ).symm.continuous.comp (continuous_pi fun i => ?_)` and prove the remaining obligations. Establish `h : Continuous fun X : Mx F E d.m d.n => R.loc i.1 X i.2.1 i.2.2.1` using `(continuous_apply _).comp ((continuous_apply _).comp (continuous_loc R i.1))`. Use `split_ifs`. Conclude with `Complex.continuous_re.comp h`.

Conclude with `Complex.continuous_im.comp h`.
-/
theorem continuous_arc (R : RD d) : Continuous (arc R) := by
  unfold arc
  refine (EuclideanSpace.equiv (Iw d) ℝ).symm.continuous.comp (continuous_pi fun i => ?_)
  have h : Continuous fun X : Mx F E d.m d.n => R.loc i.1 X i.2.1 i.2.2.1 :=
    (continuous_apply _).comp ((continuous_apply _).comp (continuous_loc R i.1))
  split_ifs
  · exact Complex.continuous_re.comp h
  · exact Complex.continuous_im.comp h

/- English proof (translation)
Unfold `fin`. Conclude with `continuous_pi fun k => continuous_snd.comp ((continuous_apply k).comp (KFock.continuous_crd d))`.
-/
theorem continuous_fin : Continuous (fin d) := by
  unfold fin
  exact continuous_pi fun k => continuous_snd.comp ((continuous_apply k).comp (KFock.continuous_crd d))

/- English proof (translation)
Unfold `RD.loc SD.cw`. Rewrite using `[Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.map_add _ (fun a b => star_add a b)]`. Both sides reduce to the same expression.
-/
theorem loc_add (R : RD d) (w : InfinitePlace F) (X Y : Mx F E d.m d.n) :
    R.loc w (X + Y) = R.loc w X + R.loc w Y := by
  unfold RD.loc SD.cw
  rw [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.map_add _ (fun a b => star_add a b)]
  rfl

/- English proof (translation)
Unfold `arc`. Rewrite using `[← map_add]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.add_apply, loc_add]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem arc_add' (R : RD d) (X Y : Mx F E d.m d.n) : arc R (X + Y) = arc R X + arc R Y := by
  unfold arc
  rw [← map_add]
  congr 1
  funext i
  simp only [Pi.add_apply, loc_add]
  split_ifs <;> simp

/- English proof (translation)
Apply `(InfiniteAdeleRing.ringEquiv_mixedSpace F).injective` to reduce the goal to its premises. Rewrite using `[RingEquiv.apply_symm_apply]`. Conclude with `(GroundTheory.Global.homeomorphMixedSpace F).apply_symm_apply x`.
-/
theorem homeo_symm_eq (x : mixedEmbedding.mixedSpace F) :
    (GroundTheory.Global.homeomorphMixedSpace F).symm x = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x := by
  apply (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective
  rw [RingEquiv.apply_symm_apply]
  exact (GroundTheory.Global.homeomorphMixedSpace F).apply_symm_apply x

/- English proof (translation)
Use `continuous_pi fun w => continuous_pi fun a => continuous_pi fun j => ?_` and prove the remaining obligations. Establish `: (fun u : Iw d → ℝ => zOf u w a j) = fun u => Complex.equivRealProdCLM.symm (u (w, a, j, true), u (w, a, j, false))`. Use function extensionality and compare the values at `u`. Both sides reduce to the same expression. Rewrite using `[this]`.

Conclude with `Complex.equivRealProdCLM.symm.continuous.comp ((continuous_apply _).prodMk (continuous_apply _))`.
-/
theorem continuous_zOf : Continuous (fun u : Iw d → ℝ => zOf u) := by
  refine continuous_pi fun w => continuous_pi fun a => continuous_pi fun j => ?_
  have : (fun u : Iw d → ℝ => zOf u w a j) =
      fun u => Complex.equivRealProdCLM.symm (u (w, a, j, true), u (w, a, j, false)) := by
    funext u
    rfl
  rw [this]
  exact Complex.equivRealProdCLM.symm.continuous.comp ((continuous_apply _).prodMk (continuous_apply _))

/- English proof (translation)
Use function extensionality and compare the values at `w a j`. Apply the tactic sequence `apply Complex.ext <;> simp [zOf]`.
-/
theorem zOf_add (u v : Iw d → ℝ) : zOf (u + v) = zOf u + zOf v := by
  funext w a j
  apply Complex.ext <;> simp [zOf]

/- English proof (translation)
Take `⟨L, hL⟩` from `KFock.archEquiv d R`. Set `cF : Vw d × Yf d → (Fin d.m × Fin d.n × Fin 2 → AF F)` to `fun p k => (Prod.mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (L.symm (zOf (EuclideanSpace.equiv (Iw d) ℝ p.1)) k)) (p.2 k) : AF F)`. Use `⟨cF, ?_, fun p q => ?_, fun p => ?_⟩` and prove the remaining obligations. Use `continuous_pi fun k => ?_` and prove the remaining obligations. Establish `e : (fun p : Vw d × Yf d => cF p k) = fun p => (Prod.mk ((GroundTheory.Global.homeomorphMixedSpace F).symm (L.symm (zOf (EuclideanSpace.equiv (Iw d) ℝ p.1)) k)) (p.2 k) : AF F)`.

Use function extensionality and compare the values at `p`. Simplify using `only [cF]`. Rewrite using `[homeo_symm_eq]`. Rewrite using `[e]`. Conclude with `Continuous.prodMk ((GroundTheory.Global.homeomorphMixedSpace F).symm.continuous.comp ((continuous_apply k).comp (L.symm.continuous.comp (continuous_zOf.comp ((EuclideanSpace.equiv (Iw d) ℝ).continuous.comp continuous_fst))))) ((continuous_apply k).comp continuous_snd)`.

Use function extensionality and compare the values at `k`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (L.symm (zOf (EuclideanSpace.equiv (Iw d) ℝ (p + q).1)) k) = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (L.symm (zOf (EuclideanSpace.equiv (Iw d) ℝ p.1)) k) + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (L.symm (zOf (E …`. Rewrite using `[← map_add, Prod.fst_add, map_add, zOf_add, map_add]`. Both sides reduce to the same expression.

Both sides reduce to the same expression. Use `(exists_jn R p.1 p.2).unique ⟨arc_jn R p.1 p.2, fin_jn R p.1 p.2⟩ ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[arc_eq_iff]`. Introduce `w`. Rewrite using `[← hL (cF p) w]`.

Establish `: (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (cF p k).1) = L.symm (zOf (EuclideanSpace.equiv (Iw d) ℝ p.1))`. Use function extensionality and compare the values at `k`. Conclude with `RingEquiv.apply_symm_apply _ _`. Rewrite using `[this, ContinuousLinearEquiv.apply_symm_apply]`. Use function extensionality and compare the values at `k show (d.crd (d.cmb (cF p)) k).2 = p.2 k`.

Rewrite using `[KFock.crd_cmb']`.
-/
theorem jn_eq_cmb (R : RD d) :
    ∃ cF : Vw d × Yf d → (Fin d.m × Fin d.n × Fin 2 → AF F), Continuous cF ∧
      (∀ p q, cF (p + q) = cF p + cF q) ∧ ∀ p, jn R p.1 p.2 = d.cmb (cF p) := by
  obtain ⟨L, hL⟩ := KFock.archEquiv d R
  let cF : Vw d × Yf d → (Fin d.m × Fin d.n × Fin 2 → AF F) := fun p k =>
    (Prod.mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (L.symm (zOf (EuclideanSpace.equiv (Iw d) ℝ p.1)) k))
      (p.2 k) : AF F)
  refine ⟨cF, ?_, fun p q => ?_, fun p => ?_⟩
  · refine continuous_pi fun k => ?_
    have e : (fun p : Vw d × Yf d => cF p k) = fun p =>
        (Prod.mk ((GroundTheory.Global.homeomorphMixedSpace F).symm (L.symm (zOf (EuclideanSpace.equiv (Iw d) ℝ p.1)) k))
          (p.2 k) : AF F) := by
      funext p
      simp only [cF]
      rw [homeo_symm_eq]
    rw [e]
    exact Continuous.prodMk ((GroundTheory.Global.homeomorphMixedSpace F).symm.continuous.comp ((continuous_apply k).comp
      (L.symm.continuous.comp (continuous_zOf.comp ((EuclideanSpace.equiv (Iw d) ℝ).continuous.comp continuous_fst)))))
      ((continuous_apply k).comp continuous_snd)
  · funext k
    refine Prod.ext ?_ ?_
    · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (L.symm (zOf (EuclideanSpace.equiv (Iw d) ℝ (p + q).1)) k) =
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (L.symm (zOf (EuclideanSpace.equiv (Iw d) ℝ p.1)) k) +
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (L.symm (zOf (EuclideanSpace.equiv (Iw d) ℝ q.1)) k)
      rw [← map_add, Prod.fst_add, map_add, zOf_add, map_add]
      rfl
    · rfl
  · refine (exists_jn R p.1 p.2).unique ⟨arc_jn R p.1 p.2, fin_jn R p.1 p.2⟩ ⟨?_, ?_⟩
    · rw [arc_eq_iff]
      intro w
      rw [← hL (cF p) w]
      have : (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (cF p k).1) =
          L.symm (zOf (EuclideanSpace.equiv (Iw d) ℝ p.1)) := by
        funext k
        exact RingEquiv.apply_symm_apply _ _
      rw [this, ContinuousLinearEquiv.apply_symm_apply]
    · funext k
      show (d.crd (d.cmb (cF p)) k).2 = p.2 k
      rw [KFock.crd_cmb']

def jnpE (R : RD d) : Vw d × Yf d ≃ₜ+ Mx F E d.m d.n where
  toFun p := jn R p.1 p.2
  invFun X := (arc R X, fin d X)
  left_inv p := Prod.ext (arc_jn R p.1 p.2) (fin_jn R p.1 p.2)
  right_inv X := jn_arc_fin R X
  map_add' p q := by
    obtain ⟨cF, -, hadd, heq⟩ := jn_eq_cmb R
    show jn R (p + q).1 (p + q).2 = jn R p.1 p.2 + jn R q.1 q.2
    rw [heq, heq, heq, hadd, KFock.cmb_add]
  continuous_toFun := by
    obtain ⟨cF, hc, -, heq⟩ := jn_eq_cmb R
    have : (fun p : Vw d × Yf d => jn R p.1 p.2) = fun p => d.cmb (cF p) := funext heq
    show Continuous fun p : Vw d × Yf d => jn R p.1 p.2
    rw [this]
    exact (KFock.continuous_cmb d).comp hc
  continuous_invFun := (continuous_arc R).prodMk continuous_fin

end PositivityTheory.SiegelWeilFormula.KFPB

end
