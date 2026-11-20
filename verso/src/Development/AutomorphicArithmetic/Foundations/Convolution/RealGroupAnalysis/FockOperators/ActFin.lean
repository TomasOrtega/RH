import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.HermAct

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F]
  [IsTotallyComplex E]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `AdeleBaseChange.finiteAdeleMap F E a.2 = 0`. Rewrite using `[ha, map_zero]`.
-/
private theorem adeleMap_snd (a : A F) (ha : a.2 = 0) : (AdeleBaseChange.adeleMap F E a).2 = 0 := by
  change AdeleBaseChange.finiteAdeleMap F E a.2 = 0
  rw [ha, map_zero]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(AdeleBaseChange.adeleMap F E u).2 + (AdeleBaseChange.adeleMap F E t).2 * (rt D.θ : A E).2 = 0`. Rewrite using `[adeleMap_snd u hu, adeleMap_snd t ht, zero_mul, add_zero]`.
-/
private theorem mkE_snd (D : Dat F E) (u t : A F) (hu : u.2 = 0) (ht : t.2 = 0) : (D.mkE u t).2 = 0 := by
  change (AdeleBaseChange.adeleMap F E u).2 + (AdeleBaseChange.adeleMap F E t).2 * (rt D.θ : A E).2 = 0
  rw [adeleMap_snd u hu, adeleMap_snd t ht, zero_mul, add_zero]

/- English proof (translation)
Simplify using `only [Dat.mkE, map_sub]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem mkE_sub (D : Dat F E) (u t u' t' : A F) :
    D.mkE (u - u') (t - t') = D.mkE u t - D.mkE u' t' := by
  simp only [Dat.mkE, map_sub]
  ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem snd_sub (a b : A E) : (a - b).2 = a.2 - b.2 := rfl

/- English proof (translation)
Take `⟨-, h2, h3, h4⟩` from `hermAct F E D`. Establish `hw : (z - z').2 = 0` using `by rw [snd_sub, h, sub_self]`. Establish `h5` using `h4 (D.co (z - z') 0) (D.co (z - z') 1) (by rw [h3]; exact hw)`. Establish `h6 : D.bar (z - z') = D.mkE (D.co (z - z') 0) (-D.co (z - z') 1)` using `by rw [← h2, h3]`. Establish `h7 : (D.bar (z - z')).2 = 0`.

Rewrite using `[h6]`. Use `mkE_snd D _ _ h5.1 ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `-(D.co (z - z') 1).2 = 0`. Rewrite using `[h5.2, neg_zero]`. Rewrite `h7` using `[map_sub, snd_sub]`.

Conclude with `sub_eq_zero.1 h7`.
-/
private theorem bar_snd (D : Dat F E) (z z' : A E) (h : z.2 = z'.2) : (D.bar z).2 = (D.bar z').2 := by
  obtain ⟨-, h2, h3, h4⟩ := hermAct F E D
  have hw : (z - z').2 = 0 := by rw [snd_sub, h, sub_self]
  have h5 := h4 (D.co (z - z') 0) (D.co (z - z') 1) (by rw [h3]; exact hw)
  have h6 : D.bar (z - z') = D.mkE (D.co (z - z') 0) (-D.co (z - z') 1) := by rw [← h2, h3]
  have h7 : (D.bar (z - z')).2 = 0 := by
    rw [h6]
    refine mkE_snd D _ _ h5.1 ?_
    change -(D.co (z - z') 1).2 = 0
    rw [h5.2, neg_zero]
  rw [map_sub, snd_sub] at h7
  exact sub_eq_zero.1 h7

/- English proof (translation)
Take `⟨-, -, -, h4⟩` from `hermAct F E D`. Establish `h5` using `h4 (a - a') (b - b') (by rw [mkE_sub, snd_sub, h, sub_self])`. Conclude with `⟨sub_eq_zero.1 h5.1, sub_eq_zero.1 h5.2⟩`.
-/
private theorem mkE_inj (D : Dat F E) (a b a' b' : A F) (h : (D.mkE a b).2 = (D.mkE a' b').2) :
    a.2 = a'.2 ∧ b.2 = b'.2 := by
  obtain ⟨-, -, -, h4⟩ := hermAct F E D
  have h5 := h4 (a - a') (b - b') (by rw [mkE_sub, snd_sub, h, sub_self])
  exact ⟨sub_eq_zero.1 h5.1, sub_eq_zero.1 h5.2⟩

end

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ D y v`. Establish `h1` using `(hermAct F E D).1 (infGL E 2 y) v`. Establish `hg : ∀ i j, pFin E ((infGL E 2 y).val i j) = (1 : Matrix (Fin 2) (Fin 2) (Af E)) i j` using `fun i j => congrArg (fun g : GL (Fin 2) (Af E) => g.val i j) (pFin_infGL y)`. Establish `hone : ∀ i j, (1 : Matrix (Fin 2) (Fin 2) (Af E)) i j = pFin E ((1 : Matrix (Fin 2) (Fin 2) (A E)) i j)`. Introduce `i j`.

Distinguish the cases in `e : i = j`. Substitute `e` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne e]`. Establish `hb : ∀ i j, pFin E (D.bar ((infGL E 2 y).val i j)) = (1 : Matrix (Fin 2) (Fin 2) (Af E)) i j`.

Introduce `i j`. Establish `e : pFin E (D.bar ((infGL E 2 y).val i j)) = pFin E (D.bar ((1 : Matrix (Fin 2) (Fin 2) (A E)) i j))` using `bar_snd D _ _ ((hg i j).trans (hone i j))`. Rewrite using `[e, hone]`. Use `congr 1`. Distinguish the cases in `e' : i = j`.

Substitute `e'` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne e']`. Establish `hm1 : (infGL E 2 y).val.map (pFin E) = 1`. Conclude with `Matrix.ext fun i j => hg i j`.

Establish `hm2 : (((infGL E 2 y).val.map D.bar)ᵀ).map (pFin E) = 1`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Use `hb j i` as an intermediate fact. Simplify using `only [Matrix.map_apply, Matrix.transpose_apply]`. Rewrite using `[this, Matrix.one_apply, Matrix.one_apply]`.

Simplify using `[eq_comm]`. Establish `hH : (D.herm (D.act (infGL E 2 y) v)).map (pFin E) = (D.herm v).map (pFin E)`. Rewrite using `[h1, Matrix.map_mul, Matrix.map_mul, hm1, hm2, one_mul, mul_one]`. Establish `e00` using `congrFun (congrFun hH 0) 0`. Establish `e01` using `congrFun (congrFun hH 0) 1`.

Establish `e11` using `congrFun (congrFun hH 1) 1`. Establish `a1` using `mkE_inj D _ _ _ _ (show (D.mkE _ 0).2 = (D.mkE _ 0).2 from e00)`. Establish `a2` using `mkE_inj D _ _ _ _ (show (D.mkE _ _).2 = (D.mkE _ _).2 from e01)`. Establish `a3` using `mkE_inj D _ _ _ _ (show (D.mkE _ 0).2 = (D.mkE _ 0).2 from e11)`. Use function extensionality and compare the values at `i`.

Use `fin_cases i`. Conclude with `a3.1`. Conclude with `a1.1`. Conclude with `a2.1`. Conclude with `a2.2`.
-/
theorem UpperTheory.ConvolutionTheory.R2.Fo.actFin :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (y : GL (Fin 2) (Cinf E)) v, finPartPi (D.act (infGL E 2 y) v) = finPartPi v := by
  intro F E _ _ _ _ _ _ _ D y v
  have h1 := (hermAct F E D).1 (infGL E 2 y) v
  have hg : ∀ i j, pFin E ((infGL E 2 y).val i j) = (1 : Matrix (Fin 2) (Fin 2) (Af E)) i j := fun i j =>
    congrArg (fun g : GL (Fin 2) (Af E) => g.val i j) (pFin_infGL y)
  have hone : ∀ i j, (1 : Matrix (Fin 2) (Fin 2) (Af E)) i j = pFin E ((1 : Matrix (Fin 2) (Fin 2) (A E)) i j) := by
    intro i j
    by_cases e : i = j
    · subst e; simp
    · simp [Matrix.one_apply_ne e]
  have hb : ∀ i j, pFin E (D.bar ((infGL E 2 y).val i j)) = (1 : Matrix (Fin 2) (Fin 2) (Af E)) i j := by
    intro i j
    have e : pFin E (D.bar ((infGL E 2 y).val i j)) = pFin E (D.bar ((1 : Matrix (Fin 2) (Fin 2) (A E)) i j)) :=
      bar_snd D _ _ ((hg i j).trans (hone i j))
    rw [e, hone]
    congr 1
    by_cases e' : i = j
    · subst e'; simp
    · simp [Matrix.one_apply_ne e']
  have hm1 : (infGL E 2 y).val.map (pFin E) = 1 := by
    exact Matrix.ext fun i j => hg i j
  have hm2 : (((infGL E 2 y).val.map D.bar)ᵀ).map (pFin E) = 1 := by
    refine Matrix.ext fun i j => ?_
    have := hb j i
    simp only [Matrix.map_apply, Matrix.transpose_apply]
    rw [this, Matrix.one_apply, Matrix.one_apply]
    simp [eq_comm]
  have hH : (D.herm (D.act (infGL E 2 y) v)).map (pFin E) = (D.herm v).map (pFin E) := by
    rw [h1, Matrix.map_mul, Matrix.map_mul, hm1, hm2, one_mul, mul_one]
  have e00 := congrFun (congrFun hH 0) 0
  have e01 := congrFun (congrFun hH 0) 1
  have e11 := congrFun (congrFun hH 1) 1
  have a1 := mkE_inj D _ _ _ _ (show (D.mkE _ 0).2 = (D.mkE _ 0).2 from e00)
  have a2 := mkE_inj D _ _ _ _ (show (D.mkE _ _).2 = (D.mkE _ _).2 from e01)
  have a3 := mkE_inj D _ _ _ _ (show (D.mkE _ 0).2 = (D.mkE _ 0).2 from e11)
  funext i
  fin_cases i
  · exact a3.1
  · exact a1.1
  · exact a2.1
  · exact a2.2
