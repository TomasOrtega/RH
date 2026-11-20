import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.EqAmOfBarEq

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

/- English proof (translation)
Establish `h` using `GlobalTheory.CuspRep.det_map (RingHom.fst (InfiniteAdeleRing E) (Af E)) (finGL E 2 k)`. Establish `h1 : Matrix.GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing E) (Af E)) (finGL E 2 k) = 1` using `map_cornerGL_of_zero _ _ (fun _ => rfl) k`. Rewrite `h` using `[h1]`. Use `h.symm.trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
private theorem fst_detFin {E : Type} [Field E] [NumberField E] (k : GL (Fin 2) (Af E)) :
    (((Matrix.GeneralLinearGroup.det (finGL E 2 k) : (A E)ˣ) : A E)).1 = 1 := by
  have h := GlobalTheory.CuspRep.det_map (RingHom.fst (InfiniteAdeleRing E) (Af E)) (finGL E 2 k)
  have h1 : Matrix.GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing E) (Af E)) (finGL E 2 k) = 1 :=
    map_cornerGL_of_zero _ _ (fun _ => rfl) k
  rw [h1] at h
  refine h.symm.trans ?_
  simp

/- English proof (translation)
Set `e : A F` to `((1, 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)`. Establish `h1 : am E e * (z : A E) = am E e`. Establish `hi1 : (am E e).1 = 1` using `map_one (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E))`. Establish `hi2 : (am E e).2 = 0` using `map_zero (AdeleBaseChange.finiteAdeleMap F E)`. Use `Prod.ext ?_ ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(am E e).1 * (z : A E).1 = (am E e).1`. Rewrite using `[hz, mul_one]`. Express the relevant statement in the definitionally equal form `(am E e).2 * (z : A E).2 = (am E e).2`. Rewrite using `[hi2, zero_mul]`. Establish `h2` using `congrArg D.co h1`.

Rewrite `h2` using `[D.co_am_mul, D.co_am]`. Establish `hu : e * D.co z 0 = e` using `congrFun h2 0`. Establish `ht : e * D.co z 1 = 0` using `congrFun h2 1`. Establish `hu1 : (D.co z 0).1 = 1`. Establish `h` using `congrArg Prod.fst hu`.

Express the relevant statement in the definitionally equal form `(1 : InfiniteAdeleRing F) * (D.co z 0).1 = 1 at h`. Rewrite `h` using `[one_mul]`. Then use the resulting hypothesis. Establish `ht1 : (D.co z 1).1 = 0`. Establish `h` using `congrArg Prod.fst ht`. Express the relevant statement in the definitionally equal form `(1 : InfiniteAdeleRing F) * (D.co z 1).1 = 0 at h`.

Rewrite `h` using `[one_mul]`. Then use the resulting hypothesis. Rewrite using `[D.coe_ideleNorm]`. Express the relevant statement in the definitionally equal form `(D.co z 0).1 ^ 2 - (rt D.δ : A F).1 * (D.co z 1).1 ^ 2 = 1`. Rewrite using `[hu1, ht1]`. Simplify using the standard rewrite rules.
-/
private theorem fst_norm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (D : Dat F E) (z : (A E)ˣ) (hz : (z : A E).1 = 1) :
    ((GroundTheory.Global.ideleNorm F E z : (A F)ˣ) : A F).1 = 1 := by
  let e : A F := ((1, 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  have h1 : am E e * (z : A E) = am E e := by
    have hi1 : (am E e).1 = 1 := map_one (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E))
    have hi2 : (am E e).2 = 0 := map_zero (AdeleBaseChange.finiteAdeleMap F E)
    refine Prod.ext ?_ ?_
    · change (am E e).1 * (z : A E).1 = (am E e).1
      rw [hz, mul_one]
    · change (am E e).2 * (z : A E).2 = (am E e).2
      rw [hi2, zero_mul]
  have h2 := congrArg D.co h1
  rw [D.co_am_mul, D.co_am] at h2
  have hu : e * D.co z 0 = e := congrFun h2 0
  have ht : e * D.co z 1 = 0 := congrFun h2 1
  have hu1 : (D.co z 0).1 = 1 := by
    have h := congrArg Prod.fst hu
    change (1 : InfiniteAdeleRing F) * (D.co z 0).1 = 1 at h
    rwa [one_mul] at h
  have ht1 : (D.co z 1).1 = 0 := by
    have h := congrArg Prod.fst ht
    change (1 : InfiniteAdeleRing F) * (D.co z 1).1 = 0 at h
    rwa [one_mul] at h
  rw [D.coe_ideleNorm]
  change (D.co z 0).1 ^ 2 - (rt D.δ : A F).1 * (D.co z 1).1 ^ 2 = 1
  rw [hu1, ht1]
  simp

/- English proof (translation)
Introduce `F _ _ _ π v`. Use `⟨fun f => ?_, fun x f g => rfl, ?_⟩` and prove the remaining obligations. Establish `e : {g | π.locRep v g f = f} = locGL F 2 v ⁻¹' {k | TR.finRep F 2 k f.1 = f.1}`. Use extensionality with `g`. Conclude with `Subtype.ext_iff`.

Rewrite using `[e]`. Conclude with `(π.cusp f.1 f.2).1.level.preimage (CuspSub.continuous_locGL v)`. Introduce `E _ _ _ D k f hf`. Establish `h1 : ((nu F (finGL E 2 k) : (A F)ˣ) : A F).1 = 1` using `fst_norm D _ (fst_detFin k)`. Generalize the expression as in `nu F (finGL E 2 k) = t at h1`.

Establish `hp : TR.pInf F (t : A F) = 1`. Express the relevant statement in the definitionally equal form `(TR.infEq F).symm (t : A F).1 = 1`. Rewrite using `[h1]`. Conclude with `map_one _`. Establish `hinf : Matrix.GeneralLinearGroup.map (TR.pInf F) (dM t) = 1`.

Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [dM, hp]`. Establish `hd : finGL F 2 (Matrix.GeneralLinearGroup.map (pFin F) (dM t)) = dM t`. Establish `h` using `TR.infGL_mul_finGL (dM t)`.

Rewrite `h` using `[hinf, map_one, one_mul]`. Then use the resulting hypothesis. Use `⟨_, π.stable (.fin (Matrix.GeneralLinearGroup.map (pFin F) (dM t))) f hf, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`. Express the relevant statement in the definitionally equal form `f.1 (g * finGL F 2 _) = f.1 (g * dM t)`. Rewrite using `[hd]`.
-/
theorem UpperTheory.ConvolutionTheory.R2.I.locSm :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2) (v : P F),
      (∀ f, IsOpen {g | π.locRep v g f = f}) ∧ (∀ x (f : π.V) g, (π.locRep v x f).1.1 g = f.1.1 (g * lc v x)) ∧
      ∀ (E : Type) [Field E] [NumberField E] [Algebra F E] (_ : Dat F E) (k : GL (Fin 2) (Af E)), ∀ f ∈ π.V,
        ∃ f' ∈ π.V, f'.1 = fun g => f.1 (g * dM (nu F (finGL E 2 k))) := by
  intro F _ _ _ π v
  refine ⟨fun f => ?_, fun x f g => rfl, ?_⟩
  · have e : {g | π.locRep v g f = f} = locGL F 2 v ⁻¹' {k | TR.finRep F 2 k f.1 = f.1} := by
      ext g
      exact Subtype.ext_iff
    rw [e]
    exact (π.cusp f.1 f.2).1.level.preimage (CuspSub.continuous_locGL v)
  · intro E _ _ _ D k f hf
    have h1 : ((nu F (finGL E 2 k) : (A F)ˣ) : A F).1 = 1 := fst_norm D _ (fst_detFin k)
    generalize nu F (finGL E 2 k) = t at h1
    have hp : TR.pInf F (t : A F) = 1 := by
      change (TR.infEq F).symm (t : A F).1 = 1
      rw [h1]
      exact map_one _
    have hinf : Matrix.GeneralLinearGroup.map (TR.pInf F) (dM t) = 1 := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [dM, hp]
    have hd : finGL F 2 (Matrix.GeneralLinearGroup.map (pFin F) (dM t)) = dM t := by
      have h := TR.infGL_mul_finGL (dM t)
      rwa [hinf, map_one, one_mul] at h
    refine ⟨_, π.stable (.fin (Matrix.GeneralLinearGroup.map (pFin F) (dM t))) f hf, ?_⟩
    funext g
    change f.1 (g * finGL F 2 _) = f.1 (g * dM t)
    rw [hd]
