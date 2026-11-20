import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LIdemEx

variable {D : D7}

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]`. Consider the case `tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]`.
-/
theorem repr_map' {F E R R' ι : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] (φ : R →ₐ[F] R') (b : Module.Basis ι F E) (z : R ⊗[F] E) (k : ι) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) z) k =
      φ ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]

/- English proof (translation)
Set `b` to `Module.Basis.ofVectorSpace D.host.F D.host.E`. Apply `(Algebra.TensorProduct.basis (AF D.host.F) b).repr.injective` to reduce the goal to its premises. Use `Finsupp.ext fun k => Prod.ext ?_ ?_` and prove the remaining obligations. Use function extensionality and compare the values at `w`. Establish `h1` using `repr_map' (evInf D.host.F w) b z k`.

Establish `h2` using `repr_map' (evInf D.host.F w) b z' k`. Establish `h : Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) z = Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) z'` using `hi w`. Rewrite `h1` using `[h, h2]`. Conclude with `h1.symm`. Use `FiniteAdeleRing.ext _ fun v => ?_` and prove the remaining obligations.

Establish `h1` using `repr_map' (evFin D.host.F v) b z k`. Establish `h2` using `repr_map' (evFin D.host.F v) b z' k`. Establish `h : Algebra.TensorProduct.map (evFin D.host.F v) (AlgHom.id D.host.F D.host.E) z = Algebra.TensorProduct.map (evFin D.host.F v) (AlgHom.id D.host.F D.host.E) z'` using `hf v`. Rewrite `h1` using `[h, h2]`. Conclude with `h1.symm`.
-/
theorem ae_ext (z z' : AE D) (hi : ∀ w, compInf D.host.F D.host.E w z = compInf D.host.F D.host.E w z')
    (hf : ∀ v, cv D v z = cv D v z') : z = z' := by
  let b := Module.Basis.ofVectorSpace D.host.F D.host.E
  apply (Algebra.TensorProduct.basis (AF D.host.F) b).repr.injective
  refine Finsupp.ext fun k => Prod.ext ?_ ?_
  · funext w
    have h1 := repr_map' (evInf D.host.F w) b z k
    have h2 := repr_map' (evInf D.host.F w) b z' k
    have h : Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) z =
        Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) z' := hi w
    rw [h, h2] at h1
    exact h1.symm
  · refine FiniteAdeleRing.ext _ fun v => ?_
    have h1 := repr_map' (evFin D.host.F v) b z k
    have h2 := repr_map' (evFin D.host.F v) b z' k
    have h : Algebra.TensorProduct.map (evFin D.host.F v) (AlgHom.id D.host.F D.host.E) z =
        Algebra.TensorProduct.map (evFin D.host.F v) (AlgHom.id D.host.F D.host.E) z' := hf v
    rw [h, h2] at h1
    exact h1.symm

open Classical in

def indS (S : Finset (Pl D)) : Af D.host.F :=
  ⟨fun v => if v ∈ S then 1 else 0, Filter.Eventually.of_forall fun v => by
    by_cases h : v ∈ S
    · simp only [if_pos h]; exact one_mem (v.adicCompletionIntegers D.host.F)
    · simp only [if_neg h]; exact zero_mem (v.adicCompletionIntegers D.host.F)⟩

def eS (S : Finset (Pl D)) : AE D := ((1, indS S) : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)

/- English proof (translation)
Use `⟨fun w => ?_, fun v => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(evInf D.host.F w (1, indS S)) ⊗ₜ[D.host.F] (1 : D.host.E) = 1`. Rewrite using `[show evInf D.host.F w (1, indS S) = 1 from rfl]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `(evFin D.host.F v (1, indS S)) ⊗ₜ[D.host.F] (1 : D.host.E) = _`.

Rewrite using `[show evFin D.host.F v (1, indS S) = if v ∈ S then 1 else 0 from rfl]`. Use `split_ifs`. Both sides reduce to the same expression. Conclude with `TensorProduct.zero_tmul _ _`.
-/
theorem isIdem_eS (S : Finset (Pl D)) : IsIdem S (eS S) := by
  classical
  refine ⟨fun w => ?_, fun v => ?_⟩
  · change (evInf D.host.F w (1, indS S)) ⊗ₜ[D.host.F] (1 : D.host.E) = 1
    rw [show evInf D.host.F w (1, indS S) = 1 from rfl]
    rfl
  · change (evFin D.host.F v (1, indS S)) ⊗ₜ[D.host.F] (1 : D.host.E) = _
    rw [show evFin D.host.F v (1, indS S) = if v ∈ S then 1 else 0 from rfl]
    split_ifs
    · rfl
    · exact TensorProduct.zero_tmul _ _

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]`. Consider the case `add x y hx hy => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, hx, hy, RingHom.map_add]`. Consider the case `tmul a x => rfl`.
-/
theorem compInf_cA (w : InfinitePlace D.host.F) (z : AE D) :
    compInf D.host.F D.host.E w (cA D z) =
      (Algebra.TensorProduct.map (AlgHom.id D.host.F w.Completion) D.sp.cm.sig).toRingHom (compInf D.host.F D.host.E w z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, hx, hy, RingHom.map_add]
  | tmul a x => rfl

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]`. Consider the case `add x y hx hy => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, hx, hy, RingHom.map_add]`. Consider the case `tmul a x => rfl`.
-/
theorem cv_cA (v : Pl D) (z : AE D) :
    cv D v (cA D z) =
      (Algebra.TensorProduct.map (AlgHom.id D.host.F (Fv D.host.F v)) D.sp.cm.sig).toRingHom (cv D v z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, hx, hy, RingHom.map_add]
  | tmul a x => rfl

/- English proof (translation)
Use `⟨ae_ext _ _ (fun w => ?_) (fun v => ?_), ae_ext _ _ (fun w => ?_) (fun v => ?_)⟩` and prove the remaining obligations. Rewrite using `[map_mul, he.1 w, one_mul]`. Apply the tactic sequence `rw [map_mul, he.2 v] split_ifs <;> simp`. Rewrite using `[compInf_cA, he.1 w, RingHom.map_one]`. Apply the tactic sequence `rw [cv_cA, he.2 v] split_ifs <;> simp`.
-/
theorem idem_props (S : Finset (Pl D)) (e : AE D) (he : IsIdem S e) : e * e = e ∧ cA D e = e := by
  classical
  refine ⟨ae_ext _ _ (fun w => ?_) (fun v => ?_), ae_ext _ _ (fun w => ?_) (fun v => ?_)⟩
  · rw [map_mul, he.1 w, one_mul]
  · rw [map_mul, he.2 v]
    split_ifs <;> simp
  · rw [compInf_cA, he.1 w, RingHom.map_one]
  · rw [cv_cA, he.2 v]
    split_ifs <;> simp

end PositivityTheory.Rg.Rsw.L.LIdemEx

namespace PositivityTheory.Rg.Rsw.L

/- English proof (translation)
Introduce `_ S` and use `⟨⟨_, LIdemEx.isIdem_eS S⟩, fun e he => LIdemEx.idem_props S e he⟩`.
-/
theorem idemEx : IdemEx := fun _ S =>
  ⟨⟨_, LIdemEx.isIdem_eS S⟩, fun e he => LIdemEx.idem_props S e he⟩

end PositivityTheory.Rg.Rsw.L

end
