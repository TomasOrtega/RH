import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar
import GroundTheory.GlobalFields.SemilocalAlgebras.Finite

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)
open scoped TensorProduct
open GroundTheory.Global.SemiLocal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace UpperTheory.V.Z.Sym.Dict.Br

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `⟨rfl⟩`.
-/
private theorem lies {v : Pl (Lp L)} {w : Plc L} (h : un w = v) : w.asIdeal.LiesOver v.asIdeal := by
  subst h
  exact ⟨rfl⟩

/- English proof (translation)
The claim follows from `HeightOneSpectrum.ext h.over.symm`.
-/
private theorem unOf {v : Pl (Lp L)} {w : Plc L} (h : w.asIdeal.LiesOver v.asIdeal) : un w = v :=
  HeightOneSpectrum.ext h.over.symm

/- English proof (translation)
Establish `hd` using `IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 (Lp L)) (Lp L) v`. Establish `key : (P.φ v w h) ∘ algebraMap (Lp L) (Kv v) = (completionMap v w) ∘ algebraMap (Lp L) (Kv v)`. Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp_apply]`. Rewrite using `[completionMap_algebraMap]`.

Conclude with `(P.φ_alg v w h x).trans (IsScalarTower.algebraMap_apply (Lp L) L _ x).symm`. Conclude with `congrFun (hd.equalizer (P.φ_cont v w h) (continuous_completionMap v w) key) a`.
-/
private theorem phi_eq (P : Pre L) (v : Pl (Lp L)) (w : Plc L) (h : un w = v)
    [w.asIdeal.LiesOver v.asIdeal] (a : Kv v) : P.φ v w h a = completionMap v w a := by
  have hd := IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 (Lp L)) (Lp L) v
  have key : (P.φ v w h) ∘ algebraMap (Lp L) (Kv v) =
      (completionMap v w) ∘ algebraMap (Lp L) (Kv v) := by
    funext x
    simp only [Function.comp_apply]
    rw [completionMap_algebraMap]
    exact (P.φ_alg v w h x).trans (IsScalarTower.algebraMap_apply (Lp L) L _ x).symm
  exact congrFun (hd.equalizer (P.φ_cont v w h) (continuous_completionMap v w) key) a

private def bas (P : Pre L) : Module.Basis (Fin 2) (Lp L) L :=
  (QuadraticAlgebra.basis P.Δ 0).map (AlgEquiv.ofRingEquiv (f := P.e) P.e_alg).toLinearEquiv

/- English proof (translation)
Establish `h0 : QuadraticAlgebra.basis P.Δ (0 : Lp L) 0 = 1`. Apply the tactic sequence `ext <;> simp [QuadraticAlgebra.basis] <;> rfl`. Rewrite using `[bas, Module.Basis.map_apply, h0]`. Simplify using the standard rewrite rules.
-/
private theorem bas_zero (P : Pre L) : bas P 0 = 1 := by
  have h0 : QuadraticAlgebra.basis P.Δ (0 : Lp L) 0 = 1 := by
    ext <;> simp [QuadraticAlgebra.basis] <;> rfl
  rw [bas, Module.Basis.map_apply, h0]
  simp

/- English proof (translation)
Establish `h1 : QuadraticAlgebra.basis P.Δ (0 : Lp L) 1 = QuadraticAlgebra.omega`. Apply the tactic sequence `ext <;> simp [QuadraticAlgebra.basis]`. Rewrite using `[bas, Module.Basis.map_apply, h1]`. Both sides reduce to the same expression.
-/
private theorem bas_one (P : Pre L) : bas P 1 = P.e QuadraticAlgebra.omega := by
  have h1 : QuadraticAlgebra.basis P.Δ (0 : Lp L) 1 = QuadraticAlgebra.omega := by
    ext <;> simp [QuadraticAlgebra.basis]
  rw [bas, Module.Basis.map_apply, h1]
  rfl

private def tt (P : Pre L) (v : Pl (Lp L)) (x : Lsq (Kv v) (cv v P.Δ)) : Kv v ⊗[Lp L] L :=
  x.re ⊗ₜ 1 + x.im ⊗ₜ P.e QuadraticAlgebra.omega

/- English proof (translation)
Simplify using `only [tt, map_add, tensorEquiv_tmul, map_one, mul_one, Pi.add_apply, Pi.mul_apply]`. Use `haveI := p.2`. Use `show completionMap v p.1 x.re + completionMap v p.1 x.im * algebraMap L _ (P.e QuadraticAlgebra.omega) = P.φ v p.1 (unOf p.2) x.re + P.φ v p.1 (unOf p.2) x.im * P.rt p.1`. Rewrite using `[phi_eq P v p.1 (unOf p.2), phi_eq P v p.1 (unOf p.2)]`. Both sides reduce to the same expression.
-/
private theorem tt_apply (P : Pre L) (v : Pl (Lp L)) (x : Lsq (Kv v) (cv v P.Δ)) (p : PlacesOver L v) :
    tensorEquiv L v (tt P v x) p = P.rho v p.1 (unOf p.2) x := by
  simp only [tt, map_add, tensorEquiv_tmul, map_one, mul_one, Pi.add_apply, Pi.mul_apply]
  haveI := p.2
  show completionMap v p.1 x.re + completionMap v p.1 x.im * algebraMap L _ (P.e QuadraticAlgebra.omega) =
    P.φ v p.1 (unOf p.2) x.re + P.φ v p.1 (unOf p.2) x.im * P.rt p.1
  rw [phi_eq P v p.1 (unOf p.2), phi_eq P v p.1 (unOf p.2)]
  rfl

/- English proof (translation)
Rewrite using `[Module.Basis.equivFun_symm_apply, Fin.sum_univ_two]`. Simplify using `only [Algebra.TensorProduct.basis_apply, bas_zero, bas_one, Matrix.cons_val_zero, Matrix.cons_val_one, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Both sides reduce to the same expression.
-/
private theorem tt_eq (P : Pre L) (v : Pl (Lp L)) (x : Lsq (Kv v) (cv v P.Δ)) :
    tt P v x = (Algebra.TensorProduct.basis (Kv v) (bas P)).equivFun.symm ![x.re, x.im] := by
  rw [Module.Basis.equivFun_symm_apply, Fin.sum_univ_two]
  simp only [Algebra.TensorProduct.basis_apply, bas_zero, bas_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl

/- English proof (translation)
Introduce `x y h`. Rewrite `h` using `[tt_eq, tt_eq]`. Establish `h'` using `(Algebra.TensorProduct.basis (Kv v) (bas P)).equivFun.symm.injective h`. Use `QuadraticAlgebra.ext ?_ ?_` and prove the remaining obligations. Simplify using `using congrFun h' 0`.

Simplify using `using congrFun h' 1`.
-/
private theorem tt_inj (P : Pre L) (v : Pl (Lp L)) : Function.Injective (tt P v) := by
  intro x y h
  rw [tt_eq, tt_eq] at h
  have h' := (Algebra.TensorProduct.basis (Kv v) (bas P)).equivFun.symm.injective h
  refine QuadraticAlgebra.ext ?_ ?_
  · simpa using congrFun h' 0
  · simpa using congrFun h' 1

/- English proof (translation)
Introduce `t`. Use `set c := (Algebra.TensorProduct.basis (Kv v) (bas P)).equivFun t`. Use `⟨⟨c 0, c 1⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[tt_eq]`. Establish `hc : (![c 0, c 1] : Fin 2 → Kv v) = c`.

Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> rfl`. Simplify using `only [QuadraticAlgebra.re, QuadraticAlgebra.im]`. Rewrite using `[hc]`. Conclude with `(Algebra.TensorProduct.basis (Kv v) (bas P)).equivFun.symm_apply_apply t`.
-/
private theorem tt_surj (P : Pre L) (v : Pl (Lp L)) : Function.Surjective (tt P v) := by
  intro t
  set c := (Algebra.TensorProduct.basis (Kv v) (bas P)).equivFun t
  refine ⟨⟨c 0, c 1⟩, ?_⟩
  rw [tt_eq]
  have hc : (![c 0, c 1] : Fin 2 → Kv v) = c := by
    funext i
    fin_cases i <;> rfl
  simp only [QuadraticAlgebra.re, QuadraticAlgebra.im]
  rw [hc]
  exact (Algebra.TensorProduct.basis (Kv v) (bas P)).equivFun.symm_apply_apply t

end UpperTheory.V.Z.Sym.Dict.Br

end

/- English proof (translation)
Introduce `L _ _ _ P v`. Prove the components needed by the constructor for the conclusion. Introduce `x y hxy`. Use `tt_inj P v ((tensorEquiv L v).injective (funext fun p => ?_))` and prove the remaining obligations. Rewrite using `[tt_apply, tt_apply]`.

Conclude with `congrFun hxy ⟨p.1, unOf p.2⟩`. Introduce `f`. Take `⟨t, ht⟩` from `(tensorEquiv L v).surjective (fun p => f ⟨p.1, unOf p.2⟩)`. Take `⟨x, rfl⟩` from `tt_surj P v t`. Use `⟨x, funext fun w => ?_⟩` and prove the remaining obligations.

Use `congrFun ht ⟨w.1, lies w.2⟩` as an intermediate fact. Rewrite `this` using `[tt_apply]`. Conclude with `this`.
-/
theorem UpperTheory.V.Z.Sym.Dict.Br.rhoBij :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (P : Pre L), ∀ v : Pl (Lp L), Function.Bijective fun (x : Lsq (Kv v) (cv v P.Δ)) (w : {w : Plc L // un w = v}) => P.rho v w.1 w.2 x := by
  intro L _ _ _ P v
  constructor
  · intro x y hxy
    refine tt_inj P v ((tensorEquiv L v).injective (funext fun p => ?_))
    rw [tt_apply, tt_apply]
    exact congrFun hxy ⟨p.1, unOf p.2⟩
  · intro f
    obtain ⟨t, ht⟩ := (tensorEquiv L v).surjective (fun p => f ⟨p.1, unOf p.2⟩)
    obtain ⟨x, rfl⟩ := tt_surj P v t
    refine ⟨x, funext fun w => ?_⟩
    have := congrFun ht ⟨w.1, lies w.2⟩
    rw [tt_apply] at this
    exact this
