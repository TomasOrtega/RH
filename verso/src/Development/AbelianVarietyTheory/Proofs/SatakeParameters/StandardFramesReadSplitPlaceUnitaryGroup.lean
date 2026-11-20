import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitLocalPlaceDataAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceIdempotentMulEqSelfOfSupportedStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitFrameRead

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem tensCast_one_tmul {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2) (x : E) :
    GlobalTheory.NJoin.tensCast h ((1 : FiniteAdeleRing (𝓞 F1) F1) ⊗ₜ[F1] x) = x ⊗ₜ[F2] (1 : FiniteAdeleRing (𝓞 F2) F2) := by
  subst h; rfl

/- English proof (translation)
Rewrite using `[Matrix.map_sub _ (map_sub _), hM, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul, hK, Matrix.mul_one, ← Matrix.map_mul, h1, sub_self]`.
-/
theorem gen_supp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (fin : A →+* B) (Ψ : B →+* C) {m k : ℕ}
    (M : Matrix (Fin m) (Fin m) A) (β : Matrix (Fin m) (Fin k) B) (K : Matrix (Fin k) (Fin k) B) (β' : Matrix (Fin k) (Fin m) B)
    (h1 : β * β' = 1) (hM : M.map fin = β * K * β') (hK : K.map Ψ = 1) : ((M - 1).map fin).map Ψ = 0 := by
  rw [Matrix.map_sub _ (map_sub _), hM, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_sub _ (map_sub _),
    Matrix.map_mul, Matrix.map_mul, hK, Matrix.mul_one, ← Matrix.map_mul, h1, sub_self]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Take `⟨⟨β, β', h1, h2, hm⟩, -⟩` from `hV`. Set `Φ` to `c.toRingHom.comp (s.proj.comp (GlobalTheory.NJoin.tensCast hF).toRingHom)`. Use `⟨⟨β.map Φ, β'.map Φ, ?_, ?_⟩, fun h hh => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← Matrix.map_mul, h1]`. Conclude with `Matrix.map_one _ (map_zero Φ) (map_one Φ)`.

Rewrite using `[← Matrix.map_mul, h2]`. Conclude with `Matrix.map_one _ (map_zero Φ) (map_one Φ)`. Introduce `i j`. Apply `GlobalTheory.T.splitPlaceIdempotent_mul_eq_self_of_supported D s hF p c hπ` to reduce the goal to its premises. Establish `hk` using `MonoidHom.mem_ker.1 (PV.into h)`.

Establish `e2 : ((Formalism.L2.Theta.mt V (PV.ψ h)) - 1).map (Formalism.L2.Theta.infPart D) = 0`. Rewrite using `[Matrix.map_sub _ (map_sub (Formalism.L2.Theta.infPart D)), Matrix.map_one _ (map_zero (Formalism.L2.Theta.infPart D)) (map_one (Formalism.L2.Theta.infPart D))]`. Establish `e3 : (Formalism.L2.Theta.mt V (PV.ψ h)).map (Formalism.L2.Theta.infPart D) = (Formalism.L2.Theta.infHom V (PV.ψ h)).val` using `rfl`. Rewrite using `[e3, hk, Units.val_one, sub_self]`. Conclude with `congrFun (congrFun e2 i) j`.

Introduce `v' hv'`. Establish `hh'` using `hh v' (by simpa using hv')`. Establish `e4` using `gen_supp (Formalism.L2.Theta.finPart D) ((ReciprocityTheory.Aut.compAt D.host.E v').comp (GlobalTheory.NJoin.tensCast hF).toRingHom) (Formalism.L2.Theta.mt V (PV.ψ h)) β _ β' h1 (hm h) (by`. Rewrite using `[← hh']`. Use extensionality with `a b`.

Conclude with `congrArg (ReciprocityTheory.Aut.compAt D.host.E v') (RingEquiv.apply_symm_apply _ _))`. Conclude with `congrFun (congrFun e4 i) j`. Establish `e7 : (Formalism.L2.Theta.mt V (PV.ψ h)).map p.π = ((Formalism.L2.Theta.mt V (PV.ψ h)).map (Formalism.L2.Theta.finPart D)).map Φ` using `Matrix.ext fun a b => hπ _`. Establish `e5 : (Formalism.L2.Theta.mt V (PV.ψ h)).map (Formalism.L2.Theta.finPart D) = _` using `hm h`. Establish `hK : ((h.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)).map (GlobalTheory.NJoin.tensCast hF).symm).map Φ = (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h)).val`.

Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Conclude with `congrArg (fun y => c (s.proj y)) (RingEquiv.apply_symm_apply _ _)`. Rewrite using `[e7, e5, ← hK]`. Conclude with `(Matrix.map_mul).trans (congrArg (· * β'.map Φ) Matrix.map_mul)`.
-/
theorem side_loc (D : D7) (s : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E)
    (p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E))
    (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E)
    (hπ : ∀ a : Formalism.L2.Theta.AE D, p.π a = c (s.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a))))
    (V : Formalism.BasicNotions.TH.HSp D) (n : ℕ) (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n) (hV : GlobalTheory.NJoin.StdFrame hF PV) :
    ∃ FS : GlobalTheory.LocMod.Frame (s.w.adicCompletion D.host.E) V.rank (Fin n), ∀ h, TrivOutside {s.v} h →
      p.IsLoc FS (PV.ψ h) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h)) := by
  obtain ⟨⟨β, β', h1, h2, hm⟩, -⟩ := hV
  let Φ := c.toRingHom.comp (s.proj.comp (GlobalTheory.NJoin.tensCast hF).toRingHom)
  refine ⟨⟨β.map Φ, β'.map Φ, ?_, ?_⟩, fun h hh => ⟨?_, ?_⟩⟩
  · rw [← Matrix.map_mul, h1]; exact Matrix.map_one _ (map_zero Φ) (map_one Φ)
  · rw [← Matrix.map_mul, h2]; exact Matrix.map_one _ (map_zero Φ) (map_one Φ)
  · intro i j
    apply GlobalTheory.T.splitPlaceIdempotent_mul_eq_self_of_supported D s hF p c hπ
    · have hk := MonoidHom.mem_ker.1 (PV.into h)
      have e2 : ((Formalism.L2.Theta.mt V (PV.ψ h)) - 1).map (Formalism.L2.Theta.infPart D) = 0 := by
        rw [Matrix.map_sub _ (map_sub (Formalism.L2.Theta.infPart D)),
          Matrix.map_one _ (map_zero (Formalism.L2.Theta.infPart D)) (map_one (Formalism.L2.Theta.infPart D))]
        have e3 : (Formalism.L2.Theta.mt V (PV.ψ h)).map (Formalism.L2.Theta.infPart D) = (Formalism.L2.Theta.infHom V (PV.ψ h)).val := rfl
        rw [e3, hk, Units.val_one, sub_self]
      exact congrFun (congrFun e2 i) j
    · intro v' hv'
      have hh' := hh v' (by simpa using hv')
      have e4 := gen_supp (Formalism.L2.Theta.finPart D) ((ReciprocityTheory.Aut.compAt D.host.E v').comp (GlobalTheory.NJoin.tensCast hF).toRingHom)
        (Formalism.L2.Theta.mt V (PV.ψ h)) β _ β' h1 (hm h) (by
          rw [← hh']
          ext a b
          exact congrArg (ReciprocityTheory.Aut.compAt D.host.E v') (RingEquiv.apply_symm_apply _ _))
      exact congrFun (congrFun e4 i) j
  · have e7 : (Formalism.L2.Theta.mt V (PV.ψ h)).map p.π = ((Formalism.L2.Theta.mt V (PV.ψ h)).map (Formalism.L2.Theta.finPart D)).map Φ :=
      Matrix.ext fun a b => hπ _
    have e5 : (Formalism.L2.Theta.mt V (PV.ψ h)).map (Formalism.L2.Theta.finPart D) = _ := hm h
    have hK : ((h.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)).map (GlobalTheory.NJoin.tensCast hF).symm).map Φ =
        (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h)).val := by
      refine Matrix.ext fun a b => ?_
      exact congrArg (fun y => c (s.proj y)) (RingEquiv.apply_symm_apply _ _)
    rw [e7, e5, ← hK]
    exact (Matrix.map_mul).trans (congrArg (· * β'.map Φ) Matrix.map_mul)

/- English proof (translation)
Introduce `D V W n r PV PW hF hV hW s`. Take `⟨p, c, hId, hc, hci, hπ⟩` from `GlobalTheory.T.exists_splitLocalPlaceData_at_splitPlace D s hF`. Establish `hpr : ∀ x : D.host.E, p.pr x = algebraMap D.host.E (s.w.adicCompletion D.host.E) x`. Introduce `x`. Unfold `GlobalTheory.LocMod.Place.pr`.

Rewrite using `[hπ]`. Establish `e1 : Formalism.L2.Theta.finPart D (Formalism.L2.Theta.incA D x) = (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] x`. Simplify using `[Formalism.L2.Theta.finPart, Formalism.L2.Theta.incA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Algebra.TensorProduct.map_tmul]`. Rewrite using `[e1, tensCast_one_tmul, ← hci x]`. Use `congr 1`.

Simplify using `[ReciprocityTheory.Aut.SplitPlace.proj]`. Take `⟨FS, hFS⟩` from `side_loc D s hF p c hπ V n PV hV`. Take `⟨FT, hFT⟩` from `side_loc D s hF p c hπ W r PW hW`. Conclude with `⟨p, hId, hpr, FS, FT, c, hc, hci, hFS, hFT⟩`.
-/
theorem main : ∀ (D : D7) (V W : Formalism.BasicNotions.TH.HSp D) (n r : ℕ) (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n) (PW : Formalism.IndefR.principalLevelFrame.RowPsi W r) (hF : D.host.F = maximalRealSubfield D.host.E), GlobalTheory.NJoin.StdFrame hF PV → GlobalTheory.NJoin.StdFrame hF PW → ∀ (s : SplitPlace D.host.E), ∃ (p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E)), Formalism.L2.JoinChr.IsPlIdem D p.e s.w ∧ (∀ x : D.host.E, p.pr x = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) ∧ ∃ (FS : GlobalTheory.LocMod.Frame (s.w.adicCompletion D.host.E) V.rank (Fin n)) (FT : GlobalTheory.LocMod.Frame (s.w.adicCompletion D.host.E) W.rank (Fin r)) (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E), Continuous c ∧ (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) ∧ (∀ h, TrivOutside {s.v} h → p.IsLoc FS (PV.ψ h) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h))) ∧ ∀ g, TrivOutside {s.v} g → p.IsLoc FT (PW.ψ g) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc r g)) := by
  intro D V W n r PV PW hF hV hW s
  obtain ⟨p, c, hId, hc, hci, hπ⟩ := GlobalTheory.T.exists_splitLocalPlaceData_at_splitPlace D s hF
  have hpr : ∀ x : D.host.E, p.pr x = algebraMap D.host.E (s.w.adicCompletion D.host.E) x := by
    intro x
    unfold GlobalTheory.LocMod.Place.pr
    rw [hπ]
    have e1 : Formalism.L2.Theta.finPart D (Formalism.L2.Theta.incA D x) =
        (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] x := by
      simp [Formalism.L2.Theta.finPart, Formalism.L2.Theta.incA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Algebra.TensorProduct.map_tmul]
    rw [e1, tensCast_one_tmul, ← hci x]
    congr 1
    simp [ReciprocityTheory.Aut.SplitPlace.proj]
  obtain ⟨FS, hFS⟩ := side_loc D s hF p c hπ V n PV hV
  obtain ⟨FT, hFT⟩ := side_loc D s hF p c hπ W r PW hW
  exact ⟨p, hId, hpr, FS, FT, c, hc, hci, hFS, hFT⟩

end GlobalTheory.SplitFrameRead
