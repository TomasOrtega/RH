import Mathlib
import Formalism.LocalRingCardinality.DataSpaces
import Formalism.LocalRingCardinality.DataRows
import Formalism.FormalDegreeBessel.StatementG
import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalRingCardinality.DataHost
import Formalism.LocalRingCardinality.Params
import Formalism.LocalRingCardinality.DataTheta
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MultilinearVanishLattice

noncomputable def UpperTheory.Reformulated.B.LowTypeThetaMapVanishing.KfLow :
    {D : Formalism.BasicNotions.D7} →
      {V : Formalism.BasicNotions.TH.HSp D} →
        {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} → (M : Formalism.IndefR.Mult.DSModel V S) → (τ : D.what₂.Tau) → Submodule ℂ ↥(M.sm τ) :=
    fun {D : Formalism.BasicNotions.D7} {V : Formalism.BasicNotions.TH.HSp D} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} (M : Formalism.IndefR.Mult.DSModel V S)
        (τ : D.what₂.Tau) ↦
      Submodule.span ℂ
        {w : ↥(M.sm τ) |
          ∃ g ∈ Formalism.QuantumDeterminants.UH (Formalism.BasicNotions.TH.gramAt D V τ),
            ∃ (w0 : ↥(Formalism.IndefR.Links.lowT M τ)), (↑w : M.H τ) = (M.rep τ g : M.H τ → M.H τ) (↑(↑w0 : ↥(M.sm τ)) : M.H τ)}

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Classical in
/- English proof (translation)
Use `⟨Formalism.L2.Theta.atTau θ V τ g, ?_⟩` and prove the remaining obligations. Unfold `Formalism.IndefR.Mult.Mult at hT`. Proceed by induction on `hT using Submodule.span_induction with`. Consider the case `mem U hU => intro x`. Conclude with `congrFun (hU.equiv τ g hg v w hw) x`.

Consider the case `zero => intro x`. Both sides reduce to the same expression. Consider the case `add U U' _ _ h h'`. Introduce `x`. Use `show U (Function.update v τ w) x + U' (Function.update v τ w) x = U v _ + U' v _`.

Rewrite using `[h x, h' x]`. Consider the case `smul a U _ h`. Introduce `x`. Use `show a • U (Function.update v τ w) x = a • U v _`. Rewrite using `[h x]`.
-/
private theorem UpperTheory.Reformulated.B.LowTypeThetaMapVanishing.equiv_of_mem
    {D : Formalism.BasicNotions.D7} {V : Formalism.BasicNotions.TH.HSp D} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar}
    (θ : D.what₂.Tau → TensorProduct (↥D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf ↥D.host.F) D.host.E →+* ℂ)
    (M : Formalism.IndefR.Mult.DSModel V S) (J : Set (Formalism.L2.Theta.GA D V)) (χ : Formalism.L2.Theta.GA D V → ℂ)
    {T : Formalism.IndefR.Mult.MMap M} (hT : T ∈ Formalism.IndefR.Mult.Mult θ M J χ) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.BasicNotions.TH.gramAt D V τ))
    (v : M.Vec) (w : M.sm τ) (hw : (w : M.H τ) = M.rep τ g (v τ)) :
    ∃ k : Formalism.L2.Theta.GA D V, ∀ x : Formalism.L2.Theta.GA D V, T (Function.update v τ w) x = T v (x * k) := by
  refine ⟨Formalism.L2.Theta.atTau θ V τ g, ?_⟩
  unfold Formalism.IndefR.Mult.Mult at hT
  induction hT using Submodule.span_induction with
  | mem U hU => intro x; exact congrFun (hU.equiv τ g hg v w hw) x
  | zero => intro x; rfl
  | add U U' _ _ h h' =>
    intro x
    show U (Function.update v τ w) x + U' (Function.update v τ w) x = U v _ + U' v _
    rw [h x, h' x]
  | smul a U _ h =>
    intro x
    show a • U (Function.update v τ w) x = a • U v _
    rw [h x]

/- English proof (translation)
Introduce `D V S θ M J χ T hT h0 s v hs hns`. Use `UpperTheory.multilinear_vanish_lattice T (fun τ => (Formalism.IndefR.Links.lowT M τ : Set (M.sm τ))) (fun τ => {w : ↥(M.sm τ) | ∃ g ∈ Formalism.QuantumDeterminants.UH (Formalism.BasicNotions.TH.gramAt D V τ), ∃ (w0 : ↥(Formalism.IndefR.Links.lowT M τ)), (↑w : M.H τ) = (M.rep τ g …` and prove the remaining obligations. Introduce and unpack `τ w ⟨g, hg, w0, hw⟩`. Use `⟨w0.1, w0.2, fun u hu => ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `UpperTheory.Reformulated.B.LowTypeThetaMapVanishing.equiv_of_mem θ M J χ hT τ g hg (Function.update u τ w0.1) w (by rw [Function.update_self]; exact hw)`.

Use function extensionality and compare the values at `x`. Establish `h1` using `hk x`. Rewrite `h1` using `[Function.update_idem]`. Establish `h2 : T (Function.update u τ w) x = T (Function.update u τ w0.1) (x * k)` using `by convert h1`. Rewrite using `[h2, hu]`.

Both sides reduce to the same expression. Introduce `τ`. Distinguish the cases in `h : τ ∈ s`. Conclude with `hs τ h`. Conclude with `Submodule.subset_span (hns τ h)`.
-/
theorem UpperTheory.Reformulated.B.LowTypeThetaMapVanishing.vanish_KfLow :
    ∀ {D : Formalism.BasicNotions.D7} {V : Formalism.BasicNotions.TH.HSp D} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar}
      (θ : D.what₂.Tau → TensorProduct (↥D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf ↥D.host.F) D.host.E →+* ℂ)
      (M : Formalism.IndefR.Mult.DSModel V S) (J : Set (Formalism.L2.Theta.GA D V)) (χ : Formalism.L2.Theta.GA D V → ℂ)
      {T : Formalism.IndefR.Mult.MMap M},
      T ∈ Formalism.IndefR.Mult.Mult θ M J χ →
        (∀ (v : (ρ : D.what₂.Tau) → ↥(Formalism.IndefR.Links.lowT M ρ)),
            ((T : ((i : D.what₂.Tau) → ↥(M.sm i)) → Formalism.L2.Theta.GA D V → ℂ) fun (ρ : D.what₂.Tau) ↦ (↑(v ρ) : ↥(M.sm ρ))) =
              (0 : Formalism.L2.Theta.GA D V → ℂ)) →
          ∀ (s : Finset D.what₂.Tau) (v : M.Vec),
            (∀ τ ∈ s, v τ ∈ UpperTheory.Reformulated.B.LowTypeThetaMapVanishing.KfLow M τ) →
              (∀ τ ∉ s,
                  ∃ g ∈ Formalism.QuantumDeterminants.UH (Formalism.BasicNotions.TH.gramAt D V τ),
                    ∃ (w0 : ↥(Formalism.IndefR.Links.lowT M τ)),
                      (↑(v τ) : M.H τ) = (M.rep τ g : M.H τ → M.H τ) (↑(↑w0 : ↥(M.sm τ)) : M.H τ)) →
                (T : ((i : D.what₂.Tau) → ↥(M.sm i)) → Formalism.L2.Theta.GA D V → ℂ) v = (0 : Formalism.L2.Theta.GA D V → ℂ) := by
  intro D V S θ M J χ T hT h0 s v hs hns
  classical
  refine UpperTheory.multilinear_vanish_lattice T (fun τ => (Formalism.IndefR.Links.lowT M τ : Set (M.sm τ)))
    (fun τ => {w : ↥(M.sm τ) |
          ∃ g ∈ Formalism.QuantumDeterminants.UH (Formalism.BasicNotions.TH.gramAt D V τ),
            ∃ (w0 : ↥(Formalism.IndefR.Links.lowT M τ)), (↑w : M.H τ) = (M.rep τ g : M.H τ → M.H τ) (↑(↑w0 : ↥(M.sm τ)) : M.H τ)})
    (fun u hu => h0 (fun ρ => ⟨u ρ, hu ρ⟩)) ?_ v ?_
  · rintro τ w ⟨g, hg, w0, hw⟩
    refine ⟨w0.1, w0.2, fun u hu => ?_⟩
    obtain ⟨k, hk⟩ := UpperTheory.Reformulated.B.LowTypeThetaMapVanishing.equiv_of_mem θ M J χ hT τ g hg (Function.update u τ w0.1) w
      (by rw [Function.update_self]; exact hw)
    funext x
    have h1 := hk x
    rw [Function.update_idem] at h1
    have h2 : T (Function.update u τ w) x = T (Function.update u τ w0.1) (x * k) := by convert h1
    rw [h2, hu]
    rfl
  · intro τ
    by_cases h : τ ∈ s
    · exact hs τ h
    · exact Submodule.subset_span (hns τ h)
