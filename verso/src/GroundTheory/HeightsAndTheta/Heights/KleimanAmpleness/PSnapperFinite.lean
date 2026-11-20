import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsSnapper
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TildeFiniteESt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistTildeSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TildeShiftSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PClaimVanish
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

/- English proof (translation)
Introduce `k _ Ω _ _ N x E _ _ _ _ F hF0 t L n c i`. Establish `hpow : ∀ (Lb : LineBundle k x) (m : ℕ), ∃ Q : FinGradedSub (S` using `k) (x := x) Ω, Lb.toSubSystem.pow m = Q.tildeSys 0 := by`. Introduce `Lb m`. Proceed by induction on `m with`. Consider the case `zero`.

Use `⟨coordGraded k x, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `twistSys k x 0 = _`. Rewrite using `[← coordGraded_tildeSys_twist (twistSys k x 0), SubSystem.twist_twistSys_zero]`. Consider the case `succ m ih`. Take `⟨Q, hQ⟩` from `ih`.

Take `⟨QL, -, hQL⟩` from `hEL k Ω N x Ω Lb.toSubFamily Lb.fg`. Take `⟨P, -, hP⟩` from `hTL k Ω N x Ω Q QL`. Use `⟨P, ?_⟩` and prove the remaining obligations. Establish `hL : Lb.toSubSystem = QL.tildeSys 0` using `SubSystem.ext_sub fun I => (hQL I).symm`. Express the relevant statement in the definitionally equal form `(Lb.toSubSystem.pow m).twist Lb.toSubSystem = _`.

Rewrite using `[hQ, hL]`. Conclude with `SubSystem.ext_sub hP`. Establish `hpows : ∀ (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ), ∃ P : FinGradedSub (S` using `k) (x := x) E, F.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n = P.tildeSys 0 := by`. Introduce `t`. Proceed by induction on `t with`.

Consider the case `zero`. Introduce `L n`. Take `⟨M, -, hM⟩` from `hE k Ω N x E F hF0`. Conclude with `⟨M, SubSystem.ext_sub fun I => (hM I).symm⟩`. Consider the case `succ t ih`.

Introduce `L n`. Take `⟨P, hP⟩` from `ih (fun j => L j.castSucc) (fun j => n j.castSucc)`. Take `⟨Q, hQ⟩` from `hpow (L (Fin.last t)) (n (Fin.last t))`. Take `⟨P', -, hP'⟩` from `hT k Ω N x E P Q`. Use `⟨P', ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(F.toSubSystem.twistPows t (fun j => (L j.castSucc).toSubSystem) (fun j => n j.castSucc)).twist ((L (Fin.last t)).toSubSystem.pow (n (Fin.last t))) = _`. Rewrite using `[hP, hQ]`. Conclude with `SubSystem.ext_sub hP'`. Take `⟨P, hP⟩` from `hpows t L n`. Rewrite using `[hP, ← hS k Ω N x E P c]`.

Conclude with `hF k Ω N x E P i c`.
-/
theorem SnapperFinite.proof (hE : Extension.Statement.{u, v, w}) (hEL : Extension.Statement.{u, w, w})
    (hT : TwistTilde.Statement.{u, v, w}) (hTL : TwistTilde.Statement.{u, w, w})
    (hS : TildeShift.Statement.{u, v, w}) (hF : TildeFiniteE.Statement.{u, v, w}) :
    SnapperFinite.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x E _ _ _ _ F hF0 t L n c i

  have hpow : ∀ (Lb : LineBundle k x) (m : ℕ), ∃ Q : FinGradedSub (S := k) (x := x) Ω,
      Lb.toSubSystem.pow m = Q.tildeSys 0 := by
    intro Lb m
    induction m with
    | zero =>
      refine ⟨coordGraded k x, ?_⟩
      change twistSys k x 0 = _
      rw [← coordGraded_tildeSys_twist (twistSys k x 0), SubSystem.twist_twistSys_zero]
    | succ m ih =>
      obtain ⟨Q, hQ⟩ := ih
      obtain ⟨QL, -, hQL⟩ := hEL k Ω N x Ω Lb.toSubFamily Lb.fg
      obtain ⟨P, -, hP⟩ := hTL k Ω N x Ω Q QL
      refine ⟨P, ?_⟩
      have hL : Lb.toSubSystem = QL.tildeSys 0 := SubSystem.ext_sub fun I => (hQL I).symm
      change (Lb.toSubSystem.pow m).twist Lb.toSubSystem = _
      rw [hQ, hL]
      exact SubSystem.ext_sub hP

  have hpows : ∀ (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ),
      ∃ P : FinGradedSub (S := k) (x := x) E,
        F.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n = P.tildeSys 0 := by
    intro t
    induction t with
    | zero =>
      intro L n
      obtain ⟨M, -, hM⟩ := hE k Ω N x E F hF0
      exact ⟨M, SubSystem.ext_sub fun I => (hM I).symm⟩
    | succ t ih =>
      intro L n
      obtain ⟨P, hP⟩ := ih (fun j => L j.castSucc) (fun j => n j.castSucc)
      obtain ⟨Q, hQ⟩ := hpow (L (Fin.last t)) (n (Fin.last t))
      obtain ⟨P', -, hP'⟩ := hT k Ω N x E P Q
      refine ⟨P', ?_⟩
      change (F.toSubSystem.twistPows t (fun j => (L j.castSucc).toSubSystem)
        (fun j => n j.castSucc)).twist ((L (Fin.last t)).toSubSystem.pow (n (Fin.last t))) = _
      rw [hP, hQ]
      exact SubSystem.ext_sub hP'
  obtain ⟨P, hP⟩ := hpows t L n
  rw [hP, ← hS k Ω N x E P c]
  exact hF k Ω N x E P i c

end

end GroundTheory.Heights₂.Heights.Kleiman
