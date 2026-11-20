import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ConjugatorMemUnipotent
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IndexEqRelIndex

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut
  Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) {p : PlF D}

/- English proof (translation)
Introduce `x y h` and use `by rw [← tauU_tauU p x, ← tauU_tauU p y, h]`.
-/
theorem tauU_inj : Function.Injective (tauU p) := fun x y h => by
  rw [← tauU_tauU p x, ← tauU_tauU p y, h]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => by have := tau_mem_KP M p h; rwa [tau_tau] at this, fun h => tau_mem_KP M p h⟩`.
-/
theorem tau_KP_iff (x : GG p) : tau p x ∈ KP M p ↔ x ∈ KP M p :=
  ⟨fun h => by have := tau_mem_KP M p h; rwa [tau_tau] at this, fun h => tau_mem_KP M p h⟩

section Parts

variable (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U)
  (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (hB : BaseAt M δ u u' w p a)

def gU : UP p := tauU p ⟨g0 M δ hA L U hL hU, conjugator_mem_unipotent M δ hA L U hL hU⟩ * hB.choose

/- English proof (translation)
Rewrite using `[XP_eq M δ u u' w hA L U hL hU, phi_smul p δ _ _ w (conjugator_mem_unipotent M δ hA L U hL hU), hB.choose_spec.1]`. Use `show ((tau p (g0 M δ hA L U hL hU) * (hB.choose : GG p)) : GG p) • a.mat = _`. Rewrite using `[mul_smul]`.
-/
theorem gU_smul : ((gU M δ u u' w hA L U hL hU a hB : UP p) : GG p) • a.mat =
    phi p δ (D.mem u).A.T (D.mem u').A.T w (XP M δ u u' w L U) := by
  rw [XP_eq M δ u u' w hA L U hL hU, phi_smul p δ _ _ w (conjugator_mem_unipotent M δ hA L U hL hU), hB.choose_spec.1]
  show ((tau p (g0 M δ hA L U hL hU) * (hB.choose : GG p)) : GG p) • a.mat = _
  rw [mul_smul]

/- English proof (translation)
Use `show (x : GG p) ∈ KP M p ∧ (x : GG p) • XP M δ u u' (p := p) w L U = XP M δ u u' (p := p) w L U ↔ tau p x ∈ KP M p ∧ (tauU p x : UP p) • ((gU M δ u u' w hA L U hL hU a hB : UP p) • a.mat) = (gU M δ u u' w hA L U hL hU a hB : UP p) • a.mat`. Rewrite using `[tau_KP_iff]`. Apply `and_congr Iff.rfl` to reduce the goal to its premises. Establish `e : ∀ y : UP p, (y • ((gU M δ u u' w hA L U hL hU a hB : UP p) • a.mat) : MP p) = (y : GG p) • (((gU M δ u u' w hA L U hL hU a hB : UP p) : GG p) • (a.mat : MP p))` using `fun y => rfl`. Establish `e2 : ((gU M δ u u' w hA L U hL hU a hB : UP p) • (a.mat : MP p) : MP p) = ((gU M δ u u' w hA L U hL hU a hB : UP p) : GG p) • (a.mat : MP p)` using `rfl`.

Rewrite using `[e2, gU_smul]`. Prove the components needed by the constructor for the conclusion. Introduce `h show tau p (x : GG p) • phi p δ (D.mem u).A.T (D.mem u').A.T w (XP M δ u u' (p := p) w L U) = phi p δ (D.mem u).A.T (D.mem u').A.T w (XP M δ u u' (p := p) w L U)`. Rewrite using `[← phi_smul p δ _ _ w x.2, h]`. Introduce `h`.

Apply `phi_inj p δ (D.mem u).A.T (D.mem u').A.T w` to reduce the goal to its premises. Rewrite using `[phi_smul p δ _ _ w x.2]`. Conclude with `h`.
-/
theorem mem_H_iff (x : UP p) :
    (x : GG p) ∈ KP M p ⊓ StabX p (XP M δ u u' w L U) ↔
      tauU p x ∈ CountAb.Hs a.mat (KU M p) (gU M δ u u' w hA L U hL hU a hB) := by
  show (x : GG p) ∈ KP M p ∧ (x : GG p) • XP M δ u u' (p := p) w L U = XP M δ u u' (p := p) w L U ↔
    tau p x ∈ KP M p ∧ (tauU p x : UP p) • ((gU M δ u u' w hA L U hL hU a hB : UP p) • a.mat) =
      (gU M δ u u' w hA L U hL hU a hB : UP p) • a.mat
  rw [tau_KP_iff]
  apply and_congr Iff.rfl
  have e : ∀ y : UP p, (y • ((gU M δ u u' w hA L U hL hU a hB : UP p) • a.mat) : MP p) =
      (y : GG p) • (((gU M δ u u' w hA L U hL hU a hB : UP p) : GG p) • (a.mat : MP p)) := fun y => rfl
  have e2 : ((gU M δ u u' w hA L U hL hU a hB : UP p) • (a.mat : MP p) : MP p) =
      ((gU M δ u u' w hA L U hL hU a hB : UP p) : GG p) • (a.mat : MP p) := rfl
  rw [e2, gU_smul]
  constructor
  · intro h
    show tau p (x : GG p) • phi p δ (D.mem u).A.T (D.mem u').A.T w (XP M δ u u' (p := p) w L U) =
      phi p δ (D.mem u).A.T (D.mem u').A.T w (XP M δ u u' (p := p) w L U)
    rw [← phi_smul p δ _ _ w x.2, h]
  · intro h
    apply phi_inj p δ (D.mem u).A.T (D.mem u').A.T w
    rw [phi_smul p δ _ _ w x.2]
    exact h

end Parts

end Formalism.L2.SG.Pf.CountAt
