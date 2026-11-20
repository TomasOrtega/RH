import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.AffineHodgeIsomorphisms.IsFormT
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.TopRes
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.ZarAbs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

noncomputable section

namespace GlobalTheory.CompanionTheory.HodgeFormTop

open CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.HT CrystallineSemistableComparison.Om.L2 CrystallineSemistableComparison.Pb

section
variable {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

def omEq (a : ℕ) : CrystallineSemistableComparison.Onto.Om K (CrystallineSemistableComparison.Onto.Sec q ⊤) a ≃ₗ[K] OmU q ⊤ a := LinearEquiv.refl K (OmU q ⊤ a)

abbrev resTop (a : ℕ) := CH.Mor.restrict (G q a) (inU q ⊤).ι

/- English proof (translation)
The claim follows from `(topRes_pf K _ (G q a) (inU q ⊤) ⊥ (fun T => inTop q T) n).1`.
-/
theorem resTop_pullC_bij (a n : ℕ) : Function.Bijective ((resTop q a).pullC n) :=
  (topRes_pf K _ (G q a) (inU q ⊤) ⊥ (fun T => inTop q T) n).1

/- English proof (translation)
The claim follows from `CrystallineSemistableComparison.P.mapH_bij _ (fun m => resTop_pullC_bij q a m) n`.
-/
theorem resTop_bij (a n : ℕ) : Function.Bijective ((resTop q a).pull n) :=
  CrystallineSemistableComparison.P.mapH_bij _ (fun m => resTop_pullC_bij q a m) n

def resTopEquiv (a : ℕ) : Hdg q a a ≃ₗ[K] HV q ⊤ a a :=
  LinearEquiv.ofBijective ((resTop q a).pull a) (resTop_bij q a a)

def LiftsT.toTop (Λ : LiftsT q) : Lifts q ⊤ where
  v T g := Λ.v T.obj g
  hv T g := Λ.hv T.obj g

/- English proof (translation)
Introduce `Λ`. Take `⟨f, hf, hc, hz⟩` from `h (LiftsT.toTop q Λ)`. Take `⟨z, rfl⟩` from `(resTop_pullC_bij q a a).2 f`. Establish `hd : CH.d (G q a) a z = 0`. Apply `(resTop_pullC_bij q a (a + 1)).1` to reduce the goal to its premises.

Rewrite using `[map_zero, ← CH.Mor.d_pullC]`. Conclude with `hf`. Establish `hcz : (resTopEquiv q a) ((CH.cx (G q a)).cls z hd) = c`. Rewrite using `[hc]`. Conclude with `CrystallineSemistableComparison.P.mapH_cls (resTop q a).hom a z hd _`.

Use `⟨z, hd, ?_, fun t => ?_⟩` and prove the remaining obligations. Rewrite using `[← hcz, LinearEquiv.symm_apply_apply]`. Conclude with `hz (t ⋙ (inU q ⊤).lift (𝟭 _) (fun T => inTop q T))`.
-/
theorem isFormT_of_isForm {a : ℕ} (g₀ : Γ(X, ⊤)) (g : Fin a → Γ(X, ⊤)) (c : HV q ⊤ a a)
    (h : IsForm q ⊤ (a := a) g₀ g c) : IsFormT q g₀ g ((resTopEquiv q a).symm c) := by
  intro Λ
  obtain ⟨f, hf, hc, hz⟩ := h (LiftsT.toTop q Λ)
  obtain ⟨z, rfl⟩ := (resTop_pullC_bij q a a).2 f
  have hd : CH.d (G q a) a z = 0 := by
    apply (resTop_pullC_bij q a (a + 1)).1
    rw [map_zero, ← CH.Mor.d_pullC]
    exact hf
  have hcz : (resTopEquiv q a) ((CH.cx (G q a)).cls z hd) = c := by
    rw [hc]
    exact CrystallineSemistableComparison.P.mapH_cls (resTop q a).hom a z hd _
  refine ⟨z, hd, ?_, fun t => ?_⟩
  · rw [← hcz, LinearEquiv.symm_apply_apply]
  · exact hz (t ⋙ (inU q ⊤).lift (𝟭 _) (fun T => inTop q T))

end

/- English proof (translation)
Introduce `K _ X q a ⟨e, he, hb⟩`. Use `⟨((resTopEquiv q a).trans (LinearEquiv.ofBijective e hb).symm).trans (omEq q a), fun g₀ g => ?_⟩` and prove the remaining obligations. Conclude with `isFormT_of_isForm q g₀ g _ (he g₀ g)`.
-/
theorem main : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (a : ℕ),
    (∃ e : CrystallineSemistableComparison.Onto.Om K (CrystallineSemistableComparison.Onto.Sec q ⊤) a →ₗ[K] CrystallineSemistableComparison.Onto.HV q ⊤ a a, CrystallineSemistableComparison.Onto.IsOm q ⊤ a e ∧ Function.Bijective e) →
    ∃ e' : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a, CrystallineSemistableComparison.Om.L2.IsOmT q a e' := by
  intro K _ X q a ⟨e, he, hb⟩
  refine ⟨((resTopEquiv q a).trans (LinearEquiv.ofBijective e hb).symm).trans (omEq q a), fun g₀ g => ?_⟩
  exact isFormT_of_isForm q g₀ g _ (he g₀ g)

end GlobalTheory.CompanionTheory.HodgeFormTop
