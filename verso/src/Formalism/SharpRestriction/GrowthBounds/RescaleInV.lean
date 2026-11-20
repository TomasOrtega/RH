import Formalism.LocalToGlobal.CharacterGerms.RowTieDefs
import Formalism.LocalToGlobal.CharacterGerms.RowTieCartFB

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace SelfConjPoints

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

def pairSubst {τ : Type} (a b : κ → MvPowerSeries τ C) : Fin 2 × κ → MvPowerSeries τ C :=
  fun q => if q.1 = 0 then a q.2 else b q.2

def hAt (X : RawChart C d I κ) {τ : Type} (a b : κ → MvPowerSeries τ C) : MvPowerSeries τ C :=
  MvPowerSeries.subst (pairSubst a b) X.h

def ee (i j : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 j

def inV (j : Fin 2) (f : PowerSeries C) : MvPowerSeries (Fin 2) C :=
  PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin 2) C) f

def HH (X : RawChart C d I κ) (x z : κ → PowerSeries C) : MvPowerSeries (Fin 2) C :=
  hAt X (fun i => inV 0 (x i)) (fun i => inV 1 (z i))

def rs (j : Fin 2) (c : C) : MvPowerSeries (Fin 2) C →+* MvPowerSeries (Fin 2) C :=
  MvPowerSeries.rescale (fun i => if i = j then c else 1)

def rc (c : C) (γ : κ → PowerSeries C) : κ → PowerSeries C := fun i => PowerSeries.rescale c (γ i)

/- English proof (translation)
The claim follows from `MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _`.
-/
theorem hsX (j : Fin 2) : MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X j : MvPowerSeries (Fin 2) C)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _

/- English proof (translation)
The claim follows from `constantCoeff_subst_zero (fun _ => MvPowerSeries.constantCoeff_X _) hf`.
-/
theorem inV_cc (j : Fin 2) {f : PowerSeries C} (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (inV j f) = 0 :=
  constantCoeff_subst_zero (fun _ => MvPowerSeries.constantCoeff_X _) hf

/- English proof (translation)
Establish `hw : MvPowerSeries.HasSubst (w • MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) C)` using `MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by simp`. Establish `hc : MvPowerSeries.HasSubst (fun _ : Unit => (w j • PowerSeries.X : PowerSeries C))` using `MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => by show MvPowerSeries.constantCoeff (w j • (PowerSeries.X : PowerSeries C)) = 0`. Rewrite using `[MvPowerSeries.smul_eq_C_mul, map_mul, show MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries C) = 0 from MvPowerSeries.constantCoeff_X (), mul_zero]`. Unfold `inV`. Rewrite using `[MvPowerSeries.rescale_eq_subst, PowerSeries.rescale_eq_subst]`.

Unfold `PowerSeries.subst`. Rewrite using `[MvPowerSeries.subst_comp_subst_apply (hsX j) hw, MvPowerSeries.subst_comp_subst_apply hc (hsX j)]`. Use `congr 1`. Use function extensionality and compare the values at `u`. Rewrite using `[MvPowerSeries.subst_X hw, ← MvPowerSeries.coe_substAlgHom (hsX j), map_smul, MvPowerSeries.coe_substAlgHom (hsX j)]`.

Establish `h1 : MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X j : MvPowerSeries (Fin 2) C)) (PowerSeries.X : PowerSeries C) = MvPowerSeries.X j` using `MvPowerSeries.subst_X (hsX j) ()`. Rewrite using `[h1]`. Both sides reduce to the same expression.
-/
theorem rescale_inV (w : Fin 2 → C) (j : Fin 2) (f : PowerSeries C) :
    MvPowerSeries.rescale w (inV j f) = inV j (PowerSeries.rescale (w j) f) := by
  have hw : MvPowerSeries.HasSubst (w • MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) C) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by simp
  have hc : MvPowerSeries.HasSubst (fun _ : Unit => (w j • PowerSeries.X : PowerSeries C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => by
      show MvPowerSeries.constantCoeff (w j • (PowerSeries.X : PowerSeries C)) = 0
      rw [MvPowerSeries.smul_eq_C_mul, map_mul,
        show MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries C) = 0 from MvPowerSeries.constantCoeff_X (), mul_zero]
  unfold inV
  rw [MvPowerSeries.rescale_eq_subst, PowerSeries.rescale_eq_subst]
  unfold PowerSeries.subst
  rw [MvPowerSeries.subst_comp_subst_apply (hsX j) hw, MvPowerSeries.subst_comp_subst_apply hc (hsX j)]
  congr 1
  funext u
  rw [MvPowerSeries.subst_X hw, ← MvPowerSeries.coe_substAlgHom (hsX j), map_smul, MvPowerSeries.coe_substAlgHom (hsX j)]
  have h1 : MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X j : MvPowerSeries (Fin 2) C)) (PowerSeries.X : PowerSeries C) =
      MvPowerSeries.X j := MvPowerSeries.subst_X (hsX j) ()
  rw [h1]
  rfl

/- English proof (translation)
Establish `hP : MvPowerSeries.HasSubst (pairSubst (fun i => inV 0 (x i)) (fun i => inV 1 (z i)))`. Use `MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => ?_` and prove the remaining obligations. Unfold `pairSubst`. Use `split_ifs`. Conclude with `inV_cc 0 (hx q.2)`.

Conclude with `inV_cc 1 (hz q.2)`. Establish `hw : MvPowerSeries.HasSubst (w • MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) C)` using `MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by simp`. Unfold `HH hAt`. Rewrite using `[MvPowerSeries.rescale_eq_subst, MvPowerSeries.subst_comp_subst_apply hP hw]`. Use `congr 1`.

Use function extensionality and compare the values at `q`. Rewrite using `[← MvPowerSeries.rescale_eq_subst]`. Unfold `pairSubst rc`. Use `split_ifs`. Conclude with `rescale_inV w 0 (x q.2)`.

Conclude with `rescale_inV w 1 (z q.2)`.
-/
theorem rescale_HH (X : RawChart C d I κ) (x z : κ → PowerSeries C) (hx : ∀ i, PowerSeries.constantCoeff (x i) = 0)
    (hz : ∀ i, PowerSeries.constantCoeff (z i) = 0) (w : Fin 2 → C) :
    MvPowerSeries.rescale w (HH X x z) = HH X (rc (w 0) x) (rc (w 1) z) := by
  have hP : MvPowerSeries.HasSubst (pairSubst (fun i => inV 0 (x i)) (fun i => inV 1 (z i))) := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => ?_
    unfold pairSubst
    split_ifs
    · exact inV_cc 0 (hx q.2)
    · exact inV_cc 1 (hz q.2)
  have hw : MvPowerSeries.HasSubst (w • MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) C) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by simp
  unfold HH hAt
  rw [MvPowerSeries.rescale_eq_subst, MvPowerSeries.subst_comp_subst_apply hP hw]
  congr 1
  funext q
  rw [← MvPowerSeries.rescale_eq_subst]
  unfold pairSubst rc
  split_ifs
  · exact rescale_inV w 0 (x q.2)
  · exact rescale_inV w 1 (z q.2)

end SelfConjPoints

open SelfConjPoints in

/- English proof (translation)
Establish `e1 : ∀ y : κ → PowerSeries C, rc 1 y = y` using `fun y => by`. Use function extensionality and compare the values at `i`. Unfold `rc`. Rewrite using `[PowerSeries.rescale_one]`. Both sides reduce to the same expression.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `rs`. Rewrite using `[rescale_HH X x z hx hz]`. Simplify using `[e1]`. Unfold `rs`.

Rewrite using `[rescale_HH X x z hx hz]`. Simplify using `[e1]`.
-/
theorem r1sHResc (C : Type) [Field C] (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ]
    (X : RawChart C d I κ) (x z : κ → PowerSeries C) (hx : ∀ i, PowerSeries.constantCoeff (x i) = 0)
    (hz : ∀ i, PowerSeries.constantCoeff (z i) = 0) (c : C) :
    HH X (rc c x) z = rs 0 c (HH X x z) ∧ HH X x (rc c z) = rs 1 c (HH X x z) := by
  have e1 : ∀ y : κ → PowerSeries C, rc 1 y = y := fun y => by
    funext i; unfold rc; rw [PowerSeries.rescale_one]; rfl
  refine ⟨?_, ?_⟩
  · unfold rs
    rw [rescale_HH X x z hx hz]
    simp [e1]
  · unfold rs
    rw [rescale_HH X x z hx hz]
    simp [e1]

end Formalism.L2.FormalSeriesBounds
