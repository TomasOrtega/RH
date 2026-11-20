import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ
open scoped Matrix

namespace GlobalTheory.ThetaTransform

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

abbrev VA (F : Type) [Field F] [NumberField F] (N : ℕ) : Type := (Fin N → AF F) × (Fin N → AF F)

def symV (w w' : VA F N) : AF F := w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2

def embR {κ : Type} (t : κ → mixedEmbedding.mixedSpace F) : κ → AF F :=
  fun i => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t i)) 0

def IsRealLine (M : ℝ →+ VA F N) : Prop := Continuous M ∧ ∀ t, fin (M t).1 = 0 ∧ fin (M t).2 = 0

def half (F : Type) [Field F] (N : ℕ) : Fin N → F := fun _ => 1 / 2

variable [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ)

def heisV (u : VA F N) (f : VA F N → ℂ) : VA F N → ℂ := fun w => ψ (⅟(2 : AF F) * symV w u) * f (w + u)

def thV (Φ : (Fin N → AF F) → ℂ) : VA F N → ℂ := fun w => GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ)

def invV (ν : Measure (AF F)) (𝓓 : Set (Fin N → AF F)) (f : VA F N → ℂ) : (Fin N → AF F) → ℂ :=
  fun x => ∫ y in 𝓓, f (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y))) ∂(muV N ν)

def QuasiV (f : VA F N → ℂ) : Prop :=
  ∀ (a b : Fin N → F) (w : VA F N), f ((rat a, rat b) + w) = ψ (-(⅟(2 : AF F) * symV (rat a, rat b) w)) * f w

def LevelV (f : VA F N → ℂ) : Prop :=
  ∃ U : AddSubgroup (VA F N), IsOpen (U : Set (VA F N)) ∧ ∀ u ∈ U, inf u.1 = 0 → inf u.2 = 0 → heisV ψ u f = f

abbrev ratSub (F : Type) [Field F] [NumberField F] (N : ℕ) : AddSubgroup (Fin N → AF F) :=
  AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))

/- English proof (translation)
Use `invOf_eq_right_inv ?_` and prove the remaining obligations. Rewrite using `[← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]`. Simplify using the standard rewrite rules.
-/
theorem invOf_two_eq : ⅟(2 : AF F) = algebraMap F (AF F) (1 / 2) := by
  refine invOf_eq_right_inv ?_
  rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
  simp

omit [Invertible (2 : AF F)] in
/- English proof (translation)
Simplify using `[Bd, half, dotProduct]`.
-/
theorem Bd_half (u u' : Fin N → AF F) : Bd (AF F) (half F N) u u' = u ⬝ᵥ u' := by
  simp [Bd, half, dotProduct]

omit [NumberField F] [Invertible (2 : AF F)] in
/- English proof (translation)
Simplify using `[half]`.
-/
theorem half_ne_zero [CharZero F] (l : Fin N) : half F N l ≠ 0 := by
  simp [half]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Rewrite using `[GlobalTheory.WeilM.schr, rho, Bd_half, Bd_half, invOf_two_eq]`.
-/
theorem schr_eq_rho (w : VA F N) (Φ : (Fin N → AF F) → ℂ) :
    GlobalTheory.WeilM.schr ψ w Φ = rho ψ (half F N) w.1 w.2 Φ := by
  funext x
  rw [GlobalTheory.WeilM.schr, rho, Bd_half, Bd_half, invOf_two_eq]

/- English proof (translation)
Rewrite using `[thV, schr_eq_rho]`. Both sides reduce to the same expression.
-/
theorem thV_eq_th (Φ : (Fin N → AF F) → ℂ) (w : VA F N) : thV ψ Φ w = th (rho ψ (half F N) w.1 w.2 Φ) := by
  rw [thV, schr_eq_rho]
  rfl

/- English proof (translation)
Rewrite using `[← add_mul, invOf_two_add_invOf_two, one_mul]`.
-/
theorem two_mul_invOf (a : AF F) : ⅟(2 : AF F) * a + ⅟(2 : AF F) * a = a := by
  rw [← add_mul, invOf_two_add_invOf_two, one_mul]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add, ← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc]`. Use `congr 2`. Simplify using `only [symV, add_dotProduct, dotProduct_add]`. Take the linear combination `(-1 : AF F) * two_mul_invOf (w.1 ⬝ᵥ u.2)`.
-/
theorem schr_schr (w u : VA F N) (Φ : (Fin N → AF F) → ℂ) :
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.WeilM.schr ψ u Φ) = ψ (⅟(2 : AF F) * symV w u) • GlobalTheory.WeilM.schr ψ (w + u) Φ := by
  funext x
  simp only [GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add, ← mul_assoc,
    ← AddChar.map_add_eq_mul, add_assoc]
  congr 2
  simp only [symV, add_dotProduct, dotProduct_add]
  linear_combination (-1 : AF F) * two_mul_invOf (w.1 ⬝ᵥ u.2)

/- English proof (translation)
Use function extensionality and compare the values at `w`. Rewrite using `[thV, schr_schr, heisV, thV]`. Conclude with `tsum_mul_left`.
-/
theorem thV_schr (u : VA F N) (Φ : (Fin N → AF F) → ℂ) : thV ψ (GlobalTheory.WeilM.schr ψ u Φ) = heisV ψ u (thV ψ Φ) := by
  funext w
  rw [thV, schr_schr, heisV, thV]
  exact tsum_mul_left

/- English proof (translation)
Introduce `a b w`. Simplify using `only [thV, GlobalTheory.WeilM.thetaSum]`. Rewrite using `[← tsum_mul_left, ← (Equiv.addRight a).tsum_eq (fun ξ : Fin N → F => ψ (-(⅟(2 : AF F) * symV (rat a, rat b) w)) * GlobalTheory.WeilM.schr ψ w Φ fun i => algebraMap F (AF F) (ξ i))]`. Use `tsum_congr fun ξ => ?_` and prove the remaining obligations. Establish `e1 : (fun i => algebraMap F (AF F) ((Equiv.addRight a ξ) i)) = rat ξ + rat a`.

Use function extensionality and compare the values at `i`. Simplify using `[rat]`. Establish `e2 : (fun i => algebraMap F (AF F) (ξ i)) = rat ξ` using `rfl`. Establish `e3 : ∀ c d : Fin N → F, rat c ⬝ᵥ rat d = algebraMap F (AF F) (c ⬝ᵥ d)` using `fun c d => by`. Simplify using `[rat, dotProduct]`.

Rewrite using `[e1, e2]`. Simplify using `only [GlobalTheory.WeilM.schr, Prod.fst_add, Prod.snd_add, ← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc]`. Use `congr 1`. Establish `h1` using `hψ (ξ ⬝ᵥ b + 1 / 2 * (a ⬝ᵥ b))`. Rewrite using `[← mul_one (ψ (-(⅟(2 : AF F) * symV (rat a, rat b) w) + _)), ← h1, ← AddChar.map_add_eq_mul]`.

Use `congr 1`. Rewrite using `[map_add, map_mul, ← invOf_two_eq, ← e3, ← e3]`. Simplify using `only [symV, add_dotProduct, dotProduct_add]`. Take the linear combination `two_mul_invOf (rat a ⬝ᵥ w.2)`.
-/
theorem quasiV_thV (hψ : ∀ a : F, ψ (algebraMap F (AF F) a) = 1) (Φ : (Fin N → AF F) → ℂ) : QuasiV ψ (thV ψ Φ) := by
  intro a b w
  simp only [thV, GlobalTheory.WeilM.thetaSum]
  rw [← tsum_mul_left, ← (Equiv.addRight a).tsum_eq (fun ξ : Fin N → F => ψ (-(⅟(2 : AF F) * symV (rat a, rat b) w)) *
    GlobalTheory.WeilM.schr ψ w Φ fun i => algebraMap F (AF F) (ξ i))]
  refine tsum_congr fun ξ => ?_
  have e1 : (fun i => algebraMap F (AF F) ((Equiv.addRight a ξ) i)) = rat ξ + rat a := by
    funext i; simp [rat]
  have e2 : (fun i => algebraMap F (AF F) (ξ i)) = rat ξ := rfl
  have e3 : ∀ c d : Fin N → F, rat c ⬝ᵥ rat d = algebraMap F (AF F) (c ⬝ᵥ d) := fun c d => by
    simp [rat, dotProduct]
  rw [e1, e2]
  simp only [GlobalTheory.WeilM.schr, Prod.fst_add, Prod.snd_add, ← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc]
  congr 1
  have h1 := hψ (ξ ⬝ᵥ b + 1 / 2 * (a ⬝ᵥ b))
  rw [← mul_one (ψ (-(⅟(2 : AF F) * symV (rat a, rat b) w) + _)), ← h1, ← AddChar.map_add_eq_mul]
  congr 1
  rw [map_add, map_mul, ← invOf_two_eq, ← e3, ← e3]
  simp only [symV, add_dotProduct, dotProduct_add]
  linear_combination two_mul_invOf (rat a ⬝ᵥ w.2)

end GlobalTheory.ThetaTransform

end
