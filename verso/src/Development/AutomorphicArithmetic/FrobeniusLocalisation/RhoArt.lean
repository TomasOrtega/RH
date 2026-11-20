import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffDefs
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.RdArith

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

/- English proof (translation)
Introduce `φ H f hf`. Rewrite using `[Formalism.HC.Der.Rd.rho_eq _ hf]`. Establish `h1` using `(H.art.ker.subgroupOf (H.unitsOne f)).card_mul_index`. Establish `h2 : (H.art.ker.subgroupOf (H.unitsOne f)).index = Nat.card (H.imgOne f)` using `Subgroup.relIndex_ker (H.unitsOne f) H.art`. Establish `h3 : Nat.card (H.unitsOne f) = (Formalism.HC.Der.Rd.KK H.condN f).card`.

Rewrite using `[← Nat.card_eq_finsetCard]`. Conclude with `Nat.card_congr (Equiv.subtypeEquivRight fun u => by`. Rewrite using `[Formalism.HC.Der.Rd.mem_KK, H.mem_unitsOne hf])`. Establish `h4 : Nat.card (H.art.ker.subgroupOf (H.unitsOne f)) = ((Formalism.HC.Der.Rd.KK H.condN f).filter fun u => u ∈ H.art.ker).card`. Rewrite using `[← Nat.card_eq_finsetCard]`.

Use `Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter (fun u => u ∈ H.unitsOne f) (fun u => u ∈ H.art.ker)).trans (Equiv.subtypeEquivRight fun u => ?_))` and prove the remaining obligations. Rewrite using `[Finset.mem_filter, Formalism.HC.Der.Rd.mem_KK, H.mem_unitsOne hf]`. Rewrite `h1` using `[h2, h3, h4]`. Establish `h5` using `Formalism.HC.Der.Rd.card_KK hf`. Rewrite `h5` using `[← h1]`.

Establish `h6` using `congrArg (Nat.cast : ℕ → ℝ) h5`. Move the coercions through the operations in `at h6`. Establish `hN : (H.condN.totient : ℝ) ≠ 0` using `by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos H.condN)).ne'`. Establish `hI : (Nat.card (H.imgOne f) : ℝ) ≠ 0` using `by exact_mod_cast Nat.card_pos.ne'`. Use `congr 1`.

Rewrite using `[div_eq_div_iff hN hI, one_mul, ← h6]`. Rewrite using `[mul_right_comm]`. Use `congr!`.
-/
theorem UpperTheory.HF.rho_art :
    ∀ {φ : Frame} (H : HostRaw φ) {f : ℕ}, f ∣ H.condN → Formalism.HC.Der.Rd.rho H.art.ker f = 1 - 1 / (Nat.card (H.imgOne f) : ℝ) := by
  intro φ H f hf
  classical
  rw [Formalism.HC.Der.Rd.rho_eq _ hf]
  have h1 := (H.art.ker.subgroupOf (H.unitsOne f)).card_mul_index
  have h2 : (H.art.ker.subgroupOf (H.unitsOne f)).index = Nat.card (H.imgOne f) :=
    Subgroup.relIndex_ker (H.unitsOne f) H.art
  have h3 : Nat.card (H.unitsOne f) = (Formalism.HC.Der.Rd.KK H.condN f).card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun u => by
      rw [Formalism.HC.Der.Rd.mem_KK, H.mem_unitsOne hf])
  have h4 : Nat.card (H.art.ker.subgroupOf (H.unitsOne f)) =
      ((Formalism.HC.Der.Rd.KK H.condN f).filter fun u => u ∈ H.art.ker).card := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter (fun u => u ∈ H.unitsOne f)
      (fun u => u ∈ H.art.ker)).trans (Equiv.subtypeEquivRight fun u => ?_))
    rw [Finset.mem_filter, Formalism.HC.Der.Rd.mem_KK, H.mem_unitsOne hf]
  rw [h2, h3, h4] at h1
  have h5 := Formalism.HC.Der.Rd.card_KK hf
  rw [← h1] at h5
  have h6 := congrArg (Nat.cast : ℕ → ℝ) h5
  push_cast at h6
  have hN : (H.condN.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos H.condN)).ne'
  have hI : (Nat.card (H.imgOne f) : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  congr 1
  rw [div_eq_div_iff hN hI, one_mul, ← h6]
  rw [mul_right_comm]
  congr!
