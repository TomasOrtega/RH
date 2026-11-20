import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfQuad
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.HL
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BBTie

namespace GlobalTheory.DiffLoc

/- English proof (translation)
Unfold `ddS`. Rewrite using `[Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.map_eq_bot_iff_of_injective]`. Conclude with `differentIdeal_ne_bot`. Conclude with `FaithfulSMul.algebraMap_injective _ _`.
-/
theorem ddS_ne (D : D7) : ddS D ≠ 0 := by
  unfold ddS
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.map_eq_bot_iff_of_injective]
  · exact differentIdeal_ne_bot
  · exact FaithfulSMul.algebraMap_injective _ _

/- English proof (translation)
Introduce `D Z n hn y`. Set `a : Fin (D.R.rS + 1)` to `⟨D.R.rS - n, by omega⟩`. Establish `he : ((D.R.rS : ℤ) - ((a : ℕ) : ℤ)) = n` using `by show ((D.R.rS : ℤ) - ((D.R.rS - n : ℕ) : ℤ)) = n`. Rewrite using `[Nat.cast_sub hn]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hspan : ∀ p : PlF D, Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' ((ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E)) = Submodule.span (Z.M p).L.O {frFac Z.δ p a}`. Introduce `p`. Establish `h` using `locDiffC_holds D Z p a`. Rewrite `h` using `[he]`. Conclude with `h`.

Establish `hf : ∀ p : PlF D, frFac Z.δ p a * btT Z p ^ n = 1`. Introduce `p`. Rewrite using `[bt_frFac_eq Z p a]`. Establish `hk : D.R.rS - a.val = n` using `by show D.R.rS - (D.R.rS - n) = n; omega`. Rewrite using `[hk]`.

Use `set U := (bt_T_unit Z p).unit`. Establish `hU : (U : (D.s.atP p).Ep) = btT Z p` using `IsUnit.unit_spec _`. Rewrite using `[← hU, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one]`. Establish `hinv : ∀ z : D.host.E, z ∈ (ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ↔ ∀ d ∈ ddS D ^ n, z * d ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)`. Introduce `z`.

Rewrite using `[zpow_neg, zpow_natCast, FractionalIdeal.mem_inv_iff (pow_ne_zero n (ddS_ne D))]`. Prove the components needed by the constructor for the conclusion. Introduce `hy p`. Establish `hm : (D.s.atP p).ιE y ∈ Submodule.span (Z.M p).L.O {frFac Z.δ p a}`. Rewrite using `[← hspan p]`.

Conclude with `Submodule.subset_span ⟨y, hy, rfl⟩`. Take `⟨o, ho⟩` from `Submodule.mem_span_singleton.1 hm`. Express the relevant statement in the definitionally equal form `(D.s.atP p).ιE y * btT Z p ^ n ∈ (Z.M p).L.O`. Rewrite using `[← ho, Subring.smul_def, smul_eq_mul, mul_assoc, hf p, mul_one]`. Conclude with `o.2`.

Introduce `h`. Rewrite using `[hinv]`. Introduce `d hd`. Rewrite using `[FractionalIdeal.mem_one_iff]`. Establish `hloc : ∀ p : PlF D, (D.s.atP p).ιE (y * d) ∈ (Z.M p).L.O`.

Introduce `p`. Establish `hmem : ∀ x ∈ Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' ((ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E)), (D.s.atP p).ιE d * x ∈ (Z.M p).L.O`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨z, hz, rfl⟩` from `hx`. Take `⟨o, ho⟩` from `(FractionalIdeal.mem_one_iff _).1 ((hinv z).1 hz d hd)`. Rewrite using `[← map_mul, mul_comm, ← ho]`. Conclude with `bt_iota_int Z p o`. Consider the case `zero => rw [mul_zero]`.

Conclude with `Subring.zero_mem _`. Consider the case `add x z _ _ hx hz => rw [mul_add]`. Conclude with `add_mem hx hz`. Consider the case `smul o x _ hx => rw [Subring.smul_def, smul_eq_mul, mul_left_comm]`. Conclude with `mul_mem o.2 hx`.

Establish `hdf : (D.s.atP p).ιE d * frFac Z.δ p a ∈ (Z.M p).L.O` using `hmem _ (by rw [hspan p]; exact Submodule.subset_span (Set.mem_singleton _))`. Establish `hyp : (D.s.atP p).ιE y * btT Z p ^ n ∈ (Z.M p).L.O` using `h p`. Establish `e : (D.s.atP p).ιE (y * d) = ((D.s.atP p).ιE y * btT Z p ^ n) * ((D.s.atP p).ιE d * frFac Z.δ p a)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hf p, mul_one, map_mul]`.

Use `_ = _ := by ring`. Rewrite using `[e]`. Conclude with `mul_mem hyp hdf`. Take `⟨o, ho⟩` from `((GlobalTheory.HL.PlacesInt.integers_local (placesOf Z)).1 (y * d)).1 hloc`. Conclude with `⟨o, ho⟩`.
-/
theorem mem_ddPow_neg_iff : ∀ (D : D7) (Z : LocDat D) (n : ℕ), n ≤ D.R.rS → ∀ y : D.host.E,
    y ∈ (ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ↔
      ∀ p : PlF D, (D.s.atP p).ιE y * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) *
        (D.s.atP p).ιE (uP p : D.host.E)) ^ n ∈ (Z.M p).L.O := by
  intro D Z n hn y
  let a : Fin (D.R.rS + 1) := ⟨D.R.rS - n, by omega⟩
  have he : ((D.R.rS : ℤ) - ((a : ℕ) : ℤ)) = n := by
    show ((D.R.rS : ℤ) - ((D.R.rS - n : ℕ) : ℤ)) = n
    rw [Nat.cast_sub hn]; ring
  have hspan : ∀ p : PlF D, Submodule.span (Z.M p).L.O ((D.s.atP p).ιE ''
      ((ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E)) =
      Submodule.span (Z.M p).L.O {frFac Z.δ p a} := by
    intro p
    have h := locDiffC_holds D Z p a
    rw [he] at h
    exact h
  have hf : ∀ p : PlF D, frFac Z.δ p a * btT Z p ^ n = 1 := by
    intro p
    rw [bt_frFac_eq Z p a]
    have hk : D.R.rS - a.val = n := by show D.R.rS - (D.R.rS - n) = n; omega
    rw [hk]
    set U := (bt_T_unit Z p).unit
    have hU : (U : (D.s.atP p).Ep) = btT Z p := IsUnit.unit_spec _
    rw [← hU, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one]
  have hinv : ∀ z : D.host.E, z ∈ (ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ↔
      ∀ d ∈ ddS D ^ n, z * d ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    intro z
    rw [zpow_neg, zpow_natCast, FractionalIdeal.mem_inv_iff (pow_ne_zero n (ddS_ne D))]
  constructor
  · intro hy p
    have hm : (D.s.atP p).ιE y ∈ Submodule.span (Z.M p).L.O {frFac Z.δ p a} := by
      rw [← hspan p]; exact Submodule.subset_span ⟨y, hy, rfl⟩
    obtain ⟨o, ho⟩ := Submodule.mem_span_singleton.1 hm
    change (D.s.atP p).ιE y * btT Z p ^ n ∈ (Z.M p).L.O
    rw [← ho, Subring.smul_def, smul_eq_mul, mul_assoc, hf p, mul_one]
    exact o.2
  · intro h
    rw [hinv]
    intro d hd
    rw [FractionalIdeal.mem_one_iff]
    have hloc : ∀ p : PlF D, (D.s.atP p).ιE (y * d) ∈ (Z.M p).L.O := by
      intro p
      have hmem : ∀ x ∈ Submodule.span (Z.M p).L.O ((D.s.atP p).ιE ''
          ((ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E)),
          (D.s.atP p).ιE d * x ∈ (Z.M p).L.O := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨z, hz, rfl⟩ := hx
          obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 ((hinv z).1 hz d hd)
          rw [← map_mul, mul_comm, ← ho]
          exact bt_iota_int Z p o
        | zero => rw [mul_zero]; exact Subring.zero_mem _
        | add x z _ _ hx hz => rw [mul_add]; exact add_mem hx hz
        | smul o x _ hx => rw [Subring.smul_def, smul_eq_mul, mul_left_comm]; exact mul_mem o.2 hx
      have hdf : (D.s.atP p).ιE d * frFac Z.δ p a ∈ (Z.M p).L.O :=
        hmem _ (by rw [hspan p]; exact Submodule.subset_span (Set.mem_singleton _))
      have hyp : (D.s.atP p).ιE y * btT Z p ^ n ∈ (Z.M p).L.O := h p
      have e : (D.s.atP p).ιE (y * d) =
          ((D.s.atP p).ιE y * btT Z p ^ n) * ((D.s.atP p).ιE d * frFac Z.δ p a) := by
        calc (D.s.atP p).ιE (y * d) = (D.s.atP p).ιE y * (D.s.atP p).ιE d * (frFac Z.δ p a * btT Z p ^ n) := by
              rw [hf p, mul_one, map_mul]
          _ = _ := by ring
      rw [e]
      exact mul_mem hyp hdf
    obtain ⟨o, ho⟩ := ((GlobalTheory.HL.PlacesInt.integers_local (placesOf Z)).1 (y * d)).1 hloc
    exact ⟨o, ho⟩

end GlobalTheory.DiffLoc
