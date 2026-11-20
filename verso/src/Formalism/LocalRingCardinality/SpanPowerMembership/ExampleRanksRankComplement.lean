import Formalism.LocalRingCardinality.Params
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameCyclicGenerator

namespace Formalism.BasicNotions.Examples₂

noncomputable def R0 : Formalism.BasicNotions.Ranks where
  toFrame := Formalism.HC.cyclicFrame 2
  k := 8
  m := 2
  t := 15
  k_even := ⟨4, rfl⟩
  m_even := ⟨1, rfl⟩
  t_odd := ⟨7, rfl⟩
  two_le_m := le_refl _
  m_add_three_le_k := by norm_num
  rank_add_five_le := by norm_num
  three_m_lt_t := by norm_num
  m_le_f := (by norm_num : 2 ≤ 2 * 2 ^ 2)
  f_le_k := (by norm_num : 2 * 2 ^ 2 ≤ 8)
  m_sq_le_N := by norm_num

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem exampleRanks_e : R0.e = 2 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem exampleRanks_k : R0.k = 8 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem exampleRanks_m : R0.m = 2 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem exampleRanks_t : R0.t = 15 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem exampleRanks_f : R0.f = 8 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem exampleRanks_n : R0.n = 4 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem exampleRanks_order : R0.ord = 4 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem exampleRanks_frame : R0.toFrame = Formalism.HC.cyclicFrame 2 := rfl
/- English proof (translation)
Use `show (Formalism.HC.frameCyc 2 1).n0 = 4`. Rewrite using `[Formalism.HC.frameCyclic_order]`. Conclude with `ZMod.addOrderOf_one _`.
-/
theorem exampleRanks_baseRank : R0.n0 = 4 := by
  show (Formalism.HC.frameCyc 2 1).n0 = 4
  rw [Formalism.HC.frameCyclic_order]
  exact ZMod.addOrderOf_one _
/- English proof (translation)
Use `show R0.toFrame.ord / R0.toFrame.n0 = 1`. Establish `h1 : R0.toFrame.n0 = 4` using `exampleRanks_baseRank`. Establish `h2 : R0.toFrame.ord = 4` using `exampleRanks_order`. Rewrite using `[h1, h2]`.
-/
theorem exampleRanks_o : R0.o = 1 := by
  show R0.toFrame.ord / R0.toFrame.n0 = 1
  have h1 : R0.toFrame.n0 = 4 := exampleRanks_baseRank
  have h2 : R0.toFrame.ord = 4 := exampleRanks_order
  rw [h1, h2]
/- English proof (translation)
The claim follows from `Formalism.HC.frameCyc_h_injective 2 1`.
-/
theorem exampleRanks_h_injective : Function.Injective R0.h :=
  Formalism.HC.frameCyc_h_injective 2 1
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem exampleRanks_r : R0.r = 9 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem exampleRanks_wittIndex : R0.rS = 0 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem exampleRanks_vertexCount : R0.nV = 24 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem exampleRanks_N_formula (j : ℕ) : R0.N j = 8 + j * 16 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem exampleRanks_rankComplement : R0.rankX' = 39 := rfl

end Formalism.BasicNotions.Examples₂
