import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinDecomp

section Quot

variable {V : Type} [AddCommGroup V]

abbrev mLat (m : ℕ) (Λ : AddSubgroup V) : AddSubgroup V := Λ.map (nsmulAddMonoidHom m)

abbrev Qm (m : ℕ) (Λ : AddSubgroup V) : Type := Λ ⧸ (mLat m Λ).addSubgroupOf Λ

def repm {m : ℕ} {Λ : AddSubgroup V} (q : Qm m Λ) : V := ((Quotient.out q : Λ) : V)

/- English proof (translation)
Simplify using `[mLat]`.
-/
theorem mem_mLat {m : ℕ} {Λ : AddSubgroup V} {x : V} : x ∈ mLat m Λ ↔ ∃ l ∈ Λ, m • l = x := by
  simp [mLat]

/- English proof (translation)
The claim follows from `(Quotient.out q : Λ).2`.
-/
theorem repm_mem {m : ℕ} {Λ : AddSubgroup V} (q : Qm m Λ) : repm q ∈ Λ := (Quotient.out q : Λ).2

/- English proof (translation)
Establish `: (⟨repm q, repm_mem q⟩ : Λ) = Quotient.out q` using `rfl`. Rewrite using `[this]`. Conclude with `QuotientAddGroup.out_eq' q`.
-/
theorem mk_repm {m : ℕ} {Λ : AddSubgroup V} (q : Qm m Λ) :
    (QuotientAddGroup.mk (⟨repm q, repm_mem q⟩ : Λ) : Qm m Λ) = q := by
  have : (⟨repm q, repm_mem q⟩ : Λ) = Quotient.out q := rfl
  rw [this]
  exact QuotientAddGroup.out_eq' q

/- English proof (translation)
Rewrite `h` using `[QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]`. Simplify `h` using `[sub_eq_neg_add]`.
-/
theorem sub_mem_of_mk_eq {m : ℕ} {Λ : AddSubgroup V} {a b : V} (ha : a ∈ Λ) (hb : b ∈ Λ)
    (h : (QuotientAddGroup.mk (⟨a, ha⟩ : Λ) : Qm m Λ) = QuotientAddGroup.mk (⟨b, hb⟩ : Λ)) : b - a ∈ mLat m Λ := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h
  simpa [sub_eq_neg_add] using h

/- English proof (translation)
The claim follows from `sub_mem_of_mk_eq (m := m) ha (repm_mem _) (mk_repm _).symm`.
-/
theorem repm_mk_sub {m : ℕ} {Λ : AddSubgroup V} {a : V} (ha : a ∈ Λ) :
    repm (QuotientAddGroup.mk (⟨a, ha⟩ : Λ) : Qm m Λ) - a ∈ mLat m Λ :=
  sub_mem_of_mk_eq (m := m) ha (repm_mem _) (mk_repm _).symm

/- English proof (translation)
Use `sub_mem_of_mk_eq (m := m) (Λ.add_mem (repm_mem q) (repm_mem q')) (repm_mem (q + q')) ?_` and prove the remaining obligations. Rewrite using `[mk_repm]`. Use `conv_rhs => rw [← mk_repm q, ← mk_repm q']`. Both sides reduce to the same expression.
-/
theorem repm_add_sub {m : ℕ} {Λ : AddSubgroup V} (q q' : Qm m Λ) :
    repm (q + q') - (repm q + repm q') ∈ mLat m Λ := by
  refine sub_mem_of_mk_eq (m := m) (Λ.add_mem (repm_mem q) (repm_mem q')) (repm_mem (q + q')) ?_
  rw [mk_repm]
  conv_rhs => rw [← mk_repm q, ← mk_repm q']
  rfl

/- English proof (translation)
Establish `h` using `repm_mk_sub (m := m) (Λ := Λ) Λ.zero_mem`. Establish `h0 : (QuotientAddGroup.mk (⟨0, Λ.zero_mem⟩ : Λ) : Qm m Λ) = 0` using `rfl`. Rewrite `h` using `[h0, sub_zero]`. Conclude with `h`.
-/
theorem repm_zero_mem {m : ℕ} {Λ : AddSubgroup V} : repm (0 : Qm m Λ) ∈ mLat m Λ := by
  have h := repm_mk_sub (m := m) (Λ := Λ) Λ.zero_mem
  have h0 : (QuotientAddGroup.mk (⟨0, Λ.zero_mem⟩ : Λ) : Qm m Λ) = 0 := rfl
  rw [h0, sub_zero] at h
  exact h

end Quot

variable {D : D7}

def lamE (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (x : WO S T) : ℂ :=
  ψ (symplOH S T (e • x) (cA D e • x))

end GlobalTheory.FinDecomp

end
