import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.CanonOrder

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

def lineSetoid : Setoid (IrrGL k) where
  r x y := ∃ m : ℤ, y = x.nu m
  iseqv :=
    { refl := fun x => ⟨0, by simp⟩
      symm := by
        rintro x _ ⟨m, rfl⟩
        exact ⟨-m, by simp⟩
      trans := by
        rintro x _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
        exact ⟨m + n, by simp⟩ }

variable (k) in

def Line : Type 1 := Quotient (lineSetoid k)

instance lineLinearOrder : LinearOrder (Line k) := (exists_wellOrder (Line k)).choose

def lineOf (x : IrrGL k) : Line k := Quotient.mk (lineSetoid k) x

def lineRep (x : IrrGL k) : IrrGL k := Quotient.out (s := lineSetoid k) (Quotient.mk (lineSetoid k) x)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem exists_height (x : IrrGL k) : ∃ m : ℤ, x = (lineRep x).nu m := by
  exact @Quotient.mk_out _ (lineSetoid k) x

def height (x : IrrGL k) : ℤ := (exists_height x).choose

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nu_height (x : IrrGL k) : (lineRep x).nu (height x) = x := by
  exact (exists_height x).choose_spec.symm

/- English proof (translation)
Replace the relevant objects with their definitions. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem lineRep_eq {x y : IrrGL k} (h : lineOf x = lineOf y) : lineRep x = lineRep y := by
  unfold lineRep
  unfold lineOf at h
  rw [h]

def key (Δ : Segment k) : Line k ×ₗ ℤ ×ₗ ℕ :=
  toLex (lineOf Δ.first, toLex (height Δ.first, Δ.len))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem key_injective : Function.Injective (key (k := k)) := by
  intro Δ Δ' h
  simp only [key, toLex_inj, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine Segment.ext_first ?_ h3
  rw [← nu_height Δ.first, ← nu_height Δ'.first, lineRep_eq h1, h2]

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
private theorem lineOf_eq_height_eq_add_of_eq_nu {x y : IrrGL k} (hy : 0 < y.fst) {n : ℤ} (h : x = y.nu n) :
    lineOf x = lineOf y ∧ height x = height y + n := by
  have hl : lineOf x = lineOf y := by
    unfold lineOf
    refine Quotient.sound (s := lineSetoid k) ⟨-n, ?_⟩
    rw [h, IrrGL.nu_nu, Int.cast_neg, add_neg_cancel, IrrGL.nu_zero]
  refine ⟨hl, ?_⟩
  have hR := lineRep_eq hl
  have hRpos : 0 < (lineRep y).fst := by
    have h2 := congrArg Sigma.fst (nu_height y)
    rw [IrrGL.nu_fst] at h2
    rw [h2]
    exact hy
  apply (IrrGL.nu_intCast_inj hRpos).1
  calc (lineRep y).nu (height x) = (lineRep x).nu (height x) := by rw [hR]
    _ = x := nu_height x
    _ = y.nu n := h
    _ = ((lineRep y).nu (height y)).nu n := by rw [nu_height]
    _ = (lineRep y).nu ((height y + n : ℤ) : ℂ) := by rw [IrrGL.nu_nu, Int.cast_add]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Separate the alternatives or extract the components of the hypothesis. Rewrite the indicated hypotheses using the stated equalities.

Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Separate the alternatives or extract the components of the hypothesis.

A detailed English derivation is pending.
-/
theorem key_le {Δ Δ' : Segment k} (h : key Δ ≤ key Δ') :
    (¬ ∃ n : ℕ, 0 < n ∧ Δ.first = Δ'.first.nu (n : ℂ)) ∧ (Δ.first = Δ'.first → Δ.len ≤ Δ'.len) := by
  have hpos : 0 < Δ'.first.fst := Δ'.d_pos
  have hle := h
  simp only [key, Prod.Lex.toLex_le_toLex] at hle
  constructor
  · rintro ⟨n, hn, heq⟩
    have heq' : Δ.first = Δ'.first.nu ((n : ℤ) : ℂ) := by
      rw [Int.cast_natCast]
      exact heq
    obtain ⟨hl, hh⟩ := lineOf_eq_height_eq_add_of_eq_nu hpos heq'
    rcases hle with hlt | ⟨_, hlt | ⟨heq2, _⟩⟩
    · rw [hl] at hlt
      exact lt_irrefl _ hlt
    · omega
    · omega
  · intro hf
    rw [hf] at hle
    rcases hle with hlt | ⟨_, hlt | ⟨_, hlen⟩⟩
    · exact absurd hlt (lt_irrefl _)
    · exact absurd hlt (lt_irrefl _)
    · exact hlen

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result.

Reduce the claim to the hypotheses of an applicable result. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem exists_isCanon {h : ℕ} (Γ : Fin h → Segment k) : ∃ σ : Equiv.Perm (Fin h), IsCanon (Γ ∘ σ) := by
  refine ⟨Tuple.sort (key ∘ Γ), ?_⟩
  have hmono : Monotone ((key ∘ Γ) ∘ Tuple.sort (key ∘ Γ)) := Tuple.monotone_sort _
  unfold IsCanon
  refine ⟨fun i j hij => key_le (hmono hij.le), fun i j l hij hjl hil => ?_⟩
  apply key_injective
  apply le_antisymm
  · calc key ((Γ ∘ Tuple.sort (key ∘ Γ)) j) ≤ key ((Γ ∘ Tuple.sort (key ∘ Γ)) l) := hmono hjl.le
      _ = key ((Γ ∘ Tuple.sort (key ∘ Γ)) i) := by rw [hil]
  · exact hmono hij.le

end GlobalTheory.CompanionTheory.CanonOrder

end
