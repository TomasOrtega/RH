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
Conclude with `@Quotient.mk_out _ (lineSetoid k) x`.
-/
theorem exists_height (x : IrrGL k) : ∃ m : ℤ, x = (lineRep x).nu m := by
  exact @Quotient.mk_out _ (lineSetoid k) x

def height (x : IrrGL k) : ℤ := (exists_height x).choose

/- English proof (translation)
Conclude with `(exists_height x).choose_spec.symm`.
-/
theorem nu_height (x : IrrGL k) : (lineRep x).nu (height x) = x := by
  exact (exists_height x).choose_spec.symm

/- English proof (translation)
Unfold `lineRep`. Unfold `lineOf at h`. Rewrite using `[h]`.
-/
theorem lineRep_eq {x y : IrrGL k} (h : lineOf x = lineOf y) : lineRep x = lineRep y := by
  unfold lineRep
  unfold lineOf at h
  rw [h]

def key (Δ : Segment k) : Line k ×ₗ ℤ ×ₗ ℕ :=
  toLex (lineOf Δ.first, toLex (height Δ.first, Δ.len))

/- English proof (translation)
Introduce `Δ Δ' h`. Simplify using `only [key, toLex_inj, Prod.mk.injEq] at h`. Take `⟨h1, h2, h3⟩` from `h`. Use `Segment.ext_first ?_ h3` and prove the remaining obligations. Rewrite using `[← nu_height Δ.first, ← nu_height Δ'.first, lineRep_eq h1, h2]`.
-/
theorem key_injective : Function.Injective (key (k := k)) := by
  intro Δ Δ' h
  simp only [key, toLex_inj, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine Segment.ext_first ?_ h3
  rw [← nu_height Δ.first, ← nu_height Δ'.first, lineRep_eq h1, h2]

/- English proof (translation)
Establish `hl : lineOf x = lineOf y`. Unfold `lineOf`. Use `Quotient.sound (s := lineSetoid k) ⟨-n, ?_⟩` and prove the remaining obligations. Rewrite using `[h, IrrGL.nu_nu, Int.cast_neg, add_neg_cancel, IrrGL.nu_zero]`. Use `⟨hl, ?_⟩` and prove the remaining obligations.

Establish `hR` using `lineRep_eq hl`. Establish `hRpos : 0 < (lineRep y).fst`. Establish `h2` using `congrArg Sigma.fst (nu_height y)`. Rewrite `h2` using `[IrrGL.nu_fst]`. Rewrite using `[h2]`.

Conclude with `hy`. Apply `(IrrGL.nu_intCast_inj hRpos).1` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.
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
Establish `hpos : 0 < Δ'.first.fst` using `Δ'.d_pos`. Establish `hle` using `h`. Simplify using `only [key, Prod.Lex.toLex_le_toLex] at hle`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, hn, heq⟩`.

Establish `heq' : Δ.first = Δ'.first.nu ((n : ℤ) : ℂ)`. Rewrite using `[Int.cast_natCast]`. Conclude with `heq`. Take `⟨hl, hh⟩` from `lineOf_eq_height_eq_add_of_eq_nu hpos heq'`. Break down `hle with hlt | ⟨_, hlt | ⟨heq2, _⟩⟩` into its components or cases.

Rewrite `hlt` using `[hl]`. Conclude with `lt_irrefl _ hlt`. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Introduce `hf`.

Rewrite `hle` using `[hf]`. Break down `hle with hlt | ⟨_, hlt | ⟨_, hlen⟩⟩` into its components or cases. Conclude with `absurd hlt (lt_irrefl _)`. Conclude with `absurd hlt (lt_irrefl _)`. Conclude with `hlen`.
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
Use `⟨Tuple.sort (key ∘ Γ), ?_⟩` and prove the remaining obligations. Establish `hmono : Monotone ((key ∘ Γ) ∘ Tuple.sort (key ∘ Γ))` using `Tuple.monotone_sort _`. Unfold `IsCanon`. Use `⟨fun i j hij => key_le (hmono hij.le), fun i j l hij hjl hil => ?_⟩` and prove the remaining obligations. Apply `key_injective` to reduce the goal to its premises.

Apply `le_antisymm` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Conclude with `hmono hij.le`.
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
