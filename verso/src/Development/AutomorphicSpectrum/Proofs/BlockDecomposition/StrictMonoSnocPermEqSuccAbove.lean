import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

namespace GlobalTheory.CompanionTheory.ConeLocal.SnocPerm

/- English proof (translation)
Establish `hcast : ∀ i : Fin n, π i.castSucc = I i` using `fun i => by`. Rewrite using `[← h]`. Simplify using the standard rewrite rules. Establish `hlast : π (Fin.last n) = k`. Rewrite using `[← h]`.

Simplify using the standard rewrite rules. Establish `hrange : Set.range I = Set.range k.succAbove`. Rewrite using `[Fin.range_succAbove]`. Use extensionality with `y`. Simplify using `only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, rfl⟩ hy`. Rewrite `hy` using `[← hcast i, ← hlast]`. Conclude with `(Fin.castSucc_lt_last i).ne (π.injective hy)`. Introduce `hy`.

Take `⟨x, rfl⟩` from `π.surjective y`. Establish `hx : x ≠ Fin.last n` using `fun hx => hy (by rw [hx, hlast])`. Take `⟨i, rfl⟩` from `Fin.exists_castSucc_eq.2 hx`. Conclude with `⟨i, (hcast i).symm⟩`. Conclude with `(StrictMono.range_inj hI (Fin.strictMono_succAbove k)).1 hrange`.
-/
theorem eq_succAbove_of_snoc_eq_perm {n : ℕ} (I : Fin n → Fin (n + 1)) (k : Fin (n + 1))
    (π : Equiv.Perm (Fin (n + 1))) (hI : StrictMono I)
    (h : Fin.snoc (α := fun _ => Fin (n + 1)) I k = ⇑π) : I = k.succAbove := by
  have hcast : ∀ i : Fin n, π i.castSucc = I i := fun i => by
    rw [← h]; simp
  have hlast : π (Fin.last n) = k := by
    rw [← h]; simp
  have hrange : Set.range I = Set.range k.succAbove := by
    rw [Fin.range_succAbove]
    ext y
    simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩ hy
      rw [← hcast i, ← hlast] at hy
      exact (Fin.castSucc_lt_last i).ne (π.injective hy)
    · intro hy
      obtain ⟨x, rfl⟩ := π.surjective y
      have hx : x ≠ Fin.last n := fun hx => hy (by rw [hx, hlast])
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 hx
      exact ⟨i, (hcast i).symm⟩
  exact (StrictMono.range_inj hI (Fin.strictMono_succAbove k)).1 hrange

end GlobalTheory.CompanionTheory.ConeLocal.SnocPerm
