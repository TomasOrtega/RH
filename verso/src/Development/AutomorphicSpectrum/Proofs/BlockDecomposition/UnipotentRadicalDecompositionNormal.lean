import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.Rodier.OpenFactor

/- English proof (translation)
Rewrite using `[← map_inv]`. Express the relevant statement in the definitionally equal form `((w⁻¹).permMatrix k * (g : Matrix (Fin N) (Fin N) k) * (w⁻¹⁻¹).permMatrix k) (w p) (w q) = _`. Simplify using `[Matrix.mul_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]`.
-/
theorem conj_perm_entry {k : Type} [Field k] {N : ℕ} (w : Equiv.Perm (Fin N)) (g : GL (Fin N) k) (p q : Fin N) :
    ((GroundTheory.Automorphic.permGL k w * g * (GroundTheory.Automorphic.permGL k w)⁻¹ : GL (Fin N) k) :
      Matrix (Fin N) (Fin N) k) (w p) (w q) = (g : Matrix (Fin N) (Fin N) k) p q := by
  rw [← map_inv]
  change ((w⁻¹).permMatrix k * (g : Matrix (Fin N) (Fin N) k) * (w⁻¹⁻¹).permMatrix k) (w p) (w q) = _
  simp [Matrix.mul_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

/- English proof (translation)
Assume the negation of the conclusion as `hqp`. Establish `hm` using `Tuple.monotone_sort (wKey d hd) (not_lt.mp hqp)`. Express the relevant statement in the definitionally equal form `wKey d hd (wOpen d hd p) ≤ wKey d hd (wOpen d hd q) at hm`. Unfold `wKey at hm`. Rewrite `hm` using `[Prod.Lex.le_iff]`.

Simplify using `only [ofLex_toLex] at hm`. Break down `hm with hlt | ⟨heq, _⟩` into its components or cases. Conclude with `lt_asymm hb (OrderDual.toDual_lt_toDual.mp hlt)`. Rewrite `heq` using `[OrderDual.toDual_inj]`. Rewrite `hb` using `[heq]`.

Conclude with `lt_irrefl _ hb`.
-/
theorem lt_of_blk_lt {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {p q : Fin N}
    (hb : blk (stdBlocks d hd) (wOpen d hd p) < blk (stdBlocks d hd) (wOpen d hd q)) : q < p := by
  by_contra hqp
  have hm := Tuple.monotone_sort (wKey d hd) (not_lt.mp hqp)
  change wKey d hd (wOpen d hd p) ≤ wKey d hd (wOpen d hd q) at hm
  unfold wKey at hm
  rw [Prod.Lex.le_iff] at hm
  simp only [ofLex_toLex] at hm
  rcases hm with hlt | ⟨heq, _⟩
  · exact lt_asymm hb (OrderDual.toDual_lt_toDual.mp hlt)
  · rw [OrderDual.toDual_inj] at heq
    rw [heq] at hb
    exact lt_irrefl _ hb

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)

/- English proof (translation)
Conclude with `Iff.rfl`.
-/
theorem mem_unipU {u : GL (Fin N) k} : u ∈ unipU k d hd ↔
    u ∈ unipB k (Fin N) ∧ pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹ ∈ unipRadLower k (stdBlocks d hd) := by
  exact Iff.rfl

/- English proof (translation)
Conclude with `Iff.rfl`.
-/
theorem mem_unipL {u : GL (Fin N) k} : u ∈ unipL k d hd ↔
    u ∈ unipB k (Fin N) ∧
      pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹ ∈ (leviEmb k (stdBlocks d hd)).range := by
  exact Iff.rfl

/- English proof (translation)
Rewrite using `[GlobalTheory.SmGL.mem_parabLower_iff k]`. Introduce `a b i j hab`. Take `⟨p, hp⟩` from `(wOpen d hd).surjective (stdBlocks d hd ⟨a, i⟩)`. Take `⟨q, hq⟩` from `(wOpen d hd).surjective (stdBlocks d hd ⟨b, j⟩)`. Rewrite using `[← hp, ← hq]`.

Unfold `pm`. Rewrite using `[conj_perm_entry]`. Apply `((GlobalTheory.SmGL.mem_unipB k).mp hn).1` to reduce the goal to its premises. Apply `lt_of_blk_lt d hd` to reduce the goal to its premises. Rewrite using `[hp, hq, GlobalTheory.SmGL.blk_apply, GlobalTheory.SmGL.blk_apply]`.

Conclude with `hab`.
-/
theorem conj_mem_parabLower {n : GL (Fin N) k} (hn : n ∈ unipB k (Fin N)) :
    pm k (wOpen d hd) * n * (pm k (wOpen d hd))⁻¹ ∈ parabLower k (stdBlocks d hd) := by
  rw [GlobalTheory.SmGL.mem_parabLower_iff k]
  intro a b i j hab
  obtain ⟨p, hp⟩ := (wOpen d hd).surjective (stdBlocks d hd ⟨a, i⟩)
  obtain ⟨q, hq⟩ := (wOpen d hd).surjective (stdBlocks d hd ⟨b, j⟩)
  rw [← hp, ← hq]
  unfold pm
  rw [conj_perm_entry]
  apply ((GlobalTheory.SmGL.mem_unipB k).mp hn).1
  apply lt_of_blk_lt d hd
  rw [hp, hq, GlobalTheory.SmGL.blk_apply, GlobalTheory.SmGL.blk_apply]
  exact hab

/- English proof (translation)
Establish `hc0` using `conj_mem_parabLower k d hd hn`. Use `set P := pm k (wOpen d hd) with hP`. Use `set e := stdBlocks d hd with he`. Establish `hc : P * n * P⁻¹ ∈ parab k (opp e)` using `hc0`. Take `⟨v, hv, hcv⟩` from `exists_levi_mul_unip k (opp e) ⟨P * n * P⁻¹, hc⟩`.

Use `set L := leviEmb k (opp e) (leviProj k (opp e) ⟨P * n * P⁻¹, hc⟩) with hL`. Establish `hcv' : P * n * P⁻¹ = L * v` using `hcv`. Apply the tactic sequence `have hLentry : ∀ p q : Fin N, ((P⁻¹ * L * P : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) p q = if blk e (wOpen d hd p) = blk e (wOpen d hd q) then (n : Matrix (Fin N) (Fin N) k) p q else 0 := by`. Introduce `p q`. Apply the tactic sequence `have h1 := conj_perm_entry (wOpen d hd) (P⁻¹ * L * P) p q`.

Simplify using `only [show GroundTheory.Automorphic.permGL k (wOpen d hd) = P from rfl] at h1`. Rewrite `h1` using `[show P * (P⁻¹ * L * P) * P⁻¹ = L by group]`. Rewrite using `[← h1]`. Take `⟨⟨x, i⟩, hxi⟩` from `e.surjective (wOpen d hd p)`. Take `⟨⟨y, j⟩, hyj⟩` from `e.surjective (wOpen d hd q)`.

Rewrite using `[← hxi, ← hyj, GlobalTheory.SmGL.blk_apply, GlobalTheory.SmGL.blk_apply]`. Use `split_ifs with hxy`. Substitute `hxy` using the available equality. Use `(GlobalTheory.SmGL.leviEmb_apply_same k (opp e) (leviProj k (opp e) ⟨P * n * P⁻¹, hc⟩) x i j).trans ?_` and prove the remaining obligations. Use `(GlobalTheory.SmGL.leviProj_apply k (opp e) ⟨P * n * P⁻¹, hc⟩ x i j).trans ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `((P * n * P⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (e ⟨x, i⟩) (e ⟨x, j⟩) = _`. Rewrite using `[hxi, hyj]`. Apply the tactic sequence `exact conj_perm_entry (wOpen d hd) n p q`. Conclude with `GlobalTheory.SmGL.leviEmb_apply_ne k (opp e) _ hxy i j`. Establish `haB : P⁻¹ * L * P ∈ unipB k (Fin N)`.

Rewrite using `[GlobalTheory.SmGL.mem_unipB k]`. Use `⟨fun p q hqp => ?_, fun p => ?_⟩` and prove the remaining obligations. Rewrite using `[hLentry] split_ifs`. Conclude with `((GlobalTheory.SmGL.mem_unipB k).mp hn).1 p q hqp`. Both sides reduce to the same expression.

Rewrite using `[hLentry, if_pos rfl]`. Conclude with `((GlobalTheory.SmGL.mem_unipB k).mp hn).2 p`. Use `⟨P⁻¹ * L * P, ?_, P⁻¹ * v * P, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_unipL k d hd]`. Use `⟨haB, ?_⟩` and prove the remaining obligations.

Use `show P * (P⁻¹ * L * P) * P⁻¹ ∈ (leviEmb k e).range`. Rewrite using `[show P * (P⁻¹ * L * P) * P⁻¹ = L by group]`. Conclude with `⟨leviProj k (opp e) ⟨P * n * P⁻¹, hc⟩, rfl⟩`. Rewrite using `[mem_unipU k d hd]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Establish `hv' : v = L⁻¹ * (P * n * P⁻¹)`. Rewrite using `[hcv']`. Use `group`. Rewrite using `[show P⁻¹ * v * P = (P⁻¹ * L * P)⁻¹ * n by rw [hv']; group]`. Conclude with `Subgroup.mul_mem _ (Subgroup.inv_mem _ haB) hn`.

Use `show P * (P⁻¹ * v * P) * P⁻¹ ∈ unipRadLower k e`. Rewrite using `[show P * (P⁻¹ * v * P) * P⁻¹ = v by group]`. Conclude with `hv`. Rewrite using `[show P⁻¹ * L * P * (P⁻¹ * v * P) = P⁻¹ * (L * v) * P by group, ← hcv'] group`.
-/
theorem exists_mul {n : GL (Fin N) k} (hn : n ∈ unipB k (Fin N)) :
    ∃ a ∈ unipL k d hd, ∃ u ∈ unipU k d hd, n = a * u := by
  have hc0 := conj_mem_parabLower k d hd hn
  set P := pm k (wOpen d hd) with hP
  set e := stdBlocks d hd with he
  have hc : P * n * P⁻¹ ∈ parab k (opp e) := hc0
  obtain ⟨v, hv, hcv⟩ := exists_levi_mul_unip k (opp e) ⟨P * n * P⁻¹, hc⟩
  set L := leviEmb k (opp e) (leviProj k (opp e) ⟨P * n * P⁻¹, hc⟩) with hL
  have hcv' : P * n * P⁻¹ = L * v := hcv
  have hLentry : ∀ p q : Fin N, ((P⁻¹ * L * P : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) p q =
      if blk e (wOpen d hd p) = blk e (wOpen d hd q) then (n : Matrix (Fin N) (Fin N) k) p q else 0 := by
    intro p q
    have h1 := conj_perm_entry (wOpen d hd) (P⁻¹ * L * P) p q
    simp only [show GroundTheory.Automorphic.permGL k (wOpen d hd) = P from rfl] at h1
    rw [show P * (P⁻¹ * L * P) * P⁻¹ = L by group] at h1
    rw [← h1]
    obtain ⟨⟨x, i⟩, hxi⟩ := e.surjective (wOpen d hd p)
    obtain ⟨⟨y, j⟩, hyj⟩ := e.surjective (wOpen d hd q)
    rw [← hxi, ← hyj, GlobalTheory.SmGL.blk_apply, GlobalTheory.SmGL.blk_apply]
    split_ifs with hxy
    · subst hxy
      refine (GlobalTheory.SmGL.leviEmb_apply_same k (opp e) (leviProj k (opp e) ⟨P * n * P⁻¹, hc⟩) x i j).trans ?_
      refine (GlobalTheory.SmGL.leviProj_apply k (opp e) ⟨P * n * P⁻¹, hc⟩ x i j).trans ?_
      change ((P * n * P⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (e ⟨x, i⟩) (e ⟨x, j⟩) = _
      rw [hxi, hyj]
      exact conj_perm_entry (wOpen d hd) n p q
    · exact GlobalTheory.SmGL.leviEmb_apply_ne k (opp e) _ hxy i j
  have haB : P⁻¹ * L * P ∈ unipB k (Fin N) := by
    rw [GlobalTheory.SmGL.mem_unipB k]
    refine ⟨fun p q hqp => ?_, fun p => ?_⟩
    · rw [hLentry]
      split_ifs
      · exact ((GlobalTheory.SmGL.mem_unipB k).mp hn).1 p q hqp
      · rfl
    · rw [hLentry, if_pos rfl]
      exact ((GlobalTheory.SmGL.mem_unipB k).mp hn).2 p
  refine ⟨P⁻¹ * L * P, ?_, P⁻¹ * v * P, ?_, ?_⟩
  · rw [mem_unipL k d hd]
    refine ⟨haB, ?_⟩
    show P * (P⁻¹ * L * P) * P⁻¹ ∈ (leviEmb k e).range
    rw [show P * (P⁻¹ * L * P) * P⁻¹ = L by group]
    exact ⟨leviProj k (opp e) ⟨P * n * P⁻¹, hc⟩, rfl⟩
  · rw [mem_unipU k d hd]
    refine ⟨?_, ?_⟩
    · have hv' : v = L⁻¹ * (P * n * P⁻¹) := by
        rw [hcv']
        group
      rw [show P⁻¹ * v * P = (P⁻¹ * L * P)⁻¹ * n by rw [hv']; group]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ haB) hn
    · show P * (P⁻¹ * v * P) * P⁻¹ ∈ unipRadLower k e
      rw [show P * (P⁻¹ * v * P) * P⁻¹ = v by group]
      exact hv
  · rw [show P⁻¹ * L * P * (P⁻¹ * v * P) = P⁻¹ * (L * v) * P by group, ← hcv']
    group

/- English proof (translation)
Rewrite `hu`, the goal using `[mem_unipU k d hd]`. Use `⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hn hu.1) (Subgroup.inv_mem _ hn), ?_⟩` and prove the remaining obligations. Establish `hN` using `GlobalTheory.SmGL.parab_le_normalizer k (GlobalTheory.SmGL.opp (stdBlocks d hd)) (conj_mem_parabLower k d hd hn)`. Establish `key : pm k (wOpen d hd) * (n * u * n⁻¹) * (pm k (wOpen d hd))⁻¹ = (pm k (wOpen d hd) * n * (pm k (wOpen d hd))⁻¹) * (pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹) * (pm k (wOpen d hd) * n * (pm k (wOpen d hd))⁻¹)⁻¹` using `by group`. Rewrite using `[key]`.

Conclude with `(Subgroup.mem_normalizer_iff.mp hN _).mp hu.2`.
-/
theorem conj_mem_unipU {n u : GL (Fin N) k} (hn : n ∈ unipB k (Fin N)) (hu : u ∈ unipU k d hd) :
    n * u * n⁻¹ ∈ unipU k d hd := by
  rw [mem_unipU k d hd] at hu ⊢
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hn hu.1) (Subgroup.inv_mem _ hn), ?_⟩
  have hN := GlobalTheory.SmGL.parab_le_normalizer k (GlobalTheory.SmGL.opp (stdBlocks d hd)) (conj_mem_parabLower k d hd hn)
  have key : pm k (wOpen d hd) * (n * u * n⁻¹) * (pm k (wOpen d hd))⁻¹ =
      (pm k (wOpen d hd) * n * (pm k (wOpen d hd))⁻¹) * (pm k (wOpen d hd) * u * (pm k (wOpen d hd))⁻¹) *
        (pm k (wOpen d hd) * n * (pm k (wOpen d hd))⁻¹)⁻¹ := by group
  rw [key]
  exact (Subgroup.mem_normalizer_iff.mp hN _).mp hu.2

end GlobalTheory.CompanionTheory.Rodier.OpenFactor

/- English proof (translation)
Introduce `k _ _ _ _ h N d hd`. Conclude with `⟨fun n hn => GlobalTheory.CompanionTheory.Rodier.OpenFactor.exists_mul k d hd hn, fun n hn u hu => GlobalTheory.CompanionTheory.Rodier.OpenFactor.conj_mem_unipU k d hd hn hu⟩`.
-/
theorem GlobalTheory.CompanionTheory.Rodier.unipB_eq_levi_mul_rad : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ n ∈ unipB k (Fin N), ∃ a ∈ unipL k d hd, ∃ u ∈ unipU k d hd, n = a * u) ∧ ∀ n ∈ unipB k (Fin N), ∀ u ∈ unipU k d hd, n * u * n⁻¹ ∈ unipU k d hd := by
  intro k _ _ _ _ h N d hd
  exact ⟨fun n hn => GlobalTheory.CompanionTheory.Rodier.OpenFactor.exists_mul k d hd hn,
    fun n hn u hu => GlobalTheory.CompanionTheory.Rodier.OpenFactor.conj_mem_unipU k d hd hn hu⟩

end
