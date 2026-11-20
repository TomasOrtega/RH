import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IwMemMul
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FixedSubgroup
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CongruenceSubgroupEventually
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DiagonalConjugateMem

/- English proof (translation)
Establish `hex : ∃ x : kˣ, ValuativeRel.valuation k (x : k) = ValuativeRel.uniformizer k`. Take `⟨x, hx⟩` from `ValuativeRel.valuation_surjective (K := k) (ValuativeRel.uniformizer k)`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Conclude with `ValuativeRel.uniformizer_ne_zero (R := k) (by simpa using hx.symm)`.

Conclude with `⟨Units.mk0 x hx0, hx⟩`. Establish `h` using `Classical.epsilon_spec hex`. Establish `h' : ValuativeRel.valuation k ((UpperTheory.V.Hi.unif k : kˣ) : k) = ValuativeRel.uniformizer k` using `h`. Rewrite using `[h']`. Conclude with `ValuativeRel.uniformizer_lt_one`.
-/
private theorem unif_lt (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] :
    ValuativeRel.valuation k ((UpperTheory.V.Hi.unif k : kˣ) : k) < 1 := by
  have hex : ∃ x : kˣ, ValuativeRel.valuation k (x : k) = ValuativeRel.uniformizer k := by
    obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (K := k) (ValuativeRel.uniformizer k)
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact ValuativeRel.uniformizer_ne_zero (R := k) (by simpa using hx.symm)
    exact ⟨Units.mk0 x hx0, hx⟩
  have h := Classical.epsilon_spec hex
  have h' : ValuativeRel.valuation k ((UpperTheory.V.Hi.unif k : kˣ) : k) = ValuativeRel.uniformizer k := h
  rw [h']
  exact ValuativeRel.uniformizer_lt_one

/- English proof (translation)
Generalize the expression as in `hD : Matrix.diagonal (fun i => (t i : k)) = D`. Establish `h1 : ∀ i, D i i = t i` using `fun i => by rw [← hD, Matrix.diagonal_apply_eq]`. Establish `h2 : ∀ i j, i ≠ j → D i j = 0` using `fun i j h => by rw [← hD, Matrix.diagonal_apply_ne _ h]`. Establish `key : ∀ (d : DecidableEq (Fin n)) (i j : Fin n), @Matrix.blockDiagonal' (Fin n) (fun _ => Unit) (fun _ => Unit) k d _ (fun a : Fin n => ((Matrix.GeneralLinearGroup.scalar Unit (t a) : GL Unit k) : Matrix Unit Unit k)) ⟨i, ()⟩ ⟨j, ()⟩ = D i j`. Introduce `d i j`.

Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Rewrite using `[Matrix.blockDiagonal'_apply_eq, h1]`. Simplify using the standard rewrite rules. Rewrite using `[Matrix.blockDiagonal'_apply_ne _ _ _ h, h2 i j h]`.

Use extensionality with `i j`. Conclude with `key (fun a b => Classical.propDecidable _) i j`.
-/
private theorem diagT_val (k : Type) [Field k] (n : ℕ) (t : Fin n → kˣ) :
    ((GlobalTheory.SmGL.diagT k (Fin n) t : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
      = Matrix.diagonal (fun i => (t i : k)) := by
  generalize hD : Matrix.diagonal (fun i => (t i : k)) = D
  have h1 : ∀ i, D i i = t i := fun i => by rw [← hD, Matrix.diagonal_apply_eq]
  have h2 : ∀ i j, i ≠ j → D i j = 0 := fun i j h => by rw [← hD, Matrix.diagonal_apply_ne _ h]
  have key : ∀ (d : DecidableEq (Fin n)) (i j : Fin n),
      @Matrix.blockDiagonal' (Fin n) (fun _ => Unit) (fun _ => Unit) k d _
        (fun a : Fin n => ((Matrix.GeneralLinearGroup.scalar Unit (t a) : GL Unit k) : Matrix Unit Unit k)) ⟨i, ()⟩ ⟨j, ()⟩ = D i j := by
    intro d i j
    by_cases h : i = j
    · subst h
      rw [Matrix.blockDiagonal'_apply_eq, h1]
      simp
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h, h2 i j h]
  ext i j
  exact key (fun a b => Classical.propDecidable _) i j

/- English proof (translation)
Take `⟨p, hp, rfl⟩` from `hg`. Use `⟨p.2, fun i => ?_⟩` and prove the remaining obligations. Establish `h1 : GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.points (Fin n)) p = 1` using `hp`. Establish `h2` using `congrArg (fun x => ((x i : GL Unit k) : Matrix Unit Unit k) () ()) h1`. Establish `h3 : ((p : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i = (1 : Matrix Unit Unit k) () ()` using `h2`.

Simplify using `using h3`.
-/
private theorem unipB_spec (k : Type) [Field k] (n : ℕ) (g : GL (Fin n) k)
    (hg : g ∈ GlobalTheory.SmGL.unipB k (Fin n)) :
    (g : Matrix (Fin n) (Fin n) k).BlockTriangular id ∧ ∀ i, (g : Matrix (Fin n) (Fin n) k) i i = 1 := by
  obtain ⟨p, hp, rfl⟩ := hg
  refine ⟨p.2, fun i => ?_⟩
  have h1 : GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.points (Fin n)) p = 1 := hp
  have h2 := congrArg (fun x => ((x i : GL Unit k) : Matrix Unit Unit k) () ()) h1
  have h3 : ((p : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i = (1 : Matrix Unit Unit k) () () := h2
  simpa using h3

/- English proof (translation)
Introduce `k _ _ _ _ n V _ _ π hπ v`. Take `⟨c, hc⟩` from `UpperTheory.congruence_subgroup_eventually (k := k) (n := n) {g | π g v = v} ((hπ v).mem_nhds (by simp))`. Use `⟨c, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show v ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd π _`. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Take `⟨h1, h2⟩` from `unipB_spec k n x hx.1`. Conclude with `hc c le_rfl _ (UpperTheory.diagonal_conjugate_mem (UpperTheory.V.Hi.unif k) (unif_lt k) c _ x (diagT_val k n _) hx.2 h1 h2)`. Use `show v ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd π _`. Introduce `g hg`. Conclude with `hc (c + 1) (Nat.le_succ c) g hg.2`.

Use `show v ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd π _`. Introduce `g hg`. Conclude with `hc (c + 1) (Nat.le_succ c) g hg.2`.
-/
theorem UpperTheory.Reformulated.B.BranchingSmooth.br_smooth :
    ∀ {k : Type} [inst : Field k] [inst_1 : ValuativeRel k] [inst_2 : TopologicalSpace k]
      [inst_3 : IsNonarchimedeanLocalField k] {n : ℕ} {V : Type} [inst_4 : AddCommGroup V] [inst_5 : _root_.Module ℂ V]
      (π : Representation ℂ (GL (Fin n) k) V), GlobalTheory.PRep.IsSmooth π → (UpperTheory.V.Hi.glIwa k n).Smooth π := by
  intro k _ _ _ _ n V _ _ π hπ v
  obtain ⟨c, hc⟩ := UpperTheory.congruence_subgroup_eventually (k := k) (n := n) {g | π g v = v} ((hπ v).mem_nhds (by simp))
  refine ⟨c, ?_, ?_, ?_⟩
  · show v ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd π _
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨h1, h2⟩ := unipB_spec k n x hx.1
    exact hc c le_rfl _ (UpperTheory.diagonal_conjugate_mem (UpperTheory.V.Hi.unif k) (unif_lt k) c _ x (diagT_val k n _) hx.2 h1 h2)
  · show v ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd π _
    intro g hg
    exact hc (c + 1) (Nat.le_succ c) g hg.2
  · show v ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd π _
    intro g hg
    exact hc (c + 1) (Nat.le_succ c) g hg.2
