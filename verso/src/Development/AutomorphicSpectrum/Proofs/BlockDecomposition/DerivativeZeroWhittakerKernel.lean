import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.DerWhit

/- English proof (translation)
Substitute using the available equality. Extract witnesses or component facts from the available result. Both sides reduce to the same expression.
-/
private theorem twKer_congr' {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) {H H' : Subgroup G} (h : H = H') (θ : H →* ℂˣ) (θ' : H' →* ℂˣ)
    (hθ : ∀ (x : G) (hx : x ∈ H), θ' ⟨x, h ▸ hx⟩ = θ ⟨x, hx⟩) :
    GlobalTheory.PRep.twKer ρ H θ = GlobalTheory.PRep.twKer ρ H' θ' := by
  subst h
  obtain rfl : θ' = θ := MonoidHom.ext fun x => hθ x x.2
  rfl

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem colFix_zero (k : Type) [Field k] (N : ℕ) : colFix k N 0 = ⊤ := by
  ext g
  simp only [Subgroup.mem_top, iff_true]
  exact fun i hi => absurd hi (Nat.not_lt_zero _)

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem mem_derUnip_zero (k : Type) [Field k] (N : ℕ) {g : GL (Fin N) k} (hg : g ∈ unipB k (Fin N)) :
    g ∈ derUnip k N 0 := by
  unfold GlobalTheory.BZMir.derUnip
  exact Subgroup.mem_inf.2 ⟨hg, GlobalTheory.CompanionTheory.DerWhit.colFix_zero k N ▸ Subgroup.mem_top g⟩

/- English proof (translation)
Treat this case separately. Treat this case separately. Treat this case separately. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem whitCharFrom_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (N : ℕ) (u : unipB k (Fin N)) :
    whitCharFrom k ψ N 0 u = whitChar ψ N u := by
  first
  | rfl
  | simp [GlobalTheory.BZMir.whitCharFrom, GlobalTheory.LocGL.whitChar]
  | (simp only [GlobalTheory.BZMir.whitCharFrom, GlobalTheory.LocGL.whitChar, MonoidHom.coe_mk,
        OneHom.coe_mk]
     congr 2
     exact Finset.sum_congr (by ext p; simp) fun _ _ => rfl)

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem twKer_derUnip_zero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (N : ℕ) (V : Type) [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) :
    twKer π (derUnip k N 0) (derChar k ψ N 0) = twKer π (unipB k (Fin N)) (whitChar ψ N) := by
  have hU : GlobalTheory.BZMir.derUnip k N 0 = GlobalTheory.SmGL.unipB k (Fin N) :=
    le_antisymm (GlobalTheory.BZMir.derUnip_le_unipB k N 0)
      fun g hg => GlobalTheory.CompanionTheory.DerWhit.mem_derUnip_zero k N hg
  refine twKer_congr' π hU _ _ fun x hx => ?_
  exact (GlobalTheory.CompanionTheory.DerWhit.whitCharFrom_zero ψ N ⟨x, hU ▸ hx⟩).symm

end GlobalTheory.CompanionTheory.DerWhit
