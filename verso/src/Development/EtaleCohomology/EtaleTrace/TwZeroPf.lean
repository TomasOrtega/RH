import Development.EtaleCohomology.EtaleTrace.TwZeroPfGlue

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Opposite

namespace LateralTheory.EtaleTrace

def PrimSplit : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (ζ ξ : Prim q A), ∃ e : Fin q → A,
  (∀ i, IsIdempotentElem (e i)) ∧ ∑ i, e i = 1 ∧ (∀ i, e i * ξ.1 = e i * ζ.1 ^ (i : ℕ)) ∧ (∀ i : Fin q, ¬ Nat.Coprime (i : ℕ) q → e i = 0)

def SplitLoc : Prop := ∀ (U : Scheme.{0}) (n : ℕ) (e : Fin n → Γ(U, ⊤)), (∀ i, IsIdempotentElem (e i)) → ∑ i, e i = 1 →
  Loc U fun V g => ∃ i, g.appTop.hom (e i) = 1

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Consider separately whether the proposition holds or fails. Reduce the conclusion to the remaining proof obligations.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Supply the required witnesses or components.
-/
theorem primLoc_of (hS : PrimSplit) (hL : SplitLoc) : PrimLoc := by
  intro q _ U ζ ξ
  obtain ⟨e, he, hs, hx, hc⟩ := hS q Γ(U, ⊤) ζ ξ
  obtain ⟨S, hSc, hP⟩ := hL U q e he hs
  refine ⟨S, hSc, fun V g hg => ?_⟩
  obtain ⟨i, hi⟩ := hP V g hg
  have key : g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (i : ℕ) := by
    have := congrArg g.appTop.hom (hx i)
    simpa [map_mul, map_pow, hi] using this
  by_cases hcop : Nat.Coprime (i : ℕ) q
  · refine ⟨ZMod.unitOfCoprime i hcop, ?_⟩
    change g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ _
    rw [key, ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt i.2]
  · have h0 := hc i hcop
    rw [h0, map_zero] at hi
    have : Subsingleton Γ(V, ⊤) := subsingleton_of_zero_eq_one hi
    exact ⟨1, Subsingleton.elim _ _⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem TwZero_of (hTw : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc) (hS : PrimSplit) (hL : SplitLoc) : TwZero :=
  TwZero_of_primLoc hTw (primLoc_of hS hL)

end LateralTheory.EtaleTrace
