import Development.EtaleCohomology.EtaleTrace.TwZeroPfGlue

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Opposite

namespace LateralTheory.EtaleTrace

def PrimSplit : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (ζ ξ : Prim q A), ∃ e : Fin q → A,
  (∀ i, IsIdempotentElem (e i)) ∧ ∑ i, e i = 1 ∧ (∀ i, e i * ξ.1 = e i * ζ.1 ^ (i : ℕ)) ∧ (∀ i : Fin q, ¬ Nat.Coprime (i : ℕ) q → e i = 0)

def SplitLoc : Prop := ∀ (U : Scheme.{0}) (n : ℕ) (e : Fin n → Γ(U, ⊤)), (∀ i, IsIdempotentElem (e i)) → ∑ i, e i = 1 →
  Loc U fun V g => ∃ i, g.appTop.hom (e i) = 1

/- English proof (translation)
Introduce `q _ U ζ ξ`. Take `⟨e, he, hs, hx, hc⟩` from `hS q Γ(U, ⊤) ζ ξ`. Take `⟨S, hSc, hP⟩` from `hL U q e he hs`. Use `⟨S, hSc, fun V g hg => ?_⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `hP V g hg`.

Establish `key : g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (i : ℕ)`. Use `congrArg g.appTop.hom (hx i)` as an intermediate fact. Simplify `this` using `[map_mul, map_pow, hi]`. Distinguish the cases in `hcop : Nat.Coprime (i : ℕ) q`. Use `⟨ZMod.unitOfCoprime i hcop, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ _`. Rewrite using `[key, ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt i.2]`. Establish `h0` using `hc i hcop`. Rewrite `hi` using `[h0, map_zero]`. Establish `: Subsingleton Γ(V, ⊤)` using `subsingleton_of_zero_eq_one hi`.

Conclude with `⟨1, Subsingleton.elim _ _⟩`.
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
The claim follows from `TwZero_of_primLoc hTw (primLoc_of hS hL)`.
-/
theorem TwZero_of (hTw : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc) (hS : PrimSplit) (hL : SplitLoc) : TwZero :=
  TwZero_of_primLoc hTw (primLoc_of hS hL)

end LateralTheory.EtaleTrace
