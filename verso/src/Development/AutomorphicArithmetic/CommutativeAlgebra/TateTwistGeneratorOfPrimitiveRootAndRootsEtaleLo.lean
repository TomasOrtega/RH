import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleProperBaseChange
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.A6supp
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TateTwistSectionsLocallyGenerated
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleLocalPrimitiveRootAndRootsOfUnity
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex UpperTheory.Et

/- English proof (translation)
Introduce `q _ i U`. Take `⟨-, h2, h3, h4, -⟩` from `UpperTheory.Cb.tateTwist_sections_locally_generated q i`. Use `⟨fun ζ => ⟨?_, ?_, ?_⟩, fun hq => (UpperTheory.Cb.etaleLocal_primitiveRoot_and_roots_of_unity q U).1 hq⟩` and prove the remaining obligations. Establish `h0 : ((q : ℕ) : ULift.{1} (ZMod q)) = 0` using `ULift.ext _ _ (ZMod.natCast_self q)`. Rewrite using `[← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)) q, h0, zero_smul]`.

Introduce `V k c hV hc haveI := hV`. Use `h3 V (ζ.map k.appTop.hom) c ?_` and prove the remaining obligations. Rewrite using `[← h4 V U k ζ]`. Conclude with `hc`. Introduce `V k y`.

Take `⟨S, hS, h⟩` from `h2 V (ζ.map k.appTop.hom) y`. Use `⟨S, hS, fun W g hg => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `h W g hg`. Use `⟨c, hc.trans ?_⟩` and prove the remaining obligations. Establish `e : GlobalTheory.EtC.twGen i ((ζ.map k.appTop.hom).map g.appTop.hom) = GlobalTheory.EtC.Sec.res (g ≫ k) (GlobalTheory.EtC.twGen i ζ)`.

Rewrite using `[← h4 W V g, ← h4 V U k]`. Simplify using `[GlobalTheory.EtC.Sec.res]`. Rewrite using `[e]`.
-/
theorem UpperTheory.tateTwist_generator_of_primitiveRoot_and_roots_etaleLocal :
    ∀ (q : ℕ) [NeZero q] (i : ℤ) (U : Scheme.{0}), (∀ ζ : GlobalTheory.EtC.Prim q Γ(U, ⊤), Gen Scheme.etaleTopology q (GlobalTheory.EtC.tw q i).obj (GlobalTheory.EtC.twGen i ζ)) ∧ (UpperTheory.Et.Inv q U → LocT Scheme.etaleTopology U fun V _ => Nonempty (GlobalTheory.EtC.Prim q Γ(V, ⊤))) := by
  intro q _ i U
  obtain ⟨-, h2, h3, h4, -⟩ := UpperTheory.Cb.tateTwist_sections_locally_generated q i
  refine ⟨fun ζ => ⟨?_, ?_, ?_⟩, fun hq => (UpperTheory.Cb.etaleLocal_primitiveRoot_and_roots_of_unity q U).1 hq⟩
  · have h0 : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := ULift.ext _ _ (ZMod.natCast_self q)
    rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)) q, h0, zero_smul]
  · intro V k c hV hc
    haveI := hV
    refine h3 V (ζ.map k.appTop.hom) c ?_
    rw [← h4 V U k ζ]
    exact hc
  · intro V k y
    obtain ⟨S, hS, h⟩ := h2 V (ζ.map k.appTop.hom) y
    refine ⟨S, hS, fun W g hg => ?_⟩
    obtain ⟨c, hc⟩ := h W g hg
    refine ⟨c, hc.trans ?_⟩
    have e : GlobalTheory.EtC.twGen i ((ζ.map k.appTop.hom).map g.appTop.hom) =
        GlobalTheory.EtC.Sec.res (g ≫ k) (GlobalTheory.EtC.twGen i ζ) := by
      rw [← h4 W V g, ← h4 V U k]
      simp [GlobalTheory.EtC.Sec.res]
    rw [e]
