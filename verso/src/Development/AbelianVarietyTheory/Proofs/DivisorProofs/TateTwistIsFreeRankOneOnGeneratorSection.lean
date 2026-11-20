import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.TwistedGenericPoint

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem loc_point {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P) (u : U) :
    ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V), Etale j ∧ j v = u ∧ P V j := by
  obtain ⟨S, hS, hP⟩ := h
  obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hS
  obtain ⟨hsurj, hprop⟩ := (Scheme.ofArrows_mem_precoverage_iff _).1 𝒰.mem₀
  obtain ⟨k, v, hv⟩ := hsurj u
  exact ⟨𝒰.X k, 𝒰.f k, v, hprop k, hv, hP _ _ (h𝒰 _ (𝒰.f k) (Presieve.ofArrows.mk k))⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem isEmpty_of_subsingleton (X : Scheme.{0}) [Subsingleton Γ(X, ⊤)] : IsEmpty X := by
  refine ⟨fun x => ?_⟩
  have := (X.presheaf.germ ⊤ x trivial).hom.domain_nontrivial
  exact not_subsingleton Γ(X, ⊤) inferInstance

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem smul_residue {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (n : ℕ) (y : M) :
    n • y = (ULift.up (n : ZMod q) : ULift.{1} (ZMod q)) • y := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  rfl

end GlobalTheory.TwistedGenericPoint

namespace GlobalTheory

open GlobalTheory.TwistedGenericPoint in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem twGen_gen : ∀ (q : ℕ) (i : ℤ) (S : Scheme.{0}) (ζ : Prim q Γ(S, ⊤)), Gen (tw q i) S (twGen i ζ) := by
  intro q i S ζ U s
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have : Subsingleton Γ(S, ⊤) := by
      obtain ⟨hu, _⟩ := ζ.2
      exact subsingleton_of_zero_eq_one (isUnit_zero_iff.1 (by simpa using hu))
    have hS := isEmpty_of_subsingleton S
    have hU : IsEmpty U := ⟨fun u => hS.elim (s u)⟩
    exact ⟨fun _ u => (hU.elim u), fun _ hne _ => (hU.elim hne.some)⟩
  · haveI : NeZero q := ⟨hq.ne'⟩
    obtain ⟨-, h2, h3, h4, -⟩ := GlobalTheory.T.tateTwist_sections_locally_generated q i
    refine ⟨fun x u => ?_, fun c hne hc => ?_⟩
    · obtain ⟨V, j, v, hj, hjv, c, hc⟩ := loc_point (h2 U (ζ.map s.appTop.hom) x) u
      refine ⟨V, j, v, (c : ZMod q), hj, hjv, ?_⟩
      have e : Sec.pull (j ≫ s) (twGen i ζ) = twGen i ((ζ.map s.appTop.hom).map j.appTop.hom) :=
        h4 V S (j ≫ s) ζ
      rw [e]
      exact hc.trans (smul_residue c _)
    · haveI : Nonempty U := hne
      have e : Sec.pull s (twGen i ζ) = twGen i (ζ.map s.appTop.hom) := h4 U S s ζ
      rw [e] at hc
      have h0 : c.val • twGen i (ζ.map s.appTop.hom) = 0 := by
        rw [smul_residue (q := q), ZMod.natCast_zmod_val]
        exact hc
      have hd := h3 U _ c.val h0
      rw [← ZMod.natCast_zmod_val c]
      exact (ZMod.natCast_eq_zero_iff _ _).2 hd

end GlobalTheory
