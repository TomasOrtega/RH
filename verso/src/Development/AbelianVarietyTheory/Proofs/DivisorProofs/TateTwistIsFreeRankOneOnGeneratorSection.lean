import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.TwistedGenericPoint

/- English proof (translation)
Take `⟨S, hS, hP⟩` from `h`. Take `⟨𝒰, h𝒰⟩` from `Scheme.exists_cover_of_mem_grothendieckTopology hS`. Take `⟨hsurj, hprop⟩` from `(Scheme.ofArrows_mem_precoverage_iff _).1 𝒰.mem₀`. Take `⟨k, v, hv⟩` from `hsurj u`. Conclude with `⟨𝒰.X k, 𝒰.f k, v, hprop k, hv, hP _ _ (h𝒰 _ (𝒰.f k) (Presieve.ofArrows.mk k))⟩`.
-/
theorem loc_point {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P) (u : U) :
    ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V), Etale j ∧ j v = u ∧ P V j := by
  obtain ⟨S, hS, hP⟩ := h
  obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hS
  obtain ⟨hsurj, hprop⟩ := (Scheme.ofArrows_mem_precoverage_iff _).1 𝒰.mem₀
  obtain ⟨k, v, hv⟩ := hsurj u
  exact ⟨𝒰.X k, 𝒰.f k, v, hprop k, hv, hP _ _ (h𝒰 _ (𝒰.f k) (Presieve.ofArrows.mk k))⟩

/- English proof (translation)
Use `⟨fun x => ?_⟩` and prove the remaining obligations. Use `(X.presheaf.germ ⊤ x trivial).hom.domain_nontrivial` as an intermediate fact. Conclude with `not_subsingleton Γ(X, ⊤) inferInstance`.
-/
theorem isEmpty_of_subsingleton (X : Scheme.{0}) [Subsingleton Γ(X, ⊤)] : IsEmpty X := by
  refine ⟨fun x => ?_⟩
  have := (X.presheaf.germ ⊤ x trivial).hom.domain_nontrivial
  exact not_subsingleton Γ(X, ⊤) inferInstance

/- English proof (translation)
Rewrite using `[← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]`. Both sides reduce to the same expression.
-/
theorem smul_residue {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (n : ℕ) (y : M) :
    n • y = (ULift.up (n : ZMod q) : ULift.{1} (ZMod q)) • y := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  rfl

end GlobalTheory.TwistedGenericPoint

namespace GlobalTheory

open GlobalTheory.TwistedGenericPoint in

/- English proof (translation)
Introduce `q i S ζ U s`. Break down `Nat.eq_zero_or_pos q with rfl | hq` into its components or cases. Establish `: Subsingleton Γ(S, ⊤)`. Take `⟨hu, _⟩` from `ζ.2`. Conclude with `subsingleton_of_zero_eq_one (isUnit_zero_iff.1 (by simpa using hu))`.

Establish `hS` using `isEmpty_of_subsingleton S`. Establish `hU : IsEmpty U` using `⟨fun u => hS.elim (s u)⟩`. Conclude with `⟨fun _ u => (hU.elim u), fun _ hne _ => (hU.elim hne.some)⟩`. Use `haveI : NeZero q := ⟨hq.ne'⟩`. Take `⟨-, h2, h3, h4, -⟩` from `GlobalTheory.T.tateTwist_sections_locally_generated q i`.

Use `⟨fun x u => ?_, fun c hne hc => ?_⟩` and prove the remaining obligations. Take `⟨V, j, v, hj, hjv, c, hc⟩` from `loc_point (h2 U (ζ.map s.appTop.hom) x) u`. Use `⟨V, j, v, (c : ZMod q), hj, hjv, ?_⟩` and prove the remaining obligations. Establish `e : Sec.pull (j ≫ s) (twGen i ζ) = twGen i ((ζ.map s.appTop.hom).map j.appTop.hom)` using `h4 V S (j ≫ s) ζ`. Rewrite using `[e]`.

Conclude with `hc.trans (smul_residue c _)`. Use `haveI : Nonempty U := hne`. Establish `e : Sec.pull s (twGen i ζ) = twGen i (ζ.map s.appTop.hom)` using `h4 U S s ζ`. Rewrite `hc` using `[e]`. Establish `h0 : c.val • twGen i (ζ.map s.appTop.hom) = 0`.

Rewrite using `[smul_residue (q := q), ZMod.natCast_zmod_val]`. Conclude with `hc`. Establish `hd` using `h3 U _ c.val h0`. Rewrite using `[← ZMod.natCast_zmod_val c]`. Conclude with `(ZMod.natCast_eq_zero_iff _ _).2 hd`.
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
