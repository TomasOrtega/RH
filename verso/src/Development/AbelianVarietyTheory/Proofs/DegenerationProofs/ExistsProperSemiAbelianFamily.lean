import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBigThetaSysWithAction
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ZarhinNormalProjectiveModelExistsProofStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFractionRingOfForallDiv
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemOfPolarisedLevel
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.ProperFamily

/- English proof (translation)
Substitute `e` using the available equality. Establish `w : ψ ≫ G.hom = (G''.hom ≫ g) ≫ f` using `by rw [n.1.w, Category.assoc]`. Conclude with `⟨h.1.lift ψ (G''.hom ≫ g) w, h.cancel (n.congr rfl (h.1.lift_fst _ _ w).symm) (h.1.lift_snd _ _ w)⟩`.
-/
theorem exists_factor {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [GrpObj G']
    [GrpObj G''] {f : S' ⟶ S} {g : S'' ⟶ S'} {k : S'' ⟶ S} {φ : G'.left ⟶ G.left} {ψ : G''.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (n : IsGrpPullback G'' G k ψ) (e : g ≫ f = k) :
    ∃ φ', IsGrpPullback G'' G' g φ' := by
  subst e
  have w : ψ ≫ G.hom = (G''.hom ≫ g) ≫ f := by rw [n.1.w, Category.assoc]
  exact ⟨h.1.lift ψ (G''.hom ≫ g) w, h.cancel (n.congr rfl (h.1.lift_fst _ _ w).symm) (h.1.lift_snd _ _ w)⟩

/- English proof (translation)
Take `⟨m, i, hi, rfl⟩` from `h`. Use `isProper_str R m` as an intermediate fact. Use `infer_instance`.
-/
theorem isProper_of_isProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsProjOver f) :
    IsProper f := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  infer_instance

/- English proof (translation)
Take `⟨x₀, hx₀⟩` from `ht`. Use `set F := Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j : I × Option s, x = t j.1 * (j.2.elim 1 Subtype.val) / (t i.1 * (i.2.elim 1 Subtype.val))})`. Establish `h₁ : ∀ a ∈ Algebra.adjoin o (s : Set Ω), a ∈ F` using `fun a ha => by`. Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem x hx`.

Use `Subfield.subset_closure (Or.inr ⟨(x₀, none), (x₀, some ⟨x, hx⟩), ?_⟩)` and prove the remaining obligations. Simplify using `only [Option.elim]`. Clear the denominators using the available nonvanishing facts. Consider the case `algebraMap r => exact Subfield.subset_closure (Or.inl ⟨r, rfl⟩)`. Consider the case `add x y _ _ hx hy => exact add_mem hx hy`.

Consider the case `mul x y _ _ hx hy => exact mul_mem hx hy`. Use `Module.Finite.of_surjective (Algebra.linearMap F Ω) fun x => ?_` and prove the remaining obligations. Take `⟨a, ha, b, hb, rfl⟩` from `hΩ x`. Conclude with `⟨⟨a / b, div_mem (h₁ a ha) (h₁ b hb)⟩, rfl⟩`.
-/
theorem finite_ratios {o Ω I : Type} [CommRing o] [Field Ω] [Algebra o Ω] (s : Finset Ω)
    (hΩ : ∀ x : Ω, ∃ a ∈ Algebra.adjoin o (s : Set Ω), ∃ b ∈ Algebra.adjoin o (s : Set Ω), x = a / b)
    (t : I → Ω) (ht : ∃ x, t x ≠ 0) :
    Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪
      {x | ∃ i j : I × Option s, x = t j.1 * (j.2.elim 1 Subtype.val) / (t i.1 * (i.2.elim 1 Subtype.val))})) Ω := by
  obtain ⟨x₀, hx₀⟩ := ht
  set F := Subfield.closure (Set.range (algebraMap o Ω) ∪
      {x | ∃ i j : I × Option s, x = t j.1 * (j.2.elim 1 Subtype.val) / (t i.1 * (i.2.elim 1 Subtype.val))})
  have h₁ : ∀ a ∈ Algebra.adjoin o (s : Set Ω), a ∈ F := fun a ha => by
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      refine Subfield.subset_closure (Or.inr ⟨(x₀, none), (x₀, some ⟨x, hx⟩), ?_⟩)
      simp only [Option.elim]
      field_simp
    | algebraMap r => exact Subfield.subset_closure (Or.inl ⟨r, rfl⟩)
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  refine Module.Finite.of_surjective (Algebra.linearMap F Ω) fun x => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := hΩ x
  exact ⟨⟨a / b, div_mem (h₁ a ha) (h₁ b hb)⟩, rfl⟩

end GlobalTheory.ProperFamily

namespace GlobalTheory

open ProperFamily in

/- English proof (translation)
Introduce `g n hn ho`. Take `⟨hL, hL₂⟩` from `GlobalTheory.abelianSchemeLaws_all`. Take `⟨k, j, hk, hj, big⟩` from `ThetaSysOfObj.exists_big g n hn.two_le`. Use `⟨(j + k * 2) * 2, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_mul, pow_add, pow_mul]`.

Introduce `o Ω _ _ _ _ R₀ hR₀ hΩ P ze hg hun hS ⟨lev⟩`. Establish `hM : IsUnit (((n ^ j * (n ^ k) ^ 2) ^ 2 : ℕ) : o)`. Use `push_cast`. Conclude with `((hun.pow _).mul ((hun.pow _).pow _)).pow _`. Take `⟨R, P', φ₁, lev', hle, hR, hg', hS', hp₁, -⟩` from `GenSpread.polAV_spreads_out o Ω R₀ hR₀ hΩ P _ ze hM hS lev hL`.

Establish `hΩ' : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b` using `fun x => by`. Take `⟨a, ha, b, hb, e⟩` from `hΩ x`. Conclude with `⟨a, hle ha, b, hle hb, e⟩`. Take `⟨S, ρ, h, φ₂, -, hN, hr, hgS, hp₂, -⟩` from `ThetaReal.exists_thetaSys_real hL hL₂ o Ω R hR hΩ' P' n k j ze hn ho hk hj hun hS' lev'`. Take `⟨s, rfl⟩` from `hR₀`.

Take `⟨M, U₀, EE, hO, -, -, ⟨out⟩⟩` from `T.zarhinNormalProjectiveModelExists_proof o Ω S ρ (big j le_rfl o Ω S (hgS.trans (hg'.trans hg)) hN hr) (Option s) (fun i => i.elim 1 Subtype.val) ⟨none, one_ne_zero⟩ (finite_ratios s hΩ S.th S.th_ne)`. Take `⟨ψ, hψ⟩` from `exists_factor (g := spMap S.R.val.toRingHom) hp₂ hp₁ (Spec.map_comp (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom) (CommRingCat.ofHom S.R.val.toRingHom)).symm`. Establish `hr' : Set.range M.pt ⊆ Set.range U₀.ι`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `(ZH.top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hO.ne)`.

Establish `hx` using `IsOpenImmersion.lift_fac U₀.ι M.pt hr'`. Take `⟨χ, hχ⟩` from `exists_factor (isGrpPullback_pullback ρ.P.A out.u₀) hψ (out.u₀_gen _ hx)`. Conclude with `⟨M.Z, M.s, M.pt, out.G, out.grp, _, isProper_of_isProjOver hO.proj, M.pt_s, out.semi, (hχ.comp out.cart).congr hx rfl⟩`.
-/
theorem exists_proper_semiAbelian_family : ∀ (g n : ℕ), n.Prime → Odd n → ∃ a : ℕ, ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (R₀ : Subalgebra o Ω), R₀.FG → (∀ x : Ω, ∃ a ∈ R₀, ∃ b ∈ R₀, x = a / b) → ∀ (P : Out.PolAV (Sp Ω)) (ze : oˣ), P.g = g → IsUnit (n : o) → (letI := P.isAb.comm; GlobalTheory.ZH.HypS P.A P.L) → Nonempty (Out.Level P (n ^ a) (unitOn (Units.map (algebraMap o Ω).toMonoidHom ze))) → ∃ (Z : Scheme.{0}) (s : Z ⟶ Sp o) (x : Sp Ω ⟶ Z) (G : Over Z) (_ : GrpObj G) (φ : P.A.left ⟶ G.left), IsProper s ∧ x ≫ s = spMap (algebraMap o Ω) ∧ IsSemiAbelian G ∧ IsGrpPullback P.A G x φ := by
  intro g n hn ho
  obtain ⟨hL, hL₂⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨k, j, hk, hj, big⟩ := ThetaSysOfObj.exists_big g n hn.two_le
  refine ⟨(j + k * 2) * 2, ?_⟩
  rw [pow_mul, pow_add, pow_mul]
  intro o Ω _ _ _ _ R₀ hR₀ hΩ P ze hg hun hS ⟨lev⟩
  have hM : IsUnit (((n ^ j * (n ^ k) ^ 2) ^ 2 : ℕ) : o) := by
    push_cast
    exact ((hun.pow _).mul ((hun.pow _).pow _)).pow _
  obtain ⟨R, P', φ₁, lev', hle, hR, hg', hS', hp₁, -⟩ :=
    GenSpread.polAV_spreads_out o Ω R₀ hR₀ hΩ P _ ze hM hS lev hL
  have hΩ' : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b := fun x => by
    obtain ⟨a, ha, b, hb, e⟩ := hΩ x
    exact ⟨a, hle ha, b, hle hb, e⟩
  obtain ⟨S, ρ, h, φ₂, -, hN, hr, hgS, hp₂, -⟩ :=
    ThetaReal.exists_thetaSys_real hL hL₂ o Ω R hR hΩ' P' n k j ze hn ho hk hj hun hS' lev'
  obtain ⟨s, rfl⟩ := hR₀
  obtain ⟨M, U₀, EE, hO, -, -, ⟨out⟩⟩ := T.zarhinNormalProjectiveModelExists_proof o Ω S ρ (big j le_rfl o Ω S (hgS.trans (hg'.trans hg)) hN hr)
    (Option s) (fun i => i.elim 1 Subtype.val) ⟨none, one_ne_zero⟩ (finite_ratios s hΩ S.th S.th_ne)
  obtain ⟨ψ, hψ⟩ := exists_factor (g := spMap S.R.val.toRingHom) hp₂ hp₁
    (Spec.map_comp (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom)
      (CommRingCat.ofHom S.R.val.toRingHom)).symm
  have hr' : Set.range M.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    exact (ZH.top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hO.ne)
  have hx := IsOpenImmersion.lift_fac U₀.ι M.pt hr'
  obtain ⟨χ, hχ⟩ := exists_factor (isGrpPullback_pullback ρ.P.A out.u₀) hψ (out.u₀_gen _ hx)
  exact ⟨M.Z, M.s, M.pt, out.G, out.grp, _, isProper_of_isProjOver hO.proj, M.pt_s, out.semi,
    (hχ.comp out.cart).congr hx rfl⟩

end GlobalTheory
