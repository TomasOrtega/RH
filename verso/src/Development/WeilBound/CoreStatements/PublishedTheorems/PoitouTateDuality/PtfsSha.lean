import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDefs
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateNineTermGs

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion GroundTheory.ProfCoh GroundTheory.Global CategoryTheory

namespace PositivityTheory.Lit1.PTN

def PerfectQZ (X Y : Type) [AddCommGroup X] [AddCommGroup Y] : Prop :=
  Finite X ∧ Finite Y ∧ ∃ P : X →+ Y →+ QZ, Function.Bijective P ∧ Function.Bijective P.flip

/- English proof (translation)
Take `⟨hX, hY, P, h1, h2⟩` from `h`. Establish `e : P.flip.flip = P` using `by ext; rfl`. Conclude with `⟨hY, hX, P.flip, h2, by rw [e]; exact h1⟩`.
-/
theorem perfectQZ_symm {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (h : PerfectQZ X Y) :
    PerfectQZ Y X := by
  obtain ⟨hX, hY, P, h1, h2⟩ := h
  have e : P.flip.flip = P := by ext; rfl
  exact ⟨hY, hX, P.flip, h2, by rw [e]; exact h1⟩

/- English proof (translation)
Take `⟨hX, hY, P, h1, h2⟩` from `h`. Establish `bY : Function.Bijective (fun φ : Y' →+ QZ => φ.comp eY.toAddMonoidHom)` using `Function.bijective_iff_has_inverse.2 ⟨fun ψ => ψ.comp eY.symm.toAddMonoidHom, fun φ => by ext; simp, fun ψ => by ext; simp⟩`. Establish `bX : Function.Bijective (fun φ : X' →+ QZ => φ.comp eX.toAddMonoidHom)` using `Function.bijective_iff_has_inverse.2 ⟨fun ψ => ψ.comp eX.symm.toAddMonoidHom, fun φ => by ext; simp, fun ψ => by ext; simp⟩`. Use `⟨Finite.of_equiv _ eX.symm.toEquiv, Finite.of_equiv _ eY.symm.toEquiv, (P.compl₂ eY.toAddMonoidHom).comp eX.toAddMonoidHom, ?_, ?_⟩` and prove the remaining obligations. Establish `e : ⇑((P.compl₂ eY.toAddMonoidHom).comp eX.toAddMonoidHom) = (fun φ : Y' →+ QZ => φ.comp eY.toAddMonoidHom) ∘ P ∘ eX`.

Use function extensionality and compare the values at `x`. Use extensionality with `y`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `bY.comp (h1.comp eX.bijective)`.

Establish `e : ⇑((P.compl₂ eY.toAddMonoidHom).comp eX.toAddMonoidHom).flip = (fun φ : X' →+ QZ => φ.comp eX.toAddMonoidHom) ∘ P.flip ∘ eY`. Use function extensionality and compare the values at `y`. Use extensionality with `x`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `bX.comp (h2.comp eY.bijective)`.
-/
theorem perfectQZ_of_addEquiv {X Y X' Y' : Type} [AddCommGroup X] [AddCommGroup Y]
    [AddCommGroup X'] [AddCommGroup Y'] (eX : X ≃+ X') (eY : Y ≃+ Y') (h : PerfectQZ X' Y') :
    PerfectQZ X Y := by
  obtain ⟨hX, hY, P, h1, h2⟩ := h
  have bY : Function.Bijective (fun φ : Y' →+ QZ => φ.comp eY.toAddMonoidHom) :=
    Function.bijective_iff_has_inverse.2 ⟨fun ψ => ψ.comp eY.symm.toAddMonoidHom,
      fun φ => by ext; simp, fun ψ => by ext; simp⟩
  have bX : Function.Bijective (fun φ : X' →+ QZ => φ.comp eX.toAddMonoidHom) :=
    Function.bijective_iff_has_inverse.2 ⟨fun ψ => ψ.comp eX.symm.toAddMonoidHom,
      fun φ => by ext; simp, fun ψ => by ext; simp⟩
  refine ⟨Finite.of_equiv _ eX.symm.toEquiv, Finite.of_equiv _ eY.symm.toEquiv,
    (P.compl₂ eY.toAddMonoidHom).comp eX.toAddMonoidHom, ?_, ?_⟩
  · have e : ⇑((P.compl₂ eY.toAddMonoidHom).comp eX.toAddMonoidHom) =
        (fun φ : Y' →+ QZ => φ.comp eY.toAddMonoidHom) ∘ P ∘ eX := by
      funext x; ext y; rfl
    rw [e]
    exact bY.comp (h1.comp eX.bijective)
  · have e : ⇑((P.compl₂ eY.toAddMonoidHom).comp eX.toAddMonoidHom).flip =
        (fun φ : X' →+ QZ => φ.comp eX.toAddMonoidHom) ∘ P.flip ∘ eY := by
      funext y; ext x; rfl
    rw [e]
    exact bX.comp (h2.comp eY.bijective)

/- English proof (translation)
Take `⟨hX, hY, P, h1, h2⟩` from `h`. Establish `torX : ∀ x : X, n • x = 0` using `fun x => by`. Rewrite using `[← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]`. Establish `torY : ∀ y : Y, n • y = 0` using `fun y => by`. Rewrite using `[← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]`.

Establish `hP : ∀ x y, n • P x y = 0` using `fun x y => by rw [← map_nsmul, torY, map_zero]`. Set `Q : X →+ (Y →ₗ[ZMod n] ZMod n)` to `{ toFun := fun x => (zmodOfQZ (P x) (hP x)).toZModLinearMap n map_zero' := by`. Use extensionality with `y`. Apply `zmodToQZ_injective (n := n)` to reduce the goal to its premises. Simplify using `[zmodToQZ_zmodOfQZ]`.

Use the proof step `map_add' := fun x x' => by`. Use extensionality with `y`. Apply `zmodToQZ_injective (n := n)` to reduce the goal to its premises. Simplify using `[zmodToQZ_zmodOfQZ] }`. Establish `hQ : ∀ x y, zmodToQZ n (Q.toZModLinearMap n x y) = P x y` using `fun x y => zmodToQZ_zmodOfQZ (P x) (hP x) y`.

Use `⟨hX, hY, Q.toZModLinearMap n, ⟨fun x x' hxx => h1.1 ?_, fun φ => ?_⟩, ⟨fun y y' hyy => h2.1 ?_, fun φ => ?_⟩⟩` and prove the remaining obligations. Use extensionality with `y`. Rewrite using `[← hQ, ← hQ, hxx]`. Take `⟨x, hx⟩` from `h1.2 ((zmodToQZ n).comp φ.toAddMonoidHom)`. Use `⟨x, LinearMap.ext fun y => zmodToQZ_injective (n := n) ?_⟩` and prove the remaining obligations.

Rewrite using `[hQ, hx]`. Both sides reduce to the same expression. Use extensionality with `x`. Use `congrArg (fun f => zmodToQZ n (f x)) hyy` as an intermediate fact. Conclude with `(hQ x y).symm.trans (this.trans (hQ x y'))`.

Take `⟨y, hy⟩` from `h2.2 ((zmodToQZ n).comp φ.toAddMonoidHom)`. Use `⟨y, LinearMap.ext fun x => zmodToQZ_injective (n := n) ?_⟩` and prove the remaining obligations. Use `show zmodToQZ n (Q.toZModLinearMap n x y) = _`. Rewrite using `[hQ]`. Conclude with `DFunLike.congr_fun hy x`.
-/
theorem perfectPair_of_perfectQZ {n : ℕ} [NeZero n] {X Y : Type} [AddCommGroup X]
    [Module (ZMod n) X] [AddCommGroup Y] [Module (ZMod n) Y] (h : PerfectQZ X Y) :
    PerfectPair (R := ZMod n) X Y := by
  obtain ⟨hX, hY, P, h1, h2⟩ := h
  have torX : ∀ x : X, n • x = 0 := fun x => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]
  have torY : ∀ y : Y, n • y = 0 := fun y => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]
  have hP : ∀ x y, n • P x y = 0 := fun x y => by rw [← map_nsmul, torY, map_zero]
  let Q : X →+ (Y →ₗ[ZMod n] ZMod n) :=
    { toFun := fun x => (zmodOfQZ (P x) (hP x)).toZModLinearMap n
      map_zero' := by
        ext y; apply zmodToQZ_injective (n := n)
        simp [zmodToQZ_zmodOfQZ]
      map_add' := fun x x' => by
        ext y; apply zmodToQZ_injective (n := n)
        simp [zmodToQZ_zmodOfQZ] }
  have hQ : ∀ x y, zmodToQZ n (Q.toZModLinearMap n x y) = P x y := fun x y =>
    zmodToQZ_zmodOfQZ (P x) (hP x) y
  refine ⟨hX, hY, Q.toZModLinearMap n, ⟨fun x x' hxx => h1.1 ?_, fun φ => ?_⟩,
    ⟨fun y y' hyy => h2.1 ?_, fun φ => ?_⟩⟩
  · ext y; rw [← hQ, ← hQ, hxx]
  · obtain ⟨x, hx⟩ := h1.2 ((zmodToQZ n).comp φ.toAddMonoidHom)
    refine ⟨x, LinearMap.ext fun y => zmodToQZ_injective (n := n) ?_⟩
    rw [hQ, hx]; rfl
  · ext x
    have := congrArg (fun f => zmodToQZ n (f x)) hyy
    exact (hQ x y).symm.trans (this.trans (hQ x y'))
  · obtain ⟨y, hy⟩ := h2.2 ((zmodToQZ n).comp φ.toAddMonoidHom)
    refine ⟨y, LinearMap.ext fun x => zmodToQZ_injective (n := n) ?_⟩
    show zmodToQZ n (Q.toZModLinearMap n x y) = _
    rw [hQ]
    exact DFunLike.congr_fun hy x

def ShaDictFS : Prop :=
  ∀ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    [IsAlgClosure K (AlgebraicClosure ℚ)] (l : ℕ) [Fact l.Prime] (r : ℕ),
  (l ≠ 2 ∨ IsTotallyComplex K) → 0 < r →
  ∀ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ (l ^ r) → ∀ inv : InvFam K (AlgebraicClosure ℚ) l r,
  InvNormalised ζ inv →
  ∀ (S : Finset (HeightOneSpectrum (𝓞 K))), ContainsAbove S l →
  ∀ (Av : S → ValuationSubring (AlgebraicClosure ℚ)), (∀ v, IsPlaceOver (Av v) v.1) →
  ∀ (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K))) →* (ZMod (l ^ r))ˣ)
    (hμ : μ.comp (toGS (AlgebraicClosure ℚ) _) = cycMod K (AlgebraicClosure ℚ) l r),
  ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K)))) M)
    (hρ : ContAction ρ),
    (∃ (K' : FiniteSubfield) (S' : Set (HeightOneSpectrum (𝓞 K'.1))) (_ : Fintype S')
      (ιs : ∀ v : S', AlgebraicClosure ℚ →ₐ[K'.1]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K'.1)).adicCompletion K'.1))
      (N : ℕ) (_ : NeZero N)
      (_ : ∀ v : HeightOneSpectrum (𝓞 K'.1), ((N : ℕ) : 𝓞 K'.1) ∈ v.asIdeal → v ∈ S')
      (_ : Odd N ∨ IsTotallyComplex K'.1)
      (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K'.1 (AlgebraicClosure ℚ) S'))
      (_ : IsDiscreteRep A) (_ : Finite A) (_ : ∀ m : A, N • m = 0),
      Nonempty (Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av) ≃+ ptSha (gsFinFamily S' ιs) A 1) ∧
      Nonempty (Sha2 ρ (locFam S Av) (continuous_locFam S Av) ≃+ ptSha (gsFinFamily S' ιs) (dualRep (gsRoots S' N) A) 2)) ∧
    (∃ (K' : FiniteSubfield) (S' : Set (HeightOneSpectrum (𝓞 K'.1))) (_ : Fintype S')
      (ιs : ∀ v : S', AlgebraicClosure ℚ →ₐ[K'.1]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K'.1)).adicCompletion K'.1))
      (N : ℕ) (_ : NeZero N)
      (_ : ∀ v : HeightOneSpectrum (𝓞 K'.1), ((N : ℕ) : 𝓞 K'.1) ∈ v.asIdeal → v ∈ S')
      (_ : Odd N ∨ IsTotallyComplex K'.1)
      (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K'.1 (AlgebraicClosure ℚ) S'))
      (_ : IsDiscreteRep A) (_ : Finite A) (_ : ∀ m : A, N • m = 0),
      Nonempty (Sha1 ρ (locFam S Av) (continuous_locFam S Av) ≃+ ptSha (gsFinFamily S' ιs) A 1) ∧
      Nonempty (Sha2 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av) ≃+ ptSha (gsFinFamily S' ιs) (dualRep (gsRoots S' N) A) 2))

section FoundSide

attribute [local instance 2000] Rep.hV2

/- English proof (translation)
Take `⟨K', S', _, ιs, N, _, hS, hK, A, _, _, hA, ⟨eY⟩, ⟨eX⟩⟩` from `h`. Take `⟨h1, h2, h3, h4⟩` from `poitouTate_sha_gs S' ιs hS hK A hA`. Conclude with `perfectQZ_of_addEquiv eX eY (perfectQZ_symm ⟨h1, h2, _, h3, h4⟩)`.
-/
theorem perfectQZ_of_found {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
    (h : ∃ (K' : FiniteSubfield) (S' : Set (HeightOneSpectrum (𝓞 K'.1))) (_ : Fintype S')
      (ιs : ∀ v : S', AlgebraicClosure ℚ →ₐ[K'.1]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K'.1)).adicCompletion K'.1))
      (N : ℕ) (_ : NeZero N)
      (_ : ∀ v : HeightOneSpectrum (𝓞 K'.1), ((N : ℕ) : 𝓞 K'.1) ∈ v.asIdeal → v ∈ S')
      (_ : Odd N ∨ IsTotallyComplex K'.1)
      (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K'.1 (AlgebraicClosure ℚ) S'))
      (_ : IsDiscreteRep A) (_ : Finite A) (_ : ∀ m : A, N • m = 0),
      Nonempty (Y ≃+ ptSha (gsFinFamily S' ιs) A 1) ∧
      Nonempty (X ≃+ ptSha (gsFinFamily S' ιs) (dualRep (gsRoots S' N) A) 2)) : PerfectQZ X Y := by
  obtain ⟨K', S', _, ιs, N, _, hS, hK, A, _, _, hA, ⟨eY⟩, ⟨eX⟩⟩ := h
  obtain ⟨h1, h2, h3, h4⟩ := poitouTate_sha_gs S' ιs hS hK A hA
  exact perfectQZ_of_addEquiv eX eY (perfectQZ_symm ⟨h1, h2, _, h3, h4⟩)

end FoundSide

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `K _ _ l _ r hl hr ζ hζ inv hinv S hS Av hAv μ hμ M _ _ _ _ _ ρ hρ`. Establish `: NeZero (l ^ r)` using `⟨pow_ne_zero r (Fact.out : l.Prime).ne_zero⟩`. Establish `hh` using `h K l r hl hr ζ hζ inv hinv S hS Av hAv μ hμ M ρ hρ`. Conclude with `⟨perfectPair_of_perfectQZ (perfectQZ_of_found (X := Sha2 ρ (locFam S Av) (continuous_locFam S Av)) (Y := Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av)) hh.1), perfectPair_of_perfectQZ (perfectQZ_of_found (X := Sha2 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av)) ( …`.
-/
theorem shaCmpFS_of_dict (h : ShaDictFS) : ShaCmpFS := by
  intro K _ _ l _ r hl hr ζ hζ inv hinv S hS Av hAv μ hμ M _ _ _ _ _ ρ hρ
  have : NeZero (l ^ r) := ⟨pow_ne_zero r (Fact.out : l.Prime).ne_zero⟩
  have hh := h K l r hl hr ζ hζ inv hinv S hS Av hAv μ hμ M ρ hρ
  exact ⟨perfectPair_of_perfectQZ
      (perfectQZ_of_found (X := Sha2 ρ (locFam S Av) (continuous_locFam S Av))
        (Y := Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av)) hh.1),
    perfectPair_of_perfectQZ
      (perfectQZ_of_found (X := Sha2 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av))
        (Y := Sha1 ρ (locFam S Av) (continuous_locFam S Av)) hh.2)⟩

end PositivityTheory.Lit1.PTN
