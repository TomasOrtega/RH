import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsFoundSideE
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalTlPush

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global GroundTheory.LocalField
  ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hN : NeZero (l ^ r)` using `⟨pow_ne_zero r (Fact.out : l.Prime).ne_zero⟩`. Establish `hmem : ζ ∈ maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S`. Use `mem_maxUnramifiedOutside_of_pow_eq_one S hN.out (fun w hw hl => hw (hS w ?_)) hζ.pow_eq_one` and prove the remaining obligations. Rewrite `hl` using `[Nat.cast_pow]`. Conclude with `w.isPrime.mem_of_pow_mem r hl`.

Set `u : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)` to `rootsOfUnity.mkOfPowEq (⟨ζ, hmem⟩ : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S) (Subtype.ext (by simpa using hζ.pow_eq_one))`. Establish `hu : ((((u : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) : AlgebraicClosure ℚ) = ζ`. Simplify using `[u]`. Use `clear_value u`. Establish `hy0 : y ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hy` using `[zero_pow (pow_ne_zero r (Fact.out : l.Prime).ne_zero), eq_comm, map_eq_zero_iff _ (algebraMap Kf.1 (AlgebraicClosure ℚ)).injective]`. Establish `hz : (((0 : Kf.1)) : (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) = 0` using `map_zero (algebraMap Kf.1 ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))`. Establish `h00 : ord (0 : (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) = 0` using `by simp [ord]`. Establish `h0 : ord (((0 : Kf.1) : (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)) = 0` using `(congrArg ord hz).trans h00`.

Rewrite `hϖ` using `[hy, h0]`. Conclude with `zero_ne_one hϖ`. Establish `hχadd : ∀ σ τ, χ (ev (σ * τ)) = χ (ev σ) + χ (ev τ)` using `fun σ τ => by`. Rewrite using `[hχ, hχ, hχ]`. Conclude with `urChar_mulF _ σ τ`.

Establish `hχlc : IsLocallyConstant fun σ => χ (ev σ)`. Establish `h : (fun σ => χ (ev σ)) = urChar ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)) ⟨l ^ r, pow_pos (Fact.out : l.Prime).pos r⟩` using `funext hχ`. Rewrite using `[h]`. Conclude with `urChar_isLocallyConstant _`. Establish `key` using `@exists_root_of_unity_preimage Kf ‹_› ‹_› S ‹_› l r ‹_› ιs v A ev hev ζ hζ u hu y hy0 κ hκ χ hχadd hχlc`.

Take `⟨x0, hx0⟩` from `key`. Establish `hx0'` using `fun s => @coe_rvF_of_eq Kf ‹_› ‹_› S ‹_› l r ‹_› ιs v ζ u hu _ _ (hx0 s)`. Conclude with `⟨x0, hx0', @TL.found_side_inv' Kf ‹_› ‹_› S ‹_› l r ‹_› hr hS ζ hζ ιs v A hA ev hev ϖ hϖ y hy κ hκ χ hχ x0 hx0'⟩`.
-/
theorem found_side' (Kf : FiniteSubfield) [NumberField Kf.1] [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)]
    (S : Set (HeightOneSpectrum (𝓞 Kf.1))) [Fintype S] {l r : ℕ} [Fact l.Prime] (hr : 0 < r)
    (hS : ∀ v : HeightOneSpectrum (𝓞 Kf.1), ((l : ℕ) : 𝓞 Kf.1) ∈ v.asIdeal → v ∈ S)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (l ^ r))
    (ιs : ∀ v : S, AlgebraicClosure ℚ →ₐ[Kf.1]
      AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))
    (v : S) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : IsPlaceOver A v.1)
    (ev : (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[
        (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)) ≃* Dec (F := Kf.1) A)
    (hev : ∀ σ x, ιs v (((ev σ : Dec (F := Kf.1) A) : G Kf.1 (AlgebraicClosure ℚ)) x) = σ (ιs v x))
    (ϖ : 𝓞 Kf.1) (hϖ : ord (((ϖ : Kf.1) : (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)) = 1)
    (y : AlgebraicClosure ℚ) (hy : y ^ (l ^ r) = algebraMap Kf.1 (AlgebraicClosure ℚ) (ϖ : Kf.1))
    (κ : Dec (F := Kf.1) A → ZMod (l ^ r))
    (hκ : ∀ g : Dec (F := Kf.1) A, (g : G Kf.1 (AlgebraicClosure ℚ)) y = ζ ^ (κ g).val * y)
    (χ : Dec (F := Kf.1) A → ZMod (l ^ r))
    (hχ : ∀ σ, χ (ev σ) = urChar ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))
      ⟨l ^ r, pow_pos (Fact.out : l.Prime).pos r⟩ σ) :
    ∃ x0 : cocycles (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S (l ^ r))) 2,
      (∀ s : Fin 2 → (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[
          (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1]
          AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)),
        ((((Additive.toMul (cochainOf _ (cocycleι _ 2 x0) s) :
          rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) :
          (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) :
          maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S) : AlgebraicClosure ℚ) =
          ζ ^ (κ (ev (s 0)) * χ (ev (s 1))).val) ∧
      gsLocalInvRootsQZ S ιs (l ^ r) v (cohomologyπ _ 2 x0) = - zmodToQZ (l ^ r) 1 := by
  have hN : NeZero (l ^ r) := ⟨pow_ne_zero r (Fact.out : l.Prime).ne_zero⟩
  have hmem : ζ ∈ maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S := by
    refine mem_maxUnramifiedOutside_of_pow_eq_one S hN.out (fun w hw hl => hw (hS w ?_)) hζ.pow_eq_one
    rw [Nat.cast_pow] at hl
    exact w.isPrime.mem_of_pow_mem r hl
  let u : rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S) :=
    rootsOfUnity.mkOfPowEq (⟨ζ, hmem⟩ : maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)
      (Subtype.ext (by simpa using hζ.pow_eq_one))
  have hu : ((((u : (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)ˣ) :
      maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) S)) : AlgebraicClosure ℚ) = ζ := by
    simp [u]
  clear_value u
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero r (Fact.out : l.Prime).ne_zero), eq_comm,
      map_eq_zero_iff _ (algebraMap Kf.1 (AlgebraicClosure ℚ)).injective] at hy
    have hz : (((0 : Kf.1)) : (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) = 0 :=
      map_zero (algebraMap Kf.1 ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))
    have h00 : ord (0 : (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) = 0 := by simp [ord]
    have h0 : ord (((0 : Kf.1) : (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1)) = 0 :=
      (congrArg ord hz).trans h00
    rw [hy, h0] at hϖ
    exact zero_ne_one hϖ
  have hχadd : ∀ σ τ, χ (ev (σ * τ)) = χ (ev σ) + χ (ev τ) := fun σ τ => by
    rw [hχ, hχ, hχ]; exact urChar_mulF _ σ τ
  have hχlc : IsLocallyConstant fun σ => χ (ev σ) := by
    have h : (fun σ => χ (ev σ)) = urChar ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))
        ⟨l ^ r, pow_pos (Fact.out : l.Prime).pos r⟩ := funext hχ
    rw [h]
    exact urChar_isLocallyConstant _
  have key := @exists_root_of_unity_preimage Kf ‹_› ‹_› S ‹_› l r ‹_› ιs v A ev hev ζ hζ u hu y hy0 κ hκ χ hχadd hχlc
  obtain ⟨x0, hx0⟩ := key
  have hx0' := fun s => @coe_rvF_of_eq Kf ‹_› ‹_› S ‹_› l r ‹_› ιs v ζ u hu _ _ (hx0 s)
  exact ⟨x0, hx0', @TL.found_side_inv' Kf ‹_› ‹_› S ‹_› l r ‹_› hr hS ζ hζ ιs v A hA ev hev ϖ hϖ y hy κ hκ χ hχ
    x0 hx0'⟩

end PositivityTheory.Lit1.PTN
