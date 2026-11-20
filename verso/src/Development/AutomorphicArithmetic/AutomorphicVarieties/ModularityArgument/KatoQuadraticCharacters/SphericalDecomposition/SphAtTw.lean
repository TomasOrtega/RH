import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.SphOfWit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.KatoTwoOfVanishOrd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VanishOrdLOfZetaUr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.UnramifiedZeta.ZetaUr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords

/- English proof (translation)
Introduce `M φ hM hφ`. Rewrite using `[TwDet.tw_tw]`. Conclude with `h (M * N) (φ * θ) (Nat.mul_pos hM hN) (TwDet.killsMu_mul (TwDet.killsMu_dvd hφ (dvd_mul_right M N)) (TwDet.killsMu_dvd hθ (dvd_mul_left N M)))`.
-/
private theorem sphAt_tw {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ι : Qbar l ≃+* ℂ} {e : ℕ} {W : R2 Ω l}
    (h : SphAt ι e W) {N : ℕ} {θ : G ℚ Ω →* (Qbar l)ˣ} (hN : 1 ≤ N) (hθ : KillsMu N θ) : SphAt ι e (Af.tw W θ) := by
  intro M φ hM hφ
  rw [TwDet.tw_tw]
  exact h (M * N) (φ * θ) (Nat.mul_pos hM hN)
    (TwDet.killsMu_mul (TwDet.killsMu_dvd hφ (dvd_mul_right M N)) (TwDet.killsMu_dvd hθ (dvd_mul_left N M)))

/- English proof (translation)
Introduce `hC hSrc l _ Ω _ _ _ K _ _ _ e N θ ψ W u ι f hf hS`. Establish `hV : VanishOrdL` using `GlobalTheory.Ord2.vanishOrdL_of_zetaUr hC Final.zetaUr`. Take `⟨hdt, ha⟩` from `u.adm hf`. Establish `h1 : Af.tw W 1 = W`. Use extensionality with `s i j`.

Express the relevant statement in the definitionally equal form `mat (Af.tw W 1) s i j = mat W s i j`. Rewrite using `[TwDet.tw_coe]`. Simplify using the standard rewrite rules. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h1]`.

Conclude with `hV l u.l_odd Ω ι e u.e_pos W ha (hSrc l Ω ι e W u.l_odd u.e_pos ha hS)`. Rewrite using `[← hdt]`. Take `⟨M, hM, hMk⟩` from `UpperTheory.V.CF.kwAbs Ω (dt W).ker (TwDet.ker_open ha.cont ha.det2) (Abelianization.commutator_subset_ker (dt W))`. Establish `ha'` using `admissible_twist_by_det l Ω ι e W ha`. Conclude with `hV l u.l_odd Ω ι e u.e_pos _ ha' (hSrc l Ω ι e _ u.l_odd u.e_pos ha' (sphAt_tw hS hM fun s hs => hMk s hs))`.
-/
theorem UpperTheory.V.Z.Kato.WeilSphericalRecords.twoS :
    GlobalTheory.Mem.LiteralAutomorphy.LitCoh → SrcS → KatoTwoS := by
  intro hC hSrc l _ Ω _ _ _ K _ _ _ e N θ ψ W u ι f hf hS
  have hV : VanishOrdL := GlobalTheory.Ord2.vanishOrdL_of_zetaUr hC Final.zetaUr
  obtain ⟨hdt, ha⟩ := u.adm hf
  have h1 : Af.tw W 1 = W := by
    ext s i j
    change mat (Af.tw W 1) s i j = mat W s i j
    rw [TwDet.tw_coe]
    simp
  refine ⟨?_, ?_⟩
  · rw [h1]
    exact hV l u.l_odd Ω ι e u.e_pos W ha (hSrc l Ω ι e W u.l_odd u.e_pos ha hS)
  · rw [← hdt]
    obtain ⟨M, hM, hMk⟩ := UpperTheory.V.CF.kwAbs Ω (dt W).ker (TwDet.ker_open ha.cont ha.det2)
      (Abelianization.commutator_subset_ker (dt W))
    have ha' := admissible_twist_by_det l Ω ι e W ha
    exact hV l u.l_odd Ω ι e u.e_pos _ ha'
      (hSrc l Ω ι e _ u.l_odd u.e_pos ha' (sphAt_tw hS hM fun s hs => hMk s hs))
