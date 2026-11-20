import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHomNmulOfIsLawStatement

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory.CobDefect

/- English proof (translation)
The claim follows from `hasSubst_of_constantCoeff_zero h`.
-/
theorem hasSubst_cc {σ τ S : Type} [Finite σ] [CommRing S] {a : σ → MvPowerSeries τ S}
    (h : ∀ i, constantCoeff (a i) = 0) : HasSubst a := hasSubst_of_constantCoeff_zero h

/- English proof (translation)
Rewrite using `[← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_map]`.
-/
theorem cc_map {R S σ : Type} [CommRing R] [CommRing S] (φ : R →+* S) (f : MvPowerSeries σ R) :
    constantCoeff (map φ f) = φ (constantCoeff f) := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_map]

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ}

/- English proof (translation)
Unfold `inL`. Rewrite using `[map_subst (hasSubst_cc fun _ => constantCoeff_X _)]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.
-/
theorem map_inL (φ : R →+* S) (f : MvPowerSeries (Fin d) R) : map φ (inL f) = inL (map φ f) := by
  unfold inL
  rw [map_subst (hasSubst_cc fun _ => constantCoeff_X _)]
  congr 1
  funext i
  simp

/- English proof (translation)
Unfold `inR`. Rewrite using `[map_subst (hasSubst_cc fun _ => constantCoeff_X _)]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.
-/
theorem map_inR (φ : R →+* S) (f : MvPowerSeries (Fin d) R) : map φ (inR f) = inR (map φ f) := by
  unfold inR
  rw [map_subst (hasSubst_cc fun _ => constantCoeff_X _)]
  congr 1
  funext i
  simp

/- English proof (translation)
Unfold `at2`. Apply the tactic sequence `rw [map_subst (hasSubst_cc fun i => by cases i <;> simp [hu, hv])]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `cases i <;> rfl`.
-/
theorem mvPowerSeriesMap_evalTwoGroups {τ : Type} [Finite τ] (φ : R →+* S) (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    (u v : Fin d → MvPowerSeries τ R) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    map φ (at2 c u v) = at2 (map φ c) (fun i => map φ (u i)) (fun i => map φ (v i)) := by
  unfold at2
  rw [map_subst (hasSubst_cc fun i => by cases i <;> simp [hu, hv])]
  congr 1
  funext i
  cases i <;> rfl

/- English proof (translation)
Unfold `cob1`. Rewrite using `[map_sub, map_sub, map_subst (hasSubst_cc hμ), map_inL, map_inR]`.
-/
theorem map_formalGroupLawCoboundaryOne_eq (φ : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (f : MvPowerSeries (Fin d) R) :
    map φ (cob1 μ f) = cob1 (fun i => map φ (μ i)) (map φ f) := by
  unfold cob1
  rw [map_sub, map_sub, map_subst (hasSubst_cc hμ), map_inL, map_inR]

/- English proof (translation)
Unfold `cob1 inL inR`. Rewrite using `[subst_sub (hasSubst_cc hμ), subst_sub (hasSubst_cc fun _ => constantCoeff_X _), subst_sub (hasSubst_cc fun _ => constantCoeff_X _)]`. Normalize the expressions using the abelian group laws.
-/
theorem formalGroupLawCoboundaryOne_sub (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (f g : MvPowerSeries (Fin d) R) : cob1 μ (f - g) = cob1 μ f - cob1 μ g := by
  unfold cob1 inL inR
  rw [subst_sub (hasSubst_cc hμ), subst_sub (hasSubst_cc fun _ => constantCoeff_X _),
    subst_sub (hasSubst_cc fun _ => constantCoeff_X _)]
  abel

/- English proof (translation)
Unfold `at2`. Apply the tactic sequence `rw [subst_sub (hasSubst_cc fun i => by cases i <;> simp [hu, hv])]`.
-/
theorem powerSeriesEvalTwoGroups_sub {τ : Type} [Finite τ] (c c' : MvPowerSeries (Fin d ⊕ Fin d) R)
    (u v : Fin d → MvPowerSeries τ R) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) : at2 (c - c') u v = at2 c u v - at2 c' u v := by
  unfold at2
  rw [subst_sub (hasSubst_cc fun i => by cases i <;> simp [hu, hv])]

/- English proof (translation)
Establish `hL : ∀ i, constantCoeff (inL (N i)) = 0` using `fun i => by`. Unfold `inL`. Conclude with `constantCoeff_subst_eq_zero (hasSubst_cc fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _) (hN i)`. Establish `hR : ∀ i, constantCoeff (inR (N i)) = 0` using `fun i => by`. Unfold `inR`.

Conclude with `constantCoeff_subst_eq_zero (hasSubst_cc fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _) (hN i)`. Apply the tactic sequence `have hE : HasSubst (Sum.elim (fun i => inL (N i)) (fun i => inR (N i))) := hasSubst_cc fun i => by cases i <;> simp [hL, hR]`. Establish `hXL : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R))` using `hasSubst_cc fun _ => constantCoeff_X _`. Establish `hXR : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R))` using `hasSubst_cc fun _ => constantCoeff_X _`. Establish `e1 : inL (subst N f) = subst (fun j => inL (N j)) f`.

Unfold `inL`. Rewrite using `[subst_comp_subst_apply (hasSubst_cc hN) hXL]`. Establish `e2 : inR (subst N f) = subst (fun j => inR (N j)) f`. Unfold `inR`. Rewrite using `[subst_comp_subst_apply (hasSubst_cc hN) hXR]`.

Establish `e3 : at2 (inL f) (fun i => inL (N i)) (fun i => inR (N i)) = subst (fun j => inL (N j)) f`. Unfold `at2`. Rewrite using `[show inL f = subst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R)) f from rfl]`. Rewrite using `[subst_comp_subst_apply hXL hE]`. Use `congr 1`.

Use function extensionality and compare the values at `j`. Rewrite using `[subst_X hE]`. Both sides reduce to the same expression. Establish `e4 : at2 (inR f) (fun i => inL (N i)) (fun i => inR (N i)) = subst (fun j => inR (N j)) f`. Unfold `at2`.

Rewrite using `[show inR f = subst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) f from rfl]`. Rewrite using `[subst_comp_subst_apply hXR hE]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Rewrite using `[subst_X hE]`.

Both sides reduce to the same expression. Establish `e5 : subst μ (subst N f) = at2 (subst μ f) (fun i => inL (N i)) (fun i => inR (N i))`. Unfold `at2`. Rewrite using `[subst_comp_subst_apply (hasSubst_cc hN) (hasSubst_cc hμ), subst_comp_subst_apply (hasSubst_cc hμ) hE]`. Use `congr 1`.

Use function extensionality and compare the values at `j`. Conclude with `hom j`. Unfold `cob1`. Rewrite using `[powerSeriesEvalTwoGroups_sub _ _ _ _ hL hR, powerSeriesEvalTwoGroups_sub _ _ _ _ hL hR, e1, e2, e3, e4, e5]`.
-/
theorem formalGroupLawCoboundaryOne_subst_of_endomorphism (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (N : Fin d → MvPowerSeries (Fin d) R)
    (hN : ∀ i, constantCoeff (N i) = 0)
    (hom : ∀ j, subst μ (N j) = at2 (μ j) (fun i => inL (N i)) (fun i => inR (N i)))
    (f : MvPowerSeries (Fin d) R) :
    cob1 μ (subst N f) = at2 (cob1 μ f) (fun i => inL (N i)) (fun i => inR (N i)) := by
  have hL : ∀ i, constantCoeff (inL (N i)) = 0 := fun i => by
    unfold inL
    exact constantCoeff_subst_eq_zero (hasSubst_cc fun _ => constantCoeff_X _)
      (fun _ => constantCoeff_X _) (hN i)
  have hR : ∀ i, constantCoeff (inR (N i)) = 0 := fun i => by
    unfold inR
    exact constantCoeff_subst_eq_zero (hasSubst_cc fun _ => constantCoeff_X _)
      (fun _ => constantCoeff_X _) (hN i)
  have hE : HasSubst (Sum.elim (fun i => inL (N i)) (fun i => inR (N i))) :=
    hasSubst_cc fun i => by cases i <;> simp [hL, hR]
  have hXL : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_cc fun _ => constantCoeff_X _
  have hXR : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_cc fun _ => constantCoeff_X _
  have e1 : inL (subst N f) = subst (fun j => inL (N j)) f := by
    unfold inL
    rw [subst_comp_subst_apply (hasSubst_cc hN) hXL]
  have e2 : inR (subst N f) = subst (fun j => inR (N j)) f := by
    unfold inR
    rw [subst_comp_subst_apply (hasSubst_cc hN) hXR]
  have e3 : at2 (inL f) (fun i => inL (N i)) (fun i => inR (N i)) = subst (fun j => inL (N j)) f := by
    unfold at2
    rw [show inL f = subst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R)) f from rfl]
    rw [subst_comp_subst_apply hXL hE]
    congr 1
    funext j
    rw [subst_X hE]
    rfl
  have e4 : at2 (inR f) (fun i => inL (N i)) (fun i => inR (N i)) = subst (fun j => inR (N j)) f := by
    unfold at2
    rw [show inR f = subst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) f from rfl]
    rw [subst_comp_subst_apply hXR hE]
    congr 1
    funext j
    rw [subst_X hE]
    rfl
  have e5 : subst μ (subst N f) = at2 (subst μ f) (fun i => inL (N i)) (fun i => inR (N i)) := by
    unfold at2
    rw [subst_comp_subst_apply (hasSubst_cc hN) (hasSubst_cc hμ),
      subst_comp_subst_apply (hasSubst_cc hμ) hE]
    congr 1
    funext j
    exact hom j
  unfold cob1
  rw [powerSeriesEvalTwoGroups_sub _ _ _ _ hL hR, powerSeriesEvalTwoGroups_sub _ _ _ _ hL hR, e1, e2, e3, e4, e5]

/- English proof (translation)
Establish `hH` using `GlobalTheory.T.isHom_nmul_of_isLaw R d μ hμ k`. Establish `hμ0` using `hμ.const`. Establish `hN0` using `hH.const`. Establish `hmapinj : ∀ {σ : Type} (a b : MvPowerSeries σ R), map (algebraMap R Q) a = map (algebraMap R Q) b → a = b`. Introduce `σ a b h`.

Use extensionality with `n`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[← coeff_map, ← coeff_map, h]`. Establish `hμQ : ∀ i, constantCoeff (up Q μ i) = 0` using `fun i => by`. Simplify using `only [up, cc_map, hμ0 i, map_zero]`.

Establish `hNQ : ∀ i, constantCoeff (up Q (nmul μ k) i) = 0` using `fun i => by`. Simplify using `only [up, cc_map, hN0 i, map_zero]`. Establish `hL : ∀ i, constantCoeff (inL (nmul μ k i)) = 0` using `fun i => by`. Unfold `inL`. Conclude with `constantCoeff_subst_eq_zero (hasSubst_cc fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _) (hN0 i)`.

Establish `hR : ∀ i, constantCoeff (inR (nmul μ k i)) = 0` using `fun i => by`. Unfold `inR`. Conclude with `constantCoeff_subst_eq_zero (hasSubst_cc fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _) (hN0 i)`. Establish `homQ : ∀ j, subst (up Q μ) (up Q (nmul μ k) j) = at2 (up Q μ j) (fun i => inL (up Q (nmul μ k) i)) (fun i => inR (up Q (nmul μ k) i))`. Introduce `j`.

Establish `h1` using `congrArg (map (algebraMap R Q)) (hH.hom j)`. Rewrite `h1` using `[map_subst (hasSubst_cc hμ0)]`. Unfold `pull2 at h1`. Rewrite `h1` using `[mvPowerSeriesMap_evalTwoGroups _ _ _ _ hL hR]`. Simplify using `only [map_inL, map_inR] at h1`.

Conclude with `h1`. Prove the components needed by the constructor for the conclusion. Apply `hmapinj` to reduce the goal to its premises. Rewrite using `[map_formalGroupLawCoboundaryOne_eq _ _ hμ0, hs, map_sub, mvPowerSeriesMap_evalTwoGroups _ _ _ _ hL hR]`. Simplify using `only [map_inL, map_inR]`.

Express the relevant statement in the definitionally equal form `cob1 (up Q μ) (defect μ k f) = _ - at2 _ (fun i => inL (up Q (nmul μ k) i)) (fun i => inR (up Q (nmul μ k) i))`. Rewrite using `[Nat.cast_smul_eq_nsmul R k g, map_nsmul, hg]`. Unfold `defect`. Rewrite using `[formalGroupLawCoboundaryOne_sub _ hμQ, formalCoboundary_smul hμQ, Nat.cast_smul_eq_nsmul, formalGroupLawCoboundaryOne_subst_of_endomorphism _ hμQ _ hNQ homQ]`. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[← cc_map, hg, map_zero]`. Unfold `cob1 inL inR`. Rewrite using `[map_sub, map_sub, constantCoeff_subst_eq_zero (hasSubst_cc hμQ) hμQ hf, constantCoeff_subst_eq_zero (hasSubst_cc fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _) hf, constantCoeff_subst_eq_zero (hasSubst_cc fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _) hf]`. Simplify using the standard rewrite rules.
-/
theorem formalGroupLawCoboundaryOne_mulDefect (R Q : Type) [CommRing R] [CommRing Q] [Algebra R Q] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : IsLaw μ)
    (hinj : Function.Injective (algebraMap R Q)) (f : MvPowerSeries (Fin d) Q)
    (g : MvPowerSeries (Fin d ⊕ Fin d) R) (s : MvPowerSeries (Fin d) R) (k : ℕ)
    (hf : constantCoeff f = 0) (hg : map (algebraMap R Q) g = cob1 (up Q μ) f)
    (hs : map (algebraMap R Q) s = defect μ k f) :
    cob1 μ s = (k : R) • g - at2 g (fun i => inL (nmul μ k i)) (fun i => inR (nmul μ k i)) ∧
      constantCoeff g = 0 := by
  have hH := GlobalTheory.T.isHom_nmul_of_isLaw R d μ hμ k
  have hμ0 := hμ.const
  have hN0 := hH.const
  have hmapinj : ∀ {σ : Type} (a b : MvPowerSeries σ R),
      map (algebraMap R Q) a = map (algebraMap R Q) b → a = b := by
    intro σ a b h
    ext n
    apply hinj
    rw [← coeff_map, ← coeff_map, h]
  have hμQ : ∀ i, constantCoeff (up Q μ i) = 0 := fun i => by
    simp only [up, cc_map, hμ0 i, map_zero]
  have hNQ : ∀ i, constantCoeff (up Q (nmul μ k) i) = 0 := fun i => by
    simp only [up, cc_map, hN0 i, map_zero]
  have hL : ∀ i, constantCoeff (inL (nmul μ k i)) = 0 := fun i => by
    unfold inL
    exact constantCoeff_subst_eq_zero (hasSubst_cc fun _ => constantCoeff_X _)
      (fun _ => constantCoeff_X _) (hN0 i)
  have hR : ∀ i, constantCoeff (inR (nmul μ k i)) = 0 := fun i => by
    unfold inR
    exact constantCoeff_subst_eq_zero (hasSubst_cc fun _ => constantCoeff_X _)
      (fun _ => constantCoeff_X _) (hN0 i)
  have homQ : ∀ j, subst (up Q μ) (up Q (nmul μ k) j) =
      at2 (up Q μ j) (fun i => inL (up Q (nmul μ k) i)) (fun i => inR (up Q (nmul μ k) i)) := by
    intro j
    have h1 := congrArg (map (algebraMap R Q)) (hH.hom j)
    rw [map_subst (hasSubst_cc hμ0)] at h1
    unfold pull2 at h1
    rw [mvPowerSeriesMap_evalTwoGroups _ _ _ _ hL hR] at h1
    simp only [map_inL, map_inR] at h1
    exact h1
  constructor
  · apply hmapinj
    rw [map_formalGroupLawCoboundaryOne_eq _ _ hμ0, hs, map_sub, mvPowerSeriesMap_evalTwoGroups _ _ _ _ hL hR]
    simp only [map_inL, map_inR]
    change cob1 (up Q μ) (defect μ k f) = _ - at2 _ (fun i => inL (up Q (nmul μ k) i))
      (fun i => inR (up Q (nmul μ k) i))
    rw [Nat.cast_smul_eq_nsmul R k g, map_nsmul, hg]
    unfold defect
    rw [formalGroupLawCoboundaryOne_sub _ hμQ, formalCoboundary_smul hμQ, Nat.cast_smul_eq_nsmul, formalGroupLawCoboundaryOne_subst_of_endomorphism _ hμQ _ hNQ homQ]
  · apply hinj
    rw [← cc_map, hg, map_zero]
    unfold cob1 inL inR
    rw [map_sub, map_sub, constantCoeff_subst_eq_zero (hasSubst_cc hμQ) hμQ hf,
      constantCoeff_subst_eq_zero (hasSubst_cc fun _ => constantCoeff_X _)
        (fun _ => constantCoeff_X _) hf,
      constantCoeff_subst_eq_zero (hasSubst_cc fun _ => constantCoeff_X _)
        (fun _ => constantCoeff_X _) hf]
    simp

/- English proof (translation)
Introduce `R Q _ _ _ d μ hμ hinj f g s k hf hg hs` and use `formalGroupLawCoboundaryOne_mulDefect R Q d μ hμ hinj f g s k hf hg hs`.
-/
theorem main : ∀ (R Q : Type) [CommRing R] [CommRing Q] [Algebra R Q] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → Function.Injective (algebraMap R Q) → ∀ (f : MvPowerSeries (Fin d) Q) (g : MvPowerSeries (Fin d ⊕ Fin d) R) (s : MvPowerSeries (Fin d) R) (k : ℕ), constantCoeff f = 0 → map (algebraMap R Q) g = cob1 (up Q μ) f → map (algebraMap R Q) s = defect μ k f → cob1 μ s = (k : R) • g - at2 g (fun i => inL (nmul μ k i)) (fun i => inR (nmul μ k i)) ∧ constantCoeff g = 0 :=
  fun R Q _ _ _ d μ hμ hinj f g s k hf hg hs => formalGroupLawCoboundaryOne_mulDefect R Q d μ hμ hinj f g s k hf hg hs

end GlobalTheory.CobDefect
