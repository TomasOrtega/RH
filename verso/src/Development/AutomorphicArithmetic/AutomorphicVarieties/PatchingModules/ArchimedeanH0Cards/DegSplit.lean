import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ObstructionBoundFromDuality
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDegreeSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecEmb

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

/- English proof (translation)
Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective`. Establish `hlw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal`. Establish `h1` using `(hA ((l : ℕ) : 𝓞 (Lp L))).mpr hv`. Apply `(hw ((l : ℕ) : 𝓞 L)).mp` to reduce the goal to its premises. Simplify using `using h1`.

Take `⟨j, hj⟩` from `(UpperTheory.V.Loc.decEmb (F := L) (Ω := Ω) (v := l)).1 A w hw hlw`. Substitute `hj` using the available equality. Take `⟨-, φL, -, hφL, hrL, -, -, hiL⟩` from `(UpperTheory.V.Loc.decEmb (F := L) (Ω := Ω) (v := l)).2 j`. Take `⟨-, φP, -, hφP, hrP, -, -, hiP⟩` from `(UpperTheory.V.Loc.decEmb (F := Lp L) (Ω := Ω) (v := l)).2 j`. Rewrite using `[← hiL w hw, ← hiP v hA]`.

Use `congr 1`. Use extensionality with `σ`. Prove the components needed by the constructor for the conclusion. Introduce `hσ`. Apply `(hrP σ).mpr` to reduce the goal to its premises.

Introduce `x`. Rewrite using `[IsScalarTower.algebraMap_apply (Lp L) L Ω]`. Conclude with `(hrL σ).mp hσ _`. Introduce `hσ`. Apply `(hrL σ).mpr` to reduce the goal to its premises.

Introduce `x`. Take `⟨g, rfl⟩` from `hσ`. Take `⟨k, hk⟩` from `hsp g.2`. Rewrite using `[hφP]`. Use `congr 1`.

Rewrite using `[← hk]`. Conclude with `k.commutes x`.
-/
private theorem deg_split (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 (Lp L))) (w : HeightOneSpectrum (𝓞 L))
    (hA : IsPlaceOver A v) (hw : IsPlaceOver A w) (hv : ((l : ℕ) : 𝓞 (Lp L)) ∈ v.asIdeal)
    (hsp : Dec (F := Lp L) A ≤ (resP L Ω).range) : locDeg w = locDeg v := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  have hlw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal := by
    have h1 := (hA ((l : ℕ) : 𝓞 (Lp L))).mpr hv
    apply (hw ((l : ℕ) : 𝓞 L)).mp
    simpa using h1
  obtain ⟨j, hj⟩ := (UpperTheory.V.Loc.decEmb (F := L) (Ω := Ω) (v := l)).1 A w hw hlw
  subst hj
  obtain ⟨-, φL, -, hφL, hrL, -, -, hiL⟩ := (UpperTheory.V.Loc.decEmb (F := L) (Ω := Ω) (v := l)).2 j
  obtain ⟨-, φP, -, hφP, hrP, -, -, hiP⟩ := (UpperTheory.V.Loc.decEmb (F := Lp L) (Ω := Ω) (v := l)).2 j
  rw [← hiL w hw, ← hiP v hA]
  congr 1
  ext σ
  constructor
  · intro hσ
    apply (hrP σ).mpr
    intro x
    rw [IsScalarTower.algebraMap_apply (Lp L) L Ω]
    exact (hrL σ).mp hσ _
  · intro hσ
    apply (hrL σ).mpr
    intro x
    obtain ⟨g, rfl⟩ := hσ
    obtain ⟨k, hk⟩ := hsp g.2
    rw [hφP]
    congr 1
    rw [← hk]
    exact k.commutes x

/- English proof (translation)
Introduce `l _ L Ω _ _ _ _ _ _ s V0 V O _ _ _ _ _ n r`. Establish `key : ∀ v : (locOf r).Vl, locDeg (s.w (Subtype.val v)) = locDeg (Subtype.val v)` using `fun v => deg_split l L Ω (s.A v.1) v.1 (s.w v.1) (s.hA _) (s.hw _) v.2 (s.split _ (Or.inl v.2))`. Rewrite using `[Finset.sum_congr rfl (fun v _ => key v)]`. Use `letI : Fintype {v : HeightOneSpectrum (𝓞 (Lp L)) // ((l : ℕ) : 𝓞 (Lp L)) ∈ v.asIdeal} := (locOf r).finV`. Establish `h` using `GlobalTheory.Proof.LocalDegreeSum.sum_locDeg (Lp L) l`.

Conclude with `h`.
-/
theorem UpperTheory.V.Pa.B2.arSum :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 V : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n), ∑ v : (locOf r).Vl, locDeg (s.w (Subtype.val v)) = Module.finrank ℚ (Lp L) := by
  intro l _ L Ω _ _ _ _ _ _ s V0 V O _ _ _ _ _ n r
  have key : ∀ v : (locOf r).Vl, locDeg (s.w (Subtype.val v)) = locDeg (Subtype.val v) := fun v =>
    deg_split l L Ω (s.A v.1) v.1 (s.w v.1) (s.hA _) (s.hw _) v.2 (s.split _ (Or.inl v.2))
  rw [Finset.sum_congr rfl (fun v _ => key v)]
  letI : Fintype {v : HeightOneSpectrum (𝓞 (Lp L)) // ((l : ℕ) : 𝓞 (Lp L)) ∈ v.asIdeal} := (locOf r).finV
  have h := GlobalTheory.Proof.LocalDegreeSum.sum_locDeg (Lp L) l
  exact h
