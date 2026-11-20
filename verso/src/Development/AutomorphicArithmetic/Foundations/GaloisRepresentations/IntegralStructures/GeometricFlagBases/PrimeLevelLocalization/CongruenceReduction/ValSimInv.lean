import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.CongruenceReduction.LevLocAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.CongruenceReduction.CjEntRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocEqOneOfMemGam

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL)
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc GLw AfQ sim comp loc SameK IsCen cj)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Int.Geo.Pl.Tj
attribute [local instance] Ideal.Quotient.field

/- English proof (translation)
Establish `h : ((sim g⁻¹ : AfQˣ) : AfQ) * ((sim g : AfQˣ) : AfQ) = 1`. Rewrite using `[map_inv, Units.inv_mul]`. Establish `h2` using `congrArg (fun x => GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E x) h`. Simplify using `only [map_mul, map_one] at h2`. Establish `h3` using `congrArg (fun x : FiniteAdeleRing (𝓞 E) E => Valued.v (x w)) h2`.

Simplify using `using h3`.
-/
private theorem val_sim_inv {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (g : GUf E n) (w : Plc E) :
    Valued.v (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim g⁻¹ : AfQˣ) : AfQ) w) *
      Valued.v (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim g : AfQˣ) : AfQ) w) = 1 := by
  have h : ((sim g⁻¹ : AfQˣ) : AfQ) * ((sim g : AfQˣ) : AfQ) = 1 := by
    rw [map_inv, Units.inv_mul]
  have h2 := congrArg (fun x => GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E x) h
  simp only [map_mul, map_one] at h2
  have h3 := congrArg (fun x : FiniteAdeleRing (𝓞 E) E => Valued.v (x w)) h2
  simpa using h3

/- English proof (translation)
Rewrite using `[map_inv]`.
-/
private theorem ent_inv {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (g : GUf E n) (w : Plc E) (i k : Fin n) :
    (comp w g⁻¹).val i k = ((comp w g)⁻¹).val i k := by
  rw [map_inv]

/- English proof (translation)
Introduce `E _ _ _ n g w`. Establish `hE` using `UpperTheory.Gal.Int.Geo.Pl.Tj.cjEnt`. Establish `ent : ∀ i k, Valued.v ((comp (cj w) g).val i k) = Valued.v (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim g : AfQˣ) : AfQ) w) * Valued.v ((comp w g⁻¹).val k i)` using `fun i k => by`. Rewrite using `[(hE E n g w i k).2, map_mul]`. Establish `ent' : ∀ i k, Valued.v ((comp (cj w) g⁻¹).val i k) = Valued.v (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim g⁻¹ : AfQˣ) : AfQ) w) * Valued.v ((comp w g).val k i)` using `fun i k => by`.

Rewrite using `[(hE E n g⁻¹ w i k).2, map_mul, inv_inv]`. Establish `hs` using `val_sim_inv g w`. Prove the components needed by the constructor for the conclusion. Introduce `h1 h2 hn`. Take `⟨a1, a2⟩` from `GlobalTheory.EulerTwRestr.mem_KGL_iff.1 h1`.

Take `⟨b1, b2⟩` from `GlobalTheory.EulerTwRestr.mem_KGL_iff.1 h2`. Simplify using `only [HeightOneSpectrum.mem_adicCompletionIntegers] at a1 a2 b1 b2`. Set `i₀ : Fin n` to `⟨0, hn⟩`. Establish `hsum : ∑ k, (comp w g).val i₀ k * ((comp w g)⁻¹).val k i₀ = 1`. Establish `h` using `congrFun (congrFun (Units.mul_inv (comp w g)) i₀) i₀`.

Simplify `h` using `[Matrix.mul_apply]`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, 1 ≤ Valued.v ((comp w g).val i₀ k * ((comp w g)⁻¹).val k i₀) := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `h` using `Valuation.map_sum_lt Valued.v (one_ne_zero) (s := Finset.univ) (fun k _ => hc k)`.

Rewrite `h` using `[hsum, map_one]`. Conclude with `lt_irrefl _ h`. Rewrite `hk` using `[map_mul]`. Establish `hu : Valued.v ((comp w g).val i₀ k) = 1` using `le_antisymm (a1 i₀ k) (hk.trans (mul_le_of_le_one_right' (a2 k i₀)))`. Establish `hv : Valued.v (((comp w g)⁻¹).val k i₀) = 1` using `le_antisymm (a2 k i₀) (hk.trans (mul_le_of_le_one_left' (a1 i₀ k)))`.

Establish `hle : Valued.v (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim g : AfQˣ) : AfQ) w) ≤ 1`. Establish `h` using `b1 i₀ k`. Rewrite `h` using `[ent, ent_inv, hv, mul_one]`. Conclude with `h`. Establish `hle' : Valued.v (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim g⁻¹ : AfQˣ) : AfQ) w) ≤ 1`.

Establish `h` using `b2 k i₀`. Rewrite `h` using `[← map_inv, ent', hu, mul_one]`. Conclude with `h`. Use `le_antisymm hle ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Introduce `h1 h2`. Take `⟨a1, a2⟩` from `GlobalTheory.EulerTwRestr.mem_KGL_iff.1 h2`. Establish `hs' : Valued.v (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim g⁻¹ : AfQˣ) : AfQ) w) = 1`. Rewrite `hs` using `[h1, mul_one]`. Conclude with `hs`.

Use `GlobalTheory.EulerTwRestr.mem_KGL_iff.2 ⟨fun i k => ?_, fun i k => ?_⟩` and prove the remaining obligations. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, ent, h1, one_mul]`. Use `a2 k i` as an intermediate fact. Rewrite `this` using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Rewrite using `[ent_inv]` and apply the resulting hypothesis.

Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, ← map_inv, ent', hs', one_mul]`. Use `a1 k i` as an intermediate fact. Rewrite `this` using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.Gal.Int.Geo.Pl.Tj.cjInt :
    UpperTheory.Gal.Int.Geo.Pl.Tj.CjInt := by
  intro E _ _ _ n g w
  have hE := UpperTheory.Gal.Int.Geo.Pl.Tj.cjEnt
  have ent : ∀ i k, Valued.v ((comp (cj w) g).val i k) =
      Valued.v (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim g : AfQˣ) : AfQ) w) *
        Valued.v ((comp w g⁻¹).val k i) := fun i k => by
    rw [(hE E n g w i k).2, map_mul]
  have ent' : ∀ i k, Valued.v ((comp (cj w) g⁻¹).val i k) =
      Valued.v (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim g⁻¹ : AfQˣ) : AfQ) w) *
        Valued.v ((comp w g).val k i) := fun i k => by
    rw [(hE E n g⁻¹ w i k).2, map_mul, inv_inv]
  have hs := val_sim_inv g w
  constructor
  · intro h1 h2 hn
    obtain ⟨a1, a2⟩ := GlobalTheory.EulerTwRestr.mem_KGL_iff.1 h1
    obtain ⟨b1, b2⟩ := GlobalTheory.EulerTwRestr.mem_KGL_iff.1 h2
    simp only [HeightOneSpectrum.mem_adicCompletionIntegers] at a1 a2 b1 b2
    let i₀ : Fin n := ⟨0, hn⟩
    have hsum : ∑ k, (comp w g).val i₀ k * ((comp w g)⁻¹).val k i₀ = 1 := by
      have h := congrFun (congrFun (Units.mul_inv (comp w g)) i₀) i₀
      simpa [Matrix.mul_apply] using h
    obtain ⟨k, hk⟩ : ∃ k, 1 ≤ Valued.v ((comp w g).val i₀ k * ((comp w g)⁻¹).val k i₀) := by
      by_contra hc
      push_neg at hc
      have h := Valuation.map_sum_lt Valued.v (one_ne_zero) (s := Finset.univ) (fun k _ => hc k)
      rw [hsum, map_one] at h
      exact lt_irrefl _ h
    rw [map_mul] at hk
    have hu : Valued.v ((comp w g).val i₀ k) = 1 :=
      le_antisymm (a1 i₀ k) (hk.trans (mul_le_of_le_one_right' (a2 k i₀)))
    have hv : Valued.v (((comp w g)⁻¹).val k i₀) = 1 :=
      le_antisymm (a2 k i₀) (hk.trans (mul_le_of_le_one_left' (a1 i₀ k)))
    have hle : Valued.v (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim g : AfQˣ) : AfQ) w) ≤ 1 := by
      have h := b1 i₀ k
      rw [ent, ent_inv, hv, mul_one] at h
      exact h
    have hle' : Valued.v (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim g⁻¹ : AfQˣ) : AfQ) w) ≤ 1 := by
      have h := b2 k i₀
      rw [← map_inv, ent', hu, mul_one] at h
      exact h
    refine le_antisymm hle ?_
    calc (1 : _) = _ := hs.symm
      _ ≤ _ := mul_le_of_le_one_left' hle'
  · intro h1 h2
    obtain ⟨a1, a2⟩ := GlobalTheory.EulerTwRestr.mem_KGL_iff.1 h2
    have hs' : Valued.v (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim g⁻¹ : AfQˣ) : AfQ) w) = 1 := by
      rw [h1, mul_one] at hs; exact hs
    refine GlobalTheory.EulerTwRestr.mem_KGL_iff.2 ⟨fun i k => ?_, fun i k => ?_⟩
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, ent, h1, one_mul]
      have := a2 k i
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at this
      rwa [ent_inv]
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← map_inv, ent', hs', one_mul]
      have := a1 k i
      rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at this
