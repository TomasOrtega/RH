import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowEqOneOfIsIntegralOfMulComplexConjEqOneAlt
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RootOfUnityEqOneOfSubOneMemSpan
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MemIdealSmulTopIffForallDual
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IdealInfSmulTopOfProjective
import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.DiagMulVecTmul
import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.InfSpanNeBot

noncomputable section

namespace PositivityTheory.EqVol

open Matrix NumberField MeasureTheory GlobalTheory.CompanionTheory.Ar.Cmp ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
  ReciprocityTheory.L2DbarEstimates

section frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Ψ : Finset (E →+* ℂ)}

omit [NumberField E] [IsCMField E]

/- English proof (translation)
The claim follows from `funext fun τ => h τ`.
-/
theorem frame_ext {x y : Frame Ψ r} (h : ∀ τ, mat x τ = mat y τ) : x = y := funext fun τ => h τ

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_rmul (x b : Frame Ψ r) (τ : Ψ) : mat (rmul x b) τ = mat x τ * mat b τ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_lact (γ : GL (Fin r) E) (x : Frame Ψ r) (τ : Ψ) :
    mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl

/- English proof (translation)
The claim follows from `frame_ext fun τ => by simp only [mat_rmul, mat_lact, Matrix.mul_assoc]`.
-/
theorem lact_rmul (γ : GL (Fin r) E) (x b : Frame Ψ r) : lact γ (rmul x b) = rmul (lact γ x) b :=
  frame_ext fun τ => by simp only [mat_rmul, mat_lact, Matrix.mul_assoc]

/- English proof (translation)
The claim follows from `frame_ext fun τ => by simp only [mat_lact, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]`.
-/
theorem lact_mul (a b : GL (Fin r) E) (x : Frame Ψ r) : lact (a * b) x = lact a (lact b x) :=
  frame_ext fun τ => by simp only [mat_lact, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

/- English proof (translation)
The claim follows from `frame_ext fun τ => by rw [mat_lact, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]`.
-/
theorem lact_one' (x : Frame Ψ r) : lact (1 : GL (Fin r) E) x = x :=
  frame_ext fun τ => by rw [mat_lact, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

def scal (s : Ψ → ℂ) : Frame Ψ r := fun τ => (s τ • (1 : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)

end frames

/- English proof (translation)
Introduce `F E _ _ _ _ _ N c J Λ 𝔞 hΛ hJ`. Use `⟨fun hN γ hγ ⟨s, hs⟩ => ?_, fun J₀ a Λ₀ ha hm => ?_⟩` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos N with rfl | hN0` into its components or cases. Conclude with `Units.ext (Subsingleton.elim _ _)`. Set `i : Fin N` to `⟨0, hN0⟩`.

Set `p : (Fin N → E) →ₗ[𝓞 E] E` to `LinearMap.proj i`. Establish `hss : s * c s = 1`. Establish `h : (γ : Matrix (Fin N) (Fin N) E)ᵀ * J * (γ : Matrix (Fin N) (Fin N) E).map c.toRingHom = J` using `hγ.1`. Establish `e : (s • (1 : Matrix (Fin N) (Fin N) E)).map c.toRingHom = c s • (1 : Matrix (Fin N) (Fin N) E)`. Use extensionality with `i j`.

Apply the tactic sequence `by_cases h : i = j <;> simp [h]`. Rewrite `h` using `[hs, e]`. Simplify using `only [transpose_smul, transpose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul] at h`. Establish `h2` using `congrArg (fun M => (M * J⁻¹) i i) h`. Simplify using `only [Matrix.smul_mul, Matrix.mul_nonsing_inv J hJ, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h2`.

Rewrite using `[mul_comm, h2]`. Take `⟨m, hm, hm'⟩` from `exists_smul_mem hΛ (Pi.single i 1)`. Take `⟨a, ha, e⟩` from `GlobalTheory.CompanionTheory.Ar.Cmp.DetMod.mem_of_smul_le (Λ.map p) (FractionalIdeal.isFractional_of_fg (hΛ.1.map p)) (fun h0 => by`. Establish `: p ((m : E) • Pi.single i 1) ∈ Λ.map p` using `Submodule.mem_map_of_mem hm'`. Rewrite `this` using `[h0]`.

Simplify using `[p, hm] at this) 𝔞 (s - 1) (by`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Establish `h` using `Submodule.mem_map_of_mem (f := p) (show _ ∈ 𝔞 • Λ from hγ.2.2 x hx)`. Rewrite `h` using `[Submodule.map_smul'', hs]`. Simplify `h)` using `[p, sub_mul, smul_mulVec]`.

Establish `e' : ((1 + a : 𝓞 E) : E) = s`. Apply the tactic sequence `have : algebraMap (𝓞 E) E a = s - 1 := by first | exact e | exact e.symm`. Use `show algebraMap (𝓞 E) E (1 + a) = s`. Rewrite using `[map_add, map_one, this]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h5` using `hN (1 + a) (by rw [e']; exact hss) (by simpa using ha)`. Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[hs, ← e', h5]`. Simplify using the standard rewrite rules. Establish `hmap : Λ₀ = Λ.map ((Matrix.mulVecLin (a : Matrix (Fin N) (Fin N) E)).restrictScalars (𝓞 E))`.

Use extensionality with `y`. Use `⟨fun hy => ⟨((a⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ y, (hm _).2 ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[mulVec_mulVec, Units.mul_inv, one_mulVec]` and apply the resulting hypothesis. Use `show (a : Matrix (Fin N) (Fin N) E) *ᵥ (((a⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ y) = y`. Rewrite using `[mulVec_mulVec, Units.mul_inv, one_mulVec]`.

Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `(hm x).1 hx`. Establish `h2 : ∀ x, x ∈ (𝔞 • Λ).toAddSubgroup ↔ (a : Matrix (Fin N) (Fin N) E) *ᵥ x ∈ (𝔞 • Λ₀).toAddSubgroup`. Introduce `x`. Rewrite using `[hmap, ← Submodule.map_smul'']`.

Use `⟨fun h => ⟨x, h, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨y, hy, e⟩`. Establish `e' : (a : Matrix (Fin N) (Fin N) E) *ᵥ y = (a : Matrix (Fin N) (Fin N) E) *ᵥ x` using `e`. Use `congrArg (fun v => ((a⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ v) e'` as an intermediate fact. Simplify using `only [mulVec_mulVec, Units.inv_mul, one_mulVec] at this`.

Conclude with `this ▸ hy`. Use extensionality with `k`. Rewrite using `[mem_conjBy]`. Use `and_congr ?_ (conj_congGrp a hm h2 k)` and prove the remaining obligations. Establish `hk : (a : Matrix (Fin N) (Fin N) E) * ((a⁻¹ * k * a : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = k * a`.

Rewrite using `[← Units.val_mul, ← Units.val_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]`. Establish `e1 : ((a⁻¹ * k * a : GL (Fin N) E) : Matrix (Fin N) (Fin N) E)ᵀ * J * ((a⁻¹ * k * a : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map c.toRingHom = (a : Matrix (Fin N) (Fin N) E)ᵀ * ((k : Matrix (Fin N) (Fin N) E)ᵀ * J₀ * (k : Matrix (Fin N) (Fin N) E).map c.toRingHom) * (a : Matri …`. Rewrite using `[← ha]`. Combine the equalities or inequalities in the displayed calculation. Use `show _ * J * _ = J ↔ _ * J₀ * _ = J₀`.

Rewrite using `[e1]`. Use `conv_lhs => rw [← ha]`. Use `⟨fun h => ?_, fun h => by rw [h]⟩` and prove the remaining obligations. Establish `u1 : IsUnit (a : Matrix (Fin N) (Fin N) E)ᵀ` using `(Matrix.isUnit_transpose _).2 a.isUnit`. Establish `u2 : IsUnit ((a : Matrix (Fin N) (Fin N) E).map c.toRingHom)` using `a.isUnit.map c.toRingHom.mapMatrix`.

Conclude with `u1.mul_left_cancel (u2.mul_right_cancel h)`.
-/
theorem levelFacts : LevelFacts := by
  intro F E _ _ _ _ _ N c J Λ 𝔞 hΛ hJ
  refine ⟨fun hN γ hγ ⟨s, hs⟩ => ?_, fun J₀ a Λ₀ ha hm => ?_⟩
  · rcases Nat.eq_zero_or_pos N with rfl | hN0
    · exact Units.ext (Subsingleton.elim _ _)
    · let i : Fin N := ⟨0, hN0⟩
      let p : (Fin N → E) →ₗ[𝓞 E] E := LinearMap.proj i
      have hss : s * c s = 1 := by
        have h : (γ : Matrix (Fin N) (Fin N) E)ᵀ * J * (γ : Matrix (Fin N) (Fin N) E).map c.toRingHom = J := hγ.1
        have e : (s • (1 : Matrix (Fin N) (Fin N) E)).map c.toRingHom = c s • (1 : Matrix (Fin N) (Fin N) E) := by
          ext i j
          by_cases h : i = j <;> simp [h]
        rw [hs, e] at h
        simp only [transpose_smul, transpose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
          smul_smul] at h
        have h2 := congrArg (fun M => (M * J⁻¹) i i) h
        simp only [Matrix.smul_mul, Matrix.mul_nonsing_inv J hJ, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
          mul_one] at h2
        rw [mul_comm, h2]
      obtain ⟨m, hm, hm'⟩ := exists_smul_mem hΛ (Pi.single i 1)
      obtain ⟨a, ha, e⟩ := GlobalTheory.CompanionTheory.Ar.Cmp.DetMod.mem_of_smul_le (Λ.map p)
        (FractionalIdeal.isFractional_of_fg (hΛ.1.map p))
        (fun h0 => by
          have : p ((m : E) • Pi.single i 1) ∈ Λ.map p := Submodule.mem_map_of_mem hm'
          rw [h0] at this
          simp [p, hm] at this) 𝔞 (s - 1) (by
          rintro _ ⟨x, hx, rfl⟩
          have h := Submodule.mem_map_of_mem (f := p) (show _ ∈ 𝔞 • Λ from hγ.2.2 x hx)
          rw [Submodule.map_smul'', hs] at h
          simpa [p, sub_mul, smul_mulVec] using h)
      have e' : ((1 + a : 𝓞 E) : E) = s := by
        have : algebraMap (𝓞 E) E a = s - 1 := by first | exact e | exact e.symm
        show algebraMap (𝓞 E) E (1 + a) = s
        rw [map_add, map_one, this]
        ring
      have h5 := hN (1 + a) (by rw [e']; exact hss) (by simpa using ha)
      refine Units.ext ?_
      rw [hs, ← e', h5]
      simp
  · have hmap : Λ₀ = Λ.map ((Matrix.mulVecLin (a : Matrix (Fin N) (Fin N) E)).restrictScalars (𝓞 E)) := by
      ext y
      refine ⟨fun hy => ⟨((a⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ y, (hm _).2 ?_, ?_⟩, ?_⟩
      · rwa [mulVec_mulVec, Units.mul_inv, one_mulVec]
      · show (a : Matrix (Fin N) (Fin N) E) *ᵥ (((a⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ y) = y
        rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
      · rintro ⟨x, hx, rfl⟩
        exact (hm x).1 hx
    have h2 : ∀ x, x ∈ (𝔞 • Λ).toAddSubgroup ↔ (a : Matrix (Fin N) (Fin N) E) *ᵥ x ∈ (𝔞 • Λ₀).toAddSubgroup := by
      intro x
      rw [hmap, ← Submodule.map_smul'']
      refine ⟨fun h => ⟨x, h, rfl⟩, ?_⟩
      rintro ⟨y, hy, e⟩
      have e' : (a : Matrix (Fin N) (Fin N) E) *ᵥ y = (a : Matrix (Fin N) (Fin N) E) *ᵥ x := e
      have := congrArg (fun v => ((a⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ v) e'
      simp only [mulVec_mulVec, Units.inv_mul, one_mulVec] at this
      exact this ▸ hy
    ext k
    rw [mem_conjBy]
    refine and_congr ?_ (conj_congGrp a hm h2 k)
    have hk : (a : Matrix (Fin N) (Fin N) E) * ((a⁻¹ * k * a : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = k * a := by
      rw [← Units.val_mul, ← Units.val_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
    have e1 : ((a⁻¹ * k * a : GL (Fin N) E) : Matrix (Fin N) (Fin N) E)ᵀ * J *
        ((a⁻¹ * k * a : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map c.toRingHom =
        (a : Matrix (Fin N) (Fin N) E)ᵀ * ((k : Matrix (Fin N) (Fin N) E)ᵀ * J₀ *
          (k : Matrix (Fin N) (Fin N) E).map c.toRingHom) * (a : Matrix (Fin N) (Fin N) E).map c.toRingHom := by
      rw [← ha]
      calc _ = ((a : Matrix (Fin N) (Fin N) E) * ((a⁻¹ * k * a : GL (Fin N) E) : Matrix (Fin N) (Fin N) E))ᵀ * J₀ *
          ((a : Matrix (Fin N) (Fin N) E) * ((a⁻¹ * k * a : GL (Fin N) E) : Matrix (Fin N) (Fin N) E)).map
            c.toRingHom := by simp only [transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
        _ = _ := by rw [hk]; simp only [transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
    show _ * J * _ = J ↔ _ * J₀ * _ = J₀
    rw [e1]
    conv_lhs => rw [← ha]
    refine ⟨fun h => ?_, fun h => by rw [h]⟩
    have u1 : IsUnit (a : Matrix (Fin N) (Fin N) E)ᵀ := (Matrix.isUnit_transpose _).2 a.isUnit
    have u2 : IsUnit ((a : Matrix (Fin N) (Fin N) E).map c.toRingHom) := a.isUnit.map c.toRingHom.mapMatrix
    exact u1.mul_left_cancel (u2.mul_right_cancel h)

/- English proof (translation)
Introduce `z hz hz1`. Take `⟨n, hn, e⟩` from `pow_eq_one_of_isIntegral_of_mul_complexConj_eq_one E z z.2 hz`. Conclude with `rootOfUnity_eq_one_of_sub_one_mem_span E z n M hn hM (by exact_mod_cast e) (h hz1)`.
-/
theorem neat_of_le (E : Type) [Field E] [NumberField E] [IsCMField E] (M : ℕ) (𝔞 : Ideal (𝓞 E)) (hM : 3 ≤ M)
    (h : 𝔞 ≤ Ideal.span {(M : 𝓞 E)}) : Neat (IsCMField.complexConj E) 𝔞 := by
  intro z hz hz1
  obtain ⟨n, hn, e⟩ := pow_eq_one_of_isIntegral_of_mul_complexConj_eq_one E z z.2 hz
  exact rootOfUnity_eq_one_of_sub_one_mem_span E z n M hn hM (by exact_mod_cast e) (h hz1)

/- English proof (translation)
Introduce `z hz hz1`. Use `neat_of_le E M _ hM le_rfl z hz ?_` and prove the remaining obligations. Establish `hzz : z * bar z = 1`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite `hz` using `[← hbar]`.

Conclude with `hz`. Establish `h3 : z - 1 ∈ Mb.map (bar : 𝓞 E →+* 𝓞 E)`. Establish `h4 : bar (z - 1) ∈ Mb.map (bar : 𝓞 E →+* 𝓞 E)` using `Ideal.mem_map_of_mem (bar : 𝓞 E →+* 𝓞 E) hz1`. Establish `e : z - 1 = -z * bar (z - 1)`. Rewrite using `[map_sub, map_one]`.

Take the linear combination `hzz`. Rewrite using `[e]`. Conclude with `Ideal.mul_mem_left _ _ h4`. Rewrite using `[← h1, Ideal.mul_eq_inf_of_coprime h2]`. Conclude with `⟨hz1, h3⟩`.
-/
theorem neat_of_split (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E)
    (hbar : ∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) (M : ℕ) (Mb : Ideal (𝓞 E)) (hM : 3 ≤ M)
    (h1 : Mb * Mb.map (bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(M : 𝓞 E)}) (h2 : Mb ⊔ Mb.map (bar : 𝓞 E →+* 𝓞 E) = ⊤) :
    Neat (IsCMField.complexConj E) Mb := by
  intro z hz hz1
  refine neat_of_le E M _ hM le_rfl z hz ?_
  have hzz : z * bar z = 1 := by
    apply RingOfIntegers.ext
    rw [← hbar] at hz
    exact hz
  have h3 : z - 1 ∈ Mb.map (bar : 𝓞 E →+* 𝓞 E) := by
    have h4 : bar (z - 1) ∈ Mb.map (bar : 𝓞 E →+* 𝓞 E) := Ideal.mem_map_of_mem (bar : 𝓞 E →+* 𝓞 E) hz1
    have e : z - 1 = -z * bar (z - 1) := by
      rw [map_sub, map_one]
      linear_combination hzz
    rw [e]
    exact Ideal.mul_mem_left _ _ h4
  rw [← h1, Ideal.mul_eq_inf_of_coprime h2]
  exact ⟨hz1, h3⟩

/- English proof (translation)
Introduce `E _ _ N Λ 𝔪 𝔪' M A γ hΛ hM hprod hγ`. Establish `: Module.Finite (𝓞 E) Λ` using `Module.Finite.iff_fg.2 hΛ.1`. Establish `: Module.FinitePresentation (𝓞 E) Λ` using `Module.finitePresentation_of_finite _ _`. Establish `: Module.Projective (𝓞 E) Λ` using `Module.Flat.projective_of_finitePresentation`. Establish `tr : ∀ (𝔟 : Ideal (𝓞 E)) (x : Λ), x ∈ 𝔟 • (⊤ : Submodule (𝓞 E) Λ) ↔ (x : Fin N → E) ∈ 𝔟 • Λ` using `fun 𝔟 x => Submodule.mem_smul_top_iff 𝔟 Λ x`.

Establish `sp : ∀ (n : ℕ) (y : Fin N → E), y ∈ Ideal.span {(n : 𝓞 E)} • Λ ↔ ∃ e ∈ Λ, y = n • e` using `fun n y => by`. Rewrite using `[Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Simplify using `only [Nat.cast_smul_eq_nsmul, eq_comm]`. Set `T : Λ →ₗ[𝓞 E] Λ` to `((Matrix.mulVecLin γ).restrictScalars (𝓞 E)).restrict hγ - LinearMap.id`. Establish `hT : ∀ x : Λ, (T x : Fin N → E) = γ *ᵥ x - x` using `fun _ => rfl`.

Establish `h𝔪 : 𝔪 ≠ ⊥`. Introduce and unpack `rfl`. Rewrite `hprod` using `[Ideal.mul_bot, eq_comm, Ideal.span_singleton_eq_bot]`. Conclude with `hM.ne' (by exact_mod_cast hprod)`. Establish `hc` using `map_ideal_smul_top_iff_cancel (𝓞 E) Λ 𝔪 𝔪' T h𝔪`.

Rewrite `hc` using `[mul_comm, hprod]`. Establish `hi` using `ideal_inf_smul_top_of_projective (𝓞 E) Λ 𝔪' (Ideal.span {(A : 𝓞 E)})`. Simplify using `only [← sub_eq_iff_eq_add', ← sp]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩ x hx`.

Rewrite using `[← hT ⟨x, hx⟩, ← tr, hi]`. Conclude with `⟨hc.1 (fun y hy => (tr _ _).2 (h1 y ((tr _ _).1 hy))) _, (tr _ _).2 (h2 x hx)⟩`. Introduce `h`. Establish `h' : ∀ x : Λ, T x ∈ 𝔪' • (⊤ : Submodule (𝓞 E) Λ) ⊓ Ideal.span {(A : 𝓞 E)} • ⊤` using `fun x => by`. Rewrite using `[← hi, tr]`.

Conclude with `h x x.2`. Conclude with `⟨fun x hx => (tr _ _).1 (hc.2 (fun y => (h' y).1) ⟨x, Submodule.smul_le_right hx⟩ ((tr _ _).2 hx)), fun x hx => (tr _ _).1 (h' ⟨x, hx⟩).2⟩`.
-/
theorem levelIdeal : LevelIdeal := by
  intro E _ _ N Λ 𝔪 𝔪' M A γ hΛ hM hprod hγ
  have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hΛ.1
  have : Module.FinitePresentation (𝓞 E) Λ := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 E) Λ := Module.Flat.projective_of_finitePresentation
  have tr : ∀ (𝔟 : Ideal (𝓞 E)) (x : Λ), x ∈ 𝔟 • (⊤ : Submodule (𝓞 E) Λ) ↔ (x : Fin N → E) ∈ 𝔟 • Λ :=
    fun 𝔟 x => Submodule.mem_smul_top_iff 𝔟 Λ x
  have sp : ∀ (n : ℕ) (y : Fin N → E), y ∈ Ideal.span {(n : 𝓞 E)} • Λ ↔ ∃ e ∈ Λ, y = n • e := fun n y => by
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    simp only [Nat.cast_smul_eq_nsmul, eq_comm]
  let T : Λ →ₗ[𝓞 E] Λ := ((Matrix.mulVecLin γ).restrictScalars (𝓞 E)).restrict hγ - LinearMap.id
  have hT : ∀ x : Λ, (T x : Fin N → E) = γ *ᵥ x - x := fun _ => rfl
  have h𝔪 : 𝔪 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot, eq_comm, Ideal.span_singleton_eq_bot] at hprod
    exact hM.ne' (by exact_mod_cast hprod)
  have hc := map_ideal_smul_top_iff_cancel (𝓞 E) Λ 𝔪 𝔪' T h𝔪
  rw [mul_comm, hprod] at hc
  have hi := ideal_inf_smul_top_of_projective (𝓞 E) Λ 𝔪' (Ideal.span {(A : 𝓞 E)})
  simp only [← sub_eq_iff_eq_add', ← sp]
  constructor
  · rintro ⟨h1, h2⟩ x hx
    rw [← hT ⟨x, hx⟩, ← tr, hi]
    exact ⟨hc.1 (fun y hy => (tr _ _).2 (h1 y ((tr _ _).1 hy))) _, (tr _ _).2 (h2 x hx)⟩
  · intro h
    have h' : ∀ x : Λ, T x ∈ 𝔪' • (⊤ : Submodule (𝓞 E) Λ) ⊓ Ideal.span {(A : 𝓞 E)} • ⊤ := fun x => by
      rw [← hi, tr]; exact h x x.2
    exact ⟨fun x hx => (tr _ _).1 (hc.2 (fun y => (h' y).1) ⟨x, Submodule.smul_le_right hx⟩ ((tr _ _).2 hx)),
      fun x hx => (tr _ _).1 (h' ⟨x, hx⟩).2⟩

/- English proof (translation)
Establish `h : ∀ (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E), herm G x y = x ⬝ᵥ (G *ᵥ fun b => cc (y b))` using `fun G x y => by simp only [herm, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]`. Establish `e : (fun b => cc ((P *ᵥ y) b)) = P.map (ccH E) *ᵥ fun b => cc (y b)`. Use function extensionality and compare the values at `b`. Simplify using `[cc, Matrix.mulVec, dotProduct]`. Rewrite using `[h, h, e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x, Matrix.vecMul_transpose]`.
-/
theorem herm_mulVec' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (G P : Matrix (Fin r) (Fin r) E)
    (x y : Fin r → E) : herm G (P *ᵥ x) (P *ᵥ y) = herm (Pᵀ * G * P.map (ccH E)) x y := by
  have h : ∀ (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E), herm G x y = x ⬝ᵥ (G *ᵥ fun b => cc (y b)) :=
    fun G x y => by simp only [herm, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have e : (fun b => cc ((P *ᵥ y) b)) = P.map (ccH E) *ᵥ fun b => cc (y b) := by
    funext b
    simp [cc, Matrix.mulVec, dotProduct]
  rw [h, h, e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x, Matrix.vecMul_transpose]

/- English proof (translation)
Introduce `E _ _ _ r G G' a L' ha hL`. Set `f` to `(Matrix.mulVecLin (a : Matrix (Fin r) (Fin r) E)).restrictScalars (𝓞 E)`. Establish `hs : ∀ y, ∃ x, (a : Matrix (Fin r) (Fin r) E) *ᵥ x = y` using `fun y => ⟨((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ y, by rw [mulVec_mulVec, Units.mul_inv, one_mulVec]⟩`. Establish `hm : ∀ x, x ∈ L' ↔ (a : Matrix (Fin r) (Fin r) E) *ᵥ x ∈ L'.map f` using `fun x => ⟨fun h => ⟨x, h, rfl⟩, by`. Introduce and unpack `⟨y, hy, e⟩`.

Establish `e' : (a : Matrix (Fin r) (Fin r) E) *ᵥ y = (a : Matrix (Fin r) (Fin r) E) *ᵥ x` using `e`. Use `congrArg (fun v => ((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) e'` as an intermediate fact. Simplify using `only [mulVec_mulVec, Units.inv_mul, one_mulVec] at this`. Conclude with `this ▸ hy⟩`. Establish `hh : ∀ x y, herm G ((a : Matrix (Fin r) (Fin r) E) *ᵥ x) ((a : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G' x y` using `fun x y => by rw [herm_mulVec', ha]`.

Use `⟨L'.map f, ⟨hL.1.map f, ?_⟩, hm, fun h x => ?_, fun ξ ⟨h1, h2⟩ => ⟨?_, fun φ => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Submodule.map_coe, show (f : (Fin r → E) → Fin r → E) = Matrix.mulVecLin (a : Matrix (Fin r) (Fin r) E) from rfl, Submodule.span_image, hL.2, Submodule.map_top, LinearMap.range_eq_top]`. Conclude with `hs`. Take `⟨x, rfl⟩` from `hs x`. Rewrite using `[← hm, h]`.

Use `⟨?_, fun h y hy => hh x y ▸ h _ ((hm y).1 hy)⟩` and prove the remaining obligations. Introduce and unpack `h _ ⟨y, hy, rfl⟩`. Conclude with `(hh x y).symm ▸ h y hy`. Introduce and unpack `_ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩`. Take `⟨k, hk⟩` from `h1 x hx y hy`.

Conclude with `⟨k, (congrArg (fun t => Algebra.trace ℚ E (-ξ * t)) (hh x y)).trans hk⟩`. Take `⟨x, hx, e⟩` from `h2 (φ.comp (f.submoduleMap L').toAddMonoidHom)`. Use `⟨_, (hm x).1 hx, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨_, y, hy, rfl⟩`. Conclude with `(e ⟨y, hy⟩).trans (congrArg (fun t => Algebra.trace ℚ E (-ξ * t)) (hh x y)).symm`.
-/
theorem dualTransport : DualTransport := by
  intro E _ _ _ r G G' a L' ha hL
  let f := (Matrix.mulVecLin (a : Matrix (Fin r) (Fin r) E)).restrictScalars (𝓞 E)
  have hs : ∀ y, ∃ x, (a : Matrix (Fin r) (Fin r) E) *ᵥ x = y := fun y =>
    ⟨((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ y, by rw [mulVec_mulVec, Units.mul_inv, one_mulVec]⟩
  have hm : ∀ x, x ∈ L' ↔ (a : Matrix (Fin r) (Fin r) E) *ᵥ x ∈ L'.map f := fun x =>
    ⟨fun h => ⟨x, h, rfl⟩, by
      rintro ⟨y, hy, e⟩
      have e' : (a : Matrix (Fin r) (Fin r) E) *ᵥ y = (a : Matrix (Fin r) (Fin r) E) *ᵥ x := e
      have := congrArg (fun v => ((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) e'
      simp only [mulVec_mulVec, Units.inv_mul, one_mulVec] at this
      exact this ▸ hy⟩
  have hh : ∀ x y, herm G ((a : Matrix (Fin r) (Fin r) E) *ᵥ x) ((a : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G' x y :=
    fun x y => by rw [herm_mulVec', ha]
  refine ⟨L'.map f, ⟨hL.1.map f, ?_⟩, hm, fun h x => ?_, fun ξ ⟨h1, h2⟩ => ⟨?_, fun φ => ?_⟩⟩
  · rw [Submodule.map_coe, show (f : (Fin r → E) → Fin r → E) = Matrix.mulVecLin (a : Matrix (Fin r) (Fin r) E) from rfl,
      Submodule.span_image, hL.2, Submodule.map_top, LinearMap.range_eq_top]
    exact hs
  · obtain ⟨x, rfl⟩ := hs x
    rw [← hm, h]
    refine ⟨?_, fun h y hy => hh x y ▸ h _ ((hm y).1 hy)⟩
    rintro h _ ⟨y, hy, rfl⟩
    exact (hh x y).symm ▸ h y hy
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨k, hk⟩ := h1 x hx y hy
    exact ⟨k, (congrArg (fun t => Algebra.trace ℚ E (-ξ * t)) (hh x y)).trans hk⟩
  · obtain ⟨x, hx, e⟩ := h2 (φ.comp (f.submoduleMap L').toAddMonoidHom)
    refine ⟨_, (hm x).1 hx, ?_⟩
    rintro ⟨_, y, hy, rfl⟩
    exact (e ⟨y, hy⟩).trans (congrArg (fun t => Algebra.trace ℚ E (-ξ * t)) (hh x y)).symm

end PositivityTheory.EqVol
