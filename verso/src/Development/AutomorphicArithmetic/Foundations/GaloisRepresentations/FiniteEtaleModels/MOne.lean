import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LiftUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BiholomorphicLiftSystem

open NumberField GlobalTheory.UPel.HT

/- English proof (translation)
Introduce `q _ D hm`. Use `haveI := D.freeLa`. Use `haveI := D.finLa`. Establish `hb : Function.Bijective (algebraMap (𝓞 D.F) D.O)` using `⟨D.algebraMap_injective hm, Datum.algebraMap_surjective_of_m_eq_one q D hm⟩`. Establish `hfin : Module.Finite D.O D.La` using `Module.Finite.of_restrictScalars_finite ℤ D.O D.La`.

Use `⟨hb, ?_, hfin⟩` and prove the remaining obligations. Set `e : 𝓞 D.F ≃+* D.O` to `RingEquiv.ofBijective _ hb`. Use `letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)`. Establish `hsmul : ∀ (r : 𝓞 D.F) (x : D.La), r • x = algebraMap (𝓞 D.F) D.O r • x` using `fun _ _ => rfl`. Use `haveI : IsScalarTower ℤ (𝓞 D.F) D.La := ⟨fun n r x => by rw [hsmul, hsmul, map_zsmul, smul_assoc]⟩`.

Establish `htors : Submodule.torsion (𝓞 D.F) D.La = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce and unpack `x ⟨⟨r, hr⟩, hx⟩`. Establish `hx' : r • x = 0` using `hx`. Establish `hr0 : r ≠ 0` using `nonZeroDivisors.ne_zero hr`.

Take `⟨s, hs⟩` from `Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {r}))`. Establish `hN : Ideal.absNorm (Ideal.span {r}) ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]`. Conclude with `hr0`. Establish `hz : ((Ideal.absNorm (Ideal.span {r}) : ℕ) : ℤ) • x = 0`.

Establish `h1 : ((Ideal.absNorm (Ideal.span {r}) : ℕ) : ℤ) • x = ((Ideal.absNorm (Ideal.span {r}) : ℕ) : 𝓞 D.F) • x`. Rewrite using `[natCast_zsmul]`. Conclude with `(Nat.cast_smul_eq_nsmul (𝓞 D.F) _ x).symm`. Rewrite using `[h1, ← hs, mul_smul, hx', smul_zero]`. Conclude with `(smul_eq_zero.mp hz).resolve_left (by exact_mod_cast hN)`.

Use `haveI : Module.Flat (𝓞 D.F) D.La := IsDedekindDomain.flat_iff_torsion_eq_bot.mpr htors`. Use `haveI : Module.Finite (𝓞 D.F) D.La := Module.Finite.of_restrictScalars_finite ℤ _ _`. Use `haveI : Module.FinitePresentation (𝓞 D.F) D.La := Module.finitePresentation_of_finite _ _`. Use `haveI : Module.Projective (𝓞 D.F) D.La := Module.Flat.projective_of_finitePresentation`. Use `haveI h1 : RingHomInvPair (e : 𝓞 D.F →+* D.O) (e.symm : D.O →+* 𝓞 D.F) := RingHomInvPair.of_ringEquiv e`.

Use `haveI h2 : RingHomInvPair (e.symm : D.O →+* 𝓞 D.F) (e : 𝓞 D.F →+* D.O) := RingHomInvPair.symm _ _`. Set `f : D.La ≃ₛₗ[(e : 𝓞 D.F →+* D.O)] D.La` to `{ AddEquiv.refl D.La with map_smul' := fun _ _ => rfl }`. Conclude with `Module.Projective.of_equiv f`.
-/
theorem UpperTheory.Gal.FiniteEtaleModels.O.mOne :
    UpperTheory.Gal.FiniteEtaleModels.O.MOne := by
  intro q _ D hm
  haveI := D.freeLa
  haveI := D.finLa
  have hb : Function.Bijective (algebraMap (𝓞 D.F) D.O) :=
    ⟨D.algebraMap_injective hm, Datum.algebraMap_surjective_of_m_eq_one q D hm⟩
  have hfin : Module.Finite D.O D.La := Module.Finite.of_restrictScalars_finite ℤ D.O D.La
  refine ⟨hb, ?_, hfin⟩
  let e : 𝓞 D.F ≃+* D.O := RingEquiv.ofBijective _ hb
  letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  have hsmul : ∀ (r : 𝓞 D.F) (x : D.La), r • x = algebraMap (𝓞 D.F) D.O r • x :=
    fun _ _ => rfl
  haveI : IsScalarTower ℤ (𝓞 D.F) D.La :=
    ⟨fun n r x => by rw [hsmul, hsmul, map_zsmul, smul_assoc]⟩
  have htors : Submodule.torsion (𝓞 D.F) D.La = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨r, hr⟩, hx⟩
    have hx' : r • x = 0 := hx
    have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {r}))
    have hN : Ideal.absNorm (Ideal.span {r}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hr0
    have hz : ((Ideal.absNorm (Ideal.span {r}) : ℕ) : ℤ) • x = 0 := by
      have h1 : ((Ideal.absNorm (Ideal.span {r}) : ℕ) : ℤ) • x =
          ((Ideal.absNorm (Ideal.span {r}) : ℕ) : 𝓞 D.F) • x := by
        rw [natCast_zsmul]
        exact (Nat.cast_smul_eq_nsmul (𝓞 D.F) _ x).symm
      rw [h1, ← hs, mul_smul, hx', smul_zero]
    exact (smul_eq_zero.mp hz).resolve_left (by exact_mod_cast hN)
  haveI : Module.Flat (𝓞 D.F) D.La := IsDedekindDomain.flat_iff_torsion_eq_bot.mpr htors
  haveI : Module.Finite (𝓞 D.F) D.La := Module.Finite.of_restrictScalars_finite ℤ _ _
  haveI : Module.FinitePresentation (𝓞 D.F) D.La := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 D.F) D.La := Module.Flat.projective_of_finitePresentation
  haveI h1 : RingHomInvPair (e : 𝓞 D.F →+* D.O) (e.symm : D.O →+* 𝓞 D.F) :=
    RingHomInvPair.of_ringEquiv e
  haveI h2 : RingHomInvPair (e.symm : D.O →+* 𝓞 D.F) (e : 𝓞 D.F →+* D.O) :=
    RingHomInvPair.symm _ _
  let f : D.La ≃ₛₗ[(e : 𝓞 D.F →+* D.O)] D.La :=
    { AddEquiv.refl D.La with map_smul' := fun _ _ => rfl }
  exact Module.Projective.of_equiv f
