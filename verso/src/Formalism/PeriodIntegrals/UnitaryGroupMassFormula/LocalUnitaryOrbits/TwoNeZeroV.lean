import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.UnitOfPair
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.IsCompactSpanRange
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.HRSumSmulRight

noncomputable section

namespace PI.OmLocU.UnN

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix Formalism.UG PI.OmLocU.Orb PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Take `⟨-, hE, hdeg, hconj⟩` from `hcm`. Assume the negation of the conclusion as `hne`. Establish `hbot : e ∉ (⊥ : IntermediateField F E)`. Introduce `hmem`. Take `⟨f, hf⟩` from `IntermediateField.mem_bot.mp hmem`.

Conclude with `hne ⟨f, hf⟩`. Establish `hint : IsIntegral F e` using `Algebra.IsIntegral.isIntegral e`. Establish `htop : (IntermediateField.adjoin F {e}) = ⊤`. Establish `hd : Module.finrank F (IntermediateField.adjoin F {e}) ∣ 2`. Use `IntermediateField.finrank_dvd_of_le_right (K := F) (le_top : (IntermediateField.adjoin F {e}) ≤ ⊤)` as an intermediate fact.

Rewrite `this` using `[IntermediateField.finrank_top', hdeg]`. Then use the resulting hypothesis. Establish `h1 : Module.finrank F (IntermediateField.adjoin F {e}) ≠ 1`. Rewrite using `[Ne, IntermediateField.finrank_eq_one_iff, IntermediateField.adjoin_simple_eq_bot_iff]`. Conclude with `hbot`. Establish `h22 : Module.finrank F (IntermediateField.adjoin F {e}) = 2`.

Break down `(Nat.dvd_prime Nat.prime_two).mp hd with h | h` into its components or cases. Conclude with `absurd h h1`. Conclude with `h`. Apply `IntermediateField.eq_of_le_of_finrank_eq le_top` to reduce the goal to its premises. Rewrite using `[h22, IntermediateField.finrank_top', hdeg]`.

Establish `hfix : ∀ x : E, σ x = x`. Introduce `x`. Establish `hx : x ∈ Algebra.adjoin F ({e} : Set E)`. Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, htop]`. Discharge the goal by the elementary cases of `trivial`.

Establish `hle : Algebra.adjoin F ({e} : Set E) ≤ AlgHom.equalizer σ (AlgHom.id F E)`. Rewrite using `[Algebra.adjoin_le_iff]`. Introduce `y hy`. Rewrite `hy` using `[Set.mem_singleton_iff]`. Substitute `hy` using the available equality.

Conclude with `he`. Conclude with `hle hx`. Take `⟨w⟩ : Nonempty (NumberField.InfinitePlace E)` from `inferInstance`. Apply `NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr (hE.isComplex w)` to reduce the goal to its premises. Rewrite using `[NumberField.InfinitePlace.isReal_iff, NumberField.ComplexEmbedding.isReal_iff]`.

Use extensionality with `x`. Establish `h` using `hconj w.embedding x`. Rewrite `h` using `[hfix]`. Rewrite using `[NumberField.ComplexEmbedding.conjugate_coe_eq, starRingEnd_apply, ← h]`.
-/
theorem fixed_mem_F (hcm : IsCMExt F E σ) (e : E) (he : σ e = e) : ∃ f : F, algebraMap F E f = e := by
  obtain ⟨-, hE, hdeg, hconj⟩ := hcm
  by_contra hne
  have hbot : e ∉ (⊥ : IntermediateField F E) := by
    intro hmem
    obtain ⟨f, hf⟩ := IntermediateField.mem_bot.mp hmem
    exact hne ⟨f, hf⟩
  have hint : IsIntegral F e := Algebra.IsIntegral.isIntegral e
  have htop : (IntermediateField.adjoin F {e}) = ⊤ := by
    have hd : Module.finrank F (IntermediateField.adjoin F {e}) ∣ 2 := by
      have := IntermediateField.finrank_dvd_of_le_right (K := F) (le_top : (IntermediateField.adjoin F {e}) ≤ ⊤)
      rwa [IntermediateField.finrank_top', hdeg] at this
    have h1 : Module.finrank F (IntermediateField.adjoin F {e}) ≠ 1 := by
      rw [Ne, IntermediateField.finrank_eq_one_iff, IntermediateField.adjoin_simple_eq_bot_iff]
      exact hbot
    have h22 : Module.finrank F (IntermediateField.adjoin F {e}) = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
      · exact absurd h h1
      · exact h
    apply IntermediateField.eq_of_le_of_finrank_eq le_top
    rw [h22, IntermediateField.finrank_top', hdeg]
  have hfix : ∀ x : E, σ x = x := by
    intro x
    have hx : x ∈ Algebra.adjoin F ({e} : Set E) := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, htop]
      trivial
    have hle : Algebra.adjoin F ({e} : Set E) ≤ AlgHom.equalizer σ (AlgHom.id F E) := by
      rw [Algebra.adjoin_le_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact he
    exact hle hx
  obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace E) := inferInstance
  apply NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr (hE.isComplex w)
  rw [NumberField.InfinitePlace.isReal_iff, NumberField.ComplexEmbedding.isReal_iff]
  ext x
  have h := hconj w.embedding x
  rw [hfix] at h
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq, starRingEnd_apply, ← h]

/- English proof (translation)
Simplify using `[sc, Algebra.TensorProduct.algebraMap_apply]`.
-/
theorem sc_eq (a : Fv F v) : sc (E := E) v a = algebraMap (Fv F v) (Fv F v ⊗[F] E) a := by
  simp [sc, Algebra.TensorProduct.algebraMap_apply]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, by simp [sc_eq]⟩`. Consider the case `tmul r e`. Take `⟨f, hf⟩` from `fixed_mem_F σ hcm (e + σ e) (by rw [map_add, sigma_invol σ hcm, add_comm])`. Use `⟨f • r, ?_⟩` and prove the remaining obligations.

Establish `hs : sigR (Fv F v) σ (r ⊗ₜ[F] e) = r ⊗ₜ[F] σ e`. Simplify using `[Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.map_tmul]`. Rewrite using `[hs, ← TensorProduct.tmul_add, ← hf, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]`. Both sides reduce to the same expression. Consider the case `add x y hx hy`.

Take `⟨t1, h1⟩` from `hx`. Take `⟨t2, h2⟩` from `hy`. Use `⟨t1 + t2, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, sc_eq, map_add, ← sc_eq, ← sc_eq, ← h1, ← h2]`. Normalize the expressions using the abelian group laws.
-/
theorem add_sig_sc (hcm : IsCMExt F E σ) (z : Fv F v ⊗[F] E) : ∃ t : Fv F v, z + sigR (Fv F v) σ z = sc (E := E) v t := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp [sc_eq]⟩
  | tmul r e =>
    obtain ⟨f, hf⟩ := fixed_mem_F σ hcm (e + σ e) (by rw [map_add, sigma_invol σ hcm, add_comm])
    refine ⟨f • r, ?_⟩
    have hs : sigR (Fv F v) σ (r ⊗ₜ[F] e) = r ⊗ₜ[F] σ e := by
      simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.map_tmul]
    rw [hs, ← TensorProduct.tmul_add, ← hf, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]
    rfl
  | add x y hx hy =>
    obtain ⟨t1, h1⟩ := hx
    obtain ⟨t2, h2⟩ := hy
    refine ⟨t1 + t2, ?_⟩
    rw [map_add, sc_eq, map_add, ← sc_eq, ← sc_eq, ← h1, ← h2]
    abel

/- English proof (translation)
Establish `h : (2 : F) ≠ 0` using `two_ne_zero`. Introduce `h2`. Apply `h` to reduce the goal to its premises. Apply `(algebraMap F (Fv F v)).injective` to reduce the goal to its premises. Rewrite using `[map_ofNat, map_zero]`.

Conclude with `h2`.
-/
theorem two_ne_zero_v : (2 : Fv F v) ≠ 0 := by
  have h : (2 : F) ≠ 0 := two_ne_zero
  intro h2
  apply h
  apply (algebraMap F (Fv F v)).injective
  rw [map_ofNat, map_zero]
  exact h2

/- English proof (translation)
Take `⟨t, ht⟩` from `add_sig_sc σ v hcm z`. Rewrite `ht` using `[hz]`. Use `⟨t / 2, ?_⟩` and prove the remaining obligations. Rewrite using `[div_eq_inv_mul, ← sc_mul, ← ht, ← smul_eq_sc, ← two_smul (Fv F v) z, smul_smul, inv_mul_cancel₀ (two_ne_zero_v v), one_smul]`.
-/
theorem fix_sc (hcm : IsCMExt F E σ) (z : Fv F v ⊗[F] E) (hz : sigR (Fv F v) σ z = z) :
    ∃ a : Fv F v, z = sc (E := E) v a := by
  obtain ⟨t, ht⟩ := add_sig_sc σ v hcm z
  rw [hz] at ht
  refine ⟨t / 2, ?_⟩
  rw [div_eq_inv_mul, ← sc_mul, ← ht, ← smul_eq_sc, ← two_smul (Fv F v) z, smul_smul,
    inv_mul_cancel₀ (two_ne_zero_v v), one_smul]

/- English proof (translation)
Simplify using `using gen_mem (E := E) v 1`.
-/
theorem one_mem_oEv : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
  simpa using gen_mem (E := E) v 1

/- English proof (translation)
Simplify using `using sc_mul_mem_oEv (E := E) v hc (one_mem_oEv v)`.
-/
theorem sc_mem {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F) : sc (E := E) v c ∈ OEv (E := E) v := by
  simpa using sc_mul_mem_oEv (E := E) v hc (one_mem_oEv v)

def oAlg : Subalgebra (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :=
  Submodule.toSubalgebra (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)) (by exact one_mem_oEv v)
    (fun _ _ hx hy => by exact oEv_mul v hx hy)

/- English proof (translation)
Establish `hle : OEv (E` using `E) v ⊆ {z | IsIntegral (v.adicCompletionIntegers F) z} := by show (Submodule.span (v.adicCompletionIntegers F) ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) : Set (Fv F v ⊗[F] E)) ⊆ _`. Introduce `z hz`. Establish `hsp : Submodule.span (v.adicCompletionIntegers F) ((fun x : 𝓞 E => inclR (F` using `F) (Fv F v) (x : E)) '' Set.univ) ≤ (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E)).toSubmodule := by`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, -, rfl⟩`.

Conclude with `IsIntegral.map_of_comp_eq (Int.castRingHom (v.adicCompletionIntegers F)) (inclR (F := F) (Fv F v)) (RingHom.ext_int _ _) (RingOfIntegers.isIntegral_coe x)`. Conclude with `hsp hz`. Establish `hint : IsIntegral (v.adicCompletionIntegers F) (algebraMap (Fv F v) (Fv F v ⊗[F] E) a)`. Rewrite using `[← sc_eq]`. Conclude with `hle ha`.

Establish `hint' : IsIntegral (v.adicCompletionIntegers F) a` using `(isIntegral_algHom_iff (IsScalarTower.toAlgHom (v.adicCompletionIntegers F) (Fv F v) (Fv F v ⊗[F] E)) (algebraMap (Fv F v) (Fv F v ⊗[F] E)).injective).mp hint`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hint'`. Rewrite using `[← hy]`. Conclude with `y.2`.
-/
theorem sc_mem_int {a : Fv F v} (ha : sc (E := E) v a ∈ OEv (E := E) v) : a ∈ v.adicCompletionIntegers F := by
  have hle : OEv (E := E) v ⊆ {z | IsIntegral (v.adicCompletionIntegers F) z} := by
    show (Submodule.span (v.adicCompletionIntegers F)
      ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) : Set (Fv F v ⊗[F] E)) ⊆ _
    intro z hz
    have hsp : Submodule.span (v.adicCompletionIntegers F)
        ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) ≤
        (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E)).toSubmodule := by
      rw [Submodule.span_le]
      rintro _ ⟨x, -, rfl⟩
      exact IsIntegral.map_of_comp_eq (Int.castRingHom (v.adicCompletionIntegers F)) (inclR (F := F) (Fv F v))
        (RingHom.ext_int _ _) (RingOfIntegers.isIntegral_coe x)
    exact hsp hz
  have hint : IsIntegral (v.adicCompletionIntegers F) (algebraMap (Fv F v) (Fv F v ⊗[F] E) a) := by
    rw [← sc_eq]
    exact hle ha
  have hint' : IsIntegral (v.adicCompletionIntegers F) a :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom (v.adicCompletionIntegers F) (Fv F v) (Fv F v ⊗[F] E))
      (algebraMap (Fv F v) (Fv F v ⊗[F] E)).injective).mp hint
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint'
  rw [← hy]
  exact y.2

/- English proof (translation)
Take `⟨a, ha⟩` from `fix_sc σ v hcm z hz`. Conclude with `⟨a, sc_mem_int v (ha ▸ hz0), ha⟩`.
-/
theorem fix_int (hcm : IsCMExt F E σ) {z : Fv F v ⊗[F] E} (hz0 : z ∈ OEv (E := E) v) (hz : sigR (Fv F v) σ z = z) :
    ∃ a ∈ v.adicCompletionIntegers F, z = sc (E := E) v a := by
  obtain ⟨a, ha⟩ := fix_sc σ v hcm z hz
  exact ⟨a, sc_mem_int v (ha ▸ hz0), ha⟩

/- English proof (translation)
Take `⟨u, hu'⟩` from `hu`. Use `⟨sc v ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F), sc_mem v (SetLike.coe_mem _), ?_⟩` and prove the remaining obligations. Establish `h1 : a * (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : Fv F v) = 1`. Establish `h2` using `congrArg (fun r : v.adicCompletionIntegers F => (r : Fv F v)) u.mul_inv`. Rewrite `h2` using `[hu']`.

Simplify using `using h2`. Rewrite using `[sc_mul, h1, sc_one]`.
-/
theorem isU_sc {a : Fv F v} (ha : a ∈ v.adicCompletionIntegers F)
    (hu : IsUnit (⟨a, ha⟩ : v.adicCompletionIntegers F)) : IsU v (sc (E := E) v a) := by
  obtain ⟨u, hu'⟩ := hu
  refine ⟨sc v ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F), sc_mem v (SetLike.coe_mem _), ?_⟩
  have h1 : a * (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : Fv F v) = 1 := by
    have h2 := congrArg (fun r : v.adicCompletionIntegers F => (r : Fv F v)) u.mul_inv
    rw [hu'] at h2
    simpa using h2
  rw [sc_mul, h1, sc_one]

/- English proof (translation)
Take `⟨w, hw, hcw⟩` from `h`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Rewrite `hcw` using `[sc_eq, map_zero, zero_mul]`. Conclude with `zero_ne_one hcw`.

Establish `hweq : w = sc v c⁻¹`. Establish `h1 : sc (E` using `E) v c⁻¹ * (sc v c * w) = sc v c⁻¹ := by rw [hcw, mul_one]`. Rewrite `h1` using `[← mul_assoc, sc_mul, inv_mul_cancel₀ hc0, sc_one, one_mul]`. Conclude with `h1`. Establish `hinv : c⁻¹ ∈ v.adicCompletionIntegers F` using `sc_mem_int v (hweq ▸ hw)`.

Establish `hprod : (⟨c, hc⟩ : v.adicCompletionIntegers F) * ⟨c⁻¹, hinv⟩ = 1`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[mul_inv_cancel₀ hc0]`. Conclude with `IsUnit.of_mul_eq_one _ hprod`.
-/
private theorem fixLoc_holds_lemma {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F)
    (h : IsU (E := E) v (sc v c)) : IsUnit (⟨c, hc⟩ : v.adicCompletionIntegers F) := by
  obtain ⟨w, hw, hcw⟩ := h
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [sc_eq, map_zero, zero_mul] at hcw
    exact zero_ne_one hcw
  have hweq : w = sc v c⁻¹ := by
    have h1 : sc (E := E) v c⁻¹ * (sc v c * w) = sc v c⁻¹ := by rw [hcw, mul_one]
    rw [← mul_assoc, sc_mul, inv_mul_cancel₀ hc0, sc_one, one_mul] at h1
    exact h1
  have hinv : c⁻¹ ∈ v.adicCompletionIntegers F := sc_mem_int v (hweq ▸ hw)
  have hprod : (⟨c, hc⟩ : v.adicCompletionIntegers F) * ⟨c⁻¹, hinv⟩ = 1 := by
    apply Subtype.ext
    simp [mul_inv_cancel₀ hc0]
  exact IsUnit.of_mul_eq_one _ hprod

/- English proof (translation)
Introduce `hcm x hx y hy hfx hfy hu`. Take `⟨a, ha, rfl⟩` from `fix_int σ v hcm hx hfx`. Take `⟨b, hb, rfl⟩` from `fix_int σ v hcm hy hfy`. Establish `hab : a + b ∈ v.adicCompletionIntegers F` using `add_mem ha hb`. Rewrite `hu` using `[sc_eq, sc_eq, ← map_add, ← sc_eq]`.

Establish `hU : IsUnit ((⟨a, ha⟩ : v.adicCompletionIntegers F) + ⟨b, hb⟩)` using `fixLoc_holds_lemma v hab hu`. Break down `IsLocalRing.isUnit_or_isUnit_of_isUnit_add hU with h | h` into its components or cases. Conclude with `Or.inl (isU_sc v ha h)`. Conclude with `Or.inr (isU_sc v hb h)`.
-/
theorem fixLoc_holds : FixLoc σ v := by
  intro hcm x hx y hy hfx hfy hu
  obtain ⟨a, ha, rfl⟩ := fix_int σ v hcm hx hfx
  obtain ⟨b, hb, rfl⟩ := fix_int σ v hcm hy hfy
  have hab : a + b ∈ v.adicCompletionIntegers F := add_mem ha hb
  rw [sc_eq, sc_eq, ← map_add, ← sc_eq] at hu
  have hU : IsUnit ((⟨a, ha⟩ : v.adicCompletionIntegers F) + ⟨b, hb⟩) := fixLoc_holds_lemma v hab hu
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hU with h | h
  · exact Or.inl (isU_sc v ha h)
  · exact Or.inr (isU_sc v hb h)

end PI.OmLocU.UnN
