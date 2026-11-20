import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DisjointSpanPerpLat

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal GlobalTheory.SelfDualLatticeCompare

namespace GlobalTheory.UnramConjUnit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

open scoped TensorProduct Matrix in
open NumberField IsDedekindDomain in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
/- English proof (translation)
Introduce `hσ`. Take `⟨-, hE, -, hconj⟩` from `h`. Take `⟨w⟩ : Nonempty (InfinitePlace E)` from `inferInstance`. Establish `hc` using `hE.isComplex w`. Rewrite `hc` using `[← InfinitePlace.mk_embedding w, InfinitePlace.isComplex_mk_iff]`.

Apply `hc` to reduce the goal to its premises. Use extensionality with `x`. Simplify `(hconj w.embedding x).symm` using `[hσ x]`.
-/
theorem _root_.GlobalTheory.UnramConjUnit.conj_ne_id (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) : ¬ ∀ e, σ e = e := by
  intro hσ
  obtain ⟨-, hE, -, hconj⟩ := h
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hc := hE.isComplex w
  rw [← InfinitePlace.mk_embedding w, InfinitePlace.isComplex_mk_iff] at hc
  apply hc
  ext x
  simpa [hσ x] using (hconj w.embedding x).symm

open scoped TensorProduct Matrix in
open NumberField IsDedekindDomain in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in

/- English proof (translation)
Establish `hne` using `_root_.GlobalTheory.UnramConjUnit.conj_ne_id h`. Take `⟨-, -, hrank, -⟩` from `h`. Set `τ : E ≃ₐ[F] E` to `AlgEquiv.ofBijective σ σ.bijective`. Establish `hτ : ∀ x, τ x = σ x` using `fun _ => rfl`. Establish `hτ1 : τ ≠ 1` using `fun h1 => hne fun e => by rw [← hτ, h1]; rfl`.

Establish `hcard : Fintype.card (E ≃ₐ[F] E) = 2`. Use `le_antisymm (hrank ▸ AlgEquiv.card_le) ?_` and prove the remaining obligations. Establish `h2 : ({1, τ} : Finset (E ≃ₐ[F] E)).card = 2` using `Finset.card_pair (Ne.symm hτ1)`. Conclude with `h2 ▸ Finset.card_le_univ _`. Use `haveI : IsGalois F E := IsGalois.of_card_aut_eq_finrank F E (by rw [Nat.card_eq_fintype_card, hcard, hrank])`.

Establish `hG : ∀ g : E ≃ₐ[F] E, g = 1 ∨ g = τ`. Introduce `g`. Assume the negation of the conclusion as `hg`. Use `push_neg at hg`. Establish `h3 : ({g, 1, τ} : Finset (E ≃ₐ[F] E)).card = 3`.

Rewrite using `[Finset.card_insert_of_notMem (by simp [hg.1, hg.2]), Finset.card_pair (Ne.symm hτ1)]`. Use `h3 ▸ Finset.card_le_univ ({g, 1, τ} : Finset (E ≃ₐ[F] E))` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hττ : ∀ x, τ (τ x) = x`. Introduce `x`.

Break down `hG (τ * τ) with h2 | h2` into its components or cases. Conclude with `congrArg (fun g : E ≃ₐ[F] E => g x) h2`. Conclude with `absurd (mul_eq_right.mp h2) hτ1`. Take `⟨P, hP, hPv⟩` from `Ideal.exists_isPrime_liesOver_of_faithfullyFlat (B := 𝓞 E) v.asIdeal`. Establish `hPbot : P ≠ ⊥`.

Introduce and unpack `rfl`. Apply `v.ne_bot` to reduce the goal to its premises. Rewrite using `[hPv.over, Ideal.under, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]`. Establish `he` using `hv ⟨P, hP, hPbot⟩ hPv`. Establish `hin : τ ∉ Ideal.inertia (E ≃ₐ[F] E) P`.

Introduce `hmem`. Establish `h1` using `Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[F] E) v.asIdeal P`. Rewrite `h1` using `[Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal P (E ≃ₐ[F] E)]`. Establish `h1' : Nat.card (Ideal.inertia (E ≃ₐ[F] E) P) = 1` using `h1.trans he`. Rewrite `h1'` using `[Subgroup.card_eq_one]`.

Rewrite `hmem` using `[h1', Subgroup.mem_bot]`. Conclude with `hτ1 hmem`. Establish `hin' : ¬ ∀ x : 𝓞 E, τ • x - x ∈ P` using `fun hall => hin (AddSubgroup.mem_inertia.mpr hall)`. Use `push_neg at hin'`. Take `⟨x, hx⟩` from `hin'`.

Use `set d : 𝓞 E := x - τ • x with hd_def`. Establish `hd : d ∉ P` using `fun hd => hx (by rw [← neg_sub]; exact P.neg_mem hd)`. Establish `hdE : (d : E) = x - σ x` using `rfl`. Establish `hfix : ∀ g : E ≃ₐ[F] E, g ((d : E) * d) = (d : E) * d`. Introduce `g`.

Break down `hG g with rfl | rfl` into its components or cases. Both sides reduce to the same expression. Establish `: τ (d : E) = -(d : E)`. Rewrite using `[hdE, map_sub, ← hτ, hττ, neg_sub]`. Rewrite using `[map_mul, this, neg_mul_neg]`.

Take `⟨c, hc⟩` from `(IsGalois.mem_range_algebraMap_iff_fixed _).mpr hfix`. Establish `hcint : IsIntegral ℤ c`. Establish `hi : IsIntegral ℤ (algebraMap F E c)`. Rewrite using `[hc]`. Conclude with `((d * d : 𝓞 E)).isIntegral_coe`.

Conclude with `(isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ F E) (algebraMap F E).injective).mp hi`. Use `⟨x, d, ⟨c, hcint⟩, hdE, hc, ?_⟩` and prove the remaining obligations. Introduce `hs`. Establish `hmem : algebraMap (𝓞 F) (𝓞 E) ⟨c, hcint⟩ ∈ P`. Rewrite `hs` using `[hPv.over]`.

Conclude with `hs`. Establish `heq : algebraMap (𝓞 F) (𝓞 E) ⟨c, hcint⟩ = d * d`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `_ = (d : E) * d`. Rewrite using `[← hc]`.

Both sides reduce to the same expression. Rewrite `hmem` using `[heq]`. Conclude with `hd ((hP.mem_or_mem hmem).elim id id)`.
-/
theorem _root_.GlobalTheory.UnramConjUnit.exists_sub_conj_notMem (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ)
    (v : HeightOneSpectrum (𝓞 F)) (hv : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.UnramAt F E v) :
    ∃ (t d : 𝓞 E) (s : 𝓞 F), (d : E) = (t : E) - σ t ∧
      algebraMap F E (s : F) = (d : E) * d ∧ s ∉ v.asIdeal := by
  classical
  have hne := _root_.GlobalTheory.UnramConjUnit.conj_ne_id h
  obtain ⟨-, -, hrank, -⟩ := h
  let τ : E ≃ₐ[F] E := AlgEquiv.ofBijective σ σ.bijective
  have hτ : ∀ x, τ x = σ x := fun _ => rfl
  have hτ1 : τ ≠ 1 := fun h1 => hne fun e => by rw [← hτ, h1]; rfl
  have hcard : Fintype.card (E ≃ₐ[F] E) = 2 := by
    refine le_antisymm (hrank ▸ AlgEquiv.card_le) ?_
    have h2 : ({1, τ} : Finset (E ≃ₐ[F] E)).card = 2 := Finset.card_pair (Ne.symm hτ1)
    exact h2 ▸ Finset.card_le_univ _
  haveI : IsGalois F E := IsGalois.of_card_aut_eq_finrank F E
    (by rw [Nat.card_eq_fintype_card, hcard, hrank])
  have hG : ∀ g : E ≃ₐ[F] E, g = 1 ∨ g = τ := by
    intro g
    by_contra hg
    push_neg at hg
    have h3 : ({g, 1, τ} : Finset (E ≃ₐ[F] E)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hg.1, hg.2]), Finset.card_pair (Ne.symm hτ1)]
    have := h3 ▸ Finset.card_le_univ ({g, 1, τ} : Finset (E ≃ₐ[F] E))
    omega
  have hττ : ∀ x, τ (τ x) = x := by
    intro x
    rcases hG (τ * τ) with h2 | h2
    · exact congrArg (fun g : E ≃ₐ[F] E => g x) h2
    · exact absurd (mul_eq_right.mp h2) hτ1
  obtain ⟨P, hP, hPv⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat (B := 𝓞 E) v.asIdeal
  have hPbot : P ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [hPv.over, Ideal.under, Ideal.comap_bot_of_injective _
      (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]
  have he := hv ⟨P, hP, hPbot⟩ hPv
  have hin : τ ∉ Ideal.inertia (E ≃ₐ[F] E) P := by
    intro hmem
    have h1 := Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[F] E) v.asIdeal P
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal P (E ≃ₐ[F] E)] at h1
    have h1' : Nat.card (Ideal.inertia (E ≃ₐ[F] E) P) = 1 := h1.trans he
    rw [Subgroup.card_eq_one] at h1'
    rw [h1', Subgroup.mem_bot] at hmem
    exact hτ1 hmem
  have hin' : ¬ ∀ x : 𝓞 E, τ • x - x ∈ P := fun hall => hin (AddSubgroup.mem_inertia.mpr hall)
  push_neg at hin'
  obtain ⟨x, hx⟩ := hin'
  set d : 𝓞 E := x - τ • x with hd_def
  have hd : d ∉ P := fun hd => hx (by rw [← neg_sub]; exact P.neg_mem hd)
  have hdE : (d : E) = x - σ x := rfl
  have hfix : ∀ g : E ≃ₐ[F] E, g ((d : E) * d) = (d : E) * d := by
    intro g
    rcases hG g with rfl | rfl
    · rfl
    · have : τ (d : E) = -(d : E) := by
        rw [hdE, map_sub, ← hτ, hττ, neg_sub]
      rw [map_mul, this, neg_mul_neg]
  obtain ⟨c, hc⟩ := (IsGalois.mem_range_algebraMap_iff_fixed _).mpr hfix
  have hcint : IsIntegral ℤ c := by
    have hi : IsIntegral ℤ (algebraMap F E c) := by
      rw [hc]
      exact ((d * d : 𝓞 E)).isIntegral_coe
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ F E)
      (algebraMap F E).injective).mp hi
  refine ⟨x, d, ⟨c, hcint⟩, hdE, hc, ?_⟩
  intro hs
  have hmem : algebraMap (𝓞 F) (𝓞 E) ⟨c, hcint⟩ ∈ P := by
    rw [hPv.over] at hs
    exact hs
  have heq : algebraMap (𝓞 F) (𝓞 E) ⟨c, hcint⟩ = d * d := by
    apply RingOfIntegers.ext
    change _ = (d : E) * d
    rw [← hc]
    rfl
  rw [heq] at hmem
  exact hd ((hP.mem_or_mem hmem).elim id id)

open scoped TensorProduct Matrix in
open NumberField IsDedekindDomain in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ h v hv`. Take `⟨t, d, s, hd, hs, hsv⟩` from `_root_.GlobalTheory.UnramConjUnit.exists_sub_conj_notMem h v hv`. Establish `hu : Valued.v (algebraMap F (v.adicCompletion F) (s : F)) = 1`. Rewrite using `[HeightOneSpectrum.algebraMap_adicCompletion]`. Simplify using `only [Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply]`.

Rewrite using `[HeightOneSpectrum.adicCompletion.valued_coe]`. Conclude with `(HeightOneSpectrum.valuation_of_algebraMap v s).trans ((HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl v s).mpr hsv)`. Use `set u : v.adicCompletion F := algebraMap F (v.adicCompletion F) (s : F) with hu_def`. Establish `hu0 : u ≠ 0` using `fun h0 => by simp [h0] at hu`. Establish `huinv : u⁻¹ ∈ v.adicCompletionIntegers F`.

Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hu, inv_one]`. Establish `hintR : ∀ y : 𝓞 E, IsIntegral (v.adicCompletionIntegers F) ((1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (y : E))`. Introduce `y`. Conclude with `y.isIntegral_coe.map_of_comp_eq (Int.castRingHom _) (Algebra.TensorProduct.includeRight (R := F) (A := _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (B := E)).toRingHom (RingHom.ext_int _ _)`. Use `⟨(1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (t : E), hintR t, (u⁻¹ : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (d : E), ?_, ?_⟩` and prove the remaining obligations.

Establish `hb : (u⁻¹ : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (d : E) = algebraMap (v.adicCompletionIntegers F) (TensorProduct F (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) E) ⟨u⁻¹, huinv⟩ * ((1 : _root_.Formalism.MainNot …`. Rewrite using `[Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Both sides reduce to the same expression. Rewrite using `[hb]`. Conclude with `isIntegral_algebraMap.mul (hintR d)`.

Establish `hsub : (1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (t : E) - _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ ((1 : _root_.Formalism.MainNotion …`. Simplify using `[_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, hd, TensorProduct.tmul_sub]`. Rewrite using `[hsub, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hs, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def]`. Express the relevant statement in the definitionally equal form `(u * u⁻¹) ⊗ₜ[F] (1 : E) = 1`. Rewrite using `[mul_inv_cancel₀ hu0]`.

Both sides reduce to the same expression.
-/
theorem _root_.GlobalTheory.UnramConjUnit.exists_sub_conj_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ →
    ∀ v : HeightOneSpectrum (𝓞 F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.UnramAt F E v →
    ∃ θ ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.OEv F E v, ∃ b ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.OEv F E v,
      (θ - _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ θ) * b = 1 := by
  intro F E _ _ _ _ _ σ h v hv
  obtain ⟨t, d, s, hd, hs, hsv⟩ := _root_.GlobalTheory.UnramConjUnit.exists_sub_conj_notMem h v hv
  have hu : Valued.v (algebraMap F (v.adicCompletion F) (s : F)) = 1 := by
    rw [HeightOneSpectrum.algebraMap_adicCompletion]
    simp only [Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [HeightOneSpectrum.adicCompletion.valued_coe]
    exact (HeightOneSpectrum.valuation_of_algebraMap v s).trans
      ((HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl v s).mpr hsv)
  set u : v.adicCompletion F := algebraMap F (v.adicCompletion F) (s : F) with hu_def
  have hu0 : u ≠ 0 := fun h0 => by simp [h0] at hu
  have huinv : u⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hu, inv_one]
  have hintR : ∀ y : 𝓞 E, IsIntegral (v.adicCompletionIntegers F)
      ((1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (y : E)) := by
    intro y
    exact y.isIntegral_coe.map_of_comp_eq (Int.castRingHom _)
      (Algebra.TensorProduct.includeRight (R := F) (A := _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (B := E)).toRingHom
      (RingHom.ext_int _ _)
  refine ⟨(1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (t : E), hintR t,
    (u⁻¹ : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (d : E), ?_, ?_⟩
  · have hb : (u⁻¹ : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (d : E) =
        algebraMap (v.adicCompletionIntegers F) (TensorProduct F (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) E) ⟨u⁻¹, huinv⟩ *
          ((1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (d : E)) := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
        mul_one, one_mul]
      rfl
    rw [hb]
    exact isIntegral_algebraMap.mul (hintR d)
  · have hsub : (1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (t : E) -
        _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ ((1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (t : E)) =
        (1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (d : E) := by
      simp [_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, hd, TensorProduct.tmul_sub]
    rw [hsub, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hs, Algebra.algebraMap_eq_smul_one,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def]
    change (u * u⁻¹) ⊗ₜ[F] (1 : E) = 1
    rw [mul_inv_cancel₀ hu0]
    rfl

end GlobalTheory.UnramConjUnit
