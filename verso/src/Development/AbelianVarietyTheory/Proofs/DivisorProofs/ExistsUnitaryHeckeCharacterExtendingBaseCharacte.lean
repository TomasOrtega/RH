import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntFOneMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCongruenceKernelIdeleCharacterTrivialAtInfStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankSmulMemAdelesFiniteMultipleOfTensorCongruStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenIntegralTensorAdeleMultiplesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensorCongruenceOfSupportedAtInfinityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerOfAlgebraMapMemAdelesFiniteMultipleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatLeFourOfDvdOfEmbeddingsLeFourStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmExtensionConjugationInvolutiveFixedFieldStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open GlobalTheory.HeckeExtend

noncomputable section

namespace GlobalTheory.HeckeExtend

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨c, hc, e⟩` from `h`. Use `⟨c, hc, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `2 • x.2 = (2 * M) • c at e`. Establish `h2 : IsUnit (2 : Af F)`. Establish `: algebraMap F (Af F) 2 = 2` using `map_ofNat _ 2`.

Rewrite using `[← this]`. Conclude with `(IsUnit.mk0 (2 : F) two_ne_zero).map _`. Rewrite `e` using `[nsmul_eq_mul, nsmul_eq_mul, Nat.cast_mul, mul_assoc, Nat.cast_ofNat]`. Rewrite using `[nsmul_eq_mul]`. Conclude with `h2.mul_left_cancel e`.
-/
theorem intF_half {x : AF F} {M : ℕ} (h : 2 • x ∈ intF F (2 * M)) : x ∈ intF F M := by
  obtain ⟨c, hc, e⟩ := h
  refine ⟨c, hc, ?_⟩
  change 2 • x.2 = (2 * M) • c at e
  have h2 : IsUnit (2 : Af F) := by
    have : algebraMap F (Af F) 2 = 2 := map_ofNat _ 2
    rw [← this]
    exact (IsUnit.mk0 (2 : F) two_ne_zero).map _
  rw [nsmul_eq_mul, nsmul_eq_mul, Nat.cast_mul, mul_assoc, Nat.cast_ofNat] at e
  rw [nsmul_eq_mul]
  exact h2.mul_left_cancel e

/- English proof (translation)
Take `⟨c, hc, e⟩` from `h`. Use `⟨2 • c, fun v => ?_, ?_⟩` and prove the remaining obligations. Establish `: (2 • c) v = c v + c v` using `by rw [two_nsmul]; rfl`. Rewrite using `[this]`. Conclude with `add_mem (hc v) (hc v)`.

Rewrite using `[e, smul_smul, mul_comm]`.
-/
theorem intF_le {x : AF F} {M : ℕ} (h : x ∈ intF F (2 * M)) : x ∈ intF F M := by
  obtain ⟨c, hc, e⟩ := h
  refine ⟨2 • c, fun v => ?_, ?_⟩
  · have : (2 • c) v = c v + c v := by rw [two_nsmul]; rfl
    rw [this]
    exact add_mem (hc v) (hc v)
  · rw [e, smul_smul, mul_comm]

/- English proof (translation)
Take `⟨s, hs, e⟩` from `mem_CE.1 h`. Conclude with `mem_CE.2 ⟨cA σ s, cA_mem_SE σ hs, by rw [← e, map_nsmul]⟩`.
-/
theorem CE_cA (σ : E →ₐ[F] E) {N : ℕ} {z : AF F ⊗[F] E} (h : z ∈ CE F E N) : cA σ z ∈ CE F E N := by
  obtain ⟨s, hs, e⟩ := mem_CE.1 h
  exact mem_CE.2 ⟨cA σ s, cA_mem_SE σ hs, by rw [← e, map_nsmul]⟩

/- English proof (translation)
Use `show (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E) (algebraMap F E y) = _`. Rewrite using `[AlgHom.commutes, IsScalarTower.algebraMap_apply F (AF F) (AF F ⊗[F] E)]`.
-/
theorem incAF_algebraMap (y : F) :
    incAF F E (algebraMap F E y) = algebraMap (AF F) (AF F ⊗[F] E) (algebraMap F (AF F) y) := by
  show (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E) (algebraMap F E y) = _
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply F (AF F) (AF F ⊗[F] E)]

/- English proof (translation)
Use `letI : Algebra F ℂ := φ.toAlgebra`. Use `haveI : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.of_finite F E`. Conclude with `⟨(IsAlgClosed.lift : E →ₐ[F] ℂ).toRingHom, (IsAlgClosed.lift : E →ₐ[F] ℂ).comp_algebraMap⟩`.
-/
theorem exists_emb_ext (φ : F →+* ℂ) : ∃ τ : E →+* ℂ, τ.comp (algebraMap F E) = φ := by
  letI : Algebra F ℂ := φ.toAlgebra
  haveI : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.of_finite F E
  exact ⟨(IsAlgClosed.lift : E →ₐ[F] ℂ).toRingHom, (IsAlgClosed.lift : E →ₐ[F] ℂ).comp_algebraMap⟩

/- English proof (translation)
Take `⟨hσσ, hfix⟩` from `GlobalTheory.T.cmExtension_conjugation_involutive_fixedField F E σ hcm`. Establish `h2 : Module.finrank F E = 2` using `hcm.2.2.1`. Establish `htr : ∀ (N : ℕ) (x : AF F), algebraMap (AF F) (AF F ⊗[F] E) x ∈ CE F E (2 * (2 * N)) → x ∈ intF F N`. Introduce `N x hx`. Use `GlobalTheory.T.finrank_smul_mem_adelesFiniteMultiple_of_tensorCongruence F E _ x hx` as an intermediate fact.

Rewrite `this` using `[h2]`. Conclude with `intF_le (intF_half this)`. Establish `hcongF : ∀ b : (AF F)ˣ, idFF F E b ∈ WE F E (8 * M) → lam b = 1`. Introduce `b hb`. Establish `e8 : 8 * M = 2 * (2 * (2 * M))` using `by ring`.

Use `hMk b (intF_le (htr (2 * M) _ ?_)) (intF_le (htr (2 * M) _ ?_))` and prove the remaining obligations. Rewrite using `[← e8, map_sub, map_one]`. Conclude with `hb.1`. Rewrite using `[← e8, map_sub, map_one]`. Use `hb.2` as an intermediate fact.

Rewrite `this` using `[← map_inv]`. Then use the resulting hypothesis. Take `⟨y, ⟨k, rfl⟩, w, hw, hyw⟩` from `Subgroup.mem_sup.1 ha`. Set `cU : (AF F ⊗[F] E)ˣ →* (AF F ⊗[F] E)ˣ` to `Units.map (cA σ).toMonoidHom`. Establish `hcW : ∀ z ∈ WE F E (8 * M), cU z ∈ WE F E (8 * M)`. Introduce `z hz`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `CE_cA σ hz.1` as an intermediate fact. Rewrite `this` using `[map_sub, map_one]`. Then use the resulting hypothesis. Use `CE_cA σ hz.2` as an intermediate fact. Rewrite `this` using `[map_sub, map_one]`.

Rewrite using `[← map_inv]`. Conclude with `this`. Establish `hfixa : cU (idFF F E a) = idFF F E a` using `Units.ext ((cA σ).commutes (a : AF F))`. Establish `hcinc : cU (Units.map (incAF F E).toMonoidHom k) = Units.map (incAF F E).toMonoidHom (Units.map σ.toMonoidHom k)` using `Units.ext rfl`. Set `ζ : Eˣ` to `Units.map σ.toMonoidHom k * k⁻¹`.

Establish `hζW : Units.map (incAF F E).toMonoidHom ζ ∈ WE F E (8 * M)`. Establish `e1` using `congrArg cU hyw`. Rewrite `e1` using `[map_mul, hfixa, hcinc, ← hyw]`. Establish `: Units.map (incAF F E).toMonoidHom ζ = w * (cU w)⁻¹`. Simplify using `only [ζ, map_mul, map_inv]`.

Rewrite using `[mul_inv_eq_iff_eq_mul, mul_right_comm, eq_mul_inv_iff_mul_eq, e1, mul_comm]`. Rewrite using `[this]`. Conclude with `mul_mem hw (inv_mem (hcW w hw))`. Establish `hζv : (ζ : E) = σ k * (k : E)⁻¹` using `by simp [ζ]`. Establish `hζ1 : (ζ : E) = 1`.

Assume the negation of the conclusion as `hne`. Use `set x : E := (ζ : E) - 1 with hxdef`. Establish `hx0 : x ≠ 0` using `sub_ne_zero.2 hne`. Establish `hxC : incAF F E x ∈ CE F E (8 * M)`. Use `hζW.1` as an intermediate fact.

Rewrite using `[hxdef, map_sub, map_one]`. Conclude with `this`. Take `⟨s, hs, hsx⟩` from `mem_CE.1 hxC`. Establish `hσx : incAF F E (σ x) = cA σ (incAF F E x)` using `rfl`. Take `⟨y, hy⟩` from `hfix (x * σ x) (by rw [map_mul, hσσ, mul_comm])`.

Establish `hyC : algebraMap (AF F) (AF F ⊗[F] E) (algebraMap F (AF F) y) ∈ CE F E (2 * (2 * (16 * M * M)))`. Rewrite using `[← incAF_algebraMap, hy, map_mul, hσx, ← hsx, map_nsmul]`. Use `mem_CE.2 ⟨s * cA σ s, SE_mul hs (cA_mem_SE σ hs), ?_⟩` and prove the remaining obligations. Simplify using `only [nsmul_eq_mul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hyI` using `htr (16 * M * M) _ hyC`. Take `⟨r, hr⟩` from `GlobalTheory.T.exists_integer_of_algebraMap_mem_adelesFiniteMultiple F y (16 * M * M) (by positivity) hyI`. Establish `hy0 : y ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hy` using `[map_zero]`. Conclude with `mul_ne_zero hx0 ((map_ne_zero σ).2 hx0) hy.symm`. Establish `hbound : ∀ φ : F →+* ℂ, ‖φ y‖ ≤ 4`. Introduce `φ`. Take `⟨τ, hτ⟩` from `exists_emb_ext (E := E) φ`.

Establish `hφ : φ y = τ (algebraMap F E y)` using `by rw [← hτ]; rfl`. Establish `hτσ` using `hcm.2.2.2 τ`. Establish `hk0 : τ (k : E) ≠ 0` using `(map_ne_zero τ).2 k.ne_zero`. Establish `hζn : ‖τ (ζ : E)‖ = 1`. Rewrite using `[hζv, map_mul, map_inv₀, hτσ, norm_mul, norm_inv, norm_star]`.

Conclude with `mul_inv_cancel₀ (norm_ne_zero_iff.2 hk0)`. Establish `hxn : ‖τ x‖ ≤ 2`. Combine the equalities or inequalities in the displayed calculation. Use `_ ≤ ‖τ (ζ : E)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _`. Use `_ = 2 := by rw [hζn, norm_one]; norm_num`.

Rewrite using `[hφ, hy, map_mul, hτσ, norm_mul, norm_star]`. Use polynomial arithmetic with `[norm_nonneg (τ x)]`. Use `GlobalTheory.T.nat_le_four_of_dvd_of_embeddings_le_four' F y (16 * M * M) r hy0 hr hbound` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hk : σ k = (k : E)`.

Rewrite `hζ1` using `[hζv]`. Conclude with `(mul_inv_eq_one₀ k.ne_zero).1 hζ1`. Take `⟨f, hf⟩` from `hfix k hk`. Establish `hf0 : f ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hf` using `[map_zero]`. Conclude with `k.ne_zero hf.symm`. Set `fU : (AF F)ˣ` to `Units.map (algebraMap F (AF F)).toMonoidHom (Units.mk0 f hf0)`. Establish `hinc : Units.map (incAF F E).toMonoidHom k = idFF F E fU`. Apply `Units.ext` to reduce the goal to its premises.

Use `show incAF F E (k : E) = algebraMap (AF F) (AF F ⊗[F] E) (algebraMap F (AF F) f)`. Rewrite using `[← hf, incAF_algebraMap]`. Establish `hw' : w = idFF F E (fU⁻¹ * a)`. Rewrite using `[map_mul, map_inv, ← hinc, ← hyw]`. Use `group`.

Establish `hb` using `hcongF (fU⁻¹ * a) (hw' ▸ hw)`. Establish `hfU : lam fU = 1` using `h1 (Units.mk0 f hf0)`. Establish `: a = fU * (fU⁻¹ * a)` using `by group`. Rewrite using `[this, map_mul, hfU, hb, mul_one]`.
-/
theorem key (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (M : ℕ) (hM : 0 < M)
    (lam : (AF F)ˣ →* Circle) (h1 : ∀ a : Fˣ, lam (Units.map (algebraMap F (AF F)).toMonoidHom a) = 1)
    (hMk : ∀ b : (AF F)ˣ, (b : AF F) - 1 ∈ intF F M → ((b⁻¹ : (AF F)ˣ) : AF F) - 1 ∈ intF F M → lam b = 1)
    (a : (AF F)ˣ) (ha : idFF F E a ∈ (Units.map (incAF F E).toMonoidHom).range ⊔ WE F E (8 * M)) :
    lam a = 1 := by
  obtain ⟨hσσ, hfix⟩ := GlobalTheory.T.cmExtension_conjugation_involutive_fixedField F E σ hcm
  have h2 : Module.finrank F E = 2 := hcm.2.2.1
  have htr : ∀ (N : ℕ) (x : AF F), algebraMap (AF F) (AF F ⊗[F] E) x ∈ CE F E (2 * (2 * N)) → x ∈ intF F N := by
    intro N x hx
    have := GlobalTheory.T.finrank_smul_mem_adelesFiniteMultiple_of_tensorCongruence F E _ x hx
    rw [h2] at this
    exact intF_le (intF_half this)
  have hcongF : ∀ b : (AF F)ˣ, idFF F E b ∈ WE F E (8 * M) → lam b = 1 := by
    intro b hb
    have e8 : 8 * M = 2 * (2 * (2 * M)) := by ring
    refine hMk b (intF_le (htr (2 * M) _ ?_)) (intF_le (htr (2 * M) _ ?_))
    · rw [← e8, map_sub, map_one]
      exact hb.1
    · rw [← e8, map_sub, map_one]
      have := hb.2
      rwa [← map_inv] at this
  obtain ⟨y, ⟨k, rfl⟩, w, hw, hyw⟩ := Subgroup.mem_sup.1 ha
  let cU : (AF F ⊗[F] E)ˣ →* (AF F ⊗[F] E)ˣ := Units.map (cA σ).toMonoidHom
  have hcW : ∀ z ∈ WE F E (8 * M), cU z ∈ WE F E (8 * M) := by
    intro z hz
    refine ⟨?_, ?_⟩
    · have := CE_cA σ hz.1
      rwa [map_sub, map_one] at this
    · have := CE_cA σ hz.2
      rw [map_sub, map_one] at this
      rw [← map_inv]
      exact this
  have hfixa : cU (idFF F E a) = idFF F E a := Units.ext ((cA σ).commutes (a : AF F))
  have hcinc : cU (Units.map (incAF F E).toMonoidHom k) =
      Units.map (incAF F E).toMonoidHom (Units.map σ.toMonoidHom k) := Units.ext rfl
  let ζ : Eˣ := Units.map σ.toMonoidHom k * k⁻¹
  have hζW : Units.map (incAF F E).toMonoidHom ζ ∈ WE F E (8 * M) := by
    have e1 := congrArg cU hyw
    rw [map_mul, hfixa, hcinc, ← hyw] at e1
    have : Units.map (incAF F E).toMonoidHom ζ = w * (cU w)⁻¹ := by
      simp only [ζ, map_mul, map_inv]
      rw [mul_inv_eq_iff_eq_mul, mul_right_comm, eq_mul_inv_iff_mul_eq, e1, mul_comm]
    rw [this]
    exact mul_mem hw (inv_mem (hcW w hw))
  have hζv : (ζ : E) = σ k * (k : E)⁻¹ := by simp [ζ]
  have hζ1 : (ζ : E) = 1 := by
    by_contra hne
    set x : E := (ζ : E) - 1 with hxdef
    have hx0 : x ≠ 0 := sub_ne_zero.2 hne
    have hxC : incAF F E x ∈ CE F E (8 * M) := by
      have := hζW.1
      rw [hxdef, map_sub, map_one]
      exact this
    obtain ⟨s, hs, hsx⟩ := mem_CE.1 hxC
    have hσx : incAF F E (σ x) = cA σ (incAF F E x) := rfl
    obtain ⟨y, hy⟩ := hfix (x * σ x) (by rw [map_mul, hσσ, mul_comm])
    have hyC : algebraMap (AF F) (AF F ⊗[F] E) (algebraMap F (AF F) y) ∈ CE F E (2 * (2 * (16 * M * M))) := by
      rw [← incAF_algebraMap, hy, map_mul, hσx, ← hsx, map_nsmul]
      refine mem_CE.2 ⟨s * cA σ s, SE_mul hs (cA_mem_SE σ hs), ?_⟩
      simp only [nsmul_eq_mul]
      push_cast
      ring
    have hyI := htr (16 * M * M) _ hyC
    obtain ⟨r, hr⟩ := GlobalTheory.T.exists_integer_of_algebraMap_mem_adelesFiniteMultiple F y (16 * M * M) (by positivity) hyI
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [map_zero] at hy
      exact mul_ne_zero hx0 ((map_ne_zero σ).2 hx0) hy.symm
    have hbound : ∀ φ : F →+* ℂ, ‖φ y‖ ≤ 4 := by
      intro φ
      obtain ⟨τ, hτ⟩ := exists_emb_ext (E := E) φ
      have hφ : φ y = τ (algebraMap F E y) := by rw [← hτ]; rfl
      have hτσ := hcm.2.2.2 τ
      have hk0 : τ (k : E) ≠ 0 := (map_ne_zero τ).2 k.ne_zero
      have hζn : ‖τ (ζ : E)‖ = 1 := by
        rw [hζv, map_mul, map_inv₀, hτσ, norm_mul, norm_inv, norm_star]
        exact mul_inv_cancel₀ (norm_ne_zero_iff.2 hk0)
      have hxn : ‖τ x‖ ≤ 2 := by
        calc ‖τ x‖ = ‖τ (ζ : E) - 1‖ := by rw [hxdef, map_sub, map_one]
        _ ≤ ‖τ (ζ : E)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [hζn, norm_one]; norm_num
      rw [hφ, hy, map_mul, hτσ, norm_mul, norm_star]
      nlinarith [norm_nonneg (τ x)]
    have := GlobalTheory.T.nat_le_four_of_dvd_of_embeddings_le_four' F y (16 * M * M) r hy0 hr hbound
    nlinarith
  have hk : σ k = (k : E) := by
    rw [hζv] at hζ1
    exact (mul_inv_eq_one₀ k.ne_zero).1 hζ1
  obtain ⟨f, hf⟩ := hfix k hk
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [map_zero] at hf
    exact k.ne_zero hf.symm
  let fU : (AF F)ˣ := Units.map (algebraMap F (AF F)).toMonoidHom (Units.mk0 f hf0)
  have hinc : Units.map (incAF F E).toMonoidHom k = idFF F E fU := by
    apply Units.ext
    show incAF F E (k : E) = algebraMap (AF F) (AF F ⊗[F] E) (algebraMap F (AF F) f)
    rw [← hf, incAF_algebraMap]
  have hw' : w = idFF F E (fU⁻¹ * a) := by
    rw [map_mul, map_inv, ← hinc, ← hyw]
    group
  have hb := hcongF (fU⁻¹ * a) (hw' ▸ hw)
  have hfU : lam fU = 1 := h1 (Units.mk0 f hf0)
  have : a = fU * (fU⁻¹ * a) := by group
  rw [this, map_mul, hfU, hb, mul_one]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB lam hc h1 hinf`. Use `haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _`. Take `⟨M, hM, hMk⟩` from `GlobalTheory.T.exists_congruence_kernel_ideleCharacter_trivialAtInfinity F lam hc hinf`. Set `V : Subgroup (AF F ⊗[F] E)ˣ` to `(Units.map (incAF F E).toMonoidHom).range ⊔ WE F E (8 * M)`. Establish `hkey : ∀ a : (AF F)ˣ, idFF F E a ∈ V → lam a = 1` using `key σ hB.cm M hM lam h1 hMk`.

Establish `hN : 0 < 8 * M` using `by positivity`. Establish `hWo : IsOpen (WE F E (8 * M) : Set (AF F ⊗[F] E)ˣ)`. Establish `ho` using `GlobalTheory.T.isOpen_integralTensorAdeleMultiples F E (8 * M) hN`. Establish `hcv : Continuous fun z : (AF F ⊗[F] E)ˣ => (z : AF F ⊗[F] E) - 1` using `Units.continuous_val.sub continuous_const`. Establish `hci : Continuous fun z : (AF F ⊗[F] E)ˣ => ((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1` using `Units.continuous_coe_inv.sub continuous_const`.

Conclude with `(ho.preimage hcv).inter (ho.preimage hci)`. Establish `hVo : IsOpen (V : Set (AF F ⊗[F] E)ˣ)` using `Subgroup.isOpen_mono le_sup_right hWo`. Set `ψ0 : (AF F)ˣ →* (AF F ⊗[F] E)ˣ ⧸ V` to `(QuotientGroup.mk' V).comp (idFF F E)`. Establish `hker : ψ0.ker ≤ lam.ker` using `fun a ha => hkey a ((QuotientGroup.eq_one_iff _).1 ha)`. Use `letI : DivisibleBy (Additive Circle) ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn u => by`.

Take `⟨t, ht⟩` from `Circle.exp_surjective u.toMul`. Use `⟨Additive.ofMul (Circle.exp (t / n)), ?_⟩` and prove the remaining obligations. Use `show Additive.ofMul (Circle.exp (t / n) ^ n) = u`. Rewrite using `[← Circle.exp_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hn), ht]`. Both sides reduce to the same expression.

Use `letI : DivisibleBy (Additive Circle) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _`. Take `⟨ρ, hρ⟩` from `(Module.Baer.of_divisible (Additive Circle)).extension_property_addMonoidHom (MonoidHom.toAdditive (QuotientGroup.kerLift ψ0)) (QuotientGroup.kerLift_injective ψ0) (MonoidHom.toAdditive (QuotientGroup.lift ψ0.ker lam hker))`. Set `κ : (AF F ⊗[F] E)ˣ ⧸ V →* Circle` to `MonoidHom.toAdditive.symm ρ`. Establish `hκ : ∀ x, κ (QuotientGroup.kerLift ψ0 x) = QuotientGroup.lift ψ0.ker lam hker x` using `fun x => DFunLike.congr_fun hρ (Additive.ofMul x)`. Establish `hV1 : ∀ z ∈ V, κ.comp (QuotientGroup.mk' V) z = 1` using `fun z hz => by`.

Rewrite using `[MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).2 hz, map_one]`. Use `⟨κ.comp (QuotientGroup.mk' V), ⟨?_, fun x => hV1 _ (le_sup_left (a := (Units.map (incAF F E).toMonoidHom).range) ⟨x, rfl⟩)⟩, fun z hz => hV1 z (le_sup_right (a := (Units.map (incAF F E).toMonoidHom).range) ?_), fun a => hκ (a : (AF F)ˣ ⧸ ψ0.ker)⟩` and prove the remaining obligations. Use `continuous_of_continuousAt_one _ ?_` and prove the remaining obligations. Unfold `ContinuousAt`. Rewrite using `[map_one]`.

Use `tendsto_const_nhds.congr' ?_` and prove the remaining obligations. Use `filter_upwards [hVo.mem_nhds (one_mem V)] with z hz`. Conclude with `(hV1 z hz).symm`. Establish `hN'` using `hN`. Use `⟨GlobalTheory.T.mem_tensorCongruence_of_supported_at_infinity F E _ hN' _ hz, GlobalTheory.T.mem_tensorCongruence_of_supported_at_infinity F E _ hN' _ ?_⟩` and prove the remaining obligations.

Introduce `u hu`. Establish `e : ((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 = -(((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * ((z : AF F ⊗[F] E) - 1))`. Rewrite using `[mul_sub, Units.inv_mul, mul_one, neg_sub]`. Rewrite using `[e, smul_neg, ← mul_smul_comm, hz u hu, mul_zero, neg_zero]`.
-/
theorem exists_extend_hecke : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ lam : (AF F)ˣ →* Circle, Continuous lam →
      (∀ a : Fˣ, lam (Units.map (algebraMap F (AF F)).toMonoidHom a) = 1) →
      (∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) → lam a = 1) →
      ∃ lam' : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF lam' ∧
        (∀ z : (AF F ⊗[F] E)ˣ, At (evI F) ((z : AF F ⊗[F] E) - 1) → lam' z = 1) ∧
        ∀ a, lam' (idFF F E a) = lam a := by
  intro F E _ _ _ _ _ σ B hB lam hc h1 hinf
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨M, hM, hMk⟩ := GlobalTheory.T.exists_congruence_kernel_ideleCharacter_trivialAtInfinity F lam hc hinf
  let V : Subgroup (AF F ⊗[F] E)ˣ := (Units.map (incAF F E).toMonoidHom).range ⊔ WE F E (8 * M)
  have hkey : ∀ a : (AF F)ˣ, idFF F E a ∈ V → lam a = 1 := key σ hB.cm M hM lam h1 hMk
  have hN : 0 < 8 * M := by positivity
  have hWo : IsOpen (WE F E (8 * M) : Set (AF F ⊗[F] E)ˣ) := by
    have ho := GlobalTheory.T.isOpen_integralTensorAdeleMultiples F E (8 * M) hN
    have hcv : Continuous fun z : (AF F ⊗[F] E)ˣ => (z : AF F ⊗[F] E) - 1 :=
      Units.continuous_val.sub continuous_const
    have hci : Continuous fun z : (AF F ⊗[F] E)ˣ => ((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 :=
      Units.continuous_coe_inv.sub continuous_const
    exact (ho.preimage hcv).inter (ho.preimage hci)
  have hVo : IsOpen (V : Set (AF F ⊗[F] E)ˣ) := Subgroup.isOpen_mono le_sup_right hWo

  let ψ0 : (AF F)ˣ →* (AF F ⊗[F] E)ˣ ⧸ V := (QuotientGroup.mk' V).comp (idFF F E)
  have hker : ψ0.ker ≤ lam.ker := fun a ha => hkey a ((QuotientGroup.eq_one_iff _).1 ha)
  letI : DivisibleBy (Additive Circle) ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn u => by
    obtain ⟨t, ht⟩ := Circle.exp_surjective u.toMul
    refine ⟨Additive.ofMul (Circle.exp (t / n)), ?_⟩
    show Additive.ofMul (Circle.exp (t / n) ^ n) = u
    rw [← Circle.exp_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hn), ht]
    rfl
  letI : DivisibleBy (Additive Circle) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨ρ, hρ⟩ := (Module.Baer.of_divisible (Additive Circle)).extension_property_addMonoidHom
    (MonoidHom.toAdditive (QuotientGroup.kerLift ψ0)) (QuotientGroup.kerLift_injective ψ0)
    (MonoidHom.toAdditive (QuotientGroup.lift ψ0.ker lam hker))
  let κ : (AF F ⊗[F] E)ˣ ⧸ V →* Circle := MonoidHom.toAdditive.symm ρ
  have hκ : ∀ x, κ (QuotientGroup.kerLift ψ0 x) = QuotientGroup.lift ψ0.ker lam hker x :=
    fun x => DFunLike.congr_fun hρ (Additive.ofMul x)
  have hV1 : ∀ z ∈ V, κ.comp (QuotientGroup.mk' V) z = 1 := fun z hz => by
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).2 hz, map_one]
  refine ⟨κ.comp (QuotientGroup.mk' V), ⟨?_, fun x => hV1 _ (le_sup_left (a := (Units.map (incAF F E).toMonoidHom).range)
    ⟨x, rfl⟩)⟩, fun z hz => hV1 z (le_sup_right (a := (Units.map (incAF F E).toMonoidHom).range) ?_), fun a => hκ (a : (AF F)ˣ ⧸ ψ0.ker)⟩
  · refine continuous_of_continuousAt_one _ ?_
    unfold ContinuousAt
    rw [map_one]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hVo.mem_nhds (one_mem V)] with z hz
    exact (hV1 z hz).symm
  · have hN' := hN
    refine ⟨GlobalTheory.T.mem_tensorCongruence_of_supported_at_infinity F E _ hN' _ hz, GlobalTheory.T.mem_tensorCongruence_of_supported_at_infinity F E _ hN' _ ?_⟩
    intro u hu
    have e : ((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 = -(((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * ((z : AF F ⊗[F] E) - 1)) := by
      rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
    rw [e, smul_neg, ← mul_smul_comm, hz u hu, mul_zero, neg_zero]

end GlobalTheory.HeckeExtend

end
