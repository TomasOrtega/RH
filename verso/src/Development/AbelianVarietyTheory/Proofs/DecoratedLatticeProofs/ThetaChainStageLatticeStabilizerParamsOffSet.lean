import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatAgree

open GlobalTheory.AdelicU GlobalTheory.LFun Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

/- English proof (translation)
Establish `e : (N : v.adicCompletion K) = ((algebraMap R K (N : R) : K) : v.adicCompletion K)`. Rewrite using `[map_natCast]`. Conclude with `(map_natCast (algebraMap K (v.adicCompletion K)) N).symm`. Rewrite using `[e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `le_antisymm (v.intValuation_le_one _) (not_lt.1 fun h => hN ((v.intValuation_lt_one_iff_mem _).1 h))`.
-/
theorem valued_natCast_eq_one {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {v : HeightOneSpectrum R} {N : ℕ} (hN : (N : R) ∉ v.asIdeal) :
    Valued.v (N : v.adicCompletion K) = 1 := by
  have e : (N : v.adicCompletion K) = ((algebraMap R K (N : R) : K) : v.adicCompletion K) := by
    rw [map_natCast]; exact (map_natCast (algebraMap K (v.adicCompletion K)) N).symm
  rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  exact le_antisymm (v.intValuation_le_one _) (not_lt.1 fun h => hN ((v.intValuation_lt_one_iff_mem _).1 h))

/- English proof (translation)
Introduce `h` and use `by have := valued_natCast_eq_one (K := K) hN rw [h, map_zero] at this exact zero_ne_one this`.
-/
theorem natCast_ne_zero_of {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {v : HeightOneSpectrum R} {N : ℕ} (hN : (N : R) ∉ v.asIdeal) :
    (N : v.adicCompletion K) ≠ 0 := fun h => by
  have := valued_natCast_eq_one (K := K) hN
  rw [h, map_zero] at this
  exact zero_ne_one this

/- English proof (translation)
Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, valued_natCast_eq_one hN, inv_one]`.
-/
theorem inv_natCast_mem {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {v : HeightOneSpectrum R} {N : ℕ} (hN : (N : R) ∉ v.asIdeal) :
    (N : v.adicCompletion K)⁻¹ ∈ v.adicCompletionIntegers K := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, valued_natCast_eq_one hN, inv_one]

/- English proof (translation)
Introduce `y hy`. Use `latLoc_induction (p := fun y => y ∈ latLoc F L' v) (fun a ha x hx => ?_) (zero_mem _) (fun _ _ => add_mem) (fun _ => neg_mem) hy` and prove the remaining obligations. Establish `hN0` using `natCast_ne_zero_of (K := F) hN`. Establish `e : (fun i => a ⊗ₜ[F] x i) = fun i => (a * (N : Fv F v)⁻¹) ⊗ₜ[F] (((N : E) • x) i)`. Use function extensionality and compare the values at `i`.

Rewrite using `[Pi.smul_apply, show (N : E) • x i = (N : F) • x i by`. Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_natCast, map_natCast], TensorProduct.tmul_smul,`. Use the proof step `TensorProduct.smul_tmul', Algebra.smul_def, map_natCast]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e]`. Conclude with `tmul_mem_latLoc (mul_mem ha (inv_natCast_mem hN)) (h x hx)`.
-/
theorem latLoc_le {L L' : Submodule (𝓞 E) (Fin n → E)} {v : HeightOneSpectrum (𝓞 F)} {N : ℕ}
    (hN : (N : 𝓞 F) ∉ v.asIdeal) (h : ∀ x ∈ L, (N : E) • x ∈ L') : latLoc F L v ≤ latLoc F L' v := by
  intro y hy
  refine latLoc_induction (p := fun y => y ∈ latLoc F L' v) (fun a ha x hx => ?_) (zero_mem _)
    (fun _ _ => add_mem) (fun _ => neg_mem) hy
  have hN0 := natCast_ne_zero_of (K := F) hN
  have e : (fun i => a ⊗ₜ[F] x i) = fun i => (a * (N : Fv F v)⁻¹) ⊗ₜ[F] (((N : E) • x) i) := by
    funext i
    rw [Pi.smul_apply, show (N : E) • x i = (N : F) • x i by
      rw [Algebra.smul_def, Algebra.smul_def, map_natCast, map_natCast], TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', Algebra.smul_def, map_natCast]
    congr 1
    field_simp
  rw [e]
  exact tmul_mem_latLoc (mul_mem ha (inv_natCast_mem hN)) (h x hx)

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Establish `hN0` using `natCast_ne_zero_of (K := E) hN`. Establish `hm : (⟨(N : w.adicCompletion E)⁻¹, inv_natCast_mem hN⟩ : Ov E w) • (fun i => algebraMap E (w.adicCompletion E) (((N : E) • x) i)) = fun i => algebraMap E (w.adicCompletion E) (x i)`. Use function extensionality and compare the values at `i`.

Express the relevant statement in the definitionally equal form `(N : w.adicCompletion E)⁻¹ * algebraMap E _ ((N : E) • x i) = _`. Rewrite using `[smul_eq_mul, map_mul, map_natCast, inv_mul_cancel_left₀ hN0]`. Express the relevant statement in the definitionally equal form `(fun i => algebraMap E (w.adicCompletion E) (x i)) ∈ latAt w L'`. Rewrite using `[← hm]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h x hx, rfl⟩)`.
-/
theorem latAt_le {L L' : Submodule (𝓞 E) (Fin n → E)} {w : HeightOneSpectrum (𝓞 E)} {N : ℕ}
    (hN : (N : 𝓞 E) ∉ w.asIdeal) (h : ∀ x ∈ L, (N : E) • x ∈ L') : latAt w L ≤ latAt w L' := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  have hN0 := natCast_ne_zero_of (K := E) hN
  have hm : (⟨(N : w.adicCompletion E)⁻¹, inv_natCast_mem hN⟩ : Ov E w) •
      (fun i => algebraMap E (w.adicCompletion E) (((N : E) • x) i)) = fun i => algebraMap E (w.adicCompletion E) (x i) := by
    funext i
    change (N : w.adicCompletion E)⁻¹ * algebraMap E _ ((N : E) • x i) = _
    rw [smul_eq_mul, map_mul, map_natCast, inv_mul_cancel_left₀ hN0]
  change (fun i => algebraMap E (w.adicCompletion E) (x i)) ∈ latAt w L'
  rw [← hm]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h x hx, rfl⟩)

end GlobalTheory.LatAgree

namespace GlobalTheory.LatAgree

open GlobalTheory.AdelicU GlobalTheory.LFun Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

/- English proof (translation)
Simplify using `only [stabLoc, hs]`.
-/
theorem stabLoc_congr (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) {L L' : Submodule (𝓞 E) (Fin n → E)}
    {v : HeightOneSpectrum (𝓞 F)} (hs : latLoc F L v = latLoc F L' v) : stabLoc σ J L v = stabLoc σ J L' v := by
  simp only [stabLoc, hs]

/- English proof (translation)
Establish `hst` using `stabLoc_congr σ J hs`. Simplify using `only [IsParamVec, IsSplitChart, IsInertChart, IsFrameAt, hst, ha]`.
-/
theorem isParamVec_congr {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {L L' : Submodule (𝓞 E) (Fin n → E)}
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v)
    (hs : latLoc F L v = latLoc F L' v) (ha : latAt w L = latAt w L') {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GLoc σ J v) V) (x : V) (B : Multiset ℂˣ) :
    IsParamVec σ J L h ρ x B ↔ IsParamVec σ J L' h ρ x B := by
  have hst := stabLoc_congr σ J hs
  simp only [IsParamVec, IsSplitChart, IsInertChart, IsFrameAt, hst, ha]

/- English proof (translation)
Unfold `IsParamFun IsParamVecOff`. Use `forall₂_congr fun v hv => forall₂_congr fun w h => ?_` and prove the remaining obligations. Conclude with `isParamVec_congr h (hs v hv) (ha w (h ▸ hv)) _ _ _`.
-/
theorem isParamFun_congr {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {L L' : Submodule (𝓞 E) (Fin n → E)}
    {S : Set (HeightOneSpectrum (𝓞 F))} (hs : ∀ v ∉ S, latLoc F L v = latLoc F L' v)
    (ha : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∉ S → latAt w L = latAt w L')
    {V : Type} [AddCommGroup V] [Module ℂ V] (f : GAd σ J → V) (c : Fam E) :
    IsParamFun σ J L S f c ↔ IsParamFun σ J L' S f c := by
  unfold IsParamFun IsParamVecOff
  refine forall₂_congr fun v hv => forall₂_congr fun w h => ?_
  exact isParamVec_congr h (hs v hv) (ha w (h ▸ hv)) _ _ _

/- English proof (translation)
Use `v.isPrime` as an intermediate fact. Take `⟨Q, hQ, hl⟩` from `(Ideal.nonempty_primesOver v.asIdeal (S := 𝓞 E)).some`. Conclude with `⟨⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩`.
-/
theorem exists_under_eq (v : HeightOneSpectrum (𝓞 F)) : ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v := by
  have := v.isPrime
  obtain ⟨Q, hQ, hl⟩ := (Ideal.nonempty_primesOver v.asIdeal (S := 𝓞 E)).some
  exact ⟨⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩

/- English proof (translation)
Use `⟨fun v hv => ?_, fun w hw => le_antisymm (latAt_le (hN w hw) h₁) (latAt_le (hN w hw) h₂)⟩` and prove the remaining obligations. Take `⟨w, rfl⟩` from `exists_under_eq (E := E) v`. Establish `hv' : (N : 𝓞 F) ∉ (w.under (𝓞 F)).asIdeal` using `fun h => hN w hv (by`. Rewrite `h` using `[HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]`. Conclude with `h)`.

Conclude with `le_antisymm (latLoc_le hv' h₁) (latLoc_le hv' h₂)`.
-/
theorem latLoc_latAt_eq {L L' : Submodule (𝓞 E) (Fin n → E)} {S : Set (HeightOneSpectrum (𝓞 F))} {N : ℕ}
    (h₁ : ∀ x ∈ L, (N : E) • x ∈ L') (h₂ : ∀ x ∈ L', (N : E) • x ∈ L)
    (hN : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∉ S → (N : 𝓞 E) ∉ w.asIdeal) :
    (∀ v ∉ S, latLoc F L v = latLoc F L' v) ∧
      ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∉ S → latAt w L = latAt w L' := by
  refine ⟨fun v hv => ?_, fun w hw => le_antisymm (latAt_le (hN w hw) h₁) (latAt_le (hN w hw) h₂)⟩
  obtain ⟨w, rfl⟩ := exists_under_eq (E := E) v
  have hv' : (N : 𝓞 F) ∉ (w.under (𝓞 F)).asIdeal := fun h => hN w hv (by
    rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at h
    exact h)
  exact le_antisymm (latLoc_le hv' h₁) (latLoc_le hv' h₂)

end GlobalTheory.LatAgree

namespace GlobalTheory.ChainOnto

/- English proof (translation)
Introduce `D c _ j _ s hs`. Take `⟨N, ⟨-, -, -, h₁, h₂⟩, hN⟩` from `hs.base`. Establish `h₁' : ∀ x ∈ GlobalTheory.AdelicU.frameLat s.V, (N : D.host.E) • x ∈ s.Λ` using `fun x hx => h₁ x (by rw [GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]; exact hx)`. Establish `h₂' : ∀ x ∈ s.Λ, (N : D.host.E) • x ∈ GlobalTheory.AdelicU.frameLat s.V` using `fun x hx => by`. Use `h₂ x hx` as an intermediate fact.

Rewrite `this` using `[GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]`. Conclude with `this`. Take `⟨hloc, hat⟩` from `GlobalTheory.LatAgree.latLoc_latAt_eq (S := (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) h₂' h₁' (fun w hw => hN w hw)`. Conclude with `⟨fun v hv => GlobalTheory.LatAgree.stabLoc_congr _ _ (hloc v hv), fun f B => GlobalTheory.LatAgree.isParamFun_congr hloc hat f B⟩`.
-/
theorem stabLoc_isParamFun_frameLat : ∀ D : D7, ForStage D fun c _ s =>
    (∀ v ∉ c.S, GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v =
      GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram (GlobalTheory.AdelicU.frameLat s.V) v) ∧
    ∀ (f : GA D s.V → ℂ) (B : GlobalTheory.LFun.Fam D.host.E),
      GlobalTheory.LFun.IsParamFun D.sp.cm.sig s.V.gram s.Λ (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) f B ↔
        GlobalTheory.LFun.IsParamFunV s.V c.S f B := by
  intro D c _ j _ s hs
  obtain ⟨N, ⟨-, -, -, h₁, h₂⟩, hN⟩ := hs.base
  have h₁' : ∀ x ∈ GlobalTheory.AdelicU.frameLat s.V, (N : D.host.E) • x ∈ s.Λ := fun x hx =>
    h₁ x (by rw [GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]; exact hx)
  have h₂' : ∀ x ∈ s.Λ, (N : D.host.E) • x ∈ GlobalTheory.AdelicU.frameLat s.V := fun x hx => by
    have := h₂ x hx
    rw [GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice] at this
    exact this
  obtain ⟨hloc, hat⟩ := GlobalTheory.LatAgree.latLoc_latAt_eq (S := (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) h₂' h₁'
    (fun w hw => hN w hw)
  exact ⟨fun v hv => GlobalTheory.LatAgree.stabLoc_congr _ _ (hloc v hv),
    fun f B => GlobalTheory.LatAgree.isParamFun_congr hloc hat f B⟩

end GlobalTheory.ChainOnto
