import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralExtensionFiniteAdelesBasicProperties
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.St.G.FrLoc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

/- English proof (translation)
The claim follows from `RingHom.congr_fun (Formalism.UG.P.afsplit_prV_comp_sigR σ v) a`.
-/
theorem prV_sigR (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : E ⊗[F] Ad F) :
    prV (E := E) v (sigR σ (Ad F) a) = sigR σ (v.adicCompletion F) (prV (E := E) v a) :=
  RingHom.congr_fun (Formalism.UG.P.afsplit_prV_comp_sigR σ v) a

/- English proof (translation)
The claim follows from `((GlobalTheory.St.G.IntAd.integral_adeles_properties F E).1 a).1 ha v`.
-/
theorem prV_OAd (v : HeightOneSpectrum (𝓞 F)) {a : E ⊗[F] Ad F} (ha : a ∈ OAd F E) :
    prV (E := E) v a ∈ intV E v :=
  ((GlobalTheory.St.G.IntAd.integral_adeles_properties F E).1 a).1 ha v

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[prVec, map_add]`.
-/
theorem prVec_add (v : HeightOneSpectrum (𝓞 F)) (x y : Fin n → E ⊗[F] Ad F) :
    prVec v (x + y) = prVec v x + prVec v y := by
  funext i; simp [prVec, map_add]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[prVec]`.
-/
theorem prVec_zero (v : HeightOneSpectrum (𝓞 F)) : prVec v (0 : Fin n → E ⊗[F] Ad F) = 0 := by
  funext i; simp [prVec]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[prVec, map_mul]`.
-/
theorem prVec_smul (v : HeightOneSpectrum (𝓞 F)) (a : E ⊗[F] Ad F) (x : Fin n → E ⊗[F] Ad F) :
    prVec v (a • x) = prV (E := E) v a • prVec v x := by
  funext i; simp [prVec, map_mul]

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x h => exact Submodule.subset_span ⟨x, h, rfl⟩`. Consider the case `zero => rw [prVec_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [prVec_add]`.

Conclude with `add_mem hx hy`. Consider the case `smul a x _ hx`. Establish `h : prVec v (a • x) = (⟨prV (E` using `E) v a, prV_OAd v a.2⟩ : intV E v) • prVec v x := prVec_smul v (a : E ⊗[F] Ad F) x`. Rewrite using `[h]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem prVec_span (v : HeightOneSpectrum (𝓞 F)) (S : Set (Fin n → E ⊗[F] Ad F))
    {x : Fin n → E ⊗[F] Ad F} (hx : x ∈ Submodule.span (OAd F E) S) :
    prVec v x ∈ Submodule.span (intV E v) (prVec v '' S) := by
  induction hx using Submodule.span_induction with
  | mem x h => exact Submodule.subset_span ⟨x, h, rfl⟩
  | zero => rw [prVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [prVec_add]; exact add_mem hx hy
  | smul a x _ hx =>
    have h : prVec v (a • x) = (⟨prV (E := E) v a, prV_OAd v a.2⟩ : intV E v) • prVec v x :=
      prVec_smul v (a : E ⊗[F] Ad F) x
    rw [h]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Establish `h` using `prVec_span v _ hx`. Use `Submodule.span_mono ?_ h` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨l, hl, rfl⟩, rfl⟩`. Conclude with `⟨l, hl, rfl⟩`.
-/
theorem prVec_hat (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin n → E))
    {x : Fin n → E ⊗[F] Ad F} (hx : x ∈ hat F L) : prVec v x ∈ loc v L := by
  have h := prVec_span v _ hx
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
  exact ⟨l, hl, rfl⟩

/- English proof (translation)
Simplify using `only [hR, hform, map_sum, map_mul, prV_sigR, prVec, Matrix.map_apply, Formalism.UG.P.afsplit_prV_inclE]`.
-/
theorem hR_prVec (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (x y : Fin n → E ⊗[F] Ad F) :
    hR σ J (v.adicCompletion F) (prVec v x) (prVec v y) = prV (E := E) v (hR σ J (Ad F) x y) := by
  simp only [hR, hform, map_sum, map_mul, prV_sigR, prVec, Matrix.map_apply, Formalism.UG.P.afsplit_prV_inclE]

end GlobalTheory.St.G.FrLoc

open GlobalTheory.St.G.FrLoc in
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J L g k Fr v`. Use `⟨?_, ?_, prV_OAd v Fr.eps_int, ?_, fun i => prVec_hat v L (Fr.b_mem i), fun i => prVec_hat v L (Fr.bd_mem i), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_mul, Fr.eps_idem]`. Rewrite using `[← prV_sigR, ← map_mul, Fr.eps_orth, map_zero]`. Introduce `y hy`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨l, hl, rfl⟩` from `hy`. Take `⟨z, hz, hzeq⟩` from `Fr.eps_full (fun i => inclE (F := F) (Ad F) (l i)) (Submodule.subset_span ⟨l, hl, rfl⟩)`. Use `⟨prVec v z, prVec_hat v L hz, ?_⟩` and prove the remaining obligations.

Establish `h` using `congrArg (prVec v) hzeq`. Rewrite `h` using `[prVec_smul, prVec_smul, map_sub, map_sub, map_one, prV_sigR, map_natCast]`. Conclude with `h`. Consider the case `zero => exact ⟨0, zero_mem _, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨z₁, hz₁, e₁⟩` from `hx`. Take `⟨z₂, hz₂, e₂⟩` from `hy`. Conclude with `⟨z₁ + z₂, add_mem hz₁ hz₂, by rw [smul_add, smul_add, e₁, e₂]⟩`. Consider the case `smul c x _ hx`. Take `⟨z, hz, e⟩` from `hx`.

Use `⟨c • z, Submodule.smul_mem _ c hz, ?_⟩` and prove the remaining obligations. Rewrite using `[Subring.smul_def, Subring.smul_def, smul_smul, mul_comm, ← smul_smul, e, smul_smul, smul_smul, mul_comm]`. Introduce `i`. Establish `h` using `congrArg (prVec v) (Fr.b_eps i)`. Rewrite `h` using `[prVec_smul]`.

Conclude with `h`. Introduce `i`. Establish `h` using `congrArg (prVec v) (Fr.bd_eps i)`. Rewrite `h` using `[prVec_smul, prV_sigR]`. Conclude with `h`.

Introduce `i j`. Take `⟨t, ht, e⟩` from `Fr.dual i j`. Use `⟨prV (E := E) v t, prV_OAd v ht, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (prV (E := E) v) e`. Rewrite `h` using `[map_sub, map_mul, map_natCast, ← hR_prVec, apply_ite (prV (E := E) v), map_zero]`.

Conclude with `h`. Establish `hsub : prVec v '' (Set.range Fr.b ∪ Set.range Fr.bd) ⊆ Set.range (fun j => prVec v (Fr.b j)) ∪ Set.range (fun j => prVec v (Fr.bd j))`. Introduce and unpack `_ ⟨x, hx | hx, rfl⟩`. Take `⟨j, rfl⟩` from `hx`. Conclude with `Or.inl ⟨j, rfl⟩`.

Take `⟨j, rfl⟩` from `hx`. Conclude with `Or.inr ⟨j, rfl⟩`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨l, hl, rfl⟩` from `hy`. Take `⟨s, hs, z, hz, e⟩` from `Fr.span (fun i => inclE (F := F) (Ad F) (l i)) (Submodule.subset_span ⟨l, hl, rfl⟩)`. Use `⟨prVec v s, Submodule.span_mono hsub (prVec_span v _ hs), prVec v z, prVec_hat v L hz, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (prVec v) e`. Rewrite `h` using `[prVec_add, prVec_smul, map_natCast]`.

Conclude with `h`. Consider the case `zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨s₁, hs₁, z₁, hz₁, e₁⟩` from `hx`. Take `⟨s₂, hs₂, z₂, hz₂, e₂⟩` from `hy`.

Use `⟨s₁ + s₂, add_mem hs₁ hs₂, z₁ + z₂, add_mem hz₁ hz₂, ?_⟩` and prove the remaining obligations. Rewrite using `[e₁, e₂, smul_add]`. Normalize the expressions using the abelian group laws. Consider the case `smul c x _ hx`. Take `⟨s, hs, z, hz, e⟩` from `hx`.

Use `⟨c • s, Submodule.smul_mem _ c hs, c • z, Submodule.smul_mem _ c hz, ?_⟩` and prove the remaining obligations. Rewrite using `[e, smul_add, Subring.smul_def, Subring.smul_def, Subring.smul_def, smul_smul, smul_smul, mul_comm]`.
-/
theorem GlobalTheory.St.G.frame_component_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (g k : ℕ) (Fr : AdFrame σ J (hat F L) g k) (v : HeightOneSpectrum (𝓞 F)), prV (E := E) v Fr.eps * prV (E := E) v Fr.eps = prV (E := E) v Fr.eps ∧ prV (E := E) v Fr.eps * sigR σ (v.adicCompletion F) (prV (E := E) v Fr.eps) = 0 ∧ prV (E := E) v Fr.eps ∈ intV E v ∧ (∀ y ∈ loc v L, ∃ z ∈ loc v L, (1 - prV (E := E) v Fr.eps - sigR σ (v.adicCompletion F) (prV (E := E) v Fr.eps)) • y = (g : E ⊗[F] v.adicCompletion F) • z) ∧ (∀ i, prVec v (Fr.b i) ∈ loc v L) ∧ (∀ i, prVec v (Fr.bd i) ∈ loc v L) ∧ (∀ i, prVec v (Fr.b i) = prV (E := E) v Fr.eps • prVec v (Fr.b i)) ∧ (∀ i, prVec v (Fr.bd i) = sigR σ (v.adicCompletion F) (prV (E := E) v Fr.eps) • prVec v (Fr.bd i)) ∧ (∀ i j, ∃ t ∈ intV E v, hR σ J (v.adicCompletion F) (prVec v (Fr.bd i)) (prVec v (Fr.b j)) - (if i = j then prV (E := E) v Fr.eps else 0) = (g : E ⊗[F] v.adicCompletion F) * t) ∧ (∀ y ∈ loc v L, InModL (loc v L) g (Set.range (fun j => prVec v (Fr.b j)) ∪ Set.range (fun j => prVec v (Fr.bd j))) y) := by
  intro F E _ _ _ _ _ σ n J L g k Fr v
  refine ⟨?_, ?_, prV_OAd v Fr.eps_int, ?_, fun i => prVec_hat v L (Fr.b_mem i),
    fun i => prVec_hat v L (Fr.bd_mem i), ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, Fr.eps_idem]
  · rw [← prV_sigR, ← map_mul, Fr.eps_orth, map_zero]
  · intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hy
      obtain ⟨z, hz, hzeq⟩ := Fr.eps_full (fun i => inclE (F := F) (Ad F) (l i))
        (Submodule.subset_span ⟨l, hl, rfl⟩)
      refine ⟨prVec v z, prVec_hat v L hz, ?_⟩
      have h := congrArg (prVec v) hzeq
      rw [prVec_smul, prVec_smul, map_sub, map_sub, map_one, prV_sigR, map_natCast] at h
      exact h
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨z₁, hz₁, e₁⟩ := hx
      obtain ⟨z₂, hz₂, e₂⟩ := hy
      exact ⟨z₁ + z₂, add_mem hz₁ hz₂, by rw [smul_add, smul_add, e₁, e₂]⟩
    | smul c x _ hx =>
      obtain ⟨z, hz, e⟩ := hx
      refine ⟨c • z, Submodule.smul_mem _ c hz, ?_⟩
      rw [Subring.smul_def, Subring.smul_def, smul_smul, mul_comm, ← smul_smul, e, smul_smul,
        smul_smul, mul_comm]
  · intro i
    have h := congrArg (prVec v) (Fr.b_eps i)
    rw [prVec_smul] at h
    exact h
  · intro i
    have h := congrArg (prVec v) (Fr.bd_eps i)
    rw [prVec_smul, prV_sigR] at h
    exact h
  · intro i j
    obtain ⟨t, ht, e⟩ := Fr.dual i j
    refine ⟨prV (E := E) v t, prV_OAd v ht, ?_⟩
    have h := congrArg (prV (E := E) v) e
    rw [map_sub, map_mul, map_natCast, ← hR_prVec, apply_ite (prV (E := E) v), map_zero] at h
    exact h
  · have hsub : prVec v '' (Set.range Fr.b ∪ Set.range Fr.bd) ⊆
        Set.range (fun j => prVec v (Fr.b j)) ∪ Set.range (fun j => prVec v (Fr.bd j)) := by
      rintro _ ⟨x, hx | hx, rfl⟩
      · obtain ⟨j, rfl⟩ := hx; exact Or.inl ⟨j, rfl⟩
      · obtain ⟨j, rfl⟩ := hx; exact Or.inr ⟨j, rfl⟩
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hy
      obtain ⟨s, hs, z, hz, e⟩ := Fr.span (fun i => inclE (F := F) (Ad F) (l i))
        (Submodule.subset_span ⟨l, hl, rfl⟩)
      refine ⟨prVec v s, Submodule.span_mono hsub (prVec_span v _ hs), prVec v z, prVec_hat v L hz, ?_⟩
      have h := congrArg (prVec v) e
      rw [prVec_add, prVec_smul, map_natCast] at h
      exact h
    | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s₁, hs₁, z₁, hz₁, e₁⟩ := hx
      obtain ⟨s₂, hs₂, z₂, hz₂, e₂⟩ := hy
      refine ⟨s₁ + s₂, add_mem hs₁ hs₂, z₁ + z₂, add_mem hz₁ hz₂, ?_⟩
      rw [e₁, e₂, smul_add]; abel
    | smul c x _ hx =>
      obtain ⟨s, hs, z, hz, e⟩ := hx
      refine ⟨c • s, Submodule.smul_mem _ c hs, c • z, Submodule.smul_mem _ c hz, ?_⟩
      rw [e, smul_add, Subring.smul_def, Subring.smul_def, Subring.smul_def, smul_smul, smul_smul,
        mul_comm]
