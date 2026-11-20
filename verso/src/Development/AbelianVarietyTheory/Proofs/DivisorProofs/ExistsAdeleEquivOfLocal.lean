import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.AdelicScalarMultiplier
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.IdeleNormTraceForm

open NumberField IsDedekindDomain TensorProduct

noncomputable section

namespace GlobalTheory.NormLevelCompare

section Adeles

open Rat.HeightOneSpectrum

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `⟨AlgEquiv.refl, fun _ => Iff.rfl⟩`.
-/
theorem padic_cast {p q : Nat.Primes} (h : p = q) :
    ∃ e : ℚ_[p] ≃ₐ[ℚ] ℚ_[q], ∀ x, e x ∈ PadicInt.subring q ↔ x ∈ PadicInt.subring p := by
  subst h
  exact ⟨AlgEquiv.refl, fun _ => Iff.rfl⟩

/- English proof (translation)
Use `⟨fun hx => ?_, fun hx => (adicCompletion.padicEquiv_bijOn v).mapsTo hx⟩` and prove the remaining obligations. Take `⟨y, hy, hxy⟩` from `(adicCompletion.padicEquiv_bijOn v).surjOn hx`. Take `rfl : y = x` from `(adicCompletion.padicEquiv v).injective hxy`. Conclude with `hy`.
-/
theorem padicEquiv_mem {R : Type} [CommRing R] [Algebra R ℚ] [IsIntegralClosure R ℤ ℚ]
    [IsDedekindDomain R] [IsFractionRing R ℚ] (v : HeightOneSpectrum R)
    (x : v.adicCompletion ℚ) :
    adicCompletion.padicEquiv v x ∈ PadicInt.subring (primesEquiv v) ↔
      x ∈ v.adicCompletionIntegers ℚ := by
  refine ⟨fun hx => ?_, fun hx => (adicCompletion.padicEquiv_bijOn v).mapsTo hx⟩
  obtain ⟨y, hy, hxy⟩ := (adicCompletion.padicEquiv_bijOn v).surjOn hx
  obtain rfl : y = x := (adicCompletion.padicEquiv v).injective hxy
  exact hy

def primeCorr : HeightOneSpectrum ℤ ≃ HeightOneSpectrum (𝓞 ℚ) :=
  (primesEquiv (R := ℤ)).trans (primesEquiv (R := 𝓞 ℚ)).symm

/- English proof (translation)
Establish `h : primesEquiv (primeCorr w) = primesEquiv w` using `by simp [primeCorr]`. Take `⟨c, hc⟩` from `padic_cast h`. Use `⟨((adicCompletion.padicEquiv (primeCorr w)).toAlgEquiv.trans c).trans (adicCompletion.padicEquiv w).symm.toAlgEquiv, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[← padicEquiv_mem w, ← padicEquiv_mem (primeCorr w), ← hc]`. Express the relevant statement in the definitionally equal form `adicCompletion.padicEquiv w ((adicCompletion.padicEquiv w).symm _) ∈ _ ↔ _`.

Rewrite using `[ContinuousAlgEquiv.apply_symm_apply]`. Both sides reduce to the same expression.
-/
theorem exists_local (w : HeightOneSpectrum ℤ) :
    ∃ e : (primeCorr w).adicCompletion ℚ ≃ₐ[ℚ] w.adicCompletion ℚ,
      ∀ x, e x ∈ w.adicCompletionIntegers ℚ ↔ x ∈ (primeCorr w).adicCompletionIntegers ℚ := by
  have h : primesEquiv (primeCorr w) = primesEquiv w := by simp [primeCorr]
  obtain ⟨c, hc⟩ := padic_cast h
  refine ⟨((adicCompletion.padicEquiv (primeCorr w)).toAlgEquiv.trans c).trans
    (adicCompletion.padicEquiv w).symm.toAlgEquiv, fun x => ?_⟩
  rw [← padicEquiv_mem w, ← padicEquiv_mem (primeCorr w), ← hc]
  change adicCompletion.padicEquiv w ((adicCompletion.padicEquiv w).symm _) ∈ _ ↔ _
  rw [ContinuousAlgEquiv.apply_symm_apply]
  rfl

/- English proof (translation)
Set `φ : FiniteAdeleRing R K →ₐ[K] FiniteAdeleRing R' K` to `{ toFun := fun a => ⟨fun w => e w (a (σ w)), by`. Establish `h1` using `σ.injective.tendsto_cofinite.eventually a.2`. Conclude with `h1.mono fun w hw => (he w _).2 hw⟩`. Use the proof step `map_one' := FiniteAdeleRing.ext _ fun w => map_one (e w)`. Use the proof step `map_mul' := fun a b => FiniteAdeleRing.ext _ fun w => map_mul (e w) _ _`.

Use the proof step `map_zero' := FiniteAdeleRing.ext _ fun w => map_zero (e w)`. Use the proof step `map_add' := fun a b => FiniteAdeleRing.ext _ fun w => map_add (e w) _ _`. Use the proof step `commutes' := fun r => FiniteAdeleRing.ext _ fun w => (e w).commutes r }`. Establish `hφ : ∀ a w, φ a w = e w (a (σ w))` using `fun _ _ => rfl`. Establish `hinj : Function.Injective φ`.

Introduce `a b hab`. Use `FiniteAdeleRing.ext _ fun v => ?_` and prove the remaining obligations. Take `⟨w, rfl⟩` from `σ.surjective v`. Apply `(e w).injective` to reduce the goal to its premises. Rewrite using `[← hφ, ← hφ, hab]`.

Establish `hsurj : Function.Surjective φ`. Introduce `b`. Set `f : ∀ v : HeightOneSpectrum R, v.adicCompletion K` to `Equiv.piCongrLeft (fun v : HeightOneSpectrum R => v.adicCompletion K) σ (fun w => (e w).symm (b w))`. Establish `hf : ∀ w, f (σ w) = (e w).symm (b w)` using `fun w => Equiv.piCongrLeft_apply_apply _ _ _ _`. Use `⟨⟨f, ?_⟩, FiniteAdeleRing.ext _ fun w => ?_⟩` and prove the remaining obligations.

Establish `h1` using `σ.symm.injective.tendsto_cofinite.eventually b.2`. Use `h1.mono fun v hv => ?_` and prove the remaining obligations. Take `⟨w, rfl⟩` from `σ.surjective v`. Rewrite `hv` using `[Equiv.symm_apply_apply]`. Express the relevant statement in the definitionally equal form `f (σ w) ∈ (σ w).adicCompletionIntegers K`.

Rewrite using `[hf, ← he, AlgEquiv.apply_symm_apply]`. Conclude with `hv`. Express the relevant statement in the definitionally equal form `e w (f (σ w)) = _`. Rewrite using `[hf, AlgEquiv.apply_symm_apply]`. Use `⟨AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩, fun a => ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(∀ w, φ a w ∈ w.adicCompletionIntegers K) ↔ ∀ v : HeightOneSpectrum R, a v ∈ v.adicCompletionIntegers K`. Rewrite using `[σ.surjective.forall]`. Conclude with `forall_congr' fun w => he w _`.
-/
theorem exists_adele_equiv_of_local {R R' K : Type} [CommRing R] [IsDedekindDomain R]
    [CommRing R'] [IsDedekindDomain R'] [Field K] [Algebra R K] [IsFractionRing R K]
    [Algebra R' K] [IsFractionRing R' K] (σ : HeightOneSpectrum R' ≃ HeightOneSpectrum R)
    (e : ∀ w, (σ w).adicCompletion K ≃ₐ[K] w.adicCompletion K)
    (he : ∀ w x, e w x ∈ w.adicCompletionIntegers K ↔ x ∈ (σ w).adicCompletionIntegers K) :
    ∃ e : FiniteAdeleRing R K ≃ₐ[K] FiniteAdeleRing R' K,
      ∀ a, (∀ w, e a w ∈ w.adicCompletionIntegers K) ↔
        ∀ v, a v ∈ v.adicCompletionIntegers K := by
  let φ : FiniteAdeleRing R K →ₐ[K] FiniteAdeleRing R' K :=
    { toFun := fun a => ⟨fun w => e w (a (σ w)), by
        have h1 := σ.injective.tendsto_cofinite.eventually a.2
        exact h1.mono fun w hw => (he w _).2 hw⟩
      map_one' := FiniteAdeleRing.ext _ fun w => map_one (e w)
      map_mul' := fun a b => FiniteAdeleRing.ext _ fun w => map_mul (e w) _ _
      map_zero' := FiniteAdeleRing.ext _ fun w => map_zero (e w)
      map_add' := fun a b => FiniteAdeleRing.ext _ fun w => map_add (e w) _ _
      commutes' := fun r => FiniteAdeleRing.ext _ fun w => (e w).commutes r }
  have hφ : ∀ a w, φ a w = e w (a (σ w)) := fun _ _ => rfl
  have hinj : Function.Injective φ := by
    intro a b hab
    refine FiniteAdeleRing.ext _ fun v => ?_
    obtain ⟨w, rfl⟩ := σ.surjective v
    apply (e w).injective
    rw [← hφ, ← hφ, hab]
  have hsurj : Function.Surjective φ := by
    intro b
    let f : ∀ v : HeightOneSpectrum R, v.adicCompletion K :=
      Equiv.piCongrLeft (fun v : HeightOneSpectrum R => v.adicCompletion K) σ
        (fun w => (e w).symm (b w))
    have hf : ∀ w, f (σ w) = (e w).symm (b w) := fun w =>
      Equiv.piCongrLeft_apply_apply _ _ _ _
    refine ⟨⟨f, ?_⟩, FiniteAdeleRing.ext _ fun w => ?_⟩
    · have h1 := σ.symm.injective.tendsto_cofinite.eventually b.2
      refine h1.mono fun v hv => ?_
      obtain ⟨w, rfl⟩ := σ.surjective v
      rw [Equiv.symm_apply_apply] at hv
      change f (σ w) ∈ (σ w).adicCompletionIntegers K
      rw [hf, ← he, AlgEquiv.apply_symm_apply]
      exact hv
    · change e w (f (σ w)) = _
      rw [hf, AlgEquiv.apply_symm_apply]
  refine ⟨AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩, fun a => ?_⟩
  change (∀ w, φ a w ∈ w.adicCompletionIntegers K) ↔
    ∀ v : HeightOneSpectrum R, a v ∈ v.adicCompletionIntegers K
  rw [σ.surjective.forall]
  exact forall_congr' fun w => he w _

/- English proof (translation)
Use `choose e he using exists_local`. Conclude with `exists_adele_equiv_of_local primeCorr e he`.
-/
theorem exists_adele_equiv :
    ∃ e : IndefiniteRowSideFullHecke.IdeleNormTraceForm.Af ≃ₐ[ℚ] IndefiniteRowSideFullHecke.AdelicScalarMultiplier.Af,
      ∀ a, e a ∈ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.zHat ↔ a ∈ IndefiniteRowSideFullHecke.IdeleNormTraceForm.Zhat := by
  choose e he using exists_local
  exact exists_adele_equiv_of_local primeCorr e he

end Adeles

section Transport

variable {A A' : Type} [CommRing A] [Algebra ℚ A] [CommRing A'] [Algebra ℚ A'] (e : A ≃ₐ[ℚ] A')

def tr (V : Type) [AddCommGroup V] [Module ℚ V] : A ⊗[ℚ] V ≃ₗ[ℚ] A' ⊗[ℚ] V :=
  TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl ℚ V)

variable {V V' : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup V'] [Module ℚ V']

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem tr_tmul (a : A) (x : V) : tr e V (a ⊗ₜ x) = e a ⊗ₜ x := rfl

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul b x => simp [smul_tmul']`. Consider the case `add x y hx hy => simp [smul_add, hx, hy]`.
-/
theorem tr_smul (a : A) (x : A ⊗[ℚ] V) : tr e V (a • x) = e a • tr e V x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => simp [smul_tmul']
  | add x y hx hy => simp [smul_add, hx, hy]

/- English proof (translation)
Apply `(tr e V).injective` to reduce the goal to its premises. Simplify using `[tr_smul]`.
-/
theorem tr_symm_smul (a : A') (x : A' ⊗[ℚ] V) :
    (tr e V).symm (a • x) = e.symm a • (tr e V).symm x := by
  apply (tr e V).injective
  simp [tr_smul]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul b x => simp`. Consider the case `add x y hx hy => simp [hx, hy]`.
-/
theorem tr_baseChange (f : V →ₗ[ℚ] V') (x : A ⊗[ℚ] V) :
    f.baseChange A' (tr e V x) = tr e V' (f.baseChange A x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => simp
  | add x y hx hy => simp [hx, hy]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']`. Consider the case `tmul b x`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add y y' hy hy' => simp only [map_add, hy, hy']`. Consider the case `tmul c y => simp`.
-/
theorem tr_bilinMap (h : LinearMap.BilinMap ℚ V V') (x y : A ⊗[ℚ] V) :
    h.baseChange A' (tr e V x) (tr e V y) = tr e V' (h.baseChange A x y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul b x =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul c y => simp

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']`. Consider the case `tmul b x`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add y y' hy hy' => simp only [map_add, hy, hy']`. Consider the case `tmul c y => simp`.
-/
theorem tr_bilinForm (h : LinearMap.BilinForm ℚ V) (x y : A ⊗[ℚ] V) :
    h.baseChange A' (tr e V x) (tr e V y) = e (h.baseChange A x y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul b x =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul c y => simp

def cj (V : Type) [AddCommGroup V] [Module ℚ V] (g : A ⊗[ℚ] V ≃ₗ[A] A ⊗[ℚ] V) :
    A' ⊗[ℚ] V ≃ₗ[A'] A' ⊗[ℚ] V where
  toFun x := tr e V (g ((tr e V).symm x))
  invFun x := tr e V (g.symm ((tr e V).symm x))
  map_add' x y := by simp
  map_smul' a x := by simp [tr_symm_smul, tr_smul]
  left_inv x := by simp
  right_inv x := by simp

/- English proof (translation)
Simplify using `[cj]`.
-/
@[simp] theorem cj_tr (g : A ⊗[ℚ] V ≃ₗ[A] A ⊗[ℚ] V) (x : A ⊗[ℚ] V) :
    cj e V g (tr e V x) = tr e V (g x) := by
  simp [cj]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul b x => simp`. Consider the case `add x y hx hy => simp [hx, hy]`.
-/
theorem tr_tr_symm (x : A' ⊗[ℚ] V) : tr e V (tr e.symm V x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => simp
  | add x y hx hy => simp [hx, hy]

/- English proof (translation)
Introduce `g'`. Use `⟨cj e.symm V g', LinearEquiv.ext fun x => ?_⟩` and prove the remaining obligations. Take `⟨y, rfl⟩` from `(tr e V).surjective x`. Take `⟨z, rfl⟩` from `(tr e.symm V).surjective y`. Rewrite using `[cj_tr, cj_tr, tr_tr_symm, tr_tr_symm]`.
-/
theorem cj_surjective : Function.Surjective (cj e V) := by
  intro g'
  refine ⟨cj e.symm V g', LinearEquiv.ext fun x => ?_⟩
  obtain ⟨y, rfl⟩ := (tr e V).surjective x
  obtain ⟨z, rfl⟩ := (tr e.symm V).surjective y
  rw [cj_tr, cj_tr, tr_tr_symm, tr_tr_symm]

def trAlg (K : Type) [CommRing K] [Algebra ℚ K] : A ⊗[ℚ] K ≃ₐ[ℚ] A' ⊗[ℚ] K :=
  Algebra.TensorProduct.congr e AlgEquiv.refl

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul b x => simp [trAlg]`. Consider the case `add x y hx hy => simp [hx, hy]`.
-/
theorem trAlg_eq (K : Type) [CommRing K] [Algebra ℚ K] (x : A ⊗[ℚ] K) :
    trAlg e K x = tr e K x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => simp [trAlg]
  | add x y hx hy => simp [hx, hy]

/- English proof (translation)
Use `Algebra.norm_eq_of_equiv_equiv e.toRingEquiv (trAlg e K).toRingEquiv (by ext a; simp [trAlg]) x` as an intermediate fact. Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem norm_trAlg (K : Type) [CommRing K] [Algebra ℚ K] (x : A ⊗[ℚ] K) :
    Algebra.norm A' (trAlg e K x) = e (Algebra.norm A x) := by
  have := Algebra.norm_eq_of_equiv_equiv e.toRingEquiv (trAlg e K).toRingEquiv
    (by ext a; simp [trAlg]) x
  rw [this]
  simp

end Transport

section Adelic

variable (e : IndefiniteRowSideFullHecke.IdeleNormTraceForm.Af ≃ₐ[ℚ] IndefiniteRowSideFullHecke.AdelicScalarMultiplier.Af)
  (he : ∀ a, e a ∈ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.zHat ↔ a ∈ IndefiniteRowSideFullHecke.IdeleNormTraceForm.Zhat)

/- English proof (translation)
Proceed by induction on `ht using AddSubgroup.closure_induction with`. Consider the case `mem t ht`. Take `⟨z', hz', x, hx, rfl⟩` from `ht`. Conclude with `AddSubgroup.subset_closure ⟨z * z', mul_mem hz hz', x, hx, by simp [smul_tmul']⟩`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [smul_neg]`. Conclude with `neg_mem hx`.
-/
theorem hat_smul_mem {V : Type} [AddCommGroup V] [Module ℚ V] (L : Set V)
    {z : IndefiniteRowSideFullHecke.AdelicScalarMultiplier.Af} (hz : z ∈ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.zHat) {t : IndefiniteRowSideFullHecke.AdelicScalarMultiplier.Af ⊗[ℚ] V}
    (ht : t ∈ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.hat L) : z • t ∈ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.hat L := by
  induction ht using AddSubgroup.closure_induction with
  | mem t ht =>
    obtain ⟨z', hz', x, hx, rfl⟩ := ht
    exact AddSubgroup.subset_closure ⟨z * z', mul_mem hz hz', x, hx, by simp [smul_tmul']⟩
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

include he in

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. It suffices to establish `H : ∀ t ∈ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.hat L, (tr e V).symm t ∈ IndefiniteRowSideFullHecke.IdeleNormTraceForm.hat L by`. Simplify using `using H _ hx`. Introduce `t ht`.

Proceed by induction on `ht using AddSubgroup.closure_induction with`. Consider the case `mem t ht`. Take `⟨z, hz, x, hx, rfl⟩` from `ht`. Take `⟨z, rfl⟩` from `e.surjective z`. Rewrite using `[← tr_tmul, LinearEquiv.symm_apply_apply]`.

Establish `h1 : (1 : IndefiniteRowSideFullHecke.IdeleNormTraceForm.Af) ⊗ₜ[ℚ] x ∈ IndefiniteRowSideFullHecke.IdeleNormTraceForm.hat L` using `Submodule.subset_span ⟨x, hx, rfl⟩`. Establish `h2` using `(IndefiniteRowSideFullHecke.IdeleNormTraceForm.hat L).smul_mem (⟨z, (he z).1 hz⟩ : IndefiniteRowSideFullHecke.IdeleNormTraceForm.Zhat) h1`. Establish `h3 : (⟨z, (he z).1 hz⟩ : IndefiniteRowSideFullHecke.IdeleNormTraceForm.Zhat) • ((1 : IndefiniteRowSideFullHecke.IdeleNormTraceForm.Af) ⊗ₜ[ℚ] x) = z ⊗ₜ[ℚ] x`. Express the relevant statement in the definitionally equal form `z • ((1 : IndefiniteRowSideFullHecke.IdeleNormTraceForm.Af) ⊗ₜ[ℚ] x) = _`. Simplify using `[smul_tmul']`.

Rewrite `h2` using `[h3]`. Then use the resulting hypothesis. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [map_neg]`.

Conclude with `neg_mem hx`. Introduce `hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem t ht`. Take `⟨x, hx, rfl⟩` from `ht`.

Conclude with `AddSubgroup.subset_closure ⟨1, one_mem _, x, hx, by simp⟩`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul z x _ hx`.

Express the relevant statement in the definitionally equal form `tr e V ((z : IndefiniteRowSideFullHecke.IdeleNormTraceForm.Af) • x) ∈ _`. Rewrite using `[tr_smul]`. Conclude with `hat_smul_mem L ((he _).2 z.2) hx`.
-/
theorem hat_iff {V : Type} [AddCommGroup V] [Module ℚ V] (L : Set V)
    (x : IndefiniteRowSideFullHecke.IdeleNormTraceForm.Adelic V) : tr e V x ∈ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.hat L ↔ x ∈ IndefiniteRowSideFullHecke.IdeleNormTraceForm.hat L := by
  constructor
  · intro hx
    suffices H : ∀ t ∈ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.hat L, (tr e V).symm t ∈ IndefiniteRowSideFullHecke.IdeleNormTraceForm.hat L by
      simpa using H _ hx
    intro t ht
    induction ht using AddSubgroup.closure_induction with
    | mem t ht =>
      obtain ⟨z, hz, x, hx, rfl⟩ := ht
      obtain ⟨z, rfl⟩ := e.surjective z
      rw [← tr_tmul, LinearEquiv.symm_apply_apply]
      have h1 : (1 : IndefiniteRowSideFullHecke.IdeleNormTraceForm.Af) ⊗ₜ[ℚ] x ∈ IndefiniteRowSideFullHecke.IdeleNormTraceForm.hat L :=
        Submodule.subset_span ⟨x, hx, rfl⟩
      have h2 := (IndefiniteRowSideFullHecke.IdeleNormTraceForm.hat L).smul_mem (⟨z, (he z).1 hz⟩ : IndefiniteRowSideFullHecke.IdeleNormTraceForm.Zhat) h1
      have h3 : (⟨z, (he z).1 hz⟩ : IndefiniteRowSideFullHecke.IdeleNormTraceForm.Zhat) • ((1 : IndefiniteRowSideFullHecke.IdeleNormTraceForm.Af) ⊗ₜ[ℚ] x) =
          z ⊗ₜ[ℚ] x := by
        change z • ((1 : IndefiniteRowSideFullHecke.IdeleNormTraceForm.Af) ⊗ₜ[ℚ] x) = _
        simp [smul_tmul']
      rwa [h3] at h2
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
  · intro hx
    induction hx using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨x, hx, rfl⟩ := ht
      exact AddSubgroup.subset_closure ⟨1, one_mem _, x, hx, by simp⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul z x _ hx =>
      change tr e V ((z : IndefiniteRowSideFullHecke.IdeleNormTraceForm.Af) • x) ∈ _
      rw [tr_smul]
      exact hat_smul_mem L ((he _).2 z.2) hx

def ue : IndefiniteRowSideFullHecke.IdeleNormTraceForm.Afˣ ≃* IndefiniteRowSideFullHecke.AdelicScalarMultiplier.Afˣ := Units.mapEquiv e.toMulEquiv

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ue_val (ν : IndefiniteRowSideFullHecke.IdeleNormTraceForm.Afˣ) : (ue e ν : IndefiniteRowSideFullHecke.AdelicScalarMultiplier.Af) = e ν := rfl

include he in
/- English proof (translation)
Unfold `IndefiniteRowSideFullHecke.AdelicScalarMultiplier.zHatUnits IndefiniteRowSideFullHecke.IdeleNormTraceForm.ZhatUnits`. Rewrite using `[Submonoid.mem_units_iff, Submonoid.mem_units_iff, ← map_inv]`. Conclude with `and_congr (he _) (he _)`.
-/
theorem units_iff (ν : IndefiniteRowSideFullHecke.IdeleNormTraceForm.Afˣ) :
    ue e ν ∈ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.zHatUnits ↔ ν ∈ IndefiniteRowSideFullHecke.IdeleNormTraceForm.ZhatUnits := by
  unfold IndefiniteRowSideFullHecke.AdelicScalarMultiplier.zHatUnits IndefiniteRowSideFullHecke.IdeleNormTraceForm.ZhatUnits
  rw [Submonoid.mem_units_iff, Submonoid.mem_units_iff, ← map_inv]
  exact and_congr (he _) (he _)

section Ideles

variable {K : Type} [Field K] [NumberField K]

def uK (K : Type) [Field K] [NumberField K] :
    (IndefiniteRowSideFullHecke.IdeleNormTraceForm.Adelic K)ˣ ≃* IndefiniteRowSideFullHecke.AdelicScalarMultiplier.Idele K := Units.mapEquiv (trAlg e K).toMulEquiv

/- English proof (translation)
The claim follows from `trAlg_eq e K _`.
-/
theorem uK_val (s : (IndefiniteRowSideFullHecke.IdeleNormTraceForm.Adelic K)ˣ) :
    (uK e K s : IndefiniteRowSideFullHecke.AdelicScalarMultiplier.Af ⊗[ℚ] K) = tr e K s := trAlg_eq e K _

/- English proof (translation)
The claim follows from `Units.ext (norm_trAlg e K _)`.
-/
theorem ideleNorm_uK (s : (IndefiniteRowSideFullHecke.IdeleNormTraceForm.Adelic K)ˣ) :
    IndefiniteRowSideFullHecke.AdelicScalarMultiplier.ideleNorm K (uK e K s) = ue e (IndefiniteRowSideFullHecke.IdeleNormTraceForm.ideleNorm K s) :=
  Units.ext (norm_trAlg e K _)

include he in
/- English proof (translation)
Establish `hO : Set.range (algebraMap (𝓞 K) K) = {x : K | IsIntegral ℤ x}`. Use extensionality with `x`. Conclude with `⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩`. Unfold `IndefiniteRowSideFullHecke.AdelicScalarMultiplier.IsUnitIdele IndefiniteRowSideFullHecke.IdeleNormTraceForm.IsUnitIdele`. Rewrite using `[hO, ← map_inv, uK_val, uK_val, hat_iff e he, hat_iff e he]`.
-/
theorem isUnitIdele_iff (s : (IndefiniteRowSideFullHecke.IdeleNormTraceForm.Adelic K)ˣ) :
    IndefiniteRowSideFullHecke.AdelicScalarMultiplier.IsUnitIdele (uK e K s) ↔ IndefiniteRowSideFullHecke.IdeleNormTraceForm.IsUnitIdele s := by
  have hO : Set.range (algebraMap (𝓞 K) K) = {x : K | IsIntegral ℤ x} := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  unfold IndefiniteRowSideFullHecke.AdelicScalarMultiplier.IsUnitIdele IndefiniteRowSideFullHecke.IdeleNormTraceForm.IsUnitIdele
  rw [hO, ← map_inv, uK_val, uK_val, hat_iff e he, hat_iff e he]

include he in
/- English proof (translation)
Unfold `IndefiniteRowSideFullHecke.AdelicScalarMultiplier.NormUnitCond IndefiniteRowSideFullHecke.IdeleNormTraceForm.IsNormScale`. Use `and_congr_right fun _ => ?_` and prove the remaining obligations. Establish `hv : ((ue e ((IndefiniteRowSideFullHecke.IdeleNormTraceForm.ideleNorm K s)⁻¹ * IndefiniteRowSideFullHecke.IdeleNormTraceForm.ratIdele q) : IndefiniteRowSideFullHecke.AdelicScalarMultiplier.Afˣ) : IndefiniteRowSideFullHecke.AdelicScalarMultiplier.Af) = (((IndefiniteRowSideFullHeck …`. Rewrite using `[ideleNorm_uK, map_mul, Units.val_mul, map_inv, ue_val]`. Use `congr 1`.

Conclude with `e.commutes _`. Rewrite using `[← units_iff e he, ← hv]`. Conclude with `⟨fun ⟨u, hu, h⟩ => Units.ext h ▸ hu, fun h => ⟨_, h, rfl⟩⟩`.
-/
theorem normScale_iff (s : (IndefiniteRowSideFullHecke.IdeleNormTraceForm.Adelic K)ˣ) (q : ℚˣ) :
    (0 < (q : ℚ) ∧ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.NormUnitCond (uK e K s) q) ↔ IndefiniteRowSideFullHecke.IdeleNormTraceForm.IsNormScale s q := by
  unfold IndefiniteRowSideFullHecke.AdelicScalarMultiplier.NormUnitCond IndefiniteRowSideFullHecke.IdeleNormTraceForm.IsNormScale
  refine and_congr_right fun _ => ?_
  have hv : ((ue e ((IndefiniteRowSideFullHecke.IdeleNormTraceForm.ideleNorm K s)⁻¹ * IndefiniteRowSideFullHecke.IdeleNormTraceForm.ratIdele q) : IndefiniteRowSideFullHecke.AdelicScalarMultiplier.Afˣ) :
      IndefiniteRowSideFullHecke.AdelicScalarMultiplier.Af) = (((IndefiniteRowSideFullHecke.AdelicScalarMultiplier.ideleNorm K (uK e K s))⁻¹ : IndefiniteRowSideFullHecke.AdelicScalarMultiplier.Afˣ) :
        IndefiniteRowSideFullHecke.AdelicScalarMultiplier.Af) * algebraMap ℚ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.Af q := by
    rw [ideleNorm_uK, map_mul, Units.val_mul, map_inv, ue_val]
    congr 1
    exact e.commutes _
  rw [← units_iff e he, ← hv]
  exact ⟨fun ⟨u, hu, h⟩ => Units.ext h ▸ hu, fun h => ⟨_, h, rfl⟩⟩

include he in

/- English proof (translation)
Rewrite using `[(uK e K).surjective.forall]`. Use `forall_congr' fun s => and_congr ?_ ?_` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨q, hq, hu⟩`. Use `⟨q, (normScale_iff e he s q).2 hq, fun r hr => ?_⟩` and prove the remaining obligations.

Conclude with `congrArg Units.val (hu (Units.mk0 r hr.1.ne') ((normScale_iff e he s _).1 hr))`. Introduce and unpack `⟨q, hq, hu⟩`. Use `⟨Units.mk0 q hq.1.ne', (normScale_iff e he s _).1 hq, fun r hr => ?_⟩` and prove the remaining obligations. Conclude with `Units.ext (hu r ((normScale_iff e he s r).2 hr))`. Rewrite using `[isUnitIdele_iff e he]`.

Prove the components needed by the constructor for the conclusion. Introduce `H q hq hc`. Take `⟨h1, h2⟩` from `H (Units.mk0 q hq.ne') ((normScale_iff e he s _).1 ⟨hq, hc⟩)`. Conclude with `⟨by simpa using h1, fun hs => congrArg Units.val (h2 hs)⟩`. Introduce `H q hq`.

Take `⟨h0, hc⟩` from `(normScale_iff e he s q).2 hq`. Take `⟨h1, h2⟩` from `H q h0 hc`. Conclude with `⟨by simpa using h1, fun hs => Units.ext (h2 hs)⟩`.
-/
theorem ideleClauses_iff :
    IndefiniteRowSideFullHecke.IdeleNormTraceForm.IdeleNormScaleAt K ↔ ∀ s : IndefiniteRowSideFullHecke.AdelicScalarMultiplier.Idele K,
      (∃! q : ℚ, 0 < q ∧ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.NormUnitCond s q) ∧
      ∀ q : ℚ, 0 < q → IndefiniteRowSideFullHecke.AdelicScalarMultiplier.NormUnitCond s q →
        (∃ x : Kˣ, Algebra.norm ℚ (x : K) = q⁻¹) ∧ (IndefiniteRowSideFullHecke.AdelicScalarMultiplier.IsUnitIdele s → q = 1) := by
  rw [(uK e K).surjective.forall]
  refine forall_congr' fun s => and_congr ?_ ?_
  · constructor
    · rintro ⟨q, hq, hu⟩
      refine ⟨q, (normScale_iff e he s q).2 hq, fun r hr => ?_⟩
      exact congrArg Units.val (hu (Units.mk0 r hr.1.ne') ((normScale_iff e he s _).1 hr))
    · rintro ⟨q, hq, hu⟩
      refine ⟨Units.mk0 q hq.1.ne', (normScale_iff e he s _).1 hq, fun r hr => ?_⟩
      exact Units.ext (hu r ((normScale_iff e he s r).2 hr))
  · rw [isUnitIdele_iff e he]
    constructor
    · intro H q hq hc
      obtain ⟨h1, h2⟩ := H (Units.mk0 q hq.ne') ((normScale_iff e he s _).1 ⟨hq, hc⟩)
      exact ⟨by simpa using h1, fun hs => congrArg Units.val (h2 hs)⟩
    · intro H q hq
      obtain ⟨h0, hc⟩ := (normScale_iff e he s q).2 hq
      obtain ⟨h1, h2⟩ := H q h0 hc
      exact ⟨by simpa using h1, fun hs => Units.ext (h2 hs)⟩

end Ideles

section Groups

variable {E : Type} [Field E] [NumberField E]
  {W : Type} [AddCommGroup W] [Module ℚ W] [Module E W] [IsScalarTower ℚ E W]

/- English proof (translation)
Use `forall_congr' fun a => ?_` and prove the remaining obligations. Rewrite using `[(tr e W).surjective.forall]`. Use `forall_congr' fun x => ?_` and prove the remaining obligations. Unfold `IndefiniteRowSideFullHecke.AdelicScalarMultiplier.adelicScalar IndefiniteRowSideFullHecke.IdeleNormTraceForm.adelicSmul`. Rewrite using `[tr_baseChange, cj_tr, cj_tr, tr_baseChange]`.

Conclude with `(tr e W).injective.eq_iff`.
-/
theorem linear_iff (g : IndefiniteRowSideFullHecke.IdeleNormTraceForm.Adelic W ≃ₗ[IndefiniteRowSideFullHecke.IdeleNormTraceForm.Af] IndefiniteRowSideFullHecke.IdeleNormTraceForm.Adelic W) :
    cj e W g ∈ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.adelicGL E W ↔ g ∈ IndefiniteRowSideFullHecke.IdeleNormTraceForm.linearAd E W := by
  refine forall_congr' fun a => ?_
  rw [(tr e W).surjective.forall]
  refine forall_congr' fun x => ?_
  unfold IndefiniteRowSideFullHecke.AdelicScalarMultiplier.adelicScalar IndefiniteRowSideFullHecke.IdeleNormTraceForm.adelicSmul
  rw [tr_baseChange, cj_tr, cj_tr, tr_baseChange]
  exact (tr e W).injective.eq_iff

omit [Module E W] [IsScalarTower ℚ E W] in
/- English proof (translation)
Unfold `IndefiniteRowSideFullHecke.AdelicScalarMultiplier.HasMultiplier IndefiniteRowSideFullHecke.IdeleNormTraceForm.HasMultiplier`. Rewrite using `[(tr e W).surjective.forall₂]`. Use `forall₂_congr fun x y => ?_` and prove the remaining obligations. Rewrite using `[cj_tr, cj_tr, tr_bilinForm, tr_bilinForm, ue_val, ← map_mul]`. Conclude with `e.injective.eq_iff`.
-/
theorem multiplier_iff (ψ : LinearMap.BilinForm ℚ W)
    (g : IndefiniteRowSideFullHecke.IdeleNormTraceForm.Adelic W ≃ₗ[IndefiniteRowSideFullHecke.IdeleNormTraceForm.Af] IndefiniteRowSideFullHecke.IdeleNormTraceForm.Adelic W) (ν : IndefiniteRowSideFullHecke.IdeleNormTraceForm.Afˣ) :
    IndefiniteRowSideFullHecke.AdelicScalarMultiplier.HasMultiplier ψ (cj e W g) (ue e ν) ↔ IndefiniteRowSideFullHecke.IdeleNormTraceForm.HasMultiplier ψ g ν := by
  unfold IndefiniteRowSideFullHecke.AdelicScalarMultiplier.HasMultiplier IndefiniteRowSideFullHecke.IdeleNormTraceForm.HasMultiplier
  rw [(tr e W).surjective.forall₂]
  refine forall₂_congr fun x y => ?_
  rw [cj_tr, cj_tr, tr_bilinForm, tr_bilinForm, ue_val, ← map_mul]
  exact e.injective.eq_iff

/- English proof (translation)
Use `and_congr (linear_iff e g) ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(∀ x y, LinearMap.BilinMap.baseChange _ h (cj e W g x) (cj e W g y) = LinearMap.BilinMap.baseChange _ h x y) ↔ ∀ x y, LinearMap.BilinMap.baseChange _ h (g x) (g y) = LinearMap.BilinMap.baseChange _ h x y`. Rewrite using `[(tr e W).surjective.forall₂]`. Use `forall₂_congr fun x y => ?_` and prove the remaining obligations. Rewrite using `[cj_tr, cj_tr, tr_bilinMap, tr_bilinMap]`.

Conclude with `(tr e E).injective.eq_iff`.
-/
theorem unitary_iff (h : W →ₗ[ℚ] W →ₗ[ℚ] E)
    (g : IndefiniteRowSideFullHecke.IdeleNormTraceForm.Adelic W ≃ₗ[IndefiniteRowSideFullHecke.IdeleNormTraceForm.Af] IndefiniteRowSideFullHecke.IdeleNormTraceForm.Adelic W) :
    cj e W g ∈ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.unitaryGroup h ↔ g ∈ IndefiniteRowSideFullHecke.IdeleNormTraceForm.unitaryAd E h := by
  refine and_congr (linear_iff e g) ?_
  change (∀ x y, LinearMap.BilinMap.baseChange _ h (cj e W g x) (cj e W g y) =
    LinearMap.BilinMap.baseChange _ h x y) ↔ ∀ x y, LinearMap.BilinMap.baseChange _ h (g x) (g y) =
    LinearMap.BilinMap.baseChange _ h x y
  rw [(tr e W).surjective.forall₂]
  refine forall₂_congr fun x y => ?_
  rw [cj_tr, cj_tr, tr_bilinMap, tr_bilinMap]
  exact (tr e E).injective.eq_iff

/- English proof (translation)
Use `and_congr (linear_iff e g) ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(∃ ν, IndefiniteRowSideFullHecke.AdelicScalarMultiplier.HasMultiplier _ (cj e W g) ν) ↔ ∃ ν, IndefiniteRowSideFullHecke.IdeleNormTraceForm.HasMultiplier _ g ν`. Rewrite using `[(ue e).surjective.exists]`. Conclude with `exists_congr fun ν => multiplier_iff e _ g ν`.
-/
theorem similitude_iff (h : W →ₗ[ℚ] W →ₗ[ℚ] E) (ξ : E)
    (g : IndefiniteRowSideFullHecke.IdeleNormTraceForm.Adelic W ≃ₗ[IndefiniteRowSideFullHecke.IdeleNormTraceForm.Af] IndefiniteRowSideFullHecke.IdeleNormTraceForm.Adelic W) :
    cj e W g ∈ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.simGroup h ξ ↔
      g ∈ IndefiniteRowSideFullHecke.IdeleNormTraceForm.similitudeAd E (IndefiniteRowSideFullHecke.IdeleNormTraceForm.traceForm E ξ h) := by
  refine and_congr (linear_iff e g) ?_
  change (∃ ν, IndefiniteRowSideFullHecke.AdelicScalarMultiplier.HasMultiplier _ (cj e W g) ν) ↔ ∃ ν, IndefiniteRowSideFullHecke.IdeleNormTraceForm.HasMultiplier _ g ν
  rw [(ue e).surjective.exists]
  exact exists_congr fun ν => multiplier_iff e _ g ν

include he

omit [Module E W] [IsScalarTower ℚ E W] in
/- English proof (translation)
Express the relevant statement in the definitionally equal form `(∀ x, cj e W g x ∈ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.hat L ↔ x ∈ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.hat L) ↔ ∀ x, g x ∈ IndefiniteRowSideFullHecke.IdeleNormTraceForm.hat L ↔ x ∈ IndefiniteRowSideFullHecke.IdeleNormTraceForm.hat L`. Rewrite using `[(tr e W).surjective.forall]`. Use `forall_congr' fun x => ?_` and prove the remaining obligations. Rewrite using `[cj_tr, hat_iff e he, hat_iff e he]`.
-/
theorem stab_iff (L : Set W) (g : IndefiniteRowSideFullHecke.IdeleNormTraceForm.Adelic W ≃ₗ[IndefiniteRowSideFullHecke.IdeleNormTraceForm.Af] IndefiniteRowSideFullHecke.IdeleNormTraceForm.Adelic W) :
    cj e W g ∈ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.stab (IndefiniteRowSideFullHecke.AdelicScalarMultiplier.hat L) ↔ g ∈ IndefiniteRowSideFullHecke.IdeleNormTraceForm.stabAd L := by
  change (∀ x, cj e W g x ∈ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.hat L ↔ x ∈ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.hat L) ↔
    ∀ x, g x ∈ IndefiniteRowSideFullHecke.IdeleNormTraceForm.hat L ↔ x ∈ IndefiniteRowSideFullHecke.IdeleNormTraceForm.hat L
  rw [(tr e W).surjective.forall]
  refine forall_congr' fun x => ?_
  rw [cj_tr, hat_iff e he, hat_iff e he]

omit [Module E W] [IsScalarTower ℚ E W] in
/- English proof (translation)
Use `and_congr (stab_iff e he L g) ?_` and prove the remaining obligations. Rewrite using `[(tr e W).surjective.forall]`. Use `forall_congr' fun x => ?_` and prove the remaining obligations. Rewrite using `[cj_tr, ← map_sub, hat_iff e he, hat_iff e he]`.
-/
theorem congr_iff (L L' : Set W)
    (g : IndefiniteRowSideFullHecke.IdeleNormTraceForm.Adelic W ≃ₗ[IndefiniteRowSideFullHecke.IdeleNormTraceForm.Af] IndefiniteRowSideFullHecke.IdeleNormTraceForm.Adelic W) :
    cj e W g ∈ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.congr (IndefiniteRowSideFullHecke.AdelicScalarMultiplier.hat L) (IndefiniteRowSideFullHecke.AdelicScalarMultiplier.hat L') ↔
      g ∈ IndefiniteRowSideFullHecke.IdeleNormTraceForm.congrAd L L' := by
  refine and_congr (stab_iff e he L g) ?_
  rw [(tr e W).surjective.forall]
  refine forall_congr' fun x => ?_
  rw [cj_tr, ← map_sub, hat_iff e he, hat_iff e he]

variable [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]

/- English proof (translation)
The claim follows from `and_congr (similitude_iff e h ξ g) (congr_iff e he _ _ g)`.
-/
theorem simLevel_iff (h : W →ₗ[ℚ] W →ₗ[ℚ] E) (ξ : E) (Λ : Submodule (𝓞 E) W) (I : Ideal (𝓞 E))
    (g : IndefiniteRowSideFullHecke.IdeleNormTraceForm.Adelic W ≃ₗ[IndefiniteRowSideFullHecke.IdeleNormTraceForm.Af] IndefiniteRowSideFullHecke.IdeleNormTraceForm.Adelic W) :
    cj e W g ∈ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.simLevel h ξ Λ I ↔
      g ∈ IndefiniteRowSideFullHecke.IdeleNormTraceForm.simLevel E (IndefiniteRowSideFullHecke.IdeleNormTraceForm.traceForm E ξ h) Λ I :=
  and_congr (similitude_iff e h ξ g) (congr_iff e he _ _ g)

/- English proof (translation)
Use `forall₂_congr fun x y => imp_congr_right fun _ => ?_` and prove the remaining obligations. Rewrite using `[← hat_iff e he, map_sub, ← cj_tr, tr_tmul, tr_tmul, map_one]`.
-/
theorem induces_iff (Λ : Submodule (𝓞 E) W) (I : Ideal (𝓞 E))
    (g : IndefiniteRowSideFullHecke.IdeleNormTraceForm.Adelic W ≃ₗ[IndefiniteRowSideFullHecke.IdeleNormTraceForm.Af] IndefiniteRowSideFullHecke.IdeleNormTraceForm.Adelic W)
    (φ : (Λ ⧸ (I • ⊤ : Submodule (𝓞 E) Λ)) ≃ₗ[𝓞 E] (Λ ⧸ (I • ⊤ : Submodule (𝓞 E) Λ))) :
    IndefiniteRowSideFullHecke.AdelicScalarMultiplier.Induces Λ I (cj e W g) φ ↔ IndefiniteRowSideFullHecke.IdeleNormTraceForm.Induces E Λ I g φ := by
  refine forall₂_congr fun x y => imp_congr_right fun _ => ?_
  rw [← hat_iff e he, map_sub, ← cj_tr, tr_tmul, tr_tmul, map_one]

/- English proof (translation)
Use `and_congr ?_ (and_congr ?_ (and_congr ?_ (forall_congr' fun φ => ?_)))` and prove the remaining obligations. Rewrite using `[Set.ext_iff, (ue e).surjective.forall]`. Use `forall_congr' fun ν => iff_congr ?_ (units_iff e he ν).symm` and prove the remaining obligations. Rewrite using `[(cj_surjective e).exists]`. Conclude with `exists_congr fun g => (and_congr (simLevel_iff e he h ξ Λ I g) (multiplier_iff e _ g ν)).symm`.

Rewrite using `[SetLike.ext_iff, SetLike.ext_iff, (cj_surjective e).forall]`. Conclude with `forall_congr' fun g => (iff_congr (and_congr (simLevel_iff e he h ξ Λ I g) (unitary_iff e h g)) (and_congr (simLevel_iff e he h ξ Λ _ g) (unitary_iff e h g))).symm`. Rewrite using `[SetLike.le_def, SetLike.le_def, (cj_surjective e).forall]`. Conclude with `forall_congr' fun g => (imp_congr (simLevel_iff e he h ξ Λ _ g) (simLevel_iff e he h ξ Λ I g)).symm`. Rewrite using `[(cj_surjective e).exists]`.

Conclude with `exists_congr fun g => (and_congr (and_congr (unitary_iff e h g) (stab_iff e he _ g)) (induces_iff e he Λ I g φ)).symm`.
-/
theorem levelClauses_iff (h : W →ₗ[ℚ] W →ₗ[ℚ] E) (ξ : E) (Λ : Submodule (𝓞 E) W) (M : ℕ)
    (I : Ideal (𝓞 E)) :
    IndefiniteRowSideFullHecke.IdeleNormTraceForm.LevelClauses E ξ h Λ M I ↔
      ((∀ ν : IndefiniteRowSideFullHecke.AdelicScalarMultiplier.Afˣ, (∃ g ∈ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.simLevel h ξ Λ I,
        IndefiniteRowSideFullHecke.AdelicScalarMultiplier.HasMultiplier (IndefiniteRowSideFullHecke.AdelicScalarMultiplier.traceForm h ξ) g ν) ↔ ν ∈ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.zHatUnits) ∧
      IndefiniteRowSideFullHecke.AdelicScalarMultiplier.simLevel h ξ Λ I ⊓ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.unitaryGroup h =
        IndefiniteRowSideFullHecke.AdelicScalarMultiplier.unitaryPrincipal h ξ Λ M ∧
      IndefiniteRowSideFullHecke.AdelicScalarMultiplier.simPrincipal h ξ Λ M ≤ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.simLevel h ξ Λ I ∧
      ∀ φ, ∃ g ∈ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.unitaryStab h Λ, IndefiniteRowSideFullHecke.AdelicScalarMultiplier.Induces Λ I g φ) := by
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ (forall_congr' fun φ => ?_)))
  · rw [Set.ext_iff, (ue e).surjective.forall]
    refine forall_congr' fun ν => iff_congr ?_ (units_iff e he ν).symm
    rw [(cj_surjective e).exists]
    exact exists_congr fun g =>
      (and_congr (simLevel_iff e he h ξ Λ I g) (multiplier_iff e _ g ν)).symm
  · rw [SetLike.ext_iff, SetLike.ext_iff, (cj_surjective e).forall]
    exact forall_congr' fun g => (iff_congr
      (and_congr (simLevel_iff e he h ξ Λ I g) (unitary_iff e h g))
      (and_congr (simLevel_iff e he h ξ Λ _ g) (unitary_iff e h g))).symm
  · rw [SetLike.le_def, SetLike.le_def, (cj_surjective e).forall]
    exact forall_congr' fun g =>
      (imp_congr (simLevel_iff e he h ξ Λ _ g) (simLevel_iff e he h ξ Λ I g)).symm
  · rw [(cj_surjective e).exists]
    exact exists_congr fun g => (and_congr
      (and_congr (unitary_iff e h g) (stab_iff e he _ g)) (induces_iff e he Λ I g φ)).symm

end Groups

end Adelic

section Hypotheses

/- English proof (translation)
Unfold `IndefiniteRowSideFullHecke.IdeleNormTraceForm.IsPrimeImagQuad IndefiniteRowSideFullHecke.AdelicScalarMultiplier.IsQuadField`. The claim follows by propositional logic.
-/
theorem quad_iff (d : ℕ) (K : Type) [Field K] [NumberField K] (δ : K) :
    IndefiniteRowSideFullHecke.IdeleNormTraceForm.IsPrimeImagQuad d K δ ↔ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.IsQuadField K d δ := by
  unfold IndefiniteRowSideFullHecke.IdeleNormTraceForm.IsPrimeImagQuad IndefiniteRowSideFullHecke.AdelicScalarMultiplier.IsQuadField
  tauto

/- English proof (translation)
Apply `sq_eq_sq_iff_eq_or_eq_neg.1` to reduce the goal to its premises. Rewrite using `[hz, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]`. Simplify using the standard rewrite rules.
-/
theorem sq_cases {d : ℕ} {z : ℂ} (hz : z ^ 2 = -(d : ℂ)) :
    z = Complex.I * (Real.sqrt d : ℂ) ∨ z = -(Complex.I * (Real.sqrt d : ℂ)) := by
  apply sq_eq_sq_iff_eq_or_eq_neg.1
  rw [hz, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  simp

variable {K : Type} [Field K] [NumberField K] {d : ℕ} {δ : K}

/- English proof (translation)
Take `⟨h1, h2, h3, h4, h5⟩` from `hK`. Conclude with `⟨h1, h2, h3, h4, by rw [neg_sq, h5]⟩`.
-/
theorem quad_neg (hK : IndefiniteRowSideFullHecke.AdelicScalarMultiplier.IsQuadField K d δ) : IndefiniteRowSideFullHecke.AdelicScalarMultiplier.IsQuadField K d (-δ) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hK
  exact ⟨h1, h2, h3, h4, by rw [neg_sq, h5]⟩

/- English proof (translation)
Take `⟨-, h2, -, h4, h5⟩` from `hK`. Establish `hli : LinearIndependent ℚ ![(1 : K), δ]`. Rewrite using `[LinearIndependent.pair_iff' one_ne_zero]`. Introduce `a ha`. Establish `h6 : ((a ^ 2 : ℚ) : K) = ((-d : ℚ) : K)`.

Rewrite `h5` using `[← ha]`. Simplify `h5` using `[Rat.smul_def]`. Establish `h7 : a ^ 2 = -(d : ℚ)` using `Rat.cast_injective h6`. Establish `h8 : (0 : ℚ) < d` using `by exact_mod_cast (by omega : 0 < d)`. Use polynomial arithmetic with `[sq_nonneg a]`.

Establish `hsp` using `hli.span_eq_top_of_card_eq_finrank (by simp [h4])`. Establish `hx : x ∈ Submodule.span ℚ (Set.range ![(1 : K), δ])` using `hsp ▸ Submodule.mem_top`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun ℚ).1 hx`. Conclude with `⟨c 0, c 1, by rw [← hc]; simp [Fin.sum_univ_two, Rat.smul_def]⟩`.
-/
theorem exists_coords (hK : IndefiniteRowSideFullHecke.AdelicScalarMultiplier.IsQuadField K d δ) (x : K) :
    ∃ a b : ℚ, x = a + b * δ := by
  obtain ⟨-, h2, -, h4, h5⟩ := hK
  have hli : LinearIndependent ℚ ![(1 : K), δ] := by
    rw [LinearIndependent.pair_iff' one_ne_zero]
    intro a ha
    have h6 : ((a ^ 2 : ℚ) : K) = ((-d : ℚ) : K) := by
      rw [← ha] at h5
      simpa [Rat.smul_def] using h5
    have h7 : a ^ 2 = -(d : ℚ) := Rat.cast_injective h6
    have h8 : (0 : ℚ) < d := by exact_mod_cast (by omega : 0 < d)
    nlinarith [sq_nonneg a]
  have hsp := hli.span_eq_top_of_card_eq_finrank (by simp [h4])
  have hx : x ∈ Submodule.span ℚ (Set.range ![(1 : K), δ]) := hsp ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).1 hx
  exact ⟨c 0, c 1, by rw [← hc]; simp [Fin.sum_univ_two, Rat.smul_def]⟩

/- English proof (translation)
Use extensionality with `x`. Take `⟨a, b, rfl⟩` from `exists_coords hK x`. Simplify using `[h]`.
-/
theorem ringHom_ext (hK : IndefiniteRowSideFullHecke.AdelicScalarMultiplier.IsQuadField K d δ) {L : Type} [Field L] [CharZero L]
    {f g : K →+* L} (h : f δ = g δ) : f = g := by
  ext x
  obtain ⟨a, b, rfl⟩ := exists_coords hK x
  simp [h]

/- English proof (translation)
Use `haveI : Algebra.IsQuadraticExtension ℚ K := { finrank_eq_two' := hK.2.2.2.1 }`. Establish `hc : Nat.card (K ≃ₐ[ℚ] K) = 2` using `by rw [IsGalois.card_aut_eq_finrank, hK.2.2.2.1]`. Use `haveI : Nontrivial (K ≃ₐ[ℚ] K) := Finite.one_lt_card_iff_nontrivial.1 (by omega)`. Take `⟨c, hc⟩` from `exists_ne (1 : K ≃ₐ[ℚ] K)`. Establish `h1 : c δ ^ 2 = δ ^ 2` using `by rw [← map_pow, hK.2.2.2.2]; simp`.

Use `⟨c, (sq_eq_sq_iff_eq_or_eq_neg.1 h1).resolve_left fun h => hc ?_⟩` and prove the remaining obligations. Use `ringHom_ext hK (f := (c : K →+* K)) (g := RingHom.id K) h` as an intermediate fact. Conclude with `AlgEquiv.ext fun x => RingHom.congr_fun this x`.
-/
theorem exists_conj (hK : IndefiniteRowSideFullHecke.AdelicScalarMultiplier.IsQuadField K d δ) : ∃ c : K ≃ₐ[ℚ] K, c δ = -δ := by
  haveI : Algebra.IsQuadraticExtension ℚ K := { finrank_eq_two' := hK.2.2.2.1 }
  have hc : Nat.card (K ≃ₐ[ℚ] K) = 2 := by rw [IsGalois.card_aut_eq_finrank, hK.2.2.2.1]
  haveI : Nontrivial (K ≃ₐ[ℚ] K) := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨c, hc⟩ := exists_ne (1 : K ≃ₐ[ℚ] K)
  have h1 : c δ ^ 2 = δ ^ 2 := by rw [← map_pow, hK.2.2.2.2]; simp
  refine ⟨c, (sq_eq_sq_iff_eq_or_eq_neg.1 h1).resolve_left fun h => hc ?_⟩
  have := ringHom_ext hK (f := (c : K →+* K)) (g := RingHom.id K) h
  exact AlgEquiv.ext fun x => RingHom.congr_fun this x

/- English proof (translation)
Establish `h : σ δ ^ 2 = -(d : ℂ)` using `by rw [← map_pow, hK.2.2.2.2]; simp`. Break down `sq_cases h with h | h` into its components or cases. Conclude with `Or.inl h`. Conclude with `Or.inr (by rw [map_neg, h, neg_neg])`.
-/
theorem embedding_cases (hK : IndefiniteRowSideFullHecke.AdelicScalarMultiplier.IsQuadField K d δ) (σ : K →+* ℂ) :
    σ δ = Complex.I * (Real.sqrt d : ℂ) ∨ σ (-δ) = Complex.I * (Real.sqrt d : ℂ) := by
  have h : σ δ ^ 2 = -(d : ℂ) := by rw [← map_pow, hK.2.2.2.2]; simp
  rcases sq_cases h with h | h
  · exact Or.inl h
  · exact Or.inr (by rw [map_neg, h, neg_neg])

/- English proof (translation)
Take `⟨σ⟩ : Nonempty (K →+* ℂ)` from `inferInstance`. Take `⟨c, hc⟩` from `exists_conj hK`. Break down `embedding_cases hK σ with h | h` into its components or cases. Conclude with `⟨σ, h⟩`. Conclude with `⟨σ.comp (c : K →+* K), by rw [← hc] at h; exact h⟩`.
-/
theorem exists_embedding (hK : IndefiniteRowSideFullHecke.AdelicScalarMultiplier.IsQuadField K d δ) :
    ∃ σ : K →+* ℂ, σ δ = Complex.I * (Real.sqrt d : ℂ) := by
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  obtain ⟨c, hc⟩ := exists_conj hK
  rcases embedding_cases hK σ with h | h
  · exact ⟨σ, h⟩
  · exact ⟨σ.comp (c : K →+* K), by rw [← hc] at h; exact h⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra K E]

omit [IsCMField E] [NumberField E] in

/- English proof (translation)
The claim follows from `forall_congr' fun τ => imp_congr_left ⟨fun h => by rw [← hσ, ← h]; rfl, fun h => ringHom_ext hK (h.trans hσ.symm)⟩`.
-/
theorem sign_iff (hK : IndefiniteRowSideFullHecke.AdelicScalarMultiplier.IsQuadField K d δ) {σ : K →+* ℂ}
    (hσ : σ δ = Complex.I * (Real.sqrt d : ℂ)) (ξ : E) :
    (∀ τ : E →+* ℂ, τ.comp (algebraMap K E) = σ → 0 < (τ ξ).im) ↔
      ∀ τ : E →+* ℂ, τ (algebraMap K E δ) = Complex.I * (Real.sqrt d : ℂ) → 0 < (τ ξ).im :=
  forall_congr' fun τ => imp_congr_left
    ⟨fun h => by rw [← hσ, ← h]; rfl, fun h => ringHom_ext hK (h.trans hσ.symm)⟩

/- English proof (translation)
Establish `h1 : IsCMField.complexConj E (algebraMap K E δ) = algebraMap K E (c δ)`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[IsCMField.complexEmbedding_complexConj, hc, map_neg, map_neg]`. Establish `h : τ (algebraMap K E δ) ^ 2 = -(d : ℂ)`.

Rewrite using `[← map_pow, ← map_pow, hK.2.2.2.2]`. Simplify using the standard rewrite rules. Apply the tactic sequence `rcases sq_cases h with h | h <;> rw [h] <;> simp`. Conclude with `RingHom.congr_fun (ringHom_ext hK (f := (IsCMField.complexConj E : E →+* E).comp (algebraMap K E)) (g := (algebraMap K E).comp (c : K →+* K)) h1) x`.
-/
theorem conj_algebraMap (hK : IndefiniteRowSideFullHecke.AdelicScalarMultiplier.IsQuadField K d δ) {c : K ≃ₐ[ℚ] K} (hc : c δ = -δ)
    (x : K) : IsCMField.complexConj E (algebraMap K E x) = algebraMap K E (c x) := by
  have h1 : IsCMField.complexConj E (algebraMap K E δ) = algebraMap K E (c δ) := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [IsCMField.complexEmbedding_complexConj, hc, map_neg, map_neg]
    have h : τ (algebraMap K E δ) ^ 2 = -(d : ℂ) := by
      rw [← map_pow, ← map_pow, hK.2.2.2.2]; simp
    rcases sq_cases h with h | h <;> rw [h] <;> simp
  exact RingHom.congr_fun (ringHom_ext hK
    (f := (IsCMField.complexConj E : E →+* E).comp (algebraMap K E))
    (g := (algebraMap K E).comp (c : K →+* K)) h1) x

/- English proof (translation)
Establish `hs : Function.Surjective (RingOfIntegers.mapRingHom (c : K →+* K))` using `fun x => ⟨RingOfIntegers.mapRingHom (c.symm : K →+* K) x, RingOfIntegers.ext (c.apply_symm_apply _)⟩`. Rewrite using `[SetLike.ext_iff]`. Use `forall_congr' fun x => iff_congr Iff.rfl ?_` and prove the remaining obligations. Unfold `IndefiniteRowSideFullHecke.IdeleNormTraceForm.conjIdeal`. Rewrite using `[Ideal.mem_map_iff_of_surjective _ hs]`.

Use `exists_congr fun y => and_congr_right fun _ => ?_` and prove the remaining obligations. Rewrite using `[IsScalarTower.algebraMap_apply (𝓞 K) K E, IsScalarTower.algebraMap_apply (𝓞 K) K E, conj_algebraMap hK hc, (algebraMap K E).injective.eq_iff]`. Conclude with `⟨fun h => RingOfIntegers.ext h.symm, fun h => h ▸ rfl⟩`.
-/
theorem conjIdeal_iff (hK : IndefiniteRowSideFullHecke.AdelicScalarMultiplier.IsQuadField K d δ) {c : K ≃ₐ[ℚ] K} (hc : c δ = -δ)
    (𝔐 𝔐' : Ideal (𝓞 K)) :
    (∀ x : 𝓞 K, x ∈ 𝔐' ↔ ∃ y ∈ 𝔐, algebraMap (𝓞 K) E x =
      IsCMField.complexConj E (algebraMap (𝓞 K) E y)) ↔ 𝔐' = IndefiniteRowSideFullHecke.IdeleNormTraceForm.conjIdeal c 𝔐 := by
  have hs : Function.Surjective (RingOfIntegers.mapRingHom (c : K →+* K)) := fun x =>
    ⟨RingOfIntegers.mapRingHom (c.symm : K →+* K) x, RingOfIntegers.ext (c.apply_symm_apply _)⟩
  rw [SetLike.ext_iff]
  refine forall_congr' fun x => iff_congr Iff.rfl ?_
  unfold IndefiniteRowSideFullHecke.IdeleNormTraceForm.conjIdeal
  rw [Ideal.mem_map_iff_of_surjective _ hs]
  refine exists_congr fun y => and_congr_right fun _ => ?_
  rw [IsScalarTower.algebraMap_apply (𝓞 K) K E, IsScalarTower.algebraMap_apply (𝓞 K) K E,
    conj_algebraMap hK hc, (algebraMap K E).injective.eq_iff]
  exact ⟨fun h => RingOfIntegers.ext h.symm, fun h => h ▸ rfl⟩

omit [Algebra K E] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨fun H P hP h => H ⟨P, hP, h⟩, fun H P => H P.asIdeal P.ne_bot⟩`.
-/
theorem unramified_iff :
    (∀ P : HeightOneSpectrum (𝓞 E),
      Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) P.asIdeal) ↔
    ∀ (P : Ideal (𝓞 E)) [P.IsPrime], P ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) P :=
  ⟨fun H P hP h => H ⟨P, hP, h⟩, fun H P => H P.asIdeal P.ne_bot⟩

/- English proof (translation)
Use linear arithmetic over natural numbers and integers.
-/
theorem rank_iff (p q : ℕ) : (1 ≤ p + q ∧ ((q < p ∧ 1 ≤ q) ∨ q = 0)) ↔ q < p := by omega

variable {W : Type} [AddCommGroup W] [Module ℚ W] [Module E W] [IsScalarTower ℚ E W]
  [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]

omit [Algebra K E] [IsScalarTower ℚ E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] in
/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem hermitian_iff (h : W →ₗ[ℚ] W →ₗ[ℚ] E) :
    IndefiniteRowSideFullHecke.IdeleNormTraceForm.IsHermitian E h ↔ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.IsHermitian h := Iff.rfl

omit [Algebra K E] [IsCMField E] [IsScalarTower ℚ E W] [Module (𝓞 E) W]
  [IsScalarTower (𝓞 E) E W] in
/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem signature_iff (h : W →ₗ[ℚ] W →ₗ[ℚ] E) (p q : ℕ) :
    IndefiniteRowSideFullHecke.IdeleNormTraceForm.HasSignature E h p q ↔ ∀ τ, IndefiniteRowSideFullHecke.AdelicScalarMultiplier.HasSignatureAt h τ p q := Iff.rfl

omit [Algebra K E] [IsScalarTower ℚ E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] in

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Algebra.trace ℚ E (ξ * h y x) = -Algebra.trace ℚ E (ξ * h x y)`. Rewrite using `[← map_neg, ← Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) (-(ξ * h x y)), hh.2 x y]`. Simplify using `[hξ]`.
-/
theorem traceForm_skew {h : W →ₗ[ℚ] W →ₗ[ℚ] E} (hh : IndefiniteRowSideFullHecke.AdelicScalarMultiplier.IsHermitian h) {ξ : E}
    (hξ : IsCMField.complexConj E ξ = -ξ) (x y : W) :
    IndefiniteRowSideFullHecke.AdelicScalarMultiplier.traceForm h ξ y x = -IndefiniteRowSideFullHecke.AdelicScalarMultiplier.traceForm h ξ x y := by
  change Algebra.trace ℚ E (ξ * h y x) = -Algebra.trace ℚ E (ξ * h x y)
  rw [← map_neg, ← Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ)
    (-(ξ * h x y)), hh.2 x y]
  simp [hξ]

omit [Algebra K E] [IsScalarTower ℚ E W] [IsScalarTower (𝓞 E) E W] in

/- English proof (translation)
Use `and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun y => iff_congr Iff.rfl (forall₂_congr fun x _ => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(∃ m : ℤ, IndefiniteRowSideFullHecke.AdelicScalarMultiplier.traceForm h ξ x y = m) ↔ _`. Rewrite using `[traceForm_skew hh hξ x y]`. Conclude with `⟨fun ⟨m, hm⟩ => ⟨-m, by simp [hm]⟩, fun ⟨m, hm⟩ => ⟨-m, by simp [← hm]⟩⟩`.
-/
theorem selfDual_iff {h : W →ₗ[ℚ] W →ₗ[ℚ] E} (hh : IndefiniteRowSideFullHecke.AdelicScalarMultiplier.IsHermitian h) {ξ : E}
    (hξ : IsCMField.complexConj E ξ = -ξ) (Λ : Submodule (𝓞 E) W) :
    IndefiniteRowSideFullHecke.IdeleNormTraceForm.IsSelfDualLattice E (IndefiniteRowSideFullHecke.IdeleNormTraceForm.traceForm E ξ h) Λ ↔
      IndefiniteRowSideFullHecke.AdelicScalarMultiplier.IsSelfDualLattice (IndefiniteRowSideFullHecke.AdelicScalarMultiplier.traceForm h ξ) Λ := by
  refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun y =>
    iff_congr Iff.rfl (forall₂_congr fun x _ => ?_)
  change (∃ m : ℤ, IndefiniteRowSideFullHecke.AdelicScalarMultiplier.traceForm h ξ x y = m) ↔ _
  rw [traceForm_skew hh hξ x y]
  exact ⟨fun ⟨m, hm⟩ => ⟨-m, by simp [hm]⟩, fun ⟨m, hm⟩ => ⟨-m, by simp [← hm]⟩⟩

end Hypotheses

/- English proof (translation)
Take `⟨e, he⟩` from `exists_adele_equiv`. Conclude with `⟨fun H K _ _ d δ hK => (ideleClauses_iff e he).1 (H d K δ ((quad_iff d K δ).2 hK)), fun H d K _ _ δ hK => (ideleClauses_iff e he).2 (H K d δ ((quad_iff d K δ).1 hK))⟩`.
-/
theorem ideleNorm_iff : IndefiniteRowSideFullHecke.IdeleNormTraceForm.IdeleNormScale ↔ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.IdeleNormStatement := by
  obtain ⟨e, he⟩ := exists_adele_equiv
  exact ⟨fun H K _ _ d δ hK => (ideleClauses_iff e he).1 (H d K δ ((quad_iff d K δ).2 hK)),
    fun H d K _ _ δ hK => (ideleClauses_iff e he).2 (H K d δ ((quad_iff d K δ).1 hK))⟩

/- English proof (translation)
Take `⟨e, he⟩` from `exists_adele_equiv`. Prove the components needed by the constructor for the conclusion. Introduce `H K _ _ d δ E _ _ _ _ W _ _ _ _ _ _ h p q ξ Λ M 𝔐 𝔐' hK hG hU hh hpq hs hξ hsg hΛ h3 hodd hconj hprod hcop`. Take `⟨c, hc⟩` from `exists_conj hK`. Take `⟨σ, hσ⟩` from `exists_embedding hK`.

Take `rfl` from `(conjIdeal_iff hK hc 𝔐 𝔐').1 hconj`. Conclude with `(levelClauses_iff e he h ξ Λ M _).1 (H d K δ c σ E W h p q ξ Λ M 𝔐 ((quad_iff d K δ).2 hK) hc (unramified_iff.2 hU) ((hermitian_iff h).2 hh) ((signature_iff h p q).2 hs) ((rank_iff p q).2 hpq).1 ((rank_iff p q).2 hpq).2 hξ ((sign_iff hK hσ ξ).2 hsg) ((selfDual_iff hh hξ Λ).2 hΛ) …`. Introduce `H d K _ _ δ c σ E _ _ _ _ hG W _ _ _ _ _ _ h p q ξ Λ M 𝔐 hK hc hU hh hs h1 hpq hξ hsg hΛ h3 hodd hprod hcop`. Establish `hK` using `(quad_iff d K δ).1 hK`. Take `⟨δ', hK', hσ⟩ : ∃ δ' : K, IndefiniteRowSideFullHecke.AdelicScalarMultiplier.IsQuadField K d δ' ∧ σ δ' = Complex.I * (Real.sqrt d : ℂ)` from `(embedding_cases hK σ).elim (fun h => ⟨δ, hK, h⟩) fun h => ⟨-δ, quad_neg hK, h⟩`.

Conclude with `(levelClauses_iff e he h ξ Λ M _).2 (H K d δ' E W h p q ξ Λ M 𝔐 (IndefiniteRowSideFullHecke.IdeleNormTraceForm.conjIdeal c 𝔐) hK' hG (unramified_iff.1 hU) ((hermitian_iff h).1 hh) ((rank_iff p q).1 ⟨h1, hpq⟩) ((signature_iff h p q).1 hs) hξ ((sign_iff hK' hσ ξ).1 hsg) ((selfDual_ …`.
-/
theorem levelGroup_iff : IndefiniteRowSideFullHecke.IdeleNormTraceForm.LevelGroup ↔ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.LevelGroupStatement := by
  obtain ⟨e, he⟩ := exists_adele_equiv
  constructor
  · intro H K _ _ d δ E _ _ _ _ W _ _ _ _ _ _ h p q ξ Λ M 𝔐 𝔐' hK hG hU hh hpq hs hξ hsg hΛ h3 hodd
      hconj hprod hcop
    obtain ⟨c, hc⟩ := exists_conj hK
    obtain ⟨σ, hσ⟩ := exists_embedding hK
    obtain rfl := (conjIdeal_iff hK hc 𝔐 𝔐').1 hconj
    exact (levelClauses_iff e he h ξ Λ M _).1
      (H d K δ c σ E W h p q ξ Λ M 𝔐 ((quad_iff d K δ).2 hK) hc (unramified_iff.2 hU)
        ((hermitian_iff h).2 hh) ((signature_iff h p q).2 hs) ((rank_iff p q).2 hpq).1
        ((rank_iff p q).2 hpq).2 hξ ((sign_iff hK hσ ξ).2 hsg) ((selfDual_iff hh hξ Λ).2 hΛ)
        h3 hodd hprod.symm hcop)
  · intro H d K _ _ δ c σ E _ _ _ _ hG W _ _ _ _ _ _ h p q ξ Λ M 𝔐 hK hc hU hh hs h1 hpq hξ hsg hΛ
      h3 hodd hprod hcop
    have hK := (quad_iff d K δ).1 hK
    obtain ⟨δ', hK', hσ⟩ : ∃ δ' : K, IndefiniteRowSideFullHecke.AdelicScalarMultiplier.IsQuadField K d δ' ∧
        σ δ' = Complex.I * (Real.sqrt d : ℂ) :=
      (embedding_cases hK σ).elim (fun h => ⟨δ, hK, h⟩) fun h => ⟨-δ, quad_neg hK, h⟩
    exact (levelClauses_iff e he h ξ Λ M _).2
      (H K d δ' E W h p q ξ Λ M 𝔐 (IndefiniteRowSideFullHecke.IdeleNormTraceForm.conjIdeal c 𝔐) hK' hG (unramified_iff.1 hU)
        ((hermitian_iff h).1 hh) ((rank_iff p q).1 ⟨h1, hpq⟩) ((signature_iff h p q).1 hs) hξ
        ((sign_iff hK' hσ ξ).1 hsg) ((selfDual_iff hh hξ Λ).1 hΛ) h3 hodd
        ((conjIdeal_iff hK hc 𝔐 _).2 rfl) hprod.symm hcop)

/- English proof (translation)
The claim follows from `and_congr ideleNorm_iff levelGroup_iff`.
-/
theorem normAndLevel_iff : IndefiniteRowSideFullHecke.IdeleNormTraceForm.NormAndLevel ↔ IndefiniteRowSideFullHecke.AdelicScalarMultiplier.Statement :=
  and_congr ideleNorm_iff levelGroup_iff

end GlobalTheory.NormLevelCompare
