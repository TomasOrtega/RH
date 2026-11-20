import Mathlib
import GroundTheory.AutomorphicForms.HermitianExistence
import GroundTheory.AutomorphicForms.HermitianOrthogonal
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Theta

open Module Matrix NumberField IsDedekindDomain TensorProduct GroundTheory.Automorphic

section Objects

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

def IsCMUnramified : Prop :=
  IsTotallyReal F ∧ IsTotallyComplex E ∧
    ∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.ramificationIdx (𝓞 F) = 1

def locIntegers (v : HeightOneSpectrum (𝓞 F)) :
    Subalgebra (v.adicCompletionIntegers F) (v.adicCompletion F ⊗[F] E) :=
  integralClosure _ _

variable {F E}

def baseGram (R : Type*) [Field R] [Algebra F R] {M : ℕ} (h : HermitianForm F E (Fin M → E)) :
    Matrix (Fin M) (Fin M) (R ⊗[F] E) :=
  (gram h.toSesq (Pi.basisFun E (Fin M))).map
    (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E)

def matForm (R : Type*) {A : Type*} [Field R] [CommRing A] [Algebra R A]
    [Algebra.IsQuadraticExtension R A] {ι : Type*} [Fintype ι] (G : Matrix ι ι A)
    (x y : ι → A) : A :=
  ∑ i, ∑ j, conj R A (x i) * G i j * y j

def signVector (A : Type*) [Ring A] (M p : ℕ) : Fin M → A :=
  fun i => if (i : ℕ) < p then 1 else -1

def HasSignatureAt {M : ℕ} (h : HermitianForm F E (Fin M → E)) (w : InfinitePlace F)
    (p q : ℕ) : Prop :=
  p + q = M ∧
    IsCongr (conjHom w.Completion (w.Completion ⊗[F] E)) (baseGram w.Completion h)
      (diagonal (signVector (w.Completion ⊗[F] E) M p))

variable (v : HeightOneSpectrum (𝓞 F))

def IsLocLattice {M : ℕ}
    (L : Submodule (locIntegers F E v) (Fin M → v.adicCompletion F ⊗[F] E)) : Prop :=
  L.FG ∧ Submodule.span (v.adicCompletion F ⊗[F] E)
    (L : Set (Fin M → v.adicCompletion F ⊗[F] E)) = ⊤

def IsSelfDualAt {M : ℕ} (h : HermitianForm F E (Fin M → E))
    (L : Submodule (locIntegers F E v) (Fin M → v.adicCompletion F ⊗[F] E)) : Prop :=
  IsLocLattice v L ∧
    ∀ x, x ∈ L ↔
      ∀ y ∈ L, matForm (v.adicCompletion F) (baseGram (v.adicCompletion F) h) x y ∈
        locIntegers F E v

def IsGlobalLattice {M : ℕ} (Λ : Submodule (𝓞 E) (Fin M → E)) : Prop :=
  Λ.FG ∧ Submodule.span E (Λ : Set (Fin M → E)) = ⊤

def latticeAt {M : ℕ} (Λ : Submodule (𝓞 E) (Fin M → E)) :
    Submodule (locIntegers F E v) (Fin M → v.adicCompletion F ⊗[F] E) :=
  Submodule.span _ ((fun x i => (1 : v.adicCompletion F) ⊗ₜ[F] x i) '' (Λ : Set (Fin M → E)))

end Objects

section Statements

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

def SelfDualHermitianExists.Statement : Prop :=
  IsCMUnramified F E →
    ∀ (M : ℕ), 1 ≤ M → ∀ p q : InfinitePlace F → ℕ, (∀ τ, p τ + q τ = M) →
      ((∃ h : HermitianForm F E (Fin M → E), (∀ τ, HasSignatureAt h τ (p τ) (q τ)) ∧
          ∀ v : HeightOneSpectrum (𝓞 F), ∃ L, IsSelfDualAt v h L) ↔
        Even (∑ τ, q τ))

def SelfDualHermitianUnique.Statement : Prop :=
  IsCMUnramified F E →
    ∀ (M : ℕ), 1 ≤ M → ∀ p q : InfinitePlace F → ℕ, (∀ τ, p τ + q τ = M) →
      ∀ h h' : HermitianForm F E (Fin M → E),
        (∀ τ, HasSignatureAt h τ (p τ) (q τ)) → (∀ τ, HasSignatureAt h' τ (p τ) (q τ)) →
        (∀ v : HeightOneSpectrum (𝓞 F), ∃ L, IsSelfDualAt v h L) →
        (∀ v : HeightOneSpectrum (𝓞 F), ∃ L', IsSelfDualAt v h' L') →
        h.Isometric h'

def SelfDualHermitianLocal.Statement : Prop :=
  IsCMUnramified F E →
    ∀ (M : ℕ), 1 ≤ M → ∀ h h' : HermitianForm F E (Fin M → E),
      ∀ (v : HeightOneSpectrum (𝓞 F)) (L L' : Submodule (locIntegers F E v)
          (Fin M → v.adicCompletion F ⊗[F] E)),
        IsSelfDualAt v h L → IsSelfDualAt v h' L' →
        ∃ P : Matrix (Fin M) (Fin M) (v.adicCompletion F ⊗[F] E), IsUnit P.det ∧
          (P.map (conjHom (v.adicCompletion F) (v.adicCompletion F ⊗[F] E)))ᵀ *
              baseGram (v.adicCompletion F) h' * P = baseGram (v.adicCompletion F) h ∧
          (fun x => P *ᵥ x) '' (L : Set (Fin M → v.adicCompletion F ⊗[F] E)) = L'

def SelfDualHermitianGlobalLattice.Statement : Prop :=
  IsCMUnramified F E →
    ∀ (M : ℕ), 1 ≤ M → ∀ h : HermitianForm F E (Fin M → E),
      (∀ v : HeightOneSpectrum (𝓞 F), ∃ L, IsSelfDualAt v h L) →
      ∃ Λ : Submodule (𝓞 E) (Fin M → E), IsGlobalLattice Λ ∧
        ∀ v : HeightOneSpectrum (𝓞 F), IsSelfDualAt v h (latticeAt v Λ)

end Statements

section Inhabitants

set_option linter.unusedSectionVars false

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

abbrev unitForm (F E : Type*) [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
    (M : ℕ) : HermitianForm F E (Fin M → E) :=
  diagForm (E := E) fun _ : Fin M => (1 : Fˣ)

/- English proof (translation)
Rewrite using `[baseGram, gram_diagForm, diagonal_map (map_zero _), ← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `[Algebra.TensorProduct.one_def]`.
-/
theorem baseGram_unitForm (R : Type*) [Field R] [Algebra F R] (M : ℕ) :
    baseGram R (unitForm F E M) = 1 := by
  rw [baseGram, gram_diagForm, diagonal_map (map_zero _), ← diagonal_one]
  congr 1
  funext i
  simp [Algebra.TensorProduct.one_def]

/- English proof (translation)
Simplify using `[matForm, Matrix.one_apply]`.
-/
theorem matForm_one (R : Type*) {A : Type*} [Field R] [CommRing A] [Algebra R A]
    [Algebra.IsQuadraticExtension R A] {ι : Type*} [Fintype ι] [DecidableEq ι] (x y : ι → A) :
    matForm R (1 : Matrix ι ι A) x y = ∑ i, conj R A (x i) * y i := by
  simp [matForm, Matrix.one_apply]

/- English proof (translation)
Use `⟨add_zero M, ?_⟩` and prove the remaining obligations. Establish `: diagonal (signVector (w.Completion ⊗[F] E) M M) = 1`. Rewrite using `[← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Simplify using `[signVector, i.isLt]`. Rewrite using `[baseGram_unitForm, this]`. Conclude with `IsCongr.refl _ _`.
-/
theorem hasSignatureAt_one (w : InfinitePlace F) (M : ℕ) :
    HasSignatureAt (unitForm F E M) w M 0 := by
  refine ⟨add_zero M, ?_⟩
  have : diagonal (signVector (w.Completion ⊗[F] E) M M) = 1 := by
    rw [← diagonal_one]
    congr 1
    funext i
    simp [signVector, i.isLt]
  rw [baseGram_unitForm, this]
  exact IsCongr.refl _ _

variable (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Rewrite `hz`, the goal using `[locIntegers, mem_integralClosure_iff]`. Conclude with `hz.map (((conj (v.adicCompletion F) (v.adicCompletion F ⊗[F] E)).toAlgHom).restrictScalars (v.adicCompletionIntegers F))`.
-/
theorem conj_mem_locIntegers {z : v.adicCompletion F ⊗[F] E} (hz : z ∈ locIntegers F E v) :
    conj (v.adicCompletion F) (v.adicCompletion F ⊗[F] E) z ∈ locIntegers F E v := by
  rw [locIntegers, mem_integralClosure_iff] at hz ⊢
  exact hz.map (((conj (v.adicCompletion F) (v.adicCompletion F ⊗[F] E)).toAlgHom).restrictScalars
    (v.adicCompletionIntegers F))

def stdLatticeAt (M : ℕ) :
    Submodule (locIntegers F E v) (Fin M → v.adicCompletion F ⊗[F] E) where
  carrier := {x | ∀ i, x i ∈ locIntegers F E v}
  add_mem' hx hy i := add_mem (hx i) (hy i)
  zero_mem' _ := zero_mem _
  smul_mem' c x hx i := by
    rw [Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul]
    exact mul_mem c.2 (hx i)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_stdLatticeAt {M : ℕ} {x : Fin M → v.adicCompletion F ⊗[F] E} :
    x ∈ stdLatticeAt v M ↔ ∀ i, x i ∈ locIntegers F E v := Iff.rfl

/- English proof (translation)
Introduce `j`. Break down `eq_or_ne j i with rfl | hj` into its components or cases. Rewrite using `[Pi.single_eq_same]`. Conclude with `one_mem _`. Rewrite using `[Pi.single_eq_of_ne hj]`.

Conclude with `zero_mem _`.
-/
theorem single_mem_stdLatticeAt {M : ℕ} (i : Fin M) :
    Pi.single i 1 ∈ stdLatticeAt (E := E) v M := by
  intro j
  rcases eq_or_ne j i with rfl | hj
  · rw [Pi.single_eq_same]; exact one_mem _
  · rw [Pi.single_eq_of_ne hj]; exact zero_mem _

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Establish `hx' : x = ∑ i, (⟨x i, hx i⟩ : locIntegers F E v) • Pi.single i 1`. Use function extensionality and compare the values at `j`. Simplify using `[Finset.sum_apply, Pi.single_apply, Subalgebra.smul_def]`.

Rewrite using `[hx']`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `single_mem_stdLatticeAt v i`.
-/
theorem stdLatticeAt_eq_span (M : ℕ) :
    stdLatticeAt (E := E) v M =
      Submodule.span _ (Set.range fun i : Fin M => Pi.single i (1 : v.adicCompletion F ⊗[F] E)) := by
  apply le_antisymm
  · intro x hx
    have hx' : x = ∑ i, (⟨x i, hx i⟩ : locIntegers F E v) • Pi.single i 1 := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, Subalgebra.smul_def]
    rw [hx']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact single_mem_stdLatticeAt v i

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[stdLatticeAt_eq_span]`. Conclude with `Submodule.fg_span (Set.finite_range _)`. Rewrite using `[eq_top_iff]`. Introduce `x _`.

Establish `hx : x = ∑ i, x i • Pi.single i (1 : v.adicCompletion F ⊗[F] E)`. Use function extensionality and compare the values at `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Rewrite using `[hx]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (single_mem_stdLatticeAt v i))`.
-/
theorem isLocLattice_std (M : ℕ) : IsLocLattice v (stdLatticeAt (E := E) v M) := by
  refine ⟨?_, ?_⟩
  · rw [stdLatticeAt_eq_span]
    exact Submodule.fg_span (Set.finite_range _)
  · rw [eq_top_iff]
    intro x _
    have hx : x = ∑ i, x i • Pi.single i (1 : v.adicCompletion F ⊗[F] E) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (single_mem_stdLatticeAt v i))

/- English proof (translation)
Use `⟨isLocLattice_std v M, fun x => ⟨fun hx y hy => ?_, fun H i => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[baseGram_unitForm, matForm_one]`. Conclude with `Subalgebra.sum_mem _ fun i _ => mul_mem (conj_mem_locIntegers v (hx i)) (hy i)`. Establish `h1` using `H (Pi.single i 1) (single_mem_stdLatticeAt v i)`. Rewrite `h1` using `[baseGram_unitForm, matForm_one]`.

Simplify using `only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1`. Simplify `conj_mem_locIntegers v h1` using `only [conj_conj]`.
-/
theorem isSelfDualAt_one (M : ℕ) : IsSelfDualAt v (unitForm F E M) (stdLatticeAt v M) := by
  refine ⟨isLocLattice_std v M, fun x => ⟨fun hx y hy => ?_, fun H i => ?_⟩⟩
  · rw [baseGram_unitForm, matForm_one]
    exact Subalgebra.sum_mem _ fun i _ => mul_mem (conj_mem_locIntegers v (hx i)) (hy i)
  · have h1 := H (Pi.single i 1) (single_mem_stdLatticeAt v i)
    rw [baseGram_unitForm, matForm_one] at h1
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at h1
    simpa only [conj_conj] using conj_mem_locIntegers v h1

def stdLattice (M : ℕ) : Submodule (𝓞 E) (Fin M → E) where
  carrier := {x | ∀ i, IsIntegral ℤ (x i)}
  add_mem' hx hy i := (hx i).add (hy i)
  zero_mem' _ := isIntegral_zero
  smul_mem' c x hx i := by
    rw [Pi.smul_apply, Algebra.smul_def]
    exact (RingOfIntegers.isIntegral_coe c).mul (hx i)

/- English proof (translation)
Introduce `j`. Break down `eq_or_ne j i with rfl | hj` into its components or cases. Rewrite using `[Pi.single_eq_same]`. Conclude with `isIntegral_one`. Rewrite using `[Pi.single_eq_of_ne hj]`.

Conclude with `isIntegral_zero`.
-/
theorem single_mem_stdLattice {M : ℕ} (i : Fin M) : Pi.single i (1 : E) ∈ stdLattice (E := E) M := by
  intro j
  rcases eq_or_ne j i with rfl | hj
  · rw [Pi.single_eq_same]; exact isIntegral_one
  · rw [Pi.single_eq_of_ne hj]; exact isIntegral_zero

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Establish `hx' : x = ∑ i, (⟨x i, hx i⟩ : 𝓞 E) • Pi.single i 1`. Use function extensionality and compare the values at `j`. Simplify using `[Finset.sum_apply, Pi.single_apply, Algebra.smul_def]`.

Both sides reduce to the same expression. Rewrite using `[hx']`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Conclude with `single_mem_stdLattice i`.
-/
theorem stdLattice_eq_span (M : ℕ) :
    stdLattice (E := E) M = Submodule.span (𝓞 E) (Set.range fun i : Fin M => Pi.single i (1 : E)) := by
  apply le_antisymm
  · intro x hx
    have hx' : x = ∑ i, (⟨x i, hx i⟩ : 𝓞 E) • Pi.single i 1 := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
      rfl
    rw [hx']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact single_mem_stdLattice i

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[stdLattice_eq_span]`. Conclude with `Submodule.fg_span (Set.finite_range _)`. Rewrite using `[eq_top_iff]`. Introduce `x _`.

Establish `hx : x = ∑ i, x i • Pi.single i (1 : E)`. Use function extensionality and compare the values at `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Rewrite using `[hx]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (single_mem_stdLattice i))`.
-/
theorem isGlobalLattice_std (M : ℕ) : IsGlobalLattice (stdLattice (E := E) M) := by
  refine ⟨?_, ?_⟩
  · rw [stdLattice_eq_span]
    exact Submodule.fg_span (Set.finite_range _)
  · rw [eq_top_iff]
    intro x _
    have hx : x = ∑ i, x i • Pi.single i (1 : E) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (single_mem_stdLattice i))

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[latticeAt, Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩ i`. Rewrite using `[locIntegers, mem_integralClosure_iff]`. Take `⟨p, hp, hpx⟩` from `hx i`.

Use `⟨p.map (Int.castRingHom (v.adicCompletionIntegers F)), hp.map _, ?_⟩` and prove the remaining obligations. Use `set g : E →+* v.adicCompletion F ⊗[F] E := (Algebra.TensorProduct.includeRight : E →ₐ[F] v.adicCompletion F ⊗[F] E).toRingHom`. Establish `e : (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F ⊗[F] E)).comp (Int.castRingHom (v.adicCompletionIntegers F)) = g.comp (algebraMap ℤ E)` using `RingHom.ext_int _ _`. Rewrite using `[Polynomial.eval₂_map, e]`. Use `show Polynomial.eval₂ (g.comp (algebraMap ℤ E)) (g (x i)) p = 0`.

Rewrite using `[← Polynomial.hom_eval₂, hpx, map_zero]`. Rewrite using `[stdLatticeAt_eq_span, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Use `Submodule.subset_span ⟨Pi.single i 1, single_mem_stdLattice i, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `j`.

Break down `eq_or_ne j i with rfl | hj` into its components or cases. Simplify using `[Algebra.TensorProduct.one_def]`. Simplify using `[Pi.single_eq_of_ne hj]`.
-/
theorem latticeAt_std (M : ℕ) : latticeAt v (stdLattice (E := E) M) = stdLatticeAt v M := by
  apply le_antisymm
  · rw [latticeAt, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩ i
    rw [locIntegers, mem_integralClosure_iff]
    obtain ⟨p, hp, hpx⟩ := hx i
    refine ⟨p.map (Int.castRingHom (v.adicCompletionIntegers F)), hp.map _, ?_⟩
    set g : E →+* v.adicCompletion F ⊗[F] E :=
      (Algebra.TensorProduct.includeRight : E →ₐ[F] v.adicCompletion F ⊗[F] E).toRingHom
    have e : (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F ⊗[F] E)).comp
        (Int.castRingHom (v.adicCompletionIntegers F)) = g.comp (algebraMap ℤ E) :=
      RingHom.ext_int _ _
    rw [Polynomial.eval₂_map, e]
    show Polynomial.eval₂ (g.comp (algebraMap ℤ E)) (g (x i)) p = 0
    rw [← Polynomial.hom_eval₂, hpx, map_zero]
  · rw [stdLatticeAt_eq_span, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine Submodule.subset_span ⟨Pi.single i 1, single_mem_stdLattice i, ?_⟩
    funext j
    rcases eq_or_ne j i with rfl | hj
    · simp [Algebra.TensorProduct.one_def]
    · simp [Pi.single_eq_of_ne hj]

/- English proof (translation)
Rewrite using `[latticeAt_std]`. Conclude with `isSelfDualAt_one v M`.
-/
theorem isSelfDualAt_latticeAt_std (M : ℕ) :
    IsSelfDualAt v (unitForm F E M) (latticeAt v (stdLattice M)) := by
  rw [latticeAt_std]
  exact isSelfDualAt_one v M

end Inhabitants

end GroundTheory.Heights₂.Theta
