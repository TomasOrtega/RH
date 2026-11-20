import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WBMemLatS
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

/- English proof (translation)
Establish `hfin : Module.Finite ℤ_[l] (integralClosure ℤ_[l] K')` using `IsIntegralClosure.finite ℤ_[l] ℚ_[l] K' (integralClosure ℤ_[l] K')`. Establish `htow : IsScalarTower ℤ_[l] K' (Om l)` using `IsScalarTower.of_algebraMap_eq (fun c => by`. Rewrite using `[IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Om l), IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] K']`. Use the proof step `rfl)`. Take `⟨b₀, hb₀⟩` from `hfin.fg_top`.

Set `ι : ↥(integralClosure ℤ_[l] K') → Formalism.Per6.BdRp l` to `fun b => rB l ((b : K') : Om l)`. Set `_ : Algebra (Wl l) (Formalism.Per6.BdRp l)` to `(wB l).toAlgebra`. Establish `hsm : ∀ (a : Wl l) (x : Formalism.Per6.BdRp l), a • x = wB l a * x` using `fun a x => Algebra.smul_def a x`. Set `T : Finset (Formalism.Per6.BdRp l)` to `b₀.image ι`. Set `N : Submodule (Wl l) (Formalism.Per6.BdRp l)` to `Submodule.span (Wl l) (T : Set (Formalism.Per6.BdRp l))`.

Establish `hZ : ∀ c : ℤ_[l], rB l (algebraMap ℤ_[l] (Om l) c) = wB l (GroundTheory.PAdicHodge.IsPerfectoidField.padicIntToWitt (K` using `ℂ_[l]) l c) := by`. Introduce `c`. Establish `h` using `GroundTheory.PAdicHodge.IsPerfectoidField.algebraMap_padic_coe (K := ℂ_[l]) l c`. Establish `h2` using `(GroundTheory.PAdicHodge.algClToBdR l).commutes (c : ℚ_[l])`. Conclude with `h2.trans h`.

Establish `hιmul : ∀ x y, ι (x * y) = ι x * ι y` using `fun x y => by simp [ι]`. Establish `hO : ∀ z, ι z ∈ N`. Introduce `z`. Establish `hz : z ∈ Submodule.span ℤ_[l] (b₀ : Set ↥(integralClosure ℤ_[l] K'))` using `hb₀ ▸ Submodule.mem_top`. Proceed by induction on `hz using Submodule.span_induction with`.

Consider the case `mem x hx => exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hx))`. Consider the case `zero => simp [ι]`. Consider the case `add x y _ _ hx hy`. Establish `e : ι (x + y) = ι x + ι y` using `by simp [ι]`. Rewrite using `[e]`.

Conclude with `N.add_mem hx hy`. Consider the case `smul c x _ hx`. Establish `e : ι (c • x) = (GroundTheory.PAdicHodge.IsPerfectoidField.padicIntToWitt (K` using `ℂ_[l]) l c) • ι x := by`. Rewrite using `[hsm, ← hZ]`. Establish `e2 : (((c • x : ↥(integralClosure ℤ_[l] K')) : K') : Om l) = algebraMap ℤ_[l] (Om l) c * ((x : K') : Om l)`.

Establish `: ((c • x : ↥(integralClosure ℤ_[l] K')) : K') = c • (x : K')` using `rfl`. Rewrite using `[this, Algebra.smul_def, IntermediateField.coe_mul]`. Conclude with `congrArg (· * ((x : K') : Om l)) (IsScalarTower.algebraMap_apply ℤ_[l] K' (Om l) c).symm`. Simplify using `only [ι, e2, map_mul]`. Rewrite using `[e]`.

Conclude with `N.smul_mem _ hx`. Establish `hmul : N * N ≤ N`. Rewrite using `[Submodule.span_mul_span, Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, y, hy, rfl⟩`. Take `⟨b, _, rfl⟩` from `Finset.mem_image.1 (Finset.mem_coe.1 hx)`.

Take `⟨b', _, rfl⟩` from `Finset.mem_image.1 (Finset.mem_coe.1 hy)`. Express the relevant statement in the definitionally equal form `ι b * ι b' ∈ N`. Rewrite using `[← hιmul]`. Conclude with `hO _`. Establish `h1 : (1 : Formalism.Per6.BdRp l) ∈ N`.

Use `hO 1` as an intermediate fact. Simplify `this` using `[ι]`. Establish `hint : ∀ b : ↥(integralClosure ℤ_[l] K'), IsIntegral ℤ_[l] ((b : K') : Om l)` using `fun b => (isIntegral_algebraMap_iff (A := K') (B := Om l) (algebraMap K' (Om l)).injective).2 b.2`. Establish `hS : ∀ x ∈ latS K', x ∈ N`. Introduce `x hx`.

Unfold `latS at hx`. Proceed by induction on `hx using Subring.closure_induction with`. Consider the case `mem x hx`. Break down `hx with ⟨a, rfl⟩ | ⟨y, ⟨hyK, hyI⟩, rfl⟩` into its components or cases. Use `N.smul_mem a h1` as an intermediate fact.

Rewrite `this` using `[hsm, mul_one]`. Then use the resulting hypothesis. Establish `hz : IsIntegral ℤ_[l] (⟨y, hyK⟩ : K')` using `(isIntegral_algebraMap_iff (A := K') (B := Om l) (algebraMap K' (Om l)).injective).1 hyI`. Conclude with `hO ⟨⟨y, hyK⟩, hz⟩`. Consider the case `zero => exact N.zero_mem`. Consider the case `one => exact h1`.

Consider the case `add _ _ _ _ hx hy => exact N.add_mem hx hy`. Consider the case `neg _ _ hx => exact N.neg_mem hx`. Consider the case `mul _ _ _ _ hx hy => exact hmul (Submodule.mul_mem_mul hx hy)`. Use `⟨T, ?_, ?_⟩` and prove the remaining obligations. Introduce `t ht`.

Take `⟨b, _, rfl⟩` from `Finset.mem_image.1 ht`. Conclude with `rB_mem_latS K' (b : K').2 (hint b)`. Introduce `x hx`. Take `⟨f, _, hf⟩` from `Submodule.mem_span_finset.1 (hS x hx)`. Conclude with `⟨f, by rw [← hf]; exact Finset.sum_congr rfl (fun t _ => by rw [hsm, mul_comm])⟩`.
-/
theorem latS_finite_span {l : ℕ} [Fact l.Prime] (K' : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] K'] :
    ∃ T : Finset (Formalism.Per6.BdRp l), (∀ t ∈ T, t ∈ latS K') ∧
      ∀ s ∈ latS K', ∃ a : Formalism.Per6.BdRp l → Wl l, s = ∑ t ∈ T, t * wB l (a t) := by
  have hfin : Module.Finite ℤ_[l] (integralClosure ℤ_[l] K') :=
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] K' (integralClosure ℤ_[l] K')
  have htow : IsScalarTower ℤ_[l] K' (Om l) := IsScalarTower.of_algebraMap_eq (fun c => by
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Om l), IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] K']
    rfl)
  obtain ⟨b₀, hb₀⟩ := hfin.fg_top
  let ι : ↥(integralClosure ℤ_[l] K') → Formalism.Per6.BdRp l := fun b => rB l ((b : K') : Om l)
  let _ : Algebra (Wl l) (Formalism.Per6.BdRp l) := (wB l).toAlgebra
  have hsm : ∀ (a : Wl l) (x : Formalism.Per6.BdRp l), a • x = wB l a * x := fun a x => Algebra.smul_def a x
  let T : Finset (Formalism.Per6.BdRp l) := b₀.image ι
  let N : Submodule (Wl l) (Formalism.Per6.BdRp l) := Submodule.span (Wl l) (T : Set (Formalism.Per6.BdRp l))
  have hZ : ∀ c : ℤ_[l], rB l (algebraMap ℤ_[l] (Om l) c) =
      wB l (GroundTheory.PAdicHodge.IsPerfectoidField.padicIntToWitt (K := ℂ_[l]) l c) := by
    intro c
    have h := GroundTheory.PAdicHodge.IsPerfectoidField.algebraMap_padic_coe (K := ℂ_[l]) l c
    have h2 := (GroundTheory.PAdicHodge.algClToBdR l).commutes (c : ℚ_[l])
    exact h2.trans h
  have hιmul : ∀ x y, ι (x * y) = ι x * ι y := fun x y => by simp [ι]
  have hO : ∀ z, ι z ∈ N := by
    intro z
    have hz : z ∈ Submodule.span ℤ_[l] (b₀ : Set ↥(integralClosure ℤ_[l] K')) := hb₀ ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hx))
    | zero => simp [ι]
    | add x y _ _ hx hy =>
      have e : ι (x + y) = ι x + ι y := by simp [ι]
      rw [e]; exact N.add_mem hx hy
    | smul c x _ hx =>
      have e : ι (c • x) = (GroundTheory.PAdicHodge.IsPerfectoidField.padicIntToWitt (K := ℂ_[l]) l c) • ι x := by
        rw [hsm, ← hZ]
        have e2 : (((c • x : ↥(integralClosure ℤ_[l] K')) : K') : Om l) =
            algebraMap ℤ_[l] (Om l) c * ((x : K') : Om l) := by
          have : ((c • x : ↥(integralClosure ℤ_[l] K')) : K') = c • (x : K') := rfl
          rw [this, Algebra.smul_def, IntermediateField.coe_mul]
          exact congrArg (· * ((x : K') : Om l)) (IsScalarTower.algebraMap_apply ℤ_[l] K' (Om l) c).symm
        simp only [ι, e2, map_mul]
      rw [e]; exact N.smul_mem _ hx
  have hmul : N * N ≤ N := by
    rw [Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    obtain ⟨b', _, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    change ι b * ι b' ∈ N
    rw [← hιmul]
    exact hO _
  have h1 : (1 : Formalism.Per6.BdRp l) ∈ N := by
    have := hO 1
    simpa [ι] using this
  have hint : ∀ b : ↥(integralClosure ℤ_[l] K'), IsIntegral ℤ_[l] ((b : K') : Om l) := fun b =>
    (isIntegral_algebraMap_iff (A := K') (B := Om l) (algebraMap K' (Om l)).injective).2 b.2
  have hS : ∀ x ∈ latS K', x ∈ N := by
    intro x hx
    unfold latS at hx
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨a, rfl⟩ | ⟨y, ⟨hyK, hyI⟩, rfl⟩
      · have := N.smul_mem a h1
        rwa [hsm, mul_one] at this
      · have hz : IsIntegral ℤ_[l] (⟨y, hyK⟩ : K') :=
          (isIntegral_algebraMap_iff (A := K') (B := Om l) (algebraMap K' (Om l)).injective).1 hyI
        exact hO ⟨⟨y, hyK⟩, hz⟩
    | zero => exact N.zero_mem
    | one => exact h1
    | add _ _ _ _ hx hy => exact N.add_mem hx hy
    | neg _ _ hx => exact N.neg_mem hx
    | mul _ _ _ _ hx hy => exact hmul (Submodule.mul_mem_mul hx hy)
  refine ⟨T, ?_, ?_⟩
  · intro t ht
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 ht
    exact rB_mem_latS K' (b : K').2 (hint b)
  · intro x hx
    obtain ⟨f, _, hf⟩ := Submodule.mem_span_finset.1 (hS x hx)
    exact ⟨f, by rw [← hf]; exact Finset.sum_congr rfl (fun t _ => by rw [hsm, mul_comm])⟩

end GlobalTheory.CompanionTheory.LTPer
