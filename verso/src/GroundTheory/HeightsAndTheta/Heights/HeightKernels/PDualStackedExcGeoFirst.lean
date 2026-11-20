import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField
  Matrix

noncomputable section

namespace StackedExceptionalFirstGeometric

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

/- English proof (translation)
Introduce `x hx`. Rewrite using `[smul_dotProduct, smul_eq_mul]`. Take `⟨r, hr⟩` from `hφ x hx`. Conclude with `⟨μ * r, by rw [map_mul, hr]⟩`.
-/
theorem smul_mem_dual (F : HermLattice K i) (μ : 𝓞 K) {φ : Fin i → K} (hφ : φ ∈ dualLattice F) :
    (algebraMap (𝓞 K) K μ) • φ ∈ dualLattice F := by
  intro x hx
  rw [smul_dotProduct, smul_eq_mul]
  obtain ⟨r, hr⟩ := hφ x hx
  exact ⟨μ * r, by rw [map_mul, hr]⟩

/- English proof (translation)
Establish `hsup : F'.lattice ⊔ Submodule.span (𝓞 K) {y} = F.lattice`. Break down `hcov _ le_sup_left (sup_le hle ((Submodule.span_singleton_le_iff_mem _ _).mpr hyF)) with h | h` into its components or cases. Conclude with `absurd (h ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)) hy`. Conclude with `h`. Rewrite `hx` using `[← hsup, Submodule.mem_sup]`.

Take `⟨z, hz, w, hw, rfl⟩` from `hx`. Take `⟨μ, rfl⟩` from `Submodule.mem_span_singleton.mp hw`. Conclude with `⟨z, hz, μ, rfl⟩`.
-/
theorem exists_decomp {F F' : HermLattice K i} (hle : F'.lattice ≤ F.lattice)
    (hcov : ∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice)
    {y : Fin i → K} (hyF : y ∈ F.lattice) (hy : y ∉ F'.lattice) {x : Fin i → K} (hx : x ∈ F.lattice) :
    ∃ z ∈ F'.lattice, ∃ μ : 𝓞 K, x = z + μ • y := by
  have hsup : F'.lattice ⊔ Submodule.span (𝓞 K) {y} = F.lattice := by
    rcases hcov _ le_sup_left (sup_le hle ((Submodule.span_singleton_le_iff_mem _ _).mpr hyF)) with h | h
    · exact absurd (h ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)) hy
    · exact h
  rw [← hsup, Submodule.mem_sup] at hx
  obtain ⟨z, hz, w, hw, rfl⟩ := hx
  obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hw
  exact ⟨z, hz, μ, rfl⟩

/- English proof (translation)
Introduce `x hx`. Take `⟨z, hz, μ, rfl⟩` from `exists_decomp hle hcov hyF hy hx`. Rewrite using `[dotProduct_add, dotProduct_smul]`. Take `⟨r, hr⟩` from `hψ z hz`. Take `⟨s, hs⟩` from `hψy`.

Conclude with `⟨r + μ * s, by rw [map_add, map_mul, hr, hs, Algebra.smul_def]⟩`.
-/
theorem mem_dual_of {F F' : HermLattice K i} (hle : F'.lattice ≤ F.lattice)
    (hcov : ∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice)
    {y : Fin i → K} (hyF : y ∈ F.lattice) (hy : y ∉ F'.lattice) {ψ : Fin i → K} (hψ : ψ ∈ dualLattice F')
    (hψy : ψ ⬝ᵥ y ∈ (algebraMap (𝓞 K) K).range) : ψ ∈ dualLattice F := by
  intro x hx
  obtain ⟨z, hz, μ, rfl⟩ := exists_decomp hle hcov hyF hy hx
  rw [dotProduct_add, dotProduct_smul]
  obtain ⟨r, hr⟩ := hψ z hz
  obtain ⟨s, hs⟩ := hψy
  exact ⟨r + μ * s, by rw [map_add, map_mul, hr, hs, Algebra.smul_def]⟩

/- English proof (translation)
Take `⟨y, hyF, hy⟩` from `SetLike.exists_of_lt hlt`. Establish `hle` using `hlt.le`. Set `𝔪 : Ideal (𝓞 K)` to `Submodule.comap (LinearMap.toSpanSingleton (𝓞 K) (Fin i → K) y) F'.lattice`. Establish `hmem : ∀ μ : 𝓞 K, μ ∈ 𝔪 ↔ μ • y ∈ F'.lattice` using `fun μ => Iff.rfl`. Establish `hunit : ∀ μ : 𝓞 K, μ ∉ 𝔪 → ∃ ν : 𝓞 K, 1 - ν * μ ∈ 𝔪`.

Introduce `μ hμ`. Take `⟨z, hz, ν, hzν⟩` from `exists_decomp (F := F) (F' := F') hle hcov (F.lattice.smul_mem μ hyF) ((hmem μ).not.mp hμ) hyF`. Use `⟨ν, (hmem _).mpr ?_⟩` and prove the remaining obligations. Rewrite using `[sub_smul, one_smul, mul_smul, sub_eq_of_eq_add hzν]`. Conclude with `hz`.

Establish `hbot : 𝔪 ≠ ⊥`. Introduce `h`. Apply `NumberField.RingOfIntegers.not_isField K` to reduce the goal to its premises. Use `⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {μ} hμ => ?_⟩` and prove the remaining obligations. Take `⟨ν, hν⟩` from `hunit μ (by rw [h, Ideal.mem_bot]; exact hμ)`.

Rewrite `hν` using `[h, Ideal.mem_bot, sub_eq_zero]`. Conclude with `⟨ν, by rw [mul_comm]; exact hν.symm⟩`. Establish `hint𝔪 : ∀ {ψ : Fin i → K}, ψ ∈ dualLattice F' → ∀ m ∈ 𝔪, algebraMap (𝓞 K) K m * (ψ ⬝ᵥ y) ∈ (algebraMap (𝓞 K) K).range`. Introduce `ψ hψ m hm`. Use `hψ _ ((hmem m).mp hm)` as an intermediate fact.

Rewrite `this` using `[dotProduct_smul, Algebra.smul_def]`. Then use the resulting hypothesis. Establish `hu : φc ⬝ᵥ y ∉ (algebraMap (𝓞 K) K).range` using `fun h => hc' (mem_dual_of hle hcov hyF hy hc h)`. Establish `hex : ∃ m ∈ 𝔪, ∃ β : 𝓞 K, algebraMap (𝓞 K) K m * (φc ⬝ᵥ y) = algebraMap (𝓞 K) K β ∧ β ∉ 𝔪`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Set `M : Submodule (𝓞 K) K` to `Submodule.map (Algebra.linearMap (𝓞 K) K) 𝔪`. Establish `hint : IsIntegral (𝓞 K) (φc ⬝ᵥ y)`. Use `isIntegral_of_smul_mem_submodule M ?_ ?_ (φc ⬝ᵥ y) ?_` and prove the remaining obligations. Rewrite using `[Submodule.ne_bot_iff]`. Take `⟨m, hm, hm0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hbot`.

Use `⟨_, ⟨m, hm, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using `using hm0`. Conclude with `Submodule.FG.map _ (IsNoetherian.noetherian _)`. Introduce and unpack `_ ⟨m, hm, rfl⟩`. Take `⟨β, hβ⟩` from `hint𝔪 hc m hm`.

Use `⟨β, hcon m hm β hβ.symm, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.linearMap_apply, hβ, smul_eq_mul, mul_comm]`. Both sides reduce to the same expression. Take `⟨w, hw⟩` from `IsIntegrallyClosed.algebraMap_eq_of_integral hint`. Conclude with `hu ⟨w, hw⟩`.

Take `⟨m₁, hm₁, β, hβ, hβ𝔪⟩` from `hex`. Take `⟨ν, hν⟩` from `hunit β hβ𝔪`. Take `⟨r₀, hr₀⟩` from `hint𝔪 hφ _ hν`. Take `⟨r₁, hr₁⟩` from `hint𝔪 hφ _ (𝔪.mul_mem_left ν hm₁)`. Use `⟨r₁, mem_dual_of hle hcov hyF hy (sub_mem hφ (smul_mem_dual F' r₁ hc)) ⟨r₀, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[sub_dotProduct, smul_dotProduct, smul_eq_mul]`. Simplify using `only [map_sub, map_one, map_mul] at hβ hr₀ hr₁ ⊢`. Take the linear combination `hr₀ + (φc ⬝ᵥ y) * hr₁ + (algebraMap (𝓞 K) K ν * (φ ⬝ᵥ y)) * hβ`.
-/
theorem exists_sub_mem_dual {F F' : HermLattice K i} (hlt : F'.lattice < F.lattice)
    (hcov : ∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice)
    {φc φ : Fin i → K} (hc : φc ∈ dualLattice F') (hc' : φc ∉ dualLattice F) (hφ : φ ∈ dualLattice F') :
    ∃ l : 𝓞 K, φ - (algebraMap (𝓞 K) K l) • φc ∈ dualLattice F := by
  obtain ⟨y, hyF, hy⟩ := SetLike.exists_of_lt hlt
  have hle := hlt.le
  let 𝔪 : Ideal (𝓞 K) := Submodule.comap (LinearMap.toSpanSingleton (𝓞 K) (Fin i → K) y) F'.lattice
  have hmem : ∀ μ : 𝓞 K, μ ∈ 𝔪 ↔ μ • y ∈ F'.lattice := fun μ => Iff.rfl
  have hunit : ∀ μ : 𝓞 K, μ ∉ 𝔪 → ∃ ν : 𝓞 K, 1 - ν * μ ∈ 𝔪 := by
    intro μ hμ
    obtain ⟨z, hz, ν, hzν⟩ := exists_decomp (F := F) (F' := F') hle hcov (F.lattice.smul_mem μ hyF)
      ((hmem μ).not.mp hμ) hyF
    refine ⟨ν, (hmem _).mpr ?_⟩
    rw [sub_smul, one_smul, mul_smul, sub_eq_of_eq_add hzν]
    exact hz
  have hbot : 𝔪 ≠ ⊥ := by
    intro h
    apply NumberField.RingOfIntegers.not_isField K
    refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {μ} hμ => ?_⟩
    obtain ⟨ν, hν⟩ := hunit μ (by rw [h, Ideal.mem_bot]; exact hμ)
    rw [h, Ideal.mem_bot, sub_eq_zero] at hν
    exact ⟨ν, by rw [mul_comm]; exact hν.symm⟩
  have hint𝔪 : ∀ {ψ : Fin i → K}, ψ ∈ dualLattice F' → ∀ m ∈ 𝔪,
      algebraMap (𝓞 K) K m * (ψ ⬝ᵥ y) ∈ (algebraMap (𝓞 K) K).range := by
    intro ψ hψ m hm
    have := hψ _ ((hmem m).mp hm)
    rwa [dotProduct_smul, Algebra.smul_def] at this
  have hu : φc ⬝ᵥ y ∉ (algebraMap (𝓞 K) K).range := fun h => hc' (mem_dual_of hle hcov hyF hy hc h)
  have hex : ∃ m ∈ 𝔪, ∃ β : 𝓞 K, algebraMap (𝓞 K) K m * (φc ⬝ᵥ y) = algebraMap (𝓞 K) K β ∧ β ∉ 𝔪 := by
    by_contra hcon
    push Not at hcon
    let M : Submodule (𝓞 K) K := Submodule.map (Algebra.linearMap (𝓞 K) K) 𝔪
    have hint : IsIntegral (𝓞 K) (φc ⬝ᵥ y) := by
      refine isIntegral_of_smul_mem_submodule M ?_ ?_ (φc ⬝ᵥ y) ?_
      · rw [Submodule.ne_bot_iff]
        obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
        refine ⟨_, ⟨m, hm, rfl⟩, ?_⟩
        simpa using hm0
      · exact Submodule.FG.map _ (IsNoetherian.noetherian _)
      · rintro _ ⟨m, hm, rfl⟩
        obtain ⟨β, hβ⟩ := hint𝔪 hc m hm
        refine ⟨β, hcon m hm β hβ.symm, ?_⟩
        rw [Algebra.linearMap_apply, hβ, smul_eq_mul, mul_comm]
        rfl
    obtain ⟨w, hw⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
    exact hu ⟨w, hw⟩
  obtain ⟨m₁, hm₁, β, hβ, hβ𝔪⟩ := hex
  obtain ⟨ν, hν⟩ := hunit β hβ𝔪
  obtain ⟨r₀, hr₀⟩ := hint𝔪 hφ _ hν
  obtain ⟨r₁, hr₁⟩ := hint𝔪 hφ _ (𝔪.mul_mem_left ν hm₁)
  refine ⟨r₁, mem_dual_of hle hcov hyF hy (sub_mem hφ (smul_mem_dual F' r₁ hc)) ⟨r₀, ?_⟩⟩
  rw [sub_dotProduct, smul_dotProduct, smul_eq_mul]
  simp only [map_sub, map_one, map_mul] at hβ hr₀ hr₁ ⊢
  linear_combination hr₀ + (φc ⬝ᵥ y) * hr₁ + (algebraMap (𝓞 K) K ν * (φ ⬝ᵥ y)) * hβ

variable {T : Type} [Fintype T] [DecidableEq T]

def formCoord : (Fin i → K) →+ ProjField K i :=
  AddMonoidHom.mk' (fun v => algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (∑ j, C (v j) * X j))
    (by intro v w; simp [add_mul, Finset.sum_add_distrib])

/- English proof (translation)
Simplify using `only [formCoord, AddMonoidHom.mk'_apply, Pi.smul_apply, smul_eq_mul, ← map_mul, Finset.mul_sum]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [C_mul, mul_assoc]`.
-/
theorem formCoord_smul (c : K) (v : Fin i → K) :
    formCoord (c • v) = algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (C c) * formCoord v := by
  simp only [formCoord, AddMonoidHom.mk'_apply, Pi.smul_apply, smul_eq_mul, ← map_mul, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [C_mul, mul_assoc]

def IsLinAt {F' : HermLattice K i} (b' : Module.Basis T ℤ (dualLattice F')) (f : MRing (dualBlocks T))
    (v : Fin i → K) : Prop :=
  mConeMap (dualLatticeCoord b') f = C (formCoord v) * X ()

/- English proof (translation)
Simplify using `only [IsLinAt, mConeMap, aeval_X]`. Both sides reduce to the same expression.
-/
theorem isLinAt_X {F' : HermLattice K i} (b' : Module.Basis T ℤ (dualLattice F')) (s : T) :
    IsLinAt b' (X ⟨(), s⟩) (b' s) := by
  simp only [IsLinAt, mConeMap, aeval_X]
  rfl

/- English proof (translation)
Rewrite using `[IsLinAt, map_sub, hf, hg, map_sub, map_sub, sub_mul]`.
-/
theorem IsLinAt.sub {F' : HermLattice K i} {b' : Module.Basis T ℤ (dualLattice F')} {f g : MRing (dualBlocks T)}
    {v w : Fin i → K} (hf : IsLinAt b' f v) (hg : IsLinAt b' g w) : IsLinAt b' (f - g) (v - w) := by
  rw [IsLinAt, map_sub, hf, hg, map_sub, map_sub, sub_mul]

def linD (m : T → ℤ) : MRing (dualBlocks T) := ∑ s, C (m s) * X ⟨(), s⟩

/- English proof (translation)
Establish `h` using `isLinAt_X b'`. Unfold `IsLinAt at h ⊢`. Rewrite using `[linD, map_sum, map_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[← smul_eq_C_mul (X ⟨(), s⟩ : MRing (dualBlocks T)) (m s), map_zsmul, h s, map_zsmul, map_zsmul, smul_mul_assoc]`.
-/
theorem isLinAt_linD {F' : HermLattice K i} (b' : Module.Basis T ℤ (dualLattice F')) (m : T → ℤ) :
    IsLinAt b' (linD m) (∑ s, m s • (b' s : Fin i → K)) := by
  have h := isLinAt_X b'
  unfold IsLinAt at h ⊢
  rw [linD, map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← smul_eq_C_mul (X ⟨(), s⟩ : MRing (dualBlocks T)) (m s), map_zsmul, h s, map_zsmul, map_zsmul,
    smul_mul_assoc]

/- English proof (translation)
Use `show f ∈ RingHom.ker (mConeMap (dualLatticeCoord b'))`. Rewrite using `[RingHom.mem_ker]`. Rewrite `hf` using `[IsLinAt, map_zero, C_0, zero_mul]`. Conclude with `hf`.
-/
theorem mem_dualIdeal_of_isLinAt_zero {F' : HermLattice K i} {b' : Module.Basis T ℤ (dualLattice F')}
    {f : MRing (dualBlocks T)} (hf : IsLinAt b' f 0) : f ∈ dualIdeal b' := by
  show f ∈ RingHom.ker (mConeMap (dualLatticeCoord b'))
  rw [RingHom.mem_ker]
  rw [IsLinAt, map_zero, C_0, zero_mul] at hf
  exact hf

/- English proof (translation)
Use `show _ ∈ RingHom.ker (mConeMap (dualLatticeCoord b'))`. Rewrite using `[RingHom.mem_ker, map_sub, map_mul, map_mul, h₁, h₂, h₃, h₄]`. Establish `: (C (formCoord v₁) * C (formCoord v₂) : MvPolynomial Unit (ProjField K i)) = C (formCoord v₃) * C (formCoord v₄)` using `by rw [← C_mul, ← C_mul, hq]`. Take the linear combination `(X () * X () : MvPolynomial Unit (ProjField K i)) * this`.
-/
theorem mem_dualIdeal_of_isLinAt_quad {F' : HermLattice K i} {b' : Module.Basis T ℤ (dualLattice F')}
    {f₁ f₂ f₃ f₄ : MRing (dualBlocks T)} {v₁ v₂ v₃ v₄ : Fin i → K} (h₁ : IsLinAt b' f₁ v₁) (h₂ : IsLinAt b' f₂ v₂)
    (h₃ : IsLinAt b' f₃ v₃) (h₄ : IsLinAt b' f₄ v₄)
    (hq : formCoord v₁ * formCoord v₂ = formCoord v₃ * formCoord v₄) :
    f₁ * f₂ - f₃ * f₄ ∈ dualIdeal b' := by
  show _ ∈ RingHom.ker (mConeMap (dualLatticeCoord b'))
  rw [RingHom.mem_ker, map_sub, map_mul, map_mul, h₁, h₂, h₃, h₄]
  have : (C (formCoord v₁) * C (formCoord v₂) : MvPolynomial Unit (ProjField K i)) =
      C (formCoord v₃) * C (formCoord v₄) := by rw [← C_mul, ← C_mul, hq]
  linear_combination (X () * X () : MvPolynomial Unit (ProjField K i)) * this

def fstEmb : MRing (dualBlocks T) →ₐ[ℤ] MRing (stackedBlocks T) :=
  rename fun p : (Σ _ : Unit, T) => (⟨Sum.inl (), p.2⟩ : Σ k, stackedBlocks T k)

/- English proof (translation)
Establish `: (graphMap P g).comp (fstEmb (T` using `T)).toRingHom = (C : _ →+* MvPolynomial Unit _).comp (Ideal.Quotient.mk P) := by`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `n`. Simplify using `[fstEmb]`. Introduce and unpack `⟨⟨⟩, s⟩`.

Simplify using `[fstEmb, graphMap]`. Conclude with `RingHom.congr_fun this f`.
-/
theorem graphMap_fstEmb (P : Ideal (MRing (dualBlocks T))) (g : (Σ _ : Unit, T) → MRing (dualBlocks T))
    (f : MRing (dualBlocks T)) : graphMap P g (fstEmb f) = C (Ideal.Quotient.mk P f) := by
  have : (graphMap P g).comp (fstEmb (T := T)).toRingHom = (C : _ →+* MvPolynomial Unit _).comp (Ideal.Quotient.mk P) := by
    apply MvPolynomial.ringHom_ext
    · intro n
      simp [fstEmb]
    · rintro ⟨⟨⟩, s⟩
      simp [fstEmb, graphMap]
  exact RingHom.congr_fun this f

/- English proof (translation)
Use `show _ ∈ RingHom.ker _`. Rewrite using `[RingHom.mem_ker, graphMap_fstEmb, Ideal.Quotient.eq_zero_iff_mem.mpr hf, C_0]`.
-/
theorem fstEmb_mem {F' : HermLattice K i} {b' : Module.Basis T ℤ (dualLattice F')} (a : T → ℤ)
    {f : MRing (dualBlocks T)} (hf : f ∈ dualIdeal b') : fstEmb f ∈ stackedGraph b' a := by
  show _ ∈ RingHom.ker _
  rw [RingHom.mem_ker, graphMap_fstEmb, Ideal.Quotient.eq_zero_iff_mem.mpr hf, C_0]

/- English proof (translation)
Simplify using `[fstEmb, graphFirst]`.
-/
theorem fstEmb_X (s : T) : fstEmb (X ⟨(), s⟩ : MRing (dualBlocks T)) = graphFirst s := by
  simp [fstEmb, graphFirst]

/- English proof (translation)
Simplify using `[fstEmb, linD, graphFirst]`.
-/
theorem fstEmb_linD (m : T → ℤ) : fstEmb (linD m) = ∑ s, C (m s) * graphFirst s := by
  simp [fstEmb, linD, graphFirst]

/- English proof (translation)
Use `⟨fun s => b.repr ⟨φ, hφ⟩ s, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (fun x : dualLattice F => (x : Fin i → K)) (b.sum_repr ⟨φ, hφ⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at h`. Use `Eq.trans (Finset.sum_congr rfl fun s _ => ?_) h` and prove the remaining obligations. Rewrite using `[hab, mul_smul]`.
-/
theorem exists_coeff_stacked {F F' : HermLattice K i} {b : Module.Basis T ℤ (dualLattice F)}
    {b' : Module.Basis T ℤ (dualLattice F')} {a : T → ℤ} (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K))
    {φ : Fin i → K} (hφ : φ ∈ dualLattice F) :
    ∃ n : T → ℤ, ∑ s, (n s * a s) • (b' s : Fin i → K) = φ := by
  refine ⟨fun s => b.repr ⟨φ, hφ⟩ s, ?_⟩
  have h := congrArg (fun x : dualLattice F => (x : Fin i → K)) (b.sum_repr ⟨φ, hφ⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at h
  refine Eq.trans (Finset.sum_congr rfl fun s _ => ?_) h
  rw [hab, mul_smul]

/- English proof (translation)
Use `⟨fun s => b'.repr ⟨φ, hφ⟩ s, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (fun x : dualLattice F' => (x : Fin i → K)) (b'.sum_repr ⟨φ, hφ⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at h`. Conclude with `h`.
-/
theorem exists_coeff {F' : HermLattice K i} (b' : Module.Basis T ℤ (dualLattice F')) {φ : Fin i → K}
    (hφ : φ ∈ dualLattice F') : ∃ n : T → ℤ, ∑ s, n s • (b' s : Fin i → K) = φ := by
  refine ⟨fun s => b'.repr ⟨φ, hφ⟩ s, ?_⟩
  have h := congrArg (fun x : dualLattice F' => (x : Fin i → K)) (b'.sum_repr ⟨φ, hφ⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at h
  exact h

/- English proof (translation)
Establish `hΓ : stackedGraph b' a ≤ V` using `le_trans le_sup_left hV`. Establish `haX : ∀ s, C (a s) * graphFirst s ∈ V` using `fun s => hV (Ideal.mem_sup_right (Ideal.subset_span ⟨s, rfl⟩))`. Establish `hcomb : ∀ n : T → ℤ, ∑ s, C (n s * a s) * graphFirst s ∈ V` using `fun n => Ideal.sum_mem _ fun s _ => by rw [C_mul, mul_assoc]; exact V.mul_mem_left _ (haX s)`. Establish `hnd : (b' c : Fin i → K) ∉ dualLattice F`. Introduce `h`.

Take `⟨n, hn⟩` from `exists_coeff_stacked hab h`. Establish `hlin : IsLinAt b' (linD (fun s => n s * a s) - X ⟨(), c⟩) 0`. Use `(isLinAt_linD b' (fun s => n s * a s)).sub (isLinAt_X b' c)` as an intermediate fact. Rewrite `this` using `[hn, sub_self]`. Then use the resulting hypothesis. Establish `hmem` using `hΓ (fstEmb_mem a (mem_dualIdeal_of_isLinAt_zero hlin))`.

Rewrite `hmem` using `[map_sub, fstEmb_linD, fstEmb_X]`. Apply `hc` to reduce the goal to its premises. Use `V.sub_mem (hcomb n) hmem` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis. Take `⟨l, hl⟩` from `exists_sub_mem_dual hlt hcov (b' c).2 hnd (b' t).2`.

Take `⟨μ, hμ⟩` from `exists_coeff b' (smul_mem_dual F' l (b' t).2)`. Take `⟨ν, hν⟩` from `exists_coeff_stacked hab hl`. Use `set L := algebraMap (𝓞 K) K l`. Establish `h₂ : IsLinAt b' (X ⟨(), t⟩ - linD (fun s => ν s * a s)) (L • (b' c : Fin i → K))`. Use `(isLinAt_X b' t).sub (isLinAt_linD b' (fun s => ν s * a s))` as an intermediate fact.

Rewrite `this` using `[hν, sub_sub_cancel]`. Then use the resulting hypothesis. Establish `h₃ : IsLinAt b' (linD μ) (L • (b' t : Fin i → K))`. Use `isLinAt_linD b' μ` as an intermediate fact. Rewrite `this` using `[hμ]`. Then use the resulting hypothesis. Establish `hrel` using `hVW (hΓ (fstEmb_mem a (mem_dualIdeal_of_isLinAt_quad (isLinAt_X b' t) h₂ h₃ (isLinAt_X b' c) (by rw [formCoord_smul, formCoord_smul]; ring))))`.

Rewrite `hrel` using `[map_sub, map_mul, map_mul, map_sub, fstEmb_X, fstEmb_X, fstEmb_linD, fstEmb_linD]`. Establish `h2 : graphFirst t * graphFirst t ∈ W`. Use `W.add_mem (W.add_mem hrel (W.mul_mem_left (∑ s, C (μ s) * graphFirst s) hcW)) (W.mul_mem_left (graphFirst t) (hVW (hcomb ν)))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Apply the tactic sequence `rcases hW.mem_or_mem h2 with h | h <;> exact h`.
-/
theorem graphFirst_mem {F F' : HermLattice K i} (hlt : F'.lattice < F.lattice)
    (hcov : ∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice)
    {b : Module.Basis T ℤ (dualLattice F)} {b' : Module.Basis T ℤ (dualLattice F')} {a : T → ℤ}
    (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) {V W : Ideal (MRing (stackedBlocks T))}
    (hV : stackedBase b' a ≤ V) {c : T} (hc : graphFirst c ∉ V) (hVW : V ≤ W) (hcW : graphFirst c ∈ W)
    (hW : W.IsPrime) (t : T) : graphFirst t ∈ W := by
  have hΓ : stackedGraph b' a ≤ V := le_trans le_sup_left hV
  have haX : ∀ s, C (a s) * graphFirst s ∈ V := fun s =>
    hV (Ideal.mem_sup_right (Ideal.subset_span ⟨s, rfl⟩))
  have hcomb : ∀ n : T → ℤ, ∑ s, C (n s * a s) * graphFirst s ∈ V := fun n =>
    Ideal.sum_mem _ fun s _ => by rw [C_mul, mul_assoc]; exact V.mul_mem_left _ (haX s)

  have hnd : (b' c : Fin i → K) ∉ dualLattice F := by
    intro h
    obtain ⟨n, hn⟩ := exists_coeff_stacked hab h
    have hlin : IsLinAt b' (linD (fun s => n s * a s) - X ⟨(), c⟩) 0 := by
      have := (isLinAt_linD b' (fun s => n s * a s)).sub (isLinAt_X b' c)
      rwa [hn, sub_self] at this
    have hmem := hΓ (fstEmb_mem a (mem_dualIdeal_of_isLinAt_zero hlin))
    rw [map_sub, fstEmb_linD, fstEmb_X] at hmem
    apply hc
    have := V.sub_mem (hcomb n) hmem
    rwa [sub_sub_cancel] at this
  obtain ⟨l, hl⟩ := exists_sub_mem_dual hlt hcov (b' c).2 hnd (b' t).2
  obtain ⟨μ, hμ⟩ := exists_coeff b' (smul_mem_dual F' l (b' t).2)
  obtain ⟨ν, hν⟩ := exists_coeff_stacked hab hl
  set L := algebraMap (𝓞 K) K l
  have h₂ : IsLinAt b' (X ⟨(), t⟩ - linD (fun s => ν s * a s)) (L • (b' c : Fin i → K)) := by
    have := (isLinAt_X b' t).sub (isLinAt_linD b' (fun s => ν s * a s))
    rwa [hν, sub_sub_cancel] at this
  have h₃ : IsLinAt b' (linD μ) (L • (b' t : Fin i → K)) := by
    have := isLinAt_linD b' μ
    rwa [hμ] at this
  have hrel := hVW (hΓ (fstEmb_mem a (mem_dualIdeal_of_isLinAt_quad (isLinAt_X b' t) h₂ h₃ (isLinAt_X b' c)
    (by rw [formCoord_smul, formCoord_smul]; ring))))
  rw [map_sub, map_mul, map_mul, map_sub, fstEmb_X, fstEmb_X, fstEmb_linD, fstEmb_linD] at hrel
  have h2 : graphFirst t * graphFirst t ∈ W := by
    have := W.add_mem (W.add_mem hrel (W.mul_mem_left (∑ s, C (μ s) * graphFirst s) hcW))
      (W.mul_mem_left (graphFirst t) (hVW (hcomb ν)))
    convert this using 1
    ring
  rcases hW.mem_or_mem h2 with h | h <;> exact h

/- English proof (translation)
Use extensionality with `W`. Simplify using `only [Set.mem_empty_iff_false, iff_false]`. Introduce and unpack `⟨hmin, hrel⟩`. Take `⟨⟨hWp, hle⟩, -⟩` from `hmin`. Take `⟨t, ht⟩` from `hrel (Sum.inl ())`.

Conclude with `ht (graphFirst_mem hlt hcov hab hV hc (le_trans le_sup_left hle) (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))) hWp t)`.
-/
theorem divSupp_first_eq_empty {F F' : HermLattice K i} (hlt : F'.lattice < F.lattice)
    (hcov : ∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice)
    {b : Module.Basis T ℤ (dualLattice F)} {b' : Module.Basis T ℤ (dualLattice F')} {a : T → ℤ}
    (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) {V : Ideal (MRing (stackedBlocks T))}
    (hV : stackedBase b' a ≤ V) {c : T} (hc : graphFirst c ∉ V) : divSupp V (graphFirst c) = ∅ := by
  ext W
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hmin, hrel⟩
  obtain ⟨⟨hWp, hle⟩, -⟩ := hmin
  obtain ⟨t, ht⟩ := hrel (Sum.inl ())
  exact ht (graphFirst_mem hlt hcov hab hV hc (le_trans le_sup_left hle)
    (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))) hWp t)

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => rintro V d - ⟨j, -⟩`. Conclude with `j.elim0`. Consider the case `succ n ih`.

Introduce and unpack `V d hEV ⟨j, hj⟩`. Rewrite using `[geoNum]`. Use `split_ifs with h`. Rewrite using `[Fintype.sum_sum_type]`. Establish `h1 : ∀ u : Unit, divSupp V (X ⟨Sum.inl u, (h (Sum.inl u)).choose⟩ : MRing (stackedBlocks T)) = ∅`.

Introduce and unpack `⟨⟩`. Conclude with `divSupp_first_eq_empty hlt hcov hab (le_trans hE hEV) (h (Sum.inl ())).choose_spec`. Rewrite using `[Finset.sum_eq_zero (fun u _ => by rw [h1 u, finsum_mem_empty, mul_zero]), zero_add]`. Use `Finset.sum_eq_zero fun u _ => ?_` and prove the remaining obligations. Take `⟨⟩` from `u`.

Distinguish the cases in `hl : d (Fin.last n) (Sum.inr ()) = 0`. Rewrite using `[hl, zero_mul]`. Take `⟨j', rfl⟩` from `Fin.exists_castSucc_eq.mpr (fun e => hl (e ▸ hj))`. Use `mul_eq_zero_of_right _ (finsum_mem_of_eqOn_zero fun W hW => ?_)` and prove the remaining obligations. Establish `hVW : V ≤ W` using `le_trans le_sup_left hW.1.1.2`.

Rewrite using `[ih W (Fin.init d) (le_trans hEV hVW) ⟨j', by rw [Fin.init]; exact hj⟩, mul_zero]`. Both sides reduce to the same expression. Both sides reduce to the same expression.
-/
theorem geoNum_eq_zero {F F' : HermLattice K i} (hlt : F'.lattice < F.lattice)
    (hcov : ∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice)
    {b : Module.Basis T ℤ (dualLattice F)} {b' : Module.Basis T ℤ (dualLattice F')} {a : T → ℤ}
    (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) {E : Ideal (MRing (stackedBlocks T))}
    (hE : stackedBase b' a ≤ E) :
    ∀ (n : ℕ) (V : Ideal (MRing (stackedBlocks T))) (d : Fin n → Unit ⊕ Unit → ℤ), E ≤ V →
      (∃ j, d j (Sum.inr ()) = 0) → geoNum n V d = 0 := by
  intro n
  induction n with
  | zero => rintro V d - ⟨j, -⟩; exact j.elim0
  | succ n ih =>
    rintro V d hEV ⟨j, hj⟩
    rw [geoNum]
    split_ifs with h
    · rw [Fintype.sum_sum_type]
      have h1 : ∀ u : Unit, divSupp V (X ⟨Sum.inl u, (h (Sum.inl u)).choose⟩ : MRing (stackedBlocks T)) = ∅ := by
        rintro ⟨⟩
        exact divSupp_first_eq_empty hlt hcov hab (le_trans hE hEV) (h (Sum.inl ())).choose_spec
      rw [Finset.sum_eq_zero (fun u _ => by rw [h1 u, finsum_mem_empty, mul_zero]), zero_add]
      refine Finset.sum_eq_zero fun u _ => ?_
      obtain ⟨⟩ := u
      by_cases hl : d (Fin.last n) (Sum.inr ()) = 0
      · rw [hl, zero_mul]
      · obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.mpr (fun e => hl (e ▸ hj))
        refine mul_eq_zero_of_right _ (finsum_mem_of_eqOn_zero fun W hW => ?_)
        have hVW : V ≤ W := le_trans le_sup_left hW.1.1.2
        rw [ih W (Fin.init d) (le_trans hEV hVW) ⟨j', by rw [Fin.init]; exact hj⟩, mul_zero]
        rfl
    · rfl

end StackedExceptionalFirstGeometric

open StackedExceptionalFirstGeometric in

/- English proof (translation)
Introduce `K _ _ i F F' T _ _ b b' a _ hlt hcov hab E hE d _ ⟨j, hj⟩`. Conclude with `geoNum_eq_zero hlt hcov hab hE.1.1.2 (i - 1) E d le_rfl ⟨j, by rw [hj, degFirst_inr]⟩`.
-/
theorem DualStackedExcGeoFirst.proof : DualStackedExcGeoFirst.Statement := by
  intro K _ _ i F F' T _ _ b b' a _ hlt hcov hab E hE d _ ⟨j, hj⟩
  exact geoNum_eq_zero hlt hcov hab hE.1.1.2 (i - 1) E d le_rfl ⟨j, by rw [hj, degFirst_inr]⟩

end

end GroundTheory.Heights₂.Heights
