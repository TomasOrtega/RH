import Mathlib
import Formalism.HermitianLattices.StatementLat
import Formalism.SizeWindowBrackets.SlopesHypothesisFinitePlaces

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

variable {K : Type} [Field K] [NumberField K]

def plEquiv (K : Type) [Field K] [NumberField K] :
    HeightOneSpectrum (𝓞 K) ≃ Formalism.LFunctionChainParameters.slopeLatticeData.FinPl K where
  toFun w := ⟨w.asIdeal, w.isMaximal⟩
  invFun p := ⟨p.1, p.2.isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField p.2 (RingOfIntegers.not_isField K)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem plEquiv_val (w : HeightOneSpectrum (𝓞 K)) : (plEquiv K w).1 = w.asIdeal := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem plEquiv_symm_asIdeal (p : Formalism.LFunctionChainParameters.slopeLatticeData.FinPl K) :
    ((plEquiv K).symm p).asIdeal = p.1 := rfl

def prW (w : HeightOneSpectrum (𝓞 K)) : ℕ := Ideal.absNorm (w.asIdeal.under ℤ)

def eW (w : HeightOneSpectrum (𝓞 K)) : ℕ := w.asIdeal.ramificationIdx ℤ

def lW (w : HeightOneSpectrum (𝓞 K)) : ℝ :=
  Real.log (Ideal.absNorm w.asIdeal : ℝ) / (Module.finrank ℚ K : ℝ)

def IsUnifW (w : HeightOneSpectrum (𝓞 K)) (ϖ : 𝓞 K) : Prop := ϖ ∈ w.asIdeal ∧ ϖ ∉ w.asIdeal ^ 2

abbrev Ow (w : HeightOneSpectrum (𝓞 K)) : Type := Localization.AtPrime w.asIdeal

instance owDVR (w : HeightOneSpectrum (𝓞 K)) : IsDiscreteValuationRing (Ow w) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) w.ne_bot _

def owToK (w : HeightOneSpectrum (𝓞 K)) : Ow w →+* K :=
  IsLocalization.lift (M := w.asIdeal.primeCompl) (g := algebraMap (𝓞 K) K) (fun y => by
    refine IsUnit.mk0 _ ?_
    intro h
    have h0 : (y : 𝓞 K) = 0 := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      rw [h, map_zero]
    exact y.2 (h0 ▸ w.asIdeal.zero_mem))

instance owAlgebra (w : HeightOneSpectrum (𝓞 K)) : Algebra (Ow w) K := (owToK w).toAlgebra

instance owTower (w : HeightOneSpectrum (𝓞 K)) : IsScalarTower (𝓞 K) (Ow w) K :=
  IsScalarTower.of_algebraMap_eq (fun x => (IsLocalization.lift_eq _ x).symm)

instance owFrac (w : HeightOneSpectrum (𝓞 K)) : IsFractionRing (Ow w) K :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization w.asIdeal.primeCompl (Ow w) K

section Mod
variable (w : HeightOneSpectrum (𝓞 K)) (V : Type) [AddCommGroup V] [Module K V]

@[reducible] def owModule : Module (Ow w) V := Module.compHom V (algebraMap (Ow w) K)

scoped instance (priority := 90) owModuleInst : Module (Ow w) V := owModule w V

scoped instance owTowerK : IsScalarTower (Ow w) K V :=
  ⟨fun r a x => by
    show (r • a) • x = algebraMap (Ow w) K r • (a • x)
    rw [Algebra.smul_def, mul_smul]⟩

scoped instance owTowerO [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] :
    IsScalarTower (𝓞 K) (Ow w) V :=
  ⟨fun r s x => by
    show algebraMap (Ow w) K (r • s) • x = r • (algebraMap (Ow w) K s • x)
    rw [Algebra.smul_def, map_mul, mul_smul, ← IsScalarTower.algebraMap_apply, algebraMap_smul]⟩

variable {V} in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ow_smul_def (r : Ow w) (x : V) : r • x = algebraMap (Ow w) K r • x := rfl

end Mod

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def atW (w : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) V) : Submodule (Ow w) V :=
  Submodule.span (Ow w) (L : Set V)

def scalW (w : HeightOneSpectrum (𝓞 K)) (c : K) (L : Submodule (𝓞 K) V) : Submodule (Ow w) V :=
  (atW w L).map ((c • (LinearMap.id : V →ₗ[K] V)).restrictScalars (Ow w))

def lenW (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) : ℕ∞ :=
  Module.length (Ow w) (atW w A ⧸ (atW w B).comap (atW w A).subtype)

def lidxW (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) : ℤ :=
  ((lenW w A (A ⊓ B)).toNat : ℤ) - ((lenW w B (A ⊓ B)).toNat : ℤ)

def lenUW (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) : ℚ :=
  ((lenW w A B).toNat : ℚ) / (eW w : ℚ)

def lidxUW (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) : ℚ :=
  (lidxW w A B : ℚ) / (eW w : ℚ)

/- English proof (translation)
Rewrite using `[← algebraMap_smul (Ow w) (t : 𝓞 K), smul_smul, IsLocalization.mk'_spec', algebraMap_smul]`.
-/
theorem mk'_smul (w : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) (t : w.asIdeal.primeCompl) (x : V) :
    (t : 𝓞 K) • ((IsLocalization.mk' (Ow w) a t) • x) = a • x := by
  rw [← algebraMap_smul (Ow w) (t : 𝓞 K), smul_smul, IsLocalization.mk'_spec', algebraMap_smul]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simpa using hx⟩`. Consider the case `zero => exact ⟨1, fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨s, hs, hx⟩` from `hx`. Take `⟨t, ht, hy⟩` from `hy`. Use `⟨s * t, fun h => (w.isPrime.mem_or_mem h).elim hs ht, ?_⟩` and prove the remaining obligations. Establish `e : (s * t) • (x + y) = t • (s • x) + s • (t • y)`.

Rewrite using `[smul_add, mul_smul, smul_comm s t x, mul_smul]`. Rewrite using `[e]`. Conclude with `L.add_mem (L.smul_mem t hx) (L.smul_mem s hy)`. Consider the case `smul r x _ hx`. Take `⟨s, hs, hx⟩` from `hx`.

Take `⟨a, t, rfl⟩` from `IsLocalization.exists_mk'_eq w.asIdeal.primeCompl r`. Use `⟨s * t, fun h => (w.isPrime.mem_or_mem h).elim hs t.2, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul, mk'_smul, smul_comm]`. Conclude with `L.smul_mem a hx`. Introduce and unpack `⟨s, hs, hx⟩`.

Establish `h1 : x = (IsLocalization.mk' (Ow w) (1 : 𝓞 K) (⟨s, hs⟩ : w.asIdeal.primeCompl)) • (s • x)`. Rewrite using `[smul_comm]`. Use `mk'_smul w 1 (⟨s, hs⟩ : w.asIdeal.primeCompl) x` as an intermediate fact. Rewrite `this` using `[one_smul]`. Conclude with `this.symm`.

Rewrite using `[h1]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hx)`.
-/
theorem mem_atW_iff {w : HeightOneSpectrum (𝓞 K)} {L : Submodule (𝓞 K) V} {x : V} :
    x ∈ atW w L ↔ ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • x ∈ L := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact ⟨1, fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simpa using hx⟩
    | zero => exact ⟨1, fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs, hx⟩ := hx
      obtain ⟨t, ht, hy⟩ := hy
      refine ⟨s * t, fun h => (w.isPrime.mem_or_mem h).elim hs ht, ?_⟩
      have e : (s * t) • (x + y) = t • (s • x) + s • (t • y) := by
        rw [smul_add, mul_smul, smul_comm s t x, mul_smul]
      rw [e]
      exact L.add_mem (L.smul_mem t hx) (L.smul_mem s hy)
    | smul r x _ hx =>
      obtain ⟨s, hs, hx⟩ := hx
      obtain ⟨a, t, rfl⟩ := IsLocalization.exists_mk'_eq w.asIdeal.primeCompl r
      refine ⟨s * t, fun h => (w.isPrime.mem_or_mem h).elim hs t.2, ?_⟩
      rw [mul_smul, mk'_smul, smul_comm]
      exact L.smul_mem a hx
  · rintro ⟨s, hs, hx⟩
    have h1 : x = (IsLocalization.mk' (Ow w) (1 : 𝓞 K) (⟨s, hs⟩ : w.asIdeal.primeCompl)) • (s • x) := by
      rw [smul_comm]
      have := mk'_smul w 1 (⟨s, hs⟩ : w.asIdeal.primeCompl) x
      rw [one_smul] at this
      exact this.symm
    rw [h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hx)

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[Submodule.restrictScalars_mem, mem_atW_iff]`. Both sides reduce to the same expression.
-/
theorem atW_restrictScalars (w : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) V) :
    (atW w L).restrictScalars (𝓞 K) = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L := by
  ext x
  rw [Submodule.restrictScalars_mem, mem_atW_iff]
  rfl

/- English proof (translation)
Introduce `_ hx` and use `Submodule.subset_span hx`.
-/
theorem le_atW (w : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) V) :
    L ≤ (atW w L).restrictScalars (𝓞 K) := fun _ hx => Submodule.subset_span hx

/- English proof (translation)
The claim follows from `Submodule.span_mono h`.
-/
theorem atW_mono (w : HeightOneSpectrum (𝓞 K)) {A B : Submodule (𝓞 K) V} (h : A ≤ B) :
    atW w A ≤ atW w B := Submodule.span_mono h

/- English proof (translation)
Simplify using `[atW]`.
-/
@[simp] theorem atW_bot (w : HeightOneSpectrum (𝓞 K)) : atW w (⊥ : Submodule (𝓞 K) V) = ⊥ := by
  simp [atW]

/- English proof (translation)
Simplify using `[atW]`.
-/
@[simp] theorem atW_top (w : HeightOneSpectrum (𝓞 K)) : atW w (⊤ : Submodule (𝓞 K) V) = ⊤ := by
  simp [atW]

/- English proof (translation)
Apply `le_antisymm (le_inf (atW_mono w inf_le_left) (atW_mono w inf_le_right))` to reduce the goal to its premises. Introduce and unpack `x ⟨hA, hB⟩`. Take `⟨s, hs, hx⟩` from `mem_atW_iff.1 hA`. Take `⟨t, ht, hy⟩` from `mem_atW_iff.1 hB`. Use `mem_atW_iff.2 ⟨s * t, fun h => (w.isPrime.mem_or_mem h).elim hs ht, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `A.smul_mem t hx`. Rewrite using `[mul_smul]`. Conclude with `B.smul_mem s hy`.
-/
theorem atW_inf (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) :
    atW w (A ⊓ B) = atW w A ⊓ atW w B := by
  apply le_antisymm (le_inf (atW_mono w inf_le_left) (atW_mono w inf_le_right))
  rintro x ⟨hA, hB⟩
  obtain ⟨s, hs, hx⟩ := mem_atW_iff.1 hA
  obtain ⟨t, ht, hy⟩ := mem_atW_iff.1 hB
  refine mem_atW_iff.2 ⟨s * t, fun h => (w.isPrime.mem_or_mem h).elim hs ht, ?_, ?_⟩
  · rw [mul_comm, mul_smul]; exact A.smul_mem t hx
  · rw [mul_smul]; exact B.smul_mem s hy

/- English proof (translation)
Unfold `atW`. Rewrite using `[Submodule.map_span]`. Both sides reduce to the same expression.
-/
theorem atW_map {V' : Type} [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V']
    [IsScalarTower (𝓞 K) K V'] (w : HeightOneSpectrum (𝓞 K)) (f : V →ₗ[K] V')
    (L : Submodule (𝓞 K) V) :
    atW w (L.map (f.restrictScalars (𝓞 K))) = (atW w L).map (f.restrictScalars (Ow w)) := by
  unfold atW
  rw [Submodule.map_span]
  rfl

/- English proof (translation)
Take `⟨s, rfl⟩` from `h`. Use `⟨s, ?_⟩` and prove the remaining obligations. Unfold `atW`. Conclude with `(Submodule.span_span_of_tower (𝓞 K) (Ow w) (s : Set V)).symm`.
-/
theorem atW_fg (w : HeightOneSpectrum (𝓞 K)) {L : Submodule (𝓞 K) V} (h : L.FG) : (atW w L).FG := by
  obtain ⟨s, rfl⟩ := h
  refine ⟨s, ?_⟩
  unfold atW
  exact (Submodule.span_span_of_tower (𝓞 K) (Ow w) (s : Set V)).symm

/- English proof (translation)
Unfold `scalW`. Rewrite using `[one_smul]`. Conclude with `Submodule.map_id _`.
-/
theorem scalW_one (w : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) V) : scalW w 1 L = atW w L := by
  unfold scalW
  rw [one_smul]
  exact Submodule.map_id _

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_scalW_iff {w : HeightOneSpectrum (𝓞 K)} {c : K} {L : Submodule (𝓞 K) V} {x : V} :
    x ∈ scalW w c L ↔ ∃ y ∈ atW w L, c • y = x := Iff.rfl

/- English proof (translation)
Unfold `scalW atW Formalism.LFunctionChainParameters.slopeLatticeData.locScal`. Rewrite using `[Submodule.map_span]`. Both sides reduce to the same expression.
-/
theorem scalW_eq_locScal (w : HeightOneSpectrum (𝓞 K)) (c : K) (L : Submodule (𝓞 K) V) :
    scalW w c L = @Formalism.LFunctionChainParameters.slopeLatticeData.locScal K V _ _ _ _ _ (plEquiv K w) (owModule w V) c L := by
  unfold scalW atW Formalism.LFunctionChainParameters.slopeLatticeData.locScal
  rw [Submodule.map_span]
  rfl

@[reducible] def rlocModule (V : Type) [AddCommGroup V] [Module K V] (p : Formalism.LFunctionChainParameters.slopeLatticeData.FinPl K) :
    Module (Formalism.LFunctionChainParameters.slopeLatticeData.Rloc p) V := owModule ((plEquiv K).symm p) V

/- English proof (translation)
Introduce `x hx`. Set `I : Ideal (𝓞 K)` to `B.colon {x}`. Assume the negation of the conclusion as `hxB`. Establish `hI : I ≠ ⊤`. Introduce `hI`.

Establish `h1 : (1 : 𝓞 K) ∈ I` using `by rw [hI]; trivial`. Rewrite `h1` using `[Submodule.mem_colon_singleton]`. Conclude with `hxB (by simpa using h1)`. Take `⟨m, hm, hIm⟩` from `Ideal.exists_le_maximal I hI`. Take `⟨s, hs, hsx⟩` from `mem_atW_iff.1 (h ((plEquiv K).symm ⟨m, hm⟩) (Submodule.subset_span hx))`.

Conclude with `hs (hIm (Submodule.mem_colon_singleton.2 hsx))`.
-/
theorem le_of_atW_le {A B : Submodule (𝓞 K) V}
    (h : ∀ w : HeightOneSpectrum (𝓞 K), atW w A ≤ atW w B) : A ≤ B := by
  intro x hx
  let I : Ideal (𝓞 K) := B.colon {x}
  by_contra hxB
  have hI : I ≠ ⊤ := by
    intro hI
    have h1 : (1 : 𝓞 K) ∈ I := by rw [hI]; trivial
    rw [Submodule.mem_colon_singleton] at h1
    exact hxB (by simpa using h1)
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨s, hs, hsx⟩ := mem_atW_iff.1 (h ((plEquiv K).symm ⟨m, hm⟩) (Submodule.subset_span hx))
  exact hs (hIm (Submodule.mem_colon_singleton.2 hsx))

/- English proof (translation)
The claim follows from `IsFractionRing.injective (Ow w) K`.
-/
theorem algebraMap_ow_injective (w : HeightOneSpectrum (𝓞 K)) :
    Function.Injective (algebraMap (Ow w) K) := IsFractionRing.injective (Ow w) K

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, rfl⟩`. Take `⟨a, t, rfl⟩` from `IsLocalization.exists_mk'_eq w.asIdeal.primeCompl r`. Establish `h1 : algebraMap (Ow w) K (IsLocalization.mk' (Ow w) a t) * algebraMap (𝓞 K) K (t : 𝓞 K) = algebraMap (𝓞 K) K a`. Rewrite using `[IsScalarTower.algebraMap_apply (𝓞 K) (Ow w) K, ← map_mul, IsLocalization.mk'_spec, ← IsScalarTower.algebraMap_apply]`.

Establish `h2` using `congrArg (w.valuation K) h1`. Rewrite `h2` using `[map_mul, (w.valuation_eq_one_iff_notMem (K := K)).2 t.2, mul_one]`. Rewrite using `[h2]`. Conclude with `w.valuation_le_one a`. Introduce `hx`.

Take `⟨n, d, h⟩` from `w.exists_primeCompl_mul_eq_of_integer x hx`. Use `⟨IsLocalization.mk' (Ow w) n d, ?_⟩` and prove the remaining obligations. Establish `hd : algebraMap (𝓞 K) K (d : 𝓞 K) ≠ 0`. Introduce `h0`. Establish `: (d : 𝓞 K) = 0` using `FaithfulSMul.algebraMap_injective (𝓞 K) K (by rw [h0, map_zero])`.

Conclude with `d.2 (this ▸ w.asIdeal.zero_mem)`. Apply `mul_right_cancel₀ hd` to reduce the goal to its premises. Rewrite using `[h, IsScalarTower.algebraMap_apply (𝓞 K) (Ow w) K, ← map_mul, IsLocalization.mk'_spec, ← IsScalarTower.algebraMap_apply]`.
-/
theorem mem_range_ow_iff (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    x ∈ (algebraMap (Ow w) K).range ↔ w.valuation K x ≤ 1 := by
  constructor
  · rintro ⟨r, rfl⟩
    obtain ⟨a, t, rfl⟩ := IsLocalization.exists_mk'_eq w.asIdeal.primeCompl r
    have h1 : algebraMap (Ow w) K (IsLocalization.mk' (Ow w) a t) * algebraMap (𝓞 K) K (t : 𝓞 K)
        = algebraMap (𝓞 K) K a := by
      rw [IsScalarTower.algebraMap_apply (𝓞 K) (Ow w) K, ← map_mul, IsLocalization.mk'_spec,
        ← IsScalarTower.algebraMap_apply]
    have h2 := congrArg (w.valuation K) h1
    rw [map_mul, (w.valuation_eq_one_iff_notMem (K := K)).2 t.2, mul_one] at h2
    rw [h2]
    exact w.valuation_le_one a
  · intro hx
    obtain ⟨n, d, h⟩ := w.exists_primeCompl_mul_eq_of_integer x hx
    refine ⟨IsLocalization.mk' (Ow w) n d, ?_⟩
    have hd : algebraMap (𝓞 K) K (d : 𝓞 K) ≠ 0 := by
      intro h0
      have : (d : 𝓞 K) = 0 := FaithfulSMul.algebraMap_injective (𝓞 K) K (by rw [h0, map_zero])
      exact d.2 (this ▸ w.asIdeal.zero_mem)
    apply mul_right_cancel₀ hd
    rw [h, IsScalarTower.algebraMap_apply (𝓞 K) (Ow w) K, ← map_mul, IsLocalization.mk'_spec,
      ← IsScalarTower.algebraMap_apply]

/- English proof (translation)
Take `⟨x, hx, hx'⟩` from `Ideal.exists_mem_pow_notMem_pow_succ w.asIdeal w.ne_bot w.isPrime.ne_top 1`. Conclude with `⟨x, by simpa using hx, hx'⟩`.
-/
theorem exists_isUnifW (w : HeightOneSpectrum (𝓞 K)) : ∃ ϖ : 𝓞 K, IsUnifW w ϖ := by
  obtain ⟨x, hx, hx'⟩ := Ideal.exists_mem_pow_notMem_pow_succ w.asIdeal w.ne_bot w.isPrime.ne_top 1
  exact ⟨x, by simpa using hx, hx'⟩

/- English proof (translation)
The claim follows from `(Localization.AtPrime.map_eq_maximalIdeal).symm`.
-/
theorem maximalIdeal_ow (w : HeightOneSpectrum (𝓞 K)) :
    IsLocalRing.maximalIdeal (Ow w) = w.asIdeal.map (algebraMap (𝓞 K) (Ow w)) :=
  (Localization.AtPrime.map_eq_maximalIdeal).symm

/- English proof (translation)
Rewrite using `[maximalIdeal_ow, ← Ideal.map_pow]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨⟨b, s⟩, hbs⟩` from `(IsLocalization.mem_map_algebraMap_iff w.asIdeal.primeCompl (Ow w)).1 h`. Establish `h1 : a * (s : 𝓞 K) = (b : 𝓞 K)` using `IsLocalization.injective (Ow w) w.asIdeal.primeCompl_le_nonZeroDivisors (by simpa using hbs)`.

Establish `h2 : (s : 𝓞 K) * a ∈ w.asIdeal ^ n` using `by rw [mul_comm, h1]; exact b.2`. Conclude with `(Ideal.IsPrime.mul_mem_pow w.asIdeal h2).resolve_left s.2`. Conclude with `Ideal.mem_map_of_mem _`.
-/
theorem algebraMap_mem_maximalIdeal_pow_iff (w : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) (n : ℕ) :
    algebraMap (𝓞 K) (Ow w) a ∈ IsLocalRing.maximalIdeal (Ow w) ^ n ↔ a ∈ w.asIdeal ^ n := by
  rw [maximalIdeal_ow, ← Ideal.map_pow]
  constructor
  · intro h
    obtain ⟨⟨b, s⟩, hbs⟩ := (IsLocalization.mem_map_algebraMap_iff w.asIdeal.primeCompl (Ow w)).1 h
    have h1 : a * (s : 𝓞 K) = (b : 𝓞 K) :=
      IsLocalization.injective (Ow w) w.asIdeal.primeCompl_le_nonZeroDivisors (by simpa using hbs)
    have h2 : (s : 𝓞 K) * a ∈ w.asIdeal ^ n := by rw [mul_comm, h1]; exact b.2
    exact (Ideal.IsPrime.mul_mem_pow w.asIdeal h2).resolve_left s.2
  · exact Ideal.mem_map_of_mem _

/- English proof (translation)
Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible (Ow w)`. Establish `hm : IsLocalRing.maximalIdeal (Ow w) = Ideal.span {π}` using `hπ.maximalIdeal_eq`. Establish `h1 : algebraMap (𝓞 K) (Ow w) ϖ ∈ IsLocalRing.maximalIdeal (Ow w)`. Simplify `h.1)` using `using (algebraMap_mem_maximalIdeal_pow_iff w ϖ 1).2 (by simpa`. Establish `h2 : algebraMap (𝓞 K) (Ow w) ϖ ∉ IsLocalRing.maximalIdeal (Ow w) ^ 2` using `fun h' => h.2 ((algebraMap_mem_maximalIdeal_pow_iff w ϖ 2).1 h')`.

Establish `h0 : algebraMap (𝓞 K) (Ow w) ϖ ≠ 0` using `fun h' => h2 (h' ▸ Ideal.zero_mem _)`. Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hπ`. Break down `n with _ | _ | n` into its components or cases. It suffices to derive a contradiction. Rewrite `hu` using `[pow_zero, mul_one]`.

Conclude with `(IsLocalRing.mem_maximalIdeal _).1 h1 (hu ▸ u.isUnit)`. Rewrite using `[hu, zero_add, pow_one]`. Conclude with `(irreducible_units_mul u).2 hπ`. It suffices to derive a contradiction. Apply `h2` to reduce the goal to its premises.

Rewrite using `[hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hu]`. Conclude with `⟨u * π ^ n, by ring⟩`.
-/
theorem IsUnifW.irreducible {w : HeightOneSpectrum (𝓞 K)} {ϖ : 𝓞 K} (h : IsUnifW w ϖ) :
    Irreducible (algebraMap (𝓞 K) (Ow w) ϖ) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Ow w)
  have hm : IsLocalRing.maximalIdeal (Ow w) = Ideal.span {π} := hπ.maximalIdeal_eq
  have h1 : algebraMap (𝓞 K) (Ow w) ϖ ∈ IsLocalRing.maximalIdeal (Ow w) := by
    simpa using (algebraMap_mem_maximalIdeal_pow_iff w ϖ 1).2 (by simpa using h.1)
  have h2 : algebraMap (𝓞 K) (Ow w) ϖ ∉ IsLocalRing.maximalIdeal (Ow w) ^ 2 :=
    fun h' => h.2 ((algebraMap_mem_maximalIdeal_pow_iff w ϖ 2).1 h')
  have h0 : algebraMap (𝓞 K) (Ow w) ϖ ≠ 0 := fun h' => h2 (h' ▸ Ideal.zero_mem _)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hπ
  rcases n with _ | _ | n
  · exfalso
    rw [pow_zero, mul_one] at hu
    exact (IsLocalRing.mem_maximalIdeal _).1 h1 (hu ▸ u.isUnit)
  · rw [hu, zero_add, pow_one]
    exact (irreducible_units_mul u).2 hπ
  · exfalso
    apply h2
    rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hu]
    exact ⟨u * π ^ n, by ring⟩

/- English proof (translation)
Establish `: NeZero w.asIdeal` using `⟨w.ne_bot⟩`. Conclude with `Nat.absNorm_under_prime w.asIdeal`.
-/
theorem prW_prime (w : HeightOneSpectrum (𝓞 K)) : (prW w).Prime := by
  have : NeZero w.asIdeal := ⟨w.ne_bot⟩
  exact Nat.absNorm_under_prime w.asIdeal

/- English proof (translation)
Establish `h` using `Ideal.absNorm_mem (w.asIdeal.under ℤ)`. Establish `h2` using `Ideal.mem_comap.1 h`. Simplify `h2` using `[prW]`.
-/
theorem natCast_prW_mem (w : HeightOneSpectrum (𝓞 K)) : ((prW w : ℕ) : 𝓞 K) ∈ w.asIdeal := by
  have h := Ideal.absNorm_mem (w.asIdeal.under ℤ)
  have h2 := Ideal.mem_comap.1 h
  simpa [prW] using h2

/- English proof (translation)
Establish `h1 : ((q : ℕ) : ℤ) ∈ w.asIdeal.under ℤ`. Rewrite using `[Ideal.under, Ideal.mem_comap]`. Simplify using `using h`. Rewrite `h1` using `[← Int.ideal_span_absNorm_eq_self (w.asIdeal.under ℤ), Ideal.mem_span_singleton]`. Establish `h2 : prW w ∣ q` using `by unfold prW; exact_mod_cast h1`.

Conclude with `((Nat.prime_dvd_prime_iff_eq (prW_prime w) hq).1 h2).symm`.
-/
theorem eq_prW_of_mem (w : HeightOneSpectrum (𝓞 K)) {q : ℕ} (hq : q.Prime)
    (h : ((q : ℕ) : 𝓞 K) ∈ w.asIdeal) : q = prW w := by
  have h1 : ((q : ℕ) : ℤ) ∈ w.asIdeal.under ℤ := by
    rw [Ideal.under, Ideal.mem_comap]; simpa using h
  rw [← Int.ideal_span_absNorm_eq_self (w.asIdeal.under ℤ), Ideal.mem_span_singleton] at h1
  have h2 : prW w ∣ q := by unfold prW; exact_mod_cast h1
  exact ((Nat.prime_dvd_prime_iff_eq (prW_prime w) hq).1 h2).symm

/- English proof (translation)
The claim follows from `Ideal.ramificationIdx_pos _ _`.
-/
theorem eW_pos (w : HeightOneSpectrum (𝓞 K)) : 0 < eW w := Ideal.ramificationIdx_pos _ _

/- English proof (translation)
Introduce `h`. Use `congrArg (algebraMap (Ow w) K) h` as an intermediate fact. Rewrite `this` using `[map_natCast, map_zero]`. Conclude with `hn (by exact_mod_cast this)`.
-/
theorem natCast_ow_ne_zero (w : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : n ≠ 0) : (n : Ow w) ≠ 0 := by
  intro h
  have := congrArg (algebraMap (Ow w) K) h
  rw [map_natCast, map_zero] at this
  exact hn (by exact_mod_cast this)

/- English proof (translation)
Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (natCast_ow_ne_zero w (prW_prime w).ne_zero) hϖ`. Establish `hspan : (w.asIdeal.under ℤ).map (algebraMap ℤ (Ow w)) = IsLocalRing.maximalIdeal (Ow w) ^ n`. Rewrite using `[← Int.ideal_span_absNorm_eq_self (w.asIdeal.under ℤ), Ideal.map_span, Set.image_singleton, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]`. Establish `: algebraMap ℤ (Ow w) ((Ideal.absNorm (w.asIdeal.under ℤ) : ℕ) : ℤ) = ((prW w : ℕ) : Ow w)`. Simplify using `[prW]`.

Rewrite using `[this, hu]`. Conclude with `Ideal.span_singleton_eq_span_singleton.2 ⟨u⁻¹, by`. Rewrite using `[mul_comm (u : Ow w), mul_assoc, Units.mul_inv, mul_one]⟩`. Establish `he : eW w = n`. Unfold `eW`.

Rewrite using `[Ideal.ramificationIdx_def, hspan, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal, ENat.toNat_natCast]`. Conclude with `⟨u, by rw [he, hu]⟩`.
-/
theorem prW_eq_unit_mul_pow (w : HeightOneSpectrum (𝓞 K)) {ϖ : Ow w} (hϖ : Irreducible ϖ) :
    ∃ u : (Ow w)ˣ, ((prW w : ℕ) : Ow w) = u * ϖ ^ eW w := by
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (natCast_ow_ne_zero w (prW_prime w).ne_zero) hϖ
  have hspan : (w.asIdeal.under ℤ).map (algebraMap ℤ (Ow w)) = IsLocalRing.maximalIdeal (Ow w) ^ n := by
    rw [← Int.ideal_span_absNorm_eq_self (w.asIdeal.under ℤ), Ideal.map_span, Set.image_singleton,
      hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
    have : algebraMap ℤ (Ow w) ((Ideal.absNorm (w.asIdeal.under ℤ) : ℕ) : ℤ) = ((prW w : ℕ) : Ow w) := by
      simp [prW]
    rw [this, hu]
    exact Ideal.span_singleton_eq_span_singleton.2 ⟨u⁻¹, by
      rw [mul_comm (u : Ow w), mul_assoc, Units.mul_inv, mul_one]⟩
  have he : eW w = n := by
    unfold eW
    rw [Ideal.ramificationIdx_def, hspan, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal,
      ENat.toNat_natCast]
  exact ⟨u, by rw [he, hu]⟩

/- English proof (translation)
Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible (Ow w)`. Take `⟨u, hu⟩` from `prW_eq_unit_mul_pow w hπ`. Rewrite using `[hu, hπ.maximalIdeal_eq, Ideal.span_singleton_pow]`. Conclude with `Ideal.span_singleton_eq_span_singleton.2 ⟨u⁻¹, by`. Rewrite using `[mul_comm (u : Ow w), mul_assoc, Units.mul_inv, mul_one]⟩`.
-/
theorem span_prW_ow (w : HeightOneSpectrum (𝓞 K)) :
    Ideal.span {((prW w : ℕ) : Ow w)} = IsLocalRing.maximalIdeal (Ow w) ^ eW w := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Ow w)
  obtain ⟨u, hu⟩ := prW_eq_unit_mul_pow w hπ
  rw [hu, hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
  exact Ideal.span_singleton_eq_span_singleton.2 ⟨u⁻¹, by
    rw [mul_comm (u : Ow w), mul_assoc, Units.mul_inv, mul_one]⟩

/- English proof (translation)
Rewrite using `[span_prW_ow, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]`.
-/
theorem length_ow_quot_prW (w : HeightOneSpectrum (𝓞 K)) :
    Module.length (Ow w) (Ow w ⧸ Ideal.span {((prW w : ℕ) : Ow w)}) = eW w := by
  rw [span_prW_ow, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]

scoped instance owTorsionFree (w : HeightOneSpectrum (𝓞 K)) (V : Type) [AddCommGroup V] [Module K V] :
    Module.IsTorsionFree (Ow w) V :=
  Module.IsTorsionFree.of_smul_eq_zero (fun r x h => by
    change algebraMap (Ow w) K r • x = 0 at h
    rcases smul_eq_zero.1 h with h | h
    · left
      exact algebraMap_ow_injective w (by rw [h, map_zero])
    · exact Or.inr h)

/- English proof (translation)
The claim follows from `Module.Finite.iff_fg.2 (atW_fg w h)`.
-/
theorem atW_finite (w : HeightOneSpectrum (𝓞 K)) {L : Submodule (𝓞 K) V} (h : L.FG) :
    Module.Finite (Ow w) (atW w L) := Module.Finite.iff_fg.2 (atW_fg w h)

/- English proof (translation)
Use `atW_finite w h` as an intermediate fact. Use `infer_instance`.
-/
theorem atW_free (w : HeightOneSpectrum (𝓞 K)) {L : Submodule (𝓞 K) V} (h : L.FG) :
    Module.Free (Ow w) (atW w L) := by
  have := atW_finite w h
  infer_instance

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Establish `: atW w L ≤ (Submodule.span K (L : Set V)).restrictScalars (Ow w)` using `Submodule.span_le.2 Submodule.subset_span`. Conclude with `this`. Conclude with `Submodule.span_mono (le_atW w L)`.
-/
theorem span_atW (w : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) V) :
    Submodule.span K (atW w L : Set V) = Submodule.span K (L : Set V) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    have : atW w L ≤ (Submodule.span K (L : Set V)).restrictScalars (Ow w) :=
      Submodule.span_le.2 Submodule.subset_span
    exact this
  · exact Submodule.span_mono (le_atW w L)

/- English proof (translation)
Use `atW_finite w h` as an intermediate fact. Use `atW_free w h` as an intermediate fact. Set `b` to `Module.Free.chooseBasis (Ow w) (atW w L)`. Establish `hli : LinearIndependent (Ow w) (fun i => ((b i : atW w L) : V))` using `b.linearIndependent.map' (atW w L).subtype (Submodule.ker_subtype _)`. Establish `hliK : LinearIndependent K (fun i => ((b i : atW w L) : V))` using `(LinearIndependent.iff_fractionRing (Ow w) K).1 hli`.

Establish `hsp : Submodule.span (Ow w) (Set.range fun i => ((b i : atW w L) : V)) = atW w L`. Establish `h1 : (Set.range fun i => ((b i : atW w L) : V)) = (atW w L).subtype '' Set.range b`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[h1, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]`.

Establish `key : ∀ S : Set V, Submodule.span (Ow w) S = atW w L → Submodule.span K S = Submodule.span K (L : Set V)` using `fun S hS => by`. Rewrite using `[← span_atW w L, ← hS, Submodule.span_span_of_tower]`. Establish `hspK` using `key _ hsp`. Rewrite using `[← hspK, finrank_span_eq_card hliK, Module.finrank_eq_card_basis b]`.
-/
theorem finrank_atW (w : HeightOneSpectrum (𝓞 K)) {L : Submodule (𝓞 K) V} (h : L.FG) :
    Module.finrank (Ow w) (atW w L) = Module.finrank K (Submodule.span K (L : Set V)) := by
  have := atW_finite w h
  have := atW_free w h
  let b := Module.Free.chooseBasis (Ow w) (atW w L)
  have hli : LinearIndependent (Ow w) (fun i => ((b i : atW w L) : V)) :=
    b.linearIndependent.map' (atW w L).subtype (Submodule.ker_subtype _)
  have hliK : LinearIndependent K (fun i => ((b i : atW w L) : V)) :=
    (LinearIndependent.iff_fractionRing (Ow w) K).1 hli
  have hsp : Submodule.span (Ow w) (Set.range fun i => ((b i : atW w L) : V)) = atW w L := by
    have h1 : (Set.range fun i => ((b i : atW w L) : V)) = (atW w L).subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [h1, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have key : ∀ S : Set V, Submodule.span (Ow w) S = atW w L →
      Submodule.span K S = Submodule.span K (L : Set V) := fun S hS => by
    rw [← span_atW w L, ← hS, Submodule.span_span_of_tower]
  have hspK := key _ hsp
  rw [← hspK, finrank_span_eq_card hliK, Module.finrank_eq_card_basis b]

/- English proof (translation)
Rewrite using `[← mem_range_ow_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨s, hs, hx'⟩` from `mem_atW_iff.1 hx`. Take `⟨a, ha⟩` from `Submodule.mem_one.1 hx'`.

Use `⟨IsLocalization.mk' (Ow w) a (⟨s, hs⟩ : w.asIdeal.primeCompl), ?_⟩` and prove the remaining obligations. Establish `hs0 : algebraMap (𝓞 K) K s ≠ 0`. Introduce `h0`. Establish `: s = 0` using `FaithfulSMul.algebraMap_injective (𝓞 K) K (by rw [h0, map_zero])`. Conclude with `hs (this ▸ w.asIdeal.zero_mem)`.

Apply `mul_right_cancel₀ hs0` to reduce the goal to its premises. Establish `e : algebraMap (𝓞 K) K s = algebraMap (Ow w) K (algebraMap (𝓞 K) (Ow w) s)` using `IsScalarTower.algebraMap_apply _ _ _ _`. Establish `h4 : IsLocalization.mk' (Ow w) a (⟨s, hs⟩ : w.asIdeal.primeCompl) * algebraMap (𝓞 K) (Ow w) s = algebraMap (𝓞 K) (Ow w) a` using `IsLocalization.mk'_spec (Ow w) a (⟨s, hs⟩ : w.asIdeal.primeCompl)`. Combine the equalities or inequalities in the displayed calculation. Introduce and unpack `⟨r, rfl⟩`.

Establish `: algebraMap (Ow w) K r = r • (1 : K)` using `by rw [Algebra.smul_def, mul_one]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.one_le.1 le_rfl))`.
-/
theorem mem_atW_one_iff (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    x ∈ atW w (1 : Submodule (𝓞 K) K) ↔ w.valuation K x ≤ 1 := by
  rw [← mem_range_ow_iff]
  constructor
  · intro hx
    obtain ⟨s, hs, hx'⟩ := mem_atW_iff.1 hx
    obtain ⟨a, ha⟩ := Submodule.mem_one.1 hx'
    refine ⟨IsLocalization.mk' (Ow w) a (⟨s, hs⟩ : w.asIdeal.primeCompl), ?_⟩
    have hs0 : algebraMap (𝓞 K) K s ≠ 0 := by
      intro h0
      have : s = 0 := FaithfulSMul.algebraMap_injective (𝓞 K) K (by rw [h0, map_zero])
      exact hs (this ▸ w.asIdeal.zero_mem)
    apply mul_right_cancel₀ hs0
    have e : algebraMap (𝓞 K) K s = algebraMap (Ow w) K (algebraMap (𝓞 K) (Ow w) s) :=
      IsScalarTower.algebraMap_apply _ _ _ _
    have h4 : IsLocalization.mk' (Ow w) a (⟨s, hs⟩ : w.asIdeal.primeCompl) * algebraMap (𝓞 K) (Ow w) s =
        algebraMap (𝓞 K) (Ow w) a := IsLocalization.mk'_spec (Ow w) a (⟨s, hs⟩ : w.asIdeal.primeCompl)
    calc algebraMap (Ow w) K (IsLocalization.mk' (Ow w) a (⟨s, hs⟩ : w.asIdeal.primeCompl)) *
          algebraMap (𝓞 K) K s
        = algebraMap (Ow w) K (IsLocalization.mk' (Ow w) a (⟨s, hs⟩ : w.asIdeal.primeCompl) *
          algebraMap (𝓞 K) (Ow w) s) := by rw [e, map_mul]
      _ = algebraMap (𝓞 K) K a := by rw [h4, ← IsScalarTower.algebraMap_apply]
      _ = x * algebraMap (𝓞 K) K s := by rw [ha, Algebra.smul_def, mul_comm]
  · rintro ⟨r, rfl⟩
    have : algebraMap (Ow w) K r = r • (1 : K) := by rw [Algebra.smul_def, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.one_le.1 le_rfl))

/- English proof (translation)
Rewrite using `[ENat.eq_top_iff_forall_ge]`. Introduce `n`. Rewrite using `[← IsDiscreteValuationRing.length_quotient_pow_maximalIdeal (R := Ow w) n]`. Conclude with `Module.length_le_of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)`.
-/
theorem length_ow_self (w : HeightOneSpectrum (𝓞 K)) : Module.length (Ow w) (Ow w) = ⊤ := by
  rw [ENat.eq_top_iff_forall_ge]
  intro n
  rw [← IsDiscreteValuationRing.length_quotient_pow_maximalIdeal (R := Ow w) n]
  exact Module.length_le_of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)

section Restrict
variable (w : HeightOneSpectrum (𝓞 K)) (Q : Type) [AddCommGroup Q] [Module (Ow w) Q] [Module (𝓞 K) Q]
  [IsScalarTower (𝓞 K) (Ow w) Q]

/- English proof (translation)
Set `f : Ow w →ₗ[Ow w] Q` to `LinearMap.toSpanSingleton (Ow w) Q x`. Establish `hker : LinearMap.ker f ≠ ⊥`. Introduce `h`. Apply `hQ` to reduce the goal to its premises. Use `Module.length_le_of_injective f (LinearMap.ker_eq_bot.1 h)` as an intermediate fact.

Rewrite `this` using `[length_ow_self]`. Conclude with `top_le_iff.1 this`. Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible (Ow w)`. Take `⟨n, hn⟩` from `IsDiscreteValuationRing.ideal_eq_span_pow_irreducible (s := (LinearMap.ker f : Ideal (Ow w))) hker hπ`. Use `⟨n, fun c hc => ?_⟩` and prove the remaining obligations.

Establish `h1 : algebraMap (𝓞 K) (Ow w) c ∈ LinearMap.ker f`. Rewrite using `[hn, ← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq]`. Conclude with `(algebraMap_mem_maximalIdeal_pow_iff w c n).2 hc`. Establish `h2 : algebraMap (𝓞 K) (Ow w) c • x = 0` using `h1`. Rewrite `h2` using `[algebraMap_smul]`. Then use the resulting hypothesis.
-/
theorem exists_pow_smul_eq_zero (hQ : Module.length (Ow w) Q ≠ ⊤) (x : Q) :
    ∃ n : ℕ, ∀ c ∈ w.asIdeal ^ n, c • x = 0 := by
  let f : Ow w →ₗ[Ow w] Q := LinearMap.toSpanSingleton (Ow w) Q x
  have hker : LinearMap.ker f ≠ ⊥ := by
    intro h
    apply hQ
    have := Module.length_le_of_injective f (LinearMap.ker_eq_bot.1 h)
    rw [length_ow_self] at this
    exact top_le_iff.1 this
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Ow w)
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (s := (LinearMap.ker f : Ideal (Ow w))) hker hπ
  refine ⟨n, fun c hc => ?_⟩
  have h1 : algebraMap (𝓞 K) (Ow w) c ∈ LinearMap.ker f := by
    rw [hn, ← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq]
    exact (algebraMap_mem_maximalIdeal_pow_iff w c n).2 hc
  have h2 : algebraMap (𝓞 K) (Ow w) c • x = 0 := h1
  rwa [algebraMap_smul] at h2

/- English proof (translation)
Take `⟨n, hn⟩` from `exists_pow_smul_eq_zero w Q hQ x`. Take `⟨a, s, rfl⟩` from `IsLocalization.exists_mk'_eq w.asIdeal.primeCompl r`. Take `⟨y, i, hi, hyi⟩` from `w.isMaximal.exists_inv s.2`. Establish `hcop : IsCoprime (s : 𝓞 K) (i ^ n)` using `IsCoprime.pow_right ⟨y, 1, by rw [one_mul]; exact hyi⟩`. Take `⟨b, c, hbc⟩` from `hcop`.

Establish `h0 : (c * i ^ n) • x = 0` using `hn _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hi n))`. Establish `h1 : x = (s : 𝓞 K) • (b • x)` using `by conv_lhs => rw [← one_smul (𝓞 K) x, ← hbc, add_smul, h0, add_zero, mul_comm, mul_smul]`. Establish `h2 : IsLocalization.mk' (Ow w) a s • x = a • (b • x)` using `by conv_lhs => rw [h1]`. Rewrite using `[← algebraMap_smul (Ow w) (s : 𝓞 K), smul_smul, IsLocalization.mk'_spec, algebraMap_smul]`. Rewrite using `[h2]`.

Conclude with `N.smul_mem a (N.smul_mem b hx)`.
-/
theorem ow_smul_mem_of_length (hQ : Module.length (Ow w) Q ≠ ⊤) (N : Submodule (𝓞 K) Q) (r : Ow w)
    {x : Q} (hx : x ∈ N) : r • x ∈ N := by
  obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero w Q hQ x
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq w.asIdeal.primeCompl r
  obtain ⟨y, i, hi, hyi⟩ := w.isMaximal.exists_inv s.2
  have hcop : IsCoprime (s : 𝓞 K) (i ^ n) := IsCoprime.pow_right ⟨y, 1, by rw [one_mul]; exact hyi⟩
  obtain ⟨b, c, hbc⟩ := hcop
  have h0 : (c * i ^ n) • x = 0 := hn _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hi n))
  have h1 : x = (s : 𝓞 K) • (b • x) := by
    conv_lhs => rw [← one_smul (𝓞 K) x, ← hbc, add_smul, h0, add_zero, mul_comm, mul_smul]
  have h2 : IsLocalization.mk' (Ow w) a s • x = a • (b • x) := by
    conv_lhs => rw [h1]
    rw [← algebraMap_smul (Ow w) (s : 𝓞 K), smul_smul, IsLocalization.mk'_spec, algebraMap_smul]
  rw [h2]
  exact N.smul_mem a (N.smul_mem b hx)

/- English proof (translation)
Distinguish the cases in `hQ : Module.length (Ow w) Q = ⊤`. Use `Submodule.length_le_length_restrictScalars (𝓞 K) (⊤ : Submodule (Ow w) Q)` as an intermediate fact. Rewrite `this` using `[Submodule.restrictScalars_top, Module.length_top, Module.length_top, hQ]`. Rewrite using `[hQ]`. Conclude with `top_le_iff.1 this`.

Set `e : Submodule (𝓞 K) Q ≃o Submodule (Ow w) Q` to `{ toFun := fun N => { N with smul_mem' := fun r _ hx => ow_smul_mem_of_length w Q hQ N r hx } invFun := fun N => N.restrictScalars (𝓞 K) left_inv := fun _ => rfl right_inv := fun _ => rfl map_rel_iff' := Iff.rfl }`. Apply `WithBot.coe_injective` to reduce the goal to its premises. Rewrite using `[Module.coe_length, Module.coe_length, Order.krullDim_eq_of_orderIso e]`.
-/
theorem length_restrict_ow : Module.length (𝓞 K) Q = Module.length (Ow w) Q := by
  by_cases hQ : Module.length (Ow w) Q = ⊤
  · have := Submodule.length_le_length_restrictScalars (𝓞 K) (⊤ : Submodule (Ow w) Q)
    rw [Submodule.restrictScalars_top, Module.length_top, Module.length_top, hQ] at this
    rw [hQ]
    exact top_le_iff.1 this
  · let e : Submodule (𝓞 K) Q ≃o Submodule (Ow w) Q :=
      { toFun := fun N => { N with smul_mem' := fun r _ hx => ow_smul_mem_of_length w Q hQ N r hx }
        invFun := fun N => N.restrictScalars (𝓞 K)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_rel_iff' := Iff.rfl }
    apply WithBot.coe_injective
    rw [Module.coe_length, Module.coe_length, Order.krullDim_eq_of_orderIso e]

end Restrict

/- English proof (translation)
Unfold `lenW`. Rewrite using `[← length_restrict_ow w]`. Establish `hA : ∀ x : V, x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A ↔ x ∈ atW w A` using `fun x => by`. Rewrite using `[← atW_restrictScalars]`. Both sides reduce to the same expression.

Establish `hB : ∀ x : V, x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B ↔ x ∈ atW w B` using `fun x => by`. Rewrite using `[← atW_restrictScalars]`. Both sides reduce to the same expression. Set `e : Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A ≃ₗ[𝓞 K] atW w A` to `{ toFun := fun x => ⟨x.1, (hA _).1 x.2⟩ invFun := fun x => ⟨x.1, (hA _).2 x.2⟩ left_inv := fun _ => rfl right_inv := fun _ => rfl map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Use `LinearEquiv.length_eq (((Submodule.Quotient.equiv _ (((atW w B).comap (atW w A).subtype).restrictScalars (𝓞 K)) e ?_).trans (Submodule.Quotient.restrictScalarsEquiv (𝓞 K) _)).symm)` and prove the remaining obligations.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `(hB _).1 hy`. Introduce `hx`.

Conclude with `⟨e.symm x, (hB _).2 hx, e.apply_symm_apply x⟩`.
-/
theorem lenW_eq_length (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) :
    lenW w A B = Module.length (𝓞 K) (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A ⧸
      (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B).comap (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A).subtype) := by
  unfold lenW
  rw [← length_restrict_ow w]
  have hA : ∀ x : V, x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A ↔ x ∈ atW w A := fun x => by
    rw [← atW_restrictScalars]; rfl
  have hB : ∀ x : V, x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B ↔ x ∈ atW w B := fun x => by
    rw [← atW_restrictScalars]; rfl
  let e : Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A ≃ₗ[𝓞 K] atW w A :=
    { toFun := fun x => ⟨x.1, (hA _).1 x.2⟩
      invFun := fun x => ⟨x.1, (hA _).2 x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine LinearEquiv.length_eq (((Submodule.Quotient.equiv _
    (((atW w B).comap (atW w A).subtype).restrictScalars (𝓞 K)) e ?_).trans
    (Submodule.Quotient.restrictScalarsEquiv (𝓞 K) _)).symm)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hB _).1 hy
  · intro hx
    exact ⟨e.symm x, (hB _).2 hx, e.apply_symm_apply x⟩

/- English proof (translation)
Rewrite using `[lenW_eq_length]`. Both sides reduce to the same expression.
-/
theorem lenW_toNat (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) :
    (lenW w A B).toNat = Formalism.HermitianLatticesTheory.locLen w.asIdeal A B := by
  rw [lenW_eq_length]; rfl

/- English proof (translation)
Unfold `lidxW Formalism.HermitianLatticesTheory.lidx`. Rewrite using `[lenW_toNat, lenW_toNat]`.
-/
theorem lidxW_eq_lidx (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) :
    lidxW w A B = Formalism.HermitianLatticesTheory.lidx w.asIdeal A B := by
  unfold lidxW Formalism.HermitianLatticesTheory.lidx
  rw [lenW_toNat, lenW_toNat]

/- English proof (translation)
Unfold `lenW`. Establish `: (atW w (A ⊓ B)).comap (atW w A).subtype = (atW w B).comap (atW w A).subtype`. Rewrite using `[atW_inf]`. Use extensionality with `x`. Simplify using the standard rewrite rules.

Rewrite using `[this]`.
-/
theorem lenW_inf (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) :
    lenW w A (A ⊓ B) = lenW w A B := by
  unfold lenW
  have : (atW w (A ⊓ B)).comap (atW w A).subtype = (atW w B).comap (atW w A).subtype := by
    rw [atW_inf]
    ext x
    simp
  rw [this]

/- English proof (translation)
Unfold `lenW`. Rewrite using `[Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff, eq_top_iff]`. Introduce `x _`. Conclude with `h x.2`.
-/
theorem lenW_eq_zero (w : HeightOneSpectrum (𝓞 K)) {A B : Submodule (𝓞 K) V} (h : atW w A ≤ atW w B) :
    lenW w A B = 0 := by
  unfold lenW
  rw [Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff, eq_top_iff]
  intro x _
  exact h x.2

abbrev idLat (I : Ideal (𝓞 K)) : Submodule (𝓞 K) K := IsLocalization.coeSubmodule K I

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨s, hs, hx⟩` from `mem_atW_iff.1 h`. Take `⟨a, ha, hax⟩` from `(IsLocalization.mem_coeSubmodule K _).1 hx`. Establish `h1 : algebraMap (𝓞 K) (Ow w) a = algebraMap (𝓞 K) (Ow w) s * r`.

Apply `algebraMap_ow_injective w` to reduce the goal to its premises. Rewrite using `[map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, hax, Algebra.smul_def]`. Establish `h2 : algebraMap (𝓞 K) (Ow w) s * r ∈ IsLocalRing.maximalIdeal (Ow w) ^ n` using `h1 ▸ (algebraMap_mem_maximalIdeal_pow_iff w a n).2 ha`. Establish `hu : IsUnit (algebraMap (𝓞 K) (Ow w) s)` using `IsLocalization.map_units (Ow w) (⟨s, hs⟩ : w.asIdeal.primeCompl)`. Conclude with `(Ideal.unit_mul_mem_iff_mem _ hu).1 h2`.

Introduce `h`. Rewrite `h` using `[maximalIdeal_ow, ← Ideal.map_pow]`. Take `⟨⟨b, s⟩, hbs⟩` from `(IsLocalization.mem_map_algebraMap_iff w.asIdeal.primeCompl (Ow w)).1 h`. Use `mem_atW_iff.2 ⟨s, s.2, (IsLocalization.mem_coeSubmodule K _).2 ⟨b, b.2, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, IsScalarTower.algebraMap_apply (𝓞 K) (Ow w) K, IsScalarTower.algebraMap_apply (𝓞 K) (Ow w) K, ← map_mul, mul_comm]`.

Conclude with `congrArg _ hbs.symm`.
-/
theorem mem_atW_idLat_pow_iff (w : HeightOneSpectrum (𝓞 K)) (n : ℕ) (r : Ow w) :
    algebraMap (Ow w) K r ∈ atW w (idLat (w.asIdeal ^ n)) ↔ r ∈ IsLocalRing.maximalIdeal (Ow w) ^ n := by
  constructor
  · intro h
    obtain ⟨s, hs, hx⟩ := mem_atW_iff.1 h
    obtain ⟨a, ha, hax⟩ := (IsLocalization.mem_coeSubmodule K _).1 hx
    have h1 : algebraMap (𝓞 K) (Ow w) a = algebraMap (𝓞 K) (Ow w) s * r := by
      apply algebraMap_ow_injective w
      rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, hax,
        Algebra.smul_def]
    have h2 : algebraMap (𝓞 K) (Ow w) s * r ∈ IsLocalRing.maximalIdeal (Ow w) ^ n :=
      h1 ▸ (algebraMap_mem_maximalIdeal_pow_iff w a n).2 ha
    have hu : IsUnit (algebraMap (𝓞 K) (Ow w) s) :=
      IsLocalization.map_units (Ow w) (⟨s, hs⟩ : w.asIdeal.primeCompl)
    exact (Ideal.unit_mul_mem_iff_mem _ hu).1 h2
  · intro h
    rw [maximalIdeal_ow, ← Ideal.map_pow] at h
    obtain ⟨⟨b, s⟩, hbs⟩ := (IsLocalization.mem_map_algebraMap_iff w.asIdeal.primeCompl (Ow w)).1 h
    refine mem_atW_iff.2 ⟨s, s.2, (IsLocalization.mem_coeSubmodule K _).2 ⟨b, b.2, ?_⟩⟩
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply (𝓞 K) (Ow w) K,
      IsScalarTower.algebraMap_apply (𝓞 K) (Ow w) K, ← map_mul, mul_comm]
    exact congrArg _ hbs.symm

/- English proof (translation)
Unfold `lenW`. Rewrite using `[← IsDiscreteValuationRing.length_quotient_pow_maximalIdeal (R := Ow w) n]`. Establish `hmem : ∀ r : Ow w, algebraMap (Ow w) K r ∈ atW w (1 : Submodule (𝓞 K) K)` using `fun r => (mem_atW_one_iff w _).2 ((mem_range_ow_iff w _).1 ⟨r, rfl⟩)`. Set `f : Ow w →ₗ[Ow w] atW w (1 : Submodule (𝓞 K) K)` to `(Algebra.linearMap (Ow w) K).codRestrict _ hmem`. Establish `hf : Function.Bijective f`.

Prove the components needed by the constructor for the conclusion. Introduce `a b hab`. Conclude with `algebraMap_ow_injective w (congrArg Subtype.val hab)`. Introduce and unpack `⟨x, hx⟩`. Take `⟨r, rfl⟩` from `(mem_range_ow_iff w x).2 ((mem_atW_one_iff w x).1 hx)`.

Conclude with `⟨r, rfl⟩`. Use `(LinearEquiv.length_eq (Submodule.Quotient.equiv _ _ (LinearEquiv.ofBijective f hf) ?_)).symm` and prove the remaining obligations. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, hr, rfl⟩`.

Conclude with `(mem_atW_idLat_pow_iff w n r).2 hr`. Introduce `hx`. Take `⟨r, rfl⟩` from `hf.2 x`. Conclude with `⟨r, (mem_atW_idLat_pow_iff w n r).1 hx, rfl⟩`.
-/
theorem lenW_one_pow (w : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    lenW w (1 : Submodule (𝓞 K) K) (idLat (w.asIdeal ^ n)) = n := by
  unfold lenW
  rw [← IsDiscreteValuationRing.length_quotient_pow_maximalIdeal (R := Ow w) n]
  have hmem : ∀ r : Ow w, algebraMap (Ow w) K r ∈ atW w (1 : Submodule (𝓞 K) K) := fun r =>
    (mem_atW_one_iff w _).2 ((mem_range_ow_iff w _).1 ⟨r, rfl⟩)
  let f : Ow w →ₗ[Ow w] atW w (1 : Submodule (𝓞 K) K) :=
    (Algebra.linearMap (Ow w) K).codRestrict _ hmem
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      exact algebraMap_ow_injective w (congrArg Subtype.val hab)
    · rintro ⟨x, hx⟩
      obtain ⟨r, rfl⟩ := (mem_range_ow_iff w x).2 ((mem_atW_one_iff w x).1 hx)
      exact ⟨r, rfl⟩
  refine (LinearEquiv.length_eq (Submodule.Quotient.equiv _ _ (LinearEquiv.ofBijective f hf) ?_)).symm
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact (mem_atW_idLat_pow_iff w n r).2 hr
  · intro hx
    obtain ⟨r, rfl⟩ := hf.2 x
    exact ⟨r, (mem_atW_idLat_pow_iff w n r).1 hx, rfl⟩

/- English proof (translation)
The claim follows from `Nat.cast_ne_zero.2 (eW_pos w).ne'`.
-/
theorem eW_ne_zero_rat (w : HeightOneSpectrum (𝓞 K)) : (eW w : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.2 (eW_pos w).ne'

omit [IsScalarTower (𝓞 K) K V] in

/- English proof (translation)
The claim follows from `div_mul_cancel₀ _ (eW_ne_zero_rat w)`.
-/
theorem lenUW_mul_eW (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) :
    lenUW w A B * (eW w : ℚ) = ((lenW w A B).toNat : ℚ) :=
  div_mul_cancel₀ _ (eW_ne_zero_rat w)

/- English proof (translation)
Take `⟨m, hm⟩` from `Ideal.exists_maximal (𝓞 K)`. Conclude with `⟨(plEquiv K).symm ⟨m, hm⟩⟩`.
-/
theorem nonempty_places (K : Type) [Field K] [NumberField K] : Nonempty (HeightOneSpectrum (𝓞 K)) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 K)
  exact ⟨(plEquiv K).symm ⟨m, hm⟩⟩

/- English proof (translation)
Take `⟨w⟩` from `nonempty_places ℚ`. Conclude with `⟨w, lenW_one_pow w 3⟩`.
-/
example : ∃ w : HeightOneSpectrum (𝓞 ℚ), lenW w (1 : Submodule (𝓞 ℚ) ℚ) (idLat (w.asIdeal ^ 3)) = 3 := by
  obtain ⟨w⟩ := nonempty_places ℚ
  exact ⟨w, lenW_one_pow w 3⟩

end Formalism.L2.Col
