import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
import Development.AutomorphicArithmetic.CommutativeAlgebra.FiniteKernelPowClassesOfPrimitiveRoot
import GroundTheory.FunctionField.PlaceAbove

open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

/- English proof (translation)
Establish `h` using `trdeg_add_eq k K (A := K')`. Rewrite `h` using `[trdeg_eq_one (k := k) (K := K), trdeg_eq_one (k := k) (K := K')]`. Establish `hfin : Algebra.trdeg K K' < Cardinal.aleph0` using `lt_of_le_of_lt (h ▸ le_add_self) Cardinal.one_lt_aleph0`. Take `⟨n, hn⟩` from `Cardinal.lt_aleph0.mp hfin`. Rewrite `h` using `[hn]`.

Establish `hn0 : n = 0`. Establish `: ((1 + n : ℕ) : Cardinal) = ((1 : ℕ) : Cardinal)` using `by push_cast; exact h`. Use `Nat.cast_injective this` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[← trdeg_eq_zero_iff, hn, hn0, Nat.cast_zero]`.
-/
private theorem functionField_isAlgebraic_of_tower (k K K' : Type) [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']
    [Algebra K K'] [IsScalarTower k K K'] [IsFunctionField k K] [IsFunctionField k K'] :
    Algebra.IsAlgebraic K K' := by
  have h := trdeg_add_eq k K (A := K')
  rw [trdeg_eq_one (k := k) (K := K), trdeg_eq_one (k := k) (K := K')] at h
  have hfin : Algebra.trdeg K K' < Cardinal.aleph0 :=
    lt_of_le_of_lt (h ▸ le_add_self) Cardinal.one_lt_aleph0
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp hfin
  rw [hn] at h
  have hn0 : n = 0 := by
    have : ((1 + n : ℕ) : Cardinal) = ((1 : ℕ) : Cardinal) := by push_cast; exact h
    have := Nat.cast_injective this
    omega
  rw [← trdeg_eq_zero_iff, hn, hn0, Nat.cast_zero]

/- English proof (translation)
Introduce `k K K' _ _ _ _ _ _ _ _ _ _ q _ hq hK'`. Use `functionField_isAlgebraic_of_tower k K K'` as an intermediate fact. Establish `: Algebra.EssFiniteType k K'` using `essFiniteType`. Establish `: Algebra.EssFiniteType K K'` using `Algebra.EssFiniteType.of_comp k K K'`. Establish `: Module.Finite K K'` using `Algebra.finite_of_essFiniteType_of_isAlgebraic`.

Establish `: NeZero (q : k)` using `⟨hq.ne_zero⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot k q`. Take `⟨T0, hT0⟩` from `UpperTheory.finite_kernel_powClasses_of_primitive_root K K' q ⟨algebraMap k K ζ, hζ.map_of_injective (algebraMap k K).injective⟩`. Take `⟨T', hT'⟩` from `hK'`. Set `φ : Kˣ →* K'ˣ` to `Units.map (algebraMap K K' : K →* K')`.

Establish `hφ : ∀ x : Kˣ, ((φ x : K'ˣ) : K') = algebraMap K K' (x : K)` using `fun x => rfl`. Establish `himg : ∀ f ∈ SelAll k K q, φ f ∈ SelAll k K' q`. Introduce `f hf w`. Establish `hw` using `(Place.liesOver_comap w).ord_algebraMap (f : K)`. Use `show (q : ℤ) ∣ w.ord ((φ f : K'ˣ) : K')`.

Rewrite using `[hφ, hw]`. Conclude with `Dvd.dvd.mul_left (hf _) _`. Set `g : K'ˣ → Kˣ` to `fun t' => if h : ∃ f ∈ SelAll k K q, ∃ u : K'ˣ, φ f = t' * u ^ q then h.choose else 1`. Use `⟨Finset.image₂ (· * ·) (T'.image g) T0, ?_⟩` and prove the remaining obligations. Introduce `f hf`.

Take `⟨t', ht', u, hu⟩` from `hT' (φ f) (himg f hf)`. Establish `hex : ∃ f ∈ SelAll k K q, ∃ u : K'ˣ, φ f = t' * u ^ q` using `⟨f, hf, u, hu⟩`. Establish `hg : g t' = hex.choose` using `dif_pos hex`. Take `⟨_, u0, hu0⟩` from `hex.choose_spec`. Use `set f0 := hex.choose`.

Establish `hmem : f * f0⁻¹ ∈ {a : Kˣ | ∃ b : K', algebraMap K K' (a : K) = b ^ q}`. Use `⟨((u * u0⁻¹ : K'ˣ) : K'), ?_⟩` and prove the remaining obligations. Rewrite using `[← hφ, map_mul, map_inv, hu, hu0]`. Use `push_cast`. Rewrite using `[mul_pow, inv_pow]`.

Clear the denominators using the available nonvanishing facts. Take `⟨s, hs, w, hw⟩` from `hT0 _ hmem`. Use `⟨f0 * s, Finset.mem_image₂.mpr ⟨f0, Finset.mem_image.mpr ⟨t', ht', hg⟩, s, hs, rfl⟩, w, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_assoc, ← hw, mul_comm f, mul_inv_cancel_left]`.
-/
theorem UpperTheory.finite_kummerSelmer_of_finite_extension :
    ∀ (k K K' : Type) [Field k] [IsAlgClosed k] [Field K] [Field K'] [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] [IsFunctionField k K] [IsFunctionField k K'] (q : ℕ) [NeZero q], IsUnit (q : k) → FinCls q (SelAll k K' q) → FinCls q (SelAll k K q) := by
  classical
  intro k K K' _ _ _ _ _ _ _ _ _ _ q _ hq hK'
  have := functionField_isAlgebraic_of_tower k K K'
  have : Algebra.EssFiniteType k K' := essFiniteType
  have : Algebra.EssFiniteType K K' := Algebra.EssFiniteType.of_comp k K K'
  have : Module.Finite K K' := Algebra.finite_of_essFiniteType_of_isAlgebraic
  have : NeZero (q : k) := ⟨hq.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k q
  obtain ⟨T0, hT0⟩ := UpperTheory.finite_kernel_powClasses_of_primitive_root K K' q
    ⟨algebraMap k K ζ, hζ.map_of_injective (algebraMap k K).injective⟩
  obtain ⟨T', hT'⟩ := hK'
  let φ : Kˣ →* K'ˣ := Units.map (algebraMap K K' : K →* K')
  have hφ : ∀ x : Kˣ, ((φ x : K'ˣ) : K') = algebraMap K K' (x : K) := fun x => rfl
  have himg : ∀ f ∈ SelAll k K q, φ f ∈ SelAll k K' q := by
    intro f hf w
    have hw := (Place.liesOver_comap w).ord_algebraMap (f : K)
    show (q : ℤ) ∣ w.ord ((φ f : K'ˣ) : K')
    rw [hφ, hw]
    exact Dvd.dvd.mul_left (hf _) _
  let g : K'ˣ → Kˣ := fun t' =>
    if h : ∃ f ∈ SelAll k K q, ∃ u : K'ˣ, φ f = t' * u ^ q then h.choose else 1
  refine ⟨Finset.image₂ (· * ·) (T'.image g) T0, ?_⟩
  intro f hf
  obtain ⟨t', ht', u, hu⟩ := hT' (φ f) (himg f hf)
  have hex : ∃ f ∈ SelAll k K q, ∃ u : K'ˣ, φ f = t' * u ^ q := ⟨f, hf, u, hu⟩
  have hg : g t' = hex.choose := dif_pos hex
  obtain ⟨_, u0, hu0⟩ := hex.choose_spec
  set f0 := hex.choose
  have hmem : f * f0⁻¹ ∈ {a : Kˣ | ∃ b : K', algebraMap K K' (a : K) = b ^ q} := by
    refine ⟨((u * u0⁻¹ : K'ˣ) : K'), ?_⟩
    rw [← hφ, map_mul, map_inv, hu, hu0]
    push_cast
    rw [mul_pow, inv_pow]
    field_simp
  obtain ⟨s, hs, w, hw⟩ := hT0 _ hmem
  refine ⟨f0 * s, Finset.mem_image₂.mpr ⟨f0, Finset.mem_image.mpr ⟨t', ht', hg⟩, s, hs, rfl⟩, w, ?_⟩
  rw [mul_assoc, ← hw, mul_comm f, mul_inv_cancel_left]
