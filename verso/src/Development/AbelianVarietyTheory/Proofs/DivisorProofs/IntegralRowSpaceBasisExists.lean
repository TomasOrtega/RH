import Mathlib

namespace GlobalTheory

/- English proof (translation)
Set `ι : (Fin n → O) →ₗ[O] (Fin n → k)` to `(Algebra.linearMap O k).compLeft (Fin n)`. Set `f : (Fin m → k) →ₗ[O] (Fin n → k)` to `(Matrix.vecMulLinear P).restrictScalars O`. Establish `hf : Function.Injective f`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `c hc`.

Conclude with `hP c hc`. Set `L : Submodule O (Fin m → k)` to `(LinearMap.range ι).comap f`. Establish `hL : ∀ c, c ∈ L ↔ ∃ a : Fin n → O, Matrix.vecMul c P = fun j => algebraMap O k (a j)`. Introduce `c`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨a, ha⟩`. Conclude with `⟨a, ha.symm⟩`. Introduce and unpack `⟨a, ha⟩`. Conclude with `⟨a, ha.symm⟩`. Establish `hfg : L.FG`.

Establish `h1 : (LinearMap.range ι).FG`. Rewrite using `[← Module.Finite.iff_fg]`. Use `infer_instance`. Establish `h2 : (L.map f).FG`. Establish `: IsNoetherian O (LinearMap.range ι)` using `isNoetherian_of_fg_of_noetherian _ h1`.

Establish `: IsNoetherian O (L.map f)` using `isNoetherian_of_le (Submodule.map_comap_le f _)`. Rewrite using `[← Module.Finite.iff_fg]`. Use `infer_instance`. Conclude with `Submodule.fg_of_fg_map_injective f hf h2`. Establish `hsp : Submodule.span k (L : Set (Fin m → k)) = ⊤`.

Rewrite using `[eq_top_iff]`. Introduce `c _`. Take `⟨d, hd⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) (Matrix.vecMul c P)`. Use `choose a ha using hd`. Establish `hd0 : algebraMap O k d ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2`.

Establish `hmem : (algebraMap O k d) • c ∈ L`. Rewrite using `[hL]`. Use `⟨a, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `j`. Rewrite using `[Matrix.smul_vecMul, ha j]`.

Simplify using `[Algebra.smul_def]`. Establish `: c = (algebraMap O k d)⁻¹ • ((algebraMap O k d) • c)`. Rewrite using `[smul_smul, inv_mul_cancel₀ hd0, one_smul]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hmem)`.

Use `haveI : Submodule.IsLattice k L := ⟨hfg, hsp⟩`. Establish `hr : Module.finrank O L = m`. Simplify using `using Submodule.IsLattice.finrank_of_pi k L`. Set `b : Module.Basis (Fin m) O L` to `Module.finBasisOfFinrankEq O L hr`. Set `M : Matrix (Fin m) (Fin m) k` to `Matrix.of fun i => (b i : Fin m → k)`.

Establish `hv : ∀ x : Fin m → O, Matrix.vecMul (fun i => algebraMap O k (x i)) M = ((∑ i, x i • b i : L) : Fin m → k)`. Introduce `x`. Use function extensionality and compare the values at `j`. Simplify using `[Matrix.vecMul, dotProduct, M, Algebra.smul_def]`. Use `⟨M, ?_, ?_⟩` and prove the remaining obligations.

Establish `hli : LinearIndependent k M.row`. Use `(b.extendOfIsLattice k).linearIndependent` as an intermediate fact. Establish `e : M.row = ⇑(b.extendOfIsLattice k)`. Use function extensionality and compare the values at `i`. Rewrite using `[Module.Basis.extendOfIsLattice_apply]`.

Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `this`. Use `Matrix.linearIndependent_rows_iff_isUnit.mp hli` as an intermediate fact. Conclude with `((Matrix.isUnit_iff_isUnit_det M).mp this).ne_zero`.

Introduce `c`. Rewrite using `[← hL]`. Prove the components needed by the constructor for the conclusion. Introduce `hc`. Use `⟨b.repr ⟨c, hc⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[hv, b.sum_repr]`. Introduce and unpack `⟨x, rfl⟩`. Rewrite using `[hv]`. Conclude with `Subtype.property _`.
-/
theorem exists_basis_matrix_of_integral_preimage
    (O k : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field k] [Algebra O k]
    [IsFractionRing O k] (m n : ℕ) (P : Matrix (Fin m) (Fin n) k)
    (hP : ∀ c, Matrix.vecMul c P = 0 → c = 0) :
    ∃ M : Matrix (Fin m) (Fin m) k, M.det ≠ 0 ∧ ∀ c : Fin m → k,
      (∃ a : Fin n → O, Matrix.vecMul c P = fun j => algebraMap O k (a j)) ↔
        ∃ b : Fin m → O, c = Matrix.vecMul (fun i => algebraMap O k (b i)) M := by
  classical
  let ι : (Fin n → O) →ₗ[O] (Fin n → k) := (Algebra.linearMap O k).compLeft (Fin n)
  let f : (Fin m → k) →ₗ[O] (Fin n → k) := (Matrix.vecMulLinear P).restrictScalars O
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    exact hP c hc
  let L : Submodule O (Fin m → k) := (LinearMap.range ι).comap f
  have hL : ∀ c, c ∈ L ↔ ∃ a : Fin n → O,
      Matrix.vecMul c P = fun j => algebraMap O k (a j) := by
    intro c
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, ha.symm⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, ha.symm⟩
  have hfg : L.FG := by
    have h1 : (LinearMap.range ι).FG := by
      rw [← Module.Finite.iff_fg]; infer_instance
    have h2 : (L.map f).FG := by
      have : IsNoetherian O (LinearMap.range ι) := isNoetherian_of_fg_of_noetherian _ h1
      have : IsNoetherian O (L.map f) := isNoetherian_of_le (Submodule.map_comap_le f _)
      rw [← Module.Finite.iff_fg]; infer_instance
    exact Submodule.fg_of_fg_map_injective f hf h2
  have hsp : Submodule.span k (L : Set (Fin m → k)) = ⊤ := by
    rw [eq_top_iff]
    intro c _
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O)
      (Matrix.vecMul c P)
    choose a ha using hd
    have hd0 : algebraMap O k d ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
    have hmem : (algebraMap O k d) • c ∈ L := by
      rw [hL]
      refine ⟨a, ?_⟩
      funext j
      rw [Matrix.smul_vecMul, ha j]
      simp [Algebra.smul_def]
    have : c = (algebraMap O k d)⁻¹ • ((algebraMap O k d) • c) := by
      rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  haveI : Submodule.IsLattice k L := ⟨hfg, hsp⟩
  have hr : Module.finrank O L = m := by
    simpa using Submodule.IsLattice.finrank_of_pi k L
  let b : Module.Basis (Fin m) O L := Module.finBasisOfFinrankEq O L hr
  let M : Matrix (Fin m) (Fin m) k := Matrix.of fun i => (b i : Fin m → k)
  have hv : ∀ x : Fin m → O, Matrix.vecMul (fun i => algebraMap O k (x i)) M
      = ((∑ i, x i • b i : L) : Fin m → k) := by
    intro x
    funext j
    simp [Matrix.vecMul, dotProduct, M, Algebra.smul_def]
  refine ⟨M, ?_, ?_⟩
  · have hli : LinearIndependent k M.row := by
      have := (b.extendOfIsLattice k).linearIndependent
      have e : M.row = ⇑(b.extendOfIsLattice k) := by
        funext i
        rw [Module.Basis.extendOfIsLattice_apply]
        rfl
      rw [e]
      exact this
    have := Matrix.linearIndependent_rows_iff_isUnit.mp hli
    exact ((Matrix.isUnit_iff_isUnit_det M).mp this).ne_zero
  · intro c
    rw [← hL]
    constructor
    · intro hc
      refine ⟨b.repr ⟨c, hc⟩, ?_⟩
      rw [hv, b.sum_repr]
    · rintro ⟨x, rfl⟩
      rw [hv]
      exact Subtype.property _

end GlobalTheory
