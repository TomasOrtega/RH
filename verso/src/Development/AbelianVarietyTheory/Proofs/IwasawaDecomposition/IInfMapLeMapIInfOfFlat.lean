import Mathlib
open scoped TensorProduct

namespace GlobalTheory.FlatIdealInf

open TensorProduct

/- English proof (translation)
Consider the cases of `nonempty_fintype ι`. Introduce `t ht`. Rewrite `ht` using `[Submodule.mem_iInf]`. Set `φ : M →ₗ[B] (∀ i, M ⧸ K i)` to `LinearMap.pi (fun i => (K i).mkQ)`. Establish `hexB : Function.Exact (⨅ i, K i).subtype φ`.

Rewrite using `[LinearMap.exact_iff, LinearMap.ker_pi, Submodule.range_subtype]`. Simplify using `only [Submodule.ker_mkQ]`. Establish `hex` using `Module.Flat.lTensor_exact R hexB`. Establish `hcomp : ∀ i (u : R ⊗[B] M), TensorProduct.piRight B B R (fun i => M ⧸ K i) (LinearMap.lTensor R φ u) i = LinearMap.lTensor R (K i).mkQ u`. Introduce `i u`.

Proceed by induction on `u using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r m => simp [φ]`. Consider the case `add x y hx hy => simp_all`. Establish `h0 : LinearMap.lTensor R φ t = 0`.

Apply `(TensorProduct.piRight B B R (fun i => M ⧸ K i)).injective` to reduce the goal to its premises. Rewrite using `[map_zero]`. Use function extensionality and compare the values at `i`. Rewrite using `[hcomp i t, Pi.zero_apply]`. Take `⟨s, hs⟩` from `ht i`.

Rewrite using `[← hs]`. Conclude with `(lTensor_exact R (LinearMap.exact_subtype_mkQ (K i)) (Submodule.mkQ_surjective _) _).mpr ⟨s, rfl⟩`. Take `⟨s, hs⟩` from `(hex t).mp h0`. Conclude with `⟨s, hs⟩`.
-/
theorem range_lTensor_iInf_le {B R M : Type} [CommRing B] [AddCommGroup R] [Module B R]
    [Module.Flat B R] [AddCommGroup M] [Module B M] {ι : Type} [Finite ι]
    (K : ι → Submodule B M) :
    ⨅ i, LinearMap.range (LinearMap.lTensor R (K i).subtype) ≤
      LinearMap.range (LinearMap.lTensor R (⨅ i, K i).subtype) := by
  classical
  cases nonempty_fintype ι
  intro t ht
  rw [Submodule.mem_iInf] at ht
  let φ : M →ₗ[B] (∀ i, M ⧸ K i) := LinearMap.pi (fun i => (K i).mkQ)
  have hexB : Function.Exact (⨅ i, K i).subtype φ := by
    rw [LinearMap.exact_iff, LinearMap.ker_pi, Submodule.range_subtype]
    simp only [Submodule.ker_mkQ]
  have hex := Module.Flat.lTensor_exact R hexB
  have hcomp : ∀ i (u : R ⊗[B] M), TensorProduct.piRight B B R (fun i => M ⧸ K i) (LinearMap.lTensor R φ u) i =
      LinearMap.lTensor R (K i).mkQ u := by
    intro i u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul r m => simp [φ]
    | add x y hx hy => simp_all
  have h0 : LinearMap.lTensor R φ t = 0 := by
    apply (TensorProduct.piRight B B R (fun i => M ⧸ K i)).injective
    rw [map_zero]
    funext i
    rw [hcomp i t, Pi.zero_apply]
    obtain ⟨s, hs⟩ := ht i
    rw [← hs]
    exact (lTensor_exact R (LinearMap.exact_subtype_mkQ (K i)) (Submodule.mkQ_surjective _) _).mpr
      ⟨s, rfl⟩
  obtain ⟨s, hs⟩ := (hex t).mp h0
  exact ⟨s, hs⟩

/- English proof (translation)
Rewrite using `[← Ideal.map_includeRight_eq (R := B) (A := R) I, Submodule.restrictScalars_mem]`. Set `e` to `(Algebra.TensorProduct.rid B R R).toRingEquiv`. Establish `he : (e : R ⊗[B] B →+* R).comp ((Algebra.TensorProduct.includeRight : B →ₐ[B] R ⊗[B] B) : B →+* R ⊗[B] B) = algebraMap B R`. Use extensionality with `b`. Simplify using `[e, Algebra.algebraMap_eq_smul_one]`.

Rewrite using `[← he, ← Ideal.map_map, Ideal.map_comap_of_equiv, Ideal.mem_comap]`. Both sides reduce to the same expression.
-/
theorem mem_map_algebraMap_iff {B R : Type} [CommRing B] [CommRing R] [Algebra B R]
    (I : Ideal B) (x : R) :
    x ∈ I.map (algebraMap B R) ↔
      x ⊗ₜ[B] (1 : B) ∈ LinearMap.range (LinearMap.lTensor R (Submodule.subtype (I.restrictScalars B))) := by
  rw [← Ideal.map_includeRight_eq (R := B) (A := R) I, Submodule.restrictScalars_mem]
  let e := (Algebra.TensorProduct.rid B R R).toRingEquiv
  have he : (e : R ⊗[B] B →+* R).comp
      ((Algebra.TensorProduct.includeRight : B →ₐ[B] R ⊗[B] B) : B →+* R ⊗[B] B) = algebraMap B R := by
    ext b
    simp [e, Algebra.algebraMap_eq_smul_one]
  rw [← he, ← Ideal.map_map, Ideal.map_comap_of_equiv, Ideal.mem_comap]
  rfl

/- English proof (translation)
Introduce `B R _ _ _ _ ι _ K x hx`. Rewrite using `[mem_map_algebraMap_iff]`. Establish `h` using `range_lTensor_iInf_le (R := R) (fun i => (K i).restrictScalars B)`. Establish `hK : (⨅ i, (K i).restrictScalars B) = (⨅ i, K i).restrictScalars B`. Use extensionality with `y`.

Simplify using the standard rewrite rules. Rewrite `h` using `[hK]`. Apply `h` to reduce the goal to its premises. Rewrite using `[Submodule.mem_iInf]`. Introduce `i`.

Conclude with `(mem_map_algebraMap_iff (K i) x).mp ((Submodule.mem_iInf _).mp hx i)`.
-/
theorem iInf_map_le_map_iInf : ∀ {B R : Type} [CommRing B] [CommRing R] [Algebra B R]
    [Module.Flat B R] {ι : Type} [Finite ι] (K : ι → Ideal B),
    ⨅ i, (K i).map (algebraMap B R) ≤ (⨅ i, K i).map (algebraMap B R) := by
  intro B R _ _ _ _ ι _ K x hx
  rw [mem_map_algebraMap_iff]
  have h := range_lTensor_iInf_le (R := R) (fun i => (K i).restrictScalars B)
  have hK : (⨅ i, (K i).restrictScalars B) = (⨅ i, K i).restrictScalars B := by
    ext y; simp
  rw [hK] at h
  apply h
  rw [Submodule.mem_iInf]
  intro i
  exact (mem_map_algebraMap_iff (K i) x).mp ((Submodule.mem_iInf _).mp hx i)

end GlobalTheory.FlatIdealInf
