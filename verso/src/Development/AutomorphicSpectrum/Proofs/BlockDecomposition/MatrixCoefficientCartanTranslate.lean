import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.CongruenceCoef

/- English proof (translation)
Take `⟨a, rfl⟩` from `hp`. Take `⟨b, hb, rfl⟩` from `hx`. Use `⟨a * b * a⁻¹, ?_, by simp only [map_mul, map_inv]⟩` and prove the remaining obligations. Conclude with `(MonoidHom.normal_ker _).conj_mem b hb a`.
-/
theorem conj_mem_Km (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N m : ℕ) {p x : GL (Fin N) k}
    (hp : p ∈ KO k (Fin N)) (hx : x ∈ Zls.Km k N m) : p * x * p⁻¹ ∈ Zls.Km k N m := by
  obtain ⟨a, rfl⟩ := hp
  obtain ⟨b, hb, rfl⟩ := hx
  refine ⟨a * b * a⁻¹, ?_, by simp only [map_mul, map_inv]⟩
  exact (MonoidHom.normal_ker _).conj_mem b hb a

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hv h hh`. Use `hv ⟨h, hh⟩` as an intermediate fact. Simplify using `using this`. Introduce `hv h`.

Simplify using `using hv h h.2`.
-/
theorem mem_fixed_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (H : Subgroup G) (v : V) :
    v ∈ fixed π H ↔ ∀ h ∈ H, π h v = v := by
  constructor
  · intro hv h hh
    have := hv ⟨h, hh⟩
    simpa using this
  · intro hv h
    simpa using hv h h.2

/- English proof (translation)
Introduce `k _ _ _ _ N V _ _ π m v hv l hl p1 p2 hp1 hp2`. Establish `hv'` using `(mem_fixed_iff π _ v).1 hv`. Establish `h1 : ∀ y ∈ Zls.Km k N m, π y (π p2 v) = π p2 v`. Introduce `y hy`. Establish `hc : p2⁻¹ * y * p2⁻¹⁻¹ ∈ Zls.Km k N m` using `conj_mem_Km k N m (inv_mem hp2) hy`.

Establish `e : y * p2 = p2 * (p2⁻¹ * y * p2⁻¹⁻¹)` using `by group`. Establish `h` using `hv' _ hc`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : ∀ x ∈ Zls.Km k N m, (l ∘ₗ π p1) ∘ₗ π x = l ∘ₗ π p1`. Introduce `x hx`.

Establish `hc : p1 * x * p1⁻¹ ∈ Zls.Km k N m` using `conj_mem_Km k N m hp1 hx`. Establish `e : p1 * x = (p1 * x * p1⁻¹) * p1` using `by group`. Establish `h` using `hl _ hc`. Use extensionality with `w`. Establish `hw` using `LinearMap.congr_fun h (π p1 w)`.

Simplify using `only [LinearMap.comp_apply] at hw ⊢`. Combine the equalities or inequalities in the displayed calculation. Use `⟨(mem_fixed_iff π _ _).2 h1, h2, ?_⟩` and prove the remaining obligations. Introduce `D x hx y hy`. Establish `h3` using `LinearMap.congr_fun (h2 x hx) (π D (π p2 v))`.

Simplify using `only [LinearMap.comp_apply] at h3`. Establish `e : π (p1 * x * D * y * p2) v = π p1 (π x (π D (π y (π p2 v))))`. Simplify using `only [map_mul, Module.End.mul_apply]`. Rewrite using `[e, h1 y hy, h3]`. Simplify using `only [LinearMap.comp_apply]`.
-/
theorem coef_const_translated_double_coset :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), ∀ (m : ℕ) (v : V), v ∈ fixed π (Zls.Km k N m) → ∀ l : Module.Dual ℂ V, (∀ x ∈ Zls.Km k N m, l ∘ₗ π x = l) → ∀ (p1 p2 : GL (Fin N) k), p1 ∈ KO k (Fin N) → p2 ∈ KO k (Fin N) → (π p2 v ∈ fixed π (Zls.Km k N m)) ∧ (∀ x ∈ Zls.Km k N m, (l ∘ₗ π p1) ∘ₗ π x = l ∘ₗ π p1) ∧ ∀ (D : GL (Fin N) k), ∀ x ∈ Zls.Km k N m, ∀ y ∈ Zls.Km k N m, l (π (p1 * x * D * y * p2) v) = (l ∘ₗ π p1) (π D (π p2 v)) := by
  intro k _ _ _ _ N V _ _ π m v hv l hl p1 p2 hp1 hp2
  have hv' := (mem_fixed_iff π _ v).1 hv
  have h1 : ∀ y ∈ Zls.Km k N m, π y (π p2 v) = π p2 v := by
    intro y hy
    have hc : p2⁻¹ * y * p2⁻¹⁻¹ ∈ Zls.Km k N m := conj_mem_Km k N m (inv_mem hp2) hy
    have e : y * p2 = p2 * (p2⁻¹ * y * p2⁻¹⁻¹) := by group
    have h := hv' _ hc
    calc π y (π p2 v) = π (y * p2) v := by rw [map_mul, Module.End.mul_apply]
      _ = π p2 (π (p2⁻¹ * y * p2⁻¹⁻¹) v) := by rw [e, map_mul, Module.End.mul_apply]
      _ = π p2 v := by rw [h]
  have h2 : ∀ x ∈ Zls.Km k N m, (l ∘ₗ π p1) ∘ₗ π x = l ∘ₗ π p1 := by
    intro x hx
    have hc : p1 * x * p1⁻¹ ∈ Zls.Km k N m := conj_mem_Km k N m hp1 hx
    have e : p1 * x = (p1 * x * p1⁻¹) * p1 := by group
    have h := hl _ hc
    ext w
    have hw := LinearMap.congr_fun h (π p1 w)
    simp only [LinearMap.comp_apply] at hw ⊢
    calc l (π p1 (π x w)) = l (π (p1 * x) w) := by rw [map_mul, Module.End.mul_apply]
      _ = l (π (p1 * x * p1⁻¹) (π p1 w)) := by rw [e, map_mul, Module.End.mul_apply]; simp
      _ = l (π p1 w) := hw
  refine ⟨(mem_fixed_iff π _ _).2 h1, h2, ?_⟩
  intro D x hx y hy
  have h3 := LinearMap.congr_fun (h2 x hx) (π D (π p2 v))
  simp only [LinearMap.comp_apply] at h3
  have e : π (p1 * x * D * y * p2) v = π p1 (π x (π D (π y (π p2 v)))) := by
    simp only [map_mul, Module.End.mul_apply]
  rw [e, h1 y hy, h3]
  simp only [LinearMap.comp_apply]

end GlobalTheory.CompanionTheory.CongruenceCoef
