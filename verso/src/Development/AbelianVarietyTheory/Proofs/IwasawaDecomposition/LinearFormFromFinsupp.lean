import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdConeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStrictIff
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

noncomputable section

namespace GlobalTheory.PolCell

variable {X : Type} [AddCommGroup X]

/- English proof (translation)
Rewrite using `[linW_apply, Finsupp.sum_single_index (by simp)]`.
-/
theorem linW_single_apply (p : X × X) (k : ℤ) (β : LinearMap.BilinForm ℤ X) :
    linW (Finsupp.single p k) β = k * β p.1 p.2 := by
  rw [linW_apply, Finsupp.sum_single_index (by simp)]

/- English proof (translation)
Simplify using `only [linW_apply]`. Conclude with `Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)`.
-/
theorem linW_add_apply (w v : (X × X) →₀ ℤ) (β : LinearMap.BilinForm ℤ X) :
    linW (w + v) β = linW w β + linW v β := by
  simp only [linW_apply]
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [linW_apply]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, linW_add_apply, ih]`.
-/
theorem linW_finset_sum_apply {ι : Type} (s : Finset ι) (g : ι → (X × X) →₀ ℤ) (β : LinearMap.BilinForm ℤ X) :
    linW (∑ i ∈ s, g i) β = ∑ i ∈ s, linW (g i) β := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [linW_apply]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, linW_add_apply, ih]

/- English proof (translation)
Take `⟨n, hn⟩` from `(Submodule.mem_torsion_iff t).mp ht`. Rewrite `hn` using `[Submonoid.smul_def]`. Establish `h` using `LinearMap.map_smul₂ β (n : ℤ) t y`. Rewrite `h` using `[hn, map_zero, LinearMap.zero_apply, eq_comm, smul_eq_zero]`. Conclude with `h.resolve_left (nonZeroDivisors.coe_ne_zero n)`.
-/
theorem bilin_eq_zero_of_mem_torsion_left (β : LinearMap.BilinForm ℤ X) {t : X}
    (ht : t ∈ Submodule.torsion ℤ X) (y : X) : β t y = 0 := by
  obtain ⟨n, hn⟩ := (Submodule.mem_torsion_iff t).mp ht
  rw [Submonoid.smul_def] at hn
  have h := LinearMap.map_smul₂ β (n : ℤ) t y
  rw [hn, map_zero, LinearMap.zero_apply, eq_comm, smul_eq_zero] at h
  exact h.resolve_left (nonZeroDivisors.coe_ne_zero n)

/- English proof (translation)
Take `⟨n, hn⟩` from `(Submodule.mem_torsion_iff t).mp ht`. Rewrite `hn` using `[Submonoid.smul_def]`. Establish `h` using `(β x).map_smul (n : ℤ) t`. Rewrite `h` using `[hn, map_zero, eq_comm, smul_eq_zero]`. Conclude with `h.resolve_left (nonZeroDivisors.coe_ne_zero n)`.
-/
theorem bilin_eq_zero_of_mem_torsion_right (β : LinearMap.BilinForm ℤ X) (x : X) {t : X}
    (ht : t ∈ Submodule.torsion ℤ X) : β x t = 0 := by
  obtain ⟨n, hn⟩ := (Submodule.mem_torsion_iff t).mp ht
  rw [Submonoid.smul_def] at hn
  have h := (β x).map_smul (n : ℤ) t
  rw [hn, map_zero, eq_comm, smul_eq_zero] at h
  exact h.resolve_left (nonZeroDivisors.coe_ne_zero n)

/- English proof (translation)
Introduce `X _ _ ℓ`. Set `T` to `Submodule.torsion ℤ X`. Set `b` to `Module.Free.chooseBasis ℤ (X ⧸ T)`. Set `e : Module.Free.ChooseBasisIndex ℤ (X ⧸ T) → X` to `fun i => (T.mkQ_surjective (b i)).choose`. Establish `he : ∀ i, T.mkQ (e i) = b i` using `fun i => (T.mkQ_surjective (b i)).choose_spec`.

Set `c : Module.Free.ChooseBasisIndex ℤ (X ⧸ T) → X →ₗ[ℤ] ℤ` to `fun i => (b.coord i).comp T.mkQ`. Establish `hdec : ∀ x, x - ∑ i, c i x • e i ∈ T`. Introduce `x`. Use `(Submodule.Quotient.mk_eq_zero T).mp ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `T.mkQ _ = 0`.

Rewrite using `[map_sub, map_sum]`. Simplify using `only [map_smul, he, c, LinearMap.comp_apply, Module.Basis.coord_apply]`. Rewrite using `[b.sum_repr, sub_self]`. Establish `hβ : ∀ β : LinearMap.BilinForm ℤ X, β = ∑ i, ∑ j, β (e i) (e j) • (c i).smulRight (c j)`. Introduce `β`.

Use extensionality with `x y`. Establish `h1 : β x y = β (∑ i, c i x • e i) y`. Use `bilin_eq_zero_of_mem_torsion_left β (hdec x) y` as an intermediate fact. Rewrite `this` using `[map_sub, LinearMap.sub_apply, sub_eq_zero]`. Then use the resulting hypothesis. Establish `h2 : ∀ x', β x' y = β x' (∑ j, c j y • e j)`.

Introduce `x'`. Use `bilin_eq_zero_of_mem_torsion_right β x' (hdec y)` as an intermediate fact. Rewrite `this` using `[map_sub, sub_eq_zero]`. Then use the resulting hypothesis. Rewrite using `[h1, h2]`. Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, smul_eq_mul]`.

Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`. Use `⟨∑ i, ∑ j, Finsupp.single (e i, e j) (ℓ ((c i).smulRight (c j))), ?_⟩` and prove the remaining obligations. Use extensionality with `β`.

Rewrite using `[linW_finset_sum_apply]`. Use `conv_rhs => rw [hβ β]`. Simplify using `only [map_sum, map_smul, smul_eq_mul, linW_finset_sum_apply, linW_single_apply]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem exists_linW_eq : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
    ∃ w : (X × X) →₀ ℤ, linW w = ℓ := by
  intro X _ _ ℓ
  classical
  let T := Submodule.torsion ℤ X
  let b := Module.Free.chooseBasis ℤ (X ⧸ T)
  let e : Module.Free.ChooseBasisIndex ℤ (X ⧸ T) → X := fun i => (T.mkQ_surjective (b i)).choose
  have he : ∀ i, T.mkQ (e i) = b i := fun i => (T.mkQ_surjective (b i)).choose_spec
  let c : Module.Free.ChooseBasisIndex ℤ (X ⧸ T) → X →ₗ[ℤ] ℤ := fun i => (b.coord i).comp T.mkQ
  have hdec : ∀ x, x - ∑ i, c i x • e i ∈ T := by
    intro x
    refine (Submodule.Quotient.mk_eq_zero T).mp ?_
    change T.mkQ _ = 0
    rw [map_sub, map_sum]
    simp only [map_smul, he, c, LinearMap.comp_apply, Module.Basis.coord_apply]
    rw [b.sum_repr, sub_self]
  have hβ : ∀ β : LinearMap.BilinForm ℤ X,
      β = ∑ i, ∑ j, β (e i) (e j) • (c i).smulRight (c j) := by
    intro β
    ext x y
    have h1 : β x y = β (∑ i, c i x • e i) y := by
      have := bilin_eq_zero_of_mem_torsion_left β (hdec x) y
      rwa [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
    have h2 : ∀ x', β x' y = β x' (∑ j, c j y • e j) := by
      intro x'
      have := bilin_eq_zero_of_mem_torsion_right β x' (hdec y)
      rwa [map_sub, sub_eq_zero] at this
    rw [h1, h2]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, smul_eq_mul]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  refine ⟨∑ i, ∑ j, Finsupp.single (e i, e j) (ℓ ((c i).smulRight (c j))), ?_⟩
  ext β
  rw [linW_finset_sum_apply]
  conv_rhs => rw [hβ β]
  simp only [map_sum, map_smul, smul_eq_mul, linW_finset_sum_apply, linW_single_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.PolCell
