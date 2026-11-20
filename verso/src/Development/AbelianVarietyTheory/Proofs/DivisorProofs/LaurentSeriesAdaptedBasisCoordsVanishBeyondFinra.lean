import Mathlib
open PowerSeries

namespace GlobalTheory

/- English proof (translation)
Establish `hr : Module.finrank K W ≤ n`. Use `Submodule.finrank_le W` as an intermediate fact. Simplify using `using this`. Use `set r := Module.finrank K W with hrdef`. Set `G : Matrix (Fin n) (Fin n) K` to `(g : Matrix (Fin n) (Fin n) R).map φ`.

Set `H : Matrix (Fin n) (Fin n) K` to `((g⁻¹ : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R).map φ`. Establish `hHG : H * G = 1`. Combine the equalities or inequalities in the displayed calculation. Set `e : Fin r → (Fin n → K)` to `fun i => Pi.single (Fin.castLE hr i) 1`. Set `v : Fin r → (Fin n → K)` to `fun i => fun b => G b (Fin.castLE hr i)`.

Establish `hHv : ∀ i, H.mulVec (v i) = e i`. Introduce `i`. Establish `: v i = G.mulVec (Pi.single (Fin.castLE hr i) 1)`. Use extensionality with `b`. Simplify using `[v, Matrix.mulVec_single]`.

Rewrite using `[this, Matrix.mulVec_mulVec, hHG, Matrix.one_mulVec]`. Establish `hcomp : (Matrix.toLin' H) ∘ v = e`. Use function extensionality and compare the values at `i`. Simplify using `only [Function.comp_apply, Matrix.toLin'_apply, hHv]`. Establish `hli : LinearIndependent K v`.

Apply `LinearIndependent.of_comp (Matrix.toLin' H)` to reduce the goal to its premises. Rewrite using `[hcomp]`. Conclude with `(Pi.linearIndependent_single_one (Fin n) K).comp _ (Fin.castLE_injective hr)`. Establish `hle : Submodule.span K (Set.range v) ≤ W`. Rewrite using `[Submodule.span_le, Set.range_subset_iff]`.

Introduce `i`. Conclude with `hg (Fin.castLE hr i) (by simp)`. Establish `heq : Submodule.span K (Set.range v) = W`. Apply `Submodule.eq_of_le_of_finrank_eq hle` to reduce the goal to its premises. Rewrite using `[finrank_span_eq_card hli, Fintype.card_fin]`.

Establish `hy' : (fun b => φ (y b)) ∈ Submodule.span K (Set.range v)` using `heq ▸ hy`. Establish `hmap : H.mulVec (fun b => φ (y b)) ∈ Submodule.span K (Set.range e)`. Use `Submodule.mem_map_of_mem (f := Matrix.toLin' H) hy'` as an intermediate fact. Rewrite `this` using `[Submodule.map_span, ← Set.range_comp, hcomp, Matrix.toLin'_apply]`. Conclude with `this`.

Establish `hker : Submodule.span K (Set.range e) ≤ LinearMap.ker (LinearMap.proj a)`. Rewrite using `[Submodule.span_le, Set.range_subset_iff]`. Introduce `i`. Simplify using `only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.proj_apply, e]`. Apply `Pi.single_eq_of_ne` to reduce the goal to its premises.

Introduce `h`. Establish `: ((Fin.castLE hr i : Fin n) : ℕ) = a` using `by rw [h]`. Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Establish `h0 : (H.mulVec (fun b => φ (y b))) a = 0` using `hker hmap`.

Establish `hcoe : φ ((((g⁻¹ : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R).mulVec y) a) = (H.mulVec (fun b => φ (y b))) a`. Rewrite using `[RingHom.map_mulVec]`. Both sides reduce to the same expression. Rewrite `hcoe` using `[h0]`. Conclude with `(injective_iff_map_eq_zero φ).mp hφ _ hcoe`.
-/
theorem inv_mulVec_coord_eq_zero_of_adapted_columns_injective {R K : Type} [CommRing R] [Field K] (φ : R →+* K)
    (hφ : Function.Injective φ) (n : ℕ) (W : Submodule K (Fin n → K))
    (g : (Matrix (Fin n) (Fin n) R)ˣ)
    (hg : ∀ j : Fin n, (j : ℕ) < Module.finrank K W →
      (fun a => φ ((g : Matrix (Fin n) (Fin n) R) a j)) ∈ W)
    (y : Fin n → R) (hy : (fun a => φ (y a)) ∈ W)
    (a : Fin n) (ha : Module.finrank K W ≤ (a : ℕ)) :
    (((g⁻¹ : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R).mulVec y) a = 0 := by
  classical
  have hr : Module.finrank K W ≤ n := by
    have := Submodule.finrank_le W
    simpa using this
  set r := Module.finrank K W with hrdef
  let G : Matrix (Fin n) (Fin n) K := (g : Matrix (Fin n) (Fin n) R).map φ
  let H : Matrix (Fin n) (Fin n) K := ((g⁻¹ : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R).map φ
  have hHG : H * G = 1 := by
    calc H * G = (RingHom.mapMatrix φ) (((g⁻¹ : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R) * (g : Matrix (Fin n) (Fin n) R)) :=
          ((RingHom.mapMatrix φ).map_mul _ _).symm
      _ = 1 := by rw [Units.inv_mul, map_one]
  let e : Fin r → (Fin n → K) := fun i => Pi.single (Fin.castLE hr i) 1
  let v : Fin r → (Fin n → K) := fun i => fun b => G b (Fin.castLE hr i)
  have hHv : ∀ i, H.mulVec (v i) = e i := by
    intro i
    have : v i = G.mulVec (Pi.single (Fin.castLE hr i) 1) := by
      ext b; simp [v, Matrix.mulVec_single]
    rw [this, Matrix.mulVec_mulVec, hHG, Matrix.one_mulVec]
  have hcomp : (Matrix.toLin' H) ∘ v = e := by
    funext i; simp only [Function.comp_apply, Matrix.toLin'_apply, hHv]
  have hli : LinearIndependent K v := by
    apply LinearIndependent.of_comp (Matrix.toLin' H)
    rw [hcomp]
    exact (Pi.linearIndependent_single_one (Fin n) K).comp _ (Fin.castLE_injective hr)
  have hle : Submodule.span K (Set.range v) ≤ W := by
    rw [Submodule.span_le, Set.range_subset_iff]
    intro i
    exact hg (Fin.castLE hr i) (by simp)
  have heq : Submodule.span K (Set.range v) = W := by
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hy' : (fun b => φ (y b)) ∈ Submodule.span K (Set.range v) := heq ▸ hy
  have hmap : H.mulVec (fun b => φ (y b)) ∈ Submodule.span K (Set.range e) := by
    have := Submodule.mem_map_of_mem (f := Matrix.toLin' H) hy'
    rw [Submodule.map_span, ← Set.range_comp, hcomp, Matrix.toLin'_apply] at this
    exact this
  have hker : Submodule.span K (Set.range e) ≤ LinearMap.ker (LinearMap.proj a) := by
    rw [Submodule.span_le, Set.range_subset_iff]
    intro i
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.proj_apply, e]
    apply Pi.single_eq_of_ne
    intro h
    have : ((Fin.castLE hr i : Fin n) : ℕ) = a := by rw [h]
    simp at this
    omega
  have h0 : (H.mulVec (fun b => φ (y b))) a = 0 := hker hmap
  have hcoe : φ ((((g⁻¹ : (Matrix (Fin n) (Fin n) R)ˣ) : Matrix (Fin n) (Fin n) R).mulVec y) a) =
      (H.mulVec (fun b => φ (y b))) a := by
    rw [RingHom.map_mulVec]
    rfl
  rw [h0] at hcoe
  exact (injective_iff_map_eq_zero φ).mp hφ _ hcoe

/- English proof (translation)
The claim follows from `inv_mulVec_coord_eq_zero_of_adapted_columns_injective (HahnSeries.ofPowerSeries ℤ F) HahnSeries.ofPowerSeries_injective n W g hg y hy a ha`.
-/
theorem adapted_coords_vanish (F : Type) [Field F] (n : ℕ)
    (W : Submodule (LaurentSeries F) (Fin n → LaurentSeries F))
    (g : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ)
    (hg : ∀ j : Fin n, (j : ℕ) < Module.finrank (LaurentSeries F) W →
      (fun a => (((g : Matrix (Fin n) (Fin n) (PowerSeries F)) a j : PowerSeries F) : LaurentSeries F)) ∈ W)
    (y : Fin n → PowerSeries F) (hy : (fun a => ((y a : PowerSeries F) : LaurentSeries F)) ∈ W)
    (a : Fin n) (ha : Module.finrank (LaurentSeries F) W ≤ (a : ℕ)) :
    (((g⁻¹ : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ) : Matrix (Fin n) (Fin n) (PowerSeries F)).mulVec y) a = 0 :=
  inv_mulVec_coord_eq_zero_of_adapted_columns_injective (HahnSeries.ofPowerSeries ℤ F) HahnSeries.ofPowerSeries_injective n W g hg y hy a ha

/- English proof (translation)
Introduce `F _ n W g hg y hy a ha` and use `adapted_coords_vanish F n W g hg y hy a ha`.
-/
theorem adapted_coords_vanish_stmt : ∀ (F : Type) [Field F] (n : ℕ) (W : Submodule (LaurentSeries F) (Fin n → LaurentSeries F)) (g : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ), (∀ j : Fin n, (j : ℕ) < Module.finrank (LaurentSeries F) W → (fun a => (((g : Matrix (Fin n) (Fin n) (PowerSeries F)) a j : PowerSeries F) : LaurentSeries F)) ∈ W) → ∀ y : Fin n → PowerSeries F, (fun a => ((y a : PowerSeries F) : LaurentSeries F)) ∈ W → ∀ a : Fin n, Module.finrank (LaurentSeries F) W ≤ (a : ℕ) → (((g⁻¹ : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ) : Matrix (Fin n) (Fin n) (PowerSeries F)).mulVec y) a = 0 :=
  fun F _ n W g hg y hy a ha => adapted_coords_vanish F n W g hg y hy a ha

end GlobalTheory
