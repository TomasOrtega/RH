import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmBilinFormEqZeroOfWeightedQuadraticSumLiftsStatement
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
open Matrix

namespace GlobalTheory.Poinc

/- English proof (translation)
Use `⟨∏ k, (f k).den, Finset.prod_pos (fun k _ => (f k).den_pos), fun k => (f k).num * ((∏ k, (f k).den) / (f k).den : ℕ), fun k => ?_⟩` and prove the remaining obligations. Take `⟨m, hm⟩ : (f k).den ∣ ∏ k, (f k).den` from `Finset.dvd_prod_of_mem _ (Finset.mem_univ k)`. Simplify using `only`. Rewrite using `[hm, Nat.mul_div_cancel_left _ (f k).den_pos]`. Use `push_cast`.

Rewrite using `[← Rat.mul_den_eq_num]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_pos_nat_mul_eq_int_family {κ : Type} [Fintype κ] (f : κ → ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∃ z : κ → ℤ, ∀ k, (z k : ℚ) = D * f k := by
  classical
  refine ⟨∏ k, (f k).den, Finset.prod_pos (fun k _ => (f k).den_pos),
    fun k => (f k).num * ((∏ k, (f k).den) / (f k).den : ℕ), fun k => ?_⟩
  obtain ⟨m, hm⟩ : (f k).den ∣ ∏ k, (f k).den := Finset.dvd_prod_of_mem _ (Finset.mem_univ k)
  dsimp only
  rw [hm, Nat.mul_div_cancel_left _ (f k).den_pos]
  push_cast
  rw [← Rat.mul_den_eq_num]
  ring

/- English proof (translation)
Take `⟨D, hD, z, hz⟩` from `exists_pos_nat_mul_eq_int_family x`. Establish `h1 : A *ᵥ z = 0`. Use function extensionality and compare the values at `i`. Apply `Int.cast_injective (α := ℚ)` to reduce the goal to its premises. Use `congrFun hx i` as an intermediate fact.

Simplify using `only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at this ⊢`. Use `push_cast`. Simplify using `only [hz, mul_left_comm _ (D : ℚ), ← Finset.mul_sum, this, mul_zero]`. Establish `h2` using `hA z h1`. Use function extensionality and compare the values at `j`.

Use `hz j` as an intermediate fact. Rewrite `this` using `[h2, Pi.zero_apply, Int.cast_zero, eq_comm, mul_eq_zero]`. Break down `this with h | h` into its components or cases. Conclude with `absurd h (Nat.cast_ne_zero.mpr hD.ne')`. Conclude with `h`.
-/
theorem int_matrix_rat_kernel_eq_zero {ι I : Type} [Fintype ι] [Fintype I] (A : Matrix ι I ℤ)
    (hA : ∀ x, A *ᵥ x = 0 → x = 0) (x : I → ℚ) (hx : A.map (Int.cast : ℤ → ℚ) *ᵥ x = 0) : x = 0 := by
  obtain ⟨D, hD, z, hz⟩ := exists_pos_nat_mul_eq_int_family x
  have h1 : A *ᵥ z = 0 := by
    funext i
    apply Int.cast_injective (α := ℚ)
    have := congrFun hx i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at this ⊢
    push_cast
    simp only [hz, mul_left_comm _ (D : ℚ), ← Finset.mul_sum, this, mul_zero]
  have h2 := hA z h1
  funext j
  have := hz j
  rw [h2, Pi.zero_apply, Int.cast_zero, eq_comm, mul_eq_zero] at this
  rcases this with h | h
  · exact absurd h (Nat.cast_ne_zero.mpr hD.ne')
  · exact h

/- English proof (translation)
Use `set Aq := A.map (Int.cast : ℤ → ℚ) with hAq`. Establish `hinj : Function.Injective Aq.mulVecLin`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `x hx`. Conclude with `int_matrix_rat_kernel_eq_zero A hA x hx`.

Set `f : Module.Dual ℚ (I → ℚ)` to `{ toFun := fun x => (fun i => (w i : ℚ)) ⬝ᵥ x map_add' := fun x y => dotProduct_add _ _ _ map_smul' := fun c x => by simp [dotProduct_smul] }`. Take `⟨l, hl⟩` from `LinearMap.dualMap_surjective_of_injective hinj f`. Use `set lv : ι → ℚ := fun c => l (fun j => if c = j then 1 else 0) with hlvdef`. Establish `hlv : ∀ y, l y = lv ⬝ᵥ y`. Introduce `y`.

Rewrite using `[LinearMap.pi_apply_eq_sum_univ l y]`. Simplify using `[dotProduct, lv, mul_comm]`. Establish `key : ∀ i, (w i : ℚ) = (lv ᵥ* Aq) i`. Introduce `i`. Use `LinearMap.congr_fun hl (Pi.single i 1)` as an intermediate fact.

Simplify using `only [LinearMap.dualMap_apply, Matrix.mulVecLin_apply, hlv] at this`. Rewrite `this` using `[Matrix.dotProduct_mulVec, dotProduct_single, mul_one]`. Rewrite using `[this]`. Simplify using `[f, dotProduct_single]`. Take `⟨D, hD, ν, hν⟩` from `exists_pos_nat_mul_eq_int_family lv`.

Use `⟨D, hD, ν, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Apply `Int.cast_injective (α := ℚ)` to reduce the goal to its premises. Simplify using `only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul]`. Use `push_cast`.

Rewrite using `[key i]`. Simplify using `only [Matrix.vecMul, dotProduct, hν, Aq, Matrix.map_apply, Finset.mul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Use `intros`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_vecMul_eq_nat_smul {ι I : Type} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]
    (A : Matrix ι I ℤ) (hA : ∀ x, A *ᵥ x = 0 → x = 0) (w : I → ℤ) :
    ∃ D : ℕ, 0 < D ∧ ∃ ν : ι → ℤ, ν ᵥ* A = (D : ℤ) • w := by
  set Aq := A.map (Int.cast : ℤ → ℚ) with hAq
  have hinj : Function.Injective Aq.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact int_matrix_rat_kernel_eq_zero A hA x hx
  let f : Module.Dual ℚ (I → ℚ) :=
    { toFun := fun x => (fun i => (w i : ℚ)) ⬝ᵥ x
      map_add' := fun x y => dotProduct_add _ _ _
      map_smul' := fun c x => by simp [dotProduct_smul] }
  obtain ⟨l, hl⟩ := LinearMap.dualMap_surjective_of_injective hinj f
  set lv : ι → ℚ := fun c => l (fun j => if c = j then 1 else 0) with hlvdef
  have hlv : ∀ y, l y = lv ⬝ᵥ y := by
    intro y
    rw [LinearMap.pi_apply_eq_sum_univ l y]
    simp [dotProduct, lv, mul_comm]
  have key : ∀ i, (w i : ℚ) = (lv ᵥ* Aq) i := by
    intro i
    have := LinearMap.congr_fun hl (Pi.single i 1)
    simp only [LinearMap.dualMap_apply, Matrix.mulVecLin_apply, hlv] at this
    rw [Matrix.dotProduct_mulVec, dotProduct_single, mul_one] at this
    rw [this]
    simp [f, dotProduct_single]
  obtain ⟨D, hD, ν, hν⟩ := exists_pos_nat_mul_eq_int_family lv
  refine ⟨D, hD, ν, ?_⟩
  funext i
  apply Int.cast_injective (α := ℚ)
  simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [key i]
  simp only [Matrix.vecMul, dotProduct, hν, Aq, Matrix.map_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros
  ring

/- English proof (translation)
Use `set e := (Module.Free.chooseBasis ℤ M).equivFun with he`. Use `set A := LinearMap.toMatrix' (g ∘ₗ e.symm.toLinearMap) with hAdef`. Establish `hA : ∀ x, A *ᵥ x = 0 → x = 0`. Introduce `x hx`. Rewrite `hx` using `[hAdef, LinearMap.toMatrix'_mulVec]`.

Establish `h` using `hg (hx.trans (map_zero g).symm)`. Simplify using `using h`. Take `⟨D, hD, ν, hν⟩` from `exists_vecMul_eq_nat_smul A hA (fun i => w (e.symm (fun j => if i = j then 1 else 0)))`. Use `⟨D, hD, ν, fun x => ?_⟩` and prove the remaining obligations. Establish `h1 : g x = A *ᵥ e x` using `by rw [hAdef, LinearMap.toMatrix'_mulVec]; simp`.

Establish `h2 : w x = ∑ i, e x i * w (e.symm (fun j => if i = j then 1 else 0))`. Use `LinearMap.pi_apply_eq_sum_univ (w ∘ₗ e.symm.toLinearMap) (e x)` as an intermediate fact. Simplify using `using this`. Establish `h3 : ∑ c, ν c * g x c = ν ⬝ᵥ (A *ᵥ e x)` using `by rw [h1]; rfl`. Rewrite using `[h3, Matrix.dotProduct_mulVec, hν, h2]`.

Simplify using `[dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]`.
-/
theorem exists_nat_mul_eq_sum_of_injective {M ι : Type} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    [Fintype ι] [DecidableEq ι] (g : M →ₗ[ℤ] (ι → ℤ)) (hg : Function.Injective g) (w : M →ₗ[ℤ] ℤ) :
    ∃ D : ℕ, 0 < D ∧ ∃ ν : ι → ℤ, ∀ x, (D : ℤ) * w x = ∑ c, ν c * g x c := by
  classical
  set e := (Module.Free.chooseBasis ℤ M).equivFun with he
  set A := LinearMap.toMatrix' (g ∘ₗ e.symm.toLinearMap) with hAdef
  have hA : ∀ x, A *ᵥ x = 0 → x = 0 := by
    intro x hx
    rw [hAdef, LinearMap.toMatrix'_mulVec] at hx
    have h := hg (hx.trans (map_zero g).symm)
    simpa using h
  obtain ⟨D, hD, ν, hν⟩ :=
    exists_vecMul_eq_nat_smul A hA (fun i => w (e.symm (fun j => if i = j then 1 else 0)))
  refine ⟨D, hD, ν, fun x => ?_⟩
  have h1 : g x = A *ᵥ e x := by rw [hAdef, LinearMap.toMatrix'_mulVec]; simp
  have h2 : w x = ∑ i, e x i * w (e.symm (fun j => if i = j then 1 else 0)) := by
    have := LinearMap.pi_apply_eq_sum_univ (w ∘ₗ e.symm.toLinearMap) (e x)
    simpa using this
  have h3 : ∑ c, ν c * g x c = ν ⬝ᵥ (A *ᵥ e x) := by rw [h1]; rfl
  rw [h3, Matrix.dotProduct_mulVec, hν, h2]
  simp [dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]

/- English proof (translation)
Introduce `W hW N hN0 hN hε r μ hμ ℓ`. Set `S : Submodule ℤ (LinearMap.BilinForm ℤ (Fin r → ℤ))` to `{ carrier := {b | ∀ x y, b x y = b y x} add_mem' := by intro a b ha hb x y; simp [ha x y, hb x y] zero_mem' := by intro x y; simp smul_mem' := by intro c b hb x y; simp [hb x y] }`. Set `Φ : LinearMap.BilinForm ℤ (Fin r → ℤ) →ₗ[ℤ] ((Fin 8 → Fin r → ZMod N) → ℤ)` to `{ toFun := fun b c => qW W b (μ c) map_add' := by intro a b; funext c; simp [qW, mul_add, Finset.sum_add_distrib] map_smul' := by intro k b; funext c; simp [qW, Finset.mul_sum, mul_left_comm] }`. Establish `hinj : Function.Injective (Φ ∘ₗ S.subtype)`. Introduce `x y hxy`.

Apply `Subtype.ext` to reduce the goal to its premises. Establish `hs : ∀ u v, ((x : LinearMap.BilinForm ℤ (Fin r → ℤ)) - (y : LinearMap.BilinForm ℤ (Fin r → ℤ))) u v = ((x : LinearMap.BilinForm ℤ (Fin r → ℤ)) - (y : LinearMap.BilinForm ℤ (Fin r → ℤ))) v u`. Introduce `u v`. Simplify using `[x.2 u v, y.2 u v]`. Establish `h0 : ∀ c, qW W ((x : LinearMap.BilinForm ℤ (Fin r → ℤ)) - (y : LinearMap.BilinForm ℤ (Fin r → ℤ))) (μ c) = 0`.

Introduce `c`. Use `congrFun hxy c` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.coe_mk, AddHom.coe_mk, Φ] at this`. Simplify using `only [qW, LinearMap.sub_apply, mul_sub, Finset.sum_sub_distrib] at this ⊢`. Rewrite using `[this, sub_self]`.

Conclude with `sub_eq_zero.mp (GlobalTheory.T.symm_bilinForm_eq_zero_of_weightedQuadraticSum_lifts W hW N hN r hε μ hμ _ hs h0)`. Take `⟨D, hD, ν, hν⟩` from `exists_nat_mul_eq_sum_of_injective (Φ ∘ₗ S.subtype) hinj (ℓ ∘ₗ S.subtype)`. Conclude with `⟨D, ν, hD, fun b hb => hν ⟨b, hb⟩⟩`.
-/
theorem linForm_eq_sum_qW_lifts : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N →
    (∃ ε : Fin 8 → ℤ, Nat.Coprime N (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs)) → ∀ r : ℕ,
    ∀ μ : ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) →
    ∀ ℓ : LinearMap.BilinForm ℤ (Fin r → ℤ) →ₗ[ℤ] ℤ, ∃ (D : ℕ) (ν : (Fin 8 → Fin r → ZMod N) → ℤ), 0 < D ∧
      ∀ b : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b x y = b y x) → (D : ℤ) * ℓ b = ∑ c, ν c * qW W b (μ c) := by
  intro W hW N hN0 hN hε r μ hμ ℓ
  let S : Submodule ℤ (LinearMap.BilinForm ℤ (Fin r → ℤ)) :=
    { carrier := {b | ∀ x y, b x y = b y x}
      add_mem' := by intro a b ha hb x y; simp [ha x y, hb x y]
      zero_mem' := by intro x y; simp
      smul_mem' := by intro c b hb x y; simp [hb x y] }
  let Φ : LinearMap.BilinForm ℤ (Fin r → ℤ) →ₗ[ℤ] ((Fin 8 → Fin r → ZMod N) → ℤ) :=
    { toFun := fun b c => qW W b (μ c)
      map_add' := by intro a b; funext c; simp [qW, mul_add, Finset.sum_add_distrib]
      map_smul' := by intro k b; funext c; simp [qW, Finset.mul_sum, mul_left_comm] }
  have hinj : Function.Injective (Φ ∘ₗ S.subtype) := by
    intro x y hxy
    apply Subtype.ext
    have hs : ∀ u v, ((x : LinearMap.BilinForm ℤ (Fin r → ℤ)) - (y : LinearMap.BilinForm ℤ (Fin r → ℤ))) u v = ((x : LinearMap.BilinForm ℤ (Fin r → ℤ)) - (y : LinearMap.BilinForm ℤ (Fin r → ℤ))) v u := by
      intro u v; simp [x.2 u v, y.2 u v]
    have h0 : ∀ c, qW W ((x : LinearMap.BilinForm ℤ (Fin r → ℤ)) - (y : LinearMap.BilinForm ℤ (Fin r → ℤ))) (μ c) = 0 := by
      intro c
      have := congrFun hxy c
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.coe_mk, AddHom.coe_mk, Φ] at this
      simp only [qW, LinearMap.sub_apply, mul_sub, Finset.sum_sub_distrib] at this ⊢
      rw [this, sub_self]
    exact sub_eq_zero.mp (GlobalTheory.T.symm_bilinForm_eq_zero_of_weightedQuadraticSum_lifts W hW N hN r hε μ hμ _ hs h0)
  obtain ⟨D, hD, ν, hν⟩ := exists_nat_mul_eq_sum_of_injective (Φ ∘ₗ S.subtype) hinj (ℓ ∘ₗ S.subtype)
  exact ⟨D, ν, hD, fun b hb => hν ⟨b, hb⟩⟩

end GlobalTheory.Poinc
