import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Use `set n := Module.finrank K V with hn`. Establish `h0 : ∀ a b x : V, Function.update ![a, b] 0 x = ![x, b]`. Apply the tactic sequence `intro a b x; ext i; fin_cases i <;> rfl`. Establish `h1 : ∀ a b x : V, Function.update ![a, b] 1 x = ![a, x]`. Apply the tactic sequence `intro a b x; ext i; fin_cases i <;> rfl`.

Set `wb : V →ₗ[K] V →ₗ[K] ⋀[K]^2 V` to `LinearMap.mk₂ K (fun a b => exteriorPower.ιMulti K 2 ![a, b]) (by intro a₁ a₂ b`. Rewrite using `[← h0 a₁ b (a₁ + a₂), AlternatingMap.map_update_add]`. Simplify using `only [h0])`. Use the proof step `(by intro c a b`. Rewrite using `[← h0 a b (c • a), AlternatingMap.map_update_smul]`.

Simplify using `only [h0])`. Use the proof step `(by intro a b₁ b₂`. Rewrite using `[← h1 a b₁ (b₁ + b₂), AlternatingMap.map_update_add]`. Simplify using `only [h1])`. Use the proof step `(by intro c a b`.

Rewrite using `[← h1 a b (c • b), AlternatingMap.map_update_smul]`. Simplify using `only [h1])`. Set `π : V ⊗[K] V →ₗ[K] ⋀[K]^2 V` to `TensorProduct.lift wb`. Establish `hπt : ∀ a b, π (a ⊗ₜ b) = exteriorPower.ιMulti K 2 ![a, b]`. Introduce `a b`.

Simplify using `[π, wb]`. Establish `hπ : Function.Surjective π`. Rewrite using `[← LinearMap.range_eq_top, eq_top_iff, ← exteriorPower.ιMulti_span K 2 V, Submodule.span_le]`. Introduce and unpack `_ ⟨m, rfl⟩`. Use `⟨m 0 ⊗ₜ m 1, ?_⟩` and prove the remaining obligations.

Apply the tactic sequence `rw [hπt]; congr 1; ext i; fin_cases i <;> rfl`. Establish `hswap : ∀ x y : V, exteriorPower.ιMulti K 2 ![x, y] = -exteriorPower.ιMulti K 2 ![y, x]`. Introduce `x y`. Rewrite using `[← (exteriorPower.ιMulti K 2).map_swap ![y, x] (show (0 : Fin 2) ≠ 1 by decide)]`. Apply the tactic sequence `congr 1; ext i; fin_cases i <;> rfl`.

Establish `hdiag : ∀ x : V, exteriorPower.ιMulti K 2 ![x, x] = 0`. Introduce `x`. Conclude with `(exteriorPower.ιMulti K 2).map_eq_zero_of_eq ![x, x] (i := 0) (j := 1) rfl (by decide)`. Set `b` to `Module.finBasis K V`. Set `bt` to `b.tensorProduct b`.

Set `r : V ⊗[K] V →ₗ[K] ⋀[K]^2 V` to `bt.constr K (fun p => if p.1 < p.2 then exteriorPower.ιMulti K 2 ![b p.1, b p.2] else 0)`. Establish `hrb : ∀ i j, r (b i ⊗ₜ b j) = if i < j then exteriorPower.ιMulti K 2 ![b i, b j] else 0`. Introduce `i j`. Rewrite using `[← Module.Basis.tensorProduct_apply, Module.Basis.constr_basis]`. Establish `hr : r ∘ₗ (LinearMap.id - (TensorProduct.comm K V V).toLinearMap) = π`.

Apply `bt.ext` to reduce the goal to its premises. Introduce and unpack `⟨i, j⟩`. Simplify using `only [bt, Module.Basis.tensorProduct_apply, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, TensorProduct.comm_tmul, map_sub, hrb, hπt]`. Break down `lt_trichotomy i j with h | h | h` into its components or cases. Simplify using `[h, lt_asymm h]`.

Substitute `h` using the available equality. Simplify using `[hdiag]`. Simplify using `[h, lt_asymm h, hswap (b i) (b j)]`. Establish `hS : ∀ t, TensorProduct.comm K V V t = t → π t = 0`. Introduce `t ht`.

Rewrite using `[← hr, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, ht, sub_self, map_zero]`. Use `set L := TensorProduct.lift β with hLdef`. Establish `hle : LinearMap.ker L ≤ LinearMap.ker π` using `fun t ht => hS t (hrel t ht)`. Establish `hVV : Module.finrank K (V ⊗[K] V) = n * n` using `Module.finrank_tensorProduct`. Establish `hext : Module.finrank K (⋀[K]^2 V) = n.choose 2` using `by rw [exteriorPower.finrank_eq]`.

Establish `hπk` using `LinearMap.finrank_range_add_finrank_ker π`. Rewrite `hπk` using `[LinearMap.range_eq_top.mpr hπ, finrank_top, hext, hVV]`. Establish `hLk` using `LinearMap.finrank_range_add_finrank_ker L`. Rewrite `hLk` using `[hVV]`. Establish `hLr : Module.finrank K (LinearMap.range L) ≤ Module.finrank K W` using `Submodule.finrank_le _`.

Establish `hNeq : LinearMap.ker L = LinearMap.ker π` using `Submodule.eq_of_le_of_finrank_le hle (by`. Generalize the expression as in `n * n = m at hπk hLk`. Generalize the expression as in `n.choose 2 = k at hπk hW`. Use the proof step `omega)`. Establish `hL : Function.Surjective L`.

Rewrite using `[← LinearMap.range_eq_top]`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Rewrite `hLk` using `[hNeq]`. Generalize the expression as in `n * n = m at hπk hLk`. Generalize the expression as in `n.choose 2 = k at hπk hW`.

Use linear arithmetic over natural numbers and integers. Use `⟨?_, hL, fun t ht => ?_⟩` and prove the remaining obligations. Use `⟨(π.quotKerEquivOfSurjective hπ).symm.trans ((Submodule.quotEquivOfEq _ _ hNeq.symm).trans (L.quotKerEquivOfSurjective hL)), ?_⟩` and prove the remaining obligations. Introduce `a c`. Rewrite using `[← hπt, ← LinearMap.quotKerEquivOfSurjective_apply_mk π hπ, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk, hLdef, TensorProduct.lift.tmul]`.

Establish `: t ∈ LinearMap.ker L` using `hNeq ▸ hS t ht`. Conclude with `this`.
-/
theorem exteriorSq_of_symm_relations (K : Type) [Field K] (V W : Type) [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Module.Finite K V] [Module.Finite K W] (β : V →ₗ[K] V →ₗ[K] W)
    (hW : Module.finrank K W ≤ (Module.finrank K V).choose 2)
    (hrel : ∀ t : V ⊗[K] V, TensorProduct.lift β t = 0 → TensorProduct.comm K V V t = t) :
    (∃ e : ⋀[K]^2 V ≃ₗ[K] W, ∀ a b, e (exteriorPower.ιMulti K 2 ![a, b]) = β a b) ∧
      Function.Surjective (TensorProduct.lift β) ∧
      ∀ t : V ⊗[K] V, TensorProduct.comm K V V t = t → TensorProduct.lift β t = 0 := by
  classical
  set n := Module.finrank K V with hn
  have h0 : ∀ a b x : V, Function.update ![a, b] 0 x = ![x, b] := by
    intro a b x; ext i; fin_cases i <;> rfl
  have h1 : ∀ a b x : V, Function.update ![a, b] 1 x = ![a, x] := by
    intro a b x; ext i; fin_cases i <;> rfl
  let wb : V →ₗ[K] V →ₗ[K] ⋀[K]^2 V :=
    LinearMap.mk₂ K (fun a b => exteriorPower.ιMulti K 2 ![a, b])
      (by intro a₁ a₂ b
          rw [← h0 a₁ b (a₁ + a₂), AlternatingMap.map_update_add]; simp only [h0])
      (by intro c a b
          rw [← h0 a b (c • a), AlternatingMap.map_update_smul]; simp only [h0])
      (by intro a b₁ b₂
          rw [← h1 a b₁ (b₁ + b₂), AlternatingMap.map_update_add]; simp only [h1])
      (by intro c a b
          rw [← h1 a b (c • b), AlternatingMap.map_update_smul]; simp only [h1])
  let π : V ⊗[K] V →ₗ[K] ⋀[K]^2 V := TensorProduct.lift wb
  have hπt : ∀ a b, π (a ⊗ₜ b) = exteriorPower.ιMulti K 2 ![a, b] := by
    intro a b; simp [π, wb]
  have hπ : Function.Surjective π := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← exteriorPower.ιMulti_span K 2 V, Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    refine ⟨m 0 ⊗ₜ m 1, ?_⟩
    rw [hπt]; congr 1; ext i; fin_cases i <;> rfl
  have hswap : ∀ x y : V, exteriorPower.ιMulti K 2 ![x, y] = -exteriorPower.ιMulti K 2 ![y, x] := by
    intro x y
    rw [← (exteriorPower.ιMulti K 2).map_swap ![y, x] (show (0 : Fin 2) ≠ 1 by decide)]
    congr 1; ext i; fin_cases i <;> rfl
  have hdiag : ∀ x : V, exteriorPower.ιMulti K 2 ![x, x] = 0 := by
    intro x
    exact (exteriorPower.ιMulti K 2).map_eq_zero_of_eq ![x, x] (i := 0) (j := 1) rfl (by decide)
  let b := Module.finBasis K V
  let bt := b.tensorProduct b
  let r : V ⊗[K] V →ₗ[K] ⋀[K]^2 V :=
    bt.constr K (fun p => if p.1 < p.2 then exteriorPower.ιMulti K 2 ![b p.1, b p.2] else 0)
  have hrb : ∀ i j, r (b i ⊗ₜ b j) = if i < j then exteriorPower.ιMulti K 2 ![b i, b j] else 0 := by
    intro i j
    rw [← Module.Basis.tensorProduct_apply, Module.Basis.constr_basis]
  have hr : r ∘ₗ (LinearMap.id - (TensorProduct.comm K V V).toLinearMap) = π := by
    apply bt.ext; rintro ⟨i, j⟩
    simp only [bt, Module.Basis.tensorProduct_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply, LinearEquiv.coe_coe, TensorProduct.comm_tmul, map_sub, hrb, hπt]
    rcases lt_trichotomy i j with h | h | h
    · simp [h, lt_asymm h]
    · subst h; simp [hdiag]
    · simp [h, lt_asymm h, hswap (b i) (b j)]
  have hS : ∀ t, TensorProduct.comm K V V t = t → π t = 0 := by
    intro t ht
    rw [← hr, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, ht,
      sub_self, map_zero]
  set L := TensorProduct.lift β with hLdef
  have hle : LinearMap.ker L ≤ LinearMap.ker π := fun t ht => hS t (hrel t ht)
  have hVV : Module.finrank K (V ⊗[K] V) = n * n := Module.finrank_tensorProduct
  have hext : Module.finrank K (⋀[K]^2 V) = n.choose 2 := by rw [exteriorPower.finrank_eq]
  have hπk := LinearMap.finrank_range_add_finrank_ker π
  rw [LinearMap.range_eq_top.mpr hπ, finrank_top, hext, hVV] at hπk
  have hLk := LinearMap.finrank_range_add_finrank_ker L
  rw [hVV] at hLk
  have hLr : Module.finrank K (LinearMap.range L) ≤ Module.finrank K W := Submodule.finrank_le _
  have hNeq : LinearMap.ker L = LinearMap.ker π :=
    Submodule.eq_of_le_of_finrank_le hle (by
      generalize n * n = m at hπk hLk
      generalize n.choose 2 = k at hπk hW
      omega)
  have hL : Function.Surjective L := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    rw [hNeq] at hLk
    generalize n * n = m at hπk hLk
    generalize n.choose 2 = k at hπk hW
    omega
  refine ⟨?_, hL, fun t ht => ?_⟩
  · refine ⟨(π.quotKerEquivOfSurjective hπ).symm.trans
      ((Submodule.quotEquivOfEq _ _ hNeq.symm).trans (L.quotKerEquivOfSurjective hL)), ?_⟩
    intro a c
    rw [← hπt, ← LinearMap.quotKerEquivOfSurjective_apply_mk π hπ, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
      LinearMap.quotKerEquivOfSurjective_apply_mk, hLdef, TensorProduct.lift.tmul]
  · have : t ∈ LinearMap.ker L := hNeq ▸ hS t ht
    exact this

end GlobalTheory
