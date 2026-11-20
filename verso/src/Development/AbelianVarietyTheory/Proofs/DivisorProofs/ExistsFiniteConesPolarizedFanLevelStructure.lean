import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteConesSiegelLevelStructure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsPosCombinationDefiniteSumStatement

open GlobalTheory.PolFan GlobalTheory.LocM

noncomputable section

namespace GlobalTheory.UPoinc.CellCones

/- English proof (translation)
Use `GlobalTheory.Poinc.Cells.cong_map (eb.toLinearMap ∘ₗ g.toIntLinearMap ∘ₗ eb.symm.toLinearMap) h i` as an intermediate fact. Simplify using `using this`.
-/
theorem cong_addHom {Y : Type} [AddCommGroup Y] {n N : ℕ} (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (g : Y →+ Y) {x y : Y}
    (h : ∀ i, ((eb x i : ℤ) : ZMod N) = (eb y i : ZMod N)) (i : Fin n) :
    ((eb (g x) i : ℤ) : ZMod N) = (eb (g y) i : ZMod N) := by
  have := GlobalTheory.Poinc.Cells.cong_map (eb.toLinearMap ∘ₗ g.toIntLinearMap ∘ₗ eb.symm.toLinearMap) h i
  simpa using this

/- English proof (translation)
Set `lift : (Fin n → ZMod N) → Y` to `fun cl => eb.symm fun i => ((cl i).val : ℤ)`. Establish `hlift : ∀ cl i, ((eb (lift cl) i : ℤ) : ZMod N) = cl i` using `fun cl i => by simp [lift]`. Set `d : (Fin n → ZMod N) → (Fin n → ZMod N)` to `fun cl i => ((eb (e (lift cl)) i : ℤ) : ZMod N)`. Use `⟨fun cl => e.symm (μ (d cl)), fun cl i => ?_, fun cl α hα => ?_, fun cl => ⟨d cl, by simp⟩⟩` and prove the remaining obligations. Establish `h1 : ∀ i, ((eb (μ (d cl)) i : ℤ) : ZMod N) = ((eb (e (lift cl)) i : ℤ) : ZMod N)` using `fun i => hμ _ _`.

Establish `h2` using `cong_addHom eb e.symm.toLinearMap.toAddMonoidHom h1 i`. Simplify using `only [LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h2`. Rewrite using `[h2, hlift]`. Simplify using `only [pull_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]`. Conclude with `hb _ _ fun i => cong_addHom eb e.toLinearMap.toAddMonoidHom (fun i => by rw [hα, hlift]) i`.
-/
theorem exists_transport {O : Type} [CommRing O] {Y : Type} [AddCommGroup Y] [Module O Y] {n N : ℕ} [NeZero N]
    (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (μ : (Fin n → ZMod N) → Y) (hμ : ∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i)
    (b : LinearMap.BilinForm ℤ Y) (e : Y ≃ₗ[O] Y)
    (hb : ∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α) :
    ∃ μ' : (Fin n → ZMod N) → Y, (∀ cl i, ((eb (μ' cl) i : ℤ) : ZMod N) = cl i) ∧
      (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) →
        pull e.toLinearMap b (μ' cl) (μ' cl) ≤ pull e.toLinearMap b α α) ∧
      ∀ cl, ∃ d, e (μ' cl) = μ d := by
  let lift : (Fin n → ZMod N) → Y := fun cl => eb.symm fun i => ((cl i).val : ℤ)
  have hlift : ∀ cl i, ((eb (lift cl) i : ℤ) : ZMod N) = cl i := fun cl i => by simp [lift]
  let d : (Fin n → ZMod N) → (Fin n → ZMod N) := fun cl i => ((eb (e (lift cl)) i : ℤ) : ZMod N)
  refine ⟨fun cl => e.symm (μ (d cl)), fun cl i => ?_, fun cl α hα => ?_, fun cl => ⟨d cl, by simp⟩⟩
  · have h1 : ∀ i, ((eb (μ (d cl)) i : ℤ) : ZMod N) = ((eb (e (lift cl)) i : ℤ) : ZMod N) := fun i => hμ _ _
    have h2 := cong_addHom eb e.symm.toLinearMap.toAddMonoidHom h1 i
    simp only [LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h2
    rw [h2, hlift]
  · simp only [pull_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    exact hb _ _ fun i => cong_addHom eb e.toLinearMap.toAddMonoidHom (fun i => by rw [hα, hlift]) i

/- English proof (translation)
Take `⟨t, bb, hbb⟩` from `hγ.basis`. Set `B' : balForms bar X` to `⟨b', hb'⟩`. Set `B₀ : balForms bar X` to `⟨b₀, hb₀⟩`. Establish `hc : ∀ n ∈ s, ∀ o, (∀ j, o ≠ Sum.inl j) → (n : ℤ) * bb.repr B' o + bb.repr B₀ o = 0`. Introduce `n hn o ho`.

Take `⟨k, cf, hk0, he⟩` from `hk n hn`. Establish `hE : k • (n • B' + B₀) = ∑ j, cf j • bb (Sum.inl j)` using `Subtype.ext (by simpa [hbb, B', B₀] using he)`. Use `congrArg (fun x => bb.repr x o) hE` as an intermediate fact. Simplify using `only [map_nsmul, map_add, map_sum, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.add_apply, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply, nsmul_eq_mul] at this`. Rewrite `this` using `[Finset.sum_eq_zero fun j _ => by rw [if_neg (ho j).symm]; simp]`.

Establish `hk' : (k : ℤ) ≠ 0` using `by exact_mod_cast hk0.ne'`. Move the coercions through the operations in `at this`. Conclude with `(mul_eq_zero.1 this).resolve_left hk'`. Establish `hp : ∀ n ∈ s, ∀ j, 0 ≤ (n : ℤ) * bb.repr B' (Sum.inl j) + bb.repr B₀ (Sum.inl j)`. Introduce `n hn j`.

Take `⟨k, cf, hk0, he⟩` from `hk n hn`. Establish `hE : k • (n • B' + B₀) = ∑ j, cf j • bb (Sum.inl j)` using `Subtype.ext (by simpa [hbb, B', B₀] using he)`. Use `congrArg (fun x => bb.repr x (Sum.inl j)) hE` as an intermediate fact. Simplify using `only [map_nsmul, map_add, map_sum, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.add_apply, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply, nsmul_eq_mul, Sum.inl.injEq] at this`. Simplify using `only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this`.

Establish `hk' : (0 : ℤ) < k` using `by exact_mod_cast hk0`. Establish `h2 : (0 : ℤ) ≤ k * ((n : ℤ) * bb.repr B' (Sum.inl j) + bb.repr B₀ (Sum.inl j))`. Move the coercions through the operations in `at this ⊢`. Rewrite using `[this]`. Check the signs of the components of the expression.

Conclude with `nonneg_of_mul_nonneg_right (by linarith) hk'`. Set `M : ℕ` to `∑ o, (bb.repr B₀ o).natAbs`. Take `⟨n₁, hn₁, h₁⟩` from `hs.exists_gt M`. Take `⟨n₂, hn₂, h₂⟩` from `hs.exists_gt n₁`. Establish `hM : ∀ o, (bb.repr B₀ o).natAbs ≤ M` using `fun o => Finset.single_le_sum (f := fun o => (bb.repr B₀ o).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ o)`.

Establish `hR : ∀ o, (∀ j, o ≠ Sum.inl j) → bb.repr B' o = 0` using `fun o ho => by`. Establish `e1` using `hc n₁ hn₁ o ho`. Establish `e2` using `hc n₂ hn₂ o ho`. Establish `: ((n₂ : ℤ) - n₁) * bb.repr B' o = 0` using `by linarith`. Conclude with `(mul_eq_zero.1 this).resolve_left (by omega)`.

Establish `hL : ∀ j, 0 ≤ bb.repr B' (Sum.inl j)` using `fun j => by`. Establish `e1` using `hp n₁ hn₁ j`. Establish `e2` using `hM (Sum.inl j)`. Assume the negation of the conclusion as `hneg`. Use `push_neg at hneg`.

Establish `: (bb.repr B₀ (Sum.inl j)) ≤ M` using `by omega`. Establish `: (n₁ : ℤ) * bb.repr B' (Sum.inl j) ≤ - n₁` using `by nlinarith`. Use linear arithmetic over natural numbers and integers. Use `⟨fun j => (bb.repr B' (Sum.inl j)).toNat, ?_⟩` and prove the remaining obligations. Establish `hsum` using `bb.sum_repr B'`.

Establish `h0 : ∑ a₂ : Fin t, bb.repr B' (Sum.inr a₂) • bb (Sum.inr a₂) = 0` using `Finset.sum_eq_zero fun o _ => by rw [hR (Sum.inr o) fun j => Sum.inr_ne_inl, zero_smul]`. Rewrite `hsum` using `[Fintype.sum_sum_type, h0, add_zero]`. Use `congrArg Subtype.val hsum` as an intermediate fact. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, hbb] at this`. Rewrite using `[show b' = (B' : LinearMap.BilinForm ℤ X) from rfl, ← this]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← natCast_zsmul, Int.toNat_of_nonneg (hL j)]`.
-/
theorem exists_nat_comb_of_infinite {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X]
    [Module O X] [Module.Finite O X] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : IsCone bar φ γ)
    {b' b₀ : LinearMap.BilinForm ℤ X} (hb' : b' ∈ balForms bar X) (hb₀ : b₀ ∈ balForms bar X)
    {s : Set ℕ} (hs : s.Infinite)
    (hk : ∀ n ∈ s, ∃ (k : ℕ) (cf : Fin m → ℕ), 0 < k ∧ k • (n • b' + b₀) = ∑ j, cf j • γ j) :
    ∃ cf : Fin m → ℕ, b' = ∑ j, cf j • γ j := by
  classical
  obtain ⟨t, bb, hbb⟩ := hγ.basis
  let B' : balForms bar X := ⟨b', hb'⟩
  let B₀ : balForms bar X := ⟨b₀, hb₀⟩
  have hc : ∀ n ∈ s, ∀ o, (∀ j, o ≠ Sum.inl j) → (n : ℤ) * bb.repr B' o + bb.repr B₀ o = 0 := by
    intro n hn o ho
    obtain ⟨k, cf, hk0, he⟩ := hk n hn
    have hE : k • (n • B' + B₀) = ∑ j, cf j • bb (Sum.inl j) := Subtype.ext (by simpa [hbb, B', B₀] using he)
    have := congrArg (fun x => bb.repr x o) hE
    simp only [map_nsmul, map_add, map_sum, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.add_apply,
      Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply, nsmul_eq_mul] at this
    rw [Finset.sum_eq_zero fun j _ => by rw [if_neg (ho j).symm]; simp] at this
    have hk' : (k : ℤ) ≠ 0 := by exact_mod_cast hk0.ne'
    push_cast at this
    exact (mul_eq_zero.1 this).resolve_left hk'
  have hp : ∀ n ∈ s, ∀ j, 0 ≤ (n : ℤ) * bb.repr B' (Sum.inl j) + bb.repr B₀ (Sum.inl j) := by
    intro n hn j
    obtain ⟨k, cf, hk0, he⟩ := hk n hn
    have hE : k • (n • B' + B₀) = ∑ j, cf j • bb (Sum.inl j) := Subtype.ext (by simpa [hbb, B', B₀] using he)
    have := congrArg (fun x => bb.repr x (Sum.inl j)) hE
    simp only [map_nsmul, map_add, map_sum, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.add_apply,
      Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply, nsmul_eq_mul, Sum.inl.injEq] at this
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    have hk' : (0 : ℤ) < k := by exact_mod_cast hk0
    have h2 : (0 : ℤ) ≤ k * ((n : ℤ) * bb.repr B' (Sum.inl j) + bb.repr B₀ (Sum.inl j)) := by
      push_cast at this ⊢; rw [this]; positivity
    exact nonneg_of_mul_nonneg_right (by linarith) hk'
  let M : ℕ := ∑ o, (bb.repr B₀ o).natAbs
  obtain ⟨n₁, hn₁, h₁⟩ := hs.exists_gt M
  obtain ⟨n₂, hn₂, h₂⟩ := hs.exists_gt n₁
  have hM : ∀ o, (bb.repr B₀ o).natAbs ≤ M := fun o =>
    Finset.single_le_sum (f := fun o => (bb.repr B₀ o).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ o)
  have hR : ∀ o, (∀ j, o ≠ Sum.inl j) → bb.repr B' o = 0 := fun o ho => by
    have e1 := hc n₁ hn₁ o ho
    have e2 := hc n₂ hn₂ o ho
    have : ((n₂ : ℤ) - n₁) * bb.repr B' o = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left (by omega)
  have hL : ∀ j, 0 ≤ bb.repr B' (Sum.inl j) := fun j => by
    have e1 := hp n₁ hn₁ j
    have e2 := hM (Sum.inl j)
    by_contra hneg
    push_neg at hneg
    have : (bb.repr B₀ (Sum.inl j)) ≤ M := by omega
    have : (n₁ : ℤ) * bb.repr B' (Sum.inl j) ≤ - n₁ := by nlinarith
    omega
  refine ⟨fun j => (bb.repr B' (Sum.inl j)).toNat, ?_⟩
  have hsum := bb.sum_repr B'
  have h0 : ∑ a₂ : Fin t, bb.repr B' (Sum.inr a₂) • bb (Sum.inr a₂) = 0 :=
    Finset.sum_eq_zero fun o _ => by rw [hR (Sum.inr o) fun j => Sum.inr_ne_inl, zero_smul]
  rw [Fintype.sum_sum_type, h0, add_zero] at hsum
  have := congrArg Subtype.val hsum
  simp only [Submodule.coe_sum, Submodule.coe_smul, hbb] at this
  rw [show b' = (B' : LinearMap.BilinForm ℤ X) from rfl, ← this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← natCast_zsmul, Int.toNat_of_nonneg (hL j)]

/- English proof (translation)
Introduce `O _ bar φ Y _ _ _ _ hF n N _ hN eb μ hμ b₀ hb₀ hb₀p hb₀m`. Use `haveI : Module.Free ℤ Y := Module.Free.of_equiv eb.symm`. Use `haveI : Module.Finite ℤ Y := Module.Finite.equiv eb.symm`. Set `Mn : ((Fin n → ZMod N) → Y) → LinearMap.BilinForm ℤ Y → Prop` to `fun μ b => ∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α`. Set `T : Set (Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ Y)` to `{x | IsCone bar φ x.2 ∧ (∀ y, y ≠ 0 → 0 < ∑ j, x.2 j y y) ∧ ∃ (b : LinearMap.BilinForm ℤ Y) (k : ℕ) (cf : Fin x.1 → ℕ), 0 < k ∧ (∀ j, 0 < cf j) ∧ k • b = ∑ j, cf j • x.2 j ∧ Mn μ b}`.

Establish `hT : T.Finite`. Take `⟨S, hS, hSe⟩` from `hF.finite`. Set `TS : Set (Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ Y)` to `{x | (∀ j, x.2 j ∈ S) ∧ Function.Injective x.2 ∧ IsCone bar φ x.2 ∧ (∀ y, y ≠ 0 → 0 < ∑ j, x.2 j y y)}`. Establish `hTS : TS.Finite` using `(GlobalTheory.Poinc.Cells.finite_families _ S hS).subset fun x hx => ⟨hx.1, hx.2.1⟩`. Establish `hfin` using `fun (x : Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ Y) (h : IsCone bar φ x.2 ∧ (∀ y, y ≠ 0 → 0 < ∑ j, x.2 j y y)) => GlobalTheory.T.finite_minimiserSystems_posCombination_definiteSum Y n N eb x.1 x.2 (fun j => (h.1.mem j).1) h.1.nonneg h.2`.

Set `Fμ : (Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ Y) → Set ((Fin n → ZMod N) → Y)` to `fun x => if h : IsCone bar φ x.2 ∧ (∀ y, y ≠ 0 → 0 < ∑ j, x.2 j y y) then ((hfin x h).choose : Set _) else ∅`. Set `M` to `(⋃ x ∈ TS, Fμ x) ∩ {μ' | ∀ cl i, ((eb (μ' cl) i : ℤ) : ZMod N) = cl i}`. Establish `hM : M.Finite` using `(hTS.biUnion fun x _ => by`. Simplify using `only [Fμ]`. Use `split_ifs`.

Conclude with `Finset.finite_toSet _`. Conclude with `Set.finite_empty).inter_of_left _`. Set `V : Set Y` to `Set.range μ`. Set `E` to `⋃ μ' ∈ M, {e : Y ≃ₗ[O] Y | ∀ cl, e (μ' cl) ∈ V}`. Establish `hl : ∀ (e : Y ≃ₗ[O] Y) x, (eb.toLinearMap ∘ₗ e.toLinearMap.toAddMonoidHom.toIntLinearMap ∘ₗ eb.symm.toLinearMap) x = eb (e (eb.symm x))` using `fun e x => rfl`.

Establish `hE : E.Finite` using `hM.biUnion fun μ' hμ' => by`. Set `Φ : (Y ≃ₗ[O] Y) → (Fin n → ZMod N) → Y` to `fun e cl => e (μ' cl)`. Use `Set.Finite.of_finite_image (f := Φ) ((Set.Finite.pi (t := fun _ => V) fun _ => Set.finite_range _).subset ?_) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨e, he, rfl⟩ cl -`. Conclude with `he cl`.

Introduce `e₁ _ e₂ _ h`. Establish `key` using `GlobalTheory.Poinc.Cells.linearMap_eq_of_eq_on_residues N (by omega) n (eb.toLinearMap ∘ₗ e₁.toLinearMap.toAddMonoidHom.toIntLinearMap ∘ₗ eb.symm.toLinearMap) (eb.toLinearMap ∘ₗ e₂.toLinearMap.toAddMonoidHom.toIntLinearMap ∘ₗ eb.symm.toLinearMap) (Set.range fun cl => eb (μ' cl)) …`. Introduce and unpack `_ ⟨cl, rfl⟩`. Rewrite using `[hl, hl]`. Simplify using `only [LinearEquiv.symm_apply_apply]`.

Conclude with `congrArg eb (congrFun h cl))`. Use `LinearEquiv.ext fun y => eb.injective ?_` and prove the remaining obligations. Use `LinearMap.congr_fun key (eb y)` as an intermediate fact. Rewrite `this` using `[hl, hl]`. Simplify using `using this`.

Use `((hTS.prod hE).image fun q => (⟨q.1.1, fun j => pull q.2.symm.toLinearMap (q.1.2 j)⟩ : Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ Y)).subset ?_` and prove the remaining obligations. Introduce and unpack `⟨m, γ⟩ ⟨hγ, hγd, b, k, cf, hk, hcf, hkb, hbm⟩`. Take `⟨e, he⟩` from `hSe m γ hγ`. Take `⟨μ', hμ'1, hμ'2, hμ'3⟩` from `exists_transport eb μ hμ b e hbm`. Establish `hc'` using `hγ.pull_equiv e`.

Establish `hd' : ∀ y, y ≠ 0 → 0 < ∑ j, pull e.toLinearMap (γ j) y y` using `fun y hy => by`. Simplify `hy)` using `using hγd (e y) (by simpa`. Establish `hkb' : k • pull e.toLinearMap b = ∑ j, cf j • pull e.toLinearMap (γ j)` using `LinearMap.ext₂ fun x y => by`. Simplify `LinearMap.congr_fun₂ hkb (e x) (e y)` using `[LinearMap.sum_apply]`. Establish `hx' : (⟨m, fun j => pull e.toLinearMap (γ j)⟩ : Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ Y) ∈ TS` using `⟨he, hc'.injective, hc', hd'⟩`.

Use `⟨⟨⟨m, fun j => pull e.toLinearMap (γ j)⟩, e⟩, ⟨hx', ?_⟩, ?_⟩` and prove the remaining obligations. Use `Set.mem_biUnion (x := μ') ⟨Set.mem_biUnion hx' ?_, hμ'1⟩ fun cl => ?_` and prove the remaining obligations. Use `show μ' ∈ Fμ ⟨m, fun j => pull e.toLinearMap (γ j)⟩`. Simplify using `only [Fμ]`. Rewrite using `[dif_pos (show IsCone bar φ (fun j => pull e.toLinearMap (γ j)) ∧ _ from ⟨hc', hd'⟩)]`.

Conclude with `(hfin ⟨m, fun j => pull e.toLinearMap (γ j)⟩ ⟨hc', hd'⟩).choose_spec (pull e.toLinearMap b) k cf hk hcf hkb' μ' hμ'1 hμ'2`. Take `⟨d, hd⟩` from `hμ'3 cl`. Conclude with `⟨d, hd.symm⟩`. Simplify using the standard rewrite rules. Take `⟨L, hL⟩ : ∃ L : List (Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ Y), ∀ x, x ∈ L ↔ x ∈ T` from `⟨hT.toFinset.toList, fun x => by simp⟩`.

Use `⟨L.length, fun i => (L.get i).1, fun i => (L.get i).2, fun i => ((hL _).1 (List.get_mem L i)).1, ?_⟩` and prove the remaining obligations. Introduce `b' hb' hb'p hb'm`. Establish `key : ∀ n' : ℕ, ∃ i : Fin L.length, ∃ (k : ℕ) (cf : Fin (L.get i).1 → ℕ), 0 < k ∧ k • (n' • b' + b₀) = ∑ j, cf j • (L.get i).2 j`. Introduce `n'`. Establish `hβs : n' • b' + b₀ ∈ balForms bar Y` using `add_mem (nsmul_mem hb' _) hb₀`.

Establish `hβp : ∀ x, x ≠ 0 → 0 < (n' • b' + b₀) x x` using `fun x hx => by`. Establish `h1` using `hb'p x`. Establish `h2` using `hb₀p x hx`. Simplify using `only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]`. Check the signs of the components of the expression.

Establish `hβm : Mn μ (n' • b' + b₀)` using `fun cl α hα => by`. Establish `h1` using `hb'm cl α hα`. Establish `h2` using `hb₀m cl α hα`. Establish `h3 : (n' : ℤ) * b' (μ cl) (μ cl) ≤ n' * b' α α` using `mul_le_mul_of_nonneg_left h1 (by positivity)`. Simplify using `only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]`.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨m, γ, k, cf, hγ, hk, hcf, hkβ⟩` from `GlobalTheory.Poinc.Cover.exists_cone O bar φ Y hF _ hβs hβp`. Establish `hγd : ∀ y, y ≠ 0 → 0 < ∑ j, γ j y y` using `fun y hy => by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Establish `h0 : ∀ j, γ j y y = 0` using `fun j => le_antisymm ((Finset.single_le_sum (fun j _ => hγ.nonneg j y) (Finset.mem_univ j)).trans hcon) (hγ.nonneg j y)`. Establish `h1` using `LinearMap.congr_fun₂ hkβ y y`. Establish `h2` using `hβp y hy`. Simplify using `only [LinearMap.smul_apply, LinearMap.sum_apply, h0, smul_zero, Finset.sum_const_zero, nsmul_eq_mul] at h1`. Establish `: (k : ℤ) * (n' • b' + b₀) y y > 0` using `mul_pos (by exact_mod_cast hk) h2`.

Simplify using `only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul] at this h1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hmem : (⟨m, γ⟩ : Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ Y) ∈ T` using `⟨hγ, hγd, _, k, cf, hk, hcf, hkβ, hβm⟩`. Take `⟨i, hi⟩` from `List.mem_iff_get.1 ((hL _).2 hmem)`. Use `⟨i, ?_⟩` and prove the remaining obligations.

Rewrite using `[hi]`. Conclude with `⟨k, cf, hk, hkβ⟩`. Use `choose f hf using key`. Take `⟨i, hi⟩` from `Finite.exists_infinite_fiber f`. Take `⟨cf, hcf⟩` from `exists_nat_comb_of_infinite ((hL _).1 (List.get_mem L i)).1 hb' hb₀ (s := f ⁻¹' {i}) (Set.infinite_coe_iff.1 hi) fun n' hn' => by`.

Use `hf n'` as an intermediate fact. Rewrite `this` using `[show f n' = i from hn']`. Conclude with `this`. Conclude with `⟨i, 1, cf, one_pos, by rw [one_smul]; exact hcf⟩`.
-/
theorem exists_finite_cones : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], IsPolFanOn bar φ Y → ∀ (n N : ℕ) [NeZero N], 3 ≤ N → ∀ (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (μ : (Fin n → ZMod N) → Y), (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) → ∀ b₀ ∈ balForms bar Y, (∀ x, x ≠ 0 → 0 < b₀ x x) → (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b₀ (μ cl) (μ cl) ≤ b₀ α α) → ∃ (p : ℕ) (m : Fin p → ℕ) (γ : ∀ i, Fin (m i) → LinearMap.BilinForm ℤ Y), (∀ i, IsCone bar φ (γ i)) ∧ ∀ b' ∈ balForms bar Y, (∀ x, 0 ≤ b' x x) → (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b' (μ cl) (μ cl) ≤ b' α α) → ∃ (i : Fin p) (k : ℕ) (cf : Fin (m i) → ℕ), 0 < k ∧ k • b' = ∑ j, cf j • γ i j := by
  intro O _ bar φ Y _ _ _ _ hF n N _ hN eb μ hμ b₀ hb₀ hb₀p hb₀m
  classical
  haveI : Module.Free ℤ Y := Module.Free.of_equiv eb.symm
  haveI : Module.Finite ℤ Y := Module.Finite.equiv eb.symm
  let Mn : ((Fin n → ZMod N) → Y) → LinearMap.BilinForm ℤ Y → Prop :=
    fun μ b => ∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α
  let T : Set (Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ Y) := {x | IsCone bar φ x.2 ∧
    (∀ y, y ≠ 0 → 0 < ∑ j, x.2 j y y) ∧ ∃ (b : LinearMap.BilinForm ℤ Y) (k : ℕ) (cf : Fin x.1 → ℕ),
      0 < k ∧ (∀ j, 0 < cf j) ∧ k • b = ∑ j, cf j • x.2 j ∧ Mn μ b}
  have hT : T.Finite := by
    obtain ⟨S, hS, hSe⟩ := hF.finite
    let TS : Set (Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ Y) := {x | (∀ j, x.2 j ∈ S) ∧
      Function.Injective x.2 ∧ IsCone bar φ x.2 ∧ (∀ y, y ≠ 0 → 0 < ∑ j, x.2 j y y)}
    have hTS : TS.Finite := (GlobalTheory.Poinc.Cells.finite_families _ S hS).subset fun x hx => ⟨hx.1, hx.2.1⟩
    have hfin := fun (x : Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ Y)
      (h : IsCone bar φ x.2 ∧ (∀ y, y ≠ 0 → 0 < ∑ j, x.2 j y y)) =>
        GlobalTheory.T.finite_minimiserSystems_posCombination_definiteSum Y n N eb x.1 x.2 (fun j => (h.1.mem j).1) h.1.nonneg h.2
    let Fμ : (Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ Y) → Set ((Fin n → ZMod N) → Y) := fun x =>
      if h : IsCone bar φ x.2 ∧ (∀ y, y ≠ 0 → 0 < ∑ j, x.2 j y y) then ((hfin x h).choose : Set _) else ∅
    let M := (⋃ x ∈ TS, Fμ x) ∩ {μ' | ∀ cl i, ((eb (μ' cl) i : ℤ) : ZMod N) = cl i}
    have hM : M.Finite := (hTS.biUnion fun x _ => by
      simp only [Fμ]; split_ifs
      · exact Finset.finite_toSet _
      · exact Set.finite_empty).inter_of_left _
    let V : Set Y := Set.range μ
    let E := ⋃ μ' ∈ M, {e : Y ≃ₗ[O] Y | ∀ cl, e (μ' cl) ∈ V}
    have hl : ∀ (e : Y ≃ₗ[O] Y) x,
        (eb.toLinearMap ∘ₗ e.toLinearMap.toAddMonoidHom.toIntLinearMap ∘ₗ eb.symm.toLinearMap) x = eb (e (eb.symm x)) :=
      fun e x => rfl
    have hE : E.Finite := hM.biUnion fun μ' hμ' => by
      let Φ : (Y ≃ₗ[O] Y) → (Fin n → ZMod N) → Y := fun e cl => e (μ' cl)
      refine Set.Finite.of_finite_image (f := Φ)
        ((Set.Finite.pi (t := fun _ => V) fun _ => Set.finite_range _).subset ?_) ?_
      · rintro _ ⟨e, he, rfl⟩ cl -
        exact he cl
      · intro e₁ _ e₂ _ h
        have key := GlobalTheory.Poinc.Cells.linearMap_eq_of_eq_on_residues N (by omega) n
          (eb.toLinearMap ∘ₗ e₁.toLinearMap.toAddMonoidHom.toIntLinearMap ∘ₗ eb.symm.toLinearMap)
          (eb.toLinearMap ∘ₗ e₂.toLinearMap.toAddMonoidHom.toIntLinearMap ∘ₗ eb.symm.toLinearMap)
          (Set.range fun cl => eb (μ' cl))
          (fun x => ⟨eb (μ' fun i => (x i : ZMod N)), ⟨_, rfl⟩, fun i => hμ'.2 _ _⟩) (by
            rintro _ ⟨cl, rfl⟩
            rw [hl, hl]
            simp only [LinearEquiv.symm_apply_apply]
            exact congrArg eb (congrFun h cl))
        refine LinearEquiv.ext fun y => eb.injective ?_
        have := LinearMap.congr_fun key (eb y)
        rw [hl, hl] at this
        simpa using this
    refine ((hTS.prod hE).image fun q => (⟨q.1.1, fun j => pull q.2.symm.toLinearMap (q.1.2 j)⟩ :
      Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ Y)).subset ?_
    rintro ⟨m, γ⟩ ⟨hγ, hγd, b, k, cf, hk, hcf, hkb, hbm⟩
    obtain ⟨e, he⟩ := hSe m γ hγ
    obtain ⟨μ', hμ'1, hμ'2, hμ'3⟩ := exists_transport eb μ hμ b e hbm
    have hc' := hγ.pull_equiv e
    have hd' : ∀ y, y ≠ 0 → 0 < ∑ j, pull e.toLinearMap (γ j) y y := fun y hy => by
      simpa using hγd (e y) (by simpa using hy)
    have hkb' : k • pull e.toLinearMap b = ∑ j, cf j • pull e.toLinearMap (γ j) := LinearMap.ext₂ fun x y => by
      simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ hkb (e x) (e y)
    have hx' : (⟨m, fun j => pull e.toLinearMap (γ j)⟩ : Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ Y) ∈ TS :=
      ⟨he, hc'.injective, hc', hd'⟩
    refine ⟨⟨⟨m, fun j => pull e.toLinearMap (γ j)⟩, e⟩, ⟨hx', ?_⟩, ?_⟩
    · refine Set.mem_biUnion (x := μ') ⟨Set.mem_biUnion hx' ?_, hμ'1⟩ fun cl => ?_
      · show μ' ∈ Fμ ⟨m, fun j => pull e.toLinearMap (γ j)⟩
        simp only [Fμ]
        rw [dif_pos (show IsCone bar φ (fun j => pull e.toLinearMap (γ j)) ∧ _ from ⟨hc', hd'⟩)]
        exact (hfin ⟨m, fun j => pull e.toLinearMap (γ j)⟩ ⟨hc', hd'⟩).choose_spec (pull e.toLinearMap b) k cf hk hcf
          hkb' μ' hμ'1 hμ'2
      · obtain ⟨d, hd⟩ := hμ'3 cl
        exact ⟨d, hd.symm⟩
    · simp
  obtain ⟨L, hL⟩ : ∃ L : List (Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ Y), ∀ x, x ∈ L ↔ x ∈ T :=
    ⟨hT.toFinset.toList, fun x => by simp⟩
  refine ⟨L.length, fun i => (L.get i).1, fun i => (L.get i).2, fun i => ((hL _).1 (List.get_mem L i)).1, ?_⟩
  intro b' hb' hb'p hb'm
  have key : ∀ n' : ℕ, ∃ i : Fin L.length, ∃ (k : ℕ) (cf : Fin (L.get i).1 → ℕ), 0 < k ∧
      k • (n' • b' + b₀) = ∑ j, cf j • (L.get i).2 j := by
    intro n'
    have hβs : n' • b' + b₀ ∈ balForms bar Y := add_mem (nsmul_mem hb' _) hb₀
    have hβp : ∀ x, x ≠ 0 → 0 < (n' • b' + b₀) x x := fun x hx => by
      have h1 := hb'p x
      have h2 := hb₀p x hx
      simp only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
      positivity
    have hβm : Mn μ (n' • b' + b₀) := fun cl α hα => by
      have h1 := hb'm cl α hα
      have h2 := hb₀m cl α hα
      have h3 : (n' : ℤ) * b' (μ cl) (μ cl) ≤ n' * b' α α := mul_le_mul_of_nonneg_left h1 (by positivity)
      simp only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
      linarith
    obtain ⟨m, γ, k, cf, hγ, hk, hcf, hkβ⟩ := GlobalTheory.Poinc.Cover.exists_cone O bar φ Y hF _ hβs hβp
    have hγd : ∀ y, y ≠ 0 → 0 < ∑ j, γ j y y := fun y hy => by
      by_contra hcon
      push_neg at hcon
      have h0 : ∀ j, γ j y y = 0 := fun j => le_antisymm ((Finset.single_le_sum (fun j _ => hγ.nonneg j y)
        (Finset.mem_univ j)).trans hcon) (hγ.nonneg j y)
      have h1 := LinearMap.congr_fun₂ hkβ y y
      have h2 := hβp y hy
      simp only [LinearMap.smul_apply, LinearMap.sum_apply, h0, smul_zero, Finset.sum_const_zero, nsmul_eq_mul] at h1
      have : (k : ℤ) * (n' • b' + b₀) y y > 0 := mul_pos (by exact_mod_cast hk) h2
      simp only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul] at this h1
      linarith
    have hmem : (⟨m, γ⟩ : Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ Y) ∈ T :=
      ⟨hγ, hγd, _, k, cf, hk, hcf, hkβ, hβm⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.1 ((hL _).2 hmem)
    refine ⟨i, ?_⟩
    rw [hi]
    exact ⟨k, cf, hk, hkβ⟩
  choose f hf using key
  obtain ⟨i, hi⟩ := Finite.exists_infinite_fiber f
  obtain ⟨cf, hcf⟩ := exists_nat_comb_of_infinite ((hL _).1 (List.get_mem L i)).1 hb' hb₀ (s := f ⁻¹' {i})
    (Set.infinite_coe_iff.1 hi) fun n' hn' => by
      have := hf n'
      rw [show f n' = i from hn'] at this
      exact this
  exact ⟨i, 1, cf, one_pos, by rw [one_smul]; exact hcf⟩

end GlobalTheory.UPoinc.CellCones
