import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LimitPairSpaces.TensorSpanEqPairSpace

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.LV

open PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.E

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Proceed by induction on `h using Submodule.span_induction with`. Consider the case `mem _ hx => exact hx.2`. Consider the case `zero`. Use `⟨fun u _ g => rfl, fun g => ?_⟩` and prove the remaining obligations. Establish `e : (fun k : Kinf E N => (0 : Sm E N).1 (g * infGL E N (Unitary.toUnits k))) = 0` using `rfl`.

Rewrite using `[e]`. Conclude with `W.zero_mem`. Consider the case `add x y _ _ hx hy`. Use `⟨fun u hu g => ?_, fun g => ?_⟩` and prove the remaining obligations. Use `show x.1 (g * finGL E N u) + y.1 (g * finGL E N u) = x.1 g + y.1 g`.

Rewrite using `[hx.1 u hu g, hy.1 u hu g]`. Establish `e : (fun k : Kinf E N => (x + y).1 (g * infGL E N (Unitary.toUnits k))) = (fun k : Kinf E N => x.1 (g * infGL E N (Unitary.toUnits k))) + fun k : Kinf E N => y.1 (g * infGL E N (Unitary.toUnits k))` using `rfl`. Rewrite using `[e]`. Conclude with `W.add_mem (hx.2 g) (hy.2 g)`. Consider the case `smul c x _ hx`.

Use `⟨fun u hu g => ?_, fun g => ?_⟩` and prove the remaining obligations. Use `show c * x.1 (g * finGL E N u) = c * x.1 g`. Rewrite using `[hx.1 u hu g]`. Establish `e : (fun k : Kinf E N => (c • x).1 (g * infGL E N (Unitary.toUnits k))) = c • fun k : Kinf E N => x.1 (g * infGL E N (Unitary.toUnits k))` using `rfl`. Rewrite using `[e]`.

Conclude with `W.smul_mem c (hx.2 g)`.
-/
theorem typeB_of_mem_typSp {N : ℕ} {K : Subgroup (GL (Fin N) (Af E))} {W : Submodule ℂ (Kinf E N → ℂ)}
    {U : Submodule ℂ (Sm E N)} {φ : Sm E N} (h : φ ∈ TypSp K W U) : TypeB K W φ := by
  induction h using Submodule.span_induction with
  | mem _ hx => exact hx.2
  | zero =>
    refine ⟨fun u _ g => rfl, fun g => ?_⟩
    have e : (fun k : Kinf E N => (0 : Sm E N).1 (g * infGL E N (Unitary.toUnits k))) = 0 := rfl
    rw [e]
    exact W.zero_mem
  | add x y _ _ hx hy =>
    refine ⟨fun u hu g => ?_, fun g => ?_⟩
    · show x.1 (g * finGL E N u) + y.1 (g * finGL E N u) = x.1 g + y.1 g
      rw [hx.1 u hu g, hy.1 u hu g]
    · have e : (fun k : Kinf E N => (x + y).1 (g * infGL E N (Unitary.toUnits k))) =
          (fun k : Kinf E N => x.1 (g * infGL E N (Unitary.toUnits k))) +
            fun k : Kinf E N => y.1 (g * infGL E N (Unitary.toUnits k)) := rfl
      rw [e]
      exact W.add_mem (hx.2 g) (hy.2 g)
  | smul c x _ hx =>
    refine ⟨fun u hu g => ?_, fun g => ?_⟩
    · show c * x.1 (g * finGL E N u) = c * x.1 g
      rw [hx.1 u hu g]
    · have e : (fun k : Kinf E N => (c • x).1 (g * infGL E N (Unitary.toUnits k))) =
          c • fun k : Kinf E N => x.1 (g * infGL E N (Unitary.toUnits k)) := rfl
      rw [e]
      exact W.smul_mem c (hx.2 g)

/- English proof (translation)
The claim follows from `Submodule.span_le.2 fun _ h => h.1`.
-/
theorem typSp_le {N : ℕ} (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ))
    (U : Submodule ℂ (Sm E N)) : TypSp K W U ≤ U :=
  Submodule.span_le.2 fun _ h => h.1

/- English proof (translation)
The claim follows from `Submodule.span_mono fun _ h => ⟨hU h.1, fun u hu g => h.2.1 u (hK hu) g, fun g => hW (h.2.2 g)⟩`.
-/
theorem typSp_mono {N : ℕ} {K K' : Subgroup (GL (Fin N) (Af E))} {W W' : Submodule ℂ (Kinf E N → ℂ)}
    {U U' : Submodule ℂ (Sm E N)} (hK : K' ≤ K) (hW : W ≤ W') (hU : U ≤ U') : TypSp K W U ≤ TypSp K' W' U' :=
  Submodule.span_mono fun _ h => ⟨hU h.1, fun u hu g => h.2.1 u (hK hu) g, fun g => hW (h.2.2 g)⟩

/- English proof (translation)
The claim follows from `Submodule.span_mono fun _ ⟨φ₁, hφ₁, φ₂, hφ₂, e⟩ => ⟨φ₁, h₁ hφ₁, φ₂, h₂ hφ₂, e⟩`.
-/
theorem tensor_span_mono {a b : ℕ} {U₁ U₁' : Submodule ℂ (Sm E a)} {U₂ U₂' : Submodule ℂ (Sm E b)} (h₁ : U₁ ≤ U₁')
    (h₂ : U₂ ≤ U₂') : tens2 U₁ U₂ ≤ tens2 U₁' U₂' :=
  Submodule.span_mono fun _ ⟨φ₁, hφ₁, φ₂, hφ₂, e⟩ => ⟨φ₁, h₁ hφ₁, φ₂, h₂ hφ₂, e⟩

def prodBil {a b : ℕ} (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) :
    U₁ →ₗ[ℂ] U₂ →ₗ[ℂ] (GA E a × GA E b → ℂ) :=
  LinearMap.mk₂ ℂ (fun φ₁ φ₂ m => φ₁.1.1 m.1 * φ₂.1.1 m.2)
    (fun x y z => by funext m; simp [add_mul])
    (fun c x z => by funext m; simp [mul_assoc])
    (fun x y z => by funext m; simp [mul_add])
    (fun c x z => by funext m; simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul]; ring)

/- English proof (translation)
Use `Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (TensorProduct.lift (prodBil U₁ U₂))) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨φ₁, h₁, φ₂, h₂, rfl⟩`. Conclude with `⟨(⟨φ₁, h₁⟩ : U₁) ⊗ₜ[ℂ] (⟨φ₂, h₂⟩ : U₂), by rw [TensorProduct.lift.tmul]; rfl⟩`.
-/
theorem fd_tens2 {a b : ℕ} (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) [FiniteDimensional ℂ U₁]
    [FiniteDimensional ℂ U₂] : FiniteDimensional ℂ (tens2 U₁ U₂) := by
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (TensorProduct.lift (prodBil U₁ U₂)))
    (Submodule.span_le.2 ?_)
  rintro _ ⟨φ₁, h₁, φ₂, h₂, rfl⟩
  exact ⟨(⟨φ₁, h₁⟩ : U₁) ⊗ₜ[ℂ] (⟨φ₂, h₂⟩ : U₂), by rw [TensorProduct.lift.tmul]; rfl⟩

/- English proof (translation)
Establish `hinj : LinearMap.ker (j.comp A.subtype) = ⊥` using `LinearMap.ker_eq_bot.2 (hj.comp Subtype.val_injective)`. Take `⟨L, hL⟩` from `LinearMap.exists_leftInverse_of_injective (j.comp A.subtype) hinj`. Use `⟨fun i => (L (j (f i)) : V), fun i => (L (j (f i))).2, fun x y => ?_⟩` and prove the remaining obligations. Take `⟨χ, hχ, e⟩` from `hs y`. Establish `e1 : (fun x => ∑ i, j (f i) x * g i y) = ∑ i, g i y • j (f i)`.

Use function extensionality and compare the values at `x`. Simplify using `[Finset.sum_apply, mul_comm]`. Establish `e2 : (⟨χ, hχ⟩ : A) = ∑ i, g i y • L (j (f i))`. Establish `h3 : L ((j.comp A.subtype) ⟨χ, hχ⟩) = ⟨χ, hχ⟩` using `LinearMap.congr_fun hL _`. Rewrite using `[← h3, LinearMap.comp_apply, Submodule.subtype_apply, e, e1, map_sum]`.

Simplify using `only [map_smul]`. Establish `e3` using `congrArg (fun v : A => j (v : V) x) e2`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at e3`. Rewrite using `[← congrFun e x, e3]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`.
-/
theorem sep_left {X Y V : Type} [AddCommGroup V] [Module ℂ V] (j : V →ₗ[ℂ] (X → ℂ)) (hj : Function.Injective j)
    (A : Submodule ℂ V) {n : ℕ} (f : Fin n → V) (g : Fin n → Y → ℂ)
    (hs : ∀ y, ∃ χ ∈ A, j χ = fun x => ∑ i, j (f i) x * g i y) :
    ∃ f' : Fin n → V, (∀ i, f' i ∈ A) ∧ ∀ x y, ∑ i, j (f i) x * g i y = ∑ i, j (f' i) x * g i y := by
  have hinj : LinearMap.ker (j.comp A.subtype) = ⊥ :=
    LinearMap.ker_eq_bot.2 (hj.comp Subtype.val_injective)
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective (j.comp A.subtype) hinj
  refine ⟨fun i => (L (j (f i)) : V), fun i => (L (j (f i))).2, fun x y => ?_⟩
  obtain ⟨χ, hχ, e⟩ := hs y
  have e1 : (fun x => ∑ i, j (f i) x * g i y) = ∑ i, g i y • j (f i) := by
    funext x
    simp [Finset.sum_apply, mul_comm]
  have e2 : (⟨χ, hχ⟩ : A) = ∑ i, g i y • L (j (f i)) := by
    have h3 : L ((j.comp A.subtype) ⟨χ, hχ⟩) = ⟨χ, hχ⟩ := LinearMap.congr_fun hL _
    rw [← h3, LinearMap.comp_apply, Submodule.subtype_apply, e, e1, map_sum]
    simp only [map_smul]
  have e3 := congrArg (fun v : A => j (v : V) x) e2
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at e3
  rw [← congrFun e x, e3]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/- English proof (translation)
Take `⟨f', hf', e⟩` from `sep_left (X := Y) (Y := X) j hj B f g fun x => by`. Take `⟨χ, hχ, e⟩` from `hs x`. Conclude with `⟨χ, hχ, by rw [e]; funext y; exact Finset.sum_congr rfl fun i _ => mul_comm _ _⟩`. Use `⟨f', hf', fun x y => ?_⟩` and prove the remaining obligations. Use `e y x` as an intermediate fact.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem sep_right {X Y V : Type} [AddCommGroup V] [Module ℂ V] (j : V →ₗ[ℂ] (Y → ℂ)) (hj : Function.Injective j)
    (B : Submodule ℂ V) {n : ℕ} (g : Fin n → X → ℂ) (f : Fin n → V)
    (hs : ∀ x, ∃ χ ∈ B, j χ = fun y => ∑ i, g i x * j (f i) y) :
    ∃ f' : Fin n → V, (∀ i, f' i ∈ B) ∧ ∀ x y, ∑ i, g i x * j (f i) y = ∑ i, g i x * j (f' i) y := by
  obtain ⟨f', hf', e⟩ := sep_left (X := Y) (Y := X) j hj B f g fun x => by
    obtain ⟨χ, hχ, e⟩ := hs x
    exact ⟨χ, hχ, by rw [e]; funext y; exact Finset.sum_congr rfl fun i _ => mul_comm _ _⟩
  refine ⟨f', hf', fun x y => ?_⟩
  have := e y x
  calc ∑ i, g i x * j (f i) y = ∑ i, j (f i) y * g i x := Finset.sum_congr rfl fun i _ => mul_comm _ _
    _ = ∑ i, j (f' i) y * g i x := this
    _ = _ := Finset.sum_congr rfl fun i _ => mul_comm _ _

/- English proof (translation)
Take `⟨n, ψ₁, ψ₂, hψ₁, hψ₂, rfl⟩` from `InducedTensorMap.tensor_pair_finite_sum hF`. Take `⟨φ₁, hφ₁, e₁⟩` from `sep_left (Sm E a).subtype Subtype.val_injective (TypSp K₁ W₁ U₁) ψ₁ (fun i y => (ψ₂ i).1 y) fun y => by`. Use `⟨∑ i, (ψ₂ i).1 y • ψ₁ i, Submodule.subset_span ⟨Submodule.sum_mem _ fun i _ => U₁.smul_mem _ (hψ₁ i), ?_⟩, ?_⟩` and prove the remaining obligations. Establish `e : (∑ i, (ψ₂ i).1 y • ψ₁ i).1 = fun x => ∑ i, (ψ₁ i).1 x * (ψ₂ i).1 y`. Use function extensionality and compare the values at `x`.

Simplify using `[Finset.sum_apply, mul_comm]`. Rewrite using `[typeB_iff, e]`. Conclude with `h₁ y`. Use function extensionality and compare the values at `x`. Simplify using `[Finset.sum_apply, mul_comm]`.

Take `⟨φ₂, hφ₂, e₂⟩` from `sep_right (Sm E b).subtype Subtype.val_injective (TypSp K₂ W₂ U₂) (fun i x => (φ₁ i).1 x) ψ₂ fun x => by`. Use `⟨∑ i, (φ₁ i).1 x • ψ₂ i, Submodule.subset_span ⟨Submodule.sum_mem _ fun i _ => U₂.smul_mem _ (hψ₂ i), ?_⟩, ?_⟩` and prove the remaining obligations. Establish `e : (∑ i, (φ₁ i).1 x • ψ₂ i).1 = fun y => ∑ i, (ψ₁ i).1 x * (ψ₂ i).1 y`. Use function extensionality and compare the values at `y`. Establish `h` using `e₁ x y`.

Simplify using `only [Submodule.subtype_apply] at h`. Rewrite using `[h]`. Simplify using `[Finset.sum_apply]`. Rewrite using `[typeB_iff, e]`. Conclude with `h₂ x`.

Use function extensionality and compare the values at `y`. Simplify using `[Finset.sum_apply]`. Establish `e : (fun m : GA E a × GA E b => ∑ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2) = fun m => ∑ i, (φ₁ i).1 m.1 * (φ₂ i).1 m.2`. Use function extensionality and compare the values at `m`. Conclude with `(e₁ m.1 m.2).trans (e₂ m.1 m.2)`.

Rewrite using `[e]`. Conclude with `InducedTensorMap.A.sum_mem hφ₁ hφ₂`.
-/
theorem tens_typ {a b : ℕ} {U₁ : Submodule ℂ (Sm E a)} {U₂ : Submodule ℂ (Sm E b)}
    {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))} {W₁ : Submodule ℂ (Kinf E a → ℂ)}
    {W₂ : Submodule ℂ (Kinf E b → ℂ)} {F : GA E a × GA E b → ℂ} (hF : F ∈ tens2 U₁ U₂)
    (h₁ : ∀ y, TypF K₁ W₁ fun x => F (x, y)) (h₂ : ∀ x, TypF K₂ W₂ fun y => F (x, y)) :
    F ∈ tens2 (TypSp K₁ W₁ U₁) (TypSp K₂ W₂ U₂) := by
  obtain ⟨n, ψ₁, ψ₂, hψ₁, hψ₂, rfl⟩ := InducedTensorMap.tensor_pair_finite_sum hF
  obtain ⟨φ₁, hφ₁, e₁⟩ := sep_left (Sm E a).subtype Subtype.val_injective (TypSp K₁ W₁ U₁) ψ₁
    (fun i y => (ψ₂ i).1 y) fun y => by
      refine ⟨∑ i, (ψ₂ i).1 y • ψ₁ i, Submodule.subset_span ⟨Submodule.sum_mem _ fun i _ =>
        U₁.smul_mem _ (hψ₁ i), ?_⟩, ?_⟩
      · have e : (∑ i, (ψ₂ i).1 y • ψ₁ i).1 = fun x => ∑ i, (ψ₁ i).1 x * (ψ₂ i).1 y := by
          funext x
          simp [Finset.sum_apply, mul_comm]
        rw [typeB_iff, e]
        exact h₁ y
      · funext x
        simp [Finset.sum_apply, mul_comm]
  obtain ⟨φ₂, hφ₂, e₂⟩ := sep_right (Sm E b).subtype Subtype.val_injective (TypSp K₂ W₂ U₂)
    (fun i x => (φ₁ i).1 x) ψ₂ fun x => by
      refine ⟨∑ i, (φ₁ i).1 x • ψ₂ i, Submodule.subset_span ⟨Submodule.sum_mem _ fun i _ =>
        U₂.smul_mem _ (hψ₂ i), ?_⟩, ?_⟩
      · have e : (∑ i, (φ₁ i).1 x • ψ₂ i).1 = fun y => ∑ i, (ψ₁ i).1 x * (ψ₂ i).1 y := by
          funext y
          have h := e₁ x y
          simp only [Submodule.subtype_apply] at h
          rw [h]
          simp [Finset.sum_apply]
        rw [typeB_iff, e]
        exact h₂ x
      · funext y
        simp [Finset.sum_apply]
  have e : (fun m : GA E a × GA E b => ∑ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2) =
      fun m => ∑ i, (φ₁ i).1 m.1 * (φ₂ i).1 m.2 := by
    funext m
    exact (e₁ m.1 m.2).trans (e₂ m.1 m.2)
  rw [e]
  exact InducedTensorMap.A.sum_mem hφ₁ hφ₂

/- English proof (translation)
Rewrite `hF`, the goal using `[tensor_span_eq_pair_space]`. Use `tens_typ hF (fun y => ⟨fun u hu g => ?_, fun g => ?_⟩) (fun x => ⟨fun u hu g => ?_, fun g => ?_⟩)` and prove the remaining obligations. Use `hT.1 u hu 1 (one_mem _) (g, y)` as an intermediate fact. Simplify `this` using `[map_one]`. Set `R : (Kinf E a × Kinf E b → ℂ) →ₗ[ℂ] (Kinf E a → ℂ)` to `{ toFun := fun z k => z (k, 1), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }`.

Establish `hR : (Submodule.span ℂ {f | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k : Kinf E a × Kinf E b => w₁ k.1 * w₂ k.2}).map R ≤ W₁`. Rewrite using `[Submodule.map_span_le]`. Introduce and unpack `_ ⟨w₁, hw₁, w₂, hw₂, rfl⟩`. Establish `e : R (fun k : Kinf E a × Kinf E b => w₁ k.1 * w₂ k.2) = w₂ 1 • w₁`. Use function extensionality and compare the values at `k`.

Simplify using `[R, mul_comm]`. Rewrite using `[e]`. Conclude with `W₁.smul_mem _ hw₁`. Establish `hm` using `hR (Submodule.mem_map_of_mem (f := R) (hT.2 (g, y)))`. Establish `e : R (fun k : Kinf E a × Kinf E b => F ((g, y) * (infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2)))) = fun k => F (g * infGL E a (Unitary.toUnits k), y)`.

Use function extensionality and compare the values at `k`. Simplify using `[R, map_one]`. Rewrite `hm` using `[e]`. Conclude with `hm`. Use `hT.1 1 (one_mem _) u hu (x, g)` as an intermediate fact.

Simplify `this` using `[map_one]`. Set `R : (Kinf E a × Kinf E b → ℂ) →ₗ[ℂ] (Kinf E b → ℂ)` to `{ toFun := fun z k => z (1, k), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }`. Establish `hR : (Submodule.span ℂ {f | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k : Kinf E a × Kinf E b => w₁ k.1 * w₂ k.2}).map R ≤ W₂`. Rewrite using `[Submodule.map_span_le]`. Introduce and unpack `_ ⟨w₁, hw₁, w₂, hw₂, rfl⟩`.

Establish `e : R (fun k : Kinf E a × Kinf E b => w₁ k.1 * w₂ k.2) = w₁ 1 • w₂`. Use function extensionality and compare the values at `k`. Simplify using `[R]`. Rewrite using `[e]`. Conclude with `W₂.smul_mem _ hw₂`.

Establish `hm` using `hR (Submodule.mem_map_of_mem (f := R) (hT.2 (x, g)))`. Establish `e : R (fun k : Kinf E a × Kinf E b => F ((x, g) * (infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2)))) = fun k => F (x, g * infGL E b (Unitary.toUnits k))`. Use function extensionality and compare the values at `k`. Simplify using `[R, map_one]`. Rewrite `hm` using `[e]`.

Conclude with `hm`.
-/
theorem pair_typ {a b : ℕ} {U₁ : Submodule ℂ (Sm E a)} {U₂ : Submodule ℂ (Sm E b)}
    {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))} {W₁ : Submodule ℂ (Kinf E a → ℂ)}
    {W₂ : Submodule ℂ (Kinf E b → ℂ)} {F : H E a b → ℂ} (hF : F ∈ pairSpace U₁ U₂) (hT : TypeH K₁ K₂ W₁ W₂ F) :
    F ∈ pairSpace (TypSp K₁ W₁ U₁) (TypSp K₂ W₂ U₂) := by
  rw [tensor_span_eq_pair_space] at hF ⊢
  refine tens_typ hF (fun y => ⟨fun u hu g => ?_, fun g => ?_⟩) (fun x => ⟨fun u hu g => ?_, fun g => ?_⟩)
  · have := hT.1 u hu 1 (one_mem _) (g, y)
    simpa [map_one] using this
  · let R : (Kinf E a × Kinf E b → ℂ) →ₗ[ℂ] (Kinf E a → ℂ) :=
      { toFun := fun z k => z (k, 1), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hR : (Submodule.span ℂ {f | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k : Kinf E a × Kinf E b => w₁ k.1 * w₂ k.2}).map R ≤
        W₁ := by
      rw [Submodule.map_span_le]
      rintro _ ⟨w₁, hw₁, w₂, hw₂, rfl⟩
      have e : R (fun k : Kinf E a × Kinf E b => w₁ k.1 * w₂ k.2) = w₂ 1 • w₁ := by
        funext k
        simp [R, mul_comm]
      rw [e]
      exact W₁.smul_mem _ hw₁
    have hm := hR (Submodule.mem_map_of_mem (f := R) (hT.2 (g, y)))
    have e : R (fun k : Kinf E a × Kinf E b => F ((g, y) * (infGL E a (Unitary.toUnits k.1),
        infGL E b (Unitary.toUnits k.2)))) = fun k => F (g * infGL E a (Unitary.toUnits k), y) := by
      funext k
      simp [R, map_one]
    rw [e] at hm
    exact hm
  · have := hT.1 1 (one_mem _) u hu (x, g)
    simpa [map_one] using this
  · let R : (Kinf E a × Kinf E b → ℂ) →ₗ[ℂ] (Kinf E b → ℂ) :=
      { toFun := fun z k => z (1, k), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hR : (Submodule.span ℂ {f | ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, f = fun k : Kinf E a × Kinf E b => w₁ k.1 * w₂ k.2}).map R ≤
        W₂ := by
      rw [Submodule.map_span_le]
      rintro _ ⟨w₁, hw₁, w₂, hw₂, rfl⟩
      have e : R (fun k : Kinf E a × Kinf E b => w₁ k.1 * w₂ k.2) = w₁ 1 • w₂ := by
        funext k
        simp [R]
      rw [e]
      exact W₂.smul_mem _ hw₂
    have hm := hR (Submodule.mem_map_of_mem (f := R) (hT.2 (x, g)))
    have e : R (fun k : Kinf E a × Kinf E b => F ((x, g) * (infGL E a (Unitary.toUnits k.1),
        infGL E b (Unitary.toUnits k.2)))) = fun k => F (x, g * infGL E b (Unitary.toUnits k)) := by
      funext k
      simp [R, map_one]
    rw [e] at hm
    exact hm

end PositivityTheory.Rg.BcB.SpectralAccumulation.LV

end
