import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullLinInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim

namespace GlobalTheory.PolFan.CarDim

namespace Tw

/- English proof (translation)
Set `τ : E ≃+* E` to `IsFractionRing.ringEquivOfRingEquiv σ`. Establish `hτ : ∀ x : 𝓞 E, τ (x : E) = ((σ x : 𝓞 E) : E)` using `fun x => IsFractionRing.ringEquivOfRingEquiv_algebraMap σ x`. Set `φ : E →+* ℂ` to `Classical.choice inferInstance`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[H.bar_eq, ← hτ, H.bar_eq, ← hτ]`.

Apply `φ.injective` to reduce the goal to its premises. Establish `h1` using `IsCMField.complexEmbedding_complexConj E (φ.comp τ.toRingHom) (a : E)`. Establish `h2` using `IsCMField.complexEmbedding_complexConj E φ (τ (a : E))`. Simplify using `only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at h1`. Rewrite using `[h1, h2]`.
-/
theorem bar_comm {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (σ : 𝓞 E ≃+* 𝓞 E) (a : 𝓞 E) :
    σ (H.bar a) = H.bar (σ a) := by
  let τ : E ≃+* E := IsFractionRing.ringEquivOfRingEquiv σ
  have hτ : ∀ x : 𝓞 E, τ (x : E) = ((σ x : 𝓞 E) : E) := fun x =>
    IsFractionRing.ringEquivOfRingEquiv_algebraMap σ x
  let φ : E →+* ℂ := Classical.choice inferInstance
  apply RingOfIntegers.ext
  rw [H.bar_eq, ← hτ, H.bar_eq, ← hτ]
  apply φ.injective
  have h1 := IsCMField.complexEmbedding_complexConj E (φ.comp τ.toRingHom) (a : E)
  have h2 := IsCMField.complexEmbedding_complexConj E φ (τ (a : E))
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at h1
  rw [h1, h2]

end Tw

namespace Tw

section Gen

variable {O : Type} [CommRing O] {bar : O → O} {σ : O ≃+* O} {ψ : InvFun O}
  {Y Y' : Type} [AddCommGroup Y] [Module O Y] [AddCommGroup Y'] [Module O Y']

def pullA (τ : Y' ≃+ Y) : LinearMap.BilinForm ℤ Y →ₗ[ℤ] LinearMap.BilinForm ℤ Y' where
  toFun β := β.compl₁₂ τ.toIntLinearEquiv.toLinearMap τ.toIntLinearEquiv.toLinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem pullA_apply (τ : Y' ≃+ Y) (β : LinearMap.BilinForm ℤ Y) (a b : Y') : pullA τ β a b = β (τ a) (τ b) := rfl

/- English proof (translation)
The claim follows from `LinearMap.ext₂ fun a b => by simp`.
-/
@[simp] theorem pullA_symm_pullA (τ : Y' ≃+ Y) (β : LinearMap.BilinForm ℤ Y) : pullA τ.symm (pullA τ β) = β :=
  LinearMap.ext₂ fun a b => by simp

/- English proof (translation)
The claim follows from `LinearMap.ext₂ fun a b => by simp`.
-/
@[simp] theorem pullA_pullA_symm (τ : Y' ≃+ Y) (β : LinearMap.BilinForm ℤ Y') : pullA τ (pullA τ.symm β) = β :=
  LinearMap.ext₂ fun a b => by simp

/- English proof (translation)
Introduce `β β' h` and use `by rw [← pullA_symm_pullA τ β, h, pullA_symm_pullA]`.
-/
theorem pullA_injective (τ : Y' ≃+ Y) : Function.Injective (pullA τ) := fun β β' h => by
  rw [← pullA_symm_pullA τ β, h, pullA_symm_pullA]

/- English proof (translation)
Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hτ, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]`.
-/
theorem symm_smul {τ : Y' ≃+ Y} (hτ : ∀ (a : O) (y : Y'), τ (a • y) = σ a • τ y) (a : O) (y : Y) :
    τ.symm (a • y) = σ.symm a • τ.symm y := by
  apply τ.injective
  rw [hτ, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

/- English proof (translation)
Apply `σ.injective` to reduce the goal to its premises. Rewrite using `[RingEquiv.apply_symm_apply, hc, RingEquiv.apply_symm_apply]`.
-/
theorem symm_comm (hc : ∀ a, σ (bar a) = bar (σ a)) (a : O) : σ.symm (bar a) = bar (σ.symm a) := by
  apply σ.injective
  rw [RingEquiv.apply_symm_apply, hc, RingEquiv.apply_symm_apply]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun y z => h.1 _ _, fun a y z => by simp only [pullA_apply, hτ, h.2, hc]⟩`.
-/
theorem pullA_mem (hc : ∀ a, σ (bar a) = bar (σ a)) {τ : Y' ≃+ Y} (hτ : ∀ (a : O) (y : Y'), τ (a • y) = σ a • τ y)
    {β : LinearMap.BilinForm ℤ Y} (h : β ∈ balForms bar Y) : pullA τ β ∈ balForms bar Y' :=
  ⟨fun y z => h.1 _ _, fun a y z => by simp only [pullA_apply, hτ, h.2, hc]⟩

variable (σ ψ) in

def TwEval : Prop :=
  ∀ (Y Y' : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [AddCommGroup Y'] [Module O Y'] [Module.Finite O Y']
    (τ : Y' ≃+ Y), (∀ (a : O) (y : Y'), τ (a • y) = σ a • τ y) → ∀ B : Y → Y → ℝ,
      ψ.eval Y' (fun a b => B (τ a) (τ b)) = ψ.eval Y B

/- English proof (translation)
Introduce `Y Y' _ _ _ _ _ _ τ hτ B`. Establish `hs : ∀ (a : O) (y : Y), τ.symm (a • y) = σ a • τ.symm y` using `fun a y => by`. Simplify using `using symm_smul hτ a y`. Use `h Y' Y τ.symm hs fun a b => B (τ a) (τ b)` as an intermediate fact. Simplify using `only [AddEquiv.apply_symm_apply] at this`.

Conclude with `this.symm`.
-/
theorem TwEval.symm (h : TwEval σ ψ) : TwEval σ.symm ψ := by
  intro Y Y' _ _ _ _ _ _ τ hτ B
  have hs : ∀ (a : O) (y : Y), τ.symm (a • y) = σ a • τ.symm y := fun a y => by
    simpa using symm_smul hτ a y
  have := h Y' Y τ.symm hs fun a b => B (τ a) (τ b)
  simp only [AddEquiv.apply_symm_apply] at this
  exact this.symm

/- English proof (translation)
The claim follows from `h Y Y' τ hτ fun a b => (β a b : ℝ)`.
-/
theorem TwEval.evalZ (h : TwEval σ ψ) [Module.Finite O Y] [Module.Finite O Y'] {τ : Y' ≃+ Y}
    (hτ : ∀ (a : O) (y : Y'), τ (a • y) = σ a • τ y) (β : LinearMap.BilinForm ℤ Y) :
    ψ.evalZ (pullA τ β) = ψ.evalZ β :=
  h Y Y' τ hτ fun a b => (β a b : ℝ)

end Gen

end Tw

namespace Tw

section Cell

variable {O : Type} [CommRing O] {bar : O → O} {σ : O ≃+* O} {ψ : InvFun O}
  {Y Y' : Type} [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [AddCommGroup Y'] [Module O Y'] [Module.Finite O Y']
  {m : ℕ}

/- English proof (translation)
Establish `hs : ∀ (a : O) (y : Y), τ.symm (a • y) = σ.symm a • τ.symm y` using `symm_smul hτ`. Establish `hcs` using `symm_comm hc`. Use `⟨fun i => pullA_mem hc hτ (h.mem i), fun i y => h.nonneg i _, ?_, ?_⟩` and prove the remaining obligations. Introduce `c hcn`. Simplify using `only [hev.evalZ hτ]`.

Rewrite using `[← h.linear c hcn]`. Conclude with `hev Y Y' τ hτ fun a b => ∑ i, c i * (δ i a b : ℝ)`. Take `⟨N, ℓ, hN, h1, h2, h3⟩` from `h.strict`. Use `⟨N, ℓ ∘ₗ pullA τ.symm, hN, fun i => ?_, fun β hβ hp => ?_, fun β hβ hp he => ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, pullA_symm_pullA, hev.evalZ hτ]`.

Conclude with `h1 i`. Establish `hβ0` using `pullA_mem hcs hs hβ`. Establish `e : β = pullA τ (pullA τ.symm β)` using `(pullA_pullA_symm τ β).symm`. Rewrite using `[e, hev.evalZ hτ, LinearMap.comp_apply, pullA_symm_pullA]`. Conclude with `h2 _ hβ0 fun y => hp _`.

Establish `hβ0` using `pullA_mem hcs hs hβ`. Establish `e : β = pullA τ (pullA τ.symm β)` using `(pullA_pullA_symm τ β).symm`. Rewrite `he` using `[e, hev.evalZ hτ, LinearMap.comp_apply, pullA_symm_pullA]`. Take `⟨k, c, hk, hkc⟩` from `h3 _ hβ0 (fun y => hp _) he`. Use `⟨k, c, hk, ?_⟩` and prove the remaining obligations.

Use `congrArg (pullA τ) hkc` as an intermediate fact. Rewrite `this` using `[map_nsmul, pullA_pullA_symm, map_sum]`. Simplify `this` using `only [map_nsmul]`.
-/
theorem isCell_pullA (hc : ∀ a, σ (bar a) = bar (σ a)) (hev : TwEval σ ψ) {τ : Y' ≃+ Y}
    (hτ : ∀ (a : O) (y : Y'), τ (a • y) = σ a • τ y) {δ : Fin m → LinearMap.BilinForm ℤ Y} (h : IsCell bar ψ δ) :
    IsCell bar ψ fun i => pullA τ (δ i) := by
  have hs : ∀ (a : O) (y : Y), τ.symm (a • y) = σ.symm a • τ.symm y := symm_smul hτ
  have hcs := symm_comm hc
  refine ⟨fun i => pullA_mem hc hτ (h.mem i), fun i y => h.nonneg i _, ?_, ?_⟩
  · intro c hcn
    simp only [hev.evalZ hτ]
    rw [← h.linear c hcn]
    exact hev Y Y' τ hτ fun a b => ∑ i, c i * (δ i a b : ℝ)
  · obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := h.strict
    refine ⟨N, ℓ ∘ₗ pullA τ.symm, hN, fun i => ?_, fun β hβ hp => ?_, fun β hβ hp he => ?_⟩
    · simp only [LinearMap.comp_apply, pullA_symm_pullA, hev.evalZ hτ]
      exact h1 i
    · have hβ0 := pullA_mem hcs hs hβ
      have e : β = pullA τ (pullA τ.symm β) := (pullA_pullA_symm τ β).symm
      rw [e, hev.evalZ hτ, LinearMap.comp_apply, pullA_symm_pullA]
      exact h2 _ hβ0 fun y => hp _
    · have hβ0 := pullA_mem hcs hs hβ
      have e : β = pullA τ (pullA τ.symm β) := (pullA_pullA_symm τ β).symm
      rw [e, hev.evalZ hτ, LinearMap.comp_apply, pullA_symm_pullA] at he
      obtain ⟨k, c, hk, hkc⟩ := h3 _ hβ0 (fun y => hp _) he
      refine ⟨k, c, hk, ?_⟩
      have := congrArg (pullA τ) hkc
      rw [map_nsmul, pullA_pullA_symm, map_sum] at this
      simpa only [map_nsmul] using this

end Cell

end Tw

namespace Tw

section Quot

variable {O : Type} [CommRing O] {bar : O → O} {σ : O ≃+* O} {ψ : InvFun O}
  {Y Y' : Type} [AddCommGroup Y] [Module O Y] [AddCommGroup Y'] [Module O Y'] {m : ℕ}

/- English proof (translation)
Simplify using `only [mem_orad, pullA_apply, hτ]`. Prove the components needed by the constructor for the conclusion. Introduce `h a y`. Use `h (σ.symm a) (τ.symm y)` as an intermediate fact. Simplify using `using this`.

Introduce `h a y`. Conclude with `h _ _`.
-/
theorem mem_orad_pullA {τ : Y' ≃+ Y} (hτ : ∀ (a : O) (y : Y'), τ (a • y) = σ a • τ y) (β : LinearMap.BilinForm ℤ Y)
    (x : Y') : x ∈ orad (O := O) (pullA τ β) ↔ τ x ∈ orad (O := O) β := by
  simp only [mem_orad, pullA_apply, hτ]
  constructor
  · intro h a y
    have := h (σ.symm a) (τ.symm y)
    simpa using this
  · intro h a y
    exact h _ _

/- English proof (translation)
Use extensionality with `y`. Simplify using `only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, AddMonoidHom.coe_coe]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `(mem_orad_pullA hτ β x).1 hx`.

Introduce `hy`. Conclude with `⟨τ.symm y, (mem_orad_pullA hτ β _).2 (by simpa using hy), by simp⟩`.
-/
theorem map_orad_pullA {τ : Y' ≃+ Y} (hτ : ∀ (a : O) (y : Y'), τ (a • y) = σ a • τ y) (β : LinearMap.BilinForm ℤ Y) :
    (orad (O := O) (pullA τ β)).toAddSubgroup.map (τ : Y' →+ Y) = (orad (O := O) β).toAddSubgroup := by
  ext y
  simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, AddMonoidHom.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_orad_pullA hτ β x).1 hx
  · intro hy
    exact ⟨τ.symm y, (mem_orad_pullA hτ β _).2 (by simpa using hy), by simp⟩

def qMap {τ : Y' ≃+ Y} (hτ : ∀ (a : O) (y : Y'), τ (a • y) = σ a • τ y) (β : LinearMap.BilinForm ℤ Y) :
    (Y' ⧸ orad (O := O) (pullA τ β)) ≃+ (Y ⧸ orad (O := O) β) :=
  QuotientAddGroup.congr _ _ τ (map_orad_pullA hτ β)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem qMap_mk {τ : Y' ≃+ Y} (hτ : ∀ (a : O) (y : Y'), τ (a • y) = σ a • τ y) (β : LinearMap.BilinForm ℤ Y) (x : Y') :
    qMap hτ β (Submodule.Quotient.mk x) = Submodule.Quotient.mk (τ x) := rfl

/- English proof (translation)
Proceed by induction on `z using Submodule.Quotient.induction_on with`. Consider the case `H x => rw [← Submodule.Quotient.mk_smul, qMap_mk, qMap_mk, hτ, Submodule.Quotient.mk_smul]`.
-/
theorem qMap_smul {τ : Y' ≃+ Y} (hτ : ∀ (a : O) (y : Y'), τ (a • y) = σ a • τ y) (β : LinearMap.BilinForm ℤ Y) (a : O)
    (z : Y' ⧸ orad (O := O) (pullA τ β)) : qMap hτ β (a • z) = σ a • qMap hτ β z := by
  induction z using Submodule.Quotient.induction_on with
  | H x => rw [← Submodule.Quotient.mk_smul, qMap_mk, qMap_mk, hτ, Submodule.Quotient.mk_smul]

/- English proof (translation)
Unfold `genRank`. Establish `e : Submodule.span ℤ (Set.range fun i => pullA τ (γ i)) = (Submodule.span ℤ (Set.range γ)).map (pullA τ)`. Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `(Submodule.equivMapOfInjective _ (pullA_injective τ) _).finrank_eq.symm`.
-/
theorem genRank_pullA (τ : Y' ≃+ Y) (γ : Fin m → LinearMap.BilinForm ℤ Y) :
    genRank (fun i => pullA τ (γ i)) = genRank γ := by
  unfold genRank
  have e : Submodule.span ℤ (Set.range fun i => pullA τ (γ i)) = (Submodule.span ℤ (Set.range γ)).map (pullA τ) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [e]
  exact (Submodule.equivMapOfInjective _ (pullA_injective τ) _).finrank_eq.symm

end Quot

section Set

variable {O : Type} [CommRing O] {bar : O → O} {σ : O ≃+* O} {ψ : InvFun O}
  {Y Y' : Type} [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [AddCommGroup Y'] [Module O Y'] [Module.Finite O Y']

/- English proof (translation)
Introduce and unpack `k ⟨m, δ, h1, ⟨c, hc0, hcs⟩, rfl⟩`. Use `⟨m, fun i => pullA (qMap hτ β) (δ i), isCell_pullA hc hev (qMap_smul hτ β) h1, ⟨c, hc0, ?_⟩, genRank_pullA _ δ⟩` and prove the remaining obligations. Use `LinearMap.ext₂ fun a b => ?_` and prove the remaining obligations. Use `LinearMap.congr_fun₂ hcs (τ a) (τ b)` as an intermediate fact. Simplify `this` using `[LinearMap.sum_apply, qMap_mk]`.
-/
theorem cdimSet_subset (hc : ∀ a, σ (bar a) = bar (σ a)) (hev : TwEval σ ψ) {τ : Y' ≃+ Y}
    (hτ : ∀ (a : O) (y : Y'), τ (a • y) = σ a • τ y) (β : LinearMap.BilinForm ℤ Y) :
    cdimSet bar ψ Y (orad β) β ⊆ cdimSet bar ψ Y' (orad (pullA τ β)) (pullA τ β) := by
  rintro k ⟨m, δ, h1, ⟨c, hc0, hcs⟩, rfl⟩
  refine ⟨m, fun i => pullA (qMap hτ β) (δ i), isCell_pullA hc hev (qMap_smul hτ β) h1, ⟨c, hc0, ?_⟩,
    genRank_pullA _ δ⟩
  refine LinearMap.ext₂ fun a b => ?_
  have := LinearMap.congr_fun₂ hcs (τ a) (τ b)
  simpa [LinearMap.sum_apply, qMap_mk] using this

end Set

end Tw

namespace Tw

/- English proof (translation)
Introduce `Y Y' _ _ _ _ _ _ τ hτ B`. Take `⟨n, s, hs⟩` from `Module.Finite.exists_fin' (𝓞 E) Y`. Establish `hsy : ∀ (a : 𝓞 E) (y : Y), τ.symm (σ a • y) = a • τ.symm y` using `fun a y => by`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hτ, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]`.

Set `s' : (Fin n → 𝓞 E) →ₗ[𝓞 E] Y'` to `{ toFun := fun x => τ.symm (s fun i => σ (x i)) map_add' := fun x x' => by`. Establish `: (fun i => σ ((x + x') i)) = (fun i => σ (x i)) + fun i => σ (x' i)` using `by ext i; simp`. Rewrite using `[this, map_add, map_add]`. Use the proof step `map_smul' := fun c x => by`. Establish `: (fun i => σ ((c • x) i)) = σ c • fun i => σ (x i)` using `by ext i; simp`.

Rewrite using `[this, map_smul, hsy]`. Use `rfl }`. Establish `hs' : Function.Surjective s'` using `fun y => by`. Take `⟨x, hx⟩` from `hs (τ y)`. Use `⟨fun i => σ.symm (x i), ?_⟩` and prove the remaining obligations.

Use `show τ.symm (s fun i => σ (σ.symm (x i))) = y`. Simplify using `only [RingEquiv.apply_symm_apply]`. Rewrite using `[hx, AddEquiv.symm_apply_apply]`. Rewrite using `[ψ.eval_eq hs', ψ.eval_eq hs]`. Use `htw σ hσ n fun a b => B (s a) (s b)` as an intermediate fact.

Simplify `this` using `[s']`.
-/
theorem twEval_of_isTwInv {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {ψ : InvFun (𝓞 E)}
    (htw : IsTwInv H ψ) {σ : 𝓞 E ≃+* 𝓞 E} (hσ : σ H.w0 = H.w0) : TwEval σ ψ := by
  intro Y Y' _ _ _ _ _ _ τ hτ B
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin' (𝓞 E) Y
  have hsy : ∀ (a : 𝓞 E) (y : Y), τ.symm (σ a • y) = a • τ.symm y := fun a y => by
    apply τ.injective
    rw [hτ, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  let s' : (Fin n → 𝓞 E) →ₗ[𝓞 E] Y' :=
    { toFun := fun x => τ.symm (s fun i => σ (x i))
      map_add' := fun x x' => by
        have : (fun i => σ ((x + x') i)) = (fun i => σ (x i)) + fun i => σ (x' i) := by ext i; simp
        rw [this, map_add, map_add]
      map_smul' := fun c x => by
        have : (fun i => σ ((c • x) i)) = σ c • fun i => σ (x i) := by ext i; simp
        rw [this, map_smul, hsy]
        rfl }
  have hs' : Function.Surjective s' := fun y => by
    obtain ⟨x, hx⟩ := hs (τ y)
    refine ⟨fun i => σ.symm (x i), ?_⟩
    show τ.symm (s fun i => σ (σ.symm (x i))) = y
    simp only [RingEquiv.apply_symm_apply]
    rw [hx, AddEquiv.symm_apply_apply]
  rw [ψ.eval_eq hs', ψ.eval_eq hs]
  have := htw σ hσ n fun a b => B (s a) (s b)
  simpa [s'] using this

end Tw

/- English proof (translation)
Introduce `E _ _ _ H ψ htw σ hσ n B`. Establish `hc : ∀ a, σ (H.bar a) = H.bar (σ a)` using `Tw.bar_comm H σ`. Establish `hev : Tw.TwEval σ ψ` using `Tw.twEval_of_isTwInv htw hσ`. Set `τ : (Fin n → 𝓞 E) ≃+ (Fin n → 𝓞 E)` to `AddEquiv.piCongrRight fun _ => σ.toAddEquiv`. Establish `hτ : ∀ (a : 𝓞 E) (y : Fin n → 𝓞 E), τ (a • y) = σ a • τ y` using `fun a y => by ext i; simp [τ]`.

Establish `hτs` using `Tw.symm_smul hτ`. Establish `hcs` using `Tw.symm_comm hc`. Use `show (carFun (⇑H.bar) ψ).toFun n (fun a b => B (τ a) (τ b)) = (carFun (⇑H.bar) ψ).toFun n B`. Simplify using `only [carFun]`. Distinguish the cases in `h : ∃ β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E), β ∈ balForms (⇑H.bar) (Fin n → 𝓞 E) ∧ (∀ y, 0 ≤ β y y) ∧ ∀ a b, B a b = β a b`.

Establish `h' : ∃ β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E), β ∈ balForms (⇑H.bar) (Fin n → 𝓞 E) ∧ (∀ y, 0 ≤ β y y) ∧ ∀ a b, B (τ a) (τ b) = β a b` using `⟨Tw.pullA τ h.choose, Tw.pullA_mem hc hτ h.choose_spec.1, fun y => h.choose_spec.2.1 _, fun a b => h.choose_spec.2.2 _ _⟩`. Rewrite using `[dif_pos h, dif_pos h']`. Establish `e : h'.choose = Tw.pullA τ h.choose` using `LinearMap.ext₂ fun a b => by`. Establish `h1` using `h'.choose_spec.2.2 a b`. Establish `h2` using `h.choose_spec.2.2 (τ a) (τ b)`.

Rewrite using `[Tw.pullA_apply]`. Conclude with `h1.symm.trans h2` after adjusting the coercions. Rewrite using `[e]`. Unfold `cdimQ`. Use `congr 2`.

Use `(Set.Subset.antisymm ?_ (Tw.cdimSet_subset hc hev hτ _))` and prove the remaining obligations. Use `Tw.cdimSet_subset (bar := ⇑H.bar) (ψ := ψ) hcs hev.symm hτs (Tw.pullA τ h.choose)` as an intermediate fact. Rewrite `this` using `[Tw.pullA_symm_pullA]`. Then use the resulting hypothesis. Establish `h' : ¬ ∃ β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E), β ∈ balForms (⇑H.bar) (Fin n → 𝓞 E) ∧ (∀ y, 0 ≤ β y y) ∧ ∀ a b, B (τ a) (τ b) = β a b`. Introduce and unpack `⟨β, h1, h2, h3⟩`.

Use `h ⟨Tw.pullA τ.symm β, Tw.pullA_mem hcs hτs h1, fun y => h2 _, fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[Tw.pullA_apply, ← h3, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]`. Rewrite using `[dif_neg h, dif_neg h']`.
-/
theorem isTwInv_carFun : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ψ : InvFun (𝓞 E)),
    IsTwInv H ψ → IsTwInv H (carFun H.bar ψ) := by
  intro E _ _ _ H ψ htw σ hσ n B
  have hc : ∀ a, σ (H.bar a) = H.bar (σ a) := Tw.bar_comm H σ
  have hev : Tw.TwEval σ ψ := Tw.twEval_of_isTwInv htw hσ
  let τ : (Fin n → 𝓞 E) ≃+ (Fin n → 𝓞 E) := AddEquiv.piCongrRight fun _ => σ.toAddEquiv
  have hτ : ∀ (a : 𝓞 E) (y : Fin n → 𝓞 E), τ (a • y) = σ a • τ y := fun a y => by ext i; simp [τ]
  have hτs := Tw.symm_smul hτ
  have hcs := Tw.symm_comm hc
  show (carFun (⇑H.bar) ψ).toFun n (fun a b => B (τ a) (τ b)) = (carFun (⇑H.bar) ψ).toFun n B
  dsimp only [carFun]
  by_cases h : ∃ β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E), β ∈ balForms (⇑H.bar) (Fin n → 𝓞 E) ∧ (∀ y, 0 ≤ β y y) ∧
      ∀ a b, B a b = β a b
  · have h' : ∃ β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E), β ∈ balForms (⇑H.bar) (Fin n → 𝓞 E) ∧ (∀ y, 0 ≤ β y y) ∧
        ∀ a b, B (τ a) (τ b) = β a b :=
      ⟨Tw.pullA τ h.choose, Tw.pullA_mem hc hτ h.choose_spec.1, fun y => h.choose_spec.2.1 _,
        fun a b => h.choose_spec.2.2 _ _⟩
    rw [dif_pos h, dif_pos h']
    have e : h'.choose = Tw.pullA τ h.choose := LinearMap.ext₂ fun a b => by
      have h1 := h'.choose_spec.2.2 a b
      have h2 := h.choose_spec.2.2 (τ a) (τ b)
      rw [Tw.pullA_apply]
      exact_mod_cast h1.symm.trans h2
    rw [e]
    unfold cdimQ
    congr 2
    refine (Set.Subset.antisymm ?_ (Tw.cdimSet_subset hc hev hτ _))
    have := Tw.cdimSet_subset (bar := ⇑H.bar) (ψ := ψ) hcs hev.symm hτs (Tw.pullA τ h.choose)
    rwa [Tw.pullA_symm_pullA] at this
  · have h' : ¬ ∃ β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E), β ∈ balForms (⇑H.bar) (Fin n → 𝓞 E) ∧ (∀ y, 0 ≤ β y y) ∧
        ∀ a b, B (τ a) (τ b) = β a b := by
      rintro ⟨β, h1, h2, h3⟩
      refine h ⟨Tw.pullA τ.symm β, Tw.pullA_mem hcs hτs h1, fun y => h2 _, fun a b => ?_⟩
      rw [Tw.pullA_apply, ← h3, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    rw [dif_neg h, dif_neg h']

end GlobalTheory.PolFan.CarDim
