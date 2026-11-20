import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BetaCounterexample
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (c : Coeff l)

omit [NumberField E] [IsCMField E] in
/- English proof (translation)
The claim follows from `inf_idem _`.
-/
theorem ln_std (n : ℕ) : (⟨stdLat E n⟩ : GenLat E n).Ln = stdLat E n := inf_idem _

/- English proof (translation)
Establish `h1 : Submodule.span (𝓞 c.F) {β} = 1`. Break down `hβ with rfl | rfl` into its components or cases. Conclude with `(Submodule.one_eq_span).symm`. Rewrite using `[Submodule.one_eq_span, ← Set.neg_singleton, Submodule.span_neg]`. Apply the tactic sequence `refine ⟨by rcases hβ with rfl | rfl <;> simp, ?_, ?_⟩`.

Unfold `BetaIs`. Rewrite using `[h1, one_mul, ln_std]`. Introduce `σ`. Rewrite using `[ln_std]`. Apply the tactic sequence `rcases hβ with rfl | rfl <;> simp`.
-/
theorem std_one (n : ℕ) (β : c.F) (hβ : β = 1 ∨ β = -1) :
    β ≠ 0 ∧ BetaIs (Dw := Dw) c (⟨stdLat E n⟩ : GenLat E n) β ∧ BetaAbs (Dw := Dw) c (⟨stdLat E n⟩ : GenLat E n) β := by
  have h1 : Submodule.span (𝓞 c.F) {β} = 1 := by
    rcases hβ with rfl | rfl
    · exact (Submodule.one_eq_span).symm
    · rw [Submodule.one_eq_span, ← Set.neg_singleton, Submodule.span_neg]
  refine ⟨by rcases hβ with rfl | rfl <;> simp, ?_, ?_⟩
  · unfold BetaIs
    rw [h1, one_mul, ln_std]
  · intro σ
    rw [ln_std]
    rcases hβ with rfl | rfl <;> simp

/- English proof (translation)
Unfold `betaH`. Establish `e` using `funext fun β => propext (h β)`. Generalize the expression as in `(fun β : c.F => β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β) = p at e ⊢`. Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem betaH_congr {n m : ℕ} (Λ : GenLat E n) (Λ' : GenLat E m)
    (h : ∀ β : c.F, (β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β) ↔
      (β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ' β ∧ BetaAbs (Dw := Dw) c Λ' β)) :
    betaH (Dw := Dw) c Λ = betaH (Dw := Dw) c Λ' := by
  unfold betaH
  have e := funext fun β => propext (h β)
  generalize (fun β : c.F => β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β) = p at e ⊢
  subst e
  rfl

/- English proof (translation)
Unfold `betaH`. Use `split_ifs with h`. Conclude with `h.choose_spec.1`. Conclude with `one_ne_zero`.
-/
theorem betaH_ne_zero {n : ℕ} (Λ : GenLat E n) : betaH (Dw := Dw) c Λ ≠ 0 := by
  unfold betaH
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_ne_zero

omit [NumberField E] [IsCMField E] in

/- English proof (translation)
Establish `key : ∀ w : Fin n → Fin n → E, Matrix.det (Matrix.of fun i j => (a • w j) i) = a ^ n * Matrix.det (Matrix.of fun i j => w j i)`. Introduce `w`. Establish `: (Matrix.of fun i j => (a • w j) i) = a • (Matrix.of fun i j => w j i)`. Use extensionality with `i j`. Simplify using the standard rewrite rules.

Rewrite using `[this, Matrix.det_smul, Fintype.card_fin]`. Use extensionality with `d`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, rfl⟩ choose w hw hw' using fun i => (h (v i)).1 (hv i)`. Use `⟨_, ⟨w, hw, rfl⟩, ?_⟩` and prove the remaining obligations.

Establish `: v = fun j => a • w j` using `funext hw'`. Substitute `this` using the available equality. Conclude with `(key w).symm`. Introduce and unpack `⟨_, ⟨w, hw, rfl⟩, rfl⟩`. Conclude with `⟨fun j => a • w j, fun i => (h _).2 ⟨w i, hw i, rfl⟩, (key w).symm⟩`.
-/
theorem detSet_scale {n : ℕ} (M M' : Submodule (𝓞 E) (Fin n → E)) (a : E)
    (h : ∀ v, v ∈ M' ↔ ∃ w ∈ M, v = a • w) : detSet M' = (fun d => a ^ n * d) '' detSet M := by
  have key : ∀ w : Fin n → Fin n → E, Matrix.det (Matrix.of fun i j => (a • w j) i) =
      a ^ n * Matrix.det (Matrix.of fun i j => w j i) := by
    intro w
    have : (Matrix.of fun i j => (a • w j) i) = a • (Matrix.of fun i j => w j i) := by
      ext i j; simp
    rw [this, Matrix.det_smul, Fintype.card_fin]
  ext d
  constructor
  · rintro ⟨v, hv, rfl⟩
    choose w hw hw' using fun i => (h (v i)).1 (hv i)
    refine ⟨_, ⟨w, hw, rfl⟩, ?_⟩
    have : v = fun j => a • w j := funext hw'
    subst this
    exact (key w).symm
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨fun j => a • w j, fun i => (h _).2 ⟨w i, hw i, rfl⟩, (key w).symm⟩

/- English proof (translation)
Establish `h1 : ∀ τ, idealAt c Λ.Ln τ = Submodule.span (𝓞 c.F) {embF c τ (a ^ n)} * idealAt c Λ.La τ`. Introduce `τ`. Unfold `idealAt`. Rewrite using `[detSet_scale Λ.La Λ.Ln a h, Submodule.span_mul_span, Set.singleton_mul, Set.image_image, Set.image_image]`. Simplify using `only [map_mul]`.

Unfold `BetaIs`. Simplify using `only [h1, mul_pow, Finset.prod_mul_distrib, Submodule.span_pow, Set.singleton_pow]`. Rewrite using `[Submodule.prod_span_singleton]`.
-/
theorem betaIs_principal {n : ℕ} (Λ : GenLat E n) (a : E) (h : ∀ v, v ∈ Λ.Ln ↔ ∃ w ∈ Λ.La, v = a • w) :
    BetaIs (Dw := Dw) c Λ (∏ τ : E →+* ℂ, embF c τ (a ^ n) ^ Dw.mult τ) := by
  have h1 : ∀ τ, idealAt c Λ.Ln τ = Submodule.span (𝓞 c.F) {embF c τ (a ^ n)} * idealAt c Λ.La τ := by
    intro τ
    unfold idealAt
    rw [detSet_scale Λ.La Λ.Ln a h, Submodule.span_mul_span, Set.singleton_mul, Set.image_image, Set.image_image]
    simp only [map_mul]
  unfold BetaIs
  simp only [h1, mul_pow, Finset.prod_mul_distrib, Submodule.span_pow, Set.singleton_pow]
  rw [Submodule.prod_span_singleton]

/- English proof (translation)
Establish `hd : ∀ τ, idealAt c (⊥ : Submodule (𝓞 E) (Fin n → E)) τ = 0`. Introduce `τ`. Unfold `idealAt`. Rewrite using `[Submodule.zero_eq_bot, Submodule.span_eq_bot]`. Introduce and unpack `_ ⟨_, ⟨v, hv, rfl⟩, rfl⟩`.

Establish `: (Matrix.of fun i j => v j i) = 0`. Use extensionality with `i j`. Simplify using `[(Submodule.mem_bot _).1 (hv j)]`. Establish `hne : Nonempty (Fin n)` using `⟨⟨0, hn⟩⟩`. Rewrite using `[this, Matrix.det_zero, map_zero]`.

Establish `hL : (⟨⊥⟩ : GenLat E n).Ln = ⊥` using `bot_inf_eq _`. Unfold `BetaIs`. Rewrite using `[hL]`. Establish `hz : ∏ τ : E →+* ℂ, idealAt c (⊥ : Submodule (𝓞 E) (Fin n → E)) τ ^ Dw.mult τ = 0` using `Finset.prod_eq_zero (Finset.mem_univ τ₀) (by rw [hd, zero_pow h0])`. Rewrite using `[hz, mul_zero]`.
-/
theorem betaIs_bot {n : ℕ} (hn : 0 < n) (τ₀ : E →+* ℂ) (h0 : Dw.mult τ₀ ≠ 0) (β : c.F) :
    BetaIs (Dw := Dw) c (⟨⊥⟩ : GenLat E n) β := by
  have hd : ∀ τ, idealAt c (⊥ : Submodule (𝓞 E) (Fin n → E)) τ = 0 := by
    intro τ
    unfold idealAt
    rw [Submodule.zero_eq_bot, Submodule.span_eq_bot]
    rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    have : (Matrix.of fun i j => v j i) = 0 := by
      ext i j; simp [(Submodule.mem_bot _).1 (hv j)]
    have hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    rw [this, Matrix.det_zero, map_zero]
  have hL : (⟨⊥⟩ : GenLat E n).Ln = ⊥ := bot_inf_eq _
  unfold BetaIs
  rw [hL]
  have hz : ∏ τ : E →+* ℂ, idealAt c (⊥ : Submodule (𝓞 E) (Fin n → E)) τ ^ Dw.mult τ = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ τ₀) (by rw [hd, zero_pow h0])
  rw [hz, mul_zero]

/- English proof (translation)
Introduce `h`. Use `(h (fun _ => 1)).2 (by` as an intermediate fact. Introduce `w hw`. Rewrite using `[(Submodule.mem_bot _).1 hw]`. Use the proof step `simp)`.

Establish `h1` using `congrFun ((Submodule.mem_bot _).1 this) ⟨0, hn⟩`. Simplify using `at h1`.
-/
theorem not_unimod_bot {n : ℕ} (hn : 0 < n) : ¬ (⟨⊥⟩ : GenLat E n).Unimod := by
  intro h
  have := (h (fun _ => 1)).2 (by
    intro w hw
    rw [(Submodule.mem_bot _).1 hw]
    simp)
  have h1 := congrFun ((Submodule.mem_bot _).1 this) ⟨0, hn⟩
  simp at h1

end GlobalTheory.BetaCounterexample
