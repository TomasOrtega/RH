import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.MatchSmulAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.ContractB
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.StrictNormal
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.BallSub

noncomputable section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc
open GlobalTheory.SmGL hiding iwahori
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

section

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[sg, GeneralLinearGroup.map_apply, val_diagT, val_diagT]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[sgT]`.

Simplify using `[Matrix.diagonal_apply_ne _ h]`.
-/
private theorem sg_diag (σ : E ≃+* E) (u : Fin n → Eˣ) :
    sg σ (diagT E (Fin n) u) = diagT E (Fin n) (sgT σ u) := by
  ext i j
  rw [sg, GeneralLinearGroup.map_apply, val_diagT, val_diagT]
  by_cases h : i = j
  · subst h
    simp [sgT]
  · simp [Matrix.diagonal_apply_ne _ h]

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
/- English proof (translation)
Introduce `a b h`. Use function extensionality and compare the values at `i`. Apply `Units.ext` to reduce the goal to its premises. Use `congrArg (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E) i i) h` as an intermediate fact. Simplify `this` using `[val_diagT]`.
-/
private theorem diag_inj : Function.Injective (diagT E (Fin n)) := by
  intro a b h
  funext i
  apply Units.ext
  have := congrArg (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E) i i) h
  simpa [val_diagT] using this

/- English proof (translation)
Establish `h1 : valuation E ((s i : E) - 1) < valuation E (1 : E)`. Rewrite using `[map_one]`. Conclude with `lt_of_le_of_lt (hs i) hr`. Establish `h2` using `Valuation.map_add_eq_of_lt_right (valuation E) h1`. Simplify using `using h2`.
-/
private theorem near_val {r : ValueGroupWithZero E} (hr : r < 1) {s : Fin n → Eˣ} (hs : Near r s) (i : Fin n) :
    valuation E (s i : E) = 1 := by
  have h1 : valuation E ((s i : E) - 1) < valuation E (1 : E) := by
    rw [map_one]
    exact lt_of_le_of_lt (hs i) hr
  have h2 := Valuation.map_add_eq_of_lt_right (valuation E) h1
  simpa using h2

/- English proof (translation)
Establish `key : ∀ k, valuation E ((t * s) k : E) = valuation E (t k : E)`. Introduce `k`. Rewrite using `[Pi.mul_apply, Units.val_mul, map_mul, near_val hr hs k, mul_one]`. Introduce `i j hij`. Rewrite using `[key, key]`.

Conclude with `ht i j hij`.
-/
private theorem strict_near {r : ValueGroupWithZero E} (hr : r < 1) {t s : Fin n → Eˣ} (ht : Strict t)
    (hs : Near r s) : Strict (t * s) := by
  have key : ∀ k, valuation E ((t * s) k : E) = valuation E (t k : E) := by
    intro k
    rw [Pi.mul_apply, Units.val_mul, map_mul, near_val hr hs k, mul_one]
  intro i j hij
  rw [key, key]
  exact ht i j hij

/- English proof (translation)
Simplify using `only [ball, Set.mem_setOf_eq] at ha ⊢`. Introduce `i j`. Establish `h : ((sg σ a : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j = σ ((a : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j)`. Rewrite using `[sg, GeneralLinearGroup.map_apply, map_sub]`. Use `congr 1`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne hij]`. Rewrite using `[h, hσ]`.

Conclude with `ha i j`.
-/
private theorem ball_sg {r : ValueGroupWithZero E} {σ : E ≃+* E} (hσ : Isom σ) {a : GL (Fin n) E}
    (ha : a ∈ ball n r) : sg σ a ∈ ball n r := by
  simp only [ball, Set.mem_setOf_eq] at ha ⊢
  intro i j
  have h : ((sg σ a : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j
      = σ ((a : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) := by
    rw [sg, GeneralLinearGroup.map_apply, map_sub]
    congr 1
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.one_apply_ne hij]
  rw [h, hσ]
  exact ha i j

/- English proof (translation)
Introduce `i j`. Rewrite using `[val_diagT]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `using hs i`.

Simplify using `[Matrix.diagonal_apply_ne _ h, one_apply_ne h]`.
-/
private theorem diag_ball {r : ValueGroupWithZero E} {s : Fin n → Eˣ} (hs : Near r s) :
    diagT E (Fin n) s ∈ ball n r := by
  intro i j
  rw [val_diagT]
  by_cases h : i = j
  · subst h
    simpa using hs i
  · simp [Matrix.diagonal_apply_ne _ h, one_apply_ne h]

end

end UpperTheory.Gal.InertialTypesAlt.L

/- English proof (translation)
Introduce `E _ _ _ _ n σ q hc r hr0 hr1 A hA`. Establish `hσ : Isom σ` using `hc.isom`. Take `⟨K, hK, -, -⟩` from `ballSub E n r hr0 hr1`. Establish `bmul : ∀ a ∈ ball n r, ∀ b ∈ ball n r, a * b ∈ ball n r`. Introduce `a ha b hb`.

Rewrite `ha`, `hb`, the goal using `[← hK]`. Conclude with `K.mul_mem ha hb`. Establish `binv : ∀ a ∈ ball n r, a⁻¹ ∈ ball n r`. Introduce `a ha`. Rewrite `ha`, the goal using `[← hK]`.

Conclude with `K.inv_mem ha`. Establish `step : ∀ δ g : GL (Fin n) E, g⁻¹ * δ * sg σ g ∈ UpperTheory.Gal.InertialTypesAlt.L.elemSet r A → ∃ k ∈ ball n r, ∃ t ∈ A, ∃ s, UpperTheory.Gal.InertialTypesAlt.L.Near r s ∧ g⁻¹ * δ * sg σ g = k⁻¹ * diagT E (Fin n) (t * s) * sg σ k`. Introduce `δ g hg`. Take `⟨a, ha, b, hb, t, ht, he⟩` from `hg`. Take `⟨k, hk, s, hs, hks⟩` from `contractB E n σ hσ t (hA t ht) r hr1 a ha b hb`.

Conclude with `⟨k, hk, t, ht, s, hs, he.trans hks⟩`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `δ g hg`. Take `⟨k, hk, t, ht, s, hs, he⟩` from `step δ g hg`. Use `⟨g * k⁻¹, t, ht, s, hs, UpperTheory.Gal.InertialTypesAlt.L.strict_near hr1 (hA t ht) hs, ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_mul, map_inv]`. Use `group`. Use `_ = diagT E (Fin n) (t * s) := by`. Rewrite using `[he]`.

Use `group`. Introduce `δ y d hd hy g`. Prove the components needed by the constructor for the conclusion. Introduce `hg`. Take `⟨k, hk, t, ht, s, hs, he⟩` from `step δ g hg`.

Establish `hts : Strict (t * s)` using `UpperTheory.Gal.InertialTypesAlt.L.strict_near hr1 (hA t ht) hs`. Establish `hx : (y⁻¹ * g * k⁻¹)⁻¹ * diagT E (Fin n) d * sg σ (y⁻¹ * g * k⁻¹) = diagT E (Fin n) (t * s)`. Rewrite using `[← hy]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_mul, map_mul, map_inv, map_inv]`.

Use `group`. Use `_ = diagT E (Fin n) (t * s) := by`. Rewrite using `[he]`. Use `group`. Take `⟨u, hu⟩` from `strictNormal E n σ q hc d (t * s) hd hts _ hx`.

Establish `h2 : u⁻¹ * d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u = t * s`. Apply `UpperTheory.Gal.InertialTypesAlt.L.diag_inj` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, map_inv, ← UpperTheory.Gal.InertialTypesAlt.L.sg_diag, ← hu]`. Conclude with `hx`. Use `⟨u, ⟨t, ht, ?_⟩, k, hk, ?_⟩` and prove the remaining obligations.

Establish `h3 : d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u / u / t = s`. Combine the equalities or inequalities in the displayed calculation. Simplify using `[div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]`. Use `_ = s := by`. Rewrite using `[h2]`.

Simplify using the standard rewrite rules. Rewrite using `[h3]`. Conclude with `hs`. Rewrite using `[← hu] group`. Introduce and unpack `⟨u, ⟨t, ht, hs⟩, κ, hκ, rfl⟩`.

Establish `hid : u⁻¹ * d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u = t * (d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u / u / t)`. Rewrite using `[mul_comm t, div_mul_cancel, div_eq_mul_inv, mul_comm (d * _) u⁻¹, mul_assoc]`. Establish `hδ : δ = y * diagT E (Fin n) d * (sg σ y)⁻¹`. Rewrite using `[← hy]`. Use `group`.

Use `⟨κ⁻¹, binv κ hκ, diagT E (Fin n) (d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u / u / t) * sg σ κ, bmul _ (UpperTheory.Gal.InertialTypesAlt.L.diag_ball hs) _ (UpperTheory.Gal.InertialTypesAlt.L.ball_sg hσ hκ), t, ht, ?_⟩` and prove the remaining obligations. Rewrite using `[hδ]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_mul, map_mul]`. Use `group`.

Use `_ = κ⁻¹ * (diagT E (Fin n) t * diagT E (Fin n) (d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u / u / t)) * sg σ κ := by`. Rewrite using `[UpperTheory.Gal.InertialTypesAlt.L.sg_diag, ← map_inv (diagT E (Fin n)) u, ← map_mul, ← map_mul, ← map_mul, hid]`. Use `_ = κ⁻¹ * diagT E (Fin n) t * (diagT E (Fin n) (d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u / u / t) * sg σ κ) := by group`.
-/
theorem UpperTheory.Gal.InertialTypesAlt.L.suppE :
    UpperTheory.Gal.InertialTypesAlt.L.SuppE := by
  intro E _ _ _ _ n σ q hc r hr0 hr1 A hA
  have hσ : Isom σ := hc.isom
  obtain ⟨K, hK, -, -⟩ := ballSub E n r hr0 hr1
  have bmul : ∀ a ∈ ball n r, ∀ b ∈ ball n r, a * b ∈ ball n r := by
    intro a ha b hb
    rw [← hK] at ha hb ⊢
    exact K.mul_mem ha hb
  have binv : ∀ a ∈ ball n r, a⁻¹ ∈ ball n r := by
    intro a ha
    rw [← hK] at ha ⊢
    exact K.inv_mem ha
  have step : ∀ δ g : GL (Fin n) E, g⁻¹ * δ * sg σ g ∈ UpperTheory.Gal.InertialTypesAlt.L.elemSet r A →
      ∃ k ∈ ball n r, ∃ t ∈ A, ∃ s, UpperTheory.Gal.InertialTypesAlt.L.Near r s ∧
        g⁻¹ * δ * sg σ g = k⁻¹ * diagT E (Fin n) (t * s) * sg σ k := by
    intro δ g hg
    obtain ⟨a, ha, b, hb, t, ht, he⟩ := hg
    obtain ⟨k, hk, s, hs, hks⟩ := contractB E n σ hσ t (hA t ht) r hr1 a ha b hb
    exact ⟨k, hk, t, ht, s, hs, he.trans hks⟩
  refine ⟨?_, ?_⟩
  · intro δ g hg
    obtain ⟨k, hk, t, ht, s, hs, he⟩ := step δ g hg
    refine ⟨g * k⁻¹, t, ht, s, hs, UpperTheory.Gal.InertialTypesAlt.L.strict_near hr1 (hA t ht) hs, ?_⟩
    calc (g * k⁻¹)⁻¹ * δ * sg σ (g * k⁻¹)
        = k * (g⁻¹ * δ * sg σ g) * (sg σ k)⁻¹ := by
          rw [map_mul, map_inv]
          group
      _ = diagT E (Fin n) (t * s) := by
          rw [he]
          group
  · intro δ y d hd hy g
    constructor
    · intro hg
      obtain ⟨k, hk, t, ht, s, hs, he⟩ := step δ g hg
      have hts : Strict (t * s) := UpperTheory.Gal.InertialTypesAlt.L.strict_near hr1 (hA t ht) hs
      have hx : (y⁻¹ * g * k⁻¹)⁻¹ * diagT E (Fin n) d * sg σ (y⁻¹ * g * k⁻¹)
          = diagT E (Fin n) (t * s) := by
        rw [← hy]
        calc (y⁻¹ * g * k⁻¹)⁻¹ * (y⁻¹ * δ * sg σ y) * sg σ (y⁻¹ * g * k⁻¹)
            = k * (g⁻¹ * δ * sg σ g) * (sg σ k)⁻¹ := by
              rw [map_mul, map_mul, map_inv, map_inv]
              group
          _ = diagT E (Fin n) (t * s) := by
              rw [he]
              group
      obtain ⟨u, hu⟩ := strictNormal E n σ q hc d (t * s) hd hts _ hx
      have h2 : u⁻¹ * d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u = t * s := by
        apply UpperTheory.Gal.InertialTypesAlt.L.diag_inj
        rw [map_mul, map_mul, map_inv, ← UpperTheory.Gal.InertialTypesAlt.L.sg_diag, ← hu]
        exact hx
      refine ⟨u, ⟨t, ht, ?_⟩, k, hk, ?_⟩
      · have h3 : d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u / u / t = s := by
          calc d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u / u / t = (u⁻¹ * d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u) / t := by
                simp [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]
            _ = s := by
                rw [h2]
                simp
        rw [h3]
        exact hs
      · rw [← hu]
        group
    · rintro ⟨u, ⟨t, ht, hs⟩, κ, hκ, rfl⟩
      have hid : u⁻¹ * d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u = t * (d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u / u / t) := by
        rw [mul_comm t, div_mul_cancel, div_eq_mul_inv, mul_comm (d * _) u⁻¹, mul_assoc]
      have hδ : δ = y * diagT E (Fin n) d * (sg σ y)⁻¹ := by
        rw [← hy]
        group
      refine ⟨κ⁻¹, binv κ hκ, diagT E (Fin n) (d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u / u / t) * sg σ κ,
        bmul _ (UpperTheory.Gal.InertialTypesAlt.L.diag_ball hs) _ (UpperTheory.Gal.InertialTypesAlt.L.ball_sg hσ hκ), t, ht, ?_⟩
      rw [hδ]
      calc (y * diagT E (Fin n) u * κ)⁻¹ * (y * diagT E (Fin n) d * (sg σ y)⁻¹)
            * sg σ (y * diagT E (Fin n) u * κ)
          = κ⁻¹ * ((diagT E (Fin n) u)⁻¹ * diagT E (Fin n) d * sg σ (diagT E (Fin n) u)) * sg σ κ := by
            rw [map_mul, map_mul]
            group
        _ = κ⁻¹ * (diagT E (Fin n) t * diagT E (Fin n) (d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u / u / t)) * sg σ κ := by
            rw [UpperTheory.Gal.InertialTypesAlt.L.sg_diag, ← map_inv (diagT E (Fin n)) u, ← map_mul, ← map_mul, ← map_mul, hid]
        _ = κ⁻¹ * diagT E (Fin n) t * (diagT E (Fin n) (d * UpperTheory.Gal.InertialTypesAlt.L.sgT σ u / u / t) * sg σ κ) := by
            group
