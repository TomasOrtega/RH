import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.MatchSmulAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.StrictNear
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.CosetSum
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.StrictNormal
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.BallSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubiniHolds

open MeasureTheory ValuativeRel Matrix
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc
open GlobalTheory.SmGL hiding iwahori
open UpperTheory.Gal.InertialTypesAlt.L

section

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

/- English proof (translation)
Establish `hc : Continuous (σ : E → E)`. Rewrite using `[continuous_iff_continuousAt]`. Introduce `x`. Rewrite using `[ContinuousAt, (IsValuativeTopology.hasBasis_nhds x).tendsto_iff (IsValuativeTopology.hasBasis_nhds (σ x))]`. Introduce `γ _`.

Use `⟨γ, trivial, fun z hz => ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq] at hz ⊢`. Rewrite using `[← map_sub, hσ]`. Conclude with `hz`. Conclude with `Continuous.units_map _ (continuous_id.matrix_map hc)`.
-/
private theorem sg_cont {σ : E ≃+* E} (hσ : Isom σ) : Continuous (sg σ : GL (Fin n) E → GL (Fin n) E) := by
  have hc : Continuous (σ : E → E) := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt, (IsValuativeTopology.hasBasis_nhds x).tendsto_iff
      (IsValuativeTopology.hasBasis_nhds (σ x))]
    intro γ _
    refine ⟨γ, trivial, fun z hz => ?_⟩
    simp only [Set.mem_setOf_eq] at hz ⊢
    rw [← map_sub, hσ]
    exact hz
  exact Continuous.units_map _ (continuous_id.matrix_map hc)

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.GeneralLinearGroup.map_apply, val_diagT, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem map_diag {F : Type} [Field F] (f : E →+* F) (u : Fin n → Eˣ) :
    Matrix.GeneralLinearGroup.map f (diagT E (Fin n) u) = diagT F (Fin n) fun i => Units.map (f : E →* F) (u i) := by
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply, val_diagT, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.diagonal_apply]
  split_ifs <;> simp

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
/- English proof (translation)
Rewrite using `[← map_mul, ← map_mul, mul_comm]`.
-/
private theorem diag_comm (u v : Fin n → Eˣ) :
    diagT E (Fin n) u * diagT E (Fin n) v = diagT E (Fin n) v * diagT E (Fin n) u := by
  rw [← map_mul, ← map_mul, mul_comm]

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `h1` using `congrArg (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E) i i) h`. Simplify using `only [val_diagT, Matrix.diagonal_apply_eq] at h1`. Conclude with `Units.ext h1`.
-/
private theorem diag_inj {u v : Fin n → Eˣ} (h : diagT E (Fin n) u = diagT E (Fin n) v) : u = v := by
  funext i
  have h1 := congrArg (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E) i i) h
  simp only [val_diagT, Matrix.diagonal_apply_eq] at h1
  exact Units.ext h1

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
/- English proof (translation)
Conclude with `map_diag (σ : E →+* E) p`.
-/
private theorem sg_diag (σ : E ≃+* E) (p : Fin n → Eˣ) :
    sg σ (diagT E (Fin n) p) = diagT E (Fin n) (sgT σ p) := by
  exact map_diag (σ : E →+* E) p

/- English proof (translation)
Establish `hc2 : δ * sg σ c = c * δ`. Combine the equalities or inequalities in the displayed calculation. Establish `key : (y⁻¹ * c * y)⁻¹ * diagT E (Fin n) d * sg σ (y⁻¹ * c * y) = diagT E (Fin n) d`. Rewrite using `[← hy]`. Simplify using `only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left]`.

Rewrite using `[← mul_assoc δ, hc2]`. Simplify using `only [mul_assoc, inv_mul_cancel_left]`. Conclude with `strictNormal E n σ q hσ d d hd hd _ key`.
-/
private theorem cent_diag {σ : E ≃+* E} {q : ℕ} (hσ : Cyc σ q) {d : Fin n → Eˣ} (hd : Strict d) {δ y c : GL (Fin n) E}
    (hy : y⁻¹ * δ * sg σ y = diagT E (Fin n) d) (hc : c⁻¹ * δ * sg σ c = δ) : ∃ u, y⁻¹ * c * y = diagT E (Fin n) u := by
  have hc2 : δ * sg σ c = c * δ := by
    calc δ * sg σ c = c * (c⁻¹ * δ * sg σ c) := by group
      _ = c * δ := by rw [hc]
  have key : (y⁻¹ * c * y)⁻¹ * diagT E (Fin n) d * sg σ (y⁻¹ * c * y) = diagT E (Fin n) d := by
    rw [← hy]
    simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left]
    rw [← mul_assoc δ, hc2]
    simp only [mul_assoc, inv_mul_cancel_left]
  exact strictNormal E n σ q hσ d d hd hd _ key

/- English proof (translation)
Introduce `i j`. Rewrite using `[val_diagT]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `using h i`.

Simplify using `[Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij]`.
-/
private theorem diag_ball {r : ValueGroupWithZero E} {s : Fin n → Eˣ} (h : Near r s) : diagT E (Fin n) s ∈ ball n r := by
  intro i j
  rw [val_diagT]
  by_cases hij : i = j
  · subst hij
    simpa using h i
  · simp [Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij]

/- English proof (translation)
Introduce `i`. Establish `h1` using `h i i`. Simplify `h1` using `[val_diagT, Matrix.diagonal_apply_eq]`.
-/
private theorem near_of_ball {r : ValueGroupWithZero E} {s : Fin n → Eˣ} (h : diagT E (Fin n) s ∈ ball n r) : Near r s := by
  intro i
  have h1 := h i i
  simpa [val_diagT, Matrix.diagonal_apply_eq] using h1

end

/- English proof (translation)
Introduce `E _ _ _ _ n σ q hσ r hr0 hr1 _ _ μ hμ A hA δ y d hd hy H hH ν hν R hR hRd`. Take `⟨K, hK, hKo, hKc⟩` from `ballSub E n r hr0 hr1`. Establish `hsupp` using `(suppE E n σ q hσ r hr0 hr1 A hA).2 δ y d hd hy`. Establish `hδ : δ = y * diagT E (Fin n) d * (sg σ y)⁻¹`. Rewrite using `[← hy]`.

Use `group`. Establish `hfix : ∀ w, (y * diagT E (Fin n) w * y⁻¹)⁻¹ * δ * sg σ (y * diagT E (Fin n) w * y⁻¹) = δ ↔ sgT σ w = w`. Introduce `w`. Establish `e : (y * diagT E (Fin n) w * y⁻¹)⁻¹ * δ * sg σ (y * diagT E (Fin n) w * y⁻¹) = y * ((diagT E (Fin n) w)⁻¹ * diagT E (Fin n) d * diagT E (Fin n) (sgT σ w)) * (sg σ y)⁻¹`. Rewrite using `[hδ, map_mul, map_mul, map_inv, sg_diag]`.

Use `group`. Rewrite using `[e]`. Prove the components needed by the constructor for the conclusion. Introduce `h conv_rhs at h => rw [hδ]`. Establish `h2 : (diagT E (Fin n) w)⁻¹ * diagT E (Fin n) d * diagT E (Fin n) (sgT σ w) = diagT E (Fin n) d` using `mul_left_cancel (mul_right_cancel h)`.

Establish `h3 : diagT E (Fin n) d * diagT E (Fin n) (sgT σ w) = diagT E (Fin n) d * diagT E (Fin n) w`. Combine the equalities or inequalities in the displayed calculation. Conclude with `diag_inj (mul_left_cancel h3)`. Introduce `h`. Rewrite using `[h, hδ, mul_assoc (diagT E (Fin n) w)⁻¹, diag_comm d w]`.

Use `group`. Establish `hcen : ∀ c ∈ H, ∃ u, y⁻¹ * c * y = diagT E (Fin n) u` using `fun c hc => cent_diag hσ hd hy ((hH c).1 hc)`. Establish `hback : ∀ c u, y⁻¹ * c * y = diagT E (Fin n) u → c = y * diagT E (Fin n) u * y⁻¹`. Introduce `c u hu`. Rewrite using `[← hu]`.

Use `group`. Establish `hfixH : ∀ c ∈ H, ∀ u, y⁻¹ * c * y = diagT E (Fin n) u → sgT σ u = u`. Introduce `c hc u hu`. Apply `(hfix u).1` to reduce the goal to its premises. Rewrite using `[← hback c u hu]`.

Conclude with `(hH c).1 hc`. Establish `hclosed : IsClosed (H : Set (GL (Fin n) E))`. Establish `hset : (H : Set (GL (Fin n) E)) = {c | c⁻¹ * δ * sg σ c = δ}` using `Set.ext hH`. Rewrite using `[hset]`. Conclude with `isClosed_eq ((continuous_inv.mul continuous_const).mul (sg_cont hσ.isom)) continuous_const`.

Establish `hcomm : ∀ a ∈ H, ∀ b ∈ H, Commute a b`. Introduce `a ha b hb`. Take `⟨u, hu⟩` from `hcen a ha`. Take `⟨v, hv⟩` from `hcen b hb`. Rewrite using `[hback a u hu, hback b v hv]`.

Use `show y * diagT E (Fin n) u * y⁻¹ * (y * diagT E (Fin n) v * y⁻¹) = y * diagT E (Fin n) v * y⁻¹ * (y * diagT E (Fin n) u * y⁻¹)`. Combine the equalities or inequalities in the displayed calculation. Establish `hV : ∀ ρ ∈ R, ∀ h : H, h ∈ {h : H | y⁻¹ * ↑h * y ∈ ball n r} ↔ (y * diagT E (Fin n) ρ)⁻¹ * ↑h * (y * diagT E (Fin n) ρ) ∈ K`. Introduce `ρ _ h`. Take `⟨u, hu⟩` from `hcen h h.2`.

Establish `e : (y * diagT E (Fin n) ρ)⁻¹ * ↑h * (y * diagT E (Fin n) ρ) = y⁻¹ * ↑h * y`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hu, mul_assoc, diag_comm u ρ, inv_mul_cancel_left]`. Rewrite using `[Set.mem_setOf_eq, e, ← SetLike.mem_coe, hK]`. Establish `hS : ∀ g, g ∈ {g : GL (Fin n) E | g⁻¹ * δ * sg σ g ∈ elemSet r A} ↔ ∃ ρ ∈ R, ∃ h ∈ H, ∃ κ ∈ K, g = h * (y * diagT E (Fin n) ρ) * κ`.

Introduce `g`. Rewrite using `[Set.mem_setOf_eq, hsupp g]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, κ, hκ, rfl⟩`. Take `⟨ρ, hρR, p, s, hp, hs, rfl⟩` from `(hR u).1 hu`.

Use `⟨ρ, hρR, y * diagT E (Fin n) p * y⁻¹, (hH _).2 ((hfix p).2 hp), diagT E (Fin n) s * κ, ?_, ?_⟩` and prove the remaining obligations. Use `K.mul_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[← SetLike.mem_coe, hK]`. Conclude with `diag_ball hs`. Rewrite using `[← SetLike.mem_coe, hK]`.

Conclude with `hκ`. Rewrite using `[map_mul, map_mul, diag_comm ρ p] group`. Introduce and unpack `⟨ρ, hρR, h, hh, κ, hκ, rfl⟩`. Take `⟨w, hw⟩` from `hcen h hh`. Establish `hw'` using `hfixH h hh w hw`.

Use `⟨w * ρ, (hR _).2 ⟨ρ, hρR, w, 1, hw', fun i => by simp, by rw [mul_one, mul_comm]⟩, κ, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hK]`. Conclude with `hκ`. Rewrite using `[map_mul, hback h w hw] group`. Establish `hD : ∀ i ∈ R, ∀ j ∈ R, (∃ h ∈ H, ∃ κ ∈ K, y * diagT E (Fin n) i = h * (y * diagT E (Fin n) j) * κ) → i = j`.

Introduce and unpack `i hi j hj ⟨h, hh, κ, hκ, he⟩`. Take `⟨w, hw⟩` from `hcen h hh`. Establish `hw'` using `hfixH h hh w hw`. Establish `hk : κ = diagT E (Fin n) (w⁻¹ * j⁻¹ * i)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[he]`. Use `group`. Use `_ = diagT E (Fin n) (w⁻¹ * j⁻¹ * i) := by`. Rewrite using `[hback h w hw, mul_comm w⁻¹ j⁻¹]`. Simplify using `only [map_mul, map_inv]`.

Use `group`. Use `hRd i hi j hj ⟨w, w⁻¹ * j⁻¹ * i, hw', near_of_ball ?_, by group⟩` and prove the remaining obligations. Rewrite using `[← hk, ← hK]`. Conclude with `hκ`. Establish `key` using `cosetSum (GL (Fin n) E) μ hμ K H hKo hKc hclosed hcomm ν hν (Fin n → Eˣ) R (fun ρ => y * diagT E (Fin n) ρ) {h : H | y⁻¹ * ↑h * y ∈ ball n r} {g : GL (Fin n) E | g⁻¹ * δ * sg σ g ∈ elemSet r A} hV hS hD`.

Rewrite `key` using `[hK]`. Conclude with `key`.
-/
theorem UpperTheory.Gal.InertialTypesAlt.L.oneField :
    UpperTheory.Gal.InertialTypesAlt.L.OneField := by
  intro E _ _ _ _ n σ q hσ r hr0 hr1 _ _ μ hμ A hA δ y d hd hy H hH ν hν R hR hRd
  obtain ⟨K, hK, hKo, hKc⟩ := ballSub E n r hr0 hr1
  have hsupp := (suppE E n σ q hσ r hr0 hr1 A hA).2 δ y d hd hy
  have hδ : δ = y * diagT E (Fin n) d * (sg σ y)⁻¹ := by
    rw [← hy]
    group
  have hfix : ∀ w, (y * diagT E (Fin n) w * y⁻¹)⁻¹ * δ * sg σ (y * diagT E (Fin n) w * y⁻¹) = δ ↔
      sgT σ w = w := by
    intro w
    have e : (y * diagT E (Fin n) w * y⁻¹)⁻¹ * δ * sg σ (y * diagT E (Fin n) w * y⁻¹) =
        y * ((diagT E (Fin n) w)⁻¹ * diagT E (Fin n) d * diagT E (Fin n) (sgT σ w)) * (sg σ y)⁻¹ := by
      rw [hδ, map_mul, map_mul, map_inv, sg_diag]
      group
    rw [e]
    constructor
    · intro h
      conv_rhs at h => rw [hδ]
      have h2 : (diagT E (Fin n) w)⁻¹ * diagT E (Fin n) d * diagT E (Fin n) (sgT σ w) = diagT E (Fin n) d :=
        mul_left_cancel (mul_right_cancel h)
      have h3 : diagT E (Fin n) d * diagT E (Fin n) (sgT σ w) = diagT E (Fin n) d * diagT E (Fin n) w := by
        calc diagT E (Fin n) d * diagT E (Fin n) (sgT σ w)
            = diagT E (Fin n) w * ((diagT E (Fin n) w)⁻¹ * diagT E (Fin n) d * diagT E (Fin n) (sgT σ w)) := by
              group
          _ = diagT E (Fin n) w * diagT E (Fin n) d := by rw [h2]
          _ = diagT E (Fin n) d * diagT E (Fin n) w := diag_comm w d
      exact diag_inj (mul_left_cancel h3)
    · intro h
      rw [h, hδ, mul_assoc (diagT E (Fin n) w)⁻¹, diag_comm d w]
      group
  have hcen : ∀ c ∈ H, ∃ u, y⁻¹ * c * y = diagT E (Fin n) u :=
    fun c hc => cent_diag hσ hd hy ((hH c).1 hc)
  have hback : ∀ c u, y⁻¹ * c * y = diagT E (Fin n) u → c = y * diagT E (Fin n) u * y⁻¹ := by
    intro c u hu
    rw [← hu]
    group
  have hfixH : ∀ c ∈ H, ∀ u, y⁻¹ * c * y = diagT E (Fin n) u → sgT σ u = u := by
    intro c hc u hu
    apply (hfix u).1
    rw [← hback c u hu]
    exact (hH c).1 hc
  have hclosed : IsClosed (H : Set (GL (Fin n) E)) := by
    have hset : (H : Set (GL (Fin n) E)) = {c | c⁻¹ * δ * sg σ c = δ} := Set.ext hH
    rw [hset]
    exact isClosed_eq ((continuous_inv.mul continuous_const).mul (sg_cont hσ.isom)) continuous_const
  have hcomm : ∀ a ∈ H, ∀ b ∈ H, Commute a b := by
    intro a ha b hb
    obtain ⟨u, hu⟩ := hcen a ha
    obtain ⟨v, hv⟩ := hcen b hb
    rw [hback a u hu, hback b v hv]
    show y * diagT E (Fin n) u * y⁻¹ * (y * diagT E (Fin n) v * y⁻¹) =
      y * diagT E (Fin n) v * y⁻¹ * (y * diagT E (Fin n) u * y⁻¹)
    calc y * diagT E (Fin n) u * y⁻¹ * (y * diagT E (Fin n) v * y⁻¹)
        = y * (diagT E (Fin n) u * diagT E (Fin n) v) * y⁻¹ := by group
      _ = y * (diagT E (Fin n) v * diagT E (Fin n) u) * y⁻¹ := by rw [diag_comm u v]
      _ = y * diagT E (Fin n) v * y⁻¹ * (y * diagT E (Fin n) u * y⁻¹) := by group
  have hV : ∀ ρ ∈ R, ∀ h : H, h ∈ {h : H | y⁻¹ * ↑h * y ∈ ball n r} ↔
      (y * diagT E (Fin n) ρ)⁻¹ * ↑h * (y * diagT E (Fin n) ρ) ∈ K := by
    intro ρ _ h
    obtain ⟨u, hu⟩ := hcen h h.2
    have e : (y * diagT E (Fin n) ρ)⁻¹ * ↑h * (y * diagT E (Fin n) ρ) = y⁻¹ * ↑h * y := by
      calc (y * diagT E (Fin n) ρ)⁻¹ * ↑h * (y * diagT E (Fin n) ρ)
          = (diagT E (Fin n) ρ)⁻¹ * (y⁻¹ * ↑h * y) * diagT E (Fin n) ρ := by group
        _ = y⁻¹ * ↑h * y := by
          rw [hu, mul_assoc, diag_comm u ρ, inv_mul_cancel_left]
    rw [Set.mem_setOf_eq, e, ← SetLike.mem_coe, hK]
  have hS : ∀ g, g ∈ {g : GL (Fin n) E | g⁻¹ * δ * sg σ g ∈ elemSet r A} ↔
      ∃ ρ ∈ R, ∃ h ∈ H, ∃ κ ∈ K, g = h * (y * diagT E (Fin n) ρ) * κ := by
    intro g
    rw [Set.mem_setOf_eq, hsupp g]
    constructor
    · rintro ⟨u, hu, κ, hκ, rfl⟩
      obtain ⟨ρ, hρR, p, s, hp, hs, rfl⟩ := (hR u).1 hu
      refine ⟨ρ, hρR, y * diagT E (Fin n) p * y⁻¹, (hH _).2 ((hfix p).2 hp), diagT E (Fin n) s * κ, ?_, ?_⟩
      · refine K.mul_mem ?_ ?_
        · rw [← SetLike.mem_coe, hK]
          exact diag_ball hs
        · rw [← SetLike.mem_coe, hK]
          exact hκ
      · rw [map_mul, map_mul, diag_comm ρ p]
        group
    · rintro ⟨ρ, hρR, h, hh, κ, hκ, rfl⟩
      obtain ⟨w, hw⟩ := hcen h hh
      have hw' := hfixH h hh w hw
      refine ⟨w * ρ, (hR _).2 ⟨ρ, hρR, w, 1, hw', fun i => by simp, by rw [mul_one, mul_comm]⟩, κ, ?_, ?_⟩
      · rw [← hK]
        exact hκ
      · rw [map_mul, hback h w hw]
        group
  have hD : ∀ i ∈ R, ∀ j ∈ R, (∃ h ∈ H, ∃ κ ∈ K, y * diagT E (Fin n) i = h * (y * diagT E (Fin n) j) * κ) →
      i = j := by
    rintro i hi j hj ⟨h, hh, κ, hκ, he⟩
    obtain ⟨w, hw⟩ := hcen h hh
    have hw' := hfixH h hh w hw
    have hk : κ = diagT E (Fin n) (w⁻¹ * j⁻¹ * i) := by
      calc κ = (h * (y * diagT E (Fin n) j))⁻¹ * (y * diagT E (Fin n) i) := by
            rw [he]
            group
        _ = diagT E (Fin n) (w⁻¹ * j⁻¹ * i) := by
          rw [hback h w hw, mul_comm w⁻¹ j⁻¹]
          simp only [map_mul, map_inv]
          group
    refine hRd i hi j hj ⟨w, w⁻¹ * j⁻¹ * i, hw', near_of_ball ?_, by group⟩
    rw [← hk, ← hK]
    exact hκ
  have key := cosetSum (GL (Fin n) E) μ hμ K H hKo hKc hclosed hcomm ν hν (Fin n → Eˣ) R
    (fun ρ => y * diagT E (Fin n) ρ) {h : H | y⁻¹ * ↑h * y ∈ ball n r}
    {g : GL (Fin n) E | g⁻¹ * δ * sg σ g ∈ elemSet r A} hV hS hD
  rw [hK] at key
  exact key
