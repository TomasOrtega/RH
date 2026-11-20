import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimitbDefs
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimPhi
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.ConvEqOfIsROp

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.RgTw (Mat G)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.F.borelG PositivityTheory.Rg.BcB.F.borelF borelH

namespace PositivityTheory.Rg.BcB.F.Rd.B

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.Rd

/- English proof (translation)
Assemble the required witnesses or components as `⟨rfl⟩`.
-/
theorem bsG' (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨rfl⟩`.
-/
theorem bsF' (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) : BorelSpace (Hf E a b) := ⟨rfl⟩

attribute [local instance] bsG' bsF'

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Real

variable {B : Block E} {Γ : Type} (g : Γ → BGen B) (X : B.Hb →L[ℂ] B.Hb) (t₀ : PT B)

def phiG (x : ChAlg g X) : Matrix B.I B.I (H E B.a B.b → ℂ) :=
  if h : ∃ Φ : Matrix B.I B.I (H E B.a B.b → ℂ), IsTestM Φ ∧ IsROp B.D Φ ((x : B.Hb →L[ℂ] B.Hb) * t₀.op) then
    h.choose
  else 0

/- English proof (translation)
Use `haveI := B.ha`. Use `haveI := B.hb`. Use `haveI := B.hν`. Establish `hm` using `hTM E B.a B.b B.D B.μa B.μb B.ν B.Ma B.Mb B.κ t.ka t₀.ka t.kb t₀.kb t.va t₀.va t.vb t₀.vb t.T t₀.T t.ψ t₀.ψ B.compat ht.ka ht.kb ht₀.ka ht₀.kb ht.ψ ht₀.ψ`. Establish `hΦ : mulM B.D.μ t.Φ t₀.Φ = (t.mul t₀).Φ` using `hm.2`.

Take `⟨-, -, hok, hop, -⟩` from `hBO E B t t₀ ht ht₀`. Establish `h2` using `hBO E B (t.mul t₀) (t.mul t₀) hok hok`. Rewrite using `[hΦ, ← hop]`. Conclude with `⟨h2.1, h2.2.1⟩`.
-/
theorem mul_facts (hTM : TensMul) (hBO : BlockOperatorsProductAdjoint) (t : PT B) (ht : t.Ok) (ht₀ : t₀.Ok) :
    IsTestM (mulM B.D.μ t.Φ t₀.Φ) ∧ IsROp B.D (mulM B.D.μ t.Φ t₀.Φ) (t.op * t₀.op) := by
  haveI := B.ha; haveI := B.hb; haveI := B.hν
  have hm := hTM E B.a B.b B.D B.μa B.μb B.ν B.Ma B.Mb B.κ t.ka t₀.ka t.kb t₀.kb t.va t₀.va t.vb t₀.vb t.T t₀.T t.ψ t₀.ψ
      B.compat ht.ka ht.kb ht₀.ka ht₀.kb ht.ψ ht₀.ψ
  have hΦ : mulM B.D.μ t.Φ t₀.Φ = (t.mul t₀).Φ := hm.2
  obtain ⟨-, -, hok, hop, -⟩ := hBO E B t t₀ ht ht₀
  have h2 := hBO E B (t.mul t₀) (t.mul t₀) hok hok
  rw [hΦ, ← hop]
  exact ⟨h2.1, h2.2.1⟩

/- English proof (translation)
Use `hok y` as an intermediate fact. Rewrite `this` using `[hy]`. Conclude with `this`.
-/
theorem ok_of_inr {t : PT B} {y : Γ} (hok : ∀ x, (g x).Ok) (hy : g y = Sum.inr t) : t.Ok := by
  have := hok y
  rw [hy] at this
  exact this

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Establish `ht₀ : t₀.Ok` using `ok_of_inr g hok ha₀`. Establish `ea : ((genE g X a₀ : ChAlg g X) : B.Hb →L[ℂ] B.Hb) = t₀.op` using `by show (g a₀).op = _`. Rewrite using `[ha₀]`. Both sides reduce to the same expression. Establish `hspec : ∀ x : ChAlg g X, IsTestM (phiG g X t₀ x) ∧ IsROp B.D (phiG g X t₀ x) ((x : B.Hb →L[ℂ] B.Hb) * t₀.op)` using `fun x => by`.

Establish `h` using `phiEx hBO hBW hBS hAW g X tX t₀ hok htX hXe ht₀ x`. Unfold `phiG`. Rewrite using `[dif_pos h]`. Conclude with `h.choose_spec`. Use `letI : CommRing (ChAlg g X) := chComm g X hc hXc hXs`.

Establish `hCc : ({1} ∪ Set.range (genE g X) ∪ {XE g X} : Set (ChAlg g X)).Countable` using `((Set.countable_singleton _).union (Set.countable_range _)).union (Set.countable_singleton _)`. Take `⟨M, s, f, hlim, hk⟩` from `hE2 E B.a B.b B.D B.I B.Hb (ContinuousLinearMap.id ℂ B.Hb) (fun v => rfl) (ChAlg g X) (StarSubalgebra.subtype _) χ (genE g X a₀) ({1} ∪ Set.range (genE g X) ∪ {XE g X}) (phiG g X t₀) hχ hχ0 hCc (Or.inl (Or.inl rfl)) (fun x => (hspec x).1) (fun x => ⟨_, (hspec x).2, fun v => by`. Express the relevant statement in the definitionally equal form `((x : B.Hb →L[ℂ] B.Hb) * t₀.op) v = ((x : B.Hb →L[ℂ] B.Hb) * ((genE g X a₀ : ChAlg g X) : B.Hb →L[ℂ] B.Hb)) v`. Rewrite using `[ea], fun u hu => by`. Establish `hu0 : u = 0` using `inner_self_eq_zero.1 (hu u)`.

Rewrite using `[hu0, map_zero]⟩)`. Use `⟨M, fun k x => s k x, f, fun y => hlim _ (Or.inl (Or.inr ⟨y, rfl⟩)), hlim _ (Or.inr rfl), fun k => ?_⟩` and prove the remaining obligations. Take `⟨h0, hcont, hne, hL, hW, hconv⟩` from `hk k`. Establish `key : ∀ x ∈ ({1} ∪ Set.range (genE g X) ∪ {XE g X} : Set (ChAlg g X)), ∀ Ψ, IsTestM Ψ → IsROp B.D Ψ ((x : B.Hb →L[ℂ] B.Hb) * t₀.op) → PositivityTheory.Rg.BcB.E.conv B.D.μ Ψ (f k) = s k (x * genE g X a₀) • f k` using `fun x hx Ψ h1 h2 => (PositivityTheory.Rg.BcB.E2.conv_eq_of_isROp B.D h1 (hspec x).1 h2 (hspec x).2 hcont hL).trans (hconv x hx)`. Use `⟨h0, hcont, hne, hL, hW, ?_, fun y t hy => ?_, ?_⟩` and prove the remaining obligations.

Establish `h0'` using `hBO E B t₀ t₀ ht₀ ht₀`. Establish `h` using `key 1 (Or.inl (Or.inl rfl)) t₀.Φ h0'.1 (by show IsROp B.D t₀.Φ (1 * t₀.op)`. Rewrite using `[one_mul]`. Conclude with `h0'.2.1)`. Rewrite `h` using `[one_mul]`.

Conclude with `h`. Establish `ht` using `ok_of_inr g hok hy`. Establish `hm` using `mul_facts t₀ hTM hBO t ht ht₀`. Establish `e : ((genE g X y : ChAlg g X) : B.Hb →L[ℂ] B.Hb) = t.op` using `by show (g y).op = _`. Rewrite using `[hy]`.

Both sides reduce to the same expression. Establish `h` using `key (genE g X y) (Or.inl (Or.inr ⟨y, rfl⟩)) _ hm.1 (by rw [e]; exact hm.2)`. Rewrite `h` using `[map_mul]`. Conclude with `h`. Establish `hm` using `mul_facts t₀ hTM hBO tX htX ht₀`.

Establish `e : ((XE g X : ChAlg g X) : B.Hb →L[ℂ] B.Hb) = tX.op` using `hXe`. Establish `h` using `key (XE g X) (Or.inr rfl) _ hm.1 (by rw [e]; exact hm.2)`. Rewrite `h` using `[map_mul]`. Conclude with `h`.
-/
theorem realise_commuting_family (hE2 : E2) (hTM : TensMul) (hBO : BlockOperatorsProductAdjoint) (hBW : BlockWordOperators) (hBS : BlockLinearCombinations) (hAW : AdjWords)
    [Countable Γ] (a₀ : Γ) (tX : PT B) (χ : ChAlg g X →⋆ₐ[ℂ] ℂ)
    (hok : ∀ x, (g x).Ok) (htX : tX.Ok) (hXe : X = tX.op) (ha₀ : g a₀ = Sum.inr t₀)
    (hc : ∀ x y, Commute (g x).op (g y).op ∧ Commute (g x).op (star (g y).op))
    (hXc : ∀ x, Commute X (g x).op ∧ Commute X (star (g x).op)) (hXs : IsSelfAdjoint X)
    (hχ : ∀ y, ‖χ y‖ ≤ ‖(y : B.Hb →L[ℂ] B.Hb)‖) (hχ0 : χ (genE g X a₀) ≠ 0) :
    ∃ (M : ℕ) (s : ℕ → ChAlg g X → ℂ) (f : ℕ → B.I → H E B.a B.b → ℂ),
      (∀ y, Tendsto (fun k => s k (genE g X y)) atTop (𝓝 (χ (genE g X y)))) ∧
      Tendsto (fun k => s k (XE g X)) atTop (𝓝 (χ (XE g X))) ∧
      ∀ k, s k (genE g X a₀) ≠ 0 ∧ (∀ i, Continuous (f k i)) ∧ f k ≠ 0 ∧ LeftInv (f k) ∧ WL2 B.D M (f k) ∧
        PositivityTheory.Rg.BcB.E.conv B.D.μ t₀.Φ (f k) = s k (genE g X a₀) • f k ∧
        (∀ y (t : PT B), g y = Sum.inr t →
          PositivityTheory.Rg.BcB.E.conv B.D.μ (mulM B.D.μ t.Φ t₀.Φ) (f k) = (s k (genE g X y) * s k (genE g X a₀)) • f k) ∧
        PositivityTheory.Rg.BcB.E.conv B.D.μ (mulM B.D.μ tX.Φ t₀.Φ) (f k) = (s k (XE g X) * s k (genE g X a₀)) • f k := by
  have ht₀ : t₀.Ok := ok_of_inr g hok ha₀
  have ea : ((genE g X a₀ : ChAlg g X) : B.Hb →L[ℂ] B.Hb) = t₀.op := by
    show (g a₀).op = _
    rw [ha₀]
    rfl
  have hspec : ∀ x : ChAlg g X, IsTestM (phiG g X t₀ x) ∧ IsROp B.D (phiG g X t₀ x) ((x : B.Hb →L[ℂ] B.Hb) * t₀.op) :=
    fun x => by
      have h := phiEx hBO hBW hBS hAW g X tX t₀ hok htX hXe ht₀ x
      unfold phiG
      rw [dif_pos h]
      exact h.choose_spec
  letI : CommRing (ChAlg g X) := chComm g X hc hXc hXs
  have hCc : ({1} ∪ Set.range (genE g X) ∪ {XE g X} : Set (ChAlg g X)).Countable :=
    ((Set.countable_singleton _).union (Set.countable_range _)).union (Set.countable_singleton _)
  obtain ⟨M, s, f, hlim, hk⟩ := hE2 E B.a B.b B.D B.I B.Hb (ContinuousLinearMap.id ℂ B.Hb) (fun v => rfl) (ChAlg g X)
    (StarSubalgebra.subtype _) χ (genE g X a₀) ({1} ∪ Set.range (genE g X) ∪ {XE g X}) (phiG g X t₀) hχ hχ0 hCc
    (Or.inl (Or.inl rfl)) (fun x => (hspec x).1) (fun x => ⟨_, (hspec x).2, fun v => by
      change ((x : B.Hb →L[ℂ] B.Hb) * t₀.op) v =
        ((x : B.Hb →L[ℂ] B.Hb) * ((genE g X a₀ : ChAlg g X) : B.Hb →L[ℂ] B.Hb)) v
      rw [ea], fun u hu => by
      have hu0 : u = 0 := inner_self_eq_zero.1 (hu u)
      rw [hu0, map_zero]⟩)
  refine ⟨M, fun k x => s k x, f, fun y => hlim _ (Or.inl (Or.inr ⟨y, rfl⟩)), hlim _ (Or.inr rfl), fun k => ?_⟩
  obtain ⟨h0, hcont, hne, hL, hW, hconv⟩ := hk k
  have key : ∀ x ∈ ({1} ∪ Set.range (genE g X) ∪ {XE g X} : Set (ChAlg g X)), ∀ Ψ, IsTestM Ψ →
      IsROp B.D Ψ ((x : B.Hb →L[ℂ] B.Hb) * t₀.op) →
      PositivityTheory.Rg.BcB.E.conv B.D.μ Ψ (f k) = s k (x * genE g X a₀) • f k := fun x hx Ψ h1 h2 =>
    (PositivityTheory.Rg.BcB.E2.conv_eq_of_isROp B.D h1 (hspec x).1 h2 (hspec x).2 hcont hL).trans (hconv x hx)
  refine ⟨h0, hcont, hne, hL, hW, ?_, fun y t hy => ?_, ?_⟩
  · have h0' := hBO E B t₀ t₀ ht₀ ht₀
    have h := key 1 (Or.inl (Or.inl rfl)) t₀.Φ h0'.1 (by
      show IsROp B.D t₀.Φ (1 * t₀.op)
      rw [one_mul]
      exact h0'.2.1)
    rw [one_mul] at h
    exact h
  · have ht := ok_of_inr g hok hy
    have hm := mul_facts t₀ hTM hBO t ht ht₀
    have e : ((genE g X y : ChAlg g X) : B.Hb →L[ℂ] B.Hb) = t.op := by
      show (g y).op = _
      rw [hy]
      rfl
    have h := key (genE g X y) (Or.inl (Or.inr ⟨y, rfl⟩)) _ hm.1 (by rw [e]; exact hm.2)
    rw [map_mul] at h
    exact h
  · have hm := mul_facts t₀ hTM hBO tX htX ht₀
    have e : ((XE g X : ChAlg g X) : B.Hb →L[ℂ] B.Hb) = tX.op := hXe
    have h := key (XE g X) (Or.inr rfl) _ hm.1 (by rw [e]; exact hm.2)
    rw [map_mul] at h
    exact h

end Real

/- English proof (translation)
Introduce `E _ _ _ B Γ _ g a₀ t₀ X tX χ hok htX hXe ha₀ hc hXc hXs hχ hχ0`. Conclude with `realise_commuting_family g X t₀ hE2 hTM hBO hBW hBS hAW a₀ tX χ hok htX hXe ha₀ hc hXc hXs hχ hχ0`.
-/
theorem realise (hE2 : E2) (hTM : TensMul) (hBO : BlockOperatorsProductAdjoint) (hBW : BlockWordOperators) (hBS : BlockLinearCombinations) (hAW : AdjWords) :
    RealiseSt := by
  intro E _ _ _ B Γ _ g a₀ t₀ X tX χ hok htX hXe ha₀ hc hXc hXs hχ hχ0
  exact realise_commuting_family g X t₀ hE2 hTM hBO hBW hBS hAW a₀ tX χ hok htX hXe ha₀ hc hXc hXs hχ hχ0

end PositivityTheory.Rg.BcB.F.Rd.B

end
