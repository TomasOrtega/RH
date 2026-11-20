import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLatFlagPair
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SplitComps
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArMonoReline
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm blockFnField)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Top.LineUnit

section Pull

variable {K₀ : Type} [Fintype K₀] {ι₀ : K₀ → Type} [∀ k, Fintype (ι₀ k)] {Ω₀ : Type} [Field Ω₀]
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]

/- English proof (translation)
Set `ψ : MvPolynomial K₀ Ω₀ →+* MvPolynomial K Ω` to `eval₂Hom (C.comp i) fun k => X (κ k)`. Establish `e : (mConeMap y).toRingHom.comp (rename v : MRing ι₀ →ₐ[ℤ] MRing J).toRingHom = ψ.comp (mConeMap y₀).toRingHom`. Use `MvPolynomial.ringHom_ext (fun r => ?_) fun p => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using `[mConeMap, ψ, hy, hv]`.

Establish `h0 : mConeMap y₀ f = 0` using `hf`. Use `show mConeMap y (rename v f) = 0`. Use `congrArg (fun φ => φ f) e` as an intermediate fact. Simplify `this` using `[h0]`.
-/
theorem rename_mem_mCoordIdeal {y₀ : (Σ k, ι₀ k) → Ω₀} {y : (Σ k, J k) → Ω} {κ : K₀ → K}
    {v : (Σ k, ι₀ k) → Σ k, J k} (i : Ω₀ →+* Ω) (hv : ∀ p, (v p).1 = κ p.1)
    (hy : ∀ p, y (v p) = i (y₀ p)) {f : MRing ι₀} (hf : f ∈ mCoordIdeal y₀) :
    rename v f ∈ mCoordIdeal y := by
  let ψ : MvPolynomial K₀ Ω₀ →+* MvPolynomial K Ω := eval₂Hom (C.comp i) fun k => X (κ k)
  have e : (mConeMap y).toRingHom.comp (rename v : MRing ι₀ →ₐ[ℤ] MRing J).toRingHom =
      ψ.comp (mConeMap y₀).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) fun p => ?_
    · simp
    · simp [mConeMap, ψ, hy, hv]
  have h0 : mConeMap y₀ f = 0 := hf
  show mConeMap y (rename v f) = 0
  have := congrArg (fun φ => φ f) e
  simpa [h0] using this

/- English proof (translation)
Use `⟨fun k => ?_, fun f hf => ?_⟩` and prove the remaining obligations. Take `⟨j, hj⟩` from `hz.1 (κ k)`. Take `⟨p, hp⟩` from `hb.2.2.2 ⟨κ k, j⟩ ⟨k, rfl⟩`. Establish `h2 : p.1 = k` using `hb.1 (by rw [← hb.2.2.1 p, hp])`. Take `⟨pk, pi⟩` from `p`.

Simplify using `only at h2`. Substitute `h2` using the available equality. Use `⟨pi, ?_⟩` and prove the remaining obligations. Use `show z (v ⟨pk, pi⟩) ≠ 0`. Rewrite using `[hp]`.

Conclude with `hj`. Use `hz.2 _ (rename_mem_mCoordIdeal i hb.2.2.1 hy hf)` as an intermediate fact. Rewrite `this` using `[map_rename, eval_rename]`. Then use the resulting hypothesis.
-/
theorem pull_mem_mcPts {y₀ : (Σ k, ι₀ k) → Ω₀} {y : (Σ k, J k) → Ω} {κ : K₀ → K}
    {v : (Σ k, ι₀ k) → Σ k, J k} (i : Ω₀ →+* Ω) (hb : IsBlockMap κ v)
    (hy : ∀ p, y (v p) = i (y₀ p)) {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) :
    (fun p => z (v p)) ∈ mcPts (mCoordIdeal y₀) := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨j, hj⟩ := hz.1 (κ k)
    obtain ⟨p, hp⟩ := hb.2.2.2 ⟨κ k, j⟩ ⟨k, rfl⟩
    have h2 : p.1 = k := hb.1 (by rw [← hb.2.2.1 p, hp])
    obtain ⟨pk, pi⟩ := p
    simp only at h2
    subst h2
    refine ⟨pi, ?_⟩
    show z (v ⟨pk, pi⟩) ≠ 0
    rw [hp]
    exact hj
  · have := hz.2 _ (rename_mem_mCoordIdeal i hb.2.2.1 hy hf)
    rwa [map_rename, eval_rename] at this

/- English proof (translation)
Use `show mConeMap y (X q) = 0 ↔ _`. Simplify using `[mConeMap, X_ne_zero]`.
-/
theorem X_mem_mCoordIdeal_iff (y : (Σ k, J k) → Ω) (q : Σ k, J k) :
    (X q : MRing J) ∈ mCoordIdeal y ↔ y q = 0 := by
  show mConeMap y (X q) = 0 ↔ _
  simp [mConeMap, X_ne_zero]

/- English proof (translation)
Take `⟨p, hp⟩` from `hb.2.2.2 q ⟨k₀, hq.symm⟩`. Establish `h2 : p.1 = k₀` using `hb.1 (by rw [← hb.2.2.1 p, hp, hq])`. Take `⟨pk, pi⟩` from `p`. Simplify using `only at h2`. Substitute `h2` using the available equality.

Conclude with `⟨e.symm pi, by simpa using hp⟩`.
-/
theorem block_onto {κ : K₀ → K} {v : (Σ k, ι₀ k) → Σ k, J k} (hb : IsBlockMap κ v) {n : Type}
    (k₀ : K₀) (e : n ≃ ι₀ k₀) (q : Σ k, J k) (hq : q.1 = κ k₀) : ∃ i, v ⟨k₀, e i⟩ = q := by
  obtain ⟨p, hp⟩ := hb.2.2.2 q ⟨k₀, hq.symm⟩
  have h2 : p.1 = k₀ := hb.1 (by rw [← hb.2.2.1 p, hp, hq])
  obtain ⟨pk, pi⟩ := p
  simp only at h2
  subst h2
  exact ⟨e.symm pi, by simpa using hp⟩

/- English proof (translation)
Use function extensionality and compare the values at `k'`. Distinguish the cases in `hk : ∃ k, κ k = k'`. Take `⟨k, rfl⟩` from `hk`. Rewrite using `[pullDeg, hκ.extend_apply]`. Distinguish the cases in `e : k = k₀`.

Substitute `e` using the available equality. Simplify using `[h1]`. Establish `: κ k ≠ κ k₀` using `fun h => e (hκ h)`. Simplify using `[h2 k e, this]`. Rewrite using `[pullDeg, Function.extend_apply' _ _ _ hk]`.

Establish `: k' ≠ κ k₀` using `fun h => hk ⟨k₀, h.symm⟩`. Simplify using `[this]`.
-/
theorem pullDeg_single [DecidableEq K] {κ : K₀ → K} (hκ : Function.Injective κ) {a : K₀ → ℤ} {k₀ : K₀}
    (h1 : a k₀ = 1) (h2 : ∀ k, k ≠ k₀ → a k = 0) :
    pullDeg κ a = fun k => (((Pi.single (κ k₀) 1 : K → ℕ) k : ℕ) : ℤ) := by
  funext k'
  by_cases hk : ∃ k, κ k = k'
  · obtain ⟨k, rfl⟩ := hk
    rw [pullDeg, hκ.extend_apply]
    by_cases e : k = k₀
    · subst e
      simp [h1]
    · have : κ k ≠ κ k₀ := fun h => e (hκ h)
      simp [h2 k e, this]
  · rw [pullDeg, Function.extend_apply' _ _ _ hk]
    have : k' ≠ κ k₀ := fun h => hk ⟨k₀, h.symm⟩
    simp [this]

end Pull

section Minors

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
  {y : (Σ k, J k) → Ω} {n : Type} {w₀ w₁ : n → Σ k, J k} {a₀ a₁ : K}

/- English proof (translation)
Use `show mConeMap y _ = 0`. Simplify using `only [mConeMap, map_sub, map_mul, aeval_X, b₀, b₁, hw]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem minor_mem (b₀ : ∀ i, (w₀ i).1 = a₀) (b₁ : ∀ i, (w₁ i).1 = a₁)
    (hw : ∀ i, y (w₀ i) = y (w₁ i)) (i j : n) :
    (X (w₀ i) * X (w₁ j) - X (w₀ j) * X (w₁ i) : MRing J) ∈ mCoordIdeal y := by
  show mConeMap y _ = 0
  simp only [mConeMap, map_sub, map_mul, aeval_X, b₀, b₁, hw]
  ring

/- English proof (translation)
Take `⟨i, hi⟩` from `hrel a₀`. Take `⟨b, hb⟩` from `s₀ ⟨a₀, i⟩ rfl`. Take `⟨j, hj⟩` from `hrel a₁`. Take `⟨c, hc⟩` from `s₁ ⟨a₁, j⟩ rfl`. Rewrite `hi` using `[← hb]`.

Rewrite `hj` using `[← hc]`. Establish `hu : (X (w₁ b) : MRing J) ∉ W`. Introduce `h`. Establish `m` using `hPW (minor_mem b₀ b₁ hw b c)`. Establish `h2 : (X (w₀ b) * X (w₁ c) : MRing J) ∈ W`.

Use `W.add_mem m (W.mul_mem_left (X (w₀ c)) h)` as an intermediate fact. Simplify using `using this`. Conclude with `(hW.mem_or_mem h2).elim hi hj`. Use `⟨X (w₁ b), X (w₀ b), hu, hi, ?_⟩` and prove the remaining obligations. Establish `e : (X (w₁ b) * X (w₀ a) - X (w₀ b) * X (w₁ a) : MRing J) = X (w₀ a) * X (w₁ b) - X (w₀ b) * X (w₁ a)` using `by ring`.

Rewrite using `[e]`. Conclude with `minor_mem b₀ b₁ hw a b`.
-/
theorem exists_unit [DecidableEq K] (b₀ : ∀ i, (w₀ i).1 = a₀) (b₁ : ∀ i, (w₁ i).1 = a₁)
    (s₀ : ∀ q : Σ k, J k, q.1 = a₀ → ∃ i, w₀ i = q) (s₁ : ∀ q : Σ k, J k, q.1 = a₁ → ∃ i, w₁ i = q)
    (hw : ∀ i, y (w₀ i) = y (w₁ i)) (a : n) {W : Ideal (MRing J)} (hW : W.IsPrime)
    (hPW : mCoordIdeal y ≤ W) (hrel : GroundTheory.Heights₂.Heights.NumbersDVR.IsRelevant W) :
    ∃ u v : MRing J, u ∉ W ∧ v ∉ W ∧ u * X (w₀ a) - v * X (w₁ a) ∈ mCoordIdeal y := by
  obtain ⟨i, hi⟩ := hrel a₀
  obtain ⟨b, hb⟩ := s₀ ⟨a₀, i⟩ rfl
  obtain ⟨j, hj⟩ := hrel a₁
  obtain ⟨c, hc⟩ := s₁ ⟨a₁, j⟩ rfl
  rw [← hb] at hi
  rw [← hc] at hj
  have hu : (X (w₁ b) : MRing J) ∉ W := by
    intro h
    have m := hPW (minor_mem b₀ b₁ hw b c)
    have h2 : (X (w₀ b) * X (w₁ c) : MRing J) ∈ W := by
      have := W.add_mem m (W.mul_mem_left (X (w₀ c)) h)
      simpa using this
    exact (hW.mem_or_mem h2).elim hi hj
  refine ⟨X (w₁ b), X (w₀ b), hu, hi, ?_⟩
  have e : (X (w₁ b) * X (w₀ a) - X (w₀ b) * X (w₁ a) : MRing J) =
      X (w₀ a) * X (w₁ b) - X (w₀ b) * X (w₁ a) := by ring
  rw [e]
  exact minor_mem b₀ b₁ hw a b

/- English proof (translation)
Take `⟨i, hi⟩` from `hz.1 a₀`. Take `⟨b, hb⟩` from `s₀ ⟨a₀, i⟩ rfl`. Take `⟨j, hj⟩` from `hz.1 a₁`. Take `⟨c, hc⟩` from `s₁ ⟨a₁, j⟩ rfl`. Rewrite `hi` using `[← hb]`.

Rewrite `hj` using `[← hc]`. Establish `hm : ∀ i j, z (w₀ i) * z (w₁ j) = z (w₀ j) * z (w₁ i)` using `fun i j => by`. Use `hz.2 _ (minor_mem b₀ b₁ hw i j)` as an intermediate fact. Simplify `this` using `[sub_eq_zero]`. Establish `h0 : z (w₀ c) ≠ 0` using `fun h => by`.

Use `hm b c` as an intermediate fact. Rewrite `this` using `[h, zero_mul]`. Conclude with `mul_ne_zero hi hj this`. Use `⟨z (w₀ c) / z (w₁ c), div_ne_zero h0 hj, fun i => ?_⟩` and prove the remaining obligations. Use `hm i c` as an intermediate fact.

Clear the denominators using the available nonvanishing facts. Conclude with `this`.
-/
theorem exists_prop (b₀ : ∀ i, (w₀ i).1 = a₀) (b₁ : ∀ i, (w₁ i).1 = a₁)
    (s₀ : ∀ q : Σ k, J k, q.1 = a₀ → ∃ i, w₀ i = q) (s₁ : ∀ q : Σ k, J k, q.1 = a₁ → ∃ i, w₁ i = q)
    (hw : ∀ i, y (w₀ i) = y (w₁ i)) {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) :
    ∃ r : ℂ, r ≠ 0 ∧ ∀ i, z (w₀ i) = r * z (w₁ i) := by
  obtain ⟨i, hi⟩ := hz.1 a₀
  obtain ⟨b, hb⟩ := s₀ ⟨a₀, i⟩ rfl
  obtain ⟨j, hj⟩ := hz.1 a₁
  obtain ⟨c, hc⟩ := s₁ ⟨a₁, j⟩ rfl
  rw [← hb] at hi
  rw [← hc] at hj
  have hm : ∀ i j, z (w₀ i) * z (w₁ j) = z (w₀ j) * z (w₁ i) := fun i j => by
    have := hz.2 _ (minor_mem b₀ b₁ hw i j)
    simpa [sub_eq_zero] using this
  have h0 : z (w₀ c) ≠ 0 := fun h => by
    have := hm b c
    rw [h, zero_mul] at this
    exact mul_ne_zero hi hj this
  refine ⟨z (w₀ c) / z (w₁ c), div_ne_zero h0 hj, fun i => ?_⟩
  have := hm i c
  field_simp
  exact this

end Minors

section Origin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

/- English proof (translation)
Set `cc : M.K → ℂ` to `fun k => if k = o.k₀ then r else 1`. Establish `hcc : ∀ k, cc k ≠ 0` using `fun k => by`. Apply the tactic sequence `by_cases e : k = o.k₀ <;> simp [cc, e, hr]`. Establish `hz'` using `mcPts_smul M.arith.2.1.2.1 cc hcc hz`. Establish `e1` using `o.A_h _ hz'`.

Establish `e2` using `M.A.smul cc z hcc`. Establish `e3` using `o.A_h _ hz`. Establish `e4 : (∏ k, ‖cc k‖ ^ M.A.a k) = ‖r‖`. Rewrite using `[Finset.prod_eq_single o.k₀]`. Simplify using `[cc, o.A_deg.1]`.

Introduce `k _ hk`. Simplify using `[o.A_deg.2 k hk]`. Simplify using the standard rewrite rules. Establish `e5 : cc o.k₀ = r` using `by simp [cc]`. Rewrite `e2` using `[e4, e3]`.

Rewrite using `[← e2, e1]`. Simplify using `only [e5]`.
-/
theorem hf_smul {Y : Model Xo c β} {S : Finset ℕ} {M : RootModel (CMType H) (D.p + D.q)}
    {Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} {Fx : FixedData Y Sys}
    (o : RootOrigin Y S M Fx) {z : (Σ k, M.ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal M.y)) {r : ℂ} (hr : r ≠ 0) :
    Fx.hf (fun i => r * z ⟨o.k₀, o.ix i⟩) = ‖r‖ * Fx.hf fun i => z ⟨o.k₀, o.ix i⟩ := by
  classical
  let cc : M.K → ℂ := fun k => if k = o.k₀ then r else 1
  have hcc : ∀ k, cc k ≠ 0 := fun k => by
    by_cases e : k = o.k₀ <;> simp [cc, e, hr]
  have hz' := mcPts_smul M.arith.2.1.2.1 cc hcc hz
  have e1 := o.A_h _ hz'
  have e2 := M.A.smul cc z hcc
  have e3 := o.A_h _ hz
  have e4 : (∏ k, ‖cc k‖ ^ M.A.a k) = ‖r‖ := by
    rw [Finset.prod_eq_single o.k₀]
    · simp [cc, o.A_deg.1]
    · intro k _ hk
      simp [o.A_deg.2 k hk]
    · simp
  have e5 : cc o.k₀ = r := by simp [cc]
  rw [e4, e3] at e2
  rw [← e2, e1]
  simp only [e5]

end Origin

end GlobalTheory.CompanionTheory.Ar.Top.LineUnit

namespace GlobalTheory.CompanionTheory.Ar.Top.LineUnit

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c Y S₀ S M₀ M₁ Sys Fx o₀ o₁ Ω _ K _ _ J _ y κ₀ v₀ κ₁ v₁ i₀ i₁ h₀ h₁ hy₀ hy₁ hg ha`. Set `w₀ : Fin (Fx.m + 1) → Σ k, J k` to `fun i => v₀ ⟨o₀.k₀, o₀.ix i⟩`. Set `w₁ : Fin (Fx.m + 1) → Σ k, J k` to `fun i => v₁ ⟨o₁.k₀, o₁.ix i⟩`. Establish `b₀ : ∀ i, (w₀ i).1 = κ₀ o₀.k₀` using `fun i => h₀.2.2.1 _`. Establish `b₁ : ∀ i, (w₁ i).1 = κ₁ o₁.k₀` using `fun i => h₁.2.2.1 _`.

Establish `s₀ : ∀ q : Σ k, J k, q.1 = κ₀ o₀.k₀ → ∃ i, w₀ i = q` using `block_onto h₀ o₀.k₀ o₀.ix`. Establish `s₁ : ∀ q : Σ k, J k, q.1 = κ₁ o₁.k₀ → ∃ i, w₁ i = q` using `block_onto h₁ o₁.k₀ o₁.ix`. Establish `hw : ∀ i, y (w₀ i) = y (w₁ i)` using `fun i => by`. Establish `e` using `congrArg (fun φ => φ (Fx.yf i)) hg`. Simplify using `only [RingHom.comp_apply] at e`.

Use `show y (v₀ _) = y (v₁ _)`. Rewrite using `[hy₀, hy₁, o₀.y_eq, o₁.y_eq]`. Conclude with `e`. Take `⟨j, hj⟩` from `ha.2.1.2.2 (κ₀ o₀.k₀)`. Take `⟨a, ha'⟩` from `s₀ ⟨κ₀ o₀.k₀, j⟩ rfl`.

Rewrite `hj` using `[← ha']`. Establish `hf : (X (w₀ a) : MRing J) ∉ mCoordIdeal y` using `hj`. Establish `hg' : (X (w₁ a) : MRing J) ∉ mCoordIdeal y`. Rewrite using `[X_mem_mCoordIdeal_iff, ← hw, ← X_mem_mCoordIdeal_iff]`. Conclude with `hf`.

Establish `d₀ : (pullHerm h₀ M₀.A).a = fun k => (((Pi.single (κ₀ o₀.k₀) 1 : K → ℕ) k : ℕ) : ℤ)` using `pullDeg_single h₀.1 o₀.A_deg.1 o₀.A_deg.2`. Establish `d₁ : (pullHerm h₁ M₁.A).a = fun k => (((Pi.single (κ₁ o₁.k₀) 1 : K → ℕ) k : ℕ) : ℤ)` using `pullDeg_single h₁.1 o₁.A_deg.1 o₁.A_deg.2`. Establish `hX : ∀ (q : Σ k, J k) (k : K), q.1 = k → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (X q : MRing J) (Pi.single k 1)`. Introduce and unpack `q k rfl`. Conclude with `isWeightedHomogeneous_X ℤ (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight J) q`.

Use `⟨⟨fun _ => (pullHerm h₀ M₀.A).a, fun _ => (pullHerm h₁ M₁.A).a, fun _ => X (w₀ a), fun _ => X (w₁ a)⟩, rfl, rfl, fun _ => ⟨?_, hf, hg', ?_⟩, fun _ => ⟨rfl, rfl, ?_⟩⟩` and prove the remaining obligations. Use `⟨Pi.single (κ₀ o₀.k₀) 1, Pi.single (κ₁ o₁.k₀) 1, hX _ _ (b₀ a), hX _ _ (b₁ a), ?_⟩ show _ = (pullHerm h₀ M₀.A).a - (pullHerm h₁ M₁.A).a` and prove the remaining obligations. Rewrite using `[d₀, d₁]`. Both sides reduce to the same expression. Introduce `W hW hPW hrel _`.

Conclude with `exists_unit b₀ b₁ s₀ s₁ hw a hW hPW hrel`. Introduce `z hz`. Take `⟨r, hr, hp⟩` from `exists_prop b₀ b₁ s₀ s₁ hw hz`. Establish `z₀` using `pull_mem_mcPts i₀ h₀ hy₀ hz`. Establish `z₁` using `pull_mem_mcPts i₁ h₁ hy₁ hz`.

Establish `e₀` using `o₀.A_h _ z₀`. Establish `e₁` using `o₁.A_h _ z₁`. Establish `es` using `hf_smul o₁ z₁ hr`. Establish `hfun : (fun i => z (w₀ i)) = fun i => r * z (w₁ i)` using `funext hp`. Use `show ‖eval z (map (Int.castRingHom ℂ) (X (w₀ a)))‖ * M₁.A.h (fun p => z (v₁ p)) = ‖eval z (map (Int.castRingHom ℂ) (X (w₁ a)))‖ * M₀.A.h (fun p => z (v₀ p))`.

Rewrite using `[map_X, map_X, eval_X, eval_X, e₀, e₁]`. Establish `e₂ : Fx.hf (fun i => z (v₀ ⟨o₀.k₀, o₀.ix i⟩)) = ‖r‖ * Fx.hf (fun i => z (v₁ ⟨o₁.k₀, o₁.ix i⟩))`. Rewrite using `[← es]`. Conclude with `congrArg Fx.hf hfun`. Rewrite using `[e₂, hp a, norm_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem lines_isometric : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S₀ S : Finset ℕ) (M₀ M₁ : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (o₀ : RootOrigin Y S₀ M₀ Fx) (o₁ : RootOrigin Y S M₁ Fx) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (κ₀ : M₀.K → K) (v₀ : (Σ k, M₀.ι k) → Σ k, J k) (κ₁ : M₁.K → K) (v₁ : (Σ k, M₁.ι k) → Σ k, J k) (i₀ : M₀.Ω →+* Ω) (i₁ : M₁.Ω →+* Ω) (h₀ : IsBlockMap κ₀ v₀) (h₁ : IsBlockMap κ₁ v₁), (∀ p, y (v₀ p) = i₀ (M₀.y p)) → (∀ p, y (v₁ p) = i₁ (M₁.y p)) → i₀.comp o₀.g = i₁.comp o₁.g → IsArithVar (mCoordIdeal y) (dimFl (CMType H) (D.p + D.q) + 1) → ∃ T : LocPair J ℤ Unit, T.x () = (pullHerm h₀ M₀.A).a ∧ T.x' () = (pullHerm h₁ M₁.A).a ∧ T.IsVertOff (mCoordIdeal y) ∅ ∧ T.IsIsometric (mCoordIdeal y) (fun _ => pullHerm h₀ M₀.A) (fun _ => pullHerm h₁ M₁.A) := by
  intro E _ _ _ H D l Xo c Y S₀ S M₀ M₁ Sys Fx o₀ o₁ Ω _ K _ _ J _ y κ₀ v₀ κ₁ v₁ i₀ i₁ h₀ h₁ hy₀ hy₁ hg ha
  let w₀ : Fin (Fx.m + 1) → Σ k, J k := fun i => v₀ ⟨o₀.k₀, o₀.ix i⟩
  let w₁ : Fin (Fx.m + 1) → Σ k, J k := fun i => v₁ ⟨o₁.k₀, o₁.ix i⟩
  have b₀ : ∀ i, (w₀ i).1 = κ₀ o₀.k₀ := fun i => h₀.2.2.1 _
  have b₁ : ∀ i, (w₁ i).1 = κ₁ o₁.k₀ := fun i => h₁.2.2.1 _
  have s₀ : ∀ q : Σ k, J k, q.1 = κ₀ o₀.k₀ → ∃ i, w₀ i = q := block_onto h₀ o₀.k₀ o₀.ix
  have s₁ : ∀ q : Σ k, J k, q.1 = κ₁ o₁.k₀ → ∃ i, w₁ i = q := block_onto h₁ o₁.k₀ o₁.ix
  have hw : ∀ i, y (w₀ i) = y (w₁ i) := fun i => by
    have e := congrArg (fun φ => φ (Fx.yf i)) hg
    simp only [RingHom.comp_apply] at e
    show y (v₀ _) = y (v₁ _)
    rw [hy₀, hy₁, o₀.y_eq, o₁.y_eq]
    exact e
  obtain ⟨j, hj⟩ := ha.2.1.2.2 (κ₀ o₀.k₀)
  obtain ⟨a, ha'⟩ := s₀ ⟨κ₀ o₀.k₀, j⟩ rfl
  rw [← ha'] at hj
  have hf : (X (w₀ a) : MRing J) ∉ mCoordIdeal y := hj
  have hg' : (X (w₁ a) : MRing J) ∉ mCoordIdeal y := by
    rw [X_mem_mCoordIdeal_iff, ← hw, ← X_mem_mCoordIdeal_iff]
    exact hf
  have d₀ : (pullHerm h₀ M₀.A).a = fun k => (((Pi.single (κ₀ o₀.k₀) 1 : K → ℕ) k : ℕ) : ℤ) :=
    pullDeg_single h₀.1 o₀.A_deg.1 o₀.A_deg.2
  have d₁ : (pullHerm h₁ M₁.A).a = fun k => (((Pi.single (κ₁ o₁.k₀) 1 : K → ℕ) k : ℕ) : ℤ) :=
    pullDeg_single h₁.1 o₁.A_deg.1 o₁.A_deg.2
  have hX : ∀ (q : Σ k, J k) (k : K), q.1 = k →
      GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (X q : MRing J) (Pi.single k 1) := by
    rintro q k rfl
    exact isWeightedHomogeneous_X ℤ (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight J) q
  refine ⟨⟨fun _ => (pullHerm h₀ M₀.A).a, fun _ => (pullHerm h₁ M₁.A).a,
    fun _ => X (w₀ a), fun _ => X (w₁ a)⟩, rfl, rfl, fun _ => ⟨?_, hf, hg', ?_⟩, fun _ => ⟨rfl, rfl, ?_⟩⟩
  · refine ⟨Pi.single (κ₀ o₀.k₀) 1, Pi.single (κ₁ o₁.k₀) 1, hX _ _ (b₀ a), hX _ _ (b₁ a), ?_⟩
    show _ = (pullHerm h₀ M₀.A).a - (pullHerm h₁ M₁.A).a
    rw [d₀, d₁]
    rfl
  · intro W hW hPW hrel _
    exact exists_unit b₀ b₁ s₀ s₁ hw a hW hPW hrel
  · intro z hz
    obtain ⟨r, hr, hp⟩ := exists_prop b₀ b₁ s₀ s₁ hw hz
    have z₀ := pull_mem_mcPts i₀ h₀ hy₀ hz
    have z₁ := pull_mem_mcPts i₁ h₁ hy₁ hz
    have e₀ := o₀.A_h _ z₀
    have e₁ := o₁.A_h _ z₁
    have es := hf_smul o₁ z₁ hr
    have hfun : (fun i => z (w₀ i)) = fun i => r * z (w₁ i) := funext hp
    show ‖eval z (map (Int.castRingHom ℂ) (X (w₀ a)))‖ * M₁.A.h (fun p => z (v₁ p)) =
      ‖eval z (map (Int.castRingHom ℂ) (X (w₁ a)))‖ * M₀.A.h (fun p => z (v₀ p))
    rw [map_X, map_X, eval_X, eval_X, e₀, e₁]
    have e₂ : Fx.hf (fun i => z (v₀ ⟨o₀.k₀, o₀.ix i⟩)) = ‖r‖ * Fx.hf (fun i => z (v₁ ⟨o₁.k₀, o₁.ix i⟩)) := by
      rw [← es]
      exact congrArg Fx.hf hfun
    rw [e₂, hp a, norm_mul]
    ring

end GlobalTheory.CompanionTheory.Ar.Top.LineUnit
