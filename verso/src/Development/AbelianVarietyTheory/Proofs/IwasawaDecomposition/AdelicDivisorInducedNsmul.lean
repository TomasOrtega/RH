import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ImaginaryRootNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetsOfParOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelAdd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelNeg
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AltSumMultilinear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArakelovTopUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPullbackStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPowStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleModelsOfHtBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelOfLocMax
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FamilyMetricsSmoothStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetricConjugationSymmetryStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueCx

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CombPow

section Free
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [zero_nsmul, zero_nsmul, LineTest.expo_zero]`. Consider the case `succ n ih => rw [succ_nsmul, succ_nsmul, LineTest.expo_add, ih]`.
-/
theorem expo_nsmul (w : Sym E →₀ ℤ) (n : ℕ) : expo Dw (n • w) = n • expo Dw w := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, LineTest.expo_zero]
  | succ n ih => rw [succ_nsmul, succ_nsmul, LineTest.expo_add, ih]

variable {Dw} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [zero_nsmul, zero_nsmul]`. Simplify using `[divOf]`. Consider the case `succ n ih => rw [succ_nsmul, succ_nsmul, LineTest.divOf_add, ih]`.
-/
theorem divOf_nsmul (ex : Letter Dw → ℤ) (n : ℕ) : divOf Y (n • ex) = n • divOf Y ex := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul]; simp [divOf]
  | succ n ih => rw [succ_nsmul, succ_nsmul, LineTest.divOf_add, ih]

/- English proof (translation)
Establish `eT : (∏ z : Letter Dw, (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose z.1 z.2 ^ expo Dw (n • w) z) = (∏ z : Letter Dw, (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose z.1 z.2 ^ expo Dw w z) ^ n`. Rewrite using `[expo_nsmul, ← Finset.prod_pow]`. Use `Finset.prod_congr rfl fun z _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, nsmul_eq_mul, mul_comm, zpow_mul, zpow_natCast]`. Simplify using `only [lgOf, dif_pos (LineTest.residueCharacteristic_prime v)]`.

Rewrite using `[eT, Finsupp.sum_smul_index' (fun _ => by simp)]`. Simplify using `only [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, mul_assoc, ← Finsupp.mul_sum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lgOf_nsmul (w : Sym E →₀ ℤ) (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v) (y : AlgPt Y.Y) :
    lgOf Y (n • w) v ε y - Real.log (ε.w (valAt y.1 ((((∏ z : Letter Dw,
      (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose z.1 z.2 ^ expo Dw w z) ^ n *
        (eqn (divOf Y (expo Dw (n • w))) (below y.1))⁻¹ : Y.Y.Fnˣ)) : Y.Y.Fn))) =
      n * (lgOf Y w v ε y - Real.log (ε.w (valAt y.1 ((((∏ z : Letter Dw,
        (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose z.1 z.2 ^ expo Dw w z) *
          (eqn (divOf Y (expo Dw w)) (below y.1))⁻¹ : Y.Y.Fnˣ)) : Y.Y.Fn)))) := by
  have eT : (∏ z : Letter Dw, (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose z.1 z.2 ^
      expo Dw (n • w) z) = (∏ z : Letter Dw,
        (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose z.1 z.2 ^ expo Dw w z) ^ n := by
    rw [expo_nsmul, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun z _ => ?_
    rw [Pi.smul_apply, nsmul_eq_mul, mul_comm, zpow_mul, zpow_natCast]
  simp only [lgOf, dif_pos (LineTest.residueCharacteristic_prime v)]
  rw [eT, Finsupp.sum_smul_index' (fun _ => by simp)]
  simp only [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, mul_assoc, ← Finsupp.mul_sum]
  ring

end Free

section Abstract

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F}

/- English proof (translation)
Take `⟨hfin, r, hr, hinf, hv⟩` from `h`. Use `⟨hfin, fun i => r (fun _ => i PUnit.unit PUnit.unit) ^ n, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hD, smul_comm]`. Conclude with `InducedPow.presents_pow L.B M.j n L.isLB hr`. Introduce `σ y y' i f hy hi hf`.

Establish `hi'` using `InducedPow.mem_chart L.B M.j n hi`. Take `⟨g, hg⟩` from `A₁.D.exists_isEqn (under y)`. Establish `hgen` using `CartierDiv.isEqn_iff_generatesAt_inv.1 hg`. Establish `hgenk (l : ℕ) : (l • A₁.D).GeneratesAt (under y) ((g : Y.Fn)⁻¹ ^ l)`. Use `CartierDiv.isEqn_iff_generatesAt_inv.1 (hg.nsmul l)` as an intermediate fact.

Rewrite `this` using `[Units.val_pow_eq_pow_val, ← inv_pow]`. Then use the resulting hypothesis. Establish `h₁` using `hinf σ y y' (fun _ => i PUnit.unit PUnit.unit) _ hy hi' (hgenk m).regularAt`. Rewrite `h₁` using `[C.pn_mPow Y σ A₁.D m (A₁.m σ) _ y hgen, hn₁, hc₁]`. Simplify using `only [Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, one_mul] at h₁`. Establish `hu` using `(hr.isEqn _ _ hi').generatesAt_iff.1 (hgenk m)`.

Establish `hgn : Aₙ.D.IsEqn (under y) (g ^ n)` using `hD ▸ hg.nsmul n`. Establish `hgenn' : Aₙ.D.GeneratesAt (under y) ((g : Y.Fn)⁻¹ ^ n)`. Use `CartierDiv.isEqn_iff_generatesAt_inv.1 hgn` as an intermediate fact. Rewrite `this` using `[Units.val_pow_eq_pow_val, ← inv_pow]`. Then use the resulting hypothesis. Establish `hgennk : ((m : ℕ) • Aₙ.D).GeneratesAt (under y) (((g : Y.Fn)⁻¹ ^ n) ^ (m : ℕ))`.

Use `CartierDiv.isEqn_iff_generatesAt_inv.1 (hgn.nsmul m)` as an intermediate fact. Rewrite `this` using `[Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← inv_pow, ← inv_pow]`. Then use the resulting hypothesis. Establish `ha : RegAt (under y) (f * ((g : Y.Fn) ^ n) ^ (m : ℕ))`. Use `(hgn.nsmul m).regularAt_iff.1 hf` as an intermediate fact. Rewrite `this` using `[Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]`. Then use the resulting hypothesis.

Establish `h₂` using `C.pn_mul Y σ _ (C.mPow Y σ Aₙ.D m (Aₙ.m σ)) _ _ y ha hgennk.regularAt`. Establish `e1 : f * ((g : Y.Fn) ^ n) ^ (m : ℕ) * (((g : Y.Fn)⁻¹) ^ n) ^ (m : ℕ) = f`. Rewrite using `[mul_assoc, ← mul_pow, ← mul_pow, mul_inv_cancel₀ g.ne_zero, one_pow, one_pow, mul_one]`. Rewrite `h₂` using `[e1, C.pn_mPow Y σ Aₙ.D _ (Aₙ.m σ) _ y hgenn', hmet σ y g hg]`. Establish `h₃ : f * ((r (fun _ => i PUnit.unit PUnit.unit) ^ n : Y.Fnˣ) : Y.Fn) = f * ((g : Y.Fn) ^ n) ^ (m : ℕ) * ((g : Y.Fn)⁻¹ ^ (m : ℕ) * (r (fun _ => i PUnit.unit PUnit.unit) : Y.Fn)) ^ n`.

Establish `hg0 : (g : Y.Fn) ≠ 0` using `g.ne_zero`. Rewrite using `[Units.val_pow_eq_pow_val, mul_pow, ← pow_mul, ← pow_mul, inv_pow, mul_comm (m : ℕ) n, mul_assoc f, ← mul_assoc (_ ^ (n * (m : ℕ))), mul_inv_cancel₀ (pow_ne_zero _ hg0), one_mul]`. Establish `h₄ : ((L.pow n).φ _).φ (i PUnit.unit) y' = (n : ℝ) * (L.φ _).φ (i PUnit.unit PUnit.unit) y'` using `((L.φ _).zpow_φ _ _ y').trans (by simp)`. Rewrite using `[hnₙ, hcₙ]`. Simplify using `only [Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, one_mul]`.

Establish `h₅ : Real.exp (-((n : ℝ) * (L.φ _).φ (i PUnit.unit PUnit.unit) y')) = Real.exp (-(L.φ _).φ (i PUnit.unit PUnit.unit) y') ^ n`. Rewrite using `[← Real.exp_nat_mul, mul_neg]`. Rewrite using `[h₂, h₃, ratVal_mul ha (InducedPow.unitAt_pow hu n).regAt, InducedPow.ratVal_pow y hu n, h₄, h₅, ← pow_mul (C.pn Y σ A₁.D (A₁.m σ) (C.cx Y σ (g : Y.Fn)⁻¹) y), mul_comm n (m : ℕ), pow_mul, h₁]`. Rewrite using `[norm_mul, norm_pow]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `v ε y yt i hyt hi`. Establish `hi' : ⊤ ≤ yt ⁻¹ᵁ L.B.U (i PUnit.unit PUnit.unit)` using `fun x hx => Set.mem_iInter.1 (hi hx) PUnit.unit`. Establish `h₁` using `hv v ε y yt (fun _ => i PUnit.unit PUnit.unit) hyt hi'`. Establish `h₂ : below y.1 ∈ (L.B.pull M.j).U fun _ => i PUnit.unit PUnit.unit` using `OfModel.le_chart M L.B ε y yt hyt (i := fun _ => i PUnit.unit PUnit.unit) hi' trivial`. Take `⟨T, S, hT, hl₁, hlₙ⟩` from `hlg v ε y`.

Use `set x := below y.1`. Use `set E₁ := eqn A₁.D x`. Use `set Eₙ := eqn Aₙ.D x`. Use `set ρ := r (fun _ => i PUnit.unit PUnit.unit)`. Establish `hu₁ : UnitAt x ((T : Y.Fn) * (E₁ : Y.Fn)⁻¹)`.

Use `(Base.isEqn_eqn A₁.D x).iff_unitAt.1 hT` as an intermediate fact. Rewrite `this` using `[div_eq_mul_inv]`. Then use the resulting hypothesis. Establish `hTn : Aₙ.D.IsEqn x (T ^ n)` using `hD ▸ hT.nsmul n`. Establish `huₙ : UnitAt x ((T : Y.Fn) ^ n * (Eₙ : Y.Fn)⁻¹)`. Use `(Base.isEqn_eqn Aₙ.D x).iff_unitAt.1 hTn` as an intermediate fact.

Rewrite `this` using `[div_eq_mul_inv, Units.val_pow_eq_pow_val]`. Then use the resulting hypothesis. Establish `hq : UnitAt x ((E₁ : Y.Fn)⁻¹ ^ (m : ℕ) * (ρ : Y.Fn))`. Use `((Base.isEqn_eqn A₁.D x).nsmul m).iff_unitAt.1 (hr.isEqn _ _ h₂)` as an intermediate fact. Rewrite `this` using `[div_eq_inv_mul, Units.val_pow_eq_pow_val, ← inv_pow]`. Then use the resulting hypothesis. Use `set Λ : Y.Fn → ℝ := fun a => Real.log (ε.w (valAt y.1 a)) with hΛ`.

Establish `hw0 {a : Y.Fn} (ha : UnitAt x a) : ε.w (valAt y.1 a) ≠ 0` using `(ε.w.pos (Base.valAt_zpow y.1 ha).1).ne'`. Establish `hmul {a b : Y.Fn} (ha : UnitAt x a) (hb : UnitAt x b) : Λ (a * b) = Λ a + Λ b`. Simplify using `only [hΛ]`. Rewrite using `[OfModel.valAt_mul y.1 ha.regAt hb.regAt, map_mul, Real.log_mul (hw0 ha) (hw0 hb)]`. Establish `hpow {a : Y.Fn} (ha : UnitAt x a) (k : ℕ) : Λ (a ^ k) = k * Λ a`.

Simplify using `only [hΛ]`. Rewrite using `[InducedPow.valAt_pow y.1 ha.regAt k, map_pow, Real.log_pow]`. Establish `hinv {a : Y.Fn} (ha : UnitAt x a) : Λ a⁻¹ = -Λ a`. Simplify using `only [hΛ]`. Use `(Base.valAt_zpow y.1 ha).2 (-1)` as an intermediate fact.

Rewrite `this` using `[zpow_neg_one, zpow_neg_one]`. Rewrite using `[this, map_inv₀, Real.log_inv]`. Establish `e : (((Eₙ⁻¹ ^ (m : ℕ) * ρ ^ n : Y.Fnˣ)) : Y.Fn) = ((T : Y.Fn) ^ n * (Eₙ : Y.Fn)⁻¹) ^ (m : ℕ) * ((((E₁ : Y.Fn)⁻¹ ^ (m : ℕ) * (ρ : Y.Fn)) ^ n) * ((((T : Y.Fn) * (E₁ : Y.Fn)⁻¹) ^ (m : ℕ)) ^ n)⁻¹)`. Establish `hT0 : (T : Y.Fn) ≠ 0` using `T.ne_zero`. Establish `hE0 : (E₁ : Y.Fn) ≠ 0` using `E₁.ne_zero`.

Establish `hEn0 : (Eₙ : Y.Fn) ≠ 0` using `Eₙ.ne_zero`. Simplify using `only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hval : Λ (((Eₙ⁻¹ ^ (m : ℕ) * ρ ^ n : Y.Fnˣ)) : Y.Fn) = (m : ℕ) * Λ ((T : Y.Fn) ^ n * (Eₙ : Y.Fn)⁻¹) + (n * Λ ((E₁ : Y.Fn)⁻¹ ^ (m : ℕ) * (ρ : Y.Fn)) - n * ((m : ℕ) * Λ ((T : Y.Fn) * (E₁ : Y.Fn)⁻¹)))`.

Establish `hp₁` using `InducedPow.unitAt_pow (InducedPow.unitAt_pow hu₁ (m : ℕ)) n`. Rewrite using `[e, hmul (InducedPow.unitAt_pow huₙ _) ((InducedPow.unitAt_pow hq n).mul hp₁.inv), hmul (InducedPow.unitAt_pow hq n) hp₁.inv, hinv hp₁, hpow huₙ, hpow hq, hpow (InducedPow.unitAt_pow hu₁ _), hpow hu₁]`. Expand and normalize the polynomial expressions, which then agree. Express the relevant statement in the definitionally equal form `(m : ℕ) * Aₙ.lg v ε y = Λ (((Eₙ⁻¹ ^ (m : ℕ) * ρ ^ n : Y.Fnˣ)) : Y.Fn) - (m : ℕ) * (Aₙ.n : ℕ) * 0`. Express the relevant statement in the definitionally equal form `(m : ℕ) * A₁.lg v ε y = Λ (((E₁⁻¹ ^ (m : ℕ) * ρ : Y.Fnˣ)) : Y.Fn) - (m : ℕ) * (A₁.n : ℕ) * 0 at h₁`.

Rewrite using `[hval, hlₙ, hnₙ]`. Rewrite `h₁` using `[hl₁, hn₁]`. Establish `hq' : (((E₁⁻¹ ^ (m : ℕ) * ρ : Y.Fnˣ)) : Y.Fn) = (E₁ : Y.Fn)⁻¹ ^ (m : ℕ) * (ρ : Y.Fn)`. Simplify using `only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]`. Establish `hu₁' : (((T * E₁⁻¹ : Y.Fnˣ)) : Y.Fn) = (T : Y.Fn) * (E₁ : Y.Fn)⁻¹`.

Simplify using `only [Units.val_mul, Units.val_inv_eq_inv_val]`. Establish `huₙ' : (((T ^ n * Eₙ⁻¹ : Y.Fnˣ)) : Y.Fn) = (T : Y.Fn) ^ n * (Eₙ : Y.Fn)⁻¹`. Simplify using `only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]`. Express the relevant statement in the definitionally equal form `(m : ℕ) * (Λ (((T * E₁⁻¹ : Y.Fnˣ)) : Y.Fn) + S) = _ at h₁`. Express the relevant statement in the definitionally equal form `(m : ℕ) * (Λ (((T ^ n * Eₙ⁻¹ : Y.Fnˣ)) : Y.Fn) + n * S) = _`.

Rewrite `h₁` using `[hq', hu₁']`. Rewrite using `[huₙ']`. Move the coercions through the operations in `at h₁ ⊢`. Take the linear combination `(n : ℝ) * h₁`.
-/
theorem induced_pow_of {A₁ Aₙ : Adl C Y} {M : Model Y} {L : HermLB M.p} {m : ℕ+} (n : ℕ)
    (hn₁ : A₁.n = 1) (hnₙ : Aₙ.n = 1) (hc₁ : A₁.ci = 0) (hcₙ : Aₙ.ci = 0) (hD : Aₙ.D = n • A₁.D)
    (hmet : ∀ (σ : F →+* ℂ) (y : Pts Y σ) (g : Y.Fnˣ), A₁.D.IsEqn (under y) g →
      C.pn Y σ Aₙ.D (Aₙ.m σ) (C.cx Y σ ((g : Y.Fn)⁻¹ ^ n)) y = C.pn Y σ A₁.D (A₁.m σ) (C.cx Y σ (g : Y.Fn)⁻¹) y ^ n)
    (hlg : ∀ (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v) (y : AlgPt Y), ∃ (T : Y.Fnˣ) (S : ℝ),
      A₁.D.IsEqn (below y.1) T ∧
      A₁.lg v ε y = Real.log (ε.w (valAt y.1 ((T * (eqn A₁.D (below y.1))⁻¹ : Y.Fnˣ) : Y.Fn))) + S ∧
      Aₙ.lg v ε y = Real.log (ε.w (valAt y.1 ((T ^ n * (eqn Aₙ.D (below y.1))⁻¹ : Y.Fnˣ) : Y.Fn))) + n * S)
    (h : A₁.Induced M L m 0) : Aₙ.Induced M (L.pow n) m 0 := by
  obtain ⟨hfin, r, hr, hinf, hv⟩ := h
  refine ⟨hfin, fun i => r (fun _ => i PUnit.unit PUnit.unit) ^ n, ?_, ?_, ?_⟩
  · rw [hD, smul_comm]
    exact InducedPow.presents_pow L.B M.j n L.isLB hr
  · intro σ y y' i f hy hi hf
    have hi' := InducedPow.mem_chart L.B M.j n hi
    obtain ⟨g, hg⟩ := A₁.D.exists_isEqn (under y)
    have hgen := CartierDiv.isEqn_iff_generatesAt_inv.1 hg
    have hgenk (l : ℕ) : (l • A₁.D).GeneratesAt (under y) ((g : Y.Fn)⁻¹ ^ l) := by
      have := CartierDiv.isEqn_iff_generatesAt_inv.1 (hg.nsmul l)
      rwa [Units.val_pow_eq_pow_val, ← inv_pow] at this
    have h₁ := hinf σ y y' (fun _ => i PUnit.unit PUnit.unit) _ hy hi' (hgenk m).regularAt
    rw [C.pn_mPow Y σ A₁.D m (A₁.m σ) _ y hgen, hn₁, hc₁] at h₁
    simp only [Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, one_mul] at h₁
    have hu := (hr.isEqn _ _ hi').generatesAt_iff.1 (hgenk m)
    have hgn : Aₙ.D.IsEqn (under y) (g ^ n) := hD ▸ hg.nsmul n
    have hgenn' : Aₙ.D.GeneratesAt (under y) ((g : Y.Fn)⁻¹ ^ n) := by
      have := CartierDiv.isEqn_iff_generatesAt_inv.1 hgn
      rwa [Units.val_pow_eq_pow_val, ← inv_pow] at this
    have hgennk : ((m : ℕ) • Aₙ.D).GeneratesAt (under y) (((g : Y.Fn)⁻¹ ^ n) ^ (m : ℕ)) := by
      have := CartierDiv.isEqn_iff_generatesAt_inv.1 (hgn.nsmul m)
      rwa [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← inv_pow, ← inv_pow] at this
    have ha : RegAt (under y) (f * ((g : Y.Fn) ^ n) ^ (m : ℕ)) := by
      have := (hgn.nsmul m).regularAt_iff.1 hf
      rwa [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val] at this
    have h₂ := C.pn_mul Y σ _ (C.mPow Y σ Aₙ.D m (Aₙ.m σ)) _ _ y ha hgennk.regularAt
    have e1 : f * ((g : Y.Fn) ^ n) ^ (m : ℕ) * (((g : Y.Fn)⁻¹) ^ n) ^ (m : ℕ) = f := by
      rw [mul_assoc, ← mul_pow, ← mul_pow, mul_inv_cancel₀ g.ne_zero, one_pow, one_pow, mul_one]
    rw [e1, C.pn_mPow Y σ Aₙ.D _ (Aₙ.m σ) _ y hgenn', hmet σ y g hg] at h₂
    have h₃ : f * ((r (fun _ => i PUnit.unit PUnit.unit) ^ n : Y.Fnˣ) : Y.Fn) =
        f * ((g : Y.Fn) ^ n) ^ (m : ℕ) *
          ((g : Y.Fn)⁻¹ ^ (m : ℕ) * (r (fun _ => i PUnit.unit PUnit.unit) : Y.Fn)) ^ n := by
      have hg0 : (g : Y.Fn) ≠ 0 := g.ne_zero
      rw [Units.val_pow_eq_pow_val, mul_pow, ← pow_mul, ← pow_mul, inv_pow, mul_comm (m : ℕ) n, mul_assoc f,
        ← mul_assoc (_ ^ (n * (m : ℕ))), mul_inv_cancel₀ (pow_ne_zero _ hg0), one_mul]
    have h₄ : ((L.pow n).φ _).φ (i PUnit.unit) y' = (n : ℝ) * (L.φ _).φ (i PUnit.unit PUnit.unit) y' :=
      ((L.φ _).zpow_φ _ _ y').trans (by simp)
    rw [hnₙ, hcₙ]
    simp only [Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, one_mul]
    have h₅ : Real.exp (-((n : ℝ) * (L.φ _).φ (i PUnit.unit PUnit.unit) y')) =
        Real.exp (-(L.φ _).φ (i PUnit.unit PUnit.unit) y') ^ n := by
      rw [← Real.exp_nat_mul, mul_neg]
    rw [h₂, h₃, ratVal_mul ha (InducedPow.unitAt_pow hu n).regAt, InducedPow.ratVal_pow y hu n, h₄, h₅,
      ← pow_mul (C.pn Y σ A₁.D (A₁.m σ) (C.cx Y σ (g : Y.Fn)⁻¹) y), mul_comm n (m : ℕ), pow_mul, h₁]
    rw [norm_mul, norm_pow]
    ring
  · intro v ε y yt i hyt hi
    have hi' : ⊤ ≤ yt ⁻¹ᵁ L.B.U (i PUnit.unit PUnit.unit) := fun x hx => Set.mem_iInter.1 (hi hx) PUnit.unit
    have h₁ := hv v ε y yt (fun _ => i PUnit.unit PUnit.unit) hyt hi'
    have h₂ : below y.1 ∈ (L.B.pull M.j).U fun _ => i PUnit.unit PUnit.unit :=
      OfModel.le_chart M L.B ε y yt hyt (i := fun _ => i PUnit.unit PUnit.unit) hi' trivial
    obtain ⟨T, S, hT, hl₁, hlₙ⟩ := hlg v ε y
    set x := below y.1
    set E₁ := eqn A₁.D x
    set Eₙ := eqn Aₙ.D x
    set ρ := r (fun _ => i PUnit.unit PUnit.unit)
    have hu₁ : UnitAt x ((T : Y.Fn) * (E₁ : Y.Fn)⁻¹) := by
      have := (Base.isEqn_eqn A₁.D x).iff_unitAt.1 hT
      rwa [div_eq_mul_inv] at this
    have hTn : Aₙ.D.IsEqn x (T ^ n) := hD ▸ hT.nsmul n
    have huₙ : UnitAt x ((T : Y.Fn) ^ n * (Eₙ : Y.Fn)⁻¹) := by
      have := (Base.isEqn_eqn Aₙ.D x).iff_unitAt.1 hTn
      rwa [div_eq_mul_inv, Units.val_pow_eq_pow_val] at this
    have hq : UnitAt x ((E₁ : Y.Fn)⁻¹ ^ (m : ℕ) * (ρ : Y.Fn)) := by
      have := ((Base.isEqn_eqn A₁.D x).nsmul m).iff_unitAt.1 (hr.isEqn _ _ h₂)
      rwa [div_eq_inv_mul, Units.val_pow_eq_pow_val, ← inv_pow] at this
    set Λ : Y.Fn → ℝ := fun a => Real.log (ε.w (valAt y.1 a)) with hΛ
    have hw0 {a : Y.Fn} (ha : UnitAt x a) : ε.w (valAt y.1 a) ≠ 0 :=
      (ε.w.pos (Base.valAt_zpow y.1 ha).1).ne'
    have hmul {a b : Y.Fn} (ha : UnitAt x a) (hb : UnitAt x b) : Λ (a * b) = Λ a + Λ b := by
      simp only [hΛ]
      rw [OfModel.valAt_mul y.1 ha.regAt hb.regAt, map_mul, Real.log_mul (hw0 ha) (hw0 hb)]
    have hpow {a : Y.Fn} (ha : UnitAt x a) (k : ℕ) : Λ (a ^ k) = k * Λ a := by
      simp only [hΛ]
      rw [InducedPow.valAt_pow y.1 ha.regAt k, map_pow, Real.log_pow]
    have hinv {a : Y.Fn} (ha : UnitAt x a) : Λ a⁻¹ = -Λ a := by
      simp only [hΛ]
      have := (Base.valAt_zpow y.1 ha).2 (-1)
      rw [zpow_neg_one, zpow_neg_one] at this
      rw [this, map_inv₀, Real.log_inv]
    have e : (((Eₙ⁻¹ ^ (m : ℕ) * ρ ^ n : Y.Fnˣ)) : Y.Fn) =
        ((T : Y.Fn) ^ n * (Eₙ : Y.Fn)⁻¹) ^ (m : ℕ) * ((((E₁ : Y.Fn)⁻¹ ^ (m : ℕ) * (ρ : Y.Fn)) ^ n) *
          ((((T : Y.Fn) * (E₁ : Y.Fn)⁻¹) ^ (m : ℕ)) ^ n)⁻¹) := by
      have hT0 : (T : Y.Fn) ≠ 0 := T.ne_zero
      have hE0 : (E₁ : Y.Fn) ≠ 0 := E₁.ne_zero
      have hEn0 : (Eₙ : Y.Fn) ≠ 0 := Eₙ.ne_zero
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
      field_simp
      ring
    have hval : Λ (((Eₙ⁻¹ ^ (m : ℕ) * ρ ^ n : Y.Fnˣ)) : Y.Fn) =
        (m : ℕ) * Λ ((T : Y.Fn) ^ n * (Eₙ : Y.Fn)⁻¹) + (n * Λ ((E₁ : Y.Fn)⁻¹ ^ (m : ℕ) * (ρ : Y.Fn)) -
          n * ((m : ℕ) * Λ ((T : Y.Fn) * (E₁ : Y.Fn)⁻¹))) := by
      have hp₁ := InducedPow.unitAt_pow (InducedPow.unitAt_pow hu₁ (m : ℕ)) n
      rw [e, hmul (InducedPow.unitAt_pow huₙ _) ((InducedPow.unitAt_pow hq n).mul hp₁.inv),
        hmul (InducedPow.unitAt_pow hq n) hp₁.inv, hinv hp₁, hpow huₙ, hpow hq, hpow (InducedPow.unitAt_pow hu₁ _),
        hpow hu₁]
      ring
    change (m : ℕ) * Aₙ.lg v ε y = Λ (((Eₙ⁻¹ ^ (m : ℕ) * ρ ^ n : Y.Fnˣ)) : Y.Fn) - (m : ℕ) * (Aₙ.n : ℕ) * 0
    change (m : ℕ) * A₁.lg v ε y = Λ (((E₁⁻¹ ^ (m : ℕ) * ρ : Y.Fnˣ)) : Y.Fn) - (m : ℕ) * (A₁.n : ℕ) * 0 at h₁
    rw [hval, hlₙ, hnₙ]
    rw [hl₁, hn₁] at h₁
    have hq' : (((E₁⁻¹ ^ (m : ℕ) * ρ : Y.Fnˣ)) : Y.Fn) = (E₁ : Y.Fn)⁻¹ ^ (m : ℕ) * (ρ : Y.Fn) := by
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    have hu₁' : (((T * E₁⁻¹ : Y.Fnˣ)) : Y.Fn) = (T : Y.Fn) * (E₁ : Y.Fn)⁻¹ := by
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    have huₙ' : (((T ^ n * Eₙ⁻¹ : Y.Fnˣ)) : Y.Fn) = (T : Y.Fn) ^ n * (Eₙ : Y.Fn)⁻¹ := by
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    change (m : ℕ) * (Λ (((T * E₁⁻¹ : Y.Fnˣ)) : Y.Fn) + S) = _ at h₁
    change (m : ℕ) * (Λ (((T ^ n * Eₙ⁻¹ : Y.Fnˣ)) : Y.Fn) + n * S) = _
    rw [hq', hu₁'] at h₁
    rw [huₙ']
    push_cast at h₁ ⊢
    linear_combination (n : ℝ) * h₁

end Abstract

section Flag

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (x : ToroidalCompactificationData s) (Φ : s.Flag)
  (k : s.Comp)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Rewrite using `[zero_nsmul, pow_zero, pow_zero]`. Take `⟨q, -, φ, f, h1, h2⟩` from `(Φ.C k).exists_adapted p`. Use `(FlagCpt.pn_met _ 0 (a := 1) ⟨_, _, φ, f, _, _, 1, ((Φ.C k).spMap_evStalk p).symm, h1, h2, by simp, by simp⟩).trans ?_` and prove the remaining obligations.

Simplify using `[FlagCpt.genSq]`. Consider the case `succ n ih`. Establish `hreg : (divOf (Φ.C k) (n • ex)).RegularAt (under p) ((g : (Φ.C k).Y.Fn)⁻¹ ^ n)`. Use `CartierDiv.isEqn_iff_generatesAt_inv.1 (divOf_nsmul (Φ.C k) ex n ▸ hg.nsmul n)` as an intermediate fact. Rewrite `this` using `[Units.val_pow_eq_pow_val, ← inv_pow]`.

Conclude with `this.regularAt`. Rewrite using `[succ_nsmul, pow_succ, pow_succ, pn_metsOf_add x Φ k Rp σ (n • ex) ex, (cxSt D.what₂.LL).pn_mAdd _ σ _ _ _ _ _ _ p hreg (CartierDiv.isEqn_iff_generatesAt_inv.1 hg).regularAt, ih]`.
-/
theorem pn_nsmul (Rp : Option ℝ) (σ : D.what₂.LL →+* ℂ) (ex : Letter S.Dw → ℤ) (p : Pts (Φ.C k).Y σ)
    (g : (Φ.C k).Y.Fnˣ) (hg : (divOf (Φ.C k) ex).IsEqn (under p) g) (n : ℕ) :
    (cxSt D.what₂.LL).pn _ σ _ (metsOf x Φ k Rp σ (n • ex)) ((cxSt D.what₂.LL).cx _ σ (((g : (Φ.C k).Y.Fn))⁻¹ ^ n)) p =
      (cxSt D.what₂.LL).pn _ σ _ (metsOf x Φ k Rp σ ex) ((cxSt D.what₂.LL).cx _ σ ((g : (Φ.C k).Y.Fn))⁻¹) p ^ n := by
  induction n with
  | zero =>
    rw [zero_nsmul, pow_zero, pow_zero]
    obtain ⟨q, -, φ, f, h1, h2⟩ := (Φ.C k).exists_adapted p
    refine (FlagCpt.pn_met _ 0 (a := 1) ⟨_, _, φ, f, _, _, 1, ((Φ.C k).spMap_evStalk p).symm, h1, h2, by simp,
      by simp⟩).trans ?_
    simp [FlagCpt.genSq]
  | succ n ih =>
    have hreg : (divOf (Φ.C k) (n • ex)).RegularAt (under p) ((g : (Φ.C k).Y.Fn)⁻¹ ^ n) := by
      have := CartierDiv.isEqn_iff_generatesAt_inv.1 (divOf_nsmul (Φ.C k) ex n ▸ hg.nsmul n)
      rw [Units.val_pow_eq_pow_val, ← inv_pow] at this
      exact this.regularAt
    rw [succ_nsmul, pow_succ, pow_succ, pn_metsOf_add x Φ k Rp σ (n • ex) ex,
      (cxSt D.what₂.LL).pn_mAdd _ σ _ _ _ _ _ _ p hreg (CartierDiv.isEqn_iff_generatesAt_inv.1 hg).regularAt, ih]

/- English proof (translation)
Introduce `D A N j S κ s x Φ k M m R w L hw h n`. Establish `hwn : ∀ a ∈ (n • w).support, a.2.1 = some R` using `fun a ha => hw a (Finsupp.support_smul ha)`. Use `induced_pow_of n rfl rfl rfl rfl ?_ ?_ ?_ h` and prove the remaining obligations. Use `show divOf (Φ.C k) (expo S.Dw (n • w)) = n • divOf (Φ.C k) (expo S.Dw w)`. Rewrite using `[expo_nsmul, divOf_nsmul]`.

Introduce `σ y g hg show (cxSt D.what₂.LL).pn _ σ (divOf (Φ.C k) (expo S.Dw (n • w))) (metsOf x Φ k (parOf (n • w)) σ (expo S.Dw (n • w))) _ y = (cxSt D.what₂.LL).pn _ σ (divOf (Φ.C k) (expo S.Dw w)) (metsOf x Φ k (parOf w) σ (expo S.Dw w)) _ y ^ n`. Rewrite using `[CombInd.metsOf_parOf x Φ k σ hwn, CombInd.metsOf_parOf x Φ k σ hw, expo_nsmul]`. Conclude with `pn_nsmul x Φ k _ σ _ y g hg n`. Introduce `v ε y`. Use `⟨∏ z : Letter S.Dw, ((Φ.C k).gr_spec (below y.1)).choose_spec.choose_spec.choose z.1 z.2 ^ expo S.Dw w z, lgOf (Φ.C k) w v ε y - Real.log (ε.w (valAt y.1 ((((∏ z : Letter S.Dw, ((Φ.C k).gr_spec (below y.1)).choose_spec.choose_spec.choose z.1 z.2 ^ expo S.Dw w z) * (eqn (divOf (Φ. …` and prove the remaining obligations.

Conclude with `(add_sub_cancel _ _).symm`. Use `show lgOf (Φ.C k) (n • w) v ε y = Real.log (ε.w (valAt y.1 ((((∏ z : Letter S.Dw, ((Φ.C k).gr_spec (below y.1)).choose_spec.choose_spec.choose z.1 z.2 ^ expo S.Dw w z) ^ n * (eqn (divOf (Φ.C k) (expo S.Dw (n • w))) (below y.1))⁻¹ : (Φ.C k).Y.Fnˣ)) : (Φ.C k).Y.Fn))) + _`. Combine the linear relations using `[lgOf_nsmul (Φ.C k) w n v ε y]`.
-/
theorem induced_nsmul : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (Φ : s.Flag) (k : s.Comp) (M : GlobalTheory.TrueGeo.Model (Φ.C k).Y) (m : ℕ+) (R : ℝ) (w : Sym D.host.E →₀ ℤ) (L : GlobalTheory.HermLB M.p), (∀ a ∈ w.support, a.2.1 = some R) → (adlOf (Φ.C k) (metsOf x Φ k) w).Induced M L m 0 → ∀ n : ℕ, (adlOf (Φ.C k) (metsOf x Φ k) (n • w)).Induced M (L.pow n) m 0 := by
  intro D A N j S κ s x Φ k M m R w L hw h n
  have hwn : ∀ a ∈ (n • w).support, a.2.1 = some R := fun a ha => hw a (Finsupp.support_smul ha)
  refine induced_pow_of n rfl rfl rfl rfl ?_ ?_ ?_ h
  · show divOf (Φ.C k) (expo S.Dw (n • w)) = n • divOf (Φ.C k) (expo S.Dw w)
    rw [expo_nsmul, divOf_nsmul]
  · intro σ y g hg
    show (cxSt D.what₂.LL).pn _ σ (divOf (Φ.C k) (expo S.Dw (n • w)))
        (metsOf x Φ k (parOf (n • w)) σ (expo S.Dw (n • w))) _ y =
      (cxSt D.what₂.LL).pn _ σ (divOf (Φ.C k) (expo S.Dw w)) (metsOf x Φ k (parOf w) σ (expo S.Dw w)) _ y ^ n
    rw [CombInd.metsOf_parOf x Φ k σ hwn, CombInd.metsOf_parOf x Φ k σ hw, expo_nsmul]
    exact pn_nsmul x Φ k _ σ _ y g hg n
  · intro v ε y
    refine ⟨∏ z : Letter S.Dw, ((Φ.C k).gr_spec (below y.1)).choose_spec.choose_spec.choose z.1 z.2 ^ expo S.Dw w z,
      lgOf (Φ.C k) w v ε y - Real.log (ε.w (valAt y.1 ((((∏ z : Letter S.Dw,
        ((Φ.C k).gr_spec (below y.1)).choose_spec.choose_spec.choose z.1 z.2 ^ expo S.Dw w z) *
          (eqn (divOf (Φ.C k) (expo S.Dw w)) (below y.1))⁻¹ : (Φ.C k).Y.Fnˣ)) : (Φ.C k).Y.Fn))),
      LineTest.isEqn_divOf _ _ _, ?_, ?_⟩
    · exact (add_sub_cancel _ _).symm
    · show lgOf (Φ.C k) (n • w) v ε y = Real.log (ε.w (valAt y.1 ((((∏ z : Letter S.Dw,
          ((Φ.C k).gr_spec (below y.1)).choose_spec.choose_spec.choose z.1 z.2 ^ expo S.Dw w z) ^ n *
            (eqn (divOf (Φ.C k) (expo S.Dw (n • w))) (below y.1))⁻¹ : (Φ.C k).Y.Fnˣ)) : (Φ.C k).Y.Fn))) + _
      linarith [lgOf_nsmul (Φ.C k) w n v ε y]

end Flag

end GlobalTheory.CombPow
