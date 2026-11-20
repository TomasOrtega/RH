import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActAApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsExtensionOfDense
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdelicHermitianCharacterPairingPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedStandardAdelicLatticeSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedStandardAdelicLatticePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFiniteAdeleExtendedCharacterOfCurveStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleAtOfIrreducibleTameStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorRationalTranslateMemThetaFunctionsStatement

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.Model

/- English proof (translation)
Apply `D.host.φ₀.injective` to reduce the goal to its premises. Rewrite using `[Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply]`. Simplify using the standard rewrite rules.
-/
theorem conjE_conjE (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply]
  simp

/- English proof (translation)
Simplify using `[sgA, inc, Formalism.UG.sigR, Formalism.UG.inclE]`.
-/
theorem sgA_incE (D : D7) (x : D.host.E) : sgA D (inc D x) = inc D (D.host.conj x) := by
  simp [sgA, inc, Formalism.UG.sigR, Formalism.UG.inclE]

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `[Wd, wdPh, ee, qH, U, Hf]`.
-/
theorem wd_at_zero (D : D7) (T : Tor D) {a d : ℕ} (G : VC D a d → ℂ) : Wd D T 0 G = G := by
  funext z
  simp [Wd, wdPh, ee, qH, U, Hf]

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Simplify using `[pt, embV, tor0]`.
-/
theorem pt_zero (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} :
    pt D (tor0 D cc δ) δ (0 : Matrix (Fin N') (Fin N) D.host.E) = 0 := by
  funext τ i j
  simp [pt, embV, tor0]

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Simplify using `only [pt, embV, tor0, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pt_nsmul (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (m : ℕ) (z : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (m • z) = m • pt D (tor0 D cc δ) δ z := by
  funext τ i j
  simp only [pt, embV, tor0, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast]
  ring

def incM (D : D7) (N N' : ℕ) : Matrix (Fin N') (Fin N) D.host.E →+ XA D N N' :=
  (inc D).toAddMonoidHom.mapMatrix

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem incM_apply (D : D7) (N N' : ℕ) (z : Matrix (Fin N') (Fin N) D.host.E) : incM D N N' z = z.map (inc D) := rfl

/- English proof (translation)
Establish `hm' : (m : D.host.E) ≠ 0` using `Nat.cast_ne_zero.2 hm.ne'`. Use `⟨Matrix.of fun i j => (m : D.host.E)⁻¹ * z i j, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `only [Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul]`. Clear the denominators using the available nonvanishing facts.

Use extensionality with `i j`. Establish `h1` using `congrFun (congrFun h i) j`. Simplify using `only [Matrix.map_apply, Matrix.smul_apply, nsmul_eq_mul] at h1`. Simplify using `only [Matrix.map_apply, Matrix.of_apply, map_mul, h1]`. Rewrite using `[← mul_assoc, ← map_natCast (inc D) m, ← map_mul, inv_mul_cancel₀ hm', map_one, one_mul]`.
-/
theorem exists_div (D : D7) {N N' : ℕ} {m : ℕ} (hm : 0 < m) (z : Matrix (Fin N') (Fin N) D.host.E) (a : XA D N N')
    (h : z.map (inc D) = m • a) : ∃ z' : Matrix (Fin N') (Fin N) D.host.E, z = m • z' ∧ z'.map (inc D) = a := by
  have hm' : (m : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  refine ⟨Matrix.of fun i j => (m : D.host.E)⁻¹ * z i j, ?_, ?_⟩
  · ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul]
    field_simp
  · ext i j
    have h1 := congrFun (congrFun h i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, nsmul_eq_mul] at h1
    simp only [Matrix.map_apply, Matrix.of_apply, map_mul, h1]
    rw [← mul_assoc, ← map_natCast (inc D) m, ← map_mul, inv_mul_cancel₀ hm', map_one, one_mul]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [h0]`. Consider the case `succ n ih => rw [succ_nsmul, h, ih, pow_succ]`.
-/
theorem mul_nsmul_left {X : Type} [AddCommGroup X] (f : X → ℂ) (h0 : f 0 = 1) (h : ∀ x y, f (x + y) = f x * f y)
    (m : ℕ) (x : X) : f (m • x) = f x ^ m := by
  induction m with
  | zero => simp [h0]
  | succ n ih => rw [succ_nsmul, h, ih, pow_succ]

/- English proof (translation)
Take `⟨ψ, hψ⟩` from `GlobalTheory.T.exists_finiteAdeleExtendedCharacter_of_curve D hD cc δ hc`. Take `⟨w, hw, hwd⟩` from `GlobalTheory.T.theta_point_additive_form D hD cc δ hc`. Take `⟨hinv, halt, hadj, hl, hr⟩` from `GlobalTheory.T.adelicHermitianCharacterPairing_properties D hD cc δ hc ψ hψ N N'`. Establish `hsd` using `GlobalTheory.T.completedStandardAdelicLattice_selfDual D hD cc δ hc ψ hψ N N'`. Take `⟨hrat, -, hdense, hden, -, -⟩` from `GlobalTheory.T.completedStandardAdelicLattice_properties D hD cc δ hc N N'`.

Establish `htt` using `GlobalTheory.T.weilOperator_rationalTranslate_mem_thetaFunctions D hD cc δ hc N N'`. Set `W₀ : Matrix (Fin N') (Fin N) D.host.E → TTs D (tor0 D cc δ) N N' →ₗ[ℂ] TTs D (tor0 D cc δ) N N'` to `fun z => { toFun := fun F => ⟨Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) F, htt z F F.2⟩ map_add' := fun F G => Subtype.ext (wd_add _ _ _) map_smul' := fun c F => Subtype.ext (wd_smul _ _ _) }`. Establish `hz1 : ∀ y : XA D N N', gamA ψ 0 y = 1` using `fun y => by simp [gamA, hψ.2.1]`. Establish `hz2 : ∀ y : XA D N N', gamA ψ y 0 = 1` using `fun y => by simp [gamA, hψ.2.1]`. Establish `hn1 : ∀ (m : ℕ) (x y : XA D N N'), gamA ψ (m • x) y = gamA ψ x y ^ m` using `fun m x y => mul_nsmul_left (fun x => gamA ψ x y) (hz1 y) (fun a b => hl a b y) m x`.

Establish `hn2 : ∀ (m : ℕ) (x y : XA D N N'), gamA ψ x (m • y) = gamA ψ x y ^ m` using `fun m x y => mul_nsmul_left (fun y => gamA ψ x y) (hz2 x) (fun a b => hr x a b) m y`. Establish `hiso : ∀ a ∈ latA D cc N N', ∀ b ∈ latA D cc N N', gamA ψ (w • a) b = 1` using `fun a ha b hb => (hsd _).1 ((latA D cc N N').smul_mem w ha) b hb`. Take `⟨WA, h1, h2, h3⟩` from `GlobalTheory.FinWeil.exists_extension_of_dense (incM D N N') (latA D cc N N').toAddSubgroup (fun x y => gamA ψ (w • x) y) W₀ (fun x y z => by simp only [smul_add, hl]) (fun x y z => hr _ _ _) hiso (fun x => by`. Take `⟨m, hm, hx⟩` from `hden x`. Use `⟨m, hm, fun a ha => ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Use `hiso _ hx a ha` as an intermediate fact. Rewrite `this` using `[smul_comm, hn1]`. Simplify using `only [hn2, this]`. Use `hiso a ha _ hx` as an intermediate fact. Rewrite `this` using `[hn2]`.

Use `show gamA ψ (w • m • a) x = 1`. Rewrite using `[smul_comm, hn1, this])`. Use the proof step `(fun x y v => by`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h` using `(hwd N N' x y).2.2 v`.

Establish `h' : gamA ψ (w • incM D N N' x) (incM D N N' y) = psi0 D cc δ (∑ i, ∑ j, (w : D.host.E) * x i j * D.host.conj (y i j))`. Rewrite using `[← hψ.2.2.1]`. Simplify using `only [gamA, incM_apply, Matrix.smul_apply, Matrix.map_apply, smul_AE, sgA_incE, map_sum, map_mul]`. Use `show Wd D _ _ (Wd D _ _ _) = gamA ψ (w • incM D N N' x) (incM D N N' y) • Wd D _ _ _`. Rewrite using `[h', h])`.

Use the proof step `(fun x m hm => hdense x m hm)`. Use the proof step `(fun v => by`. Take `⟨m, hm, hv⟩` from `v.2.2`. Use `⟨m, hm, ?_⟩` and prove the remaining obligations. Introduce and unpack `z ⟨a, ha, hz⟩`.

Take `⟨z', rfl, rfl⟩` from `exists_div D hm z a hz`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show Wd D _ (pt D _ δ (m • z')) _ = _`. Rewrite using `[pt_nsmul]`. Conclude with `hv _ ((hrat z').1 ha))`.

Use `⟨w, gamA ψ, WA, ⟨fun r => ?_, hw, hl, hr, halt, hadj, fun v => ?_, h2⟩, hsd, hinv, fun z F => ?_, h3⟩` and prove the remaining obligations. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[coe_sgO, coe_sgO, conjE_conjE]`. Use `h1 0` as an intermediate fact. Rewrite `this` using `[map_zero]`.

Rewrite using `[this]`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show Wd D _ (pt D _ δ 0) _ = _`. Rewrite using `[pt_zero, wd_at_zero]`. Rewrite using `[← incM_apply, h1]`.

Both sides reduce to the same expression.
-/
theorem exists_isModel (D : D7) (hD : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ) (N N' : ℕ) :
    ∃ w γ WA, GlobalTheory.FinWeil.IsModel D cc δ N N' w γ WA := by
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_finiteAdeleExtendedCharacter_of_curve D hD cc δ hc
  obtain ⟨w, hw, hwd⟩ := GlobalTheory.T.theta_point_additive_form D hD cc δ hc
  obtain ⟨hinv, halt, hadj, hl, hr⟩ := GlobalTheory.T.adelicHermitianCharacterPairing_properties D hD cc δ hc ψ hψ N N'
  have hsd := GlobalTheory.T.completedStandardAdelicLattice_selfDual D hD cc δ hc ψ hψ N N'
  obtain ⟨hrat, -, hdense, hden, -, -⟩ := GlobalTheory.T.completedStandardAdelicLattice_properties D hD cc δ hc N N'
  have htt := GlobalTheory.T.weilOperator_rationalTranslate_mem_thetaFunctions D hD cc δ hc N N'
  let W₀ : Matrix (Fin N') (Fin N) D.host.E → TTs D (tor0 D cc δ) N N' →ₗ[ℂ] TTs D (tor0 D cc δ) N N' := fun z =>
    { toFun := fun F => ⟨Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) F, htt z F F.2⟩
      map_add' := fun F G => Subtype.ext (wd_add _ _ _)
      map_smul' := fun c F => Subtype.ext (wd_smul _ _ _) }
  have hz1 : ∀ y : XA D N N', gamA ψ 0 y = 1 := fun y => by simp [gamA, hψ.2.1]
  have hz2 : ∀ y : XA D N N', gamA ψ y 0 = 1 := fun y => by simp [gamA, hψ.2.1]
  have hn1 : ∀ (m : ℕ) (x y : XA D N N'), gamA ψ (m • x) y = gamA ψ x y ^ m := fun m x y =>
    mul_nsmul_left (fun x => gamA ψ x y) (hz1 y) (fun a b => hl a b y) m x
  have hn2 : ∀ (m : ℕ) (x y : XA D N N'), gamA ψ x (m • y) = gamA ψ x y ^ m := fun m x y =>
    mul_nsmul_left (fun y => gamA ψ x y) (hz2 x) (fun a b => hr x a b) m y
  have hiso : ∀ a ∈ latA D cc N N', ∀ b ∈ latA D cc N N', gamA ψ (w • a) b = 1 := fun a ha b hb =>
    (hsd _).1 ((latA D cc N N').smul_mem w ha) b hb
  obtain ⟨WA, h1, h2, h3⟩ := GlobalTheory.FinWeil.exists_extension_of_dense (incM D N N') (latA D cc N N').toAddSubgroup
    (fun x y => gamA ψ (w • x) y) W₀
    (fun x y z => by simp only [smul_add, hl]) (fun x y z => hr _ _ _) hiso
    (fun x => by
      obtain ⟨m, hm, hx⟩ := hden x
      refine ⟨m, hm, fun a ha => ⟨?_, ?_⟩⟩
      · have := hiso _ hx a ha
        rw [smul_comm, hn1] at this
        simp only [hn2, this]
      · have := hiso a ha _ hx
        rw [hn2] at this
        show gamA ψ (w • m • a) x = 1
        rw [smul_comm, hn1, this])
    (fun x y v => by
      apply Subtype.ext
      have h := (hwd N N' x y).2.2 v
      have h' : gamA ψ (w • incM D N N' x) (incM D N N' y) =
          psi0 D cc δ (∑ i, ∑ j, (w : D.host.E) * x i j * D.host.conj (y i j)) := by
        rw [← hψ.2.2.1]
        simp only [gamA, incM_apply, Matrix.smul_apply, Matrix.map_apply, smul_AE, sgA_incE, map_sum, map_mul]
      show Wd D _ _ (Wd D _ _ _) = gamA ψ (w • incM D N N' x) (incM D N N' y) • Wd D _ _ _
      rw [h', h])
    (fun x m hm => hdense x m hm)
    (fun v => by
      obtain ⟨m, hm, hv⟩ := v.2.2
      refine ⟨m, hm, ?_⟩
      rintro z ⟨a, ha, hz⟩
      obtain ⟨z', rfl, rfl⟩ := exists_div D hm z a hz
      apply Subtype.ext
      show Wd D _ (pt D _ δ (m • z')) _ = _
      rw [pt_nsmul]
      exact hv _ ((hrat z').1 ha))
  refine ⟨w, gamA ψ, WA, ⟨fun r => ?_, hw, hl, hr, halt, hadj, fun v => ?_, h2⟩, hsd, hinv, fun z F => ?_, h3⟩
  · apply RingOfIntegers.ext
    rw [coe_sgO, coe_sgO, conjE_conjE]
  · have := h1 0
    rw [map_zero] at this
    rw [this]
    apply Subtype.ext
    show Wd D _ (pt D _ δ 0) _ = _
    rw [pt_zero, wd_at_zero]
  · rw [← incM_apply, h1]
    rfl

end GlobalTheory.FinWeil.Model
