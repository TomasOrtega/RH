import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormaliserCore
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsTransportAdelicCorrection
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryGroupConjugateTransposeMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarComplementFrameDiagModConductorStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegerSubConjNotMemSelfConjugatePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GenusTypePlacesPairwiseNotConjugateStatement

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis Formalism.UG
open Formalism.L2.SG.Pf.unitaryCongruence
open scoped TensorProduct

namespace GlobalTheory.LevNorm

attribute [local instance] Formalism.BasicNotions.Host.cmStar kField

/- English proof (translation)
Establish `key : ∀ (J : Matrix (Fin n) (Fin n) A) (β w : GL (Fin n) A), w ∈ UJ σ J → β⁻¹ * w * β ∈ UJ σ (cT σ (β : Matrix (Fin n) (Fin n) A) * J * (β : Matrix (Fin n) (Fin n) A))` using `fun J β w h => by show cT σ ((β⁻¹).1 * w.1 * β.1) * _ * ((β⁻¹).1 * w.1 * β.1) = _`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [cT_mul, Matrix.mul_assoc]`. Use `_ = _ := by rw [Units.mul_inv, cT_one, Matrix.one_mul, Matrix.mul_one, show cT σ w.1 * J * w.1 = J from h]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Use `key _ β⁻¹ w h` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Use `this using 2` and compare the differences between its conclusion and the goal. Combine the equalities or inequalities in the displayed calculation.

Introduce `h`. Use `key J β _ h` as an intermediate fact. Rewrite `this` using `[show β⁻¹ * (β * w * β⁻¹) * β = w by group]`. Then use the resulting hypothesis.
-/
theorem mem_UJ_conj {A : Type} [CommRing A] (σ : A →+* A) {n : ℕ} (J : Matrix (Fin n) (Fin n) A) (β w : GL (Fin n) A) :
    w ∈ UJ σ (cT σ (β : Matrix (Fin n) (Fin n) A) * J * (β : Matrix (Fin n) (Fin n) A)) ↔ β * w * β⁻¹ ∈ UJ σ J := by
  have key : ∀ (J : Matrix (Fin n) (Fin n) A) (β w : GL (Fin n) A), w ∈ UJ σ J →
      β⁻¹ * w * β ∈ UJ σ (cT σ (β : Matrix (Fin n) (Fin n) A) * J * (β : Matrix (Fin n) (Fin n) A)) := fun J β w h => by
    show cT σ ((β⁻¹).1 * w.1 * β.1) * _ * ((β⁻¹).1 * w.1 * β.1) = _
    calc _ = cT σ β.1 * (cT σ w.1 * (cT σ (β.1 * (β⁻¹).1) * J * (β.1 * (β⁻¹).1)) * w.1) * β.1 := by
          simp only [cT_mul, Matrix.mul_assoc]
      _ = _ := by rw [Units.mul_inv, cT_one, Matrix.one_mul, Matrix.mul_one, show cT σ w.1 * J * w.1 = J from h]
  constructor
  · intro h
    have := key _ β⁻¹ w h
    rw [inv_inv] at this
    convert this using 2
    calc J = cT σ (β.1 * (β⁻¹).1) * J * (β.1 * (β⁻¹).1) := by rw [Units.mul_inv, cT_one, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [cT_mul, Matrix.mul_assoc]
  · intro h
    have := key J β _ h
    rwa [show β⁻¹ * (β * w * β⁻¹) * β = w by group] at this

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem frGL_eq (I : AutInst) (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) (x : GL (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)) :
    frGL β x = β * bc (Formalism.L2.Herm.intAf I.F I.E).subtype x * β⁻¹ := rfl

/- English proof (translation)
Take `⟨G, hG⟩` from `GlobalTheory.T.unitary_group_conjugate_transpose_matrix I β hβ`. Establish `hσ` using `sigA_sigA I`. Establish `hS : ∀ s ∈ Formalism.L2.Herm.intAf I.F I.E, sigA I s ∈ Formalism.L2.Herm.intAf I.F I.E` using `fun s hs => sigA_mem I hs`. Establish `hJ : cT (sigA I) (I.J.map (inclE (F` using `I.F) (Formalism.MainNotions.S.Af I.F))) = I.J.map (inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) := by`. Use extensionality with `i j`.

Conclude with `(sigA_inclE I _).trans (congrArg _ (congrFun (congrFun I.J_herm i) j))`. Establish `hcc : ∀ M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), cT (sigA I) (cT (sigA I) M) = M` using `fun M => by`. Use extensionality with `i j`. Conclude with `hσ _`. Establish `hU : ∀ w, w ∈ UJ (sigA I) ((bc (Formalism.L2.Herm.intAf I.F I.E).subtype G).1) ↔ β * w * β⁻¹ ∈ UPts I.cm.sig I.J (Formalism.MainNotions.S.Af I.F)` using `fun w => by rw [hG]; exact mem_UJ_conj _ _ _ _`.

Establish `keeps : ∀ y : I.Gf, (∀ x ∈ K, y * x * y⁻¹ ∈ K ∧ χ (y * x * y⁻¹) = χ x) → Keeps (fun Q : Pl I.E => resS I.F Q) (sigA I) ρ κ G Pg ψ a (β⁻¹ * y.1 * β)`. Introduce `y hy x hx`. Set `X : I.Gf` to `⟨frGL β x, (hU _).1 hx.1⟩`. Establish `hX : X ∈ K` using `(hK X).1.2 ⟨⟨x, rfl⟩, fun PP hPP => by show redFn β PP (frGL β x) ∈ _`. Rewrite using `[redFn_frGL]`.

Conclude with `hx.2 PP hPP⟩`. Take `⟨h1, h2⟩` from `hy X hX`. Take `⟨⟨x', hx'⟩, h3⟩` from `(hK _).1.1 h1`. Rewrite `h2` using `[(hK _).2 h1, (hK _).2 hX, ← hx']`. Rewrite `h3` using `[← hx']`.

Use `⟨x', ?_, ⟨(hU _).2 (by rw [← frGL_eq, hx']; exact (y * X * y⁻¹).2), fun PP hPP => ?_⟩, ?_⟩` and prove the remaining obligations. Establish `e : β * bc (Formalism.L2.Herm.intAf I.F I.E).subtype x' * β⁻¹ = y.1 * (β * bc (Formalism.L2.Herm.intAf I.F I.E).subtype x * β⁻¹) * y.1⁻¹` using `hx'`. Combine the equalities or inequalities in the displayed calculation. Use `h3 PP hPP` as an intermediate fact. Rewrite `this` using `[redFn_frGL]`. Then use the resulting hypothesis.

Simplify using `only [X, redFn_frGL] at h2`. Conclude with `h2`. Take `⟨z, c, x₁, hz, hc, hsup, hm, hred⟩` from `normaliser_core Z hσ hS hn hρ hκ (by rw [hG, cT_mul, cT_mul, hcc, hJ, Matrix.mul_assoc]) hT hun hψ ha (m := β⁻¹ * y.1 * β) ((hU _).2 (by rw [show β * (β⁻¹ * y.1 * β) * β⁻¹ = y.1 by group]; exact y.2)) (keeps y fun x hx => ⟨(hy x).1.1 hx, (hy x).2 hx⟩) (by`. Use `keeps y⁻¹ fun x hx => by` as an intermediate fact. Establish `e : y * (y⁻¹ * x * y⁻¹⁻¹) * y⁻¹ = x` using `by group`.

Establish `h1 : y⁻¹ * x * y⁻¹⁻¹ ∈ K` using `(hy _).1.2 (by rw [e]; exact hx)`. Conclude with `⟨h1, by rw [← (hy _).2 h1, e]⟩`. Rewrite using `[show β⁻¹ * (y⁻¹).1 * β = (β⁻¹ * y.1 * β)⁻¹ by rw [Subgroup.coe_inv]; group] at this)` and apply the resulting hypothesis. Establish `hz' : sigA I z * z = 1` using `by rw [mul_comm, hz]`. Set `zG : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)` to `⟨z • 1, sigA I z • 1, by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hz, Matrix.one_mul, one_smul], by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hz', Matrix.one_mul, one_smul]⟩`.

Establish `hzc : ∀ w, zG * w = w * zG` using `fun w => Units.ext (by show z • 1 * w.1 = w.1 * z • 1`. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one])`. Establish `hzU : zG ∈ UPts I.cm.sig I.J (Formalism.MainNotions.S.Af I.F)`. Establish `e : cT (sigA I) (z • (1 : Matrix (Fin I.n) (Fin I.n) _)) = sigA I z • 1`. Use extensionality with `i j`.

Simplify using `only [cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_mul, eq_comm (a := i)]`. Apply the tactic sequence `split_ifs <;> simp`. Use `show cT (sigA I) (z • 1) * _ * (z • 1) = _`. Rewrite using `[e, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hz, one_smul]`. Establish `hm' : β⁻¹ * y.1 * β = zG * bc (Formalism.L2.Herm.intAf I.F I.E).subtype x₁` using `Units.ext (by`.

Rewrite using `[hm]`. Use `show _ = z • 1 * _`. Rewrite using `[Matrix.smul_mul, Matrix.one_mul])`. Establish `hpg : ∀ PP ∈ Pg, (g : kP PP) = 0` using `fun PP hPP => by`. Rewrite using `[← map_natCast (Ideal.Quotient.mk PP.asIdeal)]`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (hdiv PP hPP)`. Use `⟨⟨zG, hzU⟩, Subgroup.mem_center_iff.2 fun w => Subtype.ext (hzc _).symm, c, Subtype.ext hc, fun N hN => ?_, fun d x hx hd => ?_⟩` and prove the remaining obligations. Establish `hN' : ∀ Q ∈ Pg, (N : kP Q) ≠ 0` using `fun Q hQ h0 => by`. Take `⟨u, v, huv⟩` from `(Nat.isCoprime_iff_coprime.2 hN).intCast (R := kP Q)`. Rewrite `huv` using `[Int.cast_natCast, Int.cast_natCast, h0, hpg Q hQ, mul_zero, mul_zero, add_zero]`.

Conclude with `zero_ne_one huv`. Establish `hN0 : (N : I.F) ≠ 0` using `Nat.cast_ne_zero.2 fun e => hg (by rwa [e, Nat.coprime_zero_left] at hN)`. Set `b : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F` to `algebraMap I.F _ (N : I.F)⁻¹`. Establish `hb : (N : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * b = 1`. Rewrite using `[← map_natCast (algebraMap I.F (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), ← map_mul, mul_inv_cancel₀ hN0, map_one]`.

Establish `hb' : (N : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * sigA I b = 1`. Simplify using `using congrArg (sigA I) hb`. Establish `key : ∀ b', (N : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * b' = 1 → ∀ Q ∈ Pg, Z.p Q b' ∈ Z.O Q` using `fun b' h Q hQ => by`. Establish `h1` using `(Z.r_ker Q N).not.1 (by rw [map_natCast]; exact hN' Q hQ)`. Establish `h2` using `congrArg (fun t => (Z.O Q).valuation (Z.p Q t)) h`.

Simplify using `only [map_mul, map_one] at h2`. Rewrite using `[← ValuationSubring.valuation_le_one_iff, ← h2]`. Conclude with `le_mul_of_one_le_left' (not_lt.1 h1)`. Use `⟨_, hsup b fun Q hQ => ⟨key b hb Q hQ, key _ hb' Q hQ⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_left_comm, hb, mul_one]`.

Establish `e : ((d⁻¹ * ((⟨zG, hzU⟩ : I.Gf)⁻¹ * y) : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) = frGL β (x⁻¹ * x₁)` using `by show d.1⁻¹ * (zG⁻¹ * y.1) = _`. Rewrite using `[map_mul, map_inv, hx, frGL_eq]`. Use `congr 1`. Combine the equalities or inequalities in the displayed calculation. Use `(hK _).1.2 ⟨⟨_, e.symm⟩, fun PP hPP => ?_⟩` and prove the remaining obligations.

Take `⟨h, hh, e2⟩` from `hred PP hPP`. Establish `e3 : (bc (resS I.F PP) x).1 = midDiag I.n ρ κ 1 (resS I.F PP c)`. Use extensionality with `i j`. Use `map_eq_zero_of_zmod I (resS I.F PP) (hpg PP hPP) (hd i j)` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply, map_sub, sub_eq_zero]`.

Use `this.trans ?_` and prove the remaining obligations. Simplify using `only [midDiag, Matrix.diagonal_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `e4 : bc (resS I.F PP) x₁ = bc (resS I.F PP) x * h` using `Units.ext (by rw [Units.val_mul, e3]; exact e2)`. Rewrite using `[e, redFn_frGL, map_mul, map_inv, e4, inv_mul_cancel_left]`.

Conclude with `hh`.
-/
theorem frame_normaliser (I : AutInst) (g : ℕ) (hg : g ≠ 1) {ρ κ : ℕ} (hn : I.n = 2 * ρ + κ + 1) (hρ : 1 ≤ ρ) (hκ : 2 ≤ κ)
    (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) (hβ : IsFrame β I.L)
    (Z : PlaceSys (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (Formalism.L2.Herm.intAf I.F I.E) (Pl I.E) (fun Q => kP Q) (fun Q => resS I.F Q))
    (Pg : Finset (Pl I.E)) (hdiv : ∀ PP ∈ Pg, (g : 𝓞 I.E) ∈ PP.asIdeal)
    (hT : ∀ Q ∈ Pg, ∀ Q' ∈ Pg, sigA I (Z.e Q) ≠ Z.e Q')
    (hun : ∀ Q, sigA I (Z.e Q) = Z.e Q → ∃ δ : Formalism.L2.Herm.intAf I.F I.E, resS I.F Q (δ - sigInt I δ) ≠ 0)
    (ψ : ∀ PP : Pl I.E, AddChar (kP PP) ℂ) (hψ : ∀ Q ∈ Pg, ψ Q ≠ 1) (a : ∀ PP : Pl I.E, Fin I.n → Fin I.n → kP PP)
    (ha : ∀ PP ∈ Pg, ∀ i j, symEdge ρ κ i j → a PP i j ≠ 0) (K : Set I.Gf) (χ : I.Gf → ℂ)
    (hK : ∀ x : I.Gf, (x ∈ K ↔ (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) ∈ St β ∧
          ∀ PP ∈ Pg, redFn β PP x ∈ unipSym (kP PP) I.n ρ κ) ∧
        (x ∈ K → χ x = ∏ PP ∈ Pg, ψ PP (edgeVal ρ κ (a PP) (redFn β PP x))))
    (y : I.Gf) (hy : ∀ x, (x ∈ K ↔ y * x * y⁻¹ ∈ K) ∧ (x ∈ K → χ (y * x * y⁻¹) = χ x)) :
    ∃ z ∈ Subgroup.center I.Gf, ∃ c : Formalism.L2.Herm.intAf I.F I.E, c * sigInt I c = 1 ∧
      (∀ N : ℕ, Nat.Coprime N g → ZMod' I N (1 - c.1)) ∧
      ∀ (d : I.Gf) (x : GL (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)),
        frGL β x = (d : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) →
        (∀ i j, ZMod' I g (((x : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)) - midDiag I.n ρ κ 1 c) i j).1) →
        d⁻¹ * (z⁻¹ * y) ∈ K := by
  obtain ⟨G, hG⟩ := GlobalTheory.T.unitary_group_conjugate_transpose_matrix I β hβ
  have hσ := sigA_sigA I
  have hS : ∀ s ∈ Formalism.L2.Herm.intAf I.F I.E, sigA I s ∈ Formalism.L2.Herm.intAf I.F I.E := fun s hs => sigA_mem I hs
  have hJ : cT (sigA I) (I.J.map (inclE (F := I.F) (Formalism.MainNotions.S.Af I.F))) = I.J.map (inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) := by
    ext i j
    exact (sigA_inclE I _).trans (congrArg _ (congrFun (congrFun I.J_herm i) j))
  have hcc : ∀ M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), cT (sigA I) (cT (sigA I) M) = M := fun M => by
    ext i j
    exact hσ _
  have hU : ∀ w, w ∈ UJ (sigA I) ((bc (Formalism.L2.Herm.intAf I.F I.E).subtype G).1) ↔ β * w * β⁻¹ ∈ UPts I.cm.sig I.J (Formalism.MainNotions.S.Af I.F) :=
    fun w => by rw [hG]; exact mem_UJ_conj _ _ _ _
  have keeps : ∀ y : I.Gf, (∀ x ∈ K, y * x * y⁻¹ ∈ K ∧ χ (y * x * y⁻¹) = χ x) →
      Keeps (fun Q : Pl I.E => resS I.F Q) (sigA I) ρ κ G Pg ψ a (β⁻¹ * y.1 * β) := by
    intro y hy x hx
    let X : I.Gf := ⟨frGL β x, (hU _).1 hx.1⟩
    have hX : X ∈ K := (hK X).1.2 ⟨⟨x, rfl⟩, fun PP hPP => by
      show redFn β PP (frGL β x) ∈ _
      rw [redFn_frGL]; exact hx.2 PP hPP⟩
    obtain ⟨h1, h2⟩ := hy X hX
    obtain ⟨⟨x', hx'⟩, h3⟩ := (hK _).1.1 h1
    rw [(hK _).2 h1, (hK _).2 hX, ← hx'] at h2
    rw [← hx'] at h3
    refine ⟨x', ?_, ⟨(hU _).2 (by rw [← frGL_eq, hx']; exact (y * X * y⁻¹).2), fun PP hPP => ?_⟩, ?_⟩
    · have e : β * bc (Formalism.L2.Herm.intAf I.F I.E).subtype x' * β⁻¹ =
        y.1 * (β * bc (Formalism.L2.Herm.intAf I.F I.E).subtype x * β⁻¹) * y.1⁻¹ := hx'
      calc _ = β⁻¹ * (β * bc (Formalism.L2.Herm.intAf I.F I.E).subtype x' * β⁻¹) * β := by group
        _ = _ := by rw [e]; group
    · have := h3 PP hPP
      rwa [redFn_frGL] at this
    · simp only [X, redFn_frGL] at h2
      exact h2
  obtain ⟨z, c, x₁, hz, hc, hsup, hm, hred⟩ := normaliser_core Z hσ hS hn hρ hκ
    (by rw [hG, cT_mul, cT_mul, hcc, hJ, Matrix.mul_assoc]) hT hun hψ ha (m := β⁻¹ * y.1 * β)
    ((hU _).2 (by rw [show β * (β⁻¹ * y.1 * β) * β⁻¹ = y.1 by group]; exact y.2))
    (keeps y fun x hx => ⟨(hy x).1.1 hx, (hy x).2 hx⟩)
    (by
      have := keeps y⁻¹ fun x hx => by
        have e : y * (y⁻¹ * x * y⁻¹⁻¹) * y⁻¹ = x := by group
        have h1 : y⁻¹ * x * y⁻¹⁻¹ ∈ K := (hy _).1.2 (by rw [e]; exact hx)
        exact ⟨h1, by rw [← (hy _).2 h1, e]⟩
      rwa [show β⁻¹ * (y⁻¹).1 * β = (β⁻¹ * y.1 * β)⁻¹ by rw [Subgroup.coe_inv]; group] at this)
  have hz' : sigA I z * z = 1 := by rw [mul_comm, hz]
  let zG : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) := ⟨z • 1, sigA I z • 1,
    by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hz, Matrix.one_mul, one_smul],
    by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hz', Matrix.one_mul, one_smul]⟩
  have hzc : ∀ w, zG * w = w * zG := fun w => Units.ext (by
    show z • 1 * w.1 = w.1 * z • 1
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one])
  have hzU : zG ∈ UPts I.cm.sig I.J (Formalism.MainNotions.S.Af I.F) := by
    have e : cT (sigA I) (z • (1 : Matrix (Fin I.n) (Fin I.n) _)) = sigA I z • 1 := by
      ext i j
      simp only [cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_mul, eq_comm (a := i)]
      split_ifs <;> simp
    show cT (sigA I) (z • 1) * _ * (z • 1) = _
    rw [e, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hz, one_smul]
  have hm' : β⁻¹ * y.1 * β = zG * bc (Formalism.L2.Herm.intAf I.F I.E).subtype x₁ := Units.ext (by
    rw [hm]
    show _ = z • 1 * _
    rw [Matrix.smul_mul, Matrix.one_mul])
  have hpg : ∀ PP ∈ Pg, (g : kP PP) = 0 := fun PP hPP => by
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hdiv PP hPP)
  refine ⟨⟨zG, hzU⟩, Subgroup.mem_center_iff.2 fun w => Subtype.ext (hzc _).symm, c, Subtype.ext hc, fun N hN => ?_,
    fun d x hx hd => ?_⟩
  · have hN' : ∀ Q ∈ Pg, (N : kP Q) ≠ 0 := fun Q hQ h0 => by
      obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.2 hN).intCast (R := kP Q)
      rw [Int.cast_natCast, Int.cast_natCast, h0, hpg Q hQ, mul_zero, mul_zero, add_zero] at huv
      exact zero_ne_one huv
    have hN0 : (N : I.F) ≠ 0 := Nat.cast_ne_zero.2 fun e => hg (by rwa [e, Nat.coprime_zero_left] at hN)
    let b : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F := algebraMap I.F _ (N : I.F)⁻¹
    have hb : (N : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * b = 1 := by
      rw [← map_natCast (algebraMap I.F (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), ← map_mul, mul_inv_cancel₀ hN0, map_one]
    have hb' : (N : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * sigA I b = 1 := by
      simpa using congrArg (sigA I) hb
    have key : ∀ b', (N : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * b' = 1 → ∀ Q ∈ Pg, Z.p Q b' ∈ Z.O Q := fun b' h Q hQ => by
      have h1 := (Z.r_ker Q N).not.1 (by rw [map_natCast]; exact hN' Q hQ)
      have h2 := congrArg (fun t => (Z.O Q).valuation (Z.p Q t)) h
      simp only [map_mul, map_one] at h2
      rw [← ValuationSubring.valuation_le_one_iff, ← h2]
      exact le_mul_of_one_le_left' (not_lt.1 h1)
    refine ⟨_, hsup b fun Q hQ => ⟨key b hb Q hQ, key _ hb' Q hQ⟩, ?_⟩
    rw [mul_left_comm, hb, mul_one]
  · have e : ((d⁻¹ * ((⟨zG, hzU⟩ : I.Gf)⁻¹ * y) : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) = frGL β (x⁻¹ * x₁) := by
      show d.1⁻¹ * (zG⁻¹ * y.1) = _
      rw [map_mul, map_inv, hx, frGL_eq]
      congr 1
      calc _ = zG⁻¹ * β * (β⁻¹ * y.1 * β) * β⁻¹ := by group
        _ = zG⁻¹ * (β * zG) * bc (Formalism.L2.Herm.intAf I.F I.E).subtype x₁ * β⁻¹ := by rw [hm']; group
        _ = _ := by rw [← hzc]; group
    refine (hK _).1.2 ⟨⟨_, e.symm⟩, fun PP hPP => ?_⟩
    obtain ⟨h, hh, e2⟩ := hred PP hPP
    have e3 : (bc (resS I.F PP) x).1 = midDiag I.n ρ κ 1 (resS I.F PP c) := by
      ext i j
      have := map_eq_zero_of_zmod I (resS I.F PP) (hpg PP hPP) (hd i j)
      rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
      refine this.trans ?_
      simp only [midDiag, Matrix.diagonal_apply]
      split_ifs <;> simp
    have e4 : bc (resS I.F PP) x₁ = bc (resS I.F PP) x * h := Units.ext (by rw [Units.val_mul, e3]; exact e2)
    rw [e, redFn_frGL, map_mul, map_inv, e4, inv_mul_cancel_left]
    exact hh

/- English proof (translation)
The claim follows from `Subtype.ext ((sigA_inclE I _).trans (congrArg (inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) h.symm))`.
-/
theorem sigInt_oToS (I : AutInst) {c c' : 𝓞 I.E} (h : (c' : I.E) = star (c : I.E)) :
    sigInt I (oToS I.F I.E c) = oToS I.F I.E c' :=
  Subtype.ext ((sigA_inclE I _).trans (congrArg (inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) h.symm))

/- English proof (translation)
Introduce `c hc`. Take `⟨c', hc'⟩` from `star_intOE I (a := (c : I.E)) ⟨c, rfl⟩`. Use `⟨c', ?_, hc'⟩` and prove the remaining obligations. Establish `h1 : resS I.F Q' (sigInt I (oToS I.F I.E c)) = 0` using `Z.r_conj (σ := sigA I) (sigA_sigA I) (fun s hs => sigA_mem I hs) h (oToS I.F I.E c) ((resS_oToS Q c).trans (Ideal.Quotient.eq_zero_iff_mem.2 hc))`. Rewrite `h1` using `[sigInt_oToS I hc', resS_oToS]`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 h1`.
-/
theorem conj_of_idem (I : AutInst)
    (Z : PlaceSys (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (Formalism.L2.Herm.intAf I.F I.E) (Pl I.E) (fun Q => kP Q) (fun Q => resS I.F Q))
    {Q Q' : Pl I.E} (h : sigA I (Z.e Q) = Z.e Q') : ∀ c ∈ Q.asIdeal, ∃ c' ∈ Q'.asIdeal, (c' : I.E) = star (c : I.E) := by
  intro c hc
  obtain ⟨c', hc'⟩ := star_intOE I (a := (c : I.E)) ⟨c, rfl⟩
  refine ⟨c', ?_, hc'⟩
  have h1 : resS I.F Q' (sigInt I (oToS I.F I.E c)) = 0 :=
    Z.r_conj (σ := sigA I) (sigA_sigA I) (fun s hs => sigA_mem I hs) h (oToS I.F I.E c)
      ((resS_oToS Q c).trans (Ideal.Quotient.eq_zero_iff_mem.2 hc))
  rw [sigInt_oToS I hc', resS_oToS] at h1
  exact Ideal.Quotient.eq_zero_iff_mem.1 h1

/- English proof (translation)
Take `⟨δ, δ', h1, h2⟩` from `h`. Use `⟨oToS I.F I.E δ, fun h0 => h2 ?_⟩` and prove the remaining obligations. Rewrite `h0` using `[sigInt_oToS I h1, ← map_sub, resS_oToS]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 h0`.
-/
theorem exists_res_ne (I : AutInst) (Q : Pl I.E) (h : ∃ δ δ' : 𝓞 I.E, (δ' : I.E) = star (δ : I.E) ∧ δ - δ' ∉ Q.asIdeal) :
    ∃ δ : Formalism.L2.Herm.intAf I.F I.E, resS I.F Q (δ - sigInt I δ) ≠ 0 := by
  obtain ⟨δ, δ', h1, h2⟩ := h
  refine ⟨oToS I.F I.E δ, fun h0 => h2 ?_⟩
  rw [sigInt_oToS I h1, ← map_sub, resS_oToS] at h0
  exact Ideal.Quotient.eq_zero_iff_mem.1 h0

/- English proof (translation)
Substitute `hI hg'` using the available equality. Take `⟨Pg, hPg⟩` from `GlobalTheory.Core.Mi.PinModel.exists_isTypePlaces (D := D)`. Establish `hnc` using `GlobalTheory.T.genus_type_places_pairwise_not_conjugate D Pg hPg`. Establish `key : ∀ PP : Pl D.host.E, ∃ ψ : AddChar (kP PP) ℂ, ψ ≠ 1` using `fun PP => by`. Take `⟨ψ, hψ⟩` from `(AddChar.exists_apply_ne_zero (α := kP PP) (a := 1)).2 one_ne_zero`.

Conclude with `⟨ψ, fun h => hψ (by rw [h]; rfl)⟩`. Use `choose ψ0 hψ0 using key`. Establish `hψ : IsGenericPsi Pg ψ0` using `fun PP _ => hψ0 PP`. Establish `hg : D.host.g 0 * D.host.g 1 ≠ 0` using `mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero`. Establish `hg1 : D.host.g 0 * D.host.g 1 ≠ 1` using `fun e => (D.host.g_prime 0).ne_one (Nat.eq_one_of_mul_eq_one_right e)`.

Establish `hn' : (instOf D).n = 2 * D.R.rS + D.R.k + 1`. Rewrite using `[hn]`. Take `⟨c, hc⟩` from `D.R.m_even`. Use `D.R.two_le_m` as an intermediate fact. Unfold `Ranks.r Ranks.rS`.

Use linear arithmetic over natural numbers and integers. Establish `hk : 2 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Take `⟨hs1, hs2⟩` from `GlobalTheory.T.flagVec_mem_Lf_and_inMod (instOf D) _ e0 f0 z0 bw bwd ew hF hn'`. Take `⟨β₀, hβ₀⟩` from `GlobalTheory.T.exists_latticeFrame_lifting_spanning_vectors_mod D _ hg _ hs1 hs2`. Establish `hN : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (∀ PP ∈ Pg, resS D.host.F PP s = 0 ∧ resS D.host.F PP (sigInt (instOf D) s) = 0) → ZMod' (instOf D) (D.host.g 0 * D.host.g 1) s.1`.

Introduce `s hs`. Use `GlobalTheory.T.integralAdele_congr_zero_of_residues_squarefree (instOf D) _ hg (GlobalTheory.T.typePrimes_product_not_mem_sq_place D) s fun Q hQ => ?_` and prove the remaining obligations. Take `⟨PP, hPP, rfl | h⟩` from `GlobalTheory.T.typePrimePlace_mem_or_conj_genusTypePlaceSet D Pg hPg Q hQ`. Conclude with `(hs _ hPP).1`. Conclude with `(h s).2 (hs _ hPP).2`.

Take `⟨a₁, a₂, ha, hχ⟩` from `GlobalTheory.T.character_residueFields_eq_prod_genericShift D.host.E (Formalism.L2.Herm.intAf D.host.F D.host.E) Pg (fun PP => resS D.host.F PP) (fun PP => (resS D.host.F PP).comp (sigInt (instOf D))) (fun s => star (psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1))) ψ0 hψ ( …`. Take `⟨t, ht, e⟩` from `hN s hs`. Establish `: divN (instOf D) (D.host.g 0 * D.host.g 1) s.1 = t` using `(congrArg _ e).trans (Formalism.L2.SG.Pf.unitaryCongruence.divN_gmul _ _ hg t)`. Use `show star (psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1)) = 1`. Rewrite using `[this, hint t ht, star_one])`.

Use the proof step `(GlobalTheory.T.exists_integralAdele_prescribed_residues_and_conj D Pg hnc)`. Use the proof step `(GlobalTheory.T.residueSupport_single_place_to_conjugatePair_position D Pg hPg.1 hnc (fun s => star (psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1)) ≠ 1) fun Q hQ => by`. Take `⟨s, h1, h2⟩` from `GlobalTheory.T.exists_finiteAdditiveChar_ne_one_at_each_prime D psiEf hadd hint hrat Q hQ`. Conclude with `⟨s, h1, fun h => h2 (by simpa using congrArg star h)⟩)`. Take `⟨a, ha1, hK⟩` from `read_in_frame (instOf D) _ hg e0 f0 z0 bw bwd ew hF hn' β₀ hβ₀ Pg hPg.1 hN psiEf hadd hint ψ0 a₁ a₂ ha hχ`.

Conclude with `⟨β₀, hβ₀, frame_normaliser (instOf D) _ hg1 hn' hρ hk β₀ hβ₀.1 (adPlaces D) Pg hPg.1 (fun Q hQ Q' hQ' h => hnc Q hQ Q' hQ' (conj_of_idem (instOf D) (adPlaces D) h)) (fun Q h => exists_res_ne (instOf D) Q (GlobalTheory.T.exists_integer_sub_conj_notMem_self_conjugate_place D Q (con …`.
-/
theorem inst_normaliser (D : D7) (hρ : 1 ≤ D.R.rS) (I : AutInst) (hI : I = instOf D) (g : ℕ) (hg' : g = D.host.g 0 * D.host.g 1)
    (e0 f0 : Fin D.R.rS → VA I) (z0 : VA I) (bw bwd : Fin D.R.k → VA I) (ew : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)
    (hF : IsRefFrame I g e0 f0 z0 bw bwd ew) (hn : I.n = D.R.r) (psiEf : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F → ℂ)
    (hadd : ∀ x y, psiEf (x + y) = psiEf x * psiEf y) (hint : ∀ x ∈ IntAf I.F I.E, psiEf x = 1)
    (hrat : ∀ x : I.E, psiEf (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) x) * psiEinf I x = 1) (y : I.Gf)
    (hy : ∀ x, (x ∈ K2set I g e0 z0 bw ↔ y * x * y⁻¹ ∈ K2set I g e0 z0 bw) ∧ (x ∈ K2set I g e0 z0 bw →
      star (chi2f I psiEf g e0 f0 z0 bw bwd (y * x * y⁻¹)) = star (chi2f I psiEf g e0 f0 z0 bw bwd x))) :
    ∃ β, IsLiftFrame I g (flagVec e0 f0 z0 bw bwd) β ∧
      ∃ z ∈ Subgroup.center I.Gf, ∃ c : Formalism.L2.Herm.intAf I.F I.E, c * sigInt I c = 1 ∧
      (∀ N : ℕ, Nat.Coprime N g → ZMod' I N (1 - c.1)) ∧
      ∀ (d : I.Gf) (x : GL (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)),
        frGL β x = (d : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) →
        (∀ i j, ZMod' I g (((x : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)) - midDiag I.n D.R.rS D.R.k 1 c) i j).1) →
        d⁻¹ * (z⁻¹ * y) ∈ K2set I g e0 z0 bw := by
  subst hI hg'
  obtain ⟨Pg, hPg⟩ := GlobalTheory.Core.Mi.PinModel.exists_isTypePlaces (D := D)
  have hnc := GlobalTheory.T.genus_type_places_pairwise_not_conjugate D Pg hPg
  have key : ∀ PP : Pl D.host.E, ∃ ψ : AddChar (kP PP) ℂ, ψ ≠ 1 := fun PP => by
    obtain ⟨ψ, hψ⟩ := (AddChar.exists_apply_ne_zero (α := kP PP) (a := 1)).2 one_ne_zero
    exact ⟨ψ, fun h => hψ (by rw [h]; rfl)⟩
  choose ψ0 hψ0 using key
  have hψ : IsGenericPsi Pg ψ0 := fun PP _ => hψ0 PP
  have hg : D.host.g 0 * D.host.g 1 ≠ 0 := mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  have hg1 : D.host.g 0 * D.host.g 1 ≠ 1 := fun e => (D.host.g_prime 0).ne_one (Nat.eq_one_of_mul_eq_one_right e)
  have hn' : (instOf D).n = 2 * D.R.rS + D.R.k + 1 := by
    rw [hn]
    obtain ⟨c, hc⟩ := D.R.m_even
    have := D.R.two_le_m
    unfold Ranks.r Ranks.rS
    omega
  have hk : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  obtain ⟨hs1, hs2⟩ := GlobalTheory.T.flagVec_mem_Lf_and_inMod (instOf D) _ e0 f0 z0 bw bwd ew hF hn'
  obtain ⟨β₀, hβ₀⟩ := GlobalTheory.T.exists_latticeFrame_lifting_spanning_vectors_mod D _ hg _ hs1 hs2
  have hN : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E,
      (∀ PP ∈ Pg, resS D.host.F PP s = 0 ∧ resS D.host.F PP (sigInt (instOf D) s) = 0) →
      ZMod' (instOf D) (D.host.g 0 * D.host.g 1) s.1 := by
    intro s hs
    refine GlobalTheory.T.integralAdele_congr_zero_of_residues_squarefree (instOf D) _ hg (GlobalTheory.T.typePrimes_product_not_mem_sq_place D) s fun Q hQ => ?_
    obtain ⟨PP, hPP, rfl | h⟩ := GlobalTheory.T.typePrimePlace_mem_or_conj_genusTypePlaceSet D Pg hPg Q hQ
    · exact (hs _ hPP).1
    · exact (h s).2 (hs _ hPP).2
  obtain ⟨a₁, a₂, ha, hχ⟩ := GlobalTheory.T.character_residueFields_eq_prod_genericShift D.host.E (Formalism.L2.Herm.intAf D.host.F D.host.E) Pg (fun PP => resS D.host.F PP)
    (fun PP => (resS D.host.F PP).comp (sigInt (instOf D)))
    (fun s => star (psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1))) ψ0 hψ
    (fun s t => (congrArg (fun z => star (psiEf z))
        (Formalism.L2.SG.Pf.unitaryCongruence.divN_add (instOf D) (D.host.g 0 * D.host.g 1) s.1 t.1)).trans (by rw [hadd, star_mul']))
    (fun s hs => by
      obtain ⟨t, ht, e⟩ := hN s hs
      have : divN (instOf D) (D.host.g 0 * D.host.g 1) s.1 = t :=
        (congrArg _ e).trans (Formalism.L2.SG.Pf.unitaryCongruence.divN_gmul _ _ hg t)
      show star (psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1)) = 1
      rw [this, hint t ht, star_one])
    (GlobalTheory.T.exists_integralAdele_prescribed_residues_and_conj D Pg hnc)
    (GlobalTheory.T.residueSupport_single_place_to_conjugatePair_position D Pg hPg.1 hnc (fun s => star (psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1)) ≠ 1) fun Q hQ => by
      obtain ⟨s, h1, h2⟩ := GlobalTheory.T.exists_finiteAdditiveChar_ne_one_at_each_prime D psiEf hadd hint hrat Q hQ
      exact ⟨s, h1, fun h => h2 (by simpa using congrArg star h)⟩)
  obtain ⟨a, ha1, hK⟩ := read_in_frame (instOf D) _ hg e0 f0 z0 bw bwd ew hF hn' β₀ hβ₀ Pg hPg.1 hN psiEf hadd hint ψ0 a₁ a₂ ha hχ
  exact ⟨β₀, hβ₀, frame_normaliser (instOf D) _ hg1 hn' hρ hk β₀ hβ₀.1 (adPlaces D) Pg hPg.1
    (fun Q hQ Q' hQ' h => hnc Q hQ Q' hQ' (conj_of_idem (instOf D) (adPlaces D) h))
    (fun Q h => exists_res_ne (instOf D) Q (GlobalTheory.T.exists_integer_sub_conj_notMem_self_conjugate_place D Q (conj_of_idem (instOf D) (adPlaces D) h))) ψ0 hψ a ha1 _
    (fun x => star (chi2f (instOf D) psiEf (D.host.g 0 * D.host.g 1) e0 f0 z0 bw bwd x)) hK y hy⟩

open Formalism.L2.SG.PoincareInHH.PoincareSetting in

/- English proof (translation)
Take `⟨β, hβ, z, hz, c, hc, hs, hd⟩` from `inst_normaliser D hρ X.B.I h X.B.g X.g_eq X.e0 X.f0 X.z0 X.bw X.bwd X.ew (isRefFrame_setting X) X.n_eq X.psiEf X.psiEf_add X.psiEf_int X.psiEf_rat y hy`. Take `⟨w, hw, hw', x, hx, hx'⟩` from `GlobalTheory.T.scalar_complement_frame_diag_mod_conductor D X u β hβ c hc hs`. Use `⟨z, hz, w, hw, hw', _, hd _ x hx hx', ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.mem_center_iff.1 hz]`. Use `group`.
-/
theorem setting_normaliser {D : D7} (X : HidaSetting D) (h : X.B.I = instOf D) (hρ : 1 ≤ D.R.rS) (u : D.what₂.Word) (y : X.B.I.Gf)
    (hy : ∀ x, (x ∈ X.K2 ↔ y * x * y⁻¹ ∈ X.K2) ∧ (x ∈ X.K2 → star (X.chi2 (y * x * y⁻¹)) = star (X.chi2 x))) :
    ∃ z ∈ Subgroup.center X.B.I.Gf, ∃ w ∈ Hfin X u, (∀ w' ∈ Hfin X u, w * w' = w' * w) ∧
      ∃ k ∈ X.K2, y = (X.xu u)⁻¹ * w * X.xu u * z * k := by
  obtain ⟨β, hβ, z, hz, c, hc, hs, hd⟩ := inst_normaliser D hρ X.B.I h X.B.g X.g_eq X.e0 X.f0 X.z0 X.bw X.bwd X.ew
    (isRefFrame_setting X) X.n_eq X.psiEf X.psiEf_add X.psiEf_int X.psiEf_rat y hy
  obtain ⟨w, hw, hw', x, hx, hx'⟩ := GlobalTheory.T.scalar_complement_frame_diag_mod_conductor D X u β hβ c hc hs
  refine ⟨z, hz, w, hw, hw', _, hd _ x hx hx', ?_⟩
  rw [Subgroup.mem_center_iff.1 hz]
  group

end GlobalTheory.LevNorm

end
