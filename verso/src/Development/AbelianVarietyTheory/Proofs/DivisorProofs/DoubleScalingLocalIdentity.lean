import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksSubOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairLocalSchwartzAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianSplitSymplecticPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelUnitaryConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticFormUnitaryGroupActionInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepBijectionSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorLocalVanishStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped Matrix
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.DblShape

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Introduce `r hr`. Establish `h : ∀ i j, r • x i j = 0` using `fun i j => by`. Use `congrFun (congrFun (hx r hr) i) j` as an intermediate fact. Simplify using `using this`. Rewrite using `[← mul_smul_comm]`.

Unfold `hTens`. Simplify using `only [Finset.smul_sum, ← smul_mul_assoc, h, zero_mul, Finset.sum_const_zero, mul_zero]`.
-/
theorem at_hTens {σ : E →ₐ[F] E} {v : Pl F} {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α (AE F E))
    (JB : Matrix β β (AE F E)) (x u : Matrix α β (AE F E)) (hx : At (evFin F v) x) :
    At (evFin F v) ((-1 : AE F E) * hTens (cA σ) JA JB x u) := by
  intro r hr
  have h : ∀ i j, r • x i j = 0 := fun i j => by
    have := congrFun (congrFun (hx r hr) i) j
    simpa using this
  rw [← mul_smul_comm]
  unfold hTens
  simp only [Finset.smul_sum, ← smul_mul_assoc, h, zero_mul, Finset.sum_const_zero, mul_zero]

/- English proof (translation)
Take `⟨R, hR0, hR⟩` from `GlobalTheory.RestWitness.exists_rest κ v`. Establish `hΦ : tens (evFin F v) φ R ∈ GlobalTheory.WeilM.schA F κ` using `(hR φ hφ).2`. Establish `himpl` using `hS.impl p u (tens (evFin F v) φ R) hΦ`. Establish `hact : actB (cA σ) p u = u * ((p : GL β (AE F E)) : Matrix β β (AE F E))ᵀ` using `rfl`. Rewrite `himpl` using `[hact]`.

Establish `key : tens (evFin F v) φ₄ R = tens (evFin F v) φ₃ R`. Rewrite using `[← h4 R (hR φ₂ hφ₂), ← h2 R (hR φ hφ), ← himpl, h1 R (hR φ hφ), h3 R (hR φ₁ hφ₁)]`. Use function extensionality and compare the values at `t`. Establish `hz : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (t i))`. Introduce `u' hu'`.

Use function extensionality and compare the values at `i`. Conclude with `GlobalTheory.LatVac.at_liftV v _ u' hu'`. Establish `hRz : R (fun i => GlobalTheory.LatVac.liftV v (t i)) = R 0`. Simplify using `using (hR φ hφ).1 0 _ hz`. Use `congrFun key (fun i => GlobalTheory.LatVac.liftV v (t i))` as an intermediate fact.

Simplify using `only [tens, GlobalTheory.LatVac.evFin_liftV, hRz] at this`. Conclude with `mul_right_cancel₀ hR0 this`.
-/
theorem local_intertw {σ : E →ₐ[F] E} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)} {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ}
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (omd : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ))
    (hS : IsUSplitting (adeleClass F) ψ dd (actB (cA σ)) omd) (v : Pl F) (p : UG (cA σ) JB)
    (u : Matrix α β (AE F E)) (φ φ₁ φ₂ φ₃ φ₄ : (κ → Fv F v) → ℂ) (hφ : φ ∈ SB (κ → Fv F v))
    (hφ₁ : φ₁ ∈ SB (κ → Fv F v)) (hφ₂ : φ₂ ∈ SB (κ → Fv F v))
    (h1 : Acts (evFin F v) (dd.rho ψ u) φ φ₁) (h2 : Acts (evFin F v) (omd p) φ φ₂)
    (h3 : Acts (evFin F v) (omd p) φ₁ φ₃)
    (h4 : Acts (evFin F v) (dd.rho ψ (u * ((p : GL β (AE F E)) : Matrix β β (AE F E))ᵀ)) φ₂ φ₄) : φ₄ = φ₃ := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  have hΦ : tens (evFin F v) φ R ∈ GlobalTheory.WeilM.schA F κ := (hR φ hφ).2
  have himpl := hS.impl p u (tens (evFin F v) φ R) hΦ
  have hact : actB (cA σ) p u = u * ((p : GL β (AE F E)) : Matrix β β (AE F E))ᵀ := rfl
  rw [hact] at himpl
  have key : tens (evFin F v) φ₄ R = tens (evFin F v) φ₃ R := by
    rw [← h4 R (hR φ₂ hφ₂), ← h2 R (hR φ hφ), ← himpl, h1 R (hR φ hφ), h3 R (hR φ₁ hφ₁)]
  funext t
  have hz : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (t i)) := by
    intro u' hu'; funext i; exact GlobalTheory.LatVac.at_liftV v _ u' hu'
  have hRz : R (fun i => GlobalTheory.LatVac.liftV v (t i)) = R 0 := by
    simpa using (hR φ hφ).1 0 _ hz
  have := congrFun key (fun i => GlobalTheory.LatVac.liftV v (t i))
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hRz] at this
  exact mul_right_cancel₀ hR0 this

end GlobalTheory.DblShape

namespace GlobalTheory.DblShape

open GlobalTheory.DblScal

/- English proof (translation)
Introduce `hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp v t b c dd omd hS hLoc ι hι`. Establish `hcm : IsCMExt F E σ` using `hp.base.cm`. Establish `hstd` using `hp.base.std`. Establish `hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v)` using `GlobalTheory.SchrSB.continuous_psiAt _ hstd.1 v`. Establish `hψ1 : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1` using `GlobalTheory.PsiNontriv.psiAt_ne_one _ hstd v`.

Establish `hσσ : ∀ x : E, σ (σ x) = x`. Take `⟨w⟩ : Nonempty (InfinitePlace E)` from `inferInstance`. Introduce `x`. Apply `w.embedding.injective` to reduce the goal to its premises. Rewrite using `[hcm.2.2.2 w.embedding (σ x), hcm.2.2.2 w.embedding x, star_star]`.

Establish `hts : (t.comp σ).comp σ = t` using `AlgHom.ext fun x => by simp [hσσ]`. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Establish `hdX : X.J.det ≠ 0`. Introduce `h0`. Apply `GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hp.herm.sig w)` to reduce the goal to its premises.

Establish `e : (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det` using `(RingHom.map_det _ _).symm`. Rewrite using `[e, h0, map_zero]`. Establish `hdW : W.J.det ≠ 0`. Introduce `h0`. Apply `GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hp.skew.sig w)` to reduce the goal to its premises.

Establish `e : (W.J.map (B.emb w).1).det = (B.emb w).1 W.J.det` using `(RingHom.map_det _ _).symm`. Rewrite using `[Matrix.det_smul, e, h0, map_zero, mul_zero]`. Establish `hdD : (dbl W.J).det ≠ 0`. Rewrite using `[dbl, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]`. Conclude with `mul_ne_zero hdW (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hdW)`.

Use `set D : GL (Fin d ⊕ Fin d) (Fv F v) := dsum c with hD`. Use `set A0 : Matrix (Fin n) (Fin n) (Fv F v) := X.J.map (t.comp σ) with hA0`. Use `set B0 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (Fv F v) := ((dbl W.J).map (t.comp σ))ᵀ with hB0`. Use `set A : Matrix (Fin n) (Fin n) (Fv F v) := A0 * b.1 with hAdef`. Use `set Bm : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (Fv F v) := D.1ᵀ * B0 with hBdef`.

Establish `hAu : IsUnit A.det`. Establish `e : A0.det = ((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v) X.J.det` using `(RingHom.map_det _ _).symm`. Rewrite using `[hAdef, Matrix.det_mul]`. Use `IsUnit.mul ?_ (Matrix.isUnits_det_units b)` and prove the remaining obligations. Rewrite using `[e]`.

Conclude with `isUnit_iff_ne_zero.2 fun h => hdX (RingHom.injective ((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v) (by rw [map_zero]; exact h))`. Establish `hBu : IsUnit Bm.det`. Establish `e : ((dbl W.J).map (t.comp σ)).det = ((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v) (dbl W.J).det` using `(RingHom.map_det _ _).symm`. Rewrite using `[hBdef, Matrix.det_mul, Matrix.det_transpose, hB0, Matrix.det_transpose]`. Use `IsUnit.mul (Matrix.isUnits_det_units D) ?_` and prove the remaining obligations.

Rewrite using `[e]`. Conclude with `isUnit_iff_ne_zero.2 fun h => hdD (RingHom.injective ((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v) (by rw [map_zero]; exact h))`. Use `choose U hUat hU0 hU1 using fun (P₀ P₁ : Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)) => GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm v t P₀ P₁`. Set `coF : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E) → Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)` to `fun u => (b⁻¹).1 * u.map (piW t) * (D⁻¹).1ᵀ`. Establish `hcc : D.1ᵀ * (D⁻¹).1ᵀ = 1` using `by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]`.

Establish `hcc' : (D⁻¹).1ᵀ * D.1ᵀ = 1` using `by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]`. Establish `htr : ∀ u, At (evFin F v) u → u.map (piW (t.comp σ)) = 0 → ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), Acts (evFin F v) (dd.rho B.ψ u) φ φ₁ → ∀ Y, ι φ₁ Y = ι φ (Y + coF u)` using `hι.trans`. Establish `hmu : ∀ u, At (evFin F v) u → u.map (piW t) = 0 → ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), Acts (evFin F v) (dd.rho B.ψ u) φ φ₁ → ∀ x, At (evFin F v) x → x.map (piW (t.comp σ)) = 0 → ι φ₁ (coF x) = B.ψ (symp (cA σ) (-1 …` using `hι.mult`. Set `xY : Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v) → Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)` to `fun Y => U (b.1 * Y * D.1ᵀ) 0`. Establish `hcoY : ∀ Y, coF (xY Y) = Y`.

Introduce `Y`. Simplify using `only [coF, xY, hU0, Matrix.mul_assoc, hcc, Matrix.mul_one]`. Rewrite using `[← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]`. Establish `hxt : ∀ x, x.map (piW t) = b.1 * coF x * D.1ᵀ`. Introduce `x`.

Simplify using `only [coF, Matrix.mul_assoc, hcc', Matrix.mul_one]`. Rewrite using `[← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]`. Establish `hmatW : ∀ p : UD σ W.J, ((p : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (piW t) = D.1 * (locMatD t c p).val * (D⁻¹).1`. Introduce `p`. Establish `e : (locMatD t c p).val = (D⁻¹).1 * ((p : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (piW t) * D.1` using `rfl`.

Rewrite using `[e]`. Simplify using `only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]`. Rewrite using `[← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]`. Establish `hcoH : ∀ (u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)) (p : UD σ W.J), coF (u * ((p : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E))ᵀ) = coF u * (locMatD t c p).valᵀ`. Introduce `u p`.

Simplify using `only [coF]`. Rewrite using `[Matrix.map_mul, Matrix.transpose_map, hmatW p]`. Simplify using `only [Matrix.transpose_mul, Matrix.mul_assoc, hcc, Matrix.mul_one]`. Establish `hsymp : ∀ x u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E), At (evFin F v) x → x.map (piW (t.comp σ)) = 0 → u.map (piW t) = 0 → B.ψ (symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J)) x u) = GlobalTheory.LatVac.psiAt B.ψ v (∑ k, ∑ l, (A0 * x.map (piW t) * B0) k l * u.map (piW (t.comp …`. Introduce `x u hx hx0 hu1`.

Establish `key` using `GlobalTheory.T.hermitian_tensor_local_vanish hcm (t.comp σ) X.J W.J hp.herm.herm hp.skew.skew x u hx0 (by rw [hts]; exact hu1)`. Rewrite `key` using `[hts]`. Unfold `symp`. Rewrite using `[GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm v t _ (at_hTens _ _ x u hx)]`. Rewrite using `[map_mul, map_mul, map_neg, map_neg, map_one, map_one, neg_one_mul, neg_one_mul, ← neg_add, add_comm, key]`.

Use `show GlobalTheory.LatVac.psiAt B.ψ v _ = GlobalTheory.LatVac.psiAt B.ψ v _`. Use `congr 1`. Simplify using `only [Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_neg]`. Both sides reduce to the same expression. Set `Lm : (Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v) →ₗ[Fv F v] Fv F v) → Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)` to `fun l => Matrix.of fun k j => l (Matrix.single k j 1)`.

Set `uM : (Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v) →ₗ[Fv F v] Fv F v) → Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)` to `fun l => U 0 ((A⁻¹)ᵀ * Lm l * (Bm⁻¹)ᵀ)`. Establish `hMu : ∀ l x, At (evFin F v) x → x.map (piW (t.comp σ)) = 0 → B.ψ (symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J)) x (uM l)) = GlobalTheory.LatVac.psiAt B.ψ v (l (coF x))`. Introduce `l x hx hx0`. Rewrite using `[hsymp x (uM l) hx hx0 (hU0 _ _), hU1, hxt x]`. Use `congr 1`.

Establish `e1 : A0 * (b.1 * coF x * D.1ᵀ) * B0 = A * coF x * Bm`. Simplify using `only [hAdef, hBdef, Matrix.mul_assoc]`. Establish `e2 : Aᵀ * ((A⁻¹)ᵀ * Lm l * (Bm⁻¹)ᵀ) * Bmᵀ = Lm l`. Establish `iA : Aᵀ * (A⁻¹)ᵀ = 1` using `by rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hAu, Matrix.transpose_one]`. Establish `iB : (Bm⁻¹)ᵀ * Bmᵀ = 1` using `by rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hBu, Matrix.transpose_one]`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[iB, Matrix.mul_one, ← Matrix.mul_assoc, iA, Matrix.one_mul]`. Rewrite using `[e1, GlobalTheory.LinWShape.frob_mul, e2, GlobalTheory.LinWShape.linForm_eq l (coF x)]`. Both sides reduce to the same expression. Establish `hatR : ∀ (u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)) (N : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)), At (evFin F v) u → At (evFin F v) (u * N)`.

Introduce `u N hu r hr`. Rewrite using `[← Matrix.smul_mul, hu r hr, Matrix.zero_mul]`. Establish `hmain : ∀ p ∈ UDAt σ W.J (evFin F v), ∃ κ : ℂ, ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), (fun (Y : Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)) => ι (locOp v (omd p) φ) (Y * (locMatD t c p).valᵀ)) = κ • ι φ`. Introduce `p hpv`. Use `set P : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) := ((p : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) with hP`.

Use `set Pinv : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) := (((p⁻¹ : UD σ W.J) : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) with hPi`. Establish `hex : ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), ∃ φ₁, φ₁ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v) ∧ Acts (evFin F v) (omd p) φ φ₁`. Introduce `φ hφ`. Take `⟨φ₁, h1, h2⟩` from `hLoc p hpv φ hφ`. Conclude with `⟨φ₁, h1, h2⟩`.

Establish `hSacts : ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), Acts (evFin F v) (omd p) φ (locOp v (omd p) φ)` using `fun φ hφ => acts_locOp (hex φ hφ)`. Establish `hSSB : ∀ φ, locOp v (omd p) φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v)` using `fun φ => locOp_mem v _ φ`. Establish `hsb` using `fun (u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)) (φ : (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v) → ℂ) (hφ : φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v)) => GlobalTheory.SchrSB.schr_mem_SB B.ψ hstd.1 v (GlobalTheory.LatVac.locCo dd v u) φ hφ`. Establish `hint : ∀ (u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)), At (evFin F v) u → ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), locOp v (omd p) (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v u) φ) = schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVa …`. Introduce `u hu φ hφ`.

Conclude with `(local_intertw dd omd hS v p u φ _ _ _ _ hφ (hsb u φ hφ) (hSSB φ) (GlobalTheory.VacBridge.rho_acts_locCo dd B.ψ v u hu φ) (hSacts φ hφ) (hSacts _ (hsb u φ hφ)) (GlobalTheory.VacBridge.rho_acts_locCo dd B.ψ v _ (hatR u _ hu) _)).symm`. Establish `hinv2 : Pinvᵀ * Pᵀ = 1`. Rewrite using `[← Matrix.transpose_mul]`. Establish `: ((p * p⁻¹ : UD σ W.J) : GL (Fin d ⊕ Fin d) (AE F E)).val = P * Pinv` using `rfl`. Rewrite using `[← this, mul_inv_cancel]`.

Conclude with `Matrix.transpose_one`. Establish `hh' : (locMatD t c p).valᵀ * (locMatD t c p⁻¹).valᵀ = 1`. Rewrite using `[map_inv, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]`. Establish `hlin : ∀ x ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), ∀ y ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), ∀ a : ℂ, (fun (Y : Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)) => ι (locOp v (omd p) (a • x + y)) (Y * (locMatD t c p).valᵀ)) = a • (fun (Y : Matrix (Fin n) (Fin d ⊕ Fin d) ( …`. Introduce `x hx y hy a`.

Establish `e` using `locOp_lin (omd p).isLinear hex a 1 hx hy`. Rewrite `e` using `[one_smul, one_smul]`. Use function extensionality and compare the values at `Y`. Simplify using `only [e, map_add, map_smul, Pi.add_apply, Pi.smul_apply]`. Establish `htrS : ∀ C, ∀ x ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (xY C)) x ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v) ∧ ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (xY C)) x) = ( …`.

Introduce `C x hx`. Establish `hat` using `hUat (b.1 * C * D.1ᵀ) 0`. Establish `hat'` using `hatR _ Pᵀ hat`. Establish `h0' : (xY C * Pᵀ).map (piW (t.comp σ)) = 0`. Rewrite using `[Matrix.map_mul]`.

Simplify using `only [xY, hU1, Matrix.zero_mul]`. Use `⟨hsb _ x hx, ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `Y`. Rewrite using `[htr (xY C) hat (hU1 _ _) x hx _ (hsb _ x hx) (GlobalTheory.VacBridge.rho_acts_locCo dd B.ψ v _ hat x) Y, hcoY]`. Use function extensionality and compare the values at `Y`.

Rewrite using `[hint _ hat x hx, htr _ hat' h0' _ (hSSB x) _ (hsb _ _ (hSSB x)) (GlobalTheory.VacBridge.rho_acts_locCo dd B.ψ v _ hat' _), hcoH, hcoY, Matrix.add_mul]`. Establish `hmuS : ∀ l, ∀ x ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (uM l)) x ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v) ∧ ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (uM l)) x) = ( …`. Introduce `l x hx`. Establish `hat` using `hUat 0 ((A⁻¹)ᵀ * Lm l * (Bm⁻¹)ᵀ)`. Establish `hat'` using `hatR _ Pᵀ hat`.

Establish `h1' : (uM l * Pᵀ).map (piW t) = 0`. Rewrite using `[Matrix.map_mul]`. Simplify using `only [uM, hU0, Matrix.zero_mul]`. Use `⟨hsb _ x hx, ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `Y`.

Establish `e` using `hmu (uM l) hat (hU0 _ _) x hx _ (hsb _ x hx) (GlobalTheory.VacBridge.rho_acts_locCo dd B.ψ v _ hat x) (xY Y) (hUat _ _) (hU1 _ _)`. Rewrite `e` using `[hcoY]`. Rewrite using `[e, hMu l (xY Y) (hUat _ _) (hU1 _ _), hcoY]`. Use function extensionality and compare the values at `Y`. Establish `hZ` using `hUat (b.1 * (Y * (locMatD t c p).valᵀ) * D.1ᵀ) 0`.

Establish `e` using `hmu _ hat' h1' _ (hSSB x) _ (hsb _ _ (hSSB x)) (GlobalTheory.VacBridge.rho_acts_locCo dd B.ψ v _ hat' _) (xY (Y * (locMatD t c p).valᵀ)) hZ (hU1 _ _)`. Rewrite `e` using `[hcoY]`. Rewrite using `[hint _ hat x hx, e]`. Use `congr 1`. Establish `hs` using `GlobalTheory.DblVacEigen.SympAct.symp_actB (cA σ) (-1 : AE F E) (incM F X.J) (dbl (incM F W.J)) p (xY (Y * (locMatD t c p).valᵀ) * Pinvᵀ) (uM l)`.

Establish `ea : actB (cA σ) p (xY (Y * (locMatD t c p).valᵀ) * Pinvᵀ) = xY (Y * (locMatD t c p).valᵀ)` using `by show xY (Y * (locMatD t c p).valᵀ) * Pinvᵀ * Pᵀ = _`. Rewrite using `[Matrix.mul_assoc, hinv2, Matrix.mul_one]`. Establish `eb : actB (cA σ) p (uM l) = uM l * Pᵀ` using `rfl`. Rewrite `hs` using `[ea, eb]`. Establish `hx0 : (xY (Y * (locMatD t c p).valᵀ) * Pinvᵀ).map (piW (t.comp σ)) = 0`.

Rewrite using `[Matrix.map_mul]`. Simplify using `only [xY, hU1, Matrix.zero_mul]`. Rewrite using `[hs, hMu l _ (hatR _ _ hZ) hx0, hcoH, hcoY, Matrix.mul_assoc, hh', Matrix.mul_one]`. Conclude with `GlobalTheory.T.weil_rep_bijection_schwartz (SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v)) (GlobalTheory.LatVac.psiAt B.ψ v) hψc hψ1 ι (fun φ Y => ι (locOp v (omd p) φ) (Y * (locMatD t c p).valᵀ)) hι.bij hlin (fun C φ => schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.l …`. Use `choose! κ hκ using hmain`.

Use `⟨κ, fun p hpv φ hφ φ₁ hφ₁ hact => ?_⟩` and prove the remaining obligations. Establish `e2` using `hκ p hpv φ hφ`. Rewrite `e2` using `[locOp_eq hφ hφ₁ hact]`. Use function extensionality and compare the values at `Y`. Establish `e3` using `congrFun e2 (Y * (GlobalTheory.SplitFlip.invT (locMatD t c p)).val)`.

Simplify using `only [Pi.smul_apply, smul_eq_mul] at e3 ⊢`. Rewrite `e3` using `[GlobalTheory.SplitFlip.invT_val, Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.mul_one]`. Rewrite using `[GlobalTheory.SplitFlip.invT_val]`. Conclude with `e3`.
-/
theorem shape_dbl : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
      (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd → GlobalTheory.DblScal.LocOps omd v →
      ∀ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd → ∃ cd : GlobalTheory.DblScal.UD σ W.J → ℂ, GlobalTheory.DblScal.IsShapeD omd t c ιd cd := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp v t b c dd omd hS hLoc ι hι
  have hcm : IsCMExt F E σ := hp.base.cm
  have hstd := hp.base.std
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.SchrSB.continuous_psiAt _ hstd.1 v
  have hψ1 : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one _ hstd v
  have hσσ : ∀ x : E, σ (σ x) = x := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    intro x
    apply w.embedding.injective
    rw [hcm.2.2.2 w.embedding (σ x), hcm.2.2.2 w.embedding x, star_star]
  have hts : (t.comp σ).comp σ = t := AlgHom.ext fun x => by simp [hσσ]
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdX : X.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hp.herm.sig w)
    have e : (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det := (RingHom.map_det _ _).symm
    rw [e, h0, map_zero]
  have hdW : W.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hp.skew.sig w)
    have e : (W.J.map (B.emb w).1).det = (B.emb w).1 W.J.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_smul, e, h0, map_zero, mul_zero]
  have hdD : (dbl W.J).det ≠ 0 := by
    rw [dbl, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
    exact mul_ne_zero hdW (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hdW)
  set D : GL (Fin d ⊕ Fin d) (Fv F v) := dsum c with hD
  set A0 : Matrix (Fin n) (Fin n) (Fv F v) := X.J.map (t.comp σ) with hA0
  set B0 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (Fv F v) := ((dbl W.J).map (t.comp σ))ᵀ with hB0
  set A : Matrix (Fin n) (Fin n) (Fv F v) := A0 * b.1 with hAdef
  set Bm : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (Fv F v) := D.1ᵀ * B0 with hBdef
  have hAu : IsUnit A.det := by
    have e : A0.det = ((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v) X.J.det := (RingHom.map_det _ _).symm
    rw [hAdef, Matrix.det_mul]
    refine IsUnit.mul ?_ (Matrix.isUnits_det_units b)
    rw [e]
    exact isUnit_iff_ne_zero.2 fun h => hdX (RingHom.injective ((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v) (by rw [map_zero]; exact h))
  have hBu : IsUnit Bm.det := by
    have e : ((dbl W.J).map (t.comp σ)).det = ((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v) (dbl W.J).det :=
      (RingHom.map_det _ _).symm
    rw [hBdef, Matrix.det_mul, Matrix.det_transpose, hB0, Matrix.det_transpose]
    refine IsUnit.mul (Matrix.isUnits_det_units D) ?_
    rw [e]
    exact isUnit_iff_ne_zero.2 fun h => hdD (RingHom.injective ((t.comp σ : E →ₐ[F] Fv F v) : E →+* Fv F v) (by rw [map_zero]; exact h))
  choose U hUat hU0 hU1 using fun (P₀ P₁ : Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)) => GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm v t P₀ P₁
  let coF : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E) → Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v) :=
    fun u => (b⁻¹).1 * u.map (piW t) * (D⁻¹).1ᵀ
  have hcc : D.1ᵀ * (D⁻¹).1ᵀ = 1 := by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  have hcc' : (D⁻¹).1ᵀ * D.1ᵀ = 1 := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have htr : ∀ u, At (evFin F v) u → u.map (piW (t.comp σ)) = 0 → ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v),
      ∀ φ₁ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), Acts (evFin F v) (dd.rho B.ψ u) φ φ₁ →
      ∀ Y, ι φ₁ Y = ι φ (Y + coF u) :=
    hι.trans
  have hmu : ∀ u, At (evFin F v) u → u.map (piW t) = 0 → ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v),
      ∀ φ₁ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), Acts (evFin F v) (dd.rho B.ψ u) φ φ₁ →
      ∀ x, At (evFin F v) x → x.map (piW (t.comp σ)) = 0 →
        ι φ₁ (coF x) = B.ψ (symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J)) x u) * ι φ (coF x) :=
    hι.mult
  let xY : Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v) → Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E) :=
    fun Y => U (b.1 * Y * D.1ᵀ) 0
  have hcoY : ∀ Y, coF (xY Y) = Y := by
    intro Y
    simp only [coF, xY, hU0, Matrix.mul_assoc, hcc, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have hxt : ∀ x, x.map (piW t) = b.1 * coF x * D.1ᵀ := by
    intro x
    simp only [coF, Matrix.mul_assoc, hcc', Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have hmatW : ∀ p : UD σ W.J, ((p : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (piW t) =
      D.1 * (locMatD t c p).val * (D⁻¹).1 := by
    intro p
    have e : (locMatD t c p).val = (D⁻¹).1 *
        ((p : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (piW t) * D.1 := rfl
    rw [e]
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have hcoH : ∀ (u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)) (p : UD σ W.J),
      coF (u * ((p : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E))ᵀ) =
        coF u * (locMatD t c p).valᵀ := by
    intro u p
    simp only [coF]
    rw [Matrix.map_mul, Matrix.transpose_map, hmatW p]
    simp only [Matrix.transpose_mul, Matrix.mul_assoc, hcc, Matrix.mul_one]
  have hsymp : ∀ x u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E), At (evFin F v) x → x.map (piW (t.comp σ)) = 0 →
      u.map (piW t) = 0 →
      B.ψ (symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J)) x u) =
        GlobalTheory.LatVac.psiAt B.ψ v (∑ k, ∑ l, (A0 * x.map (piW t) * B0) k l * u.map (piW (t.comp σ)) k l) := by
    intro x u hx hx0 hu1
    have key := GlobalTheory.T.hermitian_tensor_local_vanish hcm (t.comp σ) X.J W.J hp.herm.herm hp.skew.skew x u hx0 (by rw [hts]; exact hu1)
    rw [hts] at key
    unfold symp
    rw [GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm v t _ (at_hTens _ _ x u hx)]
    rw [map_mul, map_mul, map_neg, map_neg, map_one, map_one, neg_one_mul, neg_one_mul, ← neg_add, add_comm, key]
    show GlobalTheory.LatVac.psiAt B.ψ v _ = GlobalTheory.LatVac.psiAt B.ψ v _
    congr 1
    simp only [Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_neg]
    rfl
  let Lm : (Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v) →ₗ[Fv F v] Fv F v) → Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v) :=
    fun l => Matrix.of fun k j => l (Matrix.single k j 1)
  let uM : (Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v) →ₗ[Fv F v] Fv F v) → Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E) :=
    fun l => U 0 ((A⁻¹)ᵀ * Lm l * (Bm⁻¹)ᵀ)
  have hMu : ∀ l x, At (evFin F v) x → x.map (piW (t.comp σ)) = 0 →
      B.ψ (symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J)) x (uM l)) = GlobalTheory.LatVac.psiAt B.ψ v (l (coF x)) := by
    intro l x hx hx0
    rw [hsymp x (uM l) hx hx0 (hU0 _ _), hU1, hxt x]
    congr 1
    have e1 : A0 * (b.1 * coF x * D.1ᵀ) * B0 = A * coF x * Bm := by
      simp only [hAdef, hBdef, Matrix.mul_assoc]
    have e2 : Aᵀ * ((A⁻¹)ᵀ * Lm l * (Bm⁻¹)ᵀ) * Bmᵀ = Lm l := by
      have iA : Aᵀ * (A⁻¹)ᵀ = 1 := by rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hAu, Matrix.transpose_one]
      have iB : (Bm⁻¹)ᵀ * Bmᵀ = 1 := by rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hBu, Matrix.transpose_one]
      simp only [Matrix.mul_assoc]
      rw [iB, Matrix.mul_one, ← Matrix.mul_assoc, iA, Matrix.one_mul]
    rw [e1, GlobalTheory.LinWShape.frob_mul, e2, GlobalTheory.LinWShape.linForm_eq l (coF x)]
    rfl
  have hatR : ∀ (u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)) (N : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)),
      At (evFin F v) u → At (evFin F v) (u * N) := by
    intro u N hu r hr
    rw [← Matrix.smul_mul, hu r hr, Matrix.zero_mul]
  have hmain : ∀ p ∈ UDAt σ W.J (evFin F v), ∃ κ : ℂ, ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v),
      (fun (Y : Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)) => ι (locOp v (omd p) φ) (Y * (locMatD t c p).valᵀ)) = κ • ι φ := by
    intro p hpv
    set P : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) :=
      ((p : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) with hP
    set Pinv : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) :=
      (((p⁻¹ : UD σ W.J) : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) with hPi
    have hex : ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v),
        ∃ φ₁, φ₁ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v) ∧ Acts (evFin F v) (omd p) φ φ₁ := by
      intro φ hφ
      obtain ⟨φ₁, h1, h2⟩ := hLoc p hpv φ hφ
      exact ⟨φ₁, h1, h2⟩
    have hSacts : ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), Acts (evFin F v) (omd p) φ (locOp v (omd p) φ) :=
      fun φ hφ => acts_locOp (hex φ hφ)
    have hSSB : ∀ φ, locOp v (omd p) φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v) := fun φ => locOp_mem v _ φ
    have hsb := fun (u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)) (φ : (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v) → ℂ)
        (hφ : φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v)) =>
      GlobalTheory.SchrSB.schr_mem_SB B.ψ hstd.1 v (GlobalTheory.LatVac.locCo dd v u) φ hφ
    have hint : ∀ (u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)), At (evFin F v) u →
        ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v),
        locOp v (omd p) (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v u) φ) =
          schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (u * Pᵀ)) (locOp v (omd p) φ) := by
      intro u hu φ hφ
      exact (local_intertw dd omd hS v p u φ _ _ _ _ hφ (hsb u φ hφ) (hSSB φ)
        (GlobalTheory.VacBridge.rho_acts_locCo dd B.ψ v u hu φ) (hSacts φ hφ) (hSacts _ (hsb u φ hφ))
        (GlobalTheory.VacBridge.rho_acts_locCo dd B.ψ v _ (hatR u _ hu) _)).symm
    have hinv2 : Pinvᵀ * Pᵀ = 1 := by
      rw [← Matrix.transpose_mul]
      have : ((p * p⁻¹ : UD σ W.J) : GL (Fin d ⊕ Fin d) (AE F E)).val = P * Pinv := rfl
      rw [← this, mul_inv_cancel]
      exact Matrix.transpose_one
    have hh' : (locMatD t c p).valᵀ * (locMatD t c p⁻¹).valᵀ = 1 := by
      rw [map_inv, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
    have hlin : ∀ x ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), ∀ y ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), ∀ a : ℂ,
        (fun (Y : Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)) => ι (locOp v (omd p) (a • x + y)) (Y * (locMatD t c p).valᵀ)) =
          a • (fun (Y : Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)) => ι (locOp v (omd p) x) (Y * (locMatD t c p).valᵀ)) +
            (fun (Y : Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)) => ι (locOp v (omd p) y) (Y * (locMatD t c p).valᵀ)) := by
      intro x hx y hy a
      have e := locOp_lin (omd p).isLinear hex a 1 hx hy
      rw [one_smul, one_smul] at e
      funext Y
      simp only [e, map_add, map_smul, Pi.add_apply, Pi.smul_apply]
    have htrS : ∀ C, ∀ x ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v),
        schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (xY C)) x ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v) ∧
        ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (xY C)) x) = (fun Y => ι x (Y + C)) ∧
        (fun (Y : Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)) =>
          ι (locOp v (omd p) (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (xY C)) x)) (Y * (locMatD t c p).valᵀ)) =
          fun (Y : Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)) => ι (locOp v (omd p) x) ((Y + C) * (locMatD t c p).valᵀ) := by
      intro C x hx
      have hat := hUat (b.1 * C * D.1ᵀ) 0
      have hat' := hatR _ Pᵀ hat
      have h0' : (xY C * Pᵀ).map (piW (t.comp σ)) = 0 := by
        rw [Matrix.map_mul]; simp only [xY, hU1, Matrix.zero_mul]
      refine ⟨hsb _ x hx, ?_, ?_⟩
      · funext Y
        rw [htr (xY C) hat (hU1 _ _) x hx _ (hsb _ x hx) (GlobalTheory.VacBridge.rho_acts_locCo dd B.ψ v _ hat x) Y, hcoY]
      · funext Y
        rw [hint _ hat x hx, htr _ hat' h0' _ (hSSB x) _ (hsb _ _ (hSSB x))
          (GlobalTheory.VacBridge.rho_acts_locCo dd B.ψ v _ hat' _), hcoH, hcoY, Matrix.add_mul]
    have hmuS : ∀ l, ∀ x ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v),
        schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (uM l)) x ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v) ∧
        ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (uM l)) x) =
          (fun Y => GlobalTheory.LatVac.psiAt B.ψ v (l Y) * ι x Y) ∧
        (fun (Y : Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)) =>
          ι (locOp v (omd p) (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (uM l)) x)) (Y * (locMatD t c p).valᵀ)) =
          fun (Y : Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)) =>
            GlobalTheory.LatVac.psiAt B.ψ v (l Y) * ι (locOp v (omd p) x) (Y * (locMatD t c p).valᵀ) := by
      intro l x hx
      have hat := hUat 0 ((A⁻¹)ᵀ * Lm l * (Bm⁻¹)ᵀ)
      have hat' := hatR _ Pᵀ hat
      have h1' : (uM l * Pᵀ).map (piW t) = 0 := by
        rw [Matrix.map_mul]; simp only [uM, hU0, Matrix.zero_mul]
      refine ⟨hsb _ x hx, ?_, ?_⟩
      · funext Y
        have e := hmu (uM l) hat (hU0 _ _) x hx _ (hsb _ x hx) (GlobalTheory.VacBridge.rho_acts_locCo dd B.ψ v _ hat x)
          (xY Y) (hUat _ _) (hU1 _ _)
        rw [hcoY] at e
        rw [e, hMu l (xY Y) (hUat _ _) (hU1 _ _), hcoY]
      · funext Y
        have hZ := hUat (b.1 * (Y * (locMatD t c p).valᵀ) * D.1ᵀ) 0
        have e := hmu _ hat' h1' _ (hSSB x) _ (hsb _ _ (hSSB x)) (GlobalTheory.VacBridge.rho_acts_locCo dd B.ψ v _ hat' _)
          (xY (Y * (locMatD t c p).valᵀ)) hZ (hU1 _ _)
        rw [hcoY] at e
        rw [hint _ hat x hx, e]
        congr 1
        have hs := GlobalTheory.DblVacEigen.SympAct.symp_actB (cA σ) (-1 : AE F E) (incM F X.J) (dbl (incM F W.J)) p
          (xY (Y * (locMatD t c p).valᵀ) * Pinvᵀ) (uM l)
        have ea : actB (cA σ) p (xY (Y * (locMatD t c p).valᵀ) * Pinvᵀ) = xY (Y * (locMatD t c p).valᵀ) := by
          show xY (Y * (locMatD t c p).valᵀ) * Pinvᵀ * Pᵀ = _
          rw [Matrix.mul_assoc, hinv2, Matrix.mul_one]
        have eb : actB (cA σ) p (uM l) = uM l * Pᵀ := rfl
        rw [ea, eb] at hs
        have hx0 : (xY (Y * (locMatD t c p).valᵀ) * Pinvᵀ).map (piW (t.comp σ)) = 0 := by
          rw [Matrix.map_mul]; simp only [xY, hU1, Matrix.zero_mul]
        rw [hs, hMu l _ (hatR _ _ hZ) hx0, hcoH, hcoY, Matrix.mul_assoc, hh', Matrix.mul_one]
    exact GlobalTheory.T.weil_rep_bijection_schwartz (SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v)) (GlobalTheory.LatVac.psiAt B.ψ v) hψc hψ1 ι
      (fun φ Y => ι (locOp v (omd p) φ) (Y * (locMatD t c p).valᵀ)) hι.bij hlin
      (fun C φ => schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (xY C)) φ)
      (fun l φ => schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (uM l)) φ) htrS hmuS
  choose! κ hκ using hmain
  refine ⟨κ, fun p hpv φ hφ φ₁ hφ₁ hact => ?_⟩
  have e2 := hκ p hpv φ hφ
  rw [locOp_eq hφ hφ₁ hact] at e2
  funext Y
  have e3 := congrFun e2 (Y * (GlobalTheory.SplitFlip.invT (locMatD t c p)).val)
  simp only [Pi.smul_apply, smul_eq_mul] at e3 ⊢
  rw [GlobalTheory.SplitFlip.invT_val, Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one,
    Matrix.mul_one] at e3
  rw [GlobalTheory.SplitFlip.invT_val]
  exact e3

end GlobalTheory.DblShape
