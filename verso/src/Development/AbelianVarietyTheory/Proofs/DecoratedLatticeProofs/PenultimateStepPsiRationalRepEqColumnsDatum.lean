import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiDatumAgreeColumnDatumAtTypePrime
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ToLocEqMapToMatrix
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralPeriodicCompactSupportEqFiniteSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsValuationEqZpow
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.TwBridge.PsiRat

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu)
  {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k)
  (s : ℕ) (W : TwData k)

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[le_uniformizer_iff]`. Conclude with `(hϖ _).2 le_rfl`. Take `⟨x, hx⟩` from `ValuativeRel.valuation_surjective (uniformizer k)`. Rewrite using `[← hx]`.

Conclude with `(hϖ x).1 (by rw [hx]; exact uniformizer_lt_one)`.
-/
theorem val_unif' {ϖ : kˣ} (hϖ : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) : valuation k (ϖ : k) = uniformizer k := by
  apply le_antisymm
  · rw [le_uniformizer_iff]; exact (hϖ _).2 le_rfl
  · obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (uniformizer k)
    rw [← hx]
    exact (hϖ x).1 (by rw [hx]; exact uniformizer_lt_one)

/- English proof (translation)
Rewrite using `[Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul hq.le, ← Real.rpow_mul hq.le]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sqrt_pow (q : ℝ) (hq : 0 < q) (v : ℤ) (N : ℕ) :
    (q ^ (-v)) ^ ((N : ℝ) / 2) = (Real.sqrt q) ^ (-v * N) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul hq.le, ← Real.rpow_mul hq.le]
  congr 1
  push_cast
  ring

/- English proof (translation)
Establish `hC` using `hA.compl`. Establish `hU` using `W.unif`. Establish `hq0 : ((qOf P.1 : ℕ) : X.E) ≠ 0` using `ComplRes.q_ne_zero hC`. Establish `hvalu` using `val_unif' hU`. Establish `hex : ∃ z : ℤ, IsUnit (redP P.1 (a / ((qOf P.1 : ℕ) : X.E) ^ z))`.

Take `⟨z, hz⟩` from `NormalForm.exists_valuation_eq_zpow hvalu u`. Use `⟨z, ?_⟩` and prove the remaining obligations. Establish `hv1 : valuation k (ι (a / ((qOf P.1 : ℕ) : X.E) ^ z)) = 1`. Rewrite using `[map_div₀, map_zpow₀, ← hC.unif, ← hu, map_div₀, map_zpow₀, hz, div_self]`. Conclude with `zpow_ne_zero _ ((Valuation.ne_zero_iff _).2 W.ϖ.ne_zero)`.

Conclude with `(ComplRes.v_eq_one_iff_red hC hU (ComplRes.intAt_of_v hC hv1.le)).1 hv1`. Establish `hspec : IsUnit (redP P.1 (a / ((qOf P.1 : ℕ) : X.E) ^ LocE.vP P.1 (qOf P.1) a))`. Unfold `LocE.vP`. Conclude with `Classical.epsilon_spec hex`. Use `set v := LocE.vP P.1 (qOf P.1) a with hvdef`.

Use `set b := a / ((qOf P.1 : ℕ) : X.E) ^ v with hbdef`. Establish `hbI : IntAt P.1 b`. Assume the negation of the conclusion as `h`. Rewrite `hspec` using `[reduction_eq_zero_of_not_integral P.1 h]`. Conclude with `not_isUnit_zero hspec`.

Establish `hbv : valuation k (ι b) = 1` using `(ComplRes.v_eq_one_iff_red hC hU hbI).2 hspec`. Establish `hb0 : ι b ≠ 0` using `by intro h; rw [h, map_zero] at hbv; exact zero_ne_one hbv`. Use `set ub : kˣ := Units.mk0 (ι b) hb0 with hubdef`. Establish `hu_eq : u = W.ϖ ^ v * ub`. Use `ext`.

Rewrite using `[Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, hu, hC.unif, ← map_zpow₀, ← map_mul, hbdef, mul_div_left_comm, div_self (zpow_ne_zero v hq0), mul_one]`. Establish `hη : W.η (s + 1) ub = 1` using `W.unr (s + 1) ub hbv`. Establish `hδ : (W.δ ub : ℂ) = (σ₀ (LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) b))⁻¹` using `hA.del b ub hbI hspec rfl`. Establish `hμ : ((W.η (s + 1) * W.δ) W.ϖ : ℂ) = σ₀ (cst.muq (s + 1) P)` using `hA.mu s (by rw [hA.steps]; omega)`. Establish `hnU : nabs k ub = 1` using `nabs_eq_one_of_valuation_eq_one hbv`.

Take `⟨p, hp, hpϖ⟩` from `GlobalTheory.PeriodicIntegral.exists_irreducible_of_isUnif hU`. Establish `hnϖ : nabs k W.ϖ = ((qOf P.1 : ℕ) : ℝ)⁻¹`. Rewrite using `[nabs_uniformiser hp hpϖ.symm, ComplRes.resCard_eq hC hU]`. Establish `hn : nabs k u = ((qOf P.1 : ℕ) : ℝ) ^ (-v)`. Rewrite using `[hu_eq]`.

Unfold `nabs`. Rewrite using `[map_mul, map_zpow, NNReal.coe_mul, NNReal.coe_zpow]`. Establish `h1 : ((distribHaarChar k W.ϖ : NNReal) : ℝ) = ((qOf P.1 : ℕ) : ℝ)⁻¹` using `hnϖ`. Establish `h2 : ((distribHaarChar k ub : NNReal) : ℝ) = 1` using `hnU`. Rewrite using `[h1, h2, mul_one, _root_.inv_zpow']`.

Establish `hsg : W.sg ≠ 0`. Introduce `h0`. Establish `h2` using `congrArg σ₀ (hok.sq_sq P)`. Rewrite `h2` using `[map_pow, hA.sq, h0, zero_mul, map_natCast]`. Conclude with `hq0 (by exact_mod_cast (zero_pow two_ne_zero).symm.trans h2 |>.symm)`.

Establish `hmuAt : muAt Ch sel mu cst s P a = cst.muq (s + 1) P ^ v * (LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) b)⁻¹`. Unfold `muAt LocE.locChar`. Rewrite using `[if_neg hA.nmem, ← hvdef, ← hbdef]`. Use `congr 1`. Unfold `LocE.unitV`.

Rewrite using `[dif_pos hspec, dif_pos hspec, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]`. Establish `hchar : ((W.η (s + 1) * W.δ) u : ℂ) = σ₀ (cst.muq (s + 1) P) ^ v * (σ₀ (LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) b))⁻¹`. Rewrite using `[hu_eq, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, hμ, MonoidHom.mul_apply, Units.val_mul, hη, Units.val_one, one_mul, hδ]`. Establish `hq : (0 : ℝ) < ((qOf P.1 : ℕ) : ℝ)`. Establish `: (qOf P.1 : ℕ) ≠ 0` using `fun h => hq0 (by rw [h, Nat.cast_zero])`.

Conclude with `Nat.pos_of_ne_zero this` after adjusting the coercions. Rewrite using `[hchar, hn, sqrt_pow _ hq, hmuAt, map_mul, map_mul, map_zpow₀, map_inv₀, map_zpow₀, hA.sq, mul_zpow]`. Use `push_cast`. Establish `hs1 : W.sg ^ (v * N) * W.sg ^ (-v * N) = 1`. Rewrite using `[neg_mul, _root_.zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ hsg)]`.

Take the linear combination `(σ₀ (cst.muq (s + 1) P) ^ v * (σ₀ (LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) b))⁻¹ * (Real.sqrt ((qOf P.1 : ℕ) : ℝ) : ℂ) ^ (-v * N)) * (-hs1)`.
-/
theorem char_scalar (hok : cst.Ok) (hA : AtTwist (R := R) sel mu cst σ₀ P ι s W) (a : X.E) (u : kˣ)
    (hu : (u : k) = ι a) (N : ℕ) :
    ((W.η (s + 1) * W.δ) u : ℂ) * ((nabs k u ^ ((N : ℝ) / 2) : ℝ) : ℂ) =
      W.sg ^ (LocE.vP P.1 (qOf P.1) a * N) *
        σ₀ (muAt Ch sel mu cst s P a * cst.sq P ^ (-(LocE.vP P.1 (qOf P.1) a) * N)) := by
  have hC := hA.compl
  have hU := W.unif
  have hq0 : ((qOf P.1 : ℕ) : X.E) ≠ 0 := ComplRes.q_ne_zero hC
  have hvalu := val_unif' hU
  have hex : ∃ z : ℤ, IsUnit (redP P.1 (a / ((qOf P.1 : ℕ) : X.E) ^ z)) := by
    obtain ⟨z, hz⟩ := NormalForm.exists_valuation_eq_zpow hvalu u
    refine ⟨z, ?_⟩
    have hv1 : valuation k (ι (a / ((qOf P.1 : ℕ) : X.E) ^ z)) = 1 := by
      rw [map_div₀, map_zpow₀, ← hC.unif, ← hu, map_div₀, map_zpow₀, hz, div_self]
      exact zpow_ne_zero _ ((Valuation.ne_zero_iff _).2 W.ϖ.ne_zero)
    exact (ComplRes.v_eq_one_iff_red hC hU (ComplRes.intAt_of_v hC hv1.le)).1 hv1
  have hspec : IsUnit (redP P.1 (a / ((qOf P.1 : ℕ) : X.E) ^ LocE.vP P.1 (qOf P.1) a)) := by
    unfold LocE.vP; exact Classical.epsilon_spec hex
  set v := LocE.vP P.1 (qOf P.1) a with hvdef
  set b := a / ((qOf P.1 : ℕ) : X.E) ^ v with hbdef
  have hbI : IntAt P.1 b := by
    by_contra h; rw [reduction_eq_zero_of_not_integral P.1 h] at hspec; exact not_isUnit_zero hspec
  have hbv : valuation k (ι b) = 1 := (ComplRes.v_eq_one_iff_red hC hU hbI).2 hspec
  have hb0 : ι b ≠ 0 := by intro h; rw [h, map_zero] at hbv; exact zero_ne_one hbv
  set ub : kˣ := Units.mk0 (ι b) hb0 with hubdef
  have hu_eq : u = W.ϖ ^ v * ub := by
    ext
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, hu, hC.unif, ← map_zpow₀, ← map_mul, hbdef,
      mul_div_left_comm, div_self (zpow_ne_zero v hq0), mul_one]
  have hη : W.η (s + 1) ub = 1 := W.unr (s + 1) ub hbv
  have hδ : (W.δ ub : ℂ) = (σ₀ (LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) b))⁻¹ := hA.del b ub hbI hspec rfl
  have hμ : ((W.η (s + 1) * W.δ) W.ϖ : ℂ) = σ₀ (cst.muq (s + 1) P) := hA.mu s (by rw [hA.steps]; omega)
  have hnU : nabs k ub = 1 := nabs_eq_one_of_valuation_eq_one hbv
  obtain ⟨p, hp, hpϖ⟩ := GlobalTheory.PeriodicIntegral.exists_irreducible_of_isUnif hU
  have hnϖ : nabs k W.ϖ = ((qOf P.1 : ℕ) : ℝ)⁻¹ := by
    rw [nabs_uniformiser hp hpϖ.symm, ComplRes.resCard_eq hC hU]
  have hn : nabs k u = ((qOf P.1 : ℕ) : ℝ) ^ (-v) := by
    rw [hu_eq]
    unfold nabs
    rw [map_mul, map_zpow, NNReal.coe_mul, NNReal.coe_zpow]
    have h1 : ((distribHaarChar k W.ϖ : NNReal) : ℝ) = ((qOf P.1 : ℕ) : ℝ)⁻¹ := hnϖ
    have h2 : ((distribHaarChar k ub : NNReal) : ℝ) = 1 := hnU
    rw [h1, h2, mul_one, _root_.inv_zpow']
  have hsg : W.sg ≠ 0 := by
    intro h0
    have h2 := congrArg σ₀ (hok.sq_sq P)
    rw [map_pow, hA.sq, h0, zero_mul, map_natCast] at h2
    exact hq0 (by exact_mod_cast (zero_pow two_ne_zero).symm.trans h2 |>.symm)
  have hmuAt : muAt Ch sel mu cst s P a = cst.muq (s + 1) P ^ v * (LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) b)⁻¹ := by
    unfold muAt LocE.locChar
    rw [if_neg hA.nmem, ← hvdef, ← hbdef]
    congr 1
    unfold LocE.unitV
    rw [dif_pos hspec, dif_pos hspec, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  have hchar : ((W.η (s + 1) * W.δ) u : ℂ) = σ₀ (cst.muq (s + 1) P) ^ v * (σ₀ (LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) b))⁻¹ := by
    rw [hu_eq, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, hμ, MonoidHom.mul_apply, Units.val_mul, hη,
      Units.val_one, one_mul, hδ]
  have hq : (0 : ℝ) < ((qOf P.1 : ℕ) : ℝ) := by
    have : (qOf P.1 : ℕ) ≠ 0 := fun h => hq0 (by rw [h, Nat.cast_zero])
    exact_mod_cast Nat.pos_of_ne_zero this
  rw [hchar, hn, sqrt_pow _ hq, hmuAt, map_mul, map_mul, map_zpow₀, map_inv₀, map_zpow₀, hA.sq, mul_zpow]
  push_cast
  have hs1 : W.sg ^ (v * N) * W.sg ^ (-v * N) = 1 := by
    rw [neg_mul, _root_.zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ hsg)]
  linear_combination (σ₀ (cst.muq (s + 1) P) ^ v * (σ₀ (LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) b))⁻¹ *
    (Real.sqrt ((qOf P.1 : ℕ) : ℝ) : ℂ) ^ (-v * N)) * (-hs1)

end GlobalTheory.TwBridge.PsiRat

noncomputable section
namespace GlobalTheory.TwBridge.PsiRat

/- English proof (translation)
Establish `h : ∀ {A B : Type} {a b : ℕ} (e : A ≃ Fin a) (e' : B ≃ Fin b) (z : (Fin b → E) →ₗ[E] (Fin a → E)), toLoc ι e e' z = ((LinearMap.toMatrix' z).submatrix e e').map ι`. Introduce `A B a b e e' z`. Use extensionality with `i j`. Simplify using `[toLoc, LinearMap.toMatrix'_apply, Matrix.map_apply, Matrix.submatrix_apply]`. Rewrite using `[h, h, h, LinearMap.toMatrix'_comp, ← Matrix.submatrix_mul_equiv _ _ eA eB eC, Matrix.map_mul]`.
-/
theorem toLoc_comp_rect {E k : Type} [Field E] [Field k] (ι : E →+* k) {A B C : Type} [Fintype B] [DecidableEq B]
    {a b c : ℕ} (eA : A ≃ Fin a) (eB : B ≃ Fin b) (eC : C ≃ Fin c) (x : (Fin b → E) →ₗ[E] (Fin a → E))
    (y : (Fin c → E) →ₗ[E] (Fin b → E)) :
    toLoc ι eA eB x * toLoc ι eB eC y = toLoc ι eA eC (x ∘ₗ y) := by
  have h : ∀ {A B : Type} {a b : ℕ} (e : A ≃ Fin a) (e' : B ≃ Fin b) (z : (Fin b → E) →ₗ[E] (Fin a → E)),
      toLoc ι e e' z = ((LinearMap.toMatrix' z).submatrix e e').map ι := by
    intro A B a b e e' z
    ext i j
    simp [toLoc, LinearMap.toMatrix'_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rw [h, h, h, LinearMap.toMatrix'_comp, ← Matrix.submatrix_mul_equiv _ _ eA eB eC, Matrix.map_mul]

/- English proof (translation)
Unfold `muAt LocE.locChar`. Rewrite using `[PsiStep.valuation_one₂, zpow_zero, zpow_zero, one_mul, div_one]`. Establish `h1 : IsUnit (redP P.1 (1 : X.E))` using `by rw [PsiStep.reduction_one']; exact isUnit_one`. Unfold `LocE.unitV`. Rewrite using `[dif_pos h1]`.

Establish `: h1.unit = 1` using `Units.ext (by rw [IsUnit.unit_spec, PsiStep.reduction_one', Units.val_one])`. Rewrite using `[this, map_one, Units.val_one]`.
-/
theorem muAt_one {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
    (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (i : ℕ) (P : rowSG Pr sel mu) :
    muAt Ch sel mu cst i P 1 = 1 := by
  unfold muAt LocE.locChar
  rw [PsiStep.valuation_one₂, zpow_zero, zpow_zero, one_mul, div_one]
  have h1 : IsUnit (redP P.1 (1 : X.E)) := by rw [PsiStep.reduction_one']; exact isUnit_one
  unfold LocE.unitV
  rw [dif_pos h1]
  have : h1.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, PsiStep.reduction_one', Units.val_one])
  rw [this, map_one, Units.val_one]

end GlobalTheory.TwBridge.PsiRat

namespace GlobalTheory.TwBridge

open PsiRat in

/- English proof (translation)
Introduce `X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hok hA hPhi γ g hg e' e he' he x₀ y'`. Establish `hc1 : cOf R s = 0 + 1` using `by unfold cOf; rw [hA.steps]; omega`. Establish `hc0 : cOf R (s + 1) = 0` using `by unfold cOf; rw [hA.steps]; omega`. Take `⟨eg, hegO, hgv⟩` from `hg`. Set `E' : XIx (Fin R.k) (Fin R.t) s ⊕ Fin (0 + 1) ≃ Fin (R.N s + cOf R s)` to `(e'.sumCongr (finCongr hc1.symm)).trans finSumFinEquiv`.

Set `E₁ : XIx (Fin R.k) (Fin R.t) (s + 1) ⊕ Fin 0 ≃ Fin (R.N (s + 1) + cOf R (s + 1))` to `(e.sumCongr (finCongr hc0.symm)).trans finSumFinEquiv`. Establish `hE' : IsOrd (yPos xPos (R.N s)) E'`. Introduce and unpack `(a | a)`. Simplify using `[E', yPos, he' a]`. Simplify using `[E', yPos]`.

Establish `hE₁ : IsOrd (yPos xPos (R.N (s + 1))) E₁`. Introduce and unpack `(a | a)`. Simplify using `[E₁, yPos, he a]`. Conclude with `a.elim0`. Establish `hegE : eg = E'` using `Equiv.ext fun a => Fin.ext ((hegO a).trans (hE' a).symm)`.

Substitute `hegE` using the available equality. Establish `hmat : withCol (toLoc ι e e' x₀) (fun a => ι (y' (e a))) = toLoc ι E₁ E' (joinCol (c'` using `cOf R s) (c := cOf R (s + 1)) x₀ y') := PsiStep.withCol_toLoc ι e e' hc1 hc0 x₀ y'`. Establish `hprod : toLoc ι E₁ E' (joinCol (c'` using `cOf R s) (c := cOf R (s + 1)) x₀ y') * toLoc ι E' E' γ.toLinearMap = toLoc ι E₁ E' (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y' ∘ₗ γ.toLinearMap) := toLoc_comp_rect ι E₁ E' E' _ _`. Establish `hdet : ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = ι ((LinearEquiv.det γ : X.Eˣ) : X.E)`. Establish `h` using `RingHom.map_det ι ((LinearMap.toMatrix' γ.toLinearMap).submatrix E' E')`.

Rewrite `h` using `[RingHom.mapMatrix_apply]`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, hgv, toLoc_eq_map_toMatrix', ← h, Matrix.det_submatrix_equiv_self, LinearMap.det_toMatrix', LinearEquiv.coe_det]`. Establish `hcard : Fintype.card (XIx (Fin R.k) (Fin R.t) (s + 1) ⊕ Fin 0) = R.N (s + 1) + cOf R (s + 1)`. Rewrite using `[Fintype.card_congr E₁, Fintype.card_fin]`. Establish `hPhi1` using `hPhi.1 s 0 rfl E' E₁ hegO hE₁ (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y' ∘ₗ γ.toLinearMap)`.

Establish `hsc` using `char_scalar Ch sel mu cst σ₀ P ι s W hok hA _ _ hdet (R.N (s + 1) + cOf R (s + 1))`. Establish `hL : (W.T s R).Psi g (toLoc ι e e' x₀) (fun a => ι (y' (e a))) = ((W.η (s + 1) * W.δ) (Matrix.GeneralLinearGroup.det g) : ℂ) * ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((R.N (s + 1) + cOf R (s + 1) : ℕ) : ℝ) / 2) : ℝ) : ℂ) * σ₀ (PhiAt Ch mu cst.sharp s P.1 (joinCol (c'` using `cOf R s) (c := cOf R (s + 1)) x₀ y' ∘ₗ γ.toLinearMap)) := by`. Rewrite using `[← hPhi1, ← hprod, ← hgv, ← hmat, ← hcard]`. Use `clear hsc hPhi1 hdet hprod hmat hE₁ hE' hegO hPhi hA hok hgv hcard he he'`. Unfold `Chain.Psi GlobalTheory.SplitWeil.om`.

Establish `hn1 : nabs k (1 : kˣ) = 1` using `by unfold nabs; rw [map_one, NNReal.coe_one]`. Simplify using `only [map_one, inv_one, Units.val_one, hn1, Real.one_rpow, Complex.ofReal_one, mul_one, one_mul, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mul]`. Both sides reduce to the same expression. Rewrite using `[hL, hsc]`. Unfold `PsiAt omPhi Loc.om sgn`.

Simplify using `only [map_one, Units.val_one, PsiStep.valuation_one₂, muAt_one, inv_one, mul_one, zero_mul, zpow_zero]`. Establish `h1 : (LinearEquiv.symm (1 : AutY X R (s + 1))).toLinearMap ∘ₗ (joinCol (c'` using `cOf R s) (c := cOf R (s + 1)) x₀ y' ∘ₗ γ.toLinearMap) = joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y' ∘ₗ γ.toLinearMap := by`. Use extensionality with `v`. Both sides reduce to the same expression. Rewrite using `[h1]`.

Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem psi_rat_agree : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → PhiAgree Ch sel mu cst σ₀ P ι s W →
  ∀ (γ : AutY X R s) (g : GL (XIx (Fin R.k) (Fin R.t) s ⊕ Fin (0 + 1)) k), IsGL ι γ g →
  ∀ (e' : XIx (Fin R.k) (Fin R.t) s ≃ Fin (R.N s)) (e : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1))),
    IsOrd xPos e' → IsOrd xPos e → ∀ (x₀ : HomE X.E (R.N s) (R.N (s + 1))) (y' : Sp X.E (R.N (s + 1))),
      (W.T s R).Psi g (toLoc ι e e' x₀) (fun a => ι (y' (e a))) =
        sgn sel mu P W γ (R.N (s + 1) + cOf R (s + 1)) * σ₀ (PsiAt Ch sel mu cst s P γ x₀ y') := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hok hA hPhi γ g hg e' e he' he x₀ y'
  have hc1 : cOf R s = 0 + 1 := by unfold cOf; rw [hA.steps]; omega
  have hc0 : cOf R (s + 1) = 0 := by unfold cOf; rw [hA.steps]; omega
  obtain ⟨eg, hegO, hgv⟩ := hg
  let E' : XIx (Fin R.k) (Fin R.t) s ⊕ Fin (0 + 1) ≃ Fin (R.N s + cOf R s) :=
    (e'.sumCongr (finCongr hc1.symm)).trans finSumFinEquiv
  let E₁ : XIx (Fin R.k) (Fin R.t) (s + 1) ⊕ Fin 0 ≃ Fin (R.N (s + 1) + cOf R (s + 1)) :=
    (e.sumCongr (finCongr hc0.symm)).trans finSumFinEquiv
  have hE' : IsOrd (yPos xPos (R.N s)) E' := by
    rintro (a | a)
    · simp [E', yPos, he' a]
    · simp [E', yPos]
  have hE₁ : IsOrd (yPos xPos (R.N (s + 1))) E₁ := by
    rintro (a | a)
    · simp [E₁, yPos, he a]
    · exact a.elim0
  have hegE : eg = E' := Equiv.ext fun a => Fin.ext ((hegO a).trans (hE' a).symm)
  subst hegE
  have hmat : withCol (toLoc ι e e' x₀) (fun a => ι (y' (e a))) =
      toLoc ι E₁ E' (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y') :=
    PsiStep.withCol_toLoc ι e e' hc1 hc0 x₀ y'
  have hprod : toLoc ι E₁ E' (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y') * toLoc ι E' E' γ.toLinearMap =
      toLoc ι E₁ E' (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y' ∘ₗ γ.toLinearMap) :=
    toLoc_comp_rect ι E₁ E' E' _ _
  have hdet : ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = ι ((LinearEquiv.det γ : X.Eˣ) : X.E) := by
    have h := RingHom.map_det ι ((LinearMap.toMatrix' γ.toLinearMap).submatrix E' E')
    rw [RingHom.mapMatrix_apply] at h
    rw [Matrix.GeneralLinearGroup.val_det_apply, hgv, toLoc_eq_map_toMatrix', ← h,
      Matrix.det_submatrix_equiv_self, LinearMap.det_toMatrix', LinearEquiv.coe_det]
  have hcard : Fintype.card (XIx (Fin R.k) (Fin R.t) (s + 1) ⊕ Fin 0) = R.N (s + 1) + cOf R (s + 1) := by
    rw [Fintype.card_congr E₁, Fintype.card_fin]
  have hPhi1 := hPhi.1 s 0 rfl E' E₁ hegO hE₁ (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y' ∘ₗ γ.toLinearMap)
  have hsc := char_scalar Ch sel mu cst σ₀ P ι s W hok hA _ _ hdet (R.N (s + 1) + cOf R (s + 1))
  have hL : (W.T s R).Psi g (toLoc ι e e' x₀) (fun a => ι (y' (e a))) =
      ((W.η (s + 1) * W.δ) (Matrix.GeneralLinearGroup.det g) : ℂ) *
        ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((R.N (s + 1) + cOf R (s + 1) : ℕ) : ℝ) / 2) : ℝ) : ℂ) *
        σ₀ (PhiAt Ch mu cst.sharp s P.1 (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y' ∘ₗ γ.toLinearMap)) := by
    rw [← hPhi1, ← hprod, ← hgv, ← hmat, ← hcard]
    clear hsc hPhi1 hdet hprod hmat hE₁ hE' hegO hPhi hA hok hgv hcard he he'
    unfold Chain.Psi GlobalTheory.SplitWeil.om
    have hn1 : nabs k (1 : kˣ) = 1 := by unfold nabs; rw [map_one, NNReal.coe_one]
    simp only [map_one, inv_one, Units.val_one, hn1, Real.one_rpow, Complex.ofReal_one, mul_one, one_mul,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mul]
    rfl
  rw [hL, hsc]
  unfold PsiAt omPhi Loc.om sgn
  simp only [map_one, Units.val_one, PsiStep.valuation_one₂, muAt_one, inv_one, mul_one, zero_mul, zpow_zero]
  have h1 : (LinearEquiv.symm (1 : AutY X R (s + 1))).toLinearMap ∘ₗ
      (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y' ∘ₗ γ.toLinearMap) =
        joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y' ∘ₗ γ.toLinearMap := by
    ext v; rfl
  rw [h1]
  simp only [map_mul]
  ring

end GlobalTheory.TwBridge
