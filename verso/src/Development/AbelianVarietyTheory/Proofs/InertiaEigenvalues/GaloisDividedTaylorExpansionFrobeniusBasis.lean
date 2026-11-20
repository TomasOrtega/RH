import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTaylorShiftFrobeniusTwoVariableCompatible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallinePrismsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusStratificationCoeffEqConnectionPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicValNatFactorialBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCrystalBasisAndSpanStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystalBasisTransportFreeOverPrismStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismCrystalChangeOfBasisConstantCoeffEqOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystalChangeOfBasisFrobeniusCompatStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisMatrixEqCrystalChangeOfBasisValueStatement

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CrysGal

open GlobalTheory.Prism

/- English proof (translation)
Establish `hu` using `(E.tr_bc f (E.M P' ⧸ Submodule.span P'.A (Set.range (E.tr f))) 0).unique (y₁ := Submodule.mkQ _) (y₂ := 0) (fun x => by show Submodule.Quotient.mk _ = 0`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Conclude with `Submodule.subset_span ⟨x, rfl⟩)`. Use the proof step `(fun x => rfl)`. Rewrite using `[eq_top_iff]`.

Introduce `x _`. Use `LinearMap.congr_fun hu x` as an intermediate fact. Rewrite `this` using `[Submodule.mkQ_apply, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]`. Then use the resulting hypothesis.
-/
theorem span_range_tr {l : ℕ} {R : Type} [CommRing R] (E : FCrys l R) {P P' : Obj l R}
    (f : GlobalTheory.Prism.Hom P P') : Submodule.span P'.A (Set.range (E.tr f)) = ⊤ := by
  have hu := (E.tr_bc f (E.M P' ⧸ Submodule.span P'.A (Set.range (E.tr f))) 0).unique
    (y₁ := Submodule.mkQ _) (y₂ := 0)
    (fun x => by
      show Submodule.Quotient.mk _ = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact Submodule.subset_span ⟨x, rfl⟩)
    (fun x => rfl)
  rw [eq_top_iff]
  intro x _
  have := LinearMap.congr_fun hu x
  rwa [Submodule.mkQ_apply, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero] at this

/- English proof (translation)
Establish `hx : x ∈ Submodule.span P'.A (Set.range (E.tr f))` using `(span_range_tr E f) ▸ Submodule.mem_top`. Use `(Submodule.span_le.2 ?_) hx` and prove the remaining obligations. Introduce and unpack `_ ⟨z, rfl⟩`. Take `⟨N, c, s, hz⟩` from `hgen z`. Rewrite using `[hz, map_sum]`.

Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum]`. Use `Submodule.sum_mem _ fun q _ => ?_` and prove the remaining obligations. Rewrite using `[map_smulₛₗ, ← (oE (c j q)).u_tr]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨(c j q, j), rfl⟩)`.
-/
theorem mem_span_tr {l : ℕ} {R : Type} [CommRing R] (E : FCrys l R) {P P' : Obj l R}
    (f : GlobalTheory.Prism.Hom P P') {O ι : Type} [Fintype ι] (oE : O → FHom E E) (b : ι → E.M P)
    (hgen : ∀ x : E.M P, ∃ (N : ℕ) (c : ι → Fin N → O) (s : ι → Fin N → P.A),
      x = ∑ j, ∑ q, s j q • (oE (c j q)).u P (b j)) (x : E.M P') :
    x ∈ Submodule.span P'.A (Set.range fun p : O × ι => (oE p.1).u P' (E.tr f (b p.2))) := by
  have hx : x ∈ Submodule.span P'.A (Set.range (E.tr f)) := (span_range_tr E f) ▸ Submodule.mem_top
  refine (Submodule.span_le.2 ?_) hx
  rintro _ ⟨z, rfl⟩
  obtain ⟨N, c, s, hz⟩ := hgen z
  rw [hz, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [map_sum]
  refine Submodule.sum_mem _ fun q _ => ?_
  rw [map_smulₛₗ, ← (oE (c j q)).u_tr]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(c j q, j), rfl⟩)

/- English proof (translation)
Use `choose n w gg hgg using fun j => Submodule.mem_span_set'.1 (hx j)`. Use `choose pc hpc using fun j k => (gg j k).2`. Use `⟨Σ j', Fin (n j'), inferInstance, fun i j q => (pc q.1 q.2).1, fun i j q => if q.1 = j then (if (pc q.1 q.2).2 = i then w q.1 q.2 else 0) else 0, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Rewrite using `[Fintype.sum_sigma]`.

Rewrite using `[Finset.sum_eq_single j (fun j' _ hj' => by simp [hj']) (by simp)]`. Rewrite using `[← hgg j]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [if_true, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ]`. Rewrite using `[← hpc j k]`.
-/
theorem exists_rep {A M O ι : Type} [CommRing A] [AddCommGroup M] [Module A M] [Fintype ι] [DecidableEq ι]
    (v : O → ι → M) (x : ι → M) (hx : ∀ j, x j ∈ Submodule.span A (Set.range fun p : O × ι => v p.1 p.2)) :
    ∃ (Q : Type) (_ : Fintype Q) (c : ι → ι → Q → O) (y : ι → ι → Q → A),
      ∀ j, x j = ∑ i, ∑ q, y i j q • v (c i j q) i := by
  choose n w gg hgg using fun j => Submodule.mem_span_set'.1 (hx j)
  choose pc hpc using fun j k => (gg j k).2
  refine ⟨Σ j', Fin (n j'), inferInstance, fun i j q => (pc q.1 q.2).1,
    fun i j q => if q.1 = j then (if (pc q.1 q.2).2 = i then w q.1 q.2 else 0) else 0, fun j => ?_⟩
  rw [Finset.sum_comm]
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single j (fun j' _ hj' => by simp [hj']) (by simp)]
  rw [← hgg j]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [if_true, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ]
  rw [← hpc j k]

/- English proof (translation)
Substitute `hw` using the available equality. Use `choose n₀ hn₀ using hconv`. Use `⟨Finset.univ.sup n₀, fun n hn => ?_⟩` and prove the remaining obligations. Repeatedly rewrite using `[hG, map_sum, map_smul, Finset.mul_sum, mul_smul_comm]`. Rewrite using `[Finset.sum_comm, ← Finset.sum_sub_distrib]`.

Apply `Finset.dvd_sum` to reduce the goal to its premises. Introduce `q _`. Rewrite using `[← Finset.smul_sum, show c q ⊗ₜ[ℤ_[l]] z q = c q • ((1 : O) ⊗ₜ[ℤ_[l]] z q) by`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one], ← smul_sub, Algebra.smul_def]`. Conclude with `Dvd.dvd.mul_left (hn₀ q n (le_trans (Finset.le_sup (Finset.mem_univ q)) hn)) _`.
-/
theorem conv_comb {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
    (g : ↥(GK (ϖ.field a))) {Q : Type} [Fintype Q] (c : Q → O) (z : Q → Per.Acris l)
    (F : Q → ℕ → (ZMod a → S O K e)) (G : ℕ → (ZMod a → S O K e)) (hG : ∀ k, G k = ∑ q, c q • F q k)
    (r : ℕ) (hconv : ∀ q, ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣
      (1 : O) ⊗ₜ[ℤ_[l]] z q - ∑ k ∈ Finset.range n, ϖ.muDiv a O g k * ϖ.iC t K (F q k))
    (w : OCr l O) (hw : w = ∑ q, c q ⊗ₜ[ℤ_[l]] z q) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣
      w - ∑ k ∈ Finset.range n, ϖ.muDiv a O g k * ϖ.iC t K (G k) := by
  subst hw
  choose n₀ hn₀ using hconv
  refine ⟨Finset.univ.sup n₀, fun n hn => ?_⟩
  simp_rw [hG, map_sum, map_smul, Finset.mul_sum, mul_smul_comm]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro q _
  rw [← Finset.smul_sum, show c q ⊗ₜ[ℤ_[l]] z q = c q • ((1 : O) ⊗ₜ[ℤ_[l]] z q) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], ← smul_sub, Algebra.smul_def]
  exact Dvd.dvd.mul_left (hn₀ q n (le_trans (Finset.le_sup (Finset.mem_univ q)) hn)) _

/- English proof (translation)
Introduce `k`. Use function extensionality and compare the values at `τ`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hG, Finset.sum_apply, AddSubmonoidClass.coe_finsetSum, map_sum, Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations.

Rewrite using `[Pi.smul_apply, SetLike.val_smul, hF, PowerSeries.coeff_smul, mul_smul_comm, mul_smul_comm]`.
-/
theorem comb_S {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    {a e : ℕ} {Q : Type} [Fintype Q] (c : Q → O) (w : ZMod a → Q → K⟦X⟧⟦X⟧)
    (G : ℕ → ZMod a → S O K e) (F : Q → ℕ → ZMod a → S O K e)
    (hG : ∀ k τ, (G k τ : K⟦X⟧) = (X : K⟦X⟧) ^ k * ((k.factorial : K⟦X⟧) * coeff k (∑ q, c q • w τ q)))
    (hF : ∀ q k τ, (F q k τ : K⟦X⟧) = (X : K⟦X⟧) ^ k * ((k.factorial : K⟦X⟧) * coeff k (w τ q))) :
    ∀ k, G k = ∑ q, c q • F q k := by
  intro k
  funext τ
  apply Subtype.ext
  rw [hG, Finset.sum_apply, AddSubmonoidClass.coe_finsetSum, map_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Pi.smul_apply, SetLike.val_smul, hF, PowerSeries.coeff_smul, mul_smul_comm, mul_smul_comm]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `BS l _ a e _ _ ϖ LL _ _ hl2 ι _ _ P T I hBK hS g`. Use `letI := zlLat (resF T (ϖ.field a))`. Take `⟨E, jA, hR, hIm⟩` from `hBK`. Establish `hO : ∀ c : ↥(OL LL), ∃ u : FHom E E, ∀ x, jA (u.u (ainfObj (ϖ.field a)) x) = (OfCrystal.mulZ (resF T (ϖ.field a)) c).lTensor (WCb l) (jA x)` using `fun c => by`. Take `⟨u, hu, -⟩` from `(BS l (ϖ.field a) (ainfObj (ϖ.field a)) (ainfId (ϖ.field a)) hR.ainf).2 _ _ _ _ E E jA jA hR hR (OfCrystal.mulZ (resF T (ϖ.field a)) c) fun g x => (((resF T (ϖ.field a)).actT g).map_smul c x).symm`.

Conclude with `⟨u, hu⟩`. Use `choose oE hoE using hO`. Take `⟨b, hb, hgen⟩` from `GlobalTheory.T.breuilKisinPrism_crystal_basis_and_span l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P (resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) E jA hR hIm oE hoE`. Take `⟨sh, φ₂, hsh, hφC, hφsh⟩` from `GlobalTheory.TaylorShift.shift_frob_exists l ↥LL.1`. Take `⟨PP, S₀, p₀, p₁, δ, κ, κ₀, hPPI, hδ, hκ₀, hκp, hκφ, hSS, -, hev⟩` from `GlobalTheory.T.exists_crystalline_prisms l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ hl2 sh φ₂ hsh hφC hφsh`.

Take `⟨Q, _, c, y, hε⟩` from `GlobalTheory.CrysGal.exists_rep (A := PP.A) (fun c i => (oE c).u PP (E.tr p₀ (b i))) (fun j => E.tr p₁ (b j)) (fun j => GlobalTheory.CrysGal.mem_span_tr E p₀ oE b hgen _)`. Establish `hF` using `GlobalTheory.T.crystal_changeOfBasis_frobenius_compat l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P (resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) E jA hR hIm oE hoE b hb sh φ₂ hsh hφC PP p₀ p₁ κ hPPI hκp hκφ Q c y hε`. Establish `hD` using `GlobalTheory.T.prismCrystal_changeOfBasis_constantCoeff_eq_one l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P (resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) E jA hR hIm oE hoE b hb PP S₀ p₀ p₁ δ κ κ₀ hδ hκ₀ (fun τ x => (hκp τ x).1) Q c y hε`. Establish `hK` using `GlobalTheory.T.frobeniusStratification_coeff_eq_connection_pow ↥(OL LL) ↥LL.1 l e a ι P sh φ₂ hsh hφC hφsh _ hD hF`. Take `⟨Cr, eC, h, hCrI, heCφ, heCh⟩` from `GlobalTheory.AcrisPrism.main l (ϖ.field a)`.

Establish `hev'` using `hev Cr eC h hCrI heCφ heCh g`. Take `⟨ev, hevs⟩` from `hev'`. Establish `hG` using `GlobalTheory.T.galoisMatrix_eq_crystal_changeOfBasis_value l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P (resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) E jA hR hIm oE hoE b hb PP p₀ p₁ Q c y hε Cr eC h heCh g ev hevs.1 hevs.2.1`. Take `⟨Γ, hΓ, hΓeq⟩` from `hG`. Establish `hconv` using `hevs.2.2`.

Use `⟨Γ, hΓ, fun i j r => ?_⟩` and prove the remaining obligations. Establish `hG` using `GlobalTheory.CrysGal.comb_S (e := e) (c i j) (fun τ q => κ τ (y i j q)) (fun k τ => ⟨_, hS τ j k i⟩) (fun q k τ => ⟨_, hSS τ (y i j q) k⟩) (fun k τ => (congrArg ((X : (↥LL.1)⟦X⟧) ^ k * ·) (hK τ k i j)).symm) (fun q k τ => rfl)`. Conclude with `GlobalTheory.CrysGal.conv_comb (thetaW a LL) ϖ g (c i j) (fun q => eC (ev.f (y i j q))) (fun q k τ => ⟨_, hSS τ (y i j q) k⟩) (fun k τ => ⟨_, hS τ j k i⟩) hG r (fun q => hconv (y i j q) r) _ (hΓeq i j)`.
-/
theorem galois_taylor_basis : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∀ (hS : ∀ (τ : ZMod a) (j : ι) (k : ℕ) (i : ι), (X : (↥LL.1)⟦X⟧) ^ k * (P.mxInv τ *ᵥ (P.nabla ^ k) (P.phi (bas j)) τ) i ∈ S (↥(OL LL)) (↥LL.1) e) (g : ↥(GK (ϖ.field a))), ∃ Γ, (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)).IsLMat (g : GQ l) g Γ ∧ ∀ (i j : ι) (r : ℕ), ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l ↥(OL LL)) ^ r ∣ toOCr l ↥(OL LL) (Γ i j) - ∑ k ∈ Finset.range n, ϖ.muDiv a ↥(OL LL) g k * ϖ.iC (thetaW a LL) ↥LL.1 (fun τ => ⟨_, hS τ j k i⟩) := by
  intro BS l _ a e _ _ ϖ LL _ _ hl2 ι _ _ P T I hBK hS g
  letI := zlLat (resF T (ϖ.field a))
  obtain ⟨E, jA, hR, hIm⟩ := hBK
  have hO : ∀ c : ↥(OL LL), ∃ u : FHom E E, ∀ x, jA (u.u (ainfObj (ϖ.field a)) x) =
      (OfCrystal.mulZ (resF T (ϖ.field a)) c).lTensor (WCb l) (jA x) := fun c => by
    obtain ⟨u, hu, -⟩ := (BS l (ϖ.field a) (ainfObj (ϖ.field a)) (ainfId (ϖ.field a)) hR.ainf).2 _ _ _ _ E E jA jA hR hR
      (OfCrystal.mulZ (resF T (ϖ.field a)) c) fun g x => (((resF T (ϖ.field a)).actT g).map_smul c x).symm
    exact ⟨u, hu⟩
  choose oE hoE using hO
  obtain ⟨b, hb, hgen⟩ := GlobalTheory.T.breuilKisinPrism_crystal_basis_and_span l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P (resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) E jA hR hIm oE hoE
  obtain ⟨sh, φ₂, hsh, hφC, hφsh⟩ := GlobalTheory.TaylorShift.shift_frob_exists l ↥LL.1
  obtain ⟨PP, S₀, p₀, p₁, δ, κ, κ₀, hPPI, hδ, hκ₀, hκp, hκφ, hSS, -, hev⟩ :=
    GlobalTheory.T.exists_crystalline_prisms l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ hl2 sh φ₂ hsh hφC hφsh
  obtain ⟨Q, _, c, y, hε⟩ := GlobalTheory.CrysGal.exists_rep (A := PP.A)
    (fun c i => (oE c).u PP (E.tr p₀ (b i))) (fun j => E.tr p₁ (b j))
    (fun j => GlobalTheory.CrysGal.mem_span_tr E p₀ oE b hgen _)
  have hF := GlobalTheory.T.crystal_changeOfBasis_frobenius_compat l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P (resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) E jA hR hIm oE hoE b hb sh φ₂ hsh hφC PP p₀ p₁ κ hPPI hκp hκφ Q c y hε
  have hD := GlobalTheory.T.prismCrystal_changeOfBasis_constantCoeff_eq_one l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P (resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) E jA hR hIm oE hoE b hb PP S₀ p₀ p₁ δ κ κ₀ hδ hκ₀ (fun τ x => (hκp τ x).1) Q c y hε
  have hK := GlobalTheory.T.frobeniusStratification_coeff_eq_connection_pow ↥(OL LL) ↥LL.1 l e a ι P sh φ₂ hsh hφC hφsh _ hD hF
  obtain ⟨Cr, eC, h, hCrI, heCφ, heCh⟩ := GlobalTheory.AcrisPrism.main l (ϖ.field a)
  have hev' := hev Cr eC h hCrI heCφ heCh g
  obtain ⟨ev, hevs⟩ := hev'
  have hG := GlobalTheory.T.galoisMatrix_eq_crystal_changeOfBasis_value l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P (resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) E jA hR hIm oE hoE b hb PP p₀ p₁ Q c y hε Cr eC h heCh g ev hevs.1 hevs.2.1
  obtain ⟨Γ, hΓ, hΓeq⟩ := hG
  have hconv := hevs.2.2
  refine ⟨Γ, hΓ, fun i j r => ?_⟩
  have hG := GlobalTheory.CrysGal.comb_S (e := e) (c i j) (fun τ q => κ τ (y i j q))
    (fun k τ => ⟨_, hS τ j k i⟩) (fun q k τ => ⟨_, hSS τ (y i j q) k⟩)
    (fun k τ => (congrArg ((X : (↥LL.1)⟦X⟧) ^ k * ·) (hK τ k i j)).symm) (fun q k τ => rfl)
  exact GlobalTheory.CrysGal.conv_comb (thetaW a LL) ϖ g (c i j) (fun q => eC (ev.f (y i j q)))
    (fun q k τ => ⟨_, hSS τ (y i j q) k⟩) (fun k τ => ⟨_, hS τ j k i⟩) hG r (fun q => hconv (y i j q) r)
    _ (hΓeq i j)

end GlobalTheory.CrysGal
