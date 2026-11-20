import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichKernelRangeExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing

set_option autoImplicit false
noncomputable section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.DatumOfMatrices

def sumIdx {d k h : ℕ} (hdk : d + k = h) : Fin d ⊕ Fin k ≃ Fin h :=
  finSumFinEquiv.trans (finCongr hdk)

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

def datumOf (ε : PreTilt O p) {d k h : ℕ} (hdk : d + k = h)
    (Fa : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O)) (Ga : Matrix (Fin h) (Fin d ⊕ Fin k) (Ainf p O))
    (Ψ Ψ' : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O))
    (hGF : Ga * Fa = Sandwich.mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O)))
    (hF : Fa = Ψ * Fa.map (phiInv p O))
    (hΨ : Ψ * Ψ' = xi ε • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O))) :
    Datum ε h ℤ_[p] where
  F := Fa.submatrix (sumIdx hdk).symm id
  G := Ga.submatrix id (sumIdx hdk).symm
  Ψ := Ψ.submatrix (sumIdx hdk).symm (sumIdx hdk).symm
  Ψ' := Ψ'.submatrix (sumIdx hdk).symm (sumIdx hdk).symm
  ρT := Algebra.ofId _ _
  ρM := (RingHom.mapMatrix (ofPadic p O)).comp (algebraMap _ _)
  G_mul_F := by
    rw [Matrix.submatrix_mul_equiv, hGF]
    rfl
  F_eq := by
    calc Fa.submatrix (sumIdx hdk).symm id
        = (Ψ * Fa.map (phiInv p O)).submatrix (sumIdx hdk).symm id :=
          congrArg (fun M => M.submatrix (sumIdx hdk).symm id) hF
      _ = Ψ.submatrix (sumIdx hdk).symm (sumIdx hdk).symm *
            (Fa.map (phiInv p O)).submatrix (sumIdx hdk).symm id :=
          (Matrix.submatrix_mul_equiv _ _ _ _ _).symm
      _ = _ := by rw [Matrix.submatrix_map]
  Ψ_mul := by
    rw [Matrix.submatrix_mul_equiv, hΨ]
    refine Matrix.ext fun i j => ?_
    simp [Matrix.one_apply]
  F_act := by
    intro a
    refine Matrix.ext fun i j => ?_
    simp [Algebra.ofId_apply, Matrix.algebraMap_matrix_apply, Matrix.mul_apply, Matrix.one_apply,
      apply_ite (ofPadic p O), mul_ite, ite_mul, mul_comm]

end GlobalTheory.DatumOfMatrices

namespace GlobalTheory.DatumOfMatrices

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O]

/- English proof (translation)
Apply `(G.pairing_flip_bijective C).1` to reduce the goal to its premises. Use `tb.ext fun m => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.flip_apply, LinearMap.flip_apply, map_sum]`. Establish `hlin : ∀ (t : G.Tate) (c : ℤ_[p]) (ψ : G.dual.Tate), epsPairing hε G t (c • ψ) = c * epsPairing hε G t ψ`. Introduce `t c ψ`.

Simplify using `[epsPairing, map_smul]`. Simplify using `only [← epsPairing_smul hε, hlin, hpair, mul_ite, mul_one, mul_zero, ite_smul, zero_smul]`. Simplify using the standard rewrite rules.
-/
theorem eq_sum_epsPairing_smul {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (C : Type) [Field C]
    [Algebra O C] [IsIntegrallyClosedIn O C] [IsAlgClosed C] [CharZero C] (G : PDivGroup p O)
    (tb : Module.Basis (Fin G.height) ℤ_[p] G.Tate) (χ : Fin G.height → G.dual.Tate)
    (hpair : ∀ m m', epsPairing hε G (tb m) (χ m') = if m = m' then 1 else 0)
    (χ0 : G.dual.Tate) : χ0 = ∑ m', epsPairing hε G (tb m') χ0 • χ m' := by
  classical
  apply (G.pairing_flip_bijective C).1
  refine tb.ext fun m => ?_
  rw [LinearMap.flip_apply, LinearMap.flip_apply, map_sum]
  have hlin : ∀ (t : G.Tate) (c : ℤ_[p]) (ψ : G.dual.Tate),
      epsPairing hε G t (c • ψ) = c * epsPairing hε G t ψ := by
    intro t c ψ
    simp [epsPairing, map_smul]
  simp only [← epsPairing_smul hε, hlin, hpair, mul_ite, mul_one, mul_zero, ite_smul, zero_smul]
  simp

end GlobalTheory.DatumOfMatrices

namespace GlobalTheory.DatumOfMatrices

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ _ hv ε hε G d k hdk tb χ w lb Fa Ga Ψ Ψ' hGF hF hΨ hpair hθl hθr hGr hdlog`. Use `hv.isFractionRing` as an intermediate fact. Use `hv.isIntegrallyClosed` as an intermediate fact. Establish `: IsIntegrallyClosedIn O C` using `(isIntegrallyClosed_iff_isIntegrallyClosedIn C).1 inferInstance`. Take `⟨hfin, hproj⟩` from `GlobalTheory.PDiv.omega_finite_projective p C v O hv G.dual`.

Use `haveI := hfin`. Use `haveI := hproj`. Establish `hζ : IsPrimitiveRoot (root ε).untilt p` using `by simpa [zeta] using hε 1`. Use `set σ := sumIdx hdk with hσ`. Use `set D := datumOf ε hdk Fa Ga Ψ Ψ' hGF hF hΨ with hD`.

Establish `hal : ∀ y a, D.al y (σ a) = ∑ m, WittVector.fontaineTheta O p (Fa a m) * y m`. Introduce `y a`. Simplify using `[D, datumOf, Datum.al, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, σ]`. Establish `hbb : ∀ y m', D.bb y m' = ∑ i, WittVector.fontaineTheta O p (Ga m' (Sum.inl i)) * y (σ (Sum.inl i))`. Introduce `y m'`.

Establish `h1 : D.bb y m' = ∑ a, WittVector.fontaineTheta O p (Ga m' a) * y (σ a)`. Simplify using `only [D, datumOf, Datum.bb, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.submatrix_apply, id]`. Rewrite using `[← Equiv.sum_comp σ]`. Simplify using `[σ]`. Rewrite using `[h1, Fintype.sum_sum_type]`.

Simplify using `[hGr]`. Establish `hbC : ∀ z : Fin G.height → O, GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.bC C D (fun l => algebraMap O C (z l)) = fun m' => algebraMap O C (D.bb z m')`. Introduce `z`. Use function extensionality and compare the values at `m'`. Simplify using `[GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.bC, GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.redC, Datum.bb, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, map_sum, map_mul]`.

Establish `halC : ∀ (y : Fin G.height → C) a, GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.alC C D y (σ a) = ∑ m, algebraMap O C (WittVector.fontaineTheta O p (Fa a m)) * y m`. Introduce `y a`. Simplify using `[GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.alC, GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.redC, D, datumOf, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, σ]`. Set `projL : (Fin G.height → O) →ₗ[O] (Fin d → O)` to `LinearMap.funLeft O O (σ ∘ Sum.inl)`. Set `projR : (Fin G.height → O) →ₗ[O] (Fin k → O)` to `LinearMap.funLeft O O (σ ∘ Sum.inr)`.

Establish `hFil : D.Fil = LinearMap.ker projL`. Use extensionality with `m`. Express the relevant statement in the definitionally equal form `D.bb m = 0 ↔ projL m = 0`. Prove the components needed by the constructor for the conclusion. Introduce `hm`.

Establish `hker : (fun l => algebraMap O C (m l)) ∈ LinearMap.ker (GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.bC C D)`. Rewrite using `[LinearMap.mem_ker, hbC, hm]`. Use function extensionality and compare the values at `m'`. Simplify using the standard rewrite rules. Rewrite `hker` using `[(GlobalTheory.DetInv.ker_bC_eq_range_alC_and_ker_alC_eq_range_bC p C v O hv ε hζ ℤ_[p] G.height D).1]`.

Take `⟨y, hy⟩` from `hker`. Use function extensionality and compare the values at `i`. Apply `hv.hom_inj` to reduce the goal to its premises. Establish `h1` using `congrFun hy (σ (Sum.inl i))`. Rewrite `h1` using `[halC]`.

Simplify using `only [hθl, map_zero, zero_mul, Finset.sum_const_zero] at h1`. Simplify `h1.symm` using `[projL]`. Introduce `hm`. Use function extensionality and compare the values at `m'`. Rewrite using `[hbb]`.

Establish `h2 : ∀ i, m (σ (Sum.inl i)) = 0` using `fun i => congrFun hm i`. Simplify using `[h2]`. Set `coordE : G.dual.omega ≃ₗ[O] (Fin k → O)` to `Module.evalEquiv O G.dual.omega ≪≫ₗ lb.dualBasis.equivFun`. Establish `hcoordE : ∀ x j, coordE x j = lb j x`. Introduce `x j`.

Simplify using `[coordE]`. Set `incl : (Fin k → O) →ₗ[O] (Fin G.height → O)` to `{ toFun := fun c l => Sum.elim (0 : Fin d → O) c (σ.symm l) map_add' := by`. Introduce `a b`. Use function extensionality and compare the values at `l`. Apply the tactic sequence `rcases h : σ.symm l with i | j <;> simp [h]`.

Use the proof step `map_smul' := by`. Introduce `r a`. Use function extensionality and compare the values at `l`. Apply the tactic sequence `rcases h : σ.symm l with i | j <;> simp [h] }`. Establish `hincl : ∀ c a, incl c (σ a) = Sum.elim (0 : Fin d → O) c a`.

Introduce `c a`. Simplify using `[incl]`. Establish `hinclF : ∀ c, incl c ∈ D.Fil`. Introduce `c`. Rewrite using `[hFil, LinearMap.mem_ker]`.

Use function extensionality and compare the values at `i`. Simplify using `[projL, hincl]`. Set `filE : (Fin k → O) ≃ₗ[O] D.Fil` to `{ toFun := fun c => ⟨incl c, hinclF c⟩ map_add' := by intro a b; ext1; simp map_smul' := by intro r a; ext1; simp invFun := fun m => projR m left_inv := by`. Introduce `c`. Use function extensionality and compare the values at `j`.

Simplify using `[projR, hincl]`. Use `right_inv := by`. Introduce `m`. Use `ext1`. Use function extensionality and compare the values at `l`.

Take `⟨a, rfl⟩` from `σ.surjective l`. Establish `hFil' : ∀ y, y ∈ D.Fil ↔ projL y = 0` using `fun y => by rw [hFil, LinearMap.mem_ker]`. Establish `hm : projL (m : Fin G.height → O) = 0` using `(hFil' _).1 m.2`. Break down `a with i | j` into its components or cases. Simplify using `only [hincl, Sum.elim_inl, Pi.zero_apply]`.

Conclude with `(congrFun hm i).symm`. Simplify using `[hincl, projR] }`. Set `fil : G.dual.omega ≃ₗ[O] D.Fil` to `coordE ≪≫ₗ filE`. Establish `hfil : ∀ x a, (fil x : Fin G.height → O) (σ a) = Sum.elim (0 : Fin d → O) (fun j => lb j x) a`. Introduce `x a`.

Express the relevant statement in the definitionally equal form `incl (coordE x) (σ a) = _`. Rewrite using `[hincl]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Conclude with `hcoordE x j`.

Establish `hsurjL : Function.Surjective projL`. Introduce `c`. Use `⟨fun l => Sum.elim c (0 : Fin k → O) (σ.symm l), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `[projL]`.

Set `lie : ((Fin G.height → O) ⧸ D.Fil) ≃ₗ[O] G.Lie` to `Submodule.quotEquivOfEq _ _ hFil ≪≫ₗ projL.quotKerEquivOfSurjective hsurjL ≪≫ₗ w.dualBasis.equivFun.symm`. Establish `hlie : ∀ m i, lie (D.Fil.mkQ m) (w i) = m (σ (Sum.inl i))`. Introduce `m i`. Express the relevant statement in the definitionally equal form `(w.dualBasis.equivFun.symm (projL.quotKerEquivOfSurjective hsurjL (Submodule.quotEquivOfEq _ _ hFil (D.Fil.mkQ m)))) (w i) = _`. Rewrite using `[← Module.Basis.dualBasis_equivFun, LinearEquiv.apply_symm_apply]`.

Both sides reduce to the same expression. Establish `hexpHT : ∀ j t, lb j (hodgeTate G t) = ∑ m, lb j (hodgeTate G (tb m)) * padicToO p O (tb.repr t m)`. Introduce `j t`. Use `conv_lhs => rw [← tb.sum_repr t]`. Rewrite using `[map_sum (hodgeTate G), map_sum (lb j)]`.

Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[hodgeTate_smul (padicToO p O), map_smul, smul_eq_mul, mul_comm]`. Establish `hχexp : ∀ χ0 : G.dual.Tate, χ0 = ∑ m', epsPairing hε G (tb m') χ0 • χ m'` using `eq_sum_epsPairing_smul hε C G tb χ hpair`. Establish `he : ∀ i, (tb.equivFun).symm (Pi.single i 1) = tb i`. Introduce `i`.

Simplify using the standard rewrite rules. Use `⟨D, tb.equivFun, fil, lie, fun t => ?_, fun x χ0 => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `l`. Take `⟨a, rfl⟩` from `σ.surjective l`. Rewrite using `[hal, hfil]`.

Break down `a with i | j` into its components or cases. Simplify using `[hθl]`. Simplify using `only [Sum.elim_inr, hθr, toO, Module.Basis.equivFun_apply]`. Rewrite using `[hexpHT j t]`. Take `⟨m, hm⟩` from `D.Fil.mkQ_surjective (lie.symm x)`.

Establish `hx : x = lie (D.Fil.mkQ m)` using `by rw [hm, LinearEquiv.apply_symm_apply]`. Substitute `hx` using the available equality. Rewrite using `[LinearEquiv.symm_apply_apply]`. Establish `hbq : bQuot D (D.Fil.mkQ m) = D.bb m` using `rfl`. Rewrite using `[hbq]`.

Establish `hbbx : ∀ m', D.bb m m' = lie (D.Fil.mkQ m) (dlog G (χ m'))`. Introduce `m'`. Rewrite using `[hbb, hdlog, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hlie, smul_eq_mul]`.

Rewrite using `[pairingO]`. Simplify using `only [hbbx, he]`. Use `conv_rhs => rw [hχexp χ0]`. Rewrite using `[map_sum (dlog G), map_sum]`. Use `Finset.sum_congr rfl fun m' _ => ?_` and prove the remaining obligations.

Rewrite using `[dlog_smul (padicToO p O), map_smul, smul_eq_mul, mul_comm]`.
-/
theorem hasDatum_of_matrices : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (G : PDivGroup p O) (d k : ℕ), d + k = G.height → ∀ (tb : Module.Basis (Fin G.height) ℤ_[p] G.Tate) (χ : Fin G.height → G.dual.Tate) (w : Module.Basis (Fin d) O G.omega) (lb : Module.Basis (Fin k) O G.dual.Lie) (Fa : Matrix (Fin d ⊕ Fin k) (Fin G.height) (Ainf p O)) (Ga : Matrix (Fin G.height) (Fin d ⊕ Fin k) (Ainf p O)) (Ψ Ψ' : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)), Ga * Fa = Sandwich.mu ε • (1 : Matrix (Fin G.height) (Fin G.height) (Ainf p O)) → Fa = Ψ * Fa.map (phiInv p O) → Ψ * Ψ' = xi ε • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) → (∀ m m', epsPairing hε G (tb m) (χ m') = if m = m' then 1 else 0) → (∀ i m, WittVector.fontaineTheta O p (Fa (Sum.inl i) m) = 0) → (∀ j m, WittVector.fontaineTheta O p (Fa (Sum.inr j) m) = lb j (hodgeTate G (tb m))) → (∀ m j, WittVector.fontaineTheta O p (Ga m (Sum.inr j)) = 0) → (∀ m, dlog G (χ m) = ∑ i, WittVector.fontaineTheta O p (Ga m (Sum.inl i)) • w i) → HasDatum hε G := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G d k hdk tb χ w lb Fa Ga Ψ Ψ' hGF hF hΨ hpair hθl hθr
    hGr hdlog
  classical
  have := hv.isFractionRing
  have := hv.isIntegrallyClosed
  have : IsIntegrallyClosedIn O C :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn C).1 inferInstance
  obtain ⟨hfin, hproj⟩ := GlobalTheory.PDiv.omega_finite_projective p C v O hv G.dual
  haveI := hfin
  haveI := hproj
  have hζ : IsPrimitiveRoot (root ε).untilt p := by simpa [zeta] using hε 1
  set σ := sumIdx hdk with hσ
  set D := datumOf ε hdk Fa Ga Ψ Ψ' hGF hF hΨ with hD
  have hal : ∀ y a, D.al y (σ a) = ∑ m, WittVector.fontaineTheta O p (Fa a m) * y m := by
    intro y a
    simp [D, datumOf, Datum.al, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, σ]
  have hbb : ∀ y m', D.bb y m' =
      ∑ i, WittVector.fontaineTheta O p (Ga m' (Sum.inl i)) * y (σ (Sum.inl i)) := by
    intro y m'
    have h1 : D.bb y m' = ∑ a, WittVector.fontaineTheta O p (Ga m' a) * y (σ a) := by
      simp only [D, datumOf, Datum.bb, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        Matrix.map_apply, Matrix.submatrix_apply, id]
      rw [← Equiv.sum_comp σ]
      simp [σ]
    rw [h1, Fintype.sum_sum_type]
    simp [hGr]

  have hbC : ∀ z : Fin G.height → O, GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.bC C D (fun l => algebraMap O C (z l)) =
      fun m' => algebraMap O C (D.bb z m') := by
    intro z
    funext m'
    simp [GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.bC, GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.redC, Datum.bb, Matrix.toLin'_apply, Matrix.mulVec,
      dotProduct, map_sum, map_mul]
  have halC : ∀ (y : Fin G.height → C) a, GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.alC C D y (σ a) =
      ∑ m, algebraMap O C (WittVector.fontaineTheta O p (Fa a m)) * y m := by
    intro y a
    simp [GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.alC, GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.redC, D, datumOf, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, σ]
  let projL : (Fin G.height → O) →ₗ[O] (Fin d → O) := LinearMap.funLeft O O (σ ∘ Sum.inl)
  let projR : (Fin G.height → O) →ₗ[O] (Fin k → O) := LinearMap.funLeft O O (σ ∘ Sum.inr)
  have hFil : D.Fil = LinearMap.ker projL := by
    ext m
    change D.bb m = 0 ↔ projL m = 0
    constructor
    · intro hm
      have hker : (fun l => algebraMap O C (m l)) ∈ LinearMap.ker (GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.bC C D) := by
        rw [LinearMap.mem_ker, hbC, hm]
        funext m'
        simp
      rw [(GlobalTheory.DetInv.ker_bC_eq_range_alC_and_ker_alC_eq_range_bC p C v O hv ε hζ ℤ_[p]
        G.height D).1] at hker
      obtain ⟨y, hy⟩ := hker
      funext i
      apply hv.hom_inj
      have h1 := congrFun hy (σ (Sum.inl i))
      rw [halC] at h1
      simp only [hθl, map_zero, zero_mul, Finset.sum_const_zero] at h1
      simpa [projL] using h1.symm
    · intro hm
      funext m'
      rw [hbb]
      have h2 : ∀ i, m (σ (Sum.inl i)) = 0 := fun i => congrFun hm i
      simp [h2]

  let coordE : G.dual.omega ≃ₗ[O] (Fin k → O) :=
    Module.evalEquiv O G.dual.omega ≪≫ₗ lb.dualBasis.equivFun
  have hcoordE : ∀ x j, coordE x j = lb j x := by
    intro x j
    simp [coordE]
  let incl : (Fin k → O) →ₗ[O] (Fin G.height → O) :=
    { toFun := fun c l => Sum.elim (0 : Fin d → O) c (σ.symm l)
      map_add' := by
        intro a b
        funext l
        rcases h : σ.symm l with i | j <;> simp [h]
      map_smul' := by
        intro r a
        funext l
        rcases h : σ.symm l with i | j <;> simp [h] }
  have hincl : ∀ c a, incl c (σ a) = Sum.elim (0 : Fin d → O) c a := by
    intro c a
    simp [incl]
  have hinclF : ∀ c, incl c ∈ D.Fil := by
    intro c
    rw [hFil, LinearMap.mem_ker]
    funext i
    simp [projL, hincl]
  let filE : (Fin k → O) ≃ₗ[O] D.Fil :=
    { toFun := fun c => ⟨incl c, hinclF c⟩
      map_add' := by intro a b; ext1; simp
      map_smul' := by intro r a; ext1; simp
      invFun := fun m => projR m
      left_inv := by
        intro c
        funext j
        simp [projR, hincl]
      right_inv := by
        intro m
        ext1
        funext l
        obtain ⟨a, rfl⟩ := σ.surjective l
        have hFil' : ∀ y, y ∈ D.Fil ↔ projL y = 0 := fun y => by rw [hFil, LinearMap.mem_ker]
        have hm : projL (m : Fin G.height → O) = 0 := (hFil' _).1 m.2
        rcases a with i | j
        · simp only [hincl, Sum.elim_inl, Pi.zero_apply]
          exact (congrFun hm i).symm
        · simp [hincl, projR] }
  let fil : G.dual.omega ≃ₗ[O] D.Fil := coordE ≪≫ₗ filE
  have hfil : ∀ x a, (fil x : Fin G.height → O) (σ a) =
      Sum.elim (0 : Fin d → O) (fun j => lb j x) a := by
    intro x a
    change incl (coordE x) (σ a) = _
    rw [hincl]
    congr 1
    funext j
    exact hcoordE x j
  have hsurjL : Function.Surjective projL := by
    intro c
    refine ⟨fun l => Sum.elim c (0 : Fin k → O) (σ.symm l), ?_⟩
    funext i
    simp [projL]
  let lie : ((Fin G.height → O) ⧸ D.Fil) ≃ₗ[O] G.Lie :=
    Submodule.quotEquivOfEq _ _ hFil ≪≫ₗ projL.quotKerEquivOfSurjective hsurjL ≪≫ₗ
      w.dualBasis.equivFun.symm
  have hlie : ∀ m i, lie (D.Fil.mkQ m) (w i) = m (σ (Sum.inl i)) := by
    intro m i
    change (w.dualBasis.equivFun.symm (projL.quotKerEquivOfSurjective hsurjL
      (Submodule.quotEquivOfEq _ _ hFil (D.Fil.mkQ m)))) (w i) = _
    rw [← Module.Basis.dualBasis_equivFun, LinearEquiv.apply_symm_apply]
    rfl

  have hexpHT : ∀ j t, lb j (hodgeTate G t) =
      ∑ m, lb j (hodgeTate G (tb m)) * padicToO p O (tb.repr t m) := by
    intro j t
    conv_lhs => rw [← tb.sum_repr t]
    rw [map_sum (hodgeTate G), map_sum (lb j)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hodgeTate_smul (padicToO p O), map_smul, smul_eq_mul, mul_comm]
  have hχexp : ∀ χ0 : G.dual.Tate, χ0 = ∑ m', epsPairing hε G (tb m') χ0 • χ m' :=
    eq_sum_epsPairing_smul hε C G tb χ hpair
  have he : ∀ i, (tb.equivFun).symm (Pi.single i 1) = tb i := by
    intro i
    simp
  refine ⟨D, tb.equivFun, fil, lie, fun t => ?_, fun x χ0 => ?_⟩
  · funext l
    obtain ⟨a, rfl⟩ := σ.surjective l
    rw [hal, hfil]
    rcases a with i | j
    · simp [hθl]
    · simp only [Sum.elim_inr, hθr, toO, Module.Basis.equivFun_apply]
      rw [hexpHT j t]
  · obtain ⟨m, hm⟩ := D.Fil.mkQ_surjective (lie.symm x)
    have hx : x = lie (D.Fil.mkQ m) := by rw [hm, LinearEquiv.apply_symm_apply]
    subst hx
    rw [LinearEquiv.symm_apply_apply]
    have hbq : bQuot D (D.Fil.mkQ m) = D.bb m := rfl
    rw [hbq]
    have hbbx : ∀ m', D.bb m m' = lie (D.Fil.mkQ m) (dlog G (χ m')) := by
      intro m'
      rw [hbb, hdlog, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, hlie, smul_eq_mul]
    rw [pairingO]
    simp only [hbbx, he]
    conv_rhs => rw [hχexp χ0]
    rw [map_sum (dlog G), map_sum]
    refine Finset.sum_congr rfl fun m' _ => ?_
    rw [dlog_smul (padicToO p O), map_smul, smul_eq_mul, mul_comm]

end GlobalTheory.DatumOfMatrices
