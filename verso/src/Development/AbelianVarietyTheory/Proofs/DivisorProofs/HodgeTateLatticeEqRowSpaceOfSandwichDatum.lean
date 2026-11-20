import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfGhostThetaFrobIterValuesXiMuPadicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfTeichmullerMinusOneDvdOfGhostComponentsZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularOfMulEqSmul

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat.RowSpace

section SlopeTestRemainingChoices

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

variable (p O) in

def ghostHom (n : ℕ) : Ainf p O →+* O where
  toFun := ghost p O n
  map_one' := by
    show WittVector.fontaineTheta O p (_ ^[n] 1) = 1
    rw [iterate_map_one, map_one]
  map_mul' := ghost_mul n
  map_zero' := ghost_zero n
  map_add' := ghost_add n

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ghostHom_apply (n : ℕ) (a : Ainf p O) : ghostHom p O n a = ghost p O n a := rfl

def dotLin {R : Type} [CommRing R] {h : ℕ} (v : Fin h → R) : (Fin h → R) →ₗ[R] R where
  toFun w := v ⬝ᵥ w
  map_add' := dotProduct_add v
  map_smul' c w := by simp [dotProduct_smul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dotLin_apply {R : Type} [CommRing R] {h : ℕ} (v w : Fin h → R) : dotLin v w = v ⬝ᵥ w := rfl

def toA {G : PDivGroup p O} {h : ℕ} (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) (t : G.Tate) :
    Fin h → Ainf p O := fun i => ofPadic p O (e t i)

/- English proof (translation)
Use extensionality with `i`. Simplify using `[toA]`.
-/
theorem toA_add {G : PDivGroup p O} {h : ℕ} (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p]))
    (t t' : G.Tate) : toA e (t + t') = toA e t + toA e t' := by
  ext i; simp [toA]

/- English proof (translation)
Use extensionality with `i`. Simplify using `[toA]`.
-/
theorem toA_smul {G : PDivGroup p O} {h : ℕ} (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p]))
    (c : ℤ_[p]) (t : G.Tate) : toA e (c • t) = ofPadic p O c • toA e t := by
  ext i; simp [toA]

/- English proof (translation)
Apply the tactic sequence `ext j; by_cases hij : j = i <;> simp [toA, Pi.single_apply, hij]`.
-/
theorem toA_single {G : PDivGroup p O} {h : ℕ} (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p]))
    (i : Fin h) : toA e (e.symm (Pi.single i 1)) = Pi.single i 1 := by
  ext j; by_cases hij : j = i <;> simp [toA, Pi.single_apply, hij]

/- English proof (translation)
Apply the tactic sequence `ext j; by_cases hij : j = i <;> simp [toO, Pi.single_apply, hij]`.
-/
theorem toO_single {G : PDivGroup p O} {h : ℕ} (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p]))
    (i : Fin h) : toO e (e.symm (Pi.single i 1)) = Pi.single i 1 := by
  ext j; by_cases hij : j = i <;> simp [toO, Pi.single_apply, hij]

def rowMap {G : PDivGroup p O} {h : ℕ} (F : Matrix (Fin h) (Fin h) (Ainf p O))
    (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) : (Fin h → Ainf p O) →ₗ[Ainf p O] TDual G where
  toFun r :=
    { toFun := fun t => r ⬝ᵥ (F *ᵥ toA e t)
      map_add' := fun t t' => by rw [toA_add, mulVec_add, dotProduct_add]
      map_smul' := fun c t => by
        rw [toA_smul, mulVec_smul, dotProduct_smul] }
  map_add' r r' := LinearMap.ext fun t => add_dotProduct r r' _
  map_smul' a r := LinearMap.ext fun t => smul_dotProduct a r _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rowMap_apply {G : PDivGroup p O} {h : ℕ} (F : Matrix (Fin h) (Fin h) (Ainf p O))
    (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) (r : Fin h → Ainf p O) (t : G.Tate) :
    rowMap F e r t = r ⬝ᵥ (F *ᵥ toA e t) := rfl

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ⟨1, by rw [Matrix.one_mul]; rfl⟩`. Consider the case `succ n ih`. Take `⟨X, hX⟩` from `ih`. Use `⟨D.Ψ.map (ghostHom p O (n + 1)) * X, ?_⟩` and prove the remaining obligations.

Establish `e1 : D.F.map (ghostHom p O (n + 1)) = D.Ψ.map (ghostHom p O (n + 1)) * D.F.map (ghostHom p O n)` using `by conv_lhs => rw [D.F_eq]`. Rewrite using `[Matrix.map_mul, Matrix.map_map]`. Use `congr 1`. Use extensionality with `i j`. Conclude with `hphi n _`.

Rewrite using `[e1, hX, Matrix.mul_assoc]`.
-/
theorem F_map_ghost {ε : PreTilt O p} {h : ℕ} (D : Datum ε h ℤ_[p])
    (hphi : ∀ n a, ghost p O (n + 1) (phiInv p O a) = ghost p O n a) (n : ℕ) :
    ∃ X : Matrix (Fin h) (Fin h) O,
      D.F.map (ghostHom p O n) = X * D.F.map (WittVector.fontaineTheta O p) := by
  induction n with
  | zero => exact ⟨1, by rw [Matrix.one_mul]; rfl⟩
  | succ n ih =>
    obtain ⟨X, hX⟩ := ih
    refine ⟨D.Ψ.map (ghostHom p O (n + 1)) * X, ?_⟩
    have e1 : D.F.map (ghostHom p O (n + 1)) =
        D.Ψ.map (ghostHom p O (n + 1)) * D.F.map (ghostHom p O n) := by
      conv_lhs => rw [D.F_eq]
      rw [Matrix.map_mul, Matrix.map_map]
      congr 1
      ext i j
      exact hphi n _
    rw [e1, hX, Matrix.mul_assoc]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ⟨1, by rw [Matrix.mul_one]; rfl⟩`. Consider the case `succ n ih`. Take `⟨Y, hY⟩` from `ih`. Use `⟨Y * D.Ψ'.map (ghostHom p O (n + 1)), ?_⟩` and prove the remaining obligations.

Establish `e1 : D.G.map (ghostHom p O (n + 1)) = D.G.map (ghostHom p O n) * D.Ψ'.map (ghostHom p O (n + 1))` using `by conv_lhs => rw [hG]`. Rewrite using `[Matrix.map_mul, Matrix.map_map]`. Use `congr 1`. Use extensionality with `i j`. Conclude with `hphi n _`.

Rewrite using `[e1, hY, Matrix.mul_assoc]`.
-/
theorem G_map_ghost {ε : PreTilt O p} {h : ℕ} (D : Datum ε h ℤ_[p])
    (hG : D.G = D.G.map (phiInv p O) * D.Ψ')
    (hphi : ∀ n a, ghost p O (n + 1) (phiInv p O a) = ghost p O n a) (n : ℕ) :
    ∃ Y : Matrix (Fin h) (Fin h) O,
      D.G.map (ghostHom p O n) = D.G.map (WittVector.fontaineTheta O p) * Y := by
  induction n with
  | zero => exact ⟨1, by rw [Matrix.mul_one]; rfl⟩
  | succ n ih =>
    obtain ⟨Y, hY⟩ := ih
    refine ⟨Y * D.Ψ'.map (ghostHom p O (n + 1)), ?_⟩
    have e1 : D.G.map (ghostHom p O (n + 1)) =
        D.G.map (ghostHom p O n) * D.Ψ'.map (ghostHom p O (n + 1)) := by
      conv_lhs => rw [hG]
      rw [Matrix.map_mul, Matrix.map_map]
      congr 1
      ext i j
      exact hphi n _
    rw [e1, hY, Matrix.mul_assoc]

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ _ hv ε hε G h D e fil hal`. Take `⟨-, hofP, hmu, -, -, hphi⟩` from `GlobalTheory.T.ainfGhostThetaFrobIter_values_xi_mu_padic p C v O hv ε hε`. Establish `hε1 : IsPrimitiveRoot (root ε).untilt p` using `by simpa [zeta] using hε 1`. Take `⟨hdom, -, -, -, hν, hξ, -⟩` from `GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hε1`. Use `haveI := hdom`.

Establish `hμ : Sandwich.mu ε ≠ 0`. Rewrite using `[← xi_mul_nu]`. Conclude with `mul_ne_zero hξ fun h0 => hν (by rw [h0, map_zero])`. Establish `hFG : D.F * D.G = Sandwich.mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O))` using `GlobalTheory.SelfDualFil.mul_eq_smul_comm hμ D.G_mul_F`. Establish `hGeq` using `GlobalTheory.SelfDualFil.G_eq hμ hξ D`.

Establish `hθμ : WittVector.fontaineTheta O p (Sandwich.mu ε) = 0` using `hmu 0`. Establish `hzero : ∀ X Y : Matrix (Fin h) (Fin h) (Ainf p O), X * Y = Sandwich.mu ε • 1 → ∀ w : Fin h → O, X.map (WittVector.fontaineTheta O p) *ᵥ (Y.map (WittVector.fontaineTheta O p) *ᵥ w) = 0`. Introduce `X Y hXY w`. Rewrite using `[mulVec_mulVec, ← Matrix.map_mul, hXY]`. Use extensionality with `i`.

Simplify using `[Matrix.mulVec, dotProduct, hθμ]`. Establish `halFil : ∀ w, D.al w ∈ D.Fil` using `fun w => by`. Rewrite using `[Datum.Fil, LinearMap.mem_ker, Datum.bb, Datum.al, toLin'_apply, toLin'_apply]`. Conclude with `hzero _ _ D.G_mul_F w`. Establish `halbb : ∀ u, D.al (D.bb u) = 0` using `fun u => by`.

Rewrite using `[Datum.bb, Datum.al, toLin'_apply, toLin'_apply]`. Conclude with `hzero _ _ hFG u`. Establish `hghostA : ∀ n t, (ghostHom p O n) ∘ toA e t = toO e t` using `fun n t =>`. Use function extensionality and compare the values at `fun i => hofP n _`. Establish `hmem : ∀ r, rowMap D.F e r ∈ latt G`.

Introduce `r n`. Take `⟨X, hX⟩` from `F_map_ghost D hphi n`. Use `⟨dotLin ((ghostHom p O n ∘ r) ᵥ* X) ∘ₗ (D.Fil.subtype ∘ₗ fil.toLinearMap), fun t => ?_⟩` and prove the remaining obligations. Rewrite using `[rowMap_apply, ← ghostHom_apply, RingHom.map_dotProduct]`. Establish `e1 : (ghostHom p O n) ∘ (D.F *ᵥ toA e t) = X *ᵥ D.al (toO e t)`.

Use function extensionality and compare the values at `i`. Rewrite using `[Function.comp_apply, RingHom.map_mulVec, hghostA, hX, ← mulVec_mulVec, Datum.al, toLin'_apply]`. Rewrite using `[e1, hal, dotProduct_mulVec]`. Both sides reduce to the same expression. Set `Φ` to `(rowMap D.F e).codRestrict (latt G) hmem`.

Establish `hinj : Function.Injective Φ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `r hr`. Establish `h1 : ∀ t, r ⬝ᵥ (D.F *ᵥ toA e t) = 0` using `fun t => congrArg (fun y : latt G => y.1 t) hr`. Establish `h2 : r ᵥ* D.F = 0`.

Use function extensionality and compare the values at `i`. Use `h1 (e.symm (Pi.single i 1))` as an intermediate fact. Rewrite `this` using `[toA_single, dotProduct_mulVec]`. Simplify using `using this`. Establish `h3 : Sandwich.mu ε • r = 0`.

Use `congrArg (fun z => z ᵥ* D.G) h2` as an intermediate fact. Simplify using `only [vecMul_vecMul, hFG, vecMul_smul, vecMul_one, zero_vecMul] at this`. Conclude with `this`. Conclude with `(smul_eq_zero.1 h3).resolve_left hμ`. Establish `hsurj : Function.Surjective Φ`.

Introduce `y`. Use `set s : Fin h → Ainf p O := fun i => y.1 (e.symm (Pi.single i 1)) with hs`. Establish `hy : ∀ t, y.1 t = s ⬝ᵥ toA e t`. Introduce `t`. Establish `ht : t = ∑ i, e t i • e.symm (Pi.single i 1)`.

Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_sum]`. Use extensionality with `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Use `conv_lhs => rw [ht]`.

Rewrite using `[map_sum]`. Simplify using `only [LinearMap.map_smulₛₗ, dotProduct, toA, smul_eq_mul, s]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`. Establish `hdiv : ∀ j, Sandwich.mu ε ∣ (s ᵥ* D.G) j`. Introduce `j`.

Use `GlobalTheory.T.ainfTeichmullerMinusOne_dvd_of_ghost_components_zero p C v O hv ε hε _ fun n => ?_` and prove the remaining obligations. Take `⟨x, hx⟩` from `y.2 n`. Use `set gs : Fin h → O := ghostHom p O n ∘ s with hgs`. Establish `hgt : ∀ t, gs ⬝ᵥ toO e t = x (hodgeTate G t)`. Introduce `t`.

Rewrite using `[← hx, hy, ← ghostHom_apply, RingHom.map_dotProduct, hghostA]`. Establish `hl : dotLin gs = x ∘ₗ fil.symm.toLinearMap ∘ₗ D.al.codRestrict D.Fil halFil`. Use `(Pi.basisFun O (Fin h)).ext fun i => ?_` and prove the remaining obligations. Rewrite using `[Pi.basisFun_apply, ← toO_single e i, dotLin_apply, hgt]`. Establish `e2 : D.al.codRestrict D.Fil halFil (toO e (e.symm (Pi.single i 1))) = fil (hodgeTate G (e.symm (Pi.single i 1)))` using `Subtype.ext (hal _)`.

Simplify using `only [LinearMap.comp_apply, e2, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]`. Establish `hbb : gs ᵥ* D.G.map (WittVector.fontaineTheta O p) = 0`. Use function extensionality and compare the values at `k`. Establish `e3` using `LinearMap.congr_fun hl (D.bb (Pi.single k 1))`. Establish `e4 : D.al.codRestrict D.Fil halFil (D.bb (Pi.single k 1)) = 0` using `Subtype.ext (halbb _)`.

Rewrite `e3` using `[LinearMap.comp_apply, LinearMap.comp_apply, e4, map_zero, map_zero]`. Simplify using `only [dotLin_apply, Datum.bb, toLin'_apply, dotProduct_mulVec] at e3`. Simplify using `using e3`. Take `⟨Y, hY⟩` from `G_map_ghost D hGeq hphi n`. Rewrite using `[← ghostHom_apply, RingHom.map_vecMul, hY, ← vecMul_vecMul, ← hgs, hbb, zero_vecMul]`.

Both sides reduce to the same expression. Use `choose r hr using hdiv`. Establish `h1 : s ᵥ* D.G = Sandwich.mu ε • r` using `funext fun j => hr j`. Establish `h2 : r ᵥ* D.F = s`. Apply `smul_right_injective (Fin h → Ainf p O) hμ` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `Sandwich.mu ε • (r ᵥ* D.F) = Sandwich.mu ε • s`. Rewrite using `[← smul_vecMul, ← h1, vecMul_vecMul, D.G_mul_F, vecMul_smul, vecMul_one]`. Use `⟨r, Subtype.ext (LinearMap.ext fun t => ?_)⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `r ⬝ᵥ (D.F *ᵥ toA e t) = y.1 t`. Rewrite using `[hy, dotProduct_mulVec, h2]`.

Conclude with `⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩, fun r t => rfl⟩`.
-/
theorem latt_eq_rowSpace : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (G : PDivGroup p O) (h : ℕ) (D : Datum ε h ℤ_[p]) (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) (fil : G.dual.omega ≃ₗ[O] D.Fil), (∀ t, D.al (toO e t) = (fil (hodgeTate G t) : Fin h → O)) → ∃ L : (Fin h → Ainf p O) ≃ₗ[Ainf p O] latt G, ∀ r t, (L r).1 t = r ⬝ᵥ (D.F *ᵥ fun i => ofPadic p O (e t i)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G h D e fil hal
  obtain ⟨-, hofP, hmu, -, -, hphi⟩ := GlobalTheory.T.ainfGhostThetaFrobIter_values_xi_mu_padic p C v O hv ε hε
  have hε1 : IsPrimitiveRoot (root ε).untilt p := by simpa [zeta] using hε 1
  obtain ⟨hdom, -, -, -, hν, hξ, -⟩ := GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hε1
  haveI := hdom
  have hμ : Sandwich.mu ε ≠ 0 := by
    rw [← xi_mul_nu]
    exact mul_ne_zero hξ fun h0 => hν (by rw [h0, map_zero])
  have hFG : D.F * D.G = Sandwich.mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O)) :=
    GlobalTheory.SelfDualFil.mul_eq_smul_comm hμ D.G_mul_F
  have hGeq := GlobalTheory.SelfDualFil.G_eq hμ hξ D
  have hθμ : WittVector.fontaineTheta O p (Sandwich.mu ε) = 0 := hmu 0

  have hzero : ∀ X Y : Matrix (Fin h) (Fin h) (Ainf p O), X * Y = Sandwich.mu ε • 1 →
      ∀ w : Fin h → O, X.map (WittVector.fontaineTheta O p) *ᵥ
        (Y.map (WittVector.fontaineTheta O p) *ᵥ w) = 0 := by
    intro X Y hXY w
    rw [mulVec_mulVec, ← Matrix.map_mul, hXY]
    ext i
    simp [Matrix.mulVec, dotProduct, hθμ]
  have halFil : ∀ w, D.al w ∈ D.Fil := fun w => by
    rw [Datum.Fil, LinearMap.mem_ker, Datum.bb, Datum.al, toLin'_apply, toLin'_apply]
    exact hzero _ _ D.G_mul_F w
  have halbb : ∀ u, D.al (D.bb u) = 0 := fun u => by
    rw [Datum.bb, Datum.al, toLin'_apply, toLin'_apply]
    exact hzero _ _ hFG u

  have hghostA : ∀ n t, (ghostHom p O n) ∘ toA e t = toO e t := fun n t =>
    funext fun i => hofP n _
  have hmem : ∀ r, rowMap D.F e r ∈ latt G := by
    intro r n
    obtain ⟨X, hX⟩ := F_map_ghost D hphi n
    refine ⟨dotLin ((ghostHom p O n ∘ r) ᵥ* X) ∘ₗ (D.Fil.subtype ∘ₗ fil.toLinearMap),
      fun t => ?_⟩
    rw [rowMap_apply, ← ghostHom_apply, RingHom.map_dotProduct]
    have e1 : (ghostHom p O n) ∘ (D.F *ᵥ toA e t) = X *ᵥ D.al (toO e t) := by
      funext i
      rw [Function.comp_apply, RingHom.map_mulVec, hghostA, hX, ← mulVec_mulVec, Datum.al,
        toLin'_apply]
    rw [e1, hal, dotProduct_mulVec]
    rfl
  let Φ := (rowMap D.F e).codRestrict (latt G) hmem
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro r hr
    have h1 : ∀ t, r ⬝ᵥ (D.F *ᵥ toA e t) = 0 := fun t =>
      congrArg (fun y : latt G => y.1 t) hr
    have h2 : r ᵥ* D.F = 0 := by
      funext i
      have := h1 (e.symm (Pi.single i 1))
      rw [toA_single, dotProduct_mulVec] at this
      simpa using this
    have h3 : Sandwich.mu ε • r = 0 := by
      have := congrArg (fun z => z ᵥ* D.G) h2
      simp only [vecMul_vecMul, hFG, vecMul_smul, vecMul_one, zero_vecMul] at this
      exact this
    exact (smul_eq_zero.1 h3).resolve_left hμ
  have hsurj : Function.Surjective Φ := by
    intro y
    set s : Fin h → Ainf p O := fun i => y.1 (e.symm (Pi.single i 1)) with hs
    have hy : ∀ t, y.1 t = s ⬝ᵥ toA e t := by
      intro t
      have ht : t = ∑ i, e t i • e.symm (Pi.single i 1) := by
        apply e.injective
        rw [map_sum]
        ext j
        simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [ht]
      rw [map_sum]
      simp only [LinearMap.map_smulₛₗ, dotProduct, toA, smul_eq_mul, s]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have hdiv : ∀ j, Sandwich.mu ε ∣ (s ᵥ* D.G) j := by
      intro j
      refine GlobalTheory.T.ainfTeichmullerMinusOne_dvd_of_ghost_components_zero p C v O hv ε hε _ fun n => ?_
      obtain ⟨x, hx⟩ := y.2 n
      set gs : Fin h → O := ghostHom p O n ∘ s with hgs
      have hgt : ∀ t, gs ⬝ᵥ toO e t = x (hodgeTate G t) := by
        intro t
        rw [← hx, hy, ← ghostHom_apply, RingHom.map_dotProduct, hghostA]
      have hl : dotLin gs = x ∘ₗ fil.symm.toLinearMap ∘ₗ D.al.codRestrict D.Fil halFil := by
        refine (Pi.basisFun O (Fin h)).ext fun i => ?_
        rw [Pi.basisFun_apply, ← toO_single e i, dotLin_apply, hgt]
        have e2 : D.al.codRestrict D.Fil halFil (toO e (e.symm (Pi.single i 1))) =
            fil (hodgeTate G (e.symm (Pi.single i 1))) := Subtype.ext (hal _)
        simp only [LinearMap.comp_apply, e2, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      have hbb : gs ᵥ* D.G.map (WittVector.fontaineTheta O p) = 0 := by
        funext k
        have e3 := LinearMap.congr_fun hl (D.bb (Pi.single k 1))
        have e4 : D.al.codRestrict D.Fil halFil (D.bb (Pi.single k 1)) = 0 :=
          Subtype.ext (halbb _)
        rw [LinearMap.comp_apply, LinearMap.comp_apply, e4, map_zero, map_zero] at e3
        simp only [dotLin_apply, Datum.bb, toLin'_apply, dotProduct_mulVec] at e3
        simpa using e3
      obtain ⟨Y, hY⟩ := G_map_ghost D hGeq hphi n
      rw [← ghostHom_apply, RingHom.map_vecMul, hY, ← vecMul_vecMul, ← hgs, hbb, zero_vecMul]
      rfl
    choose r hr using hdiv
    have h1 : s ᵥ* D.G = Sandwich.mu ε • r := funext fun j => hr j
    have h2 : r ᵥ* D.F = s := by
      apply smul_right_injective (Fin h → Ainf p O) hμ
      change Sandwich.mu ε • (r ᵥ* D.F) = Sandwich.mu ε • s
      rw [← smul_vecMul, ← h1, vecMul_vecMul, D.G_mul_F, vecMul_smul, vecMul_one]
    refine ⟨r, Subtype.ext (LinearMap.ext fun t => ?_)⟩
    change r ⬝ᵥ (D.F *ᵥ toA e t) = y.1 t
    rw [hy, dotProduct_mulVec, h2]
  exact ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩, fun r t => rfl⟩

end GlobalTheory.PDivLat.RowSpace
