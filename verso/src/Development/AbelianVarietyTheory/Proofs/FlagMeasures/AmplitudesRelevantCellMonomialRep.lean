import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitalSquareEqHilbertSchmidtNormalisedVector
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnipotentHaarMeasureRatioStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CutoffComputesBesselQuotientIntegral
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselNeZeroOfCyclicOrbit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction

noncomputable section

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Formalism.MainNotions.S Matrix MeasureTheory
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CellRed

variable {k r : ℕ}

/- English proof (translation)
The claim follows from `Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1`.
-/
theorem det_Hpk : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1

/- English proof (translation)
The claim follows from `((uHGroup _ _ det_Hpk).2.2 g hg).1`.
-/
theorem unit_det {g : MatKR k r} (hg : g ∈ UH (Hpk k r)) : IsUnit g.det :=
  ((uHGroup _ _ det_Hpk).2.2 g hg).1

/- English proof (translation)
The claim follows from `((uHGroup _ _ det_Hpk).2.2 g hg).2`.
-/
theorem inv_mem {g : MatKR k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹ ∈ UH (Hpk k r) :=
  ((uHGroup _ _ det_Hpk).2.2 g hg).2

/- English proof (translation)
The claim follows from `(uHGroup _ _ det_Hpk).2.1 g hg h hh`.
-/
theorem mul_mem {g h : MatKR k r} (hg : g ∈ UH (Hpk k r)) (hh : h ∈ UH (Hpk k r)) : g * h ∈ UH (Hpk k r) :=
  (uHGroup _ _ det_Hpk).2.1 g hg h hh

/- English proof (translation)
Establish `hs : σ x v ∈ smoothVecs (k` using `k) (r := r) σ := P.TranslationBesselVanishing.smooth_translate hds hv hx`. Establish `key : ∀ a ∈ Nset k r, B (σ (a * x) v) = ψ a • π 1 (B (σ x v))`. Introduce `a ha`. Use `hB.2.2.1 1 (P.Dx2.Rad.one_UW z) a ha _ hs` as an intermediate fact. Rewrite `this` using `[Matrix.one_mul]`.

Rewrite using `[← this, P.TranslationBesselVanishing.sigma_mul hds ha.1 hx]`. Both sides reduce to the same expression. Establish `e` using `key 1 (nSubgroup k r).1`. Rewrite `e` using `[Matrix.one_mul]`. Rewrite using `[key m hm]`.

Use `conv_rhs => rw [e]`. Rewrite using `[smul_smul, div_mul_cancel₀ _ h1]`.
-/
theorem bessel_unip {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup Wp]
    [NormedSpace ℂ Wp] {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : MatKR k r → (H →L[ℂ] H)} (hds : IsDSHpk k r ε lam σ) {z : Fin (2 * r + k + 1) → ℂ} {ψ : MatKR k r → ℂ}
    {π : MatKR k r → (Wp →L[ℂ] Wp)} {B : H → Wp} (hB : IsBesselMapSm z ψ σ π B) (h1 : ψ 1 ≠ 0) {v : H}
    (hv : v ∈ smoothVecs (k := k) (r := r) σ) {m x : MatKR k r} (hm : m ∈ Nset k r) (hx : x ∈ UH (Hpk k r)) :
    B (σ (m * x) v) = (ψ m / ψ 1) • B (σ x v) := by
  have hs : σ x v ∈ smoothVecs (k := k) (r := r) σ := P.TranslationBesselVanishing.smooth_translate hds hv hx
  have key : ∀ a ∈ Nset k r, B (σ (a * x) v) = ψ a • π 1 (B (σ x v)) := by
    intro a ha
    have := hB.2.2.1 1 (P.Dx2.Rad.one_UW z) a ha _ hs
    rw [Matrix.one_mul] at this
    rw [← this, P.TranslationBesselVanishing.sigma_mul hds ha.1 hx]
    rfl
  have e := key 1 (nSubgroup k r).1
  rw [Matrix.one_mul] at e
  rw [key m hm]
  conv_rhs => rw [e]
  rw [smul_smul, div_mul_cancel₀ _ h1]

/- English proof (translation)
Establish `h : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Establish `e : Hpk k r * g⁻¹ = gᴴ * Hpk k r` using `by conv_lhs => rw [← h]`. Rewrite using `[Matrix.mul_nonsing_inv_cancel_right _ _ (unit_det hg)]`. Rewrite using `[P.Dx1.Rel.zhat_eq, P.Dx1.Rel.zhat_eq]`. Simplify using `only [conjTranspose_mul, conjTranspose_conjTranspose, (hpkFacts k r).1]`.

Rewrite using `[Matrix.mul_assoc _ (Hpk k r) g⁻¹, e]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem zhat_inv (z z' : Fin (2 * r + k + 1) → ℂ) {g : MatKR k r} (hg : g ∈ UH (Hpk k r)) :
    Zhat k r z' z g⁻¹ = (Zhat k r z z' g)ᴴ := by
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  have e : Hpk k r * g⁻¹ = gᴴ * Hpk k r := by
    conv_lhs => rw [← h]
    rw [Matrix.mul_nonsing_inv_cancel_right _ _ (unit_det hg)]
  rw [P.Dx1.Rel.zhat_eq, P.Dx1.Rel.zhat_eq]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, (hpkFacts k r).1]
  rw [Matrix.mul_assoc _ (Hpk k r) g⁻¹, e]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Establish `e : ∀ l, Dmin k r z' z g⁻¹ l = star (Dmin k r z z' g l)`. Introduce `l`. Unfold `Dmin`. Rewrite using `[zhat_inv z z' hg, ← Matrix.det_conjTranspose, Matrix.conjTranspose_submatrix]`. Unfold `Gf`.

Rewrite using `[e, e, mul_comm (Tz k r z')]`. Simplify using `only [Complex.star_def, Complex.normSq_conj]`.
-/
theorem gf_inv (z z' : Fin (2 * r + k + 1) → ℂ) {g : MatKR k r} (hg : g ∈ UH (Hpk k r)) :
    Gf k r z' z g⁻¹ = Gf k r z z' g := by
  have e : ∀ l, Dmin k r z' z g⁻¹ l = star (Dmin k r z z' g l) := by
    intro l
    unfold Dmin
    rw [zhat_inv z z' hg, ← Matrix.det_conjTranspose, Matrix.conjTranspose_submatrix]
  unfold Gf
  rw [e, e, mul_comm (Tz k r z')]
  simp only [Complex.star_def, Complex.normSq_conj]

open GlobalTheory.ThA.OrbSq in
/- English proof (translation)
Establish `: ∀ (q : C.LPt) (n : ℕ) (h : D.ptSize q = n) (a : Fin n), (h ▸ D.ptPerm q : Equiv.Perm (Fin n)) ((h ▸ D.ptPerm q : Equiv.Perm (Fin n)) a) = a`. Introduce `q n h a`. Substitute `h` using the available equality. Conclude with `P.Dx1.ptPerm_invol q a`. Conclude with `this _ _ _ a`.
-/
theorem permOf_invol (p : Point ℂ (r + 1)) (a : Fin (r + 1)) : permOf p (permOf p a) = a := by
  have : ∀ (q : C.LPt) (n : ℕ) (h : D.ptSize q = n) (a : Fin n),
      (h ▸ D.ptPerm q : Equiv.Perm (Fin n)) ((h ▸ D.ptPerm q : Equiv.Perm (Fin n)) a) = a := by
    intro q n h a
    subst h
    exact P.Dx1.ptPerm_invol q a
  exact this _ _ _ a

/- English proof (translation)
Rewrite using `[← h, ZhatO, ← mul_assoc, ← mul_pow]`. Simplify using the standard rewrite rules.
-/
theorem zhat_of_zhatO {z z' : Fin (2 * r + k + 1) → ℂ} {g : MatKR k r} {Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ}
    (h : ZhatO k r z z' g = Z) (a b : Fin (r + 1)) : Zhat k r z z' g a b = (-1 : ℂ) ^ (r - b.val) * Z a b := by
  rw [← h, ZhatO, ← mul_assoc, ← mul_pow]
  simp

open GlobalTheory.ThA.OrbSq in

/- English proof (translation)
Take `⟨hw, hd⟩` from `P.Dx2.VV.ptMatN_monoP' (sw p.1) (r + 1) (isLocPt_sw p).2 (isLocPt_sw p).1`. Rewrite `hw` using `[ptMat_sw]`. Generalize the expression as in `(Eq.rec (motive := fun x _ => Fin x → ℂ) (D.ptDiag (sw p.1)) (isLocPt_sw p).2) = d at hw hd`. Establish `h1 : Zhat k r z z' g = C2.monoP (permOf p) (fun b => (-1 : ℂ) ^ (r - b.val) * d b)`. Use extensionality with `a b`.

Rewrite using `[zhat_of_zhatO (h.trans hw)]`. Simplify using `[C2.monoP]`. Establish `h2 : ∀ b : Fin (r + 1), (-1 : ℂ) ^ (r - b.val) * d b ≠ 0` using `fun b => mul_ne_zero (pow_ne_zero _ (by norm_num)) (hd b)`. Use `⟨⟨_, h2, h1⟩, fun b => star ((-1 : ℂ) ^ (r - (permOf p b).val) * d (permOf p b)), fun b => star_ne_zero.2 (h2 _), ?_⟩` and prove the remaining obligations. Rewrite using `[zhat_inv z z' hg, h1]`.

Use extensionality with `a b`. Simplify using `only [C2.monoP, conjTranspose_apply, Matrix.of_apply]`. Distinguish the cases in `e : a = permOf p b`. Rewrite using `[if_pos e, if_pos (by rw [e, permOf_invol]), e]`. Rewrite using `[if_neg e, if_neg (fun e' => e (by rw [e', permOf_invol])), star_zero]`.
-/
theorem monomial_of_pt {z z' : Fin (2 * r + k + 1) → ℂ} {g : MatKR k r} (hg : g ∈ UH (Hpk k r))
    {p : Point ℂ (r + 1)} (h : ZhatO k r z z' g = ptMat p) :
    (∃ d : Fin (r + 1) → ℂ, (∀ a, d a ≠ 0) ∧ Zhat k r z z' g = C2.monoP (permOf p) d) ∧
      ∃ d : Fin (r + 1) → ℂ, (∀ a, d a ≠ 0) ∧ Zhat k r z' z g⁻¹ = C2.monoP (permOf p) d := by
  obtain ⟨hw, hd⟩ := P.Dx2.VV.ptMatN_monoP' (sw p.1) (r + 1) (isLocPt_sw p).2 (isLocPt_sw p).1
  rw [ptMat_sw] at hw
  generalize (Eq.rec (motive := fun x _ => Fin x → ℂ) (D.ptDiag (sw p.1)) (isLocPt_sw p).2) = d at hw hd
  have h1 : Zhat k r z z' g = C2.monoP (permOf p) (fun b => (-1 : ℂ) ^ (r - b.val) * d b) := by
    ext a b
    rw [zhat_of_zhatO (h.trans hw)]
    simp [C2.monoP]
  have h2 : ∀ b : Fin (r + 1), (-1 : ℂ) ^ (r - b.val) * d b ≠ 0 := fun b =>
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (hd b)
  refine ⟨⟨_, h2, h1⟩, fun b => star ((-1 : ℂ) ^ (r - (permOf p b).val) * d (permOf p b)),
    fun b => star_ne_zero.2 (h2 _), ?_⟩
  rw [zhat_inv z z' hg, h1]
  ext a b
  simp only [C2.monoP, conjTranspose_apply, Matrix.of_apply]
  by_cases e : a = permOf p b
  · rw [if_pos e, if_pos (by rw [e, permOf_invol]), e]
  · rw [if_neg e, if_neg (fun e' => e (by rw [e', permOf_invol])), star_zero]

open GlobalTheory.ThA.OrbSq P.Dx1.Rel in

/- English proof (translation)
Introduce and unpack `ρ ⟨hρN, hρ'N⟩`. Establish `hp` using `isLocPt_sw q`. Rewrite `hZ` using `[← ptMat_sw]`. Generalize the expression as in `sw q.1 = p at hp hZ`. Establish `hU` using `unit_det hγ`.

Establish `hcomm : γ * (γ⁻¹ * ρ * γ) = ρ * γ`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv γ hU, Matrix.one_mul]`. Use `set ρ' := γ⁻¹ * ρ * γ with hρ'`. Use `set B := Bm k r z ρ with hBdef`. Use `set A := Bm k r z' ρ' with hAdef`.

Establish `hB` using `expand z hz ρ hρN`. Establish `hA` using `expand z' hz' ρ' hρ'N`. Establish `hunit : ρᴴ * Hpk k r * ρ = Hpk k r` using `hρN.1`. Establish `key : Bᴴ * Zhat k r z z' γ * A = Zhat k r z z' γ`. Rewrite using `[zhat_eq]`.

Use `set F := P.Dx1.Rel.Fm k r z`. Use `set F' := P.Dx1.Rel.Fm k r z'`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = (ρ * F)ᴴ * (Hpk k r * (γ * (ρ' * F'))) := by rw [hB, hA]`.

Use `_ = Fᴴ * ((ρᴴ * Hpk k r * ρ) * (γ * F')) := by`. Rewrite using `[← Matrix.mul_assoc γ ρ' F', hcomm]`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = Fᴴ * Hpk k r * γ * F' := by rw [hunit]; simp only [Matrix.mul_assoc]`. Establish `hsz : D.ptSize p = r + 1` using `hp.2`.

Establish `hPlt : ∀ a : Fin (r + 1), D.ptPartner p a.val < r + 1` using `fun a => by`. Use `(partner_spec p a.val (by omega)).1; omega` as an intermediate fact. Set `P : Fin (r + 1) → Fin (r + 1)` to `fun a => ⟨D.ptPartner p a.val, hPlt a⟩`. Set `t : Fin (r + 1) → ℂ` to `fun a => D.ptScal p a.val`. Establish `hP : ∀ a, P (P a) = a` using `fun a => Fin.ext (partner_spec p a.val (by omega)).2.1`.

Establish `ht : ∀ a, t a ≠ 0` using `fun a => scal_ne p hp.1 a.val (by omega)`. Establish `hblk : ∀ b : Fin r, ((P b.succ).val + 1 = (P b.castSucc).val ∧ t b.succ = t b.castSucc) ∨ P b.castSucc < P b.succ`. Introduce `b`. Break down `block p b.val (by omega) with h | h` into its components or cases. Use `left`.

Conclude with `h`. Use `right`. Conclude with `h`. Establish `hZP : D.ptMatN p (r + 1) = Matrix.of fun i a => if i = P a then t a else 0`. Use extensionality with `i a`.

Simplify using `only [D.ptMatN, Matrix.of_apply]`. Rewrite using `[(partner_spec p a.val (by omega)).2.2 i.val]`. Simplify using `only [P, t, Fin.ext_iff]`. Use `set S : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.diagonal fun b => (-1 : ℂ) ^ (r - b.val) with hS`. Establish `hZS : D.ptMatN p (r + 1) = Zhat k r z z' γ * S`.

Use extensionality with `a b`. Rewrite using `[← hZ, hS, Matrix.mul_diagonal, ZhatO, mul_comm]`. Establish `hSS : S * S = 1`. Rewrite using `[hS, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`.

Use function extensionality and compare the values at `b`. Rewrite using `[← mul_pow]`. Simplify using the standard rewrite rules. Establish `ent : ∀ i j, (S * A * S) i j = (-1 : ℂ) ^ (r - i.val) * A i j * (-1 : ℂ) ^ (r - j.val)` using `fun i j => by`. Rewrite using `[hS, Matrix.mul_diagonal, Matrix.diagonal_mul]`.

Establish `hcore` using `core r P hP t ht hblk (S * A * S) B (fun i j h => by rw [ent, hAdef, Bm_upper z' ρ' hρ'N i j h]; simp) (fun i => by rw [ent, hAdef, Bm_diag z' ρ' hρ'N i, mul_one, ← mul_pow]; simp) (Bm_upper z ρ hρN) (by`. Rewrite using `[← hZP, hZS]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [hSS, Matrix.mul_one, key])`.

Establish `hneg : ∑ b : Fin r, (S * A * S) b.castSucc b.succ = -∑ b : Fin r, A b.castSucc b.succ`. Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Establish `e : r - b.castSucc.val = (r - b.succ.val) + 1`. Use `b.isLt` as an intermediate fact.

Simplify using `only [Fin.val_castSucc, Fin.val_succ]`. Use linear arithmetic over natural numbers and integers. Establish `e2 : (-1 : ℂ) ^ (r - b.succ.val) * (-1 : ℂ) ^ (r - b.succ.val) = 1` using `by rw [← mul_pow]; simp`. Rewrite using `[ent, e, pow_succ]`. Take the linear combination `(-A b.castSucc b.succ) * e2`.

Rewrite `hcore` using `[hneg, neg_inj]`. Unfold `psi`. Rewrite using `[ell_eq, ell_eq, ← hBdef, ← hAdef, hcore]`. Use `congr 3`. Simplify using `[Complex.mul_re, Complex.conj_re]`.
-/
theorem relevant {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') {γ : MatKR k r}
    (hγ : γ ∈ UH (Hpk k r)) {q : Point ℂ (r + 1)} (hZ : ZhatO k r z z' γ = ptMat q) (c : ℝ) :
    ∀ a ∈ RStab k r γ, psi k r z c a = psi k r z' c (γ⁻¹ * a * γ) := by
  rintro ρ ⟨hρN, hρ'N⟩
  have hp := isLocPt_sw q
  rw [← ptMat_sw] at hZ
  generalize sw q.1 = p at hp hZ
  have hU := unit_det hγ
  have hcomm : γ * (γ⁻¹ * ρ * γ) = ρ * γ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv γ hU, Matrix.one_mul]
  set ρ' := γ⁻¹ * ρ * γ with hρ'
  set B := Bm k r z ρ with hBdef
  set A := Bm k r z' ρ' with hAdef
  have hB := expand z hz ρ hρN
  have hA := expand z' hz' ρ' hρ'N
  have hunit : ρᴴ * Hpk k r * ρ = Hpk k r := hρN.1
  have key : Bᴴ * Zhat k r z z' γ * A = Zhat k r z z' γ := by
    rw [zhat_eq]
    set F := P.Dx1.Rel.Fm k r z
    set F' := P.Dx1.Rel.Fm k r z'
    calc Bᴴ * (Fᴴ * Hpk k r * γ * F') * A = (F * B)ᴴ * (Hpk k r * (γ * (F' * A))) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (ρ * F)ᴴ * (Hpk k r * (γ * (ρ' * F'))) := by rw [hB, hA]
      _ = Fᴴ * ((ρᴴ * Hpk k r * ρ) * (γ * F')) := by
          rw [← Matrix.mul_assoc γ ρ' F', hcomm]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Fᴴ * Hpk k r * γ * F' := by rw [hunit]; simp only [Matrix.mul_assoc]
  have hsz : D.ptSize p = r + 1 := hp.2
  have hPlt : ∀ a : Fin (r + 1), D.ptPartner p a.val < r + 1 := fun a => by
    have := (partner_spec p a.val (by omega)).1; omega
  let P : Fin (r + 1) → Fin (r + 1) := fun a => ⟨D.ptPartner p a.val, hPlt a⟩
  let t : Fin (r + 1) → ℂ := fun a => D.ptScal p a.val
  have hP : ∀ a, P (P a) = a := fun a => Fin.ext (partner_spec p a.val (by omega)).2.1
  have ht : ∀ a, t a ≠ 0 := fun a => scal_ne p hp.1 a.val (by omega)
  have hblk : ∀ b : Fin r, ((P b.succ).val + 1 = (P b.castSucc).val ∧ t b.succ = t b.castSucc) ∨
      P b.castSucc < P b.succ := by
    intro b
    rcases block p b.val (by omega) with h | h
    · left; exact h
    · right; exact h
  have hZP : D.ptMatN p (r + 1) = Matrix.of fun i a => if i = P a then t a else 0 := by
    ext i a
    simp only [D.ptMatN, Matrix.of_apply]
    rw [(partner_spec p a.val (by omega)).2.2 i.val]
    simp only [P, t, Fin.ext_iff]
  set S : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.diagonal fun b => (-1 : ℂ) ^ (r - b.val) with hS
  have hZS : D.ptMatN p (r + 1) = Zhat k r z z' γ * S := by
    ext a b
    rw [← hZ, hS, Matrix.mul_diagonal, ZhatO, mul_comm]
  have hSS : S * S = 1 := by
    rw [hS, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext b
    rw [← mul_pow]; simp
  have ent : ∀ i j, (S * A * S) i j = (-1 : ℂ) ^ (r - i.val) * A i j * (-1 : ℂ) ^ (r - j.val) := fun i j => by
    rw [hS, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hcore := core r P hP t ht hblk (S * A * S) B
    (fun i j h => by rw [ent, hAdef, Bm_upper z' ρ' hρ'N i j h]; simp)
    (fun i => by rw [ent, hAdef, Bm_diag z' ρ' hρ'N i, mul_one, ← mul_pow]; simp)
    (Bm_upper z ρ hρN) (by
      rw [← hZP, hZS]
      calc Bᴴ * (Zhat k r z z' γ * S) * (S * A * S) = Bᴴ * Zhat k r z z' γ * (S * S) * A * S := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hSS, Matrix.mul_one, key])
  have hneg : ∑ b : Fin r, (S * A * S) b.castSucc b.succ = -∑ b : Fin r, A b.castSucc b.succ := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    have e : r - b.castSucc.val = (r - b.succ.val) + 1 := by
      have := b.isLt
      simp only [Fin.val_castSucc, Fin.val_succ]; omega
    have e2 : (-1 : ℂ) ^ (r - b.succ.val) * (-1 : ℂ) ^ (r - b.succ.val) = 1 := by rw [← mul_pow]; simp
    rw [ent, e, pow_succ]
    linear_combination (-A b.castSucc b.succ) * e2
  rw [hneg, neg_inj] at hcore
  unfold psi
  rw [ell_eq, ell_eq, ← hBdef, ← hAdef, hcore]
  congr 3
  simp [Complex.mul_re, Complex.conj_re]

/- English proof (translation)
Take `⟨μG, hμG⟩` from `P.unitary_group_haar_exists k r`. Take `⟨χ, hχ1, hχ2, hχ3⟩` from `P.character_exists_alt`. Take `⟨μW, hW⟩` from `P.weyl_haar_exists k r z hz hT`. Take `⟨μW', hW'⟩` from `P.weyl_haar_exists k r z' hz' hT'`. Take `⟨μs, hs⟩` from `P.SettingConstruction.sectionExists k r z z' hk hz hz' hT hT'`.

Conclude with `⟨{ z := z, z' := z', π := fun _ => 1, π' := fun _ => 1, μG := μG, μW := μW, μN := D.muN k r, μW' := μW', μsec := μs, χ := χ, k_pos := hk, z_mem := hz, z'_mem := hz', T_pos := hT, T'_pos := hT', π_rep := ⟨rfl, fun _ _ _ _ => rfl⟩, π'_rep := ⟨rfl, fun _ _ _ _ => rfl⟩, π_unitary := …`.
-/
theorem exists_setting (hk : 1 ≤ k) {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z')
    (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') : ∃ Bs : B.RealPlaceData k r ℂ ℂ, Bs.z = z ∧ Bs.z' = z' := by
  obtain ⟨μG, hμG⟩ := P.unitary_group_haar_exists k r
  obtain ⟨χ, hχ1, hχ2, hχ3⟩ := P.character_exists_alt
  obtain ⟨μW, hW⟩ := P.weyl_haar_exists k r z hz hT
  obtain ⟨μW', hW'⟩ := P.weyl_haar_exists k r z' hz' hT'
  obtain ⟨μs, hs⟩ := P.SettingConstruction.sectionExists k r z z' hk hz hz' hT hT'
  exact ⟨{ z := z, z' := z', π := fun _ => 1, π' := fun _ => 1, μG := μG, μW := μW, μN := D.muN k r, μW' := μW',
           μsec := μs, χ := χ, k_pos := hk, z_mem := hz, z'_mem := hz', T_pos := hT,
           T'_pos := hT', π_rep := ⟨rfl, fun _ _ _ _ => rfl⟩, π'_rep := ⟨rfl, fun _ _ _ _ => rfl⟩,
           π_unitary := fun _ _ _ => rfl, π'_unitary := fun _ _ _ => rfl, π_cont := continuousOn_const,
           π'_cont := continuousOn_const, haarG := hμG, haarW := hW, haarN := P.nilpotent_measure_is_haar k r, haarW' := hW',
           sec := hs, χ_smooth := hχ1, χ_supp := hχ2, χ_int := hχ3 }, rfl, rfl⟩

/- English proof (translation)
The claim follows from `continuous_const.matrix_mul (continuous_id (X := MatKR k r))`.
-/
theorem continuous_lmul (a : MatKR k r) : Continuous (lmulM a : Mt k r → Mt k r) :=
  continuous_const.matrix_mul (continuous_id (X := MatKR k r))

/- English proof (translation)
The claim follows from `(continuous_id (X := MatKR k r)).matrix_mul continuous_const`.
-/
theorem continuous_rmul (a : MatKR k r) : Continuous (B.rmulF a : Mt k r → Mt k r) :=
  (continuous_id (X := MatKR k r)).matrix_mul continuous_const

/- English proof (translation)
The claim follows from `(continuous_const.matrix_mul (continuous_id (X := MatKR k r))).matrix_mul continuous_const`.
-/
theorem continuous_conj (a : MatKR k r) : Continuous (conjM a : Mt k r → Mt k r) :=
  (continuous_const.matrix_mul (continuous_id (X := MatKR k r))).matrix_mul continuous_const

/- English proof (translation)
Establish `hu` using `unit_det hg`. Use `show g⁻¹ * (g * Matrix.of x * g⁻¹) * g⁻¹⁻¹ = Matrix.of x`. Rewrite using `[Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.mul_assoc g, Matrix.nonsing_inv_mul_cancel_left _ _ hu, Matrix.nonsing_inv_mul_cancel_right _ _ hu]`.
-/
theorem conj_inv_conj {g : MatKR k r} (hg : g ∈ UH (Hpk k r)) (x : Mt k r) : conjM g⁻¹ (conjM g x) = x := by
  have hu := unit_det hg
  show g⁻¹ * (g * Matrix.of x * g⁻¹) * g⁻¹⁻¹ = Matrix.of x
  rw [Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.mul_assoc g, Matrix.nonsing_inv_mul_cancel_left _ _ hu,
    Matrix.nonsing_inv_mul_cancel_right _ _ hu]

def lmulEquiv {γ : MatKR k r} (hγ : γ ∈ UH (Hpk k r)) : Mt k r ≃ᵐ Mt k r where
  toFun := lmulM γ
  invFun := lmulM γ⁻¹
  left_inv x := Matrix.nonsing_inv_mul_cancel_left γ (Matrix.of x) (unit_det hγ)
  right_inv x := Matrix.mul_nonsing_inv_cancel_left γ (Matrix.of x) (unit_det hγ)
  measurable_toFun := (continuous_lmul γ).measurable
  measurable_invFun := (continuous_lmul γ⁻¹).measurable

/- English proof (translation)
Introduce `f hf`. Rewrite using `[lintegral_map_equiv]`. Establish `h1` using `h (fun x => f (lmulM γ x)) (hf.comp (continuous_lmul γ).measurable)`. Rewrite `h1` using `[← lintegral_map hf (continuous_lmul γ).measurable, hG.2.2.2 γ hγ]`. Rewrite using `[h1]`.

Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Establish `hm : Measurable fun s : Mt k r => f (B.rmulF (Matrix.of (lmulEquiv hγ x)) s)` using `hf.comp (continuous_rmul _).measurable`. Use `Eq.trans ?_ (lintegral_map hm (continuous_conj γ).measurable).symm` and prove the remaining obligations. Use `lintegral_congr fun s => ?_` and prove the remaining obligations. Use `congr 1`.

Use `show γ * (Matrix.of s * Matrix.of x) = γ * Matrix.of s * γ⁻¹ * (γ * Matrix.of x)`. Rewrite using `[Matrix.mul_assoc _ γ⁻¹, Matrix.nonsing_inv_mul_cancel_left γ (Matrix.of x) (unit_det hγ), Matrix.mul_assoc]`.
-/
theorem quot_map {γ : MatKR k r} (hγ : γ ∈ UH (Hpk k r)) {μG μR ν : Measure (Mt k r)}
    (hG : IsHaarOn (UH (Hpk k r)) μG) (h : IsQuotMeas μG μR ν) :
    IsQuotMeas μG (μR.map (conjM γ)) (ν.map (lmulEquiv hγ)) := by
  intro f hf
  rw [lintegral_map_equiv]
  have h1 := h (fun x => f (lmulM γ x)) (hf.comp (continuous_lmul γ).measurable)
  rw [← lintegral_map hf (continuous_lmul γ).measurable, hG.2.2.2 γ hγ] at h1
  rw [h1]
  refine lintegral_congr fun x => ?_
  have hm : Measurable fun s : Mt k r => f (B.rmulF (Matrix.of (lmulEquiv hγ x)) s) :=
    hf.comp (continuous_rmul _).measurable
  refine Eq.trans ?_ (lintegral_map hm (continuous_conj γ).measurable).symm
  refine lintegral_congr fun s => ?_
  congr 1
  show γ * (Matrix.of s * Matrix.of x) = γ * Matrix.of s * γ⁻¹ * (γ * Matrix.of x)
  rw [Matrix.mul_assoc _ γ⁻¹, Matrix.nonsing_inv_mul_cancel_left γ (Matrix.of x) (unit_det hγ), Matrix.mul_assoc]

/- English proof (translation)
Establish `hu` using `unit_det hg`. Establish `hm` using `(continuous_conj g).measurable`. Establish `hii : g⁻¹⁻¹ = g` using `Matrix.nonsing_inv_nonsing_inv _ hu`. Establish `back : ∀ a ∈ C6.Rset g, g⁻¹ * a * g ∈ C6.Rset g⁻¹` using `fun a ha => ⟨ha.2, by`. Rewrite using `[hii, Matrix.mul_assoc g⁻¹, Matrix.mul_nonsing_inv_cancel_left _ _ hu, Matrix.mul_nonsing_inv_cancel_right _ _ hu]`.

Conclude with `ha.1⟩`. Use `⟨?_, fun a ha => ?_, fun a ha => ?_, fun K hK => ?_, ?_⟩` and prove the remaining obligations. Establish `hcl : IsClosed {x : Mt k r | Matrix.of x ∈ C6.Rset g}` using `(P.Dx2.OrbJ.closedR hu).closed`. Use `(Measure.map_apply hm hcl.measurableSet.compl).trans ?_` and prove the remaining obligations. Establish `h0 : μ {x : Mt k r | Matrix.of x ∈ C6.Rset g⁻¹}ᶜ = 0` using `h.conc`.

Use `measure_mono_null (fun x hx (hx' : Matrix.of x ∈ C6.Rset g⁻¹) => hx ⟨?_, ?_⟩) h0` and prove the remaining obligations. Use `hx'.2` as an intermediate fact. Rewrite `this` using `[hii]`. Conclude with `this`. Establish `e` using `conj_inv_conj hg x`.

Unfold `conjM at e`. Rewrite `e` using `[hii]`. Establish `e' : g⁻¹ * Matrix.of (conjM g x) * g = Matrix.of x` using `e`. Rewrite using `[e']`. Conclude with `hx'.1`.

Use `conv_rhs => rw [← h.left _ (back a ha)]`. Rewrite using `[Measure.map_map (continuous_lmul _).measurable hm, Measure.map_map hm (continuous_lmul _).measurable]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Use `show a * (g * Matrix.of x * g⁻¹) = g * (g⁻¹ * a * g * Matrix.of x) * g⁻¹`.

Simplify using `only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu]`. Use `conv_rhs => rw [← h.right _ (back a ha)]`. Rewrite using `[Measure.map_map (continuous_rmul _).measurable hm, Measure.map_map hm (continuous_rmul _).measurable]`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Use `show (g * Matrix.of x * g⁻¹) * a = g * (Matrix.of x * (g⁻¹ * a * g)) * g⁻¹`. Simplify using `only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]`. Rewrite using `[Measure.map_apply hm hK.measurableSet]`. Use `(measure_mono fun x hx => ?_).trans_lt (h.finite_compact _ (hK.image (continuous_conj g⁻¹)))` and prove the remaining obligations. Conclude with `⟨_, hx, conj_inv_conj hg x⟩`.

Conclude with `fun e => h.ne_zero ((Measure.map_eq_zero_iff hm.aemeasurable).1 e)`.
-/
theorem haar_conj {g : MatKR k r} (hg : g ∈ UH (Hpk k r)) {μ : Measure (Mt k r)}
    (h : B.IsHaarOn (C6.Rset g⁻¹) μ) : B.IsHaarOn (C6.Rset g) (μ.map (conjM g)) := by
  have hu := unit_det hg
  have hm := (continuous_conj g).measurable
  have hii : g⁻¹⁻¹ = g := Matrix.nonsing_inv_nonsing_inv _ hu
  have back : ∀ a ∈ C6.Rset g, g⁻¹ * a * g ∈ C6.Rset g⁻¹ := fun a ha => ⟨ha.2, by
    rw [hii, Matrix.mul_assoc g⁻¹, Matrix.mul_nonsing_inv_cancel_left _ _ hu,
      Matrix.mul_nonsing_inv_cancel_right _ _ hu]
    exact ha.1⟩
  refine ⟨?_, fun a ha => ?_, fun a ha => ?_, fun K hK => ?_, ?_⟩
  · have hcl : IsClosed {x : Mt k r | Matrix.of x ∈ C6.Rset g} := (P.Dx2.OrbJ.closedR hu).closed
    refine (Measure.map_apply hm hcl.measurableSet.compl).trans ?_
    have h0 : μ {x : Mt k r | Matrix.of x ∈ C6.Rset g⁻¹}ᶜ = 0 := h.conc
    refine measure_mono_null (fun x hx (hx' : Matrix.of x ∈ C6.Rset g⁻¹) => hx ⟨?_, ?_⟩) h0
    · have := hx'.2
      rw [hii] at this
      exact this
    · have e := conj_inv_conj hg x
      unfold conjM at e
      rw [hii] at e
      have e' : g⁻¹ * Matrix.of (conjM g x) * g = Matrix.of x := e
      rw [e']
      exact hx'.1
  · conv_rhs => rw [← h.left _ (back a ha)]
    rw [Measure.map_map (continuous_lmul _).measurable hm, Measure.map_map hm (continuous_lmul _).measurable]
    congr 1
    funext x
    show a * (g * Matrix.of x * g⁻¹) = g * (g⁻¹ * a * g * Matrix.of x) * g⁻¹
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  · conv_rhs => rw [← h.right _ (back a ha)]
    rw [Measure.map_map (continuous_rmul _).measurable hm, Measure.map_map hm (continuous_rmul _).measurable]
    congr 1
    funext x
    show (g * Matrix.of x * g⁻¹) * a = g * (Matrix.of x * (g⁻¹ * a * g)) * g⁻¹
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  · rw [Measure.map_apply hm hK.measurableSet]
    refine (measure_mono fun x hx => ?_).trans_lt (h.finite_compact _ (hK.image (continuous_conj g⁻¹)))
    exact ⟨_, hx, conj_inv_conj hg x⟩
  · exact fun e => h.ne_zero ((Measure.map_eq_zero_iff hm.aemeasurable).1 e)

open GlobalTheory.ThA.OrbSq P P.Dx2 in

/- English proof (translation)
Take `⟨Bs, rfl, rfl⟩` from `exists_setting hk hz hz' hT hT'`. Establish `hG : Rad.Good Bs g (permOf γ) _` using `⟨Rad.exists_rho Bs hg hpos hd hZw, Rad.u_inj Bs hg hpos hd hZw, fun ρ hρ => Rad.u_lstg Bs hg hpos hd hZw hρ⟩`. Establish `hm` using `Rad.rhoF_meas Bs hg hd hG`. Establish `hmu : D.muR Bs g (permOf γ) = (volume : Measure (C2.Lstidx (permOf γ) → ℂ)).map (fun x => (Matrix.of.symm (Rad.rhoF Bs g (permOf γ) x) : Mt k r))` using `rfl`. Establish `phi : ∀ x : Mt k r, Rad.phi0 Bs (permOf γ) x = cjE (rootEquiv γ) (rootCoords k r Bs.z γ x)`.

Introduce `x`. Use function extensionality and compare the values at `q`. Rewrite using `[cjE_apply]`. Establish `hq : q.1.2.val < r` using `by have h1 := q.2.1; have h2 := q.1.1.isLt; rw [Fin.lt_def] at h1; omega`. Use `show star (C2.uMap k r Bs.z (Matrix.of x) q.1.2 q.1.1) = star (flagMat k r Bs.z (Matrix.of x) q.1.2 q.1.1)`.

Unfold `C2.uMap flagMat`. Rewrite using `[dif_pos hq, dif_pos hq]`. Conclude with `congrArg star (DF.herm_es _ _)`. Establish `hrc : rootCoords k r Bs.z γ = (cjE (rootEquiv γ)).symm ∘ Rad.phi0 Bs (permOf γ)`. Use function extensionality and compare the values at `x`.

Simplify using `[phi x]`. Establish `hrm : Measurable (rootCoords k r Bs.z γ)`. Rewrite using `[hrc]`. Conclude with `(cjE (rootEquiv γ)).symm.measurable.comp (Rad.continuous_radial_phi Bs).measurable`. Establish `e1 : μ.map ((fun x => (Matrix.of.symm (Rad.rhoF Bs g (permOf γ) x) : Mt k r)) ∘ (cjE (rootEquiv γ)) ∘ rootCoords k r Bs.z γ) = μ` using `by conv_rhs => rw [← Measure.map_id (μ := μ)]`.

Apply `Measure.map_congr` to reduce the goal to its premises. Establish `: ∀ᵐ x ∂μ, Matrix.of x ∈ C6.Rset g` using `h1`. Use `filter_upwards [this] with x hx`. Simplify using `only [Function.comp, id]`. Rewrite using `[← phi, ← Rad.rhoF_unique Bs hg hd hG _ hx]`.

Both sides reduce to the same expression. Use `Rad.u_eq_low Bs hg hd hG hx` as an intermediate fact. Rewrite using `[← Matrix.conjTranspose_conjTranspose (C2.uMap k r Bs.z (Matrix.of x)), this]`. Both sides reduce to the same expression. Establish `e2 : μ = c • D.muR Bs g (permOf γ)`.

Rewrite using `[← e1, ← Measure.map_map hm ((cjE _).measurable.comp hrm), ← Measure.map_map (cjE _).measurable hrm, h2, Measure.map_smul, Measure.map_smul, (cjE_mp _).map_eq, hmu]`. Rewrite using `[e2]`. Conclude with `⟨haar_smul (Rad.haar_good Bs hg hd hG) hc0 hc, (Dx3.intR Bs hg hd hG (by linarith)).smul_measure hc⟩`.
-/
theorem root_haar (hk : 1 ≤ k) {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z')
    (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') {g : MatKR k r} (hg : g ∈ UH (Hpk k r)) (hpos : 0 < Gf k r z z' g)
    {γ : Point ℂ (r + 1)} {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0) (hZw : Zhat k r z z' g = C2.monoP (permOf γ) d)
    {μ : Measure (Mt k r)} {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ⊤) (h1 : μ {x | Matrix.of x ∉ C6.Rset g} = 0)
    (h2 : μ.map (rootCoords k r z γ) = c • volume) :
    B.IsHaarOn (C6.Rset g) μ ∧ Integrable (fun x => B.gN (Matrix.of x) ^ (-(2 * ((r : ℝ) + 1) ^ 2 + 1))) μ := by
  obtain ⟨Bs, rfl, rfl⟩ := exists_setting hk hz hz' hT hT'
  have hG : Rad.Good Bs g (permOf γ) _ :=
    ⟨Rad.exists_rho Bs hg hpos hd hZw, Rad.u_inj Bs hg hpos hd hZw, fun ρ hρ => Rad.u_lstg Bs hg hpos hd hZw hρ⟩
  have hm := Rad.rhoF_meas Bs hg hd hG
  have hmu : D.muR Bs g (permOf γ) = (volume : Measure (C2.Lstidx (permOf γ) → ℂ)).map
      (fun x => (Matrix.of.symm (Rad.rhoF Bs g (permOf γ) x) : Mt k r)) := rfl
  have phi : ∀ x : Mt k r, Rad.phi0 Bs (permOf γ) x = cjE (rootEquiv γ) (rootCoords k r Bs.z γ x) := by
    intro x
    funext q
    rw [cjE_apply]
    have hq : q.1.2.val < r := by have h1 := q.2.1; have h2 := q.1.1.isLt; rw [Fin.lt_def] at h1; omega
    show star (C2.uMap k r Bs.z (Matrix.of x) q.1.2 q.1.1) = star (flagMat k r Bs.z (Matrix.of x) q.1.2 q.1.1)
    unfold C2.uMap flagMat
    rw [dif_pos hq, dif_pos hq]
    exact congrArg star (DF.herm_es _ _)
  have hrc : rootCoords k r Bs.z γ = (cjE (rootEquiv γ)).symm ∘ Rad.phi0 Bs (permOf γ) := by
    funext x; simp [phi x]
  have hrm : Measurable (rootCoords k r Bs.z γ) := by
    rw [hrc]; exact (cjE (rootEquiv γ)).symm.measurable.comp (Rad.continuous_radial_phi Bs).measurable
  have e1 : μ.map ((fun x => (Matrix.of.symm (Rad.rhoF Bs g (permOf γ) x) : Mt k r)) ∘ (cjE (rootEquiv γ)) ∘
      rootCoords k r Bs.z γ) = μ := by
    conv_rhs => rw [← Measure.map_id (μ := μ)]
    apply Measure.map_congr
    have : ∀ᵐ x ∂μ, Matrix.of x ∈ C6.Rset g := h1
    filter_upwards [this] with x hx
    simp only [Function.comp, id]
    rw [← phi, ← Rad.rhoF_unique Bs hg hd hG _ hx]
    · rfl
    · have := Rad.u_eq_low Bs hg hd hG hx
      rw [← Matrix.conjTranspose_conjTranspose (C2.uMap k r Bs.z (Matrix.of x)), this]; rfl
  have e2 : μ = c • D.muR Bs g (permOf γ) := by
    rw [← e1, ← Measure.map_map hm ((cjE _).measurable.comp hrm), ← Measure.map_map (cjE _).measurable hrm, h2,
      Measure.map_smul, Measure.map_smul, (cjE_mp _).map_eq, hmu]
  rw [e2]
  exact ⟨haar_smul (Rad.haar_good Bs hg hd hG) hc0 hc, (Dx3.intR Bs hg hd hG (by linarith)).smul_measure hc⟩

/- English proof (translation)
Take `⟨cN, hN⟩` from `GlobalTheory.T.exists_unipotentHaarMeasure_ratio k r`. Use `P.Dx2.OrbJ.sigmaF h` as an intermediate fact. Establish `hu` using `unit_det hg`. Establish `hθ : Measurable fun p : PairSp k r => P.Dx3.cut μ M p.swap` using `(P.Dx3.cut_meas M).comp measurable_swap`. Use `⟨_, GlobalTheory.ThA.QuotCut.isOrbQuot_withDensity k r L g _ (fun p => P.Dx3.cut μ M p.swap) cN hN hκ hg (haar_conj hg h) hθ (fun p => P.Dx3.cut_nonneg _ _ _) fun p _ h2 _ _ => ?_⟩` and prove the remaining obligations.

Establish `hact : Measurable fun a : Mt k r => stabAct g (Matrix.of a) p` using `(P.Dx2.OrbJ.contT g).measurable.comp (measurable_const.prodMk measurable_id)`. Use `(integral_map (continuous_conj g).measurable.aemeasurable (hθ.comp hact).aestronglyMeasurable).trans ?_` and prove the remaining obligations. Rewrite using `[← P.Dx3.cut_norm h hM hI p.swap h2]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)` and prove the remaining obligations. Establish `e : g⁻¹ * (g * Matrix.of a * g⁻¹) * g = Matrix.of a`.

Rewrite using `[Matrix.mul_assoc g, Matrix.nonsing_inv_mul_cancel_left _ _ hu, Matrix.nonsing_inv_mul_cancel_right _ _ hu]`. Use `show B.gN (g⁻¹ * (g * Matrix.of a * g⁻¹) * g * Matrix.of p.2.2) ^ (-M) / P.Dx3.Om μ M (g⁻¹ * (g * Matrix.of a * g⁻¹) * g * Matrix.of p.2.2) = _`. Rewrite using `[e]`. Both sides reduce to the same expression.
-/
theorem exists_orbQuot (L : LocBessel k r) (hκ : L.κN ≠ ⊤) {g : MatKR k r} (hg : g ∈ UH (Hpk k r))
    {μ : Measure (Mt k r)} (h : B.IsHaarOn (C6.Rset g⁻¹) μ) {M : ℝ} (hM : 0 ≤ M)
    (hI : Integrable (fun x => B.gN (Matrix.of x) ^ (-M)) μ) : ∃ ν, IsOrbQuot L g (μ.map (conjM g)) ν := by
  obtain ⟨cN, hN⟩ := GlobalTheory.T.exists_unipotentHaarMeasure_ratio k r
  have := P.Dx2.OrbJ.sigmaF h
  have hu := unit_det hg
  have hθ : Measurable fun p : PairSp k r => P.Dx3.cut μ M p.swap := (P.Dx3.cut_meas M).comp measurable_swap
  refine ⟨_, GlobalTheory.ThA.QuotCut.isOrbQuot_withDensity k r L g _ (fun p => P.Dx3.cut μ M p.swap) cN hN hκ hg
    (haar_conj hg h) hθ (fun p => P.Dx3.cut_nonneg _ _ _) fun p _ h2 _ _ => ?_⟩
  have hact : Measurable fun a : Mt k r => stabAct g (Matrix.of a) p :=
    (P.Dx2.OrbJ.contT g).measurable.comp (measurable_const.prodMk measurable_id)
  refine (integral_map (continuous_conj g).measurable.aemeasurable (hθ.comp hact).aestronglyMeasurable).trans ?_
  rw [← P.Dx3.cut_norm h hM hI p.swap h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  have e : g⁻¹ * (g * Matrix.of a * g⁻¹) * g = Matrix.of a := by
    rw [Matrix.mul_assoc g, Matrix.nonsing_inv_mul_cancel_left _ _ hu, Matrix.nonsing_inv_mul_cancel_right _ _ hu]
  show B.gN (g⁻¹ * (g * Matrix.of a * g⁻¹) * g * Matrix.of p.2.2) ^ (-M) /
    P.Dx3.Om μ M (g⁻¹ * (g * Matrix.of a * g⁻¹) * g * Matrix.of p.2.2) = _
  rw [e]
  rfl

/- English proof (translation)
The claim follows from `Complex.exp_ne_zero _`.
-/
theorem psi_ne (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (a : MatKR k r) : psi k r z c a ≠ 0 := Complex.exp_ne_zero _

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Finset in

/- English proof (translation)
Introduce `D τ w w' θ W hW lam0 A₀ hA hT hT' _ hka γ p hp θ' hθ' νR hν`. Take `⟨q, μ', ⟨n, hn, n', hn', g, rfl, hZ, μ₀, h0, h1, rfl⟩, hq⟩` from `hν`. Take `⟨hγ, -, hGf⟩` from `hp`. Establish `hk : 1 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Use `set L := toBessel D τ w w' θ W lam0 A₀ hW hA hT hT' with hL`.

Establish `hz : inWb _ _ W.z` using `L.hz.1`. Establish `hz' : inWb _ _ W.z'` using `L.hz'.1`. Establish `hTz : 0 < Tz _ _ W.z` using `L.hz.2`. Establish `hTz' : 0 < Tz _ _ W.z'` using `L.hz'.2`. Establish `hG : IsHaarOn (UH (Hpk D.R.k D.R.rS)) W.μG` using `hW.2.2.2.2.2.2.1`.

Establish `hg : g ∈ UH (Hpk D.R.k D.R.rS)`. Establish `e : g = n⁻¹ * (n * g * n') * n'⁻¹`. Rewrite using `[Matrix.mul_assoc n, Matrix.nonsing_inv_mul_cancel_left _ _ (unit_det hn.1), Matrix.mul_nonsing_inv_cancel_right _ _ (unit_det hn'.1)]`. Rewrite using `[e]`. Conclude with `mul_mem (mul_mem (inv_mem hn.1) hγ) (inv_mem hn'.1)`.

Establish `hS` using `Formalism.FourierDecayAlt.P.Dx2.Rad.N_sub_S W.z hn`. Establish `hS'` using `Formalism.FourierDecayAlt.P.Dx2.Rad.N_sub_S W.z' hn'`. Rewrite `hGf` using `[gInv _ _ _ _ hz hz' _ hS _ hS']`. Establish `hpos : 0 < Gf _ _ W.z W.z' g` using `lt_of_le_of_ne (gNonneg _ _ _ _ hz hz' hTz hTz' g hg) hGf.symm`. Take `⟨⟨d, hd, hm⟩, d', hd', hm'⟩` from `monomial_of_pt hg hZ`.

Establish `hii : g⁻¹⁻¹ = g` using `Matrix.nonsing_inv_nonsing_inv _ (unit_det hg)`. Use `set μ : Measure (Mt D.R.k D.R.rS) := ENNReal.ofReal θ' • μ₀ with hμ`. Establish `hc : 0 < (2 * D.host.ka / gg D / (2 * Real.pi)) ^ (rootPat q).card`. Rewrite using `[mul_div_assoc 2 D.host.ka]`. Check the signs of the components of the expression.

Take `⟨hH, hI⟩` from `root_haar (μ := μ) (c := ENNReal.ofReal θ' * ENNReal.ofReal ((2 * D.host.ka / gg D / (2 * Real.pi)) ^ (rootPat q).card)) hk hz' hz hTz' hTz (inv_mem hg) (by rw [gf_inv _ _ hg]; exact hpos) hd' hm' (mul_ne_zero (by simpa using hθ') (by simpa using hc)) (ENNReal.mul_ne_top ENNReal. …`. Establish `: μ₀ {x | Matrix.of x ∉ C6.Rset g⁻¹} = 0`. Unfold `C6.Rset`. Rewrite using `[hii]`. Conclude with `h0`.

Rewrite using `[hμ, Measure.smul_apply, this, smul_zero])`. Use the proof step `(by rw [hμ, Measure.map_smul, h1, smul_smul])`. Take `⟨ν, hν⟩` from `exists_orbQuot L ENNReal.ofReal_ne_top hg hH (by positivity) hI`. Establish `hR` using `haar_conj hg hH`. Establish `hq₀ : IsQuotMeas W.μG μ (νR.map (lmulEquiv hn'.1))`.

Establish `e1 : (fun x : Mt D.R.k D.R.rS => fun i j => (n'⁻¹ * Matrix.of x * n') i j) = conjM n'⁻¹`. Use function extensionality and compare the values at `x`. Unfold `conjM`. Rewrite using `[Matrix.nonsing_inv_nonsing_inv _ (unit_det hn'.1)]`. Establish `e2 : (conjM n' ∘ conjM n'⁻¹ : Mt D.R.k D.R.rS → _) = id`.

Use function extensionality and compare the values at `x`. Use `conj_inv_conj (inv_mem hn'.1) x` as an intermediate fact. Rewrite `this` using `[Matrix.nonsing_inv_nonsing_inv _ (unit_det hn'.1)]`. Then use the resulting hypothesis. Use `quot_map hn'.1 hG hq` as an intermediate fact. Rewrite `this` using `[e1, Measure.map_smul, Measure.map_map (continuous_conj _).measurable (continuous_conj _).measurable, e2, Measure.map_id]`. Then use the resulting hypothesis.

Establish `hconc : νR.map (lmulEquiv hn'.1) {x | Matrix.of x ∉ UH (Hpk D.R.k D.R.rS)} = 0` using `CutQuot.null_of_stable (R := {x | Matrix.of x ∈ C6.Rset g⁻¹}) (T := fun s x => fun i j => (Matrix.of s * Matrix.of x) i j) hH.conc hH.ne_zero hq₀ (CutQuot.measurable_G _ _).compl (fun s hs x hx h => hx ((CutQuot.mul_mem_iff hs.1.1 (Matrix.of x)).1 h)) hG.2.2.1`. Use `⟨g, μ.map (conjM g), νR.map (lmulEquiv hn'.1), ν, (psiS D W.z n / psiS D W.z 1) * star (psiS D W.z' n'⁻¹ / psiS D W.z' 1), ⟨hg, hpos, ⟨_, d, hd, hm⟩, relevant hz hz' hg hZ _, ⟨Formalism.FourierDecayAlt.P.Dx2.OrbJ.sigmaF hR, hR.ne_zero, hR.conc, hR.left⟩, hν, ?_⟩, hconc, fun l => …` and prove the remaining obligations. Establish `e1 : (fun x : Mt D.R.k D.R.rS => fun i j => (g⁻¹ * Matrix.of x * g) i j) = conjM g⁻¹`. Use function extensionality and compare the values at `x`. Unfold `conjM`.

Rewrite using `[hii]`. Establish `e2 : (conjM g⁻¹ ∘ conjM g : Mt D.R.k D.R.rS → _) = id` using `funext (conj_inv_conj hg)`. Rewrite using `[e1, Measure.map_map (continuous_conj _).measurable (continuous_conj _).measurable, e2, Measure.map_id]`. Conclude with `hq₀`. Unfold `DminN split_ifs`.

Conclude with `dInv _ _ _ _ hz hz' _ hS _ hS' _ _`. Both sides reduce to the same expression. Take `⟨-, hds, hB, hB', hv, -⟩` from `hA`. Establish `hae : ∀ᵐ x ∂νR, Matrix.of (lmulEquiv hn'.1 x) ∈ UH (Hpk D.R.k D.R.rS)` using `(MeasurableEquiv.measurableEmbedding _).ae_map_iff.1 hconc`. Unfold `LocS.J ampJ`.

Rewrite using `[integral_map_equiv, smul_comm]`. Use `congr 1`. Use `Eq.trans (integral_congr_ae ?_) (integral_smul _ _)` and prove the remaining obligations. Use `filter_upwards [hae] with x hx`. Use `set y : MatKR D.R.k D.R.rS := Matrix.of (lmulEquiv hn'.1 x) with hy`.

Establish `ey : y = n' * Matrix.of x` using `rfl`. Establish `ex : Matrix.of x = n'⁻¹ * y` using `by rw [ey, Matrix.nonsing_inv_mul_cancel_left _ _ (unit_det hn'.1)]`. Establish `e1 : A.Φ (n * g * n' * Matrix.of x) = (psiS D W.z n / psiS D W.z 1) • A.Φ (g * y)`. Rewrite using `[show n * g * n' * Matrix.of x = n * (g * y) by rw [ey]; simp only [Matrix.mul_assoc]]`. Conclude with `bessel_unip hds hB (psi_ne _ _ _) hv hn (mul_mem hg hx)`.

Establish `e2 : A.Φ' (Matrix.of x) = (psiS D W.z' n'⁻¹ / psiS D W.z' 1) • A.Φ' y`. Rewrite using `[ex]`. Conclude with `bessel_unip hds hB' (psi_ne _ _ _) hv ((nSubgroup _ _).2.2 _ hn') hx`. Rewrite using `[e1, e2]`. Use extensionality with `u`.

Simplify using `only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, _root_.smul_apply, inner_smul_left, smul_smul, Complex.star_def]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem amp_at_monomial : ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (hW : GoodW D τ w w' θ W) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A₀ : LocS W) (hA : GoodS D lam0 A₀) (hT : 0 < Tr D w) (hT' : 0 < Tr D w'), 0 < θ → 0 < D.host.ka / gg D → ∀ γ p, RelPt D W.z W.z' γ p → ∀ θ' : ℝ, 0 < θ' → ∀ νR, RMeas D W γ θ' νR → ∃ (g₀ : MatKR D.R.k D.R.rS) (μR ν₀ : Measure (Mt D.R.k D.R.rS)) (ν : Measure (PairSp D.R.k D.R.rS)) (s : ℂ), CellData (toBessel D τ w w' θ W lam0 A₀ hW hA hT hT') W.μG g₀ μR ν₀ ν ∧ ν₀ {x | Matrix.of x ∉ UH (Hpk D.R.k D.R.rS)} = 0 ∧ (∀ l, DminN W.z W.z' γ l = DminN W.z W.z' g₀ l) ∧ ∀ (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), GoodS D lam A → A.J νR γ = s • A.J ν₀ g₀ := by
  intro D τ w w' θ W hW lam0 A₀ hA hT hT' _ hka γ p hp θ' hθ' νR hν
  obtain ⟨q, μ', ⟨n, hn, n', hn', g, rfl, hZ, μ₀, h0, h1, rfl⟩, hq⟩ := hν
  obtain ⟨hγ, -, hGf⟩ := hp
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  set L := toBessel D τ w w' θ W lam0 A₀ hW hA hT hT' with hL
  have hz : inWb _ _ W.z := L.hz.1
  have hz' : inWb _ _ W.z' := L.hz'.1
  have hTz : 0 < Tz _ _ W.z := L.hz.2
  have hTz' : 0 < Tz _ _ W.z' := L.hz'.2
  have hG : IsHaarOn (UH (Hpk D.R.k D.R.rS)) W.μG := hW.2.2.2.2.2.2.1
  have hg : g ∈ UH (Hpk D.R.k D.R.rS) := by
    have e : g = n⁻¹ * (n * g * n') * n'⁻¹ := by
      rw [Matrix.mul_assoc n, Matrix.nonsing_inv_mul_cancel_left _ _ (unit_det hn.1),
        Matrix.mul_nonsing_inv_cancel_right _ _ (unit_det hn'.1)]
    rw [e]
    exact mul_mem (mul_mem (inv_mem hn.1) hγ) (inv_mem hn'.1)
  have hS := Formalism.FourierDecayAlt.P.Dx2.Rad.N_sub_S W.z hn
  have hS' := Formalism.FourierDecayAlt.P.Dx2.Rad.N_sub_S W.z' hn'
  rw [gInv _ _ _ _ hz hz' _ hS _ hS'] at hGf
  have hpos : 0 < Gf _ _ W.z W.z' g := lt_of_le_of_ne (gNonneg _ _ _ _ hz hz' hTz hTz' g hg) hGf.symm
  obtain ⟨⟨d, hd, hm⟩, d', hd', hm'⟩ := monomial_of_pt hg hZ
  have hii : g⁻¹⁻¹ = g := Matrix.nonsing_inv_nonsing_inv _ (unit_det hg)
  set μ : Measure (Mt D.R.k D.R.rS) := ENNReal.ofReal θ' • μ₀ with hμ
  have hc : 0 < (2 * D.host.ka / gg D / (2 * Real.pi)) ^ (rootPat q).card := by
    rw [mul_div_assoc 2 D.host.ka]; positivity
  obtain ⟨hH, hI⟩ := root_haar (μ := μ)
    (c := ENNReal.ofReal θ' * ENNReal.ofReal ((2 * D.host.ka / gg D / (2 * Real.pi)) ^ (rootPat q).card))
    hk hz' hz hTz' hTz (inv_mem hg) (by rw [gf_inv _ _ hg]; exact hpos) hd' hm'
    (mul_ne_zero (by simpa using hθ') (by simpa using hc))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    (by
      have : μ₀ {x | Matrix.of x ∉ C6.Rset g⁻¹} = 0 := by
        unfold C6.Rset
        rw [hii]
        exact h0
      rw [hμ, Measure.smul_apply, this, smul_zero])
    (by rw [hμ, Measure.map_smul, h1, smul_smul])
  obtain ⟨ν, hν⟩ := exists_orbQuot L ENNReal.ofReal_ne_top hg hH (by positivity) hI
  have hR := haar_conj hg hH
  have hq₀ : IsQuotMeas W.μG μ (νR.map (lmulEquiv hn'.1)) := by
    have e1 : (fun x : Mt D.R.k D.R.rS => fun i j => (n'⁻¹ * Matrix.of x * n') i j) = conjM n'⁻¹ := by
      funext x
      unfold conjM
      rw [Matrix.nonsing_inv_nonsing_inv _ (unit_det hn'.1)]
    have e2 : (conjM n' ∘ conjM n'⁻¹ : Mt D.R.k D.R.rS → _) = id := by
      funext x
      have := conj_inv_conj (inv_mem hn'.1) x
      rwa [Matrix.nonsing_inv_nonsing_inv _ (unit_det hn'.1)] at this
    have := quot_map hn'.1 hG hq
    rwa [e1, Measure.map_smul, Measure.map_map (continuous_conj _).measurable (continuous_conj _).measurable, e2,
      Measure.map_id] at this
  have hconc : νR.map (lmulEquiv hn'.1) {x | Matrix.of x ∉ UH (Hpk D.R.k D.R.rS)} = 0 :=
    CutQuot.null_of_stable (R := {x | Matrix.of x ∈ C6.Rset g⁻¹})
      (T := fun s x => fun i j => (Matrix.of s * Matrix.of x) i j) hH.conc hH.ne_zero hq₀
      (CutQuot.measurable_G _ _).compl
      (fun s hs x hx h => hx ((CutQuot.mul_mem_iff hs.1.1 (Matrix.of x)).1 h)) hG.2.2.1
  refine ⟨g, μ.map (conjM g), νR.map (lmulEquiv hn'.1), ν,
    (psiS D W.z n / psiS D W.z 1) * star (psiS D W.z' n'⁻¹ / psiS D W.z' 1),
    ⟨hg, hpos, ⟨_, d, hd, hm⟩, relevant hz hz' hg hZ _, ⟨Formalism.FourierDecayAlt.P.Dx2.OrbJ.sigmaF hR, hR.ne_zero, hR.conc, hR.left⟩,
      hν, ?_⟩, hconc, fun l => ?_, fun lam A hA => ?_⟩
  · have e1 : (fun x : Mt D.R.k D.R.rS => fun i j => (g⁻¹ * Matrix.of x * g) i j) = conjM g⁻¹ := by
      funext x
      unfold conjM
      rw [hii]
    have e2 : (conjM g⁻¹ ∘ conjM g : Mt D.R.k D.R.rS → _) = id := funext (conj_inv_conj hg)
    rw [e1, Measure.map_map (continuous_conj _).measurable (continuous_conj _).measurable, e2, Measure.map_id]
    exact hq₀
  · unfold DminN
    split_ifs
    · exact dInv _ _ _ _ hz hz' _ hS _ hS' _ _
    · rfl
  · obtain ⟨-, hds, hB, hB', hv, -⟩ := hA
    have hae : ∀ᵐ x ∂νR, Matrix.of (lmulEquiv hn'.1 x) ∈ UH (Hpk D.R.k D.R.rS) :=
      (MeasurableEquiv.measurableEmbedding _).ae_map_iff.1 hconc
    unfold LocS.J ampJ
    rw [integral_map_equiv, smul_comm]
    congr 1
    refine Eq.trans (integral_congr_ae ?_) (integral_smul _ _)
    filter_upwards [hae] with x hx
    set y : MatKR D.R.k D.R.rS := Matrix.of (lmulEquiv hn'.1 x) with hy
    have ey : y = n' * Matrix.of x := rfl
    have ex : Matrix.of x = n'⁻¹ * y := by rw [ey, Matrix.nonsing_inv_mul_cancel_left _ _ (unit_det hn'.1)]
    have e1 : A.Φ (n * g * n' * Matrix.of x) = (psiS D W.z n / psiS D W.z 1) • A.Φ (g * y) := by
      rw [show n * g * n' * Matrix.of x = n * (g * y) by rw [ey]; simp only [Matrix.mul_assoc]]
      exact bessel_unip hds hB (psi_ne _ _ _) hv hn (mul_mem hg hx)
    have e2 : A.Φ' (Matrix.of x) = (psiS D W.z' n'⁻¹ / psiS D W.z' 1) • A.Φ' y := by
      rw [ex]
      exact bessel_unip hds hB' (psi_ne _ _ _) hv ((nSubgroup _ _).2.2 _ hn') hx
    rw [e1, e2]
    ext u
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, _root_.smul_apply,
      inner_smul_left, smul_smul, Complex.star_def]
    congr 1
    ring

end GlobalTheory.CellRed
