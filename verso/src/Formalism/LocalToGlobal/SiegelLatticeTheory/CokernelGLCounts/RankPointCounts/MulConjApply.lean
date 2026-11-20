import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IotaFIntMem
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount

noncomputable section

open scoped Classical
open NumberField IsDedekindDomain ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf.PCountEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section IntInv

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {Mp : Loc.Model F E} {n : ℕ}

/- English proof (translation)
Set `lR : Matrix (Fin n) (Fin n) Mp.R` to `fun a b => ⟨l a b, hR a b⟩`. Establish `hl : lR.map Mp.R.subtype = l` using `by ext a b; rfl`. Establish `h2` using `congrFun (congrFun (RingHom.map_adjugate Mp.R.subtype lR) a) b`. Rewrite using `[← hl, show lR.map Mp.R.subtype = Mp.R.subtype.mapMatrix lR from rfl, ← h2]`. Conclude with `(lR.adjugate a b).2`.
-/
theorem mem_of_adj {l : Matrix (Fin n) (Fin n) E} (hR : ∀ a b, l a b ∈ Mp.R) (a b : Fin n) :
    l.adjugate a b ∈ Mp.R := by
  let lR : Matrix (Fin n) (Fin n) Mp.R := fun a b => ⟨l a b, hR a b⟩
  have hl : lR.map Mp.R.subtype = l := by ext a b; rfl
  have h2 := congrFun (congrFun (RingHom.map_adjugate Mp.R.subtype lR) a) b
  rw [← hl, show lR.map Mp.R.subtype = Mp.R.subtype.mapMatrix lR from rfl, ← h2]
  exact (lR.adjugate a b).2

/- English proof (translation)
Establish `hlo : IsLo l` using `⟨h.1, h.2.1⟩`. Establish `hinv` using `isLo_inv hlo`. Establish `hdet : l.det = 1` using `det_lo' hlo`. Use `⟨hinv.1, hinv.2, fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.inv_def, hdet, Ring.inverse_one, one_smul]`.

Conclude with `mem_of_adj h.2.2 a b`.
-/
theorem intLow_inv {l : Matrix (Fin n) (Fin n) E} (h : TieN.IntLow Mp l) : TieN.IntLow Mp l⁻¹ := by
  have hlo : IsLo l := ⟨h.1, h.2.1⟩
  have hinv := isLo_inv hlo
  have hdet : l.det = 1 := det_lo' hlo
  refine ⟨hinv.1, hinv.2, fun a b => ?_⟩
  rw [Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
  exact mem_of_adj h.2.2 a b

/- English proof (translation)
Establish `hup : IsUp l` using `⟨h.1, fun a b hab => h.2.1 b a hab⟩`. Establish `hinv` using `isUp_inv hup`. Establish `hdet : l.det = 1` using `det_up' hup`. Use `⟨hinv.1, fun a b hab => hinv.2 b a hab, fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.inv_def, hdet, Ring.inverse_one, one_smul]`.

Conclude with `mem_of_adj h.2.2 a b`.
-/
theorem intUp_inv {l : Matrix (Fin n) (Fin n) E} (h : TieN.IntUp Mp l) : TieN.IntUp Mp l⁻¹ := by
  have hup : IsUp l := ⟨h.1, fun a b hab => h.2.1 b a hab⟩
  have hinv := isUp_inv hup
  have hdet : l.det = 1 := det_up' hup
  refine ⟨hinv.1, fun a b hab => hinv.2 b a hab, fun a b => ?_⟩
  rw [Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
  exact mem_of_adj h.2.2 a b

end IntInv

section Ord

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
  {δ : ∀ p : PlF D, (D.s.atP p).Fp}

/- English proof (translation)
Use `⟨fun a => by simp [Loc.uLow], fun a b hab => ?_⟩` and prove the remaining obligations. Simplify using `[Loc.uLow, hab.ne, not_lt.2 hab.le]`.
-/
theorem isLo_uLow {n : ℕ} {p : PlF D} (x : Loc.IL n → (D.s.atP p).Ep) : IsLo (Loc.uLow x) := by
  refine ⟨fun a => by simp [Loc.uLow], fun a b hab => ?_⟩
  simp [Loc.uLow, hab.ne, not_lt.2 hab.le]

/- English proof (translation)
Use `⟨fun a => by simp [Loc.uUp], fun a b hab => ?_⟩` and prove the remaining obligations. Simplify using `[Loc.uUp, hab.ne', not_lt.2 hab.le]`.
-/
theorem isUp_uUp {n : ℕ} {p : PlF D} (w₀ : Loc.Pt (D.s.atP p).Ep n) (y : Loc.IN w₀ → (D.s.atP p).Ep) :
    IsUp (Loc.uUp w₀ y) := by
  refine ⟨fun a => by simp [Loc.uUp], fun a b hab => ?_⟩
  simp [Loc.uUp, hab.ne', not_lt.2 hab.le]

end Ord

section Real

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul]`.
-/
theorem conj_mul_apply {R : Type*} [CommRing R] {n : ℕ} (fr fri : Fin n → R) (M N : Matrix (Fin n) (Fin n) R)
    (a b : Fin n) :
    ((Matrix.diagonal fr * M * Matrix.diagonal fri) * N) a b = ∑ k, fr a * M a k * fri k * N k b := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul]`.
-/
theorem mul_conj_apply {R : Type*} [CommRing R] {n : ℕ} (fr fri : Fin n → R) (M N : Matrix (Fin n) (Fin n) R)
    (a b : Fin n) :
    (N * (Matrix.diagonal fri * M * Matrix.diagonal fr)) a b = ∑ k, N a k * (fri k * M k b * fr b) := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

variable {D : Formalism.BasicNotions.D7}

/- English proof (translation)
Establish `h` using `fun k => clear_one (fun q => D.s.atP q) p (z k)`. Use `choose t ht0 htz using h`. Use `⟨∏ k, t k, Finset.prod_ne_zero_iff.2 fun k _ => ht0 k, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ k), map_mul, map_mul, map_mul, mul_comm (algebraMap _ _ ((D.s.atP p).ιF (algebraMap _ _ (t k)))), mul_assoc]`. Conclude with `Subring.mul_mem _ (alg_mem_O (fun q => D.s.atP q) p (iotaF_int_mem (fun q => D.s.atP q) p _)) (htz k)`.
-/
theorem clear_at (p : PlF D) {ι : Type} [Fintype ι] (z : ι → (D.s.atP p).Ep) :
    ∃ c : 𝓞 D.host.F, c ≠ 0 ∧ ∀ k,
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F c)) * z k ∈
        (D.s.atP p).O := by
  have h := fun k => clear_one (fun q => D.s.atP q) p (z k)
  choose t ht0 htz using h
  refine ⟨∏ k, t k, Finset.prod_ne_zero_iff.2 fun k _ => ht0 k, fun k => ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), map_mul, map_mul, map_mul,
    mul_comm (algebraMap _ _ ((D.s.atP p).ιF (algebraMap _ _ (t k)))), mul_assoc]
  exact Subring.mul_mem _ (alg_mem_O (fun q => D.s.atP q) p (iotaF_int_mem (fun q => D.s.atP q) p _)) (htz k)

variable {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {δ : ∀ p : PlF D, (D.s.atP p).Fp}

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Take `⟨Y, -, ⟨w₀, -, ⟨ξ, η⟩, hYeq⟩, rfl⟩` from `hO`. Use `set Zd : LocDat D := ⟨δ, M, hA⟩`. Establish `hR : (D.s.atP p).split = none`. Establish `h` using `(hA p).2.2.2.2.2`. Rewrite `h` using `[hM]`.

Consider the cases of `h' : (D.s.atP p).split with`. Consider the case `none => rfl`. Consider the case `some sg => rw [h'] at h`. Conclude with `h.elim`. Establish `hRO : (M p).R = (D.s.atP p).O`.

Simplify using `only [Loc.Model.R, hM]`. Conclude with `(hA p).2.2.2.1`. Use `set ι := (D.s.atP p).ιE`. Use `set al := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep`. Use `set fr : Fin (D.R.rS + 1) → (D.s.atP p).Ep := fun a => al (cf Zd p a)`.

Use `set fri : Fin (D.R.rS + 1) → (D.s.atP p).Ep := fun a => al (cfi Zd p a)`. Establish `hfr : ∀ a, fri a * fr a = 1` using `fun a => by simp only [fr, fri, ← map_mul, cfi_cf, map_one]`. Establish `hfr' : ∀ a, fr a * fri a = 1` using `fun a => by simp only [fr, fri, ← map_mul, cf_cfi, map_one]`. Establish `hmod : Matrix.diagonal fr * (ptMat w).map ι * Matrix.diagonal fr = modMat δ (D.mem u).A.T (D.mem u').A.T p w`. Use extensionality with `a b`.

Rewrite using `[modMat_apply', Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply']`. Distinguish the cases in `hb : b = sgF w a`. Rewrite using `[if_pos hb, if_pos hb, modMat_blk Zd]`. Simplify using `only [twist, qE, tau0, hR, Ring.inverse_one, mul_one, ite_self, sub_zero, map_mul, fr]`. Substitute `hb` using the available equality.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hb, if_neg hb, map_zero, mul_zero, zero_mul]`. Use `set g := Loc.uLow ξ with hgdef`. Use `set h := Loc.uUp w₀ η with hhdef`. Establish `hg : IsLo g` using `isLo_uLow ξ`.

Establish `hh : IsUp h` using `isUp_uUp w₀ η`. Establish `hgu : IsUnit g.det` using `by rw [det_lo' hg]; exact isUnit_one`. Establish `hhu : IsUnit h.det` using `by rw [det_up' hh]; exact isUnit_one`. Take `⟨c, hc0, hcz⟩` from `clear_at p (ι := Fin (D.R.rS + 1) × Fin (D.R.rS + 1) × Fin (D.R.rS + 1) × Bool) (fun k => if k.2.2.2 then fr k.1 * fri k.2.1 * g⁻¹ k.2.1 k.2.2.1 else h⁻¹ k.1 k.2.1 * fri k.2.1 * fr k.2.2.1)`. Use `set ac := al ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F c)) with hacdef`.

Use `⟨Matrix.diagonal fri * g * Matrix.diagonal fr, Matrix.diagonal fr * h * Matrix.diagonal fri, c, hc0, isLo_conj hg fri fr hfr, isUp_conj hh fr fri hfr', ?_⟩` and prove the remaining obligations. Introduce `L U hL hU hLc hUc`. Use `choose oL hoL hLeq using hLc`. Use `choose oU hoU hUeq using hUc`. Use `set l' := Matrix.diagonal fr * L.map ι * Matrix.diagonal fri with hl'`.

Use `set ρ' := Matrix.diagonal fri * U.map ι * Matrix.diagonal fr with hρ'`. Establish `hLmap : L.map ι = Matrix.diagonal fri * g * Matrix.diagonal fr + ac • Matrix.of oL`. Use extensionality with `a b`. Use `hLeq a b` as an intermediate fact. Simplify using `only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]`.

Rewrite using `[← this]`. Expand and normalize the polynomial expressions, which then agree. Establish `hUmap : U.map ι = Matrix.diagonal fr * h * Matrix.diagonal fri + ac • Matrix.of oU`. Use extensionality with `a b`. Use `hUeq a b` as an intermediate fact.

Simplify using `only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]`. Rewrite using `[← this]`. Expand and normalize the polynomial expressions, which then agree. Establish `hdd : Matrix.diagonal fr * Matrix.diagonal fri = 1`. Rewrite using `[Matrix.diagonal_mul_diagonal]`.

Simplify using `[hfr']`. Establish `hdd' : Matrix.diagonal fri * Matrix.diagonal fr = 1`. Rewrite using `[Matrix.diagonal_mul_diagonal]`. Simplify using `[hfr]`. Establish `e1 : Matrix.diagonal fr * (Matrix.diagonal fri * g * Matrix.diagonal fr) * Matrix.diagonal fri = g`.

Rewrite using `[show Matrix.diagonal fr * (Matrix.diagonal fri * g * Matrix.diagonal fr) * Matrix.diagonal fri = (Matrix.diagonal fr * Matrix.diagonal fri) * g * (Matrix.diagonal fr * Matrix.diagonal fri) by`. Simplify using `only [Matrix.mul_assoc], hdd, Matrix.one_mul, Matrix.mul_one]`. Establish `e1' : Matrix.diagonal fri * (Matrix.diagonal fr * h * Matrix.diagonal fri) * Matrix.diagonal fr = h`. Rewrite using `[show Matrix.diagonal fri * (Matrix.diagonal fr * h * Matrix.diagonal fri) * Matrix.diagonal fr = (Matrix.diagonal fri * Matrix.diagonal fr) * h * (Matrix.diagonal fri * Matrix.diagonal fr) by`. Simplify using `only [Matrix.mul_assoc], hdd', Matrix.one_mul, Matrix.mul_one]`.

Establish `hl'eq : l' = g + ac • (Matrix.diagonal fr * Matrix.of oL * Matrix.diagonal fri)`. Rewrite using `[hl', hLmap, Matrix.mul_add, Matrix.add_mul, e1, Matrix.mul_smul, Matrix.smul_mul]`. Establish `hρ'eq : ρ' = h + ac • (Matrix.diagonal fri * Matrix.of oU * Matrix.diagonal fr)`. Rewrite using `[hρ', hUmap, Matrix.mul_add, Matrix.add_mul, e1', Matrix.mul_smul, Matrix.smul_mul]`. Use `clear_value l' ρ'`.

Use `set lam := l' * g⁻¹ with hlam`. Use `set mu := h⁻¹ * ρ' with hmu`. Use `clear_value lam mu`. Establish `hlamI : TieN.IntLow (M p) lam`. Establish `hlo : IsLo lam`.

Rewrite using `[hlam, hl']`. Conclude with `isLo_mul (isLo_conj (isLo_map ι hL) fr fri hfr') (isLo_inv hg)`. Use `⟨hlo.1, hlo.2, fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[hRO, hlam, hl'eq, Matrix.add_mul, Matrix.mul_nonsing_inv g hgu, Matrix.smul_mul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`. Use `add_mem (by rw [Matrix.one_apply]; split_ifs; exact one_mem _; exact zero_mem _) ?_` and prove the remaining obligations.

Rewrite using `[conj_mul_apply, Finset.mul_sum]`. Use `Subring.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Establish `hz` using `hcz (a, k, b, true)`. Simplify using `only [if_true] at hz`. Establish `e : ac * (fr a * Matrix.of oL a k * fri k * g⁻¹ k b) = oL a k * (ac * (fr a * fri k * g⁻¹ k b))`.

Rewrite using `[Matrix.of_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Subring.mul_mem _ (hoL a k) hz`. Establish `hmuI : TieN.IntUp (M p) mu`.

Establish `hup : IsUp mu`. Rewrite using `[hmu, hρ']`. Conclude with `isUp_mul (isUp_inv hh) (isUp_conj (isUp_map ι hU) fri fr hfr)`. Use `⟨hup.1, fun a b hab => hup.2 b a hab, fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[hRO, hmu, hρ'eq, Matrix.mul_add, Matrix.nonsing_inv_mul h hhu, Matrix.mul_smul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`.

Use `add_mem (by rw [Matrix.one_apply]; split_ifs; exact one_mem _; exact zero_mem _) ?_` and prove the remaining obligations. Rewrite using `[mul_conj_apply, Finset.mul_sum]`. Use `Subring.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Establish `hz` using `hcz (a, k, b, false)`. Simplify using `only [Bool.false_eq_true, if_false] at hz`.

Establish `e : ac * (h⁻¹ a k * (fri k * Matrix.of oU k b * fr b)) = oU k b * (ac * (h⁻¹ a k * fri k * fr b))`. Rewrite using `[Matrix.of_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Subring.mul_mem _ (hoU k b) hz`.

Establish `hZ : (L * ptMat w * U * Sg D.host.E D.R.rS) * Sg D.host.E D.R.rS = L * ptMat w * U`. Rewrite using `[Matrix.mul_assoc, sg_sq, Matrix.mul_one]`. Establish `hY1 : CntLocal.ZZP (M` using `M) δ u u' p (L * ptMat w * U * Sg D.host.E D.R.rS) * LsDatumB.sgnP p = lam * Y * mu := by`. Rewrite using `[zzp_sgn_ord Zd u u' p hM, hZ, Matrix.map_mul, Matrix.map_mul]`. Use `show Matrix.diagonal fr * (L.map ι * (ptMat w).map ι * U.map ι) * Matrix.diagonal fr = _`.

Rewrite using `[regroup fr fri hfr, hmod, ← hl', ← hρ', hYeq]`. Establish `e1 : l' = lam * g` using `by rw [hlam, Matrix.mul_assoc, Matrix.nonsing_inv_mul g hgu, Matrix.mul_one]`. Establish `e2 : ρ' = h * mu` using `by rw [hmu, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv h hhu, Matrix.one_mul]`. Rewrite using `[e1, e2]`. Simplify using `only [Matrix.mul_assoc]`.

Establish `hlamu : IsUnit lam.det` using `by rw [det_lo' ⟨hlamI.1, hlamI.2.1⟩]; exact isUnit_one`. Establish `hmuu : IsUnit mu.det` using `by rw [det_up' ⟨hmuI.1, fun a b hab => hmuI.2.1 b a hab⟩]; exact isUnit_one`. Establish `h2 : Y = lam⁻¹ * (lam * Y * mu) * mu⁻¹`. Rewrite using `[show lam⁻¹ * (lam * Y * mu) * mu⁻¹ = (lam⁻¹ * lam) * Y * (mu * mu⁻¹) by simp only [Matrix.mul_assoc], Matrix.nonsing_inv_mul lam hlamu, Matrix.mul_nonsing_inv mu hmuu, Matrix.one_mul, Matrix.mul_one]`. Unfold `tupZ`.

Conclude with `kkOrb_eq_of hlamI hmuI (intLow_inv hlamI) (intUp_inv hmuI) hY1 (by rw [hY1]; exact h2)`.
-/
theorem locReal_ord (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D)
    (hM : (M p).split = none) (O : Set (MatP D p)) (hO : IsLCls M δ (D.mem u).A.T (D.mem u').A.T p w O) :
    ∃ (Lp Up : MatP D p) (c : 𝓞 D.host.F), c ≠ 0 ∧ IsLo Lp ∧ IsUp Up ∧
      ∀ L U : PairVal.MatR D, IsLo L → IsUp U →
        (∀ a b, ∃ o ∈ (D.s.atP p).O, (D.s.atP p).ιE (L a b) - Lp a b =
          algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F c)) * o) →
        (∀ a b, ∃ o ∈ (D.s.atP p).O, (D.s.atP p).ιE (U a b) - Up a b =
          algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F c)) * o) →
        tupZ M δ u u' (L * ptMat w * U * Sg D.host.E D.R.rS) p = O := by
  obtain ⟨Y, -, ⟨w₀, -, ⟨ξ, η⟩, hYeq⟩, rfl⟩ := hO
  set Zd : LocDat D := ⟨δ, M, hA⟩
  have hR : (D.s.atP p).split = none := by
    have h := (hA p).2.2.2.2.2
    rw [hM] at h
    cases h' : (D.s.atP p).split with
    | none => rfl
    | some sg => rw [h'] at h; exact h.elim
  have hRO : (M p).R = (D.s.atP p).O := by
    simp only [Loc.Model.R, hM]; exact (hA p).2.2.2.1
  set ι := (D.s.atP p).ιE
  set al := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep
  set fr : Fin (D.R.rS + 1) → (D.s.atP p).Ep := fun a => al (cf Zd p a)
  set fri : Fin (D.R.rS + 1) → (D.s.atP p).Ep := fun a => al (cfi Zd p a)
  have hfr : ∀ a, fri a * fr a = 1 := fun a => by simp only [fr, fri, ← map_mul, cfi_cf, map_one]
  have hfr' : ∀ a, fr a * fri a = 1 := fun a => by simp only [fr, fri, ← map_mul, cf_cfi, map_one]
  have hmod : Matrix.diagonal fr * (ptMat w).map ι * Matrix.diagonal fr =
      modMat δ (D.mem u).A.T (D.mem u').A.T p w := by
    ext a b
    rw [modMat_apply', Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply']
    by_cases hb : b = sgF w a
    · rw [if_pos hb, if_pos hb, modMat_blk Zd]
      simp only [twist, qE, tau0, hR, Ring.inverse_one, mul_one, ite_self, sub_zero, map_mul, fr]
      subst hb
      ring
    · rw [if_neg hb, if_neg hb, map_zero, mul_zero, zero_mul]
  set g := Loc.uLow ξ with hgdef
  set h := Loc.uUp w₀ η with hhdef
  have hg : IsLo g := isLo_uLow ξ
  have hh : IsUp h := isUp_uUp w₀ η
  have hgu : IsUnit g.det := by rw [det_lo' hg]; exact isUnit_one
  have hhu : IsUnit h.det := by rw [det_up' hh]; exact isUnit_one

  obtain ⟨c, hc0, hcz⟩ := clear_at p (ι := Fin (D.R.rS + 1) × Fin (D.R.rS + 1) × Fin (D.R.rS + 1) × Bool)
    (fun k => if k.2.2.2 then fr k.1 * fri k.2.1 * g⁻¹ k.2.1 k.2.2.1 else h⁻¹ k.1 k.2.1 * fri k.2.1 * fr k.2.2.1)
  set ac := al ((D.s.atP p).ιF (algebraMap (𝓞 D.host.F) D.host.F c)) with hacdef
  refine ⟨Matrix.diagonal fri * g * Matrix.diagonal fr, Matrix.diagonal fr * h * Matrix.diagonal fri, c, hc0,
    isLo_conj hg fri fr hfr, isUp_conj hh fr fri hfr', ?_⟩
  intro L U hL hU hLc hUc
  choose oL hoL hLeq using hLc
  choose oU hoU hUeq using hUc
  set l' := Matrix.diagonal fr * L.map ι * Matrix.diagonal fri with hl'
  set ρ' := Matrix.diagonal fri * U.map ι * Matrix.diagonal fr with hρ'

  have hLmap : L.map ι = Matrix.diagonal fri * g * Matrix.diagonal fr + ac • Matrix.of oL := by
    ext a b
    have := hLeq a b
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [← this]; ring
  have hUmap : U.map ι = Matrix.diagonal fr * h * Matrix.diagonal fri + ac • Matrix.of oU := by
    ext a b
    have := hUeq a b
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [← this]; ring
  have hdd : Matrix.diagonal fr * Matrix.diagonal fri = 1 := by
    rw [Matrix.diagonal_mul_diagonal]; simp [hfr']
  have hdd' : Matrix.diagonal fri * Matrix.diagonal fr = 1 := by
    rw [Matrix.diagonal_mul_diagonal]; simp [hfr]
  have e1 : Matrix.diagonal fr * (Matrix.diagonal fri * g * Matrix.diagonal fr) * Matrix.diagonal fri = g := by
    rw [show Matrix.diagonal fr * (Matrix.diagonal fri * g * Matrix.diagonal fr) * Matrix.diagonal fri =
      (Matrix.diagonal fr * Matrix.diagonal fri) * g * (Matrix.diagonal fr * Matrix.diagonal fri) by
        simp only [Matrix.mul_assoc], hdd, Matrix.one_mul, Matrix.mul_one]
  have e1' : Matrix.diagonal fri * (Matrix.diagonal fr * h * Matrix.diagonal fri) * Matrix.diagonal fr = h := by
    rw [show Matrix.diagonal fri * (Matrix.diagonal fr * h * Matrix.diagonal fri) * Matrix.diagonal fr =
      (Matrix.diagonal fri * Matrix.diagonal fr) * h * (Matrix.diagonal fri * Matrix.diagonal fr) by
        simp only [Matrix.mul_assoc], hdd', Matrix.one_mul, Matrix.mul_one]
  have hl'eq : l' = g + ac • (Matrix.diagonal fr * Matrix.of oL * Matrix.diagonal fri) := by
    rw [hl', hLmap, Matrix.mul_add, Matrix.add_mul, e1, Matrix.mul_smul, Matrix.smul_mul]
  have hρ'eq : ρ' = h + ac • (Matrix.diagonal fri * Matrix.of oU * Matrix.diagonal fr) := by
    rw [hρ', hUmap, Matrix.mul_add, Matrix.add_mul, e1', Matrix.mul_smul, Matrix.smul_mul]
  clear_value l' ρ'
  set lam := l' * g⁻¹ with hlam
  set mu := h⁻¹ * ρ' with hmu
  clear_value lam mu
  have hlamI : TieN.IntLow (M p) lam := by
    have hlo : IsLo lam := by
      rw [hlam, hl']; exact isLo_mul (isLo_conj (isLo_map ι hL) fr fri hfr') (isLo_inv hg)
    refine ⟨hlo.1, hlo.2, fun a b => ?_⟩
    rw [hRO, hlam, hl'eq, Matrix.add_mul, Matrix.mul_nonsing_inv g hgu, Matrix.smul_mul, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul]
    refine add_mem (by rw [Matrix.one_apply]; split_ifs; exact one_mem _; exact zero_mem _) ?_
    rw [conj_mul_apply, Finset.mul_sum]
    refine Subring.sum_mem _ fun k _ => ?_
    have hz := hcz (a, k, b, true)
    simp only [if_true] at hz
    have e : ac * (fr a * Matrix.of oL a k * fri k * g⁻¹ k b) = oL a k * (ac * (fr a * fri k * g⁻¹ k b)) := by
      rw [Matrix.of_apply]; ring
    rw [e]
    exact Subring.mul_mem _ (hoL a k) hz
  have hmuI : TieN.IntUp (M p) mu := by
    have hup : IsUp mu := by
      rw [hmu, hρ']; exact isUp_mul (isUp_inv hh) (isUp_conj (isUp_map ι hU) fri fr hfr)
    refine ⟨hup.1, fun a b hab => hup.2 b a hab, fun a b => ?_⟩
    rw [hRO, hmu, hρ'eq, Matrix.mul_add, Matrix.nonsing_inv_mul h hhu, Matrix.mul_smul, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul]
    refine add_mem (by rw [Matrix.one_apply]; split_ifs; exact one_mem _; exact zero_mem _) ?_
    rw [mul_conj_apply, Finset.mul_sum]
    refine Subring.sum_mem _ fun k _ => ?_
    have hz := hcz (a, k, b, false)
    simp only [Bool.false_eq_true, if_false] at hz
    have e : ac * (h⁻¹ a k * (fri k * Matrix.of oU k b * fr b)) = oU k b * (ac * (h⁻¹ a k * fri k * fr b)) := by
      rw [Matrix.of_apply]; ring
    rw [e]
    exact Subring.mul_mem _ (hoU k b) hz

  have hZ : (L * ptMat w * U * Sg D.host.E D.R.rS) * Sg D.host.E D.R.rS = L * ptMat w * U := by
    rw [Matrix.mul_assoc, sg_sq, Matrix.mul_one]
  have hY1 : CntLocal.ZZP (M := M) δ u u' p (L * ptMat w * U * Sg D.host.E D.R.rS) * LsDatumB.sgnP p =
      lam * Y * mu := by
    rw [zzp_sgn_ord Zd u u' p hM, hZ, Matrix.map_mul, Matrix.map_mul]
    show Matrix.diagonal fr * (L.map ι * (ptMat w).map ι * U.map ι) * Matrix.diagonal fr = _
    rw [regroup fr fri hfr, hmod, ← hl', ← hρ', hYeq]
    have e1 : l' = lam * g := by rw [hlam, Matrix.mul_assoc, Matrix.nonsing_inv_mul g hgu, Matrix.mul_one]
    have e2 : ρ' = h * mu := by rw [hmu, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv h hhu, Matrix.one_mul]
    rw [e1, e2]
    simp only [Matrix.mul_assoc]
  have hlamu : IsUnit lam.det := by rw [det_lo' ⟨hlamI.1, hlamI.2.1⟩]; exact isUnit_one
  have hmuu : IsUnit mu.det := by rw [det_up' ⟨hmuI.1, fun a b hab => hmuI.2.1 b a hab⟩]; exact isUnit_one
  have h2 : Y = lam⁻¹ * (lam * Y * mu) * mu⁻¹ := by
    rw [show lam⁻¹ * (lam * Y * mu) * mu⁻¹ = (lam⁻¹ * lam) * Y * (mu * mu⁻¹) by simp only [Matrix.mul_assoc],
      Matrix.nonsing_inv_mul lam hlamu, Matrix.mul_nonsing_inv mu hmuu, Matrix.one_mul, Matrix.mul_one]
  unfold tupZ
  exact kkOrb_eq_of hlamI hmuI (intLow_inv hlamI) (intUp_inv hmuI) hY1 (by rw [hY1]; exact h2)

end Real

end Formalism.L2.SG.Pf.PCountEx
