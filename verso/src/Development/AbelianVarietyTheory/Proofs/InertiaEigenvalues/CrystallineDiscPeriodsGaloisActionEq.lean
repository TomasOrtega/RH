import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinAinfDiscIsDomainNormBoundsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscToDiscInjectiveOfAdicBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisinStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP

/- English proof (translation)
Establish `hp : ∀ p : Polynomial R, f p = g p` using `fun p => by`. Proceed by induction on `p using Polynomial.induction_on with`. Consider the case `C a => simpa using hC a`. Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `monomial n a _ => simp [hC, hX]`.

Use `ext1 a`. Rewrite using `[← sub_eq_zero]`. Use `hsep _ fun n => ?_` and prove the remaining obligations. Rewrite using `[a.eq_X_pow_mul_shift_add_trunc n, map_add, map_add, hp, map_mul, map_mul, map_pow, map_pow, ← hX]`. Conclude with `⟨_, by rw [add_sub_add_right_eq_sub, ← mul_sub]⟩`.
-/
theorem ringHom_ext_of_sep_galPer {R B : Type} [CommRing R] [CommRing B] {f g : R⟦X⟧ →+* B}
    (hC : ∀ r, f (C r) = g (C r)) (hX : f X = g X) (hsep : ∀ b : B, (∀ n, f X ^ n ∣ b) → b = 0) :
    f = g := by
  have hp : ∀ p : Polynomial R, f p = g p := fun p => by
    induction p using Polynomial.induction_on with
    | C a => simpa using hC a
    | add p q hp hq => simp [hp, hq]
    | monomial n a _ => simp [hC, hX]
  ext1 a
  rw [← sub_eq_zero]
  refine hsep _ fun n => ?_
  rw [a.eq_X_pow_mul_shift_add_trunc n, map_add, map_add, hp, map_mul, map_mul, map_pow, map_pow, ← hX]
  exact ⟨_, by rw [add_sub_add_right_eq_sub, ← mul_sub]⟩

/- English proof (translation)
Establish `h2 : (A - B) * P = 0` using `by rw [Matrix.sub_mul, h, sub_self]`. Establish `h3 : P.det • (A - B) = 0`. Rewrite using `[← Matrix.mul_one (A - B), ← Matrix.mul_smul, ← Matrix.mul_adjugate P, ← Matrix.mul_assoc, h2, Matrix.zero_mul]`. Rewrite using `[← sub_eq_zero]`. Use extensionality with `i j`.

Establish `h4` using `congr_fun₂ h3 i j`. Rewrite `h4` using `[Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]`. Rewrite using `[Matrix.zero_apply]`. Conclude with `(mul_eq_zero.1 h4).resolve_left hP`.
-/
theorem mat_mul_right_cancel_galPer {R : Type} [CommRing R] [IsDomain R] {n : Type} [Fintype n] [DecidableEq n]
    {A B P : Matrix n n R} (hP : P.det ≠ 0) (h : A * P = B * P) : A = B := by
  have h2 : (A - B) * P = 0 := by rw [Matrix.sub_mul, h, sub_self]
  have h3 : P.det • (A - B) = 0 := by
    rw [← Matrix.mul_one (A - B), ← Matrix.mul_smul, ← Matrix.mul_adjugate P, ← Matrix.mul_assoc, h2,
      Matrix.zero_mul]
  rw [← sub_eq_zero]
  ext i j
  have h4 := congr_fun₂ h3 i j
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h4
  rw [Matrix.zero_apply]
  exact (mul_eq_zero.1 h4).resolve_left hP

/- English proof (translation)
Use extensionality with `i j`. Establish `h1` using `congr_fun₂ h i j`. Rewrite `h1` using `[Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]`. Conclude with `mul_left_cancel₀ hc h1`.
-/
theorem mat_smul_cancel_galPer {R : Type} [CommRing R] [IsDomain R] {m n : Type} {c : R} (hc : c ≠ 0)
    {A B : Matrix m n R} (h : c • A = c • B) : A = B := by
  ext i j
  have h1 := congr_fun₂ h i j
  rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul] at h1
  exact mul_left_cancel₀ hc h1

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

namespace BK

variable (bk : BK K)

/- English proof (translation)
Establish `e1 : bk.Ep - Polynomial.X ^ bk.Ep.natDegree = ∑ i ∈ Finset.range bk.Ep.natDegree, Polynomial.C (bk.Ep.coeff i) * Polynomial.X ^ i`. Rewrite using `[sub_eq_iff_eq_add']`. Conclude with `bk.monic.as_sum`. Establish `h1 : (l : Polynomial (Wq l bk.a)) ∣ bk.Ep - Polynomial.X ^ bk.Ep.natDegree`. Rewrite using `[e1]`.

Use `Finset.dvd_sum fun i hi => ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `bk.dvd_coeff i (Finset.mem_range.1 hi)`. Conclude with `⟨Polynomial.C c * Polynomial.X ^ i, by rw [hc, map_mul, map_natCast]; ring⟩`. Establish `h2 : (l : bk.S) ∣ bk.E - X ^ bk.Ep.natDegree`. Use `map_dvd (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) h1` as an intermediate fact.

Simplify using `using this`. Establish `e2 : (X : bk.S) ^ bk.Ep.natDegree = bk.E - (bk.E - X ^ bk.Ep.natDegree)` using `by ring`. Rewrite using `[e2]`. Conclude with `Submodule.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) (Ideal.mem_sup_left (Ideal.mem_span_singleton.2 h2))`.
-/
theorem X_pow_mem_J_galPer : (X : bk.S) ^ bk.Ep.natDegree ∈ bk.J := by
  have e1 : bk.Ep - Polynomial.X ^ bk.Ep.natDegree =
      ∑ i ∈ Finset.range bk.Ep.natDegree, Polynomial.C (bk.Ep.coeff i) * Polynomial.X ^ i := by
    rw [sub_eq_iff_eq_add']
    exact bk.monic.as_sum
  have h1 : (l : Polynomial (Wq l bk.a)) ∣ bk.Ep - Polynomial.X ^ bk.Ep.natDegree := by
    rw [e1]
    refine Finset.dvd_sum fun i hi => ?_
    obtain ⟨c, hc⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
    exact ⟨Polynomial.C c * Polynomial.X ^ i, by rw [hc, map_mul, map_natCast]; ring⟩
  have h2 : (l : bk.S) ∣ bk.E - X ^ bk.Ep.natDegree := by
    have := map_dvd (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) h1
    simpa using this
  have e2 : (X : bk.S) ^ bk.Ep.natDegree = bk.E - (bk.E - X ^ bk.Ep.natDegree) := by ring
  rw [e2]
  exact Submodule.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    (Ideal.mem_sup_left (Ideal.mem_span_singleton.2 h2))

/- English proof (translation)
Take `⟨ι, ⟨tb⟩⟩` from `GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk`. Establish `hc` using `tb.complete`. Use `IsHausdorff.haus hc.toIsHausdorff b fun n => ?_` and prove the remaining obligations. Rewrite using `[SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]`. Take `⟨c, hc⟩` from `hb (bk.Ep.natDegree * n)`.

Rewrite using `[hc, pow_mul, ← map_pow]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_map_of_mem bk.ev bk.X_pow_mem_J_galPer) n)`.
-/
theorem ev_sep_galPer (b : Ainf l) (hb : ∀ n, bk.ev X ^ n ∣ b) : b = 0 := by
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hc := tb.complete
  refine IsHausdorff.haus hc.toIsHausdorff b fun n => ?_
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
  obtain ⟨c, hc⟩ := hb (bk.Ep.natDegree * n)
  rw [hc, pow_mul, ← map_pow]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_map_of_mem bk.ev bk.X_pow_mem_J_galPer) n)

/- English proof (translation)
Establish `hg' : Per.σF (g : GQ l) bk.flat = bk.flat` using `hg`. Establish `hX : ((Per.σA (g : GQ l)).comp bk.ev) X = bk.ev X` using `by show Per.σA _ (bk.ev X) = bk.ev X`. Rewrite using `[bk.ev_X, GlobalTheory.RingIface.sigA_teich, hg']`. Establish `h` using `ringHom_ext_of_sep_galPer (f := (Per.σA (g : GQ l)).comp bk.ev) (g := bk.ev) (fun w => by show Per.σA _ (bk.ev (C w)) = bk.ev (C w)`. Rewrite using `[bk.ev_C, bk.gal_w]) hX`.

Use the proof step `(fun b hb => bk.ev_sep_galPer b fun n => by rw [← hX]; exact hb n)`. Conclude with `RingHom.congr_fun h a`.
-/
theorem σA_ev_galPer {g : ↥(GK K)} (hg : bk.FixFlat g) (a : bk.S) : Per.σA (g : GQ l) (bk.ev a) = bk.ev a := by
  have hg' : Per.σF (g : GQ l) bk.flat = bk.flat := hg
  have hX : ((Per.σA (g : GQ l)).comp bk.ev) X = bk.ev X := by
    show Per.σA _ (bk.ev X) = bk.ev X
    rw [bk.ev_X, GlobalTheory.RingIface.sigA_teich, hg']
  have h := ringHom_ext_of_sep_galPer (f := (Per.σA (g : GQ l)).comp bk.ev) (g := bk.ev)
    (fun w => by
      show Per.σA _ (bk.ev (C w)) = bk.ev (C w)
      rw [bk.ev_C, bk.gal_w]) hX
    (fun b hb => bk.ev_sep_galPer b fun n => by rw [← hX]; exact hb n)
  exact RingHom.congr_fun h a

/- English proof (translation)
Take `⟨ι, ⟨tb⟩⟩` from `GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk`. Establish `key : ∀ a, tb.c tb.i₀ (bk.ev a * tb.b tb.i₀) = a` using `fun a => by`. Rewrite using `[tb.c_mul, tb.c_self, mul_one]`. Introduce `a a' h`. Rewrite using `[← key a, ← key a', h]`.
-/
theorem ev_injective_galPer : Function.Injective bk.ev := by
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have key : ∀ a, tb.c tb.i₀ (bk.ev a * tb.b tb.i₀) = a := fun a => by
    rw [tb.c_mul, tb.c_self, mul_one]
  intro a a' h
  rw [← key a, ← key a', h]

/- English proof (translation)
Establish `hl1 : (1 : ℝ≥0) < l` using `by exact_mod_cast hl.out.one_lt`. Establish `he : (0 : ℝ) < bk.Ep.natDegree` using `by exact_mod_cast bk.deg_pos`. Use `⟨NNReal.rpow_pos (zero_lt_one.trans hl1), ?_⟩` and prove the remaining obligations. Conclude with `NNReal.rpow_lt_one_of_one_lt_of_neg hl1 (neg_neg_of_pos (one_div_pos.2 he))`.
-/
theorem ρ₀_pos_lt_one_galPer : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  have hl1 : (1 : ℝ≥0) < l := by exact_mod_cast hl.out.one_lt
  have he : (0 : ℝ) < bk.Ep.natDegree := by exact_mod_cast bk.deg_pos
  refine ⟨NNReal.rpow_pos (zero_lt_one.trans hl1), ?_⟩
  exact NNReal.rpow_lt_one_of_one_lt_of_neg hl1 (neg_neg_of_pos (one_div_pos.2 he))

end BK

/- English proof (translation)
Introduce `l _ K bk τ _ d ρ _ s g hg G hG`. Take `⟨h0, h1⟩` from `bk.ρ₀_pos_lt_one_galPer`. Use `haveI : IsDomain (bk.DA bk.ρ₀) := (GlobalTheory.T.breuilKisin_ainfDisc_isDomain_norm_bounds l K bk bk.ρ₀ h0 h1).1`. Take `⟨ι, ⟨tb⟩⟩` from `GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk`. Establish `hinj : Function.Injective bk.iA` using `(GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk (Ainf l) bk.ev ι tb bk.ρ₀ h0 h1).1`.

Establish `hGS : ∀ a, G (bk.iA (bk.ev a)) = bk.iA (bk.ev a)` using `fun a => by show G (toDisc l (bk.ev X) bk.ρ₀ (bk.ev a)) = _`. Rewrite using `[hG.ext, bk.σA_ev_galPer hg]`. Establish `hGτ : G (bk.iA τ) = bk.iA (Per.σA (g : GQ l) τ)` using `hG.ext τ`. Use `⟨fun j hj x => ?_, ?_⟩` and prove the remaining obligations. Establish `hGj : IsDiscMap bk.ev (G.comp j)` using `⟨fun a => by show G (j (toDisc l X bk.ρ₀ a)) = _`.

Rewrite using `[hj.ext]`. Conclude with `hGS a,`. Use `fun x => (hG.norm_le _).trans (hj.norm_le x)⟩`. Conclude with `RingHom.congr_fun (IsDiscMap.unique hGj hj) x`. Establish `he : bk.iA (bk.ev bk.E) ≠ 0` using `fun h => bk.E_ne_zero (bk.ev_injective_galPer (hinj (h.trans (map_zero _).symm) |>.trans (map_zero _).symm))`.

Establish `hl0 : ((l : ℕ) : bk.DA bk.ρ₀) ≠ 0` using `(isUnit_l_disc l (bk.ev X) bk.ρ₀).ne_zero`. Establish `hdet : (s.X'.map bk.iS).det ≠ 0`. Introduce `h0'`. Establish `hm` using `congrArg (fun M => (M.map bk.iS).det) s.X_mul`. Rewrite `hm` using `[Matrix.map_mul, Matrix.det_mul, h0', mul_zero]`.

Establish `hc : (((l : bk.S) ^ s.c₂ * bk.E ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) bk.S)).map bk.iS = bk.iS ((l : bk.S) ^ s.c₂ * bk.E ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))`. Use extensionality with `i j`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`. Rewrite `hm` using `[hc, Matrix.det_smul, Matrix.det_one, mul_one]`. Establish `h3` using `pow_eq_zero_iff'.1 hm.symm`.

Rewrite `h3` using `[map_mul, map_pow, map_pow, map_natCast]`. Conclude with `mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ he) h3.1`. Establish `hX' : (s.X'.map bk.iS).map G = s.X'.map bk.iS`. Rewrite using `[Matrix.map_map]`. Use `congr 1`.

Use function extensionality and compare the values at `a`. Conclude with `hGS a`. Establish `hσ : bk.iA (Per.σA (g : GQ l) (bk.ev bk.E * τ)) = bk.iA (bk.ev bk.E) * G (bk.iA τ)`. Rewrite using `[map_mul, bk.σA_ev_galPer hg, map_mul, hGτ]`. Establish `h` using `s.gal g G hG`.

Rewrite `h` using `[Matrix.map_mul, hX', hσ, map_mul, mul_pow, mul_pow, mul_smul, mul_smul]`. Establish `h'` using `mat_smul_cancel_galPer (pow_ne_zero _ he) h`. Use `mat_mul_right_cancel_galPer hdet ?_` and prove the remaining obligations. Rewrite using `[Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc]`. Conclude with `h'`.
-/
theorem seed_gal_periods : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ),
    ∀ g : ↥(GK K), bk.FixFlat g → ∀ G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (Per.σA (g : GQ l)) G →
      (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → ∀ x, G (j x) = j x) ∧
      bk.iA τ ^ s.N • ((ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * s.W.map G) =
        G (bk.iA τ) ^ s.N • s.W := by
  intro l _ K bk τ _ d ρ _ s g hg G hG
  obtain ⟨h0, h1⟩ := bk.ρ₀_pos_lt_one_galPer
  haveI : IsDomain (bk.DA bk.ρ₀) := (GlobalTheory.T.breuilKisin_ainfDisc_isDomain_norm_bounds l K bk bk.ρ₀ h0 h1).1
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hinj : Function.Injective bk.iA := (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk (Ainf l) bk.ev ι tb bk.ρ₀ h0 h1).1
  have hGS : ∀ a, G (bk.iA (bk.ev a)) = bk.iA (bk.ev a) := fun a => by
    show G (toDisc l (bk.ev X) bk.ρ₀ (bk.ev a)) = _
    rw [hG.ext, bk.σA_ev_galPer hg]
  have hGτ : G (bk.iA τ) = bk.iA (Per.σA (g : GQ l) τ) := hG.ext τ
  refine ⟨fun j hj x => ?_, ?_⟩
  · have hGj : IsDiscMap bk.ev (G.comp j) :=
      ⟨fun a => by
        show G (j (toDisc l X bk.ρ₀ a)) = _
        rw [hj.ext]; exact hGS a,
       fun x => (hG.norm_le _).trans (hj.norm_le x)⟩
    exact RingHom.congr_fun (IsDiscMap.unique hGj hj) x
  · have he : bk.iA (bk.ev bk.E) ≠ 0 := fun h =>
      bk.E_ne_zero (bk.ev_injective_galPer (hinj (h.trans (map_zero _).symm) |>.trans (map_zero _).symm))
    have hl0 : ((l : ℕ) : bk.DA bk.ρ₀) ≠ 0 := (isUnit_l_disc l (bk.ev X) bk.ρ₀).ne_zero
    have hdet : (s.X'.map bk.iS).det ≠ 0 := by
      intro h0'
      have hm := congrArg (fun M => (M.map bk.iS).det) s.X_mul
      rw [Matrix.map_mul, Matrix.det_mul, h0', mul_zero] at hm
      have hc : (((l : bk.S) ^ s.c₂ * bk.E ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) bk.S)).map bk.iS =
          bk.iS ((l : bk.S) ^ s.c₂ * bk.E ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
        ext i j
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      rw [hc, Matrix.det_smul, Matrix.det_one, mul_one] at hm
      have h3 := pow_eq_zero_iff'.1 hm.symm
      rw [map_mul, map_pow, map_pow, map_natCast] at h3
      exact mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ he) h3.1
    have hX' : (s.X'.map bk.iS).map G = s.X'.map bk.iS := by
      rw [Matrix.map_map]
      congr 1
      funext a
      exact hGS a
    have hσ : bk.iA (Per.σA (g : GQ l) (bk.ev bk.E * τ)) = bk.iA (bk.ev bk.E) * G (bk.iA τ) := by
      rw [map_mul, bk.σA_ev_galPer hg, map_mul, hGτ]
    have h := s.gal g G hG
    rw [Matrix.map_mul, hX', hσ, map_mul, mul_pow, mul_pow, mul_smul, mul_smul] at h
    have h' := mat_smul_cancel_galPer (pow_ne_zero _ he) h
    refine mat_mul_right_cancel_galPer hdet ?_
    rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc]
    exact h'

end GlobalTheory.BSP
