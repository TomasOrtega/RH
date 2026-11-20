import Formalism.LocalToGlobal.Columns.XiFirstLawAllLevels
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnfoldEquiv

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

/- English proof (translation)
Introduce `x`. Establish `e : ∀ y : Sp E (n + 0), y ∈ LocE.lamY P q n 0 (fun i => i + 1) ↔ y ∈ stdAt E n P`. Introduce `y`. Unfold `LocE.lamY`. Rewrite using `[ciMem_sclLat, ciMem_stdAt]`.

Use `forall_congr' fun l => ?_` and prove the remaining obligations. Unfold `LocE.scE`. Rewrite using `[if_pos (show l.1 < n from l.2), zpow_zero, inv_one, one_mul]`. Rewrite using `[e, e]`. Conclude with `hκ x`.
-/
theorem clT_stab0 {n : ℕ} {κ : Sp E n ≃ₗ[E] Sp E n} (hκ : κ ∈ GLint E n P) :
    κ ∈ stabL E (n + 0) (LocE.lamY P q n 0 (fun i => i + 1)) := by
  intro x
  have e : ∀ y : Sp E (n + 0), y ∈ LocE.lamY P q n 0 (fun i => i + 1) ↔ y ∈ stdAt E n P := by
    intro y
    unfold LocE.lamY
    rw [ciMem_sclLat, ciMem_stdAt]
    refine forall_congr' fun l => ?_
    unfold LocE.scE
    rw [if_pos (show l.1 < n from l.2), zpow_zero, inv_one, one_mul]
  rw [e, e]
  exact hκ x

/- English proof (translation)
Unfold `ocbBEnt`. Distinguish the cases in `hsn : s < n`. Establish `hsc : LocE.scE n (fun i => i + 1) s = 0` using `by unfold LocE.scE; rw [if_pos hsn]`. Rewrite using `[ciEN hsn, LinearEquiv.coe_coe, clL_ext_inX, ocbS_atN_of_lt _ hl, ciInX_apply]`. Distinguish the cases in `hln : l < n`.

Establish `hlc : LocE.scE n (fun i => i + 1) l = 0` using `by unfold LocE.scE; rw [if_pos hln]`. Rewrite using `[dif_pos hln, if_pos ⟨hln, hsn⟩, hsc, hlc, sub_zero, zpow_zero, mul_one, ocbS_eN_single hsn, ocbS_atN_of_lt _ hln]`. Rewrite using `[dif_neg hln, zero_mul, redP_zero, if_neg (fun h => hln h.1), if_neg (by omega)]`. Rewrite using `[LinearEquiv.coe_coe, clX_ext_eN κ₁ (by omega), ocbS_atN_of_lt _ hl]`. Distinguish the cases in `hls : l = s`.

Substitute `hls` using the available equality. Simplify using `only [Loc.eN, if_true, sub_self, zpow_zero, mul_one, redP_one]`. Rewrite using `[if_neg (fun h => hsn h.2)]`. Establish `h1 : Loc.eN E (n + c) s ⟨l, hl⟩ = 0`. Simplify using `only [Loc.eN]`.

Conclude with `if_neg hls`. Rewrite using `[h1, zero_mul, redP_zero, if_neg (fun h => hsn h.2), if_neg hls]`.
-/
theorem clT_extEnt {n c : ℕ} (κ₁ : Sp E n ≃ₗ[E] Sp E n) {l s : ℕ} (hl : l < n + c) (hs : s < n + c) :
    redP P (ocbBEnt n n q (clL_ext c κ₁).toLinearMap l s) =
      if l < n ∧ s < n then redP P (Loc.atN (κ₁ (Loc.eN E n s)) l) else if l = s then 1 else 0 := by
  unfold ocbBEnt
  by_cases hsn : s < n
  · have hsc : LocE.scE n (fun i => i + 1) s = 0 := by unfold LocE.scE; rw [if_pos hsn]
    rw [ciEN hsn, LinearEquiv.coe_coe, clL_ext_inX, ocbS_atN_of_lt _ hl, ciInX_apply]
    by_cases hln : l < n
    · have hlc : LocE.scE n (fun i => i + 1) l = 0 := by unfold LocE.scE; rw [if_pos hln]
      rw [dif_pos hln, if_pos ⟨hln, hsn⟩, hsc, hlc, sub_zero, zpow_zero, mul_one, ocbS_eN_single hsn, ocbS_atN_of_lt _ hln]
    · rw [dif_neg hln, zero_mul, redP_zero, if_neg (fun h => hln h.1), if_neg (by omega)]
  · rw [LinearEquiv.coe_coe, clX_ext_eN κ₁ (by omega), ocbS_atN_of_lt _ hl]
    by_cases hls : l = s
    · subst hls
      simp only [Loc.eN, if_true, sub_self, zpow_zero, mul_one, redP_one]
      rw [if_neg (fun h => hsn h.2)]
    · have h1 : Loc.eN E (n + c) s ⟨l, hl⟩ = 0 := by
        simp only [Loc.eN]
        exact if_neg hls
      rw [h1, zero_mul, redP_zero, if_neg (fun h => hsn h.2), if_neg hls]

end Gen

section Tgt

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)}

/- English proof (translation)
Unfold `Loc.inX`. Apply the tactic sequence `by_cases h : l.1 < n <;> simp [LinearMap.pi_apply, h]`.
-/
theorem clT_inX_apply {k : Type} [CommRing k] {n c : ℕ} (x : Fin n → k) (l : Fin (n + c)) :
    Loc.inX k n c x l = if h : l.1 < n then x ⟨l.1, h⟩ else 0 := by
  unfold Loc.inX
  by_cases h : l.1 < n <;> simp [LinearMap.pi_apply, h]

/- English proof (translation)
Rewrite using `[ciMem_stdAt]`. Introduce `i`. Use `h i.1 i.2` as an intermediate fact. Rewrite `this` using `[ocbS_atN_of_lt _ i.2]`. Then use the resulting hypothesis.
-/
theorem clT_vec_std {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {n : ℕ} {v : Sp E n}
    (h : ∀ l, l < n → IntAt P (Loc.atN v l)) : v ∈ stdAt E n P := by
  rw [ciMem_stdAt]
  intro i
  have := h i.1 i.2
  rwa [ocbS_atN_of_lt _ i.2] at this

/- English proof (translation)
Unfold `ocbBEnt LocE.scE`. Rewrite using `[if_pos hs, if_pos hl, sub_zero, zpow_zero, mul_one]`.
-/
theorem clT_bEnt0 {E : Type} [Field E] {n : ℕ} (q : ℕ) (g : Sp E n →ₗ[E] Sp E n) {l s : ℕ} (hl : l < n) (hs : s < n) :
    ocbBEnt n n q g l s = Loc.atN (g (Loc.eN E n s)) l := by
  unfold ocbBEnt LocE.scE
  rw [if_pos hs, if_pos hl, sub_zero, zpow_zero, mul_one]

set_option maxHeartbeats 800000 in

/- English proof (translation)
Introduce `P hP κ' hκ' hJ w`. Establish `hq : ((qOf P.1 : ℕ) : 𝓞 X.E) ∈ P.1.asIdeal` using `ciQ_mem P.1`. Establish `hu` using `ciQ_notMem_sq hB.hX hB.hPr hP`. Establish `hp` using `ciQOf_prime hB.hPr hP`. Establish `hcard` using `ciCard P.1`.

Establish `hq0 : (qOf P.1 : X.E) ≠ 0` using `ciQ_ne_zero hu`. Establish `hr` using `ocbRanks_step (R := R) hB.hm hi`. Establish `hc' : cOf R i = cOf R (i + 1) + 1`. Unfold `cOf`. Use `hB.hm` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hPhi : PhiAt Ch mu cst.sharp i P.1 = LocE.PhiGS (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) R.k (R.m / 2 - 1) (R.k + R.m - 1) R.t (i + 1) (cOf R i) (R.N i) (cOf R (i + 1)) (R.N (i + 1))`. Unfold `PhiAt`. Rewrite using `[if_pos hP, hB.sharp]`. Both sides reduce to the same expression.

Set `Φ : Loc.SF X.E X.K (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1))` to `LocE.PhiGS (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) R.k (R.m / 2 - 1) (R.k + R.m - 1) R.t (i + 1) (cOf R i) (R.N i) (cOf R (i + 1)) (R.N (i + 1))`. Set `Φr` to `@ocbPhiS (𝓞 X.E ⧸ P.1.asIdeal) (resField P.1) (ocbPsiC Ch σ P.1) (ocbChiC Ch σ P.1) R.k R.m R.t (i + 1) (R.N i) (cOf R (i + 1)) (R.N (i + 1))`. Establish `hsupp0 : ∀ y, Φ y ≠ 0 → ∀ l s, l < R.N (i + 1) + cOf R (i + 1) → s < R.N i + cOf R i → IntAt P.1 (ocbBEnt (R.N i) (R.N (i + 1)) (qOf P.1) y l s)` using `fun y hy => ocbPhiGS_supp (psi0P Ch P.1) (chiP Ch P.1) hr hc' y hy`. Establish `hred0 : ∀ y ybar, (∀ l s, l < R.N (i + 1) + cOf R (i + 1) → s < R.N i + cOf R i → IntAt P.1 (ocbBEnt (R.N i) (R.N (i + 1)) (qOf P.1) y l s)) → (∀ l s, l < R.N (i + 1) + cOf R (i + 1) → s < R.N i + cOf R i → Loc.atN (ybar (Loc.eN _ _ s)) l = redP P.1 (ocbBEnt (R.N i) (R.N (i + 1)) …` using `fun y ybar hint hrd => ocbPhiGS_red hq hu σ (psi0P Ch P.1) (chiP Ch P.1) hr hc' y ybar hint hrd`. Use `set h₀ := clL_ext (cOf R (i + 1)) κ' with hh₀def`.

Establish `hh₀ : h₀ ∈ stabL X.E (R.N (i + 1) + cOf R (i + 1)) (LocE.lamY P.1 (qOf P.1) (R.N (i + 1)) (cOf R (i + 1)) fun i => i + 1)` using `(Subgroup.mem_inf.1 hJ).1`. Take `⟨hbar, hred₀⟩` from `ocbA_red_exists hq0 hh₀`. Take `⟨htsupp, htred⟩` from `ocbT_trans hq0 σ hc' hh₀ hred₀ Φ Φr hsupp0 hred0`. Take `⟨gbar, hgred⟩` from `ocbA_red_exists (n := R.N (i + 1)) (c := 0) hq0 (clT_stab0 (q := qOf P.1) hκ')`. Establish `hent : ∀ l s, l < R.N (i + 1) + cOf R (i + 1) → s < R.N (i + 1) + cOf R (i + 1) → Loc.atN (hbar (Loc.eN _ (R.N (i + 1) + cOf R (i + 1)) s)) l = if l < R.N (i + 1) ∧ s < R.N (i + 1) then redP P.1 (Loc.atN (κ' (Loc.eN X.E (R.N (i + 1)) s)) l) else if l = s then 1 else 0`.

Introduce `l s hl hs`. Rewrite using `[(hred₀ l s hl hs).2]`. Conclude with `clT_extEnt κ' hl hs`. Establish `hent' : ∀ l s, l < R.N (i + 1) + cOf R (i + 1) → s < R.N (i + 1) + cOf R (i + 1) → Loc.atN (hbar.symm (Loc.eN _ (R.N (i + 1) + cOf R (i + 1)) s)) l = if l < R.N (i + 1) ∧ s < R.N (i + 1) then redP P.1 (Loc.atN (κ'.symm (Loc.eN X.E (R.N (i + 1)) s)) l) else if l = s then 1 else 0`. Introduce `l s hl hs`.

Rewrite using `[ocbT_red_symm hq0 hh₀ hred₀ hl hs, hh₀def, clL_ext_symm]`. Conclude with `clT_extEnt κ'.symm hl hs`. Take `⟨hfix, hvec, hact⟩` from `clX_fix_of_ent hbar _ hent`. Take `⟨hfix', hvec', -⟩` from `clX_fix_of_ent hbar.symm _ hent'`. Establish `hR1 : hbar ∈ Loc.R1 (𝓞 X.E ⧸ P.1.asIdeal) (R.N (i + 1)) (cOf R (i + 1))` using `⟨clX_R1cond hbar hfix hvec, clX_R1cond hbar.symm hfix' hvec'⟩`.

Establish `hn1 : Loc.n1Arg hbar = 0`. Unfold `Loc.n1Arg`. Use `Finset.sum_eq_zero fun j hj => ?_` and prove the remaining obligations. Establish `hj'` using `Finset.mem_range.1 hj`. Rewrite using `[hvec _ (by omega), ocbS_atN_of_lt _ (by omega)]`.

Simplify using `only [Loc.eN]`. Conclude with `if_neg (by simp)`. Establish `hgent : ∀ (l m : Fin (R.N (i + 1))), gbar (Pi.single m 1) l = redP P.1 (Loc.atN (κ' (Loc.eN X.E (R.N (i + 1)) m.1)) l.1)`. Introduce `l m`. Establish `h1` using `(hgred l.1 m.1 l.2 m.2).2`.

Establish `e1 : LocE.scE (R.N (i + 1)) (fun i => i + 1) m.1 = 0` using `by unfold LocE.scE; rw [if_pos m.2]`. Establish `e2 : LocE.scE (R.N (i + 1)) (fun i => i + 1) l.1 = 0` using `by unfold LocE.scE; rw [if_pos l.2]`. Rewrite `h1` using `[e1, e2, sub_zero, zpow_zero, mul_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ocbS_eN_single (show m.1 < R.N (i + 1) + 0 from m.2), ocbS_atN_of_lt _ (show l.1 < R.N (i + 1) + 0 from l.2)]`.

Both sides reduce to the same expression. Use `_ = _ := h1`. Establish `hg : ∀ x, hbar (Loc.inX _ (R.N (i + 1)) (cOf R (i + 1)) x) = Loc.inX _ (R.N (i + 1)) (cOf R (i + 1)) (gbar x)`. Introduce `x`. Use function extensionality and compare the values at `m`.

Distinguish the cases in `hm : m.1 < R.N (i + 1)`. Take `⟨l', rfl⟩ : ∃ l' : Fin (R.N (i + 1)), m = Fin.castAdd (cOf R (i + 1)) l'` from `⟨⟨m.1, hm⟩, Fin.ext rfl⟩`. Rewrite using `[hact, clT_inX_apply, dif_pos (by simp), residue_linearEquiv_apply_eq_sum gbar x]`. Use `Finset.sum_congr rfl fun m' _ => ?_` and prove the remaining obligations. Rewrite using `[clT_inX_apply, dif_pos (by simp), hgent]`.

Both sides reduce to the same expression. Take `⟨j, rfl⟩ : ∃ j : Fin (cOf R (i + 1)), m = Fin.natAdd (R.N (i + 1)) j` from `⟨⟨m.1 - R.N (i + 1), by omega⟩, Fin.ext (by simp; omega)⟩`. Rewrite using `[hfix, clT_inX_apply, clT_inX_apply, dif_neg (by simp), dif_neg (by simp)]`. Rewrite using `[hPhi, ← clL_ext_symm]`. Establish `hgl : ∀ v ∈ stdAt X.E (R.N (i + 1)) P.1, κ'.symm v ∈ stdAt X.E (R.N (i + 1)) P.1` using `fun v hv => (hκ' (κ'.symm v)).1 (by rw [LinearEquiv.apply_symm_apply]; exact hv)`.

Distinguish the cases in `hx : ocbXInt P.1 w`. Establish `hxI' : ocbXInt P.1 (κ'.symm.toLinearMap ∘ₗ w)`. Introduce `l s hl hs`. Establish `hv` using `clT_vec_std (P := P.1) (fun l' hl' => hx l' s hl' hs)`. Establish `h2` using `hgl _ hv`.

Rewrite `h2` using `[ciMem_stdAt]`. Rewrite using `[LinearMap.comp_apply, ocbS_atN_of_lt _ hl]`. Conclude with `h2 _`. Set `xbar : (Fin (R.N i) → 𝓞 X.E ⧸ P.1.asIdeal) →ₗ[𝓞 X.E ⧸ P.1.asIdeal] (Fin (R.N (i + 1)) → 𝓞 X.E ⧸ P.1.asIdeal)` to `Matrix.toLin' (Matrix.of fun l s => redP P.1 (Loc.atN (w (Loc.eN X.E (R.N i) s.1)) l.1))`. Establish `hxR : ocbXRed P.1 w xbar`.

Introduce `l s hl hs`. Use `show Loc.atN (Matrix.toLin' _ (Loc.eN _ (R.N i) s)) l = _`. Rewrite using `[ocbS_atN_toLin' _ hl hs]`. Both sides reduce to the same expression. Establish `hIκ : ∀ l m, l < R.N (i + 1) → m < R.N (i + 1) → IntAt P.1 (Loc.atN (κ'.symm.toLinearMap (Loc.eN X.E (R.N (i + 1)) m)) l)`.

Introduce `l m hl hm`. Establish `hv : Loc.eN X.E (R.N (i + 1)) m ∈ stdAt X.E (R.N (i + 1)) P.1`. Rewrite using `[ocbS_eN_single hm]`. Conclude with `ciSingle_mem _`. Establish `h2` using `hgl _ hv`.

Rewrite `h2` using `[ciMem_stdAt]`. Rewrite using `[ocbS_atN_of_lt _ hl]`. Conclude with `h2 _`. Establish `hxR' : ocbXRed P.1 (κ'.symm.toLinearMap ∘ₗ w) (gbar.symm.toLinearMap ∘ₗ xbar)`. Introduce `l s hl hs`.

Rewrite using `[ocbS_atN_comp _ _ hl hs, ocbS_atN_comp _ _ hl hs, redP_sum _ _ fun m _ => (hIκ l m.1 hl m.2).mul (hx m.1 s m.2 hs)]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[reduction_mul (hIκ l m.1 hl m.2) (hx m.1 s m.2 hs), ← hxR m.1 s m.2 hs]`. Use `congr 1`. Establish `h3` using `ocbT_red_symm (n := R.N (i + 1)) (c := 0) hq0 (clT_stab0 (q := qOf P.1) hκ') hgred hl m.2`.

Rewrite `h3` using `[clT_bEnt0 _ _ hl m.2]`. Conclude with `h3`. Apply `σ.injective` to reduce the goal to its premises. Rewrite using `[firstUnfolding_reduction_eq hq hu hp hcard hc' σ Φ Φr hsupp0 hred0 (cst.psi P) (fun u => ocbPsiC Ch σ P.1 u) (fun a ha => by rw [hB.psi0 P a hP ha]; rfl) hA hB.cst_ok.B_pos _ _ hxI' hxR', firstUnfolding_reduction_eq hq hu hp hcard hc' σ _ (fun x => Φr (hbar.symm.toLinearMap ∘ₗ x …`. Establish `hres : Loc.E1 (k` using `𝓞 X.E ⧸ P.1.asIdeal) (n' := R.N i) (c' := cOf R (i + 1) + 1) (n := R.N (i + 1)) (c := cOf R (i + 1)) (fun u => ocbPsiC Ch σ P.1 u) (@Finset.univ _ (resFintype P.1)) 1 Φr (gbar.symm.toLinearMap ∘ₗ xbar) = Loc.E1 (k := 𝓞 X.E ⧸ P.1.asIdeal) (n' := R.N i) (c' := cOf R (i + 1) + 1) (n …`.

Use `letI := resFintype P.1`. Establish `h` using `unfolding_equivalence _ _ _ _ _ (fun u => ocbPsiC Ch σ P.1 u) (fun a b => AddChar.map_add_eq_mul _ a b) 1 Φr hbar gbar hR1 hg xbar`. Rewrite `h` using `[show PI.UnfoldEquiv.Loc.n1Arg hbar = 0 from hn1, neg_zero]`. Simplify using `only [AddChar.map_zero_eq_one, one_mul] at h`. Conclude with `h.symm`.

Rewrite using `[hres]`. Establish `hx' : ¬ ocbXInt P.1 (κ'.symm.toLinearMap ∘ₗ w)`. Introduce `h`. Apply `hx` to reduce the goal to its premises. Introduce `l s hl hs`.

Establish `hv` using `clT_vec_std (P := P.1) (fun l' hl' => by`. Use `h l' s hl' hs` as an intermediate fact. Rewrite using `[LinearMap.comp_apply] at this)` and apply the resulting hypothesis. Establish `h2` using `(hκ' _).2 hv`. Rewrite `h2` using `[show κ' (κ'.symm.toLinearMap (w (Loc.eN X.E (R.N i) s))) = w (Loc.eN X.E (R.N i) s) from κ'.apply_symm_apply _, ciMem_stdAt]`.

Rewrite using `[ocbS_atN_of_lt _ hl]`. Conclude with `h2 _`. Rewrite using `[firstUnfolding_eq_zero_of_not_integral hc' Φ hsupp0 _ _ _ _ hx', firstUnfolding_eq_zero_of_not_integral hc' _ htsupp _ _ _ _ hx]`.
-/
theorem clT_xiTgtLaw (σ : X.K →+* ℂ) {m2 i : ℕ} (hB : OcbBase Ch sel mu cst m2) (hi : i < m2) (hA : cOf R (i + 1) + 1 ≤ cst.A) :
    XiTgtLaw Ch sel mu cst i := by
  intro P hP κ' hκ' hJ w
  classical
  have hq : ((qOf P.1 : ℕ) : 𝓞 X.E) ∈ P.1.asIdeal := ciQ_mem P.1
  have hu := ciQ_notMem_sq hB.hX hB.hPr hP
  have hp := ciQOf_prime hB.hPr hP
  have hcard := ciCard P.1
  have hq0 : (qOf P.1 : X.E) ≠ 0 := ciQ_ne_zero hu
  have hr := ocbRanks_step (R := R) hB.hm hi
  have hc' : cOf R i = cOf R (i + 1) + 1 := by
    unfold cOf
    have := hB.hm
    omega
  have hPhi : PhiAt Ch mu cst.sharp i P.1 = LocE.PhiGS (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) R.k (R.m / 2 - 1)
      (R.k + R.m - 1) R.t (i + 1) (cOf R i) (R.N i) (cOf R (i + 1)) (R.N (i + 1)) := by
    unfold PhiAt
    rw [if_pos hP, hB.sharp]
    rfl
  let Φ : Loc.SF X.E X.K (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1)) :=
    LocE.PhiGS (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) R.k (R.m / 2 - 1) (R.k + R.m - 1) R.t (i + 1) (cOf R i) (R.N i)
      (cOf R (i + 1)) (R.N (i + 1))
  let Φr := @ocbPhiS (𝓞 X.E ⧸ P.1.asIdeal) (resField P.1) (ocbPsiC Ch σ P.1) (ocbChiC Ch σ P.1) R.k R.m R.t (i + 1) (R.N i)
    (cOf R (i + 1)) (R.N (i + 1))
  have hsupp0 : ∀ y, Φ y ≠ 0 → ∀ l s, l < R.N (i + 1) + cOf R (i + 1) → s < R.N i + cOf R i →
      IntAt P.1 (ocbBEnt (R.N i) (R.N (i + 1)) (qOf P.1) y l s) :=
    fun y hy => ocbPhiGS_supp (psi0P Ch P.1) (chiP Ch P.1) hr hc' y hy
  have hred0 : ∀ y ybar, (∀ l s, l < R.N (i + 1) + cOf R (i + 1) → s < R.N i + cOf R i →
      IntAt P.1 (ocbBEnt (R.N i) (R.N (i + 1)) (qOf P.1) y l s)) →
      (∀ l s, l < R.N (i + 1) + cOf R (i + 1) → s < R.N i + cOf R i →
        Loc.atN (ybar (Loc.eN _ _ s)) l = redP P.1 (ocbBEnt (R.N i) (R.N (i + 1)) (qOf P.1) y l s)) → σ (Φ y) = Φr ybar :=
    fun y ybar hint hrd => ocbPhiGS_red hq hu σ (psi0P Ch P.1) (chiP Ch P.1) hr hc' y ybar hint hrd
  set h₀ := clL_ext (cOf R (i + 1)) κ' with hh₀def
  have hh₀ : h₀ ∈ stabL X.E (R.N (i + 1) + cOf R (i + 1))
      (LocE.lamY P.1 (qOf P.1) (R.N (i + 1)) (cOf R (i + 1)) fun i => i + 1) := (Subgroup.mem_inf.1 hJ).1
  obtain ⟨hbar, hred₀⟩ := ocbA_red_exists hq0 hh₀
  obtain ⟨htsupp, htred⟩ := ocbT_trans hq0 σ hc' hh₀ hred₀ Φ Φr hsupp0 hred0
  obtain ⟨gbar, hgred⟩ := ocbA_red_exists (n := R.N (i + 1)) (c := 0) hq0 (clT_stab0 (q := qOf P.1) hκ')

  have hent : ∀ l s, l < R.N (i + 1) + cOf R (i + 1) → s < R.N (i + 1) + cOf R (i + 1) →
      Loc.atN (hbar (Loc.eN _ (R.N (i + 1) + cOf R (i + 1)) s)) l =
        if l < R.N (i + 1) ∧ s < R.N (i + 1) then redP P.1 (Loc.atN (κ' (Loc.eN X.E (R.N (i + 1)) s)) l)
        else if l = s then 1 else 0 := by
    intro l s hl hs
    rw [(hred₀ l s hl hs).2]
    exact clT_extEnt κ' hl hs
  have hent' : ∀ l s, l < R.N (i + 1) + cOf R (i + 1) → s < R.N (i + 1) + cOf R (i + 1) →
      Loc.atN (hbar.symm (Loc.eN _ (R.N (i + 1) + cOf R (i + 1)) s)) l =
        if l < R.N (i + 1) ∧ s < R.N (i + 1) then redP P.1 (Loc.atN (κ'.symm (Loc.eN X.E (R.N (i + 1)) s)) l)
        else if l = s then 1 else 0 := by
    intro l s hl hs
    rw [ocbT_red_symm hq0 hh₀ hred₀ hl hs, hh₀def, clL_ext_symm]
    exact clT_extEnt κ'.symm hl hs
  obtain ⟨hfix, hvec, hact⟩ := clX_fix_of_ent hbar _ hent
  obtain ⟨hfix', hvec', -⟩ := clX_fix_of_ent hbar.symm _ hent'
  have hR1 : hbar ∈ Loc.R1 (𝓞 X.E ⧸ P.1.asIdeal) (R.N (i + 1)) (cOf R (i + 1)) :=
    ⟨clX_R1cond hbar hfix hvec, clX_R1cond hbar.symm hfix' hvec'⟩
  have hn1 : Loc.n1Arg hbar = 0 := by
    unfold Loc.n1Arg
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    rw [hvec _ (by omega), ocbS_atN_of_lt _ (by omega)]
    simp only [Loc.eN]
    exact if_neg (by simp)
  have hgent : ∀ (l m : Fin (R.N (i + 1))), gbar (Pi.single m 1) l = redP P.1 (Loc.atN (κ' (Loc.eN X.E (R.N (i + 1)) m.1)) l.1) := by
    intro l m
    have h1 := (hgred l.1 m.1 l.2 m.2).2
    have e1 : LocE.scE (R.N (i + 1)) (fun i => i + 1) m.1 = 0 := by unfold LocE.scE; rw [if_pos m.2]
    have e2 : LocE.scE (R.N (i + 1)) (fun i => i + 1) l.1 = 0 := by unfold LocE.scE; rw [if_pos l.2]
    rw [e1, e2, sub_zero, zpow_zero, mul_one] at h1
    calc gbar (Pi.single m 1) l = Loc.atN (gbar (Loc.eN _ (R.N (i + 1) + 0) m.1)) l.1 := by
          rw [ocbS_eN_single (show m.1 < R.N (i + 1) + 0 from m.2), ocbS_atN_of_lt _ (show l.1 < R.N (i + 1) + 0 from l.2)]
          rfl
      _ = _ := h1
  have hg : ∀ x, hbar (Loc.inX _ (R.N (i + 1)) (cOf R (i + 1)) x) = Loc.inX _ (R.N (i + 1)) (cOf R (i + 1)) (gbar x) := by
    intro x
    funext m
    by_cases hm : m.1 < R.N (i + 1)
    · obtain ⟨l', rfl⟩ : ∃ l' : Fin (R.N (i + 1)), m = Fin.castAdd (cOf R (i + 1)) l' := ⟨⟨m.1, hm⟩, Fin.ext rfl⟩
      rw [hact, clT_inX_apply, dif_pos (by simp), residue_linearEquiv_apply_eq_sum gbar x]
      refine Finset.sum_congr rfl fun m' _ => ?_
      rw [clT_inX_apply, dif_pos (by simp), hgent]
      rfl
    · obtain ⟨j, rfl⟩ : ∃ j : Fin (cOf R (i + 1)), m = Fin.natAdd (R.N (i + 1)) j :=
        ⟨⟨m.1 - R.N (i + 1), by omega⟩, Fin.ext (by simp; omega)⟩
      rw [hfix, clT_inX_apply, clT_inX_apply, dif_neg (by simp), dif_neg (by simp)]

  rw [hPhi, ← clL_ext_symm]
  have hgl : ∀ v ∈ stdAt X.E (R.N (i + 1)) P.1, κ'.symm v ∈ stdAt X.E (R.N (i + 1)) P.1 :=
    fun v hv => (hκ' (κ'.symm v)).1 (by rw [LinearEquiv.apply_symm_apply]; exact hv)
  by_cases hx : ocbXInt P.1 w
  · have hxI' : ocbXInt P.1 (κ'.symm.toLinearMap ∘ₗ w) := by
      intro l s hl hs
      have hv := clT_vec_std (P := P.1) (fun l' hl' => hx l' s hl' hs)
      have h2 := hgl _ hv
      rw [ciMem_stdAt] at h2
      rw [LinearMap.comp_apply, ocbS_atN_of_lt _ hl]
      exact h2 _
    let xbar : (Fin (R.N i) → 𝓞 X.E ⧸ P.1.asIdeal) →ₗ[𝓞 X.E ⧸ P.1.asIdeal] (Fin (R.N (i + 1)) → 𝓞 X.E ⧸ P.1.asIdeal) :=
      Matrix.toLin' (Matrix.of fun l s => redP P.1 (Loc.atN (w (Loc.eN X.E (R.N i) s.1)) l.1))
    have hxR : ocbXRed P.1 w xbar := by
      intro l s hl hs
      show Loc.atN (Matrix.toLin' _ (Loc.eN _ (R.N i) s)) l = _
      rw [ocbS_atN_toLin' _ hl hs]
      rfl
    have hIκ : ∀ l m, l < R.N (i + 1) → m < R.N (i + 1) →
        IntAt P.1 (Loc.atN (κ'.symm.toLinearMap (Loc.eN X.E (R.N (i + 1)) m)) l) := by
      intro l m hl hm
      have hv : Loc.eN X.E (R.N (i + 1)) m ∈ stdAt X.E (R.N (i + 1)) P.1 := by
        rw [ocbS_eN_single hm]
        exact ciSingle_mem _
      have h2 := hgl _ hv
      rw [ciMem_stdAt] at h2
      rw [ocbS_atN_of_lt _ hl]
      exact h2 _
    have hxR' : ocbXRed P.1 (κ'.symm.toLinearMap ∘ₗ w) (gbar.symm.toLinearMap ∘ₗ xbar) := by
      intro l s hl hs
      rw [ocbS_atN_comp _ _ hl hs, ocbS_atN_comp _ _ hl hs,
        redP_sum _ _ fun m _ => (hIκ l m.1 hl m.2).mul (hx m.1 s m.2 hs)]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [reduction_mul (hIκ l m.1 hl m.2) (hx m.1 s m.2 hs), ← hxR m.1 s m.2 hs]
      congr 1
      have h3 := ocbT_red_symm (n := R.N (i + 1)) (c := 0) hq0 (clT_stab0 (q := qOf P.1) hκ') hgred hl m.2
      rw [clT_bEnt0 _ _ hl m.2] at h3
      exact h3
    apply σ.injective
    rw [firstUnfolding_reduction_eq hq hu hp hcard hc' σ Φ Φr hsupp0 hred0 (cst.psi P) (fun u => ocbPsiC Ch σ P.1 u)
        (fun a ha => by rw [hB.psi0 P a hP ha]; rfl) hA hB.cst_ok.B_pos _ _ hxI' hxR',
      firstUnfolding_reduction_eq hq hu hp hcard hc' σ _ (fun x => Φr (hbar.symm.toLinearMap ∘ₗ x)) htsupp htred (cst.psi P)
        (fun u => ocbPsiC Ch σ P.1 u) (fun a ha => by rw [hB.psi0 P a hP ha]; rfl) hA hB.cst_ok.B_pos w xbar hx hxR]
    have hres : Loc.E1 (k := 𝓞 X.E ⧸ P.1.asIdeal) (n' := R.N i) (c' := cOf R (i + 1) + 1) (n := R.N (i + 1)) (c := cOf R (i + 1))
        (fun u => ocbPsiC Ch σ P.1 u) (@Finset.univ _ (resFintype P.1)) 1 Φr (gbar.symm.toLinearMap ∘ₗ xbar) =
        Loc.E1 (k := 𝓞 X.E ⧸ P.1.asIdeal) (n' := R.N i) (c' := cOf R (i + 1) + 1) (n := R.N (i + 1)) (c := cOf R (i + 1))
          (fun u => ocbPsiC Ch σ P.1 u) (@Finset.univ _ (resFintype P.1)) 1 (fun x => Φr (hbar.symm.toLinearMap ∘ₗ x)) xbar := by
      letI := resFintype P.1
      have h := unfolding_equivalence _ _ _ _ _ (fun u => ocbPsiC Ch σ P.1 u) (fun a b => AddChar.map_add_eq_mul _ a b) 1 Φr hbar gbar hR1 hg xbar
      rw [show PI.UnfoldEquiv.Loc.n1Arg hbar = 0 from hn1, neg_zero] at h
      simp only [AddChar.map_zero_eq_one, one_mul] at h
      exact h.symm
    rw [hres]
  · have hx' : ¬ ocbXInt P.1 (κ'.symm.toLinearMap ∘ₗ w) := by
      intro h
      apply hx
      intro l s hl hs
      have hv := clT_vec_std (P := P.1) (fun l' hl' => by
        have := h l' s hl' hs
        rwa [LinearMap.comp_apply] at this)
      have h2 := (hκ' _).2 hv
      rw [show κ' (κ'.symm.toLinearMap (w (Loc.eN X.E (R.N i) s))) = w (Loc.eN X.E (R.N i) s) from κ'.apply_symm_apply _,
        ciMem_stdAt] at h2
      rw [ocbS_atN_of_lt _ hl]
      exact h2 _
    rw [firstUnfolding_eq_zero_of_not_integral hc' Φ hsupp0 _ _ _ _ hx', firstUnfolding_eq_zero_of_not_integral hc' _ htsupp _ _ _ _ hx]

end Tgt

end Formalism.L2.Col
