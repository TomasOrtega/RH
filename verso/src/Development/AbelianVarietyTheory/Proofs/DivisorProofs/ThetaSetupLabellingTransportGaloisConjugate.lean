import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalLab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeIsoOfTwoPadicAlgClUniformisationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointTransferThroughCommonGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedPointOverLabelPowRNEqOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UTorsClosed
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.DeltaIsGreatest

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.GalTrans

section Cong
variable {X : Type} [AddCommGroup X]

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, by simp⟩`.
-/
theorem cm_refl (N : ℕ) (x : X) : CongMod N x x := ⟨0, by simp⟩

/- English proof (translation)
Take `⟨w, hw⟩` from `h`. Conclude with `⟨-w, by rw [hw, smul_neg]; abel⟩`.
-/
theorem cm_symm {N : ℕ} {x y : X} (h : CongMod N x y) : CongMod N y x := by
  obtain ⟨w, hw⟩ := h
  exact ⟨-w, by rw [hw, smul_neg]; abel⟩

/- English proof (translation)
Take `⟨w, hw⟩` from `h`. Take `⟨w', hw'⟩` from `h'`. Conclude with `⟨w' + w, by rw [hw, hw', smul_add]; abel⟩`.
-/
theorem cm_trans {N : ℕ} {x y z : X} (h : CongMod N x y) (h' : CongMod N y z) : CongMod N x z := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨w', hw'⟩ := h'
  exact ⟨w' + w, by rw [hw, hw', smul_add]; abel⟩

/- English proof (translation)
Take `⟨w, hw⟩` from `h`. Conclude with `⟨f w, by rw [hw, map_add, map_nsmul]⟩`.
-/
theorem cm_map {Y : Type} [AddCommGroup Y] (f : X →+ Y) {N : ℕ} {x y : X} (h : CongMod N x y) :
    CongMod N (f x) (f y) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨f w, by rw [hw, map_add, map_nsmul]⟩

/- English proof (translation)
Take `⟨w, hw⟩` from `QuotientAddGroup.eq.mp h`. Express the relevant statement in the definitionally equal form `N • w = -x + y at hw`. Use `⟨-w, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_neg, hw]`. Normalize the expressions using the abelian group laws.
-/
theorem cm_of_mk {N : ℕ} {x y : X}
    (h : (QuotientAddGroup.mk x : X ⧸ (nsmulAddMonoidHom N : X →+ X).range) = QuotientAddGroup.mk y) :
    CongMod N x y := by
  obtain ⟨w, hw⟩ := QuotientAddGroup.eq.mp h
  change N • w = -x + y at hw
  refine ⟨-w, ?_⟩
  rw [smul_neg, hw]
  abel

/- English proof (translation)
Take `⟨w, hw⟩` from `h`. Use `QuotientAddGroup.eq.mpr ⟨-w, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `N • (-w) = -x + y`. Rewrite using `[hw, smul_neg]`. Normalize the expressions using the abelian group laws.
-/
theorem cm_mk {N : ℕ} {x y : X} (h : CongMod N x y) :
    (QuotientAddGroup.mk x : X ⧸ (nsmulAddMonoidHom N : X →+ X).range) = QuotientAddGroup.mk y := by
  obtain ⟨w, hw⟩ := h
  refine QuotientAddGroup.eq.mpr ⟨-w, ?_⟩
  change N • (-w) = -x + y
  rw [hw, smul_neg]
  abel
/- English proof (translation)
The claim follows from `((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).charZero`.
-/
private theorem charZero_uTest_V {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}
    {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) : CharZero u.V :=
  ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).charZero

def matAct (E : Matrix (Fin 8) (Fin 8) ℤ) : (Fin 8 → X) →+ (Fin 8 → X) where
  toFun v a := ∑ b, E a b • v b
  map_zero' := by ext a; simp
  map_add' v w := by ext a; simp [smul_add, Finset.sum_add_distrib]

end Cong

open MonObj in

/- English proof (translation)
Take `⟨e, hps, hcg⟩` from `GlobalTheory.T.exists_latticeIso_of_two_padicAlgCl_uniformisations S S' ρ ρ' p y₀ y₁ u u' P₀ a a' ha ha' hL hL'`. Use `haveI := charZero_uTest_V u`. Use `haveI := charZero_uTest_V u'`. Use `⟨e, fun χ => ?_, fun m x x' w hm hx hx' hw hwa hwa' => ?_, fun m pk' x' hm hpk' => ?_⟩` and prove the remaining obligations. Establish `h1` using `(hps χ _).1 (l.q_eq χ)`.

Establish `h2` using `l'.q_eq (e χ)`. Establish `h3` using `Real.exp_injective (GlobalTheory.ZH.RealCase.psiNorm_unique u' (e χ) h2 h1)`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨f, hf1, hf2, -⟩` from `GlobalTheory.ZH.uTors_closed u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) m hm`. Take `⟨f', hf1', hf2', -⟩` from `GlobalTheory.ZH.uTors_closed u'.V u'.complete u'.A u'.G u'.D u'.U (PadicAlgCl p) m hm`.

Take `⟨pk, rfl⟩` from `hf2 x hx`. Take `⟨pk', rfl⟩` from `hf2' x' hx'`. Establish `q1` using `(hf1 pk (f pk)).2 rfl`. Establish `q2` using `(hf1' pk' (f' pk')).2 rfl`. Conclude with `⟨pk, pk', q1, q2, hcg m pk pk' _ _ w hm q1 q2 hw hwa hwa'⟩`.

Establish `hx' : x' ^ m = 1`. Establish `h0` using `hpk'`. Unfold `QkToAkU at h0`. Take `⟨w0, hw0⟩` from `u'.U.ext`. Establish `h1` using `h0 w0 hw0`.

Unfold `QkToAk at h1`. Conclude with `h1.1`. Take `⟨w, x, hw, hwa', hwa, hx⟩` from `GlobalTheory.PtTrans.ptTrans (PadicAlgCl p) u'.A u.A P₀ a' a ha' ha m x' hx'`. Take `⟨f, hf1, hf2, -⟩` from `GlobalTheory.ZH.uTors_closed u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) m hm`. Take `⟨pk, rfl⟩` from `hf2 x hx`.

Establish `q1` using `(hf1 pk (f pk)).2 rfl`. Conclude with `⟨pk, f pk, w, q1, hx, hw, hwa, hwa', hcg m pk pk' _ _ w hm q1 hpk' hw hwa hwa'⟩`.
-/
theorem compare {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω']
    {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} {ρ : S.Real} {ρ' : S'.Real} {p : ℕ} [Fact p.Prime]
    {y₀ : S.R →+* PadicAlgCl p} {y₁ : S'.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) (u' : ρ'.UTest p y₁) (l : u.Lab)
    (l' : u'.Lab) (P₀ : PolAV (Sp (PadicAlgCl p))) (a : P₀.A.left ⟶ u.A.A.left) (a' : P₀.A.left ⟶ u'.A.A.left)
    (ha : IsGrpPullback P₀.A u.A.A (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p))) a)
    (ha' : IsGrpPullback P₀.A u'.A.A (spMap (algebraMap (FractionRing u'.V) (PadicAlgCl p))) a')
    (hL : LBIso P₀.L (u.A.L.pull a)) (hL' : LBIso P₀.L (u'.A.L.pull a')) :
    ∃ e : u.D.toPre.X ≃+ u'.D.toPre.X, (∀ χ, l'.q (e χ) = l.q χ) ∧
      (∀ (m : ℕ) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (x' : TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A)
        (w : Sp (PadicAlgCl p) ⟶ P₀.A.left), 1 ≤ m → x ^ m = 1 → x' ^ m = 1 → w ≫ P₀.A.hom = 𝟙 _ → w ≫ a = x.left →
        w ≫ a' = x'.left → ∃ pk pk', QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x ∧
          QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk' x' ∧ CongMod m pk'.y (e pk.y)) ∧
      ∀ (m : ℕ) (pk' : QkPt u'.D.toPre (PadicAlgCl p) m) (x' : TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A), 1 ≤ m →
        QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk' x' → ∃ (pk : QkPt u.D.toPre (PadicAlgCl p) m)
          (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (w : Sp (PadicAlgCl p) ⟶ P₀.A.left),
          QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x ∧ x ^ m = 1 ∧ w ≫ P₀.A.hom = 𝟙 _ ∧ w ≫ a = x.left ∧
          w ≫ a' = x'.left ∧ CongMod m pk'.y (e pk.y) := by
  obtain ⟨e, hps, hcg⟩ := GlobalTheory.T.exists_latticeIso_of_two_padicAlgCl_uniformisations S S' ρ ρ' p y₀ y₁ u u' P₀ a a' ha ha' hL hL'
  haveI := charZero_uTest_V u
  haveI := charZero_uTest_V u'
  refine ⟨e, fun χ => ?_, fun m x x' w hm hx hx' hw hwa hwa' => ?_, fun m pk' x' hm hpk' => ?_⟩
  · have h1 := (hps χ _).1 (l.q_eq χ)
    have h2 := l'.q_eq (e χ)
    have h3 := Real.exp_injective (GlobalTheory.ZH.RealCase.psiNorm_unique u' (e χ) h2 h1)
    linarith
  · obtain ⟨f, hf1, hf2, -⟩ := GlobalTheory.ZH.uTors_closed u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) m hm
    obtain ⟨f', hf1', hf2', -⟩ := GlobalTheory.ZH.uTors_closed u'.V u'.complete u'.A u'.G u'.D u'.U (PadicAlgCl p) m hm
    obtain ⟨pk, rfl⟩ := hf2 x hx
    obtain ⟨pk', rfl⟩ := hf2' x' hx'
    have q1 := (hf1 pk (f pk)).2 rfl
    have q2 := (hf1' pk' (f' pk')).2 rfl
    exact ⟨pk, pk', q1, q2, hcg m pk pk' _ _ w hm q1 q2 hw hwa hwa'⟩
  · have hx' : x' ^ m = 1 := by
      have h0 := hpk'
      unfold QkToAkU at h0
      obtain ⟨w0, hw0⟩ := u'.U.ext
      have h1 := h0 w0 hw0
      unfold QkToAk at h1
      exact h1.1
    obtain ⟨w, x, hw, hwa', hwa, hx⟩ :=
      GlobalTheory.PtTrans.ptTrans (PadicAlgCl p) u'.A u.A P₀ a' a ha' ha m x' hx'
    obtain ⟨f, hf1, hf2, -⟩ := GlobalTheory.ZH.uTors_closed u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) m hm
    obtain ⟨pk, rfl⟩ := hf2 x hx
    have q1 := (hf1 pk (f pk)).2 rfl
    exact ⟨pk, f pk, w, q1, hx, hw, hwa, hwa', hcg m pk pk' _ _ w hm q1 hpk' hw hwa hwa'⟩
set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `g n F W Z i X₁ hg hn hodd hi hE8 hth hpr ε₁ hdiag D σ s hs a hga p _ z₁ c y h h' yy hlab`. Take `⟨c₀, hc, R', fg, frac, hth', hev, ρ', ε', hsame', hi₀', hR', y₀, hy₀, u, l, j, hq, hlabl, hmat⟩` from `hlab`. Take `⟨yy₂, hlab₂⟩` from `exists_isLab g n F W Z i D.X hg hn hodd hi hE8 hth D.proj D.ε D.diag p ((y ≫ s) (cPt p)) (D.lift c (y ≫ s) h')`. Take `⟨c₂, hc₂, R₂, fg₂, frac₂, hth₂, hev₂, ρ₂, ε₂, hsame₂, hi₀₂, hR₂, y₁, hy₁, u₂, l₂, j₂, hq₂, -, -⟩` from `hlab₂`. Take `⟨P₀, b, t, ε₀, hb, ht, lb, lt, hε, hp⟩` from `hga`.

Take `⟨Q, b', b'', hb', hb'', lb', lb'', hpts, hend⟩` from `exists_generic D.X.ρ D.ε ρ' ε' ρ₂ ε₂ (fun x => x) (fun x => x) hsame' hsame₂ (σ : D.X.Ω₁ →+* D.X.Ω₁) a P₀ b t ε₀ hb ht lb lt hε hp`. Use `haveI : IsDedekindDomain D.X.o₁ := ArithBase.ded (Ω := D.X.Ω₁)`. Establish `hR₂' : R₂ ≤ D.X.M.O (((gPt p ≫ y) ≫ s) (closedPoint (PadicAlgCl p)))`. Rewrite using `[Category.assoc]`. Conclude with `hR₂`.

Establish `hy₁' : ∀ r : R₂, y₁ r = D.X.M.val ((gPt p ≫ y) ≫ s) r`. Introduce `r`. Rewrite using `[Category.assoc]`. Conclude with `hy₁ r`. Establish `hM : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme D.X.M.Z`.

Establish `hn` using `D.X.normal`. Unfold `ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme`. Take `⟨h1, h2⟩` from `hn`. Conclude with `fun x => ⟨h1 x, h2 x⟩`. Take `⟨P₁, a₁, a₂, ha₁, ha₂, la₁, la₂, hpt, hen⟩` from `spread D.X.M hM ρ' ρ₂ (σ : D.X.Ω₁ →+* D.X.Ω₁) s hs (gPt p ≫ y) hR' hR₂' y₀ y₁ hy₀ hy₁' u u₂ Q hb' hb'' lb' lb''`.

Take `⟨e, heq, hfw, hbk⟩` from `compare u u₂ l l₂ P₁ a₁ a₂ ha₁ ha₂ la₁ la₂`. Establish `hN : 1 ≤ D.X.S.r * D.X.S.N`. Take `⟨jj, -, hr⟩` from `D.X.ρ.r_eq`. Rewrite using `[hr, D.X.ρ.N_eq]`. Establish `hnp` using `D.X.ρ.n_prime.pos`.

Conclude with `Nat.mul_pos (pow_pos hnp _) (pow_pos (pow_pos hnp _) _)`. Use `⟨c₂, hc₂, R₂, fg₂, frac₂, hth₂, hev₂, ρ₂, ε₂, hsame₂, hi₀₂, hR₂, y₁, hy₁, u₂, l₂, e.symm.trans j, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `χ`. Establish `h1` using `heq (e.symm χ)`. Rewrite `h1` using `[AddEquiv.apply_symm_apply]`.

Rewrite using `[h1]`. Conclude with `hq (e.symm χ)`. Introduce `bb χ hb2`. Take `⟨wg, hwg, hwg1, hwg2⟩` from `hpts bb`. Take `⟨w1, x1, x2, hw1, hw1a, hw1b, hx1, hx2⟩` from `hpt (a bb) bb wg hwg hwg1 hwg2`.

Establish `hx1p` using `GlobalTheory.LabelTorsion.pow_eq_one_of_over_label _ ρ' p y₀ u (a bb) x1 hx1`. Establish `hx2p` using `GlobalTheory.LabelTorsion.pow_eq_one_of_over_label _ ρ₂ p y₁ u₂ bb x2 hx2`. Take `⟨pk, pk2, hq1, hq2, hc12⟩` from `hfw (D.X.S.r * D.X.S.N) x1 x2 w1 hN hx1p hx2p hw1 hw1a hw1b`. Establish `e1` using `l.yy_eq (a bb) pk x1 hq1 hx1`. Establish `e2` using `l₂.yy_eq bb pk2 x2 hq2 hx2`.

Establish `c1 : CongMod (D.X.S.r * D.X.S.N) χ pk2.y` using `cm_of_mk (hb2.symm.trans e2)`. Establish `c2` using `cm_trans c1 hc12`. Establish `c3 : CongMod (D.X.S.r * D.X.S.N) (e.symm χ) pk.y`. Establish `c4` using `cm_map e.symm.toAddMonoidHom c2`. Simplify using `using c4`.

Establish `e3 : l.yy (a bb) = QuotientAddGroup.mk (e.symm χ)` using `e1.trans (cm_mk (cm_symm c3))`. Conclude with `hlabl (a bb) (e.symm χ) e3`. Introduce `m pk pk' x x' E hm hq hq' hxx`. Take `⟨pk0, x0, w0, hq0, hx0, hw0, hw0a, hw0b, hc0⟩` from `hbk m pk x hm hq`. Take `⟨pk0', x0', w0', hq0', hx0', hw0', hw0a', hw0b', hc0'⟩` from `hbk m pk' x' hm hq'`.

Take `⟨η, hη1, hη2⟩` from `hend E`. Establish `hyp : w0' ≫ a₂ ≫ u₂.φ = w0 ≫ a₂ ≫ u₂.φ ≫ (ε₂ E).left`. Rewrite `hxx` using `[← hw0b', ← hw0b]`. Simplify `hxx` using `only [Category.assoc]`. Establish `key : x0'.left ≫ u.φ = x0.left ≫ u.φ ≫ (ε' E).left`.

Establish `k1` using `hen (ε' E) (ε₂ E) η hη1 hη2 w0 w0' hw0 hw0' hyp`. Rewrite using `[← hw0a', ← hw0a]`. Simplify `k1` using `only [Category.assoc]`. Establish `hm0` using `hmat m pk0 pk0' x0 x0' E hm hq0 hq0' key`. Establish `A : CongMod m (j (e.symm pk'.y)) (j pk0'.y)`.

Establish `A1` using `cm_map (e.symm.trans j).toAddMonoidHom hc0'`. Simplify using `using A1`. Establish `B : CongMod m (j (e.symm pk.y)) (j pk0.y)`. Establish `B1` using `cm_map (e.symm.trans j).toAddMonoidHom hc0`. Simplify using `using B1`.

Establish `B2` using `cm_map (matAct E) B`. Conclude with `cm_trans A (cm_trans hm0 (cm_symm B2))`.
-/
theorem isLab_conj : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁), ∀ (s : D.X.M.Z ⟶ D.X.M.Z), D.X.M.pt ≫ s = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ D.X.M.pt → ∀ a : D.X.S.Gam ≃+ D.X.S.Gam, D.GalLab σ a → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y) (h' : (y ≫ s) ≫ D.q = c.y) (yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab D.X D.ε (D.lift c y h) yy → IsLab D.X D.ε (D.lift c (y ≫ s) h') (yy.comp a.toAddMonoidHom) := by
  intro g n F W Z i X₁ hg hn hodd hi hE8 hth hpr ε₁ hdiag D σ s hs a hga p _ z₁ c y h h' yy hlab
  obtain ⟨c₀, hc, R', fg, frac, hth', hev, ρ', ε', hsame', hi₀', hR', y₀, hy₀, u, l, j, hq, hlabl, hmat⟩ := hlab
  obtain ⟨yy₂, hlab₂⟩ := exists_isLab g n F W Z i D.X hg hn hodd hi hE8 hth D.proj D.ε D.diag p
    ((y ≫ s) (cPt p)) (D.lift c (y ≫ s) h')
  obtain ⟨c₂, hc₂, R₂, fg₂, frac₂, hth₂, hev₂, ρ₂, ε₂, hsame₂, hi₀₂, hR₂, y₁, hy₁, u₂, l₂, j₂, hq₂, -, -⟩ := hlab₂
  obtain ⟨P₀, b, t, ε₀, hb, ht, lb, lt, hε, hp⟩ := hga
  obtain ⟨Q, b', b'', hb', hb'', lb', lb'', hpts, hend⟩ :=
    exists_generic D.X.ρ D.ε ρ' ε' ρ₂ ε₂ (fun x => x) (fun x => x) hsame' hsame₂ (σ : D.X.Ω₁ →+* D.X.Ω₁) a P₀ b t ε₀
      hb ht lb lt hε hp
  haveI : IsDedekindDomain D.X.o₁ := ArithBase.ded (Ω := D.X.Ω₁)
  have hR₂' : R₂ ≤ D.X.M.O (((gPt p ≫ y) ≫ s) (closedPoint (PadicAlgCl p))) := by
    rw [Category.assoc]; exact hR₂
  have hy₁' : ∀ r : R₂, y₁ r = D.X.M.val ((gPt p ≫ y) ≫ s) r := by
    intro r; rw [Category.assoc]; exact hy₁ r
  have hM : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme D.X.M.Z := by
    have hn := D.X.normal
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme
    obtain ⟨h1, h2⟩ := hn
    exact fun x => ⟨h1 x, h2 x⟩
  obtain ⟨P₁, a₁, a₂, ha₁, ha₂, la₁, la₂, hpt, hen⟩ :=
    spread D.X.M hM ρ' ρ₂ (σ : D.X.Ω₁ →+* D.X.Ω₁) s hs (gPt p ≫ y) hR' hR₂' y₀ y₁ hy₀ hy₁' u u₂ Q hb' hb''
      lb' lb''
  obtain ⟨e, heq, hfw, hbk⟩ := compare u u₂ l l₂ P₁ a₁ a₂ ha₁ ha₂ la₁ la₂
  have hN : 1 ≤ D.X.S.r * D.X.S.N := by
    obtain ⟨jj, -, hr⟩ := D.X.ρ.r_eq
    rw [hr, D.X.ρ.N_eq]
    have hnp := D.X.ρ.n_prime.pos
    exact Nat.mul_pos (pow_pos hnp _) (pow_pos (pow_pos hnp _) _)
  refine ⟨c₂, hc₂, R₂, fg₂, frac₂, hth₂, hev₂, ρ₂, ε₂, hsame₂, hi₀₂, hR₂, y₁, hy₁, u₂, l₂, e.symm.trans j, ?_, ?_, ?_⟩
  · intro χ
    have h1 := heq (e.symm χ)
    rw [AddEquiv.apply_symm_apply] at h1
    rw [h1]
    exact hq (e.symm χ)
  · intro bb χ hb2
    obtain ⟨wg, hwg, hwg1, hwg2⟩ := hpts bb
    obtain ⟨w1, x1, x2, hw1, hw1a, hw1b, hx1, hx2⟩ := hpt (a bb) bb wg hwg hwg1 hwg2
    have hx1p := GlobalTheory.LabelTorsion.pow_eq_one_of_over_label _ ρ' p y₀ u (a bb) x1 hx1
    have hx2p := GlobalTheory.LabelTorsion.pow_eq_one_of_over_label _ ρ₂ p y₁ u₂ bb x2 hx2
    obtain ⟨pk, pk2, hq1, hq2, hc12⟩ := hfw (D.X.S.r * D.X.S.N) x1 x2 w1 hN hx1p hx2p hw1 hw1a hw1b
    have e1 := l.yy_eq (a bb) pk x1 hq1 hx1
    have e2 := l₂.yy_eq bb pk2 x2 hq2 hx2
    have c1 : CongMod (D.X.S.r * D.X.S.N) χ pk2.y := cm_of_mk (hb2.symm.trans e2)
    have c2 := cm_trans c1 hc12
    have c3 : CongMod (D.X.S.r * D.X.S.N) (e.symm χ) pk.y := by
      have c4 := cm_map e.symm.toAddMonoidHom c2
      simpa using c4
    have e3 : l.yy (a bb) = QuotientAddGroup.mk (e.symm χ) := e1.trans (cm_mk (cm_symm c3))
    exact hlabl (a bb) (e.symm χ) e3
  · intro m pk pk' x x' E hm hq hq' hxx
    obtain ⟨pk0, x0, w0, hq0, hx0, hw0, hw0a, hw0b, hc0⟩ := hbk m pk x hm hq
    obtain ⟨pk0', x0', w0', hq0', hx0', hw0', hw0a', hw0b', hc0'⟩ := hbk m pk' x' hm hq'
    obtain ⟨η, hη1, hη2⟩ := hend E
    have hyp : w0' ≫ a₂ ≫ u₂.φ = w0 ≫ a₂ ≫ u₂.φ ≫ (ε₂ E).left := by
      rw [← hw0b', ← hw0b] at hxx
      simpa only [Category.assoc] using hxx
    have key : x0'.left ≫ u.φ = x0.left ≫ u.φ ≫ (ε' E).left := by
      have k1 := hen (ε' E) (ε₂ E) η hη1 hη2 w0 w0' hw0 hw0' hyp
      rw [← hw0a', ← hw0a]
      simpa only [Category.assoc] using k1
    have hm0 := hmat m pk0 pk0' x0 x0' E hm hq0 hq0' key
    have A : CongMod m (j (e.symm pk'.y)) (j pk0'.y) := by
      have A1 := cm_map (e.symm.trans j).toAddMonoidHom hc0'
      simpa using A1
    have B : CongMod m (j (e.symm pk.y)) (j pk0.y) := by
      have B1 := cm_map (e.symm.trans j).toAddMonoidHom hc0
      simpa using B1
    have B2 := cm_map (matAct E) B
    exact cm_trans A (cm_trans hm0 (cm_symm B2))

end GlobalTheory.Poinc.GalTrans
