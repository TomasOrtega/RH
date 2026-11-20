import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RechartingsThetaSetupSameGeometricFibreAtTraitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeIsoOfTwoPadicAlgClUniformisationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomRescaledRealisationSameGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointTransferThroughCommonGrpPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEndoImageTorsionPointUniformisedModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedPointOverLabelPowRNEqOneStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UTorsClosed
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsLatticePart
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.DeltaIsGreatest
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GeomCore

section Cong
variable {X : Type} [AddCommGroup X]

/- English proof (translation)
Take `⟨w, rfl⟩` from `h`. Conclude with `⟨-w, by rw [smul_neg]; abel⟩`.
-/
theorem cm_symm {N : ℕ} {x y : X} (h : CongMod N x y) : CongMod N y x := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨-w, by rw [smul_neg]; abel⟩

/- English proof (translation)
Take `⟨w, rfl⟩` from `h`. Take `⟨w', rfl⟩` from `h'`. Conclude with `⟨w' + w, by rw [smul_add]; abel⟩`.
-/
theorem cm_trans {N : ℕ} {x y z : X} (h : CongMod N x y) (h' : CongMod N y z) : CongMod N x z := by
  obtain ⟨w, rfl⟩ := h
  obtain ⟨w', rfl⟩ := h'
  exact ⟨w' + w, by rw [smul_add]; abel⟩

/- English proof (translation)
Take `⟨w, rfl⟩` from `h`. Conclude with `⟨f w, by rw [map_add, map_nsmul]⟩`.
-/
theorem cm_map {Y : Type} [AddCommGroup Y] (f : X →+ Y) {N : ℕ} {x y : X} (h : CongMod N x y) :
    CongMod N (f x) (f y) := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨f w, by rw [map_add, map_nsmul]⟩

/- English proof (translation)
Rewrite `h` using `[QuotientAddGroup.eq]`. Take `⟨w, hw⟩` from `h`. Establish `hw' : N • w = -x + y` using `hw`. Conclude with `⟨-w, by rw [smul_neg, hw']; abel⟩`.
-/
theorem cm_of_mk {N : ℕ} {x y : X}
    (h : (QuotientAddGroup.mk x : X ⧸ (nsmulAddMonoidHom N : X →+ X).range) = QuotientAddGroup.mk y) :
    CongMod N x y := by
  rw [QuotientAddGroup.eq] at h
  obtain ⟨w, hw⟩ := h
  have hw' : N • w = -x + y := hw
  exact ⟨-w, by rw [smul_neg, hw']; abel⟩

/- English proof (translation)
Rewrite using `[QuotientAddGroup.eq]`. Take `⟨w, rfl⟩` from `h`. Conclude with `⟨-w, by change N • (-w) = -(y + N • w) + y; rw [smul_neg]; abel⟩`.
-/
theorem cm_mk {N : ℕ} {x y : X} (h : CongMod N x y) :
    (QuotientAddGroup.mk x : X ⧸ (nsmulAddMonoidHom N : X →+ X).range) = QuotientAddGroup.mk y := by
  rw [QuotientAddGroup.eq]
  obtain ⟨w, rfl⟩ := h
  exact ⟨-w, by change N • (-w) = -(y + N • w) + y; rw [smul_neg]; abel⟩

def matAct (E : Matrix (Fin 8) (Fin 8) ℤ) : (Fin 8 → X) →+ (Fin 8 → X) where
  toFun v a := ∑ b, E a b • v b
  map_zero' := by ext a; simp
  map_add' v w := by ext a; simp [smul_add, Finset.sum_add_distrib]

end Cong

open MonObj in
/- English proof (translation)
Introduce `g n F W Z i X ε hd p _ z c yy yy' h1 h2`. Take `⟨c₀, hc, R', fg, frac, hth, hev, ρ', ε', hS, -, hR, y₀, hy₀, u, l, j, hq, hyy, hall⟩` from `h1`. Take `⟨c₁, hc₁, R'', fg₁, frac₁, hth₁, hev₁, ρ'', ε'', hS₁, -, hR₁, y₁, hy₁, u', l', j', hq', hyy', hall'⟩` from `h2`. Take `⟨P₀, a, a', ha, ha', hL, hL', hlab, hε⟩` from `GlobalTheory.T.rechartings_thetaSetup_same_geometric_fibre_at_trait g n F W Z i X ε p z c c₀ hc R' fg frac hth hev ρ' ε' hS hR y₀ hy₀ c₁ hc₁ R'' fg₁ frac₁ hth₁ hev₁ ρ'' ε'' hS₁ hR₁ y₁ hy₁ u u'`. Take `⟨e, hψ, htor⟩` from `GlobalTheory.T.exists_latticeIso_of_two_padicAlgCl_uniformisations _ _ ρ' ρ'' p y₀ y₁ u u' P₀ a a' ha ha' hL hL'`.

Use `haveI : CharZero (FractionRing u.V) := (algebraMap (FractionRing u.V) (PadicAlgCl p)).charZero`. Use `haveI : CharZero u.V := (algebraMap u.V (FractionRing u.V)).charZero`. Use `haveI : CharZero (FractionRing u'.V) := (algebraMap (FractionRing u'.V) (PadicAlgCl p)).charZero`. Use `haveI : CharZero u'.V := (algebraMap u'.V (FractionRing u'.V)).charZero`. Establish `hrN : 1 ≤ X.S.r * X.S.N` using `Nat.mul_pos X.S.r_pos (by have := X.S.N_ge; omega)`.

Establish `tors : ∀ m, 1 ≤ m → (∀ x : TFK (R` using `u.V) (PadicAlgCl p) ⟶ u.A.A, x ^ m = 1 → ∃ pk, QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x) ∧ ∀ pk, ∃ x, QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x := fun m hm => by`. Take `⟨f, hf1, hf2, -⟩` from `uTors_closed u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) m hm`. Conclude with `⟨fun x hx => let ⟨pk, hpk⟩ := hf2 x hx; ⟨pk, (hf1 pk x).2 hpk.symm⟩, fun pk => ⟨f pk, (hf1 pk _).2 rfl⟩⟩`. Establish `tors' : ∀ m, 1 ≤ m → (∀ x : TFK (R` using `u'.V) (PadicAlgCl p) ⟶ u'.A.A, x ^ m = 1 → ∃ pk, QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk x) ∧ ∀ pk, ∃ x, QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk x := fun m hm => by`. Take `⟨f, hf1, hf2, -⟩` from `uTors_closed u'.V u'.complete u'.A u'.G u'.D u'.U (PadicAlgCl p) m hm`.

Conclude with `⟨fun x hx => let ⟨pk, hpk⟩ := hf2 x hx; ⟨pk, (hf1 pk x).2 hpk.symm⟩, fun pk => ⟨f pk, (hf1 pk _).2 rfl⟩⟩`. Establish `ord : ∀ m pk (x : TFK (R` using `u.V) (PadicAlgCl p) ⟶ u.A.A), QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → x ^ m = 1 := fun m pk x h => by`. Take `⟨w, hw⟩` from `u.U.ext`. Conclude with `(h w hw).1`. Establish `hqe : ∀ χ, l'.q (e χ) = l.q χ` using `fun χ => by`.

Establish `h2` using `(hψ χ _).1 (l.q_eq χ)`. Establish `h3` using `GlobalTheory.ZH.RealCase.psiNorm_unique u' (e χ) h2 (l'.q_eq (e χ))`. Conclude with `(neg_injective (Real.exp_injective h3)).symm`. Establish `hlabe : ∀ b (χ : u.D.toPre.X) (χ' : u'.D.toPre.X), l.yy b = QuotientAddGroup.mk χ → l'.yy b = QuotientAddGroup.mk χ' → CongMod (X.S.r * X.S.N) χ' (e χ)` using `fun b χ χ' h h' => by`. Take `⟨w, x, x', hw, hwa, hwa', hx, hx'⟩` from `hlab b`.

Take `⟨pk, hpk⟩` from `(tors _ hrN).1 x (GlobalTheory.T.uniformised_point_over_label_pow_rN_eq_one _ ρ' p y₀ u b x hx)`. Take `⟨pk', hpk'⟩` from `(tors' _ hrN).1 x' (GlobalTheory.T.uniformised_point_over_label_pow_rN_eq_one _ ρ'' p y₁ u' b x' hx')`. Establish `e1` using `l.yy_eq b pk x hpk hx`. Establish `e2` using `l'.yy_eq b pk' x' hpk' hx'`. Establish `t` using `htor _ pk pk' x x' w hrN hpk hpk' hw hwa hwa'`.

Establish `c1 : CongMod (X.S.r * X.S.N) χ pk.y` using `cm_of_mk (h.symm.trans e1)`. Establish `c2 : CongMod (X.S.r * X.S.N) χ' pk'.y` using `cm_of_mk (h'.symm.trans e2)`. Conclude with `cm_trans c2 (cm_trans t (cm_symm (cm_map e.toAddMonoidHom c1)))`. Establish `hcom : ∀ m, 1 ≤ m → ∀ E (χ : u.D.toPre.X), ∃ χ₂ : u.D.toPre.X, CongMod m (j χ₂) (matAct E (j χ)) ∧ CongMod m (j' (e χ₂)) (matAct E (j' (e χ)))` using `fun m hm E χ => by`. Take `⟨pk, rfl⟩` from `GlobalTheory.LevelMove.exists_lattice_part u.D.toPre u.D.tau_bimult (PadicAlgCl p) m hm χ`.

Take `⟨x, hQ⟩` from `(tors m hm).2 pk`. Take `⟨w, x', hw, hwa, hwa', hx'⟩` from `GlobalTheory.T.torsionPoint_transfer_through_common_grpPullback (PadicAlgCl p) u.A u'.A P₀ a a' ha ha' m x (ord m pk x hQ)`. Take `⟨pk', hQ'⟩` from `(tors' m hm).1 x' hx'`. Establish `hmon` using `GlobalTheory.T.isMonHom_rescaled_realisation_same_genericFibre g n F W Z i X ε hd c₀ hc R' fg frac hth hev ρ' ε' hS E`. Take `⟨x₂, hx₂φ, hx₂⟩` from `GlobalTheory.T.exists_endo_image_torsion_point_uniformised_model _ ρ' p y₀ u (ε' E) hmon m x (ord m pk x hQ)`.

Take `⟨pk₂, hQ₂⟩` from `(tors m hm).1 x₂ hx₂`. Take `⟨w₂, x₂', hw₂, hw₂a, hw₂a', hx₂'⟩` from `GlobalTheory.T.torsionPoint_transfer_through_common_grpPullback (PadicAlgCl p) u.A u'.A P₀ a a' ha ha' m x₂ hx₂`. Take `⟨pk₂', hQ₂'⟩` from `(tors' m hm).1 x₂' hx₂'`. Establish `hε₂ : x₂'.left ≫ u'.φ = x'.left ≫ u'.φ ≫ (ε'' E).left`. Use `hε E w w₂ hw hw₂ (by rw [← Category.assoc, hw₂a, hx₂φ, ← hwa]; simp only [Category.assoc])` as an intermediate fact.

Rewrite using `[← hw₂a', ← hwa']`. Simplify `this` using `only [Category.assoc]`. Establish `c1` using `hall m pk pk₂ x x₂ E hm hQ hQ₂ hx₂φ`. Establish `c2` using `hall' m pk' pk₂' x' x₂' E hm hQ' hQ₂' hε₂`. Establish `t1` using `htor m pk pk' x x' w hm hQ hQ' hw hwa hwa'`.

Establish `t2` using `htor m pk₂ pk₂' x₂ x₂' w₂ hm hQ₂ hQ₂' hw₂ hw₂a hw₂a'`. Use `⟨pk₂.y, c1, ?_⟩` and prove the remaining obligations. Conclude with `cm_trans (cm_symm (cm_map j'.toAddMonoidHom t2)) (cm_trans c2 (cm_map (matAct E) (cm_map j'.toAddMonoidHom t1)))`. Use `⟨(j.symm.trans e).trans j', ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `v`.

Take `⟨χ, rfl⟩` from `j.surjective v`. Simplify using `only [AddEquiv.trans_apply, AddEquiv.symm_apply_apply]`. Establish `h1` using `hq χ`. Establish `h2` using `hq' (e χ)`. Rewrite `h2` using `[hqe]`.

Establish `hs` using `c.scale_pos`. Establish `h4 : ((qW W c.T.β (j' (e χ)) : ℤ) : ℝ) = ((qW W c.T.β (j χ) : ℤ) : ℝ)` using `mul_left_cancel₀ hs.ne' (h2.symm.trans h1)`. Conclude with `h4` after adjusting the coercions. Introduce `b ν hν`. Take `⟨χ, hχ⟩` from `QuotientAddGroup.mk_surjective (l.yy b)`.

Take `⟨χ', hχ'⟩` from `QuotientAddGroup.mk_surjective (l'.yy b)`. Establish `e1` using `hyy b χ hχ.symm`. Establish `e2` using `hyy' b χ' hχ'.symm`. Rewrite using `[e2]`. Apply `cm_mk` to reduce the goal to its premises.

Establish `c0 : CongMod (X.S.r * X.S.N) ν (j χ)` using `cm_of_mk (hν.symm.trans e1)`. Establish `c3` using `hlabe b χ χ' hχ.symm hχ'.symm`. Establish `c4 : CongMod (X.S.r * X.S.N) (j.symm ν) χ` using `by simpa using cm_map j.symm.toAddMonoidHom c0`. Conclude with `cm_trans (cm_map j'.toAddMonoidHom c3) (cm_symm (cm_map j'.toAddMonoidHom (cm_map e.toAddMonoidHom c4)))`. Introduce `m hm E v`.

Take `⟨χ, rfl⟩` from `j.surjective v`. Take `⟨χ₂, c1, c2⟩` from `hcom m hm E χ`. Establish `c3 : CongMod m (j.symm (matAct E (j χ))) χ₂`. Simplify using `using cm_symm (cm_map j.symm.toAddMonoidHom c1)`. Establish `c4` using `cm_trans (cm_map j'.toAddMonoidHom (cm_map e.toAddMonoidHom c3)) c2`.

Simplify `c4` using `[matAct]`.
-/
theorem core : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)), IsDiagEnd F W X.ρ.P X.u ε → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z) (c : CTrait X p z) (yy yy' : X.S.Gam →+ ModN (X.S.r * X.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X ε c yy → IsLab X ε c yy' → ∃ θ : (Fin 8 → c.T.D.toPre.X) ≃+ (Fin 8 → c.T.D.toPre.X), (∀ v, qW W c.T.β (θ v) = qW W c.T.β v) ∧ (∀ x ν, yy x = QuotientAddGroup.mk ν → yy' x = QuotientAddGroup.mk (θ ν)) ∧ ∀ (m : ℕ), 1 ≤ m → ∀ (E : Matrix (Fin 8) (Fin 8) ℤ) (v : Fin 8 → c.T.D.toPre.X), CongMod m (θ (fun a => ∑ b, E a b • v b)) (fun a => ∑ b, E a b • θ v b) := by
  intro g n F W Z i X ε hd p _ z c yy yy' h1 h2
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', ε', hS, -, hR, y₀, hy₀, u, l, j, hq, hyy, hall⟩ := h1
  obtain ⟨c₁, hc₁, R'', fg₁, frac₁, hth₁, hev₁, ρ'', ε'', hS₁, -, hR₁, y₁, hy₁, u', l', j', hq', hyy', hall'⟩ := h2
  obtain ⟨P₀, a, a', ha, ha', hL, hL', hlab, hε⟩ := GlobalTheory.T.rechartings_thetaSetup_same_geometric_fibre_at_trait g n F W Z i X ε p z c c₀ hc R' fg frac hth hev ρ' ε' hS hR
    y₀ hy₀ c₁ hc₁ R'' fg₁ frac₁ hth₁ hev₁ ρ'' ε'' hS₁ hR₁ y₁ hy₁ u u'
  obtain ⟨e, hψ, htor⟩ := GlobalTheory.T.exists_latticeIso_of_two_padicAlgCl_uniformisations _ _ ρ' ρ'' p y₀ y₁ u u' P₀ a a' ha ha' hL hL'
  haveI : CharZero (FractionRing u.V) :=
    (algebraMap (FractionRing u.V) (PadicAlgCl p)).charZero
  haveI : CharZero u.V := (algebraMap u.V (FractionRing u.V)).charZero
  haveI : CharZero (FractionRing u'.V) :=
    (algebraMap (FractionRing u'.V) (PadicAlgCl p)).charZero
  haveI : CharZero u'.V := (algebraMap u'.V (FractionRing u'.V)).charZero
  have hrN : 1 ≤ X.S.r * X.S.N := Nat.mul_pos X.S.r_pos (by have := X.S.N_ge; omega)
  have tors : ∀ m, 1 ≤ m → (∀ x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, x ^ m = 1 →
      ∃ pk, QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x) ∧
      ∀ pk, ∃ x, QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x := fun m hm => by
    obtain ⟨f, hf1, hf2, -⟩ := uTors_closed u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) m hm
    exact ⟨fun x hx => let ⟨pk, hpk⟩ := hf2 x hx; ⟨pk, (hf1 pk x).2 hpk.symm⟩, fun pk => ⟨f pk, (hf1 pk _).2 rfl⟩⟩
  have tors' : ∀ m, 1 ≤ m → (∀ x : TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A, x ^ m = 1 →
      ∃ pk, QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk x) ∧
      ∀ pk, ∃ x, QkToAkU u'.U.toUnifPre (PadicAlgCl p) m pk x := fun m hm => by
    obtain ⟨f, hf1, hf2, -⟩ := uTors_closed u'.V u'.complete u'.A u'.G u'.D u'.U (PadicAlgCl p) m hm
    exact ⟨fun x hx => let ⟨pk, hpk⟩ := hf2 x hx; ⟨pk, (hf1 pk x).2 hpk.symm⟩, fun pk => ⟨f pk, (hf1 pk _).2 rfl⟩⟩
  have ord : ∀ m pk (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x →
      x ^ m = 1 := fun m pk x h => by
    obtain ⟨w, hw⟩ := u.U.ext
    exact (h w hw).1
  have hqe : ∀ χ, l'.q (e χ) = l.q χ := fun χ => by
    have h2 := (hψ χ _).1 (l.q_eq χ)
    have h3 := GlobalTheory.ZH.RealCase.psiNorm_unique u' (e χ) h2 (l'.q_eq (e χ))
    exact (neg_injective (Real.exp_injective h3)).symm
  have hlabe : ∀ b (χ : u.D.toPre.X) (χ' : u'.D.toPre.X), l.yy b = QuotientAddGroup.mk χ →
      l'.yy b = QuotientAddGroup.mk χ' → CongMod (X.S.r * X.S.N) χ' (e χ) := fun b χ χ' h h' => by
    obtain ⟨w, x, x', hw, hwa, hwa', hx, hx'⟩ := hlab b
    obtain ⟨pk, hpk⟩ := (tors _ hrN).1 x (GlobalTheory.T.uniformised_point_over_label_pow_rN_eq_one _ ρ' p y₀ u b x hx)
    obtain ⟨pk', hpk'⟩ := (tors' _ hrN).1 x' (GlobalTheory.T.uniformised_point_over_label_pow_rN_eq_one _ ρ'' p y₁ u' b x' hx')
    have e1 := l.yy_eq b pk x hpk hx
    have e2 := l'.yy_eq b pk' x' hpk' hx'
    have t := htor _ pk pk' x x' w hrN hpk hpk' hw hwa hwa'
    have c1 : CongMod (X.S.r * X.S.N) χ pk.y := cm_of_mk (h.symm.trans e1)
    have c2 : CongMod (X.S.r * X.S.N) χ' pk'.y := cm_of_mk (h'.symm.trans e2)
    exact cm_trans c2 (cm_trans t (cm_symm (cm_map e.toAddMonoidHom c1)))
  have hcom : ∀ m, 1 ≤ m → ∀ E (χ : u.D.toPre.X), ∃ χ₂ : u.D.toPre.X,
      CongMod m (j χ₂) (matAct E (j χ)) ∧ CongMod m (j' (e χ₂)) (matAct E (j' (e χ))) := fun m hm E χ => by
    obtain ⟨pk, rfl⟩ := GlobalTheory.LevelMove.exists_lattice_part u.D.toPre u.D.tau_bimult (PadicAlgCl p) m hm χ
    obtain ⟨x, hQ⟩ := (tors m hm).2 pk
    obtain ⟨w, x', hw, hwa, hwa', hx'⟩ := GlobalTheory.T.torsionPoint_transfer_through_common_grpPullback (PadicAlgCl p) u.A u'.A P₀ a a' ha ha' m x (ord m pk x hQ)
    obtain ⟨pk', hQ'⟩ := (tors' m hm).1 x' hx'
    have hmon := GlobalTheory.T.isMonHom_rescaled_realisation_same_genericFibre g n F W Z i X ε hd c₀ hc R' fg frac hth hev ρ' ε' hS E
    obtain ⟨x₂, hx₂φ, hx₂⟩ := GlobalTheory.T.exists_endo_image_torsion_point_uniformised_model _ ρ' p y₀ u (ε' E) hmon m x (ord m pk x hQ)
    obtain ⟨pk₂, hQ₂⟩ := (tors m hm).1 x₂ hx₂
    obtain ⟨w₂, x₂', hw₂, hw₂a, hw₂a', hx₂'⟩ := GlobalTheory.T.torsionPoint_transfer_through_common_grpPullback (PadicAlgCl p) u.A u'.A P₀ a a' ha ha' m x₂ hx₂
    obtain ⟨pk₂', hQ₂'⟩ := (tors' m hm).1 x₂' hx₂'
    have hε₂ : x₂'.left ≫ u'.φ = x'.left ≫ u'.φ ≫ (ε'' E).left := by
      have := hε E w w₂ hw hw₂ (by rw [← Category.assoc, hw₂a, hx₂φ, ← hwa]; simp only [Category.assoc])
      rw [← hw₂a', ← hwa']
      simpa only [Category.assoc] using this
    have c1 := hall m pk pk₂ x x₂ E hm hQ hQ₂ hx₂φ
    have c2 := hall' m pk' pk₂' x' x₂' E hm hQ' hQ₂' hε₂
    have t1 := htor m pk pk' x x' w hm hQ hQ' hw hwa hwa'
    have t2 := htor m pk₂ pk₂' x₂ x₂' w₂ hm hQ₂ hQ₂' hw₂ hw₂a hw₂a'
    refine ⟨pk₂.y, c1, ?_⟩
    exact cm_trans (cm_symm (cm_map j'.toAddMonoidHom t2))
      (cm_trans c2 (cm_map (matAct E) (cm_map j'.toAddMonoidHom t1)))
  refine ⟨(j.symm.trans e).trans j', ?_, ?_, ?_⟩
  · intro v
    obtain ⟨χ, rfl⟩ := j.surjective v
    simp only [AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
    have h1 := hq χ
    have h2 := hq' (e χ)
    rw [hqe] at h2
    have hs := c.scale_pos
    have h4 : ((qW W c.T.β (j' (e χ)) : ℤ) : ℝ) = ((qW W c.T.β (j χ) : ℤ) : ℝ) :=
      mul_left_cancel₀ hs.ne' (h2.symm.trans h1)
    exact_mod_cast h4
  · intro b ν hν
    obtain ⟨χ, hχ⟩ := QuotientAddGroup.mk_surjective (l.yy b)
    obtain ⟨χ', hχ'⟩ := QuotientAddGroup.mk_surjective (l'.yy b)
    have e1 := hyy b χ hχ.symm
    have e2 := hyy' b χ' hχ'.symm
    rw [e2]
    apply cm_mk
    have c0 : CongMod (X.S.r * X.S.N) ν (j χ) := cm_of_mk (hν.symm.trans e1)
    have c3 := hlabe b χ χ' hχ.symm hχ'.symm
    have c4 : CongMod (X.S.r * X.S.N) (j.symm ν) χ := by simpa using cm_map j.symm.toAddMonoidHom c0
    exact cm_trans (cm_map j'.toAddMonoidHom c3) (cm_symm (cm_map j'.toAddMonoidHom (cm_map e.toAddMonoidHom c4)))
  · intro m hm E v
    obtain ⟨χ, rfl⟩ := j.surjective v
    obtain ⟨χ₂, c1, c2⟩ := hcom m hm E χ
    have c3 : CongMod m (j.symm (matAct E (j χ))) χ₂ := by
      simpa using cm_symm (cm_map j.symm.toAddMonoidHom c1)
    have c4 := cm_trans (cm_map j'.toAddMonoidHom (cm_map e.toAddMonoidHom c3)) c2
    simpa [matAct] using c4

/- English proof (translation)
The claim follows from `core`.
-/
theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)), IsDiagEnd F W X.ρ.P X.u ε → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z) (c : CTrait X p z) (yy yy' : X.S.Gam →+ ModN (X.S.r * X.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X ε c yy → IsLab X ε c yy' → ∃ θ : (Fin 8 → c.T.D.toPre.X) ≃+ (Fin 8 → c.T.D.toPre.X), (∀ v, qW W c.T.β (θ v) = qW W c.T.β v) ∧ (∀ x μ, yy x = QuotientAddGroup.mk μ → yy' x = QuotientAddGroup.mk (θ μ)) ∧ ∀ (m : ℕ), 1 ≤ m → ∀ (E : Matrix (Fin 8) (Fin 8) ℤ) (v : Fin 8 → c.T.D.toPre.X), CongMod m (θ (fun a => ∑ b, E a b • v b)) (fun a => ∑ b, E a b • θ v b) := core

end GlobalTheory.GeomCore
