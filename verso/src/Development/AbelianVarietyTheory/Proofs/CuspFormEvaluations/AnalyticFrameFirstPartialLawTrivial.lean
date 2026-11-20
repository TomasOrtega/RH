import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CubicalReadingOneAnalyticFrameStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsHolFamPullbackLiftOfCommonBase
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.JetRdMulInvPow
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CorrOfJetsOfAnalyticFrameProductsStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AppLESpMapJetPt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CmFrameJetPointsAreExponentialJets
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.JetReadingLinearSubstitutionPoints

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnValPh1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Establish `hc : ContDiffAt ℂ ω (fun v : Fin N → ℂ => v k) 0` using `(contDiff_apply ℂ ℂ k).contDiffAt`. Use `MvPowerSeries.pderiv.ext (fun q => ?_) ?_` and prove the remaining obligations. Take `⟨a, j⟩` from `q`. Take `rfl : a = 0` from `Subsingleton.elim _ _`. Rewrite using `[TM.pderiv_tay hc]`.

Establish `: (fun y : Fin N → ℂ => fderiv ℂ (fun v : Fin N → ℂ => v k) y (Pi.single j 1)) = fun _ => (Pi.single j (1 : ℂ) : Fin N → ℂ) k`. Use function extensionality and compare the values at `y`. Use `(ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) k).fderiv (x := y)` as an intermediate fact. Express the relevant statement in the definitionally equal form `fderiv ℂ (fun v : Fin N → ℂ => v k) y = _ at this`. Rewrite using `[this]`.

Both sides reduce to the same expression. Rewrite using `[this, TM.tay_const, MvPowerSeries.pderiv_X]`. Distinguish the cases in `h : k = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h, Prod.ext_iff, Ne.symm h]`. Rewrite using `[constantCoeff_tay, TM.mD_zero]`. Simplify using the standard rewrite rules.
-/
theorem tay_coord {N : ℕ} (k : Fin N) : tay (fun v : Fin N → ℂ => v k) 0 = MvPowerSeries.X ((0 : Fin 1), k) := by
  have hc : ContDiffAt ℂ ω (fun v : Fin N → ℂ => v k) 0 := (contDiff_apply ℂ ℂ k).contDiffAt
  refine MvPowerSeries.pderiv.ext (fun q => ?_) ?_
  · obtain ⟨a, j⟩ := q
    obtain rfl : a = 0 := Subsingleton.elim _ _
    rw [TM.pderiv_tay hc]
    have : (fun y : Fin N → ℂ => fderiv ℂ (fun v : Fin N → ℂ => v k) y (Pi.single j 1)) =
        fun _ => (Pi.single j (1 : ℂ) : Fin N → ℂ) k := by
      funext y
      have := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) k).fderiv (x := y)
      change fderiv ℂ (fun v : Fin N → ℂ => v k) y = _ at this
      rw [this]; rfl
    rw [this, TM.tay_const, MvPowerSeries.pderiv_X]
    by_cases h : k = j
    · subst h; simp
    · simp [h, Prod.ext_iff, Ne.symm h]
  · rw [constantCoeff_tay, TM.mD_zero]; simp

/- English proof (translation)
Rewrite using `[jetOf, tay_coord, ← MvPolynomial.coe_X, psJet, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe]`.
-/
theorem jetOf_coord {N : ℕ} (m : ℕ) (k : Fin N) :
    jetOf m (fun v : Fin N → ℂ => v k) = Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), k)) := by
  rw [jetOf, tay_coord, ← MvPolynomial.coe_X, psJet, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe]

/- English proof (translation)
Proceed by induction on `I using Finset.induction_on with`. Consider the case `empty => simpa using jetOf_const (g := N) m 0`. Consider the case `insert a s ha ih`. Simplify using `only [Finset.sum_insert ha, map_add]`. Rewrite using `[← ih, ← jetOf_coord, ← jetOf_add]`.

Both sides reduce to the same expression. Conclude with `(contDiff_apply ℂ ℂ _).contDiffAt`. Conclude with `(ContDiff.sum fun i _ => contDiff_apply ℂ ℂ _).contDiffAt`.
-/
theorem jetOf_sum_coord {N : ℕ} (m : ℕ) {T : Type} (I : Finset T) (k : T → Fin N) :
    jetOf m (fun v : Fin N → ℂ => ∑ i ∈ I, v (k i)) =
      Ideal.Quotient.mk _ (∑ i ∈ I, MvPolynomial.X ((0 : Fin 1), k i)) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using jetOf_const (g := N) m 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha, map_add]
    rw [← ih, ← jetOf_coord, ← jetOf_add]
    · rfl
    · exact (contDiff_apply ℂ ℂ _).contDiffAt
    · exact (ContDiff.sum fun i _ => contDiff_apply ℂ ℂ _).contDiffAt

/- English proof (translation)
Simplify using `[psumL, LinearMap.sum_apply]`.
-/
theorem psumL_apply (n g : ℕ) (I : Finset (Fin n)) (w : Fin n → Fin g → ℂ) :
    psumL n g ⟨I⟩ w = ∑ i ∈ I, w i := by
  simp [psumL, LinearMap.sum_apply]

/- English proof (translation)
Establish `: (fun v => psumL n g ⟨I⟩ (colsOf n g v) j) = fun v : Fin (n * g) → ℂ => ∑ i ∈ I, v (finProdFinEquiv (i, j))`. Use function extensionality and compare the values at `v`. Rewrite using `[psumL_apply, Finset.sum_apply]`. Both sides reduce to the same expression. Rewrite using `[jetN, this, jetOf_sum_coord, renN, GermD.jetMap_mk]`.

Simplify using `only [map_sum, MvPolynomial.aeval_X, Equiv.symm_apply_apply]`.
-/
theorem jetN_psum {n g : ℕ} (m : ℕ) (I : Finset (Fin n)) (j : Fin g) :
    jetN m (fun w => psumL n g ⟨I⟩ w j) = Ideal.Quotient.mk _ (∑ i ∈ I, MvPolynomial.X (i, j)) := by
  have : (fun v => psumL n g ⟨I⟩ (colsOf n g v) j) = fun v : Fin (n * g) → ℂ => ∑ i ∈ I, v (finProdFinEquiv (i, j)) := by
    funext v
    rw [psumL_apply, Finset.sum_apply]; rfl
  rw [jetN, this, jetOf_sum_coord, renN, GermD.jetMap_mk]
  simp only [map_sum, MvPolynomial.aeval_X, Equiv.symm_apply_apply]

/- English proof (translation)
Establish `key : ∀ {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (σ : K → J) (_ : ∀ k, φ k = F (σ k)) (ψ : Y ⟶ X), (∑ k, if φ k = ψ then ε k else 0) = ∑ I, if F I = ψ then (∑ k, if σ k = I then ε k else 0) else 0`. Introduce `K _ φ ε σ h ψ`. Establish `: ∀ I, (if F I = ψ then (∑ k, if σ k = I then ε k else 0) else 0) = ∑ k, if σ k = I then (if φ k = ψ then ε k else 0) else 0`. Introduce `I`. Use `split_ifs with hI`.

Use `Finset.sum_congr rfl fun k _ => ?_ split_ifs with h1 h2` and prove the remaining obligations. Both sides reduce to the same expression. Conclude with `absurd (by rw [h, h1, hI]) h2`. Both sides reduce to the same expression. Use `(Finset.sum_eq_zero fun k _ => ?_).symm split_ifs with h1 h2` and prove the remaining obligations.

Conclude with `absurd (by rw [← h1, ← h, h2]) hI`. Both sides reduce to the same expression. Both sides reduce to the same expression. Simplify using `only [this]`. Rewrite using `[Finset.sum_comm]`.

Simplify using the standard rewrite rules. Introduce `ψ`. Establish `a` using `key φ ε σ h ψ`. Establish `b` using `key φ' ε' σ' h' ψ`. Simplify using `only [hc] at a`.

Use `a.trans b.symm` and compare the differences between its conclusion and the goal.
-/
theorem sameSum_of_factor {X Y : Scheme.{0}} {K K' J : Type} [Fintype K] [Fintype K'] [Fintype J] [DecidableEq J]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (F : J → (Y ⟶ X)) (σ : K → J) (σ' : K' → J)
    (h : ∀ k, φ k = F (σ k)) (h' : ∀ k, φ' k = F (σ' k))
    (hc : ∀ I, (∑ k, if σ k = I then ε k else 0) = ∑ k, if σ' k = I then ε' k else 0) :
    LB.SameSum φ ε φ' ε' := by
  classical
  have key : ∀ {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (σ : K → J) (_ : ∀ k, φ k = F (σ k)) (ψ : Y ⟶ X),
      (∑ k, if φ k = ψ then ε k else 0) = ∑ I, if F I = ψ then (∑ k, if σ k = I then ε k else 0) else 0 := by
    intro K _ φ ε σ h ψ
    have : ∀ I, (if F I = ψ then (∑ k, if σ k = I then ε k else 0) else 0) =
        ∑ k, if σ k = I then (if φ k = ψ then ε k else 0) else 0 := by
      intro I
      split_ifs with hI
      · refine Finset.sum_congr rfl fun k _ => ?_
        split_ifs with h1 h2
        · rfl
        · exact absurd (by rw [h, h1, hI]) h2
        · rfl
      · refine (Finset.sum_eq_zero fun k _ => ?_).symm
        split_ifs with h1 h2
        · exact absurd (by rw [← h1, ← h, h2]) hI
        · rfl
        · rfl
    simp only [this]
    rw [Finset.sum_comm]
    simp
  intro ψ
  have a := key φ ε σ h ψ
  have b := key φ' ε' σ' h' ψ
  simp only [hc] at a
  convert a.trans b.symm

section General

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)

/- English proof (translation)
Set `F : J → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)` to `fun I => if hol : IsHolFam (fun v : Fin (n * g) → ℂ => (Φ.e (Λ I (colsOf n g v))).left) then spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫ jetPt _ hol m else spMap (algebraMap ℂ _) ≫ (Φ.e 0).left`. Use `sameSum_of_factor φ ε φ' ε' F σ σ' (fun k => ?_) (fun k => ?_) hc` and prove the remaining obligations. Take `⟨hol, e⟩` from `h k`. Simplify using `only [F, dif_pos hol]`. Conclude with `e`.

Take `⟨hol, e⟩` from `h' k`. Simplify using `only [F, dif_pos hol]`. Conclude with `e`.
-/
theorem sameSum_of_jetMap {n : ℕ} (m : ℕ) {K K' J : Type} [Fintype K] [Fintype K'] [Fintype J] [DecidableEq J]
    (φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε : K → ℤ)
    (φ' : K' → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε' : K' → ℤ)
    (Λ : J → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (σ : K → J) (σ' : K' → J)
    (h : ∀ k, Φ.JetMap m (φ k) (Λ (σ k))) (h' : ∀ k, Φ.JetMap m (φ' k) (Λ (σ' k)))
    (hc : ∀ I, (∑ k, if σ k = I then ε k else 0) = ∑ k, if σ' k = I then ε' k else 0) :
    LB.SameSum φ ε φ' ε' := by
  classical
  let F : J → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left) := fun I =>
    if hol : IsHolFam (fun v : Fin (n * g) → ℂ => (Φ.e (Λ I (colsOf n g v))).left) then
      spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫ jetPt _ hol m
    else spMap (algebraMap ℂ _) ≫ (Φ.e 0).left
  refine sameSum_of_factor φ ε φ' ε' F σ σ' (fun k => ?_) (fun k => ?_) hc
  · obtain ⟨hol, e⟩ := h k
    simp only [F, dif_pos hol]; exact e
  · obtain ⟨hol, e⟩ := h' k
    simp only [F, dif_pos hol]; exact e

end General

/- English proof (translation)
Establish `hq : IsHolFam (fun v => (lift (f v) (h v)).left)` using `GlobalTheory.AnVal.isHolFam_pullback_lift _ _ _ P.hom Q.hom _ _ _ x (fun v => Over.w (f v)) (fun v => Over.w (h v)) hf hh`. Use `⟨hq, ?_⟩` and prove the remaining obligations. Establish `k1` using `jetPt_comp _ hq (fst P Q).left _ hf (fun v => by rw [← Over.comp_left, lift_fst]) m`. Establish `k2` using `jetPt_comp _ hq (snd P Q).left _ hh (fun v => by rw [← Over.comp_left, lift_snd]) m`. Establish `l1 : (lift a b).left ≫ (fst P Q).left = (spMap r ≫ jetPt _ hq m) ≫ (fst P Q).left`.

Rewrite using `[Category.assoc, k1, ← ea, ← Over.comp_left, lift_fst]`. Establish `l2 : (lift a b).left ≫ (snd P Q).left = (spMap r ≫ jetPt _ hq m) ≫ (snd P Q).left`. Rewrite using `[Category.assoc, k2, ← eb, ← Over.comp_left, lift_snd]`. Conclude with `pullback.hom_ext l1 l2`.
-/
theorem lift_jet {S : Scheme.{0}} {P Q : Over S} {N m : ℕ} {R : Type} [CommRing R]
    (r : Jet ℂ (Fin 1 × Fin N) m →+* R) (u : Sp R ⟶ S) (x : Sp ℂ ⟶ S)
    (a : Over.mk u ⟶ P) (b : Over.mk u ⟶ Q) (f : (Fin N → ℂ) → (Over.mk x ⟶ P)) (h : (Fin N → ℂ) → (Over.mk x ⟶ Q))
    (hf : IsHolFam fun v => (f v).left) (hh : IsHolFam fun v => (h v).left)
    (ea : a.left = spMap r ≫ jetPt _ hf m) (eb : b.left = spMap r ≫ jetPt _ hh m) :
    ∃ hq : IsHolFam (fun v => (lift (f v) (h v)).left), (lift a b).left = spMap r ≫ jetPt _ hq m := by
  have hq : IsHolFam (fun v => (lift (f v) (h v)).left) :=
    GlobalTheory.AnVal.isHolFam_pullback_lift _ _ _ P.hom Q.hom _ _ _ x (fun v => Over.w (f v)) (fun v => Over.w (h v)) hf hh
  refine ⟨hq, ?_⟩
  have k1 := jetPt_comp _ hq (fst P Q).left _ hf (fun v => by rw [← Over.comp_left, lift_fst]) m
  have k2 := jetPt_comp _ hq (snd P Q).left _ hh (fun v => by rw [← Over.comp_left, lift_snd]) m
  have l1 : (lift a b).left ≫ (fst P Q).left = (spMap r ≫ jetPt _ hq m) ≫ (fst P Q).left := by
    rw [Category.assoc, k1, ← ea, ← Over.comp_left, lift_fst]
  have l2 : (lift a b).left ≫ (snd P Q).left = (spMap r ≫ jetPt _ hq m) ≫ (snd P Q).left := by
    rw [Category.assoc, k2, ← eb, ← Over.comp_left, lift_snd]
  exact pullback.hom_ext l1 l2

section Pt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] {y : FrPt Xo c ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {el : Fin g ≃ Lt1 Dw} (Φ : AnPt y g ty el)

/- English proof (translation)
Set `B : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin 2 → Fin g → ℂ)` to `LinearMap.pi fun k => psumL n g ⟨T k⟩`. Establish `h` using `GlobalTheory.JetLinSub.jetRd_linSubst _ _ _ _ g Φ.toAnFr 2 n m B (fun p : Fin 2 × Fin g => φ p.1 p.2) (fun p => by`. Rewrite using `[← MvPolynomial.coe_X, psJet, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe, jetSubstP, GermD.jetMap_mk, MvPolynomial.aeval_X, hφ]`. Conclude with `(jetN_psum m (T p.1) p.2).symm) _ _ _ _ _ (he m).2`. Establish `hΛ : (fun K => psumL 2 g K ∘ₗ B) = fun K => psumL n g ⟨K.down.biUnion T⟩`.

Use function extensionality and compare the values at `K`. Take `⟨K⟩` from `K`. Use `LinearMap.ext fun w => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, psumL_apply, psumL_apply, Finset.sum_biUnion]`. Conclude with `Finset.sum_congr rfl fun k _ => psumL_apply n g (T k) w`.

Apply the tactic sequence `intro a _ b _ hab fin_cases a <;> fin_cases b`. Conclude with `absurd rfl hab`. Conclude with `hT`. Conclude with `hT.symm`. Conclude with `absurd rfl hab`.

Rewrite `h` using `[hΛ]`. Conclude with `h`.
-/
theorem pe_jetRd (e : ∀ m, FrTy y g Φ.jx m) (he : Φ.IsAnE e) (m : ℕ) {n : ℕ} (T : Fin 2 → Finset (Fin n))
    (hT : Disjoint (T 0) (T 1)) (φ : Fin 2 → Fin g → MvPolynomial (Fin n × Fin g) ℂ)
    (hφ : ∀ k j, Ideal.Quotient.mk (orig ℂ (Fin n × Fin g) ^ (m + 1))
      (φ k j - MvPolynomial.C (MvPolynomial.constantCoeff (φ k j))) =
      Ideal.Quotient.mk _ (∑ i ∈ T k, MvPolynomial.X (i, j))) :
    Φ.toAnFr.JetRd m _ _ (pe y g Φ.jx e m φ) (fun K => psumL n g ⟨K.down.biUnion T⟩) := by
  let B : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin 2 → Fin g → ℂ) := LinearMap.pi fun k => psumL n g ⟨T k⟩
  have h := GlobalTheory.JetLinSub.jetRd_linSubst _ _ _ _ g Φ.toAnFr 2 n m B (fun p : Fin 2 × Fin g => φ p.1 p.2) (fun p => by
    rw [← MvPolynomial.coe_X, psJet, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe, jetSubstP, GermD.jetMap_mk,
      MvPolynomial.aeval_X, hφ]
    exact (jetN_psum m (T p.1) p.2).symm) _ _ _ _ _ (he m).2
  have hΛ : (fun K => psumL 2 g K ∘ₗ B) = fun K => psumL n g ⟨K.down.biUnion T⟩ := by
    funext K
    obtain ⟨K⟩ := K
    refine LinearMap.ext fun w => ?_
    rw [LinearMap.comp_apply, psumL_apply, psumL_apply, Finset.sum_biUnion]
    · exact Finset.sum_congr rfl fun k _ => psumL_apply n g (T k) w
    · intro a _ b _ hab
      fin_cases a <;> fin_cases b
      · exact absurd rfl hab
      · exact hT
      · exact hT.symm
      · exact absurd rfl hab
  rw [hΛ] at h
  exact h

/- English proof (translation)
Take `⟨h2, e2⟩` from `((GlobalTheory.AnVal.jetPts_jetMap E H Dw l Xo c y g ty el Φ n m).2.2.1 b d Λb Λd hb hd).2`. Take `⟨h1, e1⟩` from `ha`. Conclude with `lift_jet _ _ y.x a (lift b d) _ _ h1 h2 e1 e2`.
-/
theorem jet_triple_points_eq_jet_exponentials (m : ℕ) {n : ℕ} (a b d : jO y g m n ⟶ Xo.univ.t.G)
    (Λa Λb Λd : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (ha : Φ.toAnFr.JetMap m a.left Λa)
    (hb : Φ.toAnFr.JetMap m b.left Λb) (hd : Φ.toAnFr.JetMap m d.left Λd) :
    ∃ hq : IsHolFam (fun v : Fin (n * g) → ℂ => (lift (Φ.e (Λa (colsOf n g v)))
      (lift (Φ.e (Λb (colsOf n g v))) (Φ.e (Λd (colsOf n g v))))).left),
      (lift a (lift b d)).left =
        spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫ jetPt _ hq m := by
  obtain ⟨h2, e2⟩ := ((GlobalTheory.AnVal.jetPts_jetMap E H Dw l Xo c y g ty el Φ n m).2.2.1 b d Λb Λd hb hd).2
  obtain ⟨h1, e1⟩ := ha
  exact lift_jet _ _ y.x a (lift b d) _ _ h1 h2 e1 e2

/- English proof (translation)
Establish `hj` using `(GlobalTheory.AnVal.jetPts_jetMap E H Dw l Xo c y g ty el Φ 3 m).1`. Take `⟨hq, eq⟩` from `jet_triple_points_eq_jet_exponentials Φ m _ _ _ _ _ _ (hj 0) (hj 1) (hj 2)`. Rewrite using `[eq]`. Use `GlobalTheory.AnValJetGlob.jetRd_pullGen _ _ _ _ g Φ.toAnFr 3 m _ _ _ _ _ _ _ hq fun v => ?_` and prove the remaining obligations. Establish `h` using `GlobalTheory.T.cubical_reading_one_analyticFrame E H Dw l Xo c y g ty el Φ (colsOf 3 g v 0) (colsOf 3 g v 1) (colsOf 3 g v 2)`.

Establish `hv : ![colsOf 3 g v 0, colsOf 3 g v 1, colsOf 3 g v 2] = colsOf 3 g v`. Apply the tactic sequence `funext i; fin_cases i <;> rfl`. Rewrite `h` using `[hv]`. Conclude with `h`.
-/
theorem cub_jetRd (m : ℕ) :
    Φ.toAnFr.JetRd m _ _ (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
      (lift (jpt y g Φ.jx m (0 : Fin 3)) (lift (jpt y g Φ.jx m (1 : Fin 3)) (jpt y g Φ.jx m (2 : Fin 3)))).left)
      (fun I => psumL 3 g ⟨I.down⟩) := by
  have hj := (GlobalTheory.AnVal.jetPts_jetMap E H Dw l Xo c y g ty el Φ 3 m).1
  obtain ⟨hq, eq⟩ := jet_triple_points_eq_jet_exponentials Φ m _ _ _ _ _ _ (hj 0) (hj 1) (hj 2)
  rw [eq]
  refine GlobalTheory.AnValJetGlob.jetRd_pullGen _ _ _ _ g Φ.toAnFr 3 m _ _ _ _ _ _ _ hq fun v => ?_
  have h := GlobalTheory.T.cubical_reading_one_analyticFrame E H Dw l Xo c y g ty el Φ (colsOf 3 g v 0) (colsOf 3 g v 1) (colsOf 3 g v 2)
  have hv : ![colsOf 3 g v 0, colsOf 3 g v 1, colsOf 3 g v 2] = colsOf 3 g v := by
    funext i; fin_cases i <;> rfl
  rw [hv] at h
  exact h

/- English proof (translation)
Take `⟨s⟩` from `t`. Simplify using `[Formalism.L2.Pj.scaleGen, res]`.
-/
theorem scaleGen_one {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ Xo.univ.t.G.left)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) : Formalism.L2.Pj.scaleGen φ ε 1 t = t := by
  obtain ⟨s⟩ := t
  simp [Formalism.L2.Pj.scaleGen, res]

end Pt

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hX {n g : ℕ} (m : ℕ) (i : Fin n) (j : Fin g) :
    Ideal.Quotient.mk (orig ℂ (Fin n × Fin g) ^ (m + 1))
      ((MvPolynomial.X (i, j) : MvPolynomial (Fin n × Fin g) ℂ) -
        MvPolynomial.C (MvPolynomial.constantCoeff (MvPolynomial.X (i, j) : MvPolynomial (Fin n × Fin g) ℂ))) =
      Ideal.Quotient.mk _ (∑ i ∈ ({i} : Finset (Fin n)), MvPolynomial.X (i, j)) := by
  simp

/- English proof (translation)
Establish `hc : MvPolynomial.constantCoeff (psTrunc m (addF ℂ g j)) = 0`. Rewrite using `[FBIdJet.psTrunc_eq, MvPolynomial.constantCoeff_eq, MvPowerSeries.coeff_truncTotal _ (by simp), MvPowerSeries.coeff_zero_eq_constantCoeff_apply]`. Simplify using `[addF]`. Establish `ha : (addF ℂ g j : MvPowerSeries (Fin 2 × Fin g) ℂ) = ((MvPolynomial.X ((0 : Fin 2), j) + MvPolynomial.X ((1 : Fin 2), j) : MvPolynomial (Fin 2 × Fin g) ℂ) : MvPowerSeries (Fin 2 × Fin g) ℂ)` using `by simp [addF]`. Rewrite using `[psIn, MvPolynomial.constantCoeff_rename, hc, map_zero, sub_zero, Finset.sum_pair hab]`.

Establish `h1` using `GermD.jetMap_mk (m := m) (fun p : Fin 2 × Fin g => (MvPolynomial.X (![a, b] p.1, p.2) : MvPolynomial (Fin n × Fin g) ℂ)) (fun _ => X_mem_orig _)`. Establish `h2 : ∀ P : MvPolynomial (Fin 2 × Fin g) ℂ, MvPolynomial.rename (fun p : Fin 2 × Fin g => (![a, b] p.1, p.2)) P = MvPolynomial.aeval (fun p : Fin 2 × Fin g => (MvPolynomial.X (![a, b] p.1, p.2) : MvPolynomial (Fin n × Fin g) ℂ)) P` using `fun P => by`. Rewrite using `[MvPolynomial.rename_eq_aeval]`. Both sides reduce to the same expression. Rewrite using `[h2, ← h1, ha, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe, h1]`.

Simplify using the standard rewrite rules.
-/
theorem hAdd {n g : ℕ} (m : ℕ) (a b : Fin n) (hab : a ≠ b) (j : Fin g) :
    Ideal.Quotient.mk (orig ℂ (Fin n × Fin g) ^ (m + 1))
      (psIn g m ![a, b] (addF ℂ g j) -
        MvPolynomial.C (MvPolynomial.constantCoeff (psIn g m ![a, b] (addF ℂ g j)))) =
      Ideal.Quotient.mk _ (∑ i ∈ ({a, b} : Finset (Fin n)), MvPolynomial.X (i, j)) := by
  have hc : MvPolynomial.constantCoeff (psTrunc m (addF ℂ g j)) = 0 := by
    rw [FBIdJet.psTrunc_eq, MvPolynomial.constantCoeff_eq, MvPowerSeries.coeff_truncTotal _ (by simp),
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [addF]
  have ha : (addF ℂ g j : MvPowerSeries (Fin 2 × Fin g) ℂ) =
      ((MvPolynomial.X ((0 : Fin 2), j) + MvPolynomial.X ((1 : Fin 2), j) : MvPolynomial (Fin 2 × Fin g) ℂ) :
        MvPowerSeries (Fin 2 × Fin g) ℂ) := by simp [addF]
  rw [psIn, MvPolynomial.constantCoeff_rename, hc, map_zero, sub_zero, Finset.sum_pair hab]
  have h1 := GermD.jetMap_mk (m := m) (fun p : Fin 2 × Fin g => (MvPolynomial.X (![a, b] p.1, p.2) :
    MvPolynomial (Fin n × Fin g) ℂ)) (fun _ => X_mem_orig _)
  have h2 : ∀ P : MvPolynomial (Fin 2 × Fin g) ℂ, MvPolynomial.rename (fun p : Fin 2 × Fin g => (![a, b] p.1, p.2)) P =
      MvPolynomial.aeval (fun p : Fin 2 × Fin g => (MvPolynomial.X (![a, b] p.1, p.2) :
        MvPolynomial (Fin n × Fin g) ℂ)) P := fun P => by
    rw [MvPolynomial.rename_eq_aeval]; rfl
  rw [h2, ← h1, ha, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe, h1]
  simp

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c _ _ y g ty el Φ hI e he m`. Use `⟨1, (FBIdJet.psJet_one m).symm, ?_⟩` and prove the remaining obligations. Establish `hu : unitΓ (1 : (Jet ℂ (Fin 3 × Fin g) m)ˣ) = 1` using `map_one _`. Rewrite using `[hu, scaleGen_one]`. Establish `h0` using `cub_jetRd Φ m`.

Establish `h1` using `pe_jetRd Φ e he m ![{0, 1}, {2}] (by decide) ![fun j => psIn g m ![0, 1] ((anFB ty).G.F j), fun j => MvPolynomial.X ((2 : Fin 3), j)] (fun k j => by fin_cases k`. Conclude with `hAdd m 0 1 (by decide) j`. Conclude with `hX m 2 j)`. Establish `h2` using `pe_jetRd Φ e he m ![{0}, {2}] (by decide) ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] (fun k j => by fin_cases k`. Conclude with `hX m 0 j`.

Conclude with `hX m 2 j)`. Establish `h3` using `pe_jetRd Φ e he m ![{1}, {2}] (by decide) ![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] (fun k j => by fin_cases k`. Conclude with `hX m 1 j`. Conclude with `hX m 2 j)`. Establish `alg` using `GlobalTheory.AnVal.jetRd_mul_inv_pow _ _ _ _ g Φ.toAnFr 3 m`.

Establish `i2` using `(alg _ _ _ _ _ _ _ _ _ _ h2 h2).2.1`. Establish `i3` using `(alg _ _ _ _ _ _ _ _ _ _ h3 h3).2.1`. Establish `m23` using `(alg _ _ _ _ _ _ _ _ _ _ i2 i3).1`. Establish `m123` using `(alg _ _ _ _ _ _ _ _ _ _ h1 m23).1`. Use `GlobalTheory.T.corr_of_jets_of_analytic_frame_products _ _ _ _ g Φ.toAnFr hI 3 m _ _ _ _ _ _ _ _ _ _ h0 m123 ?_` and prove the remaining obligations.

Use `sameSum_of_jetMap Φ.toAnFr m _ _ _ _ (fun I : Finset (Fin 3) => psumL 3 g ⟨I⟩) (fun I => I.down) (Sum.elim (fun K => K.down.biUnion ![{0, 1}, {2}]) (Sum.elim (fun K => K.down.biUnion ![{0}, {2}]) (fun K => K.down.biUnion ![{1}, {2}]))) h0.1 (fun k => ?_) ?_` and prove the remaining obligations. Use `m123.1 k` as an intermediate fact. Apply the tactic sequence `rcases k with k | k | k <;> exact this`. Evaluate the decidable proposition.
-/
theorem first_partial_law : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), Φ.toAnFr.Imm → ∀ e : ∀ m, FrTy y g Φ.jx m, Φ.IsAnE e → ∀ m, ∃ u : (Jet ℂ (Fin 3 × Fin g) m)ˣ, (u : Jet ℂ (Fin 3 × Fin g) m) = psJet m (anFB ty).ph1 ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t (lift (jpt y g Φ.jx m (0 : Fin 3)) (lift (jpt y g Φ.jx m (1 : Fin 3)) (jpt y g Φ.jx m (2 : Fin 3)))).left) (scaleGen _ _ (unitΓ u) (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (pe y g Φ.jx e m ![fun j => psIn g m ![0, 1] ((anFB ty).G.F j), fun j => MvPolynomial.X ((2 : Fin 3), j)]) (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.invGen Xo.univ.t.PP.L _ _ (pe y g Φ.jx e m ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)])) (LB.invGen Xo.univ.t.PP.L _ _ (pe y g Φ.jx e m ![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)]))))) := by
  intro E _ _ _ H Dw l Xo c _ _ y g ty el Φ hI e he m
  refine ⟨1, (FBIdJet.psJet_one m).symm, ?_⟩
  have hu : unitΓ (1 : (Jet ℂ (Fin 3 × Fin g) m)ˣ) = 1 := map_one _
  rw [hu, scaleGen_one]
  have h0 := cub_jetRd Φ m
  have h1 := pe_jetRd Φ e he m ![{0, 1}, {2}] (by decide)
    ![fun j => psIn g m ![0, 1] ((anFB ty).G.F j), fun j => MvPolynomial.X ((2 : Fin 3), j)] (fun k j => by
      fin_cases k
      · exact hAdd m 0 1 (by decide) j
      · exact hX m 2 j)
  have h2 := pe_jetRd Φ e he m ![{0}, {2}] (by decide)
    ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] (fun k j => by
      fin_cases k
      · exact hX m 0 j
      · exact hX m 2 j)
  have h3 := pe_jetRd Φ e he m ![{1}, {2}] (by decide)
    ![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] (fun k j => by
      fin_cases k
      · exact hX m 1 j
      · exact hX m 2 j)
  have alg := GlobalTheory.AnVal.jetRd_mul_inv_pow _ _ _ _ g Φ.toAnFr 3 m
  have i2 := (alg _ _ _ _ _ _ _ _ _ _ h2 h2).2.1
  have i3 := (alg _ _ _ _ _ _ _ _ _ _ h3 h3).2.1
  have m23 := (alg _ _ _ _ _ _ _ _ _ _ i2 i3).1
  have m123 := (alg _ _ _ _ _ _ _ _ _ _ h1 m23).1
  refine GlobalTheory.T.corr_of_jets_of_analytic_frame_products _ _ _ _ g Φ.toAnFr hI 3 m _ _ _ _ _ _ _ _ _ _ h0 m123 ?_
  refine sameSum_of_jetMap Φ.toAnFr m _ _ _ _ (fun I : Finset (Fin 3) => psumL 3 g ⟨I⟩) (fun I => I.down)
    (Sum.elim (fun K => K.down.biUnion ![{0, 1}, {2}])
      (Sum.elim (fun K => K.down.biUnion ![{0}, {2}]) (fun K => K.down.biUnion ![{1}, {2}]))) h0.1 (fun k => ?_) ?_
  · have := m123.1 k
    rcases k with k | k | k <;> exact this
  · decide

end GlobalTheory.AnValPh1
