import Development.WeilBound.CoreStatements.MultihomogeneousSquares.AntisymmetryFibreSquares
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelExistsOfGivenStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseMetricExistsOfGivenStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelArithDimensionBoundaryStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticDataUniformisedStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverDegreeOneRealisationStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverRealisationPullbackStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFlagXdegStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptBirationalArithVarStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmHostRankBounds
import Development.WeilBound.CoreStatements.FlagImmersions.SumFundOnRoot

noncomputable section

namespace SquareStatements

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights (antisymDegree)

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[← add_assoc, Nat.choose_succ_succ', Nat.choose_one_right, ih, Nat.choose_succ_succ' m 1, Nat.choose_one_right]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem choose_two_add (j m : ℕ) : (j + m).choose 2 = j * m + j.choose 2 + m.choose 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← add_assoc, Nat.choose_succ_succ', Nat.choose_one_right, ih, Nat.choose_succ_succ' m 1,
      Nat.choose_one_right]
    ring

/- English proof (translation)
Use `show ξ ((Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint Ω)) = ξ (IsLocalRing.closedPoint Ω₀)`. Use `congr 1`. Conclude with `Subsingleton.elim _ _`.
-/
theorem genPt_comp {X : Scheme.{0}} {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] (φ : Ω₀ →+* Ω)
    (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) :
    GlobalTheory.CompanionTheory.Ar.genPt (Spec.map (CommRingCat.ofHom φ) ≫ ξ) = GlobalTheory.CompanionTheory.Ar.genPt ξ := by
  show ξ ((Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint Ω)) = ξ (IsLocalRing.closedPoint Ω₀)
  congr 1
  exact Subsingleton.elim _ _

/- English proof (translation)
Establish `e₁ : A'.ξ ≫ A'.f = Spec.map (CommRingCat.ofHom A'.fn) ≫ A'.ξ₀` using `A'.fn_over`. Establish `e₂ : A.ξ ≫ A.f = Spec.map (CommRingCat.ofHom A.fn) ≫ A.ξ₀` using `A.fn_over`. Establish `e₃ : A'.ξ ≫ h = Spec.map (CommRingCat.ofHom i) ≫ A.ξ` using `a.1`. Rewrite using `[← genPt_comp A'.fn, ← e₁, a.2.1, ← Category.assoc, e₃, Category.assoc, e₂, genPt_comp, genPt_comp]`.
-/
theorem genPt_of_over {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S S' : Finset ℕ}
    {Ω Ω' : Type} [Field Ω] [Field Ω'] {K K' : Type} [Fintype K] [Fintype K'] {J : K → Type} {J' : K' → Type}
    {x : (Σ k, J k) → Ω} {x' : (Σ k, J' k) → Ω'} {A' : HodgeCpt Y S' x'} {A : HodgeCpt Y S x} {h : A'.X ⟶ A.X}
    {i : Ω →+* Ω'} {j : A.Li →+ A'.Li} (a : PB.HodgeOver A' A h i j) :
    GlobalTheory.CompanionTheory.Ar.genPt A'.ξ₀ = GlobalTheory.CompanionTheory.Ar.genPt A.ξ₀ := by
  have e₁ : A'.ξ ≫ A'.f = Spec.map (CommRingCat.ofHom A'.fn) ≫ A'.ξ₀ := A'.fn_over
  have e₂ : A.ξ ≫ A.f = Spec.map (CommRingCat.ofHom A.fn) ≫ A.ξ₀ := A.fn_over
  have e₃ : A'.ξ ≫ h = Spec.map (CommRingCat.ofHom i) ≫ A.ξ := a.1
  rw [← genPt_comp A'.fn, ← e₁, a.2.1, ← Category.assoc, e₃, Category.assoc, e₂, genPt_comp, genPt_comp]

/- English proof (translation)
Establish `: ∀ t w, Re.num II t w = Re'.num II t w` using `fun t w => by`. Simplify using `only [PB.Realis.num, hd, hl]`. Use `congrArg (PB.formPoly (e + 1)) (funext fun w => ?_)` and prove the remaining obligations. Simplify using `only [PB.Realis.limNum, this]`.
-/
theorem PB_eq_of_lines {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}
    {σ : Type} [Fintype σ] {S : PB.AnSys e σ} (Re Re' : PB.Realis S P) (hd : Re.deg = Re'.deg)
    (hl : ∀ a t, Re.line a t = Re'.line a t) (II : IntersectionSystem) : Re.PB II = Re'.PB II := by
  have : ∀ t w, Re.num II t w = Re'.num II t w := fun t w => by
    simp only [PB.Realis.num, hd, hl]
  refine congrArg (PB.formPoly (e + 1)) (funext fun w => ?_)
  simp only [PB.Realis.limNum, this]

/- English proof (translation)
Introduce `hG hW E _ _ _ H D l Xo c Y _ S Ω₀ _ ξ₀ hξ₀ hSp hSd hp hq`. Establish `hIn : PB.Inputs` using `hG.2.2.2.2.2.2.2.2.2.1`. Establish `hRes : ResK.ResKStatement` using `hG.2.2.2.2.1`. Establish `hβ : Function.Injective (algebraMap (𝓞 c.F) c.F)` using `RingOfIntegers.coe_injective`. Take `⟨Ω, _, _, K₀, _, J₀, _, x₀, 𝔐, dg, ⟨k₀⟩, hgen, hcov, harith, hsnc, hR, hom⟩` from `hBase hRes hW E H D l Xo c Y S Ω₀ ξ₀ hξ₀ hSp hSd`.

Rewrite `harith`, `hsnc` using `[← PB.card_mul_eq_dim D]`. Take `⟨⟨bW⟩, ⟨bO⟩⟩` from `PB.nonempty_bases 𝔐`. Take `⟨K, _, ι, _, Φ, _, y, M, 𝔐₁, tie, κ, v, φ, π, j, 𝔐', Fl, xdeg, e, ⟨-, -, -, -, hov, hR₁, -⟩, ⟨hcov₁, -, hsnc₁⟩, hv, htot, hFl⟩` from `GlobalTheory.T.flag_model_exists_of_given hG E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 _ dg bW bO harith hcov`. Take `⟨BM, hBM, hcj⟩` from `GlobalTheory.T.base_metric_exists_of_given hG E H D l Xo c Y S K ι Φ y M 𝔐₁ tie dg hp hq hcov₁ (hsnc₁ _ hsnc)`. Take `⟨-, hne, -⟩` from `GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers E H`.

Establish `hcard : 0 < Fintype.card (CMType H)` using `Fintype.card_pos_iff.2 hne`. Establish `hN : antisymDegree (CMType H) (D.p + D.q) = Fintype.card (CMType H) * D.p * D.q + Fintype.card (CMType H) * (D.p.choose 2 + D.q.choose 2)` using `by show Fintype.card (CMType H) * (D.p + D.q).choose 2 = _`. Rewrite using `[choose_two_add]`. Expand and normalize the polynomial expressions, which then agree. Establish `hdim : dimFl (CMType H) (D.p + D.q) = antisymDegree (CMType H) (D.p + D.q)`.

Simplify using `[dimFl, antisymDegree, Nat.choose_two_right]`. Choose the witnesses or unpack the hypotheses as in `⟨d, hd⟩ : ∃ d, d + 1 = antisymDegree (CMType H) (D.p + D.q) := by`. Use `⟨antisymDegree (CMType H) (D.p + D.q) - 1, Nat.sub_add_cancel ?_⟩` and prove the remaining obligations. Rewrite using `[hN]`. Use `Nat.mul_pos (Nat.mul_pos hcard hp) hq` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hv' : IsArithVar (mCoordIdeal y) (d + 2)`. Rewrite using `[show d + 2 = (d + 1) + 1 from rfl, hd, hN]`. Conclude with `hv`. Establish `hsub : D.p + D.q - D.p = D.q` using `by omega`.

Take `⟨FA, hFAc⟩` from `GlobalTheory.T.flagModel_arith_dimension_boundary hIn K ι Φ y (CMType H) (D.p + D.q) D.p M _ d BM hv' (by rw [hsub, hd, hN]) hcj.1 hcj.2`. Establish `hU` using `GlobalTheory.T.flag_analytic_data_uniformised K ι Φ y (CMType H) (D.p + D.q) D.p M _ d BM FA (by rw [hsub]) hd`. Take `⟨Cv, CR, hCv, -, hCRl⟩` from `GlobalTheory.T.flag_cover_degree_one_realisation K ι Φ y (CMType H) (D.p + D.q) D.p M _ d BM FA`. Establish `FS : Nonempty (PB.FlagSys CR.Re D.p)` using `⟨⟨M.j_le, hd, hU, fun τ a b hab hb => (GlobalTheory.T.flag_cover_realisation_pullback hIn K ι Φ y (CMType H) (D.p + D.q) D.p M _ d BM FA K ι Φ y M Cv CR hv' τ a b hab hb).some⟩⟩`. Take `⟨⟨pr, j', hov', hR', -⟩, hroots, hdy, -⟩` from `id htot`.

Use `choose sing hsd hho hsc using GlobalTheory.T.hodge_cpt_flag_xdeg E H D l Xo c _ _ Y S Φ K ι y 𝔐' Fl xdeg e hβ hroots`. Establish `hrd : ∀ a, ((FA.Re.comap some).ref a).a = (Top.combLine sing (Cmp.fundOnRoot a)).a` using `fun a => by show (FA.Re.ref (some a)).a = ∑ r, _ • (sing r).a`. Rewrite using `[FA.ref_some, RootFieldNumerics.Sq.sum_fundOnRoot]`. Simplify using `only [hsd]`. Conclude with `hdy a.1 a.2`.

Establish `hse : ∀ a x, (FA.Re.comap some).π x ∉ ReciprocityTheory.AnForm.P.bdry (FA.S.comap some).s → Real.log ((Top.combLine sing (Cmp.fundOnRoot a)).h ((FA.Re.comap some).R.lift x x)) = Real.log (((FA.Re.comap some).ref a).h ((FA.Re.comap some).R.lift x x)) + (FA.S.comap some).ph a ((FA. …` using `fun a x hx => by`. Establish `hx' : FA.Re.π x ∈ FA.S.open'` using `hx`. Use `Eq.trans ?_ (FA.hom_eq a x hx')` and prove the remaining obligations. Use `hSing E H D l Xo c Y S K ι Φ y M 𝔐₁ tie _ BM 𝔐' Fl xdeg e sing hBM htot hsd hho a _ (FA.Re.R.mem x x (FA.Re.R.mem_U x)) (FA.pr (FA.Re.π x)) (fun h => hx' ?_) (FA.pr_eq x)` and prove the remaining obligations. Use `show FA.S.s _ _ = 0`.

Rewrite using `[FA.s_eq]`. Conclude with `h`. Establish `halg` using `hAlg E H D l Xo c Y S K ι Φ y M 𝔐₁ tie _ d BM FA hBM`. Take `⟨x, hxa, hxs, hxc, hxl⟩` from `hX _ _ K ι _ _ (FA.S.comap some) (FA.Re.comap some) sing (FA.S.reg none).1 hrd fun a t => hFAc (some a) t`. Establish `hF : 0 < Module.finrank ℚ c.F` using `by haveI := c.fin; exact Module.finrank_pos`.

Establish `hFlpos : 0 < Fl.deg` using `by rw [hFl]; exact hcov.1`. Establish `hKne : Nonempty K` using `⟨(κ k₀).1⟩`. Take `⟨hbir, -⟩` from `GlobalTheory.T.hodge_cpt_birational_arith_var E H D l Xo c _ _ Y S Φ K ι y 𝔐' Fl hβ`. Establish `hovT` using `hov'.trans hov`. Establish `hht` using `hHt E H D l Xo c Y S Ω Φ K₀ K J₀ ι x₀ y 𝔐 𝔐' _ _ _ hovT (hR'.trans hR₁) hSd fun p hp => (hom p hp).2`.

Set `M' : RootModel (CMType H) (D.p + D.q)` to `{ K := K, «ι» := ι, Ω := Φ, y := y, arith := by rw [hdim, hN]; exact hv, birational := hbir, xdeg := xdeg, x := x, x_deg := fun t r => (hxa t r).trans (hsd r), x_smooth := hxs, x_conj := hxc, kA := 1, kA_pos := one_pos, A := trivLine ι, A_smooth := contDiffOn_const, A_conj := fun …`. Establish `key : ∀ (D' : ℕ) (_ : d + 1 = D'), ∃ (Sy' : PB.AnSys D' (CMType H × Fin (D.p + D.q))) (Re' : PB.Realis Sy' (mCoordIdeal y)), (FA.S.comap some).degPoly = Sy'.degPoly ∧ (∀ II, CR.Re.PB II = Re'.PB II) ∧ Cmp.AlgOver Re' ∧ Re'.deg = 1 ∧ (∀ r, (Re'.ref r).a = (Top.combLine sing (Cmp.f …`. Introduce `D' h`. Substitute `h` using the available equality. Conclude with `⟨_, FA.Re.comap some, rfl, PB_eq_of_lines _ _ ((CR.deg_eq.trans hCv).trans FA.deg_one.symm) hCRl, halg, FA.deg_one, hrd, hse, hxl⟩`.

Take `⟨Sy', Re', e1, e2, halg', hRd', hrd', hse', hxl'⟩` from `key _ (hd.trans hdim.symm)`. Apply the tactic sequence `let t : Cmp.HodgeTie Y S (Module.finrank ℚ c.F) M' := { A := 𝔐', Fl := Fl, e := e, roots := hroots, sing := sing, sing_deg := hsd, hodge := hho, Sy := Sy', Re := Re', alg := halg', ref_deg := by convert hrd', sing_eq := by convert hse', line_eq := by (convert hxl'); all_goals fir …`. Conclude with `⟨M', t, d, _, K, _, ι, _, _, CR.Re, (genPt_of_over hovT).trans hgen, fun p hp => by rw [← hR p hp, ← hR₁, ← hR'], hRd', hFlpos, e1, FS, e2⟩`.
-/
theorem tie_of (hX : StX) (hAlg : StAlg) (hHt : StHt) (hSing : StSing) (hBase : StBase) : StTie := by
  intro hG hW E _ _ _ H D l Xo c Y _ S Ω₀ _ ξ₀ hξ₀ hSp hSd hp hq
  have hIn : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  have hRes : ResK.ResKStatement := hG.2.2.2.2.1
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  obtain ⟨Ω, _, _, K₀, _, J₀, _, x₀, 𝔐, dg, ⟨k₀⟩, hgen, hcov, harith, hsnc, hR, hom⟩ :=
    hBase hRes hW E H D l Xo c Y S Ω₀ ξ₀ hξ₀ hSp hSd
  rw [← PB.card_mul_eq_dim D] at harith hsnc
  obtain ⟨⟨bW⟩, ⟨bO⟩⟩ := PB.nonempty_bases 𝔐
  obtain ⟨K, _, ι, _, Φ, _, y, M, 𝔐₁, tie, κ, v, φ, π, j, 𝔐', Fl, xdeg, e, ⟨-, -, -, -, hov, hR₁, -⟩,
    ⟨hcov₁, -, hsnc₁⟩, hv, htot, hFl⟩ := GlobalTheory.T.flag_model_exists_of_given hG E H D l Xo c Y S Ω K₀ J₀ x₀ 𝔐 _ dg bW bO harith hcov
  obtain ⟨BM, hBM, hcj⟩ := GlobalTheory.T.base_metric_exists_of_given hG E H D l Xo c Y S K ι Φ y M 𝔐₁ tie dg hp hq hcov₁ (hsnc₁ _ hsnc)
  obtain ⟨-, hne, -⟩ := GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers E H
  have hcard : 0 < Fintype.card (CMType H) := Fintype.card_pos_iff.2 hne
  have hN : antisymDegree (CMType H) (D.p + D.q) = Fintype.card (CMType H) * D.p * D.q +
      Fintype.card (CMType H) * (D.p.choose 2 + D.q.choose 2) := by
    show Fintype.card (CMType H) * (D.p + D.q).choose 2 = _
    rw [choose_two_add]; ring
  have hdim : dimFl (CMType H) (D.p + D.q) = antisymDegree (CMType H) (D.p + D.q) := by
    simp [dimFl, antisymDegree, Nat.choose_two_right]
  obtain ⟨d, hd⟩ : ∃ d, d + 1 = antisymDegree (CMType H) (D.p + D.q) := by
    refine ⟨antisymDegree (CMType H) (D.p + D.q) - 1, Nat.sub_add_cancel ?_⟩
    rw [hN]
    have := Nat.mul_pos (Nat.mul_pos hcard hp) hq
    omega
  have hv' : IsArithVar (mCoordIdeal y) (d + 2) := by
    rw [show d + 2 = (d + 1) + 1 from rfl, hd, hN]; exact hv
  have hsub : D.p + D.q - D.p = D.q := by omega
  obtain ⟨FA, hFAc⟩ := GlobalTheory.T.flagModel_arith_dimension_boundary hIn K ι Φ y (CMType H) (D.p + D.q) D.p M _ d BM hv' (by rw [hsub, hd, hN])
    hcj.1 hcj.2
  have hU := GlobalTheory.T.flag_analytic_data_uniformised K ι Φ y (CMType H) (D.p + D.q) D.p M _ d BM FA (by rw [hsub]) hd
  obtain ⟨Cv, CR, hCv, -, hCRl⟩ := GlobalTheory.T.flag_cover_degree_one_realisation K ι Φ y (CMType H) (D.p + D.q) D.p M _ d BM FA
  have FS : Nonempty (PB.FlagSys CR.Re D.p) := ⟨⟨M.j_le, hd, hU, fun τ a b hab hb =>
    (GlobalTheory.T.flag_cover_realisation_pullback hIn K ι Φ y (CMType H) (D.p + D.q) D.p M _ d BM FA K ι Φ y M Cv CR hv' τ a b hab hb).some⟩⟩
  obtain ⟨⟨pr, j', hov', hR', -⟩, hroots, hdy, -⟩ := id htot
  choose sing hsd hho hsc using GlobalTheory.T.hodge_cpt_flag_xdeg E H D l Xo c _ _ Y S Φ K ι y 𝔐' Fl xdeg e hβ hroots
  have hrd : ∀ a, ((FA.Re.comap some).ref a).a = (Top.combLine sing (Cmp.fundOnRoot a)).a := fun a => by
    show (FA.Re.ref (some a)).a = ∑ r, _ • (sing r).a
    rw [FA.ref_some, RootFieldNumerics.Sq.sum_fundOnRoot]
    simp only [hsd]
    exact hdy a.1 a.2
  have hse : ∀ a x, (FA.Re.comap some).π x ∉ ReciprocityTheory.AnForm.P.bdry (FA.S.comap some).s →
      Real.log ((Top.combLine sing (Cmp.fundOnRoot a)).h ((FA.Re.comap some).R.lift x x)) =
        Real.log (((FA.Re.comap some).ref a).h ((FA.Re.comap some).R.lift x x)) +
          (FA.S.comap some).ph a ((FA.Re.comap some).π x) := fun a x hx => by
    have hx' : FA.Re.π x ∈ FA.S.open' := hx
    refine Eq.trans ?_ (FA.hom_eq a x hx')
    refine hSing E H D l Xo c Y S K ι Φ y M 𝔐₁ tie _ BM 𝔐' Fl xdeg e sing hBM htot hsd hho a _
      (FA.Re.R.mem x x (FA.Re.R.mem_U x)) (FA.pr (FA.Re.π x)) (fun h => hx' ?_) (FA.pr_eq x)
    show FA.S.s _ _ = 0
    rw [FA.s_eq]
    exact h
  have halg := hAlg E H D l Xo c Y S K ι Φ y M 𝔐₁ tie _ d BM FA hBM
  obtain ⟨x, hxa, hxs, hxc, hxl⟩ := hX _ _ K ι _ _ (FA.S.comap some) (FA.Re.comap some) sing (FA.S.reg none).1 hrd
    fun a t => hFAc (some a) t
  have hF : 0 < Module.finrank ℚ c.F := by haveI := c.fin; exact Module.finrank_pos
  have hFlpos : 0 < Fl.deg := by rw [hFl]; exact hcov.1
  have hKne : Nonempty K := ⟨(κ k₀).1⟩
  obtain ⟨hbir, -⟩ := GlobalTheory.T.hodge_cpt_birational_arith_var E H D l Xo c _ _ Y S Φ K ι y 𝔐' Fl hβ
  have hovT := hov'.trans hov
  have hht := hHt E H D l Xo c Y S Ω Φ K₀ K J₀ ι x₀ y 𝔐 𝔐' _ _ _ hovT (hR'.trans hR₁) hSd fun p hp => (hom p hp).2
  let M' : RootModel (CMType H) (D.p + D.q) :=
    { K := K, «ι» := ι, Ω := Φ, y := y, arith := by rw [hdim, hN]; exact hv, birational := hbir, xdeg := xdeg, x := x,
      x_deg := fun t r => (hxa t r).trans (hsd r), x_smooth := hxs, x_conj := hxc, kA := 1, kA_pos := one_pos,
      A := trivLine ι, A_smooth := contDiffOn_const, A_conj := fun _ => rfl,
      δ := Module.finrank ℚ c.F * Fl.deg, δ_pos := Nat.mul_pos hF hFlpos }
  have key : ∀ (D' : ℕ) (_ : d + 1 = D'), ∃ (Sy' : PB.AnSys D' (CMType H × Fin (D.p + D.q)))
      (Re' : PB.Realis Sy' (mCoordIdeal y)), (FA.S.comap some).degPoly = Sy'.degPoly ∧
      (∀ II, CR.Re.PB II = Re'.PB II) ∧ Cmp.AlgOver Re' ∧ Re'.deg = 1 ∧
      (∀ r, (Re'.ref r).a = (Top.combLine sing (Cmp.fundOnRoot r)).a) ∧
      (∀ r x, Re'.π x ∉ ReciprocityTheory.AnForm.P.bdry Sy'.s → Real.log ((Top.combLine sing (Cmp.fundOnRoot r)).h
        (Re'.R.lift x x)) = Real.log ((Re'.ref r).h (Re'.R.lift x x)) + Sy'.ph r (Re'.π x)) ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ r, ∀ z ∈ mcPts (mCoordIdeal y),
        (x t r).h z = (Top.combLine (fun a => Re'.line a t) (Cmp.rootOnFund r)).h z := by
    intro D' h
    subst h
    exact ⟨_, FA.Re.comap some, rfl, PB_eq_of_lines _ _ ((CR.deg_eq.trans hCv).trans FA.deg_one.symm) hCRl, halg,
      FA.deg_one, hrd, hse, hxl⟩
  obtain ⟨Sy', Re', e1, e2, halg', hRd', hrd', hse', hxl'⟩ := key _ (hd.trans hdim.symm)
  let t : Cmp.HodgeTie Y S (Module.finrank ℚ c.F) M' :=
    { A := 𝔐', Fl := Fl, e := e, roots := hroots, sing := sing, sing_deg := hsd, hodge := hho,
      Sy := Sy', Re := Re', alg := halg', ref_deg := by convert hrd', sing_eq := by convert hse',
      line_eq := by (convert hxl'); all_goals first | rfl | exact Subsingleton.elim _ _,
      δ_eq := rfl, discr := hSd, ht_vb := hht }
  exact ⟨M', t, d, _, K, _, ι, _, _, CR.Re, (genPt_of_over hovT).trans hgen,
    fun p hp => by rw [← hR p hp, ← hR₁, ← hR'], hRd', hFlpos, e1, FS, e2⟩

end SquareStatements
