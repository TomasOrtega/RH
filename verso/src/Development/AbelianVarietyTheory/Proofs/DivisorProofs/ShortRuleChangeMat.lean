import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ShortRuleChangeOfCongr
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAdaptedCongr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumsSpan
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.OrbitAdapt

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence GlobalTheory.ShortMove

/- English proof (translation)
Use `set d := T.dδ j n with hd`. Take `⟨_, hnab⟩` from `hF.sh.dNab j hj n`. Establish `hCI` using `GlobalTheory.T.harmonic_germ_value_chart_independent`. Establish `hbad` using `GlobalTheory.ShortChange.badOK_host D T.Q.H d.l₂`. Establish `hdv : D.host.QS * D.host.q * D.host.d ∣ badN D` using `Dvd.intro _ rfl`.

Establish `hb1 : D.host.QS * D.host.q * D.host.d * d.l₂.M ≠ 1` using `fun h => by`. Use `hbad.2.1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hB` using `GlobalTheory.ShortChange.trivAt_mul (trivAt_of_dvd hdv hT) hM`. Establish `hB'` using `GlobalTheory.ShortChange.trivAt_mul (trivAt_of_dvd hdv hT') hM'`.

Establish `hK` using `hF.p.kPsi j hj`. Take `⟨ze, ⟨k, hk, hze⟩, hrep⟩` from `GlobalTheory.T.thetaChangeOfRepRootOfUnity_of_chartIndependence hCI D.host.E T.Q.H (T.Q.Dw j) d.l₂ d.Xo₂ d.c₂ d.nab₂ n ⟨(GlobalTheory.PlaceInt.host_galois_discr_moves D T.Q.H).1, GlobalTheory.ShortChange.odd_rank T hF j hj, hev, hnab⟩ _ hbad Λ g _ _ hU hg hB hB' (isBeta_cover d h …`. Establish `hP'` using `((GlobalTheory.PushKeeps.push_keeps D.host.E T.Q.H (T.Q.Dw j) T.Q.l T.Q.c n a g hg).2 Λ).2.2.2 P hP`. Establish `hz : d.eF.symm ze ^ k = 1` using `by rw [← map_pow, hze, map_one]`. Use `⟨pushLet T.Q.c g P, d.eF.symm ze, hP', fun h0 => ?_, ⟨k, hk, hz⟩, fun x0 N N' f hN hN' hR K _ _ _ _ hKe y y₂ hy => ?_⟩` and prove the remaining obligations.

Rewrite `hz` using `[h0, zero_pow hk.ne']`. Conclude with `zero_ne_one hz`. Take `⟨v, hv, hval⟩` from `hR K hKe y y₂ hy`. Establish `h₂` using `(((GlobalTheory.PlaceInt.eF_transfer D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c n d Λ).2.1 a P hP).1)`. Establish `h₂'` using `(((GlobalTheory.PlaceInt.eF_transfer D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c n d _).2.1 a _ hP').1)`.

Take `⟨v', hv', -⟩` from `(GlobalTheory.shortThetaValue_existsUnique_natural GlobalTheory.firstFiveLaws.1 hCI D.host.E T.Q.H (T.Q.Dw j) d.l₂ d.Xo₂ d.c₂ d.nab₂ hnab n _ N' hU' hM' hN' a _ h₂'.1 (d.w x0) (d.eF (betaH (Dw := T.Q.Dw j) T.Q.c (actLat g Λ)))).1 K y₂`. Use `⟨v', hv', ?_⟩` and prove the remaining obligations. Rewrite `hv'` using `[map_pushLet]`. Establish `hvv` using `hrep (d.w x0) (fixesDatum_of_congAt d.c₂ hb hcg _) N N' hN hN' a _ h₂ K y₂ v v' hv hv'`. Establish `hs : evR (T.Q.Xo j) T.Q.c (d.eF.symm ze • f) y = algebraMap T.Q.c.F K (d.eF.symm ze) * evR (T.Q.Xo j) T.Q.c f y` using `evR_mul (T.Q.Xo j) T.Q.c _ f _ (fun p y => Algebra.smul_def _ _) y`.

Rewrite using `[hs, hval, hvv, ← hKe, AlgEquiv.apply_symm_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem shortRule_change_mat (D : D7) (T : Full D) (hF : LawsFull T) (j : ℕ) (hj : InR D j) (n : ℕ)
    (Λ : GenLat D.host.E n) (g : Matrix (Fin n) (Fin n) D.host.E) (b : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F) (hg : IsUnitaryM g) (hb : (T.dδ j n).l₂.M ∣ b)
    (hcg : GlobalTheory.UnRep.CongAt (stdLat D.host.E n) b b g)
    (hev : Even n) (hU : Λ.Unimod) (hU' : (actLat g Λ).Unimod) (hT : Λ.TrivAt (badN D))
    (hT' : (actLat g Λ).TrivAt (badN D)) (hM : Λ.TrivAt (T.dδ j n).l₂.M) (hM' : (actLat g Λ).TrivAt (T.dδ j n).l₂.M)
    (hP : P ∈ harmL T.Q.c Λ a) :
    ∃ (P' : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F) (ζ : T.Q.c.F), P' ∈ harmL T.Q.c (actLat g Λ) a ∧ ζ ≠ 0 ∧
      (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧
      ∀ (x0 : Fin n → (T.Q.Dw j).La) (N N' : ℕ) (f : Rul (T.Q.Xo j) T.Q.c),
        Λ.LevOK N (T.dδ j n).l₂.M → (actLat g Λ).LevOK N' (T.dδ j n).l₂.M →
        IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j n) Λ N x0 P f →
        IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j n) (actLat g Λ) N' x0 P' (ζ • f) := by
  set d := T.dδ j n with hd
  obtain ⟨_, hnab⟩ := hF.sh.dNab j hj n
  have hCI := GlobalTheory.T.harmonic_germ_value_chart_independent
  have hbad := GlobalTheory.ShortChange.badOK_host D T.Q.H d.l₂
  have hdv : D.host.QS * D.host.q * D.host.d ∣ badN D := Dvd.intro _ rfl
  have hb1 : D.host.QS * D.host.q * D.host.d * d.l₂.M ≠ 1 := fun h => by
    have := hbad.2.1
    omega
  have hB := GlobalTheory.ShortChange.trivAt_mul (trivAt_of_dvd hdv hT) hM
  have hB' := GlobalTheory.ShortChange.trivAt_mul (trivAt_of_dvd hdv hT') hM'
  have hK := hF.p.kPsi j hj
  obtain ⟨ze, ⟨k, hk, hze⟩, hrep⟩ := GlobalTheory.T.thetaChangeOfRepRootOfUnity_of_chartIndependence hCI D.host.E T.Q.H (T.Q.Dw j) d.l₂ d.Xo₂ d.c₂ d.nab₂ n
    ⟨(GlobalTheory.PlaceInt.host_galois_discr_moves D T.Q.H).1, GlobalTheory.ShortChange.odd_rank T hF j hj, hev, hnab⟩ _ hbad
    Λ g _ _ hU hg hB hB' (isBeta_cover d hK hb1 Λ hU hB) (isBeta_cover d hK hb1 _ hU' hB')
  have hP' := ((GlobalTheory.PushKeeps.push_keeps D.host.E T.Q.H (T.Q.Dw j) T.Q.l T.Q.c n a g hg).2 Λ).2.2.2 P hP
  have hz : d.eF.symm ze ^ k = 1 := by rw [← map_pow, hze, map_one]
  refine ⟨pushLet T.Q.c g P, d.eF.symm ze, hP', fun h0 => ?_, ⟨k, hk, hz⟩,
    fun x0 N N' f hN hN' hR K _ _ _ _ hKe y y₂ hy => ?_⟩
  · rw [h0, zero_pow hk.ne'] at hz
    exact zero_ne_one hz
  obtain ⟨v, hv, hval⟩ := hR K hKe y y₂ hy
  have h₂ := (((GlobalTheory.PlaceInt.eF_transfer D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c n d Λ).2.1 a P hP).1)
  have h₂' := (((GlobalTheory.PlaceInt.eF_transfer D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c n d _).2.1 a _ hP').1)
  obtain ⟨v', hv', -⟩ := (GlobalTheory.shortThetaValue_existsUnique_natural GlobalTheory.firstFiveLaws.1 hCI D.host.E T.Q.H (T.Q.Dw j)
    d.l₂ d.Xo₂ d.c₂ d.nab₂ hnab n _ N' hU' hM' hN' a _ h₂'.1 (d.w x0)
    (d.eF (betaH (Dw := T.Q.Dw j) T.Q.c (actLat g Λ)))).1 K y₂
  refine ⟨v', hv', ?_⟩
  rw [map_pushLet] at hv'
  have hvv := hrep (d.w x0) (fixesDatum_of_congAt d.c₂ hb hcg _) N N' hN hN' a _ h₂ K y₂ v v' hv hv'
  have hs : evR (T.Q.Xo j) T.Q.c (d.eF.symm ze • f) y =
      algebraMap T.Q.c.F K (d.eF.symm ze) * evR (T.Q.Xo j) T.Q.c f y :=
    evR_mul (T.Q.Xo j) T.Q.c _ f _ (fun p y => Algebra.smul_def _ _) y
  rw [hs, hval, hvv, ← hKe, AlgEquiv.apply_symm_apply]
  ring

/- English proof (translation)
Use `choose k hk b hb using h`. Use `⟨∏ j, k j, Nat.Coprime.prod_left fun j _ => hk j, fun v hv => ?_⟩` and prove the remaining obligations. Establish `hv' : ∀ i, ∃ y : 𝓞 E, (y : E) = v i` using `fun i => by`. Use `(Submodule.mem_pi.1 hv) i (Set.mem_univ _)` as an intermediate fact. Take `⟨y, hy⟩` from `Submodule.mem_one.1 this`.

Conclude with `⟨y, hy⟩`. Use `choose y hy using hv'`. Use `⟨fun i => ((∑ j, ((∏ l ∈ Finset.univ.erase j, k l : ℕ) : 𝓞 E) * b j i * y j : 𝓞 E) : E), ?_, ?_⟩` and prove the remaining obligations. Use `Submodule.mem_pi.2 fun i _ => Submodule.mem_one.2 ⟨_, rfl⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Establish `e1 : ∀ j, ((∏ l, k l : ℕ) : E) * (gm i j - (((1 : Matrix (Fin n) (Fin n) (𝓞 E)) i j : 𝓞 E) : E)) = ((∏ l ∈ Finset.univ.erase j, k l : ℕ) : E) * ((m : E) * (b j i : E))` using `fun j => by`. Establish `hp : (∏ l, k l) = k j * ∏ l ∈ Finset.univ.erase j, k l` using `(Finset.mul_prod_erase (s := Finset.univ) (f := k) (Finset.mem_univ j)).symm`. Rewrite using `[hp]`. Use `push_cast`. Establish `h'` using `hb j i`.

Simplify using `only at h'`. Take the linear combination `(∏ l ∈ Finset.univ.erase j, ((k l : ℕ) : E)) * h'`. Establish `e2 : (gm.mulVec v - v) i = ∑ j, (gm i j - (((1 : Matrix (Fin n) (Fin n) (𝓞 E)) i j : 𝓞 E) : E)) * v j`. Simplify using `only [Pi.sub_apply, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]`. Use `congr 1`.

Simplify using `[Matrix.one_apply]`. Simplify using `only [Pi.smul_apply, nsmul_eq_mul, e2]`. Use `push_cast`. Rewrite using `[Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[← hy j]`. Establish `h'` using `e1 j`. Move the coercions through the operations in `at h'`. Take the linear combination `((y j : 𝓞 E) : E) * h'`.
-/
theorem congAt_of_cols {E : Type} [Field E] [NumberField E] {n : ℕ} (gm : Matrix (Fin n) (Fin n) E) (m : ℕ)
    (h : ∀ j : Fin n, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.CongAt m (fun i => gm i j)
      fun i => (((1 : Matrix (Fin n) (Fin n) (𝓞 E)) i j : 𝓞 E) : E)) :
    GlobalTheory.UnRep.CongAt (stdLat E n) m m gm := by
  choose k hk b hb using h
  refine ⟨∏ j, k j, Nat.Coprime.prod_left fun j _ => hk j, fun v hv => ?_⟩
  have hv' : ∀ i, ∃ y : 𝓞 E, (y : E) = v i := fun i => by
    have := (Submodule.mem_pi.1 hv) i (Set.mem_univ _)
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 this
    exact ⟨y, hy⟩
  choose y hy using hv'
  refine ⟨fun i => ((∑ j, ((∏ l ∈ Finset.univ.erase j, k l : ℕ) : 𝓞 E) * b j i * y j : 𝓞 E) : E), ?_, ?_⟩
  · refine Submodule.mem_pi.2 fun i _ => Submodule.mem_one.2 ⟨_, rfl⟩
  · funext i
    have e1 : ∀ j, ((∏ l, k l : ℕ) : E) * (gm i j - (((1 : Matrix (Fin n) (Fin n) (𝓞 E)) i j : 𝓞 E) : E)) =
        ((∏ l ∈ Finset.univ.erase j, k l : ℕ) : E) * ((m : E) * (b j i : E)) := fun j => by
      have hp : (∏ l, k l) = k j * ∏ l ∈ Finset.univ.erase j, k l :=
        (Finset.mul_prod_erase (s := Finset.univ) (f := k) (Finset.mem_univ j)).symm
      rw [hp]
      push_cast
      have h' := hb j i
      simp only at h'
      linear_combination (∏ l ∈ Finset.univ.erase j, ((k l : ℕ) : E)) * h'
    have e2 : (gm.mulVec v - v) i = ∑ j, (gm i j - (((1 : Matrix (Fin n) (Fin n) (𝓞 E)) i j : 𝓞 E) : E)) * v j := by
      simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]
      congr 1
      simp [Matrix.one_apply]
    simp only [Pi.smul_apply, nsmul_eq_mul, e2]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hy j]
    have h' := e1 j
    push_cast at h'
    linear_combination ((y j : 𝓞 E) : E) * h'

/- English proof (translation)
Unfold `Formalism.EigenvalueLevelCeiling.plc`. Use `haveI : lam.asIdeal.IsPrime := lam.isPrime`. Establish `hne : Ideal.absNorm lam.asIdeal ≠ 0` using `fun h => lam.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)`. Establish `hz : ((Ideal.absNorm lam.asIdeal : ℕ) : 𝓞 K ⧸ lam.asIdeal) = 0`. Rewrite using `[← map_natCast (Ideal.Quotient.mk lam.asIdeal), Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `Ideal.absNorm_mem _`. Establish `hd : ringChar (𝓞 K ⧸ lam.asIdeal) ∣ Ideal.absNorm lam.asIdeal` using `(ringChar.spec (𝓞 K ⧸ lam.asIdeal) _).1 hz`. Break down `CharP.char_is_prime_or_zero (𝓞 K ⧸ lam.asIdeal) (ringChar (𝓞 K ⧸ lam.asIdeal)) with h | h` into its components or cases. Conclude with `h`. Rewrite `hd` using `[h, zero_dvd_iff]`.

Conclude with `absurd hd hne`.
-/
theorem plc_prime {K : Type} [Field K] [NumberField K] (lam : HeightOneSpectrum (𝓞 K)) : (Formalism.EigenvalueLevelCeiling.plc lam).Prime := by
  unfold Formalism.EigenvalueLevelCeiling.plc
  haveI : lam.asIdeal.IsPrime := lam.isPrime
  have hne : Ideal.absNorm lam.asIdeal ≠ 0 := fun h => lam.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hz : ((Ideal.absNorm lam.asIdeal : ℕ) : 𝓞 K ⧸ lam.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk lam.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.absNorm_mem _
  have hd : ringChar (𝓞 K ⧸ lam.asIdeal) ∣ Ideal.absNorm lam.asIdeal :=
    (ringChar.spec (𝓞 K ⧸ lam.asIdeal) _).1 hz
  rcases CharP.char_is_prime_or_zero (𝓞 K ⧸ lam.asIdeal) (ringChar (𝓞 K ⧸ lam.asIdeal)) with h | h
  · exact h
  · rw [h, zero_dvd_iff] at hd
    exact absurd hd hne

attribute [local instance] Formalism.BasicNotions.Host.cmStar in

/- English proof (translation)
Establish `hM0 : 0 < (T.dδ j V.rank).l₂.M` using `by have := (T.dδ j V.rank).l₂.three_le; omega`. Establish `hpos : 0 < badN D * p * (T.dδ j V.rank).l₂.M` using `Nat.mul_pos (Nat.mul_pos hb hp) hM0`. Establish `hT' : Λ.TrivAt (badN D * p * (T.dδ j V.rank).l₂.M)`. Rewrite using `[show badN D * p * (T.dδ j V.rank).l₂.M = badN D * (T.dδ j V.rank).l₂.M * p by ring]` and apply the resulting hypothesis. Take `⟨gm, h, hgm, hc, hh, hs, e⟩` from `GlobalTheory.T.exists_rationalUnitary_move_selfDual_to_split D V hg hL T.Q.H _ hpos Λ hU hT'`.

Establish `h2 : 2 ∣ badN D * p`. Unfold `badN`. Conclude with `dvd_mul_of_dvd_left (((((dvd_pow_self 2 (by omega)).trans D.host.tower_dvd : 2 ∣ D.host.QS).mul_right _).mul_right _).mul_right _) p`. Take `⟨N', c1, c2, c3, c4, -⟩` from `GlobalTheory.SplitReps.exists_conjLat V hg hL T.Q.H (T.dδ j V.rank).l₂ (badN D * p) h2 h hs`. Rewrite `c1`, `c2`, `c3`, `c4` using `[← e]`.

Establish `hcg` using `congAt_of_cols gm _ hc`. Establish `hTb : Λ.TrivAt (badN D)` using `trivAt_of_dvd ⟨(T.dδ j V.rank).l₂.M * p, by ring⟩ hT`. Establish `hTM : Λ.TrivAt (T.dδ j V.rank).l₂.M` using `trivAt_of_dvd ⟨badN D * p, by ring⟩ hT`. Take `⟨P', ζ, hP', hζ, hroot, hR⟩` from `shortRule_change_mat D T hF j hj V.rank Λ gm _ a P hgm (dvd_mul_left _ _) hcg hev hU c1 hTb (trivAt_of_dvd (dvd_mul_right _ _) c2) hTM c3 hP`. Establish `hsp : Formalism.IndefR.FWT.SplitOffBad V (badN D * p * (T.dδ j V.rank).l₂.M) h` using `GlobalTheory.SplitReps.splitOffBad_of_suppSplit V _ h hh hs`.

Use `⟨h, actLat gm Λ, N', P', ζ, ?_, fun w => by rw [e]; rfl, c1, trivAt_of_dvd (dvd_mul_right _ _) c2, c3, trivAt_of_dvd (dvd_mul_left _ _) c2, c4, hP', hζ, hroot, fun x0 f hf => hR x0 N N' f hN c4 hf⟩` and prove the remaining obligations. Take `⟨h1, e', Q, h3, h4, h5⟩` from `hsp`. Use `⟨h1, e', Q, h3, fun PP hP hbd => h4 PP hP ?_, h5⟩` and prove the remaining obligations. Rewrite using `[show badN D * p * (T.dδ j V.rank).l₂.M = badN D * (T.dδ j V.rank).l₂.M * p by ring, Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ hbd`.
-/
theorem exists_step_split (D : D7) (T : Full D) (hF : LawsFull T) (j : ℕ) (hj : InR D j) (V : Formalism.BasicNotions.TH.HSp D)
    (hg : V.gram = 1) (hL : Formalism.IndefR.Bridge.hLat V 1 = stdLat D.host.E V.rank) (hev : Even V.rank) (hb : 0 < badN D)
    (p : ℕ) (hp : 0 < p) (Λ : GenLat D.host.E V.rank) (N : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN (T.Q.Dw j) V.rank) T.Q.c.F) (hU : Λ.Unimod)
    (hT : Λ.TrivAt (badN D * (T.dδ j V.rank).l₂.M * p)) (hN : Λ.LevOK N (T.dδ j V.rank).l₂.M)
    (hP : P ∈ harmL T.Q.c Λ a) :
    ∃ (h : Formalism.L2.Theta.GA D V) (Λ' : GenLat D.host.E V.rank) (N' : ℕ)
      (P' : MvPolynomial (LtN (T.Q.Dw j) V.rank) T.Q.c.F) (ζ : T.Q.c.F),
      Formalism.IndefR.FWT.SplitOffBad V (badN D * (T.dδ j V.rank).l₂.M) h ∧
      (∀ w, w ∈ Λ'.La ↔ (fun b => star (w b)) ∈ Formalism.IndefR.Bridge.hLat V (Formalism.IndefR.FWT.fin V h)) ∧
      Λ'.Unimod ∧ Λ'.TrivAt (badN D) ∧ Λ'.TrivAt (T.dδ j V.rank).l₂.M ∧ Λ'.TrivAt p ∧
      Λ'.LevOK N' (T.dδ j V.rank).l₂.M ∧ P' ∈ harmL T.Q.c Λ' a ∧ ζ ≠ 0 ∧ (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧
      ∀ (x0 : Fin V.rank → (T.Q.Dw j).La) (f : Rul (T.Q.Xo j) T.Q.c),
        IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j V.rank) Λ N x0 P f →
        IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j V.rank) Λ' N' x0 P' (ζ • f) := by
  have hM0 : 0 < (T.dδ j V.rank).l₂.M := by have := (T.dδ j V.rank).l₂.three_le; omega
  have hpos : 0 < badN D * p * (T.dδ j V.rank).l₂.M := Nat.mul_pos (Nat.mul_pos hb hp) hM0
  have hT' : Λ.TrivAt (badN D * p * (T.dδ j V.rank).l₂.M) := by
    rwa [show badN D * p * (T.dδ j V.rank).l₂.M = badN D * (T.dδ j V.rank).l₂.M * p by ring]
  obtain ⟨gm, h, hgm, hc, hh, hs, e⟩ := GlobalTheory.T.exists_rationalUnitary_move_selfDual_to_split D V hg hL T.Q.H _ hpos Λ hU hT'
  have h2 : 2 ∣ badN D * p := by
    unfold badN
    exact dvd_mul_of_dvd_left (((((dvd_pow_self 2 (by omega)).trans D.host.tower_dvd : 2 ∣ D.host.QS).mul_right _).mul_right _).mul_right _) p
  obtain ⟨N', c1, c2, c3, c4, -⟩ := GlobalTheory.SplitReps.exists_conjLat V hg hL T.Q.H (T.dδ j V.rank).l₂ (badN D * p) h2 h hs
  rw [← e] at c1 c2 c3 c4
  have hcg := congAt_of_cols gm _ hc
  have hTb : Λ.TrivAt (badN D) := trivAt_of_dvd ⟨(T.dδ j V.rank).l₂.M * p, by ring⟩ hT
  have hTM : Λ.TrivAt (T.dδ j V.rank).l₂.M := trivAt_of_dvd ⟨badN D * p, by ring⟩ hT
  obtain ⟨P', ζ, hP', hζ, hroot, hR⟩ := shortRule_change_mat D T hF j hj V.rank Λ gm _ a P hgm
    (dvd_mul_left _ _) hcg hev hU c1 hTb (trivAt_of_dvd (dvd_mul_right _ _) c2) hTM c3 hP
  have hsp : Formalism.IndefR.FWT.SplitOffBad V (badN D * p * (T.dδ j V.rank).l₂.M) h :=
    GlobalTheory.SplitReps.splitOffBad_of_suppSplit V _ h hh hs
  refine ⟨h, actLat gm Λ, N', P', ζ, ?_, fun w => by rw [e]; rfl, c1, trivAt_of_dvd (dvd_mul_right _ _) c2, c3,
    trivAt_of_dvd (dvd_mul_left _ _) c2, c4, hP', hζ, hroot, fun x0 f hf => hR x0 N N' f hN c4 hf⟩
  obtain ⟨h1, e', Q, h3, h4, h5⟩ := hsp
  refine ⟨h1, e', Q, h3, fun PP hP hbd => h4 PP hP ?_, h5⟩
  rw [show badN D * p * (T.dδ j V.rank).l₂.M = badN D * (T.dδ j V.rank).l₂.M * p by ring, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hbd

attribute [local instance] Formalism.BasicNotions.Host.cmStar in

/- English proof (translation)
Take `⟨y, rfl⟩` from `Submodule.mem_one.1 hx`. Conclude with `Submodule.mem_one.2 ⟨⟨star (algebraMap _ _ y), (RingOfIntegers.isIntegral_coe y).map (starRingEnd D.host.E).toIntAlgHom⟩, rfl⟩`.
-/
theorem star_mem_one (D : D7) {x : D.host.E} (hx : x ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) :
    star x ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  obtain ⟨y, rfl⟩ := Submodule.mem_one.1 hx
  exact Submodule.mem_one.2 ⟨⟨star (algebraMap _ _ y),
    (RingOfIntegers.isIntegral_coe y).map (starRingEnd D.host.E).toIntAlgHom⟩, rfl⟩

attribute [local instance] Formalism.BasicNotions.Host.cmStar in

/- English proof (translation)
Take `⟨k, hk, h1, h2⟩` from `hT`. Take `rfl : k = 1` from `(Nat.coprime_zero_right k).1 hk`. Simplify using `only [Nat.cast_one, Ideal.span_singleton_one, Submodule.top_smul] at h1 h2`. Establish `hΛ : Λ.La = stdLat D.host.E V.rank` using `le_antisymm h1 h2`. Use `⟨fun w => ?_, fun b => ?_, fun m => ⟨1, Nat.coprime_one_left m, by simpa using h1, by simpa using h2⟩⟩` and prove the remaining obligations.

Establish `hf : Formalism.IndefR.FWT.fin V (1 : Formalism.L2.Theta.GA D V) = 1` using `map_one _`. Rewrite using `[hf, hL, hΛ]`. Prove the components needed by the constructor for the conclusion. Introduce `hw`. Conclude with `Submodule.mem_pi.2 fun i _ => star_mem_one D ((Submodule.mem_pi.1 hw) i (Set.mem_univ _))`.

Introduce `hw`. Use `Submodule.mem_pi.2 fun i _ => ?_` and prove the remaining obligations. Use `star_mem_one D ((Submodule.mem_pi.1 hw) i (Set.mem_univ _))` as an intermediate fact. Simplify `this` using `only [star_star]`. Use `⟨one_mem _, 0, ∅, ⟨⟨fun _ => 0, by simp, by simp⟩, by simp⟩, by simp, fun a c => ?_⟩` and prove the remaining obligations.

Establish `: Formalism.L2.Theta.mt V (1 : Formalism.L2.Theta.GA D V) = 1` using `by simp [Formalism.L2.Theta.mt]`. Simplify using `[this]`.
-/
theorem zero_case (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (hL : Formalism.IndefR.Bridge.hLat V 1 = stdLat D.host.E V.rank)
    (Λ : GenLat D.host.E V.rank) (hT : Λ.TrivAt 0) :
    (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Formalism.IndefR.Bridge.hLat V (Formalism.IndefR.FWT.fin V 1)) ∧
      (∀ b, Formalism.IndefR.FWT.SplitOffBad V b 1) ∧ ∀ m, Λ.TrivAt m := by
  obtain ⟨k, hk, h1, h2⟩ := hT
  obtain rfl : k = 1 := (Nat.coprime_zero_right k).1 hk
  simp only [Nat.cast_one, Ideal.span_singleton_one, Submodule.top_smul] at h1 h2
  have hΛ : Λ.La = stdLat D.host.E V.rank := le_antisymm h1 h2
  refine ⟨fun w => ?_, fun b => ?_, fun m => ⟨1, Nat.coprime_one_left m, by simpa using h1, by simpa using h2⟩⟩
  · have hf : Formalism.IndefR.FWT.fin V (1 : Formalism.L2.Theta.GA D V) = 1 := map_one _
    rw [hf, hL, hΛ]
    constructor
    · intro hw
      exact Submodule.mem_pi.2 fun i _ => star_mem_one D ((Submodule.mem_pi.1 hw) i (Set.mem_univ _))
    · intro hw
      refine Submodule.mem_pi.2 fun i _ => ?_
      have := star_mem_one D ((Submodule.mem_pi.1 hw) i (Set.mem_univ _))
      simpa only [star_star] using this
  · refine ⟨one_mem _, 0, ∅, ⟨⟨fun _ => 0, by simp, by simp⟩, by simp⟩, by simp, fun a c => ?_⟩
    have : Formalism.L2.Theta.mt V (1 : Formalism.L2.Theta.GA D V) = 1 := by simp [Formalism.L2.Theta.mt]
    simp [this]

end GlobalTheory.OrbitAdapt
