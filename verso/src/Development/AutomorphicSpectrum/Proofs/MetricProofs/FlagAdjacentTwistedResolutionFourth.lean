import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LowerUnipotentFamilyAnalytic
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticProjectionBijective
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseVectorProperties
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsUpperOfMinors
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsParabolicTransvection
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentPluckerOrbit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PluckerNonvanishingOrbitInvariant
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PlkFlagPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPointTriangularChangeOrbit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentArithVarietySecondStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.Cell

section Orbits

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `h`. Conclude with `⟨fun k => c k.1, fun k => hc k.1, rfl⟩`.
-/
theorem orbit_basePart {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `h`. Conclude with `⟨fun k => c (some k), fun k => hc _, rfl⟩`.
-/
theorem orbit_fstPt {k₀ : K} {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (fstPt k₀ z) (fstPt k₀ z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c (some k), fun k => hc _, rfl⟩

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `h`. Use `⟨fun k => if k = k₀ then c none else c (some k), fun k => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only split_ifs exacts [hc _, hc _]`. Use function extensionality and compare the values at `p`. Take `⟨k, m⟩` from `p`.

Distinguish the cases in `hk : k = k₀`. Substitute `hk` using the available equality. Simplify using `only [sndPt, Function.comp, v₁_self, if_true]`. Simplify using `only [sndPt, Function.comp, v₁_ne (p := ⟨k, m⟩) hk, if_neg hk]`.
-/
theorem orbit_sndPt {k₀ : K} {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (sndPt k₀ z) (sndPt k₀ z') := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => if k = k₀ then c none else c (some k), fun k => ?_, ?_⟩
  · dsimp only
    split_ifs
    exacts [hc _, hc _]
  · funext p
    obtain ⟨k, m⟩ := p
    by_cases hk : k = k₀
    · subst hk
      simp only [sndPt, Function.comp, v₁_self, if_true]
    · simp only [sndPt, Function.comp, v₁_ne (p := ⟨k, m⟩) hk, if_neg hk]

end Orbits

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

/- English proof (translation)
Take `⟨c, hc, hcz⟩` from `sameOrbit_flagPt_mul K ι Φ y Ψ N j M F b h B₀ hB₀`. Establish `hne : ∏ i ∈ stepCols N j a, B₁ i i ≠ 0`. Rewrite `hdet` using `[Matrix.det_of_upperTriangular ht]`. Conclude with `Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ i)`. Use `⟨fun o => o.elim (∏ i ∈ stepCols N j a, B₁ i i) c, ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `(_ | k)`. Conclude with `hne`. Conclude with `hc k`. Use function extensionality and compare the values at `p`. Take `⟨o, m⟩` from `p`.

Consider the cases of `o with`. Consider the case `none`. Simplify using `only [wVec, Option.elim_none]`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun I _ => ?_` and prove the remaining obligations.

Rewrite using `[← e, (MinorCalc.minors_main ℂ N j a M.j_le).2.2.1 _ B₁ I hd ht]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `some k`. Conclude with `congrFun hcz ⟨k, m⟩`.
-/
theorem orbit_wVec_mul (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h B₀ : Ψ → Matrix (Fin N) (Fin N) ℂ) (B₁ : Matrix (Fin N) (Fin N) ℂ) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N)
    (t s : ℂ) (hB₀ : ∀ τ', IsBlockDiag j (B₀ τ') ∧ (B₀ τ').BlockTriangular id ∧ (B₀ τ').det ≠ 0)
    (hd : IsBlockDiag j B₁) (ht : B₁.BlockTriangular id) (hdet : B₁.det ≠ 0)
    (e : h τ * (1 + Matrix.single cb ca t) * B₁ = h τ * B₀ τ * (1 + Matrix.single cb ca s)) :
    SameOrbit (wVec M F b (fun τ' => h τ' * B₀ τ') τ a k₀ ca cb s) (wVec M F b h τ a k₀ ca cb t) := by
  obtain ⟨c, hc, hcz⟩ := sameOrbit_flagPt_mul K ι Φ y Ψ N j M F b h B₀ hB₀
  have hne : ∏ i ∈ stepCols N j a, B₁ i i ≠ 0 := by
    rw [Matrix.det_of_upperTriangular ht] at hdet
    exact Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ i)
  refine ⟨fun o => o.elim (∏ i ∈ stepCols N j a, B₁ i i) c, ?_, ?_⟩
  · rintro (_ | k)
    · exact hne
    · exact hc k
  · funext p
    obtain ⟨o, m⟩ := p
    cases o with
    | none =>
      simp only [wVec, Option.elim_none]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [← e, (MinorCalc.minors_main ℂ N j a M.j_le).2.2.1 _ B₁ I hd ht]
      ring
    | some k =>
      exact congrFun hcz ⟨k, m⟩

/- English proof (translation)
Take `⟨k, hk⟩ : ∃ k, M.blk (τ', i) = some k` from `Option.ne_none_iff_exists'.1 fun e => (M.blk_none _).1 e hi`. Establish `e` using `plk_flagPt K ι Φ y Ψ N j M F b g (τ', i) k hF hb hG hg hk`. Use `hp (τ', i)` as an intermediate fact. Rewrite `this` using `[e]`. Then use the resulting hypothesis.
-/
theorem minor_ne_zero_of_plk (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk)
    (b : (Σ k, baseIdx ι M.blk k) → ℂ) (hF : M.IsFrame F) (hb : b ∈ mcPts (mCoordIdeal M.x))
    (hG : M.GoodAt F (mCoordIdeal b)) (g : Ψ → Matrix (Fin N) (Fin N) ℂ) (hg : ∀ τ', IsBlockDiag j (g τ'))
    (hp : ∀ p, plk M F b (flagPt M F b g) p ≠ 0) (τ' : Ψ) (i : Fin N) (hi : IsProperStep N j i) :
    minorIJ (g τ') (stepCols N j i) (stepCols N j i) ≠ 0 := by
  obtain ⟨k, hk⟩ : ∃ k, M.blk (τ', i) = some k :=
    Option.ne_none_iff_exists'.1 fun e => (M.blk_none _).1 e hi
  have e := plk_flagPt K ι Φ y Ψ N j M F b g (τ', i) k hF hb hG hg hk
  have := hp (τ', i)
  rwa [e] at this

/- English proof (translation)
Introduce `K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b k₀ ca cb hb hab hk hca hcb RW q hq h0 h1 hinj l x hO hp0 hp1`. Establish `hs : (ca : ℕ) < N - j ↔ (cb : ℕ) < N - j`. Establish `hN` using `M.j_le`. Establish `ha` using `a.2`. Establish `hb'` using `b.2`.

Unfold `lastCol at hca`. Apply the tactic sequence `split_ifs at hca with hl <;> omega`. Establish `hlt : ca < cb`. Rewrite using `[Fin.lt_def]`. Use linear arithmetic over natural numbers and integers.

Take `⟨x₀, hx₀⟩` from `(re_pi_bijective K ι Φ y Ψ N j M n d BM FA).2 (q 0 x)`. Establish `hz` using `RW.mem x x (RW.mem_U x)`. Establish `hbase : SameOrbit (basePart M.blk (fstPt k₀ (RW.lift x x))) (BM.Rb.lift (FA.pr (q 0 x)) (FA.pr (q 0 x)))`. Establish `e1` using `orbit_basePart M.blk (h0 x x₀ hx₀)`. Establish `e2` using `FA.pr_eq x₀`.

Rewrite `e2` using `[hx₀]`. Conclude with `orbit_trans (orbit_symm e1) e2`. Take `⟨h, t, hh, ho⟩` from `GlobalTheory.T.flag_adjacent_arith_variety_second K ι Φ y Ψ N j M n BM d τ a b k₀ ca cb hb hab hk hca hcb FA.Re.arith l _ hO _ hz hbase`. Take `⟨hbv, hgood, -, -⟩` from `bvec_good K ι Φ y Ψ N j M n BM l _ hO`. Take `⟨hw0, hw1⟩` from `fstPt_sndPt_wVec K ι Φ y Ψ N j M τ a b k₀ ca cb hb hab hk hca hcb (BM.F l) (bvec BM l (FA.pr (q 0 x))) h t`.

Establish `hf` using `orbit_fstPt ho`. Establish `hg` using `orbit_sndPt ho`. Rewrite `hf` using `[hw0]`. Rewrite `hg` using `[hw1]`. Establish `hE : IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ)`.

Introduce `r s hrs`. Establish `e1 : (1 : Matrix (Fin N) (Fin N) ℂ) r s = 0` using `Matrix.one_apply_ne fun e => hrs (by rw [e])`. Establish `e2 : (Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) r s = 0`. Rewrite using `[Matrix.single_apply, if_neg]`. Introduce and unpack `⟨rfl, rfl⟩`.

Conclude with `hrs hs.symm`. Rewrite using `[Matrix.add_apply, e1, e2, add_zero]`. Establish `hEdet : (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ).det = 1`. Use `(Matrix.det_of_lowerTriangular _ fun r s hrs => ?_).trans (Finset.prod_eq_one fun r _ => ?_)` and prove the remaining obligations. Establish `e1 : (1 : Matrix (Fin N) (Fin N) ℂ) r s = 0` using `Matrix.one_apply_ne (ne_of_lt (show r < s from hrs))`.

Establish `e2 : (Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) r s = 0`. Rewrite using `[Matrix.single_apply, if_neg]`. Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `lt_asymm hlt hrs`. Rewrite using `[Matrix.add_apply, e1, e2, add_zero]`.

Establish `e2 : (Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) r r = 0`. Rewrite using `[Matrix.single_apply, if_neg]`. Introduce and unpack `⟨rfl, h'⟩`. Conclude with `hlt.ne h'`. Rewrite using `[Matrix.add_apply, e2, add_zero, Matrix.one_apply_eq]`.

Establish `hbd₁ : IsBlockDiag j (h τ * (1 + Matrix.single cb ca t))` using `((MinorCalc.minors_main ℂ N j a M.j_le).2.2.2 _ _ (hh τ).1 hE).1`. Establish `hdet₁ : (h τ * (1 + Matrix.single cb ca t)).det ≠ 0`. Rewrite using `[Matrix.det_mul, hEdet, mul_one]`. Conclude with `(hh τ).2`. Establish `hbdU : ∀ τ', IsBlockDiag j (Function.update h τ (h τ * (1 + Matrix.single cb ca t)) τ')`.

Introduce `τ'`. Distinguish the cases in `e : τ' = τ`. Substitute `e` using the available equality. Rewrite using `[Function.update_self]`. Conclude with `hbd₁`.

Rewrite using `[Function.update_of_ne e]`. Conclude with `(hh τ').1`. Establish `m0` using `minor_ne_zero_of_plk M (BM.F l) _ (BM.isFrame l) hbv hgood h (fun τ' => (hh τ').1) (fun p => (plk_ne_zero_iff_of_sameOrbit K ι Φ y Ψ N j M (BM.F l) _ _ _ p hf).1 (hp0 p))`. Establish `m1` using `minor_ne_zero_of_plk M (BM.F l) _ (BM.isFrame l) hbv hgood _ hbdU (fun p => (plk_ne_zero_iff_of_sameOrbit K ι Φ y Ψ N j M (BM.F l) _ _ _ p hg).1 (hp1 p)) τ`. Rewrite `m1` using `[Function.update_self]`.

Use `choose B₀ hd₀ ht₀ hdet₀ hu₀ using fun τ' => BigCell.exists_upper_of_minors N j (h τ') M.j_le (hh τ').1 (hh τ').2 (m0 τ')`. Take `⟨B₁, hd₁, ht₁, hdetB₁, hu₁⟩` from `BigCell.exists_upper_of_minors N j _ M.j_le hbd₁ hdet₁ m1`. Take `⟨s, es⟩` from `Parab.mul_transvection_eq N (h τ) (B₀ τ) B₁ ca cb t hcb (ht₀ τ) ht₁ (hdet₀ τ) hdetB₁ (hu₀ τ) hu₁`. Take `⟨c, a₀, hL⟩` from `(LcFam.lc_main Ψ N j τ ca cb hlt hs.symm).2.2.1 (fun τ' => h τ' * B₀ τ') fun τ' => ⟨((MinorCalc.minors_main ℂ N j a M.j_le).2.2.2 _ _ (hh τ').1 (hd₀ τ')).1, hu₀ τ'⟩`. Use `⟨c, a₀, a₀ + s, ?_⟩` and prove the remaining obligations.

Rewrite using `[hL, add_sub_cancel_left]`. Conclude with `orbit_trans ho (orbit_symm (orbit_wVec_mul M (BM.F l) _ h B₀ B₁ τ a k₀ ca cb t s (fun τ' => ⟨hd₀ τ', ht₀ τ', hdet₀ τ'⟩) hd₁ ht₁ hdetB₁ es))`.
-/
theorem vector_of_chart : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ i, HoloMap RW.A FA.S.A (q i)) → (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → (Function.Injective fun w => (q 0 w, q 1 w)) → ∀ (l : Fin BM.q) (x : RW.X), FA.pr (q 0 x) ∈ BM.O l → (∀ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x))) (fstPt k₀ (RW.lift x x)) p ≠ 0) → (∀ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x))) (sndPt k₀ (RW.lift x x)) p ≠ 0) → ∃ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a₀ a₁ : ℂ), SameOrbit (RW.lift x x) (FC.wVec M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x))) (FC.Lca τ ca cb c a₀) τ a k₀ ca cb (a₁ - a₀)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b k₀ ca cb hb hab hk hca hcb RW q hq h0 h1 hinj l x hO hp0 hp1
  have hs : (ca : ℕ) < N - j ↔ (cb : ℕ) < N - j := by
    have hN := M.j_le
    have ha := a.2
    have hb' := b.2
    unfold lastCol at hca
    split_ifs at hca with hl <;> omega
  have hlt : ca < cb := by
    rw [Fin.lt_def]
    omega
  obtain ⟨x₀, hx₀⟩ := (re_pi_bijective K ι Φ y Ψ N j M n d BM FA).2 (q 0 x)
  have hz := RW.mem x x (RW.mem_U x)
  have hbase : SameOrbit (basePart M.blk (fstPt k₀ (RW.lift x x)))
      (BM.Rb.lift (FA.pr (q 0 x)) (FA.pr (q 0 x))) := by
    have e1 := orbit_basePart M.blk (h0 x x₀ hx₀)
    have e2 := FA.pr_eq x₀
    rw [hx₀] at e2
    exact orbit_trans (orbit_symm e1) e2
  obtain ⟨h, t, hh, ho⟩ := GlobalTheory.T.flag_adjacent_arith_variety_second K ι Φ y Ψ N j M n BM d τ a b k₀ ca cb hb hab hk hca hcb FA.Re.arith l _ hO _
    hz hbase
  obtain ⟨hbv, hgood, -, -⟩ := bvec_good K ι Φ y Ψ N j M n BM l _ hO
  obtain ⟨hw0, hw1⟩ := fstPt_sndPt_wVec K ι Φ y Ψ N j M τ a b k₀ ca cb hb hab hk hca hcb (BM.F l)
    (bvec BM l (FA.pr (q 0 x))) h t
  have hf := orbit_fstPt ho
  have hg := orbit_sndPt ho
  rw [hw0] at hf
  rw [hw1] at hg
  have hE : IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) := by
    intro r s hrs
    have e1 : (1 : Matrix (Fin N) (Fin N) ℂ) r s = 0 := Matrix.one_apply_ne fun e => hrs (by rw [e])
    have e2 : (Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) r s = 0 := by
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      exact hrs hs.symm
    rw [Matrix.add_apply, e1, e2, add_zero]
  have hEdet : (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ).det = 1 := by
    refine (Matrix.det_of_lowerTriangular _ fun r s hrs => ?_).trans (Finset.prod_eq_one fun r _ => ?_)
    · have e1 : (1 : Matrix (Fin N) (Fin N) ℂ) r s = 0 := Matrix.one_apply_ne (ne_of_lt (show r < s from hrs))
      have e2 : (Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) r s = 0 := by
        rw [Matrix.single_apply, if_neg]
        rintro ⟨rfl, rfl⟩
        exact lt_asymm hlt hrs
      rw [Matrix.add_apply, e1, e2, add_zero]
    · have e2 : (Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) r r = 0 := by
        rw [Matrix.single_apply, if_neg]
        rintro ⟨rfl, h'⟩
        exact hlt.ne h'
      rw [Matrix.add_apply, e2, add_zero, Matrix.one_apply_eq]
  have hbd₁ : IsBlockDiag j (h τ * (1 + Matrix.single cb ca t)) :=
    ((MinorCalc.minors_main ℂ N j a M.j_le).2.2.2 _ _ (hh τ).1 hE).1
  have hdet₁ : (h τ * (1 + Matrix.single cb ca t)).det ≠ 0 := by
    rw [Matrix.det_mul, hEdet, mul_one]
    exact (hh τ).2
  have hbdU : ∀ τ', IsBlockDiag j (Function.update h τ (h τ * (1 + Matrix.single cb ca t)) τ') := by
    intro τ'
    by_cases e : τ' = τ
    · subst e
      rw [Function.update_self]
      exact hbd₁
    · rw [Function.update_of_ne e]
      exact (hh τ').1
  have m0 := minor_ne_zero_of_plk M (BM.F l) _ (BM.isFrame l) hbv hgood h (fun τ' => (hh τ').1)
    (fun p => (plk_ne_zero_iff_of_sameOrbit K ι Φ y Ψ N j M (BM.F l) _ _ _ p hf).1 (hp0 p))
  have m1 := minor_ne_zero_of_plk M (BM.F l) _ (BM.isFrame l) hbv hgood _ hbdU
    (fun p => (plk_ne_zero_iff_of_sameOrbit K ι Φ y Ψ N j M (BM.F l) _ _ _ p hg).1 (hp1 p)) τ
  rw [Function.update_self] at m1
  choose B₀ hd₀ ht₀ hdet₀ hu₀ using fun τ' =>
    BigCell.exists_upper_of_minors N j (h τ') M.j_le (hh τ').1 (hh τ').2 (m0 τ')
  obtain ⟨B₁, hd₁, ht₁, hdetB₁, hu₁⟩ := BigCell.exists_upper_of_minors N j _ M.j_le hbd₁ hdet₁ m1
  obtain ⟨s, es⟩ := Parab.mul_transvection_eq N (h τ) (B₀ τ) B₁ ca cb t hcb (ht₀ τ) ht₁ (hdet₀ τ) hdetB₁ (hu₀ τ) hu₁
  obtain ⟨c, a₀, hL⟩ := (LcFam.lc_main Ψ N j τ ca cb hlt hs.symm).2.2.1 (fun τ' => h τ' * B₀ τ') fun τ' =>
    ⟨((MinorCalc.minors_main ℂ N j a M.j_le).2.2.2 _ _ (hh τ').1 (hd₀ τ')).1, hu₀ τ'⟩
  refine ⟨c, a₀, a₀ + s, ?_⟩
  rw [hL, add_sub_cancel_left]
  exact orbit_trans ho (orbit_symm (orbit_wVec_mul M (BM.F l) _ h B₀ B₁ τ a k₀ ca cb t s
    (fun τ' => ⟨hd₀ τ', ht₀ τ', hdet₀ τ'⟩) hd₁ ht₁ hdetB₁ es))

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.Cell
