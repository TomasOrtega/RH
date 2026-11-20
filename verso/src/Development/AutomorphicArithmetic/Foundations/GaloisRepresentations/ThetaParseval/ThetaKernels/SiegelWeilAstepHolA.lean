import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.CntFalse
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
/- English proof (translation)
Use function extensionality and compare the values at `X`. Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, Pi.sub_apply]`. Rewrite using `[← map_sub]`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Simplify using `only [Darboux.rho, schr, Pi.sub_apply, mul_sub]`.
-/
theorem T_sub_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ Φ' : d.Fn) : d.T (Φ - Φ') = d.T Φ - d.T Φ' := by
  funext X
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, Pi.sub_apply]
  rw [← map_sub]
  congr 1
  funext x
  simp only [Darboux.rho, schr, Pi.sub_apply, mul_sub]
/- English proof (translation)
Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem f hf`. Take `⟨g, hg, rfl⟩` from `hf`. Use `⟨fun X => (∏ w' ∈ Finset.univ.erase w, fP 1 (R.loc w' X)) * g fun k => (d.crd X k).2, Submodule.subset_span ⟨fun _ => 1, g, hg, rfl⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `X`.

Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens]`. Rewrite using `[← mul_assoc, Finset.mul_prod_erase _ (fun w' => fP 1 (R.loc w' X)) (Finset.mem_univ w)]`. Consider the case `zero => exact ⟨0, zero_mem _, by funext X; simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens]⟩`. Consider the case `add f f' _ _ h h'`. Take `⟨Ψ, hΨ, rfl⟩` from `h`.

Take `⟨Ψ', hΨ', rfl⟩` from `h'`. Conclude with `⟨Ψ + Ψ', add_mem hΨ hΨ', by funext X; simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, mul_add]⟩`. Consider the case `smul a f _ h`. Take `⟨Ψ, hΨ, rfl⟩` from `h`. Conclude with `⟨a • Ψ, Submodule.smul_mem _ a hΨ, by funext X; simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens]; ring⟩`.
-/
theorem vac_tens_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (f : Mx F E d.m d.n → ℂ) (hf : f ∈ R.vac) :
    ∃ Ψ ∈ R.away w, f = R.tens w (fP 1) Ψ := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨g, hg, rfl⟩ := hf
    refine ⟨fun X => (∏ w' ∈ Finset.univ.erase w, fP 1 (R.loc w' X)) * g fun k => (d.crd X k).2,
      Submodule.subset_span ⟨fun _ => 1, g, hg, rfl⟩, ?_⟩
    funext X
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens]
    rw [← mul_assoc, Finset.mul_prod_erase _ (fun w' => fP 1 (R.loc w' X)) (Finset.mem_univ w)]
  | zero => exact ⟨0, zero_mem _, by funext X; simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens]⟩
  | add f f' _ _ h h' =>
    obtain ⟨Ψ, hΨ, rfl⟩ := h
    obtain ⟨Ψ', hΨ', rfl⟩ := h'
    exact ⟨Ψ + Ψ', add_mem hΨ hΨ', by funext X; simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, mul_add]⟩
  | smul a f _ h =>
    obtain ⟨Ψ, hΨ, rfl⟩ := h
    exact ⟨a • Ψ, Submodule.smul_mem _ a hΨ, by funext X; simp [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens]; ring⟩
/- English proof (translation)
Introduce `L hL`. Establish `hK` using `H.polyKFin F E σ d R Φ hΦ ((H.vacK F E σ d R).2.1 hv)`. Establish `hsec` using `H.secK F E σ d Φ hK`. Establish `hEis` using `H.eisWk F E σ d _ _ hsec`. Take `⟨hadd, hbd⟩` from `H.lamBd F E σ d L hL`.

Take `⟨nb, lam, 𝓖, T, x, hc, hT, rfl⟩` from `hL`. Take `⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩` from `hE`. Take `⟨hDiff, hComm⟩` from `lamDeriv (rat2 σ d.Y) _ hadd hbd U Ê hUo hd hcont hinv`. Use `show fc d.B.ψ d.b nb lam 𝓖 (fun g => iteratedDeriv j (Ê · g) (s0 d.m d.n)) T x = 0`. Rewrite using `[← hComm _ hs j]`.

Take `⟨t', ht'⟩` from `H.unfold F E σ d _ _ hsec hEis`. Take `⟨ε, w, hw, -⟩` from `(H.auxEx F E σ d).2.1`. Establish `hWL` using `H.whitLow F E σ d R hmn Φ hΦ hv nb lam 𝓖 hc ε w hw T hT x`. Rewrite `hWL` using `[zero_mul]`. Use `ordVal U p (fun z => fc d.B.ψ d.b nb lam 𝓖 (Ê z) T x) (fun z => ∫ β, flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam) (max t t') (s0 d.m d.n) 0 hUo hR hs hp hDiff ?_ hWL j hj` as an intermediate fact.

Rewrite using `[this, mul_zero]`. Introduce `z hz`. Establish `h1` using `(hfar z (lt_of_le_of_lt (le_max_left _ _) hz)).2`. Establish `h2` using `(ht' z (lt_of_le_of_lt (le_max_right _ _) hz) nb lam 𝓖 hc ε w hw x).2 T hT`. Rewrite using `[← h2]`.

Simplify using `only [fc, h1, mul_assoc]`. Conclude with `integral_const_mul _ _`.
-/
theorem ndA_k (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (hmn : d.m < d.n) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac)
    {U p Ê t} (hE : _root_.PositivityTheory.SiegelWeilFormula.AStep.EData_k d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t) (j : ℕ) (hj : j ≤ p.rootMultiplicity (s0 d.m d.n)) :
    ∀ L ∈ d.lamSet, L (fun g => iteratedDeriv j (Ê · g) (s0 d.m d.n)) = 0 := by
  intro L hL
  have hK := H.polyKFin F E σ d R Φ hΦ ((H.vacK F E σ d R).2.1 hv)
  have hsec := H.secK F E σ d Φ hK
  have hEis := H.eisWk F E σ d _ _ hsec
  obtain ⟨hadd, hbd⟩ := H.lamBd F E σ d L hL
  obtain ⟨nb, lam, 𝓖, T, x, hc, hT, rfl⟩ := hL
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE
  obtain ⟨hDiff, hComm⟩ := lamDeriv (rat2 σ d.Y) _ hadd hbd U Ê hUo hd hcont hinv
  show fc d.B.ψ d.b nb lam 𝓖 (fun g => iteratedDeriv j (Ê · g) (s0 d.m d.n)) T x = 0
  rw [← hComm _ hs j]
  obtain ⟨t', ht'⟩ := H.unfold F E σ d _ _ hsec hEis
  obtain ⟨ε, w, hw, -⟩ := (H.auxEx F E σ d).2.1
  have hWL := H.whitLow F E σ d R hmn Φ hΦ hv nb lam 𝓖 hc ε w hw T hT x
  rw [zero_mul] at hWL
  have := ordVal U p (fun z => fc d.B.ψ d.b nb lam 𝓖 (Ê z) T x)
    (fun z => ∫ β, flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam) (max t t')
    (s0 d.m d.n) 0 hUo hR hs hp hDiff ?_ hWL j hj
  · rw [this, mul_zero]
  · intro z hz
    have h1 := (hfar z (lt_of_le_of_lt (le_max_left _ _) hz)).2
    have h2 := (ht' z (lt_of_le_of_lt (le_max_right _ _) hz) nb lam 𝓖 hc ε w hw x).2 T hT
    rw [← h2]
    simp only [fc, h1, mul_assoc]
    exact integral_const_mul _ _
/- English proof (translation)
Take `⟨-, -, hTG, hLC, hT2, hSC⟩` from `H.auxEx F E σ d`. Establish `hE'` using `hE`. Take `⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩` from `hE'`. Establish `hAc` using `famCont U Ê hUo hd hcont _ hs j`. Establish `hAi : ∀ γ ∈ rat2 σ d.Y, ∀ g, iteratedDeriv j (Ê · (γ * g)) (s0 d.m d.n) = iteratedDeriv j (Ê · g) (s0 d.m d.n)` using `fun γ hγ g => derivInv U Ê hUo _ hs γ g (fun z hz => hinv z hz γ hγ g) j`.

Take `⟨Ψ, hΨ, hTΨ⟩` from `_root_.PositivityTheory.SiegelWeilFormula.AStep.vac_tens_k R w _ hv`. Take `⟨Lop, hLop⟩` from `H.locOpEx F E σ d R w`. Take `⟨φ, hφ⟩` from `H.liftEx F E σ d R w Ψ hΨ`. Take `⟨sL, ρ, pp, qq, e, -, hLD, hsL, -⟩` from `H.locInst F E σ d R w Lop hLop`. Establish `hΦφ : φ 1 = Φ`.

Establish `h0` using `(H.tAll.1 F E σ d).2.2 (φ 1 - Φ) (sub_mem (hφ 1).1 hΦ) (by rw [_root_.PositivityTheory.SiegelWeilFormula.AStep.T_sub_k, (hφ 1).2, hTΨ, sub_self])`. Conclude with `sub_eq_zero.1 h0`. Establish `hpq : pp = d.m ∧ qq = 0 ∨ pp = 0 ∧ qq = d.m`. Break down `hLD.sign with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩` into its components or cases. Use `left`.

Rewrite using `[h1, h2, cnt_true, cnt_false]`. Conclude with `⟨rfl, rfl⟩`. Use `right`. Rewrite using `[h1, h2, cnt_true, cnt_false]`. Conclude with `⟨rfl, rfl⟩`.

Use `⟨pp, qq, e, hpq, ?_⟩` and prove the remaining obligations. Use `haveI := hTG`. Use `haveI := hLC`. Use `haveI := hT2`. Use `haveI := hSC`.

Use `H.holLead d.m d.n pp qq e d.ok.hm hmn hpq d.G (par2 σ d.Y) (rat2 σ d.Y) (R.ι w) (s0 d.m d.n) d.Ht (d.sec0 Φ) (R.cont w) ?_ U p Ê t hUo hR hs hd hcont (fun z hz => ⟨(hfar z hz).1, fun g => (hfar z hz).2 g⟩) j hlow ?_` and prove the remaining obligations. Introduce `g`. Take `⟨x, y, c, r, hr, hg, hxy⟩` from `H.gSplit F E σ d R w Lop hLop Ψ hΨ φ hφ g`. Use `⟨x, y, c, r, hr, hg, fun y' => ⟨(hxy y').1, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← hΦφ, (hxy y').2 1, ← hsL, hLD.vac]`.

Introduce `ψ hψ nb hnb g a b`. Conclude with `H.lamSing F E σ d R w _ hAc hAi (_root_.PositivityTheory.SiegelWeilFormula.AStep.ndA_k H R hmn hΦ hv hE j hj) ψ hψ nb hnb g a b`.
-/
theorem holA_pf_k (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (hmn : d.m < d.n) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac)
    {U : Set ℂ} {p : Polynomial ℂ} {Ê : ℂ → d.G → ℂ} {t : ℝ}
    (hE : _root_.PositivityTheory.SiegelWeilFormula.AStep.EData_k d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t) (w : InfinitePlace F) (j : ℕ)
    (hj : j ≤ p.rootMultiplicity (s0 d.m d.n)) (hlow : ∀ i < j, ∀ g, iteratedDeriv i (Ê · g) (s0 d.m d.n) = 0) :
    ∃ (pp qq : ℕ) (e : ℤ), (pp = d.m ∧ qq = 0 ∨ pp = 0 ∧ qq = d.m) ∧
      ∀ g, IsHolW pp qq e fun y => iteratedDeriv j (Ê · (g * R.ι w y)) (s0 d.m d.n) := by
  obtain ⟨-, -, hTG, hLC, hT2, hSC⟩ := H.auxEx F E σ d
  have hE' := hE
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE'
  have hAc := famCont U Ê hUo hd hcont _ hs j
  have hAi : ∀ γ ∈ rat2 σ d.Y, ∀ g, iteratedDeriv j (Ê · (γ * g)) (s0 d.m d.n) = iteratedDeriv j (Ê · g) (s0 d.m d.n) :=
    fun γ hγ g => derivInv U Ê hUo _ hs γ g (fun z hz => hinv z hz γ hγ g) j
  obtain ⟨Ψ, hΨ, hTΨ⟩ := _root_.PositivityTheory.SiegelWeilFormula.AStep.vac_tens_k R w _ hv
  obtain ⟨Lop, hLop⟩ := H.locOpEx F E σ d R w
  obtain ⟨φ, hφ⟩ := H.liftEx F E σ d R w Ψ hΨ
  obtain ⟨sL, ρ, pp, qq, e, -, hLD, hsL, -⟩ := H.locInst F E σ d R w Lop hLop
  have hΦφ : φ 1 = Φ := by
    have h0 := (H.tAll.1 F E σ d).2.2 (φ 1 - Φ) (sub_mem (hφ 1).1 hΦ) (by rw [_root_.PositivityTheory.SiegelWeilFormula.AStep.T_sub_k, (hφ 1).2, hTΨ, sub_self])
    exact sub_eq_zero.1 h0
  have hpq : pp = d.m ∧ qq = 0 ∨ pp = 0 ∧ qq = d.m := by
    rcases hLD.sign with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
    · left; rw [h1, h2, cnt_true, cnt_false]; exact ⟨rfl, rfl⟩
    · right; rw [h1, h2, cnt_true, cnt_false]; exact ⟨rfl, rfl⟩
  refine ⟨pp, qq, e, hpq, ?_⟩
  haveI := hTG; haveI := hLC; haveI := hT2; haveI := hSC
  refine H.holLead d.m d.n pp qq e d.ok.hm hmn hpq d.G (par2 σ d.Y) (rat2 σ d.Y) (R.ι w) (s0 d.m d.n) d.Ht (d.sec0 Φ)
    (R.cont w) ?_ U p Ê t hUo hR hs hd hcont (fun z hz => ⟨(hfar z hz).1, fun g => (hfar z hz).2 g⟩) j hlow ?_
  · intro g
    obtain ⟨x, y, c, r, hr, hg, hxy⟩ := H.gSplit F E σ d R w Lop hLop Ψ hΨ φ hφ g
    refine ⟨x, y, c, r, hr, hg, fun y' => ⟨(hxy y').1, ?_⟩⟩
    rw [← hΦφ, (hxy y').2 1, ← hsL, hLD.vac]
  · intro ψ hψ nb hnb g a b
    exact H.lamSing F E σ d R w _ hAc hAi (_root_.PositivityTheory.SiegelWeilFormula.AStep.ndA_k H R hmn hΦ hv hE j hj) ψ hψ nb hnb g a b
end PositivityTheory.SiegelWeilFormula.AStep
end
end
