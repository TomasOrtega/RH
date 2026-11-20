import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.ExpNeOfLt

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Establish `hK` using `H.polyKFin F E σ d R Φ hΦ ((H.vacK F E σ d R).2.1 hv)`. Establish `hsec` using `H.secK F E σ d Φ hK`. Establish `hEis` using `H.eisWk F E σ d _ _ hsec`. Establish `hL : (fun f => fc d.B.ψ d.b nb lam 𝓖 f T x) ∈ d.lamSet` using `⟨nb, lam, 𝓖, T, x, hc, hT, rfl⟩`. Take `⟨hadd, hbd⟩` from `H.lamBd F E σ d _ hL`.

Take `⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩` from `hE`. Take `⟨hDiff, hComm⟩` from `lamDeriv (rat2 σ d.Y) _ hadd hbd U Ê hUo hd hcont hinv`. Take `⟨-, -, hI⟩` from `H.tAll.2.2.2.2 F E σ d`. Take `⟨-, hIc, hIi⟩` from `hI Φ hΦ`. Establish `hAc` using `famCont U Ê hUo hd hcont _ hs j`.

Establish `hAi : ∀ γ ∈ rat2 σ d.Y, ∀ g, iteratedDeriv j (Ê · (γ * g)) (s0 d.m d.n) = iteratedDeriv j (Ê · g) (s0 d.m d.n)` using `fun γ hγ g => derivInv U Ê hUo _ hs γ g (fun z hz => hinv z hz γ hγ g) j`. Establish `hLI : fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x = 0`. Rewrite using `[H.thetaCoef F E σ d Φ hΦ nb lam 𝓖 hc T x]`. Conclude with `(H.orbRes F E σ d).1 hmn T hT _`. Establish `hB : Bj d Φ p Ê j = (-(iteratedDeriv j (fun z => p.eval z) (s0 d.m d.n) * 2)) • d.I Φ + (fun g => iteratedDeriv j (Ê · g) (s0 d.m d.n))`.

Use function extensionality and compare the values at `g`. Simplify using `only [Bj, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `hadd (-(iteratedDeriv j (fun z => p.eval z) (s0 d.m d.n) * 2)) (d.I Φ) (fun g => iteratedDeriv j (Ê · g) (s0 d.m d.n)) hIc hAc hIi hAi`. Rewrite using `[hB, h1, hLI, mul_zero, zero_add, ← hComm _ hs j]`.

Take `⟨t', ht'⟩` from `H.unfold F E σ d _ _ hsec hEis`. Take `⟨ε, w, hw, -⟩` from `(H.auxEx F E σ d).2.1`. Establish `hWL` using `H.whitLow F E σ d R hmn Φ hΦ hv nb lam 𝓖 hc ε w hw T hT x`. Rewrite `hWL` using `[zero_mul]`. Use `ordVal U p (fun z => fc d.B.ψ d.b nb lam 𝓖 (Ê z) T x) (fun z => ∫ β, flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam) (max t t') (s0 d.m d.n) 0 hUo hR hs hp hDiff ?_ hWL j hj` as an intermediate fact.

Rewrite using `[this, mul_zero]`. Introduce `z hz`. Establish `h1` using `(hfar z (lt_of_le_of_lt (le_max_left _ _) hz)).2`. Establish `h2` using `(ht' z (lt_of_le_of_lt (le_max_right _ _) hz) nb lam 𝓖 hc ε w hw x).2 T hT`. Rewrite using `[← h2]`.

Simplify using `only [fc, h1, mul_assoc]`. Conclude with `integral_const_mul _ _`.
-/
theorem ndZero (H : Hyps) {d : SD σ} (R : RD d) (hmn : d.m < d.n) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac)
    {U p Ê t} (hE : EData d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t) (j : ℕ) (hj : j ≤ p.rootMultiplicity (s0 d.m d.n))
    {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {T : nF σ d.Y d.b} (hT : IsND T) (x : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 (Bj d Φ p Ê j) T x = 0 := by
  have hK := H.polyKFin F E σ d R Φ hΦ ((H.vacK F E σ d R).2.1 hv)
  have hsec := H.secK F E σ d Φ hK
  have hEis := H.eisWk F E σ d _ _ hsec
  have hL : (fun f => fc d.B.ψ d.b nb lam 𝓖 f T x) ∈ d.lamSet := ⟨nb, lam, 𝓖, T, x, hc, hT, rfl⟩
  obtain ⟨hadd, hbd⟩ := H.lamBd F E σ d _ hL
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE
  obtain ⟨hDiff, hComm⟩ := lamDeriv (rat2 σ d.Y) _ hadd hbd U Ê hUo hd hcont hinv
  obtain ⟨-, -, hI⟩ := H.tAll.2.2.2.2 F E σ d
  obtain ⟨-, hIc, hIi⟩ := hI Φ hΦ
  have hAc := famCont U Ê hUo hd hcont _ hs j
  have hAi : ∀ γ ∈ rat2 σ d.Y, ∀ g, iteratedDeriv j (Ê · (γ * g)) (s0 d.m d.n) = iteratedDeriv j (Ê · g) (s0 d.m d.n) :=
    fun γ hγ g => derivInv U Ê hUo _ hs γ g (fun z hz => hinv z hz γ hγ g) j
  have hLI : fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x = 0 := by
    rw [H.thetaCoef F E σ d Φ hΦ nb lam 𝓖 hc T x]; exact (H.orbRes F E σ d).1 hmn T hT _
  have hB : Bj d Φ p Ê j = (-(iteratedDeriv j (fun z => p.eval z) (s0 d.m d.n) * 2)) • d.I Φ +
      (fun g => iteratedDeriv j (Ê · g) (s0 d.m d.n)) := by
    funext g; simp only [Bj, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have h1 := hadd (-(iteratedDeriv j (fun z => p.eval z) (s0 d.m d.n) * 2)) (d.I Φ) (fun g => iteratedDeriv j (Ê · g) (s0 d.m d.n))
    hIc hAc hIi hAi
  rw [hB, h1, hLI, mul_zero, zero_add, ← hComm _ hs j]
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
Take `⟨nb, lam, 𝓖, hc⟩` from `H.coefEx F E σ d`. Establish `hE'` using `hE`. Take `⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩` from `hE'`. Take `⟨-, -, hI⟩` from `H.tAll.2.2.2.2 F E σ d`. Take `⟨-, hIc, hIi⟩` from `hI Φ hΦ`.

Establish `hBc : Continuous (Bj d Φ p Ê j)` using `(famCont U Ê hUo hd hcont _ hs j).sub (continuous_const.mul (continuous_const.mul hIc))`. Establish `hBr : ∀ γ ∈ rat2 σ d.Y, ∀ g, Bj d Φ p Ê j (γ * g) = Bj d Φ p Ê j g` using `fun γ hγ g => by`. Simplify using `only [Bj, derivInv U Ê hUo _ hs γ g (fun z hz => hinv z hz γ hγ g) j, hIi γ hγ g]`. Establish `hz` using `H.fourierZero F E σ d nb lam 𝓖 hc (Bj d Φ p Ê j) hBc (fun β hβ g => hBr _ (nbRat d hc β hβ) g) ?_`. Introduce `g`.

Conclude with `congrFun hz g`. Introduce `T g`. Distinguish the cases in `hT : IsND T`. Conclude with `ndZero H R hmn hΦ hv hE j hj hc hT g`. Take `⟨γ, hγ, T₀, T', hsub, hfc⟩` from `(H.fcConj F E σ d L nb lam 𝓖 hc).1 T hT`.

Rewrite using `[hfc _ hBc hBr g]`. Conclude with `deg H R L R' hmn hIH hΦ hv hE j hj hlow hc hsub _`.
-/
theorem stepJ (H : Hyps) {d : SD σ} (R : RD d) (L : LD d) (R' : RD L.sd) (hmn : d.m < d.n) (hIH : MainV 2 R') {Φ : d.Fn}
    (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac) {U p Ê t} (hE : EData d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t) (j : ℕ)
    (hj : j ≤ p.rootMultiplicity (s0 d.m d.n)) (hlow : ∀ i < j, ∀ g, iteratedDeriv i (Ê · g) (s0 d.m d.n) = 0) :
    ∀ g, Bj d Φ p Ê j g = 0 := by
  obtain ⟨nb, lam, 𝓖, hc⟩ := H.coefEx F E σ d
  have hE' := hE
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE'
  obtain ⟨-, -, hI⟩ := H.tAll.2.2.2.2 F E σ d
  obtain ⟨-, hIc, hIi⟩ := hI Φ hΦ
  have hBc : Continuous (Bj d Φ p Ê j) :=
    (famCont U Ê hUo hd hcont _ hs j).sub (continuous_const.mul (continuous_const.mul hIc))
  have hBr : ∀ γ ∈ rat2 σ d.Y, ∀ g, Bj d Φ p Ê j (γ * g) = Bj d Φ p Ê j g := fun γ hγ g => by
    simp only [Bj, derivInv U Ê hUo _ hs γ g (fun z hz => hinv z hz γ hγ g) j, hIi γ hγ g]
  have hz := H.fourierZero F E σ d nb lam 𝓖 hc (Bj d Φ p Ê j) hBc (fun β hβ g => hBr _ (nbRat d hc β hβ) g) ?_
  · intro g; exact congrFun hz g
  · intro T g
    by_cases hT : IsND T
    · exact ndZero H R hmn hΦ hv hE j hj hc hT g
    · obtain ⟨γ, hγ, T₀, T', hsub, hfc⟩ := (H.fcConj F E σ d L nb lam 𝓖 hc).1 T hT
      rw [hfc _ hBc hBr g]
      exact deg H R L R' hmn hIH hΦ hv hE j hj hlow hc hsub _

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ d R L R' hmn hIH Φ hΦ hv x`. Establish `hK` using `H.polyKFin F E σ d R Φ hΦ ((H.vacK F E σ d R).2.1 hv)`. Establish `hsec` using `H.secK F E σ d Φ hK`. Take `⟨U, p, Ê, t, hE⟩` from `H.eisWk F E σ d _ _ hsec (s0 d.m d.n)`. Establish `hall : ∀ j ≤ p.rootMultiplicity (s0 d.m d.n), ∀ g, Bj d Φ p Ê j g = 0`.

Introduce `j`. Proceed by induction on `j using Nat.strong_induction_on with`. Consider the case `_ j ih`. Introduce `hj`. Use `stepJ H R L R' hmn hIH hΦ hv hE j hj fun i hi g => ?_` and prove the remaining obligations.

Use `ih i hi (hi.le.trans hj) g` as an intermediate fact. Simplify `this` using `only [Bj, pderiv_lt p _ i (lt_of_lt_of_le hi hj), zero_mul, sub_zero]`. Take `⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩` from `hE`. Use `wrap U p (Ê · x) (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) t _ _ hUo hR hs hp (hd x) (fun z hz => (hfar z hz).2 x) (fun j hj => ?_) ?_` and prove the remaining obligations. Use `hall j hj.le x` as an intermediate fact.

Simplify `this` using `only [Bj, pderiv_lt p _ j hj, zero_mul, sub_zero]`. Conclude with `sub_eq_zero.1 (hall _ le_rfl x)`.
-/
theorem step (H : Hyps) : Step := by
  intro F E _ _ _ _ _ σ d R L R' hmn hIH Φ hΦ hv x
  have hK := H.polyKFin F E σ d R Φ hΦ ((H.vacK F E σ d R).2.1 hv)
  have hsec := H.secK F E σ d Φ hK
  obtain ⟨U, p, Ê, t, hE⟩ := H.eisWk F E σ d _ _ hsec (s0 d.m d.n)
  have hall : ∀ j ≤ p.rootMultiplicity (s0 d.m d.n), ∀ g, Bj d Φ p Ê j g = 0 := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      refine stepJ H R L R' hmn hIH hΦ hv hE j hj fun i hi g => ?_
      have := ih i hi (hi.le.trans hj) g
      simpa only [Bj, pderiv_lt p _ i (lt_of_lt_of_le hi hj), zero_mul, sub_zero] using this
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE
  refine wrap U p (Ê · x) (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) t _ _ hUo hR hs hp (hd x)
    (fun z hz => (hfar z hz).2 x) (fun j hj => ?_) ?_
  · have := hall j hj.le x
    simpa only [Bj, pderiv_lt p _ j hj, zero_mul, sub_zero] using this
  · exact sub_eq_zero.1 (hall _ le_rfl x)

/- English proof (translation)
Introduce `h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25` and use `step ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25⟩`.
-/
theorem stepOf : StepOf := fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 =>
  step ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25⟩

end PositivityTheory.SiegelWeilFormula.AStep

end
