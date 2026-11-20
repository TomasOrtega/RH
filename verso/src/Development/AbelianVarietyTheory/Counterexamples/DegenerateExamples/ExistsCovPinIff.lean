import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDeltaDatumHigherLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevelStatement
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.AdmissibleSmulIffOfCoprime
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.FullIffBijective

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Survey.CoverPinCounterexample

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) {n : ℕ}

/- English proof (translation)
Take `⟨d, h1, h2, hl, -, -, h3, hlev, hs⟩` from `GlobalTheory.LevelCover.exists_deltaDat_isLev E H Dw l Xo c hr n 1 ⊤ l Xo c rfl ⟨dvd_rfl, le_rfl, dvd_rfl⟩ (mul_one _).symm (Nat.coprime_one_left _) (Ideal.mul_top _).symm (top_sup_eq _)`. Conclude with `⟨d, h1, h2, hl, h3, fun _ => ⟨hlev, by rw [hl]; exact hA, hs⟩⟩`.
-/
theorem exists_trivial (hr : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1) (Tup : Type) :
    ∃ d : DeltaDat Xo c n, d.pd = 1 ∧ d.I = ⊤ ∧ d.l₂ = l ∧ d.cδ = 1 ∧ CovPin Xo c (fun _ : Tup => d) := by
  obtain ⟨d, h1, h2, hl, -, -, h3, hlev, hs⟩ := GlobalTheory.LevelCover.exists_deltaDat_isLev E H Dw l Xo c hr n 1 ⊤ l Xo c rfl
    ⟨dvd_rfl, le_rfl, dvd_rfl⟩ (mul_one _).symm (Nat.coprime_one_left _) (Ideal.mul_top _).symm (top_sup_eq _)
  exact ⟨d, h1, h2, hl, h3, fun _ => ⟨hlev, by rw [hl]; exact hA, hs⟩⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨dδ, h⟩`. Take `⟨t⟩` from `‹Nonempty Tup›`. Establish `h1` using `(h t).1.1.2.2`. Rewrite `h1` using `[(h t).2.1]`.

Conclude with `Nat.dvd_one.1 h1`. Introduce `hA`. Take `⟨d, -, -, -, -, h⟩` from `exists_trivial (n := n) Xo c hr hA Tup`. Conclude with `⟨_, h⟩`.
-/
theorem exists_covPin_iff (hr : 1 ≤ Dw.p + Dw.q) (Tup : Type) [Nonempty Tup] :
    (∃ dδ : Tup → DeltaDat Xo c n, CovPin Xo c dδ) ↔ l.A = 1 := by
  constructor
  · rintro ⟨dδ, h⟩
    obtain ⟨t⟩ := ‹Nonempty Tup›
    have h1 := (h t).1.1.2.2
    rw [(h t).2.1] at h1
    exact Nat.dvd_one.1 h1
  · intro hA
    obtain ⟨d, -, -, -, -, h⟩ := exists_trivial (n := n) Xo c hr hA Tup
    exact ⟨_, h⟩

/- English proof (translation)
Introduce `t` and use `h (f t)`.
-/
theorem covPin_comp {Tup Tup' : Type} (f : Tup' → Tup) (dδ : Tup → DeltaDat Xo c n) (h : CovPin Xo c dδ) :
    CovPin Xo c (fun t => dδ (f t)) := fun t => h (f t)

set_option synthInstance.maxHeartbeats 200000 in

/- English proof (translation)
Introduce `t` and use `⟨GlobalTheory.LevelCoverDatum.isLev_smul (dδ t) (h t).1 (a t) (ha t), (h t).2.1, (h t).2.2⟩`.
-/
theorem covPin_smul {Tup : Type} (dδ : Tup → DeltaDat Xo c n) (h : CovPin Xo c dδ) (a : ∀ t, (dδ t).c₂.F)
    (ha : ∀ t, a t ≠ 0) : CovPin Xo c (fun t => { dδ t with cδ := a t • (dδ t).cδ }) :=
  fun t => ⟨GlobalTheory.LevelCoverDatum.isLev_smul (dδ t) (h t).1 (a t) (ha t), (h t).2.1, (h t).2.2⟩

variable {Xo c}

/- English proof (translation)
Establish `h1` using `GlobalTheory.LevelCoverDatum.half_mul_conj d h`. Establish `: Ideal.span {(d.pd : 𝓞 E)} ≤ d.I` using `h1 ▸ Ideal.mul_le_left`. Conclude with `hI (this (Ideal.subset_span rfl))`.
-/
theorem pd_mem (d : DeltaDat Xo c n) (h : d.IsLev) {P : Ideal (𝓞 E)} (hI : d.I ≤ P) : (d.pd : 𝓞 E) ∈ P := by
  have h1 := GlobalTheory.LevelCoverDatum.half_mul_conj d h
  have : Ideal.span {(d.pd : 𝓞 E)} ≤ d.I := h1 ▸ Ideal.mul_le_left
  exact hI (this (Ideal.subset_span rfl))

omit [IsCMField E] in
/- English proof (translation)
Introduce `hb`. Take `⟨u, v, huv⟩ : IsCoprime (a : 𝓞 E) (b : 𝓞 E)` from `Nat.Coprime.cast hab`. Conclude with `hP ((Ideal.eq_top_iff_one _).2 (huv ▸ P.add_mem (P.mul_mem_left _ ha) (P.mul_mem_left _ hb)))`.
-/
theorem not_both {a b : ℕ} (hab : Nat.Coprime a b) {P : Ideal (𝓞 E)} (hP : P ≠ ⊤) (ha : (a : 𝓞 E) ∈ P) :
    (b : 𝓞 E) ∉ P := by
  intro hb
  obtain ⟨u, v, huv⟩ : IsCoprime (a : 𝓞 E) (b : 𝓞 E) := Nat.Coprime.cast hab
  exact hP ((Ideal.eq_top_iff_one _).2 (huv ▸ P.add_mem (P.mul_mem_left _ ha) (P.mul_mem_left _ hb)))

/- English proof (translation)
The claim follows from `not_both h.2.2.1 hP (pd_mem d h hI)`.
-/
theorem level_not_mem (d : DeltaDat Xo c n) (h : d.IsLev) {P : Ideal (𝓞 E)} (hP : P ≠ ⊤) (hI : d.I ≤ P) :
    (l.M : 𝓞 E) ∉ P := not_both h.2.2.1 hP (pd_mem d h hI)

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Establish `h1 : d.l₂.Mb ≤ P` using `by rw [h.2.2.2.1]; exact Ideal.mul_le_right.trans hI`. Establish `h2 : d.l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ P`. Rewrite using `[d.l₂.fromK, Ideal.map_span, Ideal.span_le]`.

Introduce and unpack `_ ⟨a, ⟨ha, hk⟩, rfl⟩`. Conclude with `hne a hk (h1 ha)`. Conclude with `hP (top_le_iff.1 (d.l₂.coprime ▸ sup_le h1 h2))`.
-/
theorem split_below (d : DeltaDat Xo c n) (h : d.IsLev) {P : Ideal (𝓞 E)} (hP : P ≠ ⊤) (hI : d.I ≤ P) :
    ∃ a ∈ Algebra.adjoin ℤ {H.w0}, a ∈ P ∧ H.bar a ∉ P := by
  by_contra hne
  push Not at hne
  have h1 : d.l₂.Mb ≤ P := by rw [h.2.2.2.1]; exact Ideal.mul_le_right.trans hI
  have h2 : d.l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ P := by
    rw [d.l₂.fromK, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨a, ⟨ha, hk⟩, rfl⟩
    exact hne a hk (h1 ha)
  exact hP (top_le_iff.1 (d.l₂.coprime ▸ sup_le h1 h2))

/- English proof (translation)
Establish `h1 : q ∣ d.pd`. Assume the negation of the conclusion as `hne`. Conclude with `not_both ((Nat.Prime.coprime_iff_not_dvd hq).2 hne) hP hqP (pd_mem d h hI)`. Establish `h2 : zeta q ∈ c.F` using `GlobalTheory.CoeffRingTest.zeta_mem_of_dvd (GlobalTheory.LevelCoverDatum.pd_pos d h).ne' h1 (GlobalTheory.CoeffRingTest.zeta_pd_mem d h)`. Use `⟨h1, h2, ?_⟩` and prove the remaining obligations.

Use `c.fin` as an intermediate fact. Establish `hle : (minpoly ℚ (⟨_, h2⟩ : c.F)).natDegree ≤ Module.finrank ℚ c.F` using `minpoly.natDegree_le _`. Establish `he : minpoly ℚ (zeta q) = minpoly ℚ (⟨_, h2⟩ : c.F)` using `minpoly.algHom_eq c.F.val Subtype.val_injective (⟨_, h2⟩ : c.F)`. Rewrite `hle` using `[← he, ← Polynomial.cyclotomic_eq_minpoly_rat (GlobalTheory.CoeffRingTest.zeta_prim hq.ne_zero) hq.pos, Polynomial.natDegree_cyclotomic, Nat.totient_prime hq]`. Then use the resulting hypothesis.
-/
theorem prime_under (d : DeltaDat Xo c n) (h : d.IsLev) {P : Ideal (𝓞 E)} (hP : P ≠ ⊤) (hI : d.I ≤ P) {q : ℕ}
    (hq : q.Prime) (hqP : (q : 𝓞 E) ∈ P) : q ∣ d.pd ∧ zeta q ∈ c.F ∧ q - 1 ≤ Module.finrank ℚ c.F := by
  have h1 : q ∣ d.pd := by
    by_contra hne
    exact not_both ((Nat.Prime.coprime_iff_not_dvd hq).2 hne) hP hqP (pd_mem d h hI)
  have h2 : zeta q ∈ c.F := GlobalTheory.CoeffRingTest.zeta_mem_of_dvd (GlobalTheory.LevelCoverDatum.pd_pos d h).ne' h1
    (GlobalTheory.CoeffRingTest.zeta_pd_mem d h)
  refine ⟨h1, h2, ?_⟩
  have := c.fin
  have hle : (minpoly ℚ (⟨_, h2⟩ : c.F)).natDegree ≤ Module.finrank ℚ c.F := minpoly.natDegree_le _
  have he : minpoly ℚ (zeta q) = minpoly ℚ (⟨_, h2⟩ : c.F) :=
    minpoly.algHom_eq c.F.val Subtype.val_injective (⟨_, h2⟩ : c.F)
  rwa [← he, ← Polynomial.cyclotomic_eq_minpoly_rat (GlobalTheory.CoeffRingTest.zeta_prim hq.ne_zero) hq.pos,
    Polynomial.natDegree_cyclotomic, Nat.totient_prime hq] at hle

/- English proof (translation)
Use `(Set.finite_Iic (Module.finrank ℚ c.F + 1)).subset ?_` and prove the remaining obligations. Introduce and unpack `q ⟨hq, t, P, hP, hI, hqP⟩`. Use `(prime_under (dδ t) (h t).1 hP hI hq hqP).2.2` as an intermediate fact. Simplify using `only [Set.mem_Iic]`. Use linear arithmetic over natural numbers and integers.
-/
theorem finite_primes {Tup : Type} (dδ : Tup → DeltaDat Xo c n) (h : CovPin Xo c dδ) :
    {q : ℕ | q.Prime ∧ ∃ t, ∃ P : Ideal (𝓞 E), P ≠ ⊤ ∧ (dδ t).I ≤ P ∧ (q : 𝓞 E) ∈ P}.Finite := by
  refine (Set.finite_Iic (Module.finrank ℚ c.F + 1)).subset ?_
  rintro q ⟨hq, t, P, hP, hI, hqP⟩
  have := (prime_under (dδ t) (h t).1 hP hI hq hqP).2.2
  simp only [Set.mem_Iic]
  omega

end Gen

section Row

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

/- English proof (translation)
The claim follows from `have hI := (h.tuple t).half.2.1 PP hPP ⟨level_not_mem _ (h.cov t).1 PP.isPrime.ne_top hI, split_below _ (h.cov t).1 PP.isPrime.ne_top hI, fun _ hq hqP => (prime_under _ (h.cov t).1 PP.isPrime.ne_top hI hq hqP).2⟩`.
-/
theorem pins_force (O : OMDat C R i Tp tup) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ ι x₀} (h : O.Pins κ v₀ ι x₀) (t : Tp)
    (PP : Formalism.L2.DIV.Pl D.host.E) (hPP : PP ∈ R.Q (tup t)) :
    ((C.Q.l.M : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ∧
      (∃ a ∈ Algebra.adjoin ℤ {C.Q.H.w0}, a ∈ PP.asIdeal ∧ C.Q.H.bar a ∉ PP.asIdeal) ∧
      ∀ q : ℕ, q.Prime → (q : 𝓞 D.host.E) ∈ PP.asIdeal → zeta q ∈ O.c'.F ∧ q - 1 ≤ Module.finrank ℚ O.c'.F :=
  have hI := (h.tuple t).half.2.1 PP hPP
  ⟨level_not_mem _ (h.cov t).1 PP.isPrime.ne_top hI, split_below _ (h.cov t).1 PP.isPrime.ne_top hI,
    fun _ hq hqP => (prime_under _ (h.cov t).1 PP.isPrime.ne_top hI hq hqP).2⟩

end Row

end GlobalTheory.Survey.CoverPinCounterexample
