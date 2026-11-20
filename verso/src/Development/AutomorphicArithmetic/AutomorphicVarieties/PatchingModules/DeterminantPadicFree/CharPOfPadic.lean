import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.PhiSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.AcConst
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.SelSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.MaxIndep

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

/- English proof (translation)
Take `⟨p, hp⟩` from `CharP.exists K`. Establish `hpp : p.Prime` using `CharP.char_is_prime K p`. Establish `hpK : ((p : ℕ) : K) = 0` using `CharP.cast_eq_zero K p`. Establish `hpl : p = l`. Assume the negation of the conclusion as `hne`.

Establish `hcop : l.Coprime p` using `(Nat.coprime_primes (Fact.out) hpp).2 (Ne.symm hne)`. Establish `hu : IsUnit ((p : ℕ) : ℤ_[l])` using `PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 hcop)`. Establish `hu'` using `hu.map f`. Rewrite `hu'` using `[map_natCast, hpK]`. Conclude with `not_isUnit_zero hu'`.

Substitute `hpl` using the available equality. Conclude with `hp`.
-/
private theorem charP_of_padic {l : ℕ} [Fact l.Prime] {K : Type} [Field K] [Finite K] (f : ℤ_[l] →+* K) :
    CharP K l := by
  obtain ⟨p, hp⟩ := CharP.exists K
  have hpp : p.Prime := CharP.char_is_prime K p
  have hpK : ((p : ℕ) : K) = 0 := CharP.cast_eq_zero K p
  have hpl : p = l := by
    by_contra hne
    have hcop : l.Coprime p := (Nat.coprime_primes (Fact.out) hpp).2 (Ne.symm hne)
    have hu : IsUnit ((p : ℕ) : ℤ_[l]) :=
      PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 hcop)
    have hu' := hu.map f
    rw [map_natCast, hpK] at hu'
    exact not_isUnit_zero hu'
  subst hpl
  exact hp

/- English proof (translation)
Introduce `l _ F n x hΦ`. Use `letI : Field x.K := x.field`. Use `haveI : Finite x.K := x.fin`. Use `letI : Algebra ℤ_[l] x.K := x.algZ`. Use `haveI : CharP x.K l := charP_of_padic (algebraMap ℤ_[l] x.K)`.

Use `haveI : CompactSpace F.G₀ := isCompact_iff_compactSpace.mp (F.η.ker.isClosed_of_isOpen F.η_open).isCompact`. Establish `hΦ0 : PhiCond F.G₀ l` using `UpperTheory.V.Pa.Det.phiSub l F.η.ker F.η_open hΦ`. Establish `hρ : x.ρX x.A = fun g => mat x.ρ g`. Use function extensionality and compare the values at `g`. Simplify using `[UpperTheory.V.Pa.NP.ρX, Algebra.algebraMap_self]`.

Take `⟨⟨S, hS⟩, ⟨B, hB⟩⟩` from `UpperTheory.V.Pa.Det.selSub F (A := x.A) (R := x.A) x.t (x.ρX x.A) (x.wX x.A) (x.wiX x.A) (Od x.A x.A n x.a)`. Establish `hSfg : S.FG`. Use `UpperTheory.V.Pa.Det.matFg l (K := x.K) (G := F.G₀) (R := x.A) (1 : F.G₀ →* x.A) (mat x.ρ) S hΦ0 ?_ ?_ ?_` and prove the remaining obligations. Introduce `N`. Simplify using `only [MonoidHom.one_apply]`.

Conclude with `IsLocallyConstant.const (X := F.G₀) _`. Introduce `i j`. Establish `h` using `x.cont i j`. Simplify `h` using `[PowerSeries.maximalIdeal_eq_span_X]`. Introduce `z hz`.

Rewrite `hz` using `[← SetLike.mem_coe, hS]`. Use `⟨hz.2.1, ?_⟩` and prove the remaining obligations. Introduce `g _ h _`. Establish `e` using `hz.2.2.1 g h`. Rewrite `e` using `[hρ]`.

Simplify using `using e`. Take `⟨g, κ, hmem, hind, hgen⟩` from `UpperTheory.V.Pa.Det.maxIndep x.t S B PowerSeries.X_irreducible hSfg`. Establish `hsel : ∀ j, κ j ∈ SelZ F x.t (x.ρX x.A) (x.wX x.A) (x.wiX x.A) (Od x.A x.A n x.a)`. Introduce `j`. Rewrite using `[← hS]`.

Conclude with `hmem j`. Establish `hloc : ∀ j v, ∃ Y ∈ Od x.A x.A n x.a, LocAt F (x.ρX x.A) (x.wX x.A) (x.wiX x.A) (κ j) v Y` using `fun j v => (hsel j).2.2.2.2.2 v`. Use `choose Y hYmem hYloc using hloc`. Use `⟨⟨g, κ, hsel, Y, hYmem, hYloc, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `c hc`.

Apply `hind c` to reduce the goal to its premises. Rewrite using `[← SetLike.mem_coe, hB]`. Conclude with `hc`. Introduce `z hz`. Rewrite `hz` using `[← hS]`.

Take `⟨s, c, hsc⟩` from `hgen z hz`. Use `⟨s, c, ?_⟩` and prove the remaining obligations. Rewrite using `[← hB]`. Conclude with `hsc`.
-/
theorem UpperTheory.V.Pa.Det.kapEx :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n), PhiCond F.Γ l → Nonempty (Kap x) := by
  intro l _ F n x hΦ
  letI : Field x.K := x.field
  haveI : Finite x.K := x.fin
  letI : Algebra ℤ_[l] x.K := x.algZ
  haveI : CharP x.K l := charP_of_padic (algebraMap ℤ_[l] x.K)
  haveI : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.mp (F.η.ker.isClosed_of_isOpen F.η_open).isCompact
  have hΦ0 : PhiCond F.G₀ l := UpperTheory.V.Pa.Det.phiSub l F.η.ker F.η_open hΦ
  have hρ : x.ρX x.A = fun g => mat x.ρ g := by
    funext g
    simp [UpperTheory.V.Pa.NP.ρX, Algebra.algebraMap_self]
  obtain ⟨⟨S, hS⟩, ⟨B, hB⟩⟩ := UpperTheory.V.Pa.Det.selSub F (A := x.A) (R := x.A) x.t (x.ρX x.A)
    (x.wX x.A) (x.wiX x.A) (Od x.A x.A n x.a)
  have hSfg : S.FG := by
    refine UpperTheory.V.Pa.Det.matFg l (K := x.K) (G := F.G₀) (R := x.A) (1 : F.G₀ →* x.A) (mat x.ρ) S hΦ0
      ?_ ?_ ?_
    · intro N
      simp only [MonoidHom.one_apply]
      exact IsLocallyConstant.const (X := F.G₀) _
    · intro i j
      have h := x.cont i j
      simpa [PowerSeries.maximalIdeal_eq_span_X] using h
    · intro z hz
      rw [← SetLike.mem_coe, hS] at hz
      refine ⟨hz.2.1, ?_⟩
      intro g _ h _
      have e := hz.2.2.1 g h
      rw [hρ] at e
      simpa using e
  obtain ⟨g, κ, hmem, hind, hgen⟩ :=
    UpperTheory.V.Pa.Det.maxIndep x.t S B PowerSeries.X_irreducible hSfg
  have hsel : ∀ j, κ j ∈ SelZ F x.t (x.ρX x.A) (x.wX x.A) (x.wiX x.A) (Od x.A x.A n x.a) := by
    intro j
    rw [← hS]
    exact hmem j
  have hloc : ∀ j v, ∃ Y ∈ Od x.A x.A n x.a,
      LocAt F (x.ρX x.A) (x.wX x.A) (x.wiX x.A) (κ j) v Y :=
    fun j v => (hsel j).2.2.2.2.2 v
  choose Y hYmem hYloc using hloc
  refine ⟨⟨g, κ, hsel, Y, hYmem, hYloc, ?_, ?_⟩⟩
  · intro c hc
    apply hind c
    rw [← SetLike.mem_coe, hB]
    exact hc
  · intro z hz
    rw [← hS] at hz
    obtain ⟨s, c, hsc⟩ := hgen z hz
    refine ⟨s, c, ?_⟩
    rw [← hB]
    exact hsc
