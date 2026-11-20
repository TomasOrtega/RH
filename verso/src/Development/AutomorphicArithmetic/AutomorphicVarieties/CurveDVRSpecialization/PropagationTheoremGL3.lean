import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.PropagationTheoremGL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NicePrimeEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ExistsNicePrimeAboveOfLargeDim
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.LocProp
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.GlobProp
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ChartOfFlat
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.GlobOfCharts
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IsInternalCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.MinHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.MonMemPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FibreClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ResEqOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocFlat
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocRho
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ExistsNonzeroLowCocycle
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.KrullDimLtOfNotLeTriangular
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.QuotientHomNonvanishingBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ChainedOfComap
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Seedpt
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.HasObs

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.Fr

namespace UpperTheory.V.Pr

set_option linter.overlappingInstances false

noncomputable section

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
  {F : Frame l (ResidueField O)} {C₀ : ℕ}

private def gd (S : Space O F 3) (M : Ideal S.B) : GlobData (PrimeSpectrum S.A) where
  TI := {p | S.u.TI p.asIdeal}
  Good := {p | M ≤ S.π p.asIdeal}
  Core := S.BB
  Cl := {p | p ∈ S.BB ∧ p.asIdeal.IsMaximal}
  EE := {p | S.u.ee ≤ p.asIdeal}

private def ld {S : Space O F 3} (M : Ideal S.B) {x : Ideal S.A} (L : S.Loc x) (I : Ideal L.R) : LocData L.R where
  D1 := 3 * F.d + 1
  TI := {p | L.ρ.TI p.asIdeal}
  TE := {p | L.ρ.TE p.asIdeal}
  Good := {p | M ≤ L.π p.asIdeal}
  Nice := {p | Nice L.ρ p.asIdeal}
  Thick := {p | Thick L.ρ p.asIdeal}
  sharp := I

/- English proof (translation)
The claim follows from `PrimeSpectrum.isClosed_zeroLocus (I : Set A)`.
-/
private theorem closed_le {A : Type} [CommRing A] (I : Ideal A) : IsClosed {p : PrimeSpectrum A | I ≤ p.asIdeal} :=
  PrimeSpectrum.isClosed_zeroLocus (I : Set A)

/- English proof (translation)
Rewrite `hY` using `[← PrimeSpectrum.zeroLocus_minimalPrimes]`. Take `⟨η, hη, rfl⟩` from `hY`. Conclude with `⟨η, hη, rfl⟩`.
-/
private theorem comp_eq {A : Type} [CommSemiring A] {Y : Set (PrimeSpectrum A)}
    (hY : Y ∈ irreducibleComponents (PrimeSpectrum A)) : ∃ η ∈ minimalPrimes A, Y = {p | η ≤ p.asIdeal} := by
  rw [← PrimeSpectrum.zeroLocus_minimalPrimes] at hY
  obtain ⟨η, hη, rfl⟩ := hY
  exact ⟨η, hη, rfl⟩

/- English proof (translation)
Establish `: (gd S M).TI = ({p : PrimeSpectrum S.A | S.u.triP ≤ p.asIdeal}ᶜ ∩ {p | S.u.triM ≤ p.asIdeal}ᶜ) ∩ {p | S.u.ee ≤ p.asIdeal}ᶜ`. Use extensionality with `p`. Conclude with `⟨fun h => ⟨h.1, h.2 rfl⟩, fun h => ⟨h.1, fun _ => h.2⟩⟩`. Rewrite using `[this]`. Conclude with `((closed_le _).isOpen_compl.inter (closed_le _).isOpen_compl).inter (closed_le _).isOpen_compl`.
-/
private theorem ti_open (S : Space O F 3) (M : Ideal S.B) : IsOpen (gd S M).TI := by
  have : (gd S M).TI = ({p : PrimeSpectrum S.A | S.u.triP ≤ p.asIdeal}ᶜ ∩ {p | S.u.triM ≤ p.asIdeal}ᶜ) ∩
      {p | S.u.ee ≤ p.asIdeal}ᶜ := by
    ext p
    exact ⟨fun h => ⟨h.1, h.2 rfl⟩, fun h => ⟨h.1, fun _ => h.2⟩⟩
  rw [this]
  exact ((closed_le _).isOpen_compl.inter (closed_le _).isOpen_compl).inter (closed_le _).isOpen_compl

/- English proof (translation)
Establish `: (gd S M).Good = {p : PrimeSpectrum S.A | M.map (S.inc : S.B →+* S.A) ≤ p.asIdeal}`. Use extensionality with `p`. Conclude with `Ideal.map_le_iff_le_comap.symm`. Rewrite using `[this]`. Conclude with `closed_le _`.
-/
private theorem good_closed (S : Space O F 3) (M : Ideal S.B) : IsClosed (gd S M).Good := by
  have : (gd S M).Good = {p : PrimeSpectrum S.A | M.map (S.inc : S.B →+* S.A) ≤ p.asIdeal} := by
    ext p
    exact Ideal.map_le_iff_le_comap.symm
  rw [this]
  exact closed_le _

/- English proof (translation)
The claim follows from `Ideal.comap_mono (Ideal.comap_mono h)`.
-/
private theorem π_mono {S : Space O F 3} {x : Ideal S.A} (L : S.Loc x) {P Q : Ideal L.R} (h : P ≤ Q) :
    L.π P ≤ L.π Q := Ideal.comap_mono (Ideal.comap_mono h)

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨hm.1.1, hI.off P hm.1.1 (hP.2 rfl)⟩, fun _ hQ h => hm.2 ⟨hQ.1, bot_le⟩ h⟩`.
-/
private theorem comp_of_ti {S : Space O F 3} {x : Ideal S.A} {L : S.Loc x} {I : Ideal L.R} (hI : L.Sharp I)
    {P : Ideal L.R} (hP : L.ρ.TI P) (hm : P ∈ minimalPrimes L.R) : P ∈ I.minimalPrimes :=
  ⟨⟨hm.1.1, hI.off P hm.1.1 (hP.2 rfl)⟩, fun _ hQ h => hm.2 ⟨hQ.1, bot_le⟩ h⟩

/- English proof (translation)
The claim follows from `le_trans hP (π_mono L h) ti_down _ _ h hQ := ⟨⟨fun h' => hQ.1.1 (h'.trans h), fun h' => hQ.1.2 (h'.trans h)⟩, fun e h' => hQ.2 e (h'.trans h)⟩ nice_type p hp := by by_cases h : L.ρ.ee ≤ p.asIdeal · exact Or.inr ⟨hp.off, rfl, h⟩ · exact Or.inl ⟨hp.off, fun _ => h⟩ nice_good J hJ h …`.
-/
private theorem ld_ok (hF : F.Ok C₀) (hB : F.Big C₀) {S : Space O F 3} {M : Ideal S.B} (hM : S.FinLam M)
    (h1 : P1' S M) (h23 : P23' S M) {I₃ : Ideal S.B} (hI₃ : S.FinLam I₃)
    (hE : ∀ ξ : Ideal S.A, ξ.IsPrime → S.u.TE ξ → I₃ ≤ S.π ξ) {x : Ideal S.A} (hx : ¬ S.u.triP ≤ x) (L : S.Loc x)
    {I : Ideal L.R} (hI : L.Sharp I) : (ld M L I).Ok where
  good_up _ _ h hP := le_trans hP (π_mono L h)
  ti_down _ _ h hQ := ⟨⟨fun h' => hQ.1.1 (h'.trans h), fun h' => hQ.1.2 (h'.trans h)⟩,
    fun e h' => hQ.2 e (h'.trans h)⟩
  nice_type p hp := by
    by_cases h : L.ρ.ee ≤ p.asIdeal
    · exact Or.inr ⟨hp.off, rfl, h⟩
    · exact Or.inl ⟨hp.off, fun _ => h⟩
  nice_good J hJ hd := by
    obtain ⟨p, hp, hle⟩ := exists_nice_prime_above_of_large_dim l O F C₀ 3 hF hB (Or.inr rfl) S x L hx M hM J.asIdeal hJ hd
    exact ⟨⟨p, hp.prime⟩, hp, hle⟩
  nice_thick e he _ J hJ hd := by
    obtain ⟨a, b, c⟩ := (loc_rho hF (Or.inr rfl) S x L).2.2.1 e.asIdeal
    have he' : L.ρ.TE e.asIdeal := he.1
    have h3 : I₃ ≤ L.π e.asIdeal := hE (L.im e.asIdeal) (Ideal.IsPrime.comap _)
      ⟨⟨fun h => he'.1.1 (a.2 h), fun h => he'.1.2 (b.2 h)⟩, rfl, c.1 he'.2.2⟩
    obtain ⟨p, hp, hle⟩ := exists_nice_prime_above_of_large_dim l O F C₀ 3 hF hB (Or.inr rfl) S x L hx I₃ hI₃ J.asIdeal
      (h3.trans (π_mono L hJ)) hd
    exact ⟨⟨p, hp.prime⟩, hp, ⟨hp.off, rfl, he'.2.2.trans (le_trans hJ hle)⟩, hle⟩
  comp P hP hm := comp_of_ti hI hP hm
  chain P Q hP hQ := by
    have key : ∀ q : Ideal L.R, Relation.ReflTransGen
        (fun P Q : Ideal L.R => P ∈ I.minimalPrimes ∧ Q ∈ I.minimalPrimes ∧
          ((3 * F.d + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (L.R ⧸ (P ⊔ Q))) P.asIdeal q →
        ∀ hq : q.IsPrime, Relation.ReflTransGen (ld M L I).Adj P ⟨q, hq⟩ := by
      intro q h
      induction h with
      | refl => exact fun _ => Relation.ReflTransGen.refl
      | tail _ hab ih => exact fun _ => (ih hab.1.1.1).tail hab
    exact key _ (hI.chained.2 _ hP _ hQ) Q.isPrime
  dich P hP := hI.dich _ hP
  p1 p hp hT hG P hle := h1 x L p.asIdeal hp hT hG P.asIdeal P.isPrime hle
  p23 p hp hT q hpq hex P' hle hT' := by
    obtain ⟨P, a, b, c⟩ := hex
    refine h23 x L p.asIdeal q.asIdeal hp hT ?_ ⟨P.asIdeal, P.isPrime, a, b, c⟩ P'.asIdeal P'.isPrime hle hT'
    refine Relation.ReflTransGen.lift PrimeSpectrum.asIdeal ?_ _ _ hpq
    rintro a b ⟨a1, a2, a3, a4, e, e1, -, e2, e3⟩
    exact ⟨a1, a2, a3, a4, e.asIdeal, e.isPrime, e1, e2, e3⟩

/- English proof (translation)
Use `letI : Algebra S.A L.R := (L.ι : S.A →+* L.R).toAlgebra`. Use `haveI : Module.Flat S.A L.R := (loc_flat hF (Or.inr rfl) S _ L).1`. Establish `h` using `chartOfFlat (PrimeSpectrum S.A) S.A id Topology.IsOpenEmbedding.id L.R`. Establish `hx : PrimeSpectrum.comap (algebraMap S.A L.R) (closedPoint L.R) = x` using `PrimeSpectrum.ext L.lies`. Rewrite `h` using `[hx]`.

Conclude with `h`.
-/
private theorem chart_ex (hF : F.Ok C₀) {S : Space O F 3} (x : PrimeSpectrum S.A) (L : S.Loc x.asIdeal) :
    Chart x (PrimeSpectrum.comap (L.ι : S.A →+* L.R)) := by
  letI : Algebra S.A L.R := (L.ι : S.A →+* L.R).toAlgebra
  haveI : Module.Flat S.A L.R := (loc_flat hF (Or.inr rfl) S _ L).1
  have h := chartOfFlat (PrimeSpectrum S.A) S.A id Topology.IsOpenEmbedding.id L.R
  have hx : PrimeSpectrum.comap (algebraMap S.A L.R) (closedPoint L.R) = x := PrimeSpectrum.ext L.lies
  rw [hx] at h
  exact h

/- English proof (translation)
Use extensionality with `P`. Take `⟨a, b, c⟩` from `(loc_rho hF (Or.inr rfl) S x L).2.2.1 P.asIdeal`. Conclude with `⟨fun h => ⟨⟨fun h' => h.1.1 (a.2 h'), fun h' => h.1.2 (b.2 h')⟩, fun e h' => h.2 e (c.2 h')⟩, fun h => ⟨⟨fun h' => h.1.1 (a.1 h'), fun h' => h.1.2 (b.1 h')⟩, fun e h' => h.2 e (c.1 h')⟩⟩`.
-/
private theorem ld_ti (hF : F.Ok C₀) {S : Space O F 3} (M : Ideal S.B) {x : Ideal S.A} (L : S.Loc x) (I : Ideal L.R) :
    (ld M L I).TI = PrimeSpectrum.comap (L.ι : S.A →+* L.R) ⁻¹' (gd S M).TI := by
  ext P
  obtain ⟨a, b, c⟩ := (loc_rho hF (Or.inr rfl) S x L).2.2.1 P.asIdeal
  exact ⟨fun h => ⟨⟨fun h' => h.1.1 (a.2 h'), fun h' => h.1.2 (b.2 h')⟩, fun e h' => h.2 e (c.2 h')⟩,
    fun h => ⟨⟨fun h' => h.1.1 (a.1 h'), fun h' => h.1.2 (b.1 h')⟩, fun e h' => h.2 e (c.1 h')⟩⟩

/- English proof (translation)
Take `⟨hY, y, hy, hT⟩` from `hY`. Take `⟨η, hη, hYη⟩` from `comp_eq hY`. Establish `hT' : ¬ S.u.triP ≤ y.asIdeal` using `hT.1.1`. Rewrite `hy`, the goal using `[hYη]`. Establish `hy' : η ≤ y.asIdeal` using `hy`.

Establish `hp : η.IsPrime` using `hη.1.1`. Establish `hh : S.IsHom η` using `min_hom hF (Or.inr rfl) S η hη`. Take `⟨x, -, hx, hle⟩` from `l41 hF (Or.inr rfl) S η hp hh fun h => hT' (le_trans h hy')`. Conclude with `⟨x, hle, hx⟩`.
-/
private theorem gd_meets (hF : F.Ok C₀) (S : Space O F 3) (M : Ideal S.B) (Y : Set (PrimeSpectrum S.A))
    (hY : (gd S M).CompI Y) : (Y ∩ S.BB).Nonempty := by
  obtain ⟨hY, y, hy, hT⟩ := hY
  obtain ⟨η, hη, hYη⟩ := comp_eq hY
  have hT' : ¬ S.u.triP ≤ y.asIdeal := hT.1.1
  rw [hYη] at hy ⊢
  have hy' : η ≤ y.asIdeal := hy
  have hp : η.IsPrime := hη.1.1
  have hh : S.IsHom η := min_hom hF (Or.inr rfl) S η hη
  obtain ⟨x, -, hx, hle⟩ := l41 hF (Or.inr rfl) S η hp hh fun h => hT' (le_trans h hy')
  exact ⟨x, hle, hx⟩

/- English proof (translation)
Establish `h3 : (3 : ℕ) = 2 ∨ (3 : ℕ) = 3` using `Or.inr rfl`. Establish `hloc : ∀ x ∈ (gd S M).Cl, ∃ (L : S.Loc x.asIdeal) (I : Ideal L.R), L.Sharp I ∧ (ld M L I).Concl`. Introduce `x hx`. Take `⟨L⟩` from `loc_ex hF h3 S x.asIdeal hx.2 hx.1.1`. Take `⟨I, hI⟩` from `sharp3 hF S _ L hB hx.1.2`.

Use `haveI : IsNoetherianRing L.R := L.co.toIsNoetherian`. Conclude with `⟨L, I, hI, locProp _ _ (ld_ok hF hB hM h1 h23 hI₃ hE hx.1.2 L hI)⟩`. Take `⟨-, hconn, hdense⟩` from `preconnected_rank_three hF S`. Use `⟨fun _ h => h.1, hconn, fun C hC hne => ?_, ?_, fun Y hY => ?_, fun x hx Y Y' hY hY' hxY hxY' hG => ?_, fun x hx => ?_, ?_⟩` and prove the remaining obligations. Take `⟨x, hx, hm⟩` from `jac hF h3 S C hC Set.univ isOpen_univ (by rwa [Set.inter_univ])`.

Conclude with `⟨x, hx.1.1, hx.2, hm⟩`. Use `hdense.trans (closure_minimal ?_ isClosed_closure)` and prove the remaining obligations. Introduce `p hp`. Rewrite using `[mem_closure_iff]`. Introduce `U hU hpU`.

Take `⟨x, hx, hm⟩` from `jac hF h3 S Set.univ isClosed_univ (U ∩ {p | S.u.ee ≤ p.asIdeal}ᶜ) (hU.inter (closed_le _).isOpen_compl) ⟨p, ⟨trivial, hpU, hp.2⟩, hp.1⟩`. Conclude with `⟨x, hx.1.2.1, ⟨hx.2, hm⟩, hx.1.2.2⟩`. Conclude with `gd_meets hF S M Y hY`. Take `⟨L, I, hI, hc⟩` from `hloc x hx`. Establish `hch` using `chart_ex hF x L`.

Establish `hgen : ∀ Z, (gd S M).CompI Z → x ∈ Z → ∃ P : PrimeSpectrum L.R, P.asIdeal ∈ minimalPrimes L.R ∧ P ∈ (ld M L I).TI ∧ closure {PrimeSpectrum.comap (L.ι : S.A →+* L.R) P} = Z`. Introduce `Z hZ hxZ`. Take `⟨P, hP, rfl⟩` from `hch.onto Z hZ.1 hxZ`. Use `⟨P, hP, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[ld_ti hF]`.

Take `⟨y, hy, hT⟩` from `hZ.2`. Take `⟨z, hz, rfl⟩` from `mem_closure_iff.1 hy _ (ti_open S M) hT`. Conclude with `hz`. Take `⟨P, hP, hT, rfl⟩` from `hgen Y hY hxY`. Take `⟨P', hP', hT', rfl⟩` from `hgen Y' hY' hxY'`.

Use `closure_minimal (Set.singleton_subset_iff.2 ?_) (good_closed S M)` and prove the remaining obligations. Use `hc P (hG (subset_closure rfl)) hT (le_trans ?_ (hI.chained.1 _ (comp_of_ti hI hT hP))) P' hT' hP'` and prove the remaining obligations. Conclude with `Nat.cast_le.2 (Nat.le_succ _)`. Take `⟨L, I, hI, hc⟩` from `hloc x hx.1 haveI : IsNoetherianRing L.R := L.co.toIsNoetherian`. Use `(globOfCharts _ (gd S M) (ti_open S M) (good_closed S M) x L.R _ (chart_ex hF x L) (ld M L I) (ld_ti hF M L I) rfl hc).2.1 fun P hP => ?_` and prove the remaining obligations.

Establish `hI0 : I = ⊥` using `hI.triv hx.2`. Use `(hI.dich P.asIdeal (hI0 ▸ hP)).resolve_right fun h => hx.2 ?_` and prove the remaining obligations. Conclude with `(((loc_rho hF h3 S _ L).2.2.1 P.asIdeal).2.2.1 h.1.2.2).trans ((Ideal.comap_mono (le_maximalIdeal P.isPrime.ne_top)).trans L.lies.le)`. Take `⟨ξ, Z, hξ, hT, hZ, hMZ, hle, hd⟩` from `hs`. Take `⟨x, hm, hx, h⟩` from `seedpt hF h3 S Z ξ hZ hξ hT hle`.

Take `⟨L, I, hI, hc⟩` from `hloc x ⟨hx, hm⟩`. Use `haveI : IsNoetherianRing L.R := L.co.toIsNoetherian`. Take `⟨P, hP, hPT, hπ, hdim⟩` from `h L`. Use `(globOfCharts _ (gd S M) (ti_open S M) (good_closed S M) x L.R _ (chart_ex hF x L) (ld M L I) (ld_ti hF M L I) rfl hc).2.2 ⟨⟨P, hP⟩, hMZ.trans hπ.ge, hPT, ?_⟩` and prove the remaining obligations. Use `show ((3 * F.d + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (L.R ⧸ P)`.

Rewrite using `[hdim, show ringKrullDim (S.B ⧸ Z) = _ from hd]`. Establish `: 3 * F.d + 1 ≤ 1 + 3 * F.d + 1` using `by omega`. Conclude with `this` after adjusting the coercions.
-/
private theorem gd_ok (hF : F.Ok C₀) (hB : F.Big C₀) {S : Space O F 3} {M : Ideal S.B} (hM : S.FinLam M)
    (h1 : P1' S M) (h23 : P23' S M) (hs : SeedIn S M) {I₃ : Ideal S.B} (hI₃ : S.FinLam I₃)
    (hE : ∀ ξ : Ideal S.A, ξ.IsPrime → S.u.TE ξ → I₃ ≤ S.π ξ) : (gd S M).Ok := by
  have h3 : (3 : ℕ) = 2 ∨ (3 : ℕ) = 3 := Or.inr rfl
  have hloc : ∀ x ∈ (gd S M).Cl, ∃ (L : S.Loc x.asIdeal) (I : Ideal L.R), L.Sharp I ∧ (ld M L I).Concl := by
    intro x hx
    obtain ⟨L⟩ := loc_ex hF h3 S x.asIdeal hx.2 hx.1.1
    obtain ⟨I, hI⟩ := sharp3 hF S _ L hB hx.1.2
    haveI : IsNoetherianRing L.R := L.co.toIsNoetherian
    exact ⟨L, I, hI, locProp _ _ (ld_ok hF hB hM h1 h23 hI₃ hE hx.1.2 L hI)⟩
  obtain ⟨-, hconn, hdense⟩ := preconnected_rank_three hF S
  refine ⟨fun _ h => h.1, hconn, fun C hC hne => ?_, ?_, fun Y hY => ?_, fun x hx Y Y' hY hY' hxY hxY' hG => ?_,
    fun x hx => ?_, ?_⟩
  · obtain ⟨x, hx, hm⟩ := jac hF h3 S C hC Set.univ isOpen_univ (by rwa [Set.inter_univ])
    exact ⟨x, hx.1.1, hx.2, hm⟩
  · refine hdense.trans (closure_minimal ?_ isClosed_closure)
    intro p hp
    rw [mem_closure_iff]
    intro U hU hpU
    obtain ⟨x, hx, hm⟩ := jac hF h3 S Set.univ isClosed_univ (U ∩ {p | S.u.ee ≤ p.asIdeal}ᶜ)
      (hU.inter (closed_le _).isOpen_compl) ⟨p, ⟨trivial, hpU, hp.2⟩, hp.1⟩
    exact ⟨x, hx.1.2.1, ⟨hx.2, hm⟩, hx.1.2.2⟩
  · exact gd_meets hF S M Y hY
  · obtain ⟨L, I, hI, hc⟩ := hloc x hx
    have hch := chart_ex hF x L
    have hgen : ∀ Z, (gd S M).CompI Z → x ∈ Z → ∃ P : PrimeSpectrum L.R, P.asIdeal ∈ minimalPrimes L.R ∧
        P ∈ (ld M L I).TI ∧ closure {PrimeSpectrum.comap (L.ι : S.A →+* L.R) P} = Z := by
      intro Z hZ hxZ
      obtain ⟨P, hP, rfl⟩ := hch.onto Z hZ.1 hxZ
      refine ⟨P, hP, ?_, rfl⟩
      rw [ld_ti hF]
      obtain ⟨y, hy, hT⟩ := hZ.2
      obtain ⟨z, hz, rfl⟩ := mem_closure_iff.1 hy _ (ti_open S M) hT
      exact hz
    obtain ⟨P, hP, hT, rfl⟩ := hgen Y hY hxY
    obtain ⟨P', hP', hT', rfl⟩ := hgen Y' hY' hxY'
    refine closure_minimal (Set.singleton_subset_iff.2 ?_) (good_closed S M)
    refine hc P (hG (subset_closure rfl)) hT (le_trans ?_ (hI.chained.1 _ (comp_of_ti hI hT hP))) P' hT' hP'
    exact Nat.cast_le.2 (Nat.le_succ _)
  · obtain ⟨L, I, hI, hc⟩ := hloc x hx.1
    haveI : IsNoetherianRing L.R := L.co.toIsNoetherian
    refine (globOfCharts _ (gd S M) (ti_open S M) (good_closed S M) x L.R _ (chart_ex hF x L) (ld M L I)
      (ld_ti hF M L I) rfl hc).2.1 fun P hP => ?_
    have hI0 : I = ⊥ := hI.triv hx.2
    refine (hI.dich P.asIdeal (hI0 ▸ hP)).resolve_right fun h => hx.2 ?_
    exact (((loc_rho hF h3 S _ L).2.2.1 P.asIdeal).2.2.1 h.1.2.2).trans
      ((Ideal.comap_mono (le_maximalIdeal P.isPrime.ne_top)).trans L.lies.le)
  · obtain ⟨ξ, Z, hξ, hT, hZ, hMZ, hle, hd⟩ := hs
    obtain ⟨x, hm, hx, h⟩ := seedpt hF h3 S Z ξ hZ hξ hT hle
    obtain ⟨L, I, hI, hc⟩ := hloc x ⟨hx, hm⟩
    haveI : IsNoetherianRing L.R := L.co.toIsNoetherian
    obtain ⟨P, hP, hPT, hπ, hdim⟩ := h L
    refine (globOfCharts _ (gd S M) (ti_open S M) (good_closed S M) x L.R _ (chart_ex hF x L) (ld M L I)
      (ld_ti hF M L I) rfl hc).2.2 ⟨⟨P, hP⟩, hMZ.trans hπ.ge, hPT, ?_⟩
    show ((3 * F.d + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (L.R ⧸ P)
    rw [hdim, show ringKrullDim (S.B ⧸ Z) = _ from hd]
    have : 3 * F.d + 1 ≤ 1 + 3 * F.d + 1 := by omega
    exact_mod_cast this

end

end UpperTheory.V.Pr

/- English proof (translation)
Introduce `l _ O _ _ _ _ F C₀ hF hB S₂ M₂ hM₂ hG₂ S M hM h1 h23 hs`. Take `⟨I₃, hI₃, hE⟩` from `l53 hF S₂ S M₂ hM₂ hG₂`. Use `haveI : IsNoetherianRing S.A := (gr_A hF (Or.inr rfl) S).2.2.2.2.2.1`. Establish `hG : AllGood S M` using `fun p hp hT => globProp _ (gd S M) (gd_ok hF hB hM h1 h23 hs hI₃ hE) (a := ⟨p, hp⟩) hT`. Use `⟨hG, M ⊓ I₃, ?_, fun p hp ho => ?_⟩` and prove the remaining obligations.

Unfold `Space.FinLam`. Rewrite using `[Ideal.radical_eq_sInf]`. Use `le_sInf fun J hJ => ?_` and prove the remaining obligations. Break down `hJ.2.inf_le.1 (le_sup_left.trans hJ.1) with h | h` into its components or cases. Conclude with `hM.trans (hJ.2.radical_le_iff.2 (sup_le h (le_sup_right.trans hJ.1)))`.

Conclude with `hI₃.trans (hJ.2.radical_le_iff.2 (sup_le h (le_sup_right.trans hJ.1)))`. Break down `Classical.em (S.u.ee ≤ p) with h | h` into its components or cases. Conclude with `inf_le_right.trans (hE p hp ⟨ho, rfl, h⟩)`. Conclude with `inf_le_left.trans (hG p hp ⟨ho, fun _ => h⟩)`.
-/
theorem UpperTheory.V.Pr.components_good_rank_three :
    UpperTheory.V.Pr.PropagationTheoremGL3 := by
  intro l _ O _ _ _ _ F C₀ hF hB S₂ M₂ hM₂ hG₂ S M hM h1 h23 hs
  obtain ⟨I₃, hI₃, hE⟩ := l53 hF S₂ S M₂ hM₂ hG₂
  haveI : IsNoetherianRing S.A := (gr_A hF (Or.inr rfl) S).2.2.2.2.2.1
  have hG : AllGood S M := fun p hp hT =>
    globProp _ (gd S M) (gd_ok hF hB hM h1 h23 hs hI₃ hE) (a := ⟨p, hp⟩) hT
  refine ⟨hG, M ⊓ I₃, ?_, fun p hp ho => ?_⟩
  · unfold Space.FinLam
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun J hJ => ?_
    rcases hJ.2.inf_le.1 (le_sup_left.trans hJ.1) with h | h
    · exact hM.trans (hJ.2.radical_le_iff.2 (sup_le h (le_sup_right.trans hJ.1)))
    · exact hI₃.trans (hJ.2.radical_le_iff.2 (sup_le h (le_sup_right.trans hJ.1)))
  · rcases Classical.em (S.u.ee ≤ p) with h | h
    · exact inf_le_right.trans (hE p hp ⟨ho, rfl, h⟩)
    · exact inf_le_left.trans (hG p hp ⟨ho, fun _ => h⟩)
