import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.PropagationTheoremGL2
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PreconnectedRankTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ChainedBot
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Seedpt

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.Fr UpperTheory.V.Pr

set_option linter.overlappingInstances false

noncomputable section

/- English proof (translation)
Rewrite `hY` using `[← PrimeSpectrum.zeroLocus_minimalPrimes]`. Take `⟨η, hη, rfl⟩` from `hY`. Conclude with `⟨η, hη, fun _ => Iff.rfl⟩`.
-/
private theorem comp_min {A : Type} [CommRing A] {Y : Set (PrimeSpectrum A)}
    (hY : Y ∈ irreducibleComponents (PrimeSpectrum A)) : ∃ η ∈ minimalPrimes A, ∀ p, p ∈ Y ↔ η ≤ p.asIdeal := by
  rw [← PrimeSpectrum.zeroLocus_minimalPrimes] at hY
  obtain ⟨η, hη, rfl⟩ := hY
  exact ⟨η, hη, fun _ => Iff.rfl⟩

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
  {F : Frame l (ResidueField O)} {C₀ : ℕ}

private def gd (S : Space O F 2) (M : Ideal S.B) : GlobData (PrimeSpectrum S.A) where
  TI := {p | S.u.TI p.asIdeal}
  Good := {p | M ≤ S.π p.asIdeal}
  Core := S.BB
  Cl := {p | p ∈ S.BB ∧ p.asIdeal.IsMaximal}
  EE := ∅

private def ld {S : Space O F 2} (M : Ideal S.B) {x : Ideal S.A} (L : S.Loc x) : LocData L.R where
  D1 := 2 * F.d + 1
  TI := {p | L.ρ.TI p.asIdeal}
  TE := ∅
  Good := {p | M ≤ L.π p.asIdeal}
  Nice := {p | Nice L.ρ p.asIdeal}
  Thick := ∅
  sharp := ⊥

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨fun a => hQ.1.1 (a.trans h), fun a => hQ.1.2 (a.trans h)⟩, fun a => absurd a (by decide)⟩`.
-/
private theorem ti_down {R : Type} [CommRing R] (ρ : NRep F 2 R) {P Q : Ideal R} (h : P ≤ Q) (hQ : ρ.TI Q) :
    ρ.TI P :=
  ⟨⟨fun a => hQ.1.1 (a.trans h), fun a => hQ.1.2 (a.trans h)⟩, fun a => absurd a (by decide)⟩

/- English proof (translation)
Take `⟨hc, ht⟩` from `sharp2 hF S x L hB hx`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `P Q h hP`. Conclude with `le_trans hP (Ideal.comap_mono (Ideal.comap_mono h))`. Introduce `P Q h hQ`.

Conclude with `ti_down _ h hQ`. Introduce `p hp`. Conclude with `Or.inl ⟨hp.off, fun a => absurd a (by decide)⟩`. Introduce `I hI hd`. Take `⟨p, hp, hle⟩` from `exists_nice_prime_above_of_large_dim l O F C₀ 2 hF hB (Or.inl rfl) S x L hx M hM I.asIdeal hI hd`.

Conclude with `⟨⟨p, hp.prime⟩, hp, hle⟩`. Introduce `e he`. Conclude with `absurd he (Set.notMem_empty _)`. Introduce `P _ hP`. Conclude with `hP`.

Introduce `P Q hP hQ`. Establish `key : ∀ q : Ideal L.R, Relation.ReflTransGen (fun P Q => P ∈ (⊥ : Ideal L.R).minimalPrimes ∧ Q ∈ (⊥ : Ideal L.R).minimalPrimes ∧ ((2 * F.d + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (L.R ⧸ (P ⊔ Q))) P.asIdeal q → ∀ Q : PrimeSpectrum L.R, Q.asIdeal = q → Relation.ReflTransGen (ld M L). …`. Introduce `q h`. Proceed by induction on `h with`. Consider the case `refl`.

Introduce `Q hQ`. Rewrite using `[PrimeSpectrum.ext hQ]`. Consider the case `@tail b c _ hbc ih`. Introduce `Q hQ`. Substitute `hQ` using the available equality.

Conclude with `(ih ⟨b, hbc.1.1.1⟩ rfl).tail hbc`. Conclude with `key _ (hc.2 _ hP _ hQ) Q rfl`. Introduce `P hP`. Conclude with `Or.inl (ht _ hP)`. Introduce `p hp hI hG P hP`.

Conclude with `h1 x L p.asIdeal hp hI hG P.asIdeal P.2 hP`. Introduce `p _ he`. Conclude with `absurd he (Set.notMem_empty _)`.
-/
private theorem ld_ok (hF : F.Ok C₀) (hB : F.Big C₀) {S : Space O F 2} {M : Ideal S.B} (hM : S.FinLam M)
    (h1 : P1' S M) {x : Ideal S.A} (hx : ¬ S.u.triP ≤ x) (L : S.Loc x) : (ld M L).Ok := by
  obtain ⟨hc, ht⟩ := sharp2 hF S x L hB hx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P Q h hP
    exact le_trans hP (Ideal.comap_mono (Ideal.comap_mono h))
  · intro P Q h hQ
    exact ti_down _ h hQ
  · intro p hp
    exact Or.inl ⟨hp.off, fun a => absurd a (by decide)⟩
  · intro I hI hd
    obtain ⟨p, hp, hle⟩ := exists_nice_prime_above_of_large_dim l O F C₀ 2 hF hB (Or.inl rfl) S x L hx M hM I.asIdeal hI hd
    exact ⟨⟨p, hp.prime⟩, hp, hle⟩
  · intro e he
    exact absurd he (Set.notMem_empty _)
  · intro P _ hP
    exact hP
  · intro P Q hP hQ
    have key : ∀ q : Ideal L.R, Relation.ReflTransGen
        (fun P Q => P ∈ (⊥ : Ideal L.R).minimalPrimes ∧ Q ∈ (⊥ : Ideal L.R).minimalPrimes ∧
          ((2 * F.d + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (L.R ⧸ (P ⊔ Q))) P.asIdeal q →
        ∀ Q : PrimeSpectrum L.R, Q.asIdeal = q → Relation.ReflTransGen (ld M L).Adj P Q := by
      intro q h
      induction h with
      | refl =>
        intro Q hQ
        rw [PrimeSpectrum.ext hQ]
      | @tail b c _ hbc ih =>
        intro Q hQ
        subst hQ
        exact (ih ⟨b, hbc.1.1.1⟩ rfl).tail hbc
    exact key _ (hc.2 _ hP _ hQ) Q rfl
  · intro P hP
    exact Or.inl (ht _ hP)
  · intro p hp hI hG P hP
    exact h1 x L p.asIdeal hp hI hG P.asIdeal P.2 hP
  · intro p _ he
    exact absurd he (Set.notMem_empty _)

/- English proof (translation)
Establish `: (gd S M).TI = (PrimeSpectrum.zeroLocus (S.u.triP : Set S.A))ᶜ ∩ (PrimeSpectrum.zeroLocus (S.u.triM : Set S.A))ᶜ`. Use extensionality with `p`. Conclude with `⟨fun h => h.1, fun h => ⟨h, fun a => absurd a (by decide)⟩⟩`. Rewrite using `[this]`. Conclude with `(PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl.inter (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl`.
-/
private theorem ti_open (S : Space O F 2) (M : Ideal S.B) : IsOpen (gd S M).TI := by
  have : (gd S M).TI = (PrimeSpectrum.zeroLocus (S.u.triP : Set S.A))ᶜ ∩
      (PrimeSpectrum.zeroLocus (S.u.triM : Set S.A))ᶜ := by
    ext p
    exact ⟨fun h => h.1, fun h => ⟨h, fun a => absurd a (by decide)⟩⟩
  rw [this]
  exact (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl.inter (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl

/- English proof (translation)
Establish `: (gd S M).Good = PrimeSpectrum.zeroLocus (M.map (S.inc : S.B →+* S.A) : Set S.A)`. Use extensionality with `p`. Conclude with `Ideal.map_le_iff_le_comap.symm`. Rewrite using `[this]`. Conclude with `PrimeSpectrum.isClosed_zeroLocus _`.
-/
private theorem good_closed (S : Space O F 2) (M : Ideal S.B) : IsClosed (gd S M).Good := by
  have : (gd S M).Good = PrimeSpectrum.zeroLocus (M.map (S.inc : S.B →+* S.A) : Set S.A) := by
    ext p
    exact Ideal.map_le_iff_le_comap.symm
  rw [this]
  exact PrimeSpectrum.isClosed_zeroLocus _

/- English proof (translation)
Take `⟨hc, ht⟩` from `sharp2 hF S x.asIdeal L hB hx`. Use `letI : Algebra S.A L.R := (L.ι : S.A →+* L.R).toAlgebra`. Use `haveI : Module.Flat S.A L.R := (loc_flat hF (Or.inl rfl) S x.asIdeal L).1`. Establish `ch` using `chartOfFlat (PrimeSpectrum S.A) S.A id Topology.IsOpenEmbedding.id L.R`. Establish `hpt : id (PrimeSpectrum.comap (algebraMap S.A L.R) (closedPoint L.R)) = x` using `PrimeSpectrum.ext L.lies`.

Rewrite `ch` using `[hpt]`. Establish `hr` using `(loc_rho hF (Or.inl rfl) S x.asIdeal L).2.2.1`. Take `⟨a, b, c⟩` from `globOfCharts _ (gd S M) (ti_open S M) (good_closed S M) x L.R _ ch (ld M L) (by`. Use extensionality with `p`. Conclude with `and_congr (and_congr (hr p.asIdeal).1.not (hr p.asIdeal).2.1.not) (imp_congr Iff.rfl (hr p.asIdeal).2.2.not)) rfl (locProp _ _ (ld_ok hF hB hM h1 hx L))`.

Use `⟨a fun P hP => le_trans ?_ (hc.1 P hP), b fun P hP => ht _ hP, c⟩` and prove the remaining obligations. Conclude with `Nat.cast_le.2 (Nat.le_succ _)`.
-/
private theorem at_pt (hF : F.Ok C₀) (hB : F.Big C₀) {S : Space O F 2} {M : Ideal S.B} (hM : S.FinLam M)
    (h1 : P1' S M) {x : PrimeSpectrum S.A} (hx : ¬ S.u.triP ≤ x.asIdeal) (L : S.Loc x.asIdeal) :
    (∀ Y Y', (gd S M).CompI Y → (gd S M).CompI Y' → x ∈ Y → x ∈ Y' → Y ⊆ (gd S M).Good → Y' ⊆ (gd S M).Good) ∧
      (∃ Y, (gd S M).CompI Y ∧ x ∈ Y) ∧
      ((∃ I ∈ (ld M L).Good, I ∈ (ld M L).TI ∧ ((ld M L).D1 : WithBot ℕ∞) ≤ qdim I.asIdeal) →
        ∃ Y, (gd S M).CompI Y ∧ Y ⊆ (gd S M).Good) := by
  obtain ⟨hc, ht⟩ := sharp2 hF S x.asIdeal L hB hx
  letI : Algebra S.A L.R := (L.ι : S.A →+* L.R).toAlgebra
  haveI : Module.Flat S.A L.R := (loc_flat hF (Or.inl rfl) S x.asIdeal L).1
  have ch := chartOfFlat (PrimeSpectrum S.A) S.A id Topology.IsOpenEmbedding.id L.R
  have hpt : id (PrimeSpectrum.comap (algebraMap S.A L.R) (closedPoint L.R)) = x := PrimeSpectrum.ext L.lies
  rw [hpt] at ch
  have hr := (loc_rho hF (Or.inl rfl) S x.asIdeal L).2.2.1
  obtain ⟨a, b, c⟩ := globOfCharts _ (gd S M) (ti_open S M) (good_closed S M) x L.R _ ch (ld M L) (by
    ext p
    exact and_congr (and_congr (hr p.asIdeal).1.not (hr p.asIdeal).2.1.not)
      (imp_congr Iff.rfl (hr p.asIdeal).2.2.not)) rfl (locProp _ _ (ld_ok hF hB hM h1 hx L))
  refine ⟨a fun P hP => le_trans ?_ (hc.1 P hP), b fun P hP => ht _ hP, c⟩
  exact Nat.cast_le.2 (Nat.le_succ _)

end

/- English proof (translation)
Introduce `l _ O _ _ _ _ F C₀ hF hB S M hM h1 hS`. Use `haveI : IsNoetherianRing S.A := (gr_A hF (Or.inl rfl) S).2.2.2.2.2.1`. Establish `hok : (gd S M).Ok`. Use `⟨fun p hp => hp.1, preconnected_rank_two hF S, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `C hC ⟨p, hp, hp'⟩`.

Take `⟨x, ⟨⟨a, -⟩, b⟩, c⟩` from `jac hF (Or.inl rfl) S C hC Set.univ isOpen_univ ⟨p, ⟨hp, trivial⟩, hp'⟩`. Conclude with `⟨x, a, b, c⟩`. Introduce `p hp`. Rewrite using `[mem_closure_iff]`. Introduce `U hU hpU`.

Take `⟨x, ⟨⟨-, a⟩, b⟩, c⟩` from `jac hF (Or.inl rfl) S Set.univ isClosed_univ U hU ⟨p, ⟨trivial, hpU⟩, hp⟩`. Conclude with `⟨x, a, ⟨b, c⟩, Set.notMem_empty _⟩`. Introduce and unpack `Y ⟨hY, p, hp, hpI⟩`. Take `⟨η, hη, hi⟩` from `comp_min hY`. Take `⟨x, -, b, c⟩` from `l41 hF (Or.inl rfl) S η hη.1.1 (min_hom hF (Or.inl rfl) S η hη) fun h => hpI.1.1 (h.trans ((hi p).1 hp))`.

Conclude with `⟨x, (hi x).2 c, b⟩`. Introduce `x hx`. Take `⟨L⟩` from `loc_ex hF (Or.inl rfl) S x.asIdeal hx.2 hx.1.1`. Conclude with `(at_pt hF hB hM h1 hx.1.2 L).1`. Introduce and unpack `x ⟨hx, -⟩`.

Take `⟨L⟩` from `loc_ex hF (Or.inl rfl) S x.asIdeal hx.2 hx.1.1`. Conclude with `(at_pt hF hB hM h1 hx.1.2 L).2.1`. Take `⟨ξ, Z, hξ, hI, hZ, hMZ, hZξ, hd⟩` from `hS`. Take `⟨x, hm, hx, H⟩` from `seedpt hF (Or.inl rfl) S Z ξ hZ hξ hI hZξ`. Take `⟨L⟩` from `loc_ex hF (Or.inl rfl) S x.asIdeal hm hx.1`.

Take `⟨P, hP, hPI, hπ, hdim⟩` from `H L`. Use `(at_pt hF hB hM h1 hx.2 L).2.2 ⟨⟨P, hP⟩, hMZ.trans hπ.ge, hPI, ?_⟩` and prove the remaining obligations. Use `show ((2 * F.d + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (L.R ⧸ P)`. Rewrite using `[hdim, show ringKrullDim (S.B ⧸ Z) = _ from hd]`. Conclude with `(by omega : 2 * F.d + 1 ≤ 1 + 2 * F.d + 1)` after adjusting the coercions.

Introduce `p hp hI`. Conclude with `globProp _ (gd S M) hok (a := ⟨p, hp⟩) hI`.
-/
theorem UpperTheory.V.Pr.components_good_rank_two :
    UpperTheory.V.Pr.PropagationTheoremGL2 := by
  intro l _ O _ _ _ _ F C₀ hF hB S M hM h1 hS
  haveI : IsNoetherianRing S.A := (gr_A hF (Or.inl rfl) S).2.2.2.2.2.1
  have hok : (gd S M).Ok := by
    refine ⟨fun p hp => hp.1, preconnected_rank_two hF S, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro C hC ⟨p, hp, hp'⟩
      obtain ⟨x, ⟨⟨a, -⟩, b⟩, c⟩ := jac hF (Or.inl rfl) S C hC Set.univ isOpen_univ ⟨p, ⟨hp, trivial⟩, hp'⟩
      exact ⟨x, a, b, c⟩
    · intro p hp
      rw [mem_closure_iff]
      intro U hU hpU
      obtain ⟨x, ⟨⟨-, a⟩, b⟩, c⟩ := jac hF (Or.inl rfl) S Set.univ isClosed_univ U hU ⟨p, ⟨trivial, hpU⟩, hp⟩
      exact ⟨x, a, ⟨b, c⟩, Set.notMem_empty _⟩
    · rintro Y ⟨hY, p, hp, hpI⟩
      obtain ⟨η, hη, hi⟩ := comp_min hY
      obtain ⟨x, -, b, c⟩ := l41 hF (Or.inl rfl) S η hη.1.1 (min_hom hF (Or.inl rfl) S η hη)
        fun h => hpI.1.1 (h.trans ((hi p).1 hp))
      exact ⟨x, (hi x).2 c, b⟩
    · intro x hx
      obtain ⟨L⟩ := loc_ex hF (Or.inl rfl) S x.asIdeal hx.2 hx.1.1
      exact (at_pt hF hB hM h1 hx.1.2 L).1
    · rintro x ⟨hx, -⟩
      obtain ⟨L⟩ := loc_ex hF (Or.inl rfl) S x.asIdeal hx.2 hx.1.1
      exact (at_pt hF hB hM h1 hx.1.2 L).2.1
    · obtain ⟨ξ, Z, hξ, hI, hZ, hMZ, hZξ, hd⟩ := hS
      obtain ⟨x, hm, hx, H⟩ := seedpt hF (Or.inl rfl) S Z ξ hZ hξ hI hZξ
      obtain ⟨L⟩ := loc_ex hF (Or.inl rfl) S x.asIdeal hm hx.1
      obtain ⟨P, hP, hPI, hπ, hdim⟩ := H L
      refine (at_pt hF hB hM h1 hx.2 L).2.2 ⟨⟨P, hP⟩, hMZ.trans hπ.ge, hPI, ?_⟩
      show ((2 * F.d + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (L.R ⧸ P)
      rw [hdim, show ringKrullDim (S.B ⧸ Z) = _ from hd]
      exact_mod_cast (by omega : 2 * F.d + 1 ≤ 1 + 2 * F.d + 1)
  intro p hp hI
  exact globProp _ (gd S M) hok (a := ⟨p, hp⟩) hI
