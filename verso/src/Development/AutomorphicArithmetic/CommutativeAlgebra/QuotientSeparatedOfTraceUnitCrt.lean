import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel

open UpperTheory.Gal.Int.Geo
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo

/- English proof (translation)
The claim follows from `AddSubgroup.subset_closure ⟨1, x, fun v => by rw [map_one]; exact one_mem _, rfl⟩`.
-/
private theorem inAf_mem {p : ℕ} [Fact p.Prime] (D : Datum p) (x : D.La) : inAf D x ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, x, fun v => by rw [map_one]; exact one_mem _, rfl⟩

/- English proof (translation)
Introduce `hGP hQC hQI hQU hTE hTP hTU hCRT`. Introduce `p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hLev N c a hNum C u hu W Ω _ _ z hz`. Establish `huN : L.CongOne S.N₀ u ∧ L.CongOne S.N₀ u⁻¹` using `hu`. Establish `hu1 : u ∈ L.KN 1` using `KN_anti (one_dvd _) hu`. Establish `hInt : Integ L u` using `integ_of_mem hu1`.

Rewrite using `[hLev]`. Use `⟨hu1, ?_⟩` and prove the remaining obligations. Rewrite using `[S.lev]`. Take `⟨hcrt1, hcrt2⟩` from `hCRT p D G L q r S.N₀ S.𝔞 S.std.cop S.upow u hInt`. Rewrite using `[hcrt1]`.

Use `⟨huN.1, ?_⟩` and prove the remaining obligations. Establish `hNpos : 0 < (N : ℕ)`. Use `N.2.1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[hcrt2 a N hNpos N.2.2 hNum.2]`.

Introduce `y`. Use `set x := (algebraMap (𝓞 D.F) D.O a) • y with hx`. Use `(hTP p D G L E gb u (T.M N).X (T.M N).s N N (T.M N).univ W.o W.ψ W.trans Ω z x).2 rfl x ?_` and prove the remaining obligations. Establish `ht : (toUnit (Over.mk z)).left = z`. Simplify using `using Over.w (toUnit (Over.mk z))`.

Take `⟨oz, ⟨mz⟩⟩` from `hGP _ _ gb (N : ℕ) (T.M N).X (Sp Ω) (T.M N).s z (T.M N).univ`. Take `⟨nW, hnW⟩` from `(hQC q (datAt S.atq S.sp) (Ow w) E S.b gb N S.N₀ c _ _ _ _ _ _ (T.M N).univ S.Y.univ S.Y.univ C.j (𝟙 _)).2.2.2 _ _ W.o W.π W.φ C.m`. Take `⟨hiso, hlb⟩` from `hTU p D G L E gb u (T.M N).X (T.M N).s N N (T.M N).univ W.o W.ψ W.trans hu1`. Establish `heta : ∀ y' : D.La, (T.M N).univ.eta (c • y') ≫ W.ψ = W.o.eta (c • y')`. Introduce `y'`.

Use `hTE p D G L E gb u (T.M N).X (T.M N).s N N (T.M N).univ W.o W.ψ W.trans S.N₀ c c hNum.1 hNum.1 y' y' ?_` and prove the remaining obligations. Conclude with `huN.1 _ (inAf_mem D y')`. Take `⟨nI, hnI⟩` from `hQI q (datAt S.atq S.sp) (Ow w) E S.b gb N N S.N₀ c c _ _ _ _ (T.M N).univ W.o S.Y.univ _ W.ψ hiso W.trans.1 W.trans.2.1 hlb heta nW`. Take `⟨nA, hnA⟩` from `(hQC q (datAt S.atq S.sp) (Ow w) E S.b gb N S.N₀ c _ _ _ _ _ _ (T.M N).univ S.Y.univ S.Y.univ C.j (𝟙 _)).2.2.2 _ _ oz z mz C.m`. Take `⟨nB, hnB⟩` from `(hQC q (datAt S.atq S.sp) (Ow w) E S.b gb N S.N₀ c _ _ _ _ _ _ (T.M N).univ S.Y.univ S.Y.univ (W.π ≫ C.j) (𝟙 _)).2.2.2 _ _ oz z mz nI`.

Establish `hfeq : z ≫ W.π ≫ C.j = z ≫ C.j` using `hz`. Establish `hAB : mz.φ ≫ Over.Hom.left W.ψ ≫ W.φ.φ ≫ C.m.φ = mz.φ ≫ C.m.φ`. Generalize the expression as in `hF : z ≫ W.π ≫ C.j = F at nB hnB`. Establish `hF' : F = z ≫ C.j` using `hF.symm.trans hfeq`. Substitute `hF'` using the available equality.

Establish `h` using `hQU q (datAt S.atq S.sp) (Ow w) E S.b gb N S.N₀ c S.std.three S.std.cop _ _ _ _ _ _ _ nB nA`. Rewrite `h` using `[hnB, hnI, hnW, hnA]`. Conclude with `h`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `nW.cart.1.hom_ext` to reduce the goal to its premises.

Simplify using `only [Over.comp_left, Category.assoc]`. Rewrite using `[hnW, reassoc_of% (W.φ.eta x)]`. Establish `hl` using `C.lv y`. Establish `hr : Over.Hom.left ((T.M N).univ.eta x) ≫ C.m.φ = C.j ≫ Over.Hom.left (S.Y.lv y)` using `hl`. Establish `hz'` using `mz.eta x`.

Rewrite using `[ht]`. Rewrite using `[← reassoc_of% hz', hAB, reassoc_of% hz', hr, reassoc_of% hfeq]`. Simplify using `only [Over.comp_left, Category.assoc, Over.w]`.
-/
theorem UpperTheory.quotient_separated_of_trace_unit_crt :
    GPull → QComp → QIso → QUniq → TrEta → TrEtaPt → TrUnit → CongCRT → BaseSep := by
  intro hGP hQC hQI hQU hTE hTP hTU hCRT
  intro p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hLev N c a hNum C u hu W Ω _ _ z hz
  have huN : L.CongOne S.N₀ u ∧ L.CongOne S.N₀ u⁻¹ := hu
  have hu1 : u ∈ L.KN 1 := KN_anti (one_dvd _) hu
  have hInt : Integ L u := integ_of_mem hu1
  rw [hLev]
  refine ⟨hu1, ?_⟩
  rw [S.lev]
  obtain ⟨hcrt1, hcrt2⟩ := hCRT p D G L q r S.N₀ S.𝔞 S.std.cop S.upow u hInt
  rw [hcrt1]
  refine ⟨huN.1, ?_⟩
  have hNpos : 0 < (N : ℕ) := by
    have := N.2.1
    omega
  rw [hcrt2 a N hNpos N.2.2 hNum.2]
  intro y
  set x := (algebraMap (𝓞 D.F) D.O a) • y with hx
  refine (hTP p D G L E gb u (T.M N).X (T.M N).s N N (T.M N).univ W.o W.ψ W.trans Ω z x).2 rfl x ?_
  have ht : (toUnit (Over.mk z)).left = z := by
    simpa using Over.w (toUnit (Over.mk z))
  obtain ⟨oz, ⟨mz⟩⟩ := hGP _ _ gb (N : ℕ) (T.M N).X (Sp Ω) (T.M N).s z (T.M N).univ
  obtain ⟨nW, hnW⟩ := (hQC q (datAt S.atq S.sp) (Ow w) E S.b gb N S.N₀ c _ _ _ _ _ _ (T.M N).univ S.Y.univ S.Y.univ C.j (𝟙 _)).2.2.2
    _ _ W.o W.π W.φ C.m
  obtain ⟨hiso, hlb⟩ := hTU p D G L E gb u (T.M N).X (T.M N).s N N (T.M N).univ W.o W.ψ W.trans hu1
  have heta : ∀ y' : D.La, (T.M N).univ.eta (c • y') ≫ W.ψ = W.o.eta (c • y') := by
    intro y'
    refine hTE p D G L E gb u (T.M N).X (T.M N).s N N (T.M N).univ W.o W.ψ W.trans S.N₀ c c hNum.1 hNum.1
      y' y' ?_
    exact huN.1 _ (inAf_mem D y')
  obtain ⟨nI, hnI⟩ := hQI q (datAt S.atq S.sp) (Ow w) E S.b gb N N S.N₀ c c _ _ _ _ (T.M N).univ W.o S.Y.univ _ W.ψ hiso W.trans.1
    W.trans.2.1 hlb heta nW
  obtain ⟨nA, hnA⟩ := (hQC q (datAt S.atq S.sp) (Ow w) E S.b gb N S.N₀ c _ _ _ _ _ _ (T.M N).univ S.Y.univ S.Y.univ C.j (𝟙 _)).2.2.2
    _ _ oz z mz C.m
  obtain ⟨nB, hnB⟩ := (hQC q (datAt S.atq S.sp) (Ow w) E S.b gb N S.N₀ c _ _ _ _ _ _ (T.M N).univ S.Y.univ S.Y.univ (W.π ≫ C.j) (𝟙 _)).2.2.2
    _ _ oz z mz nI
  have hfeq : z ≫ W.π ≫ C.j = z ≫ C.j := hz
  have hAB : mz.φ ≫ Over.Hom.left W.ψ ≫ W.φ.φ ≫ C.m.φ = mz.φ ≫ C.m.φ := by
    generalize hF : z ≫ W.π ≫ C.j = F at nB hnB
    have hF' : F = z ≫ C.j := hF.symm.trans hfeq
    subst hF'
    have h := hQU q (datAt S.atq S.sp) (Ow w) E S.b gb N S.N₀ c S.std.three S.std.cop _ _ _ _ _ _ _ nB nA
    rw [hnB, hnI, hnW, hnA] at h
    exact h
  apply Over.OverMorphism.ext
  apply nW.cart.1.hom_ext
  · simp only [Over.comp_left, Category.assoc]
    rw [hnW, reassoc_of% (W.φ.eta x)]
    have hl := C.lv y
    have hr : Over.Hom.left ((T.M N).univ.eta x) ≫ C.m.φ = C.j ≫ Over.Hom.left (S.Y.lv y) := hl
    have hz' := mz.eta x
    rw [ht]
    rw [← reassoc_of% hz', hAB, reassoc_of% hz', hr, reassoc_of% hfeq]
  · simp only [Over.comp_left, Category.assoc, Over.w]
