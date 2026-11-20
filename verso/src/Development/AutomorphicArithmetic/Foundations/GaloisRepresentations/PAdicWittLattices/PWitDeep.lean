import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

/- English proof (translation)
Introduce `_ hSm hTD hWC hWF p _ D G L R _ _ gb X N' N h hI`. Take `⟨k, hk, hAk, hex⟩` from `hTD p D G L R gb h hI`. Establish `hk0 : 0 < k`. Break down `Nat.eq_zero_or_pos k with rfl | hpos` into its components or cases. Conclude with `absurd (Nat.coprime_zero_left _ |>.mp hk) (Fact.out : p.Prime).one_lt.ne'`.

Conclude with `hpos`. Set `Nk : Lv p` to `⟨↑N * k, le_trans N.2.1 (Nat.le_mul_of_pos_right _ hk0), Nat.Coprime.mul N.2.2 hk⟩`. Set `M : Lv p` to `⟨↑N' * (↑N * k), le_trans Nk.2.1 (Nat.le_mul_of_pos_left _ (by have := N'.2.1; omega)), Nat.Coprime.mul N'.2.2 Nk.2.2⟩`. Establish `hNkM : (↑Nk : ℕ) ∣ ↑M` using `Dvd.intro_left _ rfl`. Use `⟨M, Dvd.intro _ rfl, ?_, ?_⟩` and prove the remaining obligations.

Introduce `u hu`. Conclude with `hAk N u (UpperTheory.Gal.Int.Geo.KN_anti hNkM hu)`. Use `haveI : Smooth (X Nk).s := (hSm p D R gb Nk (X Nk)).1 haveI : IsLocallyNoetherian (X Nk).X := LocallyOfFiniteType.isLocallyNoetherian (X Nk).s`. Take `⟨o, ψ, ht⟩` from `hex N (X Nk).X (X Nk).s (X Nk).univ`. Take `⟨π, ⟨hπ, ⟨φ⟩⟩, -⟩` from `(X N).rep (X Nk).X (X Nk).s o`.

Establish `w₂ : Wit L h (X Nk) (X N) π (ψ.left ≫ φ.φ)` using `⟨hπ, o, ψ, φ, ht, rfl⟩`. Take `⟨c, Φc, w₁, -⟩` from `hWF p D G L R gb Nk M hNkM (X Nk) (X M)`. Use `(hWC p D G L R gb M Nk N (X M) (X Nk) (X N) 1 h).2 hI (hAk N) c Φc π _ w₁ w₂` as an intermediate fact. Rewrite `this` using `[_root_.mul_one]`. Conclude with `⟨_, _, this⟩`.
-/
theorem UpperTheory.Gal.G3.pWitDeep :
    KNBasic → GenSm → TransDeep → WitComp → WitForget → WitDeep := by
  intro _ hSm hTD hWC hWF p _ D G L R _ _ gb X N' N h hI
  obtain ⟨k, hk, hAk, hex⟩ := hTD p D G L R gb h hI
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact absurd (Nat.coprime_zero_left _ |>.mp hk) (Fact.out : p.Prime).one_lt.ne'
    · exact hpos
  let Nk : Lv p := ⟨↑N * k, le_trans N.2.1 (Nat.le_mul_of_pos_right _ hk0), Nat.Coprime.mul N.2.2 hk⟩
  let M : Lv p := ⟨↑N' * (↑N * k), le_trans Nk.2.1 (Nat.le_mul_of_pos_left _ (by have := N'.2.1; omega)),
    Nat.Coprime.mul N'.2.2 Nk.2.2⟩
  have hNkM : (↑Nk : ℕ) ∣ ↑M := Dvd.intro_left _ rfl
  refine ⟨M, Dvd.intro _ rfl, ?_, ?_⟩
  · intro u hu
    exact hAk N u (UpperTheory.Gal.Int.Geo.KN_anti hNkM hu)
  · haveI : Smooth (X Nk).s := (hSm p D R gb Nk (X Nk)).1
    haveI : IsLocallyNoetherian (X Nk).X := LocallyOfFiniteType.isLocallyNoetherian (X Nk).s
    obtain ⟨o, ψ, ht⟩ := hex N (X Nk).X (X Nk).s (X Nk).univ
    obtain ⟨π, ⟨hπ, ⟨φ⟩⟩, -⟩ := (X N).rep (X Nk).X (X Nk).s o
    have w₂ : Wit L h (X Nk) (X N) π (ψ.left ≫ φ.φ) := ⟨hπ, o, ψ, φ, ht, rfl⟩
    obtain ⟨c, Φc, w₁, -⟩ := hWF p D G L R gb Nk M hNkM (X Nk) (X M)
    have := (hWC p D G L R gb M Nk N (X M) (X Nk) (X N) 1 h).2 hI (hAk N) c Φc π _ w₁ w₂
    rw [_root_.mul_one] at this
    exact ⟨_, _, this⟩
