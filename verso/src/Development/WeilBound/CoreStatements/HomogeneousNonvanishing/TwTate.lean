import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

/- English proof (translation)
Introduce `E _ _ _ H D g a k _ Q _ act e I`. Establish `ev_nsmul : ∀ (n : ℕ), 0 < n → ∀ y : D.La, I.ev n (n • y) = 1` using `fun n hn y => (I.ker n hn (n • y)).mpr ⟨y, rfl⟩`. Establish `ev_split : ∀ (n : ℕ), 0 < n → ∀ (c : D.La) (f : TwMod g.s D.La), I.ev n (((a.a n c + n • f : TwMod g.s D.La)) : D.La) = I.ev n (a.a n c)`. Introduce `n hn c f`. Establish `h1 : I.ev n (((a.a n c + n • f : TwMod g.s D.La)) : D.La) = I.ev n (a.a n c) * I.ev n (n • (f : D.La))` using `I.add n _ _`.

Establish `h0 : I.ev n (n • (f : D.La)) = 1` using `ev_nsmul n hn f`. Conclude with `h1.trans ((congrArg (fun q => I.ev n (a.a n c) * q) h0).trans (_root_.mul_one _))`. Use `⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow, ev := fun n x => I.ev n (a.a n x), add := ?_, lin := ?_, ker := ?_, onto := ?_, tower := ?_, isom := ?_ }, rfl, fun _ _ => rfl⟩` and prove the remaining obligations. Introduce `n x y`. Rewrite using `[map_add]`.

Conclude with `I.add n _ _`. Introduce `n c x`. Rewrite using `[map_smul]`. Conclude with `I.lin n (g.s c) (a.a n x)`. Introduce `n hn x`.

Conclude with `(I.ker n hn (a.a n x)).trans (a.inj n hn x)`. Introduce `n hn x`. Use `(I.onto n hn x).trans ⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨b, rfl⟩`. Take `⟨c, f, hb⟩` from `a.surj n hn b`.

Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `h3 : I.ev n b = I.ev n (((a.a n c + n • f : TwMod g.s D.La)) : D.La)`. Rewrite using `[hb]`. Conclude with `(ev_split n hn c f).symm.trans h3.symm`. Introduce and unpack `⟨c, rfl⟩`.

Conclude with `⟨_, rfl⟩`. Introduce `n m hn hm x`. Take `⟨f, hf⟩` from `a.compat n m hn hm x`. Establish `h4 : I.ev (n * m) (a.a (n * m) x) ^ m = I.ev n (a.a (n * m) x)` using `I.tower n m hn hm _`. Establish `h5 : I.ev n (a.a (n * m) x) = I.ev n (((a.a n x + n • f : TwMod g.s D.La)) : D.La)`.

Rewrite using `[hf]`. Conclude with `h4.trans (h5.trans (ev_split n hn x f))`. Introduce `n hn x y`. Establish `h` using `I.isom n hn (a.a n x) (a.a n y)`. Take `⟨t, ht⟩` from `a.isom n hn x y`.

Establish `hpow : I.ζ n ^ n = 1` using `(I.ζ_prim n hn).pow_eq_one`. Establish `heq : I.ζ n ^ (D.EF (a.a n x : D.La)) (a.a n y : D.La) = I.ζ n ^ (D.EF x) y`. Establish `h2 : (D.EF (a.a n x : D.La)) (a.a n y : D.La) = (D.EF x) y + (n : ℤ) * t`. Establish `: (twForm D g ((a.a n) x)) ((a.a n) y) = (D.EF (a.a n x : D.La)) (a.a n y : D.La)` using `rfl`. Rewrite using `[← this]`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[h2, zpow_add, zpow_mul, zpow_natCast, hpow, one_zpow, _root_.mul_one]`. Use `show e n (I.ev n (a.a n x)) (I.ev n (a.a n y)) (I.ζ n ^ (D.EF x) y)`. Rewrite using `[← heq]`. Conclude with `h`.
-/
theorem tw_tate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : HostAut H) (a : TwIso D g) (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop) (I : TateIso D k Q act e), ∃ J : TateIso D k Q (fun c y => act (g.s c) y) e, J.ζ = I.ζ ∧ ∀ n x, J.ev n x = I.ev n (a.a n x) := by
  intro E _ _ _ H D g a k _ Q _ act e I
  have ev_nsmul : ∀ (n : ℕ), 0 < n → ∀ y : D.La, I.ev n (n • y) = 1 := fun n hn y =>
    (I.ker n hn (n • y)).mpr ⟨y, rfl⟩
  have ev_split : ∀ (n : ℕ), 0 < n → ∀ (c : D.La) (f : TwMod g.s D.La),
      I.ev n (((a.a n c + n • f : TwMod g.s D.La)) : D.La) = I.ev n (a.a n c) := by
    intro n hn c f
    have h1 : I.ev n (((a.a n c + n • f : TwMod g.s D.La)) : D.La) = I.ev n (a.a n c) * I.ev n (n • (f : D.La)) :=
      I.add n _ _
    have h0 : I.ev n (n • (f : D.La)) = 1 := ev_nsmul n hn f
    exact h1.trans ((congrArg (fun q => I.ev n (a.a n c) * q) h0).trans (_root_.mul_one _))
  refine ⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow,
            ev := fun n x => I.ev n (a.a n x),
            add := ?_, lin := ?_, ker := ?_, onto := ?_, tower := ?_, isom := ?_ }, rfl, fun _ _ => rfl⟩
  · intro n x y
    rw [map_add]
    exact I.add n _ _
  · intro n c x
    rw [map_smul]
    exact I.lin n (g.s c) (a.a n x)
  · intro n hn x
    exact (I.ker n hn (a.a n x)).trans (a.inj n hn x)
  · intro n hn x
    refine (I.onto n hn x).trans ⟨?_, ?_⟩
    · rintro ⟨b, rfl⟩
      obtain ⟨c, f, hb⟩ := a.surj n hn b
      refine ⟨c, ?_⟩
      have h3 : I.ev n b = I.ev n (((a.a n c + n • f : TwMod g.s D.La)) : D.La) := by
        rw [hb]
      exact (ev_split n hn c f).symm.trans h3.symm
    · rintro ⟨c, rfl⟩
      exact ⟨_, rfl⟩
  · intro n m hn hm x
    obtain ⟨f, hf⟩ := a.compat n m hn hm x
    have h4 : I.ev (n * m) (a.a (n * m) x) ^ m = I.ev n (a.a (n * m) x) := I.tower n m hn hm _
    have h5 : I.ev n (a.a (n * m) x) = I.ev n (((a.a n x + n • f : TwMod g.s D.La)) : D.La) := by
      rw [hf]
    exact h4.trans (h5.trans (ev_split n hn x f))
  · intro n hn x y
    have h := I.isom n hn (a.a n x) (a.a n y)
    obtain ⟨t, ht⟩ := a.isom n hn x y
    have hpow : I.ζ n ^ n = 1 := (I.ζ_prim n hn).pow_eq_one
    have heq : I.ζ n ^ (D.EF (a.a n x : D.La)) (a.a n y : D.La) = I.ζ n ^ (D.EF x) y := by
      have h2 : (D.EF (a.a n x : D.La)) (a.a n y : D.La) = (D.EF x) y + (n : ℤ) * t := by
        have : (twForm D g ((a.a n) x)) ((a.a n) y) = (D.EF (a.a n x : D.La)) (a.a n y : D.La) := rfl
        rw [← this]
        linarith
      rw [h2, zpow_add, zpow_mul, zpow_natCast, hpow, one_zpow, _root_.mul_one]
    show e n (I.ev n (a.a n x)) (I.ev n (a.a n y)) (I.ζ n ^ (D.EF x) y)
    rw [← heq]
    exact h

end PositivityTheory.UnitarySelfGeneration
