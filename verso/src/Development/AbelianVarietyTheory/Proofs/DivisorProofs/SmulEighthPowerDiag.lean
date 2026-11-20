import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory

/- English proof (translation)
Introduce `X₀ X _ _ K hK`. Establish `hsel : ∀ (Y : Type) [AddCommGroup Y] (w : Fin 8) (nu : Fin 8 → Y), (fun u : Fin 8 => ∑ v, (Matrix.of fun (_ : Fin 8) (v : Fin 8) => if v = w then (1:ℤ) else 0) u v • nu v) = fun _ => nu w`. Introduce `Y _ w nu`. Use function extensionality and compare the values at `u`. Simplify using `[Matrix.of_apply]`.

Establish `hc : ∀ (mu : Fin 8 → X₀) (w : Fin 8), K (fun _ => mu w) = fun _ => K mu w`. Introduce `mu w`. Establish `h` using `hK (Matrix.of fun (_ : Fin 8) (v : Fin 8) => if v = w then (1:ℤ) else 0) mu`. Rewrite `h` using `[hsel, hsel]`. Conclude with `h`.

Set `f : X₀ →+ X` to `{ toFun := fun x => K (fun _ => x) 0 map_zero' := by show K 0 0 = 0`. Simplify using the standard rewrite rules. Use the proof step `map_add' := by`. Introduce `x y`. Use `show K ((fun _ => x) + (fun _ => y)) 0 = _`.

Rewrite using `[map_add]`. Use `rfl }`. Establish `hform : ∀ (mu : Fin 8 → X₀) (u : Fin 8), K mu u = f (mu u)`. Introduce `mu u`. Use `show K mu u = K (fun _ => mu u) 0`.

Rewrite using `[hc]`. Establish `inj : Function.Injective f`. Use `(injective_iff_map_eq_zero f).2 fun x hx => ?_` and prove the remaining obligations. Establish `h1 : K (fun _ => x) = 0`. Use function extensionality and compare the values at `u`.

Rewrite using `[hform]`. Conclude with `hx`. Establish `h2 : (fun _ : Fin 8 => x) = 0` using `K.injective (h1.trans (map_zero K).symm)`. Conclude with `congrFun h2 0`. Establish `surj : Function.Surjective f`.

Introduce `y`. Use `⟨K.symm (fun _ => y) 0, ?_⟩` and prove the remaining obligations. Establish `h` using `hform (K.symm fun _ => y) 0`. Rewrite using `[← h]`. Simplify using the standard rewrite rules.

Use `⟨AddEquiv.ofBijective f ⟨inj, surj⟩, fun mu => funext fun u => ?_⟩` and prove the remaining obligations. Conclude with `hform mu u`.
-/
theorem smul_eighth_power_diag : ∀ (X₀ X : Type) [AddCommGroup X₀] [AddCommGroup X] (K : (Fin 8 → X₀) ≃+ (Fin 8 → X)), (∀ (a : Matrix (Fin 8) (Fin 8) ℤ) (mu : Fin 8 → X₀), K (fun u => ∑ v, a u v • mu v) = fun u => ∑ v, a u v • K mu v) → ∃ k : X₀ ≃+ X, ∀ mu, K mu = fun u => k (mu u) := by
  intro X₀ X _ _ K hK
  have hsel : ∀ (Y : Type) [AddCommGroup Y] (w : Fin 8) (nu : Fin 8 → Y),
      (fun u : Fin 8 => ∑ v, (Matrix.of fun (_ : Fin 8) (v : Fin 8) => if v = w then (1:ℤ) else 0) u v • nu v)
        = fun _ => nu w := by
    intro Y _ w nu
    funext u
    simp [Matrix.of_apply]
  have hc : ∀ (mu : Fin 8 → X₀) (w : Fin 8), K (fun _ => mu w) = fun _ => K mu w := by
    intro mu w
    have h := hK (Matrix.of fun (_ : Fin 8) (v : Fin 8) => if v = w then (1:ℤ) else 0) mu
    rw [hsel, hsel] at h
    exact h
  let f : X₀ →+ X :=
    { toFun := fun x => K (fun _ => x) 0
      map_zero' := by
        show K 0 0 = 0
        simp
      map_add' := by
        intro x y
        show K ((fun _ => x) + (fun _ => y)) 0 = _
        rw [map_add]
        rfl }
  have hform : ∀ (mu : Fin 8 → X₀) (u : Fin 8), K mu u = f (mu u) := by
    intro mu u
    show K mu u = K (fun _ => mu u) 0
    rw [hc]
  have inj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun x hx => ?_
    have h1 : K (fun _ => x) = 0 := by
      funext u
      rw [hform]
      exact hx
    have h2 : (fun _ : Fin 8 => x) = 0 := K.injective (h1.trans (map_zero K).symm)
    exact congrFun h2 0
  have surj : Function.Surjective f := by
    intro y
    refine ⟨K.symm (fun _ => y) 0, ?_⟩
    have h := hform (K.symm fun _ => y) 0
    rw [← h]
    simp
  refine ⟨AddEquiv.ofBijective f ⟨inj, surj⟩, fun mu => funext fun u => ?_⟩
  exact hform mu u

end GlobalTheory
