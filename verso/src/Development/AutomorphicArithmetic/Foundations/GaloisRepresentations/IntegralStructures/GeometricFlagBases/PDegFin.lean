import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FlagBasis
open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

/- English proof (translation)
Introduce `hQ hS a9 h1 h2 h5 h6 hR hC l _ k _ _ hk X p hp hproj`. Establish `hprop : IsProper p` using `h1.2 _ p hproj`. Take `⟨r, Y, j, hj, hY⟩` from `hC k p hp hprop`. Establish `hsm : ∀ s, Smooth (j s ≫ p)` using `fun s => by`. Use `hj.1 s` as an intermediate fact.

Use `infer_instance`. Use `choose d hd using fun s => hR k (j s ≫ p) (hsm s) (hY s)`. Establish `hD : ∀ s, KunnethLefschetz.Dual l (d s) (Y s)` using `fun s => by`. Use `hj.1 s` as an intermediate fact. Use `h2 j hj s` as an intermediate fact.

Use `hQ l k hk (d s) (j s ≫ p) ⟨inferInstance, hd s⟩ ?_ (hY s)` and prove the remaining obligations. Take `⟨N, i, hi, e⟩` from `hproj`. Conclude with `⟨N, j s ≫ i, inferInstance, by rw [Category.assoc]; exact congrArg (j s ≫ ·) e⟩`. Establish `hb` using `fun n : ℤ => KunnethLefschetz.sumQ (l := l) h5 h6 hS j hj n`. Use `⟨fun n => ?_, ((2 * Finset.univ.sup d : ℕ) : ℤ), fun n hn => ?_⟩` and prove the remaining obligations.

Use `fun s => (hD s).1 n` as an intermediate fact. Conclude with `FiniteDimensional.of_injective (LinearMap.pi fun s => LateralTheory.EtaleTrace.pb l (j s) n) (hb n).1`. Break down `hn with hn | hn` into its components or cases. Establish `hs : ∀ i, Subsingleton (HtL l i (sch.obj X) n 0)` using `fun i => (a9 (ZMod (l ^ i)) (tw (l ^ i) 0)).1 _ n hn`. Establish `: Subsingleton (Hl l (sch.obj X) n 0)` using `⟨fun a b => Subtype.ext (funext fun i => Subsingleton.elim _ _)⟩`.

Use `infer_instance`. Use `⟨fun x y => (hb n).1 (funext fun s => ((hD s).2.1 n ?_).elim _ _)⟩` and prove the remaining obligations. Establish `: d s ≤ Finset.univ.sup d` using `Finset.le_sup (Finset.mem_univ s)`. Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.Gal.Int.Geo.degFin_of :
    KunnethLefschetz.QDual → CrystallineSemistableComparison.InSum → A9 → KunnethLefschetz.ProjBC → KunnethLefschetz.SumCl → KunnethLefschetz.SumHl → KunnethLefschetz.PiBC → RelDim → CompSum → DegFin := by
  intro hQ hS a9 h1 h2 h5 h6 hR hC l _ k _ _ hk X p hp hproj
  have hprop : IsProper p := h1.2 _ p hproj
  obtain ⟨r, Y, j, hj, hY⟩ := hC k p hp hprop
  have hsm : ∀ s, Smooth (j s ≫ p) := fun s => by
    have := hj.1 s
    infer_instance
  choose d hd using fun s => hR k (j s ≫ p) (hsm s) (hY s)
  have hD : ∀ s, KunnethLefschetz.Dual l (d s) (Y s) := fun s => by
    have := hj.1 s
    have := h2 j hj s
    refine hQ l k hk (d s) (j s ≫ p) ⟨inferInstance, hd s⟩ ?_ (hY s)
    obtain ⟨N, i, hi, e⟩ := hproj
    exact ⟨N, j s ≫ i, inferInstance, by rw [Category.assoc]; exact congrArg (j s ≫ ·) e⟩
  have hb := fun n : ℤ => KunnethLefschetz.sumQ (l := l) h5 h6 hS j hj n
  refine ⟨fun n => ?_, ((2 * Finset.univ.sup d : ℕ) : ℤ), fun n hn => ?_⟩
  · have := fun s => (hD s).1 n
    exact FiniteDimensional.of_injective (LinearMap.pi fun s => LateralTheory.EtaleTrace.pb l (j s) n) (hb n).1
  · rcases hn with hn | hn
    · have hs : ∀ i, Subsingleton (HtL l i (sch.obj X) n 0) := fun i =>
        (a9 (ZMod (l ^ i)) (tw (l ^ i) 0)).1 _ n hn
      have : Subsingleton (Hl l (sch.obj X) n 0) :=
        ⟨fun a b => Subtype.ext (funext fun i => Subsingleton.elim _ _)⟩
      infer_instance
    · refine ⟨fun x y => (hb n).1 (funext fun s => ((hD s).2.1 n ?_).elim _ _)⟩
      have : d s ≤ Finset.univ.sup d := Finset.le_sup (Finset.mem_univ s)
      omega
