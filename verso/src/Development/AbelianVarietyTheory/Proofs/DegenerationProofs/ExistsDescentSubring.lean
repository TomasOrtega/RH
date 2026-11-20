import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex

/- English proof (translation)
Introduce `O F _ _ io hio N A₀ hc hθ hσ hth hψ`. Establish `hθ' : ∀ x y u : A₀, ∃ a : Oˣ, Units.map io.toMonoidHom a = N.θ x y u` using `fun x y u => (hθ x x.2 y y.2 u u.2).imp fun a h => Units.ext h`. Establish `hσ' : ∀ x : A₀, ∃ a : Oˣ, Units.map io.toMonoidHom a = N.σ x` using `fun x => (hσ x x.2).imp fun a h => Units.ext h`. Establish `hth' : ∀ x : A₀, ∃ a : O, io a = N.th x` using `fun x => hth x x.2`. Establish `hψ' : ∀ χ, ∃ a : Oˣ, Units.map io.toMonoidHom a = N.ψ χ` using `fun χ => (hψ χ).imp fun a h => Units.ext h`.

Use `choose θ eθ using hθ'`. Use `choose σ eσ using hσ'`. Use `choose th eth using hth'`. Use `choose ψ eψ using hψ'`. Establish `inj : Function.Injective (Units.map io.toMonoidHom)` using `Units.map_injective hio`.

Set `B₀ : NumB O` to `{ A := A₀ θ := θ cub := { face := fun x y => inj (by rw [eθ, map_one]; exact N.cub.face _ _) s01 := fun x y z => inj (by rw [eθ, eθ]; exact N.cub.s01 _ _ _) s12 := fun x y z => inj (by rw [eθ, eθ]; exact N.cub.s12 _ _ _) coc := fun x x' x'' y => inj (by simp only [map_mul, eθ]; e …`. Set `N₀ : NumD O` to `{ toNumB := B₀ X := N.X c := fun χ => (⟨N.c χ, hc χ⟩ : A₀) c_add := fun a b => Subtype.ext (N.c_add a b) ψ := ψ even := fun χ => inj (by`. Express the relevant statement in the definitionally equal form `Units.map io.toMonoidHom (ψ (-χ) * σ ⟨N.c χ, hc χ⟩) = _`. Simplify using `only [map_mul, eψ, eσ]`. Conclude with `N.even χ)`.

Use `bimult := fun a a' b => inj (by`. Express the relevant statement in the definitionally equal form `Units.map io.toMonoidHom (_ * θ ⟨N.c a, hc a⟩ ⟨N.c a', hc a'⟩ ⟨N.c b, hc b⟩) = _`. Simplify using `only [map_mul, map_div, eψ, eθ]`. Conclude with `N.bimult a a' b) }`. Set `I : NumD.Hom io N₀ N` to `{ φ := A₀.subtype h := fun _ => 1 h_one := rfl θ_eq := fun (x y u : A₀) => by`.

Simplify using `only [mul_one]`. Conclude with `(eθ x y u).symm`. Use `σ_eq := fun (x : A₀) => by`. Simplify using `only [mul_one]`. Conclude with `(eσ x).symm`.

Use `lam := 1`. Use `th_eq := fun (x : A₀) => by`. Simplify using `only [mul_one, Units.val_one, one_mul]`. Conclude with `(eth x).symm`. Use `e := AddEquiv.refl N.X`.

Use `c_eq := fun _ => rfl`. Use `ψ_eq := fun (χ : N.X) => by`. Simplify using `only [mul_one]`. Conclude with `(eψ χ).symm }`. Set `Φ : N₀.Gt →* N.Gt` to `MonoidHom.mk' (fun g => ⟨((show A₀ from g.b) : N.A), fun (χ : N.X) => Units.map io.toMonoidHom (g.s χ), fun (χ χ' : N.X) => by`.

Use `congrArg (Units.map io.toMonoidHom) (g.mult χ χ')` as an intermediate fact. Rewrite `this` using `[map_mul, map_mul]`. Rewrite using `[← this]`. Conclude with `congrArg _ (eθ ⟨N.c χ, hc χ⟩ ⟨N.c χ', hc χ'⟩ g.b).symm⟩)`. Use the proof step `(fun g g' => NumD.Gt.ext rfl (funext fun (χ : N.X) => by`.

Express the relevant statement in the definitionally equal form `Units.map io.toMonoidHom (g.s χ * g'.s χ / θ ⟨N.c χ, hc χ⟩ g.b g'.b) = _`. Rewrite using `[map_div, map_mul, eθ]`. Use the proof step `rfl))`. Establish `Φinj : Function.Injective Φ` using `fun g g' h => NumD.Gt.ext (Subtype.ext (congrArg NumD.Gt.b h)) (funext fun (χ : N.X) => inj (congrArg (fun z : N.Gt => z.s χ) h))`. Establish `Φio : ∀ y : N.X, Φ (N₀.io y) = N.io y` using `fun y => NumD.Gt.ext rfl (funext fun (χ : N.X) => by`.

Express the relevant statement in the definitionally equal form `Units.map io.toMonoidHom (ψ (y + χ) / ψ y / ψ χ) = _`. Rewrite using `[map_div, map_div, eψ, eψ, eψ]`. Use the proof step `rfl)`. Use `⟨N₀, I, rfl, fun k p hb hs => ?_⟩` and prove the remaining obligations. Establish `hs' : ∀ χ, ∃ a : Oˣ, Units.map io.toMonoidHom a = p.1.2.s χ` using `fun χ => (hs χ).imp fun a h => Units.ext h`.

Use `choose s es using hs'`. Set `g₀ : N₀.Gt` to `⟨(⟨p.1.2.b, hb⟩ : A₀), s, fun (χ χ' : N.X) => inj (by`. Express the relevant statement in the definitionally equal form `Units.map io.toMonoidHom (s (χ + χ') * θ ⟨N.c χ, hc χ⟩ ⟨N.c χ', hc χ'⟩ ⟨p.1.2.b, hb⟩) = _`. Simplify using `only [map_mul, es, eθ]`. Conclude with `p.1.2.mult χ χ')⟩`.

Establish `hg : Φ g₀ = p.1.2` using `NumD.Gt.ext rfl (funext fun χ => es χ)`. Use `⟨⟨(p.1.1, g₀), Φinj ?_⟩, rfl, rfl, fun (χ : N.X) => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Φ (g₀ ^ k) = Φ (N₀.io (show N.X from p.1.1.toAdd))`. Rewrite using `[map_pow, hg, Φio]`. Conclude with `p.2`.

Express the relevant statement in the definitionally equal form `p.1.2.s χ * 1 = Units.map io.toMonoidHom (s χ) * 1 * 1`. Rewrite using `[es, mul_one, mul_one]`.
-/
theorem NumD.exists_descent_subring : ∀ (O F : Type) [CommRing O] [CommRing F] (io : O →+* F), Function.Injective io → ∀ (N : NumD F) (A₀ : Subgroup N.A), (∀ χ, N.c χ ∈ A₀) → (∀ x ∈ A₀, ∀ y ∈ A₀, ∀ u ∈ A₀, ∃ a : Oˣ, io a = N.θ x y u) → (∀ x ∈ A₀, ∃ a : Oˣ, io a = N.σ x) → (∀ x ∈ A₀, ∃ a : O, io a = N.th x) → (∀ χ, ∃ a : Oˣ, io a = N.ψ χ) → ∃ (N₀ : NumD O) (I : NumD.Hom io N₀ N), I.lam = 1 ∧ ∀ (k : ℕ) (p : N.QT k), p.1.2.b ∈ A₀ → (∀ χ, ∃ a : Oˣ, io a = p.1.2.s χ) → ∃ p₀ : N₀.QT k, p.1.1.toAdd = I.e p₀.1.1.toAdd ∧ I.Rel p₀.1.2 p.1.2 := by
  intro O F _ _ io hio N A₀ hc hθ hσ hth hψ
  have hθ' : ∀ x y u : A₀, ∃ a : Oˣ, Units.map io.toMonoidHom a = N.θ x y u := fun x y u =>
    (hθ x x.2 y y.2 u u.2).imp fun a h => Units.ext h
  have hσ' : ∀ x : A₀, ∃ a : Oˣ, Units.map io.toMonoidHom a = N.σ x := fun x =>
    (hσ x x.2).imp fun a h => Units.ext h
  have hth' : ∀ x : A₀, ∃ a : O, io a = N.th x := fun x => hth x x.2
  have hψ' : ∀ χ, ∃ a : Oˣ, Units.map io.toMonoidHom a = N.ψ χ := fun χ =>
    (hψ χ).imp fun a h => Units.ext h
  choose θ eθ using hθ'
  choose σ eσ using hσ'
  choose th eth using hth'
  choose ψ eψ using hψ'
  have inj : Function.Injective (Units.map io.toMonoidHom) := Units.map_injective hio
  let B₀ : NumB O :=
    { A := A₀
      θ := θ
      cub :=
        { face := fun x y => inj (by rw [eθ, map_one]; exact N.cub.face _ _)
          s01 := fun x y z => inj (by rw [eθ, eθ]; exact N.cub.s01 _ _ _)
          s12 := fun x y z => inj (by rw [eθ, eθ]; exact N.cub.s12 _ _ _)
          coc := fun x x' x'' y => inj (by simp only [map_mul, eθ]; exact N.cub.coc _ _ _ _) }
      σ := σ
      σ_one := inj (by rw [eσ, map_one]; exact N.σ_one)
      σ_mul := fun x y => inj (by simp only [map_mul, eθ, eσ]; exact N.σ_mul _ _)
      th := th }
  let N₀ : NumD O :=
    { toNumB := B₀
      X := N.X
      c := fun χ => (⟨N.c χ, hc χ⟩ : A₀)
      c_add := fun a b => Subtype.ext (N.c_add a b)
      ψ := ψ
      even := fun χ => inj (by
        change Units.map io.toMonoidHom (ψ (-χ) * σ ⟨N.c χ, hc χ⟩) = _
        simp only [map_mul, eψ, eσ]; exact N.even χ)
      bimult := fun a a' b => inj (by
        change Units.map io.toMonoidHom (_ * θ ⟨N.c a, hc a⟩ ⟨N.c a', hc a'⟩ ⟨N.c b, hc b⟩) = _
        simp only [map_mul, map_div, eψ, eθ]; exact N.bimult a a' b) }
  let I : NumD.Hom io N₀ N :=
    { φ := A₀.subtype
      h := fun _ => 1
      h_one := rfl
      θ_eq := fun (x y u : A₀) => by
        simp only [mul_one]; exact (eθ x y u).symm
      σ_eq := fun (x : A₀) => by
        simp only [mul_one]; exact (eσ x).symm
      lam := 1
      th_eq := fun (x : A₀) => by
        simp only [mul_one, Units.val_one, one_mul]; exact (eth x).symm
      e := AddEquiv.refl N.X
      c_eq := fun _ => rfl
      ψ_eq := fun (χ : N.X) => by
        simp only [mul_one]; exact (eψ χ).symm }
  let Φ : N₀.Gt →* N.Gt := MonoidHom.mk'
    (fun g => ⟨((show A₀ from g.b) : N.A), fun (χ : N.X) => Units.map io.toMonoidHom (g.s χ), fun (χ χ' : N.X) => by
      have := congrArg (Units.map io.toMonoidHom) (g.mult χ χ')
      rw [map_mul, map_mul] at this
      rw [← this]
      exact congrArg _ (eθ ⟨N.c χ, hc χ⟩ ⟨N.c χ', hc χ'⟩ g.b).symm⟩)
    (fun g g' => NumD.Gt.ext rfl (funext fun (χ : N.X) => by
      change Units.map io.toMonoidHom (g.s χ * g'.s χ / θ ⟨N.c χ, hc χ⟩ g.b g'.b) = _
      rw [map_div, map_mul, eθ]; rfl))
  have Φinj : Function.Injective Φ := fun g g' h =>
    NumD.Gt.ext (Subtype.ext (congrArg NumD.Gt.b h))
      (funext fun (χ : N.X) => inj (congrArg (fun z : N.Gt => z.s χ) h))
  have Φio : ∀ y : N.X, Φ (N₀.io y) = N.io y := fun y =>
    NumD.Gt.ext rfl (funext fun (χ : N.X) => by
      change Units.map io.toMonoidHom (ψ (y + χ) / ψ y / ψ χ) = _
      rw [map_div, map_div, eψ, eψ, eψ]; rfl)
  refine ⟨N₀, I, rfl, fun k p hb hs => ?_⟩
  have hs' : ∀ χ, ∃ a : Oˣ, Units.map io.toMonoidHom a = p.1.2.s χ := fun χ =>
    (hs χ).imp fun a h => Units.ext h
  choose s es using hs'
  let g₀ : N₀.Gt := ⟨(⟨p.1.2.b, hb⟩ : A₀), s, fun (χ χ' : N.X) => inj (by
    change Units.map io.toMonoidHom (s (χ + χ') * θ ⟨N.c χ, hc χ⟩ ⟨N.c χ', hc χ'⟩ ⟨p.1.2.b, hb⟩) = _
    simp only [map_mul, es, eθ]; exact p.1.2.mult χ χ')⟩
  have hg : Φ g₀ = p.1.2 := NumD.Gt.ext rfl (funext fun χ => es χ)
  refine ⟨⟨(p.1.1, g₀), Φinj ?_⟩, rfl, rfl, fun (χ : N.X) => ?_⟩
  · change Φ (g₀ ^ k) = Φ (N₀.io (show N.X from p.1.1.toAdd))
    rw [map_pow, hg, Φio]; exact p.2
  · change p.1.2.s χ * 1 = Units.map io.toMonoidHom (s χ) * 1 * 1
    rw [es, mul_one, mul_one]

end GlobalTheory.Ex
