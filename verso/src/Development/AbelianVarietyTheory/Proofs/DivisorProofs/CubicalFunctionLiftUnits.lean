import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricCocycleTrivialization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalFunctionOfHomomorphism

namespace GlobalTheory

/- English proof (translation)
Introduce `X _ _ _ U V _ _ e he a h3 hneg`. Use `choose f hf using h3`. Use `choose n hn using hneg`. Establish `tA : ∀ {p q : V}, Additive.ofMul p = Additive.ofMul q → p = q` using `fun h => h`. Establish `hfA : ∀ x y w, Additive.ofMul (a (x + y + w)) + Additive.ofMul (a x) + Additive.ofMul (a y) + Additive.ofMul (a w) = Additive.ofMul (e (f x y w)) + (Additive.ofMul (a (x + y)) + Additive.ofMul (a (x + w)) + Additive.ofMul (a (y + w)))` using `fun x y w => by`.

Simplify `congrArg Additive.ofMul (hf x y w)` using `only [ofMul_mul]`. Establish `hnA : ∀ x, Additive.ofMul (a (-x)) = Additive.ofMul (e (n x)) + Additive.ofMul (a x)` using `fun x => by simpa only [ofMul_mul] using congrArg Additive.ofMul (hn x)`. Establish `hs1 : ∀ x y w, f x y w = f y x w` using `fun x y w => by`. Apply `he` to reduce the goal to its premises. Apply `tA` to reduce the goal to its premises.

Establish `h1` using `hfA x y w`. Establish `h2` using `hfA y x w`. Rewrite `h2` using `[add_comm y x]`. Take the linear combination `(norm := module) h2 - h1`. Establish `hs2 : ∀ x y w, f x y w = f x w y` using `fun x y w => by`.

Apply `he` to reduce the goal to its premises. Apply `tA` to reduce the goal to its premises. Establish `h1` using `hfA x y w`. Establish `h2` using `hfA x w y`. Rewrite `h2` using `[add_right_comm x w y, add_comm w y]`.

Take the linear combination `(norm := module) h2 - h1`. Establish `hc : ∀ x x' x'' y, f (x + x') x'' y * f x x' y = f x (x' + x'') y * f x' x'' y`. Introduce `x x' x'' y`. Apply `he` to reduce the goal to its premises. Apply `tA` to reduce the goal to its premises.

Simplify using `only [map_mul, ofMul_mul]`. Establish `h1` using `hfA (x + x') x'' y`. Establish `h2` using `hfA x x' y`. Establish `h3` using `hfA x (x' + x'') y`. Establish `h4` using `hfA x' x'' y`.

Rewrite `h3` using `[← add_assoc x x' x'']`. Take the linear combination `(norm := module) h3 + h4 - h1 - h2`. Take `⟨g, hg⟩` from `GlobalTheory.symm_cubical_cocycle_isThirdDifference X U f hs1 hs2 hc`. Establish `hgA : ∀ x y w, Additive.ofMul (e (f x y w)) + (Additive.ofMul (e (g (x + y))) + Additive.ofMul (e (g (x + w))) + Additive.ofMul (e (g (y + w)))) = Additive.ofMul (e (g (x + y + w))) + Additive.ofMul (e (g x)) + Additive.ofMul (e (g y)) + Additive.ofMul (e (g w))` using `fun x y w => by`. Simplify `congrArg (fun v => Additive.ofMul (e v)) (hg x y w)` using `only [map_mul, ofMul_mul]`.

Take `⟨b, hb⟩ : ∃ b : X → V, ∀ x, b x = a x * (e (g x))⁻¹` from `⟨_, fun _ => rfl⟩`. Establish `hbA : ∀ x, Additive.ofMul (b x) = Additive.ofMul (a x) - Additive.ofMul (e (g x))` using `fun x => by rw [hb, ofMul_mul, ofMul_inv, sub_eq_add_neg]`. Establish `hΘb : ∀ x y w, Additive.ofMul (b (x + y + w)) + Additive.ofMul (b x) + Additive.ofMul (b y) + Additive.ofMul (b w) = Additive.ofMul (b (x + y)) + Additive.ofMul (b (x + w)) + Additive.ofMul (b (y + w))` using `fun x y w => by`. Simplify using `only [hbA]`. Take the linear combination `(norm := module) hfA x y w + hgA x y w`.

Establish `hb0 : Additive.ofMul (b 0) = 0`. Establish `h0` using `hΘb 0 0 0`. Simplify using `only [add_zero] at h0`. Take the linear combination `(norm := module) h0`. Establish `hε : ∀ x y, Additive.ofMul (b (-(x + y))) - Additive.ofMul (b (x + y)) = (Additive.ofMul (b (-x)) - Additive.ofMul (b x)) + (Additive.ofMul (b (-y)) - Additive.ofMul (b y))` using `fun x y => by`.

Establish `t` using `hΘb x y (-(x + y))`. Establish `e1 : x + y + -(x + y) = 0` using `add_neg_cancel _`. Establish `e2 : x + -(x + y) = -y` using `by abel`. Establish `e3 : y + -(x + y) = -x` using `by abel`. Rewrite `t` using `[e1, e2, e3]`.

Take the linear combination `(norm := module) t - hb0`. Take `⟨h, hh⟩ : ∃ h : X → U, ∀ x, h x = n x * g x * (g (-x))⁻¹` from `⟨_, fun _ => rfl⟩`. Establish `heh : ∀ x, Additive.ofMul (e (h x)) = Additive.ofMul (b (-x)) - Additive.ofMul (b x)` using `fun x => by`. Rewrite using `[hh, e.map_mul, e.map_mul, e.map_inv, ofMul_mul, ofMul_mul, ofMul_inv, hbA, hbA]`. Take the linear combination `(norm := module) -(hnA x)`.

Establish `hhom : ∀ x y, h (x + y) = h x * h y` using `fun x y => by`. Apply `he` to reduce the goal to its premises. Apply `tA` to reduce the goal to its premises. Rewrite using `[map_mul, ofMul_mul, heh, heh, heh, neg_add_rev, add_comm (-y) (-x)]`. Use `hε x y` as an intermediate fact.

Rewrite `this` using `[neg_add_rev, add_comm (-y) (-x)]`. Conclude with `this`. Take `⟨k, hk3, hkneg⟩` from `GlobalTheory.hom_eq_evenness_defect_of_cube X U h hhom`. Use `⟨fun x => e (k x) * (b x)⁻¹, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y w`.

Apply `tA` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`. Establish `hk` using `congrArg (fun v => Additive.ofMul (e v)) (hk3 x y w)`. Simplify using `only [map_mul, ofMul_mul] at hk`. Take the linear combination `(norm := module) hk - hΘb x y w`.

Introduce `x`. Apply `tA` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`. Establish `hk` using `congrArg (fun v => Additive.ofMul (e v)) (hkneg x)`. Simplify using `only [map_mul, ofMul_mul] at hk`.

Take the linear combination `(norm := module) hk + heh x`. Introduce `x`. Use `⟨k x * g x, ?_⟩` and prove the remaining obligations. Apply `tA` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv, map_mul, hbA]`.

Normalize the expressions using the abelian group laws.
-/
theorem exists_even_cube_correction : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (U V : Type) [CommGroup U] [CommGroup V] (e : U →* V), Function.Injective e → ∀ a : X → V, (∀ x y w : X, ∃ u : U, a (x + y + w) * a x * a y * a w = e u * (a (x + y) * a (x + w) * a (y + w))) → (∀ x : X, ∃ u : U, a (-x) = e u * a x) → ∃ c : X → V, (∀ x y w : X, c (x + y + w) * c x * c y * c w = c (x + y) * c (x + w) * c (y + w)) ∧ (∀ x : X, c (-x) = c x) ∧ ∀ x : X, ∃ u : U, c x * a x = e u := by
  intro X _ _ _ U V _ _ e he a h3 hneg
  choose f hf using h3
  choose n hn using hneg
  have tA : ∀ {p q : V}, Additive.ofMul p = Additive.ofMul q → p = q := fun h => h
  have hfA : ∀ x y w, Additive.ofMul (a (x + y + w)) + Additive.ofMul (a x) + Additive.ofMul (a y)
      + Additive.ofMul (a w) = Additive.ofMul (e (f x y w)) + (Additive.ofMul (a (x + y))
      + Additive.ofMul (a (x + w)) + Additive.ofMul (a (y + w))) := fun x y w => by
    simpa only [ofMul_mul] using congrArg Additive.ofMul (hf x y w)
  have hnA : ∀ x, Additive.ofMul (a (-x)) = Additive.ofMul (e (n x)) + Additive.ofMul (a x) :=
    fun x => by simpa only [ofMul_mul] using congrArg Additive.ofMul (hn x)

  have hs1 : ∀ x y w, f x y w = f y x w := fun x y w => by
    apply he; apply tA
    have h1 := hfA x y w
    have h2 := hfA y x w
    rw [add_comm y x] at h2
    linear_combination (norm := module) h2 - h1
  have hs2 : ∀ x y w, f x y w = f x w y := fun x y w => by
    apply he; apply tA
    have h1 := hfA x y w
    have h2 := hfA x w y
    rw [add_right_comm x w y, add_comm w y] at h2
    linear_combination (norm := module) h2 - h1
  have hc : ∀ x x' x'' y, f (x + x') x'' y * f x x' y = f x (x' + x'') y * f x' x'' y := by
    intro x x' x'' y
    apply he; apply tA
    simp only [map_mul, ofMul_mul]
    have h1 := hfA (x + x') x'' y
    have h2 := hfA x x' y
    have h3 := hfA x (x' + x'') y
    have h4 := hfA x' x'' y
    rw [← add_assoc x x' x''] at h3
    linear_combination (norm := module) h3 + h4 - h1 - h2
  obtain ⟨g, hg⟩ := GlobalTheory.symm_cubical_cocycle_isThirdDifference X U f hs1 hs2 hc
  have hgA : ∀ x y w, Additive.ofMul (e (f x y w)) + (Additive.ofMul (e (g (x + y)))
      + Additive.ofMul (e (g (x + w))) + Additive.ofMul (e (g (y + w))))
      = Additive.ofMul (e (g (x + y + w))) + Additive.ofMul (e (g x)) + Additive.ofMul (e (g y))
      + Additive.ofMul (e (g w)) := fun x y w => by
    simpa only [map_mul, ofMul_mul] using congrArg (fun v => Additive.ofMul (e v)) (hg x y w)

  obtain ⟨b, hb⟩ : ∃ b : X → V, ∀ x, b x = a x * (e (g x))⁻¹ := ⟨_, fun _ => rfl⟩
  have hbA : ∀ x, Additive.ofMul (b x) = Additive.ofMul (a x) - Additive.ofMul (e (g x)) :=
    fun x => by rw [hb, ofMul_mul, ofMul_inv, sub_eq_add_neg]
  have hΘb : ∀ x y w, Additive.ofMul (b (x + y + w)) + Additive.ofMul (b x) + Additive.ofMul (b y)
      + Additive.ofMul (b w) = Additive.ofMul (b (x + y)) + Additive.ofMul (b (x + w))
      + Additive.ofMul (b (y + w)) := fun x y w => by
    simp only [hbA]
    linear_combination (norm := module) hfA x y w + hgA x y w
  have hb0 : Additive.ofMul (b 0) = 0 := by
    have h0 := hΘb 0 0 0
    simp only [add_zero] at h0
    linear_combination (norm := module) h0

  have hε : ∀ x y, Additive.ofMul (b (-(x + y))) - Additive.ofMul (b (x + y))
      = (Additive.ofMul (b (-x)) - Additive.ofMul (b x))
        + (Additive.ofMul (b (-y)) - Additive.ofMul (b y)) := fun x y => by
    have t := hΘb x y (-(x + y))
    have e1 : x + y + -(x + y) = 0 := add_neg_cancel _
    have e2 : x + -(x + y) = -y := by abel
    have e3 : y + -(x + y) = -x := by abel
    rw [e1, e2, e3] at t
    linear_combination (norm := module) t - hb0
  obtain ⟨h, hh⟩ : ∃ h : X → U, ∀ x, h x = n x * g x * (g (-x))⁻¹ := ⟨_, fun _ => rfl⟩
  have heh : ∀ x, Additive.ofMul (e (h x)) = Additive.ofMul (b (-x)) - Additive.ofMul (b x) :=
    fun x => by
      rw [hh, e.map_mul, e.map_mul, e.map_inv, ofMul_mul, ofMul_mul, ofMul_inv, hbA, hbA]
      linear_combination (norm := module) -(hnA x)
  have hhom : ∀ x y, h (x + y) = h x * h y := fun x y => by
    apply he; apply tA
    rw [map_mul, ofMul_mul, heh, heh, heh, neg_add_rev, add_comm (-y) (-x)]
    have := hε x y
    rw [neg_add_rev, add_comm (-y) (-x)] at this
    exact this
  obtain ⟨k, hk3, hkneg⟩ := GlobalTheory.hom_eq_evenness_defect_of_cube X U h hhom
  refine ⟨fun x => e (k x) * (b x)⁻¹, ?_, ?_, ?_⟩
  · intro x y w
    apply tA
    simp only [ofMul_mul, ofMul_inv]
    have hk := congrArg (fun v => Additive.ofMul (e v)) (hk3 x y w)
    simp only [map_mul, ofMul_mul] at hk
    linear_combination (norm := module) hk - hΘb x y w
  · intro x
    apply tA
    simp only [ofMul_mul, ofMul_inv]
    have hk := congrArg (fun v => Additive.ofMul (e v)) (hkneg x)
    simp only [map_mul, ofMul_mul] at hk
    linear_combination (norm := module) hk + heh x
  · intro x
    refine ⟨k x * g x, ?_⟩
    apply tA
    simp only [ofMul_mul, ofMul_inv, map_mul, hbA]
    abel

end GlobalTheory
