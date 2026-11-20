import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU

/- English proof (translation)
Establish `e1 : θ a b y * θ (a * b) (c * d) y = θ a (b * (c * d)) y * θ b (c * d) y`. Rewrite using `[_root_.mul_comm]`. Conclude with `h.coc a b (c * d) y`. Establish `e2 : θ b (c * d) y * θ c d y = θ (b * c) d y * θ b c y` using `(h.coc b c d y).symm`. Establish `e3 : θ (a * c) (b * d) y * θ a c y = θ a (c * (b * d)) y * θ c (b * d) y` using `h.coc a c (b * d) y`.

Establish `e4 : θ c (b * d) y * θ b d y = θ (c * b) d y * θ c b y` using `(h.coc c b d y).symm`. Rewrite using `[e1, _root_.mul_assoc, e2, e3, _root_.mul_assoc, e4, _root_.mul_comm c b, h.s01 c b, mul_left_comm c b d]`.
-/
private theorem isCub_mul_swap_middle {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ)
    (a b c d y : A) :
    θ a b y * θ (a * b) (c * d) y * θ c d y = θ (a * c) (b * d) y * θ a c y * θ b d y := by
  have e1 : θ a b y * θ (a * b) (c * d) y = θ a (b * (c * d)) y * θ b (c * d) y := by
    rw [_root_.mul_comm]; exact h.coc a b (c * d) y
  have e2 : θ b (c * d) y * θ c d y = θ (b * c) d y * θ b c y := (h.coc b c d y).symm
  have e3 : θ (a * c) (b * d) y * θ a c y = θ a (c * (b * d)) y * θ c (b * d) y := h.coc a c (b * d) y
  have e4 : θ c (b * d) y * θ b d y = θ (c * b) d y * θ c b y := (h.coc c b d y).symm
  rw [e1, _root_.mul_assoc, e2, e3, _root_.mul_assoc, e4, _root_.mul_comm c b, h.s01 c b, mul_left_comm c b d]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
private theorem v_sub_one_add_le_v_pow_l_sub_one {U : Type} [CommGroup U] {P B C D Px Px' D' E F : U} {k : ℕ}
    (ih : P * C ^ k = D * Px * Px') (e : D * B * C = D' * E * F) :
    P * B * C ^ (k + 1) = D' * (Px * E) * (Px' * F) := by
  calc P * B * C ^ (k + 1) = (P * C ^ k) * (B * C) := by rw [pow_succ]; ac_rfl
    _ = Px * Px' * (D * B * C) := by rw [ih]; ac_rfl
    _ = D' * (Px * E) * (Px' * F) := by rw [e]; ac_rfl

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp [cubN, h.face]`. Consider the case `succ k ih`. Simplify using `only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢`. Rewrite using `[pow_succ x, pow_succ x', mul_pow x x' k]`.

Conclude with `v_sub_one_add_le_v_pow_l_sub_one ih (isCub_mul_swap_middle h (x ^ k) (x' ^ k) x x' y)`.
-/
theorem cubN_mul_left {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ) (k : ℕ)
    (x x' y : A) :
    cubN θ k 1 (x * x') y * θ x x' y ^ k = θ (x ^ k) (x' ^ k) y * cubN θ k 1 x y * cubN θ k 1 x' y := by
  induction k with
  | zero => simp [cubN, h.face]
  | succ k ih =>
    simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
    rw [pow_succ x, pow_succ x', mul_pow x x' k]
    exact v_sub_one_add_le_v_pow_l_sub_one ih (isCub_mul_swap_middle h (x ^ k) (x' ^ k) x x' y)

/- English proof (translation)
The claim follows from `map_mul _ a b`.
-/
private theorem gm_id_global_mul {X : Scheme.{0}} (z : X) (a b : Γ(X, ⊤)ˣ) :
    gm (𝟙 X) z ⊤ (a * b) = gm (𝟙 X) z ⊤ a * gm (𝟙 X) z ⊤ b :=
  map_mul _ a b

section
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} {c : CubicalStr G L} {N : ℕ}
  {T : Over S} {x x' y : T ⟶ G}

/- English proof (translation)
Take `⟨hx, hy, hv⟩` from `h`. Take `⟨hx', -, hv'⟩` from `h'`. Use `⟨by rw [mul_pow, hx, hx', _root_.one_mul], hy, fun z J hJ => ?_⟩` and prove the remaining obligations. Establish `hc` using `isCub_cubV c hJ`. Establish `e1` using `cubN_mul_left hc N x x' y`.

Rewrite `e1` using `[hx, hx', hc.face, _root_.one_mul, hc.s12 x x' y, hc.s01 x y x']`. Establish `e2` using `hc.N_add N 1 y x x'`. Simplify using `only [hc.face, _root_.one_mul, _root_.mul_one, hy] at e2`. Apply `mul_right_cancel (b := cubV c z J y x x' ^ N)` to reduce the goal to its premises. Rewrite using `[gm_id_global_mul, _root_.mul_assoc, e1, e2, ← hv z J hJ, ← hv' z J hJ]`.

Conclude with `mul_mul_mul_comm _ _ _ _`.
-/
theorem CubWeil.mul_left {ζ ζ' : Γ(T.left, ⊤)ˣ} (h : CubWeil c N x y ζ) (h' : CubWeil c N x' y ζ') :
    CubWeil c N (x * x') y (ζ * ζ') := by
  obtain ⟨hx, hy, hv⟩ := h
  obtain ⟨hx', -, hv'⟩ := h'
  refine ⟨by rw [mul_pow, hx, hx', _root_.one_mul], hy, fun z J hJ => ?_⟩
  have hc := isCub_cubV c hJ
  have e1 := cubN_mul_left hc N x x' y
  rw [hx, hx', hc.face, _root_.one_mul, hc.s12 x x' y, hc.s01 x y x'] at e1
  have e2 := hc.N_add N 1 y x x'
  simp only [hc.face, _root_.one_mul, _root_.mul_one, hy] at e2
  apply mul_right_cancel (b := cubV c z J y x x' ^ N)
  rw [gm_id_global_mul, _root_.mul_assoc, e1, e2, ← hv z J hJ, ← hv' z J hJ]
  exact mul_mul_mul_comm _ _ _ _

/- English proof (translation)
Take `⟨ζ, hζ, -⟩` from `existsUnique_cubWeil (x := (1 : T ⟶ G)) c (one_pow N) hy`. Establish `h2` using `hζ.mul_left hζ`. Rewrite `h2` using `[_root_.one_mul]`. Establish `e : ζ * ζ = ζ * 1` using `by rw [_root_.mul_one]; exact h2.unique hζ`. Rewrite `hζ` using `[mul_left_cancel e]`.

Conclude with `hζ`.
-/
theorem cubWeil_one_left (c : CubicalStr G L) (hy : y ^ N = 1) : CubWeil c N 1 y 1 := by
  obtain ⟨ζ, hζ, -⟩ := existsUnique_cubWeil (x := (1 : T ⟶ G)) c (one_pow N) hy
  have h2 := hζ.mul_left hζ
  rw [_root_.one_mul] at h2
  have e : ζ * ζ = ζ * 1 := by rw [_root_.mul_one]; exact h2.unique hζ
  rw [mul_left_cancel e] at hζ
  exact hζ

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using cubWeil_one_left c h.2.1`. Consider the case `succ n ih => simpa [pow_succ] using ih.mul_left h`.
-/
theorem CubWeil.pow_left {ζ : Γ(T.left, ⊤)ˣ} (h : CubWeil c N x y ζ) (n : ℕ) : CubWeil c N (x ^ n) y (ζ ^ n) := by
  induction n with
  | zero => simpa using cubWeil_one_left c h.2.1
  | succ n ih => simpa [pow_succ] using ih.mul_left h

/- English proof (translation)
Establish `hp` using `h.pow_left N`. Rewrite `hp` using `[h.1]`. Conclude with `hp.unique (cubWeil_one_left c h.2.1)`.
-/
theorem CubWeil.pow_eq_one {ζ : Γ(T.left, ⊤)ˣ} (h : CubWeil c N x y ζ) : ζ ^ N = 1 := by
  have hp := h.pow_left N
  rw [h.1] at hp
  exact hp.unique (cubWeil_one_left c h.2.1)

end

/- English proof (translation)
Introduce `S G _ _ L c N T`. Use `⟨fun x y hx hy => existsUnique_cubWeil c hx hy, fun x x' y ζ ζ' h h' => h.mul_left h', fun x y ζ h => ⟨h.symm, h.pow_eq_one⟩, fun T' ρ x y ζ h => h.comp ρ, ?_⟩` and prove the remaining obligations. Introduce `H _ i hi hne t y ht hy`. Take `⟨σ⟩` from `hne`. Conclude with `σ.cubWeil ht hy`.
-/
theorem cubWeil_basic : (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L) (N : ℕ) (T : Over S), (∀ x y : T ⟶ G, x ^ N = 1 → y ^ N = 1 → ∃! ζ, CubWeil c N x y ζ) ∧ (∀ (x x' y : T ⟶ G) ζ ζ', CubWeil c N x y ζ → CubWeil c N x' y ζ' → CubWeil c N (x * x') y (ζ * ζ')) ∧ (∀ (x y : T ⟶ G) ζ, CubWeil c N x y ζ → CubWeil c N y x ζ⁻¹ ∧ ζ ^ N = 1) ∧ (∀ (T' : Over S) (ρ : T' ⟶ T) (x y : T ⟶ G) ζ, CubWeil c N x y ζ → CubWeil c N (ρ ≫ x) (ρ ≫ y) (Units.map ρ.left.appTop.hom.toMonoidHom ζ)) ∧ ∀ (H : Over S) [GrpObj H] (i : H ⟶ G), IsMonHom i → Nonempty (BiTriv c i) → ∀ (t : T ⟶ H) (y : T ⟶ G), t ^ N = 1 → y ^ N = 1 → CubWeil c N (t ≫ i) y 1) := by
  intro S G _ _ L c N T
  refine ⟨fun x y hx hy => existsUnique_cubWeil c hx hy, fun x x' y ζ ζ' h h' => h.mul_left h',
    fun x y ζ h => ⟨h.symm, h.pow_eq_one⟩, fun T' ρ x y ζ h => h.comp ρ, ?_⟩
  intro H _ i hi hne t y ht hy
  obtain ⟨σ⟩ := hne
  exact σ.cubWeil ht hy

end GlobalTheory.UU
end
