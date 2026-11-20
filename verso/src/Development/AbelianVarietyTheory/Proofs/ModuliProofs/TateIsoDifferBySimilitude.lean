import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {k : Type} [Field k]
  {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} in

/- English proof (translation)
Establish `key : I.ev n (a - b) * I.ev n b = I.ev n a` using `by rw [← I.add, sub_add_cancel]`. Rewrite using `[show D.ModN n (a - b) ↔ ∃ c, a - b = n • c from Iff.rfl, ← I.ker n hn, ← key]`. Conclude with `mul_eq_right`.
-/
theorem _root_.GlobalTheory.tateIso_ev_eq_iff (I : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIso D k Q act e) {n : ℕ} (hn : 0 < n) (a b : D.La) :
    I.ev n a = I.ev n b ↔ D.ModN n (a - b) := by
  have key : I.ev n (a - b) * I.ev n b = I.ev n a := by rw [← I.add, sub_add_cancel]
  rw [show D.ModN n (a - b) ↔ ∃ c, a - b = n • c from Iff.rfl, ← I.ker n hn, ← key]
  exact mul_eq_right

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} in

/- English proof (translation)
The claim follows from `(I.onto n hn _).mpr ⟨a, rfl⟩`.
-/
theorem _root_.GlobalTheory.tateIso_ev_pow (I : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIso D k Q act e) {n : ℕ} (hn : 0 < n) (a : D.La) :
    I.ev n a ^ n = 1 :=
  (I.onto n hn _).mpr ⟨a, rfl⟩

end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} in
/- English proof (translation)
Use `haveI := D.proj`. Set `N : Submodule (𝓞 E) D.La` to `LinearMap.range ((n : 𝓞 E) • LinearMap.id)`. Establish `hN : ∀ x, x ∈ N ↔ D.ModN n x`. Introduce `x`. Use `show (∃ y, (n : 𝓞 E) • y = x) ↔ ∃ y, x = n • y`.

Simplify using `only [Nat.cast_smul_eq_nsmul]`. Apply the tactic sequence `constructor <;> rintro ⟨y, hy⟩ <;> exact ⟨y, hy.symm⟩`. Establish `hrel : ∀ x y, I.ev n x = I.ev n y ↔ x - y ∈ N` using `fun x y => (_root_.GlobalTheory.tateIso_ev_eq_iff I hn x y).trans (hN _).symm`. Establish `hs : ∀ a, ∃ b, I.ev n b = I'.ev n a` using `fun a => (I.onto n hn _).mp (_root_.GlobalTheory.tateIso_ev_pow I' hn a)`. Use `choose s hs using hs`.

Set `g : D.La →ₗ[𝓞 E] D.La ⧸ N` to `{ toFun := fun a => N.mkQ (s a) map_add' := fun a b => by`. Rewrite using `[← map_add, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← hrel, I.add, hs, hs, hs, I'.add]`. Use the proof step `map_smul' := fun c a => by`. Rewrite using `[RingHom.id_apply, ← map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← hrel, I.lin, hs, hs, I'.lin] }`. Take `⟨f, hf⟩` from `Module.projective_lifting_property N.mkQ g (Submodule.mkQ_surjective N)`.

Use `⟨f, fun a => ?_⟩` and prove the remaining obligations. Establish `h1 : N.mkQ (f a) = N.mkQ (s a)` using `LinearMap.congr_fun hf a`. Rewrite `h1` using `[Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← hrel]`. Rewrite using `[h1, hs]`.
-/
private lemma exists_linearMap_ev_eq_of_tateIso (I I' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIso D k Q act e) {n : ℕ} (hn : 0 < n) :
    ∃ f : D.La →ₗ[𝓞 E] D.La, ∀ a, I.ev n (f a) = I'.ev n a := by
  classical
  haveI := D.proj
  let N : Submodule (𝓞 E) D.La := LinearMap.range ((n : 𝓞 E) • LinearMap.id)
  have hN : ∀ x, x ∈ N ↔ D.ModN n x := by
    intro x
    show (∃ y, (n : 𝓞 E) • y = x) ↔ ∃ y, x = n • y
    simp only [Nat.cast_smul_eq_nsmul]
    constructor <;> rintro ⟨y, hy⟩ <;> exact ⟨y, hy.symm⟩
  have hrel : ∀ x y, I.ev n x = I.ev n y ↔ x - y ∈ N := fun x y =>
    (_root_.GlobalTheory.tateIso_ev_eq_iff I hn x y).trans (hN _).symm
  have hs : ∀ a, ∃ b, I.ev n b = I'.ev n a :=
    fun a => (I.onto n hn _).mp (_root_.GlobalTheory.tateIso_ev_pow I' hn a)
  choose s hs using hs
  let g : D.La →ₗ[𝓞 E] D.La ⧸ N :=
    { toFun := fun a => N.mkQ (s a)
      map_add' := fun a b => by
        rw [← map_add, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← hrel,
          I.add, hs, hs, hs, I'.add]
      map_smul' := fun c a => by
        rw [RingHom.id_apply, ← map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply,
          Submodule.Quotient.eq, ← hrel, I.lin, hs, hs, I'.lin] }
  obtain ⟨f, hf⟩ := Module.projective_lifting_property N.mkQ g (Submodule.mkQ_surjective N)
  refine ⟨f, fun a => ?_⟩
  have h1 : N.mkQ (f a) = N.mkQ (s a) := LinearMap.congr_fun hf a
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← hrel] at h1
  rw [h1, hs]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in

/- English proof (translation)
Introduce `E _ _ _ H D k _ Q _ act e he I I'`. Establish `hf : ∀ n, ∃ f : D.La →ₗ[𝓞 E] D.La, 0 < n → ∀ a, I.ev n (f a) = I'.ev n a`. Introduce `n`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Conclude with `⟨0, fun h => absurd h (lt_irrefl 0)⟩`.

Take `⟨f, hf⟩` from `exists_linearMap_ev_eq_of_tateIso I I' hn`. Conclude with `⟨f, fun _ => hf⟩`. Use `choose f hf using hf`. Establish `hk : ∀ n, ∃ ν : ℤ, 0 < n → I'.ζ n = I.ζ n ^ ν`. Introduce `n`.

Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Conclude with `⟨0, fun h => absurd h (lt_irrefl 0)⟩`. Use `haveI : NeZero n := ⟨hn.ne'⟩`. Establish `hprim : IsPrimitiveRoot ((I.ζ n : kˣ) : k) n` using `IsPrimitiveRoot.coe_units_iff.mpr (I.ζ_prim n hn)`. Establish `hpow : ((I'.ζ n : kˣ) : k) ^ n = 1`.

Rewrite using `[← Units.val_pow_eq_pow_val, (I'.ζ_prim n hn).pow_eq_one, Units.val_one]`. Take `⟨i, -, hi⟩` from `hprim.eq_pow_of_pow_eq_one hpow`. Use `⟨i, fun _ => ?_⟩` and prove the remaining obligations. Use `ext`. Rewrite using `[zpow_natCast, Units.val_pow_eq_pow_val, hi]`.

Use `choose ν hν using hk`. Use `⟨⟨f, ν, ?_, ?_, ?_⟩, fun n hn => ⟨fun a => (hf n hn a).symm, hν n hn⟩⟩` and prove the remaining obligations. Introduce `n m hn hm a`. Rewrite using `[← _root_.GlobalTheory.tateIso_ev_eq_iff I hn, ← I.tower n m hn hm, hf (n * m) (Nat.mul_pos hn hm), hf n hn, I'.tower n m hn hm]`. Introduce `n hn`.

Take `⟨g, hg⟩` from `exists_linearMap_ev_eq_of_tateIso I' I hn`. Use `⟨g, fun a => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← _root_.GlobalTheory.tateIso_ev_eq_iff I' hn, hg, hf n hn]`. Rewrite using `[← _root_.GlobalTheory.tateIso_ev_eq_iff I hn, hf n hn, hg]`. Introduce `n hn a b`.

Establish `h1` using `I.isom n hn (f n a) (f n b)`. Establish `h2` using `I'.isom n hn a b`. Rewrite `h1` using `[hf n hn, hf n hn]`. Establish `hc` using `he n _ _ _ _ hn (_root_.GlobalTheory.tateIso_ev_pow I' hn a) (_root_.GlobalTheory.tateIso_ev_pow I' hn b) h1 h2`. Rewrite `hc` using `[hν n hn, ← zpow_mul]`.

Rewrite using `[← (I.ζ_prim n hn).zpow_eq_one_iff_dvd, zpow_sub, hc, mul_inv_cancel]`.
-/
theorem _root_.GlobalTheory.tateIso_differ_by_similitude :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop), (∀ n x y c c', 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e n x y c' → c = c') → ∀ I I' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIso D k Q act e, ∃ g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sim D, ∀ n, 0 < n → (∀ a, I'.ev n a = I.ev n (g.f n a)) ∧ I'.ζ n = I.ζ n ^ g.ν n := by
  intro E _ _ _ H D k _ Q _ act e he I I'
  have hf : ∀ n, ∃ f : D.La →ₗ[𝓞 E] D.La, 0 < n → ∀ a, I.ev n (f a) = I'.ev n a := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, fun h => absurd h (lt_irrefl 0)⟩
    · obtain ⟨f, hf⟩ := exists_linearMap_ev_eq_of_tateIso I I' hn
      exact ⟨f, fun _ => hf⟩
  choose f hf using hf
  have hk : ∀ n, ∃ ν : ℤ, 0 < n → I'.ζ n = I.ζ n ^ ν := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, fun h => absurd h (lt_irrefl 0)⟩
    · haveI : NeZero n := ⟨hn.ne'⟩
      have hprim : IsPrimitiveRoot ((I.ζ n : kˣ) : k) n :=
        IsPrimitiveRoot.coe_units_iff.mpr (I.ζ_prim n hn)
      have hpow : ((I'.ζ n : kˣ) : k) ^ n = 1 := by
        rw [← Units.val_pow_eq_pow_val, (I'.ζ_prim n hn).pow_eq_one, Units.val_one]
      obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hpow
      refine ⟨i, fun _ => ?_⟩
      ext
      rw [zpow_natCast, Units.val_pow_eq_pow_val, hi]
  choose ν hν using hk
  refine ⟨⟨f, ν, ?_, ?_, ?_⟩, fun n hn => ⟨fun a => (hf n hn a).symm, hν n hn⟩⟩
  · intro n m hn hm a
    rw [← _root_.GlobalTheory.tateIso_ev_eq_iff I hn, ← I.tower n m hn hm, hf (n * m) (Nat.mul_pos hn hm),
      hf n hn, I'.tower n m hn hm]
  · intro n hn
    obtain ⟨g, hg⟩ := exists_linearMap_ev_eq_of_tateIso I' I hn
    refine ⟨g, fun a => ⟨?_, ?_⟩⟩
    · rw [← _root_.GlobalTheory.tateIso_ev_eq_iff I' hn, hg, hf n hn]
    · rw [← _root_.GlobalTheory.tateIso_ev_eq_iff I hn, hf n hn, hg]
  · intro n hn a b
    have h1 := I.isom n hn (f n a) (f n b)
    have h2 := I'.isom n hn a b
    rw [hf n hn, hf n hn] at h1
    have hc := he n _ _ _ _ hn (_root_.GlobalTheory.tateIso_ev_pow I' hn a)
      (_root_.GlobalTheory.tateIso_ev_pow I' hn b) h1 h2
    rw [hν n hn, ← zpow_mul] at hc
    rw [← (I.ζ_prim n hn).zpow_eq_one_iff_dvd, zpow_sub, hc, mul_inv_cancel]

end GlobalTheory
