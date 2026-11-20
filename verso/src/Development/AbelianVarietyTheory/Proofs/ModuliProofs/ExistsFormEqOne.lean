import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SimAlg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, by simp⟩`.
-/
theorem modN_zero (n : ℕ) : D.ModN n 0 := ⟨0, by simp⟩

/- English proof (translation)
Take `⟨a, rfl⟩` from `hx`. Take `⟨b, rfl⟩` from `hy`. Conclude with `⟨a + b, by rw [smul_add]⟩`.
-/
theorem modN_add {n : ℕ} {x y : D.La} (hx : D.ModN n x) (hy : D.ModN n y) : D.ModN n (x + y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, by rw [smul_add]⟩

/- English proof (translation)
Take `⟨a, rfl⟩` from `hx`. Conclude with `⟨-a, by rw [smul_neg]⟩`.
-/
theorem modN_neg {n : ℕ} {x : D.La} (hx : D.ModN n x) : D.ModN n (-x) := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨-a, by rw [smul_neg]⟩

/- English proof (translation)
Take `⟨a, rfl⟩` from `hx`. Conclude with `⟨f a, by rw [map_nsmul]⟩`.
-/
theorem modN_map {n : ℕ} {x : D.La} (f : D.La →ₗ[𝓞 E] D.La) (hx : D.ModN n x) : D.ModN n (f x) := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨f a, by rw [map_nsmul]⟩

/- English proof (translation)
Take `⟨a, rfl⟩` from `hx`. Conclude with `⟨m • a, by rw [mul_smul]⟩`.
-/
theorem modN_of_mul {n m : ℕ} {x : D.La} (hx : D.ModN (n * m) x) : D.ModN n x := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨m • a, by rw [mul_smul]⟩

/- English proof (translation)
Take `⟨a, ha⟩` from `hx`. Take `⟨b, hb⟩` from `hy`. Establish `h1 : x = x' + n • a` using `by rw [← ha]; abel`. Establish `h2 : y = y' + n • b` using `by rw [← hb]; abel`. Use `⟨D.EF x' b + D.EF a y' + n * D.EF a b, ?_⟩` and prove the remaining obligations.

Rewrite using `[h1, h2]`. Simplify using `only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dvd_form_sub {n : ℕ} {x x' y y' : D.La} (hx : D.ModN n (x - x')) (hy : D.ModN n (y - y')) :
    (n : ℤ) ∣ D.EF x y - D.EF x' y' := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  have h1 : x = x' + n • a := by rw [← ha]; abel
  have h2 : y = y' + n • b := by rw [← hb]; abel
  refine ⟨D.EF x' b + D.EF a y' + n * D.EF a b, ?_⟩
  rw [h1, h2]
  simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
  ring

/- English proof (translation)
Use `haveI := D.fin`. Use `haveI := D.proj`. Use `haveI : Nontrivial D.La := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [D.rank]; omega)`. Use `haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La`. Use `haveI : Module.IsTorsionFree ℤ D.La := Function.Injective.moduleIsTorsionFree D.EF D.unimod.1 (fun r x => map_smul _ r x)`.

Use `haveI : Module.Free ℤ D.La := Module.free_of_finite_type_torsion_free'`. Set `B` to `Module.Free.chooseBasis ℤ D.La`. Take `⟨i⟩` from `B.index_nonempty`. Take `⟨a, ha⟩` from `D.unimod.2 (B.coord i)`. Conclude with `⟨a, B i, by rw [ha]; simp⟩`.
-/
theorem exists_form_eq_one (h : 1 ≤ D.p + D.q) : ∃ a b : D.La, D.EF a b = 1 := by
  haveI := D.fin
  haveI := D.proj
  haveI : Nontrivial D.La := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [D.rank]; omega)
  haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  haveI : Module.IsTorsionFree ℤ D.La :=
    Function.Injective.moduleIsTorsionFree D.EF D.unimod.1 (fun r x => map_smul _ r x)
  haveI : Module.Free ℤ D.La := Module.free_of_finite_type_torsion_free'
  let B := Module.Free.chooseBasis ℤ D.La
  obtain ⟨i⟩ := B.index_nonempty
  obtain ⟨a, ha⟩ := D.unimod.2 (B.coord i)
  exact ⟨a, B i, by rw [ha]; simp⟩

/- English proof (translation)
Establish `h1` using `g.mult n hn (h a) (h b)`. Establish `h2` using `dvd_form_sub (hh a) (hh b)`. Rewrite `h2` using `[hab]`. Take `⟨c, hc⟩` from `dvd_sub h2 h1`. Conclude with `⟨c, by linear_combination hc⟩`.
-/
theorem dvd_mult_inv (g : Sim D) {n : ℕ} (hn : 0 < n) {a b : D.La} (hab : D.EF a b = 1)
    (h : D.La →ₗ[𝓞 E] D.La) (hh : ∀ x, D.ModN n (g.f n (h x) - x)) :
    (n : ℤ) ∣ g.ν n * D.EF (h a) (h b) - 1 := by
  have h1 := g.mult n hn (h a) (h b)
  have h2 := dvd_form_sub (hh a) (hh b)
  rw [hab] at h2
  obtain ⟨c, hc⟩ := dvd_sub h2 h1
  exact ⟨c, by linear_combination hc⟩

/- English proof (translation)
Establish `h1` using `g.mult n hn a b`. Establish `h2 : (n : ℤ) ∣ _` using `Dvd.dvd.trans (by push_cast; exact Dvd.intro _ rfl) (g.mult (n * m) (Nat.mul_pos hn hm) a b)`. Establish `h3` using `dvd_form_sub (g.tower n m hn hm a) (g.tower n m hn hm b)`. Rewrite `h1`, `h2` using `[hab]`. Take `⟨c, hc⟩` from `dvd_add (dvd_sub h3 h2) h1`.

Conclude with `⟨c, by linear_combination hc⟩`.
-/
theorem dvd_mult_tower (g : Sim D) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) {a b : D.La} (hab : D.EF a b = 1) :
    (n : ℤ) ∣ g.ν (n * m) - g.ν n := by
  have h1 := g.mult n hn a b
  have h2 : (n : ℤ) ∣ _ := Dvd.dvd.trans (by push_cast; exact Dvd.intro _ rfl) (g.mult (n * m) (Nat.mul_pos hn hm) a b)
  have h3 := dvd_form_sub (g.tower n m hn hm a) (g.tower n m hn hm b)
  rw [hab] at h1 h2
  obtain ⟨c, hc⟩ := dvd_add (dvd_sub h3 h2) h1
  exact ⟨c, by linear_combination hc⟩

def one (D : Datum H) : Sim D where
  f _ := LinearMap.id
  ν _ := 1
  tower n _ _ _ a := by simpa using modN_zero n
  inv n _ := ⟨LinearMap.id, fun a => by simpa using modN_zero n⟩
  mult n _ a b := by simp

def mul (g g' : Sim D) : Sim D where
  f n := g.f n ∘ₗ g'.f n
  ν n := g.ν n * g'.ν n
  tower n m hn hm a := by
    have h1 := g.tower n m hn hm (g'.f (n * m) a)
    have h2 := modN_map (g.f n) (g'.tower n m hn hm a)
    convert modN_add h1 h2 using 1
    simp
  inv n hn := by
    obtain ⟨h, hh⟩ := g.inv n hn
    obtain ⟨h', hh'⟩ := g'.inv n hn
    refine ⟨h' ∘ₗ h, fun a => ⟨?_, ?_⟩⟩
    · convert modN_add (modN_map h' (hh (g'.f n a)).1) (hh' a).1 using 1
      simp
    · convert modN_add (modN_map (g.f n) (hh' (h a)).2) (hh a).2 using 1
      simp
  mult n hn a b := by
    have h1 := g.mult n hn (g'.f n a) (g'.f n b)
    have h2 := Dvd.dvd.mul_left (g'.mult n hn a b) (g.ν n)
    obtain ⟨c, hc⟩ := dvd_add h1 h2
    exact ⟨c, by simp only [LinearMap.comp_apply]; linear_combination hc⟩

/- English proof (translation)
Establish `hex : ∀ n : ℕ, ∃ h : D.La →ₗ[𝓞 E] D.La, 0 < n → ∀ a, D.ModN n (h (g.f n a) - a) ∧ D.ModN n (g.f n (h a) - a)`. Introduce `n`. Distinguish the cases in `hn : 0 < n`. Take `⟨h, hh⟩` from `g.inv n hn`. Conclude with `⟨h, fun _ => hh⟩`.

Conclude with `⟨0, fun h => absurd h hn⟩`. Use `choose h hh using hex`. Establish `hν : ∀ n : ℕ, 0 < n → (n : ℤ) ∣ g.ν n * D.EF (h n a) (h n b) - 1` using `fun n hn => dvd_mult_inv g hn hab (h n) fun x => (hh n hn x).2`. Use `⟨⟨h, fun n => D.EF (h n a) (h n b), ?_, ?_, ?_⟩, fun n hn => ⟨hh n hn, hν n hn⟩⟩` and prove the remaining obligations. Introduce `n m hn hm x`.

Establish `h1` using `modN_neg (hh n hn (h (n * m) x)).1`. Establish `h2` using `modN_neg (modN_map (h n) (g.tower n m hn hm (h (n * m) x)))`. Establish `h3` using `modN_map (h n) (modN_of_mul (hh (n * m) (Nat.mul_pos hn hm) x).2)`. Use `modN_add (modN_add h1 h2) h3 using 1` and compare the differences between its conclusion and the goal. Simplify using `only [map_sub]`.

Normalize the expressions using the abelian group laws. Introduce `n hn`. Conclude with `⟨g.f n, fun x => ⟨(hh n hn x).2, (hh n hn x).1⟩⟩`. Introduce `n hn x y`. Establish `h1` using `Dvd.dvd.mul_left (g.mult n hn (h n x) (h n y)) (D.EF (h n a) (h n b))`.

Establish `h2` using `Dvd.dvd.mul_left (dvd_form_sub (hh n hn x).2 (hh n hn y).2) (D.EF (h n a) (h n b))`. Establish `h3` using `Dvd.dvd.mul_right (hν n hn) (D.EF (h n x) (h n y))`. Take `⟨c, hc⟩` from `dvd_sub (dvd_sub h2 h1) h3`. Conclude with `⟨c, by linear_combination hc⟩`.
-/
theorem exists_inv (g : Sim D) {a b : D.La} (hab : D.EF a b = 1) :
    ∃ g' : Sim D, ∀ n, 0 < n → (∀ a, D.ModN n (g'.f n (g.f n a) - a) ∧ D.ModN n (g.f n (g'.f n a) - a)) ∧
      (n : ℤ) ∣ g.ν n * g'.ν n - 1 := by
  have hex : ∀ n : ℕ, ∃ h : D.La →ₗ[𝓞 E] D.La, 0 < n →
      ∀ a, D.ModN n (h (g.f n a) - a) ∧ D.ModN n (g.f n (h a) - a) := by
    intro n
    by_cases hn : 0 < n
    · obtain ⟨h, hh⟩ := g.inv n hn
      exact ⟨h, fun _ => hh⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose h hh using hex
  have hν : ∀ n : ℕ, 0 < n → (n : ℤ) ∣ g.ν n * D.EF (h n a) (h n b) - 1 := fun n hn =>
    dvd_mult_inv g hn hab (h n) fun x => (hh n hn x).2
  refine ⟨⟨h, fun n => D.EF (h n a) (h n b), ?_, ?_, ?_⟩, fun n hn => ⟨hh n hn, hν n hn⟩⟩
  · intro n m hn hm x
    have h1 := modN_neg (hh n hn (h (n * m) x)).1
    have h2 := modN_neg (modN_map (h n) (g.tower n m hn hm (h (n * m) x)))
    have h3 := modN_map (h n) (modN_of_mul (hh (n * m) (Nat.mul_pos hn hm) x).2)
    convert modN_add (modN_add h1 h2) h3 using 1
    simp only [map_sub]
    abel
  · intro n hn
    exact ⟨g.f n, fun x => ⟨(hh n hn x).2, (hh n hn x).1⟩⟩
  · intro n hn x y
    have h1 := Dvd.dvd.mul_left (g.mult n hn (h n x) (h n y)) (D.EF (h n a) (h n b))
    have h2 := Dvd.dvd.mul_left (dvd_form_sub (hh n hn x).2 (hh n hn y).2) (D.EF (h n a) (h n b))
    have h3 := Dvd.dvd.mul_right (hν n hn) (D.EF (h n x) (h n y))
    obtain ⟨c, hc⟩ := dvd_sub (dvd_sub h2 h1) h3
    exact ⟨c, by linear_combination hc⟩

/- English proof (translation)
Introduce `E _ _ _ H D hpq`. Take `⟨a, b, hab⟩` from `exists_form_eq_one hpq`. Use `⟨fun g n m hn hm => ⟨dvd_mult_tower g hn hm hab, ?_⟩, ⟨one D, fun _ => ⟨rfl, rfl⟩⟩, fun g g' => ⟨mul g g', fun _ => ⟨rfl, rfl⟩⟩, fun g => exists_inv g hab⟩` and prove the remaining obligations. Take `⟨h, hh⟩` from `g.inv n hn`. Take `⟨c, hc⟩` from `dvd_mult_inv g hn hab h fun x => (hh x).2`.

Conclude with `⟨D.EF (h a) (h b), -c, by linear_combination hc⟩`.
-/
theorem sim_group : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q → (∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ)) ∧ (∃ g : Sim D, ∀ n, g.f n = LinearMap.id ∧ g.ν n = 1) ∧ (∀ g g' : Sim D, ∃ g'' : Sim D, ∀ n, g''.f n = g.f n ∘ₗ g'.f n ∧ g''.ν n = g.ν n * g'.ν n) ∧ (∀ g : Sim D, ∃ g' : Sim D, ∀ n, 0 < n → (∀ a, D.ModN n (g'.f n (g.f n a) - a) ∧ D.ModN n (g.f n (g'.f n a) - a)) ∧ (n : ℤ) ∣ g.ν n * g'.ν n - 1) := by
  intro E _ _ _ H D hpq
  obtain ⟨a, b, hab⟩ := exists_form_eq_one hpq
  refine ⟨fun g n m hn hm => ⟨dvd_mult_tower g hn hm hab, ?_⟩, ⟨one D, fun _ => ⟨rfl, rfl⟩⟩,
    fun g g' => ⟨mul g g', fun _ => ⟨rfl, rfl⟩⟩, fun g => exists_inv g hab⟩
  obtain ⟨h, hh⟩ := g.inv n hn
  obtain ⟨c, hc⟩ := dvd_mult_inv g hn hab h fun x => (hh x).2
  exact ⟨D.EF (h a) (h b), -c, by linear_combination hc⟩

end GlobalTheory.SimAlg
