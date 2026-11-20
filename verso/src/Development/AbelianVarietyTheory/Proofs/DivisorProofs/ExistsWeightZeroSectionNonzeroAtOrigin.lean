import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecSuccOfRelAmple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRingEquiv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.OriginSec

/- English proof (translation)
Establish `key : ∀ (U : Y.Opens) (_ : r z ∈ U) (f : Γ(Y, U)), IsUnit (gs r z U f) ↔ IsUnit (gs (𝟙 Y) (r z) U f)` using `fun U h f => by rw [gs_stalkMap r z U h, isUnit_map_iff]`. Use `⟨fun h => (mem_nonzeroLocus s _).2 ⟨_, hJ.mem φ r, (key _ (hJ.mem φ r) _).1 h⟩, fun h => ?_⟩` and prove the remaining obligations. Take `⟨j, hj, hu⟩` from `(mem_nonzeroLocus s _).1 h`. Rewrite using `[sval, sec_trans s r z (hJ.mem φ r) hj]`. Conclude with `(Units.isUnit _).mul ((key _ hj _).2 hu)`.
-/
theorem isUnit_sval_iff' {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    IsUnit (sval s r z J) ↔ r z ∈ nonzeroLocus s := by
  have key : ∀ (U : Y.Opens) (_ : r z ∈ U) (f : Γ(Y, U)), IsUnit (gs r z U f) ↔ IsUnit (gs (𝟙 Y) (r z) U f) :=
    fun U h f => by rw [gs_stalkMap r z U h, isUnit_map_iff]
  refine ⟨fun h => (mem_nonzeroLocus s _).2 ⟨_, hJ.mem φ r, (key _ (hJ.mem φ r) _).1 h⟩, fun h => ?_⟩
  obtain ⟨j, hj, hu⟩ := (mem_nonzeroLocus s _).1 h
  rw [sval, sec_trans s r z (hJ.mem φ r) hj]
  exact (Units.isUnit _).mul ((key _ hj _).2 hu)

/- English proof (translation)
Establish `h` using `D.c_add 0 0`. Simplify using `only [add_zero, padd] at h`. Rewrite `h` using `[← Hom.mul_def]`. Establish `: D.c 0 = 1` using `by simpa using h`. Rewrite using `[this, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]`.
-/
theorem c_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) : D.c 0 = η[D.P.A] := by
  have h := D.c_add 0 0
  simp only [add_zero, padd] at h
  rw [← Hom.mul_def] at h
  have : D.c 0 = 1 := by simpa using h
  rw [this, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

/- English proof (translation)
Establish `e1 : (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ η[D.P.A])).left = 𝟙 D.P.A.left`. Rewrite using `[padd, ← Hom.mul_def, ← Hom.one_def, _root_.mul_one]`. Both sides reduce to the same expression. Introduce `U _ h`. Rewrite using `[Fin.prod_univ_four, Fin.prod_univ_one]`.

Simplify using `only [DegPre.famφB, DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, c_zero, e1]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_zpow]`. Use `module`.
-/
theorem formEq_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (k : ℕ) :
    FormEq (K := Fin 1) (fun _ => 𝟙 D.P.A.left) (fun _ => (k : ℤ)) (D.famφB 0) (DegPre.famε k) := by
  have e1 : (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ η[D.P.A])).left = 𝟙 D.P.A.left := by
    rw [padd, ← Hom.mul_def, ← Hom.one_def, _root_.mul_one]; rfl
  intro U _ h
  rw [Fin.prod_univ_four, Fin.prod_univ_one]
  simp only [DegPre.famφB, DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, c_zero, e1]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  module

end GlobalTheory.Mum.OriginSec

open GlobalTheory.Mum.OriginSec GlobalTheory.SecRingIso in

/- English proof (translation)
Introduce `R _ _ _ _ D`. Establish `: IsProper D.toPre.P.A.hom` using `D.toPre.P.isAb.proper`. Take `⟨n, hn, a, b, ha, hb⟩` from `GlobalTheory.exists_sec_succ_of_relAmple R D.toPre.P.A D.toPre.P.L D.toPre.P.isLB D.toPre.P.ample (eSec D.toPre.P.A (closedPoint R))`. Set `Q : ℕ → Prop` to `fun m => ∃ d : H0 D.toPre.P.L m, eSec D.toPre.P.A (closedPoint R) ∈ nonzeroLocus d`. Establish `hQ : ∀ m m', Q m → Q m' → Q (m + m')` using `fun m m' ⟨d, hd⟩ ⟨d', hd'⟩ => by`.

Take `⟨e, he⟩` from `exists_mul d d'`. Conclude with `⟨e, mem_mul he hd hd'⟩`. Establish `hij : ∀ i j : ℕ, Q (n * (i + 1) + (n + 1) * j)`. Introduce `i j`. Proceed by induction on `j with`.

Consider the case `zero`. Proceed by induction on `i with`. Consider the case `zero => simpa using (⟨a, ha⟩ : Q n)`. Consider the case `succ i ih`. Use `hQ _ _ ih ⟨a, ha⟩` as an intermediate fact.

Rewrite using `[show n * (i + 1 + 1) + (n + 1) * 0 = n * (i + 1) + (n + 1) * 0 + n by ring]` and apply the resulting hypothesis. Consider the case `succ j ih`. Use `hQ _ _ ih ⟨b, hb⟩` as an intermediate fact. Rewrite using `[show n * (i + 1) + (n + 1) * (j + 1) = n * (i + 1) + (n + 1) * j + (n + 1) by ring]` and apply the resulting hypothesis. Use `⟨n * (n + 1), fun k hk => ?_⟩` and prove the remaining obligations.

Choose the witnesses or unpack the hypotheses as in `⟨d, hd⟩ : Q k := by`. Establish `hk' : n * (k / n) + k % n = k` using `Nat.div_add_mod k n`. Establish `hr : k % n < n` using `Nat.mod_lt _ hn`. Establish `hq : n + 1 ≤ k / n` using `(Nat.le_div_iff_mul_le hn).2 (by rw [mul_comm]; exact hk)`. Take `⟨t, ht⟩ : ∃ t, k / n = k % n + 1 + t` from `⟨k / n - k % n - 1, by omega⟩`.

Establish `e : k = n * (t + 1) + (n + 1) * (k % n)` using `by conv_lhs => rw [← hk', ht]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `hij _ _`. Take `⟨b', hb'⟩` from `exists_sec D.toPre.P.isLB (formEq_zero D.toPre k) d`.

Use `⟨b', ?_⟩` and prove the remaining obligations. Take `⟨J, hJ⟩ : ∃ J, Good D.toPre.P.L (eSec D.toPre.P.A (closedPoint R)) J` from `⟨fun χ => (exists_chart D.toPre.P.isLB (χ (eSec D.toPre.P.A (closedPoint R)))).choose, fun χ => (exists_chart D.toPre.P.isLB (χ (eSec D.toPre.P.A (closedPoint R)))).choose_spec⟩`. Establish `h1` using `(isUnit_sval_iff' d (𝟙 _) _ hJ).2 hd`. Rewrite `h1` using `[← hb' _ (𝟙 _) _ J hJ]`. Conclude with `(isUnit_sval_iff' b' (𝟙 _) _ hJ).1 h1`.
-/
theorem GlobalTheory.Mum.exists_secB_zero_nonzero_origin : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∃ k₀ : ℕ, ∀ k ≥ k₀, ∃ b : D.toPre.SecB k 0, eSec D.toPre.P.A (closedPoint R) ∈ nonzeroLocus b := by
  intro R _ _ _ _ D
  have : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  obtain ⟨n, hn, a, b, ha, hb⟩ := GlobalTheory.exists_sec_succ_of_relAmple R D.toPre.P.A D.toPre.P.L D.toPre.P.isLB
    D.toPre.P.ample (eSec D.toPre.P.A (closedPoint R))
  let Q : ℕ → Prop := fun m => ∃ d : H0 D.toPre.P.L m, eSec D.toPre.P.A (closedPoint R) ∈ nonzeroLocus d
  have hQ : ∀ m m', Q m → Q m' → Q (m + m') := fun m m' ⟨d, hd⟩ ⟨d', hd'⟩ => by
    obtain ⟨e, he⟩ := exists_mul d d'
    exact ⟨e, mem_mul he hd hd'⟩
  have hij : ∀ i j : ℕ, Q (n * (i + 1) + (n + 1) * j) := by
    intro i j
    induction j with
    | zero =>
      induction i with
      | zero => simpa using (⟨a, ha⟩ : Q n)
      | succ i ih =>
        have := hQ _ _ ih ⟨a, ha⟩
        rwa [show n * (i + 1 + 1) + (n + 1) * 0 = n * (i + 1) + (n + 1) * 0 + n by ring]
    | succ j ih =>
      have := hQ _ _ ih ⟨b, hb⟩
      rwa [show n * (i + 1) + (n + 1) * (j + 1) = n * (i + 1) + (n + 1) * j + (n + 1) by ring]
  refine ⟨n * (n + 1), fun k hk => ?_⟩
  obtain ⟨d, hd⟩ : Q k := by
    have hk' : n * (k / n) + k % n = k := Nat.div_add_mod k n
    have hr : k % n < n := Nat.mod_lt _ hn
    have hq : n + 1 ≤ k / n := (Nat.le_div_iff_mul_le hn).2 (by rw [mul_comm]; exact hk)
    obtain ⟨t, ht⟩ : ∃ t, k / n = k % n + 1 + t := ⟨k / n - k % n - 1, by omega⟩
    have e : k = n * (t + 1) + (n + 1) * (k % n) := by
      conv_lhs => rw [← hk', ht]
      ring
    rw [e]
    exact hij _ _
  obtain ⟨b', hb'⟩ := exists_sec D.toPre.P.isLB (formEq_zero D.toPre k) d
  refine ⟨b', ?_⟩
  obtain ⟨J, hJ⟩ : ∃ J, Good D.toPre.P.L (eSec D.toPre.P.A (closedPoint R)) J :=
    ⟨fun χ => (exists_chart D.toPre.P.isLB (χ (eSec D.toPre.P.A (closedPoint R)))).choose,
      fun χ => (exists_chart D.toPre.P.isLB (χ (eSec D.toPre.P.A (closedPoint R)))).choose_spec⟩
  have h1 := (isUnit_sval_iff' d (𝟙 _) _ hJ).2 hd
  rw [← hb' _ (𝟙 _) _ J hJ] at h1
  exact (isUnit_sval_iff' b' (𝟙 _) _ hJ).1 h1
