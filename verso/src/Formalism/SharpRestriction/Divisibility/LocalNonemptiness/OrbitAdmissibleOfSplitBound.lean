import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.OrbitPlaces
import Formalism.LocalRingCardinality.HostCls

noncomputable section

namespace Formalism.MainNotions.DIV.Inh

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.OrbitPlaces

/- English proof (translation)
Establish `hfin : Finite (HH D)` using `Finite.of_fintype (Fin D.R.ord)`. Use `⟨hev, ?_⟩` and prove the remaining obligations. Establish `hpos : 0 < addOrderOf h` using `addOrderOf_pos h`. Take `⟨k, hk⟩` from `hev`. Use linear arithmetic over natural numbers and integers.
-/
theorem even_add_order_two_le (D : D7) (h : HH D) (hev : Even (addOrderOf h)) : Even (addOrderOf h) ∧ 2 ≤ addOrderOf h := by
  have hfin : Finite (HH D) := Finite.of_fintype (Fin D.R.ord)
  refine ⟨hev, ?_⟩
  have hpos : 0 < addOrderOf h := addOrderOf_pos h
  obtain ⟨k, hk⟩ := hev
  omega

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h5, hev, -⟩`. Use `⟨h5, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hs : IsSg D p`. Conclude with `Or.inl hs`.

Use `right`. Unfold `nP at hev`. Rewrite `hev` using `[if_neg hs]`. Conclude with `hev`. Introduce and unpack `⟨h5, hc⟩`.

Distinguish the cases in `hs : IsSg D p`. Establish `hpos : 0 < addOrderOf (2 • hP D p)`. Establish `hfin : Finite (HH D)` using `Finite.of_fintype (Fin D.R.ord)`. Conclude with `addOrderOf_pos _`. Use `⟨h5, ?_, ?_⟩` and prove the remaining obligations.

Unfold `nP`. Rewrite using `[if_pos hs]`. Conclude with `even_two_mul _`. Unfold `nP`. Rewrite using `[if_pos hs]`.

Use linear arithmetic over natural numbers and integers. Establish `hev : HEv D p` using `hc.resolve_left hs`. Take `⟨h1, h2⟩` from `even_add_order_two_le D (hP D p) hev`. Use `⟨h5, ?_, ?_⟩` and prove the remaining obligations. Unfold `nP`.

Rewrite using `[if_neg hs]`. Conclude with `h1`. Unfold `nP`. Rewrite using `[if_neg hs]`. Conclude with `h2`.
-/
theorem orbOK_iff (D : D7) (p : ℕ) : OrbOK D p ↔ 5 ≤ p ∧ (IsSg D p ∨ HEv D p) := by
  constructor
  · rintro ⟨h5, hev, -⟩
    refine ⟨h5, ?_⟩
    by_cases hs : IsSg D p
    · exact Or.inl hs
    · right
      unfold nP at hev
      rw [if_neg hs] at hev
      exact hev
  · rintro ⟨h5, hc⟩
    by_cases hs : IsSg D p
    · have hpos : 0 < addOrderOf (2 • hP D p) := by
        have hfin : Finite (HH D) := Finite.of_fintype (Fin D.R.ord)
        exact addOrderOf_pos _
      refine ⟨h5, ?_, ?_⟩
      · unfold nP
        rw [if_pos hs]
        exact even_two_mul _
      · unfold nP
        rw [if_pos hs]
        omega
    · have hev : HEv D p := hc.resolve_left hs
      obtain ⟨h1, h2⟩ := even_add_order_two_le D (hP D p) hev
      refine ⟨h5, ?_, ?_⟩
      · unfold nP
        rw [if_neg hs]
        exact h1
      · unfold nP
        rw [if_neg hs]
        exact h2

/- English proof (translation)
Assume the negation of the conclusion as `hlt`. Establish `h2 : 2 ≤ p` using `hp.two_le`. Establish `hne2 : p ≠ 2`. Introduce and unpack `rfl`. Apply `hs` to reduce the goal to its premises.

Establish `hm : 2 ∈ D.host.toHostRaw.QS.primeFactors` using `Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_trans (dvd_pow_self 2 (by omega)) D.host.tower_dvd, D.host.QS_pos.ne'⟩`. Conclude with `hm`. Establish `hne4 : p ≠ 4`. Introduce and unpack `rfl`. Evaluate the numerical expressions using `at hp`.

Take `rfl : p = 3` from `by omega`. Conclude with `hj (D.host.split_small 3 hp (by norm_num) h3)`.
-/
private theorem five_le_of_prime_not_small_not_split (D : D7) (p : ℕ) (hp : p.Prime) (h3 : 3 ≤ D.host.splitBound)
    (hs : p ∉ D.host.toHostRaw.small) (hj : ¬ jacobiSym (-(D.host.d : ℤ)) p = 1) : 5 ≤ p := by
  by_contra hlt
  have h2 : 2 ≤ p := hp.two_le
  have hne2 : p ≠ 2 := by
    rintro rfl
    apply hs
    have hm : 2 ∈ D.host.toHostRaw.QS.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_trans (dvd_pow_self 2 (by omega)) D.host.tower_dvd,
        D.host.QS_pos.ne'⟩
    exact hm
  have hne4 : p ≠ 4 := by
    rintro rfl
    norm_num at hp
  obtain rfl : p = 3 := by omega
  exact hj (D.host.split_small 3 hp (by norm_num) h3)

/- English proof (translation)
Establish `hcls : D.host.cls p = PrimeClass.inertClass ∨ D.host.cls p = PrimeClass.signal` using `hc`. Unfold `Formalism.BasicNotions.Host.cls Formalism.BasicNotions.primeClass at hcls`. Apply the tactic sequence `split_ifs at hcls with a1 a2 a3 a4 a5 <;> first`. Consider the case `exact five_le_of_prime_not_small_not_split D p hp h3 a1 a4`. Consider the case `simp at hcls`.
-/
theorem five_le_of_class (D : D7) (p : ℕ) (hp : p.Prime) (h3 : 3 ≤ D.host.splitBound) (hc : IsResidueClassZero D p ∨ IsSg D p) : 5 ≤ p := by
  have hcls : D.host.cls p = PrimeClass.inertClass ∨ D.host.cls p = PrimeClass.signal := hc
  unfold Formalism.BasicNotions.Host.cls Formalism.BasicNotions.primeClass at hcls
  split_ifs at hcls with a1 a2 a3 a4 a5 <;>
    first
      | exact five_le_of_prime_not_small_not_split D p hp h3 a1 a4
      | simp at hcls

/- English proof (translation)
The claim follows from `(orbOK_iff D p).2 ⟨five_le_of_class D p hp h3 (hc.imp And.left id), hc.elim (fun h => Or.inr h.2) Or.inl⟩`.
-/
theorem orbOK_of_class (D : D7) (p : ℕ) (hp : p.Prime) (h3 : 3 ≤ D.host.splitBound)
    (hc : (IsResidueClassZero D p ∧ HEv D p) ∨ IsSg D p) : OrbOK D p := (orbOK_iff D p).2 ⟨five_le_of_class D p hp h3 (hc.imp And.left id), hc.elim (fun h => Or.inr h.2) Or.inl⟩

/- English proof (translation)
Unfold `OrbitParityCond`. Conclude with `⟨fun p hp hc => orbOK_of_class D p hp h3 hc, fun p hp hc => five_le_of_class D p hp h3 (Or.inl hc)⟩`.
-/
theorem orbit_admissible_of_split_bound (D : D7) (h3 : 3 ≤ D.host.splitBound) : OrbitParityCond D := by
  unfold OrbitParityCond
  exact ⟨fun p hp hc => orbOK_of_class D p hp h3 hc, fun p hp hc => five_le_of_class D p hp h3 (Or.inl hc)⟩

/- English proof (translation)
Establish `h3 : 3 ≤ ⌊L.sc.x ^ (L.sc.ez / 5)⌋₊` using `Nat.le_floor (by exact_mod_cast hx)`. Conclude with `orbit_admissible_of_split_bound D (h3.trans L.split_tie)`.
-/
theorem orbit_admissible_of_scale (D : D7) (L : SizeData₂ D) (hx : 3 ≤ L.sc.x ^ (L.sc.ez / 5)) : OrbitParityCond D := by
  have h3 : 3 ≤ ⌊L.sc.x ^ (L.sc.ez / 5)⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  exact orbit_admissible_of_split_bound D (h3.trans L.split_tie)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => ⟨h.nonneg, h.c6, h.dl1, h.dl1nn, h.dl2, h.dig⟩, fun ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h1, h2, h3, h4, h5, h6⟩⟩`.
-/
theorem cLarge_iff (C6 Cd : ℝ) (K : Formalism.MainNotions.G.Consts) (ce : ErrC) :
    CLarge C6 Cd K ce ↔ 0 ≤ Cd ∧ C6 ≤ ce.c6 ∧ 3 * Cd ≤ 1 + K.dl1 ∧ 0 ≤ K.dl1 ∧ 0 ≤ K.dl2 ∧ 3 * Cd ≤ ce.dig := ⟨fun h => ⟨h.nonneg, h.c6, h.dl1, h.dl1nn, h.dl2, h.dig⟩, fun ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h1, h2, h3, h4, h5, h6⟩⟩

/- English proof (translation)
Use `⟨{ La := 0, rho := 0, kII := 0, tII := 0, DII := 0, szII := 0, kII' := 0, DI := 0, kappaThresholdOne := 0, kappaThresholdTwo := 0, kI := 0, dl1 := 3 * C, dl2 := 0, Pr1 := 0, CN := 0 }, { c6 := max C6 12, dig := max (3 * C) 3, g := 10 }, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `⟨hC, le_max_left _ _, ?_, ?_, le_rfl, le_max_left _ _⟩` and prove the remaining obligations. Use `show 3 * C ≤ 1 + 3 * C`. Combine the linear equalities and inequalities to obtain the conclusion. Use `show (0 : ℝ) ≤ 3 * C`.

Combine the linear equalities and inequalities to obtain the conclusion. Unfold `Consts.Nonneg`. Use `⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, ?_, le_rfl, le_rfl, le_rfl⟩` and prove the remaining obligations. Use `show (0 : ℝ) ≤ 3 * C`. Combine the linear equalities and inequalities to obtain the conclusion.

Unfold `ErrC.Large`. Conclude with `⟨le_max_right _ _, le_max_right _ _, le_rfl⟩`.
-/
theorem exists_large_constants (C6 C : ℝ) (hC : 0 ≤ C) :
    ∃ (K : Formalism.MainNotions.G.Consts) (ce : ErrC), CLarge C6 C K ce ∧ K.Nonneg ∧ ce.Large := by
  refine ⟨{ La := 0, rho := 0, kII := 0, tII := 0, DII := 0, szII := 0, kII' := 0, DI := 0,
            kappaThresholdOne := 0, kappaThresholdTwo := 0, kI := 0, dl1 := 3 * C, dl2 := 0, Pr1 := 0, CN := 0 },
    { c6 := max C6 12, dig := max (3 * C) 3, g := 10 }, ?_, ?_, ?_⟩
  · refine ⟨hC, le_max_left _ _, ?_, ?_, le_rfl, le_max_left _ _⟩
    · show 3 * C ≤ 1 + 3 * C
      linarith
    · show (0 : ℝ) ≤ 3 * C
      linarith
  · unfold Consts.Nonneg
    refine ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, ?_,
      le_rfl, le_rfl, le_rfl⟩
    show (0 : ℝ) ≤ 3 * C
    linarith
  · unfold ErrC.Large
    exact ⟨le_max_right _ _, le_max_right _ _, le_rfl⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨by norm_num, by linarith, by linarith, by linarith, h2, by linarith⟩`.
-/
theorem CLarge_of_explicit (K : Formalism.MainNotions.G.Consts) (ce : ErrC) (h6 : ce.c6 = 12) (hd : ce.dig = 3) (hK : K.dl1 = 5) (h2 : 0 ≤ K.dl2) :
    CLarge 11 1 K ce := ⟨by norm_num, by linarith, by linarith, by linarith, h2, by linarith⟩

/- English proof (translation)
Introduce `h`. Establish `h1` using `h.dl1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem not_cLarge_of_dl1_eq_five (C : ℝ) (K : Formalism.MainNotions.G.Consts) (ce : ErrC) (hC : 11 ≤ C) (hK : K.dl1 = 5) : ¬ CLarge C C K ce := by
  intro h
  have h1 := h.dl1
  linarith

section Shape

variable {D : D7}

/- English proof (translation)
Use `SetLike.ext fun x => ?_` and prove the remaining obligations. Take `⟨r, j⟩` from `x`. Rewrite using `[YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_rowLen]`. Establish `h : (((E.nu u i z).rowLen r : ℕ) : ℝ) = (((E'.nu u i z).rowLen r : ℕ) : ℝ)` using `(E.nu_row u i hi z r).trans (E'.nu_row u i hi z r).symm`. Rewrite using `[Nat.cast_inj.mp h]`.
-/
theorem ent_nu_eq (E E' : Ent D) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (z : OrbitPlaces.Pl D) : E.nu u i z = E'.nu u i z := by
  refine SetLike.ext fun x => ?_
  obtain ⟨r, j⟩ := x
  rw [YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_rowLen]
  have h : (((E.nu u i z).rowLen r : ℕ) : ℝ) = (((E'.nu u i z).rowLen r : ℕ) : ℝ) :=
    (E.nu_row u i hi z r).trans (E'.nu_row u i hi z r).symm
  rw [Nat.cast_inj.mp h]

/- English proof (translation)
Unfold `Ent.size`. Rewrite using `[ent_nu_eq E E' u i hi z]`.
-/
theorem ent_size_eq (E E' : Ent D) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (z : OrbitPlaces.Pl D) : E.size u i z = E'.size u i z := by
  unfold Ent.size
  rw [ent_nu_eq E E' u i hi z]

/- English proof (translation)
Unfold `Ent.row`. Rewrite using `[ent_nu_eq E E' u i hi z]`.
-/
theorem ent_row_eq (E E' : Ent D) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (z : OrbitPlaces.Pl D) (r : ℕ) :
    E.row u i z r = E'.row u i z r := by
  unfold Ent.row
  rw [ent_nu_eq E E' u i hi z]

/- English proof (translation)
Unfold `Ent.cap`. Rewrite using `[ent_row_eq E E' u i hi z 1, ent_row_eq E E' u i hi z 0]`.
-/
theorem ent_cap_eq (E E' : Ent D) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (z : OrbitPlaces.Pl D) : E.cap u i z = E'.cap u i z := by
  unfold Ent.cap
  rw [ent_row_eq E E' u i hi z 1, ent_row_eq E E' u i hi z 0]

variable {L : SizeData₂ D} {X : Inst D L}

/- English proof (translation)
The claim follows from `h.wpos low := fun u i hi z hz => by rw [ent_size_eq E' E u i hi z] exact h.low u i hi z hz top := fun u i hi z hz => by rw [ent_size_eq E' E u i hi z, ent_row_eq E' E u i hi z] exact h.top u i hi z hz top1 := fun u i hi z hz => by rw [ent_row_eq E' E u i hi z] exact h.top1 u i hi …`.
-/
theorem shape_congr {E : Ent D} (h : Shape D L X E) (E' : Ent D) : Shape D L X E' where
  wpos := h.wpos
  low := fun u i hi z hz => by
    rw [ent_size_eq E' E u i hi z]
    exact h.low u i hi z hz
  top := fun u i hi z hz => by
    rw [ent_size_eq E' E u i hi z, ent_row_eq E' E u i hi z]
    exact h.top u i hi z hz
  top1 := fun u i hi z hz => by
    rw [ent_row_eq E' E u i hi z]
    exact h.top1 u i hi z hz
  sizeA := fun u i hi z => by
    rw [ent_size_eq E' E u i hi z]
    exact h.sizeA u i hi z
  rankA := h.rankA
  xa := h.xa
  capW := fun u i hi z => by
    rw [ent_cap_eq E' E u i hi z]
    exact h.capW u i hi z
  alG := fun u i hi t ht => by
    rw [ent_row_eq E' E u i hi, ent_row_eq E' E u i hi]
    exact h.alG u i hi t ht
  capG := fun u i hi z => by
    rw [ent_cap_eq E' E u i hi z]
    exact h.capG u i hi z

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => shape_congr h E', fun h => shape_congr h E⟩`.
-/
theorem shape_iff (E E' : Ent D) : Shape D L X E ↔ Shape D L X E' := ⟨fun h => shape_congr h E', fun h => shape_congr h E⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun ⟨E, h⟩ E' => shape_congr h E', fun h => (nonempty_entries D).elim fun E => ⟨E, h E⟩⟩`.
-/
theorem shape_exists_iff_forall : (∃ E : Ent D, Shape D L X E) ↔ ∀ E : Ent D, Shape D L X E := ⟨fun ⟨E, h⟩ E' => shape_congr h E', fun h => (nonempty_entries D).elim fun E => ⟨E, h E⟩⟩

end Shape

end Formalism.MainNotions.DIV.Inh

end
