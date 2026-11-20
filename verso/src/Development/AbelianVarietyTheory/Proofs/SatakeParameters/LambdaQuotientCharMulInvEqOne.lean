import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.TwistRowType

variable {E : Type} [Field E] [NumberField E]

def intSub (P : HeightOneSpectrum (𝓞 E)) : Subring E where
  carrier := {a | IntAt P a}
  mul_mem' := IntAt.mul
  one_mem' := by simpa using IntAt.coe P 1
  add_mem' := IntAt.add
  zero_mem' := by simpa using IntAt.coe P 0
  neg_mem' := fun {a} ha => by
    have h := IntAt.mul (IntAt.coe P (-1)) ha
    simpa using h

def redHom (P : HeightOneSpectrum (𝓞 E)) : intSub P →+* 𝓞 E ⧸ P.asIdeal where
  toFun a := redP P a.1
  map_one' := by simpa using reduction_coe P 1
  map_mul' a b := reduction_mul a.2 b.2
  map_zero' := by simpa using reduction_coe P 0
  map_add' a b := reduction_add a.2 b.2

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem redHom_apply (P : HeightOneSpectrum (𝓞 E)) (a : intSub P) : redHom P a = redP P a.1 := rfl

/- English proof (translation)
Establish `ha : IsUnit (redP P a)` using `isUnit_iff_exists_inv.2 ⟨_, h⟩`. Establish `hb : IsUnit (redP P b)` using `isUnit_iff_exists_inv'.2 ⟨_, h⟩`. Establish `hu : ha.unit * hb.unit = 1` using `Units.ext (by simpa using h)`. Simplify using `only [LocE.unitV, dif_pos ha, dif_pos hb]`. Rewrite using `[← Units.val_mul, ← map_mul, hu, map_one, Units.val_one]`.
-/
theorem unitV_mul_eq_one {K : Type} [Field K] {P : HeightOneSpectrum (𝓞 E)} (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    {a b : E} (h : redP P a * redP P b = 1) : LocE.unitV ξ a * LocE.unitV ξ b = 1 := by
  have ha : IsUnit (redP P a) := isUnit_iff_exists_inv.2 ⟨_, h⟩
  have hb : IsUnit (redP P b) := isUnit_iff_exists_inv'.2 ⟨_, h⟩
  have hu : ha.unit * hb.unit = 1 := Units.ext (by simpa using h)
  simp only [LocE.unitV, dif_pos ha, dif_pos hb]
  rw [← Units.val_mul, ← map_mul, hu, map_one, Units.val_one]

variable [StarRing E]

/- English proof (translation)
The claim follows from `mem_localization_standardLattice P x`.
-/
theorem mem_stdAt (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (x : Sp E n) :
    x ∈ stdAt E n P ↔ ∀ i, IntAt P (x i) := mem_localization_standardLattice P x

/- English proof (translation)
Rewrite using `[LocE.parL, LocE.sclLat, Submodule.mem_comap, mem_stdAt]`. Conclude with `Iff.rfl`.
-/
theorem mem_parL (P : HeightOneSpectrum (𝓞 E)) (q kj n : ℕ) (x : Sp E (n + 0)) :
    x ∈ LocE.parL P q kj n 0 ↔
      ∀ i : Fin (n + 0), IntAt P (((q : E) ^ (if kj ≤ i.1 ∧ i.1 < n then (1 : ℤ) else 0))⁻¹ * x i) := by
  rw [LocE.parL, LocE.sclLat, Submodule.mem_comap, mem_stdAt]
  exact Iff.rfl

/- English proof (translation)
Rewrite using `[mem_stdAt]`. Introduce `j`. Unfold `Loc.eN`. Use `split_ifs`. Simplify using `using IntAt.coe P 1`.

Simplify using `using IntAt.coe P 0`.
-/
theorem eN_mem (P : HeightOneSpectrum (𝓞 E)) (N i : ℕ) : Loc.eN E N i ∈ stdAt E N P := by
  rw [mem_stdAt]
  intro j
  unfold Loc.eN
  split_ifs
  · simpa using IntAt.coe P 1
  · simpa using IntAt.coe P 0

/- English proof (translation)
Establish `hg' : ∀ x, g x ∈ stdAt E N P ↔ x ∈ stdAt E N P` using `hg`. Establish `hm : g (Loc.eN E N j) ∈ stdAt E N P` using `(hg' _).2 (eN_mem P N j)`. Rewrite `hm` using `[mem_stdAt]`. Unfold `Loc.atN`. Use `split_ifs with h`.

Conclude with `hm _`. Simplify using `using IntAt.coe P 0`.
-/
theorem intAt_entry (P : HeightOneSpectrum (𝓞 E)) {N : ℕ} {g : Sp E N ≃ₗ[E] Sp E N}
    (hg : g ∈ stabL E N (stdAt E N P)) (i j : ℕ) : IntAt P (Loc.atN (g (Loc.eN E N j)) i) := by
  have hg' : ∀ x, g x ∈ stdAt E N P ↔ x ∈ stdAt E N P := hg
  have hm : g (Loc.eN E N j) ∈ stdAt E N P := (hg' _).2 (eN_mem P N j)
  rw [mem_stdAt] at hm
  unfold Loc.atN
  split_ifs with h
  · exact hm _
  · simpa using IntAt.coe P 0

def blockD (P : HeightOneSpectrum (𝓞 E)) (kj n : ℕ) {N : ℕ} {g : Sp E N ≃ₗ[E] Sp E N}
    (hg : g ∈ stabL E N (stdAt E N P)) : Matrix (Fin (n - kj)) (Fin (n - kj)) (intSub P) :=
  Matrix.of fun s t => ⟨Loc.atN (g (Loc.eN E N (kj + t.1))) (kj + s.1), intAt_entry P hg _ _⟩

/- English proof (translation)
Establish `h1 : (Matrix.of fun s t : Fin (n - kj) => Loc.atN (g.toLinearMap (Loc.eN E N (kj + t.1))) (kj + s.1)) = (intSub P).subtype.mapMatrix (blockD P kj n hg)`. Use extensionality with `s t`. Both sides reduce to the same expression. Rewrite using `[h1, ← RingHom.map_det, ← RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem redP_det_block (P : HeightOneSpectrum (𝓞 E)) (kj n : ℕ) {N : ℕ} {g : Sp E N ≃ₗ[E] Sp E N}
    (hg : g ∈ stabL E N (stdAt E N P)) :
    redP P (Matrix.det (Matrix.of fun s t : Fin (n - kj) =>
      Loc.atN (g.toLinearMap (Loc.eN E N (kj + t.1))) (kj + s.1))) =
      ((redHom P).mapMatrix (blockD P kj n hg)).det := by
  have h1 : (Matrix.of fun s t : Fin (n - kj) =>
      Loc.atN (g.toLinearMap (Loc.eN E N (kj + t.1))) (kj + s.1)) =
      (intSub P).subtype.mapMatrix (blockD P kj n hg) := by
    ext s t
    rfl
  rw [h1, ← RingHom.map_det, ← RingHom.map_det]
  rfl

/- English proof (translation)
Establish `hI1 : IntAt P (1 : E)` using `by simpa using IntAt.coe P 1`. Establish `hI0 : IntAt P (0 : E)` using `by simpa using IntAt.coe P 0`. Break down `le_or_gt kj n with hkn | hkn` into its components or cases. Use `swap`. Use extensionality with `s t`.

It suffices to derive a contradiction. Use `s.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `set h := g⁻¹ with hh`. Establish `hent : ∀ (f : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0)) (i j : ℕ) (hi : i < n + 0) (hj : j < n + 0), Loc.atN (f (Loc.eN E (n + 0) j)) i = LinearMap.toMatrix' f.toLinearMap ⟨i, hi⟩ ⟨j, hj⟩`.

Introduce `f i j hi hj`. Rewrite using `[LinearMap.toMatrix'_apply, LinearEquiv.coe_coe, Loc.atN, dif_pos hi]`. Establish `he : Loc.eN E (n + 0) j = Pi.single (⟨j, hj⟩ : Fin (n + 0)) (1 : E)`. Use function extensionality and compare the values at `l`. Simplify using `[Loc.eN, Pi.single_apply, Fin.ext_iff]`.

Rewrite using `[he]`. Establish `hMM : LinearMap.toMatrix' g.toLinearMap * LinearMap.toMatrix' h.toLinearMap = 1`. Rewrite using `[← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]`. Use `congr 1`. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `x`. Conclude with `g.apply_symm_apply x`. Establish `hpar : ∀ x, g x ∈ LocE.parL P q kj n 0 ↔ x ∈ LocE.parL P q kj n 0` using `hp`. Establish `hq0E : (q : E) ≠ 0` using `Nat.cast_ne_zero.mpr hq0`. Establish `hqI : IntAt P (q : E)` using `by simpa using IntAt.coe P (q : 𝓞 E)`.

Establish `hredq : redP P (q : E) = 0`. Establish `hc` using `reduction_coe P (q : 𝓞 E)`. Rewrite `hc` using `[map_natCast]`. Rewrite using `[hc, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hq`.

Establish `hlow : ∀ u, u < kj → ∀ s, kj + s < n → redP P (Loc.atN (g (Loc.eN E (n + 0) u)) (kj + s)) = 0`. Introduce `u hu s hs`. Establish `hmem : Loc.eN E (n + 0) u ∈ LocE.parL P q kj n 0`. Rewrite using `[mem_parL]`. Introduce `i`.

Unfold `Loc.eN`. Distinguish the cases in `hi : i.1 = u`. Establish `hc : ¬ (kj ≤ i.1 ∧ i.1 < n)` using `by omega`. Rewrite using `[if_pos hi, if_neg hc]`. Simplify using `using hI1`.

Rewrite using `[if_neg hi, mul_zero]`. Conclude with `hI0`. Establish `h2` using `(mem_parL P q kj n _).1 ((hpar _).2 hmem) ⟨kj + s, by omega⟩`. Establish `hc : kj ≤ kj + s ∧ kj + s < n` using `⟨by omega, hs⟩`. Simplify using `only [hc, and_self, ite_true, zpow_one] at h2`.

Establish `hval : Loc.atN (g (Loc.eN E (n + 0) u)) (kj + s) = (q : E) * ((q : E)⁻¹ * g (Loc.eN E (n + 0) u) ⟨kj + s, by omega⟩)`. Rewrite using `[Loc.atN, dif_pos (by omega : kj + s < n + 0), ← mul_assoc, mul_inv_cancel₀ hq0E, one_mul]`. Rewrite using `[hval, reduction_mul hqI h2, hredq, zero_mul]`. Establish `hid : ∀ s t : Fin (n - kj), ∑ u ∈ Finset.range (n + 0), Loc.atN (g (Loc.eN E (n + 0) u)) (kj + s.1) * Loc.atN (h (Loc.eN E (n + 0) (kj + t.1))) u = if s = t then 1 else 0`. Introduce `s t`.

Establish `hs : kj + s.1 < n + 0` using `by omega`. Establish `ht : kj + t.1 < n + 0` using `by omega`. Establish `h3` using `congrFun (congrFun hMM ⟨kj + s.1, hs⟩) ⟨kj + t.1, ht⟩`. Rewrite `h3` using `[Matrix.mul_apply, Matrix.one_apply]`. Rewrite using `[← Fin.sum_univ_eq_sum_range]`.

Use `h3 using 1` and compare the differences between its conclusion and the goal. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Rewrite using `[hent g _ _ hs u.2, hent h _ _ u.2 ht]`. Simplify using `[Fin.ext_iff]`. Use extensionality with `s t`.

Rewrite using `[RingHom.mapMatrix_apply, Matrix.map_apply]`. Use `set X := (blockD P kj n hg * blockD P kj n hg') s t with hXdef`. Apply the tactic sequence `set Y : intSub P := ∑ u ∈ Finset.range kj, (⟨Loc.atN (g (Loc.eN E (n + 0) u)) (kj + s.1), intAt_entry P hg _ _⟩ : intSub P) * ⟨Loc.atN (h (Loc.eN E (n + 0) (kj + t.1))) u, intAt_entry P hg' _ _⟩ with hYdef`. Establish `hY : ((Y : intSub P) : E) = ∑ u ∈ Finset.range kj, Loc.atN (g (Loc.eN E (n + 0) u)) (kj + s.1) * Loc.atN (h (Loc.eN E (n + 0) (kj + t.1))) u`. Rewrite using `[hYdef]`.

Use `push_cast`. Both sides reduce to the same expression. Establish `hXE : ((X : intSub P) : E) = ∑ x ∈ Finset.range (n - kj), Loc.atN (g (Loc.eN E (n + 0) (kj + x))) (kj + s.1) * Loc.atN (h (Loc.eN E (n + 0) (kj + t.1))) (kj + x)`. Rewrite using `[hXdef, Matrix.mul_apply]`. Use `push_cast`.

Rewrite using `[← Fin.sum_univ_eq_sum_range (fun x => Loc.atN (g (Loc.eN E (n + 0) (kj + x))) (kj + s.1) * Loc.atN (h (Loc.eN E (n + 0) (kj + t.1))) (kj + x)) (n - kj)]`. Both sides reduce to the same expression. Establish `hsum` using `hid s t`. Rewrite `hsum` using `[show Finset.range (n + 0) = Finset.range (kj + (n - kj)) from congrArg _ (by omega), Finset.sum_range_add]`. Establish `hXY : X + Y = (1 : Matrix (Fin (n - kj)) (Fin (n - kj)) (intSub P)) s t`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Matrix.one_apply]`. Use `show (X : E) + (Y : E) = _`. Rewrite using `[hXE, hY, add_comm, hsum]`. Apply the tactic sequence `split_ifs <;> rfl`.

Establish `hred : redHom P Y = 0`. Rewrite using `[hYdef, map_sum]`. Use `Finset.sum_eq_zero fun u hu => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Simplify using `only [redHom_apply]`.

Rewrite using `[hlow u (Finset.mem_range.1 hu) s.1 (by omega), zero_mul]`. Establish `h4` using `congrArg (redHom P) hXY`. Rewrite `h4` using `[map_add, hred, add_zero]`. Rewrite using `[h4, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem block_mul (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (hq0 : q ≠ 0) (hq : (q : 𝓞 E) ∈ P.asIdeal) (kj n : ℕ)
    {g : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0)} (hg : g ∈ stabL E (n + 0) (stdAt E (n + 0) P))
    (hg' : g⁻¹ ∈ stabL E (n + 0) (stdAt E (n + 0) P)) (hp : g ∈ stabL E (n + 0) (LocE.parL P q kj n 0)) :
    (redHom P).mapMatrix (blockD P kj n hg * blockD P kj n hg') = 1 := by
  classical
  have hI1 : IntAt P (1 : E) := by simpa using IntAt.coe P 1
  have hI0 : IntAt P (0 : E) := by simpa using IntAt.coe P 0
  rcases le_or_gt kj n with hkn | hkn
  swap
  · ext s t
    exfalso
    have := s.2
    omega
  set h := g⁻¹ with hh

  have hent : ∀ (f : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0)) (i j : ℕ) (hi : i < n + 0) (hj : j < n + 0),
      Loc.atN (f (Loc.eN E (n + 0) j)) i = LinearMap.toMatrix' f.toLinearMap ⟨i, hi⟩ ⟨j, hj⟩ := by
    intro f i j hi hj
    rw [LinearMap.toMatrix'_apply, LinearEquiv.coe_coe, Loc.atN, dif_pos hi]
    have he : Loc.eN E (n + 0) j = Pi.single (⟨j, hj⟩ : Fin (n + 0)) (1 : E) := by
      funext l
      simp [Loc.eN, Pi.single_apply, Fin.ext_iff]
    rw [he]
  have hMM : LinearMap.toMatrix' g.toLinearMap * LinearMap.toMatrix' h.toLinearMap = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    apply LinearMap.ext
    intro x
    exact g.apply_symm_apply x

  have hpar : ∀ x, g x ∈ LocE.parL P q kj n 0 ↔ x ∈ LocE.parL P q kj n 0 := hp
  have hq0E : (q : E) ≠ 0 := Nat.cast_ne_zero.mpr hq0
  have hqI : IntAt P (q : E) := by simpa using IntAt.coe P (q : 𝓞 E)
  have hredq : redP P (q : E) = 0 := by
    have hc := reduction_coe P (q : 𝓞 E)
    rw [map_natCast] at hc
    rw [hc, Ideal.Quotient.eq_zero_iff_mem]
    exact hq
  have hlow : ∀ u, u < kj → ∀ s, kj + s < n →
      redP P (Loc.atN (g (Loc.eN E (n + 0) u)) (kj + s)) = 0 := by
    intro u hu s hs
    have hmem : Loc.eN E (n + 0) u ∈ LocE.parL P q kj n 0 := by
      rw [mem_parL]
      intro i
      unfold Loc.eN
      by_cases hi : i.1 = u
      · have hc : ¬ (kj ≤ i.1 ∧ i.1 < n) := by omega
        rw [if_pos hi, if_neg hc]
        simpa using hI1
      · rw [if_neg hi, mul_zero]
        exact hI0
    have h2 := (mem_parL P q kj n _).1 ((hpar _).2 hmem) ⟨kj + s, by omega⟩
    have hc : kj ≤ kj + s ∧ kj + s < n := ⟨by omega, hs⟩
    simp only [hc, and_self, ite_true, zpow_one] at h2
    have hval : Loc.atN (g (Loc.eN E (n + 0) u)) (kj + s) =
        (q : E) * ((q : E)⁻¹ * g (Loc.eN E (n + 0) u) ⟨kj + s, by omega⟩) := by
      rw [Loc.atN, dif_pos (by omega : kj + s < n + 0), ← mul_assoc, mul_inv_cancel₀ hq0E, one_mul]
    rw [hval, reduction_mul hqI h2, hredq, zero_mul]

  have hid : ∀ s t : Fin (n - kj), ∑ u ∈ Finset.range (n + 0),
      Loc.atN (g (Loc.eN E (n + 0) u)) (kj + s.1) * Loc.atN (h (Loc.eN E (n + 0) (kj + t.1))) u =
      if s = t then 1 else 0 := by
    intro s t
    have hs : kj + s.1 < n + 0 := by omega
    have ht : kj + t.1 < n + 0 := by omega
    have h3 := congrFun (congrFun hMM ⟨kj + s.1, hs⟩) ⟨kj + t.1, ht⟩
    rw [Matrix.mul_apply, Matrix.one_apply] at h3
    rw [← Fin.sum_univ_eq_sum_range]
    convert h3 using 1
    · refine Finset.sum_congr rfl fun u _ => ?_
      rw [hent g _ _ hs u.2, hent h _ _ u.2 ht]
    · simp [Fin.ext_iff]
  ext s t
  rw [RingHom.mapMatrix_apply, Matrix.map_apply]
  set X := (blockD P kj n hg * blockD P kj n hg') s t with hXdef
  set Y : intSub P := ∑ u ∈ Finset.range kj,
    (⟨Loc.atN (g (Loc.eN E (n + 0) u)) (kj + s.1), intAt_entry P hg _ _⟩ : intSub P) *
      ⟨Loc.atN (h (Loc.eN E (n + 0) (kj + t.1))) u, intAt_entry P hg' _ _⟩ with hYdef
  have hY : ((Y : intSub P) : E) = ∑ u ∈ Finset.range kj,
      Loc.atN (g (Loc.eN E (n + 0) u)) (kj + s.1) * Loc.atN (h (Loc.eN E (n + 0) (kj + t.1))) u := by
    rw [hYdef]
    push_cast
    rfl
  have hXE : ((X : intSub P) : E) = ∑ x ∈ Finset.range (n - kj),
      Loc.atN (g (Loc.eN E (n + 0) (kj + x))) (kj + s.1) *
        Loc.atN (h (Loc.eN E (n + 0) (kj + t.1))) (kj + x) := by
    rw [hXdef, Matrix.mul_apply]
    push_cast
    rw [← Fin.sum_univ_eq_sum_range (fun x => Loc.atN (g (Loc.eN E (n + 0) (kj + x))) (kj + s.1) *
        Loc.atN (h (Loc.eN E (n + 0) (kj + t.1))) (kj + x)) (n - kj)]
    rfl
  have hsum := hid s t
  rw [show Finset.range (n + 0) = Finset.range (kj + (n - kj)) from congrArg _ (by omega),
    Finset.sum_range_add] at hsum
  have hXY : X + Y = (1 : Matrix (Fin (n - kj)) (Fin (n - kj)) (intSub P)) s t := by
    apply Subtype.ext
    rw [Matrix.one_apply]
    show (X : E) + (Y : E) = _
    rw [hXE, hY, add_comm, hsum]
    split_ifs <;> rfl
  have hred : redHom P Y = 0 := by
    rw [hYdef, map_sum]
    refine Finset.sum_eq_zero fun u hu => ?_
    rw [map_mul]
    simp only [redHom_apply]
    rw [hlow u (Finset.mem_range.1 hu) s.1 (by omega), zero_mul]
  have h4 := congrArg (redHom P) hXY
  rw [map_add, hred, add_zero] at h4
  rw [h4, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

/- English proof (translation)
Introduce `E K _ _ _ _ P q hq0 hq ξ kj n g hgJ`. Rewrite `hgJ` using `[LocE.JQ, Subgroup.mem_inf]`. Take `⟨hg, hp⟩` from `hgJ`. Establish `hg' : g⁻¹ ∈ stabL E (n + 0) (stdAt E (n + 0) P)` using `Subgroup.inv_mem _ hg`. Rewrite using `[LocE.lamQB, LocE.lamQB, ← mul_inv, unitV_mul_eq_one, inv_one]`.

Rewrite using `[redP_det_block P kj n hg, redP_det_block P kj n hg', ← Matrix.det_mul, ← RingHom.map_mul, block_mul P q hq0 hq kj n hg hg' hp, Matrix.det_one]`.
-/
theorem lamQB_mul_inv : ∀ (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ), q ≠ 0 → (q : 𝓞 E) ∈ P.asIdeal → ∀ (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (kj n : ℕ), ∀ g ∈ LocE.JQ P q kj n 0, LocE.lamQB ξ kj n g.toLinearMap * LocE.lamQB ξ kj n (g⁻¹).toLinearMap = 1 := by
  intro E K _ _ _ _ P q hq0 hq ξ kj n g hgJ
  rw [LocE.JQ, Subgroup.mem_inf] at hgJ
  obtain ⟨hg, hp⟩ := hgJ
  have hg' : g⁻¹ ∈ stabL E (n + 0) (stdAt E (n + 0) P) := Subgroup.inv_mem _ hg
  rw [LocE.lamQB, LocE.lamQB, ← mul_inv, unitV_mul_eq_one, inv_one]
  rw [redP_det_block P kj n hg, redP_det_block P kj n hg', ← Matrix.det_mul, ← RingHom.map_mul,
    block_mul P q hq0 hq kj n hg hg' hp, Matrix.det_one]

end GlobalTheory.TwistRowType
