import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import ReciprocityTheory.DualLattices.ExistsPrimitiveRoot
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonicalAcrisToBdRPlusUniqueEquivariantApproxStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.AdicMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section
namespace GlobalTheory.MemLoc.Model
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Establish `: NeZero ((l : ℕ) : Om l)` using `⟨Nat.cast_ne_zero.2 hl.ne_zero⟩`. Take `⟨z, hz⟩` from `IsAlgClosed.exists_root (Polynomial.cyclotomic l (Om l)) (ne_of_gt (Polynomial.degree_cyclotomic_pos l (Om l) hl.pos))`. Establish `hzp : IsPrimitiveRoot z l` using `Polynomial.isRoot_cyclotomic_iff.1 hz`. Use `choose r hr using fun x : Om l => IsAlgClosed.exists_pow_nat_eq x hl.pos`.

Use `⟨fun n => Nat.casesOn n 1 (fun m => r^[m] z), rfl, ?_, hzp.ne_one hl.one_lt⟩` and prove the remaining obligations. Introduce `n`. Consider the cases of `n with`. Consider the case `zero => exact hzp.pow_eq_one`. Consider the case `succ m => show (r^[m + 1] z) ^ l = r^[m] z`.

Rewrite using `[Function.iterate_succ_apply', hr]`.
-/
theorem exists_zeta (l : ℕ) [Fact l.Prime] :
    ∃ ζ : ℕ → Om l, ζ 0 = 1 ∧ (∀ m, ζ (m + 1) ^ l = ζ m) ∧ ζ 1 ≠ 1 := by
  have hl : l.Prime := Fact.out
  have : NeZero ((l : ℕ) : Om l) := ⟨Nat.cast_ne_zero.2 hl.ne_zero⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic l (Om l))
    (ne_of_gt (Polynomial.degree_cyclotomic_pos l (Om l) hl.pos))
  have hzp : IsPrimitiveRoot z l := Polynomial.isRoot_cyclotomic_iff.1 hz
  choose r hr using fun x : Om l => IsAlgClosed.exists_pow_nat_eq x hl.pos
  refine ⟨fun n => Nat.casesOn n 1 (fun m => r^[m] z), rfl, ?_, hzp.ne_one hl.one_lt⟩
  intro n
  cases n with
  | zero => exact hzp.pow_eq_one
  | succ m =>
    show (r^[m + 1] z) ^ l = r^[m] z
    rw [Function.iterate_succ_apply', hr]

/- English proof (translation)
Use `ReciprocityTheory.PGsh.untilt_eq_of_coeff (((frobeniusEquiv (Per.Fl l) l).symm)^[m] (ReciprocityTheory.PGsh.ofRoots f hf)) (fun n => f (n + m)) (fun n => by rw [Nat.add_right_comm]; exact hf _) (by` as an intermediate fact. Introduce `n`. Rewrite using `[← PreTilt.coeff_def, PreTilt.coeff_iterate_frobeniusEquiv_symm, PreTilt.coeff_def]`. Use the proof step `rfl)`. Simplify `this` using `[rootT]`.
-/
theorem rootT_ofRoots (f : ℕ → Per.OC l) (hf : ∀ n, f (n + 1) ^ l = f n) (m : ℕ) :
    rootT (ReciprocityTheory.PGsh.ofRoots f hf) m = f m := by
  have := ReciprocityTheory.PGsh.untilt_eq_of_coeff
    (((frobeniusEquiv (Per.Fl l) l).symm)^[m] (ReciprocityTheory.PGsh.ofRoots f hf))
    (fun n => f (n + m)) (fun n => by rw [Nat.add_right_comm]; exact hf _) (by
      intro n
      rw [← PreTilt.coeff_def, PreTilt.coeff_iterate_frobeniusEquiv_symm, PreTilt.coeff_def]
      rfl)
  simpa [rootT] using this

/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Establish `hn : ∀ m, ‖algebraMap (Om l) ℂ_[l] (ζ m)‖ ≤ 1`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => simp [h0]`.

Consider the case `succ m ih`. Rewrite `ih` using `[← hs m, map_pow, norm_pow]`. Conclude with `(pow_le_one_iff_of_nonneg (norm_nonneg _) hl.ne_zero).1 ih`. Set `f : ℕ → Per.OC l` to `fun m => ⟨_, (GlobalTheory.RingBasics.mem_OC _).2 (hn m)⟩`. Establish `hf : ∀ n, f (n + 1) ^ l = f n` using `fun n => Subtype.ext (by show (algebraMap (Om l) ℂ_[l] (ζ (n + 1))) ^ l = algebraMap (Om l) ℂ_[l] (ζ n)`.

Rewrite using `[← map_pow, hs])`. Conclude with `⟨ReciprocityTheory.PGsh.ofRoots f hf, fun m => by rw [rootT_ofRoots]⟩`.
-/
theorem exists_tilt (ζ : ℕ → Om l) (h0 : ζ 0 = 1) (hs : ∀ m, ζ (m + 1) ^ l = ζ m) :
    ∃ ε : Per.Fl l, ∀ m, (rootT ε m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (ζ m) := by
  have hl : l.Prime := Fact.out
  have hn : ∀ m, ‖algebraMap (Om l) ℂ_[l] (ζ m)‖ ≤ 1 := by
    intro m
    induction m with
    | zero => simp [h0]
    | succ m ih =>
      rw [← hs m, map_pow, norm_pow] at ih
      exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hl.ne_zero).1 ih
  let f : ℕ → Per.OC l := fun m => ⟨_, (GlobalTheory.RingBasics.mem_OC _).2 (hn m)⟩
  have hf : ∀ n, f (n + 1) ^ l = f n := fun n => Subtype.ext (by
    show (algebraMap (Om l) ℂ_[l] (ζ (n + 1))) ^ l = algebraMap (Om l) ℂ_[l] (ζ n)
    rw [← map_pow, hs])
  exact ⟨ReciprocityTheory.PGsh.ofRoots f hf, fun m => by rw [rootT_ofRoots]⟩

/- English proof (translation)
Use `⟨Subtype.ext ?_, fun hh => h1 ?_⟩` and prove the remaining obligations. Use `h 0` as an intermediate fact. Rewrite `this` using `[h0, map_one]`. Conclude with `this`. Use `h 1` as an intermediate fact.

Apply `(algebraMap (Om l) ℂ_[l]).injective` to reduce the goal to its premises. Rewrite using `[← this, map_one]`. Conclude with `congrArg Subtype.val hh`.
-/
theorem isEps_of_root {ζ : ℕ → Om l} (h0 : ζ 0 = 1) (h1 : ζ 1 ≠ 1) {ε : Per.Fl l}
    (h : ∀ m, (rootT ε m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (ζ m)) : IsEps ε := by
  refine ⟨Subtype.ext ?_, fun hh => h1 ?_⟩
  · have := h 0
    rw [h0, map_one] at this
    exact this
  · have := h 1
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← this, map_one]
    exact congrArg Subtype.val hh

/- English proof (translation)
Take `⟨ζ, h0, hs, h1⟩` from `exists_zeta l`. Take `⟨ε, h⟩` from `exists_tilt ζ h0 hs`. Conclude with `⟨ε, isEps_of_root h0 h1 h⟩`.
-/
theorem exists_isEps (l : ℕ) [Fact l.Prime] : ∃ e : Per.Fl l, IsEps e := by
  obtain ⟨ζ, h0, hs, h1⟩ := exists_zeta l
  obtain ⟨ε, h⟩ := exists_tilt ζ h0 hs
  exact ⟨ε, isEps_of_root h0 h1 h⟩

/- English proof (translation)
Introduce `h` and use `h.2 (by simp)`.
-/
theorem not_isEps_one : ¬ IsEps (1 : Per.Fl l) := fun h => h.2 (by simp)

/- English proof (translation)
The claim follows from `isEps_of_root C.ζ_zero C.ζ_one C.ε_root`.
-/
theorem core_isEps (C : Core l) : IsEps C.ε := isEps_of_root C.ζ_zero C.ζ_one C.ε_root

/- English proof (translation)
Assemble the required witnesses or components as `⟨(cyclotomicCharacter (Om l) l).comp (MulSemiringAction.toRingAut (GQ l) (Om l)), fun g m x hx => cyclotomicCharacter.spec l (n := m) (MulSemiringAction.toRingAut (GQ l) (Om l) g) x hx⟩`.
-/
theorem exists_chi (l : ℕ) [Fact l.Prime] : ∃ χ : GQ l →* ℤ_[l]ˣ, ∀ (g : GQ l) (m : ℕ) (x : Om l),
    x ^ (l ^ m) = 1 → g x = x ^ (PadicInt.toZModPow m (χ g : ℤ_[l])).val :=
  ⟨(cyclotomicCharacter (Om l) l).comp (MulSemiringAction.toRingAut (GQ l) (Om l)),
    fun g m x hx => cyclotomicCharacter.spec l (n := m) (MulSemiringAction.toRingAut (GQ l) (Om l) g) x hx⟩

/- English proof (translation)
Rewrite using `[xi, mu, mu, geom_sum_mul, ← map_pow]`. Use `congr 2`. Conclude with `((frobeniusEquiv (Per.Fl l) l).apply_symm_apply e).symm`.
-/
theorem mu_eq (e : Per.Fl l) : mu e = xi e * mu ((frobeniusEquiv (Per.Fl l) l).symm e) := by
  rw [xi, mu, mu, geom_sum_mul, ← map_pow]
  congr 2
  exact ((frobeniusEquiv (Per.Fl l) l).apply_symm_apply e).symm

/- English proof (translation)
Simplify using `[mu]`.
-/
theorem theta_mu (e : Per.Fl l) : Per.θ l (mu e) = e.untilt - 1 := by
  simp [mu]

/- English proof (translation)
Establish `h1` using `congrArg (Per.θ l) (mu_eq e)`. Rewrite `h1` using `[map_mul, theta_mu, theta_mu, h.1, sub_self]`. Conclude with `(mul_eq_zero.1 h1.symm).resolve_right (sub_ne_zero.2 h.2)`.
-/
theorem theta_xi {e : Per.Fl l} (h : IsEps e) : Per.θ l (xi e) = 0 := by
  have h1 := congrArg (Per.θ l) (mu_eq e)
  rw [map_mul, theta_mu, theta_mu, h.1, sub_self] at h1
  exact (mul_eq_zero.1 h1.symm).resolve_right (sub_ne_zero.2 h.2)

/- English proof (translation)
Take `⟨ι, hι⟩` from `GlobalTheory.CrisIncl.exists_incl l`. Take `⟨j, h1, h2, h3⟩` from `GlobalTheory.CrisIncl.exists_restrict l ι hι`. Establish `e : j = C.j` using `(GlobalTheory.T.canonicalAcrisToBdRPlus_unique_equivariant_approx l C.j C.j_cris).1 j ⟨h2, h3⟩`. Establish `e' : C.ι = ι` using `GlobalTheory.RingIface.bcris_ext l fun x => by rw [C.ι_j, h1, e]`. Rewrite using `[e']` and apply the resulting hypothesis.
-/
theorem core_isCrisDR (C : Core l) : Per.IsCrisDR l C.ι := by
  obtain ⟨ι, hι⟩ := GlobalTheory.CrisIncl.exists_incl l
  obtain ⟨j, h1, h2, h3⟩ := GlobalTheory.CrisIncl.exists_restrict l ι hι
  have e : j = C.j := (GlobalTheory.T.canonicalAcrisToBdRPlus_unique_equivariant_approx l C.j C.j_cris).1 j ⟨h2, h3⟩
  have e' : C.ι = ι := GlobalTheory.RingIface.bcris_ext l fun x => by rw [C.ι_j, h1, e]
  rwa [e']

/- English proof (translation)
Introduce `r` and use `⟨0, fun n _ => ⟨0, by simp [mu], 0, by simp⟩⟩`.
-/
theorem isLogA_one : IsLogA (1 : Per.Fl l) 0 := fun r => ⟨0, fun n _ => ⟨0, by simp [mu], 0, by simp⟩⟩

/- English proof (translation)
Rewrite using `[Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, -, rfl⟩`. Conclude with `⟨z, by rw [Algebra.smul_def, map_pow, map_natCast]⟩`. Introduce and unpack `⟨z, rfl⟩`.

Conclude with `⟨z, trivial, by rw [Algebra.smul_def, map_pow, map_natCast]⟩`.
-/
theorem mem_pc (R : Type) [CommRing R] (r : ℕ) (x : GlobalTheory.AdicMaps.PHat l R) :
    x ∈ ((Ideal.span {(l : R)}) ^ r • ⊤ : Submodule R (GlobalTheory.AdicMaps.PHat l R)) ↔
      ∃ z : GlobalTheory.AdicMaps.PHat l R, x = ((l : ℕ) : GlobalTheory.AdicMaps.PHat l R) ^ r * z := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨z, -, rfl⟩
    exact ⟨z, by rw [Algebra.smul_def, map_pow, map_natCast]⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, trivial, by rw [Algebra.smul_def, map_pow, map_natCast]⟩

/- English proof (translation)
The claim follows from `IsHausdorff.haus (I := Ideal.span {(l : R)}) inferInstance x fun r => by rw [SModEq.zero]; exact (mem_pc R r x).2 (h r)`.
-/
theorem pc_sep (R : Type) [CommRing R] (x : GlobalTheory.AdicMaps.PHat l R)
    (h : ∀ r, ∃ z : GlobalTheory.AdicMaps.PHat l R, x = ((l : ℕ) : GlobalTheory.AdicMaps.PHat l R) ^ r * z) : x = 0 :=
  IsHausdorff.haus (I := Ideal.span {(l : R)}) inferInstance x fun r => by
    rw [SModEq.zero]; exact (mem_pc R r x).2 (h r)

/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Establish `hc : IsAdicComplete (Ideal.span {(l : R)}) (GlobalTheory.AdicMaps.PHat l R)` using `AdicCompletion.isAdicComplete ⟨{(l : R)}, by simp⟩`. Take `⟨L, hL⟩` from `IsPrecomplete.prec (I := Ideal.span {(l : R)}) (M := GlobalTheory.AdicMaps.PHat l R) hc.toIsPrecomplete (f := fun r => algebraMap R _ (s (l ^ r))) (by`. Introduce `m n hmn`. Rewrite using `[SModEq.sub_mem, mem_pc]`.

Take `⟨z, hz⟩` from `hs m (l ^ n) (Nat.pow_le_pow_right hl.pos hmn)`. Use `⟨-algebraMap R _ z, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_sub, ← neg_sub, hz, map_neg, map_mul, map_pow, map_natCast, mul_neg])`. Use `⟨L, fun r n hn => ?_⟩` and prove the remaining obligations. Establish `h1` using `hL r`.

Rewrite `h1` using `[SModEq.sub_mem, mem_pc]`. Take `⟨z, hz⟩` from `h1`. Take `⟨w, hw⟩` from `hs r n hn`. Establish `h2` using `congrArg (algebraMap R (GlobalTheory.AdicMaps.PHat l R)) hw`. Rewrite `h2` using `[map_sub, map_mul, map_pow, map_natCast]`.

Conclude with `⟨-z - algebraMap R _ w, by linear_combination -hz - h2⟩`.
-/
theorem pc_lim (R : Type) [CommRing R] (s : ℕ → R)
    (hs : ∀ r n, l ^ r ≤ n → ∃ z : R, s n - s (l ^ r) = (l : R) ^ r * z) :
    ∃ y : GlobalTheory.AdicMaps.PHat l R, ∀ r n, l ^ r ≤ n →
      ∃ z : GlobalTheory.AdicMaps.PHat l R, y - algebraMap R _ (s n) = ((l : ℕ) : GlobalTheory.AdicMaps.PHat l R) ^ r * z := by
  have hl : l.Prime := Fact.out
  have hc : IsAdicComplete (Ideal.span {(l : R)}) (GlobalTheory.AdicMaps.PHat l R) :=
    AdicCompletion.isAdicComplete ⟨{(l : R)}, by simp⟩
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {(l : R)}) (M := GlobalTheory.AdicMaps.PHat l R) hc.toIsPrecomplete
    (f := fun r => algebraMap R _ (s (l ^ r))) (by
      intro m n hmn
      rw [SModEq.sub_mem, mem_pc]
      obtain ⟨z, hz⟩ := hs m (l ^ n) (Nat.pow_le_pow_right hl.pos hmn)
      refine ⟨-algebraMap R _ z, ?_⟩
      rw [← map_sub, ← neg_sub, hz, map_neg, map_mul, map_pow, map_natCast, mul_neg])
  refine ⟨L, fun r n hn => ?_⟩
  have h1 := hL r
  rw [SModEq.sub_mem, mem_pc] at h1
  obtain ⟨z, hz⟩ := h1
  obtain ⟨w, hw⟩ := hs r n hn
  have h2 := congrArg (algebraMap R (GlobalTheory.AdicMaps.PHat l R)) hw
  rw [map_sub, map_mul, map_pow, map_natCast] at h2
  exact ⟨-z - algebraMap R _ w, by linear_combination -hz - h2⟩

/- English proof (translation)
Take `⟨E, -⟩` from `GlobalTheory.AdicMaps.exists_acris_completion l`. Use `E.injective ?_` and prove the remaining obligations. Rewrite using `[map_zero]`. Use `pc_sep (l := l) (Per.Acris0 l) (E x) fun r => ?_` and prove the remaining obligations. Take `⟨z, hz⟩` from `h r`.

Conclude with `⟨E z, by rw [hz, map_mul, map_pow, map_natCast]⟩`.
-/
private theorem acris_sep (x : Per.Acris l)
    (h : ∀ r, ∃ z : Per.Acris l, x = ((l : ℕ) : Per.Acris l) ^ r * z) : x = 0 := by
  obtain ⟨E, -⟩ := GlobalTheory.AdicMaps.exists_acris_completion l
  refine E.injective ?_
  rw [map_zero]
  refine pc_sep (l := l) (Per.Acris0 l) (E x) fun r => ?_
  obtain ⟨z, hz⟩ := h r
  exact ⟨E z, by rw [hz, map_mul, map_pow, map_natCast]⟩

/- English proof (translation)
Take `⟨E, hE⟩` from `GlobalTheory.AdicMaps.exists_acris_completion l`. Take `⟨y, hy⟩` from `pc_lim (l := l) (Per.Acris0 l) s hs`. Use `⟨E.symm y, fun r n hn => ?_⟩` and prove the remaining obligations. Take `⟨z, hz⟩` from `hy r n hn`. Use `⟨E.symm z, E.injective ?_⟩` and prove the remaining obligations.

Rewrite using `[map_sub, map_mul, map_pow, map_natCast, hE, E.apply_symm_apply, E.apply_symm_apply]`. Conclude with `hz`.
-/
private theorem acris_lim (s : ℕ → Per.Acris0 l)
    (hs : ∀ r n, l ^ r ≤ n → ∃ z : Per.Acris0 l, s n - s (l ^ r) = (l : Per.Acris0 l) ^ r * z) :
    ∃ y : Per.Acris l, ∀ r n, l ^ r ≤ n → ∃ z : Per.Acris l,
      y - algebraMap (Per.Acris0 l) (Per.Acris l) (s n) = ((l : ℕ) : Per.Acris l) ^ r * z := by
  obtain ⟨E, hE⟩ := GlobalTheory.AdicMaps.exists_acris_completion l
  obtain ⟨y, hy⟩ := pc_lim (l := l) (Per.Acris0 l) s hs
  refine ⟨E.symm y, fun r n hn => ?_⟩
  obtain ⟨z, hz⟩ := hy r n hn
  refine ⟨E.symm z, E.injective ?_⟩
  rw [map_sub, map_mul, map_pow, map_natCast, hE, E.apply_symm_apply, E.apply_symm_apply]
  exact hz

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Use `acris_sep (y - y') fun r => ?_` and prove the remaining obligations. Take `⟨N, hN⟩` from `h r`. Take `⟨N', hN'⟩` from `h' r`. Take `⟨s, hs, z, hz⟩` from `hN (max N N') (le_max_left _ _)`.

Take `⟨s', hs', z', hz'⟩` from `hN' (max N N') (le_max_right _ _)`. Establish `: s = s'` using `Subtype.ext ((GlobalTheory.RingBasics.isUnit_nat l _ (Nat.factorial_ne_zero _)).mul_left_cancel (hs.trans hs'.symm))`. Substitute `this` using the available equality. Establish `key : y - y' = ((l : ℕ) : Per.Acris l) ^ r * (z - z')` using `by linear_combination hz - hz'`. Conclude with `⟨z - z', key⟩`.
-/
theorem isLogA_unique {e : Per.Fl l} {y y' : Per.Acris l} (h : IsLogA e y) (h' : IsLogA e y') : y = y' := by
  rw [← sub_eq_zero]
  refine acris_sep (y - y') fun r => ?_
  obtain ⟨N, hN⟩ := h r
  obtain ⟨N', hN'⟩ := h' r
  obtain ⟨s, hs, z, hz⟩ := hN (max N N') (le_max_left _ _)
  obtain ⟨s', hs', z', hz'⟩ := hN' (max N N') (le_max_right _ _)
  have : s = s' := Subtype.ext
    ((GlobalTheory.RingBasics.isUnit_nat l _ (Nat.factorial_ne_zero _)).mul_left_cancel (hs.trans hs'.symm))
  subst this
  have key : y - y' = ((l : ℕ) : Per.Acris l) ^ r * (z - z') := by linear_combination hz - hz'
  exact ⟨z - z', key⟩

/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Establish `hμ : Per.θ l (mu e) = 0` using `by rw [theta_mu, he, sub_self]`. Establish `hγ : ∀ k : ℕ, ∃ g : Per.Acris0 l, ((k.factorial : ℕ) : Per.AinfP l) * (g : Per.AinfP l) = algebraMap (Per.Ainf l) (Per.AinfP l) (mu e) ^ k`. Introduce `k`. Take `⟨d, hd⟩` from `(GlobalTheory.RingBasics.isUnit_nat l _ k.factorial_ne_zero).exists_right_inv`.

Establish `: ((k.factorial : ℕ) : Per.AinfP l) * (d * algebraMap (Per.Ainf l) (Per.AinfP l) (mu e) ^ k) = algebraMap (Per.Ainf l) (Per.AinfP l) (mu e) ^ k` using `by rw [← mul_assoc, hd, one_mul]`. Conclude with `⟨⟨_, GlobalTheory.RingIface.mem_Acris0_of_factorial_mul l (mu e) hμ k _ this⟩, this⟩`. Use `choose g hg using hγ`. Set `s : ℕ → Per.Acris0 l` to `fun n => ∑ k ∈ Finset.range n, (-1) ^ k * ((k.factorial : ℕ) : Per.Acris0 l) * g (k + 1)`. Take `⟨y, hy⟩` from `acris_lim (l := l) s (by`.

Introduce `r n hn`. Establish `: ((l : ℕ) : Per.Acris0 l) ^ r ∣ s n - s (l ^ r)`. Simplify using `only [s]`. Rewrite using `[← Finset.sum_Ico_eq_sub _ hn]`. Use `Finset.dvd_sum fun k hk => ?_` and prove the remaining obligations.

Establish `h1 : l ^ r ∣ k.factorial` using `Nat.dvd_factorial (pow_pos hl.pos r) (Finset.mem_Ico.1 hk).1`. Establish `h2 : ((l : ℕ) : Per.Acris0 l) ^ r ∣ ((k.factorial : ℕ) : Per.Acris0 l)`. Conclude with `Nat.cast_dvd_cast (α := Per.Acris0 l) h1` after adjusting the coercions. Conclude with `(h2.mul_left _).mul_right _`. Conclude with `this)`.

Use `⟨y, fun r => ⟨l ^ r, fun n hn => ⟨s n, ?_, hy r n hn⟩⟩⟩` and prove the remaining obligations. Simplify using `only [s]`. Use `push_cast`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k hk => ?_` and prove the remaining obligations.

Establish `h1 : n.factorial = n.factorial / (k + 1) * (k + 1)` using `(Nat.div_mul_cancel (Nat.dvd_factorial k.succ_pos (Finset.mem_range.1 hk))).symm`. Establish `h2 : ((n.factorial : ℕ) : Per.AinfP l) = ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * (k + 1)`. Conclude with `congrArg (Nat.cast : ℕ → Per.AinfP l) h1` after adjusting the coercions. Rewrite using `[← hg (k + 1), Nat.factorial_succ]`. Generalize the expression as in `((n.factorial / (k + 1) : ℕ) : Per.AinfP l) = q at h2 ⊢`.

Rewrite using `[h2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_isLogA {e : Per.Fl l} (he : e.untilt = 1) : ∃ y : Per.Acris l, IsLogA e y := by
  have hl : l.Prime := Fact.out
  have hμ : Per.θ l (mu e) = 0 := by rw [theta_mu, he, sub_self]
  have hγ : ∀ k : ℕ, ∃ g : Per.Acris0 l, ((k.factorial : ℕ) : Per.AinfP l) * (g : Per.AinfP l) =
      algebraMap (Per.Ainf l) (Per.AinfP l) (mu e) ^ k := by
    intro k
    obtain ⟨d, hd⟩ := (GlobalTheory.RingBasics.isUnit_nat l _ k.factorial_ne_zero).exists_right_inv
    have : ((k.factorial : ℕ) : Per.AinfP l) * (d * algebraMap (Per.Ainf l) (Per.AinfP l) (mu e) ^ k) =
      algebraMap (Per.Ainf l) (Per.AinfP l) (mu e) ^ k := by rw [← mul_assoc, hd, one_mul]
    exact ⟨⟨_, GlobalTheory.RingIface.mem_Acris0_of_factorial_mul l (mu e) hμ k _ this⟩, this⟩
  choose g hg using hγ
  let s : ℕ → Per.Acris0 l := fun n =>
    ∑ k ∈ Finset.range n, (-1) ^ k * ((k.factorial : ℕ) : Per.Acris0 l) * g (k + 1)
  obtain ⟨y, hy⟩ := acris_lim (l := l) s (by
    intro r n hn
    have : ((l : ℕ) : Per.Acris0 l) ^ r ∣ s n - s (l ^ r) := by
      simp only [s]
      rw [← Finset.sum_Ico_eq_sub _ hn]
      refine Finset.dvd_sum fun k hk => ?_
      have h1 : l ^ r ∣ k.factorial := Nat.dvd_factorial (pow_pos hl.pos r) (Finset.mem_Ico.1 hk).1
      have h2 : ((l : ℕ) : Per.Acris0 l) ^ r ∣ ((k.factorial : ℕ) : Per.Acris0 l) := by
        exact_mod_cast Nat.cast_dvd_cast (α := Per.Acris0 l) h1
      exact (h2.mul_left _).mul_right _
    exact this)
  refine ⟨y, fun r => ⟨l ^ r, fun n hn => ⟨s n, ?_, hy r n hn⟩⟩⟩
  simp only [s]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have h1 : n.factorial = n.factorial / (k + 1) * (k + 1) :=
    (Nat.div_mul_cancel (Nat.dvd_factorial k.succ_pos (Finset.mem_range.1 hk))).symm
  have h2 : ((n.factorial : ℕ) : Per.AinfP l) = ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * (k + 1) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → Per.AinfP l) h1
  rw [← hg (k + 1), Nat.factorial_succ]
  generalize ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) = q at h2 ⊢
  rw [h2]
  push_cast
  ring

/- English proof (translation)
Introduce `r`. Take `⟨N, hN⟩` from `hy r`. Use `⟨N, fun n hn => ?_⟩` and prove the remaining obligations. Take `⟨s, hs, z, hz⟩` from `hN n hn`. Use `⟨⟨Per.extP f s, hf.mem _ s.2⟩, ?_, F z, ?_⟩` and prove the remaining obligations.

Establish `hm : f (mu e) = mu e'` using `by rw [mu, mu, map_sub, map_one, h]`. Use `congrArg (Per.extP f) hs` as an intermediate fact. Simplify `this` using `only [map_mul, map_natCast, map_sum, map_pow, map_neg, map_one, GlobalTheory.RingBasics.awayMap_algebraMap₂, hm]`. Use `congrArg F hz` as an intermediate fact. Rewrite `this` using `[map_sub, map_mul, map_pow, map_natCast, hf.env]`.

Conclude with `this`.
-/
theorem isLogA_extends {f : Per.Ainf l →+* Per.Ainf l} {F : Per.Acris l →+* Per.Acris l}
    (hf : GlobalTheory.CrisMaps.Extends f F) {e e' : Per.Fl l}
    (h : f (Per.tm e) = Per.tm e') {y : Per.Acris l} (hy : IsLogA e y) : IsLogA e' (F y) := by
  intro r
  obtain ⟨N, hN⟩ := hy r
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨s, hs, z, hz⟩ := hN n hn
  refine ⟨⟨Per.extP f s, hf.mem _ s.2⟩, ?_, F z, ?_⟩
  · have hm : f (mu e) = mu e' := by rw [mu, mu, map_sub, map_one, h]
    have := congrArg (Per.extP f) hs
    simpa only [map_mul, map_natCast, map_sum, map_pow, map_neg, map_one, GlobalTheory.RingBasics.awayMap_algebraMap₂, hm] using this
  · have := congrArg F hz
    rw [map_sub, map_mul, map_pow, map_natCast, hf.env] at this
    exact this

/- English proof (translation)
The claim follows from `isLogA_extends (GlobalTheory.CrisMaps.phiA_extends l) (GlobalTheory.RingIface.phiA_teich l e) hy`.
-/
theorem isLogA_phiA {e : Per.Fl l} {y : Per.Acris l} (hy : IsLogA e y) : IsLogA (e ^ l) (phiA l y) :=
  isLogA_extends (GlobalTheory.CrisMaps.phiA_extends l) (GlobalTheory.RingIface.phiA_teich l e) hy

/- English proof (translation)
The claim follows from `isLogA_extends (GlobalTheory.CrisMaps.sigA_extends g) (GlobalTheory.RingIface.sigA_teich l g e) hy`.
-/
theorem isLogA_sigA (g : Per.Gq l) {e : Per.Fl l} {y : Per.Acris l} (hy : IsLogA e y) :
    IsLogA (Per.σF g e) (sigA g y) :=
  isLogA_extends (GlobalTheory.CrisMaps.sigA_extends g) (GlobalTheory.RingIface.sigA_teich l g e) hy

/- English proof (translation)
Take `⟨ζ, h0, hs, h1⟩` from `exists_zeta l`. Take `⟨ε, h⟩` from `exists_tilt ζ h0 hs`. Take `⟨t, ht⟩` from `exists_isLogA (isEps_of_root h0 h1 h).1`. Conclude with `⟨ζ, ε, t, h0, hs, h1, h, ht⟩`.
-/
theorem exists_part (l : ℕ) [Fact l.Prime] : ∃ (ζ : ℕ → Om l) (ε : Per.Fl l) (t : Per.Acris l),
    ζ 0 = 1 ∧ (∀ m, ζ (m + 1) ^ l = ζ m) ∧ ζ 1 ≠ 1 ∧
    (∀ m, (rootT ε m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (ζ m)) ∧ IsLogA ε t := by
  obtain ⟨ζ, h0, hs, h1⟩ := exists_zeta l
  obtain ⟨ε, h⟩ := exists_tilt ζ h0 hs
  obtain ⟨t, ht⟩ := exists_isLogA (isEps_of_root h0 h1 h).1
  exact ⟨ζ, ε, t, h0, hs, h1, h, ht⟩

end GlobalTheory.MemLoc.Model
