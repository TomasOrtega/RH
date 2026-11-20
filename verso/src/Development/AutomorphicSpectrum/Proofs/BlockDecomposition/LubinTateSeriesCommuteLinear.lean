import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer.LogGal

section Trunc

variable {R A : Type} [CommRing R] [CommRing A]

def tev (g : R →+* A) (y : A) (D : ℕ) (ψ : PowerSeries R) : A :=
  ∑ i ∈ Finset.range D, g (PowerSeries.coeff i ψ) * y ^ i

/- English proof (translation)
The claim follows from `(PowerSeries.eval₂_trunc_eq_sum_range y g D ψ).symm`.
-/
theorem tev_eq_eval₂ (g : R →+* A) (y : A) (D : ℕ) (ψ : PowerSeries R) :
    tev g y D ψ = (PowerSeries.trunc D ψ).eval₂ g y :=
  (PowerSeries.eval₂_trunc_eq_sum_range y g D ψ).symm

/- English proof (translation)
Rewrite using `[tev_eq_eval₂]`. Choose the witnesses or unpack the hypotheses as in `⟨r, hr⟩ : (Polynomial.X : Polynomial R) ^ D ∣ p - PowerSeries.trunc D (p : PowerSeries R) := by`. Rewrite using `[Polynomial.X_pow_dvd_iff]`. Introduce `d hd`. Simplify using `[PowerSeries.coeff_trunc, hd]`.

Establish `hp : p = PowerSeries.trunc D (p : PowerSeries R) + Polynomial.X ^ D * r`. Rewrite using `[← hr]`. Expand and normalize the polynomial expressions, which then agree. Use `conv_rhs => rw [hp]`. Simplify using `[Polynomial.eval₂_add, Polynomial.eval₂_mul, hy]`.
-/
theorem tev_coe {g : R →+* A} {y : A} {D : ℕ} (hy : y ^ D = 0) (p : Polynomial R) :
    tev g y D (p : PowerSeries R) = p.eval₂ g y := by
  rw [tev_eq_eval₂]
  obtain ⟨r, hr⟩ : (Polynomial.X : Polynomial R) ^ D ∣
      p - PowerSeries.trunc D (p : PowerSeries R) := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    simp [PowerSeries.coeff_trunc, hd]
  have hp : p = PowerSeries.trunc D (p : PowerSeries R) + Polynomial.X ^ D * r := by
    rw [← hr]; ring
  conv_rhs => rw [hp]
  simp [Polynomial.eval₂_add, Polynomial.eval₂_mul, hy]

/- English proof (translation)
Establish `h1 : tev g y D (a * b) = tev g y D ((PowerSeries.trunc D a * PowerSeries.trunc D b : Polynomial R) : PowerSeries R)`. Rewrite using `[tev_eq_eval₂, tev_eq_eval₂, ← PowerSeries.trunc_trunc_mul_trunc]`. Simplify using the standard rewrite rules. Rewrite using `[h1, tev_coe hy, Polynomial.eval₂_mul, tev_eq_eval₂, tev_eq_eval₂]`.
-/
theorem tev_mul {g : R →+* A} {y : A} {D : ℕ} (hy : y ^ D = 0) (a b : PowerSeries R) :
    tev g y D (a * b) = tev g y D a * tev g y D b := by
  have h1 : tev g y D (a * b) =
      tev g y D ((PowerSeries.trunc D a * PowerSeries.trunc D b : Polynomial R) : PowerSeries R) := by
    rw [tev_eq_eval₂, tev_eq_eval₂, ← PowerSeries.trunc_trunc_mul_trunc]
    simp
  rw [h1, tev_coe hy, Polynomial.eval₂_mul, tev_eq_eval₂, tev_eq_eval₂]

def tevHom (g : R →+* A) (y : A) (D : ℕ) (hy : y ^ D = 0) : PowerSeries R →+* A where
  toFun := tev g y D
  map_one' := by simpa using tev_coe (g := g) hy 1
  map_mul' := tev_mul hy
  map_zero' := by simp [tev]
  map_add' a b := by simp [tev, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tevHom_apply (g : R →+* A) (y : A) (D : ℕ) (hy : y ^ D = 0) (ψ : PowerSeries R) :
    tevHom g y D hy ψ = tev g y D ψ := rfl

/- English proof (translation)
Simplify `tev_coe (g := g) hy (Polynomial.C c)` using `[tevHom_apply]`.
-/
theorem tevHom_C (g : R →+* A) (y : A) (D : ℕ) (hy : y ^ D = 0) (c : R) :
    tevHom g y D hy (PowerSeries.C c) = g c := by
  simpa [tevHom_apply] using tev_coe (g := g) hy (Polynomial.C c)

/- English proof (translation)
Simplify `tev_coe (g := g) hy Polynomial.X` using `[tevHom_apply]`.
-/
theorem tevHom_X (g : R →+* A) (y : A) (D : ℕ) (hy : y ^ D = 0) :
    tevHom g y D hy PowerSeries.X = y := by
  simpa [tevHom_apply] using tev_coe (g := g) hy Polynomial.X

/- English proof (translation)
Take `⟨e, rfl⟩ : ∃ e, q = e + 1` from `⟨q - 1, by omega⟩`. Establish `: c * y + y ^ (e + 1) = y * (c + y ^ e)` using `by ring`. Rewrite using `[this, mul_pow, hy, zero_mul]`.
-/
theorem lt_pow_zero {y c : A} {q D : ℕ} (hq : 2 ≤ q) (hy : y ^ D = 0) : (c * y + y ^ q) ^ D = 0 := by
  obtain ⟨e, rfl⟩ : ∃ e, q = e + 1 := ⟨q - 1, by omega⟩
  have : c * y + y ^ (e + 1) = y * (c + y ^ e) := by ring
  rw [this, mul_pow, hy, zero_mul]

/- English proof (translation)
Use `set f : PowerSeries R := PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q with hf`. Establish `hf0 : PowerSeries.constantCoeff f = 0`. Establish `: q ≠ 0` using `by omega`. Simplify using `[hf, this]`. Establish `hfS : PowerSeries.HasSubst f` using `PowerSeries.HasSubst.of_constantCoeff_zero' hf0`.

Establish `hφS : PowerSeries.HasSubst φ` using `PowerSeries.HasSubst.of_constantCoeff_zero' h0`. Establish `hy' : (g π * y + y ^ q) ^ D = 0` using `lt_pow_zero hq hy`. Establish `h1 : tevHom g y D hy (PowerSeries.subst φ f) = g π * tevHom g y D hy φ + tevHom g y D hy φ ^ q`. Establish `: (PowerSeries.subst φ f : PowerSeries R) = PowerSeries.C π * φ + φ ^ q`. Rewrite using `[hf, PowerSeries.subst_add hφS, PowerSeries.subst_mul hφS, PowerSeries.subst_pow hφS, PowerSeries.subst_X hφS, PowerSeries.subst_C]`.

Both sides reduce to the same expression. Rewrite using `[this, map_add, map_mul, map_pow, tevHom_C]`. Set `Θ : PowerSeries R →+* A` to `(tevHom g y D hy).comp (PowerSeries.substAlgHom (R := R) (S := R) (τ := Unit) hfS).toRingHom`. Establish `hΘ : ∀ ψ, Θ ψ = tevHom g y D hy (PowerSeries.subst f ψ)`. Introduce `ψ`.

Simplify using `only [Θ, RingHom.comp_apply]`. Conclude with `congrArg _ (congrFun (PowerSeries.coe_substAlgHom hfS) ψ)`. Establish `hΘX : Θ PowerSeries.X = g π * y + y ^ q`. Rewrite using `[hΘ, PowerSeries.subst_X hfS, hf, map_add, map_mul, map_pow, tevHom_C, tevHom_X]`. Establish `hpoly : ∀ p : Polynomial R, Θ (p : PowerSeries R) = tevHom g (g π * y + y ^ q) D hy' (p : PowerSeries R)`.

Introduce `p`. Establish `: Θ.comp (Polynomial.coeToPowerSeries.ringHom) = (tevHom g (g π * y + y ^ q) D hy').comp (Polynomial.coeToPowerSeries.ringHom)`. Apply `Polynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using `only [RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C]`.

Rewrite using `[hΘ, PowerSeries.subst_C, tevHom_C]`. Conclude with `tevHom_C g y D hy a`. Simplify using `only [RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]`. Rewrite using `[hΘX, tevHom_X]`. Conclude with `congrArg (fun u => u p) (congrArg DFunLike.coe this)`.

Choose the witnesses or unpack the hypotheses as in `⟨ρ, hρ⟩ : (PowerSeries.X : PowerSeries R) ^ D ∣ φ - (PowerSeries.trunc D φ : PowerSeries R) := by`. Rewrite using `[PowerSeries.X_pow_dvd_iff]`. Introduce `d hd`. Simplify using `[PowerSeries.coeff_trunc, hd]`. Establish `hφ : φ = (PowerSeries.trunc D φ : PowerSeries R) + PowerSeries.X ^ D * ρ`.

Rewrite using `[← hρ]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : Θ φ = tevHom g (g π * y + y ^ q) D hy' φ`. Rewrite using `[hφ, map_add, map_add, hpoly, map_mul, map_mul, map_pow, map_pow, hΘX, tevHom_X, hy', zero_mul, zero_mul]`. Rewrite using `[← tevHom_apply g _ D hy', ← tevHom_apply g y D hy, ← h2, hΘ, ← hc, h1]`.
-/
theorem tev_comm (g : R →+* A) (π : R) {q : ℕ} (hq : 2 ≤ q) (φ : PowerSeries R)
    (h0 : PowerSeries.constantCoeff φ = 0)
    (hc : PowerSeries.subst φ (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q : PowerSeries R) =
      PowerSeries.subst (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q : PowerSeries R) φ)
    {y : A} {D : ℕ} (hy : y ^ D = 0) :
    tev g (g π * y + y ^ q) D φ = g π * tev g y D φ + tev g y D φ ^ q := by
  set f : PowerSeries R := PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q with hf
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    have : q ≠ 0 := by omega
    simp [hf, this]
  have hfS : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  have hφS : PowerSeries.HasSubst φ := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hy' : (g π * y + y ^ q) ^ D = 0 := lt_pow_zero hq hy
  have h1 : tevHom g y D hy (PowerSeries.subst φ f) =
      g π * tevHom g y D hy φ + tevHom g y D hy φ ^ q := by
    have : (PowerSeries.subst φ f : PowerSeries R) = PowerSeries.C π * φ + φ ^ q := by
      rw [hf, PowerSeries.subst_add hφS, PowerSeries.subst_mul hφS, PowerSeries.subst_pow hφS,
        PowerSeries.subst_X hφS, PowerSeries.subst_C]
      rfl
    rw [this, map_add, map_mul, map_pow, tevHom_C]
  let Θ : PowerSeries R →+* A :=
    (tevHom g y D hy).comp
      (PowerSeries.substAlgHom (R := R) (S := R) (τ := Unit) hfS).toRingHom
  have hΘ : ∀ ψ, Θ ψ = tevHom g y D hy (PowerSeries.subst f ψ) := by
    intro ψ
    simp only [Θ, RingHom.comp_apply]
    exact congrArg _ (congrFun (PowerSeries.coe_substAlgHom hfS) ψ)
  have hΘX : Θ PowerSeries.X = g π * y + y ^ q := by
    rw [hΘ, PowerSeries.subst_X hfS, hf, map_add, map_mul, map_pow, tevHom_C, tevHom_X]
  have hpoly : ∀ p : Polynomial R, Θ (p : PowerSeries R) =
      tevHom g (g π * y + y ^ q) D hy' (p : PowerSeries R) := by
    intro p
    have : Θ.comp (Polynomial.coeToPowerSeries.ringHom) =
        (tevHom g (g π * y + y ^ q) D hy').comp (Polynomial.coeToPowerSeries.ringHom) := by
      apply Polynomial.ringHom_ext
      · intro a
        simp only [RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C]
        rw [hΘ, PowerSeries.subst_C, tevHom_C]
        exact tevHom_C g y D hy a
      · simp only [RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
        rw [hΘX, tevHom_X]
    exact congrArg (fun u => u p) (congrArg DFunLike.coe this)
  obtain ⟨ρ, hρ⟩ : (PowerSeries.X : PowerSeries R) ^ D ∣
      φ - (PowerSeries.trunc D φ : PowerSeries R) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro d hd
    simp [PowerSeries.coeff_trunc, hd]
  have hφ : φ = (PowerSeries.trunc D φ : PowerSeries R) + PowerSeries.X ^ D * ρ := by
    rw [← hρ]; ring
  have h2 : Θ φ = tevHom g (g π * y + y ^ q) D hy' φ := by
    rw [hφ, map_add, map_add, hpoly, map_mul, map_mul, map_pow, map_pow, hΘX, tevHom_X, hy', zero_mul,
      zero_mul]
  rw [← tevHom_apply g _ D hy', ← tevHom_apply g y D hy, ← h2, hΘ, ← hc, h1]

end Trunc

section Abs

variable {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B}

/- English proof (translation)
Take `⟨s, hs, hx⟩` from `hx`. Take `⟨s', hs', hy⟩` from `hy`. Use `⟨s + s', S.add_mem hs hs', ?_⟩` and prove the remaining obligations. Establish `e : x + y - ϖ ^ m * (s + s') = (x - ϖ ^ m * s) + (y - ϖ ^ m * s')` using `by ring`. Rewrite using `[e]`.

Conclude with `J.add_mem hx hy`.
-/
theorem near_add {J : Ideal B} {m : ℕ} {x y : B} (hx : Near S ϖ J m x) (hy : Near S ϖ J m y) :
    Near S ϖ J m (x + y) := by
  obtain ⟨s, hs, hx⟩ := hx
  obtain ⟨s', hs', hy⟩ := hy
  refine ⟨s + s', S.add_mem hs hs', ?_⟩
  have e : x + y - ϖ ^ m * (s + s') = (x - ϖ ^ m * s) + (y - ϖ ^ m * s') := by ring
  rw [e]
  exact J.add_mem hx hy

/- English proof (translation)
Take `⟨s, hs, hx⟩` from `hx`. Take `⟨s', hs', hy⟩` from `hy`. Use `⟨s - s', S.sub_mem hs hs', ?_⟩` and prove the remaining obligations. Establish `e : x - y - ϖ ^ m * (s - s') = (x - ϖ ^ m * s) - (y - ϖ ^ m * s')` using `by ring`. Rewrite using `[e]`.

Conclude with `J.sub_mem hx hy`.
-/
theorem near_sub {J : Ideal B} {m : ℕ} {x y : B} (hx : Near S ϖ J m x) (hy : Near S ϖ J m y) :
    Near S ϖ J m (x - y) := by
  obtain ⟨s, hs, hx⟩ := hx
  obtain ⟨s', hs', hy⟩ := hy
  refine ⟨s - s', S.sub_mem hs hs', ?_⟩
  have e : x - y - ϖ ^ m * (s - s') = (x - ϖ ^ m * s) - (y - ϖ ^ m * s') := by ring
  rw [e]
  exact J.sub_mem hx hy

/- English proof (translation)
Take `⟨s, hs, hx⟩` from `hx`. Use `⟨a * s, S.mul_mem ha hs, ?_⟩` and prove the remaining obligations. Establish `e : a * x - ϖ ^ m * (a * s) = a * (x - ϖ ^ m * s)` using `by ring`. Rewrite using `[e]`. Conclude with `J.mul_mem_left a hx`.
-/
theorem near_mul {J : Ideal B} {m : ℕ} {x a : B} (ha : a ∈ S) (hx : Near S ϖ J m x) :
    Near S ϖ J m (a * x) := by
  obtain ⟨s, hs, hx⟩ := hx
  refine ⟨a * s, S.mul_mem ha hs, ?_⟩
  have e : a * x - ϖ ^ m * (a * s) = a * (x - ϖ ^ m * s) := by ring
  rw [e]
  exact J.mul_mem_left a hx

/- English proof (translation)
Take `⟨s, hs, hx⟩` from `hx`. Use `⟨σ s, hS s hs, ?_⟩` and prove the remaining obligations. Use `hJ _ hx` as an intermediate fact. Rewrite `this` using `[map_sub, map_mul, map_pow, hϖ]`. Then use the resulting hypothesis.
-/
theorem near_map (σ : B →+* B) (hS : ∀ s ∈ S, σ s ∈ S) {J : Ideal B} (hJ : ∀ x ∈ J, σ x ∈ J)
    (hϖ : σ ϖ = ϖ) {m : ℕ} {x : B} (hx : Near S ϖ J m x) : Near S ϖ J m (σ x) := by
  obtain ⟨s, hs, hx⟩ := hx
  refine ⟨σ s, hS s hs, ?_⟩
  have := hJ _ hx
  rwa [map_sub, map_mul, map_pow, hϖ] at this

def nearI (S : Subring B) (F : ℕ → Ideal B) (hϖ : ϖ ∈ S) (k m : ℕ) : Ideal S :=
  Ideal.span {(⟨ϖ, hϖ⟩ : S) ^ m} ⊔ (F k).comap S.subtype

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 hx`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 ha`. Use `⟨c, c.2, ?_⟩` and prove the remaining obligations.

Establish `hb' : ((b : S) : B) ∈ F k` using `hb`. Establish `e : ((c * (⟨ϖ, hϖ⟩ : S) ^ m + b : S) : B) - ϖ ^ m * (c : B) = (b : B)`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `hb'`. Introduce and unpack `⟨s, hs, hx⟩`. Use `Submodule.mem_sup.2 ⟨(⟨s, hs⟩ : S) * (⟨ϖ, hϖ⟩ : S) ^ m, Ideal.mem_span_singleton'.2 ⟨_, rfl⟩, x - (⟨s, hs⟩ : S) * (⟨ϖ, hϖ⟩ : S) ^ m, ?_, by ring⟩` and prove the remaining obligations. Establish `e : ((x - (⟨s, hs⟩ : S) * (⟨ϖ, hϖ⟩ : S) ^ m : S) : B) = (x : B) - ϖ ^ m * s`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Use `show ((x - (⟨s, hs⟩ : S) * (⟨ϖ, hϖ⟩ : S) ^ m : S) : B) ∈ F k`. Rewrite using `[e]`. Conclude with `hx`.
-/
theorem mem_nearI (hϖ : ϖ ∈ S) {k m : ℕ} {x : S} :
    x ∈ nearI S F hϖ k m ↔ Near S ϖ (F k) m (x : B) := by
  constructor
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    refine ⟨c, c.2, ?_⟩
    have hb' : ((b : S) : B) ∈ F k := hb
    have e : ((c * (⟨ϖ, hϖ⟩ : S) ^ m + b : S) : B) - ϖ ^ m * (c : B) = (b : B) := by
      push_cast
      ring
    rw [e]
    exact hb'
  · rintro ⟨s, hs, hx⟩
    refine Submodule.mem_sup.2 ⟨(⟨s, hs⟩ : S) * (⟨ϖ, hϖ⟩ : S) ^ m,
      Ideal.mem_span_singleton'.2 ⟨_, rfl⟩, x - (⟨s, hs⟩ : S) * (⟨ϖ, hϖ⟩ : S) ^ m, ?_, by ring⟩
    have e : ((x - (⟨s, hs⟩ : S) * (⟨ϖ, hϖ⟩ : S) ^ m : S) : B) = (x : B) - ϖ ^ m * s := by
      push_cast
      ring
    show ((x - (⟨s, hs⟩ : S) * (⟨ϖ, hϖ⟩ : S) ^ m : S) : B) ∈ F k
    rw [e]
    exact hx

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rw [E.top]`. Conclude with `Submodule.mem_top`. Consider the case `succ k ih`. Rewrite using `[pow_succ]`.

Conclude with `E.mul_le k 1 (Ideal.mul_mem_mul ih hx)`.
-/
theorem pow_mem_F (E : PerEnv S F ϖ) {x : B} (hx : x ∈ F 1) (k : ℕ) : x ^ k ∈ F k := by
  induction k with
  | zero => rw [E.top]; exact Submodule.mem_top
  | succ k ih =>
    rw [pow_succ]
    exact E.mul_le k 1 (Ideal.mul_mem_mul ih hx)

/- English proof (translation)
Take `⟨s, hs, hx⟩` from `hN`. Use `set I := nearI S F E.mem k m with hI`. Set `sS : S` to `⟨s, hs⟩`. Set `wS : S` to `⟨ϖ, E.mem⟩`. Set `xS : S` to `Q ^ M - wS ^ 1 * sS`.

Establish `hxS : (xS : B) ∈ F 1`. Establish `e : (xS : B) = (Q : B) ^ M - ϖ ^ 1 * s`. Simplify using `[xS, sS, wS]`. Rewrite using `[e]`. Conclude with `hx`.

Establish `hw : IsNilpotent (Ideal.Quotient.mk I wS)`. Use `⟨m, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_pow, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)`. Establish `hxn : IsNilpotent (Ideal.Quotient.mk I xS)`.

Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_pow, Ideal.Quotient.eq_zero_iff_mem]`. Use `Ideal.mem_sup_right ?_` and prove the remaining obligations. Use `show ((xS ^ k : S) : B) ∈ F k`. Use `push_cast`.

Conclude with `pow_mem_F E hxS k`. Establish `hQ : Ideal.Quotient.mk I Q ^ M = Ideal.Quotient.mk I wS * Ideal.Quotient.mk I sS + Ideal.Quotient.mk I xS`. Rewrite using `[← map_pow, ← map_mul, ← map_add]`. Use `congr 1`. Simplify using `[xS]`.

Establish `: IsNilpotent (Ideal.Quotient.mk I Q ^ M)`. Rewrite using `[hQ]`. Conclude with `(Commute.all _ _).isNilpotent_add ((Commute.all _ _).isNilpotent_mul_right hw) hxn`. Conclude with `IsNilpotent.of_pow this`.
-/
theorem nilp_of_near (E : PerEnv S F ϖ) (Q : S) {M : ℕ} (hN : Near S ϖ (F 1) 1 ((Q : B) ^ M))
    (k m : ℕ) : IsNilpotent (Ideal.Quotient.mk (nearI S F E.mem k m) Q) := by
  obtain ⟨s, hs, hx⟩ := hN
  set I := nearI S F E.mem k m with hI
  let sS : S := ⟨s, hs⟩
  let wS : S := ⟨ϖ, E.mem⟩
  let xS : S := Q ^ M - wS ^ 1 * sS
  have hxS : (xS : B) ∈ F 1 := by
    have e : (xS : B) = (Q : B) ^ M - ϖ ^ 1 * s := by
      simp [xS, sS, wS]
    rw [e]
    exact hx
  have hw : IsNilpotent (Ideal.Quotient.mk I wS) := by
    refine ⟨m, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  have hxn : IsNilpotent (Ideal.Quotient.mk I xS) := by
    refine ⟨k, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    refine Ideal.mem_sup_right ?_
    show ((xS ^ k : S) : B) ∈ F k
    push_cast
    exact pow_mem_F E hxS k
  have hQ : Ideal.Quotient.mk I Q ^ M =
      Ideal.Quotient.mk I wS * Ideal.Quotient.mk I sS + Ideal.Quotient.mk I xS := by
    rw [← map_pow, ← map_mul, ← map_add]
    congr 1
    simp [xS]
  have : IsNilpotent (Ideal.Quotient.mk I Q ^ M) := by
    rw [hQ]
    exact (Commute.all _ _).isNilpotent_add ((Commute.all _ _).isNilpotent_mul_right hw) hxn
  exact IsNilpotent.of_pow this

/- English proof (translation)
The claim follows from `Function.iterate_succ_apply' _ _ _`.
-/
theorem ltIter_succ (q n : ℕ) (x : B) :
    ltIter ϖ q (n + 1) x = ϖ * ltIter ϖ q n x + ltIter ϖ q n x ^ q :=
  Function.iterate_succ_apply' _ _ _

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact hx`. Consider the case `succ n ih`. Rewrite using `[ltIter_succ]`. Conclude with `S.add_mem (S.mul_mem hϖ ih) (S.pow_mem ih q)`.
-/
theorem ltIter_mem (hϖ : ϖ ∈ S) (q n : ℕ) {x : B} (hx : x ∈ S) : ltIter ϖ q n x ∈ S := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    rw [ltIter_succ]
    exact S.add_mem (S.mul_mem hϖ ih) (S.pow_mem ih q)

variable {R : Type} [CommRing R]

def gq (E : PerEnv S F ϖ) (h : R →+* B) (hh : ∀ c, h c ∈ S) (k m : ℕ) :
    R →+* S ⧸ nearI S F E.mem k m :=
  (Ideal.Quotient.mk _).comp (h.codRestrict S hh)

/- English proof (translation)
Use `⟨∑ i ∈ Finset.range D, (h.codRestrict S hh) (PowerSeries.coeff i φ) * y ^ i, ?_, ?_⟩` and prove the remaining obligations. Use `push_cast`. Both sides reduce to the same expression. Simplify using `[tev, gq, map_sum]`.
-/
theorem tev_gq (E : PerEnv S F ϖ) (h : R →+* B) (hh : ∀ c, h c ∈ S) (k m D : ℕ)
    (φ : PowerSeries R) (y : S) :
    ∃ p : S, (p : B) = ∑ i ∈ Finset.range D, h (PowerSeries.coeff i φ) * (y : B) ^ i ∧
      tev (gq E h hh k m) (Ideal.Quotient.mk _ y) D φ = Ideal.Quotient.mk _ p := by
  refine ⟨∑ i ∈ Finset.range D, (h.codRestrict S hh) (PowerSeries.coeff i φ) * y ^ i, ?_, ?_⟩
  · push_cast
    rfl
  · simp [tev, gq, map_sum]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Use `⟨Q, ⟨σ Q, hσS _ Q.2⟩, rfl, rfl, ?_⟩` and prove the remaining obligations. Take `⟨D₀, hD₀⟩` from `hnil k m`. Take `⟨D₁, hD₁⟩` from `hev m k`.

Use `⟨max D₀ D₁, ?_, ?_⟩` and prove the remaining obligations. Conclude with `pow_eq_zero_of_le (le_max_left _ _) hD₀`. Take `⟨p, hp, hpe⟩` from `tev_gq E h hh k m (max D₀ D₁) φ Q`. Rewrite using `[hpe, Ideal.Quotient.eq, mem_nearI]`. Use `hD₁ (max D₀ D₁) (le_max_right _ _)` as an intermediate fact.

Rewrite `this` using `[← hp]`. Simplify using `using this`. Consider the case `succ n ih`. Take `⟨y, r, hy, hr, D, hD, hv⟩` from `ih`. Set `wS : S` to `⟨ϖ, E.mem⟩`.

Establish `hg : gq E h hh k m π = Ideal.Quotient.mk _ wS`. Simplify using `only [gq, RingHom.comp_apply]`. Use `congr 1`. Conclude with `Subtype.ext hπ`. Use `⟨wS * y + y ^ q, wS * r + r ^ q, ?_, ?_, D, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[ltIter_succ, ← hy]`. Simplify using `[wS]`. Rewrite using `[ltIter_succ, map_add, map_mul, map_pow, hσϖ, ← hr]`. Simplify using `[wS]`. Rewrite using `[map_add, map_mul, map_pow]`.

Conclude with `lt_pow_zero hq hD`. Use `tev_comm (gq E h hh k m) π hq φ h0 hc hD` as an intermediate fact. Rewrite `this` using `[hv, hg]`. Rewrite using `[map_add, map_mul, map_pow, this]`. Simplify using the standard rewrite rules.
-/
theorem iter_val (E : PerEnv S F ϖ) (h : R →+* B) (hh : ∀ c, h c ∈ S) (π : R) (hπ : h π = ϖ)
    {q : ℕ} (hq : 2 ≤ q) (φ : PowerSeries R) (h0 : PowerSeries.constantCoeff φ = 0)
    (hc : PowerSeries.subst φ (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q : PowerSeries R) =
      PowerSeries.subst (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q : PowerSeries R) φ)
    (σ : B →+* B) (hσS : ∀ s ∈ S, σ s ∈ S) (hσϖ : σ ϖ = ϖ) (Q : S)
    (hnil : ∀ k m, IsNilpotent (Ideal.Quotient.mk (nearI S F E.mem k m) Q))
    (hev : ∀ m, EvalMod S F ϖ h φ Q (σ Q) m) (n k m : ℕ) :
    ∃ y r : S, (y : B) = ltIter ϖ q n Q ∧ (r : B) = σ (ltIter ϖ q n Q) ∧
      ∃ D, Ideal.Quotient.mk (nearI S F E.mem k m) y ^ D = 0 ∧
        tev (gq E h hh k m) (Ideal.Quotient.mk _ y) D φ = Ideal.Quotient.mk _ r := by
  induction n with
  | zero =>
    refine ⟨Q, ⟨σ Q, hσS _ Q.2⟩, rfl, rfl, ?_⟩
    obtain ⟨D₀, hD₀⟩ := hnil k m
    obtain ⟨D₁, hD₁⟩ := hev m k
    refine ⟨max D₀ D₁, ?_, ?_⟩
    · exact pow_eq_zero_of_le (le_max_left _ _) hD₀
    · obtain ⟨p, hp, hpe⟩ := tev_gq E h hh k m (max D₀ D₁) φ Q
      rw [hpe, Ideal.Quotient.eq, mem_nearI]
      have := hD₁ (max D₀ D₁) (le_max_right _ _)
      rw [← hp] at this
      simpa using this
  | succ n ih =>
    obtain ⟨y, r, hy, hr, D, hD, hv⟩ := ih
    let wS : S := ⟨ϖ, E.mem⟩
    have hg : gq E h hh k m π = Ideal.Quotient.mk _ wS := by
      simp only [gq, RingHom.comp_apply]
      congr 1
      exact Subtype.ext hπ
    refine ⟨wS * y + y ^ q, wS * r + r ^ q, ?_, ?_, D, ?_, ?_⟩
    · rw [ltIter_succ, ← hy]
      simp [wS]
    · rw [ltIter_succ, map_add, map_mul, map_pow, hσϖ, ← hr]
      simp [wS]
    · rw [map_add, map_mul, map_pow]
      exact lt_pow_zero hq hD
    · have := tev_comm (gq E h hh k m) π hq φ h0 hc hD
      rw [hv, hg] at this
      rw [map_add, map_mul, map_pow, this]
      simp

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨ρ, hρ⟩ : (PowerSeries.X : PowerSeries R) ^ 2 ∣ φ - PowerSeries.C (PowerSeries.coeff 1 φ) * PowerSeries.X := by`. Rewrite using `[PowerSeries.X_pow_dvd_iff]`. Introduce `d hd`. Use `interval_cases d`. Simplify using `[h0]`.

Simplify using the standard rewrite rules. Establish `hφ : φ = PowerSeries.C (PowerSeries.coeff 1 φ) * PowerSeries.X + PowerSeries.X ^ 2 * ρ`. Rewrite using `[← hρ]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨tevHom g y D hy ρ, ?_⟩` and prove the remaining obligations.

Rewrite using `[← tevHom_apply g y D hy]`. Use `conv_lhs => rw [hφ]`. Rewrite using `[map_add, map_mul, map_mul, map_pow, tevHom_C, tevHom_X]`.
-/
theorem tev_second {A : Type} [CommRing A] (g : R →+* A) {y : A} {D : ℕ} (hy : y ^ D = 0)
    (φ : PowerSeries R) (h0 : PowerSeries.constantCoeff φ = 0) :
    ∃ W, tev g y D φ = g (PowerSeries.coeff 1 φ) * y + y ^ 2 * W := by
  obtain ⟨ρ, hρ⟩ : (PowerSeries.X : PowerSeries R) ^ 2 ∣
      φ - PowerSeries.C (PowerSeries.coeff 1 φ) * PowerSeries.X := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro d hd
    interval_cases d
    · simp [h0]
    · simp
  have hφ : φ = PowerSeries.C (PowerSeries.coeff 1 φ) * PowerSeries.X + PowerSeries.X ^ 2 * ρ := by
    rw [← hρ]; ring
  refine ⟨tevHom g y D hy ρ, ?_⟩
  rw [← tevHom_apply g y D hy]
  conv_lhs => rw [hφ]
  rw [map_add, map_mul, map_mul, map_pow, tevHom_C, tevHom_X]

/- English proof (translation)
Use `set n := e + (c + N₀) with hn`. Take `⟨s₁, hs₁, h₁⟩` from `h0 n (by omega)`. Take `⟨s₂, hs₂, h₂⟩` from `h0 N₀ le_rfl`. Use `⟨ϖ ^ c * y N₀ + ϖ ^ N₀ * (s₁ - s₂), S.add_mem (S.mul_mem (S.pow_mem E.mem c) (hy _)) (S.mul_mem (S.pow_mem E.mem _) (S.sub_mem hs₁ hs₂)), ?_⟩` and prove the remaining obligations. Establish `hP : ϖ ^ n * ϖ' ^ n = 1` using `by rw [← mul_pow, hϖ', one_pow]`.

Establish `hP₀ : ϖ ^ N₀ * ϖ' ^ N₀ = 1` using `by rw [← mul_pow, hϖ', one_pow]`. Establish `e1 : y n - ϖ ^ e * (ϖ ^ c * y N₀ + ϖ ^ N₀ * (s₁ - s₂)) = ϖ ^ (e + N₀) * ((ϖ ^ c * (ϖ' ^ n * y n - t) - ϖ ^ 0 * s₁) - (ϖ ^ c * (ϖ' ^ N₀ * y N₀ - t) - ϖ ^ 0 * s₂))`. Establish `hn' : ϖ ^ n = ϖ ^ e * ϖ ^ c * ϖ ^ N₀` using `by rw [hn]; ring`. Rewrite `hP` using `[hn']`. Take the linear combination `(-(y n)) * hP + (ϖ ^ e * ϖ ^ c * y N₀) * hP₀`.

Rewrite using `[e1]`. Conclude with `(F k).mul_mem_left _ ((F k).sub_mem h₁ h₂)`.
-/
theorem est (E : PerEnv S F ϖ) {ϖ' : B} (hϖ' : ϖ * ϖ' = 1) {y : ℕ → B} (hy : ∀ n, y n ∈ S) {t : B}
    {c N₀ k : ℕ} (h0 : ∀ n ≥ N₀, Near S ϖ (F k) 0 (ϖ ^ c * (ϖ' ^ n * y n - t))) (e : ℕ) :
    ∃ u ∈ S, y (e + (c + N₀)) - ϖ ^ e * u ∈ F k := by
  set n := e + (c + N₀) with hn
  obtain ⟨s₁, hs₁, h₁⟩ := h0 n (by omega)
  obtain ⟨s₂, hs₂, h₂⟩ := h0 N₀ le_rfl
  refine ⟨ϖ ^ c * y N₀ + ϖ ^ N₀ * (s₁ - s₂),
    S.add_mem (S.mul_mem (S.pow_mem E.mem c) (hy _))
      (S.mul_mem (S.pow_mem E.mem _) (S.sub_mem hs₁ hs₂)), ?_⟩
  have hP : ϖ ^ n * ϖ' ^ n = 1 := by rw [← mul_pow, hϖ', one_pow]
  have hP₀ : ϖ ^ N₀ * ϖ' ^ N₀ = 1 := by rw [← mul_pow, hϖ', one_pow]
  have e1 : y n - ϖ ^ e * (ϖ ^ c * y N₀ + ϖ ^ N₀ * (s₁ - s₂)) =
      ϖ ^ (e + N₀) * ((ϖ ^ c * (ϖ' ^ n * y n - t) - ϖ ^ 0 * s₁) -
        (ϖ ^ c * (ϖ' ^ N₀ * y N₀ - t) - ϖ ^ 0 * s₂)) := by
    have hn' : ϖ ^ n = ϖ ^ e * ϖ ^ c * ϖ ^ N₀ := by rw [hn]; ring
    rw [hn'] at hP
    linear_combination (-(y n)) * hP + (ϖ ^ e * ϖ ^ c * y N₀) * hP₀
  rw [e1]
  exact (F k).mul_mem_left _ ((F k).sub_mem h₁ h₂)

/- English proof (translation)
Use `⟨ϖ ^ c * s + ϖ ^ d * u ^ 2 * w, S.add_mem (S.mul_mem (S.pow_mem hϖ c) hs) (S.mul_mem (S.mul_mem (S.pow_mem hϖ d) (S.pow_mem hu 2)) hw), ?_⟩` and prove the remaining obligations. Establish `hcomb : ϖ ^ c * ϖ ^ (2 * e) = ϖ ^ n * ϖ ^ m * ϖ ^ d`. Rewrite using `[← pow_add, ← pow_add, ← pow_add, he]`. Establish `e1 : ϖ ^ c * P * x - ϖ ^ m * (ϖ ^ c * s + ϖ ^ d * u ^ 2 * w) = ϖ ^ c * P * (x - y ^ 2 * w - ϖ ^ (m + n) * s) + ϖ ^ c * P * (y + ϖ ^ e * u) * w * (y - ϖ ^ e * u)`. Take the linear combination `(ϖ ^ (c + m) * s + ϖ ^ (m + d) * u ^ 2 * w) * hP + (P * w * u ^ 2) * hcomb`.

Rewrite using `[e1]`. Conclude with `J.add_mem (J.mul_mem_left _ hx) (J.mul_mem_left _ hy)`.
-/
theorem small {J : Ideal B} {P x y w s u : B} {c m n e d : ℕ} (hϖ : ϖ ∈ S)
    (hP : ϖ ^ n * P = 1) (hs : s ∈ S) (hu : u ∈ S) (hw : w ∈ S)
    (he : c + 2 * e = n + m + d)
    (hx : x - y ^ 2 * w - ϖ ^ (m + n) * s ∈ J) (hy : y - ϖ ^ e * u ∈ J) :
    Near S ϖ J m (ϖ ^ c * P * x) := by
  refine ⟨ϖ ^ c * s + ϖ ^ d * u ^ 2 * w, S.add_mem (S.mul_mem (S.pow_mem hϖ c) hs)
    (S.mul_mem (S.mul_mem (S.pow_mem hϖ d) (S.pow_mem hu 2)) hw), ?_⟩
  have hcomb : ϖ ^ c * ϖ ^ (2 * e) = ϖ ^ n * ϖ ^ m * ϖ ^ d := by
    rw [← pow_add, ← pow_add, ← pow_add, he]
  have e1 : ϖ ^ c * P * x - ϖ ^ m * (ϖ ^ c * s + ϖ ^ d * u ^ 2 * w) =
      ϖ ^ c * P * (x - y ^ 2 * w - ϖ ^ (m + n) * s) +
        ϖ ^ c * P * (y + ϖ ^ e * u) * w * (y - ϖ ^ e * u) := by
    linear_combination (ϖ ^ (c + m) * s + ϖ ^ (m + d) * u ^ 2 * w) * hP + (P * w * u ^ 2) * hcomb
  rw [e1]
  exact J.add_mem (J.mul_mem_left _ hx) (J.mul_mem_left _ hy)

end Abs

end GlobalTheory.CompanionTheory.LTPer.LogGal

namespace GlobalTheory.CompanionTheory.LTPer

open LogGal in

/- English proof (translation)
Introduce `B _ S F ϖ R _ E ϖ' hϖ' h hh π hπ q hq _ φ h0 hc σ hσS hσF hσϖ Q hQ hM hev t hT`. Take `⟨M, -, hN⟩` from `hM`. Use `set a := h (PowerSeries.coeff 1 φ) with ha_def`. Establish `ha : a ∈ S` using `hh _`. Establish `hσϖ' : σ ϖ' = ϖ'`.

Establish `e2 : ϖ * σ ϖ' = 1`. Use `congrArg σ hϖ'` as an intermediate fact. Rewrite `this` using `[map_mul, hσϖ, map_one]`. Then use the resulting hypothesis. Take the linear combination `(-(σ ϖ')) * hϖ' + ϖ' * e2`. Establish `hnil` using `nilp_of_near E ⟨Q, hQ⟩ hN`.

Establish `hy : ∀ n, ltIter ϖ q n Q ∈ S` using `fun n => ltIter_mem E.mem q n hQ`. Establish `key : ∀ k, σ t - a * t ∈ F k`. Introduce `k`. Take `⟨c, hT'⟩` from `hT k`. Take `⟨N₀, hN₀⟩` from `hT' 0`.

Establish `hnear : ∀ m, Near S ϖ (F k) m (ϖ ^ c * (σ t - a * t))`. Introduce `m`. Take `⟨N, hNm⟩` from `hT' m`. Take `⟨e, he⟩ : ∃ e, e = N + N₀ + m + 2 * (c + N₀)` from `⟨_, rfl⟩`. Take `⟨n, hn⟩ : ∃ n, n = e + (c + N₀)` from `⟨_, rfl⟩`.

Take `⟨d, hd⟩ : ∃ d, c + 2 * e = n + m + d` from `⟨c + 2 * e - (n + m), by omega⟩`. Establish `hE1` using `hNm n (by omega)`. Establish `hE2` using `near_map σ hσS (hσF k) hσϖ hE1`. Establish `hE3` using `near_mul ha hE1`. Take `⟨u, hu, hu'⟩` from `est E hϖ' hy hN₀ e`.

Rewrite `hu'` using `[← hn]`. Take `⟨yS, r, hyS, hr, D, hD, hv⟩` from `iter_val E h hh π hπ hq φ h0 hc σ hσS hσϖ ⟨Q, hQ⟩ hnil hev n k (m + n)`. Take `⟨W, hW⟩` from `tev_second (gq E h hh k (m + n)) hD φ h0`. Take `⟨w, rfl⟩` from `Ideal.Quotient.mk_surjective W`. Rewrite `hW` using `[hv]`.

Establish `hmem : r - ((⟨a, ha⟩ : S) * yS + yS ^ 2 * w) ∈ nearI S F E.mem k (m + n)`. Rewrite using `[← Ideal.Quotient.eq, hW, map_add, map_mul, map_mul, map_pow]`. Both sides reduce to the same expression. Rewrite `hmem` using `[mem_nearI]`. Take `⟨s, hs, hx⟩` from `hmem`.

Establish `hP : ϖ ^ n * ϖ' ^ n = 1` using `by rw [← mul_pow, hϖ', one_pow]`. Establish `hx' : (σ (ltIter ϖ q n Q) - a * ltIter ϖ q n Q) - ltIter ϖ q n Q ^ 2 * (w : B) - ϖ ^ (m + n) * s ∈ F k`. Establish `e1 : (σ (ltIter ϖ q n Q) - a * ltIter ϖ q n Q) - ltIter ϖ q n Q ^ 2 * (w : B) - ϖ ^ (m + n) * s = ((r - ((⟨a, ha⟩ : S) * yS + yS ^ 2 * w) : S) : B) - ϖ ^ (m + n) * s`. Use `push_cast`. Rewrite using `[hr, hyS]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`. Conclude with `hx`. Establish `hE4` using `small E.mem hP hs hu w.2 hd hx' hu'`. Establish `e2 : ϖ ^ c * (σ t - a * t) = a * (ϖ ^ c * (ϖ' ^ n * ltIter ϖ q n Q - t)) - σ (ϖ ^ c * (ϖ' ^ n * ltIter ϖ q n Q - t)) + ϖ ^ c * ϖ' ^ n * (σ (ltIter ϖ q n Q) - a * ltIter ϖ q n Q)`.

Simplify using `only [map_mul, map_pow, map_sub, hσϖ, hσϖ']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`. Conclude with `near_add (near_sub hE3 hE2) hE4`. Take `⟨x, hx, hxF⟩` from `hnear 0`.

Establish `hxk : x ∈ F k`. Use `E.closed k x hx fun m => ?_` and prove the remaining obligations. Take `⟨s, hs, hsF⟩` from `hnear m`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Establish `e3 : x - ϖ ^ m * s = (ϖ ^ c * (σ t - a * t) - ϖ ^ m * s) - (ϖ ^ c * (σ t - a * t) - ϖ ^ 0 * x)` using `by ring`.

Rewrite using `[e3]`. Conclude with `(F k).sub_mem hsF hxF`. Establish `hd : ϖ ^ c * (σ t - a * t) ∈ F k`. Establish `e4 : ϖ ^ c * (σ t - a * t) = (ϖ ^ c * (σ t - a * t) - ϖ ^ 0 * x) + x` using `by ring`. Rewrite using `[e4]`.

Conclude with `(F k).add_mem hxF hxk`. Establish `hP : ϖ ^ c * ϖ' ^ c = 1` using `by rw [← mul_pow, hϖ', one_pow]`. Establish `e5 : σ t - a * t = ϖ' ^ c * (ϖ ^ c * (σ t - a * t))`. Take the linear combination `(-(σ t - a * t)) * hP`. Rewrite using `[e5]`.

Conclude with `(F k).mul_mem_left _ hd`. Conclude with `sub_eq_zero.1 (E.sep _ key)`.
-/
theorem galois_log : ∀ {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B} {R : Type} [CommRing R], PerEnv S F ϖ → ∀ (ϖ' : B), ϖ * ϖ' = 1 →
    ∀ (h : R →+* B), (∀ c, h c ∈ S) → ∀ (π : R), h π = ϖ → ∀ (q : ℕ), 2 ≤ q → (∃ s ∈ S, (q : B) = ϖ * s) →
    ∀ (φ : PowerSeries R), PowerSeries.constantCoeff φ = 0 →
      PowerSeries.subst φ (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q : PowerSeries R) = PowerSeries.subst (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ q : PowerSeries R) φ →
    ∀ (σ : B →+* B), (∀ s ∈ S, σ s ∈ S) → (∀ k, ∀ x ∈ F k, σ x ∈ F k) → σ ϖ = ϖ →
    ∀ Q ∈ S, (∃ M : ℕ, 0 < M ∧ Near S ϖ (F 1) 1 (Q ^ M)) →
      (∀ m, EvalMod S F ϖ h φ Q (σ Q) m) →
    ∀ t, Tends S F ϖ (fun n => ϖ' ^ n * ltIter ϖ q n Q) t → σ t = h (PowerSeries.coeff 1 φ) * t := by
  intro B _ S F ϖ R _ E ϖ' hϖ' h hh π hπ q hq _ φ h0 hc σ hσS hσF hσϖ Q hQ hM hev t hT
  obtain ⟨M, -, hN⟩ := hM
  set a := h (PowerSeries.coeff 1 φ) with ha_def
  have ha : a ∈ S := hh _
  have hσϖ' : σ ϖ' = ϖ' := by
    have e2 : ϖ * σ ϖ' = 1 := by
      have := congrArg σ hϖ'
      rwa [map_mul, hσϖ, map_one] at this
    linear_combination (-(σ ϖ')) * hϖ' + ϖ' * e2
  have hnil := nilp_of_near E ⟨Q, hQ⟩ hN
  have hy : ∀ n, ltIter ϖ q n Q ∈ S := fun n => ltIter_mem E.mem q n hQ
  have key : ∀ k, σ t - a * t ∈ F k := by
    intro k
    obtain ⟨c, hT'⟩ := hT k
    obtain ⟨N₀, hN₀⟩ := hT' 0
    have hnear : ∀ m, Near S ϖ (F k) m (ϖ ^ c * (σ t - a * t)) := by
      intro m
      obtain ⟨N, hNm⟩ := hT' m
      obtain ⟨e, he⟩ : ∃ e, e = N + N₀ + m + 2 * (c + N₀) := ⟨_, rfl⟩
      obtain ⟨n, hn⟩ : ∃ n, n = e + (c + N₀) := ⟨_, rfl⟩
      obtain ⟨d, hd⟩ : ∃ d, c + 2 * e = n + m + d := ⟨c + 2 * e - (n + m), by omega⟩
      have hE1 := hNm n (by omega)
      have hE2 := near_map σ hσS (hσF k) hσϖ hE1
      have hE3 := near_mul ha hE1
      obtain ⟨u, hu, hu'⟩ := est E hϖ' hy hN₀ e
      rw [← hn] at hu'
      obtain ⟨yS, r, hyS, hr, D, hD, hv⟩ :=
        iter_val E h hh π hπ hq φ h0 hc σ hσS hσϖ ⟨Q, hQ⟩ hnil hev n k (m + n)
      obtain ⟨W, hW⟩ := tev_second (gq E h hh k (m + n)) hD φ h0
      obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective W
      rw [hv] at hW
      have hmem : r - ((⟨a, ha⟩ : S) * yS + yS ^ 2 * w) ∈ nearI S F E.mem k (m + n) := by
        rw [← Ideal.Quotient.eq, hW, map_add, map_mul, map_mul, map_pow]
        rfl
      rw [mem_nearI] at hmem
      obtain ⟨s, hs, hx⟩ := hmem
      have hP : ϖ ^ n * ϖ' ^ n = 1 := by rw [← mul_pow, hϖ', one_pow]
      have hx' : (σ (ltIter ϖ q n Q) - a * ltIter ϖ q n Q) - ltIter ϖ q n Q ^ 2 * (w : B)
          - ϖ ^ (m + n) * s ∈ F k := by
        have e1 : (σ (ltIter ϖ q n Q) - a * ltIter ϖ q n Q) - ltIter ϖ q n Q ^ 2 * (w : B)
            - ϖ ^ (m + n) * s = ((r - ((⟨a, ha⟩ : S) * yS + yS ^ 2 * w) : S) : B) - ϖ ^ (m + n) * s := by
          push_cast
          rw [hr, hyS]
          ring
        rw [e1]
        exact hx
      have hE4 := small E.mem hP hs hu w.2 hd hx' hu'
      have e2 : ϖ ^ c * (σ t - a * t) =
          a * (ϖ ^ c * (ϖ' ^ n * ltIter ϖ q n Q - t)) -
            σ (ϖ ^ c * (ϖ' ^ n * ltIter ϖ q n Q - t)) +
            ϖ ^ c * ϖ' ^ n * (σ (ltIter ϖ q n Q) - a * ltIter ϖ q n Q) := by
        simp only [map_mul, map_pow, map_sub, hσϖ, hσϖ']
        ring
      rw [e2]
      exact near_add (near_sub hE3 hE2) hE4
    obtain ⟨x, hx, hxF⟩ := hnear 0
    have hxk : x ∈ F k := by
      refine E.closed k x hx fun m => ?_
      obtain ⟨s, hs, hsF⟩ := hnear m
      refine ⟨s, hs, ?_⟩
      have e3 : x - ϖ ^ m * s = (ϖ ^ c * (σ t - a * t) - ϖ ^ m * s) -
          (ϖ ^ c * (σ t - a * t) - ϖ ^ 0 * x) := by ring
      rw [e3]
      exact (F k).sub_mem hsF hxF
    have hd : ϖ ^ c * (σ t - a * t) ∈ F k := by
      have e4 : ϖ ^ c * (σ t - a * t) = (ϖ ^ c * (σ t - a * t) - ϖ ^ 0 * x) + x := by ring
      rw [e4]
      exact (F k).add_mem hxF hxk
    have hP : ϖ ^ c * ϖ' ^ c = 1 := by rw [← mul_pow, hϖ', one_pow]
    have e5 : σ t - a * t = ϖ' ^ c * (ϖ ^ c * (σ t - a * t)) := by
      linear_combination (-(σ t - a * t)) * hP
    rw [e5]
    exact (F k).mul_mem_left _ hd
  exact sub_eq_zero.1 (E.sep _ key)

end GlobalTheory.CompanionTheory.LTPer
