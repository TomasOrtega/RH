import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisMembershipSpanIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfForallXiPowDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KerThetaLocalizedEqSpanFontaineXiElement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompatibleRootsOfUnityAndTiltPadic
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImportsMore

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.PdModP

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]

def low (R : Type) {A : Type} [CommRing R] [CommRing A] [Algebra R A] (γ : ℕ → A) (N : ℕ) : Submodule R A :=
  Submodule.span R (γ '' {m | m < N})

/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.image_mono fun _ hm => lt_of_lt_of_le hm h)`.
-/
theorem low_mono (γ : ℕ → A) {M N : ℕ} (h : M ≤ N) : low R γ M ≤ low R γ N :=
  Submodule.span_mono (Set.image_mono fun _ hm => lt_of_lt_of_le hm h)

/- English proof (translation)
Establish `e : {m | m < N + 1} = insert N {m | m < N}`. Use extensionality with `m`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_insert_iff]`. Use linear arithmetic over natural numbers and integers. Rewrite `hs` using `[low, e, Set.image_insert_eq, Submodule.mem_span_insert]`.

Conclude with `hs`.
-/
theorem mem_low_succ (γ : ℕ → A) (N : ℕ) (s : A) (hs : s ∈ low R γ (N + 1)) :
    ∃ (a : R) (y : A), y ∈ low R γ N ∧ s = a • γ N + y := by
  have e : {m | m < N + 1} = insert N {m | m < N} := by
    ext m; simp only [Set.mem_ofPred_eq, Set.mem_insert_iff]; omega
  rw [low, e, Set.image_insert_eq, Submodule.mem_span_insert] at hs
  exact hs

section
variable (hu : ∀ n : ℕ, IsUnit ((n.factorial : ℕ) : A)) (ξ : R) (γ : ℕ → A)
  (hγ : ∀ n : ℕ, ((n.factorial : ℕ) : A) * γ n = algebraMap R A ξ ^ n)
include hu hγ

/- English proof (translation)
Take `⟨v, hv⟩` from `(hu n).exists_left_inv`. Establish `: γ n = v * algebraMap R A ξ ^ n` using `by rw [← hγ, ← mul_assoc, hv, one_mul]`. Rewrite using `[this]`. Conclude with `Dvd.dvd.mul_left (pow_dvd_pow _ h) _`.
-/
theorem pow_dvd_gamma {m n : ℕ} (h : m ≤ n) : algebraMap R A ξ ^ m ∣ γ n := by
  obtain ⟨v, hv⟩ := (hu n).exists_left_inv
  have : γ n = v * algebraMap R A ξ ^ n := by rw [← hγ, ← mul_assoc, hv, one_mul]
  rw [this]
  exact Dvd.dvd.mul_left (pow_dvd_pow _ h) _

/- English proof (translation)
Use `(hu n).mul_left_cancel ?_` and prove the remaining obligations. Establish `h1` using `hγ n`. Establish `h2` using `hγ (n + 1)`. Rewrite `h2` using `[Nat.factorial_succ, Nat.cast_mul, pow_succ]`. Take the linear combination `(algebraMap R A ξ) * h1 - h2`.
-/
theorem mul_gamma (n : ℕ) : algebraMap R A ξ * γ n = ((n + 1 : ℕ) : A) * γ (n + 1) := by
  refine (hu n).mul_left_cancel ?_
  have h1 := hγ n
  have h2 := hγ (n + 1)
  rw [Nat.factorial_succ, Nat.cast_mul, pow_succ] at h2
  linear_combination (algebraMap R A ξ) * h1 - h2

/- English proof (translation)
Establish `hregn : ∀ (n : ℕ) (y : A), algebraMap R A ξ ^ n * y = 0 → y = 0`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro y hy`. Simplify using `using hy`.

Consider the case `succ n ih => intro y hy; exact hreg y (ih _ (by rw [← hy]; ring))`. Proceed by induction on `N with`. Consider the case `zero`. Introduce `s hs _`. Use `⟨0, ?_⟩` and prove the remaining obligations.

Simplify `hs` using `[low]`. Consider the case `succ N ih`. Introduce `s hs hd`. Take `⟨a, y, hy, rfl⟩` from `mem_low_succ γ N s hs`. Establish `h1 : algebraMap R A ξ ^ N ∣ a • γ N`.

Rewrite using `[Algebra.smul_def]`. Conclude with `Dvd.dvd.mul_left (pow_dvd_gamma hu ξ γ hγ le_rfl) _`. Take `⟨c, rfl⟩` from `ih y hy ((dvd_add_right h1).1 ((pow_dvd_pow _ N.le_succ).trans hd))`. Take `⟨z, hz⟩` from `hd`. Establish `h2 : algebraMap R A ξ ∣ algebraMap R A (a + c * N)`.

Use `⟨(N.factorial : ℕ) * z, sub_eq_zero.1 (hregn N _ ?_)⟩` and prove the remaining obligations. Rewrite `hz` using `[Algebra.smul_def, Algebra.smul_def]`. Rewrite using `[map_add, map_mul, map_natCast]`. Establish `h3` using `hγ N`. Take the linear combination `((N.factorial : ℕ) : A) * hz - (algebraMap R A a + algebraMap R A c * N) * h3`.

Take `⟨d, hd⟩` from `hsat _ h2`. Use `⟨d, ?_⟩` and prove the remaining obligations. Establish `h4` using `congrArg (algebraMap R A) hd`. Rewrite `h4` using `[map_add, map_mul, map_natCast, map_mul]`. Rewrite using `[← mul_gamma hu ξ γ hγ, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def]`.

Take the linear combination `γ N * h4`.
-/
theorem low_inter (hreg : ∀ y : A, algebraMap R A ξ * y = 0 → y = 0)
    (hsat : ∀ a : R, algebraMap R A ξ ∣ algebraMap R A a → ξ ∣ a) (N : ℕ) :
    ∀ s ∈ low R γ N, algebraMap R A ξ ^ N ∣ s → ∃ c : R, s = c • ((N : A) * γ N) := by
  have hregn : ∀ (n : ℕ) (y : A), algebraMap R A ξ ^ n * y = 0 → y = 0 := by
    intro n
    induction n with
    | zero => intro y hy; simpa using hy
    | succ n ih => intro y hy; exact hreg y (ih _ (by rw [← hy]; ring))
  induction N with
  | zero =>
    intro s hs _
    refine ⟨0, ?_⟩
    simpa [low] using hs
  | succ N ih =>
    intro s hs hd
    obtain ⟨a, y, hy, rfl⟩ := mem_low_succ γ N s hs
    have h1 : algebraMap R A ξ ^ N ∣ a • γ N := by
      rw [Algebra.smul_def]
      exact Dvd.dvd.mul_left (pow_dvd_gamma hu ξ γ hγ le_rfl) _
    obtain ⟨c, rfl⟩ := ih y hy ((dvd_add_right h1).1 ((pow_dvd_pow _ N.le_succ).trans hd))
    obtain ⟨z, hz⟩ := hd
    have h2 : algebraMap R A ξ ∣ algebraMap R A (a + c * N) := by
      refine ⟨(N.factorial : ℕ) * z, sub_eq_zero.1 (hregn N _ ?_)⟩
      rw [Algebra.smul_def, Algebra.smul_def] at hz
      rw [map_add, map_mul, map_natCast]
      have h3 := hγ N
      linear_combination ((N.factorial : ℕ) : A) * hz - (algebraMap R A a + algebraMap R A c * N) * h3
    obtain ⟨d, hd⟩ := hsat _ h2
    refine ⟨d, ?_⟩
    have h4 := congrArg (algebraMap R A) hd
    rw [map_add, map_mul, map_natCast, map_mul] at h4
    rw [← mul_gamma hu ξ γ hγ, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def]
    linear_combination γ N * h4

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.IsolatedTheoremThree.main`. Consider the case `exact _root_.GlobalTheory.IsolatedTheoremThree.main`. Consider the case `(apply _root_.GlobalTheory.IsolatedTheoremThree.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.IsolatedTheoremThree.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.IsolatedTheoremThree.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.IsolatedTheoremThree.main ..)`.
-/
theorem split_low (N : ℕ) (w : A) (hw : w ∈ Submodule.span R (Set.range γ)) :
    ∃ w₁ ∈ low R γ N, algebraMap R A ξ ^ N ∣ w - w₁ := by
  first
  | exact @_root_.GlobalTheory.IsolatedTheoremThree.main
  | exact _root_.GlobalTheory.IsolatedTheoremThree.main
  | (apply _root_.GlobalTheory.IsolatedTheoremThree.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IsolatedTheoremThree.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IsolatedTheoremThree.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IsolatedTheoremThree.main ..)

end

/- English proof (translation)
Proceed by induction on `hs using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨m, rfl⟩` from `hx`. Conclude with `⟨m + 1, Submodule.subset_span ⟨m, m.lt_succ_self, rfl⟩⟩`. Consider the case `zero => exact ⟨0, zero_mem _⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨M, h1⟩` from `hx`. Take `⟨N, h2⟩` from `hy`. Conclude with `⟨max M N, add_mem (low_mono γ (le_max_left _ _) h1) (low_mono γ (le_max_right _ _) h2)⟩`. Consider the case `smul a x _ hx`.

Take `⟨M, h1⟩` from `hx`. Conclude with `⟨M, Submodule.smul_mem _ _ h1⟩`.
-/
theorem exists_low (γ : ℕ → A) (s : A) (hs : s ∈ Submodule.span R (Set.range γ)) : ∃ M, s ∈ low R γ M := by
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    exact ⟨m + 1, Submodule.subset_span ⟨m, m.lt_succ_self, rfl⟩⟩
  | zero => exact ⟨0, zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨M, h1⟩ := hx
    obtain ⟨N, h2⟩ := hy
    exact ⟨max M N, add_mem (low_mono γ (le_max_left _ _) h1) (low_mono γ (le_max_right _ _) h2)⟩
  | smul a x _ hx =>
    obtain ⟨M, h1⟩ := hx
    exact ⟨M, Submodule.smul_mem _ _ h1⟩

/- English proof (translation)
Take `⟨M, hM⟩` from `exists_low γ s hs`. Take `⟨u, w, hw, e, hd⟩` from `h (p * M)`. Take `⟨w₁, h1, h2⟩` from `split_low hu ξ γ hγ (p * M) w hw`. Establish `h3 : s - p * w₁ ∈ low R γ (p * M)`. Use `sub_mem (low_mono γ (Nat.le_mul_of_pos_left M hp) hM) ?_` and prove the remaining obligations.

Rewrite using `[← nsmul_eq_mul]`. Conclude with `nsmul_mem h1 p`. Take `⟨c, hc⟩` from `low_inter hu ξ γ hγ hreg hsat (p * M) _ h3 (by convert dvd_add hd (Dvd.dvd.mul_left h2 (p : A)) using 1; rw [e]; ring)`. Use `⟨w₁ + (c * M) • γ (p * M), add_mem (Submodule.span_mono (Set.image_subset_range _ _) h1) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)), ?_⟩` and prove the remaining obligations. Rewrite `hc` using `[Algebra.smul_def]`.

Rewrite using `[Algebra.smul_def, map_mul, map_natCast]`. Move the coercions through the operations in `at hc`. Take the linear combination `hc`.
-/
theorem mem_of_forall (hu : ∀ n : ℕ, IsUnit ((n.factorial : ℕ) : A)) (ξ : R) (γ : ℕ → A)
    (hγ : ∀ n : ℕ, ((n.factorial : ℕ) : A) * γ n = algebraMap R A ξ ^ n)
    (hreg : ∀ y : A, algebraMap R A ξ * y = 0 → y = 0)
    (hsat : ∀ a : R, algebraMap R A ξ ∣ algebraMap R A a → ξ ∣ a) (p : ℕ) (hp : 0 < p)
    (s : A) (hs : s ∈ Submodule.span R (Set.range γ))
    (h : ∀ n : ℕ, ∃ u : A, ∃ w ∈ Submodule.span R (Set.range γ), s = u + p * w ∧ algebraMap R A ξ ^ n ∣ u) :
    ∃ w ∈ Submodule.span R (Set.range γ), s = p * w := by
  obtain ⟨M, hM⟩ := exists_low γ s hs
  obtain ⟨u, w, hw, e, hd⟩ := h (p * M)
  obtain ⟨w₁, h1, h2⟩ := split_low hu ξ γ hγ (p * M) w hw
  have h3 : s - p * w₁ ∈ low R γ (p * M) := by
    refine sub_mem (low_mono γ (Nat.le_mul_of_pos_left M hp) hM) ?_
    rw [← nsmul_eq_mul]
    exact nsmul_mem h1 p
  obtain ⟨c, hc⟩ := low_inter hu ξ γ hγ hreg hsat (p * M) _ h3
    (by convert dvd_add hd (Dvd.dvd.mul_left h2 (p : A)) using 1; rw [e]; ring)
  refine ⟨w₁ + (c * M) • γ (p * M), add_mem (Submodule.span_mono (Set.image_subset_range _ _) h1)
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)), ?_⟩
  rw [Algebra.smul_def] at hc
  rw [Algebra.smul_def, map_mul, map_natCast]
  push_cast at hc
  linear_combination hc

/- English proof (translation)
Take `⟨ζ, e, h0, -, h1, hr⟩` from `exists_zeta_eps l`. Use `⟨e, ?_, fun h => ?_⟩` and prove the remaining obligations. Establish `h` using `hr 0`. Rewrite `h` using `[h0, map_one]`. Conclude with `Subtype.ext h`.

Establish `h'` using `hr 1`. Establish `h2 : rootT e 1 = 1` using `h`. Rewrite `h'` using `[h2]`. Apply `h1` to reduce the goal to its premises. Apply `(algebraMap (Om l) ℂ_[l]).injective` to reduce the goal to its premises.

Rewrite using `[map_one, ← h']`. Both sides reduce to the same expression.
-/
theorem exists_eps (l : ℕ) [Fact l.Prime] : ∃ e : Per.Fl l, IsEps e := by
  obtain ⟨ζ, e, h0, -, h1, hr⟩ := exists_zeta_eps l
  refine ⟨e, ?_, fun h => ?_⟩
  · have h := hr 0
    rw [h0, map_one] at h
    exact Subtype.ext h
  · have h' := hr 1
    have h2 : rootT e 1 = 1 := h
    rw [h2] at h'
    apply h1
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [map_one, ← h']
    rfl

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using h`. Consider the case `succ k ih`. Apply `ih` to reduce the goal to its premises. Use `XiHaus.xi_sat he 1 ((l : Per.Ainf l) ^ k * a) (by rwa [pow_one, ← mul_assoc, ← pow_succ'])` as an intermediate fact.

Rewrite `this` using `[pow_one]`. Then use the resulting hypothesis.
-/
theorem xi_sat_pow {l : ℕ} [Fact l.Prime] {e : Per.Fl l} (he : IsEps e) (k : ℕ) (a : Per.Ainf l)
    (h : xi e ∣ (l : Per.Ainf l) ^ k * a) : xi e ∣ a := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    apply ih
    have := XiHaus.xi_sat he 1 ((l : Per.Ainf l) ^ k * a) (by rwa [pow_one, ← mul_assoc, ← pow_succ'])
    rwa [pow_one] at this

end GlobalTheory.MemLoc.PdModP

namespace GlobalTheory.MemLoc
open PdModP in

/- English proof (translation)
Introduce `l hl s h`. Take `⟨e, he⟩` from `exists_eps l`. Establish `hu : ∀ n : ℕ, IsUnit ((n.factorial : ℕ) : Per.AinfP l)` using `fun n => GlobalTheory.RingBasics.isUnit_nat l _ n.factorial_ne_zero`. Establish `hex : ∀ n : ℕ, ∃ g : Per.AinfP l, ((n.factorial : ℕ) : Per.AinfP l) * g = algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ^ n` using `fun n => by`. Take `⟨v, hv⟩` from `(hu n).exists_right_inv`.

Conclude with `⟨v * _, by rw [← mul_assoc, hv, one_mul]⟩`. Use `choose γ hγ using hex`. Establish `hspan : ∀ x : Per.AinfP l, x ∈ Per.Acris0 l ↔ x ∈ Submodule.span (Per.Ainf l) (Set.range γ)`. Introduce `x`. Rewrite using `[mem_Acris0_iff_span l e he]`.

Use `congr! 2`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, hn⟩`. Conclude with `⟨n, (hu n).mul_left_cancel (by rw [hγ, hn])⟩`.

Introduce and unpack `⟨n, rfl⟩`. Conclude with `⟨n, hγ n⟩`. Use `XiHaus.isDomain_Fl (l := l)` as an intermediate fact. Establish `hle : Submonoid.powers (l : Per.Ainf l) ≤ nonZeroDivisors _` using `powers_le_nonZeroDivisors_of_noZeroDivisors (WittVector.p_nonzero l (Per.Fl l))`. Establish `hdom : IsDomain (Per.AinfP l)` using `IsLocalization.isDomain_of_le_nonZeroDivisors _ hle`.

Establish `hinj` using `IsLocalization.injective (Per.AinfP l) hle`. Establish `hx0 : algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ≠ 0`. Rewrite using `[map_ne_zero_iff _ hinj]`. Introduce `h0`. Conclude with `XiHaus.xi_coeff_zero_ne he (by rw [h0, WittVector.zero_coeff])`.

Take `⟨w, hw, e1⟩` from `mem_of_forall hu (xi e) γ hγ (fun y hy => (mul_eq_zero.1 hy).resolve_left hx0) (by`. Introduce and unpack `a ⟨z, hz⟩`. Take `⟨⟨b, ⟨_, k, rfl⟩⟩, hb⟩` from `IsLocalization.surj (Submonoid.powers (l : Per.Ainf l)) z`. Use `xi_sat_pow he k a ⟨b, hinj ?_⟩` and prove the remaining obligations. Simplify using `only at hb`.

Rewrite using `[map_mul, map_mul, hz, ← hb]`. Use the proof step `ring)`. Use `l hl.out.pos s ((hspan _).1 s.2) (fun n => by`. Take `⟨u, w, h1, h2⟩` from `h n`. Use `⟨u, w, (hspan _).1 w.2, by rw [h1]; simp, ?_⟩` and prove the remaining obligations.

Rewrite using `[ker_localizedTheta_eq_span_xi l e he, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h2)` and apply the resulting hypothesis. Conclude with `⟨⟨w, (hspan _).2 hw⟩, Subtype.ext (by simpa using e1)⟩`.
-/
theorem dvd_of_forall_fil_add : ∀ (l : ℕ) [Fact l.Prime], ∀ s : Per.Acris0 l,
    (∀ n : ℕ, ∃ (u w : Per.Acris0 l), s = u + (l : Per.Acris0 l) * w ∧ (u : Per.AinfP l) ∈ Per.kerP l ^ n) →
    (l : Per.Acris0 l) ∣ s := by
  intro l hl s h
  obtain ⟨e, he⟩ := exists_eps l
  have hu : ∀ n : ℕ, IsUnit ((n.factorial : ℕ) : Per.AinfP l) := fun n => GlobalTheory.RingBasics.isUnit_nat l _ n.factorial_ne_zero
  have hex : ∀ n : ℕ, ∃ g : Per.AinfP l,
      ((n.factorial : ℕ) : Per.AinfP l) * g = algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ^ n := fun n => by
    obtain ⟨v, hv⟩ := (hu n).exists_right_inv
    exact ⟨v * _, by rw [← mul_assoc, hv, one_mul]⟩
  choose γ hγ using hex
  have hspan : ∀ x : Per.AinfP l, x ∈ Per.Acris0 l ↔ x ∈ Submodule.span (Per.Ainf l) (Set.range γ) := by
    intro x
    rw [mem_Acris0_iff_span l e he]
    congr! 2
    ext y
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, (hu n).mul_left_cancel (by rw [hγ, hn])⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n, hγ n⟩
  have := XiHaus.isDomain_Fl (l := l)
  have hle : Submonoid.powers (l : Per.Ainf l) ≤ nonZeroDivisors _ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors (WittVector.p_nonzero l (Per.Fl l))
  have hdom : IsDomain (Per.AinfP l) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
  have hinj := IsLocalization.injective (Per.AinfP l) hle
  have hx0 : algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ≠ 0 := by
    rw [map_ne_zero_iff _ hinj]
    intro h0
    exact XiHaus.xi_coeff_zero_ne he (by rw [h0, WittVector.zero_coeff])
  obtain ⟨w, hw, e1⟩ := mem_of_forall hu (xi e) γ hγ (fun y hy => (mul_eq_zero.1 hy).resolve_left hx0)
    (by
      rintro a ⟨z, hz⟩
      obtain ⟨⟨b, ⟨_, k, rfl⟩⟩, hb⟩ := IsLocalization.surj (Submonoid.powers (l : Per.Ainf l)) z
      refine xi_sat_pow he k a ⟨b, hinj ?_⟩
      simp only at hb
      rw [map_mul, map_mul, hz, ← hb]
      ring)
    l hl.out.pos s ((hspan _).1 s.2) (fun n => by
      obtain ⟨u, w, h1, h2⟩ := h n
      refine ⟨u, w, (hspan _).1 w.2, by rw [h1]; simp, ?_⟩
      rwa [ker_localizedTheta_eq_span_xi l e he, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h2)
  exact ⟨⟨w, (hspan _).2 hw⟩, Subtype.ext (by simpa using e1)⟩

end GlobalTheory.MemLoc
