import ReciprocityTheory.DualLattices.NsetExpInjectiveSurjective

noncomputable section

open PowerSeries

namespace ReciprocityTheory.PGsh

namespace TowerExample

variable (p : ℕ) [Fact p.Prime]

abbrev TQ (m : ℕ) := (ZMod p)⟦X⟧ ⧸ Ideal.span {(X : (ZMod p)⟦X⟧) ^ m}

/- English proof (translation)
Rewrite using `[Ne, Ideal.span_singleton_eq_top, PowerSeries.isUnit_iff_constantCoeff]`. Simplify using `[zero_pow hm.ne']`.
-/
lemma ne_top (m : ℕ) (hm : 0 < m) : Ideal.span {(X : (ZMod p)⟦X⟧) ^ m} ≠ ⊤ := by
  rw [Ne, Ideal.span_singleton_eq_top, PowerSeries.isUnit_iff_constantCoeff]
  simp [zero_pow hm.ne']

/- English proof (translation)
Rewrite using `[← not_subsingleton_iff_nontrivial, Ideal.Quotient.subsingleton_iff]`. Conclude with `ne_top p m hm`.
-/
lemma nontriv (m : ℕ) (hm : 0 < m) : Nontrivial (TQ p m) := by
  rw [← not_subsingleton_iff_nontrivial, Ideal.Quotient.subsingleton_iff]
  exact ne_top p m hm

/- English proof (translation)
Use `haveI := nontriv p m hm`. Conclude with `IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective`.
-/
lemma isLocal (m : ℕ) (hm : 0 < m) : IsLocalRing (TQ p m) := by
  haveI := nontriv p m hm
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/- English proof (translation)
The claim follows from `charP_of_injective_algebraMap (algebraMap (ZMod p) A).injective p`.
-/
lemma charP_of_zmod (A : Type) [CommRing A] [Algebra (ZMod p) A] [Nontrivial A] : CharP A p := charP_of_injective_algebraMap (algebraMap (ZMod p) A).injective p

/- English proof (translation)
Use `⟨fun a ha => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hna`. Take `⟨c, hc⟩` from `hf (↑ha.unit⁻¹ : S)`. Establish `hker : RingHom.ker f ≤ IsLocalRing.maximalIdeal R` using `IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top f)`. Establish `h1 : 1 - a * c ∈ RingHom.ker f`.

Rewrite using `[RingHom.mem_ker, map_sub, map_one, map_mul, hc, IsUnit.mul_val_inv, sub_self]`. Establish `h2 : a * c ∈ IsLocalRing.maximalIdeal R` using `Ideal.mul_mem_right c _ ((IsLocalRing.mem_maximalIdeal a).2 hna)`. Establish `h3` using `Ideal.add_mem _ (hker h1) h2`. Rewrite `h3` using `[sub_add_cancel]`. Conclude with `(Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal R).ne_top h3`.
-/
lemma isLocalHom_of_surj {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [Nontrivial S]
    (f : R →+* S) (hf : Function.Surjective f) : IsLocalHom f := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  obtain ⟨c, hc⟩ := hf (↑ha.unit⁻¹ : S)
  have hker : RingHom.ker f ≤ IsLocalRing.maximalIdeal R :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top f)
  have h1 : 1 - a * c ∈ RingHom.ker f := by
    rw [RingHom.mem_ker, map_sub, map_one, map_mul, hc, IsUnit.mul_val_inv, sub_self]
  have h2 : a * c ∈ IsLocalRing.maximalIdeal R :=
    Ideal.mul_mem_right c _ ((IsLocalRing.mem_maximalIdeal a).2 hna)
  have h3 := Ideal.add_mem _ (hker h1) h2
  rw [sub_add_cancel] at h3
  exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal R).ne_top h3

/- English proof (translation)
The claim follows from `pow_pos (Fact.out : p.Prime).pos _`.
-/
lemma pos (n : ℕ) : 0 < p ^ (n + 1) := pow_pos (Fact.out : p.Prime).pos _

/- English proof (translation)
Use `pos p n` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
lemma pos2 (n : ℕ) : 0 < 2 * p ^ (n + 1) := by
  have := pos p n
  omega

def alg (m : ℕ) (hm : 0 < m) : LAlg (ZMod p) :=
  { carrier := TQ p m, loc := isLocal p m hm }

def algO : LAlg (ZMod p) := { carrier := (ZMod p)⟦X⟧ }

def red (m : ℕ) : TQ p (2 * m) →ₐ[ZMod p] TQ p m :=
  Ideal.Quotient.liftₐ _ (Ideal.Quotient.mkₐ (ZMod p) _) (fun a ha => by
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    rw [Ideal.mem_span_singleton] at ha
    exact (pow_dvd_pow X (by omega : m ≤ 2 * m)).trans ha)

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma red_mk (m : ℕ) (f : (ZMod p)⟦X⟧) :
    red p m (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ f := rfl

/- English proof (translation)
Introduce `y`. Take `⟨f, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Conclude with `⟨Ideal.Quotient.mk _ f, red_mk p m f⟩`.
-/
lemma red_surj (m : ℕ) : Function.Surjective (red p m) := by
  intro y
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk _ f, red_mk p m f⟩

/- English proof (translation)
Use extensionality with `a`. Take `⟨f, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Rewrite using `[RingHom.mem_ker]`. Express the relevant statement in the definitionally equal form `red p m (Ideal.Quotient.mk _ f) = 0 ↔ _`. Rewrite using `[red_mk, Ideal.Quotient.eq_zero_iff_mem]`.

Simplify using `only [Ideal.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, rfl⟩`. Conclude with `⟨Ideal.Quotient.mk _ g, map_mul _ _ _⟩`. Introduce and unpack `⟨b, hb⟩`.

Take `⟨g, rfl⟩` from `Ideal.Quotient.mk_surjective b`. Rewrite `hb` using `[← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton]`. Establish `h1 : X ^ m ∣ f - X ^ m * g` using `(pow_dvd_pow X (by omega : m ≤ 2 * m)).trans hb`. Establish `h2 : (X : (ZMod p)⟦X⟧) ^ m ∣ X ^ m * g` using `dvd_mul_right _ _`. Simplify using `using dvd_add h1 h2`.
-/
lemma red_ker (m : ℕ) : RingHom.ker (red p m) =
    Ideal.span {(Ideal.Quotient.mk (Ideal.span {(X : (ZMod p)⟦X⟧) ^ (2 * m)}) (X ^ m))} := by
  ext a
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [RingHom.mem_ker]
  change red p m (Ideal.Quotient.mk _ f) = 0 ↔ _
  rw [red_mk, Ideal.Quotient.eq_zero_iff_mem]
  simp only [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨Ideal.Quotient.mk _ g, map_mul _ _ _⟩
  · rintro ⟨b, hb⟩
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hb
    have h1 : X ^ m ∣ f - X ^ m * g := (pow_dvd_pow X (by omega : m ≤ 2 * m)).trans hb
    have h2 : (X : (ZMod p)⟦X⟧) ^ m ∣ X ^ m * g := dvd_mul_right _ _
    simpa using dvd_add h1 h2

/- English proof (translation)
Take `⟨f, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Rewrite `ha` using `[← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]`. Rewrite using `[Ideal.mem_span_singleton]`. Establish `h : (X : (ZMod p)⟦X⟧) ^ m ∣ f`. Rewrite `ha` using `[two_mul, pow_add]`.

Conclude with `(mul_dvd_mul_iff_right (pow_ne_zero m PowerSeries.X_ne_zero)).1 ha`. Take `⟨g, rfl⟩` from `h`. Conclude with `⟨Ideal.Quotient.mk _ g, map_mul _ _ _⟩`.
-/
lemma red_ann (m : ℕ) (a : TQ p (2 * m))
    (ha : a * Ideal.Quotient.mk (Ideal.span {(X : (ZMod p)⟦X⟧) ^ (2 * m)}) (X ^ m) = 0) :
    a ∈ Ideal.span {(Ideal.Quotient.mk (Ideal.span {(X : (ZMod p)⟦X⟧) ^ (2 * m)}) (X ^ m))} := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at ha
  rw [Ideal.mem_span_singleton]
  have h : (X : (ZMod p)⟦X⟧) ^ m ∣ f := by
    rw [two_mul, pow_add] at ha
    exact (mul_dvd_mul_iff_right (pow_ne_zero m PowerSeries.X_ne_zero)).1 ha
  obtain ⟨g, rfl⟩ := h
  exact ⟨Ideal.Quotient.mk _ g, map_mul _ _ _⟩

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero`. Rewrite using `[zero_add, pow_one]`. Use linear arithmetic over natural numbers and integers. Consider the case `succ k ih`.

Establish `h1 : p ^ (k + 1) * 2 ≤ p ^ (k + 1) * p` using `Nat.mul_le_mul_left _ hp`. Rewrite using `[pow_succ p (k + 1)]`. Use linear arithmetic over natural numbers and integers.
-/
lemma lt_pow_succ (j : ℕ) (hp : 2 ≤ p) : j < p ^ (j + 1) := by
  induction j with
  | zero =>
    rw [zero_add, pow_one]
    omega
  | succ k ih =>
    have h1 : p ^ (k + 1) * 2 ≤ p ^ (k + 1) * p := Nat.mul_le_mul_left _ hp
    rw [pow_succ p (k + 1)]
    omega

/- English proof (translation)
Rewrite using `[← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← pow_add, ← two_mul]`. Conclude with `Ideal.subset_span (Set.mem_singleton _)`.
-/
lemma xi_sq (m : ℕ) : Ideal.Quotient.mk (Ideal.span {(X : (ZMod p)⟦X⟧) ^ (2 * m)}) (X ^ m) *
    Ideal.Quotient.mk (Ideal.span {(X : (ZMod p)⟦X⟧) ^ (2 * m)}) (X ^ m) = 0 := by
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← pow_add, ← two_mul]
  exact Ideal.subset_span (Set.mem_singleton _)

/- English proof (translation)
Use `haveI := nontriv p m hm`. Use `haveI := charP_of_zmod p (TQ p m)`. Rewrite using `[Nat.cast_pow, CharP.cast_eq_zero, zero_pow hk.ne']`.
-/
lemma char_lemma (m k : ℕ) (hm : 0 < m) (hk : 0 < k) : ((p ^ k : ℕ) : TQ p m) = 0 := by
  haveI := nontriv p m hm
  haveI := charP_of_zmod p (TQ p m)
  rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow hk.ne']

/- English proof (translation)
Use extensionality with `j`. Establish `h` using `ha j`. Rewrite `h` using `[Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]`. Simplify using `using h j (lt_pow_succ p j (Fact.out : p.Prime).two_le)`.
-/
lemma sep_lemma (a : (ZMod p)⟦X⟧)
    (ha : ∀ n : ℕ, Ideal.Quotient.mk (Ideal.span {(X : (ZMod p)⟦X⟧) ^ p ^ (n + 1)}) a = 0) :
    a = 0 := by
  ext j
  have h := ha j
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at h
  simpa using h j (lt_pow_succ p j (Fact.out : p.Prime).two_le)

/- English proof (translation)
Use `haveI := nontriv p m hm`. Use `haveI := charP_of_zmod p (TQ p m)`. Use `haveI : ExpChar (TQ p m) p := ExpChar.prime (Fact.out : p.Prime)`. Rewrite using `[map_add, map_one, add_pow_char_pow, one_pow, one_mul, map_pow]`.
-/
lemma frob_lemma (m k : ℕ) (hm : 0 < m) :
    (Ideal.Quotient.mk (Ideal.span {(X : (ZMod p)⟦X⟧) ^ m}) (1 + X)) ^ p ^ k =
      1 + 1 * Ideal.Quotient.mk (Ideal.span {(X : (ZMod p)⟦X⟧) ^ m}) (X ^ p ^ k) := by
  haveI := nontriv p m hm
  haveI := charP_of_zmod p (TQ p m)
  haveI : ExpChar (TQ p m) p := ExpChar.prime (Fact.out : p.Prime)
  rw [map_add, map_one, add_pow_char_pow, one_pow, one_mul, map_pow]

def u1X : ((ZMod p)⟦X⟧)ˣ :=
  (show IsUnit (1 + X : (ZMod p)⟦X⟧) by
    rw [PowerSeries.isUnit_iff_constantCoeff]; simp).unit

end TowerExample

open TowerExample in

def toyTower (p : ℕ) [Fact p.Prime] : ATower (ZMod p) p where
  O := algO p
  R' n := alg p (2 * p ^ (n + 1)) (pos2 p n)
  R n := alg p (p ^ (n + 1)) (pos p n)
  π n := ⟨red p (p ^ (n + 1)), by
    haveI := isLocal p _ (pos2 p n); haveI := nontriv p _ (pos p n)
    exact isLocalHom_of_surj _ (red_surj p _)⟩
  q n := ⟨Ideal.Quotient.mkₐ (ZMod p) (Ideal.span {(X : (ZMod p)⟦X⟧) ^ p ^ (n + 1)}), by
    haveI := nontriv p _ (pos p n)
    exact isLocalHom_of_surj _
      (Ideal.Quotient.mkₐ_surjective (ZMod p) (Ideal.span {(X : (ZMod p)⟦X⟧) ^ p ^ (n + 1)}))⟩
  ξ n := Ideal.Quotient.mk _ (X ^ p ^ (n + 1))
  surj n := red_surj p _
  ker_eq n := red_ker p _
  ξ_sq n := xi_sq p _
  ann n a ha := red_ann p _ a ha
  char n := char_lemma p _ _ (pos2 p n) (Nat.succ_pos n)
  sep a ha := sep_lemma p a ha
  c := 1
  cp n := 1
  cp_spec n := (map_one _).trans (map_one _).symm
  zh n := Units.map (Ideal.Quotient.mk (Ideal.span {(X : (ZMod p)⟦X⟧) ^ (2 * p ^ (n + 1))}) : (ZMod p)⟦X⟧ →* TQ p (2 * p ^ (n + 1))) (u1X p)
  zh_pow n := frob_lemma p _ _ (pos2 p n)
  ζ n := u1X p
  ζ_spec n := rfl

/- English proof (translation)
The claim follows from `(show (1 : (ZMod p)⟦X⟧) ≠ 0 from one_ne_zero)`.
-/
lemma toyTower_c_ne_zero (p : ℕ) [Fact p.Prime] : (toyTower p).c ≠ 0 := (show (1 : (ZMod p)⟦X⟧) ≠ 0 from one_ne_zero)

/- English proof (translation)
The claim follows from `(inferInstance : IsDomain (ZMod p)⟦X⟧)`.
-/
theorem toyTower_isDomain (p : ℕ) [Fact p.Prime] : IsDomain ((toyTower p).O : Type) := (inferInstance : IsDomain (ZMod p)⟦X⟧)

end ReciprocityTheory.PGsh
