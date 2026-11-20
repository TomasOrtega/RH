import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

variable {k K L : Type} [Field k] [Field K] [Field L]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, h | h⟩ hu`. Conclude with `hu.ne_zero (Subtype.ext h)`. Take `⟨y, hy⟩` from `hu.exists_right_inv`. Establish `e : (x : K) * y = 1` using `congrArg Subtype.val hy`.

Conclude with `h ((eq_inv_of_mul_eq_one_right e) ▸ y.2)`. Introduce `h`. Use `⟨x.2, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Use `push Not at hc`.

Conclude with `h (IsUnit.of_mul_eq_one ⟨_, hc.2⟩ (Subtype.ext (mul_inv_cancel₀ hc.1)))`.
-/
theorem nonUnit_coe_iff {R : Subring K} (x : R) : NonUnit R (x : K) ↔ ¬ IsUnit x := by
  constructor
  · rintro ⟨_, h | h⟩ hu
    · exact hu.ne_zero (Subtype.ext h)
    · obtain ⟨y, hy⟩ := hu.exists_right_inv
      have e : (x : K) * y = 1 := congrArg Subtype.val hy
      exact h ((eq_inv_of_mul_eq_one_right e) ▸ y.2)
  · intro h
    refine ⟨x.2, ?_⟩
    by_contra hc
    push Not at hc
    exact h (IsUnit.of_mul_eq_one ⟨_, hc.2⟩ (Subtype.ext (mul_inv_cancel₀ hc.1)))

namespace PolyTower

variable (R : Subring K) [IsLocalRing R] (r : ℕ)

def origin : Ideal (MvPolynomial (Fin r) R) :=
  (IsLocalRing.maximalIdeal R).comap MvPolynomial.constantCoeff

instance : (origin R r).IsPrime := Ideal.comap_isPrime _ _

def topRing : Subring (FractionRing (MvPolynomial (Fin r) R)) :=
  (Localization.subalgebra.ofField (FractionRing (MvPolynomial (Fin r) R))
    (origin R r).primeCompl (origin R r).primeCompl_le_nonZeroDivisors).toSubring

instance : Algebra (MvPolynomial (Fin r) R) (topRing R r) :=
  inferInstanceAs (Algebra (MvPolynomial (Fin r) R)
    (Localization.subalgebra.ofField (FractionRing (MvPolynomial (Fin r) R))
      (origin R r).primeCompl (origin R r).primeCompl_le_nonZeroDivisors))

instance : IsLocalization.AtPrime (topRing R r) (origin R r) :=
  Localization.subalgebra.isLocalization_ofField (FractionRing (MvPolynomial (Fin r) R))
    (origin R r).primeCompl (origin R r).primeCompl_le_nonZeroDivisors

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_algebraMap (x : MvPolynomial (Fin r) R) :
    ((algebraMap _ (topRing R r) x : topRing R r) : FractionRing (MvPolynomial (Fin r) R)) =
      algebraMap _ _ x := rfl

def incl : R →+* topRing R r := (algebraMap (MvPolynomial (Fin r) R) (topRing R r)).comp MvPolynomial.C

def coord (i : Fin r) : topRing R r := algebraMap (MvPolynomial (Fin r) R) (topRing R r) (MvPolynomial.X i)

/- English proof (translation)
Assume the negation of the conclusion as `h`. Conclude with `y.2 h`.
-/
theorem unit_const (y : (origin R r).primeCompl) :
    IsUnit (MvPolynomial.constantCoeff (y : MvPolynomial (Fin r) R)) := by
  by_contra h
  exact y.2 h

def sect : topRing R r →+* R := IsLocalization.lift (S := topRing R r) (unit_const R r)

/- English proof (translation)
The claim follows from `IsLocalization.lift_eq _ _`.
-/
theorem sect_algebraMap (x : MvPolynomial (Fin r) R) :
    sect R r (algebraMap _ (topRing R r) x) = MvPolynomial.constantCoeff x :=
  IsLocalization.lift_eq _ _

/- English proof (translation)
Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using `[incl]`. Introduce `i`. Simplify using `[coord]`.
-/
theorem eval_eq : MvPolynomial.eval₂Hom (incl R r) (coord R r) =
    algebraMap (MvPolynomial (Fin r) R) (topRing R r) := by
  apply MvPolynomial.ringHom_ext
  · intro a; simp [incl]
  · intro i; simp [coord]

/- English proof (translation)
Introduce `h`. Establish `e` using `congrArg Subtype.val h`. Rewrite `e` using `[coord, coe_algebraMap]`. Conclude with `MvPolynomial.X_ne_zero i ((IsFractionRing.to_map_eq_zero_iff).1 e)`.
-/
theorem coord_ne_zero (i : Fin r) : coord R r i ≠ 0 := by
  intro h
  have e := congrArg Subtype.val h
  rw [coord, coe_algebraMap] at e
  exact MvPolynomial.X_ne_zero i ((IsFractionRing.to_map_eq_zero_iff).1 e)

end PolyTower

open PolyTower in

/- English proof (translation)
The claim follows from `h normal := h' top := { const_mem := fun a => (incl R r _).2 isLocalRing := IsLocalization.AtPrime.isLocalRing _ (origin R r) essFiniteType := by have e1 : (MvPolynomial.C : R →+* MvPolynomial (Fin r) R).EssFiniteType := RingHom.essFiniteType_algebraMap.2 (inferInstance : Algebra …`.
-/
theorem IsEtTower.poly {c : k →+* K} {R : Subring K} [IsLocalRing R] (h : IsLocModel c R)
    (h' : IsIntegrallyClosed R) (r : ℕ) :
    IsEtTower c R ((topRing R r).subtype.comp ((incl R r).comp (c.codRestrict R h.const_mem)))
      (topRing R r) (incl R r) (sect R r) (coord R r) where
  base := h
  normal := h'
  top :=
    { const_mem := fun a => (incl R r _).2
      isLocalRing := IsLocalization.AtPrime.isLocalRing _ (origin R r)
      essFiniteType := by
        have e1 : (MvPolynomial.C : R →+* MvPolynomial (Fin r) R).EssFiniteType :=
          RingHom.essFiniteType_algebraMap.2
            (inferInstance : Algebra.EssFiniteType R (MvPolynomial (Fin r) R))
        have e2 : (algebraMap (MvPolynomial (Fin r) R) (topRing R r)).EssFiniteType :=
          RingHom.essFiniteType_algebraMap.2
            (Algebra.EssFiniteType.of_isLocalization _ (origin R r).primeCompl)
        exact (h.essFiniteType.comp e1).comp e2
      frac := fun f => by
        obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin r) R) f
        have hb' : algebraMap _ (FractionRing (MvPolynomial (Fin r) R)) b ≠ 0 :=
          IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
        exact ⟨_, (algebraMap _ (topRing R r) a).2, _, (algebraMap _ (topRing R r) b).2, hb',
          div_mul_cancel₀ _ hb'⟩ }
  const _ := rfl
  retr a := by simp [incl, sect_algebraMap]
  zero i := by simp [coord, sect_algebraMap]
  etale := by
    rw [eval_eq]
    have := Algebra.FormallyEtale.of_isLocalization (Rₘ := topRing R r) (origin R r).primeCompl
    exact RingHom.formallyEtale_algebraMap.2 this

/- English proof (translation)
Rewrite using `[nonUnit_coe_iff]`. Introduce `hu`. Use `hu.map ψ` as an intermediate fact. Rewrite `this` using `[h.zero]`. Conclude with `not_isUnit_zero this`.
-/
theorem IsEtTower.nonUnit_coord {cK : k →+* K} {R : Subring K} {cL : k →+* L} {T : Subring L}
    {r : ℕ} {ι : R →+* T} {ψ : T →+* R} {τ : Fin r → T} (h : IsEtTower cK R cL T ι ψ τ)
    (i : Fin r) : NonUnit T (τ i) := by
  rw [nonUnit_coe_iff]
  intro hu
  have := hu.map ψ
  rw [h.zero] at this
  exact not_isUnit_zero this

/- English proof (translation)
Introduce `t ht`. Take `⟨a, ha⟩` from `hR (ψ ⟨t, ht⟩) (ψ ⟨t, ht⟩).2`. Use `⟨a, ?_⟩` and prove the remaining obligations. Establish `e : t - cL a = ((⟨t, ht⟩ - ι ⟨cK a, h.base.const_mem a⟩ : T) : L)`. Rewrite using `[← h.const]`.

Both sides reduce to the same expression. Rewrite using `[e, nonUnit_coe_iff]`. Introduce `hu`. Establish `hu'` using `hu.map ψ`. Rewrite `hu'` using `[map_sub, h.retr]`.

Conclude with `(nonUnit_coe_iff _).1 ha hu'`.
-/
theorem IsEtTower.ratRes {cK : k →+* K} {R : Subring K} {cL : k →+* L} {T : Subring L}
    {r : ℕ} {ι : R →+* T} {ψ : T →+* R} {τ : Fin r → T} (h : IsEtTower cK R cL T ι ψ τ)
    (hR : RatRes cK R) : RatRes cL T := by
  intro t ht
  obtain ⟨a, ha⟩ := hR (ψ ⟨t, ht⟩) (ψ ⟨t, ht⟩).2
  refine ⟨a, ?_⟩
  have e : t - cL a = ((⟨t, ht⟩ - ι ⟨cK a, h.base.const_mem a⟩ : T) : L) := by
    rw [← h.const]; rfl
  rw [e, nonUnit_coe_iff]
  intro hu
  have hu' := hu.map ψ
  rw [map_sub, h.retr] at hu'
  exact (nonUnit_coe_iff _).1 ha hu'

/- English proof (translation)
Use `haveI : IsLocalRing (⊤ : Subring k) := (isLocModel_self (k := k)).isLocalRing`. Establish `hn : IsIntegrallyClosed (⊤ : Subring k)` using `IsIntegrallyClosed.of_equiv (Subring.topEquiv (R := k)).symm`. Establish `h` using `IsEtTower.poly (isLocModel_self (k := k)) hn 1`. Use `⟨_, _, _, _, _, _, _, h, PolyTower.coord_ne_zero _ _ 0, h.nonUnit_coord 0, h.ratRes fun x _ => ⟨x, trivial, Or.inl (sub_self x)⟩, fun f _ => ⟨h.top.const_mem f, ?_⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨_, rfl | hf⟩`.

Conclude with `⟨h.top.const_mem 0, Or.inl (map_zero _)⟩`. Conclude with `(hf trivial).elim`.
-/
theorem exists_isEtTower_line (k : Type) [Field k] :
    ∃ (L : Type) (_ : Field L) (cL : k →+* L) (T : Subring L) (ι : (⊤ : Subring k) →+* T)
      (ψ : T →+* (⊤ : Subring k)) (τ : Fin 1 → T),
      IsEtTower (RingHom.id k) ⊤ cL T ι ψ τ ∧ τ 0 ≠ 0 ∧ NonUnit T (τ 0) ∧ RatRes cL T ∧
        Dominates cL T ⊤ := by
  haveI : IsLocalRing (⊤ : Subring k) := (isLocModel_self (k := k)).isLocalRing
  have hn : IsIntegrallyClosed (⊤ : Subring k) :=
    IsIntegrallyClosed.of_equiv (Subring.topEquiv (R := k)).symm
  have h := IsEtTower.poly (isLocModel_self (k := k)) hn 1
  refine ⟨_, _, _, _, _, _, _, h, PolyTower.coord_ne_zero _ _ 0, h.nonUnit_coord 0,
    h.ratRes fun x _ => ⟨x, trivial, Or.inl (sub_self x)⟩, fun f _ => ⟨h.top.const_mem f, ?_⟩⟩
  rintro ⟨_, rfl | hf⟩
  · exact ⟨h.top.const_mem 0, Or.inl (map_zero _)⟩
  · exact (hf trivial).elim

/- English proof (translation)
Introduce `h` and use `by rcases ((h f hf.1).2 hf).2 with e | e · exact h0 ((map_eq_zero ρ).1 e) · exact e trivial`.
-/
theorem not_dominates_top (ρ : K →+* L) {O : Subring K} {f : K} (hf : NonUnit O f) (h0 : f ≠ 0) :
    ¬ Dominates ρ ⊤ O := fun h => by
  rcases ((h f hf.1).2 hf).2 with e | e
  · exact h0 ((map_eq_zero ρ).1 e)
  · exact e trivial

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h x`. Take `⟨x, rfl⟩` from `IsLocalRing.residue_surjective x`. Take `⟨a, ha⟩` from `h x x.2`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Establish `hn : ¬ IsUnit (x - ⟨c a, hc a⟩ : R)` using `(nonUnit_coe_iff _).1 ha`. Use `(IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 hn)` as an intermediate fact. Rewrite `this` using `[map_sub, sub_eq_zero]`. Conclude with `this.symm`. Introduce `h x hx`.

Take `⟨a, ha⟩` from `h (IsLocalRing.residue R ⟨x, hx⟩)`. Use `⟨a, (nonUnit_coe_iff (⟨x, hx⟩ - ⟨c a, hc a⟩ : R)).2 ?_⟩` and prove the remaining obligations. Establish `: IsLocalRing.residue R (⟨x, hx⟩ - ⟨c a, hc a⟩) = 0`. Rewrite using `[map_sub, sub_eq_zero]`. Conclude with `ha.symm`.

Conclude with `(IsLocalRing.mem_maximalIdeal _).1 ((IsLocalRing.residue_eq_zero_iff _).1 this)`.
-/
theorem ratRes_iff_surjective {c : k →+* K} {R : Subring K} [IsLocalRing R] (hc : ∀ a, c a ∈ R) :
    RatRes c R ↔ Function.Surjective ((IsLocalRing.residue R).comp (c.codRestrict R hc)) := by
  constructor
  · intro h x
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨a, ha⟩ := h x x.2
    refine ⟨a, ?_⟩
    have hn : ¬ IsUnit (x - ⟨c a, hc a⟩ : R) := (nonUnit_coe_iff _).1 ha
    have := (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 hn)
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  · intro h x hx
    obtain ⟨a, ha⟩ := h (IsLocalRing.residue R ⟨x, hx⟩)
    refine ⟨a, (nonUnit_coe_iff (⟨x, hx⟩ - ⟨c a, hc a⟩ : R)).2 ?_⟩
    have : IsLocalRing.residue R (⟨x, hx⟩ - ⟨c a, hc a⟩) = 0 := by
      rw [map_sub, sub_eq_zero]; exact ha.symm
    exact (IsLocalRing.mem_maximalIdeal _).1 ((IsLocalRing.residue_eq_zero_iff _).1 this)

/- English proof (translation)
Introduce `h`. Take `⟨a, -, h | h⟩` from `h Complex.I trivial`. Simplify using `using congrArg Complex.im h`. Conclude with `h trivial`.
-/
theorem not_ratRes_complex : ¬ RatRes (algebraMap ℝ ℂ) ⊤ := by
  intro h
  obtain ⟨a, -, h | h⟩ := h Complex.I trivial
  · simpa using congrArg Complex.im h
  · exact h trivial

/- English proof (translation)
Introduce `r _` and use `⟨r, by rw [RingHom.id_apply, sub_self]; exact ⟨R.zero_mem, Or.inl rfl⟩⟩`.
-/
example (R : Subring K) : RatRes (RingHom.id K) R :=
  fun r _ => ⟨r, by rw [RingHom.id_apply, sub_self]; exact ⟨R.zero_mem, Or.inl rfl⟩⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun f hf => (h f hf).1, ⟨fun a ha => ?_⟩⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Conclude with `(nonUnit_coe_iff (ρ.restrict O B (fun f hf => (h f hf).1) a)).1 ((h a a.2).2 ((nonUnit_coe_iff a).2 hn)) ha`.

Introduce and unpack `⟨h, hl⟩ f hf`. Use `⟨h f hf, fun hn => (nonUnit_coe_iff (ρ.restrict O B h ⟨f, hf⟩)).2 fun hu => ?_⟩` and prove the remaining obligations. Conclude with `(nonUnit_coe_iff (⟨f, hf⟩ : O)).1 hn (hl.map_nonunit _ hu)`.
-/
theorem dominates_iff_isLocalHom {ρ : K →+* L} {B : Subring L} {O : Subring K} :
    Dominates ρ B O ↔ ∃ h : ∀ f ∈ O, ρ f ∈ B, IsLocalHom (ρ.restrict O B h) := by
  constructor
  · intro h
    refine ⟨fun f hf => (h f hf).1, ⟨fun a ha => ?_⟩⟩
    by_contra hn
    exact (nonUnit_coe_iff (ρ.restrict O B (fun f hf => (h f hf).1) a)).1
      ((h a a.2).2 ((nonUnit_coe_iff a).2 hn)) ha
  · rintro ⟨h, hl⟩ f hf
    refine ⟨h f hf, fun hn => (nonUnit_coe_iff (ρ.restrict O B h ⟨f, hf⟩)).2 fun hu => ?_⟩
    exact (nonUnit_coe_iff (⟨f, hf⟩ : O)).1 hn (hl.map_nonunit _ hu)

/- English proof (translation)
Set `P` to `MvPolynomial (Fin r) R`. Use `letI : Algebra P T := (MvPolynomial.eval₂Hom ι τ).toAlgebra`. Use `haveI : Algebra.FormallyEtale P T := h.etale`. Set `g : P →+* DualNumber R` to `MvPolynomial.eval₂Hom (algebraMap R (DualNumber R)) fun i => TrivSqZeroExt.inr (v i)`. Use `letI : Algebra P (DualNumber R) := g.toAlgebra`.

Use `letI : Algebra P R := (MvPolynomial.constantCoeff : P →+* R).toAlgebra`. Set `ψ' : T →ₐ[P] R` to `{ ψ with commutes' := fun x => by`. Establish `: ψ.comp (MvPolynomial.eval₂Hom ι τ) = MvPolynomial.constantCoeff`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`.

Simplify using `[h.retr]`. Introduce `i`. Simplify using `[h.zero]`. Conclude with `RingHom.congr_fun this x }`. Set `f : DualNumber R →ₐ[P] R` to `{ (TrivSqZeroExt.fstHom R R R).toRingHom with commutes' := fun x => by`.

Establish `: (TrivSqZeroExt.fstHom R R R).toRingHom.comp g = MvPolynomial.constantCoeff`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using `[g]`. Introduce `i`.

Simplify using `[g]`. Conclude with `RingHom.congr_fun this x }`. Establish `hs : Function.Surjective f` using `fun a => ⟨TrivSqZeroExt.inl a, rfl⟩`. Establish `hn : IsNilpotent (RingHom.ker (f : DualNumber R →+* R))`. Use `⟨2, ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]`. Introduce `x hx y hy`. Establish `hx' : x.fst = 0` using `hx`. Establish `hy' : y.fst = 0` using `hy`. Rewrite using `[Ideal.mem_bot]`.

Apply the tactic sequence `ext <;> simp [hx', hy']`. Set `φ` to `Algebra.FormallySmooth.liftOfSurjective ψ' f hs hn`. Use `⟨φ.toRingHom, fun a => ?_, fun i => ?_⟩` and prove the remaining obligations. Use `φ.commutes (MvPolynomial.C a)` as an intermediate fact. Express the relevant statement in the definitionally equal form `φ (MvPolynomial.eval₂Hom ι τ (MvPolynomial.C a)) = g (MvPolynomial.C a) at this`.

Rewrite `this` using `[MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]`. Conclude with `this`. Use `φ.commutes (MvPolynomial.X i)` as an intermediate fact. Express the relevant statement in the definitionally equal form `φ (MvPolynomial.eval₂Hom ι τ (MvPolynomial.X i)) = g (MvPolynomial.X i) at this`. Rewrite `this` using `[MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']`.

Conclude with `this`.
-/
theorem IsEtTower.exists_deriv {cK : k →+* K} {R : Subring K} {cL : k →+* L} {T : Subring L}
    {r : ℕ} {ι : R →+* T} {ψ : T →+* R} {τ : Fin r → T} (h : IsEtTower cK R cL T ι ψ τ)
    (v : Fin r → R) : ∃ φ : T →+* DualNumber R, (∀ a, φ (ι a) = TrivSqZeroExt.inl a) ∧
      ∀ i, φ (τ i) = TrivSqZeroExt.inr (v i) := by
  let P := MvPolynomial (Fin r) R
  letI : Algebra P T := (MvPolynomial.eval₂Hom ι τ).toAlgebra
  haveI : Algebra.FormallyEtale P T := h.etale
  let g : P →+* DualNumber R :=
    MvPolynomial.eval₂Hom (algebraMap R (DualNumber R)) fun i => TrivSqZeroExt.inr (v i)
  letI : Algebra P (DualNumber R) := g.toAlgebra
  letI : Algebra P R := (MvPolynomial.constantCoeff : P →+* R).toAlgebra
  let ψ' : T →ₐ[P] R :=
    { ψ with
      commutes' := fun x => by
        have : ψ.comp (MvPolynomial.eval₂Hom ι τ) = MvPolynomial.constantCoeff := by
          apply MvPolynomial.ringHom_ext
          · intro a; simp [h.retr]
          · intro i; simp [h.zero]
        exact RingHom.congr_fun this x }
  let f : DualNumber R →ₐ[P] R :=
    { (TrivSqZeroExt.fstHom R R R).toRingHom with
      commutes' := fun x => by
        have : (TrivSqZeroExt.fstHom R R R).toRingHom.comp g = MvPolynomial.constantCoeff := by
          apply MvPolynomial.ringHom_ext
          · intro a; simp [g]
          · intro i; simp [g]
        exact RingHom.congr_fun this x }
  have hs : Function.Surjective f := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hn : IsNilpotent (RingHom.ker (f : DualNumber R →+* R)) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    have hx' : x.fst = 0 := hx
    have hy' : y.fst = 0 := hy
    rw [Ideal.mem_bot]
    ext <;> simp [hx', hy']
  let φ := Algebra.FormallySmooth.liftOfSurjective ψ' f hs hn
  refine ⟨φ.toRingHom, fun a => ?_, fun i => ?_⟩
  · have := φ.commutes (MvPolynomial.C a)
    change φ (MvPolynomial.eval₂Hom ι τ (MvPolynomial.C a)) = g (MvPolynomial.C a) at this
    rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C] at this
    exact this
  · have := φ.commutes (MvPolynomial.X i)
    change φ (MvPolynomial.eval₂Hom ι τ (MvPolynomial.X i)) = g (MvPolynomial.X i) at this
    rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X'] at this
    exact this

/- English proof (translation)
Take `⟨φ, h1, h2⟩` from `h.exists_deriv (Pi.single j 1)`. Use `congrArg (fun x => (φ x).snd) ha` as an intermediate fact. Simplify using `only [map_sum, map_mul, h1, h2, map_zero, TrivSqZeroExt.snd_sum, TrivSqZeroExt.inl_mul_inr, TrivSqZeroExt.snd_inr] at this`. Simplify `this` using `[Pi.single_apply]`.
-/
theorem IsEtTower.coord_indep {cK : k →+* K} {R : Subring K} {cL : k →+* L} {T : Subring L}
    {r : ℕ} {ι : R →+* T} {ψ : T →+* R} {τ : Fin r → T} (h : IsEtTower cK R cL T ι ψ τ)
    (a : Fin r → R) (ha : ∑ i, ι (a i) * τ i = 0) (j : Fin r) : a j = 0 := by
  obtain ⟨φ, h1, h2⟩ := h.exists_deriv (Pi.single j 1)
  have := congrArg (fun x => (φ x).snd) ha
  simp only [map_sum, map_mul, h1, h2, map_zero, TrivSqZeroExt.snd_sum,
    TrivSqZeroExt.inl_mul_inr, TrivSqZeroExt.snd_inr] at this
  simpa [Pi.single_apply] using this

/- English proof (translation)
Introduce `e`. Take `⟨φ, -, h2⟩` from `h.exists_deriv (fun _ => 1)`. Use `congrArg TrivSqZeroExt.snd (h2 j)` as an intermediate fact. Simplify using `[e] at this`.
-/
theorem IsEtTower.coord_ne_zero {cK : k →+* K} {R : Subring K} {cL : k →+* L} {T : Subring L}
    {r : ℕ} {ι : R →+* T} {ψ : T →+* R} {τ : Fin r → T} (h : IsEtTower cK R cL T ι ψ τ)
    (j : Fin r) : τ j ≠ 0 := by
  intro e
  obtain ⟨φ, -, h2⟩ := h.exists_deriv (fun _ => 1)
  have := congrArg TrivSqZeroExt.snd (h2 j)
  simp [e] at this

/- English proof (translation)
Use `haveI := h.top.isLocalRing`. Use `haveI : IsNoetherianRing T := by`. Use `letI := (cL.codRestrict T h.top.const_mem).toAlgebra`. Use `haveI : Algebra.EssFiniteType k T := h.top.essFiniteType`. Conclude with `Algebra.EssFiniteType.isNoetherianRing k T`.

Set `P` to `MvPolynomial (Fin r) R`. Use `letI : Algebra P T := (MvPolynomial.eval₂Hom ι τ).toAlgebra`. Use `haveI : Algebra.FormallyEtale P T := h.etale`. Use `set I := RingHom.ker ψ`. Use `set J : Ideal T := Ideal.span (Set.range τ)`.

Establish `hJI : J ≤ I` using `Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact h.zero i)`. Establish `hsub : ∀ x, x - ι (ψ x) ∈ I` using `fun x => by show ψ _ = 0`. Rewrite using `[map_sub, h.retr, sub_self]`. Set `Q : Ideal T` to `J ⊔ I * I`. Set `g : T →ₐ[P] T ⧸ Q` to `{ (Ideal.Quotient.mk Q).comp (ι.comp ψ) with commutes' := fun x => by`.

Establish `: ((Ideal.Quotient.mk Q).comp (ι.comp ψ)).comp (MvPolynomial.eval₂Hom ι τ) = (Ideal.Quotient.mk Q).comp (MvPolynomial.eval₂Hom ι τ)`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using `[h.retr]`. Introduce `i`.

Establish `: τ i ∈ Q` using `Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩)`. Simplify using `[h.zero, Ideal.Quotient.eq_zero_iff_mem.2 this]`. Conclude with `RingHom.congr_fun this x }`. Establish `hn : IsNilpotent (I.map (Ideal.Quotient.mk Q))`. Use `⟨2, ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_two, ← Ideal.map_mul, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]`. Conclude with `le_sup_right`. Establish `he : Ideal.Quotient.mkₐ P Q = g`. Use `Algebra.FormallyUnramified.ext _ hn fun x => ?_` and prove the remaining obligations. Rewrite using `[Ideal.Quotient.eq]`.

Use `Ideal.mem_map_of_mem (Ideal.Quotient.mk Q) (hsub x)` as an intermediate fact. Rewrite `this` using `[map_sub]`. Conclude with `this`. Establish `hIQ : I ≤ J ⊔ I • I` using `fun x hx => by`. Establish `e` using `AlgHom.congr_fun he x`.

Establish `hx' : ψ x = 0` using `hx`. Establish `: Ideal.Quotient.mk Q x = 0`. Use `e.trans ?_` and prove the remaining obligations. Use `show Ideal.Quotient.mk Q (ι (ψ x)) = 0`. Rewrite using `[hx', map_zero, map_zero]`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 this`. Establish `hI : I ≤ Ideal.jacobson ⊥`. Rewrite using `[IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]`. Conclude with `IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top ψ)`. Conclude with `le_antisymm (Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian I) hI hIQ) hJI`.
-/
theorem IsEtTower.ker_eq_span {cK : k →+* K} {R : Subring K} {cL : k →+* L} {T : Subring L}
    {r : ℕ} {ι : R →+* T} {ψ : T →+* R} {τ : Fin r → T} (h : IsEtTower cK R cL T ι ψ τ) :
    RingHom.ker ψ = Ideal.span (Set.range τ) := by
  haveI := h.top.isLocalRing
  haveI : IsNoetherianRing T := by
    letI := (cL.codRestrict T h.top.const_mem).toAlgebra
    haveI : Algebra.EssFiniteType k T := h.top.essFiniteType
    exact Algebra.EssFiniteType.isNoetherianRing k T
  let P := MvPolynomial (Fin r) R
  letI : Algebra P T := (MvPolynomial.eval₂Hom ι τ).toAlgebra
  haveI : Algebra.FormallyEtale P T := h.etale
  set I := RingHom.ker ψ
  set J : Ideal T := Ideal.span (Set.range τ)
  have hJI : J ≤ I := Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact h.zero i)
  have hsub : ∀ x, x - ι (ψ x) ∈ I := fun x => by
    show ψ _ = 0
    rw [map_sub, h.retr, sub_self]
  let Q : Ideal T := J ⊔ I * I
  let g : T →ₐ[P] T ⧸ Q :=
    { (Ideal.Quotient.mk Q).comp (ι.comp ψ) with
      commutes' := fun x => by
        have : ((Ideal.Quotient.mk Q).comp (ι.comp ψ)).comp (MvPolynomial.eval₂Hom ι τ) =
            (Ideal.Quotient.mk Q).comp (MvPolynomial.eval₂Hom ι τ) := by
          apply MvPolynomial.ringHom_ext
          · intro a; simp [h.retr]
          · intro i
            have : τ i ∈ Q := Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩)
            simp [h.zero, Ideal.Quotient.eq_zero_iff_mem.2 this]
        exact RingHom.congr_fun this x }
  have hn : IsNilpotent (I.map (Ideal.Quotient.mk Q)) := by
    refine ⟨2, ?_⟩
    rw [pow_two, ← Ideal.map_mul, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    exact le_sup_right
  have he : Ideal.Quotient.mkₐ P Q = g := by
    refine Algebra.FormallyUnramified.ext _ hn fun x => ?_
    rw [Ideal.Quotient.eq]
    have := Ideal.mem_map_of_mem (Ideal.Quotient.mk Q) (hsub x)
    rw [map_sub] at this
    exact this
  have hIQ : I ≤ J ⊔ I • I := fun x hx => by
    have e := AlgHom.congr_fun he x
    have hx' : ψ x = 0 := hx
    have : Ideal.Quotient.mk Q x = 0 := by
      refine e.trans ?_
      show Ideal.Quotient.mk Q (ι (ψ x)) = 0
      rw [hx', map_zero, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  have hI : I ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top ψ)
  exact le_antisymm (Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian I) hI hIQ) hJI

/- English proof (translation)
Use `⟨(RingHom.injective_iff_ker_eq_bot ψ).2 ?_, fun a => ⟨ι a, h.retr a⟩⟩` and prove the remaining obligations. Rewrite using `[h.ker_eq_span, Set.range_eq_empty, Ideal.span_empty]`.
-/
theorem IsEtTower.bijective_of_zero {cK : k →+* K} {R : Subring K} {cL : k →+* L} {T : Subring L}
    {ι : R →+* T} {ψ : T →+* R} {τ : Fin 0 → T} (h : IsEtTower cK R cL T ι ψ τ) :
    Function.Bijective ψ := by
  refine ⟨(RingHom.injective_iff_ker_eq_bot ψ).2 ?_, fun a => ⟨ι a, h.retr a⟩⟩
  rw [h.ker_eq_span, Set.range_eq_empty, Ideal.span_empty]

end GlobalTheory.FieldPair
