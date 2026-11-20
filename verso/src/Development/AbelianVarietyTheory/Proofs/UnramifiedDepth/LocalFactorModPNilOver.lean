import Mathlib
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.ATowerInh
import ReciprocityTheory.DualLattices.AinfFacts

open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

open TensorProduct IsLocalRing Matrix in
/- English proof (translation)
Establish `hmR : ∀ x ∈ maximalIdeal R.carrier, IsNilpotent x`. Introduce `x hx`. Apply `hρ.2` to reduce the goal to its premises. Use `haveI := ρ.2`. Establish `h1 : (ρ.1 : R.carrier →+* K.carrier) x ∈ maximalIdeal K.carrier` using `map_nonunit _ x hx`.

Rewrite `h1` using `[hK]`. Conclude with `h1`. Establish `hc0 : q.1 c = 0`. Establish `h1 : c ∈ RingHom.ker (q.1 : O.carrier →+* R.carrier)` using `hker ▸ Ideal.mem_span_singleton_self c`. Conclude with `h1`.

Establish `hc : ¬ IsUnit c`. Introduce `hu`. Establish `h1` using `hu.map q.1`. Rewrite `h1` using `[hc0]`. Conclude with `not_isUnit_zero h1`.

Establish `hsc : ¬ IsUnit (s.1 c)` using `by haveI := s.2`. Conclude with `fun h => hc ((isUnit_map_iff (s.1 : O.carrier →+* A.carrier) c).1 h)`. Use `set I : Ideal A.carrier := Ideal.span {s.1 c} with hI`. Establish `hItop : I ≠ ⊤`. Rewrite using `[hI, Ne, Ideal.span_singleton_eq_top]`.

Conclude with `hsc`. Use `haveI : Nontrivial (A.carrier ⧸ I) := _root_.ReciprocityTheory.PGsh.Ainf.quot_nontrivial I hItop`. Use `haveI : IsLocalRing (A.carrier ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective`. Set `Λ : _root_.ReciprocityTheory.PGsh.LAlg R₀` to `_root_.ReciprocityTheory.PGsh.LAlg.mk (A.carrier ⧸ I)`. Set `μ : _root_.ReciprocityTheory.PGsh.LHom A Λ` to `⟨Ideal.Quotient.mkₐ R₀ I, _root_.ReciprocityTheory.PGsh.TowerExample.isLocalHom_of_surj ((Ideal.Quotient.mkₐ R₀ I : A.carrier →ₐ[R₀] A.carrier ⧸ I) : A.carrier →+* A.carrier ⧸ I) (Ideal.Quotient.mkₐ_surjective R₀ I)⟩`.

Establish `hqc : ∀ a ∈ RingHom.ker q.1, ((Ideal.Quotient.mkₐ R₀ I).comp s.1) a = 0`. Introduce `a ha`. Establish `ha' : a ∈ RingHom.ker (q.1 : O.carrier →+* R.carrier)` using `ha`. Rewrite `ha'` using `[hker, Ideal.mem_span_singleton']`. Take `⟨b, rfl⟩` from `ha'`.

Rewrite using `[AlgHom.comp_apply, map_mul, map_mul, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), mul_zero]`. Set `j₀ : R.carrier →ₐ[R₀] A.carrier ⧸ I` to `(Ideal.Quotient.liftₐ (RingHom.ker q.1) ((Ideal.Quotient.mkₐ R₀ I).comp s.1) hqc).comp (Ideal.quotientKerAlgEquivOfSurjective hq).symm.toAlgHom`. Establish `hj₀ : ∀ x, j₀ (q.1 x) = Ideal.Quotient.mk I (s.1 x)`. Introduce `x`. Establish `h1 : (Ideal.quotientKerAlgEquivOfSurjective hq).symm (q.1 x) = Ideal.Quotient.mk (RingHom.ker q.1) x`.

Rewrite using `[AlgEquiv.symm_apply_eq]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `Ideal.Quotient.liftₐ (RingHom.ker q.1) ((Ideal.Quotient.mkₐ R₀ I).comp s.1) hqc ((Ideal.quotientKerAlgEquivOfSurjective hq).symm (q.1 x)) = _`. Rewrite using `[h1]`. Both sides reduce to the same expression.

Establish `hj₀loc : IsLocalHom (j₀ : R.carrier →+* A.carrier ⧸ I)`. Prove the components needed by the constructor for the conclusion. Introduce `x hx`. Assume the negation of the conclusion as `hxu`. Take `⟨n, hn⟩` from `hmR x ((mem_maximalIdeal x).2 hxu)`.

Establish `h1 : IsUnit ((j₀ : R.carrier →+* A.carrier ⧸ I) x ^ n)` using `hx.pow n`. Rewrite `h1` using `[← map_pow, hn, map_zero]`. Conclude with `not_isUnit_zero h1`. Set `j : _root_.ReciprocityTheory.PGsh.LHom R Λ` to `⟨j₀, hj₀loc⟩`. Establish `hψI : ∀ φ : _root_.ReciprocityTheory.PGsh.LHom A O, φ.comp s = _root_.ReciprocityTheory.PGsh.LHom.id O → ∀ a ∈ I, (q.1.comp φ.1) a = 0`.

Introduce `φ hφ a ha`. Rewrite `ha` using `[hI, Ideal.mem_span_singleton']`. Take `⟨b, rfl⟩` from `ha`. Establish `h1 : φ.1 (s.1 c) = c` using `congrArg (fun f : _root_.ReciprocityTheory.PGsh.LHom O O => f.1 c) hφ`. Rewrite using `[AlgHom.comp_apply, map_mul, map_mul, h1, hc0, mul_zero]`.

Set `ψ₀ : (φ : _root_.ReciprocityTheory.PGsh.LHom A O) → φ.comp s = _root_.ReciprocityTheory.PGsh.LHom.id O → (A.carrier ⧸ I →ₐ[R₀] R.carrier)` to `fun φ hφ => Ideal.Quotient.liftₐ I (q.1.comp φ.1) (hψI φ hφ)`. Establish `hψ₀mk : ∀ φ hφ a, ψ₀ φ hφ (Ideal.Quotient.mk I a) = q.1 (φ.1 a)` using `fun _ _ _ => rfl`. Establish `hψ₀loc : ∀ φ hφ, IsLocalHom (ψ₀ φ hφ : A.carrier ⧸ I →+* R.carrier)`. Introduce `φ hφ`. Prove the components needed by the constructor for the conclusion.

Introduce `x hx`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Establish `h1 : IsUnit (q.1 (φ.1 a))` using `hx`. Use `haveI := q.2`. Use `haveI := φ.2`.

Establish `h2 : IsUnit (φ.1 a)` using `isUnit_of_map_unit (q.1 : O.carrier →+* R.carrier) _ h1`. Establish `h3 : IsUnit a` using `isUnit_of_map_unit (φ.1 : A.carrier →+* O.carrier) _ h2`. Conclude with `h3.map (Ideal.Quotient.mk I)`. Set `ψ : (φ : _root_.ReciprocityTheory.PGsh.LHom A O) → φ.comp s = _root_.ReciprocityTheory.PGsh.LHom.id O → _root_.ReciprocityTheory.PGsh.LHom Λ R` to `fun φ hφ => ⟨ψ₀ φ hφ, hψ₀loc φ hφ⟩`. Establish `hψj : ∀ φ hφ r, ψ₀ φ hφ (j₀ r) = r`.

Introduce `φ hφ r`. Take `⟨x, rfl⟩` from `hq r`. Rewrite using `[hj₀, hψ₀mk φ hφ]`. Conclude with `congrArg (fun f : _root_.ReciprocityTheory.PGsh.LHom O R => f.1 x) (show q.comp (φ.comp s) = q.comp (_root_.ReciprocityTheory.PGsh.LHom.id O) by rw [hφ])`. Establish `hkerm : ∀ φ hφ (l : A.carrier ⧸ I), ρ.1 (ψ₀ φ hφ l) = 0 → l ∈ maximalIdeal (A.carrier ⧸ I)`.

Introduce `φ hφ l hl`. Rewrite using `[mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`. Establish `h1 : IsUnit (ρ.1 (ψ₀ φ hφ l))` using `(hu.map (ψ₀ φ hφ)).map ρ.1`. Rewrite `h1` using `[hl]`.

Conclude with `not_isUnit_zero h1`. Establish `hmK : ∀ φ hφ (l : A.carrier ⧸ I), l ∈ maximalIdeal (A.carrier ⧸ I) → ρ.1 (ψ₀ φ hφ l) = 0`. Introduce `φ hφ l hl`. Use `haveI := hψ₀loc φ hφ`. Use `haveI := ρ.2`.

Establish `h1 : (ρ.1 : R.carrier →+* K.carrier) ((ψ₀ φ hφ : A.carrier ⧸ I →+* R.carrier) l) ∈ maximalIdeal K.carrier` using `map_nonunit _ _ (map_nonunit _ l hl)`. Rewrite `h1` using `[hK]`. Conclude with `h1`. Establish `hagree : ∀ φ hφ (l : A.carrier ⧸ I), ρ.1 (ψ₀ φ hφ l) = ρ.1 (ψ₀ φ₀ hφ₀ l)`. Introduce `φ hφ l`.

Establish `h1 : ρ.1 (ψ₀ φ₀ hφ₀ (l - j₀ (ψ₀ φ₀ hφ₀ l))) = 0`. Rewrite using `[map_sub, hψj φ₀ hφ₀ (ψ₀ φ₀ hφ₀ l), sub_self, map_zero]`. Establish `h2` using `hmK φ hφ _ (hkerm φ₀ hφ₀ _ h1)`. Rewrite `h2` using `[map_sub, map_sub, hψj φ hφ (ψ₀ φ₀ hφ₀ l), sub_eq_zero]`. Conclude with `h2`.

Establish `hcomp : (Ideal.Quotient.mk I).comp (s.1 : O.carrier →+* A.carrier) = (j₀ : R.carrier →+* A.carrier ⧸ I).comp (q.1 : O.carrier →+* R.carrier)`. Use extensionality with `x`. Conclude with `(hj₀ x).symm`. Establish `hint : ((Ideal.Quotient.mk I).comp (s.1 : O.carrier →+* A.carrier)).IsIntegral` using `((RingHom.Finite.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective).comp hfin).to_isIntegral`. Use `⟨Λ, μ, j, ρ.comp (ψ φ₀ hφ₀), ⟨fun k => ?_, fun l hl => ?_⟩, Ideal.Quotient.mkₐ_surjective R₀ I, ?_, ?_, ?_⟩` and prove the remaining obligations.

Take `⟨r, rfl⟩` from `hρ.1 k`. Use `⟨j₀ r, ?_⟩` and prove the remaining obligations. Use `show ρ.1 (ψ₀ φ₀ hφ₀ (j₀ r)) = ρ.1 r`. Rewrite using `[hψj φ₀ hφ₀ r]`. Establish `hl' : ρ.1 (ψ₀ φ₀ hφ₀ l) = 0` using `hl`.

Establish `hm` using `hkerm φ₀ hφ₀ l hl'`. Rewrite using `[nilpotent_iff_mem_prime]`. Introduce `J hJ`. Establish `hJR : J.comap (j₀ : R.carrier →+* A.carrier ⧸ I) = maximalIdeal R.carrier`. Establish `hP : (J.comap (j₀ : R.carrier →+* A.carrier ⧸ I)).IsPrime` using `Ideal.comap_isPrime _ J`.

Apply `le_antisymm` to reduce the goal to its premises. Conclude with `le_maximalIdeal hP.ne_top`. Introduce `x hx`. Take `⟨n, hn⟩` from `hmR x hx`. Conclude with `hP.mem_of_pow_mem n (by rw [hn]; exact Ideal.zero_mem _)`.

Establish `hmax : (J.comap ((Ideal.Quotient.mk I).comp (s.1 : O.carrier →+* A.carrier))).IsMaximal`. Rewrite using `[hcomp, ← Ideal.comap_comap, hJR]`. Conclude with `Ideal.comap_isMaximal_of_surjective (q.1 : O.carrier →+* R.carrier) hq`. Establish `hJmax` using `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' _ hint J hmax`. Rewrite using `[eq_maximalIdeal hJmax]`.

Conclude with `hm`. Conclude with `Subtype.ext (AlgHom.ext fun r => by show ρ.1 (ψ₀ φ₀ hφ₀ (j₀ r)) = ρ.1 r`. Rewrite using `[hψj φ₀ hφ₀ r])`. Conclude with `Subtype.ext (AlgHom.ext fun x => by show Ideal.Quotient.mk I (s.1 x) = j₀ (q.1 x)`. Conclude with `(hj₀ x).symm)`.

Introduce `φ hφ`. Use `⟨ψ φ hφ, Subtype.ext (AlgHom.ext fun a => rfl), Subtype.ext (AlgHom.ext fun r => hψj φ hφ r), Subtype.ext (AlgHom.ext fun l => hagree φ hφ l)⟩` and prove the remaining obligations.
-/
private theorem exists_localFactor_lemma {R₀ : Type} [CommRing R₀] {O R K A : _root_.ReciprocityTheory.PGsh.LAlg R₀}
    (q : _root_.ReciprocityTheory.PGsh.LHom O R) (hq : Function.Surjective q.1) (c : O.carrier)
    (hker : RingHom.ker (q.1 : O.carrier →+* R.carrier) = Ideal.span {c})
    (ρ : _root_.ReciprocityTheory.PGsh.LHom R K) (hρ : _root_.ReciprocityTheory.PGsh.Be2.IsNilOver ρ) (hK : maximalIdeal K.carrier = ⊥)
    (s : _root_.ReciprocityTheory.PGsh.LHom O A) (hfin : (s.1 : O.carrier →+* A.carrier).Finite)
    (φ₀ : _root_.ReciprocityTheory.PGsh.LHom A O) (hφ₀ : φ₀.comp s = _root_.ReciprocityTheory.PGsh.LHom.id O) :
    ∃ (Λ : _root_.ReciprocityTheory.PGsh.LAlg R₀) (μ : _root_.ReciprocityTheory.PGsh.LHom A Λ) (j : _root_.ReciprocityTheory.PGsh.LHom R Λ) (ρΛ : _root_.ReciprocityTheory.PGsh.LHom Λ K),
      _root_.ReciprocityTheory.PGsh.Be2.IsNilOver ρΛ ∧ Function.Surjective μ.1 ∧ ρΛ.comp j = ρ ∧ μ.comp s = j.comp q ∧
      ∀ φ : _root_.ReciprocityTheory.PGsh.LHom A O, φ.comp s = _root_.ReciprocityTheory.PGsh.LHom.id O →
        ∃ ψ : _root_.ReciprocityTheory.PGsh.LHom Λ R, ψ.comp μ = q.comp φ ∧ ψ.comp j = _root_.ReciprocityTheory.PGsh.LHom.id R ∧ ρ.comp ψ = ρΛ := by
  classical
  have hmR : ∀ x ∈ maximalIdeal R.carrier, IsNilpotent x := by
    intro x hx
    apply hρ.2
    haveI := ρ.2
    have h1 : (ρ.1 : R.carrier →+* K.carrier) x ∈ maximalIdeal K.carrier := map_nonunit _ x hx
    rw [hK] at h1
    exact h1
  have hc0 : q.1 c = 0 := by
    have h1 : c ∈ RingHom.ker (q.1 : O.carrier →+* R.carrier) := hker ▸ Ideal.mem_span_singleton_self c
    exact h1
  have hc : ¬ IsUnit c := by
    intro hu
    have h1 := hu.map q.1
    rw [hc0] at h1
    exact not_isUnit_zero h1
  have hsc : ¬ IsUnit (s.1 c) := by
    haveI := s.2
    exact fun h => hc ((isUnit_map_iff (s.1 : O.carrier →+* A.carrier) c).1 h)
  set I : Ideal A.carrier := Ideal.span {s.1 c} with hI
  have hItop : I ≠ ⊤ := by
    rw [hI, Ne, Ideal.span_singleton_eq_top]
    exact hsc
  haveI : Nontrivial (A.carrier ⧸ I) := _root_.ReciprocityTheory.PGsh.Ainf.quot_nontrivial I hItop
  haveI : IsLocalRing (A.carrier ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let Λ : _root_.ReciprocityTheory.PGsh.LAlg R₀ := _root_.ReciprocityTheory.PGsh.LAlg.mk (A.carrier ⧸ I)
  let μ : _root_.ReciprocityTheory.PGsh.LHom A Λ := ⟨Ideal.Quotient.mkₐ R₀ I,
    _root_.ReciprocityTheory.PGsh.TowerExample.isLocalHom_of_surj ((Ideal.Quotient.mkₐ R₀ I : A.carrier →ₐ[R₀] A.carrier ⧸ I) : A.carrier →+* A.carrier ⧸ I)
      (Ideal.Quotient.mkₐ_surjective R₀ I)⟩
  have hqc : ∀ a ∈ RingHom.ker q.1, ((Ideal.Quotient.mkₐ R₀ I).comp s.1) a = 0 := by
    intro a ha
    have ha' : a ∈ RingHom.ker (q.1 : O.carrier →+* R.carrier) := ha
    rw [hker, Ideal.mem_span_singleton'] at ha'
    obtain ⟨b, rfl⟩ := ha'
    rw [AlgHom.comp_apply, map_mul, map_mul, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), mul_zero]
  let j₀ : R.carrier →ₐ[R₀] A.carrier ⧸ I :=
    (Ideal.Quotient.liftₐ (RingHom.ker q.1) ((Ideal.Quotient.mkₐ R₀ I).comp s.1) hqc).comp
      (Ideal.quotientKerAlgEquivOfSurjective hq).symm.toAlgHom
  have hj₀ : ∀ x, j₀ (q.1 x) = Ideal.Quotient.mk I (s.1 x) := by
    intro x
    have h1 : (Ideal.quotientKerAlgEquivOfSurjective hq).symm (q.1 x) =
        Ideal.Quotient.mk (RingHom.ker q.1) x := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    change Ideal.Quotient.liftₐ (RingHom.ker q.1) ((Ideal.Quotient.mkₐ R₀ I).comp s.1) hqc
      ((Ideal.quotientKerAlgEquivOfSurjective hq).symm (q.1 x)) = _
    rw [h1]
    rfl
  have hj₀loc : IsLocalHom (j₀ : R.carrier →+* A.carrier ⧸ I) := by
    constructor
    intro x hx
    by_contra hxu
    obtain ⟨n, hn⟩ := hmR x ((mem_maximalIdeal x).2 hxu)
    have h1 : IsUnit ((j₀ : R.carrier →+* A.carrier ⧸ I) x ^ n) := hx.pow n
    rw [← map_pow, hn, map_zero] at h1
    exact not_isUnit_zero h1
  let j : _root_.ReciprocityTheory.PGsh.LHom R Λ := ⟨j₀, hj₀loc⟩
  have hψI : ∀ φ : _root_.ReciprocityTheory.PGsh.LHom A O, φ.comp s = _root_.ReciprocityTheory.PGsh.LHom.id O → ∀ a ∈ I, (q.1.comp φ.1) a = 0 := by
    intro φ hφ a ha
    rw [hI, Ideal.mem_span_singleton'] at ha
    obtain ⟨b, rfl⟩ := ha
    have h1 : φ.1 (s.1 c) = c := congrArg (fun f : _root_.ReciprocityTheory.PGsh.LHom O O => f.1 c) hφ
    rw [AlgHom.comp_apply, map_mul, map_mul, h1, hc0, mul_zero]
  let ψ₀ : (φ : _root_.ReciprocityTheory.PGsh.LHom A O) → φ.comp s = _root_.ReciprocityTheory.PGsh.LHom.id O → (A.carrier ⧸ I →ₐ[R₀] R.carrier) :=
    fun φ hφ => Ideal.Quotient.liftₐ I (q.1.comp φ.1) (hψI φ hφ)
  have hψ₀mk : ∀ φ hφ a, ψ₀ φ hφ (Ideal.Quotient.mk I a) = q.1 (φ.1 a) := fun _ _ _ => rfl
  have hψ₀loc : ∀ φ hφ, IsLocalHom (ψ₀ φ hφ : A.carrier ⧸ I →+* R.carrier) := by
    intro φ hφ
    constructor
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h1 : IsUnit (q.1 (φ.1 a)) := hx
    haveI := q.2
    haveI := φ.2
    have h2 : IsUnit (φ.1 a) := isUnit_of_map_unit (q.1 : O.carrier →+* R.carrier) _ h1
    have h3 : IsUnit a := isUnit_of_map_unit (φ.1 : A.carrier →+* O.carrier) _ h2
    exact h3.map (Ideal.Quotient.mk I)
  let ψ : (φ : _root_.ReciprocityTheory.PGsh.LHom A O) → φ.comp s = _root_.ReciprocityTheory.PGsh.LHom.id O → _root_.ReciprocityTheory.PGsh.LHom Λ R :=
    fun φ hφ => ⟨ψ₀ φ hφ, hψ₀loc φ hφ⟩
  have hψj : ∀ φ hφ r, ψ₀ φ hφ (j₀ r) = r := by
    intro φ hφ r
    obtain ⟨x, rfl⟩ := hq r
    rw [hj₀, hψ₀mk φ hφ]
    exact congrArg (fun f : _root_.ReciprocityTheory.PGsh.LHom O R => f.1 x)
      (show q.comp (φ.comp s) = q.comp (_root_.ReciprocityTheory.PGsh.LHom.id O) by rw [hφ])
  have hkerm : ∀ φ hφ (l : A.carrier ⧸ I), ρ.1 (ψ₀ φ hφ l) = 0 →
      l ∈ maximalIdeal (A.carrier ⧸ I) := by
    intro φ hφ l hl
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 : IsUnit (ρ.1 (ψ₀ φ hφ l)) := (hu.map (ψ₀ φ hφ)).map ρ.1
    rw [hl] at h1
    exact not_isUnit_zero h1
  have hmK : ∀ φ hφ (l : A.carrier ⧸ I), l ∈ maximalIdeal (A.carrier ⧸ I) →
      ρ.1 (ψ₀ φ hφ l) = 0 := by
    intro φ hφ l hl
    haveI := hψ₀loc φ hφ
    haveI := ρ.2
    have h1 : (ρ.1 : R.carrier →+* K.carrier) ((ψ₀ φ hφ : A.carrier ⧸ I →+* R.carrier) l) ∈
        maximalIdeal K.carrier :=
      map_nonunit _ _ (map_nonunit _ l hl)
    rw [hK] at h1
    exact h1
  have hagree : ∀ φ hφ (l : A.carrier ⧸ I), ρ.1 (ψ₀ φ hφ l) = ρ.1 (ψ₀ φ₀ hφ₀ l) := by
    intro φ hφ l
    have h1 : ρ.1 (ψ₀ φ₀ hφ₀ (l - j₀ (ψ₀ φ₀ hφ₀ l))) = 0 := by
      rw [map_sub, hψj φ₀ hφ₀ (ψ₀ φ₀ hφ₀ l), sub_self, map_zero]
    have h2 := hmK φ hφ _ (hkerm φ₀ hφ₀ _ h1)
    rw [map_sub, map_sub, hψj φ hφ (ψ₀ φ₀ hφ₀ l), sub_eq_zero] at h2
    exact h2
  have hcomp : (Ideal.Quotient.mk I).comp (s.1 : O.carrier →+* A.carrier) =
      (j₀ : R.carrier →+* A.carrier ⧸ I).comp (q.1 : O.carrier →+* R.carrier) := by
    ext x
    exact (hj₀ x).symm
  have hint : ((Ideal.Quotient.mk I).comp (s.1 : O.carrier →+* A.carrier)).IsIntegral :=
    ((RingHom.Finite.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective).comp
      hfin).to_isIntegral
  refine ⟨Λ, μ, j, ρ.comp (ψ φ₀ hφ₀), ⟨fun k => ?_, fun l hl => ?_⟩,
    Ideal.Quotient.mkₐ_surjective R₀ I, ?_, ?_, ?_⟩
  · obtain ⟨r, rfl⟩ := hρ.1 k
    refine ⟨j₀ r, ?_⟩
    show ρ.1 (ψ₀ φ₀ hφ₀ (j₀ r)) = ρ.1 r
    rw [hψj φ₀ hφ₀ r]
  · have hl' : ρ.1 (ψ₀ φ₀ hφ₀ l) = 0 := hl
    have hm := hkerm φ₀ hφ₀ l hl'
    rw [nilpotent_iff_mem_prime]
    intro J hJ
    have hJR : J.comap (j₀ : R.carrier →+* A.carrier ⧸ I) = maximalIdeal R.carrier := by
      have hP : (J.comap (j₀ : R.carrier →+* A.carrier ⧸ I)).IsPrime := Ideal.comap_isPrime _ J
      apply le_antisymm
      · exact le_maximalIdeal hP.ne_top
      · intro x hx
        obtain ⟨n, hn⟩ := hmR x hx
        exact hP.mem_of_pow_mem n (by rw [hn]; exact Ideal.zero_mem _)
    have hmax : (J.comap ((Ideal.Quotient.mk I).comp (s.1 : O.carrier →+* A.carrier))).IsMaximal := by
      rw [hcomp, ← Ideal.comap_comap, hJR]
      exact Ideal.comap_isMaximal_of_surjective (q.1 : O.carrier →+* R.carrier) hq
    have hJmax := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' _ hint J hmax
    rw [eq_maximalIdeal hJmax]
    exact hm
  · exact Subtype.ext (AlgHom.ext fun r => by
      show ρ.1 (ψ₀ φ₀ hφ₀ (j₀ r)) = ρ.1 r
      rw [hψj φ₀ hφ₀ r])
  · exact Subtype.ext (AlgHom.ext fun x => by
      show Ideal.Quotient.mk I (s.1 x) = j₀ (q.1 x)
      exact (hj₀ x).symm)
  · intro φ hφ
    refine ⟨ψ φ hφ, Subtype.ext (AlgHom.ext fun a => rfl),
      Subtype.ext (AlgHom.ext fun r => hψj φ hφ r), Subtype.ext (AlgHom.ext fun l => hagree φ hφ l)⟩

open TensorProduct IsLocalRing Matrix in

/- English proof (translation)
Introduce `R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D hg`. Establish `hid : _root_.ReciprocityTheory.PGsh.Be2.IsNilOver (_root_.ReciprocityTheory.PGsh.LHom.id D.K)` using `⟨fun x => ⟨x, rfl⟩, fun a ha => ⟨1, by rw [pow_one]; exact (RingHom.mem_ker).1 ha⟩⟩`. Establish `hK : maximalIdeal (D.K : Type) = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `a ha`.

Establish `hsub : ∀ u v : {x // (B.map (_root_.ReciprocityTheory.PGsh.LHom.id D.K)) x = 0}, u = v`. Introduce `u v`. Establish `hu` using `u.2`. Establish `hv` using `v.2`. Rewrite `hu`, `hv` using `[B.map_id]`.

Conclude with `Subtype.ext (hu.trans hv.symm)`. Establish `h1 : (fun _ : Fin g => (⟨a, ha⟩ : maximalIdeal (D.K : Type))) = fun _ => 0` using `(D.ch.χ (_root_.ReciprocityTheory.PGsh.LHom.id D.K) hid).symm.injective (hsub _ _)`. Establish `h2` using `congrFun h1 ⟨0, hg⟩`. Conclude with `(Ideal.mem_bot).2 (congrArg Subtype.val h2)`. Establish `hW` using `D.sm.nil`.

Establish `heq` using `D.wd.ρW_eq`. Establish `hρ1 : _root_.ReciprocityTheory.PGsh.Be2.IsNilOver D.wd.ρ1`. Use `⟨fun k => ?_, fun a ha => ?_⟩` and prove the remaining obligations. Take `⟨w, hw⟩` from `hW.1 k`. Use `⟨D.wd.πW.1 w, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hw, ← heq]`. Both sides reduce to the same expression. Take `⟨w, rfl⟩` from `D.wd.πW_surj a`. Establish `hw : w ∈ RingHom.ker (D.wd.ρW.1 : D.wd.W.carrier →+* D.K.carrier)`. Rewrite using `[RingHom.mem_ker, ← heq]`.

Conclude with `(RingHom.mem_ker).1 ha`. Conclude with `(hW.2 w hw).map (D.wd.πW.1 : D.wd.W.carrier →+* (Tw.R 0).carrier)`. Use `⟨hK, hρ1, fun i => ?_⟩` and prove the remaining obligations. Establish `hsec : ∃ φ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx i) Tw.O, φ.comp (D.fin.sO i) = _root_.ReciprocityTheory.PGsh.LHom.id Tw.O`. Assume the negation of the conclusion as `hne`.

Use `push_neg at hne`. Establish `h1 : (1 : (D.fin.AAx i).carrier) = 0` using `D.fin.sep i 1 fun φ hφ => absurd hφ (hne φ)`. Conclude with `one_ne_zero h1`. Take `⟨φ₀, hφ₀⟩` from `hsec`. Establish `hfin : ((D.fin.sO i).1 : Tw.O.carrier →+* (D.fin.AAx i).carrier).Finite`.

Use `letI : Algebra Tw.O.carrier (D.fin.AAx i).carrier := ((D.fin.sO i).1 : Tw.O.carrier →+* (D.fin.AAx i).carrier).toAlgebra`. Conclude with `(D.fin.free i).2`. Conclude with `exists_localFactor_lemma (Tw.q 0) D.tower_zero_surjective (p : Tw.O.carrier) D.tower_zero_ker D.wd.ρ1 hρ1 hK (D.fin.sO i) hfin φ₀ hφ₀`.
-/
theorem _root_.GlobalTheory.localFactor_mod_p_nilOver :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : _root_.ReciprocityTheory.PGsh.BX R₀} {Tw : _root_.ReciprocityTheory.PGsh.ATowerL R₀ p} {Dt : _root_.ReciprocityTheory.PGsh.DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : _root_.ReciprocityTheory.PGsh.Be2.Dat p g B Tw Dt Oe σ cp), 0 < g → maximalIdeal (D.K : Type) = ⊥ ∧ _root_.ReciprocityTheory.PGsh.Be2.IsNilOver D.wd.ρ1 ∧ ∀ i : D.fin.ι,
    ∃ (Λ : _root_.ReciprocityTheory.PGsh.LAlg R₀) (μ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx i) Λ) (j : _root_.ReciprocityTheory.PGsh.LHom (Tw.R 0) Λ) (ρΛ : _root_.ReciprocityTheory.PGsh.LHom Λ D.K),
      _root_.ReciprocityTheory.PGsh.Be2.IsNilOver ρΛ ∧ Function.Surjective μ.1 ∧ ρΛ.comp j = D.wd.ρ1 ∧ μ.comp (D.fin.sO i) = j.comp (Tw.q 0) ∧
      ∀ φ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx i) Tw.O, φ.comp (D.fin.sO i) = _root_.ReciprocityTheory.PGsh.LHom.id Tw.O →
        ∃ ψ : _root_.ReciprocityTheory.PGsh.LHom Λ (Tw.R 0), ψ.comp μ = (Tw.q 0).comp φ ∧ ψ.comp j = _root_.ReciprocityTheory.PGsh.LHom.id (Tw.R 0) ∧ D.wd.ρ1.comp ψ = ρΛ) := by
  intro R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D hg
  have hid : _root_.ReciprocityTheory.PGsh.Be2.IsNilOver (_root_.ReciprocityTheory.PGsh.LHom.id D.K) :=
    ⟨fun x => ⟨x, rfl⟩, fun a ha => ⟨1, by rw [pow_one]; exact (RingHom.mem_ker).1 ha⟩⟩
  have hK : maximalIdeal (D.K : Type) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have hsub : ∀ u v : {x // (B.map (_root_.ReciprocityTheory.PGsh.LHom.id D.K)) x = 0}, u = v := by
      intro u v
      have hu := u.2
      have hv := v.2
      rw [B.map_id] at hu hv
      exact Subtype.ext (hu.trans hv.symm)
    have h1 : (fun _ : Fin g => (⟨a, ha⟩ : maximalIdeal (D.K : Type))) = fun _ => 0 :=
      (D.ch.χ (_root_.ReciprocityTheory.PGsh.LHom.id D.K) hid).symm.injective (hsub _ _)
    have h2 := congrFun h1 ⟨0, hg⟩
    exact (Ideal.mem_bot).2 (congrArg Subtype.val h2)
  have hW := D.sm.nil
  have heq := D.wd.ρW_eq
  have hρ1 : _root_.ReciprocityTheory.PGsh.Be2.IsNilOver D.wd.ρ1 := by
    refine ⟨fun k => ?_, fun a ha => ?_⟩
    · obtain ⟨w, hw⟩ := hW.1 k
      refine ⟨D.wd.πW.1 w, ?_⟩
      rw [← hw, ← heq]
      rfl
    · obtain ⟨w, rfl⟩ := D.wd.πW_surj a
      have hw : w ∈ RingHom.ker (D.wd.ρW.1 : D.wd.W.carrier →+* D.K.carrier) := by
        rw [RingHom.mem_ker, ← heq]
        exact (RingHom.mem_ker).1 ha
      exact (hW.2 w hw).map (D.wd.πW.1 : D.wd.W.carrier →+* (Tw.R 0).carrier)
  refine ⟨hK, hρ1, fun i => ?_⟩
  have hsec : ∃ φ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx i) Tw.O, φ.comp (D.fin.sO i) = _root_.ReciprocityTheory.PGsh.LHom.id Tw.O := by
    by_contra hne
    push_neg at hne
    have h1 : (1 : (D.fin.AAx i).carrier) = 0 := D.fin.sep i 1 fun φ hφ => absurd hφ (hne φ)
    exact one_ne_zero h1
  obtain ⟨φ₀, hφ₀⟩ := hsec
  have hfin : ((D.fin.sO i).1 : Tw.O.carrier →+* (D.fin.AAx i).carrier).Finite := by
    letI : Algebra Tw.O.carrier (D.fin.AAx i).carrier :=
      ((D.fin.sO i).1 : Tw.O.carrier →+* (D.fin.AAx i).carrier).toAlgebra
    exact (D.fin.free i).2
  exact exists_localFactor_lemma (Tw.q 0) D.tower_zero_surjective (p : Tw.O.carrier) D.tower_zero_ker D.wd.ρ1 hρ1 hK
    (D.fin.sO i) hfin φ₀ hφ₀

end GlobalTheory
