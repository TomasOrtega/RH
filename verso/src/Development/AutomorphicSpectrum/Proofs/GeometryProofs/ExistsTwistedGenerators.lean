import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Twist

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type} {x : κ → Ω}

abbrev chartR (x : κ → Ω) (c : κ) : Subalgebra ℤ Ω := Algebra.adjoin ℤ (Set.range fun j => x j / x c)

/- English proof (translation)
Take `⟨s, rfl⟩` from `h.bij.2 a`. Use `⟨s, ?_⟩` and prove the remaining obligations. Simplify using `only [genMap, TopCat.Presheaf.stalkSpecializes_refl]`. Both sides reduce to the same expression.
-/
theorem regAt_gen (h : IsCptGen ξ) (a : Ω) : a ∈ regAt ξ ⟨genPt ξ, specializes_rfl⟩ := by
  obtain ⟨s, rfl⟩ := h.bij.2 a
  refine ⟨s, ?_⟩
  simp only [genMap, TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hu`. Take `⟨u, hu⟩` from `hu`. Establish `e1 : θ r * genMap ξ q (u⁻¹ : (X.presheaf.stalk q.1)ˣ).1 = 1`. Rewrite using `[← hθ q hq r, ← hu, ← map_mul, Units.mul_inv, map_one]`.

Establish `e0 : θ r ≠ 0` using `left_ne_zero_of_mul_eq_one e1`. Conclude with `⟨e0, ⟨_, hθ q hq r⟩, ⟨_, eq_inv_of_mul_eq_one_right e1⟩⟩`. Introduce and unpack `⟨h0, -, ⟨y, hy⟩⟩`. Use `IsUnit.of_mul_eq_one y (h.inj q ?_)` and prove the remaining obligations. Rewrite using `[map_mul, hθ q hq r, hy, map_one, mul_inv_cancel₀ h0]`.
-/
theorem isUnit_germ_iff (h : IsCptGen ξ) {U : X.Opens} (θ : Γ(X, U) →+* Ω)
    (hθ : ∀ (q : Cpt ξ) (hq : q.1 ∈ U) (r : Γ(X, U)), genMap ξ q ((X.presheaf.germ U q.1 hq).hom r) = θ r)
    (q : Cpt ξ) (hq : q.1 ∈ U) (r : Γ(X, U)) :
    IsUnit ((X.presheaf.germ U q.1 hq).hom r) ↔ unitAt ξ q (θ r) := by
  constructor
  · intro hu
    obtain ⟨u, hu⟩ := hu
    have e1 : θ r * genMap ξ q (u⁻¹ : (X.presheaf.stalk q.1)ˣ).1 = 1 := by
      rw [← hθ q hq r, ← hu, ← map_mul, Units.mul_inv, map_one]
    have e0 : θ r ≠ 0 := left_ne_zero_of_mul_eq_one e1
    exact ⟨e0, ⟨_, hθ q hq r⟩, ⟨_, eq_inv_of_mul_eq_one_right e1⟩⟩
  · rintro ⟨h0, -, ⟨y, hy⟩⟩
    refine IsUnit.of_mul_eq_one y (h.inj q ?_)
    rw [map_mul, hθ q hq r, hy, map_one, mul_inv_cancel₀ h0]

/- English proof (translation)
Use `letI := X.presheaf.algebra_section_stalk (⟨q.1, hq⟩ : U)`. Establish `hl` using `hU.isLocalization_stalk ⟨q.1, hq⟩`. Prove the components needed by the constructor for the conclusion. Introduce `r`. Rewrite using `[← isUnit_germ_iff h θ hθ q hq r]`.

Use `IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk q.1) (hU.primeIdealOf ⟨q.1, hq⟩).asIdeal r` as an intermediate fact. Establish `e : IsUnit ((X.presheaf.germ U q.1 hq).hom r) ↔ r ∉ (hU.primeIdealOf ⟨q.1, hq⟩).asIdeal` using `this`. Conclude with `⟨fun a b => e.1 b a, fun a => by_contra fun b => a (e.2 b)⟩`. Introduce and unpack `g ⟨s, rfl⟩`. Take `⟨⟨r, t⟩, e⟩` from `IsLocalization.surj (hU.primeIdealOf ⟨q.1, hq⟩).asIdeal.primeCompl (S := X.presheaf.stalk q.1) s`.

Use `⟨r, t.1, t.2, ?_⟩` and prove the remaining obligations. Rewrite using `[← hθ q hq r, ← hθ q hq t.1, ← map_mul]`. Conclude with `congrArg _ e`.
-/
theorem prime_facts (h : IsCptGen ξ) {U : X.Opens} (hU : IsAffineOpen U) (θ : Γ(X, U) →+* Ω)
    (hθ : ∀ (q : Cpt ξ) (hq : q.1 ∈ U) (r : Γ(X, U)), genMap ξ q ((X.presheaf.germ U q.1 hq).hom r) = θ r)
    (q : Cpt ξ) (hq : q.1 ∈ U) :
    (∀ r, r ∈ (hU.primeIdealOf ⟨q.1, hq⟩).asIdeal ↔ ¬ unitAt ξ q (θ r)) ∧
    ∀ g ∈ regAt ξ q, ∃ u v, v ∉ (hU.primeIdealOf ⟨q.1, hq⟩).asIdeal ∧ g * θ v = θ u := by
  letI := X.presheaf.algebra_section_stalk (⟨q.1, hq⟩ : U)
  have hl := hU.isLocalization_stalk ⟨q.1, hq⟩
  constructor
  · intro r
    rw [← isUnit_germ_iff h θ hθ q hq r]
    have := IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk q.1)
      (hU.primeIdealOf ⟨q.1, hq⟩).asIdeal r
    have e : IsUnit ((X.presheaf.germ U q.1 hq).hom r) ↔ r ∉ (hU.primeIdealOf ⟨q.1, hq⟩).asIdeal := this
    exact ⟨fun a b => e.1 b a, fun a => by_contra fun b => a (e.2 b)⟩
  · rintro g ⟨s, rfl⟩
    obtain ⟨⟨r, t⟩, e⟩ := IsLocalization.surj (hU.primeIdealOf ⟨q.1, hq⟩).asIdeal.primeCompl
      (S := X.presheaf.stalk q.1) s
    refine ⟨r, t.1, t.2, ?_⟩
    rw [← hθ q hq r, ← hθ q hq t.1, ← map_mul]
    exact congrArg _ e

/- English proof (translation)
Establish `hy : hU.fromSpec P ∈ U`. Establish `: hU.fromSpec P ∈ Set.range hU.fromSpec` using `⟨P, rfl⟩`. Rewrite `this` using `[hU.range_fromSpec]`. Then use the resulting hypothesis. Use `⟨_, hy, ?_⟩` and prove the remaining obligations. Apply `hU.fromSpec.isOpenEmbedding.injective` to reduce the goal to its premises.

Conclude with `hU.fromSpec_primeIdealOf ⟨_, hy⟩`.
-/
theorem prime_point {U : X.Opens} (hU : IsAffineOpen U) (P : PrimeSpectrum Γ(X, U)) :
    ∃ (y : X) (hy : y ∈ U), hU.primeIdealOf ⟨y, hy⟩ = P := by
  have hy : hU.fromSpec P ∈ U := by
    have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
    rwa [hU.range_fromSpec] at this
  refine ⟨_, hy, ?_⟩
  apply hU.fromSpec.isOpenEmbedding.injective
  exact hU.fromSpec_primeIdealOf ⟨_, hy⟩

/- English proof (translation)
Take `⟨U, hU, hq⟩` from `h.affine c hc`. Establish `h0 : genPt ξ ∈ U` using `(hq _).2 ⟨specializes_rfl, hc, fun c' => regAt_gen h.gen _⟩`. Set `θ : Γ(X, U) →+* Ω` to `(Scheme.stalkClosedPointTo ξ).hom.comp (X.presheaf.germ U (genPt ξ) h0).hom`. Establish `hθ : ∀ (q : Cpt ξ) (hq : q.1 ∈ U) (r : Γ(X, U)), genMap ξ q ((X.presheaf.germ U q.1 hq).hom r) = θ r`. Introduce `q hqU r`.

Use `show (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.stalkSpecializes q.2 (X.presheaf.germ U q.1 hqU r)) = (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.germ U (genPt ξ) h0).hom r)`. Conclude with `congrArg (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ_stalkSpecializes_apply hqU q.2 r)`. Establish `hin : ∀ q : Cpt ξ, InChart ξ x c q → q.1 ∈ U` using `fun q hqc => (hq _).2 ⟨q.2, hqc⟩`. Use `⟨U, hU, θ, hq, hθ, fun r => ?_, fun a ha => ?_⟩` and prove the remaining obligations. Rewrite using `[h.ring c hc]`.

Introduce `q hqc`. Conclude with `⟨_, hθ q (hin q hqc) r⟩`. Establish `hreg` using `(h.ring c hc a).1 ha`. Set `J : Ideal Γ(X, U)` to `{ carrier := {d | ∃ r, θ d * a = θ r} add_mem' := by`. Introduce and unpack `d d' ⟨r, hr⟩ ⟨r', hr'⟩`.

Conclude with `⟨r + r', by rw [map_add, map_add, add_mul, hr, hr']⟩`. Use the proof step `zero_mem' := ⟨0, by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `t d ⟨r, hr⟩`. Conclude with `⟨t * r, by rw [smul_eq_mul, map_mul, map_mul, mul_assoc, hr]⟩ }`.

Establish `hJ : J = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨M, hM, hJM⟩` from `J.exists_le_maximal hne`. Take `⟨y, hy, e⟩` from `prime_point hU ⟨M, hM.isPrime⟩`. Take `⟨h', hcq⟩` from `(hq y).1 hy`.

Take `⟨u, v, hv, e'⟩` from `(prime_facts h.gen hU θ hθ ⟨y, h'⟩ hy).2 a (hreg _ hcq)`. Apply `hv` to reduce the goal to its premises. Establish `: v ∈ J` using `⟨u, by rw [mul_comm]; exact e'⟩`. Use `hJM this` as an intermediate fact. Simplify `this` using `[e]`.

Take `⟨r, hr⟩ : (1 : Γ(X, U)) ∈ J` from `hJ ▸ Submodule.mem_top`. Conclude with `⟨r, by rw [← hr, map_one, one_mul]⟩`.
-/
theorem chart_data (h : CoordTie ℤ ξ x) {c : κ} (hc : x c ≠ 0) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (θ : Γ(X, U) →+* Ω),
      (∀ q : X, q ∈ U ↔ ∃ h' : genPt ξ ⤳ q, InChart ξ x c ⟨q, h'⟩) ∧
      (∀ (q : Cpt ξ) (hq : q.1 ∈ U) (r : Γ(X, U)),
        genMap ξ q ((X.presheaf.germ U q.1 hq).hom r) = θ r) ∧
      (∀ r, θ r ∈ chartR x c) ∧ ∀ a ∈ chartR x c, ∃ r, θ r = a := by
  obtain ⟨U, hU, hq⟩ := h.affine c hc
  have h0 : genPt ξ ∈ U := (hq _).2 ⟨specializes_rfl, hc, fun c' => regAt_gen h.gen _⟩
  let θ : Γ(X, U) →+* Ω := (Scheme.stalkClosedPointTo ξ).hom.comp (X.presheaf.germ U (genPt ξ) h0).hom
  have hθ : ∀ (q : Cpt ξ) (hq : q.1 ∈ U) (r : Γ(X, U)),
      genMap ξ q ((X.presheaf.germ U q.1 hq).hom r) = θ r := by
    intro q hqU r
    show (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.stalkSpecializes q.2 (X.presheaf.germ U q.1 hqU r)) =
      (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.germ U (genPt ξ) h0).hom r)
    exact congrArg (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ_stalkSpecializes_apply hqU q.2 r)
  have hin : ∀ q : Cpt ξ, InChart ξ x c q → q.1 ∈ U := fun q hqc => (hq _).2 ⟨q.2, hqc⟩
  refine ⟨U, hU, θ, hq, hθ, fun r => ?_, fun a ha => ?_⟩
  · rw [h.ring c hc]
    intro q hqc
    exact ⟨_, hθ q (hin q hqc) r⟩
  · have hreg := (h.ring c hc a).1 ha
    let J : Ideal Γ(X, U) :=
      { carrier := {d | ∃ r, θ d * a = θ r}
        add_mem' := by
          rintro d d' ⟨r, hr⟩ ⟨r', hr'⟩
          exact ⟨r + r', by rw [map_add, map_add, add_mul, hr, hr']⟩
        zero_mem' := ⟨0, by simp⟩
        smul_mem' := by
          rintro t d ⟨r, hr⟩
          exact ⟨t * r, by rw [smul_eq_mul, map_mul, map_mul, mul_assoc, hr]⟩ }
    have hJ : J = ⊤ := by
      by_contra hne
      obtain ⟨M, hM, hJM⟩ := J.exists_le_maximal hne
      obtain ⟨y, hy, e⟩ := prime_point hU ⟨M, hM.isPrime⟩
      obtain ⟨h', hcq⟩ := (hq y).1 hy
      obtain ⟨u, v, hv, e'⟩ := (prime_facts h.gen hU θ hθ ⟨y, h'⟩ hy).2 a (hreg _ hcq)
      apply hv
      have : v ∈ J := ⟨u, by rw [mul_comm]; exact e'⟩
      have := hJM this
      simpa [e] using this
    obtain ⟨r, hr⟩ : (1 : Γ(X, U)) ∈ J := hJ ▸ Submodule.mem_top
    exact ⟨r, by rw [← hr, map_one, one_mul]⟩

/- English proof (translation)
The claim follows from `(h.ring c hc a).1 ha q hq`.
-/
theorem chartR_le (h : CoordTie ℤ ξ x) {c : κ} (hc : x c ≠ 0) {a : Ω} (ha : a ∈ chartR x c) {q : Cpt ξ}
    (hq : InChart ξ x c q) : a ∈ regAt ξ q := (h.ring c hc a).1 ha q hq

/- English proof (translation)
Take `⟨U, hU, θ, hq, hθ, hr, hs⟩` from `chart_data h hc`. Set `θ' : Γ(X, U) →+* chartR x c` to `θ.codRestrict (chartR x c) hr`. Establish `hθ' : ∀ r, ((θ' r : chartR x c) : Ω) = θ r` using `fun r => rfl`. Use `haveI : (Q.comap θ').IsPrime := Ideal.comap_isPrime θ' Q`. Take `⟨y, hy, e⟩` from `prime_point hU ⟨Q.comap θ', inferInstance⟩`.

Take `⟨h', hcq⟩` from `(hq y).1 hy`. Take `⟨f1, f2⟩` from `prime_facts h.gen hU θ hθ ⟨y, h'⟩ hy`. Simplify using `only [e] at f1 f2`. Use `⟨⟨y, h'⟩, hcq, fun a => ?_, fun g hg => ?_⟩` and prove the remaining obligations. Take `⟨r, hra⟩` from `hs a a.2`.

Establish `: a = θ' r` using `Subtype.ext hra.symm`. Rewrite using `[this, hθ', ← f1 r]`. Both sides reduce to the same expression. Take `⟨u, v, hv, e'⟩` from `f2 g hg`. Conclude with `⟨θ' u, θ' v, hv, e'⟩`.
-/
theorem chart_prime (h : CoordTie ℤ ξ x) {c : κ} (hc : x c ≠ 0) (Q : Ideal (chartR x c)) (hQ : Q.IsPrime) :
    ∃ q : Cpt ξ, InChart ξ x c q ∧ (∀ a : chartR x c, a ∈ Q ↔ ¬ unitAt ξ q (a : Ω)) ∧
      ∀ g ∈ regAt ξ q, ∃ u v : chartR x c, v ∉ Q ∧ g * (v : Ω) = u := by
  obtain ⟨U, hU, θ, hq, hθ, hr, hs⟩ := chart_data h hc
  let θ' : Γ(X, U) →+* chartR x c := θ.codRestrict (chartR x c) hr
  have hθ' : ∀ r, ((θ' r : chartR x c) : Ω) = θ r := fun r => rfl
  haveI : (Q.comap θ').IsPrime := Ideal.comap_isPrime θ' Q
  obtain ⟨y, hy, e⟩ := prime_point hU ⟨Q.comap θ', inferInstance⟩
  obtain ⟨h', hcq⟩ := (hq y).1 hy
  obtain ⟨f1, f2⟩ := prime_facts h.gen hU θ hθ ⟨y, h'⟩ hy
  simp only [e] at f1 f2
  refine ⟨⟨y, h'⟩, hcq, fun a => ?_, fun g hg => ?_⟩
  · obtain ⟨r, hra⟩ := hs a a.2
    have : a = θ' r := Subtype.ext hra.symm
    rw [this, hθ', ← f1 r]
    rfl
  · obtain ⟨u, v, hv, e'⟩ := f2 g hg
    exact ⟨θ' u, θ' v, hv, e'⟩

/- English proof (translation)
Take `⟨U, hU, θ, hq, hθ, hr, hs⟩` from `chart_data h hc`. Set `θ' : Γ(X, U) →+* chartR x c` to `θ.codRestrict (chartR x c) hr`. Establish `hθ' : ∀ r, ((θ' r : chartR x c) : Ω) = θ r` using `fun r => rfl`. Establish `hsurj : Function.Surjective θ'` using `fun a => by`. Take `⟨r, hra⟩` from `hs a a.2`.

Conclude with `⟨r, Subtype.ext hra⟩`. Establish `hqU : q.1 ∈ U` using `(hq _).2 ⟨q.2, hqc⟩`. Take `⟨f1, -⟩` from `prime_facts h.gen hU θ hθ q hqU`. Establish `hker : RingHom.ker θ' ≤ (hU.primeIdealOf ⟨q.1, hqU⟩).asIdeal` using `fun z hz => by`. Rewrite using `[f1]`.

Introduce and unpack `⟨h0, -⟩`. Conclude with `h0 (congrArg Subtype.val ((RingHom.mem_ker).1 hz))`. Use `⟨_, Ideal.map_isPrime_of_surjective hsurj hker, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.mem_map_iff_of_surjective θ' hsurj]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨r, hr', rfl⟩`. Rewrite using `[hθ', ← f1 r]`. Conclude with `hr'`. Introduce `ha`. Take `⟨r, rfl⟩` from `hsurj a`.

Rewrite `ha` using `[hθ', ← f1 r]`. Conclude with `⟨r, ha, rfl⟩`.
-/
theorem chart_point (h : CoordTie ℤ ξ x) {c : κ} (hc : x c ≠ 0) (q : Cpt ξ) (hqc : InChart ξ x c q) :
    ∃ Q : Ideal (chartR x c), Q.IsPrime ∧ ∀ a : chartR x c, a ∈ Q ↔ ¬ unitAt ξ q (a : Ω) := by
  obtain ⟨U, hU, θ, hq, hθ, hr, hs⟩ := chart_data h hc
  let θ' : Γ(X, U) →+* chartR x c := θ.codRestrict (chartR x c) hr
  have hθ' : ∀ r, ((θ' r : chartR x c) : Ω) = θ r := fun r => rfl
  have hsurj : Function.Surjective θ' := fun a => by
    obtain ⟨r, hra⟩ := hs a a.2
    exact ⟨r, Subtype.ext hra⟩
  have hqU : q.1 ∈ U := (hq _).2 ⟨q.2, hqc⟩
  obtain ⟨f1, -⟩ := prime_facts h.gen hU θ hθ q hqU
  have hker : RingHom.ker θ' ≤ (hU.primeIdealOf ⟨q.1, hqU⟩).asIdeal := fun z hz => by
    rw [f1]
    rintro ⟨h0, -⟩
    exact h0 (congrArg Subtype.val ((RingHom.mem_ker).1 hz))
  refine ⟨_, Ideal.map_isPrime_of_surjective hsurj hker, fun a => ?_⟩
  rw [Ideal.mem_map_iff_of_surjective θ' hsurj]
  constructor
  · rintro ⟨r, hr', rfl⟩
    rw [hθ', ← f1 r]
    exact hr'
  · intro ha
    obtain ⟨r, rfl⟩ := hsurj a
    rw [hθ', ← f1 r] at ha
    exact ⟨r, ha, rfl⟩

/- English proof (translation)
Take `⟨U, hU, θ, hq, hθ, hr, hs⟩` from `chart_data h hc`. Establish `hqU : q.1 ∈ U` using `(hq _).2 ⟨q.2, hqc⟩`. Take `⟨f, hfW, hqf⟩` from `hU.exists_basicOpen_le (V := W) ⟨q.1, hW⟩ hqU`. Use `⟨⟨θ f, hr f⟩, ?_, fun q' hq' hu => ?_⟩` and prove the remaining obligations. Conclude with `(isUnit_germ_iff h.gen θ hθ q hqU f).1 ((X.mem_basicOpen f q.1 hqU).1 hqf)`.

Establish `hqU' : q'.1 ∈ U` using `(hq _).2 ⟨q'.2, hq'⟩`. Conclude with `hfW ((X.mem_basicOpen f q'.1 hqU').2 ((isUnit_germ_iff h.gen θ hθ q' hqU' f).2 hu))`.
-/
theorem chart_nbhd (h : CoordTie ℤ ξ x) {c : κ} (hc : x c ≠ 0) (q : Cpt ξ) (hqc : InChart ξ x c q)
    (W : X.Opens) (hW : q.1 ∈ W) :
    ∃ s : chartR x c, unitAt ξ q (s : Ω) ∧ ∀ q' : Cpt ξ, InChart ξ x c q' → unitAt ξ q' (s : Ω) → q'.1 ∈ W := by
  obtain ⟨U, hU, θ, hq, hθ, hr, hs⟩ := chart_data h hc
  have hqU : q.1 ∈ U := (hq _).2 ⟨q.2, hqc⟩
  obtain ⟨f, hfW, hqf⟩ := hU.exists_basicOpen_le (V := W) ⟨q.1, hW⟩ hqU
  refine ⟨⟨θ f, hr f⟩, ?_, fun q' hq' hu => ?_⟩
  · exact (isUnit_germ_iff h.gen θ hθ q hqU f).1 ((X.mem_basicOpen f q.1 hqU).1 hqf)
  · have hqU' : q'.1 ∈ U := (hq _).2 ⟨q'.2, hq'⟩
    exact hfW ((X.mem_basicOpen f q'.1 hqU').2 ((isUnit_germ_iff h.gen θ hθ q' hqU' f).2 hu))

/- English proof (translation)
Set `J : Ideal (chartR x c)` to `{ carrier := {d | ∃ N : ℕ, (s : Ω) ^ N * ((d : Ω) * g) ∈ chartR x c} add_mem' := by`. Introduce and unpack `d d' ⟨N, hN⟩ ⟨N', hN'⟩`. Use `⟨N + N', ?_⟩` and prove the remaining obligations. Establish `e : (s : Ω) ^ (N + N') * (((d + d' : chartR x c) : Ω) * g) = (s : Ω) ^ N' * ((s : Ω) ^ N * ((d : Ω) * g)) + (s : Ω) ^ N * ((s : Ω) ^ N' * ((d' : Ω) * g))`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `add_mem (mul_mem (pow_mem s.2 _) hN) (mul_mem (pow_mem s.2 _) hN')`. Use the proof step `zero_mem' := ⟨0, by simp⟩`. Use the proof step `smul_mem' := by`.

Introduce and unpack `t d ⟨N, hN⟩`. Use `⟨N, ?_⟩` and prove the remaining obligations. Establish `e : (s : Ω) ^ N * (((t • d : chartR x c) : Ω) * g) = (t : Ω) * ((s : Ω) ^ N * ((d : Ω) * g))`. Rewrite using `[smul_eq_mul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `mul_mem t.2 hN }`. Establish `hrad : s ∈ J.radical`. Rewrite using `[Ideal.radical_eq_sInf, Ideal.mem_sInf]`.

Introduce and unpack `Q ⟨hJQ, hQ⟩`. Assume the negation of the conclusion as `hsQ`. Take `⟨q, hqc, f1, f2⟩` from `chart_prime h hc Q hQ`. Establish `hu : unitAt ξ q (s : Ω)`. Assume the negation of the conclusion as `hn`.

Conclude with `hsQ ((f1 s).2 hn)`. Take `⟨u, v, hv, e⟩` from `f2 g (hg q hqc hu)`. Apply `hv` to reduce the goal to its premises. Apply `hJQ` to reduce the goal to its premises. Use `⟨0, ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_zero, one_mul, mul_comm, e]`. Conclude with `u.2`. Take `⟨M, N, hN⟩` from `hrad`. Use `⟨N + M, ?_⟩` and prove the remaining obligations. Establish `e : (s : Ω) ^ (N + M) * g = (s : Ω) ^ N * ((((s ^ M : chartR x c)) : Ω) * g)`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `hN`.
-/
theorem chart_denom (h : CoordTie ℤ ξ x) {c : κ} (hc : x c ≠ 0) (s : chartR x c) (g : Ω)
    (hg : ∀ q : Cpt ξ, InChart ξ x c q → unitAt ξ q (s : Ω) → g ∈ regAt ξ q) :
    ∃ N : ℕ, (s : Ω) ^ N * g ∈ chartR x c := by
  let J : Ideal (chartR x c) :=
    { carrier := {d | ∃ N : ℕ, (s : Ω) ^ N * ((d : Ω) * g) ∈ chartR x c}
      add_mem' := by
        rintro d d' ⟨N, hN⟩ ⟨N', hN'⟩
        refine ⟨N + N', ?_⟩
        have e : (s : Ω) ^ (N + N') * (((d + d' : chartR x c) : Ω) * g) =
            (s : Ω) ^ N' * ((s : Ω) ^ N * ((d : Ω) * g)) + (s : Ω) ^ N * ((s : Ω) ^ N' * ((d' : Ω) * g)) := by
          push_cast
          ring
        rw [e]
        exact add_mem (mul_mem (pow_mem s.2 _) hN) (mul_mem (pow_mem s.2 _) hN')
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro t d ⟨N, hN⟩
        refine ⟨N, ?_⟩
        have e : (s : Ω) ^ N * (((t • d : chartR x c) : Ω) * g) = (t : Ω) * ((s : Ω) ^ N * ((d : Ω) * g)) := by
          rw [smul_eq_mul]
          push_cast
          ring
        rw [e]
        exact mul_mem t.2 hN }
  have hrad : s ∈ J.radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro Q ⟨hJQ, hQ⟩
    by_contra hsQ
    obtain ⟨q, hqc, f1, f2⟩ := chart_prime h hc Q hQ
    have hu : unitAt ξ q (s : Ω) := by
      by_contra hn
      exact hsQ ((f1 s).2 hn)
    obtain ⟨u, v, hv, e⟩ := f2 g (hg q hqc hu)
    apply hv
    apply hJQ
    refine ⟨0, ?_⟩
    rw [pow_zero, one_mul, mul_comm, e]
    exact u.2
  obtain ⟨M, N, hN⟩ := hrad
  refine ⟨N + M, ?_⟩
  have e : (s : Ω) ^ (N + M) * g = (s : Ω) ^ N * ((((s ^ M : chartR x c)) : Ω) * g) := by
    push_cast
    ring
  rw [e]
  exact hN

variable {E : Type} [AddCommGroup E] [Module Ω E]

/- English proof (translation)
Set `G : Set (chartR x c)` to `{s | ∃ b : Fin r → E, LinearIndependent Ω b ∧ ∀ q : Cpt ξ, InChart ξ x c q → unitAt ξ q (s : Ω) → L.IsFrameAt b q}`. Establish `hG : Ideal.span G = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨M, hM, hGM⟩` from `(Ideal.span G).exists_le_maximal hne`. Take `⟨q, hqc, f1, -⟩` from `chart_prime h hc M hM.isPrime`.

Take `⟨W, hW, b, -, hb⟩` from `hL q (Set.mem_univ _)`. Take `⟨s, hs, hsW⟩` from `chart_nbhd h hc q hqc W hW`. Establish `hsG : s ∈ G` using `⟨b, (hb q (Set.mem_univ _) hW).1, fun q' hq' hu => hb q' (Set.mem_univ _) (hsW q' hq' hu)⟩`. Conclude with `(f1 s).1 (hGM (Ideal.subset_span hsG)) hs`. Take `⟨S, hSG, hS⟩` from `(Ideal.span_eq_top_iff_finite G).1 hG`.

Use `⟨S, fun q hqc => ?_, fun s hs => hSG hs⟩` and prove the remaining obligations. Take `⟨Q, hQ, f⟩` from `chart_point h hc q hqc`. Assume the negation of the conclusion as `hn`. Use `push_neg at hn`. Establish `: Ideal.span (S : Set (chartR x c)) ≤ Q` using `Ideal.span_le.2 fun s hs => (f s).2 (hn s hs)`.

Rewrite `this` using `[hS]`. Conclude with `hQ.ne_top (top_le_iff.1 this)`.
-/
theorem frame_cover (h : CoordTie ℤ ξ x) {L : Lat ξ E} {r : ℕ} {V : Submodule Ω E} (hL : L.IsVB r V)
    {c : κ} (hc : x c ≠ 0) :
    ∃ S : Finset (chartR x c), (∀ q : Cpt ξ, InChart ξ x c q → ∃ s ∈ S, unitAt ξ q (s : Ω)) ∧
      ∀ s ∈ S, ∃ b : Fin r → E, LinearIndependent Ω b ∧
        ∀ q : Cpt ξ, InChart ξ x c q → unitAt ξ q (s : Ω) → L.IsFrameAt b q := by
  classical
  let G : Set (chartR x c) := {s | ∃ b : Fin r → E, LinearIndependent Ω b ∧
    ∀ q : Cpt ξ, InChart ξ x c q → unitAt ξ q (s : Ω) → L.IsFrameAt b q}
  have hG : Ideal.span G = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hGM⟩ := (Ideal.span G).exists_le_maximal hne
    obtain ⟨q, hqc, f1, -⟩ := chart_prime h hc M hM.isPrime
    obtain ⟨W, hW, b, -, hb⟩ := hL q (Set.mem_univ _)
    obtain ⟨s, hs, hsW⟩ := chart_nbhd h hc q hqc W hW
    have hsG : s ∈ G := ⟨b, (hb q (Set.mem_univ _) hW).1,
      fun q' hq' hu => hb q' (Set.mem_univ _) (hsW q' hq' hu)⟩
    exact (f1 s).1 (hGM (Ideal.subset_span hsG)) hs
  obtain ⟨S, hSG, hS⟩ := (Ideal.span_eq_top_iff_finite G).1 hG
  refine ⟨S, fun q hqc => ?_, fun s hs => hSG hs⟩
  obtain ⟨Q, hQ, f⟩ := chart_point h hc q hqc
  by_contra hn
  push_neg at hn
  have : Ideal.span (S : Set (chartR x c)) ≤ Q := Ideal.span_le.2 fun s hs => (f s).2 (hn s hs)
  rw [hS] at this
  exact hQ.ne_top (top_le_iff.1 this)

def IsSec (x : κ → Ω) (d : ℕ) (t : Ω) : Prop := ∀ c', x c' ≠ 0 → t / x c' ^ d ∈ chartR x c'

/- English proof (translation)
Introduce `c' _` and use `by rw [pow_one] exact Algebra.subset_adjoin ⟨j, rfl⟩`.
-/
theorem isSec_one_apply (j : κ) : IsSec x 1 (x j) := fun c' _ => by
  rw [pow_one]
  exact Algebra.subset_adjoin ⟨j, rfl⟩

/- English proof (translation)
Introduce `c' hc'` and use `by have : t * u / x c' ^ (d + e) = t / x c' ^ d * (u / x c' ^ e) := by rw [pow_add] field_simp rw [this] exact mul_mem (ht c' hc') (hu c' hc')`.
-/
theorem IsSec.mul {d e : ℕ} {t u : Ω} (ht : IsSec x d t) (hu : IsSec x e u) : IsSec x (d + e) (t * u) := fun c' hc' => by
  have : t * u / x c' ^ (d + e) = t / x c' ^ d * (u / x c' ^ e) := by
    rw [pow_add]
    field_simp
  rw [this]
  exact mul_mem (ht c' hc') (hu c' hc')

/- English proof (translation)
Introduce `c' hc'` and use `by rw [add_div] exact add_mem (ht c' hc') (hu c' hc')`.
-/
theorem IsSec.add {d : ℕ} {t u : Ω} (ht : IsSec x d t) (hu : IsSec x d u) : IsSec x d (t + u) := fun c' hc' => by
  rw [add_div]
  exact add_mem (ht c' hc') (hu c' hc')

/- English proof (translation)
Proceed by induction on `e with`. Consider the case `zero`. Introduce `c' _`. Simplify using the standard rewrite rules. Consider the case `succ e ih`.

Rewrite using `[pow_succ]`. Conclude with `ih.mul (isSec_one_apply j)`.
-/
theorem isSec_pow (j : κ) (e : ℕ) : IsSec x e (x j ^ e) := by
  induction e with
  | zero =>
    intro c' _
    simp
  | succ e ih =>
    rw [pow_succ]
    exact ih.mul (isSec_one_apply j)

/- English proof (translation)
Establish `key : ∃ d, IsSec x d (s * x c ^ d)`. Proceed by induction on `hs using Algebra.adjoin_induction with`. Consider the case `mem y hy`. Take `⟨j, rfl⟩` from `hy`. Use `⟨1, ?_⟩` and prove the remaining obligations.

Establish `: x j / x c * x c ^ 1 = x j`. Rewrite using `[pow_one]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Conclude with `isSec_one_apply j`.

Consider the case `algebraMap n`. Use `⟨0, fun c' _ => ?_⟩` and prove the remaining obligations. Simplify using `using (chartR x c').algebraMap_mem n`. Consider the case `add a b _ _ ha hb`. Take `⟨d, hd⟩` from `ha`.

Take `⟨e, he⟩` from `hb`. Use `⟨d + e, ?_⟩` and prove the remaining obligations. Establish `: (a + b) * x c ^ (d + e) = a * x c ^ d * x c ^ e + b * x c ^ e * x c ^ d` using `by ring`. Rewrite using `[this]`. Use `(hd.mul (isSec_pow c e)).add ?_` and prove the remaining obligations.

Rewrite using `[add_comm d e]`. Conclude with `he.mul (isSec_pow c d)`. Consider the case `mul a b _ _ ha hb`. Take `⟨d, hd⟩` from `ha`. Take `⟨e, he⟩` from `hb`.

Use `⟨d + e, ?_⟩` and prove the remaining obligations. Establish `: a * b * x c ^ (d + e) = a * x c ^ d * (b * x c ^ e)` using `by ring`. Rewrite using `[this]`. Conclude with `hd.mul he`. Take `⟨d, hd⟩` from `key`.

Use `⟨d, fun d' hd' => ?_⟩` and prove the remaining obligations. Take `⟨e, rfl⟩` from `Nat.exists_eq_add_of_le hd'`. Establish `: s * x c ^ (d + e) = s * x c ^ d * x c ^ e` using `by ring`. Rewrite using `[this]`. Conclude with `hd.mul (isSec_pow c e)`.
-/
theorem exists_isSec {c : κ} (hc : x c ≠ 0) {s : Ω} (hs : s ∈ chartR x c) :
    ∃ d, ∀ d', d ≤ d' → IsSec x d' (s * x c ^ d') := by
  have key : ∃ d, IsSec x d (s * x c ^ d) := by
    induction hs using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      refine ⟨1, ?_⟩
      have : x j / x c * x c ^ 1 = x j := by
        rw [pow_one]
        field_simp
      rw [this]
      exact isSec_one_apply j
    | algebraMap n =>
      refine ⟨0, fun c' _ => ?_⟩
      simpa using (chartR x c').algebraMap_mem n
    | add a b _ _ ha hb =>
      obtain ⟨d, hd⟩ := ha
      obtain ⟨e, he⟩ := hb
      refine ⟨d + e, ?_⟩
      have : (a + b) * x c ^ (d + e) = a * x c ^ d * x c ^ e + b * x c ^ e * x c ^ d := by ring
      rw [this]
      refine (hd.mul (isSec_pow c e)).add ?_
      rw [add_comm d e]
      exact he.mul (isSec_pow c d)
    | mul a b _ _ ha hb =>
      obtain ⟨d, hd⟩ := ha
      obtain ⟨e, he⟩ := hb
      refine ⟨d + e, ?_⟩
      have : a * b * x c ^ (d + e) = a * x c ^ d * (b * x c ^ e) := by ring
      rw [this]
      exact hd.mul he
  obtain ⟨d, hd⟩ := key
  refine ⟨d, fun d' hd' => ?_⟩
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hd'
  have : s * x c ^ (d + e) = s * x c ^ d * x c ^ e := by ring
  rw [this]
  exact hd.mul (isSec_pow c e)

/- English proof (translation)
Establish `hc'` using `hq.1`. Use `set y := x c / x c' with hy`. Establish `hyr : y ∈ regAt ξ q` using `hq.2 c`. Establish `hy0 : y ≠ 0` using `div_ne_zero hc hc'`. Establish `hz : s * x c ^ d / x c' ^ d ∈ regAt ξ q` using `chartR_le h hc' (hd c' hc') hq`.

Use `set z := s * x c ^ d / x c' ^ d with hzdef`. Establish `e1 : s * x c ^ (d + 1) / x c' ^ (d + 1) = z * y`. Rewrite using `[hzdef, hy]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite `hu` using `[e1]`. Take `⟨ha0, -, hai⟩` from `hu`. Establish `hyi : y⁻¹ ∈ regAt ξ q`. Establish `: y⁻¹ = z * (z * y)⁻¹`. Establish `hz0 : z ≠ 0` using `left_ne_zero_of_mul ha0`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Conclude with `mul_mem hz hai`. Establish `hch : InChart ξ x c q` using `⟨hc, fun j => by`. Establish `: x j / x c = x j / x c' * y⁻¹`.

Rewrite using `[hy]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Conclude with `mul_mem (hq.2 j) hyi⟩`. Use `⟨hch, ?_⟩` and prove the remaining obligations.

Establish `e2 : z * y = s * y ^ (d + 1)`. Rewrite using `[hzdef, hy, div_pow, pow_succ (x c), pow_succ (x c')]`. Clear the denominators using the available nonvanishing facts. Establish `hs0 : s ≠ 0`. Introduce `h0`.

Rewrite `ha0` using `[e2, h0, zero_mul]`. Conclude with `ha0 rfl`. Use `⟨hs0, chartR_le h hc hs hch, ?_⟩` and prove the remaining obligations. Establish `: s⁻¹ = (z * y)⁻¹ * y ^ (d + 1)`. Rewrite using `[e2]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Conclude with `mul_mem hai (pow_mem hyr _)`.
-/
theorem unit_chart (h : CoordTie ℤ ξ x) {c c' : κ} (hc : x c ≠ 0) {s : Ω} (hs : s ∈ chartR x c) {d : ℕ}
    (hd : IsSec x d (s * x c ^ d)) {q : Cpt ξ} (hq : InChart ξ x c' q)
    (hu : unitAt ξ q (s * x c ^ (d + 1) / x c' ^ (d + 1))) : InChart ξ x c q ∧ unitAt ξ q s := by
  have hc' := hq.1
  set y := x c / x c' with hy
  have hyr : y ∈ regAt ξ q := hq.2 c
  have hy0 : y ≠ 0 := div_ne_zero hc hc'
  have hz : s * x c ^ d / x c' ^ d ∈ regAt ξ q := chartR_le h hc' (hd c' hc') hq
  set z := s * x c ^ d / x c' ^ d with hzdef
  have e1 : s * x c ^ (d + 1) / x c' ^ (d + 1) = z * y := by
    rw [hzdef, hy]
    field_simp
    ring
  rw [e1] at hu
  obtain ⟨ha0, -, hai⟩ := hu
  have hyi : y⁻¹ ∈ regAt ξ q := by
    have : y⁻¹ = z * (z * y)⁻¹ := by
      have hz0 : z ≠ 0 := left_ne_zero_of_mul ha0
      field_simp
    rw [this]
    exact mul_mem hz hai
  have hch : InChart ξ x c q := ⟨hc, fun j => by
    have : x j / x c = x j / x c' * y⁻¹ := by
      rw [hy]
      field_simp
    rw [this]
    exact mul_mem (hq.2 j) hyi⟩
  refine ⟨hch, ?_⟩
  have e2 : z * y = s * y ^ (d + 1) := by
    rw [hzdef, hy, div_pow, pow_succ (x c), pow_succ (x c')]
    field_simp
  have hs0 : s ≠ 0 := by
    intro h0
    rw [e2, h0, zero_mul] at ha0
    exact ha0 rfl
  refine ⟨hs0, chartR_le h hc hs hch, ?_⟩
  have : s⁻¹ = (z * y)⁻¹ * y ^ (d + 1) := by
    rw [e2]
    field_simp
  rw [this]
  exact mul_mem hai (pow_mem hyr _)

/- English proof (translation)
Establish `: ∀ k : Fin r, ∃ g : Module.Dual Ω E, ∀ l, g (b l) = if k = l then 1 else 0` using `fun k => by`. Take `⟨g, hg⟩` from `LinearMap.exists_extend ((Finsupp.lapply k : (Fin r →₀ Ω) →ₗ[Ω] Ω) ∘ₗ hb.repr)`. Use `⟨g, fun l => ?_⟩` and prove the remaining obligations. Establish `hm : b l ∈ Submodule.span Ω (Set.range b)` using `Submodule.subset_span ⟨l, rfl⟩`. Use `LinearMap.congr_fun hg ⟨b l, hm⟩` as an intermediate fact.

Simplify using `only [LinearMap.comp_apply, Submodule.subtype_apply, Finsupp.lapply_apply] at this`. Rewrite using `[this, hb.repr_eq_single l ⟨b l, hm⟩ rfl, Finsupp.single_apply]`. Simplify using `[eq_comm]`. Use `choose β hβ using this`. Conclude with `⟨β, hβ⟩`.
-/
theorem exists_dual {r : ℕ} {b : Fin r → E} (hb : LinearIndependent Ω b) :
    ∃ β : Fin r → Module.Dual Ω E, ∀ k l, β k (b l) = if k = l then 1 else 0 := by
  classical
  have : ∀ k : Fin r, ∃ g : Module.Dual Ω E, ∀ l, g (b l) = if k = l then 1 else 0 := fun k => by
    obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Finsupp.lapply k : (Fin r →₀ Ω) →ₗ[Ω] Ω) ∘ₗ hb.repr)
    refine ⟨g, fun l => ?_⟩
    have hm : b l ∈ Submodule.span Ω (Set.range b) := Submodule.subset_span ⟨l, rfl⟩
    have := LinearMap.congr_fun hg ⟨b l, hm⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Finsupp.lapply_apply] at this
    rw [this, hb.repr_eq_single l ⟨b l, hm⟩ rfl, Finsupp.single_apply]
    simp [eq_comm]
  choose β hβ using this
  exact ⟨β, hβ⟩

/- English proof (translation)
Rewrite `he` using `[hb.2]`. Proceed by induction on `he using Submodule.span_induction with`. Consider the case `mem v hv`. Take `⟨l, rfl⟩` from `hv`. Use `⟨fun k => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hβ] split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`. Simplify using `[hβ]`. Consider the case `zero => simp [zero_mem]`.

Consider the case `add u v _ _ hu hv`. Use `⟨fun k => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add]`. Conclude with `add_mem (hu.1 k) (hv.1 k)`. Simplify using `only [map_add, add_smul, Finset.sum_add_distrib]`.

Rewrite using `[← hu.2, ← hv.2]`. Consider the case `smul a v _ hv`. Establish `e' : ∀ k, β k (a • v) = (a : Ω) * β k v` using `fun k => by show β k ((a : Ω) • v) = _`. Rewrite using `[map_smul, smul_eq_mul]`. Use `⟨fun k => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[e']`. Conclude with `mul_mem a.2 (hv.1 k)`. Simplify using `only [e', mul_smul]`. Rewrite using `[← Finset.smul_sum, ← hv.2]`. Both sides reduce to the same expression.
-/
theorem frame_coords {L : Lat ξ E} {r : ℕ} {b : Fin r → E} {q : Cpt ξ} (hb : L.IsFrameAt b q)
    {β : Fin r → Module.Dual Ω E} (hβ : ∀ k l, β k (b l) = if k = l then 1 else 0) {e : E} (he : e ∈ L q) :
    (∀ k, β k e ∈ regAt ξ q) ∧ e = ∑ k, β k e • b k := by
  rw [hb.2] at he
  induction he using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨l, rfl⟩ := hv
    refine ⟨fun k => ?_, ?_⟩
    · rw [hβ]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · simp [hβ]
  | zero => simp [zero_mem]
  | add u v _ _ hu hv =>
    refine ⟨fun k => ?_, ?_⟩
    · rw [map_add]
      exact add_mem (hu.1 k) (hv.1 k)
    · simp only [map_add, add_smul, Finset.sum_add_distrib]
      rw [← hu.2, ← hv.2]
  | smul a v _ hv =>
    have e' : ∀ k, β k (a • v) = (a : Ω) * β k v := fun k => by
      show β k ((a : Ω) • v) = _
      rw [map_smul, smul_eq_mul]
    refine ⟨fun k => ?_, ?_⟩
    · rw [e']
      exact mul_mem a.2 (hv.1 k)
    · simp only [e', mul_smul]
      rw [← Finset.smul_sum, ← hv.2]
      rfl

/- English proof (translation)
Establish `ha` using `hd' c' hc'`. Use `set a := s * x c ^ (d + 1) / x c' ^ (d + 1) with hadef`. Use `chart_denom h hc' (⟨a, ha⟩ * s') _ fun q hq hu => ?_` and prove the remaining obligations. Establish `hu' : unitAt ξ q (a * (s' : Ω))` using `hu`. Take `⟨h0, -, hi⟩` from `hu'`.

Establish `har : a ∈ regAt ξ q` using `chartR_le h hc' ha hq`. Establish `hsr : (s' : Ω) ∈ regAt ξ q` using `chartR_le h hc' s'.2 hq`. Establish `ha0 : a ≠ 0` using `left_ne_zero_of_mul h0`. Establish `hs0 : (s' : Ω) ≠ 0` using `right_ne_zero_of_mul h0`. Establish `hua : unitAt ξ q a` using `⟨ha0, har, by`.

Establish `: a⁻¹ = (s' : Ω) * (a * (s' : Ω))⁻¹` using `by field_simp`. Rewrite using `[this]`. Conclude with `mul_mem hsr hi⟩`. Establish `hus : unitAt ξ q (s' : Ω)` using `⟨hs0, hsr, by`. Establish `: (s' : Ω)⁻¹ = a * (a * (s' : Ω))⁻¹` using `by field_simp`.

Rewrite using `[this]`. Conclude with `mul_mem har hi⟩`. Take `⟨hq1, hq2⟩` from `unit_chart h hc hs hd hq hua`. Establish `hfr'` using `hb' q hq hus`. Establish `hmem : b' l ∈ L q`.

Rewrite using `[hfr'.2]`. Conclude with `Submodule.subset_span ⟨l, rfl⟩`. Conclude with `(frame_coords (hb q hq1 hq2) hβ hmem).1 k`.
-/
theorem compare (h : CoordTie ℤ ξ x) {L : Lat ξ E} {c c' : κ} (hc : x c ≠ 0) (hc' : x c' ≠ 0)
    {s : Ω} (hs : s ∈ chartR x c) (s' : chartR x c') {d : ℕ} (hd : IsSec x d (s * x c ^ d))
    (hd' : IsSec x (d + 1) (s * x c ^ (d + 1))) {r : ℕ} {b b' : Fin r → E}
    (hb : ∀ q : Cpt ξ, InChart ξ x c q → unitAt ξ q s → L.IsFrameAt b q)
    (hb' : ∀ q : Cpt ξ, InChart ξ x c' q → unitAt ξ q (s' : Ω) → L.IsFrameAt b' q)
    {β : Fin r → Module.Dual Ω E} (hβ : ∀ k l, β k (b l) = if k = l then 1 else 0) (k l : Fin r) :
    ∃ N : ℕ, (s * x c ^ (d + 1) / x c' ^ (d + 1) * (s' : Ω)) ^ N * β k (b' l) ∈ chartR x c' := by
  have ha := hd' c' hc'
  set a := s * x c ^ (d + 1) / x c' ^ (d + 1) with hadef
  refine chart_denom h hc' (⟨a, ha⟩ * s') _ fun q hq hu => ?_
  have hu' : unitAt ξ q (a * (s' : Ω)) := hu
  obtain ⟨h0, -, hi⟩ := hu'
  have har : a ∈ regAt ξ q := chartR_le h hc' ha hq
  have hsr : (s' : Ω) ∈ regAt ξ q := chartR_le h hc' s'.2 hq
  have ha0 : a ≠ 0 := left_ne_zero_of_mul h0
  have hs0 : (s' : Ω) ≠ 0 := right_ne_zero_of_mul h0
  have hua : unitAt ξ q a := ⟨ha0, har, by
    have : a⁻¹ = (s' : Ω) * (a * (s' : Ω))⁻¹ := by field_simp
    rw [this]
    exact mul_mem hsr hi⟩
  have hus : unitAt ξ q (s' : Ω) := ⟨hs0, hsr, by
    have : (s' : Ω)⁻¹ = a * (a * (s' : Ω))⁻¹ := by field_simp
    rw [this]
    exact mul_mem har hi⟩
  obtain ⟨hq1, hq2⟩ := unit_chart h hc hs hd hq hua
  have hfr' := hb' q hq hus
  have hmem : b' l ∈ L q := by
    rw [hfr'.2]
    exact Submodule.subset_span ⟨l, rfl⟩
  exact (frame_coords (hb q hq1 hq2) hβ hmem).1 k

/- English proof (translation)
Set `f : Fin (Fintype.card T) ≃ T` to `(Fintype.equivFin T).symm`. Use `⟨Fintype.card T, fun j => φ (f j), fun j p c hp e he => h1 _ p c hp e he, fun p c hp w hw => ?_⟩` and prove the remaining obligations. Take `⟨g, hg, hs⟩` from `h2 p c hp w hw`. Use `⟨fun j => g (f j), fun j => hg _, fun e he => ?_⟩` and prove the remaining obligations. Rewrite using `[hs e he]`.

Conclude with `(f.sum_comp fun t => g t * (φ t e / x c ^ m)).symm`.
-/
theorem twistGen_of_fintype {T : Type} [Fintype T] {L : Lat ξ E} {m : ℕ} (φ : T → Module.Dual Ω E)
    (h1 : ∀ t (p : Cpt ξ) c, InChart ξ x c p → ∀ e ∈ L p, φ t e / x c ^ m ∈ regAt ξ p)
    (h2 : ∀ (p : Cpt ξ) c, InChart ξ x c p → ∀ w : Module.Dual Ω E, (∀ e ∈ L p, w e ∈ regAt ξ p) →
      ∃ g : T → Ω, (∀ t, g t ∈ regAt ξ p) ∧ ∀ e ∈ L p, w e = ∑ t, g t * (φ t e / x c ^ m)) :
    ∃ (n : ℕ) (φ' : Fin n → Module.Dual Ω E), IsTwistGen ξ x L m φ' := by
  let f : Fin (Fintype.card T) ≃ T := (Fintype.equivFin T).symm
  refine ⟨Fintype.card T, fun j => φ (f j), fun j p c hp e he => h1 _ p c hp e he, fun p c hp w hw => ?_⟩
  obtain ⟨g, hg, hs⟩ := h2 p c hp w hw
  refine ⟨fun j => g (f j), fun j => hg _, fun e he => ?_⟩
  rw [hs e he]
  exact (f.sum_comp fun t => g t * (φ t e / x c ^ m)).symm

/- English proof (translation)
Take `⟨e, rfl⟩` from `Nat.exists_eq_add_of_le hNM`. Establish `: A ^ (N + e) * g = A ^ e * (s⁻¹ ^ N * ((A * s) ^ N * g))`. Rewrite using `[pow_add, mul_pow, inv_pow]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`.

Conclude with `mul_mem (pow_mem hA _) (mul_mem (pow_mem hs _) hm)`.
-/
theorem power_step {R : Subring Ω} {A s g : Ω} (hA : A ∈ R) (hs0 : s ≠ 0) (hs : s⁻¹ ∈ R) {N M : ℕ} (hNM : N ≤ M)
    (hm : (A * s) ^ N * g ∈ R) : A ^ M * g ∈ R := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hNM
  have : A ^ (N + e) * g = A ^ e * (s⁻¹ ^ N * ((A * s) ^ N * g)) := by
    rw [pow_add, mul_pow, inv_pow]
    field_simp
  rw [this]
  exact mul_mem (pow_mem hA _) (mul_mem (pow_mem hs _) hm)

/- English proof (translation)
Rewrite using `[LinearMap.smul_apply, smul_eq_mul, div_pow, pow_mul y]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem twist_eval (a x₀ y : Ω) (d M : ℕ) (β : Module.Dual Ω E) (e : E) :
    ((a * x₀ ^ (d + 1)) ^ M • β) e / y ^ ((d + 1) * M) = (a * x₀ ^ (d + 1) / y ^ (d + 1)) ^ M * β e := by
  rw [LinearMap.smul_apply, smul_eq_mul, div_pow, pow_mul y]
  ring

/- English proof (translation)
Introduce `X Ω _ ξ E _ _ κ _ x L r V hT _ hL`. Set `C` to `{c : κ // x c ≠ 0}`. Establish `hcov` using `fun c : C => frame_cover hT hL c.2`. Use `choose S hS1 hS2 using hcov`. Set `I` to `Σ c : C, {s // s ∈ S c}`.

Use `letI : Fintype I := Fintype.ofFinite I`. Set `ci : I → κ` to `fun i => i.1.1`. Establish `hci : ∀ i, x (ci i) ≠ 0` using `fun i => i.1.2`. Set `σ : ∀ i : I, chartR x (ci i)` to `fun i => i.2.1`. Establish `hF` using `fun i : I => hS2 i.1 i.2.1 i.2.2`.

Use `choose b hbl hbf using hF`. Use `choose β hβ using fun i => exists_dual (hbl i)`. Establish `hsec` using `fun i : I => exists_isSec (hci i) (σ i).2`. Use `choose d0 hd0 using hsec`. Set `d` to `Finset.univ.sup d0`.

Establish `hdle : ∀ i, d0 i ≤ d` using `fun i => Finset.le_sup (Finset.mem_univ i)`. Establish `hd : ∀ i, IsSec x d ((σ i : Ω) * x (ci i) ^ d)` using `fun i => hd0 i d (hdle i)`. Establish `hd1 : ∀ i, IsSec x (d + 1) ((σ i : Ω) * x (ci i) ^ (d + 1))` using `fun i => hd0 i _ ((hdle i).trans (Nat.le_succ d))`. Establish `hcmp` using `fun w : I × I × Fin r × Fin r => compare hT (hci w.1) (hci w.2.1) (σ w.1).2 (σ w.2.1) (hd w.1) (hd1 w.1) (hbf w.1) (hbf w.2.1) (hβ w.1) w.2.2.1 w.2.2.2`. Use `choose N hN using hcmp`.

Set `M` to `Finset.univ.sup N`. Establish `hM : ∀ w, N w ≤ M` using `fun w => Finset.le_sup (Finset.mem_univ w)`. Set `φ : I × Fin r → Module.Dual Ω E` to `fun t => ((σ t.1 : Ω) * x (ci t.1) ^ (d + 1)) ^ M • β t.1 t.2`. It suffices to establish `H : ∃ (n : ℕ) (φ' : Fin n → Module.Dual Ω E), IsTwistGen ξ x L ((d + 1) * M) φ' by`. Take `⟨n, φ', h⟩` from `H`.

Conclude with `⟨_, n, φ', h⟩`. Use `twistGen_of_fintype φ ?_ ?_` and prove the remaining obligations. Introduce `t p c hp e he`. Take `⟨s', hs'm, hs'u⟩` from `hS1 ⟨c, hp.1⟩ p hp`. Set `j : I` to `⟨⟨c, hp.1⟩, ⟨s', hs'm⟩⟩`.

Take `⟨hco, hexp⟩` from `frame_coords (hbf j p hp hs'u) (hβ j) he`. Rewrite using `[twist_eval]`. Establish `e1 : β t.1 t.2 e = ∑ l, β j l e * β t.1 t.2 (b j l)` using `by conv_lhs => rw [hexp]`. Simplify using `only [map_sum, map_smul, smul_eq_mul]`. Rewrite using `[e1, Finset.mul_sum]`.

Use `sum_mem fun l _ => ?_` and prove the remaining obligations. Rewrite using `[mul_left_comm]`. Use `mul_mem (hco l) ?_` and prove the remaining obligations. Establish `hA : (σ t.1 : Ω) * x (ci t.1) ^ (d + 1) / x c ^ (d + 1) ∈ regAt ξ p` using `chartR_le hT hp.1 (hd1 t.1 c hp.1) hp`. Conclude with `power_step hA hs'u.1 hs'u.2.2 (hM (t.1, j, t.2, l)) (chartR_le hT hp.1 (hN (t.1, j, t.2, l)) hp)`.

Introduce `p c hp w hw`. Take `⟨s', hs'm, hs'u⟩` from `hS1 ⟨c, hp.1⟩ p hp`. Set `j : I` to `⟨⟨c, hp.1⟩, ⟨s', hs'm⟩⟩`. Establish `hfr` using `hbf j p hp hs'u`. Establish `hmem : ∀ k, b j k ∈ L p` using `fun k => by`.

Rewrite using `[hfr.2]`. Conclude with `Submodule.subset_span ⟨k, rfl⟩`. Use `⟨fun t => if t.1 = j then w (b j t.2) * (s' : Ω)⁻¹ ^ M else 0, fun t => ?_, fun e he => ?_⟩` and prove the remaining obligations. Simplify using `only split_ifs`. Conclude with `mul_mem (hw _ (hmem _)) (pow_mem hs'u.2.2 _)`.

Conclude with `zero_mem _`. Take `⟨-, hexp⟩` from `frame_coords hfr (hβ j) he`. Establish `e1 : w e = ∑ l, β j l e * w (b j l)` using `by conv_lhs => rw [hexp]`. Simplify using `only [map_sum, map_smul, smul_eq_mul]`. Rewrite using `[e1, Fintype.sum_prod_type, Finset.sum_eq_single j]`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Establish `e2 : φ (j, l) e / x c ^ ((d + 1) * M) = (s' : Ω) ^ M * β j l e` using `by show (((s' : Ω) * x c ^ (d + 1)) ^ M • β j l) e / x c ^ ((d + 1) * M) = _`. Rewrite using `[twist_eval, mul_div_cancel_right₀ _ (pow_ne_zero _ hp.1)]`. Rewrite using `[e2]`. Simplify using `only [if_true]`.

Use `hs'u.1` as an intermediate fact. Rewrite using `[inv_pow]`. Clear the denominators using the available nonvanishing facts. Introduce `i _ hij`. Simplify using `[hij]`.

Introduce `hj`. Conclude with `absurd (Finset.mem_univ j) hj`.
-/
theorem exists_twistGen : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type)
    [AddCommGroup E] [Module Ω E] (κ : Type) [Finite κ] (x : κ → Ω) (L : Lat ξ E) (r : ℕ) (V : Submodule Ω E),
    CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → L.IsVB r V →
    ∃ (m n : ℕ) (φ : Fin n → Module.Dual Ω E), IsTwistGen ξ x L m φ := by
  intro X Ω _ ξ E _ _ κ _ x L r V hT _ hL
  classical
  let C := {c : κ // x c ≠ 0}
  have hcov := fun c : C => frame_cover hT hL c.2
  choose S hS1 hS2 using hcov
  let I := Σ c : C, {s // s ∈ S c}
  letI : Fintype I := Fintype.ofFinite I
  let ci : I → κ := fun i => i.1.1
  have hci : ∀ i, x (ci i) ≠ 0 := fun i => i.1.2
  let σ : ∀ i : I, chartR x (ci i) := fun i => i.2.1
  have hF := fun i : I => hS2 i.1 i.2.1 i.2.2
  choose b hbl hbf using hF
  choose β hβ using fun i => exists_dual (hbl i)
  have hsec := fun i : I => exists_isSec (hci i) (σ i).2
  choose d0 hd0 using hsec
  let d := Finset.univ.sup d0
  have hdle : ∀ i, d0 i ≤ d := fun i => Finset.le_sup (Finset.mem_univ i)
  have hd : ∀ i, IsSec x d ((σ i : Ω) * x (ci i) ^ d) := fun i => hd0 i d (hdle i)
  have hd1 : ∀ i, IsSec x (d + 1) ((σ i : Ω) * x (ci i) ^ (d + 1)) := fun i => hd0 i _ ((hdle i).trans (Nat.le_succ d))
  have hcmp := fun w : I × I × Fin r × Fin r =>
    compare hT (hci w.1) (hci w.2.1) (σ w.1).2 (σ w.2.1) (hd w.1) (hd1 w.1) (hbf w.1) (hbf w.2.1) (hβ w.1) w.2.2.1 w.2.2.2
  choose N hN using hcmp
  let M := Finset.univ.sup N
  have hM : ∀ w, N w ≤ M := fun w => Finset.le_sup (Finset.mem_univ w)
  let φ : I × Fin r → Module.Dual Ω E := fun t => ((σ t.1 : Ω) * x (ci t.1) ^ (d + 1)) ^ M • β t.1 t.2
  suffices H : ∃ (n : ℕ) (φ' : Fin n → Module.Dual Ω E), IsTwistGen ξ x L ((d + 1) * M) φ' by
    obtain ⟨n, φ', h⟩ := H
    exact ⟨_, n, φ', h⟩
  refine twistGen_of_fintype φ ?_ ?_
  · intro t p c hp e he
    obtain ⟨s', hs'm, hs'u⟩ := hS1 ⟨c, hp.1⟩ p hp
    let j : I := ⟨⟨c, hp.1⟩, ⟨s', hs'm⟩⟩
    obtain ⟨hco, hexp⟩ := frame_coords (hbf j p hp hs'u) (hβ j) he
    rw [twist_eval]
    have e1 : β t.1 t.2 e = ∑ l, β j l e * β t.1 t.2 (b j l) := by
      conv_lhs => rw [hexp]
      simp only [map_sum, map_smul, smul_eq_mul]
    rw [e1, Finset.mul_sum]
    refine sum_mem fun l _ => ?_
    rw [mul_left_comm]
    refine mul_mem (hco l) ?_
    have hA : (σ t.1 : Ω) * x (ci t.1) ^ (d + 1) / x c ^ (d + 1) ∈ regAt ξ p :=
      chartR_le hT hp.1 (hd1 t.1 c hp.1) hp
    exact power_step hA hs'u.1 hs'u.2.2 (hM (t.1, j, t.2, l)) (chartR_le hT hp.1 (hN (t.1, j, t.2, l)) hp)
  · intro p c hp w hw
    obtain ⟨s', hs'm, hs'u⟩ := hS1 ⟨c, hp.1⟩ p hp
    let j : I := ⟨⟨c, hp.1⟩, ⟨s', hs'm⟩⟩
    have hfr := hbf j p hp hs'u
    have hmem : ∀ k, b j k ∈ L p := fun k => by
      rw [hfr.2]
      exact Submodule.subset_span ⟨k, rfl⟩
    refine ⟨fun t => if t.1 = j then w (b j t.2) * (s' : Ω)⁻¹ ^ M else 0, fun t => ?_, fun e he => ?_⟩
    · dsimp only
      split_ifs
      · exact mul_mem (hw _ (hmem _)) (pow_mem hs'u.2.2 _)
      · exact zero_mem _
    · obtain ⟨-, hexp⟩ := frame_coords hfr (hβ j) he
      have e1 : w e = ∑ l, β j l e * w (b j l) := by
        conv_lhs => rw [hexp]
        simp only [map_sum, map_smul, smul_eq_mul]
      rw [e1, Fintype.sum_prod_type, Finset.sum_eq_single j]
      · refine Finset.sum_congr rfl fun l _ => ?_
        have e2 : φ (j, l) e / x c ^ ((d + 1) * M) = (s' : Ω) ^ M * β j l e := by
          show (((s' : Ω) * x c ^ (d + 1)) ^ M • β j l) e / x c ^ ((d + 1) * M) = _
          rw [twist_eval, mul_div_cancel_right₀ _ (pow_ne_zero _ hp.1)]
        rw [e2]
        simp only [if_true]
        have := hs'u.1
        rw [inv_pow]
        field_simp
      · intro i _ hij
        simp [hij]
      · intro hj
        exact absurd (Finset.mem_univ j) hj

end GlobalTheory.CompanionTheory.Ar.FlagBun.Twist
