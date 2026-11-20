import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CycOfPrime

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors

namespace GlobalTheory.SW.Nbr

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

noncomputable def co : 𝓞 E ≃+* 𝓞 E := (IsCMField.ringOfIntegersComplexConj E).toRingEquiv

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_co (a : 𝓞 E) : ((co a : 𝓞 E) : E) = cc (a : E) := rfl

/- English proof (translation)
The claim follows from `IsCMField.complexConj_apply_apply E a`.
-/
theorem cc_cc (a : E) : cc (cc a) = a := IsCMField.complexConj_apply_apply E a

/- English proof (translation)
The claim follows from `RingOfIntegers.ext (cc_cc _)`.
-/
theorem co_co (a : 𝓞 E) : co (co a) = a := RingOfIntegers.ext (cc_cc _)

/- English proof (translation)
Unfold `conjI Ideal.map`. Use `congr 1`. Use extensionality with `a`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb, h⟩`.

Conclude with `⟨b, hb, (RingOfIntegers.ext h).symm⟩`. Introduce and unpack `⟨b, hb, rfl⟩`. Conclude with `⟨b, hb, rfl⟩`.
-/
theorem conjI_eq (P : Ideal (𝓞 E)) : conjI P = P.map (co (E := E)) := by
  unfold conjI Ideal.map
  congr 1
  ext a
  constructor
  · rintro ⟨b, hb, h⟩
    exact ⟨b, hb, (RingOfIntegers.ext h).symm⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, rfl⟩

/- English proof (translation)
Rewrite using `[conjI_eq, Ideal.mem_map_of_equiv]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb, rfl⟩`. Rewrite using `[co_co]` and apply the resulting hypothesis. Conclude with `fun h => ⟨_, h, co_co a⟩`.
-/
theorem mem_conjI {P : Ideal (𝓞 E)} {a : 𝓞 E} : a ∈ conjI P ↔ co a ∈ P := by
  rw [conjI_eq, Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨b, hb, rfl⟩
    rwa [co_co]
  · exact fun h => ⟨_, h, co_co a⟩

/- English proof (translation)
Use extensionality with `a`. Rewrite using `[mem_conjI, mem_conjI, co_co]`.
-/
theorem conjI_conjI (P : Ideal (𝓞 E)) : conjI (conjI P) = P := by
  ext a
  rw [mem_conjI, mem_conjI, co_co]

/- English proof (translation)
Rewrite using `[conjI_eq, Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]`. Conclude with `(Nat.card_congr (Ideal.quotientEquiv P (P.map (co (E := E))) co rfl).toEquiv).symm`.
-/
theorem absNorm_conjI (P : Ideal (𝓞 E)) : Ideal.absNorm (conjI P) = Ideal.absNorm P := by
  rw [conjI_eq, Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv P (P.map (co (E := E))) co rfl).toEquiv).symm

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1, h.2.1, (absNorm_conjI P).trans h.2.2.1, by rw [conjI_conjI]; exact h.2.2.2.1.symm, h.2.2.2.2⟩`.
-/
theorem good_conj {M q : ℕ} {P : Ideal (𝓞 E)} (h : GoodPrime M q P) : GoodPrime M q (conjI P) :=
  ⟨h.1, h.2.1, (absNorm_conjI P).trans h.2.2.1, by rw [conjI_conjI]; exact h.2.2.2.1.symm, h.2.2.2.2⟩

omit [IsCMField E] in
/- English proof (translation)
Introduce and unpack `rfl`. Rewrite `h` using `[Ideal.absNorm_bot]`. Conclude with `hq.ne_zero h.symm`.
-/
theorem ne_bot_of_norm {q : ℕ} {P : Ideal (𝓞 E)} (hq : q.Prime) (h : Ideal.absNorm P = q) :
    P ≠ ⊥ := by
  rintro rfl
  rw [Ideal.absNorm_bot] at h
  exact hq.ne_zero h.symm

omit [IsCMField E] in
/- English proof (translation)
The claim follows from `(Ideal.isPrime_of_irreducible_absNorm (h ▸ hq)).isMaximal (ne_bot_of_norm hq h)`.
-/
theorem max_of_norm {q : ℕ} {P : Ideal (𝓞 E)} (hq : q.Prime) (h : Ideal.absNorm P = q) :
    P.IsMaximal :=
  (Ideal.isPrime_of_irreducible_absNorm (h ▸ hq)).isMaximal (ne_bot_of_norm hq h)

/- English proof (translation)
Unfold `herm`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `[Matrix.one_apply]`.
-/
theorem herm_one (x y : Fin n → E) : herm 1 x y = ∑ a, x a * cc (y a) := by
  unfold herm
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Matrix.one_apply]

/- English proof (translation)
Simplify using `[herm_one, Finset.mul_sum, mul_assoc]`.
-/
theorem herm_sl (c : E) (x y : Fin n → E) : herm 1 (c • x) y = c * herm 1 x y := by
  simp [herm_one, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Simplify using `[herm_one, Finset.mul_sum, cc, mul_left_comm]`.
-/
theorem herm_sr (c : E) (x y : Fin n → E) : herm 1 x (c • y) = cc c * herm 1 x y := by
  simp [herm_one, Finset.mul_sum, cc, mul_left_comm]

/- English proof (translation)
Simplify using `[herm_one, add_mul, Finset.sum_add_distrib]`.
-/
theorem herm_al (x x' y : Fin n → E) : herm 1 (x + x') y = herm 1 x y + herm 1 x' y := by
  simp [herm_one, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[herm_one, cc, mul_comm]`.
-/
theorem herm_symm (x y : Fin n → E) : cc (herm 1 x y) = herm 1 y x := by
  simp [herm_one, cc, mul_comm]

omit [IsCMField E] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem osmul (c : 𝓞 E) (x : Fin n → E) : c • x = (c : E) • x := rfl

def Int' (x y : Fin n → E) : Prop := IsIntegral ℤ (herm 1 x y)

/- English proof (translation)
Unfold `Int'`. Rewrite using `[← herm_symm]`. Conclude with `(co (⟨_, h⟩ : 𝓞 E)).2`.
-/
theorem Int'.symm {x y : Fin n → E} (h : Int' x y) : Int' y x := by
  unfold Int'
  rw [← herm_symm]
  exact (co (⟨_, h⟩ : 𝓞 E)).2

/- English proof (translation)
Unfold `Int'`. Rewrite using `[herm_al]`. Conclude with `IsIntegral.add h h'`.
-/
theorem Int'.add {x x' y : Fin n → E} (h : Int' x y) (h' : Int' x' y) : Int' (x + x') y := by
  unfold Int'
  rw [herm_al]
  exact IsIntegral.add h h'

/- English proof (translation)
Unfold `Int'`. Rewrite using `[osmul, herm_sl]`. Conclude with `IsIntegral.mul c.2 h`.
-/
theorem Int'.smul {x y : Fin n → E} (c : 𝓞 E) (h : Int' x y) : Int' (c • x) y := by
  unfold Int'
  rw [osmul, herm_sl]
  exact IsIntegral.mul c.2 h

/- English proof (translation)
Unfold `Int'`. Rewrite using `[herm_one]`. Simplify using `using isIntegral_zero`.
-/
theorem int_zero (y : Fin n → E) : Int' 0 y := by
  unfold Int'
  rw [herm_one]
  simpa using isIntegral_zero

/- English proof (translation)
Unfold `Int'`. Rewrite using `[osmul, osmul, herm_sl, herm_sr, coe_co, cc_cc]`.
-/
theorem int_move (c : 𝓞 E) (x y : Fin n → E) : Int' (c • x) y ↔ Int' x (co c • y) := by
  unfold Int'
  rw [osmul, osmul, herm_sl, herm_sr, coe_co, cc_cc]

def SD (Λ : Lt E n) : Prop := ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, Int' x y

/- English proof (translation)
The claim follows from `le_antisymm hle fun x hx => (h x).2 fun y hy => (h' x).1 hx y (hle hy)`.
-/
theorem SD.eq_of_le {Λ Λ' : Lt E n} (h : SD Λ) (h' : SD Λ') (hle : Λ ≤ Λ') : Λ = Λ' :=
  le_antisymm hle fun x hx => (h x).2 fun y hy => (h' x).1 hx y (hle hy)

omit [IsCMField E] in
/- English proof (translation)
The claim follows from `Submodule.smul_le`.
-/
theorem smul_le_iff {P : Ideal (𝓞 E)} {Λ Λ' : Lt E n} :
    P • Λ ≤ Λ' ↔ ∀ c ∈ P, ∀ x ∈ Λ, c • x ∈ Λ' := Submodule.smul_le

/- English proof (translation)
The claim follows from `smul_le_iff.2 fun c hc x hx => (h _).2 fun y hy => (int_move c x y).2 ((h' x).1 hx _ (smul_le_iff.1 hle _ (mem_conjI.1 hc) y hy))`.
-/
theorem conj_le {P : Ideal (𝓞 E)} {Λ Λ' : Lt E n} (h : SD Λ) (h' : SD Λ') (hle : P • Λ ≤ Λ') :
    conjI P • Λ' ≤ Λ := smul_le_iff.2 fun c hc x hx => (h _).2 fun y hy =>
  (int_move c x y).2 ((h' x).1 hx _ (smul_le_iff.1 hle _ (mem_conjI.1 hc) y hy))

omit [IsCMField E] in
/- English proof (translation)
Take `⟨s, hs, hc, h1, h2⟩` from `h`. Take `⟨t, ht, hd, h3, h4⟩` from `h'`. Use `⟨s * t, Nat.mul_pos hs ht, Nat.Coprime.mul_left hc hd, fun v hv => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.cast_mul, mul_comm, mul_smul]`. Conclude with `h3 _ (h1 v hv)`.

Rewrite using `[Nat.cast_mul, mul_smul]`. Conclude with `h2 _ (h4 v hv)`.
-/
theorem agree_trans {M : ℕ} {Λ Λ' Λ'' : Lt E n} (h : Agree M Λ Λ') (h' : Agree M Λ' Λ'') :
    Agree M Λ Λ'' := by
  obtain ⟨s, hs, hc, h1, h2⟩ := h
  obtain ⟨t, ht, hd, h3, h4⟩ := h'
  refine ⟨s * t, Nat.mul_pos hs ht, Nat.Coprime.mul_left hc hd, fun v hv => ?_, fun v hv => ?_⟩
  · rw [Nat.cast_mul, mul_comm, mul_smul]; exact h3 _ (h1 v hv)
  · rw [Nat.cast_mul, mul_smul]; exact h2 _ (h4 v hv)

omit [IsCMField E] in
/- English proof (translation)
Take `⟨s, hs, hc, h1, h2⟩` from `h`. Conclude with `⟨s, hs, hc, h2, h1⟩`.
-/
theorem agree_symm {M : ℕ} {Λ Λ' : Lt E n} (h : Agree M Λ Λ') : Agree M Λ' Λ := by
  obtain ⟨s, hs, hc, h1, h2⟩ := h
  exact ⟨s, hs, hc, h2, h1⟩

/- English proof (translation)
Establish `h1 : ((q : ℕ) : 𝓞 E) ∈ P` using `hP.2.2.1 ▸ Ideal.absNorm_mem P`. Establish `h2 : ((q : ℕ) : 𝓞 E) ∈ conjI P` using `(good_conj hP).2.2.1 ▸ Ideal.absNorm_mem _`. Conclude with `⟨q, hP.1.pos, hm, fun v hv => smul_le_iff.1 hle _ h1 v hv, fun v hv => smul_le_iff.1 (conj_le h h' hle) _ h2 v hv⟩`.
-/
theorem agree_of_le {M q m : ℕ} {P : Ideal (𝓞 E)} (hP : GoodPrime M q P) (hm : q.Coprime m)
    {Λ Λ' : Lt E n} (h : SD Λ) (h' : SD Λ') (hle : P • Λ ≤ Λ') : Agree m Λ Λ' := by
  have h1 : ((q : ℕ) : 𝓞 E) ∈ P := hP.2.2.1 ▸ Ideal.absNorm_mem P
  have h2 : ((q : ℕ) : 𝓞 E) ∈ conjI P := (good_conj hP).2.2.1 ▸ Ideal.absNorm_mem _
  exact ⟨q, hP.1.pos, hm, fun v hv => smul_le_iff.1 hle _ h1 v hv,
    fun v hv => smul_le_iff.1 (conj_le h h' hle) _ h2 v hv⟩

omit [IsCMField E] in
/- English proof (translation)
Take `⟨s, hs, -, -, h2⟩` from `ha`. Establish `hs' : (s : E) ≠ 0` using `Nat.cast_ne_zero.2 hs.ne'`. Set `f : (Fin n → E) →ₗ[𝓞 E] (Fin n → E)` to `(LinearMap.lsmul E (Fin n → E) (s : E)⁻¹).restrictScalars (𝓞 E)`. Use `Submodule.FG.of_le (h.map f) fun v hv => ⟨_, h2 v hv, ?_⟩` and prove the remaining obligations. Simplify using `[f, smul_smul, hs']`.
-/
theorem fg_of_agree {m : ℕ} {Λ Λ' : Lt E n} (h : Λ.FG) (ha : Agree m Λ Λ') : Λ'.FG := by
  obtain ⟨s, hs, -, -, h2⟩ := ha
  have hs' : (s : E) ≠ 0 := Nat.cast_ne_zero.2 hs.ne'
  let f : (Fin n → E) →ₗ[𝓞 E] (Fin n → E) :=
    (LinearMap.lsmul E (Fin n → E) (s : E)⁻¹).restrictScalars (𝓞 E)
  refine Submodule.FG.of_le (h.map f) fun v hv => ⟨_, h2 v hv, ?_⟩
  simp [f, smul_smul, hs']

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2, h3⟩`. Conclude with `⟨h1.2.1, h2, h3.trans hP.2.2.1⟩`. Introduce and unpack `⟨h1, h2, h3⟩`. Establish `ha` using `agree_of_le hP hP.2.1 h.2.1 h1 h2`.

Conclude with `⟨⟨fg_of_agree h.1 ha, h1, agree_trans (agree_symm ha) h.2.2⟩, h2, h3.trans hP.2.2.1.symm⟩`.
-/
theorem mem_Nb {M q : ℕ} {P : Ideal (𝓞 E)} (hP : GoodPrime M q P) {Λ Λ' : Lt E n}
    (h : Λ ∈ Vset E n M) : Λ' ∈ Nb M P Λ ↔
      SD Λ' ∧ P • Λ ≤ Λ' ∧ Λ'.toAddSubgroup.relIndex Λ.toAddSubgroup = q := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1.2.1, h2, h3.trans hP.2.2.1⟩
  · rintro ⟨h1, h2, h3⟩
    have ha := agree_of_le hP hP.2.1 h.2.1 h1 h2
    exact ⟨⟨fg_of_agree h.1 ha, h1, agree_trans (agree_symm ha) h.2.2⟩, h2, h3.trans hP.2.2.1.symm⟩

/- English proof (translation)
Take `⟨s, hs, -, -, h2⟩` from `h.2.2`. Use `isLocalizedModule_id (𝓞 E)⁰ (Fin n → E) E` as an intermediate fact. Use `⟨IsLocalizedModule.map_units (LinearMap.id (R := 𝓞 E) (M := Fin n → E)), fun y => ?_, fun {x₁ x₂} h => ⟨1, by rw [Subtype.ext h]⟩⟩` and prove the remaining obligations. Take `⟨d, hd⟩` from `IsLocalization.exist_integer_multiples_of_finite (𝓞 E)⁰ y`. Use `choose c hc using hd`.

Establish `h1 : (d : 𝓞 E) • y ∈ stdL E n`. Establish `: (d : 𝓞 E) • y = ∑ i, c i • (Pi.single i 1 : Fin n → E)`. Use extensionality with `j`. Simplify using `[Finset.sum_apply, Pi.single_apply, ← hc j, Algebra.smul_def]`. Rewrite using `[this]`.

Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Establish `hs' : (s : 𝓞 E) ∈ (𝓞 E)⁰` using `mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.2 hs.ne')`. Conclude with `⟨(⟨_, h2 _ h1⟩, ⟨s, hs'⟩ * d), mul_smul _ _ _⟩`.
-/
theorem isLoc {M : ℕ} {Λ : Lt E n} (h : Λ ∈ Vset E n M) :
    IsLocalizedModule (𝓞 E)⁰ Λ.subtype := by
  obtain ⟨s, hs, -, -, h2⟩ := h.2.2
  have := isLocalizedModule_id (𝓞 E)⁰ (Fin n → E) E
  refine ⟨IsLocalizedModule.map_units (LinearMap.id (R := 𝓞 E) (M := Fin n → E)), fun y => ?_,
    fun {x₁ x₂} h => ⟨1, by rw [Subtype.ext h]⟩⟩
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (𝓞 E)⁰ y
  choose c hc using hd
  have h1 : (d : 𝓞 E) • y ∈ stdL E n := by
    have : (d : 𝓞 E) • y = ∑ i, c i • (Pi.single i 1 : Fin n → E) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, ← hc j, Algebra.smul_def]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hs' : (s : 𝓞 E) ∈ (𝓞 E)⁰ := mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.2 hs.ne')
  exact ⟨(⟨_, h2 _ h1⟩, ⟨s, hs'⟩ * d), mul_smul _ _ _⟩

/- English proof (translation)
Use `isLoc h` as an intermediate fact. Rewrite using `[← IsLocalizedModule.finrank_eq (𝓞 E)⁰ Λ.subtype le_rfl, ← IsLocalization.finrank_eq E (𝓞 E)⁰ le_rfl]`. Simplify using the standard rewrite rules.
-/
theorem finrank_eq {M : ℕ} {Λ : Lt E n} (h : Λ ∈ Vset E n M) : Module.finrank (𝓞 E) Λ = n := by
  have := isLoc h
  rw [← IsLocalizedModule.finrank_eq (𝓞 E)⁰ Λ.subtype le_rfl,
    ← IsLocalization.finrank_eq E (𝓞 E)⁰ le_rfl]
  simp

omit [IsCMField E] in
/- English proof (translation)
Establish `: Module.Finite (𝓞 E) Λ` using `Module.Finite.iff_fg.mpr h`. Establish `: Module.Flat (𝓞 E) Λ` using `inferInstance`. Establish `: Module.FinitePresentation (𝓞 E) Λ` using `Module.finitePresentation_of_finite _ _`. Conclude with `Module.Flat.projective_of_finitePresentation`.
-/
theorem proj {Λ : Lt E n} (h : Λ.FG) : Module.Projective (𝓞 E) Λ := by
  have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr h
  have : Module.Flat (𝓞 E) Λ := inferInstance
  have : Module.FinitePresentation (𝓞 E) Λ := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

/- English proof (translation)
Use `isLoc h` as an intermediate fact. Use `isLocalizedModule_id (𝓞 E)⁰ E E` as an intermediate fact. Set `G` to `IsLocalizedModule.lift (𝓞 E)⁰ Λ.subtype g (IsLocalizedModule.map_units (LinearMap.id (R := 𝓞 E) (M := E)))`. Set `G'` to `G.extendScalarsOfIsLocalization (𝓞 E)⁰ E`. Use `⟨fun i => cc (G' (Pi.single i 1)), fun y => ?_⟩` and prove the remaining obligations.

Establish `h1 : G' y = g y` using `IsLocalizedModule.lift_apply (𝓞 E)⁰ Λ.subtype g (IsLocalizedModule.map_units (LinearMap.id (R := 𝓞 E) (M := E))) y`. Rewrite using `[← h1, herm_one, LinearMap.pi_apply_eq_sum_univ G']`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[cc_cc, smul_eq_mul]`. Use `congr 2`.

Use extensionality with `j`. Simplify using `[Pi.single_apply, eq_comm]`.
-/
theorem exists_vec {M : ℕ} {Λ : Lt E n} (h : Λ ∈ Vset E n M) (g : Λ →ₗ[𝓞 E] E) :
    ∃ x : Fin n → E, ∀ y : Λ, herm 1 y x = g y := by
  have := isLoc h
  have := isLocalizedModule_id (𝓞 E)⁰ E E
  let G := IsLocalizedModule.lift (𝓞 E)⁰ Λ.subtype g
    (IsLocalizedModule.map_units (LinearMap.id (R := 𝓞 E) (M := E)))
  let G' := G.extendScalarsOfIsLocalization (𝓞 E)⁰ E
  refine ⟨fun i => cc (G' (Pi.single i 1)), fun y => ?_⟩
  have h1 : G' y = g y := IsLocalizedModule.lift_apply (𝓞 E)⁰ Λ.subtype g
    (IsLocalizedModule.map_units (LinearMap.id (R := 𝓞 E) (M := E))) y
  rw [← h1, herm_one, LinearMap.pi_apply_eq_sum_univ G']
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cc_cc, smul_eq_mul]
  congr 2
  ext j
  simp [Pi.single_apply, eq_comm]

/- English proof (translation)
Use `proj h.1` as an intermediate fact. Take `⟨g, hg⟩` from `Module.projective_lifting_property P.mkQ f P.mkQ_surjective`. Take `⟨t, ht, ht1⟩` from `FractionalIdeal.exists_notMem_one_of_ne_bot (K := E) hP0 hP.ne_top`. Establish `htP : ∀ c ∈ P, IsIntegral ℤ (t * (c : E))` using `fun c hc => by`. Establish `h1` using `(FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 hP0)).1 ht _ (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 E)⁰ hc)`.

Take `⟨b, hb⟩` from `(FractionalIdeal.mem_one_iff _).1 h1`. Establish `hb : (b : E) = t * (c : E)` using `hb`. Rewrite using `[← hb]`. Conclude with `b.2`. Take `⟨x, hx⟩` from `exists_vec h (Algebra.linearMap (𝓞 E) E ∘ₗ g)`.

Use `⟨cc t • x, fun y => ?_⟩` and prove the remaining obligations. Establish `h1 : herm 1 (y : Fin n → E) (cc t • x) = t * (g y : E)`. Rewrite using `[herm_sr, cc_cc, hx]`. Both sides reduce to the same expression. Establish `h2 : f y = 0 ↔ g y ∈ P`.

Rewrite using `[← hg]`. Conclude with `Submodule.Quotient.mk_eq_zero P`. Unfold `Int'`. Rewrite using `[h1, h2]`. Use `⟨fun hi => by_contra fun hn => ht1 ?_, htP _⟩` and prove the remaining obligations.

Take `⟨u, c, hc, huc⟩` from `hP.exists_inv hn`. Establish `h3 : (u : E) * (g y : E) + (c : E) = 1` using `by exact_mod_cast congrArg (fun a : 𝓞 E => (a : E)) huc`. Establish `h4 : IsIntegral ℤ t`. Establish `: t = (u : E) * (t * (g y : E)) + t * (c : E)` using `by linear_combination (-t) * h3`. Rewrite using `[this]`.

Conclude with `(IsIntegral.mul u.2 hi).add (htP c hc)`. Conclude with `(FractionalIdeal.mem_one_iff _).2 ⟨⟨t, h4⟩, rfl⟩`.
-/
theorem exists_sep {M : ℕ} {Λ : Lt E n} (h : Λ ∈ Vset E n M) (P : Ideal (𝓞 E)) [hP : P.IsMaximal]
    (hP0 : P ≠ ⊥) (f : Λ →ₗ[𝓞 E] 𝓞 E ⧸ P) : ∃ x : Fin n → E, ∀ y : Λ, Int' y x ↔ f y = 0 := by
  have := proj h.1
  obtain ⟨g, hg⟩ := Module.projective_lifting_property P.mkQ f P.mkQ_surjective
  obtain ⟨t, ht, ht1⟩ := FractionalIdeal.exists_notMem_one_of_ne_bot (K := E) hP0 hP.ne_top
  have htP : ∀ c ∈ P, IsIntegral ℤ (t * (c : E)) := fun c hc => by
    have h1 := (FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 hP0)).1 ht _
      (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 E)⁰ hc)
    obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    have hb : (b : E) = t * (c : E) := hb
    rw [← hb]; exact b.2
  obtain ⟨x, hx⟩ := exists_vec h (Algebra.linearMap (𝓞 E) E ∘ₗ g)
  refine ⟨cc t • x, fun y => ?_⟩
  have h1 : herm 1 (y : Fin n → E) (cc t • x) = t * (g y : E) := by
    rw [herm_sr, cc_cc, hx]; rfl
  have h2 : f y = 0 ↔ g y ∈ P := by
    rw [← hg]; exact Submodule.Quotient.mk_eq_zero P
  unfold Int'
  rw [h1, h2]
  refine ⟨fun hi => by_contra fun hn => ht1 ?_, htP _⟩
  obtain ⟨u, c, hc, huc⟩ := hP.exists_inv hn
  have h3 : (u : E) * (g y : E) + (c : E) = 1 := by exact_mod_cast congrArg (fun a : 𝓞 E => (a : E)) huc
  have h4 : IsIntegral ℤ t := by
    have : t = (u : E) * (t * (g y : E)) + t * (c : E) := by linear_combination (-t) * h3
    rw [this]
    exact (IsIntegral.mul u.2 hi).add (htP c hc)
  exact (FractionalIdeal.mem_one_iff _).2 ⟨⟨t, h4⟩, rfl⟩

omit [IsCMField E] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem relIndex_eq (Λ Λ' : Lt E n) : Λ'.toAddSubgroup.relIndex Λ.toAddSubgroup =
    (Λ'.comap Λ.subtype).toAddSubgroup.index := rfl

omit [IsCMField E] in

/- English proof (translation)
Use `max_of_norm hq hP` as an intermediate fact. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Take `⟨v, hv, hc⟩` from `Hyper.cyc_of_prime N hq h2`. Conclude with `Hyper.exists_fun P N v hv (fun c hc => h1 c hc v) hc`.

Introduce and unpack `⟨f, hf, rfl⟩`. Use `⟨fun c hc x => ?_, (Hyper.index_ker P f hf).trans hP⟩` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker, map_smul, Algebra.smul_def]`. Establish `: algebraMap (𝓞 E) (𝓞 E ⧸ P) c = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 hc`. Rewrite using `[this, zero_mul]`.
-/
theorem index_iff {q : ℕ} {P : Ideal (𝓞 E)} (hq : q.Prime) (hP : Ideal.absNorm P = q)
    {Λ : Lt E n} (N : Submodule (𝓞 E) Λ) :
    ((∀ c ∈ P, ∀ x, c • x ∈ N) ∧ N.toAddSubgroup.index = q) ↔
      ∃ f : Λ →ₗ[𝓞 E] 𝓞 E ⧸ P, f ≠ 0 ∧ LinearMap.ker f = N := by
  have := max_of_norm hq hP
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨v, hv, hc⟩ := Hyper.cyc_of_prime N hq h2
    exact Hyper.exists_fun P N v hv (fun c hc => h1 c hc v) hc
  · rintro ⟨f, hf, rfl⟩
    refine ⟨fun c hc x => ?_, (Hyper.index_ker P f hf).trans hP⟩
    rw [LinearMap.mem_ker, map_smul, Algebra.smul_def]
    have : algebraMap (𝓞 E) (𝓞 E ⧸ P) c = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hc
    rw [this, zero_mul]

def nbOf (P : Ideal (𝓞 E)) (Λ₀ : Lt E n) : Lt E n where
  carrier := {x | (∀ y ∈ Λ₀, Int' x y) ∧ ∀ c ∈ conjI P, c • x ∈ Λ₀}
  add_mem' := fun ha hb => ⟨fun y hy => (ha.1 y hy).add (hb.1 y hy), fun c hc => by
    rw [smul_add]; exact Λ₀.add_mem (ha.2 c hc) (hb.2 c hc)⟩
  zero_mem' := ⟨fun y _ => int_zero y, fun c _ => by rw [smul_zero]; exact Λ₀.zero_mem⟩
  smul_mem' := fun a x hx => ⟨fun y hy => (hx.1 y hy).smul a, fun c hc => by
    rw [smul_comm]; exact Λ₀.smul_mem a (hx.2 c hc)⟩

/- English proof (translation)
Establish `hS : SD Λ` using `h.2.1`. Use `max_of_norm hP.1 hP.2.2.1` as an intermediate fact. Take `⟨a, ha, b, hb, hab⟩` from `Ideal.isCoprime_iff_exists.1 hP.2.2.2.1`. Establish `hdec : ∀ x : Fin n → E, x = a • x + b • x` using `fun x => by rw [← add_smul, hab, one_smul]`. Take `⟨f, -, hf⟩` from `(index_iff hP.1 hP.2.2.1 (Λ₀.comap Λ.subtype)).1 ⟨fun c hc x => smul_le_iff.1 h1 c hc x x.2, h3⟩`.

Take `⟨w, hw⟩` from `exists_sep h P (ne_bot_of_norm hP.1 hP.2.2.1) f`. Establish `hw' : ∀ y ∈ Λ, Int' y w ↔ y ∈ Λ₀` using `fun y hy => by`. Rewrite using `[hw ⟨y, hy⟩, ← LinearMap.mem_ker, hf]`. Both sides reduce to the same expression. Establish `hle : Λ₀ ≤ nbOf P Λ₀` using `fun x hx => ⟨fun y hy => (hS x).1 (h2 hx) y (h2 hy), fun c _ => Λ₀.smul_mem c hx⟩`.

Establish `hQ : ∀ x, (∀ y ∈ Λ₀, Int' x y) → ∀ c ∈ conjI P, c • x ∈ Λ` using `fun x hx c hc => (hS _).2 fun y hy => (int_move c x y).2 (hx _ (smul_le_iff.1 h1 _ (mem_conjI.1 hc) y hy))`. Use `⟨fun x => ⟨fun hx y hy => ?_, fun hx => ?_⟩, le_antisymm (fun x hx => ?_) (le_inf h2 hle)⟩` and prove the remaining obligations. Rewrite using `[hdec x]`. Conclude with `((int_move a x y).2 (hx.1 _ (hy.2 _ (mem_conjI.2 (by rwa [co_co]))))).add (hy.1 _ (hx.2 b hb)).symm`. Establish `hx0 : ∀ y ∈ Λ₀, Int' x y` using `fun y hy => hx y (hle hy)`.

Use `⟨hx0, fun c hc => (hw' _ (hQ x hx0 c hc)).1 ((int_move c x w).2 (hx _ ?_))⟩` and prove the remaining obligations. Establish `hw0 : ∀ y ∈ Λ₀, Int' w y` using `fun y hy => ((hw' y (h2 hy)).2 hy).symm`. Use `⟨fun y hy => (hw0 y hy).smul _, fun d hd => ?_⟩` and prove the remaining obligations. Rewrite using `[smul_comm]`. Conclude with `smul_le_iff.1 h1 _ (mem_conjI.1 hc) _ (hQ w hw0 d hd)`.

Rewrite using `[hdec x]`. Conclude with `Λ₀.add_mem (smul_le_iff.1 h1 a ha x hx.1) (hx.2.2 b hb)`.
-/
theorem nbOf_spec {M q : ℕ} {P : Ideal (𝓞 E)} (hP : GoodPrime M q P) {Λ Λ₀ : Lt E n}
    (h : Λ ∈ Vset E n M) (h1 : P • Λ ≤ Λ₀) (h2 : Λ₀ ≤ Λ)
    (h3 : Λ₀.toAddSubgroup.relIndex Λ.toAddSubgroup = q) :
    SD (nbOf P Λ₀) ∧ Λ ⊓ nbOf P Λ₀ = Λ₀ := by
  have hS : SD Λ := h.2.1
  have := max_of_norm hP.1 hP.2.2.1
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 hP.2.2.2.1
  have hdec : ∀ x : Fin n → E, x = a • x + b • x := fun x => by rw [← add_smul, hab, one_smul]
  obtain ⟨f, -, hf⟩ := (index_iff hP.1 hP.2.2.1 (Λ₀.comap Λ.subtype)).1
    ⟨fun c hc x => smul_le_iff.1 h1 c hc x x.2, h3⟩
  obtain ⟨w, hw⟩ := exists_sep h P (ne_bot_of_norm hP.1 hP.2.2.1) f
  have hw' : ∀ y ∈ Λ, Int' y w ↔ y ∈ Λ₀ := fun y hy => by
    rw [hw ⟨y, hy⟩, ← LinearMap.mem_ker, hf]; rfl
  have hle : Λ₀ ≤ nbOf P Λ₀ := fun x hx =>
    ⟨fun y hy => (hS x).1 (h2 hx) y (h2 hy), fun c _ => Λ₀.smul_mem c hx⟩
  have hQ : ∀ x, (∀ y ∈ Λ₀, Int' x y) → ∀ c ∈ conjI P, c • x ∈ Λ := fun x hx c hc =>
    (hS _).2 fun y hy => (int_move c x y).2 (hx _ (smul_le_iff.1 h1 _ (mem_conjI.1 hc) y hy))
  refine ⟨fun x => ⟨fun hx y hy => ?_, fun hx => ?_⟩, le_antisymm (fun x hx => ?_) (le_inf h2 hle)⟩
  · rw [hdec x]
    exact ((int_move a x y).2 (hx.1 _ (hy.2 _ (mem_conjI.2 (by rwa [co_co]))))).add
      (hy.1 _ (hx.2 b hb)).symm
  · have hx0 : ∀ y ∈ Λ₀, Int' x y := fun y hy => hx y (hle hy)
    refine ⟨hx0, fun c hc => (hw' _ (hQ x hx0 c hc)).1 ((int_move c x w).2 (hx _ ?_))⟩
    have hw0 : ∀ y ∈ Λ₀, Int' w y := fun y hy => ((hw' y (h2 hy)).2 hy).symm
    refine ⟨fun y hy => (hw0 y hy).smul _, fun d hd => ?_⟩
    rw [smul_comm]
    exact smul_le_iff.1 h1 _ (mem_conjI.1 hc) _ (hQ w hw0 d hd)
  · rw [hdec x]
    exact Λ₀.add_mem (smul_le_iff.1 h1 a ha x hx.1) (hx.2.2 b hb)

omit [IsCMField E] in
/- English proof (translation)
The claim follows from `AddSubgroup.inf_relIndex_left Λ.toAddSubgroup Λ'.toAddSubgroup`.
-/
theorem relIndex_inf (Λ Λ' : Lt E n) : (Λ ⊓ Λ').toAddSubgroup.relIndex Λ.toAddSubgroup =
    Λ'.toAddSubgroup.relIndex Λ.toAddSubgroup :=
  AddSubgroup.inf_relIndex_left Λ.toAddSubgroup Λ'.toAddSubgroup

/- English proof (translation)
Take `⟨h4, h5⟩` from `nbOf_spec hP h h1 h2 h3`. Use `(mem_Nb hP h).2 ⟨h4, h1.trans (h5.ge.trans inf_le_right), ?_⟩` and prove the remaining obligations. Rewrite using `[← relIndex_inf, h5, h3]`.
-/
theorem nbOf_mem {M q : ℕ} {P : Ideal (𝓞 E)} (hP : GoodPrime M q P) {Λ Λ₀ : Lt E n}
    (h : Λ ∈ Vset E n M) (h1 : P • Λ ≤ Λ₀) (h2 : Λ₀ ≤ Λ)
    (h3 : Λ₀.toAddSubgroup.relIndex Λ.toAddSubgroup = q) : nbOf P Λ₀ ∈ Nb M P Λ := by
  obtain ⟨h4, h5⟩ := nbOf_spec hP h h1 h2 h3
  refine (mem_Nb hP h).2 ⟨h4, h1.trans (h5.ge.trans inf_le_right), ?_⟩
  rw [← relIndex_inf, h5, h3]

/- English proof (translation)
Assemble the required witnesses or components as `⟨le_inf Submodule.smul_le_right h'.2.1, by rw [relIndex_inf, h'.2.2, hP.2.2.1]⟩`.
-/
theorem inf_spec {M q : ℕ} {P : Ideal (𝓞 E)} (hP : GoodPrime M q P) {Λ Λ' : Lt E n}
    (h' : Λ' ∈ Nb M P Λ) : P • Λ ≤ Λ ⊓ Λ' ∧
      (Λ ⊓ Λ').toAddSubgroup.relIndex Λ.toAddSubgroup = q :=
  ⟨le_inf Submodule.smul_le_right h'.2.1, by rw [relIndex_inf, h'.2.2, hP.2.2.1]⟩

/- English proof (translation)
Establish `hS' : SD Λ'` using `h'.1.2.1`. Use `hS'.eq_of_le (nbOf_spec hP h (inf_spec hP h').1 inf_le_left (inf_spec hP h').2).1 fun x hx => ⟨fun y hy => (hS' x).1 hx y hy.2, fun c hc => ⟨?_, Λ'.smul_mem c hx⟩⟩` and prove the remaining obligations. Conclude with `smul_le_iff.1 (conj_le h.2.1 hS' h'.2.1) c hc x hx`.
-/
theorem eq_nbOf {M q : ℕ} {P : Ideal (𝓞 E)} (hP : GoodPrime M q P) {Λ Λ' : Lt E n}
    (h : Λ ∈ Vset E n M) (h' : Λ' ∈ Nb M P Λ) : Λ' = nbOf P (Λ ⊓ Λ') := by
  have hS' : SD Λ' := h'.1.2.1
  refine hS'.eq_of_le (nbOf_spec hP h (inf_spec hP h').1 inf_le_left (inf_spec hP h').2).1
    fun x hx => ⟨fun y hy => (hS' x).1 hx y hy.2, fun c hc => ⟨?_, Λ'.smul_mem c hx⟩⟩
  exact smul_le_iff.1 (conj_le h.2.1 hS' h'.2.1) c hc x hx

omit [IsCMField E] in
/- English proof (translation)
Assume the negation of the conclusion as `hn`. Use `push Not at hn`. Use `ht (isIntegral_trans (A := 𝓞 E) t ?_)` and prove the remaining obligations. Use `isIntegral_of_smul_mem_submodule (Submodule.map (Algebra.linearMap (𝓞 E) E) Q) ?_ (Submodule.FG.map _ (IsNoetherian.noetherian _)) t ?_` and prove the remaining obligations. Take `⟨c, hc, hc0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hQ`.

Rewrite using `[Submodule.ne_bot_iff]`. Conclude with `⟨_, ⟨c, hc, rfl⟩, fun h0 => hc0 (RingOfIntegers.ext h0)⟩`. Introduce and unpack `_ ⟨d, hd, rfl⟩`. Conclude with `⟨⟨_, h d hd⟩, by_contra fun h0 => hn d hd _ h0 rfl, mul_comm _ _⟩`.
-/
theorem exists_not_mem {Q : Ideal (𝓞 E)} (hQ : Q ≠ ⊥) {t : E} (ht : ¬ IsIntegral ℤ t)
    (h : ∀ d ∈ Q, IsIntegral ℤ ((d : E) * t)) : ∃ d ∈ Q, ∃ r ∉ Q, ((r : 𝓞 E) : E) = (d : E) * t := by
  by_contra hn
  push Not at hn
  refine ht (isIntegral_trans (A := 𝓞 E) t ?_)
  refine isIntegral_of_smul_mem_submodule (Submodule.map (Algebra.linearMap (𝓞 E) E) Q) ?_
    (Submodule.FG.map _ (IsNoetherian.noetherian _)) t ?_
  · obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ
    rw [Submodule.ne_bot_iff]
    exact ⟨_, ⟨c, hc, rfl⟩, fun h0 => hc0 (RingOfIntegers.ext h0)⟩
  · rintro _ ⟨d, hd, rfl⟩
    exact ⟨⟨_, h d hd⟩, by_contra fun h0 => hn d hd _ h0 rfl, mul_comm _ _⟩

/- English proof (translation)
Establish `hQ` using `good_conj hP`. Establish `hmax` using `max_of_norm hQ.1 hQ.2.2.1`. Establish `hle'` using `smul_le_iff.1 (conj_le hS hS' hle)`. Take `⟨v, hv, hc⟩` from `Hyper.cyc_of_prime (Λ'.comap Λ.subtype) hP.1 hi`. Establish `key : ∀ x ∈ Λ', x ∈ Λ ↔ Int' x v` using `fun x hx => ⟨fun h => (hS x).1 h v v.2, fun h => (hS x).2 fun y hy => by`.

Take `⟨r, hr⟩` from `hc ⟨y, hy⟩`. Establish `hr : y - r • (v : Fin n → E) ∈ Λ'` using `hr`. Use `((hS' _).1 hr x hx).add (h.symm.smul r)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Conclude with `this.symm⟩`.

Choose the witnesses or unpack the hypotheses as in `⟨w, hw, hw'⟩ : ∃ w ∈ Λ', w ∉ Λ := by`. Assume the negation of the conclusion as `hn`. Use `push Not at hn`. Conclude with `hv (show (v : Fin n → E) ∈ Λ' from (hS'.eq_of_le hS hn).ge v.2)`. Establish `hint : ∀ x ∈ Λ', ∀ d ∈ conjI P, IsIntegral ℤ ((d : E) * herm 1 x v)` using `fun x hx d hd => by`.

Rewrite using `[← herm_sl]`. Conclude with `(hS _).1 (hle' d hd x hx) v v.2`. Take `⟨d, hd, r, hr, hrd⟩` from `exists_not_mem (ne_bot_of_norm hQ.1 hQ.2.2.1) (fun h => hw' ((key w hw).2 h)) (hint w hw)`. Take `⟨u, c, hc, huc⟩` from `hmax.exists_inv hr`. Establish `h3 : (u : E) * (r : E) + (c : E) = 1` using `by exact_mod_cast congrArg (fun a : 𝓞 E => (a : E)) huc`.

Take `⟨f, hf, hk⟩` from `Hyper.exists_fun (conjI P) (Λ.comap Λ'.subtype) ⟨w, hw⟩ hw' (fun c hc => hle' c hc w hw) fun x => by`. Set `e : 𝓞 E` to `⟨_, hint x x.2 d hd⟩`. Use `⟨u * e, (key _ (x - (u * e) • (⟨w, hw⟩ : Λ')).2).2 ?_⟩` and prove the remaining obligations. Establish `h4 : herm 1 ((x : Fin n → E) - (u * e) • w) v = (c : E) * herm 1 (x : Fin n → E) v`. Rewrite using `[sub_eq_add_neg, ← neg_smul, herm_al, osmul, herm_sl]`.

Establish `: ((-(u * e) : 𝓞 E) : E) = -((u : E) * ((d : E) * herm 1 (x : Fin n → E) v))` using `rfl`. Rewrite using `[this]`. Take the linear combination `(-herm 1 (x : Fin n → E) v) * h3 + (u : E) * herm 1 (x : Fin n → E) v * hrd`. Use `show IsIntegral ℤ (herm 1 ((x : Fin n → E) - (u * e) • w) v)`. Rewrite using `[h4]`.

Conclude with `hint x x.2 c hc`. Rewrite using `[relIndex_eq, ← hk, Hyper.index_ker _ f hf]`. Conclude with `hQ.2.2.1`.
-/
theorem index_symm {M q : ℕ} {P : Ideal (𝓞 E)} (hP : GoodPrime M q P) {Λ Λ' : Lt E n}
    (hS : SD Λ) (hS' : SD Λ') (hle : P • Λ ≤ Λ')
    (hi : Λ'.toAddSubgroup.relIndex Λ.toAddSubgroup = q) :
    Λ.toAddSubgroup.relIndex Λ'.toAddSubgroup = q := by
  have hQ := good_conj hP
  have hmax := max_of_norm hQ.1 hQ.2.2.1
  have hle' := smul_le_iff.1 (conj_le hS hS' hle)
  obtain ⟨v, hv, hc⟩ := Hyper.cyc_of_prime (Λ'.comap Λ.subtype) hP.1 hi
  have key : ∀ x ∈ Λ', x ∈ Λ ↔ Int' x v := fun x hx => ⟨fun h => (hS x).1 h v v.2, fun h =>
    (hS x).2 fun y hy => by
      obtain ⟨r, hr⟩ := hc ⟨y, hy⟩
      have hr : y - r • (v : Fin n → E) ∈ Λ' := hr
      have := ((hS' _).1 hr x hx).add (h.symm.smul r)
      rw [sub_add_cancel] at this
      exact this.symm⟩
  obtain ⟨w, hw, hw'⟩ : ∃ w ∈ Λ', w ∉ Λ := by
    by_contra hn
    push Not at hn
    exact hv (show (v : Fin n → E) ∈ Λ' from (hS'.eq_of_le hS hn).ge v.2)
  have hint : ∀ x ∈ Λ', ∀ d ∈ conjI P, IsIntegral ℤ ((d : E) * herm 1 x v) := fun x hx d hd => by
    rw [← herm_sl]
    exact (hS _).1 (hle' d hd x hx) v v.2
  obtain ⟨d, hd, r, hr, hrd⟩ := exists_not_mem (ne_bot_of_norm hQ.1 hQ.2.2.1)
    (fun h => hw' ((key w hw).2 h)) (hint w hw)
  obtain ⟨u, c, hc, huc⟩ := hmax.exists_inv hr
  have h3 : (u : E) * (r : E) + (c : E) = 1 := by exact_mod_cast congrArg (fun a : 𝓞 E => (a : E)) huc
  obtain ⟨f, hf, hk⟩ := Hyper.exists_fun (conjI P) (Λ.comap Λ'.subtype) ⟨w, hw⟩ hw'
    (fun c hc => hle' c hc w hw) fun x => by
      let e : 𝓞 E := ⟨_, hint x x.2 d hd⟩
      refine ⟨u * e, (key _ (x - (u * e) • (⟨w, hw⟩ : Λ')).2).2 ?_⟩
      have h4 : herm 1 ((x : Fin n → E) - (u * e) • w) v = (c : E) * herm 1 (x : Fin n → E) v := by
        rw [sub_eq_add_neg, ← neg_smul, herm_al, osmul, herm_sl]
        have : ((-(u * e) : 𝓞 E) : E) = -((u : E) * ((d : E) * herm 1 (x : Fin n → E) v)) := rfl
        rw [this]
        linear_combination (-herm 1 (x : Fin n → E) v) * h3 + (u : E) * herm 1 (x : Fin n → E) v * hrd
      show IsIntegral ℤ (herm 1 ((x : Fin n → E) - (u * e) • w) v)
      rw [h4]
      exact hint x x.2 c hc
  rw [relIndex_eq, ← hk, Hyper.index_ker _ f hf]
  exact hQ.2.2.1

/- English proof (translation)
Assemble the required witnesses or components as `⟨h, conj_le h.2.1 h'.1.2.1 h'.2.1, (index_symm hP h.2.1 h'.1.2.1 h'.2.1 (h'.2.2.trans hP.2.2.1)).trans (good_conj hP).2.2.1.symm⟩`.
-/
theorem nb_symm {M q : ℕ} {P : Ideal (𝓞 E)} (hP : GoodPrime M q P) {Λ Λ' : Lt E n}
    (h : Λ ∈ Vset E n M) (h' : Λ' ∈ Nb M P Λ) : Λ ∈ Nb M (conjI P) Λ' :=
  ⟨h, conj_le h.2.1 h'.1.2.1 h'.2.1, (index_symm hP h.2.1 h'.1.2.1 h'.2.1
    (h'.2.2.trans hP.2.2.1)).trans (good_conj hP).2.2.1.symm⟩

/- English proof (translation)
Use `max_of_norm hP.1 hP.2.2.1` as an intermediate fact. Use `proj h.1` as an intermediate fact. Establish `: Module.Finite (𝓞 E) Λ` using `Module.Finite.iff_fg.mpr h.1`. Establish `hc : Nat.card (𝓞 E ⧸ P) = q` using `hP.2.2.1`. Establish `: Finite (𝓞 E ⧸ P)` using `Nat.finite_of_card_ne_zero (hc ▸ hP.1.ne_zero)`.

Take `⟨h1, h2⟩` from `Hyper.count (M := Λ) P`. Rewrite `h2` using `[hc, finrank_eq h]`. Establish `hb : Set.BijOn (fun Λ' : Lt E n => Λ'.comap Λ.subtype) (Nb M P Λ) {N : Submodule (𝓞 E) Λ | ∃ f : Λ →ₗ[𝓞 E] 𝓞 E ⧸ P, f ≠ 0 ∧ LinearMap.ker f = N}`. Use `⟨fun Λ' h' => (index_iff hP.1 hP.2.2.1 _).1 ⟨fun c hc x => smul_le_iff.1 h'.2.1 c hc x x.2, h'.2.2.trans hP.2.2.1⟩, fun Λ' h' Λ'' h'' e => ?_, fun N hN => ?_⟩` and prove the remaining obligations. Establish `e'` using `congrArg (Submodule.map Λ.subtype) e`.

Simplify using `only [Submodule.map_comap_subtype] at e'`. Conclude with `(eq_nbOf hP h h').trans (e' ▸ (eq_nbOf hP h h'').symm)`. Take `⟨h3, h4⟩` from `(index_iff hP.1 hP.2.2.1 N).2 hN`. Establish `h5 : (N.map Λ.subtype).comap Λ.subtype = N` using `Submodule.comap_map_eq_of_injective Λ.injective_subtype N`. Establish `h6 : P • Λ ≤ N.map Λ.subtype` using `smul_le_iff.2 fun c hc x hx => ⟨_, h3 c hc ⟨x, hx⟩, rfl⟩`.

Establish `h7 : (N.map Λ.subtype).toAddSubgroup.relIndex Λ.toAddSubgroup = q`. Rewrite using `[relIndex_eq, h5, h4]`. Use `⟨_, nbOf_mem hP h h6 (Λ.map_subtype_le N) h7, ?_⟩` and prove the remaining obligations. Establish `h8` using `(nbOf_spec hP h h6 (Λ.map_subtype_le N) h7).2`. Use `Eq.trans ?_ h5` and prove the remaining obligations.

Use extensionality with `x`. Conclude with `⟨fun hx => h8.le ⟨x.2, hx⟩, fun hx => (h8.ge hx).2⟩`. Conclude with `⟨hb.finite_iff_finite.2 h1, by rw [hb.ncard_eq, h2]⟩`.
-/
theorem nb_count {M q : ℕ} {P : Ideal (𝓞 E)} (hP : GoodPrime M q P) {Λ : Lt E n}
    (h : Λ ∈ Vset E n M) : (Nb M P Λ).Finite ∧ (Nb M P Λ).ncard * (q - 1) = q ^ n - 1 := by
  have := max_of_norm hP.1 hP.2.2.1
  have := proj h.1
  have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr h.1
  have hc : Nat.card (𝓞 E ⧸ P) = q := hP.2.2.1
  have : Finite (𝓞 E ⧸ P) := Nat.finite_of_card_ne_zero (hc ▸ hP.1.ne_zero)
  obtain ⟨h1, h2⟩ := Hyper.count (M := Λ) P
  rw [hc, finrank_eq h] at h2
  have hb : Set.BijOn (fun Λ' : Lt E n => Λ'.comap Λ.subtype) (Nb M P Λ)
      {N : Submodule (𝓞 E) Λ | ∃ f : Λ →ₗ[𝓞 E] 𝓞 E ⧸ P, f ≠ 0 ∧ LinearMap.ker f = N} := by
    refine ⟨fun Λ' h' => (index_iff hP.1 hP.2.2.1 _).1
      ⟨fun c hc x => smul_le_iff.1 h'.2.1 c hc x x.2, h'.2.2.trans hP.2.2.1⟩,
      fun Λ' h' Λ'' h'' e => ?_, fun N hN => ?_⟩
    · have e' := congrArg (Submodule.map Λ.subtype) e
      simp only [Submodule.map_comap_subtype] at e'
      exact (eq_nbOf hP h h').trans (e' ▸ (eq_nbOf hP h h'').symm)
    · obtain ⟨h3, h4⟩ := (index_iff hP.1 hP.2.2.1 N).2 hN
      have h5 : (N.map Λ.subtype).comap Λ.subtype = N :=
        Submodule.comap_map_eq_of_injective Λ.injective_subtype N
      have h6 : P • Λ ≤ N.map Λ.subtype :=
        smul_le_iff.2 fun c hc x hx => ⟨_, h3 c hc ⟨x, hx⟩, rfl⟩
      have h7 : (N.map Λ.subtype).toAddSubgroup.relIndex Λ.toAddSubgroup = q := by
        rw [relIndex_eq, h5, h4]
      refine ⟨_, nbOf_mem hP h h6 (Λ.map_subtype_le N) h7, ?_⟩
      have h8 := (nbOf_spec hP h h6 (Λ.map_subtype_le N) h7).2
      refine Eq.trans ?_ h5
      ext x
      exact ⟨fun hx => h8.le ⟨x.2, hx⟩, fun hx => (h8.ge hx).2⟩
  exact ⟨hb.finite_iff_finite.2 h1, by rw [hb.ncard_eq, h2]⟩

/- English proof (translation)
Establish `h1 : ∀ x y : Fin n → E, herm 1 x y = (fun a => cc (y a)) ⬝ᵥ x` using `fun x y => by`. Rewrite using `[herm_one, dotProduct_comm]`. Both sides reduce to the same expression. Establish `h2 : (fun a => cc ((h *ᵥ y) a)) = (fun a => cc (y a)) ᵥ* ccT h`. Use extensionality with `a`.

Simplify using `[cc, ccT, Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm]`. Rewrite using `[h1, h1, h2, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hh, Matrix.one_mulVec]`.
-/
theorem herm_move {h : Matrix (Fin n) (Fin n) E} (hh : ccT h * h = 1) (x y : Fin n → E) :
    herm 1 (h *ᵥ x) (h *ᵥ y) = herm 1 x y := by
  have h1 : ∀ x y : Fin n → E, herm 1 x y = (fun a => cc (y a)) ⬝ᵥ x := fun x y => by
    rw [herm_one, dotProduct_comm]; rfl
  have h2 : (fun a => cc ((h *ᵥ y) a)) = (fun a => cc (y a)) ᵥ* ccT h := by
    ext a
    simp [cc, ccT, Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm]
  rw [h1, h1, h2, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hh, Matrix.one_mulVec]

/- English proof (translation)
Introduce `v` and use `by rw [hm, Matrix.mulVec_mulVec, hh, Matrix.one_mulVec]`.
-/
theorem move_inv {h : Matrix (Fin n) (Fin n) E} (hh : h * ccT h = 1) {Λ Λ₁ : Lt E n}
    (hm : Moves h Λ Λ₁) : Moves (ccT h) Λ₁ Λ := fun v => by
  rw [hm, Matrix.mulVec_mulVec, hh, Matrix.one_mulVec]

/- English proof (translation)
Establish `hs : ∀ x : Fin n → E, ∃ y, h *ᵥ y = x` using `fun x => ⟨g *ᵥ x, by rw [Matrix.mulVec_mulVec, hg, Matrix.one_mulVec]⟩`. Establish `hS' : SD Λ'` using `h'.1.2.1`. Use `(mem_Nb hP h₁).2 ⟨fun x => ?_, smul_le_iff.2 fun c hc x hx => ?_, ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `hs x`. Rewrite using `[← hm', hS']`.

Prove the components needed by the constructor for the conclusion. Introduce `H y hy`. Take `⟨y, rfl⟩` from `hs y`. Unfold `Int'`. Rewrite using `[hh]`.

Conclude with `H y ((hm' y).2 hy)`. Introduce `H y hy`. Use `H _ ((hm' y).1 hy)` as an intermediate fact. Unfold `Int' at this ⊢`. Rewrite `this` using `[hh]`. Then use the resulting hypothesis.

Take `⟨x, rfl⟩` from `hs x`. Rewrite using `[osmul, ← Matrix.mulVec_smul, ← hm']`. Conclude with `smul_le_iff.1 h'.2.1 c hc x ((hm x).2 hx)`. Set `φ : (Fin n → E) →+ (Fin n → E)` to `(Matrix.mulVecLin h).toAddMonoidHom`. Establish `e1 : Λ'.toAddSubgroup = Λ₁'.toAddSubgroup.comap φ` using `AddSubgroup.ext hm'`.

Establish `e2 : Λ.toAddSubgroup = Λ₁.toAddSubgroup.comap φ` using `AddSubgroup.ext hm`. Rewrite using `[← hP.2.2.1, ← h'.2.2, e1, e2, AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective (f := φ) hs]`.
-/
theorem nb_move {M q : ℕ} {P : Ideal (𝓞 E)} (hP : GoodPrime M q P)
    {h g : Matrix (Fin n) (Fin n) E} (hh : ∀ x y, herm 1 (h *ᵥ x) (h *ᵥ y) = herm 1 x y)
    (hg : h * g = 1) {Λ Λ₁ Λ' Λ₁' : Lt E n} (h₁ : Λ₁ ∈ Vset E n M) (hm : Moves h Λ Λ₁)
    (hm' : Moves h Λ' Λ₁') (h' : Λ' ∈ Nb M P Λ) : Λ₁' ∈ Nb M P Λ₁ := by
  have hs : ∀ x : Fin n → E, ∃ y, h *ᵥ y = x := fun x =>
    ⟨g *ᵥ x, by rw [Matrix.mulVec_mulVec, hg, Matrix.one_mulVec]⟩
  have hS' : SD Λ' := h'.1.2.1
  refine (mem_Nb hP h₁).2 ⟨fun x => ?_, smul_le_iff.2 fun c hc x hx => ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := hs x
    rw [← hm', hS']
    constructor
    · intro H y hy
      obtain ⟨y, rfl⟩ := hs y
      unfold Int'
      rw [hh]
      exact H y ((hm' y).2 hy)
    · intro H y hy
      have := H _ ((hm' y).1 hy)
      unfold Int' at this ⊢
      rwa [hh] at this
  · obtain ⟨x, rfl⟩ := hs x
    rw [osmul, ← Matrix.mulVec_smul, ← hm']
    exact smul_le_iff.1 h'.2.1 c hc x ((hm x).2 hx)
  · let φ : (Fin n → E) →+ (Fin n → E) := (Matrix.mulVecLin h).toAddMonoidHom
    have e1 : Λ'.toAddSubgroup = Λ₁'.toAddSubgroup.comap φ := AddSubgroup.ext hm'
    have e2 : Λ.toAddSubgroup = Λ₁.toAddSubgroup.comap φ := AddSubgroup.ext hm
    rw [← hP.2.2.1, ← h'.2.2, e1, e2, AddSubgroup.relIndex_comap,
      AddSubgroup.map_comap_eq_self_of_surjective (f := φ) hs]

end GlobalTheory.SW.Nbr

namespace GlobalTheory.SW

/- English proof (translation)
Introduce `E _ _ _ n M q P _ hP`. Use `⟨Nbr.good_conj hP, Nbr.conjI_conjI P, fun Λ h => ⟨(Nbr.nb_count hP h).1, (Nbr.nb_count hP h).2, fun Λ' h' => ⟨Nbr.nb_symm hP h, fun H => ?_⟩, fun Λ₀ h1 h2 h3 => ?_, fun Λ' h' m hm => ?_, fun g hg Λ₁ h₁ hm Λ' Λ₁' hm' => ?_⟩⟩` and prove the remaining obligations. Use `Nbr.nb_symm (Nbr.good_conj hP) h' H` as an intermediate fact. Rewrite `this` using `[Nbr.conjI_conjI]`. Then use the resulting hypothesis. Use `⟨Nbr.nbOf P Λ₀, ⟨Nbr.nbOf_mem hP h h1 h2 h3, (Nbr.nbOf_spec hP h h1 h2 h3).2⟩, ?_⟩` and prove the remaining obligations.

Introduce and unpack `Λ' ⟨h', rfl⟩`. Conclude with `Nbr.eq_nbOf hP h h'`. Conclude with `Nbr.agree_of_le hP hm h.2.1 h'.1.2.1 h'.2.1`. Establish `hg' : g * ccT g = 1` using `mul_eq_one_comm.1 hg.1`. Use `⟨Nbr.nb_move hP (Nbr.herm_move hg.1) hg' h₁ hm hm', Nbr.nb_move hP (fun x y => ?_) hg.1 h (Nbr.move_inv hg' hm) (Nbr.move_inv hg' hm')⟩` and prove the remaining obligations.

Rewrite using `[← Nbr.herm_move hg.1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg', Matrix.one_mulVec, Matrix.one_mulVec]`.
-/
theorem neighbours : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n M q : ℕ) (P : Ideal (𝓞 E)), 0 < M → GoodPrime M q P → GoodPrime M q (conjI P) ∧ conjI (conjI P) = P ∧ ∀ Λ ∈ Vset E n M, (Nb M P Λ).Finite ∧ (Nb M P Λ).ncard * (q - 1) = q ^ n - 1 ∧ (∀ Λ' ∈ Vset E n M, Λ' ∈ Nb M P Λ ↔ Λ ∈ Nb M (conjI P) Λ') ∧ (∀ Λ₀ : Lt E n, P • Λ ≤ Λ₀ → Λ₀ ≤ Λ → Λ₀.toAddSubgroup.relIndex Λ.toAddSubgroup = q → ∃! Λ', Λ' ∈ Nb M P Λ ∧ Λ ⊓ Λ' = Λ₀) ∧ (∀ Λ' ∈ Nb M P Λ, ∀ m : ℕ, q.Coprime m → Agree m Λ Λ') ∧ ∀ h ∈ DH E n M, ∀ Λ₁ ∈ Vset E n M, Moves h Λ Λ₁ → ∀ Λ' Λ₁' : Lt E n, Moves h Λ' Λ₁' → (Λ' ∈ Nb M P Λ ↔ Λ₁' ∈ Nb M P Λ₁) := by
  intro E _ _ _ n M q P _ hP
  refine ⟨Nbr.good_conj hP, Nbr.conjI_conjI P, fun Λ h => ⟨(Nbr.nb_count hP h).1, (Nbr.nb_count hP h).2,
    fun Λ' h' => ⟨Nbr.nb_symm hP h, fun H => ?_⟩, fun Λ₀ h1 h2 h3 => ?_, fun Λ' h' m hm => ?_,
    fun g hg Λ₁ h₁ hm Λ' Λ₁' hm' => ?_⟩⟩
  · have := Nbr.nb_symm (Nbr.good_conj hP) h' H
    rwa [Nbr.conjI_conjI] at this
  · refine ⟨Nbr.nbOf P Λ₀, ⟨Nbr.nbOf_mem hP h h1 h2 h3, (Nbr.nbOf_spec hP h h1 h2 h3).2⟩, ?_⟩
    rintro Λ' ⟨h', rfl⟩
    exact Nbr.eq_nbOf hP h h'
  · exact Nbr.agree_of_le hP hm h.2.1 h'.1.2.1 h'.2.1
  · have hg' : g * ccT g = 1 := mul_eq_one_comm.1 hg.1
    refine ⟨Nbr.nb_move hP (Nbr.herm_move hg.1) hg' h₁ hm hm',
      Nbr.nb_move hP (fun x y => ?_) hg.1 h (Nbr.move_inv hg' hm) (Nbr.move_inv hg' hm')⟩
    rw [← Nbr.herm_move hg.1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg', Matrix.one_mulVec,
      Matrix.one_mulVec]

end GlobalTheory.SW
