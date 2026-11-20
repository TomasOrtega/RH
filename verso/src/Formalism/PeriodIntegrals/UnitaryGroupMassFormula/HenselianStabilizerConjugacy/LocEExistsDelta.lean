import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HenselianStabilizerConjugacy.IsSelfDual

noncomputable section

open scoped Classical
set_option linter.style.haveILetI false
open ValuativeRel

namespace PI.SelfDualHermitianLattices.Hd

open Formalism.MainNotions.S.Loc

section Alg

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

/- English proof (translation)
Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_nontrivial_iff_subsingleton]`. Use `L.rank` as an intermediate fact. Rewrite `this` using `[Module.finrank_zero_of_subsingleton]`. Use linear arithmetic over natural numbers and integers.
-/
theorem locE_nontrivial (L : LocE F E) : Nontrivial E := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have := L.rank
  rw [Module.finrank_zero_of_subsingleton] at this
  omega

/- English proof (translation)
Rewrite `hx`, the goal using `[L.O_def]`. Conclude with `hx.map ((L.cj : E →ₐ[F] E).restrictScalars 𝒪[F])`.
-/
theorem locE_cj_mem (L : LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [L.O_def] at hx ⊢
  exact hx.map ((L.cj : E →ₐ[F] E).restrictScalars 𝒪[F])

/- English proof (translation)
Use `haveI := locE_nontrivial L`. Rewrite using `[L.O_def]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h' : IsIntegral 𝒪[F] f` using `(isIntegral_algHom_iff ((Algebra.ofId F E).restrictScalars 𝒪[F]) (algebraMap F E).injective).mp h`.

Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.mp h'`. Rewrite using `[← hy]`. Conclude with `y.2`. Introduce `h`. Establish `: algebraMap F E f = algebraMap 𝒪[F] E ⟨f, h⟩`.

Rewrite using `[IsScalarTower.algebraMap_apply 𝒪[F] F E]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `isIntegral_algebraMap`.
-/
theorem locE_algMap_mem (L : LocE F E) [IsNonarchimedeanLocalField F] {f : F} :
    algebraMap F E f ∈ L.O ↔ f ∈ 𝒪[F] := by
  haveI := locE_nontrivial L
  rw [L.O_def]
  constructor
  · intro h
    have h' : IsIntegral 𝒪[F] f :=
      (isIntegral_algHom_iff ((Algebra.ofId F E).restrictScalars 𝒪[F])
        (algebraMap F E).injective).mp h
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h'
    rw [← hy]; exact y.2
  · intro h
    have : algebraMap F E f = algebraMap 𝒪[F] E ⟨f, h⟩ := by
      rw [IsScalarTower.algebraMap_apply 𝒪[F] F E]; rfl
    rw [this]; exact isIntegral_algebraMap

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Establish `h1 : Module.finrank F E ≤ 1`. Apply `finrank_le_one (1 : E)` to reduce the goal to its premises. Introduce `w`.

Take `⟨c, hc⟩` from `h w`. Conclude with `⟨c, by rw [Algebra.smul_def, mul_one, hc]⟩`. Use `L.rank` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem locE_exists_nonF (L : LocE F E) : ∃ s : E, s ∉ Set.range (algebraMap F E) := by
  by_contra h
  push Not at h
  have h1 : Module.finrank F E ≤ 1 := by
    apply finrank_le_one (1 : E)
    intro w
    obtain ⟨c, hc⟩ := h w
    exact ⟨c, by rw [Algebra.smul_def, mul_one, hc]⟩
  have := L.rank
  omega

/- English proof (translation)
Use `haveI := locE_nontrivial L`. Use `haveI := L.reduced`. Take `⟨s, hs⟩` from `locE_exists_nonF L`. Use `set δ0 := s - L.cj s with hδ0`. Establish `hcj0 : L.cj δ0 = -δ0` using `by rw [hδ0, map_sub, L.cj_cj]; ring`.

Establish `hne0 : δ0 ≠ 0`. Introduce `h0`. Apply `hs` to reduce the goal to its premises. Establish `: L.cj s = s` using `by rw [hδ0, sub_eq_zero] at h0; exact h0.symm`. Take `⟨a, ha⟩` from `(L.cj_fix s).mp this`.

Conclude with `⟨a, ha⟩`. Establish `hfix : L.cj (δ0 * δ0) = δ0 * δ0` using `by rw [map_mul, hcj0]; ring`. Take `⟨d0, hd0⟩` from `(L.cj_fix _).mp hfix`. Establish `hd0ne : d0 ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hd0` using `[map_zero]`. Apply `hne0` to reduce the goal to its premises. Establish `: IsNilpotent δ0` using `⟨2, by rw [pow_two]; exact hd0.symm⟩`. Conclude with `this.eq_zero`. Take `⟨a, b, hb, hab⟩` from `IsFractionRing.div_surjective (A := 𝒪[F]) d0`.

Establish `hb0 : (b : F) ≠ 0`. Introduce `h`. Establish `: b = 0` using `Subtype.ext h`. Conclude with `(nonZeroDivisors.ne_zero hb) this`. Establish `hmem : (b : F) * (b : F) * d0 ∈ 𝒪[F]`.

Rewrite using `[← hab]`. Establish `: (b : F) * (b : F) * (algebraMap 𝒪[F] F a / algebraMap 𝒪[F] F b) = (b : F) * (a : F)`. Express the relevant statement in the definitionally equal form `(b : F) * (b : F) * ((a : F) / (b : F)) = (b : F) * (a : F)`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`.

Conclude with `mul_mem b.2 a.2`. Use `⟨algebraMap F E (b : F) * δ0, ?_, ?_, ?_, (b : F) * (b : F) * d0, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[L.O_def]`. Apply `IsIntegral.of_pow (n := 2) (by norm_num)` to reduce the goal to its premises. Establish `: (algebraMap F E (b : F) * δ0) ^ 2 = algebraMap F E ((b : F) * (b : F) * d0)`.

Rewrite using `[map_mul, map_mul, hd0]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, ← L.O_def]`. Conclude with `(locE_algMap_mem L).mpr hmem`. Introduce `h`.

Apply `hne0` to reduce the goal to its premises. Establish `: algebraMap F E (b : F)⁻¹ * (algebraMap F E (b : F) * δ0) = δ0`. Rewrite using `[← mul_assoc, ← map_mul, inv_mul_cancel₀ hb0, map_one, one_mul]`. Rewrite using `[← this, h, mul_zero]`. Rewrite using `[map_mul, hcj0, AlgEquiv.commutes]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `mul_ne_zero (mul_ne_zero hb0 hb0) hd0ne`. Rewrite using `[map_mul, map_mul, hd0]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem locE_exists_delta (L : LocE F E) [IsNonarchimedeanLocalField F] :
    ∃ δ : E, δ ∈ L.O ∧ δ ≠ 0 ∧ L.cj δ = -δ ∧ ∃ d : F, d ≠ 0 ∧ δ * δ = algebraMap F E d := by
  haveI := locE_nontrivial L
  haveI := L.reduced
  obtain ⟨s, hs⟩ := locE_exists_nonF L
  set δ0 := s - L.cj s with hδ0
  have hcj0 : L.cj δ0 = -δ0 := by rw [hδ0, map_sub, L.cj_cj]; ring
  have hne0 : δ0 ≠ 0 := by
    intro h0
    apply hs
    have : L.cj s = s := by rw [hδ0, sub_eq_zero] at h0; exact h0.symm
    obtain ⟨a, ha⟩ := (L.cj_fix s).mp this
    exact ⟨a, ha⟩
  have hfix : L.cj (δ0 * δ0) = δ0 * δ0 := by rw [map_mul, hcj0]; ring
  obtain ⟨d0, hd0⟩ := (L.cj_fix _).mp hfix
  have hd0ne : d0 ≠ 0 := by
    rintro rfl
    rw [map_zero] at hd0
    apply hne0
    have : IsNilpotent δ0 := ⟨2, by rw [pow_two]; exact hd0.symm⟩
    exact this.eq_zero
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝒪[F]) d0
  have hb0 : (b : F) ≠ 0 := by
    intro h
    have : b = 0 := Subtype.ext h
    exact (nonZeroDivisors.ne_zero hb) this
  have hmem : (b : F) * (b : F) * d0 ∈ 𝒪[F] := by
    rw [← hab]
    have : (b : F) * (b : F) * (algebraMap 𝒪[F] F a / algebraMap 𝒪[F] F b) = (b : F) * (a : F) := by
      change (b : F) * (b : F) * ((a : F) / (b : F)) = (b : F) * (a : F)
      field_simp
    rw [this]; exact mul_mem b.2 a.2
  refine ⟨algebraMap F E (b : F) * δ0, ?_, ?_, ?_, (b : F) * (b : F) * d0, ?_, ?_⟩
  · rw [L.O_def]
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    have : (algebraMap F E (b : F) * δ0) ^ 2 = algebraMap F E ((b : F) * (b : F) * d0) := by
      rw [map_mul, map_mul, hd0]; ring
    rw [this, ← L.O_def]
    exact (locE_algMap_mem L).mpr hmem
  · intro h
    apply hne0
    have : algebraMap F E (b : F)⁻¹ * (algebraMap F E (b : F) * δ0) = δ0 := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hb0, map_one, one_mul]
    rw [← this, h, mul_zero]
  · rw [map_mul, hcj0, AlgEquiv.commutes]; ring
  · exact mul_ne_zero (mul_ne_zero hb0 hb0) hd0ne
  · rw [map_mul, map_mul, hd0]; ring

end Alg

section Alg2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

/- English proof (translation)
Establish `h1 : L.cj (x + L.cj x) = x + L.cj x` using `by rw [map_add, L.cj_cj, add_comm]`. Take `⟨A, hA⟩` from `(L.cj_fix _).mp h1`. Establish `h2 : L.cj ((x - L.cj x) * δ) = (x - L.cj x) * δ`. Rewrite using `[map_mul, map_sub, L.cj_cj, hcj]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨Bc, hB⟩` from `(L.cj_fix _).mp h2`. Use `⟨A / 2, Bc / (2 * d), ?_⟩` and prove the remaining obligations. Establish `h2ne : (2 : F) ≠ 0` using `two_ne_zero`. Establish `hu : IsUnit (algebraMap F E (2 * d))` using `(IsUnit.mk0 _ (mul_ne_zero h2ne hd0)).map _`. Apply `hu.mul_left_cancel` to reduce the goal to its premises.

Rewrite using `[mul_add, ← mul_assoc, ← map_mul, ← map_mul]`. Establish `e1 : 2 * d * (A / 2) = d * A` using `by field_simp`. Establish `e2 : 2 * d * (Bc / (2 * d)) = Bc` using `by field_simp`. Rewrite using `[e1, e2, map_mul, map_mul, hA, hB, map_ofNat]`. Take the linear combination `(-(x - L.cj x)) * hd`.
-/
theorem locE_decomp (L : LocE F E) [CharZero F] {δ : E} (hcj : L.cj δ = -δ) {d : F} (hd0 : d ≠ 0)
    (hd : δ * δ = algebraMap F E d) (x : E) :
    ∃ a b : F, x = algebraMap F E a + algebraMap F E b * δ := by
  have h1 : L.cj (x + L.cj x) = x + L.cj x := by rw [map_add, L.cj_cj, add_comm]
  obtain ⟨A, hA⟩ := (L.cj_fix _).mp h1
  have h2 : L.cj ((x - L.cj x) * δ) = (x - L.cj x) * δ := by
    rw [map_mul, map_sub, L.cj_cj, hcj]; ring
  obtain ⟨Bc, hB⟩ := (L.cj_fix _).mp h2
  refine ⟨A / 2, Bc / (2 * d), ?_⟩
  have h2ne : (2 : F) ≠ 0 := two_ne_zero
  have hu : IsUnit (algebraMap F E (2 * d)) := (IsUnit.mk0 _ (mul_ne_zero h2ne hd0)).map _
  apply hu.mul_left_cancel
  rw [mul_add, ← mul_assoc, ← map_mul, ← map_mul]
  have e1 : 2 * d * (A / 2) = d * A := by field_simp
  have e2 : 2 * d * (Bc / (2 * d)) = Bc := by field_simp
  rw [e1, e2, map_mul, map_mul, hA, hB, map_ofNat]
  linear_combination (-(x - L.cj x)) * hd

structure QBasis (L : LocE F E) where
  ω : E
  hω : ω ∈ L.O
  hnot : ω ∉ Set.range (algebraMap F E)
  t : 𝒪[F]
  n : 𝒪[F]
  hcj : L.cj ω = algebraMap F E (t : F) - ω
  hn : ω * L.cj ω = algebraMap F E (n : F)
  span : ∀ x ∈ L.O, ∃ a b : 𝒪[F], x = algebraMap F E (a : F) + algebraMap F E (b : F) * ω

/- English proof (translation)
Use `Q.hn` as an intermediate fact. Rewrite `this` using `[Q.hcj]`. Rewrite using `[← this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem QBasis.sq {L : LocE F E} (Q : QBasis L) :
    Q.ω * Q.ω = algebraMap F E (Q.t : F) * Q.ω - algebraMap F E (Q.n : F) := by
  have := Q.hn; rw [Q.hcj] at this; rw [← this]; ring

/- English proof (translation)
Take `⟨δ, hδO, hδ0, hcj, d, hd0, hd⟩` from `locE_exists_delta L`. Use `set e : F := (2 * d)⁻¹ with he`. Establish `he0 : e ≠ 0` using `inv_ne_zero (mul_ne_zero two_ne_zero hd0)`. Set `I : Ideal 𝒪[F]` to `{ carrier := {c | ∃ a : F, algebraMap F E a + algebraMap F E ((c : F) * e) * δ ∈ L.O} add_mem' := by`. Introduce and unpack `c1 c2 ⟨a1, h1⟩ ⟨a2, h2⟩`.

Use `⟨a1 + a2, ?_⟩` and prove the remaining obligations. Establish `: algebraMap F E (a1 + a2) + algebraMap F E (((c1 + c2 : 𝒪[F]) : F) * e) * δ = (algebraMap F E a1 + algebraMap F E ((c1 : F) * e) * δ) + (algebraMap F E a2 + algebraMap F E ((c2 : F) * e) * δ)` using `by push_cast; simp only [map_add, add_mul, map_mul]; ring`. Rewrite using `[this]`. Conclude with `add_mem h1 h2`. Use the proof step `zero_mem' := ⟨0, by simp⟩`.

Use the proof step `smul_mem' := by`. Introduce and unpack `c x ⟨a, h⟩`. Use `⟨(c : F) * a, ?_⟩` and prove the remaining obligations. Establish `: algebraMap F E ((c : F) * a) + algebraMap F E (((c • x : 𝒪[F]) : F) * e) * δ = algebraMap F E (c : F) * (algebraMap F E a + algebraMap F E ((x : F) * e) * δ)`. Simplify using `only [smul_eq_mul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `mul_mem ((locE_algMap_mem L).mpr c.2) h }`. Establish `hcoord : ∀ x ∈ L.O, ∀ a b : F, x = algebraMap F E a + algebraMap F E b * δ → ∃ c : 𝒪[F], c ∈ I ∧ (c : F) * e = b`.

Introduce `x hx a b hxab`. Establish `hm : (x - L.cj x) * δ = algebraMap F E (2 * b * d)`. Rewrite using `[hxab, map_add, map_mul, hcj, AlgEquiv.commutes, AlgEquiv.commutes, map_mul, map_mul, ← hd, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree. Establish `hmem : 2 * b * d ∈ 𝒪[F]`.

Rewrite using `[← locE_algMap_mem L, ← hm]`. Conclude with `mul_mem (sub_mem hx (locE_cj_mem L hx)) hδO`. Use `⟨⟨2 * b * d, hmem⟩, ⟨a, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `: (2 * b * d) * e = b` using `by rw [he]; field_simp`. Simplify using `only [this]`.

Rewrite using `[← hxab]`. Conclude with `hx`. Use `show 2 * b * d * e = b`. Rewrite using `[he]`. Clear the denominators using the available nonvanishing facts.

Use `set c0 := Submodule.IsPrincipal.generator I with hc0`. Establish `hI : I = Ideal.span {c0}` using `(Ideal.span_singleton_generator I).symm`. Take `⟨a0, ha0⟩ : c0 ∈ I` from `Submodule.IsPrincipal.generator_mem I`. Establish `hc0ne : (c0 : F) ≠ 0`. Introduce `h`.

Establish `hc : c0 = 0` using `Subtype.ext h`. Rewrite `hc` using `[← Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero]`. Take `⟨c, hcI, hce⟩` from `hcoord δ hδO 0 1 (by simp)`. Rewrite `hcI` using `[hc]`. Establish `: c = 0` using `(Submodule.mem_bot _).mp hcI`.

Rewrite `hce` using `[this]`. Simplify using `at hce`. Use `set ω := algebraMap F E a0 + algebraMap F E ((c0 : F) * e) * δ with hωdef`. Establish `hnot : ω ∉ Set.range (algebraMap F E)`. Introduce and unpack `⟨f, hf⟩`.

Establish `hce : (c0 : F) * e ≠ 0` using `mul_ne_zero hc0ne he0`. Establish `hδF : δ = algebraMap F E ((f - a0) / ((c0 : F) * e))`. Establish `hu : IsUnit (algebraMap F E ((c0 : F) * e))` using `(IsUnit.mk0 _ hce).map _`. Apply `hu.mul_left_cancel` to reduce the goal to its premises. Rewrite using `[← map_mul, mul_div_cancel₀ _ hce, map_sub, hf, hωdef]`.

Expand and normalize the polynomial expressions, which then agree. Apply `hδ0` to reduce the goal to its premises. Establish `h2 : L.cj δ = δ` using `by rw [hδF, AlgEquiv.commutes]`. Rewrite `h2` using `[hcj]`. Establish `: (2 : E) * δ = 0` using `by linear_combination (-1 : E) * h2`.

Establish `h2u : IsUnit (2 : E)`. Use `((IsUnit.mk0 (2 : F) two_ne_zero).map (algebraMap F E))` as an intermediate fact. Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis. Conclude with `(h2u.mul_right_eq_zero).mp this`. Establish `hfixT : L.cj (ω + L.cj ω) = ω + L.cj ω` using `by rw [map_add, L.cj_cj, add_comm]`.

Take `⟨T, hT⟩` from `(L.cj_fix _).mp hfixT`. Establish `hfixN : L.cj (ω * L.cj ω) = ω * L.cj ω` using `by rw [map_mul, L.cj_cj, mul_comm]`. Take `⟨Nn, hN⟩` from `(L.cj_fix _).mp hfixN`. Establish `hTm : T ∈ 𝒪[F]` using `by rw [← locE_algMap_mem L, hT]; exact add_mem ha0 (locE_cj_mem L ha0)`. Establish `hNm : Nn ∈ 𝒪[F]` using `by rw [← locE_algMap_mem L, hN]; exact mul_mem ha0 (locE_cj_mem L ha0)`.

Use `⟨⟨ω, ha0, hnot, ⟨T, hTm⟩, ⟨Nn, hNm⟩, ?_, hN.symm, ?_⟩⟩` and prove the remaining obligations. Use `show L.cj ω = algebraMap F E T - ω`. Rewrite using `[hT]`. Expand and normalize the polynomial expressions, which then agree. Introduce `x hx`.

Take `⟨a, b, hab⟩` from `locE_decomp L hcj hd0 hd x`. Take `⟨c, hcI, hce⟩` from `hcoord x hx a b hab`. Rewrite `hcI` using `[hI]`. Take `⟨m, hm⟩` from `Ideal.mem_span_singleton'.mp hcI`. Establish `hrest : x - algebraMap F E (m : F) * ω = algebraMap F E (a - (m : F) * a0)`.

Rewrite using `[hab, hωdef, ← hce, ← hm]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hmem : a - (m : F) * a0 ∈ 𝒪[F]`. Rewrite using `[← locE_algMap_mem L, ← hrest]`.

Conclude with `sub_mem hx (mul_mem ((locE_algMap_mem L).mpr m.2) ha0)`. Use `⟨⟨_, hmem⟩, m, ?_⟩` and prove the remaining obligations. Use `show x = algebraMap F E (a - (m : F) * a0) + algebraMap F E (m : F) * ω`. Rewrite using `[← hrest]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem locE_qbasis (L : LocE F E) [IsNonarchimedeanLocalField F] [CharZero F] : Nonempty (QBasis L) := by
  obtain ⟨δ, hδO, hδ0, hcj, d, hd0, hd⟩ := locE_exists_delta L
  set e : F := (2 * d)⁻¹ with he
  have he0 : e ≠ 0 := inv_ne_zero (mul_ne_zero two_ne_zero hd0)
  let I : Ideal 𝒪[F] :=
    { carrier := {c | ∃ a : F, algebraMap F E a + algebraMap F E ((c : F) * e) * δ ∈ L.O}
      add_mem' := by
        rintro c1 c2 ⟨a1, h1⟩ ⟨a2, h2⟩
        refine ⟨a1 + a2, ?_⟩
        have : algebraMap F E (a1 + a2) + algebraMap F E (((c1 + c2 : 𝒪[F]) : F) * e) * δ =
            (algebraMap F E a1 + algebraMap F E ((c1 : F) * e) * δ) +
              (algebraMap F E a2 + algebraMap F E ((c2 : F) * e) * δ) := by
          push_cast; simp only [map_add, add_mul, map_mul]; ring
        rw [this]; exact add_mem h1 h2
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c x ⟨a, h⟩
        refine ⟨(c : F) * a, ?_⟩
        have : algebraMap F E ((c : F) * a) + algebraMap F E (((c • x : 𝒪[F]) : F) * e) * δ =
            algebraMap F E (c : F) * (algebraMap F E a + algebraMap F E ((x : F) * e) * δ) := by
          simp only [smul_eq_mul]; push_cast; ring
        rw [this]; exact mul_mem ((locE_algMap_mem L).mpr c.2) h }

  have hcoord : ∀ x ∈ L.O, ∀ a b : F, x = algebraMap F E a + algebraMap F E b * δ →
      ∃ c : 𝒪[F], c ∈ I ∧ (c : F) * e = b := by
    intro x hx a b hxab
    have hm : (x - L.cj x) * δ = algebraMap F E (2 * b * d) := by
      rw [hxab, map_add, map_mul, hcj, AlgEquiv.commutes, AlgEquiv.commutes, map_mul, map_mul, ← hd,
        map_ofNat]; ring
    have hmem : 2 * b * d ∈ 𝒪[F] := by
      rw [← locE_algMap_mem L, ← hm]
      exact mul_mem (sub_mem hx (locE_cj_mem L hx)) hδO
    refine ⟨⟨2 * b * d, hmem⟩, ⟨a, ?_⟩, ?_⟩
    · have : (2 * b * d) * e = b := by rw [he]; field_simp
      simp only [this]; rw [← hxab]; exact hx
    · show 2 * b * d * e = b
      rw [he]; field_simp
  set c0 := Submodule.IsPrincipal.generator I with hc0
  have hI : I = Ideal.span {c0} := (Ideal.span_singleton_generator I).symm
  obtain ⟨a0, ha0⟩ : c0 ∈ I := Submodule.IsPrincipal.generator_mem I
  have hc0ne : (c0 : F) ≠ 0 := by
    intro h
    have hc : c0 = 0 := Subtype.ext h
    rw [← Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero] at hc
    obtain ⟨c, hcI, hce⟩ := hcoord δ hδO 0 1 (by simp)
    rw [hc] at hcI
    have : c = 0 := (Submodule.mem_bot _).mp hcI
    rw [this] at hce; simp at hce
  set ω := algebraMap F E a0 + algebraMap F E ((c0 : F) * e) * δ with hωdef
  have hnot : ω ∉ Set.range (algebraMap F E) := by
    rintro ⟨f, hf⟩
    have hce : (c0 : F) * e ≠ 0 := mul_ne_zero hc0ne he0
    have hδF : δ = algebraMap F E ((f - a0) / ((c0 : F) * e)) := by
      have hu : IsUnit (algebraMap F E ((c0 : F) * e)) := (IsUnit.mk0 _ hce).map _
      apply hu.mul_left_cancel
      rw [← map_mul, mul_div_cancel₀ _ hce, map_sub, hf, hωdef]; ring
    apply hδ0
    have h2 : L.cj δ = δ := by rw [hδF, AlgEquiv.commutes]
    rw [hcj] at h2
    have : (2 : E) * δ = 0 := by linear_combination (-1 : E) * h2
    have h2u : IsUnit (2 : E) := by
      have := ((IsUnit.mk0 (2 : F) two_ne_zero).map (algebraMap F E)); rwa [map_ofNat] at this
    exact (h2u.mul_right_eq_zero).mp this
  have hfixT : L.cj (ω + L.cj ω) = ω + L.cj ω := by rw [map_add, L.cj_cj, add_comm]
  obtain ⟨T, hT⟩ := (L.cj_fix _).mp hfixT
  have hfixN : L.cj (ω * L.cj ω) = ω * L.cj ω := by rw [map_mul, L.cj_cj, mul_comm]
  obtain ⟨Nn, hN⟩ := (L.cj_fix _).mp hfixN
  have hTm : T ∈ 𝒪[F] := by rw [← locE_algMap_mem L, hT]; exact add_mem ha0 (locE_cj_mem L ha0)
  have hNm : Nn ∈ 𝒪[F] := by rw [← locE_algMap_mem L, hN]; exact mul_mem ha0 (locE_cj_mem L ha0)
  refine ⟨⟨ω, ha0, hnot, ⟨T, hTm⟩, ⟨Nn, hNm⟩, ?_, hN.symm, ?_⟩⟩
  · show L.cj ω = algebraMap F E T - ω
    rw [hT]; ring
  · intro x hx
    obtain ⟨a, b, hab⟩ := locE_decomp L hcj hd0 hd x
    obtain ⟨c, hcI, hce⟩ := hcoord x hx a b hab
    rw [hI] at hcI
    obtain ⟨m, hm⟩ := Ideal.mem_span_singleton'.mp hcI
    have hrest : x - algebraMap F E (m : F) * ω = algebraMap F E (a - (m : F) * a0) := by
      rw [hab, hωdef, ← hce, ← hm]; push_cast; ring
    have hmem : a - (m : F) * a0 ∈ 𝒪[F] := by
      rw [← locE_algMap_mem L, ← hrest]
      exact sub_mem hx (mul_mem ((locE_algMap_mem L).mpr m.2) ha0)
    refine ⟨⟨_, hmem⟩, m, ?_⟩
    show x = algebraMap F E (a - (m : F) * a0) + algebraMap F E (m : F) * ω
    rw [← hrest]; ring

end Alg2

section Alg3

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

/- English proof (translation)
Distinguish the cases in `h2 : IsUnit (2 : 𝒪[F])`. Take `⟨u, hu⟩` from `h2`. Establish `hmul : (u : 𝒪[F]) * ↑u⁻¹ = 1` using `u.mul_inv`. Use `⟨-(t * ↑u⁻¹), ?_, ?_⟩` and prove the remaining obligations. Establish `: t + 2 * -(t * ↑u⁻¹) = 0`.

Take the linear combination `(-t) * hmul + (t * ↑u⁻¹) * hu`. Rewrite using `[this]`. Conclude with `zero_mem _`. Establish `: -(t * ↑u⁻¹) * -(t * ↑u⁻¹) - n = ↑u⁻¹ * ↑u⁻¹ * (t * t - 4 * n)`. Take the linear combination `(n * ((u : 𝒪[F]) * ↑u⁻¹ + 1)) * hmul + (-(n * ↑u⁻¹ * ↑u⁻¹ * ((u : 𝒪[F]) + 2))) * hu`.

Rewrite using `[this]`. Conclude with `Ideal.mul_mem_left _ _ hΔ`. Establish `h2m : (2 : 𝒪[F]) ∈ 𝓂[F]` using `(IsLocalRing.mem_maximalIdeal _).mpr h2`. Establish `htt : t * t ∈ 𝓂[F]`. Establish `: t * t = (t * t - 4 * n) + 2 * (2 * n)` using `by ring`.

Rewrite using `[this]`. Conclude with `add_mem hΔ (Ideal.mul_mem_right _ _ h2m)`. Establish `ht : t ∈ 𝓂[F]`. Apply the tactic sequence `rcases (IsLocalRing.maximalIdeal.isMaximal 𝒪[F]).isPrime.mem_or_mem htt with h | h <;> exact h`. Establish `h2k : (2 : 𝓀[F]) = 0`.

Use `(IsLocalRing.residue_eq_zero_iff (2 : 𝒪[F])).mpr h2m` as an intermediate fact. Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis. Establish `hinj : Function.Injective (fun x : 𝓀[F] => x * x)`. Introduce `x y hxy`. Simplify using `only at hxy`.

Establish `h1 : (x + y) * (x + y) = 0`. Take the linear combination `(-1 : 𝓀[F]) * hxy + (x * x + x * y) * h2k`. Establish `h3 : x + y = 0` using `mul_self_eq_zero.mp h1`. Take the linear combination `h3 - y * h2k`. Take `⟨r, hr⟩` from `(Finite.injective_iff_surjective.mp hinj) (IsLocalRing.residue 𝒪[F] n)`.

Take `⟨a, ha⟩` from `IsLocalRing.residue_surjective r`. Use `⟨a, add_mem ht (Ideal.mul_mem_right _ _ h2m), ?_⟩` and prove the remaining obligations. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_sub, map_mul, ha]`. Simplify using `only at hr`. Rewrite using `[hr, sub_self]`.
-/
theorem exists_a_mod [IsNonarchimedeanLocalField F] (t n : 𝒪[F]) (hΔ : t * t - 4 * n ∈ 𝓂[F]) :
    ∃ a : 𝒪[F], t + 2 * a ∈ 𝓂[F] ∧ a * a - n ∈ 𝓂[F] := by
  by_cases h2 : IsUnit (2 : 𝒪[F])
  · obtain ⟨u, hu⟩ := h2
    have hmul : (u : 𝒪[F]) * ↑u⁻¹ = 1 := u.mul_inv
    refine ⟨-(t * ↑u⁻¹), ?_, ?_⟩
    · have : t + 2 * -(t * ↑u⁻¹) = 0 := by
        linear_combination (-t) * hmul + (t * ↑u⁻¹) * hu
      rw [this]; exact zero_mem _
    · have : -(t * ↑u⁻¹) * -(t * ↑u⁻¹) - n = ↑u⁻¹ * ↑u⁻¹ * (t * t - 4 * n) := by
        linear_combination (n * ((u : 𝒪[F]) * ↑u⁻¹ + 1)) * hmul +
          (-(n * ↑u⁻¹ * ↑u⁻¹ * ((u : 𝒪[F]) + 2))) * hu
      rw [this]; exact Ideal.mul_mem_left _ _ hΔ
  · have h2m : (2 : 𝒪[F]) ∈ 𝓂[F] := (IsLocalRing.mem_maximalIdeal _).mpr h2
    have htt : t * t ∈ 𝓂[F] := by
      have : t * t = (t * t - 4 * n) + 2 * (2 * n) := by ring
      rw [this]; exact add_mem hΔ (Ideal.mul_mem_right _ _ h2m)
    have ht : t ∈ 𝓂[F] := by
      rcases (IsLocalRing.maximalIdeal.isMaximal 𝒪[F]).isPrime.mem_or_mem htt with h | h <;> exact h
    have h2k : (2 : 𝓀[F]) = 0 := by
      have := (IsLocalRing.residue_eq_zero_iff (2 : 𝒪[F])).mpr h2m
      rwa [map_ofNat] at this
    have hinj : Function.Injective (fun x : 𝓀[F] => x * x) := by
      intro x y hxy
      simp only at hxy
      have h1 : (x + y) * (x + y) = 0 := by
        linear_combination (-1 : 𝓀[F]) * hxy + (x * x + x * y) * h2k
      have h3 : x + y = 0 := mul_self_eq_zero.mp h1
      linear_combination h3 - y * h2k
    obtain ⟨r, hr⟩ := (Finite.injective_iff_surjective.mp hinj) (IsLocalRing.residue 𝒪[F] n)
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective r
    refine ⟨a, add_mem ht (Ideal.mul_mem_right _ _ h2m), ?_⟩
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_mul, ha]
    simp only at hr; rw [hr, sub_self]

variable (L : LocE F E) [IsNonarchimedeanLocalField F]

/- English proof (translation)
Establish `hn` using `Q.hn`. Rewrite `hn` using `[Q.hcj]`. Rewrite using `[map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, Q.hcj]`. Simplify using `only [map_add, map_mul]`. Take the linear combination `(algebraMap F E b * algebraMap F E b) * hn`.
-/
theorem QBasis.normE {L : LocE F E} (Q : QBasis L) (a b : F) :
    (algebraMap F E a + algebraMap F E b * Q.ω) * L.cj (algebraMap F E a + algebraMap F E b * Q.ω) =
      algebraMap F E (a * a + (Q.t : F) * a * b + (Q.n : F) * b * b) := by
  have hn := Q.hn
  rw [Q.hcj] at hn
  rw [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, Q.hcj]
  simp only [map_add, map_mul]
  linear_combination (algebraMap F E b * algebraMap F E b) * hn

/- English proof (translation)
Assume the negation of the conclusion as `hΔ`. Establish `hΔm : Q.t * Q.t - 4 * Q.n ∈ 𝓂[F]` using `(IsLocalRing.mem_maximalIdeal _).mpr hΔ`. Take `⟨a, h1, h2⟩` from `exists_a_mod Q.t Q.n hΔm`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[F]`. Rewrite `h1`, `h2` using `[hϖ.maximalIdeal_eq]`.

Take `⟨p1, hp1⟩` from `Ideal.mem_span_singleton'.mp h1`. Take `⟨p2, hp2⟩` from `Ideal.mem_span_singleton'.mp h2`. Establish `e1 : algebraMap F E (p1 : F) * algebraMap F E (ϖ : F) = algebraMap F E (Q.t : F) + 2 * algebraMap F E (a : F)`. Establish `e1F : (p1 : F) * (ϖ : F) = (Q.t : F) + 2 * (a : F)`. Use `congrArg Subtype.val hp1` as an intermediate fact.

Move the coercions through the operations in `at this`. Conclude with `this`. Rewrite using `[← map_mul, e1F, map_add, map_mul, map_ofNat]`. Establish `e2 : algebraMap F E (p2 : F) * algebraMap F E (ϖ : F) = algebraMap F E (a : F) * algebraMap F E (a : F) - algebraMap F E (Q.n : F)`. Establish `e2F : (p2 : F) * (ϖ : F) = (a : F) * (a : F) - (Q.n : F)`.

Use `congrArg Subtype.val hp2` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`. Rewrite using `[← map_mul, e2F, map_sub, map_mul]`. Use `set y := Q.ω + algebraMap F E (a : F) with hy`.

Establish `hyO : y ∈ L.O` using `add_mem Q.hω ((locE_algMap_mem L).mpr a.2)`. Establish `hsq : y * y = algebraMap F E (p1 : F) * Q.ω * algebraMap F E (ϖ : F) + algebraMap F E (p2 : F) * algebraMap F E (ϖ : F)`. Rewrite using `[hy]`. Take the linear combination `Q.sq - Q.ω * e1 - e2`. Establish `hmemO : algebraMap F E (p1 : F) * Q.ω + algebraMap F E (p2 : F) ∈ L.O` using `add_mem (mul_mem ((locE_algMap_mem L).mpr p1.2) Q.hω) ((locE_algMap_mem L).mpr p2.2)`.

Establish `hspan : y * y ∈ Submodule.span L.O {algebraMap F E ((ϖ : 𝒪[F]) : F)}`. Rewrite using `[Submodule.mem_span_singleton]`. Use `⟨⟨_, hmemO⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Subring.smul_def, smul_eq_mul, hsq]`. Simplify using `only`.

Expand and normalize the polynomial expressions, which then agree. Establish `hyd` using `L.unram ϖ hϖ y hyO (by simpa using hspan)`. Take `⟨⟨w, hw⟩, hwy⟩` from `Submodule.mem_span_singleton.mp hyd`. Rewrite `hwy` using `[Subring.smul_def, smul_eq_mul]`. Take `⟨a', b', hab'⟩` from `Q.span w hw`.

Establish `hwy' : w * algebraMap F E (ϖ : F) = y` using `hwy`. Rewrite `hwy'` using `[hab']`. Apply `Q.hnot` to reduce the goal to its premises. Establish `hne : (1 : F) - (ϖ : F) * (b' : F) ≠ 0`. Introduce `h`.

Apply `hϖ.not_isUnit` to reduce the goal to its premises. Establish `hm : ϖ * b' = 1` using `Subtype.ext (by push_cast; linear_combination -h)`. Conclude with `⟨⟨ϖ, b', hm, by rw [mul_comm]; exact hm⟩, rfl⟩`. Use `⟨((ϖ : F) * (a' : F) - (a : F)) / (1 - (ϖ : F) * (b' : F)), ?_⟩` and prove the remaining obligations. Establish `hu : IsUnit (algebraMap F E (1 - (ϖ : F) * (b' : F)))` using `(IsUnit.mk0 _ hne).map _`.

Apply `hu.mul_left_cancel` to reduce the goal to its premises. Rewrite using `[← map_mul, mul_div_cancel₀ _ hne]`. Simplify using `only [map_sub, map_mul, map_one]`. Rewrite `hwy'` using `[hy]`. Take the linear combination `hwy'`.
-/
theorem QBasis.disc_unit {L : LocE F E} (Q : QBasis L) : IsUnit (Q.t * Q.t - 4 * Q.n) := by
  by_contra hΔ
  have hΔm : Q.t * Q.t - 4 * Q.n ∈ 𝓂[F] := (IsLocalRing.mem_maximalIdeal _).mpr hΔ
  obtain ⟨a, h1, h2⟩ := exists_a_mod Q.t Q.n hΔm
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  rw [hϖ.maximalIdeal_eq] at h1 h2
  obtain ⟨p1, hp1⟩ := Ideal.mem_span_singleton'.mp h1
  obtain ⟨p2, hp2⟩ := Ideal.mem_span_singleton'.mp h2
  have e1 : algebraMap F E (p1 : F) * algebraMap F E (ϖ : F) =
      algebraMap F E (Q.t : F) + 2 * algebraMap F E (a : F) := by
    have e1F : (p1 : F) * (ϖ : F) = (Q.t : F) + 2 * (a : F) := by
      have := congrArg Subtype.val hp1; push_cast at this; exact this
    rw [← map_mul, e1F, map_add, map_mul, map_ofNat]
  have e2 : algebraMap F E (p2 : F) * algebraMap F E (ϖ : F) =
      algebraMap F E (a : F) * algebraMap F E (a : F) - algebraMap F E (Q.n : F) := by
    have e2F : (p2 : F) * (ϖ : F) = (a : F) * (a : F) - (Q.n : F) := by
      have := congrArg Subtype.val hp2; push_cast at this; exact this
    rw [← map_mul, e2F, map_sub, map_mul]
  set y := Q.ω + algebraMap F E (a : F) with hy
  have hyO : y ∈ L.O := add_mem Q.hω ((locE_algMap_mem L).mpr a.2)
  have hsq : y * y = algebraMap F E (p1 : F) * Q.ω * algebraMap F E (ϖ : F) +
      algebraMap F E (p2 : F) * algebraMap F E (ϖ : F) := by
    rw [hy]; linear_combination Q.sq - Q.ω * e1 - e2
  have hmemO : algebraMap F E (p1 : F) * Q.ω + algebraMap F E (p2 : F) ∈ L.O :=
    add_mem (mul_mem ((locE_algMap_mem L).mpr p1.2) Q.hω) ((locE_algMap_mem L).mpr p2.2)
  have hspan : y * y ∈ Submodule.span L.O {algebraMap F E ((ϖ : 𝒪[F]) : F)} := by
    rw [Submodule.mem_span_singleton]
    refine ⟨⟨_, hmemO⟩, ?_⟩
    rw [Subring.smul_def, smul_eq_mul, hsq]; simp only; ring
  have hyd := L.unram ϖ hϖ y hyO (by simpa using hspan)
  obtain ⟨⟨w, hw⟩, hwy⟩ := Submodule.mem_span_singleton.mp hyd
  rw [Subring.smul_def, smul_eq_mul] at hwy
  obtain ⟨a', b', hab'⟩ := Q.span w hw
  have hwy' : w * algebraMap F E (ϖ : F) = y := hwy
  rw [hab'] at hwy'
  apply Q.hnot
  have hne : (1 : F) - (ϖ : F) * (b' : F) ≠ 0 := by
    intro h
    apply hϖ.not_isUnit
    have hm : ϖ * b' = 1 := Subtype.ext (by push_cast; linear_combination -h)
    exact ⟨⟨ϖ, b', hm, by rw [mul_comm]; exact hm⟩, rfl⟩
  refine ⟨((ϖ : F) * (a' : F) - (a : F)) / (1 - (ϖ : F) * (b' : F)), ?_⟩
  have hu : IsUnit (algebraMap F E (1 - (ϖ : F) * (b' : F))) := (IsUnit.mk0 _ hne).map _
  apply hu.mul_left_cancel
  rw [← map_mul, mul_div_cancel₀ _ hne]
  simp only [map_sub, map_mul, map_one]
  rw [hy] at hwy'
  linear_combination hwy'

/- English proof (translation)
Use `haveI := locE_nontrivial L`. Take `⟨a, b, hab⟩` from `Q.span x hx`. Take `⟨z1, hz1⟩` from `h 1 (one_mem _)`. Take `⟨z2, hz2⟩` from `h Q.ω Q.hω`. Establish `hn` using `Q.hn`.

Rewrite `hn` using `[Q.hcj]`. Establish `i1 : (2 * (a : F) + (b : F) * (Q.t : F)) = (ϖ : F) * (z1 : F)`. Apply `(algebraMap F E).injective` to reduce the goal to its premises. Rewrite using `[← hz1, one_mul, hab, map_add L.cj, map_mul L.cj, AlgEquiv.commutes, AlgEquiv.commutes, Q.hcj]`. Simplify using `only [map_add, map_mul, map_ofNat]`.

Expand and normalize the polynomial expressions, which then agree. Establish `i2 : ((a : F) * (Q.t : F) + (b : F) * ((Q.t : F) * (Q.t : F) - 2 * (Q.n : F))) = (ϖ : F) * (z2 : F)`. Apply `(algebraMap F E).injective` to reduce the goal to its premises. Rewrite using `[← hz2, hab, map_mul L.cj, map_add L.cj, map_mul L.cj, AlgEquiv.commutes, AlgEquiv.commutes, Q.hcj]`. Simplify using `only [map_add, map_mul, map_sub, map_ofNat]`.

Take the linear combination `(2 * algebraMap F E (b : F)) * hn`. Take `⟨u, hu⟩` from `Q.disc_unit`. Establish `hinv : ((u⁻¹ : (𝒪[F])ˣ) : F) * ((Q.t : F) * (Q.t : F) - 4 * (Q.n : F)) = 1`. Use `congrArg (fun z : 𝒪[F] => (z : F)) (u.inv_mul)` as an intermediate fact. Rewrite `this` using `[hu]`.

Move the coercions through the operations in `at this`. Conclude with `this`. Use `set v : F := ((u⁻¹ : (𝒪[F])ˣ) : F)`. Establish `hv : v ∈ 𝒪[F]` using `((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]).2`. Use `set al : F := v * (((Q.t : F) * (Q.t : F) - 2 * (Q.n : F)) * (z1 : F) - (Q.t : F) * (z2 : F))`.

Use `set be : F := v * (2 * (z2 : F) - (Q.t : F) * (z1 : F))`. Establish `hal : al ∈ 𝒪[F]` using `mul_mem hv (sub_mem (mul_mem (sub_mem (mul_mem Q.t.2 Q.t.2) (mul_mem (by simpa using (2 : 𝒪[F]).2) Q.n.2)) z1.2) (mul_mem Q.t.2 z2.2))`. Establish `hbe : be ∈ 𝒪[F]` using `mul_mem hv (sub_mem (mul_mem (by simpa using (2 : 𝒪[F]).2) z2.2) (mul_mem Q.t.2 z1.2))`. Establish `ha : (a : F) = (ϖ : F) * al`. Take the linear combination `(v * ((Q.t : F) * (Q.t : F) - 2 * (Q.n : F))) * i1 + (-(v * (Q.t : F))) * i2 + (-(a : F)) * hinv`.

Establish `hb : (b : F) = (ϖ : F) * be`. Take the linear combination `(-(v * (Q.t : F))) * i1 + (2 * v) * i2 + (-(b : F)) * hinv`. Use `⟨algebraMap F E al + algebraMap F E be * Q.ω, add_mem ((locE_algMap_mem L).mpr hal) (mul_mem ((locE_algMap_mem L).mpr hbe) Q.hω), ?_⟩` and prove the remaining obligations. Rewrite using `[hab, ha, hb]`. Simplify using `only [map_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem QBasis.trace_nondeg {L : LocE F E} (Q : QBasis L) {ϖ : 𝒪[F]} {x : E} (hx : x ∈ L.O)
    (h : ∀ c ∈ L.O, ∃ z : 𝒪[F], c * x + L.cj (c * x) = algebraMap F E ((ϖ : F) * (z : F))) :
    ∃ w ∈ L.O, x = algebraMap F E (ϖ : F) * w := by
  haveI := locE_nontrivial L
  obtain ⟨a, b, hab⟩ := Q.span x hx
  obtain ⟨z1, hz1⟩ := h 1 (one_mem _)
  obtain ⟨z2, hz2⟩ := h Q.ω Q.hω
  have hn := Q.hn
  rw [Q.hcj] at hn
  have i1 : (2 * (a : F) + (b : F) * (Q.t : F)) = (ϖ : F) * (z1 : F) := by
    apply (algebraMap F E).injective
    rw [← hz1, one_mul, hab, map_add L.cj, map_mul L.cj, AlgEquiv.commutes, AlgEquiv.commutes, Q.hcj]
    simp only [map_add, map_mul, map_ofNat]; ring
  have i2 : ((a : F) * (Q.t : F) + (b : F) * ((Q.t : F) * (Q.t : F) - 2 * (Q.n : F))) =
      (ϖ : F) * (z2 : F) := by
    apply (algebraMap F E).injective
    rw [← hz2, hab, map_mul L.cj, map_add L.cj, map_mul L.cj, AlgEquiv.commutes, AlgEquiv.commutes, Q.hcj]
    simp only [map_add, map_mul, map_sub, map_ofNat]
    linear_combination (2 * algebraMap F E (b : F)) * hn
  obtain ⟨u, hu⟩ := Q.disc_unit
  have hinv : ((u⁻¹ : (𝒪[F])ˣ) : F) * ((Q.t : F) * (Q.t : F) - 4 * (Q.n : F)) = 1 := by
    have := congrArg (fun z : 𝒪[F] => (z : F)) (u.inv_mul)
    rw [hu] at this; push_cast at this; exact this
  set v : F := ((u⁻¹ : (𝒪[F])ˣ) : F)
  have hv : v ∈ 𝒪[F] := ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]).2
  set al : F := v * (((Q.t : F) * (Q.t : F) - 2 * (Q.n : F)) * (z1 : F) - (Q.t : F) * (z2 : F))
  set be : F := v * (2 * (z2 : F) - (Q.t : F) * (z1 : F))
  have hal : al ∈ 𝒪[F] := mul_mem hv (sub_mem (mul_mem (sub_mem (mul_mem Q.t.2 Q.t.2)
    (mul_mem (by simpa using (2 : 𝒪[F]).2) Q.n.2)) z1.2) (mul_mem Q.t.2 z2.2))
  have hbe : be ∈ 𝒪[F] := mul_mem hv (sub_mem (mul_mem (by simpa using (2 : 𝒪[F]).2) z2.2)
    (mul_mem Q.t.2 z1.2))
  have ha : (a : F) = (ϖ : F) * al := by
    linear_combination (v * ((Q.t : F) * (Q.t : F) - 2 * (Q.n : F))) * i1 + (-(v * (Q.t : F))) * i2 +
      (-(a : F)) * hinv
  have hb : (b : F) = (ϖ : F) * be := by
    linear_combination (-(v * (Q.t : F))) * i1 + (2 * v) * i2 + (-(b : F)) * hinv
  refine ⟨algebraMap F E al + algebraMap F E be * Q.ω,
    add_mem ((locE_algMap_mem L).mpr hal) (mul_mem ((locE_algMap_mem L).mpr hbe) Q.hω), ?_⟩
  rw [hab, ha, hb]; simp only [map_mul]; ring

end Alg3

end PI.SelfDualHermitianLattices.Hd
