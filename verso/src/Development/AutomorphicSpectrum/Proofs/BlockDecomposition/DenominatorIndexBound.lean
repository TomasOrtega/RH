import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.IdxGe

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem index_toAddSubgroup (a : Ideal (𝓞 K)) :
    (Submodule.toAddSubgroup a).index = Ideal.absNorm a := rfl

/- English proof (translation)
Establish `hle : Submodule.toAddSubgroup (𝔱 * a) ≤ Submodule.toAddSubgroup a` using `(Submodule.toAddSubgroup_le _ _).2 Ideal.mul_le_right`. Establish `h` using `AddSubgroup.relIndex_mul_index hle`. Rewrite `h` using `[index_toAddSubgroup, index_toAddSubgroup, map_mul]`. Establish `hne : Ideal.absNorm a ≠ 0` using `fun h0 => ha (Ideal.absNorm_eq_zero_iff.1 h0)`. Conclude with `Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) h`.
-/
theorem relIndex_mul_ideal (𝔱 a : Ideal (𝓞 K)) (ha : a ≠ ⊥) :
    (Submodule.toAddSubgroup (𝔱 * a)).relIndex (Submodule.toAddSubgroup a) =
      Ideal.absNorm 𝔱 := by
  have hle : Submodule.toAddSubgroup (𝔱 * a) ≤ Submodule.toAddSubgroup a :=
    (Submodule.toAddSubgroup_le _ _).2 Ideal.mul_le_right
  have h := AddSubgroup.relIndex_mul_index hle
  rw [index_toAddSubgroup, index_toAddSubgroup, map_mul] at h
  have hne : Ideal.absNorm a ≠ 0 := fun h0 => ha (Ideal.absNorm_eq_zero_iff.1 h0)
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) h

/- English proof (translation)
Rewrite using `[den, Ideal.mem_torsionOf_iff, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨o, ho⟩` from `h 0`. Conclude with `Submodule.mem_one.2 ⟨o, by simpa [Algebra.smul_def] using ho⟩`.

Introduce `h`. Take `⟨o, ho⟩` from `Submodule.mem_one.1 h`. Introduce `i`. Conclude with `⟨o, by simpa [Algebra.smul_def] using ho⟩`.
-/
theorem mem_den_iff (x : K) (a : 𝓞 K) :
    a ∈ den K x ↔ (a : K) * x ∈ (1 : Submodule (𝓞 K) K) := by
  rw [den, Ideal.mem_torsionOf_iff, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  constructor
  · intro h
    obtain ⟨o, ho⟩ := h 0
    exact Submodule.mem_one.2 ⟨o, by simpa [Algebra.smul_def] using ho⟩
  · intro h
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 h
    intro i
    exact ⟨o, by simpa [Algebra.smul_def] using ho⟩

/- English proof (translation)
Use `set H := (Submodule.toAddSubgroup (Ideal.span {d})).addSubgroupOf (Submodule.toAddSubgroup B) with hH`. Set `g : 𝓞 K →+ Submodule.toAddSubgroup B` to `{ toFun := fun r => ⟨r * e, B.mul_mem_left r heB⟩ map_zero' := by ext; simp map_add' := fun r s => by ext; simp [add_mul] }`. Set `f : 𝓞 K →+ (Submodule.toAddSubgroup B) ⧸ H` to `(QuotientAddGroup.mk' H).comp g`. Establish `hdK : (d : K) ≠ 0` using `by simpa using hd`. Establish `hker : f.ker = Submodule.toAddSubgroup (den K x)`.

Use extensionality with `r`. Rewrite using `[AddMonoidHom.mem_ker]`. Express the relevant statement in the definitionally equal form `(QuotientAddGroup.mk (g r) : _ ⧸ H) = 0 ↔ r ∈ den K x`. Rewrite using `[QuotientAddGroup.eq_zero_iff, hH, AddSubgroup.mem_addSubgroupOf, mem_den_iff]`. Express the relevant statement in the definitionally equal form `r * e ∈ Ideal.span {d} ↔ _`.

Rewrite using `[Ideal.mem_span_singleton', Submodule.mem_one]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨o, ho⟩`. Use `⟨o, ?_⟩` and prove the remaining obligations. Use `congrArg (fun y : 𝓞 K => (y : K)) ho` as an intermediate fact.

Simplify using `only [map_mul, hex] at this`. Apply `mul_left_cancel₀ hdK` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(d : K) * (o : K) = _`. Take the linear combination `this`. Introduce and unpack `⟨o, ho⟩`.

Use `⟨o, ?_⟩` and prove the remaining obligations. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Establish `ho' : (o : K) = (r : K) * x` using `ho`. Simplify using `only [map_mul, hex, ho']`. Expand and normalize the polynomial expressions, which then agree.

Establish `hidx : (den K x).toAddSubgroup.index = Nat.card f.range`. Rewrite using `[← hker]`. Conclude with `AddSubgroup.index_ker f`. Establish `hfinite : Finite ((Submodule.toAddSubgroup B) ⧸ H)` using `Nat.finite_of_card_ne_zero hfin`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem absNorm_den_le (x : K) (d e : 𝓞 K) (hd : d ≠ 0) (hex : (e : K) = (d : K) * x)
    (B : Ideal (𝓞 K)) (hdB : Ideal.span {d} ≤ B) (heB : e ∈ B)
    (hfin : (Submodule.toAddSubgroup (Ideal.span {d})).relIndex (Submodule.toAddSubgroup B) ≠ 0) :
    Ideal.absNorm (den K x) ≤
      (Submodule.toAddSubgroup (Ideal.span {d})).relIndex (Submodule.toAddSubgroup B) := by
  set H := (Submodule.toAddSubgroup (Ideal.span {d})).addSubgroupOf (Submodule.toAddSubgroup B)
    with hH
  let g : 𝓞 K →+ Submodule.toAddSubgroup B :=
    { toFun := fun r => ⟨r * e, B.mul_mem_left r heB⟩
      map_zero' := by ext; simp
      map_add' := fun r s => by ext; simp [add_mul] }
  let f : 𝓞 K →+ (Submodule.toAddSubgroup B) ⧸ H := (QuotientAddGroup.mk' H).comp g
  have hdK : (d : K) ≠ 0 := by simpa using hd
  have hker : f.ker = Submodule.toAddSubgroup (den K x) := by
    ext r
    rw [AddMonoidHom.mem_ker]
    change (QuotientAddGroup.mk (g r) : _ ⧸ H) = 0 ↔ r ∈ den K x
    rw [QuotientAddGroup.eq_zero_iff, hH, AddSubgroup.mem_addSubgroupOf, mem_den_iff]
    change r * e ∈ Ideal.span {d} ↔ _
    rw [Ideal.mem_span_singleton', Submodule.mem_one]
    constructor
    · rintro ⟨o, ho⟩
      refine ⟨o, ?_⟩
      have := congrArg (fun y : 𝓞 K => (y : K)) ho
      simp only [map_mul, hex] at this
      apply mul_left_cancel₀ hdK
      change (d : K) * (o : K) = _
      linear_combination this
    · rintro ⟨o, ho⟩
      refine ⟨o, ?_⟩
      apply RingOfIntegers.coe_injective
      have ho' : (o : K) = (r : K) * x := ho
      simp only [map_mul, hex, ho']
      ring
  have hidx : (den K x).toAddSubgroup.index = Nat.card f.range := by
    rw [← hker]; exact AddSubgroup.index_ker f
  have hfinite : Finite ((Submodule.toAddSubgroup B) ⧸ H) := Nat.finite_of_card_ne_zero hfin
  calc Ideal.absNorm (den K x) = Nat.card f.range := hidx
    _ ≤ Nat.card ((Submodule.toAddSubgroup B) ⧸ H) :=
        Nat.card_le_card_of_injective _ Subtype.val_injective
    _ = _ := rfl

/- English proof (translation)
Take `⟨s, hs𝔱, hs⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot h𝔱`. Take `⟨𝔰, h𝔰⟩` from `Ideal.dvd_span_singleton.2 hs𝔱`. Establish `hsK : (s : K) ≠ 0` using `by simpa using hs`. Establish `h𝔰0 : 𝔰 ≠ ⊥`. Introduce and unpack `rfl`.

Rewrite `h𝔰` using `[Ideal.mul_bot]`. Conclude with `hs (Ideal.span_singleton_eq_bot.1 h𝔰)`. Establish `hle : Ideal.span {d} * 𝔰 ≤ (𝔱 * a) * 𝔰`. Rewrite using `[Ideal.span_singleton_mul_le_iff]`. Introduce `u hu`.

Establish `hmem : ∀ v ∈ 𝔱, (v : K) * ((u : K) / s) ∈ (1 : Submodule (𝓞 K) K)`. Introduce `v hv`. Establish `hvu : v * u ∈ Ideal.span {s}`. Rewrite using `[h𝔰]`. Conclude with `Ideal.mul_mem_mul hv hu`.

Take `⟨r, hr⟩` from `Ideal.mem_span_singleton'.1 hvu`. Use `Submodule.mem_one.2 ⟨r, ?_⟩` and prove the remaining obligations. Use `congrArg (fun y : 𝓞 K => (y : K)) hr` as an intermediate fact. Simplify using `only [map_mul] at this`. Express the relevant statement in the definitionally equal form `(r : K) = _`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `this`. Take `⟨y, hya, hy⟩` from `H _ hmem`. Establish `heq : d * u = s * y`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises.

Simplify using `only [map_mul, hy]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[heq, mul_right_comm 𝔱 a 𝔰, ← h𝔰, mul_comm s y]`. Conclude with `Ideal.mul_mem_mul hya (Ideal.mem_span_singleton_self s) |> fun h => by`. Rewrite `h` using `[mul_comm a]`. Then use the resulting hypothesis.

Rewrite `hle`, the goal using `[← Ideal.dvd_iff_le]`. Conclude with `(mul_dvd_mul_iff_right h𝔰0).1 hle`.
-/
theorem span_le_mul (𝔱 a : Ideal (𝓞 K)) (h𝔱 : 𝔱 ≠ ⊥) (d : 𝓞 K) (hd : d ≠ 0)
    (H : ∀ b : K, (∀ u ∈ 𝔱, (u : K) * b ∈ (1 : Submodule (𝓞 K) K)) →
      ∃ y ∈ a, (y : K) = (d : K) * b) :
    Ideal.span {d} ≤ 𝔱 * a := by
  obtain ⟨s, hs𝔱, hs⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔱
  obtain ⟨𝔰, h𝔰⟩ := Ideal.dvd_span_singleton.2 hs𝔱
  have hsK : (s : K) ≠ 0 := by simpa using hs
  have h𝔰0 : 𝔰 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot] at h𝔰
    exact hs (Ideal.span_singleton_eq_bot.1 h𝔰)
  have hle : Ideal.span {d} * 𝔰 ≤ (𝔱 * a) * 𝔰 := by
    rw [Ideal.span_singleton_mul_le_iff]
    intro u hu
    have hmem : ∀ v ∈ 𝔱, (v : K) * ((u : K) / s) ∈ (1 : Submodule (𝓞 K) K) := by
      intro v hv
      have hvu : v * u ∈ Ideal.span {s} := by
        rw [h𝔰]; exact Ideal.mul_mem_mul hv hu
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hvu
      refine Submodule.mem_one.2 ⟨r, ?_⟩
      have := congrArg (fun y : 𝓞 K => (y : K)) hr
      simp only [map_mul] at this
      change (r : K) = _
      field_simp
      linear_combination this
    obtain ⟨y, hya, hy⟩ := H _ hmem
    have heq : d * u = s * y := by
      apply RingOfIntegers.coe_injective
      simp only [map_mul, hy]
      field_simp
    rw [heq, mul_right_comm 𝔱 a 𝔰, ← h𝔰, mul_comm s y]
    exact Ideal.mul_mem_mul hya (Ideal.mem_span_singleton_self s) |> fun h => by
      rwa [mul_comm a] at h
  rw [← Ideal.dvd_iff_le] at hle ⊢
  exact (mul_dvd_mul_iff_right h𝔰0).1 hle

/- English proof (translation)
Introduce `K _ _ 𝔱 h𝔱 c hfg h1 hinv t w x ht hw hx`. Take `⟨d, hd0, hint⟩` from `FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors (𝓞 K)) hfg`. Establish `hd : d ≠ 0` using `nonZeroDivisors.ne_zero hd0`. Establish `hdK : (d : K) ≠ 0` using `by simpa using hd`. Establish `hint' : ∀ b ∈ c, ∃ y : 𝓞 K, (y : K) = (d : K) * b`.

Introduce `b hb`. Take `⟨y, hy⟩` from `hint b hb`. Conclude with `⟨y, by simpa [Algebra.smul_def] using hy⟩`. Set `g : 𝓞 K →ₗ[𝓞 K] K` to `LinearMap.toSpanSingleton (𝓞 K) K ((d : K)⁻¹)`. Establish `hg : ∀ y : 𝓞 K, g y = (y : K) * (d : K)⁻¹` using `fun y => by`.

Simplify using `[g, LinearMap.toSpanSingleton_apply, Algebra.smul_def]`. Set `a : Ideal (𝓞 K)` to `c.comap g`. Establish `hmema : ∀ y : 𝓞 K, y ∈ a ↔ (y : K) * (d : K)⁻¹ ∈ c` using `fun y => by`. Express the relevant statement in the definitionally equal form `g y ∈ c ↔ _`. Rewrite using `[hg]`.

Establish `hga : ∀ b ∈ c, ∃ y ∈ a, (y : K) = (d : K) * b`. Introduce `b hb`. Take `⟨y, hy⟩` from `hint' b hb`. Use `⟨y, (hmema y).2 ?_, hy⟩` and prove the remaining obligations. Rewrite using `[hy]`.

Use `hb using 1` and compare the differences between its conclusion and the goal. Clear the denominators using the available nonvanishing facts. Establish `hda : d ∈ a`. Rewrite using `[hmema, mul_inv_cancel₀ hdK]`. Conclude with `h1 (Submodule.one_le.1 le_rfl)`.

Establish `ha0 : a ≠ ⊥` using `fun h => hd (by simpa [h] using hda)`. Establish `hdle : Ideal.span {d} ≤ 𝔱 * a` using `span_le_mul 𝔱 a h𝔱 d hd fun b hb => hga b (hinv b hb)`. Establish `hBa : 𝔱 * a ≤ a` using `Ideal.mul_le_right`. Establish `hinj : Function.Injective g.toAddMonoidHom`. Introduce `y z hyz`.

Express the relevant statement in the definitionally equal form `g y = g z at hyz`. Rewrite `hyz` using `[hg, hg]`. Conclude with `RingOfIntegers.coe_injective (mul_right_cancel₀ (inv_ne_zero hdK) hyz)`. Establish `hc : c.toAddSubgroup = (Submodule.toAddSubgroup a).map g.toAddMonoidHom`. Use extensionality with `b`.

Prove the components needed by the constructor for the conclusion. Introduce `hb`. Take `⟨y, hya, hy⟩` from `hga b hb`. Use `⟨y, hya, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `g y = b`.

Rewrite using `[hg, hy]`. Clear the denominators using the available nonvanishing facts. Introduce and unpack `⟨y, hya, rfl⟩`. Conclude with `hya`. Establish `hone : (1 : Submodule (𝓞 K) K).toAddSubgroup = (Submodule.toAddSubgroup (Ideal.span {d})).map g.toAddMonoidHom`.

Use extensionality with `b`. Prove the components needed by the constructor for the conclusion. Introduce `hb`. Take `⟨o, ho⟩` from `Submodule.mem_one.1 hb`. Use `⟨o * d, Ideal.mem_span_singleton'.2 ⟨o, rfl⟩, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `g (o * d) = b`. Rewrite using `[hg, ← ho]`. Simplify using `only [map_mul]`. Express the relevant statement in the definitionally equal form `(o : K) * d * _ = o`. Clear the denominators using the available nonvanishing facts.

Introduce and unpack `⟨y, hy, rfl⟩`. Take `⟨o, rfl⟩` from `Ideal.mem_span_singleton'.1 hy`. Use `Submodule.mem_one.2 ⟨o, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(o : K) = g (o * d)`. Rewrite using `[hg]`.

Simplify using `only [map_mul]`. Clear the denominators using the available nonvanishing facts. Establish `hidx : idx K c = (Submodule.toAddSubgroup (Ideal.span {d})).relIndex (Submodule.toAddSubgroup a)`. Rewrite using `[idx, hc, hone, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]`. Establish `hdB : Submodule.toAddSubgroup (Ideal.span {d}) ≤ Submodule.toAddSubgroup (𝔱 * a)` using `(Submodule.toAddSubgroup_le _ _).2 hdle`.

Establish `hBa' : Submodule.toAddSubgroup (𝔱 * a) ≤ Submodule.toAddSubgroup a` using `(Submodule.toAddSubgroup_le _ _).2 hBa`. Establish `hfin : (Submodule.toAddSubgroup (Ideal.span {d})).relIndex (Submodule.toAddSubgroup (𝔱 * a)) ≠ 0`. Introduce `h0`. Establish `h` using `AddSubgroup.relIndex_mul_index hdB`. Rewrite `h` using `[h0, zero_mul, index_toAddSubgroup]`.

Conclude with `hd (Ideal.span_singleton_eq_bot.1 (Ideal.absNorm_eq_zero_iff.1 h.symm))`. Take `⟨yw, hywa, hyw⟩` from `hga w hw`. Take `⟨o, ho⟩` from `Submodule.mem_one.1 hx`. Establish `ho' : (o : K) = (t : K) * w - x` using `ho`. Establish `heK : ((t * yw - d * o : 𝓞 K) : K) = (d : K) * x`.

Simplify using `only [map_sub, map_mul, hyw, ho']`. Expand and normalize the polynomial expressions, which then agree. Establish `heB : t * yw - d * o ∈ 𝔱 * a` using `Ideal.sub_mem _ (Ideal.mul_mem_mul ht hywa) (hdle (Ideal.mem_span_singleton'.2 ⟨o, mul_comm _ _⟩))`. Establish `hden` using `absNorm_den_le x d _ hd heK (𝔱 * a) hdle heB hfin`. Rewrite using `[hidx, ← AddSubgroup.relIndex_mul_relIndex _ _ _ hdB hBa', relIndex_mul_ideal 𝔱 a ha0, mul_comm]`.

Conclude with `Nat.mul_le_mul_right _ hden`.
-/
theorem absNorm_mul_den_le_idx : ∀ (K : Type) [Field K] [NumberField K] (𝔱 : Ideal (𝓞 K)),
    𝔱 ≠ ⊥ → ∀ c : Submodule (𝓞 K) K, c.FG → (1 : Submodule (𝓞 K) K) ≤ c →
    (∀ b : K, (∀ a ∈ 𝔱, (a : K) * b ∈ (1 : Submodule (𝓞 K) K)) → b ∈ c) →
    ∀ (t : 𝓞 K) (w x : K), t ∈ 𝔱 → w ∈ c → (t : K) * w - x ∈ (1 : Submodule (𝓞 K) K) →
    Ideal.absNorm 𝔱 * Ideal.absNorm (den K x) ≤ idx K c := by
  intro K _ _ 𝔱 h𝔱 c hfg h1 hinv t w x ht hw hx
  obtain ⟨d, hd0, hint⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors (𝓞 K)) hfg
  have hd : d ≠ 0 := nonZeroDivisors.ne_zero hd0
  have hdK : (d : K) ≠ 0 := by simpa using hd
  have hint' : ∀ b ∈ c, ∃ y : 𝓞 K, (y : K) = (d : K) * b := by
    intro b hb
    obtain ⟨y, hy⟩ := hint b hb
    exact ⟨y, by simpa [Algebra.smul_def] using hy⟩
  let g : 𝓞 K →ₗ[𝓞 K] K := LinearMap.toSpanSingleton (𝓞 K) K ((d : K)⁻¹)
  have hg : ∀ y : 𝓞 K, g y = (y : K) * (d : K)⁻¹ := fun y => by
    simp [g, LinearMap.toSpanSingleton_apply, Algebra.smul_def]
  let a : Ideal (𝓞 K) := c.comap g
  have hmema : ∀ y : 𝓞 K, y ∈ a ↔ (y : K) * (d : K)⁻¹ ∈ c := fun y => by
    change g y ∈ c ↔ _
    rw [hg]
  have hga : ∀ b ∈ c, ∃ y ∈ a, (y : K) = (d : K) * b := by
    intro b hb
    obtain ⟨y, hy⟩ := hint' b hb
    refine ⟨y, (hmema y).2 ?_, hy⟩
    rw [hy]
    convert hb using 1
    field_simp
  have hda : d ∈ a := by
    rw [hmema, mul_inv_cancel₀ hdK]
    exact h1 (Submodule.one_le.1 le_rfl)
  have ha0 : a ≠ ⊥ := fun h => hd (by simpa [h] using hda)
  have hdle : Ideal.span {d} ≤ 𝔱 * a :=
    span_le_mul 𝔱 a h𝔱 d hd fun b hb => hga b (hinv b hb)
  have hBa : 𝔱 * a ≤ a := Ideal.mul_le_right

  have hinj : Function.Injective g.toAddMonoidHom := by
    intro y z hyz
    change g y = g z at hyz
    rw [hg, hg] at hyz
    exact RingOfIntegers.coe_injective (mul_right_cancel₀ (inv_ne_zero hdK) hyz)
  have hc : c.toAddSubgroup = (Submodule.toAddSubgroup a).map g.toAddMonoidHom := by
    ext b
    constructor
    · intro hb
      obtain ⟨y, hya, hy⟩ := hga b hb
      refine ⟨y, hya, ?_⟩
      change g y = b
      rw [hg, hy]
      field_simp
    · rintro ⟨y, hya, rfl⟩
      exact hya
  have hone : (1 : Submodule (𝓞 K) K).toAddSubgroup =
      (Submodule.toAddSubgroup (Ideal.span {d})).map g.toAddMonoidHom := by
    ext b
    constructor
    · intro hb
      obtain ⟨o, ho⟩ := Submodule.mem_one.1 hb
      refine ⟨o * d, Ideal.mem_span_singleton'.2 ⟨o, rfl⟩, ?_⟩
      change g (o * d) = b
      rw [hg, ← ho]
      simp only [map_mul]
      change (o : K) * d * _ = o
      field_simp
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨o, rfl⟩ := Ideal.mem_span_singleton'.1 hy
      refine Submodule.mem_one.2 ⟨o, ?_⟩
      change (o : K) = g (o * d)
      rw [hg]
      simp only [map_mul]
      field_simp
  have hidx : idx K c = (Submodule.toAddSubgroup (Ideal.span {d})).relIndex
      (Submodule.toAddSubgroup a) := by
    rw [idx, hc, hone, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]
  have hdB : Submodule.toAddSubgroup (Ideal.span {d}) ≤ Submodule.toAddSubgroup (𝔱 * a) :=
    (Submodule.toAddSubgroup_le _ _).2 hdle
  have hBa' : Submodule.toAddSubgroup (𝔱 * a) ≤ Submodule.toAddSubgroup a :=
    (Submodule.toAddSubgroup_le _ _).2 hBa
  have hfin : (Submodule.toAddSubgroup (Ideal.span {d})).relIndex
      (Submodule.toAddSubgroup (𝔱 * a)) ≠ 0 := by
    intro h0
    have h := AddSubgroup.relIndex_mul_index hdB
    rw [h0, zero_mul, index_toAddSubgroup] at h
    exact hd (Ideal.span_singleton_eq_bot.1 (Ideal.absNorm_eq_zero_iff.1 h.symm))

  obtain ⟨yw, hywa, hyw⟩ := hga w hw
  obtain ⟨o, ho⟩ := Submodule.mem_one.1 hx
  have ho' : (o : K) = (t : K) * w - x := ho
  have heK : ((t * yw - d * o : 𝓞 K) : K) = (d : K) * x := by
    simp only [map_sub, map_mul, hyw, ho']
    ring
  have heB : t * yw - d * o ∈ 𝔱 * a :=
    Ideal.sub_mem _ (Ideal.mul_mem_mul ht hywa)
      (hdle (Ideal.mem_span_singleton'.2 ⟨o, mul_comm _ _⟩))
  have hden := absNorm_den_le x d _ hd heK (𝔱 * a) hdle heB hfin
  rw [hidx, ← AddSubgroup.relIndex_mul_relIndex _ _ _ hdB hBa', relIndex_mul_ideal 𝔱 a ha0,
    mul_comm]
  exact Nat.mul_le_mul_right _ hden

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.IdxGe
