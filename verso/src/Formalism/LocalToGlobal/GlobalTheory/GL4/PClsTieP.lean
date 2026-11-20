import Formalism.LocalToGlobal.GlobalTheory.GL4.PClsTie

noncomputable section

open NumberField Formalism.BasicNotions

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Conclude with `⟨RingOfIntegers.mapRingHom (starRingEnd E) a, rfl⟩`.
-/
theorem star_int (a : 𝓞 E) : star (a : E) ∈ (algebraMap (𝓞 E) E).range := by
  exact ⟨RingOfIntegers.mapRingHom (starRingEnd E) a, rfl⟩

/- English proof (translation)
Establish `hTE : (T : E) ≠ 0` using `Nat.cast_ne_zero.2 hT0`. Establish `horth' : ∀ x, S.hT z0 (ι x) = 0`. Introduce `x`. Use `S.herm.eq (ι x) z0` as an intermediate fact. Rewrite `this` using `[horth, map_zero]`.

Conclude with `this.symm`. Establish `huniq : ∀ (v : S'.V) (t : E), ι v + t • z0 = 0 → v = 0 ∧ t = 0`. Introduce `v t h`. Establish `h1 : S.hT z0 (ι v + t • z0) = 0` using `by rw [h, map_zero]`. Rewrite `h1` using `[map_add, map_smul, horth', hz0, smul_eq_mul, zero_add, mul_eq_zero]`.

Establish `ht : t = 0` using `h1.resolve_right hTE`. Use `⟨?_, ht⟩` and prove the remaining obligations. Rewrite `h` using `[ht, zero_smul, add_zero]`. Apply `S'.nondeg.2 v` to reduce the goal to its premises. Introduce `x`.

Rewrite using `[← hι, h, map_zero]`. Establish `hdec : ∀ l ∈ L, ∃ l' ∈ L', ∃ a : 𝓞 E, γ l = ι l' + (a : E) • z0`. Introduce `l hl`. Establish `: γ l ∈ Formalism.HermitianLatticesTheory.gmap γ L` using `⟨l, hl, rfl⟩`. Rewrite `this` using `[htil, Submodule.mem_sup]`.

Take `⟨y, ⟨l', hl', rfl⟩, w, hw, hsum⟩` from `this`. Take `⟨a, rfl⟩` from `Submodule.mem_span_singleton.1 hw`. Conclude with `⟨l', hl', a, by rw [← hsum, algebraMap_smul]; rfl⟩`. Establish `hcomp : ∀ (l' : S'.V), l' ∈ L' → ∀ a : 𝓞 E, γ.symm (ι l' + (a : E) • z0) ∈ L`. Introduce `l' hl' a`.

Establish `: ι l' + (a : E) • z0 ∈ Formalism.HermitianLatticesTheory.gmap γ L`. Rewrite using `[htil]`. Use `Submodule.add_mem_sup ⟨l', hl', rfl⟩ ?_` and prove the remaining obligations. Conclude with `Submodule.mem_span_singleton.2 ⟨a, (algebraMap_smul E a z0).symm⟩`. Take `⟨l, hl, he⟩` from `this`.

Establish `: l = γ.symm (ι l' + (a : E) • z0)` using `by rw [← he]; simp`. Rewrite using `[← this]`. Conclude with `hl`. Establish `hpair : ∀ (v : S'.V) (a t : E), S.hT (ι v + a • z0) (t • z0) = star a * t * (T : E)`. Introduce `v a t`.

Simplify using `only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ₂, map_smul, horth, hz0, smul_eq_mul, starRingEnd_apply, zero_add]`. Expand and normalize the polynomial expressions, which then agree. Establish `hpair2 : ∀ (v x : S'.V) (a : E), S.hT (ι v + a • z0) (ι x) = S'.hT v x`. Introduce `v x a`. Simplify using `only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ₂, horth', smul_zero, add_zero]`.

Conclude with `hι v x`. Use `set q : S.V := γ.symm ((T : E)⁻¹ • z0) with hq`. Establish `hγq : γ q = (T : E)⁻¹ • z0` using `by simp [hq]`. Establish `hqd : q ∈ Formalism.HermitianLatticesTheory.dual S.hT L`. Rewrite using `[Formalism.L2.Herm.mem_dual]`.

Introduce `l hl`. Take `⟨l', _, a, ha⟩` from `hdec l hl`. Rewrite using `[← hγ, ha, hγq, hpair, mul_assoc, inv_mul_cancel₀ hTE, mul_one]`. Conclude with `star_int a`. Use `set Q : Submodule (𝓞 E) S.V := L ⊔ Submodule.span (𝓞 E) {q} with hQ`.

Establish `hLQ : L ≤ Q` using `le_sup_left`. Establish `hQd : Q ≤ Formalism.HermitianLatticesTheory.dual S.hT L` using `sup_le hint ((Submodule.span_singleton_le_iff_mem _ _).2 hqd)`. Set `φ : 𝓞 E →+ S.V` to `(LinearMap.toSpanSingleton (𝓞 E) S.V q).toAddMonoidHom`. Establish `hrange : (Submodule.span (𝓞 E) {q}).toAddSubgroup = φ.range`. Use extensionality with `x`.

Simplify using `only [Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton, AddMonoidHom.mem_range, φ, LinearMap.toAddMonoidHom_coe, LinearMap.toSpanSingleton_apply]`. Establish `hcomap : L.toAddSubgroup.comap φ = (Ideal.span {((T : ℕ) : 𝓞 E)}).toAddSubgroup`. Use extensionality with `a`. Simplify using `only [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, φ, LinearMap.toAddMonoidHom_coe, LinearMap.toSpanSingleton_apply, Ideal.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Take `⟨l', _, b, hb⟩` from `hdec _ h`. Rewrite `hb` using `[← algebraMap_smul E a q, map_smul, hγq, smul_smul]`. Establish `h2` using `huniq (-l') ((a : E) * (T : E)⁻¹ - (b : E)) (by`. Rewrite using `[map_neg, sub_smul, hb]`.

Use the proof step `abel)`. Establish `h3 : (a : E) = (T : E) * (b : E)`. Use `h2.2` as an intermediate fact. Clear denominators, using `at this` for the nonvanishing conditions. Take the linear combination `this`.

Use `⟨b, ?_⟩` and prove the remaining obligations. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Use `push_cast`. Conclude with `h3`. Introduce and unpack `⟨b, rfl⟩`.

Use `hcomp 0 (zero_mem _) b using 1` and compare the differences between its conclusion and the goal. Establish `e1 : algebraMap (𝓞 E) E (((T : ℕ) : 𝓞 E) * b) = (T : E) * (b : E)` using `by simp`. Rewrite using `[map_zero, zero_add, hq, ← algebraMap_smul E (((T : ℕ) : 𝓞 E) * b), e1, ← LinearEquiv.map_smul, smul_smul]`. Use `congr 2`. Clear the denominators using the available nonvanishing facts.

Establish `hLQi : L.toAddSubgroup.relIndex Q.toAddSubgroup = T ^ Module.finrank ℚ E`. Rewrite using `[hQ, Submodule.sup_toAddSubgroup, AddSubgroup.relIndex_sup_left, hrange, ← AddSubgroup.index_comap, hcomap, ← card_quot_nat E T]`. Both sides reduce to the same expression. Establish `hQi : Q.toAddSubgroup.relIndex (Formalism.HermitianLatticesTheory.dual S.hT L).toAddSubgroup = 1`. Establish `h` using `AddSubgroup.relIndex_mul_relIndex _ _ _ (Submodule.toAddSubgroup_mono hLQ) (Submodule.toAddSubgroup_mono hQd)`.

Rewrite `h` using `[hLQi, hidx]`. Establish `hp : 0 < T ^ Module.finrank ℚ E` using `pow_pos (Nat.pos_of_ne_zero hT0) _`. Conclude with `(Nat.mul_eq_left hp.ne').1 h`. Establish `hdQ : Formalism.HermitianLatticesTheory.dual S.hT L ≤ Q` using `(Submodule.toAddSubgroup_le _ _).1 (AddSubgroup.relIndex_eq_one.1 hQi)`. Introduce `x hx`.

Establish `hw : γ.symm (ι x) ∈ Formalism.HermitianLatticesTheory.dual S.hT L`. Rewrite using `[Formalism.L2.Herm.mem_dual]`. Introduce `l hl`. Take `⟨l', hl', a, ha⟩` from `hdec l hl`. Rewrite using `[← hγ, ha, LinearEquiv.apply_symm_apply, hpair2]`.

Conclude with `(Formalism.L2.Herm.mem_dual S' L' x).1 hx l' hl'`. Take `⟨l, hl, r, hr, hsum⟩` from `Submodule.mem_sup.1 (hdQ hw)`. Take `⟨b, rfl⟩` from `Submodule.mem_span_singleton.1 hr`. Take `⟨l', hl', a, ha⟩` from `hdec l hl`. Establish `he : ι x = ι l' + (a : E) • z0 + (b : E) • ((T : E)⁻¹ • z0)`.

Use `congrArg γ hsum` as an intermediate fact. Rewrite `this` using `[LinearEquiv.apply_symm_apply, map_add, ha, ← algebraMap_smul E b q, map_smul, hγq]`. Conclude with `this.symm`. Establish `h2` using `huniq (x - l') (-((a : E) + (b : E) * (T : E)⁻¹)) (by`. Rewrite using `[map_sub, he, neg_smul, add_smul, smul_smul]`.

Use the proof step `abel)`. Establish `: x = l'` using `sub_eq_zero.1 h2.1`. Rewrite using `[this]`. Conclude with `hl'`.
-/
theorem dual_le_of_split (S S' : HSpace E) (ι : S'.V →ₗ[E] S.V) (hι : HSpace.IsIsomEmb S' S ι) (z0 : S.V)
    (horth : ∀ x, S.hT (ι x) z0 = 0) (T : ℕ) (hT0 : T ≠ 0) (hz0 : S.hT z0 z0 = (T : E))
    (γ : S.V ≃ₗ[E] S.V) (hγ : ∀ x y, S.hT (γ x) (γ y) = S.hT x y)
    (L : Submodule (𝓞 E) S.V) (hint : L ≤ Formalism.HermitianLatticesTheory.dual S.hT L)
    (hidx : L.toAddSubgroup.relIndex (Formalism.HermitianLatticesTheory.dual S.hT L).toAddSubgroup = T ^ Module.finrank ℚ E)
    (L' : Submodule (𝓞 E) S'.V)
    (htil : Formalism.HermitianLatticesTheory.gmap γ L = L'.map (ι.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {z0}) :
    Formalism.HermitianLatticesTheory.dual S'.hT L' ≤ L' := by
  have hTE : (T : E) ≠ 0 := Nat.cast_ne_zero.2 hT0
  have horth' : ∀ x, S.hT z0 (ι x) = 0 := by
    intro x
    have := S.herm.eq (ι x) z0
    rw [horth, map_zero] at this
    exact this.symm

  have huniq : ∀ (v : S'.V) (t : E), ι v + t • z0 = 0 → v = 0 ∧ t = 0 := by
    intro v t h
    have h1 : S.hT z0 (ι v + t • z0) = 0 := by rw [h, map_zero]
    rw [map_add, map_smul, horth', hz0, smul_eq_mul, zero_add, mul_eq_zero] at h1
    have ht : t = 0 := h1.resolve_right hTE
    refine ⟨?_, ht⟩
    rw [ht, zero_smul, add_zero] at h
    apply S'.nondeg.2 v
    intro x
    rw [← hι, h, map_zero]

  have hdec : ∀ l ∈ L, ∃ l' ∈ L', ∃ a : 𝓞 E, γ l = ι l' + (a : E) • z0 := by
    intro l hl
    have : γ l ∈ Formalism.HermitianLatticesTheory.gmap γ L := ⟨l, hl, rfl⟩
    rw [htil, Submodule.mem_sup] at this
    obtain ⟨y, ⟨l', hl', rfl⟩, w, hw, hsum⟩ := this
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
    exact ⟨l', hl', a, by rw [← hsum, algebraMap_smul]; rfl⟩
  have hcomp : ∀ (l' : S'.V), l' ∈ L' → ∀ a : 𝓞 E, γ.symm (ι l' + (a : E) • z0) ∈ L := by
    intro l' hl' a
    have : ι l' + (a : E) • z0 ∈ Formalism.HermitianLatticesTheory.gmap γ L := by
      rw [htil]
      refine Submodule.add_mem_sup ⟨l', hl', rfl⟩ ?_
      exact Submodule.mem_span_singleton.2 ⟨a, (algebraMap_smul E a z0).symm⟩
    obtain ⟨l, hl, he⟩ := this
    have : l = γ.symm (ι l' + (a : E) • z0) := by rw [← he]; simp
    rw [← this]; exact hl
  have hpair : ∀ (v : S'.V) (a t : E), S.hT (ι v + a • z0) (t • z0) = star a * t * (T : E) := by
    intro v a t
    simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ₂, map_smul, horth, hz0, smul_eq_mul,
      starRingEnd_apply, zero_add]
    ring
  have hpair2 : ∀ (v x : S'.V) (a : E), S.hT (ι v + a • z0) (ι x) = S'.hT v x := by
    intro v x a
    simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ₂, horth', smul_zero, add_zero]
    exact hι v x
  set q : S.V := γ.symm ((T : E)⁻¹ • z0) with hq
  have hγq : γ q = (T : E)⁻¹ • z0 := by simp [hq]

  have hqd : q ∈ Formalism.HermitianLatticesTheory.dual S.hT L := by
    rw [Formalism.L2.Herm.mem_dual]
    intro l hl
    obtain ⟨l', _, a, ha⟩ := hdec l hl
    rw [← hγ, ha, hγq, hpair, mul_assoc, inv_mul_cancel₀ hTE, mul_one]
    exact star_int a
  set Q : Submodule (𝓞 E) S.V := L ⊔ Submodule.span (𝓞 E) {q} with hQ
  have hLQ : L ≤ Q := le_sup_left
  have hQd : Q ≤ Formalism.HermitianLatticesTheory.dual S.hT L :=
    sup_le hint ((Submodule.span_singleton_le_iff_mem _ _).2 hqd)

  let φ : 𝓞 E →+ S.V := (LinearMap.toSpanSingleton (𝓞 E) S.V q).toAddMonoidHom
  have hrange : (Submodule.span (𝓞 E) {q}).toAddSubgroup = φ.range := by
    ext x
    simp only [Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton, AddMonoidHom.mem_range, φ,
      LinearMap.toAddMonoidHom_coe, LinearMap.toSpanSingleton_apply]
  have hcomap : L.toAddSubgroup.comap φ = (Ideal.span {((T : ℕ) : 𝓞 E)}).toAddSubgroup := by
    ext a
    simp only [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, φ, LinearMap.toAddMonoidHom_coe,
      LinearMap.toSpanSingleton_apply, Ideal.mem_span_singleton]
    constructor
    · intro h
      obtain ⟨l', _, b, hb⟩ := hdec _ h
      rw [← algebraMap_smul E a q, map_smul, hγq, smul_smul] at hb
      have h2 := huniq (-l') ((a : E) * (T : E)⁻¹ - (b : E)) (by
        rw [map_neg, sub_smul, hb]; abel)
      have h3 : (a : E) = (T : E) * (b : E) := by
        have := h2.2
        field_simp at this
        linear_combination this
      refine ⟨b, ?_⟩
      apply RingOfIntegers.coe_injective
      push_cast
      exact h3
    · rintro ⟨b, rfl⟩
      convert hcomp 0 (zero_mem _) b using 1
      have e1 : algebraMap (𝓞 E) E (((T : ℕ) : 𝓞 E) * b) = (T : E) * (b : E) := by simp
      rw [map_zero, zero_add, hq, ← algebraMap_smul E (((T : ℕ) : 𝓞 E) * b), e1, ← LinearEquiv.map_smul, smul_smul]
      congr 2
      field_simp
  have hLQi : L.toAddSubgroup.relIndex Q.toAddSubgroup = T ^ Module.finrank ℚ E := by
    rw [hQ, Submodule.sup_toAddSubgroup, AddSubgroup.relIndex_sup_left, hrange, ← AddSubgroup.index_comap,
      hcomap, ← card_quot_nat E T]
    rfl
  have hQi : Q.toAddSubgroup.relIndex (Formalism.HermitianLatticesTheory.dual S.hT L).toAddSubgroup = 1 := by
    have h := AddSubgroup.relIndex_mul_relIndex _ _ _ (Submodule.toAddSubgroup_mono hLQ)
      (Submodule.toAddSubgroup_mono hQd)
    rw [hLQi, hidx] at h
    have hp : 0 < T ^ Module.finrank ℚ E := pow_pos (Nat.pos_of_ne_zero hT0) _
    exact (Nat.mul_eq_left hp.ne').1 h
  have hdQ : Formalism.HermitianLatticesTheory.dual S.hT L ≤ Q :=
    (Submodule.toAddSubgroup_le _ _).1 (AddSubgroup.relIndex_eq_one.1 hQi)

  intro x hx
  have hw : γ.symm (ι x) ∈ Formalism.HermitianLatticesTheory.dual S.hT L := by
    rw [Formalism.L2.Herm.mem_dual]
    intro l hl
    obtain ⟨l', hl', a, ha⟩ := hdec l hl
    rw [← hγ, ha, LinearEquiv.apply_symm_apply, hpair2]
    exact (Formalism.L2.Herm.mem_dual S' L' x).1 hx l' hl'
  obtain ⟨l, hl, r, hr, hsum⟩ := Submodule.mem_sup.1 (hdQ hw)
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hr
  obtain ⟨l', hl', a, ha⟩ := hdec l hl
  have he : ι x = ι l' + (a : E) • z0 + (b : E) • ((T : E)⁻¹ • z0) := by
    have := congrArg γ hsum
    rw [LinearEquiv.apply_symm_apply, map_add, ha, ← algebraMap_smul E b q, map_smul, hγq] at this
    exact this.symm
  have h2 := huniq (x - l') (-((a : E) + (b : E) * (T : E)⁻¹)) (by
    rw [map_sub, he, neg_smul, add_smul, smul_smul]; abel)
  have : x = l' := sub_eq_zero.1 h2.1
  rw [this]; exact hl'

/- English proof (translation)
Establish `hTE : (T : E) ≠ 0` using `Nat.cast_ne_zero.2 hT0`. Establish `horth' : ∀ x, S.hT z0 (ι x) = 0`. Introduce `x`. Use `S.herm.eq (ι x) z0` as an intermediate fact. Rewrite `this` using `[horth, map_zero]`.

Conclude with `this.symm`. Establish `huniq : ∀ (v : S'.V) (t : E), ι v + t • z0 = 0 → v = 0 ∧ t = 0`. Introduce `v t h`. Establish `h1 : S.hT z0 (ι v + t • z0) = 0` using `by rw [h, map_zero]`. Rewrite `h1` using `[map_add, map_smul, horth', hz0, smul_eq_mul, zero_add, mul_eq_zero]`.

Establish `ht : t = 0` using `h1.resolve_right hTE`. Use `⟨?_, ht⟩` and prove the remaining obligations. Rewrite `h` using `[ht, zero_smul, add_zero]`. Apply `S'.nondeg.2 v` to reduce the goal to its premises. Introduce `x`.

Rewrite using `[← hι, h, map_zero]`. Establish `key : ∀ w ∈ Submodule.span E ((Formalism.HermitianLatticesTheory.gmap γ L : Submodule (𝓞 E) S.V) : Set S.V), ∃ y ∈ Submodule.span E (L' : Set S'.V), ∃ t : E, w = ι y + t • z0`. Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem w hw`.

Rewrite `hw` using `[htil, SetLike.mem_coe, Submodule.mem_sup]`. Take `⟨y, ⟨l', hl', rfl⟩, w', hw', rfl⟩` from `hw`. Take `⟨a, rfl⟩` from `Submodule.mem_span_singleton.1 hw'`. Conclude with `⟨l', Submodule.subset_span hl', (a : E), by rw [← algebraMap_smul E a z0]; rfl⟩`. Consider the case `zero => exact ⟨0, zero_mem _, 0, by simp⟩`.

Consider the case `add w w' _ _ h h'`. Take `⟨y, hy, t, rfl⟩` from `h`. Take `⟨y', hy', t', rfl⟩` from `h'`. Conclude with `⟨y + y', add_mem hy hy', t + t', by rw [map_add, add_smul]; abel⟩`. Consider the case `smul e w _ h`.

Take `⟨y, hy, t, rfl⟩` from `h`. Conclude with `⟨e • y, Submodule.smul_mem _ e hy, e * t, by rw [smul_add, map_smul, smul_smul]⟩`. Establish `htop : Submodule.span E ((Formalism.HermitianLatticesTheory.gmap γ L : Submodule (𝓞 E) S.V) : Set S.V) = ⊤`. Establish `: ((Formalism.HermitianLatticesTheory.gmap γ L : Submodule (𝓞 E) S.V) : Set S.V) = γ '' (L : Set S.V)`. Use extensionality with `x`.

Simplify using `[Formalism.HermitianLatticesTheory.gmap]`. Rewrite using `[this]`. Use `show Submodule.span E ((γ : S.V →ₗ[E] S.V) '' (L : Set S.V)) = ⊤`. Rewrite using `[Submodule.span_image, hspan, Submodule.map_top, LinearMap.range_eq_top]`. Conclude with `γ.surjective`.

Rewrite using `[eq_top_iff]`. Introduce `v _`. Take `⟨y, hy, t, he⟩` from `key (ι v) (by rw [htop]; exact Submodule.mem_top)`. Establish `h2` using `huniq (v - y) (-t) (by rw [map_sub, he, neg_smul]; abel)`. Rewrite using `[show v = y from sub_eq_zero.1 h2.1]`.

Conclude with `hy`.
-/
theorem span_top_of_split (S S' : HSpace E) (ι : S'.V →ₗ[E] S.V) (hι : HSpace.IsIsomEmb S' S ι) (z0 : S.V)
    (horth : ∀ x, S.hT (ι x) z0 = 0) (T : ℕ) (hT0 : T ≠ 0) (hz0 : S.hT z0 z0 = (T : E))
    (γ : S.V ≃ₗ[E] S.V) (L : Submodule (𝓞 E) S.V) (hspan : Submodule.span E (L : Set S.V) = ⊤)
    (L' : Submodule (𝓞 E) S'.V)
    (htil : Formalism.HermitianLatticesTheory.gmap γ L = L'.map (ι.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {z0}) :
    Submodule.span E (L' : Set S'.V) = ⊤ := by
  have hTE : (T : E) ≠ 0 := Nat.cast_ne_zero.2 hT0
  have horth' : ∀ x, S.hT z0 (ι x) = 0 := by
    intro x
    have := S.herm.eq (ι x) z0
    rw [horth, map_zero] at this
    exact this.symm
  have huniq : ∀ (v : S'.V) (t : E), ι v + t • z0 = 0 → v = 0 ∧ t = 0 := by
    intro v t h
    have h1 : S.hT z0 (ι v + t • z0) = 0 := by rw [h, map_zero]
    rw [map_add, map_smul, horth', hz0, smul_eq_mul, zero_add, mul_eq_zero] at h1
    have ht : t = 0 := h1.resolve_right hTE
    refine ⟨?_, ht⟩
    rw [ht, zero_smul, add_zero] at h
    apply S'.nondeg.2 v
    intro x
    rw [← hι, h, map_zero]
  have key : ∀ w ∈ Submodule.span E ((Formalism.HermitianLatticesTheory.gmap γ L : Submodule (𝓞 E) S.V) : Set S.V),
      ∃ y ∈ Submodule.span E (L' : Set S'.V), ∃ t : E, w = ι y + t • z0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      rw [htil, SetLike.mem_coe, Submodule.mem_sup] at hw
      obtain ⟨y, ⟨l', hl', rfl⟩, w', hw', rfl⟩ := hw
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw'
      exact ⟨l', Submodule.subset_span hl', (a : E), by rw [← algebraMap_smul E a z0]; rfl⟩
    | zero => exact ⟨0, zero_mem _, 0, by simp⟩
    | add w w' _ _ h h' =>
      obtain ⟨y, hy, t, rfl⟩ := h
      obtain ⟨y', hy', t', rfl⟩ := h'
      exact ⟨y + y', add_mem hy hy', t + t', by rw [map_add, add_smul]; abel⟩
    | smul e w _ h =>
      obtain ⟨y, hy, t, rfl⟩ := h
      exact ⟨e • y, Submodule.smul_mem _ e hy, e * t, by rw [smul_add, map_smul, smul_smul]⟩
  have htop : Submodule.span E ((Formalism.HermitianLatticesTheory.gmap γ L : Submodule (𝓞 E) S.V) : Set S.V) = ⊤ := by
    have : ((Formalism.HermitianLatticesTheory.gmap γ L : Submodule (𝓞 E) S.V) : Set S.V) = γ '' (L : Set S.V) := by
      ext x; simp [Formalism.HermitianLatticesTheory.gmap]
    rw [this]
    show Submodule.span E ((γ : S.V →ₗ[E] S.V) '' (L : Set S.V)) = ⊤
    rw [Submodule.span_image, hspan, Submodule.map_top, LinearMap.range_eq_top]
    exact γ.surjective
  rw [eq_top_iff]
  intro v _
  obtain ⟨y, hy, t, he⟩ := key (ι v) (by rw [htop]; exact Submodule.mem_top)
  have h2 := huniq (v - y) (-t) (by rw [map_sub, he, neg_smul]; abel)
  rw [show v = y from sub_eq_zero.1 h2.1]; exact hy

end General

open Formalism.L2.Herm in
attribute [local instance] Formalism.BasicNotions.Host.cmStar in

/- English proof (translation)
Establish `hT0 : (D.mem u).A.T ≠ 0` using `(D.mem u).A.T_prime.ne_zero`. Establish `horth : ∀ x, (D.sp.X D.R.m).hT (D.sp.iX' x) (X.atT u).z0 = 0`. Introduce `x`. Take `⟨t, ht⟩` from `Submodule.mem_span_singleton.1 (X.atT u).cocycle_zero_mem_invariants`. Rewrite using `[← ht, map_smul, D.sp.z_orth, smul_zero]`.

Use `set L := D.clsLat u D.R.m ((D.fm u).til c)`. Establish `hint : L ≤ Formalism.HermitianLatticesTheory.dual (D.sp.X D.R.m).hT L`. Introduce `x hx`. Use `clsLat_int X u D.R.m le_rfl _ x hx` as an intermediate fact. Rewrite `this` using `[dualSub_eq]`.

Conclude with `this`. Establish `hidx : L.toAddSubgroup.relIndex (Formalism.HermitianLatticesTheory.dual (D.sp.X D.R.m).hT L).toAddSubgroup = (D.mem u).A.T ^ Module.finrank ℚ D.host.E`. Use `clsLat_index X u D.R.m le_rfl ((D.fm u).til c)` as an intermediate fact. Rewrite `this` using `[dualSub_eq]`. Rewrite using `[this, finrank_E]`.

Both sides reduce to the same expression. Establish `htil` using `((X.atT u).til_tie c).1`. Establish `hle` using `dual_le_of_split (D.sp.X D.R.m) D.sp.X' D.sp.iX' D.sp.iX'_isom (X.atT u).z0 horth (D.mem u).A.T hT0 (X.atT u).hermitianForm_lastCoordinateUniformizerVector_self ((X.atT u).tilG c).1 ((X.atT u).tilG c).2 L hint hidx _ htil`. Establish `hsp` using `span_top_of_split (D.sp.X D.R.m) D.sp.X' D.sp.iX' D.sp.iX'_isom (X.atT u).z0 horth (D.mem u).A.T hT0 (X.atT u).hermitianForm_lastCoordinateUniformizerVector_self ((X.atT u).tilG c).1 L (D.clsLat_lat u D.R.m _).span_eq_top _ htil`. Use `⟨⟨?_, hsp⟩, clsLatP_int X u c, ?_⟩` and prove the remaining obligations.

Establish `hfgM : (Formalism.HermitianLatticesTheory.gmap ((X.atT u).tilG c).1 L).FG` using `(D.clsLat_lat u D.R.m _).fg.map _`. Establish `hle' : ((X.atT u).lattice₂ c).map (D.sp.iX'.restrictScalars (𝓞 D.host.E)) ≤ Formalism.HermitianLatticesTheory.gmap ((X.atT u).tilG c).1 L` using `by rw [htil]; exact le_sup_left`. Establish `hn : IsNoetherian (𝓞 D.host.E) (Formalism.HermitianLatticesTheory.gmap ((X.atT u).tilG c).1 L)` using `isNoetherian_of_fg_of_noetherian _ hfgM`. Establish `hfg` using `isNoetherian_submodule.1 hn _ hle'`. Use `Submodule.fg_of_fg_map_injective _ ?_ hfg` and prove the remaining obligations.

Introduce `a b hab`. Establish `h0 : D.sp.iX' (a - b) = 0` using `by rw [map_sub]; exact sub_eq_zero.2 hab`. Use `sub_eq_zero.1 (D.sp.X'.nondeg.2 _ fun x => ?_)` and prove the remaining obligations. Rewrite using `[← D.sp.iX'_isom, h0, map_zero]`. Rewrite using `[dualSub_eq]`.

Conclude with `AddSubgroup.relIndex_eq_one.2 ((Submodule.toAddSubgroup_le _ _).2 hle)`.
-/
theorem localLattice_selfDual {D : D7} (X : FullTied D) (u : D.what₂.Word) (c : (D.fm u).clsP) :
    Submodule.IsLattice D.host.E ((X.atT u).lattice₂ c) ∧ Formalism.MainNotions.flipTwoThree.LatT D.sp.X' 1 ((X.atT u).lattice₂ c) := by
  have hT0 : (D.mem u).A.T ≠ 0 := (D.mem u).A.T_prime.ne_zero
  have horth : ∀ x, (D.sp.X D.R.m).hT (D.sp.iX' x) (X.atT u).z0 = 0 := by
    intro x
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 (X.atT u).cocycle_zero_mem_invariants
    rw [← ht, map_smul, D.sp.z_orth, smul_zero]
  set L := D.clsLat u D.R.m ((D.fm u).til c)
  have hint : L ≤ Formalism.HermitianLatticesTheory.dual (D.sp.X D.R.m).hT L := by
    intro x hx
    have := clsLat_int X u D.R.m le_rfl _ x hx
    rw [dualSub_eq] at this
    exact this
  have hidx : L.toAddSubgroup.relIndex (Formalism.HermitianLatticesTheory.dual (D.sp.X D.R.m).hT L).toAddSubgroup =
      (D.mem u).A.T ^ Module.finrank ℚ D.host.E := by
    have := clsLat_index X u D.R.m le_rfl ((D.fm u).til c)
    rw [dualSub_eq] at this
    rw [this, finrank_E]; rfl
  have htil := ((X.atT u).til_tie c).1
  have hle := dual_le_of_split (D.sp.X D.R.m) D.sp.X' D.sp.iX' D.sp.iX'_isom (X.atT u).z0 horth
    (D.mem u).A.T hT0 (X.atT u).hermitianForm_lastCoordinateUniformizerVector_self ((X.atT u).tilG c).1 ((X.atT u).tilG c).2 L hint hidx _ htil
  have hsp := span_top_of_split (D.sp.X D.R.m) D.sp.X' D.sp.iX' D.sp.iX'_isom (X.atT u).z0 horth
    (D.mem u).A.T hT0 (X.atT u).hermitianForm_lastCoordinateUniformizerVector_self ((X.atT u).tilG c).1 L (D.clsLat_lat u D.R.m _).span_eq_top _ htil
  refine ⟨⟨?_, hsp⟩, clsLatP_int X u c, ?_⟩
  ·
    have hfgM : (Formalism.HermitianLatticesTheory.gmap ((X.atT u).tilG c).1 L).FG := (D.clsLat_lat u D.R.m _).fg.map _
    have hle' : ((X.atT u).lattice₂ c).map (D.sp.iX'.restrictScalars (𝓞 D.host.E)) ≤
        Formalism.HermitianLatticesTheory.gmap ((X.atT u).tilG c).1 L := by rw [htil]; exact le_sup_left
    have hn : IsNoetherian (𝓞 D.host.E) (Formalism.HermitianLatticesTheory.gmap ((X.atT u).tilG c).1 L) :=
      isNoetherian_of_fg_of_noetherian _ hfgM
    have hfg := isNoetherian_submodule.1 hn _ hle'
    refine Submodule.fg_of_fg_map_injective _ ?_ hfg
    intro a b hab
    have h0 : D.sp.iX' (a - b) = 0 := by rw [map_sub]; exact sub_eq_zero.2 hab
    refine sub_eq_zero.1 (D.sp.X'.nondeg.2 _ fun x => ?_)
    rw [← D.sp.iX'_isom, h0, map_zero]
  · rw [dualSub_eq]
    exact AddSubgroup.relIndex_eq_one.2 ((Submodule.toAddSubgroup_le _ _).2 hle)

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
