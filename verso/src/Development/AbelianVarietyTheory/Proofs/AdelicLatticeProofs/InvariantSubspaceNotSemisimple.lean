import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

/- English proof (translation)
Take `⟨n, hn⟩` from `hJ`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `key : ∀ k : ℕ, J ^ (k + 1) ≠ ⊥`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => simpa [Submodule.pow_one] using h0`. Consider the case `succ k ih`. Take `⟨a, ha, ha0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot ih`. Take `⟨b, hb, hba⟩` from `hcon a (Ideal.pow_le_self (Nat.succ_ne_zero k) ha) ha0`.

Introduce `h`. Apply `hba` to reduce the goal to its premises. Establish `: b * a ∈ J ^ (k + 1 + 1)`. Rewrite using `[Ideal.IsTwoSided.pow_succ]`. Conclude with `Ideal.mul_mem_mul hb ha`.

Rewrite `this` using `[h]`. Simplify using `using this`. Apply `key n` to reduce the goal to its premises. Rewrite using `[Submodule.pow_succ, hn]`. Simplify using the standard rewrite rules.
-/
theorem exists_mem_mul_eq_zero_of_isNilpotent {R : Type*} [Ring R] (J : Ideal R) [J.IsTwoSided]
    (hJ : IsNilpotent J) (h0 : J ≠ ⊥) : ∃ a ∈ J, a ≠ 0 ∧ ∀ b ∈ J, b * a = 0 := by
  obtain ⟨n, hn⟩ := hJ
  by_contra hcon
  push Not at hcon
  have key : ∀ k : ℕ, J ^ (k + 1) ≠ ⊥ := by
    intro k
    induction k with
    | zero => simpa [Submodule.pow_one] using h0
    | succ k ih =>
      obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ih
      obtain ⟨b, hb, hba⟩ := hcon a (Ideal.pow_le_self (Nat.succ_ne_zero k) ha) ha0
      intro h
      apply hba
      have : b * a ∈ J ^ (k + 1 + 1) := by
        rw [Ideal.IsTwoSided.pow_succ]
        exact Ideal.mul_mem_mul hb ha
      rw [h] at this
      simpa using this
  apply key n
  rw [Submodule.pow_succ, hn]
  simp

/- English proof (translation)
Establish `: RingHomSurjective f` using `⟨hf⟩`. Conclude with `Ring.le_comap_jacobson (f := f) hb`.
-/
theorem map_mem_jacobson_of_surjective {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (hf : Function.Surjective f) {b : R} (hb : b ∈ Ring.jacobson R) : f b ∈ Ring.jacobson S := by
  have : RingHomSurjective f := ⟨hf⟩
  exact Ring.le_comap_jacobson (f := f) hb

noncomputable def spanAlg {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Set (Matrix ι ι ℂ)} (h : IsPre Γ) :
    Subalgebra ℂ (Matrix ι ι ℂ) :=
  (Submodule.span ℂ Γ).toSubalgebra (Submodule.subset_span h.one_mem) (by
    intro x y hx hy
    have h1 := Submodule.mul_mem_mul hx hy
    rw [Submodule.span_mul_span] at h1
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact h.mul_mem a ha b hb)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `x ∈ Submodule.span ℂ Γ at hx`. Express the relevant statement in the definitionally equal form `Matrix.map x (⇑σ : ℂ → ℂ) ∈ Submodule.span ℂ Γ`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem g hg => exact Submodule.subset_span (h.aut_mem σ g hg)`. Consider the case `zero`.

Establish `e : Matrix.map (0 : Matrix ι ι ℂ) (⇑σ : ℂ → ℂ) = 0`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add a b _ _ ha hb`. Establish `e : Matrix.map (a + b) (⇑σ : ℂ → ℂ) = Matrix.map a (⇑σ : ℂ → ℂ) + Matrix.map b (⇑σ : ℂ → ℂ)`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[e]`.

Conclude with `Submodule.add_mem _ ha hb`. Consider the case `smul c a _ ha`. Establish `e : Matrix.map (c • a) (⇑σ : ℂ → ℂ) = σ c • Matrix.map a (⇑σ : ℂ → ℂ)`. Use extensionality with `i j`. Simplify using the standard rewrite rules.

Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ ha`.
-/
theorem map_mem_spanAlg {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Set (Matrix ι ι ℂ)} (h : IsPre Γ)
    (σ : ℂ ≃+* ℂ) {x : Matrix ι ι ℂ} (hx : x ∈ spanAlg h) : x.map σ ∈ spanAlg h := by
  change x ∈ Submodule.span ℂ Γ at hx
  change Matrix.map x (⇑σ : ℂ → ℂ) ∈ Submodule.span ℂ Γ
  induction hx using Submodule.span_induction with
  | mem g hg => exact Submodule.subset_span (h.aut_mem σ g hg)
  | zero =>
    have e : Matrix.map (0 : Matrix ι ι ℂ) (⇑σ : ℂ → ℂ) = 0 := by
      ext i j; simp
    rw [e]; exact Submodule.zero_mem _
  | add a b _ _ ha hb =>
    have e : Matrix.map (a + b) (⇑σ : ℂ → ℂ) = Matrix.map a (⇑σ : ℂ → ℂ) + Matrix.map b (⇑σ : ℂ → ℂ) := by
      ext i j; simp
    rw [e]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    have e : Matrix.map (c • a) (⇑σ : ℂ → ℂ) = σ c • Matrix.map a (⇑σ : ℂ → ℂ) := by
      ext i j; simp
    rw [e]; exact Submodule.smul_mem _ _ ha

noncomputable def spanAlgMap {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Set (Matrix ι ι ℂ)} (h : IsPre Γ)
    (σ : ℂ ≃+* ℂ) : spanAlg h →+* spanAlg h :=
  RingHom.codRestrict ((σ : ℂ →+* ℂ).mapMatrix.comp (spanAlg h).val.toRingHom) (spanAlg h)
    (fun x => map_mem_spanAlg h σ x.2)

/- English proof (translation)
Introduce `y`. Use `⟨⟨y.1.map σ.symm, map_mem_spanAlg h σ.symm y.2⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use extensionality with `i j`. Simplify using `[spanAlgMap]`.
-/
theorem spanAlgMap_surjective {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Set (Matrix ι ι ℂ)} (h : IsPre Γ)
    (σ : ℂ ≃+* ℂ) : Function.Surjective (spanAlgMap h σ) := by
  intro y
  refine ⟨⟨y.1.map σ.symm, map_mem_spanAlg h σ.symm y.2⟩, ?_⟩
  apply Subtype.ext
  ext i j
  simp [spanAlgMap]

/- English proof (translation)
Introduce `W hW`. Establish `hW' : ∀ x ∈ Submodule.span ℂ Γ, ∀ v ∈ W, x *ᵥ v ∈ W`. Introduce `x hx v hv`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact hW x hx v hv`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [add_mulVec]`. Conclude with `W.add_mem hx hy`. Consider the case `smul c x _ hx => rw [smul_mulVec]`. Conclude with `W.smul_mem _ hx`.

Set `U : Submodule (spanAlg h) (ι → ℂ)` to `{ W.toAddSubmonoid with smul_mem' := fun c v hv => hW' c.1 c.2 v hv }`. Take `⟨U', hU⟩` from `exists_isCompl U`. Establish `hsm : ∀ (x : Matrix ι ι ℂ), x ∈ spanAlg h → ∀ v ∈ U', x *ᵥ v ∈ U'` using `fun x hx v hv => U'.smul_mem ⟨x, hx⟩ hv`. Set `W' : Submodule ℂ (ι → ℂ)` to `{ U'.toAddSubmonoid with smul_mem' := fun c v hv => by`. Use `hsm (c • 1) ((spanAlg h).smul_mem (spanAlg h).one_mem c) v hv` as an intermediate fact.

Rewrite using `[smul_mulVec, one_mulVec] at this }` and apply the resulting hypothesis. Use `⟨W', fun g hg v hv => hsm g (Submodule.subset_span hg) v hv, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.disjoint_def]`. Introduce `x hx hx'`. Conclude with `Submodule.disjoint_def.1 hU.disjoint x hx hx'`.

Rewrite using `[codisjoint_iff, Submodule.eq_top_iff']`. Introduce `x`. Establish `: x ∈ U ⊔ U'` using `by rw [hU.sup_eq_top]; trivial`. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.1 this`. Conclude with `Submodule.add_mem_sup hy hz`.
-/
theorem ss_of_isSemisimpleRing {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Set (Matrix ι ι ℂ)} (h : IsPre Γ)
    [IsSemisimpleRing (spanAlg h)] : SS Γ := by
  intro W hW
  have hW' : ∀ x ∈ Submodule.span ℂ Γ, ∀ v ∈ W, x *ᵥ v ∈ W := by
    intro x hx v hv
    induction hx using Submodule.span_induction with
    | mem x hx => exact hW x hx v hv
    | zero => simp
    | add x y _ _ hx hy => rw [add_mulVec]; exact W.add_mem hx hy
    | smul c x _ hx => rw [smul_mulVec]; exact W.smul_mem _ hx
  let U : Submodule (spanAlg h) (ι → ℂ) :=
    { W.toAddSubmonoid with smul_mem' := fun c v hv => hW' c.1 c.2 v hv }
  obtain ⟨U', hU⟩ := exists_isCompl U
  have hsm : ∀ (x : Matrix ι ι ℂ), x ∈ spanAlg h → ∀ v ∈ U', x *ᵥ v ∈ U' :=
    fun x hx v hv => U'.smul_mem ⟨x, hx⟩ hv
  let W' : Submodule ℂ (ι → ℂ) :=
    { U'.toAddSubmonoid with
      smul_mem' := fun c v hv => by
        have := hsm (c • 1) ((spanAlg h).smul_mem (spanAlg h).one_mem c) v hv
        rwa [smul_mulVec, one_mulVec] at this }
  refine ⟨W', fun g hg v hv => hsm g (Submodule.subset_span hg) v hv, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    exact Submodule.disjoint_def.1 hU.disjoint x hx hx'
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro x
    have : x ∈ U ⊔ U' := by rw [hU.sup_eq_top]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 this
    exact Submodule.add_mem_sup hy hz

/- English proof (translation)
Introduce `ι _ _ Γ h hss`. Establish `: IsArtinianRing (spanAlg h)` using `IsArtinianRing.of_finite ℂ _`. Establish `h0 : Ring.jacobson (spanAlg h) ≠ ⊥`. Introduce `h0`. Use `IsArtinianRing.isSemisimpleRing_iff_jacobson.2 h0` as an intermediate fact.

Conclude with `hss (ss_of_isSemisimpleRing h)`. Take `⟨a, ha, ha0, hba⟩` from `exists_mem_mul_eq_zero_of_isNilpotent (Ring.jacobson (spanAlg h)) IsSemiprimaryRing.isNilpotent h0`. Set `W : Submodule ℂ (ι → ℂ)` to `{ carrier := {v | ∀ b ∈ Ring.jacobson (spanAlg h), b.1 *ᵥ v = 0} add_mem' := fun {x y} hx hy b hb => by rw [mulVec_add, hx b hb, hy b hb, add_zero] zero_mem' := fun b _ => mulVec_zero _ smul_mem' := fun c v hv b hb => by rw [mulVec_smul, hv b hb, smul_zero] }`. Use `⟨W, ?_, ?_, a.1, a.2, fun h1 => ha0 (Subtype.ext h1), ?_, fun v hv => hv a ha⟩` and prove the remaining obligations. Introduce `g hg v hv b hb`.

Establish `hg' : g ∈ spanAlg h` using `Submodule.subset_span hg`. Establish `h1 : b * (⟨g, hg'⟩ : spanAlg h) ∈ Ring.jacobson (spanAlg h)` using `Ideal.mul_mem_right _ _ hb`. Establish `h2` using `hv _ h1`. Rewrite `h2` using `[MulMemClass.coe_mul, ← mulVec_mulVec]`. Conclude with `h2`.

Introduce `σ v hv b hb`. Establish `h1 : spanAlgMap h σ.symm b ∈ Ring.jacobson (spanAlg h)` using `map_mem_jacobson_of_surjective _ (spanAlgMap_surjective h σ.symm) hb`. Establish `h2` using `hv _ h1`. Use function extensionality and compare the values at `i`. Establish `h3` using `congrArg σ (congrFun h2 i)`.

Simplify `h3` using `[spanAlgMap, mulVec, dotProduct, map_sum]`. Introduce `v b hb`. Rewrite using `[mulVec_mulVec]`. Use `congrArg Subtype.val (hba b hb)` as an intermediate fact. Express the relevant statement in the definitionally equal form `b.1 * a.1 = 0 at this`.

Rewrite using `[this, zero_mulVec]`.
-/
theorem exists_socle_radical_of_not_ss :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → ¬ SS Γ → ∃ W : Submodule ℂ (ι → ℂ), (∀ g ∈ Γ, ∀ v ∈ W, g *ᵥ v ∈ W) ∧ (∀ σ : ℂ ≃+* ℂ, ∀ v ∈ W, (fun i => σ (v i)) ∈ W) ∧ ∃ a ∈ Submodule.span ℂ Γ, a ≠ 0 ∧ (∀ v, a *ᵥ v ∈ W) ∧ ∀ v ∈ W, a *ᵥ v = 0 := by
  intro ι _ _ Γ h hss
  have : IsArtinianRing (spanAlg h) := IsArtinianRing.of_finite ℂ _
  have h0 : Ring.jacobson (spanAlg h) ≠ ⊥ := by
    intro h0
    have := IsArtinianRing.isSemisimpleRing_iff_jacobson.2 h0
    exact hss (ss_of_isSemisimpleRing h)
  obtain ⟨a, ha, ha0, hba⟩ := exists_mem_mul_eq_zero_of_isNilpotent (Ring.jacobson (spanAlg h))
    IsSemiprimaryRing.isNilpotent h0
  let W : Submodule ℂ (ι → ℂ) :=
    { carrier := {v | ∀ b ∈ Ring.jacobson (spanAlg h), b.1 *ᵥ v = 0}
      add_mem' := fun {x y} hx hy b hb => by rw [mulVec_add, hx b hb, hy b hb, add_zero]
      zero_mem' := fun b _ => mulVec_zero _
      smul_mem' := fun c v hv b hb => by rw [mulVec_smul, hv b hb, smul_zero] }
  refine ⟨W, ?_, ?_, a.1, a.2, fun h1 => ha0 (Subtype.ext h1), ?_, fun v hv => hv a ha⟩
  · intro g hg v hv b hb
    have hg' : g ∈ spanAlg h := Submodule.subset_span hg
    have h1 : b * (⟨g, hg'⟩ : spanAlg h) ∈ Ring.jacobson (spanAlg h) := Ideal.mul_mem_right _ _ hb
    have h2 := hv _ h1
    rw [MulMemClass.coe_mul, ← mulVec_mulVec] at h2
    exact h2
  · intro σ v hv b hb
    have h1 : spanAlgMap h σ.symm b ∈ Ring.jacobson (spanAlg h) :=
      map_mem_jacobson_of_surjective _ (spanAlgMap_surjective h σ.symm) hb
    have h2 := hv _ h1
    funext i
    have h3 := congrArg σ (congrFun h2 i)
    simpa [spanAlgMap, mulVec, dotProduct, map_sum] using h3
  · intro v b hb
    rw [mulVec_mulVec]
    have := congrArg Subtype.val (hba b hb)
    change b.1 * a.1 = 0 at this
    rw [this, zero_mulVec]

end GlobalTheory.ClassFin
