import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TwistApply
open GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Flat.DegCurve

namespace GlobalTheory.CompanionTheory.Ar.Flat.StepIdeal

/- English proof (translation)
Use `set m := RingHom.ker χ with hm`. Establish `hfix : ∀ a ∈ J, e * a = a`. Introduce `a ha`. Take `⟨x, rfl⟩` from `Ideal.mem_span_singleton'.mp (hJe ha)`. Combine the equalities or inequalities in the displayed calculation.

Establish `hJ : ¬ J ≤ m * J`. Introduce `hle`. Establish `hfg : (J : Submodule A A).FG` using `IsNoetherian.noetherian J`. Take `⟨r, hr, hr0⟩` from `Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m (J : Submodule A A) hfg (by rwa [Ideal.smul_eq_mul])`. Apply `hJ0` to reduce the goal to its premises.

Rewrite using `[eq_bot_iff]`. Introduce `a ha`. Establish `hs : 1 - r ∈ m`. Use `m.neg_mem hr` as an intermediate fact. Rewrite `this` using `[neg_sub]`. Then use the resulting hypothesis.

Establish `hsa : (1 - r) * a = a`. Establish `h0 : r * a = 0` using `by simpa [smul_eq_mul] using hr0 a ha`. Rewrite using `[sub_mul, one_mul, h0, sub_zero]`. Establish `hpow : ∀ n : ℕ, (e * (1 - r)) ^ n * a = a`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Combine the equalities or inequalities in the displayed calculation. Take `⟨n, hn⟩` from `hnil (1 - r) hs`.

Rewrite using `[Ideal.mem_bot, ← hpow n, hn, zero_mul]`. Take `⟨t, htJ, htW⟩` from `SetLike.not_le_iff_exists.mp hJ`. Set `W : Submodule k A` to `(m * J).restrictScalars k`. Establish `hq : W.mkQ t ≠ 0`. Rewrite using `[Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`.

Conclude with `htW`. Choose the witnesses or unpack the hypotheses as in `⟨φ, hφ⟩ : ∃ φ : Module.Dual k (A ⧸ W), φ (W.mkQ t) ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hq ((Module.forall_dual_apply_eq_zero_iff k _).mp hcon)`.

Use `set l : A →ₗ[k] k := (φ (W.mkQ t))⁻¹ • (φ ∘ₗ W.mkQ) with hl`. Establish `hlt : l t = 1`. Rewrite using `[hl, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, inv_mul_cancel₀ hφ]`. Establish `hlW : ∀ a ∈ m * J, l a = 0`. Introduce `a ha`.

Establish `: W.mkQ a = 0`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `ha`. Rewrite using `[hl, LinearMap.smul_apply, LinearMap.comp_apply, this, map_zero, smul_zero]`. Establish `hdec : ∀ r : A, r - algebraMap k A (χ r) ∈ m`.

Introduce `r`. Rewrite using `[hm, RingHom.mem_ker]`. Simplify using the standard rewrite rules. Set `J₁ : Ideal A` to `{ carrier := {a | a ∈ J ∧ l a = 0} add_mem' := fun {a b} ha hb => ⟨J.add_mem ha.1 hb.1, by rw [map_add, ha.2, hb.2, add_zero]⟩ zero_mem' := ⟨J.zero_mem, map_zero l⟩ smul_mem' := fun c a ha => by`. Use `⟨J.mul_mem_left c ha.1, ?_⟩` and prove the remaining obligations.

Establish `hsplit : c * a = χ c • a + (c - algebraMap k A (χ c)) * a`. Rewrite using `[Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree. Express the relevant statement in the definitionally equal form `l (c * a) = 0`. Rewrite using `[hsplit, map_add, map_smul, ha.2, smul_zero, zero_add]`.

Conclude with `hlW _ (Ideal.mul_mem_mul (hdec c) ha.1) }`. Establish `hmemJ₁ : ∀ a, a ∈ J₁ ↔ a ∈ J ∧ l a = 0` using `fun a => Iff.rfl`. Use `⟨J₁, t, l, ?_, htJ, ?_, ?_, ?_, hlt⟩` and prove the remaining obligations. Rewrite using `[SetLike.lt_iff_le_and_exists]`. Use `⟨fun a ha => ((hmemJ₁ a).mp ha).1, t, htJ, fun h => ?_⟩` and prove the remaining obligations.

Use `((hmemJ₁ t).mp h).2` as an intermediate fact. Rewrite `this` using `[hlt]`. Conclude with `one_ne_zero this`. Introduce `a ha`. Use `⟨l a, (hmemJ₁ _).mpr ⟨J.sub_mem ha (J.mul_mem_left _ htJ), ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[← Algebra.smul_def, map_sub, map_smul, hlt, smul_eq_mul, mul_one, sub_self]`. Introduce `a ha`. Conclude with `(hmemJ₁ _).mpr ⟨J.mul_mem_left a htJ, hlW _ (Ideal.mul_mem_mul ha htJ)⟩`. Introduce `a ha`. Conclude with `((hmemJ₁ a).mp ha).2`.
-/
theorem exists_colength_one (k A : Type) [Field k] [CommRing A] [Algebra k A] [Finite A]
    (χ : A →ₐ[k] k) (e : A) (J : Ideal A) (he : IsIdempotentElem e) (hχ : χ e = 1)
    (hnil : ∀ t ∈ RingHom.ker χ, IsNilpotent (e * t)) (hJe : J ≤ Ideal.span {e}) (hJ0 : J ≠ ⊥) :
    ∃ (J₁ : Ideal A) (t : A) (l : A →ₗ[k] k), J₁ < J ∧ t ∈ J ∧
      (∀ a ∈ J, ∃ c : k, a - algebraMap k A c * t ∈ J₁) ∧
      (∀ a ∈ RingHom.ker χ, a * t ∈ J₁) ∧ (∀ a ∈ J₁, l a = 0) ∧ l t = 1 := by
  classical
  set m := RingHom.ker χ with hm
  have hfix : ∀ a ∈ J, e * a = a := by
    intro a ha
    obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.mp (hJe ha)
    calc e * (x * e) = x * (e * e) := by ring
      _ = x * e := by rw [he.eq]
  have hJ : ¬ J ≤ m * J := by
    intro hle
    have hfg : (J : Submodule A A).FG := IsNoetherian.noetherian J
    obtain ⟨r, hr, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m
      (J : Submodule A A) hfg (by rwa [Ideal.smul_eq_mul])
    apply hJ0
    rw [eq_bot_iff]
    intro a ha
    have hs : 1 - r ∈ m := by
      have := m.neg_mem hr
      rwa [neg_sub] at this
    have hsa : (1 - r) * a = a := by
      have h0 : r * a = 0 := by simpa [smul_eq_mul] using hr0 a ha
      rw [sub_mul, one_mul, h0, sub_zero]
    have hpow : ∀ n : ℕ, (e * (1 - r)) ^ n * a = a := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        calc (e * (1 - r)) ^ (n + 1) * a = (e * (1 - r)) ^ n * (e * ((1 - r) * a)) := by ring
          _ = a := by rw [hsa, hfix a ha, ih]
    obtain ⟨n, hn⟩ := hnil (1 - r) hs
    rw [Ideal.mem_bot, ← hpow n, hn, zero_mul]
  obtain ⟨t, htJ, htW⟩ := SetLike.not_le_iff_exists.mp hJ
  let W : Submodule k A := (m * J).restrictScalars k
  have hq : W.mkQ t ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact htW
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k (A ⧸ W), φ (W.mkQ t) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hq ((Module.forall_dual_apply_eq_zero_iff k _).mp hcon)
  set l : A →ₗ[k] k := (φ (W.mkQ t))⁻¹ • (φ ∘ₗ W.mkQ) with hl
  have hlt : l t = 1 := by
    rw [hl, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, inv_mul_cancel₀ hφ]
  have hlW : ∀ a ∈ m * J, l a = 0 := by
    intro a ha
    have : W.mkQ a = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ha
    rw [hl, LinearMap.smul_apply, LinearMap.comp_apply, this, map_zero, smul_zero]
  have hdec : ∀ r : A, r - algebraMap k A (χ r) ∈ m := by
    intro r
    rw [hm, RingHom.mem_ker]
    simp
  let J₁ : Ideal A :=
    { carrier := {a | a ∈ J ∧ l a = 0}
      add_mem' := fun {a b} ha hb => ⟨J.add_mem ha.1 hb.1, by rw [map_add, ha.2, hb.2, add_zero]⟩
      zero_mem' := ⟨J.zero_mem, map_zero l⟩
      smul_mem' := fun c a ha => by
        refine ⟨J.mul_mem_left c ha.1, ?_⟩
        have hsplit : c * a = χ c • a + (c - algebraMap k A (χ c)) * a := by
          rw [Algebra.smul_def]
          ring
        change l (c * a) = 0
        rw [hsplit, map_add, map_smul, ha.2, smul_zero, zero_add]
        exact hlW _ (Ideal.mul_mem_mul (hdec c) ha.1) }
  have hmemJ₁ : ∀ a, a ∈ J₁ ↔ a ∈ J ∧ l a = 0 := fun a => Iff.rfl
  refine ⟨J₁, t, l, ?_, htJ, ?_, ?_, ?_, hlt⟩
  · rw [SetLike.lt_iff_le_and_exists]
    refine ⟨fun a ha => ((hmemJ₁ a).mp ha).1, t, htJ, fun h => ?_⟩
    have := ((hmemJ₁ t).mp h).2
    rw [hlt] at this
    exact one_ne_zero this
  · intro a ha
    refine ⟨l a, (hmemJ₁ _).mpr ⟨J.sub_mem ha (J.mul_mem_left _ htJ), ?_⟩⟩
    rw [← Algebra.smul_def, map_sub, map_smul, hlt, smul_eq_mul, mul_one, sub_self]
  · intro a ha
    exact (hmemJ₁ _).mpr ⟨J.mul_mem_left a htJ, hlW _ (Ideal.mul_mem_mul ha htJ)⟩
  · intro a ha
    exact ((hmemJ₁ a).mp ha).2

end GlobalTheory.CompanionTheory.Ar.Flat.StepIdeal
