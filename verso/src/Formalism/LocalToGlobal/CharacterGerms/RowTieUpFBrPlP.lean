import Formalism.LocalToGlobal.CharacterGerms.NatCastMulTmul

set_option autoImplicit false

noncomputable section

open TensorProduct IsLocalRing Polynomial

namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl

section Main

variable {l : ℕ} [Fact l.Prime] {OE : Type} [CommRing OE]

/- English proof (translation)
Use `completeA (l := l) (OE := OE)` as an intermediate fact. Take `⟨y, hy⟩` from `hε1`. Establish `h : ((1 : ℤ_[l]) ⊗ₜ[ℤ] ε) * ((1 : ℤ_[l]) ⊗ₜ[ℤ] ε) - (1 : ℤ_[l]) ⊗ₜ[ℤ] ε ∈ Ideal.span {((l : ℕ) : ℤ_[l] ⊗[ℤ] OE)}`. Rewrite using `[Ideal.mem_span_singleton']`. Use `⟨(1 : ℤ_[l]) ⊗ₜ[ℤ] y, ?_⟩` and prove the remaining obligations.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← TensorProduct.tmul_sub, hy, mul_comm, natCast_mul_tmul, mul_one, natCast_tmul]`. Take `⟨e, he, he'⟩` from `lift_idem _ _ h`. Rewrite `he'` using `[Ideal.mem_span_singleton']`. Take `⟨z, hz⟩` from `he'`. Conclude with `⟨e, z, he, by rw [← hz, mul_comm]⟩`.
-/
theorem exists_e [Module.Free ℤ OE] [Module.Finite ℤ OE] (ε : OE) (hε1 : ∃ y, ε * ε - ε = (l : OE) * y) :
    ∃ e z : ℤ_[l] ⊗[ℤ] OE, e * e = e ∧ e - 1 ⊗ₜ ε = ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * z := by
  have := completeA (l := l) (OE := OE)
  obtain ⟨y, hy⟩ := hε1
  have h : ((1 : ℤ_[l]) ⊗ₜ[ℤ] ε) * ((1 : ℤ_[l]) ⊗ₜ[ℤ] ε) - (1 : ℤ_[l]) ⊗ₜ[ℤ] ε ∈
      Ideal.span {((l : ℕ) : ℤ_[l] ⊗[ℤ] OE)} := by
    rw [Ideal.mem_span_singleton']
    refine ⟨(1 : ℤ_[l]) ⊗ₜ[ℤ] y, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← TensorProduct.tmul_sub, hy, mul_comm, natCast_mul_tmul,
      mul_one, natCast_tmul]
  obtain ⟨e, he, he'⟩ := lift_idem _ _ h
  rw [Ideal.mem_span_singleton'] at he'
  obtain ⟨z, hz⟩ := he'
  exact ⟨e, z, he, by rw [← hz, mul_comm]⟩

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra ℤ_[l] R] {d : ℕ} [NeZero d]
  (em : ZMod d → OE →+* R)

/- English proof (translation)
Establish `ht : tauX (l` using `l) (em a) (1 ⊗ₜ ε) = em a ε := by`. Simplify using `[tauX, Algebra.TensorProduct.lift_tmul]`. Establish `he' : e = 1 ⊗ₜ ε + ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * z` using `sub_eq_iff_eq_add'.1 he`. Express the relevant statement in the definitionally equal form `residue R (tauX (l := l) (em a) e) = 1`. Establish `h1 : residue R ((l : ℕ) : R) = 0`.

Rewrite using `[IsLocalRing.residue_eq_zero_iff]`. Conclude with `hl`. Establish `h2 : residue R (em a ε) = 1`. Rewrite using `[← sub_eq_zero, ← map_one (residue R), ← map_sub, IsLocalRing.residue_eq_zero_iff]`. Conclude with `hε2 a`.

Rewrite using `[he', map_add, map_mul, map_natCast, ht, map_add, map_mul, h1, h2, zero_mul, add_zero]`.
-/
theorem chi_e (hl : ((l : ℕ) : R) ∈ maximalIdeal R) {ε : OE} (hε2 : ∀ a, em a ε - 1 ∈ maximalIdeal R)
    {e z : ℤ_[l] ⊗[ℤ] OE} (he : e - 1 ⊗ₜ ε = ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * z) (a : ZMod d) : chi (em a) e = 1 := by
  have ht : tauX (l := l) (em a) (1 ⊗ₜ ε) = em a ε := by
    simp [tauX, Algebra.TensorProduct.lift_tmul]
  have he' : e = 1 ⊗ₜ ε + ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * z := sub_eq_iff_eq_add'.1 he
  change residue R (tauX (l := l) (em a) e) = 1
  have h1 : residue R ((l : ℕ) : R) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact hl
  have h2 : residue R (em a ε) = 1 := by
    rw [← sub_eq_zero, ← map_one (residue R), ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hε2 a
  rw [he', map_add, map_mul, map_natCast, ht, map_add, map_mul, h1, h2, zero_mul, add_zero]

/- English proof (translation)
Establish `hc` using `chi_e em hl hε2 he a`. Establish `hid : tauX (l` using `l) (em a) e * tauX (l := l) (em a) e = tauX (l := l) (em a) e := by`. Rewrite using `[← map_mul, hee]`. Establish `h2 : tauX (l` using `l) (em a) e * (tauX (l := l) (em a) e - 1) = 0 := by`. Rewrite using `[mul_sub, hid, mul_one, sub_self]`.

Break down `mul_eq_zero.1 h2 with h0 | h1` into its components or cases. It suffices to derive a contradiction. Establish `h3 : chi (l` using `l) (em a) e = 0 := by`. Express the relevant statement in the definitionally equal form `residue R (tauX (l := l) (em a) e) = 0`. Rewrite using `[h0, map_zero]`.

Rewrite `h3` using `[hc]`. Conclude with `one_ne_zero h3`. Conclude with `sub_eq_zero.1 h1`.
-/
theorem tau_e (hl : ((l : ℕ) : R) ∈ maximalIdeal R) {ε : OE} (hε2 : ∀ a, em a ε - 1 ∈ maximalIdeal R)
    {e z : ℤ_[l] ⊗[ℤ] OE} (hee : e * e = e) (he : e - 1 ⊗ₜ ε = ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * z) (a : ZMod d) :
    tauX (em a) e = 1 := by
  have hc := chi_e em hl hε2 he a
  have hid : tauX (l := l) (em a) e * tauX (l := l) (em a) e = tauX (l := l) (em a) e := by
    rw [← map_mul, hee]
  have h2 : tauX (l := l) (em a) e * (tauX (l := l) (em a) e - 1) = 0 := by
    rw [mul_sub, hid, mul_one, sub_self]
  rcases mul_eq_zero.1 h2 with h0 | h1
  · exfalso
    have h3 : chi (l := l) (em a) e = 0 := by
      change residue R (tauX (l := l) (em a) e) = 0
      rw [h0, map_zero]
    rw [hc] at h3
    exact one_ne_zero h3
  · exact sub_eq_zero.1 h1

/- English proof (translation)
Use `completeA (l := l) (OE := OE)` as an intermediate fact. Establish `hz : ∀ g : ℤ_[l] ⊗[ℤ] OE, g * g = g → e * g = g → chi (em 0) g = 0 → g = 0`. Introduce `g hg heg h0`. Take `⟨w, hw⟩` from `key em hl hfrob hε3 he heg h0`. Conclude with `idem_zero (Ideal.span {((l : ℕ) : ℤ_[l] ⊗[ℤ] OE)}) hg (by rw [hw]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))`.

Establish `hu : chi (em 0) f * chi (em 0) f = chi (em 0) f` using `by rw [← map_mul, hf]`. Establish `hu' : chi (em 0) f * (chi (em 0) f - 1) = 0` using `by linear_combination hu`. Break down `mul_eq_zero.1 hu' with h | h` into its components or cases. Use `left`. Conclude with `hz f hf (by rw [mul_comm]; exact hfe) h`.

Use `right`. Use `hz (e - f) (by linear_combination hee - 2 * hfe + hf) (by linear_combination hee - hfe) (by rw [map_sub, chi_e em hl hε2 he 0, sub_eq_zero.1 h, sub_self])` as an intermediate fact. Conclude with `(sub_eq_zero.1 this).symm`.
-/
theorem prim_e [Module.Free ℤ OE] [Module.Finite ℤ OE] (hl : ((l : ℕ) : R) ∈ maximalIdeal R)
    (hfrob : ∀ a x, em (a + 1) x - em a x ^ l ∈ maximalIdeal R) {ε : OE}
    (hε2 : ∀ a, em a ε - 1 ∈ maximalIdeal R)
    (hε3 : ∀ x : OE, (∀ a, em a x ∈ maximalIdeal R) → ∃ y, ε * x = (l : OE) * y)
    {e z : ℤ_[l] ⊗[ℤ] OE} (hee : e * e = e) (he : e - 1 ⊗ₜ ε = ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * z)
    (f : ℤ_[l] ⊗[ℤ] OE) (hf : f * f = f) (hfe : f * e = f) : f = 0 ∨ f = e := by
  have := completeA (l := l) (OE := OE)
  have hz : ∀ g : ℤ_[l] ⊗[ℤ] OE, g * g = g → e * g = g → chi (em 0) g = 0 → g = 0 := by
    intro g hg heg h0
    obtain ⟨w, hw⟩ := key em hl hfrob hε3 he heg h0
    exact idem_zero (Ideal.span {((l : ℕ) : ℤ_[l] ⊗[ℤ] OE)}) hg
      (by rw [hw]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  have hu : chi (em 0) f * chi (em 0) f = chi (em 0) f := by rw [← map_mul, hf]
  have hu' : chi (em 0) f * (chi (em 0) f - 1) = 0 := by linear_combination hu
  rcases mul_eq_zero.1 hu' with h | h
  · left
    exact hz f hf (by rw [mul_comm]; exact hfe) h
  · right
    have := hz (e - f) (by linear_combination hee - 2 * hfe + hf) (by linear_combination hee - hfe)
      (by rw [map_sub, chi_e em hl hε2 he 0, sub_eq_zero.1 h, sub_self])
    exact (sub_eq_zero.1 this).symm

/- English proof (translation)
Establish `hy : e * x ∈ LinearMap.range (LinearMap.mulLeft ℤ_[l] e)` using `⟨x, by simp⟩`. Use `⟨b.repr ⟨e * x, hy⟩, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg Subtype.val (b.sum_repr ⟨e * x, hy⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at h`. Conclude with `h.symm`.
-/
theorem hb_of {ι : Type} [Fintype ι] (e : ℤ_[l] ⊗[ℤ] OE)
    (b : Module.Basis ι ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e))) (x : ℤ_[l] ⊗[ℤ] OE) :
    ∃ r : ι → ℤ_[l], e * x = ∑ i, r i • (b i : ℤ_[l] ⊗[ℤ] OE) := by
  have hy : e * x ∈ LinearMap.range (LinearMap.mulLeft ℤ_[l] e) := ⟨x, by simp⟩
  refine ⟨b.repr ⟨e * x, hy⟩, ?_⟩
  have h := congrArg Subtype.val (b.sum_repr ⟨e * x, hy⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h
  exact h.symm

/- English proof (translation)
Establish `ht : ∀ τ : OE →+* R, ∀ x : OE, tauX (l` using `l) τ (1 ⊗ₜ x) = τ x := by`. Introduce `τ x`. Simplify using `[tauX, Algebra.TensorProduct.lift_tmul]`. Introduce `a a' hchi`. Assume the negation of the conclusion as `hne`.

Take `⟨x, hx⟩` from `hsep a a' hne`. Apply `hx` to reduce the goal to its premises. Establish `h1 : chi (l` using `l) (em a) (1 ⊗ₜ x) = chi (l := l) (em a') (1 ⊗ₜ x) := by`. Rewrite using `[show chi (l := l) (em a) = chi (l := l) (em a') from hchi]`. Express the relevant statement in the definitionally equal form `residue R (tauX (l := l) (em a) (1 ⊗ₜ x)) = residue R (tauX (l := l) (em a') (1 ⊗ₜ x)) at h1`.

Rewrite `h1` using `[ht, ht, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]`. Conclude with `h1`.
-/
theorem chi_inj (hsep : ∀ a a', a ≠ a' → ∃ x, em a x - em a' x ∉ maximalIdeal R) :
    Function.Injective fun a => chi (l := l) (em a) := by
  have ht : ∀ τ : OE →+* R, ∀ x : OE, tauX (l := l) τ (1 ⊗ₜ x) = τ x := by
    intro τ x
    simp [tauX, Algebra.TensorProduct.lift_tmul]
  intro a a' hchi
  by_contra hne
  obtain ⟨x, hx⟩ := hsep a a' hne
  apply hx
  have h1 : chi (l := l) (em a) (1 ⊗ₜ x) = chi (l := l) (em a') (1 ⊗ₜ x) := by
    rw [show chi (l := l) (em a) = chi (l := l) (em a') from hchi]
  change residue R (tauX (l := l) (em a) (1 ⊗ₜ x)) = residue R (tauX (l := l) (em a') (1 ⊗ₜ x)) at h1
  rw [ht, ht, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff] at h1
  exact h1

/- English proof (translation)
Use `card_le_of_chars (F := ℤ_[l]) (fun a => chi (l := l) (em a)) (chi_inj em hsep) ((residue R).comp (algebraMap ℤ_[l] R)) (fun a r => chi_alg (em a) r) e (chi_e em hl hε2 he) (fun i => (b i : ℤ_[l] ⊗[ℤ] OE)) (hb_of e b)` as an intermediate fact. Simplify `this` using `[ZMod.card]`.
-/
theorem le_rank (hl : ((l : ℕ) : R) ∈ maximalIdeal R)
    (hsep : ∀ a a', a ≠ a' → ∃ x, em a x - em a' x ∉ maximalIdeal R) {ε : OE}
    (hε2 : ∀ a, em a ε - 1 ∈ maximalIdeal R)
    {e z : ℤ_[l] ⊗[ℤ] OE} (he : e - 1 ⊗ₜ ε = ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * z) {n : ℕ}
    (b : Module.Basis (Fin n) ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e))) : d ≤ n := by
  have := card_le_of_chars (F := ℤ_[l]) (fun a => chi (l := l) (em a)) (chi_inj em hsep)
    ((residue R).comp (algebraMap ℤ_[l] R)) (fun a r => chi_alg (em a) r) e (chi_e em hl hε2 he)
    (fun i => (b i : ℤ_[l] ⊗[ℤ] OE)) (hb_of e b)
  simpa [ZMod.card] using this

/- English proof (translation)
Establish `hl0 : residue R ((l : ℕ) : R) = 0`. Rewrite using `[IsLocalRing.residue_eq_zero_iff]`. Conclude with `hl`. Establish `hlk : ((l : ℕ) : IsLocalRing.ResidueField R) = 0`. Establish `h` using `map_natCast (residue R) l`.

Rewrite using `[← h]`. Conclude with `hl0`. Use `haveI : CharP (IsLocalRing.ResidueField R) l := by`. Conclude with `(CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)).2 hlk`. Establish `hstep : ∀ (a : ZMod d) (x : OE), residue R (em (a + 1) x) = residue R (em a x) ^ l`.

Introduce `a x`. Rewrite using `[← map_pow, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]`. Conclude with `hfrob a x`. Establish `hiter : ∀ (n : ℕ) (x : OE), residue R (em (n : ZMod d) x) = residue R (em 0 x) ^ (l ^ n)`. Introduce `n x`.

Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [Nat.cast_succ, hstep, ih, ← pow_mul, pow_succ]`. Establish `htx : ∀ x : OE, tauX (l` using `l) (em 0) (1 ⊗ₜ x) = em 0 x := by`. Introduce `x`.

Simplify using `[tauX, Algebra.TensorProduct.lift_tmul]`. Establish `hx : ∀ x : OE, chi (l` using `l) (em 0) (1 ⊗ₜ x) ^ (l ^ d) = chi (l := l) (em 0) (1 ⊗ₜ x) := by`. Introduce `x`. Express the relevant statement in the definitionally equal form `residue R (tauX (l := l) (em 0) (1 ⊗ₜ x)) ^ (l ^ d) = residue R (tauX (l := l) (em 0) (1 ⊗ₜ x))`. Rewrite using `[htx, ← hiter d x, ZMod.natCast_self]`.

Establish `hnat : ∀ a : ℕ, ((a : IsLocalRing.ResidueField R)) ^ (l ^ d) = (a : IsLocalRing.ResidueField R)`. Introduce `a`. Establish `h0 : ((a : ZMod l)) ^ (l ^ d) = (a : ZMod l)` using `ZMod.pow_card_pow _`. Establish `h` using `congrArg (ZMod.castHom (dvd_refl l) (IsLocalRing.ResidueField R)) h0`. Rewrite `h` using `[map_pow, map_natCast]`. Then use the resulting hypothesis.

Establish `hc : ∀ c : ℤ_[l], chi (l` using `l) (em 0) (c ⊗ₜ (1 : OE)) ^ (l ^ d) = chi (l := l) (em 0) (c ⊗ₜ (1 : OE)) := by`. Introduce `c`. Establish `htc : tauX (l` using `l) (em 0) (c ⊗ₜ (1 : OE)) = algebraMap ℤ_[l] R c := by`. Simplify using `[tauX, Algebra.TensorProduct.lift_tmul]`. Express the relevant statement in the definitionally equal form `residue R (tauX (l := l) (em 0) (c ⊗ₜ (1 : OE))) ^ (l ^ d) = residue R (tauX (l := l) (em 0) (c ⊗ₜ (1 : OE)))`.

Rewrite using `[htc]`. Take `⟨y, hy⟩` from `Ideal.mem_span_singleton'.1 (PadicInt.appr_spec 1 c)`. Take `⟨a, ha⟩ : ∃ a, a = c.appr 1` from `⟨_, rfl⟩`. Rewrite `hy` using `[← ha, pow_one]`. Establish `hc' : c = ((a : ℕ) : ℤ_[l]) + y * ((l : ℕ) : ℤ_[l])`.

Rewrite using `[hy]`. Expand and normalize the polynomial expressions, which then agree. Establish `hr : residue R (algebraMap ℤ_[l] R c) = (a : IsLocalRing.ResidueField R)`. Rewrite using `[hc', map_add, map_mul, map_natCast, map_natCast, map_add, map_mul, hl0, mul_zero, add_zero, map_natCast]`. Rewrite using `[hr, hnat]`.

Proceed by induction on `s using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)]`. Consider the case `tmul c x`. Establish `hsplit : c ⊗ₜ[ℤ] x = (c ⊗ₜ[ℤ] (1 : OE)) * ((1 : ℤ_[l]) ⊗ₜ[ℤ] x)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`.

Rewrite using `[hsplit, map_mul, mul_pow, hc c, hx x]`. Consider the case `add s t hs ht => rw [map_add, add_pow_char_pow, hs, ht]`.
-/
theorem chi_pow (hl : ((l : ℕ) : R) ∈ maximalIdeal R)
    (hfrob : ∀ a x, em (a + 1) x - em a x ^ l ∈ maximalIdeal R) (s : ℤ_[l] ⊗[ℤ] OE) :
    chi (em 0) s ^ (l ^ d) = chi (em 0) s := by
  have hl0 : residue R ((l : ℕ) : R) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact hl
  have hlk : ((l : ℕ) : IsLocalRing.ResidueField R) = 0 := by
    have h := map_natCast (residue R) l
    rw [← h]
    exact hl0
  haveI : CharP (IsLocalRing.ResidueField R) l := by
    exact (CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)).2 hlk
  have hstep : ∀ (a : ZMod d) (x : OE), residue R (em (a + 1) x) = residue R (em a x) ^ l := by
    intro a x
    rw [← map_pow, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hfrob a x
  have hiter : ∀ (n : ℕ) (x : OE), residue R (em (n : ZMod d) x) = residue R (em 0 x) ^ (l ^ n) := by
    intro n x
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ, hstep, ih, ← pow_mul, pow_succ]
  have htx : ∀ x : OE, tauX (l := l) (em 0) (1 ⊗ₜ x) = em 0 x := by
    intro x
    simp [tauX, Algebra.TensorProduct.lift_tmul]
  have hx : ∀ x : OE, chi (l := l) (em 0) (1 ⊗ₜ x) ^ (l ^ d) = chi (l := l) (em 0) (1 ⊗ₜ x) := by
    intro x
    change residue R (tauX (l := l) (em 0) (1 ⊗ₜ x)) ^ (l ^ d) = residue R (tauX (l := l) (em 0) (1 ⊗ₜ x))
    rw [htx, ← hiter d x, ZMod.natCast_self]
  have hnat : ∀ a : ℕ, ((a : IsLocalRing.ResidueField R)) ^ (l ^ d) = (a : IsLocalRing.ResidueField R) := by
    intro a
    have h0 : ((a : ZMod l)) ^ (l ^ d) = (a : ZMod l) := ZMod.pow_card_pow _
    have h := congrArg (ZMod.castHom (dvd_refl l) (IsLocalRing.ResidueField R)) h0
    rwa [map_pow, map_natCast] at h
  have hc : ∀ c : ℤ_[l], chi (l := l) (em 0) (c ⊗ₜ (1 : OE)) ^ (l ^ d) = chi (l := l) (em 0) (c ⊗ₜ (1 : OE)) := by
    intro c
    have htc : tauX (l := l) (em 0) (c ⊗ₜ (1 : OE)) = algebraMap ℤ_[l] R c := by
      simp [tauX, Algebra.TensorProduct.lift_tmul]
    change residue R (tauX (l := l) (em 0) (c ⊗ₜ (1 : OE))) ^ (l ^ d) =
      residue R (tauX (l := l) (em 0) (c ⊗ₜ (1 : OE)))
    rw [htc]
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec 1 c)
    obtain ⟨a, ha⟩ : ∃ a, a = c.appr 1 := ⟨_, rfl⟩
    rw [← ha, pow_one] at hy
    have hc' : c = ((a : ℕ) : ℤ_[l]) + y * ((l : ℕ) : ℤ_[l]) := by
      rw [hy]
      ring
    have hr : residue R (algebraMap ℤ_[l] R c) = (a : IsLocalRing.ResidueField R) := by
      rw [hc', map_add, map_mul, map_natCast, map_natCast, map_add, map_mul, hl0, mul_zero, add_zero,
        map_natCast]
    rw [hr, hnat]
  induction s using TensorProduct.induction_on with
  | zero => rw [map_zero, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)]
  | tmul c x =>
    have hsplit : c ⊗ₜ[ℤ] x = (c ⊗ₜ[ℤ] (1 : OE)) * ((1 : ℤ_[l]) ⊗ₜ[ℤ] x) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hsplit, map_mul, mul_pow, hc c, hx x]
  | add s t hs ht => rw [map_add, add_pow_char_pow, hs, ht]

/- English proof (translation)
Establish `hl1 : 1 < l` using `(Fact.out : l.Prime).one_lt`. Establish `hq : 1 < l ^ d` using `Nat.one_lt_pow (NeZero.ne d) hl1`. Establish `hP0 : (X ^ (l ^ d) - X : (ResidueField R)[X]) ≠ 0` using `FiniteField.X_pow_card_sub_X_ne_zero _ hq`. Establish `hroot : ∀ s : ℤ_[l] ⊗[ℤ] OE, chi (em 0) s ∈ (X ^ (l ^ d) - X : (ResidueField R)[X]).roots.toFinset`. Introduce `s`.

Rewrite using `[Multiset.mem_toFinset, mem_roots hP0, IsRoot.def, eval_sub, eval_pow, eval_X, chi_pow em hl hfrob, sub_self]`. Establish `heb : ∀ i, e * (b i : ℤ_[l] ⊗[ℤ] OE) = b i`. Introduce `i`. Take `⟨x, hx⟩` from `(b i).2`. Rewrite using `[← hx]`.

Use `show e * (e * x) = e * x`. Rewrite using `[← mul_assoc, hee]`. Set `S : (Fin n → Fin l) → ℤ_[l] ⊗[ℤ] OE` to `fun r => ∑ i, (((r i : ℕ) : ℤ_[l])) • (b i : ℤ_[l] ⊗[ℤ] OE)`. Establish `heS : ∀ r, e * S r = S r`. Introduce `r`.

Simplify using `only [S, Finset.mul_sum, mul_smul_comm, heb]`. Set `Ψ : (Fin n → Fin l) → ResidueField R` to `fun r => chi (em 0) (S r)`. Establish `hinj : Function.Injective Ψ`. Introduce `r r' h`. Establish `h0 : chi (em 0) (S r - S r') = 0`.

Rewrite using `[map_sub, sub_eq_zero]`. Conclude with `h`. Take `⟨w, hw⟩` from `key em hl hfrob hε3 he (s := S r - S r') (by rw [mul_sub, heS, heS]) h0`. Take `⟨c, hc⟩` from `hb_of e b w`. Establish `h1 : S r - S r' = ∑ i, (((l : ℕ) : ℤ_[l]) * c i) • (b i : ℤ_[l] ⊗[ℤ] OE)`.

Establish `h2 : S r - S r' = ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * (e * w)`. Establish `h3 : e * (S r - S r') = S r - S r'` using `by rw [mul_sub, heS, heS]`. Rewrite using `[← h3, hw]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2, hc, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul, ← map_natCast (algebraMap ℤ_[l] (ℤ_[l] ⊗[ℤ] OE)), ← Algebra.smul_def]`. Establish `h4 : ∑ i, ((((r i : ℕ) : ℤ_[l])) - (((r' i : ℕ) : ℤ_[l])) - ((l : ℕ) : ℤ_[l]) * c i) • b i = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `: ∑ i, ((((r i : ℕ) : ℤ_[l])) - (((r' i : ℕ) : ℤ_[l])) - ((l : ℕ) : ℤ_[l]) * c i) • (b i : ℤ_[l] ⊗[ℤ] OE) = 0`.

Simplify using `only [sub_smul, Finset.sum_sub_distrib]`. Rewrite using `[← h1]`. Simplify using `only [S]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `using this`.

Establish `h5` using `Fintype.linearIndependent_iff.1 b.linearIndependent _ h4`. Use function extensionality and compare the values at `i`. Establish `h6` using `congrArg (PadicInt.toZMod (p := l)) (h5 i)`. Simplify using `only [map_sub, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, sub_zero, map_zero] at h6`. Establish `h7 : ((r i : ℕ) : ZMod l) = ((r' i : ℕ) : ZMod l)` using `sub_eq_zero.1 h6`.

Rewrite `h7` using `[ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (r i).2, Nat.mod_eq_of_lt (r' i).2]`. Conclude with `Fin.ext h7`. Establish `h8 : (Finset.univ : Finset (Fin n → Fin l)).card ≤ (X ^ (l ^ d) - X : (ResidueField R)[X]).roots.toFinset.card` using `Finset.card_le_card_of_injOn Ψ (fun r _ => hroot _) (fun r _ r' _ h => hinj h)`. Establish `h9 : (X ^ (l ^ d) - X : (ResidueField R)[X]).roots.toFinset.card ≤ l ^ d`. Use `le_trans (Multiset.toFinset_card_le _) (le_trans (card_roots' _) ?_)` and prove the remaining obligations.

Rewrite using `[FiniteField.X_pow_card_sub_X_natDegree_eq _ hq]`. Establish `h10 : l ^ n ≤ l ^ d`. Establish `: (Finset.univ : Finset (Fin n → Fin l)).card = l ^ n` using `by simp`. Rewrite using `[← this]`. Conclude with `le_trans h8 h9`.

Conclude with `(Nat.pow_le_pow_iff_right hl1).1 h10`.
-/
theorem rank_le (hl : ((l : ℕ) : R) ∈ maximalIdeal R)
    (hfrob : ∀ a x, em (a + 1) x - em a x ^ l ∈ maximalIdeal R) {ε : OE}
    (hε3 : ∀ x : OE, (∀ a, em a x ∈ maximalIdeal R) → ∃ y, ε * x = (l : OE) * y)
    {e z : ℤ_[l] ⊗[ℤ] OE} (hee : e * e = e) (he : e - 1 ⊗ₜ ε = ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * z) {n : ℕ}
    (b : Module.Basis (Fin n) ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e))) : n ≤ d := by
  classical
  have hl1 : 1 < l := (Fact.out : l.Prime).one_lt
  have hq : 1 < l ^ d := Nat.one_lt_pow (NeZero.ne d) hl1
  have hP0 : (X ^ (l ^ d) - X : (ResidueField R)[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero _ hq
  have hroot : ∀ s : ℤ_[l] ⊗[ℤ] OE, chi (em 0) s ∈ (X ^ (l ^ d) - X : (ResidueField R)[X]).roots.toFinset := by
    intro s
    rw [Multiset.mem_toFinset, mem_roots hP0, IsRoot.def, eval_sub, eval_pow, eval_X, chi_pow em hl hfrob, sub_self]
  have heb : ∀ i, e * (b i : ℤ_[l] ⊗[ℤ] OE) = b i := by
    intro i
    obtain ⟨x, hx⟩ := (b i).2
    rw [← hx]
    show e * (e * x) = e * x
    rw [← mul_assoc, hee]
  let S : (Fin n → Fin l) → ℤ_[l] ⊗[ℤ] OE := fun r => ∑ i, (((r i : ℕ) : ℤ_[l])) • (b i : ℤ_[l] ⊗[ℤ] OE)
  have heS : ∀ r, e * S r = S r := by
    intro r
    simp only [S, Finset.mul_sum, mul_smul_comm, heb]
  let Ψ : (Fin n → Fin l) → ResidueField R := fun r => chi (em 0) (S r)
  have hinj : Function.Injective Ψ := by
    intro r r' h
    have h0 : chi (em 0) (S r - S r') = 0 := by
      rw [map_sub, sub_eq_zero]
      exact h
    obtain ⟨w, hw⟩ := key em hl hfrob hε3 he (s := S r - S r') (by rw [mul_sub, heS, heS]) h0
    obtain ⟨c, hc⟩ := hb_of e b w
    have h1 : S r - S r' = ∑ i, (((l : ℕ) : ℤ_[l]) * c i) • (b i : ℤ_[l] ⊗[ℤ] OE) := by
      have h2 : S r - S r' = ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * (e * w) := by
        have h3 : e * (S r - S r') = S r - S r' := by rw [mul_sub, heS, heS]
        rw [← h3, hw]
        ring
      rw [h2, hc, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul, ← map_natCast (algebraMap ℤ_[l] (ℤ_[l] ⊗[ℤ] OE)), ← Algebra.smul_def]
    have h4 : ∑ i, ((((r i : ℕ) : ℤ_[l])) - (((r' i : ℕ) : ℤ_[l])) - ((l : ℕ) : ℤ_[l]) * c i) • b i = 0 := by
      apply Subtype.ext
      have : ∑ i, ((((r i : ℕ) : ℤ_[l])) - (((r' i : ℕ) : ℤ_[l])) - ((l : ℕ) : ℤ_[l]) * c i) •
          (b i : ℤ_[l] ⊗[ℤ] OE) = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib]
        rw [← h1]
        simp only [S]
        ring
      simpa using this
    have h5 := Fintype.linearIndependent_iff.1 b.linearIndependent _ h4
    funext i
    have h6 := congrArg (PadicInt.toZMod (p := l)) (h5 i)
    simp only [map_sub, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, sub_zero, map_zero] at h6
    have h7 : ((r i : ℕ) : ZMod l) = ((r' i : ℕ) : ZMod l) := sub_eq_zero.1 h6
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (r i).2, Nat.mod_eq_of_lt (r' i).2] at h7
    exact Fin.ext h7
  have h8 : (Finset.univ : Finset (Fin n → Fin l)).card ≤
      (X ^ (l ^ d) - X : (ResidueField R)[X]).roots.toFinset.card :=
    Finset.card_le_card_of_injOn Ψ (fun r _ => hroot _) (fun r _ r' _ h => hinj h)
  have h9 : (X ^ (l ^ d) - X : (ResidueField R)[X]).roots.toFinset.card ≤ l ^ d := by
    refine le_trans (Multiset.toFinset_card_le _) (le_trans (card_roots' _) ?_)
    rw [FiniteField.X_pow_card_sub_X_natDegree_eq _ hq]
  have h10 : l ^ n ≤ l ^ d := by
    have : (Finset.univ : Finset (Fin n → Fin l)).card = l ^ n := by simp
    rw [← this]
    exact le_trans h8 h9
  exact (Nat.pow_le_pow_iff_right hl1).1 h10

/- English proof (translation)
Use extensionality with `x`. Establish `hx` using `h (1 ⊗ₜ x)`. Simplify `hx` using `[tauX, Algebra.TensorProduct.lift_tmul]`.
-/
theorem tauX_inj {τ τ' : OE →+* R} (h : ∀ s, tauX (l := l) τ s = tauX τ' s) : τ = τ' := by
  ext x
  have hx := h (1 ⊗ₜ x)
  simpa [tauX, Algebra.TensorProduct.lift_tmul] using hx

/- English proof (translation)
Introduce `a a' h`. Assume the negation of the conclusion as `hne`. Take `⟨x, hx⟩` from `hsep a a' hne`. Apply `hx` to reduce the goal to its premises. Rewrite using `[h, sub_self]`.

Conclude with `Ideal.zero_mem _`.
-/
theorem em_inj (hsep : ∀ a a', a ≠ a' → ∃ x, em a x - em a' x ∉ maximalIdeal R) : Function.Injective em := by
  intro a a' h
  by_contra hne
  obtain ⟨x, hx⟩ := hsep a a' hne
  apply hx
  rw [h, sub_self]
  exact Ideal.zero_mem _

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Set `ff : Option (ZMod d) → OE →+* R` to `fun o => o.elim τ em`. Establish `hff : Function.Injective ff`. Introduce `o o' h`.

Consider the cases of `o with`. Consider the case `none`. Consider the cases of `o' with`. Consider the case `none => rfl`. Consider the case `some a' => exact absurd h (hne a')`.

Consider the case `some a`. Consider the cases of `o' with`. Consider the case `none => exact absurd h.symm (hne a)`. Consider the case `some a' => exact congrArg some (em_inj em hsep h)`. Set `χ : Option (ZMod d) → (ℤ_[l] ⊗[ℤ] OE) →+* FractionRing R` to `fun o => (algebraMap R (FractionRing R)).comp (tauX (ff o)).toRingHom`.

Establish `hχ : Function.Injective χ`. Introduce `o o' h`. Apply `hff` to reduce the goal to its premises. Apply `tauX_inj (l := l)` to reduce the goal to its premises. Introduce `s`.

Conclude with `IsFractionRing.injective R (FractionRing R) (DFunLike.congr_fun h s)`. Use `card_le_of_chars (F := ℤ_[l]) χ hχ ((algebraMap R (FractionRing R)).comp (algebraMap ℤ_[l] R)) (fun o r => by show algebraMap R (FractionRing R) (tauX (ff o) (algebraMap ℤ_[l] _ r)) = _` as an intermediate fact. Rewrite using `[AlgHom.commutes]`. Use the proof step `rfl) e`. Use the proof step `(fun o => by show algebraMap R (FractionRing R) (tauX (ff o) e) = 1`.

Consider the cases of `o with`. Consider the case `none => show algebraMap R (FractionRing R) (tauX τ e) = 1`. Rewrite using `[hτ, map_one]`. Consider the case `some a => show algebraMap R (FractionRing R) (tauX (em a) e) = 1`. Rewrite using `[hte, map_one])`.

Use the proof step `(fun i => (b i : ℤ_[l] ⊗[ℤ] OE)) (hb_of e b)`. Simplify using `[ZMod.card] at this`.
-/
theorem emb_eq (hsep : ∀ a a', a ≠ a' → ∃ x, em a x - em a' x ∉ maximalIdeal R)
    {e : ℤ_[l] ⊗[ℤ] OE} (hte : ∀ a, tauX (em a) e = 1)
    (b : Module.Basis (Fin d) ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e)))
    (τ : OE →+* R) (hτ : tauX τ e = 1) : ∃ a, τ = em a := by
  by_contra hne
  push Not at hne
  let ff : Option (ZMod d) → OE →+* R := fun o => o.elim τ em
  have hff : Function.Injective ff := by
    intro o o' h
    cases o with
    | none =>
      cases o' with
      | none => rfl
      | some a' => exact absurd h (hne a')
    | some a =>
      cases o' with
      | none => exact absurd h.symm (hne a)
      | some a' => exact congrArg some (em_inj em hsep h)
  let χ : Option (ZMod d) → (ℤ_[l] ⊗[ℤ] OE) →+* FractionRing R :=
    fun o => (algebraMap R (FractionRing R)).comp (tauX (ff o)).toRingHom
  have hχ : Function.Injective χ := by
    intro o o' h
    apply hff
    apply tauX_inj (l := l)
    intro s
    exact IsFractionRing.injective R (FractionRing R) (DFunLike.congr_fun h s)
  have := card_le_of_chars (F := ℤ_[l]) χ hχ ((algebraMap R (FractionRing R)).comp (algebraMap ℤ_[l] R))
    (fun o r => by
      show algebraMap R (FractionRing R) (tauX (ff o) (algebraMap ℤ_[l] _ r)) = _
      rw [AlgHom.commutes]
      rfl) e
    (fun o => by
      show algebraMap R (FractionRing R) (tauX (ff o) e) = 1
      cases o with
      | none => show algebraMap R (FractionRing R) (tauX τ e) = 1; rw [hτ, map_one]
      | some a => show algebraMap R (FractionRing R) (tauX (em a) e) = 1; rw [hte, map_one])
    (fun i => (b i : ℤ_[l] ⊗[ℤ] OE)) (hb_of e b)
  simp [ZMod.card] at this

/- English proof (translation)
Establish `hdet` using `det_ne_zero_of_chars (F := ℤ_[l]) (fun j => chi (l := l) ((t j : EmbX (R := R) e) : OE →+* R)) (by`. Introduce `j j' h`. Take `⟨a, rfl⟩` from `jj.surjective j`. Take `⟨a', rfl⟩` from `jj.surjective j'`. Simplify using `only [ht] at h`.

Rewrite using `[chi_inj em hsep h])`. Use the proof step `((residue R).comp (algebraMap ℤ_[l] R)) (fun j r => chi_alg _ r) e`. Use the proof step `(fun j => by rw [chi_apply, (t j).2, map_one])`. Use the proof step `(fun i => (b i : ℤ_[l] ⊗[ℤ] OE)) (hb_of e b)`. Assume the negation of the conclusion as `hu`.

Apply `hdet` to reduce the goal to its premises. Establish `h1` using `(residue_eq_zero_iff _).2 ((mem_maximalIdeal _).2 hu)`. Rewrite `h1` using `[RingHom.map_det]`. Conclude with `h1`.
-/
theorem unit_det (hsep : ∀ a a', a ≠ a' → ∃ x, em a x - em a' x ∉ maximalIdeal R)
    {e : ℤ_[l] ⊗[ℤ] OE} {n : ℕ} (b : Module.Basis (Fin n) ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e)))
    (t : Fin n ≃ EmbX (R := R) e) (jj : ZMod d ≃ Fin n)
    (ht : ∀ a, ((t (jj a) : EmbX (R := R) e) : OE →+* R) = em a) :
    IsUnit (Matrix.det (Matrix.of fun i j =>
      tauX ((t j : EmbX (R := R) e) : OE →+* R) (b i : ℤ_[l] ⊗[ℤ] OE))) := by
  have hdet := det_ne_zero_of_chars (F := ℤ_[l]) (fun j => chi (l := l) ((t j : EmbX (R := R) e) : OE →+* R))
    (by
      intro j j' h
      obtain ⟨a, rfl⟩ := jj.surjective j
      obtain ⟨a', rfl⟩ := jj.surjective j'
      simp only [ht] at h
      rw [chi_inj em hsep h])
    ((residue R).comp (algebraMap ℤ_[l] R)) (fun j r => chi_alg _ r) e
    (fun j => by rw [chi_apply, (t j).2, map_one])
    (fun i => (b i : ℤ_[l] ⊗[ℤ] OE)) (hb_of e b)
  by_contra hu
  apply hdet
  have h1 := (residue_eq_zero_iff _).2 ((mem_maximalIdeal _).2 hu)
  rw [RingHom.map_det] at h1
  exact h1

/- English proof (translation)
Take `⟨e, z, hee, he⟩` from `exists_e ε hε1`. Establish `hte : ∀ a, tauX (em a) e = 1` using `tau_e em hl hε2 hee he`. Establish `he0 : e ≠ 0`. Introduce `h0`. Establish `h1` using `hte 0`.

Rewrite `h1` using `[h0, map_zero]`. Conclude with `zero_ne_one h1`. Establish `hprim` using `prim_e em hl hfrob hε2 hε3 hee he`. Use `haveI : Module.Free ℤ_[l] (ℤ_[l] ⊗[ℤ] OE) := inferInstance`. Use `haveI : Module.Finite ℤ_[l] (ℤ_[l] ⊗[ℤ] OE) := inferInstance`.

Use `haveI : Module.Finite ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e)) := inferInstance`. Use `haveI : Module.Free ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e)) := by first`. Consider the case `infer_instance`. Consider the case `exact Module.free_of_finite_type_torsion_free'`. Use `set n := Module.finrank ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e)) with hn`.

Set `b` to `Module.finBasis ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e))`. Establish `hdn : d = n` using `le_antisymm (le_rank em hl hsep hε2 he b) (rank_le em hl hfrob hε3 hee he b)`. Use `haveI : NeZero n := ⟨by rw [← hdn]; exact NeZero.ne d⟩`. Establish `hinj : Function.Injective (fun a : ZMod d => (⟨em a, hte a⟩ : EmbX (R` using `R) e)) := fun a a' h => em_inj em hsep (congrArg Subtype.val h)`. Establish `hsurj : Function.Surjective (fun a : ZMod d => (⟨em a, hte a⟩ : EmbX (R` using `R) e)) := by`.

Introduce `τ`. Take `⟨a, ha⟩` from `emb_eq em hsep hte (b.reindex (finCongr hdn.symm)) τ.1 τ.2`. Conclude with `⟨a, Subtype.ext ha.symm⟩`. Set `jjr : ZMod d ≃+* Fin n` to `(ZMod.ringEquivCongr hdn).trans (ZMod.finEquiv n).symm`. Set `jj : ZMod d ≃ Fin n` to `jjr.toEquiv`.

Establish `hjj : ∀ a, jj (a + 1) = jj a + 1`. Introduce `a`. Use `show jjr (a + 1) = jjr a + 1`. Rewrite using `[map_add, map_one]`. Set `t : Fin n ≃ EmbX (R` to `R) e := jj.symm.trans (Equiv.ofBijective _ ⟨hinj, hsurj⟩)`.

Establish `ht : ∀ a, ((t (jj a) : EmbX (R` using `R) e) : OE →+* R) = em a := by`. Introduce `a`. Use `show (((Equiv.ofBijective _ ⟨hinj, hsurj⟩) (jj.symm (jj a)) : EmbX (R := R) e) : OE →+* R) = em a`. Rewrite using `[Equiv.symm_apply_apply]`. Both sides reduce to the same expression.

Conclude with `⟨e, hee, he0, hprim, inferInstance, t, jj, hjj, ht, b, unit_det em hsep b t jj ht⟩`.
-/
theorem placeX_of [Module.Free ℤ OE] [Module.Finite ℤ OE] (hl : ((l : ℕ) : R) ∈ maximalIdeal R)
    (hfrob : ∀ a x, em (a + 1) x - em a x ^ l ∈ maximalIdeal R)
    (hsep : ∀ a a', a ≠ a' → ∃ x, em a x - em a' x ∉ maximalIdeal R) (ε : OE)
    (hε1 : ∃ y, ε * ε - ε = (l : OE) * y) (hε2 : ∀ a, em a ε - 1 ∈ maximalIdeal R)
    (hε3 : ∀ x : OE, (∀ a, em a x ∈ maximalIdeal R) → ∃ y, ε * x = (l : OE) * y) : PlaceX l OE R d em := by
  classical
  obtain ⟨e, z, hee, he⟩ := exists_e ε hε1
  have hte : ∀ a, tauX (em a) e = 1 := tau_e em hl hε2 hee he
  have he0 : e ≠ 0 := by
    intro h0
    have h1 := hte 0
    rw [h0, map_zero] at h1
    exact zero_ne_one h1
  have hprim := prim_e em hl hfrob hε2 hε3 hee he
  haveI : Module.Free ℤ_[l] (ℤ_[l] ⊗[ℤ] OE) := inferInstance
  haveI : Module.Finite ℤ_[l] (ℤ_[l] ⊗[ℤ] OE) := inferInstance
  haveI : Module.Finite ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e)) := inferInstance
  haveI : Module.Free ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e)) := by
    first
    | infer_instance
    | exact Module.free_of_finite_type_torsion_free'
  set n := Module.finrank ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e)) with hn
  let b := Module.finBasis ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e))

  have hdn : d = n := le_antisymm (le_rank em hl hsep hε2 he b) (rank_le em hl hfrob hε3 hee he b)
  haveI : NeZero n := ⟨by rw [← hdn]; exact NeZero.ne d⟩

  have hinj : Function.Injective (fun a : ZMod d => (⟨em a, hte a⟩ : EmbX (R := R) e)) :=
    fun a a' h => em_inj em hsep (congrArg Subtype.val h)
  have hsurj : Function.Surjective (fun a : ZMod d => (⟨em a, hte a⟩ : EmbX (R := R) e)) := by
    intro τ
    obtain ⟨a, ha⟩ := emb_eq em hsep hte (b.reindex (finCongr hdn.symm)) τ.1 τ.2
    exact ⟨a, Subtype.ext ha.symm⟩
  let jjr : ZMod d ≃+* Fin n := (ZMod.ringEquivCongr hdn).trans (ZMod.finEquiv n).symm
  let jj : ZMod d ≃ Fin n := jjr.toEquiv
  have hjj : ∀ a, jj (a + 1) = jj a + 1 := by
    intro a
    show jjr (a + 1) = jjr a + 1
    rw [map_add, map_one]
  let t : Fin n ≃ EmbX (R := R) e := jj.symm.trans (Equiv.ofBijective _ ⟨hinj, hsurj⟩)
  have ht : ∀ a, ((t (jj a) : EmbX (R := R) e) : OE →+* R) = em a := by
    intro a
    show (((Equiv.ofBijective _ ⟨hinj, hsurj⟩) (jj.symm (jj a)) : EmbX (R := R) e) : OE →+* R) = em a
    rw [Equiv.symm_apply_apply]
    rfl
  exact ⟨e, hee, he0, hprim, inferInstance, t, jj, hjj, ht, b, unit_det em hsep b t jj ht⟩

end Main

/- English proof (translation)
Unfold `PlaceCriterionOfIdempotent`. Introduce `l _ OE _ _ _ _ _ R _ _ _ _ _ hl _ d _ em hfrob hsep hε`. Take `⟨ε, hε1, hε2, hε3⟩` from `hε`. Conclude with `placeX_of em hl hfrob hsep ε hε1 hε2 hε3`.
-/
theorem place_doubling_condition : PlaceCriterionOfIdempotent := by
  unfold PlaceCriterionOfIdempotent
  intro l _ OE _ _ _ _ _ R _ _ _ _ _ hl _ d _ em hfrob hsep hε
  obtain ⟨ε, hε1, hε2, hε3⟩ := hε
  exact placeX_of em hl hfrob hsep ε hε1 hε2 hε3

end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
