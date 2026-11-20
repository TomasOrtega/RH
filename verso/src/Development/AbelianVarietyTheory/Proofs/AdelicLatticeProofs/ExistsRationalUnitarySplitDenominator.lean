import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitaryCorrectionCongruentOneAtLevelStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdempotentAdelesAndSmallAdelicMatricesStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryGroupWeakApproximationAtPrimesStatement

noncomputable section

namespace GlobalTheory.UnRep.LatForm

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix nonZeroDivisors

/- English proof (translation)
Proceed by induction on `m using Nat.strong_induction_on with`. Consider the case `_ m ih`. Distinguish the cases in `h : Nat.gcd m N = 1`. Conclude with `⟨0, m, h, by simp⟩`. Take `⟨m', hm'⟩` from `Nat.gcd_dvd_left m N`.

Establish `hg : 0 < Nat.gcd m N` using `Nat.gcd_pos_of_pos_left _ hm`. Establish `hm'0 : 0 < m'` using `Nat.pos_of_ne_zero (by rintro rfl; simp at hm'; omega)`. Establish `hlt : m' < m`. Establish `: 2 ≤ Nat.gcd m N` using `by omega`. Use the polynomial consequences of the given equalities and inequalities.

Take `⟨j, u, hu, hd⟩` from `ih m' hlt hm'0`. Use `⟨j + 1, u, hu, ?_⟩` and prove the remaining obligations. Rewrite using `[hm', pow_succ, ← mul_assoc, mul_comm (Nat.gcd m N)]`. Conclude with `Nat.mul_dvd_mul hd (Nat.gcd_dvd_right m N)`.
-/
theorem exists_dvd_coprime_mul_pow (N : ℕ) (m : ℕ) (hm : 0 < m) :
    ∃ j u : ℕ, u.Coprime N ∧ m ∣ u * N ^ j := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases h : Nat.gcd m N = 1
    · exact ⟨0, m, h, by simp⟩
    · obtain ⟨m', hm'⟩ := Nat.gcd_dvd_left m N
      have hg : 0 < Nat.gcd m N := Nat.gcd_pos_of_pos_left _ hm
      have hm'0 : 0 < m' := Nat.pos_of_ne_zero (by rintro rfl; simp at hm'; omega)
      have hlt : m' < m := by
        have : 2 ≤ Nat.gcd m N := by omega
        nlinarith
      obtain ⟨j, u, hu, hd⟩ := ih m' hlt hm'0
      refine ⟨j + 1, u, hu, ?_⟩
      rw [hm', pow_succ, ← mul_assoc, mul_comm (Nat.gcd m N)]
      exact Nat.mul_dvd_mul hd (Nat.gcd_dvd_right m N)

/- English proof (translation)
Establish `key : ∀ j : ℕ, ∀ z ∈ Λ, ∃ y ∈ Λ, ∃ w ∈ Λ, t ^ j • k' z = y + N ^ j • k' w`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => intro z hz; exact ⟨0, Λ.zero_mem, z, hz, by simp⟩`. Consider the case `succ j ih`.

Introduce `z hz`. Take `⟨y, hy, w, hw, e⟩` from `ih z hz`. Take `⟨w', hw', e'⟩` from `h1 w hw`. Establish `e2 : t • k' w = t • w + N • k' (-w')`. Use `congrArg k' e'` as an intermediate fact.

Rewrite `this` using `[map_nsmul, map_nsmul, map_sub, hk, smul_sub]`. Rewrite using `[map_neg, smul_neg, ← this]`. Normalize the expressions using the abelian group laws. Use `⟨t • y + N ^ j • t • w, Λ.add_mem (Λ.nsmul_mem hy _) (Λ.nsmul_mem (Λ.nsmul_mem hw _) _), -w', Λ.neg_mem hw', ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ', mul_smul, e, smul_add, smul_comm t (N ^ j), e2, smul_add, pow_succ, mul_smul, add_assoc]`.

Take `⟨j, u, hu, q, hq⟩` from `exists_dvd_coprime_mul_pow N m hm`. Use `⟨u * t ^ j, Nat.Coprime.mul_left hu (Nat.Coprime.pow_left _ ht), fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, w, hw, e⟩` from `key j z hz`. Rewrite using `[mul_smul, e, smul_add, ← mul_smul, hq, mul_comm, mul_smul]`. Conclude with `Λ.add_mem (Λ.nsmul_mem hy _) (Λ.nsmul_mem (h2 w hw) _)`.
-/
theorem inv_integral {V : Type} [AddCommGroup V] (Λ : AddSubgroup V) (k k' : V →+ V)
    (hk : ∀ z, k' (k z) = z) (N t m : ℕ) (ht : t.Coprime N) (hm : 0 < m)
    (h1 : ∀ z ∈ Λ, ∃ w ∈ Λ, t • (k z - z) = N • w) (h2 : ∀ z ∈ Λ, m • k' z ∈ Λ) :
    ∃ t' : ℕ, t'.Coprime N ∧ ∀ z ∈ Λ, t' • k' z ∈ Λ := by
  have key : ∀ j : ℕ, ∀ z ∈ Λ, ∃ y ∈ Λ, ∃ w ∈ Λ, t ^ j • k' z = y + N ^ j • k' w := by
    intro j
    induction j with
    | zero => intro z hz; exact ⟨0, Λ.zero_mem, z, hz, by simp⟩
    | succ j ih =>
      intro z hz
      obtain ⟨y, hy, w, hw, e⟩ := ih z hz
      obtain ⟨w', hw', e'⟩ := h1 w hw
      have e2 : t • k' w = t • w + N • k' (-w') := by
        have := congrArg k' e'
        rw [map_nsmul, map_nsmul, map_sub, hk, smul_sub] at this
        rw [map_neg, smul_neg, ← this]; abel
      refine ⟨t • y + N ^ j • t • w, Λ.add_mem (Λ.nsmul_mem hy _) (Λ.nsmul_mem (Λ.nsmul_mem hw _) _),
        -w', Λ.neg_mem hw', ?_⟩
      rw [pow_succ', mul_smul, e, smul_add, smul_comm t (N ^ j), e2, smul_add, pow_succ, mul_smul, add_assoc]
  obtain ⟨j, u, hu, q, hq⟩ := exists_dvd_coprime_mul_pow N m hm
  refine ⟨u * t ^ j, Nat.Coprime.mul_left hu (Nat.Coprime.pow_left _ ht), fun z hz => ?_⟩
  obtain ⟨y, hy, w, hw, e⟩ := key j z hz
  rw [mul_smul, e, smul_add, ← mul_smul, hq, mul_comm, mul_smul]
  exact Λ.add_mem (Λ.nsmul_mem hy _) (Λ.nsmul_mem (h2 w hw) _)

/- English proof (translation)
Establish `hI0 : I ∈ (Ideal (𝓞 E))⁰` using `mem_nonZeroDivisors_of_ne_zero hI`. Use `set h := Fintype.card (ClassGroup (𝓞 E)) with hh`. Establish `hpos : h ≠ 0` using `Fintype.card_ne_zero`. Establish `h1 : ClassGroup.mk0 ((⟨I, hI0⟩ : (Ideal (𝓞 E))⁰) ^ h) = 1`. Rewrite using `[map_pow, pow_card_eq_one]`.

Establish `h2 : (I ^ h).IsPrincipal` using `(ClassGroup.mk0_eq_one_iff (pow_mem hI0 h)).1 h1`. Take `⟨s, hs⟩` from `h2`. Establish `hs' : I ^ h = Ideal.span {s}` using `hs`. Use `⟨s, Ideal.pow_le_self hpos (hs' ▸ Ideal.mem_span_singleton_self s), ?_, fun P hP hsP => ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`.

Conclude with `pow_ne_zero h hI (by rw [hs']; simp)`. Conclude with `(Ideal.IsPrime.pow_le_iff hpos).1 (by rw [hs']; exact (Ideal.span_singleton_le_iff_mem _).2 hsP)`.
-/
theorem exists_mem_primes {E : Type} [Field E] [NumberField E] (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) :
    ∃ s ∈ I, s ≠ 0 ∧ ∀ P : Ideal (𝓞 E), P.IsPrime → s ∈ P → I ≤ P := by
  classical
  have hI0 : I ∈ (Ideal (𝓞 E))⁰ := mem_nonZeroDivisors_of_ne_zero hI
  set h := Fintype.card (ClassGroup (𝓞 E)) with hh
  have hpos : h ≠ 0 := Fintype.card_ne_zero
  have h1 : ClassGroup.mk0 ((⟨I, hI0⟩ : (Ideal (𝓞 E))⁰) ^ h) = 1 := by
    rw [map_pow, pow_card_eq_one]
  have h2 : (I ^ h).IsPrincipal := (ClassGroup.mk0_eq_one_iff (pow_mem hI0 h)).1 h1
  obtain ⟨s, hs⟩ := h2
  have hs' : I ^ h = Ideal.span {s} := hs
  refine ⟨s, Ideal.pow_le_self hpos (hs' ▸ Ideal.mem_span_singleton_self s), ?_, fun P hP hsP => ?_⟩
  · rintro rfl
    exact pow_ne_zero h hI (by rw [hs']; simp)
  · exact (Ideal.IsPrime.pow_le_iff hpos).1 (by rw [hs']; exact (Ideal.span_singleton_le_iff_mem _).2 hsP)

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

/- English proof (translation)
The claim follows from `Matrix.map_mul (f := (Algebra.TensorProduct.includeRight : E →ₐ[F] FiniteAdeleRing (𝓞 F) F ⊗[F] E).toRingHom)`.
-/
theorem fm_mul (A B : Matrix (Fin n) (Fin n) E) : fm F (A * B) = fm F A * fm F B :=
  Matrix.map_mul (f := (Algebra.TensorProduct.includeRight :
    E →ₐ[F] FiniteAdeleRing (𝓞 F) F ⊗[F] E).toRingHom)

/- English proof (translation)
The claim follows from `Matrix.map_one _ (by simp) rfl`.
-/
theorem fm_one : fm F (1 : Matrix (Fin n) (Fin n) E) = 1 :=
  Matrix.map_one _ (by simp) rfl

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[fm, Matrix.mulVec, dotProduct, TensorProduct.tmul_sum]`.
-/
theorem fm_mulVec_pure (M : Matrix (Fin n) (Fin n) E) (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    fm F M *ᵥ (fun i => a ⊗ₜ[F] x i) = fun i => a ⊗ₜ[F] (M *ᵥ x) i := by
  funext i
  simp [fm, Matrix.mulVec, dotProduct, TensorProduct.tmul_sum]

/- English proof (translation)
Take `⟨t, ht, h⟩` from `h`. Use `⟨t, ht, fun z hz => ?_⟩` and prove the remaining obligations. Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, x, hx, rfl⟩` from `hz`.

Take `⟨w, hw, e⟩` from `h x hx`. Use `⟨fun i => a ⊗ₜ[F] w i, AddSubgroup.subset_closure ⟨a, ha, w, hw, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[fm_mulVec_pure]`. Use function extensionality and compare the values at `i`. Use `congrArg (fun y : Fin n → E => (TensorProduct.mk F (FiniteAdeleRing (𝓞 F) F) E a) (y i)) e` as an intermediate fact.

Simplify `this` using `only [Pi.smul_apply, Pi.sub_apply, map_nsmul, map_sub, TensorProduct.mk_apply]`. Consider the case `zero => exact ⟨0, AddSubgroup.zero_mem _, by simp⟩`. Consider the case `add x y _ _ ihx ihy`. Take `⟨w, hw, e⟩` from `ihx`. Take `⟨w', hw', e'⟩` from `ihy`.

Use `⟨w + w', AddSubgroup.add_mem _ hw hw', ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add, ← e, ← e', Matrix.mulVec_add, ← smul_add]`. Use `congr 1`. Normalize the expressions using the abelian group laws. Consider the case `neg x _ ih`.

Take `⟨w, hw, e⟩` from `ih`. Use `⟨-w, AddSubgroup.neg_mem _ hw, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_neg, ← e, Matrix.mulVec_neg, ← smul_neg]`. Use `congr 1`. Normalize the expressions using the abelian group laws.
-/
theorem congAtA_of_congAt (L : Submodule (𝓞 E) (Fin n → E)) (N D : ℕ) (δ : Matrix (Fin n) (Fin n) E)
    (h : CongAt L N D δ) : CongAtA F L N D (fm F δ) := by
  obtain ⟨t, ht, h⟩ := h
  refine ⟨t, ht, fun z hz => ?_⟩
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    obtain ⟨w, hw, e⟩ := h x hx
    refine ⟨fun i => a ⊗ₜ[F] w i, AddSubgroup.subset_closure ⟨a, ha, w, hw, rfl⟩, ?_⟩
    rw [fm_mulVec_pure]
    funext i
    have := congrArg (fun y : Fin n → E =>
      (TensorProduct.mk F (FiniteAdeleRing (𝓞 F) F) E a) (y i)) e
    simpa only [Pi.smul_apply, Pi.sub_apply, map_nsmul, map_sub, TensorProduct.mk_apply] using this
  | zero => exact ⟨0, AddSubgroup.zero_mem _, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨w, hw, e⟩ := ihx
    obtain ⟨w', hw', e'⟩ := ihy
    refine ⟨w + w', AddSubgroup.add_mem _ hw hw', ?_⟩
    rw [smul_add, ← e, ← e', Matrix.mulVec_add, ← smul_add]; congr 1; abel
  | neg x _ ih =>
    obtain ⟨w, hw, e⟩ := ih
    refine ⟨-w, AddSubgroup.neg_mem _ hw, ?_⟩
    rw [smul_neg, ← e, Matrix.mulVec_neg, ← smul_neg]; congr 1; abel

/- English proof (translation)
Introduce `z hz`. Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, x, hx, rfl⟩` from `hz`. Use `AddSubgroup.subset_closure ⟨a, ha, _, h x hx, ?_⟩` and prove the remaining obligations.

Rewrite using `[fm_mulVec_pure]`. Use function extensionality and compare the values at `i`. Simplify using `[Algebra.smul_def]`. Consider the case `zero => simp`. Consider the case `add x y _ _ ihx ihy => rw [Matrix.mulVec_add, smul_add]`.

Conclude with `AddSubgroup.add_mem _ ihx ihy`. Consider the case `neg x _ ih => rw [Matrix.mulVec_neg, smul_neg]`. Conclude with `AddSubgroup.neg_mem _ ih`.
-/
theorem smul_fm_mem (L : Submodule (𝓞 E) (Fin n → E)) (s : 𝓞 E) (M : Matrix (Fin n) (Fin n) E)
    (h : ∀ v ∈ L, s • (M *ᵥ v) ∈ L) : ∀ z ∈ hat F (L : Set (Fin n → E)),
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (s : E)) • (fm F M *ᵥ z) ∈ hat F (L : Set (Fin n → E)) := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, _, h x hx, ?_⟩
    rw [fm_mulVec_pure]
    funext i
    simp [Algebra.smul_def]
  | zero => simp
  | add x y _ _ ihx ihy => rw [Matrix.mulVec_add, smul_add]; exact AddSubgroup.add_mem _ ihx ihy
  | neg x _ ih => rw [Matrix.mulVec_neg, smul_neg]; exact AddSubgroup.neg_mem _ ih

/- English proof (translation)
Introduce `z hz`. Use `smul_fm_mem (F := F) L s 1 (fun v hv => by simpa using L.smul_mem s hv) z hz` as an intermediate fact. Rewrite `this` using `[fm_one, Matrix.one_mulVec]`. Then use the resulting hypothesis.
-/
theorem smul_mem_hat (L : Submodule (𝓞 E) (Fin n → E)) (s : 𝓞 E) :
    ∀ z ∈ hat F (L : Set (Fin n → E)),
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (s : E)) • z ∈ hat F (L : Set (Fin n → E)) := by
  intro z hz
  have := smul_fm_mem (F := F) L s 1 (fun v hv => by simpa using L.smul_mem s hv) z hz
  rwa [fm_one, Matrix.one_mulVec] at this

/- English proof (translation)
Take `⟨t, ht, ha⟩` from `ha`. Take `⟨u, hu, hb⟩` from `hb`. Use `⟨t * u, Nat.Coprime.mul_left ht hu, fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨w, hw, e⟩` from `hb z hz`. Take `⟨w', hw', e'⟩` from `ha (u • z + D • w) (AddSubgroup.add_mem _ (AddSubgroup.nsmul_mem _ hz _) (AddSubgroup.nsmul_mem _ hw _))`.

Use `⟨w' + t • w, AddSubgroup.add_mem _ hw' (AddSubgroup.nsmul_mem _ hw _), ?_⟩` and prove the remaining obligations. Establish `e1 : u • z + D • w = u • (b *ᵥ z)` using `by rw [← e, smul_sub]; abel`. Rewrite `e'` using `[e1, Matrix.mulVec_smul, Matrix.mulVec_mulVec]`. Rewrite using `[smul_add, ← e', smul_comm D t, ← e, ← smul_add, mul_smul]`. Use `congr 1`.

Rewrite using `[smul_sub, smul_sub]`. Normalize the expressions using the abelian group laws.
-/
theorem congAtA_mul (L : Submodule (𝓞 E) (Fin n → E)) (N D : ℕ) (a b : Matrix (Fin n) (Fin n) (RA F E))
    (ha : CongAtA F L N D a) (hb : CongAtA F L N D b) : CongAtA F L N D (a * b) := by
  obtain ⟨t, ht, ha⟩ := ha
  obtain ⟨u, hu, hb⟩ := hb
  refine ⟨t * u, Nat.Coprime.mul_left ht hu, fun z hz => ?_⟩
  obtain ⟨w, hw, e⟩ := hb z hz
  obtain ⟨w', hw', e'⟩ := ha (u • z + D • w)
    (AddSubgroup.add_mem _ (AddSubgroup.nsmul_mem _ hz _) (AddSubgroup.nsmul_mem _ hw _))
  refine ⟨w' + t • w, AddSubgroup.add_mem _ hw' (AddSubgroup.nsmul_mem _ hw _), ?_⟩
  have e1 : u • z + D • w = u • (b *ᵥ z) := by rw [← e, smul_sub]; abel
  rw [e1, Matrix.mulVec_smul, Matrix.mulVec_mulVec] at e'
  rw [smul_add, ← e', smul_comm D t, ← e, ← smul_add, mul_smul]
  congr 1
  rw [smul_sub, smul_sub]; abel

def denIdeal (L : Submodule (𝓞 E) (Fin n → E)) (M : Matrix (Fin n) (Fin n) (RA F E)) : Ideal (𝓞 E) where
  carrier := {s | ∀ z ∈ hat F (L : Set (Fin n → E)),
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (s : E)) • (M *ᵥ z) ∈ hat F (L : Set (Fin n → E))}
  add_mem' := by
    intro a b ha hb z hz
    have := AddSubgroup.add_mem _ (ha z hz) (hb z hz)
    rw [← add_smul, ← TensorProduct.tmul_add] at this
    exact this
  zero_mem' := by intro z hz; simp
  smul_mem' := by
    intro a b hb z hz
    have := smul_mem_hat L a _ (hb z hz)
    rw [← mul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul] at this
    exact this

/- English proof (translation)
Establish `: ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (((m : 𝓞 E)) : E)) = (m : RA F E)`. Establish `h : (((m : 𝓞 E)) : E) = (m : E)` using `by simp`. Rewrite using `[h]`. Conclude with `map_natCast (Algebra.TensorProduct.includeRight : E →ₐ[F] FiniteAdeleRing (𝓞 F) F ⊗[F] E) m`. Rewrite using `[this, Nat.cast_smul_eq_nsmul]`.
-/
theorem one_tmul_natCast_smul (m : ℕ) (z : Fin n → RA F E) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (((m : 𝓞 E)) : E)) • z = m • z := by
  have : ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (((m : 𝓞 E)) : E)) = (m : RA F E) := by
    have h : (((m : 𝓞 E)) : E) = (m : E) := by simp
    rw [h]
    exact map_natCast (Algebra.TensorProduct.includeRight :
      E →ₐ[F] FiniteAdeleRing (𝓞 F) F ⊗[F] E) m
  rw [this, Nat.cast_smul_eq_nsmul]

/- English proof (translation)
Rewrite using `[← one_tmul_natCast_smul, ← mul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Both sides reduce to the same expression.
-/
theorem one_tmul_natCast_mul_smul (m : ℕ) (s : 𝓞 E) (z : Fin n → RA F E) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] ((((m : 𝓞 E) * s : 𝓞 E)) : E)) • z =
      m • ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (s : E)) • z := by
  rw [← one_tmul_natCast_smul, ← mul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl

/- English proof (translation)
Introduce `F E _ _ _ _ _ c n G hG h2 L hL hL' g N hg hN`. Take `⟨-, hden, -⟩` from `GlobalTheory.T.idempotent_adeles_and_small_adelic_matrices F E n L hL hL'`. Take `⟨d₁, hd₁, H₁⟩` from `hden g.1`. Take `⟨d₂, hd₂, H₂⟩` from `hden (g⁻¹).1`. Establish `hN' : 0 < N * (d₁ * d₂)` using `by positivity`.

Take `⟨γ₀, hγ₀, hc₀⟩` from `GlobalTheory.T.unitaryGroup_weak_approximation_at_primes F E c n G hG h2 L hL hL' g _ _ hg hN' hN'`. Take `⟨γ, hγ, hc₁, s₁, hs₁, hs⟩` from `GlobalTheory.T.exists_unitary_correction_congruent_one_at_level F E c n G hG L hL hL' γ₀ _ _ hγ₀ hN' hN'`. Establish `hc` using `congAtA_mul L _ _ _ _ (congAtA_of_congAt (F := F) L _ _ _ hc₁) hc₀`. Establish `hγγ : fm F (γ * γ₀⁻¹).1 * (fm F γ₀.1 * g.1) = fm F γ.1 * g.1`. Rewrite using `[← mul_assoc, ← fm_mul, ← Units.val_mul, inv_mul_cancel_right]`.

Rewrite `hc` using `[hγγ]`. Take `⟨t, ht, hc⟩` from `hc`. Use `set k := fm F γ.1 * g.1 with hk`. Use `set k' := (g⁻¹).1 * fm F (γ⁻¹).1 with hk'`. Establish `hkk : k' * k = 1`.

Rewrite using `[hk, hk', mul_assoc, ← mul_assoc (fm F _), ← fm_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, fm_one, one_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]`. Take `⟨m, hm, Hm⟩` from `hden k'`. Take `⟨t', ht', H'⟩` from `inv_integral (hat F (L : Set (Fin n → E))) (Matrix.mulVecLin k).toAddMonoidHom (Matrix.mulVecLin k').toAddMonoidHom (fun z => by`. Express the relevant statement in the definitionally equal form `k' *ᵥ (k *ᵥ z) = z`. Rewrite using `[Matrix.mulVec_mulVec, hkk, Matrix.one_mulVec]) _ t m ht hm hc Hm`.

Use `⟨γ, hγ, ⟨t, Nat.Coprime.coprime_mul_right_right ht, fun z hz => ?_⟩, ?_⟩` and prove the remaining obligations. Take `⟨w, hw, e⟩` from `hc z hz`. Conclude with `⟨(d₁ * d₂) • w, AddSubgroup.nsmul_mem _ hw _, by rw [e, mul_smul]⟩`. Establish `a1 : ((t * t' : ℕ) : 𝓞 E) ∈ denIdeal L k ⊓ denIdeal L k'`. Prove the components needed by the constructor for the conclusion.

Introduce `z hz`. Take `⟨w, hw, e⟩` from `hc z hz`. Rewrite using `[one_tmul_natCast_smul, mul_comm, mul_smul]`. Use `AddSubgroup.nsmul_mem _ ?_ _` and prove the remaining obligations. Establish `: t • (k *ᵥ z) = t • z + (N * (d₁ * d₂)) • w` using `by rw [← e, smul_sub]; abel`.

Rewrite using `[this]`. Conclude with `AddSubgroup.add_mem _ (AddSubgroup.nsmul_mem _ hz _) (AddSubgroup.nsmul_mem _ hw _)`. Introduce `z hz`. Rewrite using `[one_tmul_natCast_smul, mul_smul]`. Conclude with `AddSubgroup.nsmul_mem _ (H' z hz) _`.

Establish `a2 : ((d₁ * d₂ : ℕ) : 𝓞 E) * s₁ ∈ denIdeal L k ⊓ denIdeal L k'`. Prove the components needed by the constructor for the conclusion. Introduce `z hz`. Use `smul_fm_mem (F := F) L s₁ γ.1 (fun v hv => (hs v hv).1) _ (H₁ z hz)` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_smul, Matrix.mulVec_mulVec, smul_comm]`.

Rewrite using `[one_tmul_natCast_mul_smul, mul_comm, mul_smul]`. Conclude with `AddSubgroup.nsmul_mem _ this _`. Introduce `z hz`. Use `H₂ _ (smul_fm_mem (F := F) L s₁ (γ⁻¹).1 (fun v hv => (hs v hv).2) _ hz)` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_smul, Matrix.mulVec_mulVec]`.

Rewrite using `[one_tmul_natCast_mul_smul, mul_smul]`. Conclude with `AddSubgroup.nsmul_mem _ this _`. Establish `hne : denIdeal L k ⊓ denIdeal L k' ≠ ⊥`. Introduce `h`. Rewrite `a2` using `[h, Ideal.mem_bot]`.

Conclude with `mul_ne_zero (Nat.cast_ne_zero.2 (by positivity)) hs₁.1 a2`. Take `⟨s, hsI, hs0, hsP⟩` from `exists_mem_primes _ hne`. Use `⟨s, ⟨hs0, fun P hP h => ?_⟩, fun z hz => ⟨hsI.1 z hz, hsI.2 z hz⟩⟩` and prove the remaining obligations. Establish `b1` using `hsP P hP h a1`. Establish `b2` using `hsP P hP h a2`.

Establish `hcop : IsCoprime ((t * t' : ℕ) : 𝓞 E) ((N * (d₁ * d₂) : ℕ) : 𝓞 E)` using `Nat.Coprime.cast (Nat.Coprime.mul_left ht ht')`. Establish `hnot : ((N * (d₁ * d₂) : ℕ) : 𝓞 E) ∉ P`. Introduce `hh`. Take `⟨x, y, e⟩` from `hcop`. Conclude with `hP.ne_top ((Ideal.eq_top_iff_one P).2 (e ▸ P.add_mem (P.mul_mem_left x b1) (P.mul_mem_left y hh)))`.

Use `⟨?_, fun hh => hnot (by rw [Nat.cast_mul]; exact P.mul_mem_right _ hh)⟩` and prove the remaining obligations. Break down `hP.mem_or_mem b2 with h1 | h1` into its components or cases. Conclude with `(hnot (by rw [Nat.cast_mul]; exact P.mul_mem_left _ h1)).elim`. Conclude with `(hs₁.2 P hP h1).resolve_right hnot`.
-/
theorem exists_rep_split_denominator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → Module.finrank F E = 2 → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (g : GL (Fin n) (RA F E)) (N : ℕ), IsUnA c G g.1 → 0 < N → ∃ γ : GL (Fin n) E, IsUnE c G γ.1 ∧ CongAtA F L N N (fm F γ.1 * g.1) ∧ ∃ s : 𝓞 E, SplitOff c N s ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (s : E)) • ((fm F γ.1 * g.1) *ᵥ z) ∈ hat F (L : Set (Fin n → E)) ∧ ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (s : E)) • (((g⁻¹).1 * fm F (γ⁻¹).1) *ᵥ z) ∈ hat F (L : Set (Fin n → E)) := by
  intro F E _ _ _ _ _ c n G hG h2 L hL hL' g N hg hN
  obtain ⟨-, hden, -⟩ := GlobalTheory.T.idempotent_adeles_and_small_adelic_matrices F E n L hL hL'
  obtain ⟨d₁, hd₁, H₁⟩ := hden g.1
  obtain ⟨d₂, hd₂, H₂⟩ := hden (g⁻¹).1
  have hN' : 0 < N * (d₁ * d₂) := by positivity
  obtain ⟨γ₀, hγ₀, hc₀⟩ := GlobalTheory.T.unitaryGroup_weak_approximation_at_primes F E c n G hG h2 L hL hL' g _ _ hg hN' hN'
  obtain ⟨γ, hγ, hc₁, s₁, hs₁, hs⟩ := GlobalTheory.T.exists_unitary_correction_congruent_one_at_level F E c n G hG L hL hL' γ₀ _ _ hγ₀ hN' hN'
  have hc := congAtA_mul L _ _ _ _ (congAtA_of_congAt (F := F) L _ _ _ hc₁) hc₀
  have hγγ : fm F (γ * γ₀⁻¹).1 * (fm F γ₀.1 * g.1) = fm F γ.1 * g.1 := by
    rw [← mul_assoc, ← fm_mul, ← Units.val_mul, inv_mul_cancel_right]
  rw [hγγ] at hc
  obtain ⟨t, ht, hc⟩ := hc
  set k := fm F γ.1 * g.1 with hk
  set k' := (g⁻¹).1 * fm F (γ⁻¹).1 with hk'
  have hkk : k' * k = 1 := by
    rw [hk, hk', mul_assoc, ← mul_assoc (fm F _), ← fm_mul, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, fm_one, one_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  obtain ⟨m, hm, Hm⟩ := hden k'
  obtain ⟨t', ht', H'⟩ := inv_integral (hat F (L : Set (Fin n → E))) (Matrix.mulVecLin k).toAddMonoidHom
    (Matrix.mulVecLin k').toAddMonoidHom
    (fun z => by
      change k' *ᵥ (k *ᵥ z) = z
      rw [Matrix.mulVec_mulVec, hkk, Matrix.one_mulVec]) _ t m ht hm hc Hm
  refine ⟨γ, hγ, ⟨t, Nat.Coprime.coprime_mul_right_right ht, fun z hz => ?_⟩, ?_⟩
  · obtain ⟨w, hw, e⟩ := hc z hz
    exact ⟨(d₁ * d₂) • w, AddSubgroup.nsmul_mem _ hw _, by rw [e, mul_smul]⟩
  have a1 : ((t * t' : ℕ) : 𝓞 E) ∈ denIdeal L k ⊓ denIdeal L k' := by
    constructor
    · intro z hz
      obtain ⟨w, hw, e⟩ := hc z hz
      rw [one_tmul_natCast_smul, mul_comm, mul_smul]
      refine AddSubgroup.nsmul_mem _ ?_ _
      have : t • (k *ᵥ z) = t • z + (N * (d₁ * d₂)) • w := by rw [← e, smul_sub]; abel
      rw [this]
      exact AddSubgroup.add_mem _ (AddSubgroup.nsmul_mem _ hz _) (AddSubgroup.nsmul_mem _ hw _)
    · intro z hz
      rw [one_tmul_natCast_smul, mul_smul]
      exact AddSubgroup.nsmul_mem _ (H' z hz) _
  have a2 : ((d₁ * d₂ : ℕ) : 𝓞 E) * s₁ ∈ denIdeal L k ⊓ denIdeal L k' := by
    constructor
    · intro z hz
      have := smul_fm_mem (F := F) L s₁ γ.1 (fun v hv => (hs v hv).1) _ (H₁ z hz)
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, smul_comm] at this
      rw [one_tmul_natCast_mul_smul, mul_comm, mul_smul]
      exact AddSubgroup.nsmul_mem _ this _
    · intro z hz
      have := H₂ _ (smul_fm_mem (F := F) L s₁ (γ⁻¹).1 (fun v hv => (hs v hv).2) _ hz)
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec] at this
      rw [one_tmul_natCast_mul_smul, mul_smul]
      exact AddSubgroup.nsmul_mem _ this _
  have hne : denIdeal L k ⊓ denIdeal L k' ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at a2
    exact mul_ne_zero (Nat.cast_ne_zero.2 (by positivity)) hs₁.1 a2
  obtain ⟨s, hsI, hs0, hsP⟩ := exists_mem_primes _ hne
  refine ⟨s, ⟨hs0, fun P hP h => ?_⟩, fun z hz => ⟨hsI.1 z hz, hsI.2 z hz⟩⟩
  have b1 := hsP P hP h a1
  have b2 := hsP P hP h a2
  have hcop : IsCoprime ((t * t' : ℕ) : 𝓞 E) ((N * (d₁ * d₂) : ℕ) : 𝓞 E) :=
    Nat.Coprime.cast (Nat.Coprime.mul_left ht ht')
  have hnot : ((N * (d₁ * d₂) : ℕ) : 𝓞 E) ∉ P := by
    intro hh
    obtain ⟨x, y, e⟩ := hcop
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 (e ▸ P.add_mem (P.mul_mem_left x b1) (P.mul_mem_left y hh)))
  refine ⟨?_, fun hh => hnot (by rw [Nat.cast_mul]; exact P.mul_mem_right _ hh)⟩
  rcases hP.mem_or_mem b2 with h1 | h1
  · exact (hnot (by rw [Nat.cast_mul]; exact P.mul_mem_left _ h1)).elim
  · exact (hs₁.2 P hP h1).resolve_right hnot

end GlobalTheory.UnRep.LatForm
