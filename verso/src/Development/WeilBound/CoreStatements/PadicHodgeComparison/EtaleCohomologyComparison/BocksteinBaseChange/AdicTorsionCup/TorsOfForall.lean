import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.PowNsmulEqZero

noncomputable section

open TensorProduct

namespace CrystallineSemistableComparison.Adic

variable {l : ℕ} [Fact l.Prime]

section Mod
variable {M : Type*} [AddCommGroup M] [Module ℤ_[l] M]

/- English proof (translation)
Rewrite using `[← Nat.cast_pow, Nat.cast_smul_eq_nsmul]`.
-/
theorem lsmul_eq {N : Type*} [AddCommGroup N] [Module ℤ_[l] N] (n : ℕ) (y : N) :
    (l : ℤ_[l]) ^ n • y = l ^ n • y := by
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]

/- English proof (translation)
Take `⟨u, v, hu⟩ : ∃ (u : ℤ_[l]ˣ) (v : ℕ), c = u * (l : ℤ_[l]) ^ v` from `⟨_, _, PadicInt.unitCoeff_spec hc⟩`. Substitute `hu` using the available equality. Use `⟨v, ?_⟩` and prove the remaining obligations. Establish `h2 : ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * (u * (l : ℤ_[l]) ^ v) = (l : ℤ_[l]) ^ v`. Rewrite using `[← mul_assoc, Units.inv_mul, one_mul]`.

Rewrite using `[← h2, mul_smul, h, smul_zero]`.
-/
theorem pow_of_smul {N : Type*} [AddCommGroup N] [Module ℤ_[l] N] {c : ℤ_[l]} (hc : c ≠ 0) {y : N}
    (h : c • y = 0) : ∃ n : ℕ, (l : ℤ_[l]) ^ n • y = 0 := by
  obtain ⟨u, v, hu⟩ : ∃ (u : ℤ_[l]ˣ) (v : ℕ), c = u * (l : ℤ_[l]) ^ v := ⟨_, _, PadicInt.unitCoeff_spec hc⟩
  subst hu
  refine ⟨v, ?_⟩
  have h2 : ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * (u * (l : ℤ_[l]) ^ v) = (l : ℤ_[l]) ^ v := by
    rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [← h2, mul_smul, h, smul_zero]

/- English proof (translation)
The claim follows from `Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero`.
-/
theorem l_ne_zero : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero

/- English proof (translation)
Use `set T := Submodule.torsion' ℤ_[l] M (Submonoid.powers (l : ℤ_[l]))`. Establish `hI : (Ideal.span {(l : ℤ_[l])}) ≠ ⊤`. Rewrite using `[Ne, Ideal.span_singleton_eq_top, PadicInt.isUnit_iff, PadicInt.norm_p]`. Establish `: (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Conclude with `(inv_lt_one_of_one_lt₀ this).ne`.

Establish `key` using `Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := M ⧸ T) (Ideal.span {(l : ℤ_[l])}) hI`. Establish `hx : T.mkQ x ∈ (⊥ : Submodule ℤ_[l] (M ⧸ T))`. Rewrite using `[← key, Submodule.mem_iInf]`. Introduce `k`. Take `⟨w, t, ⟨n, hn⟩, rfl⟩` from `h k`.

Establish `ht : T.mkQ t = 0`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_torsion'_iff]`. Conclude with `⟨⟨_, n, rfl⟩, hn⟩`. Rewrite using `[map_add, ht, add_zero, map_smul]`. Use `Submodule.smul_mem_smul ?_ Submodule.mem_top` and prove the remaining obligations.

Rewrite using `[Ideal.span_singleton_pow]`. Conclude with `Ideal.mem_span_singleton_self _`. Rewrite `hx` using `[Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_torsion'_iff]`. Take `⟨⟨a, n, rfl⟩, ha⟩` from `hx`. Conclude with `⟨n, ha⟩`.
-/
theorem tors_of_forall [Module.Finite ℤ_[l] M] (x : M)
    (h : ∀ k : ℕ, ∃ w t : M, (∃ n : ℕ, (l : ℤ_[l]) ^ n • t = 0) ∧ x = (l : ℤ_[l]) ^ k • w + t) :
    ∃ n : ℕ, (l : ℤ_[l]) ^ n • x = 0 := by
  set T := Submodule.torsion' ℤ_[l] M (Submonoid.powers (l : ℤ_[l]))
  have hI : (Ideal.span {(l : ℤ_[l])}) ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top, PadicInt.isUnit_iff, PadicInt.norm_p]
    have : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    exact (inv_lt_one_of_one_lt₀ this).ne
  have key := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := M ⧸ T) (Ideal.span {(l : ℤ_[l])}) hI
  have hx : T.mkQ x ∈ (⊥ : Submodule ℤ_[l] (M ⧸ T)) := by
    rw [← key, Submodule.mem_iInf]
    intro k
    obtain ⟨w, t, ⟨n, hn⟩, rfl⟩ := h k
    have ht : T.mkQ t = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_torsion'_iff]
      exact ⟨⟨_, n, rfl⟩, hn⟩
    rw [map_add, ht, add_zero, map_smul]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _
  rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_torsion'_iff] at hx
  obtain ⟨⟨a, n, rfl⟩, ha⟩ := hx
  exact ⟨n, ha⟩

/- English proof (translation)
Distinguish the cases in `h0 : ∃ n : ℕ, (l : ℤ_[l]) ^ n • g = 0`. Take `⟨N, hN⟩` from `h0`. Use `⟨N, fun t _ => ?_⟩` and prove the remaining obligations. Take `⟨c, rfl⟩` from `hg t`. Rewrite using `[smul_comm, hN, smul_zero]`.

Use `⟨0, fun t ⟨n, hn⟩ => ?_⟩` and prove the remaining obligations. Take `⟨c, rfl⟩` from `hg t`. Rewrite `hn` using `[smul_smul]`. Distinguish the cases in `hc : (l : ℤ_[l]) ^ n * c = 0`. Establish `: c = 0`.

Break down `mul_eq_zero.1 hc with h | h` into its components or cases. Conclude with `absurd h (pow_ne_zero _ l_ne_zero)`. Conclude with `h`. Simplify using `[this]`. Conclude with `absurd (pow_of_smul hc hn) h0`.
-/
theorem cyclic_tors (g : M) (hg : ∀ x : M, ∃ c : ℤ_[l], x = c • g) :
    ∃ N : ℕ, ∀ t : M, (∃ n : ℕ, (l : ℤ_[l]) ^ n • t = 0) → (l : ℤ_[l]) ^ N • t = 0 := by
  by_cases h0 : ∃ n : ℕ, (l : ℤ_[l]) ^ n • g = 0
  · obtain ⟨N, hN⟩ := h0
    refine ⟨N, fun t _ => ?_⟩
    obtain ⟨c, rfl⟩ := hg t
    rw [smul_comm, hN, smul_zero]
  · refine ⟨0, fun t ⟨n, hn⟩ => ?_⟩
    obtain ⟨c, rfl⟩ := hg t
    rw [smul_smul] at hn
    by_cases hc : (l : ℤ_[l]) ^ n * c = 0
    · have : c = 0 := by
        rcases mul_eq_zero.1 hc with h | h
        · exact absurd h (pow_ne_zero _ l_ne_zero)
        · exact h
      simp [this]
    · exact absurd (pow_of_smul hc hn) h0

/- English proof (translation)
The claim follows from `(isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ_[l]) ℚ_[l] _).mpr (TensorProduct.isBaseChange ℤ_[l] M ℚ_[l])`.
-/
theorem isLoc : IsLocalizedModule (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] M 1) :=
  (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ_[l]) ℚ_[l] _).mpr (TensorProduct.isBaseChange ℤ_[l] M ℚ_[l])

/- English proof (translation)
Establish `hL` using `isLoc (l := l) (M := M)`. Take `⟨⟨x, s⟩, hv⟩` from `IsLocalizedModule.mk'_surjective (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] M 1) v`. Use `⟨(algebraMap ℤ_[l] ℚ_[l] s)⁻¹, x, ?_⟩` and prove the remaining obligations. Rewrite using `[← hv]`. Simplify using `only [Function.uncurry_apply_pair]`.

Rewrite using `[IsLocalizedModule.mk'_eq_iff, TensorProduct.mk_apply, Submonoid.smul_def, TensorProduct.smul_tmul', Algebra.smul_def, mul_inv_cancel₀]`. Conclude with `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2`.
-/
theorem tmul_surj (v : ℚ_[l] ⊗[ℤ_[l]] M) : ∃ (c : ℚ_[l]) (x : M), v = c ⊗ₜ x := by
  have hL := isLoc (l := l) (M := M)
  obtain ⟨⟨x, s⟩, hv⟩ := IsLocalizedModule.mk'_surjective (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] M 1) v
  refine ⟨(algebraMap ℤ_[l] ℚ_[l] s)⁻¹, x, ?_⟩
  rw [← hv]
  simp only [Function.uncurry_apply_pair]
  rw [IsLocalizedModule.mk'_eq_iff, TensorProduct.mk_apply, Submonoid.smul_def, TensorProduct.smul_tmul',
    Algebra.smul_def, mul_inv_cancel₀]
  exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2

/- English proof (translation)
Establish `hL` using `isLoc (l := l) (M := M)`. Establish `e` using `IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] M 1) (m := x)`. Rewrite `e` using `[TensorProduct.mk_apply]`. Rewrite using `[e]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨s, hs⟩`. Conclude with `pow_of_smul (nonZeroDivisors.ne_zero s.2) hs`. Introduce and unpack `⟨n, hn⟩`. Conclude with `⟨⟨_, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n l_ne_zero)⟩, hn⟩`.
-/
theorem tmul_eq_zero (x : M) : (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] x = 0 ↔ ∃ n : ℕ, (l : ℤ_[l]) ^ n • x = 0 := by
  have hL := isLoc (l := l) (M := M)
  have e := IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] M 1) (m := x)
  rw [TensorProduct.mk_apply] at e
  rw [e]
  constructor
  · rintro ⟨s, hs⟩
    exact pow_of_smul (nonZeroDivisors.ne_zero s.2) hs
  · rintro ⟨n, hn⟩
    exact ⟨⟨_, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n l_ne_zero)⟩, hn⟩

/- English proof (translation)
The claim follows from `inferInstance`.
-/
theorem fd [Module.Finite ℤ_[l] M] : FiniteDimensional ℚ_[l] (ℚ_[l] ⊗[ℤ_[l]] M) := inferInstance

end Mod

/- English proof (translation)
Use `set W := Submodule.span K F`. Establish `h1 : W.dualCoannihilator = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `v hv`. Rewrite `hv` using `[Submodule.mem_dualCoannihilator]`.

Conclude with `(Submodule.mem_bot K).2 (h v fun f hf => hv f (Submodule.subset_span hf))`. Use `Subspace.dualCoannihilator_dualAnnihilator_eq (W := W)` as an intermediate fact. Rewrite `this` using `[h1, Submodule.dualAnnihilator_bot]`. Conclude with `this.symm`.
-/
theorem span_dual {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (F : Set (Module.Dual K V)) (h : ∀ v, (∀ f ∈ F, f v = 0) → v = 0) : Submodule.span K F = ⊤ := by
  set W := Submodule.span K F
  have h1 : W.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_dualCoannihilator] at hv
    exact (Submodule.mem_bot K).2 (h v fun f hf => hv f (Submodule.subset_span hf))
  have := Subspace.dualCoannihilator_dualAnnihilator_eq (W := W)
  rw [h1, Submodule.dualAnnihilator_bot] at this
  exact this.symm

/- English proof (translation)
Use `hA.finite hSA` as an intermediate fact. Take `⟨g, hgS, hg⟩` from `hcyc`. Take `⟨N, hN⟩` from `cyclic_tors (M := SC) ⟨g, hgS⟩ (fun z => by`. Take `⟨c, hc⟩` from `hg z z.2`. Conclude with `⟨c, Subtype.ext (by simpa using hc)⟩)`.

Establish `hN' : ∀ z ∈ SC, (∃ n : ℕ, (l : ℤ_[l]) ^ n • z = 0) → (l : ℤ_[l]) ^ N • z = 0`. Introduce and unpack `z hz ⟨n, hn⟩`. Use `hN ⟨z, hz⟩ ⟨n, Subtype.ext (by simpa using hn)⟩` as an intermediate fact. Simplify using `using congrArg Subtype.val this`. Establish `hP : ∀ y ∈ SB, (fun k => μ k (x k) (y k)) ∈ SC`.

Introduce `y hy`. Rewrite using `[hSC]`. Introduce `k`. Use `show ρC (k + 1) k (μ (k + 1) (x (k + 1)) (y (k + 1))) = μ k (x k) (y k)`. Rewrite using `[hμ _ _ _ _ (Nat.le_succ k), (hSA x).1 hx k, (hSB y).1 hy k]`.

Use `set x' := (l : ℤ_[l]) ^ N • x with hx'def`. Establish `hx' : x' ∈ SA` using `SA.smul_mem _ hx`. Establish `hvan : ∀ y ∈ SB, ∀ k, μ k (x' k) (y k) = 0`. Introduce `y hy k`. Establish `h2` using `congrFun (hN' _ (hP y hy) (h y hy)) k`.

Simplify using `only [Pi.smul_apply, Pi.zero_apply] at h2`. Rewrite using `[hx'def, Pi.smul_apply, lsmul_eq, map_nsmul, AddMonoidHom.nsmul_apply, ← lsmul_eq]`. Conclude with `h2`. Establish `key : ∀ k : ℕ, ∃ w t : SA, (∃ n : ℕ, (l : ℤ_[l]) ^ n • t = 0) ∧ (⟨x', hx'⟩ : SA) = (l : ℤ_[l]) ^ k • w + t`. Introduce `k`.

Take `⟨a, ha⟩` from `hB.ml hSB k`. Establish `hz : l ^ a • x' (k + a) = 0`. Apply `hnd` to reduce the goal to its premises. Introduce `b`. Take `⟨y, hy, hyk⟩` from `ha b`.

Establish `hb0 : ρC (k + a) k (μ (k + a) (x' (k + a)) b) = 0`. Rewrite using `[hμ _ _ _ _ (Nat.le_add_right k a), hA.compat hSA hx' (Nat.le_add_right k a), ← hyk]`. Conclude with `hvan y hy k`. Establish `hbk : ∀ m (z : C m), m = a + k → ρC m k z = 0 → l ^ a • z = 0`. Introduce `m z hm hz0`.

Substitute `hm` using the available equality. Conclude with `(hC.bock a k z hz0).1`. Rewrite using `[map_nsmul, AddMonoidHom.nsmul_apply]`. Conclude with `hbk _ _ (Nat.add_comm k a) hb0`. Establish `hw : (l : ℤ_[l]) ^ a • x' ∈ SA` using `SA.smul_mem _ hx'`.

Take `⟨v, hv, hve⟩` from `hA.ker hSA hw (k + a) (by rw [Pi.smul_apply, lsmul_eq]; exact hz)`. Use `⟨⟨v, hv⟩, ⟨x' - (l : ℤ_[l]) ^ k • v, SA.sub_mem hx' (SA.smul_mem _ hv)⟩, ⟨a, ?_⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext show (l : ℤ_[l]) ^ a • (x' - (l : ℤ_[l]) ^ k • v) = 0` to reduce the goal to its premises. Rewrite using `[smul_sub, hve, smul_smul, ← pow_add, add_comm a k, sub_self]`. Apply `Subtype.ext show x' = (l : ℤ_[l]) ^ k • v + (x' - (l : ℤ_[l]) ^ k • v)` to reduce the goal to its premises.

Normalize the expressions using the abelian group laws. Take `⟨n, hn⟩` from `tors_of_forall (M := SA) ⟨x', hx'⟩ key`. Establish `hn' : (l : ℤ_[l]) ^ n • x' = 0` using `by simpa using congrArg Subtype.val hn`. Conclude with `⟨n + N, by rw [pow_add, mul_smul]; exact hn'⟩`.
-/
theorem pair_tors {A B C : ℕ → Type*} [∀ k, AddCommGroup (A k)] [∀ k, Module ℤ_[l] (A k)]
    [∀ k, AddCommGroup (B k)] [∀ k, Module ℤ_[l] (B k)] [∀ k, AddCommGroup (C k)] [∀ k, Module ℤ_[l] (C k)]
    {ρA : ∀ m n, A m →+ A n} {ρB : ∀ m n, B m →+ B n} {ρC : ∀ m n, C m →+ C n}
    {SA : Submodule ℤ_[l] (∀ k, A k)} {SB : Submodule ℤ_[l] (∀ k, B k)} {SC : Submodule ℤ_[l] (∀ k, C k)}
    (hA : IsSys l A ρA) (hB : IsSys l B ρB) (hC : IsSys l C ρC)
    (hSA : ∀ x, x ∈ SA ↔ ∀ k, ρA (k + 1) k (x (k + 1)) = x k)
    (hSB : ∀ x, x ∈ SB ↔ ∀ k, ρB (k + 1) k (x (k + 1)) = x k)
    (hSC : ∀ x, x ∈ SC ↔ ∀ k, ρC (k + 1) k (x (k + 1)) = x k)
    (μ : ∀ k, A k →+ B k →+ C k)
    (hμ : ∀ m n (a : A m) (b : B m), n ≤ m → ρC m n (μ m a b) = μ n (ρA m n a) (ρB m n b))
    (hnd : ∀ k (a : A k), (∀ b, μ k a b = 0) → a = 0)
    (hcyc : ∃ g ∈ SC, ∀ z ∈ SC, ∃ c : ℤ_[l], z = c • g)
    {x : ∀ k, A k} (hx : x ∈ SA)
    (h : ∀ y ∈ SB, ∃ n : ℕ, (l : ℤ_[l]) ^ n • (fun k => μ k (x k) (y k)) = 0) :
    ∃ n : ℕ, (l : ℤ_[l]) ^ n • x = 0 := by
  classical
  have := hA.finite hSA
  obtain ⟨g, hgS, hg⟩ := hcyc
  obtain ⟨N, hN⟩ := cyclic_tors (M := SC) ⟨g, hgS⟩ (fun z => by
    obtain ⟨c, hc⟩ := hg z z.2
    exact ⟨c, Subtype.ext (by simpa using hc)⟩)
  have hN' : ∀ z ∈ SC, (∃ n : ℕ, (l : ℤ_[l]) ^ n • z = 0) → (l : ℤ_[l]) ^ N • z = 0 := by
    rintro z hz ⟨n, hn⟩
    have := hN ⟨z, hz⟩ ⟨n, Subtype.ext (by simpa using hn)⟩
    simpa using congrArg Subtype.val this
  have hP : ∀ y ∈ SB, (fun k => μ k (x k) (y k)) ∈ SC := by
    intro y hy
    rw [hSC]
    intro k
    show ρC (k + 1) k (μ (k + 1) (x (k + 1)) (y (k + 1))) = μ k (x k) (y k)
    rw [hμ _ _ _ _ (Nat.le_succ k), (hSA x).1 hx k, (hSB y).1 hy k]
  set x' := (l : ℤ_[l]) ^ N • x with hx'def
  have hx' : x' ∈ SA := SA.smul_mem _ hx
  have hvan : ∀ y ∈ SB, ∀ k, μ k (x' k) (y k) = 0 := by
    intro y hy k
    have h2 := congrFun (hN' _ (hP y hy) (h y hy)) k
    simp only [Pi.smul_apply, Pi.zero_apply] at h2
    rw [hx'def, Pi.smul_apply, lsmul_eq, map_nsmul, AddMonoidHom.nsmul_apply, ← lsmul_eq]
    exact h2
  have key : ∀ k : ℕ, ∃ w t : SA, (∃ n : ℕ, (l : ℤ_[l]) ^ n • t = 0) ∧
      (⟨x', hx'⟩ : SA) = (l : ℤ_[l]) ^ k • w + t := by
    intro k
    obtain ⟨a, ha⟩ := hB.ml hSB k
    have hz : l ^ a • x' (k + a) = 0 := by
      apply hnd
      intro b
      obtain ⟨y, hy, hyk⟩ := ha b
      have hb0 : ρC (k + a) k (μ (k + a) (x' (k + a)) b) = 0 := by
        rw [hμ _ _ _ _ (Nat.le_add_right k a), hA.compat hSA hx' (Nat.le_add_right k a), ← hyk]
        exact hvan y hy k
      have hbk : ∀ m (z : C m), m = a + k → ρC m k z = 0 → l ^ a • z = 0 := by
        intro m z hm hz0
        subst hm
        exact (hC.bock a k z hz0).1
      rw [map_nsmul, AddMonoidHom.nsmul_apply]
      exact hbk _ _ (Nat.add_comm k a) hb0
    have hw : (l : ℤ_[l]) ^ a • x' ∈ SA := SA.smul_mem _ hx'
    obtain ⟨v, hv, hve⟩ := hA.ker hSA hw (k + a) (by rw [Pi.smul_apply, lsmul_eq]; exact hz)
    refine ⟨⟨v, hv⟩, ⟨x' - (l : ℤ_[l]) ^ k • v, SA.sub_mem hx' (SA.smul_mem _ hv)⟩, ⟨a, ?_⟩, ?_⟩
    · apply Subtype.ext
      show (l : ℤ_[l]) ^ a • (x' - (l : ℤ_[l]) ^ k • v) = 0
      rw [smul_sub, hve, smul_smul, ← pow_add, add_comm a k, sub_self]
    · apply Subtype.ext
      show x' = (l : ℤ_[l]) ^ k • v + (x' - (l : ℤ_[l]) ^ k • v)
      abel
  obtain ⟨n, hn⟩ := tors_of_forall (M := SA) ⟨x', hx'⟩ key
  have hn' : (l : ℤ_[l]) ^ n • x' = 0 := by simpa using congrArg Subtype.val hn
  exact ⟨n + N, by rw [pow_add, mul_smul]; exact hn'⟩

end CrystallineSemistableComparison.Adic
