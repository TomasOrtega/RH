import Mathlib

namespace GlobalTheory.Desc

open scoped TensorProduct

/- English proof (translation)
Set `φ` to `IsScalarTower.toAlgHom R C (Localization.Away x)`. Set `u : Localization.Away x` to `IsLocalization.Away.invSelf x`. Establish `hu : φ x * u = 1` using `IsLocalization.Away.mul_invSelf x`. Use `⟨⟨insert u (s.image φ), ?_⟩⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff]`.

Introduce and unpack `y -`. Establish `hU : u ∈ Algebra.adjoin R ((insert u (s.image φ) : Finset _) : Set (Localization.Away x))` using `Algebra.subset_adjoin (by simp)`. Establish `hB : ∀ b ∈ Algebra.adjoin R (s : Set C), φ b ∈ Algebra.adjoin R ((insert u (s.image φ) : Finset _) : Set (Localization.Away x))`. Introduce `b hb`. Establish `: φ b ∈ (Algebra.adjoin R (s : Set C)).map φ` using `⟨b, hb, rfl⟩`.

Rewrite `this` using `[AlgHom.map_adjoin]`. Use `Algebra.adjoin_mono ?_ this` and prove the remaining obligations. Introduce `z hz`. Simplify using `only [Finset.coe_insert, Finset.coe_image]`. Conclude with `Or.inr hz`.

Take `⟨m, c, hc⟩` from `IsLocalization.Away.surj x y`. Take `⟨n, hn⟩` from `h c`. Establish `hc' : y * φ x ^ m = φ c` using `hc`. Establish `: y = φ (x ^ n * c) * u ^ (n + m)`. Rewrite using `[map_mul, map_pow, ← hc']`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[this]`. Conclude with `mul_mem (hB _ hn) (pow_mem hU _)`.
-/
theorem finiteType_away_of_pow_mul_mem {R C : Type} [CommRing R] [CommRing C] [Algebra R C]
    (s : Finset C) (x : C) (h : ∀ c : C, ∃ n : ℕ, x ^ n * c ∈ Algebra.adjoin R (s : Set C)) :
    Algebra.FiniteType R (Localization.Away x) := by
  classical
  let φ := IsScalarTower.toAlgHom R C (Localization.Away x)
  let u : Localization.Away x := IsLocalization.Away.invSelf x
  have hu : φ x * u = 1 := IsLocalization.Away.mul_invSelf x
  refine ⟨⟨insert u (s.image φ), ?_⟩⟩
  rw [eq_top_iff]
  rintro y -
  have hU : u ∈ Algebra.adjoin R ((insert u (s.image φ) : Finset _) : Set (Localization.Away x)) :=
    Algebra.subset_adjoin (by simp)
  have hB : ∀ b ∈ Algebra.adjoin R (s : Set C),
      φ b ∈ Algebra.adjoin R ((insert u (s.image φ) : Finset _) : Set (Localization.Away x)) := by
    intro b hb
    have : φ b ∈ (Algebra.adjoin R (s : Set C)).map φ := ⟨b, hb, rfl⟩
    rw [AlgHom.map_adjoin] at this
    refine Algebra.adjoin_mono ?_ this
    intro z hz
    simp only [Finset.coe_insert, Finset.coe_image]
    exact Or.inr hz
  obtain ⟨m, c, hc⟩ := IsLocalization.Away.surj x y
  obtain ⟨n, hn⟩ := h c
  have hc' : y * φ x ^ m = φ c := hc
  have : y = φ (x ^ n * c) * u ^ (n + m) := by
    rw [map_mul, map_pow, ← hc']
    calc y = y * (φ x * u) ^ (n + m) := by rw [hu]; simp
      _ = _ := by ring
  rw [this]
  exact mul_mem (hB _ hn) (pow_mem hU _)

/- English proof (translation)
Use `set x := algebraMap R C f with hx`. Set `φ` to `algebraMap C (Localization.Away x)`. Take `⟨t, ht⟩` from `h.out`. Use `choose m a ha using fun y : Localization.Away x => IsLocalization.Away.surj x y`. Use `⟨t.image a, fun c => ?_⟩` and prove the remaining obligations.

Use `set B := Algebra.adjoin R ((t.image a : Finset C) : Set C) with hB`. Establish `hxB : x ∈ B` using `B.algebraMap_mem f`. Establish `key : ∀ y ∈ Algebra.adjoin R (t : Set (Localization.Away x)), ∃ n : ℕ, ∃ b ∈ B, y * φ x ^ n = φ b`. Introduce `y hy`. Proceed by induction on `hy using Algebra.adjoin_induction with`.

Consider the case `mem y hy`. Conclude with `⟨m y, a y, Algebra.subset_adjoin (by simpa using ⟨y, hy, rfl⟩), ha y⟩`. Consider the case `algebraMap r`. Conclude with `⟨0, algebraMap R C r, B.algebraMap_mem r, by`. Rewrite using `[pow_zero, mul_one]`.

Conclude with `IsScalarTower.algebraMap_apply R C _ r⟩`. Consider the case `add y z _ _ hy hz`. Take `⟨n, b, hb, e⟩` from `hy`. Take `⟨k, d, hd, e'⟩` from `hz`. Use `⟨n + k, b * x ^ k + d * x ^ n, add_mem (mul_mem hb (pow_mem hxB _)) (mul_mem hd (pow_mem hxB _)), ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add, map_mul, map_mul, map_pow, map_pow, ← e, ← e']`. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul y z _ _ hy hz`. Take `⟨n, b, hb, e⟩` from `hy`. Take `⟨k, d, hd, e'⟩` from `hz`.

Use `⟨n + k, b * d, mul_mem hb hd, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, ← e, ← e']`. Expand and normalize the polynomial expressions, which then agree. Take `⟨n, b, hb, e⟩` from `key (φ c) (by rw [ht]; trivial)`. Rewrite `e` using `[← map_pow, ← map_mul]`.

Take `⟨k, hk⟩` from `IsLocalization.Away.exists_of_eq x e`. Use `⟨k + n, ?_⟩` and prove the remaining obligations. Establish `: x ^ (k + n) * c = x ^ k * b` using `by rw [← hk]; ring`. Rewrite using `[this]`. Conclude with `mul_mem (pow_mem hxB _) hb`.
-/
theorem exists_pow_mul_mem_of_finiteType_away {R C : Type} [CommRing R] [CommRing C] [Algebra R C]
    (f : R) (h : Algebra.FiniteType R (Localization.Away (algebraMap R C f))) :
    ∃ s : Finset C, ∀ c : C, ∃ n : ℕ, algebraMap R C f ^ n * c ∈ Algebra.adjoin R (s : Set C) := by
  classical
  set x := algebraMap R C f with hx
  let φ := algebraMap C (Localization.Away x)
  obtain ⟨t, ht⟩ := h.out
  choose m a ha using fun y : Localization.Away x => IsLocalization.Away.surj x y
  refine ⟨t.image a, fun c => ?_⟩
  set B := Algebra.adjoin R ((t.image a : Finset C) : Set C) with hB
  have hxB : x ∈ B := B.algebraMap_mem f
  have key : ∀ y ∈ Algebra.adjoin R (t : Set (Localization.Away x)),
      ∃ n : ℕ, ∃ b ∈ B, y * φ x ^ n = φ b := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      exact ⟨m y, a y, Algebra.subset_adjoin (by simpa using ⟨y, hy, rfl⟩), ha y⟩
    | algebraMap r =>
      exact ⟨0, algebraMap R C r, B.algebraMap_mem r, by
        rw [pow_zero, mul_one]; exact IsScalarTower.algebraMap_apply R C _ r⟩
    | add y z _ _ hy hz =>
      obtain ⟨n, b, hb, e⟩ := hy
      obtain ⟨k, d, hd, e'⟩ := hz
      refine ⟨n + k, b * x ^ k + d * x ^ n,
        add_mem (mul_mem hb (pow_mem hxB _)) (mul_mem hd (pow_mem hxB _)), ?_⟩
      rw [map_add, map_mul, map_mul, map_pow, map_pow, ← e, ← e']
      ring
    | mul y z _ _ hy hz =>
      obtain ⟨n, b, hb, e⟩ := hy
      obtain ⟨k, d, hd, e'⟩ := hz
      refine ⟨n + k, b * d, mul_mem hb hd, ?_⟩
      rw [map_mul, ← e, ← e']
      ring
  obtain ⟨n, b, hb, e⟩ := key (φ c) (by rw [ht]; trivial)
  rw [← map_pow, ← map_mul] at e
  obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq x e
  refine ⟨k + n, ?_⟩
  have : x ^ (k + n) * c = x ^ k * b := by rw [← hk]; ring
  rw [this]
  exact mul_mem (pow_mem hxB _) hb

/- English proof (translation)
Set `φ : C →ₐ[R] Localization M ⊗[R] C` to `Algebra.TensorProduct.includeRight`. Establish `hloc : IsLocalizedModule M (TensorProduct.mk R (Localization M) C 1)` using `(isLocalizedModule_iff_isBaseChange M (Localization M) _).2 (TensorProduct.isBaseChange R C (Localization M))`. Establish `hφ : ∀ c, TensorProduct.mk R (Localization M) C 1 c = φ c` using `fun _ => rfl`. Take `⟨t, ht⟩` from `h.out`. Use `choose p hp using fun y => IsLocalizedModule.surj M (TensorProduct.mk R (Localization M) C 1) y`.

Use `⟨t.image fun y => (p y).1, fun c => ?_⟩` and prove the remaining obligations. Use `set B := Algebra.adjoin R ((t.image (fun y => (p y).1) : Finset C) : Set C) with hB`. Establish `key : ∀ y ∈ Algebra.adjoin (Localization M) (t : Set (Localization M ⊗[R] C)), ∃ r ∈ M, ∃ b ∈ B, r • y = φ b`. Introduce `y hy`. Proceed by induction on `hy using Algebra.adjoin_induction with`.

Consider the case `mem y hy`. Conclude with `⟨(p y).2, (p y).2.2, (p y).1, Algebra.subset_adjoin (by simpa using ⟨y, hy, rfl⟩), hp y⟩`. Consider the case `algebraMap q`. Take `⟨⟨a, r⟩, e⟩` from `IsLocalization.surj M q`. Use `⟨r, r.2, algebraMap R C a, B.algebraMap_mem a, ?_⟩` and prove the remaining obligations.

Rewrite using `[φ.commutes, Algebra.smul_def, IsScalarTower.algebraMap_apply R (Localization M), IsScalarTower.algebraMap_apply R (Localization M) _ a, ← map_mul, mul_comm]`. Conclude with `congrArg _ e`. Consider the case `add y z _ _ hy hz`. Take `⟨n, hn, b, hb, e⟩` from `hy`. Take `⟨k, hk, d, hd, e'⟩` from `hz`.

Use `⟨n * k, mul_mem hn hk, k • b + n • d, add_mem (B.smul_mem hb _) (B.smul_mem hd _), ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_smul, map_smul, ← e, ← e', smul_add, smul_smul, smul_smul, mul_comm k n]`. Consider the case `mul y z _ _ hy hz`. Take `⟨n, hn, b, hb, e⟩` from `hy`. Take `⟨k, hk, d, hd, e'⟩` from `hz`.

Use `⟨n * k, mul_mem hn hk, b * d, mul_mem hb hd, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, ← e, ← e', smul_mul_smul_comm]`. Take `⟨r, hr, b, hb, e⟩` from `key (φ c) (by rw [ht]; trivial)`. Rewrite `e` using `[← map_smul, ← hφ, ← hφ]`. Take `⟨k, hk⟩` from `IsLocalizedModule.exists_of_eq (S := M) e`.

Use `⟨k * r, mul_mem k.2 hr, ?_⟩` and prove the remaining obligations. Establish `: algebraMap R C (k * r) * c = (k : R) • b`. Rewrite using `[← Algebra.smul_def, mul_smul]`. Conclude with `hk`. Rewrite using `[this]`.

Conclude with `B.smul_mem hb _`.
-/
theorem exists_smul_mem_of_finiteType_tensor {R C : Type} [CommRing R] [CommRing C] [Algebra R C]
    (M : Submonoid R) (h : Algebra.FiniteType (Localization M) (Localization M ⊗[R] C)) :
    ∃ s : Finset C, ∀ c : C, ∃ r ∈ M, algebraMap R C r * c ∈ Algebra.adjoin R (s : Set C) := by
  classical
  let φ : C →ₐ[R] Localization M ⊗[R] C := Algebra.TensorProduct.includeRight
  have hloc : IsLocalizedModule M (TensorProduct.mk R (Localization M) C 1) :=
    (isLocalizedModule_iff_isBaseChange M (Localization M) _).2
      (TensorProduct.isBaseChange R C (Localization M))
  have hφ : ∀ c, TensorProduct.mk R (Localization M) C 1 c = φ c := fun _ => rfl
  obtain ⟨t, ht⟩ := h.out
  choose p hp using fun y => IsLocalizedModule.surj M (TensorProduct.mk R (Localization M) C 1) y
  refine ⟨t.image fun y => (p y).1, fun c => ?_⟩
  set B := Algebra.adjoin R ((t.image (fun y => (p y).1) : Finset C) : Set C) with hB
  have key : ∀ y ∈ Algebra.adjoin (Localization M) (t : Set (Localization M ⊗[R] C)),
      ∃ r ∈ M, ∃ b ∈ B, r • y = φ b := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      exact ⟨(p y).2, (p y).2.2, (p y).1, Algebra.subset_adjoin (by simpa using ⟨y, hy, rfl⟩), hp y⟩
    | algebraMap q =>
      obtain ⟨⟨a, r⟩, e⟩ := IsLocalization.surj M q
      refine ⟨r, r.2, algebraMap R C a, B.algebraMap_mem a, ?_⟩
      rw [φ.commutes, Algebra.smul_def, IsScalarTower.algebraMap_apply R (Localization M),
        IsScalarTower.algebraMap_apply R (Localization M) _ a, ← map_mul, mul_comm]
      exact congrArg _ e
    | add y z _ _ hy hz =>
      obtain ⟨n, hn, b, hb, e⟩ := hy
      obtain ⟨k, hk, d, hd, e'⟩ := hz
      refine ⟨n * k, mul_mem hn hk, k • b + n • d,
        add_mem (B.smul_mem hb _) (B.smul_mem hd _), ?_⟩
      rw [map_add, map_smul, map_smul, ← e, ← e', smul_add, smul_smul, smul_smul, mul_comm k n]
    | mul y z _ _ hy hz =>
      obtain ⟨n, hn, b, hb, e⟩ := hy
      obtain ⟨k, hk, d, hd, e'⟩ := hz
      refine ⟨n * k, mul_mem hn hk, b * d, mul_mem hb hd, ?_⟩
      rw [map_mul, ← e, ← e', smul_mul_smul_comm]
  obtain ⟨r, hr, b, hb, e⟩ := key (φ c) (by rw [ht]; trivial)
  rw [← map_smul, ← hφ, ← hφ] at e
  obtain ⟨k, hk⟩ := IsLocalizedModule.exists_of_eq (S := M) e
  refine ⟨k * r, mul_mem k.2 hr, ?_⟩
  have : algebraMap R C (k * r) * c = (k : R) • b := by
    rw [← Algebra.smul_def, mul_smul]; exact hk
  rw [this]
  exact B.smul_mem hb _

/- English proof (translation)
Set `J : Ideal B` to `(Ideal.span {x}).comap B.val`. Take `⟨t, ht⟩ : J.FG` from `IsNoetherian.noetherian J`. Use `choose r hrM hr using h`. Establish `hJ : ∀ b : B, ∃ c : C, b ∈ J → (b : C) = x * c`. Introduce `b`.

Distinguish the cases in `hb : b ∈ J`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hb)`. Conclude with `⟨c, fun _ => by rw [mul_comm]; exact hc.symm⟩`. Conclude with `⟨0, fun h => absurd h hb⟩`. Use `choose q hq using hJ`.

Use `⟨∏ b ∈ t, r (q b), prod_mem fun b _ => hrM _, ?_⟩` and prove the remaining obligations. Use `set g := ∏ b ∈ t, r (q b) with hg`. Establish `key : ∀ b ∈ Ideal.span (t : Set B), ∃ c : C, (b : C) = x * c ∧ algebraMap R C g * c ∈ B`. Introduce `b hb`. Proceed by induction on `hb using Submodule.span_induction with`.

Consider the case `mem b hb`. Use `⟨q b, hq b (ht ▸ Ideal.subset_span hb), ?_⟩` and prove the remaining obligations. Rewrite using `[hg, ← Finset.prod_erase_mul t _ hb, map_mul, mul_assoc]`. Conclude with `mul_mem (B.algebraMap_mem _) (hr _)`. Consider the case `zero => exact ⟨0, by simp, by simp⟩`.

Consider the case `add y z _ _ hy hz`. Take `⟨c, e, hc⟩` from `hy`. Take `⟨d, e', hd⟩` from `hz`. Conclude with `⟨c + d, by rw [mul_add, ← e, ← e']; rfl, by rw [mul_add]; exact add_mem hc hd⟩`. Consider the case `smul a y _ hy`.

Take `⟨c, e, hc⟩` from `hy`. Use `⟨a * c, by rw [mul_left_comm, ← e]; rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_left_comm]`. Conclude with `mul_mem a.2 hc`. Introduce `c hc`.

Take `⟨d, e, hd⟩` from `key ⟨x * c, hc⟩ (by`. Rewrite using `[ht]`. Conclude with `Ideal.mem_comap.2 (Ideal.mem_span_singleton'.2 ⟨c, mul_comm _ _⟩))`. Rewrite using `[mul_left_cancel₀ hx e]`. Conclude with `hd`.
-/
theorem exists_mul_mem_of_mul_mem {R C : Type} [CommRing R] [CommRing C] [IsDomain C] [Algebra R C]
    (B : Subalgebra R C) [IsNoetherianRing B] (x : C) (hx : x ≠ 0) (M : Submonoid R)
    (h : ∀ c : C, ∃ r ∈ M, algebraMap R C r * c ∈ B) :
    ∃ g ∈ M, ∀ c : C, x * c ∈ B → algebraMap R C g * c ∈ B := by
  classical
  let J : Ideal B := (Ideal.span {x}).comap B.val
  obtain ⟨t, ht⟩ : J.FG := IsNoetherian.noetherian J
  choose r hrM hr using h
  have hJ : ∀ b : B, ∃ c : C, b ∈ J → (b : C) = x * c := by
    intro b
    by_cases hb : b ∈ J
    · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hb)
      exact ⟨c, fun _ => by rw [mul_comm]; exact hc.symm⟩
    · exact ⟨0, fun h => absurd h hb⟩
  choose q hq using hJ
  refine ⟨∏ b ∈ t, r (q b), prod_mem fun b _ => hrM _, ?_⟩
  set g := ∏ b ∈ t, r (q b) with hg
  have key : ∀ b ∈ Ideal.span (t : Set B), ∃ c : C, (b : C) = x * c ∧ algebraMap R C g * c ∈ B := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      refine ⟨q b, hq b (ht ▸ Ideal.subset_span hb), ?_⟩
      rw [hg, ← Finset.prod_erase_mul t _ hb, map_mul, mul_assoc]
      exact mul_mem (B.algebraMap_mem _) (hr _)
    | zero => exact ⟨0, by simp, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨c, e, hc⟩ := hy
      obtain ⟨d, e', hd⟩ := hz
      exact ⟨c + d, by rw [mul_add, ← e, ← e']; rfl, by rw [mul_add]; exact add_mem hc hd⟩
    | smul a y _ hy =>
      obtain ⟨c, e, hc⟩ := hy
      refine ⟨a * c, by rw [mul_left_comm, ← e]; rfl, ?_⟩
      rw [mul_left_comm]
      exact mul_mem a.2 hc
  intro c hc
  obtain ⟨d, e, hd⟩ := key ⟨x * c, hc⟩ (by
    rw [ht]
    exact Ideal.mem_comap.2 (Ideal.mem_span_singleton'.2 ⟨c, mul_comm _ _⟩))
  rw [mul_left_cancel₀ hx e]
  exact hd

/- English proof (translation)
Take `⟨s₁, hs₁⟩` from `exists_pow_mul_mem_of_finiteType_away f h₁`. Take `⟨s₂, hs₂⟩` from `exists_smul_mem_of_finiteType_tensor 𝔭.primeCompl h₂`. Set `B` to `Algebra.adjoin R ((s₁ ∪ s₂ : Finset C) : Set C)`. Establish `hB₁ : Algebra.adjoin R (s₁ : Set C) ≤ B` using `Algebra.adjoin_mono (by simp)`. Establish `hB₂ : Algebra.adjoin R (s₂ : Set C) ≤ B` using `Algebra.adjoin_mono (by simp)`.

Establish `: IsNoetherianRing B` using `isNoetherianRing_of_fg ⟨s₁ ∪ s₂, rfl⟩`. Take `⟨g, hg, hgB⟩` from `exists_mul_mem_of_mul_mem B _ hf 𝔭.primeCompl fun c => (hs₂ c).imp fun r hr => ⟨hr.1, hB₂ hr.2⟩`. Use `⟨g, hg, finiteType_away_of_pow_mul_mem (s₁ ∪ s₂) _ fun c => ?_⟩` and prove the remaining obligations. Establish `key : ∀ (n : ℕ) (c : C), algebraMap R C f ^ n * c ∈ B → algebraMap R C g ^ n * c ∈ B`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => intro c hc`. Simplify using `using hc`. Consider the case `succ n ih`. Introduce `c hc`.

Rewrite `hc` using `[pow_succ, mul_assoc]`. Establish `h` using `ih _ hc`. Rewrite `h` using `[mul_left_comm]`. Rewrite using `[pow_succ', mul_assoc]`. Conclude with `hgB _ h`.

Take `⟨n, hn⟩` from `hs₁ c`. Conclude with `⟨n, key n c (hB₁ hn)⟩`.
-/
theorem exists_finiteType_away_of_atPrime (R C : Type) [CommRing R] [IsNoetherianRing R]
    [CommRing C] [IsDomain C] [Algebra R C] (f : R) (𝔭 : Ideal R) [𝔭.IsPrime]
    (hf : algebraMap R C f ≠ 0)
    (h₁ : Algebra.FiniteType R (Localization.Away (algebraMap R C f)))
    (h₂ : Algebra.FiniteType (Localization.AtPrime 𝔭)
      (TensorProduct R (Localization.AtPrime 𝔭) C)) :
    ∃ g : R, g ∉ 𝔭 ∧ Algebra.FiniteType R (Localization.Away (algebraMap R C g)) := by
  classical
  obtain ⟨s₁, hs₁⟩ := exists_pow_mul_mem_of_finiteType_away f h₁
  obtain ⟨s₂, hs₂⟩ := exists_smul_mem_of_finiteType_tensor 𝔭.primeCompl h₂
  let B := Algebra.adjoin R ((s₁ ∪ s₂ : Finset C) : Set C)
  have hB₁ : Algebra.adjoin R (s₁ : Set C) ≤ B := Algebra.adjoin_mono (by simp)
  have hB₂ : Algebra.adjoin R (s₂ : Set C) ≤ B := Algebra.adjoin_mono (by simp)
  have : IsNoetherianRing B := isNoetherianRing_of_fg ⟨s₁ ∪ s₂, rfl⟩
  obtain ⟨g, hg, hgB⟩ := exists_mul_mem_of_mul_mem B _ hf 𝔭.primeCompl fun c =>
    (hs₂ c).imp fun r hr => ⟨hr.1, hB₂ hr.2⟩
  refine ⟨g, hg, finiteType_away_of_pow_mul_mem (s₁ ∪ s₂) _ fun c => ?_⟩
  have key : ∀ (n : ℕ) (c : C), algebraMap R C f ^ n * c ∈ B → algebraMap R C g ^ n * c ∈ B := by
    intro n
    induction n with
    | zero => intro c hc; simpa using hc
    | succ n ih =>
      intro c hc
      rw [pow_succ, mul_assoc] at hc
      have h := ih _ hc
      rw [mul_left_comm] at h
      rw [pow_succ', mul_assoc]
      exact hgB _ h
  obtain ⟨n, hn⟩ := hs₁ c
  exact ⟨n, key n c (hB₁ hn)⟩

end GlobalTheory.Desc
