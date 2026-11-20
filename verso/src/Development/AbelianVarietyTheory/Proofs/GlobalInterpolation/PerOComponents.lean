import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove.PeriodComp

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

/- English proof (translation)
The claim follows from `x.map_smul_of_tower s y`.
-/
theorem apply_smul (x : HomE E a b) (s : 𝓞 E) (y : Sp E a) : x (s • y) = s • x y := x.map_smul_of_tower s y

/- English proof (translation)
Take `⟨T, hT⟩` from `hN`. Establish `hgen : ∀ y ∈ T, ∃ s ∈ S, s • x y ∈ N'` using `fun y hy => h y (hT ▸ Submodule.subset_span (Finset.mem_coe.mpr hy))`. Use `choose! f hfS hf using hgen`. Use `⟨∏ y ∈ T, f y, prod_mem fun y hy => hfS y hy, ?_⟩` and prove the remaining obligations. Introduce `y hy`.

Rewrite `hy` using `[← hT]`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Rewrite using `[LinearMap.smul_apply, ← Finset.mul_prod_erase T f (Finset.mem_coe.mp hy), mul_comm, mul_smul]`. Conclude with `N'.smul_mem _ (hf y (Finset.mem_coe.mp hy))`.

Consider the case `zero => rw [map_zero]`. Conclude with `N'.zero_mem`. Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `N'.add_mem hy hz`. Consider the case `smul r y _ hy => rw [GlobalTheory.ThetaMove.PeriodComp.apply_smul]`.

Conclude with `N'.smul_mem r hy`.
-/
theorem exists_common (S : Submonoid (𝓞 E)) {N : Submodule (𝓞 E) (Sp E a)} (hN : N.FG) (N' : Submodule (𝓞 E) (Sp E b))
    (x : HomE E a b) (h : ∀ y ∈ N, ∃ s ∈ S, s • x y ∈ N') : ∃ s ∈ S, s • x ∈ homO N N' := by
  classical
  obtain ⟨T, hT⟩ := hN
  have hgen : ∀ y ∈ T, ∃ s ∈ S, s • x y ∈ N' := fun y hy =>
    h y (hT ▸ Submodule.subset_span (Finset.mem_coe.mpr hy))
  choose! f hfS hf using hgen
  refine ⟨∏ y ∈ T, f y, prod_mem fun y hy => hfS y hy, ?_⟩
  intro y hy
  rw [← hT] at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    rw [LinearMap.smul_apply, ← Finset.mul_prod_erase T f (Finset.mem_coe.mp hy), mul_comm, mul_smul]
    exact N'.smul_mem _ (hf y (Finset.mem_coe.mp hy))
  | zero => rw [map_zero]; exact N'.zero_mem
  | add y z _ _ hy hz => rw [map_add]; exact N'.add_mem hy hz
  | smul r y _ hy => rw [GlobalTheory.ThetaMove.PeriodComp.apply_smul]; exact N'.smul_mem r hy

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨r, hr, x, hx, rfl⟩`.
-/
theorem smul_mem_perO {AA : Submodule (𝓞 E) E} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}
    {r : E} (hr : r ∈ AA) {x : HomE E a b} (hx : x ∈ homO N N') : r • x ∈ perO AA N N' :=
  Submodule.subset_span ⟨r, hr, x, hx, rfl⟩

/- English proof (translation)
Establish `hgen : perO AA N₁ N₁' ≤ localization₂ Q.asIdeal (perO AA N₂ N₂')`. Apply `Submodule.span_le.mpr` to reduce the goal to its premises. Introduce and unpack `_ ⟨r, hr, x, hx, rfl⟩`. Establish `hmult : ∀ y ∈ N₂, ∃ s ∈ Q.asIdeal.primeCompl, s • x y ∈ N₂'`. Introduce `y hy`.

Take `⟨u, hu, huy⟩` from `h (mem_localization_of_mem Q hy)`. Establish `hxy : x (u • y) ∈ N₁'` using `hx _ huy`. Rewrite `hxy` using `[GlobalTheory.ThetaMove.PeriodComp.apply_smul]`. Take `⟨v, hv, hvxy⟩` from `h' (mem_localization_of_mem Q hxy)`. Conclude with `⟨v * u, mul_mem hv hu, by rw [mul_smul]; exact hvxy⟩`.

Take `⟨t, ht, htx⟩` from `GlobalTheory.ThetaMove.PeriodComp.exists_common Q.asIdeal.primeCompl hN N₂' x hmult`. Conclude with `⟨t, ht, by rw [smul_comm]; exact GlobalTheory.ThetaMove.PeriodComp.smul_mem_perO hr htx⟩`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mono (AA : Submodule (𝓞 E) E) (Q : HeightOneSpectrum (𝓞 E)) (N₁ N₂ : Submodule (𝓞 E) (Sp E a))
    (N₁' N₂' : Submodule (𝓞 E) (Sp E b)) (hN : N₂.FG) (h : localization₂ Q.asIdeal N₂ ≤ localization₂ Q.asIdeal N₁)
    (h' : localization₂ Q.asIdeal N₁' ≤ localization₂ Q.asIdeal N₂') :
    localization₂ Q.asIdeal (perO AA N₁ N₁') ≤ localization₂ Q.asIdeal (perO AA N₂ N₂') := by
  have hgen : perO AA N₁ N₁' ≤ localization₂ Q.asIdeal (perO AA N₂ N₂') := by
    apply Submodule.span_le.mpr
    rintro _ ⟨r, hr, x, hx, rfl⟩
    have hmult : ∀ y ∈ N₂, ∃ s ∈ Q.asIdeal.primeCompl, s • x y ∈ N₂' := by
      intro y hy
      obtain ⟨u, hu, huy⟩ := h (mem_localization_of_mem Q hy)
      have hxy : x (u • y) ∈ N₁' := hx _ huy
      rw [GlobalTheory.ThetaMove.PeriodComp.apply_smul] at hxy
      obtain ⟨v, hv, hvxy⟩ := h' (mem_localization_of_mem Q hxy)
      exact ⟨v * u, mul_mem hv hu, by rw [mul_smul]; exact hvxy⟩
    obtain ⟨t, ht, htx⟩ := GlobalTheory.ThetaMove.PeriodComp.exists_common Q.asIdeal.primeCompl hN N₂' x hmult
    exact ⟨t, ht, by rw [smul_comm]; exact GlobalTheory.ThetaMove.PeriodComp.smul_mem_perO hr htx⟩
  calc localization₂ Q.asIdeal (perO AA N₁ N₁') ≤ localization₂ Q.asIdeal (localization₂ Q.asIdeal (perO AA N₂ N₂')) :=
        localization_mono Q hgen
    _ = localization₂ Q.asIdeal (perO AA N₂ N₂') := localization_localization₂ Q _

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Establish `hgen : perO AA N N' ≤ homAt {P} N N'`. Apply `Submodule.span_le.mpr` to reduce the goal to its premises. Introduce and unpack `_ ⟨r, hr, x, hx, rfl⟩`. Introduce `P' hP' y hy`.

Rewrite `hP'` using `[Finset.mem_singleton]`. Substitute `hP'` using the available equality. Take `⟨u, hu, huy⟩` from `hy`. Establish `hr1 : r ∈ localization₂ P'.asIdeal (1 : Submodule (𝓞 E) E)`. Rewrite using `[← hA]`.

Conclude with `mem_localization_of_mem P' hr`. Take `⟨v, hv, hvr⟩` from `hr1`. Take `⟨w, hw⟩` from `Submodule.mem_one.mp hvr`. Establish `hxy : u • x y ∈ N'`. Rewrite using `[← GlobalTheory.ThetaMove.PeriodComp.apply_smul]`.

Conclude with `hx _ huy`. Use `⟨v * u, mul_mem hv hu, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, mul_smul, smul_comm u r, ← smul_assoc v r, ← hw, algebraMap_smul]`. Conclude with `N'.smul_mem w hxy`. Introduce `z hz`.

Take `⟨s, hs, hsz⟩` from `hz`. Establish `h1` using `hgen hsz`. Introduce `P' hP' y hy`. Take `⟨t, ht, hty⟩` from `h1 P' hP' y hy`. Rewrite `hP'` using `[Finset.mem_singleton]`.

Substitute `hP'` using the available equality. Use `⟨t * s, mul_mem ht hs, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul, ← LinearMap.smul_apply]`. Conclude with `hty`. Introduce `x hx`.

Establish `h1 : (1 : E) ∈ localization₂ P.asIdeal AA`. Rewrite using `[hA]`. Conclude with `mem_localization_of_mem P (Submodule.mem_one.mpr ⟨1, map_one _⟩)`. Take `⟨v, hv, hv1⟩` from `h1`. Establish `hmult : ∀ y ∈ N, ∃ s ∈ P.asIdeal.primeCompl, s • x y ∈ N'` using `fun y hy => hx P (Finset.mem_singleton_self P) y (mem_localization_of_mem P hy)`.

Take `⟨t, ht, htx⟩` from `GlobalTheory.ThetaMove.PeriodComp.exists_common P.asIdeal.primeCompl hN N' x hmult`. Use `⟨v * t, mul_mem hv ht, ?_⟩` and prove the remaining obligations. Establish `h2` using `GlobalTheory.ThetaMove.PeriodComp.smul_mem_perO hv1 htx`. Rewrite `h2` using `[smul_one_smul, ← mul_smul]`. Then use the resulting hypothesis.
-/
theorem eq_homAt (AA : Submodule (𝓞 E) E) (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E a))
    (N' : Submodule (𝓞 E) (Sp E b)) (hN : N.FG)
    (hA : localization₂ P.asIdeal AA = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E)) :
    localization₂ P.asIdeal (perO AA N N') = homAt {P} N N' := by
  apply le_antisymm
  · have hgen : perO AA N N' ≤ homAt {P} N N' := by
      apply Submodule.span_le.mpr
      rintro _ ⟨r, hr, x, hx, rfl⟩
      intro P' hP' y hy
      rw [Finset.mem_singleton] at hP'
      subst hP'
      obtain ⟨u, hu, huy⟩ := hy
      have hr1 : r ∈ localization₂ P'.asIdeal (1 : Submodule (𝓞 E) E) := by
        rw [← hA]; exact mem_localization_of_mem P' hr
      obtain ⟨v, hv, hvr⟩ := hr1
      obtain ⟨w, hw⟩ := Submodule.mem_one.mp hvr
      have hxy : u • x y ∈ N' := by
        rw [← GlobalTheory.ThetaMove.PeriodComp.apply_smul]; exact hx _ huy
      refine ⟨v * u, mul_mem hv hu, ?_⟩
      rw [LinearMap.smul_apply, mul_smul, smul_comm u r, ← smul_assoc v r, ← hw, algebraMap_smul]
      exact N'.smul_mem w hxy
    intro z hz
    obtain ⟨s, hs, hsz⟩ := hz
    have h1 := hgen hsz
    intro P' hP' y hy
    obtain ⟨t, ht, hty⟩ := h1 P' hP' y hy
    rw [Finset.mem_singleton] at hP'
    subst hP'
    refine ⟨t * s, mul_mem ht hs, ?_⟩
    rw [mul_smul, ← LinearMap.smul_apply]
    exact hty
  · intro x hx
    have h1 : (1 : E) ∈ localization₂ P.asIdeal AA := by
      rw [hA]; exact mem_localization_of_mem P (Submodule.mem_one.mpr ⟨1, map_one _⟩)
    obtain ⟨v, hv, hv1⟩ := h1
    have hmult : ∀ y ∈ N, ∃ s ∈ P.asIdeal.primeCompl, s • x y ∈ N' := fun y hy =>
      hx P (Finset.mem_singleton_self P) y (mem_localization_of_mem P hy)
    obtain ⟨t, ht, htx⟩ := GlobalTheory.ThetaMove.PeriodComp.exists_common P.asIdeal.primeCompl hN N' x hmult
    refine ⟨v * t, mul_mem hv ht, ?_⟩
    have h2 := GlobalTheory.ThetaMove.PeriodComp.smul_mem_perO hv1 htx
    rwa [smul_one_smul, ← mul_smul] at h2

/- English proof (translation)
Establish `hv : v ∈ Submodule.span E (N' : Set (Sp E b))`. Rewrite using `[hN'.span_eq_top]`. Conclude with `Submodule.mem_top`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem w hw => exact ⟨1, one_pos, by rw [Nat.cast_one, one_smul]; exact hw⟩`.

Consider the case `zero => exact ⟨1, one_pos, by rw [smul_zero]; exact N'.zero_mem⟩`. Consider the case `add v w _ _ hv hw`. Take `⟨m, hm, hmv⟩` from `hv`. Take `⟨k, hk, hkw⟩` from `hw`. Use `⟨m * k, Nat.mul_pos hm hk, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_add, Nat.cast_mul]`. Use `N'.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`. Conclude with `N'.smul_mem _ hmv`. Rewrite using `[mul_smul]`.

Conclude with `N'.smul_mem _ hkw`. Consider the case `smul c v _ hv`. Take `⟨m, hm, hmv⟩` from `hv`. Take `⟨y, hy0, hyint⟩` from `exists_integral_multiples ℤ ℚ ({c} : Finset E)`. Establish `h1 : IsIntegral ℤ ((y : E) * c)`.

Simplify `hyint c (Finset.mem_singleton_self c)` using `[zsmul_eq_mul]`. Establish `hint : IsIntegral ℤ ((y.natAbs : E) * c)`. Break down `Int.natAbs_eq y with h | h` into its components or cases. Rewrite `h1` using `[h]`. Simplify using `using h1`.

Rewrite `h1` using `[h]`. Simplify using `using h1.neg`. Use `⟨y.natAbs * m, Nat.mul_pos (Int.natAbs_pos.mpr hy0) hm, ?_⟩` and prove the remaining obligations. Establish `key : ((y.natAbs * m : ℕ) : 𝓞 E) • (c • v) = (⟨(y.natAbs : E) * c, hint⟩ : 𝓞 E) • ((m : 𝓞 E) • v)`. Use extensionality with `i`.

Rewrite using `[Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply]`. Simplify using `only [smul_eq_mul, Algebra.smul_def, map_natCast]`. Use `push_cast`. Establish `hα : ∀ z : ↥(integralClosure ℤ E), algebraMap (↥(integralClosure ℤ E)) E z = (z : E)` using `fun _ => rfl`. Simplify using `only [hα]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`. Conclude with `N'.smul_mem _ hmv`.
-/
private theorem exists_nsmul_mem_of_isLattice (N' : Submodule (𝓞 E) (Sp E b)) (hN' : Submodule.IsLattice E N') (v : Sp E b) :
    ∃ n : ℕ, 0 < n ∧ (n : 𝓞 E) • v ∈ N' := by
  have hv : v ∈ Submodule.span E (N' : Set (Sp E b)) := by
    rw [hN'.span_eq_top]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem w hw => exact ⟨1, one_pos, by rw [Nat.cast_one, one_smul]; exact hw⟩
  | zero => exact ⟨1, one_pos, by rw [smul_zero]; exact N'.zero_mem⟩
  | add v w _ _ hv hw =>
    obtain ⟨m, hm, hmv⟩ := hv
    obtain ⟨k, hk, hkw⟩ := hw
    refine ⟨m * k, Nat.mul_pos hm hk, ?_⟩
    rw [smul_add, Nat.cast_mul]
    refine N'.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact N'.smul_mem _ hmv
    · rw [mul_smul]; exact N'.smul_mem _ hkw
  | smul c v _ hv =>
    obtain ⟨m, hm, hmv⟩ := hv
    obtain ⟨y, hy0, hyint⟩ := exists_integral_multiples ℤ ℚ ({c} : Finset E)
    have h1 : IsIntegral ℤ ((y : E) * c) := by
      simpa [zsmul_eq_mul] using hyint c (Finset.mem_singleton_self c)
    have hint : IsIntegral ℤ ((y.natAbs : E) * c) := by
      rcases Int.natAbs_eq y with h | h
      · rw [h] at h1; simpa using h1
      · rw [h] at h1; simpa using h1.neg
    refine ⟨y.natAbs * m, Nat.mul_pos (Int.natAbs_pos.mpr hy0) hm, ?_⟩
    have key : ((y.natAbs * m : ℕ) : 𝓞 E) • (c • v) =
        (⟨(y.natAbs : E) * c, hint⟩ : 𝓞 E) • ((m : 𝓞 E) • v) := by
      ext i
      rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply]
      simp only [smul_eq_mul, Algebra.smul_def, map_natCast]
      push_cast
      have hα : ∀ z : ↥(integralClosure ℤ E), algebraMap (↥(integralClosure ℤ E)) E z = (z : E) :=
        fun _ => rfl
      simp only [hα]
      ring
    rw [key]
    exact N'.smul_mem _ hmv

/- English proof (translation)
Take `⟨r, hrA, hr0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hA`. Introduce `x`. Set `S : Submonoid (𝓞 E)` to `{ carrier := {s | ∃ n : ℕ, 0 < n ∧ (n : 𝓞 E) = s} mul_mem' := by`. Introduce and unpack `_ _ ⟨m, hm, rfl⟩ ⟨k, hk, rfl⟩`. Conclude with `⟨m * k, Nat.mul_pos hm hk, by push_cast; rfl⟩`.

Use the proof step `one_mem' := ⟨1, one_pos, Nat.cast_one⟩ }`. Establish `hmult : ∀ y ∈ N, ∃ s ∈ S, s • (r⁻¹ • x) y ∈ N'` using `fun y _ => by`. Take `⟨n, hn, h⟩` from `exists_nsmul_mem_of_isLattice N' hN' ((r⁻¹ • x) y)`. Conclude with `⟨n, ⟨n, hn, rfl⟩, h⟩`. Take `⟨s, hsS, hs⟩` from `GlobalTheory.ThetaMove.PeriodComp.exists_common S hN N' (r⁻¹ • x) hmult`.

Take `⟨n, hn, rfl⟩` from `hsS`. Use `⟨n, hn, ?_⟩` and prove the remaining obligations. Establish `h2` using `GlobalTheory.ThetaMove.PeriodComp.smul_mem_perO hrA hs`. Rewrite `h2` using `[smul_comm r, smul_inv_smul₀ hr0]`. Then use the resulting hypothesis.
-/
theorem full (AA : Submodule (𝓞 E) E) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (hN : N.FG)
    (hN' : Submodule.IsLattice E N') (hA : AA ≠ ⊥) : Full (perO AA N N') := by
  obtain ⟨r, hrA, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA
  intro x
  let S : Submonoid (𝓞 E) :=
    { carrier := {s | ∃ n : ℕ, 0 < n ∧ (n : 𝓞 E) = s}
      mul_mem' := by
        rintro _ _ ⟨m, hm, rfl⟩ ⟨k, hk, rfl⟩
        exact ⟨m * k, Nat.mul_pos hm hk, by push_cast; rfl⟩
      one_mem' := ⟨1, one_pos, Nat.cast_one⟩ }
  have hmult : ∀ y ∈ N, ∃ s ∈ S, s • (r⁻¹ • x) y ∈ N' := fun y _ => by
    obtain ⟨n, hn, h⟩ := exists_nsmul_mem_of_isLattice N' hN' ((r⁻¹ • x) y)
    exact ⟨n, ⟨n, hn, rfl⟩, h⟩
  obtain ⟨s, hsS, hs⟩ := GlobalTheory.ThetaMove.PeriodComp.exists_common S hN N' (r⁻¹ • x) hmult
  obtain ⟨n, hn, rfl⟩ := hsS
  refine ⟨n, hn, ?_⟩
  have h2 := GlobalTheory.ThetaMove.PeriodComp.smul_mem_perO hrA hs
  rwa [smul_comm r, smul_inv_smul₀ hr0] at h2

/- English proof (translation)
Introduce `E _ _ _ a b AA`. Conclude with `⟨fun Q N₁ N₂ N₁' N₂' hN h h' => GlobalTheory.ThetaMove.PeriodComp.mono AA Q N₁ N₂ N₁' N₂' hN h h', fun P N N' hN hA => GlobalTheory.ThetaMove.PeriodComp.eq_homAt AA P N N' hN hA, fun N N' hN hN' hA => GlobalTheory.ThetaMove.PeriodComp.full AA N N' hN hN' hA⟩`.
-/
theorem perO_components : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (a b : ℕ) (AA : Submodule (𝓞 E) E), (∀ (Q : HeightOneSpectrum (𝓞 E)) (N₁ N₂ : Submodule (𝓞 E) (Sp E a)) (N₁' N₂' : Submodule (𝓞 E) (Sp E b)), N₂.FG → localization₂ Q.asIdeal N₂ ≤ localization₂ Q.asIdeal N₁ → localization₂ Q.asIdeal N₁' ≤ localization₂ Q.asIdeal N₂' → localization₂ Q.asIdeal (perO AA N₁ N₁') ≤ localization₂ Q.asIdeal (perO AA N₂ N₂')) ∧ (∀ (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)), N.FG → localization₂ P.asIdeal AA = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E) → localization₂ P.asIdeal (perO AA N N') = homAt {P} N N') ∧ ∀ (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)), N.FG → Submodule.IsLattice E N' → AA ≠ ⊥ → Full (perO AA N N') := by
  intro E _ _ _ a b AA
  exact ⟨fun Q N₁ N₂ N₁' N₂' hN h h' => GlobalTheory.ThetaMove.PeriodComp.mono AA Q N₁ N₂ N₁' N₂' hN h h',
    fun P N N' hN hA => GlobalTheory.ThetaMove.PeriodComp.eq_homAt AA P N N' hN hA,
    fun N N' hN hN' hA => GlobalTheory.ThetaMove.PeriodComp.full AA N N' hN hN' hA⟩

end GlobalTheory.ThetaMove.PeriodComp
