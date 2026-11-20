import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryOfUnimodularLatticesAtPlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnimodularOverlatticeCyclicSplitDiscrimina
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StarMemLocR

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.CyclicGenus

section General

variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

def Cyc (A B : Submodule R W) (I : Ideal R) : Prop :=
  ∃ x ∈ A, (∀ y ∈ A, ∃ a : R, y - a • x ∈ B) ∧ ∀ r : R, r • x ∈ B ↔ r ∈ I

/- English proof (translation)
Take `⟨x, hx⟩` from `Submodule.Quotient.mk_surjective _ (e.symm (Submodule.Quotient.mk 1))`. Establish `hx' : e (Submodule.Quotient.mk x) = Submodule.Quotient.mk 1` using `by rw [hx]; simp`. Use `⟨x, x.2, fun y hy => ?_, fun r => ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `Submodule.Quotient.mk_surjective I (e (Submodule.Quotient.mk ⟨y, hy⟩))`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Establish `: (Submodule.Quotient.mk (⟨y, hy⟩ - a • x) : A ⧸ B.comap A.subtype) = 0`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, map_sub, map_smul, hx', ← ha, ← Submodule.Quotient.mk_smul]`. Simplify using the standard rewrite rules. Rewrite `this` using `[Submodule.Quotient.mk_eq_zero]`.

Conclude with `this`. Establish `: r • (x : W) ∈ B ↔ (Submodule.Quotient.mk (r • x) : A ⧸ B.comap A.subtype) = 0`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Both sides reduce to the same expression. Rewrite using `[this, ← EmbeddingLike.map_eq_zero_iff (f := e), Submodule.Quotient.mk_smul, map_smul, hx', ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul, mul_one]`.
-/
theorem cyc_of_equiv {A B : Submodule R W} {I : Ideal R}
    (e : (A ⧸ B.comap A.subtype) ≃ₗ[R] (R ⧸ I)) : Cyc A B I := by
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (e.symm (Submodule.Quotient.mk 1))
  have hx' : e (Submodule.Quotient.mk x) = Submodule.Quotient.mk 1 := by rw [hx]; simp
  refine ⟨x, x.2, fun y hy => ?_, fun r => ?_⟩
  · obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective I (e (Submodule.Quotient.mk ⟨y, hy⟩))
    refine ⟨a, ?_⟩
    have : (Submodule.Quotient.mk (⟨y, hy⟩ - a • x) : A ⧸ B.comap A.subtype) = 0 := by
      apply e.injective
      rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, map_sub, map_smul, hx', ← ha,
        ← Submodule.Quotient.mk_smul]
      simp
    rw [Submodule.Quotient.mk_eq_zero] at this
    exact this
  · have : r • (x : W) ∈ B ↔ (Submodule.Quotient.mk (r • x) : A ⧸ B.comap A.subtype) = 0 := by
      rw [Submodule.Quotient.mk_eq_zero]; rfl
    rw [this, ← EmbeddingLike.map_eq_zero_iff (f := e), Submodule.Quotient.mk_smul, map_smul, hx',
      ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul, mul_one]

/- English proof (translation)
Set `φ : R →ₗ[R] (A ⧸ B.comap A.subtype)` to `LinearMap.toSpanSingleton R _ (Submodule.Quotient.mk ⟨x, hx⟩)`. Establish `hφ : ∀ r, φ r = Submodule.Quotient.mk (r • ⟨x, hx⟩)` using `fun r => by`. Rewrite using `[Submodule.Quotient.mk_smul]`. Both sides reduce to the same expression. Establish `hk : LinearMap.ker φ = I`.

Use extensionality with `r`. Rewrite using `[LinearMap.mem_ker, hφ, Submodule.Quotient.mk_eq_zero, ← hI]`. Both sides reduce to the same expression. Use `⟨Submodule.liftQ I φ hk.ge, ?_, fun r => hφ r⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.ker_eq_bot]`.

Conclude with `Submodule.ker_liftQ_eq_bot _ _ _ hk.le`.
-/
theorem exists_inj {A B : Submodule R W} {I : Ideal R} (x : W) (hx : x ∈ A)
    (hI : ∀ r : R, r • x ∈ B ↔ r ∈ I) :
    ∃ f : (R ⧸ I) →ₗ[R] (A ⧸ B.comap A.subtype), Function.Injective f ∧
      ∀ r : R, f (Submodule.Quotient.mk r) = Submodule.Quotient.mk (r • ⟨x, hx⟩) := by
  let φ : R →ₗ[R] (A ⧸ B.comap A.subtype) :=
    LinearMap.toSpanSingleton R _ (Submodule.Quotient.mk ⟨x, hx⟩)
  have hφ : ∀ r, φ r = Submodule.Quotient.mk (r • ⟨x, hx⟩) := fun r => by
    rw [Submodule.Quotient.mk_smul]; rfl
  have hk : LinearMap.ker φ = I := by
    ext r
    rw [LinearMap.mem_ker, hφ, Submodule.Quotient.mk_eq_zero, ← hI]; rfl
  refine ⟨Submodule.liftQ I φ hk.ge, ?_, fun r => hφ r⟩
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot _ _ _ hk.le

/- English proof (translation)
Take `⟨x, hx, h1, h2⟩` from `h`. Take `⟨f, hf, hf'⟩` from `exists_inj x hx h2`. Use `⟨(LinearEquiv.ofBijective f ⟨hf, fun q => ?_⟩).symm⟩` and prove the remaining obligations. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Take `⟨a, ha⟩` from `h1 y y.2`.

Use `⟨Submodule.Quotient.mk a, ?_⟩` and prove the remaining obligations. Rewrite using `[hf', eq_comm, Submodule.Quotient.eq]`. Conclude with `ha`.
-/
theorem equiv_of_cyc {A B : Submodule R W} {I : Ideal R} (h : Cyc A B I) :
    Nonempty ((A ⧸ B.comap A.subtype) ≃ₗ[R] (R ⧸ I)) := by
  obtain ⟨x, hx, h1, h2⟩ := h
  obtain ⟨f, hf, hf'⟩ := exists_inj x hx h2
  refine ⟨(LinearEquiv.ofBijective f ⟨hf, fun q => ?_⟩).symm⟩
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨a, ha⟩ := h1 y y.2
  refine ⟨Submodule.Quotient.mk a, ?_⟩
  rw [hf', eq_comm, Submodule.Quotient.eq]
  exact ha

/- English proof (translation)
Take `⟨x, -, h1, h2⟩` from `h`. Take `⟨a, ha⟩` from `h1 y hy`. Establish `: r • y = r • (y - a • x) + a • (r • x)` using `by rw [smul_sub, smul_comm a r x]; abel`. Rewrite using `[this]`. Conclude with `B.add_mem (B.smul_mem r ha) (B.smul_mem a ((h2 r).2 hr))`.
-/
theorem Cyc.smul_mem {A B : Submodule R W} {I : Ideal R} (h : Cyc A B I) {r : R} (hr : r ∈ I)
    {y : W} (hy : y ∈ A) : r • y ∈ B := by
  obtain ⟨x, -, h1, h2⟩ := h
  obtain ⟨a, ha⟩ := h1 y hy
  have : r • y = r • (y - a • x) + a • (r • x) := by rw [smul_sub, smul_comm a r x]; abel
  rw [this]
  exact B.add_mem (B.smul_mem r ha) (B.smul_mem a ((h2 r).2 hr))

/- English proof (translation)
Take `⟨x, hx, h1, h2⟩` from `h`. Establish `inv : ∀ s ∈ S, ∃ u, 1 - u * s ∈ P` using `fun s hs => by`. Take `⟨u, p, hp, e⟩` from `hP.exists_inv (hS s hs)`. Conclude with `⟨u, by rw [← e]; simpa using hp⟩`. Take `⟨s, hs, hsx⟩ : x ∈ locS S M` from `hM ▸ locBasic_le_locS S M' hx`.

Use `⟨s • x, hsx, fun y hy => ?_, fun r => ⟨fun hr => ?_, fun hr => ⟨M.smul_mem r hsx, ?_⟩⟩⟩` and prove the remaining obligations. Take `⟨t, ht, hty⟩ : y ∈ locS S M'` from `hM.symm ▸ locBasic_le_locS S M hy`. Take `⟨a, ha⟩` from `h1 _ hty`. Take `⟨u, hu⟩` from `inv _ (S.mul_mem ht hs)`. Take `⟨t', ht', hu'⟩` from `hPI _ hu`.

Use `⟨u * a, M.sub_mem hy (M.smul_mem _ hsx), t' * t, S.mul_mem ht' ht, ?_⟩` and prove the remaining obligations. Establish `: (t' * t) • (y - (u * a) • s • x) = t' • (t • y - a • x) + a • ((t' * (1 - u * (t * s))) • x)` using `by module`. Rewrite using `[this]`. Conclude with `L'.add_mem (L'.smul_mem _ ha) (L'.smul_mem _ ((h2 _).2 hu'))`. Take `⟨t, ht, htx⟩` from `hr.2`.

Rewrite `htx` using `[smul_smul, smul_smul, h2]`. Use `hIP htx` as an intermediate fact. Break down `hP.isPrime.mem_or_mem this with h | h` into its components or cases. Conclude with `(hP.isPrime.mem_or_mem h).resolve_left (hS t ht)`. Conclude with `absurd h (hS s hs)`.

Take `⟨t, ht, htr⟩` from `hPI r hr`. Use `⟨t, ht, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_smul, smul_smul, h2]`. Conclude with `I.mul_mem_right _ htr`.
-/
theorem Cyc.localise {M' L' M : Submodule R W} {I P : Ideal R} (h : Cyc M' L' I) (hP : P.IsMaximal)
    (S : Submonoid R) (hS : ∀ s ∈ S, s ∉ P) (hIP : I ≤ P) (hPI : ∀ r ∈ P, ∃ t ∈ S, t * r ∈ I)
    (hM : locS S M' = locS S M) : Cyc M (M ⊓ locS S L') P := by
  obtain ⟨x, hx, h1, h2⟩ := h
  have inv : ∀ s ∈ S, ∃ u, 1 - u * s ∈ P := fun s hs => by
    obtain ⟨u, p, hp, e⟩ := hP.exists_inv (hS s hs)
    exact ⟨u, by rw [← e]; simpa using hp⟩
  obtain ⟨s, hs, hsx⟩ : x ∈ locS S M := hM ▸ locBasic_le_locS S M' hx
  refine ⟨s • x, hsx, fun y hy => ?_, fun r => ⟨fun hr => ?_, fun hr => ⟨M.smul_mem r hsx, ?_⟩⟩⟩
  · obtain ⟨t, ht, hty⟩ : y ∈ locS S M' := hM.symm ▸ locBasic_le_locS S M hy
    obtain ⟨a, ha⟩ := h1 _ hty
    obtain ⟨u, hu⟩ := inv _ (S.mul_mem ht hs)
    obtain ⟨t', ht', hu'⟩ := hPI _ hu
    refine ⟨u * a, M.sub_mem hy (M.smul_mem _ hsx), t' * t, S.mul_mem ht' ht, ?_⟩
    have : (t' * t) • (y - (u * a) • s • x) =
        t' • (t • y - a • x) + a • ((t' * (1 - u * (t * s))) • x) := by module
    rw [this]
    exact L'.add_mem (L'.smul_mem _ ha) (L'.smul_mem _ ((h2 _).2 hu'))
  · obtain ⟨t, ht, htx⟩ := hr.2
    rw [smul_smul, smul_smul, h2] at htx
    have := hIP htx
    rcases hP.isPrime.mem_or_mem this with h | h
    · exact (hP.isPrime.mem_or_mem h).resolve_left (hS t ht)
    · exact absurd h (hS s hs)
  · obtain ⟨t, ht, htr⟩ := hPI r hr
    refine ⟨t, ht, ?_⟩
    rw [smul_smul, smul_smul, h2]
    exact I.mul_mem_right _ htr

/- English proof (translation)
Establish `he : ∀ P ∈ s, ∃ e : R, e ∉ P ∧ ∀ Q ∈ s, Q ≠ P → e ∈ Q`. Introduce `P hP`. Establish `: ¬ ((s.erase P).inf id ≤ P)`. Introduce `hle`. Take `⟨Q, hQ, hQP⟩` from `((hs P hP).isPrime.inf_le').1 hle`.

Rewrite `hQ` using `[Finset.mem_erase]`. Conclude with `hQ.1 ((hs Q hQ.2).eq_of_le (hs P hP).ne_top hQP)`. Take `⟨e, h1, h2⟩` from `SetLike.not_le_iff_exists.1 this`. Conclude with `⟨e, h2, fun Q hQ hne => (Finset.inf_le (f := id) (Finset.mem_erase.2 ⟨hne, hQ⟩)) h1⟩`. Use `choose! e he1 he2 using he`.

Establish `hy : ∀ P ∈ s, ∃ y ∈ A, e P • y ∉ B` using `fun P hP => hn P hP _ (he1 P hP)`. Use `choose! y hy1 hy2 using hy`. Establish `hxA : ∑ P ∈ s, e P • y P ∈ A` using `A.sum_mem fun P hP => A.smul_mem _ (hy1 P hP)`. Use `⟨_, hxA, fun r => ⟨fun hr P hP => ?_, fun hr => hk r hr _ hxA⟩⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hrP`.

Establish `h1 : (e P * r) • ∑ Q ∈ s, e Q • y Q ∈ B` using `by rw [mul_smul]; exact B.smul_mem _ hr`. Rewrite `h1` using `[← Finset.add_sum_erase s _ hP, smul_add]`. Establish `h2 : (e P * r) • ∑ Q ∈ s.erase P, e Q • y Q ∈ B`. Rewrite using `[Finset.smul_sum]`. Use `B.sum_mem fun Q hQ => ?_` and prove the remaining obligations.

Rewrite `hQ` using `[Finset.mem_erase]`. Rewrite using `[smul_smul]`. Use `hk _ (fun P' hP' => ?_) _ (hy1 Q hQ.2)` and prove the remaining obligations. Distinguish the cases in `h : P' = P`. Substitute `h` using the available equality.

Conclude with `P'.mul_mem_left _ (he2 Q hQ.2 P' hP' (Ne.symm hQ.1))`. Conclude with `P'.mul_mem_right _ (P'.mul_mem_right _ (he2 P hP P' hP' h))`. Establish `h3 : (e P * r) • e P • y P ∈ B` using `by simpa using B.sub_mem h1 h2`. Establish `h4 : e P * r ∉ P` using `fun h => ((hs P hP).isPrime.mem_or_mem h).elim (he1 P hP) hrP`. Take `⟨u, p, hp, hu⟩` from `(hs P hP).exists_inv h4`.

Apply `hy2 P hP` to reduce the goal to its premises. Establish `: e P • y P = u • ((e P * r) • e P • y P) + (p * e P) • y P`. Rewrite using `[smul_smul u, mul_smul p, ← add_smul, hu, one_smul]`. Rewrite using `[this]`. Use `B.add_mem (B.smul_mem _ h3) (hk _ (fun P' hP' => ?_) _ (hy1 P hP))` and prove the remaining obligations.

Distinguish the cases in `h : P' = P`. Substitute `h` using the available equality. Conclude with `P'.mul_mem_right _ hp`. Conclude with `P'.mul_mem_left _ (he2 P hP P' hP' h)`.
-/
theorem exists_ann {A B : Submodule R W} (s : Finset (Ideal R)) (hs : ∀ P ∈ s, P.IsMaximal)
    (hk : ∀ r : R, (∀ P ∈ s, r ∈ P) → ∀ y ∈ A, r • y ∈ B)
    (hn : ∀ P ∈ s, ∀ r : R, r ∉ P → ∃ y ∈ A, r • y ∉ B) :
    ∃ x ∈ A, ∀ r : R, r • x ∈ B ↔ ∀ P ∈ s, r ∈ P := by
  have he : ∀ P ∈ s, ∃ e : R, e ∉ P ∧ ∀ Q ∈ s, Q ≠ P → e ∈ Q := by
    intro P hP
    have : ¬ ((s.erase P).inf id ≤ P) := by
      intro hle
      obtain ⟨Q, hQ, hQP⟩ := ((hs P hP).isPrime.inf_le').1 hle
      rw [Finset.mem_erase] at hQ
      exact hQ.1 ((hs Q hQ.2).eq_of_le (hs P hP).ne_top hQP)
    obtain ⟨e, h1, h2⟩ := SetLike.not_le_iff_exists.1 this
    exact ⟨e, h2, fun Q hQ hne => (Finset.inf_le (f := id) (Finset.mem_erase.2 ⟨hne, hQ⟩)) h1⟩
  choose! e he1 he2 using he
  have hy : ∀ P ∈ s, ∃ y ∈ A, e P • y ∉ B := fun P hP => hn P hP _ (he1 P hP)
  choose! y hy1 hy2 using hy
  have hxA : ∑ P ∈ s, e P • y P ∈ A := A.sum_mem fun P hP => A.smul_mem _ (hy1 P hP)
  refine ⟨_, hxA, fun r => ⟨fun hr P hP => ?_, fun hr => hk r hr _ hxA⟩⟩
  by_contra hrP
  have h1 : (e P * r) • ∑ Q ∈ s, e Q • y Q ∈ B := by rw [mul_smul]; exact B.smul_mem _ hr
  rw [← Finset.add_sum_erase s _ hP, smul_add] at h1
  have h2 : (e P * r) • ∑ Q ∈ s.erase P, e Q • y Q ∈ B := by
    rw [Finset.smul_sum]
    refine B.sum_mem fun Q hQ => ?_
    rw [Finset.mem_erase] at hQ
    rw [smul_smul]
    refine hk _ (fun P' hP' => ?_) _ (hy1 Q hQ.2)
    by_cases h : P' = P
    · subst h
      exact P'.mul_mem_left _ (he2 Q hQ.2 P' hP' (Ne.symm hQ.1))
    · exact P'.mul_mem_right _ (P'.mul_mem_right _ (he2 P hP P' hP' h))
  have h3 : (e P * r) • e P • y P ∈ B := by simpa using B.sub_mem h1 h2
  have h4 : e P * r ∉ P := fun h => ((hs P hP).isPrime.mem_or_mem h).elim (he1 P hP) hrP
  obtain ⟨u, p, hp, hu⟩ := (hs P hP).exists_inv h4
  apply hy2 P hP
  have : e P • y P = u • ((e P * r) • e P • y P) + (p * e P) • y P := by
    rw [smul_smul u, mul_smul p, ← add_smul, hu, one_smul]
  rw [this]
  refine B.add_mem (B.smul_mem _ h3) (hk _ (fun P' hP' => ?_) _ (hy1 P hP))
  by_cases h : P' = P
  · subst h
    exact P'.mul_mem_right _ hp
  · exact P'.mul_mem_left _ (he2 P hP P' hP' h)

end General

section Primes

variable {K : Type} [Field K] [NumberField K] [StarRing K]

noncomputable abbrev cj : 𝓞 K →+* 𝓞 K := locBasic_sigma (genusCovol_hinj (K := K)) star_algebraMap_ringOfIntegers_mem_range

/- English proof (translation)
The claim follows from `genusCovol_hinj (by rw [locBasic_sigma_spec, locBasic_sigma_spec, star_star])`.
-/
theorem cj_cj (r : 𝓞 K) : cj (cj r) = r := genusCovol_hinj (by
  rw [locBasic_sigma_spec, locBasic_sigma_spec, star_star])

/- English proof (translation)
Rewrite using `[locBasic_conj_eq genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range, Ideal.mem_comap]`.
-/
theorem mem_conj {P : Ideal (𝓞 K)} {r : 𝓞 K} : r ∈ conjIdeal (K := K) P ↔ cj r ∈ P := by
  rw [locBasic_conj_eq genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range, Ideal.mem_comap]

/- English proof (translation)
Use extensionality with `r`. Rewrite using `[mem_conj, mem_conj, cj_cj]`.
-/
theorem conj_conj (P : Ideal (𝓞 K)) : conjIdeal (K := K) (conjIdeal (K := K) P) = P := by
  ext r
  rw [mem_conj, mem_conj, cj_cj]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `r hr`. Rewrite using `[← cj_cj r]`. Conclude with `Ideal.mem_map_of_mem _ (mem_conj.1 hr)`. Rewrite using `[Ideal.map_le_iff_le_comap]`.

Introduce `r hr`. Rewrite using `[Ideal.mem_comap, mem_conj, cj_cj]`. Conclude with `hr`.
-/
theorem conj_eq_map (P : Ideal (𝓞 K)) : conjIdeal (K := K) P = P.map cj := by
  apply le_antisymm
  · intro r hr
    rw [← cj_cj r]
    exact Ideal.mem_map_of_mem _ (mem_conj.1 hr)
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, mem_conj, cj_cj]
    exact hr

/- English proof (translation)
Introduce `_ hr` and use `mem_conj.2 (h (mem_conj.1 hr))`.
-/
theorem conj_mono {P Q : Ideal (𝓞 K)} (h : P ≤ Q) : conjIdeal (K := K) P ≤ conjIdeal (K := K) Q :=
  fun _ hr => mem_conj.2 (h (mem_conj.1 hr))

/- English proof (translation)
Rewrite using `[locBasic_conj_eq genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range]`. Conclude with `Ideal.comap_isMaximal_of_surjective _ (Function.Involutive.surjective cj_cj)`.
-/
theorem conj_isMaximal {P : Ideal (𝓞 K)} (hP : P.IsMaximal) : (conjIdeal (K := K) P).IsMaximal := by
  rw [locBasic_conj_eq genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range]
  exact Ideal.comap_isMaximal_of_surjective _ (Function.Involutive.surjective cj_cj)

/- English proof (translation)
Simplify using `only [conj_eq_map]`. Conclude with `map_prod (Ideal.mapHom cj) _ s`.
-/
theorem conj_prod (s : Finset (Ideal (𝓞 K))) :
    conjIdeal (K := K) (∏ P ∈ s, P) = ∏ P ∈ s, conjIdeal (K := K) P := by
  simp only [conj_eq_map]
  exact map_prod (Ideal.mapHom cj) _ s

/- English proof (translation)
Establish `key : ∀ (Q : Ideal (𝓞 K)) (s : 𝓞 K), (∀ t : 𝓞 K, algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K s) → t ∉ Q) ↔ cj s ∉ Q`. Introduce `Q s`. Prove the components needed by the constructor for the conclusion. Introduce `H`. Conclude with `H _ (locBasic_sigma_spec _ _ s)`.

Introduce `H t e`. Establish `: t = cj s` using `genusCovol_hinj (by rw [locBasic_sigma_spec, e])`. Rewrite using `[this]` and apply the resulting hypothesis. Unfold `hcompl`. Use `congr 1`.

Use extensionality with `s`. Rewrite using `[Set.mem_setOf_eq, Set.mem_setOf_eq, key, key, mem_conj, mem_conj, cj_cj]`. Conclude with `and_comm`.
-/
theorem hcompl_conj (P : Ideal (𝓞 K)) :
    hcompl (K := K) (conjIdeal (K := K) P) = hcompl (K := K) P := by
  have key : ∀ (Q : Ideal (𝓞 K)) (s : 𝓞 K),
      (∀ t : 𝓞 K, algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K s) → t ∉ Q) ↔ cj s ∉ Q := by
    intro Q s
    constructor
    · intro H; exact H _ (locBasic_sigma_spec _ _ s)
    · intro H t e
      have : t = cj s := genusCovol_hinj (by rw [locBasic_sigma_spec, e])
      rwa [this]
  unfold hcompl
  congr 1
  ext s
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, key, key, mem_conj, mem_conj, cj_cj]
  exact and_comm

/- English proof (translation)
Introduce `e`. Take `⟨θ, t, ht, hθ⟩` from `hK.2.2 P hP`. Establish `ht' : t = cj θ` using `genusCovol_hinj (by rw [locBasic_sigma_spec, ht])`. Establish `hc : Nat.card (𝓞 K ⧸ P) = T` using `by rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Establish `: Finite (𝓞 K ⧸ P)` using `Nat.finite_of_card_ne_zero (hc ▸ hT.ne_zero)`.

Use `letI := Fintype.ofFinite (𝓞 K ⧸ P)`. Set `φ` to `ZMod.ringEquivOfPrime (𝓞 K ⧸ P) hT (by rw [← hc, Nat.card_eq_fintype_card])`. Take `⟨z, hz⟩` from `φ.surjective (Ideal.Quotient.mk P θ)`. Take `⟨n, rfl⟩` from `ZMod.intCast_surjective z`. Rewrite `hz` using `[map_intCast, ← map_intCast (Ideal.Quotient.mk P), eq_comm, Ideal.Quotient.eq]`.

Establish `h2 : cj (θ - (n : 𝓞 K)) ∈ P` using `by rw [← mem_conj, e]; exact hz`. Rewrite `h2` using `[map_sub, map_intCast, ← ht']`. Apply `hθ` to reduce the goal to its premises. Simplify using `using P.sub_mem hz h2`.
-/
theorem conj_ne (hK : IsCMUnram K) {T : ℕ} (hT : T.Prime) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hN : Ideal.absNorm P = T) : conjIdeal (K := K) P ≠ P := by
  intro e
  obtain ⟨θ, t, ht, hθ⟩ := hK.2.2 P hP
  have ht' : t = cj θ := genusCovol_hinj (by rw [locBasic_sigma_spec, ht])
  have hc : Nat.card (𝓞 K ⧸ P) = T := by rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have : Finite (𝓞 K ⧸ P) := Nat.finite_of_card_ne_zero (hc ▸ hT.ne_zero)
  letI := Fintype.ofFinite (𝓞 K ⧸ P)
  let φ := ZMod.ringEquivOfPrime (𝓞 K ⧸ P) hT (by rw [← hc, Nat.card_eq_fintype_card])
  obtain ⟨z, hz⟩ := φ.surjective (Ideal.Quotient.mk P θ)
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective z
  rw [map_intCast, ← map_intCast (Ideal.Quotient.mk P), eq_comm, Ideal.Quotient.eq] at hz
  have h2 : cj (θ - (n : 𝓞 K)) ∈ P := by rw [← mem_conj, e]; exact hz
  rw [map_sub, map_intCast, ← ht'] at h2
  apply hθ
  simpa using P.sub_mem hz h2

omit [StarRing K] in

/- English proof (translation)
Establish `h0 : Ideal.span {(T : 𝓞 K)} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hT.ne_zero` after adjusting the coercions. Establish `hmax : ∀ P : Ideal (𝓞 K), P.IsPrime → (T : 𝓞 K) ∈ P → P.IsMaximal` using `fun P hP hTP => hP.isMaximal (by rintro rfl; exact hT.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hTP)))`. Establish `hsq : Squarefree (Ideal.span {(T : 𝓞 K)})`.

Rewrite using `[squarefree_iff_no_irreducibles h0]`. Introduce `P hP hd`. Establish `hP' : P.IsPrime` using `Ideal.isPrime_of_prime (UniqueFactorizationMonoid.irreducible_iff_prime.1 hP)`. Rewrite `hd` using `[Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]`. Establish `hTP : (T : 𝓞 K) ∈ P` using `Ideal.mul_le_left hd`.

Conclude with `(H P (hmax P hP' hTP) hTP).2 (by rwa [pow_two])`. Establish `hnd` using `(UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0).1 hsq`. Set `S : Finset (Ideal (𝓞 K))` to `⟨_, hnd⟩`. Establish `hm : ∀ P, P ∈ S ↔ P.IsMaximal ∧ (T : 𝓞 K) ∈ P` using `fun P => by`. Express the relevant statement in the definitionally equal form `P ∈ UniqueFactorizationMonoid.normalizedFactors _ ↔ _`.

Rewrite using `[Ideal.mem_normalizedFactors_iff h0, Ideal.span_singleton_le_iff_mem]`. Conclude with `⟨fun h => ⟨hmax P h.1 h.2, h.2⟩, fun h => ⟨h.1.isPrime, h.2⟩⟩`. Establish `hp : ∏ P ∈ S, P = Ideal.span {(T : 𝓞 K)}`. Rewrite using `[Finset.prod_eq_multiset_prod, Multiset.map_id']`. Conclude with `Ideal.prod_normalizedFactors_eq_self h0`.

Use `⟨S, hm, hp, ?_⟩` and prove the remaining obligations. Use `congrArg Ideal.absNorm hp` as an intermediate fact. Rewrite `this` using `[map_prod, Finset.prod_congr rfl (fun P hP => (H P ((hm P).1 hP).1 ((hm P).1 hP).2).1), Finset.prod_const, Ideal.absNorm_span_natCast, RingOfIntegers.rank]`. Conclude with `Nat.pow_right_injective hT.two_le this`.
-/
theorem exists_primes {T : ℕ} (hT : T.Prime)
    (H : ∀ P : Ideal (𝓞 K), P.IsMaximal → (T : 𝓞 K) ∈ P → Ideal.absNorm P = T ∧ (T : 𝓞 K) ∉ P ^ 2) :
    ∃ S : Finset (Ideal (𝓞 K)), (∀ P, P ∈ S ↔ P.IsMaximal ∧ (T : 𝓞 K) ∈ P) ∧
      ∏ P ∈ S, P = Ideal.span {(T : 𝓞 K)} ∧ S.card = Module.finrank ℚ K := by
  have h0 : Ideal.span {(T : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hT.ne_zero
  have hmax : ∀ P : Ideal (𝓞 K), P.IsPrime → (T : 𝓞 K) ∈ P → P.IsMaximal := fun P hP hTP =>
    hP.isMaximal (by rintro rfl; exact hT.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hTP)))
  have hsq : Squarefree (Ideal.span {(T : 𝓞 K)}) := by
    rw [squarefree_iff_no_irreducibles h0]
    intro P hP hd
    have hP' : P.IsPrime := Ideal.isPrime_of_prime (UniqueFactorizationMonoid.irreducible_iff_prime.1 hP)
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem] at hd
    have hTP : (T : 𝓞 K) ∈ P := Ideal.mul_le_left hd
    exact (H P (hmax P hP' hTP) hTP).2 (by rwa [pow_two])
  have hnd := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0).1 hsq
  let S : Finset (Ideal (𝓞 K)) := ⟨_, hnd⟩
  have hm : ∀ P, P ∈ S ↔ P.IsMaximal ∧ (T : 𝓞 K) ∈ P := fun P => by
    change P ∈ UniqueFactorizationMonoid.normalizedFactors _ ↔ _
    rw [Ideal.mem_normalizedFactors_iff h0, Ideal.span_singleton_le_iff_mem]
    exact ⟨fun h => ⟨hmax P h.1 h.2, h.2⟩, fun h => ⟨h.1.isPrime, h.2⟩⟩
  have hp : ∏ P ∈ S, P = Ideal.span {(T : 𝓞 K)} := by
    rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
    exact Ideal.prod_normalizedFactors_eq_self h0
  refine ⟨S, hm, hp, ?_⟩
  have := congrArg Ideal.absNorm hp
  rw [map_prod, Finset.prod_congr rfl (fun P hP => (H P ((hm P).1 hP).1 ((hm P).1 hP).2).1),
    Finset.prod_const, Ideal.absNorm_span_natCast, RingOfIntegers.rank] at this
  exact Nat.pow_right_injective hT.two_le this

/- English proof (translation)
Take `⟨S, hm, hp, hc⟩` from `exists_primes hT H`. Set `e : Ideal (𝓞 K) ↪ Cardinal` to `embeddingToCardinal`. Set `s` to `S.filter fun P => e P < e (conjIdeal (K := K) P)`. Establish `hS : ∀ P ∈ S, conjIdeal (K` using `K) P ∈ S := fun P hP => (hm _).2 ⟨conj_isMaximal ((hm P).1 hP).1, mem_conj.2 (by rw [map_natCast]; exact ((hm P).1 hP).2)⟩`. Establish `hinj : Function.Injective (conjIdeal (K` using `K) (R := 𝓞 K)) := Function.Involutive.injective conj_conj`.

Establish `him : s.image (conjIdeal (K` using `K)) = S.filter fun P => ¬ e P < e (conjIdeal (K := K) P) := by`. Use extensionality with `P`. Simplify using `only [s, Finset.mem_image, Finset.mem_filter]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨Q, ⟨hQ, hlt⟩, rfl⟩`.

Conclude with `⟨hS Q hQ, by rw [conj_conj]; exact hlt.not_gt⟩`. Introduce and unpack `⟨hP, hlt⟩`. Use `⟨_, ⟨hS P hP, ?_⟩, conj_conj P⟩` and prove the remaining obligations. Rewrite using `[conj_conj]`. Establish `h1` using `(hm P).1 hP`.

Conclude with `lt_of_le_of_ne (not_lt.1 hlt) fun h => conj_ne hK hT h1.1 (H P h1.1 h1.2).1 (e.injective h)`. Establish `hsm : ∀ P ∈ s, P.IsMaximal` using `fun P hP => ((hm P).1 (Finset.mem_filter.1 hP).1).1`. Use `⟨s, ?_, fun P hP => ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `Finset.card_filter_add_card_filter_not (s := S) fun P => e P < e (conjIdeal (K := K) P)`. Rewrite `h1` using `[← him, Finset.card_image_of_injective _ hinj, hc]`.

Use `hK.1` as an intermediate fact. Establish `h2` using `IsTotallyComplex.finrank (K := K)`. Establish `h3` using `InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K`. Establish `h4` using `IsTotallyComplex.nrRealPlaces_eq_zero (K := K)`. Express the relevant statement in the definitionally equal form `s.card + s.card = _ at h1`.

Unfold `fDeg`. Use linear arithmetic over natural numbers and integers. Establish `h1` using `(hm P).1 (Finset.mem_filter.1 hP).1`. Conclude with `⟨h1.1, (H P h1.1 h1.2).1⟩`. Rewrite using `[conj_prod]`.

Use `IsCoprime.prod_left fun P hP => IsCoprime.prod_right fun Q hQ => ?_` and prove the remaining obligations. Use `Ideal.isCoprime_iff_sup_eq.2 ((hsm P hP).coprime_of_ne (conj_isMaximal (hsm Q hQ)) ?_)` and prove the remaining obligations. Introduce and unpack `rfl`. Establish `h1` using `(Finset.mem_filter.1 hP).2`. Rewrite `h1` using `[conj_conj]`.

Conclude with `h1.not_gt (Finset.mem_filter.1 hQ).2`. Rewrite using `[conj_prod, ← hp, ← Finset.prod_filter_mul_prod_filter_not S (fun P => e P < e (conjIdeal (K := K) P)), ← him, Finset.prod_image (fun _ _ _ _ h => hinj h)]`.
-/
theorem exists_half (hK : IsCMUnram K) {T : ℕ} (hT : T.Prime)
    (H : ∀ P : Ideal (𝓞 K), P.IsMaximal → (T : 𝓞 K) ∈ P → Ideal.absNorm P = T ∧ (T : 𝓞 K) ∉ P ^ 2) :
    ∃ s : Finset (Ideal (𝓞 K)), s.card = fDeg K ∧ (∀ P ∈ s, P.IsMaximal ∧ Ideal.absNorm P = T) ∧
      IsCoprime (∏ P ∈ s, P) (conjIdeal (K := K) (∏ P ∈ s, P)) ∧
      (∏ P ∈ s, P) * conjIdeal (K := K) (∏ P ∈ s, P) = Ideal.span {(T : 𝓞 K)} := by
  obtain ⟨S, hm, hp, hc⟩ := exists_primes hT H
  let e : Ideal (𝓞 K) ↪ Cardinal := embeddingToCardinal
  let s := S.filter fun P => e P < e (conjIdeal (K := K) P)
  have hS : ∀ P ∈ S, conjIdeal (K := K) P ∈ S := fun P hP =>
    (hm _).2 ⟨conj_isMaximal ((hm P).1 hP).1, mem_conj.2 (by rw [map_natCast]; exact ((hm P).1 hP).2)⟩
  have hinj : Function.Injective (conjIdeal (K := K) (R := 𝓞 K)) :=
    Function.Involutive.injective conj_conj
  have him : s.image (conjIdeal (K := K)) = S.filter fun P => ¬ e P < e (conjIdeal (K := K) P) := by
    ext P
    simp only [s, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨Q, ⟨hQ, hlt⟩, rfl⟩
      exact ⟨hS Q hQ, by rw [conj_conj]; exact hlt.not_gt⟩
    · rintro ⟨hP, hlt⟩
      refine ⟨_, ⟨hS P hP, ?_⟩, conj_conj P⟩
      rw [conj_conj]
      have h1 := (hm P).1 hP
      exact lt_of_le_of_ne (not_lt.1 hlt) fun h => conj_ne hK hT h1.1 (H P h1.1 h1.2).1 (e.injective h)
  have hsm : ∀ P ∈ s, P.IsMaximal := fun P hP => ((hm P).1 (Finset.mem_filter.1 hP).1).1
  refine ⟨s, ?_, fun P hP => ?_, ?_, ?_⟩
  · have h1 := Finset.card_filter_add_card_filter_not (s := S) fun P => e P < e (conjIdeal (K := K) P)
    rw [← him, Finset.card_image_of_injective _ hinj, hc] at h1
    have := hK.1
    have h2 := IsTotallyComplex.finrank (K := K)
    have h3 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
    have h4 := IsTotallyComplex.nrRealPlaces_eq_zero (K := K)
    change s.card + s.card = _ at h1
    unfold fDeg
    omega
  · have h1 := (hm P).1 (Finset.mem_filter.1 hP).1
    exact ⟨h1.1, (H P h1.1 h1.2).1⟩
  · rw [conj_prod]
    refine IsCoprime.prod_left fun P hP => IsCoprime.prod_right fun Q hQ => ?_
    refine Ideal.isCoprime_iff_sup_eq.2 ((hsm P hP).coprime_of_ne (conj_isMaximal (hsm Q hQ)) ?_)
    rintro rfl
    have h1 := (Finset.mem_filter.1 hP).2
    rw [conj_conj] at h1
    exact h1.not_gt (Finset.mem_filter.1 hQ).2
  · rw [conj_prod, ← hp, ← Finset.prod_filter_mul_prod_filter_not S (fun P => e P < e (conjIdeal (K := K) P)),
      ← him, Finset.prod_image (fun _ _ _ _ h => hinj h)]

end Primes

section Lattices

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [NumberField K] [FiniteDimensional K V] in
/- English proof (translation)
Take `⟨x, hx, h1, h2⟩` from `H`. Establish `hg : ∀ (r : 𝓞 K) (v : V), g.symm (r • v) = r • g.symm v` using `fun r v => LinearMapClass.map_smul_of_tower g.symm r v`. Use `⟨g x, ?_, fun y hy => ?_, fun r => ?_⟩` and prove the remaining obligations. Rewrite using `[isomAct_mem_gmap]`. Simplify using `using hx`.

Rewrite `hy` using `[isomAct_mem_gmap]`. Take `⟨a, ha⟩` from `h1 _ hy`. Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[isomAct_mem_gmap, map_sub, hg]`. Simplify using `using ha`.

Rewrite using `[isomAct_mem_gmap, hg, ← h2]`. Simplify using the standard rewrite rules.
-/
theorem Cyc.gmap {A B : Submodule (𝓞 K) V} {I : Ideal (𝓞 K)} (H : Cyc A B I) (g : V ≃ₗ[K] V) :
    Cyc (gmap g A) (gmap g B) I := by
  obtain ⟨x, hx, h1, h2⟩ := H
  have hg : ∀ (r : 𝓞 K) (v : V), g.symm (r • v) = r • g.symm v := fun r v =>
    LinearMapClass.map_smul_of_tower g.symm r v
  refine ⟨g x, ?_, fun y hy => ?_, fun r => ?_⟩
  · rw [isomAct_mem_gmap]; simpa using hx
  · rw [isomAct_mem_gmap] at hy
    obtain ⟨a, ha⟩ := h1 _ hy
    refine ⟨a, ?_⟩
    rw [isomAct_mem_gmap, map_sub, hg]
    simpa using ha
  · rw [isomAct_mem_gmap, hg, ← h2]
    simp

omit [NumberField K] [FiniteDimensional K V] in

/- English proof (translation)
Establish `hg : ∀ (r : 𝓞 K) (v : V), g.symm (r • v) = r • g.symm v` using `fun r v => LinearMapClass.map_smul_of_tower g.symm r v`. Substitute `hA hB` using the available equality. Prove the components needed by the constructor for the conclusion. Introduce `H y hy`. Rewrite `hy`, the goal using `[isomAct_mem_gmap]`.

Rewrite using `[hg]`. Conclude with `H _ hy`. Introduce `H y hy`. Use `H (g y) (by rw [isomAct_mem_gmap]; simpa using hy)` as an intermediate fact. Rewrite `this` using `[isomAct_mem_gmap, hg]`.

Simplify using `using this`.
-/
theorem transfer (g : V ≃ₗ[K] V) {A B A' B' : Submodule (𝓞 K) V} (hA : gmap g A = A') (hB : gmap g B = B')
    (r : 𝓞 K) : (∀ y ∈ A, r • y ∈ B) ↔ ∀ y ∈ A', r • y ∈ B' := by
  have hg : ∀ (r : 𝓞 K) (v : V), g.symm (r • v) = r • g.symm v := fun r v =>
    LinearMapClass.map_smul_of_tower g.symm r v
  subst hA hB
  constructor
  · intro H y hy
    rw [isomAct_mem_gmap] at hy ⊢
    rw [hg]
    exact H _ hy
  · intro H y hy
    have := H (g y) (by rw [isomAct_mem_gmap]; simpa using hy)
    rw [isomAct_mem_gmap, hg] at this
    simpa using this

/- English proof (translation)
Introduce and unpack `y ⟨s, hs, hy⟩`. Conclude with `⟨s, hs, by rw [smul_comm]; exact H _ hy⟩`.
-/
theorem smul_loc {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (S : Submonoid R)
    {A B : Submodule R W} {r : R} (H : ∀ y ∈ A, r • y ∈ B) : ∀ y ∈ locS S A, r • y ∈ locS S B := by
  rintro y ⟨s, hs, hy⟩
  exact ⟨s, hs, by rw [smul_comm]; exact H _ hy⟩

variable (h : V →ₗ⋆[K] V →ₗ[K] K) (hK : IsCMUnram K) (hs : h.IsSymm) (hn : h.Nondegenerate)
include hK hs hn

/- English proof (translation)
Take `⟨h0, -, -, hg, -⟩` from `DiscOrder.main K V h hK hs hn L hL`. Take `⟨hNi, hd⟩` from `hg N hN`. Use `⟨hNi, ?_⟩` and prove the remaining obligations. Establish `ld` using `locDual (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range`. Establish `hc` using `cyc_of_equiv eL`.

Establish `hinf : ∀ r : 𝓞 K, (∀ P ∈ S, r ∈ P) ↔ r ∈ Ideal.span {T}`. Introduce `r`. Rewrite using `[← hp, Ideal.prod_eq_iInf_of_pairwise_isCoprime]`. Simplify using the standard rewrite rules. Introduce `P hP Q hQ hne`.

Conclude with `Ideal.isCoprime_iff_sup_eq.2 ((hS P hP).coprime_of_ne (hS Q hQ) hne)`. Establish `tr : ∀ P : Ideal (𝓞 K), P.IsMaximal → ∀ r : 𝓞 K, (∀ y ∈ loc (K` using `K) P (dual h L), r • y ∈ loc (K := K) P L) ↔ ∀ y ∈ loc (K := K) P (dual h N), r • y ∈ loc (K := K) P N := by`. Introduce `P hP r`. Take `⟨g, hg, hgL⟩` from `hN.2 P hP`. Use `transfer g ?_ hgL r` and prove the remaining obligations.

Take `⟨a1, a2, -, -, a5⟩` from `isomAct (𝓞 K) K V h g hg L`. Establish `b1` using `(ld (gmap g L) (a5.2 hL.1).fg).1 P hP.isPrime`. Establish `b2` using `(ld N hN.1.fg).1 P hP.isPrime`. Rewrite using `[b2.1, ← b2.2, ← hgL, ← a2 P, b1.2, ← b1.1, a1, (isomAct (𝓞 K) K V h g hg (dual h L)).2.1 P]`. Take `⟨x, hx, hxa⟩` from `exists_ann (A := dual h N) (B := N) S hS (fun r hr y hy => genusBasic_lg (K := K) N _ fun P hP => (tr P hP r).1 (smul_loc _ fun z hz => hc.smul_mem ((hinf r).1 hr) hz) y (locBasic_le_locS _ _ hy)) (fun P hP r hr => by`.

Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Take `⟨z, hz, -, hz2⟩` from `hc`. Take `⟨t, ht, htz⟩` from `(tr P (hS P hP) r).2 (smul_loc _ hcon) z (locBasic_le_locS _ _ hz)`. Rewrite `htz` using `[smul_smul, hz2, ← hinf]`.

Conclude with `((hS P hP).isPrime.mem_or_mem (htz P hP)).elim (genusBasic_hS P (hS P hP) t ht) hr)`. Take `⟨f, hf, -⟩` from `exists_inj x hx (I := Ideal.span {T}) fun r => (hxa r).trans (hinf r)`. Establish `c1 : Nat.card (↥(dual h N) ⧸ N.comap (dual h N).subtype) = Nat.card (𝓞 K ⧸ Ideal.span {T})`. Rewrite using `[← Nat.card_congr eL.toEquiv]`. Conclude with `hd`.

Establish `: Finite (↥(dual h N) ⧸ N.comap (dual h N).subtype)` using `Nat.finite_of_card_ne_zero (by`. Express the relevant statement in the definitionally equal form `discN h N ≠ 0`. Rewrite using `[hd])` and apply the resulting hypothesis. Conclude with `⟨(LinearEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).2 ⟨hf, c1.symm⟩)).symm⟩`.
-/
theorem forward (T : 𝓞 K) (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, P.IsMaximal)
    (hp : ∏ P ∈ S, P = Ideal.span {T}) (L N : Submodule (𝓞 K) V) (hL : IsIntLat h L)
    (eL : (↥(dual h L) ⧸ L.comap (dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {T}))
    (hN : N ∈ genus h L) :
    IsIntLat h N ∧ Nonempty ((↥(dual h N) ⧸ N.comap (dual h N).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {T})) := by
  obtain ⟨h0, -, -, hg, -⟩ := DiscOrder.main K V h hK hs hn L hL
  obtain ⟨hNi, hd⟩ := hg N hN
  refine ⟨hNi, ?_⟩
  have ld := locDual (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range
  have hc := cyc_of_equiv eL
  have hinf : ∀ r : 𝓞 K, (∀ P ∈ S, r ∈ P) ↔ r ∈ Ideal.span {T} := by
    intro r
    rw [← hp, Ideal.prod_eq_iInf_of_pairwise_isCoprime]
    · simp
    · intro P hP Q hQ hne
      exact Ideal.isCoprime_iff_sup_eq.2 ((hS P hP).coprime_of_ne (hS Q hQ) hne)
  have tr : ∀ P : Ideal (𝓞 K), P.IsMaximal → ∀ r : 𝓞 K,
      (∀ y ∈ loc (K := K) P (dual h L), r • y ∈ loc (K := K) P L) ↔
        ∀ y ∈ loc (K := K) P (dual h N), r • y ∈ loc (K := K) P N := by
    intro P hP r
    obtain ⟨g, hg, hgL⟩ := hN.2 P hP
    refine transfer g ?_ hgL r
    obtain ⟨a1, a2, -, -, a5⟩ := isomAct (𝓞 K) K V h g hg L
    have b1 := (ld (gmap g L) (a5.2 hL.1).fg).1 P hP.isPrime
    have b2 := (ld N hN.1.fg).1 P hP.isPrime
    rw [b2.1, ← b2.2, ← hgL, ← a2 P, b1.2, ← b1.1, a1, (isomAct (𝓞 K) K V h g hg (dual h L)).2.1 P]
  obtain ⟨x, hx, hxa⟩ := exists_ann (A := dual h N) (B := N) S hS
    (fun r hr y hy => genusBasic_lg (K := K) N _ fun P hP =>
      (tr P hP r).1 (smul_loc _ fun z hz => hc.smul_mem ((hinf r).1 hr) hz) y (locBasic_le_locS _ _ hy))
    (fun P hP r hr => by
      by_contra hcon
      push Not at hcon
      obtain ⟨z, hz, -, hz2⟩ := hc
      obtain ⟨t, ht, htz⟩ := (tr P (hS P hP) r).2 (smul_loc _ hcon) z (locBasic_le_locS _ _ hz)
      rw [smul_smul, hz2, ← hinf] at htz
      exact ((hS P hP).isPrime.mem_or_mem (htz P hP)).elim (genusBasic_hS P (hS P hP) t ht) hr)
  obtain ⟨f, hf, -⟩ := exists_inj x hx (I := Ideal.span {T}) fun r => (hxa r).trans (hinf r)
  have c1 : Nat.card (↥(dual h N) ⧸ N.comap (dual h N).subtype) = Nat.card (𝓞 K ⧸ Ideal.span {T}) := by
    rw [← Nat.card_congr eL.toEquiv]
    exact hd
  have : Finite (↥(dual h N) ⧸ N.comap (dual h N).subtype) := Nat.finite_of_card_ne_zero (by
    change discN h N ≠ 0
    rwa [hd])
  exact ⟨(LinearEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).2 ⟨hf, c1.symm⟩)).symm⟩

/- English proof (translation)
Establish `ld` using `locDual (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range`. Establish `key : ∀ P ∈ s, ∃ g ∈ isom h, gmap g (loc (K` using `K) P L) = loc (K := K) P N := by`. Introduce `P hPs`. Establish `hP` using `hm P hPs`. Establish `hP'` using `conj_isMaximal hP`.

Establish `u'` using `(ld M' hM'.fg).2.1 uM' P hP`. Take `⟨g, hg, hgM⟩` from `UnimodLoc.exists_isom_of_isUnimodularAt K V h hK hs hn M M' hM hM' P hP ((ld M hM.fg).2.1 uM P hP) u'`. Establish `hle : ∀ Q ∈ s, ∏ P ∈ s, P ≤ Q` using `fun Q hQ => Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun P => P) hQ)`. Establish `hIP` using `hle P hPs`. Establish `hIc : ¬ ∏ P ∈ s, P ≤ conjIdeal (K` using `K) P := fun hle => hP'.ne_top (top_le_iff.1 ((Ideal.isCoprime_iff_sup_eq.1 hco).ge.trans (sup_le hle (conj_mono hIP))))`.

Establish `hne : conjIdeal (K` using `K) P ≠ P := fun e => hIc (hIP.trans e.ge)`. Take `⟨t, ht, htI⟩ : ∃ t ∈ hcompl (K` from `K) P, t ∈ ∏ Q ∈ s.erase P, Q := by`. Establish `c1 : IsCoprime (∏ Q ∈ s.erase P, Q) P` using `IsCoprime.prod_left fun Q hQ => Ideal.isCoprime_iff_sup_eq.2 ((hm Q (Finset.mem_of_mem_erase hQ)).coprime_of_ne hP (Finset.ne_of_mem_erase hQ))`. Establish `c2 : IsCoprime (∏ Q ∈ s.erase P, Q) (conjIdeal (K` using `K) P) := IsCoprime.prod_left fun Q hQ => Ideal.isCoprime_iff_sup_eq.2 ((hm Q (Finset.mem_of_mem_erase hQ)).coprime_of_ne hP' fun e => hIc ((hle Q (Finset.mem_of_mem_erase hQ)).trans e.le))`. Take `⟨a, ha, b, hb, hab⟩` from `Ideal.isCoprime_iff_exists.1 (c1.mul_right c2)`.

Use `⟨a, locBasic_mem_hcompl P a (fun h => hP.ne_top ?_) (fun h => hP'.ne_top ?_), ha⟩` and prove the remaining obligations. Rewrite using `[Ideal.eq_top_iff_one, ← hab]`. Conclude with `P.add_mem h (Ideal.mul_le_inf hb).1`. Rewrite using `[Ideal.eq_top_iff_one, ← hab]`. Conclude with `Ideal.add_mem _ h (Ideal.mul_le_inf hb).2`.

Establish `hPI : ∀ r ∈ P, ∃ t ∈ hcompl (K` using `K) P, t * r ∈ ∏ Q ∈ s, Q := fun r hr => ⟨t, ht, by rw [← Finset.prod_erase_mul s _ hPs]; exact Ideal.mul_mem_mul htI hr⟩`. Establish `a1` using `(isomAct (𝓞 K) K V h g hg M).2.1 P`. Establish `a2` using `(isomAct (𝓞 K) K V h g hg L).2.1 P`. Establish `d1` using `(cL.gmap g).localise hP (hcompl (K := K) P) (genusBasic_hS P hP) hIP hPI (a1.trans hgM)`. Establish `d2` using `cN.localise hP (hcompl (K := K) P) (genusBasic_hS P hP) hIP hPI rfl`.

Take `⟨g', hg', -, hg2⟩` from `GlobalTheory.Mass.Hyperplane.main K V h hK hs hn M' hM' P hP hne u' _ _ inf_le_left inf_le_left (equiv_of_cyc d1) (equiv_of_cyc d2)`. Use `⟨g' * g, (isom h).mul_mem hg' hg, ?_⟩` and prove the remaining obligations. Establish `l1 : loc (K` using `K) P (gmap g L) ≤ loc (K := K) P M' := by`. Rewrite using `[← hgM, ← a1]`. Conclude with `locBasic_locS_mono _ (Submodule.map_mono hLM)`.

Unfold `loc at hg2 l1 a2 ⊢`. Rewrite `hg2` using `[locBasic_locS_inf, locBasic_locS_inf, locBasic_locS_idem, locBasic_locS_idem, inf_eq_right.2 l1, inf_eq_right.2 (locBasic_locS_mono _ hNM)]`. Rewrite using `[genusBasic_gmap_mul, ← a2, hg2]`. Introduce `P hP`. Establish `hP'` using `conj_isMaximal hP`.

Establish `mem : ∀ Q : Ideal (𝓞 K), Q.IsMaximal → ∏ P ∈ s, P ≤ Q → Q ∈ s` using `fun Q hQ hle => by`. Take `⟨Q', hQ', hle'⟩` from `(hQ.isPrime.prod_le).1 hle`. Rewrite using `[← (hm Q' hQ').eq_of_le hQ.ne_top hle']` and apply the resulting hypothesis. Distinguish the cases in `h1 : ∏ P ∈ s, P ≤ P`. Conclude with `key P (mem P hP h1)`.

Distinguish the cases in `h2 : ∏ P ∈ s, P ≤ conjIdeal (K := K) P`. Use `key _ (mem _ hP' h2)` as an intermediate fact. Unfold `loc at this ⊢`. Rewrite `this` using `[hcompl_conj]`. Then use the resulting hypothesis. Take `⟨t, ht, htI⟩ : ∃ t ∈ hcompl (K` from `K) P, t ∈ ∏ Q ∈ s, Q := by`.

Take `⟨a, ha, ha'⟩` from `SetLike.not_le_iff_exists.1 h1`. Take `⟨b, hb, hb'⟩` from `SetLike.not_le_iff_exists.1 h2`. Distinguish the cases in `hac : a ∈ conjIdeal (K := K) P`. Distinguish the cases in `hbp : b ∈ P`. Use `⟨a + b, locBasic_mem_hcompl P _ (fun h => ha' ?_) (fun h => hb' ?_), Ideal.add_mem _ ha hb⟩` and prove the remaining obligations.

Simplify using `using P.sub_mem h hbp`. Simplify using `using (conjIdeal (K := K) P).sub_mem h hac`. Conclude with `⟨b, locBasic_mem_hcompl P _ hbp hb', hb⟩`. Conclude with `⟨a, locBasic_mem_hcompl P _ ha' hac, ha⟩`. Establish `eq : ∀ {A B : Submodule (𝓞 K) V}, B ≤ A → Cyc A B (∏ P ∈ s, P) → loc (K` using `K) P B = loc (K := K) P A := fun hle hc => le_antisymm (locBasic_locS_mono _ hle) ((locBasic_locS_mono _ fun y hy => locBasic_mem_locS.2 ⟨t, ht, hc.smul_mem htI hy⟩).trans (locBasic_locS_idem _ _).le)`.

Rewrite using `[eq hLM cL, eq hNM cN]`. Conclude with `UnimodLoc.exists_isom_of_isUnimodularAt K V h hK hs hn M M' hM hM' P hP ((ld M hM.fg).2.1 uM P hP) ((ld M' hM'.fg).2.1 uM' P hP)`.
-/
theorem backward (s : Finset (Ideal (𝓞 K))) (hm : ∀ P ∈ s, P.IsMaximal)
    (hco : IsCoprime (∏ P ∈ s, P) (conjIdeal (K := K) (∏ P ∈ s, P)))
    (L N M M' : Submodule (𝓞 K) V) (hM : Submodule.IsLattice K M) (hM' : Submodule.IsLattice K M')
    (uM : IsUnimodular h M) (uM' : IsUnimodular h M') (hLM : L ≤ M) (hNM : N ≤ M')
    (cL : Cyc M L (∏ P ∈ s, P)) (cN : Cyc M' N (∏ P ∈ s, P)) : SameGenus h L N := by
  have ld := locDual (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range
  have key : ∀ P ∈ s, ∃ g ∈ isom h, gmap g (loc (K := K) P L) = loc (K := K) P N := by
    intro P hPs
    have hP := hm P hPs
    have hP' := conj_isMaximal hP
    have u' := (ld M' hM'.fg).2.1 uM' P hP
    obtain ⟨g, hg, hgM⟩ := UnimodLoc.exists_isom_of_isUnimodularAt K V h hK hs hn M M' hM hM' P hP
      ((ld M hM.fg).2.1 uM P hP) u'
    have hle : ∀ Q ∈ s, ∏ P ∈ s, P ≤ Q := fun Q hQ => Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun P => P) hQ)
    have hIP := hle P hPs
    have hIc : ¬ ∏ P ∈ s, P ≤ conjIdeal (K := K) P := fun hle =>
      hP'.ne_top (top_le_iff.1 ((Ideal.isCoprime_iff_sup_eq.1 hco).ge.trans (sup_le hle (conj_mono hIP))))
    have hne : conjIdeal (K := K) P ≠ P := fun e => hIc (hIP.trans e.ge)
    obtain ⟨t, ht, htI⟩ : ∃ t ∈ hcompl (K := K) P, t ∈ ∏ Q ∈ s.erase P, Q := by
      have c1 : IsCoprime (∏ Q ∈ s.erase P, Q) P := IsCoprime.prod_left fun Q hQ =>
        Ideal.isCoprime_iff_sup_eq.2 ((hm Q (Finset.mem_of_mem_erase hQ)).coprime_of_ne hP
          (Finset.ne_of_mem_erase hQ))
      have c2 : IsCoprime (∏ Q ∈ s.erase P, Q) (conjIdeal (K := K) P) := IsCoprime.prod_left fun Q hQ =>
        Ideal.isCoprime_iff_sup_eq.2 ((hm Q (Finset.mem_of_mem_erase hQ)).coprime_of_ne hP' fun e =>
          hIc ((hle Q (Finset.mem_of_mem_erase hQ)).trans e.le))
      obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 (c1.mul_right c2)
      refine ⟨a, locBasic_mem_hcompl P a (fun h => hP.ne_top ?_) (fun h => hP'.ne_top ?_), ha⟩
      · rw [Ideal.eq_top_iff_one, ← hab]; exact P.add_mem h (Ideal.mul_le_inf hb).1
      · rw [Ideal.eq_top_iff_one, ← hab]; exact Ideal.add_mem _ h (Ideal.mul_le_inf hb).2
    have hPI : ∀ r ∈ P, ∃ t ∈ hcompl (K := K) P, t * r ∈ ∏ Q ∈ s, Q := fun r hr =>
      ⟨t, ht, by rw [← Finset.prod_erase_mul s _ hPs]; exact Ideal.mul_mem_mul htI hr⟩
    have a1 := (isomAct (𝓞 K) K V h g hg M).2.1 P
    have a2 := (isomAct (𝓞 K) K V h g hg L).2.1 P
    have d1 := (cL.gmap g).localise hP (hcompl (K := K) P) (genusBasic_hS P hP) hIP hPI (a1.trans hgM)
    have d2 := cN.localise hP (hcompl (K := K) P) (genusBasic_hS P hP) hIP hPI rfl
    obtain ⟨g', hg', -, hg2⟩ := GlobalTheory.Mass.Hyperplane.main K V h hK hs hn M' hM' P hP hne u' _ _ inf_le_left inf_le_left
      (equiv_of_cyc d1) (equiv_of_cyc d2)
    refine ⟨g' * g, (isom h).mul_mem hg' hg, ?_⟩
    have l1 : loc (K := K) P (gmap g L) ≤ loc (K := K) P M' := by
      rw [← hgM, ← a1]
      exact locBasic_locS_mono _ (Submodule.map_mono hLM)
    unfold loc at hg2 l1 a2 ⊢
    rw [locBasic_locS_inf, locBasic_locS_inf, locBasic_locS_idem, locBasic_locS_idem, inf_eq_right.2 l1,
      inf_eq_right.2 (locBasic_locS_mono _ hNM)] at hg2
    rw [genusBasic_gmap_mul, ← a2, hg2]
  intro P hP
  have hP' := conj_isMaximal hP
  have mem : ∀ Q : Ideal (𝓞 K), Q.IsMaximal → ∏ P ∈ s, P ≤ Q → Q ∈ s := fun Q hQ hle => by
    obtain ⟨Q', hQ', hle'⟩ := (hQ.isPrime.prod_le).1 hle
    rwa [← (hm Q' hQ').eq_of_le hQ.ne_top hle']
  by_cases h1 : ∏ P ∈ s, P ≤ P
  · exact key P (mem P hP h1)
  by_cases h2 : ∏ P ∈ s, P ≤ conjIdeal (K := K) P
  · have := key _ (mem _ hP' h2)
    unfold loc at this ⊢
    rwa [hcompl_conj] at this
  obtain ⟨t, ht, htI⟩ : ∃ t ∈ hcompl (K := K) P, t ∈ ∏ Q ∈ s, Q := by
    obtain ⟨a, ha, ha'⟩ := SetLike.not_le_iff_exists.1 h1
    obtain ⟨b, hb, hb'⟩ := SetLike.not_le_iff_exists.1 h2
    by_cases hac : a ∈ conjIdeal (K := K) P
    · by_cases hbp : b ∈ P
      · refine ⟨a + b, locBasic_mem_hcompl P _ (fun h => ha' ?_) (fun h => hb' ?_), Ideal.add_mem _ ha hb⟩
        · simpa using P.sub_mem h hbp
        · simpa using (conjIdeal (K := K) P).sub_mem h hac
      · exact ⟨b, locBasic_mem_hcompl P _ hbp hb', hb⟩
    · exact ⟨a, locBasic_mem_hcompl P _ ha' hac, ha⟩
  have eq : ∀ {A B : Submodule (𝓞 K) V}, B ≤ A → Cyc A B (∏ P ∈ s, P) →
      loc (K := K) P B = loc (K := K) P A := fun hle hc =>
    le_antisymm (locBasic_locS_mono _ hle)
      ((locBasic_locS_mono _ fun y hy => locBasic_mem_locS.2 ⟨t, ht, hc.smul_mem htI hy⟩).trans (locBasic_locS_idem _ _).le)
  rw [eq hLM cL, eq hNM cN]
  exact UnimodLoc.exists_isom_of_isUnimodularAt K V h hK hs hn M M' hM hM' P hP
    ((ld M hM.fg).2.1 uM P hP) ((ld M' hM'.fg).2.1 uM' P hP)

end Lattices

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ _ _ h hK hs hn T hT H`. Use `⟨exists_half hK hT H, fun L N hL ⟨eL⟩ => ⟨fun hN => ?_, fun ⟨hN, eN⟩ => ⟨hN.1, ?_⟩⟩⟩` and prove the remaining obligations. Take `⟨S, hm, hp, -⟩` from `exists_primes hT H`. Conclude with `forward h hK hs hn _ S (fun P hP => ((hm P).1 hP).1) hp L N hL eL hN`. Take `⟨s, -, hm, hco, hp⟩` from `exists_half hK hT H`.

Establish `h0 : ∏ P ∈ s, P ≠ ⊥`. Introduce `e`. Rewrite `hp` using `[e, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot]`. Conclude with `hT.ne_zero (by exact_mod_cast hp)`. Establish `one` using `(GlobalTheory.Mass.SplitOver.main K V h hK hs hn _ h0 hco).1`.

Rewrite `one` using `[hp]`. Take `⟨M, ⟨hM, uM, hLM, ⟨cL⟩⟩, -⟩` from `one L hL ⟨eL⟩`. Take `⟨M', ⟨hM', uM', hNM, ⟨cN⟩⟩, -⟩` from `one N hN eN`. Conclude with `backward h hK hs hn s (fun P hP => (hm P hP).1) hco L N M M' hM hM' uM uM' hLM hNM (cyc_of_equiv cL) (cyc_of_equiv cN)`.
-/
theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ T : ℕ, T.Prime → (∀ P : Ideal (𝓞 K), P.IsMaximal → (T : 𝓞 K) ∈ P → Ideal.absNorm P = T ∧ (T : 𝓞 K) ∉ P ^ 2) → (∃ s : Finset (Ideal (𝓞 K)), s.card = fDeg K ∧ (∀ P ∈ s, P.IsMaximal ∧ Ideal.absNorm P = T) ∧ IsCoprime (∏ P ∈ s, P) (conjIdeal (K := K) (∏ P ∈ s, P)) ∧ (∏ P ∈ s, P) * conjIdeal (K := K) (∏ P ∈ s, P) = Ideal.span {(T : 𝓞 K)}) ∧ ∀ L N : Submodule (𝓞 K) V, IsIntLat h L → Nonempty ((↥(dual h L) ⧸ L.comap (dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})) → (N ∈ genus h L ↔ IsIntLat h N ∧ Nonempty ((↥(dual h N) ⧸ N.comap (dual h N).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)}))) := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hn T hT H
  refine ⟨exists_half hK hT H, fun L N hL ⟨eL⟩ => ⟨fun hN => ?_, fun ⟨hN, eN⟩ => ⟨hN.1, ?_⟩⟩⟩
  · obtain ⟨S, hm, hp, -⟩ := exists_primes hT H
    exact forward h hK hs hn _ S (fun P hP => ((hm P).1 hP).1) hp L N hL eL hN
  · obtain ⟨s, -, hm, hco, hp⟩ := exists_half hK hT H
    have h0 : ∏ P ∈ s, P ≠ ⊥ := by
      intro e
      rw [e, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at hp
      exact hT.ne_zero (by exact_mod_cast hp)
    have one := (GlobalTheory.Mass.SplitOver.main K V h hK hs hn _ h0 hco).1
    rw [hp] at one
    obtain ⟨M, ⟨hM, uM, hLM, ⟨cL⟩⟩, -⟩ := one L hL ⟨eL⟩
    obtain ⟨M', ⟨hM', uM', hNM, ⟨cN⟩⟩, -⟩ := one N hN eN
    exact backward h hK hs hn s (fun P hP => (hm P hP).1) hco L N M M' hM hM' uM uM' hLM hNM
      (cyc_of_equiv cL) (cyc_of_equiv cN)

end GlobalTheory.Mass.CyclicGenus
