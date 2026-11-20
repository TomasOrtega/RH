import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TopNilDefs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

/- English proof (translation)
Use `Submodule.smul_induction_on hy ?_ ?_` and prove the remaining obligations. Introduce `r hr n _`. Rewrite using `[← algebraMap_smul A r n, smul_smul, mul_comm, ← smul_smul, algebraMap_smul]`. Conclude with `Submodule.smul_mem_smul hr trivial`. Introduce `u v hu hv`.

Rewrite using `[smul_add]`. Conclude with `Submodule.add_mem _ hu hv`.
-/
private theorem UpperTheory.V.AlgebraTools.tnAlg_smul_mem {R A M : Type} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] (I : Ideal R) (a : A) {y : M}
    (hy : y ∈ (I • ⊤ : Submodule R M)) : a • y ∈ (I • ⊤ : Submodule R M) := by
  refine Submodule.smul_induction_on hy ?_ ?_
  · intro r hr n _
    rw [← algebraMap_smul A r n, smul_smul, mul_comm, ← smul_smul, algebraMap_smul]
    exact Submodule.smul_mem_smul hr trivial
  · intro u v hu hv
    rw [smul_add]
    exact Submodule.add_mem _ hu hv

/- English proof (translation)
Unfold `Ideal.map at ha`. Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem b hb`. Take `⟨r, hr, rfl⟩` from `hb`. Rewrite using `[algebraMap_smul]`.

Conclude with `Submodule.smul_mem_smul hr trivial`. Consider the case `zero => rw [zero_smul]`. Conclude with `Submodule.zero_mem _`. Consider the case `add b c _ _ hb hc => rw [add_smul]`. Conclude with `Submodule.add_mem _ hb hc`.

Consider the case `smul b c _ hc`. Rewrite using `[smul_eq_mul, mul_smul]`. Conclude with `UpperTheory.V.AlgebraTools.tnAlg_smul_mem I b hc`.
-/
private theorem UpperTheory.V.AlgebraTools.tnAlg_map_smul_mem {R A M : Type} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] (I : Ideal R)
    {a : A} (ha : a ∈ I.map (algebraMap R A)) (y : M) : a • y ∈ (I • ⊤ : Submodule R M) := by
  unfold Ideal.map at ha
  induction ha using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨r, hr, rfl⟩ := hb
    rw [algebraMap_smul]
    exact Submodule.smul_mem_smul hr trivial
  | zero => rw [zero_smul]; exact Submodule.zero_mem _
  | add b c _ _ hb hc => rw [add_smul]; exact Submodule.add_mem _ hb hc
  | smul b c _ hc =>
    rw [smul_eq_mul, mul_smul]
    exact UpperTheory.V.AlgebraTools.tnAlg_smul_mem I b hc

/- English proof (translation)
Use `haveI : Algebra.IsIntegral R A := Algebra.IsIntegral.of_finite R A`. Rewrite using `[Ideal.radical_eq_sInf, Submodule.mem_sInf]`. Introduce and unpack `P ⟨hle, hP⟩`. Apply `ha` to reduce the goal to its premises. Establish `hle' : IsLocalRing.maximalIdeal R ≤ Ideal.comap (algebraMap R A) P`.

Introduce `r hr`. Rewrite using `[Ideal.mem_comap]`. Conclude with `hle (Ideal.mem_map_of_mem _ hr)`. Establish `hne : Ideal.comap (algebraMap R A) P ≠ ⊤` using `Ideal.comap_ne_top _ hP.ne_top`. Establish `hc : Ideal.comap (algebraMap R A) P = IsLocalRing.maximalIdeal R` using `((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hne hle').symm`.

Establish `hcm : (Ideal.comap (algebraMap R A) P).IsMaximal`. Rewrite using `[hc]`. Conclude with `IsLocalRing.maximalIdeal.isMaximal R`. Conclude with `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R) P hcm`.
-/
private theorem UpperTheory.V.AlgebraTools.tnAlg_mem_radical {R A : Type} [CommRing R] [IsLocalRing R]
    [CommRing A] [Algebra R A] [Module.Finite R A] {a : A}
    (ha : ∀ n : Ideal A, n.IsMaximal → a ∈ n) :
    a ∈ ((IsLocalRing.maximalIdeal R).map (algebraMap R A)).radical := by
  haveI : Algebra.IsIntegral R A := Algebra.IsIntegral.of_finite R A
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
  rintro P ⟨hle, hP⟩
  apply ha
  have hle' : IsLocalRing.maximalIdeal R ≤ Ideal.comap (algebraMap R A) P := by
    intro r hr
    rw [Ideal.mem_comap]
    exact hle (Ideal.mem_map_of_mem _ hr)
  have hne : Ideal.comap (algebraMap R A) P ≠ ⊤ := Ideal.comap_ne_top _ hP.ne_top
  have hc : Ideal.comap (algebraMap R A) P = IsLocalRing.maximalIdeal R :=
    ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hne hle').symm
  have hcm : (Ideal.comap (algebraMap R A) P).IsMaximal := by
    rw [hc]
    exact IsLocalRing.maximalIdeal.isMaximal R
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R) P hcm

/- English proof (translation)
Introduce `R _ _ _ _ A κ _ _ _ t`. Use `haveI : HenselianLocalRing R := GlobalTheory.henselianLocalRing_of_henselianRing R`. Take `⟨e, he, hT⟩` from `GlobalTheory.exists_idempotent_notMem_iff_mem_of_henselian R (S := A) {n : MaximalSpectrum A | ∀ i, t i ∈ n.asIdeal}`. Establish `hmax : ∀ n : Ideal A, n.IsMaximal → (e ∉ n ↔ ∀ i, t i ∈ n)` using `fun n hn => hT ⟨n, hn⟩`. Use `⟨e, he, hmax, ?_⟩` and prove the remaining obligations.

Introduce `M _ _ _ _ _ x`. Establish `hpow : ∀ (a : A) (r : ℕ) (y : M), ((Algebra.lsmul R R M a : Module.End R M) ^ r) y = a ^ r • y`. Introduce `a r y`. Rewrite using `[← map_pow, Algebra.lsmul_coe]`. Rewrite using `[mem_topNil_iff_exists]`.

Simplify using `only [hpow]`. Use `set m := IsLocalRing.maximalIdeal R with hm`. Establish `hA : ∀ j : ℕ, ∀ a : A, ∀ y ∈ (m ^ j • ⊤ : Submodule R M), a • y ∈ (m ^ j • ⊤ : Submodule R M)` using `fun j a y hy => UpperTheory.V.AlgebraTools.tnAlg_smul_mem (m ^ j) a hy`. Prove the components needed by the constructor for the conclusion. Introduce `hx set y := x - e • x with hy`.

Establish `hey : e • y = 0` using `by rw [hy, smul_sub, smul_smul, he.eq, sub_self]`. It suffices to establish `y = 0 by rw [sub_eq_zero] at this; exact this.symm`. Establish `hall : ∀ j : ℕ, y ∈ (m ^ j • ⊤ : Submodule R M)`. Introduce `j`. Set `P : Submodule A M` to `{ carrier := (m ^ j • ⊤ : Submodule R M) add_mem' := fun ha hb => Submodule.add_mem _ ha hb zero_mem' := Submodule.zero_mem _ smul_mem' := fun a _ hb => hA j a _ hb }`.

Set `K : Ideal A` to `P.comap (LinearMap.toSpanSingleton A M y)`. Establish `hKe : e ∈ K` using `by show e • y ∈ P`. Rewrite using `[hey]`. Conclude with `P.zero_mem`. Establish `hKt : ∀ i, t i ∈ K.radical`.

Introduce `i`. Take `⟨r, hr⟩` from `hx i j`. Use `⟨r, ?_⟩` and prove the remaining obligations. Use `show t i ^ r • y ∈ (m ^ j • ⊤ : Submodule R M)`. Rewrite using `[hy, smul_sub]`.

Use `Submodule.sub_mem _ hr ?_` and prove the remaining obligations. Rewrite using `[smul_comm (t i ^ r) e x]`. Conclude with `hA j e _ hr`. Establish `htop : K.radical = ⊤`. Assume the negation of the conclusion as `hne`.

Take `⟨n, hn, hle⟩` from `Ideal.exists_le_maximal _ hne`. Conclude with `((hmax n hn).mpr (fun i => hle (hKt i))) (hle (Ideal.le_radical hKe))`. Establish `h1 : (1 : A) ∈ K.radical` using `htop ▸ Submodule.mem_top`. Take `⟨r, hr⟩` from `h1`. Establish `h2 : (1 : A) ^ r • y ∈ (m ^ j • ⊤ : Submodule R M)` using `hr`.

Rewrite `h2` using `[one_pow, one_smul]`. Conclude with `h2`. Establish `hbot` using `Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M) m (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top])`. Establish `hyi : y ∈ (⨅ i, m ^ i • ⊤ : Submodule R M)` using `Submodule.mem_iInf _ |>.mpr hall`. Rewrite `hyi` using `[hbot]`.

Conclude with `hyi`. Introduce `hx i j`. Establish `hin : ∀ n : Ideal A, n.IsMaximal → t i * e ∈ n`. Introduce `n hn`. Distinguish the cases in `h : e ∈ n`.

Conclude with `n.mul_mem_left _ h`. Conclude with `n.mul_mem_right _ ((hmax n hn).mp h i)`. Take `⟨N, hN⟩` from `UpperTheory.V.AlgebraTools.tnAlg_mem_radical (R := R) hin`. Use `⟨N * j, ?_⟩` and prove the remaining obligations. Establish `hex : ∀ k : ℕ, e ^ k • x = x`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ, mul_smul, hx, ih]`. Establish `hmem : (t i * e) ^ (N * j) ∈ (m ^ j).map (algebraMap R A)`.

Rewrite using `[Ideal.map_pow, pow_mul]`. Conclude with `Ideal.pow_mem_pow hN j`. Establish `h3` using `UpperTheory.V.AlgebraTools.tnAlg_map_smul_mem (m ^ j) hmem x`. Rewrite `h3` using `[mul_pow, mul_smul, hex]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.V.AlgebraTools.topNil_eq_idem :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (A κ : Type) [CommRing A] [Algebra R A] [Module.Finite R A] (t : κ → A),
      ∃ e : A, IsIdempotentElem e ∧ (∀ n : Ideal A, n.IsMaximal → (e ∉ n ↔ ∀ i, t i ∈ n)) ∧
        ∀ (M : Type) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] [Module.Finite R M] (x : M),
          x ∈ topNil (IsLocalRing.maximalIdeal R) (fun i => (Algebra.lsmul R R M (t i) : Module.End R M)) ↔ e • x = x := by
  intro R _ _ _ _ A κ _ _ _ t
  haveI : HenselianLocalRing R := GlobalTheory.henselianLocalRing_of_henselianRing R
  obtain ⟨e, he, hT⟩ := GlobalTheory.exists_idempotent_notMem_iff_mem_of_henselian R (S := A)
    {n : MaximalSpectrum A | ∀ i, t i ∈ n.asIdeal}
  have hmax : ∀ n : Ideal A, n.IsMaximal → (e ∉ n ↔ ∀ i, t i ∈ n) := fun n hn => hT ⟨n, hn⟩
  refine ⟨e, he, hmax, ?_⟩
  intro M _ _ _ _ _ x
  have hpow : ∀ (a : A) (r : ℕ) (y : M),
      ((Algebra.lsmul R R M a : Module.End R M) ^ r) y = a ^ r • y := by
    intro a r y
    rw [← map_pow, Algebra.lsmul_coe]
  rw [mem_topNil_iff_exists]
  simp only [hpow]
  set m := IsLocalRing.maximalIdeal R with hm
  have hA : ∀ j : ℕ, ∀ a : A, ∀ y ∈ (m ^ j • ⊤ : Submodule R M), a • y ∈ (m ^ j • ⊤ : Submodule R M) :=
    fun j a y hy => UpperTheory.V.AlgebraTools.tnAlg_smul_mem (m ^ j) a hy
  constructor
  · intro hx
    set y := x - e • x with hy
    have hey : e • y = 0 := by rw [hy, smul_sub, smul_smul, he.eq, sub_self]
    suffices y = 0 by rw [sub_eq_zero] at this; exact this.symm
    have hall : ∀ j : ℕ, y ∈ (m ^ j • ⊤ : Submodule R M) := by
      intro j
      let P : Submodule A M :=
        { carrier := (m ^ j • ⊤ : Submodule R M)
          add_mem' := fun ha hb => Submodule.add_mem _ ha hb
          zero_mem' := Submodule.zero_mem _
          smul_mem' := fun a _ hb => hA j a _ hb }
      let K : Ideal A := P.comap (LinearMap.toSpanSingleton A M y)
      have hKe : e ∈ K := by
        show e • y ∈ P
        rw [hey]
        exact P.zero_mem
      have hKt : ∀ i, t i ∈ K.radical := by
        intro i
        obtain ⟨r, hr⟩ := hx i j
        refine ⟨r, ?_⟩
        show t i ^ r • y ∈ (m ^ j • ⊤ : Submodule R M)
        rw [hy, smul_sub]
        refine Submodule.sub_mem _ hr ?_
        rw [smul_comm (t i ^ r) e x]
        exact hA j e _ hr
      have htop : K.radical = ⊤ := by
        by_contra hne
        obtain ⟨n, hn, hle⟩ := Ideal.exists_le_maximal _ hne
        exact ((hmax n hn).mpr (fun i => hle (hKt i))) (hle (Ideal.le_radical hKe))
      have h1 : (1 : A) ∈ K.radical := htop ▸ Submodule.mem_top
      obtain ⟨r, hr⟩ := h1
      have h2 : (1 : A) ^ r • y ∈ (m ^ j • ⊤ : Submodule R M) := hr
      rw [one_pow, one_smul] at h2
      exact h2
    have hbot := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M) m
      (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top])
    have hyi : y ∈ (⨅ i, m ^ i • ⊤ : Submodule R M) := Submodule.mem_iInf _ |>.mpr hall
    rw [hbot] at hyi
    exact hyi
  · intro hx i j
    have hin : ∀ n : Ideal A, n.IsMaximal → t i * e ∈ n := by
      intro n hn
      by_cases h : e ∈ n
      · exact n.mul_mem_left _ h
      · exact n.mul_mem_right _ ((hmax n hn).mp h i)
    obtain ⟨N, hN⟩ := UpperTheory.V.AlgebraTools.tnAlg_mem_radical (R := R) hin
    refine ⟨N * j, ?_⟩
    have hex : ∀ k : ℕ, e ^ k • x = x := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, mul_smul, hx, ih]
    have hmem : (t i * e) ^ (N * j) ∈ (m ^ j).map (algebraMap R A) := by
      rw [Ideal.map_pow, pow_mul]
      exact Ideal.pow_mem_pow hN j
    have h3 := UpperTheory.V.AlgebraTools.tnAlg_map_smul_mem (m ^ j) hmem x
    rwa [mul_pow, mul_smul, hex] at h3
