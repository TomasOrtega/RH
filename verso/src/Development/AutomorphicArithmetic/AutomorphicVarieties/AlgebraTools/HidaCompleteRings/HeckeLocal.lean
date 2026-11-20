import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.LocFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.FinMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.FinCompl
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.CofinalCompl
open IsLocalRing UpperTheory.V.Hi

/- English proof (translation)
Use `Submodule.smul_induction_on hx ?_ ?_` and prove the remaining obligations. Introduce `r hr y hy`. Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem_smul hr (hf y hy)`. Introduce `a b ha hb`.

Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ ha hb`.
-/
private theorem map_mem_smul {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (J : Ideal A) (L : Submodule A M) (f : Module.End A M) (hf : ∀ y ∈ L, f y ∈ L) {x : M}
    (hx : x ∈ J • L) : f x ∈ J • L := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr y hy
    rw [map_smul]
    exact Submodule.smul_mem_smul hr (hf y hy)
  · intro a b ha hb
    rw [map_add]
    exact Submodule.add_mem _ ha hb

/- English proof (translation)
Use `monotone_nat_of_le_succ fun n x hx => ?_` and prove the remaining obligations. Rewrite using `[Submodule.mem_comap, pow_succ', Module.End.mul_apply]`. Conclude with `map_mem_smul J L f hf hx`.
-/
private theorem mono_comap {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (J : Ideal A) (L : Submodule A M) (f : Module.End A M) (hf : ∀ y ∈ L, f y ∈ L) :
    Monotone fun n : ℕ => (J • L).comap (f ^ n) := by
  refine monotone_nat_of_le_succ fun n x hx => ?_
  rw [Submodule.mem_comap, pow_succ', Module.End.mul_apply]
  exact map_mem_smul J L f hf hx

/- English proof (translation)
Establish `hmono` using `mono_comap J (⊤ : Submodule A N) (j u) (fun _ _ => trivial)`. Take `⟨n, hn⟩` from `monotone_stabilizes_iff_noetherian.2 (inferInstance : IsNoetherian A N) ⟨_, hmono⟩`. Establish `hr : LinearMap.range (j (u ^ n)) ≤ J • (⊤ : Submodule A N)`. Introduce and unpack `_ ⟨x, rfl⟩`. Take `⟨k, hk⟩` from `h x`.

Establish `h1 : x ∈ (J • (⊤ : Submodule A N)).comap (j u ^ (max n k))` using `hmono (le_max_right n k) hk`. Establish `h2` using `hn (max n k) (le_max_left n k)`. Express the relevant statement in the definitionally equal form `(J • (⊤ : Submodule A N)).comap (j u ^ n) = (J • (⊤ : Submodule A N)).comap (j u ^ (max n k)) at h2`. Rewrite `h1` using `[← h2]`. Rewrite using `[map_pow]`.

Conclude with `h1`. Take `⟨p, hp, -, hc, h0⟩` from `LinearMap.exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul A (j (u ^ n)) J hr`. Rewrite `h0` using `[Polynomial.aeval_algHom_apply]`. Establish `h1 : Polynomial.aeval (u ^ n) p = 0` using `hj (by rw [h0, map_zero])`. Use `⟨n * p.natDegree, ?_⟩` and prove the remaining obligations.

Rewrite `h1` using `[Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_smul, ← pow_mul, add_eq_zero_iff_neg_eq]`. Rewrite using `[← h1]`. Use `neg_mem (Ideal.sum_mem _ fun k hk => ?_)` and prove the remaining obligations. Rewrite using `[Algebra.smul_def]`. Use `Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)` and prove the remaining obligations.

Conclude with `Ideal.pow_le_self (by have := Finset.mem_range.1 hk; omega) (hc k)`.
-/
private theorem pow_mem_map {A N T : Type} [CommRing A] [IsNoetherianRing A] [AddCommGroup N]
    [Module A N] [Module.Finite A N] [CommRing T] [Algebra A T] (J : Ideal A)
    (j : T →ₐ[A] Module.End A N) (hj : Function.Injective j) (u : T)
    (h : ∀ x, ∃ n : ℕ, (j u ^ n) x ∈ J • (⊤ : Submodule A N)) :
    ∃ n : ℕ, u ^ n ∈ J.map (algebraMap A T) := by
  have hmono := mono_comap J (⊤ : Submodule A N) (j u) (fun _ _ => trivial)
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.2 (inferInstance : IsNoetherian A N)
    ⟨_, hmono⟩
  have hr : LinearMap.range (j (u ^ n)) ≤ J • (⊤ : Submodule A N) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨k, hk⟩ := h x
    have h1 : x ∈ (J • (⊤ : Submodule A N)).comap (j u ^ (max n k)) :=
      hmono (le_max_right n k) hk
    have h2 := hn (max n k) (le_max_left n k)
    change (J • (⊤ : Submodule A N)).comap (j u ^ n) = (J • (⊤ : Submodule A N)).comap (j u ^ (max n k)) at h2
    rw [← h2] at h1
    rw [map_pow]
    exact h1
  obtain ⟨p, hp, -, hc, h0⟩ :=
    LinearMap.exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul A (j (u ^ n)) J hr
  rw [Polynomial.aeval_algHom_apply] at h0
  have h1 : Polynomial.aeval (u ^ n) p = 0 := hj (by rw [h0, map_zero])
  refine ⟨n * p.natDegree, ?_⟩
  rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_smul,
    ← pow_mul, add_eq_zero_iff_neg_eq] at h1
  rw [← h1]
  refine neg_mem (Ideal.sum_mem _ fun k hk => ?_)
  rw [Algebra.smul_def]
  refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
  exact Ideal.pow_le_self (by have := Finset.mem_range.1 hk; omega) (hc k)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => intro y`. Both sides reduce to the same expression. Consider the case `succ n ih`. Introduce `y`.

Rewrite using `[pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, h, ih]`.
-/
private theorem restr_pow {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    {L : Submodule A M} (t : Module.End A L) (f : Module.End A M) (h : Restr t f) (n : ℕ) :
    Restr (t ^ n) (f ^ n) := by
  induction n with
  | zero => intro y; rfl
  | succ n ih =>
    intro y
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, h, ih]

/- English proof (translation)
Introduce `A M ι _ _ _ _ Y _ op a hcomm hne T _ _ j hj hrange`. Take `⟨hcL, hidem, hfinL, -, -⟩` from `UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locFree A M ι Y op a hcomm`. Establish `hLY : locPart Y op a ≤ Y` using `inf_le_left`. Generalize the expression as in `locPart Y op a = L at *`. Use `haveI : Module.Finite A T := Module.Finite.of_injective j.toLinearMap hj`.

Use `haveI : Nontrivial L := Submodule.nontrivial_iff_ne_bot.2 hne`. Use `haveI : Nontrivial T := j.toRingHom.domain_nontrivial`. Take `⟨-, hmax, n, hn1, hn2⟩` from `UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.finMax A T`. Establish `hle : ∀ P : Ideal T, P.IsMaximal → (maximalIdeal A).map (algebraMap A T) ≤ P` using `fun P hP => Ideal.map_le_iff_le_comap.2 (hmax P hP).1.ge`. Establish `h1 : ∀ i s, Restr (j s) (op i) → ∀ P : Ideal T, P.IsMaximal → s - algebraMap A T (a i) ∈ P`.

Introduce `i s hs P hP`. Establish `hr : Restr (j (s - algebraMap A T (a i))) (op i - algebraMap A _ (a i))`. Introduce `y`. Rewrite using `[map_sub, AlgHom.commutes]`. Simplify using `[hs y]`.

Establish `hpres : ∀ y ∈ L, (op i - algebraMap A _ (a i)) y ∈ L` using `fun y hy => by`. Rewrite using `[← hr ⟨y, hy⟩]`. Conclude with `Subtype.mem _`. Take `⟨k, hk⟩` from `pow_mem_map (maximalIdeal A) j hj (s - algebraMap A T (a i)) (fun x => by`. Establish `hx : (x : M) ∈ locPart L op a` using `by rw [hidem]; exact x.2`.

Establish `hx2` using `(Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hx.2 i) 1`. Take `⟨k, hk⟩` from `(Submodule.mem_iSup_of_directed _ (mono_comap _ L _ hpres).directed_le).1 hx2`. Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.mem_smul_top_iff, restr_pow _ _ hr k x]`. Rewrite `hk` using `[pow_one]`.

Conclude with `hk)`. Conclude with `hP.isPrime.mem_of_pow_mem k (hle P hP hk)`. Establish `h2 : ∀ s : T, ∃ c : A, ∀ P : Ideal T, P.IsMaximal → s - algebraMap A T c ∈ P`. Establish `key : ∀ φ ∈ heckeAlg L op, ∀ s, j s = φ → ∃ c : A, ∀ P : Ideal T, P.IsMaximal → s - algebraMap A T c ∈ P`. Introduce `φ hφ`.

Proceed by induction on `hφ using Algebra.adjoin_induction with`. Consider the case `mem φ hφ`. Take `⟨i, hi⟩` from `hφ`. Introduce and unpack `s rfl`. Conclude with `⟨a i, h1 i s hi⟩`.

Consider the case `algebraMap r`. Introduce `s hs`. Use `⟨r, fun P _ => ?_⟩` and prove the remaining obligations. Rewrite using `[hj (hs.trans (j.commutes r).symm), sub_self]`. Conclude with `P.zero_mem`.

Consider the case `add φ ψ hφ hψ ihφ ihψ`. Introduce `s hs`. Take `⟨x, hx⟩ : φ ∈ j.range` from `hrange ▸ hφ`. Take `⟨y, hy⟩ : ψ ∈ j.range` from `hrange ▸ hψ`. Take `⟨c, hc⟩` from `ihφ x hx`.

Take `⟨d, hd⟩` from `ihψ y hy`. Take `rfl : s = x + y` from `hj (by rw [hs, map_add, ← hx, ← hy]; rfl)`. Use `⟨c + d, fun P hP => ?_⟩` and prove the remaining obligations. Use `P.add_mem (hc P hP) (hd P hP) using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_add]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `mul φ ψ hφ hψ ihφ ihψ`. Introduce `s hs`. Take `⟨x, hx⟩ : φ ∈ j.range` from `hrange ▸ hφ`. Take `⟨y, hy⟩ : ψ ∈ j.range` from `hrange ▸ hψ`.

Take `⟨c, hc⟩` from `ihφ x hx`. Take `⟨d, hd⟩` from `ihψ y hy`. Take `rfl : s = x * y` from `hj (by rw [hs, map_mul, ← hx, ← hy]; rfl)`. Use `⟨c * d, fun P hP => ?_⟩` and prove the remaining obligations. Use `P.add_mem (P.mul_mem_right y (hc P hP)) (P.mul_mem_left (algebraMap A T c) (hd P hP)) using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Introduce `s`. Conclude with `key (j s) (hrange ▸ ⟨s, rfl⟩) s rfl`. Use `haveI hloc : IsLocalRing T := by`.

Take `⟨P, hP⟩` from `Ideal.exists_maximal T`. Use `IsLocalRing.of_unique_max_ideal ⟨P, hP, fun Q hQ => hQ.eq_of_le hP.ne_top fun s hs => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `h2 s`. Establish `h3 : algebraMap A T c ∈ Q`. Use `Q.sub_mem hs (hc Q hQ)` as an intermediate fact.

Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis. Establish `h4 : c ∈ P.comap (algebraMap A T)`. Rewrite using `[(hmax P hP).1, ← (hmax Q hQ).1]`. Conclude with `h3`. Use `P.add_mem (hc P hP) h4` as an intermediate fact.

Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Establish `hm` using `maximalIdeal.isMaximal T`. Use `haveI : IsNoetherianRing T := IsNoetherianRing.of_finite A T`. Rewrite `hn1`, `hn2` using `[jacobson_eq_maximalIdeal ⊥ bot_ne_top]`. Establish `hcomp : IsAdicComplete (maximalIdeal T) T` using `UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.cofinalCompl T T _ _ n hn1 hn2 ((IsAdicComplete.map_algebraMap_iff _ _).2 (UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.finCompl A T (maximalIdeal A)))`.

Use `⟨{ complete := hcomp, finite := (hmax _ hm).2 inferInstance }, inferInstance, ?_, fun s => (h2 s).imp fun c hc => hc _ hm, fun i s hs => h1 i s hs _ hm, fun c hc => ?_⟩` and prove the remaining obligations. Use `⟨fun c hc => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Establish `: c ∈ (maximalIdeal T).comap (algebraMap A T)`. Rewrite using `[(hmax _ hm).1]`.

Conclude with `h`. Conclude with `this hc`. Rewrite using `[mem_nonZeroDivisors_iff_left]`. Introduce `s hs`. Apply `hj` to reduce the goal to its premises.

Rewrite using `[map_zero]`. Use extensionality with `y`. Establish `h3` using `congrArg (fun t => ((j t y : L) : M)) hs`. Simplify using `only [map_mul, AlgHom.commutes, map_zero] at h3`. Simplify `h3)` using `using hc _ (hLY (j s y).2) (by simpa`.
-/
theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.heckeLocal :
    ∀ (A M ι : Type) [CommRing A] [IsCNL A] [AddCommGroup M] [Module A M] (Y : Submodule A M) [Module.Finite A Y] (op : ι → Module.End A M) (a : ι → A), CommOn Y op → locPart Y op a ≠ ⊥ → ∀ (T : Type) [CommRing T] [Algebra A T] (j : T →ₐ[A] Module.End A (locPart Y op a)), Function.Injective j → j.range = heckeAlg (locPart Y op a) op → ∃ _ : IsCNL T, Module.Finite A T ∧ IsLocalHom (algebraMap A T) ∧ (∀ s : T, ∃ c : A, s - algebraMap A T c ∈ maximalIdeal T) ∧ (∀ i s, Restr (j s) (op i) → s - algebraMap A T (a i) ∈ maximalIdeal T) ∧ ∀ c : A, (∀ y ∈ Y, c • y = 0 → y = 0) → algebraMap A T c ∈ nonZeroDivisors T := by
  intro A M ι _ _ _ _ Y _ op a hcomm hne T _ _ j hj hrange
  obtain ⟨hcL, hidem, hfinL, -, -⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locFree A M ι Y op a hcomm
  have hLY : locPart Y op a ≤ Y := inf_le_left
  generalize locPart Y op a = L at *
  haveI : Module.Finite A T := Module.Finite.of_injective j.toLinearMap hj
  haveI : Nontrivial L := Submodule.nontrivial_iff_ne_bot.2 hne
  haveI : Nontrivial T := j.toRingHom.domain_nontrivial
  obtain ⟨-, hmax, n, hn1, hn2⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.finMax A T
  have hle : ∀ P : Ideal T, P.IsMaximal → (maximalIdeal A).map (algebraMap A T) ≤ P :=
    fun P hP => Ideal.map_le_iff_le_comap.2 (hmax P hP).1.ge
  have h1 : ∀ i s, Restr (j s) (op i) → ∀ P : Ideal T, P.IsMaximal →
      s - algebraMap A T (a i) ∈ P := by
    intro i s hs P hP
    have hr : Restr (j (s - algebraMap A T (a i))) (op i - algebraMap A _ (a i)) := by
      intro y
      rw [map_sub, AlgHom.commutes]
      simp [hs y]
    have hpres : ∀ y ∈ L, (op i - algebraMap A _ (a i)) y ∈ L := fun y hy => by
      rw [← hr ⟨y, hy⟩]; exact Subtype.mem _
    obtain ⟨k, hk⟩ := pow_mem_map (maximalIdeal A) j hj (s - algebraMap A T (a i)) (fun x => by
      have hx : (x : M) ∈ locPart L op a := by rw [hidem]; exact x.2
      have hx2 := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hx.2 i) 1
      obtain ⟨k, hk⟩ := (Submodule.mem_iSup_of_directed _
        (mono_comap _ L _ hpres).directed_le).1 hx2
      refine ⟨k, ?_⟩
      rw [Submodule.mem_smul_top_iff, restr_pow _ _ hr k x]
      rw [pow_one] at hk
      exact hk)
    exact hP.isPrime.mem_of_pow_mem k (hle P hP hk)
  have h2 : ∀ s : T, ∃ c : A, ∀ P : Ideal T, P.IsMaximal → s - algebraMap A T c ∈ P := by
    have key : ∀ φ ∈ heckeAlg L op, ∀ s, j s = φ →
        ∃ c : A, ∀ P : Ideal T, P.IsMaximal → s - algebraMap A T c ∈ P := by
      intro φ hφ
      induction hφ using Algebra.adjoin_induction with
      | mem φ hφ =>
        obtain ⟨i, hi⟩ := hφ
        rintro s rfl
        exact ⟨a i, h1 i s hi⟩
      | algebraMap r =>
        intro s hs
        refine ⟨r, fun P _ => ?_⟩
        rw [hj (hs.trans (j.commutes r).symm), sub_self]
        exact P.zero_mem
      | add φ ψ hφ hψ ihφ ihψ =>
        intro s hs
        obtain ⟨x, hx⟩ : φ ∈ j.range := hrange ▸ hφ
        obtain ⟨y, hy⟩ : ψ ∈ j.range := hrange ▸ hψ
        obtain ⟨c, hc⟩ := ihφ x hx
        obtain ⟨d, hd⟩ := ihψ y hy
        obtain rfl : s = x + y := hj (by rw [hs, map_add, ← hx, ← hy]; rfl)
        refine ⟨c + d, fun P hP => ?_⟩
        convert P.add_mem (hc P hP) (hd P hP) using 1
        rw [map_add]; ring
      | mul φ ψ hφ hψ ihφ ihψ =>
        intro s hs
        obtain ⟨x, hx⟩ : φ ∈ j.range := hrange ▸ hφ
        obtain ⟨y, hy⟩ : ψ ∈ j.range := hrange ▸ hψ
        obtain ⟨c, hc⟩ := ihφ x hx
        obtain ⟨d, hd⟩ := ihψ y hy
        obtain rfl : s = x * y := hj (by rw [hs, map_mul, ← hx, ← hy]; rfl)
        refine ⟨c * d, fun P hP => ?_⟩
        convert P.add_mem (P.mul_mem_right y (hc P hP))
          (P.mul_mem_left (algebraMap A T c) (hd P hP)) using 1
        rw [map_mul]; ring
    intro s
    exact key (j s) (hrange ▸ ⟨s, rfl⟩) s rfl
  haveI hloc : IsLocalRing T := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal T
    refine IsLocalRing.of_unique_max_ideal ⟨P, hP, fun Q hQ => hQ.eq_of_le hP.ne_top fun s hs => ?_⟩
    obtain ⟨c, hc⟩ := h2 s
    have h3 : algebraMap A T c ∈ Q := by
      have := Q.sub_mem hs (hc Q hQ)
      rwa [sub_sub_cancel] at this
    have h4 : c ∈ P.comap (algebraMap A T) := by
      rw [(hmax P hP).1, ← (hmax Q hQ).1]; exact h3
    have := P.add_mem (hc P hP) h4
    rwa [sub_add_cancel] at this
  have hm := maximalIdeal.isMaximal T
  haveI : IsNoetherianRing T := IsNoetherianRing.of_finite A T
  rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hn1 hn2
  have hcomp : IsAdicComplete (maximalIdeal T) T :=
    UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.cofinalCompl T T _ _ n hn1 hn2
      ((IsAdicComplete.map_algebraMap_iff _ _).2 (UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.finCompl A T (maximalIdeal A)))
  refine ⟨{ complete := hcomp, finite := (hmax _ hm).2 inferInstance }, inferInstance, ?_,
    fun s => (h2 s).imp fun c hc => hc _ hm, fun i s hs => h1 i s hs _ hm, fun c hc => ?_⟩
  · refine ⟨fun c hc => ?_⟩
    by_contra h
    have : c ∈ (maximalIdeal T).comap (algebraMap A T) := by
      rw [(hmax _ hm).1]; exact h
    exact this hc
  · rw [mem_nonZeroDivisors_iff_left]
    intro s hs
    apply hj
    rw [map_zero]
    ext y
    have h3 := congrArg (fun t => ((j t y : L) : M)) hs
    simp only [map_mul, AlgHom.commutes, map_zero] at h3
    simpa using hc _ (hLY (j s y).2) (by simpa using h3)
