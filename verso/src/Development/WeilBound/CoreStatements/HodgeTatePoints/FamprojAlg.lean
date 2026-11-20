import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LeadMinor

noncomputable section

namespace PositivityTheory.HtPt.Famproj

open NumberField GlobalTheory.CompanionTheory.Ar.HT

/- English proof (translation)
Use `choose N inst1 inst2 proj f g t ht hfg using fun m : {m : Ideal A // m.IsMaximal} => h m.1 m.2`. Establish `hspan : (1 : A) ∈ Submodule.span A (Set.range t)`. Assume the negation of the conclusion as `h1`. Establish `hne : Ideal.span (Set.range t) ≠ ⊤` using `fun h2 => h1 (by`. Express the relevant statement in the definitionally equal form `(1 : A) ∈ Ideal.span (Set.range t)`.

Rewrite using `[h2]`. Use the proof step `trivial)`. Take `⟨m, hm, hle⟩` from `Ideal.exists_le_maximal _ hne`. Conclude with `ht ⟨m, hm⟩ (hle (Ideal.subset_span ⟨⟨m, hm⟩, rfl⟩))`. Take `⟨c, hc⟩` from `Finsupp.mem_span_range_iff_exists_finsupp.mp hspan`.

Use `Module.Projective.of_split (M := DirectSum _ N) (∑ i ∈ c.support, (DirectSum.lof A _ N i).comp (f i)) (DirectSum.toModule A _ M (fun i => c i • g i)) ?_` and prove the remaining obligations. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Simplify using `only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum, DirectSum.toModule_lof, LinearMap.smul_apply, hfg, LinearMap.id_apply, smul_smul]`. Rewrite using `[← Finset.sum_smul]`.

Rewrite `hc` using `[Finsupp.sum]`. Simplify using `only [smul_eq_mul] at hc`. Rewrite using `[hc, one_smul]`.
-/
theorem projective_of_factor {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (h : ∀ m : Ideal A, m.IsMaximal → ∃ (N : Type) (_ : AddCommGroup N) (_ : Module A N) (_ : Module.Projective A N)
      (f : M →ₗ[A] N) (g : N →ₗ[A] M) (t : A), t ∉ m ∧ ∀ x, g (f x) = t • x) : Module.Projective A M := by
  classical
  choose N inst1 inst2 proj f g t ht hfg using fun m : {m : Ideal A // m.IsMaximal} => h m.1 m.2
  have hspan : (1 : A) ∈ Submodule.span A (Set.range t) := by
    by_contra h1
    have hne : Ideal.span (Set.range t) ≠ ⊤ := fun h2 => h1 (by
      change (1 : A) ∈ Ideal.span (Set.range t)
      rw [h2]
      trivial)
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    exact ht ⟨m, hm⟩ (hle (Ideal.subset_span ⟨⟨m, hm⟩, rfl⟩))
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hspan
  refine Module.Projective.of_split (M := DirectSum _ N)
    (∑ i ∈ c.support, (DirectSum.lof A _ N i).comp (f i))
    (DirectSum.toModule A _ M (fun i => c i • g i)) ?_
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum,
    DirectSum.toModule_lof, LinearMap.smul_apply, hfg, LinearMap.id_apply, smul_smul]
  rw [← Finset.sum_smul]
  rw [Finsupp.sum] at hc
  simp only [smul_eq_mul] at hc
  rw [hc, one_smul]

section Sub

variable {A Ω V : Type} [CommRing A] [Field Ω] [Algebra A Ω] [AddCommGroup V] [Module Ω V] [Module A V]
  [IsScalarTower A Ω V]

/- English proof (translation)
Establish `h1 : (1 : A) ∉ m` using `fun h => hm.ne_top ((Ideal.eq_top_iff_one _).2 h)`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨1, h1, by simpa using hy⟩`. Consider the case `zero => exact ⟨1, h1, by simp⟩`. Consider the case `add y z _ _ hy hz`.

Take `⟨t1, ht1, hy1⟩` from `hy`. Take `⟨t2, ht2, hz2⟩` from `hz`. Use `⟨t1 * t2, fun h => (hm.mem_or_mem h).elim ht1 ht2, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Apply `M.add_mem` to reduce the goal to its premises.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `M.smul_mem _ hy1`. Rewrite using `[mul_smul]`. Conclude with `M.smul_mem _ hz2`. Consider the case `smul r y _ hy`.

Take `⟨t', ht', hy'⟩` from `hy`. Take `⟨t, ht, a, hta⟩` from `hR r r.2`. Establish `key : t • (r • y) = a • y`. Rewrite using `[← algebraMap_smul Ω t, Subring.smul_def, smul_smul, hta, algebraMap_smul]`. Use `⟨t' * t, fun h => (hm.mem_or_mem h).elim ht' ht, ?_⟩` and prove the remaining obligations.

Rewrite using `[mul_smul, key, smul_comm]`. Conclude with `M.smul_mem _ hy'`.
-/
theorem exists_smul_mem (m : Ideal A) [hm : m.IsPrime] (R : Subring Ω)
    (hR : ∀ r ∈ R, ∃ t ∉ m, ∃ a : A, algebraMap A Ω t * r = algebraMap A Ω a) (M : Submodule A V) {x : V}
    (hx : x ∈ Submodule.span R (M : Set V)) : ∃ t ∉ m, t • x ∈ M := by
  have h1 : (1 : A) ∉ m := fun h => hm.ne_top ((Ideal.eq_top_iff_one _).2 h)
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, h1, by simpa using hy⟩
  | zero => exact ⟨1, h1, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨t1, ht1, hy1⟩ := hy
    obtain ⟨t2, ht2, hz2⟩ := hz
    refine ⟨t1 * t2, fun h => (hm.mem_or_mem h).elim ht1 ht2, ?_⟩
    rw [smul_add]
    apply M.add_mem
    · rw [mul_comm, mul_smul]
      exact M.smul_mem _ hy1
    · rw [mul_smul]
      exact M.smul_mem _ hz2
  | smul r y _ hy =>
    obtain ⟨t', ht', hy'⟩ := hy
    obtain ⟨t, ht, a, hta⟩ := hR r r.2
    have key : t • (r • y) = a • y := by
      rw [← algebraMap_smul Ω t, Subring.smul_def, smul_smul, hta, algebraMap_smul]
    refine ⟨t' * t, fun h => (hm.mem_or_mem h).elim ht' ht, ?_⟩
    rw [mul_smul, key, smul_comm]
    exact M.smul_mem _ hy'

omit [Algebra A Ω] [Module Ω V] [IsScalarTower A Ω V] in

/- English proof (translation)
Take `⟨S, hS⟩` from `hM`. Establish `hSM : ∀ s ∈ S, s ∈ M` using `fun s hs => hS ▸ Submodule.subset_span hs`. Use `choose! t ht hts using fun s (hs : s ∈ S) => h s (hSM s hs)`. Use `⟨∏ s ∈ S, t s, fun hp => ?_, ?_⟩` and prove the remaining obligations. Take `⟨s, hs, hsm⟩` from `Ideal.IsPrime.prod_mem_iff.1 hp`.

Conclude with `ht s hs hsm`. Introduce `x hx`. Rewrite `hx` using `[← hS]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`.

Rewrite using `[← Finset.mul_prod_erase S t hy, mul_comm, mul_smul]`. Conclude with `N.smul_mem _ (hts y hy)`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz`. Rewrite using `[smul_add]`.

Conclude with `N.add_mem hy hz`. Consider the case `smul a y _ hy`. Rewrite using `[smul_comm]`. Conclude with `N.smul_mem _ hy`.
-/
theorem exists_smul_le (m : Ideal A) [hm : m.IsPrime] {M N : Submodule A V} (hM : M.FG)
    (h : ∀ x ∈ M, ∃ t ∉ m, t • x ∈ N) : ∃ t ∉ m, ∀ x ∈ M, t • x ∈ N := by
  classical
  obtain ⟨S, hS⟩ := hM
  have hSM : ∀ s ∈ S, s ∈ M := fun s hs => hS ▸ Submodule.subset_span hs
  choose! t ht hts using fun s (hs : s ∈ S) => h s (hSM s hs)
  refine ⟨∏ s ∈ S, t s, fun hp => ?_, ?_⟩
  · obtain ⟨s, hs, hsm⟩ := Ideal.IsPrime.prod_mem_iff.1 hp
    exact ht s hs hsm
  · intro x hx
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      rw [← Finset.mul_prod_erase S t hy, mul_comm, mul_smul]
      exact N.smul_mem _ (hts y hy)
    | zero => simp
    | add y z _ _ hy hz =>
      rw [smul_add]
      exact N.add_mem hy hz
    | smul a y _ hy =>
      rw [smul_comm]
      exact N.smul_mem _ hy

/- English proof (translation)
Establish `h1 : (1 : A) ∉ m` using `fun h => hm.ne_top ((Ideal.eq_top_iff_one _).2 h)`. Establish `hbA : LinearIndependent A b`. Use `hb.restrict_scalars ?_` and prove the remaining obligations. Introduce `x y hxy`. Apply `hA` to reduce the goal to its premises.

Simplify `hxy` using `[Algebra.smul_def]`. Use `set M' := Submodule.span A (Set.range b) with hM'`. Use `haveI : Module.Free A M' := Module.Free.of_basis (Module.Basis.span hbA)`. Establish `hM'fg : M'.FG` using `Submodule.fg_span (Set.finite_range b)`. Take `⟨t, ht, hto⟩` from `exists_smul_le m hM (N := M') (fun x hx => exists_smul_mem m R hR M' (by`.

Establish `hx' : x ∈ Submodule.span R (Set.range b)` using `he ▸ Submodule.subset_span hx`. Conclude with `Submodule.span_mono (Submodule.subset_span (R := A)) hx'))`. Establish `hback : ∀ y ∈ M', ∃ s ∉ m, s • y ∈ M`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem z hz`. Use `exists_smul_mem m R hR M ?_` and prove the remaining obligations. Rewrite using `[he]`. Conclude with `Submodule.subset_span hz`. Consider the case `zero => exact ⟨1, h1, by simp⟩`.

Consider the case `add y z _ _ hy hz`. Take `⟨t1, ht1, hy1⟩` from `hy`. Take `⟨t2, ht2, hz2⟩` from `hz`. Use `⟨t1 * t2, fun h => (hm.mem_or_mem h).elim ht1 ht2, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`.

Apply `M.add_mem` to reduce the goal to its premises. Rewrite using `[mul_comm, mul_smul]`. Conclude with `M.smul_mem _ hy1`. Rewrite using `[mul_smul]`. Conclude with `M.smul_mem _ hz2`.

Consider the case `smul a y _ hy`. Take `⟨s, hs, hsy⟩` from `hy`. Conclude with `⟨s, hs, by rw [smul_comm]; exact M.smul_mem _ hsy⟩`. Take `⟨t', ht', hto'⟩` from `exists_smul_le m hM'fg (N := M) hback`. Set `f : M →ₗ[A] M'` to `LinearMap.codRestrict M' (t • M.subtype) (fun x => by simpa using hto x x.2)`.

Set `g : M' →ₗ[A] M` to `LinearMap.codRestrict M (t' • M'.subtype) (fun y => by simpa using hto' y y.2)`. Use `⟨M', inferInstance, inferInstance, Module.Projective.of_free, f, g, t' * t, fun h => (hm.mem_or_mem h).elim ht' ht, fun x => ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[f, g, smul_smul]`.
-/
theorem factor_of_frame (hA : Function.Injective (algebraMap A Ω)) (m : Ideal A) [hm : m.IsPrime] (R : Subring Ω)
    (hR : ∀ r ∈ R, ∃ t ∉ m, ∃ a : A, algebraMap A Ω t * r = algebraMap A Ω a) (M : Submodule A V) (hM : M.FG)
    {r : ℕ} (b : Fin r → V) (hb : LinearIndependent Ω b)
    (he : Submodule.span R (M : Set V) = Submodule.span R (Set.range b)) :
    ∃ (N : Type) (_ : AddCommGroup N) (_ : Module A N) (_ : Module.Projective A N)
      (f : M →ₗ[A] N) (g : N →ₗ[A] M) (t : A), t ∉ m ∧ ∀ x, g (f x) = t • x := by
  have h1 : (1 : A) ∉ m := fun h => hm.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hbA : LinearIndependent A b := by
    refine hb.restrict_scalars ?_
    intro x y hxy
    apply hA
    simpa [Algebra.smul_def] using hxy
  set M' := Submodule.span A (Set.range b) with hM'
  haveI : Module.Free A M' := Module.Free.of_basis (Module.Basis.span hbA)
  have hM'fg : M'.FG := Submodule.fg_span (Set.finite_range b)
  obtain ⟨t, ht, hto⟩ := exists_smul_le m hM (N := M') (fun x hx => exists_smul_mem m R hR M' (by
    have hx' : x ∈ Submodule.span R (Set.range b) := he ▸ Submodule.subset_span hx
    exact Submodule.span_mono (Submodule.subset_span (R := A)) hx'))
  have hback : ∀ y ∈ M', ∃ s ∉ m, s • y ∈ M := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      refine exists_smul_mem m R hR M ?_
      rw [he]
      exact Submodule.subset_span hz
    | zero => exact ⟨1, h1, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨t1, ht1, hy1⟩ := hy
      obtain ⟨t2, ht2, hz2⟩ := hz
      refine ⟨t1 * t2, fun h => (hm.mem_or_mem h).elim ht1 ht2, ?_⟩
      rw [smul_add]
      apply M.add_mem
      · rw [mul_comm, mul_smul]
        exact M.smul_mem _ hy1
      · rw [mul_smul]
        exact M.smul_mem _ hz2
    | smul a y _ hy =>
      obtain ⟨s, hs, hsy⟩ := hy
      exact ⟨s, hs, by rw [smul_comm]; exact M.smul_mem _ hsy⟩
  obtain ⟨t', ht', hto'⟩ := exists_smul_le m hM'fg (N := M) hback
  let f : M →ₗ[A] M' := LinearMap.codRestrict M' (t • M.subtype) (fun x => by simpa using hto x x.2)
  let g : M' →ₗ[A] M := LinearMap.codRestrict M (t' • M'.subtype) (fun y => by simpa using hto' y y.2)
  refine ⟨M', inferInstance, inferInstance, Module.Projective.of_free, f, g, t' * t,
    fun h => (hm.mem_or_mem h).elim ht' ht, fun x => ?_⟩
  apply Subtype.ext
  simp [f, g, smul_smul]

end Sub

/- English proof (translation)
Use `set D := differentIdeal ℤ (𝓞 E) with hD`. Establish `hD0 : D ≠ ⊥` using `differentIdeal_ne_bot`. Establish `hp0 : (p : 𝓞 E) ≠ 0` using `by exact_mod_cast hp.out.ne_zero`. Take `⟨a, ha⟩` from `IsDedekindDomain.exists_sup_span_eq (I := D * Ideal.span {(p : 𝓞 E)}) (J := D) Ideal.mul_le_left (by`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.mul_eq_bot, not_or]`.

Conclude with `⟨hD0, by rwa [Ideal.span_singleton_eq_bot]⟩)`. Choose the witnesses or unpack the hypotheses as in `⟨δ, hδD, hδ0, hsup⟩ : ∃ δ ∈ D, δ ≠ 0 ∧ D * Ideal.span {(p : 𝓞 E)} ⊔ Ideal.span {δ} = D := by`. Distinguish the cases in `ha0 : a = 0`. Take `⟨d, hdD, hd0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hD0`. Use `⟨d, hdD, hd0, ?_⟩` and prove the remaining obligations.

Rewrite `ha` using `[ha0, Ideal.span_singleton_eq_bot.mpr rfl, sup_bot_eq]`. Rewrite using `[ha]`. Conclude with `sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hdD)`. Use `⟨a, ?_, ha0, ha⟩` and prove the remaining obligations. Rewrite using `[← ha]`.

Conclude with `Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)`. Establish `hdec : ∀ x ∈ D, ∃ y ∈ D, ∃ z, x = (p : 𝓞 E) * y + z * δ`. Introduce `x hx`. Rewrite `hx` using `[← hsup, Submodule.mem_sup]`. Take `⟨u, hu, v, hv, rfl⟩` from `hx`.

Take `⟨y, hy, rfl⟩` from `(Submodule.mem_mul_span_singleton).mp hu`. Take `⟨z, rfl⟩` from `Ideal.mem_span_singleton'.mp hv`. Conclude with `⟨y, hy, z, by ring⟩`. Establish `hfin : Finite (𝓞 E ⧸ Ideal.span {δ})` using `Ring.HasFiniteQuotients.finiteQuotient (by rwa [Ne, Ideal.span_singleton_eq_bot])`. Use `set H := D.map (Ideal.Quotient.mk (Ideal.span {δ})) with hH`.

Establish `hsurj : Function.Surjective (fun h : H => (p : ℕ) • h)`. Introduce and unpack `⟨h, hh⟩`. Take `⟨x, hx, rfl⟩` from `(Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hh`. Take `⟨y, hy, z, rfl⟩` from `hdec x hx`. Use `⟨⟨Ideal.Quotient.mk _ y, Ideal.mem_map_of_mem _ hy⟩, ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton'.mpr ⟨z, rfl⟩), nsmul_eq_mul]`. Establish `hinj : Function.Injective (fun h : H => (p : ℕ) • h)` using `Finite.injective_iff_surjective.mpr hsurj`. Use `⟨δ, hδD, (Nat.card H : ℤ), ?_, ?_⟩` and prove the remaining obligations. Introduce `hdvd`.

Establish `hdvd' : p ∣ Nat.card H` using `by exact_mod_cast hdvd`. Take `⟨g, hg⟩` from `exists_prime_addOrderOf_dvd_card' (G := H) p hdvd'`. Establish `h1 : (p : ℕ) • g = (p : ℕ) • (0 : H)` using `by rw [smul_zero, ← hg, addOrderOf_nsmul_eq_zero]`. Establish `h2` using `hinj h1`. Rewrite `hg` using `[h2, addOrderOf_zero]`.

Conclude with `hp.out.ne_one hg.symm`. Introduce `x hx`. Establish `hm : Ideal.Quotient.mk (Ideal.span {δ}) x ∈ H` using `Ideal.mem_map_of_mem _ hx`. Establish `h0 : Nat.card H • (⟨_, hm⟩ : H) = 0` using `card_nsmul_eq_zero'`. Establish `h0' : Ideal.Quotient.mk (Ideal.span {δ}) ((Nat.card H : ℤ) * x) = 0`.

Use `congrArg Subtype.val h0` as an intermediate fact. Simplify `this` using `[nsmul_eq_mul]`. Take `⟨z, hz⟩` from `Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp h0')`. Conclude with `⟨z, hz.symm⟩`.
-/
theorem exists_diff_gen (E : Type) [Field E] [NumberField E] (p : ℕ) [hp : Fact p.Prime] :
    ∃ δ ∈ differentIdeal ℤ (𝓞 E), ∃ r : ℤ, ¬ (p : ℤ) ∣ r ∧ ∀ x ∈ differentIdeal ℤ (𝓞 E), ∃ z, (r : 𝓞 E) * x = z * δ := by
  classical
  set D := differentIdeal ℤ (𝓞 E) with hD
  have hD0 : D ≠ ⊥ := differentIdeal_ne_bot
  have hp0 : (p : 𝓞 E) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq (I := D * Ideal.span {(p : 𝓞 E)}) (J := D)
    Ideal.mul_le_left (by
      rw [Ne, Ideal.zero_eq_bot, Ideal.mul_eq_bot, not_or]
      exact ⟨hD0, by rwa [Ideal.span_singleton_eq_bot]⟩)
  obtain ⟨δ, hδD, hδ0, hsup⟩ : ∃ δ ∈ D, δ ≠ 0 ∧ D * Ideal.span {(p : 𝓞 E)} ⊔ Ideal.span {δ} = D := by
    by_cases ha0 : a = 0
    · obtain ⟨d, hdD, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD0
      refine ⟨d, hdD, hd0, ?_⟩
      rw [ha0, Ideal.span_singleton_eq_bot.mpr rfl, sup_bot_eq] at ha
      rw [ha]
      exact sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hdD)
    · refine ⟨a, ?_, ha0, ha⟩
      rw [← ha]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  have hdec : ∀ x ∈ D, ∃ y ∈ D, ∃ z, x = (p : 𝓞 E) * y + z * δ := by
    intro x hx
    rw [← hsup, Submodule.mem_sup] at hx
    obtain ⟨u, hu, v, hv, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_mul_span_singleton).mp hu
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.mp hv
    exact ⟨y, hy, z, by ring⟩
  have hfin : Finite (𝓞 E ⧸ Ideal.span {δ}) :=
    Ring.HasFiniteQuotients.finiteQuotient (by rwa [Ne, Ideal.span_singleton_eq_bot])
  set H := D.map (Ideal.Quotient.mk (Ideal.span {δ})) with hH
  have hsurj : Function.Surjective (fun h : H => (p : ℕ) • h) := by
    rintro ⟨h, hh⟩
    obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hh
    obtain ⟨y, hy, z, rfl⟩ := hdec x hx
    refine ⟨⟨Ideal.Quotient.mk _ y, Ideal.mem_map_of_mem _ hy⟩, ?_⟩
    apply Subtype.ext
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton'.mpr ⟨z, rfl⟩), nsmul_eq_mul]
  have hinj : Function.Injective (fun h : H => (p : ℕ) • h) := Finite.injective_iff_surjective.mpr hsurj
  refine ⟨δ, hδD, (Nat.card H : ℤ), ?_, ?_⟩
  · intro hdvd
    have hdvd' : p ∣ Nat.card H := by exact_mod_cast hdvd
    obtain ⟨g, hg⟩ := exists_prime_addOrderOf_dvd_card' (G := H) p hdvd'
    have h1 : (p : ℕ) • g = (p : ℕ) • (0 : H) := by rw [smul_zero, ← hg, addOrderOf_nsmul_eq_zero]
    have h2 := hinj h1
    rw [h2, addOrderOf_zero] at hg
    exact hp.out.ne_one hg.symm
  · intro x hx
    have hm : Ideal.Quotient.mk (Ideal.span {δ}) x ∈ H := Ideal.mem_map_of_mem _ hx
    have h0 : Nat.card H • (⟨_, hm⟩ : H) = 0 := card_nsmul_eq_zero'
    have h0' : Ideal.Quotient.mk (Ideal.span {δ}) ((Nat.card H : ℤ) * x) = 0 := by
      have := congrArg Subtype.val h0
      simpa [nsmul_eq_mul] using this
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp h0')
    exact ⟨z, hz.symm⟩

/- English proof (translation)
Take `⟨y, hy, hint⟩` from `exists_integral_multiples ℤ ℚ (Finset.univ.image (dualInt E))`. Use `⟨y, hy, fun k => ?_⟩` and prove the remaining obligations. Establish `hk` using `hint (dualInt E k) (Finset.mem_image_of_mem _ (Finset.mem_univ k))`. Use `⟨⟨y • dualInt E k, hk⟩, ?_⟩` and prove the remaining obligations. Use `show (y : E) * dualInt E k = y • dualInt E k`.

Rewrite using `[zsmul_eq_mul]`.
-/
theorem exists_den (E : Type) [Field E] [NumberField E] :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ k, ∃ z : 𝓞 E, (n : E) * dualInt E k = z := by
  classical
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image (dualInt E))
  refine ⟨y, hy, fun k => ?_⟩
  have hk := hint (dualInt E k) (Finset.mem_image_of_mem _ (Finset.mem_univ k))
  refine ⟨⟨y • dualInt E k, hk⟩, ?_⟩
  show (y : E) * dualInt E k = y • dualInt E k
  rw [zsmul_eq_mul]

/- English proof (translation)
Use `haveI : CharZero Ω := (RingHom.charZero_iff σ.injective).mp inferInstance`. Set `Φ : (E →+* ℂ) → (E →+* Ω)` to `fun τ => j.comp (τ.codRestrict F (hF τ))`. Establish `hinj : Function.Injective Φ`. Introduce `τ₁ τ₂ h`. Use extensionality with `a`.

Establish `h1` using `RingHom.congr_fun h a`. Establish `h2` using `j.injective h1`. Simplify using `using congrArg Subtype.val h2`. Establish `hle : Fintype.card (E →+* Ω) ≤ Module.finrank ℚ E`. Rewrite using `[← Nat.card_eq_fintype_card, Nat.card_congr (RingHom.equivRatAlgHom E Ω)]`.

Conclude with `card_algHom_le_finrank ℚ E Ω`. Establish `hcard : Fintype.card (E →+* ℂ) = Fintype.card (E →+* Ω)`. Apply `le_antisymm (Fintype.card_le_of_injective Φ hinj)` to reduce the goal to its premises. Rewrite using `[NumberField.Embeddings.card E ℂ]`. Conclude with `hle`.

Take `⟨τ, hτ⟩` from `((Fintype.bijective_iff_injective_and_card Φ).mpr ⟨hinj, hcard⟩).2 σ`. Conclude with `⟨τ, hτ.symm⟩`.
-/
theorem exists_emb (E : Type) [Field E] [NumberField E] (F : IntermediateField ℚ ℂ)
    (hF : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F) {Ω : Type} [Field Ω] (j : F →+* Ω) (σ : E →+* Ω) :
    ∃ τ : E →+* ℂ, σ = j.comp (τ.codRestrict F (hF τ)) := by
  classical
  haveI : CharZero Ω := (RingHom.charZero_iff σ.injective).mp inferInstance
  let Φ : (E →+* ℂ) → (E →+* Ω) := fun τ => j.comp (τ.codRestrict F (hF τ))
  have hinj : Function.Injective Φ := by
    intro τ₁ τ₂ h
    ext a
    have h1 := RingHom.congr_fun h a
    have h2 := j.injective h1
    simpa using congrArg Subtype.val h2
  have hle : Fintype.card (E →+* Ω) ≤ Module.finrank ℚ E := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr (RingHom.equivRatAlgHom E Ω)]
    exact card_algHom_le_finrank ℚ E Ω
  have hcard : Fintype.card (E →+* ℂ) = Fintype.card (E →+* Ω) := by
    apply le_antisymm (Fintype.card_le_of_injective Φ hinj)
    rw [NumberField.Embeddings.card E ℂ]
    exact hle
  obtain ⟨τ, hτ⟩ := ((Fintype.bijective_iff_injective_and_card Φ).mpr ⟨hinj, hcard⟩).2 σ
  exact ⟨τ, hτ.symm⟩

section Chart

variable {A Ω : Type} [CommRing A] [Field Ω] [Algebra A Ω] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ} {V : Type} [AddCommGroup V] [Module Ω V] [Module A V] [IsScalarTower A Ω V]
  (D : HTChart A Ω c p R N V)

/- English proof (translation)
Use `sup_le (Submodule.span_le.2 ?_) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `D.h_mem x`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `D.om.smul_mem _ hx`.
-/
theorem om'_le : D.om' ≤ D.om := by
  refine sup_le (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨x, rfl⟩; exact D.h_mem x
  · rintro _ ⟨x, hx, rfl⟩; exact D.om.smul_mem _ hx

/- English proof (translation)
The claim follows from `Submodule.mem_sup_right ⟨x, hx, rfl⟩`.
-/
theorem smul_mem_om' {x : V} (hx : x ∈ D.om) : ((p : A) ^ R) • x ∈ D.om' :=
  Submodule.mem_sup_right ⟨x, hx, rfl⟩

/- English proof (translation)
Conclude with `Submodule.FG.of_le D.om_lat.fg (om'_le D)`.
-/
theorem om'_fg [IsNoetherianRing A] : D.om'.FG := by
  exact Submodule.FG.of_le D.om_lat.fg (om'_le D)

/- English proof (translation)
Assemble the required witnesses or components as `⟨D.om, inferInstance, inferInstance, D.om_proj, Submodule.inclusion (om'_le D), (((p : A) ^ R) • LinearMap.id : V →ₗ[A] V).restrict fun _ hx => smul_mem_om' D hx, (p : A) ^ R, fun h => hp (hm.mem_of_pow_mem _ h), fun _ => rfl⟩`.
-/
theorem factor_om' (m : Ideal A) [hm : m.IsPrime] (hp : (p : A) ∉ m) :
    ∃ (N : Type) (_ : AddCommGroup N) (_ : Module A N) (_ : Module.Projective A N)
      (f : D.om' →ₗ[A] N) (g : N →ₗ[A] D.om') (t : A), t ∉ m ∧ ∀ x, g (f x) = t • x :=
  ⟨D.om, inferInstance, inferInstance, D.om_proj, Submodule.inclusion (om'_le D),
    (((p : A) ^ R) • LinearMap.id : V →ₗ[A] V).restrict fun _ hx => smul_mem_om' D hx, (p : A) ^ R,
    fun h => hp (hm.mem_of_pow_mem _ h), fun _ => rfl⟩

/- English proof (translation)
Establish `hd : ∀ i, Algebra.trace ℚ E (integralBasis E i * dualInt E k) = if i = k then 1 else 0`. Introduce `i`. Use `(Algebra.traceForm ℚ E).apply_dualBasis_right (traceForm_nondegenerate ℚ E) (Algebra.traceForm_isSymm ℚ) (integralBasis E) i k` as an intermediate fact. Simplify `this` using `[dualInt, Algebra.traceForm_apply]`. Use `conv_rhs => rw [← (integralBasis E).sum_repr z]`.

Rewrite using `[Finset.sum_mul, map_sum]`. Simplify using `only [smul_mul_assoc, map_smul, hd, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.
-/
private theorem integralBasis_repr_eq_trace_mul_dualInt (z : E) (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    (integralBasis E).repr z k = Algebra.trace ℚ E (z * dualInt E k) := by
  classical
  have hd : ∀ i, Algebra.trace ℚ E (integralBasis E i * dualInt E k) = if i = k then 1 else 0 := by
    intro i
    have := (Algebra.traceForm ℚ E).apply_dualBasis_right (traceForm_nondegenerate ℚ E)
      (Algebra.traceForm_isSymm ℚ) (integralBasis E) i k
    simpa [dualInt, Algebra.traceForm_apply] using this
  conv_rhs => rw [← (integralBasis E).sum_repr z]
  rw [Finset.sum_mul, map_sum]
  simp only [smul_mul_assoc, map_smul, hd, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/- English proof (translation)
Establish `key : ∀ y : E, Algebra.traceForm ℚ E (∑ k, dualInt E k * integralBasis E k - 1) y = 0`. Introduce `y`. Rewrite using `[Algebra.traceForm_apply, sub_mul, one_mul, map_sub, Finset.sum_mul, map_sum, Algebra.trace_eq_matrix_trace (integralBasis E) y, Matrix.trace, sub_eq_zero]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `k _`.

Rewrite using `[Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, integralBasis_repr_eq_trace_mul_dualInt]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Conclude with `sub_eq_zero.mp ((traceForm_nondegenerate ℚ E).1 _ key)`.
-/
private theorem sum_dualInt_mul_integralBasis_eq_one : ∑ k, dualInt E k * integralBasis E k = 1 := by
  classical
  have key : ∀ y : E, Algebra.traceForm ℚ E (∑ k, dualInt E k * integralBasis E k - 1) y = 0 := by
    intro y
    rw [Algebra.traceForm_apply, sub_mul, one_mul, map_sub, Finset.sum_mul, map_sum,
      Algebra.trace_eq_matrix_trace (integralBasis E) y, Matrix.trace, sub_eq_zero]
    apply Finset.sum_congr rfl
    intro k _
    rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, integralBasis_repr_eq_trace_mul_dualInt]
    congr 1
    ring
  exact sub_eq_zero.mp ((traceForm_nondegenerate ℚ E).1 _ key)

/- English proof (translation)
Use `set db := (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) (integralBasis E)`. Establish `hdb : ∀ l, dualInt E l = db l` using `fun l => rfl`. Use `conv_lhs => rw [← db.sum_repr ((a : E) * dualInt E j)]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `l _`.

Rewrite using `[LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, ← hdb]`. Establish `ht : Algebra.trace ℚ E ((a : E) * dualInt E j * integralBasis E l) = ((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E l) j : ℚ)`. Rewrite using `[show (a : E) * dualInt E j * integralBasis E l = ((a : E) * integralBasis E l) * dualInt E j by ring, ← integralBasis_repr_eq_trace_mul_dualInt, integralBasis_apply, show (a : E) = algebraMap (𝓞 E) E a from rfl, ← map_mul, integralBasis_repr_apply]`. Simplify using the standard rewrite rules. Rewrite using `[ht, Algebra.smul_def]`.

Simplify using the standard rewrite rules.
-/
private theorem coe_mul_dualInt_eq_sum (a : 𝓞 E) (j : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    (a : E) * dualInt E j = ∑ l, ((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E l) j : E) *
      dualInt E l := by
  classical
  set db := (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) (integralBasis E)
  have hdb : ∀ l, dualInt E l = db l := fun l => rfl
  conv_lhs => rw [← db.sum_repr ((a : E) * dualInt E j)]
  apply Finset.sum_congr rfl
  intro l _
  rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, ← hdb]
  have ht : Algebra.trace ℚ E ((a : E) * dualInt E j * integralBasis E l) =
      ((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E l) j : ℚ) := by
    rw [show (a : E) * dualInt E j * integralBasis E l = ((a : E) * integralBasis E l) * dualInt E j by ring,
      ← integralBasis_repr_eq_trace_mul_dualInt, integralBasis_apply, show (a : E) = algebraMap (𝓞 E) E a from rfl, ← map_mul,
      integralBasis_repr_apply]
    simp
  rw [ht, Algebra.smul_def]
  simp

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Unfold `eigProj`. Rewrite using `[Finset.mul_sum]`. Simplify using `only [mul_smul_comm, map_mul]`. Use `_ = ∑ l, σ (dualInt E l) • ∑ j, ((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E l) j : K) • ρ (RingOfIntegers.basis E j) := by`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `l _`. Use `conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr (a * RingOfIntegers.basis E l)]`. Simplify using `only [map_sum, map_zsmul, Int.cast_smul_eq_zsmul]`. Use `_ = ∑ j, (∑ l, ((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E l) j : K) * σ (dualInt E l)) • ρ (RingOfIntegers.basis E j) := by`.

Simplify using `only [Finset.smul_sum, smul_smul, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `j _`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `l _`. Rewrite using `[mul_comm]`. Use `_ = ∑ j, (σ (a : E) * σ (dualInt E j)) • ρ (RingOfIntegers.basis E j) := by`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `j _`.

Rewrite using `[← map_mul, coe_mul_dualInt_eq_sum, map_sum]`. Simplify using `only [map_mul, map_intCast]`. Use `_ = σ (a : E) • eigProj ρ σ := by`. Unfold `eigProj`. Rewrite using `[Finset.smul_sum]`.

Simplify using `only [smul_smul]`.
-/
private theorem rho_mul_eigProj' {K L : Type} [Field K] [AddCommGroup L] [Module K L]
    (ρ : 𝓞 E →+* Module.End K L) (σ : E →+* K) (a : 𝓞 E) :
    ρ a * eigProj ρ σ = σ (a : E) • eigProj ρ σ := by
  classical
  calc ρ a * eigProj ρ σ = ∑ l, σ (dualInt E l) • ρ (a * RingOfIntegers.basis E l) := by
        unfold eigProj
        rw [Finset.mul_sum]
        simp only [mul_smul_comm, map_mul]
    _ = ∑ l, σ (dualInt E l) • ∑ j, ((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E l) j : K) •
          ρ (RingOfIntegers.basis E j) := by
        apply Finset.sum_congr rfl
        intro l _
        conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr (a * RingOfIntegers.basis E l)]
        simp only [map_sum, map_zsmul, Int.cast_smul_eq_zsmul]
    _ = ∑ j, (∑ l, ((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E l) j : K) * σ (dualInt E l)) •
          ρ (RingOfIntegers.basis E j) := by
        simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro l _
        rw [mul_comm]
    _ = ∑ j, (σ (a : E) * σ (dualInt E j)) • ρ (RingOfIntegers.basis E j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← map_mul, coe_mul_dualInt_eq_sum, map_sum]
        simp only [map_mul, map_intCast]
    _ = σ (a : E) • eigProj ρ σ := by
        unfold eigProj
        rw [Finset.smul_sum]
        simp only [smul_smul]

/- English proof (translation)
Unfold `eigProj`. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, hx, smul_smul]`. Rewrite using `[← Finset.sum_smul]`. Establish `h1 : ∑ k, σ (dualInt E k) * σ ((RingOfIntegers.basis E k : 𝓞 E) : E) = 1`. Rewrite using `[← map_one σ, ← sum_dualInt_mul_integralBasis_eq_one, map_sum]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `k _`. Rewrite using `[integralBasis_apply, map_mul]`. Rewrite using `[h1, one_smul]`.
-/
private theorem eigProj_eq_self_of_eigenvector {K L : Type} [Field K] [AddCommGroup L] [Module K L]
    (ρ : 𝓞 E →+* Module.End K L) (σ : E →+* K) (x : L) (hx : ∀ a : 𝓞 E, ρ a x = σ (a : E) • x) :
    eigProj ρ σ x = x := by
  classical
  unfold eigProj
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, hx, smul_smul]
  rw [← Finset.sum_smul]
  have h1 : ∑ k, σ (dualInt E k) * σ ((RingOfIntegers.basis E k : 𝓞 E) : E) = 1 := by
    rw [← map_one σ, ← sum_dualInt_mul_integralBasis_eq_one, map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [integralBasis_apply, map_mul]
  rw [h1, one_smul]

/- English proof (translation)
Apply `eigProj_eq_self_of_eigenvector` to reduce the goal to its premises. Introduce `a`. Rewrite using `[← Module.End.mul_apply, rho_mul_eigProj']`. Both sides reduce to the same expression.
-/
private theorem eigProj_idem {K L : Type} [Field K] [AddCommGroup L] [Module K L]
    (ρ : 𝓞 E →+* Module.End K L) (σ : E →+* K) (x : L) :
    eigProj ρ σ (eigProj ρ σ x) = eigProj ρ σ x := by
  apply eigProj_eq_self_of_eigenvector
  intro a
  rw [← Module.End.mul_apply, rho_mul_eigProj']
  rfl

/- English proof (translation)
Take `⟨N', _, _, _, f', g', t', ht', hfg'⟩` from `factor_om' D m hp`. Establish `hst : ∀ (a : 𝓞 E), ∀ x ∈ D.om', D.ρΩ a x ∈ D.om'`. Introduce `a x hx`. Unfold `HTChart.om' at hx ⊢`. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.mp hx`.

Use `clear hx`. Rewrite using `[map_add]`. Apply `Submodule.add_mem` to reduce the goal to its premises. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem w hw`.

Take `⟨x', rfl⟩` from `hw`. Take `⟨y', hy', he⟩` from `D.h_lin a x'`. Establish `hrw : D.ρΩ a (D.h x') = D.h (a • x') - p ^ R • y'`. Rewrite using `[he]`. Normalize the expressions using the abelian group laws.

Rewrite using `[hrw]`. Apply `Submodule.sub_mem` to reduce the goal to its premises. Conclude with `Submodule.mem_sup_left (Submodule.subset_span ⟨_, rfl⟩)`. Apply `Submodule.mem_sup_right` to reduce the goal to its premises. Use `⟨y', hy', ?_⟩` and prove the remaining obligations.

Simplify using `only [LinearMap.smul_apply, LinearMap.id_apply, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]`. Consider the case `zero => simp`. Consider the case `add u v _ _ hu hv`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ hu hv`.

Consider the case `smul c u _ hu`. Rewrite using `[LinearMap.map_smul_of_tower]`. Conclude with `Submodule.smul_mem _ c hu`. Take `⟨z', hz', rfl⟩` from `hz`. Apply `Submodule.mem_sup_right` to reduce the goal to its premises.

Use `⟨D.ρΩ a z', D.om_stable a z' hz', ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.smul_apply, LinearMap.id_apply, LinearMap.map_smul_of_tower]`. Establish `hP : ∀ x ∈ D.om', t • eigProj D.ρΩ σ x ∈ D.om'`. Introduce `x hx`. Unfold `eigProj`.

Rewrite using `[LinearMap.sum_apply, Finset.smul_sum]`. Apply `Submodule.sum_mem` to reduce the goal to its premises. Introduce `k _`. Take `⟨a, ha⟩` from `hσ k`. Rewrite using `[LinearMap.smul_apply, ← algebraMap_smul Ω t, smul_smul, ← ha, algebraMap_smul]`.

Conclude with `Submodule.smul_mem _ a (hst _ x hx)`. Establish `hmem : ∀ x : D.omHT σ, ∃ y ∈ D.om', eigProj D.ρΩ σ y = (x : V)`. Introduce and unpack `⟨x, hx⟩`. Simplify using `only [HTChart.omHT, eigQuot, Submodule.mem_map] at hx`. Take `⟨y, hy, rfl⟩` from `hx`.

Conclude with `⟨y, hy, rfl⟩`. Establish `hf1 : ∀ x : D.omHT σ, (t • (D.omHT σ).subtype) x ∈ D.om'`. Introduce `x`. Take `⟨y, hy, hyx⟩` from `hmem x`. Rewrite using `[LinearMap.smul_apply, Submodule.subtype_apply, ← hyx]`.

Conclude with `hP y hy`. Establish `hg1 : ∀ y : D.om', (((eigProj D.ρΩ σ).restrictScalars A).comp D.om'.subtype) y ∈ D.omHT σ` using `fun y => Submodule.mem_map_of_mem y.2`. Use `⟨N', inferInstance, inferInstance, inferInstance, f'.comp (LinearMap.codRestrict D.om' (t • (D.omHT σ).subtype) hf1), (LinearMap.codRestrict (D.omHT σ) (((eigProj D.ρΩ σ).restrictScalars A).comp D.om'.subtype) hg1).comp g', t' * t, fun h => ?_, fun x => ?_⟩` and prove the remaining obligations. Break down `hm.mem_or_mem h with h | h exacts [ht' h, ht h]` into its components or cases. Apply `Subtype.ext` to reduce the goal to its premises.

Take `⟨y, hy, hyx⟩` from `hmem x`. Establish `hx : eigProj D.ρΩ σ (x : V) = x`. Rewrite using `[← hyx, eigProj_idem]`. Simplify using `only [LinearMap.comp_apply, hfg', map_smul, LinearMap.codRestrict_apply, Submodule.coe_smul, LinearMap.smul_apply, Submodule.subtype_apply, LinearMap.restrictScalars_apply, LinearMap.map_smul_of_tower, hx, mul_smul]`.
-/
theorem factor_omHT (m : Ideal A) [hm : m.IsPrime] (hp : (p : A) ∉ m) (σ : E →+* Ω) (t : A) (ht : t ∉ m)
    (hσ : ∀ k, algebraMap A Ω t * σ (dualInt E k) ∈ (algebraMap A Ω).range) :
    ∃ (N : Type) (_ : AddCommGroup N) (_ : Module A N) (_ : Module.Projective A N)
      (f : D.omHT σ →ₗ[A] N) (g : N →ₗ[A] D.omHT σ) (t : A), t ∉ m ∧ ∀ x, g (f x) = t • x := by
  classical
  obtain ⟨N', _, _, _, f', g', t', ht', hfg'⟩ := factor_om' D m hp
  have hst : ∀ (a : 𝓞 E), ∀ x ∈ D.om', D.ρΩ a x ∈ D.om' := by
    intro a x hx
    unfold HTChart.om' at hx ⊢
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    clear hx
    rw [map_add]
    apply Submodule.add_mem
    · induction hy using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨x', rfl⟩ := hw
        obtain ⟨y', hy', he⟩ := D.h_lin a x'
        have hrw : D.ρΩ a (D.h x') = D.h (a • x') - p ^ R • y' := by
          rw [he]
          abel
        rw [hrw]
        apply Submodule.sub_mem
        · exact Submodule.mem_sup_left (Submodule.subset_span ⟨_, rfl⟩)
        · apply Submodule.mem_sup_right
          refine ⟨y', hy', ?_⟩
          simp only [LinearMap.smul_apply, LinearMap.id_apply, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
      | zero => simp
      | add u v _ _ hu hv =>
        rw [map_add]
        exact Submodule.add_mem _ hu hv
      | smul c u _ hu =>
        rw [LinearMap.map_smul_of_tower]
        exact Submodule.smul_mem _ c hu
    · obtain ⟨z', hz', rfl⟩ := hz
      apply Submodule.mem_sup_right
      refine ⟨D.ρΩ a z', D.om_stable a z' hz', ?_⟩
      simp only [LinearMap.smul_apply, LinearMap.id_apply, LinearMap.map_smul_of_tower]
  have hP : ∀ x ∈ D.om', t • eigProj D.ρΩ σ x ∈ D.om' := by
    intro x hx
    unfold eigProj
    rw [LinearMap.sum_apply, Finset.smul_sum]
    apply Submodule.sum_mem
    intro k _
    obtain ⟨a, ha⟩ := hσ k
    rw [LinearMap.smul_apply, ← algebraMap_smul Ω t, smul_smul, ← ha, algebraMap_smul]
    exact Submodule.smul_mem _ a (hst _ x hx)
  have hmem : ∀ x : D.omHT σ, ∃ y ∈ D.om', eigProj D.ρΩ σ y = (x : V) := by
    rintro ⟨x, hx⟩
    simp only [HTChart.omHT, eigQuot, Submodule.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, hy, rfl⟩
  have hf1 : ∀ x : D.omHT σ, (t • (D.omHT σ).subtype) x ∈ D.om' := by
    intro x
    obtain ⟨y, hy, hyx⟩ := hmem x
    rw [LinearMap.smul_apply, Submodule.subtype_apply, ← hyx]
    exact hP y hy
  have hg1 : ∀ y : D.om', (((eigProj D.ρΩ σ).restrictScalars A).comp D.om'.subtype) y ∈ D.omHT σ :=
    fun y => Submodule.mem_map_of_mem y.2
  refine ⟨N', inferInstance, inferInstance, inferInstance,
    f'.comp (LinearMap.codRestrict D.om' (t • (D.omHT σ).subtype) hf1),
    (LinearMap.codRestrict (D.omHT σ) (((eigProj D.ρΩ σ).restrictScalars A).comp D.om'.subtype) hg1).comp g',
    t' * t, fun h => ?_, fun x => ?_⟩
  · rcases hm.mem_or_mem h with h | h
    exacts [ht' h, ht h]
  · apply Subtype.ext
    obtain ⟨y, hy, hyx⟩ := hmem x
    have hx : eigProj D.ρΩ σ (x : V) = x := by
      rw [← hyx, eigProj_idem]
    simp only [LinearMap.comp_apply, hfg', map_smul, LinearMap.codRestrict_apply, Submodule.coe_smul,
      LinearMap.smul_apply, Submodule.subtype_apply, LinearMap.restrictScalars_apply,
      LinearMap.map_smul_of_tower, hx, mul_smul]

end Chart

/- English proof (translation)
Simplify using `[eigProj, h]`.
-/
theorem eigProj_dual {Ω L : Type} [Field Ω] [AddCommGroup L] [Module Ω L] {E : Type} [Field E] [NumberField E]
    (ρ : 𝓞 E →+* Module.End Ω L) (ρ' : 𝓞 E →+* Module.End Ω (Module.Dual Ω L))
    (h : ∀ a w, ρ' a w = w ∘ₗ ρ a) (σ : E →+* Ω) (w : Module.Dual Ω L) (e : L) :
    eigProj ρ' σ w e = w (eigProj ρ σ e) := by
  simp [eigProj, h]

/- English proof (translation)
Unfold `eigQuot`. Use `set F := (eigProj ρ' σ).restrictScalars A with hF`. Use `set G := W.dualRestrict.restrictScalars A with hG`. Establish `hker : ∀ w : Module.Dual Ω L, F w = 0 ↔ G w = 0`. Introduce `w`.

Prove the components needed by the constructor for the conclusion. Introduce `hw`. Use extensionality with `⟨x, hx⟩`. Establish `hxW : ∀ a : 𝓞 E, ρ a x = σ (a : E) • x`. Introduce `a`.

Rewrite `hx` using `[hW]`. Use `(Submodule.mem_iInf _).mp hx a` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]`. Simplify using `using this`. Establish `h1` using `congrArg (fun f : Module.Dual Ω L => f x) hw`.

Simplify using `only [hF, LinearMap.restrictScalars_apply, eigProj_dual ρ ρ' h σ w x, eigProj_eq_self_of_eigenvector ρ σ x hxW, LinearMap.zero_apply] at h1`. Simplify `h1` using `[hG, Submodule.dualRestrict_apply]`. Introduce `hw`. Use extensionality with `e`. Simplify using `only [hF, LinearMap.restrictScalars_apply, eigProj_dual ρ ρ' h σ w e, LinearMap.zero_apply]`.

Establish `hPe : eigProj ρ σ e ∈ W`. Rewrite using `[hW]`. Apply `(Submodule.mem_iInf _).mpr` to reduce the goal to its premises. Introduce `a`. Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, ← Module.End.mul_apply, rho_mul_eigProj']`.

Simplify using the standard rewrite rules. Use `congrArg (fun f : Module.Dual Ω W => f ⟨_, hPe⟩) hw` as an intermediate fact. Simplify `this` using `[hG, Submodule.dualRestrict_apply]`. Establish `hk : LinearMap.ker (F.comp X.subtype) = LinearMap.ker (G.comp X.subtype)`. Use extensionality with `x`.

Simplify using `only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply]`. Conclude with `hker x`. Establish `h1 : LinearMap.range (F.comp X.subtype) = X.map F`. Rewrite using `[LinearMap.range_comp, Submodule.range_subtype]`. Establish `h2 : LinearMap.range (G.comp X.subtype) = X.map G`.

Rewrite using `[LinearMap.range_comp, Submodule.range_subtype]`. Conclude with `⟨(LinearEquiv.ofEq _ _ h1.symm).trans ((F.comp X.subtype).quotKerEquivRange.symm.trans ((Submodule.quotEquivOfEq _ _ hk).trans ((G.comp X.subtype).quotKerEquivRange.trans (LinearEquiv.ofEq _ _ h2))))⟩`.
-/
theorem nonempty_equiv_dual {A Ω L : Type} [CommRing A] [Field Ω] [Algebra A Ω] [AddCommGroup L] [Module Ω L]
    {E : Type} [Field E] [NumberField E] (ρ : 𝓞 E →+* Module.End Ω L) (ρ' : 𝓞 E →+* Module.End Ω (Module.Dual Ω L))
    (h : ∀ a w, ρ' a w = w ∘ₗ ρ a) (σ : E →+* Ω) (X : Submodule A (Module.Dual Ω L)) (W : Submodule Ω L)
    (hW : W = eigSp ρ σ) :
    Nonempty (eigQuot ρ' σ X ≃ₗ[A] X.map (W.dualRestrict.restrictScalars A)) := by
  classical
  unfold eigQuot
  set F := (eigProj ρ' σ).restrictScalars A with hF
  set G := W.dualRestrict.restrictScalars A with hG
  have hker : ∀ w : Module.Dual Ω L, F w = 0 ↔ G w = 0 := by
    intro w
    constructor
    · intro hw
      ext ⟨x, hx⟩
      have hxW : ∀ a : 𝓞 E, ρ a x = σ (a : E) • x := by
        intro a
        rw [hW] at hx
        have := (Submodule.mem_iInf _).mp hx a
        rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
        simpa using this
      have h1 := congrArg (fun f : Module.Dual Ω L => f x) hw
      simp only [hF, LinearMap.restrictScalars_apply, eigProj_dual ρ ρ' h σ w x, eigProj_eq_self_of_eigenvector ρ σ x hxW,
        LinearMap.zero_apply] at h1
      simpa [hG, Submodule.dualRestrict_apply] using h1
    · intro hw
      ext e
      simp only [hF, LinearMap.restrictScalars_apply, eigProj_dual ρ ρ' h σ w e, LinearMap.zero_apply]
      have hPe : eigProj ρ σ e ∈ W := by
        rw [hW]
        apply (Submodule.mem_iInf _).mpr
        intro a
        rw [LinearMap.mem_ker, LinearMap.sub_apply, ← Module.End.mul_apply, rho_mul_eigProj']
        simp
      have := congrArg (fun f : Module.Dual Ω W => f ⟨_, hPe⟩) hw
      simpa [hG, Submodule.dualRestrict_apply] using this
  have hk : LinearMap.ker (F.comp X.subtype) = LinearMap.ker (G.comp X.subtype) := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply]
    exact hker x
  have h1 : LinearMap.range (F.comp X.subtype) = X.map F := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have h2 : LinearMap.range (G.comp X.subtype) = X.map G := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  exact ⟨(LinearEquiv.ofEq _ _ h1.symm).trans ((F.comp X.subtype).quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ hk).trans ((G.comp X.subtype).quotKerEquivRange.trans
      (LinearEquiv.ofEq _ _ h2))))⟩

end PositivityTheory.HtPt.Famproj
