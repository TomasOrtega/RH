import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsConstantsDescend
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Polynomial

namespace ConstantsDescend

section Fibre

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/- English proof (translation)
Rewrite using `[aeval_map_algebraMap]`. Conclude with `aeval_algHom_apply (Ideal.Quotient.mkₐ A (I.map (algebraMap A B))) θ P`.
-/
theorem aeval_mk_map (θ : B) (I : Ideal A) (P : A[X]) :
    aeval (Ideal.Quotient.mk (I.map (algebraMap A B)) θ) (P.map (algebraMap A (A ⧸ I))) =
      Ideal.Quotient.mk (I.map (algebraMap A B)) (aeval θ P) := by
  rw [aeval_map_algebraMap]
  exact aeval_algHom_apply (Ideal.Quotient.mkₐ A (I.map (algebraMap A B))) θ P

/- English proof (translation)
Use `letI : Field (A ⧸ I) := Ideal.Quotient.field I`. Set `f : A[X] →+* B` to `(aeval θ).toRingHom`. Establish `hf : Function.Surjective f`. Introduce `b`. Establish `hb : b ∈ Algebra.adjoin A {θ}` using `hgen ▸ Algebra.mem_top`.

Rewrite `hb` using `[Algebra.adjoin_singleton_eq_range_aeval]`. Take `⟨P, rfl⟩` from `hb`. Conclude with `⟨P, rfl⟩`. Set `g : A[X] →+* ℂ` to `eval₂RingHom (σ.comp (Ideal.Quotient.mk I)) β`. Establish `hg : ∀ P : A[X], g P = ((P.map (algebraMap A (A ⧸ I))).map σ).eval β`.

Introduce `P`. Rewrite using `[eval_map, eval₂_map, Ideal.Quotient.algebraMap_eq]`. Both sides reduce to the same expression. Establish `hker : RingHom.ker f ≤ RingHom.ker g`. Introduce `P hP`.

Rewrite `hP`, the goal using `[RingHom.mem_ker]`. Establish `h1 : aeval (Ideal.Quotient.mk (I.map (algebraMap A B)) θ) (P.map (algebraMap A (A ⧸ I))) = 0`. Rewrite using `[aeval_mk_map]`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ (f P) = 0`. Rewrite using `[hP, map_zero]`.

Take `⟨r, hr⟩` from `minpoly.dvd _ _ h1`. Rewrite using `[hg, hr, Polynomial.map_mul, eval_mul, hβ.eq_zero, zero_mul]`. Choose the witnesses or unpack the hypotheses as in `⟨w, hw⟩ : ∃ w : B →+* ℂ, ∀ P, w (f P) = g P := by`. Use `⟨(Ideal.Quotient.lift (RingHom.ker f) g hker).comp (RingHom.quotientKerEquivOfSurjective hf).symm.toRingHom, fun P => ?_⟩` and prove the remaining obligations. Establish `he : (RingHom.quotientKerEquivOfSurjective hf).symm (f P) = Ideal.Quotient.mk (RingHom.ker f) P`.

Rewrite using `[RingEquiv.symm_apply_eq]`. Both sides reduce to the same expression. Simplify using `only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, he]`. Conclude with `Ideal.Quotient.lift_mk _ _ _`. Use `⟨w, ?_, ?_⟩` and prove the remaining obligations.

Use extensionality with `a`. Use `hw (C a)` as an intermediate fact. Simplify using `only [f, g, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, coe_eval₂RingHom, eval₂_C] at this`. Simplify using `using this`. Use `hw X` as an intermediate fact.

Simplify `this` using `[f, g]`.
-/
theorem exists_ringHom_of_root (θ : B) (hgen : Algebra.adjoin A {θ} = ⊤) (I : Ideal A) [I.IsMaximal]
    (σ : A ⧸ I →+* ℂ) (β : ℂ)
    (hβ : ((minpoly (A ⧸ I) (Ideal.Quotient.mk (I.map (algebraMap A B)) θ)).map σ).IsRoot β) :
    ∃ w : B →+* ℂ, w.comp (algebraMap A B) = σ.comp (Ideal.Quotient.mk I) ∧ w θ = β := by
  classical
  letI : Field (A ⧸ I) := Ideal.Quotient.field I
  let f : A[X] →+* B := (aeval θ).toRingHom
  have hf : Function.Surjective f := by
    intro b
    have hb : b ∈ Algebra.adjoin A {θ} := hgen ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hb
    obtain ⟨P, rfl⟩ := hb
    exact ⟨P, rfl⟩
  let g : A[X] →+* ℂ := eval₂RingHom (σ.comp (Ideal.Quotient.mk I)) β
  have hg : ∀ P : A[X], g P = ((P.map (algebraMap A (A ⧸ I))).map σ).eval β := by
    intro P
    rw [eval_map, eval₂_map, Ideal.Quotient.algebraMap_eq]
    rfl
  have hker : RingHom.ker f ≤ RingHom.ker g := by
    intro P hP
    rw [RingHom.mem_ker] at hP ⊢
    have h1 : aeval (Ideal.Quotient.mk (I.map (algebraMap A B)) θ) (P.map (algebraMap A (A ⧸ I))) = 0 := by
      rw [aeval_mk_map]
      change Ideal.Quotient.mk _ (f P) = 0
      rw [hP, map_zero]
    obtain ⟨r, hr⟩ := minpoly.dvd _ _ h1
    rw [hg, hr, Polynomial.map_mul, eval_mul, hβ.eq_zero, zero_mul]
  obtain ⟨w, hw⟩ : ∃ w : B →+* ℂ, ∀ P, w (f P) = g P := by
    refine ⟨(Ideal.Quotient.lift (RingHom.ker f) g hker).comp
      (RingHom.quotientKerEquivOfSurjective hf).symm.toRingHom, fun P => ?_⟩
    have he : (RingHom.quotientKerEquivOfSurjective hf).symm (f P) = Ideal.Quotient.mk (RingHom.ker f) P := by
      rw [RingEquiv.symm_apply_eq]
      rfl
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, he]
    exact Ideal.Quotient.lift_mk _ _ _
  refine ⟨w, ?_, ?_⟩
  · ext a
    have := hw (C a)
    simp only [f, g, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, coe_eval₂RingHom, eval₂_C] at this
    simpa using this
  · have := hw X
    simpa [f, g] using this

variable [Algebra ℚ A] [Algebra.FiniteType ℚ A]

/- English proof (translation)
Use `set J := I.map (algebraMap A B) with hJ`. Use `letI : Field (A ⧸ I) := Ideal.Quotient.field I`. Use `haveI : Nontrivial (B ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hI`. Use `haveI : Algebra.FiniteType ℚ (A ⧸ I) := Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℚ I) (Ideal.Quotient.mkₐ_surjective ℚ I)`. Use `haveI : Module.Finite ℚ (A ⧸ I) := finite_of_finite_type_of_isJacobsonRing ℚ (A ⧸ I)`.

Use `haveI : Algebra.IsAlgebraic ℚ (A ⧸ I) := Algebra.IsAlgebraic.of_finite ℚ _`. Set `σ : A ⧸ I →ₐ[ℚ] ℂ` to `IsAlgClosed.lift`. Use `set θ' := Ideal.Quotient.mk J θ with hθ'def`. Establish `hpF : p.map (algebraMap ℚ (A ⧸ I)) = (p.map (algebraMap ℚ A)).map (algebraMap A (A ⧸ I))`. Rewrite using `[Polynomial.map_map, ← IsScalarTower.algebraMap_eq]`.

Establish `hθ' : aeval θ' (p.map (algebraMap ℚ (A ⧸ I))) = 0`. Rewrite using `[hpF, hθ'def, aeval_mk_map, hp, map_zero]`. Establish `hint : IsIntegral (A ⧸ I) θ'` using `⟨_, hpm.map _, hθ'⟩`. Establish `hmem : θ' ∈ (algebraMap (A ⧸ I) (B ⧸ J)).range`. Assume the negation of the conclusion as `hn`.

Establish `h2` using `(minpoly.two_le_natDegree_iff hint).2 hn`. Use `set q := (minpoly (A ⧸ I) θ').map (σ : A ⧸ I →+* ℂ) with hq`. Establish `hs1 : (p.map (algebraMap ℚ (A ⧸ I))).Separable` using `hps.map`. Establish `hs2 : (minpoly (A ⧸ I) θ').Separable` using `hs1.of_dvd (minpoly.dvd _ _ hθ')`. Establish `hsep : q.Separable` using `hs2.map`.

Establish `hq0 : q ≠ 0` using `(Polynomial.map_ne_zero (minpoly.ne_zero hint))`. Establish `hcard : q.roots.toFinset.card = (minpoly (A ⧸ I) θ').natDegree`. Rewrite using `[Multiset.toFinset_card_of_nodup (nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree, natDegree_map]`. Take `⟨β₁, h₁, β₂, h₂, hne⟩` from `Finset.one_lt_card.1 (by omega : 1 < q.roots.toFinset.card)`. Rewrite `h₁`, `h₂` using `[Multiset.mem_toFinset, mem_roots hq0]`.

Take `⟨w₁, hw₁, hθ₁⟩` from `exists_ringHom_of_root θ hgen I σ β₁ h₁`. Take `⟨w₂, hw₂, hθ₂⟩` from `exists_ringHom_of_root θ hgen I σ β₂ h₂`. Conclude with `hne (hθ₁ ▸ hθ₂ ▸ huniq w₁ w₂ (hw₁.trans hw₂.symm))`. Set `S : Subalgebra A B` to `(⊥ : Subalgebra A (B ⧸ J)).comap (Ideal.Quotient.mkₐ A J)`. Establish `hθS : θ ∈ S`.

Take `⟨c, hc⟩` from `hmem`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective c`. Use `show Ideal.Quotient.mkₐ A J θ ∈ (⊥ : Subalgebra A (B ⧸ J))`. Establish `he : Ideal.Quotient.mkₐ A J θ = algebraMap A (B ⧸ J) a`. Rewrite using `[Ideal.Quotient.mkₐ_eq_mk, ← hθ'def, ← hc, Ideal.Quotient.algebraMap_quotient_map_quotient, Ideal.Quotient.mk_algebraMap]`.

Rewrite using `[he]`. Conclude with `Subalgebra.algebraMap_mem _ a`. Establish `hbS : b ∈ S`. Establish `: Algebra.adjoin A {θ} ≤ S` using `Algebra.adjoin_le (Set.singleton_subset_iff.2 hθS)`. Conclude with `this (hgen ▸ Algebra.mem_top)`.

Take `⟨a, ha⟩` from `Algebra.mem_bot.1 hbS`. Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq]`. Establish `he : Ideal.Quotient.mk J b = algebraMap A (B ⧸ J) a` using `ha.symm`. Rewrite using `[he, Ideal.Quotient.mk_algebraMap]`.
-/
theorem exists_sub_mem_map (θ : B) (hgen : Algebra.adjoin A {θ} = ⊤) (p : ℚ[X]) (hpm : p.Monic)
    (hps : p.Separable) (hp : aeval θ (p.map (algebraMap ℚ A)) = 0)
    (huniq : ∀ w w' : B →+* ℂ, w.comp (algebraMap A B) = w'.comp (algebraMap A B) → w θ = w' θ)
    (I : Ideal A) [I.IsMaximal] (hI : I.map (algebraMap A B) ≠ ⊤) (b : B) :
    ∃ a : A, b - algebraMap A B a ∈ I.map (algebraMap A B) := by
  classical
  set J := I.map (algebraMap A B) with hJ
  letI : Field (A ⧸ I) := Ideal.Quotient.field I
  haveI : Nontrivial (B ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hI
  haveI : Algebra.FiniteType ℚ (A ⧸ I) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℚ I) (Ideal.Quotient.mkₐ_surjective ℚ I)
  haveI : Module.Finite ℚ (A ⧸ I) := finite_of_finite_type_of_isJacobsonRing ℚ (A ⧸ I)
  haveI : Algebra.IsAlgebraic ℚ (A ⧸ I) := Algebra.IsAlgebraic.of_finite ℚ _
  let σ : A ⧸ I →ₐ[ℚ] ℂ := IsAlgClosed.lift
  set θ' := Ideal.Quotient.mk J θ with hθ'def
  have hpF : p.map (algebraMap ℚ (A ⧸ I)) = (p.map (algebraMap ℚ A)).map (algebraMap A (A ⧸ I)) := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  have hθ' : aeval θ' (p.map (algebraMap ℚ (A ⧸ I))) = 0 := by
    rw [hpF, hθ'def, aeval_mk_map, hp, map_zero]
  have hint : IsIntegral (A ⧸ I) θ' := ⟨_, hpm.map _, hθ'⟩
  have hmem : θ' ∈ (algebraMap (A ⧸ I) (B ⧸ J)).range := by
    by_contra hn
    have h2 := (minpoly.two_le_natDegree_iff hint).2 hn
    set q := (minpoly (A ⧸ I) θ').map (σ : A ⧸ I →+* ℂ) with hq
    have hs1 : (p.map (algebraMap ℚ (A ⧸ I))).Separable := hps.map
    have hs2 : (minpoly (A ⧸ I) θ').Separable := hs1.of_dvd (minpoly.dvd _ _ hθ')
    have hsep : q.Separable := hs2.map
    have hq0 : q ≠ 0 := (Polynomial.map_ne_zero (minpoly.ne_zero hint))
    have hcard : q.roots.toFinset.card = (minpoly (A ⧸ I) θ').natDegree := by
      rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree,
        natDegree_map]
    obtain ⟨β₁, h₁, β₂, h₂, hne⟩ := Finset.one_lt_card.1 (by omega : 1 < q.roots.toFinset.card)
    rw [Multiset.mem_toFinset, mem_roots hq0] at h₁ h₂
    obtain ⟨w₁, hw₁, hθ₁⟩ := exists_ringHom_of_root θ hgen I σ β₁ h₁
    obtain ⟨w₂, hw₂, hθ₂⟩ := exists_ringHom_of_root θ hgen I σ β₂ h₂
    exact hne (hθ₁ ▸ hθ₂ ▸ huniq w₁ w₂ (hw₁.trans hw₂.symm))
  let S : Subalgebra A B := (⊥ : Subalgebra A (B ⧸ J)).comap (Ideal.Quotient.mkₐ A J)
  have hθS : θ ∈ S := by
    obtain ⟨c, hc⟩ := hmem
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    show Ideal.Quotient.mkₐ A J θ ∈ (⊥ : Subalgebra A (B ⧸ J))
    have he : Ideal.Quotient.mkₐ A J θ = algebraMap A (B ⧸ J) a := by
      rw [Ideal.Quotient.mkₐ_eq_mk, ← hθ'def, ← hc, Ideal.Quotient.algebraMap_quotient_map_quotient,
        Ideal.Quotient.mk_algebraMap]
    rw [he]
    exact Subalgebra.algebraMap_mem _ a
  have hbS : b ∈ S := by
    have : Algebra.adjoin A {θ} ≤ S := Algebra.adjoin_le (Set.singleton_subset_iff.2 hθS)
    exact this (hgen ▸ Algebra.mem_top)
  obtain ⟨a, ha⟩ := Algebra.mem_bot.1 hbS
  refine ⟨a, ?_⟩
  rw [← Ideal.Quotient.eq]
  have he : Ideal.Quotient.mk J b = algebraMap A (B ⧸ J) a := ha.symm
  rw [he, Ideal.Quotient.mk_algebraMap]

/- English proof (translation)
Establish `hθA : IsIntegral A θ` using `⟨p.map (algebraMap ℚ A), hpm.map _, hp⟩`. Use `haveI : Algebra.IsIntegral A B := ⟨fun b => adjoin_le_integralClosure hθA (hgen ▸ Algebra.mem_top : b ∈ Algebra.adjoin A {θ})⟩`. Use `haveI : Algebra.FiniteType A B := ⟨⟨{θ}, by simpa using hgen⟩⟩`. Use `haveI : Module.Finite A B := Algebra.finite_iff_isIntegral_and_finiteType.2 ⟨inferInstance, inferInstance⟩`. Use `set N := LinearMap.range (Algebra.linearMap A B) with hN`.

Establish `hann : Module.annihilator A (B ⧸ N) = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨I, hI, hle⟩` from `Ideal.exists_le_maximal _ hne`. Establish `hIB : I.map (algebraMap A B) ≠ ⊤`. Establish `hk : RingHom.ker (algebraMap A B) ≤ I`.

Rewrite using `[(RingHom.injective_iff_ker_eq_bot _).1 hinj]`. Conclude with `bot_le`. Take `⟨Q, hQ, hQI⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral I hk`. Introduce `htop`. Apply `hQ.ne_top` to reduce the goal to its premises.

Rewrite using `[eq_top_iff, ← htop, Ideal.map_le_iff_le_comap, hQI]`. Establish `hsmul : (⊤ : Submodule A (B ⧸ N)) ≤ I • ⊤`. Introduce and unpack `x -`. Take `⟨b, rfl⟩` from `Submodule.Quotient.mk_surjective N x`. Take `⟨a, ha⟩` from `exists_sub_mem_map θ hgen p hpm hps hp huniq I hIB b`.

Establish `h1 : b - algebraMap A B a ∈ I • (⊤ : Submodule A B)`. Rewrite using `[Ideal.smul_top_eq_map]`. Conclude with `ha`. Establish `h2 : N.mkQ (b - algebraMap A B a) ∈ I • (⊤ : Submodule A (B ⧸ N))`. Use `Submodule.mem_map_of_mem (f := N.mkQ) h1` as an intermediate fact.

Rewrite `this` using `[Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]`. Then use the resulting hypothesis. Establish `h3 : N.mkQ (algebraMap A B a) = 0` using `(Submodule.Quotient.mk_eq_zero N).2 ⟨a, rfl⟩`. Rewrite `h2` using `[map_sub, h3, sub_zero]`. Conclude with `h2`. Take `⟨r, hr1, hr⟩` from `Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I ⊤ (Module.finite_def.1 inferInstance) hsmul`.

Establish `hr' : r ∈ I` using `hle (Module.mem_annihilator.2 fun x => hr x Submodule.mem_top)`. Conclude with `hI.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using I.sub_mem hr' hr1))`. Introduce `b`. Establish `h1 : (1 : A) ∈ Module.annihilator A (B ⧸ N)` using `hann ▸ Submodule.mem_top`. Establish `h0 : (Submodule.Quotient.mk b : B ⧸ N) = 0`.

Simplify using `using Module.mem_annihilator.1 h1 (Submodule.Quotient.mk b)`. Take `⟨a, ha⟩` from `(Submodule.Quotient.mk_eq_zero N).1 h0`. Conclude with `⟨a, ha⟩`.
-/
theorem algebraMap_surjective (hinj : Function.Injective (algebraMap A B)) (θ : B)
    (hgen : Algebra.adjoin A {θ} = ⊤) (p : ℚ[X]) (hpm : p.Monic) (hps : p.Separable)
    (hp : aeval θ (p.map (algebraMap ℚ A)) = 0)
    (huniq : ∀ w w' : B →+* ℂ, w.comp (algebraMap A B) = w'.comp (algebraMap A B) → w θ = w' θ) :
    Function.Surjective (algebraMap A B) := by
  classical
  have hθA : IsIntegral A θ := ⟨p.map (algebraMap ℚ A), hpm.map _, hp⟩
  haveI : Algebra.IsIntegral A B :=
    ⟨fun b => adjoin_le_integralClosure hθA (hgen ▸ Algebra.mem_top : b ∈ Algebra.adjoin A {θ})⟩
  haveI : Algebra.FiniteType A B := ⟨⟨{θ}, by simpa using hgen⟩⟩
  haveI : Module.Finite A B := Algebra.finite_iff_isIntegral_and_finiteType.2 ⟨inferInstance, inferInstance⟩
  set N := LinearMap.range (Algebra.linearMap A B) with hN
  have hann : Module.annihilator A (B ⧸ N) = ⊤ := by
    by_contra hne
    obtain ⟨I, hI, hle⟩ := Ideal.exists_le_maximal _ hne
    have hIB : I.map (algebraMap A B) ≠ ⊤ := by
      have hk : RingHom.ker (algebraMap A B) ≤ I := by
        rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]
        exact bot_le
      obtain ⟨Q, hQ, hQI⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral I hk
      intro htop
      apply hQ.ne_top
      rw [eq_top_iff, ← htop, Ideal.map_le_iff_le_comap, hQI]
    have hsmul : (⊤ : Submodule A (B ⧸ N)) ≤ I • ⊤ := by
      rintro x -
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective N x
      obtain ⟨a, ha⟩ := exists_sub_mem_map θ hgen p hpm hps hp huniq I hIB b
      have h1 : b - algebraMap A B a ∈ I • (⊤ : Submodule A B) := by
        rw [Ideal.smul_top_eq_map]
        exact ha
      have h2 : N.mkQ (b - algebraMap A B a) ∈ I • (⊤ : Submodule A (B ⧸ N)) := by
        have := Submodule.mem_map_of_mem (f := N.mkQ) h1
        rwa [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at this
      have h3 : N.mkQ (algebraMap A B a) = 0 := (Submodule.Quotient.mk_eq_zero N).2 ⟨a, rfl⟩
      rw [map_sub, h3, sub_zero] at h2
      exact h2
    obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I ⊤
      (Module.finite_def.1 inferInstance) hsmul
    have hr' : r ∈ I := hle (Module.mem_annihilator.2 fun x => hr x Submodule.mem_top)
    exact hI.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using I.sub_mem hr' hr1))
  intro b
  have h1 : (1 : A) ∈ Module.annihilator A (B ⧸ N) := hann ▸ Submodule.mem_top
  have h0 : (Submodule.Quotient.mk b : B ⧸ N) = 0 := by
    simpa using Module.mem_annihilator.1 h1 (Submodule.Quotient.mk b)
  obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero N).1 h0
  exact ⟨a, ha⟩

end Fibre

/- English proof (translation)
Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx => exact ⟨1, one_pos, by simpa using hx⟩`. Consider the case `algebraMap q`. Use `⟨q.den, q.den_pos, ?_⟩` and prove the remaining obligations. Establish `: (q.den : Ω) * algebraMap ℚ Ω q = (q.num : Ω)`.

Rewrite using `[eq_ratCast, ← Rat.cast_natCast, ← Rat.cast_mul, mul_comm, Rat.mul_den_eq_num, Rat.cast_intCast]`. Rewrite using `[this]`. Conclude with `Subalgebra.intCast_mem R _`. Consider the case `add x y _ _ hx hy`. Take `⟨n₁, h₁, hx⟩` from `hx`.

Take `⟨n₂, h₂, hy⟩` from `hy`. Use `⟨n₁ * n₂, Nat.mul_pos h₁ h₂, ?_⟩` and prove the remaining obligations. Establish `: ((n₁ * n₂ : ℕ) : Ω) * (x + y) = (n₂ : Ω) * ((n₁ : Ω) * x) + (n₁ : Ω) * ((n₂ : Ω) * y)` using `by push_cast; ring`. Rewrite using `[this]`. Conclude with `R.add_mem (R.mul_mem (Subalgebra.natCast_mem R _) hx) (R.mul_mem (Subalgebra.natCast_mem R _) hy)`.

Consider the case `mul x y _ _ hx hy`. Take `⟨n₁, h₁, hx⟩` from `hx`. Take `⟨n₂, h₂, hy⟩` from `hy`. Use `⟨n₁ * n₂, Nat.mul_pos h₁ h₂, ?_⟩` and prove the remaining obligations. Establish `: ((n₁ * n₂ : ℕ) : Ω) * (x * y) = ((n₁ : Ω) * x) * ((n₂ : Ω) * y)` using `by push_cast; ring`.

Rewrite using `[this]`. Conclude with `R.mul_mem hx hy`.
-/
theorem exists_nat_mul_mem {Ω : Type*} [Field Ω] [CharZero Ω] (R : Subalgebra ℤ Ω) {x : Ω}
    (hx : x ∈ Algebra.adjoin ℚ (R : Set Ω)) : ∃ n : ℕ, 0 < n ∧ (n : Ω) * x ∈ R := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | algebraMap q =>
    refine ⟨q.den, q.den_pos, ?_⟩
    have : (q.den : Ω) * algebraMap ℚ Ω q = (q.num : Ω) := by
      rw [eq_ratCast, ← Rat.cast_natCast, ← Rat.cast_mul, mul_comm, Rat.mul_den_eq_num, Rat.cast_intCast]
    rw [this]
    exact Subalgebra.intCast_mem R _
  | add x y _ _ hx hy =>
    obtain ⟨n₁, h₁, hx⟩ := hx
    obtain ⟨n₂, h₂, hy⟩ := hy
    refine ⟨n₁ * n₂, Nat.mul_pos h₁ h₂, ?_⟩
    have : ((n₁ * n₂ : ℕ) : Ω) * (x + y) = (n₂ : Ω) * ((n₁ : Ω) * x) + (n₁ : Ω) * ((n₂ : Ω) * y) := by
      push_cast; ring
    rw [this]
    exact R.add_mem (R.mul_mem (Subalgebra.natCast_mem R _) hx) (R.mul_mem (Subalgebra.natCast_mem R _) hy)
  | mul x y _ _ hx hy =>
    obtain ⟨n₁, h₁, hx⟩ := hx
    obtain ⟨n₂, h₂, hy⟩ := hy
    refine ⟨n₁ * n₂, Nat.mul_pos h₁ h₂, ?_⟩
    have : ((n₁ * n₂ : ℕ) : Ω) * (x * y) = ((n₁ : Ω) * x) * ((n₂ : Ω) * y) := by
      push_cast; ring
    rw [this]
    exact R.mul_mem hx hy

/- English proof (translation)
Use `haveI : FiniteDimensional F (IntermediateField.adjoin F (S : Set Ω)) := IntermediateField.finiteDimensional_adjoin fun x hx => hS x hx`. Take `⟨α, hα⟩` from `Field.exists_primitive_element F (IntermediateField.adjoin F (S : Set Ω))`. Establish `hθint : IsIntegral F (α : Ω)` using `(IsIntegral.of_finite F α).map (IntermediateField.adjoin F (S : Set Ω)).val`. Establish `hK : IntermediateField.adjoin F {(α : Ω)} = IntermediateField.adjoin F (S : Set Ω)`. Simplify `congr_arg IntermediateField.lift hα` using `only [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top]`.

Use `⟨α, hθint, ?_, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h1 : (α : Ω) ∈ IntermediateField.adjoin F (S : Set Ω)` using `α.2`. Rewrite `h1` using `[← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (fun x hx => (hS x hx).isAlgebraic)]`. Conclude with `h1`. Rewrite `hx` using `[← hK, ← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (fun y hy => by rw [Set.mem_singleton_iff.1 hy]; exact hθint.isAlgebraic)]`.

Conclude with `hx`.
-/
theorem exists_primitive {F Ω : Type*} [Field F] [CharZero F] [Field Ω] [Algebra F Ω] (S : Finset Ω)
    (hS : ∀ s ∈ S, IsIntegral F s) :
    ∃ θ : Ω, IsIntegral F θ ∧ θ ∈ Algebra.adjoin F (S : Set Ω) ∧
      ∀ x ∈ IntermediateField.adjoin F (S : Set Ω), x ∈ Algebra.adjoin F {θ} := by
  haveI : FiniteDimensional F (IntermediateField.adjoin F (S : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin fun x hx => hS x hx
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F (IntermediateField.adjoin F (S : Set Ω))
  have hθint : IsIntegral F (α : Ω) := (IsIntegral.of_finite F α).map (IntermediateField.adjoin F (S : Set Ω)).val
  have hK : IntermediateField.adjoin F {(α : Ω)} = IntermediateField.adjoin F (S : Set Ω) := by
    simpa only [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top] using
      congr_arg IntermediateField.lift hα
  refine ⟨α, hθint, ?_, fun x hx => ?_⟩
  · have h1 : (α : Ω) ∈ IntermediateField.adjoin F (S : Set Ω) := α.2
    rw [← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
      (fun x hx => (hS x hx).isAlgebraic)] at h1
    exact h1
  · rw [← hK, ← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
      (fun y hy => by rw [Set.mem_singleton_iff.1 hy]; exact hθint.isAlgebraic)] at hx
    exact hx

/- English proof (translation)
Establish `hgen : Algebra.adjoin A {(⟨θ, Algebra.subset_adjoin rfl⟩ : Algebra.adjoin A {θ})} = ⊤`. Use `Algebra.adjoin_adjoin_coe_preimage (R := A) (s := ({θ} : Set Ω))` as an intermediate fact. Use `this using 2` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Simplify using `[Subtype.ext_iff]`.

Establish `hinj : Function.Injective (algebraMap A (Algebra.adjoin A {θ}))`. Introduce `x y h`. Apply `Subtype.ext` to reduce the goal to its premises. Use `congrArg (Algebra.adjoin A {θ}).val h` as an intermediate fact. Rewrite `this` using `[AlgHom.commutes, AlgHom.commutes]`.

Conclude with `this`. Establish `hpB : aeval (⟨θ, Algebra.subset_adjoin rfl⟩ : Algebra.adjoin A {θ}) ((minpoly ℚ θ).map (algebraMap ℚ A)) = 0`. Establish `h` using `aeval_algHom_apply (Algebra.adjoin A {θ}).val ⟨θ, Algebra.subset_adjoin rfl⟩ ((minpoly ℚ θ).map (algebraMap ℚ A))`. Rewrite `h` using `[aeval_map_algebraMap]`. Establish `h0 : (Algebra.adjoin A {θ}).val (aeval (⟨θ, Algebra.subset_adjoin rfl⟩ : Algebra.adjoin A {θ}) ((minpoly ℚ θ).map (algebraMap ℚ A))) = 0`.

Rewrite using `[← h]`. Conclude with `minpoly.aeval ℚ θ`. Conclude with `(map_eq_zero_iff _ Subtype.val_injective).1 h0`. Take `⟨a, ha⟩` from `algebraMap_surjective hinj _ hgen (minpoly ℚ θ) (minpoly.monic hθ) (minpoly.irreducible hθ).separable hpB huniq ⟨θ, Algebra.subset_adjoin rfl⟩`. Establish `h1 : (Algebra.adjoin A {θ}).val (algebraMap A _ a) = θ` using `congrArg Subtype.val ha`.

Rewrite `h1` using `[AlgHom.commutes]`. Rewrite using `[← h1]`. Conclude with `a.2`.
-/
theorem mem_of_unique_extension {Ω : Type*} [Field Ω] [CharZero Ω] (A : Subalgebra ℚ Ω) [Algebra.FiniteType ℚ A]
    (θ : Ω) (hθ : IsIntegral ℚ θ)
    (huniq : ∀ w w' : Algebra.adjoin A {θ} →+* ℂ,
      w.comp (algebraMap A (Algebra.adjoin A {θ})) = w'.comp (algebraMap A (Algebra.adjoin A {θ})) →
        w ⟨θ, Algebra.subset_adjoin rfl⟩ = w' ⟨θ, Algebra.subset_adjoin rfl⟩) :
    θ ∈ A := by
  have hgen : Algebra.adjoin A {(⟨θ, Algebra.subset_adjoin rfl⟩ : Algebra.adjoin A {θ})} = ⊤ := by
    have := Algebra.adjoin_adjoin_coe_preimage (R := A) (s := ({θ} : Set Ω))
    convert this using 2
    ext x
    simp [Subtype.ext_iff]
  have hinj : Function.Injective (algebraMap A (Algebra.adjoin A {θ})) := by
    intro x y h
    apply Subtype.ext
    have := congrArg (Algebra.adjoin A {θ}).val h
    rw [AlgHom.commutes, AlgHom.commutes] at this
    exact this
  have hpB : aeval (⟨θ, Algebra.subset_adjoin rfl⟩ : Algebra.adjoin A {θ})
      ((minpoly ℚ θ).map (algebraMap ℚ A)) = 0 := by
    have h := aeval_algHom_apply (Algebra.adjoin A {θ}).val ⟨θ, Algebra.subset_adjoin rfl⟩
      ((minpoly ℚ θ).map (algebraMap ℚ A))
    rw [aeval_map_algebraMap] at h
    have h0 : (Algebra.adjoin A {θ}).val (aeval (⟨θ, Algebra.subset_adjoin rfl⟩ : Algebra.adjoin A {θ})
        ((minpoly ℚ θ).map (algebraMap ℚ A))) = 0 := by
      rw [← h]
      exact minpoly.aeval ℚ θ
    exact (map_eq_zero_iff _ Subtype.val_injective).1 h0
  obtain ⟨a, ha⟩ := algebraMap_surjective hinj _ hgen (minpoly ℚ θ) (minpoly.monic hθ)
    (minpoly.irreducible hθ).separable hpB huniq ⟨θ, Algebra.subset_adjoin rfl⟩
  have h1 : (Algebra.adjoin A {θ}).val (algebraMap A _ a) = θ := congrArg Subtype.val ha
  rw [AlgHom.commutes] at h1
  rw [← h1]
  exact a.2

/- English proof (translation)
Establish `hTB : ∀ t ∈ T, t ∈ B` using `fun t ht => (Algebra.adjoin_le (Set.singleton_subset_iff.2 hθB) : Algebra.adjoin ℚ {θ} ≤ B.restrictScalars ℚ) (hTθ t ht)`. Establish `hsub : ∀ x ∈ R ⊔ T, x ∈ B`. Establish `: R ⊔ T ≤ B.restrictScalars ℤ` using `sup_le (fun r hr => B.algebraMap_mem (⟨r, hRA r hr⟩ : A)) (fun t ht => hTB t ht)`. Conclude with `fun x hx => this hx`. Set `ι : ↥(R ⊔ T) →+* B` to `((R ⊔ T).val : ↥(R ⊔ T) →ₐ[ℤ] Ω).toRingHom.codRestrict B fun x => hsub x.1 x.2`.

Establish `hR' : (w.comp ι).comp (Subalgebra.inclusion (le_sup_left : R ≤ R ⊔ T)).toRingHom = (w'.comp ι).comp (Subalgebra.inclusion (le_sup_left : R ≤ R ⊔ T)).toRingHom`. Use extensionality with `⟨r, hr⟩`. Conclude with `RingHom.congr_fun hw (⟨r, hRA r hr⟩ : A)`. Establish `hT'` using `H _ _ hR'`. Introduce `x hx`.

Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem t ht`. Use `Subring.mem_map.2 ⟨⟨t, hTB t ht⟩, ?_, rfl⟩` and prove the remaining obligations. Conclude with `RingHom.congr_fun hT' ⟨t, ht⟩`. Consider the case `algebraMap q`.

Use `Subring.mem_map.2 ⟨algebraMap A B (algebraMap ℚ A q), RingHom.congr_fun hw _, ?_⟩` and prove the remaining obligations. Conclude with `(B.val.commutes _).trans (IsScalarTower.algebraMap_apply ℚ A Ω q).symm`. Consider the case `add x y _ _ hx hy => exact Subring.add_mem _ hx hy`. Consider the case `mul x y _ _ hx hy => exact Subring.mul_mem _ hx hy`.
-/
theorem agree_on_adjoin {Ω : Type*} [Field Ω] [CharZero Ω] (R T : Subalgebra ℤ Ω) (A : Subalgebra ℚ Ω)
    (B : Subalgebra A Ω) (hRA : ∀ r ∈ R, r ∈ A) (θ : Ω) (hθB : θ ∈ B)
    (hTθ : ∀ t ∈ T, t ∈ Algebra.adjoin ℚ {θ})
    (H : ∀ w w' : ↥(R ⊔ T) →+* ℂ,
      w.comp (Subalgebra.inclusion (le_sup_left : R ≤ R ⊔ T)).toRingHom =
          w'.comp (Subalgebra.inclusion (le_sup_left : R ≤ R ⊔ T)).toRingHom →
        w.comp (Subalgebra.inclusion (le_sup_right : T ≤ R ⊔ T)).toRingHom =
          w'.comp (Subalgebra.inclusion (le_sup_right : T ≤ R ⊔ T)).toRingHom)
    (w w' : B →+* ℂ) (hw : w.comp (algebraMap A B) = w'.comp (algebraMap A B)) :
    ∀ x ∈ Algebra.adjoin ℚ (T : Set Ω), x ∈ (RingHom.eqLocus w w').map B.val.toRingHom := by
  have hTB : ∀ t ∈ T, t ∈ B := fun t ht =>
    (Algebra.adjoin_le (Set.singleton_subset_iff.2 hθB) : Algebra.adjoin ℚ {θ} ≤ B.restrictScalars ℚ) (hTθ t ht)
  have hsub : ∀ x ∈ R ⊔ T, x ∈ B := by
    have : R ⊔ T ≤ B.restrictScalars ℤ :=
      sup_le (fun r hr => B.algebraMap_mem (⟨r, hRA r hr⟩ : A)) (fun t ht => hTB t ht)
    exact fun x hx => this hx
  let ι : ↥(R ⊔ T) →+* B := ((R ⊔ T).val : ↥(R ⊔ T) →ₐ[ℤ] Ω).toRingHom.codRestrict B fun x => hsub x.1 x.2
  have hR' : (w.comp ι).comp (Subalgebra.inclusion (le_sup_left : R ≤ R ⊔ T)).toRingHom =
      (w'.comp ι).comp (Subalgebra.inclusion (le_sup_left : R ≤ R ⊔ T)).toRingHom := by
    ext ⟨r, hr⟩
    exact RingHom.congr_fun hw (⟨r, hRA r hr⟩ : A)
  have hT' := H _ _ hR'
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem t ht =>
    refine Subring.mem_map.2 ⟨⟨t, hTB t ht⟩, ?_, rfl⟩
    exact RingHom.congr_fun hT' ⟨t, ht⟩
  | algebraMap q =>
    refine Subring.mem_map.2 ⟨algebraMap A B (algebraMap ℚ A q), RingHom.congr_fun hw _, ?_⟩
    exact (B.val.commutes _).trans (IsScalarTower.algebraMap_apply ℚ A Ω q).symm
  | add x y _ _ hx hy => exact Subring.add_mem _ hx hy
  | mul x y _ _ hx hy => exact Subring.mul_mem _ hx hy

/- English proof (translation)
Introduce `Ω _ _ R T hR hT H`. Take `⟨S, hS⟩` from `(Module.Finite.iff_fg (N := Subalgebra.toSubmodule T)).1 hT`. Establish `hST : ∀ s ∈ S, s ∈ T` using `fun s hs => by`. Establish `: s ∈ Subalgebra.toSubmodule T` using `hS ▸ Submodule.subset_span hs`. Conclude with `this`.

Establish `hTspan : ∀ t ∈ T, t ∈ Submodule.span ℤ (S : Set Ω)` using `fun t ht => by`. Rewrite using `[hS]`. Conclude with `ht`. Establish `hintQ : ∀ s ∈ S, IsIntegral ℚ s` using `fun s hs => ((IsIntegral.of_finite ℤ (⟨s, hST s hs⟩ : T)).map T.val).tower_top`. Take `⟨θ, hθint, hθT', hKθ⟩` from `exists_primitive S hintQ`.

Establish `hθT : θ ∈ Algebra.adjoin ℚ (T : Set Ω)` using `Algebra.adjoin_mono (fun s hs => hST s hs) hθT'`. Establish `hTθ : ∀ t ∈ T, t ∈ Algebra.adjoin ℚ {θ}` using `fun t ht => hKθ t <| Submodule.span_induction (p := fun x _ => x ∈ IntermediateField.adjoin ℚ (S : Set Ω)) (fun x hx => IntermediateField.subset_adjoin ℚ _ hx) (IntermediateField.zero_mem _) (fun x y _ _ hx hy => IntermediateField.add_mem _ hx hy) (fun z x _ hx => zsmul_mem hx z) …`. Take `⟨s, hs⟩` from `hR`. Establish `hAfg : (Algebra.adjoin ℚ (R : Set Ω)).FG` using `⟨s, by rw [← hs, Algebra.adjoin_adjoin_of_tower]⟩`. Use `haveI : Algebra.FiniteType ℚ (Algebra.adjoin ℚ (R : Set Ω)) := (Subalgebra.fg_iff_finiteType _).1 hAfg`.

Establish `hθA : θ ∈ Algebra.adjoin ℚ (R : Set Ω)`. Use `mem_of_unique_extension _ θ hθint fun w w' hw => ?_` and prove the remaining obligations. Take `⟨y, hy, hyθ⟩` from `Subring.mem_map.1 (agree_on_adjoin R T _ (Algebra.adjoin (Algebra.adjoin ℚ (R : Set Ω)) {θ}) (fun r hr => Algebra.subset_adjoin hr) θ (Algebra.subset_adjoin (Set.mem_singleton θ)) hTθ H w w' hw θ hθT)`. Establish `: y = ⟨θ, Algebra.subset_adjoin rfl⟩` using `Subtype.ext hyθ`. Rewrite using `[← this]`.

Conclude with `hy`. Establish `hTA : ∀ t ∈ T, t ∈ Algebra.adjoin ℚ (R : Set Ω)` using `fun t ht => (Algebra.adjoin_le (Set.singleton_subset_iff.2 hθA) : Algebra.adjoin ℚ {θ} ≤ _) (hTθ t ht)`. Establish `hn : ∀ s ∈ S, ∃ n : ℕ, 0 < n ∧ (n : Ω) * s ∈ R` using `fun s hs => exists_nat_mul_mem R (hTA s (hST s hs))`. Use `choose! n hn0 hnR using hn`. Use `⟨∏ s ∈ S, n s, Finset.prod_pos hn0, fun t ht => ?_⟩` and prove the remaining obligations.

Use `Submodule.span_induction (p := fun x _ => ((∏ s ∈ S, n s : ℕ) : Ω) * x ∈ R) ?_ ?_ ?_ ?_ (hTspan t ht)` and prove the remaining obligations. Introduce `x hx`. Take `⟨k, hk⟩` from `Finset.dvd_prod_of_mem n hx`. Rewrite using `[hk, Nat.cast_mul, mul_comm ((n x : ℕ) : Ω), mul_assoc]`. Conclude with `R.mul_mem (Subalgebra.natCast_mem R k) (hnR x hx)`.

Simplify using the standard rewrite rules. Introduce `x y _ _ hx hy`. Rewrite using `[mul_add]`. Conclude with `R.add_mem hx hy`. Introduce `z x _ hx`.

Rewrite using `[mul_smul_comm]`. Conclude with `zsmul_mem hx z`.
-/
theorem proof : ConstantsDescend.Statement := by
  intro Ω _ _ R T hR hT H
  classical

  obtain ⟨S, hS⟩ := (Module.Finite.iff_fg (N := Subalgebra.toSubmodule T)).1 hT
  have hST : ∀ s ∈ S, s ∈ T := fun s hs => by
    have : s ∈ Subalgebra.toSubmodule T := hS ▸ Submodule.subset_span hs
    exact this
  have hTspan : ∀ t ∈ T, t ∈ Submodule.span ℤ (S : Set Ω) := fun t ht => by
    rw [hS]
    exact ht
  have hintQ : ∀ s ∈ S, IsIntegral ℚ s := fun s hs =>
    ((IsIntegral.of_finite ℤ (⟨s, hST s hs⟩ : T)).map T.val).tower_top

  obtain ⟨θ, hθint, hθT', hKθ⟩ := exists_primitive S hintQ
  have hθT : θ ∈ Algebra.adjoin ℚ (T : Set Ω) := Algebra.adjoin_mono (fun s hs => hST s hs) hθT'
  have hTθ : ∀ t ∈ T, t ∈ Algebra.adjoin ℚ {θ} := fun t ht => hKθ t <|
    Submodule.span_induction (p := fun x _ => x ∈ IntermediateField.adjoin ℚ (S : Set Ω))
      (fun x hx => IntermediateField.subset_adjoin ℚ _ hx) (IntermediateField.zero_mem _)
      (fun x y _ _ hx hy => IntermediateField.add_mem _ hx hy) (fun z x _ hx => zsmul_mem hx z) (hTspan t ht)

  obtain ⟨s, hs⟩ := hR
  have hAfg : (Algebra.adjoin ℚ (R : Set Ω)).FG := ⟨s, by rw [← hs, Algebra.adjoin_adjoin_of_tower]⟩
  haveI : Algebra.FiniteType ℚ (Algebra.adjoin ℚ (R : Set Ω)) := (Subalgebra.fg_iff_finiteType _).1 hAfg

  have hθA : θ ∈ Algebra.adjoin ℚ (R : Set Ω) := by
    refine mem_of_unique_extension _ θ hθint fun w w' hw => ?_
    obtain ⟨y, hy, hyθ⟩ := Subring.mem_map.1 (agree_on_adjoin R T _
      (Algebra.adjoin (Algebra.adjoin ℚ (R : Set Ω)) {θ}) (fun r hr => Algebra.subset_adjoin hr) θ
      (Algebra.subset_adjoin (Set.mem_singleton θ)) hTθ H w w' hw θ hθT)
    have : y = ⟨θ, Algebra.subset_adjoin rfl⟩ := Subtype.ext hyθ
    rw [← this]
    exact hy

  have hTA : ∀ t ∈ T, t ∈ Algebra.adjoin ℚ (R : Set Ω) := fun t ht =>
    (Algebra.adjoin_le (Set.singleton_subset_iff.2 hθA) : Algebra.adjoin ℚ {θ} ≤ _) (hTθ t ht)

  have hn : ∀ s ∈ S, ∃ n : ℕ, 0 < n ∧ (n : Ω) * s ∈ R := fun s hs => exists_nat_mul_mem R (hTA s (hST s hs))
  choose! n hn0 hnR using hn
  refine ⟨∏ s ∈ S, n s, Finset.prod_pos hn0, fun t ht => ?_⟩
  refine Submodule.span_induction (p := fun x _ => ((∏ s ∈ S, n s : ℕ) : Ω) * x ∈ R) ?_ ?_ ?_ ?_ (hTspan t ht)
  · intro x hx
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n hx
    rw [hk, Nat.cast_mul, mul_comm ((n x : ℕ) : Ω), mul_assoc]
    exact R.mul_mem (Subalgebra.natCast_mem R k) (hnR x hx)
  · simp
  · intro x y _ _ hx hy
    rw [mul_add]
    exact R.add_mem hx hy
  · intro z x _ hx
    rw [mul_smul_comm]
    exact zsmul_mem hx z

end ConstantsDescend

end GroundTheory.Heights₂.Heights.HilbertSamuel
