import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsNoetherianRingOfIsAdicComplete

open IsLocalRing

namespace GlobalTheory.DirectedNoeth

variable {S : Type} [CommRing S] [IsLocalRing S]

/- English proof (translation)
Use `set m : Ideal T := (maximalIdeal S).comap T.subtype with hm`. Establish `hjac : m ≤ Ideal.jacobson ⊥`. Introduce `y hy`. Rewrite using `[Ideal.mem_jacobson_bot]`. Introduce `z`.

Establish `hu : T.subtype (y * z + 1) ∉ maximalIdeal S`. Introduce `h`. Establish `h1 : T.subtype (y * z) ∈ maximalIdeal S`. Rewrite using `[map_mul]`. Conclude with `Ideal.mul_mem_right _ _ hy`.

Establish `h2` using `Ideal.sub_mem _ h h1`. Rewrite `h2` using `[map_add, add_sub_cancel_left, map_one]`. Conclude with `(maximalIdeal.isMaximal S).ne_top ((Ideal.eq_top_iff_one _).mpr h2)`. Establish `hunit : IsUnit (T.subtype (y * z + 1))`. Assume the negation of the conclusion as `h`.

Conclude with `hu ((mem_maximalIdeal _).mpr h)`. Establish `h2 : Ideal.span {y * z + 1} = (⊤ : Ideal T)`. Rewrite using `[← hpure (Ideal.span {y * z + 1}), Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_top.mpr hunit, Ideal.comap_top]`. Conclude with `Ideal.span_singleton_eq_top.mp h2`. Establish `hK` using `Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := T ⧸ A) m hjac`.

Establish `hxn : ∀ n : ℕ, x ∈ A ⊔ m ^ n`. Introduce `n`. Establish `h` using `hx n`. Rewrite `h` using `[← hmax, ← Ideal.map_pow, ← Ideal.map_sup]`. Rewrite using `[← hpure (A ⊔ m ^ n)]`.

Conclude with `h`. Establish `h0 : Ideal.Quotient.mk A x ∈ (⨅ i : ℕ, m ^ i • ⊤ : Submodule T (T ⧸ A))`. Rewrite using `[Submodule.mem_iInf]`. Introduce `n`. Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.mp (hxn n)`.

Establish `: Ideal.Quotient.mk A x = b • (1 : T ⧸ A)`. Rewrite using `[← hab, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem_smul hb trivial`. Rewrite `h0` using `[hK, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `h0`.
-/
theorem mem_of_forall_mem_sup_pow (T : Subring S) [IsNoetherianRing T]
    (hmax : ((maximalIdeal S).comap T.subtype).map T.subtype = maximalIdeal S)
    (hpure : ∀ J : Ideal T, (J.map T.subtype).comap T.subtype = J)
    (A : Ideal T) (x : T) (hx : ∀ n : ℕ, (x : S) ∈ A.map T.subtype ⊔ maximalIdeal S ^ n) :
    x ∈ A := by
  set m : Ideal T := (maximalIdeal S).comap T.subtype with hm
  have hjac : m ≤ Ideal.jacobson ⊥ := by
    intro y hy
    rw [Ideal.mem_jacobson_bot]
    intro z
    have hu : T.subtype (y * z + 1) ∉ maximalIdeal S := by
      intro h
      have h1 : T.subtype (y * z) ∈ maximalIdeal S := by
        rw [map_mul]; exact Ideal.mul_mem_right _ _ hy
      have h2 := Ideal.sub_mem _ h h1
      rw [map_add, add_sub_cancel_left, map_one] at h2
      exact (maximalIdeal.isMaximal S).ne_top ((Ideal.eq_top_iff_one _).mpr h2)
    have hunit : IsUnit (T.subtype (y * z + 1)) := by
      by_contra h
      exact hu ((mem_maximalIdeal _).mpr h)
    have h2 : Ideal.span {y * z + 1} = (⊤ : Ideal T) := by
      rw [← hpure (Ideal.span {y * z + 1}), Ideal.map_span, Set.image_singleton,
        Ideal.span_singleton_eq_top.mpr hunit, Ideal.comap_top]
    exact Ideal.span_singleton_eq_top.mp h2
  have hK := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := T ⧸ A) m hjac
  have hxn : ∀ n : ℕ, x ∈ A ⊔ m ^ n := by
    intro n
    have h := hx n
    rw [← hmax, ← Ideal.map_pow, ← Ideal.map_sup] at h
    rw [← hpure (A ⊔ m ^ n)]
    exact h
  have h0 : Ideal.Quotient.mk A x ∈ (⨅ i : ℕ, m ^ i • ⊤ : Submodule T (T ⧸ A)) := by
    rw [Submodule.mem_iInf]
    intro n
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (hxn n)
    have : Ideal.Quotient.mk A x = b • (1 : T ⧸ A) := by
      rw [← hab, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add, Algebra.smul_def,
        mul_one, Ideal.Quotient.algebraMap_eq]
    rw [this]
    exact Submodule.smul_mem_smul hb trivial
  rw [hK, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at h0
  exact h0

/- English proof (translation)
Establish `h` using `Ideal.mem_map_of_mem (AdicCompletion.evalₐ (maximalIdeal S) n).toRingHom hx`. Rewrite `h` using `[Ideal.map_map]`. Establish `hc : (AdicCompletion.evalₐ (maximalIdeal S) n).toRingHom.comp (algebraMap S (AdicCompletion (maximalIdeal S) S)) = Ideal.Quotient.mk _`. Use extensionality with `y`. Simplify using `[AlgHom.commutes, Ideal.Quotient.algebraMap_eq]`.

Rewrite `h` using `[hc]`. Establish `h' : Ideal.Quotient.mk (maximalIdeal S ^ n) x ∈ K.map (Ideal.Quotient.mk _)`. Establish `e : (AdicCompletion.evalₐ (maximalIdeal S) n).toRingHom (algebraMap S (AdicCompletion (maximalIdeal S) S) x) = Ideal.Quotient.mk _ x`. Rewrite using `[← RingHom.comp_apply, hc]`. Rewrite using `[← e]`.

Conclude with `h`. Rewrite `h'` using `[Ideal.mem_quotient_iff_mem_sup]`. Conclude with `h'`.
-/
theorem mem_sup_pow_of_algebraMap_mem (K : Ideal S) (x : S)
    (hx : algebraMap S (AdicCompletion (maximalIdeal S) S) x ∈
      K.map (algebraMap S (AdicCompletion (maximalIdeal S) S))) (n : ℕ) :
    x ∈ K ⊔ maximalIdeal S ^ n := by
  have h := Ideal.mem_map_of_mem (AdicCompletion.evalₐ (maximalIdeal S) n).toRingHom hx
  rw [Ideal.map_map] at h
  have hc : (AdicCompletion.evalₐ (maximalIdeal S) n).toRingHom.comp
      (algebraMap S (AdicCompletion (maximalIdeal S) S)) = Ideal.Quotient.mk _ := by
    ext y
    simp [AlgHom.commutes, Ideal.Quotient.algebraMap_eq]
  rw [hc] at h
  have h' : Ideal.Quotient.mk (maximalIdeal S ^ n) x ∈ K.map (Ideal.Quotient.mk _) := by
    have e : (AdicCompletion.evalₐ (maximalIdeal S) n).toRingHom
        (algebraMap S (AdicCompletion (maximalIdeal S) S) x) = Ideal.Quotient.mk _ x := by
      rw [← RingHom.comp_apply, hc]
    rw [← e]; exact h
  rw [Ideal.mem_quotient_iff_mem_sup] at h'
  exact h'

/- English proof (translation)
Use `GlobalTheory.AdicNoeth.isNoetherianRing_of_isAdicComplete _ ((maximalIdeal S).map (algebraMap S (AdicCompletion (maximalIdeal S) S))) (hfg.map _) (AdicCompletion.isAdicComplete_self _ hfg) ?_` and prove the remaining obligations. Rewrite using `[← AdicCompletion.ker_evalOneₐ_eq_map _ hfg]`. Use `letI := Ideal.Quotient.field (maximalIdeal S)`. Use `haveI : IsNoetherianRing (S ⧸ maximalIdeal S) := inferInstance`. Conclude with `isNoetherianRing_of_ringEquiv _ (RingHom.quotientKerEquivOfSurjective (f := (AdicCompletion.evalOneₐ (maximalIdeal S)).toRingHom) (AdicCompletion.evalOneₐ_surjective _)).symm`.
-/
theorem isNoetherianRing_completion (hfg : (maximalIdeal S).FG) :
    IsNoetherianRing (AdicCompletion (maximalIdeal S) S) := by
  refine GlobalTheory.AdicNoeth.isNoetherianRing_of_isAdicComplete _
    ((maximalIdeal S).map (algebraMap S (AdicCompletion (maximalIdeal S) S))) (hfg.map _)
    (AdicCompletion.isAdicComplete_self _ hfg) ?_
  rw [← AdicCompletion.ker_evalOneₐ_eq_map _ hfg]
  letI := Ideal.Quotient.field (maximalIdeal S)
  haveI : IsNoetherianRing (S ⧸ maximalIdeal S) := inferInstance
  exact isNoetherianRing_of_ringEquiv _
    (RingHom.quotientKerEquivOfSurjective (f := (AdicCompletion.evalOneₐ (maximalIdeal S)).toRingHom)
      (AdicCompletion.evalOneₐ_surjective _)).symm

end GlobalTheory.DirectedNoeth

namespace GlobalTheory

open GlobalTheory.DirectedNoeth in

/- English proof (translation)
Introduce `S _ _ ι _ _ _ R hmono hcov hnoeth hmax hpure`. Take `⟨i₁⟩` from `‹Nonempty ι›`. Establish `hfg : (maximalIdeal S).FG` using `by haveI := hnoeth i₁`. Rewrite using `[← hmax i₁]`. Conclude with `(Ideal.fg_of_isNoetherianRing _).map _`.

Use `haveI := isNoetherianRing_completion hfg`. Use `set f := algebraMap S (AdicCompletion (maximalIdeal S) S) with hf`. Use `⟨fun (I : Ideal S) => ?_⟩` and prove the remaining obligations. Set `E : ι → Ideal S` to `fun i => (I.comap (R i).subtype).map (R i).subtype`. Establish `hEI : ∀ i, E i ≤ I` using `fun i => Ideal.map_comap_le`.

Establish `hEmono : Monotone E`. Introduce `i j hij`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `y hy`. Establish `hyj : (y : S) ∈ R j` using `hmono hij y.2`.

Establish `: (⟨y, hyj⟩ : R j) ∈ I.comap (R j).subtype` using `hy`. Conclude with `Ideal.mem_map_of_mem (R j).subtype this`. Take `⟨_, ⟨i₀, rfl⟩, hmaxl⟩` from `set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian (AdicCompletion (maximalIdeal S) S) (AdicCompletion (maximalIdeal S) S)) (Set.range fun i => (E i).map f) (Set.range_nonempty _)`. Establish `hfg0 : (E i₀).FG` using `by haveI := hnoeth i₀`. Conclude with `(Ideal.fg_of_isNoetherianRing _).map _`.

It suffices to establish `hle : I ≤ E i₀ by rw [le_antisymm hle (hEI i₀)]; exact hfg0`. Introduce `x hx`. Take `⟨k, hk⟩` from `hcov x`. Take `⟨j, hkj, hij⟩` from `directed_of (· ≤ ·) k i₀`. Establish `hxj : x ∈ R j` using `hmono hkj hk`.

Establish `hEj : (E j).map f = (E i₀).map f`. Assume the negation of the conclusion as `hne`. Conclude with `hmaxl _ ⟨j, rfl⟩ (lt_of_le_of_ne (Ideal.map_mono (hEmono hij)) (Ne.symm hne))`. Establish `hfx : f x ∈ (E i₀).map f`. Rewrite using `[← hEj]`.

Apply `Ideal.mem_map_of_mem` to reduce the goal to its premises. Conclude with `Ideal.mem_map_of_mem (R j).subtype (show (⟨x, hxj⟩ : R j) ∈ I.comap (R j).subtype from hx)`. Establish `hij' : R i₀ ≤ R j` using `hmono hij`. Set `A : Ideal (R j)` to `(I.comap (R i₀).subtype).map (Subring.inclusion hij')`. Establish `hA : A.map (R j).subtype = E i₀`.

Simplify using `only [A, E, Ideal.map_map]`. Both sides reduce to the same expression. Establish `hxA : (⟨x, hxj⟩ : R j) ∈ A` using `by haveI := hnoeth j`. Apply `mem_of_forall_mem_sup_pow (R j) (hmax j) (hpure j) A` to reduce the goal to its premises. Introduce `n`.

Rewrite using `[hA]`. Conclude with `mem_sup_pow_of_algebraMap_mem (E i₀) x hfx n`. Use `Ideal.mem_map_of_mem (R j).subtype hxA` as an intermediate fact. Rewrite `this` using `[hA]`. Then use the resulting hypothesis.
-/
theorem isNoetherianRing_of_directed_pure_union : ∀ (S : Type) [CommRing S] [IsLocalRing S] (ι : Type)
    [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (R : ι → Subring S), Monotone R →
    (∀ x : S, ∃ i, x ∈ R i) → (∀ i, IsNoetherianRing (R i)) →
    (∀ i, ((maximalIdeal S).comap (R i).subtype).map (R i).subtype = maximalIdeal S) →
    (∀ i (J : Ideal (R i)), (J.map (R i).subtype).comap (R i).subtype = J) → IsNoetherianRing S := by
  intro S _ _ ι _ _ _ R hmono hcov hnoeth hmax hpure
  obtain ⟨i₁⟩ := ‹Nonempty ι›
  have hfg : (maximalIdeal S).FG := by
    haveI := hnoeth i₁
    rw [← hmax i₁]
    exact (Ideal.fg_of_isNoetherianRing _).map _
  haveI := isNoetherianRing_completion hfg
  set f := algebraMap S (AdicCompletion (maximalIdeal S) S) with hf
  refine ⟨fun (I : Ideal S) => ?_⟩
  let E : ι → Ideal S := fun i => (I.comap (R i).subtype).map (R i).subtype
  have hEI : ∀ i, E i ≤ I := fun i => Ideal.map_comap_le
  have hEmono : Monotone E := by
    intro i j hij
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    have hyj : (y : S) ∈ R j := hmono hij y.2
    have : (⟨y, hyj⟩ : R j) ∈ I.comap (R j).subtype := hy
    exact Ideal.mem_map_of_mem (R j).subtype this
  obtain ⟨_, ⟨i₀, rfl⟩, hmaxl⟩ := set_has_maximal_iff_noetherian.mpr
    (inferInstance : IsNoetherian (AdicCompletion (maximalIdeal S) S) (AdicCompletion (maximalIdeal S) S))
    (Set.range fun i => (E i).map f) (Set.range_nonempty _)
  have hfg0 : (E i₀).FG := by
    haveI := hnoeth i₀
    exact (Ideal.fg_of_isNoetherianRing _).map _
  suffices hle : I ≤ E i₀ by rw [le_antisymm hle (hEI i₀)]; exact hfg0
  intro x hx
  obtain ⟨k, hk⟩ := hcov x
  obtain ⟨j, hkj, hij⟩ := directed_of (· ≤ ·) k i₀
  have hxj : x ∈ R j := hmono hkj hk
  have hEj : (E j).map f = (E i₀).map f := by
    by_contra hne
    exact hmaxl _ ⟨j, rfl⟩ (lt_of_le_of_ne (Ideal.map_mono (hEmono hij)) (Ne.symm hne))
  have hfx : f x ∈ (E i₀).map f := by
    rw [← hEj]
    apply Ideal.mem_map_of_mem
    exact Ideal.mem_map_of_mem (R j).subtype (show (⟨x, hxj⟩ : R j) ∈ I.comap (R j).subtype from hx)
  have hij' : R i₀ ≤ R j := hmono hij
  let A : Ideal (R j) := (I.comap (R i₀).subtype).map (Subring.inclusion hij')
  have hA : A.map (R j).subtype = E i₀ := by
    simp only [A, E, Ideal.map_map]
    rfl
  have hxA : (⟨x, hxj⟩ : R j) ∈ A := by
    haveI := hnoeth j
    apply mem_of_forall_mem_sup_pow (R j) (hmax j) (hpure j) A
    intro n
    rw [hA]
    exact mem_sup_pow_of_algebraMap_mem (E i₀) x hfx n
  have := Ideal.mem_map_of_mem (R j).subtype hxA
  rwa [hA] at this

end GlobalTheory
