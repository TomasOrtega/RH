import Mathlib
import GroundTheory.AutomorphicForms.SmoothRep

noncomputable section

namespace GroundTheory.Automorphic

open Polynomial Cardinal

section Schur

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Apply `(bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)` to reduce the goal to its premises. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(⊥ : Submodule ℂ V) = ⊤`.

Use extensionality with `v`. Simplify using `[h v]`.
-/
theorem exists_ne_zero_of_isIrreducible [ρ.IsIrreducible] : ∃ v : V, v ≠ 0 := by
  by_contra h
  push Not at h
  apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
  apply Subrepresentation.toSubmodule_injective
  change (⊥ : Submodule ℂ V) = ⊤
  ext v
  simp [h v]

/- English proof (translation)
The claim follows from `((Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf).1`.
-/
theorem injective_of_ne_zero [ρ.IsIrreducible] {f : Representation.IntertwiningMap ρ ρ}
    (hf : f ≠ 0) : Function.Injective f :=
  ((Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf).1

/- English proof (translation)
Take `⟨v, hv⟩` from `exists_ne_zero_of_isIrreducible (ρ := ρ)`. Proceed by induction on `hn : p.natDegree generalizing p with`. Consider the case `zero`. Rewrite `hn` using `[Polynomial.natDegree_eq_zero]`. Take `⟨a, rfl⟩` from `hn`.

Establish `ha : a ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hp`. Rewrite `hφ` using `[aeval_C]`. Establish `h1 : a • v = 0` using `congrArg (fun f : Representation.IntertwiningMap ρ ρ => f v) hφ`.

Conclude with `absurd h1 (smul_ne_zero ha hv)`. Consider the case `succ n ih`. Establish `hdeg : p.degree ≠ 0`. Rewrite using `[Polynomial.degree_eq_natDegree hp, hn]`. Conclude with `Nat.succ_ne_zero n` after adjusting the coercions.

Take `⟨r, hr⟩` from `IsAlgClosed.exists_root p hdeg`. Use `set q := p /ₘ (X - C r)`. Establish `hpq : (X - C r) * q = p` using `mul_divByMonic_eq_iff_isRoot.2 hr`. Establish `hq : q ≠ 0`. Introduce `hq`.

Rewrite `hpq` using `[hq, mul_zero]`. Conclude with `hp hpq.symm`. Establish `hqdeg : q.natDegree = n`. Rewrite using `[natDegree_divByMonic _ (monic_X_sub_C r), natDegree_X_sub_C, hn]`. Both sides reduce to the same expression.

Distinguish the cases in `hφr : φ - algebraMap ℂ (Representation.IntertwiningMap ρ ρ) r = 0`. Conclude with `⟨r, sub_eq_zero.1 hφr⟩`. Use `ih hq ?_ hqdeg` and prove the remaining obligations. Establish `hinj` using `injective_of_ne_zero hφr`. Rewrite `hφ` using `[← hpq, map_mul, map_sub, aeval_X, aeval_C]`.

Use `DFunLike.ext _ _ fun w => hinj ?_` and prove the remaining obligations. Establish `h1` using `congrArg (fun f : Representation.IntertwiningMap ρ ρ => f w) hφ`. Express the relevant statement in the definitionally equal form `(φ - algebraMap ℂ (Representation.IntertwiningMap ρ ρ) r) ((aeval φ q) w) = (φ - algebraMap ℂ (Representation.IntertwiningMap ρ ρ) r) 0`. Rewrite using `[map_zero]`. Conclude with `h1`.
-/
theorem exists_eq_algebraMap_of_aeval_eq_zero [ρ.IsIrreducible]
    (φ : Representation.IntertwiningMap ρ ρ) {p : ℂ[X]} (hp : p ≠ 0) (hφ : aeval φ p = 0) :
    ∃ c : ℂ, φ = algebraMap ℂ (Representation.IntertwiningMap ρ ρ) c := by
  obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible (ρ := ρ)
  induction hn : p.natDegree generalizing p with
  | zero =>
    rw [Polynomial.natDegree_eq_zero] at hn
    obtain ⟨a, rfl⟩ := hn
    have ha : a ≠ 0 := by
      rintro rfl
      simp at hp
    rw [aeval_C] at hφ
    have h1 : a • v = 0 := congrArg (fun f : Representation.IntertwiningMap ρ ρ => f v) hφ
    exact absurd h1 (smul_ne_zero ha hv)
  | succ n ih =>
    have hdeg : p.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hp, hn]
      exact_mod_cast Nat.succ_ne_zero n
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_root p hdeg
    set q := p /ₘ (X - C r)
    have hpq : (X - C r) * q = p := mul_divByMonic_eq_iff_isRoot.2 hr
    have hq : q ≠ 0 := by
      intro hq
      rw [hq, mul_zero] at hpq
      exact hp hpq.symm
    have hqdeg : q.natDegree = n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C r), natDegree_X_sub_C, hn]
      rfl
    by_cases hφr : φ - algebraMap ℂ (Representation.IntertwiningMap ρ ρ) r = 0
    · exact ⟨r, sub_eq_zero.1 hφr⟩
    · refine ih hq ?_ hqdeg
      have hinj := injective_of_ne_zero hφr
      rw [← hpq, map_mul, map_sub, aeval_X, aeval_C] at hφ
      refine DFunLike.ext _ _ fun w => hinj ?_
      have h1 := congrArg (fun f : Representation.IntertwiningMap ρ ρ => f w) hφ
      change (φ - algebraMap ℂ (Representation.IntertwiningMap ρ ρ) r) ((aeval φ q) w) =
        (φ - algebraMap ℂ (Representation.IntertwiningMap ρ ρ) r) 0
      rw [map_zero]
      exact h1

/- English proof (translation)
Take `⟨v, hv⟩` from `exists_ne_zero_of_isIrreducible (ρ := ρ)`. Prove the components needed by the constructor for the conclusion. Introduce `a b hab`. Establish `h1 : a • v = b • v` using `congrArg (fun f : Representation.IntertwiningMap ρ ρ => f v) hab`. Conclude with `smul_left_injective ℂ hv h1`.

Introduce `φ`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Establish `hsub : ∀ c : ℂ, φ - algebraMap ℂ (Representation.IntertwiningMap ρ ρ) c ≠ 0` using `fun c h => hne c (sub_eq_zero.1 h).symm`. Establish `htr : ∀ p : ℂ[X], p ≠ 0 → aeval φ p ≠ 0` using `fun p hp h => by`.

Take `⟨c, hc⟩` from `exists_eq_algebraMap_of_aeval_eq_zero φ hp h`. Conclude with `hne c hc.symm`. Establish `hsurj : ∀ c : ℂ, Function.Surjective (φ - algebraMap ℂ (Representation.IntertwiningMap ρ ρ) c)` using `fun c => ((Representation.IsIrreducible.bijective_or_eq_zero _).resolve_right (hsub c)).2`. Use `choose w hw using fun c => hsurj c v`. Establish `sum_apply : ∀ (s : Finset ℂ) (f : ℂ → Representation.IntertwiningMap ρ ρ) (x : V), (∑ j ∈ s, f j) x = ∑ j ∈ s, f j x`.

Introduce `s f x`. Establish `h1` using `congrFun (map_sum (Representation.IntertwiningMap.coeFnAddMonoidHom ρ ρ) f s) x`. Rewrite `h1` using `[Finset.sum_apply]`. Conclude with `h1`. Establish `hli : LinearIndependent ℂ w`.

Rewrite using `[linearIndependent_iff']`. Introduce `s a hsum i hi`. Establish `key : ∀ j ∈ s, aeval φ (∏ k ∈ s, (X - C k)) (w j) = aeval φ (∏ k ∈ s.erase j, (X - C k)) v`. Introduce `j hj`. Rewrite using `[← Finset.prod_erase_mul _ _ hj, map_mul]`.

Express the relevant statement in the definitionally equal form `(aeval φ (∏ k ∈ s.erase j, (X - C k))) ((aeval φ (X - C j)) (w j)) = _`. Rewrite using `[map_sub, aeval_X, aeval_C, hw j]`. Use `set P : ℂ[X] := ∑ j ∈ s, a j • ∏ k ∈ s.erase j, (X - C k) with hPdef`. Establish `hP : aeval φ P v = 0`. Establish `h0` using `congrArg (aeval φ (∏ k ∈ s, (X - C k))) hsum`.

Rewrite `h0` using `[map_sum, map_zero]`. Rewrite using `[hPdef, map_sum, sum_apply]`. Rewrite using `[← h0]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite using `[map_smul, map_smul, key j hj]`.

Both sides reduce to the same expression. Establish `hP0 : P = 0`. Assume the negation of the conclusion as `hP0`. Conclude with `hv (injective_of_ne_zero (htr P hP0) (hP.trans (map_zero _).symm))`. Establish `h1` using `congrArg (Polynomial.eval i) hP0`.

Rewrite `h1` using `[hPdef, eval_finsetSum, eval_zero, Finset.sum_eq_single i]`. Rewrite `h1` using `[eval_smul, eval_prod, smul_eq_mul]`. Use `(mul_eq_zero.1 h1).resolve_right ?_` and prove the remaining obligations. Use `Finset.prod_ne_zero_iff.2 fun k hk => ?_` and prove the remaining obligations. Rewrite using `[eval_sub, eval_X, eval_C]`.

Conclude with `sub_ne_zero.2 (Finset.ne_of_mem_erase hk).symm`. Introduce `j _ hji`. Rewrite using `[eval_smul, eval_prod, Finset.prod_eq_zero (i := i) (Finset.mem_erase.2 ⟨Ne.symm hji, hi⟩) (by rw [eval_sub, eval_X, eval_C, sub_self]), smul_zero]`. Introduce `h`. Conclude with `absurd hi h`.

Establish `h1` using `hli.cardinal_lift_le_rank`. Rewrite `h1` using `[Cardinal.mk_complex, Cardinal.lift_continuum]`. Establish `h2 : Cardinal.lift.{0} (Module.rank ℂ V) ≤ ℵ₀` using `Cardinal.lift_le_aleph0.2 hV`. Conclude with `(not_le.2 Cardinal.aleph0_lt_continuum) (h1.trans h2)`.
-/
theorem algebraMap_intertwiningMap_bijective_of_rank_le_aleph0 [ρ.IsIrreducible]
    (hV : Module.rank ℂ V ≤ ℵ₀) :
    Function.Bijective (algebraMap ℂ (Representation.IntertwiningMap ρ ρ)) := by
  obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible (ρ := ρ)
  constructor
  · intro a b hab
    have h1 : a • v = b • v :=
      congrArg (fun f : Representation.IntertwiningMap ρ ρ => f v) hab
    exact smul_left_injective ℂ hv h1
  · intro φ
    by_contra hne
    push Not at hne
    have hsub : ∀ c : ℂ, φ - algebraMap ℂ (Representation.IntertwiningMap ρ ρ) c ≠ 0 :=
      fun c h => hne c (sub_eq_zero.1 h).symm
    have htr : ∀ p : ℂ[X], p ≠ 0 → aeval φ p ≠ 0 := fun p hp h => by
      obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_aeval_eq_zero φ hp h
      exact hne c hc.symm
    have hsurj : ∀ c : ℂ,
        Function.Surjective (φ - algebraMap ℂ (Representation.IntertwiningMap ρ ρ) c) :=
      fun c => ((Representation.IsIrreducible.bijective_or_eq_zero _).resolve_right (hsub c)).2
    choose w hw using fun c => hsurj c v
    have sum_apply : ∀ (s : Finset ℂ) (f : ℂ → Representation.IntertwiningMap ρ ρ) (x : V),
        (∑ j ∈ s, f j) x = ∑ j ∈ s, f j x := by
      intro s f x
      have h1 := congrFun (map_sum (Representation.IntertwiningMap.coeFnAddMonoidHom ρ ρ) f s) x
      rw [Finset.sum_apply] at h1
      exact h1
    have hli : LinearIndependent ℂ w := by
      rw [linearIndependent_iff']
      intro s a hsum i hi
      have key : ∀ j ∈ s, aeval φ (∏ k ∈ s, (X - C k)) (w j) =
          aeval φ (∏ k ∈ s.erase j, (X - C k)) v := by
        intro j hj
        rw [← Finset.prod_erase_mul _ _ hj, map_mul]
        change (aeval φ (∏ k ∈ s.erase j, (X - C k))) ((aeval φ (X - C j)) (w j)) = _
        rw [map_sub, aeval_X, aeval_C, hw j]
      set P : ℂ[X] := ∑ j ∈ s, a j • ∏ k ∈ s.erase j, (X - C k) with hPdef
      have hP : aeval φ P v = 0 := by
        have h0 := congrArg (aeval φ (∏ k ∈ s, (X - C k))) hsum
        rw [map_sum, map_zero] at h0
        rw [hPdef, map_sum, sum_apply]
        rw [← h0]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [map_smul, map_smul, key j hj]
        rfl
      have hP0 : P = 0 := by
        by_contra hP0
        exact hv (injective_of_ne_zero (htr P hP0) (hP.trans (map_zero _).symm))
      have h1 := congrArg (Polynomial.eval i) hP0
      rw [hPdef, eval_finsetSum, eval_zero, Finset.sum_eq_single i] at h1
      · rw [eval_smul, eval_prod, smul_eq_mul] at h1
        refine (mul_eq_zero.1 h1).resolve_right ?_
        refine Finset.prod_ne_zero_iff.2 fun k hk => ?_
        rw [eval_sub, eval_X, eval_C]
        exact sub_ne_zero.2 (Finset.ne_of_mem_erase hk).symm
      · intro j _ hji
        rw [eval_smul, eval_prod, Finset.prod_eq_zero (i := i) (Finset.mem_erase.2 ⟨Ne.symm hji, hi⟩)
          (by rw [eval_sub, eval_X, eval_C, sub_self]), smul_zero]
      · intro h
        exact absurd hi h
    have h1 := hli.cardinal_lift_le_rank
    rw [Cardinal.mk_complex, Cardinal.lift_continuum] at h1
    have h2 : Cardinal.lift.{0} (Module.rank ℂ V) ≤ ℵ₀ := Cardinal.lift_le_aleph0.2 hV
    exact (not_le.2 Cardinal.aleph0_lt_continuum) (h1.trans h2)

end Schur

section Smooth

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace.SeparableSpace G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}

/- English proof (translation)
Take `⟨v, hv⟩` from `exists_ne_zero_of_isIrreducible (ρ := ρ)`. Take `⟨D, hDc, hDd⟩` from `TopologicalSpace.exists_countable_dense G`. Establish `hstable : ∀ g : G, Submodule.span ℂ (Set.range fun h : G => ρ h v) ≤ (Submodule.span ℂ (Set.range fun h : G => ρ h v)).comap (ρ g)`. Introduce `g`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨h, rfl⟩`. Conclude with `Submodule.subset_span ⟨g * h, by simp [map_mul, Module.End.mul_apply]⟩`. Set `W : Subrepresentation ρ` to `⟨Submodule.span ℂ (Set.range fun h : G => ρ h v), fun g _ hx => hstable g hx⟩`. Establish `hW : W = ⊤` using `(eq_bot_or_eq_top W).resolve_left fun h => hv (by`. Establish `hvW : v ∈ W.toSubmodule` using `Submodule.subset_span ⟨1, by simp⟩`.

Rewrite `hvW` using `[h]`. Conclude with `(Submodule.mem_bot ℂ).1 hvW)`. Establish `hspan : Submodule.span ℂ (Set.range fun h : G => ρ h v) = ⊤` using `congrArg Subrepresentation.toSubmodule hW`. Establish `hsub : Set.range (fun h : G => ρ h v) ⊆ Set.range (fun d : D => ρ (d : G) v)`. Introduce and unpack `_ ⟨g, rfl⟩`.

Establish `hU : IsOpen ((fun x : G => g⁻¹ * x) ⁻¹' (stabilizerOf ρ v : Set G))` using `(hρ v).preimage (by fun_prop)`. Take `⟨d, hdD, hdU⟩` from `hDd.exists_mem_open hU ⟨g, by simp⟩`. Use `⟨⟨d, hdD⟩, ?_⟩` and prove the remaining obligations. Establish `hd : ρ (g⁻¹ * d) v = v` using `hdU`. Express the relevant statement in the definitionally equal form `ρ d v = ρ g v`.

Use `conv_rhs => rw [← hd]`. Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]`. Establish `htop : Submodule.span ℂ (Set.range fun d : D => ρ (d : G) v) = ⊤`. Rewrite using `[eq_top_iff, ← hspan]`. Conclude with `Submodule.span_mono hsub`.

Establish `: Countable D` using `hDc.to_subtype`. Establish `: Countable (Set.range fun d : D => ρ (d : G) v)` using `(Set.countable_range _).to_subtype`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem rank_le_aleph0_of_isSmooth (hρ : IsSmooth ρ) [ρ.IsIrreducible] :
    Module.rank ℂ V ≤ ℵ₀ := by
  obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible (ρ := ρ)
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense G
  have hstable : ∀ g : G, Submodule.span ℂ (Set.range fun h : G => ρ h v) ≤
      (Submodule.span ℂ (Set.range fun h : G => ρ h v)).comap (ρ g) := by
    intro g
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h, rfl⟩
    exact Submodule.subset_span ⟨g * h, by simp [map_mul, Module.End.mul_apply]⟩
  let W : Subrepresentation ρ :=
    ⟨Submodule.span ℂ (Set.range fun h : G => ρ h v), fun g _ hx => hstable g hx⟩
  have hW : W = ⊤ := (eq_bot_or_eq_top W).resolve_left fun h => hv (by
    have hvW : v ∈ W.toSubmodule := Submodule.subset_span ⟨1, by simp⟩
    rw [h] at hvW
    exact (Submodule.mem_bot ℂ).1 hvW)
  have hspan : Submodule.span ℂ (Set.range fun h : G => ρ h v) = ⊤ :=
    congrArg Subrepresentation.toSubmodule hW
  have hsub : Set.range (fun h : G => ρ h v) ⊆ Set.range (fun d : D => ρ (d : G) v) := by
    rintro _ ⟨g, rfl⟩
    have hU : IsOpen ((fun x : G => g⁻¹ * x) ⁻¹' (stabilizerOf ρ v : Set G)) :=
      (hρ v).preimage (by fun_prop)
    obtain ⟨d, hdD, hdU⟩ := hDd.exists_mem_open hU ⟨g, by simp⟩
    refine ⟨⟨d, hdD⟩, ?_⟩
    have hd : ρ (g⁻¹ * d) v = v := hdU
    change ρ d v = ρ g v
    conv_rhs => rw [← hd]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  have htop : Submodule.span ℂ (Set.range fun d : D => ρ (d : G) v) = ⊤ := by
    rw [eq_top_iff, ← hspan]
    exact Submodule.span_mono hsub
  have : Countable D := hDc.to_subtype
  have : Countable (Set.range fun d : D => ρ (d : G) v) := (Set.countable_range _).to_subtype
  calc Module.rank ℂ V = Module.rank ℂ (⊤ : Submodule ℂ V) := (rank_top ℂ V).symm
    _ = Module.rank ℂ (Submodule.span ℂ (Set.range fun d : D => ρ (d : G) v)) := by rw [htop]
    _ ≤ #(Set.range fun d : D => ρ (d : G) v) := rank_span_le _
    _ ≤ ℵ₀ := Cardinal.mk_le_aleph0

/- English proof (translation)
The claim follows from `algebraMap_intertwiningMap_bijective_of_rank_le_aleph0 (rank_le_aleph0_of_isSmooth hρ)`.
-/
theorem algebraMap_intertwiningMap_bijective_of_isSmooth (hρ : IsSmooth ρ) [ρ.IsIrreducible] :
    Function.Bijective (algebraMap ℂ (Representation.IntertwiningMap ρ ρ)) :=
  algebraMap_intertwiningMap_bijective_of_rank_le_aleph0 (rank_le_aleph0_of_isSmooth hρ)

/- English proof (translation)
Take `⟨c, hc⟩` from `(algebraMap_intertwiningMap_bijective_of_isSmooth hρ).2 (Representation.IntertwiningMap.centralMul ρ z hz)`. Conclude with `⟨c, fun v => (congrArg (fun f : Representation.IntertwiningMap ρ ρ => f v) hc).symm⟩`.
-/
theorem exists_central_character (hρ : IsSmooth ρ) [ρ.IsIrreducible] {z : G}
    (hz : z ∈ Submonoid.center G) : ∃ c : ℂ, ∀ v : V, ρ z v = c • v := by
  obtain ⟨c, hc⟩ := (algebraMap_intertwiningMap_bijective_of_isSmooth hρ).2
    (Representation.IntertwiningMap.centralMul ρ z hz)
  exact ⟨c, fun v => (congrArg (fun f : Representation.IntertwiningMap ρ ρ => f v) hc).symm⟩

end Smooth

end GroundTheory.Automorphic
