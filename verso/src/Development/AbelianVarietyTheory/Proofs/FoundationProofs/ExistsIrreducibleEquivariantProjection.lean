import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleSubrepFixedOfUnitary

namespace GlobalTheory.AdmissibleProjection

open GlobalTheory.UnitarySemisimple

variable {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W]

def stab (ρ : Representation ℂ H W) (v : W) : Subgroup H where
  carrier := {g | ρ g v = v}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha]
      _ = v := rho_inv_rho ρ a v

/- English proof (translation)
Establish `hopen : ∀ i : K, IsOpen {h : H | ρ h w = ρ (i : H) w}`. Introduce `i`. Establish `e : {h : H | ρ h w = ρ (i : H) w} = (fun h => (i : H)⁻¹ * h) ⁻¹' {h | ρ h w = w}`. Use extensionality with `h`. Simplify using `only [Set.mem_setOf_eq, Set.mem_preimage, map_mul, Module.End.mul_apply]`.

Prove the components needed by the constructor for the conclusion. Introduce `e`. Rewrite using `[e, rho_inv_rho]`. Introduce `e`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[e]`. Conclude with `(hsm w).preimage (continuous_mul_left _)`. Take `⟨t, ht⟩` from `hK.elim_finite_subcover (fun i : K => {h : H | ρ h w = ρ (i : H) w}) hopen (fun h hh => Set.mem_iUnion.2 ⟨⟨h, hh⟩, rfl⟩)`. Use `(t.finite_toSet.image (fun i : K => ρ (i : H) w)).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`.

Take `⟨i, hi, hki⟩` from `Set.mem_iUnion₂.1 (ht k.2)`. Conclude with `⟨i, hi, hki.symm⟩`.
-/
theorem orbit_finite [TopologicalSpace H] [IsTopologicalGroup H] (ρ : Representation ℂ H W)
    (hsm : ∀ w, IsOpen {k : H | ρ k w = w}) (K : Subgroup H) (hK : IsCompact (K : Set H))
    (w : W) : (Set.range fun k : K => ρ k w).Finite := by
  have hopen : ∀ i : K, IsOpen {h : H | ρ h w = ρ (i : H) w} := by
    intro i
    have e : {h : H | ρ h w = ρ (i : H) w} = (fun h => (i : H)⁻¹ * h) ⁻¹' {h | ρ h w = w} := by
      ext h
      simp only [Set.mem_setOf_eq, Set.mem_preimage, map_mul, Module.End.mul_apply]
      constructor
      · intro e; rw [e, rho_inv_rho]
      · intro e
        calc ρ h w = ρ (i : H) (ρ (i : H)⁻¹ (ρ h w)) := (rho_rho_inv ρ _ _).symm
          _ = ρ (i : H) w := by rw [e]
    rw [e]
    exact (hsm w).preimage (continuous_mul_left _)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun i : K => {h : H | ρ h w = ρ (i : H) w}) hopen
    (fun h hh => Set.mem_iUnion.2 ⟨⟨h, hh⟩, rfl⟩)
  refine (t.finite_toSet.image (fun i : K => ρ (i : H) w)).subset ?_
  rintro _ ⟨k, rfl⟩
  obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.1 (ht k.2)
  exact ⟨i, hi, hki.symm⟩

/- English proof (translation)
Take `⟨K₀, hop, hco⟩` from `hK0`. Introduce `v`. Use `⟨K₀ ⊓ stab ρ v, fun k hk => hk.2, hfd _ ?_, fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.coe_inf]`. Conclude with `hop.inter (hsm v)`.

Use `(orbit_finite ρ hsm K₀ hco w).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `⟨⟨k, k.2.1⟩, rfl⟩`.
-/
theorem hadm_of [TopologicalSpace H] [IsTopologicalGroup H] (ρ : Representation ℂ H W)
    (hK0 : ∃ K : Subgroup H, IsOpen (K : Set H) ∧ IsCompact (K : Set H))
    (hsm : ∀ w, IsOpen {k : H | ρ k w = w})
    (hfd : ∀ K : Subgroup H, IsOpen (K : Set H) → FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K)) :
    ∀ v, ∃ K : Subgroup H, (∀ k ∈ K, ρ k v = v) ∧ FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K) ∧
      ∀ w, (Set.range fun k : K => ρ k w).Finite := by
  obtain ⟨K₀, hop, hco⟩ := hK0
  intro v
  refine ⟨K₀ ⊓ stab ρ v, fun k hk => hk.2, hfd _ ?_, fun w => ?_⟩
  · rw [Subgroup.coe_inf]; exact hop.inter (hsm v)
  · refine (orbit_finite ρ hsm K₀ hco w).subset ?_
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨k, k.2.1⟩, rfl⟩

/- English proof (translation)
Establish `hex` using `fun w => exists_compl_proj ρ B hdef hinv hadm Z w`. Set `f : W → W` to `fun w => Classical.choose (hex w)`. Establish `hf1 : ∀ w, f w ∈ Z.toSubmodule` using `fun w => (Classical.choose_spec (hex w)).1`. Establish `hf2 : ∀ w, ∀ z ∈ Z.toSubmodule, B z (w - f w) = 0` using `fun w => (Classical.choose_spec (hex w)).2`. Establish `huniq : ∀ w t, t ∈ Z.toSubmodule → (∀ z ∈ Z.toSubmodule, B z (w - t) = 0) → f w = t`.

Introduce `w t ht htw`. Establish `hd : f w - t ∈ Z.toSubmodule` using `sub_mem (hf1 w) ht`. Establish `h0 : B (f w - t) (f w - t) = 0`. Combine the equalities or inequalities in the displayed calculation. Conclude with `sub_eq_zero.1 (hdef _ h0)`.

Set `P : W →ₗ[ℂ] W` to `{ toFun := f map_add' := fun a b => huniq _ _ (add_mem (hf1 a) (hf1 b)) (fun z hz => by`. Rewrite using `[show a + b - (f a + f b) = (a - f a) + (b - f b) by abel, map_add, hf2 a z hz, hf2 b z hz, add_zero])`. Use the proof step `map_smul' := fun c a => by`. Simplify using `only [RingHom.id_apply]`. Conclude with `huniq _ _ (Z.toSubmodule.smul_mem c (hf1 a)) (fun z hz => by`.

Rewrite using `[← smul_sub, map_smul, hf2 a z hz, smul_zero]) }`. Use `⟨P, hf1, hf2, fun g w => ?_⟩` and prove the remaining obligations. Conclude with `huniq _ _ (Z.apply_mem_toSubmodule g (hf1 w)) (fun z hz => by`. Rewrite using `[← map_sub]`. Conclude with `orth_stable ρ B hinv Z (w - f w) (hf2 w) g z hz)`.
-/
theorem exists_proj (ρ : Representation ℂ H W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (hdef : ∀ v, B v v = 0 → v = 0) (hinv : ∀ g u v, B (ρ g u) (ρ g v) = B u v)
    (hadm : ∀ v, ∃ K : Subgroup H, (∀ k ∈ K, ρ k v = v) ∧ FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K) ∧
      ∀ w, (Set.range fun k : K => ρ k w).Finite)
    (Z : Subrepresentation ρ) :
    ∃ P : W →ₗ[ℂ] W, (∀ w, P w ∈ Z.toSubmodule) ∧ (∀ w, ∀ z ∈ Z.toSubmodule, B z (w - P w) = 0) ∧
      ∀ g w, P (ρ g w) = ρ g (P w) := by
  classical
  have hex := fun w => exists_compl_proj ρ B hdef hinv hadm Z w
  let f : W → W := fun w => Classical.choose (hex w)
  have hf1 : ∀ w, f w ∈ Z.toSubmodule := fun w => (Classical.choose_spec (hex w)).1
  have hf2 : ∀ w, ∀ z ∈ Z.toSubmodule, B z (w - f w) = 0 :=
    fun w => (Classical.choose_spec (hex w)).2
  have huniq : ∀ w t, t ∈ Z.toSubmodule → (∀ z ∈ Z.toSubmodule, B z (w - t) = 0) → f w = t := by
    intro w t ht htw
    have hd : f w - t ∈ Z.toSubmodule := sub_mem (hf1 w) ht
    have h0 : B (f w - t) (f w - t) = 0 := by
      calc B (f w - t) (f w - t) = B (f w - t) ((w - t) - (w - f w)) := by congr 1; abel
        _ = 0 := by rw [map_sub, htw _ hd, hf2 w _ hd, sub_zero]
    exact sub_eq_zero.1 (hdef _ h0)
  let P : W →ₗ[ℂ] W :=
    { toFun := f
      map_add' := fun a b => huniq _ _ (add_mem (hf1 a) (hf1 b)) (fun z hz => by
        rw [show a + b - (f a + f b) = (a - f a) + (b - f b) by abel, map_add, hf2 a z hz,
          hf2 b z hz, add_zero])
      map_smul' := fun c a => by
        simp only [RingHom.id_apply]
        exact huniq _ _ (Z.toSubmodule.smul_mem c (hf1 a)) (fun z hz => by
          rw [← smul_sub, map_smul, hf2 a z hz, smul_zero]) }
  refine ⟨P, hf1, hf2, fun g w => ?_⟩
  exact huniq _ _ (Z.apply_mem_toSubmodule g (hf1 w)) (fun z hz => by
    rw [← map_sub]; exact orth_stable ρ B hinv Z (w - f w) (hf2 w) g z hz)

/- English proof (translation)
Introduce `H W _ _ _ _ _ ρ B hherm hpos hdef hinv hK0 hsm hfd x hx`. Establish `hadm` using `hadm_of ρ hK0 hsm hfd`. Take `⟨K0, hxK, hfdK, -⟩` from `hadm x`. Use `set F := GlobalTheory.PRep.fixed ρ K0 with hF`. Use `haveI := hfdK`.

Establish `ofF : ∀ u ∈ F, ∀ k ∈ K0, ρ k u = u`. Introduce `u hu k hk`. Use `hu ⟨k, hk⟩` as an intermediate fact. Simplify using `using this`. Establish `memF : ∀ u, (∀ k ∈ K0, ρ k u = u) → u ∈ F`.

Introduce `u hu k`. Use `show ρ (k : H) u = ((1 : ℂˣ) : ℂ) • u`. Simplify using `[hu k k.2]`. Use `set O := (orbSpan ρ x).toSubmodule with hO`. Set `Q : W → Prop` to `fun y => y ≠ 0 ∧ y ∈ F ∧ y ∈ O`.

Establish `hex : ∃ n : ℕ, ∃ y, Q y ∧ Module.finrank ℂ ((orbSpan ρ y).toSubmodule ⊓ F : Submodule ℂ W) = n` using `⟨_, x, ⟨hx, memF x hxK, mem_orbSpan ρ x⟩, rfl⟩`. Take `⟨y, ⟨hy0, hyF, hyO⟩, hn⟩` from `Nat.find_spec hex`. Establish `hmin : ∀ t, Q t → Module.finrank ℂ ((orbSpan ρ y).toSubmodule ⊓ F : Submodule ℂ W) ≤ Module.finrank ℂ ((orbSpan ρ t).toSubmodule ⊓ F : Submodule ℂ W)`. Introduce `t ht`. Rewrite using `[hn]`.

Conclude with `Nat.find_min' hex ⟨t, ht, rfl⟩`. Use `set U := orbSpan ρ y with hU`. Establish `hyU : y ∈ U.toSubmodule` using `mem_orbSpan ρ y`. Establish `hUO : U.toSubmodule ≤ O` using `orbSpan_le ρ y (orbSpan ρ x) hyO`. Take `⟨P, hP1, hP2, hP3⟩` from `exists_proj ρ B hdef hinv hadm U`.

Use `⟨U.toSubmodule, P, ?_, fun g u hu => U.apply_mem_toSubmodule g hu, ?_, hP1, hP3, ?_⟩` and prove the remaining obligations. Introduce `h`. Apply `hy0` to reduce the goal to its premises. Rewrite `hyU` using `[h]`. Conclude with `(Submodule.mem_bot ℂ).1 hyU`.

Introduce `N hNU hN`. Set `N' : Subrepresentation ρ` to `⟨N, by intro g v hv; exact hN g v hv⟩`. Take `⟨t, htN, ht⟩` from `exists_compl_proj ρ B hdef hinv hadm N' y`. Establish `hfix : ∀ g, ρ g y = y → ρ g t = t`. Introduce `g hg`.

Establish `h1 : ρ g t - t ∈ N'.toSubmodule` using `sub_mem (N'.apply_mem_toSubmodule g htN) htN`. Establish `h2 : ∀ z ∈ N'.toSubmodule, B z (ρ g t - t) = 0`. Introduce `z hz`. Establish `e : ρ g t - t = (y - t) - ρ g (y - t)`. Rewrite using `[map_sub, hg]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e, map_sub, ht z hz, orth_stable ρ B hinv N' _ ht g z hz, sub_zero]`. Conclude with `sub_eq_zero.1 (hdef _ (h2 _ h1))`. Distinguish the cases in `ht0 : t = 0`. Use `left`.

Establish `hyo : ∀ z ∈ N'.toSubmodule, B z y = 0`. Introduce `z hz`. Simplify `ht z hz` using `[ht0]`. Establish `hUo : ∀ z ∈ N'.toSubmodule, ∀ u ∈ U.toSubmodule, B z u = 0`. Introduce `z hz u hu`.

Establish `hle : U.toSubmodule ≤ LinearMap.ker (B z)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, rfl⟩`. Conclude with `orth_stable ρ B hinv N' y hyo g z hz`. Conclude with `hle hu`.

Rewrite using `[Submodule.eq_bot_iff]`. Introduce `v hv`. Conclude with `hdef _ (hUo _ hv _ (hNU hv))`. Use `right`. Establish `hQt : Q t` using `⟨ht0, memF t (fun k hk => hfix k (ofF y hyF k hk)), hUO (hNU htN)⟩`.

Establish `h1` using `hmin t hQt`. Use `haveI : FiniteDimensional ℂ (U.toSubmodule ⊓ F : Submodule ℂ W) := Submodule.finiteDimensional_of_le inf_le_right`. Use `haveI : FiniteDimensional ℂ (N ⊓ F : Submodule ℂ W) := Submodule.finiteDimensional_of_le inf_le_right`. Establish `hle1 : ((orbSpan ρ t).toSubmodule ⊓ F : Submodule ℂ W) ≤ N ⊓ F` using `inf_le_inf_right _ (orbSpan_le ρ t N' htN)`. Establish `hle2 : (N ⊓ F : Submodule ℂ W) ≤ U.toSubmodule ⊓ F` using `inf_le_inf_right _ hNU`.

Establish `h2` using `LinearMap.finrank_le_finrank_of_injective (f := Submodule.inclusion hle1) (Submodule.inclusion_injective hle1)`. Establish `heq` using `Submodule.eq_of_le_of_finrank_le hle2 (h1.trans h2)`. Establish `hyN : y ∈ N`. Establish `: y ∈ (N ⊓ F : Submodule ℂ W)` using `heq ▸ ⟨hyU, hyF⟩`. Conclude with `this.1`.

Conclude with `le_antisymm hNU (orbSpan_le ρ y N' hyN)`. Introduce `hPx`. Establish `hxo : ∀ z ∈ U.toSubmodule, B z x = 0`. Introduce `z hz`. Simplify `hP2 x z hz` using `[hPx]`.

Establish `hle : O ≤ LinearMap.ker (B y)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, rfl⟩`. Conclude with `orth_stable ρ B hinv U x hxo g y hyU`. Conclude with `hy0 (hdef _ (hle (hUO hyU)))`.
-/
theorem exists_irreducible_equivariant_projection : ∀ (H W : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), (∀ u v, star (B u v) = B v u) → (∀ v, 0 ≤ (B v v).re) → (∀ v, B v v = 0 → v = 0) → (∀ g u v, B (ρ g u) (ρ g v) = B u v) → (∃ K : Subgroup H, IsOpen (K : Set H) ∧ IsCompact (K : Set H)) → (∀ w, IsOpen {k : H | ρ k w = w}) → (∀ K : Subgroup H, IsOpen (K : Set H) → FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K)) → ∀ x : W, x ≠ 0 → ∃ (U : Submodule ℂ W) (P : W →ₗ[ℂ] W), U ≠ ⊥ ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧ (∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U) ∧ (∀ w, P w ∈ U) ∧ (∀ g w, P (ρ g w) = ρ g (P w)) ∧ P x ≠ 0 := by
  intro H W _ _ _ _ _ ρ B hherm hpos hdef hinv hK0 hsm hfd x hx
  classical
  have hadm := hadm_of ρ hK0 hsm hfd
  obtain ⟨K0, hxK, hfdK, -⟩ := hadm x
  set F := GlobalTheory.PRep.fixed ρ K0 with hF
  haveI := hfdK
  have ofF : ∀ u ∈ F, ∀ k ∈ K0, ρ k u = u := by
    intro u hu k hk
    have := hu ⟨k, hk⟩
    simpa using this
  have memF : ∀ u, (∀ k ∈ K0, ρ k u = u) → u ∈ F := by
    intro u hu k
    show ρ (k : H) u = ((1 : ℂˣ) : ℂ) • u
    simp [hu k k.2]
  set O := (orbSpan ρ x).toSubmodule with hO
  let Q : W → Prop := fun y => y ≠ 0 ∧ y ∈ F ∧ y ∈ O
  have hex : ∃ n : ℕ, ∃ y, Q y ∧
      Module.finrank ℂ ((orbSpan ρ y).toSubmodule ⊓ F : Submodule ℂ W) = n :=
    ⟨_, x, ⟨hx, memF x hxK, mem_orbSpan ρ x⟩, rfl⟩
  obtain ⟨y, ⟨hy0, hyF, hyO⟩, hn⟩ := Nat.find_spec hex
  have hmin : ∀ t, Q t → Module.finrank ℂ ((orbSpan ρ y).toSubmodule ⊓ F : Submodule ℂ W) ≤
      Module.finrank ℂ ((orbSpan ρ t).toSubmodule ⊓ F : Submodule ℂ W) := by
    intro t ht
    rw [hn]
    exact Nat.find_min' hex ⟨t, ht, rfl⟩
  set U := orbSpan ρ y with hU
  have hyU : y ∈ U.toSubmodule := mem_orbSpan ρ y
  have hUO : U.toSubmodule ≤ O := orbSpan_le ρ y (orbSpan ρ x) hyO
  obtain ⟨P, hP1, hP2, hP3⟩ := exists_proj ρ B hdef hinv hadm U
  refine ⟨U.toSubmodule, P, ?_, fun g u hu => U.apply_mem_toSubmodule g hu, ?_, hP1, hP3, ?_⟩
  · intro h
    apply hy0
    rw [h] at hyU
    exact (Submodule.mem_bot ℂ).1 hyU
  · intro N hNU hN
    let N' : Subrepresentation ρ := ⟨N, by intro g v hv; exact hN g v hv⟩
    obtain ⟨t, htN, ht⟩ := exists_compl_proj ρ B hdef hinv hadm N' y
    have hfix : ∀ g, ρ g y = y → ρ g t = t := by
      intro g hg
      have h1 : ρ g t - t ∈ N'.toSubmodule := sub_mem (N'.apply_mem_toSubmodule g htN) htN
      have h2 : ∀ z ∈ N'.toSubmodule, B z (ρ g t - t) = 0 := by
        intro z hz
        have e : ρ g t - t = (y - t) - ρ g (y - t) := by
          rw [map_sub, hg]
          abel
        rw [e, map_sub, ht z hz, orth_stable ρ B hinv N' _ ht g z hz, sub_zero]
      exact sub_eq_zero.1 (hdef _ (h2 _ h1))
    by_cases ht0 : t = 0
    · left
      have hyo : ∀ z ∈ N'.toSubmodule, B z y = 0 := by
        intro z hz
        simpa [ht0] using ht z hz
      have hUo : ∀ z ∈ N'.toSubmodule, ∀ u ∈ U.toSubmodule, B z u = 0 := by
        intro z hz u hu
        have hle : U.toSubmodule ≤ LinearMap.ker (B z) := by
          refine Submodule.span_le.2 ?_
          rintro _ ⟨g, rfl⟩
          exact orth_stable ρ B hinv N' y hyo g z hz
        exact hle hu
      rw [Submodule.eq_bot_iff]
      intro v hv
      exact hdef _ (hUo _ hv _ (hNU hv))
    · right
      have hQt : Q t := ⟨ht0, memF t (fun k hk => hfix k (ofF y hyF k hk)), hUO (hNU htN)⟩
      have h1 := hmin t hQt
      haveI : FiniteDimensional ℂ (U.toSubmodule ⊓ F : Submodule ℂ W) :=
        Submodule.finiteDimensional_of_le inf_le_right
      haveI : FiniteDimensional ℂ (N ⊓ F : Submodule ℂ W) :=
        Submodule.finiteDimensional_of_le inf_le_right
      have hle1 : ((orbSpan ρ t).toSubmodule ⊓ F : Submodule ℂ W) ≤ N ⊓ F :=
        inf_le_inf_right _ (orbSpan_le ρ t N' htN)
      have hle2 : (N ⊓ F : Submodule ℂ W) ≤ U.toSubmodule ⊓ F := inf_le_inf_right _ hNU
      have h2 := LinearMap.finrank_le_finrank_of_injective (f := Submodule.inclusion hle1)
        (Submodule.inclusion_injective hle1)
      have heq := Submodule.eq_of_le_of_finrank_le hle2 (h1.trans h2)
      have hyN : y ∈ N := by
        have : y ∈ (N ⊓ F : Submodule ℂ W) := heq ▸ ⟨hyU, hyF⟩
        exact this.1
      exact le_antisymm hNU (orbSpan_le ρ y N' hyN)
  · intro hPx
    have hxo : ∀ z ∈ U.toSubmodule, B z x = 0 := by
      intro z hz
      simpa [hPx] using hP2 x z hz
    have hle : O ≤ LinearMap.ker (B y) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, rfl⟩
      exact orth_stable ρ B hinv U x hxo g y hyU
    exact hy0 (hdef _ (hle (hUO hyU)))

end GlobalTheory.AdmissibleProjection
