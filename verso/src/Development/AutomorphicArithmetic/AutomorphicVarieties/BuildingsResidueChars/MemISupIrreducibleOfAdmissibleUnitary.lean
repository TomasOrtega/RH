import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleSubrepFixedOfUnitary
import Development.AutomorphicArithmetic.DivisorFrames.ExistsIrreducibleSubrepHeckeEigenOfInvariantForm

/- English proof (translation)
Introduce `H W _ _ _ ρ B hdef hinv hadm x`. Use `set S : Submodule ℂ W := ⨆ U : {U : Submodule ℂ W // U ≠ ⊥ ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧ ∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U}, U.1 with hS`. Establish `hSle : ∀ U : Submodule ℂ W, U ≠ ⊥ → (∀ g, ∀ u ∈ U, ρ g u ∈ U) → (∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U) → U ≤ S`. Introduce `U h1 h2 h3`. Conclude with `le_iSup (fun U : {U : Submodule ℂ W // U ≠ ⊥ ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧ ∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U} => U.1) ⟨U, h1, h2, h3⟩`.

Establish `hSinv : ∀ g, ∀ u ∈ S, ρ g u ∈ S`. Introduce `g u hu`. Establish `hle : S ≤ S.comap (ρ g)`. Use `iSup_le ?_` and prove the remaining obligations. Introduce and unpack `⟨U, h1, h2, h3⟩ v hv`.

Conclude with `hSle U h1 h2 h3 (h2 g v hv)`. Conclude with `hle hu`. Set `Z : Subrepresentation ρ` to `⟨S, fun g v hv => hSinv g v hv⟩`. Set `O : Submodule ℂ W` to `⨅ z : S, LinearMap.ker (B (z : W))`. Establish `memO : ∀ w, w ∈ O ↔ ∀ z ∈ S, B z w = 0`.

Introduce `w`. Simplify using `[O, Submodule.mem_iInf]`. Set `Y : Subrepresentation ρ` to `⟨O, fun g v hv => (memO _).2 (GlobalTheory.UnitarySemisimple.orth_stable ρ B hinv Z v ((memO _).1 hv) g)⟩`. Take `⟨t, htS, ht⟩` from `GlobalTheory.UnitarySemisimple.exists_compl_proj ρ B hdef hinv hadm Z x`. Distinguish the cases in `h0 : x - t = 0`.

Rewrite using `[sub_eq_zero.1 h0]`. Conclude with `htS`. It suffices to derive a contradiction. Set `σ : Representation ℂ H O` to `Y.toRepresentation`. Establish `hσ : ∀ g (v : O), ((σ g v : O) : W) = ρ g v` using `fun _ _ => rfl`.

Set `B' : O →ₗ⋆[ℂ] O →ₗ[ℂ] ℂ` to `(B.comp O.subtype).compl₂ O.subtype`. Establish `hB' : ∀ u v : O, B' u v = B u v` using `fun _ _ => rfl`. Establish `hadm' : ∀ v : O, ∃ K : Subgroup H, (∀ k ∈ K, σ k v = v) ∧ FiniteDimensional ℂ (GlobalTheory.PRep.fixed σ K) ∧ ∀ w, (Set.range fun k : K => σ k w).Finite`. Introduce `v`. Take `⟨K, h1, h2, h3⟩` from `hadm v`.

Use `⟨K, fun k hk => Subtype.ext (h1 k hk), ?_, fun w => ?_⟩` and prove the remaining obligations. Set `f : GlobalTheory.PRep.fixed σ K →ₗ[ℂ] GlobalTheory.PRep.fixed ρ K` to `(O.subtype.comp (GlobalTheory.PRep.fixed σ K).subtype).codRestrict _ (by`. Introduce `u k`. Conclude with `congrArg Subtype.val (u.2 k))`. Use `Module.Finite.of_injective f ?_` and prove the remaining obligations.

Introduce `a b hab`. Establish `hab' : ((f a : GlobalTheory.PRep.fixed ρ K) : W) = ((f b : GlobalTheory.PRep.fixed ρ K) : W)` using `by rw [hab]`. Conclude with `Subtype.ext (Subtype.ext hab')`. Use `Set.Finite.of_finite_image (f := Subtype.val) ((h3 w).subset ?_) Subtype.val_injective.injOn` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨k, rfl⟩, rfl⟩`.

Conclude with `⟨k, rfl⟩`. Take `⟨U, hU, hirr, f, hfU, hf0, -⟩` from `UpperTheory.exists_irreducible_subrep_hecke_eigen_of_invariant_form H O σ B' (fun v hv => Subtype.ext (hdef _ hv)) (fun g u v => hinv g u v) hadm' ⟨x - t, (memO _).2 ht⟩ (fun h => h0 (congrArg Subtype.val h))`. Establish `hf0' : (f : W) ≠ 0` using `fun h => hf0 (Subtype.ext h)`. Establish `hfU' : (f : W) ∈ U.map O.subtype` using `⟨f, hfU, rfl⟩`. Establish `hle : U.map O.subtype ≤ S`.

Use `hSle _ (fun h => hf0' (by simpa [h] using hfU')) ?_ ?_` and prove the remaining obligations. Introduce and unpack `g _ ⟨u, hu, rfl⟩`. Conclude with `⟨σ g u, hU g u hu, rfl⟩`. Introduce `N hN hNinv`. Establish `hNO : N ≤ O` using `hN.trans (Submodule.map_subtype_le _ _)`.

Establish `hmc : (N.comap O.subtype).map O.subtype = N`. Rewrite using `[Submodule.map_comap_subtype, inf_eq_right.2 hNO]`. Establish `hle' : N.comap O.subtype ≤ U`. Introduce `u hu`. Take `⟨w, hw, hwu⟩` from `hN hu`.

Establish `: w = u` using `Subtype.ext hwu`. Conclude with `this ▸ hw`. Break down `hirr _ hle' (fun g u hu => hNinv g u hu) with h | h` into its components or cases. Use `left`. Rewrite using `[← hmc, h, Submodule.map_bot]`.

Use `right`. Rewrite using `[← hmc, h]`. Conclude with `hf0' (hdef _ ((memO _).1 f.2 _ (hle hfU')))`.
-/
theorem UpperTheory.mem_iSup_irreducible_of_admissible_unitary :
    ∀ (H W : Type) [Group H] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), (∀ v, B v v = 0 → v = 0) → (∀ g u v, B (ρ g u) (ρ g v) = B u v) → (∀ v, ∃ K : Subgroup H, (∀ k ∈ K, ρ k v = v) ∧ FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K) ∧ ∀ w, (Set.range fun k : K => ρ k w).Finite) → ∀ x : W, x ∈ ⨆ U : {U : Submodule ℂ W // U ≠ ⊥ ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧ ∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U}, U.1 := by
  intro H W _ _ _ ρ B hdef hinv hadm x
  classical
  set S : Submodule ℂ W := ⨆ U : {U : Submodule ℂ W // U ≠ ⊥ ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧ ∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U}, U.1 with hS
  have hSle : ∀ U : Submodule ℂ W, U ≠ ⊥ → (∀ g, ∀ u ∈ U, ρ g u ∈ U) →
      (∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U) → U ≤ S := by
    intro U h1 h2 h3
    exact le_iSup (fun U : {U : Submodule ℂ W // U ≠ ⊥ ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧ ∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U} => U.1) ⟨U, h1, h2, h3⟩
  have hSinv : ∀ g, ∀ u ∈ S, ρ g u ∈ S := by
    intro g u hu
    have hle : S ≤ S.comap (ρ g) := by
      refine iSup_le ?_
      rintro ⟨U, h1, h2, h3⟩ v hv
      exact hSle U h1 h2 h3 (h2 g v hv)
    exact hle hu
  let Z : Subrepresentation ρ := ⟨S, fun g v hv => hSinv g v hv⟩
  let O : Submodule ℂ W := ⨅ z : S, LinearMap.ker (B (z : W))
  have memO : ∀ w, w ∈ O ↔ ∀ z ∈ S, B z w = 0 := by
    intro w
    simp [O, Submodule.mem_iInf]
  let Y : Subrepresentation ρ := ⟨O, fun g v hv =>
    (memO _).2 (GlobalTheory.UnitarySemisimple.orth_stable ρ B hinv Z v ((memO _).1 hv) g)⟩
  obtain ⟨t, htS, ht⟩ := GlobalTheory.UnitarySemisimple.exists_compl_proj ρ B hdef hinv hadm Z x
  by_cases h0 : x - t = 0
  · rw [sub_eq_zero.1 h0]
    exact htS
  exfalso
  let σ : Representation ℂ H O := Y.toRepresentation
  have hσ : ∀ g (v : O), ((σ g v : O) : W) = ρ g v := fun _ _ => rfl
  let B' : O →ₗ⋆[ℂ] O →ₗ[ℂ] ℂ := (B.comp O.subtype).compl₂ O.subtype
  have hB' : ∀ u v : O, B' u v = B u v := fun _ _ => rfl
  have hadm' : ∀ v : O, ∃ K : Subgroup H, (∀ k ∈ K, σ k v = v) ∧
      FiniteDimensional ℂ (GlobalTheory.PRep.fixed σ K) ∧ ∀ w, (Set.range fun k : K => σ k w).Finite := by
    intro v
    obtain ⟨K, h1, h2, h3⟩ := hadm v
    refine ⟨K, fun k hk => Subtype.ext (h1 k hk), ?_, fun w => ?_⟩
    · let f : GlobalTheory.PRep.fixed σ K →ₗ[ℂ] GlobalTheory.PRep.fixed ρ K :=
        (O.subtype.comp (GlobalTheory.PRep.fixed σ K).subtype).codRestrict _ (by
          intro u k
          exact congrArg Subtype.val (u.2 k))
      refine Module.Finite.of_injective f ?_
      intro a b hab
      have hab' : ((f a : GlobalTheory.PRep.fixed ρ K) : W) = ((f b : GlobalTheory.PRep.fixed ρ K) : W) := by rw [hab]
      exact Subtype.ext (Subtype.ext hab')
    · refine Set.Finite.of_finite_image (f := Subtype.val) ((h3 w).subset ?_) Subtype.val_injective.injOn
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, rfl⟩
  obtain ⟨U, hU, hirr, f, hfU, hf0, -⟩ := UpperTheory.exists_irreducible_subrep_hecke_eigen_of_invariant_form H O σ B'
    (fun v hv => Subtype.ext (hdef _ hv)) (fun g u v => hinv g u v) hadm'
    ⟨x - t, (memO _).2 ht⟩ (fun h => h0 (congrArg Subtype.val h))
  have hf0' : (f : W) ≠ 0 := fun h => hf0 (Subtype.ext h)
  have hfU' : (f : W) ∈ U.map O.subtype := ⟨f, hfU, rfl⟩
  have hle : U.map O.subtype ≤ S := by
    refine hSle _ (fun h => hf0' (by simpa [h] using hfU')) ?_ ?_
    · rintro g _ ⟨u, hu, rfl⟩
      exact ⟨σ g u, hU g u hu, rfl⟩
    · intro N hN hNinv
      have hNO : N ≤ O := hN.trans (Submodule.map_subtype_le _ _)
      have hmc : (N.comap O.subtype).map O.subtype = N := by
        rw [Submodule.map_comap_subtype, inf_eq_right.2 hNO]
      have hle' : N.comap O.subtype ≤ U := by
        intro u hu
        obtain ⟨w, hw, hwu⟩ := hN hu
        have : w = u := Subtype.ext hwu
        exact this ▸ hw
      rcases hirr _ hle' (fun g u hu => hNinv g u hu) with h | h
      · left
        rw [← hmc, h, Submodule.map_bot]
      · right
        rw [← hmc, h]
  exact hf0' (hdef _ ((memO _).1 f.2 _ (hle hfU')))
