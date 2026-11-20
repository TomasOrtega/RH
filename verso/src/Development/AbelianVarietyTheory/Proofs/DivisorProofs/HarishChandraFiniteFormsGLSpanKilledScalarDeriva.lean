import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemExpSolCons
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology

namespace GlobalTheory.HCF

/- English proof (translation)
Introduce `E _ _ _ a L W X hX N`. Use `set S : Module.End ℂ (Sm E a) := scalD E a with hS`. Use `set f : ℂ → Module.End ℂ (Sm E a) := fun c => S - algebraMap ℂ (Module.End ℂ (Sm E a)) c with hf`. Establish `hSZ : S ∈ Zalg E a` using `Central.lie_mem_Zalg 1`. Establish `hpow : ∀ (χ : Module.End ℂ (Sm E a) → ℂ) (φ : Sm E a), CentralNilGL χ N φ → (f (χ S) ^ N) φ = 0`.

Introduce `χ φ h`. Establish `key : ∀ n : ℕ, (List.replicate n S).foldr (fun z g => z g - χ z • g) φ = (f (χ S) ^ n) φ`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`.

Consider the case `succ n ih`. Rewrite using `[List.replicate_succ, List.foldr_cons, ih, pow_succ', Module.End.mul_apply]`. Simplify using `[hf, Algebra.algebraMap_eq_smul_one]`. Rewrite using `[← key]`. Conclude with `h _ (List.length_replicate) (fun z hz => by rw [List.eq_of_mem_replicate hz]; exact hSZ)`.

Establish `hc : ∀ c d, Commute (f c) (f d)` using `fun c d => Commute.sub_left (Commute.sub_right (Commute.refl S) (Algebra.commute_algebraMap_right _ _)) (Commute.sub_right (Algebra.commute_algebraMap_left _ _) (Algebra.commute_algebraMap_left _ _))`. Establish `hcl : ∀ (l : List ℂ) c, Commute (f c) (l.map f).prod` using `fun l c => Commute.list_prod_right _ _ fun y hy => by`. Take `⟨d, -, rfl⟩` from `List.mem_map.1 hy`. Conclude with `hc c d`. Set `G : (Module.End ℂ (Sm E a) → ℂ) → List ℂ` to `fun χ => List.replicate N (χ S)`.

Establish `main : ∀ (Ls : List (Module.End ℂ (Sm E a) → ℂ)) (φ : Sm E a), (∃ χ ∈ Ls, (f (χ S) ^ N) φ = 0) → ((Ls.flatMap G).map f).prod φ = 0`. Introduce `Ls`. Proceed by induction on `Ls with`. Consider the case `nil => intro φ h`. Simplify using `at h`.

Consider the case `cons χ0 rest ih`. Introduce `φ ⟨χ, hχ, h0⟩`. Rewrite using `[List.flatMap_cons, List.map_append, List.prod_append]`. Establish `hA : ((G χ0).map f).prod = f (χ0 S) ^ N`. Simplify using `[G, List.map_replicate, List.prod_replicate]`.

Break down `List.mem_cons.1 hχ with rfl | hr` into its components or cases. Establish `hcomm : Commute ((G χ).map f).prod ((rest.flatMap G).map f).prod`. Rewrite using `[hA]`. Conclude with `(hcl _ _).pow_left N`. Rewrite using `[hcomm.eq, Module.End.mul_apply, hA, h0, map_zero]`.

Rewrite using `[Module.End.mul_apply, ih φ ⟨χ, hr, h0⟩, map_zero]`. Use `⟨hX.toFinset.toList.flatMap G, fun φ hφ => ?_⟩` and prove the remaining obligations. Establish `hsub : formsGL E a L W X N ⊆ (LinearMap.ker ((hX.toFinset.toList.flatMap G).map f).prod : Set (Sm E a))`. Introduce `ψ hψ`. Take `⟨χ, hχX, hχ⟩` from `hψ.2.2.2`.

Conclude with `LinearMap.mem_ker.2 (main _ ψ ⟨χ, by simpa using hχX, hpow χ ψ hχ⟩)`. Conclude with `LinearMap.mem_ker.1 ((Submodule.span_le.2 hsub) hφ)`.
-/
theorem span_formsGL_killed_scalD : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E)))
    (W : Submodule ℂ (Kinf E a → ℂ)) (X : Set (Module.End ℂ (Sm E a) → ℂ)), X.Finite → ∀ N : ℕ,
    ∃ Λ : List ℂ, ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N),
      (Λ.map fun c => scalD E a - algebraMap ℂ (Module.End ℂ (Sm E a)) c).prod φ = 0 := by
  intro E _ _ _ a L W X hX N
  set S : Module.End ℂ (Sm E a) := scalD E a with hS
  set f : ℂ → Module.End ℂ (Sm E a) := fun c => S - algebraMap ℂ (Module.End ℂ (Sm E a)) c with hf
  have hSZ : S ∈ Zalg E a := Central.lie_mem_Zalg 1

  have hpow : ∀ (χ : Module.End ℂ (Sm E a) → ℂ) (φ : Sm E a), CentralNilGL χ N φ → (f (χ S) ^ N) φ = 0 := by
    intro χ φ h
    have key : ∀ n : ℕ, (List.replicate n S).foldr (fun z g => z g - χ z • g) φ = (f (χ S) ^ n) φ := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [List.replicate_succ, List.foldr_cons, ih, pow_succ', Module.End.mul_apply]
        simp [hf, Algebra.algebraMap_eq_smul_one]
    rw [← key]
    exact h _ (List.length_replicate) (fun z hz => by rw [List.eq_of_mem_replicate hz]; exact hSZ)
  have hc : ∀ c d, Commute (f c) (f d) := fun c d =>
    Commute.sub_left (Commute.sub_right (Commute.refl S) (Algebra.commute_algebraMap_right _ _))
      (Commute.sub_right (Algebra.commute_algebraMap_left _ _) (Algebra.commute_algebraMap_left _ _))
  have hcl : ∀ (l : List ℂ) c, Commute (f c) (l.map f).prod := fun l c =>
    Commute.list_prod_right _ _ fun y hy => by
      obtain ⟨d, -, rfl⟩ := List.mem_map.1 hy
      exact hc c d
  let G : (Module.End ℂ (Sm E a) → ℂ) → List ℂ := fun χ => List.replicate N (χ S)
  have main : ∀ (Ls : List (Module.End ℂ (Sm E a) → ℂ)) (φ : Sm E a),
      (∃ χ ∈ Ls, (f (χ S) ^ N) φ = 0) → ((Ls.flatMap G).map f).prod φ = 0 := by
    intro Ls
    induction Ls with
    | nil => intro φ h; simp at h
    | cons χ0 rest ih =>
      intro φ ⟨χ, hχ, h0⟩
      rw [List.flatMap_cons, List.map_append, List.prod_append]
      have hA : ((G χ0).map f).prod = f (χ0 S) ^ N := by
        simp [G, List.map_replicate, List.prod_replicate]
      rcases List.mem_cons.1 hχ with rfl | hr
      · have hcomm : Commute ((G χ).map f).prod ((rest.flatMap G).map f).prod := by
          rw [hA]; exact (hcl _ _).pow_left N
        rw [hcomm.eq, Module.End.mul_apply, hA, h0, map_zero]
      · rw [Module.End.mul_apply, ih φ ⟨χ, hr, h0⟩, map_zero]
  refine ⟨hX.toFinset.toList.flatMap G, fun φ hφ => ?_⟩
  have hsub : formsGL E a L W X N ⊆ (LinearMap.ker ((hX.toFinset.toList.flatMap G).map f).prod : Set (Sm E a)) := by
    intro ψ hψ
    obtain ⟨χ, hχX, hχ⟩ := hψ.2.2.2
    exact LinearMap.mem_ker.2 (main _ ψ ⟨χ, by simpa using hχX, hpow χ ψ hχ⟩)
  exact LinearMap.mem_ker.1 ((Submodule.span_le.2 hsub) hφ)

end GlobalTheory.HCF
