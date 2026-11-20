import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

noncomputable section

open Matrix GlobalTheory.SmGL GlobalTheory.PRep

namespace GlobalTheory.LocGL

section Rad

variable {R S : Type} [CommRing R] [CommRing S] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

/- English proof (translation)
Take `⟨h1, h2⟩` from `mem_unipRad.1 hg`. Use `mem_unipRad.2 ⟨mem_parab.2 fun i j hij => ?_, fun a i j => ?_⟩` and prove the remaining obligations. Use `show f ((g : Matrix n n R) i j) = 0`. Rewrite using `[mem_parab.1 h1 i j hij, map_zero]`. Use `show f ((g : Matrix n n R) _ _) = _`.

Rewrite using `[h2 a i j, one_apply, one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem map_mem_unipRad_of_ringHom (f : R →+* S) {e : (Σ a, m a) ≃ n} {g : GL n R} (hg : g ∈ unipRad R e) :
    GeneralLinearGroup.map f g ∈ unipRad S e := by
  obtain ⟨h1, h2⟩ := mem_unipRad.1 hg
  refine mem_unipRad.2 ⟨mem_parab.2 fun i j hij => ?_, fun a i j => ?_⟩
  · show f ((g : Matrix n n R) i j) = 0
    rw [mem_parab.1 h1 i j hij, map_zero]
  · show f ((g : Matrix n n R) _ _) = _
    rw [h2 a i j, one_apply, one_apply]
    split_ifs <;> simp

end Rad

/- English proof (translation)
Use `set M := GeneralLinearGroup.map (n := n) i.symm.toRingHom with hM`. Establish `hc : Continuous M` using `Units.continuous_iff.2 ⟨continuous_matrix fun a b => hi.comp (Units.continuous_val.matrix_elem a b), continuous_matrix fun a b => hi.comp (Units.continuous_coe_inv.matrix_elem a b)⟩`. Use `⟨fun v => (h.1 v).preimage hc, fun s d e he => ?_⟩` and prove the remaining obligations. Establish `hmem : ∀ u ∈ unipRad k' e, M u ∈ unipRad k e` using `fun u hu => map_mem_unipRad_of_ringHom _ hu`. Establish `hsurj : ∀ w ∈ unipRad k e, ∃ u ∈ unipRad k' e, M u = w` using `fun w hw => ⟨GeneralLinearGroup.map i.toRingHom w, map_mem_unipRad_of_ringHom _ hw, Units.ext (Matrix.ext fun _ _ => i.symm_apply_apply _)⟩`.

Establish `hinj : Function.Injective M` using `fun x y hxy => Units.ext (Matrix.ext fun a b => i.symm.injective (congrArg (fun g : GL n k => (g : Matrix n n k) a b) hxy))`. Establish `hne : unipRad k e ≠ ⊥` using `fun hb => he ((Subgroup.eq_bot_iff_forall _).2 fun u hu => hinj ((((Subgroup.eq_bot_iff_forall _).1 hb) _ (hmem u hu)).trans (map_one M).symm))`. Establish `h1 : twKer (π.comp M) (unipRad k' e) 1 = twKer π (unipRad k e) 1`. Unfold `twKer`. Use `congr 1`.

Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, v, rfl⟩`. Conclude with `⟨⟨M u, hmem u u.2⟩, v, by simp⟩`. Introduce and unpack `⟨u, v, rfl⟩`.

Take `⟨u', hu', hu⟩` from `hsurj u u.2`. Conclude with `⟨⟨u', hu'⟩, v, by simp [hu]⟩`. Conclude with `Submodule.Quotient.subsingleton_iff.2 (h1 ▸ Submodule.Quotient.subsingleton_iff.1 (h.2 s d e hne))`.
-/
theorem isCuspidal_comp_generalLinearGroupMap {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k']
    [IsNonarchimedeanLocalField k'] (i : k ≃+* k') (hi : Continuous i.symm) {n : Type} [Fintype n]
    [DecidableEq n] {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V)
    (h : IsCuspidal π) : IsCuspidal (π.comp (GeneralLinearGroup.map (n := n) i.symm.toRingHom)) := by
  set M := GeneralLinearGroup.map (n := n) i.symm.toRingHom with hM
  have hc : Continuous M :=
    Units.continuous_iff.2 ⟨continuous_matrix fun a b => hi.comp (Units.continuous_val.matrix_elem a b),
      continuous_matrix fun a b => hi.comp (Units.continuous_coe_inv.matrix_elem a b)⟩
  refine ⟨fun v => (h.1 v).preimage hc, fun s d e he => ?_⟩
  have hmem : ∀ u ∈ unipRad k' e, M u ∈ unipRad k e := fun u hu => map_mem_unipRad_of_ringHom _ hu
  have hsurj : ∀ w ∈ unipRad k e, ∃ u ∈ unipRad k' e, M u = w := fun w hw =>
    ⟨GeneralLinearGroup.map i.toRingHom w, map_mem_unipRad_of_ringHom _ hw,
      Units.ext (Matrix.ext fun _ _ => i.symm_apply_apply _)⟩
  have hinj : Function.Injective M := fun x y hxy => Units.ext (Matrix.ext fun a b =>
    i.symm.injective (congrArg (fun g : GL n k => (g : Matrix n n k) a b) hxy))
  have hne : unipRad k e ≠ ⊥ := fun hb => he ((Subgroup.eq_bot_iff_forall _).2 fun u hu =>
    hinj ((((Subgroup.eq_bot_iff_forall _).1 hb) _ (hmem u hu)).trans (map_one M).symm))
  have h1 : twKer (π.comp M) (unipRad k' e) 1 = twKer π (unipRad k e) 1 := by
    unfold twKer
    congr 1
    ext w
    constructor
    · rintro ⟨u, v, rfl⟩
      exact ⟨⟨M u, hmem u u.2⟩, v, by simp⟩
    · rintro ⟨u, v, rfl⟩
      obtain ⟨u', hu', hu⟩ := hsurj u u.2
      exact ⟨⟨u', hu'⟩, v, by simp [hu]⟩
  exact Submodule.Quotient.subsingleton_iff.2 (h1 ▸ Submodule.Quotient.subsingleton_iff.1 (h.2 s d e hne))

end GlobalTheory.LocGL
