import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlPiEquivSymmContinuous
open Matrix
open scoped Classical

namespace GlobalTheory.CentProd

open GlobalTheory.LKRes

noncomputable def incl {R S : Type} [CommRing R] [CommRing S] (d n : ℕ) (e : R ≃+* (Fin (d + 1) → S))
    (i : Fin (d + 1)) : GL (Fin n) S →* GL (Fin n) R :=
  (glPiEquiv d n e).symm.toMonoidHom.comp (MonoidHom.mulSingle (fun _ => GL (Fin n) S) i)

/- English proof (translation)
Simplify using `[incl]`.
-/
theorem glPiEquiv_incl {R S : Type} [CommRing R] [CommRing S] (d n : ℕ) (e : R ≃+* (Fin (d + 1) → S))
    (i : Fin (d + 1)) (g : GL (Fin n) S) : glPiEquiv d n e (incl d n e i g) = Pi.mulSingle i g := by
  simp [incl]

/- English proof (translation)
Simplify using `only [Subgroup.mem_centralizer_singleton_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h i`. Use `congrArg (fun x => glPiEquiv d n e x i) h` as an intermediate fact. Simplify `this` using `[map_mul]`.

Introduce `h`. Apply `(glPiEquiv d n e).injective` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Simplify `h i` using `[map_mul]`.
-/
theorem mem_centralizer_iff_comp {R S : Type} [CommRing R] [CommRing S] (d n : ℕ) (e : R ≃+* (Fin (d + 1) → S))
    (N z : GL (Fin n) R) :
    z ∈ Subgroup.centralizer {N} ↔ ∀ i, glPiEquiv d n e z i ∈ Subgroup.centralizer {glPiEquiv d n e N i} := by
  simp only [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h i
    have := congrArg (fun x => glPiEquiv d n e x i) h
    simpa [map_mul] using this
  · intro h
    apply (glPiEquiv d n e).injective
    funext i
    simpa [map_mul] using h i

/- English proof (translation)
Establish `h : (glPiEquiv d n e N i).val = ((Pi.evalRingHom (fun _ => S) i).comp (e : R →+* _)).mapMatrix N.val`. Use extensionality with `a b`. Both sides reduce to the same expression. Rewrite using `[h, RingHom.mapMatrix_apply, Matrix.charpoly_map]`.
-/
theorem charpoly_comp {R S : Type} [CommRing R] [CommRing S] (d n : ℕ) (e : R ≃+* (Fin (d + 1) → S))
    (N : GL (Fin n) R) (i : Fin (d + 1)) :
    (glPiEquiv d n e N i).val.charpoly = N.val.charpoly.map ((Pi.evalRingHom (fun _ => S) i).comp (e : R →+* _)) := by
  have h : (glPiEquiv d n e N i).val = ((Pi.evalRingHom (fun _ => S) i).comp (e : R →+* _)).mapMatrix N.val := by
    ext a b
    rfl
  rw [h, RingHom.mapMatrix_apply, Matrix.charpoly_map]

/- English proof (translation)
Introduce `R S _ _ d n e A B hAB hS N hN`. Use `set ψ := glPiEquiv d n e with hψ`. Establish `hNi : ∀ i, (ψ N i).val.charpoly.Separable` using `fun i => by`. Rewrite using `[hψ, charpoly_comp]`. Conclude with `hN.map`.

Use `choose Gs hGs1 hGs2 using fun i => hS (ψ N i) (hNi i)`. Establish `hinclC : ∀ i g, g ∈ Subgroup.centralizer {ψ N i} → incl d n e i g ∈ Subgroup.centralizer {N}`. Introduce `i g hg`. Rewrite using `[mem_centralizer_iff_comp d n e]`. Introduce `j`.

Rewrite using `[glPiEquiv_incl]`. Distinguish the cases in `hij : j = i`. Substitute `hij` using the available equality. Simplify using `using hg`. Rewrite using `[Pi.mulSingle_eq_of_ne hij]`.

Conclude with `one_mem _`. Establish `hinclA : ∀ i g, g ∈ (GeneralLinearGroup.map (n` using `Fin n) B.subtype).range → incl d n e i g ∈ (GeneralLinearGroup.map (n := Fin n) A.subtype).range := by`. Introduce `i g hg`. Rewrite using `[glPiEquiv_mem_iff d n e A B hAB]`. Introduce `j`.

Rewrite using `[glPiEquiv_incl]`. Distinguish the cases in `hij : j = i`. Substitute `hij` using the available equality. Simplify using `using hg`. Rewrite using `[Pi.mulSingle_eq_of_ne hij]`.

Conclude with `one_mem _`. Use `⟨Finset.univ.biUnion (fun i => (Gs i).image (incl d n e i)), ?_, ?_⟩` and prove the remaining obligations. Introduce `g hg`. Simplify using `only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at hg`. Take `⟨i, g', hg', rfl⟩` from `hg`.

Conclude with `hinclC i g' (hGs1 i g' hg')`. Introduce `z hz set K := Subgroup.closure (((Finset.univ.biUnion (fun i => (Gs i).image (incl d n e i)) : Finset _) : Set (GL (Fin n) R)) ∪ ((Subgroup.centralizer {N} ⊓ (GeneralLinearGroup.map (n := Fin n) A.subtype).range : Subgroup _) : Set (GL (Fin n) R))) with hK`. Establish `hpi : ψ z ∈ Subgroup.pi Set.univ (fun i => Subgroup.closure (((Gs i : Set (GL (Fin n) S))) ∪ ((Subgroup.centralizer {ψ N i} ⊓ (GeneralLinearGroup.map (n` using `Fin n) B.subtype).range : Subgroup _) : Set (GL (Fin n) S)))) := by`. Introduce `i _`. Conclude with `hGs2 i ((mem_centralizer_iff_comp d n e N z).1 hz i)`.

Establish `hle : Subgroup.pi Set.univ (fun i => Subgroup.closure (((Gs i : Set (GL (Fin n) S))) ∪ ((Subgroup.centralizer {ψ N i} ⊓ (GeneralLinearGroup.map (n` using `Fin n) B.subtype).range : Subgroup _) : Set (GL (Fin n) S)))) ≤ K.map ψ.toMonoidHom := by`. Rewrite using `[Subgroup.pi_le_iff]`. Introduce `i`. Rewrite using `[MonoidHom.map_closure, Subgroup.closure_le]`. Introduce and unpack `_ ⟨g, hg, rfl⟩`.

Rewrite using `[SetLike.mem_coe, Subgroup.mem_map_equiv]`. Establish `: (MonoidHom.mulSingle (fun _ => GL (Fin n) S) i) g = ψ (incl d n e i g)`. Rewrite using `[hψ, glPiEquiv_incl]`. Both sides reduce to the same expression. Rewrite using `[this, MulEquiv.symm_apply_apply]`.

Apply `Subgroup.subset_closure` to reduce the goal to its premises. Break down `hg with hg | hg` into its components or cases. Use `left`. Simplify using `only [Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion, Finset.coe_image, Set.mem_image, Finset.mem_coe]`. Conclude with `⟨i, g, hg, rfl⟩`.

Use `right`. Conclude with `⟨hinclC i g hg.1, hinclA i g hg.2⟩`. Use `hle hpi` as an intermediate fact. Rewrite `this` using `[Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]`. Conclude with `this`.
-/
theorem centralizer_fg_of_pi : ∀ (R S : Type) [CommRing R] [CommRing S] (d n : ℕ) (e : R ≃+* (Fin (d + 1) → S))
    (A : Subring R) (B : Subring S), (∀ x : R, x ∈ A ↔ ∀ i, e x i ∈ B) →
    (∀ N : GL (Fin n) S, N.val.charpoly.Separable → ∃ G : Finset (GL (Fin n) S),
      (∀ g ∈ G, g ∈ Subgroup.centralizer {N}) ∧
      Subgroup.centralizer {N} ≤ Subgroup.closure ((G : Set (GL (Fin n) S)) ∪
        ((Subgroup.centralizer {N} ⊓ (GeneralLinearGroup.map (n := Fin n) B.subtype).range : Subgroup _) :
          Set (GL (Fin n) S)))) →
    ∀ N : GL (Fin n) R, N.val.charpoly.Separable → ∃ G : Finset (GL (Fin n) R),
      (∀ g ∈ G, g ∈ Subgroup.centralizer {N}) ∧
      Subgroup.centralizer {N} ≤ Subgroup.closure ((G : Set (GL (Fin n) R)) ∪
        ((Subgroup.centralizer {N} ⊓ (GeneralLinearGroup.map (n := Fin n) A.subtype).range : Subgroup _) :
          Set (GL (Fin n) R))) := by
  intro R S _ _ d n e A B hAB hS N hN
  set ψ := glPiEquiv d n e with hψ
  have hNi : ∀ i, (ψ N i).val.charpoly.Separable := fun i => by
    rw [hψ, charpoly_comp]; exact hN.map
  choose Gs hGs1 hGs2 using fun i => hS (ψ N i) (hNi i)

  have hinclC : ∀ i g, g ∈ Subgroup.centralizer {ψ N i} → incl d n e i g ∈ Subgroup.centralizer {N} := by
    intro i g hg
    rw [mem_centralizer_iff_comp d n e]
    intro j
    rw [glPiEquiv_incl]
    by_cases hij : j = i
    · subst hij; simpa using hg
    · rw [Pi.mulSingle_eq_of_ne hij]; exact one_mem _
  have hinclA : ∀ i g, g ∈ (GeneralLinearGroup.map (n := Fin n) B.subtype).range →
      incl d n e i g ∈ (GeneralLinearGroup.map (n := Fin n) A.subtype).range := by
    intro i g hg
    rw [glPiEquiv_mem_iff d n e A B hAB]
    intro j
    rw [glPiEquiv_incl]
    by_cases hij : j = i
    · subst hij; simpa using hg
    · rw [Pi.mulSingle_eq_of_ne hij]; exact one_mem _
  refine ⟨Finset.univ.biUnion (fun i => (Gs i).image (incl d n e i)), ?_, ?_⟩
  · intro g hg
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at hg
    obtain ⟨i, g', hg', rfl⟩ := hg
    exact hinclC i g' (hGs1 i g' hg')
  · intro z hz
    set K := Subgroup.closure (((Finset.univ.biUnion (fun i => (Gs i).image (incl d n e i)) : Finset _) :
      Set (GL (Fin n) R)) ∪
        ((Subgroup.centralizer {N} ⊓ (GeneralLinearGroup.map (n := Fin n) A.subtype).range : Subgroup _) :
          Set (GL (Fin n) R))) with hK
    have hpi : ψ z ∈ Subgroup.pi Set.univ (fun i => Subgroup.closure (((Gs i : Set (GL (Fin n) S))) ∪
        ((Subgroup.centralizer {ψ N i} ⊓ (GeneralLinearGroup.map (n := Fin n) B.subtype).range : Subgroup _) :
          Set (GL (Fin n) S)))) := by
      intro i _
      exact hGs2 i ((mem_centralizer_iff_comp d n e N z).1 hz i)
    have hle : Subgroup.pi Set.univ (fun i => Subgroup.closure (((Gs i : Set (GL (Fin n) S))) ∪
        ((Subgroup.centralizer {ψ N i} ⊓ (GeneralLinearGroup.map (n := Fin n) B.subtype).range : Subgroup _) :
          Set (GL (Fin n) S)))) ≤ K.map ψ.toMonoidHom := by
      rw [Subgroup.pi_le_iff]
      intro i
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨g, hg, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_map_equiv]
      have : (MonoidHom.mulSingle (fun _ => GL (Fin n) S) i) g = ψ (incl d n e i g) := by
        rw [hψ, glPiEquiv_incl]; rfl
      rw [this, MulEquiv.symm_apply_apply]
      apply Subgroup.subset_closure
      rcases hg with hg | hg
      · left
        simp only [Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion,
          Finset.coe_image, Set.mem_image, Finset.mem_coe]
        exact ⟨i, g, hg, rfl⟩
      · right
        exact ⟨hinclC i g hg.1, hinclA i g hg.2⟩
    have := hle hpi
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at this
    exact this

end GlobalTheory.CentProd
