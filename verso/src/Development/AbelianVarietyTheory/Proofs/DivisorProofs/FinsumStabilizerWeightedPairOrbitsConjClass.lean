import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemStabilizerIff
open scoped Classical

namespace GlobalTheory.MassConj

/- English proof (translation)
Establish `h` using `Quotient.mk_out (s := MulAction.orbitRel H α) a`. Express the relevant statement in the definitionally equal form `MulAction.orbitRel H α _ _ at h`. Rewrite `h` using `[MulAction.orbitRel_apply, MulAction.mem_orbit_iff]`. Take `⟨g, hg⟩` from `h`. Conclude with `⟨g, hg.symm⟩`.
-/
theorem exists_out_mk_eq_smul {H α : Type} [Group H] [MulAction H α] (a : α) :
    ∃ g : H, Quotient.out (Quotient.mk (MulAction.orbitRel H α) a :
      MulAction.orbitRel.Quotient H α) = g • a := by
  have h := Quotient.mk_out (s := MulAction.orbitRel H α) a
  change MulAction.orbitRel H α _ _ at h
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
  obtain ⟨g, hg⟩ := h
  exact ⟨g, hg.symm⟩

/- English proof (translation)
Use `set C : Subgroup G := Γ ⊓ Subgroup.centralizer {(γ₀ : G)} with hC`. Establish `memC : ∀ δ : Γ, δ * γ₀ = γ₀ * δ → (δ : G) ∈ C`. Introduce `δ h`. Rewrite using `[hC, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]`. Use `⟨δ.2, ?_⟩` and prove the remaining obligations.

Introduce `g hg`. Rewrite `hg` using `[Set.mem_singleton_iff]`. Substitute `hg` using the available equality. Use `congrArg (fun z : Γ => (z : G)) h` as an intermediate fact. Simplify using `using this.symm`.

Establish `commC : ∀ c : C, (⟨c, c.2.1⟩ : Γ) * γ₀ = γ₀ * ⟨c, c.2.1⟩`. Introduce `c`. Establish `h2` using `(Subgroup.mem_inf.mp c.2).2`. Rewrite `h2` using `[Subgroup.mem_centralizer_iff]`. Establish `h` using `h2 γ₀ (Set.mem_singleton _)`.

Use `ext`. Simplify using `[h]`. Set `f : MulAction.orbitRel.Quotient C X → {O : MulAction.orbitRel.Quotient Γ (ConjPair Γ X) // ConjClasses.mk (Quotient.out O).elt = ConjClasses.mk γ₀}` to `fun b => ⟨Quotient.mk _ ⟨γ₀, Quotient.out b⟩, by`. Take `⟨δ, hδ⟩` from `exists_out_mk_eq_smul (H := Γ) (ConjPair.mk γ₀ (Quotient.out b))`. Rewrite using `[hδ, smul_elt, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]`.

Conclude with `⟨δ⁻¹, by group⟩⟩`. Establish `inj : Function.Injective f`. Introduce `b b' hbb`. Establish `h1` using `congrArg Subtype.val hbb`. Simplify using `only [f] at h1`.

Establish `h2` using `Quotient.exact h1`. Express the relevant statement in the definitionally equal form `MulAction.orbitRel Γ _ _ _ at h2`. Rewrite `h2` using `[MulAction.orbitRel_apply, MulAction.mem_orbit_iff]`. Take `⟨δ, hδ⟩` from `h2`. Establish `he` using `congrArg ConjPair.elt hδ`.

Establish `hp` using `congrArg ConjPair.pt hδ`. Simplify using `only [smul_elt, smul_pt] at he hp`. Establish `hcomm : δ * γ₀ = γ₀ * δ`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Quotient.out_eq b, ← Quotient.out_eq b']`.

Apply `Quotient.sound` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `MulAction.orbitRel C X _ _`. Rewrite using `[MulAction.orbitRel_apply, MulAction.mem_orbit_iff]`. Conclude with `⟨⟨δ, memC δ hcomm⟩, hp⟩`. Establish `surj : Function.Surjective f`.

Introduce and unpack `⟨O, hO⟩`. Rewrite `hO` using `[ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]`. Take `⟨δ, hδ⟩` from `hO`. Take `⟨c, hc⟩` from `exists_out_mk_eq_smul (H := C) (δ • (Quotient.out O).pt)`. Use `⟨Quotient.mk _ (δ • (Quotient.out O).pt), ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [f]`. Use `conv_rhs => rw [← Quotient.out_eq O]`. Apply `Quotient.sound` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `MulAction.orbitRel Γ _ _ _`.

Rewrite using `[MulAction.orbitRel_apply, MulAction.mem_orbit_iff]`. Use `⟨(⟨c, c.2.1⟩ : Γ) * δ, ?_⟩` and prove the remaining obligations. Rewrite using `[hc, mul_smul]`. Use `ext`. Simplify using `only [smul_elt]`.

Rewrite using `[hδ, commC c]`. Use `group`. Simplify using `only [smul_pt]`. Both sides reduce to the same expression. Establish `term : ∀ b : MulAction.orbitRel.Quotient C X, (1 / (Nat.card (MulAction.stabilizer Γ (Quotient.out (f b).1)) : ℂ)) * Φ (Quotient.out (f b).1).elt (Quotient.out (f b).1).pt = (1 / (Nat.card (MulAction.stabilizer C (Quotient.out b)) : ℂ)) * Φ γ₀ (Quotient.out b)`.

Introduce `b`. Take `⟨δ, hδ⟩` from `exists_out_mk_eq_smul (H := Γ) (ConjPair.mk γ₀ (Quotient.out b))`. Establish `hfb : (f b).1 = Quotient.mk _ (ConjPair.mk γ₀ (Quotient.out b))` using `rfl`. Rewrite using `[hfb, hδ, smul_elt, smul_pt]`. Establish `hcard1 : Nat.card (MulAction.stabilizer Γ (δ • ConjPair.mk γ₀ (Quotient.out b))) = Nat.card (MulAction.stabilizer Γ (ConjPair.mk γ₀ (Quotient.out b)))` using `Nat.card_congr (MulAction.stabilizerEquivStabilizer rfl).toEquiv.symm`.

Establish `h_to : ∀ s : MulAction.stabilizer Γ (ConjPair.mk γ₀ (Quotient.out b) : ConjPair Γ X), ((s : Γ) : G) ∈ C` using `fun s => memC s.1 ((GlobalTheory.MassConj.mem_stabilizer_iff _ _).mp s.2).1`. Establish `h_to' : ∀ s : MulAction.stabilizer Γ (ConjPair.mk γ₀ (Quotient.out b) : ConjPair Γ X), (⟨((s : Γ) : G), h_to s⟩ : C) ∈ MulAction.stabilizer C (Quotient.out b)`. Introduce `s`. Rewrite using `[MulAction.mem_stabilizer_iff]`. Conclude with `((GlobalTheory.MassConj.mem_stabilizer_iff _ _).mp s.2).2`.

Establish `h_inv : ∀ t : MulAction.stabilizer C (Quotient.out b), (⟨((t : C) : G), (t : C).2.1⟩ : Γ) ∈ MulAction.stabilizer Γ (ConjPair.mk γ₀ (Quotient.out b) : ConjPair Γ X)`. Introduce `t`. Rewrite using `[GlobalTheory.MassConj.mem_stabilizer_iff]`. Conclude with `⟨commC t.1, MulAction.mem_stabilizer_iff.mp t.2⟩`. Establish `hcard2 : Nat.card (MulAction.stabilizer Γ (ConjPair.mk γ₀ (Quotient.out b) : ConjPair Γ X)) = Nat.card (MulAction.stabilizer C (Quotient.out b))` using `Nat.card_congr { toFun := fun s => ⟨⟨((s : Γ) : G), h_to s⟩, h_to' s⟩ invFun := fun t => ⟨⟨((t : C) : G), (t : C).2.1⟩, h_inv t⟩ left_inv := fun s => rfl right_inv := fun t => rfl }`.

Establish `hphi : Φ (δ * γ₀ * δ⁻¹) (δ • Quotient.out b) = Φ γ₀ (Quotient.out b)` using `hΦ δ γ₀ (Quotient.out b)`. Rewrite using `[hcard1, hcard2, hphi]`. Use `(finsum_comp_equiv (Equiv.ofBijective f ⟨inj, surj⟩)).symm.trans ?_` and prove the remaining obligations. Conclude with `finsum_congr term`.
-/
theorem finsum_pairOrbit_fibre (G : Type) [Group G] (X : Type) [MulAction G X] (Γ : Subgroup G)
    (Φ : Γ → X → ℂ)
    (hΦ : ∀ δ γ : Γ, ∀ x : X, Φ (δ * γ * δ⁻¹) ((δ : G) • x) = Φ γ x) (γ₀ : Γ) :
    ∑ᶠ O : {O : MulAction.orbitRel.Quotient Γ (ConjPair Γ X) //
        ConjClasses.mk (Quotient.out O).elt = ConjClasses.mk γ₀},
        (1 / (Nat.card (MulAction.stabilizer Γ (Quotient.out O.1)) : ℂ)) *
          Φ (Quotient.out O.1).elt (Quotient.out O.1).pt =
      ∑ᶠ b : MulAction.orbitRel.Quotient (Γ ⊓ Subgroup.centralizer {(γ₀ : G)} : Subgroup G) X,
        (1 / (Nat.card (MulAction.stabilizer (Γ ⊓ Subgroup.centralizer {(γ₀ : G)} : Subgroup G)
          (Quotient.out b)) : ℂ)) * Φ γ₀ (Quotient.out b) := by
  set C : Subgroup G := Γ ⊓ Subgroup.centralizer {(γ₀ : G)} with hC
  have memC : ∀ δ : Γ, δ * γ₀ = γ₀ * δ → (δ : G) ∈ C := by
    intro δ h
    rw [hC, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    refine ⟨δ.2, ?_⟩
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    have := congrArg (fun z : Γ => (z : G)) h
    simpa using this.symm
  have commC : ∀ c : C, (⟨c, c.2.1⟩ : Γ) * γ₀ = γ₀ * ⟨c, c.2.1⟩ := by
    intro c
    have h2 := (Subgroup.mem_inf.mp c.2).2
    rw [Subgroup.mem_centralizer_iff] at h2
    have h := h2 γ₀ (Set.mem_singleton _)
    ext
    simp [h]
  let f : MulAction.orbitRel.Quotient C X →
      {O : MulAction.orbitRel.Quotient Γ (ConjPair Γ X) //
        ConjClasses.mk (Quotient.out O).elt = ConjClasses.mk γ₀} :=
    fun b => ⟨Quotient.mk _ ⟨γ₀, Quotient.out b⟩, by
      obtain ⟨δ, hδ⟩ := exists_out_mk_eq_smul (H := Γ) (ConjPair.mk γ₀ (Quotient.out b))
      rw [hδ, smul_elt, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
      exact ⟨δ⁻¹, by group⟩⟩
  have inj : Function.Injective f := by
    intro b b' hbb
    have h1 := congrArg Subtype.val hbb
    simp only [f] at h1
    have h2 := Quotient.exact h1
    change MulAction.orbitRel Γ _ _ _ at h2
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h2
    obtain ⟨δ, hδ⟩ := h2
    have he := congrArg ConjPair.elt hδ
    have hp := congrArg ConjPair.pt hδ
    simp only [smul_elt, smul_pt] at he hp
    have hcomm : δ * γ₀ = γ₀ * δ := by
      calc δ * γ₀ = δ * γ₀ * δ⁻¹ * δ := by group
        _ = γ₀ * δ := by rw [he]
    rw [← Quotient.out_eq b, ← Quotient.out_eq b']
    apply Quotient.sound
    change MulAction.orbitRel C X _ _
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    exact ⟨⟨δ, memC δ hcomm⟩, hp⟩
  have surj : Function.Surjective f := by
    rintro ⟨O, hO⟩
    rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at hO
    obtain ⟨δ, hδ⟩ := hO
    obtain ⟨c, hc⟩ := exists_out_mk_eq_smul (H := C) (δ • (Quotient.out O).pt)
    refine ⟨Quotient.mk _ (δ • (Quotient.out O).pt), ?_⟩
    apply Subtype.ext
    simp only [f]
    conv_rhs => rw [← Quotient.out_eq O]
    apply Quotient.sound
    change MulAction.orbitRel Γ _ _ _
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    refine ⟨(⟨c, c.2.1⟩ : Γ) * δ, ?_⟩
    rw [hc, mul_smul]
    ext
    · simp only [smul_elt]
      rw [hδ, commC c]
      group
    · simp only [smul_pt]
      rfl
  have term : ∀ b : MulAction.orbitRel.Quotient C X,
      (1 / (Nat.card (MulAction.stabilizer Γ (Quotient.out (f b).1)) : ℂ)) *
          Φ (Quotient.out (f b).1).elt (Quotient.out (f b).1).pt =
        (1 / (Nat.card (MulAction.stabilizer C (Quotient.out b)) : ℂ)) * Φ γ₀ (Quotient.out b) := by
    intro b
    obtain ⟨δ, hδ⟩ := exists_out_mk_eq_smul (H := Γ) (ConjPair.mk γ₀ (Quotient.out b))
    have hfb : (f b).1 = Quotient.mk _ (ConjPair.mk γ₀ (Quotient.out b)) := rfl
    rw [hfb, hδ, smul_elt, smul_pt]
    have hcard1 : Nat.card (MulAction.stabilizer Γ (δ • ConjPair.mk γ₀ (Quotient.out b))) =
        Nat.card (MulAction.stabilizer Γ (ConjPair.mk γ₀ (Quotient.out b))) :=
      Nat.card_congr (MulAction.stabilizerEquivStabilizer rfl).toEquiv.symm
    have h_to : ∀ s : MulAction.stabilizer Γ (ConjPair.mk γ₀ (Quotient.out b) : ConjPair Γ X),
        ((s : Γ) : G) ∈ C := fun s =>
      memC s.1 ((GlobalTheory.MassConj.mem_stabilizer_iff _ _).mp s.2).1
    have h_to' : ∀ s : MulAction.stabilizer Γ (ConjPair.mk γ₀ (Quotient.out b) : ConjPair Γ X),
        (⟨((s : Γ) : G), h_to s⟩ : C) ∈ MulAction.stabilizer C (Quotient.out b) := by
      intro s
      rw [MulAction.mem_stabilizer_iff]
      exact ((GlobalTheory.MassConj.mem_stabilizer_iff _ _).mp s.2).2
    have h_inv : ∀ t : MulAction.stabilizer C (Quotient.out b),
        (⟨((t : C) : G), (t : C).2.1⟩ : Γ) ∈
          MulAction.stabilizer Γ (ConjPair.mk γ₀ (Quotient.out b) : ConjPair Γ X) := by
      intro t
      rw [GlobalTheory.MassConj.mem_stabilizer_iff]
      exact ⟨commC t.1, MulAction.mem_stabilizer_iff.mp t.2⟩
    have hcard2 : Nat.card (MulAction.stabilizer Γ (ConjPair.mk γ₀ (Quotient.out b) : ConjPair Γ X)) =
        Nat.card (MulAction.stabilizer C (Quotient.out b)) :=
      Nat.card_congr
        { toFun := fun s => ⟨⟨((s : Γ) : G), h_to s⟩, h_to' s⟩
          invFun := fun t => ⟨⟨((t : C) : G), (t : C).2.1⟩, h_inv t⟩
          left_inv := fun s => rfl
          right_inv := fun t => rfl }
    have hphi : Φ (δ * γ₀ * δ⁻¹) (δ • Quotient.out b) = Φ γ₀ (Quotient.out b) :=
      hΦ δ γ₀ (Quotient.out b)
    rw [hcard1, hcard2, hphi]
  refine (finsum_comp_equiv (Equiv.ofBijective f ⟨inj, surj⟩)).symm.trans ?_
  exact finsum_congr term

end GlobalTheory.MassConj
