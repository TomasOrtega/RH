import Mathlib
import Formalism.GaloisCohomology.LocalTateDualityK
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory

/- English proof (translation)
Simplify using `only [Sha1, Submodule.mem_iInf, LinearMap.mem_ker]`. Use `forall_congr' fun i => ?_` and prove the remaining obligations. Establish `: resH1 τ (φ i) (hφ i) (Submodule.Quotient.mk z) = Submodule.Quotient.mk (restrictCocycles1 τ (φ i) (hφ i) z)` using `rfl`. Rewrite using `[this, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, mem_coboundaries1]`. Both sides reduce to the same expression.
-/
theorem mk_mem_sha1_iff_locally_coboundary {R : Type} [CommRing R] {Γ : Type} [Group Γ]
    [TopologicalSpace Γ] {I : Type} {D : I → Type} [∀ i, Group (D i)]
    [∀ i, TopologicalSpace (D i)] (φ : ∀ i, D i →* Γ) (hφ : ∀ i, Continuous (φ i)) {N : Type}
    [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [ContinuousConstSMul R N] (τ : Representation R Γ N) (z : Z1 τ) :
    (Submodule.Quotient.mk z : H1 τ) ∈ Sha1 τ φ hφ ↔
      ∀ i, ∃ b : N, ∀ g, z.1 (φ i g) = τ (φ i g) b - b := by
  simp only [Sha1, Submodule.mem_iInf, LinearMap.mem_ker]
  refine forall_congr' fun i => ?_
  have : resH1 τ (φ i) (hφ i) (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (restrictCocycles1 τ (φ i) (hφ i) z) := rfl
  rw [this, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, mem_coboundaries1]
  rfl

/- English proof (translation)
Introduce `l _ Γ _ _ _ I _ D _ _ φ hφ A _ _ _ _ σ htor`. Establish `hup : ∀ (r s : ℕ) (a : A), r ≤ s → (l : ℤ_[l]) ^ r • a = 0 → (l : ℤ_[l]) ^ s • a = 0`. Introduce `r s a hrs h`. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hrs`. Rewrite using `[pow_add, mul_comm, mul_smul, h, smul_zero]`.

Set `P : ℕ → Submodule ℤ_[l] (Sha1 σ φ hφ)` to `fun r => { carrier := {x | ∃ z : Z1 σ, (Submodule.Quotient.mk z : H1 σ) = x.1 ∧ (∀ g, (l : ℤ_[l]) ^ r • z.1 g = 0) ∧ ∀ i, ∃ a : A, (l : ℤ_[l]) ^ r • a = 0 ∧ ∀ g, z.1 (φ i g) = σ (φ i g) a - a} zero_mem' := ⟨0, rfl, fun g => by simp, fun i => ⟨0, by simp, fun g => by simp⟩⟩ add_me …`. Introduce and unpack `x y ⟨z, hz, hz1, hz2⟩ ⟨w, hw, hw1, hw2⟩`. Use `⟨z + w, by rw [Submodule.Quotient.mk_add, hz, hw]; rfl, fun g => ?_, fun i => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ • (z.1 g + w.1 g) = 0`. Rewrite using `[smul_add, hz1, hw1, add_zero]`.

Take `⟨a, ha, ha'⟩` from `hz2 i`. Take `⟨b, hb, hb'⟩` from `hw2 i`. Use `⟨a + b, by rw [smul_add, ha, hb, add_zero], fun g => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `z.1 _ + w.1 _ = _`. Rewrite using `[ha', hb', map_add]`.

Normalize the expressions using the abelian group laws. Use the proof step `smul_mem' := by`. Introduce and unpack `c x ⟨z, hz, hz1, hz2⟩`. Use `⟨c • z, by rw [Submodule.Quotient.mk_smul, hz]; rfl, fun g => ?_, fun i => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ • (c • z.1 g) = 0`.

Rewrite using `[smul_comm, hz1, smul_zero]`. Take `⟨a, ha, ha'⟩` from `hz2 i`. Use `⟨c • a, by rw [smul_comm, ha, smul_zero], fun g => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `c • z.1 _ = _`. Rewrite using `[ha', map_smul, smul_sub] }`.

Establish `hP : ∀ r x, x ∈ P r ↔ ∃ z : Z1 σ, (Submodule.Quotient.mk z : H1 σ) = x.1 ∧ (∀ g, (l : ℤ_[l]) ^ r • z.1 g = 0) ∧ ∀ i, ∃ a : A, (l : ℤ_[l]) ^ r • a = 0 ∧ ∀ g, z.1 (φ i g) = σ (φ i g) a - a` using `fun r x => Iff.rfl`. Use `⟨P, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `r s hrs x hx`. Take `⟨z, hz, hz1, hz2⟩` from `(hP r x).1 hx`. Use `(hP s x).2 ⟨z, hz, fun g => hup r s _ hrs (hz1 g), fun i => ?_⟩` and prove the remaining obligations.

Take `⟨a, ha, ha'⟩` from `hz2 i`. Conclude with `⟨a, hup r s _ hrs ha, ha'⟩`. Introduce and unpack `⟨y, hy⟩`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Use `choose b hb using (mk_mem_sha1_iff_locally_coboundary φ hφ σ z).1 hy`.

Use `choose e he using htor`. Establish `hfin : (Set.range z.1 ∪ Set.range b).Finite` using `(isCompact_range z.2.1).finite_of_discrete.union (Set.finite_range b)`. Take `⟨r, hr⟩` from `(hfin.image e).bddAbove`. Use `⟨r, (hP r _).2 ⟨z, rfl, fun g => hup _ _ _ (hr ⟨_, Or.inl ⟨g, rfl⟩, rfl⟩) (he _), fun i => ⟨b i, hup _ _ _ (hr ⟨_, Or.inr ⟨i, rfl⟩, rfl⟩) (he _), hb i⟩⟩⟩` and prove the remaining obligations. Introduce `r R _ N _ _ _ _ τ ι hinj hrange heq hloc`.

Set `ιZ : Z1 τ →+ Z1 σ` to `{ toFun := fun z => ⟨fun g => ι (z.1 g), continuous_of_discreteTopology.comp z.2.1, fun g h => by beta_reduce; rw [z.2.2, map_add, heq]⟩ map_zero' := Subtype.ext (funext fun g => map_zero ι) map_add' := fun z w => Subtype.ext (funext fun g => map_add ι _ _) }`. Establish `hιZ : ∀ z g, (ιZ z).1 g = ι (z.1 g)` using `fun _ _ => rfl`. Set `F : H1 τ →+ H1 σ` to `QuotientAddGroup.map ((B1 τ).comap (Z1 τ).subtype).toAddSubgroup ((B1 σ).comap (Z1 σ).subtype).toAddSubgroup ιZ (by`. Introduce `z hz`. Take `⟨m, hm⟩` from `(mem_coboundaries1 τ _).1 hz`.

Use `(mem_coboundaries1 σ _).2 ⟨ι m, fun g => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ι (z.1 g) = _`. Rewrite using `[← heq, ← map_sub]`. Conclude with `congrArg ι (hm g))`. Establish `hF : ∀ z, F (Submodule.Quotient.mk z) = Submodule.Quotient.mk (ιZ z)` using `fun _ => rfl`.

Establish `hkill : ∀ n, (l : ℤ_[l]) ^ r • ι n = 0` using `fun n => (hrange _).2 ⟨n, rfl⟩`. Establish `hmem : ∀ x : H1 τ, x ∈ Sha1 τ φ hφ → ∃ h : F x ∈ Sha1 σ φ hφ, ⟨F x, h⟩ ∈ P r`. Introduce `x hx`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Establish `h1` using `(mk_mem_sha1_iff_locally_coboundary φ hφ τ z).1 hx`.

Establish `h2 : ∀ i, ∃ a : A, (l : ℤ_[l]) ^ r • a = 0 ∧ ∀ g, (ιZ z).1 (φ i g) = σ (φ i g) a - a`. Introduce `i`. Take `⟨b, hb⟩` from `h1 i`. Conclude with `⟨ι b, hkill b, fun g => by rw [hιZ, hb, map_sub, heq]⟩`. Use `⟨?_, (hP r _).2 ⟨ιZ z, rfl, fun g => hkill _, h2⟩⟩` and prove the remaining obligations.

Rewrite using `[hF, mk_mem_sha1_iff_locally_coboundary]`. Introduce `i`. Take `⟨a, -, ha⟩` from `h2 i`. Conclude with `⟨a, ha⟩`. Establish `hker : ∀ x : H1 τ, x ∈ Sha1 τ φ hφ → F x = 0 → x = 0`.

Introduce `x hx h0`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Establish `h1` using `(mk_mem_sha1_iff_locally_coboundary φ hφ τ z).1 hx`. Rewrite `h0` using `[hF, Submodule.Quotient.mk_eq_zero]`. Take `⟨a, ha⟩` from `(mem_coboundaries1 σ _).1 h0`.

Establish `ha' : ∀ g, ι (z.1 g) = σ g a - a` using `ha`. Take `⟨b, hb, hb'⟩` from `hloc a (fun i => by`. Take `⟨b, hb⟩` from `h1 i`. Conclude with `⟨ι b, hkill b, fun g => by rw [← ha', hb, map_sub, heq]⟩)`. Take `⟨n, rfl⟩` from `(hrange b).1 hb`.

Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Use `(mem_coboundaries1 τ _).2 ⟨n, fun g => hinj ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ι (z.1 g) = _`. Rewrite using `[ha', hb', map_sub, heq]`. Set `f : Sha1 τ φ hφ → P r` to `fun x => ⟨⟨F x.1, (hmem x.1 x.2).1⟩, (hmem x.1 x.2).2⟩`.

Use `(Nat.card_eq_of_bijective f ⟨?_, ?_⟩).symm` and prove the remaining obligations. Introduce `x y hxy`. Establish `h : F x.1 = F y.1` using `congrArg (fun t : P r => t.1.1) hxy`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← sub_eq_zero]`.

Conclude with `hker _ (sub_mem x.2 y.2) (by rw [map_sub, h, sub_self])`. Introduce and unpack `⟨x, hx⟩`. Take `⟨z, hz, hz1, hz2⟩` from `(hP r x).1 hx`. Establish `hlift : ∀ g, ∃ n, ι n = z.1 g` using `fun g => (hrange _).1 (hz1 g)`. Use `choose w hw using hlift`.

Establish `hwc : Continuous w`. Establish `: w = Function.invFun ι ∘ z.1`. Use function extensionality and compare the values at `g`. Rewrite using `[Function.comp_apply, ← hw, Function.leftInverse_invFun hinj]`. Rewrite using `[this]`.

Conclude with `continuous_of_discreteTopology.comp z.2.1`. Set `z' : Z1 τ` to `⟨w, hwc, fun g h => hinj (by rw [map_add, heq, hw, hw, hw, z.2.2])⟩`. Establish `hz' : ιZ z' = z` using `Subtype.ext (funext hw)`. Use `⟨⟨Submodule.Quotient.mk z', ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[mk_mem_sha1_iff_locally_coboundary]`.

Introduce `i`. Take `⟨a, ha, ha'⟩` from `hz2 i`. Take `⟨n, rfl⟩` from `(hrange a).1 ha`. Use `⟨n, fun g => hinj ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ι (w _) = _`.

Rewrite using `[hw, ha', map_sub, heq]`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `F (Submodule.Quotient.mk z') = x.1`. Rewrite using `[hF, hz', hz]`.
-/
theorem sha1_exhausted_by_torsion_levels : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (I : Type) [Finite I] (D : I → Type) [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)] (φ : ∀ i, D i →* Γ) (hφ : ∀ i, Continuous (φ i)) (A : Type) [AddCommGroup A] [Module ℤ_[l] A] [TopologicalSpace A] [DiscreteTopology A] (σ : Representation ℤ_[l] Γ A), (∀ a : A, ∃ r : ℕ, (l : ℤ_[l]) ^ r • a = 0) → ∃ P : ℕ → Submodule ℤ_[l] (Sha1 σ φ hφ), Monotone P ∧ (∀ y, ∃ r, y ∈ P r) ∧ ∀ (r : ℕ) (R : Type) [CommRing R] (N : Type) [AddCommGroup N] [Module R N] [TopologicalSpace N] [DiscreteTopology N] (τ : Representation R Γ N) (ι : N →+ A), Function.Injective ι → (∀ a : A, (l : ℤ_[l]) ^ r • a = 0 ↔ a ∈ Set.range ι) → (∀ g n, ι (τ g n) = σ g (ι n)) → (∀ a : A, (∀ i, ∃ b : A, (l : ℤ_[l]) ^ r • b = 0 ∧ ∀ g, σ (φ i g) a - a = σ (φ i g) b - b) → ∃ b : A, (l : ℤ_[l]) ^ r • b = 0 ∧ ∀ g, σ g a - a = σ g b - b) → Nat.card (P r) = Nat.card (Sha1 τ φ hφ) := by
  intro l _ Γ _ _ _ I _ D _ _ φ hφ A _ _ _ _ σ htor
  have hup : ∀ (r s : ℕ) (a : A), r ≤ s → (l : ℤ_[l]) ^ r • a = 0 → (l : ℤ_[l]) ^ s • a = 0 := by
    intro r s a hrs h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hrs
    rw [pow_add, mul_comm, mul_smul, h, smul_zero]
  let P : ℕ → Submodule ℤ_[l] (Sha1 σ φ hφ) := fun r =>
    { carrier := {x | ∃ z : Z1 σ, (Submodule.Quotient.mk z : H1 σ) = x.1 ∧
        (∀ g, (l : ℤ_[l]) ^ r • z.1 g = 0) ∧
        ∀ i, ∃ a : A, (l : ℤ_[l]) ^ r • a = 0 ∧ ∀ g, z.1 (φ i g) = σ (φ i g) a - a}
      zero_mem' := ⟨0, rfl, fun g => by simp, fun i => ⟨0, by simp, fun g => by simp⟩⟩
      add_mem' := by
        rintro x y ⟨z, hz, hz1, hz2⟩ ⟨w, hw, hw1, hw2⟩
        refine ⟨z + w, by rw [Submodule.Quotient.mk_add, hz, hw]; rfl, fun g => ?_, fun i => ?_⟩
        · change _ • (z.1 g + w.1 g) = 0
          rw [smul_add, hz1, hw1, add_zero]
        · obtain ⟨a, ha, ha'⟩ := hz2 i
          obtain ⟨b, hb, hb'⟩ := hw2 i
          refine ⟨a + b, by rw [smul_add, ha, hb, add_zero], fun g => ?_⟩
          change z.1 _ + w.1 _ = _
          rw [ha', hb', map_add]; abel
      smul_mem' := by
        rintro c x ⟨z, hz, hz1, hz2⟩
        refine ⟨c • z, by rw [Submodule.Quotient.mk_smul, hz]; rfl, fun g => ?_, fun i => ?_⟩
        · change _ • (c • z.1 g) = 0
          rw [smul_comm, hz1, smul_zero]
        · obtain ⟨a, ha, ha'⟩ := hz2 i
          refine ⟨c • a, by rw [smul_comm, ha, smul_zero], fun g => ?_⟩
          change c • z.1 _ = _
          rw [ha', map_smul, smul_sub] }
  have hP : ∀ r x, x ∈ P r ↔ ∃ z : Z1 σ, (Submodule.Quotient.mk z : H1 σ) = x.1 ∧
        (∀ g, (l : ℤ_[l]) ^ r • z.1 g = 0) ∧
        ∀ i, ∃ a : A, (l : ℤ_[l]) ^ r • a = 0 ∧ ∀ g, z.1 (φ i g) = σ (φ i g) a - a :=
    fun r x => Iff.rfl
  refine ⟨P, ?_, ?_, ?_⟩
  · intro r s hrs x hx
    obtain ⟨z, hz, hz1, hz2⟩ := (hP r x).1 hx
    refine (hP s x).2 ⟨z, hz, fun g => hup r s _ hrs (hz1 g), fun i => ?_⟩
    obtain ⟨a, ha, ha'⟩ := hz2 i
    exact ⟨a, hup r s _ hrs ha, ha'⟩
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    choose b hb using (mk_mem_sha1_iff_locally_coboundary φ hφ σ z).1 hy
    choose e he using htor
    have hfin : (Set.range z.1 ∪ Set.range b).Finite :=
      (isCompact_range z.2.1).finite_of_discrete.union (Set.finite_range b)
    obtain ⟨r, hr⟩ := (hfin.image e).bddAbove
    refine ⟨r, (hP r _).2 ⟨z, rfl, fun g => hup _ _ _ (hr ⟨_, Or.inl ⟨g, rfl⟩, rfl⟩) (he _),
      fun i => ⟨b i, hup _ _ _ (hr ⟨_, Or.inr ⟨i, rfl⟩, rfl⟩) (he _), hb i⟩⟩⟩
  · intro r R _ N _ _ _ _ τ ι hinj hrange heq hloc
    let ιZ : Z1 τ →+ Z1 σ :=
      { toFun := fun z => ⟨fun g => ι (z.1 g), continuous_of_discreteTopology.comp z.2.1,
          fun g h => by beta_reduce; rw [z.2.2, map_add, heq]⟩
        map_zero' := Subtype.ext (funext fun g => map_zero ι)
        map_add' := fun z w => Subtype.ext (funext fun g => map_add ι _ _) }
    have hιZ : ∀ z g, (ιZ z).1 g = ι (z.1 g) := fun _ _ => rfl
    let F : H1 τ →+ H1 σ := QuotientAddGroup.map
      ((B1 τ).comap (Z1 τ).subtype).toAddSubgroup ((B1 σ).comap (Z1 σ).subtype).toAddSubgroup ιZ
      (by
        intro z hz
        obtain ⟨m, hm⟩ := (mem_coboundaries1 τ _).1 hz
        refine (mem_coboundaries1 σ _).2 ⟨ι m, fun g => ?_⟩
        change ι (z.1 g) = _
        rw [← heq, ← map_sub]
        exact congrArg ι (hm g))
    have hF : ∀ z, F (Submodule.Quotient.mk z) = Submodule.Quotient.mk (ιZ z) := fun _ => rfl
    have hkill : ∀ n, (l : ℤ_[l]) ^ r • ι n = 0 := fun n => (hrange _).2 ⟨n, rfl⟩
    have hmem : ∀ x : H1 τ, x ∈ Sha1 τ φ hφ → ∃ h : F x ∈ Sha1 σ φ hφ, ⟨F x, h⟩ ∈ P r := by
      intro x hx
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      have h1 := (mk_mem_sha1_iff_locally_coboundary φ hφ τ z).1 hx
      have h2 : ∀ i, ∃ a : A, (l : ℤ_[l]) ^ r • a = 0 ∧
          ∀ g, (ιZ z).1 (φ i g) = σ (φ i g) a - a := by
        intro i
        obtain ⟨b, hb⟩ := h1 i
        exact ⟨ι b, hkill b, fun g => by rw [hιZ, hb, map_sub, heq]⟩
      refine ⟨?_, (hP r _).2 ⟨ιZ z, rfl, fun g => hkill _, h2⟩⟩
      rw [hF, mk_mem_sha1_iff_locally_coboundary]
      intro i
      obtain ⟨a, -, ha⟩ := h2 i
      exact ⟨a, ha⟩
    have hker : ∀ x : H1 τ, x ∈ Sha1 τ φ hφ → F x = 0 → x = 0 := by
      intro x hx h0
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      have h1 := (mk_mem_sha1_iff_locally_coboundary φ hφ τ z).1 hx
      rw [hF, Submodule.Quotient.mk_eq_zero] at h0
      obtain ⟨a, ha⟩ := (mem_coboundaries1 σ _).1 h0
      have ha' : ∀ g, ι (z.1 g) = σ g a - a := ha
      obtain ⟨b, hb, hb'⟩ := hloc a (fun i => by
        obtain ⟨b, hb⟩ := h1 i
        exact ⟨ι b, hkill b, fun g => by rw [← ha', hb, map_sub, heq]⟩)
      obtain ⟨n, rfl⟩ := (hrange b).1 hb
      rw [Submodule.Quotient.mk_eq_zero]
      refine (mem_coboundaries1 τ _).2 ⟨n, fun g => hinj ?_⟩
      change ι (z.1 g) = _
      rw [ha', hb', map_sub, heq]
    let f : Sha1 τ φ hφ → P r := fun x => ⟨⟨F x.1, (hmem x.1 x.2).1⟩, (hmem x.1 x.2).2⟩
    refine (Nat.card_eq_of_bijective f ⟨?_, ?_⟩).symm
    · intro x y hxy
      have h : F x.1 = F y.1 := congrArg (fun t : P r => t.1.1) hxy
      apply Subtype.ext
      rw [← sub_eq_zero]
      exact hker _ (sub_mem x.2 y.2) (by rw [map_sub, h, sub_self])
    · rintro ⟨x, hx⟩
      obtain ⟨z, hz, hz1, hz2⟩ := (hP r x).1 hx
      have hlift : ∀ g, ∃ n, ι n = z.1 g := fun g => (hrange _).1 (hz1 g)
      choose w hw using hlift
      have hwc : Continuous w := by
        have : w = Function.invFun ι ∘ z.1 := by
          funext g
          rw [Function.comp_apply, ← hw, Function.leftInverse_invFun hinj]
        rw [this]
        exact continuous_of_discreteTopology.comp z.2.1
      let z' : Z1 τ := ⟨w, hwc, fun g h => hinj (by rw [map_add, heq, hw, hw, hw, z.2.2])⟩
      have hz' : ιZ z' = z := Subtype.ext (funext hw)
      refine ⟨⟨Submodule.Quotient.mk z', ?_⟩, ?_⟩
      · rw [mk_mem_sha1_iff_locally_coboundary]
        intro i
        obtain ⟨a, ha, ha'⟩ := hz2 i
        obtain ⟨n, rfl⟩ := (hrange a).1 ha
        refine ⟨n, fun g => hinj ?_⟩
        change ι (w _) = _
        rw [hw, ha', map_sub, heq]
      · apply Subtype.ext
        apply Subtype.ext
        change F (Submodule.Quotient.mk z') = x.1
        rw [hF, hz', hz]

end GlobalTheory
