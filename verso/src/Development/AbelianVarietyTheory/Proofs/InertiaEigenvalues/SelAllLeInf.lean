import Mathlib
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology Pointwise

namespace GlobalTheory.SelInfl

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {S : Set (HeightOneSpectrum (𝓞 F))} {R : Type} [CommRing R] {M : Type}
  [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M] [T2Space M] (rhoS : Representation R (GS Ω S) M) (A : Places F Ω)

/- English proof (translation)
Take `⟨hfc, hfco⟩` from `(ReciprocityTheory.Gal.mem_Z1_iff_cocycle _ f).1 hf`. Establish `ht : ∀ g ∈ NS Ω S, toGS Ω S g = 1` using `fun g hg => (QuotientGroup.eq_one_iff g).2 hg`. Establish `hρ : ∀ g ∈ NS Ω S, ∀ x : M, (rhoS.comp (toGS Ω S)) g x = x`. Introduce `g hg x`. Rewrite using `[MonoidHom.comp_apply, ht g hg, map_one, Module.End.one_apply]`.

Establish `h1 : f 1 = 0`. Use `hfco 1 1` as an intermediate fact. Rewrite `this` using `[mul_one, map_one, Module.End.one_apply]`. Simplify using `using this`. Establish `hinv : ∀ a ∈ NS Ω S, f a = 0 → f a⁻¹ = 0`.

Introduce `a ha h0`. Use `hfco a a⁻¹` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel, h1, h0, zero_add, hρ a ha]`. Conclude with `this.symm`. Set `H : Subgroup (G F Ω)` to `{ carrier := {g | g ∈ NS Ω S ∧ f g = 0} one_mem' := ⟨(NS Ω S).one_mem, h1⟩ mul_mem' := fun {a b} ha hb => ⟨(NS Ω S).mul_mem ha.1 hb.1, by rw [hfco, ha.2, hb.2, map_zero, add_zero]⟩ inv_mem' := fun {a} ha => ⟨(NS Ω S).inv_mem ha.1, hinv a ha.1 ha.2⟩ }`.

Establish `hconj : ∀ n ∈ H, ∀ g : G F Ω, g * n * g⁻¹ ∈ H`. Introduce `n hn g`. Use `⟨(normal_NS S).conj_mem n hn.1 g, ?_⟩` and prove the remaining obligations. Establish `e1` using `hfco (g * n) g⁻¹`. Establish `e2` using `hfco g n`.

Establish `e3` using `hfco g g⁻¹`. Rewrite `e1` using `[map_mul, Module.End.mul_apply, hρ n hn.1, e2, hn.2, map_zero, add_zero]`. Rewrite `e3` using `[mul_inv_cancel, h1]`. Rewrite using `[e1, ← e3]`. Establish `hHn : H.Normal` using `⟨hconj⟩`.

Establish `hclosed : IsClosed (H : Set (G F Ω))` using `(isClosed_NS Ω S).inter (isClosed_singleton.preimage hfc)`. Establish `hsub : (⋃ v ∈ Sᶜ, ⋃ A' ∈ {A' : ValuationSubring Ω | IsPlaceOver A' v}, Inertia (F` using `F) A') ⊆ H := by`. Introduce `σ hσ`. Establish `hσN : σ ∈ NS Ω S` using `Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hσ)`. Simplify using `only [Set.mem_iUnion, Set.mem_ofPred_eq] at hσ`.

Take `⟨v, hv, A', hA', hσA'⟩` from `hσ`. Take `⟨γ, hγ⟩` from `exists_smul_eq_of_isPlaceOver (A.2 v) hA'`. Establish `hσI : σ ∈ Ine (F` using `F) (γ • A.1 v) := by`. Rewrite using `[hγ]`. Conclude with `mem_Ine.2 hσA'`.

Establish `hτ` using `GlobalTheory.Cut.ShaBound.conj_mem_Ine' hσI`. Establish `hτN : γ⁻¹ * σ * γ ∈ NS Ω S`. Use `(normal_NS S).conj_mem σ hσN γ⁻¹` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Then use the resulting hypothesis. Take `⟨m, hm⟩` from `hv0 v hv`.

Establish `hfτ : f (γ⁻¹ * σ * γ) = 0`. Rewrite using `[hm _ hτ, ht _ hτN, map_one, Module.End.one_apply, sub_self]`. Use `hconj _ ⟨hτN, hfτ⟩ γ` as an intermediate fact. Establish `e : γ * (γ⁻¹ * σ * γ) * γ⁻¹ = σ` using `by group`. Rewrite `this` using `[e]`.

Conclude with `this`. Establish `hle : NS Ω S ≤ H` using `Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal hsub) hclosed`. Conclude with `(hle hn).2`.
-/
theorem vanish {f : G F Ω → M} (hf : f ∈ Z1 (rhoS.comp (toGS Ω S) : Representation R (G F Ω) M))
    (hv0 : ∀ v ∉ S, ∃ m, ∀ g ∈ Ine (F := F) (A.1 v), f g = rhoS (toGS Ω S g) m - m) (n : G F Ω)
    (hn : n ∈ NS Ω S) : f n = 0 := by
  obtain ⟨hfc, hfco⟩ := (ReciprocityTheory.Gal.mem_Z1_iff_cocycle _ f).1 hf
  have ht : ∀ g ∈ NS Ω S, toGS Ω S g = 1 := fun g hg => (QuotientGroup.eq_one_iff g).2 hg
  have hρ : ∀ g ∈ NS Ω S, ∀ x : M, (rhoS.comp (toGS Ω S)) g x = x := by
    intro g hg x
    rw [MonoidHom.comp_apply, ht g hg, map_one, Module.End.one_apply]
  have h1 : f 1 = 0 := by
    have := hfco 1 1
    rw [mul_one, map_one, Module.End.one_apply] at this
    simpa using this
  have hinv : ∀ a ∈ NS Ω S, f a = 0 → f a⁻¹ = 0 := by
    intro a ha h0
    have := hfco a a⁻¹
    rw [mul_inv_cancel, h1, h0, zero_add, hρ a ha] at this
    exact this.symm
  let H : Subgroup (G F Ω) :=
    { carrier := {g | g ∈ NS Ω S ∧ f g = 0}
      one_mem' := ⟨(NS Ω S).one_mem, h1⟩
      mul_mem' := fun {a b} ha hb =>
        ⟨(NS Ω S).mul_mem ha.1 hb.1, by rw [hfco, ha.2, hb.2, map_zero, add_zero]⟩
      inv_mem' := fun {a} ha => ⟨(NS Ω S).inv_mem ha.1, hinv a ha.1 ha.2⟩ }
  have hconj : ∀ n ∈ H, ∀ g : G F Ω, g * n * g⁻¹ ∈ H := by
    intro n hn g
    refine ⟨(normal_NS S).conj_mem n hn.1 g, ?_⟩
    have e1 := hfco (g * n) g⁻¹
    have e2 := hfco g n
    have e3 := hfco g g⁻¹
    rw [map_mul, Module.End.mul_apply, hρ n hn.1, e2, hn.2, map_zero, add_zero] at e1
    rw [mul_inv_cancel, h1] at e3
    rw [e1, ← e3]
  have hHn : H.Normal := ⟨hconj⟩
  have hclosed : IsClosed (H : Set (G F Ω)) :=
    (isClosed_NS Ω S).inter (isClosed_singleton.preimage hfc)
  have hsub : (⋃ v ∈ Sᶜ, ⋃ A' ∈ {A' : ValuationSubring Ω | IsPlaceOver A' v}, Inertia (F := F) A') ⊆ H := by
    intro σ hσ
    have hσN : σ ∈ NS Ω S :=
      Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hσ)
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hσ
    obtain ⟨v, hv, A', hA', hσA'⟩ := hσ
    obtain ⟨γ, hγ⟩ := exists_smul_eq_of_isPlaceOver (A.2 v) hA'
    have hσI : σ ∈ Ine (F := F) (γ • A.1 v) := by
      rw [hγ]
      exact mem_Ine.2 hσA'
    have hτ := GlobalTheory.Cut.ShaBound.conj_mem_Ine' hσI
    have hτN : γ⁻¹ * σ * γ ∈ NS Ω S := by
      have := (normal_NS S).conj_mem σ hσN γ⁻¹
      rwa [inv_inv] at this
    obtain ⟨m, hm⟩ := hv0 v hv
    have hfτ : f (γ⁻¹ * σ * γ) = 0 := by
      rw [hm _ hτ, ht _ hτN, map_one, Module.End.one_apply, sub_self]
    have := hconj _ ⟨hτN, hfτ⟩ γ
    have e : γ * (γ⁻¹ * σ * γ) * γ⁻¹ = σ := by group
    rw [e] at this
    exact this
  have hle : NS Ω S ≤ H :=
    Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal hsub) hclosed
  exact (hle hn).2

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ S R _ M _ _ _ _ _ _ rhoS _ A L hL x hx`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Establish `hloc` using `(ReciprocityTheory.Gal.mem_Sel _ _ _ _ _).1 hx`. Establish `hv0 : ∀ v ∉ S, ∃ m, ∀ g ∈ Ine (F` using `F) (A.1 v), z.1 g = rhoS (toGS Ω S g) m - m := by`. Introduce `v hv`.

Establish `h1` using `hL v hv (hloc v)`. Establish `h2 : (Submodule.Quotient.mk (restrictCocycles1 _ ((Ine (F` using `F) (A.1 v)).subgroupOf (Dec (F := F) (A.1 v))).subtype continuous_subtype_val (restrictCocycles1 _ (Dec (F := F) (A.1 v)).subtype continuous_subtype_val z)) : H1 _) = 0 := h1`. Establish `h3` using `(Submodule.Quotient.mk_eq_zero _).1 h2`. Rewrite `h3` using `[Submodule.mem_comap]`. Take `⟨m, hm⟩` from `(ReciprocityTheory.Gal.mem_coboundaries1 _ _).1 h3`.

Use `⟨m, fun g hg => ?_⟩` and prove the remaining obligations. Establish `gD : g ∈ Dec (F` using `F) (A.1 v) := Ine_le_Dec _ hg`. Establish `gJ : (⟨g, gD⟩ : Dec (F` using `F) (A.1 v)) ∈ (Ine (F := F) (A.1 v)).subgroupOf (Dec (F := F) (A.1 v)) := by`. Rewrite using `[Subgroup.mem_subgroupOf]`. Conclude with `hg`.

Conclude with `hm ⟨⟨g, gD⟩, gJ⟩`. Establish `hvan : ∀ n ∈ NS Ω S, z.1 n = 0` using `fun n hn => vanish rhoS A z.2 hv0 n hn`. Take `⟨hzc, hzco⟩` from `(ReciprocityTheory.Gal.mem_Z1_iff_cocycle _ _).1 z.2`. Establish `hwd : ∀ a b : G F Ω, a⁻¹ * b ∈ NS Ω S → z.1 a = z.1 b`. Introduce `a b hab`.

Use `hzco a (a⁻¹ * b)` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_left, hvan _ hab, map_zero, add_zero]`. Conclude with `this.symm`. Set `z' : GS Ω S → M` to `fun q => Quotient.liftOn' q z.1 (fun a b hab => hwd a b (QuotientGroup.leftRel_apply.1 hab))`. Establish `hz'c : Continuous z'` using `Continuous.quotient_liftOn' hzc _`.

Establish `hz'co : ∀ p q : GS Ω S, z' (p * q) = z' p + rhoS p (z' q)`. Introduce `p q`. Take `⟨a, rfl⟩` from `QuotientGroup.mk_surjective p`. Take `⟨b, rfl⟩` from `QuotientGroup.mk_surjective q`. Conclude with `hzco a b`.

Set `w : Z1 rhoS` to `⟨z', (ReciprocityTheory.Gal.mem_Z1_iff_cocycle _ _).2 ⟨hz'c, hz'co⟩⟩`. Conclude with `⟨Submodule.Quotient.mk w, rfl⟩`.
-/
theorem selAllLeInf : Formalism.GaloisCohomology.SelAllLeInf := by
  intro F Ω _ _ _ _ _ S R _ M _ _ _ _ _ _ rhoS _ A L hL x hx
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hloc := (ReciprocityTheory.Gal.mem_Sel _ _ _ _ _).1 hx
  have hv0 : ∀ v ∉ S, ∃ m, ∀ g ∈ Ine (F := F) (A.1 v), z.1 g = rhoS (toGS Ω S g) m - m := by
    intro v hv
    have h1 := hL v hv (hloc v)
    have h2 : (Submodule.Quotient.mk (restrictCocycles1 _ ((Ine (F := F) (A.1 v)).subgroupOf (Dec (F := F) (A.1 v))).subtype
        continuous_subtype_val (restrictCocycles1 _ (Dec (F := F) (A.1 v)).subtype continuous_subtype_val z)) :
        H1 _) = 0 := h1
    have h3 := (Submodule.Quotient.mk_eq_zero _).1 h2
    rw [Submodule.mem_comap] at h3
    obtain ⟨m, hm⟩ := (ReciprocityTheory.Gal.mem_coboundaries1 _ _).1 h3
    refine ⟨m, fun g hg => ?_⟩
    have gD : g ∈ Dec (F := F) (A.1 v) := Ine_le_Dec _ hg
    have gJ : (⟨g, gD⟩ : Dec (F := F) (A.1 v)) ∈ (Ine (F := F) (A.1 v)).subgroupOf (Dec (F := F) (A.1 v)) := by
      rw [Subgroup.mem_subgroupOf]
      exact hg
    exact hm ⟨⟨g, gD⟩, gJ⟩
  have hvan : ∀ n ∈ NS Ω S, z.1 n = 0 := fun n hn => vanish rhoS A z.2 hv0 n hn
  obtain ⟨hzc, hzco⟩ := (ReciprocityTheory.Gal.mem_Z1_iff_cocycle _ _).1 z.2
  have hwd : ∀ a b : G F Ω, a⁻¹ * b ∈ NS Ω S → z.1 a = z.1 b := by
    intro a b hab
    have := hzco a (a⁻¹ * b)
    rw [mul_inv_cancel_left, hvan _ hab, map_zero, add_zero] at this
    exact this.symm
  let z' : GS Ω S → M := fun q =>
    Quotient.liftOn' q z.1 (fun a b hab => hwd a b (QuotientGroup.leftRel_apply.1 hab))
  have hz'c : Continuous z' := Continuous.quotient_liftOn' hzc _
  have hz'co : ∀ p q : GS Ω S, z' (p * q) = z' p + rhoS p (z' q) := by
    intro p q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective p
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
    exact hzco a b
  let w : Z1 rhoS := ⟨z', (ReciprocityTheory.Gal.mem_Z1_iff_cocycle _ _).2 ⟨hz'c, hz'co⟩⟩
  exact ⟨Submodule.Quotient.mk w, rfl⟩

end GlobalTheory.SelInfl

end
