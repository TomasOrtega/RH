import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.Descend
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.SelBig
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.SelMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.ZunrFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.CocConj

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Introduce `hP F Ω _ _ _ _ _ l _ M _ _ _ _ _ hl ρ S₀ Q hρ hS₀ hu hQ hT m0 hm0`. Establish `hfin : Finite (Zunr ρ S₀)` using `UpperTheory.V.Ws.Gys.zunrFin hP.gf F Ω l M ρ S₀ hS₀ hρ hu`. Take `⟨C, hC⟩ : ∃ C, C = Nat.card (TDual (ZMod (l ^ 1)) M) * Nat.card M ^ (Module.finrank ℚ F + S₀.card)` from `⟨_, rfl⟩`. Take `⟨N, hN⟩ : ∃ N, N = Nat.card (Zunr ρ S₀)` from `⟨_, rfl⟩`. Take `⟨S₁, hS₁, hcard⟩` from `(hQ.diff S₀.finite_toSet).exists_subset_card_eq (N * C)`.

Establish `hdisj : Disjoint S₀ S₁` using `Finset.disjoint_left.2 fun v h0 h1 => (hS₁ (Finset.mem_coe.2 h1)).2 (Finset.mem_coe.2 h0)`. Take `⟨S, hS⟩ : ∃ S, S = S₀ ∪ S₁` from `⟨_, rfl⟩`. Establish `hsub : S₀ ⊆ S` using `hS ▸ Finset.subset_union_left`. Establish `hSQ : ∀ v ∈ S, v ∈ S₀ ∨ v ∈ Q` using `fun v hv => by`. Rewrite `hv` using `[hS, Finset.mem_union]`.

Conclude with `hv.imp_right fun h => (hS₁ (Finset.mem_coe.2 h)).1`. Establish `hSc : S.card - S₀.card = N * C`. Rewrite using `[hS, Finset.card_union_of_disjoint hdisj, hcard]`. Use linear arithmetic over natural numbers and integers. Establish `huS : UnrOut ρ S` using `fun v hv => hu v fun h => hv (hsub h)`.

Take `⟨ρS, rfl, hρS⟩` from `UpperTheory.V.Ws.Gys.descend F Ω _ M ρ S hρ huS`. Establish `hTS : ∀ v ∈ S, v ∉ S₀ → TrivAt l (ρS.comp (toGS Ω _)) v` using `fun v hv h0 => hT v ((hSQ v hv).resolve_left h0)`. Set `Av : S → ValuationSubring Ω` to `fun v => placeOf Ω v.1`. Establish `hAv : ∀ v, IsPlaceOver (Av v) v.1` using `fun v => isPlaceOver_placeOf Ω v.1`. Establish `hbig` using `UpperTheory.V.Ws.Gys.selBig hP F Ω l M hl S₀ S ρS hsub hS₀ hρS hTS Av hAv m0 hm0`.

Establish `hmem` using `UpperTheory.V.Ws.Gys.selMem F Ω l _ M S₀ S ρS hsub hTS Av hAv m0`. Rewrite `hbig` using `[← hC, hSc]`. Use `⟨S, hSQ, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hno`. Establish `hout : ∀ x : gysSel S₀ S ρS Av m0, Submodule.Quotient.mk (Quotient.out x.1) ∈ gysSel S₀ S ρS Av m0` using `fun x => by`.

Establish `: (Submodule.Quotient.mk (Quotient.out x.1) : H1 ρS) = x.1` using `Quotient.out_eq x.1`. Rewrite using `[this]`. Conclude with `x.2`. Establish `hz : ∀ x : gysSel S₀ S ρS Av m0, (fun g => (Quotient.out x.1).1 (toGS Ω _ g)) ∈ Zunr (ρS.comp (toGS Ω _)) S₀` using `fun x => by`. Take `⟨h1, h2, h3⟩` from `hmem _ (hout x)`.

Use `⟨h1.1, fun v hv A hA => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hvS : v ∈ S`. Use `(UpperTheory.V.Ws.Gys.cocConj F Ω _ M _ _ h1.1 v (Av ⟨v, hvS⟩) A (hAv ⟨v, hvS⟩) hA).2 fun g hg => ?_` and prove the remaining obligations. Establish `hg1` using `(hTS v hvS hv _ (hAv ⟨v, hvS⟩) g (Ine_le_Dec _ hg)).1`. Use `⟨hg1, ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hne`. Conclude with `hno ⟨_, h1, h2, g, hg1, hne, h3 ⟨v, hvS⟩ hv g hg⟩`. Conclude with `h1.2 v hvS A hA`. Establish `hinj : Function.Injective fun x : gysSel S₀ S ρS Av m0 => (⟨_, hz x⟩ : Zunr (ρS.comp (toGS Ω _)) S₀)`. Introduce `x y hxy`.

Establish `h1 : Quotient.out x.1 = Quotient.out y.1`. Use `Subtype.ext (funext fun g => ?_)` and prove the remaining obligations. Take `⟨σ, rfl⟩ : ∃ σ, toGS Ω _ σ = g` from `QuotientGroup.mk_surjective g`. Conclude with `congrFun (congrArg Subtype.val hxy) σ`. Conclude with `Subtype.ext (Quotient.out_injective h1)`.

Establish `hle` using `Nat.card_le_card_of_injective _ hinj`. Rewrite `hle` using `[← hN]`. Establish `h2 : N * C < 2 ^ (N * C)` using `Nat.lt_two_pow_self`. Conclude with `absurd (hbig.trans (Nat.mul_le_mul_right C hle)) (not_le.2 h2)`.
-/
theorem UpperTheory.V.Ws.Gys.gysCore :
    CohomologyHyp → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M], l ≠ 2 → ∀ (ρ : Representation (ZMod (l ^ 1)) (G F Ω) M) (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (Q : Set (HeightOneSpectrum (𝓞 F))), ContAction ρ → ContainsAbove S₀ l → UnrOut ρ S₀ →
      Q.Infinite → (∀ v ∈ Q, TrivAt l ρ v) → ∀ m0 : M, m0 ≠ 0 →
        ∃ S : Finset (HeightOneSpectrum (𝓞 F)), (∀ v ∈ S, v ∈ S₀ ∨ v ∈ Q) ∧ ∃ c ∈ Zunr ρ S, (∀ v ∈ S₀, ∀ A, IsPlaceOver A v → ∃ m, ∀ g ∈ Dec (F := F) A, c g = ρ g m - m) ∧
          ∃ g, ρ g = 1 ∧ c g ≠ 0 ∧ c g ∈ Submodule.span (ZMod (l ^ 1)) {m0} := by
  classical
  intro hP F Ω _ _ _ _ _ l _ M _ _ _ _ _ hl ρ S₀ Q hρ hS₀ hu hQ hT m0 hm0
  have hfin : Finite (Zunr ρ S₀) := UpperTheory.V.Ws.Gys.zunrFin hP.gf F Ω l M ρ S₀ hS₀ hρ hu
  obtain ⟨C, hC⟩ : ∃ C, C = Nat.card (TDual (ZMod (l ^ 1)) M) * Nat.card M ^ (Module.finrank ℚ F + S₀.card) := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, N = Nat.card (Zunr ρ S₀) := ⟨_, rfl⟩
  obtain ⟨S₁, hS₁, hcard⟩ := (hQ.diff S₀.finite_toSet).exists_subset_card_eq (N * C)
  have hdisj : Disjoint S₀ S₁ := Finset.disjoint_left.2 fun v h0 h1 => (hS₁ (Finset.mem_coe.2 h1)).2 (Finset.mem_coe.2 h0)
  obtain ⟨S, hS⟩ : ∃ S, S = S₀ ∪ S₁ := ⟨_, rfl⟩
  have hsub : S₀ ⊆ S := hS ▸ Finset.subset_union_left
  have hSQ : ∀ v ∈ S, v ∈ S₀ ∨ v ∈ Q := fun v hv => by
    rw [hS, Finset.mem_union] at hv
    exact hv.imp_right fun h => (hS₁ (Finset.mem_coe.2 h)).1
  have hSc : S.card - S₀.card = N * C := by
    rw [hS, Finset.card_union_of_disjoint hdisj, hcard]; omega
  have huS : UnrOut ρ S := fun v hv => hu v fun h => hv (hsub h)
  obtain ⟨ρS, rfl, hρS⟩ := UpperTheory.V.Ws.Gys.descend F Ω _ M ρ S hρ huS
  have hTS : ∀ v ∈ S, v ∉ S₀ → TrivAt l (ρS.comp (toGS Ω _)) v := fun v hv h0 => hT v ((hSQ v hv).resolve_left h0)
  let Av : S → ValuationSubring Ω := fun v => placeOf Ω v.1
  have hAv : ∀ v, IsPlaceOver (Av v) v.1 := fun v => isPlaceOver_placeOf Ω v.1
  have hbig := UpperTheory.V.Ws.Gys.selBig hP F Ω l M hl S₀ S ρS hsub hS₀ hρS hTS Av hAv m0 hm0
  have hmem := UpperTheory.V.Ws.Gys.selMem F Ω l _ M S₀ S ρS hsub hTS Av hAv m0
  rw [← hC, hSc] at hbig
  refine ⟨S, hSQ, ?_⟩
  by_contra hno
  have hout : ∀ x : gysSel S₀ S ρS Av m0, Submodule.Quotient.mk (Quotient.out x.1) ∈ gysSel S₀ S ρS Av m0 := fun x => by
    have : (Submodule.Quotient.mk (Quotient.out x.1) : H1 ρS) = x.1 := Quotient.out_eq x.1
    rw [this]; exact x.2
  have hz : ∀ x : gysSel S₀ S ρS Av m0, (fun g => (Quotient.out x.1).1 (toGS Ω _ g)) ∈ Zunr (ρS.comp (toGS Ω _)) S₀ := fun x => by
    obtain ⟨h1, h2, h3⟩ := hmem _ (hout x)
    refine ⟨h1.1, fun v hv A hA => ?_⟩
    by_cases hvS : v ∈ S
    · refine (UpperTheory.V.Ws.Gys.cocConj F Ω _ M _ _ h1.1 v (Av ⟨v, hvS⟩) A (hAv ⟨v, hvS⟩) hA).2 fun g hg => ?_
      have hg1 := (hTS v hvS hv _ (hAv ⟨v, hvS⟩) g (Ine_le_Dec _ hg)).1
      refine ⟨hg1, ?_⟩
      by_contra hne
      exact hno ⟨_, h1, h2, g, hg1, hne, h3 ⟨v, hvS⟩ hv g hg⟩
    · exact h1.2 v hvS A hA
  have hinj : Function.Injective fun x : gysSel S₀ S ρS Av m0 => (⟨_, hz x⟩ : Zunr (ρS.comp (toGS Ω _)) S₀) := by
    intro x y hxy
    have h1 : Quotient.out x.1 = Quotient.out y.1 := by
      refine Subtype.ext (funext fun g => ?_)
      obtain ⟨σ, rfl⟩ : ∃ σ, toGS Ω _ σ = g := QuotientGroup.mk_surjective g
      exact congrFun (congrArg Subtype.val hxy) σ
    exact Subtype.ext (Quotient.out_injective h1)
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [← hN] at hle
  have h2 : N * C < 2 ^ (N * C) := Nat.lt_two_pow_self
  exact absurd (hbig.trans (Nat.mul_le_mul_right C hle)) (not_le.2 h2)
