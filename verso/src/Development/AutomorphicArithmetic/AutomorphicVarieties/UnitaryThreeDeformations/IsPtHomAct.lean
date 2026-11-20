import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Adjoin
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

/- English proof (translation)
Establish `hA : W.A = Sring O u`. Use extensionality with `x`. Use `show x ∈ ⨆ j, W.part j ↔ x ∈ ⨆ j, wpart O u j`. Simplify using `only [hW]`. Use `⟨(act W.gr (zpowersHom Kˣ t) (ξ.comp (Subalgebra.inclusion hA.le))).comp (Subalgebra.inclusion hA.ge), fun j x hx => ?_⟩` and prove the remaining obligations.

Establish `hx' : Subalgebra.inclusion hA.ge ⟨x, mem_Sring u hx⟩ ∈ W.gr j` using `by show x ∈ W.part j`. Rewrite using `[hW]` and apply the resulting hypothesis. Rewrite using `[AlgHom.comp_apply, act_of_mem W.gr _ _ hx']`. Both sides reduce to the same expression.
-/
private theorem exists_act {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ]
    {R : Type} [CommRing R] [Algebra O R] (u : Γ →* GG 3 R) (W : WPres O ℤ R)
    (hW : ∀ j, W.part j = wpart O u j) {K : Type} [CommRing K] [Algebra O K] (ξ : Sring O u →ₐ[O] K) (t : Kˣ) :
    ∃ ξt : Sring O u →ₐ[O] K, ∀ (j : ℤ) x (hx : x ∈ wpart O u j),
      ξt ⟨x, mem_Sring u hx⟩ = ((t ^ j : Kˣ) : K) * ξ ⟨x, mem_Sring u hx⟩ := by
  have hA : W.A = Sring O u := by
    ext x
    show x ∈ ⨆ j, W.part j ↔ x ∈ ⨆ j, wpart O u j
    simp only [hW]
  refine ⟨(act W.gr (zpowersHom Kˣ t) (ξ.comp (Subalgebra.inclusion hA.le))).comp
    (Subalgebra.inclusion hA.ge), fun j x hx => ?_⟩
  have hx' : Subalgebra.inclusion hA.ge ⟨x, mem_Sring u hx⟩ ∈ W.gr j := by
    show x ∈ W.part j
    rwa [hW]
  rw [AlgHom.comp_apply, act_of_mem W.gr _ _ hx']
  rfl

/- English proof (translation)
Introduce `l _ O _ _ _ _ _ _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF g₁ hg R _ _ _ u hu hfin ξ r hr ξ' t`. Take `⟨hm, hri, -⟩` from `conjBy_tor r t`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨W, hW, -⟩` from `exists_adapted F hF g₁ hg u hu`.

Take `⟨ξt, hξt⟩` from `exists_act u W hW.part ξ t`. Establish `e : ξ' = ξt`. Use `AlgHom.ext_of_eq_adjoin (sring_eq_adjoin F hF g₁ hg u hu hfin).1 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, a, b, -, rfl⟩`. Use `Eq.trans ?_ (hξt _ _ (entry_mem u g a b)).symm` and prove the remaining obligations.

Establish `h1` using `congrFun (congrFun (h g).2 a) b`. Rewrite `h1` using `[hm, (hr g).2]`. Conclude with `h1.symm`. Rewrite using `[e]`. Conclude with `hξt`.

Introduce `h g`. Use `⟨(hri g).trans (hr g).1, ?_⟩` and prove the remaining obligations. Use extensionality with `a b`. Rewrite using `[hm, (hr g).2]`. Conclude with `(h _ _ (entry_mem u g a b)).symm`.
-/
theorem UpperTheory.V.UnitaryThreeInertia.isPtHom_act :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] [FaithfulSMul O (PadicAlgCl l)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    ∀ (g₁ : Γ), F.Marked g₁ → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (u : Γ →* GG 3 R), F.IsUniv g₁ u →
    Module.Finite O (wpart O u 0) → ∀ (ξ : Sring O u →ₐ[O] (PadicAlgCl l)) (r : Γ →* GG 3 (PadicAlgCl l)), IsPtHom u ξ r → ∀ (ξ' : Sring O u →ₐ[O] (PadicAlgCl l)) (t : (PadicAlgCl l)ˣ), IsPtHom u ξ' (conjBy (tor (PadicAlgCl l) t) r) ↔
      ∀ (j : ℤ) x (hx : x ∈ wpart O u j), ξ' ⟨x, mem_Sring u hx⟩ = ((t ^ j : (PadicAlgCl l)ˣ) : (PadicAlgCl l)) * ξ ⟨x, mem_Sring u hx⟩ := by
  intro l _ O _ _ _ _ _ _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF g₁ hg R _ _ _ u hu hfin ξ r hr ξ' t
  obtain ⟨hm, hri, -⟩ := conjBy_tor r t
  constructor
  · intro h
    obtain ⟨W, hW, -⟩ := exists_adapted F hF g₁ hg u hu
    obtain ⟨ξt, hξt⟩ := exists_act u W hW.part ξ t
    have e : ξ' = ξt := by
      refine AlgHom.ext_of_eq_adjoin (sring_eq_adjoin F hF g₁ hg u hu hfin).1 ?_
      rintro _ ⟨g, a, b, -, rfl⟩
      refine Eq.trans ?_ (hξt _ _ (entry_mem u g a b)).symm
      have h1 := congrFun (congrFun (h g).2 a) b
      rw [hm, (hr g).2] at h1
      exact h1.symm
    rw [e]
    exact hξt
  · intro h g
    refine ⟨(hri g).trans (hr g).1, ?_⟩
    ext a b
    rw [hm, (hr g).2]
    exact (h _ _ (entry_mem u g a b)).symm
