import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.EulerFacMulConjInvSplit

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace Regroup

/- English proof (translation)
Establish `h1 : HasProd (fun p : (Σ b : β, {x // π x = b}) => f (Equiv.sigmaFiberEquiv π p)) (∏' a, f a)` using `(Equiv.sigmaFiberEquiv π).hasProd_iff.2 hf.hasProd`. Conclude with `(HasProd.sigma h1 hg).tprod_eq.symm`.
-/
theorem tprod_eq_of_fibre {α β : Type*} {f : α → ℝ} (π : α → β) {g : β → ℝ} (hf : Multipliable f)
    (hg : ∀ b, HasProd (fun c : {x // π x = b} => f c.1) (g b)) : ∏' a, f a = ∏' b, g b := by
  have h1 : HasProd (fun p : (Σ b : β, {x // π x = b}) => f (Equiv.sigmaFiberEquiv π p))
      (∏' a, f a) := (Equiv.sigmaFiberEquiv π).hasProd_iff.2 hf.hasProd
  exact (HasProd.sigma h1 hg).tprod_eq.symm

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

/- English proof (translation)
The claim follows from `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P`.
-/
theorem comap_isMaximal {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal :=
  Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P

/- English proof (translation)
Take `⟨P, hP, hP𝔭⟩` from `exists_maximal_over hK hF 𝔭.2`. Establish `hmem : ∀ c : {x : {P : Ideal (𝓞 K) // P.IsMaximal} // (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), comap_isMaximal x.2⟩ : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) = 𝔭}, c.1.1 = P ∨ c.1.1 = Formalism.HermitianLatticesTheory.conjIdeal (K` using `K) P := by`. Introduce `c`. Establish `h1 : c.1.1.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭.1` using `congrArg Subtype.val c.2`. Conclude with `(comap_eq_comap_iff hK hF hP c.1.2).1 (hP𝔭.trans h1.symm)`.

Establish `heta` using `etaF_comap hK hF hP`. Rewrite `heta` using `[hP𝔭]`. Set `c0 : {x : {P : Ideal (𝓞 K) // P.IsMaximal} // (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), comap_isMaximal x.2⟩ : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) = 𝔭}` to `⟨⟨P, hP⟩, Subtype.ext hP𝔭⟩`. Distinguish the cases in `hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P`. Establish `hN` using `absNorm_comap_inert hK hF hP hc`.

Rewrite `hN` using `[hP𝔭]`. Establish `hval : Formalism.HermitianLatticesTheory.eulerFac K M P = (1 - etaF K F 𝔭.1 ^ M * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(M : ℤ)))⁻¹`. Rewrite using `[← inv_inv (Formalism.HermitianLatticesTheory.eulerFac K M P), eulerFac_inv_inert hK hP hc, heta, if_pos hc, ← hN]`. Use `push_cast`. Rewrite using `[Real.sqrt_sq (Nat.cast_nonneg _)]`.

Establish `h` using `hasProd_prod_of_ne_finset_one (L := SummationFilter.unconditional _) (f := fun c : {x : {P : Ideal (𝓞 K) // P.IsMaximal} // (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), comap_isMaximal x.2⟩ : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) = 𝔭} => Formalism.HermitianLatticesTheory.eulerFac K M c.1.1) …`. Introduce `b hb`. It suffices to derive a contradiction. Apply `hb` to reduce the goal to its premises. Rewrite using `[Finset.mem_singleton]`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Break down `hmem b with h | h` into its components or cases. Conclude with `h`. Conclude with `h.trans hc)`.

Rewrite `h` using `[Finset.prod_singleton]`. Rewrite using `[← hval]`. Conclude with `h`. Establish `hN` using `absNorm_comap_split hK hF hP hc`. Rewrite `hN` using `[hP𝔭]`.

Establish `hPb` using `conjIdeal_isMaximal hK hP`. Establish `hPb𝔭 : (Formalism.HermitianLatticesTheory.conjIdeal (K` using `K) P).comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭.1 := by`. Rewrite using `[← hP𝔭]`. Conclude with `((comap_eq_comap_iff hK hF hP hPb).2 (Or.inr rfl)).symm`. Set `c1 : {x : {P : Ideal (𝓞 K) // P.IsMaximal} // (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), comap_isMaximal x.2⟩ : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) = 𝔭}` to `⟨⟨Formalism.HermitianLatticesTheory.conjIdeal (K := K) P, hPb⟩, Subtype.ext hPb𝔭⟩`.

Establish `hne : c0 ≠ c1`. Introduce `h`. Conclude with `hc (congrArg (fun c => c.1.1) h).symm`. Establish `hval : Formalism.HermitianLatticesTheory.eulerFac K M P * Formalism.HermitianLatticesTheory.eulerFac K M (Formalism.HermitianLatticesTheory.conjIdeal (K` using `K) P) = (1 - etaF K F 𝔭.1 ^ M * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(M : ℤ)))⁻¹ := by`. Rewrite using `[← inv_inv (Formalism.HermitianLatticesTheory.eulerFac K M P * _), eulerFac_mul_conj_inv_split hK hP hc M hM, heta, if_neg hc, hN, one_pow, one_mul]`.

Establish `h` using `hasProd_prod_of_ne_finset_one (L := SummationFilter.unconditional _) (f := fun c : {x : {P : Ideal (𝓞 K) // P.IsMaximal} // (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), comap_isMaximal x.2⟩ : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) = 𝔭} => Formalism.HermitianLatticesTheory.eulerFac K M c.1.1) …`. Introduce `b hb`. It suffices to derive a contradiction. Apply `hb` to reduce the goal to its premises. Rewrite using `[Finset.mem_insert, Finset.mem_singleton]`.

Break down `hmem b with h | h` into its components or cases. Conclude with `Or.inl (Subtype.ext (Subtype.ext h))`. Conclude with `Or.inr (Subtype.ext (Subtype.ext h)))`. Rewrite `h` using `[Finset.prod_pair hne]`. Rewrite using `[← hval]`.

Conclude with `h`.
-/
theorem hasProd_fibre (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) (M : ℕ) (hM : 1 ≤ M)
    (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) :
    HasProd (fun c : {x : {P : Ideal (𝓞 K) // P.IsMaximal} //
        (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), comap_isMaximal x.2⟩ :
          {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) = 𝔭} => Formalism.HermitianLatticesTheory.eulerFac K M c.1.1)
      (1 - etaF K F 𝔭.1 ^ M * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(M : ℤ)))⁻¹ := by
  classical
  obtain ⟨P, hP, hP𝔭⟩ := exists_maximal_over hK hF 𝔭.2
  have hmem : ∀ c : {x : {P : Ideal (𝓞 K) // P.IsMaximal} //
        (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), comap_isMaximal x.2⟩ :
          {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) = 𝔭},
      c.1.1 = P ∨ c.1.1 = Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
    intro c
    have h1 : c.1.1.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭.1 := congrArg Subtype.val c.2
    exact (comap_eq_comap_iff hK hF hP c.1.2).1 (hP𝔭.trans h1.symm)
  have heta := etaF_comap hK hF hP
  rw [hP𝔭] at heta
  let c0 : {x : {P : Ideal (𝓞 K) // P.IsMaximal} //
        (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), comap_isMaximal x.2⟩ :
          {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) = 𝔭} := ⟨⟨P, hP⟩, Subtype.ext hP𝔭⟩
  by_cases hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P
  · have hN := absNorm_comap_inert hK hF hP hc
    rw [hP𝔭] at hN
    have hval : Formalism.HermitianLatticesTheory.eulerFac K M P =
        (1 - etaF K F 𝔭.1 ^ M * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(M : ℤ)))⁻¹ := by
      rw [← inv_inv (Formalism.HermitianLatticesTheory.eulerFac K M P), eulerFac_inv_inert hK hP hc, heta, if_pos hc, ← hN]
      push_cast
      rw [Real.sqrt_sq (Nat.cast_nonneg _)]
    have h := hasProd_prod_of_ne_finset_one (L := SummationFilter.unconditional _) (f := fun c : {x : {P : Ideal (𝓞 K) // P.IsMaximal} //
        (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), comap_isMaximal x.2⟩ :
          {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) = 𝔭} => Formalism.HermitianLatticesTheory.eulerFac K M c.1.1) (s := {c0})
      (by
        intro b hb
        exfalso
        apply hb
        rw [Finset.mem_singleton]
        apply Subtype.ext
        apply Subtype.ext
        rcases hmem b with h | h
        · exact h
        · exact h.trans hc)
    rw [Finset.prod_singleton] at h
    rw [← hval]
    exact h
  · have hN := absNorm_comap_split hK hF hP hc
    rw [hP𝔭] at hN
    have hPb := conjIdeal_isMaximal hK hP
    have hPb𝔭 : (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P).comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭.1 := by
      rw [← hP𝔭]
      exact ((comap_eq_comap_iff hK hF hP hPb).2 (Or.inr rfl)).symm
    let c1 : {x : {P : Ideal (𝓞 K) // P.IsMaximal} //
        (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), comap_isMaximal x.2⟩ :
          {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) = 𝔭} :=
      ⟨⟨Formalism.HermitianLatticesTheory.conjIdeal (K := K) P, hPb⟩, Subtype.ext hPb𝔭⟩
    have hne : c0 ≠ c1 := by
      intro h
      exact hc (congrArg (fun c => c.1.1) h).symm
    have hval : Formalism.HermitianLatticesTheory.eulerFac K M P * Formalism.HermitianLatticesTheory.eulerFac K M (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) =
        (1 - etaF K F 𝔭.1 ^ M * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(M : ℤ)))⁻¹ := by
      rw [← inv_inv (Formalism.HermitianLatticesTheory.eulerFac K M P * _), eulerFac_mul_conj_inv_split hK hP hc M hM, heta,
        if_neg hc, hN, one_pow, one_mul]
    have h := hasProd_prod_of_ne_finset_one (L := SummationFilter.unconditional _) (f := fun c : {x : {P : Ideal (𝓞 K) // P.IsMaximal} //
        (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), comap_isMaximal x.2⟩ :
          {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) = 𝔭} => Formalism.HermitianLatticesTheory.eulerFac K M c.1.1) (s := {c0, c1})
      (by
        intro b hb
        exfalso
        apply hb
        rw [Finset.mem_insert, Finset.mem_singleton]
        rcases hmem b with h | h
        · exact Or.inl (Subtype.ext (Subtype.ext h))
        · exact Or.inr (Subtype.ext (Subtype.ext h)))
    rw [Finset.prod_pair hne] at h
    rw [← hval]
    exact h

end Regroup

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.lValEta lValEtaF`. Conclude with `Regroup.tprod_eq_of_fibre (fun x : {P : Ideal (𝓞 K) // P.IsMaximal} => (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), Regroup.comap_isMaximal x.2⟩ : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})) (multipliable_eulerFac hK M hM) (Regroup.hasProd_fibre hK hF M (by omega))`.
-/
theorem lValEta_eq_lValEtaF (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) (M : ℕ) (hM : 2 ≤ M) :
    Formalism.HermitianLatticesTheory.lValEta K M = lValEtaF K F M := by
  unfold Formalism.HermitianLatticesTheory.lValEta lValEtaF
  exact Regroup.tprod_eq_of_fibre
    (fun x : {P : Ideal (𝓞 K) // P.IsMaximal} =>
      (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), Regroup.comap_isMaximal x.2⟩ :
        {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}))
    (multipliable_eulerFac hK M hM) (Regroup.hasProd_fibre hK hF M (by omega))

/- English proof (translation)
Introduce `K F _ _ _ _ _ _ hK hF M hM`. Conclude with `⟨multipliable_eulerFac hK M hM, lValEta_pos hK M hM, lValEta_eq_lValEtaF hK hF M hM⟩`.
-/
theorem eulerEta : EulerEta := by
  intro K F _ _ _ _ _ _ hK hF M hM
  exact ⟨multipliable_eulerFac hK M hM, lValEta_pos hK M hM, lValEta_eq_lValEtaF hK hF M hM⟩

end Formalism.HermitianLattices.Ext.L3
