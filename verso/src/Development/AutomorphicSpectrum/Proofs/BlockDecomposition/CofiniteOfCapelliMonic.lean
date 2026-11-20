import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapS
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AutomorphicFormsFiniteGLOfGenFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCentreAnnihilatorCompatibleMaps
import GroundTheory.IdeleRoots.ConstantFrames.GaugeExistence.QdetSub

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Polynomial

namespace GlobalTheory.CompanionTheory.CTFin.MonicCofin

/- English proof (translation)
Set `π : C →ₐ[ℂ] C ⧸ I` to `Ideal.Quotient.mkₐ ℂ I`. Establish `hπ : Function.Surjective π` using `Ideal.Quotient.mkₐ_surjective ℂ I`. Establish `hint : ∀ y ∈ π '' s, IsIntegral ℂ y`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Take `⟨q, hm, hqI⟩` from `hq x hx`.

Use `⟨q, hm, ?_⟩` and prove the remaining obligations. Rewrite using `[← aeval_def, aeval_algHom_apply]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 hqI`. Establish `htop : Algebra.adjoin ℂ (π '' s) = ⊤`. Rewrite using `[← AlgHom.map_adjoin, hgen, Algebra.map_top, AlgHom.range_eq_top]`.

Conclude with `hπ`. Establish `hfg` using `fg_adjoin_of_finite (hs.image π) hint`. Rewrite `hfg` using `[htop, Algebra.top_toSubmodule]`. Take `⟨t, ht⟩` from `hfg`. Use `⟨Submodule.span ℂ (Function.surjInv hπ '' (t : Set (C ⧸ I))), FiniteDimensional.span_of_finite ℂ (t.finite_toSet.image _), fun z => ?_⟩` and prove the remaining obligations.

Establish `hmap : (Submodule.span ℂ (Function.surjInv hπ '' (t : Set (C ⧸ I)))).map π.toLinearMap = ⊤`. Rewrite using `[Submodule.map_span, ← Set.image_comp, ← ht]`. Use `congr 1`. Use `Set.image_id _` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `y`.

Conclude with `Function.surjInv_eq hπ y`. Establish `hz : π z ∈ (Submodule.span ℂ (Function.surjInv hπ '' (t : Set (C ⧸ I)))).map π.toLinearMap`. Rewrite using `[hmap]`. Conclude with `Submodule.mem_top`. Take `⟨v, hv, hvz⟩` from `hz`.

Use `⟨v, hv, ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq]`. Conclude with `hvz.symm`.
-/
theorem exists_finiteDimensional_sub_mem {C : Type*} [CommRing C] [Algebra ℂ C] (I : Ideal C) {s : Set C}
    (hs : s.Finite) (hgen : Algebra.adjoin ℂ s = ⊤) (hq : ∀ x ∈ s, ∃ q : ℂ[X], q.Monic ∧ aeval x q ∈ I) :
    ∃ V : Submodule ℂ C, FiniteDimensional ℂ V ∧ ∀ z : C, ∃ v ∈ V, z - v ∈ I := by
  let π : C →ₐ[ℂ] C ⧸ I := Ideal.Quotient.mkₐ ℂ I
  have hπ : Function.Surjective π := Ideal.Quotient.mkₐ_surjective ℂ I
  have hint : ∀ y ∈ π '' s, IsIntegral ℂ y := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨q, hm, hqI⟩ := hq x hx
    refine ⟨q, hm, ?_⟩
    rw [← aeval_def, aeval_algHom_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hqI
  have htop : Algebra.adjoin ℂ (π '' s) = ⊤ := by
    rw [← AlgHom.map_adjoin, hgen, Algebra.map_top, AlgHom.range_eq_top]
    exact hπ
  have hfg := fg_adjoin_of_finite (hs.image π) hint
  rw [htop, Algebra.top_toSubmodule] at hfg
  obtain ⟨t, ht⟩ := hfg
  refine ⟨Submodule.span ℂ (Function.surjInv hπ '' (t : Set (C ⧸ I))),
    FiniteDimensional.span_of_finite ℂ (t.finite_toSet.image _), fun z => ?_⟩
  have hmap : (Submodule.span ℂ (Function.surjInv hπ '' (t : Set (C ⧸ I)))).map π.toLinearMap = ⊤ := by
    rw [Submodule.map_span, ← Set.image_comp, ← ht]
    congr 1
    convert Set.image_id _
    funext y
    exact Function.surjInv_eq hπ y
  have hz : π z ∈ (Submodule.span ℂ (Function.surjInv hπ '' (t : Set (C ⧸ I)))).map π.toLinearMap := by
    rw [hmap]; exact Submodule.mem_top
  obtain ⟨v, hv, hvz⟩ := hz
  refine ⟨v, hv, ?_⟩
  rw [← Ideal.Quotient.eq]
  exact hvz.symm

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

/- English proof (translation)
Rewrite using `[cap, ← GroundTheory.BlockD.FourierDecayAlt.GaugeExists.evU_qdetPoly, GroundTheory.BlockD.FourierDecayAlt.GaugeExists.evU_apply, eval₂_eq_sum, Polynomial.sum]`. Use `Submodule.sum_mem _ fun k hk => ?_` and prove the remaining obligations. Rewrite using `[RingHom.id_apply, ← map_pow, ← Algebra.commutes, ← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span (coeff_mem_coeffs (by simpa using hk)))`.
-/
theorem cap_mem_span_coeffs (τ : E →+* ℂ) (u : ℂ) :
    cap (a := n) τ u ∈ Submodule.span ℂ
      ((GroundTheory.BlockD.FourierDecayAlt.GaugeExists.qdetPoly (Eop (a := n) τ)).coeffs : Set (Module.End ℂ (Sm E n))) := by
  rw [cap, ← GroundTheory.BlockD.FourierDecayAlt.GaugeExists.evU_qdetPoly, GroundTheory.BlockD.FourierDecayAlt.GaugeExists.evU_apply, eval₂_eq_sum,
    Polynomial.sum]
  refine Submodule.sum_mem _ fun k hk => ?_
  rw [RingHom.id_apply, ← map_pow, ← Algebra.commutes, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (coeff_mem_coeffs (by simpa using hk)))

/- English proof (translation)
Take `⟨b, hb, hspan, hli⟩` from `exists_linearIndependent ℂ {z | ∃ (τ : E →+* ℂ) (u : ℂ), z = cap (a := n) τ u}`. Establish `hF : (⋃ τ : E →+* ℂ, ((GroundTheory.BlockD.FourierDecayAlt.GaugeExists.qdetPoly (Eop (a` using `n) τ)).coeffs : Set (Module.End ℂ (Sm E n)))).Finite := Set.finite_iUnion fun τ => Finset.finite_toSet _`. Use `haveI := FiniteDimensional.span_of_finite ℂ hF`. Establish `hle : Submodule.span ℂ {z | ∃ (τ : E →+* ℂ) (u : ℂ), z = cap (a` using `n) τ u} ≤ Submodule.span ℂ (⋃ τ : E →+* ℂ, ((GroundTheory.BlockD.FourierDecayAlt.GaugeExists.qdetPoly (Eop (a := n) τ)).coeffs : Set (Module.End ℂ (Sm E n)))) := by`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨τ, u, rfl⟩`. Conclude with `Submodule.span_mono (Set.subset_iUnion (fun τ : E →+* ℂ => ((GroundTheory.BlockD.FourierDecayAlt.GaugeExists.qdetPoly (Eop (a := n) τ)).coeffs : Set (Module.End ℂ (Sm E n)))) τ) (cap_mem_span_coeffs τ u)`. Use `haveI := Submodule.finiteDimensional_of_le hle`. Establish `hfin : b.Finite`. Establish `hli' : LinearIndependent ℂ (fun x : b => (⟨x.1, hspan ▸ Submodule.subset_span x.2⟩ : Submodule.span ℂ {z | ∃ (τ : E →+* ℂ) (u : ℂ), z = cap (a` using `n) τ u})) := LinearIndependent.of_comp (Submodule.subtype _) hli`.

Use `hli'.finite` as an intermediate fact. Conclude with `Set.toFinite b`. Conclude with `⟨b, hfin, hb, hspan⟩`.
-/
theorem exists_finite_subset_span_cap :
    ∃ b : Set (Module.End ℂ (Sm E n)), b.Finite ∧ b ⊆ {z | ∃ τ u, z = cap (a := n) τ u} ∧
      Submodule.span ℂ b = Submodule.span ℂ {z | ∃ (τ : E →+* ℂ) (u : ℂ), z = cap (a := n) τ u} := by
  obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent ℂ {z | ∃ (τ : E →+* ℂ) (u : ℂ), z = cap (a := n) τ u}
  have hF : (⋃ τ : E →+* ℂ, ((GroundTheory.BlockD.FourierDecayAlt.GaugeExists.qdetPoly (Eop (a := n) τ)).coeffs :
      Set (Module.End ℂ (Sm E n)))).Finite := Set.finite_iUnion fun τ => Finset.finite_toSet _
  haveI := FiniteDimensional.span_of_finite ℂ hF
  have hle : Submodule.span ℂ {z | ∃ (τ : E →+* ℂ) (u : ℂ), z = cap (a := n) τ u} ≤ Submodule.span ℂ
      (⋃ τ : E →+* ℂ, ((GroundTheory.BlockD.FourierDecayAlt.GaugeExists.qdetPoly (Eop (a := n) τ)).coeffs :
      Set (Module.End ℂ (Sm E n)))) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨τ, u, rfl⟩
    exact Submodule.span_mono (Set.subset_iUnion (fun τ : E →+* ℂ =>
      ((GroundTheory.BlockD.FourierDecayAlt.GaugeExists.qdetPoly (Eop (a := n) τ)).coeffs : Set (Module.End ℂ (Sm E n)))) τ)
      (cap_mem_span_coeffs τ u)
  haveI := Submodule.finiteDimensional_of_le hle
  have hfin : b.Finite := by
    have hli' : LinearIndependent ℂ (fun x : b => (⟨x.1, hspan ▸ Submodule.subset_span x.2⟩ :
        Submodule.span ℂ {z | ∃ (τ : E →+* ℂ) (u : ℂ), z = cap (a := n) τ u})) :=
      LinearIndependent.of_comp (Submodule.subtype _) hli
    have := hli'.finite
    exact Set.toFinite b
  exact ⟨b, hfin, hb, hspan⟩

/- English proof (translation)
Establish `hZ : ∀ c : C, ι c ∈ Zalg E n` using `fun c => hr ▸ AlgHom.mem_range_self ι c`. Establish `hZ' : ∀ z ∈ Zalg E n, ∃ c : C, ι c = z` using `fun z hz => by`. Rewrite `hz` using `[← hr]`. Conclude with `hz`. Take `⟨b, hbfin, hbT, hspan⟩` from `exists_finite_subset_span_cap (E := E) (n := n)`.

Establish `hbZ : b ⊆ Zalg E n` using `fun x hx => Algebra.subset_adjoin (hbT hx)`. Set `s : Set C` to `ι ⁻¹' b`. Establish `hs : s.Finite` using `hbfin.preimage hι.injOn`. Establish `himg : ι '' s = b` using `Set.image_preimage_eq_of_subset fun x hx => hZ' x (hbZ hx)`. Establish `hgen : Algebra.adjoin ℂ s = ⊤`.

Use `Subalgebra.map_injective hι ?_` and prove the remaining obligations. Rewrite using `[AlgHom.map_adjoin, himg, Algebra.map_top, hr]`. Use `le_antisymm (Algebra.adjoin_le hbZ) (Algebra.adjoin_le ?_)` and prove the remaining obligations. Introduce `x hx`. Establish `h1 : x ∈ Submodule.span ℂ b` using `hspan ▸ Submodule.subset_span hx`.

Conclude with `(Submodule.span_le.2 Algebra.subset_adjoin : Submodule.span ℂ b ≤ Subalgebra.toSubmodule (Algebra.adjoin ℂ b)) h1`. Set `I : Ideal C` to `Ideal.span (ι ⁻¹' J)`. Establish `hI : ∀ w ∈ I, ι w ∈ Submodule.span ℂ {y | ∃ x ∈ Zalg E n, ∃ j ∈ J, y = x * j}`. Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`.

Consider the case `mem w hw => exact Submodule.subset_span ⟨1, Subalgebra.one_mem _, ι w, hw, (one_mul _).symm⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`.

Consider the case `smul a x _ hx`. Rewrite using `[smul_eq_mul, map_mul]`. Conclude with `GlobalTheory.CompanionTheory.HCFin.mul_mem_span_zalg_mul (hZ a) hx`. Establish `hrel : ∀ x ∈ s, ∃ q : ℂ[X], q.Monic ∧ aeval x q ∈ I`. Introduce `x hx`.

Take `⟨τ, u, hτ⟩` from `hbT hx`. Take `⟨q, hm, hqJ⟩` from `hq τ u`. Use `⟨q, hm, Ideal.subset_span ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ι (aeval x q) ∈ J`. Rewrite using `[← aeval_algHom_apply, hτ]`.

Conclude with `hqJ`. Take `⟨V, hV, hz⟩` from `exists_finiteDimensional_sub_mem I hs hgen hrel`. Use `⟨hJ, V.map ι.toLinearMap, inferInstance, fun z hzZ => ?_⟩` and prove the remaining obligations. Take `⟨c, rfl⟩` from `hZ' z hzZ`. Take `⟨v, hv, hvI⟩` from `hz c`.

Use `Submodule.mem_sup.2 ⟨ι v, Submodule.mem_map_of_mem hv, ι (c - v), hI _ hvI, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub]`. Normalize the expressions using the abelian group laws.
-/
theorem cofin_of_algHom {C : Type} [CommRing C] [Algebra ℂ C] (ι : C →ₐ[ℂ] Module.End ℂ (Sm E n))
    (hι : Function.Injective ι) (hr : ι.range = Zalg E n) (J : Set (Module.End ℂ (Sm E n))) (hJ : J ⊆ Zalg E n)
    (hq : ∀ (τ : E →+* ℂ) (u : ℂ), ∃ q : Polynomial ℂ, q.Monic ∧ Polynomial.aeval (cap (a := n) τ u) q ∈ J) :
    Cofin J := by
  have hZ : ∀ c : C, ι c ∈ Zalg E n := fun c => hr ▸ AlgHom.mem_range_self ι c
  have hZ' : ∀ z ∈ Zalg E n, ∃ c : C, ι c = z := fun z hz => by
    rw [← hr] at hz
    exact hz
  obtain ⟨b, hbfin, hbT, hspan⟩ := exists_finite_subset_span_cap (E := E) (n := n)
  have hbZ : b ⊆ Zalg E n := fun x hx => Algebra.subset_adjoin (hbT hx)
  let s : Set C := ι ⁻¹' b
  have hs : s.Finite := hbfin.preimage hι.injOn
  have himg : ι '' s = b := Set.image_preimage_eq_of_subset fun x hx => hZ' x (hbZ hx)
  have hgen : Algebra.adjoin ℂ s = ⊤ := by
    refine Subalgebra.map_injective hι ?_
    rw [AlgHom.map_adjoin, himg, Algebra.map_top, hr]
    refine le_antisymm (Algebra.adjoin_le hbZ) (Algebra.adjoin_le ?_)
    intro x hx
    have h1 : x ∈ Submodule.span ℂ b := hspan ▸ Submodule.subset_span hx
    exact (Submodule.span_le.2 Algebra.subset_adjoin :
      Submodule.span ℂ b ≤ Subalgebra.toSubmodule (Algebra.adjoin ℂ b)) h1
  let I : Ideal C := Ideal.span (ι ⁻¹' J)
  have hI : ∀ w ∈ I, ι w ∈ Submodule.span ℂ {y | ∃ x ∈ Zalg E n, ∃ j ∈ J, y = x * j} := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => exact Submodule.subset_span ⟨1, Subalgebra.one_mem _, ι w, hw, (one_mul _).symm⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [smul_eq_mul, map_mul]
      exact GlobalTheory.CompanionTheory.HCFin.mul_mem_span_zalg_mul (hZ a) hx
  have hrel : ∀ x ∈ s, ∃ q : ℂ[X], q.Monic ∧ aeval x q ∈ I := by
    intro x hx
    obtain ⟨τ, u, hτ⟩ := hbT hx
    obtain ⟨q, hm, hqJ⟩ := hq τ u
    refine ⟨q, hm, Ideal.subset_span ?_⟩
    change ι (aeval x q) ∈ J
    rw [← aeval_algHom_apply, hτ]
    exact hqJ
  obtain ⟨V, hV, hz⟩ := exists_finiteDimensional_sub_mem I hs hgen hrel
  refine ⟨hJ, V.map ι.toLinearMap, inferInstance, fun z hzZ => ?_⟩
  obtain ⟨c, rfl⟩ := hZ' z hzZ
  obtain ⟨v, hv, hvI⟩ := hz c
  refine Submodule.mem_sup.2 ⟨ι v, Submodule.mem_map_of_mem hv, ι (c - v), hI _ hvI, ?_⟩
  rw [map_sub]
  abel

/- English proof (translation)
Establish `hcomm : ∀ x ∈ {z : Module.End ℂ (Sm E n) | ∃ (τ : E →+* ℂ) (u : ℂ), z = cap (a` using `n) τ u}, ∀ y ∈ {z : Module.End ℂ (Sm E n) | ∃ (τ : E →+* ℂ) (u : ℂ), z = cap (a := n) τ u}, x * y = y * x := fun x hx y hy => (GlobalTheory.AutGrowth.KilledFin.Zalg_commute (Algebra.subset_adjoin hx) (Algebra.subset_adjoin hy)).eq`. Conclude with `@cofin_of_algHom E _ _ _ n (Zalg E n) (Algebra.adjoinCommRingOfComm ℂ hcomm) (Subalgebra.algebra _) (Zalg E n).val Subtype.val_injective (Subalgebra.range_val _) J hJ hq`.
-/
theorem cofin_of_monic (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ)
    (J : Set (Module.End ℂ (Sm E n))) (hJ : J ⊆ Zalg E n)
    (hq : ∀ (τ : E →+* ℂ) (u : ℂ), ∃ q : Polynomial ℂ, q.Monic ∧ Polynomial.aeval (cap (a := n) τ u) q ∈ J) :
    Cofin J := by
  have hcomm : ∀ x ∈ {z : Module.End ℂ (Sm E n) | ∃ (τ : E →+* ℂ) (u : ℂ), z = cap (a := n) τ u},
      ∀ y ∈ {z : Module.End ℂ (Sm E n) | ∃ (τ : E →+* ℂ) (u : ℂ), z = cap (a := n) τ u}, x * y = y * x :=
    fun x hx y hy => (GlobalTheory.AutGrowth.KilledFin.Zalg_commute (Algebra.subset_adjoin hx) (Algebra.subset_adjoin hy)).eq
  exact @cofin_of_algHom E _ _ _ n (Zalg E n) (Algebra.adjoinCommRingOfComm ℂ hcomm) (Subalgebra.algebra _)
    (Zalg E n).val Subtype.val_injective (Subalgebra.range_val _) J hJ hq

end GlobalTheory.CompanionTheory.CTFin.MonicCofin

end
