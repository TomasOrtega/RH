import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VanIdealHomog
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemVanishingIdealIffKillsFormStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartVanishingKillsFormMulPowStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullbackOfKernelSupStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningSectionHomogeneousFormStatement

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.GE

variable {R : Type} [CommRing R] {N : ℕ}

/- English proof (translation)
Take `⟨x, rfl⟩` from `(ConcreteCategory.bijective_of_isIso (Proj.basicOpenIsoAway (GlobalTheory.ProjSpace.grading R N) (X k) (GlobalTheory.ProjSpace.X_mem R N k) one_pos).hom).2 s`. Take `⟨n, f, hf, rfl⟩` from `HomogeneousLocalization.Away.mk_surjective _ (GlobalTheory.ProjSpace.X_mem R N k) x`. Establish `hf' : f.IsHomogeneous n` using `by simpa using hf`. Use `⟨n, f, hf', ?_⟩` and prove the remaining obligations. Conclude with `(GlobalTheory.ProjFrac.awayToSection_mk _ _ _).trans (GlobalTheory.ProjFrac.frac_eq rfl)`.
-/
theorem exists_eq_formOn (k : Fin (N + 1)) (s : Γ(PSpace R N, GlobalTheory.ProjSpace.chart R N k)) :
    ∃ (n : ℕ) (a : MvPolynomial (Fin (N + 1)) R) (ha : a.IsHomogeneous n),
      s = GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n a ha := by
  obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (Proj.basicOpenIsoAway (GlobalTheory.ProjSpace.grading R N) (X k) (GlobalTheory.ProjSpace.X_mem R N k) one_pos).hom).2 s
  obtain ⟨n, f, hf, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ (GlobalTheory.ProjSpace.X_mem R N k) x
  have hf' : f.IsHomogeneous n := by simpa using hf
  refine ⟨n, f, hf', ?_⟩
  exact (GlobalTheory.ProjFrac.awayToSection_mk _ _ _).trans (GlobalTheory.ProjFrac.frac_eq rfl)

/- English proof (translation)
Rewrite `hv`, the goal using `[mem_map_C_iff]`. Introduce `m`. Rewrite using `[coeff_homogeneousComponent]`. Use `split_ifs`. Conclude with `hv m`.

Conclude with `zero_mem _`.
-/
theorem homogeneousComponent_mem_map_C {K : Ideal R} {d : ℕ} {v : MvPolynomial (Fin (N + 1)) R}
    (hv : v ∈ K.map (C : R →+* MvPolynomial (Fin (N + 1)) R)) :
    homogeneousComponent d v ∈ K.map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  rw [mem_map_C_iff] at hv ⊢
  intro m
  rw [coeff_homogeneousComponent]
  split_ifs
  · exact hv m
  · exact zero_mem _

def homogOf (J : Ideal (MvPolynomial (Fin (N + 1)) R)) (hJ : HomogIdeal J) :
    HomogeneousIdeal (GlobalTheory.ProjSpace.grading R N) :=
  ⟨J, fun d f hf => by
    have := hJ d f hf
    rwa [← decomposition.decompose'_apply f d] at this⟩

/- English proof (translation)
Introduce `s hs`. Take `⟨n, a, ha, rfl⟩` from `exists_eq_formOn k s`. Rewrite `hs` using `[Scheme.Hom.ker_apply]`. Take `⟨m, h, hK⟩` from `GlobalTheory.T.chart_vanishing_kills_form_mul_pow φ n a ha k hs`. Take `⟨m', hm'⟩` from `hge _ ((GlobalTheory.T.mem_vanishing_ideal_iff_kills_form φ _ _ h).2 hK) k`.

Take `⟨u, hu, v, hv, huv⟩` from `Submodule.mem_sup.1 hm'`. Establish `hb : (X k ^ m' * (X k ^ m * a) : MvPolynomial (Fin (N + 1)) R).IsHomogeneous (m' + (m + n))` using `(isHomogeneous_X_pow k m').mul h`. Establish `hcu` using `homogeneousComponent_isHomogeneous (m' + (m + n)) u`. Establish `hcv` using `homogeneousComponent_isHomogeneous (m' + (m + n)) v`. Establish `hsum : homogeneousComponent (m' + (m + n)) u + homogeneousComponent (m' + (m + n)) v = X k ^ m' * (X k ^ m * a)`.

Rewrite using `[← map_add, huv, homogeneousComponent_of_mem hb, if_pos rfl]`. Establish `e1 : GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n a ha = GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl (m' + (m + n)) _ (hcu.add hcv)` using `GlobalTheory.ProjFrac.frac_eq (by rw [hsum]; ring)`. Rewrite using `[e1, GlobalTheory.ProjSpace.formOn_add hcu hcv]`. Use `Submodule.add_mem_sup ?_ ?_` and prove the remaining obligations. Rewrite using `[Scheme.Hom.ker_apply]`.

Conclude with `(GlobalTheory.ProjSpace.vPlusι_app_formOn_eq_zero_iff (homogOf J hJ) k hcu).2 ⟨0, by rw [pow_zero, one_mul]; exact hJ _ _ hu⟩`. Conclude with `(GlobalTheory.T.thickening_section_homogeneous_form I N e k).2 _ _ hcv (homogeneousComponent_mem_map_C hv)`.
-/
theorem ker_le_sup_chart {Y : Scheme.{0}} (I : Ideal R) (e : ℕ)
    (J : Ideal (MvPolynomial (Fin (N + 1)) R)) (hJ : HomogIdeal J)
    (φ : Y ⟶ PSpace R N) [QuasiCompact φ]
    (hge : ∀ f ∈ vanIdeal φ, ∀ k, ∃ m : ℕ, X k ^ m * f ∈
      J ⊔ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R))
    (k : Fin (N + 1)) :
    (Scheme.Hom.ker φ).ideal ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩ ≤
      (Scheme.Hom.ker (GlobalTheory.ProjSpace.vPlusι (homogOf J hJ))).ideal
          ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩ ⊔
        (Scheme.Hom.ker (thickι R I N e)).ideal
          ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩ := by
  intro s hs
  obtain ⟨n, a, ha, rfl⟩ := exists_eq_formOn k s
  rw [Scheme.Hom.ker_apply] at hs
  obtain ⟨m, h, hK⟩ := GlobalTheory.T.chart_vanishing_kills_form_mul_pow φ n a ha k hs
  obtain ⟨m', hm'⟩ := hge _ ((GlobalTheory.T.mem_vanishing_ideal_iff_kills_form φ _ _ h).2 hK) k
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 hm'
  have hb : (X k ^ m' * (X k ^ m * a) : MvPolynomial (Fin (N + 1)) R).IsHomogeneous (m' + (m + n)) :=
    (isHomogeneous_X_pow k m').mul h
  have hcu := homogeneousComponent_isHomogeneous (m' + (m + n)) u
  have hcv := homogeneousComponent_isHomogeneous (m' + (m + n)) v
  have hsum : homogeneousComponent (m' + (m + n)) u + homogeneousComponent (m' + (m + n)) v =
      X k ^ m' * (X k ^ m * a) := by
    rw [← map_add, huv, homogeneousComponent_of_mem hb, if_pos rfl]
  have e1 : GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n a ha =
      GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl (m' + (m + n)) _ (hcu.add hcv) :=
    GlobalTheory.ProjFrac.frac_eq (by rw [hsum]; ring)
  rw [e1, GlobalTheory.ProjSpace.formOn_add hcu hcv]
  refine Submodule.add_mem_sup ?_ ?_
  · rw [Scheme.Hom.ker_apply]
    exact (GlobalTheory.ProjSpace.vPlusι_app_formOn_eq_zero_iff (homogOf J hJ) k hcu).2
      ⟨0, by rw [pow_zero, one_mul]; exact hJ _ _ hu⟩
  · exact (GlobalTheory.T.thickening_section_homogeneous_form I N e k).2 _ _ hcv (homogeneousComponent_mem_map_C hv)

instance isClosedImmersion_thickι (I : Ideal R) (e : ℕ) : IsClosedImmersion (thickι R I N e) := by
  have : IsClosedImmersion (thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

/- English proof (translation)
The claim follows from `(pullback.lift_fst _ _ _).trans (Category.comp_id _)`.
-/
theorem thickMap_thickι (I : Ideal R) (e : ℕ) :
    thickMap R I e (PO R N) ≫ thickι R I N (e + 1) = thickι R I N e :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/- English proof (translation)
Introduce `R _ _ I N Cs i β hi hsq J hJ hle hge`. Establish `hcl : ∀ e, IsClosedImmersion (i e ≫ thickι R I N e)` using `fun e => by`. Use `hi e` as an intermediate fact. Use `infer_instance`. Establish `hfac : ∀ e, ∃ ψ : Cs e ⟶ GlobalTheory.ProjSpace.VPlus (homogOf J hJ), ψ ≫ GlobalTheory.ProjSpace.vPlusι (homogOf J hJ) = i e ≫ thickι R I N e` using `fun e => (GlobalTheory.ProjSpace.exists_comp_vPlusι_iff (homogOf J hJ) _).2 fun k n f hf hfJ => (GlobalTheory.T.mem_vanishing_ideal_iff_kills_form _ n f hf).1 (hle e hfJ) k`.

Use `choose b hb using hfac`. Use `⟨GlobalTheory.ProjSpace.VPlus (homogOf J hJ), GlobalTheory.ProjSpace.vPlusι (homogOf J hJ), b, inferInstance, fun e => ?_, fun e => ?_⟩` and prove the remaining obligations. Establish `hc : IsClosedImmersion (b e ≫ GlobalTheory.ProjSpace.vPlusι (homogOf J hJ))`. Rewrite using `[hb]`. Conclude with `hcl e`.

Use `GlobalTheory.T.is_pullback_of_kernel_sup _ _ _ _ (hb e) ?_` and prove the remaining obligations. Rewrite using `[hb]`. Use `hcl e` as an intermediate fact. Establish `h1 : Scheme.Hom.ker (GlobalTheory.ProjSpace.vPlusι (homogOf J hJ)) ≤ Scheme.Hom.ker (i e ≫ thickι R I N e)`. Rewrite using `[← hb e]`.

Conclude with `Scheme.Hom.le_ker_comp _ _`. Establish `h2 : Scheme.Hom.ker (thickι R I N e) ≤ Scheme.Hom.ker (i e ≫ thickι R I N e)` using `Scheme.Hom.le_ker_comp _ _`. Use `Scheme.IdealSheafData.ext_of_iSup_eq_top (fun k => ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩) (GlobalTheory.ProjSpace.iSup_chart R N) fun k => le_antisymm ?_ ?_` and prove the remaining obligations. Conclude with `ker_le_sup_chart I e J hJ _ (hge e) k`. Conclude with `(Scheme.IdealSheafData.le_def.1 (sup_le h1 h2)) _`.

Use `(cancel_mono (GlobalTheory.ProjSpace.vPlusι (homogOf J hJ))).1 ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, hb, hb, ← Category.assoc, (hsq e).w, Category.assoc, thickMap_thickι]`.
-/
theorem exists_closed_of_homogIdeal : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (N : ℕ)
    (Cs : ℕ → Scheme.{0}) (i : ∀ e, Cs e ⟶ (thickObj R I e (PO R N)).left)
    (β : ∀ e, Cs e ⟶ Cs (e + 1)),
    (∀ e, IsClosedImmersion (i e)) →
    (∀ e, IsPullback (β e) (i e) (i (e + 1)) (thickMap R I e (PO R N))) →
    ∀ (J : Ideal (MvPolynomial (Fin (N + 1)) R)), HomogIdeal J →
    (∀ e, J ≤ vanIdeal (i e ≫ thickι R I N e)) →
    (∀ e, ∀ f ∈ vanIdeal (i e ≫ thickι R I N e), ∀ k, ∃ m : ℕ, X k ^ m * f ∈
      J ⊔ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) →
    ∃ (C' : Scheme.{0}) (j : C' ⟶ (PO R N).left) (b : ∀ e, Cs e ⟶ C'),
      IsClosedImmersion j ∧
      (∀ e, IsPullback (b e) (i e) j (pullback.fst (PO R N).hom (thick R I e))) ∧
      ∀ e, β e ≫ b (e + 1) = b e := by
  intro R _ _ I N Cs i β hi hsq J hJ hle hge
  have hcl : ∀ e, IsClosedImmersion (i e ≫ thickι R I N e) := fun e => by
    have := hi e
    infer_instance
  have hfac : ∀ e, ∃ ψ : Cs e ⟶ GlobalTheory.ProjSpace.VPlus (homogOf J hJ),
      ψ ≫ GlobalTheory.ProjSpace.vPlusι (homogOf J hJ) = i e ≫ thickι R I N e := fun e =>
    (GlobalTheory.ProjSpace.exists_comp_vPlusι_iff (homogOf J hJ) _).2 fun k n f hf hfJ =>
      (GlobalTheory.T.mem_vanishing_ideal_iff_kills_form _ n f hf).1 (hle e hfJ) k
  choose b hb using hfac
  refine ⟨GlobalTheory.ProjSpace.VPlus (homogOf J hJ), GlobalTheory.ProjSpace.vPlusι (homogOf J hJ), b, inferInstance,
    fun e => ?_, fun e => ?_⟩
  · have hc : IsClosedImmersion (b e ≫ GlobalTheory.ProjSpace.vPlusι (homogOf J hJ)) := by
      rw [hb]
      exact hcl e
    refine GlobalTheory.T.is_pullback_of_kernel_sup _ _ _ _ (hb e) ?_
    rw [hb]
    have := hcl e
    have h1 : Scheme.Hom.ker (GlobalTheory.ProjSpace.vPlusι (homogOf J hJ)) ≤
        Scheme.Hom.ker (i e ≫ thickι R I N e) := by
      rw [← hb e]
      exact Scheme.Hom.le_ker_comp _ _
    have h2 : Scheme.Hom.ker (thickι R I N e) ≤ Scheme.Hom.ker (i e ≫ thickι R I N e) :=
      Scheme.Hom.le_ker_comp _ _
    refine Scheme.IdealSheafData.ext_of_iSup_eq_top
      (fun k => ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩)
      (GlobalTheory.ProjSpace.iSup_chart R N) fun k => le_antisymm ?_ ?_
    · exact ker_le_sup_chart I e J hJ _ (hge e) k
    · exact (Scheme.IdealSheafData.le_def.1 (sup_le h1 h2)) _
  · refine (cancel_mono (GlobalTheory.ProjSpace.vPlusι (homogOf J hJ))).1 ?_
    rw [Category.assoc, hb, hb, ← Category.assoc, (hsq e).w, Category.assoc, thickMap_thickι]

end GlobalTheory.CompanionTheory.GE
