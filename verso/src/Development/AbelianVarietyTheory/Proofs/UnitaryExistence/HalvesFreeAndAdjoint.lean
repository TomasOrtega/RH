import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegPFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ZeroNotAdmissibleOfRankPos

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HalfPairing

open scoped TensorProduct in

/- English proof (translation)
Use `haveI : IsArtinianRing (R ⧸ I) := isArtinian_of_finite`. Take `⟨b⟩` from `Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] N) r (fun P => by haveI := P.isMaximal`. Use `letI : Field ((R ⧸ I) ⧸ P.asIdeal) := Ideal.Quotient.field _`. Rewrite using `[(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.asIdeal) ((R ⧸ I) ⧸ P.asIdeal) N).finrank_eq]`. Establish `h1` using `Module.rankAtStalk_baseChange (R := R) (M := N) (S := (R ⧸ I) ⧸ P.asIdeal) ⊥`.

Rewrite `h1` using `[Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank, hr]`. Conclude with `h1)`. Conclude with `⟨(TensorProduct.quotTensorEquivQuotSMul N I).symm ≪≫ₗ (b.equivFun.restrictScalars R)⟩`.
-/
theorem nonempty_equiv_quot {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (I : Ideal R) [Finite (R ⧸ I)] (r : ℕ)
    (hr : Module.finrank R N = r) :
    Nonempty ((N ⧸ (I • ⊤ : Submodule R N)) ≃ₗ[R] (Fin r → R ⧸ I)) := by
  haveI : IsArtinianRing (R ⧸ I) := isArtinian_of_finite
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] N) r (fun P => by
    haveI := P.isMaximal
    letI : Field ((R ⧸ I) ⧸ P.asIdeal) := Ideal.Quotient.field _
    rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.asIdeal)
      ((R ⧸ I) ⧸ P.asIdeal) N).finrank_eq]
    have h1 := Module.rankAtStalk_baseChange (R := R) (M := N) (S := (R ⧸ I) ⧸ P.asIdeal) ⊥
    rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank, hr] at h1
    exact h1)
  exact ⟨(TensorProduct.quotTensorEquivQuotSMul N I).symm ≪≫ₗ (b.equivFun.restrictScalars R)⟩

/- English proof (translation)
Establish `hk : ∀ a ∈ I, ∀ q : Q, a • q = 0`. Introduce `a ha q`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_smul, map_zero]`. Use function extensionality and compare the values at `i`.

Rewrite using `[Pi.smul_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_mul]`. Both sides reduce to the same expression. Set `f : Fin r → ((R ⧸ I) →ₗ[R] Q)` to `fun b => Submodule.liftQ I (LinearMap.toSpanSingleton R Q (x b)) (fun a ha => by`. Rewrite using `[LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]`. Conclude with `hk a ha _)`.

Establish `hf : ∀ b, f b 1 = x b` using `fun b => by`. Establish `: f b (Submodule.Quotient.mk (1 : R)) = x b`. Simplify using `only [f, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul]`. Conclude with `this`. Set `ψ : (Fin r → R ⧸ I) →ₗ[R] Q` to `∑ b, (f b) ∘ₗ LinearMap.proj b`.

Establish `hψ : ∀ b, ψ (Pi.single b 1) = x b` using `fun b => by`. Simplify using `only [ψ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]`. Rewrite using `[Finset.sum_eq_single b]`. Rewrite using `[Pi.single_eq_same, hf]`. Introduce `i _ hi`.

Rewrite using `[Pi.single_eq_of_ne hi, map_zero]`. Simplify using the standard rewrite rules. Establish `hs : Function.Surjective ψ`. Rewrite using `[← LinearMap.range_eq_top, eq_top_iff, ← hx, Submodule.span_le]`. Introduce and unpack `_ ⟨b, rfl⟩`.

Conclude with `⟨_, hψ b⟩`. Establish `hi : Function.Injective (e.toLinearMap ∘ₗ ψ)` using `OrzechProperty.injective_of_surjective_endomorphism _ (e.surjective.comp hs)`. Conclude with `⟨LinearEquiv.ofBijective ψ ⟨Function.Injective.of_comp (f := e) hi, hs⟩, hψ⟩`.
-/
theorem exists_equiv_of_span {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] (I : Ideal R) (r : ℕ)
    (e : Q ≃ₗ[R] (Fin r → R ⧸ I)) (x : Fin r → Q) (hx : Submodule.span R (Set.range x) = ⊤) :
    ∃ ψ : (Fin r → R ⧸ I) ≃ₗ[R] Q, ∀ b, ψ (Pi.single b 1) = x b := by
  have hk : ∀ a ∈ I, ∀ q : Q, a • q = 0 := by
    intro a ha q
    apply e.injective
    rw [map_smul, map_zero]
    funext i
    rw [Pi.smul_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_mul]
    rfl
  let f : Fin r → ((R ⧸ I) →ₗ[R] Q) := fun b =>
    Submodule.liftQ I (LinearMap.toSpanSingleton R Q (x b)) (fun a ha => by
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]; exact hk a ha _)
  have hf : ∀ b, f b 1 = x b := fun b => by
    have : f b (Submodule.Quotient.mk (1 : R)) = x b := by
      simp only [f, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul]
    exact this
  let ψ : (Fin r → R ⧸ I) →ₗ[R] Q := ∑ b, (f b) ∘ₗ LinearMap.proj b
  have hψ : ∀ b, ψ (Pi.single b 1) = x b := fun b => by
    simp only [ψ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [Finset.sum_eq_single b]
    · rw [Pi.single_eq_same, hf]
    · intro i _ hi; rw [Pi.single_eq_of_ne hi, map_zero]
    · simp
  have hs : Function.Surjective ψ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hx, Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    exact ⟨_, hψ b⟩
  have hi : Function.Injective (e.toLinearMap ∘ₗ ψ) :=
    OrzechProperty.injective_of_surjective_endomorphism _ (e.surjective.comp hs)
  exact ⟨LinearEquiv.ofBijective ψ ⟨Function.Injective.of_comp (f := e) hi, hs⟩, hψ⟩

/- English proof (translation)
Use `⟨fun b => e.symm (Pi.single b 1), eq_top_iff.2 fun q _ => ?_⟩` and prove the remaining obligations. Establish `h : q = ∑ b, e.symm (Pi.single b (e q b))`. Rewrite using `[← map_sum, Finset.univ_sum_single, e.symm_apply_apply]`. Rewrite using `[h]`. Use `Submodule.sum_mem _ fun b _ => ?_` and prove the remaining obligations.

Take `⟨a, ha⟩` from `Ideal.Quotient.mk_surjective (e q b)`. Establish `: (Pi.single b (e q b) : Fin r → R ⧸ I) = a • Pi.single b 1`. Rewrite using `[← Pi.single_smul, ← ha, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]`. Rewrite using `[this, map_smul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)`.
-/
theorem exists_span {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] (I : Ideal R) (r : ℕ)
    (e : Q ≃ₗ[R] (Fin r → R ⧸ I)) : ∃ x : Fin r → Q, Submodule.span R (Set.range x) = ⊤ := by
  refine ⟨fun b => e.symm (Pi.single b 1), eq_top_iff.2 fun q _ => ?_⟩
  have h : q = ∑ b, e.symm (Pi.single b (e q b)) := by
    rw [← map_sum, Finset.univ_sum_single, e.symm_apply_apply]
  rw [h]
  refine Submodule.sum_mem _ fun b _ => ?_
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (e q b)
  have : (Pi.single b (e q b) : Fin r → R ⧸ I) = a • Pi.single b 1 := by
    rw [← Pi.single_smul, ← ha, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]
  rw [this, map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)

/- English proof (translation)
Take `⟨ψ, hψ⟩` from `exists_equiv_of_span I r e x hx`. Take `⟨ψ', hψ'⟩` from `exists_equiv_of_span I r e x' hx'`. Establish `h0 : ∀ b, (ψ.symm ≪≫ₗ ψ') (x b) = x' b` using `fun b => by`. Rewrite using `[LinearEquiv.trans_apply, ← hψ, ψ.symm_apply_apply, hψ']`. Use `⟨ψ.symm ≪≫ₗ ψ', h0, fun g hg => ?_⟩` and prove the remaining obligations.

Apply `LinearEquiv.toLinearMap_injective` to reduce the goal to its premises. Use `LinearMap.ext_on_range hx fun b => ?_` and prove the remaining obligations. Conclude with `(hg b).trans (h0 b).symm`.
-/
theorem existsUnique_equiv {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] (I : Ideal R) (r : ℕ)
    (e : Q ≃ₗ[R] (Fin r → R ⧸ I)) (x x' : Fin r → Q) (hx : Submodule.span R (Set.range x) = ⊤)
    (hx' : Submodule.span R (Set.range x') = ⊤) : ∃! g : Q ≃ₗ[R] Q, ∀ b, g (x b) = x' b := by
  obtain ⟨ψ, hψ⟩ := exists_equiv_of_span I r e x hx
  obtain ⟨ψ', hψ'⟩ := exists_equiv_of_span I r e x' hx'
  have h0 : ∀ b, (ψ.symm ≪≫ₗ ψ') (x b) = x' b := fun b => by
    rw [LinearEquiv.trans_apply, ← hψ, ψ.symm_apply_apply, hψ']
  refine ⟨ψ.symm ≪≫ₗ ψ', h0, fun g hg => ?_⟩
  apply LinearEquiv.toLinearMap_injective
  refine LinearMap.ext_on_range hx fun b => ?_
  exact (hg b).trans (h0 b).symm

/- English proof (translation)
Use `choose w hw using hrep`. Set `a : (P →ₗ[R] P) → (Q →ₗ[R] Q)` to `fun g => { toFun := w g map_add' := fun v v' => hnd _ _ fun u => by rw [← hw, hadd, hadd, hw, hw] map_smul' := fun r v => hnd _ _ fun u => by`. Rewrite using `[← hw, RingHom.id_apply, hbal, hbal, ← map_smul, hw] }`. Establish `ha : ∀ g u v, B (g u) v = B u (a g v)` using `fun g u v => hw g v u`. Establish `hinv : ∀ g g' : P →ₗ[R] P, (∀ u, g (g' u) = u) → a g' ∘ₗ a g = LinearMap.id` using `fun g g' h => by`.

Use extensionality with `v`. Use `hnd _ _ fun u => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, ← ha, ← ha, h, LinearMap.id_apply]`. Set `adj : (P ≃ₗ[R] P) → (Q ≃ₗ[R] Q)` to `fun g => LinearEquiv.ofLinear (a g) (a g.symm) (hinv _ _ fun u => g.symm_apply_apply u) (hinv _ _ fun u => g.apply_symm_apply u)`. Establish `hadj : ∀ (g : P ≃ₗ[R] P) u v, B (g u) v = B u (adj g v)` using `fun g u v => ha g u v`.

Use `⟨adj, fun g g' => ?_, fun k g => ⟨fun h => ?_, fun h => h ▸ hadj g⟩⟩` and prove the remaining obligations. Use extensionality with `v`. Use `hnd _ _ fun u => ?_` and prove the remaining obligations. Rewrite using `[← hadj, LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← hadj, ← hadj]`. Use extensionality with `v`.

Conclude with `hnd _ _ fun u => by rw [← h, hadj]`.
-/
theorem exists_adjoint {R P Q Z : Type} [CommRing R] [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [AddCommGroup Z] (s : R → R) (B : P → Q → Z) (hadd : ∀ u v w, B u (v + w) = B u v + B u w)
    (hbal : ∀ a u v, B u (a • v) = B (s a • u) v)
    (hnd : ∀ v w, (∀ u, B u v = B u w) → v = w)
    (hrep : ∀ (g : P →ₗ[R] P) (v : Q), ∃ w, ∀ u, B (g u) v = B u w) :
    ∃ adj : (P ≃ₗ[R] P) → (Q ≃ₗ[R] Q), (∀ g g', adj (g * g') = adj g' * adj g) ∧
      ∀ (k : Q ≃ₗ[R] Q) (g : P ≃ₗ[R] P), (∀ u v, B (g u) v = B u (k v)) ↔ k = adj g := by
  choose w hw using hrep
  let a : (P →ₗ[R] P) → (Q →ₗ[R] Q) := fun g =>
    { toFun := w g
      map_add' := fun v v' => hnd _ _ fun u => by rw [← hw, hadd, hadd, hw, hw]
      map_smul' := fun r v => hnd _ _ fun u => by
        rw [← hw, RingHom.id_apply, hbal, hbal, ← map_smul, hw] }
  have ha : ∀ g u v, B (g u) v = B u (a g v) := fun g u v => hw g v u
  have hinv : ∀ g g' : P →ₗ[R] P, (∀ u, g (g' u) = u) → a g' ∘ₗ a g = LinearMap.id := fun g g' h => by
    ext v
    refine hnd _ _ fun u => ?_
    rw [LinearMap.comp_apply, ← ha, ← ha, h, LinearMap.id_apply]
  let adj : (P ≃ₗ[R] P) → (Q ≃ₗ[R] Q) := fun g =>
    LinearEquiv.ofLinear (a g) (a g.symm) (hinv _ _ fun u => g.symm_apply_apply u)
      (hinv _ _ fun u => g.apply_symm_apply u)
  have hadj : ∀ (g : P ≃ₗ[R] P) u v, B (g u) v = B u (adj g v) := fun g u v => ha g u v
  refine ⟨adj, fun g g' => ?_, fun k g => ⟨fun h => ?_, fun h => h ▸ hadj g⟩⟩
  · ext v
    refine hnd _ _ fun u => ?_
    rw [← hadj, LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← hadj, ← hadj]
  · ext v
    exact hnd _ _ fun u => by rw [← h, hadj]

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

/- English proof (translation)
Establish `h : ∃ c, c ∈ I.map (H.bar : 𝓞 E →+* 𝓞 E) ∧ c - 1 ∈ I`. Take `⟨m, hm, mb, hmb, hsum⟩` from `Submodule.mem_sup.1 (hI ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ I ⊔ _)`. Use `⟨mb, hmb, ?_⟩` and prove the remaining obligations. Establish `: mb - 1 = -m` using `by rw [← hsum]; ring`. Rewrite using `[this]`.

Conclude with `neg_mem hm`. Unfold `cHalf`. Rewrite using `[dif_pos h]`. Conclude with `h.choose_spec`.
-/
theorem cHalf_spec (I : Ideal (𝓞 E)) (hI : I ⊔ I.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤) :
    cHalf H I ∈ I.map (H.bar : 𝓞 E →+* 𝓞 E) ∧ cHalf H I - 1 ∈ I := by
  have h : ∃ c, c ∈ I.map (H.bar : 𝓞 E →+* 𝓞 E) ∧ c - 1 ∈ I := by
    obtain ⟨m, hm, mb, hmb, hsum⟩ := Submodule.mem_sup.1 (hI ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ I ⊔ _)
    refine ⟨mb, hmb, ?_⟩
    have : mb - 1 = -m := by rw [← hsum]; ring
    rw [this]; exact neg_mem hm
  unfold cHalf
  rw [dif_pos h]
  exact h.choose_spec

/- English proof (translation)
Take `⟨b, hb, rfl⟩` from `(Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective).1 ha`. Establish `: H.bar ((H.bar : 𝓞 E →+* 𝓞 E) b) = b` using `LevelPairing.bar_bar H b`. Rewrite using `[this]` and apply the resulting hypothesis.
-/
theorem bar_mem {I : Ideal (𝓞 E)} {a : 𝓞 E} (ha : a ∈ I.map (H.bar : 𝓞 E →+* 𝓞 E)) : H.bar a ∈ I := by
  obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective).1 ha
  have : H.bar ((H.bar : 𝓞 E →+* 𝓞 E) b) = b := LevelPairing.bar_bar H b
  rwa [this]

/- English proof (translation)
Use `Dw.alt (x + y)` as an intermediate fact. Simplify using `only [map_add, LinearMap.add_apply, Dw.alt] at this`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ef_swap (x y : Dw.La) : Dw.EF y x = -Dw.EF x y := by
  have := Dw.alt (x + y)
  simp only [map_add, LinearMap.add_apply, Dw.alt] at this
  linarith

/- English proof (translation)
Take `⟨b, rfl⟩` from `Ideal.mem_span_singleton'.1 ha`. Establish `: (b * (N : 𝓞 E)) • y = (N : ℤ) • (b • y)`. Rewrite using `[mul_comm, mul_smul, ← Int.cast_smul_eq_zsmul (𝓞 E)]`. Simplify using the standard rewrite rules. Rewrite using `[this, map_zsmul]`.

Conclude with `Dvd.intro _ rfl`.
-/
theorem dvd_of_mem (N : ℕ) (x y : Dw.La) {a : 𝓞 E} (ha : a ∈ Ideal.span {(N : 𝓞 E)}) :
    (N : ℤ) ∣ Dw.EF x (a • y) := by
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  have : (b * (N : 𝓞 E)) • y = (N : ℤ) • (b • y) := by
    rw [mul_comm, mul_smul, ← Int.cast_smul_eq_zsmul (𝓞 E)]; simp
  rw [this, map_zsmul]
  exact Dvd.intro _ rfl

/- English proof (translation)
The claim follows from `Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)`.
-/
theorem qRep_mk {K : Submodule (𝓞 E) Dw.La} (q : Dw.La ⧸ K) : Submodule.Quotient.mk (qRep q) = q :=
  Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)

/- English proof (translation)
Take `⟨hc, hc1⟩` from `cHalf_spec I hI`. Use `set c := cHalf H I with hcdef`. Establish `hmul : ∀ a ∈ I, a * c ∈ Ideal.span {(N : 𝓞 E)}` using `fun a ha => hp ▸ Ideal.mul_mem_mul ha hc`. Establish `hright : ∀ x, ∀ y ∈ KI, (N : ℤ) ∣ Dw.EF x (c • y)`. Introduce `x y hy`.

Rewrite `hy` using `[hKI]`. Use `Submodule.smul_induction_on hy (fun a ha z _ => ?_) (fun u v hu hv => ?_)` and prove the remaining obligations. Rewrite using `[← mul_smul, mul_comm]`. Conclude with `dvd_of_mem _ _ _ (hmul a ha)`. Rewrite using `[smul_add, map_add]`.

Conclude with `dvd_add hu hv`. Establish `hleft : ∀ x ∈ KJ, ∀ y, (N : ℤ) ∣ Dw.EF x (c • y)`. Introduce `x hx y`. Rewrite `hx` using `[hKJ]`. Use `Submodule.smul_induction_on hx (fun a ha z _ => ?_) (fun u v hu hv => ?_)` and prove the remaining obligations.

Rewrite using `[Dw.adj, ← mul_smul]`. Conclude with `dvd_of_mem _ _ _ (hmul _ (bar_mem ha))`. Rewrite using `[map_add, LinearMap.add_apply]`. Conclude with `dvd_add hu hv`. Set `B : (Dw.La ⧸ KJ) → (Dw.La ⧸ KI) → ZMod N` to `fun p q => ((Dw.EF (qRep p) (c • qRep q) : ℤ) : ZMod N)`.

Establish `hB : ∀ u v, B (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) = ((Dw.EF u (c • v) : ℤ) : ZMod N)`. Introduce `u v`. Rewrite using `[eq_comm, ZMod.intCast_eq_intCast_iff_dvd_sub]`. Establish `h1` using `(Submodule.Quotient.eq _).1 (qRep_mk (Submodule.Quotient.mk u : Dw.La ⧸ KJ))`. Establish `h2` using `(Submodule.Quotient.eq _).1 (qRep_mk (Submodule.Quotient.mk v : Dw.La ⧸ KI))`.

Establish `h3` using `dvd_add (hleft _ h1 (qRep (Submodule.Quotient.mk v : Dw.La ⧸ KI))) (hright u _ h2)`. Rewrite `h3` using `[map_sub, LinearMap.sub_apply, smul_sub, map_sub, sub_add_sub_cancel]`. Then use the resulting hypothesis. Establish `haddr : ∀ u v w, B u (v + w) = B u v + B u w`. Introduce `u v w`. Take `⟨u, rfl⟩` from `Submodule.Quotient.mk_surjective _ u`.

Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ v`. Take `⟨w, rfl⟩` from `Submodule.Quotient.mk_surjective _ w`. Rewrite using `[← Submodule.Quotient.mk_add, hB, hB, hB, smul_add, map_add, Int.cast_add]`. Establish `haddl : ∀ u u' v, B (u + u') v = B u v + B u' v`. Introduce `u v w`.

Take `⟨u, rfl⟩` from `Submodule.Quotient.mk_surjective _ u`. Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ v`. Take `⟨w, rfl⟩` from `Submodule.Quotient.mk_surjective _ w`. Rewrite using `[← Submodule.Quotient.mk_add, hB, hB, hB, map_add, LinearMap.add_apply, Int.cast_add]`. Establish `hbal : ∀ (a : 𝓞 E) u v, B u (a • v) = B (H.bar a • u) v`.

Introduce `a u v`. Take `⟨u, rfl⟩` from `Submodule.Quotient.mk_surjective _ u`. Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ v`. Rewrite using `[← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, hB, hB, Dw.adj, LevelPairing.bar_bar, smul_comm]`. Establish `hNI : (N : 𝓞 E) ∈ I`.

Establish `: Ideal.span {(N : 𝓞 E)} ≤ I` using `hp ▸ Ideal.mul_le_left`. Conclude with `this (Ideal.subset_span rfl)`. Establish `hnd : ∀ v w, (∀ u, B u v = B u w) → v = w`. Introduce `v w h`. Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ v`.

Take `⟨w, rfl⟩` from `Submodule.Quotient.mk_surjective _ w`. Rewrite using `[eq_comm, Submodule.Quotient.eq, hKI]`. Take `⟨z, hz⟩` from `LevelPairing.exists_eq_smul_of_dvd (c • (w - v)) N hN (fun y => by`. Use `h (Submodule.Quotient.mk y)` as an intermediate fact. Rewrite `this` using `[hB, hB, ZMod.intCast_eq_intCast_iff_dvd_sub]`.

Rewrite using `[ef_swap, dvd_neg, smul_sub, map_sub]`. Conclude with `this)`. Establish `: w - v = (N : 𝓞 E) • z - (c - 1) • (w - v)`. Rewrite using `[sub_smul, one_smul, hz, ← Int.cast_smul_eq_zsmul (𝓞 E)]`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Conclude with `sub_mem (Submodule.smul_mem_smul hNI trivial) (Submodule.smul_mem_smul hc1 trivial)`. Establish `hrep : ∀ (g : (Dw.La ⧸ KJ) →ₗ[𝓞 E] (Dw.La ⧸ KJ)) (v : Dw.La ⧸ KI), ∃ w, ∀ u, B (g u) v = B u w`. Introduce `g v`. Use `haveI := Dw.proj`.

Use `haveI : Module.Projective ℤ Dw.La := by haveI := Dw.fin`. Take `⟨m, p, s, -, -, hps⟩` from `Module.Finite.exists_comp_eq_id_of_projective (𝓞 E) Dw.La`. Conclude with `Module.Projective.of_split (s.restrictScalars ℤ) (p.restrictScalars ℤ) (LinearMap.ext fun x => LinearMap.congr_fun hps x)`. Set `f : Dw.La →+ ZMod N` to `AddMonoidHom.mk' (fun u => B (g (Submodule.Quotient.mk u)) v) (fun u u' => by`. Simplify using `only [Submodule.Quotient.mk_add, map_add, haddl])`.

Take `⟨F, hF⟩` from `Module.projective_lifting_property (Int.castAddHom (ZMod N)).toIntLinearMap f.toIntLinearMap (ZMod.intCast_surjective)`. Take `⟨w, hw⟩` from `Dw.unimod.2 F`. Establish `hF' : ∀ u, ((Dw.EF w u : ℤ) : ZMod N) = f u` using `fun u => by`. Rewrite using `[hw]`. Conclude with `LinearMap.congr_fun hF u`.

Use `⟨Submodule.Quotient.mk (-w), fun u => ?_⟩` and prove the remaining obligations. Take `⟨u, rfl⟩` from `Submodule.Quotient.mk_surjective _ u`. Establish `h0 : f (H.bar (c - 1) • u) = 0`. Establish `: (Submodule.Quotient.mk (H.bar (c - 1) • u) : Dw.La ⧸ KJ) = 0`. Rewrite using `[Submodule.Quotient.mk_eq_zero, hKJ]`.

Conclude with `Submodule.smul_mem_smul (Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hc1) trivial`. Express the relevant statement in the definitionally equal form `B (g (Submodule.Quotient.mk _)) v = 0`. Rewrite using `[this, map_zero]`. Use `haddl 0 0 v` as an intermediate fact. Rewrite `this` using `[add_zero]`.

Conclude with `left_eq_add.1 this`. Express the relevant statement in the definitionally equal form `f u = _`. Establish `h1 : Dw.EF u (c • -w) = Dw.EF w (H.bar (c - 1) • u) + Dw.EF w u`. Rewrite using `[← Dw.adj, ef_swap, sub_smul, one_smul, smul_neg, map_neg, map_sub]`. Simplify using the standard rewrite rules.

Rewrite using `[hB, h1, Int.cast_add, hF', hF', h0, zero_add]`. Take `⟨adj, h1, h2⟩` from `exists_adjoint (fun a => H.bar a) B haddr hbal hnd hrep`. Use `⟨adj, h1, fun k g => ?_⟩` and prove the remaining obligations. Rewrite using `[← h2]`. Establish `key : ∀ u v : Dw.La, ((N : ℤ) ∣ Dw.EF (qRep (g (Submodule.Quotient.mk u))) (c • v) - Dw.EF u (c • qRep (k (Submodule.Quotient.mk v)))) ↔ B (g (Submodule.Quotient.mk u)) (Submodule.Quotient.mk v) = B (Submodule.Quotient.mk u) (k (Submodule.Quotient.mk v))`.

Introduce `u v`. Rewrite using `[← ZMod.intCast_eq_intCast_iff_dvd_sub, ← hB, ← hB, qRep_mk, qRep_mk, eq_comm]`. Prove the components needed by the constructor for the conclusion. Introduce `h u v`. Take `⟨u, rfl⟩` from `Submodule.Quotient.mk_surjective _ u`.

Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ v`. Conclude with `(key u v).1 (h u v)`. Introduce `h u v`. Conclude with `(key u v).2 (h _ _)`.
-/
theorem exists_adjoint_halves (N : ℕ) (hN : N ≠ 0) (I : Ideal (𝓞 E))
    (hp : I * I.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(N : 𝓞 E)})
    (hI : I ⊔ I.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤) (KJ KI : Submodule (𝓞 E) Dw.La)
    (hKJ : KJ = I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤) (hKI : KI = I • ⊤) :
    ∃ adj : ((Dw.La ⧸ KJ) ≃ₗ[𝓞 E] (Dw.La ⧸ KJ)) → ((Dw.La ⧸ KI) ≃ₗ[𝓞 E] (Dw.La ⧸ KI)),
      (∀ g g', adj (g * g') = adj g' * adj g) ∧
      ∀ (k : (Dw.La ⧸ KI) ≃ₗ[𝓞 E] (Dw.La ⧸ KI)) (kst : (Dw.La ⧸ KJ) ≃ₗ[𝓞 E] (Dw.La ⧸ KJ)),
        (∀ u v : Dw.La, ((N : ℤ) ∣ Dw.EF (qRep (kst (Submodule.Quotient.mk u))) (cHalf H I • v) -
          Dw.EF u (cHalf H I • qRep (k (Submodule.Quotient.mk v))))) ↔ k = adj kst := by
  obtain ⟨hc, hc1⟩ := cHalf_spec I hI
  set c := cHalf H I with hcdef
  have hmul : ∀ a ∈ I, a * c ∈ Ideal.span {(N : 𝓞 E)} := fun a ha => hp ▸ Ideal.mul_mem_mul ha hc
  have hright : ∀ x, ∀ y ∈ KI, (N : ℤ) ∣ Dw.EF x (c • y) := by
    intro x y hy
    rw [hKI] at hy
    refine Submodule.smul_induction_on hy (fun a ha z _ => ?_) (fun u v hu hv => ?_)
    · rw [← mul_smul, mul_comm]; exact dvd_of_mem _ _ _ (hmul a ha)
    · rw [smul_add, map_add]; exact dvd_add hu hv
  have hleft : ∀ x ∈ KJ, ∀ y, (N : ℤ) ∣ Dw.EF x (c • y) := by
    intro x hx y
    rw [hKJ] at hx
    refine Submodule.smul_induction_on hx (fun a ha z _ => ?_) (fun u v hu hv => ?_)
    · rw [Dw.adj, ← mul_smul]; exact dvd_of_mem _ _ _ (hmul _ (bar_mem ha))
    · rw [map_add, LinearMap.add_apply]; exact dvd_add hu hv
  let B : (Dw.La ⧸ KJ) → (Dw.La ⧸ KI) → ZMod N := fun p q => ((Dw.EF (qRep p) (c • qRep q) : ℤ) : ZMod N)
  have hB : ∀ u v, B (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) = ((Dw.EF u (c • v) : ℤ) : ZMod N) := by
    intro u v
    rw [eq_comm, ZMod.intCast_eq_intCast_iff_dvd_sub]
    have h1 := (Submodule.Quotient.eq _).1 (qRep_mk (Submodule.Quotient.mk u : Dw.La ⧸ KJ))
    have h2 := (Submodule.Quotient.eq _).1 (qRep_mk (Submodule.Quotient.mk v : Dw.La ⧸ KI))
    have h3 := dvd_add (hleft _ h1 (qRep (Submodule.Quotient.mk v : Dw.La ⧸ KI))) (hright u _ h2)
    rwa [map_sub, LinearMap.sub_apply, smul_sub, map_sub, sub_add_sub_cancel] at h3
  have haddr : ∀ u v w, B u (v + w) = B u v + B u w := by
    intro u v w
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [← Submodule.Quotient.mk_add, hB, hB, hB, smul_add, map_add, Int.cast_add]
  have haddl : ∀ u u' v, B (u + u') v = B u v + B u' v := by
    intro u v w
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [← Submodule.Quotient.mk_add, hB, hB, hB, map_add, LinearMap.add_apply, Int.cast_add]
  have hbal : ∀ (a : 𝓞 E) u v, B u (a • v) = B (H.bar a • u) v := by
    intro a u v
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, hB, hB, Dw.adj, LevelPairing.bar_bar,
      smul_comm]
  have hNI : (N : 𝓞 E) ∈ I := by
    have : Ideal.span {(N : 𝓞 E)} ≤ I := hp ▸ Ideal.mul_le_left
    exact this (Ideal.subset_span rfl)
  have hnd : ∀ v w, (∀ u, B u v = B u w) → v = w := by
    intro v w h
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [eq_comm, Submodule.Quotient.eq, hKI]
    obtain ⟨z, hz⟩ := LevelPairing.exists_eq_smul_of_dvd (c • (w - v)) N hN (fun y => by
      have := h (Submodule.Quotient.mk y)
      rw [hB, hB, ZMod.intCast_eq_intCast_iff_dvd_sub] at this
      rw [ef_swap, dvd_neg, smul_sub, map_sub]
      exact this)
    have : w - v = (N : 𝓞 E) • z - (c - 1) • (w - v) := by
      rw [sub_smul, one_smul, hz, ← Int.cast_smul_eq_zsmul (𝓞 E)]; simp
    rw [this]
    exact sub_mem (Submodule.smul_mem_smul hNI trivial) (Submodule.smul_mem_smul hc1 trivial)
  have hrep : ∀ (g : (Dw.La ⧸ KJ) →ₗ[𝓞 E] (Dw.La ⧸ KJ)) (v : Dw.La ⧸ KI), ∃ w, ∀ u, B (g u) v = B u w := by
    intro g v
    haveI := Dw.proj
    haveI : Module.Projective ℤ Dw.La := by
      haveI := Dw.fin
      obtain ⟨m, p, s, -, -, hps⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 E) Dw.La
      exact Module.Projective.of_split (s.restrictScalars ℤ) (p.restrictScalars ℤ)
        (LinearMap.ext fun x => LinearMap.congr_fun hps x)
    let f : Dw.La →+ ZMod N := AddMonoidHom.mk' (fun u => B (g (Submodule.Quotient.mk u)) v) (fun u u' => by
      simp only [Submodule.Quotient.mk_add, map_add, haddl])
    obtain ⟨F, hF⟩ := Module.projective_lifting_property (Int.castAddHom (ZMod N)).toIntLinearMap f.toIntLinearMap
      (ZMod.intCast_surjective)
    obtain ⟨w, hw⟩ := Dw.unimod.2 F
    have hF' : ∀ u, ((Dw.EF w u : ℤ) : ZMod N) = f u := fun u => by
      rw [hw]; exact LinearMap.congr_fun hF u
    refine ⟨Submodule.Quotient.mk (-w), fun u => ?_⟩
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    have h0 : f (H.bar (c - 1) • u) = 0 := by
      have : (Submodule.Quotient.mk (H.bar (c - 1) • u) : Dw.La ⧸ KJ) = 0 := by
        rw [Submodule.Quotient.mk_eq_zero, hKJ]
        exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hc1) trivial
      change B (g (Submodule.Quotient.mk _)) v = 0
      rw [this, map_zero]
      have := haddl 0 0 v
      rw [add_zero] at this
      exact left_eq_add.1 this
    change f u = _
    have h1 : Dw.EF u (c • -w) = Dw.EF w (H.bar (c - 1) • u) + Dw.EF w u := by
      rw [← Dw.adj, ef_swap, sub_smul, one_smul, smul_neg, map_neg, map_sub]
      simp
    rw [hB, h1, Int.cast_add, hF', hF', h0, zero_add]
  obtain ⟨adj, h1, h2⟩ := exists_adjoint (fun a => H.bar a) B haddr hbal hnd hrep
  refine ⟨adj, h1, fun k g => ?_⟩
  rw [← h2]
  have key : ∀ u v : Dw.La, ((N : ℤ) ∣ Dw.EF (qRep (g (Submodule.Quotient.mk u))) (c • v) -
      Dw.EF u (c • qRep (k (Submodule.Quotient.mk v)))) ↔
      B (g (Submodule.Quotient.mk u)) (Submodule.Quotient.mk v) =
        B (Submodule.Quotient.mk u) (k (Submodule.Quotient.mk v)) := by
    intro u v
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, ← hB, ← hB, qRep_mk, qRep_mk, eq_comm]
  constructor
  · intro h u v
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    exact (key u v).1 (h u v)
  · intro h u v
    exact (key u v).2 (h _ _)

end

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c n d hd`. Take `⟨-, hM, -, hMb, hI, -⟩` from `hd`. Establish `hN : d.pd ≠ 0`. Introduce `h`. Use `d.l₂.three_le` as an intermediate fact.

Rewrite `this` using `[hM, h]`. Use linear arithmetic over natural numbers and integers. Establish `hM0 : l.M ≠ 0` using `by have := l.three_le; omega`. Establish `hp : d.I * d.I.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(d.pd : 𝓞 E)}`. Establish `h2` using `d.l₂.prod`.

Rewrite `h2` using `[hMb, hM, Ideal.map_mul, mul_mul_mul_comm, l.prod, Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton]`. Use `mul_left_cancel₀ ?_ h2` and prove the remaining obligations. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hM0` after adjusting the coercions. Establish `hb : d.I.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ ⊥`.

Introduce `h`. Rewrite `hp` using `[h, Ideal.mul_bot, eq_comm, Ideal.span_singleton_eq_bot]`. Conclude with `hN (by exact_mod_cast hp)`. Use `haveI : Finite (𝓞 E ⧸ d.I.map (H.bar : 𝓞 E →+* 𝓞 E)) := Ideal.finiteQuotientOfFreeOfNeBot _ hb`. Use `haveI := Dw.fin`.

Use `haveI := Dw.proj`. Take `⟨e⟩` from `nonempty_equiv_quot (N := Dw.La) (d.I.map (H.bar : 𝓞 E →+* 𝓞 E)) _ Dw.rank`. Conclude with `⟨exists_span _ _ e, fun x x' => existsUnique_equiv _ _ e x x', exists_adjoint_halves d.pd hN d.I hp hI _ _ rfl rfl⟩`.
-/
theorem halves_free_and_adjoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → (∃ x₀ : Fin (Dw.p + Dw.q) → LaJ Xo c d, Submodule.span (𝓞 E) (Set.range x₀) = ⊤) ∧ (∀ x x' : Fin (Dw.p + Dw.q) → LaJ Xo c d, Submodule.span (𝓞 E) (Set.range x) = ⊤ → Submodule.span (𝓞 E) (Set.range x') = ⊤ → ∃! g : LaJ Xo c d ≃ₗ[𝓞 E] LaJ Xo c d, ∀ b, g (x b) = x' b) ∧ ∃ adj : (LaJ Xo c d ≃ₗ[𝓞 E] LaJ Xo c d) → (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d), (∀ g g', adj (g * g') = adj g' * adj g) ∧ ∀ (k : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) (kst : LaJ Xo c d ≃ₗ[𝓞 E] LaJ Xo c d), (∀ u v : Dw.La, ((d.pd : ℤ) ∣ Dw.EF (qRep (kst (Submodule.Quotient.mk u))) (cHalf H d.I • v) - Dw.EF u (cHalf H d.I • qRep (k (Submodule.Quotient.mk v))))) ↔ k = adj kst := by
  intro E _ _ _ H Dw l Xo c n d hd
  obtain ⟨-, hM, -, hMb, hI, -⟩ := hd
  have hN : d.pd ≠ 0 := by
    intro h
    have := d.l₂.three_le
    rw [hM, h] at this
    omega
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  have hp : d.I * d.I.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(d.pd : 𝓞 E)} := by
    have h2 := d.l₂.prod
    rw [hMb, hM, Ideal.map_mul, mul_mul_mul_comm, l.prod, Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton] at h2
    refine mul_left_cancel₀ ?_ h2
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hM0
  have hb : d.I.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ ⊥ := by
    intro h
    rw [h, Ideal.mul_bot, eq_comm, Ideal.span_singleton_eq_bot] at hp
    exact hN (by exact_mod_cast hp)
  haveI : Finite (𝓞 E ⧸ d.I.map (H.bar : 𝓞 E →+* 𝓞 E)) := Ideal.finiteQuotientOfFreeOfNeBot _ hb
  haveI := Dw.fin
  haveI := Dw.proj
  obtain ⟨e⟩ := nonempty_equiv_quot (N := Dw.La) (d.I.map (H.bar : 𝓞 E →+* 𝓞 E)) _ Dw.rank
  exact ⟨exists_span _ _ e, fun x x' => existsUnique_equiv _ _ e x x',
    exists_adjoint_halves d.pd hN d.I hp hI _ _ rfl rfl⟩

end GlobalTheory.HalfPairing
