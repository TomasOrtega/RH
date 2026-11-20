import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsHolomorphicFamily

namespace GlobalTheory.HolArc

/- English proof (translation)
Set `K` to `FractionRing S`. Set `L` to `FractionRing R`. Use `letI : Algebra K L := FractionRing.liftAlgebra S L`. Use `haveI : IsScalarTower S K L := FractionRing.isScalarTower_liftAlgebra S L`. Use `haveI : Algebra.FormallyEtale R L := .of_isLocalization (nonZeroDivisors _)`.

Use `haveI : Algebra.FormallyUnramified S L := Algebra.FormallyUnramified.comp S R L`. Use `haveI : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.of_restrictScalars S K L`. Use `haveI : Algebra.EssFiniteType R L := .of_isLocalization L (nonZeroDivisors _)`. Use `haveI : Algebra.EssFiniteType S L := Algebra.EssFiniteType.comp S R L`. Use `haveI : Algebra.EssFiniteType K L := Algebra.EssFiniteType.of_comp S K L`.

Use `haveI : Algebra.IsSeparable K L := Algebra.FormallyUnramified.isSeparable K L`. Use `haveI : Algebra.IsAlgebraic K L := inferInstance`. Use `haveI : Algebra.IsAlgebraic S L := (IsFractionRing.comap_isAlgebraic_iff (A := S) (K := K)).2 inferInstance`. Conclude with `Algebra.IsAlgebraic.of_injective (IsScalarTower.toAlgHom S R L) (IsFractionRing.injective R L)`.
-/
theorem isAlgebraic_of_etale (S R : Type) [CommRing S] [IsDomain S] [CommRing R] [IsDomain R]
    [Algebra S R] [Algebra.Etale S R] [FaithfulSMul S R] : Algebra.IsAlgebraic S R := by
  let K := FractionRing S
  let L := FractionRing R
  letI : Algebra K L := FractionRing.liftAlgebra S L
  haveI : IsScalarTower S K L := FractionRing.isScalarTower_liftAlgebra S L
  haveI : Algebra.FormallyEtale R L := .of_isLocalization (nonZeroDivisors _)
  haveI : Algebra.FormallyUnramified S L := Algebra.FormallyUnramified.comp S R L
  haveI : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.of_restrictScalars S K L
  haveI : Algebra.EssFiniteType R L := .of_isLocalization L (nonZeroDivisors _)
  haveI : Algebra.EssFiniteType S L := Algebra.EssFiniteType.comp S R L
  haveI : Algebra.EssFiniteType K L := Algebra.EssFiniteType.of_comp S K L
  haveI : Algebra.IsSeparable K L := Algebra.FormallyUnramified.isSeparable K L
  haveI : Algebra.IsAlgebraic K L := inferInstance
  haveI : Algebra.IsAlgebraic S L := (IsFractionRing.comap_isAlgebraic_iff (A := S) (K := K)).2 inferInstance
  exact Algebra.IsAlgebraic.of_injective (IsScalarTower.toAlgHom S R L)
    (IsFractionRing.injective R L)

/- English proof (translation)
Rewrite using `[faithfulSMul_iff_algebraMap_injective, injective_iff_map_eq_zero]`. Introduce `a ha`. Assume the negation of the conclusion as `h`. Establish `hreg : IsSMulRegular R a` using `Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero h)`. Establish `: a • (1 : R) = a • (0 : R)` using `by simp [Algebra.smul_def, ha]`.

Conclude with `one_ne_zero (hreg this)`.
-/
theorem faithfulSMul_of_flat (S R : Type) [CommRing S] [IsDomain S] [CommRing R] [IsDomain R]
    [Algebra S R] [Module.Flat S R] : FaithfulSMul S R := by
  rw [faithfulSMul_iff_algebraMap_injective, injective_iff_map_eq_zero]
  intro a ha
  by_contra h
  have hreg : IsSMulRegular R a :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero h)
  have : a • (1 : R) = a • (0 : R) := by simp [Algebra.smul_def, ha]
  exact one_ne_zero (hreg this)

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨w, hw⟩ : ∃ w, MvPolynomial.eval w q ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hq (MvPolynomial.funext fun x => by simpa using h x)`. Set `v` to `w - b₀`.

Set `Q : Polynomial ℂ` to `MvPolynomial.aeval (fun i => Polynomial.C (b₀ i) + Polynomial.X * Polynomial.C (v i)) q`. Establish `hQ : ∀ u, Q.eval u = MvPolynomial.eval (b₀ + u • v) q` using `fun u => by`. Establish `: (Polynomial.evalRingHom u).comp (MvPolynomial.aeval (R` using `ℂ) (fun i => Polynomial.C (b₀ i) + Polynomial.X * Polynomial.C (v i)) : MvPolynomial (Fin m) ℂ →ₐ[ℂ] Polynomial ℂ).toRingHom = MvPolynomial.eval (b₀ + u • v) := by`. Apply the tactic sequence `refine MvPolynomial.ringHom_ext (fun a => ?_) fun i => ?_ <;> simp <;> ring`. Conclude with `congrArg (fun f : MvPolynomial (Fin m) ℂ →+* ℂ => f q) this`.

Establish `hQ0 : Q ≠ 0` using `fun h => hw (by`. Use `hQ 1` as an intermediate fact. Simplify `this.symm)` using `[h, v]`. Establish `hfin : (((Q.roots.toFinset.erase 0 : Finset ℂ) : Set ℂ))ᶜ ∈ nhds (0 : ℂ)` using `(Finset.finite_toSet _).isClosed.isOpen_compl.mem_nhds (by simp)`. Take `⟨ρ, hρ, hb⟩` from `Metric.mem_nhds_iff.1 hfin`.

Use `⟨v, ρ, hρ, fun u hu hu0 h => hb hu ?_⟩` and prove the remaining obligations. Simplify using `only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Multiset.mem_toFinset, Set.mem_singleton_iff, Polynomial.mem_roots hQ0, Polynomial.IsRoot.def, hQ, h]`. Simplify using `using hu0`.
-/
theorem exists_line (m : ℕ) (q : MvPolynomial (Fin m) ℂ) (hq : q ≠ 0) (b₀ : Fin m → ℂ) :
    ∃ (v : Fin m → ℂ) (ρ : ℝ), 0 < ρ ∧
      ∀ u ∈ Metric.ball (0 : ℂ) ρ, u ≠ 0 → MvPolynomial.eval (b₀ + u • v) q ≠ 0 := by
  obtain ⟨w, hw⟩ : ∃ w, MvPolynomial.eval w q ≠ 0 := by
    by_contra h
    push_neg at h
    exact hq (MvPolynomial.funext fun x => by simpa using h x)
  let v := w - b₀
  let Q : Polynomial ℂ := MvPolynomial.aeval
    (fun i => Polynomial.C (b₀ i) + Polynomial.X * Polynomial.C (v i)) q
  have hQ : ∀ u, Q.eval u = MvPolynomial.eval (b₀ + u • v) q := fun u => by
    have : (Polynomial.evalRingHom u).comp
        (MvPolynomial.aeval (R := ℂ) (fun i => Polynomial.C (b₀ i) + Polynomial.X * Polynomial.C (v i)) :
          MvPolynomial (Fin m) ℂ →ₐ[ℂ] Polynomial ℂ).toRingHom =
        MvPolynomial.eval (b₀ + u • v) := by
      refine MvPolynomial.ringHom_ext (fun a => ?_) fun i => ?_ <;> simp <;> ring
    exact congrArg (fun f : MvPolynomial (Fin m) ℂ →+* ℂ => f q) this
  have hQ0 : Q ≠ 0 := fun h => hw (by
    have := hQ 1
    simpa [h, v] using this.symm)
  have hfin : (((Q.roots.toFinset.erase 0 : Finset ℂ) : Set ℂ))ᶜ ∈ nhds (0 : ℂ) :=
    (Finset.finite_toSet _).isClosed.isOpen_compl.mem_nhds (by simp)
  obtain ⟨ρ, hρ, hb⟩ := Metric.mem_nhds_iff.1 hfin
  refine ⟨v, ρ, hρ, fun u hu hu0 h => hb hu ?_⟩
  simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Multiset.mem_toFinset,
    Set.mem_singleton_iff, Polynomial.mem_roots hQ0, Polynomial.IsRoot.def, hQ, h]
  simpa using hu0

end GlobalTheory.HolArc

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.HolArc

/- English proof (translation)
Introduce `F A _ _ _ _ hS ψ₀ p hp`. Use `haveI := hS`. Use `haveI : (RingHom.ker ψ₀).IsPrime := RingHom.ker_isPrime ψ₀`. Take `⟨g, m, s, hg, het⟩` from `SmoothPointFamily.exists_etale_away (R := F) (RingHom.ker ψ₀)`. Establish `hg₀ : ψ₀ g ≠ 0` using `hg`.

Establish `hgne : g ≠ 0` using `fun h => hg₀ (by simp [h])`. Set `σ : F →+* ℂ` to `ψ₀.comp (algebraMap F A)`. Set `R` to `Localization.Away g`. Set `ι : A →+* R` to `algebraMap A R`. Establish `hle : Submonoid.powers g ≤ nonZeroDivisors A` using `powers_le_nonZeroDivisors_of_noZeroDivisors hgne`.

Use `haveI : IsDomain R := IsLocalization.isDomain_localization hle`. Establish `hι : Function.Injective ι` using `IsLocalization.injective R hle`. Set `e : R →+* ℂ` to `IsLocalization.Away.lift g (g := ψ₀) (isUnit_iff_ne_zero.2 hg₀)`. Establish `he : ∀ a, e (ι a) = ψ₀ a` using `fun a => IsLocalization.Away.lift_eq g _ a`. Set `P : MvPolynomial (Fin m) F →+* R` to `MvPolynomial.eval₂Hom (algebraMap F R) fun i => ι (s i)`.

Establish `hPC : ∀ k, P (MvPolynomial.C k) = ι (algebraMap F A k)` using `fun k => by`. Simplify using `only [P, MvPolynomial.eval₂Hom_C]`. Conclude with `IsScalarTower.algebraMap_apply F A R k`. Establish `hPX : ∀ i, P (MvPolynomial.X i) = ι (s i)` using `fun i => by simp [P]`. Establish `heC : ∀ k, e (P (MvPolynomial.C k)) = σ k` using `fun k => by rw [hPC, he]; rfl`.

Choose the witnesses or unpack the hypotheses as in `⟨c, hc0, hc⟩ : ∃ c : MvPolynomial (Fin m) F, c ≠ 0 ∧ ι p ∣ P c := by`. Use `letI : Algebra (MvPolynomial (Fin m) F) R := P.toAlgebra`. Use `haveI : Algebra.Etale (MvPolynomial (Fin m) F) R := het`. Use `haveI : FaithfulSMul (MvPolynomial (Fin m) F) R := faithfulSMul_of_flat _ _`. Use `haveI := isAlgebraic_of_etale (MvPolynomial (Fin m) F) R`.

Conclude with `(Algebra.IsAlgebraic.isAlgebraic (ι p)).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff ι hι).2 hp))`. Take `⟨N, τ, n, f, O, hN, hO, hO₀, hd, hτ, hrec⟩` from `GlobalTheory.EtaleFamily.exists_holomorphic_sections 0 m F R P Set.univ (fun _ => σ) 0 e het isOpen_univ trivial (fun a => differentiableOn_const _) heC`. Take `⟨h3, h4⟩` from `hrec 0 e heC hO₀`. Simplify using `only [hPX, he] at h3 h4`. Set `b₀ : Fin m → ℂ` to `fun i => ψ₀ (s i)`.

Establish `hq0 : MvPolynomial.map σ c ≠ 0` using `(map_ne_zero_iff _ (MvPolynomial.map_injective σ σ.injective)).2 hc0`. Take `⟨v, ρ, hρ, hline⟩` from `exists_line m (MvPolynomial.map σ c) hq0 b₀`. Set `ℓ : ℂ → (Fin 0 → ℂ) × (Fin m → ℂ)` to `fun u => (0, b₀ + u • v)`. Establish `hℓd : Differentiable ℂ ℓ` using `(differentiable_const _).prodMk ((differentiable_const _).add (differentiable_id.smul_const v))`. Establish `hℓ0 : ℓ 0 = (0, b₀)` using `by simp [ℓ]`.

Establish `hNo : ℓ ⁻¹' N ∈ 𝓝 (0 : ℂ)` using `(hN.preimage hℓd.continuous).mem_nhds (by simpa only [Set.mem_preimage, hℓ0] using h3)`. Take `⟨ρ', hρ', hb⟩` from `Metric.mem_nhds_iff.1 hNo`. Establish `hsub : ∀ u ∈ Metric.ball (0 : ℂ) (min ρ ρ'), ℓ u ∈ N` using `fun u hu => hb (Metric.ball_subset_ball (min_le_right _ _) hu)`. Use `⟨fun u => (τ (ℓ u)).comp ι, min ρ ρ', ⟨lt_min hρ hρ', fun a => ?_⟩, ?_, fun u hu => ?_, fun u hu hu0 h => ?_⟩` and prove the remaining obligations. Conclude with `(hd (ι a)).comp hℓd.differentiableOn hsub`.

Use `RingHom.ext fun a => ?_` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply, hℓ0]`. Rewrite using `[show ((0 : Fin 0 → ℂ), b₀) = (0, fun i => ψ₀ (s i)) from rfl, h4, he]`. Use `RingHom.ext fun k => ?_` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply]`.

Rewrite using `[← hPC]`. Conclude with `(hτ _ (hsub u hu)).2.1 k`. Establish `hev : (τ (ℓ u)).comp P = (MvPolynomial.eval (b₀ + u • v)).comp (MvPolynomial.map σ)`. Use `MvPolynomial.ringHom_ext (fun k => ?_) fun i => ?_` and prove the remaining obligations. Simplify using `using (hτ _ (hsub u hu)).2.1 k`.

Simplify `(hτ _ (hsub u hu)).2.2 i` using `[ℓ]`. Take `⟨d, hd'⟩` from `hc`. Establish `h0 : τ (ℓ u) (P c) = 0`. Rewrite using `[hd', map_mul]`. Conclude with `mul_eq_zero_of_left h _`.

Establish `h1` using `congrArg (fun f : MvPolynomial (Fin m) F →+* ℂ => f c) hev`. Simplify using `only [RingHom.comp_apply] at h1`. Conclude with `hline u (Metric.ball_subset_ball (min_le_left _ _) hu) hu0 (h1.symm.trans h0)`.
-/
theorem exists_holPts_ne_zero : ∀ (F A : Type) [Field F] [CommRing A] [IsDomain A] [Algebra F A], Algebra.Smooth F A → ∀ (ψ₀ : A →+* ℂ) (p : A), p ≠ 0 → ∃ (ψ : ℂ → (A →+* ℂ)) (r : ℝ), IsHolPts ψ r ∧ ψ 0 = ψ₀ ∧ (∀ u ∈ Metric.ball (0 : ℂ) r, (ψ u).comp (algebraMap F A) = ψ₀.comp (algebraMap F A)) ∧ ∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ψ u p ≠ 0 := by
  intro F A _ _ _ _ hS ψ₀ p hp
  haveI := hS
  haveI : (RingHom.ker ψ₀).IsPrime := RingHom.ker_isPrime ψ₀
  obtain ⟨g, m, s, hg, het⟩ := SmoothPointFamily.exists_etale_away (R := F) (RingHom.ker ψ₀)
  have hg₀ : ψ₀ g ≠ 0 := hg
  have hgne : g ≠ 0 := fun h => hg₀ (by simp [h])
  let σ : F →+* ℂ := ψ₀.comp (algebraMap F A)
  let R := Localization.Away g
  let ι : A →+* R := algebraMap A R
  have hle : Submonoid.powers g ≤ nonZeroDivisors A :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hgne
  haveI : IsDomain R := IsLocalization.isDomain_localization hle
  have hι : Function.Injective ι := IsLocalization.injective R hle
  let e : R →+* ℂ := IsLocalization.Away.lift g (g := ψ₀) (isUnit_iff_ne_zero.2 hg₀)
  have he : ∀ a, e (ι a) = ψ₀ a := fun a => IsLocalization.Away.lift_eq g _ a
  let P : MvPolynomial (Fin m) F →+* R := MvPolynomial.eval₂Hom (algebraMap F R) fun i => ι (s i)
  have hPC : ∀ k, P (MvPolynomial.C k) = ι (algebraMap F A k) := fun k => by
    simp only [P, MvPolynomial.eval₂Hom_C]
    exact IsScalarTower.algebraMap_apply F A R k
  have hPX : ∀ i, P (MvPolynomial.X i) = ι (s i) := fun i => by simp [P]
  have heC : ∀ k, e (P (MvPolynomial.C k)) = σ k := fun k => by rw [hPC, he]; rfl

  obtain ⟨c, hc0, hc⟩ : ∃ c : MvPolynomial (Fin m) F, c ≠ 0 ∧ ι p ∣ P c := by
    letI : Algebra (MvPolynomial (Fin m) F) R := P.toAlgebra
    haveI : Algebra.Etale (MvPolynomial (Fin m) F) R := het
    haveI : FaithfulSMul (MvPolynomial (Fin m) F) R := faithfulSMul_of_flat _ _
    haveI := isAlgebraic_of_etale (MvPolynomial (Fin m) F) R
    exact (Algebra.IsAlgebraic.isAlgebraic (ι p)).exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff ι hι).2 hp))
  obtain ⟨N, τ, n, f, O, hN, hO, hO₀, hd, hτ, hrec⟩ :=
    GlobalTheory.EtaleFamily.exists_holomorphic_sections 0 m F R P Set.univ (fun _ => σ) 0 e het
      isOpen_univ trivial (fun a => differentiableOn_const _) heC
  obtain ⟨h3, h4⟩ := hrec 0 e heC hO₀
  simp only [hPX, he] at h3 h4
  let b₀ : Fin m → ℂ := fun i => ψ₀ (s i)
  have hq0 : MvPolynomial.map σ c ≠ 0 :=
    (map_ne_zero_iff _ (MvPolynomial.map_injective σ σ.injective)).2 hc0
  obtain ⟨v, ρ, hρ, hline⟩ := exists_line m (MvPolynomial.map σ c) hq0 b₀
  let ℓ : ℂ → (Fin 0 → ℂ) × (Fin m → ℂ) := fun u => (0, b₀ + u • v)
  have hℓd : Differentiable ℂ ℓ :=
    (differentiable_const _).prodMk ((differentiable_const _).add (differentiable_id.smul_const v))
  have hℓ0 : ℓ 0 = (0, b₀) := by simp [ℓ]
  have hNo : ℓ ⁻¹' N ∈ 𝓝 (0 : ℂ) :=
    (hN.preimage hℓd.continuous).mem_nhds (by simpa only [Set.mem_preimage, hℓ0] using h3)
  obtain ⟨ρ', hρ', hb⟩ := Metric.mem_nhds_iff.1 hNo
  have hsub : ∀ u ∈ Metric.ball (0 : ℂ) (min ρ ρ'), ℓ u ∈ N := fun u hu =>
    hb (Metric.ball_subset_ball (min_le_right _ _) hu)
  refine ⟨fun u => (τ (ℓ u)).comp ι, min ρ ρ', ⟨lt_min hρ hρ', fun a => ?_⟩, ?_, fun u hu => ?_,
    fun u hu hu0 h => ?_⟩
  · exact (hd (ι a)).comp hℓd.differentiableOn hsub
  · refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply, hℓ0]
    rw [show ((0 : Fin 0 → ℂ), b₀) = (0, fun i => ψ₀ (s i)) from rfl, h4, he]
  · refine RingHom.ext fun k => ?_
    simp only [RingHom.comp_apply]
    rw [← hPC]
    exact (hτ _ (hsub u hu)).2.1 k
  · have hev : (τ (ℓ u)).comp P = (MvPolynomial.eval (b₀ + u • v)).comp (MvPolynomial.map σ) := by
      refine MvPolynomial.ringHom_ext (fun k => ?_) fun i => ?_
      · simpa using (hτ _ (hsub u hu)).2.1 k
      · simpa [ℓ] using (hτ _ (hsub u hu)).2.2 i
    obtain ⟨d, hd'⟩ := hc
    have h0 : τ (ℓ u) (P c) = 0 := by
      rw [hd', map_mul]
      exact mul_eq_zero_of_left h _
    have h1 := congrArg (fun f : MvPolynomial (Fin m) F →+* ℂ => f c) hev
    simp only [RingHom.comp_apply] at h1
    exact hline u (Metric.ball_subset_ball (min_le_left _ _) hu) hu0 (h1.symm.trans h0)

end GlobalTheory.HolArc
