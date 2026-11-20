import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RankPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.ObjDim

section Chart

open ReciprocityTheory.ChartRestriction.G.Chart

/- English proof (translation)
Take `⟨g, hgC, hg⟩` from `hB.exists_etale_mvPolynomial`. Use `letI : Algebra (MvPolynomial (Fin n) R) B := g.toAlgebra`. Use `haveI : IsScalarTower R (MvPolynomial (Fin n) R) B := IsScalarTower.of_algebraMap_eq' hgC.symm`. Use `haveI : Algebra.Etale (MvPolynomial (Fin n) R) B := hg`. Establish `hπ : ∀ m : ℕ, ∃ π : B →ₐ[R] JetR R (Fin n) m, (jetAug R (Fin n) m).comp π = ε' ∧ ∀ j, π (sX R j) = algebraMap R _ (ε' (sX R j)) + zR m j` using `fun m => etale_exists (n := n) ε' (jetAug R (Fin n) m) (ker_jetAug_nil (Fin n) m) _ (fun j => by`.

Rewrite using `[map_add, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, jetAug_zR, add_zero])`. Use `choose π hπaug hπX using hπ`. Use `⟨π, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `m`. Use `etale_ext (n := n) ε' (jetAug R (Fin n) m) (ker_jetAug_nil (Fin n) m) _ _ ?_ ?_ ?_` and prove the remaining obligations.

Rewrite using `[← AlgHom.comp_assoc, jetAug_comp_trunc]`. Conclude with `hπaug (m + 1)`. Conclude with `hπaug m`. Introduce `j`. Rewrite using `[AlgHom.comp_apply, hπX, hπX, map_add, AlgHom.commutes]`.

Both sides reduce to the same expression. Introduce `m`. Use `etale_ext (n := n) ε' (jetAug R (Fin n) 0) (ker_jetAug_nil (Fin n) 0) _ _ ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[← AlgHom.comp_assoc, jetAug_comp_zero]`. Conclude with `hπaug m`.

Use extensionality with `s`. Simplify using the standard rewrite rules. Introduce `j`. Rewrite using `[AlgHom.comp_apply, hπX, map_add, AlgHom.commutes, AlgHom.comp_apply, jetZero_zR, add_zero]`. Both sides reduce to the same expression.

Introduce `A _ _ aug m hJ φ' hφ'aug`. Establish `hJn` using `nil_of_pow _ hJ`. Establish `hmem : ∀ j : Fin n, φ' (sX (S` using `B) R j) - algebraMap R A (ε' (sX (S := B) R j)) ∈ RingHom.ker aug := by`. Introduce `j`. Rewrite using `[RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, ← AlgHom.comp_apply, hφ'aug, sub_self]`.

Set `ψ` to `jetLift R (RingHom.ker aug) hJ (fun j : Fin n => φ' (sX (S := B) R j) - algebraMap R A (ε' (sX (S := B) R j))) hmem`. Establish `hψaug : aug.comp ψ = jetAug R (Fin n) m` using `jet_ext fun j => by`. Rewrite using `[AlgHom.comp_apply, jetLift_zR, jetAug_zR]`. Conclude with `hmem j`. Establish `hψπ : ψ.comp (π m) = φ'`.

Use `etale_ext (n := n) ε' aug hJn _ _ ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[← AlgHom.comp_assoc, hψaug]`. Conclude with `hπaug m`. Conclude with `hφ'aug`. Introduce `j`.

Rewrite using `[AlgHom.comp_apply, hπX, map_add, AlgHom.commutes, jetLift_zR, add_sub_cancel]`. Use `⟨ψ, ⟨hψaug, hψπ⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `ψ₂ ⟨_, h4⟩`. Apply `jet_ext` to reduce the goal to its premises. Introduce `j`.

Rewrite using `[jetLift_zR]`. Use `AlgHom.congr_fun h4 (sX R j)` as an intermediate fact. Rewrite `this` using `[AlgHom.comp_apply, hπX, map_add, AlgHom.commutes]`. Rewrite using `[← this, add_sub_cancel_left]`.
-/
theorem algChart_of_relativeDimension {R : Type} [CommRing R] (B : Type) [CommRing B] [Algebra R B] {n : ℕ}
    (hB : (algebraMap R B).IsStandardSmoothOfRelativeDimension n) (ε' : B →ₐ[R] R) :
    ∃ (π : ∀ m : ℕ, B →ₐ[R] JetR R (Fin n) m),
      (∀ m, (jetTruncR R (Fin n) m).comp (π (m + 1)) = π m) ∧
      (∀ m, (jetZeroR R (Fin n) m).comp (π m) = (Algebra.ofId R _).comp ε') ∧
      ∀ (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (m : ℕ), (RingHom.ker aug) ^ (m + 1) = ⊥ →
        ∀ φ : B →ₐ[R] A, aug.comp φ = ε' →
          ∃! ψ : JetR R (Fin n) m →ₐ[R] A, aug.comp ψ = jetAug R (Fin n) m ∧ ψ.comp (π m) = φ := by
  obtain ⟨g, hgC, hg⟩ := hB.exists_etale_mvPolynomial
  letI : Algebra (MvPolynomial (Fin n) R) B := g.toAlgebra
  haveI : IsScalarTower R (MvPolynomial (Fin n) R) B := IsScalarTower.of_algebraMap_eq' hgC.symm
  haveI : Algebra.Etale (MvPolynomial (Fin n) R) B := hg
  have hπ : ∀ m : ℕ, ∃ π : B →ₐ[R] JetR R (Fin n) m, (jetAug R (Fin n) m).comp π = ε' ∧
      ∀ j, π (sX R j) = algebraMap R _ (ε' (sX R j)) + zR m j := fun m =>
    etale_exists (n := n) ε' (jetAug R (Fin n) m) (ker_jetAug_nil (Fin n) m) _ (fun j => by
      rw [map_add, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, jetAug_zR, add_zero])
  choose π hπaug hπX using hπ
  refine ⟨π, ?_, ?_, ?_⟩
  · intro m
    refine etale_ext (n := n) ε' (jetAug R (Fin n) m) (ker_jetAug_nil (Fin n) m) _ _ ?_ ?_ ?_
    · rw [← AlgHom.comp_assoc, jetAug_comp_trunc]
      exact hπaug (m + 1)
    · exact hπaug m
    · intro j
      rw [AlgHom.comp_apply, hπX, hπX, map_add, AlgHom.commutes]
      rfl
  · intro m
    refine etale_ext (n := n) ε' (jetAug R (Fin n) 0) (ker_jetAug_nil (Fin n) 0) _ _ ?_ ?_ ?_
    · rw [← AlgHom.comp_assoc, jetAug_comp_zero]
      exact hπaug m
    · ext s
      simp
    · intro j
      rw [AlgHom.comp_apply, hπX, map_add, AlgHom.commutes, AlgHom.comp_apply, jetZero_zR, add_zero]
      rfl
  · intro A _ _ aug m hJ φ' hφ'aug
    have hJn := nil_of_pow _ hJ
    have hmem : ∀ j : Fin n, φ' (sX (S := B) R j) -
        algebraMap R A (ε' (sX (S := B) R j)) ∈ RingHom.ker aug := by
      intro j
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
        ← AlgHom.comp_apply, hφ'aug, sub_self]
    let ψ := jetLift R (RingHom.ker aug) hJ
      (fun j : Fin n => φ' (sX (S := B) R j) - algebraMap R A (ε' (sX (S := B) R j))) hmem
    have hψaug : aug.comp ψ = jetAug R (Fin n) m := jet_ext fun j => by
      rw [AlgHom.comp_apply, jetLift_zR, jetAug_zR]; exact hmem j
    have hψπ : ψ.comp (π m) = φ' := by
      refine etale_ext (n := n) ε' aug hJn _ _ ?_ ?_ ?_
      · rw [← AlgHom.comp_assoc, hψaug]
        exact hπaug m
      · exact hφ'aug
      · intro j
        rw [AlgHom.comp_apply, hπX, map_add, AlgHom.commutes, jetLift_zR, add_sub_cancel]
    refine ⟨ψ, ⟨hψaug, hψπ⟩, ?_⟩
    rintro ψ₂ ⟨_, h4⟩
    apply jet_ext
    intro j
    rw [jetLift_zR]
    have := AlgHom.congr_fun h4 (sX R j)
    rw [AlgHom.comp_apply, hπX, map_add, AlgHom.commutes] at this
    rw [← this, add_sub_cancel_left]

/- English proof (translation)
Set `e' : Spec (CommRingCat.of k) ⟶ G.left` to `(η[G]).left`. Take `⟨U₀, -, U, hU, hp, hle, hsm⟩` from `hG.exists_isStandardSmoothOfRelativeDimension (e' (default : PrimeSpectrum k))`. Establish `hU₀ : U₀ = ⊤`. Use `eq_top_iff.2 fun y _ => ?_` and prove the remaining obligations. Establish `h1 : G.hom (e' (default : PrimeSpectrum k)) ∈ U₀` using `hle hp`.

Establish `h2 : y = G.hom (e' (default : PrimeSpectrum k))` using `Subsingleton.elim (α := PrimeSpectrum k) _ _`. Rewrite using `[h2]`. Conclude with `h1`. Substitute `hU₀` using the available equality. Take `⟨C, hC⟩ : ∃ C : Chart G, (alg0 C).IsStandardSmoothOfRelativeDimension n` from `⟨⟨U, hU, fun y _ => by`.

Establish `h2 : y = (default : PrimeSpectrum k)` using `Subsingleton.elim (α := PrimeSpectrum k) _ _`. Rewrite using `[h2]`. Conclude with `hp⟩,`. Use the proof step `RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 (G.hom.appLE ⊤ U hle).hom (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv hsm⟩`. Take `⟨π, htr, hze, huniv⟩` from `algChart_of_relativeDimension Γ(G.left, C.U) hC (eps C)`.

Use `⟨fun m => pt C (π m), fun m => ?_, fun m => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[spMap_pt, htr]`. Rewrite using `[spMap_pt, hze, pt_eps]`. Introduce `A _ _ aug m hJ y hy`. Establish `hJn` using `nil_of_pow _ hJ`.

Establish `hy' : spMap aug ≫ y = pt C ((Algebra.ofId k k).comp (eps C))` using `by rw [pt_eps]; exact hy`. Take `⟨φ, rfl⟩` from `exists_pt C y (le_preimage_of_nil C aug (aug_surj aug) (elt_nil _ hJn) y _ hy')`. Establish `hφ : aug.comp φ = eps C`. Use `pt_injective C ((spMap_pt C aug φ).symm.trans hy')` as an intermediate fact. Rewrite using `[this]`.

Use extensionality with `b`. Both sides reduce to the same expression. Take `⟨ψ, ⟨hψ1, hψ2⟩, hψu⟩` from `huniv A aug m hJ φ hφ`. Use `⟨ψ, ⟨hψ1, by rw [spMap_pt, hψ2]⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `ψ₂ ⟨h1, h2⟩`.

Rewrite `h2` using `[spMap_pt]`. Conclude with `hψu ψ₂ ⟨h1, (pt_injective C h2).symm⟩`.
-/
theorem univChart_of_relativeDimension {k : Type} [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G] {n : ℕ}
    (hG : SmoothOfRelativeDimension n G.hom) :
    ∃ x : ∀ m : ℕ, sp (R₀ := k) (JetR k (Fin n) m) ⟶ G, IsUnivChart G n x := by
  let e' : Spec (CommRingCat.of k) ⟶ G.left := (η[G]).left
  obtain ⟨U₀, -, U, hU, hp, hle, hsm⟩ :=
    hG.exists_isStandardSmoothOfRelativeDimension (e' (default : PrimeSpectrum k))
  have hU₀ : U₀ = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have h1 : G.hom (e' (default : PrimeSpectrum k)) ∈ U₀ := hle hp
    have h2 : y = G.hom (e' (default : PrimeSpectrum k)) :=
      Subsingleton.elim (α := PrimeSpectrum k) _ _
    rw [h2]; exact h1
  subst hU₀
  obtain ⟨C, hC⟩ : ∃ C : Chart G, (alg0 C).IsStandardSmoothOfRelativeDimension n := ⟨⟨U, hU, fun y _ => by
    have h2 : y = (default : PrimeSpectrum k) := Subsingleton.elim (α := PrimeSpectrum k) _ _
    rw [h2]; exact hp⟩,
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 (G.hom.appLE ⊤ U hle).hom
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv hsm⟩
  obtain ⟨π, htr, hze, huniv⟩ := algChart_of_relativeDimension Γ(G.left, C.U) hC (eps C)
  refine ⟨fun m => pt C (π m), fun m => ?_, fun m => ?_, ?_⟩
  · rw [spMap_pt, htr]
  · rw [spMap_pt, hze, pt_eps]
  · intro A _ _ aug m hJ y hy
    have hJn := nil_of_pow _ hJ
    have hy' : spMap aug ≫ y = pt C ((Algebra.ofId k k).comp (eps C)) := by rw [pt_eps]; exact hy
    obtain ⟨φ, rfl⟩ := exists_pt C y (le_preimage_of_nil C aug (aug_surj aug) (elt_nil _ hJn) y _ hy')
    have hφ : aug.comp φ = eps C := by
      have := pt_injective C ((spMap_pt C aug φ).symm.trans hy')
      rw [this]
      ext b
      rfl
    obtain ⟨ψ, ⟨hψ1, hψ2⟩, hψu⟩ := huniv A aug m hJ φ hφ
    refine ⟨ψ, ⟨hψ1, by rw [spMap_pt, hψ2]⟩, ?_⟩
    rintro ψ₂ ⟨h1, h2⟩
    rw [spMap_pt] at h2
    exact hψu ψ₂ ⟨h1, (pt_injective C h2).symm⟩

def tangentAction {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {n : ℕ}
    {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x) {O : Type} [CommRing O]
    (act : O → (G ⟶ G)) [∀ a, IsMonHom (act a)] (h1 : act 1 = 𝟙 G) (hm : ∀ a b, act (a * b) = act a ≫ act b)
    (ha : ∀ a b, act (a + b) = act a * act b) : O →+* Module.End R (Fin n → R) :=
  RingHom.mk'
    { toFun := fun a => tmap hx (act a)
      map_one' := LinearMap.ext fun c => tvec_inj hx (by
        rw [tvec_tmap, h1, Category.comp_id]; rfl)
      map_mul' := fun a b => LinearMap.ext fun c => tvec_inj hx (by
        rw [Module.End.mul_apply, tvec_tmap, tvec_tmap, tvec_tmap, mul_comm, hm, Category.assoc]) }
    fun a b => LinearMap.ext fun c => tvec_inj hx (by
      show tvec (tmap hx (act (a + b)) c) = tvec (tmap hx (act a) c + tmap hx (act b) c)
      rw [tvec_add hx, tvec_tmap, tvec_tmap, tvec_tmap, ha, MonObj.comp_mul])

end Chart

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Count

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {k : Type} [Field k] [IsAlgClosed k]
  [CharZero k]

open Classical in

/- English proof (translation)
Set `c : E ≃+* E` to `(IsCMField.complexConj E).toRingEquiv`. Establish `hc : c (H.rt : E) = -(H.rt : E)`. Use `H.bar_eq H.rt` as an intermediate fact. Rewrite `this` using `[GlobalTheory.HostModel.bar_rt]`. Conclude with `this.symm.trans (by simp)`.

Set `e : (E →+* k) ≃ (E →+* k)` to `⟨fun φ => φ.comp c.toRingHom, fun φ => φ.comp c.symm.toRingHom, fun φ => by ext; simp, fun φ => by ext; simp⟩`. Establish `he : ∀ φ, e φ (H.rt : E) = -φ (H.rt : E)` using `fun φ => by show φ (c _) = _`. Rewrite using `[hc, map_neg]`. Establish `hr0 : r ≠ -r` using `fun h => by`. Establish `h0 : r = 0` using `by linear_combination h / 2`.

Rewrite `hr` using `[h0]`. Establish `: (H.d : k) = 0` using `by linear_combination hr`. Conclude with `H.d_prime.ne_zero (by exact_mod_cast this)`. Rewrite using `[two_mul]`. Use `nth_rewrite 2 [← e.sum_comp]`.

Rewrite using `[← Finset.sum_add_distrib, ← NumberField.Embeddings.card E k, ← Finset.card_univ, ← smul_eq_mul, ← Finset.sum_const]`. Use `Finset.sum_congr rfl fun φ _ => ?_` and prove the remaining obligations. Rewrite using `[he]`. Establish `h2 : φ (H.rt : E) ^ 2 = r ^ 2`. Rewrite using `[← map_pow, GlobalTheory.HostModel.coe_rt_sq, hr]`.

Simplify using the standard rewrite rules. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h` into its components or cases. Rewrite using `[h, if_pos rfl, if_neg hr0.symm]`. Rewrite using `[h, neg_neg, if_pos rfl, if_neg hr0.symm, add_comm]`.
-/
theorem two_mul_sum_embeddings {r : k} (hr : r ^ 2 = -(H.d : k)) (p q : ℕ) :
    2 * ∑ φ : E →+* k, (if φ (H.rt : E) = r then p else q) = Module.finrank ℚ E * (p + q) := by
  let c : E ≃+* E := (IsCMField.complexConj E).toRingEquiv
  have hc : c (H.rt : E) = -(H.rt : E) := by
    have := H.bar_eq H.rt
    rw [GlobalTheory.HostModel.bar_rt] at this
    exact this.symm.trans (by simp)
  let e : (E →+* k) ≃ (E →+* k) :=
    ⟨fun φ => φ.comp c.toRingHom, fun φ => φ.comp c.symm.toRingHom, fun φ => by ext; simp, fun φ => by ext; simp⟩
  have he : ∀ φ, e φ (H.rt : E) = -φ (H.rt : E) := fun φ => by
    show φ (c _) = _
    rw [hc, map_neg]
  have hr0 : r ≠ -r := fun h => by
    have h0 : r = 0 := by linear_combination h / 2
    rw [h0] at hr
    have : (H.d : k) = 0 := by linear_combination hr
    exact H.d_prime.ne_zero (by exact_mod_cast this)
  rw [two_mul]
  nth_rewrite 2 [← e.sum_comp]
  rw [← Finset.sum_add_distrib, ← NumberField.Embeddings.card E k, ← Finset.card_univ, ← smul_eq_mul,
    ← Finset.sum_const]
  refine Finset.sum_congr rfl fun φ _ => ?_
  rw [he]
  have h2 : φ (H.rt : E) ^ 2 = r ^ 2 := by
    rw [← map_pow, GlobalTheory.HostModel.coe_rt_sq, hr]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
  · rw [h, if_pos rfl, if_neg hr0.symm]
  · rw [h, neg_neg, if_pos rfl, if_neg hr0.symm, add_comm]

open Classical in
/- English proof (translation)
Establish `h1` using `two_mul_sum_embeddings H hr 1 0`. Establish `h2` using `two_mul_sum_embeddings H hr p q`. Rewrite `h1` using `[add_zero, _root_.mul_one]`. Rewrite `h2`, the goal using `[← h1]`. Rewrite using `[Nat.mul_div_cancel_left _ two_pos]`.

Rewrite `h2` using `[_root_.mul_assoc]`. Conclude with `Nat.eq_of_mul_eq_mul_left two_pos h2`.
-/
theorem sum_embeddings {r : k} (hr : r ^ 2 = -(H.d : k)) (p q : ℕ) :
    ∑ φ : E →+* k, (if φ (H.rt : E) = r then p else q) = Module.finrank ℚ E / 2 * (p + q) := by
  have h1 := two_mul_sum_embeddings H hr 1 0
  have h2 := two_mul_sum_embeddings H hr p q
  rw [add_zero, _root_.mul_one] at h1
  rw [← h1] at h2 ⊢
  rw [Nat.mul_div_cancel_left _ two_pos]
  rw [_root_.mul_assoc] at h2
  exact Nat.eq_of_mul_eq_mul_left two_pos h2

/- English proof (translation)
Establish `hs : EigenSplit.IsSplitting fun φ : E →+* k => φ.comp (algebraMap (𝓞 E) E)`. Take `⟨b⟩` from `EigenSplit.nonempty_basis (E := E) (NumberField.Embeddings.card E k)`. Conclude with `EigenSplit.isSplitting_of_isUnit_discr b (EigenSplit.det_sq_eq_discr_of_field Function.injective_id b) (by simpa using NumberField.discr_ne_zero E)`. Rewrite using `[(EigenSplit.eigenEquiv hs ρ).finrank_eq, Module.finrank_pi_fintype, ← sum_embeddings H hr]`. Use `Finset.sum_congr rfl fun φ _ => ?_` and prove the remaining obligations.

Use `split_ifs with hφ`. Conclude with `(h _).1 hφ`. Conclude with `(h _).2 hφ`.
-/
theorem finrank_eq_of_eigenSub {r : k} (hr : r ^ 2 = -(H.d : k)) {p q : ℕ} {V : Type} [AddCommGroup V] [Module k V]
    [Module.Finite k V] (ρ : 𝓞 E →+* Module.End k V)
    (h : ∀ τ : 𝓞 E →+* k, (τ H.rt = r → Module.finrank k (EigenSplit.eigenSub ρ τ) = p) ∧
      (τ H.rt ≠ r → Module.finrank k (EigenSplit.eigenSub ρ τ) = q)) :
    Module.finrank k V = Module.finrank ℚ E / 2 * (p + q) := by
  classical
  have hs : EigenSplit.IsSplitting fun φ : E →+* k => φ.comp (algebraMap (𝓞 E) E) := by
    obtain ⟨b⟩ := EigenSplit.nonempty_basis (E := E) (NumberField.Embeddings.card E k)
    exact EigenSplit.isSplitting_of_isUnit_discr b (EigenSplit.det_sq_eq_discr_of_field Function.injective_id b)
      (by simpa using NumberField.discr_ne_zero E)
  rw [(EigenSplit.eigenEquiv hs ρ).finrank_eq, Module.finrank_pi_fintype, ← sum_embeddings H hr]
  refine Finset.sum_congr rfl fun φ _ => ?_
  split_ifs with hφ
  · exact (h _).1 hφ
  · exact (h _).2 hφ

end Count

/- English proof (translation)
Take `⟨c, hc⟩` from `univChart_of_relativeDimension ((Over.pullback x).obj G) hn`. Establish `: ∀ a, IsMonHom (act.act a)` using `act.hom`. Set `ρ` to `tangentAction hc (fun a => (Over.pullback x).map (act.act a)) (by rw [act.one, CategoryTheory.Functor.map_id]) (fun a b => by rw [act.mul, Functor.map_comp]) (fun a b => by rw [act.add, Functor.map_mul])`. Establish `key : ∀ (τ : 𝓞 E →+* k) (N : ℕ), LieMult act x τ N → Module.finrank k (EigenSplit.eigenSub ρ τ) = N`. Introduce `τ N hN`.

Establish `e : EigenSplit.eigenSub ρ τ = Chart.eigLat hc (fun a => (Over.pullback x).map (act.act a)) (fun a => τ a)`. Use extensionality with `v`. Rewrite using `[EigenSplit.mem_eigenSub, Chart.mem_eigLat_iff]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Establish `: IsMonHom (Iso.refl G).hom` using `inferInstanceAs (IsMonHom (𝟙 G))`. Conclude with `Chart.finrank_of_lieMult (isGrpPullback_of_iso (Iso.refl G)) (Category.comp_id x) hc act act.act (fun a => by simp) _ (fun a => rfl) τ hN`. Use `finrank_eq_of_eigenSub H hr ρ fun τ => ⟨fun h => key τ _ ((hD τ).1 h), fun h => key τ _ ((hD τ).2 h)⟩` as an intermediate fact. Rewrite `this` using `[Module.finrank_fin_fun]`. Then use the resulting hypothesis.
-/
theorem dim_eq_of_detCond {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {S : Scheme.{0}} {G : Over S} [GrpObj G] (act : OAct (𝓞 E) G) {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    (x : Sp k ⟶ S) {r : k} (hr : r ^ 2 = -(H.d : k)) (hD : DetCond D act x r) {n : ℕ}
    (hn : SmoothOfRelativeDimension n (pullback.snd G.hom x)) : n = Module.finrank ℚ E / 2 * (D.p + D.q) := by
  obtain ⟨c, hc⟩ := univChart_of_relativeDimension ((Over.pullback x).obj G) hn
  have : ∀ a, IsMonHom (act.act a) := act.hom
  let ρ := tangentAction hc (fun a => (Over.pullback x).map (act.act a)) (by rw [act.one, CategoryTheory.Functor.map_id])
    (fun a b => by rw [act.mul, Functor.map_comp]) (fun a b => by rw [act.add, Functor.map_mul])
  have key : ∀ (τ : 𝓞 E →+* k) (N : ℕ), LieMult act x τ N → Module.finrank k (EigenSplit.eigenSub ρ τ) = N := by
    intro τ N hN
    have e : EigenSplit.eigenSub ρ τ =
        Chart.eigLat hc (fun a => (Over.pullback x).map (act.act a)) (fun a => τ a) := by
      ext v
      rw [EigenSplit.mem_eigenSub, Chart.mem_eigLat_iff]
      rfl
    rw [e]
    have : IsMonHom (Iso.refl G).hom := inferInstanceAs (IsMonHom (𝟙 G))
    exact Chart.finrank_of_lieMult (isGrpPullback_of_iso (Iso.refl G)) (Category.comp_id x) hc act act.act
      (fun a => by simp) _ (fun a => rfl) τ hN
  have := finrank_eq_of_eigenSub H hr ρ fun τ => ⟨fun h => key τ _ ((hD τ).1 h), fun h => key τ _ ((hD τ).2 h)⟩
  rwa [Module.finrank_fin_fun] at this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {B : Type}
  [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}

/- English proof (translation)
Assemble the required witnesses or components as `⟨o.t.semi.comm, o.t.semi.smooth, o.proper, o.t.semi.geomConnected⟩`.
-/
theorem isAbelianScheme (o : Obj D l b s) : IsAbelianScheme o.t.G :=
  ⟨o.t.semi.comm, o.t.semi.smooth, o.proper, o.t.semi.geomConnected⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨t.PP.rig, t.PP.rigGen⟩`.
-/
theorem rigidified {t : SAB H S} : Out.Rigidified t.G t.PP.L := ⟨t.PP.rig, t.PP.rigGen⟩

/- English proof (translation)
Take `⟨-, w, hw, -⟩` from `t.sym`. Conclude with `fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff w).1 hw) _⟩`.
-/
theorem sym {t : SAB H S} : Out.Sym t.G t.PP.L := by
  obtain ⟨-, w, hw, -⟩ := t.sym
  exact fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff w).1 hw) _⟩

/- English proof (translation)
Use `o.t.semi.smooth` as an intermediate fact. Use `o.t.semi.geomConnected` as an intermediate fact. Use `choose n W hW hd using H1.exists_dim o.t.G.hom`. Establish `: IsZariskiLocalAtSource (@SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)))` using `HasRingHomProperty.instIsZariskiLocalAtSource`. Use `IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q))) W (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_` and prove the remaining obligations.

Set `k` to `AlgebraicClosure (o.t.G.left.residueField y)`. Set `z : Sp k ⟶ o.t.G.left` to `Spec.map (CommRingCat.ofHom (algebraMap (o.t.G.left.residueField y) k)) ≫ o.t.G.left.fromSpecResidueField y`. Establish `hz : ∀ u, z u = y` using `fun u => Scheme.fromSpecResidueField_apply y _`. Set `x : Sp k ⟶ S` to `z ≫ o.t.G.hom`. Set `β : B →+* k` to `(Spec.preimage (x ≫ s)).hom`.

Establish `hβ : x ≫ s = spMap β` using `(Spec.map_preimage (x ≫ s)).symm`. Establish `: CharZero k` using `charZero_of_inj_zero fun m hm => by`. Assume the negation of the conclusion as `h0`. Use `(b.unit m (Nat.pos_of_ne_zero h0)).map β` as an intermediate fact. Rewrite `this` using `[map_natCast, hm]`.

Conclude with `not_isUnit_zero this`. Establish `hr : β b.ρ ^ 2 = -(H.d : k)` using `by rw [← map_pow, b.ρ_sq, map_neg, map_natCast]`. Establish `: ConnectedSpace ↥(pullback o.t.G.hom x)` using `GeometricallyConnected.geometrically_connectedSpace (f := o.t.G.hom) x _ _ (IsPullback.of_hasPullback _ _)`. Set `z' : Sp k ⟶ pullback o.t.G.hom x` to `pullback.lift z (𝟙 _) (Category.id_comp _).symm`. Take `⟨m, hm⟩` from `exists_dim_of_preconnected (pullback.snd o.t.G.hom x) (z' (default : PrimeSpectrum k))`.

Establish `e₁ : n y = m` using `H1.dim_base (IsPullback.of_hasPullback _ _) (hd y) hm (z' (default : PrimeSpectrum k)) (by`. Establish `e : z' ≫ pullback.fst o.t.G.hom x = z` using `pullback.lift_fst _ _ _`. Establish `e'` using `(congrArg (fun q : Sp k ⟶ o.t.G.left => q (default : PrimeSpectrum k)) e).trans (hz _)`. Conclude with `(congrArg (fun u => u ∈ W y) e').mpr (hW y))`. Rewrite using `[← dim_eq_of_detCond D o.t.act x hr (o.geom k x β hβ).1 hm, ← e₁]`.

Conclude with `hd y`.
-/
theorem smoothOfRelativeDimension (o : Obj D l b s) :
    SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom := by
  have := o.t.semi.smooth
  have := o.t.semi.geomConnected
  choose n W hW hd using H1.exists_dim o.t.G.hom
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q))) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top
    (P := @SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q))) W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_
  let k := AlgebraicClosure (o.t.G.left.residueField y)
  let z : Sp k ⟶ o.t.G.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (o.t.G.left.residueField y) k)) ≫ o.t.G.left.fromSpecResidueField y
  have hz : ∀ u, z u = y := fun u => Scheme.fromSpecResidueField_apply y _
  let x : Sp k ⟶ S := z ≫ o.t.G.hom
  let β : B →+* k := (Spec.preimage (x ≫ s)).hom
  have hβ : x ≫ s = spMap β := (Spec.map_preimage (x ≫ s)).symm
  have : CharZero k := charZero_of_inj_zero fun m hm => by
    by_contra h0
    have := (b.unit m (Nat.pos_of_ne_zero h0)).map β
    rw [map_natCast, hm] at this
    exact not_isUnit_zero this
  have hr : β b.ρ ^ 2 = -(H.d : k) := by rw [← map_pow, b.ρ_sq, map_neg, map_natCast]
  have : ConnectedSpace ↥(pullback o.t.G.hom x) :=
    GeometricallyConnected.geometrically_connectedSpace (f := o.t.G.hom) x _ _ (IsPullback.of_hasPullback _ _)
  let z' : Sp k ⟶ pullback o.t.G.hom x := pullback.lift z (𝟙 _) (Category.id_comp _).symm
  obtain ⟨m, hm⟩ := exists_dim_of_preconnected (pullback.snd o.t.G.hom x) (z' (default : PrimeSpectrum k))
  have e₁ : n y = m := H1.dim_base (IsPullback.of_hasPullback _ _) (hd y) hm (z' (default : PrimeSpectrum k)) (by
    have e : z' ≫ pullback.fst o.t.G.hom x = z := pullback.lift_fst _ _ _
    have e' := (congrArg (fun q : Sp k ⟶ o.t.G.left => q (default : PrimeSpectrum k)) e).trans (hz _)
    exact (congrArg (fun u => u ∈ W y) e').mpr (hW y))
  rw [← dim_eq_of_detCond D o.t.act x hr (o.geom k x β hβ).1 hm, ← e₁]
  exact hd y

end GlobalTheory.ObjDim

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ _ _ _ _ o` and use `⟨ObjDim.isAbelianScheme o, ObjDim.smoothOfRelativeDimension o, ObjDim.rigidified, ObjDim.sym⟩`.
-/
theorem obj_isAbelianScheme_dim_rigidified_sym :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ o =>
    ⟨ObjDim.isAbelianScheme o, ObjDim.smoothOfRelativeDimension o, ObjDim.rigidified, ObjDim.sym⟩

def Obj.toPolAV {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s) : Out.PolAV S where
  A := o.t.G
  isAb := ObjDim.isAbelianScheme o
  g := Module.finrank ℚ E / 2 * (D.p + D.q)
  smoothDim := ObjDim.smoothOfRelativeDimension o
  L := o.t.PP.L
  isLB := o.t.PP.isLB
  rigid := ObjDim.rigidified
  sym := ObjDim.sym
  ample := o.ample
  ktriv := o.ktriv

end GlobalTheory
