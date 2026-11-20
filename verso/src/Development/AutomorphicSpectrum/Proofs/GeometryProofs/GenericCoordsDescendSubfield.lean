import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagModelStatementHoldsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SegreRefineLineBundlesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptBlockRefinementStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelDominantHodgeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEigenVectorBundleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenspaceDecompositionInternalStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelEmbeddingInjectiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIsLocalRingIsFractionRingStalk
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsRegularSectionGenerator
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SatModel

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {Li : Type} [AddCommGroup Li]
  [Module Ω Li]

/- English proof (translation)
Establish `: b '' {k | (k : ℕ) < r} = Set.range b`. Rewrite using `[← Set.image_univ]`. Use `congr 1`. Use extensionality with `k`. Simplify using `[k.2]`.

Rewrite using `[flagStep, this]`.
-/
theorem flagStep_self {r : ℕ} (b : Fin r → Li) : flagStep Ω b r = Submodule.span Ω (Set.range b) := by
  have : b '' {k | (k : ℕ) < r} = Set.range b := by
    rw [← Set.image_univ]
    congr 1
    ext k
    simp [k.2]
  rw [flagStep, this]

/- English proof (translation)
Establish `: dualMap (RingHom.id Ω) = RingHom.id (DualNumber Ω)`. Apply the tactic sequence `ext a <;> simp [dualMap]`. Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem spMap_dualMap_id : spMap (dualMap (RingHom.id Ω)) = 𝟙 (Sp (DualNumber Ω)) := by
  have : dualMap (RingHom.id Ω) = RingHom.id (DualNumber Ω) := by
    ext a <;> simp [dualMap]
  rw [this]
  simp

/- English proof (translation)
Introduce `p hp`. Take `⟨U, hU, b, hb, hf⟩` from `h p (hT hp)`. Conclude with `⟨U, hU, b, hb, fun q hq => hf q (hT hq)⟩`.
-/
theorem IsFlagVBOn_mono {L : Lat ξ Li} {T T' : Set (Cpt ξ)} {r : ℕ} {b₀ : Fin r → Li} (h : L.IsFlagVBOn T b₀)
    (hT : T' ⊆ T) : L.IsFlagVBOn T' b₀ := by
  intro p hp
  obtain ⟨U, hU, b, hb, hf⟩ := h p (hT hp)
  exact ⟨U, hU, b, hb, fun q hq => hf q (hT hq)⟩

/- English proof (translation)
Introduce `p hp`. Take `⟨U, hU, b, hb, hf⟩` from `h p hp`. Conclude with `⟨U, hU, b, by rw [← flagStep_self, ← flagStep_self, hb], hf⟩`.
-/
theorem isVBOn_of_isFlagVBOn {L : Lat ξ Li} {T : Set (Cpt ξ)} {r : ℕ} {b₀ : Fin r → Li} (h : L.IsFlagVBOn T b₀) :
    L.IsVBOn T r (Submodule.span Ω (Set.range b₀)) := by
  intro p hp
  obtain ⟨U, hU, b, hb, hf⟩ := h p hp
  exact ⟨U, hU, b, by rw [← flagStep_self, ← flagStep_self, hb], hf⟩

/- English proof (translation)
Use `⟨fun h => Submodule.span_subset_span (regAt ξ (Flat.ZLat.gp ξ)) Ω S h, fun h => ?_⟩` and prove the remaining obligations. Proceed by induction on `h using Submodule.span_induction with`. Consider the case `mem e he => exact Submodule.subset_span he`. Consider the case `zero => exact zero_mem _`. Consider the case `add x y _ _ hx hy => exact add_mem hx hy`.

Consider the case `smul c x _ hx`. Conclude with `Submodule.smul_mem _ (⟨c, Flat.ZLat.mem_regAt_gp hg c⟩ : regAt ξ (Flat.ZLat.gp ξ)) hx`.
-/
theorem mem_span_gp_iff (hg : IsCptGen ξ) (S : Set Li) (x : Li) :
    x ∈ Submodule.span (regAt ξ (Flat.ZLat.gp ξ)) S ↔ x ∈ Submodule.span Ω S := by
  refine ⟨fun h => Submodule.span_subset_span (regAt ξ (Flat.ZLat.gp ξ)) Ω S h, fun h => ?_⟩
  induction h using Submodule.span_induction with
  | mem e he => exact Submodule.subset_span he
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul c x _ hx =>
    exact Submodule.smul_mem _ (⟨c, Flat.ZLat.mem_regAt_gp hg c⟩ : regAt ξ (Flat.ZLat.gp ξ)) hx

/- English proof (translation)
Take `⟨U, hU, b, hb, hf⟩` from `h _ hT`. Take `⟨-, hfr⟩` from `hf _ hT hU`. Take `⟨U', hU', c, hc, hf'⟩` from `hL (Flat.ZLat.gp ξ) trivial`. Take `⟨-, hfr'⟩` from `hf' _ trivial hU'`. Rewrite using `[← flagStep_self, ← hb, flagStep_self]`.

Use extensionality with `x`. Rewrite using `[← mem_span_gp_iff hg, ← hfr]`. Use `show x ∈ L (Flat.ZLat.gp ξ) ⊓ V.restrictScalars _ ↔ _`. Rewrite using `[Submodule.mem_inf, hfr', mem_span_gp_iff hg, hc]`. Simplify using the standard rewrite rules.
-/
theorem span_eq_of_isFlagVBOn (hg : IsCptGen ξ) {L : Lat ξ Li} {n : ℕ} (hL : L.IsVB n ⊤) {T : Set (Cpt ξ)}
    (hT : Flat.ZLat.gp ξ ∈ T) {V : Submodule Ω Li} {r : ℕ} {b₀ : Fin r → Li} (h : (L.inter V).IsFlagVBOn T b₀) :
    Submodule.span Ω (Set.range b₀) = V := by
  obtain ⟨U, hU, b, hb, hf⟩ := h _ hT
  obtain ⟨-, hfr⟩ := hf _ hT hU
  obtain ⟨U', hU', c, hc, hf'⟩ := hL (Flat.ZLat.gp ξ) trivial
  obtain ⟨-, hfr'⟩ := hf' _ trivial hU'
  rw [← flagStep_self, ← hb, flagStep_self]
  ext x
  rw [← mem_span_gp_iff hg, ← hfr]
  show x ∈ L (Flat.ZLat.gp ξ) ⊓ V.restrictScalars _ ↔ _
  rw [Submodule.mem_inf, hfr', mem_span_gp_iff hg, hc]
  simp

/- English proof (translation)
Use `haveI := Fintype.ofFinite I`. Establish `hfr : ∀ s, ∃ B : Fin (r s) → Li, (∀ i, flagStep Ω B i = flagStep Ω (b₀ s) i) ∧ (L.inter (V s)).IsFrameAt B p`. Introduce `s`. Take `⟨U, hU, B, hB, hf⟩` from `hb s p rfl`. Conclude with `⟨B, hB, hf p rfl hU⟩`.

Use `choose B hB hfB using hfr`. Establish `hBV : ∀ s k, B s k ∈ V s`. Introduce `s k`. Establish `h : B s k ∈ (L.inter (V s)) p`. Rewrite using `[(hfB s).2]`.

Conclude with `Submodule.subset_span ⟨k, rfl⟩`. Conclude with `h.2`. Set `Bt : (Σ s, Fin (r s)) → Li` to `fun i => B i.1 i.2`. Establish `hli : LinearIndependent Ω Bt`. Rewrite using `[Fintype.linearIndependent_iff]`.

Introduce and unpack `c hc ⟨s, k⟩`. Establish `hz` using `(iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero _).1 hV Finset.univ (fun s => ∑ k, c ⟨s, k⟩ • B s k) (fun s _ => Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hBV s k)) (by rw [← hc, Fintype.sum_sigma])`. Conclude with `Fintype.linearIndependent_iff.1 (hfB s).1 (fun k => c ⟨s, k⟩) (hz s (Finset.mem_univ s)) k`. Set `kil : Set (Σ s, Fin (r s))` to `Sigma.mk σ '' {k : Fin (r σ) | (k : ℕ) < n}`. Establish `hF : flagStep Ω (b₀ σ) n = Submodule.span Ω (Bt '' kil)`.

Rewrite using `[← hB σ n, flagStep, Set.image_image]`. Set `e` to `Finite.equivFin {i // i ∉ kil}`. Use `⟨_, fun i => (flagStep Ω (b₀ σ) n).mkQ (Bt (e.symm i)), ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : LinearIndependent Ω (fun i : {i // i ∉ kil} => Bt i)` using `hli.comp _ Subtype.val_injective`. Establish `hd : Disjoint (Submodule.span Ω (Set.range fun i : {i // i ∉ kil} => Bt i)) (LinearMap.ker (flagStep Ω (b₀ σ) n).mkQ)`.

Rewrite using `[Submodule.ker_mkQ, hF]`. Establish `: (Set.range fun i : {i // i ∉ kil} => Bt i) = Bt '' kilᶜ`. Use extensionality with `x`. Simplify using `[Set.mem_image]`. Rewrite using `[this]`.

Conclude with `hli.disjoint_span_image disjoint_compl_left`. Conclude with `(h1.map hd).comp _ e.symm.injective`. Establish `hLp : L p = Submodule.span (regAt ξ p) (Set.range Bt)`. Rewrite using `[hL, Set.range_sigma_eq_iUnion_range, Submodule.span_iUnion]`. Conclude with `iSup_congr fun s => (hfB s).2`.

Use `show (L p).map _ = _`. Rewrite using `[hLp, Submodule.map_span]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨_, ⟨i, rfl⟩, rfl⟩`.

Distinguish the cases in `hi : i ∈ kil`. Establish `: (flagStep Ω (b₀ σ) n).mkQ (Bt i) = 0`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hF]`. Conclude with `Submodule.subset_span ⟨i, hi, rfl⟩`. Use `show (flagStep Ω (b₀ σ) n).mkQ (Bt i) ∈ _`.

Rewrite using `[this]`. Conclude with `zero_mem _`. Use `Submodule.subset_span ⟨e ⟨i, hi⟩, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩`.
-/
theorem exists_frame_map_mkQ {I : Type} [Finite I] {L : Lat ξ Li} {p : Cpt ξ} {V : I → Submodule Ω Li}
    (hV : iSupIndep V) (hL : L p = ⨆ s, L.inter (V s) p) {r : I → ℕ} (b₀ : ∀ s, Fin (r s) → Li)
    (hb : ∀ s, (L.inter (V s)).IsFlagVBOn {p} (b₀ s)) (σ : I) (n : ℕ) :
    ∃ (m : ℕ) (h : Fin m → Li ⧸ flagStep Ω (b₀ σ) n), (L.map (flagStep Ω (b₀ σ) n).mkQ).IsFrameAt h p := by
  classical
  haveI := Fintype.ofFinite I
  have hfr : ∀ s, ∃ B : Fin (r s) → Li, (∀ i, flagStep Ω B i = flagStep Ω (b₀ s) i) ∧
      (L.inter (V s)).IsFrameAt B p := by
    intro s
    obtain ⟨U, hU, B, hB, hf⟩ := hb s p rfl
    exact ⟨B, hB, hf p rfl hU⟩
  choose B hB hfB using hfr
  have hBV : ∀ s k, B s k ∈ V s := by
    intro s k
    have h : B s k ∈ (L.inter (V s)) p := by
      rw [(hfB s).2]
      exact Submodule.subset_span ⟨k, rfl⟩
    exact h.2
  let Bt : (Σ s, Fin (r s)) → Li := fun i => B i.1 i.2
  have hli : LinearIndependent Ω Bt := by
    rw [Fintype.linearIndependent_iff]
    rintro c hc ⟨s, k⟩
    have hz := (iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero _).1 hV Finset.univ
      (fun s => ∑ k, c ⟨s, k⟩ • B s k) (fun s _ => Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hBV s k))
      (by rw [← hc, Fintype.sum_sigma])
    exact Fintype.linearIndependent_iff.1 (hfB s).1 (fun k => c ⟨s, k⟩) (hz s (Finset.mem_univ s)) k
  let kil : Set (Σ s, Fin (r s)) := Sigma.mk σ '' {k : Fin (r σ) | (k : ℕ) < n}
  have hF : flagStep Ω (b₀ σ) n = Submodule.span Ω (Bt '' kil) := by
    rw [← hB σ n, flagStep, Set.image_image]
  let e := Finite.equivFin {i // i ∉ kil}
  refine ⟨_, fun i => (flagStep Ω (b₀ σ) n).mkQ (Bt (e.symm i)), ?_, ?_⟩
  · have h1 : LinearIndependent Ω (fun i : {i // i ∉ kil} => Bt i) := hli.comp _ Subtype.val_injective
    have hd : Disjoint (Submodule.span Ω (Set.range fun i : {i // i ∉ kil} => Bt i))
        (LinearMap.ker (flagStep Ω (b₀ σ) n).mkQ) := by
      rw [Submodule.ker_mkQ, hF]
      have : (Set.range fun i : {i // i ∉ kil} => Bt i) = Bt '' kilᶜ := by
        ext x
        simp [Set.mem_image]
      rw [this]
      exact hli.disjoint_span_image disjoint_compl_left
    exact (h1.map hd).comp _ e.symm.injective
  · have hLp : L p = Submodule.span (regAt ξ p) (Set.range Bt) := by
      rw [hL, Set.range_sigma_eq_iUnion_range, Submodule.span_iUnion]
      exact iSup_congr fun s => (hfB s).2
    show (L p).map _ = _
    rw [hLp, Submodule.map_span]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      by_cases hi : i ∈ kil
      · have : (flagStep Ω (b₀ σ) n).mkQ (Bt i) = 0 := by
          rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hF]
          exact Submodule.subset_span ⟨i, hi, rfl⟩
        show (flagStep Ω (b₀ σ) n).mkQ (Bt i) ∈ _
        rw [this]
        exact zero_mem _
      · refine Submodule.subset_span ⟨e ⟨i, hi⟩, ?_⟩
        simp
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩

/- English proof (translation)
Introduce `z hz`. Establish `key : ∀ φ : Localization.AtPrime P →+* Ω, (∀ a : A, φ (algebraMap A _ a) = a) → ∀ w, φ w ∈ A`. Introduce `φ hφ w`. Take `⟨⟨x, s⟩, hxs⟩` from `IsLocalization.surj P.primeCompl w`. Establish `hs : (s : A) ∉ P` using `s.2`.

Establish `hu : IsUnit (s : A)` using `IsLocalRing.notMem_maximalIdeal.1 (IsLocalRing.eq_maximalIdeal hP ▸ hs)`. Take `⟨u, hu⟩` from `hu.exists_right_inv`. Establish `h1 : φ w * ((s : A) : Ω) = (x : Ω)`. Use `congrArg φ hxs` as an intermediate fact. Rewrite `this` using `[map_mul, hφ, hφ]`. Then use the resulting hypothesis.

Establish `h2 : ((s : A) : Ω) * (u : Ω) = 1` using `by exact_mod_cast congrArg Subtype.val hu`. Establish `h3 : φ w = x * u`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h3]`. Conclude with `mul_mem x.2 u.2`.

Simplify using `only [LocalSubring.ofPrime, LocalSubring.range_toSubring] at hz`. Take `⟨w, rfl⟩` from `hz`. Conclude with `key _ (fun a => IsLocalization.lift_eq _ a) w`.
-/
theorem ofPrime_le {A : Subring Ω} [IsLocalRing A] (P : Ideal A) [hP : P.IsMaximal] :
    (LocalSubring.ofPrime A P).toSubring ≤ A := by
  intro z hz
  have key : ∀ φ : Localization.AtPrime P →+* Ω, (∀ a : A, φ (algebraMap A _ a) = a) → ∀ w, φ w ∈ A := by
    intro φ hφ w
    obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.surj P.primeCompl w
    have hs : (s : A) ∉ P := s.2
    have hu : IsUnit (s : A) := IsLocalRing.notMem_maximalIdeal.1 (IsLocalRing.eq_maximalIdeal hP ▸ hs)
    obtain ⟨u, hu⟩ := hu.exists_right_inv
    have h1 : φ w * ((s : A) : Ω) = (x : Ω) := by
      have := congrArg φ hxs
      rwa [map_mul, hφ, hφ] at this
    have h2 : ((s : A) : Ω) * (u : Ω) = 1 := by exact_mod_cast congrArg Subtype.val hu
    have h3 : φ w = x * u := by
      calc φ w = φ w * (((s : A) : Ω) * (u : Ω)) := by rw [h2, _root_.mul_one]
        _ = x * u := by rw [← _root_.mul_assoc, h1]
    rw [h3]
    exact mul_mem x.2 u.2
  simp only [LocalSubring.ofPrime, LocalSubring.range_toSubring] at hz
  obtain ⟨w, rfl⟩ := hz
  exact key _ (fun a => IsLocalization.lift_eq _ a) w

/- English proof (translation)
Substitute `h` using the available equality. Use `infer_instance`.
-/
theorem isLocalRing_of_eq {A B : Subring Ω} (h : A = B) [IsLocalRing B] : IsLocalRing A := by
  subst h
  infer_instance

/- English proof (translation)
Take `⟨hloc, hfr, -⟩` from `regAt_isLocalRing_isFractionRing_stalk X Ω ξ hg p`. Establish `hA : (integralClosure ((regAt ξ p).map (RingHom.id Ω)) Ω).toSubring = regAt ξ p`. Establish `hmap : (regAt ξ p).map (RingHom.id Ω) = regAt ξ p` using `Subring.map_id _`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `a ha`.

Establish `ha' : IsIntegral ((regAt ξ p).map (RingHom.id Ω)) a` using `ha`. Rewrite `ha'` using `[hmap]`. Take `⟨z, hz⟩` from `IsIntegrallyClosed.isIntegral_iff.1 ha'`. Conclude with `hz ▸ z.2`. Introduce `a ha`.

Establish `ha' : a ∈ (regAt ξ p).map (RingHom.id Ω)` using `by rw [hmap]; exact ha`. Conclude with `isIntegral_algebraMap (x := (⟨a, ha'⟩ : (regAt ξ p).map (RingHom.id Ω)))`. Use `haveI : IsLocalRing (integralClosure ((regAt ξ p).map (RingHom.id Ω)) Ω).toSubring := isLocalRing_of_eq hA`. Use `⟨fun p' hp' => ?_, fun p₁ p₂ h₁ h₂ => ?_⟩` and prove the remaining obligations. Take `⟨P, hP, e⟩` from `h.1 p' hp'`.

Rewrite using `[e]`. Conclude with `le_antisymm ((ofPrime_le P).trans hA.le) (hA.ge.trans (LocalSubring.le_ofPrime _ P))`. Take `⟨P₁, hP₁, e₁⟩` from `h.1 p₁ h₁`. Take `⟨P₂, hP₂, e₂⟩` from `h.1 p₂ h₂`. Take `rfl : P₁ = P₂` from `(IsLocalRing.eq_maximalIdeal hP₁).trans (IsLocalRing.eq_maximalIdeal hP₂).symm`.

Conclude with `(h.2 P₁ hP₁).unique ⟨h₁, e₁⟩ ⟨h₂, e₂⟩`.
-/
theorem normAt_id_elim {X' : Scheme.{0}} {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} (hg : IsCptGen ξ) {f : X' ⟶ X} {p : Cpt ξ}
    (hic : IsIntegrallyClosed (regAt ξ p)) (h : NormAt ξ' f (RingHom.id Ω) p) :
    (∀ p' : Cpt ξ', f p'.1 = p.1 → regAt ξ' p' = regAt ξ p) ∧
      ∀ p₁ p₂ : Cpt ξ', f p₁.1 = p.1 → f p₂.1 = p.1 → p₁ = p₂ := by
  obtain ⟨hloc, hfr, -⟩ := regAt_isLocalRing_isFractionRing_stalk X Ω ξ hg p
  have hA : (integralClosure ((regAt ξ p).map (RingHom.id Ω)) Ω).toSubring = regAt ξ p := by
    have hmap : (regAt ξ p).map (RingHom.id Ω) = regAt ξ p := Subring.map_id _
    apply le_antisymm
    · intro a ha
      have ha' : IsIntegral ((regAt ξ p).map (RingHom.id Ω)) a := ha
      rw [hmap] at ha'
      obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 ha'
      exact hz ▸ z.2
    · intro a ha
      have ha' : a ∈ (regAt ξ p).map (RingHom.id Ω) := by rw [hmap]; exact ha
      exact isIntegral_algebraMap (x := (⟨a, ha'⟩ : (regAt ξ p).map (RingHom.id Ω)))
  haveI : IsLocalRing (integralClosure ((regAt ξ p).map (RingHom.id Ω)) Ω).toSubring := isLocalRing_of_eq hA
  refine ⟨fun p' hp' => ?_, fun p₁ p₂ h₁ h₂ => ?_⟩
  · obtain ⟨P, hP, e⟩ := h.1 p' hp'
    rw [e]
    exact le_antisymm ((ofPrime_le P).trans hA.le) (hA.ge.trans (LocalSubring.le_ofPrime _ P))
  · obtain ⟨P₁, hP₁, e₁⟩ := h.1 p₁ h₁
    obtain ⟨P₂, hP₂, e₂⟩ := h.1 p₂ h₂
    obtain rfl : P₁ = P₂ := (IsLocalRing.eq_maximalIdeal hP₁).trans (IsLocalRing.eq_maximalIdeal hP₂).symm
    exact (h.2 P₁ hP₁).unique ⟨h₁, e₁⟩ ⟨h₂, e₂⟩

/- English proof (translation)
Introduce `x`. Set `p : Cpt ξ` to `⟨x, hall x⟩`. Take `⟨-, hf, ⟨e⟩⟩` from `regAt_isLocalRing_isFractionRing_stalk X Ω ξ hg p`. Use `⟨Function.Injective.isDomain (genMap ξ p) (hg.inj p), ?_⟩` and prove the remaining obligations. Establish `: IsIntegrallyClosed (regAt ξ p)` using `(isIntegrallyClosed_iff Ω).2 fun {a} ha => ⟨⟨a, hN p a ha⟩, rfl⟩`.

Conclude with `IsIntegrallyClosed.of_equiv e.symm`.
-/
theorem isNormalScheme_of_normalCpt (hg : IsCptGen ξ) (hall : ∀ q : X, genPt ξ ⤳ q) (hN : Flat.NormalCpt ξ) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X := by
  intro x
  let p : Cpt ξ := ⟨x, hall x⟩
  obtain ⟨-, hf, ⟨e⟩⟩ := regAt_isLocalRing_isFractionRing_stalk X Ω ξ hg p
  refine ⟨Function.Injective.isDomain (genMap ξ p) (hg.inj p), ?_⟩
  have : IsIntegrallyClosed (regAt ξ p) := (isIntegrallyClosed_iff Ω).2 fun {a} ha => ⟨⟨a, hN p a ha⟩, rfl⟩
  exact IsIntegrallyClosed.of_equiv e.symm

/- English proof (translation)
Establish `hnat : ∀ m : ℕ, (m : Ω) ≠ 0 → unitAt ξ p (m : Ω)`. Introduce `m`. Proceed by induction on `m using Nat.recOnMul with`. Consider the case `zero => intro h; exact absurd (by simp) h`. Consider the case `one => intro _`.

Simplify using `using Flat.ZUnit.one`. Consider the case `prime r hr => intro _`. Conclude with `not_not.1 (hp r hr)`. Consider the case `mul a b ha hb`. Introduce `h`.

Rewrite `h`, the goal using `[Nat.cast_mul]`. Conclude with `Flat.ZUnit.mul (ha (left_ne_zero_of_mul h)) (hb (right_ne_zero_of_mul h))`. Break down `Int.natAbs_eq n with e | e` into its components or cases. Rewrite `hn`, the goal using `[e]`. Simplify using `only [Int.cast_natCast] at hn ⊢`.

Conclude with `hnat _ hn`. Rewrite `hn`, the goal using `[e]`. Simplify using `only [Int.cast_neg, Int.cast_natCast, ne_eq, neg_eq_zero] at hn ⊢`. Establish `h` using `hnat _ hn`. Conclude with `⟨neg_ne_zero.2 h.1, neg_mem h.2.1, by rw [inv_neg]; exact neg_mem h.2.2⟩`.
-/
theorem unitAt_int {p : Cpt ξ} (hp : ∀ r : ℕ, r.Prime → ¬ InFibre ξ r p) {n : ℤ} (hn : (n : Ω) ≠ 0) :
    unitAt ξ p (n : Ω) := by
  have hnat : ∀ m : ℕ, (m : Ω) ≠ 0 → unitAt ξ p (m : Ω) := by
    intro m
    induction m using Nat.recOnMul with
    | zero => intro h; exact absurd (by simp) h
    | one => intro _; simpa using Flat.ZUnit.one
    | prime r hr => intro _; exact not_not.1 (hp r hr)
    | mul a b ha hb =>
      intro h
      rw [Nat.cast_mul] at h ⊢
      exact Flat.ZUnit.mul (ha (left_ne_zero_of_mul h)) (hb (right_ne_zero_of_mul h))
  rcases Int.natAbs_eq n with e | e
  · rw [e] at hn ⊢
    simp only [Int.cast_natCast] at hn ⊢
    exact hnat _ hn
  · rw [e] at hn ⊢
    simp only [Int.cast_neg, Int.cast_natCast, ne_eq, neg_eq_zero] at hn ⊢
    have h := hnat _ hn
    exact ⟨neg_ne_zero.2 h.1, neg_mem h.2.1, by rw [inv_neg]; exact neg_mem h.2.2⟩

/- English proof (translation)
Proceed by induction on `he using Submodule.span_induction with`. Consider the case `mem e he`. Take `⟨v, hv1, hv2⟩` from `he`. Use `Submodule.subset_span ⟨v ≫ act a, ?_, ?_⟩` and prove the remaining obligations. Use `show _ ≫ (v ≫ act a).left = _`.

Rewrite using `[Over.comp_left, ← Category.assoc, hv1, ← Over.comp_left, MonObj.one_comp]`. Rewrite using `[h a e, Over.comp_left, hv2, Over.comp_left]`. Conclude with `Category.assoc _ _ _`. Consider the case `zero => simpa using (M.lat p).zero_mem`. Consider the case `add x y _ _ hx hy => simpa using (M.lat p).add_mem hx hy`.

Consider the case `smul c x _ hx`. Establish `: ρ a (c • x) = c • ρ a x` using `by show ρ a ((c : Ω) • x) = (c : Ω) • ρ a x`. Conclude with `map_smul _ _ _`. Rewrite using `[this]`. Conclude with `(M.lat p).smul_mem c hx`.
-/
theorem lat_stable {G : Over X} [GrpObj G] (M : LieModel G ξ Li) {O : Type} [CommRing O] (act : O → (G ⟶ G))
    [∀ a, IsMonHom (act a)] (ρ : O →+* Module.End Ω Li) (h : M.IsActOf act ρ) (p : Cpt ξ) (a : O) (e : Li)
    (he : e ∈ M.lat p) : ρ a e ∈ M.lat p := by
  induction he using Submodule.span_induction with
  | mem e he =>
    obtain ⟨v, hv1, hv2⟩ := he
    refine Submodule.subset_span ⟨v ≫ act a, ?_, ?_⟩
    · show _ ≫ (v ≫ act a).left = _
      rw [Over.comp_left, ← Category.assoc, hv1, ← Over.comp_left, MonObj.one_comp]
    · rw [h a e, Over.comp_left, hv2, Over.comp_left]
      exact Category.assoc _ _ _
  | zero => simpa using (M.lat p).zero_mem
  | add x y _ _ hx hy => simpa using (M.lat p).add_mem hx hy
  | smul c x _ hx =>
    have : ρ a (c • x) = c • ρ a x := by
      show ρ a ((c : Ω) • x) = (c : Ω) • ρ a x
      exact map_smul _ _ _
    rw [this]
    exact (M.lat p).smul_mem c hx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Take `⟨E', _, _, ⟨M₁⟩⟩` from `lieModel_exists X' t'.G Ω ξ'`. Take `⟨j, hj₁, hj₂, hj₃, hj₄, -⟩` from `GlobalTheory.T.lie_model_dominant_hodge E H X t X' t' g m Ω Ω ξ ξ' (RingHom.id Ω) Li E' M M₁ hg hg' hd`. Establish `hinj : Function.Injective j`. Use `(injective_iff_map_eq_zero j).2 fun e he => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h0`.

Establish `h1 : LinearIndependent Ω (fun _ : Fin 1 => e)` using `LinearIndependent.of_subsingleton 0 h0`. Conclude with `(hj₃ 1 _ h1).ne_zero 0 he`. Establish `hsurj : Function.Surjective j`. Set `S : Submodule Ω E'` to `{ carrier := Set.range j add_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, map_add j a b⟩ zero_mem' := ⟨0, map_zero j⟩ smul_mem' := by rintro c _ ⟨a, rfl⟩; exact ⟨c • a, hj₂ c a⟩ }`. Establish `hS : S = ⊤` using `top_le_iff.1 (hj₄ ▸ Submodule.span_le.2 fun x hx => hx)`.

Introduce `x`. Establish `: x ∈ S` using `hS ▸ Submodule.mem_top`. Conclude with `this`. Set `M₂ : LieModel t'.G ξ' Li` to `{ pt := fun e => M₁.pt (j e) tan := fun e => M₁.tan _ inj := M₁.inj.comp hinj onto := fun v hv => by`. Take `⟨e', rfl⟩` from `M₁.onto v hv`.

Take `⟨e, rfl⟩` from `hsurj e'`. Conclude with `⟨e, rfl⟩`. Use `add := fun e e' => by rw [map_add, M₁.add]`. Use `smul := fun c e => by rw [hj₂]; exact M₁.smul c (j e) }`. Establish `hcanc : ∀ v w : epsAt ξ' ⟶ t'.G, v.left ≫ m.φ = w.left ≫ m.φ → v = w`.

Introduce `v w h`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `m.cart.1.hom_ext h ?_` and prove the remaining obligations. Rewrite using `[Over.w v, Over.w w]`. Take `⟨j₂, hj₂₁, -, -, -, hlat⟩` from `GlobalTheory.T.lie_model_dominant_hodge E H X t X' t' g m Ω Ω ξ ξ' (RingHom.id Ω) Li Li M M₂ hg hg' hd`.

Establish `hid : j₂ = AddMonoidHom.id Li`. Use extensionality with `e`. Conclude with `M₂.inj (hcanc _ _ ((hj₂₁ e).trans (hj₁ e).symm))`. Use `⟨M₂, hj₁, hid ▸ hlat, fun a e => hcanc _ _ ?_⟩` and prove the remaining obligations. Establish `h1` using `ha a e`.

Use `show (M₂.pt (ρ a e)).left ≫ m.φ = (M₂.pt e ≫ t'.act.act a).left ≫ m.φ`. Rewrite using `[Over.comp_left, Category.assoc, m.act a, ← Category.assoc]`. Use `show (M₁.pt (j (ρ a e))).left ≫ m.φ = ((M₁.pt (j e)).left ≫ m.φ) ≫ _`. Rewrite using `[hj₁, hj₁, h1, Over.comp_left, Category.assoc]`.
-/
theorem exists_lieModel_pull {X' : Scheme.{0}} (t : SAB H X) (t' : SAB H X') (g : X' ⟶ X) (m : SABMap t' t g)
    (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (M : LieModel t.G ξ Li) (ρ : 𝓞 E →+* Module.End Ω Li) (hg : IsCptGen ξ)
    (hg' : IsCptGen ξ') (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ g (RingHom.id Ω)) (ha : M.IsActOf t.act.act ρ) :
    ∃ M' : LieModel t'.G ξ' Li, (∀ e, (M'.pt e).left ≫ m.φ = spMap (dualMap (RingHom.id Ω)) ≫ (M.pt e).left) ∧
      M'.lat = M.lat.pull ξ' g (AddMonoidHom.id Li) ∧ M'.IsActOf t'.act.act ρ := by
  obtain ⟨E', _, _, ⟨M₁⟩⟩ := lieModel_exists X' t'.G Ω ξ'
  obtain ⟨j, hj₁, hj₂, hj₃, hj₄, -⟩ := GlobalTheory.T.lie_model_dominant_hodge E H X t X' t' g m Ω Ω ξ ξ' (RingHom.id Ω) Li E' M M₁ hg hg' hd
  have hinj : Function.Injective j := by
    refine (injective_iff_map_eq_zero j).2 fun e he => ?_
    by_contra h0
    have h1 : LinearIndependent Ω (fun _ : Fin 1 => e) := LinearIndependent.of_subsingleton 0 h0
    exact (hj₃ 1 _ h1).ne_zero 0 he
  have hsurj : Function.Surjective j := by
    let S : Submodule Ω E' :=
      { carrier := Set.range j
        add_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, map_add j a b⟩
        zero_mem' := ⟨0, map_zero j⟩
        smul_mem' := by rintro c _ ⟨a, rfl⟩; exact ⟨c • a, hj₂ c a⟩ }
    have hS : S = ⊤ := top_le_iff.1 (hj₄ ▸ Submodule.span_le.2 fun x hx => hx)
    intro x
    have : x ∈ S := hS ▸ Submodule.mem_top
    exact this
  let M₂ : LieModel t'.G ξ' Li :=
    { pt := fun e => M₁.pt (j e)
      tan := fun e => M₁.tan _
      inj := M₁.inj.comp hinj
      onto := fun v hv => by
        obtain ⟨e', rfl⟩ := M₁.onto v hv
        obtain ⟨e, rfl⟩ := hsurj e'
        exact ⟨e, rfl⟩
      add := fun e e' => by rw [map_add, M₁.add]
      smul := fun c e => by rw [hj₂]; exact M₁.smul c (j e) }
  have hcanc : ∀ v w : epsAt ξ' ⟶ t'.G, v.left ≫ m.φ = w.left ≫ m.φ → v = w := by
    intro v w h
    apply Over.OverMorphism.ext
    refine m.cart.1.hom_ext h ?_
    rw [Over.w v, Over.w w]
  obtain ⟨j₂, hj₂₁, -, -, -, hlat⟩ := GlobalTheory.T.lie_model_dominant_hodge E H X t X' t' g m Ω Ω ξ ξ' (RingHom.id Ω) Li Li M M₂ hg hg' hd
  have hid : j₂ = AddMonoidHom.id Li := by
    ext e
    exact M₂.inj (hcanc _ _ ((hj₂₁ e).trans (hj₁ e).symm))
  refine ⟨M₂, hj₁, hid ▸ hlat, fun a e => hcanc _ _ ?_⟩
  have h1 := ha a e
  show (M₂.pt (ρ a e)).left ≫ m.φ = (M₂.pt e ≫ t'.act.act a).left ≫ m.φ
  rw [Over.comp_left, Category.assoc, m.act a, ← Category.assoc]
  show (M₁.pt (j (ρ a e))).left ≫ m.φ = ((M₁.pt (j e)).left ≫ m.φ) ≫ _
  rw [hj₁, hj₁, h1, Over.comp_left, Category.assoc]

end GlobalTheory.CompanionTheory.Ar.SatModel

namespace GlobalTheory.CompanionTheory.Ar.SatModel

open Classical in

/- English proof (translation)
Use `haveI : Fintype (CMType H ⊕ CMType H) := Fintype.ofFinite _`. Establish `hl` using `GlobalTheory.T.label_embedding_injective E H l c`. Establish `hinj : Function.Injective fun s : CMType H ⊕ CMType H => cst.comp (labelEmb c s)`. Introduce `s s' h`. Conclude with `hl.1 (RingHom.ext fun a => cst.injective (congrArg (fun φ : 𝓞 E →+* Ω => φ a) h))`.

Establish `hcard : Fintype.card (CMType H ⊕ CMType H) = Module.finrank ℚ E`. Rewrite using `[← Nat.card_eq_fintype_card]`. Conclude with `hl.2`. Use `⟨(GlobalTheory.T.eigenspace_decomposition_internal Ω Li E ρ _ _ hinj hcard).submodule_iSupIndep, ?_⟩` and prove the remaining obligations. Establish `hvb` using `(GlobalTheory.T.lie_omega_lattice_vector_bundle X Ω ξ t.G Li M hg t.semi.smooth).1`.

Use `(GlobalTheory.T.lattice_eigen_vector_bundle X Ω ξ Li E ρ M.lat {q | ∀ r : ℕ, r.Prime → ¬ InFibre ξ r q} (Module.finrank Ω Li) _ (fun s : CMType H ⊕ CMType H => cst.comp (labelEmb c s)) hg hinj hcard ?_ ?_ ?_ ?_).2` as an intermediate fact. Conclude with `this`. Introduce `p _`. Conclude with `hvb p trivial |>.imp fun U h => ⟨h.1, h.2.imp fun b hb => ⟨hb.1, fun q _ hq => hb.2 q trivial hq⟩⟩`. Introduce `p _ a e he haveI := t.act.hom`.

Conclude with `lat_stable M t.act.act ρ hact p a e he`. Introduce `p hp s a`. Establish `hf` using `(regAt_isLocalRing_isFractionRing_stalk X Ω ξ hg p).2.1`. Use `hint p hp` as an intermediate fact. Establish `hi : IsIntegral ℤ (cst (labelEmb c s a))` using `(RingOfIntegers.isIntegral a).map (cst.comp (labelEmb c s)).toIntAlgHom`.

Take `⟨z, hz⟩` from `IsIntegrallyClosed.isIntegral_iff.1 (hi.tower_top (A := regAt ξ p))`. Conclude with `hz ▸ z.2`. Introduce `p hp`. Use `unitAt_int hp ?_` and prove the remaining obligations. Conclude with `NumberField.discr_ne_zero E` after adjusting the coercions.
-/
theorem lat_eq_iSup_of_char0 {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    {X : Scheme.{0}} (t : SAB H X) {Ω : Type} [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hg : IsCptGen ξ) (cst : c.F →+* Ω) {Li : Type} [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li)
    (ρ : 𝓞 E →+* Module.End Ω Li) (hact : M.IsActOf t.act.act ρ)
    (hint : ∀ q : Cpt ξ, (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → IsIntegrallyClosed (regAt ξ q)) :
    iSupIndep (fun s : CMType H ⊕ CMType H => eigSp ρ (cst.comp (labelEmb c s))) ∧
    ∀ q : Cpt ξ, (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) →
      M.lat q = ⨆ s : CMType H ⊕ CMType H, M.lat.inter (eigSp ρ (cst.comp (labelEmb c s))) q := by
  haveI : Fintype (CMType H ⊕ CMType H) := Fintype.ofFinite _
  have hl := GlobalTheory.T.label_embedding_injective E H l c
  have hinj : Function.Injective fun s : CMType H ⊕ CMType H => cst.comp (labelEmb c s) := by
    intro s s' h
    exact hl.1 (RingHom.ext fun a => cst.injective (congrArg (fun φ : 𝓞 E →+* Ω => φ a) h))
  have hcard : Fintype.card (CMType H ⊕ CMType H) = Module.finrank ℚ E := by
    rw [← Nat.card_eq_fintype_card]; exact hl.2
  refine ⟨(GlobalTheory.T.eigenspace_decomposition_internal Ω Li E ρ _ _ hinj hcard).submodule_iSupIndep, ?_⟩
  have hvb := (GlobalTheory.T.lie_omega_lattice_vector_bundle X Ω ξ t.G Li M hg t.semi.smooth).1
  have := (GlobalTheory.T.lattice_eigen_vector_bundle X Ω ξ Li E ρ M.lat {q | ∀ r : ℕ, r.Prime → ¬ InFibre ξ r q} (Module.finrank Ω Li) _
    (fun s : CMType H ⊕ CMType H => cst.comp (labelEmb c s)) hg hinj hcard ?_ ?_ ?_ ?_).2
  · exact this
  · intro p _
    exact hvb p trivial |>.imp fun U h => ⟨h.1, h.2.imp fun b hb => ⟨hb.1, fun q _ hq => hb.2 q trivial hq⟩⟩
  · intro p _ a e he
    haveI := t.act.hom
    exact lat_stable M t.act.act ρ hact p a e he
  · intro p hp s a
    have hf := (regAt_isLocalRing_isFractionRing_stalk X Ω ξ hg p).2.1
    have := hint p hp
    have hi : IsIntegral ℤ (cst (labelEmb c s a)) := (RingOfIntegers.isIntegral a).map (cst.comp (labelEmb c s)).toIntAlgHom
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hi.tower_top (A := regAt ξ p))
    exact hz ▸ z.2
  · intro p hp
    refine unitAt_int hp ?_
    exact_mod_cast NumberField.discr_ne_zero E

end GlobalTheory.CompanionTheory.Ar.SatModel

namespace GlobalTheory.CompanionTheory.Ar

open SatModel in

/- English proof (translation)
Establish `hg : IsCptGen ξ` using `htie.gen`. Establish `hvb` using `(GlobalTheory.T.lie_omega_lattice_vector_bundle X Ω ξ t.G Li M hg t.semi.smooth).1`. Take `⟨c₀, u, hc₀, hsemi, hjc, hbind, -⟩` from `id hgf`. Establish `hgp : Flat.ZLat.gp ξ ∈ {q : Cpt ξ | ∀ r : ℕ, r.Prime → ¬ InFibre ξ r q}`. Introduce `r hr hn`.

Conclude with `hn (Flat.ZLat.unitAt_gp hg (Nat.cast_ne_zero.2 hr.ne_zero))`. Establish `hspan : ∀ s, Submodule.span Ω (Set.range (b s)) = eigSp ρ (cst.comp (labelEmb c s))` using `fun s => span_eq_of_isFlagVBOn hg hvb hgp (hfl s)`. Set `x : ((k : K) → J k) → Ω` to `fun c' => ∏ k, y ⟨k, c' k⟩`. Establish `hover : ξ ≫ (specZIsTerminal.from X) = Spec.map (CommRingCat.ofHom (algebraMap ℤ Ω))` using `specZIsTerminal.hom_ext _ _`. Establish `hw : ∃ l, x l ≠ 0`.

Take `⟨l, hl⟩` from `htie.cover (Flat.ZLat.gp ξ)`. Conclude with `⟨l, hl.1⟩`. Take `⟨κ', _, y0, M', g, hd, hN, hch, hflag, -, hnorm⟩` from `GlobalTheory.T.FlagModelStatement_holds ℤ Ω ((k : K) → J k) x (PModel.mk X ξ (specZIsTerminal.from X) hover hall htie) Unit (fun _ => (k : K) → J k) (fun _ => x) (CMType H ⊕ CMType H) Li (fun _ => M.lat) (fun _ => Module.finrank Ω Li) (labelRk D) (fun _ => ⊤) b (fun _ => hw) (fun …`. Establish `hd' : GlobalTheory.CompanionTheory.Ar.Dominates M'.ξ ξ g (RingHom.id Ω)` using `hd`. Establish `hξ : M'.ξ ≫ g = ξ`.

Establish `: M'.ξ ≫ g = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ ξ` using `hd'`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Establish `hg' : IsCptGen M'.ξ` using `M'.tie.gen`. Take `⟨K₁, _, J₁, _, y₁, bk, bx, -, hbk, hy₁, tie₁, -⟩` from `GlobalTheory.T.segre_refine_line_bundles ℤ Ω κ' y0 M' K J y Empty Empty.elim (hch ()) (fun a => a.elim)`.

Choose the witnesses or unpack the hypotheses as in `⟨t', ⟨m₁⟩⟩ : ∃ t' : SAB H M'.X, Nonempty (SABMap t' t g) := by`. Take `⟨_, _, _, _, _, m₁, -⟩` from `sabPull Out.proved_CubePullSt g t`. Conclude with `⟨_, ⟨m₁⟩⟩`. Take `⟨n, hn⟩` from `sabComp pullCubComp E H Y.X X M'.X Y.t t t' f g m m₁`. Take `⟨Ml, hMl, hlat, hactl⟩` from `exists_lieModel_pull t t' g m₁ M'.ξ M ρ hg hg' hd' hact`.

Establish `hsub : ∀ s, (Ml.eigLat ρ (cst.comp (labelEmb c s))).IsFlagVBOn Set.univ (b s)`. Introduce `s`. Establish `h` using `hflag s`. Rewrite `h` using `[hspan s, ← hlat]`. Conclude with `h`.

Establish `hNs : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M'.X` using `isNormalScheme_of_normalCpt hg' M'.all hN`. Establish `hpatch : ∀ (L₀ : Lat M'.ξ Li) (Lp : ℕ → Lat M'.ξ Li), Lat.patch ∅ L₀ Lp = L₀` using `Lat.patch_empty`. Set `𝔐 : HodgeCpt Y ∅ y₁` to `{ X := M'.X ξ := M'.ξ all := M'.all tie := tie₁ normal := hNs f := g ≫ f Ω₀ := Ω₀ ξ₀ := ξ₀ gen₀ := hgen₀ cst := cst cst_over := by`. Establish `e : M'.ξ ≫ (g ≫ f) ≫ Y.s = (M'.ξ ≫ g) ≫ f ≫ Y.s` using `by simp only [Category.assoc]`. Conclude with `e.trans (by rw [hξ]; exact hcst)`.

Use `fn := algebraMap Ω₀ Ω`. Use `fn_over := by`. Establish `e : M'.ξ ≫ g ≫ f = (M'.ξ ≫ g) ≫ f` using `by simp only [Category.assoc]`. Conclude with `e.trans (by rw [hξ]; exact hdom)`. Use `t := t'`.

Use `m := n`. Use `Li := Li`. Use `M := Ml`. Use `ρ := ρ`. Use `act := hactl`.

Use `S_prime := by simp`. Use `R := fun _ => 0`. Use `R_ge := by simp`. Use `tors := by simp`. Use `vb := fun s => by`.

Rewrite using `[hpatch]`. Establish `h` using `isVBOn_of_isFlagVBOn (hsub s)`. Rewrite `h` using `[hspan s]`. Conclude with `h }`. Establish `hV : ∀ s, 𝔐.V s = 𝔐.dR s` using `fun s => hpatch _ _`.

Set `Fl : 𝔐.Flag` to `{ b := b sub := fun s => by`. Rewrite using `[hV s]`. Conclude with `hsub s`. Use `Li₀ := Li₀`. Use `M₀ := M₀`.

Use `j := j`. Use `j_pt := fun e => by show (Ml.pt (j e)).left ≫ n.φ = spMap (dualMap (algebraMap Ω₀ Ω)) ≫ (M₀.pt e).left`. Rewrite using `[hn, ← Category.assoc, hMl, spMap_dualMap_id, Category.id_comp]`. Conclude with `hj e`. Use `V₀ := V₀`.

Use `V₀_mem := hV₀`. Use `deg := d`. Use `generic := by`. Establish `e : (algebraMap Ω₀ Ω).toAlgebra = ‹Algebra Ω₀ Ω›` using `Algebra.algebra_ext _ _ fun _ => rfl`. Use `show letI := (algebraMap Ω₀ Ω).toAlgebra`.

Use `IsGenericFlag (Ω' := Ω) j V₀ b d`. Rewrite using `[e]`. Conclude with `hgf }`. Take `⟨hind, hsum⟩` from `lat_eq_iSup_of_char0 c t ξ hg cst M ρ hact hint`. Establish `hnormAt : ∀ p : Cpt ξ, (∀ r : ℕ, r.Prime → ¬ InFibre ξ r p) → NormAt M'.ξ g (RingHom.id Ω) p`.

Introduce `p hp`. Use `hnorm p (fun _ => htie.cover p) fun σ n => ?_` and prove the remaining obligations. Conclude with `exists_frame_map_mkQ hind (hsum p hp) b (fun s => IsFlagVBOn_mono (hfl s) (Set.singleton_subset_iff.2 hp)) σ n`. Establish `hdown : ∀ (q : Cpt M'.ξ), (∀ r : ℕ, r.Prime → ¬ InFibre M'.ξ r q) → ∀ h : genPt ξ ⤳ g q.1, ∀ r : ℕ, r.Prime → ¬ InFibre ξ r ⟨g q.1, h⟩`. Introduce `q hq h r hr hn`.

Take `⟨h', -, h2⟩` from `RegAtDom.regAt_dominates X Ω ξ M'.X Ω M'.ξ g (RingHom.id Ω) hd' q`. Conclude with `hn (h2 hg' _ (natCast_mem _ r) (not_not.1 (hq r hr)))`. Use `⟨K₁, inferInstance, J₁, inferInstance, y₁, bk, bx, 𝔐, g, Fl, hbk, hy₁, hξ, rfl, rfl, rfl, fun s i => ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show (Ml.pt (b s i)).left ≫ n.φ = _`. Rewrite using `[hn, ← Category.assoc, hMl, spMap_dualMap_id, Category.id_comp]`.

Introduce `q hq h`. Conclude with `(normAt_id_elim hg (hint _ (hdown q hq h)) (hnormAt _ (hdown q hq h))).1 q rfl`. Introduce `q₁ q₂ hq e`. Take `⟨h, -⟩` from `RegAtDom.regAt_dominates X Ω ξ M'.X Ω M'.ξ g (RingHom.id Ω) hd' q₁`. Conclude with `(normAt_id_elim hg (hint _ (hdown q₁ hq h)) (hnormAt _ (hdown q₁ hq h))).2 q₁ q₂ rfl e.symm`.
-/
theorem SatModel.exists_flagged_model (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (f : X ⟶ Y.X) (Ω₀ : Type) [Field Ω₀] [Algebra Ω₀ Ω] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X) (cst : c.F →+* Ω) (t : SAB H X) (m : SABMap t Y.t f) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (ρ : 𝓞 E →+* Module.End Ω Li) (Li₀ : Type) [AddCommGroup Li₀] [Module Ω₀ Li₀] (M₀ : LieModel Y.t.G ξ₀ Li₀) (j : Li₀ →+ Li) (V₀ : CMType H ⊕ CMType H → Submodule Ω₀ Li₀) (b : ∀ s, Fin (labelRk D s) → Li) (d : ℕ)
    (hall : ∀ q : X, genPt ξ ⤳ q) (htie : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩))
    (hint : ∀ q : Cpt ξ, (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → IsIntegrallyClosed (regAt ξ q))
    (hgen₀ : IsCptGen ξ₀) (hdom : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f (algebraMap Ω₀ Ω))
    (hcst : ξ ≫ f ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F))) (hact : M.IsActOf t.act.act ρ)
    (hj : ∀ e, (M.pt (j e)).left ≫ m.φ = spMap (dualMap (algebraMap Ω₀ Ω)) ≫ (M₀.pt e).left)
    (hV₀ : ∀ s e, e ∈ V₀ s ↔ j e ∈ eigSp ρ (cst.comp (labelEmb c s)))
    (hgf : IsGenericFlag (Ω' := Ω) j V₀ b d)
    (hfl : ∀ s, (M.eigLat ρ (cst.comp (labelEmb c s))).IsFlagVBOn {q | ∀ r : ℕ, r.Prime → ¬ InFibre ξ r q} (b s)) :
    ∃ (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω) (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (𝔐 : HodgeCpt Y ∅ y') (g : 𝔐.X ⟶ X) (Fl : 𝔐.Flag), Function.Injective bk ∧ (∀ k a, y' ⟨bk k, bx k a⟩ = y ⟨k, a⟩) ∧ 𝔐.ξ ≫ g = ξ ∧ 𝔐.f = g ≫ f ∧ genPt 𝔐.ξ₀ = genPt ξ₀ ∧ Fl.deg = d ∧ (∀ s i, (𝔐.M.pt (Fl.b s i)).left ≫ 𝔐.m.φ = (M.pt (b s i)).left ≫ m.φ) ∧ (∀ q' : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q') → ∀ h : genPt ξ ⤳ g q'.1, regAt 𝔐.ξ q' = regAt ξ ⟨g q'.1, h⟩) ∧ ∀ q₁ q₂ : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q₁) → g q₁.1 = g q₂.1 → q₁ = q₂ := by
  classical
  have hg : IsCptGen ξ := htie.gen
  have hvb := (GlobalTheory.T.lie_omega_lattice_vector_bundle X Ω ξ t.G Li M hg t.semi.smooth).1
  obtain ⟨c₀, u, hc₀, hsemi, hjc, hbind, -⟩ := id hgf

  have hgp : Flat.ZLat.gp ξ ∈ {q : Cpt ξ | ∀ r : ℕ, r.Prime → ¬ InFibre ξ r q} := by
    intro r hr hn
    exact hn (Flat.ZLat.unitAt_gp hg (Nat.cast_ne_zero.2 hr.ne_zero))
  have hspan : ∀ s, Submodule.span Ω (Set.range (b s)) = eigSp ρ (cst.comp (labelEmb c s)) := fun s =>
    span_eq_of_isFlagVBOn hg hvb hgp (hfl s)

  let x : ((k : K) → J k) → Ω := fun c' => ∏ k, y ⟨k, c' k⟩
  have hover : ξ ≫ (specZIsTerminal.from X) = Spec.map (CommRingCat.ofHom (algebraMap ℤ Ω)) := specZIsTerminal.hom_ext _ _
  have hw : ∃ l, x l ≠ 0 := by
    obtain ⟨l, hl⟩ := htie.cover (Flat.ZLat.gp ξ)
    exact ⟨l, hl.1⟩
  obtain ⟨κ', _, y0, M', g, hd, hN, hch, hflag, -, hnorm⟩ := GlobalTheory.T.FlagModelStatement_holds ℤ Ω ((k : K) → J k) x
    (PModel.mk X ξ (specZIsTerminal.from X) hover hall htie) Unit (fun _ => (k : K) → J k) (fun _ => x)
    (CMType H ⊕ CMType H) Li (fun _ => M.lat) (fun _ => Module.finrank Ω Li) (labelRk D) (fun _ => ⊤) b
    (fun _ => hw) (fun _ => hvb) hbind (fun _ _ => trivial)
  have hd' : GlobalTheory.CompanionTheory.Ar.Dominates M'.ξ ξ g (RingHom.id Ω) := hd
  have hξ : M'.ξ ≫ g = ξ := by
    have : M'.ξ ≫ g = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ ξ := hd'
    rw [this]
    simp
  have hg' : IsCptGen M'.ξ := M'.tie.gen
  obtain ⟨K₁, _, J₁, _, y₁, bk, bx, -, hbk, hy₁, tie₁, -⟩ := GlobalTheory.T.segre_refine_line_bundles ℤ Ω κ' y0 M' K J y Empty Empty.elim
    (hch ()) (fun a => a.elim)
  obtain ⟨t', ⟨m₁⟩⟩ : ∃ t' : SAB H M'.X, Nonempty (SABMap t' t g) := by
    obtain ⟨_, _, _, _, _, m₁, -⟩ := sabPull Out.proved_CubePullSt g t
    exact ⟨_, ⟨m₁⟩⟩
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H Y.X X M'.X Y.t t t' f g m m₁
  obtain ⟨Ml, hMl, hlat, hactl⟩ := exists_lieModel_pull t t' g m₁ M'.ξ M ρ hg hg' hd' hact
  have hsub : ∀ s, (Ml.eigLat ρ (cst.comp (labelEmb c s))).IsFlagVBOn Set.univ (b s) := by
    intro s
    have h := hflag s
    rw [hspan s, ← hlat] at h
    exact h
  have hNs : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M'.X := isNormalScheme_of_normalCpt hg' M'.all hN
  have hpatch : ∀ (L₀ : Lat M'.ξ Li) (Lp : ℕ → Lat M'.ξ Li), Lat.patch ∅ L₀ Lp = L₀ := Lat.patch_empty
  let 𝔐 : HodgeCpt Y ∅ y₁ :=
    { X := M'.X
      ξ := M'.ξ
      all := M'.all
      tie := tie₁
      normal := hNs
      f := g ≫ f
      Ω₀ := Ω₀
      ξ₀ := ξ₀
      gen₀ := hgen₀
      cst := cst
      cst_over := by
        have e : M'.ξ ≫ (g ≫ f) ≫ Y.s = (M'.ξ ≫ g) ≫ f ≫ Y.s := by simp only [Category.assoc]
        exact e.trans (by rw [hξ]; exact hcst)
      fn := algebraMap Ω₀ Ω
      fn_over := by
        have e : M'.ξ ≫ g ≫ f = (M'.ξ ≫ g) ≫ f := by simp only [Category.assoc]
        exact e.trans (by rw [hξ]; exact hdom)
      t := t'
      m := n
      Li := Li
      M := Ml
      ρ := ρ
      act := hactl
      S_prime := by simp
      R := fun _ => 0
      R_ge := by simp
      tors := by simp
      vb := fun s => by
        rw [hpatch]
        have h := isVBOn_of_isFlagVBOn (hsub s)
        rw [hspan s] at h
        exact h }
  have hV : ∀ s, 𝔐.V s = 𝔐.dR s := fun s => hpatch _ _
  let Fl : 𝔐.Flag :=
    { b := b
      sub := fun s => by
        rw [hV s]
        exact hsub s
      Li₀ := Li₀
      M₀ := M₀
      j := j
      j_pt := fun e => by
        show (Ml.pt (j e)).left ≫ n.φ = spMap (dualMap (algebraMap Ω₀ Ω)) ≫ (M₀.pt e).left
        rw [hn, ← Category.assoc, hMl, spMap_dualMap_id, Category.id_comp]
        exact hj e
      V₀ := V₀
      V₀_mem := hV₀
      deg := d
      generic := by
        have e : (algebraMap Ω₀ Ω).toAlgebra = ‹Algebra Ω₀ Ω› := Algebra.algebra_ext _ _ fun _ => rfl
        show letI := (algebraMap Ω₀ Ω).toAlgebra; IsGenericFlag (Ω' := Ω) j V₀ b d
        rw [e]
        exact hgf }
  obtain ⟨hind, hsum⟩ := lat_eq_iSup_of_char0 c t ξ hg cst M ρ hact hint
  have hnormAt : ∀ p : Cpt ξ, (∀ r : ℕ, r.Prime → ¬ InFibre ξ r p) → NormAt M'.ξ g (RingHom.id Ω) p := by
    intro p hp
    refine hnorm p (fun _ => htie.cover p) fun σ n => ?_
    exact exists_frame_map_mkQ hind (hsum p hp) b
      (fun s => IsFlagVBOn_mono (hfl s) (Set.singleton_subset_iff.2 hp)) σ n
  have hdown : ∀ (q : Cpt M'.ξ), (∀ r : ℕ, r.Prime → ¬ InFibre M'.ξ r q) → ∀ h : genPt ξ ⤳ g q.1,
      ∀ r : ℕ, r.Prime → ¬ InFibre ξ r ⟨g q.1, h⟩ := by
    intro q hq h r hr hn
    obtain ⟨h', -, h2⟩ := RegAtDom.regAt_dominates X Ω ξ M'.X Ω M'.ξ g (RingHom.id Ω) hd' q
    exact hn (h2 hg' _ (natCast_mem _ r) (not_not.1 (hq r hr)))
  refine ⟨K₁, inferInstance, J₁, inferInstance, y₁, bk, bx, 𝔐, g, Fl, hbk, hy₁, hξ, rfl, rfl, rfl, fun s i => ?_, ?_, ?_⟩
  · show (Ml.pt (b s i)).left ≫ n.φ = _
    rw [hn, ← Category.assoc, hMl, spMap_dualMap_id, Category.id_comp]
  · intro q hq h
    exact (normAt_id_elim hg (hint _ (hdown q hq h)) (hnormAt _ (hdown q hq h))).1 q rfl
  · intro q₁ q₂ hq e
    obtain ⟨h, -⟩ := RegAtDom.regAt_dominates X Ω ξ M'.X Ω M'.ξ g (RingHom.id Ω) hd' q₁
    exact (normAt_id_elim hg (hint _ (hdown q₁ hq h)) (hnormAt _ (hdown q₁ hq h))).2 q₁ q₂ rfl e.symm

end GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c Y Ω _ _ K _ J _ y X ξ f Ω₀ _ _ ξ₀ cst t m Li _ _ M ρ Li₀ _ _ M₀ j V₀ b d hall htie hint hgen₀ hdom hcst hact hj hV₀ hgf hfl`. Take `⟨K₁, _, J₁, _, y₁, bk, bx, 𝔐, g, Fl, hbk, hy₁, hξ, hf, hξ₀, hdeg, hpt, hreg, huniq⟩` from `SatModel.exists_flagged_model E H D l Xo c Y Ω K J y X ξ f Ω₀ ξ₀ cst t m Li M ρ Li₀ M₀ j V₀ b d hall htie hint hgen₀ hdom hcst hact hj hV₀ hgf hfl`. Take `⟨K', _, J', _, y', κ, v, tie', xdeg, e, hκ, hy', hroot⟩` from `GlobalTheory.T.hodge_cpt_block_refinement E H D l Xo c _ _ Y ∅ Ω K₁ J₁ y₁ 𝔐 Fl`. Set `𝔑 : HodgeCpt Y ∅ y'` to `{ 𝔐 with tie := tie' }`. Set `Fl' : 𝔑.Flag` to `{ Fl with }`.

Use `⟨K', inferInstance, J', inferInstance, y', κ ∘ bk, fun k => (bx k).trans (v (bk k)), 𝔑, g, Fl', xdeg, e, hκ.comp hbk, fun k a => ?_, hξ, hf, hξ₀, hdeg, hroot, hpt, hreg, huniq⟩` and prove the remaining obligations. Use `show y' ⟨κ (bk k), v (bk k) (bx k a)⟩ = y ⟨k, a⟩`. Rewrite using `[hy', hy₁]`.
-/
theorem exists_sat_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (f : X ⟶ Y.X) (Ω₀ : Type) [Field Ω₀] [Algebra Ω₀ Ω] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X) (cst : c.F →+* Ω) (t : SAB H X) (m : SABMap t Y.t f) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (ρ : 𝓞 E →+* Module.End Ω Li) (Li₀ : Type) [AddCommGroup Li₀] [Module Ω₀ Li₀] (M₀ : LieModel Y.t.G ξ₀ Li₀) (j : Li₀ →+ Li) (V₀ : CMType H ⊕ CMType H → Submodule Ω₀ Li₀) (b : ∀ s, Fin (labelRk D s) → Li) (d : ℕ), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ q : Cpt ξ, (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → IsIntegrallyClosed (regAt ξ q)) → IsCptGen ξ₀ → GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f (algebraMap Ω₀ Ω) → ξ ≫ f ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) → M.IsActOf t.act.act ρ → (∀ e, (M.pt (j e)).left ≫ m.φ = spMap (dualMap (algebraMap Ω₀ Ω)) ≫ (M₀.pt e).left) → (∀ s e, e ∈ V₀ s ↔ j e ∈ eigSp ρ (cst.comp (labelEmb c s))) → IsGenericFlag (Ω' := Ω) j V₀ b d → (∀ s, (M.eigLat ρ (cst.comp (labelEmb c s))).IsFlagVBOn {q | ∀ r : ℕ, r.Prime → ¬ InFibre ξ r q} (b s)) → ∃ (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω) (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (𝔐 : HodgeCpt Y ∅ y') (g : 𝔐.X ⟶ X) (Fl : 𝔐.Flag) (xdeg : RootIx D → K' → ℤ) (e : RootIx D → Ω), Function.Injective bk ∧ (∀ k a, y' ⟨bk k, bx k a⟩ = y ⟨k, a⟩) ∧ 𝔐.ξ ≫ g = ξ ∧ 𝔐.f = g ≫ f ∧ genPt 𝔐.ξ₀ = genPt ξ₀ ∧ Fl.deg = d ∧ Fl.RootLines xdeg e ∧ (∀ s i, (𝔐.M.pt (Fl.b s i)).left ≫ 𝔐.m.φ = (M.pt (b s i)).left ≫ m.φ) ∧ (∀ q' : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q') → ∀ h : genPt ξ ⤳ g q'.1, regAt 𝔐.ξ q' = regAt ξ ⟨g q'.1, h⟩) ∧ ∀ q₁ q₂ : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q₁) → g q₁.1 = g q₂.1 → q₁ = q₂ := by
  intro E _ _ _ H D l Xo c Y Ω _ _ K _ J _ y X ξ f Ω₀ _ _ ξ₀ cst t m Li _ _ M ρ Li₀ _ _ M₀ j V₀ b d hall htie hint
    hgen₀ hdom hcst hact hj hV₀ hgf hfl
  obtain ⟨K₁, _, J₁, _, y₁, bk, bx, 𝔐, g, Fl, hbk, hy₁, hξ, hf, hξ₀, hdeg, hpt, hreg, huniq⟩ :=
    SatModel.exists_flagged_model E H D l Xo c Y Ω K J y X ξ f Ω₀ ξ₀ cst t m Li M ρ Li₀ M₀ j V₀ b d hall htie hint
      hgen₀ hdom hcst hact hj hV₀ hgf hfl
  obtain ⟨K', _, J', _, y', κ, v, tie', xdeg, e, hκ, hy', hroot⟩ :=
    GlobalTheory.T.hodge_cpt_block_refinement E H D l Xo c _ _ Y ∅ Ω K₁ J₁ y₁ 𝔐 Fl
  let 𝔑 : HodgeCpt Y ∅ y' := { 𝔐 with tie := tie' }
  let Fl' : 𝔑.Flag := { Fl with }
  refine ⟨K', inferInstance, J', inferInstance, y', κ ∘ bk, fun k => (bx k).trans (v (bk k)), 𝔑, g, Fl', xdeg, e,
    hκ.comp hbk, fun k a => ?_, hξ, hf, hξ₀, hdeg, hroot, hpt, hreg, huniq⟩
  show y' ⟨κ (bk k), v (bk k) (bx k a)⟩ = y ⟨k, a⟩
  rw [hy', hy₁]

end GlobalTheory.CompanionTheory.Ar
