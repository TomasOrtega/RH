import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.EqOneOfPowEqOneOfCongrOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsEqPowOfTorsionCompEqOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsOddNeZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqOfDominantGeometricPointsOfUnramified
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionZerosTwistLe
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.FiniteOrderFix

open TorsionZero in

/- English proof (translation)
Take `⟨R, _, _, _, 𝒜, _, Φ, -, -, -, hρ⟩` from `SectionRing.exists_sectionRing K X p L hL`. Use `choose ρ hρc hρ using hρ`. Take `⟨i, hi⟩ : ∃ i, genericPoint X ∈ nonzeroLocus (s i)` from `TopologicalSpace.Opens.mem_iSup.1 (by rw [hcov]; trivial)`. Use `letI : Algebra K Γ(X, nonzeroLocus (s i)) := (constHom p _).toAlgebra`. Take `⟨h1, h2, -⟩` from `chart_facts p Φ ρ hL hρc hρ s i hi (fun _ => rfl) (r i) (hr i) (fun f => by`.

Take `⟨F, hF⟩` from `hgen i f`. Conclude with `⟨F, hF.symm⟩)`. Take `⟨f, hfU, hf⟩` from `(haff i).exists_basicOpen_le ⟨_, hU⟩ hi`. Take `⟨F, hF⟩` from `hgen i f`. Take `⟨n, G, hG, hGF⟩` from `exists_homogenisation F i`.

Establish `hG' : (G * MvPolynomial.X i).IsHomogeneous (n + 1)` using `hG.mul (MvPolynomial.isHomogeneous_X K i)`. Establish `hGf : MvPolynomial.aeval (r i) G = f` using `(hGF _ (r i) h1).trans hF.symm`. Establish `hm` using `aeval_mem_of_isHomogeneous 𝒜 (fun j => (Φ N (s j)).2) hG'`. Take `⟨u, hu⟩` from `(Φ (N * (n + 1))).surjective ⟨_, hm⟩`. Establish `hu' : (Φ _ u : R) = MvPolynomial.aeval (fun j => (Φ N (s j) : R)) (G * MvPolynomial.X i)` using `congrArg Subtype.val hu`.

Use `⟨n + 1, u, ?_, fun z hz hzu => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h0`. Establish `h3` using `eq_zero_of_not_mem Φ ρ hL hρ u fun h => by`. Take `⟨k, hk⟩` from `TopologicalSpace.Opens.mem_iSup.1 h`. Establish `e : u.f k = 0` using `by_contra fun e => h0 ⟨k, e⟩`.

Rewrite `hk` using `[e, Scheme.basicOpen_zero]`. Conclude with `hk`. Establish `h4` using `(h2 _ _ hG').1 (hu'.symm.trans h3)`. Rewrite `h4` using `[map_mul, MvPolynomial.aeval_X, h1, _root_.mul_one, hGf]`. Rewrite `hf` using `[h4, Scheme.basicOpen_zero]`.

Conclude with `hf`. Take `⟨ev, hev, hevr⟩` from `exists_ev p Φ ρ hL hρc hρ z hz`. Establish `h3` using `(hev _ u).2 hzu`. Rewrite `h3` using `[hu', map_mul, map_mul, MvPolynomial.aeval_X, mul_ne_zero_iff]`. Establish `hzi` using `(hev _ (s i)).1 h3.2`.

Set `v : Γ(X, nonzeroLocus (s i)) →ₐ[K] K` to `{ TorsionZero.val z _ hzi with commutes' := fun a => val_const p z hz _ hzi a }`. Establish `h4` using `h3.1`. Rewrite `h4` using `[MvPolynomial.comp_aeval_apply, funext fun j => hevr N (s j) (s i) _ hzi (r i j) (hr i j), aeval_mul_of_isHomogeneous _ _ hG, mul_ne_zero_iff]`. Establish `h5 : v f ≠ 0`. Rewrite using `[← hGf, MvPolynomial.comp_aeval_apply]`.

Conclude with `h4.1`. Conclude with `fun y hy => hfU ((val_ne_zero_iff z _ hzi f).1 h5 hy)`.
-/
theorem exists_sec_le {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp K) {L : LB X}
    (hL : L.IsLB) {N : ℕ} {σ : Type} (s : σ → (lbPow L N).Sec)
    (hcov : ⨆ i, nonzeroLocus (s i) = ⊤) (haff : ∀ i, IsAffineOpen (nonzeroLocus (s i)))
    (r : ∀ i, σ → Γ(X, nonzeroLocus (s i)))
    (hr : ∀ i j k, resG X (inf_le_right : nonzeroLocus (s i) ⊓ (lbPow L N).U k ≤ _) ((s j).f k) =
      resG X inf_le_left (r i j) * resG X inf_le_right ((s i).f k))
    (hgen : ∀ i (f : Γ(X, nonzeroLocus (s i))), ∃ F : MvPolynomial σ K,
      f = MvPolynomial.eval₂ (constHom p _) (r i) F)
    (U : X.Opens) (hU : genericPoint X ∈ U) :
    ∃ (d : ℕ) (u : (lbPow L (N * d)).Sec), (∃ j, u.f j ≠ 0) ∧
      ∀ z : Sp K ⟶ X, z ≫ p = 𝟙 _ → ⊤ ≤ z ⁻¹ᵁ nonzeroLocus u → ⊤ ≤ z ⁻¹ᵁ U := by
  obtain ⟨R, _, _, _, 𝒜, _, Φ, -, -, -, hρ⟩ := SectionRing.exists_sectionRing K X p L hL
  choose ρ hρc hρ using hρ
  obtain ⟨i, hi⟩ : ∃ i, genericPoint X ∈ nonzeroLocus (s i) :=
    TopologicalSpace.Opens.mem_iSup.1 (by rw [hcov]; trivial)
  letI : Algebra K Γ(X, nonzeroLocus (s i)) := (constHom p _).toAlgebra
  obtain ⟨h1, h2, -⟩ := chart_facts p Φ ρ hL hρc hρ s i hi (fun _ => rfl) (r i) (hr i) (fun f => by
    obtain ⟨F, hF⟩ := hgen i f
    exact ⟨F, hF.symm⟩)
  obtain ⟨f, hfU, hf⟩ := (haff i).exists_basicOpen_le ⟨_, hU⟩ hi
  obtain ⟨F, hF⟩ := hgen i f
  obtain ⟨n, G, hG, hGF⟩ := exists_homogenisation F i
  have hG' : (G * MvPolynomial.X i).IsHomogeneous (n + 1) := hG.mul (MvPolynomial.isHomogeneous_X K i)
  have hGf : MvPolynomial.aeval (r i) G = f := (hGF _ (r i) h1).trans hF.symm
  have hm := aeval_mem_of_isHomogeneous 𝒜 (fun j => (Φ N (s j)).2) hG'
  obtain ⟨u, hu⟩ := (Φ (N * (n + 1))).surjective ⟨_, hm⟩
  have hu' : (Φ _ u : R) = MvPolynomial.aeval (fun j => (Φ N (s j) : R)) (G * MvPolynomial.X i) :=
    congrArg Subtype.val hu
  refine ⟨n + 1, u, ?_, fun z hz hzu => ?_⟩
  · by_contra h0
    have h3 := eq_zero_of_not_mem Φ ρ hL hρ u fun h => by
      obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h
      have e : u.f k = 0 := by_contra fun e => h0 ⟨k, e⟩
      rw [e, Scheme.basicOpen_zero] at hk
      exact hk
    have h4 := (h2 _ _ hG').1 (hu'.symm.trans h3)
    rw [map_mul, MvPolynomial.aeval_X, h1, _root_.mul_one, hGf] at h4
    rw [h4, Scheme.basicOpen_zero] at hf
    exact hf
  · obtain ⟨ev, hev, hevr⟩ := exists_ev p Φ ρ hL hρc hρ z hz
    have h3 := (hev _ u).2 hzu
    rw [hu', map_mul, map_mul, MvPolynomial.aeval_X, mul_ne_zero_iff] at h3
    have hzi := (hev _ (s i)).1 h3.2
    let v : Γ(X, nonzeroLocus (s i)) →ₐ[K] K :=
      { TorsionZero.val z _ hzi with commutes' := fun a => val_const p z hz _ hzi a }
    have h4 := h3.1
    rw [MvPolynomial.comp_aeval_apply, funext fun j => hevr N (s j) (s i) _ hzi (r i j) (hr i j),
      aeval_mul_of_isHomogeneous _ _ hG, mul_ne_zero_iff] at h4
    have h5 : v f ≠ 0 := by
      rw [← hGf, MvPolynomial.comp_aeval_apply]
      exact h4.1
    exact fun y hy => hfU ((val_ne_zero_iff z _ hzi f).1 h5 hy)

/- English proof (translation)
Break down `Nat.eq_zero_or_pos P.g with hg | hg` into its components or cases. Conclude with `EndOnTorsion.eq_of_dim_zero P P' hg _ _ (hf 0 1 (one_pow _))`. Use `polAV_isIntegral_of_isAlgClosed K P` as an intermediate fact. Use `P'.isAb.proper` as an intermediate fact. Establish `hw : f.left ≫ P'.A.hom = f'.left ≫ P'.A.hom` using `(Over.w f).trans (Over.w f').symm`.

Use `isClosedImmersion_equalizer_ι_of_isSeparated P'.A.hom hw` as an intermediate fact. Set `U : P.A.left.Opens` to `⟨(Set.range (equalizer.ι f.left f'.left))ᶜ, (equalizer.ι f.left f'.left).isClosedEmbedding.isClosed_range.isOpen_compl⟩`. Establish `hU : genericPoint P.A.left ∉ U` using `fun hU => by`. Take `⟨m, s, hcov, hs⟩` from `veryAmple_lbPow h.ample K P 4 le_rfl`. Use `choose haff r hr hgen using hs`.

Take `⟨d, u, hu, hz⟩` from `exists_sec_le P.A.hom P.isLB s hcov haff r hr hgen U hU`. Take `⟨k, hk⟩ : ∃ k, 4 ^ P.g * P.g.factorial * d < (q ^ k) ^ 2` from `⟨_, (Nat.lt_pow_self hq).trans_le (Nat.le_self_pow two_ne_zero _)⟩`. Establish `hM : ((q ^ k : ℕ) : K) ≠ 0` using `by rw [Nat.cast_pow]; exact pow_ne_zero _ hqK`. Establish `hM1 : 1 ≤ q ^ k` using `Nat.one_le_pow _ _ (by omega)`. Establish `hcard` using `(h.mulN (Sp K) P _ hM1).2.2.2.2 K (𝟙 _) hM`.

Establish `h₄` using `card_zeros_on_torsion_coset_le h.mulN SectionRing.exists_sectionRing (PowSec.exists_basis_sections h.globalSectionsRank) (veryAmple_lbPow h.ample) (exists_mulPull_sec h.mulPull) SmoothDim.ringKrullDim_affineOpen polAV_isIntegral_of_isAlgClosed isIntegral_adjoin_of_mul_pow_mem gra …`. Establish `h₅ : ∀ x : baseOver (Sp K) ⟶ P.A, x ^ q ^ k = 1 → ¬ ⊤ ≤ x.left ⁻¹ᵁ nonzeroLocus u` using `fun x hx hx' => (TorsionZero.top_le_iff x.left _).1 (hz x.left (Over.w x) hx') (range_subset_range_equalizer_ι x.left (congrArg (·.left) (hf k x hx)) ⟨_, rfl⟩)`. Establish `e : (q ^ k) ^ (2 * P.g) = (q ^ k) ^ 2 * (q ^ k) ^ (2 * P.g - 2)`. Rewrite using `[← pow_add]`. Use `congr 1`.

Use linear arithmetic over natural numbers and integers. Rewrite `h₄` using `[Nat.card_congr (Equiv.subtypeEquivRight fun x => and_iff_left_of_imp (h₅ x)), hcard, e]`. Conclude with `absurd (Nat.le_of_mul_le_mul_right h₄ (pow_pos hM1 _)) (not_le.2 hk)`. Establish `: IsDominant (equalizer.ι f.left f'.left)` using `⟨dense_iff_closure_eq.2 (top_unique ((genericPoint_spec P.A.left).def.ge.trans (closure_mono (Set.singleton_subset_iff.2 (not_not.1 hU)))))⟩`. Conclude with `Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated P'.A.hom hw _ (equalizer.condition _ _))`.
-/
theorem eq_of_agree_on_pow_torsion (h : Laws) {K : Type} [Field K] [IsAlgClosed K] (P P' : PolAV (Sp K))
    {q : ℕ} (hq : 2 ≤ q) (hqK : (q : K) ≠ 0) (f f' : P.A ⟶ P'.A)
    (hf : ∀ (k : ℕ) (x : baseOver (Sp K) ⟶ P.A), x ^ q ^ k = 1 → x ≫ f = x ≫ f') : f = f' := by
  rcases Nat.eq_zero_or_pos P.g with hg | hg
  · exact EndOnTorsion.eq_of_dim_zero P P' hg _ _ (hf 0 1 (one_pow _))
  have := polAV_isIntegral_of_isAlgClosed K P
  have := P'.isAb.proper
  have hw : f.left ≫ P'.A.hom = f'.left ≫ P'.A.hom := (Over.w f).trans (Over.w f').symm
  have := isClosedImmersion_equalizer_ι_of_isSeparated P'.A.hom hw
  let U : P.A.left.Opens := ⟨(Set.range (equalizer.ι f.left f'.left))ᶜ,
    (equalizer.ι f.left f'.left).isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hU : genericPoint P.A.left ∉ U := fun hU => by
    obtain ⟨m, s, hcov, hs⟩ := veryAmple_lbPow h.ample K P 4 le_rfl
    choose haff r hr hgen using hs
    obtain ⟨d, u, hu, hz⟩ := exists_sec_le P.A.hom P.isLB s hcov haff r hr hgen U hU
    obtain ⟨k, hk⟩ : ∃ k, 4 ^ P.g * P.g.factorial * d < (q ^ k) ^ 2 :=
      ⟨_, (Nat.lt_pow_self hq).trans_le (Nat.le_self_pow two_ne_zero _)⟩
    have hM : ((q ^ k : ℕ) : K) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hqK
    have hM1 : 1 ≤ q ^ k := Nat.one_le_pow _ _ (by omega)
    have hcard := (h.mulN (Sp K) P _ hM1).2.2.2.2 K (𝟙 _) hM
    have h₄ := card_zeros_on_torsion_coset_le h.mulN SectionRing.exists_sectionRing
      (PowSec.exists_basis_sections h.globalSectionsRank) (veryAmple_lbPow h.ample) (exists_mulPull_sec h.mulPull)
      SmoothDim.ringKrullDim_affineOpen polAV_isIntegral_of_isAlgClosed isIntegral_adjoin_of_mul_pow_mem
      graded_bezout_bound K P 4 d (q ^ k) 1 hg le_rfl hM u hu
    have h₅ : ∀ x : baseOver (Sp K) ⟶ P.A, x ^ q ^ k = 1 → ¬ ⊤ ≤ x.left ⁻¹ᵁ nonzeroLocus u :=
      fun x hx hx' => (TorsionZero.top_le_iff x.left _).1 (hz x.left (Over.w x) hx')
        (range_subset_range_equalizer_ι x.left (congrArg (·.left) (hf k x hx)) ⟨_, rfl⟩)
    have e : (q ^ k) ^ (2 * P.g) = (q ^ k) ^ 2 * (q ^ k) ^ (2 * P.g - 2) := by
      rw [← pow_add]; congr 1; omega
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun x => and_iff_left_of_imp (h₅ x)), hcard, e] at h₄
    exact absurd (Nat.le_of_mul_le_mul_right h₄ (pow_pos hM1 _)) (not_le.2 hk)
  have : IsDominant (equalizer.ι f.left f'.left) := ⟨dense_iff_closure_eq.2 (top_unique
    ((genericPoint_spec P.A.left).def.ge.trans (closure_mono (Set.singleton_subset_iff.2 (not_not.1 hU)))))⟩
  exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated P'.A.hom hw _ (equalizer.condition _ _))

open SerreField in

/- English proof (translation)
Establish `hdiv` using `DivisibleHom.exists_eq_pow_of_torsion_comp_eq_one (fun S _ P n hn => ⟨(h.mulN S P n hn).1, (h.mulN S P n hn).2.1, (h.mulN S P n hn).2.2.1, (h.mulN S P n hn).2.2.2.1⟩)`. Establish `hfix'` using `fix_torsion_of_fix_geometric_of_isDominant h.mulN P M (by omega) (by`. Simplify using `using (Nat.cast_ne_zero.2 (by omega) : (M : K) ≠ 0).isUnit.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) (𝟙 _) σ hσ hfix`. Set `τ : P.A ⟶ P.A` to `σ`. Establish `hu : IsMonHom (τ * (𝟙 P.A)⁻¹)`.

Rewrite using `[Hom.mul_def, Hom.inv_def]`. Use `infer_instance`. Take `⟨⟨φ, hφ, e⟩, -⟩` from `hdiv _ P P.A M (by omega) (τ * (𝟙 P.A)⁻¹) hu (fun T x hx => by`. Rewrite using `[MonObj.comp_mul, GrpObj.comp_inv, hfix' T x hx, Category.comp_id, mul_inv_cancel])`. Establish `hpow : ∀ (n : ℕ) (x : P.A ⟶ P.A), (toRing τ ^ n).1 (Additive.ofMul x) = Additive.ofMul (x ≫ (σ ^ n : CategoryTheory.End P.A))` using `fun n x => by`.

Proceed by induction on `n with`. Consider the case `zero => exact congrArg Additive.ofMul (Category.comp_id x).symm`. Consider the case `succ n ih`. Rewrite using `[pow_succ', pow_succ', End.mul_def, ← Category.assoc]`. Conclude with `(congrArg (toRing τ).1 ih).trans (toRing_apply _ _)`.

Establish `key : toRing τ = 1`. Use `eq_one_of_pow_eq_one_of_congr_one (homRing P.A) M hM ?_ ?_ (toRing τ) (toRing φ) m hm ?_ ?_` and prove the remaining obligations. Introduce and unpack `k ⟨f, u, hu, hf⟩ hk e`. Establish `h1` using `congrArg (fun g : homRing P.A => g.1 (Additive.ofMul (𝟙 P.A))) e`. Simplify using `only [natCast_mul_apply, hf, Category.id_comp] at h1`.

Establish `h2 : u ^ k = 1` using `h1`. Take `⟨_, _, _, -⟩` from `h.mulN _ P k (by omega)`. Establish `h3 : u = 1` using `DivisibleHom.cancel_of_flat_surjective (mulA P.A k) (by rw [DivisibleHom.mulA_comp, h2, MonObj.comp_one])`. Conclude with `homRing_ext (by rw [hf, h3, Category.id_comp]; rfl)`. Introduce and unpack `q ⟨f, u, hu, hf⟩ hq e`.

Establish `h3 : u = 1` using `eq_of_agree_on_pow_torsion h P P hq (Nat.cast_ne_zero.2 (by omega)) u 1 fun k x hx => by`. Take `⟨⟨g, v, hv, hg⟩, e⟩` from `e k`. Establish `h1` using `congrArg (fun g : homRing P.A => g.1 (Additive.ofMul (𝟙 P.A))) e`. Simplify using `only [← Nat.cast_pow, natCast_mul_apply, hf, hg, Category.id_comp] at h1`. Establish `h2 : u = v ^ q ^ k` using `h1`.

Rewrite using `[h2, MonObj.comp_pow, ← MonObj.pow_comp, hx, MonObj.one_comp, MonObj.comp_one]`. Conclude with `homRing_ext (by rw [hf, h3, Category.id_comp]; rfl)`. Use `homRing_ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = Additive.ofMul (𝟙 P.A) + ((M : homRing P.A) * toRing φ).1 _`. Rewrite using `[natCast_mul_apply, toRing_apply, toRing_apply, Category.id_comp, Category.id_comp, ← ofMul_pow, ← e, ← ofMul_mul, mul_comm, inv_mul_cancel_right]`.

Conclude with `homRing_ext (by rw [hpow, hord, Category.id_comp]; rfl)`. Establish `h1` using `congrArg (fun g : homRing P.A => g.1 (Additive.ofMul (𝟙 P.A))) key`. Simplify using `only [toRing_apply, Category.id_comp] at h1`. Conclude with `h1`.
-/
theorem eq_one_of_field (h : Laws) {K : Type} [Field K] [IsAlgClosed K] [CharZero K] (P : PolAV (Sp K))
    {M : ℕ} (hM : 3 ≤ M) (σ : CategoryTheory.End P.A) [hσ : IsMonHom (σ : P.A ⟶ P.A)] {m : ℕ} (hm : m ≠ 0)
    (hord : σ ^ m = 1) (hfix : ∀ x : baseOver (Sp K) ⟶ P.A, x ^ M = 1 → x ≫ σ = x) : σ = 1 := by
  have hdiv := DivisibleHom.exists_eq_pow_of_torsion_comp_eq_one (fun S _ P n hn =>
    ⟨(h.mulN S P n hn).1, (h.mulN S P n hn).2.1, (h.mulN S P n hn).2.2.1, (h.mulN S P n hn).2.2.2.1⟩)
  have hfix' := fix_torsion_of_fix_geometric_of_isDominant h.mulN P M (by omega) (by
    simpa using (Nat.cast_ne_zero.2 (by omega) : (M : K) ≠ 0).isUnit.map
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) (𝟙 _) σ hσ hfix
  let τ : P.A ⟶ P.A := σ
  have hu : IsMonHom (τ * (𝟙 P.A)⁻¹) := by
    rw [Hom.mul_def, Hom.inv_def]; infer_instance
  obtain ⟨⟨φ, hφ, e⟩, -⟩ := hdiv _ P P.A M (by omega) (τ * (𝟙 P.A)⁻¹) hu (fun T x hx => by
    rw [MonObj.comp_mul, GrpObj.comp_inv, hfix' T x hx, Category.comp_id, mul_inv_cancel])
  have hpow : ∀ (n : ℕ) (x : P.A ⟶ P.A), (toRing τ ^ n).1 (Additive.ofMul x) =
      Additive.ofMul (x ≫ (σ ^ n : CategoryTheory.End P.A)) := fun n x => by
    induction n with
    | zero => exact congrArg Additive.ofMul (Category.comp_id x).symm
    | succ n ih =>
      rw [pow_succ', pow_succ', End.mul_def, ← Category.assoc]
      exact (congrArg (toRing τ).1 ih).trans (toRing_apply _ _)
  have key : toRing τ = 1 := by
    refine eq_one_of_pow_eq_one_of_congr_one (homRing P.A) M hM ?_ ?_ (toRing τ) (toRing φ) m hm ?_ ?_
    · rintro k ⟨f, u, hu, hf⟩ hk e
      have h1 := congrArg (fun g : homRing P.A => g.1 (Additive.ofMul (𝟙 P.A))) e
      simp only [natCast_mul_apply, hf, Category.id_comp] at h1
      have h2 : u ^ k = 1 := h1
      obtain ⟨_, _, _, -⟩ := h.mulN _ P k (by omega)
      have h3 : u = 1 := DivisibleHom.cancel_of_flat_surjective (mulA P.A k)
        (by rw [DivisibleHom.mulA_comp, h2, MonObj.comp_one])
      exact homRing_ext (by rw [hf, h3, Category.id_comp]; rfl)
    · rintro q ⟨f, u, hu, hf⟩ hq e
      have h3 : u = 1 := eq_of_agree_on_pow_torsion h P P hq (Nat.cast_ne_zero.2 (by omega)) u 1
        fun k x hx => by
          obtain ⟨⟨g, v, hv, hg⟩, e⟩ := e k
          have h1 := congrArg (fun g : homRing P.A => g.1 (Additive.ofMul (𝟙 P.A))) e
          simp only [← Nat.cast_pow, natCast_mul_apply, hf, hg, Category.id_comp] at h1
          have h2 : u = v ^ q ^ k := h1
          rw [h2, MonObj.comp_pow, ← MonObj.pow_comp, hx, MonObj.one_comp, MonObj.comp_one]
      exact homRing_ext (by rw [hf, h3, Category.id_comp]; rfl)
    · refine homRing_ext ?_
      change _ = Additive.ofMul (𝟙 P.A) + ((M : homRing P.A) * toRing φ).1 _
      rw [natCast_mul_apply, toRing_apply, toRing_apply, Category.id_comp, Category.id_comp,
        ← ofMul_pow, ← e, ← ofMul_mul, mul_comm, inv_mul_cancel_right]
    · exact homRing_ext (by rw [hpow, hord, Category.id_comp]; rfl)
  have h1 := congrArg (fun g : homRing P.A => g.1 (Additive.ofMul (𝟙 P.A))) key
  simp only [toRing_apply, Category.id_comp] at h1
  exact h1

/- English proof (translation)
Introduce and unpack `⟨laws, -⟩ S _ P F _ _ _ p h hfst h0 ⟨n, hn, hord⟩ hfix`. Take `⟨P', g, hg, -, pm, -⟩` from `laws.polBaseChange S _ p P`. Establish `hg' : IsPullback (snd (Over.mk p) P.A).left (fst (Over.mk p) P.A).left P.A.hom p` using `(IsPullback.of_hasPullback p P.A.hom).flip`. Set `e` to `hg.isoIsPullback _ _ hg'`. Establish `e₁ : e.hom ≫ (snd (Over.mk p) P.A).left = g` using `hg.isoIsPullback_hom_fst _ _ hg'`.

Establish `e₂ : e.hom ≫ (fst (Over.mk p) P.A).left = P'.A.hom` using `hg.isoIsPullback_hom_snd _ _ hg'`. Establish `e₃ : h.left ≫ (fst (Over.mk p) P.A).left = (fst (Over.mk p) P.A).left` using `congrArg (·.left) hfst`. Set `σ : CategoryTheory.End P'.A` to `Over.homMk (e.hom ≫ h.left ≫ e.inv) (by`. Rewrite using `[← e₂, Category.assoc, Category.assoc, e.inv_hom_id_assoc, e₃])`. Establish `hσ : σ.left ≫ e.hom = e.hom ≫ h.left`.

Express the relevant statement in the definitionally equal form `(e.hom ≫ h.left ≫ e.inv) ≫ e.hom = _`. Simplify using the standard rewrite rules. Establish `hpow : ∀ k : ℕ, (σ ^ k).left ≫ e.hom = e.hom ≫ (h ^ k).left` using `fun k => by`. Proceed by induction on `k with`. Consider the case `zero => exact (Category.id_comp _).trans (Category.comp_id _).symm`.

Consider the case `succ k ih`. Rewrite using `[pow_succ', pow_succ', End.mul_def, End.mul_def, Over.comp_left, Over.comp_left, Category.assoc, hσ, reassoc_of% ih]`. Set `c : Over.mk p ⟶ Over.mk ((baseOver (Sp F)).hom ≫ p)` to `Over.homMk (𝟙 _) (by simp)`. Set `ρ : (baseOver (Sp F) ⟶ P'.A) →* (Over.mk p ⟶ P.A)` to `MonoidHom.mk' (fun x => c ≫ toBase hg.w x) fun x y => by rw [pm, MonObj.comp_mul]`. Establish `hρ : ∀ x, (ptSecT P.A (ρ x)).left = x.left ≫ e.hom` using `fun x => by`.

Use `hg'.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[← Over.comp_left, ptSecT, lift_snd, Category.assoc, e₁]`. Conclude with `Category.id_comp _`. Rewrite using `[← Over.comp_left, ptSecT, lift_fst, Category.assoc, e₂]`. Conclude with `(Over.w x).symm`.

Establish `key : ∀ x, ptSecT P.A (ρ x) ≫ h = ptSecT P.A (ρ x) → x ≫ σ = x` using `fun x hx => by`. Use `congrArg (·.left) hx` as an intermediate fact. Simplify using `only [Over.comp_left, hρ] at this`. Use `Over.OverMorphism.ext ((cancel_mono e.hom).1 ?_)` and prove the remaining obligations. Rewrite using `[Over.comp_left, Category.assoc, hσ, ← Category.assoc, this]`.

Establish `hη : (1 : baseOver (Sp F) ⟶ P'.A) = η[P'.A]` using `(congrArg (· ≫ η[P'.A]) toUnit_unit).trans (Category.id_comp _)`. Establish `: IsMonHom (σ : P'.A ⟶ P'.A)` using `laws.rigidity _ _ _ P'.isAb P'.isAb σ (by`. Use `key 1 (by rw [map_one]; exact h0)` as an intermediate fact. Rewrite using `[hη] at this)` and apply the resulting hypothesis. Establish `h1 : σ = 1` using `eq_one_of_field laws P' le_rfl σ (m := n) (by omega) (Over.OverMorphism.ext ((cancel_mono e.hom).1 ((hpow n).trans (by rw [hord]; exact (hpow 0).symm)))) fun x hx => key x (hfix _ (by rw [← map_pow, hx, map_one]))`.

Use `Over.OverMorphism.ext ((cancel_epi e.hom).1 ?_)` and prove the remaining obligations. Rewrite using `[← hσ, h1]`. Conclude with `hpow 0`.
-/
theorem eq_one_of_finite_order_of_fix_three_torsion :
    LL → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] (p : Spec (CommRingCat.of F) ⟶ S) (h : CategoryTheory.End (Over.mk p ⊗ P.A)), h ≫ fst _ _ = fst _ _ → ptSecT P.A 1 ≫ h = ptSecT P.A 1 → (∃ n, 1 ≤ n ∧ h ^ n = 1) → (∀ x : Over.mk p ⟶ P.A, x ^ 3 = 1 → ptSecT P.A x ≫ h = ptSecT P.A x) → h = 1 := by
  rintro ⟨laws, -⟩ S _ P F _ _ _ p h hfst h0 ⟨n, hn, hord⟩ hfix
  obtain ⟨P', g, hg, -, pm, -⟩ := laws.polBaseChange S _ p P
  have hg' : IsPullback (snd (Over.mk p) P.A).left (fst (Over.mk p) P.A).left P.A.hom p :=
    (IsPullback.of_hasPullback p P.A.hom).flip
  let e := hg.isoIsPullback _ _ hg'
  have e₁ : e.hom ≫ (snd (Over.mk p) P.A).left = g := hg.isoIsPullback_hom_fst _ _ hg'
  have e₂ : e.hom ≫ (fst (Over.mk p) P.A).left = P'.A.hom := hg.isoIsPullback_hom_snd _ _ hg'
  have e₃ : h.left ≫ (fst (Over.mk p) P.A).left = (fst (Over.mk p) P.A).left := congrArg (·.left) hfst
  let σ : CategoryTheory.End P'.A := Over.homMk (e.hom ≫ h.left ≫ e.inv) (by
    rw [← e₂, Category.assoc, Category.assoc, e.inv_hom_id_assoc, e₃])
  have hσ : σ.left ≫ e.hom = e.hom ≫ h.left := by
    change (e.hom ≫ h.left ≫ e.inv) ≫ e.hom = _
    simp
  have hpow : ∀ k : ℕ, (σ ^ k).left ≫ e.hom = e.hom ≫ (h ^ k).left := fun k => by
    induction k with
    | zero => exact (Category.id_comp _).trans (Category.comp_id _).symm
    | succ k ih =>
      rw [pow_succ', pow_succ', End.mul_def, End.mul_def, Over.comp_left, Over.comp_left, Category.assoc, hσ,
        reassoc_of% ih]
  let c : Over.mk p ⟶ Over.mk ((baseOver (Sp F)).hom ≫ p) := Over.homMk (𝟙 _) (by simp)
  let ρ : (baseOver (Sp F) ⟶ P'.A) →* (Over.mk p ⟶ P.A) := MonoidHom.mk' (fun x => c ≫ toBase hg.w x)
    fun x y => by rw [pm, MonObj.comp_mul]
  have hρ : ∀ x, (ptSecT P.A (ρ x)).left = x.left ≫ e.hom := fun x => by
    refine hg'.hom_ext ?_ ?_
    · rw [← Over.comp_left, ptSecT, lift_snd, Category.assoc, e₁]
      exact Category.id_comp _
    · rw [← Over.comp_left, ptSecT, lift_fst, Category.assoc, e₂]
      exact (Over.w x).symm
  have key : ∀ x, ptSecT P.A (ρ x) ≫ h = ptSecT P.A (ρ x) → x ≫ σ = x := fun x hx => by
    have := congrArg (·.left) hx
    simp only [Over.comp_left, hρ] at this
    refine Over.OverMorphism.ext ((cancel_mono e.hom).1 ?_)
    rw [Over.comp_left, Category.assoc, hσ, ← Category.assoc, this]
  have hη : (1 : baseOver (Sp F) ⟶ P'.A) = η[P'.A] :=
    (congrArg (· ≫ η[P'.A]) toUnit_unit).trans (Category.id_comp _)
  have : IsMonHom (σ : P'.A ⟶ P'.A) := laws.rigidity _ _ _ P'.isAb P'.isAb σ (by
    have := key 1 (by rw [map_one]; exact h0)
    rwa [hη] at this)
  have h1 : σ = 1 := eq_one_of_field laws P' le_rfl σ (m := n) (by omega)
    (Over.OverMorphism.ext ((cancel_mono e.hom).1 ((hpow n).trans (by rw [hord]; exact (hpow 0).symm))))
    fun x hx => key x (hfix _ (by rw [← map_pow, hx, map_one]))
  refine Over.OverMorphism.ext ((cancel_epi e.hom).1 ?_)
  rw [← hσ, h1]
  exact hpow 0

end GlobalTheory.FiniteOrderFix
