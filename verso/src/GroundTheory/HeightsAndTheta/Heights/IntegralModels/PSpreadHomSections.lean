import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadHomSections
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsRatDenominators
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsGenericPullInj
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PClearDenominators
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PVectorBundleRestrict
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PGenericSections
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace SpreadHomSections

variable {X : Scheme.{0}} (f : X ⟶ SpecZ) (a : ℤ) (hq : IsUnit (a : ℚ))

/- English proof (translation)
Establish `h` using `h₁ X f U hU`. Rewrite `h` using `[← toInvOpen_ι f ℚ a hq]`. Take `⟨N, hN, c, hc⟩` from `h b`. Conclude with `⟨N, hN, (invOpen f a).ι.app U c, hc⟩`.
-/
lemma exists_app_eq_nsmul (h₁ : RatDenominators.Statement) {U : X.Opens} (hU : IsAffineOpen U)
    (b : Γ(baseChange f ℚ, toInvOpen f ℚ a hq ⁻¹ᵁ ((invOpen f a).ι ⁻¹ᵁ U))) :
    ∃ N : ℕ, 0 < N ∧ ∃ c : Γ((invOpen f a : Scheme.{0}), (invOpen f a).ι ⁻¹ᵁ U),
      (toInvOpen f ℚ a hq).app _ c = N • b := by
  have h := h₁ X f U hU
  rw [← toInvOpen_ι f ℚ a hq] at h
  obtain ⟨N, hN, c, hc⟩ := h b
  exact ⟨N, hN, (invOpen f a).ι.app U c, hc⟩

/- English proof (translation)
Establish `hb` using `(h₂ _ _ (toInvOpen f ℚ a hq) G _ k e he).bijective_self`. Take `⟨b, rfl⟩` from `hb.2 σ`. Use `choose N hN c hc using fun i => exists_app_eq_nsmul f a hq h₁ hU (b i)`. Use `⟨∏ i, N i, Finset.prod_pos fun i _ => hN i, ∑ i, ((∏ j ∈ Finset.univ.erase i, N j) • c i) • e i, ?_⟩` and prove the remaining obligations. Rewrite using `[pullSectionOn_sum, Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_nsmul, hc i, smul_smul, Finset.prod_erase_mul _ _ (Finset.mem_univ i), smul_assoc]`.
-/
lemma exists_pull_eq_nsmul (h₁ : RatDenominators.Statement) (h₂ : PullbackBasis.Statement.{0})
    {U : X.Opens} (hU : IsAffineOpen U) {G : (invOpen f a : Scheme.{0}).Modules} {k : ℕ}
    {e : Fin k → Γ(G, (invOpen f a).ι ⁻¹ᵁ U)} (he : IsBasisOn G _ e)
    (σ : Γ((Scheme.Modules.pullback (toInvOpen f ℚ a hq)).obj G,
      toInvOpen f ℚ a hq ⁻¹ᵁ ((invOpen f a).ι ⁻¹ᵁ U))) :
    ∃ N : ℕ, 0 < N ∧ ∃ τ : Γ(G, (invOpen f a).ι ⁻¹ᵁ U),
      pullSectionOn (toInvOpen f ℚ a hq) G _ τ = N • σ := by
  have hb := (h₂ _ _ (toInvOpen f ℚ a hq) G _ k e he).bijective_self
  obtain ⟨b, rfl⟩ := hb.2 σ
  choose N hN c hc using fun i => exists_app_eq_nsmul f a hq h₁ hU (b i)
  refine ⟨∏ i, N i, Finset.prod_pos fun i _ => hN i,
    ∑ i, ((∏ j ∈ Finset.univ.erase i, N j) • c i) • e i, ?_⟩
  rw [pullSectionOn_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_nsmul, hc i, smul_smul, Finset.prod_erase_mul _ _ (Finset.mem_univ i), smul_assoc]

/- English proof (translation)
Use `choose N hN τ hτ using fun i => exists_pull_eq_nsmul f a hq h₁ h₂ hU he' (φ.app _ (pullSectionOn (toInvOpen f ℚ a hq) F _ (e i)))`. Use `⟨∏ i, N i, Finset.prod_pos fun i _ => hN i, fun V hV s => ?_⟩` and prove the remaining obligations. Take `⟨r, rfl⟩` from `(he V hV).2 s`. Use `⟨∑ i, r i • (G.presheaf.map (homOfLE hV).op).hom ((∏ j ∈ Finset.univ.erase i, N j) • τ i), ?_⟩` and prove the remaining obligations. Establish `hV' : toInvOpen f ℚ a hq ⁻¹ᵁ V ≤ toInvOpen f ℚ a hq ⁻¹ᵁ ((invOpen f a).ι ⁻¹ᵁ U)` using `(Opens.map (toInvOpen f ℚ a hq).base).monotone hV`.

Rewrite using `[pullSectionOn_sum, pullSectionOn_sum, map_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Scheme.Modules.Hom.app_smul, smul_comm]`. Use `congr 1`. Rewrite using `[pullSectionOn_res _ _ hV (homOfLE hV'), pullSectionOn_res _ _ hV (homOfLE hV'), map_nsmul, hτ, smul_smul, Finset.prod_erase_mul _ _ (Finset.mem_univ i), app_map_apply, map_nsmul]`.
-/
lemma exists_pull_eq_nsmul_hom (h₁ : RatDenominators.Statement) (h₂ : PullbackBasis.Statement.{0})
    {U : X.Opens} (hU : IsAffineOpen U) {F G : (invOpen f a : Scheme.{0}).Modules}
    (φ : (Scheme.Modules.pullback (toInvOpen f ℚ a hq)).obj F ⟶
      (Scheme.Modules.pullback (toInvOpen f ℚ a hq)).obj G)
    {k k' : ℕ} {e : Fin k → Γ(F, (invOpen f a).ι ⁻¹ᵁ U)} {e' : Fin k' → Γ(G, (invOpen f a).ι ⁻¹ᵁ U)}
    (he : IsBasisOn F _ e) (he' : IsBasisOn G _ e') :
    ∃ N : ℕ, 0 < N ∧ ∀ (V : (invOpen f a : Scheme.{0}).Opens), V ≤ (invOpen f a).ι ⁻¹ᵁ U →
      ∀ s : Γ(F, V), ∃ τ : Γ(G, V), pullSectionOn (toInvOpen f ℚ a hq) G V τ =
        N • φ.app (toInvOpen f ℚ a hq ⁻¹ᵁ V) (pullSectionOn (toInvOpen f ℚ a hq) F V s) := by
  classical
  choose N hN τ hτ using fun i => exists_pull_eq_nsmul f a hq h₁ h₂ hU he'
    (φ.app _ (pullSectionOn (toInvOpen f ℚ a hq) F _ (e i)))
  refine ⟨∏ i, N i, Finset.prod_pos fun i _ => hN i, fun V hV s => ?_⟩
  obtain ⟨r, rfl⟩ := (he V hV).2 s
  refine ⟨∑ i, r i • (G.presheaf.map (homOfLE hV).op).hom ((∏ j ∈ Finset.univ.erase i, N j) • τ i), ?_⟩
  have hV' : toInvOpen f ℚ a hq ⁻¹ᵁ V ≤ toInvOpen f ℚ a hq ⁻¹ᵁ ((invOpen f a).ι ⁻¹ᵁ U) :=
    (Opens.map (toInvOpen f ℚ a hq).base).monotone hV
  rw [pullSectionOn_sum, pullSectionOn_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Scheme.Modules.Hom.app_smul, smul_comm]
  congr 1
  rw [pullSectionOn_res _ _ hV (homOfLE hV'), pullSectionOn_res _ _ hV (homOfLE hV'), map_nsmul, hτ,
    smul_smul, Finset.prod_erase_mul _ _ (Finset.mem_univ i), app_map_apply, map_nsmul]

end SpreadHomSections

/- English proof (translation)
Introduce `X f _ _ a ha F G hF hG φ`. Take `⟨m₀, hm₀, hinj⟩` from `h₃ X f a ha G hG`. Establish `hq : IsUnit (((a : ℕ) : ℤ) : ℚ)` using `isUnit_intCast_rat a (by exact_mod_cast ha.ne')`. Establish `chart : ∀ y : (invOpen f (a : ℤ) : Scheme.{0}), ∃ U : X.Opens, IsAffineOpen U ∧ y ∈ (invOpen f a).ι ⁻¹ᵁ U ∧ ∃ N : ℕ, 0 < N ∧ ∀ (V : (invOpen f a : Scheme.{0}).Opens), V ≤ (invOpen f a).ι ⁻¹ᵁ U → ∀ s : Γ(F, V), ∃ τ : Γ(G, V), pullSectionOn (toInvOpen f ℚ a (isUnit_intCast_rat a (b …`. Introduce `y`.

Take `⟨U₁, -, hy₁, k, e, he⟩` from `hF y`. Take `⟨U₂, -, hy₂, k', e', he'⟩` from `hG y`. Take `⟨U, hU, hyU, hUle⟩` from `Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (show (invOpen f a).ι.base y ∈ (invOpen f a).ι ''ᵁ (U₁ ⊓ U₂) from ⟨y, ⟨hy₁, hy₂⟩, rfl⟩)`. Establish `hW : (invOpen f a).ι ⁻¹ᵁ U ≤ U₁ ⊓ U₂` using `((Opens.map (invOpen f a).ι.base).monotone hUle).trans ((invOpen f a).ι.preimage_image_eq (U₁ ⊓ U₂)).le`. Take `⟨N, hN, hτ⟩` from `SpreadHomSections.exists_pull_eq_nsmul_hom f a _ h₁ h₂ hU φ (he.restrict (hW.trans inf_le_left)) (he'.restrict (hW.trans inf_le_right))`.

Conclude with `⟨U, hU, hyU, N, hN, hτ⟩`. Establish `hcpt : IsCompact ((invOpen f (a : ℤ) : X.Opens) : Set X)` using `QuasiCompact.isCompact_preimage (f := f) _ (PrimeSpectrum.basicOpen _).isOpen (PrimeSpectrum.isCompact_basicOpen _)`. Establish `: CompactSpace (invOpen f (a : ℤ) : Scheme.{0})` using `isCompact_iff_compactSpace.mp hcpt`. Use `choose U hU hyU N hN hτ using chart`. Take `⟨S, hS⟩` from `isCompact_univ.elim_finite_subcover (fun y => (((invOpen f a).ι ⁻¹ᵁ U y : (invOpen f (a : ℤ) : Scheme.{0}).Opens) : Set (invOpen f (a : ℤ) : Scheme.{0}))) (fun y => ((invOpen f a).ι ⁻¹ᵁ U y).isOpen) (fun y _ => Set.mem_iUnion.2 ⟨y, hyU y⟩)`.

Establish `hcov : ∀ x : (invOpen f (a : ℤ) : Scheme.{0}), ∃ y : S, x ∈ (invOpen f a).ι ⁻¹ᵁ U y`. Introduce `x`. Take `⟨y, hy, hx⟩` from `Set.mem_iUnion₂.1 (hS (Set.mem_univ x))`. Conclude with `⟨⟨y, hy⟩, hx⟩`. Use `⟨m₀ * ∏ y ∈ S, N y, Nat.mul_pos hm₀ (Finset.prod_pos fun y _ => hN y), fun n hn hmn V hV s => ?_⟩` and prove the remaining obligations.

Establish `hinjV` using `hinj n hn (dvd_trans (dvd_mul_right _ _) hmn)`. Establish `loc : ∀ y : S, ∃ t : Γ(G, V ⊓ (invOpen f a).ι ⁻¹ᵁ U y), pullSectionOn (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne'))) G _ t = (((Scheme.Modules.pullback (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne')))).obj G).presheaf.map (homOfLE ((Opens.m …`. Introduce `y`. Take `⟨τ, hτy⟩` from `hτ y (V ⊓ _) inf_le_right ((F.presheaf.map (homOfLE (inf_le_left : V ⊓ (invOpen f a).ι ⁻¹ᵁ U y ≤ V)).op).hom s)`. Establish `hu : IsUnit ((N y : ℕ) : Γ((invOpen f (a : ℤ) : Scheme.{0}), V ⊓ (invOpen f a).ι ⁻¹ᵁ U y))`.

Establish `h1` using `isUnit_intCast_of_le_invOpen ((invOpen f a).ι ≫ f) ((a : ℤ) * n) (V := V ⊓ (invOpen f a).ι ⁻¹ᵁ U y) (inf_le_left.trans hV)`. Establish `hd : ((N y : ℕ) : ℤ) ∣ (a : ℤ) * n`. Use `dvd_mul_of_dvd_right ?_ _` and prove the remaining obligations. Conclude with `(Finset.dvd_prod_of_mem N y.2).trans ((dvd_mul_left _ _).trans hmn)` after adjusting the coercions. Take `⟨c, hc⟩` from `hd`.

Rewrite `h1` using `[hc, Int.cast_mul]`. Conclude with `isUnit_of_mul_isUnit_left h1` after adjusting the coercions. Use `⟨(hu.unit⁻¹).val • τ, ?_⟩` and prove the remaining obligations. Rewrite using `[pullSectionOn_smul, hτy, ← Nat.cast_smul_eq_nsmul (R := Γ(baseChange f ℚ, toInvOpen f ℚ a hq ⁻¹ᵁ (V ⊓ (invOpen f a).ι ⁻¹ᵁ U y))), smul_smul, ← map_natCast ((toInvOpen f ℚ a hq).app (V ⊓ (invOpen f a).ι ⁻¹ᵁ U y)).hom, ← map_mul, IsUnit.val_inv_mul, map_one, one_smul, pullSectionO …`. Use `choose t ht using loc`.

Take `⟨T, hT⟩` from `modules_exists_glue G (V := V) (fun y : S => V ⊓ (invOpen f a).ι ⁻¹ᵁ U y) (fun _ => inf_le_left) (fun x _ => by obtain ⟨y, hy⟩ := hcov x; exact ⟨y, ‹_›, hy⟩) t (fun y z => by`. Apply `hinjV _ (inf_le_left.trans (inf_le_left.trans hV))` to reduce the goal to its premises. Rewrite using `[pullSectionOn_res _ _ inf_le_left (homOfLE ((Opens.map (toInvOpen f ℚ a hq).base).monotone inf_le_left)), pullSectionOn_res _ _ inf_le_right (homOfLE ((Opens.map (toInvOpen f ℚ a hq).base).monotone inf_le_right)), ht, ht, res_res _ _ _ (homOfLE ((Opens.map (toInvOpen f ℚ a hq).b …`. Use `⟨T, ?_⟩` and prove the remaining obligations. Apply `modules_eq_of_locally` to reduce the goal to its premises.

Introduce `z hz`. Take `⟨y, hy⟩` from `hcov ((toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne'))).base z)`. Use `⟨toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne')) ⁻¹ᵁ (V ⊓ (invOpen f a).ι ⁻¹ᵁ U y), (Opens.map _).monotone inf_le_left, ⟨hz, hy⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← pullSectionOn_res _ _ inf_le_left (homOfLE ((Opens.map (toInvOpen f ℚ a hq).base).monotone inf_le_left)), hT, ht]`.
-/
theorem SpreadHomSections.proof (h₁ : RatDenominators.Statement) (h₂ : PullbackBasis.Statement.{0})
    (h₃ : GenericPullInj.Statement) : SpreadHomSections.Statement := by
  classical
  intro X f _ _ a ha F G hF hG φ
  obtain ⟨m₀, hm₀, hinj⟩ := h₃ X f a ha G hG
  have hq : IsUnit (((a : ℕ) : ℤ) : ℚ) := isUnit_intCast_rat a (by exact_mod_cast ha.ne')

  have chart : ∀ y : (invOpen f (a : ℤ) : Scheme.{0}), ∃ U : X.Opens, IsAffineOpen U ∧
      y ∈ (invOpen f a).ι ⁻¹ᵁ U ∧ ∃ N : ℕ, 0 < N ∧
        ∀ (V : (invOpen f a : Scheme.{0}).Opens), V ≤ (invOpen f a).ι ⁻¹ᵁ U →
          ∀ s : Γ(F, V), ∃ τ : Γ(G, V),
            pullSectionOn (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne'))) G V τ =
              N • φ.app (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne')) ⁻¹ᵁ V)
                (pullSectionOn (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne'))) F V s) := by
    intro y
    obtain ⟨U₁, -, hy₁, k, e, he⟩ := hF y
    obtain ⟨U₂, -, hy₂, k', e', he'⟩ := hG y
    obtain ⟨U, hU, hyU, hUle⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show (invOpen f a).ι.base y ∈ (invOpen f a).ι ''ᵁ (U₁ ⊓ U₂) from ⟨y, ⟨hy₁, hy₂⟩, rfl⟩)
    have hW : (invOpen f a).ι ⁻¹ᵁ U ≤ U₁ ⊓ U₂ :=
      ((Opens.map (invOpen f a).ι.base).monotone hUle).trans
        ((invOpen f a).ι.preimage_image_eq (U₁ ⊓ U₂)).le
    obtain ⟨N, hN, hτ⟩ := SpreadHomSections.exists_pull_eq_nsmul_hom f a _ h₁ h₂ hU φ
      (he.restrict (hW.trans inf_le_left)) (he'.restrict (hW.trans inf_le_right))
    exact ⟨U, hU, hyU, N, hN, hτ⟩

  have hcpt : IsCompact ((invOpen f (a : ℤ) : X.Opens) : Set X) :=
    QuasiCompact.isCompact_preimage (f := f) _ (PrimeSpectrum.basicOpen _).isOpen
      (PrimeSpectrum.isCompact_basicOpen _)
  have : CompactSpace (invOpen f (a : ℤ) : Scheme.{0}) := isCompact_iff_compactSpace.mp hcpt
  choose U hU hyU N hN hτ using chart
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover
    (fun y => (((invOpen f a).ι ⁻¹ᵁ U y : (invOpen f (a : ℤ) : Scheme.{0}).Opens) :
      Set (invOpen f (a : ℤ) : Scheme.{0})))
    (fun y => ((invOpen f a).ι ⁻¹ᵁ U y).isOpen) (fun y _ => Set.mem_iUnion.2 ⟨y, hyU y⟩)
  have hcov : ∀ x : (invOpen f (a : ℤ) : Scheme.{0}), ∃ y : S, x ∈ (invOpen f a).ι ⁻¹ᵁ U y := by
    intro x
    obtain ⟨y, hy, hx⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ x))
    exact ⟨⟨y, hy⟩, hx⟩
  refine ⟨m₀ * ∏ y ∈ S, N y, Nat.mul_pos hm₀ (Finset.prod_pos fun y _ => hN y),
    fun n hn hmn V hV s => ?_⟩
  have hinjV := hinj n hn (dvd_trans (dvd_mul_right _ _) hmn)

  have loc : ∀ y : S, ∃ t : Γ(G, V ⊓ (invOpen f a).ι ⁻¹ᵁ U y),
      pullSectionOn (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne'))) G _ t =
        (((Scheme.Modules.pullback (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne')))).obj
          G).presheaf.map (homOfLE ((Opens.map (toInvOpen f ℚ a
            (isUnit_intCast_rat a (by exact_mod_cast ha.ne'))).base).monotone
            (inf_le_left : V ⊓ (invOpen f a).ι ⁻¹ᵁ U y ≤ V))).op).hom
          (φ.app (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne')) ⁻¹ᵁ V)
            (pullSectionOn (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne'))) F V s)) := by
    intro y
    obtain ⟨τ, hτy⟩ := hτ y (V ⊓ _) inf_le_right
      ((F.presheaf.map (homOfLE (inf_le_left : V ⊓ (invOpen f a).ι ⁻¹ᵁ U y ≤ V)).op).hom s)
    have hu : IsUnit ((N y : ℕ) : Γ((invOpen f (a : ℤ) : Scheme.{0}), V ⊓ (invOpen f a).ι ⁻¹ᵁ U y)) := by
      have h1 := isUnit_intCast_of_le_invOpen ((invOpen f a).ι ≫ f) ((a : ℤ) * n)
        (V := V ⊓ (invOpen f a).ι ⁻¹ᵁ U y)
        (inf_le_left.trans hV)
      have hd : ((N y : ℕ) : ℤ) ∣ (a : ℤ) * n := by
        refine dvd_mul_of_dvd_right ?_ _
        exact_mod_cast (Finset.dvd_prod_of_mem N y.2).trans ((dvd_mul_left _ _).trans hmn)
      obtain ⟨c, hc⟩ := hd
      rw [hc, Int.cast_mul] at h1
      exact_mod_cast isUnit_of_mul_isUnit_left h1
    refine ⟨(hu.unit⁻¹).val • τ, ?_⟩
    rw [pullSectionOn_smul, hτy, ← Nat.cast_smul_eq_nsmul (R := Γ(baseChange f ℚ,
      toInvOpen f ℚ a hq ⁻¹ᵁ (V ⊓ (invOpen f a).ι ⁻¹ᵁ U y))), smul_smul,
      ← map_natCast ((toInvOpen f ℚ a hq).app (V ⊓ (invOpen f a).ι ⁻¹ᵁ U y)).hom,
      ← map_mul, IsUnit.val_inv_mul, map_one, one_smul,
      pullSectionOn_res _ _ inf_le_left (homOfLE ((Opens.map (toInvOpen f ℚ a hq).base).monotone inf_le_left)),
      app_map_apply]
  choose t ht using loc

  obtain ⟨T, hT⟩ := modules_exists_glue G (V := V) (fun y : S => V ⊓ (invOpen f a).ι ⁻¹ᵁ U y)
    (fun _ => inf_le_left) (fun x _ => by obtain ⟨y, hy⟩ := hcov x; exact ⟨y, ‹_›, hy⟩) t
    (fun y z => by
      apply hinjV _ (inf_le_left.trans (inf_le_left.trans hV))
      rw [pullSectionOn_res _ _ inf_le_left (homOfLE ((Opens.map (toInvOpen f ℚ a hq).base).monotone inf_le_left)),
        pullSectionOn_res _ _ inf_le_right (homOfLE ((Opens.map (toInvOpen f ℚ a hq).base).monotone inf_le_right)),
        ht, ht, res_res _ _ _ (homOfLE ((Opens.map (toInvOpen f ℚ a hq).base).monotone
          (inf_le_left.trans inf_le_left : V ⊓ (invOpen f a).ι ⁻¹ᵁ U y ⊓ (V ⊓ (invOpen f a).ι ⁻¹ᵁ U z) ≤ V))),
        res_res _ _ _ (homOfLE ((Opens.map (toInvOpen f ℚ a hq).base).monotone
          (inf_le_left.trans inf_le_left : V ⊓ (invOpen f a).ι ⁻¹ᵁ U y ⊓ (V ⊓ (invOpen f a).ι ⁻¹ᵁ U z) ≤ V)))])
  refine ⟨T, ?_⟩
  apply modules_eq_of_locally
  intro z hz
  obtain ⟨y, hy⟩ := hcov ((toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne'))).base z)
  refine ⟨toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne')) ⁻¹ᵁ
    (V ⊓ (invOpen f a).ι ⁻¹ᵁ U y), (Opens.map _).monotone inf_le_left, ⟨hz, hy⟩, ?_⟩
  rw [← pullSectionOn_res _ _ inf_le_left (homOfLE ((Opens.map (toInvOpen f ℚ a hq).base).monotone inf_le_left)), hT, ht]

end

end GroundTheory.Heights₂.Heights.Model
