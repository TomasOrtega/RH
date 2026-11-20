import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelNotMemRowSG
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnderEqIffMapLe

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.DetIdlValue

variable {X : Fields} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}

/- English proof (translation)
Establish `hu : ∀ v, (sel v).under (𝓞 X.F) = v` using `fun v => HeightOneSpectrum.ext (hsel v)`. Establish `hu' : ∀ v, (conjPrime₂ (sel v)).under (𝓞 X.F) = v` using `fun v => HeightOneSpectrum.ext ((GlobalTheory.MuOffMove.under_conjP hX _).trans (hsel v))`. Establish `hsub : Function.mulSupport (fun v => g (sel v) * g (conjPrime₂ (sel v))) ⊆ (hfin.toFinset.image fun P => P.under (𝓞 X.F) : Finset _)`. Introduce `v hv`. Rewrite using `[Finset.mem_coe, Finset.mem_image]`.

Distinguish the cases in `h : g (sel v) = 1`. Use `⟨conjPrime₂ (sel v), hfin.mem_toFinset.2 fun h' => hv ?_, hu' v⟩` and prove the remaining obligations. Simplify using `only [h, h', mul_one]`. Conclude with `⟨sel v, hfin.mem_toFinset.2 h, hu v⟩`. Rewrite using `[finprod_eq_prod_of_mulSupport_subset _ hsub, finprod_eq_prod _ hfin, ← Finset.prod_fiberwise_of_maps_to (g := fun P : HeightOneSpectrum (𝓞 X.E) => P.under (𝓞 X.F)) fun P hP => Finset.mem_image_of_mem (fun P : HeightOneSpectrum (𝓞 X.E) => P.under (𝓞 X.F)) hP]`.

Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Distinguish the cases in `hc : conjPrime₂ (sel v) = sel v`. Rewrite using `[hc, h1 _ hc, mul_one]`. Use `Finset.prod_eq_one fun w hw => h1 w ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hw'`.

Establish `hwv : w.asIdeal.under (𝓞 X.F) = v.asIdeal` using `congrArg HeightOneSpectrum.asIdeal (Finset.mem_filter.1 hw).2`. Break down `((GlobalTheory.ThetaMove.split_of_conj_ne₂ X w v hX hw' hwv).2 (sel v)).1 (hsel v) with e | e` into its components or cases. Conclude with `hw' (e ▸ hc)`. Rewrite `hc` using `[e, GlobalTheory.CharValCompare.conjP_conjP]`. Conclude with `hw' hc.symm`.

Establish `hsp` using `(GlobalTheory.ThetaMove.split_of_conj_ne₂ X (sel v) v hX hc (hsel v)).2`. Rewrite using `[← Finset.prod_pair (Ne.symm hc)]`. Use `Finset.prod_subset (fun w hw => ?_) fun w hw hw' => ?_` and prove the remaining obligations. Rewrite using `[Finset.mem_insert, Finset.mem_singleton]`. Conclude with `(hsp w).1 (congrArg HeightOneSpectrum.asIdeal (Finset.mem_filter.1 hw).2)`.

Assume the negation of the conclusion as `hg`. Rewrite `hw` using `[Finset.mem_insert, Finset.mem_singleton]`. Conclude with `hw' (Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 hg, HeightOneSpectrum.ext ((hsp w).2 hw)⟩)`.
-/
theorem finprod_group {M : Type} [CommMonoid M] (hX : X.Ok) (hsel : IsSel X sel) (g : HeightOneSpectrum (𝓞 X.E) → M)
    (hfin : (Function.mulSupport g).Finite) (h1 : ∀ w, conjPrime₂ w = w → g w = 1) :
    ∏ᶠ w, g w = ∏ᶠ v, g (sel v) * g (conjPrime₂ (sel v)) := by
  classical
  have hu : ∀ v, (sel v).under (𝓞 X.F) = v := fun v => HeightOneSpectrum.ext (hsel v)
  have hu' : ∀ v, (conjPrime₂ (sel v)).under (𝓞 X.F) = v := fun v =>
    HeightOneSpectrum.ext ((GlobalTheory.MuOffMove.under_conjP hX _).trans (hsel v))
  have hsub : Function.mulSupport (fun v => g (sel v) * g (conjPrime₂ (sel v))) ⊆
      (hfin.toFinset.image fun P => P.under (𝓞 X.F) : Finset _) := by
    intro v hv
    rw [Finset.mem_coe, Finset.mem_image]
    by_cases h : g (sel v) = 1
    · refine ⟨conjPrime₂ (sel v), hfin.mem_toFinset.2 fun h' => hv ?_, hu' v⟩
      simp only [h, h', mul_one]
    · exact ⟨sel v, hfin.mem_toFinset.2 h, hu v⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub, finprod_eq_prod _ hfin,
    ← Finset.prod_fiberwise_of_maps_to (g := fun P : HeightOneSpectrum (𝓞 X.E) => P.under (𝓞 X.F))
      fun P hP => Finset.mem_image_of_mem (fun P : HeightOneSpectrum (𝓞 X.E) => P.under (𝓞 X.F)) hP]
  refine Finset.prod_congr rfl fun v _ => ?_
  by_cases hc : conjPrime₂ (sel v) = sel v
  · rw [hc, h1 _ hc, mul_one]
    refine Finset.prod_eq_one fun w hw => h1 w ?_
    by_contra hw'
    have hwv : w.asIdeal.under (𝓞 X.F) = v.asIdeal := congrArg HeightOneSpectrum.asIdeal (Finset.mem_filter.1 hw).2
    rcases ((GlobalTheory.ThetaMove.split_of_conj_ne₂ X w v hX hw' hwv).2 (sel v)).1 (hsel v) with e | e
    · exact hw' (e ▸ hc)
    · rw [e, GlobalTheory.CharValCompare.conjP_conjP] at hc
      exact hw' hc.symm
  · have hsp := (GlobalTheory.ThetaMove.split_of_conj_ne₂ X (sel v) v hX hc (hsel v)).2
    rw [← Finset.prod_pair (Ne.symm hc)]
    refine Finset.prod_subset (fun w hw => ?_) fun w hw hw' => ?_
    · rw [Finset.mem_insert, Finset.mem_singleton]
      exact (hsp w).1 (congrArg HeightOneSpectrum.asIdeal (Finset.mem_filter.1 hw).2)
    · by_contra hg
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      exact hw' (Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 hg, HeightOneSpectrum.ext ((hsp w).2 hw)⟩)

/- English proof (translation)
Rewrite using `[inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_sub, Int.toNat_sub_toNat_neg]`.
-/
theorem pow_toNat_mul {G : Type} [CommGroup G] (a : G) (k : ℤ) : a ^ k.toNat * a⁻¹ ^ (-k).toNat = a ^ k := by
  rw [inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_sub, Int.toNat_sub_toNat_neg]

/- English proof (translation)
The claim follows from `ordSub_detSub_eq hN (GlobalTheory.CharValCompare.isFr_frameAt (GlobalTheory.CharValCompare.exists_isFr w hN))`.
-/
theorem ordSub_eq_ordDet {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {N : Submodule (𝓞 E) (Sp E n)}
    (hN : Submodule.IsLattice E N) (w : HeightOneSpectrum (𝓞 E)) : GlobalTheory.Mem.Chr.ordSub w (GlobalTheory.Mem.Chr.detSub N) = ordDet w N :=
  ordSub_detSub_eq hN (GlobalTheory.CharValCompare.isFr_frameAt (GlobalTheory.CharValCompare.exists_isFr w hN))

/- English proof (translation)
Introduce `X n sel SB χ σ mU N fr hX hsel hN hT hU`. Use `set g : HeightOneSpectrum (𝓞 X.E) → ℂˣ := fun w => if w ∈ SB ∨ conjPrime₂ w ∈ SB then 1 else χ.val w ^ (ordDet w N).toNat with hg`. Establish `hfin : (Function.mulSupport g).Finite`. Use `(GlobalTheory.OrdDetConj.ordDet_conj_finite X.E n N hN).2.subset fun w hw h0 => hw ?_` and prove the remaining obligations. Simplify using `[hg, h0]`.

Establish `h0 : ∀ w, conjPrime₂ w = w → ordDet w N = 0` using `fun w hw => by`. Use `GlobalTheory.OrdDetConj.ordDet_conjP hN w` as an intermediate fact. Rewrite `this` using `[hw]`. Use linear arithmetic over natural numbers and integers. Establish `h1 : ∀ w, conjPrime₂ w = w → g w = 1` using `fun w hw => by simp [hg, h0 w hw]`.

Establish `e1 : χ.1 (detIdl SB N fr) = (∏ P ∈ SB, χ.locK P (LinearEquiv.det (fr P))) * ∏ᶠ w, g w`. Unfold `detIdl`. Rewrite using `[map_mul, map_prod, MonoidHom.map_finprod _ (finite_detIdl SB hN.1)]`. Use `congr 1`. Use `finprod_congr fun w => ?_` and prove the remaining obligations.

Simplify using `only [hg]`. Use `split_ifs`. Conclude with `map_one _`. Rewrite using `[map_pow, ordSub_eq_ordDet hN.1]`. Both sides reduce to the same expression.

Establish `e2 : ∀ v, σ (GlobalTheory.MuOffMove.term sel SB mU N v) = (((g (sel v) * g (conjPrime₂ (sel v)))⁻¹ : ℂˣ) : ℂ)`. Introduce `v`. Unfold `GlobalTheory.MuOffMove.term`. Distinguish the cases in `hc : conjPrime₂ (sel v) = sel v`. Rewrite using `[hc, h1 _ hc, h0 _ hc]`.

Simplify using the standard rewrite rules. Take `⟨hm, hsp⟩` from `GlobalTheory.ThetaMove.split_of_conj_ne₂ X (sel v) v hX hc (hsel v)`. Distinguish the cases in `hv : sel v ∈ SB ∨ conjPrime₂ (sel v) ∈ SB`. Establish `hv' : ∃ P ∈ SB, P.asIdeal.under (𝓞 X.F) = v.asIdeal` using `hv.elim (fun h => ⟨_, h, (hsp _).2 (Or.inl rfl)⟩) fun h => ⟨_, h, (hsp _).2 (Or.inr rfl)⟩`. Rewrite using `[if_pos hv']`.

Simplify using `only [hg, GlobalTheory.CharValCompare.conjP_conjP]`. Rewrite using `[if_pos hv, if_pos hv.symm]`. Simplify using the standard rewrite rules. Establish `hv' : ¬ ∃ P ∈ SB, P.asIdeal.under (𝓞 X.F) = v.asIdeal`. Introduce and unpack `⟨P, hP, e⟩`.

Break down `(hsp P).1 e with rfl | rfl` into its components or cases. Use `exacts [hv (Or.inl hP), hv (Or.inr hP)]`. Take `⟨ha, hb⟩` from `not_or.1 hv`. Take `⟨u1, s1⟩` from `hU _ ha hb`. Take `⟨u2, -⟩` from `hU _ hb (by rwa [GlobalTheory.CharValCompare.conjP_conjP])`.

Rewrite using `[if_neg hv']`. Simplify using `only [hg, GlobalTheory.CharValCompare.conjP_conjP]`. Rewrite using `[if_neg hv, if_neg fun h => hv (Or.symm h), GlobalTheory.OrdDetConj.ordDet_conjP hN, GlobalTheory.HeckeSplit.val_eq_inv_of_split X.F X.E χ v _ _ hT u1 u2 (Ne.symm hc) hm, pow_toNat_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, s1, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_va …`. Establish `hinj : Function.Injective sel` using `fun v w h => HeightOneSpectrum.ext (by rw [← hsel v, h, hsel w])`. Establish `e3 : σ (muOff sel SB mU N) = (((∏ᶠ w, g w)⁻¹ : ℂˣ) : ℂ)`.

Express the relevant statement in the definitionally equal form `σ (∏ᶠ v, GlobalTheory.MuOffMove.term sel SB mU N v) = _`. Rewrite using `[finprod_group hX hsel g hfin h1, ← finprod_inv_distrib, map_finprod σ (GlobalTheory.MuOffMove.term_finite hsel SB mU hN), finprod_congr e2]`. Conclude with `((Units.coeHom ℂ).map_finprod_of_injective Units.val_injective fun v => (g (sel v) * g (conjPrime₂ (sel v)))⁻¹).symm`. Rewrite using `[e3, e1, Finset.prod_coe_sort SB fun P => ((χ.locK P (LinearEquiv.det (fr P)) : ℂˣ) : ℂ)⁻¹]`. Simplify using `[mul_comm]`.
-/
theorem inv_val_detIdl : ∀ (X : Fields) (n : ℕ) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (SB : Finset (HeightOneSpectrum (𝓞 X.E))) (χ : Formalism.L2.Host.HChar X.E) (σ : X.K →+* ℂ) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (N : Submodule (𝓞 X.E) (Sp X.E n)) (fr : HeightOneSpectrum (𝓞 X.E) → Sp X.E n ≃ₗ[X.E] Sp X.E n), X.Ok → IsSel X sel → IsSdLat N → χ.TrivOn X.F → (∀ w, w ∉ SB → conjPrime₂ w ∉ SB → χ.UnrAt w ∧ σ ((mU w : X.Kˣ) : X.K) = ((χ.val w : ℂˣ) : ℂ)⁻¹) → ((χ.1 (detIdl SB N fr) : ℂˣ) : ℂ)⁻¹ = σ (muOff sel SB mU N) * ∏ P : SB, ((χ.locK P.1 (LinearEquiv.det (fr P.1)) : ℂˣ) : ℂ)⁻¹ := by
  intro X n sel SB χ σ mU N fr hX hsel hN hT hU
  classical
  set g : HeightOneSpectrum (𝓞 X.E) → ℂˣ := fun w =>
    if w ∈ SB ∨ conjPrime₂ w ∈ SB then 1 else χ.val w ^ (ordDet w N).toNat with hg
  have hfin : (Function.mulSupport g).Finite := by
    refine (GlobalTheory.OrdDetConj.ordDet_conj_finite X.E n N hN).2.subset fun w hw h0 => hw ?_
    simp [hg, h0]
  have h0 : ∀ w, conjPrime₂ w = w → ordDet w N = 0 := fun w hw => by
    have := GlobalTheory.OrdDetConj.ordDet_conjP hN w
    rw [hw] at this
    omega
  have h1 : ∀ w, conjPrime₂ w = w → g w = 1 := fun w hw => by simp [hg, h0 w hw]
  have e1 : χ.1 (detIdl SB N fr) = (∏ P ∈ SB, χ.locK P (LinearEquiv.det (fr P))) * ∏ᶠ w, g w := by
    unfold detIdl
    rw [map_mul, map_prod, MonoidHom.map_finprod _ (finite_detIdl SB hN.1)]
    congr 1
    refine finprod_congr fun w => ?_
    simp only [hg]
    split_ifs
    · exact map_one _
    · rw [map_pow, ordSub_eq_ordDet hN.1]
      rfl
  have e2 : ∀ v, σ (GlobalTheory.MuOffMove.term sel SB mU N v) = (((g (sel v) * g (conjPrime₂ (sel v)))⁻¹ : ℂˣ) : ℂ) := by
    intro v
    unfold GlobalTheory.MuOffMove.term
    by_cases hc : conjPrime₂ (sel v) = sel v
    · rw [hc, h1 _ hc, h0 _ hc]
      simp
    · obtain ⟨hm, hsp⟩ := GlobalTheory.ThetaMove.split_of_conj_ne₂ X (sel v) v hX hc (hsel v)
      by_cases hv : sel v ∈ SB ∨ conjPrime₂ (sel v) ∈ SB
      · have hv' : ∃ P ∈ SB, P.asIdeal.under (𝓞 X.F) = v.asIdeal :=
          hv.elim (fun h => ⟨_, h, (hsp _).2 (Or.inl rfl)⟩) fun h => ⟨_, h, (hsp _).2 (Or.inr rfl)⟩
        rw [if_pos hv']
        simp only [hg, GlobalTheory.CharValCompare.conjP_conjP]
        rw [if_pos hv, if_pos hv.symm]
        simp
      · have hv' : ¬ ∃ P ∈ SB, P.asIdeal.under (𝓞 X.F) = v.asIdeal := by
          rintro ⟨P, hP, e⟩
          rcases (hsp P).1 e with rfl | rfl
          exacts [hv (Or.inl hP), hv (Or.inr hP)]
        obtain ⟨ha, hb⟩ := not_or.1 hv
        obtain ⟨u1, s1⟩ := hU _ ha hb
        obtain ⟨u2, -⟩ := hU _ hb (by rwa [GlobalTheory.CharValCompare.conjP_conjP])
        rw [if_neg hv']
        simp only [hg, GlobalTheory.CharValCompare.conjP_conjP]
        rw [if_neg hv, if_neg fun h => hv (Or.symm h), GlobalTheory.OrdDetConj.ordDet_conjP hN,
          GlobalTheory.HeckeSplit.val_eq_inv_of_split X.F X.E χ v _ _ hT u1 u2 (Ne.symm hc) hm, pow_toNat_mul,
          Units.val_zpow_eq_zpow_val, map_zpow₀, s1, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, inv_zpow]
  have hinj : Function.Injective sel := fun v w h => HeightOneSpectrum.ext (by rw [← hsel v, h, hsel w])
  have e3 : σ (muOff sel SB mU N) = (((∏ᶠ w, g w)⁻¹ : ℂˣ) : ℂ) := by
    change σ (∏ᶠ v, GlobalTheory.MuOffMove.term sel SB mU N v) = _
    rw [finprod_group hX hsel g hfin h1, ← finprod_inv_distrib,
      map_finprod σ (GlobalTheory.MuOffMove.term_finite hsel SB mU hN), finprod_congr e2]
    exact ((Units.coeHom ℂ).map_finprod_of_injective Units.val_injective
      fun v => (g (sel v) * g (conjPrime₂ (sel v)))⁻¹).symm
  rw [e3, e1, Finset.prod_coe_sort SB fun P => ((χ.locK P (LinearEquiv.det (fr P)) : ℂˣ) : ℂ)⁻¹]
  simp [mul_comm]

end GlobalTheory.DetIdlValue
