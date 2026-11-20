import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalSchrodingerModelUniqTransportExistsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFrameHalfInverseStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralMatrixUpImageCompletedHomLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpImageIntegralMatrixMemCompletedHomLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateHalfAnnihilatorMemCompletedHomLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletedHomLatticeStableSplitIdempotentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndicatorVac

/- English proof (translation)
Take `⟨h1, h2, v, ε, hv, h3⟩` from `q.split`. Use `⟨by rw [← map_mul, h1], ?_, v, ε, hv, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.LatVac.cA_cA, mul_comm, h2]`. Rewrite using `[GlobalTheory.LatVac.cA_cA, add_comm, h3]`.
-/
theorem splitC (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) : IsSplitIdem D (cA D q.e) := by
  obtain ⟨h1, h2, v, ε, hv, h3⟩ := q.split
  refine ⟨by rw [← map_mul, h1], ?_, v, ε, hv, ?_⟩
  · rw [GlobalTheory.LatVac.cA_cA, mul_comm, h2]
  · rw [GlobalTheory.LatVac.cA_cA, add_comm, h3]

/- English proof (translation)
Use `q.sec_pr 1` as an intermediate fact. Rewrite `this` using `[map_one, mul_one]`. Conclude with `this`.
-/
theorem e_eq (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) : q.sec 1 = q.e := by
  have := q.sec_pr 1; rw [map_one, mul_one] at this; exact this

/- English proof (translation)
Establish `hp : q.pr e' * q.pr e' = q.pr e'` using `by rw [← map_mul, he]`. Break down `(IsIdempotentElem.iff_eq_zero_or_one.1 hp) with h | h` into its components or cases. Use `left`. Rewrite using `[← q.sec_pr, h, map_zero]`. Use `right`.

Rewrite using `[← q.sec_pr, h, e_eq]`.
-/
theorem mul_e (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (e' : Formalism.L2.Theta.AE D) (he : e' * e' = e') : q.e * e' = 0 ∨ q.e * e' = q.e := by
  have hp : q.pr e' * q.pr e' = q.pr e' := by rw [← map_mul, he]
  rcases (IsIdempotentElem.iff_eq_zero_or_one.1 hp) with h | h
  · left; rw [← q.sec_pr, h, map_zero]
  · right; rw [← q.sec_pr, h, e_eq]

set_option maxHeartbeats 1600000 in
/- English proof (translation)
Take `⟨h1, h2, -⟩` from `he'`. Establish `hc1 : cA D e' * cA D e' = cA D e'` using `by rw [← map_mul, h1]`. Establish `hA` using `mul_e D k q e' h1`. Establish `hB : cA D q.e * e' = 0 ∨ cA D q.e * e' = cA D q.e`. Break down `mul_e D k q (cA D e') hc1 with h | h` into its components or cases.

Use `left`. Use `congrArg (cA D) h` as an intermediate fact. Rewrite `this` using `[map_mul, GlobalTheory.LatVac.cA_cA, map_zero]`. Then use the resulting hypothesis. Use `right`. Use `congrArg (cA D) h` as an intermediate fact.

Rewrite `this` using `[map_mul, GlobalTheory.LatVac.cA_cA]`. Then use the resulting hypothesis. Establish `hu' : ∀ i j, u i j = q.e * e' * u i j + cA D q.e * e' * u i j` using `fun i j => by`. Rewrite using `[mul_assoc, mul_assoc, hu i j, ← add_mul, hsupp i j]`. Establish `hee : q.e * q.e = q.e` using `q.split.1`. Establish `hce : cA D q.e * cA D q.e = cA D q.e` using `by rw [← map_mul, hee]`.

Apply the tactic sequence `rcases hA with hA | hA <;> rcases hB with hB | hB`. Use `left`. Use extensionality with `i j`. Rewrite using `[hu' i j, hA, hB]`. Simplify using the standard rewrite rules.

Use `right`. Use `right`. Introduce `i j`. Rewrite using `[hu' i j, hA, hB, zero_mul, zero_add, ← mul_assoc, hce]`. Use `right`.

Use `left`. Introduce `i j`. Rewrite using `[hu' i j, hA, hB, zero_mul, add_zero, ← mul_assoc, hee]`. It suffices to derive a contradiction. Establish `hpe : q.pr q.e = 1` using `by rw [← e_eq D k q, q.pr_sec]`.

Establish `h7 : q.e = 0`. Break down `mul_e D k q (cA D e') hc1 with h | h` into its components or cases. Establish `h5 : cA D q.e * e' = 0`. Use `congrArg (cA D) h` as an intermediate fact. Rewrite `this` using `[map_mul, GlobalTheory.LatVac.cA_cA, map_zero]`. Then use the resulting hypothesis.

Establish `h6 : cA D q.e = 0` using `hB.symm.trans h5`. Use `congrArg (cA D) h6` as an intermediate fact. Rewrite `this` using `[GlobalTheory.LatVac.cA_cA, map_zero]`. Then use the resulting hypothesis. Combine the equalities or inequalities in the displayed calculation. Rewrite `hpe` using `[h7, map_zero]`.

Conclude with `zero_ne_one hpe`.
-/
theorem cases (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (e' : Formalism.L2.Theta.AE D) (he' : IsSplitIdem D e') {m n : ℕ} (u : Mx D m n)
    (hsupp : ∀ i j, (q.e + cA D q.e) * u i j = u i j) (hu : IsHalf e' u) :
    u = 0 ∨ IsHalf q.e u ∨ IsHalf (cA D q.e) u := by
  obtain ⟨h1, h2, -⟩ := he'
  have hc1 : cA D e' * cA D e' = cA D e' := by rw [← map_mul, h1]
  have hA := mul_e D k q e' h1
  have hB : cA D q.e * e' = 0 ∨ cA D q.e * e' = cA D q.e := by
    rcases mul_e D k q (cA D e') hc1 with h | h
    · left; have := congrArg (cA D) h; rwa [map_mul, GlobalTheory.LatVac.cA_cA, map_zero] at this
    · right; have := congrArg (cA D) h; rwa [map_mul, GlobalTheory.LatVac.cA_cA] at this
  have hu' : ∀ i j, u i j = q.e * e' * u i j + cA D q.e * e' * u i j := fun i j => by
    rw [mul_assoc, mul_assoc, hu i j, ← add_mul, hsupp i j]
  have hee : q.e * q.e = q.e := q.split.1
  have hce : cA D q.e * cA D q.e = cA D q.e := by rw [← map_mul, hee]
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · left; ext i j; rw [hu' i j, hA, hB]; simp
  · right; right; intro i j; rw [hu' i j, hA, hB, zero_mul, zero_add, ← mul_assoc, hce]
  · right; left; intro i j; rw [hu' i j, hA, hB, zero_mul, add_zero, ← mul_assoc, hee]
  · exfalso
    have hpe : q.pr q.e = 1 := by rw [← e_eq D k q, q.pr_sec]
    have h7 : q.e = 0 := by
      rcases mul_e D k q (cA D e') hc1 with h | h
      · have h5 : cA D q.e * e' = 0 := by
          have := congrArg (cA D) h; rwa [map_mul, GlobalTheory.LatVac.cA_cA, map_zero] at this
        have h6 : cA D q.e = 0 := hB.symm.trans h5
        have := congrArg (cA D) h6; rwa [GlobalTheory.LatVac.cA_cA, map_zero] at this
      · calc q.e = q.e * cA D e' := h.symm
          _ = q.e * e' * cA D e' := by rw [hA]
          _ = 0 := by rw [mul_assoc, h2, mul_zero]
    rw [h7, map_zero] at hpe
    exact zero_ne_one hpe

end GlobalTheory.IndicatorVac

open GlobalTheory.IndicatorVac in

/- English proof (translation)
Introduce `D k _ _ _ _ q hU Y Y' _ _ _ _ S T FS FT ψ ψk hψ hc hcond LS LT hS hT hFS hFT`. Establish `hmono : ∀ u, u ∈ latO S T (LS : Set _) (LT : Set _) (· = q.v) → u ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True` using `fun u hu => AddSubgroup.closure_mono (fun w hw => by`. Take `⟨α, h1, _, h3⟩` from `hw`. Conclude with `⟨α, h1, fun v hv => absurd trivial hv, h3⟩) hu`. Establish `hsy : ∀ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) → ∀ u ∈ latO S T (LS : Set _) (LT : Set _) (· = q.v), ψ (symplO S T ((ofSplit q).up FS FT x) u) = 1` using `fun x hx u hu => GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT (hmono _ (GlobalTheory.T.up_image_integral_matrix_mem_completed_hom_lattice D k q hU Y Y' S T FS FT LS LT hS hT hFS hFT x hx)) (hmono _ hu)`.

Prove the components needed by the constructor for the conclusion. Introduce `Tm O hTm hO`. Establish `hE : ∀ u ∈ latO S T (LS : Set _) (LT : Set _) (· = q.v), IsHalf q.e u → heisO ψ S T u (Tm O) = Tm O`. Introduce `u hu he`. Take `⟨x, hx, rfl⟩` from `GlobalTheory.T.exists_integral_matrix_up_image_completed_hom_lattice D k q hU Y Y' S T FS FT LS LT hS hT hFS hFT u hu he`.

Use `(hTm.trans x O O fun t => ?_).symm` and prove the remaining obligations. Rewrite using `[hO]`. Establish `hh : (∀ r s, (t + x) r s ∈ 𝒪[k]) ↔ ∀ r s, t r s ∈ 𝒪[k]`. Use `⟨fun h r s => ?_, fun h r s => ?_⟩` and prove the remaining obligations. Use `sub_mem (h r s) (hx r s)` as an intermediate fact.

Simplify using `using this`. Conclude with `add_mem (h r s) (hx r s)`. Distinguish the cases in `ht : ∀ r s, t r s ∈ 𝒪[k]`. Rewrite using `[Set.indicator_of_mem (show t ∈ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from ht), Set.indicator_of_mem (show t + x ∈ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from hh.2 ht)]`. Rewrite using `[Set.indicator_of_notMem (show t ∉ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from ht), Set.indicator_of_notMem (show t + x ∉ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from fun h => ht (hh.1 h))]`.

Establish `hC : ∀ u ∈ latO S T (LS : Set _) (LT : Set _) (· = q.v), IsHalf (cA D q.e) u → heisO ψ S T u (Tm O) = Tm O`. Introduce `u hu he`. Use `(hTm.modul u he O O fun t => ?_).symm` and prove the remaining obligations. Rewrite using `[hO]`. Distinguish the cases in `ht : ∀ r s, t r s ∈ 𝒪[k]`.

Rewrite using `[hsy t ht u hu, one_mul]`. Rewrite using `[Set.indicator_of_notMem (show t ∉ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from ht), mul_zero]`. Use `⟨hTm.theta O, ?_, ?_⟩` and prove the remaining obligations. Introduce `u hu`. Take `⟨ha, hsupp⟩` from `GlobalTheory.T.completed_hom_lattice_stable_split_idempotent D k q S T LS LT u hu`.

Use `set a : WO S T := Matrix.of fun i j => q.e * u i j with ha_def`. Establish `hb : u - a ∈ latO S T (LS : Set _) (LT : Set _) (· = q.v)` using `sub_mem hu ha`. Establish `hee : q.e * q.e = q.e` using `q.split.1`. Establish `hce : cA D q.e * cA D q.e = cA D q.e` using `by rw [← map_mul, hee]`. Establish `haH0 : IsHalf q.e a` using `fun i j => by`.

Simplify using `only [ha_def, Matrix.of_apply]`. Rewrite using `[← mul_assoc, hee]`. Establish `hbH0 : IsHalf (cA D q.e) (u - a)` using `fun i j => by`. Establish `h1 : (u - a) i j = cA D q.e * u i j`. Simplify using `only [Matrix.sub_apply, ha_def, Matrix.of_apply]`.

Use `hsupp i j` as an intermediate fact. Take the linear combination `-this`. Rewrite using `[h1, ← mul_assoc, hce]`. Establish `haH : IsHalf q.e (a + a)` using `fun i j => by rw [Matrix.add_apply, mul_add, haH0 i j]`. Establish `hbH : IsHalf (cA D q.e) ((u - a) + (u - a))` using `fun i j => by rw [Matrix.add_apply, mul_add, hbH0 i j]`.

Establish `h2 : (2 • u : WO S T) = (a + a) + ((u - a) + (u - a))` using `by rw [two_nsmul]; abel`. Establish `key` using `GlobalTheory.LatVac.heisO_heisO ψ (a + a) ((u - a) + (u - a)) (Tm O)`. Rewrite `key` using `[hC _ (add_mem hb hb) hbH, hE _ (add_mem ha ha) haH, ← h2]`. Establish `hph : ψ (symplOH S T (a + a) ((u - a) + (u - a))) = 1`. Take `⟨x, hx, hxa⟩` from `GlobalTheory.T.exists_integral_matrix_up_image_completed_hom_lattice D k q hU Y Y' S T FS FT LS LT hS hT hFS hFT a ha haH0`.

Establish `h3 : symplOH S T (a + a) ((u - a) + (u - a)) = symplO S T a ((u - a) + (u - a))`. Rewrite using `[symplOH, GlobalTheory.LatVac.symplO_add_left, mul_add, ← add_mul, ← RingHom.map_add, add_halves, RingHom.map_one, one_mul]`. Rewrite using `[h3]`. Use `hsy x hx _ (add_mem hb hb)` as an intermediate fact. Rewrite `this` using `[← hxa]`. Then use the resulting hypothesis.

Rewrite `key` using `[hph, one_smul]`. Conclude with `key.symm`. Introduce `e' he' u hu hue`. Break down `cases D k q e' he' u (GlobalTheory.T.completed_hom_lattice_stable_split_idempotent D k q S T LS LT u hu).2 hue with h | h | h` into its components or cases. Substitute `h` using the available equality.

Conclude with `GlobalTheory.LatVac.heisO_zero ψ _`. Conclude with `hE u hu h`. Conclude with `hC u hu h`. Introduce `f hf`. Establish `h78` using `GlobalTheory.T.heisenberg_frame_half_inverse D k (ofSplit q) Y Y' S T FS FT ψ ψk hc`.

Establish `hth : IsThetaFunO ψ S T f` using `hf.1`. Establish `hlv : IsLatVac (heisO ψ S T) (latO S T (LS : Set _) (LT : Set _) (· = q.v)) f` using `hf.2`. Establish `h1 : ∀ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) → heisO ψ S T ((ofSplit q).up FS FT x) f = f` using `fun x hx => hlv.2 q.e q.split _ (GlobalTheory.T.up_image_integral_matrix_mem_completed_hom_lattice D k q hU Y Y' S T FS FT LS LT hS hT hFS hFT x hx) (h78.1 x).1`. Establish `h2 : ∀ y : WO S T, IsHalf (cA D (ofSplit q).e) y → (∀ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) → ψ (symplO S T ((ofSplit q).up FS FT x) y) = 1) → heisO ψ S T y f = f` using `fun y hy hann => hlv.2 (cA D q.e) (splitC D k q) y (GlobalTheory.T.conjugate_half_annihilator_mem_completed_hom_lattice D k q hU Y Y' S T FS FT LS LT hS hT hFS hFT ψ ψk hψ hc hcond y hy hann) hy`. Take `⟨T₁, hT₁, hT₁O⟩` from `(GlobalTheory.T.localSchrodingerModel_uniq_transport_exists D k (ofSplit q) Y Y' S T FS FT ψ hψ).2.2 f hth h1 h2`.

Conclude with `⟨T₁, hT₁, fun O hO => hT₁O O hO⟩`.
-/
theorem GlobalTheory.LocMod.indicator_vac : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), IsStdChar D ψ (-1) → (ofSplit q).IsChar ψ ψk → HasConductor ψk 1 → ∀ (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → (∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v)) → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) → (∀ Tm O, (ofSplit q).IsModel ψ FS FT Tm → IsOne O → GlobalTheory.FinPl.Vac ψ S T LS LT (· = q.v) (Tm O)) ∧ ∀ f, GlobalTheory.FinPl.Vac ψ S T LS LT (· = q.v) f → ∃ Tm, (ofSplit q).IsModel ψ FS FT Tm ∧ ∀ O, IsOne O → Tm O = f := by
  intro D k _ _ _ _ q hU Y Y' _ _ _ _ S T FS FT ψ ψk hψ hc hcond LS LT hS hT hFS hFT
  have hmono : ∀ u, u ∈ latO S T (LS : Set _) (LT : Set _) (· = q.v) → u ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True :=
    fun u hu => AddSubgroup.closure_mono (fun w hw => by
      obtain ⟨α, h1, _, h3⟩ := hw
      exact ⟨α, h1, fun v hv => absurd trivial hv, h3⟩) hu
  have hsy : ∀ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) → ∀ u ∈ latO S T (LS : Set _) (LT : Set _) (· = q.v),
      ψ (symplO S T ((ofSplit q).up FS FT x) u) = 1 := fun x hx u hu =>
    GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT (hmono _ (GlobalTheory.T.up_image_integral_matrix_mem_completed_hom_lattice D k q hU Y Y' S T FS FT LS LT hS hT hFS hFT x hx)) (hmono _ hu)
  constructor
  · intro Tm O hTm hO
    have hE : ∀ u ∈ latO S T (LS : Set _) (LT : Set _) (· = q.v), IsHalf q.e u → heisO ψ S T u (Tm O) = Tm O := by
      intro u hu he
      obtain ⟨x, hx, rfl⟩ := GlobalTheory.T.exists_integral_matrix_up_image_completed_hom_lattice D k q hU Y Y' S T FS FT LS LT hS hT hFS hFT u hu he
      refine (hTm.trans x O O fun t => ?_).symm
      rw [hO]
      have hh : (∀ r s, (t + x) r s ∈ 𝒪[k]) ↔ ∀ r s, t r s ∈ 𝒪[k] := by
        refine ⟨fun h r s => ?_, fun h r s => ?_⟩
        · have := sub_mem (h r s) (hx r s); simpa using this
        · exact add_mem (h r s) (hx r s)
      by_cases ht : ∀ r s, t r s ∈ 𝒪[k]
      · rw [Set.indicator_of_mem (show t ∈ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from ht),
          Set.indicator_of_mem (show t + x ∈ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from hh.2 ht)]
      · rw [Set.indicator_of_notMem (show t ∉ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from ht),
          Set.indicator_of_notMem (show t + x ∉ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from fun h => ht (hh.1 h))]
    have hC : ∀ u ∈ latO S T (LS : Set _) (LT : Set _) (· = q.v), IsHalf (cA D q.e) u → heisO ψ S T u (Tm O) = Tm O := by
      intro u hu he
      refine (hTm.modul u he O O fun t => ?_).symm
      rw [hO]
      by_cases ht : ∀ r s, t r s ∈ 𝒪[k]
      · rw [hsy t ht u hu, one_mul]
      · rw [Set.indicator_of_notMem (show t ∉ {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} from ht), mul_zero]
    refine ⟨hTm.theta O, ?_, ?_⟩
    · intro u hu
      obtain ⟨ha, hsupp⟩ := GlobalTheory.T.completed_hom_lattice_stable_split_idempotent D k q S T LS LT u hu
      set a : WO S T := Matrix.of fun i j => q.e * u i j with ha_def
      have hb : u - a ∈ latO S T (LS : Set _) (LT : Set _) (· = q.v) := sub_mem hu ha
      have hee : q.e * q.e = q.e := q.split.1
      have hce : cA D q.e * cA D q.e = cA D q.e := by rw [← map_mul, hee]
      have haH0 : IsHalf q.e a := fun i j => by
        simp only [ha_def, Matrix.of_apply]; rw [← mul_assoc, hee]
      have hbH0 : IsHalf (cA D q.e) (u - a) := fun i j => by
        have h1 : (u - a) i j = cA D q.e * u i j := by
          simp only [Matrix.sub_apply, ha_def, Matrix.of_apply]
          have := hsupp i j
          linear_combination -this
        rw [h1, ← mul_assoc, hce]
      have haH : IsHalf q.e (a + a) := fun i j => by rw [Matrix.add_apply, mul_add, haH0 i j]
      have hbH : IsHalf (cA D q.e) ((u - a) + (u - a)) := fun i j => by rw [Matrix.add_apply, mul_add, hbH0 i j]
      have h2 : (2 • u : WO S T) = (a + a) + ((u - a) + (u - a)) := by rw [two_nsmul]; abel
      have key := GlobalTheory.LatVac.heisO_heisO ψ (a + a) ((u - a) + (u - a)) (Tm O)
      rw [hC _ (add_mem hb hb) hbH, hE _ (add_mem ha ha) haH, ← h2] at key
      have hph : ψ (symplOH S T (a + a) ((u - a) + (u - a))) = 1 := by
        obtain ⟨x, hx, hxa⟩ := GlobalTheory.T.exists_integral_matrix_up_image_completed_hom_lattice D k q hU Y Y' S T FS FT LS LT hS hT hFS hFT a ha haH0
        have h3 : symplOH S T (a + a) ((u - a) + (u - a)) = symplO S T a ((u - a) + (u - a)) := by
          rw [symplOH, GlobalTheory.LatVac.symplO_add_left, mul_add, ← add_mul, ← RingHom.map_add, add_halves,
            RingHom.map_one, one_mul]
        rw [h3]
        have := hsy x hx _ (add_mem hb hb)
        rwa [← hxa] at this
      rw [hph, one_smul] at key
      exact key.symm
    · intro e' he' u hu hue
      rcases cases D k q e' he' u (GlobalTheory.T.completed_hom_lattice_stable_split_idempotent D k q S T LS LT u hu).2 hue with h | h | h
      · subst h; exact GlobalTheory.LatVac.heisO_zero ψ _
      · exact hE u hu h
      · exact hC u hu h
  · intro f hf
    have h78 := GlobalTheory.T.heisenberg_frame_half_inverse D k (ofSplit q) Y Y' S T FS FT ψ ψk hc
    have hth : IsThetaFunO ψ S T f := hf.1
    have hlv : IsLatVac (heisO ψ S T) (latO S T (LS : Set _) (LT : Set _) (· = q.v)) f := hf.2
    have h1 : ∀ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) → heisO ψ S T ((ofSplit q).up FS FT x) f = f :=
      fun x hx => hlv.2 q.e q.split _ (GlobalTheory.T.up_image_integral_matrix_mem_completed_hom_lattice D k q hU Y Y' S T FS FT LS LT hS hT hFS hFT x hx) (h78.1 x).1
    have h2 : ∀ y : WO S T, IsHalf (cA D (ofSplit q).e) y →
        (∀ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) → ψ (symplO S T ((ofSplit q).up FS FT x) y) = 1) →
        heisO ψ S T y f = f := fun y hy hann =>
      hlv.2 (cA D q.e) (splitC D k q) y
        (GlobalTheory.T.conjugate_half_annihilator_mem_completed_hom_lattice D k q hU Y Y' S T FS FT LS LT hS hT hFS hFT ψ ψk hψ hc hcond y hy hann) hy
    obtain ⟨T₁, hT₁, hT₁O⟩ := (GlobalTheory.T.localSchrodingerModel_uniq_transport_exists D k (ofSplit q) Y Y' S T FS FT ψ hψ).2.2 f hth h1 h2
    exact ⟨T₁, hT₁, fun O hO => hT₁O O hO⟩
