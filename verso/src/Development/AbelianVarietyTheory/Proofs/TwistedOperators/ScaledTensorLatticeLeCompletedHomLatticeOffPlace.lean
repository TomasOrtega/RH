import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LatOEqHatA
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdeleTensorComponentIdempotentSumAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumAddConjIdempotentConjFixed
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteAdeleOfSplitPlacesIdempotentSumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedMatrixGroupOfLocalMultiplierStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultiplierStandardLatticeOfMoverTrivialStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultiplierShiftedLatticeAwayFromPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel.TrOff

section Help
variable {D : D7} {S T : HSp D}

/- English proof (translation)
The claim follows from `Matrix.ext fun i j => mul_add c (x i j) (y i j)`.
-/
theorem partAt_add (c : AE D) (x y : WO S T) :
    GlobalTheory.LiftLevel.partAt c (x + y) = GlobalTheory.LiftLevel.partAt c x + GlobalTheory.LiftLevel.partAt c y :=
  Matrix.ext fun i j => mul_add c (x i j) (y i j)

/- English proof (translation)
The claim follows from `Matrix.ext fun _ _ => mul_zero c`.
-/
theorem partAt_zero (c : AE D) : GlobalTheory.LiftLevel.partAt c (0 : WO S T) = 0 :=
  Matrix.ext fun _ _ => mul_zero c

/- English proof (translation)
The claim follows from `Matrix.ext fun i j => mul_neg c (x i j)`.
-/
theorem partAt_neg (c : AE D) (x : WO S T) : GlobalTheory.LiftLevel.partAt c (-x) = -GlobalTheory.LiftLevel.partAt c x :=
  Matrix.ext fun i j => mul_neg c (x i j)

noncomputable def gm (S T : HSp D) (γ : Af D.host.F) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) : WO S T :=
  Matrix.of fun a k => (pairA D.host.F 0 γ) ⊗ₜ[D.host.F] y k a

/- English proof (translation)
The claim follows from `Matrix.ext fun a k => TensorProduct.tmul_add _ (x k a) (y k a)`.
-/
theorem gm_add (γ : Af D.host.F) (x y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    gm S T γ (x + y) = gm S T γ x + gm S T γ y :=
  Matrix.ext fun a k => TensorProduct.tmul_add _ (x k a) (y k a)

/- English proof (translation)
The claim follows from `Matrix.ext fun a k => TensorProduct.tmul_zero _ _`.
-/
theorem gm_zero (γ : Af D.host.F) : gm S T γ 0 = 0 :=
  Matrix.ext fun a k => TensorProduct.tmul_zero _ _

/- English proof (translation)
The claim follows from `Matrix.ext fun a k => TensorProduct.tmul_neg _ (x k a)`.
-/
theorem gm_neg (γ : Af D.host.F) (x : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    gm S T γ (-x) = -gm S T γ x :=
  Matrix.ext fun a k => TensorProduct.tmul_neg _ (x k a)

/- English proof (translation)
Use `Matrix.ext fun a k => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ)) * ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] y k a) = (pairA D.host.F 0 ((1 - σ) * α)) ⊗ₜ[D.host.F] y k a`. Rewrite using `[sub_mul, one_mul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← TensorProduct.sub_tmul]`. Use `congr 1`. Use `Prod.ext ?_ ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(0 : Ainf D.host.F) - _ * 0 = 0`. Rewrite using `[mul_zero, sub_zero]`. Express the relevant statement in the definitionally equal form `α - σ * α = (1 - σ) * α`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem partAt_gm (σ α : Af D.host.F) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    GlobalTheory.LiftLevel.partAt (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ)) (gm S T α y) =
      gm S T ((1 - σ) * α) y := by
  refine Matrix.ext fun a k => ?_
  change (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ)) * ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] y k a) =
    (pairA D.host.F 0 ((1 - σ) * α)) ⊗ₜ[D.host.F] y k a
  rw [sub_mul, one_mul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    ← TensorProduct.sub_tmul]
  congr 1
  refine Prod.ext ?_ ?_
  · change (0 : Ainf D.host.F) - _ * 0 = 0
    rw [mul_zero, sub_zero]
  · change α - σ * α = (1 - σ) * α
    ring

end Help

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨b, rfl⟩` from `hx`.

Introduce `a`. Use `show IsIntegral ℤ ((Pi.single b 1 : Fin n → E) a)`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Rewrite using `[Pi.single_eq_same]`.

Conclude with `isIntegral_one`. Rewrite using `[Pi.single_eq_of_ne h]`. Conclude with `isIntegral_zero`. Consider the case `zero => intro a`. Conclude with `isIntegral_zero`.

Consider the case `add x y _ _ hx hy => intro a`. Conclude with `(hx a).add (hy a)`. Consider the case `smul c x _ hx => intro a`. Conclude with `(c.2).mul (hx a)`. Introduce `h`.

Establish `e : v = ∑ a, (⟨v a, h a⟩ : 𝓞 E) • (Pi.single a 1 : Fin n → E)`. Use function extensionality and compare the values at `i`. Rewrite using `[Finset.sum_apply, Finset.sum_eq_single i]`. Rewrite using `[Pi.smul_apply, Pi.single_eq_same]`. Express the relevant statement in the definitionally equal form `v i = v i * 1`.

Rewrite using `[mul_one]`. Introduce `b _ hb`. Rewrite using `[Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero]`. Introduce `hi`. Conclude with `absurd (Finset.mem_univ i) hi`.

Rewrite using `[e]`. Conclude with `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)`.
-/
theorem mem_stdL_int {E : Type} [Field E] [NumberField E] {n : ℕ} (v : Fin n → E) :
    v ∈ stdL E n ↔ ∀ a, IsIntegral ℤ (v a) := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      intro a
      show IsIntegral ℤ ((Pi.single b 1 : Fin n → E) a)
      by_cases h : a = b
      · subst h; rw [Pi.single_eq_same]; exact isIntegral_one
      · rw [Pi.single_eq_of_ne h]; exact isIntegral_zero
    | zero => intro a; exact isIntegral_zero
    | add x y _ _ hx hy => intro a; exact (hx a).add (hy a)
    | smul c x _ hx => intro a; exact (c.2).mul (hx a)
  · intro h
    have e : v = ∑ a, (⟨v a, h a⟩ : 𝓞 E) • (Pi.single a 1 : Fin n → E) := by
      funext i
      rw [Finset.sum_apply, Finset.sum_eq_single i]
      · rw [Pi.smul_apply, Pi.single_eq_same]
        change v i = v i * 1
        rw [mul_one]
      · intro b _ hb
        rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [e]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

/- English proof (translation)
Introduce `D n v`. Rewrite using `[mem_stdL_int, mem_stdL_int]`. Use `forall_congr' fun a => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ ↔ IsIntegral ℤ (star (v a))`. Conclude with `⟨fun h => h.map (starRingEnd D.host.E).toIntAlgHom, fun h => by`.

Use `h.map (starRingEnd D.host.E).toIntAlgHom` as an intermediate fact. Rewrite using `[show (starRingEnd D.host.E).toIntAlgHom (star (v a)) = v a from star_star (v a)] at this⟩` and apply the resulting hypothesis.
-/
theorem star_stdL : ∀ (D : D7) (n : ℕ) (v : Fin n → D.host.E), v ∈ stdL D.host.E n ↔ star v ∈ stdL D.host.E n := by
  intro D n v
  rw [mem_stdL_int, mem_stdL_int]
  refine forall_congr' fun a => ?_
  change _ ↔ IsIntegral ℤ (star (v a))
  exact ⟨fun h => h.map (starRingEnd D.host.E).toIntAlgHom, fun h => by
    have := h.map (starRingEnd D.host.E).toIntAlgHom
    rwa [show (starRingEnd D.host.E).toIntAlgHom (star (v a)) = v a from star_star (v a)] at this⟩

/- English proof (translation)
Introduce `D S T k₀ f hT hf h i j`. Set `i₀ : Fin T.rank` to `⟨0, hT⟩`. Set `x : WO S T` to `Matrix.of fun a b => if a = i₀ ∧ b = i then f else 0`. Establish `hx : IsHalf f x` using `fun a b => by`. Simplify using `only [x, Matrix.of_apply]`.

Use `split_ifs`. Conclude with `hf`. Conclude with `mul_zero f`. Establish `h1` using `congrFun (congrFun (h x hx) i₀) j`. Unfold `actO at h1`.

Rewrite `h1` using `[GlobalTheory.AdelicLatMove.mt_one, Matrix.one_mul, Matrix.mul_apply, Finset.sum_eq_single i]`. Simplify using `only [x, Matrix.of_apply, true_and, if_true] at h1`. Rewrite using `[Matrix.sub_apply, mul_sub, h1, Matrix.one_apply]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[hij, Ne.symm hij]`. Introduce `b _ hb`. Simplify using `[x, hb]`. Introduce `hi`.

Conclude with `absurd (Finset.mem_univ i) hi`.
-/
theorem rowTriv : ∀ (D : D7) (S T : HSp D) (k₀ : GA D S) (f : AE D), 0 < T.rank → f * f = f → (∀ x : WO S T, IsHalf f x → actO S T k₀ 1 x = x) → ∀ i j, f * (mt S k₀⁻¹ - 1) i j = 0 := by
  intro D S T k₀ f hT hf h i j
  let i₀ : Fin T.rank := ⟨0, hT⟩
  let x : WO S T := Matrix.of fun a b => if a = i₀ ∧ b = i then f else 0
  have hx : IsHalf f x := fun a b => by
    simp only [x, Matrix.of_apply]
    split_ifs
    · exact hf
    · exact mul_zero f
  have h1 := congrFun (congrFun (h x hx) i₀) j
  unfold actO at h1
  rw [GlobalTheory.AdelicLatMove.mt_one, Matrix.one_mul, Matrix.mul_apply, Finset.sum_eq_single i] at h1
  · simp only [x, Matrix.of_apply, true_and, if_true] at h1
    rw [Matrix.sub_apply, mul_sub, h1, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  · intro b _ hb
    simp [x, hb]
  · intro hi; exact absurd (Finset.mem_univ i) hi

end GlobalTheory.LiftLevel.TrOff

namespace GlobalTheory.LiftLevel

open GlobalTheory.LiftLevel.TrOff in

/- English proof (translation)
Introduce `D S T C hn ΛT hsd hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ Λ' hab hmover hgen hIsMov Lv hLv u hu`. Distinguish the cases in `hT : T.rank = 0`. Establish `h0 : GlobalTheory.LiftLevel.partAt (1 - e - cA D e) u = 0` using `Matrix.ext fun i _ => absurd i.2 (by omega)`. Rewrite using `[h0]`. Conclude with `zero_mem _`.

Establish `hTpos : 0 < T.rank` using `Nat.pos_of_ne_zero hT`. Take `⟨σ, hσ, hσ0, hσ1⟩` from `GlobalTheory.T.exists_finiteAdele_of_splitPlaces_idempotentSum D _ e he`. Establish `hf : 1 - e - cA D e = 1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ)` using `by rw [hσ]; ring`. Establish `hgg : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ) * algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ) = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ)`. Rewrite using `[hσ]`.

Conclude with `(GlobalTheory.IdemConjSum.idemSum_add_conj_idem _ e he).1`. Establish `hff : (1 - e - cA D e) * (1 - e - cA D e) = 1 - e - cA D e`. Rewrite using `[hf]`. Take the linear combination `hgg`. Establish `hrow` using `rowTriv D S T k₀ (1 - e - cA D e) hTpos hff hmover.2.1`.

Rewrite `hrow` using `[hf]`. Establish `hstar : ∀ v, v ∈ stdL D.host.E S.rank ↔ star v ∈ stdL D.host.E S.rank` using `star_stdL D S.rank`. Rewrite using `[GlobalTheory.Ker.LatTens.latO_eq_hatA D S T C _ _ ΛT C.X.Λ hstar hAA]`. Establish `hO : ∀ (c : 𝓞 D.host.F), ∀ y ∈ tens (stdL D.host.E S.rank) C.X.Λ, (algebraMap D.host.F D.host.E (c : D.host.F)) • y ∈ tens (stdL D.host.E S.rank) C.X.Λ` using `fun c y hy => GlobalTheory.Ker.HatLat.smul_mem_tens _ _ (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c) hy`. Establish `hgen' : ∀ α ∈ intAf D.host.F, ∀ y ∈ tens Λ' (Lv.sh C.X.Λ), gm S T ((1 - σ) * α) y ∈ hatA S T (tens (stdL D.host.E S.rank) C.X.Λ)`.

Introduce `α hα y hy`. Establish `hγ : (1 - σ) * α ∈ intAf D.host.F`. Introduce `w`. Rewrite using `[map_mul, map_sub, map_one]`. Distinguish the cases in `hw : ∃ PP ∈ Pg ∪ Q, HeightOneSpectrum.under (𝓞 D.host.F) PP = w`.

Take `⟨PP, hPP, rfl⟩` from `hw`. Rewrite using `[hσ1 PP hPP, sub_self, zero_mul]`. Conclude with `zero_mem _`. Use `push_neg at hw`. Rewrite using `[hσ0 w hw, sub_zero, one_mul]`.

Conclude with `hα w`. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨v, hv, u', hu', rfl⟩` from `hy`. Use `GlobalTheory.T.mem_completedMatrixGroup_of_local_multiplier D S T _ hO _ hγ _ fun w => ?_` and prove the remaining obligations.

Distinguish the cases in `hw : ∃ PP ∈ Pg ∪ Q, HeightOneSpectrum.under (𝓞 D.host.F) PP = w`. Use `left`. Take `⟨PP, hPP, rfl⟩` from `hw`. Rewrite using `[map_mul, map_sub, map_one, hσ1 PP hPP, sub_self, zero_mul]`. Use `right push_neg at hw`.

Take `⟨t₁, ht₁, h1⟩` from `GlobalTheory.T.exists_multiplier_standard_lattice_of_mover_trivial D S k₀ Λ' σ w (hσ0 w hw) hrow hIsMov v hv`. Establish `hu'' : u' ∈ idq (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) C.X.Λ`. Establish `: Lv.sh C.X.Λ = idq Lv.𝔪 (conjI Lv.𝔪) C.X.Λ` using `rfl`. Rewrite `hu'` using `[this, hLv]`. Conclude with `hu'`.

Take `⟨t₂, ht₂, h2'⟩` from `GlobalTheory.T.exists_multiplier_shifted_lattice_away_from_places D T.rank Pg Q C.X.Λ w hw u' hu''`. Use `⟨t₁ * t₂, fun hm => (w.isPrime.mem_or_mem hm).elim ht₁ ht₂, ?_⟩` and prove the remaining obligations. Use `AddSubgroup.subset_closure ⟨_, h1, _, h2', ?_⟩` and prove the remaining obligations. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap D.host.F D.host.E ((t₁ * t₂ : 𝓞 D.host.F) : D.host.F) * (v i * u' j) = algebraMap D.host.F D.host.E (t₁ : D.host.F) * v i * (algebraMap D.host.F D.host.E (t₂ : D.host.F) * u' j)`.

Rewrite using `[show ((t₁ * t₂ : 𝓞 D.host.F) : D.host.F) = (t₁ : D.host.F) * (t₂ : D.host.F) from rfl, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => rw [gm_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [gm_add]`.

Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [gm_neg]`. Conclude with `neg_mem hx`. Rewrite using `[hf]`. Proceed by induction on `hu using AddSubgroup.closure_induction with`.

Consider the case `mem w hw`. Take `⟨α, hα, y, hy, rfl⟩` from `hw`. Conclude with `(partAt_gm σ α y).symm ▸ hgen' α hα y hy`. Consider the case `zero => rw [partAt_zero]`. Conclude with `zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [partAt_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [partAt_neg]`. Conclude with `neg_mem hx`.
-/
theorem partAt_off_mem_latO : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ u ∈ hatA S T (tens Λ' (Lv.sh C.X.Λ)), GlobalTheory.LiftLevel.partAt (1 - e - cA D e) u ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  intro D S T C hn ΛT hsd hAA βS βT hβS hβT Pg Q ξ hPg h2 e he a k₀ Λ' hab hmover hgen hIsMov Lv hLv u hu
  by_cases hT : T.rank = 0
  · have h0 : GlobalTheory.LiftLevel.partAt (1 - e - cA D e) u = 0 := Matrix.ext fun i _ => absurd i.2 (by omega)
    rw [h0]; exact zero_mem _
  have hTpos : 0 < T.rank := Nat.pos_of_ne_zero hT
  obtain ⟨σ, hσ, hσ0, hσ1⟩ := GlobalTheory.T.exists_finiteAdele_of_splitPlaces_idempotentSum D _ e he
  have hf : 1 - e - cA D e = 1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ) := by rw [hσ]; ring
  have hgg : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ) * algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ)
      = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ) := by
    rw [hσ]; exact (GlobalTheory.IdemConjSum.idemSum_add_conj_idem _ e he).1
  have hff : (1 - e - cA D e) * (1 - e - cA D e) = 1 - e - cA D e := by
    rw [hf]; linear_combination hgg
  have hrow := rowTriv D S T k₀ (1 - e - cA D e) hTpos hff hmover.2.1
  rw [hf] at hrow
  have hstar : ∀ v, v ∈ stdL D.host.E S.rank ↔ star v ∈ stdL D.host.E S.rank := star_stdL D S.rank
  rw [GlobalTheory.Ker.LatTens.latO_eq_hatA D S T C _ _ ΛT C.X.Λ hstar hAA]
  have hO : ∀ (c : 𝓞 D.host.F), ∀ y ∈ tens (stdL D.host.E S.rank) C.X.Λ,
      (algebraMap D.host.F D.host.E (c : D.host.F)) • y ∈ tens (stdL D.host.E S.rank) C.X.Λ := fun c y hy =>
    GlobalTheory.Ker.HatLat.smul_mem_tens _ _ (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c) hy
  have hgen' : ∀ α ∈ intAf D.host.F, ∀ y ∈ tens Λ' (Lv.sh C.X.Λ),
      gm S T ((1 - σ) * α) y ∈ hatA S T (tens (stdL D.host.E S.rank) C.X.Λ) := by
    intro α hα y hy
    have hγ : (1 - σ) * α ∈ intAf D.host.F := by
      intro w
      rw [map_mul, map_sub, map_one]
      by_cases hw : ∃ PP ∈ Pg ∪ Q, HeightOneSpectrum.under (𝓞 D.host.F) PP = w
      · obtain ⟨PP, hPP, rfl⟩ := hw
        rw [hσ1 PP hPP, sub_self, zero_mul]; exact zero_mem _
      · push_neg at hw
        rw [hσ0 w hw, sub_zero, one_mul]; exact hα w
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨v, hv, u', hu', rfl⟩ := hy
      refine GlobalTheory.T.mem_completedMatrixGroup_of_local_multiplier D S T _ hO _ hγ _ fun w => ?_
      by_cases hw : ∃ PP ∈ Pg ∪ Q, HeightOneSpectrum.under (𝓞 D.host.F) PP = w
      · left
        obtain ⟨PP, hPP, rfl⟩ := hw
        rw [map_mul, map_sub, map_one, hσ1 PP hPP, sub_self, zero_mul]
      · right
        push_neg at hw
        obtain ⟨t₁, ht₁, h1⟩ := GlobalTheory.T.exists_multiplier_standard_lattice_of_mover_trivial D S k₀ Λ' σ w (hσ0 w hw) hrow hIsMov v hv
        have hu'' : u' ∈ idq (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) C.X.Λ := by
          have : Lv.sh C.X.Λ = idq Lv.𝔪 (conjI Lv.𝔪) C.X.Λ := rfl
          rw [this, hLv] at hu'; exact hu'
        obtain ⟨t₂, ht₂, h2'⟩ := GlobalTheory.T.exists_multiplier_shifted_lattice_away_from_places D T.rank Pg Q C.X.Λ w hw u' hu''
        refine ⟨t₁ * t₂, fun hm => (w.isPrime.mem_or_mem hm).elim ht₁ ht₂, ?_⟩
        refine AddSubgroup.subset_closure ⟨_, h1, _, h2', ?_⟩
        refine Matrix.ext fun i j => ?_
        change algebraMap D.host.F D.host.E ((t₁ * t₂ : 𝓞 D.host.F) : D.host.F) * (v i * u' j) =
          algebraMap D.host.F D.host.E (t₁ : D.host.F) * v i * (algebraMap D.host.F D.host.E (t₂ : D.host.F) * u' j)
        rw [show ((t₁ * t₂ : 𝓞 D.host.F) : D.host.F) = (t₁ : D.host.F) * (t₂ : D.host.F) from rfl, map_mul]
        ring
    | zero => rw [gm_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [gm_add]; exact add_mem hx hy
    | neg x _ hx => rw [gm_neg]; exact neg_mem hx
  rw [hf]
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, y, hy, rfl⟩ := hw
    exact (partAt_gm σ α y).symm ▸ hgen' α hα y hy
  | zero => rw [partAt_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [partAt_add]; exact add_mem hx hy
  | neg x _ hx => rw [partAt_neg]; exact neg_mem hx

end GlobalTheory.LiftLevel

end
