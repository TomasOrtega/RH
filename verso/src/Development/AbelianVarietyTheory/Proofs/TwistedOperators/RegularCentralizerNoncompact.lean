import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientMeasureFibrationStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

namespace GlobalTheory.ArchVanish

open GlobalTheory.AdelicU

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def archKerEquiv (w : InfinitePlace F) : GArch σ J w × (projArch σ J w).ker ≃ₜ* GAd σ J where
  toFun p := embArch σ J w p.1 * p.2
  invFun x := (projArch σ J w x, ⟨(embArch σ J w (projArch σ J w x))⁻¹ * x, by
    rw [MonoidHom.mem_ker, map_mul, map_inv, projArch_embArch_self, inv_mul_cancel]⟩)
  left_inv p := by
    obtain ⟨a, z, hz⟩ := p
    have hz' : projArch σ J w z = 1 := hz
    refine Prod.ext ?_ (Subtype.ext ?_)
    · simp [hz']
    · simp [hz']
  right_inv x := by simp
  map_mul' p q := by
    obtain ⟨a, z, hz⟩ := p
    obtain ⟨a', z', hz'⟩ := q
    have hc := (commute_embArch σ J a' (g := z) hz).eq
    simp only [Prod.mk_mul_mk, Subgroup.coe_mul, map_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (embArch σ J w a'), hc, mul_assoc]
  continuous_toFun := ((continuous_embArch σ J w).comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := by
    refine (continuous_projArch σ J w).prodMk (Continuous.subtype_mk ?_ _)
    exact ((continuous_embArch σ J w).comp (continuous_projArch σ J w)).inv.mul continuous_id

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem archKerEquiv_apply (w : InfinitePlace F) (p : GArch σ J w × (projArch σ J w).ker) :
    archKerEquiv σ J w p = embArch σ J w p.1 * p.2 := rfl

variable {σ J}

/- English proof (translation)
Rewrite using `[Orb.mem_cent, Orb.mem_cent]`. Use `⟨fun h => by simpa using congrArg (projArch σ J w) h, fun h => GAd_ext σ J (fun u => ?_) fun v => by simp⟩` and prove the remaining obligations. Distinguish the cases in `hu : u = w`. Substitute `hu` using the available equality. Simplify using `using h`.

Simplify using `[projArch_embArch_ne σ J hu]`.
-/
theorem embArch_mem_cent_iff {w : InfinitePlace F} (a : GArch σ J w) (γ : GAd σ J) :
    embArch σ J w a ∈ Orb.cent γ ↔ a ∈ Orb.cent (projArch σ J w γ) := by
  rw [Orb.mem_cent, Orb.mem_cent]
  refine ⟨fun h => by simpa using congrArg (projArch σ J w) h, fun h => GAd_ext σ J (fun u => ?_) fun v => by simp⟩
  by_cases hu : u = w
  · subst hu; simpa using h
  · simp [projArch_embArch_ne σ J hu]

/- English proof (translation)
Use `⟨⟨fun s t => Subtype.ext (GAd_ext σ J (fun u => ?_) fun v => ?_)⟩⟩` and prove the remaining obligations. Establish `hc` using `Orb.isMulCommutative_cent_HA (isRegSS_projArch_ratEmb hγ u)`. Establish `hs : projArch σ J u s ∈ Orb.cent (projArch σ J u (ratEmb σ J γ))`. Rewrite using `[Orb.mem_cent, ← map_mul, ← map_mul, Orb.mem_cent.1 s.2]`. Establish `ht : projArch σ J u t ∈ Orb.cent (projArch σ J u (ratEmb σ J γ))`.

Rewrite using `[Orb.mem_cent, ← map_mul, ← map_mul, Orb.mem_cent.1 t.2]`. Simplify using `using congrArg Subtype.val (hc.1.1 ⟨_, hs⟩ ⟨_, ht⟩)`. Establish `hc` using `Orb.isMulCommutative_cent_HA (isRegSS_proj_ratEmb hγ v)`. Establish `hs : proj σ J v s ∈ Orb.cent (proj σ J v (ratEmb σ J γ))`. Rewrite using `[Orb.mem_cent, ← map_mul, ← map_mul, Orb.mem_cent.1 s.2]`.

Establish `ht : proj σ J v t ∈ Orb.cent (proj σ J v (ratEmb σ J γ))`. Rewrite using `[Orb.mem_cent, ← map_mul, ← map_mul, Orb.mem_cent.1 t.2]`. Simplify using `using congrArg Subtype.val (hc.1.1 ⟨_, hs⟩ ⟨_, ht⟩)`.
-/
theorem isMulCommutative_cent_ratEmb {γ : GRat σ J} (hγ : IsRegSS γ.1.1) :
    IsMulCommutative (Orb.cent (ratEmb σ J γ)) := by
  refine ⟨⟨fun s t => Subtype.ext (GAd_ext σ J (fun u => ?_) fun v => ?_)⟩⟩
  · have hc := Orb.isMulCommutative_cent_HA (isRegSS_projArch_ratEmb hγ u)
    have hs : projArch σ J u s ∈ Orb.cent (projArch σ J u (ratEmb σ J γ)) := by
      rw [Orb.mem_cent, ← map_mul, ← map_mul, Orb.mem_cent.1 s.2]
    have ht : projArch σ J u t ∈ Orb.cent (projArch σ J u (ratEmb σ J γ)) := by
      rw [Orb.mem_cent, ← map_mul, ← map_mul, Orb.mem_cent.1 t.2]
    simpa using congrArg Subtype.val (hc.1.1 ⟨_, hs⟩ ⟨_, ht⟩)
  · have hc := Orb.isMulCommutative_cent_HA (isRegSS_proj_ratEmb hγ v)
    have hs : proj σ J v s ∈ Orb.cent (proj σ J v (ratEmb σ J γ)) := by
      rw [Orb.mem_cent, ← map_mul, ← map_mul, Orb.mem_cent.1 s.2]
    have ht : proj σ J v t ∈ Orb.cent (proj σ J v (ratEmb σ J γ)) := by
      rw [Orb.mem_cent, ← map_mul, ← map_mul, Orb.mem_cent.1 t.2]
    simpa using congrArg Subtype.val (hc.1.1 ⟨_, hs⟩ ⟨_, ht⟩)

/- English proof (translation)
The claim follows from `Orb.isMulCommutative_cent_HA (isRegSS_projArch_ratEmb hγ w)`.
-/
theorem isMulCommutative_cent_projArch_ratEmb {γ : GRat σ J} (hγ : IsRegSS γ.1.1) (w : InfinitePlace F) :
    IsMulCommutative (Orb.cent (projArch σ J w (ratEmb σ J γ))) :=
  Orb.isMulCommutative_cent_HA (isRegSS_projArch_ratEmb hγ w)

/- English proof (translation)
Establish `hz : projArch σ J w z.1 = 1` using `z.2`. Rewrite using `[archKerEquiv_apply, Subgroup.mem_comap, Subgroup.coe_subtype]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `ha : a ∈ Orb.cent (projArch σ J w γ)`.

Use `congrArg (projArch σ J w) (Orb.mem_cent.1 h)` as an intermediate fact. Rewrite using `[Orb.mem_cent]`. Simplify `this` using `[hz]`. Use `⟨ha, ?_⟩` and prove the remaining obligations. Simplify using `using mul_mem (inv_mem ((embArch_mem_cent_iff a _).2 ha)) h`.

Introduce and unpack `⟨ha, hz'⟩`. Conclude with `mul_mem ((embArch_mem_cent_iff a _).2 ha) hz'`.
-/
theorem archKerEquiv_mem_cent_iff (w : InfinitePlace F) (γ : GAd σ J) (a : GArch σ J w)
    (z : (projArch σ J w).ker) :
    archKerEquiv σ J w (a, z) ∈ Orb.cent γ ↔
      a ∈ Orb.cent (projArch σ J w γ) ∧ z ∈ (Orb.cent γ).comap (projArch σ J w).ker.subtype := by
  have hz : projArch σ J w z.1 = 1 := z.2
  rw [archKerEquiv_apply, Subgroup.mem_comap, Subgroup.coe_subtype]
  constructor
  · intro h
    have ha : a ∈ Orb.cent (projArch σ J w γ) := by
      have := congrArg (projArch σ J w) (Orb.mem_cent.1 h)
      rw [Orb.mem_cent]; simpa [hz] using this
    refine ⟨ha, ?_⟩
    simpa using mul_mem (inv_mem ((embArch_mem_cent_iff a _).2 ha)) h
  · rintro ⟨ha, hz'⟩
    exact mul_mem ((embArch_mem_cent_iff a _).2 ha) hz'

/- English proof (translation)
Establish `hz : projArch σ J w z.1 = 1` using `z.2`. Use `⟨(∏ u ∈ Finset.univ.erase w, fa u (projArch σ J u (z.1⁻¹ * γ * z))) * ∏ᶠ v, ff v (proj σ J v (z.1⁻¹ * γ * z)), fun a => ?_⟩` and prove the remaining obligations. Simplify using `only [archKerEquiv_apply, Orb.tensor]`. Rewrite using `[← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w)]`. Establish `h1 : projArch σ J w ((embArch σ J w a * z)⁻¹ * γ * (embArch σ J w a * z)) = a⁻¹ * projArch σ J w γ * a`.

Simplify using `[hz]`. Establish `h2 : ∀ u ∈ Finset.univ.erase w, fa u (projArch σ J u ((embArch σ J w a * z)⁻¹ * γ * (embArch σ J w a * z))) = fa u (projArch σ J u (z.1⁻¹ * γ * z))` using `fun u hu => by simp [projArch_embArch_ne σ J (Finset.ne_of_mem_erase hu)]`. Establish `h3 : ∀ v, proj σ J v ((embArch σ J w a * z)⁻¹ * γ * (embArch σ J w a * z)) = proj σ J v (z.1⁻¹ * γ * z)` using `fun v => by simp`. Rewrite using `[h1, Finset.prod_congr rfl h2]`. Simplify using `only [h3]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_tensor_conj_archKerEquiv (fa : ∀ w, GArch σ J w → ℂ) (ff : ∀ v, GLoc σ J v → ℂ)
    (w : InfinitePlace F) (γ : GAd σ J) (z : (projArch σ J w).ker) :
    ∃ K : ℂ, ∀ a, Orb.tensor σ J fa ff ((archKerEquiv σ J w (a, z))⁻¹ * γ * archKerEquiv σ J w (a, z)) =
      K * fa w (a⁻¹ * projArch σ J w γ * a) := by
  classical
  have hz : projArch σ J w z.1 = 1 := z.2
  refine ⟨(∏ u ∈ Finset.univ.erase w, fa u (projArch σ J u (z.1⁻¹ * γ * z))) *
    ∏ᶠ v, ff v (proj σ J v (z.1⁻¹ * γ * z)), fun a => ?_⟩
  simp only [archKerEquiv_apply, Orb.tensor]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w)]
  have h1 : projArch σ J w ((embArch σ J w a * z)⁻¹ * γ * (embArch σ J w a * z)) = a⁻¹ * projArch σ J w γ * a := by
    simp [hz]
  have h2 : ∀ u ∈ Finset.univ.erase w, fa u (projArch σ J u ((embArch σ J w a * z)⁻¹ * γ * (embArch σ J w a * z))) =
      fa u (projArch σ J u (z.1⁻¹ * γ * z)) :=
    fun u hu => by simp [projArch_embArch_ne σ J (Finset.ne_of_mem_erase hu)]
  have h3 : ∀ v, proj σ J v ((embArch σ J w a * z)⁻¹ * γ * (embArch σ J w a * z)) = proj σ J v (z.1⁻¹ * γ * z) :=
    fun v => by simp
  rw [h1, Finset.prod_congr rfl h2]
  simp only [h3]
  ring

open Orb in

/- English proof (translation)
Establish `hB : IsClosed ((projArch σ J w).ker : Set (GAd σ J))`. Rewrite using `[MonoidHom.coe_ker]`. Conclude with `isClosed_singleton.preimage (continuous_projArch σ J w)`. Use `haveI : LocallyCompactSpace (projArch σ J w).ker := hB.locallyCompactSpace`. Conclude with `GlobalTheory.T.quotient_measure_fibration (GArch σ J w) (projArch σ J w).ker (GAd σ J) (archKerEquiv σ J w) _ _ (cent γ) (archKerEquiv_mem_cent_iff w γ) (isClosed_cent γ) hcomm dh dt da ds φ hi hint h0`.
-/
theorem quotInt_cent_eq_zero_of_arch (w : InfinitePlace F) (γ : GAd σ J) (hcomm : IsMulCommutative (cent γ))
    (dh : Measure (GAd σ J)) [dh.IsHaarMeasure] (dt : Measure (cent γ)) [dt.IsHaarMeasure]
    (da : Measure (GArch σ J w)) [da.IsHaarMeasure] (ds : Measure (cent (projArch σ J w γ))) [ds.IsHaarMeasure]
    (φ : GAd σ J → ℂ) (hi : GlobalTheory.AutomorphicL2Unitary.LeftInv (cent γ) φ)
    (hint : Integrable (GlobalTheory.AutomorphicL2Unitary.descend (cent γ) φ) (quotMeas (cent γ) dt dh))
    (h0 : ∀ z : (projArch σ J w).ker, quotInt (cent (projArch σ J w γ)) ds da (fun a => φ (archKerEquiv σ J w (a, z))) = 0) :
    quotInt (cent γ) dt dh φ = 0 := by
  have hB : IsClosed ((projArch σ J w).ker : Set (GAd σ J)) := by
    rw [MonoidHom.coe_ker]; exact isClosed_singleton.preimage (continuous_projArch σ J w)
  haveI : LocallyCompactSpace (projArch σ J w).ker := hB.locallyCompactSpace
  exact GlobalTheory.T.quotient_measure_fibration (GArch σ J w) (projArch σ J w).ker (GAd σ J) (archKerEquiv σ J w) _ _ (cent γ)
    (archKerEquiv_mem_cent_iff w γ) (isClosed_cent γ) hcomm dh dt da ds φ hi hint h0

end General

end GlobalTheory.ArchVanish

end

namespace GlobalTheory.ArchVanish

set_option maxHeartbeats 400000 in

/- English proof (translation)
Introduce `D V S M μa fa ff hμa hfa hff γ hγ w hnc b hb hbl hbw μ _ dt _`. Establish `hcm` using `isCMExt_host D`. Establish `hJ` using `GlobalTheory.Doubling.isHermND_gram V`. Establish `hcomm : IsMulCommutative (cent (rat V γ))` using `isMulCommutative_cent_ratEmb hγ`. Use `haveI : dt.IsMulRightInvariant := isMulRightInvariant_cent hcomm dt`.

Establish `hT : IsClosed (cent (rat V γ) : Set (GA D V))` using `isClosed_cent _`. Establish `hten` using `continuous_of_mem_ccAd (tensor_mem_ccAd hfa.mem hff)`. Establish `hφi : LeftInv (cent (rat V γ)) fun x => b x * conjFn (rat V γ) (tensor D.sp.cm.sig V.gram fa ff) x` using `fun t ht x => by dsimp only; rw [hbl t ht x, leftInv_conjFn le_rfl _ t ht x]`. Establish `hint : Integrable (descend (cent (rat V γ)) fun x => b x * conjFn (rat V γ) (tensor D.sp.cm.sig V.gram fa ff) x) (quotMeas (cent (rat V γ)) dt μ)`. Take `⟨C, hC, h0⟩` from `isProperOrbit_ratEmb hcm hJ hγ _ hten.2`.

Use `integrable_descend hT hφi (hb.mul (hten.1.comp (by fun_prop))) hC fun x hx => h0 x ?_` and prove the remaining obligations. Conclude with `subset_tsupport _ (right_ne_zero_of_mul hx)`. Establish `horb : ∀ (ds : Measure (cent (projArch D.sp.cm.sig V.gram w (rat V γ)))) [ds.IsHaarMeasure] [ds.IsMulRightInvariant], HasOrbInt (μa w) (projArch D.sp.cm.sig V.gram w (rat V γ)) ds (fa w) 0`. Take `⟨ρ, rfl⟩` from `(placeOf_bijective D).2 w`. Introduce `ds _ _`.

Use `haveI := (M.ds ρ).1`. Establish `hs : IsRegSS (matAt V ρ (projArch D.sp.cm.sig V.gram (placeOf D ρ) (rat V γ)))` using `(isRegSS_archMat_iff hcm (embOverOf D ρ)).2 (isRegSS_projArch_ratEmb hγ _)`. Establish `h` using `(hfa ρ).orb_noncompact _ hs hnc`. Conclude with `h ds`. Use `haveI := hμa w`.

Take `⟨ds, hds1, hds2⟩ : ∃ ds : Measure (cent (projArch D.sp.cm.sig V.gram w (rat V γ))), ds.IsHaarMeasure ∧ ds.IsMulRightInvariant` from `by haveI : LocallyCompactSpace (cent (projArch D.sp.cm.sig V.gram w (rat V γ))) := (isClosed_cent _).locallyCompactSpace`. Conclude with `⟨Measure.haar, inferInstance, isMulRightInvariant_cent (isMulCommutative_cent_projArch_ratEmb (σ := D.sp.cm.sig) (J := V.gram) hγ w) _⟩`. Use `⟨hint, quotInt_cent_eq_zero_of_arch (σ := D.sp.cm.sig) (J := V.gram) w (rat V γ) hcomm μ dt (μa w) ds _ hφi hint fun z => ?_⟩` and prove the remaining obligations. Take `⟨K, hK⟩` from `exists_tensor_conj_archKerEquiv (σ := D.sp.cm.sig) (J := V.gram) fa ff w (rat V γ) z`. Establish `e1 : (fun a => (fun x => b x * conjFn (rat V γ) (tensor D.sp.cm.sig V.gram fa ff) x) (archKerEquiv D.sp.cm.sig V.gram w (a, z))) = fun a => (b z * K) * conjFn (projArch D.sp.cm.sig V.gram w (rat V γ)) (fa w) a` using `funext fun a => by`.

Simplify using `only [conjFn]`. Rewrite using `[hK a, archKerEquiv_apply, hbw]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`. Establish `e2` using `(horb ds).2`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem hasQuotInt_weighted_eq_zero : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), (∀ w, (μa w).IsHaarMeasure) → IsTestArchG M μa fa → IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∀ γ : GF V, IsRegSS γ.1.1 → ∀ w, ¬ IsCompact (cent (projArch D.sp.cm.sig V.gram w (rat V γ)) : Set (GArch D.sp.cm.sig V.gram w)) → ∀ b : GA D V → ℂ, Continuous b → LeftInv (cent (rat V γ)) b → (∀ g x, b (embArch D.sp.cm.sig V.gram w g * x) = b x) → ∀ (μ : Measure (GA D V)) [μ.IsHaarMeasure] (dt : Measure (cent (rat V γ))) [dt.IsHaarMeasure], HasQuotInt (cent (rat V γ)) dt μ (fun x => b x * conjFn (rat V γ) (tensor D.sp.cm.sig V.gram fa ff) x) 0 := by
  intro D V S M μa fa ff hμa hfa hff γ hγ w hnc b hb hbl hbw μ _ dt _
  have hcm := isCMExt_host D
  have hJ := GlobalTheory.Doubling.isHermND_gram V
  have hcomm : IsMulCommutative (cent (rat V γ)) := isMulCommutative_cent_ratEmb hγ
  haveI : dt.IsMulRightInvariant := isMulRightInvariant_cent hcomm dt
  have hT : IsClosed (cent (rat V γ) : Set (GA D V)) := isClosed_cent _
  have hten := continuous_of_mem_ccAd (tensor_mem_ccAd hfa.mem hff)
  have hφi : LeftInv (cent (rat V γ)) fun x => b x * conjFn (rat V γ) (tensor D.sp.cm.sig V.gram fa ff) x :=
    fun t ht x => by dsimp only; rw [hbl t ht x, leftInv_conjFn le_rfl _ t ht x]
  have hint : Integrable (descend (cent (rat V γ)) fun x => b x * conjFn (rat V γ) (tensor D.sp.cm.sig V.gram fa ff) x)
      (quotMeas (cent (rat V γ)) dt μ) := by
    obtain ⟨C, hC, h0⟩ := isProperOrbit_ratEmb hcm hJ hγ _ hten.2
    refine integrable_descend hT hφi (hb.mul (hten.1.comp (by fun_prop))) hC fun x hx => h0 x ?_
    exact subset_tsupport _ (right_ne_zero_of_mul hx)

  have horb : ∀ (ds : Measure (cent (projArch D.sp.cm.sig V.gram w (rat V γ)))) [ds.IsHaarMeasure]
      [ds.IsMulRightInvariant], HasOrbInt (μa w) (projArch D.sp.cm.sig V.gram w (rat V γ)) ds (fa w) 0 := by
    obtain ⟨ρ, rfl⟩ := (placeOf_bijective D).2 w
    intro ds _ _
    haveI := (M.ds ρ).1
    have hs : IsRegSS (matAt V ρ (projArch D.sp.cm.sig V.gram (placeOf D ρ) (rat V γ))) :=
      (isRegSS_archMat_iff hcm (embOverOf D ρ)).2 (isRegSS_projArch_ratEmb hγ _)
    have h := (hfa ρ).orb_noncompact _ hs hnc
    exact h ds
  haveI := hμa w
  obtain ⟨ds, hds1, hds2⟩ : ∃ ds : Measure (cent (projArch D.sp.cm.sig V.gram w (rat V γ))),
      ds.IsHaarMeasure ∧ ds.IsMulRightInvariant := by
    haveI : LocallyCompactSpace (cent (projArch D.sp.cm.sig V.gram w (rat V γ))) :=
      (isClosed_cent _).locallyCompactSpace
    exact ⟨Measure.haar, inferInstance, isMulRightInvariant_cent
      (isMulCommutative_cent_projArch_ratEmb (σ := D.sp.cm.sig) (J := V.gram) hγ w) _⟩
  refine ⟨hint, quotInt_cent_eq_zero_of_arch (σ := D.sp.cm.sig) (J := V.gram) w (rat V γ) hcomm μ dt (μa w) ds _ hφi
    hint fun z => ?_⟩
  obtain ⟨K, hK⟩ := exists_tensor_conj_archKerEquiv (σ := D.sp.cm.sig) (J := V.gram) fa ff w (rat V γ) z
  have e1 : (fun a => (fun x => b x * conjFn (rat V γ) (tensor D.sp.cm.sig V.gram fa ff) x)
      (archKerEquiv D.sp.cm.sig V.gram w (a, z))) =
      fun a => (b z * K) * conjFn (projArch D.sp.cm.sig V.gram w (rat V γ)) (fa w) a := funext fun a => by
    simp only [conjFn]
    rw [hK a, archKerEquiv_apply, hbw]
    ring
  rw [e1]
  have e2 := (horb ds).2
  calc quotInt _ ds (μa w) (fun a => (b z * K) * conjFn (projArch D.sp.cm.sig V.gram w (rat V γ)) (fa w) a)
      = (b z * K) * quotInt _ ds (μa w) (conjFn (projArch D.sp.cm.sig V.gram w (rat V γ)) (fa w)) :=
        integral_const_mul _ _
    _ = 0 := by rw [show quotInt _ _ _ _ = _ from e2, mul_zero]

end GlobalTheory.ArchVanish
