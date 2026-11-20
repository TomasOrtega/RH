import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVectorStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalCombinationOfFixedLocalTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoweUnramifiedAllVacuaStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnramifiedLocalPairOfInertWeilDatumStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.CorrInert

variable {D : D7}

/- English proof (translation)
Take `⟨Φ, hΦ⟩` from `GlobalTheory.IdemSupport.exists_comp D`. Take `⟨e, f, h⟩` from `GlobalTheory.IdemSupport.exists_isPrimeIdem hΦ P`. Establish `hc : P = GlobalTheory.IdemSupport.cP P`. Use `(GlobalTheory.IdemSupport.isConjPl_iff P P).1 fun c hc => ⟨GlobalTheory.IdemSupport.cO D c, ?_, rfl⟩` and prove the remaining obligations. Establish `h1 : GlobalTheory.IdemSupport.cO D c ∈ (conjPl P).asIdeal` using `Ideal.mem_map_of_mem _ hc`.

Rewrite `h1` using `[hP]`. Then use the resulting hypothesis. Break down `h with ⟨h, -⟩ | h` into its components or cases. It suffices to derive a contradiction. Establish `hd` using `GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ h`. Establish `hd'` using `GlobalTheory.IdemSupport.delta_conj hΦ hd`.

Rewrite `hd'` using `[← hc]`. Establish `h2` using `GlobalTheory.IdemSupport.ev_mul (Φ := Φ) e (cA D e) P`. Rewrite `h2` using `[h.1.2.1, GlobalTheory.IdemSupport.ev_zero, hd.2.1, hd'.2.1, one_mul]`. Conclude with `zero_ne_one h2`. Take `⟨rfl, h⟩` from `h`.

Conclude with `⟨f, Or.inr ⟨rfl, h⟩⟩`.
-/
theorem exists_idem_of_conj_eq (P : Pl D.host.E) (hP : conjPl P = P) : ∃ e, IsPrimeIdem P e e := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨e, f, h⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem hΦ P
  have hc : P = GlobalTheory.IdemSupport.cP P := by
    refine (GlobalTheory.IdemSupport.isConjPl_iff P P).1 fun c hc => ⟨GlobalTheory.IdemSupport.cO D c, ?_, rfl⟩
    have h1 : GlobalTheory.IdemSupport.cO D c ∈ (conjPl P).asIdeal := Ideal.mem_map_of_mem _ hc
    rwa [hP] at h1
  rcases h with ⟨h, -⟩ | h
  · exfalso
    have hd := GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ h
    have hd' := GlobalTheory.IdemSupport.delta_conj hΦ hd
    rw [← hc] at hd'
    have h2 := GlobalTheory.IdemSupport.ev_mul (Φ := Φ) e (cA D e) P
    rw [h.1.2.1, GlobalTheory.IdemSupport.ev_zero, hd.2.1, hd'.2.1, one_mul] at h2
    exact zero_ne_one h2
  · obtain ⟨rfl, h⟩ := h
    exact ⟨f, Or.inr ⟨rfl, h⟩⟩

/- English proof (translation)
Unfold `rep at h`. Use `split_ifs at h with hl`. Take `⟨e', f', -, -, -, he', -, -, -, -, -, -, -, hs, -⟩` from `hl.choose_spec`. Take `⟨-, rfl⟩` from `((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P e f he).2.2.2.1 e' f' he'`. Conclude with `hs γ h`.

Conclude with `absurd h (Finset.notMem_empty _)`.
-/
theorem suppF_of_mem_rep (V : HSp D) {P : Pl D.host.E} {e f : AE D} (he : IsPrimeIdem P e f) {d : List ℤ}
    {γ : GA D V} (h : γ ∈ rep V P d) : SuppF V f γ := by
  unfold rep at h
  split_ifs at h with hl
  · obtain ⟨e', f', -, -, -, he', -, -, -, -, -, -, -, hs, -⟩ := hl.choose_spec
    obtain ⟨-, rfl⟩ :=
      ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P e f he).2.2.2.1 e' f' he'
    exact hs γ h
  · exact absurd h (Finset.notMem_empty _)

/- English proof (translation)
Establish `hm : opOf π P c ∈ Submodule.span ℂ (Set.range fun h => π (ι h))`. Use `Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _ (Submodule.sum_mem _ fun γ hγ => ?_)` and prove the remaining obligations. Take `⟨h, rfl⟩` from `hι γ (suppF_of_mem_rep V he hγ)`. Conclude with `Submodule.subset_span ⟨h, rfl⟩`. Take `⟨b, hb⟩` from `Finsupp.mem_span_range_iff_exists_finsupp.1 hm`.

Use `⟨b, fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[← hb]`. Simplify using `only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply]`.
-/
theorem exists_pullback {V : HSp D} {P : Pl D.host.E} {e f : AE D} (he : IsPrimeIdem P e f)
    {W : Type} [AddCommGroup W] [Module ℂ W] (π : GA D V →* Module.End ℂ W) {H : Type} (ι : H → GA D V)
    (hι : ∀ g, SuppF V f g → ∃ h, ι h = g) (c : List ℤ →₀ ℂ) :
    ∃ b : H →₀ ℂ, ∀ u, (b.sum fun h z => z • π (ι h) u) = opOf π P c u := by
  have hm : opOf π P c ∈ Submodule.span ℂ (Set.range fun h => π (ι h)) := by
    refine Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _ (Submodule.sum_mem _ fun γ hγ => ?_)
    obtain ⟨h, rfl⟩ := hι γ (suppF_of_mem_rep V he hγ)
    exact Submodule.subset_span ⟨h, rfl⟩
  obtain ⟨b, hb⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hm
  refine ⟨b, fun u => ?_⟩
  rw [← hb]
  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply]

/- English proof (translation)
Take `⟨bT, hb⟩` from `exists_pullback he πT ιT hT cT`. Take `⟨bS, hbS⟩` from `howe bT fun u hu k hk => by`. Rewrite using `[hb]`. Conclude with `(GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors T P).2.1 cT W πT u (fixT u hu) k hk`. Take `⟨cS, hc⟩` from `GlobalTheory.T.exists_sphericalCombination_of_fixed_localTranslates S P e f he (Finsupp.mapDomain ιS bS) fun g hg => by`.

Take `⟨g', -, rfl⟩` from `Finset.mem_image.1 (Finsupp.mapDomain_support hg)`. Conclude with `hS g'`. Use `⟨cS, fun u hu => ?_⟩` and prove the remaining obligations. Establish `e1 : ((Finsupp.mapDomain ιS bS).sum fun g z => z • πS g u) = bT.sum fun h z => z • πT (ιT h) u`. Rewrite using `[hbS u hu]`.

Conclude with `Finsupp.sum_mapDomain_index (h := fun g (z : ℂ) => z • πS g u) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)`. Rewrite using `[← hc W πS u (fixS u hu) fun k hk => ?_, e1, hb]`. Rewrite using `[e1, Finsupp.sum, map_sum]`. Use `Finset.sum_congr rfl fun h _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, comm, fixS u hu k hk]`.
-/
theorem half {S T : HSp D} {P : Pl D.host.E} {e f : AE D} (he : IsPrimeIdem P e f)
    {W : Type} [AddCommGroup W] [Module ℂ W] (πS : GA D S →* Module.End ℂ W) (πT : GA D T →* Module.End ℂ W)
    (comm : ∀ g h u, πS g (πT h u) = πT h (πS g u)) (Vac : W → Prop)
    (fixS : ∀ u, Vac u → ∀ k ∈ hyp S P, πS k u = u) (fixT : ∀ u, Vac u → ∀ k ∈ hyp T P, πT k u = u)
    {GS GT : Type} (ιS : GS → GA D S) (ιT : GT → GA D T) (hS : ∀ g, SuppF S f (ιS g))
    (hT : ∀ g, SuppF T f g → ∃ h, ιT h = g)
    (howe : ∀ bT : GT →₀ ℂ, (∀ u, Vac u → ∀ k ∈ hyp T P,
        πT k (bT.sum fun h z => z • πT (ιT h) u) = bT.sum fun h z => z • πT (ιT h) u) →
      ∃ bS : GS →₀ ℂ, ∀ u, Vac u → (bT.sum fun h z => z • πT (ιT h) u) = bS.sum fun g z => z • πS (ιS g) u)
    (cT : List ℤ →₀ ℂ) : ∃ cS, ∀ u, Vac u → opOf πS P cS u = opOf πT P cT u := by
  classical
  obtain ⟨bT, hb⟩ := exists_pullback he πT ιT hT cT
  obtain ⟨bS, hbS⟩ := howe bT fun u hu k hk => by
    rw [hb]
    exact (GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors T P).2.1 cT W πT u (fixT u hu) k hk
  obtain ⟨cS, hc⟩ := GlobalTheory.T.exists_sphericalCombination_of_fixed_localTranslates S P e f he (Finsupp.mapDomain ιS bS) fun g hg => by
    obtain ⟨g', -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hg)
    exact hS g'
  refine ⟨cS, fun u hu => ?_⟩
  have e1 : ((Finsupp.mapDomain ιS bS).sum fun g z => z • πS g u) = bT.sum fun h z => z • πT (ιT h) u := by
    rw [hbS u hu]
    exact Finsupp.sum_mapDomain_index (h := fun g (z : ℂ) => z • πS g u) (fun _ => zero_smul _ _)
      (fun _ _ _ => add_smul _ _ _)
  rw [← hc W πS u (fixS u hu) fun k hk => ?_, e1, hb]
  rw [e1, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [map_smul, comm, fixS u hu k hk]

/- English proof (translation)
Simplify using `only [Finsupp.sum, Submodule.coe_sum, Submodule.coe_smul]`.
-/
theorem coe_sum_smul {W : Type} [AddCommGroup W] [Module ℂ W] {M : Submodule ℂ W} {H : Type} (b : H →₀ ℂ) (v : H → M) :
    ((b.sum fun h z => z • v h : M) : W) = b.sum fun h z => z • (v h : W) := by
  simp only [Finsupp.sum, Submodule.coe_sum, Submodule.coe_smul]

/- English proof (translation)
Introduce `hH D ψ S T χS χT om P hW hP hV`. Take `⟨e, he⟩` from `exists_idem_of_conj_eq P hP`. Take `⟨ϖ, σ, q, δ, JS, JT, ψ', M, ρ, ω, ιS, ιT, hL, rS, rT, kS, kT, hω, hM, hvac⟩` from `GlobalTheory.T.exists_unramifiedLocalPair_of_inertWeilDatum ψ S T χS χT om P hW hP hV e he`. Use `haveI : CharZero (P.adicCompletion D.host.E) := algebraRat.charZero _`. Take `⟨h1, h2⟩` from `GlobalTheory.T.howeUnramified_all_vacua hH _ ϖ σ q δ _ _ JS JT ψ' M ρ ω hL`.

Establish `oneS : (1 : GA D S) ∈ hyp S P`. Rewrite using `[← map_one ιS, kS]`. Conclude with `one_mem _`. Establish `oneT : (1 : GA D T) ∈ hyp T P`. Rewrite using `[← map_one ιT, kT]`.

Conclude with `one_mem _`. Establish `comm : ∀ g h u, (om.comp (MonoidHom.inl _ _)) g ((om.comp (MonoidHom.inr _ _)) h u) = (om.comp (MonoidHom.inr _ _)) h ((om.comp (MonoidHom.inl _ _)) g u)`. Introduce `g h u`. Express the relevant statement in the definitionally equal form `(om (g, 1) * om (1, h)) u = (om (1, h) * om (g, 1)) u`. Rewrite using `[← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, one_mul, mul_one, one_mul, mul_one]`.

Establish `fixS : ∀ u, IsVacAt ψ S T P u → ∀ k ∈ hyp S P, (om.comp (MonoidHom.inl _ _)) k u = u` using `fun u hu k hk => hV u hu k hk 1 oneT`. Establish `fixT : ∀ u, IsVacAt ψ S T P u → ∀ k ∈ hyp T P, (om.comp (MonoidHom.inr _ _)) k u = u` using `fun u hu k hk => hV u hu 1 oneS k hk`. Establish `ωS : ∀ g (m : M), ((ω (g, 1) m : M) : WO S T → ℂ) = (om.comp (MonoidHom.inl _ _)) (ιS g) m`. Introduce `g m`. Rewrite using `[hω, map_one]`.

Both sides reduce to the same expression. Establish `ωT : ∀ h (m : M), ((ω (1, h) m : M) : WO S T → ℂ) = (om.comp (MonoidHom.inr _ _)) (ιT h) m`. Introduce `g m`. Rewrite using `[hω, map_one]`. Both sides reduce to the same expression.

Use `⟨hV, fun cT => ?_, fun cS => ?_⟩` and prove the remaining obligations. Use `half he _ _ comm (IsVacAt ψ S T P) fixS fixT ιS ιT (fun g => (rS _).1 ⟨g, rfl⟩) (fun g hg => (rT g).2 hg) (fun bT hb => ?_) cT` and prove the remaining obligations. Take `⟨bS, hbS⟩` from `h1 bT fun s hs k hk => by`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[ωT, coe_sum_smul]`.

Simplify using `only [ωT]`. Conclude with `hb s ((hvac s).1 hs) _ ((kT k).2 hk)`. Use `⟨bS, fun u hu => ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val (hbS ⟨u, hM u hu⟩ ((hvac _).2 hu))` as an intermediate fact. Rewrite `this` using `[coe_sum_smul, coe_sum_smul]`.

Simplify `this` using `only [ωS, ωT]`. It suffices to establish `h : ∃ cT, ∀ u, IsVacAt ψ S T P u → opOf (om.comp (MonoidHom.inr _ _)) P cT u = opOf (om.comp (MonoidHom.inl _ _)) P cS u from h.imp fun cT h u hu => (h u hu).symm`. Use `half he _ _ (fun g h u => (comm h g u).symm) (IsVacAt ψ S T P) fixT fixS ιT ιS (fun g => (rT _).1 ⟨g, rfl⟩) (fun g hg => (rS g).2 hg) (fun bS hb => ?_) cS` and prove the remaining obligations. Take `⟨bT, hbT⟩` from `h2 bS fun s hs k hk => by`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[ωS, coe_sum_smul]`. Simplify using `only [ωS]`. Conclude with `hb s ((hvac s).1 hs) _ ((kS k).2 hk)`. Use `⟨bT, fun u hu => ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val (hbT ⟨u, hM u hu⟩ ((hvac _).2 hu))` as an intermediate fact.

Rewrite `this` using `[coe_sum_smul, coe_sum_smul]`. Simplify `this` using `only [ωS, ωT]`.
-/
theorem sphCorr_of_inert : HoweUnram → ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E), IsWeilDatumO ψ S T χS χT om → conjPl P = P → VacFix ψ om P → SphCorr ψ om P := by
  intro hH D ψ S T χS χT om P hW hP hV
  obtain ⟨e, he⟩ := exists_idem_of_conj_eq P hP
  obtain ⟨ϖ, σ, q, δ, JS, JT, ψ', M, ρ, ω, ιS, ιT, hL, rS, rT, kS, kT, hω, hM, hvac⟩ :=
    GlobalTheory.T.exists_unramifiedLocalPair_of_inertWeilDatum ψ S T χS χT om P hW hP hV e he
  haveI : CharZero (P.adicCompletion D.host.E) := algebraRat.charZero _
  obtain ⟨h1, h2⟩ := GlobalTheory.T.howeUnramified_all_vacua hH _ ϖ σ q δ _ _ JS JT ψ' M ρ ω hL
  have oneS : (1 : GA D S) ∈ hyp S P := by
    rw [← map_one ιS, kS]; exact one_mem _
  have oneT : (1 : GA D T) ∈ hyp T P := by
    rw [← map_one ιT, kT]; exact one_mem _
  have comm : ∀ g h u, (om.comp (MonoidHom.inl _ _)) g ((om.comp (MonoidHom.inr _ _)) h u) =
      (om.comp (MonoidHom.inr _ _)) h ((om.comp (MonoidHom.inl _ _)) g u) := by
    intro g h u
    change (om (g, 1) * om (1, h)) u = (om (1, h) * om (g, 1)) u
    rw [← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, one_mul, mul_one, one_mul, mul_one]
  have fixS : ∀ u, IsVacAt ψ S T P u → ∀ k ∈ hyp S P, (om.comp (MonoidHom.inl _ _)) k u = u :=
    fun u hu k hk => hV u hu k hk 1 oneT
  have fixT : ∀ u, IsVacAt ψ S T P u → ∀ k ∈ hyp T P, (om.comp (MonoidHom.inr _ _)) k u = u :=
    fun u hu k hk => hV u hu 1 oneS k hk
  have ωS : ∀ g (m : M), ((ω (g, 1) m : M) : WO S T → ℂ) = (om.comp (MonoidHom.inl _ _)) (ιS g) m := by
    intro g m
    rw [hω, map_one]; rfl
  have ωT : ∀ h (m : M), ((ω (1, h) m : M) : WO S T → ℂ) = (om.comp (MonoidHom.inr _ _)) (ιT h) m := by
    intro g m
    rw [hω, map_one]; rfl
  refine ⟨hV, fun cT => ?_, fun cS => ?_⟩
  · refine half he _ _ comm (IsVacAt ψ S T P) fixS fixT ιS ιT (fun g => (rS _).1 ⟨g, rfl⟩)
      (fun g hg => (rT g).2 hg) (fun bT hb => ?_) cT
    obtain ⟨bS, hbS⟩ := h1 bT fun s hs k hk => by
      apply Subtype.ext
      rw [ωT, coe_sum_smul]
      simp only [ωT]
      exact hb s ((hvac s).1 hs) _ ((kT k).2 hk)
    refine ⟨bS, fun u hu => ?_⟩
    have := congrArg Subtype.val (hbS ⟨u, hM u hu⟩ ((hvac _).2 hu))
    rw [coe_sum_smul, coe_sum_smul] at this
    simpa only [ωS, ωT] using this
  · suffices h : ∃ cT, ∀ u, IsVacAt ψ S T P u →
        opOf (om.comp (MonoidHom.inr _ _)) P cT u = opOf (om.comp (MonoidHom.inl _ _)) P cS u from
      h.imp fun cT h u hu => (h u hu).symm
    refine half he _ _ (fun g h u => (comm h g u).symm) (IsVacAt ψ S T P) fixT fixS ιT ιS (fun g => (rT _).1 ⟨g, rfl⟩)
      (fun g hg => (rS g).2 hg) (fun bS hb => ?_) cS
    obtain ⟨bT, hbT⟩ := h2 bS fun s hs k hk => by
      apply Subtype.ext
      rw [ωS, coe_sum_smul]
      simp only [ωS]
      exact hb s ((hvac s).1 hs) _ ((kS k).2 hk)
    refine ⟨bT, fun u hu => ?_⟩
    have := congrArg Subtype.val (hbT ⟨u, hM u hu⟩ ((hvac _).2 hu))
    rw [coe_sum_smul, coe_sum_smul] at this
    simpa only [ωS, ωT] using this

end GlobalTheory.Hk3.CorrInert

end
