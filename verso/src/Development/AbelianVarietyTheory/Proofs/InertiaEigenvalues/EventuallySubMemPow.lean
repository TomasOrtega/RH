import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Acris0TorsionFree
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOrbitPadicComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisMembershipSpanIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapAinfInvPrimeBdRPlusInjective
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.AcrisGal

open Filter Topology

variable {l : ℕ} [hl : Fact l.Prime]

/- English proof (translation)
Apply `GlobalTheory.RingIface.sigO_coe` to reduce the goal to its premises.
-/
private theorem sigO_coe_pt (g : Per.Gq l) (y : Per.OC l) :
    ((Per.σO g y : Per.OC l) : ℂ_[l]) = Per.σC g (y : ℂ_[l]) := by
  apply GlobalTheory.RingIface.sigO_coe

/- English proof (translation)
Express the relevant statement in the definitionally equal form `_ = algebraMap (Per.Ainf l) (Per.Acris l) x`. Use `symm`. Apply `GlobalTheory.RingIface.tower` to reduce the goal to its premises.
-/
private theorem tower_pt (x : Per.Ainf l) : algebraMap (Per.Acris0 l) (Per.Acris l)
    (algebraMap (Per.Ainf l) (Per.Acris0 l) x) = ainfToAcris l x := by
  change _ = algebraMap (Per.Ainf l) (Per.Acris l) x
  symm
  apply GlobalTheory.RingIface.tower

/- English proof (translation)
Establish `hd : DenseRange (fun x : Om l => (x : ℂ_[l]))` using `UniformSpace.Completion.denseRange_coe`. Take `⟨x, hx⟩` from `hd.exists_dist_lt y (half_pos hε)`. Rewrite `hx` using `[dist_eq_norm]`. Use `filter_upwards [GlobalTheory.Cyc.eventually_apply_eq x 1] with g hg`. Establish `e : Per.σC g y - y = Per.σC g (y - x) - (y - x)`.

Rewrite using `[map_sub, GlobalTheory.RingBasics.σC_coe, hg, AlgEquiv.one_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem eventually_norm_σC_sub_lt (y : ℂ_[l]) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ g : GQ l in 𝓝 1, ‖Per.σC g y - y‖ < ε := by
  have hd : DenseRange (fun x : Om l => (x : ℂ_[l])) := UniformSpace.Completion.denseRange_coe
  obtain ⟨x, hx⟩ := hd.exists_dist_lt y (half_pos hε)
  rw [dist_eq_norm] at hx
  filter_upwards [GlobalTheory.Cyc.eventually_apply_eq x 1] with g hg
  have e : Per.σC g y - y = Per.σC g (y - x) - (y - x) := by
    rw [map_sub, GlobalTheory.RingBasics.σC_coe, hg, AlgEquiv.one_apply]; ring
  rw [e]
  calc ‖Per.σC g (y - x) - (y - x)‖ ≤ ‖Per.σC g (y - x)‖ + ‖y - x‖ := norm_sub_le _ _
    _ < ε := by rw [GlobalTheory.RingBasics.norm_σC]; linarith

/- English proof (translation)
Establish `h0 : ((l : ℕ) : ℂ_[l]) ≠ 0` using `GlobalTheory.RingBasics.p_ne_zero`. Use `⟨⟨(z : ℂ_[l]) / l, (GlobalTheory.RingBasics.mem_OC _).2 ?_⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[norm_div]`. Conclude with `div_le_one_of_le₀ hz (norm_nonneg _)`. Express the relevant statement in the definitionally equal form `(z : ℂ_[l]) = ((l : Per.OC l) : ℂ_[l]) * ((z : ℂ_[l]) / l)`.

Establish `: ((l : Per.OC l) : ℂ_[l]) = l` using `by simp`. Rewrite using `[this]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_eq_l_mul (z : Per.OC l) (hz : ‖(z : ℂ_[l])‖ ≤ ‖((l : ℕ) : ℂ_[l])‖) :
    ∃ c : Per.OC l, z = (l : Per.OC l) * c := by
  have h0 : ((l : ℕ) : ℂ_[l]) ≠ 0 := GlobalTheory.RingBasics.p_ne_zero
  refine ⟨⟨(z : ℂ_[l]) / l, (GlobalTheory.RingBasics.mem_OC _).2 ?_⟩, Subtype.ext ?_⟩
  · rw [norm_div]; exact div_le_one_of_le₀ hz (norm_nonneg _)
  · change (z : ℂ_[l]) = ((l : Per.OC l) : ℂ_[l]) * ((z : ℂ_[l]) / l)
    have : ((l : Per.OC l) : ℂ_[l]) = l := by simp
    rw [this]; field_simp

variable {ξ : Per.Ainf l}

/- English proof (translation)
Establish `hl0 : (0 : ℝ) < ‖((l : ℕ) : ℂ_[l])‖` using `norm_pos_iff.2 GlobalTheory.RingBasics.p_ne_zero`. Use `filter_upwards [eventually_norm_σC_sub_lt ((Per.θ l y : Per.OC l) : ℂ_[l]) hl0] with g hg`. Establish `h1 : Per.θ l (Per.σA g y - y) = Per.σO g (Per.θ l y) - Per.θ l y` using `by rw [map_sub, GlobalTheory.RingBasics.θ_σA]`. Take `⟨c, hc⟩` from `exists_eq_l_mul (Per.σO g (Per.θ l y) - Per.θ l y) (by rw [AddSubgroupClass.coe_sub, sigO_coe_pt]; exact hg.le)`. Take `⟨c', rfl⟩` from `GlobalTheory.MemLoc.ThetaD.θ_surj l c`.

Establish `hk : Per.σA g y - y - (l : Per.Ainf l) * c' ∈ RingHom.ker (Per.θ l)`. Rewrite using `[RingHom.mem_ker, map_sub, h1, hc, map_mul, map_natCast, sub_self]`. Rewrite `hk` using `[hξ, Ideal.mem_span_singleton']`. Take `⟨d, hd⟩` from `hk`. Rewrite using `[Ideal.mem_span_pair]`.

Conclude with `⟨c', d, by linear_combination hd⟩`.
-/
theorem eventually_sub_mem_one (hξ : RingHom.ker (Per.θ l) = Ideal.span {ξ}) (y : Per.Ainf l) :
    ∀ᶠ g : GQ l in 𝓝 1, Per.σA g y - y ∈ Ideal.span {((l : ℕ) : Per.Ainf l), ξ} := by
  have hl0 : (0 : ℝ) < ‖((l : ℕ) : ℂ_[l])‖ := norm_pos_iff.2 GlobalTheory.RingBasics.p_ne_zero
  filter_upwards [eventually_norm_σC_sub_lt ((Per.θ l y : Per.OC l) : ℂ_[l]) hl0] with g hg
  have h1 : Per.θ l (Per.σA g y - y) = Per.σO g (Per.θ l y) - Per.θ l y := by rw [map_sub, GlobalTheory.RingBasics.θ_σA]
  obtain ⟨c, hc⟩ := exists_eq_l_mul (Per.σO g (Per.θ l y) - Per.θ l y)
    (by rw [AddSubgroupClass.coe_sub, sigO_coe_pt]; exact hg.le)
  obtain ⟨c', rfl⟩ := GlobalTheory.MemLoc.ThetaD.θ_surj l c
  have hk : Per.σA g y - y - (l : Per.Ainf l) * c' ∈ RingHom.ker (Per.θ l) := by
    rw [RingHom.mem_ker, map_sub, h1, hc, map_mul, map_natCast, sub_self]
  rw [hξ, Ideal.mem_span_singleton'] at hk
  obtain ⟨d, hd⟩ := hk
  rw [Ideal.mem_span_pair]
  exact ⟨c', d, by linear_combination hd⟩

/- English proof (translation)
Use `set I : Ideal (Per.Ainf l) := Ideal.span {((l : ℕ) : Per.Ainf l), ξ} with hI`. Establish `hlI : ((l : ℕ) : Per.Ainf l) ∈ I` using `Ideal.subset_span (by simp)`. Establish `ht : ∀ z : Per.Fl l, ∀ᶠ g : GQ l in 𝓝 1, Per.σA g (WittVector.teichmuller l z) - WittVector.teichmuller l z ∈ I ^ (N + 1)`. Introduce `z`. Take `⟨w, rfl⟩` from `(iterateFrobeniusEquiv (Per.Fl l) l N).surjective z`.

Use `filter_upwards [eventually_sub_mem_one hξ (WittVector.teichmuller l w)] with g hg`. Use `SModEq.sub_mem.1 ((SModEq.sub_mem.2 hg).pow_pow_add_one hlI N)` as an intermediate fact. Rewrite using `[iterateFrobeniusEquiv_def, map_pow, map_pow]`. Conclude with `this`. Take `⟨c, hc⟩` from `WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff y N`.

Establish `hall` using `(Filter.eventually_all_finset (Finset.Iic N)).2 (fun i _ => ht ((((_root_.frobeniusEquiv (Per.Fl l) l).symm ^ i) (y.coeff i))))`. Use `filter_upwards [hall] with g hg`. Rewrite `hc` using `[sub_eq_iff_eq_add]`. Rewrite using `[hc, map_add, map_mul, map_pow, map_natCast, map_sum, add_sub_add_comm, ← mul_sub, ← Finset.sum_sub_distrib]`. Use `add_mem (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hlI _)) (sum_mem fun i hi => ?_)` and prove the remaining obligations.

Rewrite using `[map_mul, map_pow, map_natCast, ← sub_mul]`. Conclude with `Ideal.mul_mem_right _ _ (hg i hi)`.
-/
theorem eventually_sub_mem_pow (hξ : RingHom.ker (Per.θ l) = Ideal.span {ξ}) (N : ℕ) (y : Per.Ainf l) :
    ∀ᶠ g : GQ l in 𝓝 1, Per.σA g y - y ∈ Ideal.span {((l : ℕ) : Per.Ainf l), ξ} ^ (N + 1) := by
  set I : Ideal (Per.Ainf l) := Ideal.span {((l : ℕ) : Per.Ainf l), ξ} with hI
  have hlI : ((l : ℕ) : Per.Ainf l) ∈ I := Ideal.subset_span (by simp)
  have ht : ∀ z : Per.Fl l, ∀ᶠ g : GQ l in 𝓝 1,
      Per.σA g (WittVector.teichmuller l z) - WittVector.teichmuller l z ∈ I ^ (N + 1) := by
    intro z
    obtain ⟨w, rfl⟩ := (iterateFrobeniusEquiv (Per.Fl l) l N).surjective z
    filter_upwards [eventually_sub_mem_one hξ (WittVector.teichmuller l w)] with g hg
    have := SModEq.sub_mem.1 ((SModEq.sub_mem.2 hg).pow_pow_add_one hlI N)
    rw [iterateFrobeniusEquiv_def, map_pow, map_pow]
    exact this
  obtain ⟨c, hc⟩ := WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff y N
  have hall := (Filter.eventually_all_finset (Finset.Iic N)).2
    (fun i _ => ht ((((_root_.frobeniusEquiv (Per.Fl l) l).symm ^ i) (y.coeff i))))
  filter_upwards [hall] with g hg
  rw [sub_eq_iff_eq_add] at hc
  rw [hc, map_add, map_mul, map_pow, map_natCast, map_sum, add_sub_add_comm, ← mul_sub,
    ← Finset.sum_sub_distrib]
  refine add_mem (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hlI _)) (sum_mem fun i hi => ?_)
  rw [map_mul, map_pow, map_natCast, ← sub_mul]
  exact Ideal.mul_mem_right _ _ (hg i hi)

/- English proof (translation)
Establish `hθ : Per.θ l ξ = 0` using `by rw [← RingHom.mem_ker, hξ]; exact Ideal.mem_span_singleton_self ξ`. Establish `hxl : (l : Per.Acris l) ∣ ainfToAcris l ξ ^ l`. Rewrite using `[← factorial_mul_dpow ξ hθ l]`. Take `⟨k, hk⟩` from `Nat.dvd_factorial hl.out.pos le_rfl`. Rewrite using `[hk]`.

Use `push_cast`. Conclude with `Dvd.dvd.mul_right (dvd_mul_right _ _) _`. Rewrite `hz` using `[Ideal.span_insert]`. Establish `h1` using `Ideal.sup_pow_add_le_pow_sup_pow hz`. Rewrite `h1` using `[Ideal.span_singleton_pow, Ideal.span_singleton_pow, Submodule.mem_sup]`.

Take `⟨a, ha, b, hb, rfl⟩` from `h1`. Take `⟨a', rfl⟩` from `Ideal.mem_span_singleton'.1 ha`. Take `⟨b', rfl⟩` from `Ideal.mem_span_singleton'.1 hb`. Rewrite using `[map_add, map_mul, map_mul, map_pow, map_pow, map_natCast, pow_mul]`. Conclude with `dvd_add (Dvd.intro_left _ rfl) (Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hxl N) _)`.
-/
theorem dvd_of_mem (hξ : RingHom.ker (Per.θ l) = Ideal.span {ξ}) (N : ℕ) {z : Per.Ainf l}
    (hz : z ∈ Ideal.span {((l : ℕ) : Per.Ainf l), ξ} ^ (N + l * N)) :
    (l : Per.Acris l) ^ N ∣ ainfToAcris l z := by
  have hθ : Per.θ l ξ = 0 := by rw [← RingHom.mem_ker, hξ]; exact Ideal.mem_span_singleton_self ξ
  have hxl : (l : Per.Acris l) ∣ ainfToAcris l ξ ^ l := by
    rw [← factorial_mul_dpow ξ hθ l]
    obtain ⟨k, hk⟩ := Nat.dvd_factorial hl.out.pos le_rfl
    rw [hk]; push_cast
    exact Dvd.dvd.mul_right (dvd_mul_right _ _) _
  rw [Ideal.span_insert] at hz
  have h1 := Ideal.sup_pow_add_le_pow_sup_pow hz
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow, Submodule.mem_sup] at h1
  obtain ⟨a, ha, b, hb, rfl⟩ := h1
  obtain ⟨a', rfl⟩ := Ideal.mem_span_singleton'.1 ha
  obtain ⟨b', rfl⟩ := Ideal.mem_span_singleton'.1 hb
  rw [map_add, map_mul, map_mul, map_pow, map_pow, map_natCast, pow_mul]
  exact dvd_add (Dvd.intro_left _ rfl) (Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hxl N) _)

/- English proof (translation)
Take `⟨ξ, hξ, -, -⟩` from `GlobalTheory.Prism.exists_generator l`. Use `filter_upwards [eventually_sub_mem_pow hξ (N + l * N) y] with g hg`. Establish `h` using `dvd_of_mem hξ N (Ideal.pow_le_pow_right (Nat.le_succ _) hg)`. Establish `e : galC g (ainfToAcris l y) = ainfToAcris l (Per.σA g y)` using `(GlobalTheory.CrisMaps.sigA_extends g).alg y`. Rewrite using `[e, ← map_sub]` and apply the resulting hypothesis.
-/
theorem eventually_dvd_ainf (N : ℕ) (y : Per.Ainf l) :
    ∀ᶠ g : GQ l in 𝓝 1, (l : Per.Acris l) ^ N ∣ galC g (ainfToAcris l y) - ainfToAcris l y := by
  obtain ⟨ξ, hξ, -, -⟩ := GlobalTheory.Prism.exists_generator l
  filter_upwards [eventually_sub_mem_pow hξ (N + l * N) y] with g hg
  have h := dvd_of_mem hξ N (Ideal.pow_le_pow_right (Nat.le_succ _) hg)
  have e : galC g (ainfToAcris l y) = ainfToAcris l (Per.σA g y) := (GlobalTheory.CrisMaps.sigA_extends g).alg y
  rwa [e, ← map_sub]

/- English proof (translation)
Use `choose c hc using GlobalTheory.RingBasics.exists_pow_div_factorial l`. Establish `hc' : ∀ n : ℕ, (n.factorial : Per.Acris l) * algebraMap ℤ_[l] _ (c n) = (l : Per.Acris l) ^ n` using `fun n => by`. Simplify `congrArg (algebraMap ℤ_[l] (Per.Acris l)) (hc n)` using `only [map_mul, map_natCast, map_pow]`. Use `filter_upwards [eventually_dvd_ainf (N + 1) x] with g ⟨D, hD⟩`. Use `set X := ainfToAcris l x with hX`.

Use `set Y := ∑ m ∈ Finset.range (k + 1), dpow x hx m * (algebraMap ℤ_[l] (Per.Acris l) (c (k - m)) * (l : Per.Acris l) ^ (N * (k - m)) * D ^ (k - m)) with hYdef`. Establish `hY : (k.factorial : Per.Acris l) * Y = (X + (l : Per.Acris l) ^ (N + 1) * D) ^ k`. Rewrite using `[hYdef, add_pow, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Establish `hmk` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)`.

Rewrite using `[← Nat.choose_mul_factorial_mul_factorial hmk, ← factorial_mul_dpow x hx m, mul_pow, ← pow_mul, show (N + 1) * (k - m) = (k - m) + N * (k - m) by ring, pow_add, ← hc' (k - m)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hσ : galC g (dpow x hx k) = Y`. Establish `h1` using `congrArg (galC g) (factorial_mul_dpow x hx k)`.

Rewrite using `[map_mul, map_natCast, map_pow, ← hX, show galC g X = X + (l : Per.Acris l) ^ (N + 1) * D by`. Rewrite using `[← hD]`. Use the proof step `ring] at h1`. Conclude with `sub_eq_zero.1 (acris_nat_cancel k.factorial_ne_zero (by rw [mul_sub, h1, hY, sub_self]))`. Establish `hc0 : algebraMap ℤ_[l] (Per.Acris l) (c 0) = 1` using `by simpa using hc' 0`.

Rewrite using `[hσ, hYdef, Finset.sum_range_succ, Nat.sub_self, hc0, pow_zero, mul_zero, pow_zero, mul_one, mul_one, mul_one, add_sub_cancel_right]`. Use `Finset.dvd_sum fun m hm => Dvd.dvd.mul_left (Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow _ (Nat.le_mul_of_pos_right N (by have := Finset.mem_range.1 hm; omega))) _) _) _` and prove the remaining obligations.
-/
theorem eventually_dvd_dpow {x : Per.Ainf l} (hx : Per.θ l x = 0) (k N : ℕ) :
    ∀ᶠ g : GQ l in 𝓝 1, (l : Per.Acris l) ^ N ∣ galC g (dpow x hx k) - dpow x hx k := by
  choose c hc using GlobalTheory.RingBasics.exists_pow_div_factorial l
  have hc' : ∀ n : ℕ, (n.factorial : Per.Acris l) * algebraMap ℤ_[l] _ (c n) = (l : Per.Acris l) ^ n :=
    fun n => by
      simpa only [map_mul, map_natCast, map_pow] using congrArg (algebraMap ℤ_[l] (Per.Acris l)) (hc n)
  filter_upwards [eventually_dvd_ainf (N + 1) x] with g ⟨D, hD⟩
  set X := ainfToAcris l x with hX
  set Y := ∑ m ∈ Finset.range (k + 1), dpow x hx m * (algebraMap ℤ_[l] (Per.Acris l) (c (k - m)) *
    (l : Per.Acris l) ^ (N * (k - m)) * D ^ (k - m)) with hYdef
  have hY : (k.factorial : Per.Acris l) * Y = (X + (l : Per.Acris l) ^ (N + 1) * D) ^ k := by
    rw [hYdef, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmk := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    rw [← Nat.choose_mul_factorial_mul_factorial hmk, ← factorial_mul_dpow x hx m, mul_pow, ← pow_mul,
      show (N + 1) * (k - m) = (k - m) + N * (k - m) by ring, pow_add, ← hc' (k - m)]
    push_cast
    ring
  have hσ : galC g (dpow x hx k) = Y := by
    have h1 := congrArg (galC g) (factorial_mul_dpow x hx k)
    rw [map_mul, map_natCast, map_pow, ← hX, show galC g X = X + (l : Per.Acris l) ^ (N + 1) * D by
      rw [← hD]; ring] at h1
    exact sub_eq_zero.1 (acris_nat_cancel k.factorial_ne_zero (by rw [mul_sub, h1, hY, sub_self]))
  have hc0 : algebraMap ℤ_[l] (Per.Acris l) (c 0) = 1 := by simpa using hc' 0
  rw [hσ, hYdef, Finset.sum_range_succ, Nat.sub_self, hc0, pow_zero, mul_zero, pow_zero, mul_one, mul_one,
    mul_one, add_sub_cancel_right]
  refine Finset.dvd_sum fun m hm => Dvd.dvd.mul_left (Dvd.dvd.mul_right (Dvd.dvd.mul_left
    (pow_dvd_pow _ (Nat.le_mul_of_pos_right N (by have := Finset.mem_range.1 hm; omega))) _) _) _

variable (l) in

def fixNear : Subring (Per.Acris l) where
  carrier := {x | ∀ N : ℕ, ∀ᶠ g : GQ l in 𝓝 1, (l : Per.Acris l) ^ N ∣ galC g x - x}
  mul_mem' {a b} ha hb N := by
    filter_upwards [ha N, hb N] with g ⟨u, hu⟩ ⟨v, hv⟩
    refine ⟨galC g a * v + u * b, ?_⟩
    rw [map_mul]
    linear_combination galC g a * hv + b * hu
  one_mem' N := .of_forall fun g => ⟨0, by simp⟩
  add_mem' {a b} ha hb N := by
    filter_upwards [ha N, hb N] with g ⟨u, hu⟩ ⟨v, hv⟩
    exact ⟨u + v, by rw [map_add]; linear_combination hu + hv⟩
  zero_mem' N := .of_forall fun g => ⟨0, by simp⟩
  neg_mem' {a} ha N := by
    filter_upwards [ha N] with g ⟨u, hu⟩
    exact ⟨-u, by rw [map_neg]; linear_combination -hu⟩

/- English proof (translation)
Take `⟨e, he⟩` from `GlobalTheory.MemLoc.exists_isEps_for_inj l`. Establish `hx : Per.θ l (GlobalTheory.MemLoc.xi e) = 0` using `(GlobalTheory.T.fontaineTheta_eq_zero_iff_fontaineXiElement_dvd l e he _).2 dvd_rfl`. Take `⟨s, hs⟩` from `s`. Establish `key : ∀ y ∈ Submodule.span (Per.Ainf l) {y : Per.AinfP l | ∃ n : ℕ, ((n.factorial : ℕ) : Per.AinfP l) * y = algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.xi e) ^ n}, ∀ hy : y ∈ Per.Acris0 l, algebraMap (Per.Acris0 l) (Per.Acris l) ⟨y, hy⟩ ∈ fixNear l`. Introduce `y hy`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Introduce `hy0`. Take `⟨n, hn⟩` from `hy`. Establish `h1 : (n.factorial : Per.Acris0 l) * ⟨y, hy0⟩ = algebraMap (Per.Ainf l) (Per.Acris0 l) (GlobalTheory.MemLoc.xi e) ^ n` using `Subtype.ext (by simpa using hn)`.

Establish `h2` using `congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) h1`. Rewrite `h2` using `[map_mul, map_natCast, map_pow, tower_pt]`. Rewrite using `[eq_dpow hx h2]`. Conclude with `fun N => eventually_dvd_dpow hx n N`. Consider the case `zero`.

Introduce `h0`. Establish `e0 : (⟨0, h0⟩ : Per.Acris0 l) = 0` using `Subtype.ext rfl`. Rewrite using `[e0, map_zero]`. Conclude with `zero_mem _`. Consider the case `add y z hy hz ihy ihz`.

Introduce `h0`. Establish `hy0` using `(GlobalTheory.MemLoc.mem_Acris0_iff_span l e he y).2 hy`. Establish `hz0` using `(GlobalTheory.MemLoc.mem_Acris0_iff_span l e he z).2 hz`. Establish `e0 : (⟨y + z, h0⟩ : Per.Acris0 l) = ⟨y, hy0⟩ + ⟨z, hz0⟩` using `Subtype.ext rfl`. Rewrite using `[e0, map_add]`.

Conclude with `add_mem (ihy hy0) (ihz hz0)`. Consider the case `smul r y hy ihy`. Introduce `h0`. Establish `hy0` using `(GlobalTheory.MemLoc.mem_Acris0_iff_span l e he y).2 hy`. Establish `e0 : (⟨r • y, h0⟩ : Per.Acris0 l) = algebraMap (Per.Ainf l) (Per.Acris0 l) r * ⟨y, hy0⟩` using `Subtype.ext (Algebra.smul_def r y)`.

Rewrite using `[e0, map_mul, tower_pt]`. Conclude with `mul_mem (fun N => eventually_dvd_ainf N r) (ihy hy0)`. Conclude with `key s ((GlobalTheory.MemLoc.mem_Acris0_iff_span l e he s).1 hs) hs`.
-/
theorem algebraMap_mem_fixNear (s : Per.Acris0 l) :
    algebraMap (Per.Acris0 l) (Per.Acris l) s ∈ fixNear l := by
  obtain ⟨e, he⟩ := GlobalTheory.MemLoc.exists_isEps_for_inj l
  have hx : Per.θ l (GlobalTheory.MemLoc.xi e) = 0 := (GlobalTheory.T.fontaineTheta_eq_zero_iff_fontaineXiElement_dvd l e he _).2 dvd_rfl
  obtain ⟨s, hs⟩ := s
  have key : ∀ y ∈ Submodule.span (Per.Ainf l) {y : Per.AinfP l | ∃ n : ℕ,
      ((n.factorial : ℕ) : Per.AinfP l) * y = algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.xi e) ^ n},
      ∀ hy : y ∈ Per.Acris0 l, algebraMap (Per.Acris0 l) (Per.Acris l) ⟨y, hy⟩ ∈ fixNear l := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      intro hy0
      obtain ⟨n, hn⟩ := hy
      have h1 : (n.factorial : Per.Acris0 l) * ⟨y, hy0⟩ =
          algebraMap (Per.Ainf l) (Per.Acris0 l) (GlobalTheory.MemLoc.xi e) ^ n := Subtype.ext (by simpa using hn)
      have h2 := congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) h1
      rw [map_mul, map_natCast, map_pow, tower_pt] at h2
      rw [eq_dpow hx h2]
      exact fun N => eventually_dvd_dpow hx n N
    | zero =>
      intro h0
      have e0 : (⟨0, h0⟩ : Per.Acris0 l) = 0 := Subtype.ext rfl
      rw [e0, map_zero]; exact zero_mem _
    | add y z hy hz ihy ihz =>
      intro h0
      have hy0 := (GlobalTheory.MemLoc.mem_Acris0_iff_span l e he y).2 hy
      have hz0 := (GlobalTheory.MemLoc.mem_Acris0_iff_span l e he z).2 hz
      have e0 : (⟨y + z, h0⟩ : Per.Acris0 l) = ⟨y, hy0⟩ + ⟨z, hz0⟩ := Subtype.ext rfl
      rw [e0, map_add]; exact add_mem (ihy hy0) (ihz hz0)
    | smul r y hy ihy =>
      intro h0
      have hy0 := (GlobalTheory.MemLoc.mem_Acris0_iff_span l e he y).2 hy
      have e0 : (⟨r • y, h0⟩ : Per.Acris0 l) = algebraMap (Per.Ainf l) (Per.Acris0 l) r * ⟨y, hy0⟩ :=
        Subtype.ext (Algebra.smul_def r y)
      rw [e0, map_mul, tower_pt]
      exact mul_mem (fun N => eventually_dvd_ainf N r) (ihy hy0)
  exact key s ((GlobalTheory.MemLoc.mem_Acris0_iff_span l e he s).1 hs) hs

/- English proof (translation)
Introduce `l _ x n`. Take `⟨s, z, rfl⟩` from `(GlobalTheory.MemLoc.acris_basic l).2.2.1 x n`. Use `filter_upwards [algebraMap_mem_fixNear s n] with g ⟨u, hu⟩`. Use `⟨u + (galC g z - z), ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_mul, map_pow, map_natCast]`.

Take the linear combination `hu`.
-/
theorem galC_sub_dvd_mem_nhds : ∀ (l : ℕ) [Fact l.Prime] (x : Per.Acris l) (n : ℕ),
    {g : GQ l | (l : Per.Acris l) ^ n ∣ galC g x - x} ∈ nhds (1 : GQ l) := by
  intro l _ x n
  obtain ⟨s, z, rfl⟩ := (GlobalTheory.MemLoc.acris_basic l).2.2.1 x n
  filter_upwards [algebraMap_mem_fixNear s n] with g ⟨u, hu⟩
  refine ⟨u + (galC g z - z), ?_⟩
  rw [map_add, map_mul, map_pow, map_natCast]
  linear_combination hu

end GlobalTheory.AcrisGal
