import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNefFibresAmple
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNefAmpleFibre
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLiftModel
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothMetricOfIsSmoothHerm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

/- English proof (translation)
Establish `h` using `GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.isProjVarQ_of_isArithVar hP`. Conclude with `⟨(GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiProjPrime_iff _).mp h.1, h.2⟩`.
-/
theorem isProjVarF_map_of_isArithVar {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {D : ℕ} (hP : IsArithVar P (D + 1)) :
    IsProjVarF (P.map (MvPolynomial.map (Int.castRingHom ℚ))) D := by
  classical
  have h := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.isProjVarQ_of_isArithVar hP
  exact ⟨(GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiProjPrime_iff _).mp h.1, h.2⟩

section Basis

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

/- English proof (translation)
Establish `hdeg : ∀ {τ : Type} [Fintype τ] (m : (Σ _ : Unit, τ) →₀ ℕ), m.degree = ∑ i, m ⟨(), i⟩`. Introduce `τ _ m`. Rewrite using `[Finsupp.degree_apply, Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => by`. Simplify using `using hx), Fintype.sum_sigma, Fintype.sum_unique]`. Establish `hw : ∀ {τ : Type} (m : τ →₀ ℕ), Finsupp.weight 1 m = m.degree`.

Introduce `τ m`. Rewrite using `[Finsupp.degree_eq_weight_one]`. Both sides reduce to the same expression. Establish `hH : g.IsHomogeneous (d ())`. Introduce `m hm`.

Rewrite using `[hw, hdeg]`. Conclude with `hg m (mem_support_iff.mpr hm) ()`. Establish `hL : ∀ p : Σ _ : Unit, κ, (∑ i, C (c p.2 i) * X (⟨(), i⟩ : Σ _ : Unit, κ') : MRing (fun _ : Unit => κ')).IsHomogeneous 1` using `fun p => IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_C_mul_X _ _`. Establish `h` using `hH.aeval _ hL`. Rewrite `h` using `[one_mul]`.

Introduce `m hm k`. Use `h (mem_support_iff.mp hm)` as an intermediate fact. Rewrite `this` using `[hw, hdeg]`. Conclude with `this`.
-/
theorem isMultiHomog_aeval_linear {κ κ' : Type} [Fintype κ] [Fintype κ'] (c : κ → κ' → ℤ)
    {g : MRing (fun _ : Unit => κ)} {d : Unit → ℕ} (hg : IsMultiHomog g d) :
    IsMultiHomog (aeval (fun p : Σ _ : Unit, κ => ∑ i, C (c p.2 i) * X (⟨(), i⟩ : Σ _ : Unit, κ')) g) d := by
  have hdeg : ∀ {τ : Type} [Fintype τ] (m : (Σ _ : Unit, τ) →₀ ℕ), m.degree = ∑ i, m ⟨(), i⟩ := by
    intro τ _ m
    classical
    rw [Finsupp.degree_apply, Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => by
      simpa using hx), Fintype.sum_sigma, Fintype.sum_unique]
  have hw : ∀ {τ : Type} (m : τ →₀ ℕ), Finsupp.weight 1 m = m.degree := by
    intro τ m
    rw [Finsupp.degree_eq_weight_one]
    rfl
  have hH : g.IsHomogeneous (d ()) := by
    intro m hm
    rw [hw, hdeg]
    exact hg m (mem_support_iff.mpr hm) ()
  have hL : ∀ p : Σ _ : Unit, κ,
      (∑ i, C (c p.2 i) * X (⟨(), i⟩ : Σ _ : Unit, κ') : MRing (fun _ : Unit => κ')).IsHomogeneous 1 :=
    fun p => IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_C_mul_X _ _
  have h := hH.aeval _ hL
  rw [one_mul] at h
  intro m hm k
  have := h (mem_support_iff.mp hm)
  rw [hw, hdeg] at this
  exact this

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Set `L : Submodule ℤ Ω` to `Submodule.span ℤ (Set.range x')`. Establish `: Module.Finite ℤ L` using `Module.Finite.span_of_finite ℤ (Set.finite_range x')`. Set `b` to `Module.Free.chooseBasis ℤ L`. Set `x'' : Module.Free.ChooseBasisIndex ℤ L → Ω` to `fun i => (b i : Ω)`. Establish `hL : L ≤ (chartLat y n 1).toIntSubmodule` using `Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hmem j)`.

Set `cf : ι' → Module.Free.ChooseBasisIndex ℤ L → ℤ` to `fun j => b.repr ⟨x' j, Submodule.subset_span ⟨j, rfl⟩⟩`. Establish `hexp : ∀ j, x' j = ∑ i, (cf j i : Ω) * x'' i`. Introduce `j`. Establish `h` using `congrArg Subtype.val (b.sum_repr ⟨x' j, Submodule.subset_span ⟨j, rfl⟩⟩)`. Rewrite `h` using `[Submodule.coe_sum]`.

Use `h.symm.trans (Finset.sum_congr rfl fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul, zsmul_eq_mul]`. Use `⟨_, inferInstance, x'', fun i => hL (b i).2, b.linearIndependent.map' L.subtype L.ker_subtype, fun c hc => ?_, fun s => ?_⟩` and prove the remaining obligations. Take `⟨u, hu, hsum⟩` from `hgen c hc`. Use `⟨fun i => ∑ j, (cf j i : Ω) * u j, fun i => ?_, ?_⟩` and prove the remaining obligations.

Conclude with `Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) (hu j)`. Rewrite using `[← hsum]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`. Use `_ = ∑ j, u j * (x' j * ∏ k, y ⟨k, c k⟩ ^ (-n k)) := Finset.sum_congr rfl fun j _ => by rw [← hexp j]`. Take `⟨d, g, h, hg, hh, hh0, hgh⟩` from `hbir s`. Set `σ : MRing (fun _ : Unit => ι') →ₐ[ℤ] MRing (fun _ : Unit => Module.Free.ChooseBasisIndex ℤ L)` to `aeval fun p => ∑ i, C (cf p.2 i) * X ⟨(), i⟩`. Establish `hev : ∀ f, aeval (fun p : Σ _ : Unit, Module.Free.ChooseBasisIndex ℤ L => x'' p.2) (σ f) = aeval (fun p : Σ _ : Unit, ι' => x' p.2) f`.

Introduce `f`. Rewrite using `[← AlgHom.comp_apply, comp_aeval]`. Use `congr 2`. Use function extensionality and compare the values at `p`. Simplify using `[hexp p.2]`.

Use `⟨d, σ g, σ h, isMultiHomog_aeval_linear cf hg, isMultiHomog_aeval_linear cf hh, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hev]`. Conclude with `hh0`. Rewrite using `[hev, hev]`. Conclude with `hgh`.
-/
theorem exists_linearIndependent_of_generates (y : (Σ k, ι k) → Ω) (n : K → ℤ) {ι' : Type} [Fintype ι']
    (x' : ι' → Ω) (hmem : ∀ j, x' j ∈ chartLat y n 1) (hgen : KH.GeneratesOn y n x')
    (hbir : Birational (fun p : Σ _ : Unit, ι' => x' p.2)) :
    ∃ (ι'' : Type) (_ : Fintype ι'') (x'' : ι'' → Ω), (∀ j, x'' j ∈ chartLat y n 1) ∧
      LinearIndependent ℤ x'' ∧ KH.GeneratesOn y n x'' ∧ Birational (fun p : Σ _ : Unit, ι'' => x'' p.2) := by
  classical
  let L : Submodule ℤ Ω := Submodule.span ℤ (Set.range x')
  have : Module.Finite ℤ L := Module.Finite.span_of_finite ℤ (Set.finite_range x')
  let b := Module.Free.chooseBasis ℤ L
  let x'' : Module.Free.ChooseBasisIndex ℤ L → Ω := fun i => (b i : Ω)
  have hL : L ≤ (chartLat y n 1).toIntSubmodule :=
    Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hmem j)
  let cf : ι' → Module.Free.ChooseBasisIndex ℤ L → ℤ :=
    fun j => b.repr ⟨x' j, Submodule.subset_span ⟨j, rfl⟩⟩
  have hexp : ∀ j, x' j = ∑ i, (cf j i : Ω) * x'' i := by
    intro j
    have h := congrArg Subtype.val (b.sum_repr ⟨x' j, Submodule.subset_span ⟨j, rfl⟩⟩)
    rw [Submodule.coe_sum] at h
    refine h.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [Submodule.coe_smul, zsmul_eq_mul]
  refine ⟨_, inferInstance, x'', fun i => hL (b i).2, b.linearIndependent.map' L.subtype L.ker_subtype,
    fun c hc => ?_, fun s => ?_⟩
  · obtain ⟨u, hu, hsum⟩ := hgen c hc
    refine ⟨fun i => ∑ j, (cf j i : Ω) * u j, fun i => ?_, ?_⟩
    · exact Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) (hu j)
    · rw [← hsum]
      calc ∑ i, (∑ j, (cf j i : Ω) * u j) * (x'' i * ∏ k, y ⟨k, c k⟩ ^ (-n k))
          = ∑ j, u j * ((∑ i, (cf j i : Ω) * x'' i) * ∏ k, y ⟨k, c k⟩ ^ (-n k)) := by
            simp only [Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        _ = ∑ j, u j * (x' j * ∏ k, y ⟨k, c k⟩ ^ (-n k)) :=
            Finset.sum_congr rfl fun j _ => by rw [← hexp j]
  · obtain ⟨d, g, h, hg, hh, hh0, hgh⟩ := hbir s
    let σ : MRing (fun _ : Unit => ι') →ₐ[ℤ] MRing (fun _ : Unit => Module.Free.ChooseBasisIndex ℤ L) :=
      aeval fun p => ∑ i, C (cf p.2 i) * X ⟨(), i⟩
    have hev : ∀ f, aeval (fun p : Σ _ : Unit, Module.Free.ChooseBasisIndex ℤ L => x'' p.2) (σ f) =
        aeval (fun p : Σ _ : Unit, ι' => x' p.2) f := by
      intro f
      rw [← AlgHom.comp_apply, comp_aeval]
      congr 2
      funext p
      simp [hexp p.2]
    refine ⟨d, σ g, σ h, isMultiHomog_aeval_linear cf hg, isMultiHomog_aeval_linear cf hh, ?_, ?_⟩
    · rw [hev]; exact hh0
    · rw [hev, hev]; exact hgh

end Basis

/- English proof (translation)
Introduce `K _ ι _ Ω _ _ y D α t I hI hV hbir ht hnef hnefQ`. Set `_ : LinearOrder K` to `LinearOrder.lift' _ (Fintype.equivFin K).injective`. Set `_ : ∀ k, LinearOrder (ι k)` to `fun k => LinearOrder.lift' _ (Fintype.equivFin (ι k)).injective`. Establish `hnum : 0 < t.num` using `Rat.num_pos.mpr ht`. Use `set p : ℕ := t.num.toNat with hp_def`.

Use `set q : ℕ := t.den with hq_def`. Establish `hp : 1 ≤ p` using `by omega`. Establish `hq : 1 ≤ q` using `t.den_pos`. Establish `hpn : ((p : ℤ) : ℚ) = t.num`. Rewrite using `[hp_def, Int.toNat_of_nonneg hnum.le]`.

Establish `htq : t = (p : ℚ) / q`. Rewrite using `[hq_def, ← Int.cast_natCast, hpn]`. Conclude with `(Rat.num_div_den t).symm`. Establish `hGen` using `hKA ℚ K ι I (KH.genIdeal y) D α q p hI (isProjVarF_map_of_isArithVar hV) hnefQ hq hp`. Establish `hFib : ∀ ℓ : ℕ, ℓ.Prime → KH.AmpleV (ZMod ℓ) (fibreIdeal ℓ y) (q • α + fun _ => (p : ℤ))`.

Introduce `ℓ hℓ`. Establish `h` using `hNF K ι Ω y D α q p ℓ hV hnef hq hp hℓ`. Rewrite `h` using `[natCast_zsmul]`. Then use the resulting hypothesis. Establish `hGen2` using `hKA ℚ K ι I (KH.genIdeal y) D α (2 * q) (2 * p - 1) hI (isProjVarF_map_of_isArithVar hV) hnefQ (by omega) (by omega)`. Establish `hExtra : ∃ c : ℕ, 1 ≤ c ∧ KH.AmpleV ℚ (KH.genIdeal y) (c • (q • α + fun _ => (p : ℤ)) - fun _ => 1)`.

Use `⟨2, by norm_num, ?_⟩` and prove the remaining obligations. Establish `he : (2 • (q • α + fun _ => (p : ℤ)) - fun _ => (1 : ℤ) : K → ℤ) = (2 * q) • α + fun _ => ((2 * p - 1 : ℕ) : ℤ)`. Use function extensionality and compare the values at `k`. Simplify using `only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]`. Simplify using `only [nsmul_eq_mul]`.

Rewrite using `[Nat.cast_sub (by omega)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[he]`. Conclude with `hGen2`.

Take `⟨a, ι', _, x', ha, hmem, hgen, hbir'⟩` from `hLM K ι Ω y D _ hV hbir hGen hExtra hFib`. Take `⟨ι'', _, x'', hmem'', hli, hgen'', hbir''⟩` from `exists_linearIndependent_of_generates y _ x' hmem hgen hbir'`. Use `⟨a * q, _, ι'', inferInstance, x'', Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), fun k => ?_, hmem'', hli, hgen'', hbir''⟩` and prove the remaining obligations. Establish `hq0 : (q : ℚ) ≠ 0` using `by exact_mod_cast (show q ≠ 0 by omega)`. Simplify using `only [Pi.smul_apply, Pi.add_apply, nsmul_eq_mul, Int.cast_mul, Int.cast_add, Int.cast_natCast, Nat.cast_mul, htq]`.

Clear the denominators using the available nonvanishing facts. Simplify using `only [Pi.mul_apply, Pi.natCast_apply]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Lift.proof (hKA : KH.KAmpStatement) (hNF : NefAmpleFibre.Statement) (hLM : LiftModel.Statement) :
    Lift.Statement := by
  intro K _ ι _ Ω _ _ y D α t I hI hV hbir ht hnef hnefQ
  classical
  let _ : LinearOrder K := LinearOrder.lift' _ (Fintype.equivFin K).injective
  let _ : ∀ k, LinearOrder (ι k) := fun k => LinearOrder.lift' _ (Fintype.equivFin (ι k)).injective
  have hnum : 0 < t.num := Rat.num_pos.mpr ht
  set p : ℕ := t.num.toNat with hp_def
  set q : ℕ := t.den with hq_def
  have hp : 1 ≤ p := by omega
  have hq : 1 ≤ q := t.den_pos
  have hpn : ((p : ℤ) : ℚ) = t.num := by
    rw [hp_def, Int.toNat_of_nonneg hnum.le]
  have htq : t = (p : ℚ) / q := by
    rw [hq_def, ← Int.cast_natCast, hpn]
    exact (Rat.num_div_den t).symm
  have hGen := hKA ℚ K ι I (KH.genIdeal y) D α q p hI (isProjVarF_map_of_isArithVar hV) hnefQ hq hp
  have hFib : ∀ ℓ : ℕ, ℓ.Prime → KH.AmpleV (ZMod ℓ) (fibreIdeal ℓ y) (q • α + fun _ => (p : ℤ)) := by
    intro ℓ hℓ
    have h := hNF K ι Ω y D α q p ℓ hV hnef hq hp hℓ
    rwa [natCast_zsmul] at h
  have hGen2 := hKA ℚ K ι I (KH.genIdeal y) D α (2 * q) (2 * p - 1) hI (isProjVarF_map_of_isArithVar hV) hnefQ
    (by omega) (by omega)
  have hExtra : ∃ c : ℕ, 1 ≤ c ∧
      KH.AmpleV ℚ (KH.genIdeal y) (c • (q • α + fun _ => (p : ℤ)) - fun _ => 1) := by
    refine ⟨2, by norm_num, ?_⟩
    have he : (2 • (q • α + fun _ => (p : ℤ)) - fun _ => (1 : ℤ) : K → ℤ) =
        (2 * q) • α + fun _ => ((2 * p - 1 : ℕ) : ℤ) := by
      funext k
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
      simp only [nsmul_eq_mul]
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [he]
    exact hGen2
  obtain ⟨a, ι', _, x', ha, hmem, hgen, hbir'⟩ := hLM K ι Ω y D _ hV hbir hGen hExtra hFib
  obtain ⟨ι'', _, x'', hmem'', hli, hgen'', hbir''⟩ :=
    exists_linearIndependent_of_generates y _ x' hmem hgen hbir'
  refine ⟨a * q, _, ι'', inferInstance, x'', Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
    fun k => ?_, hmem'', hli, hgen'', hbir''⟩
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  simp only [Pi.smul_apply, Pi.add_apply, nsmul_eq_mul, Int.cast_mul, Int.cast_add,
    Int.cast_natCast, Nat.cast_mul, htq]
  field_simp
  simp only [Pi.mul_apply, Pi.natCast_apply]
  push_cast
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
