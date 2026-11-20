import Mathlib
import Formalism.JumpKernelCokernel.LengthTheoremsWithEarlier
import Formalism.TruncatedSeriesCounting.EtaDeterminantPolynomialIdentities

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.DCount

open Module PowerSeries

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Take `⟨n, f, hf⟩` from `Module.Finite.exists_fin' O M`. Establish `hI : ∀ i : Fin n, Ideal.span {x} ≤ LinearMap.ker (LinearMap.toSpanSingleton O M (f (Pi.single i 1)))`. Introduce `i`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ rfl`.

Simplify using `[h]`. Set `g : (Fin n → O ⧸ Ideal.span {x}) →ₗ[O] M` to `∑ i, ((Ideal.span {x}).liftQ _ (hI i)) ∘ₗ LinearMap.proj i`. Establish `hg : Function.Surjective g`. Introduce `m`. Take `⟨v, rfl⟩` from `hf m`.

Use `⟨fun i => Submodule.Quotient.mk (v i), ?_⟩` and prove the remaining obligations. Establish `hv : v = ∑ i, v i • Pi.single i (1 : O)`. Use extensionality with `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Use `conv_rhs => rw [hv]`.

Rewrite using `[map_sum, LinearMap.sum_apply]`. Conclude with `Finset.sum_congr rfl fun i _ => by`. Rewrite using `[map_smul]`. Both sides reduce to the same expression. Establish `h1 : Module.length O (O ⧸ Ideal.span {x}) ≠ ⊤` using `Module.length_ne_top_iff.mpr (isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero hx))`.

Establish `h2` using `Module.length_le_of_surjective g hg`. Rewrite `h2` using `[Module.length_pi]`. Introduce `htop`. Rewrite `h2` using `[htop, top_le_iff]`. Break down `WithTop.mul_eq_top_iff.mp h2 with h3 | h3` into its components or cases.

Conclude with `h1 h3.2`. Use `ENat.card_eq_top.mp h3.1` as an intermediate fact. Conclude with `not_finite (Fin n)`.
-/
theorem length_ne_top_of_smul {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M]
    (x : O) (hx : x ≠ 0) (h : ∀ m : M, x • m = 0) : Module.length O M ≠ ⊤ := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' O M
  have hI : ∀ i : Fin n, Ideal.span {x} ≤
      LinearMap.ker (LinearMap.toSpanSingleton O M (f (Pi.single i 1))) := by
    intro i
    rw [Ideal.span_le]
    rintro _ rfl
    simp [h]
  let g : (Fin n → O ⧸ Ideal.span {x}) →ₗ[O] M :=
    ∑ i, ((Ideal.span {x}).liftQ _ (hI i)) ∘ₗ LinearMap.proj i
  have hg : Function.Surjective g := by
    intro m
    obtain ⟨v, rfl⟩ := hf m
    refine ⟨fun i => Submodule.Quotient.mk (v i), ?_⟩
    have hv : v = ∑ i, v i • Pi.single i (1 : O) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hv]
    rw [map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by
      rw [map_smul]; rfl
  have h1 : Module.length O (O ⧸ Ideal.span {x}) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr
      (isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero hx))
  have h2 := Module.length_le_of_surjective g hg
  rw [Module.length_pi] at h2
  intro htop
  rw [htop, top_le_iff] at h2
  rcases WithTop.mul_eq_top_iff.mp h2 with h3 | h3
  · exact h1 h3.2
  · have := ENat.card_eq_top.mp h3.1
    exact not_finite (Fin n)

def satL {O R : Type} [CommRing O] [AddCommGroup R] [Module O R] (l : O) (R' : Submodule O R) : Submodule O R where
  carrier := {z | ∃ t : ℕ, l ^ t • z ∈ R'}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨s, hs⟩ ⟨t, ht⟩
    refine ⟨s + t, ?_⟩
    rw [smul_add, pow_add]
    refine R'.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact R'.smul_mem _ hs
    · rw [mul_smul]; exact R'.smul_mem _ ht
  smul_mem' := by
    rintro c z ⟨t, ht⟩
    exact ⟨t, by rw [smul_comm]; exact R'.smul_mem c ht⟩

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ`. Establish `hd : ϖ ∣ l`. Rewrite `hϖ` using `[IsDiscreteValuationRing.irreducible_iff_uniformizer]`. Rewrite `hl` using `[hϖ, Ideal.mem_span_singleton]`.

Conclude with `hl`. Conclude with `⟨n, Units.mul_left_dvd.mpr (pow_dvd_pow_of_dvd hd n)⟩`.
-/
theorem dvd_pow_of_ne_zero (l : O) (hl : l ∈ IsLocalRing.maximalIdeal O) {r : O} (hr : r ≠ 0) :
    ∃ n : ℕ, r ∣ l ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
  have hd : ϖ ∣ l := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer] at hϖ
    rw [hϖ, Ideal.mem_span_singleton] at hl
    exact hl
  exact ⟨n, Units.mul_left_dvd.mpr (pow_dvd_pow_of_dvd hd n)⟩

/- English proof (translation)
Use `⟨fun r hr a b hab => ?_⟩` and prove the remaining obligations. Establish `hr0 : r ≠ 0` using `hr.ne_zero`. Take `⟨n, s, hs⟩` from `dvd_pow_of_ne_zero l hl hr0`. Proceed by induction on `a using Submodule.Quotient.induction_on with | H a => ?_`. Proceed by induction on `b using Submodule.Quotient.induction_on with | H b => ?_`.

Simplify using `only [← Submodule.Quotient.mk_smul] at hab`. Rewrite `hab`, the goal using `[Submodule.Quotient.eq]`. Take `⟨t, ht⟩` from `hab`. Use `⟨t + n, ?_⟩` and prove the remaining obligations. Establish `: l ^ (t + n) • (a - b) = s • (l ^ t • (r • a - r • b))`.

Rewrite using `[← smul_sub, smul_comm (l ^ t) r, smul_smul s r, mul_comm s r, ← hs, smul_smul, ← pow_add, add_comm n t]`. Rewrite using `[this]`. Conclude with `R'.smul_mem s ht`.
-/
theorem torsionFree_sat {R : Type} [AddCommGroup R] [Module O R] (l : O)
    (hl : l ∈ IsLocalRing.maximalIdeal O) (R' : Submodule O R) :
    Module.IsTorsionFree O (R ⧸ satL l R') := by
  refine ⟨fun r hr a b hab => ?_⟩
  have hr0 : r ≠ 0 := hr.ne_zero
  obtain ⟨n, s, hs⟩ := dvd_pow_of_ne_zero l hl hr0
  induction a using Submodule.Quotient.induction_on with | H a => ?_
  induction b using Submodule.Quotient.induction_on with | H b => ?_
  simp only [← Submodule.Quotient.mk_smul] at hab
  rw [Submodule.Quotient.eq] at hab ⊢
  obtain ⟨t, ht⟩ := hab
  refine ⟨t + n, ?_⟩
  have : l ^ (t + n) • (a - b) = s • (l ^ t • (r • a - r • b)) := by
    rw [← smul_sub, smul_comm (l ^ t) r, smul_smul s r, mul_comm s r, ← hs, smul_smul,
      ← pow_add, add_comm n t]
  rw [this]
  exact R'.smul_mem s ht

variable {R : Type} [AddCommGroup R] [Module O R]

abbrev Aq (O : Type) [CommRing O] (k : ℕ) := PowerSeries O ⧸ Ideal.span {(X : PowerSeries O) ^ k}

abbrev Aql (O : Type) [CommRing O] (k c : ℕ) (l : O) :=
  PowerSeries O ⧸ Ideal.span {(X : PowerSeries O) ^ k, C (l ^ c)}

/- English proof (translation)
The claim follows from `Ideal.span_mono (by simp)`.
-/
theorem spanX_le (k c : ℕ) (l : O) :
    Ideal.span {(X : PowerSeries O) ^ k} ≤ Ideal.span {(X : PowerSeries O) ^ k, C (l ^ c)} :=
  Ideal.span_mono (by simp)

def red (k c : ℕ) (l : O) : Aq O k →ₐ[O] Aql O k c l := Ideal.Quotient.factorₐ O (spanX_le k c l)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem red_mk (k c : ℕ) (l : O) (a : PowerSeries O) :
    red k c l (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a := rfl

/- English proof (translation)
Rewrite using `[Algebra.smul_def]`. Both sides reduce to the same expression.
-/
theorem smul_Aql (k c : ℕ) (l a : O) (y : Aql O k c l) :
    a • y = Ideal.Quotient.mk _ (C a) * y := by
  rw [Algebra.smul_def]; rfl

/- English proof (translation)
Rewrite using `[Algebra.smul_def]`. Both sides reduce to the same expression.
-/
theorem smul_Aq (k : ℕ) (a : O) (y : Aq O k) :
    a • y = Ideal.Quotient.mk _ (C a) * y := by
  rw [Algebra.smul_def]; rfl

/- English proof (translation)
Rewrite using `[smul_Aql, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp)), zero_mul]`.
-/
theorem lc_smul_Aql (k c : ℕ) (l : O) (y : Aql O k c l) : (l ^ c) • y = 0 := by
  rw [smul_Aql, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp)), zero_mul]

/- English proof (translation)
Proceed by induction on `y using Quotient.inductionOn' with | h a => ?_`. Establish `h' : (Ideal.Quotient.mk (Ideal.span {(X : PowerSeries O) ^ k, C (l ^ c)})) a = 0` using `h`. Rewrite `h'` using `[Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_pair]`. Take `⟨u, w, huw⟩` from `h'`. Use `⟨Ideal.Quotient.mk _ w, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_Aq]`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ a = _`. Rewrite using `[← huw, ← map_mul, mul_comm (C (l ^ c)) w, Ideal.Quotient.eq, add_sub_cancel_right]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)`.
-/
theorem red_eq_zero (k c : ℕ) (l : O) (y : Aq O k) (h : red k c l y = 0) :
    ∃ z : Aq O k, y = (l ^ c) • z := by
  induction y using Quotient.inductionOn' with | h a => ?_
  have h' : (Ideal.Quotient.mk (Ideal.span {(X : PowerSeries O) ^ k, C (l ^ c)})) a = 0 := h
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_pair] at h'
  obtain ⟨u, w, huw⟩ := h'
  refine ⟨Ideal.Quotient.mk _ w, ?_⟩
  rw [smul_Aq]
  change Ideal.Quotient.mk _ a = _
  rw [← huw, ← map_mul, mul_comm (C (l ^ c)) w, Ideal.Quotient.eq, add_sub_cancel_right]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

section Main

variable [Module.Free O R] [Module.Finite O R]

/- English proof (translation)
Use `set R'' := satL l R' with hR''`. Use `set π : Module.End O R := q - l • (1 : Module.End O R) with hπ`. Establish `htf : ∀ (a : O) (z : R), a ≠ 0 → a • z = 0 → z = 0` using `fun a z ha h => (smul_eq_zero.mp h).resolve_left ha`. Establish `hq'' : ∀ z ∈ R'', q z ∈ R''`. Introduce and unpack `z ⟨t, ht⟩`.

Conclude with `⟨t, by rw [← map_smul]; exact hR'q _ ht⟩`. Establish `hle : R' ≤ R''` using `fun z hz => ⟨0, by simpa using hz⟩`. Establish `hmap : R''.map π ≤ R''`. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Simplify using `only [hπ, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]`.

Conclude with `R''.sub_mem (hq'' z hz) (R''.smul_mem l hz)`. Establish `hc : ∀ z : ↥R'', (l ^ c • R''.subtype) z ∈ R'` using `fun z => by`. Take `⟨t, ht⟩` from `z.2`. Conclude with `hsat _ t ht`. Set `s : ↥R'' →ₗ[O] ↥R'` to `((l ^ c) • R''.subtype).codRestrict R' hc`.

Set `P : ((j : Fin m') → Aq O (k j)) →ₗ[O] ((j : Fin m') → Aql O (k j) c l)` to `LinearMap.pi (fun j => (red (k j) c l).toLinearMap ∘ₗ LinearMap.proj j)`. Set `jm : ↥R'' →ₗ[O] ((j : Fin m') → Aql O (k j) c l)` to `P ∘ₗ e.toLinearMap ∘ₗ s`. Set `πB : Module.End O ((j : Fin m') → Aql O (k j) c l)` to `LinearMap.pi (fun j : Fin m' => (LinearMap.mulLeft O (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries O) ^ k j, PowerSeries.C (l ^ c)}) ((PowerSeries.X : PowerSeries O) - PowerSeries.C l))).comp (LinearMap.proj (R := O) (φ := fun j : Fin m' => PowerSeries O ⧸ Ideal.sp …`. Establish `hPsurj : Function.Surjective (P ∘ₗ e.toLinearMap)`. Introduce `b`.

Use `choose y hy using fun j => Ideal.Quotient.mk_surjective (b j)`. Use `⟨e.symm (fun j => Ideal.Quotient.mk _ (y j)), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `j`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, P, LinearMap.pi_apply, LinearMap.proj_apply, AlgHom.toLinearMap_apply]`. Rewrite using `[red_mk]`.

Conclude with `hy j`. Establish `: Module.Finite O ((j : Fin m') → Aql O (k j) c l)` using `Module.Finite.of_surjective _ hPsurj`. Establish `hfin : Module.length O ((j : Fin m') → Aql O (k j) c l) ≠ ⊤` using `length_ne_top_of_smul (l ^ c) (pow_ne_zero _ hl0) (fun b => funext fun j => by`. Simplify using `only [Pi.smul_apply, Pi.zero_apply]`. Conclude with `lc_smul_Aql _ _ _ _)`.

Establish `hker : LinearMap.ker jm = R'.comap R''.subtype`. Use extensionality with `z`. Simplify using `only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `hw : ∀ j, ∃ w : Aq O (k j), (e (s z)) j = (l ^ c) • w` using `fun j => red_eq_zero _ _ _ _ (congrFun h j)`. Use `choose w hw using hw`. Establish `hsz : s z = (l ^ c) • e.symm w`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_smul, e.apply_symm_apply]`.

Use function extensionality and compare the values at `j`. Conclude with `hw j`. Establish `h2 : (l ^ c) • (z : R) = (l ^ c) • ((e.symm w : ↥R') : R)` using `congrArg Subtype.val hsz`. Establish `h3` using `htf (l ^ c) ((z : R) - ((e.symm w : ↥R') : R)) (pow_ne_zero _ hl0) (by rw [smul_sub, h2, sub_self])`. Rewrite `h3` using `[sub_eq_zero]`.

Use `(e.symm w).2 using 1` and compare the differences between its conclusion and the goal. Introduce `hz`. Establish `hsz : s z = (l ^ c) • (⟨z, hz⟩ : ↥R')` using `Subtype.ext rfl`. Use function extensionality and compare the values at `j`. Use `show red (k j) c l ((e (s z)) j) = 0`.

Rewrite using `[hsz, map_smul, Pi.smul_apply, map_smul]`. Conclude with `lc_smul_Aql _ _ _ _`. Establish `hequiv : ∀ (x : ↥R'') (hx : π x ∈ R''), jm ⟨π x, hx⟩ = πB (jm x)`. Introduce `x hx`. Use function extensionality and compare the values at `j`.

Establish `hs : s ⟨π x, hx⟩ = ⟨q (s x), hR'q _ (s x).2⟩ - l • s x`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [s, hπ, LinearMap.codRestrict_apply, LinearMap.smul_apply, Submodule.subtype_apply, LinearMap.sub_apply, Module.End.one_apply, Submodule.coe_sub, Submodule.coe_smul, map_smul]`. Rewrite using `[smul_sub, smul_comm (l ^ c) l]`. Use `show red (k j) c l ((e (s ⟨π x, hx⟩)) j) = Ideal.Quotient.mk _ ((PowerSeries.X : PowerSeries O) - PowerSeries.C l) * red (k j) c l ((e (s x)) j)`.

Rewrite using `[hs, map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, he, map_sub, map_smul, map_mul, smul_Aql, map_sub, ← sub_mul]`. Both sides reduce to the same expression. Establish `hJ` using `Formalism.KernelCokernelLengths.lemma_D_joint_form O R π R' R'' _ πB jm hle hmap hfin hker hequiv`. Establish `hT` using `Formalism.KernelCokernelLengths.torsion_kernel_sum_length O l hl0 m' c k`. Use `torsionFree_sat l hlm R'` as an intermediate fact.

Establish `: Module.Free O (R ⧸ R'')` using `Module.free_of_finite_type_torsion_free'`. Set `qb : Module.End O (R ⧸ R'')` to `R''.mapQ R'' q (fun z hz => hq'' z hz)`. Establish `hpow : ∀ (N : ℕ) (z : R), (qb ^ N) (R''.mkQ z) = R''.mkQ ((q ^ N) z)`. Introduce `N`. Proceed by induction on `N with`.

Consider the case `zero => intro z`. Both sides reduce to the same expression. Consider the case `succ N ih => intro z`. Rewrite using `[pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]`. Both sides reduce to the same expression.

Establish `hqb : IsNilpotent qb`. Take `⟨N, hN⟩` from `hq`. Use `⟨N, ?_⟩` and prove the remaining obligations. Apply `Submodule.linearMap_qext` to reduce the goal to its premises. Use extensionality with `z`.

Simplify using `only [LinearMap.comp_apply, hpow, hN, LinearMap.zero_apply, map_zero]`. Establish `hrange : (LinearMap.range π).map R''.mkQ = LinearMap.range (qb - l • (1 : Module.End O (R ⧸ R'')))`. Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨z, rfl⟩, rfl⟩`.

Conclude with `⟨R''.mkQ z, by simp [qb, hπ]⟩`. Introduce and unpack `⟨w', rfl⟩`. Proceed by induction on `w' using Submodule.Quotient.induction_on with | H z => ?_`. Conclude with `⟨π z, ⟨z, rfl⟩, by simp [qb, hπ]⟩`. Establish `hL` using `Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.length_pi_zero_bound O (R ⧸ R'') l hl0 qb hqb`.

Establish `hlen2 : Module.length O (R ⧸ (R'' ⊔ LinearMap.range π)) = (finrank O (R ⧸ R'') : ℕ∞) * Module.length O (O ⧸ Ideal.span {l})`. Rewrite using `[← (Submodule.quotientQuotientEquivQuotientSup R'' (LinearMap.range π)).length_eq, hrange, hL]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← add_mul]`. Use `gcongr`.

Use `push_cast`. Rewrite using `[mul_comm (m' : ℕ∞)]`. Use `gcongr`.
-/
theorem lemmaD_count (l : O) (hl0 : l ≠ 0) (hlm : l ∈ IsLocalRing.maximalIdeal O)
    (q : Module.End O R) (hq : IsNilpotent q) (R' : Submodule O R) (hR'q : ∀ x ∈ R', q x ∈ R')
    (m' : ℕ) (k : Fin m' → ℕ) (e : ↥R' ≃ₗ[O] ((j : Fin m') → Aq O (k j)))
    (he : ∀ (x : ↥R') (j : Fin m'), e ⟨q x, hR'q x x.2⟩ j = Ideal.Quotient.mk _ X * e x j)
    (c : ℕ) (hsat : ∀ z : R, ∀ t : ℕ, l ^ t • z ∈ R' → l ^ c • z ∈ R')
    (ρ : ℕ) (hρ : finrank O (R ⧸ satL l R') ≤ ρ) :
    Module.length O (R ⧸ (R' ⊔ LinearMap.range (q - l • (1 : Module.End O R)))) ≤
      ((ρ + c * m' : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {l}) := by
  set R'' := satL l R' with hR''
  set π : Module.End O R := q - l • (1 : Module.End O R) with hπ
  have htf : ∀ (a : O) (z : R), a ≠ 0 → a • z = 0 → z = 0 := fun a z ha h =>
    (smul_eq_zero.mp h).resolve_left ha
  have hq'' : ∀ z ∈ R'', q z ∈ R'' := by
    rintro z ⟨t, ht⟩
    exact ⟨t, by rw [← map_smul]; exact hR'q _ ht⟩
  have hle : R' ≤ R'' := fun z hz => ⟨0, by simpa using hz⟩
  have hmap : R''.map π ≤ R'' := by
    rintro _ ⟨z, hz, rfl⟩
    simp only [hπ, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact R''.sub_mem (hq'' z hz) (R''.smul_mem l hz)
  have hc : ∀ z : ↥R'', (l ^ c • R''.subtype) z ∈ R' := fun z => by
    obtain ⟨t, ht⟩ := z.2
    exact hsat _ t ht
  let s : ↥R'' →ₗ[O] ↥R' := ((l ^ c) • R''.subtype).codRestrict R' hc
  let P : ((j : Fin m') → Aq O (k j)) →ₗ[O] ((j : Fin m') → Aql O (k j) c l) :=
    LinearMap.pi (fun j => (red (k j) c l).toLinearMap ∘ₗ LinearMap.proj j)
  let jm : ↥R'' →ₗ[O] ((j : Fin m') → Aql O (k j) c l) := P ∘ₗ e.toLinearMap ∘ₗ s
  let πB : Module.End O ((j : Fin m') → Aql O (k j) c l) :=
    LinearMap.pi (fun j : Fin m' =>
      (LinearMap.mulLeft O
        (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries O) ^ k j, PowerSeries.C (l ^ c)})
          ((PowerSeries.X : PowerSeries O) - PowerSeries.C l))).comp
        (LinearMap.proj (R := O) (φ := fun j : Fin m' =>
          PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O) ^ k j, PowerSeries.C (l ^ c)}) j))
  have hPsurj : Function.Surjective (P ∘ₗ e.toLinearMap) := by
    intro b
    choose y hy using fun j => Ideal.Quotient.mk_surjective (b j)
    refine ⟨e.symm (fun j => Ideal.Quotient.mk _ (y j)), ?_⟩
    funext j
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, P,
      LinearMap.pi_apply, LinearMap.proj_apply, AlgHom.toLinearMap_apply]
    rw [red_mk]
    exact hy j
  have : Module.Finite O ((j : Fin m') → Aql O (k j) c l) :=
    Module.Finite.of_surjective _ hPsurj
  have hfin : Module.length O ((j : Fin m') → Aql O (k j) c l) ≠ ⊤ :=
    length_ne_top_of_smul (l ^ c) (pow_ne_zero _ hl0) (fun b => funext fun j => by
      simp only [Pi.smul_apply, Pi.zero_apply]; exact lc_smul_Aql _ _ _ _)
  have hker : LinearMap.ker jm = R'.comap R''.subtype := by
    ext z
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · intro h
      have hw : ∀ j, ∃ w : Aq O (k j), (e (s z)) j = (l ^ c) • w := fun j =>
        red_eq_zero _ _ _ _ (congrFun h j)
      choose w hw using hw
      have hsz : s z = (l ^ c) • e.symm w := by
        apply e.injective
        rw [map_smul, e.apply_symm_apply]
        funext j
        exact hw j
      have h2 : (l ^ c) • (z : R) = (l ^ c) • ((e.symm w : ↥R') : R) := congrArg Subtype.val hsz
      have h3 := htf (l ^ c) ((z : R) - ((e.symm w : ↥R') : R)) (pow_ne_zero _ hl0) (by rw [smul_sub, h2, sub_self])
      rw [sub_eq_zero] at h3
      convert (e.symm w).2 using 1
    · intro hz
      have hsz : s z = (l ^ c) • (⟨z, hz⟩ : ↥R') := Subtype.ext rfl
      funext j
      show red (k j) c l ((e (s z)) j) = 0
      rw [hsz, map_smul, Pi.smul_apply, map_smul]
      exact lc_smul_Aql _ _ _ _
  have hequiv : ∀ (x : ↥R'') (hx : π x ∈ R''), jm ⟨π x, hx⟩ = πB (jm x) := by
    intro x hx
    funext j
    have hs : s ⟨π x, hx⟩ = ⟨q (s x), hR'q _ (s x).2⟩ - l • s x := by
      apply Subtype.ext
      simp only [s, hπ, LinearMap.codRestrict_apply, LinearMap.smul_apply, Submodule.subtype_apply,
        LinearMap.sub_apply, Module.End.one_apply, Submodule.coe_sub, Submodule.coe_smul, map_smul]
      rw [smul_sub, smul_comm (l ^ c) l]
    show red (k j) c l ((e (s ⟨π x, hx⟩)) j) =
      Ideal.Quotient.mk _ ((PowerSeries.X : PowerSeries O) - PowerSeries.C l) * red (k j) c l ((e (s x)) j)
    rw [hs, map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, he, map_sub, map_smul, map_mul, smul_Aql,
      map_sub, ← sub_mul]
    rfl
  have hJ := Formalism.KernelCokernelLengths.lemma_D_joint_form O R π R' R'' _ πB jm hle hmap hfin hker hequiv
  have hT := Formalism.KernelCokernelLengths.torsion_kernel_sum_length O l hl0 m' c k
  have := torsionFree_sat l hlm R'
  have : Module.Free O (R ⧸ R'') := Module.free_of_finite_type_torsion_free'
  let qb : Module.End O (R ⧸ R'') := R''.mapQ R'' q (fun z hz => hq'' z hz)
  have hpow : ∀ (N : ℕ) (z : R), (qb ^ N) (R''.mkQ z) = R''.mkQ ((q ^ N) z) := by
    intro N
    induction N with
    | zero => intro z; rfl
    | succ N ih => intro z; rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]; rfl
  have hqb : IsNilpotent qb := by
    obtain ⟨N, hN⟩ := hq
    refine ⟨N, ?_⟩
    apply Submodule.linearMap_qext
    ext z
    simp only [LinearMap.comp_apply, hpow, hN, LinearMap.zero_apply, map_zero]
  have hrange : (LinearMap.range π).map R''.mkQ =
      LinearMap.range (qb - l • (1 : Module.End O (R ⧸ R''))) := by
    ext w
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨R''.mkQ z, by simp [qb, hπ]⟩
    · rintro ⟨w', rfl⟩
      induction w' using Submodule.Quotient.induction_on with | H z => ?_
      exact ⟨π z, ⟨z, rfl⟩, by simp [qb, hπ]⟩
  have hL := Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.length_pi_zero_bound O (R ⧸ R'') l hl0 qb hqb
  have hlen2 : Module.length O (R ⧸ (R'' ⊔ LinearMap.range π)) =
      (finrank O (R ⧸ R'') : ℕ∞) * Module.length O (O ⧸ Ideal.span {l}) := by
    rw [← (Submodule.quotientQuotientEquivQuotientSup R'' (LinearMap.range π)).length_eq, hrange, hL]
  calc _ ≤ _ := hJ
    _ ≤ _ := add_le_add (le_of_eq hlen2) hT
    _ ≤ _ := by
      rw [← add_mul]
      gcongr
      push_cast
      rw [mul_comm (m' : ℕ∞)]
      gcongr

end Main

end Formalism.MainNotions.RamifiedCoefficientChains.S9.DCount
