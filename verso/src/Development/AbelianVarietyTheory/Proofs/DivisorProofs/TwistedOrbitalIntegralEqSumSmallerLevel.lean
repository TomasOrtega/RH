import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgEqOfLeRightStabiliserStatement
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCountFib
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section
namespace GlobalTheory.BCT.OrbLev
open Formalism.MainNotions.Gaps.CC.Fib MulAction Function

variable {G : Type} [Group G]

/- English proof (translation)
Establish `h : t * δ = δ * θ t` using `ht`. Establish `h2 : t⁻¹ * δ * θ t = δ` using `by rw [mul_assoc, ← h]; group`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem twCent_left (θ : G →* G) (δ : G) {t : G} (ht : t ∈ twCent θ δ) (y : G) :
    (t * y)⁻¹ * δ * θ (t * y) = y⁻¹ * δ * θ y := by
  have h : t * δ = δ * θ t := ht
  have h2 : t⁻¹ * δ * θ t = δ := by rw [mul_assoc, ← h]; group
  calc (t * y)⁻¹ * δ * θ (t * y) = y⁻¹ * (t⁻¹ * δ * θ t) * θ y := by rw [map_mul]; group
    _ = y⁻¹ * δ * θ y := by rw [h2]

/- English proof (translation)
Use extensionality with `w`. Simplify using `only [Subgroup.mem_map, mem_Gam, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨γ⁻¹ * w * γ, ⟨Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hγ) h1) hγ, ?_⟩, by group⟩` and prove the remaining obligations.

Use `U.mul_mem (U.mul_mem hu h2) (U.inv_mem hu)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use `group`. Introduce and unpack `⟨v, ⟨h1, h2⟩, rfl⟩`. Use `⟨Γ.mul_mem (Γ.mul_mem hγ h1) (Γ.inv_mem hγ), ?_⟩` and prove the remaining obligations.

Use `U.mul_mem (U.mul_mem (U.inv_mem hu) h2) hu` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use `group`.
-/
theorem Gam_mul (Γ U : Subgroup G) {γ z u : G} (hγ : γ ∈ Γ) (hu : u ∈ U) :
    Gam Γ U (γ * z * u) = (Gam Γ U z).map (MulAut.conj γ).toMonoidHom := by
  ext w
  simp only [Subgroup.mem_map, mem_Gam, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨γ⁻¹ * w * γ, ⟨Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hγ) h1) hγ, ?_⟩, by group⟩
    have := U.mul_mem (U.mul_mem hu h2) (U.inv_mem hu)
    convert this using 1; group
  · rintro ⟨v, ⟨h1, h2⟩, rfl⟩
    refine ⟨Γ.mul_mem (Γ.mul_mem hγ h1) (Γ.inv_mem hγ), ?_⟩
    have := U.mul_mem (U.mul_mem (U.inv_mem hu) h2) hu
    convert this using 1; group

/- English proof (translation)
Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce `hw`. Set `s` to `(stabEquiv hUK x k).symm ⟨w, hw⟩`. Conclude with `⟨s.1, s.2, rfl⟩`.

Introduce and unpack `⟨a, ha, rfl⟩`. Use `(stabEquiv hUK x k ⟨a, ha⟩).2` as an intermediate fact. Simplify using `using this`.
-/
theorem Gam_eq_stab {Γ K U : Subgroup G} (hUK : U ≤ K) (x : G) (k : K) :
    Gam Γ U (x * k) = (stabilizer (Gam Γ K x) (k : K ⧸ U.subgroupOf K)).map (Gam Γ K x).subtype := by
  ext w
  constructor
  · intro hw
    let s := (stabEquiv hUK x k).symm ⟨w, hw⟩
    exact ⟨s.1, s.2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    have := (stabEquiv hUK x k ⟨a, ha⟩).2
    simpa using this

variable [TopologicalSpace G] [IsTopologicalGroup G]

/- English proof (translation)
Take `⟨h1, h2⟩` from `ht`. Set `h : G ≃ₜ G` to `(Homeomorph.mulRight γ⁻¹).trans (Homeomorph.mulLeft γ)`. Establish `hf : ⇑h = ⇑(MulAut.conj γ).toMonoidHom`. Use function extensionality and compare the values at `z`. Simplify using `[h, MulAut.conj_apply, mul_assoc]`.

Use `⟨by simpa [MulAut.conj_apply] using T.mul_mem (T.mul_mem hγ h1) (T.inv_mem hγ), ?_⟩` and prove the remaining obligations. Rewrite using `[← MonoidHom.map_zpowers, Subgroup.coe_map, ← hf, ← h.image_closure]`. Conclude with `h2.image h.continuous`.
-/
theorem conj_mem_cpt (T : Subgroup G) {γ : G} (hγ : γ ∈ T) {t : G}
    (ht : t ∈ {t | t ∈ T ∧ IsCompact (closure (Subgroup.zpowers t : Set G))}) :
    (MulAut.conj γ).toMonoidHom t ∈ {t | t ∈ T ∧ IsCompact (closure (Subgroup.zpowers t : Set G))} := by
  obtain ⟨h1, h2⟩ := ht
  let h : G ≃ₜ G := (Homeomorph.mulRight γ⁻¹).trans (Homeomorph.mulLeft γ)
  have hf : ⇑h = ⇑(MulAut.conj γ).toMonoidHom := by
    funext z; simp [h, MulAut.conj_apply, mul_assoc]
  refine ⟨by simpa [MulAut.conj_apply] using T.mul_mem (T.mul_mem hγ h1) (T.inv_mem hγ), ?_⟩
  rw [← MonoidHom.map_zpowers, Subgroup.coe_map, ← hf, ← h.image_closure]
  exact h2.image h.continuous

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[cptPart, MonoidHom.map_closure]`. Apply `Subgroup.closure_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨t, ht, rfl⟩`. Conclude with `conj_mem_cpt T hγ ht`.

Rewrite using `[cptPart, Subgroup.closure_le]`. Introduce `t ht`. Use `⟨(MulAut.conj γ⁻¹).toMonoidHom t, Subgroup.subset_closure (conj_mem_cpt T (T.inv_mem hγ) ht), ?_⟩` and prove the remaining obligations. Simplify using `[MulAut.conj_apply, mul_assoc]`.
-/
theorem cptPart_map_conj (T : Subgroup G) {γ : G} (hγ : γ ∈ T) :
    (cptPart T).map (MulAut.conj γ).toMonoidHom = cptPart T := by
  apply le_antisymm
  · rw [cptPart, MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨t, ht, rfl⟩
    exact conj_mem_cpt T hγ ht
  · rw [cptPart, Subgroup.closure_le]
    intro t ht
    refine ⟨(MulAut.conj γ⁻¹).toMonoidHom t, Subgroup.subset_closure (conj_mem_cpt T (T.inv_mem hγ) ht), ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/- English proof (translation)
Use `letI : ∀ i, Fintype (β i) := fun i => Fintype.ofFinite _`. Use `set I := hh.toFinset.image Sigma.fst`. Establish `h1 : support h ⊆ ((I.sigma fun _ => Finset.univ : Finset (Σ i, β i)) : Set _)`. Introduce `p hp`. Simplify using `only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_univ, and_true, I, Finset.mem_image]`.

Conclude with `⟨p, hh.mem_toFinset.2 hp, rfl⟩`. Establish `h2 : (support fun i => ∑ᶠ b, h ⟨i, b⟩) ⊆ (I : Set ι)`. Introduce `i hi`. Choose the witnesses or unpack the hypotheses as in `⟨b, hb⟩ : ∃ b, h ⟨i, b⟩ ≠ 0 := by`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Conclude with `hi (finsum_eq_zero_of_forall_eq_zero hc)`. Simplify using `only [Finset.mem_coe, I, Finset.mem_image]`. Conclude with `⟨⟨i, b⟩, hh.mem_toFinset.2 hb, rfl⟩`. Rewrite using `[finsum_eq_sum_of_support_subset _ h1, finsum_eq_sum_of_support_subset _ h2, Finset.sum_sigma]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[finsum_eq_sum_of_fintype]`.
-/
theorem finsum_sigma_of_finite {ι : Type} {β : ι → Type} [∀ i, Finite (β i)] (h : (Σ i, β i) → ℂ)
    (hh : (support h).Finite) : ∑ᶠ p, h p = ∑ᶠ i, ∑ᶠ b, h ⟨i, b⟩ := by
  letI : ∀ i, Fintype (β i) := fun i => Fintype.ofFinite _
  set I := hh.toFinset.image Sigma.fst
  have h1 : support h ⊆ ((I.sigma fun _ => Finset.univ : Finset (Σ i, β i)) : Set _) := by
    intro p hp
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_univ, and_true, I, Finset.mem_image]
    exact ⟨p, hh.mem_toFinset.2 hp, rfl⟩
  have h2 : (support fun i => ∑ᶠ b, h ⟨i, b⟩) ⊆ (I : Set ι) := by
    intro i hi
    obtain ⟨b, hb⟩ : ∃ b, h ⟨i, b⟩ ≠ 0 := by
      by_contra hc; push_neg at hc
      exact hi (finsum_eq_zero_of_forall_eq_zero hc)
    simp only [Finset.mem_coe, I, Finset.mem_image]
    exact ⟨⟨i, b⟩, hh.mem_toFinset.2 hb, rfl⟩
  rw [finsum_eq_sum_of_support_subset _ h1, finsum_eq_sum_of_support_subset _ h2, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [finsum_eq_sum_of_fintype]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/- English proof (translation)
Use `letI : Fintype X := Fintype.ofFinite X`. Use `haveI : Finite (orbitRel.Quotient H X) := Quotient.finite _`. Use `letI : Fintype (orbitRel.Quotient H X) := Fintype.ofFinite _`. Rewrite using `[finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, ← Finset.sum_fiberwise Finset.univ (fun y => (Quotient.mk'' y : orbitRel.Quotient H X)) φ]`. Use `Finset.sum_congr rfl fun ω _ => ?_` and prove the remaining obligations.

Establish `hmem : ∀ y, (Quotient.mk'' y : orbitRel.Quotient H X) = ω ↔ y ∈ orbit H ω.out`. Introduce `y`. Use `conv_lhs => rw [← Quotient.out_eq' ω]`. Rewrite using `[Quotient.eq'']`. Conclude with `orbitRel_apply`.

Establish `hc : ∀ y ∈ Finset.univ.filter (fun y => (Quotient.mk'' y : orbitRel.Quotient H X) = ω), φ y = φ ω.out`. Introduce `y hy`. Take `⟨h, rfl⟩` from `(hmem y).1 (Finset.mem_filter.1 hy).2`. Conclude with `hφ h _`. Rewrite using `[Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]`.

Use `congr 2`. Rewrite using `[← Set.ncard_coe_finset]`. Use `congr 1`. Use extensionality with `y`. Simplify using `[hmem]`.
-/
theorem finsum_orbits {H X : Type} [Group H] [MulAction H X] [Finite X] (φ : X → ℂ)
    (hφ : ∀ (h : H) y, φ (h • y) = φ y) :
    ∑ᶠ y, φ y = ∑ᶠ ω : orbitRel.Quotient H X, ((orbit H ω.out).ncard : ℂ) * φ ω.out := by
  letI : Fintype X := Fintype.ofFinite X
  haveI : Finite (orbitRel.Quotient H X) := Quotient.finite _
  letI : Fintype (orbitRel.Quotient H X) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    ← Finset.sum_fiberwise Finset.univ (fun y => (Quotient.mk'' y : orbitRel.Quotient H X)) φ]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have hmem : ∀ y, (Quotient.mk'' y : orbitRel.Quotient H X) = ω ↔ y ∈ orbit H ω.out := by
    intro y
    conv_lhs => rw [← Quotient.out_eq' ω]
    rw [Quotient.eq'']
    exact orbitRel_apply
  have hc : ∀ y ∈ Finset.univ.filter (fun y => (Quotient.mk'' y : orbitRel.Quotient H X) = ω), φ y = φ ω.out := by
    intro y hy
    obtain ⟨h, rfl⟩ := (hmem y).1 (Finset.mem_filter.1 hy).2
    exact hφ h _
  rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]
  congr 2
  rw [← Set.ncard_coe_finset]
  congr 1
  ext y
  simp [hmem]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/- English proof (translation)
Rewrite using `[GlobalTheory.T.avg_eq_of_le_rightStabiliser H u ⊤ (fun k _ => show ∀ x, u (x * k) = u x from fun x => by rw [hu, hu]) (by simp)]`. Simplify using `only [hu, Subgroup.index_top, Nat.cast_one, inv_one, one_mul]`. Conclude with `finsum_eq_single _ (1 : H ⧸ (⊤ : Subgroup H)) (fun x hx => absurd (QuotientGroup.subsingleton_quotient_top.elim x 1) hx)`.
-/
theorem avg_const' {H : Type} [Group H] (u : H → ℂ) (c : ℂ) (hu : ∀ h, u h = c) : avg u = c := by
  rw [GlobalTheory.T.avg_eq_of_le_rightStabiliser H u ⊤ (fun k _ => show ∀ x, u (x * k) = u x from fun x => by rw [hu, hu]) (by simp)]
  simp only [hu, Subgroup.index_top, Nat.cast_one, inv_one, one_mul]
  exact finsum_eq_single _ (1 : H ⧸ (⊤ : Subgroup H)) (fun x hx => absurd (QuotientGroup.subsingleton_quotient_top.elim x 1) hx)

/- English proof (translation)
Introduce `G _ _ _ θ K _hKo hKc _hθK K' hL δ f hf hT hfin`. Take `⟨hK'o, hK'K, hθK'⟩` from `hL`. Use `set T := twCent θ δ with hTdef`. Use `set C := cptPart T with hCdef`. Set `F : G → ℂ` to `fun y => f (y⁻¹ * δ * θ y)`.

Establish `FT : ∀ t ∈ T, ∀ y, F (t * y) = F y` using `fun t ht y => by simp only [F, twCent_left θ δ ht y]`. Establish `FK : ∀ y, ∀ k ∈ K', F (y * k) = F y`. Introduce `y k hk`. Simplify using `only [F]`. Establish `e : (y * k)⁻¹ * δ * θ (y * k) = k⁻¹ * (y⁻¹ * δ * θ y) * θ k` using `by rw [map_mul]; group`.

Rewrite using `[e, (hf.2 _ (hθK' k hk) _).2, (hf.2 _ (K'.inv_mem hk) _).1]`. Set `g : DoubleCoset.Quotient (T : Set G) (K' : Set G) → ℂ` to `fun q => (((T ⊓ K'.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex C : ℕ) : ℂ) * F (Quotient.out q)`. Establish `hsecond : twOrb θ K' δ f = ∑ᶠ q, g q`. Unfold `twOrb`. Use `finsum_congr fun q => ?_` and prove the remaining obligations.

Use `congr 1`. Conclude with `avg_const' _ _ fun k => FK _ k k.2`. Use `⟨?_, hsecond⟩` and prove the remaining obligations. Rewrite using `[hsecond]`. Use `set S := K'.subgroupOf K with hSdef`.

Establish `hn : K'.relIndex K ≠ 0` using `by haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc`. Establish `ho : IsOpen ((K'.subgroupOf K : Subgroup K) : Set K)`. Rewrite using `[Subgroup.coe_subgroupOf]`. Conclude with `hK'o.preimage continuous_subtype_val`. Use `haveI := Subgroup.quotient_finite_of_isOpen _ ho`.

Conclude with `Subgroup.index_ne_zero_of_finite`. Use `haveI : S.FiniteIndex := ⟨hn⟩`. Use `haveI : Finite (K ⧸ S) := Subgroup.finite_quotient_of_finiteIndex`. Establish `avgK : ∀ x : G, avg (fun k : K => F (x * k)) = ((K'.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ y : K ⧸ S, F (x * (Quotient.out y : K))`. Introduce `x`.

Use `GlobalTheory.T.avg_eq_of_le_rightStabiliser K _ S (fun k hk => show ∀ z : K, F (x * ((z * k : K) : G)) = F (x * z) from fun z => ?_) hn` and prove the remaining obligations. Rewrite using `[Subgroup.coe_mul, ← mul_assoc]`. Conclude with `FK _ _ (Subgroup.mem_subgroupOf.1 hk)`. Set `e` to `fib (Γ := T) (K := K) hK'K`. Use `haveI hfo : ∀ c : DoubleCoset.Quotient (T : Set G) (K : Set G), Finite (orbitRel.Quotient (Gam T K (Quotient.out c)) (K ⧸ S)) := fun c => Quotient.finite _`.

Establish `hc : ∀ c : DoubleCoset.Quotient (T : Set G) (K : Set G), (((T ⊓ K.map (MulAut.conj (Quotient.out c)).toMonoidHom).relIndex C : ℕ) : ℂ) * ∑ᶠ y : K ⧸ S, F (Quotient.out c * (Quotient.out y : K)) = ∑ᶠ ω, g (e.symm ⟨c, ω⟩)`. Introduce `c`. Establish `hwK : T ⊓ K.map (MulAut.conj (Quotient.out c)).toMonoidHom = Gam T K (Quotient.out c)` using `(Gam_eq_map T K _).symm`. Rewrite using `[hwK]`. Establish `hφ : ∀ (h : Gam T K (Quotient.out c)) (y : K ⧸ S), F (Quotient.out c * (Quotient.out (h • y) : K)) = F (Quotient.out c * (Quotient.out y : K))`.

Introduce `h y`. Establish `e1 : ((Quotient.out (h • y) : K) : K ⧸ S) = ((toK T K (Quotient.out c) h * Quotient.out y : K) : K ⧸ S)`. Rewrite using `[QuotientGroup.out_eq']`. Use `conv_lhs => rw [← QuotientGroup.out_eq' y]`. Both sides reduce to the same expression.

Establish `hu` using `mk_eq_iff.1 e1.symm`. Establish `e2 : Quotient.out c * ((Quotient.out (h • y) : K) : G) = (h : G) * (Quotient.out c * (Quotient.out y : K)) * (((toK T K (Quotient.out c) h * Quotient.out y : K) : G)⁻¹ * (Quotient.out (h • y) : K))`. Rewrite using `[Subgroup.coe_mul, toK_coe]`. Use `group`. Rewrite using `[e2, FK _ _ hu, FT _ (mem_Gam.1 h.2).1]`.

Rewrite using `[finsum_orbits (fun y : K ⧸ S => F (Quotient.out c * (Quotient.out y : K))) hφ, mul_finsum]`. Use `finsum_congr fun ω => ?_` and prove the remaining obligations. Establish `hq : e.symm ⟨c, ω⟩ = DoubleCoset.mk T K' (Quotient.out c * (Quotient.out ω.out : K))`. Establish `: ω = Quotient.mk'' ((Quotient.out ω.out : K) : K ⧸ S)`. Rewrite using `[QuotientGroup.out_eq', Quotient.out_eq']`.

Establish `h` using `fibRep_symm_mk hK'K Quotient.out (DoubleCoset.out_eq' T K) c (Quotient.out ω.out)`. Rewrite `h` using `[← this]`. Conclude with `h`. Take `⟨γ, hγ, u, hu, hout⟩` from `(DoubleCoset.eq T K' (Quotient.out c * (Quotient.out ω.out : K)) (Quotient.out (e.symm ⟨c, ω⟩))).1 (by rw [DoubleCoset.out_eq', hq])`. Establish `hF : F (Quotient.out (e.symm ⟨c, ω⟩)) = F (Quotient.out c * (Quotient.out ω.out : K))`.

Rewrite using `[hout, FK _ _ hu, FT _ hγ]`. Establish `hCc : C.map (MulAut.conj γ).toMonoidHom = C` using `cptPart_map_conj T hγ`. Establish `h1` using `Subgroup.relIndex_map_map_of_injective (Gam T K' (Quotient.out c * (Quotient.out ω.out : K))) C (f := (MulAut.conj γ).toMonoidHom) (MulAut.conj γ).injective`. Rewrite `h1` using `[hCc]`. Establish `h2 : ((stabilizer (Gam T K (Quotient.out c)) ω.out).map (Gam T K (Quotient.out c)).subtype).subgroupOf (Gam T K (Quotient.out c)) = stabilizer (Gam T K (Quotient.out c)) ω.out` using `Subgroup.comap_map_eq_self_of_injective (Gam T K (Quotient.out c)).subtype_injective _`.

Establish `hHC : Gam T K (Quotient.out c) ≤ C` using `by rw [← hwK]; exact (hT _).1`. Establish `hw : (T ⊓ K'.map (MulAut.conj (Quotient.out (e.symm ⟨c, ω⟩))).toMonoidHom).relIndex C = (orbit (Gam T K (Quotient.out c)) ω.out).ncard * (Gam T K (Quotient.out c)).relIndex C`. Rewrite using `[← Gam_eq_map, hout, Gam_mul T K' hγ hu, h1, Gam_eq_stab hK'K, QuotientGroup.out_eq', ← Subgroup.relIndex_mul_relIndex _ _ _ (Subgroup.map_subtype_le _) hHC, Subgroup.relIndex, h2, index_stabilizer]`. Simplify using `only [g]`. Rewrite using `[hw, hF]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hsupp : (support fun p => g (e.symm p)).Finite`. Use `(hfin.preimage e.symm.injective.injOn).subset ?_` and prove the remaining obligations. Introduce `p hp`.

Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq]`. Introduce `h0`. Conclude with `hp (by simp only [g]; rw [show F (Quotient.out (e.symm p)) = 0 from h0, mul_zero])`. Combine the equalities or inequalities in the displayed calculation. Unfold `twOrb`.

Use `finsum_congr fun c => ?_` and prove the remaining obligations. Rewrite using `[avgK]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = ((K'.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ c, ∑ᶠ ω, g (e.symm ⟨c, ω⟩) := by`. Rewrite using `[← mul_finsum]`.

Use `congr 1`. Conclude with `finsum_congr hc`. Use `_ = ((K'.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q, g q := by`. Rewrite using `[← finsum_sigma_of_finite _ hsupp, finsum_comp_equiv e.symm]`.
-/
theorem twOrb_eq_sum_smallerLevel : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → (∀ k ∈ K, θ k ∈ K) → ∀ K' : Subgroup G, IsLevel θ K K' → ∀ (δ : G) (f : G → ℂ), IsHecke K' f → (∀ x : G, twCent θ δ ⊓ K.map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent θ δ) ∧ (twCent θ δ ⊓ K'.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent θ δ)) ≠ 0) → {q : DoubleCoset.Quotient (twCent θ δ : Set G) (K' : Set G) | f ((Quotient.out q)⁻¹ * δ * θ (Quotient.out q)) ≠ 0}.Finite → twOrb θ K δ f = ((K'.relIndex K : ℕ) : ℂ)⁻¹ * twOrb θ K' δ f ∧ twOrb θ K' δ f = ∑ᶠ q : DoubleCoset.Quotient (twCent θ δ : Set G) (K' : Set G), (((twCent θ δ ⊓ K'.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart (twCent θ δ)) : ℕ) : ℂ) * f ((Quotient.out q)⁻¹ * δ * θ (Quotient.out q)) := by
  intro G _ _ _ θ K _hKo hKc _hθK K' hL δ f hf hT hfin
  obtain ⟨hK'o, hK'K, hθK'⟩ := hL
  set T := twCent θ δ with hTdef
  set C := cptPart T with hCdef
  let F : G → ℂ := fun y => f (y⁻¹ * δ * θ y)
  have FT : ∀ t ∈ T, ∀ y, F (t * y) = F y := fun t ht y => by simp only [F, twCent_left θ δ ht y]
  have FK : ∀ y, ∀ k ∈ K', F (y * k) = F y := by
    intro y k hk
    simp only [F]
    have e : (y * k)⁻¹ * δ * θ (y * k) = k⁻¹ * (y⁻¹ * δ * θ y) * θ k := by rw [map_mul]; group
    rw [e, (hf.2 _ (hθK' k hk) _).2, (hf.2 _ (K'.inv_mem hk) _).1]
  let g : DoubleCoset.Quotient (T : Set G) (K' : Set G) → ℂ := fun q =>
    (((T ⊓ K'.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex C : ℕ) : ℂ) * F (Quotient.out q)
  have hsecond : twOrb θ K' δ f = ∑ᶠ q, g q := by
    unfold twOrb
    refine finsum_congr fun q => ?_
    congr 1
    exact avg_const' _ _ fun k => FK _ k k.2
  refine ⟨?_, hsecond⟩
  rw [hsecond]
  set S := K'.subgroupOf K with hSdef
  have hn : K'.relIndex K ≠ 0 := by
    haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
    have ho : IsOpen ((K'.subgroupOf K : Subgroup K) : Set K) := by
      rw [Subgroup.coe_subgroupOf]; exact hK'o.preimage continuous_subtype_val
    haveI := Subgroup.quotient_finite_of_isOpen _ ho
    exact Subgroup.index_ne_zero_of_finite
  haveI : S.FiniteIndex := ⟨hn⟩
  haveI : Finite (K ⧸ S) := Subgroup.finite_quotient_of_finiteIndex
  have avgK : ∀ x : G, avg (fun k : K => F (x * k)) = ((K'.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ y : K ⧸ S, F (x * (Quotient.out y : K)) := by
    intro x
    refine GlobalTheory.T.avg_eq_of_le_rightStabiliser K _ S (fun k hk => show ∀ z : K, F (x * ((z * k : K) : G)) = F (x * z) from fun z => ?_) hn
    rw [Subgroup.coe_mul, ← mul_assoc]
    exact FK _ _ (Subgroup.mem_subgroupOf.1 hk)
  let e := fib (Γ := T) (K := K) hK'K
  haveI hfo : ∀ c : DoubleCoset.Quotient (T : Set G) (K : Set G), Finite (orbitRel.Quotient (Gam T K (Quotient.out c)) (K ⧸ S)) :=
    fun c => Quotient.finite _
  have hc : ∀ c : DoubleCoset.Quotient (T : Set G) (K : Set G),
      (((T ⊓ K.map (MulAut.conj (Quotient.out c)).toMonoidHom).relIndex C : ℕ) : ℂ) *
        ∑ᶠ y : K ⧸ S, F (Quotient.out c * (Quotient.out y : K)) = ∑ᶠ ω, g (e.symm ⟨c, ω⟩) := by
    intro c
    have hwK : T ⊓ K.map (MulAut.conj (Quotient.out c)).toMonoidHom = Gam T K (Quotient.out c) :=
      (Gam_eq_map T K _).symm
    rw [hwK]
    have hφ : ∀ (h : Gam T K (Quotient.out c)) (y : K ⧸ S),
        F (Quotient.out c * (Quotient.out (h • y) : K)) = F (Quotient.out c * (Quotient.out y : K)) := by
      intro h y
      have e1 : ((Quotient.out (h • y) : K) : K ⧸ S) =
          ((toK T K (Quotient.out c) h * Quotient.out y : K) : K ⧸ S) := by
        rw [QuotientGroup.out_eq']
        conv_lhs => rw [← QuotientGroup.out_eq' y]
        rfl
      have hu := mk_eq_iff.1 e1.symm
      have e2 : Quotient.out c * ((Quotient.out (h • y) : K) : G) = (h : G) * (Quotient.out c * (Quotient.out y : K)) *
          (((toK T K (Quotient.out c) h * Quotient.out y : K) : G)⁻¹ * (Quotient.out (h • y) : K)) := by
        rw [Subgroup.coe_mul, toK_coe]; group
      rw [e2, FK _ _ hu, FT _ (mem_Gam.1 h.2).1]
    rw [finsum_orbits (fun y : K ⧸ S => F (Quotient.out c * (Quotient.out y : K))) hφ, mul_finsum]
    refine finsum_congr fun ω => ?_
    have hq : e.symm ⟨c, ω⟩ = DoubleCoset.mk T K' (Quotient.out c * (Quotient.out ω.out : K)) := by
      have : ω = Quotient.mk'' ((Quotient.out ω.out : K) : K ⧸ S) := by
        rw [QuotientGroup.out_eq', Quotient.out_eq']
      have h := fibRep_symm_mk hK'K Quotient.out (DoubleCoset.out_eq' T K) c (Quotient.out ω.out)
      rw [← this] at h
      exact h
    obtain ⟨γ, hγ, u, hu, hout⟩ := (DoubleCoset.eq T K' (Quotient.out c * (Quotient.out ω.out : K))
      (Quotient.out (e.symm ⟨c, ω⟩))).1 (by rw [DoubleCoset.out_eq', hq])
    have hF : F (Quotient.out (e.symm ⟨c, ω⟩)) = F (Quotient.out c * (Quotient.out ω.out : K)) := by
      rw [hout, FK _ _ hu, FT _ hγ]
    have hCc : C.map (MulAut.conj γ).toMonoidHom = C := cptPart_map_conj T hγ
    have h1 := Subgroup.relIndex_map_map_of_injective (Gam T K' (Quotient.out c * (Quotient.out ω.out : K))) C
      (f := (MulAut.conj γ).toMonoidHom) (MulAut.conj γ).injective
    rw [hCc] at h1
    have h2 : ((stabilizer (Gam T K (Quotient.out c)) ω.out).map (Gam T K (Quotient.out c)).subtype).subgroupOf
        (Gam T K (Quotient.out c)) = stabilizer (Gam T K (Quotient.out c)) ω.out :=
      Subgroup.comap_map_eq_self_of_injective (Gam T K (Quotient.out c)).subtype_injective _
    have hHC : Gam T K (Quotient.out c) ≤ C := by rw [← hwK]; exact (hT _).1
    have hw : (T ⊓ K'.map (MulAut.conj (Quotient.out (e.symm ⟨c, ω⟩))).toMonoidHom).relIndex C =
        (orbit (Gam T K (Quotient.out c)) ω.out).ncard * (Gam T K (Quotient.out c)).relIndex C := by
      rw [← Gam_eq_map, hout, Gam_mul T K' hγ hu, h1, Gam_eq_stab hK'K, QuotientGroup.out_eq',
        ← Subgroup.relIndex_mul_relIndex _ _ _ (Subgroup.map_subtype_le _) hHC, Subgroup.relIndex, h2,
        index_stabilizer]
    simp only [g]
    rw [hw, hF]
    push_cast
    ring
  have hsupp : (support fun p => g (e.symm p)).Finite := by
    refine (hfin.preimage e.symm.injective.injOn).subset ?_
    intro p hp
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    intro h0
    exact hp (by simp only [g]; rw [show F (Quotient.out (e.symm p)) = 0 from h0, mul_zero])
  calc twOrb θ K δ f
      = ∑ᶠ c : DoubleCoset.Quotient (T : Set G) (K : Set G), ((K'.relIndex K : ℕ) : ℂ)⁻¹ *
          ((((T ⊓ K.map (MulAut.conj (Quotient.out c)).toMonoidHom).relIndex C : ℕ) : ℂ) *
            ∑ᶠ y : K ⧸ S, F (Quotient.out c * (Quotient.out y : K))) := by
        unfold twOrb
        refine finsum_congr fun c => ?_
        rw [avgK]; ring
    _ = ((K'.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ c, ∑ᶠ ω, g (e.symm ⟨c, ω⟩) := by
        rw [← mul_finsum]; congr 1; exact finsum_congr hc
    _ = ((K'.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q, g q := by
        rw [← finsum_sigma_of_finite _ hsupp, finsum_comp_equiv e.symm]

end GlobalTheory.BCT.OrbLev
