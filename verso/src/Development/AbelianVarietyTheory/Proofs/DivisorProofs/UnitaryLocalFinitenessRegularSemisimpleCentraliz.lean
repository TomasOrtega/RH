import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfSubsetCpt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommuteOfCommuteSeparableCharpolyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSetTwistedCentralizerEllipticStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOrbitConjCompactModCentralizerUnitaryStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct Pointwise

namespace GlobalTheory.LocFinU

/- English proof (translation)
Introduce `E _ _ _ hE n w y hy`. Take `⟨Ω, hΩ, hsub⟩` from `GlobalTheory.T.exists_compact_set_twisted_centralizer_elliptic E hE n w y hy`. Use `⟨Ω, hΩ, fun t ht => ?_⟩` and prove the remaining obligations. Establish `hc : ∀ a ∈ twCent (MonoidHom.id (UL n w)) y, ∀ b ∈ twCent (MonoidHom.id (UL n w)) y, a * b = b * a`. Introduce `a ha b hb`.

Establish `ha' : a.1.val * y.1.val = y.1.val * a.1.val`. Establish `h0 : a * y = y * a` using `ha`. Use `congrArg (fun g : UL n w => g.1.val) h0` as an intermediate fact. Simplify `this` using `only [Subgroup.coe_mul, Units.val_mul]`. Establish `hb' : b.1.val * y.1.val = y.1.val * b.1.val`.

Establish `h0 : b * y = y * b` using `hb`. Use `congrArg (fun g : UL n w => g.1.val) h0` as an intermediate fact. Simplify `this` using `only [Subgroup.coe_mul, Units.val_mul]`. Use `GlobalTheory.T.commute_of_commute_of_charpoly_separable' _ n _ _ _ hy ha' hb'` as an intermediate fact. Conclude with `Subtype.ext (Units.ext this)`.

Use `cptPart_subset_of_comm _ hc ht` as an intermediate fact. Conclude with `hsub t this.1 this.2`.
-/
theorem bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : UL n w), y.1.val.charpoly.Separable → ∃ Ω : Set (UL n w), IsCompact Ω ∧ (cptPart (twCent (MonoidHom.id (UL n w)) y) : Set (UL n w)) ⊆ Ω := by
  intro E _ _ _ hE n w y hy
  obtain ⟨Ω, hΩ, hsub⟩ := GlobalTheory.T.exists_compact_set_twisted_centralizer_elliptic E hE n w y hy
  refine ⟨Ω, hΩ, fun t ht => ?_⟩
  have hc : ∀ a ∈ twCent (MonoidHom.id (UL n w)) y, ∀ b ∈ twCent (MonoidHom.id (UL n w)) y, a * b = b * a := by
    intro a ha b hb
    have ha' : a.1.val * y.1.val =
        y.1.val * a.1.val :=
      by
        have h0 : a * y = y * a := ha
        have := congrArg (fun g : UL n w => g.1.val) h0
        simpa only [Subgroup.coe_mul, Units.val_mul] using this
    have hb' : b.1.val * y.1.val =
        y.1.val * b.1.val :=
      by
        have h0 : b * y = y * b := hb
        have := congrArg (fun g : UL n w => g.1.val) h0
        simpa only [Subgroup.coe_mul, Units.val_mul] using this
    have := GlobalTheory.T.commute_of_commute_of_charpoly_separable' _ n _ _ _ hy ha' hb'
    exact Subtype.ext (Units.ext this)
  have := cptPart_subset_of_comm _ hc ht
  exact hsub t this.1 this.2

end GlobalTheory.LocFinU

namespace GlobalTheory.LocFinU

/- English proof (translation)
Use extensionality with `g`. Simplify using `[Subgroup.coe_map, MulAut.conj_apply]`.
-/
theorem conj_map_eq {G : Type} [Group G] (x : G) (K : Subgroup G) :
    (K.map (MulAut.conj x).toMonoidHom : Set G) = (fun k => x * k * x⁻¹) '' (K : Set G) := by
  ext g
  simp [Subgroup.coe_map, MulAut.conj_apply]

/- English proof (translation)
Introduce `E _ _ _ hE n w y hy K' hK'`. Take `⟨hK'o, -, -⟩` from `hK'`. Take `⟨Ω, hΩ, hsub⟩` from `bound E hE n w y hy`. Use `⟨fun x => ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `t ht`.

Take `⟨htT, htK⟩` from `Subgroup.mem_inf.1 ht`. Apply `Subgroup.subset_closure` to reduce the goal to its premises. Use `⟨htT, ?_⟩` and prove the remaining obligations. Establish `hc : IsCompact ((KL n w).map (MulAut.conj x).toMonoidHom : Set (UL n w))`. Rewrite using `[conj_map_eq]`.

Conclude with `(isCompact_KL n w).image ((continuous_const.mul continuous_id).mul continuous_const)`. Use `hc.of_isClosed_subset isClosed_closure ?_` and prove the remaining obligations. Conclude with `closure_minimal (Subgroup.zpowers_le.2 htK) hc.isClosed`. Establish `hP : cptPart (twCent (MonoidHom.id _) y) ≤ twCent (MonoidHom.id _) y` using `(Subgroup.closure_le _).2 (fun t ht => ht.1)`. Establish `hU : IsOpen ((K'.map (MulAut.conj x).toMonoidHom : Subgroup _) : Set (UL n w))`.

Rewrite using `[conj_map_eq]`. Conclude with `((Homeomorph.mulLeft x).trans (Homeomorph.mulRight x⁻¹)).isOpenMap _ hK'o`. Establish `h` using `relIndex_ne_zero_of_subset_cpt _ _ hU Ω hΩ hsub`. Establish `e : (twCent (MonoidHom.id _) y ⊓ K'.map (MulAut.conj x).toMonoidHom).subgroupOf (cptPart (twCent (MonoidHom.id _) y)) = (K'.map (MulAut.conj x).toMonoidHom).subgroupOf (cptPart (twCent (MonoidHom.id _) y))`. Use extensionality with `z`.

Simplify using `only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]`. Conclude with `⟨fun h => h.2, fun h => ⟨hP z.2, h⟩⟩`. Unfold `Subgroup.relIndex at h ⊢`. Rewrite using `[e]` and apply the resulting hypothesis. Introduce `C hC`.

Take `⟨Ω', hΩ', horb⟩` from `GlobalTheory.T.regular_orbit_conj_compact_mod_centralizer_unitary E hE n w y hy C hC`. Take `⟨s, hs⟩` from `hΩ'.elim_finite_subcover (fun g : Ω' => (g : UL n w) • (K' : Set (UL n w))) (fun g => hK'o.smul _) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, ⟨1, K'.one_mem, mul_one x⟩⟩)`. Use `(s.finite_toSet.image (fun g : Ω' => DoubleCoset.mk (twCent (MonoidHom.id (UL n w)) y) K' (g : UL n w))).subset ?_` and prove the remaining obligations. Introduce `q hq`. Take `⟨t, ht, ω, hω, heq⟩` from `horb _ hq`.

Use `hs hω` as an intermediate fact. Simplify using `only [Set.mem_iUnion] at this`. Take `⟨i, hi, k, hk, hik⟩` from `this`. Use `⟨i, hi, ?_⟩` and prove the remaining obligations. Use `conv_rhs => rw [← Quotient.out_eq q]`.

Use `(DoubleCoset.eq _ _ _ _).2 ⟨t, ht, k, hk, ?_⟩` and prove the remaining obligations. Rewrite using `[heq, ← hik]`. Simplify using `only [smul_eq_mul, mul_assoc]`.
-/
theorem locFin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : UL n w), y.1.val.charpoly.Separable → ∀ K' : Subgroup (UL n w), IsLevel (MonoidHom.id _) (KL n w) K' → (∀ x : UL n w, twCent (MonoidHom.id _) y ⊓ (KL n w).map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent (MonoidHom.id _) y) ∧ (twCent (MonoidHom.id _) y ⊓ K'.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id _) y)) ≠ 0) ∧ ∀ C : Set (UL n w), IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id (UL n w)) y : Set (UL n w)) (K' : Set (UL n w)) | (Quotient.out q)⁻¹ * y * Quotient.out q ∈ C}.Finite := by
  intro E _ _ _ hE n w y hy K' hK'
  obtain ⟨hK'o, -, -⟩ := hK'
  obtain ⟨Ω, hΩ, hsub⟩ := bound E hE n w y hy
  refine ⟨fun x => ⟨?_, ?_⟩, ?_⟩
  · intro t ht
    obtain ⟨htT, htK⟩ := Subgroup.mem_inf.1 ht
    apply Subgroup.subset_closure
    refine ⟨htT, ?_⟩
    have hc : IsCompact ((KL n w).map (MulAut.conj x).toMonoidHom : Set (UL n w)) := by
      rw [conj_map_eq]
      exact (isCompact_KL n w).image ((continuous_const.mul continuous_id).mul continuous_const)
    refine hc.of_isClosed_subset isClosed_closure ?_
    exact closure_minimal (Subgroup.zpowers_le.2 htK) hc.isClosed
  · have hP : cptPart (twCent (MonoidHom.id _) y) ≤ twCent (MonoidHom.id _) y :=
      (Subgroup.closure_le _).2 (fun t ht => ht.1)
    have hU : IsOpen ((K'.map (MulAut.conj x).toMonoidHom : Subgroup _) : Set (UL n w)) := by
      rw [conj_map_eq]
      exact ((Homeomorph.mulLeft x).trans (Homeomorph.mulRight x⁻¹)).isOpenMap _ hK'o
    have h := relIndex_ne_zero_of_subset_cpt _ _ hU Ω hΩ hsub
    have e : (twCent (MonoidHom.id _) y ⊓ K'.map (MulAut.conj x).toMonoidHom).subgroupOf
        (cptPart (twCent (MonoidHom.id _) y)) =
        (K'.map (MulAut.conj x).toMonoidHom).subgroupOf (cptPart (twCent (MonoidHom.id _) y)) := by
      ext z
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨hP z.2, h⟩⟩
    unfold Subgroup.relIndex at h ⊢
    rwa [e]
  · intro C hC
    obtain ⟨Ω', hΩ', horb⟩ := GlobalTheory.T.regular_orbit_conj_compact_mod_centralizer_unitary E hE n w y hy C hC
    obtain ⟨s, hs⟩ := hΩ'.elim_finite_subcover (fun g : Ω' => (g : UL n w) • (K' : Set (UL n w)))
      (fun g => hK'o.smul _) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, ⟨1, K'.one_mem, mul_one x⟩⟩)
    refine (s.finite_toSet.image
      (fun g : Ω' => DoubleCoset.mk (twCent (MonoidHom.id (UL n w)) y) K' (g : UL n w))).subset ?_
    intro q hq
    obtain ⟨t, ht, ω, hω, heq⟩ := horb _ hq
    have := hs hω
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, k, hk, hik⟩ := this
    refine ⟨i, hi, ?_⟩
    conv_rhs => rw [← Quotient.out_eq q]
    refine (DoubleCoset.eq _ _ _ _).2 ⟨t, ht, k, hk, ?_⟩
    rw [heq, ← hik]
    simp only [smul_eq_mul, mul_assoc]

end GlobalTheory.LocFinU
