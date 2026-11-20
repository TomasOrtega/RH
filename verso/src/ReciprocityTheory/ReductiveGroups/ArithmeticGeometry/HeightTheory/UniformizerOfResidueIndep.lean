import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValAlgebraMapEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial

/- English proof (translation)
Take `⟨hw1, f, hf⟩` from `hw`. Take `⟨p, q, hq, rfl⟩` from `IsFractionRing.div_surjective (A := MvPolynomial σ Ω) f`. Establish `hq0 : q ≠ 0` using `nonZeroDivisors.ne_zero hq`. Establish `key : ∀ P : MvPolynomial σ Ω, algebraMap (MvPolynomial σ Ω) (FractionRing (MvPolynomial σ Ω)) P = aeval t (bind₁ g P)`. Introduce `P`.

Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a`. Rewrite using `[bind₁_C_right, aeval_C, ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]`. Consider the case `add P Q hP hQ => simp only [map_add, hP, hQ]`. Consider the case `mul_X P x hP => simp only [map_mul, hP, bind₁_X_right, hg]`.

Establish `hinj` using `IsFractionRing.injective (MvPolynomial σ Ω) (FractionRing (MvPolynomial σ Ω))`. Establish `hp0 : p ≠ 0`. Introduce and unpack `rfl`. Rewrite `hf` using `[map_zero, zero_div, AddValuation.map_zero]`. Simplify using `at hf`.

Establish `hne : ∀ P : MvPolynomial σ Ω, P ≠ 0 → bind₁ g P ≠ 0`. Introduce `P hP h0`. Apply `hP` to reduce the goal to its premises. Apply `hinj` to reduce the goal to its premises. Rewrite using `[key, h0, map_zero, map_zero]`.

Take `⟨c, hc0, hc⟩` from `ValuationResidueLemmas.exists_val_coeff w t ht hind _ (hne p hp0)`. Take `⟨d, hd0, hd⟩` from `ValuationResidueLemmas.exists_val_coeff w t ht hind _ (hne q hq0)`. Rewrite `hc`, `hd` using `[← key]`. Establish `hqa : algebraMap (MvPolynomial σ Ω) (FractionRing (MvPolynomial σ Ω)) q ≠ 0`. Introduce `h0; exact hq0 (hinj (by rw [h0, map_zero]))`.

Establish `hda : algebraMap Ω (FractionRing (MvPolynomial σ Ω)) d ≠ 0` using `(map_ne_zero _).2 hd0`. Use `⟨c / d, ?_⟩` and prove the remaining obligations. Establish `h1 : w (algebraMap (MvPolynomial σ Ω) (FractionRing (MvPolynomial σ Ω)) p) = 1 + w (algebraMap Ω (FractionRing (MvPolynomial σ Ω)) d)`. Rewrite using `[← hf, ← hd, ← AddValuation.map_mul, div_mul_cancel₀ _ hqa]`. Establish `h2 : w (algebraMap Ω (FractionRing (MvPolynomial σ Ω)) c) = w (algebraMap Ω (FractionRing (MvPolynomial σ Ω)) (c / d)) + w (algebraMap Ω (FractionRing (MvPolynomial σ Ω)) d)`.

Rewrite using `[← AddValuation.map_mul, ← map_mul, div_mul_cancel₀ _ hd0]`. Conclude with `ValuationResidueLemmas.wt_cancel (hw1 _ hda) (by rw [← h2, ← hc, h1])`.
-/
theorem uniformizer_of_residue_indep {Ω : Type} [Field Ω] {σ τ : Type}
    (w : AddValuation (FractionRing (MvPolynomial σ Ω)) (WithTop ℤ)) (hw : IsNormDiscrete w)
    (t : τ → FractionRing (MvPolynomial σ Ω)) (ht : ∀ s, t s ∈ vRing w)
    (hind : letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (vRing w) (algebraMap Ω (FractionRing (MvPolynomial σ Ω)))
      AlgebraicIndependent (IsLocalRing.ResidueField
          ((vRing w).comap (algebraMap Ω (FractionRing (MvPolynomial σ Ω)))))
        (fun s => IsLocalRing.residue (vRing w) ⟨t s, ht s⟩))
    (g : σ → MvPolynomial τ Ω)
    (hg : ∀ x, algebraMap (MvPolynomial σ Ω) (FractionRing (MvPolynomial σ Ω)) (X x) =
      aeval t (g x)) :
    ∃ π : Ω, w (algebraMap Ω (FractionRing (MvPolynomial σ Ω)) π) = 1 := by
  classical
  obtain ⟨hw1, f, hf⟩ := hw
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial σ Ω) f
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  have key : ∀ P : MvPolynomial σ Ω,
      algebraMap (MvPolynomial σ Ω) (FractionRing (MvPolynomial σ Ω)) P =
        aeval t (bind₁ g P) := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C a =>
      rw [bind₁_C_right, aeval_C, ← MvPolynomial.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply]
    | add P Q hP hQ => simp only [map_add, hP, hQ]
    | mul_X P x hP => simp only [map_mul, hP, bind₁_X_right, hg]
  have hinj := IsFractionRing.injective (MvPolynomial σ Ω) (FractionRing (MvPolynomial σ Ω))
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div, AddValuation.map_zero] at hf
    simp at hf
  have hne : ∀ P : MvPolynomial σ Ω, P ≠ 0 → bind₁ g P ≠ 0 := by
    intro P hP h0
    apply hP
    apply hinj
    rw [key, h0, map_zero, map_zero]
  obtain ⟨c, hc0, hc⟩ := ValuationResidueLemmas.exists_val_coeff w t ht hind _ (hne p hp0)
  obtain ⟨d, hd0, hd⟩ := ValuationResidueLemmas.exists_val_coeff w t ht hind _ (hne q hq0)
  rw [← key] at hc hd
  have hqa : algebraMap (MvPolynomial σ Ω) (FractionRing (MvPolynomial σ Ω)) q ≠ 0 := by
    intro h0; exact hq0 (hinj (by rw [h0, map_zero]))
  have hda : algebraMap Ω (FractionRing (MvPolynomial σ Ω)) d ≠ 0 :=
    (map_ne_zero _).2 hd0
  refine ⟨c / d, ?_⟩
  have h1 : w (algebraMap (MvPolynomial σ Ω) (FractionRing (MvPolynomial σ Ω)) p) =
      1 + w (algebraMap Ω (FractionRing (MvPolynomial σ Ω)) d) := by
    rw [← hf, ← hd, ← AddValuation.map_mul, div_mul_cancel₀ _ hqa]
  have h2 : w (algebraMap Ω (FractionRing (MvPolynomial σ Ω)) c) =
      w (algebraMap Ω (FractionRing (MvPolynomial σ Ω)) (c / d)) +
        w (algebraMap Ω (FractionRing (MvPolynomial σ Ω)) d) := by
    rw [← AddValuation.map_mul, ← map_mul, div_mul_cancel₀ _ hd0]
  exact ValuationResidueLemmas.wt_cancel (hw1 _ hda) (by rw [← h2, ← hc, h1])

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

set_option maxHeartbeats 800000 in

/- English proof (translation)
Distinguish the cases in `htriv : ∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0`. Conclude with `Or.inl htriv`. Use `right`. Simplify using `only [not_forall] at htriv`. Take `⟨a0, ha0, hva0⟩` from `htriv`.

Establish `hvK : IsTrivOn K (d.Wres c w)`. Introduce `a ha`. Use `show w (algebraMap (Ω c) (OmS (Ω c) d.D d.N) (algebraMap K (Ω c) a)) = 0`. Rewrite using `[← IsScalarTower.algebraMap_apply]`. Conclude with `d.val_algebraMap_eq_zero c p w hw a ha`.

Take `⟨j0, hw0, hint, hx0, hq⟩` from `d.exists_integral_base hd c (d.Wres c w)`. Establish `htr` using `trdeg_residue_le d.D (hd.trdeg c) (d.Wres c w) hvK a0 ha0 hva0`. Use `letI iWV : Algebra (IsLocalRing.ResidueField (vRing (d.Wres c w))) (IsLocalRing.ResidueField (vRing w)) := resAlg (F := Ω c) w`. Use `letI iRW := resAlg (F := K) (d.Wres c w)`. Use `letI iRV : Algebra (IsLocalRing.ResidueField ((vRing (d.Wres c w)).comap (algebraMap K (Ω c)))) (IsLocalRing.ResidueField (vRing w)) := ((algebraMap (IsLocalRing.ResidueField (vRing (d.Wres c w))) (IsLocalRing.ResidueField (vRing w))).comp (algebraMap (IsLocalRing.ResidueField (( …`.

Use `haveI : IsScalarTower (IsLocalRing.ResidueField ((vRing (d.Wres c w)).comap (algebraMap K (Ω c)))) (IsLocalRing.ResidueField (vRing (d.Wres c w))) (IsLocalRing.ResidueField (vRing w)) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Set `t' : TVar d.D d.N → vRing w` to `fun e => ⟨d.sH c (X e), (hw.2 (X e)).1⟩`. Set `ρ : Fin (d.N + 1) → IsLocalRing.ResidueField (vRing (d.Wres c w))` to `fun j => IsLocalRing.residue _ ⟨ratio (Ω := Ω c) (d.w j c) (d.w j0 c), hint j⟩`. Establish `hres : ∀ i, i ≠ 0 → IsLocalRing.residue (vRing w) (t' (i, j0)) = -∑ j ∈ Finset.univ.erase j0, IsLocalRing.residue (vRing w) (t' (i, j)) * algebraMap _ (IsLocalRing.ResidueField (vRing w)) (ρ j)`. Introduce `i hi`.

Establish `hV : t' (i, j0) = -∑ j ∈ Finset.univ.erase j0, t' (i, j) * comapIncl (vRing w) (algebraMap (Ω c) (OmS (Ω c) d.D d.N)) ⟨ratio (Ω` using `Ω c) (d.w j c) (d.w j0 c), hint j⟩ := by`. Apply `Subtype.ext` to reduce the goal to its premises. Use `push_cast`. Conclude with `d.genericHomAt_relation hd c j0 hw0 hq i hi`. Rewrite using `[hV, map_neg, map_sum]`.

Use `congr 1`. Take `⟨e0, he0⟩` from `exists_rename_notMem p hp`. Establish `hcK : ∀ a : K, algebraMap K (OmS (Ω c) d.D d.N) a ∈ vRing w`. Introduce `a`. Distinguish the cases in `ha : a = 0`.

Rewrite using `[ha, map_zero]`. Conclude with `zero_mem _`. Rewrite using `[mem_valuationRing, d.val_algebraMap_eq_zero c p w hw a ha]`. Establish `hoK : ∀ a : K, a ∈ (vRing (d.Wres c w)).comap (algebraMap K (Ω c))`. Introduce `a`.

Use `show algebraMap (Ω c) (OmS (Ω c) d.D d.N) (algebraMap K (Ω c) a) ∈ vRing w`. Rewrite using `[← IsScalarTower.algebraMap_apply]`. Conclude with `hcK a`. Set `φ : K →+* vRing w` to `(algebraMap K (OmS (Ω c) d.D d.N)).codRestrict (vRing w) hcK`. Set `ψ : K →+* IsLocalRing.ResidueField ((vRing (d.Wres c w)).comap (algebraMap K (Ω c)))` to `(IsLocalRing.residue _).comp ((RingHom.id K).codRestrict _ hoK)`.

Establish `hψ : Function.Surjective ψ`. Introduce `r`. Take `⟨x, rfl⟩` from `IsLocalRing.residue_surjective r`. Conclude with `⟨x.1, rfl⟩`. Establish `hc : ∀ a, algebraMap (IsLocalRing.ResidueField ((vRing (d.Wres c w)).comap (algebraMap K (Ω c)))) (IsLocalRing.ResidueField (vRing w)) (ψ a) = IsLocalRing.residue (vRing w) (φ a)`.

Introduce `a`. Use `show IsLocalRing.residue (vRing w) (comapIncl (vRing w) (algebraMap (Ω c) (OmS (Ω c) d.D d.N)) (comapIncl (vRing (d.Wres c w)) (algebraMap K (Ω c)) ⟨a, hoK a⟩)) = _`. Conclude with `congrArg _ (Subtype.ext (IsScalarTower.algebraMap_apply K (Ω c) _ a).symm)`. Establish `hu : AlgebraicIndependent (IsLocalRing.ResidueField ((vRing (d.Wres c w)).comap (algebraMap K (Ω c)))) (fun e : {e // e ≠ e0} => IsLocalRing.residue (vRing w) (t' e.1))`. Apply `algebraicIndependent_residue_of_isUnit (vRing w) φ ψ hψ hc (fun e : {e // e ≠ e0} => t' e.1)` to reduce the goal to its premises.

Introduce `q hq`. Establish `hq0 : q ≠ 0` using `by rintro rfl; exact hq (map_zero _)`. Establish `hnot` using `he0 q hq0`. Establish `hcoe : ((eval₂ φ (fun e : {e // e ≠ e0} => t' e.1) q : vRing w) : OmS (Ω c) d.D d.N) = d.sH c (rename Subtype.val q)`. Establish `e1` using `eval₂_comp_left (vRing w).subtype φ (fun e : {e // e ≠ e0} => t' e.1) q`.

Establish `e2 : (vRing w).subtype.comp φ = algebraMap K (OmS (Ω c) d.D d.N)` using `RingHom.ext fun _ => rfl`. Rewrite `e1` using `[e2]`. Use `e1.trans ?_` and prove the remaining obligations. Use `conv_rhs => rw [MvPolynomial.aeval_unique (d.sH c), aeval_rename, aeval_def]`. Both sides reduce to the same expression.

Establish `h0` using `(hw.2 (rename Subtype.val q)).1`. Establish `h1 : ¬ (0 < w (d.sH c (rename Subtype.val q)))` using `fun h => hnot ((hw.2 _).2.mp h)`. Establish `hv0 : w (d.sH c (rename Subtype.val q)) = 0` using `le_antisymm (not_lt.mp h1) h0`. Establish `he : eval₂ φ (fun e : {e // e ≠ e0} => t' e.1) q = ⟨d.sH c (rename Subtype.val q), h0⟩` using `Subtype.ext hcoe`. Rewrite using `[he]`.

Conclude with `isUnit_of_val_eq_zero' w h0 hv0`. Set `tb : {e : TVar d.D d.N // e.1 = 0 ∨ e.2 ≠ j0} → IsLocalRing.ResidueField (vRing w)` to `fun e => IsLocalRing.residue (vRing w) (t' e.1)`. Establish `hmemG : ∀ (M : Type) [Field M] [Algebra M (IsLocalRing.ResidueField (vRing w))], (∀ j, ∃ m : M, algebraMap M (IsLocalRing.ResidueField (vRing w)) m = algebraMap (IsLocalRing.ResidueField (vRing (d.Wres c w))) _ (ρ j)) → ∀ e : {e // e ≠ e0}, IsLocalRing.residue (vRing w) (t' e.1) …`. Introduce `M _ _ hM e`. Take `⟨⟨i, j⟩, he⟩` from `e`.

Distinguish the cases in `hij : i = 0 ∨ j ≠ j0`. Conclude with `Algebra.subset_adjoin ⟨⟨(i, j), hij⟩, rfl⟩`. Rewrite `hij` using `[not_or, not_not]`. Take `⟨hi, rfl⟩` from `hij`. Use `show IsLocalRing.residue (vRing w) (t' (i, _)) ∈ _`.

Rewrite using `[hres i hi]`. Use `neg_mem (Subalgebra.sum_mem _ fun j hj => Subalgebra.mul_mem _ ?_ ?_)` and prove the remaining obligations. Conclude with `Algebra.subset_adjoin ⟨⟨(i, j), Or.inr (Finset.ne_of_mem_erase hj)⟩, rfl⟩`. Take `⟨m, hm⟩` from `hM j`. Rewrite using `[← hm]`.

Conclude with `Subalgebra.algebraMap_mem _ m`. Establish `hcard : Fintype.card {e : TVar d.D d.N // e ≠ e0} = Fintype.card {e : TVar d.D d.N // e.1 = 0 ∨ e.2 ≠ j0} + (d.D - 1)`. Rewrite using `[card_subtype_ne', card_baseOrOffColumn, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]`. Establish `h3` using `hd.D_ge`. Establish `h4 : d.D + 1 ≤ (d.D + 1) * (d.N + 1)` using `Nat.le_mul_of_pos_right _ (Nat.succ_pos _)`.

Use linear arithmetic over natural numbers and integers. Take `⟨htrW, hindW⟩` from `trdeg_eq_of_card tb _ hu (hmemG _ fun j => ⟨ρ j, rfl⟩) (d.D - 1) htr hcard (fun _ => rfl)`. Set `k1` to `IntermediateField.adjoin (IsLocalRing.ResidueField ((vRing (d.Wres c w)).comap (algebraMap K (Ω c)))) {r | ∃ j, ∃ h : ratio (Ω := Ω c) (d.w j c) (d.w j0 c) ∈ vRing (d.Wres c w), r = IsLocalRing.residue (vRing (d.Wres c w)) ⟨_, h⟩}`. Use `letI ik1 : Algebra k1 (IsLocalRing.ResidueField (vRing w)) := ((algebraMap (IsLocalRing.ResidueField (vRing (d.Wres c w))) (IsLocalRing.ResidueField (vRing w))).comp (algebraMap k1 (IsLocalRing.ResidueField (vRing (d.Wres c w))))).toAlgebra`. Establish `hk1le` using `(trdeg_le_of_injective k1.val Subtype.val_injective).trans htr`.

Take `⟨htrk1, -⟩` from `trdeg_eq_of_card (E := k1) tb _ hu (hmemG k1 fun j => ⟨⟨ρ j, IntermediateField.subset_adjoin _ _ ⟨j, hint j, rfl⟩⟩, rfl⟩) (d.D - 1) hk1le hcard (fun _ => rfl)`. Establish `hRC : d.ResCond c (d.Wres c w) (d.D - 1)` using `⟨htrW, j0, hw0, fun j => hint j, htrk1⟩`. Establish `hz0mem : (∑ j, d.sH c (X (0, j)) * algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω` using `Ω c) (d.w j c) (d.w j0 c))) ∈ vRing w := sum_mem fun j _ => mul_mem (hw.2 (X (0, j))).1 (hint j)`. Establish `hz0V : (⟨_, hz0mem⟩ : vRing w) = ∑ j, t' (0, j) * comapIncl (vRing w) (algebraMap (Ω c) (OmS (Ω c) d.D d.N)) ⟨_, hint j⟩`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `push_cast`. Both sides reduce to the same expression. Establish `hres0 : IsLocalRing.residue (vRing w) ⟨_, hz0mem⟩ = ∑ j, algebraMap (IsLocalRing.ResidueField (vRing (d.Wres c w))) _ (ρ j) * tb ⟨(0, j), Or.inl rfl⟩`. Rewrite using `[hz0V, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, mul_comm]`. Both sides reduce to the same expression. Establish `hli` using `hindW.linearIndependent.comp (fun j : Fin (d.N + 1) => (⟨(0, j), Or.inl rfl⟩ : {e : TVar d.D d.N // e.1 = 0 ∨ e.2 ≠ j0})) (fun a b hab => by simpa using hab)`. Establish `hρ0 : ρ j0 = 1`. Establish `e : (⟨ratio (Ω` using `Ω c) (d.w j0 c) (d.w j0 c), hint j0⟩ : vRing (d.Wres c w)) = 1 := Subtype.ext (scalarRatio_eq hw0 (one_smul _ _).symm)`.

Use `show IsLocalRing.residue _ _ = 1`. Rewrite using `[e, map_one]`. Establish `hne : IsLocalRing.residue (vRing w) ⟨_, hz0mem⟩ ≠ 0`. Introduce `h0`. Use `Fintype.linearIndependent_iff.mp hli ρ (by` as an intermediate fact.

Rewrite using `[← h0, hres0]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def]`. Use the proof step `rfl) j0`. Rewrite `this` using `[hρ0]`.

Conclude with `one_ne_zero this`. Establish `hunit : w (∑ j, d.sH c (X (0, j)) * algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω` using `Ω c) (d.w j c) (d.w j0 c))) = 0 := val_eq_zero_of_isUnit' w hz0mem ((IsLocalRing.residue_ne_zero_iff_isUnit _).mp hne)`. Establish `hNorm : IsNormDiscrete (d.Wres c w)`. Use `⟨fun x hx => hw.1.1 _ ((map_ne_zero _).mpr hx), ?_⟩` and prove the remaining obligations. Set `G : TVar d.D d.N → MvPolynomial {e : TVar d.D d.N // e.1 = 0 ∨ e.2 ≠ j0} (Ω c)` to `fun e => if h : e.1 = 0 ∨ e.2 ≠ j0 then X ⟨e, h⟩ else -∑ j ∈ (Finset.univ.erase j0).attach, X ⟨(e.1, j.1), Or.inr (Finset.ne_of_mem_erase j.2)⟩ * C (ratio (Ω := Ω c) (d.w j.1 c) (d.w j0 c))`.

Establish `hG : ∀ e, d.sH c (X e) = aeval (fun e : {e : TVar d.D d.N // e.1 = 0 ∨ e.2 ≠ j0} => d.sH c (X e.1)) (G e)`. Introduce and unpack `⟨i, j⟩`. Distinguish the cases in `h : i = 0 ∨ j ≠ j0`. Simplify using `only [G, dif_pos h, aeval_X]`. Simplify using `only [G, dif_neg h, map_neg, map_sum, map_mul, aeval_X, aeval_C]`.

Rewrite `h` using `[not_or, not_not]`. Take `⟨hi, hj⟩` from `h`. Substitute `j` using the available equality. Rewrite using `[d.genericHomAt_relation hd c _ hw0 hq i hi]`. Use `congr 1`.

Conclude with `(Finset.sum_attach _ (fun j => d.sH c (X (i, j)) * algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w j0 c)))).symm`. Establish `hg : ∀ x : SVar d.D d.N, algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) (X x) = aeval (fun e : {e : TVar d.D d.N // e.1 = 0 ∨ e.2 ≠ j0} => d.sH c (X e.1)) (Sum.elim (fun _ => G (0, d.jc c)) (fun ik => G (ik.1, (d.jc c).succAbove ik.2)) x)`. Introduce and unpack `(_ | ⟨i, k⟩)`. Rewrite using `[Sum.elim_inl, ← hG]`. Simplify using `[Data.sH, sHom, genericImage_base]`.

Rewrite using `[Sum.elim_inr, ← hG]`. Simplify using `[Data.sH, sHom, genericImage_succAbove]`. Take `⟨π, hπ⟩` from `uniformizer_of_residue_indep w hw.1 (fun e : {e : TVar d.D d.N // e.1 = 0 ∨ e.2 ≠ j0} => d.sH c (X e.1)) (fun e => (hw.2 (X e.1)).1) hindW _ hg`. Conclude with `⟨π, hπ⟩`. Conclude with `⟨⟨hNorm, Or.inr ⟨hvK, hRC⟩⟩, hvK, j0, hw0, fun j => hint j, hunit⟩`.
-/
theorem PlaceTrivialOrPositive (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (p : Ideal (KTp K d.D d.N))
    (hp : p ∈ d.HtOne) (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (hw : w ∈ d.OverP c p) :
    (∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0) ∨
    (d.admitted c (d.Wres c w) ∧ IsTrivOn K (d.Wres c w) ∧
      ∃ j0, d.w j0 c ≠ 0 ∧ (∀ j, 0 ≤ d.Wres c w (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) ∧
        w (∑ j, d.sH c (MvPolynomial.X (0, j)) *
          algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) = 0) := by
  classical
  by_cases htriv : ∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0
  · exact Or.inl htriv
  right
  simp only [not_forall] at htriv
  obtain ⟨a0, ha0, hva0⟩ := htriv
  have hvK : IsTrivOn K (d.Wres c w) := by
    intro a ha
    show w (algebraMap (Ω c) (OmS (Ω c) d.D d.N) (algebraMap K (Ω c) a)) = 0
    rw [← IsScalarTower.algebraMap_apply]
    exact d.val_algebraMap_eq_zero c p w hw a ha
  obtain ⟨j0, hw0, hint, hx0, hq⟩ := d.exists_integral_base hd c (d.Wres c w)
  have htr := trdeg_residue_le d.D (hd.trdeg c) (d.Wres c w) hvK a0 ha0 hva0
  letI iWV : Algebra (IsLocalRing.ResidueField (vRing (d.Wres c w)))
      (IsLocalRing.ResidueField (vRing w)) := resAlg (F := Ω c) w
  letI iRW := resAlg (F := K) (d.Wres c w)
  letI iRV : Algebra (IsLocalRing.ResidueField ((vRing (d.Wres c w)).comap (algebraMap K (Ω c))))
      (IsLocalRing.ResidueField (vRing w)) :=
    ((algebraMap (IsLocalRing.ResidueField (vRing (d.Wres c w))) (IsLocalRing.ResidueField (vRing w))).comp
      (algebraMap (IsLocalRing.ResidueField ((vRing (d.Wres c w)).comap (algebraMap K (Ω c))))
        (IsLocalRing.ResidueField (vRing (d.Wres c w))))).toAlgebra
  haveI : IsScalarTower (IsLocalRing.ResidueField ((vRing (d.Wres c w)).comap (algebraMap K (Ω c))))
      (IsLocalRing.ResidueField (vRing (d.Wres c w))) (IsLocalRing.ResidueField (vRing w)) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let t' : TVar d.D d.N → vRing w := fun e => ⟨d.sH c (X e), (hw.2 (X e)).1⟩
  let ρ : Fin (d.N + 1) → IsLocalRing.ResidueField (vRing (d.Wres c w)) := fun j =>
    IsLocalRing.residue _ ⟨ratio (Ω := Ω c) (d.w j c) (d.w j0 c), hint j⟩
  have hres : ∀ i, i ≠ 0 → IsLocalRing.residue (vRing w) (t' (i, j0)) =
      -∑ j ∈ Finset.univ.erase j0, IsLocalRing.residue (vRing w) (t' (i, j)) *
        algebraMap _ (IsLocalRing.ResidueField (vRing w)) (ρ j) := by
    intro i hi
    have hV : t' (i, j0) = -∑ j ∈ Finset.univ.erase j0, t' (i, j) *
        comapIncl (vRing w) (algebraMap (Ω c) (OmS (Ω c) d.D d.N))
          ⟨ratio (Ω := Ω c) (d.w j c) (d.w j0 c), hint j⟩ := by
      apply Subtype.ext
      push_cast
      exact d.genericHomAt_relation hd c j0 hw0 hq i hi
    rw [hV, map_neg, map_sum]
    congr 1
  obtain ⟨e0, he0⟩ := exists_rename_notMem p hp
  have hcK : ∀ a : K, algebraMap K (OmS (Ω c) d.D d.N) a ∈ vRing w := by
    intro a
    by_cases ha : a = 0
    · rw [ha, map_zero]; exact zero_mem _
    · rw [mem_valuationRing, d.val_algebraMap_eq_zero c p w hw a ha]
  have hoK : ∀ a : K, a ∈ (vRing (d.Wres c w)).comap (algebraMap K (Ω c)) := by
    intro a
    show algebraMap (Ω c) (OmS (Ω c) d.D d.N) (algebraMap K (Ω c) a) ∈ vRing w
    rw [← IsScalarTower.algebraMap_apply]
    exact hcK a
  let φ : K →+* vRing w := (algebraMap K (OmS (Ω c) d.D d.N)).codRestrict (vRing w) hcK
  let ψ : K →+* IsLocalRing.ResidueField ((vRing (d.Wres c w)).comap (algebraMap K (Ω c))) :=
    (IsLocalRing.residue _).comp ((RingHom.id K).codRestrict _ hoK)
  have hψ : Function.Surjective ψ := by
    intro r
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective r
    exact ⟨x.1, rfl⟩
  have hc : ∀ a, algebraMap (IsLocalRing.ResidueField ((vRing (d.Wres c w)).comap (algebraMap K (Ω c))))
      (IsLocalRing.ResidueField (vRing w)) (ψ a) = IsLocalRing.residue (vRing w) (φ a) := by
    intro a
    show IsLocalRing.residue (vRing w) (comapIncl (vRing w) (algebraMap (Ω c) (OmS (Ω c) d.D d.N))
      (comapIncl (vRing (d.Wres c w)) (algebraMap K (Ω c)) ⟨a, hoK a⟩)) = _
    exact congrArg _ (Subtype.ext (IsScalarTower.algebraMap_apply K (Ω c) _ a).symm)
  have hu : AlgebraicIndependent (IsLocalRing.ResidueField ((vRing (d.Wres c w)).comap (algebraMap K (Ω c))))
      (fun e : {e // e ≠ e0} => IsLocalRing.residue (vRing w) (t' e.1)) := by
    apply algebraicIndependent_residue_of_isUnit (vRing w) φ ψ hψ hc (fun e : {e // e ≠ e0} => t' e.1)
    intro q hq
    have hq0 : q ≠ 0 := by rintro rfl; exact hq (map_zero _)
    have hnot := he0 q hq0
    have hcoe : ((eval₂ φ (fun e : {e // e ≠ e0} => t' e.1) q : vRing w) : OmS (Ω c) d.D d.N) =
        d.sH c (rename Subtype.val q) := by
      have e1 := eval₂_comp_left (vRing w).subtype φ (fun e : {e // e ≠ e0} => t' e.1) q
      have e2 : (vRing w).subtype.comp φ = algebraMap K (OmS (Ω c) d.D d.N) := RingHom.ext fun _ => rfl
      rw [e2] at e1
      refine e1.trans ?_
      conv_rhs => rw [MvPolynomial.aeval_unique (d.sH c), aeval_rename, aeval_def]
      rfl
    have h0 := (hw.2 (rename Subtype.val q)).1
    have h1 : ¬ (0 < w (d.sH c (rename Subtype.val q))) := fun h => hnot ((hw.2 _).2.mp h)
    have hv0 : w (d.sH c (rename Subtype.val q)) = 0 := le_antisymm (not_lt.mp h1) h0
    have he : eval₂ φ (fun e : {e // e ≠ e0} => t' e.1) q = ⟨d.sH c (rename Subtype.val q), h0⟩ :=
      Subtype.ext hcoe
    rw [he]
    exact isUnit_of_val_eq_zero' w h0 hv0
  let tb : {e : TVar d.D d.N // e.1 = 0 ∨ e.2 ≠ j0} → IsLocalRing.ResidueField (vRing w) :=
    fun e => IsLocalRing.residue (vRing w) (t' e.1)
  have hmemG : ∀ (M : Type) [Field M] [Algebra M (IsLocalRing.ResidueField (vRing w))],
      (∀ j, ∃ m : M, algebraMap M (IsLocalRing.ResidueField (vRing w)) m =
        algebraMap (IsLocalRing.ResidueField (vRing (d.Wres c w))) _ (ρ j)) →
      ∀ e : {e // e ≠ e0}, IsLocalRing.residue (vRing w) (t' e.1) ∈ Algebra.adjoin M (Set.range tb) := by
    intro M _ _ hM e
    obtain ⟨⟨i, j⟩, he⟩ := e
    by_cases hij : i = 0 ∨ j ≠ j0
    · exact Algebra.subset_adjoin ⟨⟨(i, j), hij⟩, rfl⟩
    · rw [not_or, not_not] at hij
      obtain ⟨hi, rfl⟩ := hij
      show IsLocalRing.residue (vRing w) (t' (i, _)) ∈ _
      rw [hres i hi]
      refine neg_mem (Subalgebra.sum_mem _ fun j hj => Subalgebra.mul_mem _ ?_ ?_)
      · exact Algebra.subset_adjoin ⟨⟨(i, j), Or.inr (Finset.ne_of_mem_erase hj)⟩, rfl⟩
      · obtain ⟨m, hm⟩ := hM j
        rw [← hm]
        exact Subalgebra.algebraMap_mem _ m
  have hcard : Fintype.card {e : TVar d.D d.N // e ≠ e0} =
      Fintype.card {e : TVar d.D d.N // e.1 = 0 ∨ e.2 ≠ j0} + (d.D - 1) := by
    rw [card_subtype_ne', card_baseOrOffColumn, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    have h3 := hd.D_ge
    have h4 : d.D + 1 ≤ (d.D + 1) * (d.N + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    omega
  obtain ⟨htrW, hindW⟩ := trdeg_eq_of_card tb _ hu (hmemG _ fun j => ⟨ρ j, rfl⟩) (d.D - 1) htr hcard (fun _ => rfl)
  let k1 := IntermediateField.adjoin (IsLocalRing.ResidueField ((vRing (d.Wres c w)).comap (algebraMap K (Ω c))))
    {r | ∃ j, ∃ h : ratio (Ω := Ω c) (d.w j c) (d.w j0 c) ∈ vRing (d.Wres c w),
      r = IsLocalRing.residue (vRing (d.Wres c w)) ⟨_, h⟩}
  letI ik1 : Algebra k1 (IsLocalRing.ResidueField (vRing w)) :=
    ((algebraMap (IsLocalRing.ResidueField (vRing (d.Wres c w))) (IsLocalRing.ResidueField (vRing w))).comp
      (algebraMap k1 (IsLocalRing.ResidueField (vRing (d.Wres c w))))).toAlgebra
  have hk1le := (trdeg_le_of_injective k1.val Subtype.val_injective).trans htr
  obtain ⟨htrk1, -⟩ := trdeg_eq_of_card (E := k1) tb _ hu
    (hmemG k1 fun j => ⟨⟨ρ j, IntermediateField.subset_adjoin _ _ ⟨j, hint j, rfl⟩⟩, rfl⟩) (d.D - 1) hk1le hcard (fun _ => rfl)
  have hRC : d.ResCond c (d.Wres c w) (d.D - 1) := ⟨htrW, j0, hw0, fun j => hint j, htrk1⟩

  have hz0mem : (∑ j, d.sH c (X (0, j)) * algebraMap (Ω c) (OmS (Ω c) d.D d.N)
      (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) ∈ vRing w :=
    sum_mem fun j _ => mul_mem (hw.2 (X (0, j))).1 (hint j)
  have hz0V : (⟨_, hz0mem⟩ : vRing w) = ∑ j, t' (0, j) *
      comapIncl (vRing w) (algebraMap (Ω c) (OmS (Ω c) d.D d.N)) ⟨_, hint j⟩ := by
    apply Subtype.ext
    push_cast
    rfl
  have hres0 : IsLocalRing.residue (vRing w) ⟨_, hz0mem⟩ =
      ∑ j, algebraMap (IsLocalRing.ResidueField (vRing (d.Wres c w))) _ (ρ j) *
        tb ⟨(0, j), Or.inl rfl⟩ := by
    rw [hz0V, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, mul_comm]
    rfl
  have hli := hindW.linearIndependent.comp
    (fun j : Fin (d.N + 1) => (⟨(0, j), Or.inl rfl⟩ : {e : TVar d.D d.N // e.1 = 0 ∨ e.2 ≠ j0}))
    (fun a b hab => by simpa using hab)
  have hρ0 : ρ j0 = 1 := by
    have e : (⟨ratio (Ω := Ω c) (d.w j0 c) (d.w j0 c), hint j0⟩ : vRing (d.Wres c w)) = 1 :=
      Subtype.ext (scalarRatio_eq hw0 (one_smul _ _).symm)
    show IsLocalRing.residue _ _ = 1
    rw [e, map_one]
  have hne : IsLocalRing.residue (vRing w) ⟨_, hz0mem⟩ ≠ 0 := by
    intro h0
    have := Fintype.linearIndependent_iff.mp hli ρ (by
      rw [← h0, hres0]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def]
      rfl) j0
    rw [hρ0] at this
    exact one_ne_zero this
  have hunit : w (∑ j, d.sH c (X (0, j)) * algebraMap (Ω c) (OmS (Ω c) d.D d.N)
      (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) = 0 :=
    val_eq_zero_of_isUnit' w hz0mem ((IsLocalRing.residue_ne_zero_iff_isUnit _).mp hne)

  have hNorm : IsNormDiscrete (d.Wres c w) := by
    refine ⟨fun x hx => hw.1.1 _ ((map_ne_zero _).mpr hx), ?_⟩
    let G : TVar d.D d.N → MvPolynomial {e : TVar d.D d.N // e.1 = 0 ∨ e.2 ≠ j0} (Ω c) := fun e =>
      if h : e.1 = 0 ∨ e.2 ≠ j0 then X ⟨e, h⟩ else
        -∑ j ∈ (Finset.univ.erase j0).attach,
          X ⟨(e.1, j.1), Or.inr (Finset.ne_of_mem_erase j.2)⟩ *
            C (ratio (Ω := Ω c) (d.w j.1 c) (d.w j0 c))
    have hG : ∀ e, d.sH c (X e) =
        aeval (fun e : {e : TVar d.D d.N // e.1 = 0 ∨ e.2 ≠ j0} => d.sH c (X e.1)) (G e) := by
      rintro ⟨i, j⟩
      by_cases h : i = 0 ∨ j ≠ j0
      · simp only [G, dif_pos h, aeval_X]
      · simp only [G, dif_neg h, map_neg, map_sum, map_mul, aeval_X, aeval_C]
        rw [not_or, not_not] at h
        obtain ⟨hi, hj⟩ := h
        subst j
        rw [d.genericHomAt_relation hd c _ hw0 hq i hi]
        congr 1
        exact (Finset.sum_attach _ (fun j => d.sH c (X (i, j)) *
          algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w j0 c)))).symm
    have hg : ∀ x : SVar d.D d.N,
        algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) (X x) =
          aeval (fun e : {e : TVar d.D d.N // e.1 = 0 ∨ e.2 ≠ j0} => d.sH c (X e.1))
            (Sum.elim (fun _ => G (0, d.jc c)) (fun ik => G (ik.1, (d.jc c).succAbove ik.2)) x) := by
      rintro (_ | ⟨i, k⟩)
      · rw [Sum.elim_inl, ← hG]
        simp [Data.sH, sHom, genericImage_base]
      · rw [Sum.elim_inr, ← hG]
        simp [Data.sH, sHom, genericImage_succAbove]
    obtain ⟨π, hπ⟩ := uniformizer_of_residue_indep w hw.1
      (fun e : {e : TVar d.D d.N // e.1 = 0 ∨ e.2 ≠ j0} => d.sH c (X e.1))
      (fun e => (hw.2 (X e.1)).1) hindW _ hg
    exact ⟨π, hπ⟩
  exact ⟨⟨hNorm, Or.inr ⟨hvK, hRC⟩⟩, hvK, j0, hw0, fun j => hint j, hunit⟩

end Data

end ReciprocityTheory.ChartRestriction.G.T0
