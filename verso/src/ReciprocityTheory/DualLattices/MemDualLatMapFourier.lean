import ReciprocityTheory.DualLattices.ValuationFourierLeOne
import ReciprocityTheory.DualLattices.CharTableIsUnit
import ReciprocityTheory.DualLattices.TransposeMulSelf

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

def tableM (e : H ≃ AddChar N C) (σ : H ≃ N) : Matrix N N C :=
  Matrix.of fun x j => e (σ.symm j) x

/- English proof (translation)
Unfold `tableM`. Conclude with `charTable_isUnit (σ.symm.trans e)`.
-/
theorem tableM_isUnit (e : H ≃ AddChar N C) (σ : H ≃ N) : IsUnit (tableM e σ).det := by
  unfold tableM
  exact charTable_isUnit (σ.symm.trans e)

/- English proof (translation)
Simplify using `only [fourier_apply', Matrix.mul_apply, Matrix.transpose_apply, tableM, Matrix.of_apply, Equiv.symm_apply_apply]`. Conclude with `Finset.sum_congr rfl fun a _ => mul_comm _ _`.
-/
private theorem fourier_column_eq (e : H ≃ AddChar N C) (σ : H ≃ N) (Dm : Matrix N N C) (h : H)
    (j : N) :
    fourier (R := R) (fun h a => e h a) (fun x => Dm x j) h =
      ((tableM e σ)ᵀ * Dm) (σ h) j := by
  simp only [fourier_apply', Matrix.mul_apply, Matrix.transpose_apply, tableM,
    Matrix.of_apply, Equiv.symm_apply_apply]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

/- English proof (translation)
Rewrite using `[Submodule.map_span]`. Use `congr 1`. Use extensionality with `f`. Simplify using `only [Set.mem_image, Set.mem_range]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨_, ⟨j, rfl⟩, rfl⟩`. Use `⟨σ.symm j, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `h`. Simplify using `only [Matrix.submatrix_apply, Equiv.apply_symm_apply]`. Conclude with `(fourier_column_eq e σ Dm h j).symm`.

Introduce and unpack `⟨k, rfl⟩`. Use `⟨_, ⟨σ k, rfl⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `h`. Simplify using `only [Matrix.submatrix_apply]`. Conclude with `fourier_column_eq e σ Dm h (σ k)`.
-/
theorem map_fourier_spanCols (e : H ≃ AddChar N C) (σ : H ≃ N) (Dm : Matrix N N C) :
    (Submodule.span R (Set.range fun j x => Dm x j)).map (fourier (R := R) fun h a => e h a) =
      Submodule.span R (Set.range fun k h => ((tableM e σ)ᵀ * Dm).submatrix σ σ h k) := by
  rw [Submodule.map_span]
  congr 1
  ext f
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
    refine ⟨σ.symm j, ?_⟩
    funext h
    simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply]
    exact (fourier_column_eq e σ Dm h j).symm
  · rintro ⟨k, rfl⟩
    refine ⟨_, ⟨σ k, rfl⟩, ?_⟩
    funext h
    simp only [Matrix.submatrix_apply]
    exact fourier_column_eq e σ Dm h (σ k)

/- English proof (translation)
Introduce `h0`. Establish `h1 : ψ a * ψ (-a) = 1`. Rewrite using `[← AddChar.map_add_eq_mul]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[h0, zero_mul]`.

Conclude with `zero_ne_one h1`.
-/
private theorem addChar_apply_ne_zero_dual_lattices (ψ : AddChar N C) (a : N) : ψ a ≠ 0 := by
  intro h0
  have h1 : ψ a * ψ (-a) = 1 := by
    rw [← AddChar.map_add_eq_mul]
    simp
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

/- English proof (translation)
Establish `h0` using `he 0 0`. Rewrite `h0` using `[add_zero]`. Use extensionality with `a`. Establish `ha : e 0 a = e 0 a * e 0 a`. Use `congrArg (fun ψ : AddChar N C => ψ a) h0` as an intermediate fact.

Simplify `this` using `only [AddChar.mul_apply]`. Rewrite using `[AddChar.one_apply]`. Conclude with `mul_left_cancel₀ (addChar_apply_ne_zero_dual_lattices (e 0) a) (by rw [mul_one]; exact ha.symm)`.
-/
theorem e_zero (e : H ≃ AddChar N C) (he : ∀ h h', e (h + h') = e h * e h') : e 0 = 1 := by
  have h0 := he 0 0
  rw [add_zero] at h0
  ext a
  have ha : e 0 a = e 0 a * e 0 a := by
    have := congrArg (fun ψ : AddChar N C => ψ a) h0
    simpa only [AddChar.mul_apply] using this
  rw [AddChar.one_apply]
  exact mul_left_cancel₀ (addChar_apply_ne_zero_dual_lattices (e 0) a) (by rw [mul_one]; exact ha.symm)

/- English proof (translation)
Establish `h1` using `he (-h) h`. Establish `hz : -h + h = 0` using `by simp`. Rewrite `h1` using `[hz, e_zero e he]`. Establish `h2` using `congrArg (fun ψ : AddChar N C => ψ a) h1`. Simplify using `only [AddChar.mul_apply, AddChar.one_apply] at h2`.

Establish `h3 : e h (-a) * e h a = 1`. Rewrite using `[← AddChar.map_add_eq_mul]`. Simplify using the standard rewrite rules. Conclude with `mul_right_cancel₀ (addChar_apply_ne_zero_dual_lattices (e h) a) (h2.symm.trans h3.symm)`.
-/
theorem e_neg_apply (e : H ≃ AddChar N C) (he : ∀ h h', e (h + h') = e h * e h') (h : H) (a : N) :
    e (-h) a = e h (-a) := by
  have h1 := he (-h) h
  have hz : -h + h = 0 := by simp
  rw [hz, e_zero e he] at h1
  have h2 := congrArg (fun ψ : AddChar N C => ψ a) h1
  simp only [AddChar.mul_apply, AddChar.one_apply] at h2
  have h3 : e h (-a) * e h a = 1 := by
    rw [← AddChar.map_add_eq_mul]
    simp
  exact mul_right_cancel₀ (addChar_apply_ne_zero_dual_lattices (e h) a) (h2.symm.trans h3.symm)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
private theorem mem_dualLat_iff_pairing_integral {X : Type} [Fintype X] {M : Submodule R (X → C)} {u : X → C} :
    u ∈ dualLat M ↔ ∀ f ∈ M, ∃ r : R, algebraMap R C r = ∑ a, u a * f a := Iff.rfl

/- English proof (translation)
Rewrite using `[Submodule.mem_map]`. Use `⟨fun a => u (-a), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_dualLat_iff_pairing_integral]`. Introduce `f hf`. Take `⟨r, hr⟩` from `(mem_dualLat_iff_pairing_integral.1 hu) (fun x => f (-x)) (AA.antipode f hf)`.

Use `⟨r, hr.trans ?_⟩` and prove the remaining obligations. Conclude with `Fintype.sum_equiv (Equiv.neg N) _ _ (fun a => by simp)`. Use function extensionality and compare the values at `x`. Simplify using `only [fourier_apply']`. Conclude with `Fintype.sum_equiv (Equiv.neg N) _ _ (fun a => by simp [e_neg_apply e he])`.
-/
theorem antipode_fourier (e : H ≃ AddChar N C) (he : ∀ h h', e (h + h') = e h * e h')
    (AA : HopfOrder (C := C) R N) (u : N → C) (hu : u ∈ dualLat AA.carrier) :
    (fun x => fourier (R := R) (fun h a => e h a) u (-x)) ∈
      (dualLat AA.carrier).map (fourier (R := R) fun h a => e h a) := by
  rw [Submodule.mem_map]
  refine ⟨fun a => u (-a), ?_, ?_⟩
  · rw [mem_dualLat_iff_pairing_integral]
    intro f hf
    obtain ⟨r, hr⟩ := (mem_dualLat_iff_pairing_integral.1 hu) (fun x => f (-x)) (AA.antipode f hf)
    refine ⟨r, hr.trans ?_⟩
    exact Fintype.sum_equiv (Equiv.neg N) _ _ (fun a => by simp)
  · funext x
    simp only [fourier_apply']
    exact Fintype.sum_equiv (Equiv.neg N) _ _ (fun a => by simp [e_neg_apply e he])

/- English proof (translation)
Establish `hBB : B * B⁻¹ = 1` using `Matrix.mul_nonsing_inv B hB`. Use `symm`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [fourier_apply', Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `_ = ∑ x, ∑ i, B a i * B⁻¹ i x * e h x := Finset.sum_comm`. Use `_ = ∑ x, (B * B⁻¹) a x * e h x := by`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.mul_apply, Finset.sum_mul]`. Use `_ = e h a := by simp [hBB, Matrix.one_apply]`.
-/
theorem char_expand (e : H ≃ AddChar N C) (B : Matrix N N C) (hB : IsUnit B.det) (h : H) (a : N) :
    e h a = ∑ i, fourier (R := R) (fun h a => e h a) (fun x => B⁻¹ i x) h * B a i := by
  have hBB : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hB
  symm
  calc ∑ i, fourier (R := R) (fun h a => e h a) (fun x => B⁻¹ i x) h * B a i
      = ∑ i, ∑ x, B a i * B⁻¹ i x * e h x := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [fourier_apply', Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
    _ = ∑ x, ∑ i, B a i * B⁻¹ i x * e h x := Finset.sum_comm
    _ = ∑ x, (B * B⁻¹) a x * e h x := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Matrix.mul_apply, Finset.sum_mul]
    _ = e h a := by simp [hBB, Matrix.one_apply]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
private theorem mem_intFun_iff_pairing {X : Type} {f : X → C} :
    f ∈ intFun (C := C) R X ↔ ∀ x, ∃ r : R, algebraMap R C r = f x := Iff.rfl

/- English proof (translation)
Establish `hg : ∀ i, (fun a => u a * B a i) ∈ dualLat AA.carrier`. Introduce `i`. Rewrite using `[mem_dualLat_iff_pairing_integral]`. Introduce `f hf`. Establish `hcol : (fun x => B x i) ∈ AA.carrier`.

Rewrite using `[hAA]`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Take `⟨r, hr⟩` from `(mem_dualLat_iff_pairing_integral.1 hu) _ (AA.mul_mem _ _ hcol hf)`. Use `⟨r, hr.trans (Finset.sum_congr rfl fun a _ => ?_)⟩` and prove the remaining obligations. Simplify using `only [Pi.mul_apply]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hk : ∀ i, (fun x => B⁻¹ i x) ∈ dualLat AA.carrier`. Introduce `i`. Rewrite using `[hAA, mem_dualLat_spanCols_iff, mem_intFun_iff_pairing]`. Introduce `j`.

Use `show ∃ r : R, algebraMap R C r = (B⁻¹ * B) i j`. Rewrite using `[Matrix.nonsing_inv_mul B hB, Matrix.one_apply]`. Distinguish the cases in `hij : i = j`. Conclude with `⟨1, by simp [hij]⟩`. Conclude with `⟨0, by simp [hij]⟩`.

Establish `hsplit : addPull R H (fourier (R` using `R) (fun h a => e h a) u) = ∑ i, fun p : H × H => fourier (R := R) (fun h a => e h a) (fun a => u a * B a i) p.1 * fourier (R := R) (fun h a => e h a) (fun x => B⁻¹ i x) p.2 := by`. Use function extensionality and compare the values at `p`. Rewrite using `[Finset.sum_apply]`. Simplify using `only [addPull, LinearMap.funLeft_apply]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[fourier_apply' (R := R) (fun h a => e h a) u (p.1 + p.2)]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `show u a * e (p.1 + p.2) a = _`. Rewrite using `[he, AddChar.mul_apply, char_expand (R := R) e B hB p.2 a]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = ∑ a, ∑ i, u a * B a i * e p.1 a * fourier (R := R) (fun h a => e h a) (fun x => B⁻¹ i x) p.2 := by`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Use `_ = ∑ i, ∑ a, u a * B a i * e p.1 a * fourier (R := R) (fun h a => e h a) (fun x => B⁻¹ i x) p.2 := Finset.sum_comm`. Use `_ = ∑ i, fourier (R := R) (fun h a => e h a) (fun a => u a * B a i) p.1 * fourier (R := R) (fun h a => e h a) (fun x => B⁻¹ i x) p.2 := by`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[fourier_apply' (R := R) (fun h a => e h a) (fun a => u a * B a i) p.1, Finset.sum_mul]`. Rewrite using `[hsplit]`.

Use `Submodule.sum_mem _ fun i _ => Submodule.subset_span ?_` and prove the remaining obligations. Conclude with `⟨_, Submodule.mem_map_of_mem (hg i), _, Submodule.mem_map_of_mem (hk i), rfl⟩`.
-/
theorem comul_fourier (e : H ≃ AddChar N C) (he : ∀ h h', e (h + h') = e h * e h')
    (AA : HopfOrder (C := C) R N) (B : Matrix N N C) (hB : IsUnit B.det)
    (hAA : AA.carrier = Submodule.span R (Set.range fun j x => B x j))
    (u : N → C) (hu : u ∈ dualLat AA.carrier) :
    addPull R H (fourier (R := R) (fun h a => e h a) u) ∈
      tensorSpan R ((dualLat AA.carrier).map (fourier (R := R) fun h a => e h a)) := by
  have hg : ∀ i, (fun a => u a * B a i) ∈ dualLat AA.carrier := by
    intro i
    rw [mem_dualLat_iff_pairing_integral]
    intro f hf
    have hcol : (fun x => B x i) ∈ AA.carrier := by
      rw [hAA]
      exact Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨r, hr⟩ := (mem_dualLat_iff_pairing_integral.1 hu) _ (AA.mul_mem _ _ hcol hf)
    refine ⟨r, hr.trans (Finset.sum_congr rfl fun a _ => ?_)⟩
    simp only [Pi.mul_apply]
    ring
  have hk : ∀ i, (fun x => B⁻¹ i x) ∈ dualLat AA.carrier := by
    intro i
    rw [hAA, mem_dualLat_spanCols_iff, mem_intFun_iff_pairing]
    intro j
    show ∃ r : R, algebraMap R C r = (B⁻¹ * B) i j
    rw [Matrix.nonsing_inv_mul B hB, Matrix.one_apply]
    by_cases hij : i = j
    · exact ⟨1, by simp [hij]⟩
    · exact ⟨0, by simp [hij]⟩
  have hsplit : addPull R H (fourier (R := R) (fun h a => e h a) u) =
      ∑ i, fun p : H × H => fourier (R := R) (fun h a => e h a) (fun a => u a * B a i) p.1 *
        fourier (R := R) (fun h a => e h a) (fun x => B⁻¹ i x) p.2 := by
    funext p
    rw [Finset.sum_apply]
    simp only [addPull, LinearMap.funLeft_apply]
    calc fourier (R := R) (fun h a => e h a) u (p.1 + p.2)
        = ∑ a, u a * e p.1 a *
            ∑ i, fourier (R := R) (fun h a => e h a) (fun x => B⁻¹ i x) p.2 * B a i := by
          rw [fourier_apply' (R := R) (fun h a => e h a) u (p.1 + p.2)]
          refine Finset.sum_congr rfl fun a _ => ?_
          show u a * e (p.1 + p.2) a = _
          rw [he, AddChar.mul_apply, char_expand (R := R) e B hB p.2 a]
          ring
      _ = ∑ a, ∑ i, u a * B a i * e p.1 a *
            fourier (R := R) (fun h a => e h a) (fun x => B⁻¹ i x) p.2 := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ = ∑ i, ∑ a, u a * B a i * e p.1 a *
            fourier (R := R) (fun h a => e h a) (fun x => B⁻¹ i x) p.2 := Finset.sum_comm
      _ = ∑ i, fourier (R := R) (fun h a => e h a) (fun a => u a * B a i) p.1 *
            fourier (R := R) (fun h a => e h a) (fun x => B⁻¹ i x) p.2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [fourier_apply' (R := R) (fun h a => e h a) (fun a => u a * B a i) p.1, Finset.sum_mul]
  rw [hsplit]
  refine Submodule.sum_mem _ fun i _ => Submodule.subset_span ?_
  exact ⟨_, Submodule.mem_map_of_mem (hg i), _, Submodule.mem_map_of_mem (hk i), rfl⟩

/- English proof (translation)
Simplify using `only [fourier_apply', Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pairing_fourier (e : H ≃ AddChar N C) (w : H → C) (u : N → C) :
    ∑ h, w h * fourier (R := R) (fun h a => e h a) u h =
      ∑ a, fourier (R := R) (fun a h => e h a) w a * u a := by
  simp only [fourier_apply', Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/- English proof (translation)
Rewrite using `[mem_dualLat_iff_pairing_integral, mem_dualLat_iff_pairing_integral]`. Prove the components needed by the constructor for the conclusion. Introduce `hw f hf`. Take `⟨r, hr⟩` from `hw _ (Submodule.mem_map_of_mem hf)`. Conclude with `⟨r, hr.trans (pairing_fourier (R := R) e w f)⟩`.

Introduce `hw g hg`. Take `⟨f, hf, rfl⟩` from `Submodule.mem_map.1 hg`. Take `⟨r, hr⟩` from `hw f hf`. Conclude with `⟨r, hr.trans (pairing_fourier (R := R) e w f).symm⟩`.
-/
theorem mem_dualLat_map_fourier (e : H ≃ AddChar N C) (M : Submodule R (N → C)) (w : H → C) :
    w ∈ dualLat (M.map (fourier (R := R) fun h a => e h a)) ↔
      fourier (R := R) (fun a h => e h a) w ∈ dualLat M := by
  rw [mem_dualLat_iff_pairing_integral, mem_dualLat_iff_pairing_integral]
  constructor
  · intro hw f hf
    obtain ⟨r, hr⟩ := hw _ (Submodule.mem_map_of_mem hf)
    exact ⟨r, hr.trans (pairing_fourier (R := R) e w f)⟩
  · intro hw g hg
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hg
    obtain ⟨r, hr⟩ := hw f hf
    exact ⟨r, hr.trans (pairing_fourier (R := R) e w f).symm⟩

/- English proof (translation)
Establish `hM` using `tableM_isUnit e σ`. Use `⟨fun h => ((tableM e σ)⁻¹ *ᵥ f) (σ h), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `a`. Simplify using `only [fourier_apply']`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [tableM, Matrix.of_apply, Equiv.symm_apply_apply]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = (tableM e σ *ᵥ ((tableM e σ)⁻¹ *ᵥ f)) a := rfl`. Use `_ = f a := by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hM, Matrix.one_mulVec]`.
-/
theorem fourier'_surjective (e : H ≃ AddChar N C) (σ : H ≃ N) (f : N → C) :
    ∃ w, fourier (R := R) (fun a h => e h a) w = f := by
  have hM := tableM_isUnit e σ
  refine ⟨fun h => ((tableM e σ)⁻¹ *ᵥ f) (σ h), ?_⟩
  funext a
  simp only [fourier_apply']
  calc ∑ x, ((tableM e σ)⁻¹ *ᵥ f) (σ x) * e x a
      = ∑ j, tableM e σ a j * ((tableM e σ)⁻¹ *ᵥ f) j :=
        Fintype.sum_equiv σ _ _ fun x => by
          simp only [tableM, Matrix.of_apply, Equiv.symm_apply_apply]
          ring
    _ = (tableM e σ *ᵥ ((tableM e σ)⁻¹ *ᵥ f)) a := rfl
    _ = f a := by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hM, Matrix.one_mulVec]

end ReciprocityTheory.PGsh.L2
