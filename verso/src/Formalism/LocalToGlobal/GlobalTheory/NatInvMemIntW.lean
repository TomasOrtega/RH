import Formalism.LocalToGlobal.GlobalTheory.ColValOfTiedSOfFin
import Formalism.LocalToGlobal.GlobalTheory.ColMemOfIsLocBasis

noncomputable section

open Matrix NumberField

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def eqv (D : D7) : (D.sp.X 0).V ≃ₗ[D.host.E] (Fin (D.R.N 0) → D.host.E) :=
  (D.sp.X 0).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _))).symm)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem eqv_apply (y : (D.sp.X 0).V) : eqv D y = crd y := rfl

/- English proof (translation)
Unfold `Formalism.L2.Forms.clsCrd`. Rewrite using `[Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Use `hy using 1` and compare the differences between its conclusion and the goal.

Conclude with `(eqv D).symm_apply_apply y`. Introduce `h`. Conclude with `⟨_, h, (eqv D).apply_symm_apply z⟩`.
-/
theorem mem_clsCrd_iff {u : D.what₂.Word} (c : (D.mem u).C.cls 0) (z : Fin (D.R.N 0) → D.host.E) :
    z ∈ Formalism.L2.Forms.clsCrd D u 0 (Nat.zero_le _) c ↔ (eqv D).symm z ∈ D.clsLat u 0 c := by
  unfold Formalism.L2.Forms.clsCrd
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    convert hy using 1
    exact (eqv D).symm_apply_apply y
  · intro h
    exact ⟨_, h, (eqv D).apply_symm_apply z⟩

def vcol (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (a : Fin (D.R.N 0)) : (D.sp.X 0).V :=
  (eqv D).symm fun r => Y r a

/- English proof (translation)
Rewrite using `[← eqv_apply]`. Conclude with `(eqv D).apply_symm_apply _`.
-/
theorem crd_vcol (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (a : Fin (D.R.N 0)) :
    crd (vcol Y a) = fun r => Y r a := by
  rw [← eqv_apply]
  exact (eqv D).apply_symm_apply _

variable {u : D.what₂.Word} (B : ColBase D u)

/- English proof (translation)
Establish `hfr : ∀ r : Fin (D.R.N 0), (eqv D).symm (Pi.single r 1) = (D.sp.X 0).frame ((finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _))).symm r)`. Introduce `r`. Rewrite using `[LinearEquiv.symm_apply_eq]`. Use extensionality with `r'`. Simplify using `[eqv, Pi.single_apply]`.

Rewrite using `[Finsupp.single_apply]`. Apply the tactic sequence `split_ifs <;> simp_all [Fin.cast_inj]`. Establish `hz : (fun r => Y r a) = ∑ r, Y r a • (Pi.single r (1 : D.host.E) : Fin (D.R.N 0) → D.host.E)`. Use extensionality with `r'`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.

Establish `hbc : B.bc c τ (vcol Y a) = ∑ r, B.rho τ (Y r a) • B.bc c τ ((D.sp.X 0).frame ((finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _))).symm r))`. Unfold `vcol`. Rewrite using `[hz, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, B.bc_smul, hfr]`.

Establish `hexp : ∀ v : (B.Q c τ).V, v = ∑ i, (B.Q c τ).b.repr v ((B.eQ c τ).symm i) • (B.Q c τ).b ((B.eQ c τ).symm i)`. Introduce `v`. Rewrite using `[Equiv.sum_comp (B.eQ c τ).symm (fun j => (B.Q c τ).b.repr v j • (B.Q c τ).b j)]`. Conclude with `((B.Q c τ).b.sum_repr v).symm`. Rewrite using `[hbc]`.

Simplify using `only [Matrix.mul_apply, Matrix.map_apply, Mb, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Use `conv_rhs => rw [hexp (B.bc c τ ((D.sp.X 0).frame ((finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _))).symm r)))]`. Rewrite using `[Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, mul_comm]`.
-/
theorem sum_gamma (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
    (a : Fin (D.R.N 0)) :
    ∑ i, (Mb B c τ * Y.map (B.rho τ)) i a • (B.Q c τ).b ((B.eQ c τ).symm i) = B.bc c τ (vcol Y a) := by
  have hfr : ∀ r : Fin (D.R.N 0), (eqv D).symm (Pi.single r 1) =
      (D.sp.X 0).frame ((finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _))).symm r) := by
    intro r
    rw [LinearEquiv.symm_apply_eq]
    ext r'
    simp [eqv, Pi.single_apply]
    rw [Finsupp.single_apply]
    split_ifs <;> simp_all [Fin.cast_inj]
  have hz : (fun r => Y r a) = ∑ r, Y r a • (Pi.single r (1 : D.host.E) : Fin (D.R.N 0) → D.host.E) := by
    ext r'
    simp [Finset.sum_apply, Pi.single_apply]
  have hbc : B.bc c τ (vcol Y a) = ∑ r, B.rho τ (Y r a) •
      B.bc c τ ((D.sp.X 0).frame ((finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _))).symm r)) := by
    unfold vcol
    rw [hz, map_sum, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_smul, B.bc_smul, hfr]
  have hexp : ∀ v : (B.Q c τ).V,
      v = ∑ i, (B.Q c τ).b.repr v ((B.eQ c τ).symm i) • (B.Q c τ).b ((B.eQ c τ).symm i) := by
    intro v
    rw [Equiv.sum_comp (B.eQ c τ).symm (fun j => (B.Q c τ).b.repr v j • (B.Q c τ).b j)]
    exact ((B.Q c τ).b.sum_repr v).symm
  rw [hbc]
  simp only [Matrix.mul_apply, Matrix.map_apply, Mb, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  conv_rhs => rw [hexp (B.bc c τ ((D.sp.X 0).frame ((finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _))).symm r)))]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, mul_comm]

/- English proof (translation)
Take `⟨k, hk⟩` from `hy`. Establish `hint : IsIntegral ℤ (rhoC D τ (k : D.host.E))` using `(RingOfIntegers.isIntegral_coe k).map (rhoC D τ).toIntAlgHom`. Establish `hk' : (s : D.what₂.LL) * rhoC D τ y ∈ intW D.what₂.places w`. Establish `h1 : rhoC D τ ((s : D.host.E) * y) = (s : D.what₂.LL) * rhoC D τ y`. Rewrite using `[map_mul, map_natCast]`.

Rewrite using `[← h1, ← hk]`. Conclude with `Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwG_int_mem D w ⟨_, hint⟩`. Establish `hinv : ((s : D.what₂.LL))⁻¹ ∈ intW D.what₂.places w`. Express the relevant statement in the definitionally equal form `(0 : WithTop ℤ) ≤ D.what₂.places.val w ((s : D.what₂.LL))⁻¹`. Establish `h0 : D.what₂.places.val w ((s : D.what₂.LL)) = 0` using `Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_val_nat_eq_zero (s := s) (hs := hs)`.

Rewrite using `[AddValuation.map_inv, h0, neg_zero]`. Establish `hs0 : (s : D.what₂.LL) ≠ 0`. Introduce `h`. Apply `hs` to reduce the goal to its premises. Establish `h2 : s = 0` using `by exact_mod_cast h`.

Rewrite using `[h2]`. Conclude with `dvd_zero _`. Establish `h3` using `(intW D.what₂.places w).mul_mem hinv hk'`. Rewrite `h3` using `[← mul_assoc, inv_mul_cancel₀ hs0, one_mul]`. Then use the resulting hypothesis.
-/
theorem rhoC_mem_intW (w : D.what₂.places.Pl) (τ : D.what₂.Tau) (y : D.host.E) (s : ℕ)
    (hs : ¬ D.what₂.places.resChar w ∣ s) (hy : (s : D.host.E) * y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) :
    rhoC D τ y ∈ intW D.what₂.places w := by
  obtain ⟨k, hk⟩ := hy
  have hint : IsIntegral ℤ (rhoC D τ (k : D.host.E)) :=
    (RingOfIntegers.isIntegral_coe k).map (rhoC D τ).toIntAlgHom
  have hk' : (s : D.what₂.LL) * rhoC D τ y ∈ intW D.what₂.places w := by
    have h1 : rhoC D τ ((s : D.host.E) * y) = (s : D.what₂.LL) * rhoC D τ y := by
      rw [map_mul, map_natCast]
    rw [← h1, ← hk]
    exact Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwG_int_mem D w ⟨_, hint⟩
  have hinv : ((s : D.what₂.LL))⁻¹ ∈ intW D.what₂.places w := by
    change (0 : WithTop ℤ) ≤ D.what₂.places.val w ((s : D.what₂.LL))⁻¹
    have h0 : D.what₂.places.val w ((s : D.what₂.LL)) = 0 :=
      Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_val_nat_eq_zero (s := s) (hs := hs)
    rw [AddValuation.map_inv, h0, neg_zero]
  have hs0 : (s : D.what₂.LL) ≠ 0 := by
    intro h
    apply hs
    have h2 : s = 0 := by exact_mod_cast h
    rw [h2]
    exact dvd_zero _
  have h3 := (intW D.what₂.places w).mul_mem hinv hk'
  rwa [← mul_assoc, inv_mul_cancel₀ hs0, one_mul] at h3

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(0 : WithTop ℤ) ≤ D.what₂.places.val w ((t : D.what₂.LL))⁻¹`. Establish `h0 : D.what₂.places.val w ((t : D.what₂.LL)) = 0` using `Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_val_nat_eq_zero (s := t) (hs := ht)`. Rewrite using `[AddValuation.map_inv, h0, neg_zero]`.
-/
theorem natInv_mem_intW (w : D.what₂.places.Pl) (t : ℕ) (ht : ¬ D.what₂.places.resChar w ∣ t) :
    ((t : D.what₂.LL))⁻¹ ∈ intW D.what₂.places w := by
  change (0 : WithTop ℤ) ≤ D.what₂.places.val w ((t : D.what₂.LL))⁻¹
  have h0 : D.what₂.places.val w ((t : D.what₂.LL)) = 0 :=
    Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwA_val_nat_eq_zero (s := t) (hs := ht)
  rw [AddValuation.map_inv, h0, neg_zero]

/- English proof (translation)
Establish `hp1 : ¬ D.what₂.places.resChar w ∣ 1` using `(D.what₂.places.resChar_prime w).not_dvd_one`. Establish `hg : ∀ a, ∑ i, (Mb B c τ * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (B.rho τ)) i a • (B.Q c τ).b ((B.eQ c τ).symm i) = B.bc c τ (vcol (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) a)` using `fun a => sum_gamma B c τ _ a`. Establish `hsmul : ∀ (r : D.what₂.LL) (hr : r ∈ intW D.what₂.places w) (v : (B.Q c τ).V), r • v = (⟨r, hr⟩ : intW D.what₂.places w) • v` using `fun r hr v => by rw [Subring.smul_def]`. Establish `hcolv : ∀ v : Fin (D.R.N 0) → D.host.E, (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ v = ∑ a, v a • (fun r => (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) r a)`. Introduce `v`.

Use extensionality with `r`. Simplify using `only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Conclude with `Finset.sum_congr rfl fun _ _ => mul_comm _ _`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_mul]`.

Use `IsUnit.mul (isUnit_iff_ne_zero.2 (Mb_det_ne B c τ)) ?_` and prove the remaining obligations. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit Y)).map _`. Simplify using `only [hg]`. Apply `le_antisymm` to reduce the goal to its premises.

Unfold `locW`. Rewrite using `[Submodule.span_le]`. Introduce `x hx`. Rewrite `hx` using `[SetLike.mem_coe, B.bc_L c τ]`. Use `Submodule.span_induction (p := fun x _ => x ∈ Submodule.span (intW D.what₂.places w) (Set.range fun a => B.bc c τ (vcol (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) a))) ?_ ?_ ?_ ?_ hx` and prove the remaining obligations.

Introduce and unpack `_ ⟨y, hy, rfl⟩`. Establish `hz : eqv D y ∈ Formalism.L2.Forms.clsCrd D u 0 (Nat.zero_le _) c`. Rewrite using `[mem_clsCrd_iff, LinearEquiv.symm_apply_apply]`. Conclude with `hy`. Take `⟨s, hs, hint⟩` from `(hY (eqv D y)).1 ⟨1, hp1, by rw [Nat.cast_one, one_smul]; exact hz⟩`.

Establish `h1 : (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((((Y⁻¹ : GL (Fin (D.R.N 0)) D.host.E)) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ eqv D y) = eqv D y`. Rewrite using `[Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Establish `hyz : y = ∑ a, ((((Y⁻¹ : GL (Fin (D.R.N 0)) D.host.E)) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ eqv D y) a • vcol (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) a` using `by conv_lhs => rw [← (eqv D).symm_apply_apply y, ← h1, hcolv, map_sum]`. Simplify using `only [LinearEquiv.map_smul]`. Both sides reduce to the same expression.

Rewrite using `[hyz, map_sum]`. Use `Submodule.sum_mem _ fun a _ => ?_` and prove the remaining obligations. Rewrite using `[B.bc_smul, hB, hsmul _ (rhoC_mem_intW w τ _ s hs (hint a))]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)`. Conclude with `zero_mem _`.

Introduce `x y _ _ hx hy`. Conclude with `add_mem hx hy`. Introduce `r x _ hx`. Establish `hr : r • x = (⟨_, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwG_int_mem D w r⟩ : intW D.what₂.places w) • x`. Rewrite using `[Subring.smul_def]`.

Conclude with `(algebraMap_smul D.what₂.LL r x).symm`. Rewrite using `[hr]`. Conclude with `Submodule.smul_mem _ _ hx`. Unfold `locW`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨a, rfl⟩`. Establish `hcol : (fun r => (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) r a) = (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ Pi.single a 1`. Use extensionality with `r`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Take `⟨s, hs, hsm⟩` from `(hY (fun r => (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) r a)).2 ⟨1, hp1, fun b => by`.

Rewrite using `[hcol, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Nat.cast_one, one_mul]`. Distinguish the cases in `hb : b = a`. Substitute `hb` using the available equality. Conclude with `⟨1, by simp⟩`. Conclude with `⟨0, by simp [Pi.single_apply, hb]⟩⟩`.

Rewrite `hsm` using `[SetLike.mem_coe, mem_clsCrd_iff, LinearEquiv.map_smul]`. Establish `hQ : B.bc c τ ((s : D.host.E) • vcol (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) a) ∈ (B.Q c τ).L`. Rewrite using `[B.bc_L c τ]`. Conclude with `Submodule.subset_span ⟨_, hsm, rfl⟩`. Rewrite `hQ` using `[B.bc_smul, map_natCast]`.

Establish `hs0 : (s : D.what₂.LL) ≠ 0`. Introduce `h`. Apply `hs` to reduce the goal to its premises. Establish `h2 : s = 0` using `by exact_mod_cast h`. Rewrite using `[h2]`.

Conclude with `dvd_zero _`. Establish `h4 : B.bc c τ (vcol (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) a) = (⟨_, natInv_mem_intW w s hs⟩ : intW D.what₂.places w) • ((s : D.what₂.LL) • B.bc c τ (vcol (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) a))`. Rewrite using `[Subring.smul_def, smul_smul, inv_mul_cancel₀ hs0, one_smul]`. Rewrite using `[SetLike.mem_coe]`. Use `beta_reduce`.

Rewrite using `[h4]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hQ)`.
-/
theorem locBasis_gamma (hB : B.rho = rhoC D) (w : D.what₂.places.Pl) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau)
    (Y : GL (Fin (D.R.N 0)) D.host.E)
    (hY : Formalism.L2.Forms.IsLocBasis (D.what₂.places.resChar w)
      (Formalism.L2.Forms.clsCrd D u 0 (Nat.zero_le _) c : Set (Fin (D.R.N 0) → D.host.E)) Y) :
    Formalism.MainNotions.flipTwoThree.LocBasis D w (B.Q c τ) (B.eQ c τ)
      (Mb B c τ * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (B.rho τ)) := by
  have hp1 : ¬ D.what₂.places.resChar w ∣ 1 := (D.what₂.places.resChar_prime w).not_dvd_one
  have hg : ∀ a, ∑ i, (Mb B c τ * (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E).map (B.rho τ)) i a •
      (B.Q c τ).b ((B.eQ c τ).symm i) = B.bc c τ (vcol (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) a) :=
    fun a => sum_gamma B c τ _ a
  have hsmul : ∀ (r : D.what₂.LL) (hr : r ∈ intW D.what₂.places w) (v : (B.Q c τ).V),
      r • v = (⟨r, hr⟩ : intW D.what₂.places w) • v := fun r hr v => by rw [Subring.smul_def]
  have hcolv : ∀ v : Fin (D.R.N 0) → D.host.E, (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ v =
      ∑ a, v a • (fun r => (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) r a) := by
    intro v
    ext r
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_mul]
    refine IsUnit.mul (isUnit_iff_ne_zero.2 (Mb_det_ne B c τ)) ?_
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit Y)).map _
  · simp only [hg]
    apply le_antisymm
    · unfold locW
      rw [Submodule.span_le]
      intro x hx
      rw [SetLike.mem_coe, B.bc_L c τ] at hx
      refine Submodule.span_induction (p := fun x _ => x ∈ Submodule.span (intW D.what₂.places w)
        (Set.range fun a => B.bc c τ (vcol (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) a))) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨y, hy, rfl⟩
        have hz : eqv D y ∈ Formalism.L2.Forms.clsCrd D u 0 (Nat.zero_le _) c := by
          rw [mem_clsCrd_iff, LinearEquiv.symm_apply_apply]
          exact hy
        obtain ⟨s, hs, hint⟩ := (hY (eqv D y)).1 ⟨1, hp1, by rw [Nat.cast_one, one_smul]; exact hz⟩
        have h1 : (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
            ((((Y⁻¹ : GL (Fin (D.R.N 0)) D.host.E)) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ eqv D y) =
            eqv D y := by
          rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
        have hyz : y = ∑ a, ((((Y⁻¹ : GL (Fin (D.R.N 0)) D.host.E)) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
            eqv D y) a • vcol (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) a := by
          conv_lhs => rw [← (eqv D).symm_apply_apply y, ← h1, hcolv, map_sum]
          simp only [LinearEquiv.map_smul]
          rfl
        rw [hyz, map_sum]
        refine Submodule.sum_mem _ fun a _ => ?_
        rw [B.bc_smul, hB, hsmul _ (rhoC_mem_intW w τ _ s hs (hint a))]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
      · exact zero_mem _
      · intro x y _ _ hx hy
        exact add_mem hx hy
      · intro r x _ hx
        have hr : r • x = (⟨_, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwG_int_mem D w r⟩ : intW D.what₂.places w) • x := by
          rw [Subring.smul_def]
          exact (algebraMap_smul D.what₂.LL r x).symm
        rw [hr]
        exact Submodule.smul_mem _ _ hx
    · unfold locW
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      have hcol : (fun r => (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) r a) =
          (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ Pi.single a 1 := by
        ext r
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      obtain ⟨s, hs, hsm⟩ := (hY (fun r => (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) r a)).2 ⟨1, hp1, fun b => by
        rw [hcol, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Nat.cast_one, one_mul]
        by_cases hb : b = a
        · subst hb
          exact ⟨1, by simp⟩
        · exact ⟨0, by simp [Pi.single_apply, hb]⟩⟩
      rw [SetLike.mem_coe, mem_clsCrd_iff, LinearEquiv.map_smul] at hsm
      have hQ : B.bc c τ ((s : D.host.E) • vcol (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) a) ∈
          (B.Q c τ).L := by
        rw [B.bc_L c τ]
        exact Submodule.subset_span ⟨_, hsm, rfl⟩
      rw [B.bc_smul, map_natCast] at hQ
      have hs0 : (s : D.what₂.LL) ≠ 0 := by
        intro h
        apply hs
        have h2 : s = 0 := by exact_mod_cast h
        rw [h2]
        exact dvd_zero _
      have h4 : B.bc c τ (vcol (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) a) =
          (⟨_, natInv_mem_intW w s hs⟩ : intW D.what₂.places w) •
            ((s : D.what₂.LL) • B.bc c τ (vcol (Y : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) a)) := by
        rw [Subring.smul_def, smul_smul, inv_mul_cancel₀ hs0, one_smul]
      rw [SetLike.mem_coe]
      beta_reduce
      rw [h4]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hQ)

end Formalism.L2.GlobalTheoryTheory.ColValS
