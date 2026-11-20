import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisGe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjPrincipalFractionalIntegralIdempotentSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfDualVectorPairsIntegralFrameColumns
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InverseSelfDualFrameStandardSpaceIntegral

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevelDatum

variable {D : D7}

def rowP (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (e : AE D) (x : Fin W.rank → D.host.E) (a : Fin W.rank) : EAf D :=
  toEAf D e * ∑ k, eToEAf D (∑ l, D.sp.cm.sig (x l) * W.gram l k) * β.val k a

/- English proof (translation)
Simplify using `only [rowP, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib, mul_add]`.
-/
theorem rowPairing_add (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (e : AE D) (x y : Fin W.rank → D.host.E) (a : Fin W.rank) :
    rowP W β e (x + y) a = rowP W β e x a + rowP W β e y a := by
  simp only [rowP, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib, mul_add]

/- English proof (translation)
Simplify using `only [rowP, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, mul_zero]`.
-/
theorem rowPairing_zero (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (e : AE D) (a : Fin W.rank) :
    rowP W β e 0 a = 0 := by
  simp only [rowP, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, mul_zero]

/- English proof (translation)
Simplify using `only [rowP, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc, ← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rowPairing_smul (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (e : AE D) (c : D.host.E) (x : Fin W.rank → D.host.E)
    (a : Fin W.rank) : rowP W β e (c • x) a = eToEAf D (D.sp.cm.sig c) * rowP W β e x a := by
  simp only [rowP, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc, ← Finset.mul_sum]
  ring

/- English proof (translation)
Simplify using `only [FWT.uMat, rowP, hV, inv_one, Matrix.one_mul, Matrix.mul_assoc]`. Simplify using `only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem uMat_eq (V W : HSp D) (hV : V.gram = 1) (βV : GL (Fin V.rank) (EAf D)) (β : GL (Fin W.rank) (EAf D)) (e : AE D)
    (X : Fin V.rank → Fin W.rank → D.host.E) (b : Fin V.rank) (a : Fin W.rank) :
    FWT.uMat V W βV β e X b a = ∑ b', (βV⁻¹).val b b' * rowP W β e (X b') a := by
  simp only [FWT.uMat, rowP, hV, inv_one, Matrix.one_mul, Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem eToEAf_int (c : 𝓞 D.host.E) : eToEAf D (c : D.host.E) = (oToS D.host.F D.host.E c : Formalism.L2.Herm.intAf D.host.F D.host.E) := rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨_, (RingOfIntegers.isIntegral_coe c).map (D.sp.cm.sig : D.host.E →+* D.host.E).toIntAlgHom⟩, rfl⟩`.
-/
theorem exists_sig (c : 𝓞 D.host.E) : ∃ c' : 𝓞 D.host.E, (c' : D.host.E) = D.sp.cm.sig (c : D.host.E) :=
  ⟨⟨_, (RingOfIntegers.isIntegral_coe c).map (D.sp.cm.sig : D.host.E →+* D.host.E).toIntAlgHom⟩, rfl⟩

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨c, hc, v, hv, rfl⟩` from `hx`. Rewrite using `[rowPairing_smul, rowP, ← mul_assoc, mul_comm _ (toEAf D e)]`. Conclude with `mul_mem (GlobalTheory.IdemIntegral.conj_mem_intAf D e P he hP c hc) (GlobalTheory.PairIntegral.pair_mem_intAf D W β Λ hβ v hv a)`.

Consider the case `zero => rw [rowPairing_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [rowPairing_add]`. Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx`.

Take `⟨c', hc'⟩` from `exists_sig c`. Rewrite using `[show c • x = (c : D.host.E) • x from rfl, rowPairing_smul, ← hc', eToEAf_int]`. Conclude with `mul_mem (Subtype.prop _) hx`.
-/
theorem rowP_int (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E))
    (hβ : IsSDFrame W β Λ 1) (e : AE D) (P : Finset (Pl D.host.E)) (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (x : Fin W.rank → D.host.E) (hx : x ∈ latG W 1) (a : Fin W.rank) :
    rowP W β e x a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, v, hv, rfl⟩ := hx
    rw [rowPairing_smul, rowP, ← mul_assoc, mul_comm _ (toEAf D e)]
    exact mul_mem (GlobalTheory.IdemIntegral.conj_mem_intAf D e P he hP c hc) (GlobalTheory.PairIntegral.pair_mem_intAf D W β Λ hβ v hv a)
  | zero => rw [rowPairing_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [rowPairing_add]; exact add_mem hx hy
  | smul c x _ hx =>
    obtain ⟨c', hc'⟩ := exists_sig c
    rw [show c • x = (c : D.host.E) • x from rfl, rowPairing_smul, ← hc', eToEAf_int]
    exact mul_mem (Subtype.prop _) hx

/- English proof (translation)
Use `Submodule.smul_induction_on (p := fun x => resS D.host.F PP ⟨_, hi x⟩ = 0) hx (fun c hc y _ => ?_) (fun x y hx hy => ?_)` and prove the remaining obligations. Take `⟨c', hc', e'⟩` from `hJ c hc`. Establish `: (⟨_, hi (c • y)⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = oToS D.host.F D.host.E c' * ⟨_, hi y⟩`. Use `Subtype.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `rowP W β e (ι (c • y)) a = eToEAf D (c' : D.host.E) * rowP W β e (ι y) a`.

Rewrite using `[map_smul, show c • ι y = (c : D.host.E) • ι y from rfl, rowPairing_smul, e']`. Rewrite using `[this, map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hc', zero_mul]`. Establish `: (⟨_, hi (x + y)⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨_, hi x⟩ + ⟨_, hi y⟩`. Use `Subtype.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `rowP W β e (ι (x + y)) a = rowP W β e (ι x) a + rowP W β e (ι y) a`.

Rewrite using `[map_add, rowPairing_add]`. Rewrite using `[this, map_add, hx, hy, add_zero]`.
-/
theorem residue_rowPairing_eq_zero (W : HSp D) (β : GL (Fin W.rank) (EAf D)) (e : AE D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (a : Fin W.rank)
    (hi : ∀ x, rowP W β e (ι x) a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (J : Ideal (𝓞 D.host.E)) (PP : Pl D.host.E)
    (hJ : ∀ c ∈ J, ∃ c' ∈ PP.asIdeal, (c' : D.host.E) = D.sp.cm.sig (c : D.host.E))
    (x : La) (hx : x ∈ J • (⊤ : Submodule (𝓞 D.host.E) La)) : resS D.host.F PP ⟨_, hi x⟩ = 0 := by
  refine Submodule.smul_induction_on (p := fun x => resS D.host.F PP ⟨_, hi x⟩ = 0) hx (fun c hc y _ => ?_) (fun x y hx hy => ?_)
  · obtain ⟨c', hc', e'⟩ := hJ c hc
    have : (⟨_, hi (c • y)⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = oToS D.host.F D.host.E c' * ⟨_, hi y⟩ := by
      refine Subtype.ext ?_
      change rowP W β e (ι (c • y)) a = eToEAf D (c' : D.host.E) * rowP W β e (ι y) a
      rw [map_smul, show c • ι y = (c : D.host.E) • ι y from rfl, rowPairing_smul, e']
    rw [this, map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hc', zero_mul]
  · have : (⟨_, hi (x + y)⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨_, hi x⟩ + ⟨_, hi y⟩ := by
      refine Subtype.ext ?_
      change rowP W β e (ι (x + y)) a = rowP W β e (ι x) a + rowP W β e (ι y) a
      rw [map_add, rowPairing_add]
    rw [this, map_add, hx, hy, add_zero]

/- English proof (translation)
Establish `h : IsIntM (FWT.uMat V W βV β e X)` using `fun b a => by`. Rewrite using `[uMat_eq V W hV]`. Conclude with `sum_mem fun b' _ => mul_mem (hβ b b') (hi b' a)`. Use `⟨h, fun PP b a => ?_⟩` and prove the remaining obligations. Rewrite using `[redM, dif_pos (h b a)]`.

Simplify using `only [← map_mul, ← map_sum]`. Use `congr 1`. Use `Subtype.ext ?_` and prove the remaining obligations. Rewrite using `[AddSubmonoidClass.coe_finsetSum]`. Conclude with `uMat_eq V W hV βV β e X b a`.
-/
theorem redM_uMat (V W : HSp D) (hV : V.gram = 1) (βV : GL (Fin V.rank) (EAf D)) (hβ : IsIntM (βV⁻¹).val)
    (β : GL (Fin W.rank) (EAf D)) (e : AE D) (X : Fin V.rank → Fin W.rank → D.host.E)
    (hi : ∀ b a, rowP W β e (X b) a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    IsIntM (FWT.uMat V W βV β e X) ∧ ∀ PP b a, redM PP (FWT.uMat V W βV β e X) b a =
      ∑ b', resS D.host.F PP ⟨_, hβ b b'⟩ * resS D.host.F PP ⟨_, hi b' a⟩ := by
  have h : IsIntM (FWT.uMat V W βV β e X) := fun b a => by
    rw [uMat_eq V W hV]
    exact sum_mem fun b' _ => mul_mem (hβ b b') (hi b' a)
  refine ⟨h, fun PP b a => ?_⟩
  rw [redM, dif_pos (h b a)]
  simp only [← map_mul, ← map_sum]
  congr 1
  refine Subtype.ext ?_
  rw [AddSubmonoidClass.coe_finsetSum]
  exact uMat_eq V W hV βV β e X b a

/- English proof (translation)
Establish `h1 : omegaK Pg y = omegaK Pg y'`. Unfold `omegaK`. Use `if_congr (forall₂_congr fun PP hPP => by rw [h PP (Or.inl hPP)]) rfl rfl` and prove the remaining obligations. Establish `h2 : omegaQ Q r ξ k y = omegaQ Q r ξ k y'`. Establish `e : (∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det) ↔ ∀ PP ∈ Q, LowZero r (y' PP) ∧ IsUnit (topL r (y' PP)).det` using `forall₂_congr fun PP hPP => by rw [h PP (Or.inr hPP)]`.

Unfold `omegaQ`. Distinguish the cases in `c : ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det`. Rewrite using `[dif_pos c, dif_pos (e.1 c)]`. Use `Finset.prod_congr rfl fun PP _ => ?_` and prove the remaining obligations. Establish `: (c PP.1 PP.2).2.unit = (e.1 c PP.1 PP.2).2.unit` using `Units.ext (by`.

Rewrite using `[IsUnit.unit_spec, IsUnit.unit_spec, h PP.1 (Or.inr PP.2)])`. Rewrite using `[this]`. Rewrite using `[dif_neg c, dif_neg (fun c' => c (e.2 c'))]`. Rewrite using `[h1, h2]`.
-/
theorem omega_congr {a b : ℕ} (Pg Q : Finset (Pl D.host.E)) (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y y' : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) (h : ∀ PP, PP ∈ Pg ∨ PP ∈ Q → y PP = y' PP) :
    omegaK Pg y * omegaQ Q r ξ k y = omegaK Pg y' * omegaQ Q r ξ k y' := by
  classical
  have h1 : omegaK Pg y = omegaK Pg y' := by
    unfold omegaK
    refine if_congr (forall₂_congr fun PP hPP => by rw [h PP (Or.inl hPP)]) rfl rfl
  have h2 : omegaQ Q r ξ k y = omegaQ Q r ξ k y' := by
    have e : (∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det) ↔
        ∀ PP ∈ Q, LowZero r (y' PP) ∧ IsUnit (topL r (y' PP)).det :=
      forall₂_congr fun PP hPP => by rw [h PP (Or.inr hPP)]
    unfold omegaQ
    by_cases c : ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det
    · rw [dif_pos c, dif_pos (e.1 c)]
      refine Finset.prod_congr rfl fun PP _ => ?_
      have : (c PP.1 PP.2).2.unit = (e.1 c PP.1 PP.2).2.unit := Units.ext (by
        rw [IsUnit.unit_spec, IsUnit.unit_spec, h PP.1 (Or.inr PP.2)])
      rw [this]
    · rw [dif_neg c, dif_neg (fun c' => c (e.2 c'))]
  rw [h1, h2]

/- English proof (translation)
Establish `hf : ∀ PP : Pl D.host.E, 0 < Nat.card (kP PP)ˣ` using `fun PP => by`. Establish `: Finite (kP PP)` using `Ideal.finiteQuotientOfFreeOfNeBot _ PP.ne_bot`. Conclude with `Nat.card_pos`. Take `⟨M, hM, h⟩` from `GlobalTheory.Mem.FrameVal.exists_roots (∏ PP ∈ Q, Nat.card (kP PP)ˣ) (Finset.prod_pos fun PP _ => hf PP)`. Use `⟨M, hM, fun r ξ k y => mul_mem ?_ ?_⟩` and prove the remaining obligations.

Unfold `omegaK split_ifs exacts [one_mem _, zero_mem _]`. Unfold `omegaQ split_ifs`. Use `prod_mem fun PP _ => zpow_mem (h _ ?_) _` and prove the remaining obligations. Take `⟨u, hu⟩` from `Finset.dvd_prod_of_mem (fun PP : Pl D.host.E => Nat.card (kP PP)ˣ) PP.2`. Rewrite using `[hu, pow_mul, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one, one_pow]`.

Conclude with `zero_mem _`.
-/
theorem exists_omega_field (Pg Q : Finset (Pl D.host.E)) : ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧
    ∀ {a b : ℕ} (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ)
      (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)), omegaK Pg y * omegaQ Q r ξ k y ∈ M := by
  have hf : ∀ PP : Pl D.host.E, 0 < Nat.card (kP PP)ˣ := fun PP => by
    have : Finite (kP PP) := Ideal.finiteQuotientOfFreeOfNeBot _ PP.ne_bot
    exact Nat.card_pos
  obtain ⟨M, hM, h⟩ := GlobalTheory.Mem.FrameVal.exists_roots (∏ PP ∈ Q, Nat.card (kP PP)ˣ) (Finset.prod_pos fun PP _ => hf PP)
  refine ⟨M, hM, fun r ξ k y => mul_mem ?_ ?_⟩
  · unfold omegaK
    split_ifs
    exacts [one_mem _, zero_mem _]
  · unfold omegaQ
    split_ifs
    · refine prod_mem fun PP _ => zpow_mem (h _ ?_) _
      obtain ⟨u, hu⟩ := Finset.dvd_prod_of_mem (fun PP : Pl D.host.E => Nat.card (kP PP)ˣ) PP.2
      rw [hu, pow_mul, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one, one_pow]
    · exact zero_mem _

set_option maxHeartbeats 800000 in

/- English proof (translation)
Establish `key : ∀ b' a, resS D.host.F PP ⟨_, hi (z b') a⟩ = resS D.host.F PP ⟨_, hi (x b') a⟩` using `fun b' a => by`. Establish `h2` using `residue_rowPairing_eq_zero W β e ι a (fun x => hi x a) J PP hJ _ (h b')`. Establish `: (⟨_, hi (z b') a⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨_, hi (z b' - x b') a⟩ + ⟨_, hi (x b') a⟩`. Use `Subtype.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `rowP W β e (ι (z b')) a = rowP W β e (ι (z b' - x b')) a + rowP W β e (ι (x b')) a`.

Rewrite using `[← rowPairing_add, ← LinearMap.map_add, sub_add_cancel]`. Rewrite using `[this, RingHom.map_add, h2, zero_add]`. Use function extensionality and compare the values at `b a`. Conclude with `((redM_uMat V W hV βV hβ β e (fun b => ι (z b)) fun b a => hi (z b) a).2 PP b a).trans ((Finset.sum_congr rfl fun b' _ => congrArg _ (key b' a)).trans ((redM_uMat V W hV βV hβ β e (fun b => ι (x b)) fun b a => hi (x b) a).2 PP b a).symm)`.
-/
theorem exists_datum (V W : HSp D) (hV : V.gram = 1) (βV : GL (Fin V.rank) (EAf D)) (hβ : IsIntM (βV⁻¹).val)
    (β : GL (Fin W.rank) (EAf D)) (e : AE D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E))
    (hi : ∀ x a, rowP W β e (ι x) a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (J : Ideal (𝓞 D.host.E)) (PP : Pl D.host.E)
    (hJ : ∀ c ∈ J, ∃ c' ∈ PP.asIdeal, (c' : D.host.E) = D.sp.cm.sig (c : D.host.E))
    (x z : Fin V.rank → La) (h : ∀ b, z b - x b ∈ J • (⊤ : Submodule (𝓞 D.host.E) La)) :
    redM PP (FWT.uMat V W βV β e fun b => ι (z b)) = redM PP (FWT.uMat V W βV β e fun b => ι (x b)) := by
  have key : ∀ b' a, resS D.host.F PP ⟨_, hi (z b') a⟩ = resS D.host.F PP ⟨_, hi (x b') a⟩ := fun b' a => by
    have h2 := residue_rowPairing_eq_zero W β e ι a (fun x => hi x a) J PP hJ _ (h b')
    have : (⟨_, hi (z b') a⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨_, hi (z b' - x b') a⟩ + ⟨_, hi (x b') a⟩ := by
      refine Subtype.ext ?_
      change rowP W β e (ι (z b')) a = rowP W β e (ι (z b' - x b')) a + rowP W β e (ι (x b')) a
      rw [← rowPairing_add, ← LinearMap.map_add, sub_add_cancel]
    rw [this, RingHom.map_add, h2, zero_add]
  funext b a
  exact ((redM_uMat V W hV βV hβ β e (fun b => ι (z b)) fun b a => hi (z b) a).2 PP b a).trans
    ((Finset.sum_congr rfl fun b' _ => congrArg _ (key b' a)).trans
      ((redM_uMat V W hV βV hβ β e (fun b => ι (x b)) fun b a => hi (x b) a).2 PP b a).symm)

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A Ks _ _ _ R hlev hvP i hV t La _ _ ι hι`. Take `⟨M, hM, hv⟩` from `exists_omega_field R.Pg (R.Q t)`. Use `⟨M, hM, fun M' hle hP J hJ => ?_⟩` and prove the remaining obligations. Take `⟨-, e, he, -⟩` from `hvP i t`. Establish `hβ` using `GlobalTheory.StdFrameInv.isIntM_inv D i _ _ hV (hlev.βV i)`.

Establish `hi : ∀ x a, rowP (Wc D i) (R.βW i) e (ι x) a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E` using `fun x a => rowP_int _ _ _ (hlev.βW i) e _ he (fun PP h => hP PP (by simpa using h)) _ (hι.2.le (LinearMap.mem_range_self ι x)) a`. Use `⟨fun q => ⟨_, hle (hv (Wc D i).rank (R.xiR t) (-1) fun PP => redM PP (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => ι (q b).out))⟩, e, he, fun x => ⟨(redM_uMat (Vc D i) (Wc D i) hV.1 _ hβ (R.βW i) e (fun b => ι (x b)) fun b a => hi (x b) a).1, ?_⟩⟩` and prove the remaining obligations. Conclude with `omega_congr _ _ _ _ _ _ _ fun PP hPP => exists_datum (Vc D i) (Wc D i) hV.1 _ hβ (R.βW i) e ι hi J PP (hJ PP hPP) x _ fun b => (Submodule.Quotient.eq _).1 (Quotient.out_eq _)`.
-/
theorem exists_phi : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.thP_vP → ∀ (i : Fin D.R.m), VStd D i → ∀ (t : T0) (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ M' : IntermediateField ℚ ℂ, M ≤ M' → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ J : Ideal (𝓞 D.host.E), (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ∀ c ∈ J, ∃ c' ∈ PP.asIdeal, (c' : D.host.E) = D.sp.cm.sig (c : D.host.E)) → ∃ φ : (Fin (Vc D i).rank → La ⧸ (J • ⊤ : Submodule (𝓞 D.host.E) La)) → M', PhiIs R i M'.val.toRingHom t ι (J • ⊤) φ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hlev hvP i hV t La _ _ ι hι
  obtain ⟨M, hM, hv⟩ := exists_omega_field R.Pg (R.Q t)
  refine ⟨M, hM, fun M' hle hP J hJ => ?_⟩
  obtain ⟨-, e, he, -⟩ := hvP i t
  have hβ := GlobalTheory.StdFrameInv.isIntM_inv D i _ _ hV (hlev.βV i)
  have hi : ∀ x a, rowP (Wc D i) (R.βW i) e (ι x) a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun x a =>
    rowP_int _ _ _ (hlev.βW i) e _ he (fun PP h => hP PP (by simpa using h)) _
      (hι.2.le (LinearMap.mem_range_self ι x)) a
  refine ⟨fun q => ⟨_, hle (hv (Wc D i).rank (R.xiR t) (-1) fun PP => redM PP
    (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => ι (q b).out))⟩, e, he, fun x =>
    ⟨(redM_uMat (Vc D i) (Wc D i) hV.1 _ hβ (R.βW i) e (fun b => ι (x b)) fun b a => hi (x b) a).1, ?_⟩⟩
  exact omega_congr _ _ _ _ _ _ _ fun PP hPP => exists_datum (Vc D i) (Wc D i) hV.1 _ hβ (R.βW i) e ι hi J PP (hJ PP hPP) x _
    fun b => (Submodule.Quotient.eq _).1 (Quotient.out_eq _)

end GlobalTheory.LevelDatum
