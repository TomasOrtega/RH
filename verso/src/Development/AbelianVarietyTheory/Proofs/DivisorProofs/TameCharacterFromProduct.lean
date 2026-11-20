import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorResIEqResS
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnitChineseRemainder
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoActCompare.TameConj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeoActCompare
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions (idealHat CongMod)
open GlobalTheory.IdemSupport (mem_intAE_iff parts_cA finPart_cA_mem)

variable {D : D7}

/- English proof (translation)
The claim follows from `(Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective`.
-/
theorem swapAE_injective : Function.Injective (swapAE D) :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective

/- English proof (translation)
Rewrite `hy`, `hz`, the goal using `[mem_intAE_iff]`. Rewrite using `[RingHom.map_mul]`. Conclude with `mul_mem hy hz`.
-/
theorem mul_mem_intAE {y z : Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ intAE D) (hz : z ∈ intAE D) :
    y * z ∈ intAE D := by
  rw [mem_intAE_iff] at hy hz ⊢
  rw [RingHom.map_mul]
  exact mul_mem hy hz

/- English proof (translation)
The claim follows from `AddSubgroup.subset_closure ⟨1, one_mem (Formalism.UG.intAd D.host.F), a, rfl⟩`.
-/
theorem tmul_mem_intAE (a : 𝓞 D.host.E) : (1 : Af D.host.F) ⊗ₜ[D.host.F] (a : D.host.E) ∈ intAE D :=
  AddSubgroup.subset_closure ⟨1, one_mem (Formalism.UG.intAd D.host.F), a, rfl⟩

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem w hw`. Take `⟨b, hb, t, ht, rfl⟩` from `hw`. Conclude with `AddSubgroup.subset_closure ⟨b, hb, t * y, mul_mem_intAE ht hy, mul_assoc _ _ _⟩`. Consider the case `zero => rw [zero_mul]`.

Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb => rw [add_mul]`. Conclude with `add_mem ha hb`. Consider the case `neg a _ ha => rw [neg_mul]`. Conclude with `neg_mem ha`.
-/
theorem mul_mem_idealHat {I : Ideal (𝓞 D.host.E)} {y z : Af D.host.F ⊗[D.host.F] D.host.E}
    (hz : z ∈ idealHat D I) (hy : y ∈ intAE D) : z * y ∈ idealHat D I := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨b, hb, t, ht, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨b, hb, t * y, mul_mem_intAE ht hy, mul_assoc _ _ _⟩
  | zero => rw [zero_mul]; exact zero_mem _
  | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
  | neg a _ ha => rw [neg_mul]; exact neg_mem ha

/- English proof (translation)
Establish `hb : Function.Surjective (swapAE D)` using `(Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).surjective`. Proceed by induction on `hs using Submodule.span_induction with`. Consider the case `mem w hw`. Take `⟨b, hb, rfl⟩` from `hw`. Introduce `z hz`.

Use `AddSubgroup.subset_closure ⟨b, hb, 1, tmul_mem_intAE 1, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_one]`. Conclude with `swapAE_injective hz`. Consider the case `zero`. Introduce `z hz`.

Rewrite using `[show z = 0 from swapAE_injective (hz.trans (swapAE D).map_zero.symm)]`. Conclude with `zero_mem _`. Consider the case `add a b _ _ h1 h2`. Introduce `z hz`. Take `⟨p, hp⟩` from `hb (a : EAf D)`.

Take `⟨q, hq⟩` from `hb (b : EAf D)`. Rewrite using `[show z = p + q from swapAE_injective (by rw [RingHom.map_add, hp, hq]; exact hz)]`. Conclude with `add_mem (h1 p hp) (h2 q hq)`. Consider the case `smul a b _ h2`. Introduce `z hz`.

Take `⟨p, hp⟩` from `hb (a : EAf D)`. Take `⟨q, hq⟩` from `hb (b : EAf D)`. Rewrite using `[show z = q * p from swapAE_injective (by rw [RingHom.map_mul, hp, hq, mul_comm]; exact hz)]`. Conclude with `mul_mem_idealHat (h2 q hq) ((mem_intAE_iff p).2 (hp ▸ a.2))`.
-/
theorem mem_idealHat_of_idS {I : Ideal (𝓞 D.host.E)} {s : LatticeBasisLifts.OAf D} (hs : s ∈ Formalism.L2.DIV.idS D.host.F I) :
    ∀ z : Af D.host.F ⊗[D.host.F] D.host.E, swapAE D z = (s : EAf D) → z ∈ idealHat D I := by
  have hb : Function.Surjective (swapAE D) :=
    (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).surjective
  induction hs using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨b, hb, rfl⟩ := hw
    intro z hz
    refine AddSubgroup.subset_closure ⟨b, hb, 1, tmul_mem_intAE 1, ?_⟩
    rw [mul_one]
    exact swapAE_injective hz
  | zero =>
    intro z hz
    rw [show z = 0 from swapAE_injective (hz.trans (swapAE D).map_zero.symm)]
    exact zero_mem _
  | add a b _ _ h1 h2 =>
    intro z hz
    obtain ⟨p, hp⟩ := hb (a : EAf D)
    obtain ⟨q, hq⟩ := hb (b : EAf D)
    rw [show z = p + q from swapAE_injective (by rw [RingHom.map_add, hp, hq]; exact hz)]
    exact add_mem (h1 p hp) (h2 q hq)
  | smul a b _ h2 =>
    intro z hz
    obtain ⟨p, hp⟩ := hb (a : EAf D)
    obtain ⟨q, hq⟩ := hb (b : EAf D)
    rw [show z = q * p from swapAE_injective (by rw [RingHom.map_mul, hp, hq, mul_comm]; exact hz)]
    exact mul_mem_idealHat (h2 q hq) ((mem_intAE_iff p).2 (hp ▸ a.2))

/- English proof (translation)
The claim follows from `(H.bar_eq a).symm`.
-/
theorem bar_coe (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (a : 𝓞 D.host.E) :
    D.sp.cm.sig (a : D.host.E) = (H.bar a : D.host.E) := (H.bar_eq a).symm

/- English proof (translation)
Establish `: intAE D ≤ (intAE D).comap (sigR (Af D.host.F) D.sp.cm.sig).toAddMonoidHom`. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, x, rfl⟩`. Conclude with `AddSubgroup.subset_closure ⟨a, ha, H.bar x, congrArg (a ⊗ₜ[D.host.F] ·) (bar_coe H x)⟩`. Conclude with `this hz`.
-/
theorem sigR_mem_intAE {z : Af D.host.F ⊗[D.host.F] D.host.E} (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E)
    (hz : z ∈ intAE D) : sigR (Af D.host.F) D.sp.cm.sig z ∈ intAE D := by
  have : intAE D ≤ (intAE D).comap (sigR (Af D.host.F) D.sp.cm.sig).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, x, rfl⟩
    exact AddSubgroup.subset_closure ⟨a, ha, H.bar x, congrArg (a ⊗ₜ[D.host.F] ·) (bar_coe H x)⟩
  exact this hz

/- English proof (translation)
Rewrite using `[(parts_cA z).2]`. Establish `: idealHat D I ≤ (idealHat D J).comap (sigR (Af D.host.F) D.sp.cm.sig).toAddMonoidHom`. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨b, hb, y, hy, rfl⟩`. Use `AddSubgroup.subset_closure ⟨H.bar b, h b hb, _, sigR_mem_intAE H hy, ?_⟩` and prove the remaining obligations.

Use `((sigR (Af D.host.F) D.sp.cm.sig).map_mul _ _).trans (congrArg (· * _) ?_)` and prove the remaining obligations. Conclude with `congrArg ((1 : Af D.host.F) ⊗ₜ[D.host.F] ·) (bar_coe H b)`. Conclude with `this hz`.
-/
theorem cA_mem_idealHat (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) {I J : Ideal (𝓞 D.host.E)}
    (h : ∀ b ∈ I, H.bar b ∈ J) {z : AE D} (hz : finPart D z ∈ idealHat D I) :
    finPart D (cA D z) ∈ idealHat D J := by
  rw [(parts_cA z).2]
  have : idealHat D I ≤ (idealHat D J).comap (sigR (Af D.host.F) D.sp.cm.sig).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨b, hb, y, hy, rfl⟩
    refine AddSubgroup.subset_closure ⟨H.bar b, h b hb, _, sigR_mem_intAE H hy, ?_⟩
    refine ((sigR (Af D.host.F) D.sp.cm.sig).map_mul _ _).trans (congrArg (· * _) ?_)
    exact congrArg ((1 : Af D.host.F) ⊗ₜ[D.host.F] ·) (bar_coe H b)
  exact this hz

/- English proof (translation)
Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]`.
-/
theorem bar_bar (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (a : 𝓞 D.host.E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rfl`. Consider the case `tmul a x => exact congrArg (a ⊗ₜ[D.host.F] ·) (star_star x)`. Consider the case `add a b ha hb => rw [RingHom.map_add, RingHom.map_add, ha, hb]`.
-/
theorem cA_cA (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul a x => exact congrArg (a ⊗ₜ[D.host.F] ·) (star_star x)
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, ha, hb]

/- English proof (translation)
Establish `e1 : f X * f Xi = 1` using `by rw [← map_mul, hX, map_one]`. Establish `e2 : f (c X) * f (c Xi) = 1` using `by rw [← map_mul, ← map_mul, hX, map_one, map_one]`. Prove the components needed by the constructor for the conclusion. Establish `h6` using `hBA (X - 1) (by rwa [map_sub, map_one])`. Rewrite `h6` using `[map_sub, map_one, map_sub, map_one]`.

Establish `h8` using `hA _ (sub_mem h5 (hA _ h6 _ ha')) _ (hO _ h4)`. Use `h8 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_mul, map_mul]`. Take the linear combination `a' * e2`. Establish `h6` using `hAB (x * Xi - 1) (by`.

Use `hA _ (sub_mem h1 h2) _ h4 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_sub, map_mul, map_one]`. Take the linear combination `e1)`. Rewrite `h6` using `[map_sub, map_one, map_sub, map_one]`. Then use the resulting hypothesis.
-/
theorem conj_quot_congr {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (c : R →+* R) (O A B : AddSubgroup S)
    (hA : ∀ z ∈ A, ∀ y ∈ O, z * y ∈ A) (hO : ∀ z, f z ∈ O → f (c z) ∈ O)
    (hAB : ∀ z, f z ∈ A → f (c z) ∈ B) (hBA : ∀ z, f z ∈ B → f (c z) ∈ A) (x X Xi : R) (hX : X * Xi = 1)
    (a a' : S) (ha' : a' ∈ O) (h1 : f x - a ∈ A) (h2 : f X - a ∈ A) (h3 : f X - 1 ∈ B) (h4 : f Xi ∈ O)
    (h5 : f (c x) - a' ∈ A) : f (c (x * Xi)) - a' ∈ A ∧ f (c (x * Xi)) - 1 ∈ B := by
  have e1 : f X * f Xi = 1 := by rw [← map_mul, hX, map_one]
  have e2 : f (c X) * f (c Xi) = 1 := by rw [← map_mul, ← map_mul, hX, map_one, map_one]
  constructor
  · have h6 := hBA (X - 1) (by rwa [map_sub, map_one])
    rw [map_sub, map_one, map_sub, map_one] at h6
    have h8 := hA _ (sub_mem h5 (hA _ h6 _ ha')) _ (hO _ h4)
    convert h8 using 1
    rw [map_mul, map_mul]
    linear_combination a' * e2
  · have h6 := hAB (x * Xi - 1) (by
      convert hA _ (sub_mem h1 h2) _ h4 using 1
      rw [map_sub, map_mul, map_one]
      linear_combination e1)
    rwa [map_sub, map_one, map_sub, map_one] at h6

/- English proof (translation)
Use `⟨hx, (mem_intAE_iff _).2 (hu ▸ u.1.2), (mem_intAE_iff _).2 ?_⟩` and prove the remaining obligations. Establish `e1 : swapAE D (finPart D (x : AE D)) * swapAE D (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) = 1`. Rewrite using `[← RingHom.map_mul, ← RingHom.map_mul, Units.mul_inv, RingHom.map_one, RingHom.map_one]`. Establish `e2 : (((u⁻¹ : (LatticeBasisLifts.OAf D)ˣ) : LatticeBasisLifts.OAf D) : EAf D) * ((u : LatticeBasisLifts.OAf D) : EAf D) = 1` using `congrArg Subtype.val u.inv_mul`. Rewrite `e2` using `[hu]`.

Rewrite using `[← left_inv_eq_right_inv e2 e1]`. Conclude with `Subtype.property _`.
-/
theorem finUnit_of_unit {x : (AE D)ˣ} {u : (LatticeBasisLifts.OAf D)ˣ} (hx : infPart D (x : AE D) = 1)
    (hu : ((u : LatticeBasisLifts.OAf D) : EAf D) = swapAE D (finPart D (x : AE D))) : FinUnit x := by
  refine ⟨hx, (mem_intAE_iff _).2 (hu ▸ u.1.2), (mem_intAE_iff _).2 ?_⟩
  have e1 : swapAE D (finPart D (x : AE D)) * swapAE D (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) = 1 := by
    rw [← RingHom.map_mul, ← RingHom.map_mul, Units.mul_inv, RingHom.map_one, RingHom.map_one]
  have e2 : (((u⁻¹ : (LatticeBasisLifts.OAf D)ˣ) : LatticeBasisLifts.OAf D) : EAf D) * ((u : LatticeBasisLifts.OAf D) : EAf D) = 1 :=
    congrArg Subtype.val u.inv_mul
  rw [hu] at e2
  rw [← left_inv_eq_right_inv e2 e1]
  exact Subtype.property _

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, RingHom.map_mul, hx.1, hy.1, one_mul]`. Rewrite using `[Units.val_mul, RingHom.map_mul]`. Conclude with `mul_mem_intAE hx.2.1 hy.2.1`. Rewrite using `[mul_inv, Units.val_mul, RingHom.map_mul]`.

Conclude with `mul_mem_intAE hx.2.2 hy.2.2`.
-/
theorem FinUnit_mul {x y : (AE D)ˣ} (hx : FinUnit x) (hy : FinUnit y) : FinUnit (x * y) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Units.val_mul, RingHom.map_mul, hx.1, hy.1, one_mul]
  · rw [Units.val_mul, RingHom.map_mul]
    exact mul_mem_intAE hx.2.1 hy.2.1
  · rw [mul_inv, Units.val_mul, RingHom.map_mul]
    exact mul_mem_intAE hx.2.2 hy.2.2

/- English proof (translation)
Use `⟨?_, hx.2.2, hx.2.1⟩` and prove the remaining obligations. Establish `e : infPart D (x : AE D) * infPart D ((x⁻¹ : (AE D)ˣ) : AE D) = 1`. Rewrite using `[← RingHom.map_mul, Units.mul_inv, RingHom.map_one]`. Rewrite `e` using `[hx.1, one_mul]`. Then use the resulting hypothesis.
-/
theorem FinUnit_inv {x : (AE D)ˣ} (hx : FinUnit x) : FinUnit x⁻¹ := by
  refine ⟨?_, hx.2.2, hx.2.1⟩
  have e : infPart D (x : AE D) * infPart D ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    rw [← RingHom.map_mul, Units.mul_inv, RingHom.map_one]
  rwa [hx.1, one_mul] at e

/- English proof (translation)
Use `⟨?_, finPart_cA_mem hx.2.1, finPart_cA_mem hx.2.2⟩` and prove the remaining obligations. Conclude with `(parts_cA (x : AE D)).1.trans (by rw [hx.1, RingHom.map_one])`.
-/
theorem FinUnit_conj {x : (AE D)ˣ} (hx : FinUnit x) : FinUnit (Units.map (cA D).toMonoidHom x) := by
  refine ⟨?_, finPart_cA_mem hx.2.1, finPart_cA_mem hx.2.2⟩
  exact (parts_cA (x : AE D)).1.trans (by rw [hx.1, RingHom.map_one])

/- English proof (translation)
Take `⟨a, ha⟩` from `exists_sub_mem I hI s`. Use `⟨a, (resI_eq_mk_iff I hI s a).2 ha, mem_idealHat_of_idS ha _ ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.map_sub, ← hs]`. Both sides reduce to the same expression.
-/
theorem exists_congr {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥) (s : LatticeBasisLifts.OAf D)
    {z : Af D.host.F ⊗[D.host.F] D.host.E} (hs : (s : EAf D) = swapAE D z) :
    ∃ a : 𝓞 D.host.E, resI D.host.F I hI s = Ideal.Quotient.mk I a ∧
      z - (1 : Af D.host.F) ⊗ₜ[D.host.F] (a : D.host.E) ∈ idealHat D I := by
  obtain ⟨a, ha⟩ := exists_sub_mem I hI s
  refine ⟨a, (resI_eq_mk_iff I hI s a).2 ha, mem_idealHat_of_idS ha _ ?_⟩
  rw [RingHom.map_sub, ← hs]
  rfl

/- English proof (translation)
Establish `h : ∀ (v : (Formalism.L2.Herm.intAf F E)ˣ) (w : ↥Pg), Units.map (Ideal.Quotient.factor (hle w)).toMonoidHom (Units.map (resI F I hI).toMonoidHom v) = Units.map (Formalism.L2.DIV.resS F w.1).toMonoidHom v` using `fun v w => Units.ext (factor_resI_eq_resS hI w.1 (hle w) v.1)`. Simplify using `only [chiProd_apply, h, Units.coe_prod, map_prod, Finset.prod_mul_distrib, Finset.prod_inv_distrib]`.
-/
theorem chiProd_resI {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {I : Ideal (𝓞 E)} (hI : I ≠ ⊥) {Pg : Finset (Formalism.L2.DIV.Pl E)} (hle : ∀ w : ↥Pg, I ≤ w.1.asIdeal)
    {K : Type} [Field K] (σ : K →+* ℂ) (χ : ∀ w : ↥Pg, (Formalism.L2.DIV.kP w.1)ˣ →* Kˣ)
    (u ub : (Formalism.L2.Herm.intAf F E)ˣ) :
    ∏ w : ↥Pg, (σ ((χ w (Units.map (Formalism.L2.DIV.resS F w.1).toMonoidHom u) : Kˣ) : K))⁻¹ *
        σ ((χ w (Units.map (Formalism.L2.DIV.resS F w.1).toMonoidHom ub) : Kˣ) : K) =
      (σ ((chiProd hle χ (Units.map (resI F I hI).toMonoidHom u) : Kˣ) : K))⁻¹ *
        σ ((chiProd hle χ (Units.map (resI F I hI).toMonoidHom ub) : Kˣ) : K) := by
  have h : ∀ (v : (Formalism.L2.Herm.intAf F E)ˣ) (w : ↥Pg), Units.map (Ideal.Quotient.factor (hle w)).toMonoidHom
      (Units.map (resI F I hI).toMonoidHom v) = Units.map (Formalism.L2.DIV.resS F w.1).toMonoidHom v :=
    fun v w => Units.ext (factor_resI_eq_resS hI w.1 (hle w) v.1)
  simp only [chiProd_apply, h, Units.coe_prod, map_prod, Finset.prod_mul_distrib, Finset.prod_inv_distrib]

/- English proof (translation)
Establish `h4 : μ x * μ Y = μ X`. Rewrite using `[← map_mul, ← one_mul (μ X), ← h3, ← map_mul, mul_right_comm x, inv_mul_cancel_right]`. Establish `h5 : (μ x : ℂ) * μ Y = μ X` using `by rw [← Circle.coe_mul, h4]`. Rewrite using `[← eq_inv_of_mul_eq_one_right h1]`. Take the linear combination `t * h5 - (μ x : ℂ) * h2`.
-/
theorem circle_step {G : Type} [CommGroup G] (μ : G →* Circle) (x X Y : G) (s t : ℂ) (h1 : s * (μ X : ℂ) = 1)
    (h2 : t * (μ Y : ℂ) = 1) (h3 : μ (x * X⁻¹ * Y) = 1) : (μ x : ℂ) = s⁻¹ * t := by
  have h4 : μ x * μ Y = μ X := by
    rw [← map_mul, ← one_mul (μ X), ← h3, ← map_mul, mul_right_comm x, inv_mul_cancel_right]
  have h5 : (μ x : ℂ) * μ Y = μ X := by rw [← Circle.coe_mul, h4]
  rw [← eq_inv_of_mul_eq_one_right h1]
  linear_combination t * h5 - (μ x : ℂ) * h2

set_option maxHeartbeats 800000 in

/- English proof (translation)
Introduce `D H l Pg hle K _ σ μ χ hfix hT x u ub hx hu hub`. Establish `hM : l.Mb * l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≠ ⊥`. Rewrite using `[l.prod, Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]`. Use `l.three_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hI : l.Mb ≠ ⊥` using `fun h => hM (by rw [h, Ideal.bot_mul])`. Establish `hJ : l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≠ ⊥` using `fun h => hM (by rw [h, Ideal.mul_bot])`. Establish `hIJ : ∀ b ∈ l.Mb, H.bar b ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)` using `fun b hb => Ideal.mem_map_of_mem _ hb`. Establish `hJI : ∀ b ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E), H.bar b ∈ l.Mb` using `fun b hb => by`. Take `⟨c, hc, rfl⟩` from `(Ideal.mem_map_iff_of_surjective _ H.bar.surjective).1 hb`.

Conclude with `(bar_bar H c).symm ▸ hc`. Take `⟨a, ha, ha2⟩` from `exists_congr hI u.1 hu`. Take `⟨b, hb, hb2⟩` from `exists_congr hI ub.1 hub`. Take `⟨X, hX, hX1, hX2⟩` from `GlobalTheory.UnitResidue.exists_finUnit_congMod D _ _ hI hJ l.coprime a (ha ▸ (Units.map (resI D.host.F l.Mb hI).toMonoidHom u).isUnit)`. Establish `hxu` using `finUnit_of_unit hx hu`.

Take `⟨hY1, hY2⟩` from `conj_quot_congr (finPart D) (cA D) (intAE D) (idealHat D l.Mb) (idealHat D _) (fun z hz y hy => mul_mem_idealHat hz hy) (fun z hz => finPart_cA_mem hz) (fun z hz => cA_mem_idealHat H hIJ hz) (fun z hz => cA_mem_idealHat H hJI hz) x X (X⁻¹ : (AE D)ˣ) X.mul_inv _ _ (tmul_mem_intAE …`. Establish `h1` using `hT X hX a (Units.map (resI D.host.F l.Mb hI).toMonoidHom u) ha hX1 hX2`. Establish `h2` using `hT (Units.map (cA D).toMonoidHom (x * X⁻¹)) (FinUnit_conj (FinUnit_mul hxu (FinUnit_inv hX))) b (Units.map (resI D.host.F l.Mb hI).toMonoidHom ub) hb hY1 hY2`. Establish `h3` using `hfix (x * X⁻¹ * Units.map (cA D).toMonoidHom (x * X⁻¹)) (by show cA D (((x * X⁻¹ : (AE D)ˣ) : AE D) * cA D ((x * X⁻¹ : (AE D)ˣ) : AE D)) = ((x * X⁻¹ : (AE D)ˣ) : AE D) * cA D ((x * X⁻¹ : (AE D)ˣ) : AE D)`. Rewrite using `[RingHom.map_mul, cA_cA, mul_comm])`.

Conclude with `(circle_step μ x X _ _ _ h1 h2 h3).trans (chiProd_resI hI hle σ χ u ub).symm`.
-/
theorem isInvTame_of_half : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (hle : ∀ w : ↥Pg, l.Mb ≤ w.1.asIdeal) (K : Type) [Field K] (σ : K →+* ℂ) (μ : (AE D)ˣ →* Circle) (χ : ∀ w : ↥Pg, (Formalism.L2.DIV.kP w.1)ˣ →* Kˣ), (∀ x : (AE D)ˣ, cA D (x : AE D) = (x : AE D) → μ x = 1) → LevelLiftConditions.IsInvTame σ l.Mb (l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) μ (chiProd hle χ) → LatticeBasisLifts.IsInvTame σ Pg μ χ := by
  intro D H l Pg hle K _ σ μ χ hfix hT x u ub hx hu hub
  have hM : l.Mb * l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≠ ⊥ := by
    rw [l.prod, Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    have := l.three_le
    omega
  have hI : l.Mb ≠ ⊥ := fun h => hM (by rw [h, Ideal.bot_mul])
  have hJ : l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≠ ⊥ := fun h => hM (by rw [h, Ideal.mul_bot])
  have hIJ : ∀ b ∈ l.Mb, H.bar b ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) :=
    fun b hb => Ideal.mem_map_of_mem _ hb
  have hJI : ∀ b ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E), H.bar b ∈ l.Mb := fun b hb => by
    obtain ⟨c, hc, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ H.bar.surjective).1 hb
    exact (bar_bar H c).symm ▸ hc
  obtain ⟨a, ha, ha2⟩ := exists_congr hI u.1 hu
  obtain ⟨b, hb, hb2⟩ := exists_congr hI ub.1 hub
  obtain ⟨X, hX, hX1, hX2⟩ := GlobalTheory.UnitResidue.exists_finUnit_congMod D _ _ hI hJ l.coprime a
    (ha ▸ (Units.map (resI D.host.F l.Mb hI).toMonoidHom u).isUnit)
  have hxu := finUnit_of_unit hx hu
  obtain ⟨hY1, hY2⟩ := conj_quot_congr (finPart D) (cA D) (intAE D) (idealHat D l.Mb) (idealHat D _)
    (fun z hz y hy => mul_mem_idealHat hz hy) (fun z hz => finPart_cA_mem hz)
    (fun z hz => cA_mem_idealHat H hIJ hz) (fun z hz => cA_mem_idealHat H hJI hz) x X (X⁻¹ : (AE D)ˣ) X.mul_inv _ _
    (tmul_mem_intAE b) ha2 hX1 hX2 hX.2.2 hb2
  have h1 := hT X hX a (Units.map (resI D.host.F l.Mb hI).toMonoidHom u) ha hX1 hX2
  have h2 := hT (Units.map (cA D).toMonoidHom (x * X⁻¹)) (FinUnit_conj (FinUnit_mul hxu (FinUnit_inv hX))) b
    (Units.map (resI D.host.F l.Mb hI).toMonoidHom ub) hb hY1 hY2
  have h3 := hfix (x * X⁻¹ * Units.map (cA D).toMonoidHom (x * X⁻¹)) (by
    show cA D (((x * X⁻¹ : (AE D)ˣ) : AE D) * cA D ((x * X⁻¹ : (AE D)ˣ) : AE D)) =
      ((x * X⁻¹ : (AE D)ˣ) : AE D) * cA D ((x * X⁻¹ : (AE D)ˣ) : AE D)
    rw [RingHom.map_mul, cA_cA, mul_comm])
  exact (circle_step μ x X _ _ _ h1 h2 h3).trans (chiProd_resI hI hle σ χ u ub).symm

end GlobalTheory.GeoActCompare.TameConj
