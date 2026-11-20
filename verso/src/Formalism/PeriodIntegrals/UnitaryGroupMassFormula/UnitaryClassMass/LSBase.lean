import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.LSSkeleton
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.UJClassMassOfDeep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.HermASingleLeft
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.RationalPointsDense

open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence PI.UnitaryGroupMassFormula.UJClassFin
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section Base

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
variable {M : ℕ}

/- English proof (translation)
Use `show ∑ i, (x + y) i • b i ∈ L0`. Simplify using `only [Pi.add_apply, add_smul, Finset.sum_add_distrib]`. Conclude with `L0.add_mem hx hy`.
-/
theorem crd_add (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) {x y : Fin M → E}
    (hx : x ∈ crdOf b L0) (hy : y ∈ crdOf b L0) : x + y ∈ crdOf b L0 := by
  show ∑ i, (x + y) i • b i ∈ L0
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  exact L0.add_mem hx hy

/- English proof (translation)
Use `show ∑ i, (0 : Fin M → E) i • b i ∈ L0`. Simplify using the standard rewrite rules.
-/
theorem crd_zero (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) : (0 : Fin M → E) ∈ crdOf b L0 := by
  show ∑ i, (0 : Fin M → E) i • b i ∈ L0
  simp

/- English proof (translation)
Use `show ∑ i, (-x) i • b i ∈ L0`. Simplify using `only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]`. Conclude with `L0.neg_mem hx`.
-/
theorem crd_neg (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) {x : Fin M → E}
    (hx : x ∈ crdOf b L0) : -x ∈ crdOf b L0 := by
  show ∑ i, (-x) i • b i ∈ L0
  simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]
  exact L0.neg_mem hx

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `crd_add b L0 hx (crd_neg b L0 hy)`.
-/
theorem crd_sub (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) {x y : Fin M → E}
    (hx : x ∈ crdOf b L0) (hy : y ∈ crdOf b L0) : x - y ∈ crdOf b L0 := by
  rw [sub_eq_add_neg]; exact crd_add b L0 hx (crd_neg b L0 hy)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => rw [Finset.sum_empty]`. Conclude with `crd_zero b L0`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`.

Conclude with `crd_add b L0 (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))`.
-/
theorem crd_sum (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) {ι : Type*} (s : Finset ι)
    (f : ι → Fin M → E) (hf : ∀ i ∈ s, f i ∈ crdOf b L0) : ∑ i ∈ s, f i ∈ crdOf b L0 := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact crd_zero b L0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact crd_add b L0 (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Use `show ∑ i, (e • x) i • b i ∈ L0`. Establish `: ∑ i, (e • x) i • b i = e • ∑ i, x i • b i`. Simplify using `[Finset.smul_sum, smul_smul]`. Rewrite using `[this]`. Conclude with `int_smul_mem L0 he hx`.
-/
theorem crd_smul (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) {e : E} (he : IsIntegral ℤ e)
    {x : Fin M → E} (hx : x ∈ crdOf b L0) : e • x ∈ crdOf b L0 := by
  show ∑ i, (e • x) i • b i ∈ L0
  have : ∑ i, (e • x) i • b i = e • ∑ i, x i • b i := by
    simp [Finset.smul_sum, smul_smul]
  rw [this]
  exact int_smul_mem L0 he hx

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[vinc, map_mul]`.
-/
theorem vinc_smul (c : E) (x : Fin M → E) : vinc (F := F) (c • x) = inclR (F := F) (Af F) c • vinc (F := F) x := by
  funext i
  simp [vinc, map_mul]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [vinc, Pi.smul_apply, inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply, TensorProduct.tmul_smul]`.
-/
theorem vinc_Fsmul (c : F) (x : Fin M → E) : vinc (F := F) (c • x) = c • vinc (F := F) x := by
  funext i
  simp only [vinc, Pi.smul_apply, inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply, TensorProduct.tmul_smul]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[vinc]`.
-/
theorem vinc_add (x y : Fin M → E) : vinc (F := F) (x + y) = vinc x + vinc y := by
  funext i; simp [vinc]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[vinc]`.
-/
theorem vinc_sub (x y : Fin M → E) : vinc (F := F) (x - y) = vinc x - vinc y := by
  funext i; simp [vinc]

/- English proof (translation)
The claim follows from `AddSubgroup.subset_closure ⟨1, intAf_one, x, hx, rfl⟩`.
-/
theorem vinc_mem (L : Set (Fin M → E)) {x : Fin M → E} (hx : x ∈ L) : vinc (F := F) x ∈ latHat F E L :=
  AddSubgroup.subset_closure ⟨1, intAf_one, x, hx, rfl⟩

/- English proof (translation)
Proceed by induction on `ho using AddSubgroup.closure_induction with`. Consider the case `mem o ho`. Take `⟨a, ha, e, he, rfl⟩` from `ho`. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`.

Take `⟨a', ha', x, hx, rfl⟩` from `hy`. Use `AddSubgroup.subset_closure ⟨a * a', intAf_mul ha ha', e • x, crd_smul b L0 he hx, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using `[Algebra.TensorProduct.tmul_mul_tmul]`. Consider the case `zero => rw [smul_zero]`.

Conclude with `zero_mem _`. Consider the case `add y y' _ _ h1 h2 => rw [smul_add]`. Conclude with `add_mem h1 h2`. Consider the case `neg y _ h1 => rw [smul_neg]`. Conclude with `neg_mem h1`.

Consider the case `zero => rw [zero_smul]`. Conclude with `zero_mem _`. Consider the case `add o o' _ _ h1 h2 => rw [add_smul]`. Conclude with `add_mem h1 h2`. Consider the case `neg o _ h1 => rw [neg_smul]`.

Conclude with `neg_mem h1`.
-/
theorem latHat_Oh_smul (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) {o : Af F ⊗[F] E}
    (ho : o ∈ Oh F E) {y : Fin M → Af F ⊗[F] E} (hy : y ∈ latHat F E (crdOf b L0)) :
    o • y ∈ latHat F E (crdOf b L0) := by
  induction ho using AddSubgroup.closure_induction with
  | mem o ho =>
    obtain ⟨a, ha, e, he, rfl⟩ := ho
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a', ha', x, hx, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a * a', intAf_mul ha ha', e • x, crd_smul b L0 he hx, ?_⟩
      funext i
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    | zero => rw [smul_zero]; exact zero_mem _
    | add y y' _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
    | neg y _ h1 => rw [smul_neg]; exact neg_mem h1
  | zero => rw [zero_smul]; exact zero_mem _
  | add o o' _ _ h1 h2 => rw [add_smul]; exact add_mem h1 h2
  | neg o _ h1 => rw [neg_smul]; exact neg_mem h1

/- English proof (translation)
The claim follows from `latHat_Oh_smul b L0 (incl_mem_Oh he) hy`.
-/
theorem latHat_incl_smul (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) {e : E}
    (he : IsIntegral ℤ e) {y : Fin M → Af F ⊗[F] E} (hy : y ∈ latHat F E (crdOf b L0)) :
    inclR (F := F) (Af F) e • y ∈ latHat F E (crdOf b L0) :=
  latHat_Oh_smul b L0 (incl_mem_Oh he) hy

end Base

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hτ hs hnd hL hsig`. Use `set L := crdOf b L0 with hLdef`. Take `⟨⟨c1, hc1, hup⟩, ⟨c2, hc2, hlow⟩⟩` from `crdBounds F E V M b L0 hL`. Take `⟨u, hu, hu'⟩` from `up_nat L ⟨c1, hc1, hup⟩`. Take `⟨k, hk, hk'⟩` from `low_nat L ⟨c2, hc2, hlow⟩`.

Establish `hNpos : 0 < u * k` using `Nat.mul_pos hu hk`. Establish `hNL : ∀ z : Fin M → E, vinc (F` using `F) z ∈ latHat F E L → (((u * k : ℕ) : F)) • z ∈ L := by`. Introduce `z hz`. Establish `hi : ∀ i, IsIntegral ℤ (u • z i)`. Introduce `i`.

Apply `oh_inter (F := F)` to reduce the goal to its premises. Use `up_Oh L hu' hz i` as an intermediate fact. Simplify `this` using `[vinc, map_nsmul]`. Establish `e : (((u * k : ℕ) : F)) • z = ∑ i, Pi.single i ((k : F) • (u • z i))`. Use function extensionality and compare the values at `j`.

Simplify using `only [Finset.sum_apply, Pi.single_apply, Pi.smul_apply, Nat.cast_mul]`. Simplify using `only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Nat.cast_smul_eq_nsmul]`. Rewrite using `[mul_comm, mul_smul]`. Rewrite using `[Nat.cast_smul_eq_nsmul F, Nat.cast_smul_eq_nsmul F]`. Rewrite using `[e]`.

Conclude with `crd_sum b L0 _ _ fun i _ => hk' i _ (hi i)`. Establish `hD : ∀ y ∈ latHat F E L, ∃ l ∈ L, ∃ y' ∈ latHat F E L, y = vinc (F` using `F) l + (u * k) • y' := by`. Introduce `y hy`. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`.

Take `⟨a, ha, x, hx, rfl⟩` from `hy`. Take `⟨e, o, ho, hae⟩` from `approx (E := E) (u * k) hNpos (a ⊗ₜ[F] (1 : E))`. Establish `he : IsIntegral ℤ e`. Apply `oh_inter (F := F)` to reduce the goal to its premises. Establish `: inclR (Af F) e = a ⊗ₜ[F] (1 : E) - (u * k) • o` using `by rw [hae]; abel`.

Rewrite using `[this]`. Conclude with `sub_mem (tmul_mem_Oh ha isIntegral_one) (AddSubgroup.nsmul_mem _ ho _)`. Use `⟨e • x, crd_smul b L0 he hx, o • vinc (F := F) x, latHat_Oh_smul b L0 ho (vinc_mem L hx), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Establish `e1 : a ⊗ₜ[F] x i = (a ⊗ₜ[F] (1 : E)) * inclR (Af F) (x i)`.

Simplify using `[inclR, Algebra.TensorProduct.tmul_mul_tmul]`. Rewrite using `[e1, hae]`. Simplify using `only [vinc, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_mul, add_mul, smul_mul_assoc]`. Consider the case `zero => exact ⟨0, crd_zero b L0, 0, zero_mem _, by funext i; simp [vinc]⟩`. Consider the case `add y z _ _ h1 h2`.

Take `⟨l, hl, y', hy', e1⟩` from `h1`. Take `⟨l', hl', z', hz', e2⟩` from `h2`. Use `⟨l + l', crd_add b L0 hl hl', y' + z', add_mem hy' hz', ?_⟩` and prove the remaining obligations. Rewrite using `[e1, e2, vinc_add, smul_add]`. Normalize the expressions using the abelian group laws.

Consider the case `neg y _ h1`. Take `⟨l, hl, y', hy', e1⟩` from `h1`. Use `⟨-l, crd_neg b L0 hl, -y', neg_mem hy', ?_⟩` and prove the remaining obligations. Rewrite using `[e1, smul_neg, neg_add]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Simplify using `[vinc]`. Use extensionality with `x`. Simplify using `only [abelian₂, Set.mem_ofPred_eq, inv_one, finMat_one, Matrix.one_mulVec]`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Take `⟨l, hl, y', hy', e⟩` from `hD _ hx`. Use `set z : Fin M → E := (((u * k : ℕ) : F))⁻¹ • (x - l) with hz`. Establish `hNF : (((u * k : ℕ) : F)) ≠ 0` using `by exact_mod_cast hNpos.ne'`. Establish `hvz : vinc (F` using `F) z = y' := by`.

Rewrite using `[hz, vinc_Fsmul, vinc_sub, e, add_sub_cancel_left, ← Nat.cast_smul_eq_nsmul F, smul_smul, inv_mul_cancel₀ hNF, one_smul]`. Establish `h1` using `hNL z (by rw [hvz]; exact hy')`. Establish `h2 : (((u * k : ℕ) : F)) • z = x - l`. Rewrite using `[hz, smul_smul, mul_inv_cancel₀ hNF, one_smul]`. Rewrite `h1` using `[h2]`.

Use `crd_add b L0 h1 hl` as an intermediate fact. Simplify using `using this`. Introduce `hx`. Conclude with `vinc_mem L hx`.
-/
theorem lsOne : LSOne := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hτ hs hnd hL hsig
  set L := crdOf b L0 with hLdef
  obtain ⟨⟨c1, hc1, hup⟩, ⟨c2, hc2, hlow⟩⟩ := crdBounds F E V M b L0 hL
  obtain ⟨u, hu, hu'⟩ := up_nat L ⟨c1, hc1, hup⟩
  obtain ⟨k, hk, hk'⟩ := low_nat L ⟨c2, hc2, hlow⟩
  have hNpos : 0 < u * k := Nat.mul_pos hu hk

  have hNL : ∀ z : Fin M → E, vinc (F := F) z ∈ latHat F E L → (((u * k : ℕ) : F)) • z ∈ L := by
    intro z hz
    have hi : ∀ i, IsIntegral ℤ (u • z i) := by
      intro i
      apply oh_inter (F := F)
      have := up_Oh L hu' hz i
      simpa [vinc, map_nsmul] using this
    have e : (((u * k : ℕ) : F)) • z = ∑ i, Pi.single i ((k : F) • (u • z i)) := by
      funext j
      simp only [Finset.sum_apply, Pi.single_apply, Pi.smul_apply, Nat.cast_mul]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Nat.cast_smul_eq_nsmul]
      rw [mul_comm, mul_smul]
      rw [Nat.cast_smul_eq_nsmul F, Nat.cast_smul_eq_nsmul F]
    rw [e]
    exact crd_sum b L0 _ _ fun i _ => hk' i _ (hi i)

  have hD : ∀ y ∈ latHat F E L, ∃ l ∈ L, ∃ y' ∈ latHat F E L, y = vinc (F := F) l + (u * k) • y' := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      obtain ⟨e, o, ho, hae⟩ := approx (E := E) (u * k) hNpos (a ⊗ₜ[F] (1 : E))
      have he : IsIntegral ℤ e := by
        apply oh_inter (F := F)
        have : inclR (Af F) e = a ⊗ₜ[F] (1 : E) - (u * k) • o := by rw [hae]; abel
        rw [this]
        exact sub_mem (tmul_mem_Oh ha isIntegral_one) (AddSubgroup.nsmul_mem _ ho _)
      refine ⟨e • x, crd_smul b L0 he hx, o • vinc (F := F) x, latHat_Oh_smul b L0 ho (vinc_mem L hx), ?_⟩
      funext i
      have e1 : a ⊗ₜ[F] x i = (a ⊗ₜ[F] (1 : E)) * inclR (Af F) (x i) := by
        simp [inclR, Algebra.TensorProduct.tmul_mul_tmul]
      rw [e1, hae]
      simp only [vinc, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_mul, add_mul, smul_mul_assoc]
    | zero => exact ⟨0, crd_zero b L0, 0, zero_mem _, by funext i; simp [vinc]⟩
    | add y z _ _ h1 h2 =>
      obtain ⟨l, hl, y', hy', e1⟩ := h1
      obtain ⟨l', hl', z', hz', e2⟩ := h2
      refine ⟨l + l', crd_add b L0 hl hl', y' + z', add_mem hy' hz', ?_⟩
      rw [e1, e2, vinc_add, smul_add]; abel
    | neg y _ h1 =>
      obtain ⟨l, hl, y', hy', e1⟩ := h1
      refine ⟨-l, crd_neg b L0 hl, -y', neg_mem hy', ?_⟩
      rw [e1, smul_neg, neg_add]
      congr 1
      funext i; simp [vinc]
  ext x
  simp only [abelian₂, Set.mem_ofPred_eq, inv_one, finMat_one, Matrix.one_mulVec]
  constructor
  · intro hx
    obtain ⟨l, hl, y', hy', e⟩ := hD _ hx
    set z : Fin M → E := (((u * k : ℕ) : F))⁻¹ • (x - l) with hz
    have hNF : (((u * k : ℕ) : F)) ≠ 0 := by exact_mod_cast hNpos.ne'
    have hvz : vinc (F := F) z = y' := by
      rw [hz, vinc_Fsmul, vinc_sub, e, add_sub_cancel_left, ← Nat.cast_smul_eq_nsmul F, smul_smul,
        inv_mul_cancel₀ hNF, one_smul]
    have h1 := hNL z (by rw [hvz]; exact hy')
    have h2 : (((u * k : ℕ) : F)) • z = x - l := by
      rw [hz, smul_smul, mul_inv_cancel₀ hNF, one_smul]
    rw [h2] at h1
    have := crd_add b L0 h1 hl
    simpa using this
  · intro hx
    exact vinc_mem L hx

end PI.UnitaryGroupMassFormula.UJClassMass
