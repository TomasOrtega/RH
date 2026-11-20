import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ApartOfNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtPLoc
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open scoped TensorProduct

/- English proof (translation)
Introduce `hQ hT hI p _ E _ _ _`. Take `⟨Q⟩` from `hQ p`. Take `⟨ι, h1, h2, h3⟩` from `hT E`. Take `⟨e, he, he'⟩` from `hI p E`. Set `M : AfQ ⊗[ℚ] E →ₐ[ℚ] AfP p ⊗[ℚ] E` to `Algebra.TensorProduct.map Q.ρ.toRatAlgHom (AlgHom.id ℚ E)`.

Establish `hM : ∀ (a : AfQ) (x : E), M (a ⊗ₜ x) = Q.ρ a ⊗ₜ x` using `fun a x => rfl`. Establish `hρe : Q.ρ e = 0` using `(Q.ker e).2 fun v hv => (he v).2 hv`. Establish `hιa : ∀ a : AfQ, ι (a ⊗ₜ 1) = finiteAdeleMap ℚ E a` using `fun a => by`. Rewrite using `[h1, map_one, mul_one]`. Establish `hιE : ∀ x : E, ι (1 ⊗ₜ x) = algebraMap E (Af E) x` using `fun x => by`.

Rewrite using `[h1, map_one, one_mul]`. Establish `hMker : ∀ y, M y = 0 → (e ⊗ₜ[ℚ] (1 : E)) * y = y`. Introduce `y hy`. Set `b` to `Module.finBasis ℚ E`. Take `⟨c, rfl⟩` from `TensorProduct.eq_repr_basis_right b y`.

Establish `hc0 : (c.mapRange Q.ρ (map_zero _)).sum (fun i m => m ⊗ₜ[ℚ] b i) = 0`. Rewrite using `[Finsupp.sum_mapRange_index (by simp)]`. Rewrite using `[← hy, Finsupp.sum, Finsupp.sum, map_sum]`. Both sides reduce to the same expression. Establish `hc` using `TensorProduct.sum_tmul_basis_right_eq_zero b _ hc0`.

Establish `hci : ∀ i, e * c i = c i`. Introduce `i`. Establish `hi : Q.ρ (c i) = 0`. Use `DFunLike.congr_fun hc i` as an intermediate fact. Simplify using `using this`.

Establish `hv` using `(Q.ker (c i)).1 hi`. Use `Subtype.ext (funext fun v => ?_)` and prove the remaining obligations. Distinguish the cases in `hp : (p : 𝓞 ℚ) ∈ v.asIdeal`. Use `show e v * c i v = c i v`. Rewrite using `[(he v).1 hp, one_mul]`.

Use `show e v * c i v = c i v`. Rewrite using `[hv v hp, mul_zero]`. Rewrite using `[Finsupp.sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, hci]`.

Establish `hιe : ι (e ⊗ₜ 1) = finiteAdeleMap ℚ E e` using `hιa e`. Establish `hMe : M (e ⊗ₜ 1) = 0` using `by rw [hM, hρe, TensorProduct.zero_tmul]`. Establish `hMker' : ∀ x : Af E, M (ι.symm x) = 0 ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → pLoc E w x = 0`. Introduce `x`. Prove the components needed by the constructor for the conclusion.

Introduce `h w hw`. Establish `h'` using `congrArg ι (hMker _ h)`. Rewrite `h'` using `[map_mul, hιe, ι.apply_symm_apply]`. Rewrite using `[← h', map_mul, (he' w).2 hw, zero_mul]`. Introduce `h`.

Establish `hx : finiteAdeleMap ℚ E e * x = x`. Use `GlobalTheory.EulerTw.pLoc_ext E fun w => ?_` and prove the remaining obligations. Distinguish the cases in `hp : (p : 𝓞 E) ∈ w.asIdeal`. Rewrite using `[map_mul, (he' w).1 hp, one_mul]`. Rewrite using `[map_mul, (he' w).2 hp, zero_mul, h w hp]`.

Rewrite using `[← hx, ← hιe, map_mul ι.symm, ι.symm_apply_apply, map_mul, hMe, zero_mul]`. Establish `hgen : ∀ (a : AfP p) (c : 𝓞 E), IsIntAf a → ∃ y ∈ AddSubgroup.closure {y : AfQ ⊗[ℚ] E | ∃ (a : AfQ) (x : 𝓞 E), (∀ v : Plc ℚ, Valued.v (a v) ≤ 1) ∧ y = a ⊗ₜ (x : E)}, M y = a ⊗ₜ (c : E)`. Introduce `a c ha`. Take `⟨b, rfl⟩` from `Q.surj a`. Establish `hb` using `(Q.int b).1 ha`.

Use `⟨((1 - e) * b) ⊗ₜ (c : E), AddSubgroup.subset_closure ⟨_, c, ?_, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce `v`. Distinguish the cases in `hp : (p : 𝓞 ℚ) ∈ v.asIdeal`. Establish `: ((1 - e) * b) v = (1 - e v) * b v` using `rfl`. Rewrite using `[this, (he v).1 hp, sub_self, zero_mul, map_zero]`.

Conclude with `zero_le'`. Establish `: ((1 - e) * b) v = (1 - e v) * b v` using `rfl`. Rewrite using `[this, (he v).2 hp, sub_zero, one_mul]`. Conclude with `hb v hp`. Rewrite using `[hM, map_mul, map_sub, map_one, hρe, sub_zero, one_mul]`.

Establish `hMs : Function.Surjective M`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, map_zero _⟩`. Consider the case `tmul a x`.

Take `⟨b, rfl⟩` from `Q.surj a`. Conclude with `⟨b ⊗ₜ x, rfl⟩`. Consider the case `add u v hu hv`. Take `⟨u', rfl⟩` from `hu`. Take `⟨v', rfl⟩` from `hv`.

Conclude with `⟨u' + v', map_add _ _ _⟩`. Establish `hO : ∀ z ∈ OHat p E, ∃ y ∈ AddSubgroup.closure {y : AfQ ⊗[ℚ] E | ∃ (a : AfQ) (x : 𝓞 E), (∀ v : Plc ℚ, Valued.v (a v) ≤ 1) ∧ y = a ⊗ₜ (x : E)}, M y = z`. Introduce `z hz`. Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`.

Take `⟨a, c, ha, rfl⟩` from `hz`. Conclude with `hgen a c ha`. Consider the case `zero => exact ⟨0, zero_mem _, map_zero _⟩`. Consider the case `add u v _ _ hu hv`. Take `⟨u', hu', rfl⟩` from `hu`.

Take `⟨v', hv', rfl⟩` from `hv`. Conclude with `⟨u' + v', add_mem hu' hv', map_add _ _ _⟩`. Consider the case `neg u _ hu`. Take `⟨u', hu', rfl⟩` from `hu`. Conclude with `⟨-u', neg_mem hu', map_neg _ _⟩`.

Establish `hC : ∀ y ∈ AddSubgroup.closure {y : AfQ ⊗[ℚ] E | ∃ (a : AfQ) (x : 𝓞 E), (∀ v : Plc ℚ, Valued.v (a v) ≤ 1) ∧ y = a ⊗ₜ (x : E)}, M y ∈ OHat p E`. Introduce `y hy`. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨a, c, ha, rfl⟩` from `hy`.

Conclude with `AddSubgroup.subset_closure ⟨Q.ρ a, c, (Q.int a).2 fun v _ => ha v, rfl⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add u v _ _ hu hv => rw [map_add]`. Conclude with `add_mem hu hv`.

Consider the case `neg u _ hu => rw [map_neg]`. Conclude with `neg_mem hu`. Conclude with `⟨{ toAdQ := Q Φ := (M : AfQ ⊗[ℚ] E →+* AfP p ⊗[ℚ] E).comp (ι.symm : Af E →+* AfQ ⊗[ℚ] E) Φ_E := fun x => by show M (ι.symm _) = _`. Rewrite using `[← hιE, ι.symm_apply_apply, hM, map_one]`. Use `Φ_Q := fun a => by show M (ι.symm _) = _`.

Rewrite using `[← hιa, ι.symm_apply_apply, hM]`. Use `Φ_surj := fun z => by`. Take `⟨y, rfl⟩` from `hMs z`. Use `⟨ι y, ?_⟩` and prove the remaining obligations. Use `show M (ι.symm (ι y)) = _`.

Rewrite using `[ι.symm_apply_apply]`. Use `Φ_ker := hMker'`. Use `Φ_int := fun x => by show M (ι.symm x) ∈ OHat p E ↔ _`. Prove the components needed by the constructor for the conclusion. Introduce `hx w hw`.

Take `⟨y, hy, hyz⟩` from `hO _ hx`. Establish `hd : M (ι.symm (x - ι y)) = 0`. Rewrite using `[map_sub, map_sub, ι.symm_apply_apply, hyz, sub_self]`. Establish `h0` using `(hMker' _).1 hd w hw`. Rewrite `h0` using `[map_sub, sub_eq_zero]`.

Rewrite using `[h0]`. Conclude with `(h2 y).1 hy w`. Introduce `hx`. Establish `hz : M (ι.symm (finiteAdeleMap ℚ E e * x)) = 0`. Rewrite using `[← hιe, map_mul ι.symm, ι.symm_apply_apply, map_mul, hMe, zero_mul]`.

Establish `hi : ι.symm (x - finiteAdeleMap ℚ E e * x) ∈ AddSubgroup.closure {y : AfQ ⊗[ℚ] E | ∃ (a : AfQ) (x : 𝓞 E), (∀ v : Plc ℚ, Valued.v (a v) ≤ 1) ∧ y = a ⊗ₜ (x : E)}`. Use `(h2 _).2 fun w => ?_` and prove the remaining obligations. Rewrite using `[ι.apply_symm_apply, map_sub, map_mul]`. Distinguish the cases in `hp : (p : 𝓞 E) ∈ w.asIdeal`. Rewrite using `[(he' w).1 hp, one_mul, sub_self, map_zero]`.

Conclude with `zero_le'`. Rewrite using `[(he' w).2 hp, zero_mul, sub_zero]`. Conclude with `hx w hp`. Use `hC _ hi` as an intermediate fact. Rewrite `this` using `[map_sub, map_sub, hz, sub_zero]`. Then use the resulting hypothesis.

Use `Φ_conj := fun x => by show M (ι.symm (conjFin (conjE E) x)) = conjT E (AfP p) (M (ι.symm x))`. Take `⟨y, rfl⟩` from `ι.surjective x`. Rewrite using `[ι.symm_apply_apply]`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a z`. Rewrite using `[h1, map_mul, h3, conjFin_algebraMap, ← h1, ι.symm_apply_apply, hM, hM, conjT_tmul]`. Both sides reduce to the same expression. Consider the case `add u v hu hv`. Simplify using `only [map_add, hu, hv] }⟩`.
-/
theorem UpperTheory.Gal.W2.Seed.pAdTEx :
    AdQEx → AdTensor → IdemP → AdTEx := by
  intro hQ hT hI p _ E _ _ _
  obtain ⟨Q⟩ := hQ p
  obtain ⟨ι, h1, h2, h3⟩ := hT E
  obtain ⟨e, he, he'⟩ := hI p E
  let M : AfQ ⊗[ℚ] E →ₐ[ℚ] AfP p ⊗[ℚ] E :=
    Algebra.TensorProduct.map Q.ρ.toRatAlgHom (AlgHom.id ℚ E)
  have hM : ∀ (a : AfQ) (x : E), M (a ⊗ₜ x) = Q.ρ a ⊗ₜ x := fun a x => rfl
  have hρe : Q.ρ e = 0 := (Q.ker e).2 fun v hv => (he v).2 hv
  have hιa : ∀ a : AfQ, ι (a ⊗ₜ 1) = finiteAdeleMap ℚ E a := fun a => by
    rw [h1, map_one, mul_one]
  have hιE : ∀ x : E, ι (1 ⊗ₜ x) = algebraMap E (Af E) x := fun x => by
    rw [h1, map_one, one_mul]

  have hMker : ∀ y, M y = 0 → (e ⊗ₜ[ℚ] (1 : E)) * y = y := by
    intro y hy
    let b := Module.finBasis ℚ E
    obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_right b y
    have hc0 : (c.mapRange Q.ρ (map_zero _)).sum (fun i m => m ⊗ₜ[ℚ] b i) = 0 := by
      rw [Finsupp.sum_mapRange_index (by simp)]
      rw [← hy, Finsupp.sum, Finsupp.sum, map_sum]
      rfl
    have hc := TensorProduct.sum_tmul_basis_right_eq_zero b _ hc0
    have hci : ∀ i, e * c i = c i := by
      intro i
      have hi : Q.ρ (c i) = 0 := by
        have := DFunLike.congr_fun hc i
        simpa using this
      have hv := (Q.ker (c i)).1 hi
      refine Subtype.ext (funext fun v => ?_)
      by_cases hp : (p : 𝓞 ℚ) ∈ v.asIdeal
      · show e v * c i v = c i v
        rw [(he v).1 hp, one_mul]
      · show e v * c i v = c i v
        rw [hv v hp, mul_zero]
    rw [Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hci]

  have hιe : ι (e ⊗ₜ 1) = finiteAdeleMap ℚ E e := hιa e
  have hMe : M (e ⊗ₜ 1) = 0 := by rw [hM, hρe, TensorProduct.zero_tmul]
  have hMker' : ∀ x : Af E, M (ι.symm x) = 0 ↔
      ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → pLoc E w x = 0 := by
    intro x
    constructor
    · intro h w hw
      have h' := congrArg ι (hMker _ h)
      rw [map_mul, hιe, ι.apply_symm_apply] at h'
      rw [← h', map_mul, (he' w).2 hw, zero_mul]
    · intro h
      have hx : finiteAdeleMap ℚ E e * x = x := by
        refine GlobalTheory.EulerTw.pLoc_ext E fun w => ?_
        by_cases hp : (p : 𝓞 E) ∈ w.asIdeal
        · rw [map_mul, (he' w).1 hp, one_mul]
        · rw [map_mul, (he' w).2 hp, zero_mul, h w hp]
      rw [← hx, ← hιe, map_mul ι.symm, ι.symm_apply_apply, map_mul, hMe, zero_mul]
  have hgen : ∀ (a : AfP p) (c : 𝓞 E), IsIntAf a →
      ∃ y ∈ AddSubgroup.closure {y : AfQ ⊗[ℚ] E | ∃ (a : AfQ) (x : 𝓞 E),
        (∀ v : Plc ℚ, Valued.v (a v) ≤ 1) ∧ y = a ⊗ₜ (x : E)}, M y = a ⊗ₜ (c : E) := by
    intro a c ha
    obtain ⟨b, rfl⟩ := Q.surj a
    have hb := (Q.int b).1 ha
    refine ⟨((1 - e) * b) ⊗ₜ (c : E), AddSubgroup.subset_closure ⟨_, c, ?_, rfl⟩, ?_⟩
    · intro v
      by_cases hp : (p : 𝓞 ℚ) ∈ v.asIdeal
      · have : ((1 - e) * b) v = (1 - e v) * b v := rfl
        rw [this, (he v).1 hp, sub_self, zero_mul, map_zero]
        exact zero_le'
      · have : ((1 - e) * b) v = (1 - e v) * b v := rfl
        rw [this, (he v).2 hp, sub_zero, one_mul]
        exact hb v hp
    · rw [hM, map_mul, map_sub, map_one, hρe, sub_zero, one_mul]
  have hMs : Function.Surjective M := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul a x =>
      obtain ⟨b, rfl⟩ := Q.surj a
      exact ⟨b ⊗ₜ x, rfl⟩
    | add u v hu hv =>
      obtain ⟨u', rfl⟩ := hu
      obtain ⟨v', rfl⟩ := hv
      exact ⟨u' + v', map_add _ _ _⟩
  have hO : ∀ z ∈ OHat p E, ∃ y ∈ AddSubgroup.closure {y : AfQ ⊗[ℚ] E | ∃ (a : AfQ) (x : 𝓞 E),
      (∀ v : Plc ℚ, Valued.v (a v) ≤ 1) ∧ y = a ⊗ₜ (x : E)}, M y = z := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, c, ha, rfl⟩ := hz
      exact hgen a c ha
    | zero => exact ⟨0, zero_mem _, map_zero _⟩
    | add u v _ _ hu hv =>
      obtain ⟨u', hu', rfl⟩ := hu
      obtain ⟨v', hv', rfl⟩ := hv
      exact ⟨u' + v', add_mem hu' hv', map_add _ _ _⟩
    | neg u _ hu =>
      obtain ⟨u', hu', rfl⟩ := hu
      exact ⟨-u', neg_mem hu', map_neg _ _⟩
  have hC : ∀ y ∈ AddSubgroup.closure {y : AfQ ⊗[ℚ] E | ∃ (a : AfQ) (x : 𝓞 E),
      (∀ v : Plc ℚ, Valued.v (a v) ≤ 1) ∧ y = a ⊗ₜ (x : E)}, M y ∈ OHat p E := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, c, ha, rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨Q.ρ a, c, (Q.int a).2 fun v _ => ha v, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add u v _ _ hu hv => rw [map_add]; exact add_mem hu hv
    | neg u _ hu => rw [map_neg]; exact neg_mem hu
  exact ⟨{ toAdQ := Q
           Φ := (M : AfQ ⊗[ℚ] E →+* AfP p ⊗[ℚ] E).comp (ι.symm : Af E →+* AfQ ⊗[ℚ] E)
           Φ_E := fun x => by
            show M (ι.symm _) = _
            rw [← hιE, ι.symm_apply_apply, hM, map_one]
           Φ_Q := fun a => by
            show M (ι.symm _) = _
            rw [← hιa, ι.symm_apply_apply, hM]
           Φ_surj := fun z => by
            obtain ⟨y, rfl⟩ := hMs z
            refine ⟨ι y, ?_⟩
            show M (ι.symm (ι y)) = _
            rw [ι.symm_apply_apply]
           Φ_ker := hMker'
           Φ_int := fun x => by
            show M (ι.symm x) ∈ OHat p E ↔ _
            constructor
            · intro hx w hw
              obtain ⟨y, hy, hyz⟩ := hO _ hx
              have hd : M (ι.symm (x - ι y)) = 0 := by
                rw [map_sub, map_sub, ι.symm_apply_apply, hyz, sub_self]
              have h0 := (hMker' _).1 hd w hw
              rw [map_sub, sub_eq_zero] at h0
              rw [h0]
              exact (h2 y).1 hy w
            · intro hx
              have hz : M (ι.symm (finiteAdeleMap ℚ E e * x)) = 0 := by
                rw [← hιe, map_mul ι.symm, ι.symm_apply_apply, map_mul, hMe, zero_mul]
              have hi : ι.symm (x - finiteAdeleMap ℚ E e * x) ∈ AddSubgroup.closure
                  {y : AfQ ⊗[ℚ] E | ∃ (a : AfQ) (x : 𝓞 E),
                    (∀ v : Plc ℚ, Valued.v (a v) ≤ 1) ∧ y = a ⊗ₜ (x : E)} := by
                refine (h2 _).2 fun w => ?_
                rw [ι.apply_symm_apply, map_sub, map_mul]
                by_cases hp : (p : 𝓞 E) ∈ w.asIdeal
                · rw [(he' w).1 hp, one_mul, sub_self, map_zero]
                  exact zero_le'
                · rw [(he' w).2 hp, zero_mul, sub_zero]
                  exact hx w hp
              have := hC _ hi
              rwa [map_sub, map_sub, hz, sub_zero] at this
           Φ_conj := fun x => by
            show M (ι.symm (conjFin (conjE E) x)) = conjT E (AfP p) (M (ι.symm x))
            obtain ⟨y, rfl⟩ := ι.surjective x
            rw [ι.symm_apply_apply]
            induction y using TensorProduct.induction_on with
            | zero => simp
            | tmul a z =>
              rw [h1, map_mul, h3, conjFin_algebraMap, ← h1, ι.symm_apply_apply, hM, hM, conjT_tmul]
              rfl
            | add u v hu hv =>
              simp only [map_add, hu, hv] }⟩
