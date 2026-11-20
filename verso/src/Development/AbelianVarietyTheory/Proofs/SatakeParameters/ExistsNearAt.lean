import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsOverVUnder
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwU.Approx
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use `set w := ι z with hw`. Establish `hfin : Set.Finite {Q : HeightOneSpectrum (𝓞 E) | w Q ∉ Q.adicCompletionIntegers E}` using `Filter.eventually_cofinite.1 w.2`. Use `set T := hfin.toFinset with hT`. Establish `hPT : P ∉ T`. Rewrite using `[hT, Set.Finite.mem_toFinset]`.

Conclude with `fun h' => h' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 h)`. Set `e : HeightOneSpectrum (𝓞 E) → ℕ` to `fun Q => (WithZero.log (Valued.v (w Q))).toNat`. Establish `hbound : ∀ Q ∈ T, ∀ s : 𝓞 E, s ∈ Q.asIdeal ^ e Q → Valued.v ((algebraMap E (Q.adicCompletion E) (algebraMap (𝓞 E) E s))) * Valued.v (w Q) ≤ 1`. Introduce `Q hQ s hs`. Establish `hQ' : w Q ∉ Q.adicCompletionIntegers E` using `by rwa [hT, Set.Finite.mem_toFinset] at hQ`.

Establish `hne : Valued.v (w Q) ≠ 0`. Introduce `h0`. Apply `hQ'` to reduce the goal to its premises. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, h0]`. Conclude with `zero_le'`.

Establish `h1 : Valued.v ((algebraMap E (Q.adicCompletion E) (algebraMap (𝓞 E) E s))) ≤ WithZero.exp (-((e Q : ℕ) : ℤ))` using `by show Valued.v (((algebraMap (𝓞 E) E s : E)) : Q.adicCompletion E) ≤ _`. Rewrite using `[HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `(HeightOneSpectrum.intValuation_le_pow_iff_mem _ _ _).2 hs`. Establish `h2 : Valued.v (w Q) ≤ WithZero.exp ((e Q : ℕ) : ℤ)`. Rewrite using `[← WithZero.exp_log hne, WithZero.exp_le_exp]`.

Conclude with `Int.self_le_toNat _`. Combine the equalities or inequalities in the displayed calculation. Take `⟨s, hs⟩` from `IsDedekindDomain.exists_forall_sub_mem_ideal (s := insert P T) (fun Q : HeightOneSpectrum (𝓞 E) => Q.asIdeal) (fun Q => if Q = P then 1 else e Q) (fun Q _ => Q.prime) (fun Q _ Q' _ hne h' => hne (HeightOneSpectrum.ext h')) (fun Q => if Q.1 = P then 1 else 0)`. Establish `hsP : s ∉ P.asIdeal`. Introduce `hm`.

Establish `h1` using `hs P (Finset.mem_insert_self _ _)`. Simplify using `only [if_true, pow_one] at h1`. Apply `P.isPrime.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`. Use `P.asIdeal.sub_mem hm h1` as an intermediate fact.

Simplify using `using this`. Establish `hsQ : ∀ Q ∈ T, s ∈ Q.asIdeal ^ e Q`. Introduce `Q hQ`. Establish `hQP : Q ≠ P` using `fun h' => hPT (h' ▸ hQ)`. Establish `h1` using `hs Q (Finset.mem_insert_of_mem hQ)`.

Simplify `h1` using `[hQP]`. Use `⟨s, hsP, ?_⟩` and prove the remaining obligations. Establish `hmem : iA F E (algebraMap (𝓞 E) E s) * z ∈ RInt F E`. Use `(hι.2 _).2 fun Q => ?_` and prove the remaining obligations. Establish `e1 : ι (iA F E (algebraMap (𝓞 E) E s) * z) Q = algebraMap E (Q.adicCompletion E) (algebraMap (𝓞 E) E s) * w Q`.

Rewrite using `[map_mul, show ι (iA F E (algebraMap (𝓞 E) E s)) = algebraMap E _ (algebraMap (𝓞 E) E s) from hι.1 _]`. Both sides reduce to the same expression. Rewrite using `[e1, map_mul]`. Distinguish the cases in `hQ : Q ∈ T`. Conclude with `hbound Q hQ s (hsQ Q hQ)`.

Establish `hQ' : w Q ∈ Q.adicCompletionIntegers E`. Assume the negation of the conclusion as `hc`. Conclude with `hQ (by rw [hT, Set.Finite.mem_toFinset]; exact hc)`. Rewrite `hQ'` using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Establish `hs1 : Valued.v ((algebraMap E (Q.adicCompletion E) (algebraMap (𝓞 E) E s))) ≤ 1` using `by show Valued.v (((algebraMap (𝓞 E) E s : E)) : Q.adicCompletion E) ≤ _`.

Rewrite using `[HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `HeightOneSpectrum.intValuation_le_one _ _`. Conclude with `mul_le_one' hs1 hQ'`. Conclude with `hmem`.
-/
theorem intAtA_of_val {ι : AfE F E ≃+* FiniteAdeleRing (𝓞 E) E} (hι : IsAdIso ι) (P : HeightOneSpectrum (𝓞 E))
    (z : AfE F E) (h : Valued.v (ι z P) ≤ 1) : IntAtA (F := F) P z := by
  classical
  set w := ι z with hw
  have hfin : Set.Finite {Q : HeightOneSpectrum (𝓞 E) | w Q ∉ Q.adicCompletionIntegers E} :=
    Filter.eventually_cofinite.1 w.2
  set T := hfin.toFinset with hT
  have hPT : P ∉ T := by
    rw [hT, Set.Finite.mem_toFinset]
    exact fun h' => h' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 h)
  let e : HeightOneSpectrum (𝓞 E) → ℕ := fun Q => (WithZero.log (Valued.v (w Q))).toNat
  have hbound : ∀ Q ∈ T, ∀ s : 𝓞 E, s ∈ Q.asIdeal ^ e Q →
      Valued.v ((algebraMap E (Q.adicCompletion E) (algebraMap (𝓞 E) E s))) * Valued.v (w Q) ≤ 1 := by
    intro Q hQ s hs
    have hQ' : w Q ∉ Q.adicCompletionIntegers E := by rwa [hT, Set.Finite.mem_toFinset] at hQ
    have hne : Valued.v (w Q) ≠ 0 := by
      intro h0
      apply hQ'
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, h0]
      exact zero_le'
    have h1 : Valued.v ((algebraMap E (Q.adicCompletion E) (algebraMap (𝓞 E) E s))) ≤ WithZero.exp (-((e Q : ℕ) : ℤ)) := by
      show Valued.v (((algebraMap (𝓞 E) E s : E)) : Q.adicCompletion E) ≤ _
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
      exact (HeightOneSpectrum.intValuation_le_pow_iff_mem _ _ _).2 hs
    have h2 : Valued.v (w Q) ≤ WithZero.exp ((e Q : ℕ) : ℤ) := by
      rw [← WithZero.exp_log hne, WithZero.exp_le_exp]
      exact Int.self_le_toNat _
    calc _ ≤ WithZero.exp (-((e Q : ℕ) : ℤ)) * WithZero.exp ((e Q : ℕ) : ℤ) := mul_le_mul' h1 h2
      _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
  obtain ⟨s, hs⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := insert P T)
    (fun Q : HeightOneSpectrum (𝓞 E) => Q.asIdeal) (fun Q => if Q = P then 1 else e Q)
    (fun Q _ => Q.prime) (fun Q _ Q' _ hne h' => hne (HeightOneSpectrum.ext h'))
    (fun Q => if Q.1 = P then 1 else 0)
  have hsP : s ∉ P.asIdeal := by
    intro hm
    have h1 := hs P (Finset.mem_insert_self _ _)
    simp only [if_true, pow_one] at h1
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have := P.asIdeal.sub_mem hm h1
    simpa using this
  have hsQ : ∀ Q ∈ T, s ∈ Q.asIdeal ^ e Q := by
    intro Q hQ
    have hQP : Q ≠ P := fun h' => hPT (h' ▸ hQ)
    have h1 := hs Q (Finset.mem_insert_of_mem hQ)
    simpa [hQP] using h1
  refine ⟨s, hsP, ?_⟩
  have hmem : iA F E (algebraMap (𝓞 E) E s) * z ∈ RInt F E := by
    refine (hι.2 _).2 fun Q => ?_
    have e1 : ι (iA F E (algebraMap (𝓞 E) E s) * z) Q =
        algebraMap E (Q.adicCompletion E) (algebraMap (𝓞 E) E s) * w Q := by
      rw [map_mul, show ι (iA F E (algebraMap (𝓞 E) E s)) = algebraMap E _ (algebraMap (𝓞 E) E s) from hι.1 _]
      rfl
    rw [e1, map_mul]
    by_cases hQ : Q ∈ T
    · exact hbound Q hQ s (hsQ Q hQ)
    · have hQ' : w Q ∈ Q.adicCompletionIntegers E := by
        by_contra hc
        exact hQ (by rw [hT, Set.Finite.mem_toFinset]; exact hc)
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hQ'
      have hs1 : Valued.v ((algebraMap E (Q.adicCompletion E) (algebraMap (𝓞 E) E s))) ≤ 1 := by
        show Valued.v (((algebraMap (𝓞 E) E s : E)) : Q.adicCompletion E) ≤ _
        rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
        exact HeightOneSpectrum.intValuation_le_one _ _
      exact mul_le_one' hs1 hQ'
  exact hmem

def compAt (ι : AfE F E ≃+* FiniteAdeleRing (𝓞 E) E) (P : HeightOneSpectrum (𝓞 E)) : AfE F E →+* P.adicCompletion E where
  toFun a := ι a P
  map_one' := by rw [map_one]; rfl
  map_mul' a b := by rw [map_mul]; rfl
  map_zero' := by rw [map_zero]; rfl
  map_add' a b := by rw [map_add]; rfl

/- English proof (translation)
Take `⟨ι, hι⟩` from `exists_isAdIso F E`. Use `set Φ := compAt ι P with hΦ`. Establish `hΦi : ∀ x : E, Φ (iA F E x) = algebraMap E (P.adicCompletion E) x`. Introduce `x`. Use `show (ι (iA F E x)) P = _`.

Rewrite using `[show ι (iA F E x) = algebraMap E _ x from hι.1 x]`. Both sides reduce to the same expression. Use `set A : Matrix (Fin N) (Fin N) (P.adicCompletion E) := Φ.mapMatrix ((y⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) with hA`. Use `set B : Matrix (Fin N) (Fin N) (P.adicCompletion E) := Φ.mapMatrix ((y : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) with hB`. Establish `hAB : A * B = 1`.

Rewrite using `[hA, hB, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]`. Use `set qq : P.adicCompletion E := algebraMap E _ ((((qOf P : ℕ) : E) ^ n)⁻¹) with hqq`. Set `S : Set (Matrix (Fin N) (Fin N) (P.adicCompletion E))` to `{G | G.det ≠ 0} ∩ ⋂ a : Fin N, ⋂ b : Fin N, {G | Valued.v (qq * (A * G - 1) a b) ≤ 1}`. Establish `hSo : IsOpen S`. Use `IsOpen.inter (isOpen_ne_fun (Continuous.matrix_det continuous_id) continuous_const) ?_` and prove the remaining obligations.

Use `isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => ?_` and prove the remaining obligations. Establish `hc : Continuous fun G : Matrix (Fin N) (Fin N) (P.adicCompletion E) => qq * (A * G - 1) a b`. Use `continuous_const.mul ?_` and prove the remaining obligations. Conclude with `((continuous_const.matrix_mul continuous_id).sub continuous_const).matrix_elem a b`. Conclude with `(Valued.isOpen_integer (P.adicCompletion E)).preimage hc`.

Establish `hBS : B ∈ S`. Use `⟨?_, Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun b => ?_⟩` and prove the remaining obligations. Introduce `h0`. Use `congrArg Matrix.det hAB` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, h0, mul_zero, Matrix.det_one]`.

Conclude with `zero_ne_one this`. Use `show Valued.v (qq * (A * B - 1) a b) ≤ 1`. Rewrite using `[hAB, sub_self]`. Simplify using the standard rewrite rules. Establish `hd : DenseRange fun g : Matrix (Fin N) (Fin N) E => g.map (algebraMap E (P.adicCompletion E))` using `DenseRange.piMap fun _ => DenseRange.piMap fun _ => HeightOneSpectrum.denseRange_algebraMap E P`.

Take `⟨g0, hg0⟩` from `hd.exists_mem_open hSo ⟨B, hBS⟩`. Take `⟨hdet, hcong⟩` from `hg0`. Establish `hdet0 : g0.det ≠ 0`. Introduce `h0`. Apply `hdet` to reduce the goal to its premises.

Use `show (g0.map (algebraMap E (P.adicCompletion E))).det = 0`. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]`. Use `⟨Matrix.GeneralLinearGroup.mkOfDetNeZero g0 hdet0, fun a b => ?_⟩` and prove the remaining obligations. Use `intAtA_of_val hι P _ ?_` and prove the remaining obligations. Establish `hc : Valued.v (qq * (A * g0.map (algebraMap E (P.adicCompletion E)) - 1) a b) ≤ 1` using `Set.mem_iInter.1 (Set.mem_iInter.1 hcong a) b`.

Use `Eq.trans_le ?_ hc` and prove the remaining obligations. Use `congr 1`. Use `show Φ _ = _`. Rewrite using `[map_mul, hΦi]`. Use `congr 1`.

Establish `e1 : ((y⁻¹ * ratA F (Matrix.GeneralLinearGroup.mkOfDetNeZero g0 hdet0) : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 = ((y⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) * g0.map (iA F E) - 1` using `rfl`. Rewrite using `[e1]`. Establish `e2 : Φ (((((y⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) (AfE F E)) * g0.map (iA F E) - 1 : Matrix (Fin N) (Fin N) (AfE F E))) a b) = Φ.mapMatrix (((y⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) (AfE F E)) * g0.map (iA F E) - 1) a b` using `rfl`. Establish `e3 : Φ.mapMatrix (g0.map (iA F E)) = g0.map (algebraMap E (P.adicCompletion E))` using `Matrix.ext fun i j => hΦi (g0 i j)`. Rewrite using `[e2, map_sub, map_mul, map_one, e3]`.
-/
theorem exists_nearAt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N n : ℕ)
    (P : HeightOneSpectrum (𝓞 E)) (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : ∃ g : GL (Fin N) E, NearAt P n y g := by
  classical
  obtain ⟨ι, hι⟩ := exists_isAdIso F E
  set Φ := compAt ι P with hΦ
  have hΦi : ∀ x : E, Φ (iA F E x) = algebraMap E (P.adicCompletion E) x := by
    intro x
    show (ι (iA F E x)) P = _
    rw [show ι (iA F E x) = algebraMap E _ x from hι.1 x]
    rfl
  set A : Matrix (Fin N) (Fin N) (P.adicCompletion E) := Φ.mapMatrix ((y⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) with hA
  set B : Matrix (Fin N) (Fin N) (P.adicCompletion E) := Φ.mapMatrix ((y : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) with hB
  have hAB : A * B = 1 := by
    rw [hA, hB, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
  set qq : P.adicCompletion E := algebraMap E _ ((((qOf P : ℕ) : E) ^ n)⁻¹) with hqq
  let S : Set (Matrix (Fin N) (Fin N) (P.adicCompletion E)) :=
    {G | G.det ≠ 0} ∩ ⋂ a : Fin N, ⋂ b : Fin N, {G | Valued.v (qq * (A * G - 1) a b) ≤ 1}
  have hSo : IsOpen S := by
    refine IsOpen.inter (isOpen_ne_fun (Continuous.matrix_det continuous_id) continuous_const) ?_
    refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => ?_
    have hc : Continuous fun G : Matrix (Fin N) (Fin N) (P.adicCompletion E) => qq * (A * G - 1) a b := by
      refine continuous_const.mul ?_
      exact ((continuous_const.matrix_mul continuous_id).sub continuous_const).matrix_elem a b
    exact (Valued.isOpen_integer (P.adicCompletion E)).preimage hc
  have hBS : B ∈ S := by
    refine ⟨?_, Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun b => ?_⟩
    · intro h0
      have := congrArg Matrix.det hAB
      rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
      exact zero_ne_one this
    · show Valued.v (qq * (A * B - 1) a b) ≤ 1
      rw [hAB, sub_self]
      simp
  have hd : DenseRange fun g : Matrix (Fin N) (Fin N) E => g.map (algebraMap E (P.adicCompletion E)) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ => HeightOneSpectrum.denseRange_algebraMap E P
  obtain ⟨g0, hg0⟩ := hd.exists_mem_open hSo ⟨B, hBS⟩
  obtain ⟨hdet, hcong⟩ := hg0
  have hdet0 : g0.det ≠ 0 := by
    intro h0
    apply hdet
    show (g0.map (algebraMap E (P.adicCompletion E))).det = 0
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero g0 hdet0, fun a b => ?_⟩
  refine intAtA_of_val hι P _ ?_
  have hc : Valued.v (qq * (A * g0.map (algebraMap E (P.adicCompletion E)) - 1) a b) ≤ 1 :=
    Set.mem_iInter.1 (Set.mem_iInter.1 hcong a) b
  refine Eq.trans_le ?_ hc
  congr 1
  show Φ _ = _
  rw [map_mul, hΦi]
  congr 1
  have e1 : ((y⁻¹ * ratA F (Matrix.GeneralLinearGroup.mkOfDetNeZero g0 hdet0) : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 =
      ((y⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) * g0.map (iA F E) - 1 := rfl
  rw [e1]
  have e2 : Φ (((((y⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) (AfE F E)) * g0.map (iA F E) - 1 :
      Matrix (Fin N) (Fin N) (AfE F E))) a b) =
      Φ.mapMatrix (((y⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) (AfE F E)) * g0.map (iA F E) - 1) a b := rfl
  have e3 : Φ.mapMatrix (g0.map (iA F E)) = g0.map (algebraMap E (P.adicCompletion E)) :=
    Matrix.ext fun i j => hΦi (g0 i j)
  rw [e2, map_sub, map_mul, map_one, e3]

end GlobalTheory.TwU.Approx
