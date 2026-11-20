import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIntegralIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NcardImageOfLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CongruentOneMatricesTransitiveNearHermitianStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatrixCongruentOneModUniformizerPowGroupAndOrbitStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryNearIdentityCloseTuplesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryTupleMatrixRightMulNearIdentityStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AlgMem
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.ThickOrbit

/- English proof (translation)
Establish `: Finite (B ⧸ A.addSubgroupOf B)`. Use `h.to_subtype` as an intermediate fact. Set `f : B ⧸ A.addSubgroupOf B → ((QuotientAddGroup.mk : W → W ⧸ A) '' (B : Set W))` to `fun q => ⟨QuotientAddGroup.mk (q.out : W), q.out, q.out.2, rfl⟩`. Use `Finite.of_injective f fun a b hab => ?_` and prove the remaining obligations. Establish `h1 : (QuotientAddGroup.mk (a.out : W) : W ⧸ A) = QuotientAddGroup.mk (b.out : W)` using `congrArg Subtype.val hab`.

Rewrite `h1` using `[QuotientAddGroup.eq]`. Rewrite using `[← a.out_eq', ← b.out_eq', QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]`. Simplify using `using h1`. Conclude with `AddSubgroup.index_ne_zero_of_finite`.
-/
theorem relIndex_ne_zero_of_finite {W : Type} [AddCommGroup W] (A B : AddSubgroup W)
    (h : ((QuotientAddGroup.mk : W → W ⧸ A) '' (B : Set W)).Finite) : A.relIndex B ≠ 0 := by
  have : Finite (B ⧸ A.addSubgroupOf B) := by
    have := h.to_subtype
    let f : B ⧸ A.addSubgroupOf B → ((QuotientAddGroup.mk : W → W ⧸ A) '' (B : Set W)) := fun q =>
      ⟨QuotientAddGroup.mk (q.out : W), q.out, q.out.2, rfl⟩
    refine Finite.of_injective f fun a b hab => ?_
    have h1 : (QuotientAddGroup.mk (a.out : W) : W ⧸ A) = QuotientAddGroup.mk (b.out : W) :=
      congrArg Subtype.val hab
    rw [QuotientAddGroup.eq] at h1
    rw [← a.out_eq', ← b.out_eq', QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    simpa using h1
  exact AddSubgroup.index_ne_zero_of_finite

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

/- English proof (translation)
The claim follows from `(GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (Subring.pow_mem _ ϖ.2 k)`.
-/
theorem pow_mem (L : LocE F E) (ϖ : 𝒪[F]) (k : ℕ) : algebraMap F E ((ϖ : F) ^ k) ∈ L.O :=
  (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (Subring.pow_mem _ ϖ.2 k)

/- English proof (translation)
The claim follows from `Λ.smul_mem ⟨c, hc⟩ hv`.
-/
theorem smul_mem (L : LocE F E) {n : ℕ} {Λ : Submodule L.O (Fin n → E)} {c : E} (hc : c ∈ L.O)
    {v : Fin n → E} (hv : v ∈ Λ) : c • v ∈ Λ := Λ.smul_mem ⟨c, hc⟩ hv

/- English proof (translation)
Use `L.free` as an intermediate fact. Establish `: Module.Finite F E` using `Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)`. Establish `h1 : IsAlgebraic F c` using `(Algebra.IsIntegral.isIntegral (R := F) c).isAlgebraic`. Establish `h2 : IsAlgebraic 𝒪[F] c` using `(IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2 h1`. Take `⟨d, hd, hi⟩` from `h2.exists_integral_multiple`.

Take `⟨k, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hϖ`. Use `⟨k, (L.O_def _).2 ?_⟩` and prove the remaining obligations. Establish `h3` using `hi.smul (↑u⁻¹ : 𝒪[F])`. Rewrite `h3` using `[smul_smul, ← mul_assoc, Units.inv_mul, one_mul, Algebra.smul_def]`. Use `h3 using 2` and compare the differences between its conclusion and the goal.

Rewrite using `[IsScalarTower.algebraMap_apply 𝒪[F] F E, map_pow, map_pow, map_pow]`. Both sides reduce to the same expression.
-/
theorem exists_pow_mul_mem (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (c : E) :
    ∃ k : ℕ, algebraMap F E ((ϖ : F) ^ k) * c ∈ L.O := by
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  have h1 : IsAlgebraic F c := (Algebra.IsIntegral.isIntegral (R := F) c).isAlgebraic
  have h2 : IsAlgebraic 𝒪[F] c := (IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2 h1
  obtain ⟨d, hd, hi⟩ := h2.exists_integral_multiple
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hϖ
  refine ⟨k, (L.O_def _).2 ?_⟩
  have h3 := hi.smul (↑u⁻¹ : 𝒪[F])
  rw [smul_smul, ← mul_assoc, Units.inv_mul, one_mul, Algebra.smul_def] at h3
  convert h3 using 2
  rw [IsScalarTower.algebraMap_apply 𝒪[F] F E, map_pow, map_pow, map_pow]
  rfl

/- English proof (translation)
Rewrite using `[smul_smul, ← map_mul, pow_add]`.
-/
theorem pow_add_smul (ϖ : 𝒪[F]) {V : Type} [AddCommGroup V] [Module E V] (a b : ℕ) (v : V) :
    algebraMap F E ((ϖ : F) ^ (a + b)) • v =
      algebraMap F E ((ϖ : F) ^ a) • algebraMap F E ((ϖ : F) ^ b) • v := by
  rw [smul_smul, ← map_mul, pow_add]

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.PowMulMem.exists_pow_smul_mem`. Consider the case `exact _root_.GlobalTheory.PowMulMem.exists_pow_smul_mem`. Consider the case `(apply _root_.GlobalTheory.PowMulMem.exists_pow_smul_mem <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.PowMulMem.exists_pow_smul_mem <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.PowMulMem.exists_pow_smul_mem <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.PowMulMem.exists_pow_smul_mem ..)`.
-/
theorem exists_pow_smul_mem (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {n : ℕ}
    {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) (v : Fin n → E) :
    ∃ k : ℕ, algebraMap F E ((ϖ : F) ^ k) • v ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.PowMulMem.exists_pow_smul_mem
  | exact _root_.GlobalTheory.PowMulMem.exists_pow_smul_mem
  | (apply _root_.GlobalTheory.PowMulMem.exists_pow_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowMulMem.exists_pow_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowMulMem.exists_pow_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowMulMem.exists_pow_smul_mem ..)

/- English proof (translation)
Take `⟨s, hs⟩` from `hΛ'.1`. Use `choose k hk using exists_pow_smul_mem L hϖ hΛ`. Use `⟨s.sup k, fun v hv => ?_⟩` and prove the remaining obligations. Rewrite `hv` using `[← hs]`. Proceed by induction on `hv using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨d, hd⟩` from `Nat.exists_eq_add_of_le' (Finset.le_sup (f := k) hx)`. Rewrite using `[hd, pow_add_smul]`. Conclude with `smul_mem L (pow_mem L ϖ d) (hk x)`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `Λ.add_mem hx hy`. Consider the case `smul c x _ hx`. Rewrite using `[smul_comm]`. Conclude with `Λ.smul_mem c hx`.
-/
theorem exists_pow_le (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {n : ℕ}
    {Λ Λ' : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) (hΛ' : IsLat L Λ') :
    ∃ k : ℕ, ∀ v ∈ Λ', algebraMap F E ((ϖ : F) ^ k) • v ∈ Λ := by
  obtain ⟨s, hs⟩ := hΛ'.1
  choose k hk using exists_pow_smul_mem L hϖ hΛ
  refine ⟨s.sup k, fun v hv => ?_⟩
  rw [← hs] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := k) hx)
    rw [hd, pow_add_smul]
    exact smul_mem L (pow_mem L ϖ d) (hk x)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Λ.add_mem hx hy
  | smul c x _ hx =>
    rw [smul_comm]; exact Λ.smul_mem c hx

/- English proof (translation)
Take `⟨-, -, -, -, -, hc, hq, -⟩` from `GlobalTheory.UnramOrder.order_facts L ϖ hϖ`. Establish `hc` using `hc j`. Use `set I : Ideal L.O := Ideal.span {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ j)} with hI`. Establish `hI' : I = Ideal.span {(⟨_, pow_mem L ϖ j⟩ : L.O)}`. Rewrite using `[hI]`.

Conclude with `congrArg Ideal.span (Set.ext fun y => by simp [Subtype.ext_iff])`. Establish `: Finite (L.O ⧸ I)` using `Nat.finite_of_card_ne_zero (by rw [hc]; positivity)`. Take `⟨k, s, hs⟩` from `Submodule.fg_iff_exists_fin_generating_family.1 hΛ.1`. Use `⟨Set.range fun q : Fin k → L.O ⧸ I => ∑ i, (q i).out • s i, Set.finite_range _, fun v hv => ?_⟩` and prove the remaining obligations. Rewrite `hv` using `[← hs, Submodule.mem_span_range_iff_exists_fun]`.

Take `⟨c, rfl⟩` from `hv`. Establish `h1 : ∀ i, ∃ d : L.O, c i = (Ideal.Quotient.mk I (c i)).out + ⟨_, pow_mem L ϖ j⟩ * d`. Introduce `i`. Establish `h2 : c i - (Ideal.Quotient.mk I (c i)).out ∈ I`. Rewrite using `[← Ideal.Quotient.eq]`.

Conclude with `(Quotient.out_eq' _).symm`. Rewrite `h2` using `[hI', Ideal.mem_span_singleton]`. Take `⟨d, hd⟩` from `h2`. Conclude with `⟨d, by rw [← hd, ← hI']; ring⟩`. Use `choose d hd using h1`.

Use `⟨_, ⟨fun i => Ideal.Quotient.mk I (c i), rfl⟩, ∑ i, d i • s i, ?_, ?_⟩` and prove the remaining obligations. Use `Submodule.sum_mem _ fun i _ => Λ.smul_mem _ ?_` and prove the remaining obligations. Rewrite using `[← hs]`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Rewrite using `[Finset.smul_sum, ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `conv_lhs => rw [hd i, add_smul, mul_smul]`. Both sides reduce to the same expression.
-/
theorem exists_reps (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {n : ℕ}
    {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) (j : ℕ) :
    ∃ R : Set (Fin n → E), R.Finite ∧ ∀ v ∈ Λ, ∃ r ∈ R, ∃ w ∈ Λ,
      v = r + algebraMap F E ((ϖ : F) ^ j) • w := by
  obtain ⟨-, -, -, -, -, hc, hq, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  have hc := hc j
  set I : Ideal L.O := Ideal.span {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ j)} with hI
  have hI' : I = Ideal.span {(⟨_, pow_mem L ϖ j⟩ : L.O)} := by
    rw [hI]
    exact congrArg Ideal.span (Set.ext fun y => by simp [Subtype.ext_iff])
  have : Finite (L.O ⧸ I) := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  obtain ⟨k, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hΛ.1
  refine ⟨Set.range fun q : Fin k → L.O ⧸ I => ∑ i, (q i).out • s i, Set.finite_range _,
    fun v hv => ?_⟩
  rw [← hs, Submodule.mem_span_range_iff_exists_fun] at hv
  obtain ⟨c, rfl⟩ := hv
  have h1 : ∀ i, ∃ d : L.O, c i = (Ideal.Quotient.mk I (c i)).out + ⟨_, pow_mem L ϖ j⟩ * d := by
    intro i
    have h2 : c i - (Ideal.Quotient.mk I (c i)).out ∈ I := by
      rw [← Ideal.Quotient.eq]
      exact (Quotient.out_eq' _).symm
    rw [hI', Ideal.mem_span_singleton] at h2
    obtain ⟨d, hd⟩ := h2
    exact ⟨d, by rw [← hd, ← hI']; ring⟩
  choose d hd using h1
  refine ⟨_, ⟨fun i => Ideal.Quotient.mk I (c i), rfl⟩, ∑ i, d i • s i, ?_, ?_⟩
  · refine Submodule.sum_mem _ fun i _ => Λ.smul_mem _ ?_
    rw [← hs]; exact Submodule.subset_span ⟨i, rfl⟩
  · rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_lhs => rw [hd i, add_smul, mul_smul]
    rfl

/- English proof (translation)
Use `IsUnit.map _ (IsUnit.mk0 _ (pow_ne_zero _ ?_))` and prove the remaining obligations. Introduce `h`. Conclude with `hϖ.ne_zero (Subtype.ext h)`.
-/
theorem isUnit_pow {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (k : ℕ) :
    IsUnit (algebraMap F E ((ϖ : F) ^ k)) := by
  refine IsUnit.map _ (IsUnit.mk0 _ (pow_ne_zero _ ?_))
  intro h
  exact hϖ.ne_zero (Subtype.ext h)

/- English proof (translation)
Take `⟨R, hR, hR'⟩` from `exists_reps L hϖ hΛ (e + M)`. Take `⟨u, hu⟩` from `isUnit_pow (E := E) hϖ e`. Use `((Set.Finite.pi' (fun _ : Fin m => hR)).image (fun r => (QuotientAddGroup.mk ((↑u⁻¹ : E) • r) : _ ⧸ A))).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Use `choose r hr w hw h using fun a => hR' _ (hS x hx a)`.

Use `⟨r, hr, ?_⟩` and prove the remaining obligations. Rewrite using `[QuotientAddGroup.eq]`. Use `hA w hw using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `a`. Establish `h1` using `congrArg (fun t => (↑u⁻¹ : E) • t) (h a)`.

Simplify using `only [pow_add_smul, ← hu, smul_add, smul_smul (↑u⁻¹ : E) (u : E), Units.inv_mul, one_smul] at h1`. Simplify using `only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, h1]`. Normalize the expressions using the abelian group laws.
-/
theorem finite_image (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {n m : ℕ}
    {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) (M e : ℕ)
    (A : AddSubgroup (Fin m → Fin n → E))
    (hA : ∀ w : Fin m → Fin n → E, (∀ a, w a ∈ Λ) → algebraMap F E ((ϖ : F) ^ M) • w ∈ A)
    (S : Set (Fin m → Fin n → E)) (hS : ∀ x ∈ S, ∀ a, algebraMap F E ((ϖ : F) ^ e) • x a ∈ Λ) :
    ((QuotientAddGroup.mk : _ → _ ⧸ A) '' S).Finite := by
  obtain ⟨R, hR, hR'⟩ := exists_reps L hϖ hΛ (e + M)
  obtain ⟨u, hu⟩ := isUnit_pow (E := E) hϖ e
  refine ((Set.Finite.pi' (fun _ : Fin m => hR)).image
    (fun r => (QuotientAddGroup.mk ((↑u⁻¹ : E) • r) : _ ⧸ A))).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  choose r hr w hw h using fun a => hR' _ (hS x hx a)
  refine ⟨r, hr, ?_⟩
  rw [QuotientAddGroup.eq]
  convert hA w hw using 1
  funext a
  have h1 := congrArg (fun t => (↑u⁻¹ : E) • t) (h a)
  simp only [pow_add_smul, ← hu, smul_add, smul_smul (↑u⁻¹ : E) (u : E), Units.inv_mul, one_smul] at h1
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, h1]
  abel

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `only [rmul, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]`.
-/
theorem rmul_rmul {n m : ℕ} (x : Fin m → Fin n → E) (A B : Matrix (Fin m) (Fin m) E) :
    rmul (rmul x A) B = rmul x (A * B) := by
  funext j
  simp only [rmul, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `[rmul, Matrix.one_apply]`.
-/
theorem rmul_one {n m : ℕ} (x : Fin m → Fin n → E) : rmul x 1 = x := by
  funext j
  simp [rmul, Matrix.one_apply]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `[rmul, Finset.sum_add_distrib]`.
-/
theorem rmul_add {n m : ℕ} (x y : Fin m → Fin n → E) (A : Matrix (Fin m) (Fin m) E) :
    rmul (x + y) A = rmul x A + rmul y A := by
  funext j
  simp [rmul, Finset.sum_add_distrib]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `only [rmul, Pi.smul_apply, Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => smul_comm _ _ _`.
-/
theorem rmul_smul {n m : ℕ} (c : E) (x : Fin m → Fin n → E) (A : Matrix (Fin m) (Fin m) E) :
    rmul (c • x) A = c • rmul x A := by
  funext j
  simp only [rmul, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun _ _ => smul_comm _ _ _

/- English proof (translation)
The claim follows from `Λ.sum_mem fun i _ => smul_mem L (hA i a) (hx i)`.
-/
theorem rmul_mem (L : LocE F E) {n m : ℕ} {Λ : Submodule L.O (Fin n → E)} {x : Fin m → Fin n → E}
    (hx : ∀ a, x a ∈ Λ) {A : Matrix (Fin m) (Fin m) E} (hA : IsIntM L A) (a : Fin m) :
    rmul x A a ∈ Λ :=
  Λ.sum_mem fun i _ => smul_mem L (hA i a) (hx i)

/- English proof (translation)
Use `choose c hc h using hA`. Use `⟨∑ k, c k a • x k, Λ.sum_mem fun k _ => smul_mem L (hc k a) (hx k), ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← congrFun (rmul_one x) a]`. Simplify using `only [rmul, Finset.smul_sum, smul_smul, ← h, sub_smul, Finset.sum_sub_distrib]`.
-/
theorem rmul_cong (L : LocE F E) {ϖ : 𝒪[F]} {n m i : ℕ} {Λ : Submodule L.O (Fin n → E)}
    {x : Fin m → Fin n → E} (hx : ∀ a, x a ∈ Λ) {A : Matrix (Fin m) (Fin m) E}
    (hA : A ∈ congK L ϖ m i) (a : Fin m) :
    ∃ w ∈ Λ, rmul x A a - x a = algebraMap F E ((ϖ : F) ^ i) • w := by
  choose c hc h using hA
  refine ⟨∑ k, c k a • x k, Λ.sum_mem fun k _ => smul_mem L (hc k a) (hx k), ?_⟩
  conv_lhs => rw [← congrFun (rmul_one x) a]
  simp only [rmul, Finset.smul_sum, smul_smul, ← h, sub_smul, Finset.sum_sub_distrib]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[cT, Matrix.mul_apply, mul_comm]`.
-/
theorem cT_mul (L : LocE F E) {m : ℕ} (A B : Matrix (Fin m) (Fin m) E) :
    cT L (A * B) = cT L B * cT L A := by
  ext a b
  simp [cT, Matrix.mul_apply, mul_comm]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[cT, Matrix.one_apply, apply_ite L.cj, eq_comm]`.
-/
theorem cT_one (L : LocE F E) {m : ℕ} : cT L (1 : Matrix (Fin m) (Fin m) E) = 1 := by
  ext a b
  simp [cT, Matrix.one_apply, apply_ite L.cj, eq_comm]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[gramT, GlobalTheory.HL.Model.hf_smul_left, GlobalTheory.HL.Model.hf_smul_right, mul_assoc, -algebraMap_smul]`.
-/
theorem gramT_smul (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (c : F)
    (x : Fin m → Fin n → E) :
    gramT L Hm (algebraMap F E c • x) = (algebraMap F E c * algebraMap F E c) • gramT L Hm x := by
  ext a b
  simp [gramT, GlobalTheory.HL.Model.hf_smul_left, GlobalTheory.HL.Model.hf_smul_right, mul_assoc,
    -algebraMap_smul]

/- English proof (translation)
Establish `hpe` using `isUnit_pow (E := E) hϖ e`. Take `⟨N', hN'⟩` from `GlobalTheory.T.exists_isometry_near_identity_close_tuples L ϖ hϖ Hm hH Λ hΛ m ((algebraMap F E ((ϖ : F) ^ e) * algebraMap F E ((ϖ : F) ^ e)) • Γ) (by rw [Matrix.det_smul]; exact ((hpe.mul hpe).pow _).mul hΓ) N`. Establish `hi' : 1 ≤ N' + i` using `by omega`. Take `⟨j, hj⟩` from `GlobalTheory.T.congruentOneMatrices_transitive_near_hermitian L ϖ hϖ m Γ hh hΓ (N' + i) hi'`. Take `⟨h1, hK', -⟩` from `GlobalTheory.T.matrixCongruentOneModUniformizerPow_group_and_orbits L ϖ hϖ m (N' + i) hi'`.

Take `⟨h2, hK, -⟩` from `GlobalTheory.T.matrixCongruentOneModUniformizerPow_group_and_orbits L ϖ hϖ m i hi`. Use `⟨N' + (j + e), fun y u hy hG hu => ?_⟩` and prove the remaining obligations. Establish `hint : ∀ v ∈ Λ, ∀ w ∈ Λ, hf L Hm v w ∈ L.O` using `fun v hv w hw => (hΛ.2 w).2 hw v hv`. Set `D : Matrix (Fin m) (Fin m) E` to `Matrix.of fun a b => algebraMap F E ((ϖ : F) ^ N') * (hf L Hm (algebraMap F E ((ϖ : F) ^ e) • y b) (u a) + hf L Hm (u b) (algebraMap F E ((ϖ : F) ^ e) • y a)) + algebraMap F E ((ϖ : F) ^ (N' + N' + j + e + e)) * hf L Hm (u b) (u a)`. Establish `hD : IsHerm L D`.

Use extensionality with `a b`. Simplify using `only [cT, D, Matrix.of_apply, map_add, map_mul, AlgEquiv.commutes, ← GlobalTheory.HL.Model.hf_symm L hH.1]`. Expand and normalize the polynomial expressions, which then agree. Establish `hD' : IsIntM L D` using `fun a b => L.O.add_mem (L.O.mul_mem (pow_mem L ϖ _) (L.O.add_mem (hint _ (hy b) _ (hu a)) (hint _ (hu b) _ (hy a)))) (L.O.mul_mem (pow_mem L ϖ _) (hint _ (hu b) _ (hu a)))`. Take `⟨A, hA, hA'⟩` from `hj Γ ⟨1, h1, by rw [cT_one]; simp⟩ D hD hD'`.

Use `set y1 := y + algebraMap F E ((ϖ : F) ^ (N' + (j + e))) • u with hy1`. Establish `hG1 : gramT L Hm y1 = cT L A * Γ * A`. Rewrite using `[← hA', ← hG]`. Use extensionality with `a b`. Simplify using `only [gramT, hy1, D, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, GlobalTheory.HL.Model.hf_add_left, GlobalTheory.HL.Model.hf_add_right, GlobalTheory.HL.Model.hf_smul_left, GlobalTheory.HL.Model.hf_smul_right, AlgEquiv.commutes]`.

Simplify using `only [map_pow]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨-, hAu, -, hAi, -⟩` from `hK' A hA`. Establish `hG2 : gramT L Hm (rmul y1 A⁻¹) = Γ`. Rewrite using `[GlobalTheory.HL.ContModel.gramT_rmul, hG1]`.

Combine the equalities or inequalities in the displayed calculation. Take `⟨g, hg, hgc, hgy⟩` from `hN' (algebraMap F E ((ϖ : F) ^ e) • y) (algebraMap F E ((ϖ : F) ^ e) • rmul y1 A⁻¹) hy (by rw [gramT_smul, hG]) (by rw [gramT_smul, hG2]) (by`. Introduce `a`. Take `⟨w, hw, hw'⟩` from `rmul_cong L (x := algebraMap F E ((ϖ : F) ^ e) • y) hy hAi a`. Use `⟨algebraMap F E ((ϖ : F) ^ i) • w + algebraMap F E ((ϖ : F) ^ (j + e + e)) • rmul u A⁻¹ a, Λ.add_mem (smul_mem L (pow_mem L ϖ _) hw) (smul_mem L (pow_mem L ϖ _) (rmul_mem L hu (hK' _ hAi).1 a)), ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_add, ← pow_add_smul, ← hw', hy1, rmul_add, rmul_smul, rmul_smul]`. Simplify using `only [Pi.smul_apply, Pi.add_apply, smul_add, ← pow_add_smul]`. Rewrite using `[show e + (N' + (j + e)) = N' + (j + e + e) by ring]`. Use the proof step `abel)`. Use `⟨g, hg, hgc, A, (((hK 1 h2).2.2.2.2.2) (N' + i) (by omega) A hA).2, ?_⟩` and prove the remaining obligations.

Establish `h3 : (fun a => g (y a)) = rmul y1 A⁻¹`. Use function extensionality and compare the values at `a`. Use `hgy a` as an intermediate fact. Simplify using `only [Pi.smul_apply, map_smul] at this`. Conclude with `(hpe.smul_left_cancel).1 this`.

Rewrite using `[h3, rmul_rmul, Matrix.nonsing_inv_mul _ hAu, rmul_one]`.
-/
theorem exists_close (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {n : ℕ}
    {Hm : Matrix (Fin n) (Fin n) E} (hH : IsHermND L Hm) {Λ : Submodule L.O (Fin n → E)}
    (hΛ : IsSD L Hm Λ) {m : ℕ} {Γ : Matrix (Fin m) (Fin m) E} (hh : IsHerm L Γ) (hΓ : IsUnit Γ.det)
    (N e i : ℕ) (hi : 1 ≤ i) : ∃ M : ℕ, ∀ y u : Fin m → Fin n → E,
      (∀ a, algebraMap F E ((ϖ : F) ^ e) • y a ∈ Λ) → gramT L Hm y = Γ → (∀ a, u a ∈ Λ) →
      ∃ g ∈ isomG L Hm, CongId L ϖ Λ N g ∧ ∃ A ∈ congK L ϖ m i,
        y + algebraMap F E ((ϖ : F) ^ M) • u = rmul (fun a => g (y a)) A := by
  have hpe := isUnit_pow (E := E) hϖ e
  obtain ⟨N', hN'⟩ := GlobalTheory.T.exists_isometry_near_identity_close_tuples L ϖ hϖ Hm hH Λ hΛ m
    ((algebraMap F E ((ϖ : F) ^ e) * algebraMap F E ((ϖ : F) ^ e)) • Γ)
    (by rw [Matrix.det_smul]; exact ((hpe.mul hpe).pow _).mul hΓ) N
  have hi' : 1 ≤ N' + i := by omega
  obtain ⟨j, hj⟩ := GlobalTheory.T.congruentOneMatrices_transitive_near_hermitian L ϖ hϖ m Γ hh hΓ (N' + i) hi'
  obtain ⟨h1, hK', -⟩ := GlobalTheory.T.matrixCongruentOneModUniformizerPow_group_and_orbits L ϖ hϖ m (N' + i) hi'
  obtain ⟨h2, hK, -⟩ := GlobalTheory.T.matrixCongruentOneModUniformizerPow_group_and_orbits L ϖ hϖ m i hi
  refine ⟨N' + (j + e), fun y u hy hG hu => ?_⟩
  have hint : ∀ v ∈ Λ, ∀ w ∈ Λ, hf L Hm v w ∈ L.O := fun v hv w hw => (hΛ.2 w).2 hw v hv
  let D : Matrix (Fin m) (Fin m) E := Matrix.of fun a b =>
    algebraMap F E ((ϖ : F) ^ N') * (hf L Hm (algebraMap F E ((ϖ : F) ^ e) • y b) (u a) +
      hf L Hm (u b) (algebraMap F E ((ϖ : F) ^ e) • y a)) +
      algebraMap F E ((ϖ : F) ^ (N' + N' + j + e + e)) * hf L Hm (u b) (u a)
  have hD : IsHerm L D := by
    ext a b
    simp only [cT, D, Matrix.of_apply, map_add, map_mul, AlgEquiv.commutes, ← GlobalTheory.HL.Model.hf_symm L hH.1]
    ring
  have hD' : IsIntM L D := fun a b =>
    L.O.add_mem (L.O.mul_mem (pow_mem L ϖ _) (L.O.add_mem (hint _ (hy b) _ (hu a))
      (hint _ (hu b) _ (hy a)))) (L.O.mul_mem (pow_mem L ϖ _) (hint _ (hu b) _ (hu a)))
  obtain ⟨A, hA, hA'⟩ := hj Γ ⟨1, h1, by rw [cT_one]; simp⟩ D hD hD'
  set y1 := y + algebraMap F E ((ϖ : F) ^ (N' + (j + e))) • u with hy1
  have hG1 : gramT L Hm y1 = cT L A * Γ * A := by
    rw [← hA', ← hG]
    ext a b
    simp only [gramT, hy1, D, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, GlobalTheory.HL.Model.hf_add_left, GlobalTheory.HL.Model.hf_add_right,
      GlobalTheory.HL.Model.hf_smul_left, GlobalTheory.HL.Model.hf_smul_right, AlgEquiv.commutes]
    simp only [map_pow]
    ring
  obtain ⟨-, hAu, -, hAi, -⟩ := hK' A hA
  have hG2 : gramT L Hm (rmul y1 A⁻¹) = Γ := by
    rw [GlobalTheory.HL.ContModel.gramT_rmul, hG1]
    calc _ = cT L (A * A⁻¹) * Γ * (A * A⁻¹) := by rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = Γ := by rw [Matrix.mul_nonsing_inv _ hAu, cT_one]; simp
  obtain ⟨g, hg, hgc, hgy⟩ := hN' (algebraMap F E ((ϖ : F) ^ e) • y)
    (algebraMap F E ((ϖ : F) ^ e) • rmul y1 A⁻¹) hy (by rw [gramT_smul, hG])
    (by rw [gramT_smul, hG2]) (by
      intro a
      obtain ⟨w, hw, hw'⟩ := rmul_cong L (x := algebraMap F E ((ϖ : F) ^ e) • y) hy hAi a
      refine ⟨algebraMap F E ((ϖ : F) ^ i) • w +
        algebraMap F E ((ϖ : F) ^ (j + e + e)) • rmul u A⁻¹ a, Λ.add_mem
        (smul_mem L (pow_mem L ϖ _) hw)
        (smul_mem L (pow_mem L ϖ _) (rmul_mem L hu (hK' _ hAi).1 a)), ?_⟩
      rw [smul_add, ← pow_add_smul, ← hw', hy1, rmul_add, rmul_smul, rmul_smul]
      simp only [Pi.smul_apply, Pi.add_apply, smul_add, ← pow_add_smul]
      rw [show e + (N' + (j + e)) = N' + (j + e + e) by ring]
      abel)
  refine ⟨g, hg, hgc, A, (((hK 1 h2).2.2.2.2.2) (N' + i) (by omega) A hA).2, ?_⟩
  have h3 : (fun a => g (y a)) = rmul y1 A⁻¹ := by
    funext a
    have := hgy a
    simp only [Pi.smul_apply, map_smul] at this
    exact (hpe.smul_left_cancel).1 this
  rw [h3, rmul_rmul, Matrix.nonsing_inv_mul _ hAu, rmul_one]

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm hH Λs hΛs Λ hΛ m Γ hΓ N e`. Take `⟨i1, hi1⟩` from `GlobalTheory.T.exists_isometry_tupleMatrixRightMul_near_identity L ϖ hϖ Hm hH Λ hΛ m Γ hΓ N e`. Use `⟨i1 + 1, by omega, fun i hi K hK hKN x hx hG => ?_⟩` and prove the remaining obligations. Establish `horb : ∀ y ∈ torb K x, (∀ a, algebraMap F E ((ϖ : F) ^ e) • y a ∈ Λ) ∧ gramT L Hm y = Γ ∧ ∀ g ∈ K, (fun a => g (y a)) ∈ torb K x`. Introduce and unpack `_ ⟨g, hg, rfl⟩`.

Use `⟨fun a => ?_, ?_, fun g' hg' => ⟨g' * g, K.mul_mem hg' hg, rfl⟩⟩` and prove the remaining obligations. Establish `h : g • Λ = Λ` using `(hK hg).2`. Rewrite using `[← map_smul, ← h]`. Conclude with `⟨_, hx a, rfl⟩`. Rewrite using `[← hG]`.

Use extensionality with `a b`. Conclude with `(hK hg).1 _ _`. Use `⟨?_, fun y hy A hA hA' => ?_⟩` and prove the remaining obligations. Use `swap`. Take `⟨h1, h2, h3⟩` from `horb y hy`.

Take `⟨g, hg, hgc, hgy⟩` from `hi1 i (by omega) y h1 h2 A hA hA'`. Rewrite using `[← funext hgy]`. Conclude with `h3 g (hKN g hg hgc)`. Establish `hh : IsHerm L Γ`. Rewrite using `[← hG]`.

Use extensionality with `a b`. Conclude with `(GlobalTheory.HL.Model.hf_symm L hH.1 _ _).symm`. Take `⟨M, hM⟩` from `exists_close L hϖ hH hΛ hh hΓ N e i (by omega)`. Take `⟨-, hC, -⟩` from `GlobalTheory.T.matrixCongruentOneModUniformizerPow_group_and_orbits L ϖ hϖ m i (by omega)`. Set `B : AddSubgroup (Fin m → Fin n → E)` to `(tupLat L Λ m).map (DistribMulAction.toAddMonoidHom _ (algebraMap F E ((ϖ : F) ^ M)))`.

Establish `hB : ∀ w : Fin m → Fin n → E, (∀ a, w a ∈ Λ) → algebraMap F E ((ϖ : F) ^ M) • w ∈ B` using `fun w hw => ⟨w, fun a _ => hw a, rfl⟩`. Take `⟨k, hk⟩` from `exists_pow_le L hϖ hΛ.1 hΛs.1`. Take `⟨l, hl⟩` from `exists_pow_le L hϖ hΛs.1 hΛ.1`. Use `⟨B, relIndex_ne_zero_of_finite _ _ (finite_image L hϖ hΛ.1 M k B hB _ fun z hz a => hk _ (hz a trivial)), relIndex_ne_zero_of_finite _ _ (finite_image L hϖ hΛs.1 0 l _ (fun w hw a _ => by simpa using hw a) _ ?_), ?_, finite_image L hϖ hΛ.1 M e B hB _ ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨w, hw, rfl⟩ a`.

Conclude with `hl _ (smul_mem L (pow_mem L ϖ M) (hw a trivial))`. Introduce and unpack `_ ⟨y, hy, A, hA, rfl⟩ _ ⟨v, hv, rfl⟩`. Take `⟨h1, h2, h3⟩` from `horb y hy`. Take `⟨-, hAu, -, hAi, -⟩` from `hC A hA`. Take `⟨g, hg, hgc, A', hA', h⟩` from `hM y (rmul v A⁻¹) h1 h2 (rmul_mem L (fun a => hv a trivial) (hC _ hAi).1)`.

Use `⟨_, h3 g (hKN g hg hgc), A' * A, (hC _ hA').2.2.2.2.1 A hA, ?_⟩` and prove the remaining obligations. Rewrite using `[← rmul_rmul, ← h, rmul_add, rmul_smul, rmul_rmul, Matrix.nonsing_inv_mul _ hAu, rmul_one]`. Both sides reduce to the same expression. Introduce and unpack `_ ⟨y, hy, A, hA, rfl⟩ a`. Use `rmul_mem L (x := algebraMap F E ((ϖ : F) ^ e) • y) (horb y hy).1 (hC A hA).1 a` as an intermediate fact.

Rewrite `this` using `[rmul_smul]`. Then use the resulting hypothesis.
-/
theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λs, IsSD L Hm Λs → ∀ Λ, IsSD L Hm Λ → ∀ (m : ℕ) (Γ : Matrix (Fin m) (Fin m) E), IsUnit Γ.det → ∀ N e : ℕ, ∃ i0 : ℕ, 1 ≤ i0 ∧ ∀ i ≥ i0, ∀ K : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)), K ≤ isomG L Hm ⊓ stabL L Λ → (∀ g ∈ isomG L Hm, CongId L ϖ Λ N g → g ∈ K) → ∀ x : Fin m → Fin n → E, (∀ a, algebraMap F E ((ϖ : F) ^ e) • x a ∈ Λ) → gramT L Hm x = Γ → IsCO (tupLat L Λs m) (thick L ϖ (torb K x) i) ∧ (∀ y ∈ torb K x, ∀ A ∈ congK L ϖ m i, cT L A * Γ * A = Γ → rmul y A ∈ torb K x) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm hH Λs hΛs Λ hΛ m Γ hΓ N e
  obtain ⟨i1, hi1⟩ := GlobalTheory.T.exists_isometry_tupleMatrixRightMul_near_identity L ϖ hϖ Hm hH Λ hΛ m Γ hΓ N e
  refine ⟨i1 + 1, by omega, fun i hi K hK hKN x hx hG => ?_⟩
  have horb : ∀ y ∈ torb K x, (∀ a, algebraMap F E ((ϖ : F) ^ e) • y a ∈ Λ) ∧ gramT L Hm y = Γ ∧
      ∀ g ∈ K, (fun a => g (y a)) ∈ torb K x := by
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨fun a => ?_, ?_, fun g' hg' => ⟨g' * g, K.mul_mem hg' hg, rfl⟩⟩
    · have h : g • Λ = Λ := (hK hg).2
      rw [← map_smul, ← h]
      exact ⟨_, hx a, rfl⟩
    · rw [← hG]
      ext a b
      exact (hK hg).1 _ _
  refine ⟨?_, fun y hy A hA hA' => ?_⟩
  swap
  · obtain ⟨h1, h2, h3⟩ := horb y hy
    obtain ⟨g, hg, hgc, hgy⟩ := hi1 i (by omega) y h1 h2 A hA hA'
    rw [← funext hgy]
    exact h3 g (hKN g hg hgc)
  have hh : IsHerm L Γ := by
    rw [← hG]
    ext a b
    exact (GlobalTheory.HL.Model.hf_symm L hH.1 _ _).symm
  obtain ⟨M, hM⟩ := exists_close L hϖ hH hΛ hh hΓ N e i (by omega)
  obtain ⟨-, hC, -⟩ := GlobalTheory.T.matrixCongruentOneModUniformizerPow_group_and_orbits L ϖ hϖ m i (by omega)
  let B : AddSubgroup (Fin m → Fin n → E) :=
    (tupLat L Λ m).map (DistribMulAction.toAddMonoidHom _ (algebraMap F E ((ϖ : F) ^ M)))
  have hB : ∀ w : Fin m → Fin n → E, (∀ a, w a ∈ Λ) → algebraMap F E ((ϖ : F) ^ M) • w ∈ B :=
    fun w hw => ⟨w, fun a _ => hw a, rfl⟩
  obtain ⟨k, hk⟩ := exists_pow_le L hϖ hΛ.1 hΛs.1
  obtain ⟨l, hl⟩ := exists_pow_le L hϖ hΛs.1 hΛ.1
  refine ⟨B, relIndex_ne_zero_of_finite _ _ (finite_image L hϖ hΛ.1 M k B hB _
      fun z hz a => hk _ (hz a trivial)),
    relIndex_ne_zero_of_finite _ _ (finite_image L hϖ hΛs.1 0 l _
      (fun w hw a _ => by simpa using hw a) _ ?_), ?_, finite_image L hϖ hΛ.1 M e B hB _ ?_⟩
  · rintro _ ⟨w, hw, rfl⟩ a
    exact hl _ (smul_mem L (pow_mem L ϖ M) (hw a trivial))
  · rintro _ ⟨y, hy, A, hA, rfl⟩ _ ⟨v, hv, rfl⟩
    obtain ⟨h1, h2, h3⟩ := horb y hy
    obtain ⟨-, hAu, -, hAi, -⟩ := hC A hA
    obtain ⟨g, hg, hgc, A', hA', h⟩ := hM y (rmul v A⁻¹) h1 h2
      (rmul_mem L (fun a => hv a trivial) (hC _ hAi).1)
    refine ⟨_, h3 g (hKN g hg hgc), A' * A, (hC _ hA').2.2.2.2.1 A hA, ?_⟩
    rw [← rmul_rmul, ← h, rmul_add, rmul_smul, rmul_rmul, Matrix.nonsing_inv_mul _ hAu, rmul_one]
    rfl
  · rintro _ ⟨y, hy, A, hA, rfl⟩ a
    have := rmul_mem L (x := algebraMap F E ((ϖ : F) ^ e) • y) (horb y hy).1 (hC A hA).1 a
    rwa [rmul_smul] at this

end GlobalTheory.ThickOrbit
