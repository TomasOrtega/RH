import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimitiveVectorExtendsHyperbolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalOrderTwoPrimesAlmostAllStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalOrderVolumeAlmostAllStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorIntegerRingAlmostAllPlaces
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeGramScalarAlmostAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicSumNondegenerateFrameStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsLocalApproximateIdentity
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimLoc

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [JR, Matrix.map_apply]`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>`. Apply the tactic sequence `refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j <;>`. Simplify using `[hypOne]`.
-/
theorem JR_hypOne {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : JR (F := F) R (hypOne J) = hypOne (JR (F := F) R J) := by
  ext i j
  simp only [JR, Matrix.map_apply]
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j <;>
    simp [hypOne]

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

/- English proof (translation)
Rewrite using `[GoodTrans.mem_latV_iff b v O hO]`. Introduce `a i`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Simplify `O.one_mem` using `[e0]`. Simplify `O.zero_mem` using `[e0]`.
-/
theorem e0_mem_latV {d : ℕ} (M : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (O : Subring (Fv F v ⊗[F] E))
    (hO : ∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
      v.adicCompletionIntegers F) :
    (e0 (Fv F v ⊗[F] E) M : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) ∈ latV b v := by
  rw [GoodTrans.mem_latV_iff b v O hO]
  intro a i
  refine Fin.cases ?_ (fun i => ?_) i
  · simpa [e0] using O.one_mem
  · simpa [e0] using O.zero_mem

/- English proof (translation)
Introduce and unpack `y ⟨g, hg, rfl⟩`. Conclude with `(hg _).2 (e0_mem_latV M b v O hO)`.
-/
theorem primV_subset (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (O : Subring (Fv F v ⊗[F] E))
    (hO : ∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
      v.adicCompletionIntegers F) : primV σ J b v ⊆ latV b v := by
  rintro y ⟨g, hg, rfl⟩
  exact (hg _).2 (e0_mem_latV M b v O hO)

/- English proof (translation)
Set `h' : HA (Fv F v) σ J` to `(⟨g, hg⟩ : HR (Fv F v) σ J)`. Establish `hact : ∀ (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (a : Fin 1), actW (Fv F v) σ J h' X a = (g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) *ᵥ X a` using `fun _ _ => rfl`. Introduce `X`. Rewrite using `[GoodTrans.mem_latV_iff b v O hO, GoodTrans.mem_latV_iff b v O hO]`. Prove the components needed by the constructor for the conclusion.

Introduce `hX a i`. Establish `e : X a = ((g⁻¹ : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) _) *ᵥ ((g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) *ᵥ X a)`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`. Rewrite using `[e]`. Conclude with `GoodTrans.mulVec_mem O _ hgiO _ (fun j => by rw [← hact]; exact hX a j) i`.

Introduce `hX a i show (actW (Fv F v) σ J h' X a) i ∈ O`. Rewrite using `[hact]`. Conclude with `GoodTrans.mulVec_mem O _ hgO _ (hX a) i`.
-/
theorem latStab_of_integral (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (O : Subring (Fv F v ⊗[F] E))
    (hO : ∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
      v.adicCompletionIntegers F)
    (g : GL (Fin M) (Fv F v ⊗[F] E)) (hg : g ∈ HR (Fv F v) σ J)
    (hgO : ∀ i j, (g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) i j ∈ O)
    (hgiO : ∀ i j, ((g⁻¹ : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) _) i j ∈ O) :
    latStab σ J b v ((⟨g, hg⟩ : HR (Fv F v) σ J) : HA (Fv F v) σ J) := by
  let h' : HA (Fv F v) σ J := (⟨g, hg⟩ : HR (Fv F v) σ J)
  have hact : ∀ (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (a : Fin 1),
      actW (Fv F v) σ J h' X a = (g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) *ᵥ X a :=
    fun _ _ => rfl
  intro X
  rw [GoodTrans.mem_latV_iff b v O hO, GoodTrans.mem_latV_iff b v O hO]
  constructor
  · intro hX a i
    have e : X a = ((g⁻¹ : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) _) *ᵥ
        ((g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) *ᵥ X a) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e]
    exact GoodTrans.mulVec_mem O _ hgiO _ (fun j => by rw [← hact]; exact hX a j) i
  · intro hX a i
    show (actW (Fv F v) σ J h' X a) i ∈ O
    rw [hact]
    exact GoodTrans.mulVec_mem O _ hgO _ (hX a) i

/- English proof (translation)
Establish `hXO` using `(GoodTrans.mem_latV_iff b v O hO X).1 hX`. Set `x : Fin (M + 2) → O` to `fun i => ⟨X 0 i, hXO 0 i⟩`. Distinguish the cases in `hp : ∀ P : Ideal O, P.IsMaximal → ∃ i, x i ∉ P`. Use `left`. Establish `hJR : JR (F` using `F) (Fv F v) (hypOne J) = hypOne (JR (F := F) (Fv F v) J) := JR_hypOne _ J`.

Establish `hmulT : JR (F` using `F) (Fv F v) J * JR (F := F) (Fv F v) Ji = 1 := by`. Use `congrArg (RingHom.mapMatrix (inclR (Fv F v) (F := F) (E := E))) hmul` as an intermediate fact. Rewrite `this` using `[map_mul, map_one]`. Then use the resulting hypothesis. Take `⟨g, hgU, hgx, hgO, hgiO⟩` from `GlobalTheory.T.primitive_vector_extends_hyperbolic _ O (sigR (Fv F v) σ) hstab hss h2 hδ π₁ π₂ hπ M (JR (Fv F v) J) (JR (Fv F v) Ji) hJO hJiO hmulT (fun i j => by show sigR (Fv F v) σ (inclR (Fv F v) (J j i)) = inclR (Fv F v) (J i j)`. Rewrite using `[← hJs i j]`.

Use the proof step `rfl)`. Use `x hp (by rw [← hJR]; exact hg)`. Establish `hgH : g ∈ HR (Fv F v) σ (hypOne J)` using `by show g ∈ UJ (sigR (Fv F v) σ) (JR (Fv F v) (hypOne J))`. Rewrite using `[hJR]`. Conclude with `hgU`.

Use `⟨(⟨g, hgH⟩ : HR (Fv F v) σ (hypOne J)), latStab_of_integral σ (hypOne J) b v O hO g hgH hgO hgiO, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `a`. Rewrite using `[Fin.fin_one_eq_zero a]`. Conclude with `hgx`. Use `right push_neg at hp`.

Take `⟨P, hPm, hP⟩` from `hp`. Establish `aux : ∀ c : O, P = Ideal.span {c} → ¬ IsUnit c ∧ X ∈ (fun (Y : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) a i => (c : Fv F v ⊗[F] E) * Y a i) '' latV b v`. Introduce `c hc`. Use `⟨fun hu => hPm.ne_top (by rw [hc]; exact Ideal.span_singleton_eq_top.2 hu), ?_⟩` and prove the remaining obligations. Establish `hdiv : ∀ i, ∃ y : O, y * c = x i` using `fun i => by`.

Use `hP i` as an intermediate fact. Rewrite `this` using `[hc]`. Conclude with `Ideal.mem_span_singleton'.1 this`. Use `choose y hy using hdiv`. Use `⟨fun _ i => (y i : Fv F v ⊗[F] E), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[GoodTrans.mem_latV_iff b v O hO]`. Conclude with `fun _ i => (y i).2`. Use function extensionality and compare the values at `a i`. Rewrite using `[Fin.fin_one_eq_zero a]`. Use `congrArg Subtype.val (hy i)` as an intermediate fact.

Simplify using `only [Subring.coe_mul] at this`. Use `show (c : Fv F v ⊗[F] E) * (y i : Fv F v ⊗[F] E) = X 0 i`. Rewrite using `[mul_comm]`. Conclude with `this`. Break down `hπ P hPm with h | h` into its components or cases.

Conclude with `⟨π₁, Or.inl rfl, aux _ h⟩`. Conclude with `⟨π₂, Or.inr rfl, aux _ h⟩`.
-/
theorem cover_pt (σ : E →ₐ[F] E) {M d : ℕ} (J Ji : Matrix (Fin M) (Fin M) E) (hmul : J * Ji = 1)
    (hJs : ∀ i j, σ (J j i) = J i j)
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (O : Subring (Fv F v ⊗[F] E))
    (hO : ∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
      v.adicCompletionIntegers F)
    (hstab : ∀ y ∈ O, sigR (Fv F v) σ y ∈ O)
    (hss : ∀ y, sigR (Fv F v) σ (sigR (Fv F v) σ y) = y)
    (h2 : IsUnit (2 : O)) (hδ : ∃ δ : O, IsUnit δ ∧ sigR (Fv F v) σ δ = -δ)
    (π₁ π₂ : O) (hπ : ∀ P : Ideal O, P.IsMaximal → P = Ideal.span {π₁} ∨ P = Ideal.span {π₂})
    (hJO : ∀ i j, inclR (Fv F v) (J i j) ∈ O) (hJiO : ∀ i j, inclR (Fv F v) (Ji i j) ∈ O)
    (X : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) (hX : X ∈ latV b v)
    (hg : hform (sigR (Fv F v) σ) (JR (Fv F v) (hypOne J)) (X 0) (X 0) = 0) :
    X ∈ primV σ J b v ∨ ∃ c : O, (c = π₁ ∨ c = π₂) ∧ ¬ IsUnit c ∧
      X ∈ (fun (Y : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) a i => (c : Fv F v ⊗[F] E) * Y a i) ''
        latV b v := by
  classical
  have hXO := (GoodTrans.mem_latV_iff b v O hO X).1 hX
  let x : Fin (M + 2) → O := fun i => ⟨X 0 i, hXO 0 i⟩
  by_cases hp : ∀ P : Ideal O, P.IsMaximal → ∃ i, x i ∉ P
  · left
    have hJR : JR (F := F) (Fv F v) (hypOne J) = hypOne (JR (F := F) (Fv F v) J) := JR_hypOne _ J
    have hmulT : JR (F := F) (Fv F v) J * JR (F := F) (Fv F v) Ji = 1 := by
      have := congrArg (RingHom.mapMatrix (inclR (Fv F v) (F := F) (E := E))) hmul
      rwa [map_mul, map_one] at this
    obtain ⟨g, hgU, hgx, hgO, hgiO⟩ := GlobalTheory.T.primitive_vector_extends_hyperbolic _ O (sigR (Fv F v) σ) hstab hss h2 hδ π₁ π₂ hπ M
      (JR (Fv F v) J) (JR (Fv F v) Ji) hJO hJiO hmulT
      (fun i j => by
        show sigR (Fv F v) σ (inclR (Fv F v) (J j i)) = inclR (Fv F v) (J i j)
        rw [← hJs i j]
        rfl)
      x hp (by rw [← hJR]; exact hg)
    have hgH : g ∈ HR (Fv F v) σ (hypOne J) := by
      show g ∈ UJ (sigR (Fv F v) σ) (JR (Fv F v) (hypOne J))
      rw [hJR]; exact hgU
    refine ⟨(⟨g, hgH⟩ : HR (Fv F v) σ (hypOne J)),
      latStab_of_integral σ (hypOne J) b v O hO g hgH hgO hgiO, ?_⟩
    funext a
    rw [Fin.fin_one_eq_zero a]
    exact hgx
  · right
    push_neg at hp
    obtain ⟨P, hPm, hP⟩ := hp
    have aux : ∀ c : O, P = Ideal.span {c} → ¬ IsUnit c ∧
        X ∈ (fun (Y : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) a i => (c : Fv F v ⊗[F] E) * Y a i) ''
          latV b v := by
      intro c hc
      refine ⟨fun hu => hPm.ne_top (by rw [hc]; exact Ideal.span_singleton_eq_top.2 hu), ?_⟩
      have hdiv : ∀ i, ∃ y : O, y * c = x i := fun i => by
        have := hP i
        rw [hc] at this
        exact Ideal.mem_span_singleton'.1 this
      choose y hy using hdiv
      refine ⟨fun _ i => (y i : Fv F v ⊗[F] E), ?_, ?_⟩
      · rw [GoodTrans.mem_latV_iff b v O hO]
        exact fun _ i => (y i).2
      · funext a i
        rw [Fin.fin_one_eq_zero a]
        have := congrArg Subtype.val (hy i)
        simp only [Subring.coe_mul] at this
        show (c : Fv F v ⊗[F] E) * (y i : Fv F v ⊗[F] E) = X 0 i
        rw [mul_comm]
        exact this
    rcases hπ P hPm with h | h
    · exact ⟨π₁, Or.inl rfl, aux _ h⟩
    · exact ⟨π₂, Or.inr rfl, aux _ h⟩

end Place

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ h M J hJ hM d b`. Establish `hinv : ∀ x, σ (σ x) = x` using `fun x => by`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[h.2.2.2, h.2.2.2, star_star]`.

Establish `I` using `GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units F E σ h d b`. Establish `hH` using `(GlobalTheory.T.hyperbolic_sum_nondegenerate_frame F E σ h M J hJ).1`. Establish `hdet : IsUnit J.det` using `isUnit_iff_ne_zero.2 hJ.2`. Use `filter_upwards [GlobalTheory.CompanionTheory.SW.GoodRing.good_ring F E σ h d b, GlobalTheory.T.local_order_two_primes_almost_all F E σ h d b, GlobalTheory.T.local_order_volume_almost_all F E σ h (M + 2) (hypOne J) hH (by omega) d b, Filter.eventually_all.2 fun i => Filter.eventua …`. Take `⟨O, hO, hstab, -, h2, hδ, -, -⟩` from `hring`.

Take `⟨π₁, π₂, hπ, hu₁, hu₂⟩` from `h36 O hO`. Use `⟨primV_subset σ J b v O hO, ?_⟩` and prove the remaining obligations. Introduce `lam hlam m hm h₂`. Establish `hss : ∀ z : Fv F v ⊗[F] E, sigR (Fv F v) σ (sigR (Fv F v) σ z) = z`. Introduce `z`.

Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e => show a ⊗ₜ[F] σ (σ e) = a ⊗ₜ[F] e`. Rewrite using `[hinv]`. Consider the case `add p q hp hq => rw [map_add, map_add, hp, hq]`.

Establish `hmeas : MeasurableSet (latV b v : Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E))` using `GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.measurableSet_latV σ h b 1 (M + 2) v`. Use `set H := hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂ with hHdef`. Establish `hnull` using `hm.1 H`. Use `set Z : Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) := (gramR (Fv F v) σ (hypOne J) ⁻¹' {(H : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E))} ∩ {X | LinearIndependent (Fv F v ⊗[F] E) X})ᶜ with hZ`. Establish `hnull' : m H Z = 0` using `hnull`.

Set `Sc : O → Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E)` to `fun c => {X | ¬ IsUnit c ∧ X ∈ (fun (Y : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) a i => (c : Fv F v ⊗[F] E) * Y a i) '' latV b v}`. Establish `hbd : ∀ c : O, IsUnit (c : Fv F v ⊗[F] E) → m H (Sc c) ≤ ENNReal.ofReal (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) * m H (latV b v)`. Introduce `c hc`. Distinguish the cases in `hu : IsUnit c`. Establish `: Sc c = ∅` using `Set.eq_empty_of_forall_notMem fun X hX => hX.1 hu`.

Rewrite using `[this, measure_empty]`. Simplify using the standard rewrite rules. Conclude with `(measure_mono fun X hX => hX.2).trans (h37 O hO lam hlam m hm h₂ c hu hc _ hmeas)`. Establish `hcov : (latV b v : Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E)) ⊆ ((primV σ J b v ∪ Sc π₁) ∪ Sc π₂) ∪ Z`. Introduce `X hX`.

Distinguish the cases in `hXZ : X ∈ Z`. Conclude with `Or.inr hXZ`. Use `left`. Establish `hgr : gramR (Fv F v) σ (hypOne J) X = (H : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E))`. Simplify using `only [hZ, Set.mem_compl_iff, not_not] at hXZ`.

Conclude with `hXZ.1`. Establish `hg : hform (sigR (Fv F v) σ) (JR (Fv F v) (hypOne J)) (X 0) (X 0) = 0`. Use `congrFun (congrFun hgr 0) 0` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations. Simplify using `[hHdef, hermOf]`.

Break down `cover_pt σ J J⁻¹ (Matrix.mul_nonsing_inv _ hdet) hJ.1 b v O hO hstab hss h2 hδ π₁ π₂ hπ (fun i j => (hO _).2 (hJv i j)) (fun i j => (hO _).2 (hJiv i j)) X hX hg with hp | ⟨c, hc, hn, hi⟩` into its components or cases. Conclude with `Or.inl (Or.inl hp)`. Break down `hc with rfl | rfl` into its components or cases. Conclude with `Or.inl (Or.inr ⟨hn, hi⟩)`. Conclude with `Or.inr ⟨hn, hi⟩`.

Establish `hN : ENNReal.ofReal (2 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) = ENNReal.ofReal (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) + ENNReal.ofReal (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2)`. Rewrite using `[← ENNReal.ofReal_add (by positivity) (by positivity)]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation.

Conclude with `hbd _ hu₁`. Conclude with `hbd _ hu₂`. Use `_ = m H (primV σ J b v) + ENNReal.ofReal (2 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) * m H (latV b v) := by`. Rewrite using `[hN, add_mul, add_assoc]`.
-/
theorem prim_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, primV σ J b v ⊆ latV b v ∧ ∀ lam : Measure (Fv F v), IsStdV v lam → ∀ m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E), IsGramFibFree (Fv F v) σ (hypOne J) 1 (coordW (Fv F v) b lam 1 (M + 2)) (coordHerm (Fv F v) σ b lam 1) m → ∀ h₂ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b, m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (latV b v) ≤ m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (primV σ J b v) + ENNReal.ofReal (2 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) * m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (latV b v) := by
  intro F E _ _ _ _ _ σ h M J hJ hM d b
  have hinv : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  have I := GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units F E σ h d b
  have hH := (GlobalTheory.T.hyperbolic_sum_nondegenerate_frame F E σ h M J hJ).1
  have hdet : IsUnit J.det := isUnit_iff_ne_zero.2 hJ.2
  filter_upwards [GlobalTheory.CompanionTheory.SW.GoodRing.good_ring F E σ h d b, GlobalTheory.T.local_order_two_primes_almost_all F E σ h d b,
    GlobalTheory.T.local_order_volume_almost_all F E σ h (M + 2) (hypOne J) hH (by omega) d b,
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => I.1 (J i j),
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => I.1 (J⁻¹ i j)]
    with v hring h36 h37 hJv hJiv
  obtain ⟨O, hO, hstab, -, h2, hδ, -, -⟩ := hring
  obtain ⟨π₁, π₂, hπ, hu₁, hu₂⟩ := h36 O hO
  refine ⟨primV_subset σ J b v O hO, ?_⟩
  intro lam hlam m hm h₂
  have hss : ∀ z : Fv F v ⊗[F] E, sigR (Fv F v) σ (sigR (Fv F v) σ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      show a ⊗ₜ[F] σ (σ e) = a ⊗ₜ[F] e
      rw [hinv]
    | add p q hp hq => rw [map_add, map_add, hp, hq]
  have hmeas : MeasurableSet (latV b v : Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E)) :=
    GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.measurableSet_latV σ h b 1 (M + 2) v
  set H := hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂ with hHdef
  have hnull := hm.1 H
  set Z : Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) :=
    (gramR (Fv F v) σ (hypOne J) ⁻¹' {(H : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E))} ∩
      {X | LinearIndependent (Fv F v ⊗[F] E) X})ᶜ with hZ
  have hnull' : m H Z = 0 := hnull
  let Sc : O → Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) := fun c =>
    {X | ¬ IsUnit c ∧ X ∈ (fun (Y : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) a i =>
      (c : Fv F v ⊗[F] E) * Y a i) '' latV b v}
  have hbd : ∀ c : O, IsUnit (c : Fv F v ⊗[F] E) → m H (Sc c) ≤
      ENNReal.ofReal (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) * m H (latV b v) := by
    intro c hc
    by_cases hu : IsUnit c
    · have : Sc c = ∅ := Set.eq_empty_of_forall_notMem fun X hX => hX.1 hu
      rw [this, measure_empty]
      simp
    · exact (measure_mono fun X hX => hX.2).trans (h37 O hO lam hlam m hm h₂ c hu hc _ hmeas)
  have hcov : (latV b v : Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E)) ⊆
      ((primV σ J b v ∪ Sc π₁) ∪ Sc π₂) ∪ Z := by
    intro X hX
    by_cases hXZ : X ∈ Z
    · exact Or.inr hXZ
    · left
      have hgr : gramR (Fv F v) σ (hypOne J) X = (H : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) := by
        simp only [hZ, Set.mem_compl_iff, not_not] at hXZ
        exact hXZ.1
      have hg : hform (sigR (Fv F v) σ) (JR (Fv F v) (hypOne J)) (X 0) (X 0) = 0 := by
        have := congrFun (congrFun hgr 0) 0
        refine this.trans ?_
        simp [hHdef, hermOf]
      rcases cover_pt σ J J⁻¹ (Matrix.mul_nonsing_inv _ hdet) hJ.1 b v O hO hstab hss h2 hδ π₁ π₂ hπ
        (fun i j => (hO _).2 (hJv i j)) (fun i j => (hO _).2 (hJiv i j)) X hX hg with hp | ⟨c, hc, hn, hi⟩
      · exact Or.inl (Or.inl hp)
      · rcases hc with rfl | rfl
        · exact Or.inl (Or.inr ⟨hn, hi⟩)
        · exact Or.inr ⟨hn, hi⟩
  have hN : ENNReal.ofReal (2 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) =
      ENNReal.ofReal (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) +
        ENNReal.ofReal (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  calc m H (latV b v) ≤ m H (((primV σ J b v ∪ Sc π₁) ∪ Sc π₂) ∪ Z) := measure_mono hcov
    _ ≤ m H ((primV σ J b v ∪ Sc π₁) ∪ Sc π₂) + m H Z := measure_union_le _ _
    _ = m H ((primV σ J b v ∪ Sc π₁) ∪ Sc π₂) := by rw [hnull', add_zero]
    _ ≤ m H (primV σ J b v ∪ Sc π₁) + m H (Sc π₂) := measure_union_le _ _
    _ ≤ m H (primV σ J b v) + m H (Sc π₁) + m H (Sc π₂) := by gcongr; exact measure_union_le _ _
    _ ≤ m H (primV σ J b v) + ENNReal.ofReal (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) * m H (latV b v) +
        ENNReal.ofReal (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) * m H (latV b v) := by
      gcongr
      · exact hbd _ hu₁
      · exact hbd _ hu₂
    _ = m H (primV σ J b v) + ENNReal.ofReal (2 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) * m H (latV b v) := by
      rw [hN, add_mul, add_assoc]

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimLoc
