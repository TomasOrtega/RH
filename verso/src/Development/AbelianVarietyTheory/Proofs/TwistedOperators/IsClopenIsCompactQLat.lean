import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DualLiftInvariance
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairOperatorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClopenIsCompactMapsPair

open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData

noncomputable section
namespace GlobalTheory.LastSteps

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' n'' : Type}

section Duals

/- English proof (translation)
Set `f : Red L →ₗ[𝒪[k]] 𝓀[k]` to `(maximalIdeal 𝒪[k] • ⊤ : Submodule 𝒪[k] L).liftQ F (Submodule.smul_le.2 fun s hs x _ => by`. Rewrite using `[LinearMap.mem_ker, map_smul, Algebra.smul_def, ResidueField.algebraMap_eq, (residue_eq_zero_iff s).2 hs, zero_mul])`. Conclude with `⟨f.extendScalarsOfSurjective residue_surjective, fun _ => rfl⟩`.
-/
theorem exists_dual (L : Submodule 𝒪[k] (n → k)) (F : L →ₗ[𝒪[k]] 𝓀[k]) :
    ∃ f : Module.Dual 𝓀[k] (Red L), ∀ z, f (Red.mk L z) = F z := by
  let f : Red L →ₗ[𝒪[k]] 𝓀[k] :=
    (maximalIdeal 𝒪[k] • ⊤ : Submodule 𝒪[k] L).liftQ F (Submodule.smul_le.2 fun s hs x _ => by
      rw [LinearMap.mem_ker, map_smul, Algebra.smul_def, ResidueField.algebraMap_eq,
        (residue_eq_zero_iff s).2 hs, zero_mul])
  exact ⟨f.extendScalarsOfSurjective residue_surjective, fun _ => rfl⟩

/- English proof (translation)
The claim follows from `LinearMap.ext fun x => by obtain ⟨z, rfl⟩ := Red.mk_surjective L x exact h z`.
-/
theorem dual_ext {L : Submodule 𝒪[k] (n → k)} {f g : Module.Dual 𝓀[k] (Red L)}
    (h : ∀ z, f (Red.mk L z) = g (Red.mk L z)) : f = g :=
  LinearMap.ext fun x => by
    obtain ⟨z, rfl⟩ := Red.mk_surjective L x
    exact h z

/- English proof (translation)
Use `letI := Fintype.ofFinite V`. Rewrite using `[finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Fintype.sum_eq_add_sum_subtype_ne F 0]`.
-/
theorem finsum_split {V A : Type} [Finite V] [Zero V] [AddCommMonoid A] (F : V → A) :
    ∑ᶠ v, F v = F 0 + ∑ᶠ v : {v : V // v ≠ 0}, F v := by
  classical
  letI := Fintype.ofFinite V
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Fintype.sum_eq_add_sum_subtype_ne F 0]

/- English proof (translation)
Use `letI := Fintype.ofFinite {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}`. Rewrite using `[finsum_eq_sum_of_fintype, sum_withLat]`.
-/
theorem finsum_ofDual {A : Type} [AddCommMonoid A] (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] (F : Pair k n → A) :
    ∑ᶠ f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}, F (ofDual L f) = ∑ P ∈ withLat L, F P := by
  letI := Fintype.ofFinite {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}
  rw [finsum_eq_sum_of_fintype, sum_withLat]

/- English proof (translation)
Take `⟨q⟩ : Nonempty (Unif k)` from `inferInstance`. Use `letI := Fintype.ofFinite {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}`. Use `letI := Fintype.ofFinite {x : Red L // x ≠ 0}`. Set `e : Red L ≃ₗ[𝓀[k]] Module.Dual 𝓀[k] (Red L)` to `LinearEquiv.ofFinrankEq _ _ Subspace.dual_finrank_eq.symm`. Rewrite using `[Finset.card_eq_sum_ones, Finset.card_eq_sum_ones, sum_withKer L q, sum_withLat]`.

Conclude with `Fintype.sum_equiv (e.toEquiv.subtypeEquiv fun x => by simp) _ _ fun _ => rfl`.
-/
theorem card_withKer (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] : (withKer L).card = (withLat L).card := by
  obtain ⟨q⟩ : Nonempty (Unif k) := inferInstance
  letI := Fintype.ofFinite {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}
  letI := Fintype.ofFinite {x : Red L // x ≠ 0}
  let e : Red L ≃ₗ[𝓀[k]] Module.Dual 𝓀[k] (Red L) := LinearEquiv.ofFinrankEq _ _ Subspace.dual_finrank_eq.symm
  rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones, sum_withKer L q, sum_withLat]
  exact Fintype.sum_equiv (e.toEquiv.subtypeEquiv fun x => by simp) _ _ fun _ => rfl

variable [Fintype n] {L : Submodule 𝒪[k] (n → k)} {F : n → k}

/- English proof (translation)
Introduce `y hy` and use `by obtain ⟨s, hs, -⟩ := h ⟨y, hy⟩ exact hs ▸ s.2`.
-/
theorem inDual_of_lifts {f : Module.Dual 𝓀[k] (Red L)} (h : Lifts L F f) : InDual L F := fun y hy => by
  obtain ⟨s, hs, -⟩ := h ⟨y, hy⟩
  exact hs ▸ s.2

/- English proof (translation)
The claim follows from `dual_ext fun z => by obtain ⟨s, hs, e⟩ := h z obtain ⟨t, ht, e'⟩ := h' z rw [← e, ← e', Subtype.ext (hs.trans ht.symm)]`.
-/
theorem lifts_unique {f g : Module.Dual 𝓀[k] (Red L)} (h : Lifts L F f) (h' : Lifts L F g) : f = g :=
  dual_ext fun z => by
    obtain ⟨s, hs, e⟩ := h z
    obtain ⟨t, ht, e'⟩ := h' z
    rw [← e, ← e', Subtype.ext (hs.trans ht.symm)]

/- English proof (translation)
Set `G : L →ₗ[𝒪[k]] 𝒪[k]` to `{ toFun := fun y => ⟨F ⬝ᵥ y, h y y.2⟩ map_add' := fun y z => Subtype.ext (by simp [dotProduct_add]) map_smul' := fun s y => Subtype.ext (dotProduct_smul s F (y : n → k)) }`. Take `⟨f, hf⟩` from `exists_dual L (Algebra.linearMap 𝒪[k] 𝓀[k] ∘ₗ G)`. Conclude with `⟨f, fun y => ⟨G y, rfl, (hf y).symm⟩⟩`.
-/
theorem exists_lifts (h : InDual L F) : ∃ f, Lifts L F f := by
  let G : L →ₗ[𝒪[k]] 𝒪[k] :=
    { toFun := fun y => ⟨F ⬝ᵥ y, h y y.2⟩
      map_add' := fun y z => Subtype.ext (by simp [dotProduct_add])
      map_smul' := fun s y => Subtype.ext (dotProduct_smul s F (y : n → k)) }
  obtain ⟨f, hf⟩ := exists_dual L (Algebra.linearMap 𝒪[k] 𝓀[k] ∘ₗ G)
  exact ⟨f, fun y => ⟨G y, rfl, (hf y).symm⟩⟩

open Classical in

/- English proof (translation)
Use `if_congr ⟨fun ⟨F, hF, hD⟩ y => ?_, fun h => ⟨_, h, fun y _ => by simp⟩⟩ rfl rfl` and prove the remaining obligations. Take `⟨s, hs, e⟩` from `hF y`. Use `⟨s + q.1 * ⟨_, hD y y.2⟩, ?_, ?_⟩` and prove the remaining obligations. Establish `: q.1 • η = F + q.1 • (η - q.inv • F)` using `by rw [smul_sub, q.smul_inv_smul]; abel`. Rewrite using `[this, add_dotProduct, smul_dotProduct, ← hs]`.

Both sides reduce to the same expression. Rewrite using `[map_add, map_mul, (residue_eq_zero_iff _).2 q.mem_max, zero_mul, add_zero, e]`.
-/
theorem cosetInd_eq (q : Unif k) (f : Module.Dual 𝓀[k] (Red L)) (η : n → k) :
    cosetInd q L f η = if Lifts L (q.1 • η) f then 1 else 0 := by
  refine if_congr ⟨fun ⟨F, hF, hD⟩ y => ?_, fun h => ⟨_, h, fun y _ => by simp⟩⟩ rfl rfl
  obtain ⟨s, hs, e⟩ := hF y
  refine ⟨s + q.1 * ⟨_, hD y y.2⟩, ?_, ?_⟩
  · have : q.1 • η = F + q.1 • (η - q.inv • F) := by rw [smul_sub, q.smul_inv_smul]; abel
    rw [this, add_dotProduct, smul_dotProduct, ← hs]
    rfl
  · rw [map_add, map_mul, (residue_eq_zero_iff _).2 q.mem_max, zero_mul, add_zero, e]

end Duals

section Decomposition
variable [Fintype n'] {L : Submodule 𝒪[k] (n' → k)} {LY : Submodule 𝒪[k] (n → k)} {x₀ : Matrix n n' k}

open Classical in

/- English proof (translation)
Take `⟨f₀, hf⟩` from `exists_dual L (fW.restrictScalars 𝒪[k] ∘ₗ Red.mk LY ∘ₗ ((mulVecLin x₀).restrictScalars 𝒪[k]).restrict h)`. Establish `hf' : ∀ z : L, f₀ (Red.mk L z) = fW (Red.mk LY ⟨x₀ *ᵥ z, h z z.2⟩)` using `hf`. Use `⟨f₀, hf', fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[finsum_eq_single _ f₀ fun f' hne => ?_, compInd, if_pos ⟨h, fun z => (hf' z).symm⟩, mul_one]`. Rewrite using `[compInd, if_neg, mul_zero]`.

Introduce and unpack `⟨_, h'⟩`. Conclude with `hne (dual_ext fun z => (h' z).symm.trans (hf' z).symm)`.
-/
theorem exists_pull (h : ∀ z ∈ L, x₀ *ᵥ z ∈ LY) (fW : Module.Dual 𝓀[k] (Red LY)) :
    ∃ f₀ : Module.Dual 𝓀[k] (Red L), (∀ z : L, f₀ (Red.mk L z) = fW (Red.mk LY ⟨x₀ *ᵥ z, h z z.2⟩)) ∧
      ∀ w : Module.Dual 𝓀[k] (Red L) → ℂ, ∑ᶠ f', w f' * compInd L LY f' fW x₀ = w f₀ := by
  obtain ⟨f₀, hf⟩ := exists_dual L (fW.restrictScalars 𝒪[k] ∘ₗ Red.mk LY ∘ₗ
    ((mulVecLin x₀).restrictScalars 𝒪[k]).restrict h)
  have hf' : ∀ z : L, f₀ (Red.mk L z) = fW (Red.mk LY ⟨x₀ *ᵥ z, h z z.2⟩) := hf
  refine ⟨f₀, hf', fun w => ?_⟩
  rw [finsum_eq_single _ f₀ fun f' hne => ?_, compInd, if_pos ⟨h, fun z => (hf' z).symm⟩, mul_one]
  rw [compInd, if_neg, mul_zero]
  rintro ⟨_, h'⟩
  exact hne (dual_ext fun z => (h' z).symm.trans (hf' z).symm)

/- English proof (translation)
The claim follows from `if_neg fun h' => h h'.1`.
-/
theorem compInd_of_not (h : ¬ ∀ z ∈ L, x₀ *ᵥ z ∈ LY) (f' : Module.Dual 𝓀[k] (Red L))
    (fW : Module.Dual 𝓀[k] (Red LY)) : compInd L LY f' fW x₀ = 0 := if_neg fun h' => h h'.1

/- English proof (translation)
Distinguish the cases in `h : ∀ z ∈ L, x₀ *ᵥ z ∈ LY`. Take `⟨f₀, -, hf⟩` from `exists_pull h fW`. Simplify `(hf fun _ => 1).symm` using `[latInd, if_pos h]`. Simplify using `[compInd_of_not h, latInd, if_neg h]`.
-/
theorem latInd_eq_finsum (fW : Module.Dual 𝓀[k] (Red LY)) :
    latInd L LY x₀ = ∑ᶠ f' : Module.Dual 𝓀[k] (Red L), compInd L LY f' fW x₀ := by
  by_cases h : ∀ z ∈ L, x₀ *ᵥ z ∈ LY
  · obtain ⟨f₀, -, hf⟩ := exists_pull h fW
    simpa [latInd, if_pos h] using (hf fun _ => 1).symm
  · simp [compInd_of_not h, latInd, if_neg h]

variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (ε : 𝓀[k]ˣ) (P : Pair k n')

/- English proof (translation)
Distinguish the cases in `h : ∀ z ∈ P.ker, x₀ *ᵥ z ∈ LY`. Take `⟨f₀, h0, hf⟩` from `exists_pull h fW`. Rewrite using `[hf fun f' => χ (-((ε : 𝓀[k]) * f' (qvec q P))), term, dif_pos h, qvec, h0]`. Simplify using `[compInd_of_not h, term, dif_neg h]`.
-/
theorem term_eq_finsum (fW : Module.Dual 𝓀[k] (Red LY)) :
    term q χ ε P LY fW x₀ = ∑ᶠ f' : Module.Dual 𝓀[k] (Red P.ker),
      χ (-((ε : 𝓀[k]) * f' (qvec q P))) * compInd P.ker LY f' fW x₀ := by
  by_cases h : ∀ z ∈ P.ker, x₀ *ᵥ z ∈ LY
  · obtain ⟨f₀, h0, hf⟩ := exists_pull h fW
    rw [hf fun f' => χ (-((ε : 𝓀[k]) * f' (qvec q P))), term, dif_pos h, qvec, h0]
  · simp [compInd_of_not h, term, dif_neg h]

/- English proof (translation)
Use extensionality with `x₀`. Distinguish the cases in `h : ∀ z ∈ P.ker, x₀ *ᵥ z ∈ LY`. Simplify using `[term, dif_pos h, latInd, if_pos h]`. Simplify using `[term, dif_neg h, latInd, if_neg h]`.
-/
theorem term_zero : term q χ ε P LY 0 = latInd P.ker LY := by
  ext x₀
  by_cases h : ∀ z ∈ P.ker, x₀ *ᵥ z ∈ LY
  · simp [term, dif_pos h, latInd, if_pos h]
  · simp [term, dif_neg h, latInd, if_neg h]

variable [LY.IsLattice k] (fW : {f : Module.Dual 𝓀[k] (Red LY) // f ≠ 0})

/- English proof (translation)
Use extensionality with `x₀`. Conclude with `if_congr ⟨fun ⟨h, h'⟩ y hy => Pair.mem_ker.2 ⟨h y hy, h' ⟨y, hy⟩⟩, fun h => ⟨fun y hy => (Pair.mem_ker.1 (h y hy)).1, fun z => (Pair.mem_ker.1 (h z z.2)).2⟩⟩ rfl rfl`.
-/
theorem compInd_zero : compInd L LY 0 fW.1 = latInd L (ofDual LY fW).ker := by
  ext x₀
  classical
  exact if_congr ⟨fun ⟨h, h'⟩ y hy => Pair.mem_ker.2 ⟨h y hy, h' ⟨y, hy⟩⟩, fun h =>
    ⟨fun y hy => (Pair.mem_ker.1 (h y hy)).1, fun z => (Pair.mem_ker.1 (h z z.2)).2⟩⟩ rfl rfl

/- English proof (translation)
Use extensionality with `x₀`. Conclude with `if_congr Iff.rfl rfl rfl`.
-/
theorem compInd_eq_phiOne [L.IsLattice k] (f' : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}) :
    compInd L LY f'.1 fW.1 = phiOne (ofDual L f') (ofDual LY fW) := by
  ext x₀
  classical
  exact if_congr Iff.rfl rfl rfl

/- English proof (translation)
Use extensionality with `x₀`. Rewrite using `[term_eq_finsum, finsum_split, compInd_zero, Pi.add_apply]`. Simplify using `only [LinearMap.zero_apply, mul_zero, neg_zero, AddChar.map_zero_eq_one, one_mul, compInd_eq_phiOne]`. Both sides reduce to the same expression.
-/
theorem term_ne_zero : term q χ ε P LY fW.1 =
    latInd P.ker (ofDual LY fW).ker + mainDatum q χ ε P (ofDual LY fW) := by
  ext x₀
  rw [term_eq_finsum, finsum_split, compInd_zero, Pi.add_apply]
  simp only [LinearMap.zero_apply, mul_zero, neg_zero, AddChar.map_zero_eq_one, one_mul,
    compInd_eq_phiOne]
  rfl

/- English proof (translation)
Use extensionality with `x₀`. Rewrite using `[Finset.sum_apply, ← finsum_ofDual]`. Use `finsum_congr fun f' => ?_` and prove the remaining obligations. Rewrite using `[(cross_hasVal q (P := ofDual P.ker f') rfl P.hasVal_vec).unique (ofDual_hasVal P.ker f' ⟨_, _⟩)]`. Both sides reduce to the same expression.
-/
theorem mainDatum_eq (Q : Pair k n) : mainDatum q χ ε P Q =
    ∑ P' ∈ withLat P.ker, χ (-((ε : 𝓀[k]) * cross q P P')) • phiOne P' Q := by
  ext x₀
  rw [Finset.sum_apply, ← finsum_ofDual]
  refine finsum_congr fun f' => ?_
  rw [(cross_hasVal q (P := ofDual P.ker f') rfl P.hasVal_vec).unique (ofDual_hasVal P.ker f' ⟨_, _⟩)]
  rfl

variable {M A : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup A] [Module ℂ A]

/- English proof (translation)
Rewrite using `[dia_apply, FFStar_apply]`. Conclude with `Finset.sum_congr rfl fun P hP => by rw [cross_dia_right q (mem_withKer.1 hP).symm]`.
-/
theorem dia_FFStar (φ : Form k n' M) (P' : Pair k n') :
    dia ε (FFStar q χ φ) P' = ∑ P ∈ withKer P'.lat, χ (-((ε : 𝓀[k]) * cross q P P')) • φ P := by
  rw [dia_apply, FFStar_apply]
  exact Finset.sum_congr rfl fun P hP => by rw [cross_dia_right q (mem_withKer.1 hP).symm]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun P hP => ?_` and prove the remaining obligations. Rewrite using `[mainDatum_eq, mem_withKer.1 hP, Finset.sum_apply, Finset.sum_smul]`. Conclude with `Finset.sum_congr rfl fun P' _ => by rw [Pi.smul_apply, smul_eq_mul, mul_comm, mul_smul]`. Use `_ = _ := by`.

Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun P' hP' => by rw [dia_FFStar, mem_withLat.1 hP', Finset.smul_sum]`.
-/
theorem sum_mainDatum (L : Submodule 𝒪[k] (n' → k)) (Q : Pair k n) (φ : Form k n' M) (x₀ : Matrix n n' k) :
    ∑ P ∈ withKer L, mainDatum q χ ε P Q x₀ • φ P =
      ∑ P' ∈ withLat L, phiOne P' Q x₀ • dia ε (FFStar q χ φ) P' := by
  calc _ = ∑ P ∈ withKer L, ∑ P' ∈ withLat L, phiOne P' Q x₀ • χ (-((ε : 𝓀[k]) * cross q P P')) • φ P := by
        refine Finset.sum_congr rfl fun P hP => ?_
        rw [mainDatum_eq, mem_withKer.1 hP, Finset.sum_apply, Finset.sum_smul]
        exact Finset.sum_congr rfl fun P' _ => by rw [Pi.smul_apply, smul_eq_mul, mul_comm, mul_smul]
    _ = _ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun P' hP' => by rw [dia_FFStar, mem_withLat.1 hP', Finset.smul_sum]

variable [DecidableEq n'] [Fintype n]

/- English proof (translation)
Use `latInd_smul (x := x₀) g 1 L L₁` as an intermediate fact. Rewrite `this` using `[MulAction.mem_stabilizer_iff.1 hg, one_smul]`. Simplify using `using this.symm`.
-/
theorem latInd_mul {g : GL n' k} (hg : g ∈ latStab L) (L₁ : Submodule 𝒪[k] (n → k)) (x₀ : Matrix n n' k) :
    latInd L L₁ (x₀ * g.val) = latInd L L₁ x₀ := by
  classical
  have := latInd_smul (x := x₀) g 1 L L₁
  rw [MulAction.mem_stabilizer_iff.1 hg, one_smul] at this
  simpa using this.symm

omit [Fintype n] in

/- English proof (translation)
Take `⟨q⟩ : Nonempty (Unif k)` from `inferInstance`. Rewrite using `[Finset.sum_congr rfl fun P₁ h => by rw [mem_withKer.1 h], ← Finset.smul_sum, ← trKer_apply, (PairOp.vanishing q).trKer_eq_zero φ hφ L, smul_zero]`.
-/
theorem sum_latInd {φ : Form k n' M} (hφ : φ ∈ Mram k n' M) (L : Submodule 𝒪[k] (n' → k)) [L.IsLattice k]
    (L₁ : Submodule 𝒪[k] (n → k)) (x₀ : Matrix n n' k) : ∑ P₁ ∈ withKer L, latInd P₁.ker L₁ x₀ • φ P₁ = 0 := by
  obtain ⟨q⟩ : Nonempty (Unif k) := inferInstance
  rw [Finset.sum_congr rfl fun P₁ h => by rw [mem_withKer.1 h], ← Finset.smul_sum, ← trKer_apply,
    (PairOp.vanishing q).trKer_eq_zero φ hφ L, smul_zero]

variable {π : Representation ℂ (GL n' k) M} {θ : M →ₗ[ℂ] (Matrix n n' k → ℂ) →ₗ[ℂ] A} {φ : Form k n' M}

/- English proof (translation)
Take `⟨q⟩ : Nonempty (Unif k)` from `inferInstance`. Establish `hv : formOf π P (evalEquiv π P ⟨φ, he⟩) = φ` using `congrArg Subtype.val ((evalEquiv π P).left_inv ⟨φ, he⟩)`. Use `(PairOp.vanishing q).invariant_eq_zero π P (evalEquiv π P ⟨φ, he⟩) (hv.symm ▸ hφ) A (θ.flip (latInd P.ker L₁)) (Or.inr fun g hg w => ?_)` and prove the remaining obligations. Use `hθ g hg w _ (latInd_mem_SB P.ker L₁)` as an intermediate fact. Simplify using `only [latInd_mul hg] at this`.

Conclude with `this`.
-/
theorem lift_latInd (hφ : φ ∈ Mram k n' M) (he : φ ∈ EqForm π) (hθ : IsLiftInv π θ P.ker)
    (L₁ : Submodule 𝒪[k] (n → k)) [L₁.IsLattice k] : θ (φ P) (latInd P.ker L₁) = 0 := by
  obtain ⟨q⟩ : Nonempty (Unif k) := inferInstance
  have hv : formOf π P (evalEquiv π P ⟨φ, he⟩) = φ := congrArg Subtype.val ((evalEquiv π P).left_inv ⟨φ, he⟩)
  refine (PairOp.vanishing q).invariant_eq_zero π P (evalEquiv π P ⟨φ, he⟩) (hv.symm ▸ hφ) A
    (θ.flip (latInd P.ker L₁)) (Or.inr fun g hg w => ?_)
  have := hθ g hg w _ (latInd_mem_SB P.ker L₁)
  simp only [latInd_mul hg] at this
  exact this

/- English proof (translation)
Set `T : Pair k n' → Pair k n' → A` to `fun P₁ P₂ => χ (-((ε : 𝓀[k]) * cross q P₁ P₂)) • θ (φ P₁) (phiOne P₂ Q)`. Establish `hT : ∀ g : GL n' k, g • L = L → ∀ P₁ P₂, P₁.ker = L → P₂.lat = L → T (g • P₁) (g • P₂) = T P₁ P₂`. Introduce `g hg P₁ P₂ h₁ h₂`. Establish `h3 : phiOne (g • P₂) Q = fun x => phiOne P₂ Q (x * g.val)` using `funext fun x => by`. Simplify using `using phiOne_smul (P := P₂) (Q := Q) (x := x) g 1`.

Simplify using `only [T]`. Rewrite using `[cross_smul q (h₂.trans h₁.symm), he g P₁, h3, hθ g hg _ _ (phiOne_mem_SB P₂ Q)]`. Establish `h1 : ∀ P₁ ∈ withKer L, ∑ P₂ ∈ withLat L, T P₁ P₂ = ∑ P₂ ∈ withLat L, T P P₂` using `fun P₁ h => by`. Take `⟨g, rfl⟩` from `MulAction.exists_smul_eq (GL n' k) P P₁`. Establish `hg : g • L = L` using `by simpa [hP] using h`.

Use `conv_lhs => rw [← hg, sum_withLat_smul]`. Conclude with `Finset.sum_congr rfl fun P₂ h₂ => hT g hg _ _ hP (mem_withLat.1 h₂)`. Establish `h2 : ∀ P₂ ∈ withLat L, ∑ P₁ ∈ withKer L, T P₁ P₂ = ∑ P₁ ∈ withKer L, T P₁ P'` using `fun P₂ h => by`. Take `⟨g, rfl⟩` from `MulAction.exists_smul_eq (GL n' k) P' P₂`. Establish `hg : g • L = L` using `by simpa [hP'] using h`.

Use `conv_lhs => rw [← hg, sum_withKer_smul]`. Conclude with `Finset.sum_congr rfl fun P₁ h₁ => hT g hg _ _ (mem_withKer.1 h₁) hP'`. Establish `h3` using `Finset.sum_comm (s := withKer L) (t := withLat L) (f := T)`. Rewrite `h3` using `[Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_const, Finset.sum_const, card_withKer, ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ]`. Establish `h4 : ((withLat L).card : ℂ) ≠ 0`.

Conclude with `(Finset.card_pos.2 ⟨P', mem_withLat.2 hP'⟩).ne'` after adjusting the coercions. Establish `h5` using `smul_right_injective A h4 h3`. Rewrite using `[mainDatum_eq, dia_FFStar, hP, hP']`. Simplify `h5` using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]`.
-/
theorem lift_mainDatum {L : Submodule 𝒪[k] (n' → k)} [L.IsLattice k] (he : φ ∈ EqForm π) (hθ : IsLiftInv π θ L)
    (Q : Pair k n) {P P' : Pair k n'} (hP : P.ker = L) (hP' : P'.lat = L) :
    θ (φ P) (mainDatum q χ ε P Q) = θ (dia ε (FFStar q χ φ) P') (phiOne P' Q) := by
  classical
  let T : Pair k n' → Pair k n' → A := fun P₁ P₂ => χ (-((ε : 𝓀[k]) * cross q P₁ P₂)) • θ (φ P₁) (phiOne P₂ Q)
  have hT : ∀ g : GL n' k, g • L = L → ∀ P₁ P₂, P₁.ker = L → P₂.lat = L → T (g • P₁) (g • P₂) = T P₁ P₂ := by
    intro g hg P₁ P₂ h₁ h₂
    have h3 : phiOne (g • P₂) Q = fun x => phiOne P₂ Q (x * g.val) := funext fun x => by
      simpa using phiOne_smul (P := P₂) (Q := Q) (x := x) g 1
    simp only [T]
    rw [cross_smul q (h₂.trans h₁.symm), he g P₁, h3, hθ g hg _ _ (phiOne_mem_SB P₂ Q)]
  have h1 : ∀ P₁ ∈ withKer L, ∑ P₂ ∈ withLat L, T P₁ P₂ = ∑ P₂ ∈ withLat L, T P P₂ := fun P₁ h => by
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL n' k) P P₁
    have hg : g • L = L := by simpa [hP] using h
    conv_lhs => rw [← hg, sum_withLat_smul]
    exact Finset.sum_congr rfl fun P₂ h₂ => hT g hg _ _ hP (mem_withLat.1 h₂)
  have h2 : ∀ P₂ ∈ withLat L, ∑ P₁ ∈ withKer L, T P₁ P₂ = ∑ P₁ ∈ withKer L, T P₁ P' := fun P₂ h => by
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL n' k) P' P₂
    have hg : g • L = L := by simpa [hP'] using h
    conv_lhs => rw [← hg, sum_withKer_smul]
    exact Finset.sum_congr rfl fun P₁ h₁ => hT g hg _ _ (mem_withKer.1 h₁) hP'
  have h3 := Finset.sum_comm (s := withKer L) (t := withLat L) (f := T)
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_const, Finset.sum_const, card_withKer,
    ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at h3
  have h4 : ((withLat L).card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.2 ⟨P', mem_withLat.2 hP'⟩).ne'
  have h5 := smul_right_injective A h4 h3
  rw [mainDatum_eq, dia_FFStar, hP, hP']
  simpa only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply] using h5

end Decomposition

section Transform
variable [Fintype n]

/- English proof (translation)
Use `⟨(isClopen_lattice L).preimage (f := fun y : n → k => q.inv • y) (by fun_prop), ?_⟩` and prove the remaining obligations. Take `⟨g, rfl⟩` from `exists_smul_lat (stdLat k n) L`. Establish `hK : IsCompact (Set.univ.pi fun _ : n => (𝒪[k] : Set k))` using `isCompact_univ_pi fun _ => isCompact_int k`. Use `hK.image (f := fun z : n → k => ((q.1 : 𝒪[k]) : k) • (g.val *ᵥ z)) ((continuous_const.matrix_mulVec continuous_id).const_smul ((q.1 : 𝒪[k]) : k)) using 1` and compare the differences between its conclusion and the goal. Use extensionality with `y`.

Simplify using `only [Set.mem_setOf_eq, mem_smul_iff, mem_stdLat, Set.mem_image, Set.mem_pi, Set.mem_univ, true_imp_iff, SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨_, h, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `q.1 • g • g⁻¹ • q.inv • y = y`.

Rewrite using `[smul_inv_smul, q.smul_inv_smul]`. Introduce and unpack `⟨z, hz, rfl⟩`. Express the relevant statement in the definitionally equal form `∀ i, (g⁻¹ • q.inv • q.1 • g • z) i ∈ _`. Rewrite using `[q.inv_smul_smul, inv_smul_smul]` and apply the resulting hypothesis.
-/
theorem isClopen_isCompact_qLat (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] :
    IsClopen {y : n → k | q.inv • y ∈ L} ∧ IsCompact {y : n → k | q.inv • y ∈ L} := by
  classical
  refine ⟨(isClopen_lattice L).preimage (f := fun y : n → k => q.inv • y) (by fun_prop), ?_⟩
  obtain ⟨g, rfl⟩ := exists_smul_lat (stdLat k n) L
  have hK : IsCompact (Set.univ.pi fun _ : n => (𝒪[k] : Set k)) := isCompact_univ_pi fun _ => isCompact_int k
  convert hK.image (f := fun z : n → k => ((q.1 : 𝒪[k]) : k) • (g.val *ᵥ z))
    ((continuous_const.matrix_mulVec continuous_id).const_smul ((q.1 : 𝒪[k]) : k)) using 1
  ext y
  simp only [Set.mem_setOf_eq, mem_smul_iff, mem_stdLat, Set.mem_image, Set.mem_pi, Set.mem_univ, true_imp_iff,
    SetLike.mem_coe]
  constructor
  · intro h
    refine ⟨_, h, ?_⟩
    change q.1 • g • g⁻¹ • q.inv • y = y
    rw [smul_inv_smul, q.smul_inv_smul]
  · rintro ⟨z, hz, rfl⟩
    change ∀ i, (g⁻¹ • q.inv • q.1 • g • z) i ∈ _
    rwa [q.inv_smul_smul, inv_smul_smul]

variable [MeasurableSpace k] [BorelSpace k] (q : Unif k) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)
  (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k]

omit [BorelSpace k] in

/- English proof (translation)
Take `⟨h1, h2⟩` from `isClopen_isCompact_qLat q L`. Conclude with `ENNReal.toReal_pos (h1.2.measure_ne_zero μ ⟨0, by simp⟩) h2.measure_lt_top.ne`.
-/
theorem volQ_pos : 0 < volQ μ q L := by
  obtain ⟨h1, h2⟩ := isClopen_isCompact_qLat q L
  exact ENNReal.toReal_pos (h1.2.measure_ne_zero μ ⟨0, by simp⟩) h2.measure_lt_top.ne

include hψ

open Classical in

/- English proof (translation)
Use `haveI := secondCountable k`. Use `haveI := t2Space k`. Take `⟨h1, h2⟩` from `isClopen_isCompact_qLat q L`. Establish `h3` using `ite_mem_SB h1 h2`. Use `Continuous.integrable_of_hasCompactSupport (h3.1.continuous.mul ?_) h3.2.mul_right` and prove the remaining obligations.

Conclude with `continuous_subtype_val.comp (hψ.continuous.comp (continuous_const.dotProduct continuous_id))`.
-/
theorem integrable_qLat (η : n → k) :
    Integrable (fun y => (if q.inv • y ∈ L then (1 : ℂ) else 0) * (ψ (η ⬝ᵥ y) : ℂ)) μ := by
  haveI := secondCountable k
  haveI := t2Space k
  obtain ⟨h1, h2⟩ := isClopen_isCompact_qLat q L
  have h3 := ite_mem_SB h1 h2
  refine Continuous.integrable_of_hasCompactSupport (h3.1.continuous.mul ?_) h3.2.mul_right
  exact continuous_subtype_val.comp (hψ.continuous.comp (continuous_const.dotProduct continuous_id))

open Classical in

/- English proof (translation)
Use `haveI := secondCountable k`. Establish `hd : ∀ y : n → k, (q.1 • η) ⬝ᵥ y = η ⬝ᵥ (q.1 • y)` using `fun y => by rw [smul_dotProduct, dotProduct_smul]`. Use `split_ifs with h`. Establish `: ∀ y, (if q.inv • y ∈ L then (1 : ℂ) else 0) * (ψ (η ⬝ᵥ y) : ℂ) = {y : n → k | q.inv • y ∈ L}.indicator (fun _ => (1 : ℂ)) y` using `fun y => by`. Distinguish the cases in `hy : q.inv • y ∈ L`.

Establish `h1` using `h _ hy`. Rewrite `h1` using `[hd, q.smul_inv_smul]`. Rewrite using `[if_pos hy, Set.indicator_of_mem (show y ∈ {y : n → k | q.inv • y ∈ L} from hy), apply_int_eq_one hψ ⟨_, h1⟩, Circle.coe_one, mul_one]`. Rewrite using `[if_neg hy, Set.indicator_of_notMem (show y ∉ {y : n → k | q.inv • y ∈ L} from hy), zero_mul]`. Simplify using `only [this]`.

Rewrite using `[integral_indicator_const _ (isClopen_isCompact_qLat q L).1.2.measurableSet]`. Simplify using `[volQ]`. Choose the witnesses or unpack the hypotheses as in `⟨w, hw, hne⟩ : ∃ w : n → k, q.inv • w ∈ L ∧ ψ (η ⬝ᵥ w) ≠ 1 := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`.

Use `h fun z hz => ?_` and prove the remaining obligations. Distinguish the cases in `h0 : (q.1 • η) ⬝ᵥ z = 0`. Rewrite using `[h0]`. Conclude with `zero_mem _`. Use `(Valuation.mem_integer_iff _ _).2 ?_` and prove the remaining obligations.

Use `(hψ ((q.1 • η) ⬝ᵥ z)).1 fun y hy => by` as an intermediate fact. Establish `ht : y / ((q.1 • η) ⬝ᵥ z) ∈ 𝒪[k]`. Rewrite using `[Valuation.mem_integer_iff, map_div₀]`. Conclude with `div_le_one_of_le₀ hy zero_le'`. Establish `h1` using `hc (q.1 • (⟨_, ht⟩ : 𝒪[k]) • z) (by rw [q.inv_smul_smul]; exact L.smul_mem _ hz)`.

Rewrite `h1` using `[← hd, dotProduct_smul]`. Rewrite using `[← div_mul_cancel₀ y h0]` and apply the resulting hypothesis. Simplify using `using this`. Establish `h1` using `integral_add_right_eq_self (μ := μ) (fun y => (if q.inv • y ∈ L then (1 : ℂ) else 0) * (ψ (η ⬝ᵥ y) : ℂ)) w`. Establish `h2 : ∀ y, (if q.inv • (y + w) ∈ L then (1 : ℂ) else 0) * (ψ (η ⬝ᵥ (y + w)) : ℂ) = (ψ (η ⬝ᵥ w) : ℂ) * ((if q.inv • y ∈ L then (1 : ℂ) else 0) * (ψ (η ⬝ᵥ y) : ℂ))` using `fun y => by`.

Simplify using `only [smul_add, L.add_mem_iff_left hw]`. Rewrite using `[dotProduct_add, AddChar.map_add_eq_mul, Circle.coe_mul]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [h2, integral_const_mul] at h1`. Establish `h3 : (ψ (η ⬝ᵥ w) : ℂ) - 1 ≠ 0` using `fun h4 => hne (Circle.ext (by simpa using sub_eq_zero.mp h4))`.

Use `(mul_eq_zero.mp ?_).resolve_left h3` and prove the remaining obligations. Rewrite using `[sub_mul, h1, one_mul, sub_self]`.
-/
theorem integral_qLat (η : n → k) :
    ∫ y, (if q.inv • y ∈ L then (1 : ℂ) else 0) * (ψ (η ⬝ᵥ y) : ℂ) ∂μ =
      if InDual L (q.1 • η) then (volQ μ q L : ℂ) else 0 := by
  haveI := secondCountable k
  have hd : ∀ y : n → k, (q.1 • η) ⬝ᵥ y = η ⬝ᵥ (q.1 • y) := fun y => by rw [smul_dotProduct, dotProduct_smul]
  split_ifs with h
  · have : ∀ y, (if q.inv • y ∈ L then (1 : ℂ) else 0) * (ψ (η ⬝ᵥ y) : ℂ) =
        {y : n → k | q.inv • y ∈ L}.indicator (fun _ => (1 : ℂ)) y := fun y => by
      by_cases hy : q.inv • y ∈ L
      · have h1 := h _ hy
        rw [hd, q.smul_inv_smul] at h1
        rw [if_pos hy, Set.indicator_of_mem (show y ∈ {y : n → k | q.inv • y ∈ L} from hy),
          apply_int_eq_one hψ ⟨_, h1⟩, Circle.coe_one, mul_one]
      · rw [if_neg hy, Set.indicator_of_notMem (show y ∉ {y : n → k | q.inv • y ∈ L} from hy), zero_mul]
    simp only [this]
    rw [integral_indicator_const _ (isClopen_isCompact_qLat q L).1.2.measurableSet]
    simp [volQ]
  · obtain ⟨w, hw, hne⟩ : ∃ w : n → k, q.inv • w ∈ L ∧ ψ (η ⬝ᵥ w) ≠ 1 := by
      by_contra hc
      push Not at hc
      refine h fun z hz => ?_
      by_cases h0 : (q.1 • η) ⬝ᵥ z = 0
      · rw [h0]; exact zero_mem _
      refine (Valuation.mem_integer_iff _ _).2 ?_
      have := (hψ ((q.1 • η) ⬝ᵥ z)).1 fun y hy => by
        have ht : y / ((q.1 • η) ⬝ᵥ z) ∈ 𝒪[k] := by
          rw [Valuation.mem_integer_iff, map_div₀]
          exact div_le_one_of_le₀ hy zero_le'
        have h1 := hc (q.1 • (⟨_, ht⟩ : 𝒪[k]) • z) (by rw [q.inv_smul_smul]; exact L.smul_mem _ hz)
        rw [← hd, dotProduct_smul] at h1
        rwa [← div_mul_cancel₀ y h0]
      simpa using this
    have h1 := integral_add_right_eq_self (μ := μ)
      (fun y => (if q.inv • y ∈ L then (1 : ℂ) else 0) * (ψ (η ⬝ᵥ y) : ℂ)) w
    have h2 : ∀ y, (if q.inv • (y + w) ∈ L then (1 : ℂ) else 0) * (ψ (η ⬝ᵥ (y + w)) : ℂ) =
        (ψ (η ⬝ᵥ w) : ℂ) * ((if q.inv • y ∈ L then (1 : ℂ) else 0) * (ψ (η ⬝ᵥ y) : ℂ)) := fun y => by
      simp only [smul_add, L.add_mem_iff_left hw]
      rw [dotProduct_add, AddChar.map_add_eq_mul, Circle.coe_mul]
      ring
    simp only [h2, integral_const_mul] at h1
    have h3 : (ψ (η ⬝ᵥ w) : ℂ) - 1 ≠ 0 := fun h4 => hne (Circle.ext (by simpa using sub_eq_zero.mp h4))
    refine (mul_eq_zero.mp ?_).resolve_left h3
    rw [sub_mul, h1, one_mul, sub_self]

variable [Fintype n'] (ε : 𝒪[k]ˣ) (P : Pair k n') (x₀ : Matrix n n' k) (η : n → k)

/- English proof (translation)
Use `haveI := secondCountable k`. Distinguish the cases in `h : ∀ z ∈ P.ker, x₀ *ᵥ z ∈ L`. Use `swap`. Establish `: ∀ y, datum q P L x₀ y = 0` using `fun y => if_neg fun h' => h h'.1`. Simplify using `[datumHat, this, term, dif_neg h]`.

Establish `hψ'` using `hasConductor_mulShift hψ ε`. Use `set w := x₀ *ᵥ (q.1 • P.vec) with hw`. Establish `hF : ∀ y, datum q P L x₀ y * (ψ (((ε : 𝒪[k]) : k) * (η ⬝ᵥ y)) : ℂ) = (ψ (-(((ε : 𝒪[k]) : k) * (η ⬝ᵥ w))) : ℂ) * ((if q.inv • (y + w) ∈ L then (1 : ℂ) else 0) * (ψ.mulShift ((ε : 𝒪[k]) : k) (η ⬝ᵥ (y + w)) : ℂ))` using `fun y => by`. Establish `h1 : q.inv • (y + w) = q.inv • y + x₀ *ᵥ P.vec`. Rewrite using `[smul_add, hw, ← mulVec_smul, q.inv_smul_smul]`.

Rewrite using `[mul_left_comm, ← Circle.coe_mul, AddChar.mulShift_apply, ← AddChar.map_add_eq_mul, dotProduct_add, mul_add, neg_add_cancel_comm_assoc, h1, datum]`. Use `congr 1`. Conclude with `if_congr (and_iff_right h) rfl rfl`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `only [hF]`.

Conclude with `((integrable_qLat q hψ' μ L η).comp_add_right w).const_mul _`. Simplify using `only [datumHat, hF]`. Rewrite using `[integral_const_mul, integral_add_right_eq_self (μ := μ) (fun y => (if q.inv • y ∈ L then (1 : ℂ) else 0) * (ψ.mulShift ((ε : 𝒪[k]) : k) (η ⬝ᵥ y) : ℂ)) w, integral_qLat q hψ']`. Simplify using `only [cosetInd_eq]`. Use `split_ifs with hD`.

Take `⟨f, hf⟩` from `exists_lifts hD`. Rewrite using `[finsum_eq_single _ f fun g hg => by rw [if_neg fun h' => hg (lifts_unique h' hf), mul_zero], if_pos hf, mul_one, mul_comm, term, dif_pos h]`. Take `⟨s, hs, e⟩` from `hf ⟨w, h _ (Pair.smul_mem_ker q.mem_max P.hasVal_vec.mem)⟩`. Establish `e' : -(((resUnit ε : 𝓀[k]ˣ) : 𝓀[k]) * residue 𝒪[k] s) = residue 𝒪[k] (-(ε * s))` using `by simp [resUnit]`. Establish `hs' : (s : k) = (q.1 : k) * (η ⬝ᵥ w)` using `by rw [hs, smul_dotProduct]; rfl`.

Rewrite using `[← e, e', resChar_residue]`. Use `congr 3`. Use `push_cast`. Rewrite using `[hs', Unif.inv]`. Clear denominators, using `[q.ne_zero]` for the nonvanishing conditions.

Simplify using `[show ∀ f, ¬ Lifts L (q.1 • η) f from fun f hf => hD (inDual_of_lifts hf)]`.
-/
theorem datumHat_eq :
    Integrable (fun y => datum q P L x₀ y * (ψ (((ε : 𝒪[k]) : k) * (η ⬝ᵥ y)) : ℂ)) μ ∧
      datumHat ψ ε μ q P L x₀ η = (volQ μ q L : ℂ) * ∑ᶠ fW : Module.Dual 𝓀[k] (Red L),
        term q (resChar ψ hψ q) (resUnit ε) P L fW x₀ * cosetInd q L fW η := by
  classical
  haveI := secondCountable k
  by_cases h : ∀ z ∈ P.ker, x₀ *ᵥ z ∈ L
  swap
  · have : ∀ y, datum q P L x₀ y = 0 := fun y => if_neg fun h' => h h'.1
    simp [datumHat, this, term, dif_neg h]
  have hψ' := hasConductor_mulShift hψ ε
  set w := x₀ *ᵥ (q.1 • P.vec) with hw
  have hF : ∀ y, datum q P L x₀ y * (ψ (((ε : 𝒪[k]) : k) * (η ⬝ᵥ y)) : ℂ) =
      (ψ (-(((ε : 𝒪[k]) : k) * (η ⬝ᵥ w))) : ℂ) * ((if q.inv • (y + w) ∈ L then (1 : ℂ) else 0) *
        (ψ.mulShift ((ε : 𝒪[k]) : k) (η ⬝ᵥ (y + w)) : ℂ)) := fun y => by
    have h1 : q.inv • (y + w) = q.inv • y + x₀ *ᵥ P.vec := by
      rw [smul_add, hw, ← mulVec_smul, q.inv_smul_smul]
    rw [mul_left_comm, ← Circle.coe_mul, AddChar.mulShift_apply, ← AddChar.map_add_eq_mul, dotProduct_add, mul_add,
      neg_add_cancel_comm_assoc, h1, datum]
    congr 1
    exact if_congr (and_iff_right h) rfl rfl
  refine ⟨?_, ?_⟩
  · simp only [hF]
    exact ((integrable_qLat q hψ' μ L η).comp_add_right w).const_mul _
  simp only [datumHat, hF]
  rw [integral_const_mul, integral_add_right_eq_self (μ := μ) (fun y => (if q.inv • y ∈ L then (1 : ℂ) else 0) *
    (ψ.mulShift ((ε : 𝒪[k]) : k) (η ⬝ᵥ y) : ℂ)) w, integral_qLat q hψ']
  simp only [cosetInd_eq]
  split_ifs with hD
  · obtain ⟨f, hf⟩ := exists_lifts hD
    rw [finsum_eq_single _ f fun g hg => by rw [if_neg fun h' => hg (lifts_unique h' hf), mul_zero],
      if_pos hf, mul_one, mul_comm, term, dif_pos h]
    obtain ⟨s, hs, e⟩ := hf ⟨w, h _ (Pair.smul_mem_ker q.mem_max P.hasVal_vec.mem)⟩
    have e' : -(((resUnit ε : 𝓀[k]ˣ) : 𝓀[k]) * residue 𝒪[k] s) = residue 𝒪[k] (-(ε * s)) := by simp [resUnit]
    have hs' : (s : k) = (q.1 : k) * (η ⬝ᵥ w) := by rw [hs, smul_dotProduct]; rfl
    rw [← e, e', resChar_residue]
    congr 3
    push_cast
    rw [hs', Unif.inv]
    field_simp [q.ne_zero]
  · simp [show ∀ f, ¬ Lifts L (q.1 • η) f from fun f hf => hD (inDual_of_lifts hf)]

end Transform

section Kernels
variable [Fintype n']

/- English proof (translation)
Establish `hm : ∀ v : n' ⊕ Fin 1 → k, withCol x₀ y *ᵥ v = x₀ *ᵥ (v ∘ Sum.inl) + v (Sum.inr 0) • y` using `fun v => by`. Use extensionality with `i`. Simplify using `[withCol, mulVec, dotProduct, mul_comm]`. Use `if_congr ?_ rfl rfl` and prove the remaining obligations. Simplify using `only [← gluedLat_one, mem_gluedLat, hm, Fin.forall_fin_one]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, h'⟩ v ⟨s, hs, -, hv, -⟩`. Use `add_mem (h _ hs) (LY.smul_mem s h')` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[hv rfl, mulVec_sub, mulVec_smul, smul_add, mul_comm, mul_smul]`.

Normalize the expressions using the abelian group laws. Introduce `h`. Use `⟨fun z hz => ?_, ?_⟩` and prove the remaining obligations. Simplify `hz, by simp⟩` using `using h (Sum.elim z 0) ⟨0, by simpa`. Simplify `h (Sum.elim P.vec fun _ => q.inv) ⟨1, by simp, by simp⟩` using `[add_comm]`.
-/
theorem datum_eq (q : Unif k) (P : Pair k n') (LY : Submodule 𝒪[k] (n → k)) (x₀ : Matrix n n' k) (y : n → k) :
    datum q P LY x₀ y = latInd (gluedS q 1 P.ker P.vec) LY (withCol x₀ y) := by
  classical
  have hm : ∀ v : n' ⊕ Fin 1 → k, withCol x₀ y *ᵥ v = x₀ *ᵥ (v ∘ Sum.inl) + v (Sum.inr 0) • y := fun v => by
    ext i
    simp [withCol, mulVec, dotProduct, mul_comm]
  refine if_congr ?_ rfl rfl
  simp only [← gluedLat_one, mem_gluedLat, hm, Fin.forall_fin_one]
  constructor
  · rintro ⟨h, h'⟩ v ⟨s, hs, -, hv, -⟩
    have := add_mem (h _ hs) (LY.smul_mem s h')
    convert this using 1
    rw [hv rfl, mulVec_sub, mulVec_smul, smul_add, mul_comm, mul_smul]
    abel
  · intro h
    refine ⟨fun z hz => ?_, ?_⟩
    · simpa using h (Sum.elim z 0) ⟨0, by simpa using hz, by simp⟩
    · simpa [add_comm] using h (Sum.elim P.vec fun _ => q.inv) ⟨1, by simp, by simp⟩

omit [Fintype n'] in

/- English proof (translation)
Establish `hq : (q.1 : k) * q.inv = 1` using `mul_inv_cancel₀ q.ne_zero`. Establish `h1 : ∀ s : 𝒪[k], (v - s • q.inv • avec k n'' 1 1) ∘ Sum.inl = v ∘ Sum.inl` using `fun s => by`. Use extensionality with `i`. Simplify using `[avec]`. Establish `h2 : ∀ s : 𝒪[k], (v - s • q.inv • avec k n'' 1 1) (Sum.inr 0) = v (Sum.inr 0) - s * q.inv` using `fun s => by`.

Simplify using `[avec, Subring.smul_def]`. Rewrite using `[lastPair, Pair.hasVal_iff (glue_hasVal _), glue_ker]`. Simplify using `only [mem_lastKer, h1, h2]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, rfl, hL, ht⟩`.

Use `⟨hL, s + q.1 * ⟨_, ht⟩, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(s : k) + q.1 * (v (Sum.inr 0) - s * q.inv) = q.1 * v (Sum.inr 0)`. Take the linear combination `(-(s : k)) * hq`. Rewrite using `[map_add, map_mul, (residue_eq_zero_iff _).2 q.mem_max, zero_mul, add_zero]`. Introduce and unpack `⟨hL, s, hs, rfl⟩`.

Use `⟨s, rfl, hL, ?_⟩` and prove the remaining obligations. Establish `: v (Sum.inr 0) - s * q.inv = 0`. Rewrite using `[hs]`. Express the relevant statement in the definitionally equal form `_ - (q.1 : k) * v (Sum.inr 0) * q.inv = 0`. Take the linear combination `(-(v (Sum.inr 0))) * hq`.

Rewrite using `[this]`. Conclude with `zero_mem _`.
-/
theorem lastPair_hasVal (q : Unif k) (L : Submodule 𝒪[k] (n'' → k)) [L.IsLattice k] (v : n'' ⊕ Fin 1 → k)
    (a : 𝓀[k]) : (lastPair q L).HasVal v a ↔
      v ∘ Sum.inl ∈ L ∧ ∃ s : 𝒪[k], (s : k) = q.1 • v (Sum.inr 0) ∧ residue 𝒪[k] s = a := by
  have hq : (q.1 : k) * q.inv = 1 := mul_inv_cancel₀ q.ne_zero
  have h1 : ∀ s : 𝒪[k], (v - s • q.inv • avec k n'' 1 1) ∘ Sum.inl = v ∘ Sum.inl := fun s => by
    ext i
    simp [avec]
  have h2 : ∀ s : 𝒪[k], (v - s • q.inv • avec k n'' 1 1) (Sum.inr 0) = v (Sum.inr 0) - s * q.inv := fun s => by
    simp [avec, Subring.smul_def]
  rw [lastPair, Pair.hasVal_iff (glue_hasVal _), glue_ker]
  simp only [mem_lastKer, h1, h2]
  constructor
  · rintro ⟨s, rfl, hL, ht⟩
    refine ⟨hL, s + q.1 * ⟨_, ht⟩, ?_, ?_⟩
    · change (s : k) + q.1 * (v (Sum.inr 0) - s * q.inv) = q.1 * v (Sum.inr 0)
      linear_combination (-(s : k)) * hq
    · rw [map_add, map_mul, (residue_eq_zero_iff _).2 q.mem_max, zero_mul, add_zero]
  · rintro ⟨hL, s, hs, rfl⟩
    refine ⟨s, rfl, hL, ?_⟩
    have : v (Sum.inr 0) - s * q.inv = 0 := by
      rw [hs]
      change _ - (q.1 : k) * v (Sum.inr 0) * q.inv = 0
      linear_combination (-(v (Sum.inr 0))) * hq
    rw [this]
    exact zero_mem _

omit [Fintype n'] in
open Classical in

/- English proof (translation)
Establish `h1 : ∀ y, (withRow x' η *ᵥ y) ∘ Sum.inl = x' *ᵥ y` using `fun y => rfl`. Establish `h2 : ∀ y, q.1 • (withRow x' η *ᵥ y) (Sum.inr 0) = (q.1 • η) ⬝ᵥ y` using `fun y => by`. Rewrite using `[smul_dotProduct]`. Both sides reduce to the same expression. Rewrite using `[latInd, ite_zero_mul_ite_zero, mul_one]`.

Use `if_congr ?_ rfl rfl` and prove the remaining obligations. Simplify using `only [maps_iff_hasVal, lastPair_hasVal, h1, h2]`. Conclude with `⟨fun h => ⟨fun y hy => (h y _ (ofDual_hasVal LY fW ⟨y, hy⟩)).1, fun y => (h y _ (ofDual_hasVal LY fW y)).2⟩, fun h y a ⟨hy, ha⟩ => ⟨h.1 y hy, ha ▸ h.2 ⟨y, hy⟩⟩⟩`.
-/
theorem phiOne_last [Fintype n] (q : Unif k) (LY : Submodule 𝒪[k] (n → k)) [LY.IsLattice k]
    (L : Submodule 𝒪[k] (n'' → k)) [L.IsLattice k] (fW : {f : Module.Dual 𝓀[k] (Red LY) // f ≠ 0})
    (x' : Matrix n'' n k) (η : n → k) :
    phiOne (ofDual LY fW) (lastPair q L) (withRow x' η) =
      latInd LY L x' * (if Lifts LY (q.1 • η) fW.1 then 1 else 0) := by
  have h1 : ∀ y, (withRow x' η *ᵥ y) ∘ Sum.inl = x' *ᵥ y := fun y => rfl
  have h2 : ∀ y, q.1 • (withRow x' η *ᵥ y) (Sum.inr 0) = (q.1 • η) ⬝ᵥ y := fun y => by
    rw [smul_dotProduct]; rfl
  rw [latInd, ite_zero_mul_ite_zero, mul_one]
  refine if_congr ?_ rfl rfl
  simp only [maps_iff_hasVal, lastPair_hasVal, h1, h2]
  exact ⟨fun h => ⟨fun y hy => (h y _ (ofDual_hasVal LY fW ⟨y, hy⟩)).1, fun y => (h y _ (ofDual_hasVal LY fW y)).2⟩,
    fun h y a ⟨hy, ha⟩ => ⟨h.1 y hy, ha ▸ h.2 ⟨y, hy⟩⟩⟩

end Kernels

section Last
variable [Fintype n] [Fintype n'] (q : Unif k) (LY : Submodule 𝒪[k] (n → k)) [LY.IsLattice k]
  (L'' : Submodule 𝒪[k] (n'' → k)) [L''.IsLattice k] {M A : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup A]
  [Module ℂ A] (x' : Matrix n'' n k) (η : n → k)

omit [Fintype n'] in

/- English proof (translation)
Rewrite using `[phiOne_last, cosetInd_eq]`.
-/
theorem phiOne_last' (fW : {f : Module.Dual 𝓀[k] (Red LY) // f ≠ 0}) :
    phiOne (ofDual LY fW) (lastPair q L'') (withRow x' η) = latInd LY L'' x' * cosetInd q LY fW.1 η := by
  rw [phiOne_last, cosetInd_eq]

/- English proof (translation)
Simplify using `only [← phiOne_last']`. Simplify using `only [fun P => finsum_ofDual LY fun Q => mainDatum q χ ε P Q x₀ * phiOne Q (lastPair q L'') (withRow x' η), Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun Q _ => ?_` and prove the remaining obligations. Simplify using `only [mul_comm _ (phiOne Q (lastPair q L'') (withRow x' η)), mul_smul, ← Finset.smul_sum, sum_mainDatum]`.
-/
theorem sum_main_last (χ : AddChar 𝓀[k] ℂ) (ε : 𝓀[k]ˣ) (L : Submodule 𝒪[k] (n' → k)) (φ : Form k n' M)
    (x₀ : Matrix n n' k) :
    ∑ P ∈ withKer L, (∑ᶠ fW : {f : Module.Dual 𝓀[k] (Red LY) // f ≠ 0},
        mainDatum q χ ε P (ofDual LY fW) x₀ * (latInd LY L'' x' * cosetInd q LY fW.1 η)) • φ P =
      ∑ Q ∈ withLat LY, ∑ P' ∈ withLat L,
        (phiOne Q (lastPair q L'') (withRow x' η) * phiOne P' Q x₀) • dia ε (FFStar q χ φ) P' := by
  simp only [← phiOne_last']
  simp only [fun P => finsum_ofDual LY fun Q => mainDatum q χ ε P Q x₀ * phiOne Q (lastPair q L'') (withRow x' η),
    Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun Q _ => ?_
  simp only [mul_comm _ (phiOne Q (lastPair q L'') (withRow x' η)), mul_smul, ← Finset.smul_sum, sum_mainDatum]

variable [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (ε : 𝒪[k]ˣ)
  (μ : Measure (n → k)) [μ.IsAddHaarMeasure]

/- English proof (translation)
Use `letI := Fintype.ofFinite {f : Module.Dual 𝓀[k] (Red LY) // f ≠ 0}`. Use extensionality with `x₀`. Simplify using `only [Pi.smul_apply, Pi.add_apply, Finset.sum_apply, smul_eq_mul]`. Rewrite using `[(datumHat_eq q hψ μ LY ε P x₀ η).2, finsum_split, finsum_eq_sum_of_fintype, sum_withLat, term_zero, mul_left_comm, mul_add, Finset.mul_sum]`. Use `congr 2`.

Expand and normalize the polynomial expressions, which then agree. Use `Finset.sum_congr rfl fun f _ => ?_` and prove the remaining obligations. Rewrite using `[term_ne_zero, phiOne_last', Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem datumHat_mul (P : Pair k n') :
    latInd LY L'' x' • (fun x₀ => datumHat ψ ε μ q P LY x₀ η) = (volQ μ q LY : ℂ) •
      ((latInd LY L'' x' * cosetInd q LY 0 η) • latInd P.ker LY +
        ∑ Q ∈ withLat LY, phiOne Q (lastPair q L'') (withRow x' η) •
          (latInd P.ker Q.ker + mainDatum q (resChar ψ hψ q) (resUnit ε) P Q)) := by
  letI := Fintype.ofFinite {f : Module.Dual 𝓀[k] (Red LY) // f ≠ 0}
  ext x₀
  simp only [Pi.smul_apply, Pi.add_apply, Finset.sum_apply, smul_eq_mul]
  rw [(datumHat_eq q hψ μ LY ε P x₀ η).2, finsum_split, finsum_eq_sum_of_fintype, sum_withLat, term_zero,
    mul_left_comm, mul_add, Finset.mul_sum]
  congr 2
  · ring
  · refine Finset.sum_congr rfl fun f _ => ?_
    rw [term_ne_zero, phiOne_last', Pi.add_apply]
    ring

variable [DecidableEq n'] {L : Submodule 𝒪[k] (n' → k)} [L.IsLattice k] {φ : Form k n' M}

/- English proof (translation)
Establish `h` using `fun P => congrFun (datumHat_mul q LY L'' x' η hψ ε μ P) x₀`. Simplify using `only [Pi.smul_apply, Pi.add_apply, Finset.sum_apply, smul_eq_mul] at h`. Simplify using `only [mul_comm _ (latInd LY L'' x'), h]`. Simplify using `only [mul_smul, add_smul, Finset.sum_smul, ← Finset.smul_sum, Finset.sum_add_distrib, sum_latInd hφ, smul_zero, zero_add]`. Rewrite using `[Finset.sum_comm]`.

Simplify using `only [← Finset.smul_sum, Finset.sum_add_distrib, sum_latInd hφ, zero_add, sum_mainDatum]`.
-/
theorem sum_datumHat (hφ : φ ∈ Mram k n' M) (x₀ : Matrix n n' k) :
    ∑ P ∈ withKer L, (datumHat ψ ε μ q P LY x₀ η * latInd LY L'' x') • φ P =
      (volQ μ q LY : ℂ) • ∑ Q ∈ withLat LY, ∑ P' ∈ withLat L,
        (phiOne Q (lastPair q L'') (withRow x' η) * phiOne P' Q x₀) •
          dia (resUnit ε) (FFStar q (resChar ψ hψ q) φ) P' := by
  have h := fun P => congrFun (datumHat_mul q LY L'' x' η hψ ε μ P) x₀
  simp only [Pi.smul_apply, Pi.add_apply, Finset.sum_apply, smul_eq_mul] at h
  simp only [mul_comm _ (latInd LY L'' x'), h]
  simp only [mul_smul, add_smul, Finset.sum_smul, ← Finset.smul_sum, Finset.sum_add_distrib, sum_latInd hφ,
    smul_zero, zero_add]
  rw [Finset.sum_comm]
  simp only [← Finset.smul_sum, Finset.sum_add_distrib, sum_latInd hφ, zero_add, sum_mainDatum]

/- English proof (translation)
Establish `h0` using `lift_latInd P hφ he (hP.symm ▸ hθ)`. Rewrite using `[← map_smul, datumHat_mul q LY L'' x' η hψ]`. Simplify using `only [map_smul, map_add, map_sum, h0 LY, fun Q : Pair k n => h0 Q.ker, smul_zero, zero_add, fun Q => lift_mainDatum q (resChar ψ hψ q) (resUnit ε) he hθ Q hP hP']`.
-/
theorem lift_datumHat {π : Representation ℂ (GL n' k) M} {θ : M →ₗ[ℂ] (Matrix n n' k → ℂ) →ₗ[ℂ] A}
    (hφ : φ ∈ Mram k n' M) (he : φ ∈ EqForm π) (hθ : IsLiftInv π θ L) {P P' : Pair k n'} (hP : P.ker = L)
    (hP' : P'.lat = L) :
    latInd LY L'' x' • θ (φ P) (fun x₀ => datumHat ψ ε μ q P LY x₀ η) =
      (volQ μ q LY : ℂ) • ∑ Q ∈ withLat LY, phiOne Q (lastPair q L'') (withRow x' η) •
        θ (dia (resUnit ε) (FFStar q (resChar ψ hψ q) φ) P') (phiOne P' Q) := by
  have h0 := lift_latInd P hφ he (hP.symm ▸ hθ)
  rw [← map_smul, datumHat_mul q LY L'' x' η hψ]
  simp only [map_smul, map_add, map_sum, h0 LY, fun Q : Pair k n => h0 Q.ker, smul_zero, zero_add,
    fun Q => lift_mainDatum q (resChar ψ hψ q) (resUnit ε) he hθ Q hP hP']

end Last

/- English proof (translation)
Introduce `k _ _ _ _ _ _ n n' n'' _ _ _ _`. Use `⟨fun q ψ hψ ε μ _ P LY _ => ⟨datum_eq q P LY, volQ_pos q μ LY, datumHat_eq q hψ μ LY ε P⟩, fun q ψ hψ ε P LY _ => ⟨fun fW x₀ => ⟨latInd_eq_finsum fW, term_eq_finsum q _ _ P fW⟩, term_zero q _ _ P, fun fW => ⟨compInd_zero fW, compInd_eq_phiOne fW, term_ne_zero q _ _ P fW⟩, fun L h …` and prove the remaining obligations. Use `haveI : L.IsLattice k := by`. Apply the tactic sequence `rcases hL with rfl | ⟨fW, rfl⟩ <;> infer_instance`. Conclude with `lift_latInd P hφ he hθ L`.
-/
theorem lastTwoSteps : LastTwoSteps := by
  intro k _ _ _ _ _ _ n n' n'' _ _ _ _
  refine ⟨fun q ψ hψ ε μ _ P LY _ => ⟨datum_eq q P LY, volQ_pos q μ LY, datumHat_eq q hψ μ LY ε P⟩,
    fun q ψ hψ ε P LY _ => ⟨fun fW x₀ => ⟨latInd_eq_finsum fW, term_eq_finsum q _ _ P fW⟩, term_zero q _ _ P,
      fun fW => ⟨compInd_zero fW, compInd_eq_phiOne fW, term_ne_zero q _ _ P fW⟩, fun L hL =>
        ⟨fun g hg => latInd_mul hg L, fun M _ _ φ hφ => ⟨sum_latInd hφ P.ker L, fun π A _ _ θ he hθ => ?_⟩⟩⟩,
    fun q ψ hψ ε L _ Q M _ _ φ _ => ⟨sum_mainDatum q _ _ L Q φ,
      fun π A _ _ θ he hθ P P' hP hP' => lift_mainDatum q _ _ he hθ Q hP hP'⟩,
    fun q LY _ L'' _ => ⟨fun fW x' η => ⟨phiOne_last q LY L'' fW x' η, phiOne_last' q LY L'' x' η fW⟩,
      fun ψ hψ ε L _ M _ _ φ hφ x' η => ⟨sum_main_last q LY L'' x' η _ _ L φ, fun μ _ =>
        ⟨sum_datumHat q LY L'' x' η hψ ε μ hφ,
          fun π A _ _ θ he hθ P P' hP hP' => lift_datumHat q LY L'' x' η hψ ε μ hφ he hθ hP hP'⟩⟩⟩⟩
  haveI : L.IsLattice k := by
    rcases hL with rfl | ⟨fW, rfl⟩ <;> infer_instance
  exact lift_latInd P hφ he hθ L

end GlobalTheory.LastSteps
